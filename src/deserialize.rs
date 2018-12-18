use std::io;
use std::fs::File;
use std::rc::Rc;
use std::fmt;
use std::cell::RefCell;
use byteorder::{ReadBytesExt, BigEndian};
use num_traits::cast::FromPrimitive;
use num::bigint::BigInt;
use super::types::*;

// #[macro_use] extern crate lazy_static;
// #[macro_use] extern crate num_derive;

fn invalid(s: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, s)
}

fn throw<T>(s: &str) -> io::Result<T> { Err(invalid(s)) }

fn guard(b: bool, s: &str) -> io::Result<()> {
    if b { Ok(()) } else { throw(s) }
}

trait Deserialize<A: Sized> {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<A>;
}

impl<S> Deserialize<u8> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<u8> {
        let c = d.read_u8()?;
        println!("read {}: u8", c);
        Ok(c)
    }
}

impl<S> Deserialize<u32> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<u32> {
        let x: u8 = ().read(d)?;
        let c =
            if x < 255 { x.into() }
            else { d.read_u32::<BigEndian>()? };
        println!("read {}: u32", c);
        Ok(c)
    }
}

impl<S> Deserialize<usize> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<usize> {
        let c: u32 = ().read(d)?;
        Ok(c as usize)
    }
}

impl<S> Deserialize<u64> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<u64> {
        d.read_u64::<BigEndian>()
    }
}

fn readn<A, F>(n: usize, mut f: F) -> io::Result<Vec<A>>
where F: FnMut() -> io::Result<A> {
    let mut vec = Vec::with_capacity(n);
    for _ in 0..n { vec.push(f()?) }
    Ok(vec)
}

impl<A: fmt::Debug, S: Deserialize<A>> Deserialize<Vec<A>> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<Vec<A>> {
        let v = readn(().read(d)?, || self.read(d))?;
        println!("read {:?}: vec", v);
        Ok(v)
    }
}

fn read_blob<T: io::Read>(d: &mut T) -> io::Result<Box<[u8]>> {
    let n: usize = ().read(d)?;
    let mut buf: Vec<u8> = vec![0; n];
    d.read_exact(buf.as_mut_slice())?;
    Ok(buf.into_boxed_slice())
}

impl<A, B, S: Deserialize<A> + Deserialize<B>> Deserialize<(A, B)> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<(A, B)> {
        Ok((self.read(d)?, self.read(d)?))
    }
}

impl<A: fmt::Debug, S: Deserialize<A>> Deserialize<Box<[A]>> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<Box<[A]>> {
        Ok(<S as Deserialize<Vec<A>>>::read(self, d)?.into_boxed_slice())
    }
}

impl<S> Deserialize<String> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<String> {
        let mut vec = Vec::new();
        loop {
            let c: u8 = ().read(d)?;
            if c == 0 {
                let s = String::from_utf8(vec).map_err(|_| invalid("bad utf8"))?;
                println!("read \"{}\": string", s);
                return Ok(s)
            } else { vec.push(c) }
        }
    }
}

impl<S> Deserialize<bool> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<bool> {
        let c: u8 = ().read(d)?;
        Ok(c != 0)
    }
}

impl<S> Deserialize<BigInt> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<BigInt> {
        let s: String = ().read(d)?;
        s.parse().map_err(|_| invalid("bad bignum"))
    }
}

impl<A, S: Deserialize<A>> Deserialize<Option<A>> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<Option<A>> {
        if <S as Deserialize<bool>>::read(self, d)? { Ok(Some(self.read(d)?)) }
        else { Ok(None) }
    }
}

struct ObjectReader<A>{table: RefCell<Vec<A>>}

impl<A: Clone> ObjectReader<A> {
    fn new() -> ObjectReader<A> { ObjectReader{table: RefCell::new(Vec::new())} }

    fn read_core<T: io::Read, F>(&self, d: &mut T, f: F) -> io::Result<A>
    where F: FnOnce(&mut T, u8) -> io::Result<A> {
        let c: u8 = ().read(d)?;
        if c == 0 {
            let table = self.table.borrow_mut();
            let n: usize = table.read(d)?;
            println!("backref {}", n);
            let a = table.get(n).ok_or(invalid("out of range"))?;
            Ok(a.clone())
        } else {
            let x = f(d, c-1)?;
            let mut table = self.table.borrow_mut();
            table.push(x);
            Ok(table.last().unwrap().clone())
        }
    }
}

impl Deserialize<Name> for ObjectReader<Name> {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<Name> {
        let name = ObjectReader::read_core(self, d, |d, n| {
            match n {
                0 => Ok(Rc::new(Name2::Anon)),
                1 => Ok(Rc::new(Name2::Str(Rc::new(Name2::Anon), self.read(d)?))),
                2 => Ok(Rc::new(Name2::Num(Rc::new(Name2::Anon), self.read(d)?))),
                3 => Ok(Rc::new(Name2::Str(self.read(d)?, self.read(d)?))),
                4 => Ok(Rc::new(Name2::Num(self.read(d)?, self.read(d)?))),
                _ => throw(&format!("bad name {}", n))
            }
        })?;
        println!("read {}: name", name);
        Ok(name)
    }
}

impl<S> Deserialize<BinderInfo> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<BinderInfo> {
        let c: u8 = self.read(d)?;
        let bi =
             if c & 4 != 0 { BinderInfo::Implicit }
        else if c & 2 != 0 { BinderInfo::StrictImplicit }
        else if c & 1 != 0 { BinderInfo::InstImplicit }
        else if c & 8 != 0 { BinderInfo::AuxDecl }
        else { BinderInfo::Default };
        println!("read {:?}: binder_info", bi);
        Ok(bi)
    }
}

struct Deserializer {
    name_reader: ObjectReader<Name>,
    lvl_reader: ObjectReader<Level>,
    expr_reader: ObjectReader<Expr>
}

impl Deserializer {
    fn new() -> Deserializer {
        Deserializer {
            name_reader: ObjectReader::new(),
            lvl_reader: ObjectReader::new(),
            expr_reader: ObjectReader::new(),
        }
    }
}

impl Deserialize<Name> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<Name> {
        self.name_reader.read(d)
    }
}

impl Deserialize<Level> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<Level> {
        let lvl = ObjectReader::read_core(&self.lvl_reader, d, |d, _| {
            let n: u8 = self.read(d)?;
            match n {
                0 => Ok(Rc::new(Level2::Zero)),
                1 => Ok(Rc::new(Level2::Succ(self.read(d)?))),
                2 => Ok(Rc::new(Level2::Max(self.read(d)?, self.read(d)?))),
                3 => Ok(Rc::new(Level2::IMax(self.read(d)?, self.read(d)?))),
                4 => Ok(Rc::new(Level2::Param(self.name_reader.read(d)?))),
                5 => Ok(Rc::new(Level2::Meta(self.name_reader.read(d)?))),
                _ => throw(&format!("bad name {}", n))
            }
        })?;
        println!("read {:?}: level", lvl);
        Ok(lvl)
    }
}

fn read_macro<T: io::Read>(s: &Deserializer, d: &mut T, args: Vec<Expr>) -> io::Result<Expr> {
    let k: String = s.read(d)?;
    let m = match &*k {
        "prenum" => MacroDef::Prenum(s.read(d)?),
        "STI" => MacroDef::StructureInstance {
            struct_: s.read(d)?, catchall: s.read(d)?, fields: s.read(d)? },
        "Quote" => MacroDef::ExprQuote { val: s.read(d)?, reflected: s.read(d)? },
        "Annot" => MacroDef::Annot(s.read(d)?),
        _ => unimplemented!("unknown macro {}", k)
    };
    guard(check_macro(&m, &args), "bad macro args")?;
    Ok(Rc::new(Expr2::Macro(m, args)))
}

impl Deserialize<Expr> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<Expr> {
        let expr = ObjectReader::read_core(&self.expr_reader, d, |d, n| {
            match n {
                0 => Ok(Rc::new(Expr2::Var(self.read(d)?))),
                1 => Ok(Rc::new(Expr2::Sort(self.read(d)?))),
                2 => Ok(Rc::new(Expr2::Const(self.read(d)?, self.read(d)?))),
                3 => Ok(Rc::new(Expr2::MVar(self.read(d)?, self.read(d)?, self.read(d)?))),
                4 => Ok(Rc::new(Expr2::Local(self.read(d)?, self.read(d)?, self.read(d)?, self.read(d)?))),
                5 => Ok(Rc::new(Expr2::App(self.read(d)?, self.read(d)?))),
                6 => Ok(Rc::new(Expr2::Lam(self.read(d)?, self.read(d)?, self.read(d)?, self.read(d)?))),
                7 => Ok(Rc::new(Expr2::Pi(self.read(d)?, self.read(d)?, self.read(d)?, self.read(d)?))),
                8 => Ok(Rc::new(Expr2::Let(self.read(d)?, self.read(d)?, self.read(d)?, self.read(d)?))),
                9 => { let args = self.read(d)?; Ok(read_macro(self, d, args)?) },
                _ => throw(&format!("bad name {}", n))
            }
        })?;
        println!("read {:?}: expr", expr);
        Ok(expr)
    }
}

impl Deserialize<ModuleName> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<ModuleName> {
        let (r, n) = self.read(d)?;
        Ok(ModuleName{relative: r, name: n})
    }
}

impl Deserialize<ExportDecl> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<ExportDecl> {
        let e = ExportDecl {
            ns: self.read(d)?,
            as_: self.read(d)?,
            had_explicit: self.read(d)?,
            except_names: self.read(d)?,
            renames:  self.read(d)?
        };
        println!("read {:?}", e);
        Ok(e)
    }
}

impl Deserialize<ReducibilityHints> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<ReducibilityHints> {
        let k: u8 = self.read(d)?;
        Ok(match k {
            0 => { let b = self.read(d)?; ReducibilityHints::Regular(self.read(d)?, b) },
            1 => ReducibilityHints::Opaque,
            2 => ReducibilityHints::Abbrev,
            _ => throw("bad reducibility hints")?
        })
    }
}

impl Deserialize<Declaration> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<Declaration> {
        let k: u8 = self.read(d)?;
        let has_value = k & 1 != 0;
        let is_th_ax = k & 2 != 0;
        let is_trusted = k & 4 != 0;
        let n = self.read(d)?;
        let ps = self.read(d)?;
        let ty = self.read(d)?;
        Ok(if has_value {
            let val = self.read(d)?;
            if is_th_ax {
                Declaration::Thm{name: n, ps, ty, val}
            } else {
                Declaration::Defn{name: n, ps, ty, val, hints: self.read(d)?, is_trusted}
            }
        } else if is_th_ax { Declaration::Ax{name: n, ps, ty} }
        else { Declaration::Cnst{name: n, ps, ty, is_trusted} })
    }
}

impl<S> Deserialize<PosInfo> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<PosInfo> {
        Ok(PosInfo{line: ().read(d)?, col: ().read(d)?})
    }
}

impl<S> Deserialize<ReducibleStatus> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<ReducibleStatus> {
        let c = FromPrimitive::from_u8(self.read(d)?).ok_or(invalid("bad reducible"))?;
        println!("read {:?}: reducible_status", c);
        Ok(c)
    }
}

impl<S> Deserialize<ElabStrategy> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<ElabStrategy> {
        let c = FromPrimitive::from_u8(self.read(d)?).ok_or(invalid("bad elab strategy"))?;
        println!("read {:?}: elab strategy", c);
        Ok(c)
    }
}

fn read_attr_ext<T: io::Read>(s: &Deserializer, d: &mut T, n: Name) -> io::Result<AttrData> {
    match to_simple_name(&n) {
        Some("reducibility") => Ok(AttrData::Reducibility(().read(d)?)),
        Some("_refl_lemma") => Ok(AttrData::Basic),
        Some("instance") => Ok(AttrData::Basic),
        Some("simp") => Ok(AttrData::Basic),
        Some("wrapper_eq") => Ok(AttrData::Basic),
        Some("congr") => Ok(AttrData::Basic),
        Some("inline") => Ok(AttrData::Basic),
        Some("elab_strategy") => Ok(AttrData::ElabStrategy(s.read(d)?)),
        Some("derive") => Ok(AttrData::User(s.read(d)?)),
        _ => unimplemented!("unknown attr {}", n)
    }
}

impl Deserialize<AttrEntry> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<AttrEntry> {
        let attr = self.read(d)?;
        let prio = self.read(d)?;
        let decl = self.read(d)?;
        let deleted = self.read(d)?;
        let c =
            if deleted { AttrEntry{attr, prio, record: AttrRecord(decl, None)} }
            else { AttrEntry {
                attr: attr.clone(), prio,
                record: AttrRecord(decl, Some(read_attr_ext(self, d, attr)?))
            } };
        println!("read {:?}: attr_entry", c);
        Ok(c)
    }
}

impl Deserialize<InductiveDecl> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<InductiveDecl> {
        Ok(InductiveDecl {
            name: self.read(d)?,
            level_params: self.read(d)?,
            nparams: self.read(d)?,
            ty: self.read(d)?,
            rules: self.read(d)? })
    }
}

impl Deserialize<CompRule> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<CompRule> {
        Ok(CompRule { num_bu: self.read(d)?, comp_rhs: self.read(d)? })
    }
}

impl Deserialize<InductiveDefn> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<InductiveDefn> {
        Ok(InductiveDefn {
            num_ac_e: self.read(d)?,
            elim_prop: self.read(d)?,
            dep_elim: self.read(d)?,
            level_params: self.read(d)?,
            elim_type: self.read(d)?,
            decl: self.read(d)?,
            is_k: self.read(d)?,
            num_indices: self.read(d)?,
            is_trusted: self.read(d)?,
            comp_rules: self.read(d)? })

    }
}

impl<S> Deserialize<GInductiveKind> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<GInductiveKind> {
        let c = FromPrimitive::from_u8(self.read(d)?).ok_or(invalid("bad reducible"))?;
        println!("read {:?}: GInductiveKind", c);
        Ok(c)
    }
}

impl Deserialize<GInductiveEntry> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<GInductiveEntry> {
        let kind = self.read(d)?;
        let inner = self.read(d)?;
        let num_params = self.read(d)?;
        let num_indices = self.read(d)?;
        let inds = self.read(d)?;
        let mut intro_rules = readn(().read(d)?, || self.read(d))?;
        intro_rules.reverse();
        let e = GInductiveEntry {
            kind, inner, num_params, num_indices, inds, intro_rules,
            offsets: self.read(d)?,
            idx_to_ir_range: self.read(d)?,
            packs: self.read(d)?,
            unpacks: self.read(d)? };
        println!("read {:?}: GInductiveEntry", e);
        Ok(e)
    }
}

impl Deserialize<VMLocalInfo> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<VMLocalInfo> {
        Ok(VMLocalInfo {id: self.read(d)?, ty: self.read(d)?})
    }
}

impl Deserialize<VMInstr> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<VMInstr> {
        let k: u8 = self.read(d)?;
        let i = match k {
            0 => VMInstr::Push(self.read(d)?),
            1 => VMInstr::Move(self.read(d)?),
            2 => VMInstr::Ret,
            3 => VMInstr::Drop(self.read(d)?),
            4 => VMInstr::Goto(self.read(d)?, self.read(d)?),
            5 => VMInstr::SConstr(self.read(d)?),
            6 => VMInstr::Constr(self.read(d)?, self.read(d)?),
            7 => VMInstr::Num(self.read(d)?),
            8 => VMInstr::Destruct,
            9 => VMInstr::Cases2(self.read(d)?, self.read(d)?),
            10 => VMInstr::CasesN(self.read(d)?),
            11 => VMInstr::NatCases(self.read(d)?, self.read(d)?),
            12 => VMInstr::BuiltinCases(self.read(d)?, self.read(d)?),
            13 => VMInstr::Proj(self.read(d)?),
            14 => VMInstr::Apply,
            15 => VMInstr::InvokeGlobal(self.read(d)?),
            16 => VMInstr::InvokeBuiltin(self.read(d)?),
            17 => VMInstr::InvokeCFun(self.read(d)?),
            18 => VMInstr::Closure(self.read(d)?, self.read(d)?),
            19 => VMInstr::Unreachable,
            20 => VMInstr::Expr(self.read(d)?),
            21 => VMInstr::LocalInfo(self.read(d)?, self.read(d)?),
            _ => throw("bad opcode")?
        };
        println!("read {:?}: VMInstr", i);
        Ok(i)
    }
}

impl Deserialize<VMDecl> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<VMDecl> {
        let name = self.read(d)?;
        let arity = self.read(d)?;
        let code_sz = self.read(d)?;
        let pos_info = self.read(d)?;
        let args_info = self.read(d)?;
        let code = readn(code_sz, || self.read(d))?;
        Ok(VMDecl { kind: VMDeclKind::Bytecode(code),
            name, arity, args_info, pos_info, olean: None })
    }
}

impl Deserialize<ClassEntry> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<ClassEntry> {
        let k: u8 = self.read(d)?;
        Ok(match k {
            0 => ClassEntry::Class(self.read(d)?),
            1 => ClassEntry::Instance(self.read(d)?, self.read(d)?, self.read(d)?),
            2 => ClassEntry::Tracker(self.read(d)?, self.read(d)?),
            _ => throw("bad class entry")?
        })
    }
}

pub fn read_olean(mut f: File) -> io::Result<OLean> {
    let ds = Deserializer::new();
    let header: String = ds.read(&mut f)?;
    guard(header == "oleanfile", "incorrect header")?;
    let version: String = ds.read(&mut f)?;
    println!("version: {}", version);
    let _claimed_hash: u32 = ds.read(&mut f)?;
    let uses_sorry: bool = ds.read(&mut f)?;
    println!("uses_sorry: {}", uses_sorry);
    let imports: Vec<ModuleName> = ds.read(&mut f)?;
    println!("imports: {:?}", imports);
    let code: Box<[u8]> = read_blob(&mut f)?;
    println!("code: [{:?}]", code.len());
    Ok(OLean {version, uses_sorry, imports, code})
}

pub fn read_olean_modifications(mut d: &[u8]) -> io::Result<Vec<Modification>> {
    let ds = Deserializer::new();
    let mut mods = Vec::new();
    loop {
        let k: String = ds.read(&mut d)?;
        println!("reading {}", k);
        mods.push(match &*k {
            "EndFile" => return Ok(mods),
            "export_decl" => Modification::ExportDecl(ds.read(&mut d)?, ds.read(&mut d)?),
            "decl" => Modification::Decl { decl: ds.read(&mut d)?, trust_lvl: ds.read(&mut d)? },
            "PInfo" => Modification::PosInfo(ds.read(&mut d)?, ds.read(&mut d)?),
            "ind" => Modification::Inductive{ defn: ds.read(&mut d)?, trust_lvl: ds.read(&mut d)? },
            "auxrec" => Modification::AuxRec(ds.read(&mut d)?),
            "prt" => Modification::Protected(ds.read(&mut d)?),
            "gind" => Modification::GInd(ds.read(&mut d)?),
            "nspace" => Modification::NewNS(ds.read(&mut d)?),
            "VMR" => Modification::VMReserve(ds.read(&mut d)?, ds.read(&mut d)?),
            "VMC" => Modification::VMCode(ds.read(&mut d)?),
            "EqnL" => Modification::EqnLemmas(ds.read(&mut d)?),
            "SEqnL" => Modification::HasSimpleEqnLemma(ds.read(&mut d)?),
            "no_conf" => Modification::NoConf(ds.read(&mut d)?),
            "doc" => Modification::Doc(ds.read(&mut d)?, ds.read(&mut d)?),
            "ncomp" => Modification::Noncomputable(ds.read(&mut d)?),

            "TK" => Modification::TokenConfig{tk: ds.read(&mut d)?, prec: ds.read(&mut d)?},
            "ATTR" => Modification::Attr(ds.read(&mut d)?),
            "class" => Modification::Class(ds.read(&mut d)?),
            _ => return throw(&format!("unknown modification {}", k))
        })
    }
}
