use std::io;
use std::fs::File;
use std::rc::Rc;
use std::fmt;
use std::cell::RefCell;
use byteorder::{ReadBytesExt, BigEndian};
use num_traits::cast::FromPrimitive;
use num::bigint::BigInt;
use crate::types::*;
use crate::hasher;

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
        d.read_u8()
    }
}

impl<S> Deserialize<u32> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<u32> {
        let x: u8 = ().read(d)?;
        if x < 255 { Ok(x.into()) }
        else { d.read_u32::<BigEndian>() }
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
        let hi: u32 = ().read(d)?;
        let lo: u32 = ().read(d)?;
        Ok(((hi as u64) << 32) | (lo as u64))
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
        readn(().read(d)?, || self.read(d))
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
                return String::from_utf8(vec)
                    .map_err(|s| invalid(&format!("bad utf8, got {:?}", s.into_bytes())))
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
        Ok(if <S as Deserialize<bool>>::read(self, d)? {
            Some(self.read(d)?)
        } else { None })
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
        ObjectReader::read_core(self, d, |d, n| {
            match n {
                0 => Ok(Name::anon()),
                1 => Ok(Name::str(Name::anon(), self.read(d)?)),
                2 => Ok(Name::num(Name::anon(), self.read(d)?)),
                3 => Ok(Name::str(self.read(d)?, self.read(d)?)),
                4 => Ok(Name::num(self.read(d)?, self.read(d)?)),
                _ => throw(&format!("bad name {}", n))
            }
        })
    }
}

impl<S> Deserialize<BinderInfo> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<BinderInfo> {
        let c: u8 = self.read(d)?;
        Ok(if c & 4 != 0 { BinderInfo::Implicit }
        else if c & 2 != 0 { BinderInfo::StrictImplicit }
        else if c & 1 != 0 { BinderInfo::InstImplicit }
        else if c & 8 != 0 { BinderInfo::AuxDecl }
        else { BinderInfo::Default })
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
        ObjectReader::read_core(&self.lvl_reader, d, |d, _| {
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
        })
    }
}

impl Deserialize<EquationsHeader> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<EquationsHeader> {
        Ok(EquationsHeader {
            num_fns: self.read(d)?,
            is_private: self.read(d)?,
            is_meta: self.read(d)?,
            is_ncomp: self.read(d)?,
            is_lemma: self.read(d)?,
            is_aux_lemmas: self.read(d)?,
            prev_errors: self.read(d)?,
            gen_code: self.read(d)?,
            fn_names: self.read(d)?,
            fn_actual_names: self.read(d)? })
    }
}

fn read_macro<T: io::Read>(s: &Deserializer, d: &mut T, args: Vec<Expr>) -> io::Result<Expr> {
    let k: String = s.read(d)?;
    let m = match &*k {
        "Prenum" => MacroDef::Prenum(s.read(d)?),
        "STI" => MacroDef::StructureInstance {
            struct_: s.read(d)?, catchall: s.read(d)?, fields: s.read(d)? },
        "fieldN" => MacroDef::FieldNotation(s.read(d)?, s.read(d)?),
        "Annot" => MacroDef::Annot(s.read(d)?),
        "Choice" => MacroDef::Choice,
        "CNatM" => MacroDef::NatValue(s.read(d)?),
        "RecFn" => MacroDef::RecFn(s.read(d)?),
        "Proj" => MacroDef::Proj {
            i_name: s.read(d)?, c_name: s.read(d)?, proj_name: s.read(d)?,
            idx: s.read(d)?, ps: s.read(d)?, ty: s.read(d)?, val: s.read(d)? },
        "Eqns" => MacroDef::Equations(s.read(d)?),
        "Eqn" => MacroDef::Equation { ignore_if_unused: s.read(d)? },
        "NEqn" => MacroDef::NoEquation,
        "EqnR" => MacroDef::EquationsResult,
        "AsPat" => MacroDef::AsPattern,
        "Quote" => MacroDef::ExprQuote { val: s.read(d)?, reflected: s.read(d)? },
        "Sorry" => MacroDef::Sorry { synth: s.read(d)? },
        "Str" => MacroDef::String(s.read(d)?),
        "ACApp" => MacroDef::ACApp,
        "PermAC" => MacroDef::PermAC,
        "TyE" => MacroDef::TypedExpr,
        _ => unimplemented!("unknown macro {}", k)
    };
    guard(check_macro(&m, &args), "bad macro args")?;
    Ok(Rc::new(Expr2::Macro(m, args)))
}

// These are un-inlined from Deserialize<Expr> because the intermediates
// in all the match branches bloat the stack frame, and this function is called deeply
fn read_var<T: io::Read>(d: &mut T) -> io::Result<Expr> {
    Ok(Rc::new(Expr2::Var(().read(d)?))) }
fn read_sort<T: io::Read>(s: &Deserializer, d: &mut T) -> io::Result<Expr> {
    Ok(Rc::new(Expr2::Sort(s.read(d)?))) }
fn read_const<T: io::Read>(s: &Deserializer, d: &mut T) -> io::Result<Expr> {
    Ok(Rc::new(Expr2::Const(s.read(d)?, s.read(d)?))) }
fn read_mvar<T: io::Read>(s: &Deserializer, d: &mut T) -> io::Result<Expr> {
    Ok(Rc::new(Expr2::MVar(s.read(d)?, s.read(d)?, s.read(d)?))) }
fn read_local<T: io::Read>(s: &Deserializer, d: &mut T) -> io::Result<Expr> {
    Ok(Rc::new(Expr2::Local(s.read(d)?, s.read(d)?, s.read(d)?, s.read(d)?))) }
fn read_app<T: io::Read>(s: &Deserializer, d: &mut T) -> io::Result<Expr> {
    Ok(Rc::new(Expr2::App(s.read(d)?, s.read(d)?))) }
fn read_lam<T: io::Read>(s: &Deserializer, d: &mut T) -> io::Result<Expr> {
    Ok(Rc::new(Expr2::Lam(s.read(d)?, s.read(d)?, s.read(d)?, s.read(d)?))) }
fn read_pi<T: io::Read>(s: &Deserializer, d: &mut T) -> io::Result<Expr> {
    Ok(Rc::new(Expr2::Pi(s.read(d)?, s.read(d)?, s.read(d)?, s.read(d)?))) }
fn read_let<T: io::Read>(s: &Deserializer, d: &mut T) -> io::Result<Expr> {
    Ok(Rc::new(Expr2::Let(s.read(d)?, s.read(d)?, s.read(d)?, s.read(d)?))) }
fn read_macro_expr<T: io::Read>(s: &Deserializer, d: &mut T) -> io::Result<Expr> {
    let args = s.read(d)?; Ok(read_macro(s, d, args)?) }

impl Deserialize<Expr> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<Expr> {
        ObjectReader::read_core(&self.expr_reader, d, |d, n| {
            match n {
                0 => read_var(d),
                1 => read_sort(self, d),
                2 => read_const(self, d),
                3 => read_mvar(self, d),
                4 => read_local(self, d),
                5 => read_app(self, d),
                6 => read_lam(self, d),
                7 => read_pi(self, d),
                8 => read_let(self, d),
                9 => read_macro_expr(self, d),
                _ => throw(&format!("bad name {}", n))
            }
        })
    }
}

impl Deserialize<ModuleName> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<ModuleName> {
        Ok(ModuleName{relative: self.read(d)?, name: self.read(d)?})
    }
}

impl Deserialize<ExportDecl> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<ExportDecl> {
        Ok(ExportDecl {
            ns: self.read(d)?,
            as_: self.read(d)?,
            had_explicit: self.read(d)?,
            except_names: self.read(d)?,
            renames:  self.read(d)?
        })
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
        FromPrimitive::from_u8(self.read(d)?).ok_or(invalid("bad reducible"))
    }
}

impl<S> Deserialize<ElabStrategy> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<ElabStrategy> {
        Ok(FromPrimitive::from_u8(self.read(d)?).unwrap_or(ElabStrategy::Simple))
    }
}

fn read_attr_ext<T: io::Read>(s: &Deserializer, d: &mut T, n: Name) -> io::Result<AttrData> {
    Ok(match n.to_simple_name() {
        Some("_refl_lemma") => AttrData::Basic,
        Some("simp") => AttrData::Basic,
        Some("wrapper_eq") => AttrData::Basic,
        Some("congr") => AttrData::Basic,
        Some("elab_strategy") => AttrData::ElabStrategy(s.read(d)?),
        Some("elab_with_expected_type") => AttrData::Basic,
        Some("elab_as_eliminator") => AttrData::Basic,
        Some("elab_simple") => AttrData::Basic,
        Some("parsing_only") => AttrData::Basic,
        Some("pp_using_anonymous_constructor") => AttrData::Basic,
        Some("user_command") => AttrData::Basic,
        Some("user_notation") => AttrData::Basic,
        Some("user_attribute") => AttrData::Basic,
        Some("algebra") => AttrData::Basic,
        Some("class") => AttrData::Basic,
        Some("instance") => AttrData::Basic,
        Some("inline") => AttrData::Basic,
        Some("inverse") => AttrData::Basic,
        Some("pattern") => AttrData::Basic,
        Some("reducibility") => AttrData::Reducibility(().read(d)?),
        Some("reducible") => AttrData::Basic,
        Some("semireducible") => AttrData::Basic,
        Some("irreducible") => AttrData::Basic,
        Some("refl") => AttrData::Basic,
        Some("symm") => AttrData::Basic,
        Some("trans") => AttrData::Basic,
        Some("subst") => AttrData::Basic,
        Some("intro") => AttrData::Intro{eager: ().read(d)?},
        Some("hole_command") => AttrData::Basic,
        Some("no_inst_pattern") => AttrData::Basic,
        Some("vm_monitor") => AttrData::Basic,
        Some("unify") => AttrData::Basic,
        Some("recursor") => AttrData::Indices(().read(d)?),
        _ =>
            if n == name![_simp.sizeof] { AttrData::Basic }
            else { AttrData::User(s.read(d)?) }
    })
}

impl Deserialize<AttrEntry> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<AttrEntry> {
        let attr = self.read(d)?;
        let prio = self.read(d)?;
        let decl = self.read(d)?;
        let deleted = self.read(d)?;
        Ok(if deleted {
            AttrEntry{attr, prio, record: AttrRecord(decl, None)} }
        else { AttrEntry {
            attr: attr.clone(), prio,
            record: AttrRecord(decl, Some(read_attr_ext(self, d, attr)?)) } })
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
        FromPrimitive::from_u8(self.read(d)?).ok_or(invalid("bad ginductive kind"))
    }
}

impl Deserialize<GInductiveEntry> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<GInductiveEntry> {
        let kind = self.read(d)?;
        let inner = self.read(d)?;
        let num_params = self.read(d)?;
        let num_indices = self.read(d)?;
        let inds: Vec<Name> = self.read(d)?;
        let mut intro_rules = readn(inds.len(), || self.read(d))?;
        intro_rules.reverse();
        Ok(GInductiveEntry {
            kind, inner, num_params, num_indices, inds, intro_rules,
            offsets: self.read(d)?,
            idx_to_ir_range: self.read(d)?,
            packs: self.read(d)?,
            unpacks: self.read(d)? })
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
        Ok(match k {
            0 => VMInstr::Push(self.read(d)?),
            1 => VMInstr::Move(self.read(d)?),
            2 => VMInstr::Ret,
            3 => VMInstr::Drop(self.read(d)?),
            4 => VMInstr::Goto(self.read(d)?),
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
        })
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

impl Deserialize<ProjectionInfo> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<ProjectionInfo> {
        Ok(ProjectionInfo {
            constr: self.read(d)?,
            nparams: self.read(d)?,
            i: self.read(d)?,
            inst_implicit: self.read(d)? })
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

impl Deserialize<Action> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<Action> {
        let k: u8 = self.read(d)?;
        Ok(match k {
            0 => Action::Skip,
            1 => Action::Expr{rbp: self.read(d)?},
            2 => Action::Exprs {
                sep: self.read(d)?,
                rec: self.read(d)?,
                ini: self.read(d)?,
                is_foldr: self.read(d)?,
                rbp: self.read(d)?,
                terminator: self.read(d)? },
            3 => Action::Binder{rbp: self.read(d)?},
            4 => Action::Binders{rbp: self.read(d)?},
            5 => Action::ScopedExpr {
                rec: self.read(d)?,
                rbp: self.read(d)?,
                use_lambda: self.read(d)? },
            6 => throw("Ext actions never appear in olean files")?,
            _ => throw("bad action")?
        })
    }
}

impl Deserialize<Transition> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<Transition> {
        Ok(Transition{tk: self.read(d)?, pp: self.read(d)?, act: self.read(d)?})
    }
}

impl<S> Deserialize<NotationEntryGroup> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<NotationEntryGroup> {
        FromPrimitive::from_u8(self.read(d)?).ok_or(invalid("bad notation entry group"))
    }
}

impl Deserialize<NotationEntry> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<NotationEntry> {
        let k: u8 = self.read(d)?;
        let overload = self.read(d)?;
        let parse_only = self.read(d)?;
        let expr = self.read(d)?;
        Ok(if k == 2 {
            NotationEntry {
                kind: NotationEntryKind::Numeral(self.read(d)?),
                expr, overload, parse_only,
                group: NotationEntryGroup::Main }
        } else {
            NotationEntry {
                group: self.read(d)?,
                kind: NotationEntryKind::Reg {
                    is_nud: match k { 0 => true, 1 => false, _ => throw("bad notation entry")? },
                    transitions: self.read(d)?,
                    prio: self.read(d)? },
                expr, overload, parse_only }
        })
    }
}

impl Deserialize<InverseEntry> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<InverseEntry> {
        Ok(InverseEntry {
            decl: self.read(d)?,
            arity: self.read(d)?,
            inv: self.read(d)?,
            inv_arity: self.read(d)?,
            lemma: self.read(d)? })
    }
}

impl<S> Deserialize<OpKind> for S {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<OpKind> {
        FromPrimitive::from_u8(self.read(d)?).ok_or(invalid("bad op kind"))
    }
}

impl Deserialize<RecursorInfo> for Deserializer {
    fn read<T: io::Read>(&self, d: &mut T) -> io::Result<RecursorInfo> {
        Ok(RecursorInfo {
            rec: self.read(d)?,
            ty: self.read(d)?,
            dep_elim: self.read(d)?,
            recursive: self.read(d)?,
            num_args: self.read(d)?,
            major_pos: self.read(d)?,
            univ_pos: self.read(d)?,
            params_pos: self.read(d)?,
            indices_pos: self.read(d)?,
            produce_motive: self.read(d)? })
    }
}

pub fn read_olean(mut f: File) -> io::Result<OLean> {
    let ds = Deserializer::new();
    let header: String = ds.read(&mut f)?;
    guard(header == "oleanfile", "incorrect header")?;
    let version: String = ds.read(&mut f)?;
    let claimed_hash: u32 = ds.read(&mut f)?;
    let uses_sorry = ds.read(&mut f)?;
    let imports = ds.read(&mut f)?;
    let code = read_blob(&mut f)?;
    guard(claimed_hash == hasher::hash(&code), "incorrect hash")?;
    Ok(OLean { version, uses_sorry, imports, code })
}

pub fn read_olean_modifications(mut d: &[u8]) -> io::Result<Vec<Modification>> {
    let ds = Deserializer::new();
    let mut mods = Vec::new();
    loop {
        let k: String = ds.read(&mut d)?;
        mods.push(match &*k {
            "EndFile" => return Ok(mods),
            "export_decl" => Modification::ExportDecl(ds.read(&mut d)?, ds.read(&mut d)?),
            "decl" => Modification::Decl { decl: ds.read(&mut d)?, trust_lvl: ds.read(&mut d)? },
            "PInfo" => Modification::PosInfo(ds.read(&mut d)?, ds.read(&mut d)?),
            "ind" => Modification::Inductive { defn: ds.read(&mut d)?, trust_lvl: ds.read(&mut d)? },
            "auxrec" => Modification::AuxRec(ds.read(&mut d)?),
            "prt" => Modification::Protected(ds.read(&mut d)?),
            "prv" => Modification::Private { name: ds.read(&mut d)?, real: ds.read(&mut d)? },
            "gind" => Modification::GInd(ds.read(&mut d)?),
            "nspace" => Modification::NewNS(ds.read(&mut d)?),
            "VMR" => Modification::VMReserve(ds.read(&mut d)?, ds.read(&mut d)?),
            "VMC" => Modification::VMCode(ds.read(&mut d)?),
            "VMMonitor" => Modification::VMMonitor(ds.read(&mut d)?),
            "EqnL" => Modification::EqnLemmas(ds.read(&mut d)?),
            "SEqnL" => Modification::HasSimpleEqnLemma(ds.read(&mut d)?),
            "no_conf" => Modification::NoConf(ds.read(&mut d)?),
            "doc" => Modification::Doc(ds.read(&mut d)?, ds.read(&mut d)?),
            "ncomp" => Modification::Noncomputable(ds.read(&mut d)?),
            "proj" => Modification::Proj(ds.read(&mut d)?, ds.read(&mut d)?),
            "decl_trace" => Modification::DeclTrace(ds.read(&mut d)?),
            "USR_CMD" => Modification::UserCommand(ds.read(&mut d)?),
            "USR_NOTATION" => Modification::UserNotation(ds.read(&mut d)?),
            "USR_ATTR" => Modification::UserAttribute(ds.read(&mut d)?),
            "HOLE_CMD" => Modification::HoleCommand(ds.read(&mut d)?),
            "quot" => Modification::Quot,
            "native_module_path" => Modification::NativeModulePath(ds.read(&mut d)?),
            "key_eqv" => Modification::KeyEquivalence(ds.read(&mut d)?, ds.read(&mut d)?),

            "TK" => Modification::Token(KToken{tk: ds.read(&mut d)?, prec: ds.read(&mut d)?}),
            "NOTA" => Modification::Notation(ds.read(&mut d)?),
            "ATTR" => Modification::Attr(ds.read(&mut d)?),
            "class" => Modification::Class(ds.read(&mut d)?),
            "inverse" => Modification::Inverse(ds.read(&mut d)?),
            "REL" => Modification::Relation(ds.read(&mut d)?, ds.read(&mut d)?),
            "UNIFICATION_HINT" => Modification::UnificationHint(ds.read(&mut d)?, ds.read(&mut d)?),
            "UREC" => Modification::UserRecursor(ds.read(&mut d)?),
            "active_export_decls" => return throw("active_export_decls should not appear in olean files"),
            _ => return throw(&format!("unknown modification {}", k))
        })
    }
}
