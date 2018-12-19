use std::rc::Rc;
use std::fmt;
use num::bigint::BigInt;

pub type Name = Rc<Name2>;
#[derive(PartialEq, Eq)] pub enum Name2 {
    Anon,
    Str(Name, String),
    Num(Name, u32)
}

pub fn is_anon(n: &Name2) -> bool {
    if let Name2::Anon = n { true } else { false }
}

pub fn to_simple_name(n: &Name2) -> Option<&str> {
    if let Name2::Str(n2, ref s) = n {
        if is_anon(n2) {Some(s)} else {None}
    } else {None}
}

pub fn mk_name(ns: &[&str]) -> Name {
    Rc::new(match ns.split_last() {
        None => Name2::Anon,
        Some((&s, ref ns)) => Name2::Str(mk_name(ns), String::from(s))
    })
}

impl fmt::Display for Name2 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Name2::Anon => write!(f, "[anonymous]"),
            Name2::Str(n, s) =>
                if is_anon(n) { f.write_str(&s) }
                else { write!(f, "{}.{}", n, s) },
            Name2::Num(ref n, s) =>
                if is_anon(n) { write!(f, "{}", s) }
                else { write!(f, "{}.{}", n, s) }
        }
    }
}

impl fmt::Debug for Name2 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

pub type Level = Rc<Level2>;
#[derive(Debug)] pub enum Level2 {
    Zero,
    Succ(Level),
    Max(Level, Level),
    IMax(Level, Level),
    Param(Name),
    Meta(Name)
}

#[derive(Debug)] pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
    AuxDecl
}

pub type Expr = Rc<Expr2>;
#[derive(Debug)] pub enum Expr2 {
    Var(u32),
    Sort(Level),
    Const(Name, Vec<Level>),
    MVar(Name, Name, Expr),
    Local(Name, Name, BinderInfo, Expr),
    App(Expr, Expr),
    Lam(Name, BinderInfo, Expr, Expr),
    Pi(Name, BinderInfo, Expr, Expr),
    Let(Name, Expr, Expr, Expr),
    Macro(MacroDef, Vec<Expr>)
}

#[derive(Debug)] pub enum MacroDef {
    Prenum(BigInt),
    StructureInstance {struct_: Name, catchall: bool, fields: Vec<Name>},
    ExprQuote{val: Expr, reflected: bool},
    Annot(Name),
}

pub fn check_macro(m: &MacroDef, args: &Vec<Expr>) -> bool {
    match m {
        MacroDef::StructureInstance {fields, ..} => args.len() >= fields.len(),
        MacroDef::ExprQuote{..} => args.len() == 0,
        MacroDef::Annot{..} => args.len() == 1,
        _ => true
    }
}

#[derive(Debug)] pub struct ModuleName {
    pub relative: Option<u32>,
    pub name: Name
}

#[derive(Debug)] pub struct ExportDecl {
    pub ns: Name,
    pub as_: Name,
    pub had_explicit: bool,
    pub except_names: Vec<Name>,
    pub renames: Vec<(Name, Name)>
}

#[derive(Debug)] pub enum ReducibilityHints {
    Regular(u32, bool),
    Opaque,
    Abbrev
}

#[derive(Debug)] pub enum Declaration {
    Defn{name: Name, ps: Vec<Name>, ty: Expr, val: Expr, hints: ReducibilityHints, is_trusted: bool},
    Thm{name: Name, ps: Vec<Name>, ty: Expr, val: Expr},
    Cnst{name: Name, ps: Vec<Name>, ty: Expr, is_trusted: bool},
    Ax{name: Name, ps: Vec<Name>, ty: Expr}
}

#[derive(Debug)] pub struct PosInfo { pub line: u32, pub col: u32 }

#[derive(Debug, FromPrimitive)]
pub enum ReducibleStatus { Reducible, Semireducible, Irreducible }

#[derive(Debug, FromPrimitive)]
pub enum ElabStrategy { Simple, WithExpectedType, AsEliminator }

#[derive(Debug)] pub enum AttrData {
    Basic,
    Reducibility(ReducibleStatus),
    ElabStrategy(ElabStrategy),
    Intro{eager: bool},
    Indices(Vec<u32>),
    User(Expr)
}

#[derive(Debug)] pub struct AttrRecord(pub Name, pub Option<AttrData>);

#[derive(Debug)] pub struct AttrEntry {
    pub attr: Name,
    pub prio: u32,
    pub record: AttrRecord
}

#[derive(Debug)] pub struct InductiveDecl {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub nparams: u32,
    pub ty: Expr,
    pub rules: Vec<(Name, Expr)>
}

#[derive(Debug)] pub struct CompRule {
    pub num_bu: u32,
    pub comp_rhs: u32
}

#[derive(Debug)] pub struct InductiveDefn {
    pub num_ac_e: u32,
    pub elim_prop: bool,
    pub dep_elim: bool,
    pub level_params: Vec<Name>,
    pub elim_type: Expr,
    pub decl: InductiveDecl,
    pub is_k: bool,
    pub num_indices: u32,
    pub is_trusted: bool,
    pub comp_rules: Vec<CompRule>
}

#[derive(Debug, FromPrimitive)]
pub enum GInductiveKind { Basic, Mutual, Nested }

#[derive(Debug)] pub struct GInductiveEntry {
    pub kind: GInductiveKind,
    pub inner: bool,
    pub num_params: u32,
    pub num_indices: Vec<u32>,
    pub inds: Vec<Name>,
    pub intro_rules: Vec<Vec<Name>>,
    pub offsets: Vec<u32>,
    pub idx_to_ir_range: Vec<(u32, u32)>,
    pub packs: Vec<Name>,
    pub unpacks: Vec<Name>
}

#[derive(Debug)] pub struct VMLocalInfo {
    pub id: Name,
    pub ty: Option<Expr>
}

#[derive(Debug)] pub enum VMInstr {
    Push(u32),
    Move(u32),
    Ret,
    Drop(u32),
    Goto(u32, u32),
    SConstr(u32),
    Constr(u32, u32),
    Num(BigInt),
    Destruct,
    Cases2(u32, u32),
    CasesN(Vec<u32>),
    NatCases(u32, u32),
    BuiltinCases(Name, Vec<u32>),
    Proj(u32),
    Apply,
    InvokeGlobal(Name),
    InvokeBuiltin(Name),
    InvokeCFun(Name),
    Closure(Name, u32),
    Unreachable,
    Expr(Expr),
    LocalInfo(u32, VMLocalInfo)
}

#[derive(Debug)] pub enum VMDeclKind {
    Bytecode(Vec<VMInstr>),
    // Builtin,
    // CFun
}

#[derive(Debug)] pub struct VMDecl {
    pub kind: VMDeclKind,
    pub name: Name,
    pub arity: u32,
    pub args_info: Vec<VMLocalInfo>,
    pub pos_info: Option<PosInfo>,
    pub olean: Option<String>
}

#[derive(Debug)] pub enum ClassEntry {
    Class(Name),
    Instance(Name, Name, u32),
    Tracker(Name, Name),
}

#[derive(Debug)] pub enum Modification {
    ExportDecl(Name, ExportDecl),
    Decl {decl: Declaration, trust_lvl: u32},
    PosInfo(Name, PosInfo),
    Inductive{defn: InductiveDefn, trust_lvl: u32},
    AuxRec(Name),
    Protected(Name),
    GInd(GInductiveEntry),
    NewNS(Name),
    VMReserve(Name, u32),
    VMCode(VMDecl),
    EqnLemmas(Name),
    HasSimpleEqnLemma(Name),
    NoConf(Name),
    Doc(Name, String),
    Noncomputable(Name),

    TokenConfig{tk: String, prec: u32},
    Attr(AttrEntry),
    Class(ClassEntry)
}

pub struct OLean {
    pub version: String,
    pub uses_sorry: bool,
    pub imports: Vec<ModuleName>,
    pub code: Box<[u8]>
}

impl fmt::Display for OLean {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "version: {}", self.version)?;
        writeln!(f, "uses sorry: {}", self.uses_sorry)?;
        writeln!(f, "imports: {:?}", self.imports)
    }
}
