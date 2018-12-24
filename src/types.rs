use std::rc::Rc;
use std::fmt;
use std::fmt::{Debug, Display, Formatter};
use std::ops::Deref;
use num::bigint::BigInt;

#[derive(PartialEq, Eq, Hash, Clone)] pub struct Name(Rc<Name2>);

#[derive(PartialEq, Eq, Hash)] pub enum Name2 {
    Anon,
    Str(Name, String),
    Num(Name, u32)
}

impl Name2 {
    pub fn is_anon(&self) -> bool {
        if let Name2::Anon = self { true } else { false }
    }

    pub fn to_simple_name(&self) -> Option<&str> {
        if let Name2::Str(n2, ref s) = self {
            if n2.0.is_anon() {Some(s)} else {None}
        } else {None}
    }

    pub fn parent(&self) -> Name {
        match self {
            Name2::Anon => Name::anon(),
            Name2::Str(n, _) => n.clone(),
            Name2::Num(n, _) => n.clone()
        }
    }
}

impl Name {
    pub fn new(n: Name2) -> Name { Name(Rc::new(n)) }
    pub fn anon() -> Name { Name::new(Name2::Anon) }
    pub fn is_anon(&self) -> bool { self.0.is_anon() }
    pub fn parent(&self) -> Name { self.0.parent() }
    pub fn str(self, s: String) -> Name { Name::new(Name2::Str(self, s)) }
    pub fn num(self, s: u32) -> Name { Name::new(Name2::Num(self, s)) }

    pub fn append(self, other: &Name2) -> Name {
        match other {
            Name2::Anon => self,
            Name2::Str(n, s) => self.append(n).str(s.clone()),
            Name2::Num(n, s) => self.append(n).num(s.clone())
        }
    }
}

impl Deref for Name {
    type Target = Name2;
    fn deref(&self) -> &Name2 { self.0.deref() }
}

impl From<&[&str]> for Name {
    fn from(ns: &[&str]) -> Name {
        match ns.split_last() {
            None => Name::anon(),
            Some((&s, ns)) => Name::str(ns.into(), String::from(s))
        }
    }
}

impl From<&str> for Name {
    fn from(n: &str) -> Name { Name::str(Name::anon(), String::from(n)) }
}

macro_rules! name {
    [$e:expr; $x:ident] => {
        Name::str($e, String::from(stringify!($x)))
    };
    [$e:expr; $x:ident . $($rest:tt).*] => {
        name![Name::str($e, String::from(stringify!($x))); $($rest).*]
    };
    [$($ns:tt).*] => { name![Name::anon(); $($ns).*] };
}

pub fn parse_name(ns: &str) -> Name {
    let mut n = Name::anon();
    for s in ns.split('.') { n = Name::str(n, s.to_string()) }
    n
}

impl Display for Name2 {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Name2::Anon => write!(f, "[anonymous]"),
            Name2::Str(n, s) =>
                if n.is_anon() { f.write_str(&s) }
                else { write!(f, "{}.{}", n, s) },
            Name2::Num(ref n, s) =>
                if n.is_anon() { write!(f, "{}", s) }
                else { write!(f, "{}.{}", n, s) }
        }
    }
}

impl Debug for Name2 {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result { Display::fmt(self, f) }
}

impl Display for Name {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result { Display::fmt(self.deref(), f) }
}

impl fmt::Debug for Name {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result { Debug::fmt(self.deref(), f) }
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

#[derive(Debug)] pub struct EquationsHeader {
    pub num_fns: u32,
    pub is_private: bool,
    pub is_meta: bool,
    pub is_ncomp: bool,
    pub is_lemma: bool,
    pub is_aux_lemmas: bool,
    pub prev_errors: bool,
    pub gen_code: bool,
    pub fn_names: Vec<Name>,
    pub fn_actual_names: Vec<Name>
}

#[derive(Debug)] pub enum MacroDef {
    Prenum(BigInt),
    StructureInstance {struct_: Name, catchall: bool, fields: Vec<Name>},
    FieldNotation(Name, u32),
    Annot(Name),
    Choice,
    NatValue(BigInt),
    RecFn(Name),
    Proj {
        i_name: Name, c_name: Name, proj_name: Name,
        idx: u32, ps: Vec<Name>, ty: Expr, val: Expr },
    Equations(EquationsHeader),
    Equation{ignore_if_unused: bool},
    NoEquation,
    EquationsResult,
    AsPattern,
    ExprQuote{val: Expr, reflected: bool},
    Sorry{synth: bool},
    String(String),
    ACApp,
    PermAC,
    TypedExpr,
}

pub fn check_macro(m: &MacroDef, args: &Vec<Expr>) -> bool {
    match m {
        MacroDef::StructureInstance {fields, ..} => args.len() >= fields.len(),
        MacroDef::FieldNotation{..} => args.len() == 1,
        MacroDef::Annot{..} => args.len() == 1,
        MacroDef::Choice => args.len() > 1,
        MacroDef::NatValue{..} => args.len() == 0,
        MacroDef::RecFn{..} => args.len() == 1,
        MacroDef::Proj{..} => args.len() == 1,
        MacroDef::Equation{..} => args.len() == 2,
        MacroDef::NoEquation => args.len() == 0,
        MacroDef::AsPattern => args.len() == 2,
        MacroDef::ExprQuote{..} => args.len() == 0,
        MacroDef::Sorry{..} => args.len() == 1,
        MacroDef::String{..} => args.len() == 0,
        MacroDef::PermAC => args.len() == 4,
        MacroDef::TypedExpr => args.len() == 2,
        _ => true
    }
}

#[derive(Debug)] pub struct ModuleName {
    pub relative: Option<u32>,
    pub name: Name
}

impl ModuleName {
    pub fn resolve(&self, mut base: Name) -> Name {
        match &self.relative {
            None => self.name.clone(),
            Some(n) => {
                for _ in 0..n+1 { base = base.parent() }
                base.append(&self.name)
            }
        }
    }
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
    pub comp_rhs: Expr
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
    Goto(u32),
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

#[derive(Debug)] pub struct ProjectionInfo {
    pub constr: Name,
    pub nparams: u32,
    pub i: u32,
    pub inst_implicit: bool
}

#[derive(Debug)] pub enum Action {
    Skip,
    Expr{rbp: u32},
    Exprs {
        sep: Name,
        rec: Expr,
        ini: Option<Expr>,
        is_foldr: bool,
        rbp: u32,
        terminator: Option<Name> },
    Binder{rbp: u32},
    Binders{rbp: u32},
    ScopedExpr {
        rec: Expr,
        rbp: u32,
        use_lambda: bool }
}

#[derive(Debug)] pub struct Transition {
    pub tk: Name,
    pub pp: Name,
    pub act: Action
}

#[derive(Debug)] pub enum NotationEntryKind {
    Reg {
        is_nud: bool,
        transitions: Vec<Transition>,
        prio: u32
    },
    Numeral(BigInt)
}

#[derive(Debug, FromPrimitive)] pub enum NotationEntryGroup { Main, Reserve }

#[derive(Debug)] pub struct NotationEntry {
    pub kind: NotationEntryKind,
    pub expr: Expr,
    pub overload: bool,
    pub group: NotationEntryGroup,
    pub parse_only: bool
}

#[derive(Debug)] pub struct InverseEntry {
    pub decl: Name,
    pub arity: u32,
    pub inv: Name,
    pub inv_arity: u32,
    pub lemma: Name
}

#[derive(Debug, FromPrimitive)] pub enum OpKind { Relation, Subst, Trans, Refl, Symm }

#[derive(Debug)] pub struct RecursorInfo {
    pub rec: Name,
    pub ty: Name,
    pub dep_elim: bool,
    pub recursive: bool,
    pub num_args: u32,
    pub major_pos: u32,
    pub univ_pos: Vec<u32>,
    pub params_pos: Vec<Option<u32>>,
    pub indices_pos: Vec<u32>,
    pub produce_motive: Vec<bool>
}

#[derive(Clone, Debug)] pub struct KToken {
    pub tk: String,
    pub prec: Option<u32>
}

#[derive(Debug)] pub enum Modification {
    ExportDecl(Name, ExportDecl),
    Decl {decl: Declaration, trust_lvl: u32},
    PosInfo(Name, PosInfo),
    Inductive{defn: InductiveDefn, trust_lvl: u32},
    AuxRec(Name),
    Protected(Name),
    Private{name: Name, real: Name},
    GInd(GInductiveEntry),
    NewNS(Name),
    VMReserve(Name, u32),
    VMCode(VMDecl),
    VMMonitor(Name),
    EqnLemmas(Name),
    HasSimpleEqnLemma(Name),
    NoConf(Name),
    Doc(Name, String),
    Noncomputable(Name),
    Proj(Name, ProjectionInfo),
    DeclTrace(Name),
    UserCommand(Name),
    UserNotation(Name),
    UserAttribute(Name),
    HoleCommand(Name),
    Quot,
    NativeModulePath(Name),
    KeyEquivalence(Name, Name),

    Token(KToken),
    Notation(NotationEntry),
    Attr(AttrEntry),
    Class(ClassEntry),
    Inverse(InverseEntry),
    Relation(OpKind, Name),
    UnificationHint(Name, u32),
    UserRecursor(RecursorInfo)
}

#[derive(Debug)] pub struct OLean {
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
