import system.io
open io

structure equations_header :=
(num_fns : unsigned)
(is_private : bool)
(is_meta : bool)
(is_ncomp : bool)
(is_lemma : bool)
(is_aux_lemmas : bool)
(prev_errors : bool)
(gen_code : bool)
(fn_names : list name)
(fn_actual_names : list name)

meta mutual inductive macro_def', expr'
with macro_def' : Type
| prenum (n : ℤ)
| struct_inst (struct : name) (catchall : bool) (fields : list name)
| field_notation (name : name) (idx : unsigned)
| annot (name : name)
| choice
| nat_value (n : ℤ)
| rec_fn (name : name)
| proj (i c proj : name) (idx : unsigned) (ps : list name) (ty val : expr')
| equations (header : equations_header)
| equation (ignore_if_unused : bool)
| no_equation
| equations_result
| as_pattern
| expr_quote (val : expr') (reflected : bool)
| sorry_ (synth : bool)
| string (s : string)
| ac_app
| perm_ac
| typed_expr

with expr' : Type
| var      {} : nat → expr'
| sort     {} : level → expr'
| const    {} : name → list level → expr'
| mvar        : name → name → expr' → expr'
| local_const : name → name → binder_info → expr' → expr'
| app         : expr' → expr' → expr'
| lam         : name → binder_info → expr' → expr' → expr'
| pi          : name → binder_info → expr' → expr' → expr'
| elet        : name → expr' → expr' → expr' → expr'
| macro       : macro_def' → list expr' → expr'

private meta def ls := λ xs, format.join (list.intersperse " " xs)
private meta def p := format.paren ∘ ls
private meta def br : list format → format
| [] := to_fmt "⟨⟩"
| xs := to_fmt "⟨" ++
  format.group (format.nest 1 $ format.join $
    list.intersperse ("," ++ format.line) $ xs.map to_fmt) ++ to_fmt "⟩"

meta instance : has_to_format equations_header :=
⟨λ ⟨e1,e2,e3,e4,e5,e6,e7,e8,e9,e10⟩, br [
  to_fmt e1, to_fmt e2, to_fmt e3, to_fmt e4, to_fmt e5,
  to_fmt e6, to_fmt e7, to_fmt e8, to_fmt e9, to_fmt e10]⟩

section
open macro_def' expr'

meta mutual def macro_def'.to_fmt, expr'.to_fmt
with macro_def'.to_fmt : macro_def' → format
| (prenum n) := ls ["prenum", to_string n]
| (struct_inst n c f) := ls ["struct_inst", to_fmt n, to_fmt c, to_fmt f]
| (field_notation n i) := ls ["field_notation", to_fmt n, to_fmt i]
| (annot n) := ls ["annot", to_fmt n]
| choice := "choice"
| (nat_value n) := ls ["nat_value", to_string n]
| (rec_fn n) := ls ["rec_fn", to_fmt n]
| (proj i c pj ix ps ty v) := ls ["proj", to_fmt i, to_fmt c,
  to_fmt pj, to_fmt ix, to_fmt ps, ty.to_fmt, v.to_fmt]
| (equations h) := ls ["equations", to_fmt h]
| (equation i) := ls ["equation", to_fmt i]
| no_equation := "no_equation"
| equations_result := "equations_result"
| as_pattern := "as_pattern"
| (expr_quote v r) := ls ["expr_quote", v.to_fmt, to_fmt r]
| (sorry_ s) := ls ["sorry", to_fmt s]
| (string s) := ls ["string", to_fmt s]
| ac_app := "ac_app"
| perm_ac := "perm_ac"
| typed_expr := "typed_expr"

with expr'.to_fmt : expr' → format
| (var n) := p ["var", to_fmt n]
| (sort l) := p ["sort", to_fmt l]
| (const n ls) := p ["const", to_fmt n, to_fmt ls]
| (mvar n m t)   := p ["mvar", to_fmt n, to_fmt m, t.to_fmt]
| (local_const n m bi t) := p ["local_const", to_fmt n, to_fmt m, t.to_fmt]
| (app e f) := p ["app", e.to_fmt, f.to_fmt]
| (lam n bi e t) := p ["lam", to_fmt n, repr bi, e.to_fmt, t.to_fmt]
| (pi n bi e t) := p ["pi", to_fmt n, repr bi, e.to_fmt, t.to_fmt]
| (elet n g e f) := p ["elet", to_fmt n, g.to_fmt, e.to_fmt, f.to_fmt]
| (macro d args) := p ("macro" :: d.to_fmt :: args.map expr'.to_fmt)

meta instance : has_to_format macro_def' := ⟨macro_def'.to_fmt⟩
meta instance : has_to_format expr' := ⟨expr'.to_fmt⟩

meta instance : has_to_string macro_def' := ⟨format.to_string ∘ to_fmt⟩
meta instance : has_to_string expr' := ⟨format.to_string ∘ to_fmt⟩

end
meta structure deserializer_data :=
(seek : ℕ)
(readn : ℕ → ℕ → io char_buffer)
(name_table : buffer name)
(level_table : buffer level)
(expr'_table : buffer expr')

meta def mk_data (f : ℕ → ℕ → io char_buffer) : deserializer_data :=
⟨0, f, mk_buffer, mk_buffer, mk_buffer⟩

@[reducible] meta def deserializer := state_t deserializer_data io

namespace deserializer
open deserializer_data

meta def from_file {α} (s : string) (m : deserializer α) : io α :=
do h ← mk_file_handle s mode.read tt,
   prod.fst <$> m.run (mk_data $ λ _, monad_io_file_system.read h)

meta def from_buffer {α} (buf : char_buffer) (m : deserializer α) : io α :=
prod.fst <$> m.run (mk_data $ λ s n,
  return ⟨min n (buf.size - s), ⟨λ i, buf.read' (s+i.1)⟩⟩)

meta class readable (α : Type*) := (read1 {} : deserializer α)

meta def view {α} [readable α] : deserializer α := readable.read1

meta def viewa (α) [H : readable α] : deserializer α := readable.read1

meta def read_buf (n : ℕ) : deserializer char_buffer :=
do d ← get,
  buf ← monad_lift $ d.readn d.seek n,
  put {seek := d.seek + buf.size, ..d},
  return buf

meta def corrupted {α} (s : string := "corrupted stream"): deserializer α :=
do d ← get, monad_lift $ do
  buf ← d.readn (d.seek - 10) 11,
  io.fail (s ++ " at " ++ to_string d.seek ++
    "\n" ++ to_string (char_to_hex <$> buf.to_list) ++
    "\n" ++ to_string (buf.to_list))

meta instance char.readable : readable char :=
⟨do ⟨1, a⟩ ← read_buf 1 | corrupted "EOF",
    return (a.read 0)⟩

meta def readb : deserializer ℕ := char.val <$> viewa char

meta def read_unsigned_ext : deserializer unsigned :=
do ⟨4, a⟩ ← read_buf 4 | corrupted "EOF",
  return $ unsigned.of_nat' $
    (a.read 0).1.shiftl 24 +
    (a.read 1).1.shiftl 16 +
    (a.read 2).1.shiftl 8 +
    (a.read 3).1

meta instance unsigned.readable : readable unsigned :=
⟨do c ← readb, if c < 255 then
  return (unsigned.of_nat' c) else read_unsigned_ext⟩

meta instance nat.readable : readable ℕ :=
⟨unsigned.to_nat <$> view⟩

meta def read64 : deserializer ℕ :=
do hi ← view, lo ← view,
  return (nat.shiftl hi 32 + lo)

meta def read_blob : deserializer char_buffer :=
view >>= read_buf

meta instance bool.readable : readable bool :=
⟨(λ n, n ≠ 0) <$> readb⟩

meta def iterate {α} (a : α) (f : α → deserializer (option α)) : deserializer α :=
⟨λ d, io.iterate (a, d) (λ ⟨a', d'⟩, do
  (some a', d') ← (f a').run d' | return none,
  return (a', d'))⟩

meta def read_string_aux : char_buffer → deserializer char_buffer
| buf := do
  c ← viewa char,
  if c.1 = 0 then return buf else read_string_aux (buf.push_back c)

meta instance string.readable : readable string :=
⟨buffer.to_string <$> read_string_aux mk_buffer⟩

def string.to_int (s : string) : ℤ :=
if s.front = '-' then -s.mk_iterator.next.next_to_string.to_nat else s.to_nat

meta instance int.readable : readable ℤ :=
⟨string.to_int <$> view⟩

meta instance pair.readable {α β} [readable α] [readable β] : readable (α × β) :=
⟨prod.mk <$> view <*> view⟩

meta def readn_list {α} [readable α] : ℕ → deserializer (list α)
| 0 := return []
| (n+1) := list.cons <$> view <*> readn_list n

meta def readn_list_rev {α} [readable α] : ℕ → deserializer (list α)
| 0 := return []
| (n+1) := do l ← readn_list_rev n, a ← view, return (a :: l)

meta instance list.readable {α} [readable α] : readable (list α) :=
⟨do len ← viewa unsigned, readn_list len.1⟩

meta instance option.readable {α} [readable α] : readable (option α) :=
⟨mcond view (some <$> view) (return none)⟩

-- meta def trase {α} [has_to_string α] (a : α) (s : option string := none) : deserializer unit :=
-- trace ((option.rec_on s "" (++ ": ")) ++ to_string a) (return ())

meta def obj_read_core {α} [has_to_string α] (fld : deserializer_data → buffer α)
  (put : buffer α → deserializer_data → deserializer_data)
  (f : ℕ → deserializer α) : deserializer α :=
do c ← readb,
  match c with
  | 0 := do
    i ← viewa unsigned,
    table ← fld <$> get,
    if h : i.1 < table.size then
      return $ table.read ⟨i.1, h⟩
    else corrupted ("not in table " ++ to_string i.1 ++ " ≥ " ++ to_string table.size ++ "\n" ++
      to_string table.to_list)
  | c+1 := do
    r ← f c,
    table ← fld <$> get,
    modify (put $ table.push_back r),
    return r
  end

end deserializer

open deserializer deserializer_data

-- meta def tsh {α} [has_to_string α] (m : deserializer α) (s : option string := none) : deserializer α :=
-- do a ← m, trase a s, return a

meta instance name.readable : readable name :=
⟨obj_read_core name_table (λ t d, {name_table := t, ..d}) $ λ c,
  match c with
  | 0 /- LL_ANON -/ := return name.anonymous
  | 1 /- LL_STRING -/ := mk_simple_name <$> viewa string
  | 2 /- LL_INT -/ := do n ← view, return (name.anonymous.mk_numeral n)
  | 3 /- LL_STRING_PREFIX -/ := mk_str_name <$> name.readable.read1 <*> viewa string
  | 4 /- LL_INT_PREFIX -/ := do nm ← name.readable.read1, i ← view, return (nm.mk_numeral i)
  | _ := corrupted ("bad name" ++ to_string c)
  end⟩

meta instance level.readable : readable level :=
⟨obj_read_core level_table (λ t d, {level_table := t, ..d}) $ λ _,
  do c ← readb,
  let lread := level.readable.read1 in
  match c with
  | 0 /- Zero -/ := return level.zero
  | 1 /- Succ -/ := level.succ <$> lread
  | 2 /- Max -/ := level.max <$> lread <*> lread
  | 3 /- IMax -/ := level.imax <$> lread <*> lread
  | 4 /- Param -/ := level.param <$> view
  | 5 /- Meta -/ := level.mvar <$> view
  | _ := corrupted "bad level"
  end⟩

meta instance : readable binder_info :=
⟨do c ← readb, return $
  if c.test_bit 2 then binder_info.implicit else
  if c.test_bit 1 then binder_info.strict_implicit else
  if c.test_bit 0 then binder_info.inst_implicit else
  if c.test_bit 3 then binder_info.aux_decl else
  binder_info.default⟩

meta instance : readable equations_header :=
⟨equations_header.mk <$> view <*> view <*> view <*> view <*>
  view <*> view <*> view <*> view <*> view <*> view⟩

meta def macro_def'.check : macro_def' → list expr' → bool
| (macro_def'.struct_inst _ _ fs) args := fs.length ≤ args.length
| (macro_def'.annot _) args := args.length = 1
| macro_def'.choice args := args.length > 1
| (macro_def'.nat_value _) args := args.length = 0
| (macro_def'.rec_fn _) args := args.length = 1
| (macro_def'.proj _ _ _ _ _ _ _) args := args.length = 1
| (macro_def'.equation _) args := args.length = 2
| macro_def'.no_equation args := args.length = 0
| macro_def'.as_pattern args := args.length = 2
| (macro_def'.expr_quote _ _) args := args.length = 0
| (macro_def'.sorry_ _) args := args.length = 1
| (macro_def'.string _) args := args.length = 0
| macro_def'.perm_ac args := args.length = 4
| macro_def'.typed_expr args := args.length = 2
| _ args := tt

meta def read_macro1 [readable expr'] (args : list expr') : string → deserializer macro_def'
| "Prenum" := macro_def'.prenum <$> view
| "STI" := macro_def'.struct_inst <$> view <*> view <*> view
| "fieldN" := macro_def'.field_notation <$> view <*> view
| "Annot" := macro_def'.annot <$> view
| "Choice" := return macro_def'.choice
| "CNatM" := macro_def'.nat_value <$> view
| "RecFn" := macro_def'.rec_fn <$> view
| "Proj" := macro_def'.proj <$> view <*> view <*> view <*> view <*> view <*> view <*> view
| "Eqns" := macro_def'.equations <$> view
| "Eqn" := macro_def'.equation <$> view
| "NEqn" := return macro_def'.no_equation
| "EqnR" := return macro_def'.equations_result
| "AsPat" := return macro_def'.as_pattern
| "Quote" := macro_def'.expr_quote <$> view <*> view
| "Sorry" := macro_def'.sorry_ <$> view
| "Str" := macro_def'.string <$> view
| "ACApp" := return macro_def'.ac_app
| "PermAC" := return macro_def'.perm_ac
| "TyE" := return macro_def'.typed_expr
| m := corrupted ("unknown macro " ++ m)

meta instance expr'.readable : readable expr' :=
⟨obj_read_core expr'_table (λ t d, {expr'_table := t, ..d}) $ λ c,
  let eread := expr'.readable.read1 in
  match c with
  | 0 /- Var -/ := expr'.var <$> view
  | 1 /- Sort -/ := expr'.sort <$> view
  | 2 /- Constant -/ := expr'.const <$> view <*> view
  | 3 /- Meta -/ := expr'.mvar <$> view <*> view <*> eread
  | 4 /- Local -/ := expr'.local_const <$> view <*> view <*> view <*> eread
  | 5 /- App -/ := expr'.app <$> eread <*> eread
  | 6 /- Lambda -/ := expr'.lam <$> view <*> view <*> eread <*> eread
  | 7 /- Pi -/ := expr'.pi <$> view <*> view <*> eread <*> eread
  | 8 /- Let -/ :=  expr'.elet <$> view <*> eread <*> eread <*> eread
  | 9 /- Macro -/ := do
    args ← @view _ (@list.readable _ expr'.readable),
    m ← view >>= @read_macro1 expr'.readable args,
    if m.check args
    then return (expr'.macro m args)
    else corrupted "bad macro args"
  | _ := corrupted "bad expr'"
  end⟩

structure module_name :=
(relative : option unsigned)
(name : name)

instance : has_to_string module_name :=
⟨λ m, match m with
| ⟨some r, n⟩ := to_string n ++ " - relative " ++ to_string r
| ⟨none, n⟩ := to_string n
end⟩

structure olean_data :=
(imports : list module_name)
(code : char_buffer)
(uses_sorry : bool)

meta instance module_name.readable : readable module_name :=
⟨module_name.mk <$> view <*> view⟩

meta def read_olean (s : string) : io olean_data :=
from_file s $ do
  header ← viewa string,
  guard (header = "oleanfile"),
  version ← viewa string,
  -- trase version "version",
  claimed_hash ← viewa unsigned,
  -- trase claimed_hash "claimed_hash",
  uses_sorry ← viewa bool,
  -- trase uses_sorry "uses_sorry",
  imports ← viewa (list module_name),
  -- trase imports "imports",
  code ← read_blob,
  -- guard (claimed_hash = hash code),
  return ⟨imports, code, uses_sorry⟩

structure export_decl :=
(ns : name) (as : name)
(had_explicit : bool)
(except_names : list name)
(renames : list (name × name))

meta instance : has_to_format export_decl :=
⟨λ ⟨ns, as, he, en, rn⟩, br
  [to_fmt ns, to_fmt as, to_fmt he, to_fmt en, to_fmt rn]⟩

meta structure inductive_decl :=
(d_name : name)
(level_params : list name)
(nparams : unsigned)
(type : expr')
(rules : list (name × expr'))

meta instance : has_to_format inductive_decl :=
⟨λ ⟨n, ps, np, ty, r⟩, br [to_fmt n, to_fmt ps, to_fmt np, to_fmt ty, to_fmt r]⟩

meta instance : readable inductive_decl :=
⟨inductive_decl.mk <$> view <*> view <*> view <*> view <*> view⟩

meta structure comp_rule :=
(num_bu : unsigned)
(comp_rhs : expr')

meta instance : has_to_format comp_rule :=
⟨λ ⟨n, rhs⟩, br [to_fmt n, to_fmt rhs]⟩

meta instance : readable comp_rule :=
⟨comp_rule.mk <$> view <*> view⟩

meta structure inductive_defn :=
(num_ACe : unsigned)
(elim_prop : bool)
(dep_elim : bool)
(level_param_names : list name)
(elim_type : expr')
(decl : inductive_decl)
(is_K_target : bool)
(num_indices : unsigned)
(is_trusted : bool)
(comp_rules : list comp_rule)

meta instance : has_to_format inductive_defn :=
⟨λ ⟨e1,e2,e3,e4,e5,e6,e7,e8,e9,e10⟩, br [
  to_fmt e1, to_fmt e2, to_fmt e3, to_fmt e4, to_fmt e5,
  to_fmt e6, to_fmt e7, to_fmt e8, to_fmt e9, to_fmt e10]⟩

meta instance : readable inductive_defn :=
⟨inductive_defn.mk <$> view <*> view <*> view <*> view <*>
  view <*> view <*> view <*> view <*> view <*> view⟩

meta instance : has_to_format reducibility_hints :=
⟨λ n, match n with
  | reducibility_hints.regular n b := br ["regular", to_fmt n, to_fmt b]
  | reducibility_hints.opaque := "opaque"
  | reducibility_hints.abbrev := "abbrev"
  end⟩

meta instance : readable reducibility_hints :=
⟨do k ← readb,
  match k with
  | 0 /- Regular -/ := flip reducibility_hints.regular <$> view <*> view
  | 1 /- Opaque -/ := return reducibility_hints.opaque
  | 2 /- Abbrev -/ := return reducibility_hints.abbrev
  | _ := corrupted "bad reducibility_hints"
  end⟩

meta inductive declaration'
| defn : name → list name → expr' → expr' → reducibility_hints → bool → declaration'
| thm  : name → list name → expr' → expr' → declaration'
| cnst : name → list name → expr' → bool → declaration'
| ax   : name → list name → expr' → declaration'

section
open declaration'

meta instance : has_to_format declaration' :=
⟨λ d, match d with
  | defn n ps t v h tr := ls ["defn",
    to_fmt n, to_fmt ps, to_fmt t, to_fmt v, to_fmt h, to_fmt tr]
  | thm n ps t v := ls ["thm", to_fmt n, to_fmt ps, to_fmt t, to_fmt v]
  | cnst n ps t tr := ls ["cnst", to_fmt n, to_fmt ps, to_fmt t, to_fmt tr]
  | ax n ps t := ls ["ax", to_fmt n, to_fmt ps, to_fmt t]
  end⟩

end

meta instance : readable declaration' :=
⟨do k ← readb,
  let has_value := k.test_bit 0,
  let is_th_ax := k.test_bit 1,
  let is_trusted := k.test_bit 2,
  n ← view, ps ← view, t ← view,
  if has_value then do
    v ← view,
    if is_th_ax then return $ declaration'.thm n ps t v
    else do
      hints ← view,
      return $ declaration'.defn n ps t v hints is_trusted
  else if is_th_ax then return $ declaration'.ax n ps t
  else return $ declaration'.cnst n ps t is_trusted⟩

inductive reducible_status
| reducible
| semireducible
| irreducible

meta instance : has_to_string reducible_status :=
⟨λ n, match n with
  | reducible_status.reducible := "reducible"
  | reducible_status.semireducible := "semireducible"
  | reducible_status.irreducible := "irreducible"
  end⟩

meta instance : has_to_format reducible_status := ⟨format.of_string ∘ to_string⟩

meta instance : readable reducible_status :=
⟨do c ← readb,
  match c with
  | 0 := return reducible_status.reducible
  | 1 := return reducible_status.semireducible
  | 2 := return reducible_status.irreducible
  | _ := corrupted
  end⟩

inductive elab_strategy
| simple
| with_expected_type
| as_eliminator

meta instance : has_to_string elab_strategy :=
⟨λ n, match n with
  | elab_strategy.simple := "simple"
  | elab_strategy.with_expected_type := "with_expected_type"
  | elab_strategy.as_eliminator := "as_eliminator"
  end⟩

meta instance : has_to_format elab_strategy := ⟨format.of_string ∘ to_string⟩

meta instance : readable elab_strategy :=
⟨do c ← readb,
  match c with
  | 0 := return elab_strategy.simple
  | 1 := return elab_strategy.with_expected_type
  | 2 := return elab_strategy.as_eliminator
  | _ := corrupted
  end⟩

meta inductive attr_data : Type
| basic : attr_data
| reducibility : reducible_status → attr_data
| elab_strategy : elab_strategy → attr_data
| intro (eager : bool) : attr_data
| indices (idxs : list unsigned) : attr_data
| user : expr' → attr_data

meta structure attr_record :=
(decl : name)
(data : option attr_data)

meta instance : has_to_format attr_record :=
⟨λ d, match d with
  | ⟨decl, none⟩ := br [to_fmt decl, "deleted"]
  | ⟨decl, some attr_data.basic⟩ := to_fmt decl
  | ⟨decl, some (attr_data.reducibility r)⟩ := br [to_fmt decl, to_fmt r]
  | ⟨decl, some (attr_data.elab_strategy s)⟩ := br [to_fmt decl, to_fmt s]
  | ⟨decl, some (attr_data.intro b)⟩ := br [to_fmt decl, to_fmt b]
  | ⟨decl, some (attr_data.indices ix)⟩ := br [to_fmt decl, to_fmt ix]
  | ⟨decl, some (attr_data.user e)⟩ := br [to_fmt decl, to_fmt e]
  end⟩

meta structure attr_entry :=
(attr : name)
(prio : unsigned)
(record : attr_record)

meta instance : has_to_format attr_entry :=
⟨λ ⟨a, p, r⟩, br [to_fmt a, to_fmt p, to_fmt r]⟩

meta def read_attr_ext : name → deserializer attr_data
| `_refl_lemma := return attr_data.basic
| `simp := return attr_data.basic
| `wrapper_eq := return attr_data.basic
| `congr := return attr_data.basic
| `elab_strategy := attr_data.elab_strategy <$> view
| `elab_with_expected_type := return attr_data.basic
| `elab_as_eliminator := return attr_data.basic
| `elab_simple := return attr_data.basic
| `parsing_only := return attr_data.basic
| `pp_using_anonymous_constructor := return attr_data.basic
| `user_command := return attr_data.basic
| `user_notation := return attr_data.basic
| `user_attribute := return attr_data.basic
| `algebra := return attr_data.basic
| `class := return attr_data.basic
| `instance := return attr_data.basic
| `inline := return attr_data.basic
| `inverse := return attr_data.basic
| `pattern := return attr_data.basic
| `reducibility := attr_data.reducibility <$> view
| `reducible := return attr_data.basic
| `semireducible := return attr_data.basic
| `irreducible := return attr_data.basic
| `refl := return attr_data.basic
| `symm := return attr_data.basic
| `trans := return attr_data.basic
| `subst := return attr_data.basic
| `intro := attr_data.intro <$> view
| `hole_command := return attr_data.basic
| `no_inst_pattern := return attr_data.basic
| `vm_monitor := return attr_data.basic
| `unify := return attr_data.basic
| `recursor := attr_data.indices <$> view
| `_simp.sizeof := return attr_data.basic
| n := attr_data.user <$> view
-- | n := corrupted ("unsupported attr " ++ to_string n)

meta instance : readable attr_entry :=
⟨do attr ← view,
  prio ← view,
  decl ← view,
  deleted ← viewa bool,
  if deleted then
    return ⟨attr, prio, ⟨decl, none⟩⟩
  else do
    dat ← read_attr_ext attr,
    return ⟨attr, prio, ⟨decl, some dat⟩⟩⟩

inductive ginductive_kind | basic | mutual_ | nested

meta instance : has_to_string ginductive_kind :=
⟨λ n, match n with
  | ginductive_kind.basic := "basic"
  | ginductive_kind.mutual_ := "mutual"
  | ginductive_kind.nested := "nested"
  end⟩

meta instance : has_to_format ginductive_kind := ⟨format.of_string ∘ to_string⟩

meta instance : readable ginductive_kind :=
⟨do c ← readb,
  match c with
  | 0 := return ginductive_kind.basic
  | 1 := return ginductive_kind.mutual_
  | 2 := return ginductive_kind.nested
  | _ := corrupted
  end⟩

structure ginductive_entry :=
(kind : ginductive_kind)
(inner : bool)
(num_params : unsigned)
(num_indices : list unsigned)
(inds : list name)
(intro_rules : list (list name))
(offsets : list unsigned)
(idx_to_ir_range : list (unsigned × unsigned))
(packs : list name)
(unpacks : list name)

meta instance : has_to_format ginductive_entry :=
⟨λ ⟨e1,e2,e3,e4,e5,e6,e7,e8,e9,e10⟩, br [
  to_fmt e1, to_fmt e2, to_fmt e3, to_fmt e4, to_fmt e5,
  to_fmt e6, to_fmt e7, to_fmt e8, to_fmt e9, to_fmt e10]⟩

meta instance : readable ginductive_entry :=
⟨do k ← view, inner ← view, np ← view, ni ← view,
  inds ← viewa (list name),
  intro_rules ← readn_list_rev inds.length,
  ginductive_entry.mk k inner np ni inds intro_rules <$>
    view <*> view <*> view <*> view⟩

@[reducible] def pos_info := unsigned × unsigned

meta structure vm_local_info' :=
(id : name) (type : option expr')

meta instance : readable vm_local_info' :=
⟨vm_local_info'.mk <$> view <*> view⟩

meta instance : has_to_format vm_local_info' :=
⟨λ ⟨id, t⟩, br [to_fmt id, to_fmt t]⟩

meta inductive vm_instr
| push (idx : unsigned)
| move (idx : unsigned)
| ret
| drop (num : unsigned)
| goto (tgt : unsigned)
| sconstr (idx : unsigned)
| constr (idx : unsigned) (nfields : unsigned)
| num (n : ℤ)
| destruct
| cases2 (one : unsigned) (two : unsigned)
| casesN (npcs : list unsigned)
| nat_cases (z : unsigned) (s : unsigned)
| builtin_cases (fn : name) (npcs : list unsigned)
| proj (idx : unsigned)
| apply
| invoke_global (fn : name)
| invoke_builtin (fn : name)
| invoke_cfun (fn : name)
| closure (fn : name) (nargs : unsigned)
| unreachable
| expr (e : expr')
| local_info (idx : unsigned) (info : vm_local_info')

section
open vm_instr

meta instance : has_to_format vm_instr :=
⟨λ i, match i with
| push i := ls ["push", to_fmt i]
| move i := ls ["move", to_fmt i]
| ret := "ret"
| drop i := ls ["drop", to_fmt i]
| goto tgt := ls ["goto", to_fmt tgt]
| sconstr i := ls ["sconstr", to_fmt i]
| constr i n := ls ["constr", to_fmt i, to_fmt n]
| num n := ls ["num", to_string n]
| destruct := "destruct"
| cases2 l1 l2 := ls ["cases2", to_fmt l1, to_fmt l2]
| casesN ll := ls ["casesN", to_fmt ll]
| nat_cases l1 l2 := ls ["nat_cases", to_fmt l1, to_fmt l2]
| builtin_cases f npcs := ls ["builtin_cases", to_fmt f, to_fmt npcs]
| proj i := ls ["proj", to_fmt i]
| apply := "apply"
| invoke_global fn := ls ["invoke_global", to_fmt fn]
| invoke_builtin fn := ls ["invoke_builtin", to_fmt fn]
| invoke_cfun fn := ls ["invoke_cfun", to_fmt fn]
| closure fn n := ls ["closure", to_fmt fn, to_fmt n]
| unreachable := "unreachable"
| expr e := ls ["expr", to_fmt e]
| local_info i info := ls ["local_info", to_fmt i, to_fmt info]
end⟩

end

meta instance : readable vm_instr :=
⟨do opcode ← readb,
  match opcode with
  | 0 := vm_instr.push <$> view
  | 1 := vm_instr.move <$> view
  | 2 := return vm_instr.ret
  | 3 := vm_instr.drop <$> view
  | 4 := vm_instr.goto <$> view
  | 5 := vm_instr.sconstr <$> view
  | 6 := vm_instr.constr <$> view <*> view
  | 7 := vm_instr.num <$> view
  | 8 := return vm_instr.destruct
  | 9 := vm_instr.cases2 <$> view <*> view
  | 10 := vm_instr.casesN <$> view
  | 11 := vm_instr.nat_cases <$> view <*> view
  | 12 := vm_instr.builtin_cases <$> view <*> view
  | 13 := vm_instr.proj <$> view
  | 14 := return vm_instr.apply
  | 15 := vm_instr.invoke_global <$> view
  | 16 := vm_instr.invoke_builtin <$> view
  | 17 := vm_instr.invoke_cfun <$> view
  | 18 := vm_instr.closure <$> view <*> view
  | 19 := return vm_instr.unreachable
  | 20 := vm_instr.expr <$> view
  | 21 := vm_instr.local_info <$> view <*> view
  | _ := corrupted
  end⟩

meta instance : has_to_string vm_decl_kind :=
⟨λ n, match n with
  | vm_decl_kind.bytecode := "bytecode"
  | vm_decl_kind.builtin := "builtin"
  | vm_decl_kind.cfun := "cfun"
  end⟩

meta instance : has_to_format vm_decl_kind := ⟨format.of_string ∘ to_string⟩

meta def vm_decl_data : vm_decl_kind → Type
| vm_decl_kind.bytecode := list vm_instr
| vm_decl_kind.builtin := empty
| vm_decl_kind.cfun := empty

meta instance : ∀ k, has_to_format (vm_decl_data k)
| vm_decl_kind.bytecode := ⟨λ l : list _, to_fmt l⟩
| vm_decl_kind.builtin := ⟨λ _, ↑"()"⟩
| vm_decl_kind.cfun := ⟨λ _, ↑"()"⟩

meta structure vm_decl' :=
(kind : vm_decl_kind)
(name : name)
(arity : unsigned)
(args_info : list vm_local_info')
(pos_info : option pos_info)
(olean : option string)
(dat : vm_decl_data kind)

meta instance : has_to_format vm_decl' :=
⟨λ ⟨e1,e2,e3,e4,e5,e6,e7⟩, br [
  to_fmt e1, to_fmt e2, to_fmt e3, to_fmt e4, to_fmt e5, to_fmt e6, to_fmt e7]⟩

meta instance : readable vm_decl' :=
⟨do fn ← view,
  arity ← view,
  code_sz ← view,
  pos ← view,
  args_info ← view,
  code ← readn_list code_sz,
  return ⟨vm_decl_kind.bytecode, fn, arity, args_info, pos, none, code⟩⟩

inductive class_entry
| class_ (n : name)
| inst (n : name) (inst : name) (prio : unsigned)
| tracker (n : name) (track : name)

meta instance : has_to_format class_entry :=
⟨λ n, match n with
  | class_entry.class_ n := p ["class", to_fmt n]
  | class_entry.inst n i pr := p ["inst", to_fmt n, to_fmt i, to_fmt pr]
  | class_entry.tracker n t := p ["tracker", to_fmt n, to_fmt t]
  end⟩

meta instance : readable class_entry :=
⟨do k ← readb,
  match k with
  | 0 := class_entry.class_ <$> view
  | 1 := class_entry.inst <$> view <*> view <*> view
  | 2 := class_entry.tracker <$> view <*> view
  | _ := corrupted
  end⟩

structure proj_info :=
(constr : name)
(nparams : unsigned)
(i : unsigned)
(inst_implicit : bool)

meta instance : has_to_format proj_info :=
⟨λ ⟨c,n,i,ii⟩, br [to_fmt c, to_fmt n, to_fmt i, to_fmt ii]⟩

meta instance : readable proj_info :=
⟨proj_info.mk <$> view <*> view <*> view <*> view⟩

meta inductive action
| skip
| expr (rbp : unsigned)
| exprs (sep : name) (rec : expr') (ini : option expr')
  (is_foldr : bool) (rbp : unsigned) (terminator : option name)
| binder (rbp : unsigned)
| binders (rbp : unsigned)
| scoped_expr (rec : expr') (rbp : unsigned) (use_lambda : bool)
| ext (impossible : empty)

meta instance : has_to_format action :=
⟨λ n, match n with
  | action.skip := "skip"
  | action.expr rbp := p ["expr", to_fmt rbp]
  | action.exprs sep rec ini fold rbp tm := p ["exprs",
    to_fmt sep, to_fmt rec, to_fmt ini, to_fmt rbp, to_fmt tm]
  | action.binder rbp := p ["binder", to_fmt rbp]
  | action.binders rbp := p ["binders", to_fmt rbp]
  | action.scoped_expr rec rbp lam :=
    p ["scoped_expr", to_fmt rec, to_fmt rbp, to_fmt lam]
  end⟩

meta instance : readable action :=
⟨do k ← readb,
  match k with
  | 0 := return action.skip
  | 1 := action.expr <$> view
  | 2 := action.exprs <$> view <*> view <*> view <*> view <*> view <*> view
  | 3 := action.binder <$> view
  | 4 := action.binders <$> view
  | 5 := action.scoped_expr <$> view <*> view <*> view
  | 6 := corrupted "Ext actions never appear in olean files"
  | _ := corrupted
  end⟩

meta structure transition :=
(tk : name) (pp : name) (act : action)

meta instance : readable transition :=
⟨transition.mk <$> view <*> view <*> view⟩

meta instance : has_to_format transition :=
⟨λ ⟨tk, pp, act⟩, br [to_fmt tk, to_fmt pp, to_fmt act]⟩

meta inductive notation_entry_kind
| reg (is_nud : bool) (transitions : list transition) (prio : unsigned)
| numeral (n : ℤ)

meta instance : has_to_format notation_entry_kind :=
⟨λ n, match n with
  | notation_entry_kind.reg tt tr prio := p ["nud", to_fmt tr, to_fmt prio]
  | notation_entry_kind.reg ff tr prio := p ["led", to_fmt tr, to_fmt prio]
  | notation_entry_kind.numeral n := p ["numeral", to_string n]
  end⟩

inductive notation_entry_group | main | reserve_

meta instance : has_to_string notation_entry_group :=
⟨λ n, match n with
  | notation_entry_group.main := "main"
  | notation_entry_group.reserve_ := "reserve"
  end⟩

meta instance : has_to_format notation_entry_group := ⟨format.of_string ∘ to_string⟩

meta instance : readable notation_entry_group :=
⟨do c ← readb,
  match c with
  | 0 := return notation_entry_group.main
  | 1 := return notation_entry_group.reserve_
  | _ := corrupted
  end⟩

meta structure notation_entry :=
(kind : notation_entry_kind)
(expr : expr')
(overload : bool)
(group : notation_entry_group)
(parse_only : bool)

meta instance : has_to_format notation_entry :=
⟨λ ⟨k, pe, ol, g, po⟩, br [to_fmt k, to_fmt pe, to_fmt ol, to_fmt g, to_fmt po]⟩

meta instance : readable notation_entry :=
⟨do k ← readb,
  ol ← view,
  po ← view,
  e ← view,
  if k = 2 then do
    n ← view,
    return ⟨notation_entry_kind.numeral n, e, ol, notation_entry_group.main, po⟩
  else do
    g ← view,
    nud ← match k with
    | 0 := return tt
    | 1 := return ff
    | _ := corrupted
    end,
    tr ← view,
    prio ← view,
    return ⟨notation_entry_kind.reg nud tr prio, e, ol, g, po⟩⟩

meta structure inverse_entry :=
(decl : name) (arity : unsigned) (inv : name) (inv_arity : unsigned) (lemma_ : name)

meta instance : readable inverse_entry :=
⟨inverse_entry.mk <$> view <*> view <*> view <*> view <*> view⟩

meta instance : has_to_format inverse_entry :=
⟨λ ⟨d, a, i, ia, l⟩, br [to_fmt d, to_fmt a, to_fmt i, to_fmt ia, to_fmt l]⟩

inductive op_kind | relation | subst | trans | refl | symm

meta instance : has_to_string op_kind :=
⟨λ n, match n with
  | op_kind.relation := "relation"
  | op_kind.subst := "subst"
  | op_kind.trans := "trans"
  | op_kind.refl := "refl"
  | op_kind.symm := "symm"
  end⟩

meta instance : has_to_format op_kind := ⟨format.of_string ∘ to_string⟩

meta instance : readable op_kind :=
⟨do c ← readb,
  match c with
  | 0 := return op_kind.relation
  | 1 := return op_kind.subst
  | 2 := return op_kind.trans
  | 3 := return op_kind.refl
  | 4 := return op_kind.symm
  | _ := corrupted
  end⟩

meta structure recursor_info :=
(rec_ : name)
(ty : name)
(dep_elim : bool)
(recursive : bool)
(num_args : unsigned)
(major_pos : unsigned)
(univ_pos : list unsigned)
(params_pos : list (option unsigned))
(indices_pos : list unsigned)
(produce_motive : list bool)

meta instance : has_to_format recursor_info :=
⟨λ ⟨r, t, de, rc, na, mp, up, pp, ip, pm⟩, br [to_fmt r, to_fmt t, to_fmt de,
  to_fmt rc, to_fmt na, to_fmt mp, to_fmt up, to_fmt pp, to_fmt ip, to_fmt pm]⟩

meta instance : readable recursor_info :=
⟨recursor_info.mk <$> view <*> view <*> view <*> view <*> view <*>
  view <*> view <*> view <*> view <*> view⟩

meta inductive modification
| export_decl (in_ns : name) (decl : export_decl)
| pos_info (decl_name : name) (pos_info : pos_info)
| inductive_ (defn : inductive_defn) (trust_lvl : unsigned)
| decl (decl : declaration') (trust_lvl : unsigned)
| aux_rec (decl : name)
| protected_ (name : name)
| private_ (name : name) (real : _root_.name)
| gind (entry : ginductive_entry)
| new_ns (ns : name)
| vm_reserve (fn : name) (arity : unsigned)
| vm_code (decl : vm_decl')
| vm_monitor (decl : name)
| eqn_lemmas (lem : name)
| has_simple_eqn_lemma (decl : name)
| no_conf (decl : name)
| doc (decl : name) (doc : string)
| ncomp (decl : name)
| proj (decl : name) (info : proj_info)
| decl_trace (decl : name)
| user_command (decl : name)
| user_notation (decl : name)
| user_attr (decl : name)
| hole_command (decl : name)
| quot
| native_module_path (decl : name)
| key_eqv (n1 : name) (n2 : name)

-- scoped extensions, not sure if these need to be separated out
| token (tk : string) (prec : option unsigned)
| notation_ (entry : notation_entry)
| attr (entry : attr_entry)
| class_ (entry : class_entry)
| inverse (entry : inverse_entry)
| relation (kind : op_kind) (decl : name)
| unification_hint (decl : name) (prio : unsigned)
| user_recursor (info : recursor_info)

section
open modification

meta def modification.to_fmt : modification → format
| (export_decl ns d) := ls ["export_decl", to_fmt ns, to_fmt d]
| (pos_info d info) := ls ["pos_info", to_fmt d, to_fmt info]
| (inductive_ d l) := ls ["inductive", to_fmt d, to_fmt l]
| (decl d l) := ls ["decl", to_fmt d, to_fmt l]
| (aux_rec d) := ls ["aux_rec", to_fmt d]
| (protected_ d) := ls ["protected", to_fmt d]
| (private_ d r) := ls ["private", to_fmt d, to_fmt r]
| (gind e) := ls ["gind", to_fmt e]
| (new_ns ns) := ls ["new_ns", to_fmt ns]
| (vm_reserve fn ar) := ls ["vm_reserve", to_fmt fn, to_fmt ar]
| (vm_code d) := ls ["vm_code", to_fmt d]
| (vm_monitor d) := ls ["vm_monitor", to_fmt d]
| (eqn_lemmas lem) := ls ["eqn_lemmas", to_fmt lem]
| (has_simple_eqn_lemma d) := ls ["has_simple_eqn_lemma", to_fmt d]
| (no_conf d) := ls ["no_conf", to_fmt d]
| (doc d s) := ls ["doc", to_fmt d, to_fmt s]
| (ncomp d) := ls ["ncomp", to_fmt d]
| (proj d i) := ls ["proj", to_fmt d, to_fmt i]
| (decl_trace d) := ls ["decl_trace", to_fmt d]
| (user_command d) := ls ["user_command", to_fmt d]
| (user_notation d) := ls ["user_notation", to_fmt d]
| (user_attr d) := ls ["user_attr", to_fmt d]
| (hole_command d) := ls ["hole_command", to_fmt d]
| quot := "quot"
| (native_module_path d) := ls ["native_module_path", to_fmt d]
| (key_eqv n1 n2) := ls ["key_eqv", to_fmt n1, to_fmt n2]

| (token tk prec) := ls ["token", to_fmt tk, to_fmt prec]
| (notation_ e) := ls ["notation", to_fmt e]
| (attr e) := ls ["attr", to_fmt e]
| (class_ e) := ls ["class", to_fmt e]
| (inverse e) := ls ["inverse", to_fmt e]
| (relation k d) := ls ["relation", to_fmt k, to_fmt d]
| (unification_hint d pr) := ls ["unification_hint", to_fmt d, to_fmt pr]
| (user_recursor e) := ls ["user_recursor", to_fmt e]

meta instance : has_to_format modification := ⟨modification.to_fmt⟩

end

meta def modification_readers : rbmap string (deserializer modification) :=
rbmap.from_list [
  ("export_decl", modification.export_decl <$> view <*>
    (export_decl.mk <$> view <*> view <*> view <*> view <*> view)),
  ("PInfo", modification.pos_info <$> view <*> view),
  ("ind", modification.inductive_ <$> view <*> view),
  ("decl", modification.decl <$> view <*> view),
  ("auxrec", modification.aux_rec <$> view),
  ("prt", modification.protected_ <$> view),
  ("prv", modification.private_ <$> view <*> view),
  ("gind", modification.gind <$> view),
  ("nspace", modification.new_ns <$> view),
  ("VMR", modification.vm_reserve <$> view <*> view),
  ("VMC", modification.vm_code <$> view),
  ("VMMonitor", modification.vm_monitor <$> view),
  ("EqnL", modification.eqn_lemmas <$> view),
  ("SEqnL", modification.has_simple_eqn_lemma <$> view),
  ("no_conf", modification.no_conf <$> view),
  ("doc", modification.doc <$> view <*> view),
  ("ncomp", modification.ncomp <$> view),
  ("proj", modification.proj <$> view <*> view),
  ("decl_trace", modification.decl_trace <$> view),
  ("USR_CMD", modification.user_command <$> view),
  ("USR_NOTATION", modification.user_notation <$> view),
  ("USR_ATTR", modification.user_attr <$> view),
  ("HOLE_CMD", modification.hole_command <$> view),
  ("quot", return modification.quot),
  ("native_module_path", modification.native_module_path <$> view),
  ("key_eqv", modification.key_eqv <$> view <*> view),

  ("TK", modification.token <$> view <*> view),
  ("NOTA", modification.notation_ <$> view),
  ("ATTR", modification.attr <$> view),
  ("class", modification.class_ <$> view),
  ("inverse", modification.inverse <$> view),
  ("REL", modification.relation <$> view <*> view),
  ("UNIFICATION_HINT", modification.unification_hint <$> view <*> view),
  ("UREC", modification.user_recursor <$> view),
  ("active_export_decls", corrupted "active_export_decls should not appear in olean files") ]

meta def read_modifications : buffer modification → deserializer (buffer modification)
| buf := do k ← viewa string,
  if k = "EndFile" then return mk_buffer
  else match modification_readers.find k with
  | some m := do mod ← m, read_modifications (buf.push_back mod)
  | none := corrupted $ "unknown modification " ++ k
  end

#eval do
  -- ol ← read_olean "src/olean.dat",
  -- ol ← read_olean "../lean/library/init/core.olean",
  ol ← read_olean "../mathlib/logic/basic.olean",
  -- ol ← read_olean "../mathlib/test.olean",
  from_buffer ol.code $ do
    mods ← read_modifications mk_buffer,
    return $ mods.iterate () (λ _ mod r,
      let x := r in trace (to_fmt mod).to_string x)
