import Lean
/-! Print the elaborated type of declarations compiled below a module prefix, one JSON object per
line.  Two formats:

* **legacy** (default): every theorem, as `{"name", "type"}` with `type` the string
  `"{universe parameters} ⊢ {type}"`.  `docs/statements.json` records the SHA-256 of this string,
  so `scripts/fidelity.py` compares against it.  Do not change this format.
* **canonical** (`--canonical`, used by `scripts/hashdiff.py`): every theorem, definition,
  opaque constant, axiom, inductive type and constructor, as `{"name", "module", "kind", "type"}`
  plus `"value"` (the body) for definitions.  Universe parameters are renamed `u0, u1, …` by
  position and private names lose the module they were declared in (`_priv.<name>`), so moving a
  declaration to another file does not change its text.

In both formats binder names are erased, because hygienic names mention the module they were
elaborated in, and types are printed by `Expr.dbgToString`, which shows every argument and every
constant by its full name.

**Helper constants (canonical format).**  Lean stores parts of a declaration in constants of their
own with generated names: the functional of a structural recursion (`f._f`), the packed function
of a well-founded recursion (`f._unary`), matchers (`f.match_1`), sparse case splits
(`f._sparseCasesOn_1`), parts of instances (`inst._aux_1`) and nested proofs (`f._proof_1`).
These are no records of the dump.  A record that mentions one of them prints its *content* in
place of its name:

* a helper that is a theorem is printed as `_proof`, and so is its application to arguments (a
  proof again).  Nothing more is needed: the proposition it proves is fixed, up to definitional
  equality, by the place where the proof stands (the function it is an argument of and the
  arguments before it, the type of a `let`, the type of the record), all of which are printed,
  and two proofs of one proposition are equal.  Its own type and its arguments are deliberately
  not printed: Lean infers the type from the proof term and passes the variables that the proof
  term uses, so both can change when only the proof is rewritten;
* a helper that is a definition is printed as `_<class> T v`, with its type, its body and the
  last component of its name without the number as class (`_f`, `_unary`, `_match`, `_aux`, …),
  with the universe levels of the place of use and with the helpers it mentions printed the same
  way.

So the numbers and the owner in a generated name play no role (a renumbering changes no text), a
change inside a helper definition changes the text of every record that uses it, and the names
inside stay visible to the rename map of `scripts/hashdiff.py`.  Constants that Lean derives from
a recorded inductive type alone (`rec`, `casesOn`, `brecOn`, `_sizeOf_inst`, …) keep their names.
A helper declared in another module of the library is read from that module's `.olean`.

Not a record either:

* the lemmas that Lean realizes for a definition `f` in whichever module first needs them:
  `f.eq_<n>`, `f.eq_def`, `f.eq_unfold`, `f.congr_simp`.  Such a name alone decides nothing: the
  declaration must be a theorem that concludes `f … = …` for the constant `f` it is named after,
  and `f` must be a definition if it is a constant of the library (for a constant of Mathlib the
  form of the statement decides).  A theorem that somebody wrote under the name `eq_17` in a
  namespace is a record;
* `X.casesOn`, `X.recOn`, `X.noConfusion`, … if `X` is an inductive type of the library or one
  of its constructors;
* the lemmas Lean derives from a matcher on demand (`f.match_1.splitter`, …).

It reads the `.olean` files directly, so it does not load the imports of those modules: printing a
type needs no environment, and walking all of Mathlib would page gigabytes into memory.

Usage, from the repository root:

* `lean --run scripts/DumpTypes.lean [--canonical] Prefix …`: every module below each prefix
  (`LeanDLRA.OpenProblems`), skipping stale `.olean` files whose source file no longer exists;
* `lean --run scripts/DumpTypes.lean [--canonical] --modules M₁ M₂ …`: exactly these modules;
* `--root=DIR`: the directory of the `.olean` files (default `.lake/build/lib/lean`);
* `--stats`: with `--canonical`, a line on standard error that counts the helpers printed by
  content and the generated constants left by name.
-/
open Lean

/-- The expression with every binder name replaced by the same name. -/
partial def eraseBinderNames (e : Expr) : Expr :=
  e.replace fun
    | .forallE _ d b i => some (.forallE `x (eraseBinderNames d) (eraseBinderNames b) i)
    | .lam _ d b i => some (.lam `x (eraseBinderNames d) (eraseBinderNames b) i)
    | .letE _ t v b nd =>
      some (.letE `x (eraseBinderNames t) (eraseBinderNames v) (eraseBinderNames b) nd)
    | _ => none

/-- `_priv.<user name>` for a private name (which contains its module), the name itself otherwise. -/
def normalizeName (n : Name) : Name :=
  match privateToUserName? n with
  | some u => `_priv ++ u
  | none => n

/-- The canonical form of an expression: universe parameters `lps` renamed `u0, u1, …` by
position, private constant names normalized, binder names erased. -/
def canonical (lps : List Name) (e : Expr) : Expr :=
  let us := lps.mapIdx fun i _ => Level.param (.mkSimple s!"u{i}")
  let e := (e.instantiateLevelParams lps us).replace fun
    | .const n ls => if isPrivateName n then some (.const (normalizeName n) ls) else none
    | _ => none
  eraseBinderNames e

/-- Last components of constants that Lean derives from an inductive type alone. -/
def derivedSuffixes : List String :=
  ["casesOn", "recOn", "noConfusion", "noConfusionType", "below", "brecOn", "binductionOn",
    "ibelow", "ctorIdx", "toCtorIdx", "ctorElim", "ctorElimType"]

/-- `cs` consists of non-empty groups of digits separated by `_` (exactly one group if
`single`). -/
def digitGroups (single : Bool) (cs : List Char) : Bool :=
  let rec go (inGroup : Bool) : List Char → Bool
    | [] => inGroup
    | c :: cs =>
      if c.isDigit then go true cs else c == '_' && inGroup && !single && go false cs
  go false cs

/-- `s` is `pre` followed by groups of digits separated by `_`: `match_1`, `match_1_2`,
`_sizeOf_3`; with `single` by exactly one group: `eq_17`. -/
def isNumbered (pre s : String) (single : Bool := false) : Bool :=
  s.startsWith pre && digitGroups single (s.toList.drop pre.length)

/-- The last component of a matcher name (`match_1`, and `match_1_1` inside a theorem). -/
def isMatcherComponent (s : String) : Bool := isNumbered "match_" s

/-- Whether a proper prefix of the name is the name of a matcher. -/
def belowMatcher : Name → Bool
  | .str p _ => (match p with | .str _ s => isMatcherComponent s | _ => false) || belowMatcher p
  | .num p _ => belowMatcher p
  | .anonymous => false

/-- The conclusion of a type: the body below its leading binders. -/
def conclusion : Expr → Expr
  | .forallE _ _ b _ => conclusion b
  | .mdata _ e => conclusion e
  | e => e

/-- The constant `f` if `type` concludes `f … = …`. -/
def equationHead? (type : Expr) : Option Name :=
  let c := conclusion type
  if c.isAppOfArity ``Eq 3 then
    match (c.getArg! 1).consumeMData.getAppFn.consumeMData with
    | .const f _ => some f
    | _ => none
  else none

/-- Last components of the lemmas that Lean realizes on demand for a definition. -/
def isOnDemandLemmaName (s : String) : Bool :=
  isNumbered "eq_" s true || ["eq_def", "eq_unfold", "congr_simp"].contains s

/-- The constant `f` if the declaration is, by name and form, a lemma that Lean realizes on demand
for `f`: a theorem `f.eq_<n>`, `f.eq_def`, `f.eq_unfold` or `f.congr_simp` that concludes
`f … = …`. -/
def onDemandLemmaOf? (info : ConstantInfo) : Option Name :=
  match privateToUserName info.name with
  | .str p s =>
    if info.isTheorem && isOnDemandLemmaName s then
      match equationHead? info.type with
      | some f => if privateToUserName f == p then some f else none
      | none => none
    else none
  | _ => none

/-- Whether a type has a binder named `motive`, as the type of every matcher has. -/
def hasMotive : Expr → Bool
  | .forallE n _ b _ => n == `motive || hasMotive b
  | .mdata _ e => hasMotive e
  | _ => false

/-- Whether the name shows that a declaration is no record of the canonical dump: an internal
name (`_proof_1`, `_f`, …), a matcher (a definition named `match_<n>` with a motive), or a lemma
derived from a matcher. -/
def hasGeneratedName (info : ConstantInfo) : Bool :=
  let n := privateToUserName info.name
  n.isInternal || belowMatcher n ||
    match n with
    | .str _ s => isMatcherComponent s && !info.isTheorem && hasMotive info.type
    | _ => false

/-- Whether the last component `s` names a constant that Lean derives from an inductive type
alone (`X.casesOn`, `X._sizeOf_inst`, …).  The record of the type determines such a constant, so
it is printed by name. -/
def isDerivedFromType (s : String) : Bool :=
  derivedSuffixes.contains s || s == "_sizeOf_inst" || isNumbered "_sizeOf_" s

/-- The last component of a name, if it is a string. -/
def lastComponent (n : Name) : String :=
  match privateToUserName n with
  | .str _ s => s
  | _ => ""

/-- Whether a name can be the name of a helper whose content is printed: only such names are
looked up in other modules. -/
def looksAuxiliary (n : Name) : Bool :=
  let n := privateToUserName n
  !isDerivedFromType (lastComponent n) &&
    (n.isInternal || belowMatcher n || isMatcherComponent (lastComponent n))

/-- The kind of a declaration, or `none` for kinds that are not dumped (recursors, quotients). -/
def kindOf : ConstantInfo → Option String
  | .thmInfo _ => some "theorem"
  | .defnInfo _ => some "def"
  | .opaqueInfo _ => some "opaque"
  | .axiomInfo _ => some "axiom"
  | .inductInfo _ => some "inductive"
  | .ctorInfo _ => some "constructor"
  | _ => none

/-- The class of a helper definition: the last component of its name without the numbers, with a
leading underscore (`match_1_2` gives `_match`, `_sparseCasesOn_2` gives `_sparseCasesOn`). -/
def helperClass (n : Name) : Name :=
  match privateToUserName n with
  | .str _ s =>
    let parts := (s.splitOn "_").filter fun g => !(g.length > 0 && g.all Char.isDigit)
    let core := "_".intercalate (parts.filter (· ≠ ""))
    .mkSimple ("_" ++ (if core.isEmpty then "aux" else core))
  | _ => `_aux

/-- Path of a module below `root`, with the given extension. -/
def modulePath (root : System.FilePath) (mod : String) (ext : String) : System.FilePath :=
  (mod.splitOn "." |>.foldl (· / ·) root).addExtension ext

/-- A copy of a string that shares no memory with it: what is read from an `.olean` file dies
with the region of that file. -/
def copyString (s : String) : String := s.foldl (fun acc c => acc.push c) ""

/-- A name as text, as key of the tables that outlive the module the name was read from (a copy:
the text of a name with one component can be the string stored in the file). -/
def nameKey (n : Name) : String := copyString n.toString

/-- A module name as text, as it appears in file paths and on the command line (a copy, see
`copyString`). -/
def moduleKey (n : Name) : String := copyString (n.toString (escape := false))

/-- What the dump needs to know of a constant of another module: a definition, a type or
constructor, a theorem, or something else. -/
def isDefinitionCode : UInt8 := 1
def isTypeCode : UInt8 := 2
def isTheoremCode : UInt8 := 3
def kindCode : ConstantInfo → UInt8
  | .defnInfo _ => isDefinitionCode
  | .inductInfo _ => isTypeCode
  | .ctorInfo _ => isTypeCode
  | .thmInfo _ => isTheoremCode
  | _ => 0

/-- The constants of a module by name. -/
abbrev Table := Std.HashMap Name ConstantInfo

/-- State of a canonical dump. -/
structure DumpState where
  /-- Every constant name of the library, as text → its `kindCode`. -/
  kinds : Std.HashMap String UInt8 := {}
  /-- Every name of the library that can be the name of a helper, as text → the modules that
  declare it. -/
  index : Std.HashMap String (Array String) := {}
  /-- Whether `kinds` and `index` have been filled. -/
  indexed : Bool := false
  /-- Modules read for a helper they declare; their memory is kept until the end. -/
  foreign : Std.HashMap String Table := {}
  /-- The constants of the module that is being dumped. -/
  here : Table := {}
  /-- Per module: what a constant is replaced by (level parameters and content), if anything. -/
  memo : Std.HashMap Name (Option (List Name × Expr)) := {}
  /-- Helpers whose content is being computed (a cycle is left by name). -/
  visiting : NameSet := {}
  /-- Counts for `--stats`: helper classes printed by content, constants left by name. -/
  counts : Std.HashMap String Nat := {}

abbrev DumpM := StateT DumpState IO

def count (key : String) : DumpM Unit :=
  modify fun s => { s with counts := s.counts.insert key (s.counts.getD key 0 + 1) }

/-- Fill the tables of the constant names: over the targets and the modules of the library (those
with an `.olean` below `root`) that they import, directly or not. -/
unsafe def buildIndex (root : System.FilePath) (targets : List String) : DumpM Unit := do
  let mut kinds : Std.HashMap String UInt8 := {}
  let mut index : Std.HashMap String (Array String) := {}
  let mut seen : Std.HashSet String := {}
  let mut todo := targets
  while !todo.isEmpty do
    let mod := todo.head!
    todo := todo.tail!
    if seen.contains mod then continue
    seen := seen.insert mod
    let file := modulePath root mod "olean"
    unless ← file.pathExists do continue
    let (data, region) ← readModuleData file
    for c in data.constants do
      let key := nameKey c.name
      kinds := kinds.insert key (kindCode c)
      if looksAuxiliary c.name then index := index.insert key ((index.getD key #[]).push mod)
    count "module indexed"
    let imports := data.imports.toList.map fun i => moduleKey i.module
    region.free
    todo := imports ++ todo
  modify fun s => { s with kinds := kinds, index := index, indexed := true }

/-- A constant by name: in the module that is being dumped, or, if the name can be that of a
helper, in the module of the library that declares it. -/
unsafe def findHelper (root : System.FilePath) (targets : List String) (n : Name) :
    DumpM (Option ConstantInfo) := do
  if let some info := (← get).here[n]? then return some info
  unless looksAuxiliary n do return none
  unless (← get).indexed do buildIndex root targets
  for mod in (← get).index.getD (nameKey n) #[] do
    let table ← match (← get).foreign[mod]? with
      | some t => pure t
      | none => do
        -- The region is not freed: the constants found here are used until the end of the run.
        let (data, _) ← readModuleData (modulePath root mod "olean")
        let t : Table := data.constants.foldl (fun t c => t.insert c.name c) {}
        modify fun s => { s with foreign := s.foreign.insert mod t }
        count "module read for a helper"
        pure t
    if let some info := table[n]? then return some info
  return none

/-- The `kindCode` of a constant of the library: from the module that is being dumped, else from
the table of the library; `none` if the library has no constant of this name. -/
unsafe def kindCodeOf (root : System.FilePath) (targets : List String) (n : Name) :
    DumpM (Option UInt8) := do
  if let some info := (← get).here[n]? then return some (kindCode info)
  unless (← get).indexed do buildIndex root targets
  return (← get).kinds[nameKey n]?

/-- Whether a declaration is no record of the canonical dump: a generated name, a constant
derived from an inductive type of the library, or a lemma realized on demand for a definition. -/
unsafe def isAuxiliary (root : System.FilePath) (targets : List String) (info : ConstantInfo) :
    DumpM Bool := do
  if hasGeneratedName info then return true
  if let .str p s := info.name then
    if derivedSuffixes.contains s then
      -- A namespace or a constant that is no type: somebody wrote the declaration, a record.
      if (← kindCodeOf root targets p) == some isTypeCode then return true
  let some f := onDemandLemmaOf? info | return false
  match ← kindCodeOf root targets f with
  | some code =>
    if code == isDefinitionCode then return true
    count "record: named like an on-demand lemma, of a constant that is no definition"
    return false
  | none =>
    -- `f` is a constant (the statement applies it) and the library does not declare it.
    count "no record: on-demand lemma of a constant outside the library"
    return true

/-- Whether a constant is a record of the canonical dump. -/
unsafe def isRecord (root : System.FilePath) (targets : List String) (info : ConstantInfo) :
    DumpM Bool := do
  if (kindOf info).isNone then return false
  return !(← isAuxiliary root targets info)

mutual

/-- `helperContent` without the memo. -/
unsafe def helperContentCore (root : System.FilePath) (targets : List String) (n : Name) :
    DumpM (Option (List Name × Expr)) := do
  -- A theorem with a generated name is a proof and nothing else; its module is not read.
  let user := privateToUserName n
  if user.isInternal || belowMatcher user then
    if (← kindCodeOf root targets n) == some isTheoremCode then
      count "by content: _proof"
      return some ([], mkConst `_proof)
  let found ← findHelper root targets n
  if found.isNone then count s!"by name: {helperClass n} (not in the library)"
  let some info := found | return none
  if ← isRecord root targets info then return none
  match info with
  | .thmInfo _ => return none
  | .defnInfo d =>
    -- No checked definition mentions itself; an unsafe one may, and then stays a name there.
    if (← get).visiting.contains n then
      IO.eprintln s!"DumpTypes: {n} refers to itself; it is printed by name there"
      count "by name: cycle"
      return none
    modify fun s => { s with visiting := s.visiting.insert n }
    let type ← inlineHelpers root targets d.type
    let value ← inlineHelpers root targets d.value
    modify fun s => { s with visiting := s.visiting.erase n }
    count s!"by content: {helperClass n}"
    return some (d.levelParams, mkApp2 (mkConst (helperClass n)) type value)
  | .recInfo _ | .quotInfo _ => return none
  | _ =>
    count s!"by name: {helperClass n} (no definition, no theorem)"
    return none

/-- What a constant mentioned in a record is printed as: `none` for its name, or the level
parameters and the content of a helper.  Only a name that can be the name of a helper is looked
up: records, constants derived from a type and lemmas realized on demand keep their names,
whichever module declares them. -/
unsafe def helperContent (root : System.FilePath) (targets : List String) (n : Name) :
    DumpM (Option (List Name × Expr)) := do
  unless looksAuxiliary n do return none
  if let some r := (← get).memo[n]? then return r
  let result ← helperContentCore root targets n
  modify fun s => { s with memo := s.memo.insert n result }
  return result

/-- The expression with every helper constant replaced by its content. -/
unsafe def inlineHelpers (root : System.FilePath) (targets : List String) (e : Expr) :
    DumpM Expr := do
  let mut found : Std.HashMap Name (List Name × Expr) := {}
  for c in e.getUsedConstants do
    if let some r ← helperContent root targets c then found := found.insert c r
  if found.isEmpty then return e
  return e.replace fun x =>
    match x.getAppFn with
    | .const n ls =>
      match found[n]? with
      | some (lps, body) =>
        -- A proof applied to arguments is a proof: the arguments go with it.
        if body.isConstOf `_proof then some body
        -- A helper definition applied to arguments: the head is replaced when it is visited.
        else if x.isApp then none
        else some (body.instantiateLevelParams lps ls)
      | none => none
    | _ => none

end

/-- One JSON line per dumped declaration of the module `mod` stored in `file`. -/
unsafe def dumpModule (root : System.FilePath) (targets : List String) (canonicalMode : Bool)
    (mod : String) (file : System.FilePath) : DumpM Unit := do
  let (data, region) ← readModuleData file
  let out ← IO.getStdout
  if canonicalMode then
    let here : Table := data.constants.foldl (fun t c => t.insert c.name c) {}
    modify fun s => { s with here := here, memo := {}, visiting := {} }
  for info in data.constants do
    if canonicalMode then
      let some kind := kindOf info | continue
      if ← isAuxiliary root targets info then continue
      let lps := info.levelParams
      let type ← inlineHelpers root targets info.type
      let mut fields := [("name", toJson (normalizeName info.name).toString),
        ("module", toJson mod), ("kind", toJson kind),
        ("type", toJson s!"{lps.length} ⊢ {canonical lps type}")]
      if let .defnInfo d := info then
        let value ← inlineHelpers root targets d.value
        fields := fields ++ [("value", toJson s!"{canonical lps value}")]
      out.putStrLn (Json.compress (Json.mkObj fields))
    else
      unless info.isTheorem do continue
      if info.name.isInternal then continue
      let typ := s!"{info.levelParams} ⊢ {eraseBinderNames info.type}"
      out.putStrLn (Json.compress (Json.mkObj [("name", info.name.toString), ("type", typ)]))
  -- Nothing of this module is used after this point: the memo is reset with the next module.
  modify fun s => { s with here := {}, memo := {} }
  region.free

unsafe def main (args : List String) : IO Unit := do
  let rootArg := args.find? (·.startsWith "--root=")
  let root : System.FilePath :=
    match rootArg with
    | some a => System.FilePath.mk ("=".intercalate ((a.splitOn "=").drop 1))
    | none => System.FilePath.mk ".lake/build/lib/lean"
  let canonicalMode := args.contains "--canonical"
  let modulesMode := args.contains "--modules"
  let targets := args.filter fun a => !a.startsWith "--"
  let run : DumpM Unit := do
    if modulesMode then
      for mod in targets do
        let file := modulePath root mod "olean"
        unless ← file.pathExists do
          throw <| IO.userError s!"no .olean for module {mod} (build it first): {file}"
        dumpModule root targets canonicalMode mod file
    else
      let mut found : Array (String × System.FilePath) := #[]
      for pre in targets do
        let dir := pre.splitOn "." |>.foldl (· / ·) root
        for file in ← dir.walkDir do
          unless file.extension == some "olean" do continue
          -- The module name and the source file, from the path below `root`.
          let rel := (file.withExtension "").components.drop (root.components.length)
          let source := (rel.foldl (· / ·) ("." : System.FilePath)).addExtension "lean"
          unless ← source.pathExists do continue
          found := found.push (".".intercalate rel, file)
      let mods := found.toList.map (·.1)
      for (mod, file) in found do
        dumpModule root mods canonicalMode mod file
  let (_, state) ← run.run {}
  if args.contains "--stats" then
    let items := state.counts.toList.toArray.qsort (fun a b => a.1 < b.1)
    let text := ", ".intercalate (items.toList.map fun (k, v) => s!"{k} {v}")
    IO.eprintln s!"DumpTypes: {text}"
