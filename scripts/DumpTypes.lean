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
constant by its full name.  Auxiliary declarations (recursors, `casesOn`, `noConfusion`, equation
lemmas, `_proof_i`, matchers, …) are skipped.

It reads the `.olean` files directly, so it does not load the imports of those modules: printing a
type needs no environment, and walking all of Mathlib would page gigabytes into memory.

Usage, from the repository root:

* `lean --run scripts/DumpTypes.lean [--canonical] Prefix …`: every module below each prefix
  (`LeanDLRA.OpenProblems`), skipping stale `.olean` files whose source file no longer exists;
* `lean --run scripts/DumpTypes.lean [--canonical] --modules M₁ M₂ …`: exactly these modules.
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

/-- Last components of declarations generated automatically next to a user declaration. -/
def auxiliarySuffixes : List String :=
  ["casesOn", "recOn", "noConfusion", "noConfusionType", "below", "brecOn", "binductionOn",
    "ibelow", "ctorIdx", "toCtorIdx", "ctorElim", "ctorElimType", "eq_def", "eq_unfold",
    "congr_simp"]

/-- Whether a declaration is generated automatically: an internal name (`_proof_1`, `match_1`,
…), a structural recursor helper, or a lemma realized on demand in whichever module first needs
it (`eq_<n>`, `eq_def`, `congr_simp`). -/
def isAuxiliary (n : Name) : Bool :=
  let n := privateToUserName n
  n.isInternal ||
    match n with
    | .str _ s =>
      auxiliarySuffixes.contains s ||
        (s.startsWith "eq_" && s.length > 3 && (s.drop 3).all Char.isDigit)
    | _ => false

/-- The kind of a declaration, or `none` for kinds that are not dumped (recursors, quotients). -/
def kindOf : ConstantInfo → Option String
  | .thmInfo _ => some "theorem"
  | .defnInfo _ => some "def"
  | .opaqueInfo _ => some "opaque"
  | .axiomInfo _ => some "axiom"
  | .inductInfo _ => some "inductive"
  | .ctorInfo _ => some "constructor"
  | _ => none

/-- One JSON line per dumped declaration of the module `mod` stored in `file`. -/
unsafe def dumpModule (canonicalMode : Bool) (mod : String) (file : System.FilePath) :
    IO Unit := do
  let (data, region) ← readModuleData file
  let out ← IO.getStdout
  for info in data.constants do
    if canonicalMode then
      let some kind := kindOf info | continue
      if isAuxiliary info.name then continue
      let lps := info.levelParams
      let mut fields := [("name", toJson (normalizeName info.name).toString),
        ("module", toJson mod), ("kind", toJson kind),
        ("type", toJson s!"{lps.length} ⊢ {canonical lps info.type}")]
      if let .defnInfo d := info then
        fields := fields ++ [("value", toJson s!"{canonical lps d.value}")]
      out.putStrLn (Json.compress (Json.mkObj fields))
    else
      unless info.isTheorem do continue
      if info.name.isInternal then continue
      let typ := s!"{info.levelParams} ⊢ {eraseBinderNames info.type}"
      out.putStrLn (Json.compress (Json.mkObj [("name", info.name.toString), ("type", typ)]))
  region.free

/-- Path of a module below `root`, with the given extension. -/
def modulePath (root : System.FilePath) (mod : String) (ext : String) : System.FilePath :=
  (mod.splitOn "." |>.foldl (· / ·) root).addExtension ext

unsafe def main (args : List String) : IO Unit := do
  let root : System.FilePath := ".lake/build/lib/lean"
  let canonicalMode := args.contains "--canonical"
  let modulesMode := args.contains "--modules"
  let targets := args.filter (!·.startsWith "--")
  if modulesMode then
    for mod in targets do
      let file := modulePath root mod "olean"
      unless ← file.pathExists do
        throw <| IO.userError s!"no .olean for module {mod} (build it first): {file}"
      dumpModule canonicalMode mod file
  else
    for pre in targets do
      let dir := pre.splitOn "." |>.foldl (· / ·) root
      for file in ← dir.walkDir do
        unless file.extension == some "olean" do continue
        -- The module name and the source file, from the path below `root`.
        let rel := (file.withExtension "").components.drop (root.components.length)
        let source := (rel.foldl (· / ·) ("." : System.FilePath)).addExtension "lean"
        unless ← source.pathExists do continue
        dumpModule canonicalMode (".".intercalate rel) file
