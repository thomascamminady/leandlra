import LeanDLRACatalogue

/-!
Writes `wip/index.json`, the declaration inventory of step 1 of `wip/PLAN.md`: every declaration of
the library with its module, kind, finer kind (`defKind`: instance, scopedInstance, projection,
notation, abbrev, def, class, structure, inductive, theorem, opaque), whether it is private,
structural hashes of its type and (for definitions) its body, the library declarations its type
mentions, and the library declarations its type or proof uses. `scripts/connectivity.py` reads it
to find orphan modules, theorems stated only in local definitions, duplicate statements,
definitions that unfold to the same term, and definitions outside a `Defs.lean`.
Run with `lake env lean scripts/Inventory.lean`; set `INVENTORY_OUT` to write another file.
-/

open Lean Elab Command

/-- Library declarations (other than `self`) that occur in `e`. -/
def libraryRefs (env : Environment) (self : Name) (e : Expr) : Array String :=
  e.getUsedConstants.foldl (init := #[]) fun acc d =>
    match env.getModuleIdxFor? d with
    | some i =>
      if (`LeanDLRA).isPrefixOf env.header.moduleNames[i.toNat]! && d != self && !d.isInternal
          && !acc.contains d.toString then acc.push d.toString else acc
    | none => acc

/-- Names of the scoped instances, which `Meta.isInstanceCore` sees only inside their namespace. -/
def scopedInstances (env : Environment) : NameSet :=
  (Meta.instanceExtension.ext.getState env).scopedEntries.map.fold (init := {}) fun acc _ es =>
    es.foldl (init := acc) fun acc e => match e.globalName? with
      | some n => acc.insert n
      | none => acc

/-- The finer kind of a declaration, for the definition-location rule of `docs/CONVENTIONS.md` §3
(projections and notation are generated; scoped instances are exempt). -/
def defKind (env : Environment) (scopedInsts : NameSet) (c : Name) : ConstantInfo → String
  | .defnInfo d =>
    if Meta.isInstanceCore env c then "instance"
    else if scopedInsts.contains c then "scopedInstance"
    else if env.isProjectionFn c then "projection"
    else if d.type.isConstOf ``ParserDescr || d.type.isConstOf ``TrailingParserDescr then "notation"
    else if d.hints.isAbbrev then "abbrev"
    else "def"
  | .thmInfo _ => if env.isProjectionFn c then "projection" else "theorem"
  | .inductInfo _ =>
    if isClass env c then "class" else if isStructure env c then "structure" else "inductive"
  | .opaqueInfo _ => "opaque"
  | _ => "other"

#eval show CommandElabM Unit from do
  let env ← getEnv
  let scopedInsts := scopedInstances env
  let path := (← IO.getEnv "INVENTORY_OUT").getD "wip/index.json"
  let mut out : Array Json := #[]
  for (c, info) in env.constants.toList do
    if c.isInternal then continue
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`LeanDLRA).isPrefixOf mod do continue
    if isAuxRecursor env c || isNoConfusion env c then continue
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "def"
      | .inductInfo _ => "structure"
      | .ctorInfo _ => "constructor"
      | .opaqueInfo _ => "opaque"
      | _ => "other"
    if kind == "constructor" || kind == "other" then continue
    let value := info.value? (allowOpaque := true)
    let bodyHash := match info, value with
      | .defnInfo _, some v => toString v.hash
      | _, _ => ""
    out := out.push <| Json.mkObj [
      ("name", toJson c.toString), ("module", toJson mod.toString), ("kind", toJson kind),
      ("defKind", toJson (defKind env scopedInsts c info)),
      ("private", toJson (isPrivateName c)), ("typeHash", toJson (toString info.type.hash)),
      ("bodyHash", toJson bodyHash),
      ("typeUses", toJson (libraryRefs env c info.type)),
      ("uses", toJson (libraryRefs env c info.type ++
        ((value.map (libraryRefs env c)).getD #[])))]
  IO.FS.writeFile path (Json.compress (Json.arr out))
  logInfo m!"wrote {path} ({out.size} declarations)"
