import LeanDLRA

/-!
Writes `wip/index.json`, the declaration inventory of step 1 of `wip/PLAN.md`: every declaration of
the library with its module, kind, whether it is private, structural hashes of its type and (for
definitions) its body, the library declarations its type mentions, and the library declarations its
type or proof uses. `scripts/connectivity.py` reads it to find orphan modules, theorems stated only in
local definitions, duplicate statements and definitions that unfold to the same term.
Run with `lake env lean scripts/Inventory.lean`.
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

#eval show CommandElabM Unit from do
  let env ← getEnv
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
      ("private", toJson (isPrivateName c)), ("typeHash", toJson (toString info.type.hash)),
      ("bodyHash", toJson bodyHash),
      ("typeUses", toJson (libraryRefs env c info.type)),
      ("uses", toJson (libraryRefs env c info.type ++
        ((value.map (libraryRefs env c)).getD #[])))]
  IO.FS.writeFile "wip/index.json" (Json.compress (Json.arr out))
  logInfo m!"wrote wip/index.json ({out.size} declarations)"
