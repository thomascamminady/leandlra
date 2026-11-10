import LeanDLRACatalogue

/-!
Writes `website/decls.json`: every declaration of the library with its module, kind, source
line and the first line of its docstring. Used by `scripts/build_site.py` to link Lean names to
their source and API documentation. Run with `lake env lean scripts/DeclIndex.lean`.
-/

open Lean Elab Command

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
    let line ← match ← liftCoreM (findDeclarationRanges? c) with
      | some r => pure r.range.pos.line
      | none => pure 0
    let doc := ((← findDocString? env c).getD "").splitOn "\n" |>.head!
    -- direct dependencies on other library declarations (type and proof/body)
    let refs := info.type.getUsedConstants ++ ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
    let uses := refs.foldl (init := (#[] : Array String)) fun acc d =>
      match env.getModuleIdxFor? d with
      | some i =>
        if (`LeanDLRA).isPrefixOf env.header.moduleNames[i.toNat]! && d != c && !d.isInternal
            && !acc.contains d.toString then acc.push d.toString else acc
      | none => acc
    out := out.push <| Json.mkObj [("name", toJson c.toString), ("module", toJson mod.toString),
      ("kind", toJson kind), ("line", toJson line), ("doc", toJson doc), ("uses", toJson uses)]
  IO.FS.writeFile "website/decls.json" (Json.compress (Json.arr out))
  logInfo m!"wrote website/decls.json ({out.size} declarations)"
