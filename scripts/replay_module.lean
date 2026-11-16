import Lean.Replay
import Lean.Util.Path

/-!
Kernel replay of exactly one module: `leanchecker`'s `replayFromImports` without its
module-prefix matching.

  lake env lean --run scripts/replay_module.lean MODULE

`leanchecker M` replays every module whose name has `M` as a prefix, one task each, in one process.
Once a task has freed the `.olean` regions of its imports, the toolchain's `findOLean` cache can
still hold a module name that lives in them, and the next import in that process reads it from
unmapped memory (SIGSEGV on the Linux runners). `scripts/replay.sh` uses this script for the
modules whose name is a prefix of another module's name, and `leanchecker` for all others.
The code below is `replayFromImports` of the toolchain's `LeanChecker.lean` for one module; the
check itself is `Lean.Kernel.Environment.replay`, as in `leanchecker`.
-/

open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let [arg] := args | IO.eprintln "usage: replay_module.lean MODULE"; return 2
  let module := arg.toName
  initSearchPath (← findSysroot)
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants := {}
  -- The last ("most private") part subsumes the others.
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    newConstants := newConstants.insert name ci
  discard <| env.toKernelEnv.replay newConstants
  return 0
