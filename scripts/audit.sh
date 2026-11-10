#!/usr/bin/env bash
# Axiom audit: builds the given targets, then checks that every constant of their `LeanDLRA` modules
# (private and generated ones included, whatever their namespace) depends only on propext,
# Classical.choice, Quot.sound, and that no source file contains placeholders.
#
#   scripts/audit.sh                      the core library (target LeanDLRA)
#   scripts/audit.sh LeanDLRACatalogue    everything: the core and the catalogue
#   scripts/audit.sh LeanDLRA MODULE...   the core and the listed modules (what the gate runs)
#
# A target is a library (LeanDLRA, LeanDLRACatalogue) or a module name (docs/STRUCTURE.md).
set -uo pipefail
cd "$(dirname "$0")/.."
if [ "$#" -eq 0 ]; then set -- LeanDLRA; fi
for target in "$@"; do
  if ! [[ "$target" =~ ^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$ ]]; then
    echo "AUDIT FAIL: not a library or module name: $target"; exit 1
  fi
done
# The placeholder scan covers all sources, also those outside the targets.
if grep -rnE '\bsorry\b|\bsorryAx\b|\badmit\b|^\s*(@\[[^]]*\]\s*)?((private|protected|noncomputable|scoped|local)\s+)*axiom\b|native_decide|implemented_by|\bextern\b|\bunsafe\b|debug\.skipKernelTC|\bdecide\s*:=\s*true' LeanDLRA; then
  echo "AUDIT FAIL: placeholder or custom axiom in sources"; exit 1
fi
lake build "$@" || { echo "AUDIT FAIL: build"; exit 1; }
mkdir -p .lake/check
{
  for target in "$@"; do echo "import $target"; done
  cat <<'LEAN'
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut bad : Array (Name × Name) := #[]
  let mut n : Nat := 0
  for (c, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    unless (`LeanDLRA).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    n := n + 1
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        bad := bad.push (c, a)
  let k := (env.header.moduleNames.filter fun m => (`LeanDLRA).isPrefixOf m && m != `LeanDLRA).size
  if bad.isEmpty then
    logInfo m!"AUDIT OK: {n} constants in {k} LeanDLRA modules, standard axioms only"
  else logError m!"AUDIT FAIL: {bad}"
LEAN
} > .lake/check/Audit.lean
out=$(lake env lean .lake/check/Audit.lean 2>&1); echo "$out" | tail -5
echo "$out" | grep -q "AUDIT OK" || exit 1
echo "audited targets: $*"
