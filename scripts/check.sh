#!/usr/bin/env bash
# Scope: both
# Certify Lean files: compiles with no errors AND no warnings (including the Mathlib style
# linters), no sorry/admit/axioms, and every declaration in the
# file depends only on the three standard axioms (propext, Classical.choice, Quot.sound).
# Usage: scripts/check.sh LeanDLRA/Path/File.lean [more files...]
set -uo pipefail
cd "$(dirname "$0")/.."
status=0
mkdir -p .lake/check
# At most two cold compiles at once: each one rebuilds a 2 GB heap, and with many agents running
# more than that makes the machine swap. A slot older than 20 minutes belongs to a killed process.
slot=""
release() { [ -n "$slot" ] && rmdir "$slot" 2>/dev/null; }
trap release EXIT
acquire() {
  while true; do
    find .lake/check -maxdepth 1 -name 'slot?' -mmin +20 -exec rmdir {} + 2>/dev/null
    for i in 1 2; do
      if mkdir ".lake/check/slot$i" 2>/dev/null; then slot=".lake/check/slot$i"; return; fi
    done
    sleep 3
  done
}
acquire
for f in "$@"; do
  if grep -nE '\bsorry\b|\bsorryAx\b|\badmit\b|^\s*(@\[[^]]*\]\s*)?((private|protected|noncomputable|scoped|local)\s+)*axiom\b|native_decide|implemented_by|\bextern\b|\bunsafe\b|debug\.skipKernelTC|\bdecide\s*:=\s*true' "$f"; then
    echo "FAIL [$f]: forbidden token found (see above)"; status=1; continue
  fi
  tmp=".lake/check/$(echo "$f" | tr '/' '_')"
  cp "$f" "$tmp"
  cat >> "$tmp" <<'LEAN'

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut bad : Array (Name × Name) := #[]
  let mut n : Nat := 0
  for (c, _) in env.constants.map₂.toList do
    n := n + 1
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        bad := bad.push (c, a)
  if bad.isEmpty then logInfo m!"AXIOM-CHECK OK ({n} declarations)"
  else logError m!"AXIOM-CHECK FAIL: {bad}"
LEAN
  # Same options as the [leanOptions] of lakefile.toml, so the Mathlib style linters run too.
  out=$(lake env lean -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false \
    -Dweak.linter.mathlibStandardSet=true -Dweak.linter.style.header=false \
    -DmaxSynthPendingDepth=3 "$tmp" 2>&1)
  if echo "$out" | grep -qE "error|declaration uses|warning"; then
    echo "$out" | grep -v '^Note\|^Hint\|̵' | head -60
    echo "FAIL [$f]"; status=1
  elif echo "$out" | grep -q "AXIOM-CHECK OK"; then
    echo "OK   [$f] $(echo "$out" | grep -o 'AXIOM-CHECK OK.*')"
  else
    echo "$out" | head -30; echo "FAIL [$f]: axiom check did not run"; status=1
  fi
done
exit $status
