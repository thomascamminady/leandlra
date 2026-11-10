#!/usr/bin/env bash
# Build the snapshot behind scripts/fc: the state after `import Mathlib` + the core library (the
# modules listed in LeanDLRA.lean, docs/STRUCTURE.md), with the same options as lakefile.toml.
# Rerun after `lake build LeanDLRA` so new core modules become visible.  Catalogue modules are not
# in the snapshot: a file that imports one is checked with scripts/check.sh instead.
set -euo pipefail
cd "$(dirname "$0")/.."
WARM=.lake/warm
mkdir -p "$WARM/tmp"
scripts/gen_root.sh
lake build LeanDLRA
lake env | grep -E '^(LEAN_PATH|LEAN_SYSROOT|LAKE_HOME|ELAN_TOOLCHAIN)=' | sed 's/^/export /' > "$WARM/env.sh"
# Every core module by name, not the root file: the root changes whenever a module is added,
# while the existing oleans stay valid, so the snapshot survives gate commits.
{ echo 'import Mathlib'; grep -E '^import ' LeanDLRA.lean; } > "$WARM/header.new.lean"
# shellcheck disable=SC1091
source "$WARM/env.sh"
new="$WARM/universe.snap.new"
lean --incr-header-save="$new" -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false \
  -Dweak.linter.mathlibStandardSet=true -Dweak.linter.style.header=false \
  -DmaxSynthPendingDepth=3 "$WARM/header.new.lean"
# Atomic swap, so a check that is running keeps its old snapshot and a new one sees the new file.
mv "$new.deps" "$WARM/universe.snap.deps"
mv "$new" "$WARM/universe.snap"
mv "$WARM/header.new.lean" "$WARM/header.lean"
echo "snapshot ready: $(du -h "$WARM/universe.snap" | cut -f1)"
