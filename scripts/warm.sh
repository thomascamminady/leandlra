#!/usr/bin/env bash
# What scripts/fc will check against: the state of the installed `.olean` files. Read-only: it
# builds nothing, does not regenerate the root files and writes nothing (until 2026-11-10 this
# script ran `scripts/gen_root.sh` and `lake build LeanDLRA` and saved a snapshot of the imported
# library for `lean --incr-load`; scripts/fc no longer uses a snapshot, see there).
#
#   scripts/warm.sh            summary for the core and the catalogue, exit 1 if the core is not
#                              completely installed and up to date
#   scripts/warm.sh --list     also name the modules that are not up to date
#
# For every module of LeanDLRA.lean (core) and LeanDLRACatalogue.lean (catalogue):
#   missing   no `.olean`: a file that imports the module cannot be checked (fc exits with 4);
#   stale     the source is newer than the `.olean`: fc checks against the older, installed state;
#   behind    an imported module of the library has a newer `.olean`: the module was compiled
#             against an older state of that import.
# The catalogue is built apart from the core (`scripts/catalogue.sh`), so `behind` is its normal
# state between two catalogue builds. A leftover snapshot of the old fc is reported with its size.
set -euo pipefail
ROOT="${FC_ROOT:-}"
if [ -z "$ROOT" ]; then
  ROOT="$(cd "$(dirname "$0")" && pwd)"
  while [ "$ROOT" != "/" ] && [ ! -f "$ROOT/lakefile.toml" ]; do ROOT="$(dirname "$ROOT")"; done
fi
[ -f "$ROOT/lakefile.toml" ] || { echo "warm.sh: no lakefile.toml above $(dirname "$0")"; exit 2; }
cd "$ROOT"
list=0
[ "${1:-}" = "--list" ] && list=1
LIB=.lake/build/lib/lean
toolchain="$(cat lean-toolchain 2>/dev/null || echo unknown)"
echo "repository $ROOT, toolchain $toolchain"

modules_of() { grep -E '^import LeanDLRA\.' "$1" | awk '{print $2}'; }
core="$(modules_of LeanDLRA.lean)"
catalogue="$(modules_of LeanDLRACatalogue.lean | grep -v -x -F -f <(echo "$core") || true)"

bad_core=0
report() { # report NAME MODULES
  local name="$1" total=0 missing=0 stale=0 behind=0 m src olean imp io state
  for m in $2; do
    total=$((total + 1))
    src="${m//.//}.lean"
    olean="$LIB/${m//.//}.olean"
    state=""
    if [ ! -f "$olean" ]; then
      missing=$((missing + 1)); state="missing"
    else
      if [ "$src" -nt "$olean" ]; then stale=$((stale + 1)); state="stale"; fi
      for imp in $(awk '/^(public )?(meta )?import LeanDLRA\./{print $NF} /^(namespace|open|noncomputable|section|theorem|lemma|def|\/-!)/{exit}' "$src" 2>/dev/null); do
        io="$LIB/${imp//.//}.olean"
        if [ -f "$io" ] && [ "$io" -nt "$olean" ]; then
          behind=$((behind + 1)); state="$state behind($imp)"; break
        fi
      done
    fi
    if [ "$list" = 1 ] && [ -n "$state" ]; then echo "  $m: $state"; fi
  done
  echo "$name: $total modules, $missing missing, $stale stale, $behind behind"
  if [ "$name" = core ]; then bad_core=$((missing + stale + behind)); fi
}
report core "$core"
report catalogue "$catalogue"
if [ -f .lake/warm/universe.snap ]; then
  echo "leftover of the old fc: .lake/warm/universe.snap ($(du -h .lake/warm/universe.snap | cut -f1))," \
    "not used any more; it can be deleted together with universe.snap.deps and header.lean"
fi
if [ "$bad_core" -gt 0 ]; then
  echo "the core is not completely installed (a gate round may be running: tail -n 3 wip/gate.log)"
  exit 1
fi
echo "core installed and up to date: scripts/fc FILE.lean checks against it"
