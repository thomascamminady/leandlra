#!/usr/bin/env bash
# Build and check everything, the core library and the catalogue (docs/STRUCTURE.md), outside the gate.
#
# The gate (scripts/gate.py) builds and audits the core and the slices of a round only. A change of a
# core definition can therefore break a catalogue module that the round did not touch. This script
# finds such modules: it builds LeanDLRACatalogue, lists the modules that fail, and, if all compile,
# runs the axiom audit and the statement check over everything. CI runs the same checks on every
# push (.github/workflows/catalogue.yml); run this script locally when a current build of everything
# is needed, for example before `make dump`.
#
# Last comes the sweep. The gate keeps a rolling dump of all statements (scripts/rolling.py) and
# refreshes, in a round, only the modules of that round. A core change can alter the elaborated
# statement of a catalogue theorem that no round touched; a fresh dump of everything, compared
# with the rolling dump, shows it. Read the report before seeding again
# (`uv run -q scripts/rolling.py seed`): seeding absorbs whatever changed.
#
# It needs an idle gate and holds wip/enqueue.lock while it runs, so no group is queued meanwhile.
# Exit status: 0 everything is fine, 1 a module or a check fails, 3 the gate is busy, 4 the sweep
# found statements that differ from the rolling dump of the gate (.lake/hashdiff/sweep.md).
set -uo pipefail
cd "$(dirname "$0")/.."
lock=wip/enqueue.lock
log=.lake/check/catalogue.log
mkdir -p .lake/check wip/ready
if ! mkdir "$lock" 2>/dev/null; then
  echo "catalogue: $lock is held (a group is being queued, or maintenance): try again later"; exit 3
fi
trap 'rmdir "$lock" 2>/dev/null' EXIT
if [ -n "$(find wip/ready -maxdepth 1 -name '*.lean' -print -quit)" ]; then
  echo "catalogue: the gate is busy (wip/ready is not empty): try again later"; exit 3
fi
sha=$(git rev-parse --short HEAD)
start=$(date +%s)
LEAN_NUM_THREADS="${GATE_LEAN_THREADS:-5}" nice -n 10 lake build --wfail LeanDLRACatalogue > "$log" 2>&1
code=$?
# Lake marks a failed module with ✖ and a module with warnings (a failure under --wfail) with ⚠.
broken=$(grep -E '^(✖|⚠) \[[0-9]+/[0-9]+\]' "$log" | awk '{print $4}' | sort -u)
minutes=$(( ($(date +%s) - start) / 60 ))
if [ "$code" -ne 0 ]; then
  count=$(printf '%s\n' "$broken" | grep -c . || true)
  echo "CATALOGUE BROKEN $sha: $count module(s) fail (${minutes} min), full log in $log"
  printf '%s\n' "$broken"
  exit 1
fi
echo "catalogue: build of everything is current (${minutes} min)"
scripts/audit.sh LeanDLRACatalogue || { echo "CATALOGUE BROKEN $sha: axiom audit"; exit 1; }
uv run -q scripts/fidelity.py || { echo "CATALOGUE BROKEN $sha: statement check"; exit 1; }
rolling=.lake/hashdiff/rolling.jsonl.gz
if [ -f "$rolling" ]; then
  full=.lake/hashdiff/full.jsonl.gz
  uv run -q scripts/hashdiff.py dump "$full" --lib=LeanDLRACatalogue \
    || { echo "CATALOGUE BROKEN $sha: dump of everything"; exit 1; }
  if ! uv run -q scripts/hashdiff.py diff "$rolling" "$full" --move \
      --report=.lake/hashdiff/sweep.md; then
    echo "CATALOGUE SWEEP $sha: statements differ from the rolling dump (.lake/hashdiff/sweep.md)"
    exit 4
  fi
fi
echo "CATALOGUE OK $sha: build, axiom audit, statement check and sweep of everything"
