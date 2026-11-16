#!/usr/bin/env bash
# Replay library modules through the kernel with leanchecker, one at a time.
#   scripts/replay.sh                  every module (build LeanDLRACatalogue first)
#   scripts/replay.sh <commit>         the modules changed since <commit> (all if the commit is unknown)
#   scripts/replay.sh <commit> core    the same, restricted to the core library (the modules listed in
#                                      LeanDLRA.lean); use "" as commit for the whole core
set -euo pipefail
cd "$(dirname "$0")/.."
# leanchecker overflows the default 8 MB stack of the Linux runners on some modules (exit 139
# on FixedRank.TangentSpace since 2026-11-10). Raise the soft limit to 1 GiB, or to the hard
# limit where that is lower (macOS: 64 MiB); threads created by glibc inherit it.
ulimit -s 1048576 2>/dev/null || ulimit -s "$(ulimit -Hs)" 2>/dev/null || true
base="${1:-}"
scope="${2:-all}"
case "$scope" in
  all|core) ;;
  *) echo "usage: scripts/replay.sh [COMMIT] [all|core]" >&2; exit 2 ;;
esac
if [ -n "$base" ] && git cat-file -e "$base^{commit}" 2>/dev/null; then
  files=$(git diff --name-only --diff-filter=AM "$base" HEAD -- 'LeanDLRA/*.lean' 'LeanDLRA/**/*.lean')
else
  files=$(git ls-files 'LeanDLRA/*.lean' 'LeanDLRA/**/*.lean')
fi
count=0
for f in $files; do
  module=$(echo "${f%.lean}" | tr '/' '.')
  if [ "$scope" = core ] && ! grep -qxF "import $module" LeanDLRA.lean; then
    continue
  fi
  echo "replaying $module"
  lake env leanchecker "$module"
  count=$((count + 1))
done
echo "kernel replay OK: $count modules ($scope)"
