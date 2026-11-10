#!/bin/zsh
# Queue a group of checked slices so that the gate processes them in ONE round.
#
# The gate (scripts/gate.py) takes the oldest files of wip/ready, up to its batch size, in every
# round. The files of one batch (for example a new Defs.lean and the files that import it) must
# not be split over two rounds, and the groups of two agents must not interleave: a split group
# fails the whole-library build and costs a full round. This script waits until wip/ready is
# empty, that is, until the gate has finished everything queued before, and then moves the whole
# group in at once, under a lock.
#
# Usage:  scripts/enqueue.sh wip/UnifyX_A.lean wip/UnifyX_B.lean ...     (1 to 6 files)
#
# It blocks until the group is queued (possibly for hours): run it as one background command and
# wait for its exit; do not poll. Every file needs an entry in wip/manifest.json. The source files
# stay where they are (copies are queued).
#
# Maintenance: `mkdir wip/enqueue.lock` holds all waiting groups back (for work that needs an idle
# gate); `rmdir wip/enqueue.lock` releases them.

set -u
cd "${0:A:h}/.." || exit 2

max=6
if (( $# < 1 || $# > max )); then
  print -u2 "usage: scripts/enqueue.sh SLICE.lean ...   (1 to $max files, one gate round)"
  exit 2
fi
for f in "$@"; do
  if [[ ! -f "$f" || "$f" != *.lean ]]; then
    print -u2 "enqueue: not a slice file: $f"
    exit 2
  fi
  if ! grep -q "^  \"${f:t:r}\": {" wip/manifest.json; then
    print -u2 "enqueue: no entry in wip/manifest.json for ${f:t:r}"
    exit 2
  fi
done

lock=wip/enqueue.lock
stage=wip/ready/.incoming.$$
held=0
cleanup() {
  if (( held )); then
    rm -rf "$stage"
    rmdir "$lock" 2>/dev/null
  fi
}
trap cleanup EXIT
trap 'exit 130' INT TERM

mkdir -p wip/ready
while true; do
  if mkdir "$lock" 2>/dev/null; then
    held=1
    queued=(wip/ready/*.lean(N))
    if (( ${#queued} == 0 )); then
      mkdir -p "$stage"
      for f in "$@"; do cp "$f" "$stage/" || exit 1; done
      # Renames within one directory tree: the gate (polling every 15 s) sees all or nothing.
      for f in "$@"; do mv "$stage/${f:t}" wip/ready/ || exit 1; done
      rmdir "$stage"
      rmdir "$lock"
      held=0
      print "enqueue: queued $# file(s) at $(date '+%H:%M:%S'): ${(j:, :)${@:t:r}}"
      exit 0
    fi
    rmdir "$lock"
    held=0
  fi
  sleep 20
done
