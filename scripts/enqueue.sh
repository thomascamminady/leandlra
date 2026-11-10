#!/bin/zsh
# Queue a group of checked slices so that the gate processes them in ONE round.
#
# The gate (scripts/gate.py) takes whole groups from wip/ready, oldest first, as many as fit into
# its batch size; a group is never split over two rounds. A group is the slice files plus a marker
# wip/ready/<id>.group (JSON: id, files, renames, expect_changed, promote, queued), which this
# script writes last, by a rename, after all files have been moved in, under a lock. Slice files
# without a marker are handled as before (oldest first, a few per round, possibly split): do not
# copy files into wip/ready by hand.
#
# Usage:  scripts/enqueue.sh [OPTION ...] wip/UnifyX_A.lean wip/UnifyX_B.lean ...   (1 to 12 files)
#
#   --renames FILE.json   renamed declarations of this group, a JSON object old name -> new name;
#                         the gate merges them into docs/renames.json in the commit of the round
#   --expect-changed N    at most N declarations of the round may change or disappear (statement
#                         hash diff under the rename map); 0 for a group that only moves or renames
#   --promote MODULE      add this module to the core library (docs/promoted.txt); repeatable
#   --id ID               name of the group (default: time and process number)
#
# It returns as soon as the group is queued; the gate log (wip/gate.log) has the verdict: one line
# `PUSHED <title>` for the round or `REJECT <slice>: <reason>` for every file of the group. It
# waits only while a file of the same name is still queued from an earlier group, or during
# maintenance. Every file needs an entry in wip/manifest.json. The source files stay where they
# are (copies are queued).
#
# Maintenance: `mkdir wip/enqueue.lock` holds all groups back (for work that needs an idle gate
# once the queue has drained); `rmdir wip/enqueue.lock` releases them.

set -u
cd "${0:A:h}/.." || exit 2

max=12
usage() {
  print -u2 "usage: scripts/enqueue.sh [--renames FILE.json] [--expect-changed N] [--promote MODULE]..." \
    "[--id ID] SLICE.lean ...   (1 to $max files, one gate round)"
  exit 2
}
fail() {
  print -u2 "enqueue: $1"
  exit 2
}

renames="" expect="" id=""
promote=()
files=()
while (( $# )); do
  case "$1" in
    --renames|--expect-changed|--promote|--id)
      (( $# >= 2 )) || usage
      case "$1" in
        --renames) renames="$2" ;;
        --expect-changed) expect="$2" ;;
        --promote) promote+=("$2") ;;
        --id) id="$2" ;;
      esac
      shift 2 ;;
    --renames=*) renames="${1#*=}"; shift ;;
    --expect-changed=*) expect="${1#*=}"; shift ;;
    --promote=*) promote+=("${1#*=}"); shift ;;
    --id=*) id="${1#*=}"; shift ;;
    --) shift; files+=("$@"); break ;;
    -*) print -u2 "enqueue: unknown option $1"; usage ;;
    *) files+=("$1"); shift ;;
  esac
done

(( ${#files} >= 1 && ${#files} <= max )) || usage
names=("${(@)files:t}")
distinct=("${(@u)names}")
keys=("${(@)names:r}")
(( ${#distinct} == ${#names} )) || fail "the same file name twice: ${(j:, :)names}"
for f in "${files[@]}"; do
  [[ -f "$f" && "$f" == *.lean ]] || fail "not a slice file: $f"
  grep -q "^  \"${f:t:r}\": {" wip/manifest.json || fail "no entry in wip/manifest.json for ${f:t:r}"
done
[[ -z "$expect" || "$expect" == <-> ]] || fail "--expect-changed: not a number: $expect"
for m in "${promote[@]}"; do
  [[ "$m" =~ "^LeanDLRA(\.[A-Za-z_][A-Za-z0-9_']*)+$" ]] || fail "--promote: not a module name: $m"
done
[[ -z "$renames" || -f "$renames" ]] || fail "--renames: no such file: $renames"
[[ -n "$id" ]] || id="$(date '+%Y%m%d-%H%M%S')-$$"
[[ "$id" =~ "^[A-Za-z0-9][A-Za-z0-9_.-]*$" && "$id" != legacy ]] || fail "--id: not a group name: $id"
[[ ! -e "wip/ready/$id.group" ]] || fail "--id: a group $id is already queued"

# The marker, complete before anything is queued.
marker="$(uv run -q --no-project python - "$id" "$expect" "$renames" "${(j:,:)promote}" "${names[@]}" <<'PY'
import datetime
import json
import re
import sys

gid, expect, renames, promote, *files = sys.argv[1:]
marker: dict[str, object] = {"id": gid, "files": files}
if renames:
    try:
        with open(renames, encoding="utf-8") as f:
            table = json.load(f)
    except (OSError, ValueError) as err:
        sys.exit(f"enqueue: --renames {renames}: {err}")
    ident = re.compile(r"[^\s()\[\]{}⦃⦄,]+")
    if not isinstance(table, dict) or not all(
        isinstance(new, str) and ident.fullmatch(old) and ident.fullmatch(new) and old != new
        for old, new in table.items()
    ):
        sys.exit(f"enqueue: --renames {renames}: expected a JSON object old name -> new name")
    marker["renames"] = table
if expect:
    marker["expect_changed"] = int(expect)
if promote:
    marker["promote"] = promote.split(",")
marker["queued"] = datetime.datetime.now().isoformat(timespec="seconds")
print(json.dumps(marker, ensure_ascii=False, indent=1))
PY
)" || exit 2

lock=wip/enqueue.lock
stage=wip/ready/.incoming.$$
partial=wip/ready/.$id.group.tmp
held=0
moved=()
cleanup() {
  if (( held )); then
    # Without its marker a group would be taken apart as loose files: take it back.
    (( ${#moved} )) && rm -f "${moved[@]}"
    rm -rf "$stage" "$partial"
    rmdir "$lock" 2>/dev/null
  fi
}
trap cleanup EXIT
trap 'exit 130' INT TERM

mkdir -p wip/ready
told=0
while true; do
  if mkdir "$lock" 2>/dev/null; then
    held=1
    busy=()
    for n in "${names[@]}"; do [[ -e "wip/ready/$n" ]] && busy+=("$n"); done
    if (( ${#busy} == 0 )); then
      mkdir -p "$stage"
      for f in "${files[@]}"; do cp "$f" "$stage/" || exit 1; done
      print -r -- "$marker" > "$partial" || exit 1
      # Renames within one directory tree. The gate takes the files only with their marker (loose
      # files only when they are two minutes old), so it sees the whole group or nothing.
      for n in "${names[@]}"; do
        mv "$stage/$n" wip/ready/ || exit 1
        moved+=("wip/ready/$n")
      done
      mv "$partial" "wip/ready/$id.group" || exit 1
      moved=()
      rmdir "$stage"
      rmdir "$lock"
      held=0
      print "enqueue: queued ${#files} file(s) at $(date '+%H:%M:%S'): ${(j:, :)keys} (group $id)"
      exit 0
    fi
    rmdir "$lock"
    held=0
    (( told )) || print -u2 "enqueue: waiting, still queued from an earlier group: ${(j:, :)busy}"
    told=1
  fi
  sleep "${ENQUEUE_POLL:-20}"
done
