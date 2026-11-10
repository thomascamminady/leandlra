# /// script
# requires-python = ">=3.11"
# dependencies = ["fire"]
# ///
"""The only path from a proof attempt to `main`.

Agents queue checked slices with ``scripts/enqueue.sh``: the slices go to ``wip/ready/`` together with
a marker ``<id>.group`` that names them.  A round takes whole groups in the order of their arrival
(slices without a marker are *legacy*: the oldest few form one pseudo-group) and, for the round:

1. checks every file (manifest entry, forbidden tokens, rename map, promotions), copies the slices to
   their targets and builds them with ``lake build --wfail``, so any warning fails;
2. regenerates the root files, checks that the core imports no catalogue module
   (``scripts/core.py``), builds the core library and audits the core and the slices
   (``scripts/audit.sh``);
3. merges the renames of the groups into ``docs/renames.json`` and checks, with
   ``scripts/rolling.py``, the recorded statements (fidelity) and the changed declarations (hashdiff)
   on the core modules and the slices;
4. commits exactly its own files and pushes.

A failure in 1 rejects the group of the failing slice (a legacy slice alone) and the round goes on.
A failure in 2-3 restores the tree; a round of several groups is then repeated group by group, so
that one bad group does not reject the others.  Nothing is pushed unless every step passed.  A journal
(``wip/gate.round.json``) records what a round put into the tree: after a kill, the next start
restores the tree or finishes the push.  ``--dry-run`` prints what the next round would do.
"""

from __future__ import annotations

import dataclasses
import gzip
import json
import os
import re
import shutil
import subprocess
import sys
import time
from collections.abc import Callable, Mapping, Sequence
from collections.abc import Set as AbstractSet
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, TypedDict

ROOT = Path(__file__).resolve().parent.parent
TRAILER = "Co-Authored-By: Claude <noreply@anthropic.com>"
FORBIDDEN = re.compile(
    r"\bsorry\b|\bsorryAx\b|\badmit\b|^\s*(@\[[^]]*\]\s*)?"
    r"((private|protected|noncomputable|scoped|local)\s+)*axiom\b|native_decide|implemented_by"
    r"|\bextern\b|\bunsafe\b|debug\.skipKernelTC|\bdecide\s*:=\s*true",
    re.MULTILINE,
)
PUSH = ("git", "push", "-q", "git@github.com:thomascamminady/leandlra.git", "HEAD:main")
ROOTS = ("LeanDLRA.lean", "LeanDLRACatalogue.lean")
# The core build: with `--wfail`, so a core module that a slice of the round makes warn fails too.
CORE_BUILD = ("lake", "build", "--wfail", "LeanDLRA")
# The last commit that touched one of these paths dates the rolling dump (scripts/rolling.py).
LIBRARY = ("LeanDLRA", *ROOTS)
RENAMES, PROMOTED = "docs/renames.json", "docs/promoted.txt"
HASHDIR = ".lake/hashdiff"
ROLLING = ("rolling.jsonl.gz", "rolling_statements.jsonl.gz")
TOOL = ("uv", "run", "-q", "scripts/rolling.py")
LEGACY = "legacy"
IDENT = re.compile(r"[^\s()\[\]{}⦃⦄,]+")  # a constant name, as in scripts/fidelity.py
MODULE = re.compile(r"LeanDLRA(\.[A-Za-z_][A-Za-z0-9_']*)+")
SLICE_FILE = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_'-]*\.lean")

Run = Callable[..., tuple[int, str]]


class Slice(TypedDict):
    """One entry of `wip/manifest.json`."""

    source: str
    target: str
    stubs: list[str]
    ops: list[str]
    chars: int


@dataclass(frozen=True)
class Group:
    """Slices that enter `main` together or not at all (``marker`` is None for legacy slices)."""

    id: str
    files: tuple[str, ...]
    renames: Mapping[str, str] = field(default_factory=dict)
    expect_changed: int | None = None
    promote: tuple[str, ...] = ()
    marker: str | None = None
    age: float = 0.0

    @property
    def atomic(self) -> bool:
        """Whether one bad slice rejects the whole group."""
        return self.marker is not None


@dataclass(frozen=True)
class BadMarker:
    """A marker that cannot be processed, with the files it is known to name."""

    name: str
    reason: str
    files: tuple[str, ...] = ()


@dataclass(frozen=True)
class Selection:
    """The groups of the next round and the markers to reject."""

    groups: list[Group]
    bad: list[BadMarker]


@dataclass(frozen=True)
class Stats:
    """The summary of `scripts/rolling.py diff`."""

    base: str
    declarations: int
    changed: int
    moved: int
    added: int
    removed: int


@dataclass(frozen=True)
class Attempt:
    """The outcome of one attempt: ``pushed``, ``empty`` (no group left), ``failed`` or ``stop``."""

    status: str
    stage: str = ""
    reason: str = ""
    groups: tuple[Group, ...] = ()


# ---------------------------------------------------------------------------------------------
# Pure parts: markers, selection, rename map, log lines


def module_name(target: str) -> str:
    """``LeanDLRA/A/B.lean`` → ``LeanDLRA.A.B``."""
    return target.removesuffix(".lean").replace("/", ".")


def module_path(module: str) -> str:
    """``LeanDLRA.A.B`` → ``LeanDLRA/A/B.lean``."""
    return module.replace(".", "/") + ".lean"


def key(name: str) -> str:
    """The manifest key of a slice file name."""
    return name.removesuffix(".lean")


def parse_marker(name: str, text: str, age: float) -> Group | BadMarker:
    """Read a marker ``<id>.group``: a JSON object with ``files`` (the slice file names, in order)
    and optionally ``id`` (the file name without `.group`), ``renames`` (old name → new name),
    ``expect_changed`` (integer ≥ 0), ``promote`` (module names) and ``queued`` (a time, not
    read: the age of a group is the modification time of its marker)."""
    gid = name.removesuffix(".group")
    try:
        raw: Any = json.loads(text)
    except ValueError as err:
        return BadMarker(name, f"not JSON ({err})")
    files: Any = raw.get("files") if isinstance(raw, dict) else None
    if not (
        isinstance(files, list)
        and files
        and all(isinstance(f, str) and SLICE_FILE.fullmatch(f) for f in files)
        and len(set(files)) == len(files)
    ):
        return BadMarker(name, "files: expected a list of distinct slice file names")
    renames: Any = raw.get("renames", {})
    expect: Any = raw.get("expect_changed")
    promote: Any = raw.get("promote", [])
    problem = ""
    if raw.get("id", gid) != gid:
        problem = "id differs from the file name"
    elif not isinstance(renames, dict) or not all(
        isinstance(v, str) for v in renames.values()
    ):
        problem = "renames: expected an object old name -> new name"
    elif expect is not None and (type(expect) is not int or expect < 0):
        problem = "expect_changed: expected a non-negative integer"
    elif not isinstance(promote, list) or not all(
        isinstance(m, str) and MODULE.fullmatch(m) for m in promote
    ):
        problem = "promote: expected a list of module names LeanDLRA.…"
    if problem:
        return BadMarker(name, problem, tuple(files))
    return Group(gid, tuple(files), renames, expect, tuple(promote), name, age)


def select_round(
    files: Mapping[str, float],
    markers: Sequence[Group | BadMarker],
    targets: Mapping[str, str],
    batch: int,
    legacy_max: int,
    now: float,
    grace: float,
) -> Selection:
    """Choose the groups of the next round.

    ``files`` maps the slice files of `wip/ready` to their modification times, ``targets`` manifest
    keys to target paths.  Marked groups (by marker time) and legacy files (by file time, visible
    once they are ``grace`` seconds old) form one queue.  From its head the round takes whole
    groups, and up to ``legacy_max`` consecutive legacy files as one pseudo-group, while the number
    of files stays within ``batch`` and no target is written twice; the first unit is always taken.
    Nothing overtakes a unit that does not fit.
    """
    bad = [m for m in markers if isinstance(m, BadMarker)]
    claimed: set[str] = {f for m in bad for f in m.files}
    marked: list[Group] = []
    for group in sorted(
        (m for m in markers if isinstance(m, Group)), key=lambda g: (g.age, g.id)
    ):
        missing = [f for f in group.files if f not in files]
        twice = [f for f in group.files if f in claimed]
        if missing or twice:
            reason = (
                f"{missing[0]} is not in wip/ready"
                if missing
                else f"{twice[0]} belongs to an older group"
            )
            rest = tuple(f for f in group.files if f in files and f not in claimed)
            bad.append(BadMarker(group.marker or group.id, reason, rest))
            claimed.update(rest)
            continue
        claimed.update(group.files)
        marked.append(group)
    units: list[tuple[float, str, Group | None]] = [(g.age, g.id, g) for g in marked]
    units += [
        (t, name, None)
        for name, t in files.items()
        if name not in claimed and now - t >= grace
    ]
    chosen: list[Group] = []
    legacy: list[str] = []
    slot, closed, count = 0, False, 0
    used: set[str] = set()
    for age, name, group in sorted(units, key=lambda u: (u[0], u[1])):
        names = group.files if group else (name,)
        wanted = {targets[key(f)] for f in names if key(f) in targets}
        if count and (count + len(names) > batch or wanted & used):
            break
        if group is None:
            if closed or len(legacy) >= legacy_max:
                break
            if not legacy:
                slot = len(chosen)
            legacy.append(name)
        else:
            closed = bool(legacy)
            chosen.append(group)
        count += len(names)
        used |= wanted
    if legacy:
        chosen.insert(
            slot, Group(LEGACY, tuple(legacy), age=min(files[f] for f in legacy))
        )
    return Selection(chosen, bad)


def merge_renames(base: Mapping[str, str], extra: Mapping[str, str]) -> dict[str, str]:
    """``base`` with the entries of ``extra``; ValueError on a conflict or a cycle.

    Chains are allowed (``A → B`` with ``B → C``: `fidelity.load_renames` follows them).
    """
    merged = dict(base)
    for old, new in extra.items():
        if not IDENT.fullmatch(old) or not IDENT.fullmatch(new):
            raise ValueError(f"not a pair of constant names: {old!r} -> {new!r}")
        if old == new:
            raise ValueError(f"{old} is mapped to itself")
        if merged.get(old, new) != new:
            raise ValueError(f"{old} is already mapped to {merged[old]}, not to {new}")
        merged[old] = new
    for old, first in merged.items():
        seen = [old]
        name = first
        while name in merged and merged[name] != name:
            if name in seen:
                raise ValueError(f"cycle: {' -> '.join([*seen, name])}")
            seen.append(name)
            name = merged[name]
    return merged


def stamp(message: str) -> str:
    """A line of the gate log."""
    return f"{time.strftime('%H:%M:%S')} {message}\n"


def reject_line(slice_key: str, reason: str) -> str:
    """The log line agents wait for when a slice is rejected."""
    return f"REJECT {slice_key}: {reason.strip().splitlines()[0][:160] if reason.strip() else ''}"


def commit_title(keys: Sequence[str], all_updated: bool) -> str:
    """The first line of the commit message; `PUSHED <title>` is the log line agents wait for."""
    verb = "Update" if all_updated else "Add"
    return f"{verb} {len(keys)} {'slices' if len(keys) > 1 else 'slice'} ({', '.join(keys)})"


def commit_message(title: str, ops: Sequence[str]) -> str:
    """The commit message of a round."""
    return f"{title}\n\n{' '.join(ops)}\n\n{TRAILER}\n"


def parse_stats(output: str) -> Stats | None:
    """The `HASHDIFF {...}` line printed by `scripts/rolling.py diff`."""
    for line in reversed(output.splitlines()):
        if line.startswith("HASHDIFF {"):
            try:
                return Stats(**json.loads(line.removeprefix("HASHDIFF ")))
            except (ValueError, TypeError):
                return None
    return None


def hashdiff_line(new: str, stats: Stats) -> str:
    """The log line with the declaration counts of a round."""
    return (
        f"HASHDIFF {stats.base}..{new}: {stats.declarations} declarations, {stats.changed} changed, "
        f"{stats.moved} moved, {stats.added} added, {stats.removed} removed"
    )


def core_line(sha: str, core: int, catalogue: int) -> str:
    """The log line with the coverage of an accepted round."""
    return (
        f"CORE {sha}: {core} core modules, {catalogue} slice modules in the catalogue"
    )


# ---------------------------------------------------------------------------------------------
# The gate


def shell(root: Path) -> Run:
    """The command runner of the real gate: exit code and combined output, run in ``root``."""

    def run(*cmd: str, timeout: int = 14400) -> tuple[int, str]:
        # At most five Lean workers: each needs over a gigabyte, and the 16 GB machine must not swap.
        env = {
            **os.environ,
            "LEAN_NUM_THREADS": os.environ.get("GATE_LEAN_THREADS", "5"),
        }
        proc = subprocess.run(
            cmd,
            cwd=root,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
            env=env,
        )
        return proc.returncode, proc.stdout + proc.stderr

    return run


class Gate:
    """The gate on one repository; every command goes through ``run`` (a fake one in the tests)."""

    def __init__(self, root: Path, run: Run, dry: bool = False) -> None:
        self.root, self.run, self.dry = root, run, dry
        self.wip = root / "wip"
        self.ready, self.rejected, self.done = (
            self.wip / "ready",
            self.wip / "rejected",
            self.wip / "done",
        )
        self.journal = self.wip / "gate.round.json"

    # -- small helpers ---------------------------------------------------------------------

    def log(self, message: str) -> None:
        """Append a timestamped line to the gate log (print it in a dry run)."""
        if self.dry:
            print(message)
            return
        with (self.wip / "gate.log").open("a", encoding="utf-8") as handle:
            handle.write(stamp(message))

    def table(self) -> dict[str, Slice]:
        """Slice table: `wip/manifest.json`."""
        return json.loads((self.wip / "manifest.json").read_text(encoding="utf-8"))

    def git(self, *args: str) -> str:
        """The output of a git command, stripped."""
        return self.run("git", *args)[1].strip()

    def tracked(self, rel: str) -> bool:
        """Whether a path is on `main` already."""
        return self.run("git", "cat-file", "-e", f"HEAD:{rel}")[0] == 0

    def read(self, rel: str) -> str | None:
        """The text of a file of the repository, None if it does not exist."""
        path = self.root / rel
        return path.read_text(encoding="utf-8") if path.exists() else None

    def scan(self) -> tuple[dict[str, float], list[Group | BadMarker]]:
        """The slice files of `wip/ready` with their times, and the markers.

        The markers are read first: `enqueue.sh` writes a marker after its files, so every file of
        a marker seen here is in the listing that follows.
        """
        markers = [
            parse_marker(p.name, p.read_text(encoding="utf-8"), p.stat().st_mtime)
            for p in sorted(self.ready.glob("*.group"))
        ]
        files = {p.name: p.stat().st_mtime for p in self.ready.glob("*.lean")}
        return files, markers

    # -- rejecting and restoring -----------------------------------------------------------

    def reject_file(self, name: str, reason: str) -> None:
        """Move a slice to `wip/rejected/` with the reason next to it."""
        self.rejected.mkdir(exist_ok=True)
        (self.rejected / f"{key(name)}.log").write_text(reason, encoding="utf-8")
        if (self.ready / name).exists():
            shutil.move(str(self.ready / name), str(self.rejected / name))
        self.log(reject_line(key(name), reason))

    def move_marker(self, marker: str | None, where: Path) -> None:
        """Take a marker out of the queue."""
        if marker and (self.ready / marker).exists():
            where.mkdir(exist_ok=True)
            shutil.move(str(self.ready / marker), str(where / marker))

    def reject_group(self, group: Group, reason: str) -> None:
        """Reject every slice of a group for the same reason."""
        for name in group.files:
            self.reject_file(name, reason)
        self.move_marker(group.marker, self.rejected)

    def reject_marker(self, bad: BadMarker) -> None:
        """Reject a marker and the files it is known to name."""
        self.log(f"BADGROUP {bad.name.removesuffix('.group')}: {bad.reason}")
        for name in bad.files:
            self.reject_file(name, f"group marker {bad.name}: {bad.reason}\n")
        self.move_marker(bad.name, self.rejected)

    def restore_target(self, rel: str) -> None:
        """Take a slice back out of the library tree.

        A module that is already on main (an audit fix of a landed file) is restored from ``HEAD``
        instead of deleted, so a rejected fix never removes a proven module.
        """
        if self.tracked(rel):
            self.run("git", "checkout", "-q", "HEAD", "--", rel)
            return
        self.run("git", "rm", "-q", "--cached", "--ignore-unmatch", rel)
        (self.root / rel).unlink(missing_ok=True)

    def settle(
        self,
        group: Group,
        problems: Sequence[tuple[str, str]],
        targets: Mapping[str, str],
    ) -> Group | None:
        """Reject what the problems ``(file or "", reason)`` of a group require; return what is left.

        A marked group is rejected as a whole, a legacy slice alone.  ``targets`` maps the files
        that are already in the tree to their targets, which are restored.
        """
        if not problems:
            return group
        bad = {name: reason for name, reason in problems if name}
        if group.atomic:
            first = next(iter(problems))
            why = (
                f"group {group.id} rejected: {key(first[0])}: {first[1]}"
                if first[0]
                else first[1]
            )
            for name in group.files:
                if name in targets:
                    self.restore_target(targets[name])
                self.reject_file(name, bad.get(name) or why)
            self.move_marker(group.marker, self.rejected)
            return None
        for name, reason in bad.items():
            if name in targets:
                self.restore_target(targets[name])
            self.reject_file(name, reason)
        rest = tuple(f for f in group.files if f not in bad)
        return dataclasses.replace(group, files=rest) if rest else None

    def screen(
        self,
        group: Group,
        table: Mapping[str, Slice],
        renames: Mapping[str, str],
        earlier: AbstractSet[str],
    ) -> tuple[list[tuple[str, str]], dict[str, str]]:
        """File-level checks of a group: its problems ``(file or "", reason)`` and the rename map
        with its entries.  ``earlier`` are the modules of the groups before it in the round.
        Nothing is written."""
        problems: list[tuple[str, str]] = []
        seen: dict[str, str] = {}
        for name in group.files:
            entry = table.get(key(name))
            if entry is None:
                problems.append((name, "not a slice of the manifest\n"))
                continue
            target = entry["target"]
            if not (
                target.startswith("LeanDLRA/")
                and target.endswith(".lean")
                and MODULE.fullmatch(module_name(target))
            ):
                problems.append((name, f"target outside the library: {target}\n"))
                continue
            if target in seen:
                problems.append(
                    (name, f"same target as {key(seen[target])}: {target}\n")
                )
                continue
            seen[target] = name
            if FORBIDDEN.search((self.ready / name).read_text(encoding="utf-8")):
                problems.append((name, "forbidden token in the source\n"))
        merged = dict(renames)
        try:
            merged = merge_renames(renames, group.renames)
        except ValueError as err:
            problems.append(("", f"renames: {err}\n"))
        modules = {module_name(target) for target in seen}
        for module in group.promote:
            if module not in modules | earlier and not self.tracked(
                module_path(module)
            ):
                problems.append(
                    ("", f"promote: {module} is neither in the group nor on main\n")
                )
        return problems, merged

    # -- journal and recovery --------------------------------------------------------------

    def save(self, journal: dict[str, Any]) -> None:
        """Write the journal of the running round (atomically)."""
        partial = self.journal.with_suffix(".tmp")
        partial.write_text(json.dumps(journal, indent=1), encoding="utf-8")
        os.replace(partial, self.journal)

    def restore(self, journal: dict[str, Any]) -> None:
        """Undo what a round put into the tree, then forget the round."""
        for rel in journal["targets"]:
            self.restore_target(rel)
        for rel in (RENAMES, PROMOTED):
            saved: dict[str, Any] | None = journal["saved"].get(rel)
            if saved is None:
                continue
            if saved["text"] is None:
                (self.root / rel).unlink(missing_ok=True)
            else:
                (self.root / rel).write_text(saved["text"], encoding="utf-8")
        # The root files as they are on main, not as the generator would write them now: the
        # tree is `HEAD` again even if a root file was committed out of step with the generator.
        for rel in ROOTS:
            self.restore_target(rel)
        # Nothing of the round stays staged, and its dump is not left for a later `accept`.
        self.run("git", "reset", "-q", "--", RENAMES, PROMOTED)
        self.run(*TOOL, "discard")
        self.journal.unlink(missing_ok=True)

    def keep(self, journal: dict[str, Any], rel: str) -> None:
        """Record the present content of a file in the journal before the round changes it."""
        if rel not in journal["saved"]:
            journal["saved"][rel] = {"text": self.read(rel)}
            self.save(journal)

    def round_commit(self, journal: dict[str, Any]) -> str:
        """The commit of a round ("" if there is none): the one with its title among the commits
        made since the round started (others, of documentation, may have been made on top)."""
        log = self.git("log", "--format=%h %s", f"{journal['base']}..HEAD")
        for line in log.splitlines():
            sha, _, subject = line.partition(" ")
            if subject == journal["title"]:
                return sha
        return ""

    def recover(self) -> bool:
        """Finish or undo a round that was interrupted; False if the gate must stop."""
        if not self.journal.exists():
            return True
        journal: dict[str, Any] = json.loads(self.journal.read_text(encoding="utf-8"))
        if journal["stage"] == "committing" and self.round_commit(journal):
            self.log(f"RECOVER publishing the committed round: {journal['title']}")
            return self.publish(journal)
        self.log(
            f"RECOVER restoring {len(journal['targets'])} targets of an interrupted round "
            f"({', '.join(key(f) for g in journal['groups'] for f in g['files'])})"
        )
        self.restore(journal)
        return True

    def preflight(self) -> str | None:
        """Why no round may start: a library tree that is not `HEAD`, or no usable rolling dump."""
        dirty = self.run(
            "git",
            "--no-optional-locks",
            "status",
            "--porcelain",
            "--",
            *LIBRARY,
            PROMOTED,
        )[1]
        if dirty.strip():
            return f"the library tree differs from HEAD\n{dirty[:800]}"
        for name in ROLLING:
            if not (self.root / HASHDIR / name).exists():
                return (
                    f"{HASHDIR}/{name} is missing: build everything, then seed it with "
                    "`uv run -q scripts/rolling.py seed`"
                )
        with gzip.open(self.root / HASHDIR / ROLLING[0], "rt", encoding="utf-8") as f:
            header: dict[str, Any] = json.loads(f.readline())
        library = self.git("rev-list", "-1", "HEAD", "--", *LIBRARY)
        if header.get("library_commit") != library:
            return (
                f"{HASHDIR}/{ROLLING[0]} describes {str(header.get('library_commit'))[:7]}, the "
                f"library is at {library[:7]}: refresh the changed modules with "
                "`uv run -q scripts/rolling.py dump MODULE ... && uv run -q scripts/rolling.py accept`"
                ", or seed again"
            )
        return None

    # -- one round -------------------------------------------------------------------------

    def fail(
        self, journal: dict[str, Any], live: Sequence[Group], stage: str, reason: str
    ) -> Attempt:
        """A failure of the round as a whole: restore the tree and report the groups it had."""
        self.log(f"ROUNDFAIL {stage}: {reason.strip().splitlines()[0][:160]}")
        self.restore(journal)
        return Attempt("failed", stage, reason, tuple(live))

    def stop(self, message: str) -> Attempt:
        """A failure that is not the fault of a group: the journal stays, the gate stops."""
        self.log(f"STOP: {message}")
        return Attempt("stop")

    def keep_report(self, label: str) -> str:
        """Give the hashdiff report of the round its final name."""
        source = self.root / HASHDIR / "round_report.md"
        target = f"{HASHDIR}/report_{label}.md"
        if source.exists():
            os.replace(source, self.root / target)
        return target

    def attempt(self, groups: Sequence[Group]) -> Attempt:
        """Run the given groups through the gate as one round."""
        table = self.table()
        renames: dict[str, str] = json.loads(self.read(RENAMES) or "{}")
        live: list[Group] = []
        earlier: set[str] = set()
        for group in groups:
            problems, merged = self.screen(group, table, renames, earlier)
            left = self.settle(group, problems, {})
            if left is not None:
                live.append(left)
                renames = merged
                earlier |= {module_name(table[key(f)]["target"]) for f in left.files}
        if not live:
            return Attempt("empty")
        targets = {f: table[key(f)]["target"] for g in live for f in g.files}
        journal: dict[str, Any] = {
            "base": self.git("rev-parse", "HEAD"),
            "stage": "applying",
            "title": "",
            "groups": [dataclasses.asdict(g) for g in live],
            "targets": sorted(set(targets.values())),
            "saved": {},
            "started": time.strftime("%Y-%m-%dT%H:%M:%S"),
        }
        self.save(journal)
        for name, rel in targets.items():
            (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(self.ready / name, self.root / rel)

        # 1. A cold build with the real imports in which any warning is a failure.  It is repeated
        # until it passes for exactly the slices that are left.
        while True:
            names = [f for g in live for f in g.files]
            modules = [module_name(targets[f]) for f in names]
            code, out = self.run("lake", "build", "--wfail", *modules)
            if code == 0:
                break
            failed = {
                f
                for f in names
                if re.search(
                    rf"(✖|⚠) \[\d+/\d+\] \w+ {re.escape(module_name(targets[f]))}(?![\w.])",
                    out,
                )
            }
            detail = "\n".join(
                line
                for line in out.splitlines()
                if "error" in line or "warning" in line
            )
            reason = f"lake build --wfail failed\n{detail[:6000]}\n"
            if not failed:
                return self.fail(journal, live, "slice build", reason)
            live = [
                left
                for g in live
                if (
                    left := self.settle(
                        g, [(f, reason) for f in g.files if f in failed], targets
                    )
                )
                is not None
            ]
            if not live:
                self.restore(journal)
                return Attempt("empty")

        # 2. Root files, core closure, core build, audit of the core and of the slices.
        for name in names:
            self.run("git", "add", targets[name])
        listed = self.read(PROMOTED) or ""
        have = {line.split("#")[0].strip() for line in listed.splitlines()}
        promote = [
            m
            for m in dict.fromkeys(m for g in live for m in g.promote)
            if m not in have
        ]
        if promote:
            self.keep(journal, PROMOTED)
            sep = "" if not listed or listed.endswith("\n") else "\n"
            (self.root / PROMOTED).write_text(
                listed + sep + "".join(f"{m}\n" for m in promote), encoding="utf-8"
            )
        checks: tuple[tuple[str, tuple[str, ...], str], ...] = (
            ("root files", ("scripts/gen_root.sh",), "gen_root failed"),
            (
                "core check",
                ("uv", "run", "-q", "scripts/core.py", "check"),
                "core module imports a catalogue module",
            ),
            ("core build", CORE_BUILD, "core build failed"),
            ("audit", ("scripts/audit.sh", "LeanDLRA", *modules), "audit failed"),
        )
        for stage, cmd, why in checks:
            code, out = self.run(*cmd)
            if code != 0:
                return self.fail(journal, live, stage, f"{why}\n{out[-3000:]}\n")

        # 3. Rename map, recorded statements, changed declarations (core modules and slices).
        if any(g.renames for g in live):
            try:
                merged = json.loads(self.read(RENAMES) or "{}")
                for group in live:
                    merged = merge_renames(merged, group.renames)
            except ValueError as err:
                return self.fail(journal, live, "renames", f"renames: {err}\n")
            self.keep(journal, RENAMES)
            (self.root / RENAMES).write_text(
                json.dumps(merged, indent=2, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
        code, out = self.run(*TOOL, "dump", *modules)
        if code != 0:
            return self.stop(f"rolling dump failed {out[-800:]}")
        code, out = self.run(*TOOL, "fidelity")
        if code == 1:
            return self.fail(
                journal, live, "fidelity", f"fidelity check failed\n{out[-3000:]}\n"
            )
        if code != 0:
            return self.stop(f"fidelity could not run {out[-800:]}")
        code, out = self.run(*TOOL, "diff", f"--report={HASHDIR}/round_report.md")
        stats = parse_stats(out)
        if code != 0 or stats is None:
            return self.stop(f"hashdiff could not run {out[-800:]}")
        expected = [g.expect_changed for g in live if g.expect_changed is not None]
        if expected and stats.changed + stats.removed > sum(expected):
            self.log(hashdiff_line("rejected", stats))
            report = self.keep_report(f"{stats.base}..rejected_{key(names[0])}")
            reason = (
                f"hashdiff: {stats.changed} changed and {stats.removed} removed declarations, "
                f"at most {sum(expected)} expected (report: {report})\n"
            )
            return self.fail(journal, live, "hashdiff", reason)

        # 4. Commit exactly the files of the round, and push.
        title = commit_title(
            [key(f) for f in names], all(self.tracked(targets[f]) for f in names)
        )
        ops = sorted({op for f in names for op in table[key(f)]["ops"]})
        paths = [
            *dict.fromkeys(targets[f] for f in names),
            *[rel for rel in ROOTS if (self.root / rel).exists()],
            *[rel for rel in (PROMOTED, RENAMES) if rel in journal["saved"]],
        ]
        core = set(
            re.findall(r"^import\s+(\S+)", self.read(ROOTS[0]) or "", re.MULTILINE)
        )
        journal.update(
            stage="committing",
            title=title,
            groups=[dataclasses.asdict(g) for g in live],
            hashdiff=dataclasses.asdict(stats),
            core=[len(core), sum(m not in core for m in modules)],
        )
        self.save(journal)
        self.run("git", "add", *paths)
        code, out = self.run(
            "git", "commit", "-q", "-m", commit_message(title, ops), "--", *paths
        )
        if code != 0:
            if self.run("git", "diff", "--cached", "--quiet", "HEAD", "--", *paths)[0]:
                return self.stop(f"commit failed {out[-800:]}")
            reason = "nothing to commit: every slice is identical to main\n"
            return self.fail(journal, live, "commit", reason)
        return Attempt("pushed" if self.publish(journal) else "stop")

    def publish(self, journal: dict[str, Any]) -> bool:
        """Push a committed round and close it; False if the gate must stop.  Safe to repeat."""
        code, out = self.run(*PUSH)
        if code != 0:
            self.log(f"STOP: push failed {out[-800:]}")
            return False
        code, out = self.run(*TOOL, "accept")
        if code != 0:
            self.log(f"STOP: rolling dump not updated {out[-800:]}")
            return False
        sha = self.round_commit(journal)
        stats = Stats(**journal["hashdiff"])
        self.keep_report(f"{stats.base}..{sha}")
        self.log(hashdiff_line(sha, stats))
        self.log(core_line(sha, *journal["core"]))
        self.done.mkdir(exist_ok=True)
        for group in journal["groups"]:
            for name in group["files"]:
                if (self.ready / name).exists():
                    shutil.move(str(self.ready / name), str(self.done / name))
            self.move_marker(group["marker"], self.done)
        self.log(f"PUSHED {journal['title']}")
        self.journal.unlink()
        return True

    def process(self, groups: Sequence[Group]) -> bool:
        """One round, with the group-by-group fallback; False if the gate must stop."""
        result = self.attempt(groups)
        if result.status == "failed" and len(result.groups) > 1:
            self.log(
                f"FALLBACK {result.stage}: {len(result.groups)} groups one by one "
                f"({', '.join(g.id for g in result.groups)})"
            )
            for group in result.groups:
                single = self.attempt([group])
                if single.status == "stop":
                    return False
                if single.status == "failed":
                    self.reject_group(single.groups[0], single.reason)
            return True
        if result.status == "failed":
            self.reject_group(result.groups[0], result.reason)
        return result.status != "stop"

    # -- the loop --------------------------------------------------------------------------

    def select(self, batch: int, legacy_max: int, grace: float) -> Selection:
        """The next round, from the present content of `wip/ready`."""
        files, markers = self.scan()
        targets = {k: entry["target"] for k, entry in self.table().items()}
        return select_round(
            files, markers, targets, batch, legacy_max, time.time(), grace
        )

    def plan(self, batch: int, legacy_max: int, grace: float) -> None:
        """Dry run: print what the next round would do; nothing is written or built."""
        if self.journal.exists():
            print(f"an interrupted round would be recovered first: {self.journal}")
        problem = self.preflight()
        if problem:
            print(f"the gate would STOP: {problem}")
        selection = self.select(batch, legacy_max, grace)
        for bad in selection.bad:
            print(
                f"BADGROUP {bad.name}: {bad.reason}; rejects {list(bad.files) or 'no file'}"
            )
        table = self.table()
        renames: dict[str, str] = json.loads(self.read(RENAMES) or "{}")
        names: list[str] = []
        earlier: set[str] = set()
        for group in selection.groups:
            problems, merged = self.screen(group, table, renames, earlier)
            bad_files = dict(p for p in problems if p[0])
            print(
                f"group {group.id}: {len(group.files)} file(s), {len(group.renames)} rename(s), "
                f"expect_changed={group.expect_changed}, promote={list(group.promote)}"
            )
            for name, reason in problems:
                print(f"  would REJECT {key(name) or 'the group'}: {reason.strip()}")
            if problems and group.atomic:
                continue
            renames = merged
            for name in (f for f in group.files if f not in bad_files):
                target = table[key(name)]["target"]
                verb = "update" if self.tracked(target) else "add"
                print(f"  {key(name)} -> {target} ({verb})")
                names.append(name)
                earlier.add(module_name(target))
        if not names:
            print("nothing to do")
            return
        updated = all(self.tracked(table[key(f)]["target"]) for f in names)
        print(f"commit: {commit_title([key(f) for f in names], updated)}")
        queued, _ = self.scan()
        print(f"left in the queue: {len(queued) - len(names)} slice file(s)")

    def loop(self, batch: int, once: bool, legacy_max: int, grace: float) -> int:
        """Process `wip/ready/` forever (or one round with ``once``); the exit status."""
        self.ready.mkdir(parents=True, exist_ok=True)
        self.log("gate started")
        problem = None if self.recover() else "recovery failed"
        problem = problem or self.preflight()
        while problem is None:
            selection = self.select(batch, legacy_max, grace)
            for bad in selection.bad:
                self.reject_marker(bad)
            if selection.groups:
                self.log(
                    f"ROUND {len(selection.groups)} group(s): "
                    + "; ".join(
                        f"{g.id} ({', '.join(key(f) for f in g.files)})"
                        for g in selection.groups
                    )
                )
                if not self.process(selection.groups):
                    problem = "round stopped"
                else:
                    problem = self.preflight()
            elif once:
                return 0
            elif not selection.bad:
                time.sleep(15)
        if problem != "round stopped":
            self.log(f"STOP: {problem}")
            print(f"gate: {problem}", file=sys.stderr)
        self.log("gate stopped, see above")
        return 1


def main(
    batch: int = 12,
    once: bool = False,
    dry_run: bool = False,
    legacy_max: int = 6,
    grace: int = 120,
    root: str = "",
) -> None:
    """Process `wip/ready/` forever (or one round with `--once`).

    ``--batch`` is the largest number of files of a round (a single group may be larger),
    ``--legacy-max`` the largest number of slices without a marker taken per round, ``--grace`` the
    age in seconds from which such a slice is taken.  ``--dry-run`` prints the next round and
    changes nothing.  ``--root`` is the repository (default: the parent of this script's folder).
    """
    base = Path(root).resolve() if root else ROOT
    gate = Gate(base, shell(base), dry=dry_run)
    if dry_run:
        gate.plan(batch, legacy_max, grace)
        return
    sys.exit(gate.loop(batch, once, legacy_max, grace))


def cli() -> None:
    """Command line."""
    import fire  # imported here so that the tests need only pytest

    fire.Fire(main)


if __name__ == "__main__":
    cli()
