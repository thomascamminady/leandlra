# /// script
# requires-python = ">=3.11"
# dependencies = ["fire"]
# ///
"""Rolling dump: fidelity and hashdiff for one gate round, on the core and the slices only.

A round of ``scripts/gate.py`` builds the core library and its own slices, nothing else: a
catalogue module that no round touches may be stale or broken.  So the checks of a round read
exactly the modules ``M`` = modules listed in ``LeanDLRA.lean`` ∪ slice modules of the round, and
take everything else from the *rolling dump*, the last known entries of every module:

* ``.lake/hashdiff/rolling.jsonl.gz``: a dump as written by ``scripts/hashdiff.py dump``
  (every declaration, canonical type and body), with ``library_commit`` in its header: the last
  commit to the library that it describes;
* ``.lake/hashdiff/rolling_statements.jsonl.gz``: module, name and printed type of every theorem,
  in the form whose hash ``docs/statements.json`` records (``scripts/fidelity.py``).

Commands (the gate runs ``dump``, ``fidelity``, ``diff`` before the commit, ``accept`` after)::

    uv run scripts/rolling.py seed                  # once, after a full build: dump every module
    uv run scripts/rolling.py dump MODULE ...       # dump M (core + the given slice modules)
    uv run scripts/rolling.py fidelity              # recorded statements; exit 1 if one is lost
    uv run scripts/rolling.py diff --report=R.md    # old entries of M against the new ones
    uv run scripts/rolling.py accept                # the rolling dump takes the new entries of M
    uv run scripts/rolling.py discard               # forget the entries of a rejected round
    uv run scripts/rolling.py status

``fidelity`` looks every recorded statement up in the new entries of ``M`` and, for modules
outside ``M``, in the rolling dump: a statement that disappears from a module of ``M`` is missing,
a statement of an untouched catalogue module never is.  ``diff`` compares the rolling entries of
the modules of ``M`` with their new entries, under ``docs/renames.json``, with
``hashdiff.compare``; its last line ``HASHDIFF {json}`` carries the counts.  Exit status 2 means
that a check could not run (no build, no dump), never that a statement changed.
"""

from __future__ import annotations

import datetime
import itertools
import json
import os
import re
import subprocess
import sys
from collections.abc import Iterable, Iterator, Sequence
from pathlib import Path
from typing import Any

import fidelity
import hashdiff

ROOT = Path(__file__).resolve().parent.parent
HASHDIR = ".lake/hashdiff"
ROLLING, STATEMENTS = "rolling.jsonl.gz", "rolling_statements.jsonl.gz"
ROUND, ROUND_STATEMENTS = "round.jsonl.gz", "round_statements.jsonl.gz"
ROUND_BEFORE = "round_before.jsonl.gz"
LIBRARY = ("LeanDLRA", "LeanDLRA.lean", "LeanDLRACatalogue.lean")
# Quotes inside JSON strings are escaped, so these match keys only, wherever they stand in a line.
MODULE_OF = re.compile(r'"module":"([^"\\]*)"')
NAME_OF = re.compile(r'"name":"((?:[^"\\]|\\.)*)"')


class ToolError(Exception):
    """A check could not run."""


def at(root: Path, name: str) -> Path:
    """A file of the dump directory."""
    return root / HASHDIR / name


def git(root: Path, *args: str) -> str:
    """Output of a git command in the repository, or the empty string on failure."""
    r = subprocess.run(
        ["git", *args], check=False, cwd=root, capture_output=True, text=True
    )
    return r.stdout.strip() if r.returncode == 0 else ""


def imports(path: Path) -> list[str]:
    """The modules imported by a root file (none if it does not exist)."""
    if not path.exists():
        return []
    return re.findall(
        r"^import\s+(\S+)", path.read_text(encoding="utf-8"), re.MULTILINE
    )


def library_modules(root: Path, lib: str) -> list[str]:
    """The modules of the core (``LeanDLRA``) or of everything (``LeanDLRACatalogue``)."""
    core = imports(root / "LeanDLRA.lean")
    if lib == "LeanDLRA":
        return core
    rest = [m for m in imports(root / f"{lib}.lean") if m != "LeanDLRA"]
    return list(dict.fromkeys([*core, *rest]))


def module_of(line: str) -> str:
    """The module of a dumped line."""
    m = MODULE_OF.search(line)
    return m.group(1) if m else json.loads(line)["module"]


def read_header(path: Path) -> dict[str, Any]:
    """The header of a dump."""
    with hashdiff.open_text(path, "r") as f:
        return json.loads(f.readline())


def lines_of(path: Path) -> Iterator[str]:
    """The lines of a dump after its header."""
    with hashdiff.open_text(path, "r") as f:
        next(f, None)
        for line in f:
            if line.strip():
                yield line


def write_lines(path: Path, header: dict[str, Any], lines: Iterable[str]) -> int:
    """Write a dump atomically (the lines may be read from the file it replaces)."""
    path.parent.mkdir(parents=True, exist_ok=True)
    partial = path.with_name("partial-" + path.name)
    count = 0
    with hashdiff.open_text(partial, "w") as f:
        f.write(json.dumps(header) + "\n")
        for line in lines:
            f.write(line)
            count += 1
    os.replace(partial, path)
    return count


def make_header(root: Path, modules: Sequence[str], listed: bool) -> dict[str, Any]:
    """The header of a dump made now; with the module list for the dump of a round."""
    header: dict[str, Any] = {
        "format": hashdiff.FORMAT,
        "created": datetime.datetime.now().isoformat(timespec="seconds"),
        "commit": git(root, "rev-parse", "--short", "HEAD"),
        "dirty": bool(
            git(root, "--no-optional-locks", "status", "--porcelain", "--", *LIBRARY)
        ),
        "modules": len(modules),
        "library_commit": git(root, "rev-list", "-1", "HEAD", "--", *LIBRARY),
    }
    if listed:
        header["module_list"] = list(modules)
    return header


def build_current(root: Path, targets: Sequence[str]) -> None:
    """Fail unless the build of the targets is current (the dumper reads their `.olean` files)."""
    r = subprocess.run(
        ["nice", "-n", "10", "lake", "build", "--no-build", *targets],
        check=False,
        cwd=root,
        capture_output=True,
        text=True,
    )
    if r.returncode != 0:
        raise ToolError(
            f"the build of {' '.join(targets[:3])} … is not current\n{(r.stdout + r.stderr)[-2000:]}"
        )


def run_dumper(root: Path, modules: Sequence[str], canonical: bool) -> Iterator[str]:
    """The lines printed by `scripts/DumpTypes.lean` for exactly these modules."""
    cmd = ["nice", "-n", "10", "lake", "env", "lean", "--run", hashdiff.DUMPER]
    cmd += ["--canonical"] if canonical else []
    with subprocess.Popen(
        [*cmd, "--modules", *modules], cwd=root, stdout=subprocess.PIPE, text=True
    ) as proc:
        assert proc.stdout is not None
        for line in proc.stdout:
            if line.startswith("{"):
                yield line
    if proc.returncode != 0:
        raise ToolError(f"{hashdiff.DUMPER} failed with exit status {proc.returncode}")


def dump_pair(
    root: Path,
    modules: Sequence[str],
    canonical_out: Path,
    statements_out: Path,
    header: dict[str, Any],
) -> tuple[int, int]:
    """Dump the modules in both forms; the numbers of declarations and of theorems written.

    The plain form of the dumper has no module field: a theorem gets the module that the
    canonical dump of the same run gives for its name (private theorems, whose names differ in
    the two forms, are left out: no recorded statement is private).
    """
    where: dict[str, str] = {}

    def canonical() -> Iterator[str]:
        for line in run_dumper(root, modules, True):
            if '"kind":"theorem"' in line:
                m = NAME_OF.search(line)
                if m:
                    where[json.loads(f'"{m.group(1)}"')] = module_of(line)
            yield line

    def plain() -> Iterator[str]:
        for line in run_dumper(root, modules, False):
            rec: dict[str, str] = json.loads(line)
            module = where.get(rec["name"])
            if module is not None:
                entry = {"module": module, "name": rec["name"], "type": rec["type"]}
                yield (
                    json.dumps(entry, ensure_ascii=False, separators=(",", ":")) + "\n"
                )

    count = write_lines(canonical_out, header, canonical())
    return count, write_lines(statements_out, header, plain())


def round_modules(root: Path) -> set[str]:
    """The modules of the dump of the running round (empty if there is none)."""
    fresh = at(root, ROUND)
    return set(read_header(fresh)["module_list"]) if fresh.exists() else set()


def proved_types(root: Path, names: set[str]) -> dict[str, str]:
    """Name → printed type for the given theorems: the round's entries, else the rolling ones."""
    modules = round_modules(root)
    table: dict[str, str] = {}
    sources = [(at(root, STATEMENTS), False)]
    if modules:
        sources.append((at(root, ROUND_STATEMENTS), True))
    for path, fresh in sources:
        for line in lines_of(path):
            m = NAME_OF.search(line)
            if m is None or json.loads(f'"{m.group(1)}"') not in names:
                continue
            if fresh or module_of(line) not in modules:
                rec: dict[str, str] = json.loads(line)
                table[rec["name"]] = rec["type"]
    return table


def check_statements(root: Path, renames: Path, cap: int) -> tuple[str, list[str]]:
    """The fidelity check on the rolling dump: its summary line and the failures."""
    recorded: dict[str, str] = json.loads(
        (root / "docs" / "statements.json").read_text(encoding="utf-8")
    )
    rmap = fidelity.load_renames(renames)
    names = set(recorded) | {rmap[n] for n in recorded if n in rmap}
    exact, via, problems = fidelity.check(
        recorded, proved_types(root, names), rmap, cap
    )
    summary = (
        f"{exact + via} of {len(recorded)} recorded statements proved verbatim ({exact} exactly, "
        f"{via} via the rename map with {len(rmap)} entries; {len(round_modules(root))} modules "
        "read in this round, the others from the rolling dump)"
    )
    return summary, problems


def compare_round(
    root: Path, renames: Path, limit: int
) -> tuple[hashdiff.Result, str, str]:
    """Rolling entries of the round's modules against their new entries: result, report, base."""
    modules = round_modules(root)
    if not modules:
        raise ToolError(f"no dump of a round: {HASHDIR}/{ROUND}")
    before, after = at(root, ROUND_BEFORE), at(root, ROUND)
    old_header = read_header(at(root, ROLLING))
    kept = (line for line in lines_of(at(root, ROLLING)) if module_of(line) in modules)
    write_lines(before, old_header, kept)
    rmap = hashdiff.normalize_renames(hashdiff.load_renames(renames))
    header_b, records_b = hashdiff.read_dump(before)
    header_a, records_a = hashdiff.read_dump(after)
    res = hashdiff.compare(records_b, records_a, rmap)
    text = hashdiff.render(
        res, before, after, (header_b, header_a), renames, rmap, False, limit
    )
    return res, text, str(old_header.get("library_commit", ""))[:7]


def accept_round(root: Path) -> bool:
    """Replace the rolling entries of the round's modules by the new ones; False if no round."""
    modules = round_modules(root)
    if not modules:
        return False
    now = make_header(root, [], False)
    del now["modules"]
    for rolling, fresh in ((ROLLING, ROUND), (STATEMENTS, ROUND_STATEMENTS)):
        if not at(root, fresh).exists():
            continue
        header = {**read_header(at(root, rolling)), **now}
        kept = (
            line
            for line in lines_of(at(root, rolling))
            if module_of(line) not in modules
        )
        write_lines(
            at(root, rolling), header, itertools.chain(kept, lines_of(at(root, fresh)))
        )
    # The canonical dump of the round goes last: while it exists, `accept` can be repeated.
    for name in (ROUND_STATEMENTS, ROUND_BEFORE, ROUND):
        at(root, name).unlink(missing_ok=True)
    return True


# ---------------------------------------------------------------------------------------------
# Commands


def path_in(root: Path, name: str) -> Path:
    """A path given on the command line, relative to the repository."""
    return Path(name) if Path(name).is_absolute() else root / name


def seed(lib: str = "LeanDLRACatalogue", check: bool = True) -> None:
    """Make the rolling dump from a current build of the whole library."""
    modules = library_modules(ROOT, lib)
    if check:
        build_current(ROOT, [lib])
    header = make_header(ROOT, modules, False)
    count, stated = dump_pair(
        ROOT, modules, at(ROOT, ROLLING), at(ROOT, STATEMENTS), header
    )
    print(
        f"seeded {HASHDIR}/{ROLLING}: {count} declarations, {stated} theorems, "
        f"{len(modules)} modules of {lib}, library commit {header['library_commit'][:7]}"
    )
    summary, problems = check_statements(ROOT, path_in(ROOT, fidelity.RENAMES), 1 << 16)
    print("\n".join([summary, *problems]))


def dump(*slices: str, check: bool = True) -> None:
    """Dump the core modules and the given slice modules as the entries of the running round."""
    modules = list(dict.fromkeys([*library_modules(ROOT, "LeanDLRA"), *slices]))
    if check:
        build_current(ROOT, ["LeanDLRA", *slices])
    header = make_header(ROOT, modules, True)
    count, stated = dump_pair(
        ROOT, modules, at(ROOT, ROUND), at(ROOT, ROUND_STATEMENTS), header
    )
    print(f"dumped {count} declarations, {stated} theorems from {len(modules)} modules")


def fidelity_check(renames: str = fidelity.RENAMES, cap: int = 1 << 16) -> None:
    """Check the recorded statements; exit 1 if one is missing or differs."""
    summary, problems = check_statements(ROOT, path_in(ROOT, renames), cap)
    print(summary)
    if problems:
        print("\n".join(problems))
        sys.exit(1)


def diff(report: str = "", renames: str = hashdiff.RENAMES, limit: int = 40) -> None:
    """Compare the round's modules with their rolling entries; the last line has the counts."""
    res, text, base = compare_round(ROOT, path_in(ROOT, renames), limit)
    if report:
        path_in(ROOT, report).write_text(text, encoding="utf-8")
    print(text.split("\n## ")[0])
    counts = {
        "base": base,
        "declarations": res.after_count,
        "changed": len(res.type_changed) + len(res.value_changed),
        "moved": len(res.moved),
        "added": len(res.appeared) + len(res.aliases),
        "removed": len(res.disappeared),
    }
    print("HASHDIFF " + json.dumps(counts))


def accept() -> None:
    """Take the entries of the running round into the rolling dump (after its commit)."""
    print("rolling dump updated" if accept_round(ROOT) else "nothing to accept")


def discard() -> None:
    """Forget the entries of a round that was not committed."""
    for name in (ROUND_STATEMENTS, ROUND_BEFORE, ROUND):
        at(ROOT, name).unlink(missing_ok=True)


def status() -> None:
    """Describe the rolling dump."""
    for name in (ROLLING, STATEMENTS, ROUND, ROUND_STATEMENTS):
        path = at(ROOT, name)
        if not path.exists():
            print(f"{name}: missing")
            continue
        header = read_header(path)
        shown = {k: v for k, v in header.items() if k != "module_list"}
        print(f"{name}: {shown}")


def cli() -> None:
    """Command line; exit status 2 if a check could not run."""
    import fire  # imported here so that the tests need only pytest

    try:
        fire.Fire(
            {
                "seed": seed,
                "dump": dump,
                "fidelity": fidelity_check,
                "diff": diff,
                "accept": accept,
                "discard": discard,
                "status": status,
            }
        )
    except SystemExit as err:
        if isinstance(err.code, int) or err.code is None:
            raise
        print(f"rolling: {err.code}", file=sys.stderr)
        sys.exit(2)
    except (ToolError, OSError, ValueError, KeyError, StopIteration) as err:
        print(f"rolling: {type(err).__name__}: {err}", file=sys.stderr)
        sys.exit(2)


if __name__ == "__main__":
    cli()
