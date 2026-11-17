# /// script
# requires-python = ">=3.11"
# dependencies = ["fire"]
# ///
# Scope: both
"""Public names of slices that the library declares already: the name check of ``enqueue.sh``.

A round of ``scripts/gate.py`` builds the core and the slices of the round, and ``scripts/fc``
checks a slice alone, so neither sees a slice that declares a name which a module outside its
imports declares too: the catalogue build (``LeanDLRACatalogue`` imports every module) fails
later. ``scripts/enqueue.sh`` runs this check before it queues a group.

Every public declaration of a slice (theorem, lemma, def, abbrev, structure, class, inductive
type, named instance, opaque constant; read from the source with its namespaces by
``core_checks.declarations_in``; private ones and unnamed instances are left out) is looked up in

* the declaration index of the rolling dump ``.lake/hashdiff/rolling.jsonl.gz``
  (``scripts/rolling.py``): every declaration of every module of the last gate round, also the
  generated ones; modules whose source file no longer exists are skipped, and so are the target
  modules of the slices of the call, which the slices replace (an update keeps its own names);
* the other slices of the call (two files of one group that declare the same name);
* the slices that earlier groups queued in ``wip/ready/`` and the gate has not taken yet, except
  those for a target of this call.

Usage::

    uv run -q scripts/name_clash.py check wip/A.lean wip/B.lean [--allow=NAME,NAME] [--root=.]

``--allow`` names declarations (full names, as printed) whose clash is intended. Exit 0: no
clash; without a rolling dump the check is skipped with a warning. Exit 1: a clash (printed).
Exit 2: a slice or the manifest cannot be read, or an allowed name is not a name.
"""

from __future__ import annotations

import json
import re
import sys
from collections.abc import Collection, Sequence
from dataclasses import dataclass
from pathlib import Path

import core
import core_checks
import rolling

ROOT = Path(__file__).resolve().parent.parent
DUMP = f"{rolling.HASHDIR}/{rolling.ROLLING}"
MANIFEST = "wip/manifest.json"
READY = "wip/ready"
IDENT = re.compile(r"[^\s()\[\]{}⦃⦄,\"\\]+")  # a constant name, as in scripts/gate.py


@dataclass(frozen=True)
class Slice:
    """A slice file: how it is shown, the module it replaces, its public names with lines."""

    label: str
    module: str
    names: tuple[tuple[int, str], ...]


@dataclass(frozen=True)
class Clash:
    """A name of a slice that is declared elsewhere already."""

    slice: Slice
    line: int
    name: str
    where: str


def public_names(text: str) -> tuple[tuple[int, str], ...]:
    """``(line, full name)`` of the declarations of a source text that make a public name."""
    return tuple(
        (d.line, d.name)
        for d in core_checks.declarations_in(text)
        if "private" not in d.modifiers and d.named
    )


def module_of_target(target: str) -> str:
    """``LeanDLRA/A/B.lean`` → ``LeanDLRA.A.B``."""
    return target.removesuffix(".lean").replace("/", ".")


def read_slice(path: Path, label: str, table: dict[str, dict[str, object]]) -> Slice:
    """A slice file with the module of its manifest target; KeyError without an entry."""
    target = table[path.stem]["target"]
    if not isinstance(target, str):
        raise KeyError(path.stem)
    text = path.read_text(encoding="utf-8")
    return Slice(label, module_of_target(target), public_names(text))


def dump_index(root: Path, skip: frozenset[str]) -> dict[str, str]:
    """Declaration name → module, from the rolling dump; private names, the modules in ``skip``
    and modules without a source file are left out."""
    index: dict[str, str] = {}
    exists: dict[str, bool] = {}
    for line in rolling.lines_of(root / DUMP):
        module = rolling.module_of(line)
        if module in skip:
            continue
        if module not in exists:
            exists[module] = core.source_of(module, root).exists()
        if not exists[module]:
            continue
        found = rolling.NAME_OF.search(line)
        if found is None:
            continue
        name: str = json.loads(f'"{found.group(1)}"')
        if not name.startswith("_priv."):
            index.setdefault(name, module)
    return index


def stale_note(root: Path) -> str:
    """A warning if the rolling dump describes an older library commit ("" if it is current)."""
    header = rolling.read_header(root / DUMP)
    library = rolling.git(root, "rev-list", "-1", "HEAD", "--", *rolling.LIBRARY)
    described = str(header.get("library_commit", ""))
    if library and described != library:
        return (
            f"the rolling dump describes {described[:7]}, the library is at {library[:7]}: "
            "names added since then are not seen"
        )
    return ""


def find_clashes(
    slices: Sequence[Slice],
    index: dict[str, str],
    core_modules: frozenset[str],
    queued: Sequence[Slice],
    allowed: frozenset[str],
) -> list[Clash]:
    """The clashes of the names of ``slices`` with the index, with each other and with the
    queued slices of earlier groups."""
    clashes: list[Clash] = []
    for i, piece in enumerate(slices):
        others = [s for j, s in enumerate(slices) if j != i]
        for line, name in piece.names:
            if name in allowed:
                continue
            where = ""
            if name in index:
                module = index[name]
                part = "core" if module in core_modules else "catalogue"
                where = f"{module} ({part}) declares it already"
            elif twin := next((s for s in others if name in names_of(s)), None):
                where = f"{twin.label} of the same call declares it too"
            elif twin := next((s for s in queued if name in names_of(s)), None):
                where = f"{twin.label}, queued by an earlier group, declares it too"
            if where:
                clashes.append(Clash(piece, line, name, where))
    return clashes


def names_of(piece: Slice) -> set[str]:
    """The names of a slice as a set."""
    return {name for _, name in piece.names}


def queued_slices(
    root: Path,
    mine: Collection[str],
    targets: frozenset[str],
    table: dict[str, dict[str, object]],
) -> list[Slice]:
    """The slice files in ``wip/ready`` of other groups whose target is not one of ``targets``."""
    out: list[Slice] = []
    for path in sorted((root / READY).glob("*.lean")):
        if path.name in mine or path.stem not in table:
            continue
        try:
            piece = read_slice(path, f"{READY}/{path.name}", table)
        except (KeyError, OSError, UnicodeDecodeError):
            continue
        if piece.module not in targets:
            out.append(piece)
    return out


def allowed_names(allow: object) -> frozenset[str]:
    """The names of ``--allow`` (comma-separated)."""
    return frozenset(core_checks.split_list(allow))


def run_check(root: Path, files: Sequence[str], allowed: frozenset[str]) -> int:
    """Print the clashes of the slice files; the exit status."""
    if bad := sorted(n for n in allowed if not IDENT.fullmatch(n)):
        print(
            f"enqueue: --allow-name: not a declaration name: {bad[0]}", file=sys.stderr
        )
        return 2
    try:
        table: dict[str, dict[str, object]] = json.loads(
            (root / MANIFEST).read_text(encoding="utf-8")
        )
    except (OSError, ValueError) as err:
        print(f"enqueue: name check: cannot read {MANIFEST}: {err}", file=sys.stderr)
        return 2
    slices: list[Slice] = []
    for name in files:
        path = Path(name) if Path(name).is_absolute() else root / name
        try:
            slices.append(read_slice(path, name, table))
        except (KeyError, OSError, UnicodeDecodeError) as err:
            print(f"enqueue: name check: cannot read {name}: {err}", file=sys.stderr)
            return 2
    if not (root / DUMP).exists():
        print(
            f"enqueue: warning: no {DUMP}, public names not checked against the library",
            file=sys.stderr,
        )
        index: dict[str, str] = {}
    else:
        if note := stale_note(root):
            print(f"enqueue: warning: {note}", file=sys.stderr)
        index = dump_index(root, frozenset(s.module for s in slices))
    targets = frozenset(s.module for s in slices)
    queued = queued_slices(root, {Path(f).name for f in files}, targets, table)
    listed = root / core.CORE_ROOT
    core_set = frozenset(core.core_modules(root) if listed.exists() else [])
    clashes = find_clashes(slices, index, core_set, queued, allowed)
    for c in clashes:
        print(
            f"enqueue: name clash: {c.slice.label}:{c.line} declares {c.name}; {c.where}",
            file=sys.stderr,
        )
    if clashes:
        print(
            "enqueue: nothing queued. Rename the declaration, or remove it from the other module "
            "by an update of that module in the same group; if the clash is intended, pass "
            "--allow-name NAME for each name",
            file=sys.stderr,
        )
        return 1
    return 0


def check(*files: str, allow: object = "", root: str = "") -> None:
    """Check the public names of the slice files against the library and the queue."""
    base = Path(root).resolve() if root else ROOT
    sys.exit(run_check(base, files, allowed_names(allow)))


def cli() -> None:
    """Command line."""
    import fire  # imported here so that the tests need only pytest

    fire.Fire({"check": check})


if __name__ == "__main__":
    cli()
