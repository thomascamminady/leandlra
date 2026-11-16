# /// script
# requires-python = ">=3.11"
# dependencies = ["fire"]
# ///
"""Checks of the core library that need no Lean: where definitions stand, and duplicate statements.

"Core" is the notion of ``scripts/core.py``: the modules imported by ``LeanDLRA.lean``. Both checks
compare with a baseline (``docs/core_checks_baseline.json``, written by ``baseline``), so that they
can block a round on *new* findings while the old ones are being worked off; ``--strict`` ignores
the baseline.

``defs``: the ``Defs.lean`` rule of ``docs/CONVENTIONS.md`` §3, read from the sources: a public
``def``, ``abbrev``, ``structure``, ``class``, ``inductive``, ``opaque`` or non-scoped ``instance``
in a core file that is not a ``Defs.lean``. Exempt: ``private``, ``scoped`` and ``local``
declarations, declarations in or below a namespace whose name ends in ``Example`` or ``Examples`` and the ``Corrections`` and
``Counterexamples`` folders. A source scan, not the elaborated environment: it sees what the
author wrote (no projections, no ``match_1``), it does not see a definition that a macro makes.

``duplicates``: two public theorems of the core whose elaborated statements have the same hash, from
the rolling record ``.lake/hashdiff/rolling_statements.jsonl.gz`` (``scripts/rolling.py``; the type
is printed with binder names erased, so it is the statement and nothing else).

    uv run -q scripts/core_checks.py defs [--strict] [--list]
    uv run -q scripts/core_checks.py duplicates [--strict] [--list]
    uv run -q scripts/core_checks.py baseline          # write both baselines from today's findings

Exit 0: no finding beyond the baseline. Exit 1: a new finding (printed). Exit 2: nothing to read
(no record, no core root file).
"""

from __future__ import annotations

import gzip
import hashlib
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

import core

ROOT = Path(__file__).resolve().parent.parent
BASELINE = "docs/core_checks_baseline.json"
RECORD = ".lake/hashdiff/rolling_statements.jsonl.gz"
EXEMPT_AREAS = frozenset(("Corrections", "Counterexamples"))

_BLOCK_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)
_LINE_COMMENT = re.compile(r"--[^\n]*")
_NAMESPACE = re.compile(r"^\s*namespace\s+(\S+)")
_SECTION = re.compile(r"^\s*section\b")
_END = re.compile(r"^\s*end\b(?:\s+\S+)?\s*$")
_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"((?:(?:public|noncomputable|protected|unsafe|partial|nonrec|scoped|local|private)\s+)*)"
    r"(def|abbrev|structure|class|inductive|instance|opaque)\b\s*(\S*)"
)


def strip_comments(text: str) -> str:
    """The text without comments; line breaks inside a block comment stay (line numbers)."""
    keep = lambda m: "\n" * m.group(0).count("\n")
    return _LINE_COMMENT.sub("", _BLOCK_COMMENT.sub(keep, text))


def definitions_in(text: str) -> list[tuple[int, str, str]]:
    """``(line, kind, qualified name)`` of the public definitions of a source text that the
    ``Defs.lean`` rule covers (unnamed instances get the name ``instance``)."""
    stack: list[list[str]] = []
    out: list[tuple[int, str, str]] = []
    for number, line in enumerate(strip_comments(text).splitlines(), start=1):
        if m := _NAMESPACE.match(line):
            stack.append(m.group(1).split("."))
        elif _SECTION.match(line):
            stack.append([])
        elif _END.match(line):
            if stack:
                stack.pop()
        elif m := _DECL.match(line):
            modifiers = m.group(1).split()
            if {"private", "scoped", "local"} & set(modifiers):
                continue
            kind, name = m.group(2), m.group(3)
            if kind == "instance" and (
                not name or name.startswith((":", "(", "{", "["))
            ):
                name = "instance"
            namespaces = [c for scope in stack for c in scope]
            parts = namespaces + name.split(".")
            if any(c.endswith(("Example", "Examples")) for c in parts[:-1]):
                continue
            out.append((number, kind, ".".join(parts)))
    return out


def defs_findings(root: Path = ROOT) -> list[tuple[str, int, str, str]]:
    """``(module, line, kind, name)`` of the violations of the ``Defs.lean`` rule in the core."""
    out: list[tuple[str, int, str, str]] = []
    for module in core.core_modules(root):
        parts = module.split(".")
        if parts[-1] == "Defs" or (len(parts) > 2 and parts[1] in EXEMPT_AREAS):
            continue
        path = core.source_of(module, root)
        if not path.exists():
            continue
        for line, kind, name in definitions_in(path.read_text(encoding="utf-8")):
            out.append((module, line, kind, name))
    return out


def duplicate_groups(root: Path = ROOT) -> list[list[tuple[str, str]]]:
    """Groups of ``(module, theorem)`` of the core with one statement hash, largest first."""
    path = root / RECORD
    modules = frozenset(core.core_modules(root))
    by_hash: dict[str, list[tuple[str, str]]] = defaultdict(list)
    with gzip.open(path, "rt", encoding="utf-8") as f:
        for number, line in enumerate(f):
            if number == 0:
                continue  # the header
            entry = json.loads(line)
            if entry["module"] in modules:
                digest = hashlib.sha256(entry["type"].encode()).hexdigest()
                by_hash[digest].append((entry["module"], entry["name"]))
    groups = [sorted(g) for g in by_hash.values() if len(g) > 1]
    return sorted(groups, key=lambda g: (-len(g), g))


def defs_keys(findings: list[tuple[str, int, str, str]]) -> list[str]:
    return sorted({f"{module}:{name}" for module, _, _, name in findings})


def duplicate_keys(groups: list[list[tuple[str, str]]]) -> list[str]:
    """A group is known by its sorted theorem names (stable when files move)."""
    return sorted("=".join(sorted(name for _, name in g)) for g in groups)


def read_baseline(root: Path) -> dict[str, list[str]]:
    path = root / BASELINE
    return json.loads(path.read_text()) if path.exists() else {}


def run_defs(root: Path, strict: bool, list_all: bool) -> int:
    findings = defs_findings(root)
    known = set() if strict else set(read_baseline(root).get("defs", []))
    new = [f for f in findings if f"{f[0]}:{f[3]}" not in known]
    shown = findings if list_all else new
    for module, line, kind, name in shown:
        print(f"DEFS-RULE {module}:{line}: public {kind} {name} outside a Defs.lean")
    print(
        f"defs: {len(findings)} violations in the core, {len(new)} not in the baseline"
    )
    return 1 if new else 0


def run_duplicates(root: Path, strict: bool, list_all: bool) -> int:
    if not (root / RECORD).exists():
        print(f"duplicates: no record {RECORD} (scripts/rolling.py seed)")
        return 2
    groups = duplicate_groups(root)
    known = set() if strict else set(read_baseline(root).get("duplicates", []))
    new = [
        g for g, k in zip(groups, duplicate_keys(groups), strict=True) if k not in known
    ]
    for g in groups if list_all else new:
        print(
            "DUPLICATE-STATEMENT "
            + "; ".join(f"{name} ({module})" for module, name in g)
        )
    print(
        f"duplicates: {len(groups)} groups in the core, {len(new)} not in the baseline"
    )
    return 1 if new else 0


def run_baseline(root: Path) -> int:
    data = {"defs": defs_keys(defs_findings(root))}
    if (root / RECORD).exists():
        data["duplicates"] = duplicate_keys(duplicate_groups(root))
    (root / BASELINE).write_text(json.dumps(data, indent=1, ensure_ascii=False) + "\n")
    print(
        f"{BASELINE}: {len(data['defs'])} definitions, {len(data.get('duplicates', []))} groups"
    )
    return 0


class Checks:
    """Checks of the core that need no Lean."""

    def defs(self, strict: bool = False, list: bool = False) -> None:
        """The Defs.lean rule on the core; list shows all findings, not only the new ones."""
        sys.exit(run_defs(ROOT, strict, list))

    def duplicates(self, strict: bool = False, list: bool = False) -> None:
        """Public core theorems with one statement hash."""
        sys.exit(run_duplicates(ROOT, strict, list))

    def baseline(self) -> None:
        """Write docs/core_checks_baseline.json from today's findings."""
        sys.exit(run_baseline(ROOT))


if __name__ == "__main__":
    import fire  # only the command line needs it: the tests import this module without it

    fire.Fire(Checks)
