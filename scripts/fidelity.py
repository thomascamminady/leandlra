# /// script
# requires-python = ">=3.11"
# dependencies = ["fire"]
# ///
# Scope: both
"""Check that no recorded statement changed without anybody noticing.

Two files map theorems to the SHA-256 of their elaborated type, taken before any of them was
proved: ``docs/statements.json`` for the theorems of the core library and
``docs/statements_catalogue.json`` for those of the catalogue (``docs/STRUCTURE.md``).  No name is
in both; ``scripts/rolling.py records`` checks that each theorem is in the file of the library
that declares it.  This script dumps the kernel types of the theorems of a library (by default
everything: every module imported by ``LeanDLRACatalogue.lean``, so statements may move between
files) and checks each recorded theorem in one of two ways:

* **exactly**: the theorem of the same name has a type with the recorded hash;
* **via the rename map** ``docs/renames.json`` (old constant name → new constant name, the audited
  map of decision Q6 in ``wip/UNIFY.md``): the theorem under its new name has the recorded type
  with the renamed constants substituted.

Only the hash of a recorded type is known, so the second check runs backwards: in the new type,
each constant that is a new name of the map is replaced by itself or by one of the old names mapped
to it, and one of these candidates must have the recorded hash.  The first candidates replace a
constant the same way at every occurrence (2^k candidates for k renamed constants without merges);
if none matches, every occurrence is varied separately, up to ``cap`` candidates.  A new type that
still mentions an old name of the map cannot be the renamed recorded type and fails.

It fails if a recorded theorem is missing or has a different type.  The library must be built
(``lake build LeanDLRACatalogue``); with ``--lib=LeanDLRA`` only the core is read and only the core
record is checked.  ``--scope=core|catalogue|all`` chooses the record explicitly.
"""

from __future__ import annotations

import hashlib
import itertools
import json
import re
import subprocess
import sys
from collections import defaultdict
from collections.abc import Iterator
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
# The two records of statements: the core library and the catalogue.
RECORDS = {
    "core": "docs/statements.json",
    "catalogue": "docs/statements_catalogue.json",
}
SCOPES = ("core", "catalogue", "all")
RENAMES = "docs/renames.json"
# The library of all modules (core and catalogue); the core library alone is ``LeanDLRA``.
EVERYTHING = "LeanDLRACatalogue"

# Constants in `Expr.dbgToString` output (as in scripts/hashdiff.py): maximal runs of characters
# other than the delimiters, optionally followed by universe levels `.{u_1}`.
DELIMS = r"\s()\[\]{}⦃⦄,"
IDENT = re.compile(r"[^" + DELIMS + r"]+")
TOKEN = re.compile(rf"(?<![^{DELIMS}])([^{DELIMS}]+?)(?=\.\{{|[{DELIMS}]|$)")
NAME = re.compile(r'^\{"name":"((?:[^"\\]|\\.)*)"')


def sha256(text: str) -> str:
    """Hex SHA-256 of a text, as recorded in ``docs/statements.json``."""
    return hashlib.sha256(text.encode()).hexdigest()


def read_record(path: Path) -> dict[str, str]:
    """One record of statements: theorem name → hex SHA-256 of its printed type."""
    raw: Any = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict) or not all(isinstance(v, str) for v in raw.values()):
        raise SystemExit(f"{path}: expected a JSON object theorem name -> hash")
    return raw


def record_text(table: dict[str, str]) -> str:
    """The text of a record as committed: sorted keys, one entry per line."""
    return json.dumps(table, indent=1, sort_keys=True) + "\n"


def read_records(
    root: Path = ROOT, missing_ok: bool = False
) -> dict[str, dict[str, str]]:
    """Both records, ``core`` and ``catalogue``; a name in both is an error.

    A missing file is an error too, unless ``missing_ok`` (then it counts as empty).
    """
    parts: dict[str, dict[str, str]] = {}
    for part, name in RECORDS.items():
        path = root / name
        parts[part] = read_record(path) if path.exists() or not missing_ok else {}
    both = sorted(set(parts["core"]) & set(parts["catalogue"]))
    if both:
        raise SystemExit(
            f"recorded in both {RECORDS['core']} and {RECORDS['catalogue']}: "
            + ", ".join(both[:5])
            + (f" and {len(both) - 5} more" if len(both) > 5 else "")
        )
    return parts


def load_recorded(root: Path = ROOT, scope: str = "all") -> dict[str, str]:
    """The recorded statements of the core, of the catalogue, or of both (``scope``)."""
    if scope not in SCOPES:
        raise SystemExit(f"scope must be one of {', '.join(SCOPES)}, not {scope!r}")
    parts = read_records(root)
    return {
        name: digest
        for part, table in parts.items()
        if scope in (part, "all")
        for name, digest in table.items()
    }


def library_modules(root: Path = ROOT, lib: str = EVERYTHING) -> list[str]:
    """The modules of a library: the imports of its root file ``<lib>.lean``.

    An imported root file stands for its own imports: ``LeanDLRACatalogue.lean`` begins with
    ``import LeanDLRA``, which stands for the modules of the core library.
    """
    text = (root / f"{lib}.lean").read_text(encoding="utf-8")
    modules: list[str] = []
    for m in re.finditer(r"^import\s+(\S+)", text, re.MULTILINE):
        name = m.group(1)
        if "." not in name and (root / f"{name}.lean").is_file():
            modules += library_modules(root, name)
        else:
            modules.append(name)
    return modules


def load_renames(path: Path) -> dict[str, str]:
    """The rename map, with chains followed (``A → B``, ``B → C`` gives ``A → C``, ``B → C``)."""
    if not path.exists():
        return {}
    raw: Any = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise SystemExit(f"{path}: expected a JSON object old name -> new name")
    for old, new in raw.items():
        if (
            not isinstance(new, str)
            or not IDENT.fullmatch(old)
            or not IDENT.fullmatch(new)
        ):
            raise SystemExit(
                f"{path}: not a pair of constant names: {old!r} -> {new!r}"
            )
    final: dict[str, str] = {}
    for old in raw:
        seen = [old]
        name = raw[old]
        while name in raw and name != raw[name]:
            if name in seen:
                raise SystemExit(
                    f"rename map has a cycle: {' -> '.join([*seen, name])}"
                )
            seen.append(name)
            name = raw[name]
        if name != old:
            final[old] = name
    return final


def dump(names: set[str], lib: str = EVERYTHING) -> dict[str, str]:
    """Name → printed type, for the theorems of a library with one of the given names."""
    modules = library_modules(lib=lib)
    cmd = ["nice", "-n", "10", "lake", "env", "lean", "--run", "scripts/DumpTypes.lean"]
    table: dict[str, str] = {}
    with subprocess.Popen(
        [*cmd, "--modules", *modules], cwd=ROOT, stdout=subprocess.PIPE, text=True
    ) as proc:
        assert proc.stdout is not None
        for line in proc.stdout:
            m = NAME.match(line)
            if m and json.loads(f'"{m.group(1)}"') in names:
                entry = json.loads(line)
                table[entry["name"]] = entry["type"]
    if proc.returncode != 0:
        raise SystemExit(
            f"scripts/DumpTypes.lean failed with exit status {proc.returncode}"
        )
    return table


def candidates(text: str, renames: dict[str, str], cap: int) -> Iterator[str]:
    """Texts that the rename map turns into ``text``: possible recorded forms of a new type."""
    olds: dict[str, list[str]] = defaultdict(list)
    for old, new in sorted(renames.items()):
        olds[new].append(old)
    spots = [(m.start(1), m.end(1), m.group(1)) for m in TOKEN.finditer(text)]
    if any(name in renames for _, _, name in spots):
        return  # mentions an old name, which the map would have renamed
    spots = [s for s in spots if s[2] in olds]

    def build(choice: list[str]) -> str:
        parts: list[str] = []
        pos = 0
        for (start, end, _), name in zip(spots, choice, strict=True):
            parts += [text[pos:start], name]
            pos = end
        return "".join(parts) + text[pos:]

    names = sorted({name for _, _, name in spots})
    options = {name: [name, *olds[name]] for name in names}
    uniform = 1
    for name in names:
        uniform *= len(options[name])
    if uniform > cap:
        return
    for combo in itertools.product(*(options[name] for name in names)):
        chosen = dict(zip(names, combo, strict=True))
        yield build([chosen[name] for _, _, name in spots])
    separate = 1
    for _, _, name in spots:
        separate *= len(options[name])
    if uniform < separate <= cap:
        for choice in itertools.product(*(options[name] for _, _, name in spots)):
            yield build(list(choice))


def check(
    recorded: dict[str, str], proved: dict[str, str], renames: dict[str, str], cap: int
) -> tuple[int, int, list[str]]:
    """Counts of exact matches and matches via the rename map, and the failures."""
    exact = via = 0
    problems: list[str] = []
    for name, digest in recorded.items():
        new_name = renames.get(name, name)
        text = proved.get(new_name)
        note = f" (renamed to {new_name})" if new_name != name else ""
        if text is None:
            problems.append(f"missing: {name}{note}")
        elif new_name == name and sha256(text) == digest:
            exact += 1
        elif any(sha256(c) == digest for c in candidates(text, renames, cap)):
            via += 1
        else:
            problems.append(f"differs: {name}{note}")
    return exact, via, problems


def main(
    renames: str = RENAMES, cap: int = 1 << 16, lib: str = EVERYTHING, scope: str = ""
) -> None:
    """Compare the compiled statements of the library ``lib`` with the recorded ones.

    ``scope`` (``core``, ``catalogue`` or ``all``) chooses the records; by default the core
    record for the core library ``LeanDLRA`` and both records otherwise.
    """
    scope = scope or ("core" if lib == "LeanDLRA" else "all")
    recorded = load_recorded(ROOT, scope)
    renames_path = Path(renames) if Path(renames).is_absolute() else ROOT / renames
    rmap = load_renames(renames_path)
    proved = dump(set(recorded) | {rmap[n] for n in recorded if n in rmap}, lib)
    exact, via, problems = check(recorded, proved, rmap, cap)
    print(
        f"{exact + via} of {len(recorded)} recorded statements proved verbatim "
        f"({exact} exactly, {via} via the rename map {renames} with {len(rmap)} entries; "
        f"records: {scope})"
    )
    if problems:
        print("\n".join(problems))
        sys.exit(1)


def cli() -> None:
    """Command line."""
    import fire  # imported here so that the tests need only pytest

    fire.Fire(main)


if __name__ == "__main__":
    cli()
