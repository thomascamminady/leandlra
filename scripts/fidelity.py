# /// script
# requires-python = ">=3.11"
# dependencies = ["fire"]
# ///
"""Check that no recorded statement changed without anybody noticing.

``docs/statements.json`` maps theorems to the SHA-256 of their elaborated type, taken before any of
them was proved.  This script dumps the kernel types of the theorems of the library (every module
imported by ``LeanDLRA.lean``, so statements may move between files) and checks each recorded
theorem in one of two ways:

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

It fails if a recorded theorem is missing or has a different type.
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
BASELINE = ROOT / "docs" / "statements.json"
RENAMES = "docs/renames.json"

# Constants in `Expr.dbgToString` output (as in scripts/hashdiff.py): maximal runs of characters
# other than the delimiters, optionally followed by universe levels `.{u_1}`.
DELIMS = r"\s()\[\]{}⦃⦄,"
IDENT = re.compile(r"[^" + DELIMS + r"]+")
TOKEN = re.compile(rf"(?<![^{DELIMS}])([^{DELIMS}]+?)(?=\.\{{|[{DELIMS}]|$)")
NAME = re.compile(r'^\{"name":"((?:[^"\\]|\\.)*)"')


def sha256(text: str) -> str:
    """Hex SHA-256 of a text, as recorded in ``docs/statements.json``."""
    return hashlib.sha256(text.encode()).hexdigest()


def library_modules(root: Path = ROOT) -> list[str]:
    """The modules imported by the root file ``LeanDLRA.lean``."""
    text = (root / "LeanDLRA.lean").read_text(encoding="utf-8")
    return [m.group(1) for m in re.finditer(r"^import\s+(\S+)", text, re.MULTILINE)]


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


def dump(names: set[str]) -> dict[str, str]:
    """Name → printed type, for the theorems of the library with one of the given names."""
    modules = library_modules()
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


def main(renames: str = RENAMES, cap: int = 1 << 16) -> None:
    """Compare the compiled statements with the recorded baseline."""
    recorded: dict[str, str] = json.loads(BASELINE.read_text(encoding="utf-8"))
    renames_path = Path(renames) if Path(renames).is_absolute() else ROOT / renames
    rmap = load_renames(renames_path)
    proved = dump(set(recorded) | {rmap[n] for n in recorded if n in rmap})
    exact, via, problems = check(recorded, proved, rmap, cap)
    print(
        f"{exact + via} of {len(recorded)} recorded statements proved verbatim "
        f"({exact} exactly, {via} via the rename map {renames} with {len(rmap)} entries)"
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
