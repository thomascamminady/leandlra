# /// script
# requires-python = ">=3.11"
# dependencies = ["fire"]
# ///
"""Statement hash diff: did a batch change what any declaration of the library says?

Phase A1 of ``wip/UNIFY.md``. The workflow for one batch of the unification:

1. ``make build && make dump`` before the batch (writes ``.lake/hashdiff/after.jsonl.gz``);
2. apply the batch, add its renames to ``docs/renames.json``;
3. ``make build && make dump`` after the batch (the previous dump becomes
   ``.lake/hashdiff/before.jsonl.gz``);
4. ``make hashdiff`` (add ``MOVE=1`` for a batch that only moves declarations).

The same with explicit files::

    uv run scripts/hashdiff.py dump before.jsonl.gz
    uv run scripts/hashdiff.py dump after.jsonl.gz
    uv run scripts/hashdiff.py diff before.jsonl.gz after.jsonl.gz --move --report=hashdiff.md

``dump`` checks with ``lake build --no-build`` that the build is current, then runs
``scripts/DumpTypes.lean --canonical`` on every module of a library (by default everything: the
modules imported by ``LeanDLRACatalogue.lean``, the core and the catalogue of
``docs/STRUCTURE.md``; ``--lib=LeanDLRA`` dumps the core library alone) and writes one
JSON line per theorem, definition, inductive type and constructor: the fully elaborated type (and
the body of a definition), printed with every argument and every constant by its full name,
binder names erased, universe parameters numbered, private names without their module. Gzipped if
the file name ends in ``.gz``.

``diff`` applies the rename map (``{"Old.name": "New.name", ...}``, chains followed) to the
declaration names and to every constant in the texts of both dumps, then reports every declaration
whose type (or definition body) changed, disappeared or appeared. Each old declaration is compared
with its new name. New declarations named like an old name in the map are the deprecated aliases
a rename leaves behind. With ``--move`` the exit status is 1 if any type or body changed or any
declaration disappeared: a move must not change what anything says.
"""

from __future__ import annotations

import datetime
import gzip
import hashlib
import json
import os
import re
import subprocess
import sys
from collections import defaultdict
from collections.abc import Callable, Iterator
from dataclasses import dataclass, field
from pathlib import Path
from typing import IO, Any

ROOT = Path(__file__).resolve().parent.parent
DUMPER = "scripts/DumpTypes.lean"
FORMAT = "leandlra-hashdiff/1"
RENAMES = "docs/renames.json"
# The library of all modules (core and catalogue); the core library alone is ``LeanDLRA``.
EVERYTHING = "LeanDLRACatalogue"

# Characters that delimit constants in `Expr.dbgToString` output. A constant is a maximal run of
# other characters, optionally followed by its universe levels `.{u0, 0}`.
DELIMS = r"\s()\[\]{}⦃⦄,"
IDENT = re.compile(r"[^" + DELIMS + r"]+")


# ---------------------------------------------------------------------------------------------
# Library and rename map


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


def unlisted_sources(modules: list[str], root: Path = ROOT) -> list[str]:
    """Source files below ``LeanDLRA/`` whose module is not among the given ones."""
    listed = set(modules)
    found = (
        ".".join(p.relative_to(root).with_suffix("").parts)
        for p in (root / "LeanDLRA").rglob("*.lean")
    )
    return sorted(m for m in found if m not in listed)


def load_renames(path: Path) -> dict[str, str]:
    """The rename map in ``path`` (old constant name → new constant name); empty if missing."""
    if not path.exists():
        return {}
    raw: Any = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise SystemExit(f"{path}: expected a JSON object old name -> new name")
    renames: dict[str, str] = {}
    for old, new in raw.items():
        if (
            not isinstance(new, str)
            or not IDENT.fullmatch(old)
            or not IDENT.fullmatch(new)
        ):
            raise SystemExit(
                f"{path}: not a pair of constant names: {old!r} -> {new!r}"
            )
        if old != new:
            renames[old] = new
    return renames


def normalize_renames(renames: dict[str, str]) -> dict[str, str]:
    """Follow chains (``A → B``, ``B → C`` gives ``A → C``, ``B → C``); reject cycles."""
    final: dict[str, str] = {}
    for old, first in renames.items():
        seen = [old]
        name = first
        while name in renames and renames[name] != name:
            if name in seen:
                raise SystemExit(
                    f"rename map has a cycle: {' -> '.join([*seen, name])}"
                )
            seen.append(name)
            name = renames[name]
        if name != old:
            final[old] = name
    return final


def make_renamer(renames: dict[str, str]) -> Callable[[str], str]:
    """A function replacing every constant of the map in a printed expression by its new name."""
    if not renames:
        return lambda text: text
    # Only tokens starting with a first name component that occurs in the map are looked up.
    heads = sorted(
        {re.escape(name.split(".")[0]) for name in renames}, key=len, reverse=True
    )
    token = re.compile(
        rf"(?<![^{DELIMS}])((?:{'|'.join(heads)})(?:\.[^{DELIMS}]*?)?)(?=\.\{{|[{DELIMS}]|$)"
    )

    def repl(m: re.Match[str]) -> str:
        return renames.get(m.group(1), m.group(1))

    return lambda text: token.sub(repl, text)


# ---------------------------------------------------------------------------------------------
# Dumps


def open_text(path: Path, mode: str) -> IO[str]:
    """Open a text file for reading (``"r"``) or writing (``"w"``), gzipped if named ``*.gz``."""
    if path.suffix != ".gz":
        return path.open(mode, encoding="utf-8")
    if mode == "r":
        return gzip.open(path, "rt", encoding="utf-8")
    return gzip.open(path, "wt", encoding="utf-8", compresslevel=3)


def read_dump(path: Path) -> tuple[dict[str, Any], Iterator[dict[str, Any]]]:
    """The header and an iterator over the declarations of a dump."""
    f = open_text(path, "r")
    header: dict[str, Any] = json.loads(f.readline())
    if header.get("format") != FORMAT:
        f.close()
        raise SystemExit(
            f"{path}: not a hashdiff dump (format {header.get('format')!r})"
        )

    def records() -> Iterator[dict[str, Any]]:
        with f:
            for line in f:
                if line.strip():
                    yield json.loads(line)

    return header, records()


def git(*args: str) -> str:
    """Output of a git command in the repository, or the empty string on failure."""
    r = subprocess.run(
        ["git", *args], check=False, cwd=ROOT, capture_output=True, text=True
    )
    return r.stdout.strip() if r.returncode == 0 else ""


def dump(out: str, check: bool = True, lib: str = EVERYTHING) -> None:
    """Dump every declaration of the built library ``lib`` to ``out`` (``.gz`` for gzip)."""
    modules = library_modules(lib=lib)
    if check:
        r = subprocess.run(
            ["nice", "-n", "10", "lake", "build", "--no-build", lib],
            check=False,
            cwd=ROOT,
            capture_output=True,
            text=True,
        )
        if r.returncode != 0:
            print((r.stdout + r.stderr)[-2000:], file=sys.stderr)
            raise SystemExit(
                f"the build is not current: run `lake build {lib}` first (or --check=False)"
            )
    unlisted = unlisted_sources(modules)
    if lib != EVERYTHING:
        print(
            f"note: {len(unlisted)} modules outside {lib} are not dumped",
            file=sys.stderr,
        )
        unlisted = []
    for m in unlisted:
        print(
            f"warning: {m} is not imported by {lib}.lean (not dumped)",
            file=sys.stderr,
        )
    target = Path(out)
    target.parent.mkdir(parents=True, exist_ok=True)
    partial = target.with_name(
        "partial-" + target.name
    )  # same suffix, so same compression
    header = {
        "format": FORMAT,
        "created": datetime.datetime.now().isoformat(timespec="seconds"),
        "commit": git("rev-parse", "--short", "HEAD"),
        "dirty": bool(
            git(
                "status",
                "--porcelain",
                "--",
                "LeanDLRA",
                "LeanDLRA.lean",
                f"{EVERYTHING}.lean",
            )
        ),
        "modules": len(modules),
        "lib": lib,
    }
    cmd = ["nice", "-n", "10", "lake", "env", "lean", "--run", DUMPER, "--canonical"]
    count = 0
    with open_text(partial, "w") as f:
        f.write(json.dumps(header) + "\n")
        with subprocess.Popen(
            [*cmd, "--modules", *modules], cwd=ROOT, stdout=subprocess.PIPE, text=True
        ) as proc:
            assert proc.stdout is not None
            for line in proc.stdout:
                if line.startswith("{"):
                    f.write(line)
                    count += 1
        if proc.returncode != 0:
            partial.unlink()
            raise SystemExit(f"{DUMPER} failed with exit status {proc.returncode}")
    os.replace(partial, target)
    print(f"wrote {out}: {count} declarations from {len(modules)} modules")


# ---------------------------------------------------------------------------------------------
# Comparison


@dataclass
class Decl:
    """One dumped declaration, reduced to what the comparison needs."""

    name: str
    module: str
    kind: str
    type_hash: bytes
    value_hash: bytes | None


@dataclass
class Result:
    """The outcome of comparing two dumps."""

    before_count: int = 0
    after_count: int = 0
    renamed: list[tuple[str, str]] = field(default_factory=list)
    unchanged: int = 0
    moved: list[tuple[str, str, str]] = field(default_factory=list)
    type_changed: list[str] = field(default_factory=list)
    value_changed: list[str] = field(default_factory=list)
    disappeared: list[tuple[str, str]] = field(default_factory=list)
    appeared: list[tuple[str, str]] = field(default_factory=list)
    aliases: list[tuple[str, str]] = field(default_factory=list)
    unapplied: list[tuple[str, str]] = field(default_factory=list)

    def failures(self) -> int:
        """Changes that a move batch must not have."""
        return len(self.type_changed) + len(self.value_changed) + len(self.disappeared)


def digest(text: str) -> bytes:
    """SHA-256 of a text."""
    return hashlib.sha256(text.encode()).digest()


def is_alias_value(value: str, target: str) -> bool:
    """Whether a definition body is just the constant ``target`` (a deprecated alias)."""
    return re.fullmatch(re.escape(target) + r"(\.\{[^}]*\})?", value) is not None


def reduce(
    record: dict[str, Any],
    rename: Callable[[str], str],
    name: str,
    alias_of: str | None,
) -> Decl:
    """Hash a dumped declaration after renaming its constants.

    ``alias_of`` is the new name of an old declaration whose body, if it is just that constant, is
    a deprecated alias: its body is then not compared.
    """
    kind: str = record["kind"]
    value: str | None = record.get("value")
    value_hash = None
    if value is not None:
        renamed_value = rename(value)
        if alias_of is None or not is_alias_value(renamed_value, alias_of):
            value_hash = digest(renamed_value)
    return Decl(
        name=name,
        module=record["module"],
        kind=kind,
        type_hash=digest(kind + "\0" + rename(record["type"])),
        value_hash=value_hash,
    )


def same_content(a: Decl, b: Decl) -> bool:
    """Whether two reduced declarations agree in kind, type and body (the module may differ)."""
    return (a.kind, a.type_hash, a.value_hash) == (b.kind, b.type_hash, b.value_hash)


def compare(
    before: Iterator[dict[str, Any]],
    after: Iterator[dict[str, Any]],
    renames: dict[str, str],
) -> Result:
    """Compare two dumps under a (normalized) rename map.

    An entry ``old → new`` of the map is applied to an old declaration ``old`` only while the
    rename is being carried out. Once it is settled, that is, ``new`` exists in the old dump too
    and ``old`` is the same declaration in both dumps (what an earlier rename left behind: a
    deprecated alias, or a specialization of ``new``), ``old`` is compared under its own name.
    Otherwise a leftover of another kind or type than its target (a ``def`` that abbreviates a
    structure) would be reported as a changed type in every later comparison.
    """
    rename = make_renamer(renames)
    res = Result()
    new: dict[str, list[Decl]] = defaultdict(list)
    for rec in after:
        new[rec["name"]].append(reduce(rec, rename, rec["name"], None))
        res.after_count += 1
    old_names: set[str] = set()
    read: list[tuple[str, str | None, Decl, Decl | None]] = []
    for rec in before:
        name: str = rec["name"]
        res.before_count += 1
        old_names.add(name)
        target = renames.get(name)
        if target is not None and target not in new:
            res.unapplied.append((name, target))
            target = None
        own = reduce(rec, rename, name, None)
        mapped = None if target is None else reduce(rec, rename, name, target)
        read.append((name, target, own, mapped))
    old: dict[str, list[Decl]] = defaultdict(list)
    for name, target, own, mapped in read:
        if target is None or mapped is None:
            old[name].append(own)
        elif target in old_names and any(
            same_content(own, d) for d in new.get(name, [])
        ):
            old[name].append(own)
            res.aliases.append((name, own.module))
        else:
            res.renamed.append((name, target))
            old[target].append(mapped)
    for key, olds in old.items():
        news = new.get(key)
        if not news:
            res.disappeared += [(d.name, d.module) for d in olds]
            continue
        if {d.type_hash for d in olds} != {d.type_hash for d in news}:
            res.type_changed.append(key)
            continue
        old_values = {d.value_hash for d in olds if d.value_hash is not None}
        new_values = {d.value_hash for d in news if d.value_hash is not None}
        if old_values and new_values and old_values != new_values:
            res.value_changed.append(key)
            continue
        res.unchanged += 1
        old_modules = sorted({d.module for d in olds})
        new_modules = sorted({d.module for d in news})
        if old_modules != new_modules:
            res.moved.append((key, ", ".join(old_modules), ", ".join(new_modules)))
    for key, news in new.items():
        if key in old:
            continue
        bucket = res.aliases if key in renames else res.appeared
        bucket += [(d.name, d.module) for d in news]
    return res


def first_difference(a: str, b: str, width: int = 70) -> tuple[str, str]:
    """The neighbourhoods of the first position where two texts differ."""
    i = 0
    n = min(len(a), len(b))
    while i < n and a[i] == b[i]:
        i += 1
    start = max(0, i - width)

    def cut(s: str) -> str:
        return (
            ("…" if start else "")
            + s[start : i + width]
            + ("…" if i + width < len(s) else "")
        )

    return cut(a), cut(b)


def texts_for(
    path: Path, keys: set[str], rename: Callable[[str], str], renames: dict[str, str]
) -> dict[str, tuple[str, str]]:
    """Renamed ``(type, value)`` texts of the declarations in ``path`` whose (new) name is a key."""
    _, records = read_dump(path)
    out: dict[str, tuple[str, str]] = {}
    for rec in records:
        key = renames.get(rec["name"], rec["name"])
        if key in keys and key not in out:
            out[key] = (
                rename(rec["kind"] + " " + rec["type"]),
                rename(rec.get("value", "")),
            )
    return out


def describe(header: dict[str, Any], path: Path, count: int) -> str:
    """One line about a dump."""
    dirty = " + uncommitted changes" if header.get("dirty") else ""
    return f"{path} ({header.get('created')}, commit {header.get('commit')}{dirty}, {count} declarations)"


def render(
    res: Result,
    before: Path,
    after: Path,
    headers: tuple[dict[str, Any], dict[str, Any]],
    renames_path: Path,
    renames: dict[str, str],
    move: bool,
    limit: int,
) -> str:
    """The Markdown report."""
    rename = make_renamer(renames)
    changed = set(res.type_changed) | set(res.value_changed)
    old_texts = texts_for(before, changed, rename, renames) if changed else {}
    new_texts = texts_for(after, changed, rename, {}) if changed else {}

    def head(items: list[Any]) -> list[Any]:
        return items if limit <= 0 else items[:limit]

    def more(items: list[Any]) -> list[str]:
        return [f"- … and {len(items) - limit} more"] if 0 < limit < len(items) else []

    lines = [
        "# Statement hash diff (scripts/hashdiff.py)",
        "",
        f"- before: {describe(headers[0], before, res.before_count)}",
        f"- after: {describe(headers[1], after, res.after_count)}",
        f"- rename map: {renames_path} ({len(renames)} entries, {len(res.renamed)} applied)",
        f"- mode: {'move (no statement may change)' if move else 'report'}",
        "",
        "| outcome | declarations |",
        "|---|---|",
        f"| unchanged | {res.unchanged} |",
        f"| of which moved to another module | {len(res.moved)} |",
        f"| of which renamed | {len(res.renamed)} |",
        f"| **type changed** | {len(res.type_changed)} |",
        f"| **definition body changed** | {len(res.value_changed)} |",
        f"| **disappeared** | {len(res.disappeared)} |",
        f"| appeared | {len(res.appeared)} |",
        f"| appeared as deprecated alias (old name in the rename map) | {len(res.aliases)} |",
        "",
    ]
    if res.unapplied:
        lines += ["## Rename map entries whose new name is not in the after dump", ""]
        lines += [f"- `{a}` → `{b}`" for a, b in res.unapplied] + [""]
    for title, keys, index in (
        ("Type changed", res.type_changed, 0),
        ("Definition body changed", res.value_changed, 1),
    ):
        if not keys:
            continue
        lines += [f"## {title}", ""]
        for key in head(keys):
            a = old_texts.get(key, ("", ""))[index]
            b = new_texts.get(key, ("", ""))[index]
            x, y = first_difference(a, b)
            lines += [f"- `{key}`", "  ```", f"  - {x}", f"  + {y}", "  ```"]
        lines += [*more(keys), ""]
    for title, pairs in (
        ("Disappeared", res.disappeared),
        ("Appeared", res.appeared),
        ("Deprecated aliases", res.aliases),
    ):
        if pairs:
            lines += [f"## {title}", ""]
            lines += [f"- `{n}` ({m})" for n, m in head(pairs)] + [*more(pairs), ""]
    if res.moved:
        lines += ["## Moved", ""]
        lines += [f"- `{n}`: {a} → {b}" for n, a, b in head(res.moved)] + [
            *more(res.moved),
            "",
        ]
    return "\n".join(lines)


def diff(
    before: str,
    after: str,
    renames: str = RENAMES,
    move: bool = False,
    report: str = "",
    limit: int = 40,
) -> None:
    """Compare two dumps; with ``--move`` exit 1 if any statement changed or disappeared."""
    before_path, after_path = Path(before), Path(after)
    renames_path = Path(renames) if Path(renames).is_absolute() else ROOT / renames
    rmap = normalize_renames(load_renames(renames_path))
    header_b, records_b = read_dump(before_path)
    header_a, records_a = read_dump(after_path)
    res = compare(records_b, records_a, rmap)
    text = render(
        res,
        before_path,
        after_path,
        (header_b, header_a),
        renames_path,
        rmap,
        move,
        limit,
    )
    if report:
        Path(report).write_text(text, encoding="utf-8")
    print(text if not report else text.split("\n## ")[0])
    verdict = (
        f"{len(res.type_changed)} types changed, {len(res.value_changed)} definition bodies "
        f"changed, {len(res.disappeared)} disappeared, {len(res.appeared)} appeared"
    )
    if move and res.failures():
        print(f"FAIL (move batch): {verdict}", file=sys.stderr)
        sys.exit(1)
    print(f"{'OK (move batch)' if move else 'done'}: {verdict}")


def cli() -> None:
    """Command line: ``dump`` and ``diff``."""
    import fire  # imported here so that the tests need only pytest

    fire.Fire({"dump": dump, "diff": diff})


if __name__ == "__main__":
    cli()
