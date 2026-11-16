# /// script
# requires-python = ">=3.11"
# dependencies = ["fire", "polars"]
# ///
"""Index of the definitions of the core library (``docs/DEFINITIONS.md``).

The core library is the set of modules imported by ``LeanDLRA.lean`` (``docs/STRUCTURE.md``). This
script reads their sources and lists every ``def``, ``abbrev``, ``structure``, ``class`` and
``inductive``: full name, kind, file and line, and the first sentence of the docstring. Deprecated
aliases are listed in a section of their own. It needs no Lean and no build.

The sources are scanned as text. Comments and strings are blanked first, so a declaration keyword
inside a docstring is not read as a declaration; namespaces are followed through ``namespace`` /
``section`` / ``mutual`` / ``end``. ``check`` compares the result with the statement record of the
gate (``.lake/hashdiff/rolling.jsonl.gz``), which is produced by Lean itself.

Usage::

    uv run -q scripts/definitions.py write          # writes docs/DEFINITIONS.md
    uv run -q scripts/definitions.py missing        # definitions without a docstring
    uv run -q scripts/definitions.py kinds          # numbers by kind
    uv run -q scripts/definitions.py check          # compare with the statement record
"""

from __future__ import annotations

import gzip
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

import polars as pl

PACKAGE = "LeanDLRA"
CORE_ROOT = "LeanDLRA.lean"
ROLLING = ".lake/hashdiff/rolling.jsonl.gz"

#: The path of this script in the repository, as printed in the header of the page.
SELF = "scripts/definitions.py"

#: The declaration kinds of the index.
KINDS = (
    "def",
    "abbrev",
    "structure",
    "class",
    "class inductive",
    "class abbrev",
    "inductive",
)

#: Kinds that are scanned only to explain names of the statement record: named instances, and
#: aliases (an alias of a definition is a definition for Lean).
OTHER_KINDS = ("alias", "instance")

MODIFIER = (
    r"(?:private|protected|noncomputable|unsafe|partial|nonrec|public|scoped|local)"
)
COMMAND = re.compile(
    r"^[ \t]*(?:"
    r"(?P<ns>namespace)[ \t]+(?P<nsname>\S+)"
    r"|(?P<sec>(?:noncomputable[ \t]+)?(?:public[ \t]+)?section)\b[^\n]*"
    r"|(?P<mutual>mutual)[ \t]*$"
    r"|(?P<end>end)(?:[ \t]+\S+)?[ \t]*$"
    r"|(?P<attrs>(?:@\[[^\]]*\]\s*)*)"
    rf"(?P<mods>(?:{MODIFIER}\s+)*)"
    r"(?P<kind>def|abbrev|structure|class[ \t]+inductive|class[ \t]+abbrev|class|inductive"
    r"|alias|instance)"
    r"[ \t]+(?:\(priority[^)\n]*\)[ \t]*)?(?P<name>[^\s:({\[⦃]+)"
    r")",
    re.MULTILINE,
)

#: Abbreviations after which a period does not end a sentence.
ABBREVIATIONS = (
    "e.g",
    "i.e",
    "cf",
    "resp",
    "vs",
    "Thm",
    "Lem",
    "Def",
    "Prop",
    "Cor",
    "Rem",
    "Alg",
    "Sec",
    "Fig",
    "Eq",
    "eq",
    "eqs",
    "Ch",
    "No",
    "p",
    "pp",
)


@dataclass(frozen=True)
class Definition:
    """One definition of the core library."""

    name: str
    kind: str
    module: str
    folder: str
    file: str
    line: int
    private: bool
    documented: bool
    summary: str
    deprecated: bool
    target: str


def core_modules(root: Path) -> list[str]:
    """The modules of the core library: the imports of ``LeanDLRA.lean``."""
    modules: list[str] = []
    for line in (root / CORE_ROOT).read_text(encoding="utf-8").splitlines():
        match = re.fullmatch(rf"import\s+({PACKAGE}\.\S+)\s*", line)
        if match:
            modules.append(match.group(1))
    return modules


def source_of(module: str, root: Path) -> Path:
    """The source file of a module."""
    return root.joinpath(*module.split(".")).with_suffix(".lean")


def blank_comments(text: str) -> tuple[str, list[tuple[int, int, str]]]:
    """Blank comments and strings; collect the docstrings.

    Returns the text with every comment and every string literal replaced by spaces (line breaks
    are kept, so offsets and line numbers agree with the source), and the docstrings ``/-- … -/``
    as triples ``(start, end, content)``. Block comments nest.
    """
    out = list(text)
    docs: list[tuple[int, int, str]] = []
    i = 0
    n = len(text)

    def blank(start: int, end: int) -> None:
        for k in range(start, end):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        if text.startswith("--", i):
            end = text.find("\n", i)
            end = n if end < 0 else end
            blank(i, end)
            i = end
        elif text.startswith("/-", i):
            start = i
            depth = 1
            i += 2
            while i < n and depth > 0:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if text.startswith("/--", start) and not text.startswith("/---", start):
                docs.append((start, i, text[start + 3 : max(start + 3, i - 2)]))
            blank(start, i)
        elif text[i] == '"':
            start = i
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i = min(n, i + 1)
            blank(start, i)
        elif text[i] == "'" and i + 2 < n and text[i + 1] == '"' and text[i + 2] == "'":
            i += 3  # the character literal '"'
        else:
            i += 1
    return "".join(out), docs


def first_sentence(doc: str) -> str:
    """The first sentence of a docstring, on one line.

    The first paragraph is taken and cut after the first period that ends a sentence: a period
    outside backticks and brackets, not after an abbreviation such as ``Thm.``, and followed by the
    end of the paragraph or by white space and a capital letter, a backtick, a bracket or ``*``.
    A paragraph without such a period (for example one that ends with a colon before a displayed
    formula) is returned whole.
    """
    paragraph = re.split(r"\n[ \t]*\n", doc.strip(), maxsplit=1)[0]
    line = re.sub(r"\s+", " ", paragraph).strip()
    in_code = False
    depth = 0
    for i, ch in enumerate(line):
        if ch == "`":
            in_code = not in_code
        elif in_code:
            continue
        elif ch in "[(":
            depth += 1
        elif ch in "])":
            depth = max(0, depth - 1)
        elif ch == "." and depth == 0:
            rest = line[i + 1 :]
            if rest and not re.match(r"\s+(?:[A-Z`\[(*]|$)", rest):
                continue
            word = re.search(r"([A-Za-z.]+)$", line[:i])
            if word and word.group(1) in ABBREVIATIONS:
                continue
            return line[: i + 1]
    return line


def scan(module: str, root: Path) -> list[Definition]:
    """The declarations of one module with a kind of ``KINDS`` or ``OTHER_KINDS``, in source order.

    For an alias, ``target`` is the declaration it stands for; ``deprecated`` says whether the
    declaration carries the attribute ``deprecated``.
    """
    path = source_of(module, root)
    text = path.read_text(encoding="utf-8")
    code, docs = blank_comments(text)
    rel = path.relative_to(root).as_posix()
    folder = "/".join(module.split(".")[1:-1])
    scopes: list[str | None] = []
    found: list[Definition] = []
    for match in COMMAND.finditer(code):
        if match.group("ns"):
            scopes.append(match.group("nsname"))
        elif match.group("sec") or match.group("mutual"):
            scopes.append(None)
        elif match.group("end"):
            if scopes:
                scopes.pop()
        else:
            raw = match.group("name")
            if raw.startswith("_root_."):
                name = raw.removeprefix("_root_.")
            else:
                name = ".".join([s for s in scopes if s is not None] + [raw])
            start = match.start()
            kind = re.sub(r"\s+", " ", match.group("kind"))
            target = (
                re.match(r"\s*:=\s*(\S+)", code[match.end() :])
                if kind == "alias"
                else None
            )
            doc = next(
                (
                    d
                    for d in reversed(docs)
                    if d[1] <= start and not code[d[1] : start].strip()
                ),
                None,
            )
            found.append(
                Definition(
                    name=name,
                    kind=kind,
                    module=module,
                    folder=folder,
                    file=rel,
                    line=text.count("\n", 0, match.start("kind")) + 1,
                    private="private" in match.group("mods").split(),
                    documented=doc is not None,
                    summary=first_sentence(doc[2]) if doc is not None else "",
                    deprecated="deprecated" in match.group("attrs"),
                    target=target.group(1) if target else "",
                )
            )
    return found


def scan_all(root: Path) -> list[Definition]:
    """The scanned declarations of all core modules, aliases and named instances included."""
    return [d for module in core_modules(root) for d in scan(module, root)]


def scan_core(root: Path) -> list[Definition]:
    """The definitions of all core modules (the kinds of ``KINDS``)."""
    return [d for d in scan_all(root) if d.kind in KINDS]


def frame(definitions: list[Definition]) -> pl.DataFrame:
    """The definitions as a table."""
    return pl.DataFrame([asdict(d) for d in definitions])


def cell(text: str) -> str:
    """A text as the cell of a Markdown table."""
    return text.replace("|", "\\|")


def link(d: Definition) -> str:
    """A link from ``docs/`` to the source line of a definition."""
    short = d.file.removeprefix(f"{PACKAGE}/")
    return f"[{short}:{d.line}](../{d.file}#L{d.line})"


def render(declarations: list[Definition], modules: int) -> str:
    """The page ``docs/DEFINITIONS.md`` from the result of ``scan_all``."""
    definitions = [d for d in declarations if d.kind in KINDS]
    aliases = [d for d in declarations if d.kind == "alias" and d.deprecated]
    public = [d for d in definitions if not d.private]
    private = [d for d in definitions if d.private]
    undocumented = [d for d in public if not d.documented]
    lines: list[str] = [
        "# Definitions of the core library",
        "",
        f"Generated by `{SELF}` from the sources; do not edit by hand.",
        "",
        "This page lists every `def`, `abbrev`, `structure`, `class` and `inductive` of the core",
        "library (the modules imported by `LeanDLRA.lean`, see [STRUCTURE.md](STRUCTURE.md)): the",
        "full name, the kind, the file and line, and the first sentence of the docstring. Theorems",
        "are not listed; for the main theorems see [MAIN_RESULTS.md](MAIN_RESULTS.md). How the",
        "definitions relate to each other is the subject of [CONCEPTS.md](CONCEPTS.md). Fields of",
        "structures, instances and notations are not listed; they are in the file of their",
        "structure or type.",
        "",
        (
            f"The core has {modules} modules with {len(public)} definitions"
            f" ({len(undocumented)} of them without a docstring) and {len(private)} private"
            " definitions, which are helpers of one file and are not listed."
        ),
        "",
        "## Numbers by folder",
        "",
        "| Folder | Modules | Definitions | Without docstring |",
        "|---|---:|---:|---:|",
    ]
    counts = (
        frame(public)
        .group_by("folder")
        .agg(
            pl.col("module").n_unique().alias("modules"),
            pl.len().alias("definitions"),
            (~pl.col("documented")).sum().alias("undocumented"),
        )
        .sort("folder")
    )
    for row in counts.iter_rows(named=True):
        lines.append(
            f"| `{row['folder']}` | {row['modules']} | {row['definitions']}"
            f" | {row['undocumented']} |"
        )
    folders = sorted({d.folder for d in public})
    for folder in folders:
        lines += [
            "",
            f"## `{PACKAGE}/{folder}`",
            "",
            "| Name | Kind | File and line | First sentence of the docstring |",
            "|---|---|---|---|",
        ]
        for d in sorted(
            (d for d in public if d.folder == folder), key=lambda d: (d.file, d.line)
        ):
            summary = cell(d.summary) if d.documented else "*(no docstring)*"
            lines.append(f"| `{d.name}` | {d.kind} | {link(d)} | {summary} |")
    lines += [
        "",
        "## Definitions without a docstring",
        "",
    ]
    if undocumented:
        lines += ["| Name | Kind | File and line |", "|---|---|---|"]
        for d in sorted(undocumented, key=lambda d: (d.file, d.line)):
            lines.append(f"| `{d.name}` | {d.kind} | {link(d)} |")
    else:
        lines.append("None.")
    if aliases:
        lines += [
            "",
            "## Deprecated aliases",
            "",
            "Old names that still compile, with a deprecation warning. Use the new name.",
            "",
            "| Old name | New name | File and line |",
            "|---|---|---|",
        ]
        for d in sorted(aliases, key=lambda d: (d.file, d.line)):
            lines.append(f"| `{d.name}` | `{d.target}` | {link(d)} |")
    return "\n".join(lines) + "\n"


def recorded_definitions(path: Path, modules: set[str]) -> set[str]:
    """The definitions of the given modules in the statement record of the gate.

    The record has one JSON object per line (keys ``kind``, ``module``, ``name``, ``type``,
    ``value``) after a header line. Definitions have the kind ``def`` or ``inductive``. Names that
    Lean generates (``match_1``, ``proof_1``, ``_priv.…``, instances ``inst…``, …) are left out.
    """
    generated = re.compile(
        r"(^_priv\.|\.match_\d|\.proof_\d|\._|\.inst[A-Z]|^inst[A-Z]|\.eq_\d)"
    )
    names: set[str] = set()
    with gzip.open(path, "rt", encoding="utf-8") as handle:
        next(handle)
        for line in handle:
            record = json.loads(line)
            if record["module"] not in modules or record["kind"] not in (
                "def",
                "inductive",
            ):
                continue
            if not generated.search(record["name"]):
                names.add(record["name"])
    return names


class Commands:
    """The commands of ``definitions.py``."""

    def __init__(self, root: str = "") -> None:
        self.root: Path = Path(root).resolve() if root else Path.cwd()
        if not (self.root / CORE_ROOT).is_file():
            raise SystemExit(f"{self.root} is not the repository root (no {CORE_ROOT})")

    def write(self, output: str = "docs/DEFINITIONS.md") -> None:
        """Write the index of the definitions of the core to ``output``."""
        modules = core_modules(self.root)
        declarations = scan_all(self.root)
        Path(output).write_text(render(declarations, len(modules)), encoding="utf-8")
        public = [d for d in declarations if d.kind in KINDS and not d.private]
        print(
            f"{output}: {len(modules)} modules, {len(public)} definitions,"
            f" {sum(not d.documented for d in public)} without a docstring"
        )

    def missing(self, private: bool = False) -> None:
        """Print the core definitions without a docstring (``--private``: the private ones)."""
        for d in scan_core(self.root):
            if not d.documented and d.private == private:
                print(f"{d.file}:{d.line}: {d.kind} {d.name}")

    def kinds(self) -> None:
        """Print the number of definitions of each kind."""
        table = (
            frame(scan_core(self.root))
            .group_by("kind", "private")
            .agg(
                pl.len().alias("definitions"),
                (~pl.col("documented")).sum().alias("undocumented"),
            )
            .sort("kind", "private")
        )
        with pl.Config(tbl_rows=-1):
            print(table)

    def check(self, record: str = ROLLING) -> None:
        """Compare the definitions found in the sources with the statement record of the gate.

        Exit status 1 if a public definition of the sources is missing in the record, or if a
        definition of the record is not explained by the sources. A name of the record is
        explained if it is a scanned definition, an alias or a named instance, or if it lies
        below a scanned structure or inductive type (a field or a generated eliminator).
        """
        modules = core_modules(self.root)
        recorded = recorded_definitions(self.root / record, set(modules))
        declarations = [d for d in scan_all(self.root) if not d.private]
        scanned = {d.name for d in declarations if d.kind in KINDS}
        others = {d.name for d in declarations if d.kind in OTHER_KINDS}
        types = {
            d.name
            for d in declarations
            if d.kind not in ("def", "abbrev", *OTHER_KINDS)
        }

        def below_type(name: str) -> bool:
            parts = name.split(".")
            return any(".".join(parts[:k]) in types for k in range(1, len(parts)))

        only_sources = sorted(scanned - recorded)
        only_record = sorted(
            n for n in recorded - scanned - others if not below_type(n)
        )
        for name in only_sources:
            print(f"in the sources, not in the record: {name}")
        for name in only_record:
            print(f"in the record, not in the sources: {name}")
        print(
            f"{len(scanned)} definitions in the sources, {len(recorded)} in the record,"
            f" {len(scanned & recorded)} in both"
        )
        if only_sources or only_record:
            sys.exit(1)


if __name__ == "__main__":
    import fire  # imported here so that the tests need only pytest and polars

    fire.Fire(Commands)
