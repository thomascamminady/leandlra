# /// script
# requires-python = ">=3.11"
# dependencies = ["fire"]
# ///
"""Pages that quote Lean statements: expand a template from the sources, and check a page.

No Lean is run. A template is a Markdown file in which a line may be one of the directives

``@stmt FILE NAME FULLNAME``   the statement of the declaration ``NAME`` of ``FILE`` (the name as
                               written after the keyword, without a universe list ``.{u}``;
                               ``NAME#k`` selects the k-th declaration of that name), cut
                               before its ``:=`` or ``where``;
                               definitions and structures are quoted up to the next blank line.
``@full FILE NAME FULLNAME``   the declaration ``NAME`` up to the next blank line (with proof).
``@ex FILE K``                 the statement of the K-th ``example`` of ``FILE``.
``@exfull FILE K``             the K-th ``example`` of ``FILE`` up to the next blank line.
``@lines FILE START END [FULLNAME]``  the source lines ``START`` to ``END`` (any text file of
                               the repository; the block is fenced as ``lean`` for a Lean file
                               and as ``text`` otherwise).
``@quote FILE FIRST [|| LAST]``  the same for lines that are found by their text: from the one
                               line of ``FILE`` in which the regular expression ``FIRST`` is
                               found to the next line in which ``LAST`` is found (without
                               ``LAST``: that one line). Use it for files whose lines move.

Inside a line, ``@loc(FILE NAME)`` stands for a link ``[FILE:LINE](…FILE#LLINE)`` to the line on
which the declaration ``NAME`` of ``FILE`` starts (for the tables of a page), and ``@file(FILE)``
for a link to a file or folder of the repository, which must exist. In both links a leading
``LeanDLRA/`` is left out of the text. ``@commit`` stands for the short hash and the date of the
commit ``HEAD``, as in ``59b1738 (2026-11-10)``, and ``@coremodules`` for the number of modules
that ``LeanDLRA.lean`` imports.

``expand`` replaces each directive by a line with a link to the quoted lines and a fenced block
with the text of the source. ``check`` compares every ``lean`` block of a page with the lines its
link cites and looks up every identifier and path written in backticks (spans of at most three
characters are taken for variables unless they are core declarations). A link to a line in a table
row that starts with a backticked name is compared with that name.

``expand`` writes nothing and ends with code 2 if a file it quotes differs from ``HEAD`` (``git
status --porcelain`` lists it): a page that exists was generated from committed text, so that it
may name the commit. ``keys`` lists the citation keys ``[Key]`` and ``[Key, …]`` of the comments
of the core modules and of the given pages that have no entry in the bibliography.

    uv run scripts/docgen.py expand TEMPLATE OUT [--prefix ../] [--root .]
    uv run scripts/docgen.py check PAGE [PAGE ...] [--verbose] [--root .]
    uv run scripts/docgen.py keys [PAGE ...] [--bib docs/references.bib] [--root .]

Exit codes: 0 nothing to report; 1 ``check`` or ``keys`` found a problem, or a directive names a
declaration that does not exist; 2 ``expand`` found a quoted file that differs from ``HEAD``.
"""

from __future__ import annotations

import gzip
import json
import re
import subprocess
import sys
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path

import core

OPEN = "([{⟨⦃"
CLOSE = ")]}⟩⦄"
BODY_KINDS = ("def", "abbrev", "structure", "class", "inductive")
RECORD = ".lake/hashdiff/rolling.jsonl.gz"
LINK = re.compile(r"\]\((?:\.\./)*(?P<file>[^)#\s]+)#L(?P<a>\d+)(?:-L(?P<b>\d+))?\)")
LOC = re.compile(r"@loc\((?P<file>\S+) (?P<name>[^)\s]+)\)")
ROW = re.compile(r"^\| `(?P<name>[^`]+)` \|")
FILE = re.compile(r"@file\((?P<file>[^)\s]+)\)")
IDENT = re.compile(r"^[A-Za-z_𝓛][\w.'₀-₉!?𝓛]*$")
TAIL = re.compile(r"^\s*(:=.*|where.*)?\s*$", re.DOTALL)
PATH_END = (".lean", ".md", ".py", ".txt", ".bib", ".gz", ".json", ".toml")
BLANK = re.compile(r"\n[ \t]*\n")
COMMIT = re.compile(r"@commit\b")
CORE = re.compile(r"@coremodules\b")
KEY = re.compile(r"\[(?P<key>[A-Z][A-Za-z]*\d{4}[a-z]?)(?=[\],;])")
ENTRY = re.compile(r"^@\w+\s*\{\s*(?P<key>[^,\s]+)\s*,", re.MULTILINE)
BIB = "docs/references.bib"


@dataclass(frozen=True)
class Statement:
    """A declaration cut out of a source file: lines ``start`` to ``end`` (1-based, inclusive)."""

    file: str
    name: str
    kind: str
    start: int
    end: int
    text: str


def blank_comments(text: str) -> str:
    """Replace comments by spaces, keeping offsets (block comments nest)."""
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        if text.startswith("--", i):
            end = text.find("\n", i)
            end = n if end < 0 else end
            for k in range(i, end):
                out[k] = " "
            i = end
        elif text.startswith("/-", i):
            start, depth = i, 1
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
            for k in range(start, i):
                if out[k] != "\n":
                    out[k] = " "
        else:
            i += 1
    return "".join(out)


def is_where(code: str, i: int) -> bool:
    """Whether the keyword ``where`` starts at offset ``i``."""
    return code[i - 1].isspace() and re.match(r"where\b", code[i : i + 6]) is not None


def statement_end(code: str, begin: int) -> int:
    """Offset of the ``:=`` or ``where`` of bracket depth 0 after ``begin``."""
    depth, i = 0, begin
    while i < len(code):
        ch = code[i]
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
        elif depth == 0 and (code.startswith(":=", i) or is_where(code, i)):
            return i
        i += 1
    return len(code)


def find(
    root: Path, file: str, name: str, occurrence: int = 0, whole: bool = False
) -> Statement:
    """The declaration ``name`` of ``file``; ``name`` may be ``example``.

    With ``whole`` the text runs to the next blank line, otherwise theorems, lemmas, examples
    and instances are cut before their ``:=``.
    """
    text = (root / file).read_text(encoding="utf-8")
    code = blank_comments(text)
    if name == "example":
        pattern = re.compile(r"^(?P<kind>example)\b", re.MULTILINE)
    else:
        pattern = re.compile(
            r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|scoped)\s+)*"
            r"(?P<kind>theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+"
            + re.escape(name)
            + r"(?:\.\{[^}]*\})?(?![\w.'₀-₉!?])",
            re.MULTILINE,
        )
    matches = list(pattern.finditer(code))
    if len(matches) < max(occurrence, 1):
        raise SystemExit(f"{file}: {name} (occurrence {occurrence}) not found")
    if len(matches) > 1 and occurrence == 0:
        raise SystemExit(
            f"{file}: {name} is declared {len(matches)} times; write {name}#k"
        )
    match = matches[max(occurrence, 1) - 1]
    kind = match.group("kind")
    begin = match.start()
    if whole or kind in BODY_KINDS:
        blank = BLANK.search(text, begin)
        stop = blank.start() if blank else len(text)
    else:
        stop = statement_end(code, match.end())
    body = text[begin:stop].rstrip()
    start = text.count("\n", 0, begin) + 1
    return Statement(file, name, kind, start, start + body.count("\n"), body)


def block(st: Statement, full: str, prefix: str) -> list[str]:
    """The line with the link, then the fenced code."""
    one = st.start == st.end
    span = f"line {st.start}" if one else f"lines {st.start}–{st.end}"
    anchor = f"#L{st.start}" if one else f"#L{st.start}-L{st.end}"
    link = f"[`{st.file}`, {span}]({prefix}{st.file}{anchor})"
    head = f"`{full}` in {link}:" if full else f"{link}:"
    fence = "lean" if st.file.endswith(".lean") else "text"
    return [head, "", f"```{fence}", *st.text.split("\n"), "```"]


def location(root: Path, file: str, name: str, prefix: str) -> str:
    """The link ``[FILE:LINE](…)`` to the first line of the declaration ``name`` of ``file``."""
    base, _, occ = name.partition("#")
    st = find(root, file, base, int(occ) if occ else 0)
    return f"[{file.removeprefix('LeanDLRA/')}:{st.start}]({prefix}{file}#L{st.start})"


def file_link(root: Path, file: str, prefix: str) -> str:
    """The link ``[`FILE`](…FILE)`` to a file or folder of the repository, which must exist."""
    if not (root / file).exists():
        raise FileNotFoundError(file)
    return f"[`{file.removeprefix('LeanDLRA/')}`]({prefix}{file})"


def git(root: Path, *args: str) -> str:
    """The output of a git command that only reads, run in ``root``."""
    done = subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=False
    )
    if done.returncode != 0:
        raise SystemExit(f"git {' '.join(args)}: {done.stderr.strip()}")
    return done.stdout


def head_commit(root: Path) -> str:
    """The short hash and the date of the commit ``HEAD``, as ``59b1738 (2026-11-10)``."""
    return git(root, "log", "-1", "--format=%h (%cs)").strip()


def changed_files(root: Path, files: Iterable[str]) -> list[str]:
    """The lines of ``git status --porcelain`` for ``files``: those that differ from ``HEAD``."""
    listed = sorted(set(files))
    if not listed:
        return []
    out = git(root, "status", "--porcelain", "--", *listed)
    return [line for line in out.split("\n") if line.strip()]


def core_count(root: Path, quoted: set[str]) -> str:
    """The number of modules that ``LeanDLRA.lean`` imports."""
    quoted.add(core.CORE_ROOT)
    return str(len(core.core_modules(root)))


def lines_between(root: Path, file: str, first: str, last: str) -> tuple[int, int]:
    """The numbers of the one line in which ``first`` is found and of the next with ``last``."""
    src = (root / file).read_text(encoding="utf-8").split("\n")
    hits = [i for i, line in enumerate(src, 1) if re.search(first, line)]
    if len(hits) != 1:
        raise SystemExit(f"{file}: {len(hits)} lines match {first!r}, expected one")
    if not last:
        return hits[0], hits[0]
    for i in range(hits[0], len(src) + 1):
        if re.search(last, src[i - 1]):
            return hits[0], i
    raise SystemExit(f"{file}: no line from line {hits[0]} on matches {last!r}")


def expand_line(root: Path, line: str, prefix: str, quoted: set[str]) -> list[str]:
    """The lines that replace ``line`` (the line itself if it is no directive).

    The files whose text or line numbers the result contains are added to ``quoted``.
    """
    quoted.update(m["file"] for m in LOC.finditer(line))
    line = LOC.sub(lambda m: location(root, m["file"], m["name"], prefix), line)
    line = FILE.sub(lambda m: file_link(root, m["file"], prefix), line)
    line = COMMIT.sub(lambda _: head_commit(root), line)
    line = CORE.sub(lambda _: core_count(root, quoted), line)
    parts = line.split()
    key = parts[0] if parts else ""
    if key in ("@stmt", "@full", "@ex", "@exfull", "@lines", "@quote"):
        quoted.add(parts[1])
    if key in ("@stmt", "@full"):
        name, _, occ = parts[2].partition("#")
        st = find(root, parts[1], name, int(occ) if occ else 0, whole=key == "@full")
        return block(st, parts[3], prefix)
    if key in ("@ex", "@exfull"):
        st = find(root, parts[1], "example", int(parts[2]), whole=key == "@exfull")
        return block(st, "", prefix)
    if key in ("@lines", "@quote"):
        if key == "@lines":
            start, end = int(parts[2]), int(parts[3])
        else:
            first, _, last = line.split(None, 2)[2].partition(" || ")
            start, end = lines_between(root, parts[1], first.strip(), last.strip())
        src = (root / parts[1]).read_text(encoding="utf-8").split("\n")
        st = Statement(
            parts[1], "", "lines", start, end, "\n".join(src[start - 1 : end])
        )
        return block(st, parts[4] if key == "@lines" and len(parts) > 4 else "", prefix)
    return [line]


def expand(template: str, out: str, prefix: str = "../", root: str = ".") -> None:
    """Write ``out`` from ``template``; ``prefix`` leads from ``out`` to the repository root."""
    result: list[str] = []
    quoted: set[str] = set()
    for line in Path(template).read_text(encoding="utf-8").split("\n"):
        result += expand_line(Path(root), line, prefix, quoted)
    changed = changed_files(Path(root), quoted)
    if changed:
        print(f"{out} not written: quoted files differ from HEAD", file=sys.stderr)
        for line in changed:
            print(f"  {line}", file=sys.stderr)
        raise SystemExit(2)
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    Path(out).write_text("\n".join(result), encoding="utf-8")
    print(f"{out}: {len(result)} lines")


@dataclass(frozen=True)
class Names:
    """Declared names: all recorded names, the core ones, and names by last component."""

    full: frozenset[str]
    core: frozenset[str]
    by_last: dict[str, set[str]]
    core_text: str


def load_names(root: Path) -> Names:
    """Names from the statement record of the gate (if present) and the text of the core."""
    modules = core.core_modules(root)
    core_text = "\n".join(
        (root / (m.replace(".", "/") + ".lean")).read_text(encoding="utf-8")
        for m in modules
    )
    full: set[str] = set()
    in_core: set[str] = set()
    by_last: dict[str, set[str]] = {}
    record = root / RECORD
    if record.exists():
        with gzip.open(record, "rt", encoding="utf-8") as handle:
            next(handle)
            for line in handle:
                entry = json.loads(line)
                name: str = entry["name"]
                full.add(name)
                if entry["module"] in modules:
                    in_core.add(name)
                by_last.setdefault(name.rsplit(".", 1)[-1], set()).add(name)
    return Names(frozenset(full), frozenset(in_core), by_last, core_text)


def check_row(root: Path, page: str, number: int, line: str) -> list[str]:
    """Problems of the links to source lines in a table row that starts with a declared name."""
    row = ROW.match(line)
    if not row:
        return []
    last = row["name"].rsplit(".", 1)[-1]
    problems: list[str] = []
    for link in LINK.finditer(line):
        path = root / link["file"]
        src = path.read_text(encoding="utf-8").split("\n") if path.is_file() else []
        a = int(link["a"])
        if a > len(src) or last not in src[a - 1]:
            problems.append(
                f"{page}:{number}: `{row['name']}` is not declared at {link['file']}:{a}"
            )
    return problems


def check_blocks(
    root: Path, page: str, lines: list[str]
) -> tuple[list[str], list[str], int]:
    """Problems of the code blocks of a page, its prose lines, and the number of blocks."""
    problems: list[str] = []
    prose: list[str] = []
    i, blocks = 0, 0
    while i < len(lines):
        if not lines[i].startswith("```"):
            prose.append(lines[i])
            problems += check_row(root, page, i + 1, lines[i])
            i += 1
            continue
        lang = lines[i][3:].strip()
        j = i + 1
        while j < len(lines) and not lines[j].startswith("```"):
            j += 1
        body = "\n".join(lines[i + 1 : j])
        k = i - 1
        while k >= 0 and not lines[k].strip():
            k -= 1
        link = LINK.search(lines[k]) if k >= 0 else None
        if link:
            blocks += 1
            a = int(link["a"])
            b = int(link["b"] or link["a"])
            src = (root / link["file"]).read_text(encoding="utf-8").split("\n")
            text = "\n".join(src[a - 1 : b])
            if not (text.startswith(body) and TAIL.match(text[len(body) :])):
                problems.append(
                    f"{page}:{i + 1}: block differs from {link['file']}:{a}-{b}"
                )
        elif lang == "lean":
            blocks += 1
            problems.append(
                f"{page}:{i + 1}: lean block without a link to its source lines"
            )
        i = j + 1
    return problems, prose, blocks


def check_span(root: Path, names: Names, span: str, verbose: bool) -> tuple[str, bool]:
    """A message about one backticked span (empty if nothing to say) and whether it is an error."""
    if "/" in span or span.endswith(PATH_END):
        path = span.split("#")[0].split(":")[0]
        if re.search(r"[*<>… ]", path) or (root / path).exists():
            return "", False
        if (root / "LeanDLRA" / path).exists():
            return "", False
        return f"path `{span}` does not exist", True
    if not IDENT.match(span):
        return "", False
    last = span.rsplit(".", 1)[-1]
    hits = {span, "LeanDLRA." + span} & names.full
    if not hits:
        hits = {n for n in names.by_last.get(last, set()) if n.endswith("." + span)}
    if hits & names.core:
        return (
            f"ok `{span}` -> {sorted(hits & names.core)[:2]}" if verbose else ""
        ), False
    if len(span) <= 3:
        return "", False
    if hits:
        return f"`{span}` is recorded only in the catalogue: {sorted(hits)[:2]}", True
    if re.search(r"(?<![\w.'])" + re.escape(last) + r"(?![\w'])", names.core_text):
        note = f"note: `{span}` is not in the record; '{last}' occurs in the core text"
        return (note if verbose else ""), False
    return f"`{span}` not found in the core", True


def check_page(
    root: Path, names: Names, page: str, verbose: bool
) -> tuple[list[str], int]:
    """The messages about one page (the last one is its summary) and the number of problems."""
    lines = Path(page).read_text(encoding="utf-8").split("\n")
    problems, prose, blocks = check_blocks(root, page, lines)
    spans = dict.fromkeys(re.findall(r"`([^`\n]+)`", "\n".join(prose)))
    messages: list[str] = []
    bad = len(problems)
    for span in spans:
        message, error = check_span(root, names, span, verbose)
        if message:
            messages.append(f"{page}: {message}")
        bad += error
    messages += problems
    messages.append(
        f"{page}: {blocks} quoted blocks, {len(spans)} backticked spans, {bad} problems"
    )
    return messages, bad


def check(*pages: str, verbose: bool = False, root: str = ".") -> None:
    """Report blocks that differ from the source and names or paths that do not exist."""
    base = Path(root)
    names = load_names(base)
    total = 0
    for page in pages:
        messages, bad = check_page(base, names, page, verbose)
        print("\n".join(messages))
        total += bad
    raise SystemExit(1 if total else 0)


def comment_text(text: str) -> str:
    """The comments of a Lean source; every other character is replaced by a space."""
    code = blank_comments(text)
    return "".join(
        t if c != t or t.isspace() else " " for c, t in zip(code, text, strict=True)
    )


def bib_keys(text: str) -> set[str]:
    """The keys of the entries of a BibTeX file."""
    return {m["key"] for m in ENTRY.finditer(text)}


def cited_keys(root: Path, pages: Iterable[str]) -> dict[str, list[str]]:
    """Citation key → the files that cite it: comments of the core modules, and ``pages``."""
    texts: dict[str, str] = {}
    for module in core.core_modules(root):
        file = module.replace(".", "/") + ".lean"
        texts[file] = comment_text((root / file).read_text(encoding="utf-8"))
    for page in pages:
        texts[page] = Path(page).read_text(encoding="utf-8")
    cited: dict[str, list[str]] = {}
    for file, text in texts.items():
        for key in sorted({m["key"] for m in KEY.finditer(text)}):
            cited.setdefault(key, []).append(file)
    return cited


def missing_keys(root: Path, pages: Iterable[str], bib: str) -> dict[str, list[str]]:
    """The cited keys without an entry in the bibliography ``bib``, with the citing files."""
    path = root / bib
    known = bib_keys(path.read_text(encoding="utf-8")) if path.is_file() else set()
    cited = cited_keys(root, pages)
    return {key: cited[key] for key in sorted(cited) if key not in known}


def keys(*pages: str, bib: str = BIB, root: str = ".") -> None:
    """List the citation keys of the core and of ``pages`` that have no entry in ``bib``."""
    base = Path(root)
    cited = cited_keys(base, pages)
    missing = missing_keys(base, pages, bib)
    for key, files in missing.items():
        more = f" and {len(files) - 3} more" if len(files) > 3 else ""
        print(f"[{key}] has no entry in {bib}: {', '.join(files[:3])}{more}")
    print(f"{len(cited)} citation keys, {len(missing)} without an entry in {bib}")
    raise SystemExit(1 if missing else 0)


if __name__ == "__main__":
    import fire  # imported here so that the tests need only pytest

    fire.Fire({"expand": expand, "check": check, "keys": keys})
