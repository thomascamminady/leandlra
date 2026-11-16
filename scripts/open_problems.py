# /// script
# requires-python = ">=3.11"
# dependencies = ["fire"]
# ///
"""Index of the open problems (``docs/OPEN_PROBLEMS.md``).

Sources, all inside the repository:

* ``docs/survey/open-problems.json``: the merged list of open problems, one record per problem with
  a topic key, a status and a free-text pointer to the Lean declarations that bear on it;
* ``docs/survey/open-<topic>.json``: the raw extracted items of each topic (only counted here);
* ``docs/survey/synthesis.json``: the title of each topic;
* ``docs/references.bib``: the map from arXiv identifier to citation key;
* ``LeanDLRA/OpenProblems/**``: the module docstrings name the problems (``OP-XX-NN``) each module
  treats; the modules are linked from the problem;
* the ``## TODO`` sections of the core modules (those imported by ``LeanDLRA.lean``).

Status words: ``open``; ``partly`` (the survey says "partially addressed"); ``proved`` (the survey
says "resolved in LeanDLRA"), with the Lean names given in the survey.

Usage::

    uv run -q scripts/open_problems.py write    # writes docs/OPEN_PROBLEMS.md
    uv run -q scripts/open_problems.py check    # exit status 1 if the page is out of date
    uv run -q scripts/open_problems.py stats    # numbers by topic and status
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Any

import fire

ROOT: Path = Path(__file__).resolve().parent.parent
PAGE: Path = ROOT / "docs" / "OPEN_PROBLEMS.md"
STATUS_WORD: dict[str, str] = {
    "open": "open",
    "partially addressed": "partly",
    "resolved in LeanDLRA": "proved",
}
STATUS_ORDER: list[str] = ["proved", "partly", "open"]
MAX_STATEMENT: int = 230

_ID = re.compile(r"OP-[A-Z]+-\d+")
_PATH = re.compile(r"(?:LeanDLRA/)?[A-Za-z0-9_]+(?:/[A-Za-z0-9_]+)*\.lean")
_EPRINT = re.compile(r"eprint\s*=\s*\{([^}]*)\}")
_ENTRY = re.compile(r"^@\w+\{([^,\s]+),", re.MULTILINE)
_IMPORT = re.compile(r"^import (LeanDLRA\.\S+)", re.MULTILINE)


def load_json(root: Path, rel: str) -> Any:
    """Read a JSON file below ``root``."""
    return json.loads((root / rel).read_text(encoding="utf-8"))


def citation_keys(bib: str) -> dict[str, str]:
    """Map arXiv identifiers to BibTeX keys (first key wins)."""
    keys: dict[str, str] = {}
    for chunk in re.split(r"(?m)^(?=@)", bib):
        head = _ENTRY.match(chunk)
        eprint = _EPRINT.search(chunk)
        if head and eprint:
            keys.setdefault(eprint.group(1).strip(), head.group(1))
    return keys


def cite(paper: str, keys: dict[str, str]) -> str:
    """Citation key of an arXiv identifier, or ``arXiv:id`` when the bibliography lacks it."""
    return keys.get(paper, f"arXiv:{paper}")


def one_line(text: str, limit: int = MAX_STATEMENT) -> str:
    """Collapse whitespace and cut at a word boundary, with an ellipsis."""
    flat = " ".join(text.split())
    if len(flat) <= limit:
        return flat
    return flat[: limit - 1].rsplit(" ", 1)[0].rstrip(",;:") + "…"


def module_docs(root: Path) -> dict[str, list[str]]:
    """Map problem identifiers to the ``OpenProblems`` modules whose docstring names them."""
    found: dict[str, list[str]] = {}
    base = root / "LeanDLRA" / "OpenProblems"
    for path in sorted(base.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        match = re.search(r"/-!\s*\n#([^\n]*)", text)
        if not match:
            continue
        rel = path.relative_to(root).as_posix()
        for ident in _ID.findall(match.group(1)):
            found.setdefault(ident, []).append(rel)
    return found


def core_modules(root: Path) -> list[Path]:
    """Source files of the modules imported by ``LeanDLRA.lean``."""
    text = (root / "LeanDLRA.lean").read_text(encoding="utf-8")
    return [root / (m.replace(".", "/") + ".lean") for m in _IMPORT.findall(text)]


def todo_items(text: str) -> list[str]:
    """Items of the ``## TODO`` section of a module docstring (bullets or a paragraph)."""
    match = re.search(r"^## TODO[ \t]*\n(.*?)(?=^#|-/)", text, re.MULTILINE | re.DOTALL)
    if not match:
        return []
    body = match.group(1).strip()
    if not body:
        return []
    parts = re.split(r"(?m)^[*-] ", body)
    return [" ".join(p.split()) for p in parts if p.strip()]


def core_todos(root: Path) -> dict[str, list[tuple[str, str]]]:
    """Core ``## TODO`` items grouped by top-level folder: ``(file, item)`` pairs."""
    grouped: dict[str, list[tuple[str, str]]] = {}
    for path in core_modules(root):
        if not path.exists():
            continue
        rel = path.relative_to(root).as_posix()
        for item in todo_items(path.read_text(encoding="utf-8")):
            parts = Path(rel).parts
            topic = parts[1] if len(parts) > 2 else "(top level)"
            grouped.setdefault(topic, []).append((rel, item))
    return {k: grouped[k] for k in sorted(grouped)}


def linkify(text: str, root: Path) -> str:
    """Turn ``.lean`` paths that exist into links (relative to ``docs/``); mark names as code."""

    def repl(m: re.Match[str]) -> str:
        rel = m.group(0)
        full = rel if rel.startswith("LeanDLRA/") else "LeanDLRA/" + rel
        if (root / full).exists():
            return f"[`{rel}`](../{full})"
        return f"`{rel}`"

    return _PATH.sub(repl, text)


def render(root: Path = ROOT) -> str:
    """The page, as text."""
    problems: list[dict[str, Any]] = load_json(root, "docs/survey/open-problems.json")
    synthesis: dict[str, Any] = load_json(root, "docs/survey/synthesis.json")
    titles: dict[str, str] = {o["key"]: o["category_title"] for o in synthesis["open"]}
    keys = citation_keys((root / "docs" / "references.bib").read_text(encoding="utf-8"))
    modules = module_docs(root)
    todos = core_todos(root)

    raw: dict[str, int] = {}
    for path in sorted((root / "docs" / "survey").glob("open-*.json")):
        topic = path.stem.removeprefix("open-")
        if topic != "problems":
            raw[topic] = len(json.loads(path.read_text(encoding="utf-8")))

    by_topic: dict[str, list[dict[str, Any]]] = {}
    for p in problems:
        by_topic.setdefault(p["category_key"], []).append(p)

    def status(p: dict[str, Any]) -> str:
        return STATUS_WORD.get(p["status"], "open")

    total: dict[str, int] = {s: 0 for s in STATUS_ORDER}
    for p in problems:
        total[status(p)] += 1

    out: list[str] = [
        "# Open problems",
        "",
        "Generated by `scripts/open_problems.py` from `docs/survey/*.json`, the `OpenProblems`",
        "module docstrings and the `## TODO` sections of the core modules. Do not edit by hand.",
        "",
        (
            f"The survey lists {len(problems)} problems in {len(by_topic)} topics: "
            f"{total['proved']} proved, {total['partly']} partly addressed, {total['open']} open. "
            "A status is the survey's; `proved` and `partly` come with the Lean names the survey "
            "gives, and the other problems may list declarations that serve as building blocks. "
            "Papers are cited by key (`docs/references.bib`); an identifier of the form `arXiv:id` "
            "is a paper that has no key yet."
        ),
        "",
        "## Topics",
        "",
        "| Topic | Problems | Proved | Partly | Open | Raw items |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    order = [k for k in titles if k in by_topic] + sorted(set(by_topic) - set(titles))
    for k in order:
        c = {s: sum(1 for p in by_topic[k] if status(p) == s) for s in STATUS_ORDER}
        out.append(
            f"| [{k}](#{k}) | {len(by_topic[k])} | {c['proved']} | {c['partly']} | {c['open']} "
            f"| {raw.get(k, 0)} |"
        )
    out += [""]
    for k in order:
        out += [f"## {k}", "", titles.get(k, k) + ".", ""]
        out += [
            "| Id | Statement | Status | Source | Lean |",
            "|---|---|---|---|---|",
        ]
        items = sorted(
            by_topic[k],
            key=lambda p: (STATUS_ORDER.index(status(p)), p["priority"], p["id"]),
        )
        for p in items:
            src = ", ".join(dict.fromkeys(cite(s["paper"], keys) for s in p["sources"]))
            lean = linkify(p.get("lean_ref") or "", root).replace("|", "\\|")
            mods = ", ".join(
                f"[`{Path(m).name}`](../{m})" for m in modules.get(p["id"], [])
            )
            cell = "; ".join(
                x for x in (lean, ("modules: " + mods) if mods else "") if x
            )
            title = one_line(p["title"]).replace("|", "\\|")
            out.append(f"| {p['id']} | {title} | {status(p)} | {src} | {cell} |")
        out.append("")
    out += ["## Gaps recorded in the core library", ""]
    out += [
        "Each item is a `## TODO` entry of a core module docstring.",
        "",
    ]
    for topic, items in todos.items():
        out += [f"### {topic}", ""]
        for rel, item in items:
            out.append(f"* [`{rel.removeprefix('LeanDLRA/')}`](../{rel}): {item}")
        out.append("")
    return "\n".join(out).rstrip("\n") + "\n"


class Cli:
    """Command line entry points."""

    def write(self) -> None:
        """Write ``docs/OPEN_PROBLEMS.md``."""
        text = render()
        PAGE.write_text(text, encoding="utf-8")
        print(f"wrote {PAGE.relative_to(ROOT)} ({len(text.splitlines())} lines)")

    def check(self) -> None:
        """Exit with status 1 if the page differs from what the sources produce."""
        if not PAGE.exists() or PAGE.read_text(encoding="utf-8") != render():
            print(
                "docs/OPEN_PROBLEMS.md is out of date: run make docs", file=sys.stderr
            )
            sys.exit(1)
        print("docs/OPEN_PROBLEMS.md is up to date")

    def stats(self) -> None:
        """Print the number of problems by topic and status."""
        problems: list[dict[str, Any]] = load_json(
            ROOT, "docs/survey/open-problems.json"
        )
        table: dict[tuple[str, str], int] = {}
        for p in problems:
            key = (p["category_key"], STATUS_WORD.get(p["status"], "open"))
            table[key] = table.get(key, 0) + 1
        for (topic, st), n in sorted(table.items()):
            print(f"{topic:18s} {st:8s} {n}")


if __name__ == "__main__":
    fire.Fire(Cli)
