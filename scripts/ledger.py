# /// script
# requires-python = ">=3.11"
# dependencies = ["fire"]
# ///
"""Generate ``docs/PROVEN.md`` and the status block of ``README.md`` from the Lean sources.

Each tracked module contributes its title (the first heading of the module docstring), its number
of theorems and definitions, and the arXiv ids it cites.  Paper titles come from
``docs/survey/papers.json`` and ``papers/catalogue.json``.  ``docs/ledger.json`` lists curated main
results with their source.

The status block has one line for the core library (the modules imported by ``LeanDLRA.lean``,
read with ``scripts/core.py``) and one line for the catalogue (the other tracked modules).

    uv run -q scripts/ledger.py
"""

from __future__ import annotations

import collections
import json
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import core

ROOT = Path(__file__).resolve().parent.parent
START, END = "<!-- status:start -->", "<!-- status:end -->"
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance)\b",
    re.MULTILINE,
)
ARXIV = re.compile(r"\b(\d{4}\.\d{4,5})\b")
SLICE = re.compile(r"P(\d{4})_(\d{4,5})[a-z]?\.lean$")
FOLDERS = {
    "Foundations": "Foundations",
    "Analysis": "Analysis",
    "LinearAlgebra": "Linear algebra",
    "Matrix": "Matrices",
    "Classical": "Classical matrix analysis",
    "FixedRank": "The fixed-rank manifold",
    "DLRA": "The DLRA problem",
    "Dynamics": "Dynamics",
    "Integrators": "Integrators",
    "HighOrder": "Integrators of higher order",
    "Randomized": "Randomized and interpolatory integrators",
    "Stiff": "Stiff problems",
    "Stability": "Stability and structure",
    "Tensor": "Tensors",
    "Training": "Low-rank training",
    "Stochastic": "Stochastic problems",
    "Filtering": "Filtering",
    "Kinetic": "Kinetic equations",
    "Control": "Optimal control",
    "Research": "Research",
    "OpenProblems": "Open problems of the survey",
    "Literature": "Published theorems",
    "Novel": "Novel results",
    "Corrections": "Corrections",
}


@dataclass(frozen=True)
class Module:
    """Summary of one Lean module."""

    path: str
    title: str
    theorems: int
    defs: int
    papers: tuple[str, ...]

    @property
    def folder(self) -> str:
        """Top folder below ``LeanDLRA/``."""
        parts = self.path.split("/")
        return parts[1] if len(parts) > 2 else "Other"


def tracked(root: Path = ROOT) -> list[str]:
    """Paths of all committed Lean modules of the library."""
    out = subprocess.run(
        ["git", "ls-files", "LeanDLRA"],
        cwd=root,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    return sorted(p for p in out.split() if p.endswith(".lean"))


def core_paths(root: Path = ROOT) -> frozenset[str]:
    """Paths of the modules of the core library: the imports of ``LeanDLRA.lean``."""
    return frozenset(
        core.source_of(module, Path()).as_posix() for module in core.core_modules(root)
    )


def summary(path: str, root: Path = ROOT) -> Module:
    """Title, counts and cited papers of one module."""
    text = (root / path).read_text(encoding="utf-8")
    title = re.search(r"/-!\s*\n#\s*(.+)", text)
    kinds = collections.Counter(m.group(1) for m in DECL.finditer(text))
    papers = set(ARXIV.findall(text))
    if slice_id := SLICE.search(path):
        papers.add(f"{slice_id.group(1)}.{slice_id.group(2)}")
    return Module(
        path=path,
        title=title.group(1).strip() if title else "",
        theorems=kinds["theorem"] + kinds["lemma"],
        defs=sum(kinds.values()) - kinds["theorem"] - kinds["lemma"],
        papers=tuple(sorted(papers)),
    )


def titles() -> dict[str, str]:
    """arXiv id → title, from the survey and the harvested catalogue."""
    table: dict[str, str] = {}
    for rel in ("papers/catalogue.json", "docs/survey/papers.json"):
        path = ROOT / rel
        if path.exists():
            for entry in json.loads(path.read_text(encoding="utf-8")):
                table[entry["id"]] = entry["title"]
    return table


def arxiv(paper: str) -> str:
    """Markdown link to a paper."""
    return f"[{paper}](https://arxiv.org/abs/{paper})"


def cell(text: str) -> str:
    """Escape a table cell."""
    return text.replace("|", "\\|").replace("\n", " ")


def module_table(mods: list[Module]) -> list[str]:
    """One table of modules."""
    rows = ["| Module | Content | Theorems | Sources |", "|---|---|---:|---|"]
    for mod in mods:
        name = mod.path.removeprefix("LeanDLRA/").removesuffix(".lean")
        papers = ", ".join(arxiv(p) for p in mod.papers)
        rows.append(
            f"| [`{name}`](../{mod.path}) | {cell(mod.title)} | {mod.theorems} | {papers} |"
        )
    return rows


def curated(entries: list[dict[str, Any]]) -> list[str]:
    """The curated main results, grouped by file."""
    rows = ["| Result | Lean | Source | File |", "|---|---|---|---|"]
    for entry in entries:
        names = ", ".join(f"`{n.strip()}`" for n in entry["lean_names"].split(",")[:3])
        rows.append(
            f"| {cell(entry['result'])} | {cell(names)} | {cell(entry['source'])} "
            f"| [`{entry['file']}`](../{entry['file']}) |"
        )
    return rows


def proven(
    mods: list[Module], ledger: list[dict[str, Any]], names: dict[str, str]
) -> str:
    """Text of docs/PROVEN.md; ``names`` gives the titles of the cited papers."""
    lines = [
        "# Proven",
        "",
        "Generated by `scripts/ledger.py`. Every module below builds with no `sorry`, no warnings and",
        "only the axioms `propext`, `Classical.choice` and `Quot.sound`.",
    ]
    groups: dict[str, list[Module]] = collections.defaultdict(list)
    for mod in mods:
        groups[mod.folder].append(mod)
    order = [f for f in FOLDERS if f in groups]
    order += sorted(set(groups) - set(FOLDERS))
    for folder in order:
        lines += ["", f"## {FOLDERS.get(folder, folder)}", ""]
        lines += module_table(groups[folder])
    lines += ["", "## Curated main results", ""]
    lines += curated(ledger)
    cited = sorted({p for mod in mods for p in mod.papers if p in names})
    lines += ["", "## Cited papers", ""]
    lines += [f"* {arxiv(p)}: {names[p]}" for p in cited]
    return "\n".join(lines) + "\n"


def count_line(label: str, mods: list[Module]) -> str:
    """One line of the status block: the counts of a list of modules."""
    papers = {p for mod in mods for p in mod.papers}
    return (
        f"* {label}: {len(mods)} modules, {sum(m.theorems for m in mods)} theorems and lemmas, "
        f"{len(papers)} papers cited by arXiv identifier."
    )


def status(mods: list[Module], core_files: frozenset[str]) -> str:
    """The README status block: one line for the core library and one for the catalogue."""
    lines = [
        count_line("Core library", [m for m in mods if m.path in core_files]),
        count_line("Catalogue", [m for m in mods if m.path not in core_files]),
    ]
    return f"{START}\n\n" + "\n".join(lines) + f"\n\n{END}"


def replace_status(text: str, block: str) -> str:
    """``text`` with the part between the two status marks replaced by ``block``."""
    head, rest = text.split(START, 1)
    _, tail = rest.split(END, 1)
    return head + block + tail


def main() -> None:
    """Rewrite docs/PROVEN.md and the status block of README.md."""
    mods = [summary(p) for p in tracked()]
    core_files = core_paths()
    ledger = json.loads((ROOT / "docs" / "ledger.json").read_text(encoding="utf-8"))
    (ROOT / "docs" / "PROVEN.md").write_text(
        proven(mods, ledger, titles()), encoding="utf-8"
    )
    readme = ROOT / "README.md"
    text = readme.read_text(encoding="utf-8")
    readme.write_text(replace_status(text, status(mods, core_files)), encoding="utf-8")
    in_core = sum(m.path in core_files for m in mods)
    print(f"{len(mods)} modules, {in_core} of them in the core library")


if __name__ == "__main__":
    import fire  # imported here so that the tests need only pytest

    fire.Fire(main)
