"""Tests of ``scripts/ledger.py`` (``docs/PROVEN.md`` and the status block of the README)."""

from __future__ import annotations

from pathlib import Path

import ledger

CORE = "LeanDLRA/Topic/Defs.lean"
PAPER = "LeanDLRA/Literature/Kinetic/P2412_05912a.lean"
CORE_TEXT = """/-!
# Topic: definitions

Follows arXiv 2010.02022.
-/

def double (x : Nat) : Nat := 2 * x

@[simp] theorem double_zero : double 0 = 0 := rfl

private lemma double_one : double 1 = 2 := rfl
"""
PAPER_TEXT = """/-!
# Results of a paper

See also arXiv 2010.02022 and arXiv 1301.1058.
-/

theorem one : 1 = 1 := rfl
"""


def tree(tmp_path: Path) -> Path:
    """A repository with one core module and one catalogue module."""
    for path, text in ((CORE, CORE_TEXT), (PAPER, PAPER_TEXT)):
        (tmp_path / path).parent.mkdir(parents=True)
        (tmp_path / path).write_text(text, encoding="utf-8")
    (tmp_path / "LeanDLRA.lean").write_text(
        "-- Generated.\nimport LeanDLRA.Topic.Defs\n", encoding="utf-8"
    )
    return tmp_path


def modules(root: Path) -> list[ledger.Module]:
    return [ledger.summary(path, root) for path in (CORE, PAPER)]


def test_summary_counts_declarations_and_papers(tmp_path: Path) -> None:
    core, paper = modules(tree(tmp_path))
    assert core == ledger.Module(CORE, "Topic: definitions", 2, 1, ("2010.02022",))
    assert core.folder == "Topic"
    assert paper.theorems == 1
    # the identifier in the name of a paper file counts as a cited paper
    assert paper.papers == ("1301.1058", "2010.02022", "2412.05912")
    assert paper.folder == "Literature"


def test_core_paths_are_the_imports_of_the_root_file(tmp_path: Path) -> None:
    assert ledger.core_paths(tree(tmp_path)) == frozenset({CORE})


def test_status_has_a_core_line_and_a_catalogue_line(tmp_path: Path) -> None:
    root = tree(tmp_path)
    block = ledger.status(modules(root), ledger.core_paths(root))
    assert block.split("\n") == [
        ledger.START,
        "",
        "* Core library: 1 modules, 2 theorems and lemmas, 1 papers cited by arXiv identifier.",
        "* Catalogue: 1 modules, 1 theorems and lemmas, 3 papers cited by arXiv identifier.",
        "",
        ledger.END,
    ]


def test_replace_status_keeps_the_rest_of_the_readme() -> None:
    text = f"# Title\n\n{ledger.START}\n\nold line\n\n{ledger.END}\n\nMore text.\n"
    block = f"{ledger.START}\n\nnew\n\n{ledger.END}"
    assert ledger.replace_status(text, block) == f"# Title\n\n{block}\n\nMore text.\n"


def test_proven_lists_modules_by_folder_and_the_curated_results(tmp_path: Path) -> None:
    entry = {
        "result": "Doubling | zero",
        "lean_names": "double_zero, a, b, c",
        "source": "[Author2020, Thm. 1]",
        "file": CORE,
    }
    names = {"2010.02022": "A paper"}
    lines = ledger.proven(modules(tree(tmp_path)), [entry], names).split("\n")
    # folders of the table `FOLDERS` first and in its order, the others after them by name
    assert [line for line in lines if line.startswith("## ")] == [
        "## Published theorems",
        "## Topic",
        "## Curated main results",
        "## Cited papers",
    ]
    assert (
        f"| [`Topic/Defs`](../{CORE}) | Topic: definitions | 2 "
        "| [2010.02022](https://arxiv.org/abs/2010.02022) |"
    ) in lines
    assert (
        "| Doubling \\| zero | `double_zero`, `a`, `b` | [Author2020, Thm. 1] "
        f"| [`{CORE}`](../{CORE}) |"
    ) in lines
    # only papers with a known title are listed
    assert lines[-2:] == [
        "* [2010.02022](https://arxiv.org/abs/2010.02022): A paper",
        "",
    ]
