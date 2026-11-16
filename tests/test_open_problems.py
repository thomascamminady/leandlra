"""Tests of ``open_problems.py`` (the generated index of open problems)."""

from __future__ import annotations

import json
from pathlib import Path

import open_problems as op

BIB = """@article{AliceBob2020,
  eprint = {2001.00001},
}

@misc{Carol2021,
  eprint = {2102.00002},
}
"""


def test_citation_keys_and_fallback() -> None:
    keys = op.citation_keys(BIB)
    assert keys == {"2001.00001": "AliceBob2020", "2102.00002": "Carol2021"}
    assert op.cite("2001.00001", keys) == "AliceBob2020"
    assert op.cite("9999.99999", keys) == "arXiv:9999.99999"


def test_one_line_cuts_at_word() -> None:
    assert op.one_line("a  b\nc") == "a b c"
    cut = op.one_line("word " * 100, 20)
    assert len(cut) <= 20 and cut.endswith("…")


def test_todo_items() -> None:
    text = "/-!\n# T\n\n## TODO\n\n* first\n  item\n* second\n\n## Other\n-/\n"
    assert op.todo_items(text) == ["first item", "second"]
    assert op.todo_items("/-!\n## TODO\n\nOne paragraph.\n-/") == ["One paragraph."]
    assert op.todo_items("/-!\n# T\n-/") == []


def make_repo(root: Path) -> None:
    (root / "docs" / "survey").mkdir(parents=True)
    (root / "LeanDLRA" / "OpenProblems").mkdir(parents=True)
    (root / "LeanDLRA" / "A").mkdir(parents=True)
    (root / "docs" / "references.bib").write_text(BIB)
    (root / "LeanDLRA.lean").write_text("import LeanDLRA.A.B\n")
    (root / "LeanDLRA" / "A" / "B.lean").write_text(
        "/-!\n# B\n\n## TODO\n\n* do it\n-/\n"
    )
    (root / "LeanDLRA" / "OpenProblems" / "M.lean").write_text(
        "/-!\n# Open problems OP-XX-01\n-/\n"
    )

    def rec(i: int, status: str, ref: str | None) -> dict[str, object]:
        r: dict[str, object] = {
            "id": f"OP-XX-0{i}",
            "title": f"Problem {i}",
            "statement": "s",
            "sources": [{"paper": "2001.00001", "location": "x"}],
            "status": status,
            "priority": i,
            "category_key": "xx",
        }
        if ref is not None:
            r["lean_ref"] = ref
        return r

    problems = [
        rec(1, "open", "building blocks: LeanDLRA/A/B.lean foo"),
        rec(2, "resolved in LeanDLRA", "A/B.lean: bar"),
        rec(3, "partially addressed", None),
    ]
    (root / "docs" / "survey" / "open-problems.json").write_text(json.dumps(problems))
    (root / "docs" / "survey" / "open-xx.json").write_text(json.dumps([{}, {}]))
    (root / "docs" / "survey" / "synthesis.json").write_text(
        json.dumps({"open": [{"key": "xx", "category_title": "Topic XX"}]})
    )


def test_render(tmp_path: Path) -> None:
    make_repo(tmp_path)
    page = op.render(tmp_path)
    assert "1 proved, 1 partly addressed, 1 open" in page
    assert "| [xx](#xx) | 3 | 1 | 1 | 1 | 2 |" in page
    rows = [ln for ln in page.splitlines() if ln.startswith("| OP-XX")]
    assert [r.split("|")[1].strip() for r in rows] == [
        "OP-XX-02",
        "OP-XX-03",
        "OP-XX-01",
    ]
    assert "AliceBob2020" in rows[0]
    assert "[`A/B.lean`](../LeanDLRA/A/B.lean)" in rows[0]
    assert "modules: [`M.lean`](../LeanDLRA/OpenProblems/M.lean)" in rows[2]
    assert "* [`A/B.lean`](../LeanDLRA/A/B.lean): do it" in page
    assert op.render(tmp_path) == page


def test_committed_page_is_current() -> None:
    assert op.PAGE.read_text(encoding="utf-8") == op.render()
