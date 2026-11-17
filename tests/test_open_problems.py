# Scope: both
"""Tests of ``open_problems.py`` (the generated index of open problems)."""

from __future__ import annotations

import json
from pathlib import Path

import open_problems as op
import pytest

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
        rec(2, "resolved in LeanDLRA", "A/B.lean: bar_baz"),
        rec(3, "partially addressed", None),
    ]
    (root / "docs" / "survey" / "open-problems.json").write_text(json.dumps(problems))
    (root / "docs" / "survey" / "open-xx.json").write_text(json.dumps([{}, {}]))
    (root / "docs" / "survey" / "synthesis.json").write_text(
        json.dumps({"open": [{"key": "xx", "category_title": "Topic XX"}]})
    )


INDEX: op.Index = {
    "foo": [("LeanDLRA.A.foo", "LeanDLRA.A.B")],
    "A.foo": [("LeanDLRA.A.foo", "LeanDLRA.A.B")],
    "LeanDLRA.A.foo": [("LeanDLRA.A.foo", "LeanDLRA.A.B")],
    "bar_baz": [("LeanDLRA.A.bar_baz", "LeanDLRA.A.B")],
}


def test_resolve_and_render_lean(tmp_path: Path) -> None:
    make_repo(tmp_path)
    assert op.resolve("bar_baz", INDEX, None) == ("LeanDLRA.A.bar_baz", "LeanDLRA.A.B")
    assert op.resolve("nope_x", INDEX, None) is None
    assert op.is_candidate("bar_baz") and not op.is_candidate("blocks")
    assert not op.is_candidate("t1") and not op.is_candidate("e.g")
    tally = op.Tally()
    text = op.render_lean(
        "A/B.lean: bar_baz, ghost_lemma (one case)", tmp_path, INDEX, tally
    )
    assert "[`bar_baz`](../LeanDLRA/A/B.lean)" in text
    assert "`ghost_lemma` (not in the library)" in text
    assert (tally.resolved, tally.unresolved) == (1, 1)


def test_proved_without_resolved_name(tmp_path: Path) -> None:
    make_repo(tmp_path)
    _, tally = op.render(tmp_path, {})
    assert tally.proved_without_name == ["OP-XX-02"]
    _, tally = op.render(tmp_path, INDEX)
    assert tally.proved_without_name == []


def test_render(tmp_path: Path) -> None:
    make_repo(tmp_path)
    page = op.render(tmp_path, INDEX)[0]
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
    assert op.render(tmp_path, INDEX)[0] == page


def test_committed_page_is_current() -> None:
    dump = op.default_dump()
    if not dump.exists():
        pytest.skip("no rolling dump")
    text, tally = op.render(op.ROOT, op.load_index(dump))
    assert op.PAGE.read_text(encoding="utf-8") == text
    assert not tally.proved_without_name
