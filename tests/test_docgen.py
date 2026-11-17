# Scope: both
"""Tests of ``scripts/docgen.py`` (pages that quote Lean statements)."""

from __future__ import annotations

from collections.abc import Iterable
from pathlib import Path

import docgen
import pytest

FILE = "LeanDLRA/Topic/Defs.lean"
SOURCE = """/-
Copyright …
-/
import Mathlib.Data.Real.Basic

/-!
# Topic

Follows [Author2020, Thm. 1] and [Other1999].
-/

namespace LeanDLRA

/-- The double of `x`. -/
def double (x : ℝ) : ℝ :=
  2 * x

/-- A pair of numbers. -/
structure Pair where
  /-- The first number. -/
  fst : ℝ
  /-- The second number. -/
  snd : ℝ

/-- Doubling is additive. -/
theorem double_add (x y : ℝ)
    (h : 0 ≤ x) :
    double (x + y) = double x + double y := by
  unfold double
  ring

theorem default_arg (x : ℝ := 0) : -- not the end := of the statement
    double x = 2 * x := rfl

theorem foo : double 0 = 0 := by simp [double]

namespace Other

theorem foo (x : ℝ) : double x = x + x := by
  unfold double; ring

end Other

example : double 1 = 2 := by norm_num [double]

example (x : ℝ) (hx : x = 1) :
    double x = 2 := by
  subst hx; norm_num [double]

def notKey : List ℕ := [Code2020]

end LeanDLRA
"""
TEMPLATE = f"""# Page

Compared at commit @commit; the core has @coremodules modules. See @file({FILE}).

| Name | Place |
|---|---|
| `double` | @loc({FILE} double) |

@stmt {FILE} double_add double_add

@full {FILE} foo#2 Other.foo

@ex {FILE} 2

@lines README.txt 1 2

The definition `double` and the structure `Pair`.
"""


def tree(tmp_path: Path) -> Path:
    """A repository with a core of one module."""
    (tmp_path / "LeanDLRA" / "Topic").mkdir(parents=True)
    (tmp_path / FILE).write_text(SOURCE, encoding="utf-8")
    (tmp_path / "LeanDLRA.lean").write_text(
        "import LeanDLRA.Topic.Defs\n", encoding="utf-8"
    )
    (tmp_path / "README.txt").write_text("one\ntwo\nthree\n", encoding="utf-8")
    return tmp_path


def line_of(text: str) -> int:
    """The number of the line of ``SOURCE`` that starts with ``text``."""
    return next(
        i for i, line in enumerate(SOURCE.split("\n"), 1) if line.startswith(text)
    )


@pytest.fixture
def no_git(monkeypatch: pytest.MonkeyPatch) -> list[set[str]]:
    """Replace the two functions that call git; the result collects the files asked for."""
    asked: list[set[str]] = []

    def unchanged(root: Path, files: Iterable[str]) -> list[str]:
        asked.append(set(files))
        return []

    monkeypatch.setattr(docgen, "changed_files", unchanged)
    monkeypatch.setattr(docgen, "head_commit", lambda root: "abc1234 (2026-01-02)")
    return asked


def test_name_with_universe_list(tmp_path: Path) -> None:
    file = "LeanDLRA/Topic/Universe.lean"
    (tmp_path / "LeanDLRA" / "Topic").mkdir(parents=True)
    (tmp_path / file).write_text(
        "theorem poly.{u} (α : Type u) :\n    Nonempty (α → α) := ⟨id⟩\n\n"
        "theorem poly' : True := trivial\n",
        encoding="utf-8",
    )
    st = docgen.find(tmp_path, file, "poly")
    assert (st.start, st.end) == (1, 2)
    assert st.text == "theorem poly.{u} (α : Type u) :\n    Nonempty (α → α)"
    assert docgen.find(tmp_path, file, "poly'").start == 4


def test_theorem_is_cut_before_its_proof(tmp_path: Path) -> None:
    st = docgen.find(tree(tmp_path), FILE, "double_add")
    assert st.kind == "theorem"
    assert st.start == line_of("theorem double_add")
    assert st.end == st.start + 2
    assert st.text.endswith("double (x + y) = double x + double y")
    assert ":=" not in st.text


def test_assignment_in_brackets_or_comments_is_not_the_end(tmp_path: Path) -> None:
    st = docgen.find(tree(tmp_path), FILE, "default_arg")
    assert st.text.endswith("double x = 2 * x")
    assert "(x : ℝ := 0)" in st.text


def test_definitions_and_structures_are_quoted_completely(tmp_path: Path) -> None:
    root = tree(tmp_path)
    assert docgen.find(root, FILE, "double").text.endswith("2 * x")
    pair = docgen.find(root, FILE, "Pair")
    assert pair.kind == "structure"
    assert pair.text.endswith("snd : ℝ")


def test_full_keeps_the_proof(tmp_path: Path) -> None:
    st = docgen.find(tree(tmp_path), FILE, "double_add", whole=True)
    assert st.text.endswith("ring")


def test_a_name_declared_twice_needs_its_number(tmp_path: Path) -> None:
    root = tree(tmp_path)
    with pytest.raises(SystemExit, match="declared 2 times"):
        docgen.find(root, FILE, "foo")
    assert docgen.find(root, FILE, "foo", 1).text == "theorem foo : double 0 = 0"
    assert docgen.find(root, FILE, "foo", 2).start == line_of("theorem foo (x")
    with pytest.raises(SystemExit, match="not found"):
        docgen.find(root, FILE, "missing")


def test_examples_are_counted(tmp_path: Path) -> None:
    st = docgen.find(tree(tmp_path), FILE, "example", 2)
    assert st.start == line_of("example (x : ℝ)")
    assert st.text.endswith("double x = 2")


def test_where_ends_a_statement() -> None:
    code = "instance : Inhabited Pair where\n  default := ⟨0, 0⟩"
    assert code[docgen.statement_end(code, 0) :].startswith("where")


def test_inline_directives(tmp_path: Path, no_git: list[set[str]]) -> None:
    root = tree(tmp_path)
    quoted: set[str] = set()
    n = line_of("def double")
    assert docgen.expand_line(root, f"@loc({FILE} double)", "../", quoted) == [
        f"[Topic/Defs.lean:{n}](../{FILE}#L{n})"
    ]
    assert quoted == {FILE}
    assert docgen.expand_line(root, f"@file({FILE})", "../", quoted) == [
        f"[`Topic/Defs.lean`](../{FILE})"
    ]
    with pytest.raises(FileNotFoundError):
        docgen.expand_line(root, "@file(LeanDLRA/No.lean)", "../", quoted)
    assert docgen.expand_line(root, "at @commit, @coremodules modules", "", quoted) == [
        "at abc1234 (2026-01-02), 1 modules"
    ]
    assert quoted == {FILE, "LeanDLRA.lean"}


def test_block_directives(tmp_path: Path) -> None:
    root = tree(tmp_path)
    quoted: set[str] = set()
    a = line_of("theorem double_add")
    lines = docgen.expand_line(
        root, f"@stmt {FILE} double_add double_add", "../", quoted
    )
    assert (
        lines[0]
        == f"`double_add` in [`{FILE}`, lines {a}–{a + 2}](../{FILE}#L{a}-L{a + 2}):"
    )
    assert lines[1:4] == ["", "```lean", "theorem double_add (x y : ℝ)"]
    assert lines[-1] == "```"
    text = docgen.expand_line(root, "@lines README.txt 1 2", "../", quoted)
    assert text == [
        "[`README.txt`, lines 1–2](../README.txt#L1-L2):",
        "",
        "```text",
        "one",
        "two",
        "```",
    ]
    assert quoted == {FILE, "README.txt"}


def test_quote_finds_lines_by_their_text(tmp_path: Path) -> None:
    root = tree(tmp_path)
    quoted: set[str] = set()
    assert docgen.lines_between(root, "README.txt", "^two$", "") == (2, 2)
    assert docgen.lines_between(root, "README.txt", "^one", "^t") == (1, 2)
    text = docgen.expand_line(root, "@quote README.txt ^one$ || ^thr", "../", quoted)
    assert text[0] == "[`README.txt`, lines 1–3](../README.txt#L1-L3):"
    assert text[2:] == ["```text", "one", "two", "three", "```"]
    one = docgen.expand_line(root, "@quote README.txt ^two$", "../", quoted)
    assert one[0] == "[`README.txt`, line 2](../README.txt#L2):"
    assert quoted == {"README.txt"}
    with pytest.raises(SystemExit, match="2 lines match"):
        docgen.lines_between(root, "README.txt", "^t", "")
    with pytest.raises(SystemExit, match="no line from line 3"):
        docgen.lines_between(root, "README.txt", "three", "one")


def test_expand_and_check(tmp_path: Path, no_git: list[set[str]]) -> None:
    root = tree(tmp_path)
    template, page = root / "template.md", root / "docs" / "PAGE.md"
    template.write_text(TEMPLATE, encoding="utf-8")
    docgen.expand(str(template), str(page), root=str(root))
    assert no_git == [{FILE, "LeanDLRA.lean", "README.txt"}]
    text = page.read_text(encoding="utf-8")
    assert "commit abc1234 (2026-01-02); the core has 1 modules" in text
    names = docgen.load_names(root)
    messages, bad = docgen.check_page(root, names, str(page), False)
    assert bad == 0
    # the spans are counted once each: two names, two paths, `Other.foo`, `README.txt`, `Pair`
    assert messages == [f"{page}: 4 quoted blocks, 7 backticked spans, 0 problems"]
    with pytest.raises(SystemExit) as done:
        docgen.check(str(page), root=str(root))
    assert done.value.code == 0


def test_check_finds_a_stale_block_and_an_unknown_name(
    tmp_path: Path, no_git: list[set[str]]
) -> None:
    root = tree(tmp_path)
    template, page = root / "template.md", root / "docs" / "PAGE.md"
    template.write_text(TEMPLATE + "\nThe lemma `double_sub`.\n", encoding="utf-8")
    docgen.expand(str(template), str(page), root=str(root))
    changed = SOURCE.replace("(h : 0 ≤ x) :", "(h : 0 < x) :")
    (root / FILE).write_text(changed, encoding="utf-8")
    messages, bad = docgen.check_page(root, docgen.load_names(root), str(page), False)
    a = line_of("theorem double_add")
    assert bad == 2
    assert f"{page}: `double_sub` not found in the core" in messages
    assert any(m.endswith(f"block differs from {FILE}:{a}-{a + 2}") for m in messages)
    with pytest.raises(SystemExit) as done:
        docgen.check(str(page), root=str(root))
    assert done.value.code == 1


def test_check_compares_table_rows_with_their_lines(tmp_path: Path) -> None:
    root = tree(tmp_path)
    n = line_of("def double")
    good = f"| `double` | [Topic/Defs.lean:{n}](../{FILE}#L{n}) |"
    bad = f"| `double` | [Topic/Defs.lean:{n + 1}](../{FILE}#L{n + 1}) |"
    assert docgen.check_row(root, "PAGE.md", 7, good) == []
    assert docgen.check_row(root, "PAGE.md", 7, bad) == [
        f"PAGE.md:7: `double` is not declared at {FILE}:{n + 1}"
    ]


def test_expand_refuses_files_that_differ_from_head(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    root = tree(tmp_path)
    template, page = root / "template.md", root / "docs" / "PAGE.md"
    template.write_text(f"@stmt {FILE} double_add double_add\n", encoding="utf-8")
    monkeypatch.setattr(docgen, "changed_files", lambda root, files: [f" M {FILE}"])
    with pytest.raises(SystemExit) as done:
        docgen.expand(str(template), str(page), root=str(root))
    assert done.value.code == 2
    assert not page.exists()
    assert f" M {FILE}" in capsys.readouterr().err


def test_changed_files_asks_git_only_for_files(monkeypatch: pytest.MonkeyPatch) -> None:
    calls: list[tuple[str, ...]] = []

    def fake(root: Path, *args: str) -> str:
        calls.append(args)
        return " M b.lean\n?? a.lean\n"

    monkeypatch.setattr(docgen, "git", fake)
    assert docgen.changed_files(Path("."), []) == []
    assert calls == []
    assert docgen.changed_files(Path("."), ["b.lean", "a.lean", "b.lean"]) == [
        " M b.lean",
        "?? a.lean",
    ]
    assert calls == [("status", "--porcelain", "--", "a.lean", "b.lean")]


def test_citation_keys(tmp_path: Path) -> None:
    root = tree(tmp_path)
    page = root / "PAGE.md"
    page.write_text(
        "See [Third2001; Author2020] and [a link](x.md).\n", encoding="utf-8"
    )
    assert "Code2020" not in docgen.comment_text(SOURCE)
    assert docgen.cited_keys(root, [str(page)]) == {
        "Author2020": [FILE],
        "Other1999": [FILE],
        "Third2001": [str(page)],
    }
    bib = root / "docs" / "references.bib"
    bib.parent.mkdir()
    bib.write_text(
        "@article{Author2020,\n  title = {T},\n}\n\n@book{ Third2001 ,\n}\n",
        encoding="utf-8",
    )
    assert docgen.bib_keys(bib.read_text(encoding="utf-8")) == {
        "Author2020",
        "Third2001",
    }
    assert docgen.missing_keys(root, [str(page)], "docs/references.bib") == {
        "Other1999": [FILE]
    }
    with pytest.raises(SystemExit) as done:
        docgen.keys(str(page), root=str(root))
    assert done.value.code == 1


def test_without_the_record_dotted_names_are_found_in_the_core_text(
    tmp_path: Path,
) -> None:
    text = "namespace LeanDLRA\n\ntheorem HasLocalError.of_tubeExt : True := trivial\n"
    names = docgen.Names(frozenset(), frozenset(), {}, text)
    for span in ("HasLocalError.of_tubeExt", "LeanDLRA.HasLocalError.of_tubeExt"):
        assert docgen.check_span(tmp_path, names, span, False) == ("", False)
    assert docgen.check_span(tmp_path, names, "Other.of_tubeExtra", False) == (
        "`Other.of_tubeExtra` not found in the core",
        True,
    )
    message, error = docgen.check_span(tmp_path, names, "Missing.of_tube", True)
    assert error and "not found" in message
