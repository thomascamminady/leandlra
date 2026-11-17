# Scope: core
"""Tests of ``definitions.py`` (the index of the definitions of the core library)."""

from __future__ import annotations

from pathlib import Path

import definitions

SOURCE = """/-
Copyright …
-/
import Mathlib

/-!
# A module

The word def inside a module docstring is not a declaration.
-/

namespace LeanDLRA

/-- A set, e.g. the tube. The second sentence. -/
def tube (ρ : ℝ) : Set ℝ := {x | x ≤ ρ}

-- def commented : ℕ := 0

section Inner

/-- A step relation `M t₀ t₁ Y₀ Y₁` ([Key2022, Thm. 2]): it relates
two states. More text. -/
structure Step where
  /-- A field. -/
  size : ℝ

def bare : ℕ := 0

/-- A private helper. -/
private def helper : ℕ := 1

end Inner

namespace Frobenius

/-- An instance with a name. -/
noncomputable scoped instance (priority := high) uniform : Inhabited ℕ := ⟨0⟩

/-- The string "def fake" is not a declaration. -/
@[simp] noncomputable def _root_.LeanDLRA.message : String := "def fake : ℕ"

@[deprecated (since := "2026-11-09")] alias old := Frobenius.tube

end Frobenius

end LeanDLRA
"""


def tree(tmp_path: Path) -> Path:
    """A repository with one core module."""
    (tmp_path / "LeanDLRA" / "Topic").mkdir(parents=True)
    (tmp_path / "LeanDLRA.lean").write_text(
        "import LeanDLRA.Topic.Defs\n", encoding="utf-8"
    )
    (tmp_path / "LeanDLRA" / "Topic" / "Defs.lean").write_text(SOURCE, encoding="utf-8")
    return tmp_path


def test_first_sentence_stops_at_the_first_full_stop() -> None:
    assert definitions.first_sentence("A set. More.") == "A set."


def test_first_sentence_skips_abbreviations_and_brackets() -> None:
    doc = "The bound of [Key2022, Thm. 2] holds, i.e. it is true. Next."
    assert (
        definitions.first_sentence(doc)
        == "The bound of [Key2022, Thm. 2] holds, i.e. it is true."
    )


def test_first_sentence_skips_periods_in_code_and_joins_lines() -> None:
    doc = "The lemma `Foo.bar` shows\n`a.b`. Second.\n\nSecond paragraph."
    assert definitions.first_sentence(doc) == "The lemma `Foo.bar` shows `a.b`."


def test_first_sentence_without_period_returns_the_paragraph() -> None:
    assert definitions.first_sentence("The formula:\n\n  x = y") == "The formula:"


def test_blank_comments_keeps_offsets_and_collects_docstrings() -> None:
    text = 'a /- x /- y -/ z -/ b\n/-- doc -/ def c := "def d" -- def e\n'
    code, docs = definitions.blank_comments(text)
    assert len(code) == len(text)
    assert code.count("\n") == text.count("\n")
    assert "def d" not in code and "def e" not in code and "def c" in code
    assert [d[2].strip() for d in docs] == ["doc"]


def test_core_modules(tmp_path: Path) -> None:
    assert definitions.core_modules(tree(tmp_path)) == ["LeanDLRA.Topic.Defs"]


def test_scan_finds_names_kinds_lines_and_docstrings(tmp_path: Path) -> None:
    found = {d.name: d for d in definitions.scan("LeanDLRA.Topic.Defs", tree(tmp_path))}
    assert set(found) == {
        "LeanDLRA.tube",
        "LeanDLRA.Step",
        "LeanDLRA.bare",
        "LeanDLRA.helper",
        "LeanDLRA.Frobenius.uniform",
        "LeanDLRA.message",
        "LeanDLRA.Frobenius.old",
    }
    tube = found["LeanDLRA.tube"]
    assert (tube.kind, tube.folder, tube.file) == (
        "def",
        "Topic",
        "LeanDLRA/Topic/Defs.lean",
    )
    assert (
        tube.line
        == SOURCE.splitlines().index("def tube (ρ : ℝ) : Set ℝ := {x | x ≤ ρ}") + 1
    )
    assert tube.summary == "A set, e.g. the tube."
    step = found["LeanDLRA.Step"]
    assert step.kind == "structure"
    assert step.summary.startswith("A step relation") and step.summary.endswith(
        "two states."
    )
    assert not found["LeanDLRA.bare"].documented
    assert found["LeanDLRA.helper"].private
    assert found["LeanDLRA.Frobenius.uniform"].kind == "instance"
    alias = found["LeanDLRA.Frobenius.old"]
    assert (alias.kind, alias.deprecated, alias.target) == (
        "alias",
        True,
        "Frobenius.tube",
    )


def test_render_lists_undocumented_definitions_and_aliases(tmp_path: Path) -> None:
    root = tree(tmp_path)
    page = definitions.render(definitions.scan_all(root), 1)
    assert (
        "The core has 1 modules with 4 definitions (1 of them without a docstring)"
        in page
    )
    assert "| `LeanDLRA.tube` | def | [Topic/Defs.lean:" in page
    assert "LeanDLRA.helper" not in page
    assert "LeanDLRA.Frobenius.uniform" not in page
    undocumented = page.split("## Definitions without a docstring")[1]
    assert "`LeanDLRA.bare`" in undocumented.split("## Deprecated aliases")[0]
    assert "| `LeanDLRA.Frobenius.old` | `Frobenius.tube` |" in page
