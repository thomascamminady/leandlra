# Scope: core
"""Tests for ``scripts/core_checks.py`` (no Lean, no fire)."""

import gzip
import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
SCRIPTS = next(
    d
    for d in (HERE.parent / "scripts", HERE.parent.parent.parent / "scripts")
    if (d / "core_checks.py").exists()
)
sys.path.insert(0, str(SCRIPTS))
sys.path.insert(
    1,
    str(
        next(d for d in HERE.parents if (d / "scripts" / "core.py").exists())
        / "scripts"
    ),
)

import core_checks as cc


def test_definitions_in_a_source_text() -> None:
    text = """
namespace A.B
def f := 1
private def g := 2
noncomputable abbrev h := 3
scoped instance : Foo := ⟨⟩
instance : Foo := ⟨⟩
instance instBar : Bar := ⟨⟩
structure S where
  x : Nat
@[simp] protected def T.k := 4
section
class C (α : Type) where
end
namespace Examples
def data := 5
end Examples
end A.B
theorem t : True := trivial
-- def inLine := 1
/- def inBlock := 1 -/
def top := 6
"""
    got = [(k, n) for _, k, n in cc.definitions_in(text)]
    assert got == [
        ("def", "A.B.f"),
        ("abbrev", "A.B.h"),
        ("instance", "A.B.instance"),
        ("instance", "A.B.instBar"),
        ("structure", "A.B.S"),
        ("def", "A.B.T.k"),
        ("class", "A.B.C"),
        ("def", "top"),
    ]
    assert cc.definitions_in("-- c\n/- b\n-/\ndef x := 1\n")[0][0] == 4


def tree(root: Path, files: dict[str, str]) -> None:
    for rel, text in files.items():
        path = root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    modules = [r.removesuffix(".lean").replace("/", ".") for r in files]
    (root / "LeanDLRA.lean").write_text("".join(f"import {m}\n" for m in modules))


def test_defs_rule_on_core_files_only(tmp_path: Path) -> None:
    tree(
        tmp_path,
        {
            "LeanDLRA/Topic/Defs.lean": "def inDefs := 1\n",
            "LeanDLRA/Topic/Other.lean": "def outside := 1\ntheorem t : True := trivial\n",
            "LeanDLRA/Corrections/C.lean": "def exempt := 1\n",
        },
    )
    (tmp_path / "LeanDLRA/Catalogue.lean").write_text(
        "def notCore := 1\n"
    )  # not imported
    assert cc.defs_findings(tmp_path) == [("LeanDLRA.Topic.Other", 1, "def", "outside")]


def test_baseline_makes_old_findings_pass_and_new_ones_block(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    tree(tmp_path, {"LeanDLRA/T/A.lean": "def a := 1\n"})
    (tmp_path / "docs").mkdir()
    assert cc.run_defs(tmp_path, strict=False, list_all=False) == 1
    assert cc.run_baseline(tmp_path) == 0
    assert cc.run_defs(tmp_path, strict=False, list_all=False) == 0
    assert cc.run_defs(tmp_path, strict=True, list_all=False) == 1
    (tmp_path / "LeanDLRA/T/A.lean").write_text("def a := 1\nstructure N where\n")
    capsys.readouterr()
    assert cc.run_defs(tmp_path, strict=False, list_all=False) == 1
    out = capsys.readouterr().out
    assert "DEFS-RULE LeanDLRA.T.A:2: public structure N" in out
    assert "public def a" not in out


def write_record(root: Path, entries: list[tuple[str, str, str]]) -> None:
    path = root / cc.RECORD
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = [json.dumps({"format": "leandlra-hashdiff/1"})]
    lines += [json.dumps({"module": m, "name": n, "type": t}) for m, n, t in entries]
    with gzip.open(path, "wt", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")


def test_duplicate_statements_in_the_core(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    tree(tmp_path, {"LeanDLRA/T/A.lean": "", "LeanDLRA/T/B.lean": ""})
    (tmp_path / "docs").mkdir()
    write_record(
        tmp_path,
        [
            ("LeanDLRA.T.A", "LeanDLRA.A.one", "⊢ True"),
            ("LeanDLRA.T.B", "LeanDLRA.B.one", "⊢ True"),
            ("LeanDLRA.T.B", "LeanDLRA.B.two", "⊢ False"),
            ("LeanDLRA.Lit.X", "LeanDLRA.X.one", "⊢ True"),  # catalogue: ignored
        ],
    )
    assert cc.duplicate_groups(tmp_path) == [
        [("LeanDLRA.T.A", "LeanDLRA.A.one"), ("LeanDLRA.T.B", "LeanDLRA.B.one")]
    ]
    assert cc.run_duplicates(tmp_path, strict=False, list_all=False) == 1
    assert "DUPLICATE-STATEMENT LeanDLRA.A.one (LeanDLRA.T.A); LeanDLRA.B.one" in (
        capsys.readouterr().out
    )
    cc.run_baseline(tmp_path)
    assert cc.run_duplicates(tmp_path, strict=False, list_all=False) == 0
    assert cc.run_duplicates(tmp_path, strict=True, list_all=False) == 1


def test_duplicates_without_a_record_exit_2(tmp_path: Path) -> None:
    tree(tmp_path, {"LeanDLRA/T/A.lean": ""})
    assert cc.run_duplicates(tmp_path, strict=False, list_all=False) == 2


# -- vacuity --------------------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("head", "expected"),
    [
        ("(x : ℝ) (hx : 0 ≤ x) : 0 ≤ x ^ 2", True),
        ("{L : ℝ≥0} (hF : IsLipschitzField F L) : P", True),
        ("(sol : IsDLRASolution F Y) : P", True),
        ("(hf : Continuous f) : P", True),  # named like a hypothesis, not data
        ("{f : ℕ → ℝ} (hA : ∀ u v, ⟪A u, v⟫ = ⟪u, A v⟫) : P", True),
        ("(x : ℝ) : 0 ≤ x → 0 ≤ x ^ 3", True),
        ("(h : ℝ) (t : ℝ) : step h t = t + h", False),  # a step size called h
        ("{h : ℝ} (U : ∀ i, Matrix (ι i) (r i) ℝ) : P U", False),
        ("(V : Matrix (∀ k : {k // k ∉ τ.modes}, ι k) s ℝ) : Q V", False),
        ("[Fact (1 < p)] (x : ℝ) : ‖x‖ = |x|", False),
        ("(f : ℝ → ℝ) (g : (n : ℕ) → Fin n → ℝ) : (fun x => f x) = f", False),
        ("{x : ℝ≥0∞} : x ≤ ⊤", False),
        (": ∀ ε > 0, ∃ δ > 0, δ ≤ ε", False),
    ],
)
def test_has_hypotheses(head: str, expected: bool) -> None:
    assert cc.has_hypotheses(head) is expected


VACUITY = """
namespace LeanDLRA

/-- A docstring that mentions `witnessed_le` does not count. -/
theorem lonely_le {x : ℝ} (hx : 0 ≤ x) : x ≤ x + 1 := by linarith

theorem witnessed_le {x : ℝ} (hx : 0 ≤ x) :
    x ≤ 2 * x + 1 := by
  linarith

theorem dotted.lemma_le {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x := hx

theorem helper_le {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x := hx

theorem noHypotheses (x : ℝ) : x = x := rfl

private theorem hidden_le {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x := hx

example : (1 : ℝ) ≤ 2 * 1 + 1 := witnessed_le (by norm_num)

example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x := hx.dotted.lemma_le

section Examples

private theorem uses_helper : (0 : ℝ) ≤ 1 := helper_le (x := 1) (by norm_num)

theorem inExamples_le {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x := hx

end Examples

end LeanDLRA
"""


def test_unwitnessed_theorems_of_a_file() -> None:
    assert cc.unwitnessed(VACUITY) == [(5, "LeanDLRA.lonely_le")]
    witness, inside = cc.examples_of(VACUITY)
    assert "witnessed_le (by norm_num)" in witness
    assert "helper_le" in witness and 27 in inside
    assert cc.mentions("exact hP.of_global hL", "LeanDLRA.DLRAProblem.of_global")
    assert not cc.mentions("exact of_global₂", "LeanDLRA.DLRAProblem.of_global")
    assert not cc.mentions("exact not_of_global", "LeanDLRA.DLRAProblem.of_global")


def test_vacuity_ratchet_like_defs(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    tree(
        tmp_path, {"LeanDLRA/T/A.lean": VACUITY, "LeanDLRA/T/Defs.lean": "def d := 1\n"}
    )
    (tmp_path / "docs").mkdir()
    assert cc.vacuity_findings(tmp_path) == [("LeanDLRA.T.A", 5, "LeanDLRA.lonely_le")]
    assert cc.run_vacuity(tmp_path, strict=False, list_all=False) == 1
    assert "NO-EXAMPLE LeanDLRA.T.A:5: LeanDLRA.lonely_le has hypotheses" in (
        capsys.readouterr().out
    )
    assert cc.run_baseline(tmp_path, ["vacuity"]) == 0
    assert set(cc.read_baseline(tmp_path)) == {
        "vacuity"
    }  # --only: the others are not written
    assert cc.run_vacuity(tmp_path, strict=False, list_all=False) == 0
    assert cc.run_vacuity(tmp_path, strict=True, list_all=False) == 1
    (tmp_path / "LeanDLRA/T/A.lean").write_text(
        VACUITY + "\ntheorem LeanDLRA.more_le {x : ℝ} (hx : 0 < x) : 0 < x := hx\n"
    )
    capsys.readouterr()
    assert cc.run_vacuity(tmp_path, strict=False, list_all=False) == 1
    out = capsys.readouterr().out
    assert "LeanDLRA.more_le" in out and "lonely_le" not in out


def test_baseline_only_keeps_the_other_entries(tmp_path: Path) -> None:
    tree(tmp_path, {"LeanDLRA/T/A.lean": "def a := 1\n"})
    (tmp_path / "docs").mkdir()
    (tmp_path / cc.BASELINE).write_text(json.dumps({"defs": [], "duplicates": ["x=y"]}))
    assert cc.run_baseline(tmp_path, ["vacuity"]) == 0
    assert cc.read_baseline(tmp_path) == {
        "defs": [],
        "duplicates": ["x=y"],
        "vacuity": [],
    }
    # Without a record the duplicates entry stays.
    assert cc.run_baseline(tmp_path) == 0
    assert cc.read_baseline(tmp_path)["duplicates"] == ["x=y"]
    assert cc.read_baseline(tmp_path)["defs"] == ["LeanDLRA.T.A:a"]
    assert cc.run_baseline(tmp_path, ["nope"]) == 2
    assert cc.split_list(("a", "b,c")) == ["a", "b", "c"]
    assert cc.split_list("") == []


# -- mathlib and the ratchet ----------------------------------------------------------------------


def test_core_files_that_import_all_of_mathlib(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    tree(
        tmp_path,
        {
            "LeanDLRA/T/A.lean": "import Mathlib\n",
            "LeanDLRA/T/B.lean": "import Mathlib.Analysis.Normed.Group.Basic\n",
            "LeanDLRA/T/C.lean": "/- c -/\nimport LeanDLRA.T.B\nimport Mathlib\n",
        },
    )
    (tmp_path / "docs").mkdir()
    assert cc.mathlib_findings(tmp_path) == ["LeanDLRA.T.A", "LeanDLRA.T.C"]
    assert cc.run_mathlib(tmp_path, strict=False, list_all=False) == 1
    assert "IMPORT-MATHLIB LeanDLRA.T.A" in capsys.readouterr().out
    cc.run_baseline(tmp_path, ["mathlib"])
    assert cc.run_mathlib(tmp_path, strict=False, list_all=False) == 0


def test_ratchet_fails_only_on_growth(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    tree(tmp_path, {"LeanDLRA/T/A.lean": "def a := 1\ndef b := 2\n"})
    (tmp_path / "docs").mkdir()
    assert cc.run_ratchet(tmp_path) == 2  # no baseline entries
    assert "RATCHET defs: no baseline entry" in capsys.readouterr().out
    cc.run_baseline(tmp_path)
    assert set(cc.read_baseline(tmp_path)) == {"defs", "vacuity", "mathlib"}
    assert cc.run_ratchet(tmp_path) == 0
    out = capsys.readouterr().out
    assert "RATCHET defs: 2, baseline 2" in out
    assert "RATCHET duplicates: not measured" in out  # no record, as in CI
    # A finding replaced by another (a rename, a file move) is no growth.
    (tmp_path / "LeanDLRA/T/A.lean").write_text("def a := 1\ndef c := 2\n")
    assert cc.run_ratchet(tmp_path, ["defs"]) == 0
    (tmp_path / "LeanDLRA/T/A.lean").write_text("def a := 1\n")
    assert cc.run_ratchet(tmp_path, ["defs"]) == 0
    assert "1 fewer: the baseline can be rewritten" in capsys.readouterr().out
    (tmp_path / "LeanDLRA/T/A.lean").write_text("def a := 1\ndef b := 2\ndef d := 3\n")
    assert cc.run_ratchet(tmp_path, ["defs", "mathlib"]) == 1
    out = capsys.readouterr().out
    assert "RATCHET defs: 3, more than the 2 of the baseline" in out
    assert "RATCHET mathlib: 0, baseline 0" in out
    assert cc.run_ratchet(tmp_path, ["nope"]) == 2


def test_duplicates_are_counted_by_extra_copies_and_read_the_round(
    tmp_path: Path,
) -> None:
    tree(tmp_path, {"LeanDLRA/T/A.lean": "", "LeanDLRA/T/B.lean": ""})
    (tmp_path / "docs").mkdir()
    write_record(
        tmp_path,
        [
            ("LeanDLRA.T.A", "LeanDLRA.A.one", "⊢ True"),
            ("LeanDLRA.T.B", "LeanDLRA.B.one", "⊢ True"),
            ("LeanDLRA.T.B", "LeanDLRA.B.two", "⊢ False"),
        ],
    )
    cc.run_baseline(tmp_path, ["duplicates"])
    assert cc.count("duplicates", tmp_path) == 1
    assert cc.baseline_count("duplicates", ["a=b=c", "d=e"]) == 3
    # A running gate round: its statements replace those of its modules.
    path = tmp_path / cc.ROUND_RECORD
    header = {"format": "leandlra-hashdiff/1", "module_list": ["LeanDLRA.T.B"]}
    lines = [json.dumps(header)] + [
        json.dumps({"module": "LeanDLRA.T.B", "name": n, "type": "⊢ True"})
        for n in ("LeanDLRA.B.one", "LeanDLRA.B.two")
    ]
    with gzip.open(path, "wt", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")
    assert cc.count("duplicates", tmp_path) == 2
    assert cc.run_ratchet(tmp_path, ["duplicates"]) == 1
    path.unlink()
    assert cc.run_ratchet(tmp_path, ["duplicates"]) == 0
