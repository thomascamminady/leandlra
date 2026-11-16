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
