"""Tests for the pure parts of ``scripts/connectivity.py``."""

from __future__ import annotations

from pathlib import Path
from typing import Any

import connectivity
import core


def decl(name: str, module: str, kind: str, **extra: Any) -> dict[str, Any]:
    """An index entry."""
    return {
        "name": name,
        "module": module,
        "kind": kind,
        "private": False,
        "typeUses": [],
        "uses": [],
        **extra,
    }


def test_core_is_what_the_root_file_lists(tmp_path: Path) -> None:
    """Folders alone decide nothing: a promoted catalogue module is core, and a module of a core
    folder that the root file does not list is not."""
    (tmp_path / "LeanDLRA.lean").write_text(
        "-- generated\nimport LeanDLRA.Analysis.Defs\n"
        "import LeanDLRA.OpenProblems.TensorNetworks.Part1Defs\n"
    )
    found = connectivity.core_set(tmp_path)
    assert found == frozenset(core.core_modules(tmp_path))
    assert "LeanDLRA.Analysis.Defs" in found
    assert (
        "LeanDLRA.OpenProblems.TensorNetworks.Part1Defs" in found
    )  # docs/promoted.txt
    assert "LeanDLRA.OpenProblems.TensorNetworks.Part3" not in found
    assert "LeanDLRA.Analysis.NotListed" not in found
    assert "LeanDLRA.Literature.Kinetic.P2101_12571a" not in found


def test_the_notion_of_core_of_the_repository_is_the_one_of_core_py() -> None:
    root = (
        connectivity.ROOT
        if (connectivity.ROOT / "LeanDLRA.lean").exists()
        else core.ROOT
    )
    assert connectivity.core_set(root) == frozenset(core.core_modules(root))
    assert connectivity.core_set(root)  # the root file lists modules


def test_areas() -> None:
    assert connectivity.area("LeanDLRA.Literature.Kinetic.P2101_12571a") == "Literature"
    assert connectivity.area("LeanDLRA.Defs") == "root"


CORE = frozenset(("LeanDLRA.Analysis.Defs", "LeanDLRA.OpenProblems.Promoted"))


def test_catalogue_connection() -> None:
    decls = [
        decl("C.norm", "LeanDLRA.Analysis.Defs", "def"),
        decl("C.thm", "LeanDLRA.Analysis.Defs", "theorem", typeUses=["C.norm"]),
        decl("P.rank", "LeanDLRA.OpenProblems.Promoted", "def"),
        # A: one statement in core terms, one in local terms, one in Mathlib terms.
        decl("A.loc", "LeanDLRA.Literature.A", "def"),
        decl("A.t1", "LeanDLRA.Literature.A", "theorem", typeUses=["C.norm", "A.loc"]),
        decl("A.t2", "LeanDLRA.Literature.A", "theorem", typeUses=["A.loc"]),
        decl("A.t3", "LeanDLRA.Literature.A", "theorem", typeUses=["Nat.add"]),
        # B: the core (a promoted module) appears only in a proof; the private theorem with a
        # core statement does not count as a statement.
        decl("B.t", "LeanDLRA.Literature.B", "theorem", uses=["P.rank"]),
        decl(
            "B.p",
            "LeanDLRA.Literature.B",
            "theorem",
            private=True,
            typeUses=["P.rank"],
            uses=["P.rank"],
        ),
        # C: standalone; it uses only a catalogue module.
        decl("D.t", "LeanDLRA.Novel.C", "theorem", typeUses=["A.loc"], uses=["A.loc"]),
        # D: the core only in the body of a definition.
        decl("E.d", "LeanDLRA.OpenProblems.D", "def", uses=["C.norm"]),
    ]
    got = connectivity.catalogue_connection(decls, CORE)
    assert sorted(got) == ["Literature", "Novel", "OpenProblems", "all"]
    lit = got["Literature"]
    assert (lit.modules, lit.stated, lit.used_only, lit.standalone) == (2, 1, 1, 0)
    assert (
        lit.theorems,
        lit.theorems_core,
        lit.theorems_local,
        lit.theorems_mathlib,
    ) == (
        4,
        1,
        1,
        2,
    )
    novel = got["Novel"]
    assert (novel.modules, novel.stated, novel.used_only, novel.standalone) == (
        1,
        0,
        0,
        1,
    )
    assert (novel.theorems, novel.theorems_core, novel.theorems_local) == (1, 0, 1)
    # The promoted module is core although its folder is a catalogue folder.
    op = got["OpenProblems"]
    assert (op.modules, op.stated, op.used_only, op.standalone) == (1, 0, 1, 0)
    total = got["all"]
    assert (total.modules, total.stated, total.used_only, total.standalone) == (
        4,
        1,
        2,
        1,
    )
    assert (
        total.theorems
        == total.theorems_core + total.theorems_local + total.theorems_mathlib
    )


def test_catalogue_connection_without_catalogue() -> None:
    decls = [decl("C.norm", "LeanDLRA.Analysis.Defs", "def")]
    assert connectivity.catalogue_connection(decls, CORE) == {}


def test_defs_rule_with_def_kinds() -> None:
    decls = [
        decl("LeanDLRA.ok", "LeanDLRA.Analysis.Defs", "def", defKind="def"),
        decl("LeanDLRA.bad", "LeanDLRA.Analysis.Gronwall", "def", defKind="def"),
        decl(
            "LeanDLRA.S", "LeanDLRA.Analysis.Gronwall", "structure", defKind="structure"
        ),
        decl("LeanDLRA.S.f", "LeanDLRA.Analysis.Gronwall", "def", defKind="projection"),
        decl("LeanDLRA.inst", "LeanDLRA.Analysis.Gronwall", "def", defKind="instance"),
        decl(
            "LeanDLRA.sc", "LeanDLRA.Analysis.Gronwall", "def", defKind="scopedInstance"
        ),
        decl("LeanDLRA.term", "LeanDLRA.Analysis.Gronwall", "def", defKind="notation"),
        decl(
            "LeanDLRA.thm", "LeanDLRA.Analysis.Gronwall", "theorem", defKind="theorem"
        ),
        decl("LeanDLRA.Examples.e", "LeanDLRA.Analysis.Gronwall", "def", defKind="def"),
        decl("LeanDLRA.cex", "LeanDLRA.Corrections.P1", "def", defKind="def"),
        {
            **decl("LeanDLRA.p", "LeanDLRA.Analysis.Gronwall", "def", defKind="def"),
            "private": True,
        },
    ]
    assert connectivity.defs_rule_violations(decls) == [
        ("LeanDLRA.bad", "def", "LeanDLRA.Analysis.Gronwall"),
        ("LeanDLRA.S", "structure", "LeanDLRA.Analysis.Gronwall"),
        ("LeanDLRA.inst", "instance", "LeanDLRA.Analysis.Gronwall"),
    ]


def test_defs_rule_without_def_kinds() -> None:
    decls = [
        decl("LeanDLRA.S", "LeanDLRA.Matrix.X", "structure"),
        decl("LeanDLRA.S.f", "LeanDLRA.Matrix.X", "def"),
        decl("LeanDLRA.S.g", "LeanDLRA.Matrix.Y", "def"),
        decl("LeanDLRA.thm", "LeanDLRA.Matrix.X", "theorem"),
    ]
    assert connectivity.defs_rule_violations(decls) == [
        ("LeanDLRA.S", "structure", "LeanDLRA.Matrix.X"),
        ("LeanDLRA.S.g", "def", "LeanDLRA.Matrix.Y"),
    ]
