"""Tests for the pure parts of ``scripts/connectivity.py``."""

from __future__ import annotations

from typing import Any

import connectivity


def decl(name: str, module: str, kind: str, **extra: Any) -> dict[str, Any]:
    """An index entry."""
    return {"name": name, "module": module, "kind": kind, "private": False, **extra}


def test_core_areas() -> None:
    assert connectivity.is_core("LeanDLRA.LinearAlgebra.Frobenius.Defs")
    assert connectivity.is_core("LeanDLRA.Foundations.ODE")
    assert connectivity.is_core("LeanDLRA.Filtering.KalmanBucy")
    assert connectivity.is_core("LeanDLRA.Defs")
    assert not connectivity.is_core("LeanDLRA.Literature.Kinetic.P2101_12571a")
    assert not connectivity.is_core("LeanDLRA.References.CerutiLubich2022")
    assert not connectivity.is_core("LeanDLRA.Unknown.X")


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
