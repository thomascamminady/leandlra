"""Tests for scripts/core.py (the core/catalogue rule)."""

from __future__ import annotations

from pathlib import Path

import core


def write(root: Path, module: str, text: str) -> None:
    path = core.source_of(module, root)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def test_header_imports_reads_only_the_header() -> None:
    text = (
        "/- Copyright, with a line\nimport Not.This\n /- nested -/ -/\n"
        "-- import Nor.This\n"
        "module\n"
        "import Mathlib.Data.Real.Basic\n"
        "public import LeanDLRA.A.B\n"
        "meta import LeanDLRA.A.C\n"
        "import all LeanDLRA.A.D\n"
        "\n"
        "/-- A docstring.\nimport LeanDLRA.Not.AnImport\n-/\n"
        "theorem t : True := trivial\n"
        "import LeanDLRA.Too.Late\n"
    )
    assert core.header_imports(text) == [
        "Mathlib.Data.Real.Basic",
        "LeanDLRA.A.B",
        "LeanDLRA.A.C",
        "LeanDLRA.A.D",
    ]


def test_header_imports_of_empty_and_comment_only_files() -> None:
    assert core.header_imports("") == []
    assert core.header_imports("-- nothing\n/- open comment") == []


def test_core_modules_reads_the_generated_root(tmp_path: Path) -> None:
    (tmp_path / "LeanDLRA.lean").write_text(
        "-- Generated\n-- second line\nimport LeanDLRA.A\nimport LeanDLRA.B.C\n"
    )
    assert core.core_modules(tmp_path) == ["LeanDLRA.A", "LeanDLRA.B.C"]


def test_violations_finds_imports_that_leave_the_core(tmp_path: Path) -> None:
    (tmp_path / "LeanDLRA.lean").write_text(
        "import LeanDLRA.Core.A\nimport LeanDLRA.Core.B\nimport LeanDLRA.Literature.Promoted\n"
    )
    write(
        tmp_path,
        "LeanDLRA.Core.A",
        "import Mathlib\nimport LeanDLRA.Literature.Promoted\n",
    )
    write(
        tmp_path,
        "LeanDLRA.Core.B",
        "import LeanDLRA.Core.A\nimport LeanDLRA.Literature.Paper\n",
    )
    write(
        tmp_path, "LeanDLRA.Literature.Promoted", "import LeanDLRA.OpenProblems.Defs\n"
    )
    write(tmp_path, "LeanDLRA.Literature.Paper", "import LeanDLRA.Core.A\n")
    write(tmp_path, "LeanDLRA.OpenProblems.Defs", "")
    assert core.violations(tmp_path) == [
        ("LeanDLRA.Core.B", "LeanDLRA.Literature.Paper"),
        ("LeanDLRA.Literature.Promoted", "LeanDLRA.OpenProblems.Defs"),
    ]
    assert core.all_modules(tmp_path) == [
        "LeanDLRA.Core.A",
        "LeanDLRA.Core.B",
        "LeanDLRA.Literature.Paper",
        "LeanDLRA.Literature.Promoted",
        "LeanDLRA.OpenProblems.Defs",
    ]


def test_no_violation_when_the_core_is_closed(tmp_path: Path) -> None:
    (tmp_path / "LeanDLRA.lean").write_text(
        "import LeanDLRA.Core.A\nimport LeanDLRA.Core.B\n"
    )
    write(tmp_path, "LeanDLRA.Core.A", "import Mathlib\n")
    write(
        tmp_path,
        "LeanDLRA.Core.B",
        "import LeanDLRA.Core.A\n\ntheorem t : True := trivial\n",
    )
    write(tmp_path, "LeanDLRA.Literature.Paper", "import LeanDLRA.Core.B\n")
    assert core.violations(tmp_path) == []
