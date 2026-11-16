"""Tests for the summary of ``scripts/lint_core.py`` (no Lean)."""

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(
    0, str(next(d for d in (HERE.parent / "scripts",) if (d / "lint_core.py").exists()))
)
import lint_core

SAMPLE = """x.lean:9:0: error: -- Found 3 errors in 900 declarations (plus 40 automatically generated ones) in LeanDLRA with 15 linters

/- The `unusedArguments` linter reports:
UNUSED ARGUMENTS -/
-- LeanDLRA.A.B
#check LeanDLRA.f /- argument 3 h unused -/
#check LeanDLRA.g /- argument 1 x unused -/

/- The `simpNF` linter reports:
SOME SIMP LEMMAS ARE NOT IN SIMP-NORMAL FORM. -/
-- LeanDLRA.C
#check LeanDLRA.h /- bad -/
"""


def test_summary_counts_per_linter_and_file() -> None:
    out = lint_core.summarize(SAMPLE).splitlines()
    assert out[0].startswith("-- Found 3 errors in 900 declarations")
    assert "unusedArguments: 2" in out and "simpNF: 1" in out
    assert "        2  LeanDLRA.A.B" in out


def test_summary_of_a_clean_run() -> None:
    text = "-- Found 0 errors in 9 declarations (plus 1 automatically generated ones) x\n-- All linting checks passed!"
    assert lint_core.summarize(text).splitlines()[-1] == "no finding"
