"""Tests for the pure parts of ``scripts/fidelity.py``."""

from __future__ import annotations

import json
from pathlib import Path

import fidelity
import pytest

A = "LeanDLRA.Old.a"
B = "LeanDLRA.New.b"
C = "LeanDLRA.c"
OLD = f"[u_1] ⊢ forall {{x : Type.{{u_1}}}}, ({A}.{{u_1}} x) -> ({A}.{{u_1}} x) -> Real"
NEW = f"[u_1] ⊢ forall {{x : Type.{{u_1}}}}, ({B}.{{u_1}} x) -> ({B}.{{u_1}} x) -> Real"


def check(
    recorded: dict[str, str], proved: dict[str, str], renames: dict[str, str]
) -> tuple[int, int, list[str]]:
    """Run the check with a generous cap."""
    return fidelity.check(recorded, proved, renames, 1 << 12)


def test_exact_match() -> None:
    assert check({"LeanDLRA.t": fidelity.sha256(OLD)}, {"LeanDLRA.t": OLD}, {}) == (
        1,
        0,
        [],
    )


def test_changed_and_missing_statements_fail() -> None:
    recorded = {"LeanDLRA.t": fidelity.sha256(OLD), "LeanDLRA.u": fidelity.sha256(OLD)}
    exact, via, problems = check(recorded, {"LeanDLRA.t": NEW}, {})
    assert (exact, via) == (0, 0)
    assert problems == ["differs: LeanDLRA.t", "missing: LeanDLRA.u"]


def test_match_through_renamed_constants() -> None:
    recorded = {"LeanDLRA.t": fidelity.sha256(OLD)}
    assert check(recorded, {"LeanDLRA.t": NEW}, {A: B}) == (0, 1, [])


def test_renamed_theorem() -> None:
    recorded = {"LeanDLRA.t": fidelity.sha256(OLD)}
    assert check(
        recorded, {"LeanDLRA.t_new": NEW}, {A: B, "LeanDLRA.t": "LeanDLRA.t_new"}
    ) == (
        0,
        1,
        [],
    )
    _, _, problems = check(recorded, {}, {"LeanDLRA.t": "LeanDLRA.t_new"})
    assert problems == ["missing: LeanDLRA.t (renamed to LeanDLRA.t_new)"]


def test_rename_does_not_excuse_other_changes() -> None:
    recorded = {"LeanDLRA.t": fidelity.sha256(OLD)}
    changed = NEW.replace("Real", "Nat")
    _, via, problems = check(recorded, {"LeanDLRA.t": changed}, {A: B})
    assert via == 0 and problems == ["differs: LeanDLRA.t"]


def test_new_type_still_using_an_old_name_fails() -> None:
    mixed = OLD.replace(f"({A}.{{u_1}} x) -> Real", f"({B}.{{u_1}} x) -> Real")
    recorded = {"LeanDLRA.t": fidelity.sha256(OLD)}
    assert check(recorded, {"LeanDLRA.t": mixed}, {A: B})[2] == ["differs: LeanDLRA.t"]


def test_merge_into_an_existing_constant() -> None:
    # A and C were duplicates; A is merged into C. The recorded type mentions both.
    old = f"[] ⊢ Eq.{{1}} Nat {A} {C}"
    new = f"[] ⊢ Eq.{{1}} Nat {C} {C}"
    recorded = {"LeanDLRA.t": fidelity.sha256(old)}
    assert check(recorded, {"LeanDLRA.t": new}, {A: C}) == (0, 1, [])


def test_candidates_respect_the_cap() -> None:
    text = " ".join([B] * 20)
    assert len(list(fidelity.candidates(text, {A: B}, 1 << 12))) == 2
    assert list(fidelity.candidates(text, {A: B, C: B}, 2)) == []


def test_load_renames_follows_chains(tmp_path: Path) -> None:
    path = tmp_path / "renames.json"
    assert fidelity.load_renames(path) == {}
    path.write_text(json.dumps({A: B, B: C, C: C}))
    assert fidelity.load_renames(path) == {A: C, B: C}
    path.write_text(json.dumps({A: B, B: A}))
    with pytest.raises(SystemExit):
        fidelity.load_renames(path)
