# Scope: both
"""The two records of statements of the repository: core and catalogue.

``docs/statements.json`` (core) and ``docs/statements_catalogue.json`` (catalogue) share no name,
are written in the committed form of ``fidelity.record_text``, and together keep every entry of the
single record they were split from: same names, same hashes.
"""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

import fidelity
import pytest
import rolling

ROOT = Path(__file__).resolve().parent.parent


def git(*args: str) -> str | None:
    """Output of a git command in the repository, or None if it fails."""
    try:
        r = subprocess.run(
            ["git", *args], cwd=ROOT, capture_output=True, text=True, check=False
        )
    except OSError:
        return None
    return r.stdout if r.returncode == 0 else None


def test_records_are_disjoint_and_in_committed_form() -> None:
    parts = fidelity.read_records(ROOT)  # raises if a name is in both
    assert parts["core"] and parts["catalogue"]
    for part, table in parts.items():
        path = ROOT / fidelity.RECORDS[part]
        assert path.read_text(encoding="utf-8") == fidelity.record_text(table), path
        assert all(len(h) == 64 and int(h, 16) >= 0 for h in table.values())


def test_split_keeps_every_recorded_statement() -> None:
    """The union of the two records equals the single record before the split.

    The comparison is made at the commit that added the catalogue record, against its parent;
    before that commit exists (an uncommitted split), the working tree against ``HEAD``.
    """
    catalogue = fidelity.RECORDS["catalogue"]
    added = git("log", "--diff-filter=A", "--reverse", "--format=%H", "--", catalogue)
    if added is None:
        pytest.skip("no git history")
    if added.split():
        commit = added.split()[0]
        old_text = git("show", f"{commit}^:{fidelity.RECORDS['core']}")
        new = {
            part: git("show", f"{commit}:{name}")
            for part, name in fidelity.RECORDS.items()
        }
        if old_text is None or None in new.values():
            pytest.skip(f"history of {commit[:7]} not available")
        parts = {part: json.loads(text or "") for part, text in new.items()}
    else:
        if git("cat-file", "-e", f"HEAD:{catalogue}") is not None:
            pytest.skip("the catalogue record is in HEAD but was never added")
        old_text = git("show", f"HEAD:{fidelity.RECORDS['core']}")
        if old_text is None:
            pytest.skip("no record in HEAD")
        parts = fidelity.read_records(ROOT)
    old: dict[str, str] = json.loads(old_text)
    assert not set(parts["core"]) & set(parts["catalogue"])
    union = {**parts["core"], **parts["catalogue"]}
    assert sorted(union) == sorted(old)
    assert union == old
    assert fidelity.record_text(union) == old_text


def test_each_statement_is_in_the_record_of_its_library() -> None:
    """Against the rolling dump of the gate, where there is one (not in CI)."""
    record = ROOT / rolling.HASHDIR / rolling.STATEMENTS
    if not record.exists():
        pytest.skip(f"no rolling dump {record}")
    _, places, wrong = rolling.misplaced_records(ROOT, record, ROOT / fidelity.RENAMES)
    assert wrong == {}, "run: uv run -q scripts/rolling.py records --write"
    assert "unknown" not in places.values()
