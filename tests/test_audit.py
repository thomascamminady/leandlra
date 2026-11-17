# Scope: both
"""scripts/audit.sh with a fake `lake`: the ratchet switch (AUDIT_RATCHETS)."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
from pathlib import Path

import pytest

SCRIPTS = Path(__file__).resolve().parent.parent / "scripts"
FAKE_LAKE = """#!/usr/bin/env bash
echo "lake $*" >> "$LAKE_LOG"
if [ "$1" = env ]; then echo "AUDIT OK: 1 constants in 1 LeanDLRA modules"; fi
exit 0
"""

pytestmark = pytest.mark.skipif(
    shutil.which("bash") is None or shutil.which("uv") is None,
    reason="needs bash and uv",
)


def make_tree(root: Path, baseline_defs: list[str]) -> dict[str, str]:
    """A repository with the audit, the core checks, one core file, a baseline; the env."""
    (root / "scripts").mkdir()
    for name in ("audit.sh", "core_checks.py", "core.py", "private_dups.py"):
        shutil.copy(SCRIPTS / name, root / "scripts" / name)
    (root / "LeanDLRA/T").mkdir(parents=True)
    (root / "LeanDLRA/T/A.lean").write_text("def a := 1\ndef b := 2\n")
    (root / "LeanDLRA.lean").write_text("import LeanDLRA.T.A\n")
    (root / "docs").mkdir()
    baseline = {"defs": baseline_defs, "vacuity": [], "mathlib": []}
    (root / "docs/core_checks_baseline.json").write_text(json.dumps(baseline))
    bin_dir = root / "bin"
    bin_dir.mkdir()
    (bin_dir / "lake").write_text(FAKE_LAKE)
    (bin_dir / "lake").chmod(0o755)
    env = {k: v for k, v in os.environ.items() if not k.startswith("AUDIT_RATCHET")}
    env["PATH"] = f"{bin_dir}{os.pathsep}{env['PATH']}"
    env["LAKE_LOG"] = str(root / "lake.log")
    return env


def audit(root: Path, env: dict[str, str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["bash", "scripts/audit.sh"],
        cwd=root,
        env=env,
        capture_output=True,
        text=True,
        timeout=300,
        check=False,
    )


def test_ratchets_are_off_by_default(tmp_path: Path) -> None:
    env = make_tree(
        tmp_path, ["LeanDLRA.T.A:a"]
    )  # one definition more than the baseline
    result = audit(tmp_path, env)
    assert result.returncode == 0, result.stdout + result.stderr
    assert "RATCHET" not in result.stdout
    assert "audited targets: LeanDLRA" in result.stdout


def test_growth_fails_the_audit_before_the_build(tmp_path: Path) -> None:
    env = make_tree(tmp_path, ["LeanDLRA.T.A:a"])
    result = audit(tmp_path, {**env, "AUDIT_RATCHETS": "1"})
    assert result.returncode == 1
    assert "RATCHET defs: 2, more than the 1 of the baseline" in result.stdout
    assert "AUDIT FAIL: ratchet" in result.stdout
    assert not (tmp_path / "lake.log").exists()  # nothing was built


def test_ratchets_within_the_baseline_and_selected_checks(tmp_path: Path) -> None:
    env = make_tree(tmp_path, ["LeanDLRA.T.A:a", "LeanDLRA.T.A:b"])
    result = audit(tmp_path, {**env, "AUDIT_RATCHETS": "1"})
    assert result.returncode == 0, result.stdout + result.stderr
    assert "RATCHET defs: 2, baseline 2" in result.stdout
    assert "RATCHET duplicates: no baseline entry" not in result.stdout  # not measured
    assert "lake build LeanDLRA" in (tmp_path / "lake.log").read_text()
    # The gate leaves the duplicates out; a check without a baseline entry fails.
    picked = {**env, "AUDIT_RATCHETS": "1", "AUDIT_RATCHET_CHECKS": "defs,mathlib"}
    result = audit(tmp_path, picked)
    assert result.returncode == 0
    assert "duplicates" not in result.stdout
    (tmp_path / "docs/core_checks_baseline.json").write_text(json.dumps({"defs": []}))
    result = audit(tmp_path, {**picked, "AUDIT_RATCHET_CHECKS": "mathlib"})
    assert result.returncode == 1
    assert "RATCHET mathlib: no baseline entry" in result.stdout
