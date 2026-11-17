# Scope: both
"""The workflows that the pipeline relies on, read as text (no YAML parser, no GitHub)."""

from __future__ import annotations

import re
from pathlib import Path

import gate

REPO = Path(__file__).resolve().parent.parent
WORKFLOWS = REPO / ".github" / "workflows"


def text(name: str) -> str:
    return (WORKFLOWS / name).read_text(encoding="utf-8")


def test_promotion_is_switched_off_and_only_fast_forwards() -> None:
    promote = text("promote.yml")
    assert 'workflows: ["Lean Action CI"]' in promote
    assert re.search(
        r"^name: Lean Action CI$", text("lean_action_ci.yml"), re.MULTILINE
    )
    assert "branches: [staging]" in promote
    for guard in (
        "vars.STAGING_PROMOTE == '1'",
        "github.event.workflow_run.conclusion == 'success'",
        "github.event.workflow_run.event == 'push'",
        "github.event.workflow_run.head_branch == 'staging'",
    ):
        assert guard in promote
    assert "--force" not in promote and "+$SHA" not in promote
    assert 'git push origin "$SHA:refs/heads/main"' in promote
    assert "git merge-base --is-ancestor origin/main" in promote


def test_promotion_starts_the_workflows_that_a_push_to_main_starts() -> None:
    started = re.findall(r"for workflow in ([\w. ]+); do", text("promote.yml"))[
        0
    ].split()
    on_main = sorted(
        p.name
        for p in WORKFLOWS.glob("*.yml")
        if re.search(r"push:\n\s+branches: \[main\]", p.read_text(encoding="utf-8"))
        and p.name != "docs_check.yml"  # it runs on pushes to staging already
    )
    assert sorted(started) == on_main
    for name in started:
        assert "workflow_dispatch:" in text(name)


def test_core_workflow_runs_on_every_branch_and_passes_the_ratchet_switch() -> None:
    ci = text("lean_action_ci.yml")
    assert re.search(
        r"^on:\n  push:\n", ci, re.MULTILINE
    )  # no branch filter: staging too
    assert "AUDIT_RATCHETS: ${{ vars.AUDIT_RATCHETS }}" in ci
    assert 'if [ "$GITHUB_REF_NAME" = staging ]; then base=$(last staging); fi' in ci


def test_docs_check_runs_the_make_target() -> None:
    assert "run: make docs-check" in text("docs_check.yml")
    assert re.search(r"^docs-check:", (REPO / "Makefile").read_text(), re.MULTILINE)


def test_gate_pushes_without_force() -> None:
    for branch in ("main", "staging"):
        command = gate.push_command(branch)
        assert command[-1] == f"HEAD:{branch}"
        assert not any(c.startswith(("-f", "--force", "+")) for c in command)
