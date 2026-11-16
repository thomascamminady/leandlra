"""Tests for ``scripts/private_dups.py`` and its call in ``scripts/audit.sh`` (no Lean is
started: ``lake`` is a stand-in that fails, which ends the audit after the warning)."""

import os
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPTS = next(
    d
    for d in (HERE.parent / "scripts", HERE.parent.parent.parent / "scripts")
    if (d / "private_dups.py").exists()
)
sys.path.insert(0, str(SCRIPTS))

import private_dups


def test_names_are_qualified_by_the_open_namespaces() -> None:
    text = """
namespace A.B
private def f := 1
section
@[simp] private lemma g : True := trivial
end
protected private theorem h : True := trivial
private def _root_.top := 2
end A.B
private def outside := 3
private noncomputable def C.d := 4
"""
    assert private_dups.private_names(text) == [
        "A.B.f",
        "A.B.g",
        "A.B.h",
        "top",
        "outside",
        "C.d",
    ]


def test_comments_and_public_declarations_are_ignored() -> None:
    text = """
/-- docs
private def inDocstring := 1 -/
-- private def inLine := 1
/- block
private def inBlock := 1
-/
def publicDef := 1
theorem private_looking : True := trivial
"""
    assert private_dups.private_names(text) == []


def write(root: Path, rel: str, text: str) -> None:
    (root / rel).parent.mkdir(parents=True, exist_ok=True)
    (root / rel).write_text(text)


def test_duplicates_need_two_modules_and_the_same_qualified_name(
    tmp_path: Path,
) -> None:
    lib = tmp_path / "LeanDLRA"
    write(
        lib,
        "X.lean",
        "namespace N\nprivate lemma helper := 1\nprivate lemma helper2 := 1\nend N\n",
    )
    write(lib, "Y.lean", "namespace N\nprivate lemma helper := 2\nend N\n")
    write(lib, "Z.lean", "namespace M\nprivate lemma helper := 3\nend M\n")
    write(
        lib, "W.lean", "private def once := 1\nprivate def once := 2\n"
    )  # one module only
    assert private_dups.duplicates(lib) == {
        "N.helper": ["LeanDLRA/X.lean", "LeanDLRA/Y.lean"]
    }


def test_command_line_warns_and_strict_fails(tmp_path: Path) -> None:
    lib = tmp_path / "LeanDLRA"
    write(lib, "X.lean", "private lemma t := 1\n")
    write(lib, "Y.lean", "private lemma t := 2\n")
    run = ["uv", "run", "-q", str(SCRIPTS / "private_dups.py"), str(lib)]
    res = subprocess.run(run, capture_output=True, text=True, check=False)
    assert res.returncode == 0
    assert "AUDIT WARN: private name t is defined in 2 modules" in res.stdout
    res = subprocess.run(
        [*run, "--strict"], capture_output=True, text=True, check=False
    )
    assert res.returncode == 1


def test_audit_prints_the_warning_before_the_build(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    (root / "scripts").mkdir(parents=True)
    (root / "bin").mkdir()
    for name in ("audit.sh", "private_dups.py"):
        shutil.copy(SCRIPTS / name, root / "scripts" / name)
    write(root, "LeanDLRA/X.lean", "private lemma t := 1\n")
    write(root, "LeanDLRA/Y.lean", "private lemma t := 2\n")
    (root / "bin" / "lake").write_text(
        "#!/usr/bin/env bash\necho fake lake >&2\nexit 1\n"
    )
    (root / "bin" / "lake").chmod(0o755)
    env = {**os.environ, "PATH": f"{root / 'bin'}:{os.environ['PATH']}"}
    res = subprocess.run(
        ["bash", str(root / "scripts" / "audit.sh")],
        capture_output=True,
        text=True,
        check=False,
        env=env,
        cwd=root,
    )
    out = res.stdout + res.stderr
    assert "AUDIT WARN: private name t is defined in 2 modules" in out
    assert out.index("AUDIT WARN") < out.index("AUDIT FAIL: build")
    assert res.returncode == 1
    # Without a duplicate there is no warning.
    write(root, "LeanDLRA/Y.lean", "private lemma u := 2\n")
    res = subprocess.run(
        ["bash", str(root / "scripts" / "audit.sh")],
        capture_output=True,
        text=True,
        check=False,
        env=env,
        cwd=root,
    )
    assert "AUDIT WARN" not in res.stdout + res.stderr
