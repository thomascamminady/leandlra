"""Tests for ``scripts/fc`` and ``scripts/warm.sh`` with stand-ins for ``lake`` and
``memory_pressure`` (no Lean is started)."""

import os
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
SCRIPTS = next(
    d
    for d in (HERE.parent / "scripts", HERE.parent.parent.parent / "scripts")
    if (d / "fc").exists()
)
LAKEFILE = """name = "Demo"

[leanOptions]
pp.unicode.fun = true # pretty-prints
relaxedAutoImplicit = false
maxSynthPendingDepth = 3

[[lean_lib]]
name = "LeanDLRA"
"""
FAKE_LAKE = """#!/usr/bin/env bash
printf '%s\\n' "$*" >> "$FAKE_LOG"
last="${@: -1}"
cp "$last" "$FAKE_LOG.checked"
sed "s|@FILE@|$last|g" "$FAKE_OUT"
exit "$(cat "$FAKE_CODE")"
"""
FAKE_MEMORY = """#!/usr/bin/env bash
echo "The system has 17179869184 (1048576 pages with a page size of 16384)."
cat "$FAKE_FREE"
"""


@dataclass
class Repo:
    """A stand-in repository with stand-ins for ``lake`` and ``memory_pressure``."""

    root: Path
    env: dict[str, str]

    @property
    def log(self) -> Path:
        return self.root / "lake.log"

    def set(self, out: str = "", code: int = 0, free: int | None = 60) -> None:
        (self.root / "fake.out").write_text(out)
        (self.root / "fake.code").write_text(str(code))
        line = "" if free is None else f"System-wide memory free percentage: {free}%\n"
        (self.root / "fake.free").write_text(line)

    def run(self, script: str, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["bash", str(self.root / "scripts" / script), *args],
            cwd=self.root,
            env=self.env,
            capture_output=True,
            text=True,
            check=False,
        )

    def tree(self, below: str) -> list[tuple[str, float]]:
        return sorted(
            (str(p.relative_to(self.root)), p.stat().st_mtime)
            for p in (self.root / below).rglob("*")
        )


@pytest.fixture
def repo(tmp_path: Path) -> Repo:
    root = tmp_path / "repo"
    (root / "scripts").mkdir(parents=True)
    (root / "bin").mkdir()
    (root / ".lake" / "build" / "lib" / "lean").mkdir(parents=True)
    (root / ".lake" / "build" / "marker").write_text("x")
    for name in ("fc", "warm.sh"):
        shutil.copy(SCRIPTS / name, root / "scripts" / name)
    (root / "scripts" / "axiom_check.lean").write_text("#eval axiomCheck\n")
    (root / "lakefile.toml").write_text(LAKEFILE)
    (root / "lean-toolchain").write_text("leanprover/lean4:test\n")
    (root / "A.lean").write_text("import Mathlib\n\ntheorem a : True := trivial\n")
    for name, text in (("lake", FAKE_LAKE), ("memory_pressure", FAKE_MEMORY)):
        (root / "bin" / name).write_text(text)
        (root / "bin" / name).chmod(0o755)
    env = {
        "PATH": f"{root / 'bin'}:{os.environ['PATH']}",
        "FAKE_LOG": str(root / "lake.log"),
        "FAKE_OUT": str(root / "fake.out"),
        "FAKE_CODE": str(root / "fake.code"),
        "FAKE_FREE": str(root / "fake.free"),
    }
    out = Repo(root, env)
    out.set()
    return out


def test_clean_file_is_ok_and_gets_the_package_options(repo: Repo) -> None:
    before = repo.tree(".lake/build")
    res = repo.run("fc", "A.lean")
    assert res.returncode == 0, res.stdout + res.stderr
    assert res.stdout.startswith("OK [A.lean]")
    assert repo.log.read_text().strip() == (
        "env lean -j2 -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false "
        f"-DmaxSynthPendingDepth=3 {repo.root.resolve() / 'A.lean'}"
    )
    # The file itself is checked, with its own imports; nothing is written into `.lake/build`.
    assert Path(f"{repo.log}.checked").read_text() == (repo.root / "A.lean").read_text()
    assert repo.tree(".lake/build") == before
    assert not (repo.root / ".lake" / "warm" / "slots" / "fc1").exists()


def test_warning_and_error_fail(repo: Repo) -> None:
    repo.set(out="@FILE@:3:8: warning: unused variable `h`\n")
    res = repo.run("fc", "A.lean")
    assert res.returncode == 1
    assert "WARN [A.lean]" in res.stdout
    assert res.stdout.startswith("A.lean:3:8: warning: unused variable")
    repo.set(out="@FILE@:3:8: error: unsolved goals\n", code=1)
    res = repo.run("fc", "A.lean")
    assert res.returncode == 1
    assert "FAIL [A.lean]" in res.stdout


@pytest.mark.parametrize(
    ("free", "args", "started"),
    [
        (34, [], False),
        (35, [], True),
        (49, ["--min-free=50"], False),
        (50, ["--min-free=50"], True),
        (5, ["--min-free=0"], True),
        (None, [], False),
        (None, ["--min-free=0"], True),
    ],
)
def test_memory_threshold(
    repo: Repo, free: int | None, args: list[str], started: bool
) -> None:
    repo.set(free=free)
    res = repo.run("fc", *args, "A.lean")
    assert repo.log.exists() == started
    assert res.returncode == (0 if started else 3)
    assert ("NOT STARTED [A.lean]" in res.stdout) != started
    assert not (repo.root / ".lake" / "warm" / "slots" / "fc1").exists()


def test_threshold_from_the_environment(repo: Repo) -> None:
    repo.set(free=40)
    repo.env["FC_MIN_FREE"] = "45"
    assert repo.run("fc", "A.lean").returncode == 3
    assert repo.run("fc", "--min-free=40", "A.lean").returncode == 0


def test_import_without_olean_is_reported_and_nothing_is_built(repo: Repo) -> None:
    repo.set(
        out="@FILE@:1:0: error: object file '/x/.lake/build/lib/lean/B.olean' of module B "
        "does not exist\n",
        code=1,
    )
    before = repo.tree(".lake/build")
    res = repo.run("fc", "A.lean")
    assert res.returncode == 4
    assert "NO OLEAN [A.lean]" in res.stdout
    assert (
        repo.log.read_text().count("\n") == 1
    )  # one call of `lake env lean`, no build
    assert "build" not in repo.log.read_text().split(str(repo.root.resolve()))[0]
    assert repo.tree(".lake/build") == before


def test_axioms_checks_a_copy_and_reports_under_the_name_of_the_file(
    repo: Repo,
) -> None:
    repo.set(out="@FILE@:3:0: error: AXIOM-CHECK FAIL: #[(a, sorryAx)]\n")
    source = (repo.root / "A.lean").read_text()
    res = repo.run("fc", "--axioms", "A.lean")
    assert res.returncode == 1
    assert "A.lean:3:0: error: AXIOM-CHECK FAIL" in res.stdout.splitlines()[0]
    assert res.stdout.splitlines()[0].startswith("A.lean:")
    checked = Path(f"{repo.log}.checked").read_text()
    assert checked.startswith(source)
    assert checked.rstrip().endswith("#eval axiomCheck")
    assert (repo.root / "A.lean").read_text() == source
    assert list((repo.root / ".lake" / "warm" / "tmp").iterdir()) == []


def test_state_folder_can_be_moved_out_of_dot_lake(repo: Repo) -> None:
    repo.env["FC_STATE"] = str(repo.root / "state")
    before = repo.tree(".lake")
    assert repo.run("fc", "--axioms", "A.lean").returncode == 0
    assert repo.tree(".lake") == before
    assert (repo.root / "state" / "slots").is_dir()


@pytest.mark.parametrize(
    "args",
    [[], ["--frobnicate", "A.lean"], ["Missing.lean"], ["--min-free=x", "A.lean"]],
)
def test_usage_errors(repo: Repo, args: list[str]) -> None:
    res = repo.run("fc", *args)
    assert res.returncode == 2
    assert not repo.log.exists()


def module(
    repo: Repo, name: str, imports: list[str], olean: float | None, source: float
) -> None:
    """A module source with imports and, if ``olean`` is a time, its installed object file."""
    src = repo.root / (name.replace(".", "/") + ".lean")
    src.parent.mkdir(parents=True, exist_ok=True)
    src.write_text(
        "".join(f"import {i}\n" for i in imports) + "\ntheorem t : True := trivial\n"
    )
    os.utime(src, (source, source))
    if olean is not None:
        obj = repo.root / ".lake/build/lib/lean" / (name.replace(".", "/") + ".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        obj.write_text("")
        os.utime(obj, (olean, olean))


def test_warm_reports_the_installed_state_and_writes_nothing(repo: Repo) -> None:
    module(repo, "LeanDLRA.Core.A", [], olean=2000, source=1000)
    module(repo, "LeanDLRA.Core.B", ["LeanDLRA.Core.A"], olean=3000, source=1000)
    module(repo, "LeanDLRA.Literature.C", ["LeanDLRA.Core.B"], olean=2500, source=1000)
    module(
        repo,
        "LeanDLRA.Literature.D",
        ["LeanDLRA.Literature.C"],
        olean=None,
        source=1000,
    )
    module(repo, "LeanDLRA.Literature.E", ["LeanDLRA.Core.A"], olean=2500, source=2600)
    core = ["LeanDLRA.Core.A", "LeanDLRA.Core.B"]
    cat = ["LeanDLRA.Literature.C", "LeanDLRA.Literature.D", "LeanDLRA.Literature.E"]
    (repo.root / "LeanDLRA.lean").write_text("".join(f"import {m}\n" for m in core))
    (repo.root / "LeanDLRACatalogue.lean").write_text(
        "import LeanDLRA\n" + "".join(f"import {m}\n" for m in core + cat)
    )
    before = repo.tree(".")
    res = repo.run("warm.sh", "--list")
    assert res.returncode == 0, res.stdout + res.stderr
    assert "core: 2 modules, 0 missing, 0 stale, 0 behind" in res.stdout
    assert "catalogue: 3 modules, 1 missing, 1 stale, 1 behind" in res.stdout
    assert "LeanDLRA.Literature.C:  behind(LeanDLRA.Core.B)" in res.stdout
    assert "LeanDLRA.Literature.D: missing" in res.stdout
    assert "LeanDLRA.Literature.E: stale" in res.stdout
    assert repo.tree(".") == before
    assert not repo.log.exists()  # no `lake` at all


def test_warm_fails_while_the_core_is_not_installed(repo: Repo) -> None:
    module(repo, "LeanDLRA.Core.A", [], olean=None, source=1000)
    (repo.root / "LeanDLRA.lean").write_text("import LeanDLRA.Core.A\n")
    (repo.root / "LeanDLRACatalogue.lean").write_text(
        "import LeanDLRA\nimport LeanDLRA.Core.A\n"
    )
    res = repo.run("warm.sh")
    assert res.returncode == 1
    assert "core: 1 modules, 1 missing" in res.stdout
    assert "catalogue: 0 modules" in res.stdout
