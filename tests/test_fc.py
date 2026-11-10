"""Tests for ``scripts/fc`` and ``scripts/warm.sh`` with stand-ins for ``lake``, ``lean`` and
``memory_pressure`` (no Lean is started)."""

import json
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
# `lake env CMD …` runs CMD with the search path of the workspace in front of an incoming one.
FAKE_LAKE = """#!/usr/bin/env bash
printf '%s\\n' "$*" >> "$FAKE_LOG"
shift
LEAN_PATH="/workspace/lib${LEAN_PATH:+:$LEAN_PATH}" exec "$@"
"""
# `lean`: logs its search path and arguments and what the first folder of the search path shows
# (file, content, where the file really lies), prints the prepared messages (for all files, or
# for the file with a given base name), writes the `-o` target on success.
FAKE_LEAN = """#!/usr/bin/env bash
last="${@: -1}"
base="$(basename "$last" .lean)"
printf '%s | %s\\n' "$LEAN_PATH" "$*" >> "$FAKE_LOG.lean"
first="${LEAN_PATH%%:*}"
if [ "$first" != "/workspace/lib" ]; then
  (cd "$first" && find -L . -type f | sort | while IFS= read -r p; do
    if [ -L "$p" ]; then real="$(readlink "$p")"
    else real="$(cd "$(dirname "$p")" && pwd -P)/$(basename "$p")"; fi
    printf '%s\\t%s\\t%s\\n' "${p#./}" "$(cat "$p")" "$real"
  done) >> "$FAKE_LOG.view"
fi
echo "--" >> "$FAKE_LOG.view"
cp "$last" "$FAKE_LOG.checked"
out="$FAKE_OUT"; code="$FAKE_CODE"
[ -f "$FAKE_OUT.$base" ] && out="$FAKE_OUT.$base"
[ -f "$FAKE_CODE.$base" ] && code="$FAKE_CODE.$base"
sed "s|@FILE@|$last|g" "$out"
code="$(cat "$code")"
olean=""; prev=""
for a in "$@"; do [ "$prev" = "-o" ] && olean="$a"; prev="$a"; done
if [ "$code" = 0 ] && [ -n "$olean" ]; then echo "olean of $base" > "$olean"; fi
if [ -f "$FAKE_FREE.next" ]; then mv "$FAKE_FREE.next" "$FAKE_FREE"; fi
exit "$code"
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

    def set(
        self, out: str = "", code: int = 0, free: int | None = 60, only: str = ""
    ) -> None:
        """Messages and exit code of ``lean`` (``only``: for the file with this base name)."""
        suffix = f".{only}" if only else ""
        (self.root / f"fake.out{suffix}").write_text(out)
        (self.root / f"fake.code{suffix}").write_text(str(code))
        line = "" if free is None else f"System-wide memory free percentage: {free}%\n"
        (self.root / "fake.free").write_text(line)

    def free_after_next_lean(self, free: int) -> None:
        (self.root / "fake.free.next").write_text(
            f"System-wide memory free percentage: {free}%\n"
        )

    def lean_calls(self) -> list[tuple[list[str], list[str]]]:
        """Search path and arguments of every start of the stand-in ``lean``."""
        log = Path(f"{self.log}.lean")
        if not log.exists():
            return []
        calls = (line.split(" | ", 1) for line in log.read_text().splitlines())
        return [(path.split(":"), args.split(" ")) for path, args in calls]

    def views(self) -> list[dict[str, tuple[str, str]]]:
        """Per start of ``lean``: file of the view -> (content, where the file really lies)."""
        log = Path(f"{self.log}.view")
        out: list[dict[str, tuple[str, str]]] = [{}]
        for line in log.read_text().splitlines() if log.exists() else []:
            if line == "--":
                out.append({})
            else:
                name, content, real = line.split("\t")
                out[-1][name] = (content, real)
        return out[:-1]

    def overlay(self) -> list[str]:
        """Files below the folder of compiled prerequisites."""
        base = self.root / ".lake" / "warm" / "overlay"
        return sorted(
            str(p.relative_to(base).as_posix()) for p in base.rglob("*") if p.is_file()
        )

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
    for name, text in (
        ("lake", FAKE_LAKE),
        ("lean", FAKE_LEAN),
        ("memory_pressure", FAKE_MEMORY),
    ):
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


# ---------------------------------------------------------------------------------------------
# `--with`: prerequisites that are not installed


def new_slice(repo: Repo, name: str, target: str, imports: list[str]) -> str:
    """A slice ``wip/NAME.lean`` with its entry in the manifest; the path as given to fc."""
    wip = repo.root / "wip"
    wip.mkdir(exist_ok=True)
    manifest = wip / "manifest.json"
    data = json.loads(manifest.read_text()) if manifest.exists() else {}
    data[name] = {
        "source": "core",
        "target": target,
        "stubs": [],
        "ops": [],
        "chars": 0,
    }
    manifest.write_text(json.dumps(data, indent=2))
    (wip / f"{name}.lean").write_text(
        "".join(f"import {i}\n" for i in imports) + "\ntheorem t : True := trivial\n"
    )
    return f"wip/{name}.lean"


def test_with_compiles_the_prerequisite_outside_the_build_and_puts_it_first(
    repo: Repo,
) -> None:
    b = new_slice(repo, "SliceB", "LeanDLRA/New/B.lean", ["Mathlib"])
    (repo.root / "A.lean").write_text(
        "import LeanDLRA.New.B\n\ntheorem a : True := trivial\n"
    )
    before = repo.tree(".lake/build")
    res = repo.run("fc", "--with", b, "A.lean")
    assert res.returncode == 0, res.stdout + res.stderr
    lines = res.stdout.splitlines()
    assert lines[0].startswith("PREREQUISITE [wip/SliceB.lean] as LeanDLRA.New.B (")
    assert lines[1].startswith("OK [A.lean]")
    (path1, args1), (path2, args2) = repo.lean_calls()
    # The prerequisite: compiled as the module of its target, from a copy, into the overlay.
    assert path1 == ["/workspace/lib"]
    root = next(a for a in args1 if a.startswith("--root=")).removeprefix("--root=")
    assert args1[-1] == f"{root}/LeanDLRA/New/B.lean"
    assert "/.lake/warm/tmp/" in root
    out = args1[args1.index("-o") + 1]
    assert out.endswith("/LeanDLRA/New/B.olean") and "/.lake/warm/overlay/" in out
    assert "-DrelaxedAutoImplicit=false" in args1
    # The file: the view first, then the workspace; the file itself, not a copy.
    assert len(path2) == 2 and path2[1] == "/workspace/lib"
    assert path2[0].endswith("/view") and "/.lake/warm/tmp/fc." in path2[0]
    assert args2[-1] == str(repo.root.resolve() / "A.lean")
    assert "-o" not in args2
    (olean,) = repo.overlay()
    assert olean.endswith("/LeanDLRA/New/B.olean")
    # The view shows the compiled prerequisite, and it is the file of the overlay.
    view1, view2 = repo.views()
    assert view1 == {}
    assert view2 == {
        "LeanDLRA/New/B.olean": (
            "olean of B",
            str(repo.root.resolve() / ".lake" / "warm" / "overlay" / olean),
        )
    }
    assert repo.tree(".lake/build") == before
    assert list((repo.root / ".lake" / "warm" / "tmp").iterdir()) == []
    assert not (repo.root / ".lake" / "warm" / "slots" / "fc1").exists()


def test_with_uses_a_compiled_prerequisite_again_until_something_below_it_changes(
    repo: Repo,
) -> None:
    module(repo, "LeanDLRA.Core.A", [], olean=2000, source=1000)
    b = new_slice(repo, "SliceB", "LeanDLRA/New/B.lean", ["LeanDLRA.Core.A"])
    (repo.root / "A.lean").write_text("import LeanDLRA.New.B\n")
    assert repo.run("fc", "--with", b, "A.lean").returncode == 0
    assert len(repo.lean_calls()) == 2
    res = repo.run("fc", f"--with={b}", "A.lean")
    assert res.returncode == 0
    assert (
        "PREREQUISITE [wip/SliceB.lean] as LeanDLRA.New.B: compiled before"
        in res.stdout
    )
    assert len(repo.lean_calls()) == 3
    assert repo.views()[2] == repo.views()[1]
    # A new text of the slice.
    with (repo.root / b).open("a") as f:
        f.write("theorem t2 : True := trivial\n")
    assert repo.run("fc", "--with", b, "A.lean").returncode == 0
    assert len(repo.lean_calls()) == 5
    assert (
        repo.views()[4]["LeanDLRA/New/B.olean"]
        != repo.views()[2]["LeanDLRA/New/B.olean"]
    )
    # A new installed `.olean` below it (a gate round).
    (repo.root / ".lake/build/lib/lean/LeanDLRA/Core/A.olean").write_text("new")
    assert repo.run("fc", "--with", b, "A.lean").returncode == 0
    assert len(repo.lean_calls()) == 7
    # The same `.olean`, another Lake trace (something further below changed).
    (repo.root / ".lake/build/lib/lean/LeanDLRA/Core/A.trace").write_text("{}")
    assert repo.run("fc", "--with", b, "A.lean").returncode == 0
    assert len(repo.lean_calls()) == 9
    # Other options: the axiom check does not change the prerequisite.
    assert repo.run("fc", "--axioms", "--with", b, "A.lean").returncode == 0
    assert len(repo.lean_calls()) == 10
    assert len(repo.overlay()) == 4


def test_with_several_prerequisites_in_order(repo: Repo) -> None:
    b = new_slice(repo, "SliceB", "LeanDLRA/New/B.lean", [])
    c = new_slice(repo, "SliceC", "LeanDLRA/New/C.lean", ["LeanDLRA.New.B"])
    (repo.root / "A.lean").write_text("import LeanDLRA.New.C\n")
    res = repo.run("fc", "--with", b, "--with", c, "A.lean")
    assert res.returncode == 0, res.stdout + res.stderr
    (path_b, _), (path_c, args_c), (path_a, _) = repo.lean_calls()
    assert path_b == ["/workspace/lib"]
    assert len(path_c) == 2 and args_c[-1].endswith("/LeanDLRA/New/C.lean")
    # One view for all prerequisites: two folders with `LeanDLRA/` would hide each other.
    assert path_a == [path_c[0], "/workspace/lib"]
    _, view_c, view_a = repo.views()
    assert set(view_c) == {"LeanDLRA/New/B.olean"}
    assert set(view_a) == {"LeanDLRA/New/B.olean", "LeanDLRA/New/C.olean"}
    assert view_a["LeanDLRA/New/C.olean"][0] == "olean of C"
    # A new text of B: C is compiled again too, since its import changed.
    with (repo.root / b).open("a") as f:
        f.write("theorem t2 : True := trivial\n")
    assert repo.run("fc", "--with", b, "--with", c, "A.lean").returncode == 0
    assert len(repo.lean_calls()) == 6
    # Nothing new: two folders used again, one start of Lean.
    assert repo.run("fc", "--with", b, "--with", c, "A.lean").returncode == 0
    assert len(repo.lean_calls()) == 7


def installed(repo: Repo, rel: str, text: str) -> str:
    """An installed file below the build folder of the library; its real path."""
    path = repo.root / ".lake/build/lib/lean" / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    return str(path.resolve())


def test_with_keeps_the_installed_modules_of_the_package_visible(repo: Repo) -> None:
    # Lean takes a whole package from the first folder of the search path that has it: the view
    # must show every installed module of the library, and the prerequisite in place of its
    # installed files (all kinds of them), not beside them.
    root = installed(repo, "LeanDLRA.olean", "root")
    far = installed(repo, "LeanDLRA/Core/A.olean", "far")
    deep = installed(repo, "LeanDLRA/Core/Deep/D.olean", "deep")
    beside = installed(repo, "LeanDLRA/New/Old.olean", "beside")
    longer = installed(repo, "LeanDLRA/New/BStep.olean", "longer name")
    below = installed(repo, "LeanDLRA/New/B/Sub.olean", "below")
    for kind in ("olean", "ilean", "olean.private", "trace"):
        installed(repo, f"LeanDLRA/New/B.{kind}", "installed text of B")
    installed(repo, "LeanDLRACatalogue.olean", "other root")
    installed(repo, "LeanDLRACatalogue/X.olean", "other package")
    b = new_slice(repo, "SliceB", "LeanDLRA/New/B.lean", [])
    (repo.root / "A.lean").write_text("import LeanDLRA.New.B\nimport LeanDLRA.Core.A\n")
    before = repo.tree(".lake/build")
    res = repo.run("fc", "--with", b, "A.lean")
    assert res.returncode == 0, res.stdout + res.stderr
    view = repo.views()[1]
    (compiled,) = repo.overlay()
    assert view == {
        "LeanDLRA.olean": ("root", root),
        "LeanDLRA/Core/A.olean": ("far", far),
        "LeanDLRA/Core/Deep/D.olean": ("deep", deep),
        "LeanDLRA/New/Old.olean": ("beside", beside),
        "LeanDLRA/New/BStep.olean": ("longer name", longer),
        "LeanDLRA/New/B/Sub.olean": ("below", below),
        "LeanDLRA/New/B.olean": (
            "olean of B",
            str(repo.root.resolve() / ".lake/warm/overlay" / compiled),
        ),
    }
    # Removing the view removed links only.
    assert repo.tree(".lake/build") == before
    assert Path(far).read_text() == "far" and Path(below).read_text() == "below"
    assert list((repo.root / ".lake" / "warm" / "tmp").iterdir()) == []


def test_with_the_root_module_of_the_library(repo: Repo) -> None:
    far = installed(repo, "LeanDLRA/Core/A.olean", "far")
    installed(repo, "LeanDLRA.olean", "installed root")
    installed(repo, "LeanDLRA.ilean", "installed root")
    (repo.root / "LeanDLRA.lean").write_text("import Mathlib\n")
    c = new_slice(repo, "SliceC", "LeanDLRA/New/C.lean", [])
    (repo.root / "A.lean").write_text("import LeanDLRA\nimport LeanDLRA.Core.A\n")
    for withs in (
        ["--with", "LeanDLRA.lean"],
        ["--with", "LeanDLRA.lean", "--with", c],
    ):
        res = repo.run("fc", *withs, "A.lean")
        assert res.returncode == 0, res.stdout + res.stderr
        view = repo.views()[-1]
        assert view["LeanDLRA.olean"][0] == "olean of LeanDLRA"
        assert view["LeanDLRA/Core/A.olean"] == ("far", far)
        assert "LeanDLRA.ilean" not in view
        assert ("LeanDLRA/New/C.olean" in view) == (len(withs) == 4)
    # The other order of the two prerequisites gives the same view.
    res = repo.run("fc", "--with", c, "--with", "LeanDLRA.lean", "A.lean")
    assert res.returncode == 0, res.stdout + res.stderr
    assert repo.views()[-1] == view


def test_with_refuses_a_module_of_another_package(repo: Repo) -> None:
    (repo.root / "wip").mkdir()
    (repo.root / "wip" / "Free.lean").write_text("theorem t : True := trivial\n")
    (repo.root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib").mkdir(
        parents=True
    )
    for name, owner in (
        ("Mathlib.Order.New", "a package of the workspace"),
        ("Lean.New", "the toolchain"),
    ):
        res = repo.run("fc", "--with", f"wip/Free.lean={name}", "A.lean")
        assert res.returncode == 2, res.stdout
        assert f"cannot replace {name}" in res.stdout and owner in res.stdout
    assert repo.lean_calls() == []


def test_with_module_names(repo: Repo) -> None:
    (repo.root / "wip").mkdir()
    (repo.root / "wip" / "Free.lean").write_text("theorem t : True := trivial\n")
    (repo.root / "LeanDLRA.lean").write_text("")
    module(repo, "LeanDLRA.Core.Z", [], olean=None, source=1000)
    # Not in the manifest and no name given.
    res = repo.run("fc", "--with", "wip/Free.lean", "A.lean")
    assert res.returncode == 2 and "wip/Free.lean=Module.Name" in res.stdout
    # A name given; a module of the library by its path.
    res = repo.run(
        "fc", "--with", "wip/Free.lean=My.Mod", "--with=LeanDLRA/Core/Z.lean", "A.lean"
    )
    assert res.returncode == 0, res.stdout + res.stderr
    assert "PREREQUISITE [wip/Free.lean] as My.Mod (" in res.stdout
    assert "PREREQUISITE [LeanDLRA/Core/Z.lean] as LeanDLRA.Core.Z (" in res.stdout
    assert [a[-1].split("/src/")[1] for _, a in repo.lean_calls()[:2]] == [
        "My/Mod.lean",
        "LeanDLRA/Core/Z.lean",
    ]
    # A file that is neither: no guess from the path.
    (repo.root / "scripts" / "X.lean").write_text("")
    assert repo.run("fc", "--with", "scripts/X.lean", "A.lean").returncode == 2


@pytest.mark.parametrize(
    "args",
    [
        ["--with"],
        ["--with", "wip/Missing.lean", "A.lean"],
        ["--with", "wip/Free.lean=../x", "A.lean"],
        ["--with", "wip/Free.lean=a/b", "A.lean"],
        ["--with", "wip/Free.lean=M", "--with", "A.lean=M", "A.lean"],
    ],
)
def test_with_usage_errors(repo: Repo, args: list[str]) -> None:
    (repo.root / "wip").mkdir()
    (repo.root / "wip" / "Free.lean").write_text("")
    res = repo.run("fc", *args)
    assert res.returncode == 2, res.stdout
    assert not repo.log.exists()
    assert not (repo.root / ".lake" / "warm").exists()


def test_with_a_failing_prerequisite_stops_before_the_file(repo: Repo) -> None:
    b = new_slice(repo, "SliceB", "LeanDLRA/New/B.lean", [])
    repo.set(out="@FILE@:3:8: error: unsolved goals\n", code=1, only="B")
    res = repo.run("fc", "--with", b, "A.lean")
    assert res.returncode == 5
    lines = res.stdout.splitlines()
    assert lines[0] == "wip/SliceB.lean:3:8: error: unsolved goals"
    assert lines[1].startswith(
        "PREREQUISITE FAILED [wip/SliceB.lean] as LeanDLRA.New.B"
    )
    assert "A.lean was not checked" in lines[1]
    assert len(repo.lean_calls()) == 1
    assert repo.overlay() == []
    assert list((repo.root / ".lake" / "warm" / "overlay").iterdir()) == []
    assert not (repo.root / ".lake" / "warm" / "slots" / "fc1").exists()
    # A warning in a prerequisite is said, and the file is still checked.
    repo.set(out="@FILE@:3:8: warning: unused variable `h`\n", only="B")
    res = repo.run("fc", "--with", b, "A.lean")
    assert res.returncode == 0
    assert "PREREQUISITE [wip/SliceB.lean] as LeanDLRA.New.B (" in res.stdout
    assert ", with warnings)" in res.stdout
    assert res.stdout.splitlines()[-1].startswith("OK [A.lean]")


def test_with_a_prerequisite_whose_import_is_not_installed(repo: Repo) -> None:
    b = new_slice(repo, "SliceB", "LeanDLRA/New/B.lean", ["LeanDLRA.New.C"])
    repo.set(
        out="@FILE@:1:0: error: object file '/x/LeanDLRA/New/C.olean' of module "
        "LeanDLRA.New.C does not exist\n",
        code=1,
    )
    res = repo.run("fc", "--with", b, "A.lean")
    assert res.returncode == 4
    assert "NO OLEAN [wip/SliceB.lean]" in res.stdout
    assert list((repo.root / ".lake" / "warm" / "overlay").iterdir()) == []


def test_with_refuses_to_mix_two_texts_of_a_module(repo: Repo) -> None:
    (repo.root / "LeanDLRA.lean").write_text("")
    module(repo, "LeanDLRA.Old.B", [], olean=2000, source=1000)
    module(repo, "LeanDLRA.Old.Mid", ["LeanDLRA.Old.B"], olean=2000, source=1000)
    module(repo, "LeanDLRA.Old.Top", ["LeanDLRA.Old.Mid"], olean=2000, source=1000)
    module(repo, "LeanDLRA.Old.Side", [], olean=2000, source=1000)
    b = new_slice(repo, "SliceB", "LeanDLRA/Old/B.lean", [])
    (repo.root / "A.lean").write_text(
        "import LeanDLRA.Old.B\nimport LeanDLRA.Old.Side\nimport LeanDLRA.Old.Top\n"
    )
    res = repo.run("fc", "--with", b, "A.lean")
    assert res.returncode == 6
    assert res.stdout.startswith(
        "MIXED [A.lean]: the installed LeanDLRA.Old.Mid imports LeanDLRA.Old.B"
    )
    assert not repo.log.exists()
    assert not (repo.root / ".lake" / "warm").exists()
    # With the modules in between as prerequisites it is one consistent set.
    res = repo.run(
        "fc",
        *("--with", b),
        *("--with", "LeanDLRA/Old/Mid.lean"),
        *("--with", "LeanDLRA/Old/Top.lean"),
        "A.lean",
    )
    assert res.returncode == 0, res.stdout + res.stderr
    assert len(repo.lean_calls()) == 4
    # Without a module in between the same slice is fine.
    (repo.root / "A.lean").write_text(
        "import LeanDLRA.Old.B\nimport LeanDLRA.Old.Side\n"
    )
    assert repo.run("fc", "--with", b, "A.lean").returncode == 0


def test_with_tests_the_memory_before_every_start(repo: Repo) -> None:
    b = new_slice(repo, "SliceB", "LeanDLRA/New/B.lean", [])
    repo.set(free=30)
    res = repo.run("fc", "--with", b, "A.lean")
    assert res.returncode == 3 and repo.lean_calls() == []
    repo.set(free=60)
    repo.free_after_next_lean(20)
    res = repo.run("fc", "--with", b, "A.lean")
    assert res.returncode == 3
    assert "PREREQUISITE [wip/SliceB.lean]" in res.stdout
    assert "NOT STARTED [A.lean]: 20 % of the memory free" in res.stdout
    assert len(repo.lean_calls()) == 1
    # The compiled prerequisite is kept for the next try.
    repo.set(free=60)
    res = repo.run("fc", "--with", b, "A.lean")
    assert res.returncode == 0 and "compiled before" in res.stdout
    assert len(repo.lean_calls()) == 2


def test_with_removes_folders_not_used_for_a_day(repo: Repo) -> None:
    b = new_slice(repo, "SliceB", "LeanDLRA/New/B.lean", [])
    assert repo.run("fc", "--with", b, "A.lean").returncode == 0
    base = repo.root / ".lake" / "warm" / "overlay"
    (used,) = base.iterdir()
    stale = base / "0123"
    stale.mkdir()
    for folder in (used, stale):
        os.utime(folder, (1000, 1000))
    assert repo.run("fc", "--with", b, "A.lean").returncode == 0
    # The stale one is gone; the old one of this slice was removed and compiled again.
    assert [p.name for p in base.iterdir()] == [used.name]
    assert len(repo.lean_calls()) == 4


# `lean` stand-ins for the lock: the first tries what another script could do to the lock of a
# running check, the second takes the lock away.
LEAN_FOREIGN_RMDIR = """#!/usr/bin/env bash
printf 'x\\n' >> "$FAKE_LOG"
rmdir "$FC_TEST_LOCK" 2> /dev/null
echo "rmdir=$?" > "$FAKE_LOG.lock"
cat "$FC_TEST_LOCK/owner" >> "$FAKE_LOG.lock" 2> /dev/null
olean=""; prev=""
for a in "$@"; do [ "$prev" = "-o" ] && olean="$a"; prev="$a"; done
[ -n "$olean" ] && echo olean > "$olean"
exit 0
"""
LEAN_TAKES_THE_LOCK_AWAY = LEAN_FOREIGN_RMDIR.replace(
    'rmdir "$FC_TEST_LOCK" 2> /dev/null', 'rm -rf "$FC_TEST_LOCK"'
)


def lock_of(repo: Repo) -> Path:
    return repo.root / ".lake" / "warm" / "slots" / "fc1"


def lock_log(repo: Repo) -> str:
    log = repo.root / ".lake" / "warm" / "lock.log"
    return log.read_text() if log.exists() else ""


def start_of(pid: int) -> str:
    res = subprocess.run(
        ["ps", "-o", "lstart=", "-p", str(pid)],
        capture_output=True,
        text=True,
        check=True,
    )
    return res.stdout.rstrip("\n")


def hold_lock(repo: Repo, pid: int, started: str) -> None:
    lock_of(repo).mkdir(parents=True)
    (lock_of(repo) / "owner").write_text(f"{pid}\n{started}\n2026-01-01 00:00:00 X\n")


def ended_process() -> int:
    proc = subprocess.Popen(["true"])
    proc.wait()
    return proc.pid


def test_lock_names_its_owner_and_a_foreign_rmdir_fails(repo: Repo) -> None:
    (repo.root / "bin" / "lean").write_text(LEAN_FOREIGN_RMDIR)
    repo.env["FC_TEST_LOCK"] = str(lock_of(repo))
    res = repo.run("fc", "A.lean")
    assert res.returncode == 0, res.stdout + res.stderr
    seen = Path(f"{repo.log}.lock").read_text().splitlines()
    assert seen[0] != "rmdir=0"
    assert seen[1].isdigit() and seen[2] and seen[3].endswith(" A.lean")
    assert "LOCK LOST" not in res.stderr
    assert not lock_of(repo).exists()
    events = [line.split(" ", 3)[3] for line in lock_log(repo).splitlines()]
    assert events == ["taken [A.lean]", "released [A.lean]"]


def test_lock_of_an_ended_process_is_taken_over(repo: Repo) -> None:
    pid = ended_process()
    hold_lock(repo, pid, "Thu Jan  1 00:00:00 2026")
    res = repo.run("fc", "A.lean")
    assert res.returncode == 0 and res.stdout.startswith("OK [A.lean]")
    assert f"removed the lock of the ended process {pid}" in lock_log(repo)
    assert not lock_of(repo).exists()


def test_same_process_id_with_another_start_counts_as_ended(repo: Repo) -> None:
    hold_lock(repo, os.getpid(), "Thu Jan  1 00:00:00 1970")
    res = repo.run("fc", "A.lean")
    assert res.returncode == 0 and res.stdout.startswith("OK [A.lean]")
    assert not lock_of(repo).exists()


def test_lock_of_a_running_process_is_respected(repo: Repo) -> None:
    hold_lock(repo, os.getpid(), start_of(os.getpid()))
    proc = subprocess.Popen(
        ["bash", str(repo.root / "scripts" / "fc"), "A.lean"],
        cwd=repo.root,
        env=repo.env,
        stdout=subprocess.PIPE,
        text=True,
    )
    with pytest.raises(subprocess.TimeoutExpired):
        proc.wait(timeout=4)
    # It waits: nothing was started and the lock is still the one of the other process.
    assert not repo.log.exists()
    assert (lock_of(repo) / "owner").read_text().startswith(f"{os.getpid()}\n")
    assert "removed" not in lock_log(repo)
    (lock_of(repo) / "owner").unlink()
    lock_of(repo).rmdir()
    out, _ = proc.communicate(timeout=30)
    assert proc.returncode == 0 and out.startswith("OK [A.lean]")
    assert not lock_of(repo).exists()


def test_empty_lock_folder_is_respected_until_it_is_old(repo: Repo) -> None:
    lock_of(repo).mkdir(parents=True)
    proc = subprocess.Popen(
        ["bash", str(repo.root / "scripts" / "fc"), "A.lean"],
        cwd=repo.root,
        env=repo.env,
        stdout=subprocess.PIPE,
        text=True,
    )
    with pytest.raises(subprocess.TimeoutExpired):
        proc.wait(timeout=4)
    assert not repo.log.exists() and lock_of(repo).is_dir()
    old = lock_of(repo).stat().st_mtime - 31 * 60
    os.utime(lock_of(repo), (old, old))
    out, _ = proc.communicate(timeout=30)
    assert proc.returncode == 0 and out.startswith("OK [A.lean]")
    assert not lock_of(repo).exists()


def test_lock_taken_away_is_said_and_no_further_lean_starts(repo: Repo) -> None:
    (repo.root / "bin" / "lean").write_text(LEAN_TAKES_THE_LOCK_AWAY)
    repo.env["FC_TEST_LOCK"] = str(lock_of(repo))
    # One Lean process: the verdict stands, and the loss is said and logged.
    res = repo.run("fc", "A.lean")
    assert res.returncode == 0 and res.stdout.startswith("OK [A.lean]")
    assert "LOCK LOST [A.lean]" in res.stderr
    assert "LOST, owner now:" in lock_log(repo)
    # Two Lean processes: the second one is not started.
    b = new_slice(repo, "SliceB", "LeanDLRA/New/B.lean", [])
    repo.log.unlink()
    res = repo.run("fc", "--with", b, "A.lean")
    assert res.returncode == 3, res.stdout + res.stderr
    assert "NOT STARTED [A.lean]: the lock of this check was taken away" in res.stdout
    # One call of `lake` and one start of `lean`: the prerequisite only.
    calls = repo.log.read_text().splitlines()
    assert len(calls) == 2 and calls[0].endswith("/B.lean") and calls[1] == "x"
    # A lock that is not ours any more is left alone.
    (repo.root / "bin" / "lean").write_text(
        LEAN_TAKES_THE_LOCK_AWAY.replace(
            'rm -rf "$FC_TEST_LOCK"', 'echo 1 > "$FC_TEST_LOCK/owner"'
        )
    )
    res = repo.run("fc", "A.lean")
    assert "LOCK LOST [A.lean]" in res.stderr
    assert (lock_of(repo) / "owner").read_text() == "1\n"
