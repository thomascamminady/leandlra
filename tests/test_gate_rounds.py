"""Rounds of scripts/gate.py in a throwaway repository: real git, fake lake and scripts."""

from __future__ import annotations

import gzip
import json
import os
import re
import subprocess
from pathlib import Path

import gate
import pytest

CATALOGUE = {"Literature", "OpenProblems", "Novel", "Corrections"}
LIBRARY = ("LeanDLRA", "LeanDLRA.lean", "LeanDLRACatalogue.lean")


class World:
    """A repository with a queue, and the command runner the gate under test gets.

    Git commands run for real (except the push); `lake`, `scripts/gen_root.sh`, `scripts/audit.sh`,
    `scripts/core.py` and `scripts/rolling.py` are played by this class, which fails them when a
    file or module listed in one of its sets is in the tree.
    """

    def __init__(self, root: Path) -> None:
        self.root = root
        self.calls: list[tuple[str, ...]] = []
        self.bad_slices: set[str] = set()  # modules that fail `lake build --wfail`
        self.anonymous_failure = (
            False  # `lake build --wfail` fails without naming a slice
        )
        self.core_breakers: set[str] = (
            set()
        )  # modules whose presence fails `lake build LeanDLRA`
        self.core_check_bad: set[str] = (
            set()
        )  # modules whose presence fails `core.py check`
        self.audit_bad: set[str] = set()  # modules that fail the audit
        self.unfaithful: set[str] = set()  # modules whose presence fails fidelity
        self.changed: dict[str, int] = {}  # module -> declarations it changes
        self.removed: dict[str, int] = {}  # module -> declarations it removes
        self.push_code = 0
        self.tool_broken = ""  # a rolling.py command that cannot run
        self.dumped: list[str] = []
        self.clock = 1000.0
        for folder in ("wip/ready", "docs", "LeanDLRA", ".lake/hashdiff"):
            (root / folder).mkdir(parents=True)
        self.write(".gitignore", "wip/\n.lake/\n")
        self.write("docs/renames.json", json.dumps({"Old.a": "New.a"}, indent=2) + "\n")
        self.write("docs/promoted.txt", "# promoted catalogue modules\n")
        self.write("LeanDLRA/Base.lean", "def base := 1\n")
        self.write("wip/manifest.json", "{}")
        self.real("git", "init", "-q", "-b", "main")
        self.real("git", "config", "user.name", "Test")
        self.real("git", "config", "user.email", "test@example.org")
        self.real("git", "config", "commit.gpgsign", "false")
        self.real("git", "add", "-A")
        self.gen_root()
        self.real("git", "add", "-A")
        self.real("git", "commit", "-q", "-m", "start")
        self.seed()

    # -- the repository ------------------------------------------------------------------------

    def write(self, rel: str, text: str) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def read(self, rel: str) -> str:
        return (self.root / rel).read_text(encoding="utf-8")

    def real(self, *cmd: str) -> tuple[int, str]:
        proc = subprocess.run(
            cmd, cwd=self.root, capture_output=True, text=True, check=False
        )
        return proc.returncode, proc.stdout + proc.stderr

    def head(self) -> str:
        return self.real("git", "rev-parse", "HEAD")[1].strip()

    def status(self) -> str:
        return self.real("git", "status", "--porcelain")[1]

    def committed_files(self, rev: str = "HEAD") -> list[str]:
        out = self.real("git", "show", "--name-only", "--format=", rev)[1]
        return sorted(out.split())

    def subjects(self) -> list[str]:
        return self.real("git", "log", "--format=%s")[1].splitlines()

    def log(self) -> list[str]:
        path = self.root / "wip/gate.log"
        return path.read_text(encoding="utf-8").splitlines() if path.exists() else []

    def lines(self, kind: str) -> list[str]:
        """The log lines of one kind, without their time."""
        return [line[9:] for line in self.log() if line[9:].startswith(kind)]

    def seed(self) -> None:
        """A rolling dump that describes the present library commit."""
        commit = self.real("git", "rev-list", "-1", "HEAD", "--", *LIBRARY)[1].strip()
        for name in gate.ROLLING:
            with gzip.open(
                self.root / gate.HASHDIR / name, "wt", encoding="utf-8"
            ) as f:
                f.write(json.dumps({"library_commit": commit}) + "\n")

    # -- the queue -----------------------------------------------------------------------------

    def slice(
        self, name: str, target: str = "", text: str = "", queue: bool = True
    ) -> str:
        """Add a slice to the manifest and (unless told otherwise) to `wip/ready`."""
        target = target or f"LeanDLRA/Literature/{name}.lean"
        table = json.loads(self.read("wip/manifest.json"))
        table[name] = {
            "source": f"wip/{name}.lean",
            "target": target,
            "stubs": [],
            "ops": [f"OP-{name}"],
            "chars": 1,
        }
        self.write("wip/manifest.json", json.dumps(table))
        if queue:
            self.write(
                f"wip/ready/{name}.lean", text or f"theorem {name} : True := trivial\n"
            )
            self.clock += 10
            os.utime(self.root / f"wip/ready/{name}.lean", (self.clock, self.clock))
        return gate.module_name(target)

    def group(self, gid: str, names: list[str], **extra: object) -> None:
        """Queue the slices (if they are not there yet) and their marker."""
        for name in names:
            if not (self.root / f"wip/ready/{name}.lean").exists():
                self.slice(name)
        marker = {"id": gid, "files": [f"{n}.lean" for n in names], **extra}
        self.write(f"wip/ready/{gid}.group", json.dumps(marker))
        self.clock += 10
        os.utime(self.root / f"wip/ready/{gid}.group", (self.clock, self.clock))

    def ready(self) -> list[str]:
        return sorted(p.name for p in (self.root / "wip/ready").iterdir())

    def folder(self, name: str) -> list[str]:
        path = self.root / "wip" / name
        return sorted(p.name for p in path.iterdir()) if path.exists() else []

    # -- the runner ----------------------------------------------------------------------------

    def present(self, modules: set[str]) -> list[str]:
        return sorted(m for m in modules if (self.root / gate.module_path(m)).exists())

    def gen_root(self) -> tuple[int, str]:
        files = self.real("git", "ls-files", "LeanDLRA")[1].splitlines()
        modules = sorted(f[:-5].replace("/", ".") for f in files if f.endswith(".lean"))
        promoted = {
            line.split("#")[0].strip()
            for line in self.read("docs/promoted.txt").splitlines()
        }
        core = [m for m in modules if m.split(".")[1] not in CATALOGUE or m in promoted]
        rest = [m for m in modules if m not in core]
        self.write("LeanDLRA.lean", "".join(f"import {m}\n" for m in core))
        self.write(
            "LeanDLRACatalogue.lean",
            "import LeanDLRA\n" + "".join(f"import {m}\n" for m in rest),
        )
        return 0, ""

    def tool(self, command: str, args: tuple[str, ...]) -> tuple[int, str]:
        if command == self.tool_broken:
            return 2, f"rolling: cannot run {command}"
        if command == "dump":
            self.dumped = list(args)
        elif command == "fidelity":
            lost = self.present(self.unfaithful & set(self.dumped))
            if lost:
                return (
                    1,
                    f"488 of 489 recorded statements proved verbatim\nmissing: thm_of_{lost[0]}\n",
                )
        elif command == "diff":
            report = next(a for a in args if a.startswith("--report=")).removeprefix(
                "--report="
            )
            self.write(report, "# report\n")
            counts = {
                "base": "abc1234",
                "declarations": 100,
                "changed": sum(self.changed.get(m, 0) for m in self.dumped),
                "moved": 0,
                "added": len(self.dumped),
                "removed": sum(self.removed.get(m, 0) for m in self.dumped),
            }
            return 0, f"# report\nHASHDIFF {json.dumps(counts)}\n"
        elif command == "accept":
            self.seed()
        return 0, ""

    def __call__(self, *cmd: str, timeout: int = 14400) -> tuple[int, str]:
        self.calls.append(cmd)
        if cmd == gate.PUSH:
            return (
                self.push_code,
                "" if self.push_code == 0 else "fatal: no route to host",
            )
        if cmd[0] == "git":
            return self.real(*cmd)
        if cmd[:3] == ("lake", "build", "--wfail") and cmd != gate.CORE_BUILD:
            failed = [m for m in cmd[3:] if m in self.bad_slices]
            if failed:
                out = "".join(
                    f"✖ [7/9] Building {m}\nerror: {m}: unsolved goals\n"
                    for m in failed
                )
                return 1, out + "error: build failed\n"
            if self.anonymous_failure:
                return 1, "error: no such file or directory\n"
            return 0, ""
        if cmd == gate.CORE_BUILD:
            broken = self.present(self.core_breakers)
            return (
                (1, f"error: {broken[0]} breaks the library\n") if broken else (0, "")
            )
        if cmd == ("scripts/gen_root.sh",):
            return self.gen_root()
        if cmd == ("uv", "run", "-q", "scripts/core.py", "check"):
            bad = self.present(self.core_check_bad)
            return (
                (1, f"{bad[0]} imports LeanDLRA.Literature.X, which is not core\n")
                if bad
                else (0, "")
            )
        if cmd[:2] == ("scripts/audit.sh", "LeanDLRA"):
            bad = [m for m in cmd[2:] if m in self.audit_bad]
            return (1, f"audit: {bad[0]} uses an axiom\n") if bad else (0, "")
        if cmd[:4] == gate.TOOL:
            return self.tool(cmd[4], cmd[5:])
        raise AssertionError(f"unexpected command: {cmd}")

    def commands(self, *prefix: str) -> list[tuple[str, ...]]:
        """The calls that start with the given words."""
        return [c for c in self.calls if c[: len(prefix)] == prefix]

    def slice_builds(self) -> list[tuple[str, ...]]:
        """The builds of slices (`lake build --wfail MODULE ...`), without the core build."""
        return [
            c for c in self.commands("lake", "build", "--wfail") if c != gate.CORE_BUILD
        ]

    def run_gate(self, batch: int = 12, legacy_max: int = 6, grace: float = 0.0) -> int:
        """One pass of the gate over the queue (as `gate.py --once`, until the queue is empty)."""
        return gate.Gate(self.root, self).loop(batch, True, legacy_max, grace)


@pytest.fixture
def world(tmp_path: Path) -> World:
    return World(tmp_path)


LIT = "LeanDLRA/Literature"


# -- accepted rounds ------------------------------------------------------------------------------


def test_round_with_one_group_is_committed_and_pushed(world: World) -> None:
    world.group("g1", ["A", "B"])
    base = world.head()
    assert world.run_gate() == 0
    assert world.subjects()[0] == "Add 2 slices (A, B)"
    message = world.real("git", "log", "-1", "--format=%B")[1]
    assert message.strip() == f"Add 2 slices (A, B)\n\nOP-A OP-B\n\n{gate.TRAILER}"
    assert world.committed_files() == [
        f"{LIT}/A.lean",
        f"{LIT}/B.lean",
        "LeanDLRACatalogue.lean",
    ]
    assert world.real("git", "rev-list", "--count", f"{base}..HEAD")[1].strip() == "1"
    assert world.status() == ""
    assert world.commands(*gate.PUSH) == [gate.PUSH]
    assert world.ready() == []
    assert world.folder("done") == ["A.lean", "B.lean", "g1.group"]
    assert not (world.root / "wip/gate.round.json").exists()
    log = world.log()
    assert all(re.match(r"\d\d:\d\d:\d\d \S", line) for line in log)
    sha = world.real("git", "rev-parse", "--short", "HEAD")[1].strip()
    assert [line[9:] for line in log] == [
        "gate started",
        "ROUND 1 group(s): g1 (A, B)",
        f"HASHDIFF abc1234..{sha}: 100 declarations, 0 changed, 0 moved, 2 added, 0 removed",
        f"CORE {sha}: 1 core modules, 2 slice modules in the catalogue",
        "PUSHED Add 2 slices (A, B)",
    ]
    assert (world.root / gate.HASHDIR / f"report_abc1234..{sha}.md").exists()


def test_stages_run_in_order(world: World) -> None:
    world.group("g1", ["A"])
    world.run_gate()
    module = "LeanDLRA.Literature.A"
    work = [c for c in world.calls if c[0] != "git" or c[1] in ("commit", "push")]
    assert [c[:5] for c in work] == [
        ("lake", "build", "--wfail", module),
        ("scripts/gen_root.sh",),
        ("uv", "run", "-q", "scripts/core.py", "check"),
        gate.CORE_BUILD,
        ("scripts/audit.sh", "LeanDLRA", module),
        (*gate.TOOL, "dump"),
        (*gate.TOOL, "fidelity"),
        (*gate.TOOL, "diff"),
        ("git", "commit", "-q", "-m", gate.commit_message("Add 1 slice (A)", ["OP-A"])),
        gate.PUSH,
        (*gate.TOOL, "accept"),
    ]
    assert world.commands(*gate.TOOL, "dump") == [(*gate.TOOL, "dump", module)]


def test_several_groups_share_a_round_and_a_commit(world: World) -> None:
    world.group("g1", ["A", "B"])
    world.group("g2", ["C"])
    world.group("g3", ["D", "E"])
    assert world.run_gate(batch=3) == 0
    assert world.subjects()[:2] == ["Add 2 slices (D, E)", "Add 3 slices (A, B, C)"]
    assert world.lines("ROUND") == [
        "ROUND 2 group(s): g1 (A, B); g2 (C)",
        "ROUND 1 group(s): g3 (D, E)",
    ]
    assert len(world.commands(*gate.CORE_BUILD)) == 2


def test_update_of_a_landed_slice(world: World) -> None:
    world.group("g1", ["A"])
    world.run_gate()
    world.slice("A", text="theorem A : True := by trivial\n")
    world.group("g2", ["A"])
    world.run_gate()
    assert world.subjects()[0] == "Update 1 slice (A)"
    assert world.read(f"{LIT}/A.lean") == "theorem A : True := by trivial\n"
    assert world.committed_files() == [f"{LIT}/A.lean"]


def test_core_slice_changes_the_core_root(world: World) -> None:
    world.slice("Core", target="LeanDLRA/Analysis/Core.lean")
    world.group("g1", ["Core"])
    world.run_gate()
    assert world.committed_files() == ["LeanDLRA.lean", "LeanDLRA/Analysis/Core.lean"]
    assert world.lines("CORE")[0].endswith(
        ": 2 core modules, 0 slice modules in the catalogue"
    )


def test_gate_commits_only_its_own_files(world: World) -> None:
    world.write("docs/notes.md", "someone else's work\n")
    world.real("git", "add", "docs/notes.md")
    world.write("docs/renames.json", world.read("docs/renames.json") + "\n")
    world.group("g1", ["A"])
    world.run_gate()
    assert world.committed_files() == [f"{LIT}/A.lean", "LeanDLRACatalogue.lean"]
    assert sorted(world.status().splitlines()) == [
        " M docs/renames.json",
        "A  docs/notes.md",
    ]


def test_legacy_files_still_work(world: World) -> None:
    for name in ("L1", "L2", "L3"):
        world.slice(name)
    assert world.run_gate(legacy_max=2) == 0
    assert world.subjects()[:2] == ["Add 1 slice (L3)", "Add 2 slices (L1, L2)"]
    assert world.lines("ROUND")[0] == "ROUND 1 group(s): legacy (L1, L2)"
    assert world.folder("done") == ["L1.lean", "L2.lean", "L3.lean"]


def test_young_legacy_file_is_left_alone(world: World) -> None:
    world.slice("L1")
    os.utime(world.root / "wip/ready/L1.lean")
    assert world.run_gate(grace=120.0) == 0
    assert world.ready() == ["L1.lean"]
    assert world.commands("lake") == []


# -- failures of a slice --------------------------------------------------------------------------


def test_forbidden_token_rejects_the_group_and_the_round_goes_on(world: World) -> None:
    world.slice("A", text="theorem A : True := by sorry\n")
    world.group("g1", ["A", "B"])
    world.group("g2", ["C"])
    assert world.run_gate() == 0
    assert world.subjects()[0] == "Add 1 slice (C)"
    assert world.lines("REJECT") == [
        "REJECT A: forbidden token in the source",
        "REJECT B: group g1 rejected: A: forbidden token in the source",
    ]
    assert world.folder("rejected") == [
        "A.lean",
        "A.log",
        "B.lean",
        "B.log",
        "g1.group",
    ]
    assert world.slice_builds() == [
        ("lake", "build", "--wfail", "LeanDLRA.Literature.C")
    ]
    assert not (world.root / f"{LIT}/A.lean").exists()
    assert not (world.root / f"{LIT}/B.lean").exists()


def test_forbidden_token_in_a_legacy_slice_rejects_only_that_slice(
    world: World,
) -> None:
    world.slice("L1", text="axiom cheat : False\n")
    world.slice("L2")
    world.run_gate()
    assert world.lines("REJECT") == ["REJECT L1: forbidden token in the source"]
    assert world.subjects()[0] == "Add 1 slice (L2)"


def test_slice_without_manifest_entry(world: World) -> None:
    world.write("wip/ready/Stray.lean", "theorem s : True := trivial\n")
    world.group("g1", ["Stray", "A"])
    world.run_gate()
    assert world.lines("REJECT") == [
        "REJECT Stray: not a slice of the manifest",
        "REJECT A: group g1 rejected: Stray: not a slice of the manifest",
    ]
    assert world.commands("lake") == []


def test_two_slices_of_a_group_with_one_target(world: World) -> None:
    world.slice("A1", target=f"{LIT}/A.lean")
    world.slice("A2", target=f"{LIT}/A.lean")
    world.group("g1", ["A1", "A2"])
    world.run_gate()
    assert world.lines("REJECT")[1] == f"REJECT A2: same target as A1: {LIT}/A.lean"


def test_slice_build_failure_rejects_its_group_only(world: World) -> None:
    world.group("g1", ["A", "B"])
    world.group("g2", ["C"])
    world.bad_slices = {"LeanDLRA.Literature.B"}
    assert world.run_gate() == 0
    assert world.lines("REJECT") == [
        "REJECT A: group g1 rejected: B: lake build --wfail failed",
        "REJECT B: lake build --wfail failed",
    ]
    assert "unsolved goals" in world.read("wip/rejected/B.log")
    assert world.subjects()[0] == "Add 1 slice (C)"
    # The build is repeated for the slices that are left; the rejected targets are gone.
    assert [c[3:] for c in world.slice_builds()] == [
        ("LeanDLRA.Literature.A", "LeanDLRA.Literature.B", "LeanDLRA.Literature.C"),
        ("LeanDLRA.Literature.C",),
    ]
    assert not (world.root / f"{LIT}/A.lean").exists()
    assert not (world.root / f"{LIT}/B.lean").exists()
    assert world.status() == ""
    assert world.lines("FALLBACK") == []


def test_slice_build_failure_restores_a_landed_module(world: World) -> None:
    world.group("g1", ["A"])
    world.run_gate()
    landed = world.read(f"{LIT}/A.lean")
    world.slice("A", text="theorem A : True := by wrong\n")
    world.group("g2", ["A", "B"])
    world.bad_slices = {"LeanDLRA.Literature.A"}
    world.run_gate()
    assert world.read(f"{LIT}/A.lean") == landed
    assert not (world.root / f"{LIT}/B.lean").exists()
    assert world.status() == ""
    assert world.subjects()[0] == "Add 1 slice (A)"


def test_slice_build_failure_in_a_legacy_round_rejects_the_slice_alone(
    world: World,
) -> None:
    world.slice("L1")
    world.slice("L2")
    world.bad_slices = {"LeanDLRA.Literature.L1"}
    world.run_gate()
    assert world.lines("REJECT") == ["REJECT L1: lake build --wfail failed"]
    assert world.subjects()[0] == "Add 1 slice (L2)"


def test_every_group_rejected_leaves_a_clean_tree(world: World) -> None:
    world.group("g1", ["A"])
    world.bad_slices = {"LeanDLRA.Literature.A"}
    base = world.head()
    assert world.run_gate() == 0
    assert world.head() == base
    assert world.status() == ""
    assert not (world.root / "wip/gate.round.json").exists()
    assert world.commands(*gate.PUSH) == []


def test_build_failure_that_names_no_slice_fails_the_round(world: World) -> None:
    world.group("g1", ["A"])
    world.anonymous_failure = True
    world.run_gate()
    assert world.lines("ROUNDFAIL") == [
        "ROUNDFAIL slice build: lake build --wfail failed"
    ]
    assert world.lines("REJECT") == ["REJECT A: lake build --wfail failed"]
    assert world.status() == ""


# -- failures of a round --------------------------------------------------------------------------


def test_core_build_failure_of_one_group_rejects_it(world: World) -> None:
    world.group("g1", ["A", "B"])
    world.core_breakers = {"LeanDLRA.Literature.B"}
    base = world.head()
    assert world.run_gate() == 0
    assert world.lines("ROUNDFAIL") == ["ROUNDFAIL core build: core build failed"]
    assert world.lines("REJECT") == [
        "REJECT A: core build failed",
        "REJECT B: core build failed",
    ]
    assert "LeanDLRA.Literature.B breaks the library" in world.read(
        "wip/rejected/A.log"
    )
    assert world.lines("FALLBACK") == []
    assert world.head() == base
    assert world.status() == ""
    assert world.read("LeanDLRACatalogue.lean") == "import LeanDLRA\n"
    assert world.folder("rejected")[-1] == "g1.group"
    assert not (world.root / "wip/gate.round.json").exists()
    assert world.commands(*gate.TOOL, "discard") == [(*gate.TOOL, "discard")]


def test_round_failure_with_several_groups_falls_back_group_by_group(
    world: World,
) -> None:
    world.group("g1", ["A"])
    world.group("g2", ["B", "C"])
    world.group("g3", ["D"])
    world.core_breakers = {"LeanDLRA.Literature.C"}
    assert world.run_gate() == 0
    assert world.lines("FALLBACK") == [
        "FALLBACK core build: 3 groups one by one (g1, g2, g3)"
    ]
    assert world.lines("PUSHED") == ["PUSHED Add 1 slice (A)", "PUSHED Add 1 slice (D)"]
    assert world.lines("REJECT") == [
        "REJECT B: core build failed",
        "REJECT C: core build failed",
    ]
    order = [
        line.split()[0]
        for line in world.log()
        if line[9:].split()[0] in ("PUSHED", "REJECT")
    ]
    assert order == sorted(order)
    kinds = [line[9:].split()[0] for line in world.log()]
    assert kinds == [
        "gate",
        "ROUND",
        "ROUNDFAIL",
        "FALLBACK",
        "HASHDIFF",
        "CORE",
        "PUSHED",
        "ROUNDFAIL",
        "REJECT",
        "REJECT",
        "HASHDIFF",
        "CORE",
        "PUSHED",
    ]
    # The slice builds: the whole round, then each group alone, in the order of the queue.
    assert [c[3:] for c in world.slice_builds()] == [
        tuple(f"LeanDLRA.Literature.{c}" for c in "ABCD"),
        ("LeanDLRA.Literature.A",),
        ("LeanDLRA.Literature.B", "LeanDLRA.Literature.C"),
        ("LeanDLRA.Literature.D",),
    ]
    assert world.subjects()[:2] == ["Add 1 slice (D)", "Add 1 slice (A)"]
    assert world.status() == ""
    assert sorted(p.name for p in (world.root / LIT).iterdir()) == ["A.lean", "D.lean"]
    assert world.read("LeanDLRACatalogue.lean").splitlines() == [
        "import LeanDLRA",
        "import LeanDLRA.Literature.A",
        "import LeanDLRA.Literature.D",
    ]


def test_tree_is_restored_between_the_round_and_the_fallback(world: World) -> None:
    world.group("g1", ["A"])
    world.group("g2", ["B"])
    world.core_breakers = {"LeanDLRA.Literature.B"}
    seen: list[list[str]] = []
    inner = world.__call__

    def spy(*cmd: str, timeout: int = 14400) -> tuple[int, str]:
        if cmd[:3] == ("lake", "build", "--wfail") and cmd != gate.CORE_BUILD:
            seen.append(sorted(p.name for p in (world.root / LIT).glob("*.lean")))
        return inner(*cmd, timeout=timeout)

    gate.Gate(world.root, spy).loop(12, True, 6, 0.0)
    assert seen == [["A.lean", "B.lean"], ["A.lean"], ["A.lean", "B.lean"]]


def test_target_outside_the_library_is_rejected(world: World) -> None:
    world.slice("Tool", target="scripts/Tool.lean")
    world.slice("Root", target="LeanDLRA.lean")
    world.group("g1", ["Tool"])
    world.group("g2", ["Root"])
    world.group("g3", ["A"])
    before = world.read("LeanDLRA.lean")
    world.run_gate()
    assert world.lines("REJECT") == [
        "REJECT Tool: target outside the library: scripts/Tool.lean",
        "REJECT Root: target outside the library: LeanDLRA.lean",
    ]
    assert not (world.root / "scripts/Tool.lean").exists()
    assert world.lines("PUSHED") == ["PUSHED Add 1 slice (A)"]
    assert world.slice_builds() == [
        ("lake", "build", "--wfail", "LeanDLRA.Literature.A")
    ]
    assert before is not None and before in (world.read("LeanDLRA.lean") or "")


def test_core_check_failure(world: World) -> None:
    world.slice("Core", target="LeanDLRA/Analysis/Core.lean")
    world.group("g1", ["Core"])
    world.core_check_bad = {"LeanDLRA.Analysis.Core"}
    world.run_gate()
    assert world.lines("REJECT") == [
        "REJECT Core: core module imports a catalogue module"
    ]
    assert "imports LeanDLRA.Literature.X" in world.read("wip/rejected/Core.log")
    assert world.commands(*gate.CORE_BUILD) == []
    assert world.status() == ""
    assert world.read("LeanDLRA.lean") == "import LeanDLRA.Base\n"


def test_audit_failure_rejects_and_restores(world: World) -> None:
    world.group("g1", ["A"])
    world.group("g2", ["B"])
    world.audit_bad = {"LeanDLRA.Literature.A"}
    assert world.run_gate() == 0
    assert world.lines("REJECT") == ["REJECT A: audit failed"]
    assert world.lines("PUSHED") == ["PUSHED Add 1 slice (B)"]
    assert world.lines("STOP") == []
    assert world.commands("scripts/audit.sh")[0] == (
        "scripts/audit.sh",
        "LeanDLRA",
        "LeanDLRA.Literature.A",
        "LeanDLRA.Literature.B",
    )


def test_failed_round_restores_root_files_as_committed(world: World) -> None:
    # A root file that was committed out of step with the generator: a failed round must leave
    # it as it is on main (the tree is `HEAD` again), or the next preflight would stop the gate.
    committed = world.read("LeanDLRA.lean") + "-- edited by hand\n"
    world.write("LeanDLRA.lean", committed)
    world.real("git", "commit", "-q", "-m", "root by hand", "--", "LeanDLRA.lean")
    world.seed()
    world.group("g1", ["A"])
    world.audit_bad = {"LeanDLRA.Literature.A"}
    assert world.run_gate() == 0
    assert world.lines("REJECT") == ["REJECT A: audit failed"]
    assert world.read("LeanDLRA.lean") == committed
    assert world.status() == ""
    assert world.lines("STOP") == []
    world.group("g2", ["B"])
    assert world.run_gate() == 0
    assert world.lines("PUSHED") == ["PUSHED Add 1 slice (B)"]


def test_fidelity_failure_rejects_and_restores_the_rename_map(world: World) -> None:
    before = world.read("docs/renames.json")
    world.group("g1", ["A"], renames={"thm.old": "thm.new"})
    world.unfaithful = {"LeanDLRA.Literature.A"}
    base = world.head()
    assert world.run_gate() == 0
    assert world.lines("ROUNDFAIL") == ["ROUNDFAIL fidelity: fidelity check failed"]
    assert world.lines("REJECT") == ["REJECT A: fidelity check failed"]
    assert "missing: thm_of_LeanDLRA.Literature.A" in world.read("wip/rejected/A.log")
    assert world.read("docs/renames.json") == before
    assert world.head() == base
    assert world.status() == ""
    assert world.commands(*gate.PUSH) == []


def test_fidelity_runs_after_the_rename_map_is_merged(world: World) -> None:
    world.group("g1", ["A"], renames={"thm.old": "thm.new"})
    seen: list[dict[str, str]] = []
    inner = world.__call__

    def spy(*cmd: str, timeout: int = 14400) -> tuple[int, str]:
        if cmd == (*gate.TOOL, "fidelity"):
            seen.append(json.loads(world.read("docs/renames.json")))
        return inner(*cmd, timeout=timeout)

    gate.Gate(world.root, spy).loop(12, True, 6, 0.0)
    assert seen == [{"Old.a": "New.a", "thm.old": "thm.new"}]


def test_renames_are_committed_with_the_slices(world: World) -> None:
    world.group("g1", ["A"], renames={"thm.old": "thm.new"})
    world.group("g2", ["B"], renames={"thm.new": "thm.newer"})
    world.run_gate()
    assert world.committed_files() == [
        f"{LIT}/A.lean",
        f"{LIT}/B.lean",
        "LeanDLRACatalogue.lean",
        "docs/renames.json",
    ]
    text = world.read("docs/renames.json")
    assert json.loads(text) == {
        "Old.a": "New.a",
        "thm.old": "thm.new",
        "thm.new": "thm.newer",
    }
    assert text == json.dumps(json.loads(text), indent=2, ensure_ascii=False) + "\n"
    assert world.status() == ""


def test_round_without_renames_leaves_the_rename_map_alone(world: World) -> None:
    world.group("g1", ["A"])
    world.run_gate()
    assert "docs/renames.json" not in world.committed_files()


@pytest.mark.parametrize(
    ("renames", "reason"),
    [
        (
            {"Old.a": "Other.a"},
            "renames: Old.a is already mapped to New.a, not to Other.a",
        ),
        ({"New.a": "Old.a"}, "renames: cycle: Old.a -> New.a -> Old.a"),
    ],
)
def test_conflicting_renames_reject_the_group_before_anything_is_built(
    world: World, renames: dict[str, str], reason: str
) -> None:
    world.group("g1", ["A"], renames=renames)
    world.group("g2", ["B"])
    world.run_gate()
    assert world.lines("REJECT") == [f"REJECT A: {reason}"]
    assert world.slice_builds() == [
        ("lake", "build", "--wfail", "LeanDLRA.Literature.B")
    ]
    assert json.loads(world.read("docs/renames.json")) == {"Old.a": "New.a"}


def test_renames_of_two_groups_that_conflict_reject_the_later_group(
    world: World,
) -> None:
    world.group("g1", ["A"], renames={"x": "y"})
    world.group("g2", ["B"], renames={"x": "z"})
    world.run_gate()
    assert world.lines("REJECT") == [
        "REJECT B: renames: x is already mapped to y, not to z"
    ]
    assert world.lines("PUSHED") == ["PUSHED Add 1 slice (A)"]


# -- hashdiff -------------------------------------------------------------------------------------


def test_hashdiff_is_logged_for_groups_without_expectation(world: World) -> None:
    world.group("g1", ["A"])
    world.changed = {"LeanDLRA.Literature.A": 5}
    world.removed = {"LeanDLRA.Literature.A": 2}
    world.run_gate()
    assert world.lines("PUSHED") == ["PUSHED Add 1 slice (A)"]
    assert re.fullmatch(
        r"HASHDIFF abc1234\.\.[0-9a-f]{7,}: 100 declarations, 5 changed, 0 moved, 1 added, 2 removed",
        world.lines("HASHDIFF")[0],
    )


def test_hashdiff_within_the_expectation(world: World) -> None:
    world.group("g1", ["A"], expect_changed=3)
    world.changed = {"LeanDLRA.Literature.A": 2}
    world.removed = {"LeanDLRA.Literature.A": 1}
    world.run_gate()
    assert world.lines("PUSHED") == ["PUSHED Add 1 slice (A)"]


def test_hashdiff_beyond_the_expectation_rejects(world: World) -> None:
    world.group("g1", ["A"], expect_changed=0)
    world.changed = {"LeanDLRA.Literature.A": 2}
    base = world.head()
    world.run_gate()
    assert world.lines("HASHDIFF") == [
        "HASHDIFF abc1234..rejected: 100 declarations, 2 changed, 0 moved, 1 added, 0 removed"
    ]
    report = f"{gate.HASHDIR}/report_abc1234..rejected_A.md"
    assert world.lines("REJECT") == [
        f"REJECT A: hashdiff: 2 changed and 0 removed declarations, at most 0 expected (report: {report})"
    ]
    assert (world.root / report).exists()
    assert world.head() == base
    assert world.status() == ""


def test_hashdiff_fallback_finds_the_group(world: World) -> None:
    world.group("g1", ["A"], expect_changed=1)
    world.group("g2", ["B"], expect_changed=0)
    world.changed = {"LeanDLRA.Literature.A": 1, "LeanDLRA.Literature.B": 3}
    world.run_gate()
    assert world.lines("FALLBACK") == [
        "FALLBACK hashdiff: 2 groups one by one (g1, g2)"
    ]
    assert world.lines("PUSHED") == ["PUSHED Add 1 slice (A)"]
    assert world.lines("REJECT")[0].startswith(
        "REJECT B: hashdiff: 3 changed and 0 removed"
    )


def test_expectations_of_a_round_are_added_up(world: World) -> None:
    world.group("g1", ["A"], expect_changed=2)
    world.group("g2", ["B"], expect_changed=1)
    world.changed = {"LeanDLRA.Literature.A": 2, "LeanDLRA.Literature.B": 1}
    world.run_gate()
    assert world.lines("PUSHED") == ["PUSHED Add 2 slices (A, B)"]
    assert world.lines("FALLBACK") == []


# -- promotion to the core ------------------------------------------------------------------------


def test_promote_adds_the_module_to_the_core(world: World) -> None:
    world.group("g1", ["A", "B"], promote=["LeanDLRA.Literature.A"])
    world.run_gate()
    assert world.read("docs/promoted.txt") == (
        "# promoted catalogue modules\nLeanDLRA.Literature.A\n"
    )
    assert world.committed_files() == [
        "LeanDLRA.lean",
        f"{LIT}/A.lean",
        f"{LIT}/B.lean",
        "LeanDLRACatalogue.lean",
        "docs/promoted.txt",
    ]
    assert (
        world.read("LeanDLRA.lean")
        == "import LeanDLRA.Base\nimport LeanDLRA.Literature.A\n"
    )
    assert (
        world.read("LeanDLRACatalogue.lean")
        == "import LeanDLRA\nimport LeanDLRA.Literature.B\n"
    )
    assert world.lines("CORE")[0].endswith(
        ": 2 core modules, 1 slice modules in the catalogue"
    )
    assert world.status() == ""


def test_promote_skips_listed_modules_and_accepts_landed_ones(world: World) -> None:
    world.group("g1", ["A"], promote=["LeanDLRA.Literature.A"])
    world.run_gate()
    world.group("g2", ["B"], promote=["LeanDLRA.Literature.A", "LeanDLRA.Literature.B"])
    world.group("g3", ["C"], promote=["LeanDLRA.Literature.B"])
    world.run_gate()
    assert world.read("docs/promoted.txt").splitlines()[1:] == [
        "LeanDLRA.Literature.A",
        "LeanDLRA.Literature.B",
    ]
    assert world.lines("REJECT") == []


def test_promote_is_restored_when_the_round_fails(world: World) -> None:
    before = world.read("docs/promoted.txt")
    world.group("g1", ["A"], promote=["LeanDLRA.Literature.A"])
    world.core_check_bad = {"LeanDLRA.Literature.A"}
    world.run_gate()
    assert world.lines("REJECT") == ["REJECT A: core module imports a catalogue module"]
    assert world.read("docs/promoted.txt") == before
    assert world.read("LeanDLRA.lean") == "import LeanDLRA.Base\n"
    assert world.status() == ""


def test_promote_of_an_unknown_module_rejects_the_group(world: World) -> None:
    world.group("g1", ["A"], promote=["LeanDLRA.Literature.Nowhere"])
    world.run_gate()
    assert world.lines("REJECT") == [
        "REJECT A: promote: LeanDLRA.Literature.Nowhere is neither in the group nor on main"
    ]
    assert world.commands("lake") == []


# -- markers that cannot be used ------------------------------------------------------------------


def test_marker_naming_a_missing_file_is_rejected_with_its_files(world: World) -> None:
    world.slice("A")
    world.slice("B", queue=False)
    world.group("g1", ["A"])
    marker = {"files": ["A.lean", "B.lean"]}
    world.write("wip/ready/g1.group", json.dumps(marker))
    world.group("g2", ["C"])
    assert world.run_gate() == 0
    assert world.lines("BADGROUP") == ["BADGROUP g1: B.lean is not in wip/ready"]
    assert world.lines("REJECT") == [
        "REJECT A: group marker g1.group: B.lean is not in wip/ready"
    ]
    assert world.folder("rejected") == ["A.lean", "A.log", "g1.group"]
    assert world.lines("PUSHED") == ["PUSHED Add 1 slice (C)"]


def test_marker_that_is_not_json_is_set_aside(world: World) -> None:
    world.slice("A")
    world.write("wip/ready/g1.group", "{")
    os.utime(world.root / "wip/ready/A.lean")
    assert world.run_gate(grace=120.0) == 0
    assert world.lines("BADGROUP")[0].startswith("BADGROUP g1: not JSON")
    assert world.folder("rejected") == ["g1.group"]
    # Its files are not known: they are taken as loose files once they are old enough.
    assert world.ready() == ["A.lean"]
    assert world.run_gate(grace=0.0) == 0
    assert world.lines("ROUND") == ["ROUND 1 group(s): legacy (A)"]


# -- stops ----------------------------------------------------------------------------------------


def test_gate_refuses_to_start_without_the_rolling_dump(world: World) -> None:
    (world.root / gate.HASHDIR / gate.ROLLING[0]).unlink()
    world.group("g1", ["A"])
    assert world.run_gate() == 1
    assert world.lines("STOP") == [
        (
            f"STOP: {gate.HASHDIR}/rolling.jsonl.gz is missing: build everything, then seed it "
            "with `uv run -q scripts/rolling.py seed`"
        )
    ]
    assert world.log()[-1].endswith("gate stopped, see above")
    assert world.commands("lake") == []
    assert world.ready() == ["A.lean", "g1.group"]


def test_gate_refuses_a_rolling_dump_of_another_library_commit(world: World) -> None:
    world.write("LeanDLRA/Base.lean", "def base := 2\n")
    world.real("git", "commit", "-q", "-am", "manual change of the library")
    world.group("g1", ["A"])
    assert world.run_gate() == 1
    assert "refresh the changed modules" in world.lines("STOP")[0]
    assert world.commands("lake") == []


def test_commits_outside_the_library_do_not_make_the_dump_stale(world: World) -> None:
    world.write("docs/notes.md", "notes\n")
    world.real("git", "add", "docs/notes.md")
    world.real("git", "commit", "-q", "-m", "notes")
    world.group("g1", ["A"])
    assert world.run_gate() == 0
    assert world.lines("PUSHED") == ["PUSHED Add 1 slice (A)"]


@pytest.mark.parametrize(
    "rel", ["LeanDLRA/Base.lean", "LeanDLRA/Stray.lean", "LeanDLRA.lean"]
)
def test_gate_refuses_a_library_tree_that_is_not_head(world: World, rel: str) -> None:
    world.write(rel, "def stray := 1\n")
    world.group("g1", ["A"])
    assert world.run_gate() == 1
    assert world.lines("STOP")[0].startswith("STOP: the library tree differs from HEAD")
    assert world.commands("lake") == []


def test_push_failure_stops_and_the_next_start_publishes(world: World) -> None:
    world.group("g1", ["A"])
    world.push_code = 1
    assert world.run_gate() == 1
    assert world.lines("STOP")[0].startswith("STOP: push failed")
    assert world.lines("PUSHED") == []
    assert world.subjects()[0] == "Add 1 slice (A)"
    assert (world.root / "wip/gate.round.json").exists()
    assert world.ready() == ["A.lean", "g1.group"]
    assert world.commands(*gate.TOOL, "accept") == []

    world.push_code = 0
    world.calls.clear()
    assert world.run_gate() == 0
    assert world.lines("RECOVER") == [
        "RECOVER publishing the committed round: Add 1 slice (A)"
    ]
    assert world.lines("PUSHED") == ["PUSHED Add 1 slice (A)"]
    assert len(world.lines("HASHDIFF")) == 1
    assert len(world.lines("CORE")) == 1
    assert world.commands(*gate.TOOL, "accept") == [(*gate.TOOL, "accept")]
    assert world.commands("lake") == []
    assert world.folder("done") == ["A.lean", "g1.group"]
    assert not (world.root / "wip/gate.round.json").exists()


@pytest.mark.parametrize("command", ["dump", "fidelity", "diff"])
def test_check_that_cannot_run_stops_the_gate_and_rejects_nothing(
    world: World, command: str
) -> None:
    world.group("g1", ["A"])
    world.tool_broken = command
    base = world.head()
    assert world.run_gate() == 1
    assert world.lines("REJECT") == []
    assert world.lines("STOP")[0].endswith(f"rolling: cannot run {command}")
    assert world.head() == base
    assert world.ready() == ["A.lean", "g1.group"]
    # The next start takes the round out of the tree and tries again.
    world.tool_broken = ""
    assert world.run_gate() == 0
    assert world.lines("RECOVER") == [
        "RECOVER restoring 1 targets of an interrupted round (A)"
    ]
    assert world.lines("PUSHED") == ["PUSHED Add 1 slice (A)"]


def test_slices_identical_to_main_are_rejected_not_committed(world: World) -> None:
    world.group("g1", ["A"])
    world.run_gate()
    head = world.head()
    world.group("g2", ["A"])
    assert world.run_gate() == 0
    assert world.lines("REJECT") == [
        "REJECT A: nothing to commit: every slice is identical to main"
    ]
    assert world.head() == head
    assert world.status() == ""


# -- recovery after a kill ------------------------------------------------------------------------


class Killed(Exception):
    """The gate process dies."""


def kill_at(world: World, *prefix: str, after: bool = False) -> None:
    """Run the gate and kill it before (or after) the first command with this prefix."""
    inner = world.__call__

    def runner(*cmd: str, timeout: int = 14400) -> tuple[int, str]:
        hit = cmd[: len(prefix)] == prefix
        if hit and not after:
            raise Killed
        result = inner(*cmd, timeout=timeout)
        if hit:
            raise Killed
        return result

    with pytest.raises(Killed):
        gate.Gate(world.root, runner).loop(12, True, 6, 0.0)


STAGES = [
    ("lake", "build", "--wfail"),
    ("scripts/gen_root.sh",),
    gate.CORE_BUILD,
    ("scripts/audit.sh",),
    (*gate.TOOL, "dump"),
    (*gate.TOOL, "fidelity"),
    (*gate.TOOL, "diff"),
    ("git", "commit"),
]


@pytest.mark.parametrize("stage", STAGES, ids=[" ".join(s[-2:]) for s in STAGES])
def test_kill_before_the_commit_is_undone_at_the_next_start(
    world: World, stage: tuple[str, ...]
) -> None:
    world.group("g1", ["A"])
    world.run_gate()
    landed = world.read(f"{LIT}/A.lean")
    before = {
        rel: world.read(rel) for rel in ("docs/renames.json", "docs/promoted.txt")
    }
    world.slice("A", text="theorem A : True := by trivial\n")
    world.group("g2", ["A", "B"], renames={"x": "y"}, promote=["LeanDLRA.Literature.B"])
    head = world.head()
    kill_at(world, *stage)
    assert (world.root / "wip/gate.round.json").exists()
    assert (world.root / f"{LIT}/B.lean").exists()

    world.bad_slices = {
        "LeanDLRA.Literature.B"
    }  # the round is not repeated successfully
    assert world.run_gate() == 0
    assert world.lines("RECOVER") == [
        "RECOVER restoring 2 targets of an interrupted round (A, B)"
    ]
    assert world.head() == head
    assert world.status() == ""
    assert world.read(f"{LIT}/A.lean") == landed
    assert not (world.root / f"{LIT}/B.lean").exists()
    assert {rel: world.read(rel) for rel in before} == before
    assert (
        world.read("LeanDLRACatalogue.lean")
        == "import LeanDLRA\nimport LeanDLRA.Literature.A\n"
    )
    assert not (world.root / "wip/gate.round.json").exists()


@pytest.mark.parametrize(
    "stage",
    [("git", "commit"), gate.PUSH, (*gate.TOOL, "accept")],
    ids=["commit", "push", "accept"],
)
def test_kill_after_the_commit_is_finished_at_the_next_start(
    world: World, stage: tuple[str, ...]
) -> None:
    world.group("g1", ["A"], renames={"x": "y"})
    kill_at(world, *stage, after=True)
    assert world.subjects()[0] == "Add 1 slice (A)"
    assert world.lines("PUSHED") == []
    world.calls.clear()
    assert world.run_gate() == 0
    assert world.lines("RECOVER") == [
        "RECOVER publishing the committed round: Add 1 slice (A)"
    ]
    assert world.lines("PUSHED") == ["PUSHED Add 1 slice (A)"]
    assert world.commands(*gate.PUSH) == [gate.PUSH]
    assert world.commands("lake") == []
    assert world.subjects()[:2] == ["Add 1 slice (A)", "start"]
    assert world.folder("done") == ["A.lean", "g1.group"]
    assert world.status() == ""


def test_committed_round_is_recognized_under_later_commits(world: World) -> None:
    world.group("g1", ["A"])
    kill_at(world, *gate.PUSH)
    world.write("docs/notes.md", "notes\n")
    world.real("git", "add", "docs/notes.md")
    world.real("git", "commit", "-q", "-m", "notes")
    assert world.run_gate() == 0
    assert world.lines("PUSHED") == ["PUSHED Add 1 slice (A)"]
    # The lines name the commit of the round, not the commit on top of it.
    sha = world.real("git", "rev-parse", "--short", "HEAD~1")[1].strip()
    assert world.lines("CORE") == [
        f"CORE {sha}: 1 core modules, 1 slice modules in the catalogue"
    ]
    assert world.lines("HASHDIFF")[0].split(":")[0].endswith(f"..{sha}")
    assert (world.root / f"{LIT}/A.lean").exists()


# -- dry run --------------------------------------------------------------------------------------


def snapshot(root: Path) -> dict[str, bytes]:
    return {
        str(p.relative_to(root)): p.read_bytes()
        for p in sorted(root.rglob("*"))
        if p.is_file() and ".git/" not in str(p.relative_to(root)) + "/"
    }


def test_dry_run_prints_the_round_and_changes_nothing(
    world: World, capsys: pytest.CaptureFixture[str]
) -> None:
    world.group("g1", ["A"])
    world.run_gate()
    world.slice("A", text="theorem A : True := by trivial\n")
    world.slice("Bad", text="theorem b : True := by sorry\n")
    world.group("g2", ["A", "B"], renames={"x": "y"}, expect_changed=0)
    world.group("g3", ["Bad", "C"])
    world.group("g4", ["D"], promote=["LeanDLRA.Literature.B"])
    world.slice("L1")
    world.calls.clear()
    before = snapshot(world.root)
    head = world.head()
    capsys.readouterr()
    gate.Gate(world.root, world, dry=True).plan(12, 6, 0.0)
    out = capsys.readouterr().out
    assert out.splitlines() == [
        "group g2: 2 file(s), 1 rename(s), expect_changed=0, promote=[]",
        f"  A -> {LIT}/A.lean (update)",
        f"  B -> {LIT}/B.lean (add)",
        "group g3: 2 file(s), 0 rename(s), expect_changed=None, promote=[]",
        "  would REJECT Bad: forbidden token in the source",
        "group g4: 1 file(s), 0 rename(s), expect_changed=None, promote=['LeanDLRA.Literature.B']",
        f"  D -> {LIT}/D.lean (add)",
        "group legacy: 1 file(s), 0 rename(s), expect_changed=None, promote=[]",
        f"  L1 -> {LIT}/L1.lean (add)",
        "commit: Add 4 slices (A, B, D, L1)",
        "left in the queue: 2 slice file(s)",
    ]
    assert snapshot(world.root) == before
    assert world.head() == head
    assert all(c[0] == "git" for c in world.calls)
    assert {c[1] for c in world.calls} <= {
        "--no-optional-locks",
        "cat-file",
        "rev-list",
    }


def test_dry_run_reports_a_missing_rolling_dump(
    world: World, capsys: pytest.CaptureFixture[str]
) -> None:
    (world.root / gate.HASHDIR / gate.ROLLING[1]).unlink()
    gate.Gate(world.root, world, dry=True).plan(12, 6, 0.0)
    out = capsys.readouterr().out.splitlines()
    assert out[0].startswith(
        "the gate would STOP: .lake/hashdiff/rolling_statements.jsonl.gz is missing"
    )
    assert out[-1] == "nothing to do"
