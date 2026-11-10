"""scripts/enqueue.sh in a throwaway tree: the marker, the checks, the lock."""

from __future__ import annotations

import json
import shutil
import subprocess
import time
from collections.abc import Sequence
from pathlib import Path

import gate
import pytest

HERE = Path(__file__).resolve().parent
SCRIPT = next(
    (
        p
        for p in (HERE.parent / "enqueue.sh", HERE.parent / "scripts/enqueue.sh")
        if p.exists()
    ),
    HERE.parent / "scripts/enqueue.sh",
)
KEYS = [f"S{i:02d}" for i in range(13)]

pytestmark = pytest.mark.skipif(
    shutil.which("zsh") is None or shutil.which("uv") is None, reason="needs zsh and uv"
)


class Tree:
    """A repository with the script, a manifest and unqueued slices in `wip/`."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self.ready = root / "wip/ready"
        (root / "scripts").mkdir()
        shutil.copy(SCRIPT, root / "scripts/enqueue.sh")
        (root / "wip").mkdir()
        table = {k: {"target": f"LeanDLRA/Literature/{k}.lean"} for k in KEYS}
        (root / "wip/manifest.json").write_text(json.dumps(table, indent=2))
        for k in KEYS:
            (root / f"wip/{k}.lean").write_text(
                f"theorem {k.lower()} : True := trivial\n"
            )

    def start(self, *args: str) -> subprocess.Popen[str]:
        return subprocess.Popen(
            ["zsh", "scripts/enqueue.sh", *args],
            cwd=self.root,
            env={**__import__("os").environ, "ENQUEUE_POLL": "0.2"},
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )

    def run(self, *args: str) -> tuple[int, str, str]:
        proc = self.start(*args)
        out, err = proc.communicate(timeout=60)
        return proc.returncode, out, err

    def queue(self) -> list[str]:
        """Everything in `wip/ready`, hidden files included."""
        return (
            sorted(p.name for p in self.ready.iterdir()) if self.ready.exists() else []
        )

    def marker(self, gid: str) -> gate.Group:
        path = self.ready / f"{gid}.group"
        parsed = gate.parse_marker(path.name, path.read_text(), path.stat().st_mtime)
        assert isinstance(parsed, gate.Group), parsed
        return parsed


@pytest.fixture
def tree(tmp_path: Path) -> Tree:
    return Tree(tmp_path)


def slices(keys: Sequence[str]) -> list[str]:
    return [f"wip/{k}.lean" for k in keys]


def finish(proc: subprocess.Popen[str]) -> tuple[int, str, str]:
    out, err = proc.communicate(timeout=60)
    return proc.returncode, out, err


# -- queueing -------------------------------------------------------------------------------------


def test_group_is_queued_with_its_marker(tree: Tree) -> None:
    code, out, err = tree.run("--id", "g1", "wip/S01.lean", "wip/S00.lean")
    assert (code, err) == (0, "")
    assert out.startswith("enqueue: queued 2 file(s) at ")
    assert out.rstrip().endswith(": S01, S00 (group g1)")
    # Nothing but the files and the marker: no staging folder, no partial marker, no lock.
    assert tree.queue() == ["S00.lean", "S01.lean", "g1.group"]
    assert not (tree.root / "wip/enqueue.lock").exists()
    assert (tree.ready / "S01.lean").read_text() == (
        tree.root / "wip/S01.lean"
    ).read_text()
    raw = json.loads((tree.ready / "g1.group").read_text())
    assert list(raw) == ["id", "files", "queued"]
    assert (raw["id"], raw["files"]) == ("g1", ["S01.lean", "S00.lean"])
    group = tree.marker("g1")
    assert group.files == ("S01.lean", "S00.lean")  # the order of the command line
    assert (group.renames, group.expect_changed, group.promote) == ({}, None, ())
    assert group.atomic


def test_default_name_and_no_waiting_for_other_groups(tree: Tree) -> None:
    assert tree.run("wip/S00.lean")[0] == 0
    started = time.monotonic()
    assert tree.run("wip/S01.lean", "wip/S02.lean")[0] == 0  # the queue is not empty
    assert time.monotonic() - started < 10
    markers = [n for n in tree.queue() if n.endswith(".group")]
    assert len(markers) == 2
    groups = sorted(
        (tree.marker(m.removesuffix(".group")) for m in markers), key=lambda g: g.age
    )
    assert [g.files for g in groups] == [("S00.lean",), ("S01.lean", "S02.lean")]
    assert all(g.id != gate.LEGACY for g in groups)


def test_options_are_written_to_the_marker(tree: Tree) -> None:
    (tree.root / "wip/r.json").write_text('{"Old.name": "New.name", "A.b": "A.c"}')
    code, _, err = tree.run(
        "--renames",
        "wip/r.json",
        "--expect-changed=0",
        "--promote",
        "LeanDLRA.Literature.S00",
        "--promote=LeanDLRA.Literature.S01",
        "--id=moves",
        "--",
        *slices(KEYS[:2]),
    )
    assert (code, err) == (0, "")
    group = tree.marker("moves")
    assert group.renames == {"Old.name": "New.name", "A.b": "A.c"}
    assert group.expect_changed == 0
    assert group.promote == ("LeanDLRA.Literature.S00", "LeanDLRA.Literature.S01")
    raw = json.loads((tree.ready / "moves.group").read_text())
    assert list(raw) == [
        "id",
        "files",
        "renames",
        "expect_changed",
        "promote",
        "queued",
    ]


def test_twelve_files_are_the_limit(tree: Tree) -> None:
    assert tree.run("--id", "big", *slices(KEYS[:12]))[0] == 0
    assert len(tree.marker("big").files) == 12
    code, _, err = tree.run("--id", "bigger", *slices(KEYS))
    assert code == 2
    assert "1 to 12 files" in err
    assert "bigger.group" not in tree.queue()


@pytest.mark.parametrize(
    ("args", "message"),
    [
        ([], "usage:"),
        (["--id", "x"], "usage:"),
        (["wip/Nope.lean"], "not a slice file: wip/Nope.lean"),
        (["wip/manifest.json"], "not a slice file: wip/manifest.json"),
        (["wip/Unknown.lean"], "no entry in wip/manifest.json for Unknown"),
        (["wip/S00.lean", "wip/other/S00.lean"], "the same file name twice"),
        (
            ["--expect-changed", "few", "wip/S00.lean"],
            "--expect-changed: not a number: few",
        ),
        (
            ["--expect-changed", "-1", "wip/S00.lean"],
            "--expect-changed: not a number: -1",
        ),
        (["--promote", "Mathlib.Data", "wip/S00.lean"], "--promote: not a module name"),
        (["--promote", "LeanDLRA", "wip/S00.lean"], "--promote: not a module name"),
        (["--renames", "wip/none.json", "wip/S00.lean"], "--renames: no such file"),
        (["--renames", "wip/list.json", "wip/S00.lean"], "expected a JSON object"),
        (["--renames", "wip/same.json", "wip/S00.lean"], "expected a JSON object"),
        (
            ["--renames", "wip/broken.json", "wip/S00.lean"],
            "--renames wip/broken.json:",
        ),
        (["--id", "a/b", "wip/S00.lean"], "--id: not a group name: a/b"),
        (["--id", ".hidden", "wip/S00.lean"], "--id: not a group name"),
        (["--id", "legacy", "wip/S00.lean"], "--id: not a group name: legacy"),
        (["--id", "taken", "wip/S00.lean"], "a group taken is already queued"),
        (["--force", "wip/S00.lean"], "unknown option --force"),
        (["wip/S00.lean", "--renames"], "usage:"),
    ],
)
def test_bad_arguments_queue_nothing(tree: Tree, args: list[str], message: str) -> None:
    (tree.root / "wip/Unknown.lean").write_text("-- no manifest entry\n")
    (tree.root / "wip/other").mkdir()
    (tree.root / "wip/other/S00.lean").write_text("-- same name\n")
    (tree.root / "wip/list.json").write_text('["a", "b"]')
    (tree.root / "wip/same.json").write_text('{"a": "a"}')
    (tree.root / "wip/broken.json").write_text('{"a": ')
    tree.ready.mkdir()
    (tree.ready / "taken.group").write_text("{}")
    code, out, err = tree.run(*args)
    assert (code, out) == (2, "")
    assert message in err
    assert tree.queue() == ["taken.group"]
    assert not (tree.root / "wip/enqueue.lock").exists()


# -- waiting --------------------------------------------------------------------------------------


def test_maintenance_hold_keeps_groups_back(tree: Tree) -> None:
    (tree.root / "wip/enqueue.lock").mkdir()
    proc = tree.start("--id", "held", "wip/S00.lean")
    time.sleep(1.5)
    assert proc.poll() is None
    assert tree.queue() == []
    (tree.root / "wip/enqueue.lock").rmdir()
    assert finish(proc)[0] == 0
    assert tree.queue() == ["S00.lean", "held.group"]
    assert not (tree.root / "wip/enqueue.lock").exists()


def test_waits_while_a_file_of_the_same_name_is_queued(tree: Tree) -> None:
    assert tree.run("--id", "first", "wip/S00.lean")[0] == 0
    (tree.root / "wip/S00.lean").write_text("theorem s00 : 1 = 1 := rfl\n")
    proc = tree.start("--id", "second", "wip/S00.lean", "wip/S01.lean")
    time.sleep(1.5)
    assert proc.poll() is None
    assert tree.queue() == [
        "S00.lean",
        "first.group",
    ]  # nothing of the second group yet
    assert not (tree.root / "wip/enqueue.lock").exists()  # others are not held up
    assert tree.run("--id", "third", "wip/S02.lean")[0] == 0
    # The gate takes the first group out of the queue.
    (tree.ready / "S00.lean").unlink()
    (tree.ready / "first.group").unlink()
    code, out, err = finish(proc)
    assert code == 0
    assert err.count("\n") == 1  # said once
    assert "enqueue: waiting, still queued from an earlier group: S00.lean" in err
    assert "(group second)" in out
    assert tree.queue() == [
        "S00.lean",
        "S01.lean",
        "S02.lean",
        "second.group",
        "third.group",
    ]
    assert (tree.ready / "S00.lean").read_text() == "theorem s00 : 1 = 1 := rfl\n"


def test_interrupted_while_waiting_leaves_nothing(tree: Tree) -> None:
    (tree.root / "wip/enqueue.lock").mkdir()
    proc = tree.start("--id", "gone", "wip/S00.lean")
    time.sleep(1.0)
    proc.terminate()
    assert finish(proc)[0] == 130
    assert tree.queue() == []
    assert (tree.root / "wip/enqueue.lock").is_dir()  # the hold of somebody else stays


def test_groups_queued_at_the_same_time_stay_whole(tree: Tree) -> None:
    procs = [
        tree.start("--id", f"p{i}", *slices(KEYS[3 * i : 3 * i + 3])) for i in range(4)
    ]
    assert [finish(p)[0] for p in procs] == [0, 0, 0, 0]
    assert tree.queue() == sorted(
        [f"{k}.lean" for k in KEYS[:12]] + [f"p{i}.group" for i in range(4)]
    )
    assert not (tree.root / "wip/enqueue.lock").exists()
    # The gate's selection sees four whole groups and no loose file.
    files = {p.name: p.stat().st_mtime for p in tree.ready.glob("*.lean")}
    markers = [tree.marker(f"p{i}") for i in range(4)]
    targets = {k: f"LeanDLRA/Literature/{k}.lean" for k in KEYS}
    selection = gate.select_round(files, markers, targets, 12, 6, time.time(), 120.0)
    assert selection.bad == []
    assert sorted(g.id for g in selection.groups) == ["p0", "p1", "p2", "p3"]
    assert sum(len(g.files) for g in selection.groups) == 12
