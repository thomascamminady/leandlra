"""scripts/rolling.py with a fake dumper: partial fidelity and hashdiff on a rolling dump."""

from __future__ import annotations

import dataclasses
import json
import subprocess
import sys
from collections.abc import Iterator, Sequence
from pathlib import Path

import fidelity
import gate
import pytest
import rolling

CORE_A, CORE_B = "LeanDLRA.Core.A", "LeanDLRA.Core.B"
LIT_X, LIT_Y, LIT_Z = (
    "LeanDLRA.Literature.X",
    "LeanDLRA.Literature.Y",
    "LeanDLRA.Literature.Z",
)

Decl = tuple[str, str, str, str | None]  # name, kind, type, body


def thm(name: str, typ: str) -> Decl:
    return (name, "theorem", typ, None)


def define(name: str, typ: str, body: str) -> Decl:
    return (name, "def", typ, body)


class Library:
    """The compiled library as the dumper sees it: module -> declarations."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self.modules: dict[str, list[Decl]] = {
            CORE_A: [thm("core_a", "1 = 1"), define("f", "Nat", "fun x => x")],
            CORE_B: [thm("core_b", "f = f")],
            LIT_X: [
                thm("lit_x", "2 = 2"),
                thm("_private.LeanDLRA.Literature.X.0.aux", "True"),
            ],
            LIT_Y: [thm("lit_y", "3 = 3")],
        }
        self.dumper_calls: list[tuple[tuple[str, ...], bool]] = []
        (root / "docs").mkdir()
        self.write_roots([CORE_A, CORE_B], [LIT_X, LIT_Y])
        self.record(["core_a", "core_b", "lit_x", "lit_y"])
        self.renames({})

    def write_roots(self, core: Sequence[str], rest: Sequence[str]) -> None:
        (self.root / "LeanDLRA.lean").write_text("".join(f"import {m}\n" for m in core))
        (self.root / "LeanDLRACatalogue.lean").write_text(
            "import LeanDLRA\n" + "".join(f"import {m}\n" for m in rest)
        )

    def record(self, names: Sequence[str]) -> None:
        """Record the present statements of the given theorems as the baseline."""
        types = {d[0]: d[2] for decls in self.modules.values() for d in decls}
        table = {name: fidelity.sha256(types[name]) for name in names}
        (self.root / "docs/statements.json").write_text(json.dumps(table))

    def renames(self, table: dict[str, str]) -> None:
        (self.root / "docs/renames.json").write_text(json.dumps(table))

    def dumper(
        self, root: Path, modules: Sequence[str], canonical: bool
    ) -> Iterator[str]:
        """What `scripts/DumpTypes.lean [--canonical] --modules ...` prints."""
        assert root == self.root
        self.dumper_calls.append((tuple(modules), canonical))
        for module in modules:
            for name, kind, typ, body in self.modules[
                module
            ]:  # KeyError: no such .olean
                private = name.startswith("_private.")
                if canonical:
                    shown = "_priv." + name.rsplit(".", 1)[1] if private else name
                    rec = {
                        "kind": kind,
                        "module": module,
                        "name": shown,
                        "type": f"C[{typ}]",
                    }
                    if body is not None:
                        rec["value"] = body
                    yield (
                        json.dumps(rec, ensure_ascii=False, separators=(",", ":"))
                        + "\n"
                    )
                elif kind == "theorem":
                    rec = {"name": name, "type": typ}
                    yield (
                        json.dumps(rec, ensure_ascii=False, separators=(",", ":"))
                        + "\n"
                    )

    def round(self, *slices: str) -> None:
        """What the gate does before the checks of a round."""
        rolling.dump(*slices)

    def fidelity(self) -> tuple[str, list[str]]:
        return rolling.check_statements(
            self.root, self.root / "docs/renames.json", 1 << 16
        )

    def diff(self) -> rolling.hashdiff.Result:
        return rolling.compare_round(self.root, self.root / "docs/renames.json", 40)[0]

    def rolling_names(self, name: str = rolling.ROLLING) -> dict[str, str]:
        """Name -> module in a rolling file."""
        return {
            json.loads(line)["name"]: json.loads(line)["module"]
            for line in rolling.lines_of(rolling.at(self.root, name))
        }


@pytest.fixture
def lib(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Library:
    library = Library(tmp_path)
    monkeypatch.setattr(rolling, "ROOT", tmp_path)
    monkeypatch.setattr(rolling, "run_dumper", library.dumper)
    monkeypatch.setattr(rolling, "build_current", lambda root, targets: None)
    rolling.seed()
    library.dumper_calls.clear()
    return library


# -- seeding --------------------------------------------------------------------------------------


def test_seed_dumps_every_module_in_both_forms(lib: Library) -> None:
    assert lib.rolling_names() == {
        "core_a": CORE_A,
        "f": CORE_A,
        "core_b": CORE_B,
        "lit_x": LIT_X,
        "_priv.aux": LIT_X,
        "lit_y": LIT_Y,
    }
    # Statements: theorems only, with the module of the canonical dump; no private names.
    assert lib.rolling_names(rolling.STATEMENTS) == {
        "core_a": CORE_A,
        "core_b": CORE_B,
        "lit_x": LIT_X,
        "lit_y": LIT_Y,
    }
    header = rolling.read_header(rolling.at(lib.root, rolling.ROLLING))
    assert header["format"] == rolling.hashdiff.FORMAT
    assert header["modules"] == 4
    summary, problems = lib.fidelity()
    assert problems == []
    assert summary == (
        "4 of 4 recorded statements proved verbatim (4 exactly, 0 via the rename map with 0 "
        "entries; 0 modules read in this round, the others from the rolling dump)"
    )


def test_seed_of_the_core_only(lib: Library) -> None:
    rolling.seed(lib="LeanDLRA")
    assert set(lib.rolling_names().values()) == {CORE_A, CORE_B}


def test_library_modules(lib: Library) -> None:
    assert rolling.library_modules(lib.root, "LeanDLRA") == [CORE_A, CORE_B]
    assert rolling.library_modules(lib.root, "LeanDLRACatalogue") == [
        CORE_A,
        CORE_B,
        LIT_X,
        LIT_Y,
    ]


# -- a round reads the core and its slices only ---------------------------------------------------


def test_round_reads_exactly_the_core_and_the_slices(lib: Library) -> None:
    del lib.modules[LIT_Y]  # a stale catalogue module: its .olean must not be asked for
    lib.round(LIT_X)
    assert lib.dumper_calls == [
        ((CORE_A, CORE_B, LIT_X), True),
        ((CORE_A, CORE_B, LIT_X), False),
    ]
    assert rolling.round_modules(lib.root) == {CORE_A, CORE_B, LIT_X}
    summary, problems = lib.fidelity()
    assert problems == []
    assert summary.startswith("4 of 4 recorded statements proved verbatim (4 exactly")
    assert "3 modules read in this round" in summary


def test_statement_that_disappears_from_the_core_is_missing(lib: Library) -> None:
    lib.modules[CORE_B] = []
    lib.round()
    assert lib.fidelity()[1] == ["missing: core_b"]


def test_statement_that_disappears_from_a_catalogue_slice_is_missing(
    lib: Library,
) -> None:
    lib.modules[LIT_X] = [thm("other", "True")]
    lib.round(LIT_X)
    assert lib.fidelity()[1] == ["missing: lit_x"]


def test_statement_of_an_untouched_catalogue_module_is_never_missing(
    lib: Library,
) -> None:
    lib.modules[LIT_X] = []  # changed on disk, but not a slice of this round
    lib.round(LIT_Y)
    assert lib.fidelity()[1] == []


def test_changed_statement_differs(lib: Library) -> None:
    lib.modules[LIT_X] = [thm("lit_x", "2 = 3")]
    lib.round(LIT_X)
    assert lib.fidelity()[1] == ["differs: lit_x"]


def test_statement_that_moves_between_modules_of_the_round_is_found(
    lib: Library,
) -> None:
    lib.modules[CORE_A].append(thm("lit_x", "2 = 2"))
    lib.modules[LIT_X] = []
    lib.round(LIT_X)
    assert lib.fidelity()[1] == []
    assert [m[0] for m in lib.diff().moved] == ["lit_x"]


def test_renamed_statement_is_found_through_the_rename_map(lib: Library) -> None:
    lib.modules[LIT_X] = [thm("lit_x_new", "2 = 2")]
    lib.round(LIT_X)
    assert lib.fidelity()[1] == ["missing: lit_x"]
    lib.renames({"lit_x": "lit_x_new"})
    summary, problems = lib.fidelity()
    assert problems == []
    assert "(3 exactly, 1 via the rename map with 1 entries" in summary


def test_new_slice_module_is_read(lib: Library) -> None:
    lib.modules[LIT_Z] = [thm("lit_z", "4 = 4")]
    lib.round(LIT_Z)
    lib.record(["core_a", "lit_z"])
    assert lib.fidelity()[1] == []


# -- diff -----------------------------------------------------------------------------------------


def test_diff_of_an_unchanged_round(lib: Library) -> None:
    lib.round(LIT_X)
    res = lib.diff()
    assert (res.before_count, res.after_count) == (5, 5)
    assert res.failures() == 0
    assert (res.appeared, res.moved) == ([], [])


def test_diff_counts_changes_of_the_round_modules_only(lib: Library) -> None:
    lib.modules[CORE_A] = [thm("core_a", "1 = 2"), define("f", "Nat", "fun x => x + 1")]
    lib.modules[CORE_B] = [thm("new_b", "True")]
    lib.modules[LIT_Y] = []  # not in the round: neither read nor counted as removed
    lib.round(LIT_X)
    res = lib.diff()
    assert res.type_changed == ["core_a"]
    assert res.value_changed == ["f"]
    assert [d[0] for d in res.disappeared] == ["core_b"]
    assert [a[0] for a in res.appeared] == ["new_b"]
    assert res.after_count == 5


def test_diff_applies_the_rename_map(lib: Library) -> None:
    lib.modules[CORE_A] = [thm("core_a", "1 = 1"), define("g", "Nat", "fun x => x")]
    lib.modules[CORE_B] = [thm("core_b", "g = g")]
    lib.round()
    assert lib.diff().failures() == 2  # f disappeared, core_b changed
    lib.renames({"f": "g"})
    res = lib.diff()
    assert res.failures() == 0
    assert res.renamed == [("f", "g")]


def test_diff_command_prints_the_counts_for_the_gate(
    lib: Library, capsys: pytest.CaptureFixture[str]
) -> None:
    lib.modules[CORE_A] = [thm("core_a", "1 = 2"), define("f", "Nat", "fun x => x")]
    lib.modules[LIT_Z] = [thm("lit_z", "4 = 4")]
    lib.modules[LIT_X] = [thm("lit_x", "2 = 2")]
    lib.round(LIT_X, LIT_Z)
    capsys.readouterr()
    rolling.diff(report=".lake/hashdiff/round_report.md")
    out = capsys.readouterr().out
    stats = gate.parse_stats(out)
    assert stats == gate.Stats("", 5, 1, 0, 1, 1)
    assert (
        (lib.root / ".lake/hashdiff/round_report.md")
        .read_text()
        .startswith("# Statement hash diff")
    )


def counts(capsys: pytest.CaptureFixture[str]) -> gate.Stats:
    """The numbers that `rolling.py diff` hands to the gate."""
    capsys.readouterr()
    rolling.diff()
    stats = gate.parse_stats(capsys.readouterr().out)
    assert stats is not None
    return stats


def with_settled_alias(lib: Library) -> None:
    """A library whose core kept `f` as a deprecated alias of `g` in an earlier round."""
    lib.modules[CORE_A] = [
        thm("core_a", "1 = 1"),
        define("g", "Nat", "fun x => x"),
        define("f", "Nat", "g"),
    ]
    lib.renames({"f": "g"})
    rolling.seed()


def test_settled_alias_is_not_counted_as_added(
    lib: Library, capsys: pytest.CaptureFixture[str]
) -> None:
    with_settled_alias(lib)
    lib.round(LIT_X)
    res = lib.diff()
    assert res.settled == [("f", CORE_A)]
    assert (res.aliases, res.appeared, res.renamed) == ([], [], [])
    assert counts(capsys) == gate.Stats("", 6, 0, 0, 0, 0)
    assert rolling.accept_round(lib.root)
    # The next round adds one theorem: one added, whatever aliases are standing.
    lib.modules[CORE_B].append(thm("new_b", "True"))
    lib.round()
    assert lib.diff().settled == [("f", CORE_A)]
    assert counts(capsys) == gate.Stats("", 5, 0, 0, 1, 0)


def test_new_alias_is_counted_as_added_in_its_round_only(
    lib: Library, capsys: pytest.CaptureFixture[str]
) -> None:
    lib.modules[CORE_A] = [
        thm("core_a", "1 = 1"),
        define("g", "Nat", "fun x => x"),
        define("f", "Nat", "g"),
    ]
    lib.modules[CORE_B] = [thm("core_b", "g = g")]
    lib.renames({"f": "g"})
    lib.round()
    res = lib.diff()
    assert res.renamed == [("f", "g")]
    assert res.aliases == [("f", CORE_A)]
    assert res.settled == []
    assert counts(capsys) == gate.Stats("", 4, 0, 0, 1, 0)
    assert rolling.accept_round(lib.root)
    lib.round()
    res = lib.diff()
    assert (res.renamed, res.aliases) == ([], [])
    assert res.settled == [("f", CORE_A)]
    assert counts(capsys) == gate.Stats("", 4, 0, 0, 0, 0)


def test_rename_without_alias_adds_nothing(
    lib: Library, capsys: pytest.CaptureFixture[str]
) -> None:
    lib.modules[CORE_A] = [thm("core_a", "1 = 1"), define("g", "Nat", "fun x => x")]
    lib.modules[CORE_B] = [thm("core_b", "g = g")]
    lib.round()
    # Without the map: `f` removed, `g` added, `core_b` changed.
    assert counts(capsys) == gate.Stats("", 3, 1, 0, 1, 1)
    lib.renames({"f": "g"})
    res = lib.diff()
    assert res.renamed == [("f", "g")]
    assert (res.aliases, res.settled, res.appeared) == ([], [], [])
    assert counts(capsys) == gate.Stats("", 3, 0, 0, 0, 0)


def test_settled_alias_that_moves_is_moved_not_added(
    lib: Library, capsys: pytest.CaptureFixture[str]
) -> None:
    with_settled_alias(lib)
    lib.modules[CORE_A] = [thm("core_a", "1 = 1"), define("g", "Nat", "fun x => x")]
    lib.modules[CORE_B] = [thm("core_b", "f = f"), define("f", "Nat", "g")]
    lib.round()
    res = lib.diff()
    assert res.settled == [("f", CORE_A)]
    assert res.moved == [("f", CORE_A, CORE_B)]
    assert counts(capsys) == gate.Stats("", 4, 0, 1, 0, 0)


def test_diff_line_has_exactly_the_fields_that_the_gate_reads(
    lib: Library, capsys: pytest.CaptureFixture[str]
) -> None:
    with_settled_alias(lib)
    lib.round()
    capsys.readouterr()
    rolling.diff()
    out = capsys.readouterr().out
    last = out.strip().splitlines()[-1]
    assert last.startswith("HASHDIFF {")
    fields = {f.name for f in dataclasses.fields(gate.Stats)}
    assert set(json.loads(last.removeprefix("HASHDIFF "))) == fields
    assert (
        "| deprecated alias of an earlier rename (in both dumps, not new) | 1 |" in out
    )
    assert "| appeared as deprecated alias (old name in the rename map) | 0 |" in out


def test_diff_without_a_round_cannot_run(lib: Library) -> None:
    with pytest.raises(rolling.ToolError, match="no dump of a round"):
        lib.diff()


# -- accept and discard ---------------------------------------------------------------------------


def test_accept_replaces_the_entries_of_the_round_modules(lib: Library) -> None:
    lib.modules[CORE_B] = [thm("core_b2", "True")]
    lib.modules[LIT_X] = [thm("lit_x", "2 = 2"), thm("lit_x2", "True")]
    lib.modules[LIT_Y] = []  # not in the round: its entries stay
    lib.round(LIT_X)
    assert rolling.accept_round(lib.root)
    expected = {
        "core_a": CORE_A,
        "f": CORE_A,
        "core_b2": CORE_B,
        "lit_x": LIT_X,
        "lit_x2": LIT_X,
        "lit_y": LIT_Y,
    }
    assert lib.rolling_names() == expected
    del expected["f"]
    assert lib.rolling_names(rolling.STATEMENTS) == expected
    header = rolling.read_header(rolling.at(lib.root, rolling.ROLLING))
    assert header["modules"] == 4
    assert rolling.round_modules(lib.root) == set()
    assert not rolling.accept_round(lib.root)
    # Without a round, fidelity reads the rolling dump alone.
    assert lib.fidelity()[1] == ["missing: core_b"]


def test_accept_can_be_repeated_after_a_kill(
    lib: Library, monkeypatch: pytest.MonkeyPatch
) -> None:
    lib.modules[LIT_X] = [thm("lit_x", "2 = 2"), thm("lit_x2", "True")]
    lib.round(LIT_X)
    real = rolling.write_lines
    calls = 0

    def dying(path: Path, header: dict[str, object], lines: Iterator[str]) -> int:
        nonlocal calls
        calls += 1
        if calls == 2:
            raise KeyboardInterrupt
        return real(path, header, lines)

    monkeypatch.setattr(rolling, "write_lines", dying)
    with pytest.raises(KeyboardInterrupt):
        rolling.accept_round(lib.root)
    assert "lit_x2" in lib.rolling_names()
    assert "lit_x2" not in lib.rolling_names(rolling.STATEMENTS)
    monkeypatch.setattr(rolling, "write_lines", real)
    assert rolling.accept_round(lib.root)
    assert list(lib.rolling_names()).count("lit_x2") == 1
    assert "lit_x2" in lib.rolling_names(rolling.STATEMENTS)
    assert len(lib.rolling_names()) == 6  # `aux` went, `lit_x2` came


def test_discard_forgets_a_rejected_round(lib: Library) -> None:
    lib.modules[LIT_X] = []
    lib.round(LIT_X)
    assert lib.fidelity()[1] == ["missing: lit_x"]
    rolling.discard()
    assert rolling.round_modules(lib.root) == set()
    assert lib.fidelity()[1] == []
    assert not rolling.accept_round(lib.root)


def test_failing_dumper_leaves_the_last_dump(
    lib: Library, monkeypatch: pytest.MonkeyPatch
) -> None:
    before = lib.rolling_names()

    def broken(root: Path, modules: Sequence[str], canonical: bool) -> Iterator[str]:
        yield from lib.dumper(root, modules[:1], canonical)
        raise rolling.ToolError("scripts/DumpTypes.lean failed with exit status 1")

    monkeypatch.setattr(rolling, "run_dumper", broken)
    with pytest.raises(rolling.ToolError):
        rolling.seed()
    with pytest.raises(rolling.ToolError):
        rolling.dump(LIT_X)
    assert lib.rolling_names() == before
    assert rolling.round_modules(lib.root) == set()


# -- command line and the gate --------------------------------------------------------------------


def run_cli(monkeypatch: pytest.MonkeyPatch, *args: str) -> int:
    pytest.importorskip("fire")
    monkeypatch.setattr(sys, "argv", ["rolling.py", *args])
    with pytest.raises(SystemExit) as caught:
        rolling.cli()
        raise SystemExit(0)
    return int(caught.value.code or 0)


def test_exit_status_tells_a_lost_statement_from_a_check_that_cannot_run(
    lib: Library, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    assert run_cli(monkeypatch, "fidelity") == 0
    lib.modules[LIT_X] = []
    assert run_cli(monkeypatch, "dump", LIT_X) == 0
    assert run_cli(monkeypatch, "fidelity") == 1
    assert "missing: lit_x" in capsys.readouterr().out
    assert run_cli(monkeypatch, "diff") == 0
    assert run_cli(monkeypatch, "discard") == 0
    assert run_cli(monkeypatch, "diff") == 2
    assert "no dump of a round" in capsys.readouterr().err
    rolling.at(lib.root, rolling.STATEMENTS).unlink()
    assert run_cli(monkeypatch, "fidelity") == 2
    rolling.seed()
    assert (
        run_cli(monkeypatch, "fidelity") == 1
    )  # `lit_x` is gone from the seeded library
    (lib.root / "docs/renames.json").write_text('{"a": "b", "b": "a"}')
    assert run_cli(monkeypatch, "fidelity") == 2
    assert "cycle" in capsys.readouterr().err


def test_gate_accepts_the_dump_that_seed_and_accept_write(lib: Library) -> None:
    def git(*args: str) -> str:
        cmd = ["git", "-c", "user.name=t", "-c", "user.email=t@example.org", *args]
        return subprocess.run(
            cmd, cwd=lib.root, capture_output=True, text=True, check=True
        ).stdout

    def runner(*cmd: str, timeout: int = 14400) -> tuple[int, str]:
        proc = subprocess.run(
            cmd, cwd=lib.root, capture_output=True, text=True, check=False
        )
        return proc.returncode, proc.stdout + proc.stderr

    (lib.root / ".gitignore").write_text(".lake/\n")
    (lib.root / "LeanDLRA/Core").mkdir(parents=True)
    (lib.root / "LeanDLRA/Core/A.lean").write_text("-- a\n")
    git("init", "-q", "-b", "main")
    git("add", "-A")
    git("commit", "-q", "-m", "start")
    checker = gate.Gate(lib.root, runner)
    assert "describes" in (checker.preflight() or "")
    rolling.seed()
    assert checker.preflight() is None

    (lib.root / "LeanDLRA/Core/A.lean").write_text("-- a2\n")
    git("commit", "-q", "-am", "a round")
    assert "describes" in (checker.preflight() or "")
    lib.round()
    assert rolling.accept_round(lib.root)
    assert checker.preflight() is None
