"""The pure parts of scripts/gate.py: markers, selection of a round, rename map, log lines."""

from __future__ import annotations

import json
import re

import gate
import pytest
from gate import BadMarker, Group, Stats


def marker(
    gid: str, files: list[str], age: float = 0.0, **extra: object
) -> Group | BadMarker:
    return gate.parse_marker(f"{gid}.group", json.dumps({"files": files, **extra}), age)


def group(gid: str, files: list[str], age: float = 0.0, **extra: object) -> Group:
    parsed = marker(gid, files, age, **extra)
    assert isinstance(parsed, Group), parsed
    return parsed


def choose(
    files: dict[str, float],
    markers: list[Group | BadMarker],
    batch: int = 12,
    legacy_max: int = 6,
    now: float = 1000.0,
    grace: float = 120.0,
    targets: dict[str, str] | None = None,
) -> gate.Selection:
    table = (
        targets
        if targets is not None
        else {gate.key(f): f"LeanDLRA/{f}" for f in files}
    )
    return gate.select_round(files, markers, table, batch, legacy_max, now, grace)


def ids(selection: gate.Selection) -> list[tuple[str, tuple[str, ...]]]:
    return [(g.id, g.files) for g in selection.groups]


# -- markers --------------------------------------------------------------------------------------


def test_marker_with_all_fields() -> None:
    text = json.dumps(
        {
            "id": "g1",
            "files": ["A.lean", "B.lean"],
            "renames": {"Old.name": "New.name"},
            "expect_changed": 0,
            "promote": ["LeanDLRA.Literature.A"],
            "queued": "2026-11-10T08:00:00",
        }
    )
    parsed = gate.parse_marker("g1.group", text, 5.0)
    assert parsed == Group(
        "g1",
        ("A.lean", "B.lean"),
        {"Old.name": "New.name"},
        0,
        ("LeanDLRA.Literature.A",),
        "g1.group",
        5.0,
    )
    assert parsed.atomic
    assert not Group(gate.LEGACY, ("A.lean",)).atomic


@pytest.mark.parametrize(
    ("text", "reason"),
    [
        ('{"files": ["A.lean"', "not JSON"),
        ("[]", "files:"),
        ('{"files": []}', "files:"),
        ('{"files": ["A.lean", "A.lean"]}', "files:"),
        ('{"files": ["../A.lean"]}', "files:"),
        ('{"files": ["A.txt"]}', "files:"),
        ('{"files": ["A.lean"], "id": "other"}', "id differs"),
        ('{"files": ["A.lean"], "renames": ["a"]}', "renames:"),
        ('{"files": ["A.lean"], "renames": {"a": 1}}', "renames:"),
        ('{"files": ["A.lean"], "expect_changed": -1}', "expect_changed:"),
        ('{"files": ["A.lean"], "expect_changed": true}', "expect_changed:"),
        ('{"files": ["A.lean"], "expect_changed": "3"}', "expect_changed:"),
        ('{"files": ["A.lean"], "promote": "LeanDLRA.A"}', "promote:"),
        ('{"files": ["A.lean"], "promote": ["Mathlib.A"]}', "promote:"),
    ],
)
def test_bad_markers(text: str, reason: str) -> None:
    parsed = gate.parse_marker("g1.group", text, 0.0)
    assert isinstance(parsed, BadMarker)
    assert parsed.reason.startswith(reason)


def test_bad_marker_keeps_its_files_for_rejection() -> None:
    parsed = gate.parse_marker(
        "g1.group", '{"files": ["A.lean"], "expect_changed": -1}', 0.0
    )
    assert isinstance(parsed, BadMarker)
    assert parsed.files == ("A.lean",)


# -- selection ------------------------------------------------------------------------------------


def test_groups_are_taken_whole_in_fifo_order() -> None:
    files = {f"{c}.lean": 1.0 for c in "ABCDEFG"}
    markers = [
        group("late", ["F.lean", "G.lean"], age=30.0),
        group("first", ["A.lean", "B.lean"], age=10.0),
        group("second", ["C.lean", "D.lean", "E.lean"], age=20.0),
    ]
    assert ids(choose(files, markers, batch=5)) == [
        ("first", ("A.lean", "B.lean")),
        ("second", ("C.lean", "D.lean", "E.lean")),
    ]
    assert [g for g, _ in ids(choose(files, markers, batch=12))] == [
        "first",
        "second",
        "late",
    ]
    # Never a part of a group, and nothing overtakes a group that does not fit.
    assert [g for g, _ in ids(choose(files, markers, batch=4))] == ["first"]


def test_first_group_is_taken_even_if_larger_than_the_batch() -> None:
    files = {f"{c}.lean": 1.0 for c in "ABCD"}
    markers = [
        group("big", ["A.lean", "B.lean", "C.lean"], age=1.0),
        group("b", ["D.lean"], age=2.0),
    ]
    assert [g for g, _ in ids(choose(files, markers, batch=2))] == ["big"]


def test_equal_times_are_ordered_by_id() -> None:
    files = {"A.lean": 1.0, "B.lean": 1.0}
    markers = [group("b", ["B.lean"], age=5.0), group("a", ["A.lean"], age=5.0)]
    assert [g for g, _ in ids(choose(files, markers))] == ["a", "b"]


def test_legacy_files_form_one_pseudo_group_oldest_first() -> None:
    files = {f"L{i}.lean": float(i) for i in range(8)}
    selection = choose(files, [], legacy_max=6)
    assert ids(selection) == [(gate.LEGACY, tuple(f"L{i}.lean" for i in range(6)))]
    assert not selection.groups[0].atomic
    assert selection.groups[0].marker is None


def test_legacy_files_wait_behind_an_older_group() -> None:
    files = {"A.lean": 1.0, "B.lean": 1.0, "L1.lean": 50.0, "L2.lean": 60.0}
    markers = [group("g", ["A.lean", "B.lean"], age=10.0)]
    assert ids(choose(files, markers, batch=2)) == [("g", ("A.lean", "B.lean"))]
    assert ids(choose(files, markers, batch=12)) == [
        ("g", ("A.lean", "B.lean")),
        (gate.LEGACY, ("L1.lean", "L2.lean")),
    ]


def test_older_legacy_files_come_first_and_are_one_run() -> None:
    files = {"L1.lean": 5.0, "A.lean": 1.0, "L2.lean": 50.0}
    markers = [group("g", ["A.lean"], age=10.0)]
    # L1 is older than the group, L2 younger: one run of legacy files per round.
    assert ids(choose(files, markers)) == [
        (gate.LEGACY, ("L1.lean",)),
        ("g", ("A.lean",)),
    ]


def test_young_legacy_files_are_not_visible() -> None:
    # A group whose marker is not written yet must not be taken apart.
    files = {"A.lean": 950.0, "B.lean": 950.0, "Old.lean": 100.0}
    assert ids(choose(files, [], now=1000.0, grace=120.0)) == [
        (gate.LEGACY, ("Old.lean",))
    ]
    assert ids(choose(files, [], now=1000.0, grace=0.0))[0][1] == (
        "Old.lean",
        "A.lean",
        "B.lean",
    )
    marked = [group("g", ["A.lean", "B.lean"], age=951.0)]
    assert [g for g, _ in ids(choose(files, marked))] == [gate.LEGACY, "g"]


def test_marker_naming_a_missing_file_is_bad() -> None:
    files = {"A.lean": 1.0, "C.lean": 1.0}
    markers = [
        group("g", ["A.lean", "B.lean"], age=10.0),
        group("h", ["C.lean"], age=20.0),
    ]
    selection = choose(files, markers)
    assert selection.bad == [
        BadMarker("g.group", "B.lean is not in wip/ready", ("A.lean",))
    ]
    assert ids(selection) == [("h", ("C.lean",))]


def test_file_of_two_groups_belongs_to_the_older() -> None:
    files = {"A.lean": 1.0, "B.lean": 1.0}
    markers = [
        group("young", ["A.lean", "B.lean"], age=20.0),
        group("old", ["A.lean"], age=10.0),
    ]
    selection = choose(files, markers)
    assert ids(selection) == [("old", ("A.lean",))]
    assert selection.bad == [
        BadMarker("young.group", "A.lean belongs to an older group", ("B.lean",))
    ]


def test_unparsable_marker_is_reported_and_its_files_are_claimed() -> None:
    files = {"A.lean": 1.0, "B.lean": 1.0}
    bad = marker("g", ["A.lean"], expect_changed=-1)
    selection = choose(files, [bad], grace=0.0)
    assert selection.bad == [bad]
    assert ids(selection) == [(gate.LEGACY, ("B.lean",))]


def test_groups_with_the_same_target_are_not_in_one_round() -> None:
    files = {"A1.lean": 1.0, "A2.lean": 1.0, "B.lean": 1.0}
    targets = {"A1": "LeanDLRA/A.lean", "A2": "LeanDLRA/A.lean", "B": "LeanDLRA/B.lean"}
    markers = [
        group("g1", ["A1.lean"], age=1.0),
        group("g2", ["A2.lean"], age=2.0),
        group("g3", ["B.lean"], age=3.0),
    ]
    assert [g for g, _ in ids(choose(files, markers, targets=targets))] == ["g1"]


def test_empty_queue() -> None:
    assert choose({}, []) == gate.Selection([], [])


# -- rename map -----------------------------------------------------------------------------------


def test_merge_renames_adds_entries_and_keeps_the_base() -> None:
    base = {"A": "B"}
    assert gate.merge_renames(base, {"C": "D", "A": "B"}) == {"A": "B", "C": "D"}
    assert base == {"A": "B"}


def test_merge_renames_allows_chains() -> None:
    assert gate.merge_renames({"A": "B"}, {"B": "C"}) == {"A": "B", "B": "C"}


@pytest.mark.parametrize(
    ("base", "extra", "message"),
    [
        ({"A": "B"}, {"A": "C"}, "A is already mapped to B, not to C"),
        ({"A": "B"}, {"B": "A"}, "cycle: "),
        ({"A": "B", "B": "C"}, {"C": "A"}, "cycle: "),
        ({}, {"A": "A"}, "A is mapped to itself"),
        ({}, {"A b": "C"}, "not a pair of constant names"),
        ({}, {"A": "f(x)"}, "not a pair of constant names"),
    ],
)
def test_merge_renames_refuses(
    base: dict[str, str], extra: dict[str, str], message: str
) -> None:
    with pytest.raises(ValueError, match=re.escape(message)):
        gate.merge_renames(base, extra)


def test_merged_map_is_accepted_by_fidelity(tmp_path: object) -> None:
    from pathlib import Path

    import fidelity

    assert isinstance(tmp_path, Path)
    merged = gate.merge_renames({"A": "B"}, {"B": "C", "D": "E"})
    path = tmp_path / "renames.json"
    path.write_text(json.dumps(merged), encoding="utf-8")
    assert fidelity.load_renames(path) == {"A": "C", "B": "C", "D": "E"}


# -- log lines and commit message -----------------------------------------------------------------


def test_log_line_formats() -> None:
    assert re.fullmatch(r"\d\d:\d\d:\d\d PUSHED x\n", gate.stamp("PUSHED x"))
    assert gate.reject_line("K", "first line\nsecond\n") == "REJECT K: first line"
    assert gate.reject_line("K", "x" * 200) == "REJECT K: " + "x" * 160
    assert gate.reject_line("K", "") == "REJECT K: "
    stats = Stats("abc1234", 4321, 2, 3, 4, 1)
    assert (
        gate.hashdiff_line("def5678", stats)
        == "HASHDIFF abc1234..def5678: 4321 declarations, 2 changed, 3 moved, 4 added, 1 removed"
    )
    assert gate.core_line("def5678", 250, 3) == (
        "CORE def5678: 250 core modules, 3 slice modules in the catalogue"
    )


def test_commit_title_and_message() -> None:
    assert gate.commit_title(["A"], False) == "Add 1 slice (A)"
    assert gate.commit_title(["A", "B"], True) == "Update 2 slices (A, B)"
    message = gate.commit_message("Add 1 slice (A)", ["OP-1", "OP-2"])
    assert message == (
        "Add 1 slice (A)\n\nOP-1 OP-2\n\nCo-Authored-By: Claude <noreply@anthropic.com>\n"
    )


def test_parse_stats_reads_the_last_hashdiff_line() -> None:
    line = json.dumps(
        {
            "base": "abc",
            "declarations": 9,
            "changed": 1,
            "moved": 0,
            "added": 2,
            "removed": 0,
        }
    )
    assert gate.parse_stats(f"# report\nHASHDIFF {line}\n") == Stats(
        "abc", 9, 1, 0, 2, 0
    )
    assert gate.parse_stats("no line") is None
    assert gate.parse_stats('HASHDIFF {"base": "abc"}') is None


def test_module_names() -> None:
    assert gate.module_name("LeanDLRA/Literature/A.lean") == "LeanDLRA.Literature.A"
    assert gate.module_path("LeanDLRA.Literature.A") == "LeanDLRA/Literature/A.lean"
    assert gate.key("A.lean") == "A"
