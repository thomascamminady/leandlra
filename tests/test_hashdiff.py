"""Tests for the pure parts of ``scripts/hashdiff.py``."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import hashdiff
import pytest

A = "LeanDLRA.Old.a"
B = "LeanDLRA.New.b"


def rec(
    name: str,
    typ: str,
    kind: str = "theorem",
    module: str = "LeanDLRA.M",
    value: str | None = None,
) -> dict[str, Any]:
    """A dumped declaration."""
    r: dict[str, Any] = {"name": name, "module": module, "kind": kind, "type": typ}
    if value is not None:
        r["value"] = value
    return r


def run(
    before: list[dict[str, Any]],
    after: list[dict[str, Any]],
    renames: dict[str, str] | None = None,
) -> hashdiff.Result:
    """Compare two in-memory dumps."""
    return hashdiff.compare(iter(before), iter(after), renames or {})


def test_normalize_follows_chains_and_drops_identities() -> None:
    raw = {"A": "B", "B": "C", "D": "D"}
    assert hashdiff.normalize_renames(raw) == {"A": "C", "B": "C"}


def test_normalize_rejects_cycles() -> None:
    with pytest.raises(SystemExit):
        hashdiff.normalize_renames({"A": "B", "B": "A"})


def test_load_renames(tmp_path: Path) -> None:
    assert hashdiff.load_renames(tmp_path / "missing.json") == {}
    good = tmp_path / "good.json"
    good.write_text(json.dumps({A: B, B: B}))
    assert hashdiff.load_renames(good) == {A: B}
    bad = tmp_path / "bad.json"
    bad.write_text(json.dumps({"LeanDLRA.x y": B}))
    with pytest.raises(SystemExit):
        hashdiff.load_renames(bad)


def test_renamer_replaces_whole_constants_only() -> None:
    rename = hashdiff.make_renamer({A: B, "Foo.c": "Foo.d"})
    text = (
        f"forall {{x : Type.{{u0}}}}, ({A}.{{u0}} x) -> ({A} x) -> {A}_spec -> {A}.field "
        f"-> [x_1 : {A}] -> My{A} -> Foo.c -> Foo.cc"
    )
    assert rename(text) == (
        f"forall {{x : Type.{{u0}}}}, ({B}.{{u0}} x) -> ({B} x) -> {A}_spec -> {A}.field "
        f"-> [x_1 : {B}] -> My{A} -> Foo.d -> Foo.cc"
    )
    assert hashdiff.make_renamer({})("unchanged") == "unchanged"


def test_identical_dumps_have_no_differences() -> None:
    dump = [
        rec("LeanDLRA.t", f"0 ⊢ {A} 1"),
        rec(A, "0 ⊢ Nat -> Nat", "def", value="fun (x : Nat) => x"),
    ]
    res = run(dump, list(dump))
    assert res.unchanged == 2
    assert res.failures() == 0 and not res.appeared and not res.moved


def test_changed_type_value_disappeared_appeared_and_moved() -> None:
    before = [
        rec("LeanDLRA.t", "0 ⊢ True"),
        rec("LeanDLRA.d", "0 ⊢ Nat", "def", value="0"),
        rec("LeanDLRA.gone", "0 ⊢ True"),
        rec("LeanDLRA.moved", "0 ⊢ True", module="LeanDLRA.Old"),
        rec("LeanDLRA.kind", "0 ⊢ True"),
    ]
    after = [
        rec("LeanDLRA.t", "0 ⊢ False"),
        rec("LeanDLRA.d", "0 ⊢ Nat", "def", value="1"),
        rec("LeanDLRA.new", "0 ⊢ True"),
        rec("LeanDLRA.moved", "0 ⊢ True", module="LeanDLRA.Defs"),
        rec("LeanDLRA.kind", "0 ⊢ True", "def", value="trivial"),
    ]
    res = run(before, after)
    assert res.type_changed == ["LeanDLRA.t", "LeanDLRA.kind"]
    assert res.value_changed == ["LeanDLRA.d"]
    assert res.disappeared == [("LeanDLRA.gone", "LeanDLRA.M")]
    assert res.appeared == [("LeanDLRA.new", "LeanDLRA.M")]
    assert res.moved == [("LeanDLRA.moved", "LeanDLRA.Old", "LeanDLRA.Defs")]
    assert res.failures() == 4


def test_rename_with_deprecated_alias() -> None:
    before = [
        rec(A, "1 ⊢ Type.{u0} -> Prop", "def", value="fun (x : Type.{u0}) => True"),
        rec("LeanDLRA.uses", f"1 ⊢ forall {{x : Type.{{u0}}}}, {A}.{{u0}} x"),
    ]
    after = [
        rec(B, "1 ⊢ Type.{u0} -> Prop", "def", value="fun (x : Type.{u0}) => True"),
        rec(A, "1 ⊢ Type.{u0} -> Prop", "def", value=f"{B}.{{u0}}"),
        rec("LeanDLRA.uses", f"1 ⊢ forall {{x : Type.{{u0}}}}, {B}.{{u0}} x"),
    ]
    assert run(before, after).type_changed == ["LeanDLRA.uses"]
    res = run(before, after, {A: B})
    assert res.failures() == 0
    assert res.renamed == [(A, B)]
    assert res.aliases == [(A, "LeanDLRA.M")]
    assert res.unchanged == 2


def test_alias_carried_over_from_an_earlier_rename() -> None:
    # After an earlier batch A → B: B is real, A a deprecated alias. This batch moves B.
    before = [
        rec(B, "0 ⊢ Prop", "def", value="True", module="LeanDLRA.Old"),
        rec(A, "0 ⊢ Prop", "def", value=B),
    ]
    after = [
        rec(B, "0 ⊢ Prop", "def", value="True", module="LeanDLRA.Defs"),
        rec(A, "0 ⊢ Prop", "def", value=B),
    ]
    res = run(before, after, {A: B})
    assert res.failures() == 0
    assert res.aliases == [(A, "LeanDLRA.M")]


def test_rename_target_missing_is_reported() -> None:
    before = [rec(A, "0 ⊢ True")]
    res = run(before, list(before), {A: B})
    assert res.unapplied == [(A, B)]
    assert res.unchanged == 1


def test_merge_of_definitions_with_different_bodies_is_flagged() -> None:
    before = [
        rec(A, "0 ⊢ Nat", "def", value="Nat.add 1 1"),
        rec(B, "0 ⊢ Nat", "def", value="2"),
    ]
    after = [rec(B, "0 ⊢ Nat", "def", value="2"), rec(A, "0 ⊢ Nat", "def", value=B)]
    res = run(before, after, {A: B})
    assert res.value_changed == [B]


def test_private_declarations_with_the_same_name() -> None:
    before = [
        rec("_priv.LeanDLRA.aux", "0 ⊢ True", module="LeanDLRA.X"),
        rec("_priv.LeanDLRA.aux", "0 ⊢ False", module="LeanDLRA.Y"),
    ]
    after = [
        rec("_priv.LeanDLRA.aux", "0 ⊢ False", module="LeanDLRA.Z"),
        rec("_priv.LeanDLRA.aux", "0 ⊢ True", module="LeanDLRA.X"),
    ]
    res = run(before, after)
    assert res.failures() == 0 and len(res.moved) == 1


def test_dump_round_trip(tmp_path: Path) -> None:
    path = tmp_path / "d.jsonl.gz"
    header = {"format": hashdiff.FORMAT, "commit": "abc"}
    with hashdiff.open_text(path, "w") as f:
        f.write(json.dumps(header) + "\n")
        f.write(json.dumps(rec("LeanDLRA.t", "0 ⊢ True")) + "\n")
    got_header, records = hashdiff.read_dump(path)
    assert got_header == header
    assert [r["name"] for r in records] == ["LeanDLRA.t"]
    plain = tmp_path / "x.jsonl"
    plain.write_text('{"format": "other"}\n')
    with pytest.raises(SystemExit):
        hashdiff.read_dump(plain)


def test_first_difference() -> None:
    a, b = hashdiff.first_difference("x" * 100 + "abc", "x" * 100 + "abd", width=5)
    assert a == "…xxxabc" and b == "…xxxabd"


def test_library_modules_and_unlisted_sources(tmp_path: Path) -> None:
    (tmp_path / "LeanDLRA" / "A").mkdir(parents=True)
    (tmp_path / "LeanDLRA" / "A" / "B.lean").write_text("")
    (tmp_path / "LeanDLRA" / "A" / "C.lean").write_text("")
    (tmp_path / "LeanDLRA.lean").write_text("-- generated\nimport LeanDLRA.A.B\n")
    (tmp_path / "LeanDLRACatalogue.lean").write_text(
        "-- generated\nimport LeanDLRA\nimport LeanDLRA.A.C\n"
    )
    core = hashdiff.library_modules(tmp_path, "LeanDLRA")
    assert core == ["LeanDLRA.A.B"]
    assert hashdiff.unlisted_sources(core, tmp_path) == ["LeanDLRA.A.C"]
    everything = hashdiff.library_modules(tmp_path)
    assert everything == ["LeanDLRA.A.B", "LeanDLRA.A.C"]
    assert hashdiff.unlisted_sources(everything, tmp_path) == []
