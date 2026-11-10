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


def added(res: hashdiff.Result) -> int:
    """The "added" count of a gate round (``scripts/rolling.py diff``)."""
    return len(res.appeared) + len(res.aliases)


def accounted(res: hashdiff.Result) -> int:
    """Declarations of the after dump by outcome (dumps without repeated names)."""
    return res.unchanged + len(res.type_changed) + len(res.value_changed) + added(res)


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
    assert res.settled == []
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
    assert res.settled == [(A, "LeanDLRA.M")]
    assert res.aliases == []


def test_settled_alias_of_another_kind_is_not_a_change() -> None:
    # A structure B and a definition A that abbreviates it, the same in both dumps.
    both = [
        rec(B, "0 ⊢ Nat -> Prop", "inductive"),
        rec(A, "0 ⊢ Nat -> Prop", "def", value=B),
        rec("LeanDLRA.uses", f"0 ⊢ {A} 0"),
    ]
    res = run(both, list(both), {A: B})
    assert res.failures() == 0
    assert res.renamed == []
    assert res.settled == [(A, "LeanDLRA.M")]
    assert res.aliases == []
    assert res.unchanged == 3


def test_settled_specialization_is_not_a_change() -> None:
    # A is B at equal arguments: another type than B, kept from an earlier merge.
    both = [
        rec(B, "0 ⊢ Nat -> Nat -> Prop", "def", value="fun (x x_1 : Nat) => True"),
        rec(A, "0 ⊢ Nat -> Prop", "def", value=f"fun (x : Nat) => {B} x x"),
    ]
    res = run(both, list(both), {A: B})
    assert res.failures() == 0
    assert res.unchanged == 2


def test_settled_alias_that_moves_is_a_move() -> None:
    before = [
        rec(B, "0 ⊢ Prop", "inductive"),
        rec(A, "0 ⊢ Prop", "def", value=B, module="LeanDLRA.Old"),
    ]
    after = [
        rec(B, "0 ⊢ Prop", "inductive"),
        rec(A, "0 ⊢ Prop", "def", value=B, module="LeanDLRA.Defs"),
    ]
    res = run(before, after, {A: B})
    assert res.failures() == 0
    assert res.moved == [(A, "LeanDLRA.Old", "LeanDLRA.Defs")]


def test_definition_replaced_by_an_alias_of_another_kind_is_flagged() -> None:
    # The round that merges A into the structure B is still reported (once).
    before = [
        rec(B, "0 ⊢ Nat -> Prop", "inductive"),
        rec(A, "0 ⊢ Nat -> Prop", "def", value="fun (x : Nat) => True"),
    ]
    after = [
        rec(B, "0 ⊢ Nat -> Prop", "inductive"),
        rec(A, "0 ⊢ Nat -> Prop", "def", value=B),
    ]
    res = run(before, after, {A: B})
    assert res.type_changed == [B]
    assert res.renamed == [(A, B)]


def test_settled_alias_whose_statement_changes_is_flagged() -> None:
    before = [rec(B, "0 ⊢ Prop", "inductive"), rec(A, "0 ⊢ Prop", "def", value=B)]
    after = [
        rec(B, "0 ⊢ Nat -> Prop", "inductive"),
        rec(A, "0 ⊢ Nat -> Prop", "def", value=B),
    ]
    res = run(before, after, {A: B})
    assert res.type_changed == [B]


# -- what counts as new: settled aliases, new aliases, renames with and without alias ------------

A_APPLY, B_APPLY = A + "_apply", B + "_apply"
STANDING = [
    rec(B, "0 ⊢ Nat -> Nat", "def", value="fun (x : Nat) => x"),
    rec(B_APPLY, f"0 ⊢ forall (x : Nat), Eq ({B} x) x"),
    rec(A, "0 ⊢ Nat -> Nat", "def", value=B),
    rec(A_APPLY, f"0 ⊢ forall (x : Nat), Eq ({B} x) x"),
]
STANDING_MAP = {A: B, A_APPLY: B_APPLY}


def test_settled_aliases_are_not_new() -> None:
    # A definition and a theorem kept as deprecated aliases by an earlier round.
    after = [*STANDING, rec("LeanDLRA.fresh", "0 ⊢ True")]
    res = run(STANDING, after, STANDING_MAP)
    assert res.failures() == 0
    assert res.settled == [(A, "LeanDLRA.M"), (A_APPLY, "LeanDLRA.M")]
    assert res.aliases == []
    assert res.appeared == [("LeanDLRA.fresh", "LeanDLRA.M")]
    assert res.renamed == [] and res.moved == [] and res.unapplied == []
    assert res.unchanged == 4
    assert added(res) == 1 == res.after_count - res.before_count
    assert accounted(res) == res.after_count


def test_new_alias_is_new_once() -> None:
    # The round of the rename: the alias is new. Every later round: it is settled.
    before = [
        rec(A, "0 ⊢ Nat -> Nat", "def", value="fun (x : Nat) => x"),
        rec(A_APPLY, f"0 ⊢ forall (x : Nat), Eq ({A} x) x"),
    ]
    first = run(before, STANDING, STANDING_MAP)
    assert first.failures() == 0
    assert sorted(first.renamed) == [(A, B), (A_APPLY, B_APPLY)]
    assert sorted(first.aliases) == [(A, "LeanDLRA.M"), (A_APPLY, "LeanDLRA.M")]
    assert first.settled == [] and first.appeared == []
    assert added(first) == 2 == first.after_count - first.before_count
    assert accounted(first) == first.after_count
    later = run(STANDING, list(STANDING), STANDING_MAP)
    assert later.failures() == 0
    assert later.aliases == [] and later.appeared == [] and later.renamed == []
    assert sorted(later.settled) == sorted(first.aliases)
    assert added(later) == 0
    assert accounted(later) == later.after_count


def test_new_and_settled_aliases_in_one_comparison() -> None:
    c, d = "LeanDLRA.Old.c", "LeanDLRA.New.d"
    before = [*STANDING, rec(c, "0 ⊢ Prop", "def", value="True")]
    after = [
        *STANDING,
        rec(d, "0 ⊢ Prop", "def", value="True"),
        rec(c, "0 ⊢ Prop", "def", value=d),
    ]
    res = run(before, after, {**STANDING_MAP, c: d})
    assert res.failures() == 0
    assert res.settled == [(A, "LeanDLRA.M"), (A_APPLY, "LeanDLRA.M")]
    assert res.aliases == [(c, "LeanDLRA.M")]
    assert res.renamed == [(c, d)]
    assert added(res) == 1 == res.after_count - res.before_count
    assert accounted(res) == res.after_count


def test_rename_without_alias() -> None:
    before = [rec(A, "0 ⊢ Prop", "def", value="True"), rec("LeanDLRA.uses", f"0 ⊢ {A}")]
    after = [rec(B, "0 ⊢ Prop", "def", value="True"), rec("LeanDLRA.uses", f"0 ⊢ {B}")]
    res = run(before, after, {A: B})
    assert res.failures() == 0
    assert res.renamed == [(A, B)]
    assert res.aliases == [] and res.settled == [] and res.appeared == []
    assert added(res) == 0 and res.unchanged == 2
    # Without the entry in the map: one removed, one added, one changed (as before).
    res = run(before, after)
    assert res.disappeared == [(A, "LeanDLRA.M")]
    assert res.appeared == [(B, "LeanDLRA.M")]
    assert res.type_changed == ["LeanDLRA.uses"]
    assert res.aliases == [] and res.settled == []


def test_rename_with_alias_but_without_map_entry() -> None:
    # No entry in the map: the alias is an ordinary declaration whose body changed.
    before = [rec(A, "0 ⊢ Prop", "def", value="True")]
    after = [
        rec(B, "0 ⊢ Prop", "def", value="True"),
        rec(A, "0 ⊢ Prop", "def", value=B),
    ]
    res = run(before, after)
    assert res.value_changed == [A]
    assert res.appeared == [(B, "LeanDLRA.M")]
    assert res.aliases == [] and res.settled == []


def test_settled_alias_that_is_removed_disappears() -> None:
    res = run(STANDING, STANDING[:2], STANDING_MAP)
    assert sorted(res.renamed) == [(A, B), (A_APPLY, B_APPLY)]
    assert res.failures() == 0  # the old names are found under their targets
    assert res.aliases == [] and res.settled == [] and res.appeared == []
    # Removed together with its map entry, an alias is a removed declaration.
    res = run(STANDING, STANDING[:2])
    assert res.disappeared == [(A, "LeanDLRA.M"), (A_APPLY, "LeanDLRA.M")]


def test_report_lists_new_and_settled_aliases_apart(tmp_path: Path) -> None:
    c, d = "LeanDLRA.Old.c", "LeanDLRA.New.d"
    before = [*STANDING, rec(c, "0 ⊢ Prop", "def", value="True")]
    after = [
        *STANDING,
        rec(d, "0 ⊢ Prop", "def", value="True"),
        rec(c, "0 ⊢ Prop", "def", value=d),
    ]
    renames = {**STANDING_MAP, c: d}
    text = hashdiff.render(
        run(before, after, renames),
        tmp_path / "before",
        tmp_path / "after",
        ({}, {}),
        tmp_path / "renames.json",
        renames,
        False,
        40,
    )
    lines = text.splitlines()
    assert "| appeared | 0 |" in lines
    assert "| appeared as deprecated alias (old name in the rename map) | 1 |" in lines
    assert (
        "| deprecated alias of an earlier rename (in both dumps, not new) | 2 |"
        in lines
    )
    new_at = lines.index("## Deprecated aliases")
    old_at = lines.index("## Deprecated aliases of earlier renames (in both dumps)")
    assert lines[new_at + 2 : old_at - 1] == [f"- `{c}` (LeanDLRA.M)"]
    assert lines[old_at + 2 : old_at + 4] == [
        f"- `{A}` (LeanDLRA.M)",
        f"- `{A_APPLY}` (LeanDLRA.M)",
    ]


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


# Generated proof constants (T2): a remark in the report, never a change of the counts.

OWN = "LeanDLRA.thinU._proof_1"
OTHER = "LeanDLRA.svTail._proof_1"


def test_number_proofs_names_by_first_occurrence() -> None:
    text = f"f ({OTHER}.{{u0}} x) ({OWN} x) ({OTHER}.{{u0}} y) Nat.succ._proof_2"
    assert hashdiff.number_proofs(text) == (
        "f (_proof#1.{u0} x) (_proof#2 x) (_proof#1.{u0} y) _proof#3"
    )
    # Not a generated proof: a longer name, a matcher, a user name that only contains the word.
    for other in ("A._proof_1.b", "A.match_1", "A.my_proof_1", "A._proof_x"):
        assert hashdiff.number_proofs(f"f ({other} x)") == f"f ({other} x)"


def test_proof_names_only() -> None:
    renamed = (f"f ({OTHER} x) ({OTHER} y)", f"f ({OWN} x) ({OWN} y)")
    assert hashdiff.proof_names_only(*renamed)
    # The same text is no difference at all.
    assert not hashdiff.proof_names_only(renamed[0], renamed[0])
    # Two proofs that were one, or one that were two: the sharing pattern differs.
    assert not hashdiff.proof_names_only(
        f"f ({OTHER} x) ({OTHER} y)", f"f ({OWN} x) ({OTHER} y)"
    )
    # Anything else that differs is a difference.
    assert not hashdiff.proof_names_only(f"f ({OTHER} x)", f"g ({OWN} x)")
    assert not hashdiff.proof_names_only("f (A.match_1 x)", "f (B.match_1 x)")
    assert not hashdiff.proof_names_only("f (A._f x)", "f (B._f x)")


def write_dump(path: Path, records: list[dict[str, Any]]) -> Path:
    with hashdiff.open_text(path, "w") as f:
        f.write(json.dumps({"format": hashdiff.FORMAT}) + "\n")
        for r in records:
            f.write(json.dumps(r) + "\n")
    return path


def test_report_remarks_on_generated_names_and_counts_them_as_before(
    tmp_path: Path,
) -> None:
    d, e, t = "LeanDLRA.thinU", "LeanDLRA.other", "LeanDLRA.thm"
    before = [
        rec(d, "0 ⊢ Nat", "def", value=f"g ({OTHER} x)"),
        rec(e, "0 ⊢ Nat", "def", value="g 1"),
        rec(t, f"0 ⊢ P ({OTHER} x)"),
        rec("LeanDLRA.old.match_1", "0 ⊢ Nat", "def", value="m"),
    ]
    after = [
        rec(d, "0 ⊢ Nat", "def", value=f"g ({OWN} x)"),
        rec(e, "0 ⊢ Nat", "def", value="g 2"),
        rec(t, f"0 ⊢ P ({OWN} x)"),
        rec("LeanDLRA.thm.match_1_1", "0 ⊢ Nat", "def", value="m"),
    ]
    res = run(before, after)
    # The counts of the comparison do not know the remark.
    assert res.type_changed == [t]
    assert res.value_changed == [d, e]
    assert [n for n, _ in res.disappeared] == ["LeanDLRA.old.match_1"]
    assert [n for n, _ in res.appeared] == ["LeanDLRA.thm.match_1_1"]
    text = hashdiff.render(
        res,
        write_dump(tmp_path / "before.jsonl.gz", before),
        write_dump(tmp_path / "after.jsonl.gz", after),
        ({}, {}),
        tmp_path / "renames.json",
        {},
        False,
        40,
    )
    lines = text.splitlines()
    note = " — only names of generated proofs (`X._proof_n`) differ"
    assert "| **type changed** | 1 |" in lines
    assert "| **definition body changed** | 2 |" in lines
    assert "| of the changed: only names of generated proofs differ | 2 |" in lines
    assert f"- `{t}`{note}" in lines
    assert f"- `{d}`{note}" in lines
    assert f"- `{e}`" in lines
    assert (
        "- `LeanDLRA.thm.match_1_1` (LeanDLRA.M) — name of a generated matcher of "
        "`LeanDLRA.thm`" in lines
    )
    assert (
        "- `LeanDLRA.old.match_1` (LeanDLRA.M) — name of a generated matcher of "
        "`LeanDLRA.old`" in lines
    )


# ---------------------------------------------------------------------------------------------
# Texts of the dumper since T6: a helper constant is printed by its content (`_f T v`,
# `_match T v`; a helper theorem with its arguments as `_proof`), not by its name.


def body(weight: str, step: int) -> str:
    """The body of a structural recursion as the dumper prints it."""
    step_text = f"HAdd.hAdd.{{0, 0, 0}} Nat Nat Nat inst ({weight} x) {step}"
    return f"fun (x : Nat) => _f (Nat → Nat) (fun (x : Nat) => {step_text}) _proof"


def test_content_of_helpers_follows_the_rename_map_and_shows_changes() -> None:
    before = [
        rec("LeanDLRA.weight", "0 ⊢ Nat → Nat", "def", value="fun (x : Nat) => x"),
        rec("LeanDLRA.sumTo", "0 ⊢ Nat → Nat", "def", value=body("LeanDLRA.weight", 1)),
        rec("LeanDLRA.user", "0 ⊢ Eq.{1} Nat (LeanDLRA.sumTo 0) 0"),
    ]
    renames = {
        "LeanDLRA.weight": "LeanDLRA.weight2",
        "LeanDLRA.sumTo": "LeanDLRA.sumUpTo",
    }
    renamed = [
        rec("LeanDLRA.weight2", "0 ⊢ Nat → Nat", "def", value="fun (x : Nat) => x"),
        rec(
            "LeanDLRA.sumUpTo",
            "0 ⊢ Nat → Nat",
            "def",
            value=body("LeanDLRA.weight2", 1),
        ),
        rec("LeanDLRA.user", "0 ⊢ Eq.{1} Nat (LeanDLRA.sumUpTo 0) 0"),
    ]
    # A rename of a constant that is mentioned inside a helper is no change of its users.
    res = run(before, renamed, renames)
    assert sorted(res.renamed) == sorted(renames.items())
    assert (res.type_changed, res.value_changed, res.disappeared) == ([], [], [])
    assert res.unchanged == 3
    # Without the map it is one.
    assert run(before, renamed).failures() > 0
    # A change inside the helper is a change of the definition that owns it.
    changed = [before[0], {**before[1], "value": body("LeanDLRA.weight", 2)}, before[2]]
    res = run(before, changed)
    assert (res.type_changed, res.value_changed) == ([], ["LeanDLRA.sumTo"])


def test_content_of_helpers_is_no_generated_proof_name() -> None:
    text = body("LeanDLRA.weight", 1)
    assert hashdiff.number_proofs(text) == text
    assert not hashdiff.proof_names_only(text, body("LeanDLRA.weight", 2))
    assert hashdiff.generated_note("LeanDLRA.sumTo") == ""
