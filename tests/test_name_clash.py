# Scope: both
"""Tests for ``scripts/name_clash.py`` (no Lean, no fire)."""

from __future__ import annotations

import gzip
import json
from pathlib import Path

import core_checks
import name_clash as nc
import pytest


def write_dump(
    root: Path, entries: list[tuple[str, str]], kind: str = "theorem"
) -> None:
    """A rolling dump with these ``(module, name)`` entries."""
    path = root / nc.DUMP
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = [json.dumps({"format": "leandlra-hashdiff/1", "library_commit": ""})]
    lines += [
        json.dumps(
            {"kind": kind, "module": m, "name": n, "type": '0 ⊢ "name":"x"'},
            ensure_ascii=False,
            separators=(",", ":"),
        )
        for m, n in entries
    ]
    with gzip.open(path, "wt", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")


def write(root: Path, rel: str, text: str) -> None:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def repo(root: Path, slices: dict[str, str], modules: dict[str, str]) -> None:
    """A tree with a manifest (slice key -> target module), module sources, a core root."""
    table = {k: {"target": m.replace(".", "/") + ".lean"} for k, m in slices.items()}
    write(root, nc.MANIFEST, json.dumps(table))
    for module, text in modules.items():
        write(root, module.replace(".", "/") + ".lean", text)
    write(root, "LeanDLRA.lean", "import LeanDLRA.Core.A\n")


SOURCE = """
namespace LeanDLRA

theorem t₁ : True := trivial
private theorem hidden : True := trivial
protected def Foo.bar := 1
instance : Inhabited Nat := ⟨0⟩
noncomputable scoped instance (priority := high) instNamed : Inhabited Nat := ⟨1⟩
theorem _root_.rootName : True := trivial
structure S where
  x : Nat

noncomputable section Inner
def inner := 2
end Inner

end LeanDLRA

lemma outside {x : Nat} (hx : 0 < x) : 0 < x := hx
"""


def test_public_names_of_a_slice() -> None:
    assert [n for _, n in nc.public_names(SOURCE)] == [
        "LeanDLRA.t₁",
        "LeanDLRA.Foo.bar",
        "LeanDLRA.instNamed",
        "rootName",
        "LeanDLRA.S",
        "LeanDLRA.inner",
        "outside",
    ]
    assert nc.public_names(SOURCE)[0][0] == 4


def test_parser_follows_mutual_blocks_and_open_in() -> None:
    text = (
        "namespace A\nmutual\ninductive T\n| a\ninductive U\n| b\nend\n"
        "open Nat in theorem t : True := trivial\n"
        "class inductive C\n| c\nirreducible_def d : Nat := 1\nend A\ndef e := 1\n"
    )
    got = [(d.kind, d.name) for d in core_checks.declarations_in(text)]
    assert got == [
        ("inductive", "A.T"),
        ("inductive", "A.U"),
        ("theorem", "A.t"),
        ("class", "A.C"),
        ("def", "A.d"),
        ("def", "e"),
    ]


def test_dump_index_skips_private_names_replaced_and_deleted_modules(
    tmp_path: Path,
) -> None:
    repo(tmp_path, {}, {"LeanDLRA.Core.A": "", "LeanDLRA.Lit.B": ""})
    write_dump(
        tmp_path,
        [
            ("LeanDLRA.Core.A", "LeanDLRA.a"),
            ("LeanDLRA.Core.A", "_priv.LeanDLRA.p"),
            ("LeanDLRA.Lit.B", "LeanDLRA.b"),
            ("LeanDLRA.Gone.C", "LeanDLRA.c"),  # no source file any more
        ],
    )
    assert nc.dump_index(tmp_path, frozenset()) == {
        "LeanDLRA.a": "LeanDLRA.Core.A",
        "LeanDLRA.b": "LeanDLRA.Lit.B",
    }
    assert nc.dump_index(tmp_path, frozenset({"LeanDLRA.Lit.B"})) == {
        "LeanDLRA.a": "LeanDLRA.Core.A"
    }


def piece(label: str, module: str, *names: str) -> nc.Slice:
    return nc.Slice(label, module, tuple((i + 1, n) for i, n in enumerate(names)))


def test_clashes_with_the_library_the_call_and_the_queue() -> None:
    a = piece(
        "wip/A.lean", "LeanDLRA.X.A", "LeanDLRA.core", "LeanDLRA.cat", "LeanDLRA.ok"
    )
    b = piece("wip/B.lean", "LeanDLRA.X.B", "LeanDLRA.twin", "LeanDLRA.late")
    c = piece("wip/C.lean", "LeanDLRA.X.C", "LeanDLRA.twin")
    q = piece("wip/ready/Q.lean", "LeanDLRA.X.Q", "LeanDLRA.late")
    index = {"LeanDLRA.core": "LeanDLRA.Core.M", "LeanDLRA.cat": "LeanDLRA.Lit.N"}
    core_set = frozenset({"LeanDLRA.Core.M"})
    found = nc.find_clashes([a, b, c], index, core_set, [q], frozenset())
    assert [(x.slice.label, x.line, x.name, x.where) for x in found] == [
        (
            "wip/A.lean",
            1,
            "LeanDLRA.core",
            "LeanDLRA.Core.M (core) declares it already",
        ),
        (
            "wip/A.lean",
            2,
            "LeanDLRA.cat",
            "LeanDLRA.Lit.N (catalogue) declares it already",
        ),
        (
            "wip/B.lean",
            1,
            "LeanDLRA.twin",
            "wip/C.lean of the same call declares it too",
        ),
        (
            "wip/B.lean",
            2,
            "LeanDLRA.late",
            "wip/ready/Q.lean, queued by an earlier group, declares it too",
        ),
        (
            "wip/C.lean",
            1,
            "LeanDLRA.twin",
            "wip/B.lean of the same call declares it too",
        ),
    ]
    allowed = frozenset({"LeanDLRA.core", "LeanDLRA.twin", "LeanDLRA.late"})
    rest = nc.find_clashes([a, b, c], index, core_set, [q], allowed)
    assert [x.name for x in rest] == ["LeanDLRA.cat"]


@pytest.mark.parametrize(
    ("value", "names"),
    [
        ("", set()),
        ("LeanDLRA.a,LeanDLRA.b₁", {"LeanDLRA.a", "LeanDLRA.b₁"}),
        (("a", "b"), {"a", "b"}),
        (["x, y"], {"x", "y"}),
    ],
)
def test_allowed_names(value: object, names: set[str]) -> None:
    assert nc.allowed_names(value) == names


def test_run_check_end_to_end(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    repo(
        tmp_path,
        {
            "New": "LeanDLRA.Lit.New",
            "Upd": "LeanDLRA.Core.A",
            "Old": "LeanDLRA.Lit.Old",
        },
        {"LeanDLRA.Core.A": "", "LeanDLRA.Lit.Old": ""},
    )
    write_dump(
        tmp_path,
        [("LeanDLRA.Core.A", "LeanDLRA.kept"), ("LeanDLRA.Lit.Old", "LeanDLRA.used")],
    )
    write(
        tmp_path,
        "wip/New.lean",
        "namespace LeanDLRA\ntheorem used : True := trivial\nend LeanDLRA\n",
    )
    write(tmp_path, "wip/Upd.lean", "theorem LeanDLRA.kept : True := trivial\n")
    # An update of its own target keeps its names.
    assert nc.run_check(tmp_path, ["wip/Upd.lean"], frozenset()) == 0
    assert nc.run_check(tmp_path, ["wip/New.lean"], frozenset()) == 1
    err = capsys.readouterr().err
    assert (
        "enqueue: name clash: wip/New.lean:2 declares LeanDLRA.used; "
        "LeanDLRA.Lit.Old (catalogue) declares it already"
    ) in err
    assert "--allow-name NAME" in err
    assert nc.run_check(tmp_path, ["wip/New.lean"], frozenset({"LeanDLRA.used"})) == 0
    # A move: the group also updates the module that has the name, without it.
    write(tmp_path, "wip/Old.lean", "theorem LeanDLRA.other : True := trivial\n")
    assert nc.run_check(tmp_path, ["wip/New.lean", "wip/Old.lean"], frozenset()) == 0
    # A queued slice of an earlier group counts, unless it is for a target of this call.
    write(tmp_path, "wip/ready/Old.lean", "theorem LeanDLRA.fresh : True := trivial\n")
    write(tmp_path, "wip/Upd.lean", "theorem LeanDLRA.fresh : True := trivial\n")
    assert nc.run_check(tmp_path, ["wip/Upd.lean"], frozenset()) == 1
    assert "wip/ready/Old.lean, queued by an earlier group" in capsys.readouterr().err
    assert nc.run_check(tmp_path, ["wip/Upd.lean", "wip/Old.lean"], frozenset()) == 0


def test_run_check_without_dump_warns_and_bad_input_exits_2(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    repo(tmp_path, {"New": "LeanDLRA.Lit.New"}, {})
    write(tmp_path, "wip/New.lean", "theorem a : True := trivial\n")
    write(tmp_path, "wip/Unknown.lean", "theorem b : True := trivial\n")
    assert nc.run_check(tmp_path, ["wip/New.lean"], frozenset()) == 0
    assert "warning: no .lake/hashdiff/rolling.jsonl.gz" in capsys.readouterr().err
    assert nc.run_check(tmp_path, ["wip/Unknown.lean"], frozenset()) == 2
    assert nc.run_check(tmp_path, ["wip/New.lean"], frozenset({"f(x)"})) == 2
    assert "not a declaration name: f(x)" in capsys.readouterr().err
