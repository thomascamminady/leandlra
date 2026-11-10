"""``scripts/DumpTypes.lean`` on two small modules, with real Lean (opt-in).

Skipped unless ``LEANDLRA_LEAN_TESTS=1``: the file starts ``lean`` seven times (core Lean only, no
Mathlib; well under a minute and under 1 GB), and the project's rule is one Lean process at a time
and none while a gate round or a check is running.  It is skipped as well below 50 % free memory
(``LEANDLRA_MIN_FREE`` sets another threshold).

    LEANDLRA_LEAN_TESTS=1 uv run -q --with pytest pytest -q tests/test_dumper.py

What it protects: the canonical dump shows the content of helper constants (so a change in the
body of a recursive definition changes its record), no generated name is left in a record, and
only lemmas that Lean makes itself are left out under the names ``eq_<n>``.
"""

import json
import os
import re
import shutil
import subprocess
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
DUMPER = next(
    d / "DumpTypes.lean"
    for d in (HERE.parent / "scripts", HERE.parent.parent.parent / "scripts")
    if (d / "DumpTypes.lean").exists()
)
REPO = next(p for p in HERE.parents if (p / "lean-toolchain").exists())
MIN_FREE = int(os.environ.get("LEANDLRA_MIN_FREE", "50"))

A = """namespace T

def weight (n : Nat) : Nat := n + 1

def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => weight n + sumTo n

def gcd' (a b : Nat) : Nat :=
  if h : b = 0 then a else gcd' b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

private def twice : Nat → Nat
  | 0 => 0
  | n + 1 => twice n + 2

def useTwice (n : Nat) : Nat := twice n

def sign : Int → Int
  | .ofNat 0 => 0
  | .ofNat _ => 1
  | .negSucc _ => -1

structure Box where
  val : Nat
  pos : 0 < val

def box1 : Box := ⟨1, by decide⟩

def box3 : Box := ⟨1, by decide⟩

structure Wrap (α : Type) where
  val : α

theorem Wrap.eq_1 : Wrap Nat = Wrap Nat := rfl

theorem self_le (n : Nat) : n ≤ n := Nat.le_refl n

theorem sumTo_zero : sumTo 0 = 0 := by rw [sumTo]

end T
"""
B = """import T.A
namespace T.Paper

theorem eq_17 (a b : Nat) : a + b = b + a := Nat.add_comm a b

theorem eq_3 (n : Nat) : T.gcd' n 0 = n := by rw [T.gcd']; simp

end T.Paper
"""
# Label, old text, new text, the records that have to change (all in module A).
CHANGES: list[tuple[str, str, str, set[str]]] = [
    (
        "structural recursion",
        "weight n + sumTo n",
        "weight n + sumTo n + 1",
        {"T.sumTo"},
    ),
    ("well-founded recursion", "then a else", "then a + 0 else", {"T.gcd'"}),
    ("private recursion", "twice n + 2", "twice n + 3", {"_priv.T.twice"}),
    ("patterns", "| .ofNat 0 => 0", "| .ofNat 1 => 0", {"T.sign"}),
    (
        "order of two definitions that share a nested proof",
        "def box1 : Box := ⟨1, by decide⟩\n\ndef box3 : Box := ⟨1, by decide⟩",
        "def box3 : Box := ⟨1, by decide⟩\n\ndef box1 : Box := ⟨1, by decide⟩",
        set(),
    ),
    (
        "proof of a theorem, now with a match",
        "theorem self_le (n : Nat) : n ≤ n := Nat.le_refl n",
        (
            "theorem self_le (n : Nat) : n ≤ n :=\n  match n with\n"
            "  | 0 => Nat.le_refl 0\n  | k + 1 => Nat.le_refl (k + 1)"
        ),
        set(),
    ),
]
# A generated name has an owner in front (`T.sumTo._f`).  The bare `_f`, `_unary`, `_match` and
# `_proof` are the class markers that the dumper prints in place of such a name.
GENERATED = re.compile(
    r"\.(_f|_unary|_mutual|_proof_\d+|_aux_\d+|_sparseCasesOn_\d+|match_\d+(_\d+)*)$"
)
TOKEN = re.compile(r"[^\s()\[\]{}⦃⦄,]+")

Records = dict[str, dict[str, str]]


def free_percent() -> int:
    """Free memory in percent as the project measures it; 100 where it cannot be measured."""
    if shutil.which("memory_pressure") is None:
        return 100
    text = subprocess.run(
        ["memory_pressure"], check=False, capture_output=True, text=True
    ).stdout
    found = re.findall(r"(\d+)%", text.strip().splitlines()[-1]) if text.strip() else []
    return int(found[0]) if found else 100


def lean(args: list[str], cwd: Path, lean_path: Path | None = None) -> str:
    """Standard output of `lean ARGS` (the toolchain of the repository); fails on an error."""
    binary = subprocess.run(
        ["elan", "which", "lean"], cwd=REPO, check=True, capture_output=True, text=True
    ).stdout.strip()
    env = dict(os.environ)
    if lean_path is not None:
        env["LEAN_PATH"] = str(lean_path)
    proc = subprocess.run(
        [binary, *args], cwd=cwd, env=env, check=False, capture_output=True, text=True
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    return proc.stdout


def build(folder: Path, a: str) -> Path:
    """Compile the two modules below `folder`; the folder of the `.olean` files."""
    lib = folder / "lib"
    (folder / "T").mkdir(parents=True)
    (lib / "T").mkdir(parents=True)
    for name, text in (("A", a), ("B", B)):
        (folder / "T" / f"{name}.lean").write_text(text, encoding="utf-8")
        lean(
            ["--root=.", "-o", str(lib / "T" / f"{name}.olean"), f"T/{name}.lean"],
            folder,
            lib,
        )
    return lib


def dump(lib: Path, canonical: bool) -> Records:
    flags = ["--canonical"] if canonical else []
    out = lean(
        ["--run", str(DUMPER), *flags, f"--root={lib}", "--modules", "T.A", "T.B"], REPO
    )
    return {
        r["name"]: r
        for r in map(json.loads, (line for line in out.splitlines() if line))
    }


def text_of(record: dict[str, str]) -> str:
    return record["type"] + "\n" + record.get("value", "")


@pytest.fixture(scope="module")
def dumps(tmp_path_factory: pytest.TempPathFactory) -> dict[str, Records]:
    """The canonical dumps before and after the changes, and the legacy dump before them."""
    if os.environ.get("LEANDLRA_LEAN_TESTS") != "1":
        pytest.skip("real Lean runs only with LEANDLRA_LEAN_TESTS=1")
    if shutil.which("elan") is None:
        pytest.skip("no elan")
    free = free_percent()
    if free < MIN_FREE:
        pytest.skip(f"{free} % of the memory free, {MIN_FREE} % needed")
    changed = A
    for label, old, new, _ in CHANGES:
        assert changed.count(old) == 1, label
        changed = changed.replace(old, new)
    before = build(tmp_path_factory.mktemp("before"), A)
    after = build(tmp_path_factory.mktemp("after"), changed)
    return {
        "before": dump(before, True),
        "after": dump(after, True),
        "legacy": dump(before, False),
    }


def test_a_change_inside_a_helper_changes_the_record(dumps: dict[str, Records]) -> None:
    before, after = dumps["before"], dumps["after"]
    expected = set().union(*(names for *_, names in CHANGES))
    assert expected <= set(before)
    found = {name for name in before if before[name] != after.get(name)}
    assert found == expected
    # Nothing appears or disappears: the shared proof and the matcher of a proof are no records.
    assert set(before) == set(after)


def test_no_generated_name_is_left_in_a_record(dumps: dict[str, Records]) -> None:
    for name, record in dumps["before"].items():
        assert not GENERATED.search(name), name
        # A name with universe levels is printed as `T.f._f.{1}`: the token ends with a dot.
        left = [
            tok
            for tok in TOKEN.findall(text_of(record))
            if GENERATED.search(tok.rstrip("."))
        ]
        assert not left, (name, left)
    body = dumps["before"]["T.sumTo"]["value"]
    assert (
        "T.weight" in body
    )  # the functional of the recursion is printed with its content


def test_records_and_fields(dumps: dict[str, Records]) -> None:
    before = dumps["before"]
    assert {"T.weight", "T.Box", "T.Box.mk", "T.box1", "T.box3", "T.sumTo_zero"} <= set(
        before
    )
    assert before["T.sumTo"]["kind"] == "def"
    assert before["T.sumTo"]["module"] == "T.A"
    assert before["T.sumTo"]["type"] == "0 ⊢ Nat -> Nat"
    assert before["T.Paper.eq_3"]["module"] == "T.B"
    assert set(before["T.sumTo_zero"]) == {"name", "module", "kind", "type"}
    # The same nested proof gives the same text, whichever definition owns the constant.
    assert before["T.box1"]["value"] == before["T.box3"]["value"]


def test_equation_names(dumps: dict[str, Records]) -> None:
    names = set(dumps["before"])
    # Written by hand: records.  `T.Wrap` is no definition, `T.Paper` is no constant at all.
    assert {"T.Wrap.eq_1", "T.Paper.eq_17", "T.Paper.eq_3"} <= names
    # Made by Lean for `rw [sumTo]` and `rw [T.gcd']`, the second one in the other module.
    made = {
        n
        for n in names
        if re.search(r"^T\.(sumTo|gcd')\.(eq_\d+|eq_def|eq_unfold)$", n)
    }
    assert not made


def test_legacy_format(dumps: dict[str, Records]) -> None:
    legacy = dumps["legacy"]
    assert all(set(r) == {"name", "type"} for r in legacy.values())
    assert (
        legacy["T.self_le"]["type"]
        == "[] ⊢ forall (x : Nat), LE.le.{0} Nat instLENat x x"
    )
    assert "T.sumTo" not in legacy  # theorems only
    assert "T.Paper.eq_17" in legacy
