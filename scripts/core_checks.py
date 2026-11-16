# /// script
# requires-python = ">=3.11"
# dependencies = ["fire"]
# ///
"""Checks of the core library that need no Lean: where definitions stand, duplicate statements,
theorems without an example.

"Core" is the notion of ``scripts/core.py``: the modules imported by ``LeanDLRA.lean``. The checks
compare with a baseline (``docs/core_checks_baseline.json``, written by ``baseline``), so that they
can block a round on *new* findings while the old ones are being worked off; ``--strict`` ignores
the baseline.

``defs``: the ``Defs.lean`` rule of ``docs/CONVENTIONS.md`` §3, read from the sources: a public
``def``, ``abbrev``, ``structure``, ``class``, ``inductive``, ``opaque`` or non-scoped ``instance``
in a core file that is not a ``Defs.lean``. Exempt: ``private``, ``scoped`` and ``local``
declarations, declarations in or below a namespace whose name ends in ``Example`` or
``Examples`` and the ``Corrections`` and ``Counterexamples`` folders. A source scan, not the
elaborated environment: it sees what the author wrote (no projections, no ``match_1``), it does
not see a definition that a macro makes.

``duplicates``: two public theorems of the core whose elaborated statements have the same hash, from
the rolling record ``.lake/hashdiff/rolling_statements.jsonl.gz`` (``scripts/rolling.py``; the type
is printed with binder names erased, so it is the statement and nothing else).

``vacuity``: the non-vacuity rule (every general theorem has an ``example`` showing that its
hypotheses can hold), as a heuristic on the sources: a public ``theorem`` or ``lemma`` of a core
file that has hypotheses (``has_hypotheses``: a binder with a relation or an ``Is…``/``Has…``
predicate in its type, or named ``h…`` with a type that is not data, or an implication in the
statement) and whose name (its last component, as an identifier, also after a dot) occurs in no
``example`` of the same file and nowhere inside a namespace or section of the file whose name
ends in ``Example`` or ``Examples``. Not seen: hypotheses from ``variable``, data-like binders
that are propositions, witnesses in other files; a different declaration with the same last
component counts as a mention.

    uv run -q scripts/core_checks.py defs [--strict] [--list]
    uv run -q scripts/core_checks.py duplicates [--strict] [--list]
    uv run -q scripts/core_checks.py vacuity [--strict] [--list]
    uv run -q scripts/core_checks.py baseline [--only=vacuity,...]   # today's findings

Exit 0: no finding beyond the baseline. Exit 1: a new finding (printed). Exit 2: nothing to read
(no record, no core root file).
"""

from __future__ import annotations

import gzip
import hashlib
import json
import re
import sys
from collections import defaultdict
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path

import core

ROOT = Path(__file__).resolve().parent.parent
BASELINE = "docs/core_checks_baseline.json"
RECORD = ".lake/hashdiff/rolling_statements.jsonl.gz"
EXEMPT_AREAS = frozenset(("Corrections", "Counterexamples"))

_BLOCK_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)
_LINE_COMMENT = re.compile(r"--[^\n]*")
_NAMESPACE = re.compile(r"^\s*namespace\s+(\S+)")
# A scope that `end` closes without being a namespace: a section (also `noncomputable section`)
# and a `mutual` block.
_SECTION = re.compile(r"^\s*(?:noncomputable\s+)?section\b|^\s*mutual\b")
_END = re.compile(r"^\s*end\b(?:\s+\S+)?\s*$")
_DECL = re.compile(
    r"^\s*(?:(?:open|set_option)\b[^\n]*?\bin\s+)?"
    r"(?:@\[[^\]]*\]\s*)*"
    r"((?:(?:public|noncomputable|protected|unsafe|partial|nonrec|scoped|local|private)\s+)*)"
    r"(class\s+inductive|irreducible_def|def|abbrev|structure|class|inductive|instance"
    r"|opaque|theorem|lemma)\b(.*)"
)
_PRIORITY = re.compile(r"^\s*\(priority\s*:=[^)]*\)")
_NAME = re.compile(r"^\s*([^\s:({\[⦃⟨]+)")
# The kinds of declaration that the `Defs.lean` rule covers.
DEFINITION_KINDS = frozenset(
    ("def", "abbrev", "structure", "class", "inductive", "instance", "opaque")
)


@dataclass(frozen=True)
class Declaration:
    """A declaration of a source text, as the source writes it.

    ``name`` is qualified with the namespaces open at the declaration (``_root_.`` removed); an
    unnamed instance (``named`` false) gets the name ``instance`` under them. ``in_examples``:
    a namespace of the name ends in ``Example`` or ``Examples``.
    """

    line: int
    kind: str
    name: str
    modifiers: frozenset[str]
    named: bool
    in_examples: bool


def strip_comments(text: str) -> str:
    """The text without comments; line breaks inside a block comment stay (line numbers)."""
    keep = lambda m: "\n" * m.group(0).count("\n")
    return _LINE_COMMENT.sub("", _BLOCK_COMMENT.sub(keep, text))


def declarations_in(text: str) -> list[Declaration]:
    """The theorems, lemmas, definitions, structures, classes, inductive types, instances and
    opaque constants of a source text, in their order.

    A line scan of the text without comments: a declaration starts a line (after attributes,
    modifiers and ``open … in``); ``namespace``, ``section``, ``mutual`` and ``end`` are
    followed. A declaration that a macro makes is not seen; ``irreducible_def`` counts as
    ``def``, ``class inductive`` as ``class``.
    """
    stack: list[list[str]] = []
    out: list[Declaration] = []
    for number, line in enumerate(strip_comments(text).splitlines(), start=1):
        if m := _NAMESPACE.match(line):
            stack.append(m.group(1).split("."))
        elif _SECTION.match(line):
            stack.append([])
        elif _END.match(line):
            if stack:
                stack.pop()
        elif m := _DECL.match(line):
            kind = m.group(2).split()[0]
            kind = "def" if kind == "irreducible_def" else kind
            rest = _PRIORITY.sub("", m.group(3)) if kind == "instance" else m.group(3)
            found = _NAME.match(rest)
            name = found.group(1).rstrip(".") if found else ""
            namespaces = [c for scope in stack for c in scope]
            if name.startswith("_root_."):
                namespaces, name = [], name.removeprefix("_root_.")
            parts = namespaces + (name or "instance").split(".")
            out.append(
                Declaration(
                    line=number,
                    kind=kind,
                    name=".".join(parts),
                    modifiers=frozenset(m.group(1).split()),
                    named=bool(name),
                    in_examples=any(
                        c.endswith(("Example", "Examples")) for c in parts[:-1]
                    ),
                )
            )
    return out


def definitions_in(text: str) -> list[tuple[int, str, str]]:
    """``(line, kind, qualified name)`` of the public definitions of a source text that the
    ``Defs.lean`` rule covers (unnamed instances get the name ``instance``)."""
    return [
        (d.line, d.kind, d.name)
        for d in declarations_in(text)
        if d.kind in DEFINITION_KINDS
        and not {"private", "scoped", "local"} & d.modifiers
        and not d.in_examples
    ]


def defs_findings(root: Path = ROOT) -> list[tuple[str, int, str, str]]:
    """``(module, line, kind, name)`` of the violations of the ``Defs.lean`` rule in the core."""
    out: list[tuple[str, int, str, str]] = []
    for module in core.core_modules(root):
        parts = module.split(".")
        if parts[-1] == "Defs" or (len(parts) > 2 and parts[1] in EXEMPT_AREAS):
            continue
        path = core.source_of(module, root)
        if not path.exists():
            continue
        for line, kind, name in definitions_in(path.read_text(encoding="utf-8")):
            out.append((module, line, kind, name))
    return out


def duplicate_groups(root: Path = ROOT) -> list[list[tuple[str, str]]]:
    """Groups of ``(module, theorem)`` of the core with one statement hash, largest first."""
    path = root / RECORD
    modules = frozenset(core.core_modules(root))
    by_hash: dict[str, list[tuple[str, str]]] = defaultdict(list)
    with gzip.open(path, "rt", encoding="utf-8") as f:
        for number, line in enumerate(f):
            if number == 0:
                continue  # the header
            entry = json.loads(line)
            if entry["module"] in modules:
                digest = hashlib.sha256(entry["type"].encode()).hexdigest()
                by_hash[digest].append((entry["module"], entry["name"]))
    groups = [sorted(g) for g in by_hash.values() if len(g) > 1]
    return sorted(groups, key=lambda g: (-len(g), g))


# -- non-vacuity ----------------------------------------------------------------------------------

_OPEN, _CLOSE = "([{⦃⟨", ")]}⦄⟩"
# Tokens that contain a relation sign without being one: arrows, `fun` arrows, assignments and the
# types `ℝ≥0`, `ℝ≥0∞`.
_NOT_RELATION = re.compile(r"=>|->|<-|<;>|:=|ℝ≥0∞?")
_RELATION = re.compile(r"[=≠≤<≥>∈∉⊆⊂↔∧∨¬∣]")
_PREDICATE = re.compile(r"^\s*@?(?:[\w.']*\.)?(?:Is|Has)[A-Z]")
# The head of a type of data: numbers, types, matrices, sets, and type variables (one letter).
_DATA = re.compile(
    r"^\s*(?:ℝ|ℕ|ℤ|ℂ|ℚ|Real|Nat|Int|Complex|Type|Sort|Fin|Matrix|Set|Finset|List"
    r"|[A-Za-zα-ωΑ-Ω𝕜][₀-₉']*)(?![\w.])"
)
_ARROW = re.compile(r"→|(?<![<=-])->")
_SCOPE = re.compile(r"^\s*(?:noncomputable\s+)?(?:namespace|section)\s+(\S+)\s*$")
_PLAIN_SCOPE = re.compile(r"^\s*(?:(?:noncomputable\s+)?section|mutual)\s*$")
_EXAMPLE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*example\b")
_THEOREM_KINDS = frozenset(("theorem", "lemma"))


def extent(lines: list[str], start: int) -> str:
    """The command that starts on line ``start`` (0-based): up to the next line that starts in
    column 0 (a ``|`` of a pattern match does not end it)."""
    end = start + 1
    while end < len(lines) and not (lines[end][:1].strip() and lines[end][0] != "|"):
        end += 1
    return "\n".join(lines[start:end])


def top_level(text: str) -> str:
    """The characters of a text outside every bracket."""
    out: list[str] = []
    depth = 0
    for ch in text:
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth = max(depth - 1, 0)
        elif depth == 0:
            out.append(ch)
    return "".join(out)


def binders_and_statement(head: str) -> tuple[list[tuple[str, str]], str]:
    """The binder groups ``(bracket, content)`` of a declaration head (the text after the name,
    before ``:=``) and the statement after its colon outside brackets."""
    groups: list[tuple[str, str]] = []
    depth, begin = 0, 0
    for i, ch in enumerate(head):
        if ch in _OPEN:
            if depth == 0:
                begin = i
            depth += 1
        elif ch in _CLOSE:
            depth = max(depth - 1, 0)
            if depth == 0:
                groups.append((head[begin], head[begin + 1 : i]))
        elif ch == ":" and depth == 0:
            return groups, head[i + 1 :]
    return groups, ""


def is_hypothesis(names: str, kind: str) -> bool:
    """Whether a binder group ``names : kind`` assumes something."""
    bare = top_level(_NOT_RELATION.sub(" ", kind))
    if _RELATION.search(bare) or _PREDICATE.match(kind):
        return True
    named = any(n.startswith("h") for n in names.split())
    return named and not _DATA.match(kind) and not _ARROW.search(bare)


def has_hypotheses(head: str) -> bool:
    """Whether a theorem head (the text after its name, before ``:=``) assumes something.

    A heuristic: an explicit, implicit or strict-implicit binder whose type has a relation
    (``= ≠ ≤ < ≥ > ∈ ∉ ⊆ ⊂ ↔ ∧ ∨ ¬ ∣``) outside brackets or starts with a predicate ``Is…`` or
    ``Has…``, or that is named like a hypothesis (``h…``) and whose type is neither data (a number
    type, ``Type``, ``Fin``, ``Matrix``, ``Set``, a one-letter type variable) nor a function type;
    or an implication ``→`` outside brackets in the statement. Instance binders ``[…]`` do not
    count.
    """
    groups, statement = binders_and_statement(head)
    for bracket, content in groups:
        names, colon, kind = content.partition(":")
        if bracket in "({⦃" and colon and is_hypothesis(names, kind):
            return True
    return bool(_ARROW.search(top_level(_NOT_RELATION.sub(" ", statement))))


def examples_of(text: str) -> tuple[str, frozenset[int]]:
    """The witness text of a source text, and the numbers of the lines inside example scopes.

    The witness text is every ``example`` command and everything inside a namespace or section
    whose name ends in ``Example`` or ``Examples`` (the helpers of the examples)."""
    lines = strip_comments(text).splitlines()
    out: list[str] = []
    inside: set[int] = set()
    scopes: list[bool] = []
    for i, line in enumerate(lines):
        if m := _SCOPE.match(line):
            scopes.append(m.group(1).endswith(("Example", "Examples")))
        elif _PLAIN_SCOPE.match(line):
            scopes.append(False)
        elif _END.match(line):
            if scopes:
                scopes.pop()
        elif any(scopes):
            out.append(line)
            inside.add(i + 1)
        elif _EXAMPLE.match(line):
            out.append(extent(lines, i))
    return "\n".join(out), frozenset(inside)


def mentions(witness: str, name: str) -> bool:
    """Whether the last component of a name occurs in the witness text as an identifier (also
    after a dot: dot notation and qualified names count)."""
    last = re.escape(name.rsplit(".", 1)[-1])
    return re.search(rf"(?<![\w'!?]){last}(?![\w'!?])", witness) is not None


def unwitnessed(text: str) -> list[tuple[int, str]]:
    """``(line, name)`` of the public theorems of a source text that have hypotheses and that no
    example of the text mentions (outside example scopes)."""
    lines = strip_comments(text).splitlines()
    witness, inside = examples_of(text)
    out: list[tuple[int, str]] = []
    for d in declarations_in(text):
        if d.kind not in _THEOREM_KINDS or "private" in d.modifiers:
            continue
        if d.in_examples or d.line in inside:
            continue
        command = extent(lines, d.line - 1)
        m = _DECL.match(command)
        rest = command[m.start(3) :] if m else ""
        found = _NAME.match(rest)
        head = rest[found.end() :] if found else rest
        if has_hypotheses(head.split(":=", 1)[0]) and not mentions(witness, d.name):
            out.append((d.line, d.name))
    return out


def vacuity_findings(root: Path = ROOT) -> list[tuple[str, int, str]]:
    """``(module, line, name)`` of the public core theorems with hypotheses and no example."""
    out: list[tuple[str, int, str]] = []
    for module in core.core_modules(root):
        path = core.source_of(module, root)
        if path.exists():
            text = path.read_text(encoding="utf-8")
            out += [(module, line, name) for line, name in unwitnessed(text)]
    return out


def defs_keys(findings: list[tuple[str, int, str, str]]) -> list[str]:
    return sorted({f"{module}:{name}" for module, _, _, name in findings})


def duplicate_keys(groups: list[list[tuple[str, str]]]) -> list[str]:
    """A group is known by its sorted theorem names (stable when files move)."""
    return sorted("=".join(sorted(name for _, name in g)) for g in groups)


def vacuity_keys(findings: list[tuple[str, int, str]]) -> list[str]:
    return sorted({f"{module}:{name}" for module, _, name in findings})


def read_baseline(root: Path) -> dict[str, list[str]]:
    path = root / BASELINE
    return json.loads(path.read_text()) if path.exists() else {}


def split_list(value: object) -> list[str]:
    """The items of a comma-separated option: a string, or a sequence of strings (fire turns
    ``--x=a,b`` into a tuple), in their order, without blanks."""
    items: list[object] = list(value) if isinstance(value, (list, tuple)) else [value]
    return [
        part.strip()
        for item in items
        if item not in (None, "")
        for part in str(item).split(",")
        if part.strip()
    ]


def run_defs(root: Path, strict: bool, list_all: bool) -> int:
    findings = defs_findings(root)
    known = set() if strict else set(read_baseline(root).get("defs", []))
    new = [f for f in findings if f"{f[0]}:{f[3]}" not in known]
    shown = findings if list_all else new
    for module, line, kind, name in shown:
        print(f"DEFS-RULE {module}:{line}: public {kind} {name} outside a Defs.lean")
    print(
        f"defs: {len(findings)} violations in the core, {len(new)} not in the baseline"
    )
    return 1 if new else 0


def run_duplicates(root: Path, strict: bool, list_all: bool) -> int:
    if not (root / RECORD).exists():
        print(f"duplicates: no record {RECORD} (scripts/rolling.py seed)")
        return 2
    groups = duplicate_groups(root)
    known = set() if strict else set(read_baseline(root).get("duplicates", []))
    new = [
        g for g, k in zip(groups, duplicate_keys(groups), strict=True) if k not in known
    ]
    for g in groups if list_all else new:
        print(
            "DUPLICATE-STATEMENT "
            + "; ".join(f"{name} ({module})" for module, name in g)
        )
    print(
        f"duplicates: {len(groups)} groups in the core, {len(new)} not in the baseline"
    )
    return 1 if new else 0


def run_vacuity(root: Path, strict: bool, list_all: bool) -> int:
    findings = vacuity_findings(root)
    known = set() if strict else set(read_baseline(root).get("vacuity", []))
    new = [f for f in findings if f"{f[0]}:{f[2]}" not in known]
    for module, line, name in findings if list_all else new:
        print(
            f"NO-EXAMPLE {module}:{line}: {name} has hypotheses, no example mentions it"
        )
    files = sorted({f[0] for f in findings})
    bare = [
        m
        for m in files
        if not examples_of(core.source_of(m, root).read_text(encoding="utf-8"))[
            0
        ].strip()
    ]
    print(
        f"vacuity: {len(findings)} public core theorems with hypotheses and no example in "
        f"{len(files)} files ({len(bare)} without any example), {len(new)} not in the baseline"
    )
    return 1 if new else 0


CHECKS = ("defs", "duplicates", "vacuity")


def run_baseline(root: Path, only: Sequence[str] = ()) -> int:
    """Write the baseline of the given checks (default: all) from today's findings; the entries
    of the other checks stay. Without a record, the duplicates entry stays as it is."""
    wanted = list(only) or list(CHECKS)
    if unknown := [c for c in wanted if c not in CHECKS]:
        print(f"baseline: unknown check {unknown[0]} (known: {', '.join(CHECKS)})")
        return 2
    data = read_baseline(root)
    written: list[str] = []
    for check in wanted:
        if check == "defs":
            data["defs"] = defs_keys(defs_findings(root))
        elif check == "duplicates":
            if not (root / RECORD).exists():
                continue
            data["duplicates"] = duplicate_keys(duplicate_groups(root))
        else:
            data["vacuity"] = vacuity_keys(vacuity_findings(root))
        written.append(check)
    (root / BASELINE).write_text(json.dumps(data, indent=1, ensure_ascii=False) + "\n")
    print(f"{BASELINE}: " + ", ".join(f"{c} {len(data[c])}" for c in written))
    return 0


class Checks:
    """Checks of the core that need no Lean."""

    def defs(self, strict: bool = False, list: bool = False) -> None:
        """The Defs.lean rule on the core; list shows all findings, not only the new ones."""
        sys.exit(run_defs(ROOT, strict, list))

    def duplicates(self, strict: bool = False, list: bool = False) -> None:
        """Public core theorems with one statement hash."""
        sys.exit(run_duplicates(ROOT, strict, list))

    def vacuity(self, strict: bool = False, list: bool = False) -> None:
        """Public core theorems with hypotheses that no example of their file mentions."""
        sys.exit(run_vacuity(ROOT, strict, list))

    def baseline(self, only: object = "") -> None:
        """Write docs/core_checks_baseline.json from today's findings (--only=defs,vacuity:
        these checks only, the others stay)."""
        sys.exit(run_baseline(ROOT, split_list(only)))


if __name__ == "__main__":
    import fire  # only the command line needs it: the tests import this module without it

    fire.Fire(Checks)
