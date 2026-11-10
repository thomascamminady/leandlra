# /// script
# requires-python = ">=3.11"
# dependencies = ["fire", "polars"]
# ///
"""Connectivity report for the declaration inventory (step 1 of ``wip/PLAN.md``).

Reads ``wip/index.json`` (written by ``scripts/Inventory.lean``) and writes ``wip/connectivity.md``:

* how the catalogue connects to the core: per folder the catalogue modules with a statement that
  mentions a core declaration, the modules that use the core only inside proofs or bodies, and the
  standalone modules (no use of a core declaration); the same for the public theorems;
* orphan modules: catalogue modules that use no core declaration and that nothing else uses;
* theorems whose statement mentions library declarations but no core one (stated in local definitions);
* groups of theorems with the same statement hash in different modules (duplicate statements);
* groups of definitions with the same body hash (definitions that unfold to the same term);
* local definition names that occur in several modules (candidates for one core definition);
* the ``Defs.lean`` rule of ``docs/CONVENTIONS.md`` §3, in warning mode: public definitions,
  abbreviations, structures, classes, inductive types and (non-scoped) instances outside a file
  named ``Defs.lean``. Exempt: private and generated declarations (projections, notation), scoped
  instances, ``Examples`` namespaces and the ``Corrections``/``Counterexamples`` folders. With an
  index written before ``defKind`` existed, a definition ``S.f`` next to a structure ``S`` in the
  same module counts as a projection.

"Core" is the notion of ``scripts/core.py`` and ``docs/STRUCTURE.md``: the modules imported by
``LeanDLRA.lean`` (the core folders and the modules of ``docs/promoted.txt``, written there by
``scripts/gen_root.sh``). Every other module is a catalogue module. The index is as old as the last
run of ``scripts/Inventory.lean``; the report says how many modules of today it does not know.
"""

from __future__ import annotations

import json
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import core

ROOT = Path(__file__).resolve().parent.parent
DEFS_RULE_KINDS = frozenset(
    ("def", "abbrev", "instance", "structure", "class", "inductive", "opaque")
)
DEFS_RULE_EXEMPT_AREAS = frozenset(("Corrections", "Counterexamples"))


def area(module: str) -> str:
    """The top-level folder of a module, e.g. ``Literature`` for ``LeanDLRA.Literature.Kinetic.P...``."""
    parts = module.split(".")
    return parts[1] if len(parts) > 2 else "root"


def core_set(root: Path = ROOT) -> frozenset[str]:
    """The core modules: those imported by ``LeanDLRA.lean`` (``scripts/core.py``)."""
    return frozenset(core.core_modules(root))


@dataclass
class Connection:
    """How the catalogue modules of one folder connect to the core."""

    modules: int = 0
    stated: int = 0  # modules with a public theorem whose statement mentions the core
    used_only: int = (
        0  # modules that use the core, but in no statement of a public theorem
    )
    standalone: int = 0  # modules that use no core declaration at all
    theorems: int = 0  # public theorems
    theorems_core: int = 0  # the statement mentions a core declaration
    theorems_local: int = (
        0  # the statement mentions library declarations, none of the core
    )
    theorems_mathlib: int = 0  # the statement mentions no library declaration


def catalogue_connection(
    decls: list[dict[str, Any]], core_modules: frozenset[str]
) -> dict[str, Connection]:
    """Per folder (and under ``all``): how the catalogue modules connect to the core.

    A declaration mentions or uses the core if one of the library declarations in its ``typeUses``
    (statement) or ``uses`` (statement, body or proof) belongs to a core module.
    """
    module_of: dict[str, str] = {d["name"]: d["module"] for d in decls}

    def in_core(names: list[str]) -> bool:
        return any(module_of.get(u) in core_modules for u in names)

    stated: set[str] = set()
    uses_core: set[str] = set()
    out: dict[str, Connection] = defaultdict(Connection)
    for d in decls:
        module: str = d["module"]
        if module in core_modules:
            continue
        if in_core(d["uses"]) or in_core(d["typeUses"]):
            uses_core.add(module)
        if d["kind"] != "theorem" or d["private"]:
            continue
        library = [u for u in d["typeUses"] if u in module_of]
        if in_core(library):
            field = "theorems_core"
            stated.add(module)
        else:
            field = "theorems_local" if library else "theorems_mathlib"
        for key in (area(module), "all"):
            out[key].theorems += 1
            setattr(out[key], field, getattr(out[key], field) + 1)
    for module in {d["module"] for d in decls} - core_modules:
        for key in (area(module), "all"):
            out[key].modules += 1
            if module in stated:
                out[key].stated += 1
            elif module in uses_core:
                out[key].used_only += 1
            else:
                out[key].standalone += 1
    return dict(out)


def defs_rule_violations(decls: list[dict[str, Any]]) -> list[tuple[str, str, str]]:
    """``(name, kind, module)`` of the public definitions outside a ``Defs.lean``."""
    structures = {(d["name"], d["module"]) for d in decls if d["kind"] == "structure"}
    out: list[tuple[str, str, str]] = []
    for d in decls:
        name: str = d["name"]
        module: str = d["module"]
        if d["private"] or module.split(".")[-1] == "Defs":
            continue
        if area(module) in DEFS_RULE_EXEMPT_AREAS or "Examples" in name.split(".")[:-1]:
            continue
        kind: str | None = d.get("defKind")
        if kind is None:  # index without `defKind`
            kind = d["kind"]
            if kind not in ("def", "structure"):
                continue
            if kind == "def" and (name.rpartition(".")[0], module) in structures:
                continue  # probably a structure projection
        elif kind not in DEFS_RULE_KINDS:
            continue
        out.append((name, kind, module))
    return out


def table(rows: list[list[str]], header: list[str]) -> str:
    """A Markdown table."""
    lines = ["| " + " | ".join(header) + " |", "|" + "---|" * len(header)]
    lines += ["| " + " | ".join(r) + " |" for r in rows]
    return "\n".join(lines)


def main(
    index: str = "wip/index.json",
    out: str = "wip/connectivity.md",
    limit: int = 40,
    root: str = "",
) -> None:
    """Write the connectivity report (``root``: the repository, default the one of this script)."""
    import polars as pl  # imported here so that the tests need only pytest

    base = Path(root).resolve() if root else ROOT
    core_modules = core_set(base)
    decls: list[dict[str, Any]] = json.loads((base / index).read_text(encoding="utf-8"))
    df = pl.DataFrame(
        {
            "name": [d["name"] for d in decls],
            "module": [d["module"] for d in decls],
            "kind": [d["kind"] for d in decls],
            "private": [d["private"] for d in decls],
            "typeHash": [d["typeHash"] for d in decls],
            "bodyHash": [d["bodyHash"] for d in decls],
        }
    )
    module_of: dict[str, str] = {d["name"]: d["module"] for d in decls}
    uses_core: dict[str, bool] = defaultdict(bool)
    used_from_outside: dict[str, bool] = defaultdict(bool)
    for d in decls:
        mod = d["module"]
        for u in d["uses"]:
            umod = module_of.get(u)
            if umod is None or umod == mod:
                continue
            if umod in core_modules:
                uses_core[mod] = True
            used_from_outside[umod] = True

    modules = sorted({d["module"] for d in decls})
    non_core = [m for m in modules if m not in core_modules]
    orphans = [m for m in non_core if not uses_core[m] and not used_from_outside[m]]
    no_core = [m for m in non_core if not uses_core[m]]
    today = set(core.all_modules(base))
    unknown = sorted(today - set(modules))
    gone = sorted(set(modules) - today)
    connection = catalogue_connection(decls, core_modules)
    total = connection.get("all", Connection())

    local_only: list[list[str]] = []
    for d in decls:
        if d["kind"] != "theorem" or d["private"] or d["module"] in core_modules:
            continue
        type_uses = [u for u in d["typeUses"] if u in module_of]
        if type_uses and not any(module_of[u] in core_modules for u in type_uses):
            local_only.append([d["name"], d["module"]])

    theorems = df.filter((pl.col("kind") == "theorem") & ~pl.col("private"))
    dup_stmt = (
        theorems.group_by("typeHash")
        .agg(pl.col("name"), pl.col("module").n_unique().alias("modules"))
        .filter(pl.col("modules") > 1)
        .sort(pl.col("name").list.len(), descending=True)
    )
    defs = df.filter((pl.col("kind") == "def") & (pl.col("bodyHash") != ""))
    dup_def = (
        defs.group_by("bodyHash")
        .agg(pl.col("name"), pl.col("module").n_unique().alias("modules"))
        .filter(pl.col("modules") > 1)
        .sort(pl.col("name").list.len(), descending=True)
    )
    short = df.filter(
        pl.col("kind").is_in(["def", "structure"]) & ~pl.col("private")
    ).with_columns(pl.col("name").str.split(".").list.last().alias("short"))
    repeated = (
        short.group_by("short")
        .agg(pl.col("module").n_unique().alias("modules"))
        .filter(pl.col("modules") > 2)
        .sort("modules", descending=True)
    )

    violations = defs_rule_violations(decls)
    core_violations = [v for v in violations if v[2] in core_modules]
    by_area: dict[str, int] = defaultdict(int)
    core_by_area: dict[str, int] = defaultdict(int)
    modules_by_area: dict[str, set[str]] = defaultdict(set)
    for _, _, m in violations:
        by_area[area(m)] += 1
        core_by_area[area(m)] += m in core_modules
        modules_by_area[area(m)].add(m)
    per_module: dict[str, int] = defaultdict(int)
    for _, _, m in core_violations:
        per_module[m] += 1
    kinds_note = (
        ""
        if any("defKind" in d for d in decls)
        else " (index without `defKind`: instances and notation counted as definitions)"
    )
    areas = sorted(a for a in connection if a != "all")

    parts = [
        "# Connectivity report (generated by scripts/connectivity.py)",
        "",
        (
            f"{len(decls)} declarations in {len(modules)} modules of the index `{index}`; "
            f"{len(modules) - len(non_core)} core modules (listed in `LeanDLRA.lean`), "
            f"{len(non_core)} catalogue modules."
        ),
        (
            f"Age of the index: {len(unknown)} of the {len(today)} modules of today are not in "
            f"it, {len(gone)} of its modules have no source file any more."
        ),
        "",
        "## The catalogue and the core",
        "",
        (
            "Catalogue modules by what connects them to the core. A statement is the type of a public "
            "theorem; a use is a mention in a statement, a definition body or a proof."
        ),
        "",
        table(
            [
                [a, *(str(v) for v in _module_row(connection[a]))]
                for a in [*areas, "all"]
            ],
            [
                "folder",
                "catalogue modules",
                "a statement mentions a core declaration",
                "core used only in proofs or bodies",
                "standalone (no use of the core)",
            ],
        ),
        "",
        table(
            [
                [a, *(str(v) for v in _theorem_row(connection[a]))]
                for a in [*areas, "all"]
            ],
            [
                "folder",
                "public theorems",
                "statement mentions a core declaration",
                "statement in local definitions only",
                "statement in Mathlib terms only",
            ],
        ),
        "",
        "## Summary",
        "",
        (
            f"- Catalogue modules with a statement in core terms: {total.stated} of "
            f"{total.modules}; standalone: {total.standalone}"
        ),
        (
            f"- Catalogue theorems whose statement mentions a core declaration: "
            f"{total.theorems_core} of {total.theorems}"
        ),
        f"- Orphan modules (use no core declaration, used by nothing else): {len(orphans)}",
        f"- Theorems stated only in local (non-core) library definitions: {len(local_only)}",
        f"- Statement hashes shared by theorems in different modules: {dup_stmt.height}",
        f"- Definition bodies shared across modules: {dup_def.height}",
        f"- Definition names defined in more than two modules: {repeated.height}",
        (
            f"- Defs rule (warning): {len(violations)} public definitions outside a "
            f"`Defs.lean`, {len(core_violations)} of them in core modules{kinds_note}"
        ),
        "",
        "## Orphan modules",
        "",
        *[f"- `{m}`" for m in orphans],
        "",
        "## Modules that use no core declaration",
        "",
        *[f"- `{m}`" for m in no_core],
        "",
        f"## Theorems stated only in local definitions (first {limit})",
        "",
        table(local_only[:limit], ["theorem", "module"]),
        "",
        f"## Duplicate statements (first {limit} groups)",
        "",
        *[
            f"- {', '.join(f'`{n}`' for n in row['name'])}"
            for row in dup_stmt.head(limit).iter_rows(named=True)
        ],
        "",
        f"## Definitions with the same body (first {limit} groups)",
        "",
        *[
            f"- {', '.join(f'`{n}`' for n in row['name'])}"
            for row in dup_def.head(limit).iter_rows(named=True)
        ],
        "",
        "## Definition names in more than two modules",
        "",
        table(
            [[r["short"], str(r["modules"])] for r in repeated.iter_rows(named=True)],
            ["name", "modules"],
        ),
        "",
        "## Defs rule (warning mode): public definitions outside a `Defs.lean`",
        "",
        "Rule: `docs/CONVENTIONS.md` §3. Not enforced yet.",
        "",
        table(
            [
                [a, str(n), str(core_by_area[a]), str(len(modules_by_area[a]))]
                for a, n in sorted(by_area.items())
            ],
            ["folder", "definitions", "of these in core modules", "modules"],
        ),
        "",
        "### Core modules by number of definitions outside a `Defs.lean`",
        "",
        table(
            [
                [m, str(n)]
                for m, n in sorted(per_module.items(), key=lambda x: (-x[1], x[0]))
            ],
            ["module", "definitions"],
        ),
        "",
        f"### Core definitions outside a `Defs.lean` (first {limit})",
        "",
        table(
            [[f"`{n}`", k, m] for n, k, m in core_violations[:limit]],
            ["name", "kind", "module"],
        ),
        "",
        "## Modules of today that the index does not know",
        "",
        *[f"- `{m}`" for m in unknown],
        "",
    ]
    (base / out).write_text("\n".join(parts), encoding="utf-8")
    print(
        f"wrote {out}: {total.modules} catalogue modules, {total.stated} with a statement in "
        f"core terms, {total.used_only} using the core only in proofs or bodies, "
        f"{total.standalone} standalone; {total.theorems_core} of {total.theorems} catalogue "
        f"theorems mention a core declaration; {len(orphans)} orphans, "
        f"{len(local_only)} local-only theorems, {dup_stmt.height} duplicate statements, "
        f"{dup_def.height} duplicate definition bodies; Defs rule (warning): "
        f"{len(violations)} definitions outside a Defs.lean ({len(core_violations)} in core); "
        f"index does not know {len(unknown)} modules of today"
    )


def _module_row(c: Connection) -> tuple[int, int, int, int]:
    return c.modules, c.stated, c.used_only, c.standalone


def _theorem_row(c: Connection) -> tuple[int, int, int, int]:
    return c.theorems, c.theorems_core, c.theorems_local, c.theorems_mathlib


def cli() -> None:
    """Command line."""
    import fire  # imported here so that the tests need only pytest

    fire.Fire(main)


if __name__ == "__main__":
    cli()
