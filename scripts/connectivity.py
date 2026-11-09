# /// script
# requires-python = ">=3.11"
# dependencies = ["fire", "polars"]
# ///
"""Connectivity report for the declaration inventory (step 1 of ``wip/PLAN.md``).

Reads ``wip/index.json`` (written by ``scripts/Inventory.lean``) and writes ``wip/connectivity.md``:

* orphan modules: paper or catalogue modules that use no core declaration and that nothing else uses;
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

"Core" means the layer folders of the target layout (``LinearAlgebra``, ``Analysis``,
``FixedRank``, ``DLRA``, ``Integrators``, ``Tensor``, ``Kinetic``, ``Stochastic``, ``Training``,
``Filtering``, ``Control``), the old core folders (``Classical``, ``Dynamics``, ``Foundations``,
``HighOrder``, ``Matrix``, ``Randomized``, ``Stability``, ``Stiff``) and modules directly below
``LeanDLRA``. Folders in neither list are reported and treated as non-core.
"""

from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
LAYERS = (
    "LinearAlgebra",
    "Analysis",
    "FixedRank",
    "DLRA",
    "Integrators",
    "Tensor",
    "Kinetic",
    "Stochastic",
    "Training",
    "Filtering",
    "Control",
)
OLD_CORE = (
    "Classical",
    "Dynamics",
    "Foundations",
    "HighOrder",
    "Matrix",
    "Randomized",
    "Stability",
    "Stiff",
)
CORE = frozenset((*LAYERS, *OLD_CORE, "root"))
NON_CORE = frozenset(
    (
        "Literature",
        "OpenProblems",
        "Novel",
        "Corrections",
        "Counterexamples",
        "Research",
        "References",
        "Examples",
    )
)
DEFS_RULE_KINDS = frozenset(
    ("def", "abbrev", "instance", "structure", "class", "inductive", "opaque")
)
DEFS_RULE_EXEMPT_AREAS = frozenset(("Corrections", "Counterexamples"))


def area(module: str) -> str:
    """The top-level folder of a module, e.g. ``Literature`` for ``LeanDLRA.Literature.Kinetic.P...``."""
    parts = module.split(".")
    return parts[1] if len(parts) > 2 else "root"


def is_core(module: str) -> bool:
    """Whether a module belongs to the core: a layer folder, an old core folder or the root."""
    return area(module) in CORE


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
    index: str = "wip/index.json", out: str = "wip/connectivity.md", limit: int = 40
) -> None:
    """Write the connectivity report."""
    import polars as pl  # imported here so that the tests need only pytest

    decls: list[dict[str, Any]] = json.loads((ROOT / index).read_text(encoding="utf-8"))
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
            if is_core(umod):
                uses_core[mod] = True
            used_from_outside[umod] = True

    modules = sorted({d["module"] for d in decls})
    non_core = [m for m in modules if not is_core(m)]
    orphans = [m for m in non_core if not uses_core[m] and not used_from_outside[m]]
    no_core = [m for m in non_core if not uses_core[m]]

    local_only: list[list[str]] = []
    for d in decls:
        if d["kind"] != "theorem" or d["private"] or is_core(d["module"]):
            continue
        type_uses = [u for u in d["typeUses"] if u in module_of]
        if type_uses and not any(is_core(module_of[u]) for u in type_uses):
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

    per_area: dict[str, list[int]] = defaultdict(lambda: [0, 0])
    for m in non_core:
        per_area[area(m)][0] += 1
        per_area[area(m)][1] += 0 if uses_core[m] else 1
    unclassified = sorted({area(m) for m in modules} - CORE - NON_CORE)

    violations = defs_rule_violations(decls)
    core_violations = [v for v in violations if is_core(v[2])]
    by_area: dict[str, int] = defaultdict(int)
    modules_by_area: dict[str, set[str]] = defaultdict(set)
    for _, _, m in violations:
        by_area[area(m)] += 1
        modules_by_area[area(m)].add(m)
    per_module: dict[str, int] = defaultdict(int)
    for _, _, m in core_violations:
        per_module[m] += 1
    kinds_note = (
        ""
        if any("defKind" in d for d in decls)
        else " (index without `defKind`: instances and notation counted as definitions)"
    )

    parts = [
        "# Connectivity report (generated by scripts/connectivity.py)",
        "",
        (
            f"{len(decls)} declarations in {len(modules)} modules; "
            f"{len(modules) - len(non_core)} core modules, {len(non_core)} paper/catalogue modules."
        ),
        "",
        "## Summary",
        "",
        table(
            [[a, str(n), str(k)] for a, (n, k) in sorted(per_area.items())],
            ["area", "modules", "modules using no core declaration"],
        ),
        "",
        f"- Orphan modules (use no core declaration, used by nothing else): {len(orphans)}",
        f"- Theorems stated only in local (non-core) library definitions: {len(local_only)}",
        f"- Statement hashes shared by theorems in different modules: {dup_stmt.height}",
        f"- Definition bodies shared across modules: {dup_def.height}",
        f"- Definition names defined in more than two modules: {repeated.height}",
        (
            f"- Defs rule (warning): {len(violations)} public definitions outside a "
            f"`Defs.lean`, {len(core_violations)} of them in core modules{kinds_note}"
        ),
        *(
            [
                f"- Folders in neither the core nor the non-core list: {', '.join(unclassified)}"
            ]
            if unclassified
            else []
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
                [
                    a,
                    "core" if a in CORE else "non-core",
                    str(n),
                    str(len(modules_by_area[a])),
                ]
                for a, n in sorted(by_area.items())
            ],
            ["area", "layer", "definitions", "modules"],
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
    ]
    (ROOT / out).write_text("\n".join(parts), encoding="utf-8")
    print(
        f"wrote {out}: {len(orphans)} orphans, {len(no_core)} modules without core use, "
        f"{len(local_only)} local-only theorems, {dup_stmt.height} duplicate statements, "
        f"{dup_def.height} duplicate definition bodies; Defs rule (warning): "
        f"{len(violations)} definitions outside a Defs.lean ({len(core_violations)} in core)"
    )


def cli() -> None:
    """Command line."""
    import fire  # imported here so that the tests need only pytest

    fire.Fire(main)


if __name__ == "__main__":
    cli()
