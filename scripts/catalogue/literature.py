# /// script
# requires-python = ">=3.11"
# dependencies = ["fire"]
# ///
# Scope: catalogue
"""Turn the surveyed literature results that are not formalized yet into work slices.

Writes one skeleton ``wip/Lit<id><letter>.lean`` per group of results of a paper, with the results to
state and prove listed in its header, and adds the slices to ``wip/manifest.json`` with an empty stub
list.  Unlike a roadmap slice there is no recorded statement to compare with, so these need a review of
the statements against the survey text.
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

import fire

ROOT = Path(__file__).resolve().parents[2]
WIP = ROOT / "wip"
ORDER = [
    "Foundations & geometry",
    "Matrix integrators (KSL/BUG)",
    "Rank-adaptive & parallel integrators",
    "High-order integrators",
    "Randomized, sketched & interpolatory",
    "Tensor networks",
    "Stiff, parabolic & implicit",
    "Low-rank training",
    "Kinetic equations: stability & conservation",
    "Optimal control & inverse problems",
    "Stochastic & uncertainty quantification",
    "Applications & other",
]
DIRS = dict(
    zip(
        ORDER,
        [
            "Foundations",
            "Integrators",
            "RankAdaptive",
            "HighOrder",
            "Randomized",
            "TensorNetworks",
            "Stiff",
            "Training",
            "Kinetic",
            "Control",
            "Stochastic",
            "Applications",
        ],
        strict=True,
    )
)
SIZE = 5


def wanted(result: dict[str, Any]) -> bool:
    """Results still to do: formalizable, or only partially formalized."""
    status = str(result.get("status", ""))
    return status.startswith(("formalizable", "partially"))


def rank(result: dict[str, Any]) -> int:
    """Easy results first."""
    status = str(result.get("status", ""))
    for index, word in enumerate(["easy", "medium", "hard"]):
        if word in status:
            return index
    return 1


def main(size: int = SIZE) -> None:
    """Write the skeletons and extend the manifest."""
    data = json.loads((ROOT / "docs/survey/synthesis.json").read_text(encoding="utf-8"))
    details = {
        paper["id"]: {r["label"]: r for r in paper["main_results"]}
        for paper in json.loads(
            (ROOT / "docs/survey/papers.json").read_text(encoding="utf-8")
        )
    }
    manifest: dict[str, Any] = json.loads(
        (WIP / "manifest.json").read_text(encoding="utf-8")
    )
    queue: list[str] = []
    papers = sorted(
        data["landscape"], key=lambda p: ORDER.index(p.get("topic", ORDER[-1]))
    )
    for paper in papers:
        todo = sorted((r for r in paper.get("results", []) if wanted(r)), key=rank)
        pid = paper["id"]
        tag = re.sub(r"\W", "_", pid)
        directory = DIRS[paper.get("topic", ORDER[-1])]
        for index in range(0, len(todo), size):
            chunk = todo[index : index + size]
            letter = chr(ord("a") + index // size)
            name = f"Lit{tag}{letter}"
            lines = [
                "import LeanDLRA.Integrators.BUG",
                "import LeanDLRA.Matrix.Projectors",
                "",
                "/-!",
                f"# Results of arXiv {pid}: {paper.get('short_title', '')}",
                "",
                "State and prove the results below; see `wip/LIT.md`. Replace this list by a short",
                "description of what the module proves.",
                "",
            ]
            for result in chunk:
                extra = next(iter([details.get(pid, {}).get(result["label"], {})]))
                lines.append(f"* **{result['label']}** ({result.get('status', '')}).")
                lines.append(f"  Statement: {result['statement']}".replace("-/", "- /"))
                if extra.get("assumptions"):
                    lines.append(
                        f"  Assumptions: {extra['assumptions']}".replace("-/", "- /")
                    )
                if extra.get("abstract_framework_fit"):
                    fit = extra["abstract_framework_fit"]
                    lines.append(f"  Fit: {fit}".replace("-/", "- /"))
                if result.get("note"):
                    lines.append(f"  Note: {result['note']}".replace("-/", "- /"))
            lines += [
                "-/",
                "",
                "open Set Filter Topology Finset",
                "open scoped RealInnerProductSpace Matrix",
                "",
                f"namespace LeanDLRA.Literature.P{tag}",
                "",
                f"end LeanDLRA.Literature.P{tag}",
                "",
            ]
            (WIP / f"{name}.lean").write_text("\n".join(lines), encoding="utf-8")
            manifest[name] = {
                "source": f"arXiv {pid}",
                "target": f"LeanDLRA/Literature/{directory}/P{tag}{letter}.lean",
                "stubs": [],
                "ops": [],
                "chars": 0,
            }
            queue.append(name)
    (WIP / "manifest.json").write_text(json.dumps(manifest, indent=1), encoding="utf-8")
    (WIP / "lit_queue.txt").write_text("\n".join(queue) + "\n", encoding="utf-8")
    print(f"{len(queue)} literature slices")


if __name__ == "__main__":
    fire.Fire(main)
