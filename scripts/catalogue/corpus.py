# /// script
# requires-python = ">=3.11"
# dependencies = ["fire"]
# ///
# Scope: catalogue
"""Download the core corpus and extract numbered statements (theorems, lemmas, ...)."""

from __future__ import annotations

import json
import re
import subprocess
import time
import urllib.request
from pathlib import Path

import fire

ROOT = Path(__file__).resolve().parents[2]
PDF = ROOT / "papers" / "pdf"
TXT = ROOT / "papers" / "txt"
STM = ROOT / "papers" / "statements"
CORE: list[str] = [
    "1301.1058",
    "2010.02022",
    "2104.05247",
    "2304.05660",
    "1906.01369",
    "2002.11392",
    "1709.02594",
    "2402.08607",
    "2403.02834",
    "2502.07040",
    "2608.27749",
    "2608.17157",
    "2608.12893",
    "2610.11747",
    "2507.15192",
    "2107.07282",
    "2206.09374",
    "2212.12012",
    "2311.06399",
    "2309.06125",
    "2410.17091",
    "2510.19518",
    "2607.03402",
    "2506.17475",
    "2410.18720",
    "2406.17887",
    "2505.08022",
    "2502.03006",
    "2607.05872",
    "2609.32615",
    "2610.41606",
    "2609.02721",
    "2606.31662",
    "2412.05912",
    "2306.01485",
    "2308.11581",
    "2606.15843",
    "2608.21545",
    "2412.00858",
    "2308.16720",
    "2002.12197",
    "2305.19059",
    "2312.00172",
    "2409.06384",
    "2506.15259",
    "2602.07437",
    "2610.29554",
    "2006.05211",
    "2402.05347",
    "2405.15382",
]
HEAD = re.compile(
    r"^\s*(?:\*\*)?(Theorem|Lemma|Proposition|Corollary|Remark|Assumption|Definition|Counterexample|Example)\s+"
    r"(?:\d+(?:\.\d+)*|[A-Z](?:\.\d+)?)\b.*$"
)
PROOF = re.compile(r"^\s*Proof[\.\s:]")


RELEVANT = re.compile(
    r"dynamical low|dlra|dlrt|basis.update|projector.splitting|low.rank training|bug integrator|"
    r"time.dependent low.rank|low.rank (tensor )?integrator|tucker.*integrator|tensor.train.*time|"
    r"rank.adaptive|step.and.truncate",
    re.IGNORECASE,
)


def relevant_ids() -> list[str]:
    """All catalogue entries whose title or abstract matches the DLRA relevance pattern."""
    rows = json.loads((ROOT / "papers" / "catalogue.json").read_text())
    return sorted(
        r["id"] for r in rows if RELEVANT.search(r["title"] + " " + r["summary"])
    )


def fetch(everything: bool = False) -> None:
    """Download PDFs into papers/pdf (skips existing) and convert with pdftotext.

    By default only the CORE list; with ``--everything`` all DLRA-relevant catalogue entries.
    """
    PDF.mkdir(parents=True, exist_ok=True)
    TXT.mkdir(parents=True, exist_ok=True)
    ids = sorted(set(CORE) | set(relevant_ids())) if everything else CORE
    for aid in ids:
        pdf = PDF / f"{aid}.pdf"
        if not pdf.exists() or pdf.stat().st_size < 20_000:
            req = urllib.request.Request(
                f"https://arxiv.org/pdf/{aid}",
                headers={"User-Agent": "leandlra-literature-harvest/0.1"},
            )
            try:
                with urllib.request.urlopen(req, timeout=120) as r:
                    pdf.write_bytes(r.read())
            except Exception as exc:  # noqa: BLE001
                print(f"FAILED {aid}: {exc}")
                continue
            time.sleep(3.1)
        txt = TXT / f"{aid}.txt"
        if not txt.exists():
            subprocess.run(["pdftotext", "-layout", str(pdf), str(txt)], check=False)


def extract(max_lines: int = 16) -> None:
    """Write statement blocks (head line plus following text, stopping at Proof) per paper."""
    STM.mkdir(parents=True, exist_ok=True)
    for txt in sorted(TXT.glob("*.txt")):
        lines = txt.read_text(errors="replace").splitlines()
        blocks: list[str] = []
        i = 0
        while i < len(lines):
            if HEAD.match(lines[i]):
                block = [lines[i].strip()]
                j = i + 1
                while j < len(lines) and j - i < max_lines:
                    if HEAD.match(lines[j]) or PROOF.match(lines[j]):
                        break
                    if lines[j].strip():
                        block.append(re.sub(r"\s+", " ", lines[j]).strip())
                    j += 1
                blocks.append("\n".join(block))
                i = j
            else:
                i += 1
        (STM / f"{txt.stem}.txt").write_text("\n\n".join(blocks))
    counts = {
        p.stem: p.read_text().count("\n\n") + 1 for p in sorted(STM.glob("*.txt"))
    }
    meta = {
        r["id"]: r for r in json.loads((ROOT / "papers" / "catalogue.json").read_text())
    }
    for k, v in sorted(counts.items(), key=lambda kv: -kv[1]):
        print(f"{v:4d} {k:12} {str(meta.get(k, {}).get('title', '?'))[:80]}")


if __name__ == "__main__":
    fire.Fire({"fetch": fetch, "extract": extract})
