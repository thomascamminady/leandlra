# /// script
# requires-python = ">=3.11"
# dependencies = ["fire", "polars"]
# ///
# Scope: catalogue
"""Harvest dynamical low-rank approximation papers from the arXiv API.

Writes papers/catalogue.json (metadata only). PDFs are fetched separately by `pdfs`.
"""

from __future__ import annotations

import json
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path

import fire
import polars as pl

ROOT = Path(__file__).resolve().parents[2]
PAPERS = ROOT / "papers"
ATOM = "{http://www.w3.org/2005/Atom}"
API = "http://export.arxiv.org/api/query"
USER_AGENT = "python-arxiv-harvest/1.0"

QUERIES: list[str] = [
    'ti:"dynamical low-rank"',
    'abs:"dynamical low-rank"',
    'ti:"dynamical low rank"',
    'abs:"dynamical low rank"',
    'ti:"low-rank training"',
    'abs:"basis-update" AND abs:"Galerkin"',
    'abs:"projector-splitting" AND abs:"low-rank"',
    'au:Kusch AND all:"low-rank"',
    'au:Kusch AND all:"low rank"',
    "au:Schotthofer",
    "au:Schotthoefer",
    'au:Ceruti AND all:"low-rank"',
    'au:Lubich AND all:"low-rank"',
    'au:Einkemmer AND all:"low-rank"',
    'au:Kieri AND all:"low-rank"',
    'au:Uschmajew AND all:"dynamical"',
    'au:Vandereycken AND all:"low-rank"',
    "au:Zangrando",
    'au:Tudisco AND all:"low-rank"',
    'au:Nobile AND all:"dynamical low"',
    'au:Peng AND all:"dynamical low-rank"',
    'au:Sapsis AND all:"low-rank"',
    'all:"low-rank" AND all:"Lean" AND all:"formal"',
]


def _get(url: str) -> bytes:
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=60) as resp:
        return resp.read()


def _entries(query: str, page: int = 200, limit: int = 1000) -> list[dict[str, object]]:
    out: list[dict[str, object]] = []
    for start in range(0, limit, page):
        params = urllib.parse.urlencode(
            {
                "search_query": query,
                "start": start,
                "max_results": page,
                "sortBy": "submittedDate",
                "sortOrder": "descending",
            }
        )
        root = ET.fromstring(_get(f"{API}?{params}"))
        batch = root.findall(f"{ATOM}entry")
        for e in batch:
            raw = e.findtext(f"{ATOM}id", "")
            arxiv_id = raw.rsplit("/abs/", 1)[-1].rsplit("v", 1)[0]
            out.append(
                {
                    "id": arxiv_id,
                    "title": " ".join(e.findtext(f"{ATOM}title", "").split()),
                    "published": e.findtext(f"{ATOM}published", "")[:10],
                    "authors": [
                        a.findtext(f"{ATOM}name", "")
                        for a in e.findall(f"{ATOM}author")
                    ],
                    "summary": " ".join(e.findtext(f"{ATOM}summary", "").split()),
                    "primary": (
                        pc.get("term", "")
                        if (
                            pc := e.find(
                                "{http://arxiv.org/schemas/atom}primary_category"
                            )
                        )
                        is not None
                        else ""
                    ),
                }
            )
        time.sleep(3.1)  # arXiv asks for one request every three seconds
        if len(batch) < page:
            break
    return out


def harvest() -> None:
    """Run every query and merge the results into papers/catalogue.json."""
    PAPERS.mkdir(exist_ok=True)
    seen: dict[str, dict[str, object]] = {}
    for q in QUERIES:
        got = _entries(q)
        print(f"{len(got):5d}  {q}", flush=True)
        for row in got:
            row_id = str(row["id"])
            if row_id in seen:
                queries = seen[row_id].setdefault("queries", [])
                if isinstance(queries, list):
                    queries.append(q)
            else:
                row["queries"] = [q]
                seen[row_id] = row
    rows = sorted(seen.values(), key=lambda r: str(r["published"]), reverse=True)
    (PAPERS / "catalogue.json").write_text(
        json.dumps(rows, indent=1, ensure_ascii=False)
    )
    df = pl.DataFrame(rows).with_columns(
        pl.col("published").str.slice(0, 4).alias("year")
    )
    print(f"total unique: {df.height}")
    print(df.group_by("year").len().sort("year", descending=True).head(12))


if __name__ == "__main__":
    fire.Fire({"harvest": harvest})
