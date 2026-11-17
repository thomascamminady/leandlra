# Scope: both
"""Relative links of the tracked Markdown pages point to files that exist.

The pages of the catalogue are in ``docs/catalogue/`` (``docs/STRUCTURE.md``); a template of
``scripts/templates/`` is read from ``docs/``, where its page is written.
"""

from __future__ import annotations

import re
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
LINK = re.compile(r"\]\(([^)\s#]+)(?:#[^)\s]*)?\)")
FENCE = re.compile(r"^```.*?^```", re.DOTALL | re.MULTILINE)


def pages() -> list[str]:
    """The tracked Markdown files outside the Lean sources."""
    try:
        out = subprocess.run(
            ["git", "ls-files", "*.md"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=True,
        ).stdout
    except (OSError, subprocess.CalledProcessError):
        return []
    return [p for p in out.split() if not p.startswith("LeanDLRA/")]


def broken_links(page: str) -> list[str]:
    """The relative link targets of a page that do not exist."""
    base = ROOT / (
        "docs" if page.startswith("scripts/templates/") else Path(page).parent
    )
    text = FENCE.sub("", (ROOT / page).read_text(encoding="utf-8"))
    return [
        target
        for target in LINK.findall(text)
        if not re.match(r"^[a-z]+:", target)
        and not target.startswith("/")
        and ("/" in target or "." in target)
        and not (base / target).exists()
    ]


@pytest.mark.parametrize("page", pages())
def test_relative_links_exist(page: str) -> None:
    assert broken_links(page) == []


def test_catalogue_pages_live_in_docs_catalogue() -> None:
    for name in ("PROVEN.md", "NOVEL.md", "CORRECTIONS.md", "survey"):
        assert (ROOT / "docs" / "catalogue" / name).exists()
        assert not (ROOT / "docs" / name).exists()
    assert (ROOT / "docs" / "catalogue" / "CATALOGUE.md").is_file()
