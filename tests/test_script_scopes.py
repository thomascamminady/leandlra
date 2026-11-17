# Scope: both
"""Every script and test names the library it serves: ``Scope: core``, ``catalogue`` or ``both``.

The tag is a comment near the top of the file (``#`` or ``--``). Scripts and tests for the catalogue
alone are in ``scripts/catalogue/`` and ``tests/catalogue/``, and nothing else is tagged
``catalogue`` (``docs/STRUCTURE.md``).
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
TAG = re.compile(r"^(?:#|--) Scope: (\S+)\s*$")
SCOPES = {"core", "catalogue", "both"}
# The tag stands in the first lines: after a shebang, a script block or imports.
HEAD = 12


def tracked(folder: str) -> list[Path]:
    """The script or test files below a folder (no templates, no caches)."""
    base = ROOT / folder
    return sorted(
        p
        for p in base.rglob("*")
        if p.is_file()
        and "templates" not in p.relative_to(base).parts
        and "__pycache__" not in p.parts
        and p.suffix in {".py", ".sh", ".lean", ""}
    )


def scope_of(path: Path) -> list[str]:
    """The scopes named by tags in the first lines of a file."""
    with path.open(encoding="utf-8") as f:
        head = [next(f, "") for _ in range(HEAD)]
    return [m.group(1) for line in head if (m := TAG.match(line))]


FILES = tracked("scripts") + tracked("tests")


@pytest.mark.parametrize("path", FILES, ids=lambda p: str(p.relative_to(ROOT)))
def test_every_script_and_test_has_one_scope(path: Path) -> None:
    scopes = scope_of(path)
    assert len(scopes) == 1, f"{path}: expected one 'Scope:' tag, found {scopes}"
    assert scopes[0] in SCOPES
    in_catalogue = "catalogue" in path.relative_to(ROOT).parts[1:-1]
    assert (scopes[0] == "catalogue") == in_catalogue, (
        f"{path}: tagged {scopes[0]}; catalogue-only files live in a catalogue/ folder"
    )


def test_the_scripts_that_stay_in_place() -> None:
    for name in (
        "fc",
        "gate.py",
        "enqueue.sh",
        "hashdiff.py",
        "rolling.py",
        "fidelity.py",
    ):
        assert (ROOT / "scripts" / name).is_file()
    assert len(tracked("scripts/catalogue")) >= 1
