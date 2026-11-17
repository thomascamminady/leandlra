# Scope: both
"""Links of scripts/build_site.py into the API reference, which documents the core only."""

from __future__ import annotations

import build_site
from build_site import Decl


def decl(module: str) -> Decl:
    return Decl(name="LeanDLRA.foo", module=module, kind="theorem", line=3, doc="")


def test_core_module_has_api_link() -> None:
    d = decl("LeanDLRA.DLRA.QuasiOptimality")
    assert build_site.has_api(d.module)
    assert d.api == "docs/LeanDLRA/DLRA/QuasiOptimality.html#LeanDLRA.foo"
    assert "<sup>[api](docs/LeanDLRA/DLRA/QuasiOptimality.html#LeanDLRA.foo)</sup>" in (
        build_site.decl_link(d)
    )


def test_catalogue_module_has_no_api_link() -> None:
    for folder in ("Literature", "OpenProblems", "Novel", "Corrections"):
        d = decl(f"LeanDLRA.{folder}.X.Y")
        assert not build_site.has_api(d.module)
        assert d.api == ""
        assert build_site.decl_link(d) == f"[`foo`]({d.src})"


def test_folder_name_inside_a_core_path_is_not_catalogue() -> None:
    assert build_site.has_api("LeanDLRA.Research.NovelSchemes")


def test_repo_links_of_the_catalogue_pages() -> None:
    text = (
        "[a](../../LeanDLRA/X.lean#L3) [p](PROVEN.md) [c](../CONCEPTS.md) [s](survey/)"
    )
    out = build_site.rewrite_repo_links(text, "docs/catalogue/NOVEL.md")
    blob = f"{build_site.REPO_URL}/blob/main"
    assert out == (
        f"[a]({blob}/LeanDLRA/X.lean#L3) [p](proven.html) [c]({blob}/docs/CONCEPTS.md) "
        f"[s]({build_site.REPO_URL}/tree/main/docs/catalogue/survey)"
    )
    readme = "[n](docs/catalogue/NOVEL.md) [k](docs/catalogue/CORRECTIONS.md#x)"
    assert build_site.rewrite_repo_links(readme, "README.md") == (
        "[n](novel.html) [k](corrections.html#x)"
    )
