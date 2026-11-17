# /// script
# requires-python = ">=3.11"
# dependencies = ["fire"]
# ///
"""Generate the pages of the project website (Jekyll, just-the-docs theme) in ``website/``.

Inputs: README.md, docs/*.md and the declaration index ``website/decls.json`` written by
``scripts/DeclIndex.lean``. Every Lean declaration name,
``LeanDLRA/...`` path and arXiv id found in the text is turned into a link: declarations link to
their source line on GitHub and to their doc-gen4 API entry (served under ``docs/``).
"""

from __future__ import annotations

import collections
import json
import re
from dataclasses import dataclass
from pathlib import Path

import fire

ROOT = Path(__file__).resolve().parent.parent
SITE = ROOT / "website"
REPO_URL = "https://github.com/thomascamminady/leandlra"
SITE_URL = "https://camminady.dev/leandlra/"
ARXIV = re.compile(r"(?<![\w./\[])(\d{4}\.\d{4,5})(?![\w\]])")
MD_LINK = re.compile(r"\[[^\]\n]*\]\([^)\n]*\)")
CODE_SPAN = re.compile(r"`([^`\n]+)`")
TOKEN = re.compile(r"[A-Za-z_][\w.'₀-₉ᵀ⁻¹]*")
PATH = re.compile(r"LeanDLRA/[\w/]+\.lean")


@dataclass(frozen=True)
class Decl:
    """One declaration of the library."""

    name: str
    module: str
    kind: str
    line: int
    doc: str
    uses: tuple[str, ...] = ()

    @property
    def path(self) -> str:
        """Repository path of the defining file."""
        return self.module.replace(".", "/") + ".lean"

    @property
    def src(self) -> str:
        """GitHub link to the source line."""
        return f"{REPO_URL}/blob/main/{self.path}#L{self.line}"

    @property
    def api(self) -> str:
        """Site-relative link to the doc-gen4 entry ("" for a catalogue module: the API reference
        documents the core only)."""
        if not has_api(self.module):
            return ""
        return f"docs/{self.module.replace('.', '/')}.html#{self.name}"


# The catalogue folders; the API reference (workflow "API docs") documents only the modules
# outside them, so links into it are written for core modules only.
CATALOGUE_PREFIXES = tuple(
    f"LeanDLRA.{folder}."
    for folder in ("Literature", "OpenProblems", "Novel", "Corrections")
)


def has_api(module: str) -> bool:
    """Whether the API reference has a page for the module (core modules only)."""
    return not module.startswith(CATALOGUE_PREFIXES)


class Index:
    """Resolve (possibly abbreviated) Lean names to declarations."""

    def __init__(self, decls: list[Decl]) -> None:
        self.by_suffix: dict[str, list[Decl]] = collections.defaultdict(list)
        self.by_module: dict[str, list[Decl]] = collections.defaultdict(list)
        for d in decls:
            parts = d.name.split(".")
            for i in range(len(parts)):
                self.by_suffix[".".join(parts[i:])].append(d)
            self.by_module[d.module].append(d)

    def resolve(self, token: str, module: str | None = None) -> Decl | None:
        """The declaration a token refers to, if unambiguous (preferring ``module``)."""
        token = token.rstrip(".,;:")
        # only tokens that look like Lean names (snake_case, dotted or CamelCase): avoids linking
        # math symbols such as `e`, `h` and plain English words such as `blocks`
        if not re.search(r"[_.]|[A-Z]", token) or len(token) < 3:
            return None
        cands = self.by_suffix.get(token, [])
        if module:
            local = [d for d in cands if d.module == module]
            if len(local) == 1:
                return local[0]
        return cands[0] if len(cands) == 1 else None


def load_index() -> Index:
    """Load website/decls.json (empty index if it has not been generated)."""
    path = SITE / "decls.json"
    if not path.exists():
        print("warning: website/decls.json missing; Lean names will not be linked")
        return Index([])
    raw = json.loads(path.read_text(encoding="utf-8"))
    return Index(
        [
            Decl(
                name=str(d["name"]),
                module=str(d["module"]),
                kind=str(d["kind"]),
                line=int(d["line"]),
                doc=str(d["doc"]).strip(),
                uses=tuple(str(u) for u in d.get("uses", [])),
            )
            for d in raw
        ]
    )


def decl_link(d: Decl, label: str | None = None) -> str:
    """Markdown for a declaration: code link to source plus a small API link (core only)."""
    code = f"[`{label or d.name.removeprefix('LeanDLRA.')}`]({d.src})"
    return f"{code} <sup>[api]({d.api})</sup>" if d.api else code


def linkify_names(text: str, index: Index, module: str | None = None) -> str:
    """Link every resolvable Lean name in a free-text list (e.g. a ledger's Lean column)."""

    def repl(m: re.Match[str]) -> str:
        d = index.resolve(m.group(0), module)
        return decl_link(d, m.group(0).rstrip(".,;:")) if d else m.group(0)

    return TOKEN.sub(repl, text)


def linkify_markdown(text: str, index: Index) -> str:
    """Link Lean names inside code spans, repository paths and arXiv ids in Markdown text."""

    def span(m: re.Match[str]) -> str:
        content = m.group(1)
        if not PATH.search(content) and not any(
            index.resolve(t) for t in TOKEN.findall(content)
        ):
            return m.group(0)
        out, pos = [], 0
        for t in re.finditer(rf"{PATH.pattern}|{TOKEN.pattern}", content):
            out.append(content[pos : t.start()])
            tok = t.group(0)
            if PATH.fullmatch(tok):
                out.append(f"[`{tok}`]({REPO_URL}/blob/main/{tok})")
            elif d := index.resolve(tok):
                out.append(decl_link(d, tok))
            else:
                out.append(tok)
            pos = t.end()
        out.append(content[pos:])
        return "".join(out)

    # protect existing Markdown links (their text must not receive nested links)
    links: list[str] = []

    def hide(m: re.Match[str]) -> str:
        links.append(m.group(0))
        return f"\x00{len(links) - 1}\x00"

    text = MD_LINK.sub(hide, text)
    text = CODE_SPAN.sub(span, text)
    text = ARXIV.sub(
        lambda m: f"[{m.group(1)}](https://arxiv.org/abs/{m.group(1)})", text
    )
    return re.sub("\x00(\\d+)\x00", lambda m: links[int(m.group(1))], text)


def escape_pipes(text: str) -> str:
    """Stop kramdown from reading `|` in prose as table syntax (real table rows are kept)."""
    out = []
    fence = False
    for line in text.splitlines():
        if line.lstrip().startswith("```"):
            fence = not fence
        if fence or line.lstrip().startswith("|") or "|" not in line:
            out.append(line)
            continue
        line = line.replace("||", "‖")
        parts = re.split(r"(`[^`]*`)", line)
        line = "".join(
            p.replace("|", "∣")
            if p.startswith("`")
            else re.sub(r"(?<!\\)\|", r"\\|", p)
            for p in parts
        )
        out.append(line)
    return "\n".join(out)


def cell(text: str) -> str:
    """Make a value safe for a Markdown table cell."""
    return " ".join(str(text).split()).replace("|", "\\|")


def front(title: str, order: float, permalink: str, extra: str = "") -> str:
    """just-the-docs front matter."""
    return f"---\nlayout: default\ntitle: {title}\nnav_order: {order}\npermalink: {permalink}\n{extra}---\n\n"


def rewrite_repo_links(text: str, source: str) -> str:
    """Point repository-relative Markdown links at GitHub, mirrored docs at site pages."""
    mirrored = {
        "README.md": "./",
        "docs/PROVEN.md": "proven.html",
        "docs/NOVEL.md": "novel.html",
        "docs/CORRECTIONS.md": "corrections.html",
    }
    base = Path(source).parent

    def repl(m: re.Match[str]) -> str:
        target, anchor = m.group(1), m.group(2) or ""
        if target.startswith(SITE_URL):
            return f"]({target.removeprefix(SITE_URL) or './'}{anchor})"
        if re.match(r"^[a-z]+:", target) or target.startswith("/"):
            return m.group(0)
        resolved = re.sub(r"(^|/)\./", r"\1", (base / target).as_posix())
        if resolved in mirrored:
            return f"]({mirrored[resolved]}{anchor})"
        kind = (
            "tree"
            if resolved.endswith("/") or "." not in Path(resolved).name
            else "blob"
        )
        return f"]({REPO_URL}/{kind}/main/{resolved}{anchor})"

    return re.sub(r"\]\(([^)#\s]+)(#[^)\s]*)?\)", repl, text)


AREA_ORDER = [
    "Foundations",
    "Matrix",
    "Dynamics",
    "Integrators",
    "Stability",
    "Training",
]


def module_key(module: str) -> tuple[int, str]:
    """Order modules by library layer, then by name."""
    parts = module.split(".")
    layer = parts[1] if len(parts) > 1 else ""
    return (AREA_ORDER.index(layer) if layer in AREA_ORDER else len(AREA_ORDER), module)


def module_title(path: Path) -> str:
    """Title of a module from its module docstring."""
    m = re.search(r"/-!\s*\n#\s*(.+)", path.read_text(encoding="utf-8"))
    return m.group(1).strip() if m else ""


def page_library(index: Index) -> str:
    """All modules and all declarations, linked."""
    lines = [
        front("Library", 4, "/library.html"),
        "# Library",
        "",
        "Every module and every declaration of LeanDLRA. Theorem names link to the source line; *api*",
        "opens the generated documentation.",
        "",
        "| Module | Content | Theorems | Definitions |",
        "|---|---|---:|---:|",
    ]
    modules = sorted(index.by_module, key=module_key)
    for mod in modules:
        decls = index.by_module[mod]
        path = mod.replace(".", "/") + ".lean"
        title = module_title(ROOT / path) if (ROOT / path).exists() else ""
        n_thm = sum(d.kind == "theorem" for d in decls)
        lines.append(
            f"| [`{mod}`](#{slug(mod)}) | {cell(title)} | {n_thm} | {len(decls) - n_thm} |"
        )
    for mod in modules:
        decls = sorted(index.by_module[mod], key=lambda d: d.line)
        path = mod.replace(".", "/") + ".lean"
        lines += [
            "",
            f"## {mod}",
            "",
            (
                f"{module_title(ROOT / path) if (ROOT / path).exists() else ''} — "
                f"[source]({REPO_URL}/blob/main/{path})"
                + (
                    f" · [api](docs/{mod.replace('.', '/')}.html)"
                    if has_api(mod)
                    else ""
                )
            ),
            "",
            '<details markdown="1"><summary>'
            + f"{len(decls)} declarations"
            + "</summary>",
            "",
            "| Declaration | Kind | Description |",
            "|---|---|---|",
        ]
        lines += [f"| {decl_link(d)} | {d.kind} | {cell(d.doc)} |" for d in decls]
        lines += ["", "</details>"]
    return "\n".join(lines) + "\n"


def slug(text: str) -> str:
    """Header id exactly as kramdown generates it (also GitHub's for ASCII headers)."""
    text = text.replace("`", "")
    text = re.sub(r"^[^a-zA-Z]+", "", text)
    text = re.sub(r"[^a-zA-Z0-9 \-]", "", text)
    return text.replace(" ", "-").lower()


def module_imports(path: Path) -> list[str]:
    """LeanDLRA modules imported by a module."""
    return re.findall(
        r"^import (LeanDLRA\.[\w.]+)", path.read_text(encoding="utf-8"), re.MULTILINE
    )


PROVENANCE_HTML = """
<p>How every certified result is built: <b>papers</b> (orange) &rarr; <b>results</b> (stars; red =
beyond the literature) &larr; <b>Lean declarations</b> (coloured by module; squares are definitions)
&larr; the declarations their proofs use. Pick a result or an open problem on the left; increase the
depth to see further down the proof tree; switch to the module map for the import structure. Click a
node to open its source line, paper or entry. Hover for details.</p>
<p id="prov-stats"></p>
<div class="prov-toolbar">
  <button class="btn" data-mode="results">Result provenance</button>
  <button class="btn" data-mode="problems">Open problems</button>
  <button class="btn" data-mode="modules">Module map</button>
  <label>Depth <select id="prov-depth"><option>1</option><option selected>2</option>
  <option>3</option><option>4</option><option>6</option><option>10</option></select></label>
</div>
<p class="prov-legend"><span><i style="background:#f28e2b"></i>paper</span>
<span><i style="background:#4e79a7"></i>result</span><span><i style="background:#e15759"></i>new result</span>
<span><i style="background:#edc948"></i>open problem</span><span><i style="background:#59a14f"></i>Lean declaration</span></p>
<p id="prov-info" style="min-height:1.5em;font-size:0.85rem;color:#555"></p>
<div class="prov-layout">
  <div id="prov-side" class="prov-side"><input id="prov-search" placeholder="filter..." style="width:100%">
  <div id="prov-list"></div></div>
  <div id="cy"></div>
</div>
<script src="https://cdnjs.cloudflare.com/ajax/libs/cytoscape/3.30.2/cytoscape.min.js"></script>
<script src="assets/provenance.js?v=__PROV_HASH__"></script>
"""


ROADMAP_DECL = re.compile(
    r"/--\s*(?P<doc>.*?)-/\s*(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+(?P<name>[^\s(:{\[]+)",
    re.DOTALL,
)


def mirror(
    source: str, title: str, order: float, permalink: str, index: Index
) -> str | None:
    """A docs/*.md file as a site page, with links."""
    path = ROOT / source
    if not path.exists():
        return None
    body = rewrite_repo_links(path.read_text(encoding="utf-8"), source)
    return front(title, order, permalink) + linkify_markdown(escape_pipes(body), index)


def main() -> None:
    """Write all pages into website/."""
    SITE.mkdir(exist_ok=True)
    index = load_index()
    readme = rewrite_repo_links(
        (ROOT / "README.md").read_text(encoding="utf-8"), "README.md"
    )
    pages = {
        "index.md": front("Home", 1, "/") + linkify_markdown(readme, index),
        "proven.md": mirror("docs/PROVEN.md", "Proven", 2, "/proven.html", index),
        "novel.md": mirror("docs/NOVEL.md", "Novel", 3, "/novel.html", index),
        "corrections.md": mirror(
            "docs/CORRECTIONS.md", "Corrections", 4, "/corrections.html", index
        ),
        "library.md": page_library(index),
    }
    for name, content in pages.items():
        if content is not None:
            head, sep, body = content.partition("---\n\n")
            raw = head + sep + "{% raw %}\n" + body + "\n{% endraw %}\n"
            (SITE / name).write_text(raw, encoding="utf-8")
            print(f"wrote website/{name}")


if __name__ == "__main__":
    fire.Fire(main)
