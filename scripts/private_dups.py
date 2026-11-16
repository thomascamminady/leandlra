#!/usr/bin/env -S uv run -q --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["fire"]
# ///
"""Warn about private names that are defined in two modules.

The rolling record and the dumps know a private declaration as ``_priv.<name>`` with the
enclosing namespaces but without the module (``scripts/DumpTypes.lean``); two private
declarations with the same qualified name in different modules therefore make a record entry
ambiguous. This scans the sources (comments removed, ``namespace``/``section``/``end`` tracked)
and lists such names. It is a source-level check: it does not see names that a macro or a
``variable``-dependent command creates, and it counts a name once per module.

    uv run -q scripts/private_dups.py [DIR]          warnings only, exit 0 (default DIR: LeanDLRA)
    uv run -q scripts/private_dups.py --strict       exit 1 if there is a duplicate
"""

import re
import sys
from collections import defaultdict
from pathlib import Path

_BLOCK_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)
_LINE_COMMENT = re.compile(r"--[^\n]*")
_NAMESPACE = re.compile(r"^\s*namespace\s+(\S+)")
_SECTION = re.compile(r"^\s*section\b(?:\s+(\S+))?")
_END = re.compile(r"^\s*end\b(?:\s+(\S+))?\s*$")
_KINDS = "def|theorem|lemma|abbrev|instance|structure|inductive|class|opaque|axiom|irreducible_def"
_PRIVATE = re.compile(
    rf"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:protected|noncomputable|unsafe|partial|nonrec)\s+)*"
    rf"private\s+(?:(?:protected|noncomputable|unsafe|partial|nonrec)\s+)*"
    rf"(?:{_KINDS})\s+(\S+)"
)


def strip_comments(text: str) -> str:
    """The text without block and line comments; line breaks inside a block stay."""

    def keep_lines(m: re.Match[str]) -> str:
        return "\n" * m.group(0).count("\n")

    return _LINE_COMMENT.sub("", _BLOCK_COMMENT.sub(keep_lines, text))


def private_names(text: str) -> list[str]:
    """The qualified user names of the private declarations of one source text."""
    stack: list[list[str]] = []  # per open scope: the namespace components it added
    found: list[str] = []
    for line in strip_comments(text).splitlines():
        if m := _NAMESPACE.match(line):
            stack.append(m.group(1).split("."))
        elif m := _SECTION.match(line):
            stack.append([])
        elif m := _END.match(line):
            if stack:
                stack.pop()
        elif m := _PRIVATE.match(line):
            name = m.group(1).strip("(){}[]:")
            if name.startswith("_root_."):
                found.append(name.removeprefix("_root_."))
            else:
                found.append(".".join([c for scope in stack for c in scope] + [name]))
    return found


def duplicates(root: Path) -> dict[str, list[str]]:
    """Qualified private name -> the modules (paths relative to ``root``) that define it twice."""
    where: dict[str, set[str]] = defaultdict(set)
    for path in sorted(root.rglob("*.lean")):
        for name in private_names(path.read_text(encoding="utf-8")):
            where[name].add(path.relative_to(root.parent).as_posix())
    return {n: sorted(m) for n, m in sorted(where.items()) if len(m) > 1}


def main(directory: str = "LeanDLRA", strict: bool = False) -> int:
    """Print one warning per private name that two modules define; exit 1 only with ``strict``."""
    dups = duplicates(Path(directory))
    for name, modules in dups.items():
        print(
            f"AUDIT WARN: private name {name} is defined in {len(modules)} modules: "
            + ", ".join(modules)
        )
    if not dups:
        print("private names: no name is defined in two modules")
    return 1 if dups and strict else 0


if __name__ == "__main__":
    import fire  # only for the command line; tests import this module without it

    sys.exit(fire.Fire(main))
