# /// script
# requires-python = ">=3.11"
# dependencies = ["fire"]
# ///
# Scope: core
"""The environment linters (Batteries' ``#lint``, with the ``@[env_linter]`` checks of Mathlib that
the core imports) on the core library, summarized by linter.

The core is ``LeanDLRA.lean`` (``scripts/core.py``); ``scripts/LintCore.lean`` imports it and runs
``#lint in LeanDLRA``, so exactly the core declarations are linted (the catalogue is not in the
environment). ``lake exe runLinter`` is not used: it is not built, and it would lint the default
targets of the workspace, the catalogue included. One Lean process, started through ``scripts/fc``
(memory test, lock).

    uv run -q scripts/lint_core.py run [--min-free=45] [--out=FILE]    # lint, then summarize
    uv run -q scripts/lint_core.py summarize FILE                      # summarize a saved output

Findings of one linter are listed by module with their counts. Nothing is fixed or written into
the library; the full text goes to ``--out`` (default ``.lake/check/lint_core.out``).
Exit: 0 the lint ran (findings or not; read the counts), 3/4/5 as ``scripts/fc``, 2 no output.
"""

from __future__ import annotations

import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HEADER = re.compile(r"^/- The `([^`]+)` linter reports:")
TOTAL = re.compile(
    r"-- Found (\d+) errors? in (\d+) declarations \(plus (\d+) automatically"
)
FILE = re.compile(r"^-- ([A-Za-z_][\w.']*)\s*$")
ENTRY = re.compile(r"^#check\s")


def summarize(text: str) -> str:
    """Counts of findings per linter, per linter the counts per file, and the totals line."""
    per_linter: Counter[str] = Counter()
    per_file: dict[str, Counter[str]] = defaultdict(Counter)
    linter, file, total = "", "?", ""
    for line in text.splitlines():
        if m := HEADER.match(line):
            linter, file = m.group(1), "?"
        elif m := TOTAL.search(line):
            total = line[line.index("-- Found") :]
        elif m := FILE.match(line):
            file = m.group(1)
        elif linter and ENTRY.match(line):
            per_linter[linter] += 1
            per_file[linter][file] += 1
    out = [total or "-- no totals line in the output"]
    if "All linting checks passed" in text and not per_linter:
        out.append("no finding")
    for name, n in per_linter.most_common():
        out.append(f"{name}: {n}")
        for f, k in per_file[name].most_common(8):
            out.append(f"    {k:5d}  {f}")
        if len(per_file[name]) > 8:
            out.append(f"    ... {len(per_file[name]) - 8} more files")
    return "\n".join(out)


def run(min_free: int = 45, out: str = ".lake/check/lint_core.out") -> int:
    """Lint the core through ``scripts/fc``; write the text to ``out`` and print the summary."""
    target = ROOT / out
    target.parent.mkdir(parents=True, exist_ok=True)
    res = subprocess.run(
        [
            str(ROOT / "scripts" / "fc"),
            f"--min-free={min_free}",
            "scripts/LintCore.lean",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    target.write_text(res.stdout + res.stderr)
    if res.returncode in (3, 4, 5, 6) or res.returncode == 2:
        print(
            res.stdout.strip().splitlines()[-1]
            if res.stdout.strip()
            else "fc: no output"
        )
        return res.returncode
    print(summarize(res.stdout))
    print(f"full text: {out}")
    return 0


if __name__ == "__main__":
    import fire  # only the command line needs it

    fire.Fire(
        {"run": run, "summarize": lambda f: print(summarize(Path(f).read_text()))}
    )
    sys.exit(0)
