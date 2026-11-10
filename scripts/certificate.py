# /// script
# requires-python = ">=3.11"
# dependencies = ["fire"]
# ///
"""Write `certificate.json`: what `.github/workflows/certify.yml` verified, tied to the exact sources.

The certificate is a claim, not a proof. It lets anyone rerun the checks on the same commit and compare
the file hashes, and the workflow signs it with a GitHub build attestation.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import time
from pathlib import Path
from typing import Any

import fire

ROOT = Path(__file__).resolve().parent.parent


def git(*args: str) -> str:
    """Output of a git command."""
    return subprocess.run(
        ["git", *args], cwd=ROOT, capture_output=True, text=True, check=True
    ).stdout.strip()


def digest(path: Path) -> str:
    """SHA-256 of a file."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main(checks: str, out: str = "certificate.json") -> None:
    """Write the certificate; `checks` is a comma-separated list of the checks that passed."""
    files = [
        ROOT / p
        for p in git(
            "ls-files", "LeanDLRA", "LeanDLRA.lean", "LeanDLRACatalogue.lean"
        ).split("\n")
    ]
    # The two root files are not modules of their own; the core is what `LeanDLRA.lean` imports.
    root = (ROOT / "LeanDLRA.lean").read_text(encoding="utf-8")
    core = len(re.findall(r"^import LeanDLRA\.", root, re.MULTILINE))
    manifest: dict[str, Any] = json.loads(
        (ROOT / "lake-manifest.json").read_text(encoding="utf-8")
    )
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    theorems = sum(
        len(
            re.findall(
                r"^(?:private |protected )*(?:theorem|lemma)\s",
                p.read_text(encoding="utf-8"),
                re.MULTILINE,
            )
        )
        for p in files
    )
    certificate = {
        "repository": os.environ.get("GITHUB_REPOSITORY", ""),
        "commit": git("rev-parse", "HEAD"),
        "tree": git("rev-parse", "HEAD^{tree}"),
        "toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "mathlib": mathlib["rev"],
        "date_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "run": f"{os.environ.get('GITHUB_SERVER_URL', '')}/{os.environ.get('GITHUB_REPOSITORY', '')}"
        f"/actions/runs/{os.environ.get('GITHUB_RUN_ID', '')}",
        "checks_passed": [c.strip() for c in checks.split(",") if c.strip()],
        "modules": len(files) - 2,
        "core_modules": core,
        "theorems_and_lemmas": theorems,
        "axioms_allowed": ["propext", "Classical.choice", "Quot.sound"],
        "sources_sha256": {str(p.relative_to(ROOT)): digest(p) for p in files},
    }
    (ROOT / out).write_text(json.dumps(certificate, indent=1) + "\n", encoding="utf-8")
    print(
        f"{out}: {len(files) - 2} modules ({core} in the core), {theorems} theorems, "
        f"commit {certificate['commit']}"
    )


if __name__ == "__main__":
    fire.Fire(main)
