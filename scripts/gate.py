# /// script
# requires-python = ">=3.11"
# dependencies = ["fire"]
# ///
"""The only path from a proof attempt to `main`.

Agents drop finished slices into ``wip/ready/``.  This loop takes a few at a time and, for each batch:

1. scans for forbidden tokens and builds the slices from cold oleans with ``lake build --wfail``, so
   any warning fails; the Lean kernel checks every declaration during this build;
2. runs the whole-library audit (``scripts/audit.sh``): standard axioms only, for every constant;
3. commits and pushes.

A slice failing 1 moves to ``wip/rejected/`` with a log and never reaches git.  A failure in 2-3
restores nothing and stops the loop, because it means something is wrong with the batch as a whole.
Nothing is pushed unless every step passed.  CI then rebuilds everything and replays the changed
modules through the kernel independently (``scripts/replay.sh``).
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import time
from pathlib import Path
from typing import TypedDict

import fire

ROOT = Path(__file__).resolve().parent.parent
WIP = ROOT / "wip"
READY, REJECTED, DONE = WIP / "ready", WIP / "rejected", WIP / "done"
LOG = WIP / "gate.log"
TRAILER = "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
FORBIDDEN = re.compile(
    r"\bsorry\b|\bsorryAx\b|\badmit\b|^\s*(@\[[^]]*\]\s*)?"
    r"((private|protected|noncomputable|scoped|local)\s+)*axiom\b|native_decide|implemented_by"
    r"|\bextern\b|\bunsafe\b|debug\.skipKernelTC|\bdecide\s*:=\s*true",
    re.MULTILINE,
)


class Slice(TypedDict):
    """One entry of `wip/manifest.json`."""

    source: str
    target: str
    stubs: list[str]
    ops: list[str]
    chars: int


def log(message: str) -> None:
    """Append a timestamped line to the gate log."""
    with LOG.open("a", encoding="utf-8") as handle:
        handle.write(f"{time.strftime('%H:%M:%S')} {message}\n")


def run(*cmd: str, timeout: int = 14400) -> tuple[int, str]:
    """Run a command in the repository and return exit code and combined output."""
    # At most five Lean workers: each needs over a gigabyte, and the 16 GB machine must not swap.
    env = {**os.environ, "LEAN_NUM_THREADS": os.environ.get("GATE_LEAN_THREADS", "5")}
    proc = subprocess.run(
        cmd,
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=timeout,
        check=False,
        env=env,
    )
    return proc.returncode, proc.stdout + proc.stderr


def manifest() -> dict[str, Slice]:
    """Slice table: `wip/manifest.json`."""
    return json.loads((WIP / "manifest.json").read_text(encoding="utf-8"))


def reject(path: Path, reason: str) -> None:
    """Move a slice to `wip/rejected/` with the reason next to it."""
    REJECTED.mkdir(exist_ok=True)
    (REJECTED / f"{path.stem}.log").write_text(reason, encoding="utf-8")
    shutil.move(str(path), str(REJECTED / path.name))
    log(
        f"REJECT {path.stem}: {reason.strip().splitlines()[0][:160] if reason.strip() else ''}"
    )


def remove_target(target: Path) -> None:
    """Take a slice back out of the library tree.

    A module that is already on main (an audit fix of a landed file) is restored from ``HEAD``
    instead of deleted, so a rejected fix never removes a proven module.
    """
    if run("git", "cat-file", "-e", f"HEAD:{target.relative_to(ROOT)}")[0] == 0:
        run("git", "checkout", "-q", "HEAD", "--", str(target))
        return
    run("git", "rm", "-q", "--cached", "--ignore-unmatch", str(target))
    target.unlink(missing_ok=True)


def process(batch: list[Path]) -> bool:
    """Run one batch through the gate; return False if the loop must stop."""
    table = manifest()
    accepted: list[Path] = []
    targets: dict[str, Path] = {}
    for path in batch:
        entry = table.get(path.stem)
        if entry is None:
            reject(path, "not a slice of the manifest\n")
            continue
        target = ROOT / entry["target"]
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(path, target)
        targets[path.stem] = target
        accepted.append(path)
    modules = {
        p.stem: str(targets[p.stem].relative_to(ROOT).with_suffix("")).replace("/", ".")
        for p in accepted
    }

    # 1. Forbidden tokens, then a cold build with its real imports in which any warning is a failure.
    for path in list(accepted):
        if FORBIDDEN.search(path.read_text(encoding="utf-8")):
            remove_target(targets[path.stem])
            reject(path, "forbidden token in the source\n")
            accepted.remove(path)
    if not accepted:
        return True
    code, out = run("lake", "build", "--wfail", *[modules[p.stem] for p in accepted])
    if code != 0:
        for path in list(accepted):
            mod = re.escape(modules[path.stem])
            if re.search(rf"(✖|⚠) \[\d+/\d+\] \w+ {mod}\b", out):
                remove_target(targets[path.stem])
                detail = "\n".join(
                    line
                    for line in out.splitlines()
                    if "error" in line or "warning" in line
                )
                reject(path, f"lake build --wfail failed\n{detail[:6000]}\n")
                accepted.remove(path)
    if not accepted:
        return True

    for path in accepted:
        run("git", "add", str(targets[path.stem]))
    run("scripts/gen_root.sh")
    code, out = run("lake", "build", "LeanDLRA")
    if code != 0:
        log(f"STOP: whole-library build failed\n{out[-3000:]}")
        for path in accepted:
            remove_target(targets[path.stem])
            reject(path, f"whole-library build failed\n{out[-3000:]}\n")
        run("scripts/gen_root.sh")
        return True

    # 2. Whole-library audit.
    code, out = run("scripts/audit.sh")
    if code != 0:
        log(f"STOP: audit failed\n{out[-3000:]}")
        return False

    # 3. Commit and push.
    ops = sorted({op for p in accepted for op in table[p.stem]["ops"]})
    names = ", ".join(p.stem for p in accepted)
    updated = [
        p
        for p in accepted
        if run("git", "cat-file", "-e", f"HEAD:{targets[p.stem].relative_to(ROOT)}")[0]
        == 0
    ]
    verb = "Update" if len(updated) == len(accepted) else "Add"
    title = (
        f"{verb} {len(accepted)} {'slices' if len(accepted) > 1 else 'slice'} ({names})"
    )
    message = f"{title}\n\n{' '.join(ops)}\n\n{TRAILER}\n"
    run(
        "git",
        "add",
        "LeanDLRA.lean",
        *[str(targets[p.stem]) for p in accepted],
    )
    code, out = run("git", "commit", "-q", "-m", message)
    if code != 0:
        log(f"STOP: commit failed {out[-800:]}")
        return False
    code, out = run(
        "git", "push", "-q", "git@github.com:thomascamminady/leandlra.git", "HEAD:main"
    )
    if code != 0:
        log(f"STOP: push failed {out[-800:]}")
        return False
    DONE.mkdir(exist_ok=True)
    for path in accepted:
        shutil.move(str(path), str(DONE / path.name))
    log(f"PUSHED {title}")
    return True


def main(batch: int = 4, once: bool = False) -> None:
    """Process `wip/ready/` forever (or one round with `--once`)."""
    READY.mkdir(parents=True, exist_ok=True)
    log("gate started")
    while True:
        files = sorted(READY.glob("*.lean"), key=lambda p: p.stat().st_mtime)[:batch]
        if files:
            if not process(files):
                log("gate stopped, see above")
                return
        elif once:
            return
        else:
            time.sleep(15)


if __name__ == "__main__":
    fire.Fire(main)
