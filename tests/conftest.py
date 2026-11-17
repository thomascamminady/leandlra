# Scope: both
"""Make the scripts in ``scripts/`` and ``scripts/catalogue/`` importable as modules in the tests."""

import sys
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent.parent / "scripts"
sys.path.insert(0, str(SCRIPTS / "catalogue"))
sys.path.insert(0, str(SCRIPTS))
