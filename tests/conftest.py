"""Make the scripts in ``scripts/`` importable as modules in the tests."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
