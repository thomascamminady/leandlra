import LeanDLRA
import Batteries.Tactic.Lint
-- Scope: core

/-! The linters of Batteries and Mathlib (`@[env_linter]`) on the declarations of the core
library: `LeanDLRA.lean` imports the core only, and `#lint in LeanDLRA` takes the declarations of
the modules whose name starts with `LeanDLRA` that this environment holds. Run through
`scripts/lint_core.py`, which sends the file through `scripts/fc`. -/

#lint in LeanDLRA
