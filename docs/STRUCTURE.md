# Core and catalogue

All Lean sources are below `LeanDLRA/`. They form two Lake libraries.

| | Core | Catalogue |
|---|---|---|
| Library | `LeanDLRA` | `LeanDLRACatalogue` (the core and everything else) |
| Root file | `LeanDLRA.lean` | `LeanDLRACatalogue.lean` |
| Build | `lake build` | `lake build LeanDLRACatalogue` |
| Content | one connected theory | results of single papers that are not stated in the core definitions |

**Core.** The folders `Foundations`, `LinearAlgebra`, `Analysis`, `Matrix`, `FixedRank`, `DLRA`,
`Integrators`, `Tensor`, `Dynamics`, `Stability`, `Stiff`, `HighOrder`, `Randomized`, `Stochastic`,
`Control`, `Training`, `Classical` and `Research`, and the modules listed in
[`promoted.txt`](promoted.txt). Every core theorem is stated in the shared definitions of the core
(`docs/CONCEPTS.md`), so core results can be combined with each other. Statements about what the
library provides refer to the core.

**Catalogue.** The other modules of the folders `Literature`, `OpenProblems`, `Novel` and
`Corrections`. Each is a proven result, checked like the core (no `sorry`, standard axioms only), but
stated in definitions of its own file or of the paper it comes from. A catalogue theorem therefore
does not automatically apply to the objects of the core.

**Rule.** A core module imports core modules only. `scripts/core.py check` tests this; the gate and
CI run it.

**Promotion.** A catalogue module becomes a core module once its definitions are the core definitions
or are proven equal to them. Add its name to `docs/promoted.txt` (every module it imports must be in
the core) and run `scripts/gen_root.sh`, which writes both root files. The file itself does not move.

## Imports

```lean
import LeanDLRA                              -- the core
import LeanDLRACatalogue                     -- the core and the catalogue
import LeanDLRA.Literature.Lit2010_05249a    -- one module, core or catalogue
```

## Checks

| Command | What it does |
|---|---|
| `make build` | writes the root files, checks the import rule, builds the core |
| `make verify` | `make build` and the axiom audit of the core (`scripts/audit.sh`) |
| `make catalogue` | builds everything with warnings as errors, audits the axioms of every constant, checks the recorded statements (`scripts/fidelity.py`) |

The gate (`scripts/gate.py`), through which every change of a Lean file reaches `main`, builds the
changed files and the core and audits both. It does not build the catalogue. A change of a core file
can therefore leave a catalogue module that no longer compiles; this cannot make a false statement
pass, because a module that does not compile proves nothing. The `Catalogue` workflow reports such
modules, and they are repaired or removed.

| Workflow | Trigger | Scope | Must be green |
|---|---|---|---|
| `lean_action_ci.yml` | every push | core: build with warnings as errors, import rule, audit, kernel replay of changed core modules | on every commit |
| `catalogue.yml` | push to `main` | everything: build with warnings as errors, audit, recorded statements unchanged, kernel replay of changed modules | before a release |
| `kernel_replay.yml` | nightly | `leanchecker` replay of every module | before a release |
| `certify.yml` | manual | everything: clean build, audit, replay, external checkers, signed `certificate.json` | for a release |

The API reference on the website covers both the core and the catalogue.
