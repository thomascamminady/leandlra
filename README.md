# LeanDLRA

Dynamical low-rank approximation (DLRA) approximates the solution `A(t)` of a matrix
differential equation `Ȧ = F(t, A)` by matrices `Y(t)` of rank at most `r`. The approximation is
kept in factored form and advanced in time by an integrator that updates the factors. The same
idea is used for tensors in the Tucker, tensor train and tree tensor network formats.

LeanDLRA is a Lean 4 + Mathlib library of this theory. Its core contains the definitions
(matrices of rank at most `r`, the tangent projector, the DLRA problem, steps and runs of an
integrator) and theorems stated in these definitions: the best approximation of rank at most
`r`, and error bounds for the basis update and Galerkin (BUG) integrator, the projector-splitting
integrator, the parallel BUG integrator and the BUG integrator with explicit Euler substeps, with
versions for Tucker tensors and tree tensor networks. A second library, the catalogue, contains
results of single papers that are not yet stated in the core definitions.

Every statement of the core on `main` is proved; the build fails on `sorry`, and the audit of each
merge checks that only the standard axioms `propext`, `Classical.choice` and `Quot.sound` are used.

[![Lean Action CI](https://github.com/thomascamminady/leandlra/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/thomascamminady/leandlra/actions/workflows/lean_action_ci.yml)

## Contents

<!-- status:start -->

* Core library: 227 modules, 4845 theorems and lemmas, 63 papers cited by arXiv identifier.
* Catalogue: 362 modules, 13376 theorems and lemmas, 180 papers cited by arXiv identifier.

<!-- status:end -->

* [Getting started: the method in fifteen lines, the definitions to read first, a worked example](docs/GETTING_STARTED.md)
* [Main results of the core, by topic, with the Lean statements](docs/MAIN_RESULTS.md)
* [Index of the definitions of the core](docs/DEFINITIONS.md)
* [Concepts: how the definitions relate to each other](docs/CONCEPTS.md)
* [Core and catalogue: how the library is organized](docs/STRUCTURE.md)
* [All modules with their sources](docs/catalogue/PROVEN.md)
* [Website and API reference](https://camminady.dev/leandlra/)

Two more pages are about results of single papers. With few exceptions the declarations they name
belong to the catalogue and not to the core:

* [Novel results](docs/catalogue/NOVEL.md)
* [Corrections to published statements](docs/catalogue/CORRECTIONS.md)
* [Catalogue concept map: the local forms of the core notions in single papers](docs/catalogue/CATALOGUE.md)

## One theorem

The main theorem on the BUG integrator is `MatrixBUG.exists_run_norm_sub_le`
(`LeanDLRA/Integrators/Matrix/BUGRun.lean`). Let the field `F` be Lipschitz with constant `L`,
bounded by `B` and jointly continuous on the tube of radius `ρ` around the exact solution `A`
over `[t₀, t₀ + N * h]`. Let the normal component `(I - U Uᵀ) F(t, Y) (I - V Vᵀ)` have norm at
most `ε` at every point `Y = U S Vᵀ` of the tube, where `U` and `V` have `r` orthonormal columns,
with `ε ≥ 0`. Let `r` be at most the number of rows and of columns, let the start value have rank
at most `r` and distance at most `δ` from `A t₀`, and let `0 ≤ h ≤ H` and `N * h ≤ T`. If the
bound below plus `4 * B * h` is smaller than `ρ`, then a run of `N` BUG steps of size `h` exists,
all its values have rank at most `r`, and

    ‖Y n - A (t₀ + n * h)‖ ≤ e^{L T} δ + T e^{L T} (c₁ ε + c₂ h)    for all n ≤ N,

with `c₁ = bugC₁ L H` and `c₂ = bugC₂ L B H`. The constants depend only on `L`, `B` and `H`; no
singular value enters. The theorem is an instance of
`StepMethod.IsTubeLocal.exists_run_norm_sub_le` (`LeanDLRA/Integrators/Method.lean`), which
gives a run with a bound of the same form for every one-step method that is tube-local with a
margin constant `κ ≥ 2` (`StepMethod.IsTubeLocal`) and whose steps have a local error `h * c`.

## Using LeanDLRA in your project

LeanDLRA builds with the Lean toolchain in `lean-toolchain` (`leanprover/lean4:v4.36.0`) and
Mathlib `v4.36.0`. Use the same toolchain in your project and add to its `lakefile.toml`:

```toml
[[require]]
name = "LeanDLRA"
git = "https://github.com/thomascamminady/leandlra"
rev = "main"
```

Then fetch the dependencies and the Mathlib build cache, and import what you need:

```bash
lake update LeanDLRA
lake exe cache get
```

```lean
import LeanDLRA.Integrators.Matrix.BUGRun
```

This module contains the theorem named above. `import LeanDLRA` imports the core, the connected
theory. `import LeanDLRACatalogue` adds the catalogue, the results of single papers that are not
yet stated in the core definitions ([docs/STRUCTURE.md](docs/STRUCTURE.md)). Pin `rev` to a commit
or tag for a reproducible build.

## Contributing

Every file must build with `lake build --wfail`, contain no `sorry`, `admit`, `axiom` or
`native_decide`, and pass `make verify`. CI runs the same checks on every push. A core module
imports core modules only ([docs/STRUCTURE.md](docs/STRUCTURE.md)).

A new result is stated in the core definitions where that is possible; the steps are described
in [Getting started, section 6](docs/GETTING_STARTED.md#6-how-to-add-a-result). Names, notation,
hypotheses and file headers follow [docs/CONVENTIONS.md](docs/CONVENTIONS.md); its section 13 is
a checklist for a new file.

## Verifying

```bash
lake exe cache get
make verify
```

`make verify` builds the core and runs `scripts/audit.sh`, which rejects placeholders, custom axioms
and `native_decide`, and checks the axioms of every constant, private ones included. `make catalogue`
does the same for everything, core and catalogue, and checks the recorded statements.

| Workflow | Trigger | Checks |
|---|---|---|
| `lean_action_ci.yml` | every push | core: build with warnings as errors, import rule, audit, kernel replay of new commits |
| `catalogue.yml` | push to `main` | everything: build with warnings as errors, audit, recorded statements unchanged (`scripts/fidelity.py`), kernel replay of new commits |
| `kernel_replay.yml` | nightly | `leanchecker` replay of every module |
| `certify.yml` | manual | everything: clean build, audit, replay, external checkers (`lake check --paranoid`), signed `certificate.json` |

Verify a certificate with

```bash
gh attestation verify certificate.json --repo thomascamminady/leandlra
```

## License

Apache-2.0, see [LICENSE](LICENSE).
