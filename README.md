# LeanDLRA

A Lean 4 + Mathlib formalization of dynamical low-rank approximation (DLRA): tangent-space projectors,
error bounds for projector splitting (KSL), basis-update & Galerkin (BUG), rank-adaptive, parallel,
Tucker and tree tensor network integrators, stability and conservation, kinetic equations, and
low-rank training of neural networks.

The library contains no `sorry`. Every constant depends only on `propext`, `Classical.choice` and
`Quot.sound`.

[![Lean Action CI](https://github.com/thomascamminady/leandlra/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/thomascamminady/leandlra/actions/workflows/lean_action_ci.yml)

## Contents

<!-- status:start -->

410 modules, 14457 theorems and lemmas, 178 cited papers.

<!-- status:end -->

* [What is proven and where it comes from](docs/PROVEN.md)
* [Novel results](docs/NOVEL.md)
* [Corrections to published statements](docs/CORRECTIONS.md)
* [Website and API reference](https://camminady.dev/leandlra/)

## Using LeanDLRA in your project

LeanDLRA builds with the Lean toolchain in `lean-toolchain` (`leanprover/lean4:v4.36.0-rc2`) and
Mathlib `v4.36.0-rc2`. Use the same toolchain in your project and add to its `lakefile.toml`:

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
import LeanDLRA.Integrators.BUG
```

`import LeanDLRA` imports the whole library. Pin `rev` to a commit or tag for a reproducible build.

## Contributing

Every file must build with `lake build --wfail`, contain no `sorry`, `admit`, `axiom` or
`native_decide`, and pass `make verify`. CI runs the same checks on every push.

## Verifying

```bash
lake exe cache get
make verify
```

`make verify` builds the library and runs `scripts/audit.sh`, which rejects placeholders, custom axioms
and `native_decide`, and checks the axioms of every constant, private ones included.

| Workflow | Trigger | Checks |
|---|---|---|
| `lean_action_ci.yml` | every push | build with warnings as errors, audit, recorded statements unchanged (`scripts/fidelity.py`), kernel replay of new commits |
| `kernel_replay.yml` | nightly | `leanchecker` replay of every module |
| `certify.yml` | manual | clean build, audit, replay, external checkers (`lake check --paranoid`), signed `certificate.json` |

Verify a certificate with

```bash
gh attestation verify certificate.json --repo thomascamminady/leandlra
```

## License

Apache-2.0, see [LICENSE](LICENSE).
