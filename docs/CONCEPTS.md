# Concept map

Which definitions of the library mean the same thing, which imply which, and which are
different (with a separating example). Every row names the Lean lemma that proves it
(`wip/PLAN.md`, zeroth principle; `wip/UNIFY.md` §b). Sections are appended per unification batch.

## Pseudoinverses (UNIFY F6, batch C1, 2026-11-09)

Core file: `LeanDLRA/LinearAlgebra/Factorization/Defs.lean`. Relations are Lean lemmas there or in
the named file; "equal" means the local definition had the same body (and the same binders) as the
core one and was replaced by it, with a deprecated alias left under the old name.

| Concept | Core | Relation (lemma) |
|---|---|---|
| Penrose equations `A G A = A`, `G A G = G`, `(A G)ᵀ = A G`, `(G A)ᵀ = G A` | `Matrix.IsMoorePenrose A G` | defining; at most one solution (`Matrix.IsMoorePenrose.unique`) |
| Moore–Penrose inverse `A⁺` | `Matrix.pinv A` (explicit: `W diag(λ⁺) Wᵀ Aᵀ` from `Aᵀ A = W diag(λ) Wᵀ`) | satisfies the equations (`Matrix.isMoorePenrose_pinv`); `A.IsMoorePenrose G ↔ G = A.pinv` (`Matrix.isMoorePenrose_iff_eq_pinv`) |
| Gram pseudoinverse `(Aᵀ A)⁻¹ Aᵀ` | `Matrix.gramPinv A` | **implies** under full column rank: `Matrix.isMoorePenrose_gramPinv`, `Matrix.gramPinv_eq_pinv` (`IsUnit (Aᵀ * A).det`, equivalently `A.rank = Fintype.card k` by `Matrix.isUnit_det_transpose_mul_self_iff`); exactly: `Matrix.gramPinv_eq_pinv_iff` (`gramPinv A = pinv A ↔ IsUnit (Aᵀ * A).det ∨ A = 0`) |
| `pinvL` (`Literature/Integrators/P2001_08599a`) | `Matrix.gramPinv` | equal, replaced |
| `pinv` (`Literature/Integrators/P2001_08599b`) | `Matrix.gramPinv` | equal, replaced |
| `Novel.OpTR37.pinv` | `Matrix.gramPinv` | equal, replaced |
| `Novel.OpRS34.pinvT` | `Matrix.gramPinv` | equal, replaced |
| `gramPinv` (`Literature/Randomized/P2410_17091a`) | `Matrix.gramPinv` | equal, replaced |
| `IsMoorePenrose` (`Literature/Stochastic/P2607_27438a`, square matrices) | `Matrix.IsMoorePenrose` at `m = n` | equal (same four equations), replaced |
| Penrose conjunction of `svd_pinv_penrose` (`P2410_17091a`) and `isMoorePenrose_mul_mul` (`Literature/Training/P2505_08022a`) | `Matrix.isMoorePenrose_mul_mul_transpose`: `(U S Vᵀ)⁺ = V S⁻¹ Uᵀ` | `svd_pinv_penrose` restated with `Matrix.IsMoorePenrose` and proved by the core lemma; `isMoorePenrose_mul_mul` (not a C1 file) still states the conjunction |
| `{1}`-inverse hypotheses `X G X = X` (`RandomizedBUG.dgn_exact`) | `Matrix.IsMoorePenrose.mul_pinv_mul` | implied by `IsMoorePenrose` (first Penrose equation) |
| `IsChartData U V U⊥ V⊥ G` (`P2001_08599a`) vs `IsChartBasis` (`P2001_08599b`) | – | equivalent: `isChartData_iff` (`IsChartData ↔ IsChartBasis U U⊥ ∧ IsChartBasis V V⊥ ∧ IsUnit G.det`; `U U⁺ + U⊥ U⊥⁺ = 1` is the dimension count) |

**Failed bridge (finding).** `Matrix.gramPinv A = Matrix.pinv A` is false without full column rank:
for `A = diag(1, 0)`, `Aᵀ A` is singular, Mathlib's `⁻¹` gives `0`, so `gramPinv A = 0`, while
`pinv A = A ≠ 0` (the last `example` of `Factorization/Defs.lean`). Every use of the Gram formula in
the C1 files carries a full-column-rank hypothesis (`IsUnit (Uᵀ * U).det` or `IsUnit (Kᵀ * K)`), so
the two notions agree wherever results are stated; `Matrix.gramPinv` stays a separate core
definition because the papers write the Gram formula.

Not yet bridged (outside the C1 files): `svdPinv` (`Literature/Randomized/P2308_16547a`, expected
`IsMoorePenrose (U diag σ Vᵀ) (svdPinv …)`), `isMoorePenrose_mul_mul` (`P2505_08022a`, a copy of
`Matrix.isMoorePenrose_mul_mul_transpose`), the column projectors `A * A.gramPinv` (`colP`,
`Novel.OpTR37.colProj`, `projOmega`: batch C2).
