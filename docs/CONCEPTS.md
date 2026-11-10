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

## Column-space and Galerkin projectors (UNIFY F5, batch C2, 2026-11-09)

Core file: `LeanDLRA/LinearAlgebra/Factorization/Defs.lean` (the projectors are built from the
pseudoinverses of C1; they move to `LinearAlgebra/Projection/Defs.lean` later, hash-neutral).

| Concept | Core | Relation (lemma) |
|---|---|---|
| Orthogonal projector onto the column space of `A` (any rank) | `Matrix.rangeProj A = A A⁺` | defining; characterized by `Matrix.eq_rangeProj_iff` (symmetric, fixes the columns of `A`, of the form `A C`); `Matrix.isOrthProjMat_rangeProj` |
| `U Uᵀ` for orthonormal `U` | `Matrix.rangeProj U` | equal: `Matrix.rangeProj_eq_mul_transpose` |
| `W Wᵀ` for any `W = A C` with `W Wᵀ A = A` (QR, SVD, Gram–Schmidt bases) | `Matrix.rangeProj A` | equal: `Matrix.rangeProj_eq_of_capture` (orthonormality of `W` is not needed); same column space gives the same projector: `Matrix.rangeProj_eq_rangeProj_of_mul` |
| Gram formula `A (Aᵀ A)⁻¹ Aᵀ` | `Matrix.colProj A = A * A.gramPinv` | **implies** under full column rank: `Matrix.colProj_eq_rangeProj`; exactly: `Matrix.colProj_eq_rangeProj_iff` (`IsUnit (Aᵀ * A).det ∨ A = 0`); `colProj (A C) = colProj A` for invertible `C` (`Matrix.colProj_mul_of_isUnit`) |
| Oblique projector with test matrix `S = A` | `obliqueProj A A` | equal to `Matrix.colProj A`: `LeanDLRA.obliqueProj_self` |
| `colP` (`Literature/Foundations/P2309_06125a`, `A (AᵀA)⁻¹ Aᵀ`) | `Matrix.colProj` | equal (`Matrix.colProj_def`), replaced |
| `Novel.OpTR37.colProj` (`K K⁺`) | `Matrix.colProj` | equal (same body), replaced |
| `Novel.BlindSpotII.colProj` (`orth K (orth K)ᵀ`) | `Matrix.rangeProj` | equal: `BlindSpotII.rangeProj_eq_orth_mul_transpose`, replaced |
| `colProj` (`Literature/Training/P2410_18720a`, Gram–Schmidt fold, now `gramSchmidtProj`) | `Matrix.rangeProj` | equal: `gramSchmidtProj_eq_rangeProj`; the invariant `IsColProj A univ Q` is `Q = rangeProj A` (`isColProj_univ_iff`); statements use the core projector |
| Galerkin projector `Z ↦ U Uᵀ Z V Vᵀ` | `LeanDLRA.galerkinProj U V = leftProj U * rightProj V` | defining (`galerkinProj_def`, `galerkinProj_apply`); orthogonal for orthonormal `U`, `V`: `isOrthProj_galerkinProj` |
| `galerkinProj` (`Research/SameMinibatchAugmentation`, `Novel/KineticAP`, `Literature/HighOrder/P2502_07040a`), `galProj` (`Literature/HighOrder/P2402_08607a`) | `LeanDLRA.galerkinProj` | equal (same body `leftProj U * rightProj V`), replaced; the local copies carried unused `DecidableEq` arguments or `Fin p` index types, which the core one drops |

**Failed bridge (finding).** `Matrix.colProj A = Matrix.rangeProj A` is false without full column
rank: for `A = diag(1, 0)`, Mathlib's `(Aᵀ A)⁻¹` is `0`, so `colProj A = 0`, while
`rangeProj A = A ≠ 0` (the last `example` of `Factorization/Defs.lean`). The two papers that write
the Gram formula (`P2309_06125a`, `OpTR37`) assume full column rank wherever they use it, so their
results are statements about `rangeProj` as well (`colProj_eq_rangeProj`).

**Different (not merged).** The mass-weighted Galerkin projector `galProj` of
`Literature/HighOrder/P2501_06145b` (`Ub Ubᵀ Mx Z My Vb Vbᵀ`) is orthogonal for the mass inner
product, not the Frobenius one; it equals `galerkinProj` only for `Mx = 1`, `My = 1` (weighted
norms: UNIFY F11, batch C13). Statements written with the unfolded `leftProj U * rightProj V`
(about 20 files, e.g. `P2412_09400a`, `P1804_04561a`, `P2505_08022a`) are `galerkinProj U V` by
`rfl` (`galerkinProj_def`) and can be restated in a later batch.

## SVD, truncation, tails and rank selection (UNIFY F8, batch C3, 2026-11-09)

Core file: `LeanDLRA/LinearAlgebra/Factorization/Defs.lean` (`Matrix.svdTrunc`, `tailSqSum` and
`IsBestLowRankApprox` move to `LinearAlgebra/{SVD,LowRank}/Defs.lean` with batch B5,
hash-neutral). `epsRank`, `distLR` (`Matrix/LowRankDistance.lean`) and `WeylSingular.tailNorm`
(`Classical/WeylSingular.lean`) are existing core definitions.

| Concept | Core | Relation (lemma) |
|---|---|---|
| SVD `A = U diag(σ) Vᵀ` with `p` triplets, `U`, `V` orthonormal, `σ` antitone, `σ ≥ 0` | `Matrix.IsSVD A U σ V` (fields `orthU orthV antitone nonneg eq`) | defining |
| Truncation to the first `r` triplets `U diag(σ₀…σ_{r-1},0…) Vᵀ` | `Matrix.svdTrunc U σ V r` | defining; leading-column form `U_{:r} Σ_r V_{:r}ᵀ` for `r ≤ p`: `Matrix.svdTrunc_eq_submatrix` |
| Discarded weight `∑_{i ≥ r} σᵢ²` | `tailSqSum σ r` | defining |
| Best rank-`r` approximation (Frobenius) | `IsBestLowRankApprox r A X` (minimizer form) | defining; the truncated SVD of an SVD is one: `P2209_13569.IsSVD.isBestLowRankApprox_svdTrunc` |
| `IsSVD` (`Literature/Training/P2209_13569a`; fields `left_orth right_orth antitone nonneg eq_mul`) | `Matrix.IsSVD` | equal, replaced (fields renamed) |
| `IsSVD` (`Literature/Kinetic/P2112_02695a`; fields `orthU orthW antitone nonneg eq`) | `Matrix.IsSVD` | equal, replaced (`orthW` → `orthV`) |
| `svdTrunc hr U σ V` (`P2209_13569a`), `truncSVD U σ W hr` (`P2112_02695a`) | `Matrix.svdTrunc U σ V r` | equal for `r ≤ p` (`Matrix.svdTrunc_eq_submatrix`), replaced; the core one needs no `r ≤ p`, so `IsSVD.sub_svdTrunc` and `IsSVD.norm_sub_truncSVD_sq` lost that hypothesis |
| `tailSq` (`P2112_02695a`, `Literature/Training/P2609_32615a`), `tailSum` (`Literature/Kinetic/P2303_01856a`) | `tailSqSum` | equal (same body), replaced |
| `svdTail σ s = √(∑ …)` (`Literature/Training/P2205_13571a`) | `√(tailSqSum σ s)` | equal: `svdTail_eq_sqrt_tailSqSum`; kept (it is the norm, not the square) |
| `tolRank A tol = min {r : τ_r(A) ≤ tol}` (`Literature/RankAdaptive/P2602_14854a`) | `epsRank tol A` | equal: `P2602_14854.epsRank_eq_sInf_tailNorm` (the tail is `distLR`, `tailNorm_eq_infDist`), replaced |
| `adaptiveRank S ϑ` (`Literature/RankAdaptive/P2104_05247a`, same definition) | `epsRank ϑ S` | equal (same argument), replaced |
| `tolRank ϑ X`, `svTail` (`Novel/BlindSpotII`) | `epsRank ϑ X`, `WeylSingular.tailNorm` | equal: `BlindSpotII.tolRank_eq_epsRank` (exists), `svTail` has the body of `tailNorm`; not yet replaced (follow-up) |

**Not bridged, with reason.** `IsPartitionedSVD` (`P2609_32615a`) does not sort the singular values
and splits them into two blocks with a gap `τⱼ < σᵢ`, so it is not an `IsSVD` of the concatenated
factors; `IsTruncRank s ϑ r₁` (`P2609_32615a`) is the minimality of `r₁` for the abstract weights `s`
and agrees with `epsRank` only when `s` are the singular values. `nuclearNorm` (`P2209_13569a`)
has no second user.

## QR and orthonormal frames (UNIFY F10, batch C4, 2026-11-09)

Core file: `LeanDLRA/LinearAlgebra/Factorization/Defs.lean`.

| Concept | Core | Relation (lemma) |
|---|---|---|
| Orthonormal frame capturing `X`: `Wᵀ W = 1`, `W Wᵀ X = X` | `Matrix.IsOrthCapture W X` | defining; `↔ Wᵀ W = 1 ∧ ∃ R, X = W R` (`Matrix.isOrthCapture_iff`) |
| Orthonormal basis of the column space: capture and `W = X C` | `Matrix.IsOrthBasisOf W X` | **implies** `IsOrthCapture` (`IsOrthBasisOf.isOrthCapture`); `W Wᵀ = rangeProj X` (`IsOrthBasisOf.mul_transpose_eq_rangeProj`) |
| Thin QR `K = Q R`, `Qᵀ Q = 1`, `R` upper triangular | `Matrix.IsQR K Q R` | **implies** `IsOrthCapture Q K` (`IsQR.isOrthCapture`); with invertible `R`, `IsOrthBasisOf Q K` (`IsQR.isOrthBasisOf`), hence `Q Qᵀ = rangeProj K` |
| `IsQR` (`Literature/Integrators/P2010_02022a`) | `Matrix.IsQR` | equal (same fields), replaced |
| `IsGSQR` (`Literature/Kinetic/P2502_03008b`, adds `0 ≤ R c c`) | `Matrix.IsQR` | **implies**: now `IsGSQR extends Matrix.IsQR` (`IsGSQR.toIsQR`) |
| `IsQR` (`Literature/Kinetic/P2502_03008a`: `Qᵀ Q = 1 ∧ ∃ R, Y = Q R`, rectangular `R`) | `Matrix.IsOrthCapture` | equal (`Matrix.isOrthCapture_iff`), replaced; same name as `Matrix.IsQR` but a different notion |
| `IsOrth` (`Literature/HighOrder/P2403_02834a`) | `Matrix.IsOrthBasisOf` | equal (same fields, `orthonormal` → `orth`), replaced |
| `IsOrthOf Q W` (`Literature/HighOrder/P2502_07040b`, `colSpan Q = W` for a subspace `W`) | `Matrix.IsOrthCapture` | **implies** for every `X` with `colSpan X ≤ W`: `IsOrthOf.isOrthCapture`; kept (its target is a subspace, not a matrix) |
| `IsBestRankApprox` (`P2502_07040b`) | `IsBestLowRankApprox` | equal (same body), replaced |
| `IsOrthonormalCols V` (`Literature/Stiff/P2503_04932a`, `∑ₙ V n a V n b = δ_{ab}`) | `Vᵀ * V = 1` | equal (`transpose_mul_self_eq_one_iff`), inlined (`docs/CONVENTIONS.md` §4) |
| `IsOrthBasisOf Û K` (`Research/SameMinibatchAugmentation`: `Ûᵀ Û = 1 ∧ ∃ C, Û = K C`, same column count) | `Matrix.IsOrthBasisOf` | equal: `StochasticDescent.isOrthBasisOf_iff` (the capture follows because `Ûᵀ K C = 1` makes `C` invertible); not yet replaced (76 uses in `Novel/MinibatchBias`, follow-up) |

**Separating example.** `Matrix.IsOrthCapture` does not imply `Matrix.IsOrthBasisOf`: `W = 1`
(2 × 2) captures `X = e₁` but its columns do not lie in the column space of `X`. The local `IsQR` of
`P2502_03008a` is a capture, not a QR factorization: it allows rectangular `R` and more columns than
`rank Y`.

## Vocabulary of `Analysis/Defs.lean` and Mathlib's orthogonal projection (UNIFY B3a, B3b, 2026-11-09)

Core files: `LeanDLRA/Analysis/Defs.lean` (ODE solutions, conditions on fields, tubes, Euler
steps), `LeanDLRA/LinearAlgebra/Projection/Defs.lean`. All definitions were moved with their names
and types unchanged (hash 0).

| Concept | Core | Relation (lemma) |
|---|---|---|
| Mathlib's orthogonal projection `K.starProjection` onto a subspace with an orthogonal projection | `LeanDLRA.IsOrthProj` | implies: `LeanDLRA.isOrthProj_starProjection` (the private copy of `Dynamics/ContinuousDLRA.lean` is removed) |
| `MeanSquare.isOrthProj_starProjection` (`Stochastic/MeanSquare.lean`) | `LeanDLRA.isOrthProj_starProjection` | same statement; duplicate, to be removed (F22, C13) |
| `Novel.KineticAP.isOrthProj_starProjection` (`[FiniteDimensional ℝ E]`, no instance argument) | `LeanDLRA.isOrthProj_starProjection` | special case (finite dimension gives `HasOrthogonalProjection`); duplicate, F22, C13 |
| Global Lipschitz field `IsLipschitzField F L` | `LeanDLRA.IsLipschitzOnTube F A a b ρ L` | implies: `IsLipschitzField.isLipschitzOnTube` (`Foundations/Localization.lean`) |
| Field given on a tube | `LeanDLRA.tubeExt` (radial retraction `ballRetract`) | global extension with the same constants: `isLipschitzField_tubeExt`, `isBoundedField_tubeExt`, agrees on the tube (`tubeExt_eq`) |
| Explicit Euler step of a frozen field, projected Euler step | `LeanDLRA.eulerStep F h x = x + h • F x`, `LeanDLRA.projEuler P F h t x = x + h • P (F t x)` | `projEuler P F h t = eulerStep (P ∘ F t) h` by definition (no lemma yet) |

## Tangent and normal projectors of the fixed-rank manifold (UNIFY F7, batch B4, 2026-11-10)

Core file: `LeanDLRA/FixedRank/Defs.lean` (moved, names and types unchanged). Lemmas in
`FixedRank/Defs.lean`, `Matrix/Curvature.lean` and `Matrix/Interpolation.lean`.

| Concept | Core | Relation (lemma) |
|---|---|---|
| Tangent projector from a left and a right projector, `L + R - L R`; normal projector `(1 - L)(1 - R)` | `LeanDLRA.tangent L R`, `LeanDLRA.normal L R` | defining; orthogonal for commuting orthogonal `L`, `R` (`IsOrthProj.tangent`, `Foundations/Projector.lean`) |
| Tangent projector at `Y = U S Vᵀ`, `Z ↦ U Uᵀ Z + Z V Vᵀ - U Uᵀ Z V Vᵀ` | `LeanDLRA.tangentProj U V = tangent (leftProj U) (rightProj V)` | `tangentProj_apply` |
| The same with projector matrices, `Pu B + B Pv - Pu B Pv` | `LeanDLRA.Curvature.tangentProjMat Pu Pv` | equal: `Curvature.tangentProjMat_eq_tangent` (`= tangent (leftMulCLM Pu) (rightMulCLM Pv)`), `tangentProjMat_eq_tangentProj` (`Pu = U Uᵀ`, `Pv = V Vᵀ`) |
| Left/right multiplication by an orthogonal projector matrix | `Frobenius.leftMulCLM P`, `Frobenius.rightMulCLM P` | implies `IsOrthProj`: `Curvature.IsOrthProjMat.isOrthProj_leftMulCLM`, `…_rightMulCLM`, and `IsOrthProjMat.isOrthProj_tangent` for the tangent projector |
| `ErrorOrder.isOrthProj_leftMulCLM`, `…_rightMulCLM` (`Research/IntegratorErrorOrder.lean`, hypotheses `M * M = M`, `Mᵀ = M`) | `Curvature.IsOrthProjMat.isOrthProj_leftMulCLM` | same statement unbundled; duplicate, F22/C13 |
| Oblique (interpolatory) tangent projector, sketched tangent projector | `LeanDLRA.obliqueTangentProj U SU V SV = tangent (leftOblique U SU) (rightOblique V SV)`, `LeanDLRA.sketchTangentProj` (instance with `SU = Θᵀ Θ P`, `SV = Ωᵀ Ω W`) | `obliqueTangentProj_apply` |
| Two-sided sketch `Z ↦ Θ Z Ωᵀ` (`sketchCLM`, `Matrix/Interpolation.lean`) | `Frobenius.sandwichCLM Θ Ωᵀ` | equal: `sketchCLM_eq_sandwichCLM` (`sketchCLM` itself: C13) |
| `Novel.OpTR37.tanProj P Q Z = Z - (1 - P) Z (1 - Q)`, `tangentAt` (`Lit/Training/P2410_18720a`), `tanProj` (`Lit/Foundations/P2309_06125a`) | `tangentProjAt Y` (planned, a7) | not bridged yet: `tangentProjAt` needs `Matrix.rangeProj` (C2, now in `Factorization/Defs.lean`) |

`filippov` (Filippov regularisation, `Analysis/Defs.lean`) moved in the same batch; its local
form `filippovGradR` (`Lit/Training/P2505_08022a`) is not bridged yet.
