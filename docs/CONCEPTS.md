# Concept map

Which definitions of the library mean the same thing, which imply which, and which are
different (with a separating example). Every row names the Lean lemma that proves it. The first
sections cover the vocabulary of linear algebra and analysis, the later ones the integrators.

## Pseudoinverses

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
| Penrose conjunction of `svd_pinv_penrose` (`P2410_17091a`) and `isMoorePenrose_mul_mul` (`Literature/Training/P2505_08022a`) | `Matrix.isMoorePenrose_mul_mul_transpose`: `(U S Vᵀ)⁺ = V S⁻¹ Uᵀ` | `svd_pinv_penrose` restated with `Matrix.IsMoorePenrose` and proved by the core lemma; `isMoorePenrose_mul_mul` replaced by the core lemma (deprecated alias) |
| `{1}`-inverse hypotheses `X G X = X` (`RandomizedBUG.dgn_exact`) | `Matrix.IsMoorePenrose.mul_pinv_mul` | implied by `IsMoorePenrose` (first Penrose equation) |
| `IsChartData U V U⊥ V⊥ G` (`P2001_08599a`) vs `IsChartBasis` (`P2001_08599b`) | – | equivalent: `isChartData_iff` (`IsChartData ↔ IsChartBasis U U⊥ ∧ IsChartBasis V V⊥ ∧ IsUnit G.det`; `U U⁺ + U⊥ U⊥⁺ = 1` is the dimension count) |

**Failed bridge (finding).** `Matrix.gramPinv A = Matrix.pinv A` is false without full column rank:
for `A = diag(1, 0)`, `Aᵀ A` is singular, Mathlib's `⁻¹` gives `0`, so `gramPinv A = 0`, while
`pinv A = A ≠ 0` (the last `example` of `Factorization/Defs.lean`). Every use of the Gram formula in
the files of this section carries a full-column-rank hypothesis (`IsUnit (Uᵀ * U).det` or `IsUnit (Kᵀ * K)`), so
the two notions agree wherever results are stated; `Matrix.gramPinv` stays a separate core
definition because the papers write the Gram formula.

Also proved: `diag(σ⁻¹)` is the Moore–Penrose inverse of `diag(σ)` for every `σ`
(`Matrix.isMoorePenrose_diagonal`, stated in `Literature/Randomized/P2308_16547a` for now, to move to
`Factorization/Defs.lean`), and `svdPinv U σ V = V diag(σ⁻¹) Uᵀ` (`P2308_16547a`) is the Moore–Penrose
inverse of `U diag(σ) Vᵀ` for orthonormal `U`, `V` and **every** `σ`, zero entries included:
`P2308_16547.isMoorePenrose_svdPinv`, `svdPinv_eq_pinv` (implies; `svdPinv` is kept because it takes
the SVD factors). The column projectors `A * A.gramPinv` are in the next section.

## Column-space and Galerkin projectors

Core file: `LeanDLRA/LinearAlgebra/Factorization/Defs.lean` (the projectors are built from the
pseudoinverses of the previous section; they move to `LinearAlgebra/Projection/Defs.lean` later, with unchanged statements).

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
product, not the Frobenius one; it equals `galerkinProj` only for `Mx = 1`, `My = 1` (see the
section "Weighted norms"). Statements written with the unfolded `leftProj U * rightProj V`
(about 20 files, e.g. `P2412_09400a`, `P1804_04561a`, `P2505_08022a`) are `galerkinProj U V` by
`rfl` (`galerkinProj_def`) and can be restated later.

## SVD, truncation, tails and rank selection

Core file: `LeanDLRA/LinearAlgebra/Factorization/Defs.lean` (`Matrix.svdTrunc`, `tailSqSum` and
`IsBestLowRankApprox` are to move to `LinearAlgebra/SVD/Defs.lean` and
`LinearAlgebra/LowRank/Defs.lean` with unchanged statements). `epsRank`, `distLR`
(`Matrix/LowRankDistance.lean`) and `WeylSingular.tailNorm` (`Classical/WeylSingular.lean`) are
existing core definitions.

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
| `tolRank ϑ X`, `svTail` (`Novel/BlindSpotII`) | `epsRank ϑ X`, `WeylSingular.tailNorm` | equal (`WeylSingular.epsRank_eq_sInf_tailNorm`; `svTail` had the body of `tailNorm`), replaced in `Novel/BlindSpotII` and `Novel/GeoLoRAFreeze` (deprecated aliases, 2026-11-10) |

**Not bridged, with reason.** `IsPartitionedSVD` (`P2609_32615a`) does not sort the singular values
and splits them into two blocks with a gap `τⱼ < σᵢ`, so it is not an `IsSVD` of the concatenated
factors; `IsTruncRank s ϑ r₁` (`P2609_32615a`) is the minimality of `r₁` for the abstract weights `s`
and agrees with `epsRank` only when `s` are the singular values. `nuclearNorm` (`P2209_13569a`)
has no second user.

## QR and orthonormal frames

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
| `IsOrthBasisOf Û K` (`Research/SameMinibatchAugmentation`: `Ûᵀ Û = 1 ∧ ∃ C, Û = K C`, same column count) | `Matrix.IsOrthBasisOf` | equal: `StochasticDescent.isOrthBasisOf_iff` (the capture follows because `Ûᵀ K C = 1` makes `C` invertible); replaced in `Research/SameMinibatchAugmentation` and `Novel/MinibatchBias` (no alias, see the file); `Û Ûᵀ = U' U'ᵀ` for `K = U' D` is `Matrix.IsOrthBasisOf.mul_transpose_eq_mul_transpose` (stated in the research file, to move to `Factorization/Defs.lean`) |
| `IsQRRoutine qr` (`Literature/Training/P2509_15113a`: `∀ K, Qᵀ Q = 1 ∧ Q R = K`, `R` not triangular) | `Matrix.IsOrthCapture`, `Matrix.IsQR` | equal to `∀ K, IsOrthCapture (qr K).1 K ∧ (qr K).2 = (qr K).1ᵀ K` (`P2509_15113.isQRRoutine_iff`); **implied** by `∀ K, IsQR K (qr K).1 (qr K).2` (`isQRRoutine_of_isQR`); does not imply it (separating `example`: `K ↦ (J, Jᵀ K)` with the swap `J`, `R = Jᵀ` at `K = 1` is not upper triangular). Kept (it is a routine, not a predicate on one matrix) |
| `IsCoreQR i C Q S` (`Literature/Training/P2305_19059a`: `Qᵀ Q = 1`, `Matᵢ(C)ᵀ = Q Sᵀ`, `S` invertible) | `Matrix.IsOrthBasisOf` | equal to `IsOrthBasisOf Q (Matᵢ C)ᵀ ∧ S = Matᵢ(C) Q` (`P2305_19059.isCoreQR_iff`; invertibility of `S` is automatic since `Q` is square in the column count); `IsCoreQR.isOrthBasisOf`. Kept (it carries `S`) |

**Separating example.** `Matrix.IsOrthCapture` does not imply `Matrix.IsOrthBasisOf`: `W = 1`
(2 × 2) captures `X = e₁` but its columns do not lie in the column space of `X`. The local `IsQR` of
`P2502_03008a` is a capture, not a QR factorization: it allows rectangular `R` and more columns than
`rank Y`.

## Vocabulary of `Analysis/Defs.lean` and Mathlib's orthogonal projection

Core files: `LeanDLRA/Analysis/Defs.lean` (ODE solutions, conditions on fields, tubes, Euler
steps), `LeanDLRA/LinearAlgebra/Projection/Defs.lean`. All definitions were moved with their names
and types unchanged (hash 0).

| Concept | Core | Relation (lemma) |
|---|---|---|
| Mathlib's orthogonal projection `K.starProjection` onto a subspace with an orthogonal projection | `LeanDLRA.IsOrthProj` | implies: `LeanDLRA.isOrthProj_starProjection` (the private copy of `Dynamics/ContinuousDLRA.lean` is removed) |
| `MeanSquare.isOrthProj_starProjection` (`Stochastic/MeanSquare.lean`) | `LeanDLRA.isOrthProj_starProjection` | same statement; duplicate, to be removed |
| `Novel.KineticAP.isOrthProj_starProjection` (`[FiniteDimensional ℝ E]`, no instance argument) | `LeanDLRA.isOrthProj_starProjection` | special case (finite dimension gives `HasOrthogonalProjection`); duplicate, to be removed |
| Global Lipschitz field `IsLipschitzField F L` | `LeanDLRA.IsLipschitzOnTube F A a b ρ L` | implies: `IsLipschitzField.isLipschitzOnTube` (`Foundations/Localization.lean`) |
| Field given on a tube | `LeanDLRA.tubeExt` (radial retraction `ballRetract`) | global extension with the same constants if `0 ≤ ρ` and `0 ≤ L` (resp. `0 ≤ B`): `isLipschitzField_tubeExt`, `isBoundedField_tubeExt`; agrees on the tube (`tubeExt_eq`); see the section "Tubes, the problem on a tube and the tube theorem" |
| Explicit Euler step of a frozen field, projected Euler step | `LeanDLRA.eulerStep F h x = x + h • F x`, `LeanDLRA.projEuler P F h t x = x + h • P (F t x)` | `projEuler P F h t = eulerStep (P ∘ F t) h` by definition (no lemma yet) |

## Tangent and normal projectors of the fixed-rank manifold

Core files: `LeanDLRA/FixedRank/Defs.lean` (projectors from factors or projector matrices),
`LeanDLRA/FixedRank/TangentSpace/Defs.lean` (projector and space at a point),
`LeanDLRA/FixedRank/TangentSpace.lean` (interface). Further lemmas in `Matrix/Curvature.lean`,
`Matrix/Projectors.lean` and `Matrix/Interpolation.lean`.

### Which definition to use

| Situation | Use | Why |
|---|---|---|
| A statement about a point `Y` of the matrix space, no factors in sight (a field projected at `Y`, a retraction, a Riemannian gradient, a curve on the manifold) | `tangentProjAt Y`, `tangentSpaceAt Y` | defined for every `Y`, without a rank hypothesis and without a choice of factors; `tangentProjAt Y` is the orthogonal projector onto `tangentSpaceAt Y` |
| The factors `U`, `V` with orthonormal columns are the data (integrator steps, K-, L- and S-steps, substep analysis) | `tangentProj U V` | no pseudo-inverse; computes with `U Uᵀ`, `V Vᵀ` |
| Two projector matrices `Pu`, `Pv` are the data (curvature bounds, perturbation of the projector) | `Curvature.tangentProjMat Pu Pv` | a function of the two projectors, so differences `Pu - Pu'` can be estimated |
| Two commuting projectors on an arbitrary inner product space (function spaces, tensors, a proof that only uses `L + R - L R`) | `tangent L R`, `normal L R` | the algebra of the tangent and normal projector without matrices |
| An oblique (interpolatory, sketched) projector | `obliqueTangentProj U SU V SV`, `sketchTangentProj` | not orthogonal; none of the lemmas of `tangentProjAt` applies |

At a point `Y = U S Vᵀ` with orthonormal `U`, `V` and invertible `S` the first three coincide:
`tangentProjAt (U * S * Vᵀ) = tangentProj U V` (`tangentProjAt_eq_tangentProj`) and
`tangentProjAt Y Z = Curvature.tangentProjMat Y.rangeProj Yᵀ.rangeProj Z`
(`tangentProjAt_apply_eq_tangentProjMat`). If `S` is singular, the rank of `Y` is smaller than the
number of columns of `U`, the space `tangentSpaceAt Y` is smaller than the range of
`tangentProj U V` (`tangentSpaceAt_mul_mul_transpose_le`), and the two projectors differ.
A point of the fixed-rank manifold is a point of `fixedRankSet m n r`
(`LinearAlgebra/LowRank/SepRank.lean`); no lemma of the interface needs this hypothesis.

### Table

| Concept | Core | Relation (lemma) |
|---|---|---|
| Tangent projector from a left and a right projector, `L + R - L R`; normal projector `(1 - L)(1 - R)` | `LeanDLRA.tangent L R`, `LeanDLRA.normal L R` | defining; orthogonal for commuting orthogonal `L`, `R` (`IsOrthProj.tangent`, `Foundations/Projector.lean`) |
| Tangent projector for factors `U`, `V`, `Z ↦ U Uᵀ Z + Z V Vᵀ - U Uᵀ Z V Vᵀ` | `LeanDLRA.tangentProj U V = tangent (leftProj U) (rightProj V)` | `tangentProj_apply`; fixed points and range: `tangentProj_eq_self_iff`, `mem_range_tangentProj` (`Matrix/Projectors.lean`) |
| The same with projector matrices, `Pu B + B Pv - Pu B Pv` | `LeanDLRA.Curvature.tangentProjMat Pu Pv` | equal: `Curvature.tangentProjMat_eq_tangent` (`= tangent (leftMulCLM Pu) (rightMulCLM Pv)`), `tangentProjMat_eq_tangentProj` (`Pu = U Uᵀ`, `Pv = V Vᵀ`) |
| Tangent projector at a point `Y`, `Z ↦ P Z + Z Q - P Z Q` with `P = rangeProj Y`, `Q = rangeProj Yᵀ` | `LeanDLRA.tangentProjAt Y = tangent (leftMulCLM Y.rangeProj) (rightMulCLM Yᵀ.rangeProj)` | `tangentProjAt_apply`; orthogonal projector (`isOrthProj_tangentProjAt`); equal to `tangentProjMat` at the range projectors (`tangentProjAt_apply_eq_tangentProjMat`) and to `tangentProj U V` at `Y = U S Vᵀ` with invertible `S` (`tangentProjAt_eq_tangentProj`); `tangentProjAt Y Y = Y` (`tangentProjAt_self`) |
| Tangent space at a point `Y`, `{A Y + Y B}` | `LeanDLRA.tangentSpaceAt Y` (a submodule) | `mem_tangentSpaceAt`; it is the range and the fixed-point set of `tangentProjAt Y` (`range_tangentProjAt`, `tangentProjAt_eq_self_iff`), and `tangentProjAt Y = (tangentSpaceAt Y).starProjection` (`tangentProjAt_eq_starProjection`); with factors it is `{U B + C Vᵀ}` (`mem_tangentSpaceAt_mul_mul_transpose`, `S` invertible) and in general contained in the range of `tangentProj U V` (`tangentSpaceAt_mul_mul_transpose_le`) |
| Normal projector at a point `Y`, `Z ↦ (1 - P) Z (1 - Q)` | `1 - tangentProjAt Y` | `one_sub_tangentProjAt_apply`, `isOrthProj_one_sub_tangentProjAt` |
| Left/right multiplication by an orthogonal projector matrix | `Frobenius.leftMulCLM P`, `Frobenius.rightMulCLM P` | implies `IsOrthProj`: `Curvature.IsOrthProjMat.isOrthProj_leftMulCLM`, `…_rightMulCLM`, and `IsOrthProjMat.isOrthProj_tangent` for the tangent projector |
| Oblique (interpolatory) tangent projector, sketched tangent projector | `LeanDLRA.obliqueTangentProj U SU V SV = tangent (leftOblique U SU) (rightOblique V SV)`, `LeanDLRA.sketchTangentProj` (instance with `SU = Θᵀ Θ P`, `SV = Ωᵀ Ω W`) | `obliqueTangentProj_apply` |
| Two-sided sketch `Z ↦ Θ Z Ωᵀ` (`sketchCLM`, `Matrix/Interpolation.lean`) | `Frobenius.sandwichCLM Θ Ωᵀ` | equal: `sketchCLM_eq_sandwichCLM` |

### Local forms of the catalogue

| Local form | Core | Relation |
|---|---|---|
| `tangentAt Y` (`Literature/Training/P2410_18720a`) | `tangentProjAt Y` | replaced (same term); deprecated alias in the paper file |
| `tanProj Y = (tangentSpace Y).starProjection` (`Literature/Foundations/P2309_06125a`, used in `Novel/OpHO38`) | `tangentProjAt Y` | replaced; equal by `tangentProjAt_eq_starProjection`; deprecated alias in the paper file |
| `tangentSpace Y` (`P2309_06125a`), `tangentSpaceAt X` (`Literature/Training/P2306_00897a`) | `tangentSpaceAt Y` | replaced (same text); deprecated alias for `tangentSpace` in the paper file |
| `rankSet m n r` (`P2309_06125a`) | `fixedRankSet m n r` | replaced (same body; the unused instance argument `[Fintype m]` disappears); deprecated alias in the paper file |
| `riemGrad G X = (tangentSpaceAt X).starProjection (G X)` (`P2306_00897a`) | `tangentProjAt X (G X)` | equal: `P2306_00897.riemGrad_eq_tangentProjAt`; kept (the file states its results with `riemGrad`) |
| `Novel.OpTR37.tanProj P Q Z = Z - (1 - P) Z (1 - Q)` | `Curvature.tangentProjMat P Q Z` | equal (`OpTR37.tanProj_eq_tangentProjMat`); kept, the proofs of the file compute with its form; at `P = Y.rangeProj`, `Q = Yᵀ.rangeProj` it is `tangentProjAt Y Z` by `tangentProjAt_apply_eq_tangentProjMat` |
| `MLFEM.IsTangent U V X := ∃ B C, X = U * B + C * Vᵀ` (`Literature/HighOrder/P2501_06145a`) | `tangentSpaceAt (U * S * Vᵀ)` | the right-hand side of `mem_tangentSpaceAt_mul_mul_transpose`; not bridged (the file works with weighted inner products and with factors that are not orthonormal in the Frobenius sense) |
| `doTangent U Yh`, `doTangentSubmodule U Yh` (`Literature/Stochastic/P2407_01404a`): `{V Yhᵀ + U Zᵀ, Yhᵀ Z = 0}` | none | tangent space of the dynamically orthogonal factorization with the gauge `Yhᵀ Z = 0`: a parametrization, contained in `{C Yhᵀ + U B}`; not bridged |
| `IsTangentRep`, `dTanProj` (`P2309_06125a`) | none | a gauged representation of a tangent vector and the derivative of the projector along a curve; not tangent projectors |
| `tangentProjection U V F` (`Literature/Integrators/P2001_08599a`), with `Matrix.gramPinv` | `Curvature.tangentProjMat U.colProj V.colProj F` (expected) | the same expression after expanding; not proved, not bridged (oblique chart file) |

### Tangent objects of other manifolds (not replaced; named for orientation)

| Object | Manifold | Relation to the matrix objects |
|---|---|---|
| `tangentSpace U C`, `tangentProj U C`, `stiefelTangent U` (`Literature/Training/P2305_19059a`) | Tucker tensors | `tangentProj U C = (tangentSpace U C).starProjection`, the pattern of `tangentProjAt_eq_starProjection`; for two modes it is expected to be the matrix case; not bridged to the core tensor projector |
| `Tensor.tuckerTangentProj`, `modeTangentProj`, `Tensor.ttTangentSum`, `Tensor.ttTangentProj` (tensor core) | Tucker, tensor train | built from mode or interface projectors like `tangent L R`; see the section "Tensor step vocabulary" |
| `tangentPi U Z`, `tangentPiCLM`, `tangentSpace U Z` (`Literature/Foundations/P2008_07427a`) | symplectic low-rank factorization | projector with the weight `(Zᵀ Z)⁻¹` and a horizontal gauge; not an instance of `tangent L R` |
| `tangentP τ X V = tangent (projV τ V) (projX τ X)`, `tangentVec`, `IsTangent` (`Literature/Kinetic/P1801_01103a`) | low-rank functions `∑ Xᵢ Sᵢⱼ Vⱼ` in `L²` | `tangentP` is the core `tangent` of the function-space projectors by definition |
| `tangent`, `tangentSpace` (`Literature/Kinetic/P2101_12571a`); `tangentSet`, `tangentV`, `tangentZ`, `tangentZV` (`Literature/Kinetic/P2503_10562a`) | conservative low-rank kinetic ansatz | sets of tangent vectors with fixed (conserved) basis functions and a gauge; no projector of the core corresponds |

`filippov` (Filippov regularisation, `Analysis/Defs.lean`): its local form `filippovGradR S`
(`Literature/Training/P2505_08022a`) is `filippov gradR Set.univ S`
(`P2505_08022.filippovGradR_eq_filippov`); the local name is kept.

## Low-rank and SVD vocabulary, normal-component bounds

Core files: `LeanDLRA/LinearAlgebra/LowRank/Defs.lean` (`lowRankSet`, `distLR`, `epsRank`,
`colSpan`, `ofCols`, `WeylSingular.tailNorm`), `LeanDLRA/LinearAlgebra/SVD/Defs.lean`
(`LinearMap.rightSingularBasis`, `rightSingularVectors`, `leftSingularVectors`,
`EckartYoung.rightSingularVectors`, `topRightSingularVectors`, `truncation`),
`LeanDLRA/LinearAlgebra/Factorization/Defs.lean` (`KyFan.podBasis`),
`LeanDLRA/Integrators/Matrix/Defs.lean` (`MatrixBUG.FactoredNormalBound`, `NearNormalBound`). All
moved with names and types unchanged.

| Concept | Core | Relation (lemma) |
|---|---|---|
| Singular-value tail `τ_r(A) = (∑_{l ≥ r} σ_l²)^{1/2}` | `WeylSingular.tailNorm A r` | equal to the distance to the rank-`≤ r` matrices, `distLR r A` by definition of `distLR`: `WeylSingular.tailNorm_eq_infDist` (Eckart–Young) |
| Tolerance rank of the singular values `min {r : τ_r(X) ≤ ε}` | `epsRank ε X` (distance form) | equal: `WeylSingular.epsRank_eq_sInf_tailNorm`; the copy `P2602_14854.epsRank_eq_sInf_tailNorm` (`Lit/RankAdaptive/P2602_14854a`) is a duplicate |
| Global factored normal-component bound | `MatrixBUG.FactoredNormalBound F r ε` | implies the localized one: `nearNormalBound_of_factored`; satisfied with `ε = 0` by the identity field (`example`, `Integrators/Matrix/Defs.lean`) |
| Localized bound near `Y` on `[t₀, t₁]` | `NearNormalBound F r ε t₀ t₁ Y ρ` | defining; equivalent to the region form `FactoredNormalBoundOn` on `Icc t₀ t₁ ×ˢ Metric.closedBall Y ρ`: `nearNormalBound_iff` (section "Normal-component bounds on regions") |

## Runge–Kutta tableaux and the `φ`-functions

Core file: `LeanDLRA/Analysis/Defs.lean`: `ButcherTableau R s` (arrays `a`, `b`, `c` over any coefficient
ring `R`), `ButcherTableau.IsExplicit`, `ButcherTableau.IsRowSum`, the tableaux `euler`, `rk4`,
`ssprk104` (generic in `R`, so the same tableau serves the order conditions over `ℚ` and the steps over
`ℝ`), and `LeanDLRA.phi1`, `LeanDLRA.phi2` (`φ₁(z) = (eᶻ - 1)/z`, `φ₂(z) = (eᶻ - 1 - z)/z²`, with
their limits at `0`). The core step structures of `HighOrder/RungeKuttaBUG.lean` keep their raw
arguments `a b c`; a tableau `T` enters as `T.a T.b T.c`.

| Concept | Core | Relation (lemma) |
|---|---|---|
| `rk4A`, `rk4B`, `rk4C` (`Literature/Randomized/P2512_15703a`) | `ButcherTableau.rk4` over `ℝ` | equal (same arrays), replaced (deprecated definitions); `apRK4_eq_rk4` now takes `rk4.a rk4.b rk4.c` and uses `rk4_isExplicit` |
| `rk4a`, `rk4b` (`Literature/Randomized/P2409_06384a`, `ℕ`-indexed) | `ButcherTableau.rk4` | equal on the indices `< 4` (`P2409_06384.rk4a_eq`, `rk4b_eq`); kept, since the extension by `0` to `ℕ` is the convention of that file's stage maps |
| `ssprk104A`, `ssprk104b`, `ssprk104c` (`OpenProblems/HighOrder/Part3Defs`, over `ℚ`) | `ButcherTableau.ssprk104` over `ℚ` | equal (`ssprk104A_eq`, `ssprk104b_eq`, `ssprk104c_eq`, all `rfl`); kept under their names because catalogue statements use them |
| `ExplicitRK s` (`Literature/HighOrder/P2502_07040b`) | `ButcherTableau ℝ s` with `IsExplicit` | equivalent: `ExplicitRK.equivButcherTableau : ExplicitRK s ≃ {T // T.IsExplicit}`, `ExplicitRK.isExplicit_toButcherTableau`; kept (it bundles explicitness) |
| `rkStage`, `rkResult` (`Literature/HighOrder/P2502_07040a`) | `RungeKuttaBUG.IsGalerkinRKStep F a b c (fun _ => 1) 1` | for explicit tableaux they form that step (`isGalerkinRKStep_rkStage`) and are its only solution (`eq_rkStage_of_isGalerkinRKStep`, from `galerkinRK_eq_rk`) |
| `rkConst` (`Literature/HighOrder/P2608_17157a`: `M_p/p! (1/(p+1) + ∑ |bᵢ| cᵢ^p) + L C_st ∑ |bᵢ|`) | `RungeKuttaBUG.rkConst` (Lipschitz stage constant) | **different** constants with the same name: the paper one is renamed `klRKConst` (deprecated alias `rkConst`) |
| `phi1` (`Literature/Stiff/P2312_00172a`) | `LeanDLRA.phi1` | equal, replaced (deprecated alias) |
| `phi1`, `phi2` (`OpenProblems/Stiff/Part3Defs`) | `LeanDLRA.phi1`, `LeanDLRA.phi2` | equal (`phi1_eq`, `phi2_eq`, `rfl`); kept (a catalogue statement uses `phi1`) |

## Weighted norms

Core file: `LeanDLRA/LinearAlgebra/Frobenius/Defs.lean`. `WeightedMatrix wx wv` is `Matrix m n ℝ` as a
type synonym carrying the weighted inner product `Frobenius.weightedInner wx wv`
(`WeightedMatrix.inner_def`); for positive weights (instances `Fact (∀ i, 0 < wx i)`,
`Fact (∀ j, 0 < wv j)`) it is a real inner product space, so every abstract inner-product theorem
applies to discrete weighted `L²` norms (`WeightedMatrix.norm_sq_eq`: `‖X‖² = ∑ wxᵢ wvⱼ Xᵢⱼ²`).
`WeightedMatrix.toFrobenius : WeightedMatrix wx wv ≃ₗᵢ[ℝ] Matrix m n ℝ`, `X ↦ diag(√wx) X diag(√wv)`,
is the isometry to the Frobenius space (`inner_toFrobenius`, `norm_toFrobenius`; built from
`Frobenius.weightedInner_eq_inner`). Conversions: `toWeighted`, `ofWeighted` (identities).

| Concept | Core | Relation (lemma) |
|---|---|---|
| `gridFrobSq Δx Y = Δx ∑ Yᵢⱼ²` (`Literature/Kinetic/P2607_27736a`) | `WeightedMatrix (fun _ => Δx) (fun _ => 1)` | equal to the squared weighted norm for `Δx > 0` (`gridFrobSq_eq_norm_sq_weighted`) and to `Δx ‖Y‖²` (`gridFrobSq_eq`, exists) |
| `frob2 A = ∑ Aᵢⱼ²` (`Literature/Kinetic/P2502_20883a`) | Frobenius norm | equal to `‖A‖²` (`frob2_eq_norm_sq`) |

Not bridged yet: the vector and function weighted products `ipx`, `ipv` (`P2101_12571a/b`), `ipw`
(`P2602_12337a`), `wInner` (`P2311_09425a`), `l2Sq` (`P2212_12012a`, `P1902_00424a`) belong to the
kinetic framework; `frob2` of `P2503_04932a` is on three-way arrays (`Tensor/Defs`).

## Duplicate lemmas and remaining frames

| Concept | Core | Relation (lemma) |
|---|---|---|
| `Novel.OpTR37.tanProj P Q Z = Z - (1 - P) Z (1 - Q)` | `Curvature.tangentProjMat P Q Z` | equal (`tanProj_eq_tangentProjMat`); kept, see the section on tangent projectors |
| `tangentP τ X V` (`Literature/Kinetic/P1801_01103a`) | `LeanDLRA.tangent` | is `tangent` of the function-space projectors by definition (no change) |
| `stiff_derivative_mem_tangent` (`P1803_10473a`, `A Y + Y Aᵀ`), `stiff_derivative_mem_tangent'` (`P2010_05249a`, `A_x Y + Y A_y`) | `LeanDLRA.mul_add_mul_mem_range_tangentProj` (new, `FixedRank/TangentSpace.lean`) | both are now one-line instances of the core lemma (statements unchanged) |
| `isOrthProj_leftMul`, `isOrthProj_rightMul` (`P2001_08599a`), `ErrorOrder.isOrthProj_leftMulCLM`, `isOrthProj_rightMulCLM` (`Research/IntegratorErrorOrder`) | `Curvature.IsOrthProjMat.isOrthProj_leftMulCLM`, `isOrthProj_rightMulCLM` | one-line instances (statements unchanged) |
| `norm_transpose_mul_le`, `norm_mul_le_of_orthonormal` (`P2101_07104a`), `norm_transpose_mul_le`, `norm_mul_orthonormal_le` (`P2107_07282a`), `norm_mul_le_of_orthonormal` (`P2008_07427a`) | `LeanDLRA.norm_transpose_mul_le`, `LeanDLRA.norm_mul_le_of_orthonormal` (`Matrix/Projectors.lean`) | one-line instances (statements unchanged) |
| `riccatiField` (root namespace, from `OpenProblems/Curated/StiffAndStochasticDefs`) and the former `KalmanBucy.riccatiField` | `LeanDLRA.riccatiField` | one definition: the copy in `namespace LeanDLRA.KalmanBucy` and the bridge between the two are removed; the root name stays because a recorded statement (`riccati_equilibrium_attracts`) uses it |
| `IsXQR Measure.count K X' S'` (`Literature/Kinetic/P2311_09425b`, finite grid) | `Matrix.IsOrthCapture` | equal to `X̃ᵀ X̃ = 1 ∧ K̃ = X̃ S'` for the grid matrices (`isXQR_count_iff`), hence a capture (`IsXQR.isOrthCapture_count`); for a general measure it is the same statement in `L²(ν)` (different carrier). `IsVQR` (in `Lp`) is not bridged: the core has no abstract orthonormal-frame notion yet |

## Tensor, training and filtering vocabulary

Core files: `LeanDLRA/Tensor/Defs.lean` (extended: `modePrefix`, `tuckerSqrtC₁`, `tuckerSqrtC₂`,
`TTNFrame` with `height`, `size`, `ttnErrBound`, `IsAugRecoverable`, `IsTTNAugRecoverable`),
`LeanDLRA/Training/Defs.lean` (`projGradStep`, `geoLoRADir`, `IsGeoLoRABases`, `geoLoRAStep`,
`fedClientIter`, `fedRound`, `fedDrift`, `fedAvgClientIter`, `fedAvgRound`,
`FactorizedDynamics.loraPrecond`, `InexactGradient.ArmijoTest`,
`InexactGradient.IsDiscreteGradient`), `LeanDLRA/Filtering/Defs.lean` (`LeanDLRA.riccatiField`,
`rotatingMode`, `diagProj`, `innovCov`, `kalmanGain`, `analysisCov`, `josephCov`,
`OpenProblems.Stiff.ensCentering`, `enkfField`). All moved with names and types unchanged. The
step predicates of the tensor integrators are the subject of the next section.

| Concept | Core | Relation (lemma) |
|---|---|---|
| Ordered prefix product `P 0 ⋯ P (k-1)` of mode operators | `modePrefix P k` | equal to `modeProd P` for `d ≤ k`: `modePrefix_of_le` (`Classical/CommutingProjectorTelescoping.lean`) |
| `√d` constants of the Tucker BUG local error | `tuckerSqrtC₁`, `tuckerSqrtC₂` | at most `tuckerC₁`, `tuckerC₂`: `tuckerSqrtC₁_le`, `tuckerSqrtC₂_le` |
| Projected gradient step `x - h Π ∇ℒ(x)` | `projGradStep` | the GeoLoRA step is one: `geoLoRAStep_eq`; the FeDLRT round is one plus drift: `fedRound_eq` |
| Factor-wise (LoRA) preconditioner | `FactorizedDynamics.loraPrecond` | quadratic form: `inner_loraPrecond`, `inner_loraPrecond_self_nonneg` |
| Kalman–Bucy covariance field `A P + P Aᵀ - ρ P² + Qn` | `LeanDLRA.riccatiField` | the only definition; in `namespace LeanDLRA.KalmanBucy` the bare name resolves to it |
| One Kalman analysis step | `innovCov`, `kalmanGain`, `analysisCov`, `josephCov` | Joseph identity `josephCov_sub_analysisCov`, `analysisCov_mono` (`Stochastic/KalmanBucy.lean`) |

## Tensor step vocabulary

Core files: `LeanDLRA/Tensor/Defs.lean` (`TreeShape`, `TTNFrame`, `modePrefix`,
`Tensor.ttTangentSum`, `IsTTNAugRecoverable`), `LeanDLRA/Tensor/Steps.lean` (`kslModeField`,
`IsTuckerKSLStep`, `IsExactKSteps`, `IsTTNKSLStep`, `IsTTNBUGStep`, `IsAugTTNBUGStep`,
`IsParTTNBUGStep`, `IsTTNRecoverable`, `modeTangentProj`), the folder
`LeanDLRA/Tensor/TTN/Abstract/` (the theorems about the step predicates, on a real inner product
space), `LeanDLRA/Tensor/Tucker/Tangent.lean` and `LeanDLRA/Tensor/TT/TangentProjector.lean`.
`Tensor/Steps.lean` is not a `Defs.lean`: the step predicates use `modeProd`, `modeProdLeOne`,
`parTuckerBUG` (`Integrators/TuckerBUG.lean`) and `Exactness.IsRecoverable`
(`Integrators/Exactness.lean`), which are declared next to theorems.

| Concept | Core | Relation (lemma) |
|---|---|---|
| Shape of a dimension tree without mode labels | `TreeShape` (`Tensor/Defs.lean`) | image of a dimension tree: `DimTree.toTreeShape` (`Tensor/TTN/Integrators.lean`; `toTreeShape_leaf`, `toTreeShape_node`) |
| Field of the `K`-substep of mode `i`, `x ↦ Q₀ i (P₁ 0 ⋯ P₁ (i-1)) F(t, x)` | `kslModeField` | defined through `modePrefix` |
| One step of the nested Tucker projector-splitting integrator with given `K`-values | `IsTuckerKSLStep` | holds at a valid inner node of a dimension tree: `DimTree.IsValid.isTuckerKSLStep` (`Tensor/TTN/Integrators.lean`); local error with inexact `K`-values: `tucker_ksl_local_error_inexact` (`Tensor/TTN/Abstract/ProjectorSplitting.lean`) |
| The `K`-values are the exact substep values | `IsExactKSteps` | hypothesis of the exactness theorem `tucker_ksl_exact` (`Tensor/TTN/Abstract/ProjectorSplittingExactness.lean`); the step on tensors is in `Tensor/TTN/ProjectorSplittingExactness.lean` |
| One step of the recursive projector-splitting integrator for tree tensor networks over a `TreeShape` | `IsTTNKSLStep` | every step on tensors is one: `DimTree.IsProjectorSplittingStep.isTTNKSLStep` (`Tensor/TTN/ProjectorSplitting.lean`); error bounds `ttn_ksl_local_error`, `ttn_ksl_global_error` (`Tensor/TTN/Abstract/ProjectorSplitting.lean`), on tensors `DimTree.projectorSplitting_global_error` |
| Frame of a tree tensor network step | `TTNFrame E` (`Tensor/Defs.lean`) | frame of a basis family on a dimension tree: `DimTree.BasisFrame.toTTNFrame`, with `toTTNFrame_size`, `toTTNFrame_height` (`Tensor/TTN/ParallelBUG.lean`) |
| One step of the parallel BUG integrator for tree tensor networks over a frame | `IsParTTNBUGStep` | every step on tensors is one: `DimTree.BasisFrame.IsParBUGStep.isParTTNBUGStep` (`Tensor/TTN/ParallelBUG.lean`); error bounds `parTTN_local_error_le_size`, `parTTN_global_error_le` (`Tensor/TTN/Abstract/ParallelBUG.lean`), on tensors `DimTree.BasisFrame.parBUG_global_error` |
| One step of the fixed-rank and of the rank-adaptive BUG integrator for tree tensor networks over a frame | `IsTTNBUGStep`, `IsAugTTNBUGStep` | every step on tensors is one: `DimTree.BasisFrame.IsBUGStep.isTTNBUGStep` (`Tensor/TTN/BUG.lean`), `DimTree.BasisFrame.IsAugBUGStep.isAugTTNBUGStep` (`Tensor/TTN/RankAdaptiveBUG.lean`); error bounds `ttn_local_error`, `ttn_global_error_le` (`Tensor/TTN/Abstract/BUG.lean`), `augTTN_local_error_le_size`, `augTTN_global_error_le` (`Tensor/TTN/Abstract/RankAdaptiveBUG.lean`), on tensors `DimTree.BasisFrame.bug_global_error`, `DimTree.BasisFrame.augBUG_global_error`; the truncation of the rank-adaptive step on tensors is a clause of the step, no truncation of a tree tensor network is proved to satisfy it |
| Recursive recoverability along a frame | `IsTTNRecoverable` (`Tensor/Steps.lean`), `IsTTNAugRecoverable` (`Tensor/Defs.lean`) | recursion of `Exactness.IsRecoverable` over the frame; hypotheses of the exactness theorems `ttn_exact` and `augTTN_exact`; no instance on `Tensor ι` |
| Tangent projector of the Tucker manifold from abstract mode projectors, `∏ᵢ P₀ i + ∑ᵢ (1 - P₀ i) Q₀ i` | `modeTangentProj` (`Tensor/Steps.lean`) | orthogonal projector for commuting mode projectors and compatible co-range projectors: `modeTangentProj_isOrthProj` (`Tensor/Tucker/Tangent.lean`); the projector on tensors with trivial core projector is one: `Tensor.tuckerTangentProj_one_eq` |
| Tangent projector of the Tucker manifold on tensors, with core projector `P_C` | `Tensor.tuckerTangentProj U PC W` (`Tensor/Tucker/Tangent.lean`) | orthogonal projection onto the tangent space: `Tensor.tuckerTangentProj_eq_starProjection`; a different object from `modeTangentProj` (general `P_C`), equal to it for `P_C = 1` (row above) |
| Alternating sum of interface operators of a tensor train | `Tensor.ttTangentSum` (`Tensor/Defs.lean`) | projector properties: `Tensor.ttTangentSum_idem`, `Tensor.ttTangentSum_isOrthProj`, `Tensor.ttTangentSum_isObliqueProj` (`Tensor/TT/TangentProjector.lean`), used by `Tensor.isOrthProj_ttTangentProj`; the catalogue copy `OpenProblems.TensorNetworks.ttTangentSum` is the same expression: `ttTangentSum_eq_tensor` (`OpenProblems/TensorNetworks/Part2Defs.lean`); `OpenProblems.Randomized.ttTangent` is equal after the index shift `R k ↦ R (k + 1)`: `ttTangent_eq_ttTangentSum` (`OpenProblems/Randomized/Part4Defs.lean`) |
| Multilinear product `C ×₁ U₁ ⋯ ×_d U_d` | `Tensor.tucker` (`Tensor/Defs.lean`) | on three modes its entries are the triple sum `OpenProblems.TensorNetworks.tucker3`: `tucker_apply_eq_tucker3` (`OpenProblems/TensorNetworks/Part3Defs.lean`) |

Kept in the catalogue:

| Definition | Module | Why it stays |
|---|---|---|
| `ttTangentSum` | `OpenProblems/TensorNetworks/Part2Defs.lean` | three theorems recorded in `docs/statements.json` are stated with it (`ttTangentSum_idem`, `ttTangentSum_isObliqueProj`, `ttTangentSum_isOrthProj` in `OpenProblems/TensorNetworks/Part2b.lean`), and a recorded statement does not change; bridged by `ttTangentSum_eq_tensor`; no core module uses it |
| `schmidtOp` | `OpenProblems/TensorNetworks/Part2Defs.lean` | the operator `X ↦ ∑ₖ Bₖ X Cₖᵀ` on matrices, without a core counterpart; used in the catalogue files `Part2b` and `Part2c` of that folder only |
| `IsDefectParTuckerStep` | `OpenProblems/TensorNetworks/Part2Defs.lean` | a parallel Tucker step with a defect term; used in the catalogue file `Part2c` only; its relation to `parTuckerBUG` is not examined |
| `tucker3` | `OpenProblems/TensorNetworks/Part3Defs.lean` | tensors with three modes as functions `ι → κ → μ → ℝ`; used in the catalogue files `Part3a` and `Part3b` of that folder only; bridged (table above) |
| `tuckerTensor3` | `Literature/TensorNetworks/P1709_02594a.lean` | used in its own file only; not compared with `tucker3` or `Tensor.tucker` |

## Kinetic transport, flux and difference operators

Core files: `LeanDLRA/Kinetic/Defs.lean` (the streaming operator `Kinetic.streaming D M`, the map
`Y ↦ ∑ₖ Dₖ Y Mₖ` as a continuous linear map; the periodic difference matrices `Kinetic.fwdDiff`,
`Kinetic.bwdDiff`, `Kinetic.centralDiff`, `Kinetic.secondDiff N h` of type
`Matrix (ZMod N) (ZMod N) ℝ`; the moments `Kinetic.quadMoment`, `Kinetic.density`) and
`LeanDLRA/Kinetic/Stencils.lean` (the products of the four difference matrices with a matrix,
entry by entry: `Kinetic.fwdDiff_mul_apply`, `Kinetic.bwdDiff_mul_apply`,
`Kinetic.centralDiff_mul_apply`, `Kinetic.secondDiff_mul_apply`; and their transposes:
`Kinetic.fwdDiff_transpose`, `Kinetic.bwdDiff_transpose`, `Kinetic.centralDiff_transpose`,
`Kinetic.secondDiff_transpose`). The transposes say that minus the forward difference is the
adjoint of the backward difference and that the central difference is skew; this is what
summation by parts needs on the periodic grid.

The table lists the local forms of the catalogue files on kinetic equations. A local definition
that is equal to a core definition is replaced by it. One that is a multiple, a special case or
a generalization of a core definition stays, with a proven bridge. A step of a paper file is
bridged only to core maps that exist (`eulerStep`, `galerkinEulerStep`, `kslK`, `consTrunc`);
the core has no step structure for the schemes of these files.

| Concept | Core | Relation (lemma) |
|---|---|---|
| forward / backward difference `D⁺`, `D⁻` on `ZMod Nx`, divided by `Δx` (`Literature/Kinetic/P2212_12012a`, (3.3)) | `Kinetic.fwdDiff`, `Kinetic.bwdDiff` | equal (same body), **replaced** (rename map `docs/renames.json`); the four lemmas of the paper file on the products and the transposes of the two matrices are now the core lemmas `Kinetic.fwdDiff_mul_apply`, `Kinetic.bwdDiff_mul_apply`, `Kinetic.bwdDiff_transpose`, `Kinetic.fwdDiff_transpose` of `Kinetic/Stencils.lean` |
| advection operator `𝓛 g = D⁻ g A⁺ + D⁺ g A⁻` (`P2212_12012.transport`), and `downwind` | `Kinetic.streaming` | instance with two terms: `transport_eq_streaming`, `downwind_eq_streaming` (stay local: fixed matrices `plusA`, `minusA`) |
| central difference `Dˣ` on `ZMod n`, divided by `2 Δx` (`Literature/Kinetic/P2307_07538a`) | `Kinetic.centralDiff` | equal (same body), **replaced**; `Dx_mul_apply`, `Dx_transpose` keep their names and are the core lemmas at this grid |
| stabilizing second difference `Dˣˣ`, divided by `2 Δx` (`P2307_07538.Dxx`) | `Kinetic.secondDiff` | a multiple, stays: `Dxx_eq_smul_secondDiff : Dxx n Δx = (Δx / 2) • Kinetic.secondDiff n Δx` (all `Δx`, also `Δx = 0`) |
| `D⁺` divided by `√(2 Δx)` (`P2307_07538.Dplus`) | `Kinetic.fwdDiff` | a multiple, stays: `Dplus_eq_smul_fwdDiff : Dplus n Δx = (Δx / √(2 * Δx)) • Kinetic.fwdDiff n Δx` |
| `transport Δx A Aa u = -Dˣ u A + Dˣˣ u \|A\|` and `flux` (`P2307_07538`) | `Kinetic.streaming` | instances: `transport_eq_streaming` (terms `(-Dˣ, A)`, `(Dˣˣ, \|A\|)`), `flux_eq_streaming` (terms `(Dˣᵀ, A)`, `(-Dˣˣᵀ, \|A\|)`) |
| `u★ = X★ S★ V★ᵀ` of scheme (16) (`P2307_07538.IsCoupledStep`) | `galerkinEulerStep` (`Stability/Energy.lean`) | `IsCoupledStep.uStar_eq_galerkinEulerStep`: one core step with `P = P_X ∘ P_V`, field `transport`, from `u⁰ = X⁰ S⁰ V⁰ᵀ` |
| explicit K-step (16a) (`P2307_07538.kStar`) | `kslK` | `kStar_mul_transpose_eq_kslK : kStar … * V₀ᵀ = kslK (rightProj V₀) (transport Δx A Aa) Δt (X₀ * S₀ * V₀ᵀ)`, no orthonormality needed |
| conservative truncation of Sec. 6 (`P2307_07538.IsConservativeTruncation`) | `consTrunc` (`Stability/Conservation.lean`) | `IsConservativeTruncation.eq_consTrunc`: `C` right multiplication by `e₀ e₀ᵀ`, `T` the left projection `U Uᵀ` |
| `Dp`, `Dm` on grid functions and `DpM`, `DmM` on matrix columns (`Literature/Kinetic/P2402_16746a`) | `Kinetic.fwdDiff`, `Kinetic.bwdDiff` | different type (maps, not matrices), stay: `Dp_eq_fwdDiff_mulVec`, `Dm_eq_bwdDiff_mulVec`, `DpM_eq_fwdDiff_mul`, `DmM_eq_bwdDiff_mul` |
| flux `𝓛 g = D⁻ g A⁺ + D⁺ g A⁻` (`P2402_16746.Params.flux`) | `Kinetic.streaming` | instance with two terms: `Params.flux_eq_streaming` |
| stencils `T⁽²⁾`, `T⁽¹⁾` for a neighbour permutation `σ` on any finite index set (`Literature/Kinetic/P2111_07160a`) | `Kinetic.centralDiff`, `Kinetic.secondDiff` | more general than the core, stay; on `ZMod N` with `σ = Equiv.addRight 1`: `T2_addRight_eq_centralDiff`, `T1_addRight_eq_smul_secondDiff : T1 … Δ = -(Δ / 2) • Kinetic.secondDiff N Δ` |
| flux `F(u)` of Sec. 2.4 (`P2111_07160.PNScheme.flux`) | `Kinetic.streaming` | instance with four terms: `PNScheme.flux_eq_streaming` |
| explicit Euler update `u - Δt F(u)` (`PNScheme.euler`) | `eulerStep` (`Analysis/Defs.lean`) | `PNScheme.euler_eq_eulerStep : S.euler Δt u = eulerStep (fun u => -S.flux u) Δt u` |
| fixed-rank S-step (34c) (`P2111_07160.bugStreamS`) | `galerkinEulerStep` | `bugStreamS_eq_galerkinEulerStep` (new bases with orthonormal columns): `X * bugStreamS … * Wᵀ` is one core step with `P = P_X ∘ P_W` from `u⁰ = X₀ S₀ W₀ᵀ` |
| augmented S-step (`P2111_07160.augStreamS`) | `eulerStep`, `leftProj`, `rightProj` | `augStreamS_eq_eulerStep`, `mul_augStreamS_mul_eq_proj_eulerStep` (no orthonormality needed) |
| moments `(p, f(x, ·))ᵥ`, density, current, stress, kinetic energy, energy flux (`Literature/Kinetic/P2608_00397a`, `Grid.pair`, `dens`, `cur`, `stress`, `kin`, `heat`) | `Kinetic.quadMoment`, `Kinetic.density` | the core moments at the field `G.wv` of the structure `Grid`, stay; six bridges by `rfl`: `Grid.pair_eq_quadMoment`, `Grid.dens_eq_density`, `Grid.cur_eq_quadMoment`, `Grid.stress_eq_quadMoment`, `Grid.kin_eq_quadMoment`, `Grid.heat_eq_quadMoment` |
| transport `D(f) = -v·∇ₓ f - E·∇ᵥ f` with frozen field (`P2608_00397.Grid.transport`) | `Kinetic.streaming` | minus an instance with `2 d` terms, the discrete derivatives (linear maps) written as matrices: `Grid.transport_eq_neg_streaming` |
| moment `∫ ζ f dv` (`Literature/Kinetic/P2101_12571b`, `Grid.density`) | `Kinetic.quadMoment`, `Kinetic.density` | the core moment at the field `q.wv`, stays (the name occurs on 78 lines of the file); `Grid.density_eq_quadMoment`, `Grid.density_one_eq_density` by `rfl` |
| discrete Vlasov right-hand side `-v ∂ₓ f + E[f] ∂ᵥ f` (`P2101_12571.vlasovRHS`) | `Kinetic.streaming` | value at `f` with the field value `E f`: `vlasovRHS_eq_streaming` (two terms `(-dx, diag v)`, `(diag (E f), dvᵀ)`); not a statement of linearity in `f` |
| centred difference `vpDx` on `Fin 4` (`P2101_12571b`), `Fin`-indexed stencils of `P2307_07538b`, `P1907_04247a.transport` | `Kinetic.centralDiff`, `Kinetic.streaming` | not bridged; the core stencils are indexed by `ZMod N`, and the core form for cells numbered by `Fin N` is the submatrix along `ZMod.finEquiv N` (`Kinetic.fwdDiff_submatrix_finEquiv` and the three analogues, `Kinetic/Stencils.lean`), to which these local stencils can be compared |

## Time grids, step relations, runs and the local error

Core file: `LeanDLRA/Integrators/Defs.lean` (definitions and first lemmas). The lemmas that need
the Grönwall estimate are in `LeanDLRA/Integrators/GlobalError.lean`, the construction of a run in
`LeanDLRA/Integrators/Tube.lean`. A method is a relation between the start and the result of one
step, not a function, because the low-rank integrators involve choices (bases from QR or SVD
factorizations are not unique). The relation contains the algorithm only; Lipschitz constants and
normal-component bounds are hypotheses of the theorems. The predicates on step relations constrain
forward steps `t₀ ≤ t₁` only.

| Concept | Core | Relation (lemma) |
|---|---|---|
| Time grid `τ 0 ≤ τ 1 ≤ ⋯ ≤ τ N` (the step sizes may differ and may be zero) | `IsGrid τ N` | defining: `isGrid_iff`; equivalent to monotonicity on `{0, …, N}`: `isGrid_iff_monotoneOn`; restriction to the first `n ≤ N` steps: `IsGrid.of_le` |
| Uniform grid `n ↦ t₀ + n h` | `uniformGrid t₀ h` | a grid for `0 ≤ h`: `isGrid_uniformGrid`; step size `h`: `uniformGrid_succ_sub`; step `n < N` lies in `[t₀, t₀ + N h]`: `uniformGrid_step` |
| One step of a method for one field: `Y₁` is an admissible result of a step from `Y₀` at time `t₀` to time `t₁` | `StepRel E` (the type `ℝ → ℝ → E → E → Prop`), written `M t₀ t₁ Y₀ Y₁` | defining |
| Numerical solution: values `Y 0, …, Y N` on a grid, each obtained from the previous one by a step | `IsRun M τ N Y` | defining (fields `grid`, `step`); on the uniform grid with `0 ≤ h` it is `∀ n < N, M (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (Y (n + 1))`: `isRun_uniformGrid_iff`; restriction: `IsRun.of_le`; a run over `N` steps exists if every run over `n < N` steps that starts at `Y₀` can be continued by one step: `exists_isRun` |
| Local error of one step: `‖Y₁ - Φ t₁‖ ≤ δ` for every exact solution `Φ` on `[t₀, t₁]` with `Φ t₀ = Y₀` | `HasLocalError F t₀ t₁ Y₀ Y₁ δ` | defining; the exact solution is quantified, so the statement holds trivially if there is none; a larger bound: `HasLocalError.mono` |
| Local error of a method on a region `D` of pairs (time, state) | `StepRel.HasLocalErrorOn M F D δ` with `δ : ℝ → ℝ → ℝ` | implies the local errors of the steps of a run that stays in `D`: `IsRun.hasLocalError` |
| Method that reproduces a solution `A` of a problem whose right-hand side does not depend on the state (`IsDerivRHS F A t₀ t₁`) | `StepRel.IsExactFor M F A` | implied by local error `0` on a region that contains the graph of `A`: `StepRel.HasLocalErrorOn.isExactFor`; a run that starts at `A (τ 0)` equals `A` on the grid: `IsRun.eq_of_isExactFor` |
| Conservation of a quantity `I` up to `ϑ` per forward step | `StepRel.ConservesUpTo M I ϑ` | along a run `|I (Y n) - I (Y 0)| ≤ n * ϑ`: `IsRun.abs_sub_le` |

## Exact-flow fans and the global error

Core files: `LeanDLRA/Integrators/Defs.lean` (`IsExactFan`, `FanStable`),
`LeanDLRA/Integrators/GlobalError.lean` (the estimates). The exact-flow fan of numerical values
`Y n` consists of the exact solutions started at these values ("Lady Windermere's fan"). The global
error follows from the local errors and from the stability of the exact flow along the fan; the
method does not enter.

| Concept | Core | Relation (lemma) |
|---|---|---|
| Exact-flow fan: `Φ n` solves `y' = F(t, y)` on `[τ n, τ (n + 1)]` with `Φ n (τ n) = Y n` | `IsExactFan F τ N Y Φ` | defining (fields `sol`, `start`); on the uniform grid it is the pair of hypotheses `hΦ`, `hΦ₀` of `lady_windermere`: `isExactFan_uniformGrid_iff`; exists for a globally Lipschitz field that is continuous in time, on a complete space: `exists_isExactFan` |
| Stability of the exact flow along the fan with factors `a n`: `‖Φ n (τ (n + 1)) - A (τ (n + 1))‖ ≤ a n * ‖Φ n (τ n) - A (τ n)‖` | `FanStable A τ N Φ a` | holds with `a n = Real.exp (L * (τ (n + 1) - τ n))` for a Lipschitz field: `IsLipschitzField.fanStable`, on a region: `IsLipschitzFieldOn.fanStable`, on a tube: `IsLipschitzOnTube.fanStable`, `DLRAProblem.fanStable`; with a one-sided Lipschitz constant `ℓ` in place of `L`: `IsOneSidedLipschitzField.fanStable`, `IsOneSidedLipschitzFieldOn.fanStable`, `fanStable_of_inner_le` |
| Local errors of the steps and local errors along a fan | `HasLocalError` | implies `‖Y (n + 1) - Φ n (τ (n + 1))‖ ≤ δ n` along any fan: `IsExactFan.norm_sub_le_of_hasLocalError` |
| Global error from local errors and stability, `‖Y n - A (τ n)‖ ≤ (∏ a) ‖Y 0 - A (τ 0)‖ + ∑ (∏ a) δ k` | `IsExactFan.norm_sub_le` | from the discrete estimate `FanStable.norm_sub_le` (which rests on `discrete_gronwall_prod_le`); for a globally Lipschitz field, with no fan in the hypotheses: `IsLipschitzField.norm_sub_le_of_hasLocalError` |

## Tubes, the problem on a tube and the tube theorem

Core files: `LeanDLRA/Analysis/Defs.lean` (tube, extension, fields on regions),
`LeanDLRA/DLRA/Defs.lean` (`DLRAProblem`), `LeanDLRA/Foundations/Localization.lean` (properties of
the extension), `LeanDLRA/Integrators/Tube.lean` (the tube theorem). The tube of radius `ρ` around
a curve `A` on `[a, b]` is the set of pairs `(t, x)` with `t ∈ [a, b]` and `‖x - A t‖ ≤ ρ`. The
tube theorem bounds the global error of numerical values from hypotheses on the tube only: an error
bound below the tube radius keeps the values in the tube.

| Concept | Core | Relation (lemma) |
|---|---|---|
| Tube around `A` | `tubeSet A a b ρ` | defining |
| Field that is `L`-Lipschitz, resp. bounded by `B`, on the tube | `IsLipschitzOnTube F A a b ρ L`, `IsBoundedOnTube F A a b ρ B` | equal to the region forms `IsLipschitzFieldOn F (tubeSet A a b ρ) L`, `IsBoundedFieldOn F (tubeSet A a b ρ) B`: `isLipschitzOnTube_iff`, `isBoundedOnTube_iff`; implied by the global forms: `IsLipschitzField.isLipschitzOnTube` |
| Extension of a field on a tube to the whole space (radial retraction `ballRetract` onto the ball around `A t`; zero for `t ∉ [a, b]`) | `tubeExt F A a b ρ` | agrees with `F` on the tube: `tubeExt_eq`; `L`-Lipschitz everywhere if `0 ≤ L`, `0 ≤ ρ`: `isLipschitzField_tubeExt`; bounded by `B` everywhere if `0 ≤ B`, `0 ≤ ρ`: `isBoundedField_tubeExt`; a curve in the tube solves the extended equation iff it solves the original one: `odeSolution_tubeExt_iff` |
| The problem: `A` solves `y' = F(t, y)` on `[a, b]`, `F` is `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around `A`, `0 ≤ L`, `0 ≤ B` | `DLRAProblem F A a b ρ L B` (fields `sol`, `L_nonneg`, `B_nonneg`, `lipschitz`, `bounded`) | defining: `dlraProblem_iff`; from a globally Lipschitz and bounded field, for every `ρ`: `DLRAProblem.of_global`; smaller interval and radius: `DLRAProblem.mono`; the extension is a global problem with the same `L`, `B` and the same solution if `0 ≤ ρ`: `DLRAProblem.tubeExt` |
| Exact solutions near `A` (needed for the fan) | `exists_ODESolution_near` | a consequence of the tube hypotheses and continuity of `F` on the tube, on a complete space; used in the tube theorem for local errors |
| Tube theorem, exact solutions given: radii `R n` with `R n + 2 * B * (τ (n + 1) - τ n) < ρ`, error bound at most `R n` | `IsLipschitzOnTube.norm_sub_le_of_fan` | conclusion `‖Y n - A (τ n)‖ ≤ Real.exp (L * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ + ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k`; with the margin as a hypothesis on the values: `IsExactFan.norm_sub_le_of_near`; uniform grid: `IsLipschitzOnTube.norm_sub_le_of_fan_uniformGrid` |
| Tube theorem for local errors (no fan in the hypotheses; `F` continuous on the tube, complete space) | `IsLipschitzOnTube.norm_sub_le_of_hasLocalError` | bundled form: `DLRAProblem.norm_sub_le_of_hasLocalError` |
| Tube theorem for the runs of a step relation | `IsRun.norm_sub_le_of_tube` | from `DLRAProblem.norm_sub_le_of_hasLocalError`; for a method with `StepRel.HasLocalErrorOn` on an inner tube: `IsRun.norm_sub_le_of_hasLocalErrorOn`; on the uniform grid with local error `h * c`, bound `Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c` and condition `… + 2 * B * h < ρ`: `IsRun.norm_sub_le_of_tube_uniformGrid` (the estimate of the sum is `uniformGrid_errorBound_le`) |
| Local error with respect to the extended field | `HasLocalError (tubeExt F A a b ρ) t₀ t₁ Y₀ Y₁ δ` | implies the local error with respect to `F` if `‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ`: `HasLocalError.of_tubeExt` (`Integrators/Method.lean`) |

## Step methods and tube-local methods

Core file: `LeanDLRA/Integrators/Method.lean`. A step method assigns a step relation to every
field. The file proves once, for all step methods, that a method with three properties of one step
can be run near a solution and that the run satisfies the error bound of the tube theorem. The
three properties are (E) a step exists for every globally Lipschitz field, (I) a step keeps the
admissibility predicate `Adm`, (T) a step of the extended field `tubeExt F A a b ρ` from a start
value with the margin `‖Y₀ - A t₀‖ + κ * B * (t₁ - t₀) < ρ` is a step of `F`. The local error (L)
is a separate hypothesis of the theorem.

| Concept | Core | Relation (lemma) |
|---|---|---|
| Method as a map from fields to step relations | `StepMethod E` (the type `(ℝ → E → E) → StepRel E`), written `M F t₀ t₁ Y₀ Y₁` | defining; `M F` is a `StepRel E` |
| Method with (E), (I), (T), admissible values `Adm` and margin constant `κ` | `StepMethod.IsTubeLocal M Adm κ` (fields `exists_step`, `adm_of_step`, `step_of_tubeExt`) | defining; a larger `κ`: `StepMethod.IsTubeLocal.mono` |
| Runs with an invariant: every step from an admissible value near `A` ends at an admissible value | `IsRun.adm_and_norm_sub_le_of_tube` (predicates `Adm n` that may depend on the step index) | for the trivial invariant it is `IsRun.norm_sub_le_of_tube`; uniform grid: `IsRun.adm_and_norm_sub_le_of_tube_uniformGrid` |
| Existence of a run for a step relation whose steps exist, keep `Adm` and have a local error near `A` | `exists_isRun_norm_sub_le_of_tube` | from `exists_isRun` and `IsRun.adm_and_norm_sub_le_of_tube`; uniform grid: `exists_isRun_norm_sub_le_of_tube_uniformGrid` |
| Existence of a run and error bound for a tube-local method with `2 ≤ κ` and local error `h * c`, under `Real.exp (L * T) * δ + T * Real.exp (L * T) * c + κ * B * h < ρ` | `StepMethod.IsTubeLocal.exists_run_norm_sub_le` | conclusion: a run `Y` of `M F` on `uniformGrid t₀ h` with `Y 0 = Y₀` and, for `n ≤ N`, `Adm (Y n)` and `‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) * c`; instances: the five matrix integrators of the section "Matrix integrators as step methods" below, and explicit Euler (the last `example`s of the file) |
| The run theorem on a grid `τ` with variable step sizes and local error bounds `δ n` | `StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_isGrid` (`Integrators/MethodGrid.lean`) | `exists_isRun_norm_sub_le_of_tube` for the step relation `M F` of a tube-local method; conclusion `‖Y n - A (τ n)‖ ≤ Real.exp (L * (τ n - τ 0)) * ‖Y₀ - A (τ 0)‖ + ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k`, if upper bounds `R n` of this bound satisfy `R n + κ * B * (τ (n + 1) - τ n) < ρ` |
| The run theorem for steps with local error `h * c + ϑ` (a step followed by a change of at most `ϑ`, for example a truncation to a tolerance) | `StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_tol` (`Integrators/MethodTolerance.lean`) | the grid theorem for the uniform grid and `δ n = h * c + ϑ`; bound `Real.exp (L * T) * (δ + n * ϑ) + T * Real.exp (L * T) * c` under `Real.exp (L * T) * (δ + N * ϑ) + T * Real.exp (L * T) * c + κ * B * h < ρ`; a result that is changed by at most `ϑ` has local error `δ + ϑ`: `HasLocalError.add_of_norm_sub_le`; used in the last `example` of `Integrators/Matrix/TruncBUGRun.lean` (a truncation computed up to an error `ϑ`) |

## The steps of the BUG integrator

Core files: `LeanDLRA/Integrators/BUGCore.lean` (the algorithm), `LeanDLRA/Integrators/BUG.lean`
(the step with the normal-component bound of the error analysis),
`LeanDLRA/Integrators/TuckerBUG.lean` (several modes). The abstract step is written with orthogonal
projections on an inner product space `E`: `P₀`, `Q₀` are the projections of the start value
(column and row space in the matrix case), `P₁`, `Q₁` those of the updated bases. The step
[CerutiLubich2022, §3.1] solves one differential equation per mode for the new bases and then a
Galerkin equation in the new bases.

| Concept | Core | Relation (lemma) |
|---|---|---|
| Basis update for a family of modes `i`: substep solutions `YK i` of `y' = Q₀ i (F(t, y))` from `Y₀`, whose end values lie in the range of the new projection `P₁ i` | `BasisUpdate F Q₀ P₁ t₀ t₁ Y₀ YK` (fields `projQ₀`, `projP₁`, `comm₁`, `kSol`, `kStart`, `kCap`) | defining; two modes written out: `basisUpdate_two_iff` |
| One step of the BUG integrator, algorithm only: the basis update for the two modes and the Galerkin solution `YS` of `y' = P₁ (Q₁ (F(t, y)))` from `P₁ (Q₁ Y₀)` | `IsBUGStepCore F P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS` (extends `BasisUpdate F ![Q₀, P₀] ![P₁, Q₁] t₀ t₁ Y₀ ![YK, YL]`; fields `sSol`, `sStart`) | defining: `isBUGStepCore_iff`; its basis update: `IsBUGStepCore.toBasisUpdate` |
| The step with the normal-component bound `ε` at the results of the two basis substeps | `IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS` | equivalent to the core step and the two bounds: `isBUGStep_iff`; implies: `IsBUGStep.isBUGStepCore`; converse with the bounds as hypotheses: `IsBUGStepCore.isBUGStep` |
| The step for `d` modes (Tucker format) | `IsTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS` | basis update for `d` modes, normal bounds and a Galerkin step with `modeProd P₁`: `isTuckerBUGStep_iff`; for two modes equivalent to `IsBUGStep`: `isTuckerBUGStep_two_iff` |
| Local error of the core step for a globally Lipschitz and bounded field [CerutiLubich2022, Lemma 4] | `IsBUGStepCore.hasLocalError` | hypotheses: the two normal-component bounds `ε` at the results `YK t₁`, `YL t₁` of the basis substeps; conclusion `HasLocalError F t₀ t₁ Y₀ (YS t₁) ((t₁ - t₀) * (bugC₁ L H * ε + bugC₂ L B H * (t₁ - t₀)))` for `t₁ - t₀ ≤ H`, with `bugC₁ L H = 2 + 2 * L * H * Real.exp (L * H)` and `bugC₂ L B H = L * B * (8 + Real.exp (L * H) * (1 + 8 * L * H))` |
| The core step near a reference solution `A` of a field on a tube | `isBUGStepCore_tubeExt_iff_of_near` | a step of `tubeExt F A a b ρ` is a step of `F`, and conversely, if `‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ`; the basis substeps stay within `2 * B * (t₁ - t₀)` of the start: `BasisUpdate.norm_sub_lt_of_near`; without the margin, for curves in the tube: `basisUpdate_tubeExt_iff`, `isBUGStepCore_tubeExt_iff`; local error from tube hypotheses: `IsBUGStepCore.hasLocalError_of_tube` |

## Matrix integrators as step methods

Core files: `LeanDLRA/Integrators/Matrix/BUGStep.lean`, `LeanDLRA/Integrators/Matrix/BUGRun.lean`
(BUG, [CerutiLubich2022]); `LeanDLRA/Integrators/Matrix/KSLStep.lean`,
`LeanDLRA/Integrators/Matrix/KSLRun.lean` (projector splitting, [LubichOseledets2014],
[KieriLubichWalach2016]); `LeanDLRA/Integrators/Matrix/ParallelBUGStep.lean`,
`LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean` (parallel BUG with fixed rank,
[CerutiKuschLubich2024]); `LeanDLRA/Integrators/Matrix/EulerBUGStep.lean`,
`LeanDLRA/Integrators/Matrix/EulerBUGRun.lean` (BUG with explicit Euler substeps and fixed rank;
the module docstrings cite Nobile and Riffaud, arXiv 2502.07040, §2.1, Algorithm 1);
`LeanDLRA/Integrators/Matrix/AdaptiveBUGStep.lean`, `LeanDLRA/Integrators/Matrix/TruncBUGRun.lean`
(BUG with augmented bases, truncated by a tolerance or to a fixed rank; the module docstrings
cite Ceruti, Kusch and Lubich, arXiv 2104.05247). The steps in factors (`IsStep`) of the first
three are defined in `LeanDLRA/Integrators/Matrix/BUG.lean`,
`LeanDLRA/Integrators/Matrix/ProjectorSplitting.lean` and
`LeanDLRA/Integrators/Matrix/ParallelBUG.lean`, that of the fourth in `EulerBUGStep.lean`; the
fifth uses `MatrixBUG.IsRankAdaptiveStep` of `LeanDLRA/Integrators/Matrix/BUG.lean`. A step
relation on matrices quantifies the factorization of the start value, so a run may change the
factorization between steps; for the first three integrators a chain of factor steps is a run
(`isRun_stepRel_of_isStep` in each of the three namespaces). In all five cases the admissible
values of the run theorems are the matrices of rank at most `r`, and their normal-component
hypothesis is `FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε`.

| Concept | Core | Relation (lemma) |
|---|---|---|
| Matrix BUG step in factors `U₀ S₀ V₀ᵀ → U₁ S(t₁) V₁ᵀ` | `MatrixBUG.IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S` | an instance of the abstract core step with `leftProj U₀`, `rightProj V₀`, `leftProj U₁`, `rightProj V₁`: `MatrixBUG.IsStep.isBUGStepCore` |
| BUG step relation on matrices | `MatrixBUG.stepRel F r` (`∃ U₀ S₀ V₀ U₁ V₁ K Lf S, Y₀ = U₀ * S₀ * V₀ᵀ ∧ IsStep … ∧ Y₁ = U₁ * S t₁ * V₁ᵀ`) | from a factor step: `MatrixBUG.IsStep.stepRel`; a chain of factor steps is a run: `MatrixBUG.isRun_stepRel_of_isStep`; rank: `MatrixBUG.stepRel.rank_le`, `MatrixBUG.stepRel.rank_start_le`, `MatrixBUG.IsRun.rank_le`; a step from `Y₀` exists iff `Y₀.rank ≤ r` (globally Lipschitz field, continuous in time on the step interval, `r` at most the number of rows and of columns): `MatrixBUG.exists_stepRel_iff` |
| BUG: step near the solution and local error | `MatrixBUG.stepRel_tubeExt_iff_of_near`, `MatrixBUG.stepRel.hasLocalError_of_tube` | margin `‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ`; local error `(t₁ - t₀) * (bugC₁ L H * ε + bugC₂ L B H * (t₁ - t₀))` for `t₁ - t₀ ≤ H`; for a global field: `MatrixBUG.stepRel.hasLocalError`, `MatrixBUG.stepRel_hasLocalErrorOn` |
| BUG is tube-local | `MatrixBUG.isTubeLocal_stepRel`: `StepMethod.IsTubeLocal (fun G => stepRel G r) (fun Y => Y.rank ≤ r) 4` | instance of `StepMethod.IsTubeLocal` with `κ = 4` |
| BUG: existence of a run and error bound [CerutiLubich2022, Thm. 4] | `MatrixBUG.exists_run_norm_sub_le` | instance of `StepMethod.IsTubeLocal.exists_run_norm_sub_le`: a run with `(Y n).rank ≤ r` and `‖Y n - A (t₀ + n * h)‖ ≤ bugGlobalBound L B H T δ ε h` under `bugGlobalBound L B H T δ ε h + 4 * B * h < ρ` and `h ≤ H`; `bugGlobalBound L B H T δ ε h = Real.exp (L * T) * δ + T * Real.exp (L * T) * (bugC₁ L H * ε + bugC₂ L B H * h)` (`bugGlobalBound_eq`); every run: `MatrixBUG.IsRun.norm_sub_le`; chain of factor steps: `MatrixBUG.norm_sub_le_of_isStep`; the condition can be met if `T * Real.exp (L * T) * bugC₁ L H * ε < ρ`: `exists_bugGlobalBound_lt` |
| BUG: the earlier forms of the error bound | `MatrixBUG.global_error_le` (global field, exact solutions on the steps given), `MatrixBUG.norm_sub_le_of_tube` (tube hypotheses, exact solutions given), `bug_global_error_le_of_tube` (abstract step, tube hypotheses) | `MatrixBUG.norm_sub_le_of_tube` follows from `IsLipschitzOnTube.norm_sub_le_of_fan_uniformGrid` and `MatrixBUG.IsStep.hasLocalError_of_tube`; `bug_global_error_le_of_tube` and `MatrixBUG.global_error_le` are recovered as `example`s in `Integrators/Matrix/BUGTube.lean` |
| Projector-splitting step in factors (K, S, L substeps one after the other) | `MatrixKSL.IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf` | defining |
| Projector-splitting step relation | `MatrixKSL.stepRel F r` (`∃ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf, Y₀ = U₀ * S₀ * V₀ᵀ ∧ IsStep … ∧ Y₁ = U₁ * (Lf t₁)ᵀ`) | from a factor step: `MatrixKSL.IsStep.stepRel`; chain: `MatrixKSL.isRun_stepRel_of_isStep`; rank: `MatrixKSL.stepRel.rank_le`, `MatrixKSL.IsRun.rank_le`; a step exists iff `Y₀.rank ≤ r`, under the same hypotheses: `MatrixKSL.exists_stepRel_iff` |
| Projector splitting: step near the solution and local error | `MatrixKSL.stepRel_tubeExt_iff_of_near`, `MatrixKSL.stepRel.hasLocalError_of_tube` | margin `‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ`; local error `(t₁ - t₀) * (10 * L * B * (t₁ - t₀) + ε)`, no bound on the step size; for a global field: `MatrixKSL.stepRel.hasLocalError`, `MatrixKSL.stepRel_hasLocalErrorOn` |
| Projector splitting is tube-local | `MatrixKSL.isTubeLocal_stepRel` | instance of `StepMethod.IsTubeLocal` with `κ = 4` and `Adm Y = (Y.rank ≤ r)` |
| Projector splitting: existence of a run and error bound | `MatrixKSL.exists_run_norm_sub_le` | instance of `StepMethod.IsTubeLocal.exists_run_norm_sub_le`: bound `Real.exp (L * T) * δ + T * Real.exp (L * T) * (10 * L * B * h + ε)` under `… + 4 * B * h < ρ`; every run: `MatrixKSL.IsRun.norm_sub_le`; chain of factor steps: `MatrixKSL.norm_sub_le_of_isStep` |
| Parallel BUG step in factors with augmented bases | `MatrixParallelBUG.IsStep`, result `MatrixParallelBUG.augmented` | defining |
| Parallel BUG, augmented step relation (result of rank at most `2 r`, no truncation) | `MatrixParallelBUG.augmentedRel F r` | from a factor step, with any new directions `U₁`, `V₁`: `MatrixParallelBUG.IsStep.augmentedRel`; local error on a tube `(t₁ - t₀) * (7 * L * B * (t₁ - t₀) + ε)`: `MatrixParallelBUG.augmentedRel.hasLocalError_of_tube` |
| Parallel BUG with fixed rank: augmented step followed by a best approximation of rank at most `r` | `MatrixParallelBUG.stepRel F r` (`∃ Yh, augmentedRel F r t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧ ‖Y₁ - Yh‖ ≤ distLR r Yh`) | every augmented step can be completed: `MatrixParallelBUG.augmentedRel.exists_stepRel`; chain: `MatrixParallelBUG.isRun_stepRel_of_isStep`; rank: `MatrixParallelBUG.stepRel.rank_le`, `MatrixParallelBUG.IsRun.rank_le`; a step exists iff `Y₀.rank ≤ r`, under the same hypotheses: `MatrixParallelBUG.exists_stepRel_iff` |
| Parallel BUG: step near the solution and local error | `MatrixParallelBUG.stepRel_tubeExt_iff_of_near`, `MatrixParallelBUG.stepRel.hasLocalError_of_tube` | margin `‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ` (the three substeps start from the same matrix); local error `(t₁ - t₀) * (24 * L * B * (t₁ - t₀) + 3 * ε)`; needs `F` continuous on the tube and `A` continuous |
| Parallel BUG is tube-local | `MatrixParallelBUG.isTubeLocal_stepRel` | instance of `StepMethod.IsTubeLocal` with `κ = 2` and `Adm Y = (Y.rank ≤ r)` |
| Parallel BUG: existence of a run and error bound | `MatrixParallelBUG.exists_run_norm_sub_le` | instance of `StepMethod.IsTubeLocal.exists_run_norm_sub_le`: bound `Real.exp (L * T) * δ + T * Real.exp (L * T) * (24 * L * B * h + 3 * ε)` under `… + 2 * B * h < ρ`; every run: `MatrixParallelBUG.IsRun.norm_sub_le`; chain of factor steps: `MatrixParallelBUG.norm_sub_le_of_isStep` |
| Euler BUG step in factors: one evaluation `F₀ = F t₀ (U₀ * S₀ * V₀ᵀ)`; new bases `Ua`, `Va` with orthonormal columns whose ranges contain `U₀`, `F₀ * V₀` and `V₀`, `F₀ᵀ * U₀`; core `Sa = Uaᵀ * (U₀ * S₀ * V₀ᵀ + (t₁ - t₀) • F₀) * Va` | `MatrixEulerBUG.IsStep F t₀ t₁ U₀ S₀ V₀ Ua Sa Va` | defining; distance from the explicit Euler step of the full problem: `MatrixEulerBUG.IsStep.norm_sub_euler_le`; a step exists for every field: `MatrixEulerBUG.exists_isStep` |
| Euler BUG, augmented step relation (new bases with at most `2 r` columns, no truncation) | `MatrixEulerBUG.augmentedRel F r` | from a factor step: `MatrixEulerBUG.IsStep.augmentedRel`; rank at most `2 r`: `MatrixEulerBUG.augmentedRel.rank_le`; local error on a tube: `MatrixEulerBUG.augmentedRel.hasLocalError_of_tube` |
| Euler BUG with fixed rank: augmented step followed by a best approximation of rank at most `r` | `MatrixEulerBUG.stepRel F r` (`∃ Yh, augmentedRel F r t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧ ‖Y₁ - Yh‖ ≤ distLR r Yh`) | every augmented step can be completed: `MatrixEulerBUG.augmentedRel.exists_stepRel`; rank: `MatrixEulerBUG.stepRel.rank_le`, `MatrixEulerBUG.IsRun.rank_le`; a step exists iff `Y₀.rank ≤ r`, for every field (`r` at most the numbers of rows and columns): `MatrixEulerBUG.exists_stepRel_iff`; a run exists on every grid: `MatrixEulerBUG.exists_run` |
| Euler BUG: step near the solution and local error | `MatrixEulerBUG.stepRel_tubeExt_iff`, `MatrixEulerBUG.stepRel.hasLocalError_of_tube` | a step of `tubeExt F A a b ρ` is a step of `F`, and conversely, if `‖Y₀ - A t₀‖ ≤ ρ` (no margin: the step evaluates the field at `(t₀, Y₀)` only); local error `(t₁ - t₀) * ((11 * L * B + Lt) * (t₁ - t₀) + 3 * ε)` under `‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ` and `‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀)` on `[t₀, t₁)`; needs `F` continuous on the tube and `A` continuous |
| Euler BUG is tube-local | `MatrixEulerBUG.isTubeLocal_stepRel` | instance of `StepMethod.IsTubeLocal` with `κ = 0` and `Adm Y = (Y.rank ≤ r)`; the run theorem uses it with `κ = 2` (`StepMethod.IsTubeLocal.mono`) |
| Euler BUG: existence of a run and error bound | `MatrixEulerBUG.exists_run_norm_sub_le` | instance of `StepMethod.IsTubeLocal.exists_run_norm_sub_le`: bound `Real.exp (L * T) * δ + T * Real.exp (L * T) * ((11 * L * B + Lt) * h + 3 * ε)` under `… + 2 * B * h < ρ`, with the Lipschitz condition in time `‖F t x - F s x‖ ≤ Lt * (t - s)` for `s ≤ t` and `x` in the tube at both times; every run: `MatrixEulerBUG.IsRun.norm_sub_le` |
| BUG with augmented bases, step relation without truncation (result of rank at most `2 r`) | `MatrixBUG.augmentedRel F r` (`Integrators/Matrix/AdaptiveBUGStep.lean`) | a step `MatrixBUG.IsRankAdaptiveStep` from a factorization with `r` columns; rank: `MatrixBUG.augmentedRel.rank_le`; local error on a tube: `MatrixBUG.augmentedRel.hasLocalError_of_tube` |
| BUG with augmented bases and truncation by a tolerance `ϑ` (rank-adaptive) | `MatrixBUG.adaptiveStepRel F R ϑ` | from an augmented step: `MatrixBUG.augmentedRel.adaptiveStepRel`; local error on a tube: `MatrixBUG.adaptiveStepRel.hasLocalError_of_tube`; no run theorem in the core |
| BUG with augmented bases and truncation to rank `r` | `MatrixBUG.truncStepRel F r κ` (`∃ Yh, augmentedRel F r t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧ ‖Y₁ - Yh‖ ≤ κ * distLR r Yh`) | every augmented step can be completed for `1 ≤ κ`: `MatrixBUG.augmentedRel.exists_truncStepRel`; rank: `MatrixBUG.truncStepRel.rank_le`; step near the solution: `MatrixBUG.truncStepRel_tubeExt_iff_of_near`; local error on a tube: `MatrixBUG.truncStepRel.hasLocalError_of_tube` |
| Truncated BUG is tube-local; existence of a run and error bound | `MatrixBUG.isTubeLocal_truncStepRel`, `MatrixBUG.trunc_exists_run_norm_sub_le` (`Integrators/Matrix/TruncBUGRun.lean`) | instance of `StepMethod.IsTubeLocal` with `κ = 4` (the margin constant; the factor of the truncation is a different `κ`) and `Adm Y = (Y.rank ≤ r)`; bound `Real.exp (L * T) * δ + T * Real.exp (L * T) * (κ * (10 * L * B * h + ε) + (1 + κ) * (bugC₁ L H * ε + bugC₂ L B H * h))` under `… + 4 * B * h < ρ`, `h ≤ H`, `1 ≤ κ`; every run: `MatrixBUG.IsRun.norm_sub_le_of_truncStepRel` |

**Two spellings of one hypothesis (finding).** `MatrixBUG.stepRel.hasLocalError` takes the global
normal-component bound as `MatrixBUG.FactoredNormalBound F r ε`, `MatrixKSL.stepRel.hasLocalError`
takes it as `FactoredNormalBoundOn F r univ ε`. The two are equivalent by
`factoredNormalBound_iff_univ` (next section).

**Not bridged yet (finding, 2026-11-16).** The core files that use `StepRel` and `IsRun` are the
six files of the generic theory (`Integrators/Defs.lean`, `Integrators/GlobalError.lean`,
`Integrators/Tube.lean`, `Integrators/Method.lean`, `Integrators/MethodGrid.lean`,
`Integrators/MethodTolerance.lean`) and the ten files of the five matrix integrators above.
The other step predicates of the core are predicates on the data of one step (bases, substep
solutions) and have no step relation of type `StepRel`: among them `IsTuckerBUGStep`,
`IsParTuckerBUGStep`, `IsAugTuckerBUGStep`, `IsRankAdaptiveBUGStep`, `IsParallelBUGStep`,
`IsMidpointBUGStep`, `IsImplicitBUGStep`, and the tensor-train steps `IsTTKSLStep`,
`IsTTAugBUGStep`. The error bounds of the core for these
steps are stated for chains of steps and are not instances of
`StepMethod.IsTubeLocal.exists_run_norm_sub_le`.

## Normal-component bounds on regions

Core files: `LeanDLRA/DLRA/Defs.lean` (`NormalBoundOn`), `LeanDLRA/Integrators/Matrix/Defs.lean`
(the factored forms for matrices). The normal component of `F(t, Y)` at a point `Y` with
projections `P`, `Q` is `(1 - P) ((1 - Q) (F t Y))`. The factored forms bound
`(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)` for `U`, `V` with orthonormal columns and every
`S`; for invertible `S` this is the normal component at the rank-`r` matrix `U * S * Vᵀ`. The bound
`ε` is the model error in the error bounds above.

| Concept | Core | Relation (lemma) |
|---|---|---|
| Normal-component bound for a set `𝒯` of triples `(P, Q, Y)` on a region `D` | `NormalBoundOn F 𝒯 D ε` | defining; smaller sets, larger `ε`: `NormalBoundOn.mono`; one triple: `normalBoundOn_singleton_iff` |
| Factored bound at the rank-`r` points `U * S * Vᵀ` of a region `D` | `FactoredNormalBoundOn F r D ε` | the matrix case of `NormalBoundOn` with the triples `(leftProj U, rightProj V, U * S * Vᵀ)`: `factoredNormalBoundOn_iff_normalBoundOn`; smaller region, larger `ε`: `FactoredNormalBoundOn.mono` |
| Global factored bound | `MatrixBUG.FactoredNormalBound F r ε` | equivalent to the region form on `univ`: `factoredNormalBound_iff_univ`; implies the localized one: `nearNormalBound_of_factored` |
| Localized bound near `Y` on `[t₀, t₁]` | `NearNormalBound F r ε t₀ t₁ Y ρ` | equivalent to the region form on `Icc t₀ t₁ ×ˢ Metric.closedBall Y ρ`: `nearNormalBound_iff` |
