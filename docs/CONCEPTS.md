# Concept map

Which definitions of the library mean the same thing, which imply which, and which are
different (with a separating example). Every row names the Lean lemma that proves it. The first
sections cover the vocabulary of linear algebra and analysis, the later ones the integrators.

The local forms of the catalogue (definitions of single papers in `Literature/`,
`OpenProblems/`, `Novel/` and `Corrections/` that state a core notion in their own terms) and
their relation to the core are in [catalogue/CATALOGUE.md](catalogue/CATALOGUE.md), under the
same section names.

## Pseudoinverses

Core file: `LeanDLRA/LinearAlgebra/Factorization/Defs.lean`. Relations are Lean lemmas there or in
the named file; "equal" means the local definition had the same body (and the same binders) as the
core one and was replaced by it, with a deprecated alias left under the old name.

| Concept | Core | Relation (lemma) |
|---|---|---|
| Penrose equations `A G A = A`, `G A G = G`, `(A G)ᵀ = A G`, `(G A)ᵀ = G A` | `Matrix.IsMoorePenrose A G` | defining; at most one solution (`Matrix.IsMoorePenrose.unique`) |
| Moore–Penrose inverse `A⁺` | `Matrix.pinv A` (explicit: `W diag(λ⁺) Wᵀ Aᵀ` from `Aᵀ A = W diag(λ) Wᵀ`) | satisfies the equations (`Matrix.isMoorePenrose_pinv`); `A.IsMoorePenrose G ↔ G = A.pinv` (`Matrix.isMoorePenrose_iff_eq_pinv`) |
| Gram pseudoinverse `(Aᵀ A)⁻¹ Aᵀ` | `Matrix.gramPinv A` | **implies** under full column rank: `Matrix.isMoorePenrose_gramPinv`, `Matrix.gramPinv_eq_pinv` (`IsUnit (Aᵀ * A).det`, equivalently `A.rank = Fintype.card k` by `Matrix.isUnit_det_transpose_mul_self_iff`); exactly: `Matrix.gramPinv_eq_pinv_iff` (`gramPinv A = pinv A ↔ IsUnit (Aᵀ * A).det ∨ A = 0`) |
| `{1}`-inverse hypotheses `X G X = X` (`RandomizedBUG.dgn_exact`) | `Matrix.IsMoorePenrose.mul_pinv_mul` | implied by `IsMoorePenrose` (first Penrose equation) |

**Failed bridge (finding).** `Matrix.gramPinv A = Matrix.pinv A` is false without full column rank:
for `A = diag(1, 0)`, `Aᵀ A` is singular, Mathlib's `⁻¹` gives `0`, so `gramPinv A = 0`, while
`pinv A = A ≠ 0` (the last `example` of `LinearAlgebra/Factorization/Defs.lean`). Every use of the
Gram formula in the catalogue files of this section ([CATALOGUE.md](catalogue/CATALOGUE.md)) carries
a full-column-rank hypothesis (`IsUnit (Uᵀ * U).det` or `IsUnit (Kᵀ * K)`), so the two notions agree
wherever results are stated; `Matrix.gramPinv` stays a separate core definition because the papers
write the Gram formula.

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
| Galerkin projector `Z ↦ U Uᵀ Z V Vᵀ` | `LeanDLRA.galerkinProj U V = leftProj U * rightProj V` | defining (`galerkinProj_def`, `galerkinProj_apply`); orthogonal for orthonormal `U`, `V`: `isOrthProj_galerkinProj` |

**Failed bridge (finding).** `Matrix.colProj A = Matrix.rangeProj A` is false without full column
rank: for `A = diag(1, 0)`, Mathlib's `(Aᵀ A)⁻¹` is `0`, so `colProj A = 0`, while
`rangeProj A = A ≠ 0` (the last `example` of `LinearAlgebra/Factorization/Defs.lean`).

## SVD, truncation, tails and rank selection

Core file: `LeanDLRA/LinearAlgebra/Factorization/Defs.lean` (`Matrix.svdTrunc`, `tailSqSum` and
`IsBestLowRankApprox` are to move to `LinearAlgebra/SVD/Defs.lean` and
`LinearAlgebra/LowRank/Defs.lean` with unchanged statements). `epsRank`, `distLR`
(`LinearAlgebra/LowRank/Defs.lean`) and `WeylSingular.tailNorm` (`Classical/WeylSingular.lean`) are
existing core definitions.

| Concept | Core | Relation (lemma) |
|---|---|---|
| SVD `A = U diag(σ) Vᵀ` with `p` triplets, `U`, `V` orthonormal, `σ` antitone, `σ ≥ 0` | `Matrix.IsSVD A U σ V` (fields `orthU orthV antitone nonneg eq`) | defining |
| Truncation to the first `r` triplets `U diag(σ₀…σ_{r-1},0…) Vᵀ` | `Matrix.svdTrunc U σ V r` | defining; leading-column form `U_{:r} Σ_r V_{:r}ᵀ` for `r ≤ p`: `Matrix.svdTrunc_eq_submatrix` |
| Discarded weight `∑_{i ≥ r} σᵢ²` | `tailSqSum σ r` | defining |
| Best rank-`r` approximation (Frobenius) | `IsBestLowRankApprox r A X` (minimizer form) | defining; that the truncated SVD of an SVD is one is proved in the catalogue ([CATALOGUE.md](catalogue/CATALOGUE.md)) |
| Lower bound `ρ ≤ σ_{r-1}(U S Vᵀ)` from `ρ ‖w‖ ≤ ‖S w‖` for orthonormal `U`, `V` | `SVD.le_singularValues_of_eq_mul` (`LinearAlgebra/SVD/MinMax.lean`), from the max-min bound `LinearMap.le_singularValues_of_mul_norm_le` | converse of `WeylSingular.mul_norm_le_norm_toEuclideanLin_core` (module docstring) |
| Truncation of a matrix of rank at most `r` | `EckartYoung.truncation A r` | equals `A`: `EckartYoung.truncation_eq_self`; with `EckartYoung.rank_truncation_le` it gives `RandomizedBUG.truncation_eq_self_iff` |
| Derivative of `B ↦ truncation B r` at `A` with the gap `σ_r(A) < σ_{r-1}(A)` | `EckartYoung.hasFDerivAt_truncation`, `EckartYoung.hasDerivWithinAt_truncation` (`LinearAlgebra/SVD/TruncationDeriv.lean`) | the projector onto the top `r` right singular vectors is the only orthogonal projector with the properties of `EckartYoung.truncation_eq_mul_of_isOrthProjMat`, so the derivative is defined without a choice of vectors |
| Two perturbation bounds for singular subspaces | `norm_sub_le_of_isOrthProjMat` (`LinearAlgebra/SVD/TruncationDeriv.lean`: gaps on both sides, any orthogonal projectors that commute with `Aᵀ A`, `Bᵀ B`) and `SinTheta.wedin_frobenius`, `SinTheta.norm_truncation_sub_le_of_gap` (`LinearAlgebra/SVD/SinTheta.lean`: a gap on one side, singular vectors) | neither implies the other (module docstrings of both files) |
| Growth of `distLR r` along an exact solution | `distLR_flow_le_exp_mul_add` (`Matrix/LowRankDistance.lean`), `distLR_flow_le_sharp` (`Matrix/LowRankDistanceFlow.lean`), `distLR_flow_le_exp_of_tube` (`Integrators/Matrix/FlowDistance.lean`) | the second keeps the recorded form of the first (with continuity of the field in time); for a start of rank at most `r` both give `h ε e^{L h}`: `distLR_flow_le_exp`; the third is the form on a tube |

## QR and orthonormal frames

Core file: `LeanDLRA/LinearAlgebra/Factorization/Defs.lean`.

| Concept | Core | Relation (lemma) |
|---|---|---|
| Orthonormal frame capturing `X`: `Wᵀ W = 1`, `W Wᵀ X = X` | `Matrix.IsOrthCapture W X` | defining; `↔ Wᵀ W = 1 ∧ ∃ R, X = W R` (`Matrix.isOrthCapture_iff`) |
| Orthonormal basis of the column space: capture and `W = X C` | `Matrix.IsOrthBasisOf W X` | **implies** `IsOrthCapture` (`IsOrthBasisOf.isOrthCapture`); `W Wᵀ = rangeProj X` (`IsOrthBasisOf.mul_transpose_eq_rangeProj`) |
| Thin QR `K = Q R`, `Qᵀ Q = 1`, `R` upper triangular | `Matrix.IsQR K Q R` | **implies** `IsOrthCapture Q K` (`IsQR.isOrthCapture`); with invertible `R`, `IsOrthBasisOf Q K` (`IsQR.isOrthBasisOf`), hence `Q Qᵀ = rangeProj K` |
| `IsOrthBasisOf Û K` (`Research/SameMinibatchAugmentation.lean`: `Ûᵀ Û = 1 ∧ ∃ C, Û = K C`, same column count) | `Matrix.IsOrthBasisOf` | equal: `StochasticDescent.isOrthBasisOf_iff` (the capture follows because `Ûᵀ K C = 1` makes `C` invertible); replaced in `Research/SameMinibatchAugmentation.lean` and `Novel/MinibatchBias.lean` (no alias, see the file); `Û Ûᵀ = U' U'ᵀ` for `K = U' D` is `Matrix.IsOrthBasisOf.mul_transpose_eq_mul_transpose` (stated in the research file, to move to `LinearAlgebra/Factorization/Defs.lean`) |

**Separating example.** `Matrix.IsOrthCapture` does not imply `Matrix.IsOrthBasisOf`: `W = 1`
(2 × 2) captures `X = e₁` but its columns do not lie in the column space of `X`.

## Vocabulary of `Analysis/Defs.lean` and Mathlib's orthogonal projection

Core files: `LeanDLRA/Analysis/Defs.lean` (ODE solutions, conditions on fields, tubes, Euler
steps), `LeanDLRA/LinearAlgebra/Projection/Defs.lean`. All definitions were moved with their names
and types unchanged (hash 0).

| Concept | Core | Relation (lemma) |
|---|---|---|
| Mathlib's orthogonal projection `K.starProjection` onto a subspace with an orthogonal projection | `LeanDLRA.IsOrthProj` | implies: `LeanDLRA.isOrthProj_starProjection` (the private copy of `Dynamics/ContinuousDLRA.lean` is removed) |
| `MeanSquare.isOrthProj_starProjection` (`Stochastic/MeanSquare.lean`) | `LeanDLRA.isOrthProj_starProjection` | same statement; duplicate, to be removed |
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
| Lipschitz bound of `Y ↦ tangentProjAt Y` between matrices of rank `r`, with `ρ ≤ σ_{r-1}(X)` | `norm_tangentProjAt_sub_le`, `norm_tangentProj_sub_tangentProjAt_le` (`FixedRank/TangentSpace/Curvature.lean`) | the constant `2 ρ⁻¹` of `Curvature.koch_lubich_tangent_frob`, stated at a matrix instead of for factors; the lower bound is needed at one of the two points only |
| Lipschitz bound of `Y ↦ tangentProjAt Y` with the constant `1` instead of `2` | `norm_tangentProjAt_sub_le_inv_mul`, `norm_tangentProj_sub_tangentProjAt_le_inv_mul`, `Curvature.norm_tangentProjMat_sub_le_inv_mul` (`FixedRank/TangentSpace/ProjectorLipschitz.lean`) | `‖P(Y) B - P(X) B‖ ≤ ρ⁻¹ ‖Y - X‖ ‖B‖` with `ρ ≤ σ_{r-1}(X)`; **implies** `norm_tangentProj_sub_tangentProjAt_le` (restated in an `example` of the file); the third is the factor form of the first; the constant `1` is attained (an `example` of the file has equality) |
| Tangent projector at `X` on a vector that is normal at `Y`, and the converse | `norm_tangentProjAt_apply_le_of_tangentProjAt_eq_zero`, `norm_tangentProj_apply_le_of_tangentProjAt_eq_zero` (`FixedRank/TangentSpace/ProjectorLipschitz.lean`) | the two bounds `‖P(X) N‖ ≤ ρ⁻¹ ‖Y - X‖ ‖N‖` (`P(Y) N = 0`) and `‖P(Y) N‖ ≤ ρ⁻¹ ‖Y - X‖ ‖N‖` (`P(X) N = 0`); the Lipschitz bound is the orthogonal sum of the two |
| The same with the spectral norm `‖N‖₂ = specNorm N` of the normal vector | `norm_tangentProjAt_apply_le_one_add_mul_specNorm_of_tangentProjAt_eq_zero`, `norm_tangentProjAt_apply_le_sqrt_two_mul_specNorm_of_tangentProjAt_eq_zero` (`FixedRank/TangentSpace/ProjectorSpectral.lean`) | factors `ρ⁻¹ ‖Y - X‖ (1 + ρ⁻¹ ‖Y - X‖)` and `√2 ρ⁻¹ ‖Y - X‖`; not the same bound as with `‖N‖` in the Frobenius norm: with `‖N‖₂` the constant `1` does not hold for all `Y` (the family of examples is not formalized in the core) |
| Velocity of a curve of rank-`r` matrices; first-order optimality of a best approximation | `mem_tangentSpaceAt_of_hasDerivWithinAt`, `tangentProjAt_sub_eq_zero_of_forall_norm_sub_le`, `tangentProjAt_truncation_sub_eq_zero` | the derivative lies in `tangentSpaceAt`; `P(X) (A - X) = 0` for a best approximation `X` and for the truncated SVD |
| Distance to the matrices of rank at most `r` after an explicit tangent step | `tailNorm_add_tangent_le` (`FixedRank/TangentStepTruncation.lean`) | `WeylSingular.tailNorm (U S Vᵀ + Z) r ≤ ‖Z‖² / ρ` for a tangent `Z`; `tailNorm` is `distLR` (`WeylSingular.tailNorm_eq_infDist`) |

### Tangent objects of other manifolds (not replaced; named for orientation)

| Object | Manifold | Relation to the matrix objects |
|---|---|---|
| `Tensor.tuckerTangentProj`, `modeTangentProj`, `Tensor.ttTangentSum`, `Tensor.ttTangentProj` (tensor core) | Tucker, tensor train | built from mode or interface projectors like `tangent L R`; see the section "Tensor step vocabulary" |
| Lipschitz constant of `Tensor.tuckerTangentProj` and of `Tensor.ttTangentProj` | Tucker, tensor train | Tucker: `Tensor.norm_tuckerTangentProj_sub_le` with `√d`, lower bound `23 / 20` for `d = 3` (`Tensor.exists_mul_le_norm_tuckerTangentProj_sub`), rank one `√(2 (d - 1) / d)` (`Tensor.norm_tuckerTangentProj_sub_le_of_unique`, attained); tensor train: `Tensor.norm_ttTangentProj_sub_le` with `2`; for `d = 2` the rank-one constant is `1` as for `tangentProjAt` |
| Normal component of a nearby tensor | Tucker, tensor train | `Tensor.norm_sub_tuckerTangentProj_tucker_le`, `Tensor.norm_sub_ttTangentProj_tt_le`: `e² / √(2 ρ (ρ - 2 e))`, no dependence on `d`; for matrices the second-order bound is `norm_one_sub_tangentProjAt_apply_sub_le` |

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
| Tolerance rank of the singular values `min {r : τ_r(X) ≤ ε}` | `epsRank ε X` (distance form) | equal: `WeylSingular.epsRank_eq_sInf_tailNorm` |
| Rank of a tolerance truncation is monotone in the Loewner order | `LoewnerRank.epsRank_le_epsRank_of_posSemidef`, `LoewnerRank.distLR_le_distLR_of_posSemidef` (`Research/LoewnerRank.lean`) | for `0 ⪯ Y ⪯ X`; along a truncated backward Euler run for a Lyapunov equation: `LoewnerRank.rank_le_epsRank_of_truncated_lyapunov_run` |
| Rank sandwich of a tolerance truncation: for a stationary iteration, and for a time-stepping sequence with reconstruction errors `η_k` | `epsRank_sandwich` (Bachmayr–Dahmen), `DynamicRecompression.norm_sub_le_and_epsRank_le_rank_and_rank_le_epsRank` (`Research/DynamicRecompression.lean`) | the second has the error `θ + η_k + E_{k+1}` and the rank between the `(θ + ζ_k)`-rank and the `(θ - ζ_k)`-rank of the exact value |
| Rank freeze: iterates of a tolerance truncation at a fixed tolerance | `DynamicRecompression.rank_le_rank_zero_of_forall_norm_sub_le`, `DynamicRecompression.distLR_le_norm_sub_of_forall_norm_sub_le` | if `‖Z k - Y k‖ ≤ ϑ` the rank does not grow and the error stays above the distance to the matrices of the initial rank; the error `k ϑ` is attained: `DynamicRecompression.exists_stepTruncation_norm_sub_eq_mul` |
| Method that uses the field only on matrices of rank at most `k`: lower bound, and the bound of a full-state method | `InformationLowerBound.half_norm_sub_le_max_error`, `InformationLowerBoundExample.mul_integral_distLR_le_max_error`, `RankInformationUpperBound.norm_sub_le_exp_mul_add_integral_distLR` | worst-case error at least `L ∫ distLR k (A s)` for one of two `L`-Lipschitz fields that agree on the matrices of rank at most `k`; the output `A 0 + T B` attains it (`InformationLowerBound.norm_sub_affine_le_integral_distLR`); the full-state method is within `e^{2 L T}`; linear fields are excluded: `InformationLowerBound.linearMap_ext_of_rank_le_one` |
| Error of a state of rank `r` along turning tangent spaces, and of a state of rank `k > r` truncated to `r` | `RankStatePriceExample.dlra_error_eq_mul_sqrt`, `RankStatePrice.norm_sub_le_distLR_add_two_mul_of_isDLRASolution` | `ε √(1 + t²)` against `distLR 1 ≤ ε`; the truncation of the state of rank `k` adds twice its error (`RankInformationUpperBound.norm_sub_le_distLR_add_two_mul`) |
| Global factored normal-component bound | `MatrixBUG.FactoredNormalBound F r ε` | implies the localized one: `nearNormalBound_of_factored`; satisfied with `ε = 0` by the identity field (`example`, `Integrators/Matrix/Defs.lean`) |
| Localized bound near `Y` on `[t₀, t₁]` | `NearNormalBound F r ε t₀ t₁ Y ρ` | defining; equivalent to the region form `FactoredNormalBoundOn` on `Icc t₀ t₁ ×ˢ Metric.closedBall Y ρ`: `nearNormalBound_iff` (section "Normal-component bounds on regions") |

## Runge–Kutta tableaux and the `φ`-functions

Core file: `LeanDLRA/Analysis/Defs.lean`: `ButcherTableau R s` (arrays `a`, `b`, `c` over any coefficient
ring `R`), `ButcherTableau.IsExplicit`, `ButcherTableau.IsRowSum`, the tableaux `euler`, `rk4`,
`ssprk104` (generic in `R`, so the same tableau serves the order conditions over `ℚ` and the steps over
`ℝ`), and `LeanDLRA.phi1`, `LeanDLRA.phi2` (`φ₁(z) = (eᶻ - 1)/z`, `φ₂(z) = (eᶻ - 1 - z)/z²`, with
their limits at `0`). The core step structures of `HighOrder/RungeKuttaBUG.lean` keep their raw
arguments `a b c`; a tableau `T` enters as `T.a T.b T.c`.

## Weighted norms

Core file: `LeanDLRA/LinearAlgebra/Frobenius/Defs.lean`. `WeightedMatrix wx wv` is `Matrix m n ℝ` as a
type synonym carrying the weighted inner product `Frobenius.weightedInner wx wv`
(`WeightedMatrix.inner_def`); for positive weights (instances `Fact (∀ i, 0 < wx i)`,
`Fact (∀ j, 0 < wv j)`) it is a real inner product space, so every abstract inner-product theorem
applies to discrete weighted `L²` norms (`WeightedMatrix.norm_sq_eq`: `‖X‖² = ∑ wxᵢ wvⱼ Xᵢⱼ²`).
`WeightedMatrix.toFrobenius : WeightedMatrix wx wv ≃ₗᵢ[ℝ] Matrix m n ℝ`, `X ↦ diag(√wx) X diag(√wv)`,
is the isometry to the Frobenius space (`inner_toFrobenius`, `norm_toFrobenius`; built from
`Frobenius.weightedInner_eq_inner`). Conversions: `toWeighted`, `ofWeighted` (identities).

## Duplicate lemmas and remaining frames

| Concept | Core | Relation (lemma) |
|---|---|---|

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
| Federated round with two local steps | `fedRound P gc g lr 2 x` | two projected gradient steps of the global loss if `g` is the average of the `gc c`: `fedRound_two_eq_projGradStep` (`Research/FederatedTwoSteps.lean`) |

## Tensor step vocabulary

Core files: `LeanDLRA/Tensor/Defs.lean` (`TreeShape`, `TTNFrame`, `modePrefix`,
`Tensor.ttTangentSum`, `IsTTNAugRecoverable`), `LeanDLRA/Tensor/Steps.lean` (`kslModeField`,
`IsTuckerKSLStep`, `IsExactKSteps`, `IsTTNKSLStep`, `IsTTNBUGStep`, `IsAugTTNBUGStep`,
`IsParTTNBUGStep`, `IsTTNRecoverable`, `modeTangentProj`), the folder
`LeanDLRA/Tensor/TTN/Abstract/` (the theorems about the step predicates, on a real inner product
space), `LeanDLRA/Tensor/Tucker/Tangent.lean` and `LeanDLRA/Tensor/TT/TangentProjector.lean`.
`Tensor/Steps.lean` is not a definitions file: the step predicates use `modeProd`, `modeProdLeOne`,
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
| Alternating sum of interface operators of a tensor train | `Tensor.ttTangentSum` (`Tensor/Defs.lean`) | projector properties: `Tensor.ttTangentSum_idem`, `Tensor.ttTangentSum_isOrthProj`, `Tensor.ttTangentSum_isObliqueProj` (`Tensor/TT/TangentProjector.lean`), used by `Tensor.isOrthProj_ttTangentProj`; two catalogue copies are bridged to it ([CATALOGUE.md](catalogue/CATALOGUE.md)) |
| Commutation of the admissible mode operators of a child with its co-range projector | `TTNFrame.IsCoRangeCommuting` (`Tensor/TTN/Defs.lean`) | holds for the frame of every basis frame on tensors: `DimTree.BasisFrame.isCoRangeCommuting_toTTNFrame`; under it the factor `s` of `ttn_global_error_le` becomes `√(s - 1)` for the `ε`-term: `ttn_global_error_le_sqrt`, `DimTree.BasisFrame.bug_global_error_sqrt` (never larger, since `√(s - 1) ≤ s`); attained on a star: `SqrtNodesExample.norm_sub_starFrame_exact` |
| Multilinear product `C ×₁ U₁ ⋯ ×_d U_d` | `Tensor.tucker` (`Tensor/Defs.lean`) | defining; on three modes it is bridged to a catalogue copy ([CATALOGUE.md](catalogue/CATALOGUE.md)) |
| One step of the tensor-train projector-splitting integrator | `Tensor.IsTTKSLStep` (`Tensor/TT/ProjectorSplitting.lean`) | exactness `Tensor.IsTTKSLStep.exact` and the increment form `Tensor.IsTTKSLStep.eq_add_ttTangentProj` (`Tensor/TT/ProjectorSplittingExactness.lean`), robust error `Tensor.IsTTKSLStep.local_error`, `Tensor.tt_ksl_global_error` (`Tensor/TT/ProjectorSplittingError.lean`); it is not a step `IsTTNKSLStep` of the linear tree (every inner node of the latter has an additional backward substep) |

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

## DLRA solutions and the equations for the factors

Core files: `LeanDLRA/DLRA/Defs.lean` (`IsDLRASolution`) and `LeanDLRA/DLRA/DynamicallyOrthogonal.lean`
(the three systems of equations for the factors and their relation to `IsDLRASolution`); the product
rule for the factors is in `LeanDLRA/Matrix/GaugeODE.lean`. A DLRA solution is a solution of the
projected equation `Y' = P(Y) F(t, Y)`, `P(Y) = tangentProjAt Y`, with rank exactly `r` on the
closed interval. The factor systems are the dynamically orthogonal (DO) system for `Y = U Zᵀ` with
`Uᵀ U = 1`, its dual (DDO) for `Y = Z Vᵀ` with `Vᵀ V = 1`, and the bi-orthogonal (BO) system with
`Zᵀ Z = 1`.

| Concept | Core | Relation (lemma) |
|---|---|---|
| Solution of the projected equation with rank `r` on `[a, b]`: an `ODESolution` of `fun t x => tangentProjAt x (F t x)` with `(Y t).rank = r` on `Icc a b` | `IsDLRASolution r F Y a b` | defining; the rank condition at `b` is part of it; for factors of full column rank `U`, `Z` it is equivalent to continuity on `[a, b]` and the right derivative `tangentProjAt (Y t) (F t (Y t))` on `[a, b)`: `DynamicallyOrthogonal.isDLRASolution_iff_hasDerivWithinAt` |
| Right derivative of a DLRA solution through an orthonormal factorization `Y t = Q S Vᵀ`, `S` invertible | `tangentProj Q V (F t (Y t))` | `DynamicallyOrthogonal.IsDLRASolution.hasDerivWithinAt_tangentProj`; conversely from such factorizations at every `t ∈ [a, b)` and rank `r` at `b`: `DynamicallyOrthogonal.isDLRASolution_of_factorization` |
| DO system `Uᵀ U̇ = 0`, `Ż = (F t Y)ᵀ U`, `U̇ (Zᵀ Z) = (1 - U Uᵀ) F t Y Z` | none (stated as hypotheses and conclusions) | equivalent to `IsDLRASolution r F (fun t => U t * (Z t)ᵀ) a b` together with the gauge `Uᵀ U̇ = 0` on `[a, b)`: `DynamicallyOrthogonal.doSystem_iff_isDLRASolution`; pointwise: `DynamicallyOrthogonal.hasDerivWithinAt_do_iff`, `DynamicallyOrthogonal.hasDerivAt_do_iff` |
| DDO system for `Y = Z Vᵀ` | none | `DynamicallyOrthogonal.ddoSystem_iff_isDLRASolution`; pointwise: `DynamicallyOrthogonal.hasDerivWithinAt_ddo_iff` |
| BO factors `U`, `Z` with `Zᵀ Z = 1`, skew `Ω`, `U̇ = F Z + U Ω`, `Ż = Z Ω + (1 - Z Zᵀ) Fᵀ U (Uᵀ U)⁻¹` | none | imply `IsDLRASolution r F (fun t => U t * (Z t)ᵀ) a b`: `DynamicallyOrthogonal.isDLRASolution_of_bo`; the converse is not stated in the core |
| Tangent projector at `U Zᵀ` for factors of full rank | `tangentProjAt` | `DynamicallyOrthogonal.tangentProjAt_mul_transpose_apply : P(Y) A = Π_U A + A Π_Z - Π_U A Π_Z` with the Gram projectors `Matrix.colProj`; the transpose commutes: `DynamicallyOrthogonal.tangentProjAt_transpose`; rank of `U Zᵀ`: `DynamicallyOrthogonal.rank_mul_transpose` |
| Existence and uniqueness of a DLRA solution of rank `r` from `Y₀` with `B (b - a) < σ_{r-1}(Y₀)` | `exists_isDLRASolution`, `IsDLRASolution.eqOn` (`DLRA/Existence.lean`) | in factored form `exists_factors_isDLRASolution`; the converse `IsDLRASolution.exists_factors`; the solution of the factor equations is a DLRA solution of rank `r` |
| Distance of a DLRA solution `Y` from a curve `X` of critical points of the distance to `A` | `IsDLRASolution.norm_sub_le_integral` (`DLRA/QuasiOptimality.lean`) | same conclusion as `dlra_norm_sub_le_integral`, which takes an `ODESolution` of `tangentProj (U t) (V t) (F t x)` with factors; `dlra_norm_sub_truncation_le_integral` is the case `F t Y = Ȧ t`, `X t = truncation (A t) r`; the forms for a field that is Lipschitz on a tube and for the truncation under a gap are in `DLRA/QuasiOptimalityTube.lean` and `DLRA/QuasiOptimalityGap.lean` |
| Margin `‖X - A‖ ≤ ρ / 4` and margin `θ ρ` in the quasi-optimality bound | `IsDLRASolution.norm_sub_le_integral`, `IsDLRASolution.norm_sub_le_integral_of_margin` (`DLRA/QuasiOptimalityMargin.lean`) | the second, with `θ = 1 / 4`, is the first (examples at the end of the file); the second needs `2 * θ < 1`; constants `L + 2 * μ / ρ + κ` and `L + κ` with `κ = 2 * μ / ((1 - 2 * θ) * ρ)` |
| Margin `θ ρ` with `θ < 1` in the quasi-optimality bound | `IsDLRASolution.norm_sub_le_integral_of_margin_lt_one`, `dlra_norm_sub_le_integral_of_margin_lt_one` (`DLRA/QuasiOptimalityNormal.lean`) | **implies** the bound of `DLRA/QuasiOptimalityMargin.lean` for `2 * θ < 1` (restated in an `example`); constants `L + κ` and `L + μ / ρ + κ` with `κ = μ / ((1 - θ) * ρ)`; the constant `1` of `norm_tangentProjAt_sub_le_inv_mul` replaces the `2` |
| The forms of the bound with the margin `ρ / 4`: error against `A`, curve of best approximations, tube, truncation under a gap | `dlra_norm_sub_le_add_integral_of_margin_lt_one`, `IsDLRASolution.norm_sub_le_integral_of_forall_norm_sub_le_of_margin_lt_one`, `IsDLRASolution.norm_sub_le_integral_of_isLipschitzOnTube_of_margin_lt_one`, `IsDLRASolution.norm_sub_truncation_le_integral_of_gap_of_margin_lt_one` (`DLRA/QuasiOptimalitySharp.lean`) | each **implies** the theorem of `DLRA/QuasiOptimality.lean`, `DLRA/QuasiOptimalityTube.lean` or `DLRA/QuasiOptimalityGap.lean` with the same hypotheses and margin `θ ρ`, `θ < 1` (restated in `example`s with `θ = 1 / 4`) |
| Lipschitz constant of the projected field `Y ↦ P(Y) F(t, Y)` | `norm_tangentProjAt_field_sub_le_inv_mul` (`DLRA/QuasiOptimalitySharp.lean`) | `B / ρ + L` for `F` that is `L`-Lipschitz and bounded by `B`, from the constant `1` of the projector in place of `2` |
| Truncated SVD as a curve against the DLRA solution: margin `ρ / 16`, `θ ρ`, `ρ / 2` | `dlra_norm_sub_truncation_le_integral`, `dlra_norm_sub_truncation_le_integral_of_margin_lt_one`, `dlra_norm_sub_truncation_le_integral_of_norm_sub_le_half` (`DLRA/QuasiOptimality.lean`, `DLRA/QuasiOptimalityTruncation.lean`) | the third **implies** the first (and the recorded matrix form of the theorem): `ρ / 16 ≤ ρ / 2`, `2 μ / ρ ≤ 16 μ / ρ`, `3 μ / ρ ≤ 8 μ / ρ`; the third is the second for `θ = 1 / 2` |
| Frobenius norm and spectral norm of the tail in the quasi-optimality bound | `IsDLRASolution.norm_sub_le_integral_of_specNorm_sub_le`, `dlra_norm_sub_truncation_le_integral_of_specNorm_sub_le` (`DLRA/QuasiOptimalitySpectral.lean`) | margin `‖X - A‖₂ ≤ θ ρ` and integrand `‖X - A‖₂` in place of the Frobenius norm; since `‖·‖₂ ≤ ‖·‖` the bounds of `DLRA/QuasiOptimalityNormal.lean` follow (two are restated in `example`s); exponent `L + μ / ρ` without the term `κ`, the Lipschitz term keeps `‖X - A‖` |
| Tail of the truncated SVD, spectral norm | `EckartYoung.specNorm_sub_truncation`, `dlra_norm_sub_truncation_le_integral_of_singularValues_le` (`Classical/EckartYoung.lean`, `DLRA/QuasiOptimalitySpectral.lean`) | `‖truncation A r - A‖₂ = σ_r(A)` (indices from zero), so the margin is `σ_r(A t) ≤ θ ρ` and the integrand is `σ_r(A s)`; the second follows from `dlra_norm_sub_truncation_le_integral_of_specNorm_sub_le` and the first |
| Rank and singular values of `truncation A r` under `ρ ≤ σ_{r-1}(A)` | `EckartYoung.rank_truncation_of_le_singularValues`, `EckartYoung.le_singularValues_truncation`, `EckartYoung.exists_truncation_eq_mul_diagonal_mul_transpose` (`DLRA/QuasiOptimality.lean`) | the truncation is `U diag(σ) Vᵀ` with `σ i ≥ ρ`; hence rank `r` and `ρ ≤ σ_{r-1}(truncation A r)` |
| Growth rate of the quasi-optimality bound: the whole velocity `μ`, or only its normal component `ν` | `IsDLRASolution.norm_sub_le_integral_exp_integral_of_integral_lt` (`DLRA/QuasiOptimalityNormalVelocity.lean`) | rate `L + ν / ρ + ν / (ρ - ε) + μ ε / ρ²` in place of `L + μ / ρ`, in a tube of radius `ε < ρ` that the bound itself stays below; the source is `L ‖X - A‖ + d`, `d` the defect of the curve `X`; the pairing of the two tangent projectors is `inner_sub_tangentProjAt_sub_le_norm_sq_mul` |
| Defect `P(X) Ȧ - Ẋ` of the truncated SVD | `tangentProjAt_sub_eq_neg_pinv_transpose_mul_add_of_hasDerivWithinAt`, `norm_sub_tangentProjAt_le_div_sub_mul_norm_pinv_transpose_mul_add` (`DLRA/QuasiOptimalityDefect.lean`) | `P(X)(Ȧ - Ẋ) = -W(Ẋ)` with the Weingarten map `W(Z) = (X⁺)ᵀ Zᵀ R + R Zᵀ (X⁺)ᵀ`; the defect is between `‖W(Ȧ)‖ / (1 + τ / ρ)` and `‖W(Ȧ)‖ / (1 - τ / ρ)`; the bound `μ τ / (ρ - τ)` of `DLRA/QuasiOptimalityTimeLocal.lean` follows |
| Normal components in the Frobenius norm and in the spectral norm in the pairing of the two tangent projectors | `inner_sub_tangentProjAt_sub_le_norm_sq_mul`, `inner_sub_tangentProjAt_sub_le_half_mul_specNorm` (`DLRA/QuasiOptimalityNormalVelocity.lean`, `DLRA/QuasiOptimalityNormalVelocitySpectral.lean`) | the second has spectral norms and the factor `(1 + s) / 2`, `s` the product of the sines of the largest angles between the column spaces and between the row spaces, `s ≤ 1`; with `s = 1` and `‖·‖₂ ≤ ‖·‖` the other follows |
| Constants `ρ`, `μ` on the interval and functions of time `ρ(t)`, `μ(t)` | `IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_singularValues_lt` (`DLRA/QuasiOptimalityTimeLocal.lean`) | the form with constants is an `example` of the file; the rate is `L + μ(t) / σ_{r-1}(A t)` |
| Field `F = S + G` with `S` tangential | `IsDLRASolution.norm_sub_le_integral_exp_integral_of_tangent_add_of_integral_lt` (`DLRA/QuasiOptimalityStiff.lean`) | the rate has the one-sided constant `ℓ` of `F` in place of `L` and the term `L ε / ρ`; for `S = 0` it is the rate of `DLRA/QuasiOptimalityNormalVelocity.lean` with `ℓ` in place of `L`, plus the term `L ε / ρ` |
| Velocity of `U Σ Yᵀ` with factor velocities written with a gauge `A` and a skew `B` | `Literature.P2503_18271.tdb_velocity_gauge_free` (`DLRA/GaugeInvariance.lean`) | equals `tangentProj U Y M`, so it does not depend on the gauge; the factor equations of the DO system are the case `A = B = 0` |

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
| Grönwall with a time-dependent rate `k`, from `‖f'‖ ≤ k ‖f‖ + g`, or from `⟪f, f'⟫ ≤ (k ‖f‖ + g) ‖f‖` | `norm_le_exp_integral_mul_add_integral_exp_integral_mul`, `norm_le_exp_integral_mul_add_integral_exp_integral_mul_of_inner_le` (`Analysis/GronwallVariableRate.lean`, `Analysis/GronwallInner.lean`) | same conclusion `‖f x‖ ≤ e^{∫ k} δ + ∫ e^{∫ₛ k} g`; the second needs `0 ≤ g` and an inner product space and follows from the other when `‖f'‖ ≤ k ‖f‖ + g`; constant rate: `gronwallBound` |
| Two-sided enclosure of the error of a run by a companion with a certified bound `β` | `abs_norm_sub_sub_norm_sub_le_of_norm_sub_le` (`Stiff/CompanionEnclosure.lean`) | `|‖Y - A‖ - ‖Y - Y'‖| ≤ β`; `β` from residuals: `abs_norm_sub_sub_norm_sub_le_of_implicitEuler`; from a defect bound: `abs_norm_sub_sub_norm_sub_le_of_defect_steps` |
| Implicit midpoint step as a reflection at the backward Euler value, `2 W - Y` | `ImplicitMidpointBUGStiff.sq_norm_two_smul_sub_add_le_of_backwardEuler`, `ImplicitMidpointBUGStiff.norm_sub_le_add_sum_of_implicitMidpoint` (`Research/ImplicitMidpointBUGStiff.lean`) | the reflection does not increase the norm; run bound with the factor one on the start error |

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
`LeanDLRA/Integrators/Matrix/ParallelBUG.lean`, that of the fourth in
`LeanDLRA/Integrators/Matrix/EulerBUGStep.lean`; the fifth uses `MatrixBUG.IsRankAdaptiveStep` of `LeanDLRA/Integrators/Matrix/BUG.lean`. A step
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
| BUG with augmented bases and truncation by a tolerance `ϑ` (rank-adaptive) | `MatrixBUG.adaptiveStepRel F R ϑ` | from an augmented step: `MatrixBUG.augmentedRel.adaptiveStepRel`; local error on a tube: `MatrixBUG.adaptiveStepRel.hasLocalError_of_tube`; runs: next section |
| BUG with augmented bases and truncation to rank `r` | `MatrixBUG.truncStepRel F r κ` (`∃ Yh, augmentedRel F r t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧ ‖Y₁ - Yh‖ ≤ κ * distLR r Yh`) | every augmented step can be completed for `1 ≤ κ`: `MatrixBUG.augmentedRel.exists_truncStepRel`; rank: `MatrixBUG.truncStepRel.rank_le`; step near the solution: `MatrixBUG.truncStepRel_tubeExt_iff_of_near`; local error on a tube: `MatrixBUG.truncStepRel.hasLocalError_of_tube` |
| Truncated BUG is tube-local; existence of a run and error bound | `MatrixBUG.isTubeLocal_truncStepRel`, `MatrixBUG.trunc_exists_run_norm_sub_le` (`Integrators/Matrix/TruncBUGRun.lean`) | instance of `StepMethod.IsTubeLocal` with `κ = 4` (the margin constant; the factor of the truncation is a different `κ`) and `Adm Y = (Y.rank ≤ r)`; bound `Real.exp (L * T) * δ + T * Real.exp (L * T) * (κ * (10 * L * B * h + ε) + (1 + κ) * (bugC₁ L H * ε + bugC₂ L B H * h))` under `… + 4 * B * h < ρ`, `h ≤ H`, `1 ≤ κ`; every run: `MatrixBUG.IsRun.norm_sub_le_of_truncStepRel` |
| Midpoint BUG step in projector form | `MidpointBUG.IsMidpointBUGStep` (`HighOrder/MidpointBUG.lean`) | defined on a general state space; the error bound of the older form is `midpointBUG_global_error_le` |
| Midpoint BUG step at the level of factors, without truncation | `MatrixMidpointBUG.IsStep` (`HighOrder/Defs.lean`) | a step in the sense of the previous row: `MatrixMidpointBUG.IsStep.isMidpointBUGStep`, with `leftProj U₀`, `rightProj V₀`, `leftProj Uh`, `rightProj Vh`, `galerkinProj Ub Vb` |
| Midpoint BUG, augmented step relation (result of rank at most `4 r`) and with truncation to rank `r` | `MatrixMidpointBUG.augmentedRel F r`, `MatrixMidpointBUG.stepRel F r` (`∃ Yh, augmentedRel F r t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧ ‖Y₁ - Yh‖ ≤ distLR r Yh`) | from a factor step: `MatrixMidpointBUG.IsStep.augmentedRel`; local errors `MatrixMidpointBUG.augmentedRel.hasLocalError`, `MatrixMidpointBUG.stepRel.hasLocalError` (`HighOrder/MidpointBUGStep.lean`) |
| Midpoint BUG with fixed rank is tube-local; existence of a run and error bound | `MatrixMidpointBUG.isTubeLocal_stepRel`, `MatrixMidpointBUG.exists_run_norm_sub_le` (`HighOrder/MidpointBUGRun.lean`) | instance of `StepMethod.IsTubeLocal` with `κ = 2`; the run theorem uses `StepMethod.IsTubeLocal.mono` with `κ = 3`; the bound holds for every run: `MatrixMidpointBUG.IsRun.norm_sub_le` |
| Implicit BUG step at the level of factors; step relation | `MatrixImplicitBUG.IsStep`, `MatrixImplicitBUG.stepRel F r` (`Stiff/Defs.lean`) | a step in the sense of `IsMatrixImplicitBUGStep` with capture tolerance `0` and no truncation: `MatrixImplicitBUG.IsStep.isMatrixImplicitBUGStep` (`Stiff/ImplicitBUGStep.lean`); the stages are the limits of the fixed-point iterations from the start values, and for a globally `L`-Lipschitz field with `h L < 1` these conditions follow from the stage equations: `MatrixImplicitBUG.IsStep.of_lipschitz`; existence: `MatrixImplicitBUG.exists_stepRel` |
| Implicit BUG on matrices: local error on a tube; runs | `MatrixImplicitBUG.IsStep.hasLocalError_of_tube` (`Stiff/ImplicitBUGStep.lean`), `MatrixImplicitBUG.exists_run_norm_sub_le`, `MatrixImplicitBUG.IsRun.norm_sub_le` (`Stiff/ImplicitBUGRun.lean`) | not an instance of `StepMethod.IsTubeLocal` (a backward Euler stage need not exist for `h L ≥ 1`); the run bound `Real.exp (L * T) * δ + T * Real.exp (L * T) * ((14 * L * B + 8 * Lt) * h + 6 * ε)` contains `L`, so it is not a bound for stiff fields |
| Run theorem with `e^{L T}` and with `e^{ℓ T}`, `ℓ` a one-sided Lipschitz constant on the tube | `StepMethod.IsTubeLocal.exists_run_norm_sub_le`, `StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_oneSided` (`Integrators/MethodOneSided.lean`) | the second is the first with `ℓ = L` (example at the end of `Integrators/MethodOneSided.lean`); for `ℓ < 0`: `…_of_oneSided_neg`, bound `Real.exp (ℓ * (n * h)) * δ + (h - ℓ⁻¹) * c`; for the BUG integrator `MatrixBUG.exists_run_norm_sub_le_of_oneSided` (`Integrators/Matrix/BUGRunOneSided.lean`) |
| Local error of the BUG step with `2 L B h` and `√2` | `IsBUGStep.local_error_two_mul` (`Integrators/BUGCapture.lean`) | same hypotheses as `IsBUGStep.local_error`; `kstep_capture_two_mul` is `kstep_capture` with `2 L B h` in place of `4 L B h`; the constants `c₁`, `c₂` are at most `bugC₁ L H`, `bugC₂ L B H`: `bugConstants_two_mul_le` |
| Rank-adaptive step from a padded start, two-sided term | `AugmentationRank.error_le_of_twoSided_of_leaks_eq_zero` (`Research/TwoSidedPadded.lean`) | the padded factors `Ũ S̃ Ṽᵀ` equal `U₀ S₀ V₀ᵀ` (`AugmentationRank.mul_paddedCoeff_mul_transpose_eq`) and have vanishing weighted leaks; the product `ℓ_C ℓ_D` of the unweighted leaks remains |
| Auxiliary flows `P`, `Q` of a Sylvester field `𝒜 Y + Y ℬ` | `AugmentationRank.exists_rightFactor_of_sylvester`, `AugmentationRank.exists_leftFactor_of_sylvester` (`Research/SylvesterFlows.lean`) | they are the hypotheses of `AugmentationRank.capture_of_sylvester` and `AugmentationRank.error_le_of_sylvester`; `…_of_continuousOn` drops them for continuous coefficients |
| Explicit midpoint step in bases with `2 r` columns, without truncation and with truncation to rank `r` | `ExplicitMidpoint.augmentedRel F r`, `ExplicitMidpoint.stepRel F r` (`HighOrder/Defs.lean`) | the second is the result of the first followed by a best approximation of rank at most `r` (`∃ Yh, augmentedRel F r t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧ ‖Y₁ - Yh‖ ≤ distLR r Yh`); a step exists from every matrix of rank at most `r` if `2 r` is at most the matrix sizes: `ExplicitMidpoint.exists_stepRel` |
| Explicit midpoint method is tube-local; existence of a run and error bound | `ExplicitMidpoint.isTubeLocal_stepRel`, `ExplicitMidpoint.exists_run_norm_sub_le` (`Research/ExplicitMidpointRun.lean`) | instance of `StepMethod.IsTubeLocal` with `κ = 2`; bound `Real.exp (L * T) * δ + T * Real.exp (L * T) * (C₁ * h ^ 2 + C₂ * ε)`; the field is of class `C²` as for the midpoint BUG integrator, with the normal bound at rank `r` only; every run: `ExplicitMidpoint.IsRun.norm_sub_le` |
| Capture defect `θ` of the explicit midpoint step | `norm_capture_defect_le` (free parameter `τ`) and `norm_capture_defect_le_sq_add` (`τ = h² + ε`, `Research/ExplicitMidpointCapture.lean`) | the second is the first with this choice; `ExplicitMidpoint.norm_update_sub_le_cube_add` (`Research/ExplicitMidpointGalerkin.lean`) inserts it into `ExplicitMidpoint.norm_update_sub_le` |

| BUG step for given data `Y₁ = P₁ (Y₀ + (A₁ - A₀)) Q₁` | `MatrixBUG.projStep_eq_add_sub` (`Integrators/Matrix/BUGQuasiOptimality.lean`) | `Y₁ = Y₀ + D - (1 - P₁) D (1 - Q₀) - P₁ (1 - P₀) D (1 - Q₁)`, `D = A₁ - A₀`; `DataDriven.bug_err_succ` (`Research/DataDrivenErrorRecursion.lean`) is the same identity for projectors given as operators |
| Error of the BUG integrator against `T_r(A)`: growth `9/2 lam`, or the normal velocity as growth rate | `norm_bugRun_sub_truncation_le_mul_of_forall_le`, `norm_bugRun_sub_truncation_le_mul_of_norm_sub_tangentProjAt_le` (`Integrators/Matrix/BUGQuasiOptimalityTruncation.lean`, `Integrators/Matrix/BUGQuasiOptimalityNormalTruncation.lean`) | the continuous counterparts are `IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_singularValues_lt` and `IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_integral_lt` |
| Error certificates of the BUG integrator: robust (against `A`), quasi-optimal (against `T_r(A)`) | `le_and_le_of_forall_hybrid_step`, `norm_adaptiveBugRun_sub_truncation_le_and_norm_sub_le` (`Integrators/Matrix/BUGHybridQuasiOptimality.lean`, `Integrators/Matrix/BUGAdaptiveQuasiOptimality.lean`) | every step satisfies `a (n + 1) ≤ a n + δ n` and `abs (a n - d n) ≤ s n`; the hybrid bound uses certified quasi-optimal steps where a gap exists and the local errors elsewhere |

**Two spellings of one hypothesis (finding).** `MatrixBUG.stepRel.hasLocalError` takes the global
normal-component bound as `MatrixBUG.FactoredNormalBound F r ε`, `MatrixKSL.stepRel.hasLocalError`
takes it as `FactoredNormalBoundOn F r univ ε`. The two are equivalent by
`factoredNormalBound_iff_univ` (next section).

**Not bridged yet (finding, 2026-11-16).** The core files that use `StepRel` and `IsRun` are the
six files of the generic theory (`Integrators/Defs.lean`, `Integrators/GlobalError.lean`,
`Integrators/Tube.lean`, `Integrators/Method.lean`, `Integrators/MethodGrid.lean`,
`Integrators/MethodTolerance.lean`), the files of the matrix integrators above, and the files of
the next section. The other step predicates of the core are predicates on the data of one step
(bases, substep solutions) and have no step relation of type `StepRel`: among them
`IsTuckerBUGStep` (the step relation of the Tucker integrator is `TuckerBUG.stepRel`, next
section), `IsParTuckerBUGStep`, `IsAugTuckerBUGStep`, `IsRankAdaptiveBUGStep`,
`IsParallelBUGStep`, `IsImplicitBUGStep`, and the tensor-train steps `IsTTKSLStep`,
`IsTTAugBUGStep`. The midpoint BUG step has a step relation on matrices,
`MatrixMidpointBUG.stepRel`, in the files `HighOrder/Defs.lean`, `HighOrder/MidpointBUGStep.lean`
and `HighOrder/MidpointBUGRun.lean`; the explicit midpoint step in bases with `2 r` columns has
`ExplicitMidpoint.stepRel` (`HighOrder/Defs.lean`, `Research/ExplicitMidpointRun.lean`), and the
implicit BUG step on matrices `MatrixImplicitBUG.stepRel` (`Stiff/Defs.lean`); the projector form
`MidpointBUG.IsMidpointBUGStep` has none. The error bounds of the core for these steps are stated
for
chains of steps and are not instances of `StepMethod.IsTubeLocal.exists_run_norm_sub_le`.

## Further step methods: tolerance, sketches, retractions, Tucker tensors

Core files: `LeanDLRA/Integrators/Matrix/AdaptiveBUGRun.lean` (rank-adaptive BUG, runs),
`LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean` (parallel BUG with a tolerance),
`LeanDLRA/Randomized/DRSVDStep.lean`, `LeanDLRA/Randomized/DRSVDRun.lean` (dynamical randomized
SVD, Carrel, arXiv 2410.17091), `LeanDLRA/Integrators/Matrix/ProjectedEuler.lean`,
`LeanDLRA/Integrators/Matrix/ProjectedRK.lean`, `LeanDLRA/HighOrder/ProjectedRK.lean` (projected
Euler and Runge–Kutta methods, Kieri and Vandereycken, Comput. Methods Appl. Math. 19 (2019)),
`LeanDLRA/Tensor/Tucker/BUGStep.lean`, `LeanDLRA/Tensor/Tucker/BUGRun.lean` (BUG for Tucker
tensors, [CerutiLubich2022]). All are instances of `StepMethod.IsTubeLocal`; the table gives the
step relation, the margin constant and the run theorem. The hypotheses on `F` and `A` of the run
theorems are those of the previous section; the integrators with a tolerance use the form with a
tolerance for every step (`StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_tol`).

| Concept | Core | Relation (lemma) |
|---|---|---|
| Rank-adaptive BUG with truncation by `ϑ`: tube-local method | `MatrixBUG.isTubeLocal_adaptiveStepRel_Ici` | `R = Set.Ici r₀`, every matrix admissible, `κ = 4`; a step exists from every matrix: `MatrixBUG.exists_adaptiveStepRel_Ici` |
| Rank-adaptive BUG: existence of a run and error bound | `MatrixBUG.adaptive_exists_run_norm_sub_le` | bound `bugGlobalBound L B H T δ ε h + Real.exp (L * T) * (n * ϑ)`; every run: `MatrixBUG.IsRun.norm_sub_le_of_adaptiveStepRel` (term `T * Real.exp (L * T) * ϑ / h`); local error of a uniform step: `MatrixBUG.adaptiveStepRel.hasLocalError_uniformGrid` |
| Parallel BUG with truncation by `ϑ`, step relation | `MatrixParallelBUG.adaptiveStepRel F R ϑ` | from the augmented step: `MatrixParallelBUG.augmentedRel.adaptiveStepRel`; truncated singular value decomposition: `MatrixParallelBUG.augmentedRel.adaptiveStepRel_truncation`; chains of factor steps: `MatrixParallelBUG.isRun_adaptiveStepRel_of_isStep`; local error: `MatrixParallelBUG.adaptiveStepRel.hasLocalError_of_tube` |
| Parallel BUG with truncation by `ϑ`: tube-local, run and error bound | `MatrixParallelBUG.isTubeLocal_adaptiveStepRel_Ici`, `MatrixParallelBUG.adaptive_exists_run_norm_sub_le` | `κ = 2`; bound `Real.exp (L * T) * (δ + n * ϑ) + T * Real.exp (L * T) * (7 * L * B * h + ε)`; every run: `MatrixParallelBUG.IsRun.norm_sub_le_of_adaptiveStepRel`; chain of factor steps: `MatrixParallelBUG.adaptive_norm_sub_le_of_isStep` |
| Dynamical randomized SVD: step relation without and with truncation to rank `r` | `MatrixDRSVD.augmentedRel F k l`, `MatrixDRSVD.stepRel F r k l` | sketch basis with `k` columns, range basis with `l` columns; bridge to the BUG step with one mode: `MatrixDRSVD.isTuckerBUGStepCore_of_factors`; to the step of the older analysis: `MatrixDRSVD.isDRSVDStep_of_factors` (`RandomizedBUG.IsDRSVDStep`); local error: `MatrixDRSVD.stepRel.hasLocalError_of_tube` |
| Dynamical randomized SVD: tube-local, run and error bound | `MatrixDRSVD.isTubeLocal_stepRel`, `MatrixDRSVD.exists_run_norm_sub_le` | `κ = 3`, admissible `Y.rank ≤ r`; bound `Real.exp (L * T) * δ + T * Real.exp (L * T) * ((2 * bugC₁ L H + 1) * ε + (2 * bugC₂ L B H + 10 * L * B) * h)`; every run: `MatrixDRSVD.IsRun.norm_sub_le`; the older global form `RandomizedBUG.drsvd_global_error_le` has given exact solutions |
| Projected Euler step: before and after the retraction | `MatrixProjEuler.tangentRel F r`, `MatrixProjEuler.stepRel F r κ` | `Y₁ = ℛ(Y₀ + (t₁ - t₀) P(Y₀) F₀)`; `‖Y₁ - X‖ ≤ κ * distLR r X`; a step exists for `1 ≤ κ`: `MatrixProjEuler.exists_stepRel`; the retraction by a truncated singular value decomposition: `MatrixProjEuler.tangentRel.stepRel_truncation`; `Z - P Z = (1 - U Uᵀ) Z (1 - V Vᵀ)`: `sub_tangentProj_apply` |
| Projected Euler: tube-local, local error, run and error bound | `MatrixProjEuler.isTubeLocal_stepRel`, `MatrixProjEuler.stepRel.hasLocalError_of_tube`, `MatrixProjEuler.exists_run_norm_sub_le` | `κ = 0` (margin constant; the factor of the retraction is a different `κ`); for `κ = 1` the constant of `MatrixEulerBUG.exists_run_norm_sub_le`; every run: `MatrixProjEuler.IsRun.norm_sub_le` |
| Projected Runge–Kutta step | `MatrixPRK.stepRel F r κ a b c`, stage derivative `MatrixPRK.stageDeriv` | stages `η_j = ℛ(Y₀ + h ∑ a_{jl} P(η_l) F(t₀ + c_l h, η_l))`; abstract analysis (stage growth, local error constant): `ProjectedRK.stageGrowth`, `ProjectedRK.localErrorConst`, `ProjectedRK.norm_sub_le_of_stages` |
| Projected Runge–Kutta: tube-local, run and error bound | `MatrixPRK.isTubeLocal_stepRel`, `MatrixPRK.exists_run_norm_sub_le` | margin constant `(1 + κ) * tabWeight a b + 1`; the order of the classical scheme is a hypothesis (`hRK`); every run: `MatrixPRK.IsRun.norm_sub_le` |
| Tucker BUG step relation | `TuckerBUG.stepRel F r` | admissible: `Tensor.ModeRankLE r`; the data are a step `IsTuckerBUGStepCore` (`Tensor.isTuckerBUGStepCore_of_orthonormal`); step near the solution and local error: `TuckerBUG.stepRel_tubeExt_iff_of_near`, `TuckerBUG.stepRel.hasLocalError_of_tube` |
| Tucker BUG: tube-local, run and error bound | `TuckerBUG.isTubeLocal_stepRel`, `TuckerBUG.exists_run_norm_sub_le` | margin constant `d + 2`; normal bound at `TuckerBUG.normalTriples r`; bound with `tuckerC₁ d L H`, `tuckerC₂ d L B H`; every run: `TuckerBUG.IsRun.norm_sub_le` |
| Distance of an exact solution to the matrices of rank at most `r`, bound without a term `h²` | `distLR_flow_le_exp` (global field), `distLR_flow_le_exp_of_tube` (field controlled on a tube) | both `dist ≤ h * ε * Real.exp (L * h)` with constant 1; the older tube bound `distLR_flow_le_of_tube` has `h * (10 * L * B * h + ε)` |

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
