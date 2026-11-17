# Catalogue concept map

The local forms of the catalogue: definitions and lemmas of the files in `Literature/`,
`OpenProblems/`, `Novel/` and `Corrections/` that state a notion of the core in their own terms,
and how each one relates to the core definition (equal and replaced, implies, kept with a proven
bridge, or not bridged). The core definitions and their relations are in
[CONCEPTS.md](../CONCEPTS.md); the sections here have the same names as there.

## Pseudoinverses

| Concept | Core | Relation (lemma) |
|---|---|---|
| `pinvL` (`Literature/Integrators/P2001_08599a`) | `Matrix.gramPinv` | equal, replaced |
| `pinv` (`Literature/Integrators/P2001_08599b`) | `Matrix.gramPinv` | equal, replaced |
| `Novel.OpTR37.pinv` | `Matrix.gramPinv` | equal, replaced |
| `Novel.OpRS34.pinvT` | `Matrix.gramPinv` | equal, replaced |
| `gramPinv` (`Literature/Randomized/P2410_17091a`) | `Matrix.gramPinv` | equal, replaced |
| `IsMoorePenrose` (`Literature/Stochastic/P2607_27438a`, square matrices) | `Matrix.IsMoorePenrose` at `m = n` | equal (same four equations), replaced |
| Penrose conjunction of `svd_pinv_penrose` (`P2410_17091a`) and `isMoorePenrose_mul_mul` (`Literature/Training/P2505_08022a`) | `Matrix.isMoorePenrose_mul_mul_transpose`: `(U S Vᵀ)⁺ = V S⁻¹ Uᵀ` | `svd_pinv_penrose` restated with `Matrix.IsMoorePenrose` and proved by the core lemma; `isMoorePenrose_mul_mul` replaced by the core lemma (deprecated alias) |
| `IsChartData U V U⊥ V⊥ G` (`P2001_08599a`) vs `IsChartBasis` (`P2001_08599b`) | – | equivalent: `isChartData_iff` (`IsChartData ↔ IsChartBasis U U⊥ ∧ IsChartBasis V V⊥ ∧ IsUnit G.det`; `U U⁺ + U⊥ U⊥⁺ = 1` is the dimension count) |

Also proved: `diag(σ⁻¹)` is the Moore–Penrose inverse of `diag(σ)` for every `σ`
(`Matrix.isMoorePenrose_diagonal`, stated in `Literature/Randomized/P2308_16547a` for now, to move to
`Factorization/Defs.lean`), and `svdPinv U σ V = V diag(σ⁻¹) Uᵀ` (`P2308_16547a`) is the Moore–Penrose
inverse of `U diag(σ) Vᵀ` for orthonormal `U`, `V` and **every** `σ`, zero entries included:
`P2308_16547.isMoorePenrose_svdPinv`, `svdPinv_eq_pinv` (implies; `svdPinv` is kept because it takes
the SVD factors). The column projectors `A * A.gramPinv` are in the next section.

## Column-space and Galerkin projectors

| Concept | Core | Relation (lemma) |
|---|---|---|
| `colP` (`Literature/Foundations/P2309_06125a`, `A (AᵀA)⁻¹ Aᵀ`) | `Matrix.colProj` | equal (`Matrix.colProj_def`), replaced |
| `Novel.OpTR37.colProj` (`K K⁺`) | `Matrix.colProj` | equal (same body), replaced |
| `Novel.BlindSpotII.colProj` (`orth K (orth K)ᵀ`) | `Matrix.rangeProj` | equal: `BlindSpotII.rangeProj_eq_orth_mul_transpose`, replaced |
| `colProj` (`Literature/Training/P2410_18720a`, Gram–Schmidt fold, now `gramSchmidtProj`) | `Matrix.rangeProj` | equal: `gramSchmidtProj_eq_rangeProj`; the invariant `IsColProj A univ Q` is `Q = rangeProj A` (`isColProj_univ_iff`); statements use the core projector |
| `galerkinProj` (`Research/SameMinibatchAugmentation`, `Novel/KineticAP`, `Literature/HighOrder/P2502_07040a`), `galProj` (`Literature/HighOrder/P2402_08607a`) | `LeanDLRA.galerkinProj` | equal (same body `leftProj U * rightProj V`), replaced; the local copies carried unused `DecidableEq` arguments or `Fin p` index types, which the core one drops |

**Full column rank.** The two papers that write the Gram formula (`P2309_06125a`, `OpTR37`)
assume full column rank wherever they use it, so their results are statements about `rangeProj`
as well (`colProj_eq_rangeProj`).

**Different (not merged).** The mass-weighted Galerkin projector `galProj` of
`Literature/HighOrder/P2501_06145b` (`Ub Ubᵀ Mx Z My Vb Vbᵀ`) is orthogonal for the mass inner
product, not the Frobenius one; it equals `galerkinProj` only for `Mx = 1`, `My = 1` (see the
section "Weighted norms"). Statements written with the unfolded `leftProj U * rightProj V`
(about 20 files, e.g. `P2412_09400a`, `P1804_04561a`, `P2505_08022a`) are `galerkinProj U V` by
`rfl` (`galerkinProj_def`) and can be restated later.

## SVD, truncation, tails and rank selection

| Concept | Core | Relation (lemma) |
|---|---|---|
| `IsSVD` (`Literature/Training/P2209_13569a`; fields `left_orth right_orth antitone nonneg eq_mul`) | `Matrix.IsSVD` | equal, replaced (fields renamed) |
| `IsSVD` (`Literature/Kinetic/P2112_02695a`; fields `orthU orthW antitone nonneg eq`) | `Matrix.IsSVD` | equal, replaced (`orthW` → `orthV`) |
| `svdTrunc hr U σ V` (`P2209_13569a`), `truncSVD U σ W hr` (`P2112_02695a`) | `Matrix.svdTrunc U σ V r` | equal for `r ≤ p` (`Matrix.svdTrunc_eq_submatrix`), replaced; the core one needs no `r ≤ p`, so `IsSVD.sub_svdTrunc` and `IsSVD.norm_sub_truncSVD_sq` lost that hypothesis |
| `tailSq` (`P2112_02695a`, `Literature/Training/P2609_32615a`), `tailSum` (`Literature/Kinetic/P2303_01856a`) | `tailSqSum` | equal (same body), replaced |
| `svdTail σ s = √(∑ …)` (`Literature/Training/P2205_13571a`) | `√(tailSqSum σ s)` | equal: `svdTail_eq_sqrt_tailSqSum`; kept (it is the norm, not the square) |
| `tolRank A tol = min {r : τ_r(A) ≤ tol}` (`Literature/RankAdaptive/P2602_14854a`) | `epsRank tol A` | equal: `P2602_14854.epsRank_eq_sInf_tailNorm` (the tail is `distLR`, `tailNorm_eq_infDist`), replaced |
| `adaptiveRank S ϑ` (`Literature/RankAdaptive/P2104_05247a`, same definition) | `epsRank ϑ S` | equal (same argument), replaced |
| `tolRank ϑ X`, `svTail` (`Novel/BlindSpotII`) | `epsRank ϑ X`, `WeylSingular.tailNorm` | equal (`WeylSingular.epsRank_eq_sInf_tailNorm`; `svTail` had the body of `tailNorm`), replaced in `Novel/BlindSpotII` and `Novel/GeoLoRAFreeze` (deprecated aliases, 2026-11-10) |
| `P2209_13569.IsSVD.isBestLowRankApprox_svdTrunc` (`Literature/Training/P2209_13569a`) | `IsBestLowRankApprox` | the truncated SVD of an SVD is a best rank-`r` approximation; no core lemma of this form |

**Not bridged, with reason.** `IsPartitionedSVD` (`P2609_32615a`) does not sort the singular values
and splits them into two blocks with a gap `τⱼ < σᵢ`, so it is not an `IsSVD` of the concatenated
factors; `IsTruncRank s ϑ r₁` (`P2609_32615a`) is the minimality of `r₁` for the abstract weights `s`
and agrees with `epsRank` only when `s` are the singular values. `nuclearNorm` (`P2209_13569a`)
has no second user.

## QR and orthonormal frames

| Concept | Core | Relation (lemma) |
|---|---|---|
| `IsQR` (`Literature/Integrators/P2010_02022a`) | `Matrix.IsQR` | equal (same fields), replaced |
| `IsGSQR` (`Literature/Kinetic/P2502_03008b`, adds `0 ≤ R c c`) | `Matrix.IsQR` | **implies**: now `IsGSQR extends Matrix.IsQR` (`IsGSQR.toIsQR`) |
| `IsQR` (`Literature/Kinetic/P2502_03008a`: `Qᵀ Q = 1 ∧ ∃ R, Y = Q R`, rectangular `R`) | `Matrix.IsOrthCapture` | equal (`Matrix.isOrthCapture_iff`), replaced; same name as `Matrix.IsQR` but a different notion |
| `IsOrth` (`Literature/HighOrder/P2403_02834a`) | `Matrix.IsOrthBasisOf` | equal (same fields, `orthonormal` → `orth`), replaced |
| `IsOrthOf Q W` (`Literature/HighOrder/P2502_07040b`, `colSpan Q = W` for a subspace `W`) | `Matrix.IsOrthCapture` | **implies** for every `X` with `colSpan X ≤ W`: `IsOrthOf.isOrthCapture`; kept (its target is a subspace, not a matrix) |
| `IsBestRankApprox` (`P2502_07040b`) | `IsBestLowRankApprox` | equal (same body), replaced |
| `IsOrthonormalCols V` (`Literature/Stiff/P2503_04932a`, `∑ₙ V n a V n b = δ_{ab}`) | `Vᵀ * V = 1` | equal (`transpose_mul_self_eq_one_iff`), inlined (`docs/CONVENTIONS.md` §4) |
| `IsQRRoutine qr` (`Literature/Training/P2509_15113a`: `∀ K, Qᵀ Q = 1 ∧ Q R = K`, `R` not triangular) | `Matrix.IsOrthCapture`, `Matrix.IsQR` | equal to `∀ K, IsOrthCapture (qr K).1 K ∧ (qr K).2 = (qr K).1ᵀ K` (`P2509_15113.isQRRoutine_iff`); **implied** by `∀ K, IsQR K (qr K).1 (qr K).2` (`isQRRoutine_of_isQR`); does not imply it (separating `example`: `K ↦ (J, Jᵀ K)` with the swap `J`, `R = Jᵀ` at `K = 1` is not upper triangular). Kept (it is a routine, not a predicate on one matrix) |
| `IsCoreQR i C Q S` (`Literature/Training/P2305_19059a`: `Qᵀ Q = 1`, `Matᵢ(C)ᵀ = Q Sᵀ`, `S` invertible) | `Matrix.IsOrthBasisOf` | equal to `IsOrthBasisOf Q (Matᵢ C)ᵀ ∧ S = Matᵢ(C) Q` (`P2305_19059.isCoreQR_iff`; invertibility of `S` is automatic since `Q` is square in the column count); `IsCoreQR.isOrthBasisOf`. Kept (it carries `S`) |

The local `IsQR` of `P2502_03008a` is a capture, not a QR factorization: it allows rectangular
`R` and more columns than `rank Y`.

## Vocabulary of `Analysis/Defs.lean` and Mathlib's orthogonal projection

| Concept | Core | Relation (lemma) |
|---|---|---|
| `Novel.KineticAP.isOrthProj_starProjection` (`[FiniteDimensional ℝ E]`, no instance argument) | `LeanDLRA.isOrthProj_starProjection` | special case (finite dimension gives `HasOrthogonalProjection`); duplicate, to be removed |

## Tangent and normal projectors of the fixed-rank manifold

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
| `tangentPi U Z`, `tangentPiCLM`, `tangentSpace U Z` (`Literature/Foundations/P2008_07427a`) | symplectic low-rank factorization | projector with the weight `(Zᵀ Z)⁻¹` and a horizontal gauge; not an instance of `tangent L R` |
| `tangentP τ X V = tangent (projV τ V) (projX τ X)`, `tangentVec`, `IsTangent` (`Literature/Kinetic/P1801_01103a`) | low-rank functions `∑ Xᵢ Sᵢⱼ Vⱼ` in `L²` | `tangentP` is the core `tangent` of the function-space projectors by definition |
| `tangent`, `tangentSpace` (`Literature/Kinetic/P2101_12571a`); `tangentSet`, `tangentV`, `tangentZ`, `tangentZV` (`Literature/Kinetic/P2503_10562a`) | conservative low-rank kinetic ansatz | sets of tangent vectors with fixed (conserved) basis functions and a gauge; no projector of the core corresponds |

`filippov` (Filippov regularisation, `Analysis/Defs.lean`): its local form `filippovGradR S`
(`Literature/Training/P2505_08022a`) is `filippov gradR Set.univ S`
(`P2505_08022.filippovGradR_eq_filippov`); the local name is kept.

## Low-rank and SVD vocabulary, normal-component bounds

| Concept | Core | Relation (lemma) |
|---|---|---|
| `P2602_14854.epsRank_eq_sInf_tailNorm` (`Literature/RankAdaptive/P2602_14854a`) | `WeylSingular.epsRank_eq_sInf_tailNorm` | duplicate (same statement) |

## Runge–Kutta tableaux and the `φ`-functions

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
| `riccatiField` (root namespace, from `OpenProblems/Curated/StiffAndStochasticDefs.lean`) and the former `KalmanBucy.riccatiField` | `LeanDLRA.riccatiField` | one definition: the copy in `namespace LeanDLRA.KalmanBucy` and the bridge between the two are removed; the root name stays because a recorded statement (`riccati_equilibrium_attracts`) uses it |
| `IsXQR Measure.count K X' S'` (`Literature/Kinetic/P2311_09425b`, finite grid) | `Matrix.IsOrthCapture` | equal to `X̃ᵀ X̃ = 1 ∧ K̃ = X̃ S'` for the grid matrices (`isXQR_count_iff`), hence a capture (`IsXQR.isOrthCapture_count`); for a general measure it is the same statement in `L²(ν)` (different carrier). `IsVQR` (in `Lp`) is not bridged: the core has no abstract orthonormal-frame notion yet |

## Tensor step vocabulary

| Concept | Core | Relation (lemma) |
|---|---|---|
| `OpenProblems.TensorNetworks.ttTangentSum` (`OpenProblems/TensorNetworks/Part2Defs.lean`) | `Tensor.ttTangentSum` | the same expression: `ttTangentSum_eq_tensor` |
| `OpenProblems.Randomized.ttTangent` (`OpenProblems/Randomized/Part4Defs.lean`) | `Tensor.ttTangentSum` | equal after the index shift `R k ↦ R (k + 1)`: `ttTangent_eq_ttTangentSum` |
| `OpenProblems.TensorNetworks.tucker3` (`OpenProblems/TensorNetworks/Part3Defs.lean`) | `Tensor.tucker` | on three modes the entries of `Tensor.tucker` are this triple sum: `tucker_apply_eq_tucker3` |

Kept in the catalogue:

| Definition | Module | Why it stays |
|---|---|---|
| `ttTangentSum` | `OpenProblems/TensorNetworks/Part2Defs.lean` | three theorems recorded in `docs/statements_catalogue.json` are stated with it (`ttTangentSum_idem`, `ttTangentSum_isObliqueProj`, `ttTangentSum_isOrthProj` in `OpenProblems/TensorNetworks/Part2b.lean`), and a recorded statement does not change; bridged by `ttTangentSum_eq_tensor`; no core module uses it |
| `schmidtOp` | `OpenProblems/TensorNetworks/Part2Defs.lean` | the operator `X ↦ ∑ₖ Bₖ X Cₖᵀ` on matrices, without a core counterpart; used in the catalogue files `Part2b` and `Part2c` of that folder only |
| `IsDefectParTuckerStep` | `OpenProblems/TensorNetworks/Part2Defs.lean` | a parallel Tucker step with a defect term; used in the catalogue file `Part2c` only; its relation to `parTuckerBUG` is not examined |
| `tucker3` | `OpenProblems/TensorNetworks/Part3Defs.lean` | tensors with three modes as functions `ι → κ → μ → ℝ`; used in the catalogue files `Part3a` and `Part3b` of that folder only; bridged (table above) |
| `tuckerTensor3` | `Literature/TensorNetworks/P1709_02594a.lean` | used in its own file only; not compared with `tucker3` or `Tensor.tucker` |

## Kinetic transport, flux and difference operators

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
| stencils `Dx`, `Dxx`, `Dp` on grid functions, with the spacing `dx` as argument (`Literature/Kinetic/P2411_06844a`) | `Kinetic.centralDiff`, `Kinetic.secondDiff`, `Kinetic.fwdDiff` | actions on grid functions of the core matrices, stay: `Dx_eq_centralDiff_mulVec`, `Dxx_eq_secondDiff_mulVec`, `Dp_eq_fwdDiff_mulVec` (the core lemmas `Kinetic.centralDiff_mulVec`, `Kinetic.secondDiff_mulVec`, `Kinetic.fwdDiff_mulVec` read backwards); the upwind combination `upw dx a` is the action of `a • Kinetic.centralDiff N dx - (dx / 2 * |a|) • Kinetic.secondDiff N dx`: `upw_eq_mulVec` |
| column space, orthogonal projector onto a subspace, hyperplane `u^⊥` and its projector (`Literature/Kinetic/P2411_06844a`) | none in the core | the local copies are replaced by the definitions `Novel.BGKEntropy.colSpace`, `IsOrthProjOnto`, `hyperplane`, `hyperProj` of the catalogue file `Novel/BGKEntropy.lean` (rename map `docs/renames.json`); not related to a projector of the core |
| `D^x` on `ZMod N`, divided by `2 Δx` (`Literature/Kinetic/P2502_03008a`) | `Kinetic.centralDiff` | equal (same body), **replaced** (rename map `docs/renames.json`); `Dx_mulVec` states the stencil at one cell (`Kinetic.centralDiff_mulVec`) and `Dx_transpose` is `Kinetic.centralDiff_transpose` |
| `Dxx`, `Dplus` with the scalings `1 / (2 Δx)` and `1 / √(2 Δx)` (`P2502_03008a`) | `Kinetic.secondDiff`, `Kinetic.fwdDiff` | multiples, stay: `Dxx_eq_smul_secondDiff : Dxx Δx = (Δx / 2) • Kinetic.secondDiff N Δx`, `Dplus_eq_smul_fwdDiff : Dplus Δx = (Δx / √(2 * Δx)) • Kinetic.fwdDiff N Δx` |
| `dPlus`, `dMinus` on grid functions and `DP`, `DM` on matrices (`Literature/Kinetic/P2402_16746b`) | `Kinetic.fwdDiff`, `Kinetic.bwdDiff` | actions of the core matrices, stay: `dPlus_eq_fwdDiff_mulVec`, `dMinus_eq_bwdDiff_mulVec`, `DP_eq_fwdDiff_mul`, `DM_eq_bwdDiff_mul` (the last two through `Kinetic.fwdDiff_mul_apply`, `Kinetic.bwdDiff_mul_apply`) |
| flux `flux` and its adjoint `fluxAdj` of the staggered `P_N` scheme (`P2402_16746b`) | `Kinetic.streaming` | instances with two terms: `flux_eq_streaming` (terms `(bwdDiff, A⁺)`, `(fwdDiff, A⁻)`), `fluxAdj_eq_streaming` (terms `(fwdDiff, A⁺)`, `(bwdDiff, A⁻)`) |
| centred difference `vpDx` on `Fin 4` (`P2101_12571b`), `Fin`-indexed stencils of `P2307_07538b`, `P1907_04247a.transport` | `Kinetic.centralDiff`, `Kinetic.streaming` | not bridged; the core stencils are indexed by `ZMod N`, and the core form for cells numbered by `Fin N` is the submatrix along `ZMod.finEquiv N` (`Kinetic.fwdDiff_submatrix_finEquiv` and the three analogues, `Kinetic/Stencils.lean`), to which these local stencils can be compared |
