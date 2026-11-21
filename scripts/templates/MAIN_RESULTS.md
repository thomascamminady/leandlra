# Main results of the core library

This page states the main theorems of the core library, by topic. The core library is the set of
modules imported by `LeanDLRA.lean`. The second library of the repository, the catalogue of paper
files (`LeanDLRACatalogue.lean`), is not covered: a result is listed here only if it is stated in
the definitions of the core. Where the core has no result on a topic, the page says so. The two
libraries are described in [STRUCTURE.md](STRUCTURE.md).

If you are new to the library, read [GETTING_STARTED.md](GETTING_STARTED.md) first. All
definitions of the core are listed in [DEFINITIONS.md](DEFINITIONS.md); how they relate to each
other is the subject of [CONCEPTS.md](CONCEPTS.md).

**How to read an entry.** Each entry gives the full Lean name, a link to the file and the lines,
the statement, one paragraph in words, and the source. The statements are copied from the source
files and were compared with them at commit @commit. A theorem is quoted from its
keyword to the `:=` that starts its proof; a definition or structure is quoted completely.
Arguments that a file declares once for a whole section (with the keyword `variable`), for example
the field `F`, the constants `L B ε` or the index types `m n` of matrices, are not repeated in the
quoted block. All names live in the namespace `LeanDLRA`, which is omitted.

**Sources.** A paper is cited by its key in square brackets where the source file uses a key, and
otherwise in the form the docstring of the declaration uses (authors and arXiv number). The keys
are resolved in the last section. A result without a source line has no paper cited in its
docstring.

## Contents

1. [Terms and notation](#1-terms-and-notation)
2. [Low-rank linear algebra](#2-low-rank-linear-algebra)
3. [The DLRA problem and its bundles](#3-the-dlra-problem-and-its-bundles)
4. [Steps, runs and the global error](#4-steps-runs-and-the-global-error)
5. [The BUG integrator](#5-the-bug-integrator)
6. [Projector splitting and variants of the BUG integrator](#6-projector-splitting-and-variants-of-the-bug-integrator)
7. [Stiff problems and the primal–dual error representation](#7-stiff-problems-and-the-primaldual-error-representation)
8. [Tensors](#8-tensors)
9. [Kinetic equations: vocabulary](#9-kinetic-equations-vocabulary)
10. [Training, filtering, control](#10-training-filtering-control)
11. [Results of single papers in the core](#11-results-of-single-papers-in-the-core)
12. [Citation keys](#12-citation-keys)

## 1. Terms and notation

The page uses the following terms, each with one meaning.

* **State space.** A real inner product space `E`. Abstract results are stated on `E`. For
  matrices `E` is `Matrix m n ℝ` with the Frobenius inner product and the Frobenius norm; these
  are scoped instances that a file activates with `open scoped LeanDLRA.Frobenius`. In a matrix
  statement `‖A‖` is therefore the Frobenius norm. The spectral norm is written `specNorm A`.
* **Field.** The right-hand side `F : ℝ → E → E` of the differential equation `Y' = F(t, Y)`; the
  time is the first argument.
* **Solution.** `ODESolution F y a b` says that `y` solves `y' = F(t, y)` on the interval
  `[a, b]`: `y` is continuous on `[a, b]` and has the right derivative `F t (y t)` at every `t`
  in `[a, b)`.
* **Exact solution** `A`: a solution of the full equation, the object that is approximated.
  **Numerical values** `Y 0, Y 1, …`: the values an integrator produces. **Start value** `Y₀`.
  **Initial error** `δ`: a bound for `‖Y₀ - A t₀‖`.
* **Step size** `h`, with an upper bound `H` where a constant depends on it, and a **horizon**
  `T` with `N * h ≤ T` for `N` steps.
* **Lipschitz constant** `L` and **bound** `B` of the field: `‖F t x - F t y‖ ≤ L * ‖x - y‖` and
  `‖F t x‖ ≤ B`.
* **Tube.** The set of all pairs `(t, x)` with `t` in `[a, b]` and `‖x - A t‖ ≤ ρ`, written
  `tubeSet A a b ρ`; `ρ` is the **tube radius**. (In the single entry on curvature in section 2
  the letter `ρ` is a lower bound for singular values instead; the entry says so.)
* **Orthogonal projector.** A continuous linear map `P` on `E` that is idempotent and symmetric
  (`IsOrthProj P`).
* **Normal component.** For a matrix `Y = U S Vᵀ` with orthonormal columns of `U` and `V`, the
  part `(I - U Uᵀ) F(t, Y) (I - V Vᵀ)` of the field, which is orthogonal to the column space and
  to the row space of `Y`. In projector form it is `(1 - P) ((1 - Q) (F t Y))`. Its bound is `ε`.
* **Truncation tolerance** `ϑ`: a bound for the change of a value by a rank truncation.
* **Step, grid, run.** A step of a method leads from a value `Y₀` at time `t₀` to a value `Y₁`
  at time `t₁`. A grid is a nondecreasing sequence of times. A run is a sequence of values in
  which each value is obtained from the previous one by a step between consecutive grid times.
* **Local error** of a step: the distance between its result and the exact solution of the full
  equation that starts at the start value of the step. **Global error**: `‖Y n - A (τ n)‖`.
* **Robust.** An error bound is called robust if its constants do not depend on the singular
  values of the numerical values or of the exact solution. Section 2 shows why this matters: the
  tangent projector of the fixed-rank matrices has a Lipschitz constant proportional to the
  inverse of the smallest singular value.

## 2. Low-rank linear algebra

### 2.1 Singular value decomposition

@stmt LeanDLRA/Classical/SVD.lean exists_svd SVD.exists_svd

A real matrix `A` of rank `r` is a product `U * diagonal σ * Vᵀ` in which `U` and `V` have `r`
orthonormal columns each and `σ` is a nonincreasing family of positive numbers. The numbers `σ i`
are the first `r` singular values of the linear map of `A` in the sense of Mathlib
(`(Matrix.toEuclideanLin A).singularValues i`). There are no constants. The hypothesis `hr` only
names the rank.

### 2.2 Best approximation of rank at most r (Eckart–Young–Mirsky)

@stmt LeanDLRA/LinearAlgebra/SVD/Defs.lean truncation EckartYoung.truncation

@stmt LeanDLRA/Classical/EckartYoung.lean rank_truncation_le EckartYoung.rank_truncation_le

@stmt LeanDLRA/Classical/EckartYoung.lean sum_sq_singularValues_le_sq_norm_sub EckartYoung.sum_sq_singularValues_le_sq_norm_sub

@stmt LeanDLRA/Classical/EckartYoung.lean sq_norm_sub_truncation EckartYoung.sq_norm_sub_truncation

@stmt LeanDLRA/Classical/EckartYoung.lean infDist_setOf_rank_le EckartYoung.infDist_setOf_rank_le

The truncation of `A` to rank `r` is the product of `A` with the orthogonal projector onto the
span of its first `r` right singular vectors. It has rank at most `r`. Every matrix `B` of rank
at most `r` satisfies `‖A - B‖² ≥ ∑ σ_i(A)²`, the sum taken over the indices `i` from `r` to the
number of columns minus one, and the truncation attains this value. Hence the distance in the
Frobenius norm from `A` to the set of matrices of rank at most `r` is the square root of that
sum. The singular values are those of Mathlib, indexed from zero in nonincreasing order. There
are no hypotheses besides the rank bound on `B`.

Source: the docstrings name Schmidt (1907), Eckart and Young (1936) and Mirsky (1960).

### 2.3 The tangent projector of the fixed-rank matrices

@stmt LeanDLRA/FixedRank/Defs.lean tangentProj tangentProj

@stmt LeanDLRA/Matrix/Projectors.lean isOrthProj_tangentProj isOrthProj_tangentProj

For matrices `U` and `V`, `tangentProj U V` is the map `Z ↦ U Uᵀ Z + Z V Vᵀ - U Uᵀ Z V Vᵀ`
(`tangentProj_apply`). It is built from the left projector `leftProj U`, the right projector
`rightProj V` and the combination `tangent L R = L + R - L * R`. If `U` and `V` have orthonormal
columns (`hU`, `hV`), it is an orthogonal projector. For `Y = U S Vᵀ` with invertible `S` its
range is the tangent space at `Y` of the manifold of matrices of the rank of `Y`; the theorem
quoted here states only the projector property.

Source: [KochLubich2007, Lemma 4.1].

@stmt LeanDLRA/FixedRank/TangentSpace/Defs.lean tangentProjAt tangentProjAt

@stmt LeanDLRA/FixedRank/TangentSpace/Defs.lean tangentSpaceAt tangentSpaceAt

@stmt LeanDLRA/FixedRank/TangentSpace.lean tangentProjAt_eq_starProjection tangentProjAt_eq_starProjection

@stmt LeanDLRA/FixedRank/TangentSpace.lean tangentProjAt_eq_tangentProj tangentProjAt_eq_tangentProj

`tangentProjAt Y` and `tangentSpaceAt Y` depend on the matrix `Y` alone: no factorization is
chosen and no rank is assumed. With the orthogonal projector `P = Y.rangeProj` onto the column
space of `Y` and the orthogonal projector `Q = Yᵀ.rangeProj` onto its row space,
`tangentProjAt Y` is the map `Z ↦ P Z + Z Q - P Z Q` (`tangentProjAt_apply`). `tangentSpaceAt Y`
is the subspace of the matrices `A Y + Y B` with square matrices `A`, `B`
(`mem_tangentSpaceAt`). For every matrix `Y` the first is the orthogonal projection onto the
second. At `Y = U S Vᵀ`, where `U` and `V` have orthonormal columns (`hU`, `hV`) and `S` is
invertible (`hS`), it is `tangentProj U V`. The normal projector `1 - tangentProjAt Y` is
`Z ↦ (1 - P) Z (1 - Q)` (`one_sub_tangentProjAt_apply`). The core has no manifold structure on
the set of matrices of a given rank (section 2.5 has the set `fixedRankSet`); that
`tangentSpaceAt Y` is the tangent space of this manifold at `Y` is the statement of the cited
paper and not a theorem of the core.

Source: [KochLubich2007, §2.1 and Lemma 4.1], as cited in the module docstring of
`LeanDLRA/FixedRank/TangentSpace/Defs.lean`.

### 2.4 Curvature: the tangent projector depends on the point with constant 1/ρ

@stmt LeanDLRA/Matrix/Curvature.lean koch_lubich_tangent_frob Curvature.koch_lubich_tangent_frob

In this entry `ρ` is not a tube radius: it is a positive lower bound for the singular values of
the factor `S` (hypothesis `hS`: `ρ * ‖v‖ ≤ ‖S v‖` for all vectors `v`). Let `Y = U S Vᵀ` and
`Y' = U' S' Vᵀ'` with orthonormal columns of `U`, `V`, `U'`, `V'`; nothing is assumed about
`S'`. Then the tangent projectors at the two points, applied to any matrix `B`, differ by at most
`2 ρ⁻¹ ‖Y' - Y‖ ‖B‖` in the Frobenius norm. `tangentProjMat` is the tangent projector written
with the two projection matrices; it agrees with `tangentProj`
(`Curvature.tangentProjMat_eq_tangentProj`). The constant is `2 / ρ`; it becomes large when `Y`
has a small singular value. Error bounds that use this estimate inherit the factor, and the
bounds of sections 5 to 8 are called robust because they avoid it.

Source: Koch and Lubich 2007, Lemma 4.2 [KochLubich2007], in the form with Frobenius norms of
Bachmayr, Eisenmann, Kieri and Uschmajew, arXiv 2002.12197, Lemma A.2, as cited in the docstring.

**At a matrix, without a factorization.** The file
@file(LeanDLRA/FixedRank/TangentSpace/Curvature.lean) states the same estimates for `tangentProjAt`. The lower bound `ρ` is now one for the `r`-th
singular value `σ_{r-1}(X)` of a matrix `X` of rank `r` (singular values `σ₀ ≥ σ₁ ≥ ⋯`,
indexed from zero as in Mathlib):

@stmt LeanDLRA/FixedRank/TangentSpace/Curvature.lean norm_tangentProj_sub_tangentProjAt_le norm_tangentProj_sub_tangentProjAt_le

@stmt LeanDLRA/FixedRank/TangentSpace/Curvature.lean norm_tangentProjAt_sub_le norm_tangentProjAt_sub_le

The first theorem compares the projector of orthonormal factors `U`, `V` with the projector at
the matrix `X`; the core `S` may be any matrix, invertible or not. The second is the Lipschitz
bound of `Y ↦ tangentProjAt Y` between matrices of rank `r`. In both, the lower bound is needed
at one of the two points only, and there is no smallness condition on `‖Y - X‖`.

@stmt LeanDLRA/FixedRank/TangentSpace/Curvature.lean mem_tangentSpaceAt_of_hasDerivWithinAt mem_tangentSpaceAt_of_hasDerivWithinAt

@stmt LeanDLRA/FixedRank/TangentSpace/Curvature.lean tangentProjAt_sub_eq_zero_of_forall_norm_sub_le tangentProjAt_sub_eq_zero_of_forall_norm_sub_le

@stmt LeanDLRA/FixedRank/TangentSpace/Curvature.lean tangentProjAt_truncation_sub_eq_zero tangentProjAt_truncation_sub_eq_zero

The derivative of a curve of matrices of rank `r` with `σ_{r-1} ≥ ρ > 0` lies in the tangent
space at the curve (`s` is a set of times such as `Set.Ici t`, so the derivative may be a right
derivative). A best approximation `X` of `A` among the matrices of rank at most `r`
(`hbest`) satisfies the first-order condition `P(X) (A - X) = 0`, and so does the truncated
singular value decomposition. The proof of the second uses the curve `(1 + ε M) X (1 + ε N)`,
whose velocity at `ε = 0` is the tangent vector `M X + X N`; no factorization of `X` is chosen.
The module docstring also has `norm_one_sub_tangentProjAt_apply_sub_le`,
`‖(1 - P(Y)) (Y - X)‖ ≤ ρ⁻¹ ‖Y - X‖²`, which is not quoted here.

Source: the module docstring cites [KochLubich2007, §2 and Lemma 4.2].

@stmt LeanDLRA/FixedRank/TangentStepTruncation.lean tailNorm_add_tangent_le tailNorm_add_tangent_le

An explicit step along a tangent direction leaves the matrices of rank at most `r`, but only to
second order. Let `X = U S Vᵀ` with orthonormal `U`, `V` and `ρ ≤ σ_{r-1}(S)`, and let `Z` be a
tangent matrix at `X`, `(1 - U Uᵀ) Z (1 - V Vᵀ) = 0`, with `‖Z‖ ≤ ρ / 2`. Then the Frobenius norm
of the singular values of `X + Z` beyond the first `r`, which is the distance of `X + Z` to the
matrices of rank at most `r` (`WeylSingular.tailNorm_eq_infDist`), is at most `‖Z‖² / ρ`. The
constant contains the lower bound `ρ`; the bound concerns one tangent step of a given size.

Source: the module docstring cites arXiv 2111.14540, Sections 6 and 7 (retraction of a tangent
step by the truncated singular value decomposition).

**The constant 1.** The constant `2` of the two theorems above can be replaced by `1`. The file
@file(LeanDLRA/FixedRank/TangentSpace/ProjectorLipschitz.lean) proves the Lipschitz bound with
`1`, first for factors and then at a matrix:

@stmt LeanDLRA/FixedRank/TangentSpace/ProjectorLipschitz.lean norm_tangentProjMat_sub_le_inv_mul Curvature.norm_tangentProjMat_sub_le_inv_mul

@stmt LeanDLRA/FixedRank/TangentSpace/ProjectorLipschitz.lean norm_tangentProjAt_sub_le_inv_mul norm_tangentProjAt_sub_le_inv_mul

The hypotheses are those of `Curvature.koch_lubich_tangent_frob`, and of `norm_tangentProjAt_sub_le`
in the second statement: `X` and `Y` have rank `r`, and the lower bound `ρ` is needed at `X`
only. There is no smallness condition on `‖Y - X‖`; all norms are Frobenius norms. The proof
splits `P(Y) B - P(X) B` into the orthogonal pieces `P(Y) (1 - P(X)) B` and
`-(1 - P(Y)) P(X) B`, and bounds each by `ρ⁻¹ ‖Y - X‖` times the norm of the vector it is applied
to. The two bounds on normal vectors are

@stmt LeanDLRA/FixedRank/TangentSpace/ProjectorLipschitz.lean norm_tangentProjAt_apply_le_of_tangentProjAt_eq_zero norm_tangentProjAt_apply_le_of_tangentProjAt_eq_zero

@stmt LeanDLRA/FixedRank/TangentSpace/ProjectorLipschitz.lean norm_tangentProj_apply_le_of_tangentProjAt_eq_zero norm_tangentProj_apply_le_of_tangentProjAt_eq_zero

The first says that the tangent projector at `X` is small on a vector `N` that is normal at `Y`,
`P(Y) N = 0`; the second is the same with the roles of `X` and `Y` exchanged, for `Y = U S Vᵀ`
given by factors and `N` normal at `X`. The module docstring lists the factor forms
(`Curvature.norm_tangentProjMat_le_of_tangentProjMat_eq_zero` and its relatives) and the bound
`‖(1 - P(Y)) Z‖ ≤ ρ⁻¹ ‖Y - X‖ ‖Z‖` for `Z` tangent at `X`
(`norm_one_sub_tangentProj_apply_le_of_tangentProjAt_eq_self`).

The constant `1` cannot be lowered. An `example` in the file has `X = e₁ e₁ᵀ`
(`ρ = 1`), `Y = (9/25) v vᵀ`, `v = (3/5, 4/5)ᵀ`, and `N = w wᵀ`, `w = (-4/5, 3/5)ᵀ`, in which
`norm_tangentProjAt_apply_le_of_tangentProj_eq_zero` holds with equality, so that a bound
`‖P(X) N‖ ≤ c ρ⁻¹ ‖Y - X‖ ‖N‖` for all `X`, `Y`, `N` needs `c ≥ 1`. The module docstring
relates this to the literature: the global bound in Frobenius norms, without a smallness condition
and with the lower bound at one point only, is Lemma 4.1 of [WeiCaiChanLeung2016] with the
constant `2`, and the constant `1` equals the maximal curvature `1 / σ_r` of the manifold of
matrices of rank `r` [FepponLermusiaux2018, Theorem 24].

**Normal vectors with the spectral norm.** The file
@file(LeanDLRA/FixedRank/TangentSpace/ProjectorSpectral.lean) bounds `‖P(X) N‖` by the spectral
norm `‖N‖₂ = specNorm N` of the normal vector `N` (`P(Y) N = 0`); `‖P(X) N‖` and `‖Y - X‖` stay
Frobenius norms:

@stmt LeanDLRA/FixedRank/TangentSpace/ProjectorSpectral.lean norm_tangentProjAt_apply_le_one_add_mul_specNorm_of_tangentProjAt_eq_zero norm_tangentProjAt_apply_le_one_add_mul_specNorm_of_tangentProjAt_eq_zero

@stmt LeanDLRA/FixedRank/TangentSpace/ProjectorSpectral.lean norm_tangentProjAt_apply_le_sqrt_two_mul_specNorm_of_tangentProjAt_eq_zero norm_tangentProjAt_apply_le_sqrt_two_mul_specNorm_of_tangentProjAt_eq_zero

The factor in the first bound is `1` to first order in `‖Y - X‖`, and it is the bound that the
derivative of the first-order condition of section 3.7 needs. In the second bound the constant is
`√2` for all `Y`. The two constants are not those of section 2.4: the module docstring says that
the bound with the constant `1` and `‖N‖₂` does not hold, with a family of examples in which the
quotient `‖P(X) N‖² / ‖Y - X‖²` tends to `2`; this family is not formalized in the core. The
squared form with the factor `1 + (ρ⁻¹ ‖Y - X‖)²` and the factor-level bounds are in the file.

### 2.5 Separation rank and the fixed-rank set

@stmt LeanDLRA/LinearAlgebra/LowRank/Defs.lean lowRankSet lowRankSet

@stmt LeanDLRA/LinearAlgebra/LowRank/SepRank.lean HasSepRankLE HasSepRankLE

@stmt LeanDLRA/LinearAlgebra/LowRank/SepRank.lean HasSepRankLE.rank_le HasSepRankLE.rank_le

@stmt LeanDLRA/LinearAlgebra/LowRank/SepRank.lean hasSepRankLE_iff_rank_le hasSepRankLE_iff_rank_le

@stmt LeanDLRA/LinearAlgebra/LowRank/SepRank.lean hasSepRankLE_iff_mem_lowRankSet hasSepRankLE_iff_mem_lowRankSet

@stmt LeanDLRA/LinearAlgebra/LowRank/SepRank.lean fixedRankSet fixedRankSet

@stmt LeanDLRA/LinearAlgebra/LowRank/SepRank.lean mem_lowRankSet_iff_exists_mem_fixedRankSet mem_lowRankSet_iff_exists_mem_fixedRankSet

@stmt LeanDLRA/LinearAlgebra/LowRank/SepRank.lean mem_fixedRankSet_of_factor mem_fixedRankSet_of_factor

`lowRankSet m n r` is the set of real `m × n` matrices of rank at most `r`, and
`fixedRankSet m n r` the set of those of rank exactly `r`; the first is the union of the sets
`fixedRankSet m n s` with `s ≤ r`. A function `f` of two variables with values in a semiring `R`
has separation rank at most `r` if it is a sum of `r` products of a function of the first
variable and a function of the second variable. The two variables range over arbitrary types, so
the definition applies to a function on phase space before any discretization. Every matrix of
samples `f (xs i) (ys j)` of such a function has rank at most `r`; for this statement `R` is a
commutative ring with the strong rank condition of Mathlib, which every field satisfies. Over a
field and on finite index types the two notions agree: `f` has separation rank at most `r` if
and only if the matrix with the entries `f i j` has rank at most `r`. For a real matrix `A` this
says that its entries have separation rank at most `r` if and only if `A` lies in
`lowRankSet m n r`. The last entry gives elements of the fixed-rank set: a product `U * S * Vᵀ`
in which `U` and `V` have orthonormal columns (`Uᵀ * U = 1`, `Vᵀ * V = 1`) and `S` is invertible
has rank exactly the number of columns of `U`. There are no constants.

### 2.6 Lower bounds for singular values from subspaces

@stmt LeanDLRA/LinearAlgebra/SVD/MinMax.lean le_singularValues_of_mul_norm_le LinearMap.le_singularValues_of_mul_norm_le

@stmt LeanDLRA/LinearAlgebra/SVD/MinMax.lean SVD.le_singularValues_of_eq_mul SVD.le_singularValues_of_eq_mul

@stmt LeanDLRA/LinearAlgebra/SVD/MinMax.lean EckartYoung.truncation_eq_self EckartYoung.truncation_eq_self

The first theorem is the max-min characterization of the singular values (Courant–Fischer for
`T† T`): if a linear map `T` satisfies `ρ ‖y‖ ≤ ‖T y‖` on a subspace `W` of dimension at least
`k + 1`, then `ρ ≤ σ_k(T)` with the zero-based `LinearMap.singularValues` of Mathlib. The second
applies it to `X = U S Vᵀ` with `r > 0` orthonormal columns in `U` and `V`: a lower bound `ρ`
of the core `S` (`ρ ‖w‖ ≤ ‖S w‖` for all `w`) is a lower bound of `σ_{r-1}(X)`; the docstring
calls it the converse of `WeylSingular.mul_norm_le_norm_toEuclideanLin_core`. The third says that
the truncated singular value decomposition of a matrix of rank at most `r` is the matrix itself.
The singular value `σ_{r-1}` is the quantity that the curvature bounds of section 2.4 and the
existence and quasi-optimality theorems of sections 3.6 and 3.7 ask to be bounded below.

Source: [Bhatia1997, §III.1] (max-min principle), as cited in the module docstring.

### 2.7 The truncated singular value decomposition is differentiable under a gap

@stmt LeanDLRA/LinearAlgebra/SVD/TruncationDeriv.lean norm_sub_le_of_isOrthProjMat norm_sub_le_of_isOrthProjMat

@stmt LeanDLRA/LinearAlgebra/SVD/TruncationDeriv.lean EckartYoung.hasFDerivAt_truncation EckartYoung.hasFDerivAt_truncation

@stmt LeanDLRA/LinearAlgebra/SVD/TruncationDeriv.lean EckartYoung.hasDerivWithinAt_truncation EckartYoung.hasDerivWithinAt_truncation

The map `B ↦ truncation B r` is the truncated singular value decomposition of rank `r`
(section 2.2). The second theorem says: if `A` has a gap after the `r`-th singular value,
`σ_r(A) < σ_{r-1}(A)`, then the map has a Fréchet derivative `L` at `A`, and
`‖L H‖ ≤ (1 + 4 ‖A‖² / (σ_{r-1}(A)² - σ_r(A)²)) ‖H‖` for every direction `H`. The constant
`4 ‖A‖²` is that of the proof, not a sharp one (module docstring). The third theorem transports
this to a curve `t ↦ A(t)` with a derivative within a set `s` at `t` (for example a right
derivative) and a gap at `A(t)`: the curve `t ↦ truncation (A t) r` has the derivative
`fderiv ℝ (fun B => truncation B r) (A t) A'` within `s`. The module docstring also lists
`EckartYoung.differentiableAt_truncation`, `EckartYoung.continuousAt_truncation` and
`EckartYoung.norm_fderiv_truncation_apply_le`. The first theorem is a Davis–Kahan bound for two
orthogonal projectors `P`, `P'` that commute with `Aᵀ A` and `Bᵀ B` and are separated by gaps
on both sides (`β < α'`, `β' < α`): `‖P' - P‖ ≤ ‖Bᵀ B - Aᵀ A‖ (1 / (α'² - β²) + 1 / (α² - β'²))`.
Under a gap the projector onto the top `r` right singular vectors is the only one with these
properties (`EckartYoung.topRightSingularVectors_mul_transpose_eq`), so that
`truncation A r = A P` for each such `P` (`EckartYoung.truncation_eq_mul_of_isOrthProjMat`).
The proof compares `P` and `P'` through Sylvester equations; no resolvent and no implicit
function theorem is used.

Source: the module docstring cites [KochLubich2007].

### 2.8 Perturbation of singular subspaces: Wedin and Davis–Kahan

@stmt LeanDLRA/LinearAlgebra/SVD/SinTheta.lean wedin_frobenius SinTheta.wedin_frobenius

@stmt LeanDLRA/LinearAlgebra/SVD/SinTheta.lean norm_truncation_sub_le_of_gap SinTheta.norm_truncation_sub_le_of_gap

@stmt LeanDLRA/LinearAlgebra/SVD/SinTheta.lean davisKahan SinTheta.davisKahan

For real matrices `A`, `B` let `V`, `Ṽ` be the top-`(r + 1)` right singular vectors
(`EckartYoung.topRightSingularVectors`). Under the gap `σ_{r+1}(A) + δ ≤ σ_r(B)` with `δ > 0`,
the part of `Ṽ` outside the range of `V` has Frobenius norm at most `√2 ‖B - A‖ / δ`
(`SinTheta.wedin_frobenius`; `SinTheta.wedin_specNorm` is the bound `‖B - A‖₂ / δ` in the
spectral norm). The second theorem is a Lipschitz bound for the truncation of rank `r + 1`
under the same gap, with the explicit constant
`1 + √2 (σ₀(A) + σ_{r+1}(A)) / δ`. The third is the same statement for symmetric operators on a
finite-dimensional real inner product space: a vector in the top-`(r + 1)` eigenspace of `T'`
has a component of squared norm at most `(ε ‖x‖ / δ)²` in the eigenvectors of `T` with index
above `r`, if `‖T' x - T x‖ ≤ ε ‖x‖` and `λ_{r+1}(T) + δ ≤ λ_r(T')`. These bounds need the gap on
one side only and are stated in `‖B - A‖`. The bound of section 2.7 has gaps on both sides and
holds for projectors that are not given by singular vectors; neither implies the other (module
docstrings of both files).

Source: Wedin, BIT 12 (1972); Davis and Kahan, SIAM J. Numer. Anal. 7 (1970); Stewart and Sun,
*Matrix Perturbation Theory*, §V.4, as listed in the module docstring (no citation key).

## 3. The DLRA problem and its bundles

A bundle is a structure that collects the standing assumptions of a group of theorems, so that a
theorem takes one hypothesis instead of five.

### 3.1 Solutions and fields

@stmt LeanDLRA/Analysis/Defs.lean ODESolution ODESolution

@stmt LeanDLRA/Analysis/Defs.lean IsLipschitzField IsLipschitzField

@stmt LeanDLRA/Analysis/Defs.lean IsBoundedField IsBoundedField

@stmt LeanDLRA/Analysis/Defs.lean tubeSet tubeSet

These are the definitions behind the terms "solution", "Lipschitz constant", "bound" and "tube"
of section 1. `IsLipschitzField` and `IsBoundedField` are global: they speak about all times and
all states. Their forms on a tube are `IsLipschitzOnTube` and `IsBoundedOnTube`.

@stmt LeanDLRA/Foundations/Existence.lean exists_ODESolution exists_ODESolution

Existence of solutions (Picard–Lindelöf): if the field is globally Lipschitz in the state (`hL`),
bounded (`hB`) and continuous in time for every fixed state (`hcont`), then for every interval
`[a, b]` and every start value `y₀` there is a solution on `[a, b]` with `y a = y₀`. The space
`E` has to be complete. No constant appears in the conclusion.

### 3.2 The bundle `DLRAProblem`

@stmt LeanDLRA/DLRA/Defs.lean DLRAProblem DLRAProblem

@stmt LeanDLRA/DLRA/Defs.lean DLRAProblem.of_global DLRAProblem.of_global

`DLRAProblem F A a b ρ L B` collects the standing assumptions of the error analysis: `A` is a
solution of `Y' = F(t, Y)` on `[a, b]`, the constants `L` and `B` are nonnegative, and on the
tube of radius `ρ` around `A` the field is `L`-Lipschitz and bounded by `B`. Nothing is assumed
outside the tube. The constants are arguments of the structure, so that they can appear in the
conclusions of theorems. `DLRAProblem.of_global` builds the bundle, for every radius, from a
field that is Lipschitz and bounded everywhere.

Source: the assumptions on a tube are those of [ZhaoOstermannGu2021, Property 1(b)]; the global
ones are the standing assumptions of [CerutiLubich2022] and [KieriLubichWalach2016].

@stmt LeanDLRA/Integrators/Tube.lean DLRAProblem.tubeExt DLRAProblem.tubeExt

The extension of the field from the tube. `tubeExt F A a b ρ` is the field that evaluates `F` at
the nearest point of the ball of radius `ρ` around `A t` for `t` in `[a, b]`, and is zero for
other times. Under a `DLRAProblem` with `0 ≤ ρ` this field is globally `L`-Lipschitz, globally
bounded by `B`, and has the same exact solution `A`. It agrees with `F` on the tube
(`tubeExt_eq`). This is the device by which theorems for global assumptions are applied to
fields that satisfy them only near the exact solution. The constants `L` and `B` do not change.

### 3.3 The normal component

@stmt LeanDLRA/DLRA/Defs.lean NormalBoundOn NormalBoundOn

@stmt LeanDLRA/Integrators/Matrix/Defs.lean FactoredNormalBoundOn FactoredNormalBoundOn

`NormalBoundOn F 𝒯 D ε` is the bound `ε` for the normal component in projector form: `𝒯` is a
set of triples `(P, Q, Y)` of two projectors and a state, `D` a set of pairs of a time and a
state, and the bound is required whenever the triple is in `𝒯` and `(t, Y)` is in `D`.
`FactoredNormalBoundOn F r D ε` is the matrix form: for all `U` and `V` with `r` orthonormal
columns and all `S` such that `(t, U S Vᵀ)` is in `D`, the Frobenius norm of
`(I - U Uᵀ) F(t, U S Vᵀ) (I - V Vᵀ)` is at most `ε`. In the theorems of sections 5 and 6 the
set `D` is the tube. The two forms are related by `factoredNormalBoundOn_iff_normalBoundOn`. The
number `ε` measures how far the field is from being tangent to the matrices of rank `r`; it is
a quantity of the problem and is not small in general. The file
[`LeanDLRA/Integrators/Matrix/FactoredNormalBound.lean`](../LeanDLRA/Integrators/Matrix/FactoredNormalBound.lean)
shows that the factored bound and a Lipschitz bound together also control the mixed components
of the field in the directions in which `S` is small, for example
`‖(1 - U Uᵀ) F(t, U S Vᵀ) (V b)‖ ≤ ε + L ‖S b‖` for a unit column `b`
(`norm_normal_mul_field_mul_col_le`, as its module docstring states it).

Source: the bound on the normal component is the assumption of [KieriLubichWalach2016] and
[CerutiLubich2022]; the form on a tube follows [ZhaoOstermannGu2021, eq. (3.3)].

### 3.4 The continuous approximation

@stmt LeanDLRA/Dynamics/ContinuousDLRA.lean dlra_norm_sub_le_gronwallBound ODESolution.dlra_norm_sub_le_gronwallBound

The error of the time-continuous approximation. Let `F` be `L`-Lipschitz with `0 ≤ L`, let `A`
solve `A' = F(t, A)` and let `Y` solve the projected equation `Y' = P(t) F(t, Y)` on `[a, b]`,
where `P t` is any family of continuous linear maps. If the neglected part `(1 - P t) F(t, Y t)`
has norm at most `ε` along `Y` (`hε`) and the initial error is at most `δ` (`hδ`), then
`‖Y t - A t‖ ≤ gronwallBound δ L ε (t - a)` on `[a, b]`. `gronwallBound` is the function of
Mathlib; for `L ≠ 0` its value is `δ e^{L(t-a)} + ε (e^{L(t-a)} - 1) / L`. The constants are `L`,
`ε` and `δ` only; no singular value and no property of the maps `P t` enters.

Source: Kieri, Lubich and Walach 2016 [KieriLubichWalach2016]; Carrel, Gander and Vandereycken,
arXiv 2203.08455, Theorem 2.3, as cited in the docstring.

@stmt LeanDLRA/DLRA/QuasiOptimality.lean dlra_norm_sub_truncation_le_integral dlra_norm_sub_truncation_le_integral

Quasi-optimality for matrices: the distance of the approximation from the best approximation.
`A` is a differentiable curve of matrices with derivative `A'` (`hA`), and
`X t = truncation (A t) r` is its truncated singular value decomposition of rank `r` (`hXbest`,
with `EckartYoung.truncation` of section 2.2). `Y` is the dynamical low-rank approximation of
the curve: it has the form `U t * S t * (V t)ᵀ` with orthonormal columns of `U t` and `V t`
(`hUV`), solves `Y' = tangentProj (U t) (V t) (A' t)` (`hY`) and starts at `X 0` (`hY₀`).
Assume on `[0, T]` that `‖A' t‖ ≤ μ` (`hμ`), that the `r`-th singular value of `A t` is at
least `ρ > 0` (`hσ`), that `‖X t - A t‖ ≤ ρ / 16` (`hd`) and that `X` is differentiable (`hX`).
Then for `t` in `[0, T]`

`‖Y t - X t‖ ≤ 2 β e^{β t} ∫₀ᵗ ‖X s - A s‖ ds`, `β = 8 μ / ρ`.

The constant `β` contains the lower bound `ρ` of the `r`-th singular value. That `Y` exists on
`[0, T]` in the factored form is a hypothesis; section 3.6 shows existence of a DLRA solution on
intervals that are short in terms of the smallest singular value of the start value. Section 3.7
has the bound for a general field `F`, for a field that is Lipschitz on a tube only, and for the
truncated singular value decomposition under a gap, with the constants `L + 6 μ/ρ` and
`L + 4 μ/ρ`.

Source: the module docstring says that a bound of this kind is in [KochLubich2007] and that the
constants `ρ / 16`, `β = 8 μ / ρ` and the factor 2 are those of its own proof.

### 3.5 DLRA solutions and the equations for the factors

@stmt LeanDLRA/DLRA/Defs.lean IsDLRASolution IsDLRASolution

A DLRA solution of rank `r` is a solution of the projected equation `Y' = P(Y) F(t, Y)` in the
sense of `ODESolution` (section 3.1), with `P(Y) = tangentProjAt Y` the orthogonal projector onto
the tangent space of the matrices of rank `r` at `Y`, together with the condition that `Y t` has
rank exactly `r` for all `t` in `[a, b]`. The rank condition at the endpoint `b` is part of the
definition: a limit of matrices of rank `r` can have smaller rank, and there `tangentProjAt` is
not the projector of the manifold of rank `r`. The definition does not mention a factorization.
The file
[`LeanDLRA/DLRA/DynamicallyOrthogonal.lean`](../LeanDLRA/DLRA/DynamicallyOrthogonal.lean) relates
it to the systems of equations for factors `Y = U Zᵀ` that the module docstring names: the
dynamically orthogonal (DO) system, its dual (DDO) and the bi-orthogonal (BO) system. For a
product of factors of full rank the file also computes the tangent projector
(`DynamicallyOrthogonal.tangentProjAt_mul_transpose_apply`).

@stmt LeanDLRA/DLRA/DynamicallyOrthogonal.lean isDLRASolution_iff_hasDerivWithinAt DynamicallyOrthogonal.isDLRASolution_iff_hasDerivWithinAt

If `U t` and `Z t` have full column rank on `[a, b]`, then `U Zᵀ` is a DLRA solution of rank `r`
if and only if it is continuous on `[a, b]` and has the right derivative
`tangentProjAt (U Zᵀ) (F t (U Zᵀ))` on `[a, b)`: the rank condition is automatic for factors of
full rank.

@stmt LeanDLRA/DLRA/DynamicallyOrthogonal.lean doSystem_iff_isDLRASolution DynamicallyOrthogonal.doSystem_iff_isDLRASolution

@stmt LeanDLRA/DLRA/DynamicallyOrthogonal.lean ddoSystem_iff_isDLRASolution DynamicallyOrthogonal.ddoSystem_iff_isDLRASolution

The DO formulation: let `U`, `Z` be continuous on `[a, b]` with right derivatives `U̇`, `Ż` on
`[a, b)`, `Uᵀ U = 1` and `Zᵀ Z` invertible on `[a, b]`. The DO system (`Uᵀ U̇ = 0`,
`Ż = (F(t, Y))ᵀ U`, `U̇ (Zᵀ Z) = (1 - U Uᵀ) F(t, Y) Z`, `Y = U Zᵀ`) holds on `[a, b)` if and only
if `Y` is a DLRA solution of rank `r` that satisfies the gauge condition `Uᵀ U̇ = 0` on `[a, b)`.
The DDO statement is the mirror image for `Y = Z Vᵀ` with `Vᵀ V = 1`. In both, the hypotheses on
the factors are required on the closed interval `[a, b]`, because `IsDLRASolution` asks for rank
`r` at `b` too. The factors are given and differentiable: the theorems translate between two
descriptions of a given pair of factors and do not construct them.

@stmt LeanDLRA/DLRA/DynamicallyOrthogonal.lean isDLRASolution_of_bo DynamicallyOrthogonal.isDLRASolution_of_bo

Bi-orthogonal factors give a DLRA solution: with `Zᵀ Z = 1`, `Uᵀ U` invertible, a skew-symmetric
`Ω t` and the two equations for `U̇` and `Ż` above, `U Zᵀ` is a DLRA solution of rank `r`. Only
this direction is stated: the module docstring says that the converse needs differentiable
eigendecompositions of `Uᵀ U`. The file ends with three `example`s with `1 × 1` matrices in
which the DO, the BO and the DDO system hold.

Source: the module docstring names Koch and Lubich 2007 [KochLubich2007], Musharbash, Nobile and
Zhou 2015, and Cheng, Hou and Zhang 2013 for the three formulations. It states what is proved
here, that the first two are the same thing as the projected equation and that the BO system gives
a solution of it.

### 3.6 Existence and uniqueness of the DLRA solution

The theorems of sections 3.4 and 3.7 and of the later sections take a solution `Y` as a
hypothesis. The two files of this section show that a DLRA solution of rank `r` exists on short
intervals and is unique.

@stmt LeanDLRA/Foundations/AprioriExistence.lean exists_ODESolution_of_apriori_sublevel exists_ODESolution_of_apriori_sublevel

@stmt LeanDLRA/Foundations/AprioriExistence.lean exists_ODESolution_of_closedBall exists_ODESolution_of_closedBall

`Foundations/Existence.lean` (section 3.1) needs a field that is Lipschitz and bounded on the
whole space. The factor equations of dynamical low-rank approximation contain `S⁻¹` and are
Lipschitz and bounded only on a region. The first theorem treats such fields without a
continuation argument. Let `g` be a Lipschitz function of the state (`hg`) and `δ₁ < δ₂`; let `f`
be Lipschitz and bounded on the sublevel set `{g ≤ δ₂}` (`hL`, `hM`) and continuous in time there
(`hc`). Suppose that every solution of every damped equation `y' = c(y) f(t, y)`, with `c` of
values in `[0, 1]` and zero where `g > δ₂`, that starts at `y₀` has `g (y t) ≤ δ₁` on `[a, b]`
(`hpri`). Then `y' = f(t, y)`, `y a = y₀` has a solution on `[a, b]`, and it satisfies `g (y t) ≤
δ₁`. The proof multiplies the field by a Lipschitz cutoff (`isLipschitzField_cutoff_smul`,
`isBoundedField_cutoff_smul`). The second theorem is the local Picard–Lindelöf theorem: a field
that is Lipschitz and bounded by `M` on the closed ball of radius `δ` around `y₀` has a solution
on `[a, b]` with `M (b - a) < δ`, and `‖y t - y₀‖ ≤ M (t - a)`.

@stmt LeanDLRA/DLRA/Existence.lean IsDLRASolution.sub_le_singularValues IsDLRASolution.sub_le_singularValues

@stmt LeanDLRA/DLRA/Existence.lean IsDLRASolution.eqOn IsDLRASolution.eqOn

@stmt LeanDLRA/DLRA/Existence.lean exists_isDLRASolution exists_isDLRASolution

The first theorem: along a DLRA solution of rank `r` of a field bounded by `B`, the `r`-th
singular value can decrease at most with speed `B`. The second: two DLRA solutions of rank `r`
with the same value at `a` agree on `[a, b]`; the field is Lipschitz and bounded, and no lower
bound for the singular values is asked in the statement (the singular value is continuous and
positive along both solutions, so it has a positive minimum). The third theorem is existence and
uniqueness: for a field that is Lipschitz and bounded by `B` in the state and continuous in
time, and a start value `Y₀` of rank `r` with `B (b - a) < σ_{r-1}(Y₀)`, a DLRA solution of rank
`r` with `Y a = Y₀` exists on `[a, b]`, its `r`-th singular value stays above
`σ_{r-1}(Y₀) - B (t - a)`, and every DLRA solution of rank `r` with this start value agrees with
it. The smallness condition on `b - a` involves the smallest nonzero singular value of the start
value; for `r = 0` it cannot hold, and uniqueness (`IsDLRASolution.eqOn`) covers `r = 0`.

@stmt LeanDLRA/DLRA/Existence.lean exists_factors_isDLRASolution exists_factors_isDLRASolution

The same solution in factored form. For `U₀`, `V₀` with orthonormal columns and a core `S₀` with
`ρ ‖v‖ ≤ ‖S₀ v‖` and `B (b - a) < ρ`, the factor equations
`U̇ = (1 - U Uᵀ) F V S⁻¹`, `Ṡ = Uᵀ F V`, `V̇ = (1 - V Vᵀ) Fᵀ U S⁻ᵀ` (with `F = F t (U S Vᵀ)`) have
a solution on `[a, b]` with these starting values; the factors stay orthonormal, the core has
the lower bound `ρ - B (t - a)`, and `U S Vᵀ` is a DLRA solution of rank `r`.
`IsDLRASolution.exists_factors` gives the converse: a DLRA solution with
`B (b - a) < σ_{r-1}(Y a)` has factors of this kind. The solution is not continued past `b`;
the module docstring lists a solution up to the first time at which `σ_r` reaches zero, and fields
that are Lipschitz and bounded on a tube only, as open.

Source: the module docstring of `DLRA/Existence.lean` cites [KochLubich2007] for the factor
equations. The two statements on uniqueness and existence cite no theorem of a paper.

### 3.7 Quasi-optimality of the DLRA solution

Let `A` solve `A' = F(t, A)` and let `X` be a curve of rank-`r` matrices that are critical points
of the distance to `A`, `P(X) (A - X) = 0`, for example best approximations. The theorems of this
section bound the distance of the DLRA solution `Y` from `X` by the time integral of the
approximation error `‖X - A‖`. All norms are Frobenius norms, except where the spectral norm
`‖·‖₂` (`specNorm`) is written.

@stmt LeanDLRA/DLRA/QuasiOptimality.lean IsDLRASolution.norm_sub_le_integral IsDLRASolution.norm_sub_le_integral

`Y` is a DLRA solution of rank `r` (`hY`) of a field that is `L`-Lipschitz on the whole space
(`hF`); `A` solves the full equation (`hA`) with `‖F t (A t)‖ ≤ μ` (`hμ`). `X` is continuous
with right derivatives on `[a, b)` (`hXc`, `hX`), has rank `r` and `σ_{r-1}(X t) ≥ ρ > 0`
(`hXr`, `hσ`), satisfies the first-order condition (`hopt`) and stays within `ρ / 4` of `A`
(`hd`); `‖Y a - X a‖ ≤ δ` (`hδ`). Then for `t ∈ [a, b]`

`‖Y t - X t‖ ≤ e^{(L + 6 μ/ρ)(t - a)} (δ + (L + 4 μ/ρ) ∫ₐᵗ ‖X s - A s‖ ds)`.

The constants contain the lower bound `ρ` of the `r`-th singular value of `X`, as the constant
of section 2.4 does. No smallness of `‖Y - X‖` is assumed: the Lipschitz bound of the tangent
projector needs the lower bound at `X` only. The file has the variants for a curve `X` of best
approximations of rank at most `r` (`IsDLRASolution.norm_sub_le_integral_of_forall_norm_sub_le`),
the bound for `‖Y t - A t‖` (`dlra_norm_sub_le_add_integral`), and the differentiated first-order
condition `norm_tangentProjAt_sub_le_of_hasDerivWithinAt`, which gives `‖X'‖ ≤ 2 μ` and
`‖X' - P(X) A'‖ ≤ 4 μ ρ⁻¹ ‖A - X‖`. The case of section 3.4, `F(t, Y) = Ȧ(t)` and
`X t = truncation (A t) r`, is `dlra_norm_sub_truncation_le_integral`.

@stmt LeanDLRA/DLRA/QuasiOptimalityTube.lean IsDLRASolution.norm_sub_le_integral_of_isLipschitzOnTube IsDLRASolution.norm_sub_le_integral_of_isLipschitzOnTube

The same bound for a field that is `L`-Lipschitz only on the tube of radius `R` around `A`
(`IsLipschitzOnTube`), under the condition `hsmall` that the right-hand side added to
`‖X t - A t‖` stays below `R`. `IsDLRASolution.norm_sub_lt_of_isLipschitzOnTube` shows that then
the DLRA solution never leaves the tube, `‖Y t - A t‖ < R`. The proof extends the field to the
whole space (`tubeExt`) and uses a continuity argument (`bootstrap_of_continuousOn`); the
constants are those of the global case.

@stmt LeanDLRA/DLRA/QuasiOptimalityGap.lean IsDLRASolution.norm_sub_truncation_le_integral_of_gap IsDLRASolution.norm_sub_truncation_le_integral_of_gap

The curve `X` is the truncated singular value decomposition of the exact solution,
`X t = truncation (A t) r`, and the hypotheses on `X` are replaced by a gap
`ρ ≤ σ_{r-1}(A t) - σ_r(A t)` along the solution. Under the gap the truncation is
differentiable (section 2.7), so `t ↦ truncation (A t) r` has right derivatives; it is a best
approximation (section 2.2), and `σ_{r-1}(truncation (A t) r) ≥ ρ` (Weyl). The variant on a tube
is `IsDLRASolution.norm_sub_truncation_le_integral_of_gap_of_isLipschitzOnTube`.

@stmt LeanDLRA/DLRA/QuasiOptimalityMargin.lean IsDLRASolution.norm_sub_le_integral_of_margin IsDLRASolution.norm_sub_le_integral_of_margin

The margin `‖X t - A t‖ ≤ ρ / 4` of the first theorem is used once in its proof, to absorb the
differentiated first-order condition into the left-hand side of `‖X'‖ ≤ ‖P(X) A'‖ +
‖P(X) (A' - X')‖`. The theorem above replaces it by `‖X t - A t‖ ≤ θ ρ` with any `θ < 1 / 2`
(`hθ`, `hd`). Then `‖X'‖ ≤ μ / (1 - 2 θ)`
(`norm_le_div_of_tangentProjAt_sub_eq_zero`), and with `κ = 2 μ / ((1 - 2 θ) ρ)` the bound is

`‖Y t - X t‖ ≤ e^{(L + 2 μ/ρ + κ)(t - a)} (δ + (L + κ) ∫ₐᵗ ‖X s - A s‖ ds)`.

For `θ = 1 / 4` these are the constants of the first theorem of this section, and they are smaller
for `θ < 1 / 4`; the `example`s at the end of the file restate `dlra_norm_sub_le_integral` and
`IsDLRASolution.norm_sub_le_integral` and prove them from this theorem with `θ = 1 / 4`. What is
not shown in this theorem: it stops at `θ < 1 / 2`, since at `θ = 1 / 2` the absorbed inequality
says nothing. It uses the constant `2` of section 2.4; with the constant `1` of the same section
the margin reaches every `θ < 1`, as follows.

**Margins below `ρ`.** With the constant `1` of section 2.4 in place of the `2`, the same
argument works for every margin `θ < 1`. The file @file(LeanDLRA/DLRA/QuasiOptimalityNormal.lean)
differentiates the first-order condition with the constant `1`,
`‖P(X) (Ȧ - Ẋ)‖ ≤ ρ⁻¹ ‖Ẋ‖ ‖A - X‖` (`norm_tangentProjAt_sub_le_inv_mul_of_hasDerivWithinAt`),
which gives `‖Ẋ‖ ≤ μ / (1 - θ)` under `‖X - A‖ ≤ θ ρ`
(`norm_le_div_one_sub_of_tangentProjAt_sub_eq_zero`). The theorem:

@stmt LeanDLRA/DLRA/QuasiOptimalityNormal.lean IsDLRASolution.norm_sub_le_integral_of_margin_lt_one IsDLRASolution.norm_sub_le_integral_of_margin_lt_one

The hypotheses are those of `IsDLRASolution.norm_sub_le_integral_of_margin`, with `hθ : θ < 1` in
place of `2 θ < 1`. With `κ = μ / ((1 - θ) ρ)` the bound is

`‖Y t - X t‖ ≤ e^{(L + μ/ρ + κ)(t - a)} (δ + (L + κ) ∫ₐᵗ ‖X s - A s‖ ds)`.

For `2 θ < 1` both constants are at most those of section 3.7 above (the file restates
`dlra_norm_sub_le_integral_of_margin` and proves it from this theorem in an `example`); for
`θ = 1 / 4` they are `L + 7 μ / (3 ρ)` and `L + 4 μ / (3 ρ)` in place of `L + 6 μ / ρ` and
`L + 4 μ / ρ`. The version for `Y` as a solution of `Ẏ = P(Y) F(t, Y)` with factors
(`dlra_norm_sub_le_integral_of_margin_lt_one`) is in the same file. What is not shown: the
argument stops at `θ < 1`, since at `θ = 1` the inequality `(1 - θ) ‖Ẋ‖ ≤ μ` says nothing. The
module docstring says that the bound `‖Ẋ‖ ≤ μ / (1 - θ)` cannot be improved for any `θ < 1`, with
a family of curves in `ℝ²` that is not formalized in the core; nothing is claimed on the
optimality of the two constants of the theorem. The `example`s of the file show the hypotheses
at the margin `θ = 3 / 4` with `A ≠ X`.

**The other forms of the theorem.** The file @file(LeanDLRA/DLRA/QuasiOptimalitySharp.lean) carries
the bound with the margin `θ ρ`, `θ < 1`, to the forms that section 3.7 has with the margin
`ρ / 4`: the bound for the error against `A`
(`dlra_norm_sub_le_add_integral_of_margin_lt_one`), a curve `X` of best approximations of rank at
most `r` (`IsDLRASolution.norm_sub_le_integral_of_forall_norm_sub_le_of_margin_lt_one`), a field
that is Lipschitz on a tube only
(`IsDLRASolution.norm_sub_lt_of_isLipschitzOnTube_of_margin_lt_one`,
`IsDLRASolution.norm_sub_le_integral_of_isLipschitzOnTube_of_margin_lt_one`,
`IsDLRASolution.norm_sub_le_integral_of_forall_norm_sub_le_of_isLipschitzOnTube_of_lt_one`), and
the truncated singular value decomposition under a gap:

@stmt LeanDLRA/DLRA/QuasiOptimalitySharp.lean IsDLRASolution.norm_sub_truncation_le_integral_of_gap_of_margin_lt_one IsDLRASolution.norm_sub_truncation_le_integral_of_gap_of_margin_lt_one

Here `X t = truncation (A t) r`, the gap condition `ρ ≤ σ_{r-1}(A t) - σ_r(A t)` is that of
`IsDLRASolution.norm_sub_truncation_le_integral_of_gap`, the margin is
`‖truncation (A t) r - A t‖ ≤ θ ρ`, and the constants are those of the previous theorem. The
variant on a tube is
`IsDLRASolution.norm_sub_truncation_le_integral_of_gap_of_isLipschitzOnTube_of_lt_one`.
The file also has the Lipschitz constant of the projected field:

@stmt LeanDLRA/DLRA/QuasiOptimalitySharp.lean norm_tangentProjAt_field_sub_le_inv_mul norm_tangentProjAt_field_sub_le_inv_mul

For `F` that is `L`-Lipschitz and bounded by `B` (`hF`, `hB`) and `X`, `Y` of rank `r` with
`ρ ≤ σ_{r-1}(X)` the projected field `Y ↦ P(Y) F(t, Y)` is Lipschitz with the constant
`B / ρ + L`, in place of `2 B / ρ + L`. The `example`s of the file restate the theorems of the
files of the margin `ρ / 4` and prove them from the theorems of this file with `θ = 1 / 4`.

**The truncated singular value decomposition has rank `r`.** The theorems for
`X t = truncation (A t) r` need that `X t` has rank `r` and that `ρ ≤ σ_{r-1}(X t)` when
`ρ ≤ σ_{r-1}(A t)`. The file @file(LeanDLRA/DLRA/QuasiOptimality.lean) has these as lemmas, with a
factorization of the truncation:

@stmt LeanDLRA/DLRA/QuasiOptimality.lean EckartYoung.exists_truncation_eq_mul_diagonal_mul_transpose EckartYoung.exists_truncation_eq_mul_diagonal_mul_transpose

@stmt LeanDLRA/DLRA/QuasiOptimality.lean EckartYoung.rank_truncation_of_le_singularValues EckartYoung.rank_truncation_of_le_singularValues

@stmt LeanDLRA/DLRA/QuasiOptimality.lean EckartYoung.le_singularValues_truncation EckartYoung.le_singularValues_truncation

If the `r`-th singular value of `A` is at least `ρ > 0`, then `truncation A r` is `U diag(σ) Vᵀ`
with `r` orthonormal columns of `U` and of `V` and `σ i ≥ ρ`; hence it has rank `r` (and not only
at most `r`, `EckartYoung.rank_truncation_le`), and its `r`-th singular value is at least `ρ`
(for `0 < r`).

**The truncated singular value decomposition with the margin `θ ρ`.** For the case
`F(t, Y) = Ȧ(t)`, `X t = truncation (A t) r` of section 3.4 the file
@file(LeanDLRA/DLRA/QuasiOptimalityTruncation.lean) has the bound for every `θ < 1`, and the
corollary with the margin `ρ / 2`:

@stmt LeanDLRA/DLRA/QuasiOptimalityTruncation.lean dlra_norm_sub_truncation_le_integral_of_margin_lt_one dlra_norm_sub_truncation_le_integral_of_margin_lt_one

@stmt LeanDLRA/DLRA/QuasiOptimalityTruncation.lean dlra_norm_sub_truncation_le_integral_of_norm_sub_le_half dlra_norm_sub_truncation_le_integral_of_norm_sub_le_half

The hypotheses are those of `dlra_norm_sub_truncation_le_integral` of section 3.4 with the
margin `‖X t - A t‖ ≤ θ ρ` in place of `ρ / 16`. With `κ = μ / ((1 - θ) ρ)` the bound is
`‖Y t - X t‖ ≤ κ e^{(μ/ρ + κ) t} ∫₀ᵗ ‖X s - A s‖ ds`; for `θ = 1 / 2` the factor is
`2 μ / ρ` and the exponent `3 μ / ρ`. Under the recorded margin `ρ / 16` the theorem of
section 3.4 has the factor `2 β = 16 μ / ρ` and the exponent `β = 8 μ / ρ`; the corollary has
a weaker hypothesis (`ρ / 2` in place of `ρ / 16`) and the smaller constants `2 μ / ρ` and
`3 μ / ρ`. The `example`s of the file prove `dlra_norm_sub_truncation_le_integral` and the
recorded matrix form of the quasi-optimality theorem from the corollary, and show the
hypotheses for a curve with `A ≠ X`. Nothing is claimed on the optimality of the constants.

**The spectral norm of the tail.** In the theorems above the tail `A - X` enters through its
Frobenius norm, in the margin and in the integrand. The file
@file(LeanDLRA/DLRA/QuasiOptimalitySpectral.lean) uses the spectral norm `‖A - X‖₂ = specNorm`
where the differentiated first-order condition allows it, by means of the bounds of
section 2.4 on normal vectors with `‖N‖₂`:

@stmt LeanDLRA/DLRA/QuasiOptimalitySpectral.lean norm_le_div_one_sub_of_specNorm_sub_le norm_le_div_one_sub_of_specNorm_sub_le

The speed of a curve `X` of critical points (`P(X u) (A u - X u) = 0` on `s`, rank `r`,
`ρ ≤ σ_{r-1}(X u)`) with `‖Ȧ‖ ≤ μ` in the Frobenius norm is at most `μ / (1 - θ)` if
`‖X t - A t‖₂ ≤ θ ρ`, `θ < 1`. The file has the velocity bound
`‖X' - P(X t) A'‖ ≤ μ / ((1 - θ) ρ) ‖A t - X t‖₂`
(`norm_sub_tangentProjAt_le_div_one_sub_mul_specNorm`), and the quasi-optimality theorem:

@stmt LeanDLRA/DLRA/QuasiOptimalitySpectral.lean dlra_norm_sub_le_integral_of_specNorm_sub_le dlra_norm_sub_le_integral_of_specNorm_sub_le

With `κ = μ / ((1 - θ) ρ)` the bound is

`‖Y t - X t‖ ≤ e^{(L + μ/ρ)(t - a)} (δ + L ∫ₐᵗ ‖X s - A s‖ ds + κ ∫ₐᵗ ‖X s - A s‖₂ ds)`.

The exponent is `L + μ/ρ`, without the term `κ` of the theorem with the Frobenius norm. The proof
is Grönwall's inequality for `Y - X` with the splitting
`P(Y) F(Y) - Ẋ = P(Y) (F(Y) - F(A)) + (P(Y) - P(X)) F(A) + (P(X) F(A) - Ẋ)`, whose three terms are
at most `L ‖Y - A‖`, `(μ/ρ) ‖Y - X‖` (the constant `1` of section 2.4) and `κ ‖A - X‖₂`. The
Lipschitz term keeps the Frobenius norm of the tail, and `μ` bounds the field in the Frobenius
norm. The version for a DLRA solution is `IsDLRASolution.norm_sub_le_integral_of_specNorm_sub_le`.
Since `‖·‖₂ ≤ ‖·‖` the bounds of the Frobenius norm follow, and the file restates two of them in
`example`s.

For the truncated singular value decomposition the tail has a closed form,

@stmt LeanDLRA/Classical/EckartYoung.lean specNorm_sub_truncation specNorm_sub_truncation

so that the margin is a condition on the singular values, `σ_r(A t) ≤ θ ρ` with
`ρ ≤ σ_{r-1}(A t)` (singular values are indexed from zero). The theorem for `F(t, Y) = Ȧ(t)`:

@stmt LeanDLRA/DLRA/QuasiOptimalitySpectral.lean dlra_norm_sub_truncation_le_integral_of_singularValues_le dlra_norm_sub_truncation_le_integral_of_singularValues_le

The hypotheses are those of `dlra_norm_sub_truncation_le_integral_of_margin_lt_one`, with the
margin `σ_r(A t) ≤ θ ρ` in place of `‖X t - A t‖ ≤ θ ρ`; the bound is
`‖Y t - X t‖ ≤ κ e^{(μ/ρ) t} ∫₀ᵗ σ_r(A s) ds`. The form with `‖X t - A t‖₂` in the margin and the
integrand is `dlra_norm_sub_truncation_le_integral_of_specNorm_sub_le`. The integral of the
singular value `σ_r` replaces the integral of the Frobenius norm `(∑_{i ≥ r} σ_i²)^{1/2}` of
section 3.4, which is at least `σ_r`; the exponent has no term `κ`.

The module docstring cites the nearest published statements. The splitting above is that of
[FepponLermusiaux2018, Theorem 32], whose constants are pointwise, whose tail is measured in the
Frobenius norm and whose exponent has the constant `2`; the bound on the principal curvatures
`σ_r(A) / σ_{r-1}(A)` in the normal direction `A - X` is [FepponLermusiaux2018, Theorem 24], and
the speed bound `‖Ẋ‖ ≤ μ / (1 - σ_r / σ_{r-1})` is the first-order perturbation bound of the
truncated singular value decomposition [FepponLermusiaux2018, Theorem 25] and
[CarrelGanderVandereycken2023, Theorem 3.8]. The constants `ρ`, `μ`, `θ` of the file are uniform
on the interval. The `example`s of the file show the hypotheses for curves with `A ≠ X`.

**The theorems side by side.** `κ₁ = 2 μ / ((1 - 2 θ) ρ)` and `κ = μ / ((1 - θ) ρ)`; `Y` is a
DLRA solution, `X` a curve of critical points, `δ` the initial error. In the first four rows the
bound is `e^{E (t - a)} (δ + C ∫ₐᵗ g)` with the exponent `E`, the factor `C` and the integrand `g`
of the table; the last five rows are the case `F(t, Y) = Ȧ(t)`, `X t = truncation (A t) r`,
`L = 0`, `δ = 0`, and the bound is `C e^{E t} ∫₀ᵗ g`.

| Theorem | Hypothesis on the tail | Factor and exponent | Integrand | File |
|---|---|---|---|---|
| `IsDLRASolution.norm_sub_le_integral` | `‖X - A‖ ≤ ρ / 4` | `L + 4 μ/ρ`; `L + 6 μ/ρ` | `‖X - A‖` | @file(LeanDLRA/DLRA/QuasiOptimality.lean) |
| `IsDLRASolution.norm_sub_le_integral_of_margin` | `‖X - A‖ ≤ θ ρ`, `2 θ < 1` | `L + κ₁`; `L + 2 μ/ρ + κ₁` | `‖X - A‖` | @file(LeanDLRA/DLRA/QuasiOptimalityMargin.lean) |
| `IsDLRASolution.norm_sub_le_integral_of_margin_lt_one` | `‖X - A‖ ≤ θ ρ`, `θ < 1` | `L + κ`; `L + μ/ρ + κ` | `‖X - A‖` | @file(LeanDLRA/DLRA/QuasiOptimalityNormal.lean) |
| `IsDLRASolution.norm_sub_le_integral_of_specNorm_sub_le` | `‖X - A‖₂ ≤ θ ρ`, `θ < 1` | `L` and `κ`; `L + μ/ρ` | `‖X - A‖` with `L`, `‖X - A‖₂` with `κ` | @file(LeanDLRA/DLRA/QuasiOptimalitySpectral.lean) |
| `dlra_norm_sub_truncation_le_integral` | `‖X - A‖ ≤ ρ / 16` | `16 μ/ρ`; `8 μ/ρ` | `‖X - A‖` | @file(LeanDLRA/DLRA/QuasiOptimality.lean) |
| `dlra_norm_sub_truncation_le_integral_of_margin_lt_one` | `‖X - A‖ ≤ θ ρ`, `θ < 1` | `κ`; `μ/ρ + κ` | `‖X - A‖` | @file(LeanDLRA/DLRA/QuasiOptimalityTruncation.lean) |
| `dlra_norm_sub_truncation_le_integral_of_norm_sub_le_half` | `‖X - A‖ ≤ ρ / 2` | `2 μ/ρ`; `3 μ/ρ` | `‖X - A‖` | @file(LeanDLRA/DLRA/QuasiOptimalityTruncation.lean) |
| `dlra_norm_sub_truncation_le_integral_of_specNorm_sub_le` | `‖X - A‖₂ ≤ θ ρ`, `θ < 1` | `κ`; `μ / ρ` | `‖X - A‖₂` | @file(LeanDLRA/DLRA/QuasiOptimalitySpectral.lean) |
| `dlra_norm_sub_truncation_le_integral_of_singularValues_le` | `σ_r(A) ≤ θ ρ`, `θ < 1` | `κ`; `μ / ρ` | `σ_r(A)` | @file(LeanDLRA/DLRA/QuasiOptimalitySpectral.lean) |

In all rows `ρ` is a lower bound of `σ_{r-1}(X)` (for the truncation, of `σ_{r-1}(A)`), and `μ`
bounds `‖F(t, A t)‖` (for the truncation, `‖Ȧ‖`) in the Frobenius norm. The first four rows take a
field `F` that is `L`-Lipschitz on the whole space; the forms for a field
that is Lipschitz on a tube, for a curve of best approximations, for the error against `A` and
for the truncation under a gap are in the files named above. The factor of the fifth row is
`2 β`, `β = 8 μ / ρ`.

What is not shown. A DLRA solution `Y` is a hypothesis of all of these theorems; section 3.6
gives existence only on intervals with `B (b - a) < σ_{r-1}(Y a)`, and the two are not combined
here. The bound is quasi-optimality in the sense of the time integral of the best-approximation
error, with a factor `e^{(L + 6 μ/ρ)(t - a)}` that grows when `ρ` is small; no statement is made for
`ρ` going to zero. The module docstrings say that the constants `ρ / 4`, `6 μ / ρ`, `4 μ / ρ` are
those of their own proofs, and that a bound of this kind is in [KochLubich2007]. The tube
hypotheses are those of [ZhaoOstermannGu2021]. The theorems with a margin below `ρ` and with the
spectral norm keep the hypotheses that `X` is a curve of critical points with `σ_{r-1}(X) ≥ ρ`
and that the margin holds on the whole interval; they say nothing for a margin `θ ≥ 1`, and the
table above lists the constants of the proofs, not optimal ones. The growth rates in which the
velocity enters through its normal component only are in section 3.8.

### 3.8 Quasi-optimality with the normal velocity as growth rate

In the bounds of section 3.7 the growth rate is `L + μ/ρ`, where `μ` bounds the whole velocity
`‖F(t, A t)‖` of the exact solution. The files of this section bound the error `‖Y - X‖` of a
DLRA solution `Y` against a curve `X` of rank-`r` matrices with a rate in which the velocity
enters at leading order only through its component `ν ≥ ‖(1 - P(X)) F(t, A t)‖` normal to the
manifold at `X`; the whole velocity is multiplied by the radius `ε < ρ` of a tube around `X`
that contains `Y`. All norms are Frobenius norms except where `‖·‖₂` or `specNorm` is written.

**The rate `L + ν/ρ + ν/(ρ - ε) + μ ε/ρ²`.** The file
@file(LeanDLRA/DLRA/QuasiOptimalityNormalVelocity.lean) pairs the two tangent projectors with the
error. For `X`, `Y` of rank `r` with `ρ ≤ σ_{r-1}(X)`, `ρ' ≤ σ_{r-1}(Y)`:

@stmt LeanDLRA/DLRA/QuasiOptimalityNormalVelocity.lean inner_sub_tangentProjAt_sub_le_norm_sq_mul inner_sub_tangentProjAt_sub_le_norm_sq_mul

Only the component of `Ẏ - Ẋ` along `Y - X` changes `‖Y - X‖`, so the term
`(P(Y) - P(X)) F(t, A t)` enters through its inner product with `Y - X`, which is the sum of two
inner products of normal components; the normal components `(1 - P(Y)) X` and `(1 - P(X)) Y` are
of second order in `‖Y - X‖` (section 2.4). The theorem for a solution that is not assumed to
stay in the tube: the bound itself has to stay below `ε`.

@stmt LeanDLRA/DLRA/QuasiOptimalityNormalVelocity.lean IsDLRASolution.norm_sub_le_integral_exp_integral_of_integral_lt IsDLRASolution.norm_sub_le_integral_exp_integral_of_integral_lt

The curve `X` is any differentiable curve of rank-`r` matrices: it need not consist of critical
points of the distance to `A`, and `A` need not solve the differential equation; both enter
through the defect `d ≥ ‖P(X) F(t, A t) - Ẋ‖` and through `‖X - A‖`. The module docstring names
the Weingarten map of [FepponLermusiaux2018, Proposition 22] as the growth generator at leading
order. For `X t = truncation (A t) r` under the gap `σ_r(A t) < σ_{r-1}(A t)`, with
`ρ = σ_{r-1}(A t)` and the defect bound `μ σ_r/(σ_{r-1} - σ_r)`:

@stmt LeanDLRA/DLRA/QuasiOptimalityNormalVelocity.lean IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_integral_lt IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_integral_lt

**The defect of the truncation.** Let `X` be a curve of critical points (`P(X)(A - X) = 0`, the
truncated singular value decomposition is one) with tail `R = A - X`, `τ = ‖R‖₂ < ρ ≤ σ_{r-1}(X)`.
With the Moore–Penrose inverse `X⁺` and `W(Z) = (X⁺)ᵀ Zᵀ R + R Zᵀ (X⁺)ᵀ` the file
@file(LeanDLRA/DLRA/QuasiOptimalityDefect.lean) gives the defect in closed form,

@stmt LeanDLRA/DLRA/QuasiOptimalityDefect.lean tangentProjAt_sub_eq_neg_pinv_transpose_mul_add_of_hasDerivWithinAt tangentProjAt_sub_eq_neg_pinv_transpose_mul_add_of_hasDerivWithinAt

that is, `P(X)(Ȧ - Ẋ) = -W(Ẋ)`, and bounds it from both sides by `W(Ȧ)`:

@stmt LeanDLRA/DLRA/QuasiOptimalityDefect.lean norm_sub_tangentProjAt_le_div_sub_mul_norm_pinv_transpose_mul_add norm_sub_tangentProjAt_le_div_sub_mul_norm_pinv_transpose_mul_add

@stmt LeanDLRA/DLRA/QuasiOptimalityDefect.lean norm_pinv_transpose_mul_add_le_one_add_mul_norm_sub_tangentProjAt norm_pinv_transpose_mul_add_le_one_add_mul_norm_sub_tangentProjAt

The two bounds differ by the factor `(ρ + τ)/(ρ - τ)`. `W(Z)` sees only the two mixed blocks
`Pu Z (1 - Pv)` and `(1 - Pu) Z Pv` of `Z` (`Pu`, `Pv` the projectors onto the column and the row
space of `X`), so `‖P(X) Ȧ - Ẋ‖ ≤ μ τ/(ρ - τ)` holds with `μ` a bound of the mixed blocks of `Ȧ`
only. The quasi-optimality theorem against the truncation, with the source
`ρ/(ρ - τ) ω s`, `ω ≥ ‖W(F(t, A t))‖`, in place of `μ σ_r/(σ_{r-1} - σ_r)`:

@stmt LeanDLRA/DLRA/QuasiOptimalityDefect.lean IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_norm_pinv_le IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_norm_pinv_le

**Spectral norms of the normal components, and an a posteriori form.** The file
@file(LeanDLRA/DLRA/QuasiOptimalityNormalVelocitySpectral.lean) has the pairing of the two
projectors with spectral norms of the normal components and the factor `(1 + s)/2`, where `s₁`,
`s₂` are the products of the sines of the largest angles between the column spaces and between
the row spaces of `X` and `Y`:

@stmt LeanDLRA/DLRA/QuasiOptimalityNormalVelocitySpectral.lean inner_sub_tangentProjAt_sub_le_half_mul_specNorm inner_sub_tangentProjAt_sub_le_half_mul_specNorm

To leading order in `‖Y - X‖` the rate is `‖(1 - P(X)) Z‖₂/σ_{r-1}(X)`, half of the rate of the
Frobenius form and with the spectral norm. The a posteriori form has the singular value
`σ_{r-1}(Y t)`, the normal components at `Y` and the sines measured on the computed solution; it
needs no smallness condition:

@stmt LeanDLRA/DLRA/QuasiOptimalityNormalVelocitySpectral.lean IsDLRASolution.norm_sub_le_integral_exp_integral_of_specNorm_sub_tangentProjAt_le IsDLRASolution.norm_sub_le_integral_exp_integral_of_specNorm_sub_tangentProjAt_le

**Constants that depend on time.** The bounds of section 3.7 have `ρ`, `μ`, `θ` constant on the
interval. In @file(LeanDLRA/DLRA/QuasiOptimalityTimeLocal.lean) they are functions of time, with
`τ(s) = ‖X s - A s‖₂ < ρ(s)`. For the truncation under the gap, with `ρ(t) = σ_{r-1}(A t)` and
no hypothesis on the curve besides the gap:

@stmt LeanDLRA/DLRA/QuasiOptimalityTimeLocal.lean IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_singularValues_lt IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_singularValues_lt

The module docstring restates `dlra_norm_sub_le_integral_of_specNorm_sub_le` as an `example` and
derives the bound of [FepponLermusiaux2018, Theorem 32] from it (kernel `e^{η (t - s)}` with
`η ≥ L + 2 ‖F(t, A t)‖/σ_{r-1}(A t)`, gap term with the Frobenius norm of the tail).

**The speed and velocity bounds are attained.** For a curve of critical points with the margin
`‖X - A‖ ≤ θ ρ`, `θ < 1`, the file @file(LeanDLRA/DLRA/QuasiOptimalityNormal.lean) has
`‖P(X)(Ȧ - Ẋ)‖ ≤ ρ⁻¹ ‖Ẋ‖ ‖A - X‖`, `‖Ẋ‖ ≤ μ/(1 - θ)` and
`‖Ẋ - P(X) Ȧ‖ ≤ μ/((1 - θ) ρ) ‖A - X‖`. The file
@file(LeanDLRA/DLRA/QuasiOptimalitySpeedSharp.lean) shows that all three are equalities for the
rotating projector of rank one in `ℝ²`, `X t = u uᵀ`, `A t = θ • 1 + (1 - θ) • X t`,
`u = (cos t, sin t)`, for every `θ` with `0 ≤ θ < 1`:

@stmt LeanDLRA/DLRA/QuasiOptimalitySpeedSharp.lean norm_sub_tangentProjAt_eq QuasiOptimalitySpeedExample.norm_sub_tangentProjAt_eq

@stmt LeanDLRA/DLRA/QuasiOptimalitySpeedSharp.lean exists_mul_div_lt_norm_deriv exists_mul_div_lt_norm_deriv

The second theorem says that for every `c < 1` there are curves that satisfy the hypotheses with
`c μ/(1 - θ) < ‖Ẋ‖`. Not shown: the quasi-optimality bounds that are derived from the velocity
bound by Grönwall's inequality are not shown to be attained.

**A tangential stiff part.** Let `F(t, Z) = S(t, Z) + G(t, Z)`, where `S` maps every matrix of
rank `r` into the tangent space at that matrix; the main case is the Sylvester operator
`S(Z) = M Z + Z N`, whose norm grows with the mesh refinement. The tangent projector does not see
`S`, so `Y` solves `Ẏ = S(t, Y) + P(Y) G(t, Y)`. In
@file(LeanDLRA/DLRA/QuasiOptimalityStiff.lean) the stiff part enters only through the one-sided
Lipschitz constant `ℓ` of `F` (which may be negative) and through the defect
`d ≥ ‖S(t, X t) + P(X t) G(t, A t) - Ẋ t‖` of the curve; the Lipschitz constant and the size of
`S` do not occur:

@stmt LeanDLRA/DLRA/QuasiOptimalityStiff.lean IsDLRASolution.norm_sub_le_integral_exp_integral_of_tangent_add_of_integral_lt IsDLRASolution.norm_sub_le_integral_exp_integral_of_tangent_add_of_integral_lt

Here `L` is the Lipschitz constant of `G`, `μ ≥ ‖G(t, A t)‖` and `ν ≥ ‖(1 - P(X t)) G(t, A t)‖`.
The case `F(t, Z) = M Z + Z N + G(t, Z)` is `…_of_sylvester_add_of_integral_lt` of the same file.
For the truncated singular value decomposition of a solution `A` with a gap,
@file(LeanDLRA/DLRA/QuasiOptimalityStiffTruncation.lean) bounds the source `d` by the defect of
the truncation plus `κ ‖A - T‖`, where `κ` measures how far the tangent space at `T` is from
being invariant under the adjoint of `S`:

@stmt LeanDLRA/DLRA/QuasiOptimalityStiffTruncation.lean IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_sylvester_add IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_sylvester_add

The stiff part enters the source through the failure of the tangent space at `T` to be invariant
under `S'`, `‖(1 - P(T)) S' P(T) w‖ ≤ κ ‖w‖`, and not through its norm.

**The theorems side by side.** `Y` is a DLRA solution of rank `r`, `δ` the initial error, the
bound is `e^{∫ k} δ + ∫ e^{∫ₛᵗ k} (source)`, and `ε < ρ` is the radius of a tube that the bound
itself must stay below.

| Theorem | Growth rate `k` | Source | File |
|---|---|---|---|
| `IsDLRASolution.norm_sub_le_integral_exp_integral_of_integral_lt` | `L + ν/ρ + ν/(ρ - ε) + μ ε/ρ²` | `L ‖X - A‖ + d` | @file(LeanDLRA/DLRA/QuasiOptimalityNormalVelocity.lean) |
| `IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_integral_lt` | the same, `ρ = σ_{r-1}(A)` | `L ‖T - A‖ + μ σ_r/(σ_{r-1} - σ_r)` | @file(LeanDLRA/DLRA/QuasiOptimalityNormalVelocity.lean) |
| `IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_norm_pinv_le` | the same | `L ‖T - A‖ + ρ/(ρ - τ) ω` | @file(LeanDLRA/DLRA/QuasiOptimalityDefect.lean) |
| `IsDLRASolution.norm_sub_le_integral_exp_integral_of_specNorm_sub_tangentProjAt_le` | `L + (1 + ς)/2 (ν'/ρ + ν/ρ')` | `L ‖X - A‖ + d` | @file(LeanDLRA/DLRA/QuasiOptimalityNormalVelocitySpectral.lean) |
| `IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_singularValues_lt` | `L + μ(t)/ρ(t)` | `L ‖T - A‖ + μ/(ρ - τ) τ` | @file(LeanDLRA/DLRA/QuasiOptimalityTimeLocal.lean) |
| `IsDLRASolution.norm_sub_le_integral_exp_integral_of_tangent_add_of_integral_lt` | `ℓ + ν/ρ + ν/(ρ - ε) + μ ε/ρ² + L ε/ρ` | `L ‖X - A‖ + d` | @file(LeanDLRA/DLRA/QuasiOptimalityStiff.lean) |
| `IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_sylvester_add` | the same, `ρ = σ_{r-1}(A)` | `L ‖T - A‖ + ρ/(ρ - τ) ω + κ ‖T - A‖` | @file(LeanDLRA/DLRA/QuasiOptimalityStiffTruncation.lean) |

In the third and fourth rows `τ`, `ω`, `ς`, `ν'`, `ρ'` are the quantities of the statements above
(the tail, the Weingarten map of the velocity, the sines, the normal component at `Y` and the
singular value at `Y`). The last two rows are for `F = S + G` with `S` tangential.

What is not shown. A DLRA solution `Y` is a hypothesis; the smallness condition on the bound
(`hB`) is a hypothesis on the data and is not derived. No statement is made for `ρ` going to
zero, and the constants are those of the proofs. In the stiff rows the stiff part `S` must map
the matrices of rank `r` into their tangent spaces (`hS`), and the numbers `d` or `κ` are
data; the files do not bound them for a given discretization beyond the formulas above.

Literature. The pairing of the projectors with normal components is the mechanism of the curvature
estimates of [FepponLermusiaux2018] (Proposition 22, Theorems 24, 25, 32). A stiffness-uniform
DLRA error bound against the exact solution with the one-sided constant is published, with a term
for the rank-`r` approximation error and not a best-approximation term, in
[CarrelVandereycken2023] (Theorem 7) and [KieriVandereycken2019] (Lemma 1); the bounds of this
section are against a best approximation or a curve of critical points, and no priority claim is
made. The hypothesis that the stiff part is tangential is the standard one of Bachmayr, Eisenmann,
Kieri and Uschmajew (arXiv 2002.12197, assumption A4) and of [KochLubich2007].

**Grönwall's inequality with a time-dependent rate.** The bounds of this section have a rate
`k(t)` that depends on time. Mathlib's `gronwallBound` and `gronwallIntegralBound` solve the
comparison equation `u' = K u + η` with a constant `K`. The file
@file(LeanDLRA/Analysis/GronwallVariableRate.lean) compares with the solution of
`u' = k(t) u + g(t)`, `u(a) = δ`, for continuous `k` and `g`, without a sign condition on `k`,
`g` or `δ`:

@stmt LeanDLRA/Analysis/GronwallVariableRate.lean norm_le_exp_integral_mul_add_integral_exp_integral_mul norm_le_exp_integral_mul_add_integral_exp_integral_mul

In an inner product space only the component of `f'` along `f` changes `‖f‖`. The file
@file(LeanDLRA/Analysis/GronwallInner.lean) has the same conclusion under the one-sided bound
`⟪f, f'⟫ ≤ (k ‖f‖ + g) ‖f‖` with `g ≥ 0` on `[a, b)`, and no bound on the part of `f'` orthogonal
to `f`:

@stmt LeanDLRA/Analysis/GronwallInner.lean norm_le_exp_integral_mul_add_integral_exp_integral_mul_of_inner_le norm_le_exp_integral_mul_add_integral_exp_integral_mul_of_inner_le

The condition `0 ≤ g` cannot be dropped: `f = 0` satisfies the hypothesis for every `g`.

### 3.9 Optimality of low-rank time integration

The sections above bound the error of a method against the exact solution or against a best
approximation. The files of this section ask how much a method can achieve at all when it uses the
field only on matrices of low rank, what a method with a full state achieves with the same
information, what a state of rank `r` costs, and what a tolerance truncation does to the rank of a
run, for several truncation rules. `distLR k Z` is the distance of `Z` from the matrices of rank
at most `k` (`lowRankSet`), `L` is a Lipschitz constant of the field `F` and `A` the exact
solution. Norms are Frobenius norms. The constants are those of the proofs, and the statements
are for the matrix case.

**A lower bound for the information on matrices of rank at most `k`.** A method of rank `k` for
`y' = F(t, y)` uses the field only through values `F(t, Z)` at matrices `Z` of rank at most `k`.
Two fields that agree on these matrices are treated alike by every such method, adaptive or not,
whatever the output is. In @file(LeanDLRA/Research/InformationLowerBound.lean):

@stmt LeanDLRA/Research/InformationLowerBound.lean half_norm_sub_le_max_error InformationLowerBound.half_norm_sub_le_max_error

`Φ` maps a field to the output, and `S` is the set of points at which the field is evaluated. If
the solutions `A₁`, `A₂` of two fields that agree on `S` differ, the output has error at least
`‖A₁ - A₂‖ / 2` for one of the two fields. Two fields `G ± c distLR k(·) W` agree with `G` on the
matrices of rank at most `k`, and the perturbation raises the Lipschitz constant by at most
`|c| ‖W‖`:

@stmt LeanDLRA/Research/InformationLowerBound.lean isLipschitzField_add_distLR_smul InformationLowerBound.isLipschitzField_add_distLR_smul

`InformationLowerBound.isOneSidedLipschitzField_add_distLR_smul` is the same for the one-sided
Lipschitz constant. For `2 × 2` matrices, `k = 1`, the constant field `G = e₂e₂ᵀ`, `W = e₁e₁ᵀ`
and the start `a e₁e₁ᵀ`, the solutions of the two fields are `diag(a ± L t²/2, t)` with
`distLR 1 = t`, and their distance at `T` is `L T² = 2 L ∫₀ᵀ distLR 1 (A(s)) ds`:

@stmt LeanDLRA/Research/InformationLowerBound.lean mul_integral_distLR_le_max_error InformationLowerBoundExample.mul_integral_distLR_le_max_error

So for `0 ≤ T`, `T + L T²/2 ≤ a` and every `Φ` that depends on the field only through the
matrices of rank at most one, one of the two `L`-Lipschitz fields has an error of at least
`L ∫₀ᵀ distLR 1 (A(s)) ds`. The constant `1` in front of `L ∫ distLR` cannot be raised for this
information: if `F` is `L`-Lipschitz and equals a constant `B` on the matrices of rank at most
`k`, the output `A(0) + T B` has the error

@stmt LeanDLRA/Research/InformationLowerBound.lean norm_sub_affine_le_integral_distLR InformationLowerBound.norm_sub_affine_le_integral_distLR

and for the two fields of the pair above this output has the error exactly
`L T²/2 = L ∫₀ᵀ distLR 1 (A(s)) ds`, because
`InformationLowerBoundExample.norm_pairSol_sub_central` gives `|c| T²/2`. The bound does not apply
to every field: a linear field is determined by its values on the matrices of rank at most one,

@stmt LeanDLRA/Research/InformationLowerBound.lean linearMap_ext_of_rank_le_one InformationLowerBound.linearMap_ext_of_rank_le_one

so no pair of linear fields agrees on them. What is not shown: the bound is for the information,
that is, for maps that depend on `F` only through its restriction to the matrices of rank at most
`k`; it is not a bound for DLRA or for a method that evaluates `F` elsewhere. The pair of this
paragraph is for `2 × 2` matrices and rank one (all sizes are treated below), and polynomial fields
are not treated.

**All sizes and ranks, and a dissipative pair.** In
@file(LeanDLRA/Research/InformationLowerBoundGeneral.lean) the pair is given for `m × n` matrices
and every rank `k` with `1 ≤ k`, `k + 1 ≤ m` and `k + 1 ≤ n`. Two matrices `U`, `V` with `k + 1`
orthonormal columns embed the diagonal construction of size `k + 1`: with `W = u₁ v₁ᵀ` and
`B = u_{k+1} v_{k+1}ᵀ` the fields are `F_c(t, Z) = B + c distLR k Z · W` and the solutions are
`A_c(t) = U diag(a + c t²/2, a, …, a, t) Vᵀ`, as long as `T + |c| T²/2 ≤ a`. The distance of
`U diag(d) Vᵀ` from the matrices of rank at most `r` is at least `min |dᵢ|`
(`InformationLowerBoundGeneral.le_distLR_mul_diagonal_mul_transpose`), which gives
`distLR k (A_c(t)) = t`.

@stmt LeanDLRA/Research/InformationLowerBoundGeneral.lean exists_lowRank_information_pair InformationLowerBoundGeneral.exists_lowRank_information_pair

The two fields are `L`-Lipschitz and agree on the matrices of rank at most `k`, the solutions start
at the same matrix of rank at most `k`, and every output that depends on the field only through
these matrices has the error `L ∫₀ᵀ distLR k (A₁(s)) ds` or more for one of the two fields. The
`example` of the file is the case of `3 × 4` matrices, `k = 2`, `L = T = 1` and `a = 2`. The
version with an explicit frame is
`InformationLowerBoundGeneralExample.mul_integral_distLR_le_max_error`, and
`InformationLowerBoundGeneralExample.norm_frameSol_sub_central` gives the error `|c| T²/2` of the
output `A(0) + T B` for both fields, as in the `2 × 2` pair above.

The second pair of the file is dissipative. With `G(Z) = μ A₀ + B - μ Z` and the fields
`F_± = G ± L distLR k(·) W`, `0 ≤ L` and `0 < μ`, the fields are one-sided Lipschitz with the
constant `L - μ` (`InformationLowerBoundGeneralExample.isOneSidedLipschitzField_dissField`),
Lipschitz with the constant `μ + L`, and agree on the matrices of rank at most `k`. The solutions
are `A_±(t) = A₀ ± z(t) W + y(t) B` with `y(t) = (1 - e^{-μ t})/μ` and
`z(t) = L (1 - e^{-μ t} - μ t e^{-μ t})/μ²`. For `1/μ + L/μ² ≤ a`:

@stmt LeanDLRA/Research/InformationLowerBoundGeneral.lean mul_integral_exp_distLR_le_max_error InformationLowerBoundGeneralExample.mul_integral_exp_distLR_le_max_error

and the term of the lower bound is at most `L / μ` times the distance at the final time:

@stmt LeanDLRA/Research/InformationLowerBoundGeneral.lean mul_integral_exp_distLR_dissSol_le InformationLowerBoundGeneralExample.mul_integral_exp_distLR_dissSol_le

For this pair the forced error is therefore at most `L / μ` times the best-approximation error at
the final time; it is not of the size `L ∫ distLR`. The weight `e^{-μ (T - s)}` is not the weight
`e^{ℓ (T - s)}`, `ℓ = L - μ`, of the usual upper bounds for one-sided Lipschitz fields (the two
differ by the factor `e^{L (T - s)}`), so the lower bound is not shown to match an upper bound.
What is not shown: `k = 0` is excluded (the construction needs `W ⊥ B`); the sharpness is the
identity for the pair only, the general upper bound is
`InformationLowerBound.norm_sub_affine_le_integral_distLR`; the dissipative pair is one family and
gives no upper bound for the dissipative class; two further pairs of the paper (one with `W = B`,
one by a determinant) are not in the core.

**A full state with the same information.** A method that evaluates `F` only at matrices of rank at
most `k` but keeps a full matrix as its state has an error bound of the same form. If a curve `Z`
satisfies `‖Ż - F(t, Z)‖ ≤ L distLR k Z + η`, for example `Ż = F(t, W)` with `W` a best
approximation of rank at most `k` of `Z` (`η = 0`;
`RankInformationUpperBound.norm_sub_le_mul_distLR_of_norm_sub_eq`) or the interpolant of an
explicit Euler method with these field values (`η` its consistency error), then in
@file(LeanDLRA/Research/RankInformationUpperBound.lean):

@stmt LeanDLRA/Research/RankInformationUpperBound.lean norm_sub_le_exp_mul_add_integral_distLR RankInformationUpperBound.norm_sub_le_exp_mul_add_integral_distLR

Neither a singular value of `A` or `Z` nor a gap enters. With the lower bound above, the worst case
of the information on matrices of rank at most `k` is determined up to the factor `e^{2LT}`. A best
approximation of rank at most `r` of the result has the error

@stmt LeanDLRA/Research/RankInformationUpperBound.lean norm_sub_le_distLR_add_two_mul RankInformationUpperBound.norm_sub_le_distLR_add_two_mul

What is not shown: the state is a full matrix, so the statement says nothing about a method at
low-rank cost. The example of the file is the rotating projector `X(t) = u(t) u(t)ᵀ` of
@file(LeanDLRA/DLRA/QuasiOptimalitySpeedSharp.lean) with the data `A(t) = X(t) + ε (1 - X(0))` and
the field `F(t, Z) = Ẋ(t)` (Lipschitz constant `0`):

@stmt LeanDLRA/Research/RankInformationUpperBound.lean dlra_error_eq_at_rank_one RankInformationUpperBoundExample.dlra_error_eq_at_rank_one

`X` is the DLRA solution of rank one from the best approximation `X(0)` of `A(0) = diag(1, ε)`,
its error is `ε` at every time, also at `t = π/2`, where the data have rank one, while the full
state `Z = A` of the bound above has the error `0`.

**The price of a state of rank `r`.** For a field without dependence on the state,
`F(t, Z) = Ȧ(t)` (Lipschitz constant `0`), a method that integrates `Ȧ` and truncates has the
error `distLR r (A(T))`. The projected equation `Ẏ = P(Y) Ȧ` of rank `r` loses the part of `Ȧ`
that is normal at `Y`, and the loss adds up while the tangent space turns. In
@file(LeanDLRA/Research/RankStatePrice.lean) the family in `ℝ^{2 × 2}` with `r = 1`,
`u(t) = (cos t, sin t)`, `Y t = u(t) e₁ᵀ` and
`A t = u(t) (e₁ + ε t e₂)ᵀ + ε u⊥(t) e₂ᵀ` has the following properties.

@stmt LeanDLRA/Research/RankStatePrice.lean dlra_error_eq_mul_sqrt RankStatePriceExample.dlra_error_eq_mul_sqrt

`Y` is the solution of rank one of the projected equation from a best approximation of `A 0`, the
distance of `A t` from the matrices of rank one is at most `ε` at all times, and the error of `Y`
is `ε √(1 + t²)`: it grows with the angle through which the tangent space has turned, while the
best-approximation error stays below `ε`. The second column of `A` is `ε` times an involute of the
unit circle, whose velocity `ε t u⊥(t)` is normal at `Y t` at every time. That the DLRA error is
not bounded by a multiple of the best-approximation error that is uniform in time is known at
eigenvalue crossings [MusharbashNobileZhou2015, §5.3]; in the family the best approximation of
rank one stays within `ε` of `A t` and the error is an equality. A lower bound for a class of
methods of rank one is stated next.

**Oblique tangent projectors on rank-one states.** The family above is one in which the projected
equation loses `ε` per radian of turning. In
@file(LeanDLRA/Research/ObliqueProjectorLowerBound.lean) the same is shown for a class of methods,
for `2 × 2` matrices, rank one and a field `Ȧ` without dependence on the state (`L = 0`). A method
of the form `Ẏ = Π(Y) Ȧ` has `Π(Y)` linear, the identity on the tangent space `{X : ⟪N, X⟫ = 0}`
and with range in it (an oblique projector onto the tangent space; the projected equation is the
orthogonal one). The hypotheses are imposed only along the circle of states `Y(θ) = u(θ) e₁ᵀ`,
`u(θ) = (cos θ, sin θ)`, with the unit normal `N(θ) = u⊥(θ) e₂ᵀ`, together with the continuity of
`θ ↦ Π(Y(θ)) N(θ)`:

@stmt LeanDLRA/Research/ObliqueProjectorLowerBound.lean exists_data_two_pi_mul_le_norm_sub ObliqueProjectorLowerBound.exists_data_two_pi_mul_le_norm_sub

For every method of the class and every `ε ≥ 0`, `k : ℕ`, there are data of initial error `ε` whose
normal component `⟪N(Y), A - Y⟫` stays `±ε`, while the state turns by `2π k`, and on which the error
is at least `2π k ε` at the end. The data depend on the method. Here `ε` is the normal component of
the error, not the distance of `A` from the matrices of rank one: for a general `Π` nothing is
proved about `distLR 1 (A t)`, and when `distLR 1 (A (2π k)) ≥ 2π k ε` the bound holds for every
matrix of rank one and says nothing about the method. The last conjunct gives the distance in a
subclass: if `Π(Y(θ)) N(θ)` has a zero left column for every `θ`, as for the family
`ObliqueProjectorLowerBoundExample.tangentObliqueProj κ`, `Π_κ(Y) a = a - ⟪N, a⟫ (N + κ B)`, whose
member `κ = 0` is the orthogonal projection on the circle, then `distLR 1 (A t) ≤ ε` for all `t`.
In that subclass `ε` bounds the best-approximation error and the method loses at least `ε` per
radian of turning, as the projected equation does on the family of
@file(LeanDLRA/Research/RankStatePrice.lean). The `example` of the file is the member `κ = 1/2`
(not the orthogonal projection) with `ε = 1/10` and one turn.

What is not shown: only `2 × 2` matrices, rank one and `L = 0`, in continuous time; the reduction
of one-step maps `Y₊ = Φ(Y, ΔA)` that are `C¹` in `ΔA` to this form; a version with discrete
steps; the uniqueness of the solution of the method (`Y` is shown to be a solution); general
sizes and ranks; a bound in terms of the best-approximation error for a general `Π` (that link is
to leading order in `ε` and on paper only); and the upper bound for the projected equation in this
class. Literature: oblique (interpolatory) projectors as methods are published, with an upper
bound in the normal component of the field and constants `C_{m,r} C_{n,r}`
[CarrelEtAl2025, Thm. 10]; no published lower bound for a class of low-rank methods was found in
the sources read, and continuity is imposed as in width theory, where without it maps without
stability are allowed.

A state of rank `k ≥ r` whose result is truncated to rank `r` (buffer modes) has the error
`distLR r (A t)` plus twice the error of the state of rank `k`
(`RankInformationUpperBound.norm_sub_le_distLR_add_two_mul`). With the quasi-optimality bound of
section 3.7 for the rank `k`:

@stmt LeanDLRA/Research/RankStatePrice.lean norm_sub_le_distLR_add_two_mul_of_isDLRASolution RankStatePrice.norm_sub_le_distLR_add_two_mul_of_isDLRASolution

the singular value `ρ` and the distance of the curve `X` of rank `k` take the place of those of
the rank `r`. The device of keeping more modes than needed and truncating the output is that of
the frequent-directions sketch [GhashamiEtAl2015] (abstract: the bound
`‖A - π_{B_k}(A)‖² ≤ (1 + k/(ℓ - k)) ‖A - A_k‖²` for a sketch with `ℓ > k` rows).

**Tolerance truncation in time stepping: the rank freezes.** Let `Y_{k+1} = T_ϑ(Z_k)` be a step
followed by the truncated singular value decomposition at the tolerance rank `epsRank ϑ` (the
truncation of the rank-adaptive BUG integrator [CerutiKuschLubich2022]). In
@file(LeanDLRA/Research/DynamicRecompression.lean):

@stmt LeanDLRA/Research/DynamicRecompression.lean rank_truncation_epsRank_le_of_norm_sub_le DynamicRecompression.rank_truncation_epsRank_le_of_norm_sub_le

If the matrix that is truncated lies within `ϑ` of the previous iterate, the rank does not grow:
the iterate itself is a competitor within the tolerance. For a step-truncation method or an
augmented BUG step, `‖Z_k - Y_k‖` is at most the step size times a bound of the field. A tolerance
that does not decrease with the step size therefore freezes the rank, and the error stays above the
distance of every matrix, in particular of the exact solution, from the matrices of the initial
rank:

@stmt LeanDLRA/Research/DynamicRecompression.lean rank_le_rank_zero_of_forall_norm_sub_le DynamicRecompression.rank_le_rank_zero_of_forall_norm_sub_le

@stmt LeanDLRA/Research/DynamicRecompression.lean distLR_le_norm_sub_of_forall_norm_sub_le DynamicRecompression.distLR_le_norm_sub_of_forall_norm_sub_le

For step truncation of exact increments `A (k+1) - A k` the error is at most the start error plus
`k ϑ`, and this is attained:

@stmt LeanDLRA/Research/DynamicRecompression.lean norm_sub_le_add_mul_of_stepTruncation DynamicRecompression.norm_sub_le_add_mul_of_stepTruncation

@stmt LeanDLRA/Research/DynamicRecompression.lean exists_stepTruncation_norm_sub_eq_mul DynamicRecompression.exists_stepTruncation_norm_sub_eq_mul

The start is `diag(1, 0)`, the spectral gap at the cut is one, and `N ϑ ≤ 1`. The term `n ϑ` of
the error bound of [CerutiKuschLubich2022, Thm. 2] is therefore attained with the constant one for
a method that decides from the truncated iterate alone
(`DynamicRecompression.norm_sub_eq_mul_of_stepTruncation` is the version from the start zero). What
is not shown: the freeze is a statement for the truncation rule `T_ϑ` with a fixed `ϑ` and for
sequences with `‖Z_k - Y_k‖ ≤ ϑ`; it does not say how a rank-adaptive integrator with a tolerance
tied to the step size behaves.

**Recompression: the rank sandwich.** Let `V_{k+1} = V_k + h F_k(W_k)` be an explicit Euler
sequence whose field is evaluated at matrices `W_k` with `‖W_k - V_k‖ ≤ η_k` (in an application
`W_k` is the iterate `Y_k` plus a reconstruction of the remainder `V_k - Y_k` from a linear
sketch, and `V_k` is never formed), and let `Y_{k+1} = T_θ(W_k + h F_k(W_k))`. With `ζ_k = η_k +
E_{k+1}` for any solution `E` of `E_{k+1} ≥ (1 + h L) E_k + h L η_k + δ_k`:

@stmt LeanDLRA/Research/DynamicRecompression.lean norm_sub_le_and_epsRank_le_rank_and_rank_le_epsRank DynamicRecompression.norm_sub_le_and_epsRank_le_rank_and_rank_le_epsRank

The error is at most `θ + ζ_k`, and the rank of `Y_{k+1}` is between the `(θ + ζ_k)`-rank and the
`(θ - ζ_k)`-rank of the exact `A (k+1)`. The tolerance `θ` enters once and is not multiplied by the
number of steps; the reconstruction errors enter through the Lipschitz constant only. The
statement has the form of the recompression lemma of Bachmayr and Dahmen
[BachmayrDahmen2013, Lemma 2] for a stationary iteration (for matrices `epsRank_sandwich`).

**Ranks of truncated backward Euler runs through the Loewner order.** In
@file(LeanDLRA/Research/LoewnerRank.lean), for symmetric positive semidefinite matrices
`0 ⪯ Y ⪯ X` the `ε`-rank is monotone:

@stmt LeanDLRA/Research/LoewnerRank.lean epsRank_le_epsRank_of_posSemidef LoewnerRank.epsRank_le_epsRank_of_posSemidef

(`LoewnerRank.distLR_le_distLR_of_posSemidef` is the same for the distance). The proof needs no
eigenvalues: for a best approximation of `X` with row space spanned by `V`, a generalised Schur
complement `S` of `Y` satisfies `0 ⪯ S ⪯ Y`, `rank (Y - S) ≤ r` and `S V = 0`. The backward Euler
step of the differential Lyapunov equation `A' = -PA - AP + F` with `P ⪰ 0`,
`X₁ + h (P X₁ + X₁ P) = X₀ + h F`, is monotone in the Loewner order
(`LoewnerRank.posSemidef_of_add_smul_lyapunov`). A truncation `Y_{j+1}` of the step `Ŷ_{j+1}` from
`Y_j` that is below `Ŷ_{j+1}` in the Loewner order and has at most the `θ`-rank of `Ŷ_{j+1}` (the
truncated eigenvalue decomposition at the tolerance rank) stays below the untruncated run `X_j`
and has at most its `θ`-rank:

@stmt LeanDLRA/Research/LoewnerRank.lean rank_le_epsRank_of_truncated_lyapunov_run LoewnerRank.rank_le_epsRank_of_truncated_lyapunov_run

for every step size and every tolerance. In contrast to the recompression lemma above, the
tolerance need not exceed the accumulated error. The error obeys, with `P - c 1 ⪰ 0`:

@stmt LeanDLRA/Research/LoewnerRank.lean norm_sub_le_of_truncated_lyapunov_run LoewnerRank.norm_sub_le_of_truncated_lyapunov_run

The Sylvester problem `A' = -PA - AQ + G Hᵀ` is the off-diagonal block of the Lyapunov problem with
`diag(P, Q)` and the forcing `[G; H][G; H]ᵀ`. What is not shown: the truncation is assumed to
satisfy the two inequalities `0 ⪯ Y_{j+1} ⪯ Ŷ_{j+1}` and the rank bound; the files do not construct
it for a given implementation.

**A rectangular scheme with stacked-factor truncation.** The Sylvester problem
`A' = -PA - AQ + G Hᵀ` with `P ⪰ 0`, `Q ⪰ 0` is the off-diagonal block of the Lyapunov problem with
`diag(P, Q)` and the forcing `[G; H][G; H]ᵀ`. A low-rank scheme for the `m × n` unknown stores a
factor pair `(L, R)`, `Y = L Rᵀ`, and carries the positive semidefinite matrix `W Wᵀ` of the
stacked factor `W = [L; R]` along: its off-diagonal block is `Y`
(`StackedTruncation.toBlocks₁₂_mul_transpose`), a backward Euler step of the Lyapunov problem for
`W Wᵀ` is a backward Euler step of the Sylvester problem for `Y`
(`StackedTruncation.toBlocks₁₂_add_smul_lyapunov`), and the rank of the block is at most the rank of
the whole (`StackedTruncation.rank_toBlocks₁₂_le`). Stacked-factor truncation replaces the step
`Ŵ = [L̂; R̂]` by `W = Ŵ Z` with `Z Zᵀ ⪯ 1`, for instance the orthogonal projector onto leading
eigenvectors of the Gram matrix `ŴᵀŴ = L̂ᵀL̂ + R̂ᵀR̂`
(`StackedTruncation.posSemidef_one_sub_mul_transpose`). It only removes a positive semidefinite
part of `Ŵ Ŵᵀ` (`StackedTruncation.posSemidef_mul_transpose_sub_mul_transpose`); the truncated
singular value decomposition of `L̂ R̂ᵀ` is in general not of this form. In
@file(LeanDLRA/Research/StackedTruncation.lean) the computed iterates therefore stay below the
untruncated lifted run in the Loewner order, and the argument of the previous paragraph applies to
the lifted run:

@stmt LeanDLRA/Research/StackedTruncation.lean rank_le_epsRank_of_stacked_sylvester_run StackedTruncation.rank_le_epsRank_of_stacked_sylvester_run

The off-diagonal block of `X` is the backward Euler run of the Sylvester problem, and the computed
iterates have `rank (L_j R_jᵀ) ≤ rank_θ(X_j)` for every step size and every tolerance. If
`P ⪰ c`, `Q ⪰ c ≥ 0` and every truncation changes `Ŵ Ŵᵀ` by at most `θ`, the error is bounded
through the lifted run (the factor `√2` is the norm of the off-diagonal block of a symmetric
matrix, `StackedTruncation.two_mul_norm_toBlocks₁₂_sq_le`):

@stmt LeanDLRA/Research/StackedTruncation.lean norm_sub_le_of_stacked_sylvester_run StackedTruncation.norm_sub_le_of_stacked_sylvester_run

What is not shown: the truncation rule is a hypothesis (`hW`, `hZ`, `hZrank`, `hT`). That the
leading eigenvectors of `ŴᵀŴ` give a `Z` with `rank Z = rank_θ(Ŵ Ŵᵀ)` and tail at most `θ` is not
proved.

**Ranks that do not depend on the number of steps.** In
@file(LeanDLRA/Research/StationaryDomination.lean) let `P ⪰ 0` and let `S` satisfy the stationary
Lyapunov equation `P S + S P = F₀ + F` with `F₀ ⪰ 0`. A backward Euler run of the differential
Lyapunov equation `A' = -PA - AP + F` that starts below `S` stays below `S`:

@stmt LeanDLRA/Research/StationaryDomination.lean posSemidef_sub_of_lyapunov_run StationaryDomination.posSemidef_sub_of_lyapunov_run

No sign condition on `F` is needed: the difference `S - X_j` is a backward Euler run with the
forcing `F₀ ⪰ 0`, and the resolvent is positive
(`LoewnerRank.posSemidef_of_add_smul_lyapunov`). If `P ⪰ c > 0` and `F ⪰ 0`, the start condition
`X₀ ⪯ S` follows from `P X₀ + X₀ P ⪯ F₀` (`StationaryDomination.posSemidef_sub_of_lyapunov_le`),
because the inverse of `M ↦ P M + M P` is positive (`StationaryDomination.posSemidef_of_lyapunov`),
and the stationary equation has exactly one solution (`StationaryDomination.existsUnique_lyapunov`).
For a start `X₀ = W₀ W₀ᵀ` and `t > 0` the right-hand side `F₀ = t W₀ W₀ᵀ + t⁻¹ (P W₀)(P W₀)ᵀ` has
rank at most twice the number of columns of `W₀`, so a stationary majorant with a right-hand side
of low rank exists:

@stmt LeanDLRA/Research/StationaryDomination.lean exists_lyapunov_posSemidef_sub StationaryDomination.exists_lyapunov_posSemidef_sub

With the order argument for truncated runs of the previous paragraphs and the monotonicity of the
`ε`-rank in the Loewner order, the ranks of the truncated iterates are bounded by the `θ`-rank of
`S`:

@stmt LeanDLRA/Research/StationaryDomination.lean rank_le_epsRank_of_truncated_lyapunov_run_of_stationary StationaryDomination.rank_le_epsRank_of_truncated_lyapunov_run_of_stationary

for every step size and every tolerance. The matrix `S` depends on neither the step size nor the
number of steps. The truncated iterates `Y_{j+1}` are assumed positive semidefinite (`hYpos`), and
the start is excluded: for `θ ≥ ‖S‖` the bound is `0`, while `Y₀` need not vanish. The same holds
for the stacked-factor scheme with a stationary solution of the lifted problem
(`StationaryDomination.rank_le_epsRank_of_stacked_sylvester_run_of_stationary`).

For the Sylvester problem with `P ⪰ α`, `Q ⪰ β` and `a = α + β ≥ 0` (neither `P` nor `Q` needs to
be positive semidefinite), the shift `σ = (β - α)/2` gives the lifted operator
`diag(P + σ, Q - σ)` with both blocks `⪰ a/2`, and the shift does not change the off-diagonal block
(`StackedTruncation.shift_mul_add_mul_shift`). The end-to-end statement collects the run, the
rank bound and the error bound:

@stmt LeanDLRA/Research/StationaryDomination.lean rank_le_epsRank_and_norm_sub_le_of_shifted_lift StationaryDomination.rank_le_epsRank_and_norm_sub_le_of_shifted_lift

What is not shown: a bound for `rank_θ(S)` itself, through the approximation of `1 / x` by
exponential sums [DahmenDeVoreGrasedyckSuli2014, Lemma 5] (for the singular value decay of
Lyapunov solutions see also Stillfjord, arXiv 1804.02197, Thm. 3), is a citation and not in the
core: the files prove that `S` exists, is unique and dominates every run, and that its right-hand
side has rank at most `2 r₀ + r_f`. The truncation rule is a hypothesis, as above. Inexact solves
of the resolvent, time dependent forcing, semilinear terms and tensors are not treated, and the
examples of the file are runs with one step. Literature: the ingredients are classical, namely the
positivity of the inverse of the Lyapunov operator and of the backward Euler resolvent, the
comparison with a stationary supersolution, the embedding of a Sylvester equation as a block of a
Lyapunov equation, and the approximability of the inverse of the Lyapunov operator by exponential
sums for a right-hand side of low rank. The composition, a bound of the rank of the computed
iterates of a truncated backward Euler scheme by `rank_θ(S)` for every step size, tolerance and
number of steps, was not found in the sources read; the monotone-iteration literature for Lyapunov
and Riccati equations was not read. No claim of novelty is made.

**The plain truncation does not obey a fixed fraction of the tolerance.** Let `Ŷ_{j+1}` be the
backward Euler step of `A' = -(P A + A Q) + F` from `Y_j`, let `Y_{j+1} = T_θ(Ŷ_{j+1})` be the
truncated singular value decomposition at the Frobenius tolerance `θ` (rank `epsRank θ`), and let
`X_j` be the untruncated backward Euler run with `X₀ = Y₀`. The question is whether
`rank Y_j ≤ rank_δ(X_j)` for `δ` a fraction of `θ`, where `rank_δ` is `epsRank δ`. This is not the
scheme of the previous paragraphs: the truncated singular value decomposition of `L̂ R̂ᵀ` is in
general not a stacked-factor truncation. In @file(LeanDLRA/Research/StackedTruncation.lean), for
scalar problems (`1 × 1` matrices, `P = Q = 1/2`) with a sign change, no fixed fraction `c θ`
of the tolerance works:

@stmt LeanDLRA/Research/StackedTruncation.lean exists_plain_rank_gt_epsRank StackedTruncation.exists_plain_rank_gt_epsRank

Step one lands on `-θ` and is truncated to zero, so that the truncated run is ahead of the
untruncated one by `θ/(1 + h)` when both become positive. The step size of the instance is
`h = c/4`: the statement refutes a fixed fraction for every `c > 0`, and it says nothing about
fractions of the form `θ h a/(1 + h a)` that depend on the step size (`a = λ_min(P) + λ_min(Q)`).
For these, with `a = 1` in the following statements (`P = Q = 1/2`, `θ = 1`), the comparison is
refuted for `2 × 2` matrices at every step size, with a factor `κ` in front. In
@file(LeanDLRA/Research/PlainTruncationRank.lean):

@stmt LeanDLRA/Research/PlainTruncationRank.lean exists_plain_rank_gt_epsRank_mul_step_fraction PlainTruncationRank.exists_plain_rank_gt_epsRank_mul_step_fraction

For every `h > 0` there are diagonal `2 × 2` data and a factor `1/2 < κ < 1` such that `Y₃` has
rank one while `‖X₃‖ ≤ κ h/(1 + h)`. The lower bound `1/2 < κ` is what makes the `epsRank`
conjunct say this: for a negative tolerance `epsRank` is `0` for every matrix. The mechanism
involves two modes that are removed in different steps: one is removed with the whole
tolerance, the other shares the tolerance with the returning mode one, the accumulated error
exceeds `θ`, and both modes are released in the third step. This family lies on a tie
(`‖Ŷ₂‖ = θ`); `PlainTruncationRank.exists_plain_rank_gt_epsRank_of_params` has the parameters free,
and the `example` after it is an instance with `h = 1/4`, `κ = 99/100` and no ties. At a single
step size no fraction at all works:

@stmt LeanDLRA/Research/PlainTruncationRank.lean exists_plain_rank_gt_rank PlainTruncationRank.exists_plain_rank_gt_rank

With `h = 1/9` there are `2 × 2` data for which `Y₃` has rank two while `X₃` has rank at most one.
Hence `rank Y₃ > rank_δ(X₃)` for every `δ ≥ 0`: at this step size no positive fraction of the
tolerance repairs the comparison. Here `P` and `Q` are multiples of the identity, and what has no
common singular basis is the pair `(X₀, F)`; the singular vectors of truncated steps one and two
are rotated against each other, and the two removed parts add up to a matrix whose smallest singular
value exceeds the tolerance. The instance is one step size; nothing follows for other step sizes.
The statements show that the comparison with a fraction of the tolerance fails for the plain
scheme in the forms above, not that no rank bound holds for it.

The comparison does hold for decoupled modes with a sign condition. If `P`, `Q`, `F` and the
iterates are diagonal, the truncation removes diagonal entries, and every mode starts between zero
and the untruncated run on the side of its forcing (for instance `X₀ = Y₀ = 0`), then every entry
of `Ŷ_j` is dominated by the entry of `X_j`, all low-rank distances of `Ŷ_j` are at most those of
`X_j`, and the rank is bounded with the full tolerance:

@stmt LeanDLRA/Research/PlainTruncationRank.lean abs_le_abs_of_decoupled_run PlainTruncationRank.abs_le_abs_of_decoupled_run

@stmt LeanDLRA/Research/PlainTruncationRank.lean rank_le_epsRank_of_decoupled_run PlainTruncationRank.rank_le_epsRank_of_decoupled_run

The distances are compared in `distLR_diagonal_le_of_abs_le`. That the
truncation removes diagonal entries is assumed (`hy`, `hrank`): on ties the truncated singular
value decomposition of a diagonal matrix need not be diagonal, and the family for every `h` above
starts on the other side of zero.

What is not shown: the comparison for non-commuting data with `X₀ = Y₀ = 0` is open (no violation
was found in numerical chains, and the domination of the tails was found numerically to fail for
such data, so the proof above does not extend); for decoupled modes without the sign condition,
cascades with more modes refute smaller fractions than the family above (numerics and one exact
instance, not in the core), and whether the comparison holds there with some constant `c ≤ 1/√2`
times `θ h a/(1 + h a)` is open; the comparison for vectors (one of the two dimensions equal to
one) and at steps one and two of every problem, which rests on the Lipschitz argument for the
tails (`epsRank_le_sub`), is not a run statement in the core; and for `h a > 1` the Lipschitz
argument gives a positive fraction of the tolerance for every problem, which is not stated in the
core either. The stacked-factor rule above is the variant of the scheme for which a rank bound is
in the core.

**Energy of a run of the implicit BUG integrator.** For `F(Z) = -BᵀB Z - Z CᵀC` the S-step of the
BUG integrator with backward Euler substeps satisfies an energy identity
(`IsMatrixImplicitBUGStep.energy_eq_inner_of_sylvester`, section 7.7). A truncation by the
singular value decomposition is a multiplication by an orthogonal projector from the left and one
from the right, and increases neither the norm nor the stiff energy
`h (‖B Y‖² + ‖Y Cᵀ‖²)`. In @file(LeanDLRA/Research/ImplicitBUGRunEnergy.lean):

@stmt LeanDLRA/Research/ImplicitBUGRunEnergy.lean half_sq_norm_add_sum_energy_implicitBUG_run_le_of_sylvester half_sq_norm_add_sum_energy_implicitBUG_run_le_of_sylvester

whatever the bases are and however large `B` and `C` are. If the residual bound of the run theorem
`norm_implicitBUG_run_sub_le_of_sylvester_residual` has the form `a ‖Yⱼ‖ + b (energy of Yⱼ)^{1/2}`
(for bases that contain the factors of `k` ADI steps with shifts of an interval, a spectral
splitting of the ADI residual gives `a` as a Zolotarev number of the interval; arXiv 1609.09494,
Corollary 3.2, is cited in the docstring for it), the distance to the backward Euler run on the full
matrix is bounded without any bound of `B` or `C`:

@stmt LeanDLRA/Research/ImplicitBUGRunEnergy.lean norm_implicitBUG_run_sub_le_of_sylvester_energy_residual norm_implicitBUG_run_sub_le_of_sylvester_energy_residual

The hypothesis `hres` is on the residual of the bases and is not derived here. The run theorem
is the one of section 7.7.

**Literature.** The two-problem argument of information-based complexity for initial value
problems with inexact information gives a lower bound of the form of `half_norm_sub_le_max_error`:
for two data whose noisy-information sets intersect the error is at least half the distance of
the solutions ([BochacikEtAl2020], proof of Lemma 2; the same bound for deterministic algorithms in
[CzyzewskaEtAl2022], Theorem 5.3). There every evaluation of the field carries noise of size at
most `δ`; here the field is exact but known only on the matrices of rank at most `k`, so that at a
state `Z` it is known up to `L distLR k Z`, and the pair must consist of `L`-Lipschitz fields
that agree there. The classes in which the bound does not apply (linear fields) have no
counterpart in those papers. In these terms, values of the field on matrices of rank at most `k`
are inexact information about the field at the state, of accuracy `L distLR k`, and the lower
bound `L ∫ distLR k` has the constant one, which is attained. For the full state, as for initial
value problems with inexact information [CzyzewskaEtAl2022, Theorem 5.3], an Euler method that
evaluates the field at a best approximation of rank at most `k` of a full state is worst-case
optimal, here up to the factor `e^{2LT}`; there the constant is unspecified and the noise level
constant, and the file has the
level `L distLR k(A(s))` along the solution, the factor `e^{2L(T - s)}` and the lower constant
one. For the rank freeze: that truncation tolerances must tighten with the step is known
([BachmayrDolbeaultSachsenmaier2025], §1; [RodgersDektorVenturi2022], Corollary 1); the files show
that for a fixed tolerance the rank cannot increase once the step moves the iterate by less than
the tolerance, and that the term `n ϑ` of [CerutiKuschLubich2022] is attained with the constant
one. The recompression sandwich has the form of [BachmayrDahmen2013, Lemma 2].

The pair for all sizes is the embedding of the `2 × 2` pair, not another device. The dissipative
pair and its weighted identity were not compared with any source beyond these papers; sources on
information-based complexity that were not read (Traub, Wasilkowski and Woźniakowski; Kacewicz;
Plaskota) may contain the device for classes of one-sided Lipschitz fields.

## 4. Steps, runs and the global error

This section is independent of low rank. It contains the argument that turns a bound for the
local error of a method into a bound for the global error, and its last entry is the theorem of
which the integrators of sections 5 and 6 are instances.

### 4.1 Definitions

@stmt LeanDLRA/Integrators/Defs.lean StepRel StepRel

@stmt LeanDLRA/Integrators/Defs.lean IsGrid IsGrid

@stmt LeanDLRA/Integrators/Defs.lean uniformGrid uniformGrid

@stmt LeanDLRA/Integrators/Defs.lean IsRun IsRun

@stmt LeanDLRA/Integrators/Defs.lean HasLocalError HasLocalError

@stmt LeanDLRA/Integrators/Defs.lean StepRel.HasLocalErrorOn StepRel.HasLocalErrorOn

A step relation `M : StepRel E` is a relation `M t₀ t₁ Y₀ Y₁` that reads "`Y₁` is a result of
one step from `Y₀` at time `t₀` to time `t₁`". It is a relation and not a function because a
step of a low-rank integrator involves choices (of bases) and because a step need not exist.
`IsRun M τ N Y` says that `τ` is a grid with `N` intervals and that `Y (n + 1)` is a result of a
step from `Y n` for every `n < N`. `HasLocalError F t₀ t₁ Y₀ Y₁ δ` says that `Y₁` is within `δ`
of the value at `t₁` of every solution of the full equation that starts at `Y₀` at time `t₀`.
The statement quantifies over these solutions and does not assert that one exists.
`M.HasLocalErrorOn F D δ` says that every step of `M` that starts in the set `D` has local
error `δ t₀ t₁`.

### 4.2 From local errors to the global error

@stmt LeanDLRA/Integrators/GlobalError.lean IsLipschitzField.norm_sub_le_of_hasLocalError IsLipschitzField.norm_sub_le_of_hasLocalError

Global assumptions. Let `F` be globally `L`-Lipschitz with `0 ≤ L` and continuous in time
(`hc`), `τ` a grid, `A` a solution on `[τ 0, τ N]`, and `Y` any sequence whose `k`-th step has
local error `δ k` (`hloc`). Then for all `n ≤ N`

`‖Y n - A (τ n)‖ ≤ e^{L (τ n - τ 0)} ‖Y 0 - A (τ 0)‖ + ∑_{k<n} e^{L (τ n - τ (k+1))} δ k`.

The space `E` has to be complete. The constants are the Lipschitz constant and the grid only.
This is the classical argument known as Lady Windermere's fan; no paper is cited.

@stmt LeanDLRA/Integrators/Tube.lean IsRun.norm_sub_le_of_tube IsRun.norm_sub_le_of_tube

Assumptions on a tube. Let `Y` be a run of a step relation `M`, and let the assumptions on the
field hold only on the tube of radius `ρ` around `A` (`hP`, with joint continuity `hc` there).
The local error is assumed for the method near `A` and not for the run: `hM` says that every
step of `M` from time `τ n` that starts within `R n` of `A (τ n)` has local error `δ n`. If the
error bound of the previous entry is at most `R n` for every `n` (`hR`) and
`R n + 2 * B * (τ (n + 1) - τ n) < ρ` (`hsmall`), the same error bound holds. The theorem shows
in particular that the run stays in the tube; this is not assumed. The constants are `L`, the
grid and the local errors; the bound `B` and the radius `ρ` enter only the smallness condition.

### 4.3 One run theorem, many methods

The file [`LeanDLRA/Integrators/Method.lean`](../LeanDLRA/Integrators/Method.lean) is the entry
point of the theory of integrators. It names the three properties of a method that the
construction of a run needs, and proves existence of a run together with its error bound once
for all methods that have them.

@stmt LeanDLRA/Integrators/Method.lean StepMethod StepMethod

@stmt LeanDLRA/Integrators/Method.lean StepMethod.IsTubeLocal StepMethod.IsTubeLocal

A one-step method `M : StepMethod E` assigns a step relation to every field. `Adm` is the set of
admissible values of the method (for the integrators of this library: the matrices of rank at
most `r`). `M.IsTubeLocal Adm κ` consists of three properties:

* existence (`exists_step`): for a globally Lipschitz field that is continuous in time on the
  step interval, a step exists from every admissible value;
* invariance (`adm_of_step`): the result of a step from an admissible value is admissible;
* locality (`step_of_tubeExt`): a step for the extended field `tubeExt F A a b ρ` that starts at
  an admissible value `Y₀` with `‖Y₀ - A t₀‖ + κ * B * (t₁ - t₀) < ρ` is a step for `F` itself.

The number `κ` is the margin constant: it says how many step lengths, at the speed bound `B`,
the method needs between the start value and the boundary of the tube. Locality is what a
method has if all its substeps move with speed at most `B`.

@stmt LeanDLRA/Integrators/Method.lean StepMethod.IsTubeLocal.exists_run_norm_sub_le StepMethod.IsTubeLocal.exists_run_norm_sub_le

The run theorem. Let `M` be tube-local with admissible values `Adm` and margin constant
`κ ≥ 2`. Let `F`, `A` satisfy a `DLRAProblem` on the tube of radius `ρ` over
`[t₀, t₀ + N * h]`, with `F` jointly continuous on the tube (`hc`). Let every step of `M F` of
size `h` from an admissible value in the tube have local error at most `h * c` (`hloc`; the
hypothesis is needed only for start values within the error bound of `A`). Then for every
admissible start value `Y₀` with `‖Y₀ - A t₀‖ ≤ δ` there is a run of `N` steps of size `h` from
`Y₀`, all its values are admissible, and

`‖Y n - A (t₀ + n * h)‖ ≤ e^{L T} δ + T e^{L T} c` for all `n ≤ N`,

where `T` is any number with `N * h ≤ T`. The only further hypothesis is the smallness condition
`e^{L T} δ + T e^{L T} c + κ * B * h < ρ` (`hsmall`): the error bound plus the margin must fit
into the tube. The constants are `L`, `T` and the local error constant `c`; the bound `B`, the
radius `ρ` and `κ` enter only the smallness condition. The theorem asserts existence of the run:
it is not assumed that the method can be carried out. No paper is cited; the theorem is the
common part of the proofs of sections 5.2, 6.1, 6.2, 6.3 and 6.4. Forms for arbitrary grids and for
admissible sets that change from step to step are `exists_isRun_norm_sub_le_of_tube` and
`IsRun.adm_and_norm_sub_le_of_tube` in the same file.

Instances in the core at the time of writing:

| Integrator | Tube-local method | Margin constant `κ` | Run theorem | Section |
|---|---|---|---|---|
| BUG | `MatrixBUG.isTubeLocal_stepRel` | 4 | `MatrixBUG.exists_run_norm_sub_le` | 5.2 |
| projector splitting | `MatrixKSL.isTubeLocal_stepRel` | 4 | `MatrixKSL.exists_run_norm_sub_le` | 6.1 |
| parallel BUG with fixed rank | `MatrixParallelBUG.isTubeLocal_stepRel` | 2 | `MatrixParallelBUG.exists_run_norm_sub_le` | 6.2 |
| BUG with augmented bases and truncation to a fixed rank | `MatrixBUG.isTubeLocal_truncStepRel` | 4 | `MatrixBUG.trunc_exists_run_norm_sub_le` | 6.3 |
| BUG with explicit Euler substeps and fixed rank | `MatrixEulerBUG.isTubeLocal_stepRel` | 0 | `MatrixEulerBUG.exists_run_norm_sub_le` | 6.4 |
| rank-adaptive BUG, truncation by a tolerance `ϑ` | `MatrixBUG.isTubeLocal_adaptiveStepRel_Ici` | 4 | `MatrixBUG.adaptive_exists_run_norm_sub_le` | 6.3 |
| parallel BUG, truncation by a tolerance `ϑ` | `MatrixParallelBUG.isTubeLocal_adaptiveStepRel_Ici` | 2 | `MatrixParallelBUG.adaptive_exists_run_norm_sub_le` | 6.2 |
| dynamical randomized SVD | `MatrixDRSVD.isTubeLocal_stepRel` | 3 | `MatrixDRSVD.exists_run_norm_sub_le` | 6.7 |
| projected Euler method | `MatrixProjEuler.isTubeLocal_stepRel` | 0 | `MatrixProjEuler.exists_run_norm_sub_le` | 6.8 |
| projected Runge–Kutta methods | `MatrixPRK.isTubeLocal_stepRel` | `(1 + κ) α + 1` | `MatrixPRK.exists_run_norm_sub_le` | 6.8 |
| midpoint BUG with fixed rank (the 4r variant) | `MatrixMidpointBUG.isTubeLocal_stepRel` | 2 | `MatrixMidpointBUG.exists_run_norm_sub_le` | 6.5 |
| explicit midpoint method in bases with `2 r` columns, truncation to rank `r` | `ExplicitMidpoint.isTubeLocal_stepRel` | 2 | `ExplicitMidpoint.exists_run_norm_sub_le` | 6.6 |
| BUG for Tucker tensors, fixed multilinear rank | `TuckerBUG.isTubeLocal_stepRel` | `d + 2` | `TuckerBUG.exists_run_norm_sub_le` | 8.2 |

In the first five rows and in the rows for the two midpoint methods, the dynamical randomized
SVD and the projected methods the admissible values are the matrices of rank at most `r`; for the
integrators with a truncation tolerance every matrix is admissible (the set of the numbers of
columns of a start factorization is `Set.Ici r₀`); for the Tucker integrator they are the tensors
of multilinear rank at most `r`. The hypotheses on `F` and `A` are the same in all rows, in the
same order: a `DLRAProblem` on the tube, joint continuity of `F` there, and a bound `ε` on the
normal part of `F` at the factored points of the tube. The theorems of sections 6.4 and 6.8 have
more, on the dependence of the field on time; the theorems for the two midpoint methods take a
field of class `C²` with bounds on its derivatives (sections 6.5 and 6.6); the theorem for the
projected
Runge–Kutta methods has hypotheses on the order of the classical scheme (section 6.8). The run
theorem asks for a margin constant of at least 2 (`hκ`). For the integrators whose constant is
smaller (sections 6.4, 6.5, 6.6 and 6.8, constant 0, 2 or `(1 + κ) α + 1`), it is used with a larger
constant (`StepMethod.IsTubeLocal.mono`; the midpoint BUG integrator with 3). The integrators with
a truncation tolerance are instances of the form of the theorem with a tolerance for every step,
the second theorem below (`StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_tol`), because the
local error of a step is `h c + ϑ`.

The integrators of sections 6 to 8 that are not rows of the table (the implicit BUG integrator
in projector form, the integrators for tree tensor networks, the midpoint BUG integrator in
projector form) and the
tensor theorems `tucker_global_error_le`, `tucker_global_error_le_of_tube` have error theorems of
an older form, in which the field satisfies global assumptions or the steps and the exact
solutions through the numerical values are hypotheses.

The implicit BUG integrator on matrices (section 7.1) is not a row either, for a different
reason: property (E) asks for a step of every globally Lipschitz field and every step size, and
a backward Euler stage need not exist for `h L ≥ 1`. Its run theorem is proved directly from the
form for the uniform grid (`exists_isRun_norm_sub_le_of_tube_uniformGrid`).

**To get an error bound for a method** that is a row of the table, apply its run theorem; the
guide ([GUIDE.md](GUIDE.md), sections 1 and 2) lists the steps. A method that is not a row has to
be shown to be tube-local first: existence of a step from every admissible value, invariance of
the admissible set, and locality (the three fields of `StepMethod.IsTubeLocal`).

Three more forms of the run theorem are in files of their own.

@stmt LeanDLRA/Integrators/MethodGrid.lean StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_isGrid StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_isGrid

@stmt LeanDLRA/Integrators/MethodTolerance.lean StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_tol StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_tol

@stmt LeanDLRA/Integrators/MethodOneSided.lean StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_oneSided StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_oneSided

@stmt LeanDLRA/Integrators/MethodOneSided.lean StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_oneSided_neg StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_oneSided_neg

The first is the run theorem for a grid `τ 0 ≤ τ 1 ≤ ⋯ ≤ τ N` with variable step sizes
(`IsGrid τ N`) and a local error bound `δ n` that may depend on the step. The numbers `R n` are
upper bounds of the error bound at step `n` (`hR`). The local error has to be shown only for
steps that start within `R n` of the solution (`hloc`), and `R n` plus the margin
`κ * B * (τ (n + 1) - τ n)` of step `n` must be smaller than `ρ` (`hsmall`). The run satisfies

`‖Y n - A (τ n)‖ ≤ e^{L (τ n - τ 0)} ‖Y₀ - A (τ 0)‖ + ∑_{k<n} e^{L (τ n - τ (k + 1))} δ k`.

The second is the case of the uniform grid and of steps with local error `h * c + ϑ`: a step
with local error `h * c` whose result is then changed by at most `ϑ`, for example by a
truncation to a tolerance (`HasLocalError.add_of_norm_sub_le` in the same file). The run
satisfies `‖Y n - A (t₀ + n * h)‖ ≤ e^{L T} (δ + n ϑ) + T e^{L T} c`; the tolerance enters once
for every step taken. Both theorems cite no paper. The last `example` of
[`LeanDLRA/Integrators/Matrix/TruncBUGRun.lean`](../LeanDLRA/Integrators/Matrix/TruncBUGRun.lean)
applies the second to a truncation that is computed only up to an error `ϑ`; the core has no
other use of the two theorems at the time of writing.

The third form is in
[`LeanDLRA/Integrators/MethodOneSided.lean`](../LeanDLRA/Integrators/MethodOneSided.lean) (the
last two statements above). In the proof of the run theorem the Lipschitz constant `L` of the
field on the tube has two parts: it gives the exact solutions started at the numerical values
and the steps of the globally Lipschitz extension, and it bounds the distance of two exact
solutions in the tube. For the second part a one-sided Lipschitz constant `ℓ` of `F` on the tube
(`IsOneSidedLipschitzFieldOn`, with `ℓ ≤ L`) is enough. For `0 ≤ ℓ` the run satisfies

`‖Y n - A (t₀ + n h)‖ ≤ e^{ℓ T} δ + T e^{ℓ T} c`,

with `ℓ` in place of `L` in the exponent and in the smallness condition. For `ℓ < 0` the first
theorem is replaced by the second: runs of every length `N` exist, with
`‖Y n - A (t₀ + n h)‖ ≤ e^{ℓ n h} δ + (h - ℓ⁻¹) c`, and the smallness condition
`δ + (h - ℓ⁻¹) c + κ B h < ρ` does not contain the final time. What is not shown: `L` stays in the
hypotheses (`DLRAProblem`) and in the local error constant `c` of the method; it gives existence
and does not enter the propagation of errors. The theorems do not make an integrator uniform in
the stiffness (section 7). The `example`s at the end of the file derive
`StepMethod.IsTubeLocal.exists_run_norm_sub_le` from the first theorem with `ℓ = L` and show that
the hypotheses can hold with `ℓ < L`. The file cites no paper. Section 5.3 applies the two
theorems to the BUG integrator.

## 5. The BUG integrator

The BUG integrator ("basis update and Galerkin") of [CerutiLubich2022] advances a matrix
`Y₀ = U₀ S₀ V₀ᵀ` of rank `r` in three substeps: a differential equation for `K = U S` with the
old `V₀` (K-step), one for `L = V Sᵀ` with the old `U₀` (L-step), both started at `Y₀`, which
give new bases `U₁` and `V₁`; then a Galerkin differential equation for `S` in the new bases
(S-step), started at the projection of `Y₀`.

### 5.1 The step

@stmt LeanDLRA/Integrators/Matrix/BUG.lean IsStep MatrixBUG.IsStep

@stmt LeanDLRA/Integrators/Matrix/BUGStep.lean stepRel MatrixBUG.stepRel

`MatrixBUG.IsStep` is one step in terms of the factors. The fields `kSol`, `lSol`, `sSol` are
the three differential equations (their fields are `MatrixBUG.kField`, `MatrixBUG.lField`,
`MatrixBUG.sField`). The new bases are not required to come from a particular QR factorization:
the fields `kCap` and `lCap` only require that `U₁` and `V₁` have orthonormal columns and that
their ranges contain the results of the K-step and the L-step. `MatrixBUG.stepRel F r` is the
step relation on matrices: `Y₁` is a result of a step from `Y₀` if there are factors of `Y₀` with
`r` columns and a factor step that ends in `Y₁`. It contains no constant of the error analysis.
The same step in projector form on a general state space is `IsBUGStepCore`, built on
`BasisUpdate`, which holds the K-step and L-step data shared with other integrators.

Source: [CerutiLubich2022, §3.1].

### 5.2 Existence of a run and the robust error bound

@stmt LeanDLRA/Integrators/Matrix/BUGRun.lean exists_run_norm_sub_le MatrixBUG.exists_run_norm_sub_le

@stmt LeanDLRA/Foundations/Localization.lean bugGlobalBound bugGlobalBound

@stmt LeanDLRA/Integrators/Defs.lean bugC₁ bugC₁

@stmt LeanDLRA/Integrators/Defs.lean bugC₂ bugC₂

This is the main theorem of the library on the BUG integrator. Hypotheses: `hP`, the field is
`L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around the exact solution `A` over
`[t₀, t₀ + N * h]`; `hc`, it is jointly continuous on the tube; `hε`, its normal component at
the matrices of rank `r` in the tube is at most `ε`; `hh`, `hhH`, `hNT`, the step size satisfies
`0 ≤ h ≤ H` and `N * h ≤ T`; `hrm`, `hrn`, the rank `r` is at most the number of rows and of
columns; `hY₀`, `hδ`, the start value has rank at most `r` and is within `δ` of `A t₀`;
`hsmall`, the error bound plus `4 * B * h` is smaller than `ρ`. Conclusion: there is a run of
`N` BUG steps of size `h` from `Y₀`; every value has rank at most `r`; and for all `n ≤ N`

`‖Y n - A (t₀ + n * h)‖ ≤ e^{L T} δ + T e^{L T} (c₁ ε + c₂ h)`

with `c₁ = bugC₁ L H` and `c₂ = bugC₂ L B H`. The constants depend on `L`, `B`, `H` and `T`
only. They do not depend on the singular values of the values `Y n` or of `A`, on the rank `r`,
or on the size of the matrices: the bound is robust. The error is of first order in `h`, plus a
multiple of `ε` that does not go to zero with `h`. The existence of the run is part of the
conclusion; nothing is assumed about the field outside the tube.

The theorem is the instance of the run theorem of section 4.3 for the BUG integrator:

@stmt LeanDLRA/Integrators/Matrix/BUGRun.lean isTubeLocal_stepRel MatrixBUG.isTubeLocal_stepRel

The admissible values are the matrices of rank at most `r` and the margin constant is 4.

@stmt LeanDLRA/Integrators/Matrix/BUGRun.lean IsRun.norm_sub_le MatrixBUG.IsRun.norm_sub_le

The same bound for every run, not only for the one constructed: under the same hypotheses on the
field, every run `Y` of the BUG integrator with `‖Y 0 - A t₀‖ ≤ δ` satisfies the error bound.
Here no rank condition on the start value is needed, because a step from `Y 0` exists only if
`Y 0` has rank at most `r` (`MatrixBUG.exists_stepRel_iff`).

@stmt LeanDLRA/Integrators/Matrix/BUGRun.lean exists_bugGlobalBound_lt exists_bugGlobalBound_lt

The smallness condition can be met: if the part of the bound that comes from the normal
component is smaller than the tube radius, `T e^{L T} c₁ ε < ρ`, and `0 < H`, then there are a
positive `δ` and a positive `h ≤ H` for which `hsmall` holds.

The `example`s of the matrix integrators use one linear test field, fixed in
@file(LeanDLRA/Integrators/Matrix/LinearFieldExample.lean): `F(t, Y) = M Y + Y Nᵀ + G` on `2 × 2`
matrices with `M = -E`, `N = 0`, `G = E = e₁ e₁ᵀ`, so that `E` is a stationary point, the start
value `(5/4) E` of rank one, `K = 10` steps of size `h = 1/100` and the tube radius `4`. The file
has the hypotheses of the error theorems for it (`L = 1`, `B = 4`, `ε = 1`) and bounds of the
constants of the bound.

Source: [CerutiLubich2022, Thm. 4]. The paper states the bound for a field that is Lipschitz
and bounded everywhere and for a given sequence of steps; the form quoted here assumes these
properties on a tube only and also proves that the steps exist. The form with global
assumptions is `MatrixBUG.global_error_le` in
[`LeanDLRA/Integrators/Matrix/BUG.lean`](../LeanDLRA/Integrators/Matrix/BUG.lean).

### 5.3 The BUG integrator with smaller local constants and a one-sided Lipschitz constant

Two files improve the bound of section 5.2 in two independent ways. The statements are about the
same step and the same hypotheses on `F` and `A`; the older theorems stay as they are.

@stmt LeanDLRA/Integrators/BUGCapture.lean kstep_capture_two_mul kstep_capture_two_mul

@stmt LeanDLRA/Integrators/BUGCapture.lean bug_capture_two_mul bug_capture_two_mul

@stmt LeanDLRA/Integrators/BUGCapture.lean local_error_two_mul#1 IsBUGStep.local_error_two_mul

*Smaller constants*
([`LeanDLRA/Integrators/BUGCapture.lean`](../LeanDLRA/Integrators/BUGCapture.lean)).
The K-step capture estimate behind the robust local error, `‖(1 - P₁) A(t₁)‖ ≤ h (4 L B h + ε)`
(`kstep_capture`), holds with `2 L B h` in place of `4 L B h` (first theorem). The two capture
errors, left and right, are combined orthogonally (`IsOrthProj.norm_sub_apply_sq`) and give the
factor `√2` in place of `2` (second theorem). With `ϑ = h (2 L B h + ε)` the local error of one
step is then (third theorem)

`‖Y₁ - A(t₁)‖ ≤ (e^{L h} - 1) (B h + √2 ϑ) + √2 ϑ`.

In the `O`-form `h (c₁ ε + c₂ h)` the constants are `c₁ = √2 (1 + L H e^{L H})` and
`c₂ = L B (e^{L H} + 2 √2 (1 + L H e^{L H}))`, at most `bugC₁ L H` and `bugC₂ L B H`. The file
has the same for the Tucker integrator with `d` modes
(`IsTuckerBUGStep.local_error_two_mul`: `√d` in place of `√2`) and the local error of a step
near a reference solution for a field that is Lipschitz and bounded only on a tube
(`IsBUGStepCore.hasLocalError_of_tube_two_mul`).

@stmt LeanDLRA/Integrators/Matrix/BUGRunOneSided.lean exists_run_norm_sub_le_of_oneSided MatrixBUG.exists_run_norm_sub_le_of_oneSided

@stmt LeanDLRA/Integrators/Matrix/BUGRunOneSided.lean exists_run_norm_sub_le_of_oneSided_neg MatrixBUG.exists_run_norm_sub_le_of_oneSided_neg

*Runs*
([`LeanDLRA/Integrators/Matrix/BUGRunOneSided.lean`](../LeanDLRA/Integrators/Matrix/BUGRunOneSided.lean)).
The hypotheses are those of `MatrixBUG.exists_run_norm_sub_le` (section 5.2) and a one-sided
Lipschitz constant `ℓ` of `F` on the tube (`hℓ`). For `0 ≤ ℓ` the first theorem gives a run with

`‖Y n - A (t₀ + n h)‖ ≤ e^{ℓ T} δ + T e^{ℓ T} (c₁ ε + c₂ h)`,

with the constants `c₁`, `c₂` above; with `ℓ = L` the bound is at most `bugGlobalBound`. For
`ℓ < 0` the second theorem gives runs of every length with
`‖Y n - A (t₀ + n h)‖ ≤ e^{ℓ n h} δ + (h - ℓ⁻¹) (c₁ ε + c₂ h)`, and neither the bound nor the
smallness condition contains `N`. Both are instances of the theorems of section 4.3 with the BUG
integrator as the tube-local method. What is not shown: `L` remains in the constants `c₁`, `c₂`
and in the existence of the steps, and only the propagation from step to step uses `ℓ`; the
bound is therefore not uniform in the stiffness. The `example`s prove
`MatrixBUG.exists_run_norm_sub_le` from the first theorem, and satisfy the hypotheses of the
second for the dissipative field `F(t, Y) = -Y`. The module docstring cites
[CerutiLubich2022, Thm. 4] for the bound of section 5.2.

### 5.4 Quasi-optimality of the BUG integrator for given data

The robust bounds of sections 5.2 and 5.3 compare the iterate with the exact solution and hold
without a condition on singular values. The files of this section compare the BUG iterate with a
reference of rank `r`, the truncated singular value decomposition `T_r(A(t_n))`, for the matrix
approximation problem: given data `A(t)`, field `F(t, Y) = Ȧ(t)`. This is the discrete counterpart
of section 3.7 and 3.8. One step of the integrator of [CerutiLubich2022] from `Y₀` with the
orthogonal projectors `P₀`, `Q₀` onto its column and row space is `Y₁ = P₁ (Y₀ + (A₁ - A₀)) Q₁`,
where the range of `P₁` contains the range of `(Y₀ + (A₁ - A₀)) Q₀` (K-step) and the range of `Q₁`
contains the row space of `P₀ (Y₀ + (A₁ - A₀))` (L-step). All norms are Frobenius norms and `‖·‖₂`
is the spectral norm.

**The identity of the step.** With `D = A₁ - A₀`, the file
@file(LeanDLRA/Integrators/Matrix/BUGQuasiOptimality.lean) writes the step as

@stmt LeanDLRA/Integrators/Matrix/BUGQuasiOptimality.lean projStep_eq_add_sub MatrixBUG.projStep_eq_add_sub

and bounds the error against a reference `X₁` of rank `r`. The references are described by
generalized inverses (`X G X = X`, `X G` and `G X` symmetric, `‖G‖₂ ≤ g`, so that `g⁻¹` is a
lower bound of the smallest nonzero singular value), and the tail `A - X` is orthogonal to the
column and the row space of `X`, as it is for the truncated singular value decomposition. The
one-step bound has the tail times the path length of the reference in one step as source:


@stmt LeanDLRA/Integrators/Matrix/BUGQuasiOptimality.lean norm_projStep_sub_le_tail MatrixBUG.norm_projStep_sub_le_tail

@stmt LeanDLRA/Integrators/Matrix/BUGQuasiOptimality.lean norm_projRun_sub_le MatrixBUG.norm_projRun_sub_le

Here `τ ≥ ‖A₁ - X₁‖₂`, `ξ ≥ ‖X₁ - X₀‖₂`, `d_K ≥ ‖P₁ (1 - P₀)‖₂`, `d_L ≥ ‖(1 - Q₀) Q₁‖₂` are the
sines of the angles between the old bases and the bases after the step, `c` bounds the inverses of
the overlaps of the old bases with the reference, and `ΔR = (A₁ - X₁) - (A₀ - X₀)`. The sum over
the steps is a Riemann sum of `∫ σ_{r+1}(A) ‖Ẋ‖ dt`; all terms vanish with the tail, which is the
exactness property of [CerutiLubich2022, Theorem 3] and [LubichOseledets2014, Theorem 4.1]. The
robust bound [CerutiLubich2022, Theorem 4] has the normal component of the field in place of the
tail; for given data this is the size of the derivative of the tail.

**Constants from the distances.** In @file(LeanDLRA/Integrators/Matrix/BUGQuasiOptimalityStep.lean)
the constants for the overlaps and the sines are derived from `‖Y₀ - X₀‖` and the increments, for
projectors of equal trace. With `g ‖X₁ - X₀‖₂ ≤ η_X`, `g ‖ΔR‖₂ ≤ η_R`, `g ‖X₁ - X₀‖ ≤ η_F`,
`g ‖A₁ - A₀‖ ≤ η_F`, `η_X ≤ η_F ≤ 1/16` and `g ‖Y₀ - X₀‖ ≤ 1/16`:

@stmt LeanDLRA/Integrators/Matrix/BUGQuasiOptimalityStep.lean norm_projStep_sub_le_of_trace MatrixBUG.norm_projStep_sub_le_of_trace

The factors `23 / 10`, `43 / 20`, `11 / 5` are `2` in the limit of small step numbers and
`g ‖Y₀ - X₀‖`; those of `MatrixBUG.norm_projStep_sub_le_tail` are `4`. No generalized inverse of
`Y₀` is used.

**Against the truncated singular value decomposition.** With `‖Ȧ‖ ≤ μ`,
`σ_r(A) ≤ τ < ρ ≤ σ_{r-1}(A)` (indices start at zero), `lam = μ / (ρ - τ)` and `h lam ≤ 1/16`,
the file @file(LeanDLRA/Integrators/Matrix/BUGQuasiOptimalityTruncation.lean) has one step and a
run in the quantities of
`IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_singularValues_lt` (section 3.8):

@stmt LeanDLRA/Integrators/Matrix/BUGQuasiOptimalityTruncation.lean Exactness.IsBUGIncrementStep.norm_sub_truncation_le Exactness.IsBUGIncrementStep.norm_sub_truncation_le

@stmt LeanDLRA/Integrators/Matrix/BUGQuasiOptimalityTruncation.lean norm_bugRun_sub_truncation_le_mul_of_forall_le norm_bugRun_sub_truncation_le_mul_of_forall_le

The bound has the values `σ_r(A(t_k))` on the grid and not the integral of `σ_r(A)`, since the
integrator sees the data on the grid only. The smallness condition `htube` is needed for the
overlap of the bases of the iterate with those of the reference. The exponent `9/2 lam` is not
sharp: the continuous bound has `μ / ρ`.

**The normal velocity as growth rate.** The growth factor of the bound above contains the whole
velocity `μ`. The file @file(LeanDLRA/Integrators/Matrix/BUGQuasiOptimalityNormalStep.lean) has
a step in which the increment of the reference enters the factor of the old error only multiplied
by a small number, the discrete form of the rate of section 3.8:

@stmt LeanDLRA/Integrators/Matrix/BUGQuasiOptimalityNormalStep.lean norm_projStep_sub_le_of_trace_of_ginv_mul_norm_le MatrixBUG.norm_projStep_sub_le_of_trace_of_ginv_mul_norm_le

The mechanism is that of the continuous case: in the identity of the step the only term of leading
order that carries the increment of the reference is `W = (1 - P₁) (X₁ - X₀) (1 - Q₀)`, which
meets the old error through the orthogonal projector `M ↦ (1 - P₁) M (1 - Q₀)` of the Frobenius
space only in a component of second order. The run, with `ν ≥ ‖(1 - P(T_r(A))) Ȧ‖` and a relative
tube radius `θ ≤ 1/16`, is in
@file(LeanDLRA/Integrators/Matrix/BUGQuasiOptimalityNormalTruncation.lean):

@stmt LeanDLRA/Integrators/Matrix/BUGQuasiOptimalityNormalTruncation.lean norm_bugRun_sub_truncation_le_mul_of_norm_sub_tangentProjAt_le norm_bugRun_sub_truncation_le_mul_of_norm_sub_tangentProjAt_le

The growth rate is `K = 9/4 (ν + lam τ)/ρ + 5/2 lam (θ + 2 h lam)`: the whole velocity is
multiplied by the relative tail `τ / ρ`, by the relative radius `θ` or by the step number `h lam`.

**The tail seen from the old reference.** In
@file(LeanDLRA/Integrators/Matrix/BUGQuasiOptimalityWeingartenStep.lean) the source `9/4 η_F τ`
is replaced by `ω`, with `ω² ≥ ‖(A₁ - X₁) Pv₀‖² + ‖Pu₀ (A₁ - X₁)‖²`, the tail at the end of the
step seen from the row and the column space of the old reference, with the factor `1` at leading
order and with every tube radius `θ < 1/2` with `η_F + θ < 1`:

@stmt LeanDLRA/Integrators/Matrix/BUGQuasiOptimalityWeingartenStep.lean norm_projStep_sub_le_of_trace_of_norm_tail_sq_le MatrixBUG.norm_projStep_sub_le_of_trace_of_norm_tail_sq_le

The source has a form in the increment of the data: for a reflexive generalized inverse `G₀` and
`g ‖A₁ - X₁‖₂ ≤ q ≤ 1`, `(1 - q)² (‖(A₁ - X₁) Pv₀‖² + ‖Pu₀ (A₁ - X₁)‖²)` is at most
`‖(A₁ - X₁) (A₁ - A₀)ᵀ G₀ᵀ‖² + ‖G₀ᵀ (A₁ - A₀)ᵀ (A₁ - X₁)‖²`, the two parts of the Weingarten map
`Z ↦ G₀ᵀ Zᵀ R + R Zᵀ G₀ᵀ` of section 3.8 at the increment of the data. The run, for every
sequence `B` that satisfies the recursion of the module docstring:

@stmt LeanDLRA/Integrators/Matrix/BUGQuasiOptimalityWeingartenTruncation.lean norm_bugRun_sub_truncation_le_of_norm_tail_sq_le norm_bugRun_sub_truncation_le_of_norm_tail_sq_le

At leading order in the step the recursion is `B (k+1) = (1 + 3/2 η_R + η_X θ d (1 + d)) B k + ω k`.
Here the hypotheses are on the data at the grid points only.

**Robust and quasi-optimal certificates on one run.** The quasi-optimal bounds need a gap
`σ_r(A) ≤ τ < ρ ≤ σ_{r-1}(A)` on every step, the robust bounds do not. In
@file(LeanDLRA/Integrators/Matrix/BUGHybridQuasiOptimality.lean) both are combined on a run in
which the rank `r n` changes from step to step. With `a n = ‖Y n - A n‖`,
`d n = ‖Y n - T_{r n}(A n)‖`, the tail `s n = ‖A n - T_{r n}(A n)‖` and local errors `δ n`, every
step satisfies `a (n + 1) ≤ a n + δ n` and `|a n - d n| ≤ s n`, and a step may be certified:
`d n ≤ Ed n → d (n + 1) ≤ Ed (n + 1)`.

@stmt LeanDLRA/Integrators/Matrix/BUGHybridQuasiOptimality.lean le_and_le_of_forall_hybrid_step le_and_le_of_forall_hybrid_step

Every pair `Ea`, `Ed` that dominates the initial errors and satisfies the two inequalities on
every step bounds both errors; the choice `Ea n = a 0 + ∑ δ` is the robust bound. A truncation of
an iterate to a lower rank is a certified step by
`EckartYoung.norm_truncation_sub_truncation_le_of_norm_sub_le`, and the gap is checked on the
iterate by `EckartYoung.le_singularValues_of_norm_sub_truncation_le`. The run of BUG steps at the
current rank with the gap checked on the iterate:

@stmt LeanDLRA/Integrators/Matrix/BUGHybridQuasiOptimality.lean norm_bugRun_sub_truncation_le_and_norm_sub_le_of_forall_hybrid_step norm_bugRun_sub_truncation_le_and_norm_sub_le_of_forall_hybrid_step

**Rank-adaptive runs.** The file @file(LeanDLRA/Integrators/Matrix/BUGAdaptiveQuasiOptimality.lean)
uses the tail seen from the old reference as source and allows two kinds of certified steps: a
step whose result is within `γ k` of a BUG step at the current rank `r k` (the gap checked on the
iterate: `ρ k + Ed k + τ k + ψ k ≤ σ_{r k - 1}(Y k)`), and a truncation
`Y (k+1) = T_{r (k+1)}(Z k)` of a matrix `Z k` with `‖Z k - Y k - ΔA‖ ≤ ζ k` to a lower, the same
or a higher rank (the augmented solution of [CerutiKuschLubich2022] is one such `Z k`), with the
gap checked on `Z k`. On every other step the bound continues with the local error `δ k` and the
tail.

@stmt LeanDLRA/Integrators/Matrix/BUGAdaptiveQuasiOptimality.lean norm_adaptiveBugRun_sub_truncation_le_and_norm_sub_le norm_adaptiveBugRun_sub_truncation_le_and_norm_sub_le

All hypotheses are on the data at the grid points and on the iterates; the sequences `Ed`, `Ea`
are any solution of the inequalities.

What is not shown. The truncation of the augmented solution is not treated in the fixed-rank files
(there `d_K`, `d_L` are not small); the adaptive file treats it through the certified steps and
the gap on `Z k`. The smallness conditions are hypotheses on the data or on the iterates. The
constants `9 / 4`, `5 / 2`, `4 / 3`, `23 / 10` are those of the proofs. The example of
@file(LeanDLRA/Integrators/Matrix/BUGQuasiOptimalityTruncation.lean) satisfies the hypotheses
of the step bound for a moving reference with a tail and an error that are not zero.

### 5.5 The constants of the BUG capture estimate and of the local error are attained

The local error bound `IsBUGStep.local_error_two_mul` (section 5.3) is
`‖Y₁ - A(t₁)‖ ≤ (e^{L h} - 1) (B h + √2 ϑ) + √2 ϑ`, `ϑ = h (2 L B h + ε)`, and rests on the
capture estimate `‖(1 - P₁) A(t₁)‖ ≤ h (2 L B h + ε)` (`kstep_capture_two_mul`). The file
@file(LeanDLRA/Integrators/BUGCaptureSharp.lean) has examples in `ℂ`, as a real inner product
space of dimension two, that bound the constants from below.

@stmt LeanDLRA/Integrators/BUGCaptureSharp.lean norm_sub_eq_local_error_two_mul BUGCaptureExample.norm_sub_eq_local_error_two_mul

@stmt LeanDLRA/Integrators/BUGCaptureSharp.lean exists_isBUGStep_mul_lt_norm_sub exists_isBUGStep_mul_lt_norm_sub

@stmt LeanDLRA/Integrators/BUGCaptureSharp.lean exists_kstep_mul_lt_norm exists_kstep_mul_lt_norm

For the constant field `ε (1 + i)` (`L = 0`), the zero old projectors and projectors after the step
onto the real and the imaginary axis, the local error bound is an equality, `‖Y₁ - A(t₁)‖ = √2 h ε`
for every `ε ≥ 0` and `h ≥ 0`; so the factor `√2` of `ε` cannot be lowered. For the field
`F(x) = 1 + i L min(|Re x|, 1)` the capture is `‖(1 - P₁) A(t₁)‖ = L / 2`, so the constant `2` of
`kstep_capture_two_mul` cannot be replaced by a number below `1 / 2`. Not shown: the optimal
constant between `1 / 2` and `2`, and the sharpness of the dependence on `L` in the exponential.

### 5.6 A posteriori bound through a lagged sweep

Let `A' = F(t, A)` with `F = M + N` one-sided Lipschitz with constant `ℓ`, and `N` Lipschitz with
constant `κ`. For any curve `Y` (for example the interpolant of the iterates of a low-rank
integrator; no differentiability is needed) let `Z` solve the equation in which `N` is evaluated
along `Y`, `Z' = M(t, Z) + N(t, Y t)`. The defect of `Z` in the full equation is
`N(t, Y) - N(t, Z)`, of norm at most `κ ‖Y - Z‖`. In
@file(LeanDLRA/Foundations/SweepAposteriori.lean):

@stmt LeanDLRA/Foundations/SweepAposteriori.lean norm_sub_le_add_gronwallBound_of_sweep norm_sub_le_add_gronwallBound_of_sweep

@stmt LeanDLRA/Foundations/SweepAposteriori.lean norm_sub_le_add_of_sweep_steps norm_sub_le_add_of_sweep_steps

The error of `Y` is bounded by the computable distance `‖Y - Z‖`, plus a Grönwall term in which
only `ℓ` and the constant `κ` of the part `N` enter. The distance `Y - Z` is the residual of `Y`
integrated with the flow of `M`, so the bound sees the norm of the integrated residual and not the
integral of its norm. For `M = 0` the curve `Z` is the Picard iterate of `Y`. The module docstring
names Picard iteration and waveform relaxation as the mechanism and [BillaudFriessNouy2017,
Prop. 1] for the residual bound with a moving reduced space.

## 6. Projector splitting and variants of the BUG integrator

### 6.1 The projector-splitting integrator

The projector-splitting integrator of [LubichOseledets2014], also called the KSL integrator,
performs the K-step, then an S-step backward in time, then the L-step, each starting from the
result of the one before.

@stmt LeanDLRA/Integrators/Matrix/ProjectorSplitting.lean IsStep MatrixKSL.IsStep

@stmt LeanDLRA/Integrators/Matrix/KSLStep.lean stepRel MatrixKSL.stepRel

@stmt LeanDLRA/Integrators/Matrix/KSLRun.lean isTubeLocal_stepRel MatrixKSL.isTubeLocal_stepRel

@stmt LeanDLRA/Integrators/Matrix/KSLRun.lean exists_run_norm_sub_le MatrixKSL.exists_run_norm_sub_le

The hypotheses are those of the BUG theorem of section 5.2, without the bound `H` on the step
size. Conclusion: there is a run of `N` projector-splitting steps of size `h` from `Y₀`, every
value has rank at most `r`, and

`‖Y n - A (t₀ + n * h)‖ ≤ e^{L T} δ + T e^{L T} (10 L B h + ε)` for all `n ≤ N`.

The constants depend on `L`, `B` and `T` only, and not on singular values. The smallness
condition `hsmall` asks that this bound plus `4 * B * h` is smaller than `ρ`. The theorem is an
instance of the run theorem of section 4.3, with the matrices of rank at most `r` as
admissible values and margin constant 4. `MatrixKSL.IsRun.norm_sub_le` gives the bound for every
run. The older form with global assumptions and a given sequence of steps is
`MatrixKSL.global_error` in
[`LeanDLRA/Integrators/Matrix/ProjectorSplitting.lean`](../LeanDLRA/Integrators/Matrix/ProjectorSplitting.lean);
its constant in front of `h` is `11 L B T e^{L T}`.

Source: [KieriLubichWalach2016, Thm. 2.1] for the error bound; [LubichOseledets2014, §3.2] for
the integrator. The explicit constants are those of the formal statement.

### 6.2 The parallel BUG integrator

In the parallel BUG integrator of [CerutiKuschLubich2024] the K-step, the L-step and the S-step
all start from the old factors `U₀`, `S₀`, `V₀` and can be computed at the same time. The
results are assembled in the bases augmented by the new directions found in the K-step and the
L-step (`MatrixParallelBUG.augmented`). The docstring of `MatrixParallelBUG.augmentedRel` says
that this matrix has rank at most `2 * r` (the core has no lemma with this bound for
`MatrixParallelBUG.augmented`); it is then truncated. The core has two results: one for the
integrator with a fixed rank `r`, in which the truncation is a best approximation of rank at
most `r`, and one for the integrator with a truncation tolerance, whose rank changes from step
to step.

**Fixed rank.**

@stmt LeanDLRA/Integrators/Matrix/ParallelBUG.lean IsStep MatrixParallelBUG.IsStep

@stmt LeanDLRA/Integrators/Matrix/ParallelBUGStep.lean augmentedRel MatrixParallelBUG.augmentedRel

@stmt LeanDLRA/Integrators/Matrix/ParallelBUGStep.lean stepRel MatrixParallelBUG.stepRel

`MatrixParallelBUG.IsStep` is the step in terms of the factors: the three differential equations
(`kSol`, `lSol`, `sSol`) with their start values, and the conditions on the new directions `U₁`,
`V₁` (orthogonal to the old bases, `perpU`, `perpV`; their ranges contain the new parts of the
K-step and the L-step, `capU`, `capV`). `MatrixParallelBUG.augmentedRel F r` is the step without
truncation as a relation between matrices, and `MatrixParallelBUG.stepRel F r` is the step of
the integrator with fixed rank: `Y₁` has rank at most `r` and is as close to the result `Yh` of
the step without truncation as a matrix of rank at most `r` can be (`distLR r Yh` is the
distance of `Yh` to the set of matrices of rank at most `r`). The docstring of the definition
notes that such a `Y₁` is computed by a truncated singular value decomposition of `Yh`; the
truncation of section 2.2 has rank at most `r` and attains the distance.

@stmt LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean isTubeLocal_stepRel MatrixParallelBUG.isTubeLocal_stepRel

@stmt LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean exists_run_norm_sub_le MatrixParallelBUG.exists_run_norm_sub_le

The hypotheses are those of the BUG theorem of section 5.2, without the bound `H` on the step
size. Conclusion: there is a run of `N` steps of size `h` from `Y₀`, every value has rank at
most `r`, and

`‖Y n - A (t₀ + n * h)‖ ≤ e^{L T} δ + T e^{L T} (24 L B h + 3 ε)` for all `n ≤ N`.

The constants depend on `L`, `B` and `T` only, and not on singular values. The smallness
condition `hsmall` asks that this bound plus `2 * B * h` is smaller than `ρ`; the margin
constant is 2 and not 4 because the three substeps all start at `Y₀` (docstring of
`MatrixParallelBUG.IsStep.norm_sub_lt_of_near`). No truncation tolerance
appears in the bound: the best approximation of rank at most `r` costs at most a constant times
the error of the step without truncation (the module docstring derives `24 = 10 + 2 * 7` and
`3 = 1 + 2 * 1`). The theorem is an instance of the run theorem of section 4.3, like the
theorems of sections 5.2 and 6.1.
`MatrixParallelBUG.IsRun.norm_sub_le` gives the bound for every run.

**Truncation tolerance, variable rank.**

@stmt LeanDLRA/Integrators/Matrix/ParallelBUG.lean global_error_paper MatrixParallelBUG.global_error_paper

This theorem has the older form: the field is Lipschitz with constant `L` and bounded by `B`
everywhere (`hF`, `hB`), and Lipschitz in time with constant `Lt` (`hFt`); the sequence of steps
is given (`hstep`), with ranks `rk k` that may change from step to step; the normal component is
at most `ε` at the numerical values at the grid times (`hε`); `Φ k` is the exact solution of the
full equation started at the `k`-th numerical value (`hΦ`, `hΦ₀`); every truncation changes the
value by at most `ϑ` (`htr`); and `h > 0`. Conclusion: for `k * h ≤ T`

`‖Y_k - A (t₀ + k * h)‖ ≤ e^{L T} δ + (7 L B + Lt) T e^{L T} h + T e^{L T} ε + T e^{L T} ϑ / h`.

The constants depend on `L`, `Lt`, `B` and `T` only. The theorem does not prove that the steps
exist and does not work on a tube. `MatrixParallelBUG.global_error` in the same file is the
variant without the Lipschitz condition in time: it assumes the bound `ε` on the normal
component at the `k`-th numerical value for all times `t` with
`t₀ + k * h ≤ t < t₀ + (k + 1) * h`, it allows `h = 0`, and its bound is
`e^{L T} (‖Y_0 - A t₀‖ + T (7 L B h + ε) + k ϑ)`.

Source: [CerutiKuschLubich2024, §3 and Thm. 4.1]; the docstring of
`MatrixParallelBUG.global_error_paper` cites the same paper as arXiv 2304.05660, Theorem 4.1.

**Truncation tolerance, runs on a tube.**

@stmt LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean adaptiveStepRel MatrixParallelBUG.adaptiveStepRel

@stmt LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean isTubeLocal_adaptiveStepRel_Ici MatrixParallelBUG.isTubeLocal_adaptiveStepRel_Ici

@stmt LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean adaptive_exists_run_norm_sub_le MatrixParallelBUG.adaptive_exists_run_norm_sub_le

The step with truncation by a tolerance `ϑ`: the three substeps are solved from the same start
value, the result `Yh` has rank at most `2 r`, and `Y₁` is any matrix with `‖Y₁ - Yh‖ ≤ ϑ`; the
truncated singular value decomposition is one such matrix
(`MatrixParallelBUG.augmentedRel.adaptiveStepRel_truncation`). The set `R` collects the numbers
of columns of the start factorization. For `R = Set.Ici r₀` with `r₀` at most both matrix sizes
the method is tube-local with every matrix admissible and margin constant 2. The run theorem
has the hypotheses of the theorem above on the tube (a `DLRAProblem`, joint continuity, the
normal bound `ε` at every number of columns `r ≥ r₀`), no hypothesis on the field outside the
tube and no singular value. Conclusion: a run exists, and for `n ≤ N`

`‖Y n - A (t₀ + n * h)‖ ≤ e^{L T} (δ + n ϑ) + T e^{L T} (7 L B h + ε)`,

if the same bound with `N` in place of `n`, plus `2 * B * h`, is smaller than `ρ`. For every run
(not only for the one that exists) `MatrixParallelBUG.IsRun.norm_sub_le_of_adaptiveStepRel`
gives the bound with the term `T e^{L T} ϑ / h` in place of `e^{L T} n ϑ`; it is the bound
`C₀ δ + C₁ h + C₂ ε + C₃ ϑ / h` of the theorem of the paper for a field that is controlled on a
tube only. The statement of existence is weak (the matrix `Yh` itself is a truncation within
every tolerance), the bound for every run is not. The theorem is an instance of the form of the
run theorem with a tolerance for every step (section 4.3). Local error of one step:
`(t₁ - t₀) (7 L B (t₁ - t₀) + ε) + ϑ`
(`MatrixParallelBUG.adaptiveStepRel.hasLocalError_of_tube`). The file ends with two `example`s,
the field `Y / max ‖Y‖ 1` (no normal component) and a linear field.

Source: [CerutiKuschLubich2024, §3 and Thm. 4.1].

### 6.3 The rank-adaptive BUG integrator

@stmt LeanDLRA/Integrators/Matrix/BUG.lean IsRankAdaptiveStep MatrixBUG.IsRankAdaptiveStep

@stmt LeanDLRA/Integrators/Matrix/BUG.lean rankAdaptive_global_error_le MatrixBUG.rankAdaptive_global_error_le

A rank-adaptive step performs the K-step and the L-step as in section 5, forms augmented bases
`Ua`, `Va` that contain both the old bases and the results of the two steps (`augU`, `kCap`,
`augV`, `lCap`), performs the S-step in the augmented bases, and truncates the result with
tolerance `ϑ` (`trunc`). The rank `r j` may change from step to step. The theorem has the older
form (global assumptions `hF`, `hB`; given steps `hstep`; exact solutions `Φ j` started at the
numerical values; the global bound `MatrixBUG.FactoredNormalBound F (r j) ε` on the normal
component at every rank that occurs). Conclusion: for `j * h ≤ T`

`‖Y_j - A (t₀ + j * h)‖ ≤ e^{L T} δ + T e^{L T} (c₁ ε + c₂ h) + e^{L T} j ϑ`

with the constants `c₁`, `c₂` of section 5.2. The constants depend on `L`, `B`, `H`, `T` only;
the truncation enters with the number `j` of steps taken.

Source: Ceruti, Kusch and Lubich, arXiv 2104.05247, Theorem 2, as cited in the docstring
(the integrator: §2.1 there).

@stmt LeanDLRA/Research/AugmentationRank.lean exists_error_ge_of_isRankAdaptiveStep AugmentationRank.exists_error_ge_of_isRankAdaptiveStep

A lower bound for one step. There are a field `F` on `3 × 2` matrices that does not depend on time
and whose normal component vanishes at every point `U S Vᵀ` with one column in `U` and `V`
(`FactoredNormalBoundOn` with `ε = 0` on the whole space), a start `U₀ V₀ᵀ` of rank one with
orthonormal factors, and a solution `A` of the differential equation from this start, such that
every rank-adaptive step of size `h > 0` from the start whose augmented left basis `Ua` has two
columns has error at least `h² / 2 - ϑ`, where `ϑ` is the truncation tolerance of the step; and
such a step with tolerance zero exists for every `h`. The field of the example is a polynomial of
degree two and is not globally Lipschitz (module docstring of the file). The same file has an
upper bound for a Galerkin step whose space contains a point close to the exact solution
(`AugmentationRank.galerkin_error_of_predictor`) and an upper bound for fields of the form `𝒜(t) Y
+ Y ℬ(t)` (`AugmentationRank.error_le_of_sylvester`; section 6.10 removes the hypotheses on the
auxiliary flows); they are not quoted here. The theorem cites no theorem of a paper.

@stmt LeanDLRA/Integrators/Matrix/AdaptiveBUGStep.lean truncStepRel MatrixBUG.truncStepRel

@stmt LeanDLRA/Integrators/Matrix/TruncBUGRun.lean trunc_exists_run_norm_sub_le MatrixBUG.trunc_exists_run_norm_sub_le

The integrator with augmented bases and truncation to a fixed rank, as a step relation.
`MatrixBUG.augmentedRel F r` is one step of the rank-adaptive integrator from a factorization of
the start value with `r` columns, before any truncation; its result `Yh` has rank at most
`2 r`. `MatrixBUG.truncStepRel F r κ` adds a truncation to rank `r`: the result has rank at most
`r`, and its distance from `Yh` is at most `κ` times `distLR r Yh`, the distance of `Yh` from
the matrices of rank at most `r`. For `κ = 1` the result is a best approximation. The
hypotheses of the theorem on `F`, `A`, the rank, the step size and the start value are those of
section 5.2, with `hκ : 1 ≤ κ` added. If the bound below plus `4 * B * h` is smaller than `ρ`
(`hsmall`), a run of `N` steps of size `h` exists, all its values have rank at most `r`, and for
`n ≤ N`

`‖Y n - A (t₀ + n * h)‖ ≤ e^{L T} δ + T e^{L T} (κ (10 L B h + ε) + (1 + κ) (c₁ ε + c₂ h))`,

with `c₁ = bugC₁ L H` and `c₂ = bugC₂ L B H`. No truncation tolerance and no singular value
appears. The theorem is an instance of the run theorem of section 4.3. The step with truncation
by a tolerance is `MatrixBUG.adaptiveStepRel` in the same file as `MatrixBUG.truncStepRel`,
with its local error (`MatrixBUG.adaptiveStepRel.hasLocalError_of_tube`); its runs are treated
next.

Source: the integrator with augmented bases is that of Ceruti, Kusch and Lubich,
arXiv 2104.05247, as cited in the module docstrings. The docstring of the theorem cites no
theorem of a paper.

**Truncation tolerance, runs on a tube.**

@stmt LeanDLRA/Integrators/Matrix/AdaptiveBUGRun.lean isTubeLocal_adaptiveStepRel_Ici MatrixBUG.isTubeLocal_adaptiveStepRel_Ici

@stmt LeanDLRA/Integrators/Matrix/AdaptiveBUGRun.lean adaptive_exists_run_norm_sub_le MatrixBUG.adaptive_exists_run_norm_sub_le

For `R = Set.Ici r₀` the step relation `MatrixBUG.adaptiveStepRel F R ϑ` is a tube-local
method with every matrix admissible (a start value is factored with any number `r ≥ r₀` of
columns) and margin constant 4. The run theorem has the hypotheses of section 5.2 on the tube,
with the normal bound `ε` at every `r ≥ r₀` (`hε`) and a truncation tolerance `ϑ ≥ 0`. Conclusion:
a run of `N` steps of size `h ≤ H` exists, and for `n ≤ N`

`‖Y n - A (t₀ + n * h)‖ ≤ bugGlobalBound L B H T δ ε h + e^{L T} (n ϑ)`,

where `bugGlobalBound L B H T δ ε h` is the bound of section 5.2; the condition `hsmall` asks
that the bound with `N` in place of `n`, plus `4 * B * h`, is smaller than `ρ`. The tolerance
enters once for every step taken, as in the older theorem above, but the fields are controlled
on the tube only, and no exact solution through the numerical values is supplied.
`MatrixBUG.IsRun.norm_sub_le_of_adaptiveStepRel` gives the bound for every run with the term
`T e^{L T} ϑ / h`. The existence statement is weak, because the matrix before truncation is a
truncation within every tolerance; the bound for every run applies to the truncated singular
value decomposition that an implementation computes. The theorem is an instance of the form of
the run theorem with a tolerance for every step (section 4.3).

Source: Ceruti, Kusch and Lubich, arXiv 2104.05247, as cited in
the module docstring; the docstring of the theorem cites no theorem of a paper.

**A-posteriori bounds, tolerance schedules and rank selection.**

@stmt LeanDLRA/Integrators/RankAdaptiveBUGAposteriori.lean rankAdaptiveBUG_aposteriori_global_error rankAdaptiveBUG_aposteriori_global_error

@stmt LeanDLRA/Integrators/RankAdaptiveBUGAposteriori.lean rankAdaptiveBUG_global_error_of_tol rankAdaptiveBUG_global_error_of_tol

@stmt LeanDLRA/Integrators/RankSelection.lean singularValues_pred_epsRank_gt singularValues_pred_epsRank_gt

The two files @file(LeanDLRA/Integrators/RankAdaptiveBUGAposteriori.lean) and
@file(LeanDLRA/Integrators/RankSelection.lean) extend the global bound of this section on the
projector level (`IsRankAdaptiveBUGStep`, `L`-Lipschitz field, given steps). The first theorem
replaces the bound `ε` of the normal component by a computable residual of the Galerkin step:
if `η n` bounds `‖F(t, YS n t) - Pa n (Qa n (F(t, YS n t)))‖` on step `n`, with tolerance `ϑ n`,
then `‖Y n - A (t₀ + n h)‖ ≤ e^{L n h} (‖Y 0 - A t₀‖ + ∑_{k<n} (ϑ k + h η k))`. The second is
the bound for a tolerance that changes from step to step: if `ϑ n ≤ τ h²`, the error is at most
`e^{L T} (δ + T (c₁ ε + (c₂ + τ) h))` with the constants `c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H` of
section 5.2, so a tolerance of order `h²` does not change the order. The older form of the
theorem is used (exact solutions `Φ n` through the numerical values). The first file also states
that a larger Galerkin space loses at most the stability factor (`galerkin_quasiMonotone_of_le`)
and that for a linear field a Galerkin space that contains the Krylov vectors `𝒜ʲ y₀`,
`j ≤ k`, of the start value gives an error of order `(h ‖𝒜‖)^{k+1}` (`galerkin_krylov_error`).
The third theorem concerns the rank decision: if the tolerance rule `epsRank θ A` keeps
`r₁ > 0` singular values, the smallest retained one is larger than `θ / √(n - r₁ + 1)`, `n` the
number of columns. The same file shows that the truncated singular value decomposition is not
continuous at equal singular values (`not_continuousAt_truncation_tie`) and how much one added
basis vector can gain (`norm_sq_sub_specNorm_sq_le_norm_sq_enrich`).

Source: the integrator is that of Ceruti, Kusch and Lubich, arXiv 2104.05247, whose Theorem 2 is
`rankAdaptiveBUG_global_error`; the statements of the two files cite no theorem of a paper.

The rank of a tolerance truncation in time stepping: a tolerance `ϑ` that does not decrease with
the step size freezes the rank, and the term `n ϑ` of the bound of the rank-adaptive integrator
is attained with the constant one; see [section 3.9](#39-optimality-of-low-rank-time-integration).

### 6.4 The BUG integrator with explicit Euler substeps

@stmt LeanDLRA/Integrators/Matrix/EulerBUGStep.lean IsStep MatrixEulerBUG.IsStep

@stmt LeanDLRA/Integrators/Matrix/EulerBUGStep.lean augmentedRel MatrixEulerBUG.augmentedRel

@stmt LeanDLRA/Integrators/Matrix/EulerBUGStep.lean stepRel MatrixEulerBUG.stepRel

A step of this integrator evaluates the field once, at the start value: `F₀ = F(t₀, Y₀)` with
`Y₀ = U₀ S₀ V₀ᵀ`. `MatrixEulerBUG.IsStep` is the step in terms of the factors. The new bases
`Ua`, `Va` have orthonormal columns, the range of `Ua` contains the columns of `U₀` and of
`F₀ V₀` (`capU`, `capK`), the range of `Va` contains the columns of `V₀` and of `F₀ᵀ U₀`
(`capV`, `capL`), and the new core is `Sa = Uaᵀ (Y₀ + (t₁ - t₀) F₀) Va` (`sStep`): the explicit
Euler step of the full problem, projected onto the new bases. `MatrixEulerBUG.augmentedRel F r`
is the step relation without truncation: a factor step from some factorization of `Y₀` with `r`
columns whose new bases have at most `2 r` columns. `MatrixEulerBUG.stepRel F r` is the
integrator with fixed rank `r`: the result `Y₁` has rank at most `r`, and its distance from a
result `Yh` of the step without truncation is at most `distLR r Yh`, the distance of `Yh` from
the matrices of rank at most `r`.

@stmt LeanDLRA/Integrators/Matrix/EulerBUGRun.lean exists_run_norm_sub_le MatrixEulerBUG.exists_run_norm_sub_le

The hypotheses on `F`, `A`, the rank and the start value are those of section 5.2. Two are
added: the field is Lipschitz in time with a constant `Lt ≥ 0` on the tube (`hFt`, `hLt`), that
is, `‖F t x - F s x‖ ≤ Lt * (t - s)` for `s ≤ t` and every `x` that lies in the tube at both
times. For a field that does not depend on time, `Lt = 0`. There is no bound `H` on the step
size. If the bound below plus `2 * B * h` is smaller than `ρ` (`hsmall`), a run of `N` steps of
size `h` exists from every start value of rank at most `r` within `δ` of `A t₀`, all its values
have rank at most `r`, and for `n ≤ N`

`‖Y n - A (t₀ + n * h)‖ ≤ e^{L T} δ + T e^{L T} ((11 L B + Lt) h + 3 ε)`.

The constants depend on `L`, `B`, `Lt` and `T`; no singular value appears, and no truncation
tolerance. The theorem is an instance of the run theorem of section 4.3. A step from `Y₀`
exists for every field if and only if `Y₀` has rank at most `r`
(`MatrixEulerBUG.exists_stepRel_iff`, for `r` at most the number of rows and of columns), and
the bound holds for every run (`MatrixEulerBUG.IsRun.norm_sub_le`). The error analysis of the
step for orthogonal projectors on a general state space, on which the local error rests, is in
[`LeanDLRA/Integrators/EulerBUG.lean`](../LeanDLRA/Integrators/EulerBUG.lean).

Source: the integrator is Algorithm 1 of Nobile and Riffaud, arXiv 2502.07040, §2.1, as cited
in the module docstrings of the two files. The docstring of the theorem cites no theorem of a
paper.

### 6.5 The midpoint BUG integrator: second order

@stmt LeanDLRA/HighOrder/MidpointBUGGlobal.lean midpointBUG_global_error_le midpointBUG_global_error_le

The midpoint BUG integrator in projector form on a general state space
(`MidpointBUG.IsMidpointBUGStep`,
[`LeanDLRA/HighOrder/MidpointBUG.lean`](../LeanDLRA/HighOrder/MidpointBUG.lean)). The theorem
has the older form: the steps are given (`hstep`), and so are the exact solutions `Φ n` that
start at the numerical values (`hΦ`, `hΦ₀`). The hypotheses on the field are global: `F` is
Lipschitz with constant `L` and bounded by `B`, the map `(t, x) ↦ F t x` is twice continuously
differentiable (`hF₂`), and its first and second derivatives are bounded by `M₁` and `M₂`
(`hM₁`, `hM₂`). `ε` bounds the normal components in the first half step, `ε₂` the normal
component of `F` at the midpoint predictor in the augmented bases, and `ϑ` is the truncation
tolerance (fields of the step predicate; docstring of the theorem). Conclusion: for `n ≤ N`
with `n * h ≤ T` and `h ≤ H`

`‖Y n - A (t₀ + n * h)‖ ≤ e^{L T} δ + T e^{L T} C (ε₂ + h ε + h²) + e^{L T} n ϑ`,

with `C = midpointBUGConst L M₁ B (M₂ (1 + B)² + M₁² (1 + B)) H` (docstring of the theorem). The
constants depend on `L`, `B`, `M₁`, `M₂`, `T` and `H`, and on no singular value. The error is of
second order in `h` up to the terms with `ε₂`, `h ε` and the tolerance.

Source: Ceruti, Einkemmer, Kusch and Lubich, arXiv 2402.08607, Theorem 2, as cited in the
module docstring. The docstring of the theorem lists the differences: the paper assumes the
bounds in a neighbourhood of the exact solution and a bound of the third derivative of exact
solutions; here the bounds on `F` are global and the third derivative is bounded through `M₁`
and `M₂`.

**The midpoint BUG step on matrices, and runs.**

@stmt LeanDLRA/HighOrder/Defs.lean augmentedRel#1 MatrixMidpointBUG.augmentedRel

@stmt LeanDLRA/HighOrder/Defs.lean stepRel#1 MatrixMidpointBUG.stepRel

The theorem above has given steps. The step of the fixed-rank integrator on matrices is defined
in [`LeanDLRA/HighOrder/Defs.lean`](../LeanDLRA/HighOrder/Defs.lean) as a relation between the
old and the new value (`StepRel`, section 4.1). `MatrixMidpointBUG.IsStep` is the step at the
level of the factors, without truncation: an augmented BUG step over the half interval
`[t₀, t½]`, `t½ = (t₀ + t₁) / 2`, which gives the midpoint predictor `Yh = Uh Sh(t½) Vhᵀ`; then
orthonormal bases `Ub`, `Vb` whose ranges contain the columns of `(Uh, F(t½, Yh) Vh)` and of
`(Vh, F(t½, Yh)ᵀ Uh)`; and the Galerkin step `Sb' = Ubᵀ F(t, Ub Sb Vbᵀ) Vb` over the whole
step. `augmentedRel F r` is the result `Ub Sb(t₁) Vbᵀ` of such a step from a factorization with
`r` columns: the half step has exactly `2 r` columns and `Ub`, `Vb` at most `4 r` (the "4r
variant"). `stepRel F r` truncates it: the new value has rank at most `r` and is at most as far
from the result of `augmentedRel` as the distance of that result from the matrices of rank at
most `r` (`distLR`), so every best approximation, in particular the truncated singular value
decomposition, is allowed.

@stmt LeanDLRA/HighOrder/MidpointBUGStep.lean stepRel.hasLocalError MatrixMidpointBUG.stepRel.hasLocalError

The local error of one step. The normal bounds `ε` at rank `r` and `ε₂` at rank `2 r` hold on a
tube around a solution `A` (`FactoredNormalBoundOn`); `F` is `L`-Lipschitz, bounded by `B` and
of class `C²` with `‖DF‖ ≤ M₁` and `‖D²F‖ ≤ M₂` as a map of `(t, Y)`; the start value is near the
solution (`hsmall`). Then the local error is at most
`h (e^{L H} ε + 2 C (h² + h ε + ε₂))` with `h = t₁ - t₀ ≤ H` and the constant `C` of the theorem
above. The step without truncation has the local error `C h (h² + h ε + ε₂)`
(`MatrixMidpointBUG.augmentedRel.hasLocalError`). Both are taken from the projector form
(`MatrixMidpointBUG.IsStep.isMidpointBUGStep` is the bridge) and are not proved a second time.

@stmt LeanDLRA/HighOrder/MidpointBUGRun.lean isTubeLocal_stepRel MatrixMidpointBUG.isTubeLocal_stepRel

@stmt LeanDLRA/HighOrder/MidpointBUGRun.lean exists_run_norm_sub_le MatrixMidpointBUG.exists_run_norm_sub_le

The fixed-rank midpoint BUG integrator is a tube-local method (section 4.3) with the matrices of
rank at most `r` as admissible values and margin constant 2, if `2 r` is at most both matrix
sizes. The run theorem: with the hypotheses on `F` above, a solution `A` of the full equation on
`[t₀, t₀ + N h]`, `0 ≤ h ≤ H`, `N h ≤ T`, a start value of rank at most `r` with
`‖Y₀ - A t₀‖ ≤ δ`, and the condition `hsmall` (the bound plus `3 B h` is below the tube radius
`ρ`), a run `Y 0 = Y₀, …, Y N` of `stepRel F r` exists, every `Y n` has rank at most `r`, and

`‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (e^{L H} ε + 2 C (h² + h ε + ε₂))`.

The constants depend on `L`, `B`, `M₁`, `M₂`, `T` and `H`, and on no singular value of any
`Y n`. For `ε = ε₂ = 0` the bound is of order `h²`; with `ε`, `ε₂` the terms `h ε` and `ε₂`
do not go to zero with `h`. `MatrixMidpointBUG.IsRun.norm_sub_le` gives the bound for every
run, not only for the one that exists. The theorem is an instance of the run theorem of
section 4.3 with the margin constant raised from 2 to 3. The local error is taken from the
projector form, whose hypotheses on the regularity of `F` are global: only the normal bounds are
localized to the tube, and the bounds on `F` and its derivatives are assumed everywhere. The
paper assumes these bounds near the exact solution only.

Source: Ceruti, Einkemmer, Kusch and Lubich, arXiv 2402.08607, §3, Algorithm 1 (the 4r variant),
as cited in the module docstrings. The statements cite no theorem of a paper.

### 6.6 The explicit midpoint update in augmented bases

A step from the factored point `Y₀ = U₀ S₀ V₀ᵀ` with step size `h`, defined in the module docstring
of
[`LeanDLRA/Research/ExplicitMidpointGalerkin.lean`](../LeanDLRA/Research/ExplicitMidpointGalerkin.lean):
the predictor `Z = Y₀ + (h/2) P₀ F(t₀, Y₀)` with `P₀ = tangentProj U₀ V₀` (no differential equation
is solved for it), one evaluation `G = F(t₀ + h/2, Z)`, augmented bases `Ua`, `Va` with
orthonormal columns that contain `U₀`, `V₀` and whose ranges contain those of `G V₀` and
`Gᵀ U₀`, and then either the Galerkin flow of `galerkinProj Ua Va` over the step or the explicit
update `Y₁ = Y₀ + h • galerkinProj Ua Va G`. The file proves local errors for both. The
quantities
`θ = ‖(1 - Ua Uaᵀ) G (1 - V₀ V₀ᵀ)‖` and `θ' = ‖(1 - U₀ U₀ᵀ) G (1 - Va Vaᵀ)‖`, the capture defects,
are hypotheses (`hθ`, `hθ'`) of every statement of that file except the last one: the bases are
given. The size of `θ` and `θ'` is bounded in a second file, at the end of this section, and the
two files are combined for the explicit update in the last statement of this section.

@stmt LeanDLRA/Research/ExplicitMidpointGalerkin.lean ODESolution.norm_midpoint_defect_le ODESolution.norm_midpoint_defect_le

Midpoint-rule defect of an exact solution: if `A` solves `y' = F(t, y)` on `[t₀, t₀ + h]`, is of
class `C³` there and its third derivative is bounded by `M₃`, then the defect is at most
`M₃ h³ / 24`. The constant is the sharp one of `MidpointBUG.midpoint_defect_le_sharp`. The
companion `ODESolution.norm_half_step_sub_le` gives, for `C²` and the bound `M₂` of the second
derivative, `‖A(t₀ + h/2) - A t₀ - (h/2) F(t₀, A t₀)‖ ≤ M₂ h² / 8`.

@stmt LeanDLRA/Research/ExplicitMidpointGalerkin.lean norm_one_sub_galerkinProj_le_of_capture ExplicitMidpoint.norm_one_sub_galerkinProj_le_of_capture

@stmt LeanDLRA/Research/ExplicitMidpointGalerkin.lean norm_predictor_sub_le ExplicitMidpoint.norm_predictor_sub_le

Two ingredients. If `Ua`, `Va` capture `G V₀` and `Gᵀ U₀` and the capture defects are at most `θ`
and `θ'`, then `G` is at most `θ + θ'` away from the Galerkin space of `Ua`, `Va`; the identity
behind it splits `G - galerkinProj Ua Va G` into one term for each defect
(`ExplicitMidpoint.sub_galerkin_eq_of_capture`). If the normal component of `F` is at most `ε` at
the factored point `Y₀`, the predictor is within `M₂ h² / 8 + (h/2) ε` of the exact solution at
the midpoint of the step.

@stmt LeanDLRA/Research/ExplicitMidpointGalerkin.lean galerkin_local_error ExplicitMidpoint.galerkin_local_error

The local error of the Galerkin step. With `η = M₂ h² / 8 + (h/2) ε` it is at most
`(e^{L h} - 1) h ((L B + Lₜ) h / 2 + L η + θ + θ') + h (L η + θ + θ') + M₃ h³ / 24`. The
hypotheses on the field are those of section 6.5: `F` is `L`-Lipschitz, bounded by `B` and
`Lₜ`-Lipschitz in time. The statement is an instance of `MidpointBUG.midpointGalerkin_local_error`
with the predictor of this section in place of a half step of the BUG integrator.

@stmt LeanDLRA/Research/ExplicitMidpointGalerkin.lean norm_update_sub_le ExplicitMidpoint.norm_update_sub_le

The local error of the explicit update, with two evaluations of `F` and no differential equation:

`‖Y₁ - A(t₀ + h)‖ ≤ h (θ + θ') + L h² ε / 2 + h³ (M₃ / 24 + L M₂ / 8)`.

Here `F` is `L`-Lipschitz only on a region `D` that contains `(t₀, Y₀)`, `(t₀ + h/2, Z)` and
`(t₀ + h/2, A(t₀ + h/2))` (`IsLipschitzFieldOn`, `hDZ`, `hDA`), and the normal component is
bounded on `D` (`FactoredNormalBoundOn`, section 3.3). The terms are of order `h`
(the capture defects), `h²` (the normal component at the start) and `h³`. These are local errors
of one step. The page states no global error for this step: the file contains none.

Source: the module docstring cites Ceruti, Einkemmer, Kusch and Lubich, arXiv 2402.08607, for the
Galerkin step (the docstring of `galerkin_local_error` names its Theorem 1). The explicit update
has no source line in the docstrings. The file ends with `example`s that satisfy the hypotheses of
`ODESolution.norm_midpoint_defect_le`, `ODESolution.norm_half_step_sub_le`, `norm_predictor_sub_le`,
`galerkin_local_error` (a constant field, every `h > 0`) and `norm_update_sub_le` (a field for
which every rank-adaptive BUG step with a two-column left basis has error at least h²/2,
with `h = 3/2`).

**Size of the capture defect.**

@stmt LeanDLRA/Research/ExplicitMidpointCapture.lean norm_capture_defect_le norm_capture_defect_le

@stmt LeanDLRA/Research/ExplicitMidpointCapture.lean norm_capture_defect_right_le norm_capture_defect_right_le

The quantity `θ` of the explicit midpoint step is bounded for every orthonormal `Ua` whose range
contains those of `U₀` and `G V₀`, where `G = F(t₀ + h/2, Z)` is the field at the predictor `Z`.
The hypotheses are on a region `D` that contains the segment in time over the ball of radius `ρ`
around `Y₀ = U₀ S₀ V₀ᵀ`: the normal bound `ε` at rank `r` (`hN`), the Lipschitz constant `L`
(`hL`), the bound `B` (`hB`), the Lipschitz constant `Lₜ` in time (`hFt`), and `r` smaller than
both matrix sizes. The parameter `τ > 0` and the numbers `κ`, `e`, `δ` are chosen by the user,
with `κ ≥ √r (ε / (2 τ) + L̃)`, `e ≥ √r (ε + L̃ τ / 2)`, `L̃ = max L (2 B / ρ)`, and `δ` at least
the expression of `hδ`; then `θ` is at most
`(L + κ + h/2 L κ) δ + ε + e + (h/2)² κ (L B + Lₜ + B κ)`. The constants contain `‖S₀‖` and no
inverse of `S₀`, so they do not depend on small singular values; the splitting of the mixed
components of the field uses the regularized inverse `(S₀ᵀ S₀ + τ² 1)⁻¹` in place of a singular
value decomposition (module docstring). All norms are Frobenius norms, which is the reason for
the factors `√r`. The second theorem is the same bound for `θ'`, by transposition. The file has
`example`s for the hypotheses of both.

**The capture defect is of order `h² + ε`, and the combined local error.**

@stmt LeanDLRA/Research/ExplicitMidpointCapture.lean norm_capture_defect_le_sq_add norm_capture_defect_le_sq_add

@stmt LeanDLRA/Research/ExplicitMidpointCapture.lean norm_capture_defect_right_le_sq_add norm_capture_defect_right_le_sq_add

@stmt LeanDLRA/Research/ExplicitMidpointGalerkin.lean norm_update_sub_le_cube_add ExplicitMidpoint.norm_update_sub_le_cube_add

The first two theorems are the choice `τ = h² + ε` in the two theorems above. For `0 < h ≤ H`
and numbers `κ`, `D₁`, `D₂` that satisfy the lower bounds `hκ`, `hD₁`, `hD₂` (with
`L̃ = max L (2 B / ρ)`) and the smallness condition `hsmall`, the capture defect satisfies

`θ ≤ C₁ h² + C₂ ε`,

with `C₁ = (L + κ + (H/2) L κ) D₁ + √r L̃/2 + κ (L B + Lₜ + B κ)/4` and
`C₂ = (L + κ + (H/2) L κ) D₂ + 1 + √r (1 + L̃/2)`, and the same bound for `θ'`. The constants
contain `‖S₀‖` (through `D₁`) and no inverse of `S₀`: they do not depend on the small singular
values of `S₀`. This replaces the free parameter `τ` of the two theorems above by the size of the
step and of the normal component, and it is the form in which the capture defect enters the
local error of the explicit update (and, below, the runs). The third theorem inserts both bounds
into
`norm_update_sub_le`: under the hypotheses of the first two (on a region `D` that contains the
ball around `Y₀` and the exact solution at the midpoint) and with bounds `M₂`, `M₃` of the second
and third derivative of the exact solution, the explicit update has the local error

`‖Y₁ - A(t₀ + h)‖ ≤ h³ (2 C₁ + M₃/24 + L M₂/8) + h ε (2 C₂ + L h/2)`,

that is `O(h³ + h ε)`. Two evaluations of `F` and no differential equation are needed, and no
singular value of `S₀` enters. What is not shown: the Galerkin step (`galerkin_local_error`) is
not combined with the capture bounds; the constants `C₁`, `C₂` are those of this proof.

The module docstring of `LeanDLRA/Research/ExplicitMidpointCapture.lean` cites [CerutiEtAl2024b]
as the source of the integrator; it cites no paper for the bound of the capture defect.

**Runs of the explicit midpoint method.**

@stmt LeanDLRA/HighOrder/Defs.lean stepRel#3 ExplicitMidpoint.stepRel

@stmt LeanDLRA/Research/ExplicitMidpointRun.lean exists_stepRel ExplicitMidpoint.exists_stepRel

@stmt LeanDLRA/Research/ExplicitMidpointRun.lean isTubeLocal_stepRel ExplicitMidpoint.isTubeLocal_stepRel

@stmt LeanDLRA/Research/ExplicitMidpointRun.lean exists_run_norm_sub_le ExplicitMidpoint.exists_run_norm_sub_le

The step relation (`ExplicitMidpoint.stepRel F r`, defined in
[`LeanDLRA/HighOrder/Defs.lean`](../LeanDLRA/HighOrder/Defs.lean) next to `augmentedRel`, the
step before truncation) is the explicit update of this section from a factorization with `r`
columns, followed by a best approximation of rank at most `r`: the result is at most as far from
the update as the distance of the update to the matrices of rank at most `r`. It is carried out
with two evaluations of `F` and no differential equation. A step exists from every matrix of
rank at most `r` for every field, if `2 r` is at most both matrix sizes (second statement). Near
a reference solution the steps of the tube extension are the steps of `F`, and the method is
tube-local with margin constant 2 (third statement; section 4.3). The local error of one step
near the reference solution is `h (C₁ h² + C₂ ε)` (`ExplicitMidpoint.stepRel.hasLocalError`):
the update of the combined local error above, plus the distance of the exact solution to the
matrices of rank at most `r`, at most `h ε e^{L h}`, plus the error of the truncation
(`norm_bestTrunc_sub_le`).

The last statement is the run theorem. The hypotheses are those of
`MatrixMidpointBUG.exists_run_norm_sub_le` (section 6.5): `F` is `L`-Lipschitz and bounded by
`B`, the uncurried field is of class `C²` with `‖DF‖ ≤ M₁` and `‖D²F‖ ≤ M₂`, everywhere; the
normal part of `F` is at most `ε` at the factored points with `r` columns of the tube around a
solution `A` (`FactoredNormalBoundOn`); no normal bound at rank `2 r` is needed. For constants
`C₁`, `C₂` that are bounded below by explicit expressions in `r`, `L`, `B`, `M₁`, `M₂`, `H`, a
radius `σ` of the balls on which the capture is estimated, and `‖A t₀‖ + B T + ρ`, and under two
smallness conditions, every start value of rank at most `r` within `δ` of `A t₀` starts a run of
rank at most `r` with

`‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (C₁ h² + C₂ ε)`.

The same bound holds for every run (`ExplicitMidpoint.IsRun.norm_sub_le`). The error is of second
order in `h` up to a multiple of `ε`, and no inverse of a singular value enters the constants. The
derivative bounds of the exact solution come from `M₁`, `M₂`
(`ODESolution.norm_iteratedDerivWithin_two_le_of_contDiff` and its companion for the third
derivative). What is not shown: the regularity bounds on `F` are global, as for the midpoint BUG
integrator, and the constants are those of this proof, not sharp ones; the page makes no
statement about the Galerkin step of this section in runs. The module docstring cites
[KieriVandereycken2019, Thm. 6], robust second order of projected explicit Runge–Kutta methods
of order two at rank `r`, and [CerutiEtAl2024b] for the integrator whose Galerkin space contains
`U₀` and `G V₀` in the same way.

### 6.7 The dynamical randomized SVD

@stmt LeanDLRA/Randomized/DRSVDStep.lean augmentedRel MatrixDRSVD.augmentedRel

@stmt LeanDLRA/Randomized/DRSVDStep.lean stepRel MatrixDRSVD.stepRel

@stmt LeanDLRA/Randomized/DRSVDStep.lean stepRel.hasLocalError_of_tube MatrixDRSVD.stepRel.hasLocalError_of_tube

The integrator of Carrel (arXiv 2410.17091, Algorithm 3) in the variant with an augmented
sketch. `W` is a matrix with `k` orthonormal columns whose range contains the row space of the
start value `Y₀`; the B-step solves `B' = F(B Wᵀ) W` from `Y₀ W`; a matrix `Q` with `l`
orthonormal columns captures the result `B(t₁)`; the C-step solves `C' = F(Q Cᵀ)ᵀ Q` from
`Y₀ᵀ Q`; the result `Q C(t₁)ᵀ` is truncated to rank `r` by a best approximation. The sketch is
data of the relation: the relation holds for every sketch with these properties, and no
probability enters any statement. The step is a step of the BUG integrator with one mode
(`MatrixDRSVD.isTuckerBUGStepCore_of_factors`), and through that bridge the local error is the
local error of the BUG step. The local error of the theorem above is
`(t₁ - t₀) ((2 c₁ + 1) ε + (2 c₂ + 10 L B) (t₁ - t₀))` with `c₁ = bugC₁ L H`,
`c₂ = bugC₂ L B H`, under the normal bound `ε` at rank `r` and at `k` columns, `k ≤ l`.

@stmt LeanDLRA/Randomized/DRSVDRun.lean isTubeLocal_stepRel MatrixDRSVD.isTubeLocal_stepRel

@stmt LeanDLRA/Randomized/DRSVDRun.lean exists_run_norm_sub_le MatrixDRSVD.exists_run_norm_sub_le

The method is tube-local with the matrices of rank at most `r` admissible and margin constant 3
(the B-step moves by at most `B h`, and the C-step starts at `Q Qᵀ Y₀`, which is within `B h` of
`Y₀`). The run theorem has the hypotheses of section 5.2 on the tube and the normal bound `ε` at
`r` and at `k` columns (`hε`). Conclusion: for a start value of rank at most `r` a run
exists, all its values have rank at most `r`, and for `n ≤ N`

`‖Y n - A (t₀ + n * h)‖ ≤ e^{L T} δ + T e^{L T} ((2 c₁ + 1) ε + (2 c₂ + 10 L B) h)`.

No truncation tolerance appears, since the truncation is a best approximation of rank at most
`r`. `MatrixDRSVD.IsRun.norm_sub_le` gives the bound for every run, in particular for runs with
the sketches that an implementation draws. The statements say nothing about how likely it is
that a random sketch has the properties that the relation asks for; they hold for every sketch
that has them. Compared with the older bound of `RandomizedBUG.drsvd_global_error_le`, the
hypotheses on `F` are needed on the tube only and no exact solutions through the numerical
values are supplied; the price is the smallness condition and the larger constants.

Source: Carrel, arXiv 2410.17091, §§2–3, as cited in the module docstrings.

### 6.8 The projected Euler method and projected Runge–Kutta methods

@stmt LeanDLRA/Integrators/Matrix/FlowDistance.lean distLR_flow_le_exp_of_tube distLR_flow_le_exp_of_tube

@stmt LeanDLRA/Matrix/LowRankDistance.lean distLR_flow_le_exp distLR_flow_le_exp

Both methods retract to the matrices of rank at most `r` after a step of the projected equation
`Y' = P(Y) F(t, Y)`, and the analysis needs a bound for the distance of the exact solution to
those matrices that has no term `h²`. The second theorem is the global form: `F` is
`L`-Lipschitz and bounded, the normal bound `ε` holds at every factored rank-`r` matrix, and the
solution starts at a matrix of rank at most `r`; then the distance after a step of size `h` is at
most `h ε e^{L h}`, with constant 1 in front of `h ε`. The first theorem is the form for a field
that is controlled on a tube around a reference solution only; it requires the margin
`‖Φ t₀ - A t₀‖ + 3 B (t₁ - t₀) < ρ`. The global theorem cannot be applied to the tube extension
of the field, so the first theorem proves its own statement by splitting the step into `N`
substeps and letting `N` tend to infinity (module docstring of
[`LeanDLRA/Integrators/Matrix/FlowDistance.lean`]
(../LeanDLRA/Integrators/Matrix/FlowDistance.lean)).

Source: Kieri and Vandereycken, Comput. Methods Appl. Math. 19 (2019), eq. (15) (proof of their
Theorem 2), as cited in the docstring; there it is obtained from the solution of the projected
equation, which the two theorems do not use.

@stmt LeanDLRA/Matrix/LowRankDistanceFlow.lean distLR_flow_le_sharp distLR_flow_le_sharp

The same distance along an exact solution `A` on `[t₀, t₁]` for a start value of any rank:
`distLR r (A t) ≤ e^{L (t - t₀)} distLR r (A t₀) + ε (t - t₀) e^{L (t - t₀)}`, with the constant
one in front of `ε`. The field is `L`-Lipschitz, bounded, continuous in time and has the normal
bound `ε` at the factored matrices of rank `r`. The module docstring says that the bound itself is
`distLR_flow_le_exp_mul_add` in `LeanDLRA/Matrix/LowRankDistance.lean` and that this file keeps
the recorded form of the statement; for a start of rank at most `r` it gives
`h ε e^{L h}` after time `h`, which is `distLR_flow_le_exp`. That the constant one cannot be
lowered is not proved there; the docstring names a constant field for which the library
certifies a lower bound `t / 3`.

@stmt LeanDLRA/Integrators/Matrix/ProjectedEuler.lean stepRel MatrixProjEuler.stepRel

@stmt LeanDLRA/Integrators/Matrix/ProjectedEuler.lean stepRel.hasLocalError_of_tube MatrixProjEuler.stepRel.hasLocalError_of_tube

@stmt LeanDLRA/Integrators/Matrix/ProjectedEuler.lean exists_run_norm_sub_le MatrixProjEuler.exists_run_norm_sub_le

The projected Euler method `Y₁ = ℛ(Y₀ + (t₁ - t₀) P(Y₀) F(t₀, Y₀))` with a retraction `ℛ` to the
matrices of rank at most `r` that is `κ`-quasi-optimal (`‖ℛ(X) - X‖ ≤ κ dist(X, M_{≤ r})`;
`κ = 1` is the truncated singular value decomposition). The method is tube-local with margin
constant 0, since the step evaluates the field at the start value only
(`MatrixProjEuler.isTubeLocal_stepRel`). The local error is
`(t₁ - t₀) ((10 κ L B + (1 + κ) (L B + Lₜ) / 2) (t₁ - t₀) + (1 + 2 κ) ε)`. The run theorem has
the hypotheses of section 6.4: the tube, the normal bound `ε` at rank `r`, and the Lipschitz
condition `hFt` in time with constant `Lt`. Conclusion: a run from a start value of rank at most
`r` exists, its values have rank at most `r`, and

`‖Y n - A (t₀ + n * h)‖ ≤ e^{L T} δ + T e^{L T} c` with
`c = (10 κ L B + (1 + κ) (L B + Lt) / 2) h + (1 + 2 κ) ε`.

For `κ = 1` the constant is that of section 6.4. The one-sided Lipschitz constant of the paper is
not used: the bound has `e^{L T}`. Neither a projected solution nor full rank of the numerical
values is assumed (module docstring).

Source: Kieri and Vandereycken, Comput. Methods Appl. Math. 19 (2019), §4, Lemma 3 and
Theorem 4, as cited in the docstrings.

@stmt LeanDLRA/HighOrder/Defs.lean stepRel#2 MatrixPRK.stepRel

@stmt LeanDLRA/Integrators/Matrix/ProjectedRK.lean exists_run_norm_sub_le MatrixPRK.exists_run_norm_sub_le

@stmt LeanDLRA/HighOrder/ProjectedRK.lean norm_sub_le_of_stages ProjectedRK.norm_sub_le_of_stages

The projected Runge–Kutta method with an explicit tableau `(a, b, c)` of `s` stages: every stage
and the result are a retraction of the start value plus `h` times a combination of projected
stage derivatives. The local error is analyzed in the abstract setting of
[`LeanDLRA/HighOrder/ProjectedRK.lean`](../LeanDLRA/HighOrder/ProjectedRK.lean) (the second
theorem above, `‖y₁ - w_f‖ ≤ h · localErrorConst a b L κ · (ε + g + K h^{q'})`) and for matrices
in [`LeanDLRA/Integrators/Matrix/ProjectedRK.lean`]
(../LeanDLRA/Integrators/Matrix/ProjectedRK.lean).
The matrix method is tube-local with margin constant `(1 + κ) α + 1`, `α = tabWeight a b`
(`MatrixPRK.isTubeLocal_stepRel`). The run theorem has the hypotheses of the projected Euler
theorem and in addition a hypothesis `hRK` on the classical scheme: from every start value of
rank at most `r` near `A`, the classical Runge–Kutta step of `F` has local error `K h^{p+1}` and
stage errors `K h^{q_j+1}`. These orders are hypotheses, because the core has no order theory of
Runge–Kutta methods; the theorem is weaker than the run theorems of the other integrators, whose
local errors are proved from the hypotheses on `F`. Conclusion: a run exists, has rank at most
`r`, and

`‖Y n - A (t₀ + n * h)‖ ≤ e^{L T} δ + T e^{L T} C (ε + ε e^{L h} + K h^{q'})`,
`C = localErrorConst a b L κ`,

for every admissible exponent `q'` (`ProjectedRK.admissible_min_q₂`,
`ProjectedRK.admissible_of_b₂_eq_zero` give the exponent of the paper). The step size is at most
1. The constants are those of the proof and are not optimized. A projected Heun method serves as
the non-vacuity example.

Source: Kieri and Vandereycken, Comput. Methods Appl. Math. 19 (2019), §5, Lemma 7 and
Theorem 6, as cited in the docstrings.

### 6.9 A field with a two-sided term: a leak bound for one rank-adaptive step

@stmt LeanDLRA/Research/TwoSidedLeak.lean error_le_of_twoSided AugmentationRank.error_le_of_twoSided

The field is `F(Y) = 𝒜 Y + Y ℬ + C Y D` with constant coefficients, and one step of the
rank-adaptive BUG integrator starts at `Y₀ = U₀ S₀ V₀ᵀ`. For `C = 0` the Galerkin space of the
step contains the exact solution (`AugmentationRank.capture_of_sylvester`). A two-sided term
destroys this unless `C` maps the range of `U₀` into itself and `D` maps the row space of `V₀`
into itself. The amount by which it does not is measured by the leaks
`ν_C = ‖(1 - U₀ U₀ᵀ) C U₀ S₀‖`,
`ν_D = ‖S₀ V₀ᵀ D (1 - V₀ V₀ᵀ)‖` and the unweighted `ℓ_C = ‖(1 - U₀ U₀ᵀ) C U₀‖`,
`ℓ_D = ‖V₀ᵀ D (1 - V₀ V₀ᵀ)‖`. The theorem bounds the error of one step with truncation tolerance
`ϑ` by

`(e^{L h} - 1) (θ + M₂ h²) + θ + ϑ`, `θ = 2 h e^{L h} (ε₀ + h Γ₁ (ν_C + ν_D + ℓ_C ℓ_D) + h² Γ₂)`,

where `ε₀` bounds the normal component of `F` at the start, `M₂` bounds the derivative of
`t ↦ F(t, A(t))`, and `Γ₁`, `Γ₂` depend on bounds of the coefficients, of `‖S₀‖` and of the
increments of the substep solutions; no singular value enters. So the local error is of order
`h³` if `ε₀ = 0` and the leaks are `O(h)`, and of order `h²` otherwise. The statement is a
sufficient condition for local order three; it does not characterize it, and the bound is not
sharp in every case (the module docstring gives a case with a vanishing leak of `D` where the
capture is exact while the bound keeps a term `h² ν_C`). The auxiliary flows of the Sylvester
case (`P`, `Z`, `Q`, `Zr`) and the bounds on the increments of the K- and L-step solutions are
hypotheses; for `P` and `Q` existence with continuous coefficients is shown in section 6.10
(`exists_rightFactor_of_sylvester`), as the module docstring of this file says; the existence
of the corrections `Z`, `Zr` is not formalised. The theorem is a bound for one step: it gives no
global error. The file ends with a step on `2 × 2` matrices for which the leak of `C` is 1 and
the hypotheses hold (`AugmentationRank.isRankAdaptiveStep_leakLeft`,
`AugmentationRank.leak_leakLeft`).

Source: the module docstring cites [CerutiKuschLubich2022] and [CerutiEtAl2024b, Sec. 5.2].

@stmt LeanDLRA/Research/TwoSidedPadded.lean error_le_of_twoSided_of_leaks_eq_zero AugmentationRank.error_le_of_twoSided_of_leaks_eq_zero

**Padded start.** The same matrix `Y₀ = U₀ S₀ V₀ᵀ` can be written in bases `Ũ`, `Ṽ` whose ranges
contain those of `U₀`, `C U₀` and of `V₀`, `Dᵀ V₀`, with the coefficient matrix
`S̃ = Ũᵀ U₀ S₀ V₀ᵀ Ṽ`, the old coefficients padded with zeros
(`AugmentationRank.mul_paddedCoeff_mul_transpose_eq`: `Ũ S̃ Ṽᵀ = U₀ S₀ V₀ᵀ`). For the padded
factors the weighted leaks and the normal component at the start vanish
(`leftLeak_paddedCoeff_eq_zero`, `rightLeak_paddedCoeff_eq_zero`). The theorem above is the
local error of a rank-adaptive step whose start has vanishing weighted leaks:

`‖Y₁ - A(t₁)‖ ≤ (e^{L h} - 1) (θ + M₂ h²) + θ + ϑ`, `θ = 2 h e^{L h} (h Γ₁ ℓ_C ℓ_D + h² Γ₂)`.

What remains is the product `ℓ_C ℓ_D` of the unweighted leaks of the padded bases: the local error
is of order three in `h` only when that product is `O(h)`, which is a sufficient condition and
not a characterisation. The auxiliary flows and the increment bounds are hypotheses, as in
`error_le_of_twoSided`; the padded bases must have the same number of columns; no global error
is stated. The module docstring cites [CerutiKuschLubich2022] and Appelö and Cheng,
arXiv 2402.05347, Section 3.1 (bases merged with the column and row spaces of the field).

### 6.10 Fields of Sylvester type: the rank-adaptive step captures the solution

The files of this section treat the rank-adaptive BUG integrator (`MatrixBUG.IsRankAdaptiveStep`,
section 6.3) on fields `F(t, Y) = 𝒜(t) Y + Y ℬ(t)` on `m × n` matrices. The module docstrings
cite Ceruti, Kusch and Lubich, arXiv 2104.05247. Section 6.3 mentions the older statements
`AugmentationRank.capture_of_sylvester` and `AugmentationRank.error_le_of_sylvester`, which take
two auxiliary flows `P` and `Q` as hypotheses; the first file of this section shows that these
flows exist.

@stmt LeanDLRA/Research/SylvesterFlows.lean exists_odeSolution_sylvester AugmentationRank.exists_odeSolution_sylvester

@stmt LeanDLRA/Research/SylvesterFlows.lean capture_of_sylvester_of_continuousOn AugmentationRank.capture_of_sylvester_of_continuousOn

@stmt LeanDLRA/Research/SylvesterFlows.lean error_le_of_sylvester_of_continuousOn AugmentationRank.error_le_of_sylvester_of_continuousOn

The linear equation `X' = C(t) X + X D(t)` with coefficients continuous on `[t₀, t₁]` has a
solution on `[t₀, t₁]` from every starting value. The proof extends the coefficients constantly
outside the interval; no matrix exponential is used and the coefficients may depend on time. It
gives the flows `P' = P ℬ - (V₀ᵀ ℬ V₀) P`, `P(t₀) = V₀ᵀ` and `Q' = 𝒜 Q - Q (U₀ᵀ 𝒜 U₀)`,
`Q(t₀) = U₀` (`exists_rightFactor_of_sylvester`, `exists_leftFactor_of_sylvester`). With them,
for continuous coefficients, the hypotheses on `P` and `Q` of the older statements disappear:
for a step started on the exact solution (`hA₀`), the Galerkin space of the step contains the
exact solution at the end of the step, `Ua Uaᵀ A(t₁) = A(t₁)` and `A(t₁) Va Vaᵀ = A(t₁)`, and the
local error is at most `(e^{L h} - 1) M₂ h² + ϑ`, where `M₂` bounds the derivative of
`t ↦ F(t, A(t))` and `ϑ` is the truncation tolerance. No singular value and no normal component
of the field enters.

@stmt LeanDLRA/Research/SylvesterGlobal.lean rankAdaptive_global_error_le_of_sylvester AugmentationRank.rankAdaptive_global_error_le_of_sylvester

The global error. `N` steps of the rank-adaptive BUG integrator with step size `h`, truncation
tolerance `ϑ` and ranks that may change from step to step; the exact solutions `Φ j` start at the
numerical values (`hΦ`, `hΦ₀`, the older form) and `M₂` bounds the derivative of
`t ↦ F(t, Φ j t)` along them. For `j h ≤ T`

`‖Y j - A (t₀ + j h)‖ ≤ e^{L T} (δ + T L e^{L h} M₂ h² + j ϑ)`,

with `δ` the initial error. So on these fields the integrator has global order two up to the
truncation term `j ϑ`, without a normal component and without a singular value in the bound. The
proof is Lady Windermere's fan with the local bound above.

@stmt LeanDLRA/Research/PerturbedSylvester.lean error_le_of_perturbedSylvester AugmentationRank.error_le_of_perturbedSylvester

A Lipschitz perturbation. The field is `F(Y) = 𝒜 Y + Y ℬ + G(Y)` with constant `𝒜`, `ℬ` and a
`g`-Lipschitz map `G`. With `a`, `b` bounds of `‖𝒜‖`, `‖ℬ‖`, `γ₀` a bound of `‖G(Y₀)‖`, `B` a
bound of `F` along the exact solution and the K- and L-step solutions, and `ε₀` a bound of the
normal component of `F` at the start, the capture defect of the Galerkin space is at most

`θ = 2 h ε₀ + 4 e^{3 (a + b) h} h² (g B + (a + b) γ₀)`

(`AugmentationRank.norm_sub_galerkinProj_le_of_perturbedSylvester`), and the theorem bounds the
error of the step by `(e^{L h} - 1) (θ + M₂ h²) + θ + ϑ`. So the local error is
`O(h ε₀ + (g B + (a + b) γ₀) h² + h³)`, and no singular value of `S₀` enters. The exponent
`3 (a + b) h` makes the bound useless for stiff coefficients (module docstring). Not shown: a
global error bound for this field; the bounds `hBA`, `hBK`, `hBL` of `F` along the solutions are
hypotheses of the statement.

@stmt LeanDLRA/Research/RankOneGalerkinBarrier.lean sq_div_le_error_of_rankOne_galerkin AugmentationRank.sq_div_le_error_of_rankOne_galerkin

A lower bound for a Galerkin step in one fixed rank-one space. The field is `F(Y) = W Y` on `2 ×
2` matrices with the rotation generator `W = [[0, -1], [1, 0]]` and the start `Y₀ = e₁ e₁ᵀ` of
rank one with singular value one; the exact solution is `A(t) = (cos t, sin t)ᵀ e₁ᵀ`. For every
pair of orthonormal `u`, `v` the Galerkin solution `Ŷ' = u uᵀ (W Ŷ) v vᵀ` started at `u uᵀ Y₀ v
vᵀ` does not move (`AugmentationRank.galerkin_eq_start_of_rankOne`, because `uᵀ W u = 0`), and its
error at time `h` is at least `(1 - cos h) / 2` (`AugmentationRank.error_ge_of_rankOne_galerkin`)
and at least `h² / π²` for `0 ≤ h ≤ π`. The local error of every such step is therefore of size at
least `h²`: a method of local order three at rank `r` cannot be a Galerkin step in one fixed space
of rank `r`. The rank-adaptive integrator, which uses a space of rank `2 r`, is exact up to
`O(h³)` on this field (`AugmentationRank.error_le_of_sylvester`). The bound is not the smallest
error over `u`, `v` (module docstring); it concerns this one field and the Galerkin step with a
fixed space, not other methods of rank `r`.

## 7. Stiff problems and the primal–dual error representation

A problem is called stiff here if the Lipschitz constant `L` of the field is large while its
one-sided Lipschitz constant `ℓ` is moderate or negative:

@stmt LeanDLRA/Analysis/Defs.lean IsOneSidedLipschitzField IsOneSidedLipschitzField

### 7.1 The implicit BUG integrator

@stmt LeanDLRA/Stiff/ImplicitBUG.lean IsImplicitBUGStep IsImplicitBUGStep

One step of the BUG integrator with backward Euler substeps, in projector form on a general
state space: implicit K-step and L-step (`kstep`, `lstep`), new projectors `P₁`, `Q₁` that
capture their results up to a tolerance `τ` (`kcap`, `lcap`), bounds `ε` for the normal
components at these results, an implicit Galerkin step (`sstep`) and a truncation with tolerance
`ϑ` (`trunc`).

@stmt LeanDLRA/Stiff/ImplicitSolvability.lean implicitBUG_wellPosed implicitBUG_wellPosed

Solvability of the substeps. Let the field be one-sided Lipschitz with constant `ℓ` and Lipschitz
(with any constant), and let `h ≥ 0` with `h * ℓ < 1`. Then each of the three implicit equations
of a step has exactly one solution, for any orthogonal projectors, and under the additional
hypothesis `hF0` (`⟪F t y, y⟫ ≤ ℓ * ‖y‖²`) the solution `YS` of the Galerkin equation satisfies
`(1 - h * ℓ) * ‖YS‖ ≤ ‖Y₀‖`. The condition on the step size involves `ℓ` and not `L`; for
`ℓ ≤ 0` every step size is allowed. The space has to be complete.

@stmt LeanDLRA/Stiff/ImplicitBUG.lean implicitBUG_global_error_le implicitBUG_global_error_le

Error bound of the older form (global assumptions, given steps, exact solutions `Φ n` started
at the numerical values). In addition to `L` and `B` the field has a Lipschitz constant `Lₜ` in
time (`hFt`) and a one-sided Lipschitz constant `ℓ` (`hos`), and the step size satisfies
`h * L ≤ 1` and `h * ℓ ≤ 1 / 2`. Conclusion: for `n * h ≤ T`

`‖Y n - A (t₀ + n * h)‖ ≤ e^{L T} (‖Y 0 - A t₀‖ + T ((14 L B + 8 Lₜ) h + 6 ε) + n (6 τ + ϑ))`.

The constants do not depend on singular values. They do depend on the Lipschitz constant `L`,
through the factor `e^{L T}`, through `14 L B` and through the step size restriction
`h * L ≤ 1`; in this sense the bound is not uniform in the stiffness. The core has no global
error bound for a low-rank integrator whose constants depend only on `ℓ`. For one step, section
7.3 has a bound without the Lipschitz constant of the field, and section 7.4 a family of
problems for which no bound of the form `K (h ε + h²)` holds with one constant `K`.

Source: the step is the first-order scheme of Nakao, Qiu and Einkemmer, arXiv 2311.15143, §3.1,
and of Saha, Yang and Yin, arXiv 2610.18419, Algorithm 3.1, as cited in the docstring. The two
theorems cite no theorem of a paper.

**The step on matrices, and runs.**

@stmt LeanDLRA/Stiff/Defs.lean IsStep MatrixImplicitBUG.IsStep

@stmt LeanDLRA/Stiff/Defs.lean stepRel MatrixImplicitBUG.stepRel

@stmt LeanDLRA/Stiff/ImplicitBUGStep.lean exists_stepRel MatrixImplicitBUG.exists_stepRel

@stmt LeanDLRA/Stiff/ImplicitBUGRun.lean exists_run_norm_sub_le MatrixImplicitBUG.exists_run_norm_sub_le

`MatrixImplicitBUG.IsStep` is one step of the fixed-rank integrator at the level of the factors
([`LeanDLRA/Stiff/Defs.lean`](../LeanDLRA/Stiff/Defs.lean)): backward Euler K-, L- and S-steps,
and new bases that contain the results of the K- and L-step. The stage equations of a backward
Euler step can have several solutions, and for a field that is controlled only near a solution a
solution far away carries no information. The step therefore asks for the solution that the
fixed-point iteration from the start value reaches. For a field that is Lipschitz with constant
`L` on the whole space and `h L < 1` the iteration is a contraction, its limit is the only
solution, and the condition asks nothing beyond the equations
(`MatrixImplicitBUG.IsStep.of_lipschitz`).
`MatrixImplicitBUG.stepRel F r` is the step relation (section 4.1).

[`LeanDLRA/Stiff/ImplicitBUGStep.lean`](../LeanDLRA/Stiff/ImplicitBUGStep.lean) shows that a step
is a step `IsMatrixImplicitBUGStep` of the core with capture tolerance zero and no truncation, so
the analysis of this section applies to it; that its stages stay within `B h` of the start value
(the S-stage within `3 B h`), so that a step sees the field only on a ball around the start
value and near a reference solution the steps of the tube extension are the steps of `F`; the
local error for a field that is Lipschitz, bounded and Lipschitz in time on a tube
(`MatrixImplicitBUG.IsStep.hasLocalError_of_tube`); and the existence of a step for a globally
Lipschitz field with `h L < 1`, by Banach's fixed point theorem and without continuity in time
(third statement).

The run theorem (fourth statement,
[`LeanDLRA/Stiff/ImplicitBUGRun.lean`](../LeanDLRA/Stiff/ImplicitBUGRun.lean)): `F` is
`L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around a solution `A`, jointly
continuous, `Lt`-Lipschitz in time, with normal part at most `ε` at the rank-`r` matrices of the
tube, and `h L ≤ 1 / 2`. Every start value of rank at most `r` within `δ` of `A t₀` starts a run
of rank at most `r` with

`‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} ((14 L B + 8 Lt) h + 6 ε)`,

if `N h ≤ T` and the right-hand side plus `4 B h` is below `ρ`; the bound holds for every run
(`MatrixImplicitBUG.IsRun.norm_sub_le`). **This is not a stiff error bound.** The constants are
those of `implicitBUG_global_error_le` and contain `L` through `e^{L T}`, `L B` and the step size
condition `h L ≤ 1 / 2`; for a stiff field the bound is as poor as for the explicit integrators.
The integrator is not a row of the table of section 4.3 (see there), so the run theorem is
proved from the form for the uniform grid. The core has no run theorem for this integrator whose
constants depend on the one-sided Lipschitz constant only. The module docstrings cite
[CerutiLubich2022] for the fixed-rank integrator and arXiv 2610.18419, Algorithm 3.1, for the
backward Euler substeps.

### 7.2 The primal–dual error representation

The file
[`LeanDLRA/Stiff/DualWeightedResidual.lean`](../LeanDLRA/Stiff/DualWeightedResidual.lean)
treats a linear problem `A' = 𝓛 A + q` discretized by the implicit Euler method, and the linear
output `⟪ψ N, ·⟫` of the last value, given by the last element of a sequence `ψ` of dual
values. `A` is the implicit Euler sequence of the full problem (hypothesis `hA`), `Y` any other
sequence (the low-rank values), and `𝓛' k` the adjoint of `𝓛 k` (`hadj`). The output error is
`⟪ψ N, Y N - A N⟫`. The file has variants for nonlinear problems with a linearization remainder
(`primalDual_error_identity_of_linearization`), which are not quoted here. The primal residual
of `Y` is
`R_k = Y (k+1) - Y k - h (𝓛 k (Y (k+1)) + q k)` and the dual residual of `ψ` is
`ρ_k = ψ k - h 𝓛' k (ψ k) - ψ (k+1)`.

@stmt LeanDLRA/Stiff/DualWeightedResidual.lean primalDual_error_identity primalDual_error_identity

@stmt LeanDLRA/Stiff/DualWeightedResidual.lean dual_error_representation dual_error_representation

The identity holds for arbitrary sequences `Y` and `ψ`: the error of `Y` weighted by `ψ n`
equals the weighted initial error, plus the primal residuals weighted by `ψ`, minus the dual
residuals paired with the errors. If `ψ` solves the discrete adjoint equation exactly (`hψ`, the
dual residuals vanish), the output error is exactly the weighted initial error plus the sum of
the weighted primal residuals. No constants appear, and the identities are equalities: no
singular value, no Lipschitz constant and no step size restriction enters. The reference `A`
is the implicit Euler sequence of the full problem and not the exact solution of the
differential equation.

@stmt LeanDLRA/Stiff/DualWeightedResidual.lean abs_corrected_output_sub_le abs_corrected_output_sub_le

The product bound. If `⟪𝓛 k x, x⟫ ≤ ℓ * ‖x‖²`, `h ≥ 0` and `h * ℓ < 1`, the output corrected by
the weighted primal residuals differs from the reference output `⟪ψ N, A N⟫` by at most the
initial term `‖ψ 0‖ * ‖Y 0 - A 0‖` plus a sum of products: the norm of the `k`-th dual residual
times the initial error plus the norms of the primal residuals up to index `k`, with the
stability factor `a = max 1 (1 - h * ℓ)⁻¹` to the power `k + 1`. The factor depends on `h` and
`ℓ` and not on a Lipschitz constant.

@stmt LeanDLRA/Stiff/DualWeightedResidual.lean galerkin_output_error galerkin_output_error

@stmt LeanDLRA/Stiff/DualWeightedResidual.lean implicitBUG_dualConsistent_output_error implicitBUG_dualConsistent_output_error

If every step of `Y` is an implicit Galerkin step with an orthogonal projector `P k` (`hY`) and
the dual value `ψ k` lies in the range of `P k` (`hψP`), the weighted primal residuals vanish
and the output error consists of the initial term and the dual residual terms only. The last
theorem is the same statement for the implicit BUG step of section 7.1 whose new bases contain
`ψ k` (`hψ`), followed by a truncation `consTrunc (C k) (T k)` that keeps the part of the value
in the range of a projector `C k` containing `ψ (k+1)` (`hC`, `hCψ`, `hT`, `hY`). There the
dual residuals are paired with the errors of the values `X k` before the truncation. The
truncation tolerances `ϑ k` and the singular values do not occur in the identity.

Status of these results. The mechanism is classical, and the module docstring of the file
claims no novelty for it. The docstring names dual-weighted residual error representations
(Becker and Rannacher, Acta Numerica 10, 2001), adjoint correction of output functionals
(Pierce and Giles, SIAM Review 42, 2000) and primal–dual output bounds for reduced bases. The
vanishing of the weighted primal residuals for Galerkin steps is Galerkin orthogonality, and a
bound by products of primal and dual residuals is the classical output superconvergence
estimate. The file states the identities for arbitrary sequences `Y` and `ψ`, with the implicit
Euler sequence of the full problem as reference, so that they apply to low-rank time
integrators. The truncation `consTrunc` is the conservative truncation of Einkemmer, Ostermann
and Scalone, arXiv 2206.09374, as cited in its docstring:

@stmt LeanDLRA/Stability/Conservation.lean consTrunc consTrunc

### 7.3 One step for a field with a stiff linear part: coupling numbers

@stmt LeanDLRA/Stiff/CouplingLocalError.lean IsRankAdaptiveBUGStep.stiff_local_error IsRankAdaptiveBUGStep.stiff_local_error

@stmt LeanDLRA/Stiff/CouplingLocalError.lean stiffCaptureConst stiffCaptureConst

A local error bound for one rank-adaptive BUG step in projector form on a general state space
(`IsRankAdaptiveBUGStep`: the step of section 5 with exact substeps, new projectors `P₁`, `Q₁`
that fix `Y₀`, and a truncation with tolerance `ϑ`). The field is `F t x = 𝓛 x + G t x` with a
continuous linear map `𝓛` (`hsplit`); `F` is one-sided Lipschitz with constant `ℓ` (`hF`) and
`G` is Lipschitz with constant `LG` (`hG`). The number `κ` bounds the two off-diagonal blocks of
`𝓛` with respect to the range of `P₀` and its complement, and the same for `Q₀` (`hκP`, `hκP'`,
`hκQ`, `hκQ'`); the module docstring calls such a number a coupling number of `𝓛` with the
projector. The number `κh` bounds one such block for the product `P₁ * Q₁` of the new projectors
(`hκh`). Along the exact solution `A` on `[t₀, t₁]`, `B₁` bounds `‖F t (A t)‖` and `B₂` bounds
`‖𝓛 (F t (A t))‖` (`hB₁`, `hB₂`). The step starts at the exact value (`hA₀`), which lies in the
ranges of `P₀` and `Q₀` (`hP₀Y`, `hQ₀Y`). Conclusion, with `h = t₁ - t₀`:

`‖Y₁ - A t₁‖ ≤ (κh + LG) B₁ h² max(1, e^{ℓ h}) + 2 h (ε + C h) + ϑ`, `C = stiffCaptureConst ℓ LG κ B₁ B₂ h`.

In the quoted statement the middle term is `2 * stiffCapture ℓ LG κ B₁ B₂ ε h`, which equals
`2 h (ε + C h)` by `stiffCapture_eq`. The bound contains neither the norm of `𝓛` nor a Lipschitz
constant of `F`, and no singular value. It is a bound for one step from the exact value; the
core has no global error bound of this form. The number `κh` depends on the bases computed in
the step, and no bound for it in terms of the data of the problem is proved (module docstring of
the file).

Source: the theorem cites no theorem of a paper. The module docstring compares it with the
local error bounds of [CerutiLubich2022, Lemma 4] and [CerutiKuschLubich2022, Thm. 2] and refers
to [CarrelVandereycken2023, §2.3] for low-rank integrators for stiff problems.

### 7.4 A family of stiff problems without a uniform constant for one step

@stmt LeanDLRA/Research/StiffOrderReduction.lean not_exists_uniform_bound StiffOrderReduction.Example.not_exists_uniform_bound

The file
[`LeanDLRA/Research/StiffOrderReduction.lean`](../LeanDLRA/Research/StiffOrderReduction.lean)
applies one BUG step to the linear matrix differential equation `Y' = Y N + C`
(`StiffOrderReduction.field`), starting on the exact solution. `StiffOrderReduction.Example` is
a family of such problems on `2 × 3` matrices with a start value of rank one and the parameters
`c`, `s` with `c² + s² = 1`, `lam > 0` and `σ`. In the theorem, `result c s lam σ h` is the
result of one rank-adaptive BUG step of size `h` with exact substeps, augmented bases with two
columns and truncation tolerance zero (`StiffOrderReduction.Example.isRankAdaptiveStep`),
`exact U₀ (S₀ σ) (V₀ c s) D h` is the exact solution at time `h`, and `normalDefect c s lam σ`
is the norm of the normal component of the field at the start value; it equals `|s|`
(`StiffOrderReduction.Example.normalDefect_eq`). The theorem says that no constant `K` bounds
the error of the step by `K (h ε + h²)`, `ε = normalDefect c s lam σ`, for all members of the
family and all step sizes `0 < h ≤ 1/2`. For every member the exact solution is affine in time
with a derivative of norm `√2`; the norm of `N` is `lam`, which is not bounded over the family
(docstring of the theorem). The explicit form is
`StiffOrderReduction.Example.order_reduction_explicit`: for `0 < h ≤ 1/2`, `lam ≥ 2 / h³`,
`s = √(2 / (h lam))` and `c = √(1 - s²)` the normal component is at most `h` and the error of
the step is at least `(√3 / 4) h`.

The statement is about one step with exact substeps and about this family only. It does not
exclude bounds whose constants contain other quantities of the operator `N` (module docstring
of the file). The constants of the bound of section 7.3 contain such quantities, the coupling
numbers.

Source: the theorem cites no theorem of a paper. The module docstring refers to
[CerutiLubich2022], [CerutiKuschLubich2022] and [CarrelVandereycken2023, §2.3].

### 7.5 No stiffness-uniform global bound when the forcing varies on the scale of the step

@stmt LeanDLRA/Research/StiffGlobalCycle.lean half_le_norm_sub_exactState StiffGlobalCycle.half_le_norm_sub_exactState

@stmt LeanDLRA/Research/StiffGlobalCycle.lean not_exists_uniform_global_bound StiffGlobalCycle.not_exists_uniform_global_bound

The file
[`LeanDLRA/Research/StiffGlobalCycle.lean`](../LeanDLRA/Research/StiffGlobalCycle.lean) applies
the rank-adaptive BUG integrator with step size `h` and truncation tolerance zero to
`Y' = Y N + G(t)` on `2 × 2` matrices, `N = -diag(0, lam)`, where the forcing `G` is piecewise
constant with period `3 h`, so that the step size is part of the data. One cycle of three steps
starts at the rank-one state `σ w vᵀ`: an active step in which the added content is damped, a
free step that is exact, and a return step that is exact and ends on `σ w vᵀ` again. The
numerical solution is `3 h`-periodic (`StiffGlobalCycle.exists_cycle`); the exact solution gains
a part that is not damped in every cycle (`StiffGlobalCycle.exists_exact_cycle`). The first
theorem: if `lam s² h ≥ 2`, the error after `J` cycles is at least `J h / 2`, one sixth of the
elapsed time `3 J h`. The second theorem: there is no constant `K` such that for all admissible
parameters with `0 < σ` and `σ lam ≤ 1`, all step sizes `h` and all `J` with `3 J h ≤ 1`, the
error after `J` cycles is at most `K (h (1 + |log h|) + s)`. In the proof `s = h`, `lam = 2 / h³`,
`σ = h³ / 2` and `3 J h = 1`.

What the family satisfies: the forcing does not depend on the solution, `N` is symmetric negative
semidefinite, the normal component at the start of the active step is `|s|`, and the truncation
tolerance is zero. Under `σ lam ≤ 1` the forcing is bounded uniformly over the family:
`StiffGlobalCycle.norm_sq_cycleForcing_le` gives `‖G‖² ≤ 1 + 2 s² ≤ 3` on every step of a cycle.
What the family does not satisfy: regularity of the forcing in time that is uniform in `h`; the
forcing jumps at the grid points. So the theorem concerns forcing that may vary on the scale of the
step. It says nothing about forcing with regularity bounded independently of `h`, and nothing about
other integrators. It concerns the global error and complements section 7.4, which concerns one
step. Section 7.6 measures the error of this family against the variation of the forcing.

Source: the theorem cites no theorem of a paper. The module docstring refers to the smoothing
estimates of arXiv 1803.10473, Assumption 1(a).

### 7.6 Stiff problems with forcing: six results and what stays open

The files of this section concern the rank-adaptive BUG integrator for the stiff linear problem
`Y' = 𝓛 Y + g(t)` with a dissipative operator `𝓛` (`⟪𝓛 x, x⟫ ≤ 0`), for example
`𝓛 Y = M Y + Y N` with symmetric negative semidefinite `M`, `N`. They are stated for the step
predicate `IsRankAdaptiveBUGStep` of the projector form (`F`, tolerance `ϑ`, bound `ε`, projectors
`P₀ Q₀ P₁ Q₁`, results `YK YL YS Y₁` of the K-, L- and S-substep and of the step). The question
behind them is whether the global error is bounded by `C (h (1 + Var g) + ε + n ϑ)` with a
constant `C` that does not depend on the stiffness, for a forcing `g` of bounded variation `Var g`
in time. **This question is open in the core**: the files prove a lower bound that shows that this
form cannot be improved on, upper bounds that hold for every stiffness but contain numbers that
are not bounded by the data, and a family that shows that one natural way to bound those numbers
fails.

@stmt LeanDLRA/Research/StiffGlobalVariation.lean variation_mul_le_norm_sub_exactState StiffGlobalCycle.variation_mul_le_norm_sub_exactState

Lower bound in terms of the variation. `StiffGlobalCycle` (section 7.5) uses a forcing that is
piecewise constant with period `3 h`, `cycleForcing c s lam σ h k`, on `2 × 2` matrices. The
three jumps of one cycle have norms that add up to at most 6, for every stiffness `lam` and step
size (`StiffGlobalCycle.variation_cycleForcing_le`). If `lam s² h ≥ 2`, the error after `J` cycles
is at least `h / 12` times `J` times the sum of the three jumps, that is at least `h / 12` times
the variation of the forcing over these cycles. Hence a bound that is uniform in the stiffness and
contains the variation of the forcing must contain it at least in the form `h · Var g`, with a
factor at least `1 / 12`; a bound `C h (1 + Var g)^γ` with `γ < 1` is excluded. The theorem does
not decide whether `C (h (1 + Var g) + ε + n ϑ)` holds uniformly in the stiffness.

@stmt LeanDLRA/Research/StiffEnergyGalerkin.lean IsRankAdaptiveBUGStep.stiff_energy_error IsRankAdaptiveBUGStep.stiff_energy_error

@stmt LeanDLRA/Research/StiffEnergyGalerkin.lean stiff_energy_global_error stiff_energy_global_error

An energy bound without coupling numbers. Let `𝓛` be symmetric and dissipative, `A` an exact
solution on the step, and `R = P₁ Q₁` the projector onto the Galerkin space of the step. The
stiff operator enters through one number only: `γ²` bounds the energy `-⟪𝓛 η, η⟫` of the part
`η = A(t) - R A(t)` of the exact solution outside the Galerkin space (`hγ`), and `θ` bounds
`‖η(t₁)‖` (`hθ`). Then for one step

`‖Y₁ - A t₁‖ ≤ ‖Y₀ - A t₀‖ + γ √((t₁ - t₀) / 2) + θ + ϑ`.

The step need not start on the exact solution, and the error at the start enters with the factor
one. The second theorem adds this up over `N` steps on any grid: the error is at most the initial
error plus `∑ₙ (γₙ √(hₙ / 2) + θₙ + ϑₙ)`. The bound contains neither `‖𝓛‖` nor the coupling
numbers of section 7.3. The forcing `g` is an arbitrary function of time and may jump at the grid
points. Not shown: no bound for `γₙ` and `θₙ` in terms of the data is proved, so the theorem does
not show that the global error is small for a forcing of bounded variation. For the step of
`StiffCouplingExample` the bound holds with `γ = 0` and is attained for every stiffness, while
the coupling numbers of that step grow with the stiffness; for the exact solution
`StiffCouplingExample.decaySol`, which decays like `e^{-λ t}` outside the Galerkin space, the
hypotheses hold with `γ = √λ`, so the energy term is not zero (examples at the end of the file).
The inequality for one Galerkin step is `stiff_galerkin_energy_compare`; it is the estimate of
the Galerkin method for parabolic problems.

@stmt LeanDLRA/Research/StiffOldColumnGalerkin.lean stiff_error_of_comm_left IsRankAdaptiveBUGStep.stiff_error_of_comm_left

@stmt LeanDLRA/Research/StiffOldColumnGalerkin.lean stiff_global_error_of_comm_left stiff_global_error_of_comm_left

Invariant old column space. Let the projector `P₀` onto the old column space commute with `𝓛`
(`hP𝓛`; true for `𝓛 Y = Y N` with symmetric negative semidefinite `N` and `P₀ Y = U₀ U₀ᵀ Y`),
let `P₀ Y₀ = Y₀`, and let `β` bound the part `g - P₀ g` of the forcing outside the old column
space (`hβ`). The bound contains neither `‖𝓛‖` nor a coupling number nor any quantity of the
exact solution: the error of the step is at most the initial error plus two numbers of the step,
`‖P₀ Ŷ - Y_L(t₁)‖` (the difference on the old columns between the S-step result `Ŷ = YS t₁` and
the L-step result) and `‖Ŷ - P₀ Ŷ‖` (the part on the added columns), plus `β (t₁ - t₀) + ϑ`. The
reason is that the equation splits along `P₀`. The second theorem is the sum over steps on any
grid, with `ωₙ = ‖Pₙ Ŷₙ₊₁ - Y_{L,n}(τₙ₊₁)‖` and `2 βₙ (τₙ₊₁ - τₙ)` in place of the second and
third number. Not shown: no bound for the numbers `ωₙ` in terms of the data is proved; the
file reduces the question, for operators that commute with the old column projectors, to a bound
for `∑ₙ ωₙ`.

@stmt LeanDLRA/Research/StiffOldColumnVariation.lean stiff_global_error_of_piecewise_const_uniform stiff_global_error_of_piecewise_const_uniform

@stmt LeanDLRA/Research/StiffOldColumnVariation.lean norm_left_galerkin_sub_lstep_le IsRankAdaptiveBUGStep.norm_left_galerkin_sub_lstep_le

Forcing that is constant on every step, with value `cₙ` on step `n`, and a symmetric `𝓛` that
commutes with the old and the augmented left projectors. The numbers `βₙ` are then given by the
data: the jump `‖cₙ₊₁ - cₙ‖` of the forcing, the bound `ε`, and the part of the old forcing in
the augmented column space that the column space after the step has lost (`hcol` asks that none
is lost). The numbers `ωₙ` are bounded by the L-step alone (second theorem):
`ω ≤ 2 μ (t₁ - t₀)` if `‖𝓛 (Y_L(t) - Y₀)‖ ≤ μ` on the step, that is, if the velocity of the
L-step changes by at most `μ`. For a uniform grid of step size `h` the first theorem gives

`‖Y_N - A(τ_N)‖ ≤ ‖Y₀ - A(τ₀)‖ + ∑ₙ (ωₙ + ϑₙ) + 2 h (‖c₀ - P₀ c₀‖ + ∑ₙ ‖cₙ₊₁ - cₙ‖) + 2 h N ε`.

Here `∑ₙ ‖cₙ₊₁ - cₙ‖` is the variation of the forcing and `h N` the length of the time interval,
so the terms other than `∑ₙ ωₙ` have the form `h · Var g` and `h N ε` of the question above. What
remains is `∑ₙ ωₙ`, which is at most `2 h` times the sum of the changes of the velocities of the
L-steps. Not shown: a bound for that sum in terms of the data, the case that the Galerkin result
has smaller rank than the augmented basis or that the truncation removes a column on which the
forcing acts (the hypothesis `hcol` fails), and steps whose augmented row space is not invariant
under `𝓛`.

@stmt LeanDLRA/Research/StiffVelocityVariation.lean sqrt_mul_norm_le_sum_norm_map_sub StiffVelocityVariation.sqrt_mul_norm_le_sum_norm_map_sub

The sum of the velocity changes is not bounded by the data. A bound for `∑ₙ ωₙ` that is
proportional to `h` would follow if the sum of the numbers `μₙ` over the steps were at most a
constant times the velocity at the start plus the variation of the forcing, with a constant that
does not depend on `𝓛`. The theorem shows that there is no such constant. For every `K` and every
step size `h > 0` the file gives `2 ^ K` steps of the integrator for `F(t, x) = 𝓛 x + c` with a
symmetric negative semidefinite `𝓛` whose `K` eigenvalues are `-log 2 / (h 2 ^ k)`, a constant
forcing, and all normal parts and truncation errors zero (`isRankAdaptiveBUGStep_dyadicTrajectory`).
For this family, with `𝓛 xs + c = 0` at a stationary point `xs`,

`∑ₙ ‖𝓛 (Y_{L,n}(τₙ₊₁) - Yₙ)‖ ≥ (√K / 4) ‖𝓛 Y₀ + c‖`.

With `N = 2 ^ K` steps the factor is `√(log₂ N) / 4`, which is unbounded. What this does not
show: in this family the Galerkin results equal the results of the L-steps and the global error
of the integrator is zero. The theorem shows that the sum of the velocity changes is the wrong
quantity to bound in order to prove the question above; it does not show that the error is
large. The module docstring says that the square root of the logarithm is the true size for this
family (an upper bound by the Cauchy–Schwarz inequality), which is not proved in the library.

@stmt LeanDLRA/Research/StiffInvariantGalerkin.lean stiff_error_of_invariant_galerkin IsRankAdaptiveBUGStep.stiff_error_of_invariant_galerkin

@stmt LeanDLRA/Research/StiffInvariantGalerkin.lean stiff_global_error_of_invariant_galerkin stiff_global_error_of_invariant_galerkin

Invariant Galerkin space. Let the range of `P₁ Q₁`, the Galerkin space of the step, be invariant
under `𝓛`. For matrices and `𝓛 Y = M Y + Y N` this holds when the augmented column space is
invariant under `M` and the augmented row space under `N`. The operator need not be symmetric
and the projectors need not commute with it. On an invariant space the Galerkin step is the
exact flow of the equation in which the part `f` is replaced by its projection, so its only
defect is the part of `f` outside the Galerkin space along the Galerkin trajectory: if `f` is
one-sided Lipschitz with constant `ℓ` along the Galerkin trajectory and the exact solution, and
`‖f(t, Ŷ(t)) - P₁ Q₁ f(t, Ŷ(t))‖ ≤ η` on the step, then

`‖Y₁ - A(t₁)‖ ≤ gronwallBound ‖Y₀ - A(t₀)‖ ℓ η (t₁ - t₀) + ϑ`.

The bound contains neither `‖𝓛‖` nor a coupling number, no quantity of the exact solution after
the start, and no quantity of the K- or L-step. For a forcing `g(t)` it reads
`‖Y₁ - A(t₁)‖ ≤ ‖Y₀ - A(t₀)‖ + η (t₁ - t₀) + ϑ`
(`IsRankAdaptiveBUGStep.stiff_error_of_invariant_galerkin_forcing`), and for a symmetric `𝓛`
that commutes with the augmented projectors and a forcing constant on the step it is
`‖Y₀ - A(t₀)‖ + 2 ε (t₁ - t₀) + ϑ` with the bound `ε` for the normal parts
(`stiff_error_of_invariant_const`). The second theorem adds this over `N` steps on any grid and
for an arbitrary forcing: `‖Y_N - A(τ_N)‖ ≤ ‖Y₀ - A(τ₀)‖ + ∑ₙ (ηₙ (τₙ₊₁ - τₙ) + ϑₙ)`. The forcing
may jump at every grid point; its variation and the columns lost by the truncation do not
enter, in contrast to `stiff_global_error_of_piecewise_const_uniform`. What is not shown: the
invariance is a hypothesis on the augmented bases of every step, and the core does not show that
the integrator produces invariant bases (for `𝓛 Y = Y N` it holds, for example, if the rows of the
start value and of the forcing seen by the L-step lie in an invariant subspace of `N` whose
dimension is the rank); no bound for `η` in terms of `ε` is proved for a part `f` that depends on
the state. For the example at the end of the file the error after the time `t` is `|b| t` for
every stiffness. This result does not decide the question above: the numbers `ωₙ` of the
old-column bound do not appear, and no bound for `η` in terms of the data is proved. The module
docstring cites
[CerutiKuschLubich2022], whose error bound depends on the Lipschitz constant of the whole
right-hand side.

**Summary.** Proved: the form `h · Var g` cannot be improved (lower bound with the factor
`1 / 12`); an energy bound with two unbounded numbers `γₙ`, `θₙ`; a bound for invariant old
column spaces with the unbounded numbers `ωₙ`, in which the forcing enters through its variation;
a family showing that the velocity changes `μₙ` are not controlled by the data; and a bound for
invariant Galerkin spaces that contains no coupling number and no quantity of the exact solution
after the start, in which the part `η` of the forcing outside the Galerkin space remains. Open:
whether
a bound `C (h (1 + Var g) + ε + n ϑ)` with `C` independent of the stiffness holds, for forcing of
bounded variation, in any of these classes.

Source: the integrator is that of [CerutiKuschLubich2022]; the energy bound and the module
docstrings refer to [OstermannPiazzolaWalach2019] and [CarrelVandereycken2023, §2.3] for stiff
problems. None of the statements cites a theorem of a paper.

### 7.7 The implicit BUG integrator for stiff Sylvester-type fields

The files of this section study the global error of the BUG integrator with backward Euler
substeps (`IsMatrixImplicitBUGStep`, section 7.1) for the linear stiff field
`F(Z) = M Z - Z CᵀC`: `M` is dissipative and bounded by `μ`, and `C` is arbitrary, so that the
matrix `N = -CᵀC` acting on the rows is symmetric negative semidefinite of any norm (the
stiffness). Two-sided stiffness is the field `-BᵀB Z - Z CᵀC` or `N Z + Z N`. The question is
whether the error of a run is bounded with constants that do not depend on `‖C‖`. The answer in
the files depends on the class: it is no for one step in general, yes for runs when the reference
is smooth in the rows, no for stiffness on both sides, and the section ends with a table. Norms
are Frobenius norms. The constants are those of the proofs.

**Where the stiff part enters one step.** Every substep is an implicit Galerkin step
`x₁ = P (x₀ + h F(t, x₁))` with an orthogonal projector `P` (`Q₀` in the K-step, `P₀` in the
L-step, `P₁ Q₁` in the S-step). For `F = S + G` with `S` additive and `G` Lipschitz with the
constant `L`, the file @file(LeanDLRA/Stiff/ImplicitGalerkinTangential.lean) compares the step
with an arbitrary pair of reference states `u₀`, `u₁`:

@stmt LeanDLRA/Stiff/ImplicitGalerkinTangential.lean implicitGalerkin_compare_of_add implicitGalerkin_compare_of_add

The stiff part enters through the one-sided Lipschitz constant `ℓ` of `F`, through the backward
Euler defect of the reference, and through `P S (1 - P) u₁`: the block of `S` that maps the
complement of the Galerkin space into it, applied to the part of the reference that the Galerkin
space does not contain. The block vanishes if `S` commutes with `P`
(`apply_apply_sub_apply_eq_zero_of_comm`). For `S(Z) = M Z + Z N` the K-step sees
`u₁ (1 - Q₀) N Q₀` and the L-step `P₀ M (1 - P₀) u₁`, with the projectors of the numerical
solution (`IsMatrixImplicitBUGStep.norm_kstep_sub_le_of_sylvester_add`).

**One step: no bound uniform in the stiffness.** The K-step uses the compression `V₀ᵀ N V₀` of
the stiff matrix to the row space of the numerical solution. If this row space carries a small
rough component of angle `θ`, the compression is of size `‖N‖ θ²` and the K-step has the
effective step size `h/(1 + h ‖N‖ θ²)`. The file @file(LeanDLRA/Research/ImplicitBUGStiffRows.lean)
has a family of `2 × 2` matrices of rank `1`: `M = diag(0, -1)`, `N = diag(0, -lam)`,
`X(t) = (3/5, 4/5 e^{-t})ᵀ (1, 0)`, `Y₀ = (3/5, 4/5)ᵀ (c, s)`, `c² + s² = 1`, `h lam s² = 1`.
`X` is an exact solution of rank `1` with singular value at least `3 / 5`, the field is linear and
dissipative, `‖Y₀ - X(0)‖² ≤ 2 s² = 2/(h lam)`, and every step from `Y₀` loses `2h / 25`:

@stmt LeanDLRA/Research/ImplicitBUGStiffRows.lean two_mul_div_le_norm_sub StiffRowsExample.two_mul_div_le_norm_sub

@stmt LeanDLRA/Research/ImplicitBUGStiffRows.lean not_exists_forall_norm_sub_le StiffRowsExample.not_exists_forall_norm_sub_le

So no bound `‖Y₁ - X(t₁)‖ ≤ C₁ ‖Y₀ - X(t₀)‖ + C₂ h²` holds with constants independent of `lam`,
although the flow on the matrices of rank `1` is non-expansive.

**Runs on the same family are uniform.** The loss of a step is of size `h a/(1 + a)` with
`a = h lam sₙ²`, the stiff energy of the numerical row basis. The L-step is a full resolvent step
for the rough component of the row basis: with `tₙ = sₙ/cₙ`, `tₙ₊₁² + h lam tₙ₊₁² ≤ tₙ²`, so
the squared tangent of the row angle decreases and its decrease pays the stiff energy of all later
row bases, `∑_{k ≥ 1} h lam tₖ² ≤ t₀²`. Only the initial step can lose `≈ h`. The file
@file(LeanDLRA/Research/ImplicitBUGStiffRowsRun.lean):

@stmt LeanDLRA/Research/ImplicitBUGStiffRowsRun.lean norm_run_sub_le StiffRowsExample.norm_run_sub_le

**Runs with the reference rows in the kernel of the stiffness.** Let `Q` be an orthogonal
projector with `C Q = 0`. In @file(LeanDLRA/Research/ImplicitBUGWeightedRows.lean) the functional
`‖Y (1 - Q)‖²`, the angles between the numerical row space and the range of `Q` weighted by the
singular values of `Y`, satisfies `‖Y₁ (1 - Q)‖² + 2 h ‖U₀ L₁ᵀ Cᵀ‖² ≤ (1 + 5 h μ) ‖Y₀ (1 - Q)‖²`
for one step: its decrease pays the stiff energy of all later steps, and the loss of a step is
`h μ` times the square root of a stiff energy. For every rank and every `C`, for backward Euler
steps `X_{j+1} - h M X_{j+1} = X_j` of a reference with rows in the range of `Q`:

@stmt LeanDLRA/Research/ImplicitBUGWeightedRows.lean norm_implicitBUG_run_sub_le_of_sylvester norm_implicitBUG_run_sub_le_of_sylvester

**Runs against a reference with smooth rows.** The file
@file(LeanDLRA/Research/ImplicitBUGSmoothRows.lean) compares the integrator (exact capture, no
truncation) with a sequence `X_{j+1} - h M X_{j+1} + h X_{j+1} CᵀC = X_j + δ_j`, `‖δ_j‖ ≤ d`,
`‖X_j CᵀC‖ ≤ κ`, `‖X_{j+1} - X_j‖ ≤ h ω`, which need not lie in the kernel of `N`. For
`h μ ≤ 1/8`:

@stmt LeanDLRA/Research/ImplicitBUGSmoothRows.lean norm_implicitBUG_run_sub_le_of_sylvester_of_norm_mul_gram_le norm_implicitBUG_run_sub_le_of_sylvester_of_norm_mul_gram_le

Neither `C` nor the singular values of the numerical solution enter, and the rank is arbitrary.
Every loss of a step carries the factor `h μ` and is bounded by the current error with its stiff
energy, by `h ‖X CᵀC‖` and by `‖X₁ - X₀‖`. The file
@file(LeanDLRA/Research/ImplicitBUGStiffLemmas.lean) has the step lemmas in terms of the
projectors, for bases of any size with exact capture.

**Runs with truncation, and against an exact solution.** In
@file(LeanDLRA/Research/ImplicitBUGStiffTruncation.lean) the rank may change from step to step:
step `j` starts from `Y_j` of any rank, uses bases of any size with exact capture, and is
followed by a truncation by an orthogonal projector `T_j` acting from the left (the truncated
singular value decomposition is of this form) with `‖Y_{j+1} - Ŷ_{j+1}‖ ≤ ϑ_j`:

@stmt LeanDLRA/Research/ImplicitBUGStiffTruncation.lean norm_implicitBUG_truncated_run_sub_le_of_sylvester norm_implicitBUG_truncated_run_sub_le_of_sylvester

For an exact solution `A` of the differential equation whose velocity is `K₂`-Lipschitz in time
the same bound holds for `‖Y_N - A(N h)‖` with `d = K₂ h²`
(`norm_implicitBUG_truncated_run_sub_solution_le_of_sylvester`).

**Comparison with backward Euler of the full problem; the factor one.** Backward Euler of the
full problem does not increase the Frobenius norm. In
@file(LeanDLRA/Research/ImplicitBUGStiffLocal.lean) one step of the integrator is compared with
the backward Euler step `Ỹ` of the full problem from the same start value, `Ỹ - h M Ỹ + h Ỹ CᵀC
= Y₀`. The local error depends on the start value only, and it is bounded by `h μ` times the
stiff energy of the start value minus a free comparison matrix `Z`; no term of the size of the
error enters, and there is no restriction on `h μ`:

@stmt LeanDLRA/Research/ImplicitBUGStiffLocal.lean IsMatrixImplicitBUGStep.sqrt_sq_norm_galerkin_sub_backwardEuler_add_le_of_sylvester IsMatrixImplicitBUGStep.sqrt_sq_norm_galerkin_sub_backwardEuler_add_le_of_sylvester

The error of any sequence against a backward Euler reference is then the start error plus the
defects plus the sum of the local errors, and the start error enters with the factor one
(@file(LeanDLRA/Research/ImplicitBUGStiffSharpRun.lean)):

@stmt LeanDLRA/Research/ImplicitBUGStiffSharpRun.lean norm_sub_le_add_sum_of_backwardEuler ImplicitBUGStiffSharpRun.norm_sub_le_add_sum_of_backwardEuler

With the energy identity of backward Euler the sum of the local errors gives a closed bound whose
growth factor is `(1 + c² (h μ)² / 16)^N`, `c = 27/4 + 2 h μ`, instead of an exponential in `μ t`,
for runs with truncation by projectors acting from the left:

@stmt LeanDLRA/Research/ImplicitBUGStiffSharpRun.lean norm_implicitBUG_truncated_run_sub_le_of_sylvester_of_sq norm_implicitBUG_truncated_run_sub_le_of_sylvester_of_sq

The same comparison for a semilinear field `F(Z) = G(Z) - Z CᵀC` is in
@file(LeanDLRA/Research/ImplicitBUGStiffSemilinear.lean): two backward Euler steps of the full
problem satisfy `(1 - h ℓ) ‖W - W'‖ ≤ ‖R - R'‖` if `G` is one-sided Lipschitz with the constant
`ℓ` at the pair, the sum of the local errors is propagated with `q = (1 - h ℓ)⁻¹`, and the local
error in the energy norm is bounded by the normal part of the K-step and the defect of a
comparison matrix, with no constant that depends on `C` or on the singular values
(`ImplicitBUGStiffSemilinear.norm_implicitBUG_run_sub_le_of_semilinear` is the run bound).

**Stiffness on both sides: one step can lose a fixed part of the solution.** For the field
`N Z + Z N`, with the same stiff matrix on both sides, the stiff energy of the numerical column
basis reduces the effective step size of the L-step, so that a rough component of the row basis
is not damped by the full resolvent; the S-step then damps the whole component of the solution
along this row vector. The file @file(LeanDLRA/Research/ImplicitBUGStiffTwoSided.lean) has the
family `N = diag(0, -lam)`, `X(t) = diag(1, 0)` (stationary), `Y₀ = (c, s)ᵀ (c, s)`,
`c² + s² = 1`, `h lam s⁶ = 1`, with `‖Y₀ - X‖² = 2 s² = 2 (h lam)^{-1/3}`:

@stmt LeanDLRA/Research/ImplicitBUGStiffTwoSided.lean one_div_le_norm_sub StiffTwoSidedExample.one_div_le_norm_sub

@stmt LeanDLRA/Research/ImplicitBUGStiffTwoSided.lean not_exists_forall_norm_sub_le StiffTwoSidedExample.not_exists_forall_norm_sub_le

Every step from `Y₀` has `‖Y₁ - X‖ ≥ 1/11` for every step size `h > 0`; the loss does not vanish
with the step size, and no bound `C₁ ‖Y₀ - X‖ + C₂ h` holds. With stiffness on one side only and
the rows of the reference in the kernel, the loss of a step is at most `2 h μ ‖Y₀‖`
(`IsMatrixImplicitBUGStep.norm_mul_sub_le_of_sylvester`).

**Augmenting the bases does not prevent the loss.** The file
@file(LeanDLRA/Research/ImplicitBUGStiffAugmented.lean) has a family of `3 × 2` matrices of rank
`1` with `M = diag(0, -μ, -3μ)` and `N = diag(0, -lam)`, `X(t) = e₁ e₁ᵀ` stationary, in which the
span of the old column basis and of the K-step result contains no vector that is close to the
smooth direction and has a small stiff energy. For every step whose column basis lies in that span
(the augmented basis, and the basis of the fixed-rank integrator), every row basis after the step
and every truncation by an orthogonal projector from the right, the result is at distance `≥ 1/3`
from `X`, for every step size:

@stmt LeanDLRA/Research/ImplicitBUGStiffAugmented.lean one_div_three_le_norm_sub StiffAugmentedExample.one_div_three_le_norm_sub

The start error `‖Y₀ - X‖² = 2 (1 - c c')` tends to zero while the hypotheses are kept by
`lam → ∞`.

**The S-step is an energy projection.** For `F(Z) = -BᵀB Z - Z CᵀC` the backward Euler step
`A + h (BᵀB A + A CᵀC) = Y₀` of the full matrix is the minimizer of a quadratic functional
with the energy `E(Z) = ‖Z‖² + h ‖B Z‖² + h ‖Z Cᵀ‖²`. The S-step is the Galerkin equation of the
same problem on the space `{U₁ G V₁ᵀ}` of the bases after the step. Hence, whatever the bases
are, in the file @file(LeanDLRA/Research/ImplicitBUGEnergyProjection.lean):

@stmt LeanDLRA/Research/ImplicitBUGEnergyProjection.lean IsMatrixImplicitBUGStep.energy_sub_le_of_sylvester IsMatrixImplicitBUGStep.energy_sub_le_of_sylvester

So `U₁ S₁ V₁ᵀ` is the best approximation of the full backward Euler step in this space in the
energy norm; the stiffness enters the error of the step only through the energy distance of `A`
to the space of the bases, and no bound of `B` or `C` is used. The nearest published statement of
this form is the energy-best approximation in the norm of `I + h B` of the projected step in the
preprint version of [KieriVandereycken2019].

**Rational Krylov bases: the error is an ADI residual.** The equation for `A` is a Sylvester
equation with the right-hand side `U₀ S₀ V₀ᵀ` of rank `r`. If the bases after the step contain
the shifted resolvents of the old bases (a rational Krylov space), the factored alternating
direction implicit (ADI) iteration with `k` pairs of shifts lies in the space, and the energy
error of the step against the full backward Euler step is at most the squared norm of the ADI
residual `Ûₖ S₀ V̂ₖᵀ`, `Ûₖ = ∏ⱼ (h BᵀB + 1 - tⱼ) (h BᵀB + sⱼ)⁻¹ U₀` and likewise `V̂ₖ`
(@file(LeanDLRA/Research/ImplicitBUGRationalKrylov.lean); ADI: Beckermann and Townsend,
arXiv 1609.09494, Theorem 2.1 and Corollary 3.2):

@stmt LeanDLRA/Research/ImplicitBUGRationalKrylov.lean IsMatrixImplicitBUGStep.energy_sub_le_sq_norm_adi_of_sylvester IsMatrixImplicitBUGStep.energy_sub_le_sq_norm_adi_of_sylvester

In the `3 × 2` family of the previous paragraph, where every step with the column basis in the
span of `U₀` and `K₁` loses `1 / 3`, the step with the resolvent bases is within
`‖Y₀ - X‖ + 2 abs (s t)` of the solution for all `h`, `μ`, `lam ≥ 0`
(`RationalKrylovExample.exists_isMatrixImplicitBUGStep_norm_sub_le`). The run with truncation
tolerances stays within `∑ (δⱼ + ϑⱼ)` of backward Euler on the full matrix
(`norm_implicitBUG_run_sub_le_of_sylvester_residual`), where `δⱼ` bounds a residual of step `j`.

**Damped a posteriori bounds.** Let `𝒫 Z = Z - h M Z + h Z CᵀC` be the operator of a backward
Euler step and `R = 𝒫⁻¹`. For any sequence `Y_j` with residuals `ρ_j = Y_j - 𝒫 Y_{j+1}` and a
backward Euler reference `𝒫 X_{j+1} = X_j + δ_j` the error is
`R^N (Y₀ - X₀) - ∑ R^{N-j} (ρ_j + δ_j)`, so each local residual is damped by the steps that follow
it. In @file(LeanDLRA/Research/ImplicitBUGStiffDamped.lean) the exact representation holds for any
sequence, with no hypothesis on the integrator, the truncation or the tolerance, and the powers of
`R` are bounded by the powers of the two one-sided resolvents `(1 - h M)⁻¹` and `(1 + h CᵀC)⁻¹`,
applied to factors of a low-rank matrix one side at a time:

@stmt LeanDLRA/Research/ImplicitBUGStiffDamped.lean sub_eq_sub_sum_of_backwardEuler ImplicitBUGStiffDamped.sub_eq_sub_sum_of_backwardEuler

@stmt LeanDLRA/Research/ImplicitBUGStiffDamped.lean norm_sub_le_min_add_sum_min_of_backwardEuler ImplicitBUGStiffDamped.norm_sub_le_min_add_sum_min_of_backwardEuler

In the second theorem the sum is over any splitting `ρ_j + δ_j = ∑_a P_{j,a}`, and each part takes
the better of the two resolvent powers. For `F(Z) = -BᵀB Z - Z CᵀC` the file
@file(LeanDLRA/Research/ImplicitBUGTwoSidedDamped.lean) splits the residuals with partitions of
unity, one acting on each side, before the choice of the side is made part by part:

@stmt LeanDLRA/Research/ImplicitBUGTwoSidedDamped.lean norm_sub_le_min_add_sum_min_of_sylvester ImplicitBUGTwoSidedDamped.norm_sub_le_min_add_sum_min_of_sylvester

The resolvent `(1 + h BᵀB)⁻¹` and its complement `h BᵀB (1 + h BᵀB)⁻¹` form such a partition
(`norm_sub_le_sum_min_add_sum_min_of_sylvester_resolvent`).

**Error inside and outside the column space.** With `A_j` a reference with
`𝒫 A_{j+1} = A_j + g_j + δ_j` and orthogonal projectors `T_j` acting from the left with
`T_j Y_j = Y_j`, the error splits orthogonally,
`‖Y_j - A_j‖² = ‖Y_j - T_j A_j‖² + ‖A_j - T_j A_j‖²`, into the distance to the best approximation
of the reference with columns in the range of `T_j` and the part of the reference outside it.
In @file(LeanDLRA/Research/ImplicitBUGStiffColumnSpace.lean), with `W_j` the backward Euler step
of the full problem from `Y_j` and `γ_j ≥ ‖T_{j+1} (1 - T_j)‖₂` the rotation of the range:

@stmt LeanDLRA/Research/ImplicitBUGStiffColumnSpace.lean norm_sub_proj_mul_le_add_sum_of_backwardEuler ImplicitBUGStiffColumnSpace.norm_sub_proj_mul_le_add_sum_of_backwardEuler

For a run with truncation `Y_{j+1} = T_{j+1} Ŷ_{j+1}` the last term is at most the local error
`‖Ŷ_{j+1} - W_j‖` before the truncation: the truncated parts do not enter. What enters instead is
the part of the reference outside the range, weighted by `h μ` and the rotation; neither `C` nor a
singular value enters (`norm_implicitBUG_truncated_run_sub_le_sqrt_of_sylvester`).

**Angles to the best-approximation column space.** The file
@file(LeanDLRA/Research/ImplicitBUGStiffColumnAngle.lean) compares the part `‖A_j - T_j A_j‖` and
the rotation with the same quantities for the projectors `P_j` onto the dominant left singular
vectors of `A_j`: with `s_j` the sine of the largest angle between the two ranges,
`‖A_j - T_j A_j‖ ≤ ‖A_j - P_j A_j‖ + s_j ‖P_j A_j‖` and
`‖T_{j+1} (1 - T_j)‖₂ ≤ ‖P_{j+1} (1 - P_j)‖₂ + s_{j+1} + s_j`.

@stmt LeanDLRA/Research/ImplicitBUGStiffColumnAngle.lean norm_sub_proj_mul_le_add_sum_of_backwardEuler_of_specNorm_le ImplicitBUGStiffColumnAngle.norm_sub_proj_mul_le_add_sum_of_backwardEuler_of_specNorm_le

The angles cannot be removed. The last section of the file gives a stationary reference and a
stationary sequence that is reproduced exactly by a backward Euler step followed by the
truncation to the dominant left singular vector, with `M = 0`, no defect and no local error, and
whose distance from the reference is at least `δ/(δ² + w)` times the error of a rank-one
approximation, where `w` is the quotient of the weights `h λ/(1 + h λ)` of the slowest and of the
fastest row mode:

@stmt LeanDLRA/Research/ImplicitBUGStiffColumnAngle.lean mul_norm_reference_sub_rankOne_lt_norm_sub ImplicitBUGStiffColumnAngleExample.mul_norm_reference_sub_rankOne_lt_norm_sub

So the run bound of `ImplicitBUGStiffColumnSpace` does not hold with `‖A_j - T_j A_j‖` replaced by
a multiple of the error of the best approximation with a constant that depends neither on the
stiff operator nor on the step size.

**Weighted norms on the rows.** Let `S` commute with `CᵀC`. A backward Euler step commutes with
the multiplication by `S` from the right, and so does a projector acting from the left; hence
every bound of the previous two paragraphs holds verbatim in the weighted norm `‖Z S‖`
(@file(LeanDLRA/Research/ImplicitBUGStiffWeighted.lean)). For `M = 0` the truncation itself has a
weight: with `R Rᵀ = (1 + h CᵀC)⁻¹` and `S Sᵀ = 1 - R Rᵀ = h CᵀC (1 + h CᵀC)⁻¹` the backward Euler
step `W` from `Y` satisfies `W - A₁ = E R Rᵀ` for `E = Y - A`, and

@stmt LeanDLRA/Research/ImplicitBUGStiffWeighted.lean sq_norm_sub_mul_eq ImplicitBUGStiffWeighted.sq_norm_sub_mul_eq

so a step `Y₁` that is at most as far from `W` as a competitor `Z` (for the truncation to rank
`r`: every matrix of rank `r`, in particular the old value) satisfies
`‖(Y₁ - A₁) S‖² + ‖(Y₁ - A₁ - E) R‖² ≤ ‖(Z - A₁) S‖² + ‖(Z - A₁ - E) R‖²`. For a stationary
reference the error in the norm `‖Z S‖` does not increase, whatever `C` and `h` are:

@stmt LeanDLRA/Research/ImplicitBUGStiffWeighted.lean norm_sub_mul_le_of_norm_sub_le_of_stationary ImplicitBUGStiffWeighted.norm_sub_mul_le_of_norm_sub_le_of_stationary

For a moving reference it grows at most by the weighted increments of the reference that the
competitor does not follow (`norm_sub_mul_le_add_sum_of_norm_sub_le`). The examples of the file
are a stationary relaxation with two row modes whose stationary truncated sequence is far from
the best approximation in the Frobenius norm and is the best approximation in the weighted norm,
and one whose stationary sequence is the best approximation in the Frobenius norm and not in the
weighted norm.

**The results side by side.** `e₀ = ‖Y₀ - X₀‖`; "one-sided" means stiffness on the rows only
(`-CᵀC`), "two-sided" on rows and columns; `κ`, `ω`, `d` are the bounds of the smooth reference
above; `ϑ_j` are the truncation tolerances.

| Setting | What is proved | Constants | File |
|---|---|---|---|
| one-sided, `M = diag(0, -1)`, `N = diag(0, -lam)`, one step, `2 × 2`, rank `1` | counterexample: no `C₁ e₀ + C₂ h²` uniform in `lam` | loss `2h / 25`, `h lam s² = 1` | @file(LeanDLRA/Research/ImplicitBUGStiffRows.lean) |
| one-sided, the same family, runs | bound uniform in `lam` | `4 e₀ + 18 (1 + n h) h`, `h ≤ 1`, `c ≥ 1/2` | @file(LeanDLRA/Research/ImplicitBUGStiffRowsRun.lean) |
| one-sided, kernel class `C Q = 0`, rows of the reference in the range of `Q`, any rank | run bound | `e₀' + 2 h μ ‖Y₀‖ + (1 + 4 h μ √N) √((1 + 5 h μ)^N) ‖Y₀ (1 - Q)‖`, `h μ ≤ 1` | @file(LeanDLRA/Research/ImplicitBUGWeightedRows.lean) |
| one-sided, smooth rows (`‖X CᵀC‖ ≤ κ`, `‖X₁ - X₀‖ ≤ h ω`, defect `d`) | run bound | `(1 + 9 h μ)^N (e₀ + 2 h μ ‖Y₀‖ + N (2 d + 2 h μ h (7 κ + 3 ω)))`, `h μ ≤ 1/8` | @file(LeanDLRA/Research/ImplicitBUGSmoothRows.lean) |
| one-sided, smooth rows, truncation, exact solution | run bound | the same plus `2 ∑ ϑ_j`; `d = K₂ h²` for an exact solution | @file(LeanDLRA/Research/ImplicitBUGStiffTruncation.lean) |
| one-sided, one step against backward Euler of the full problem | local error bound | `(27/4 + 2 h μ) h μ λ`, no restriction on `h μ` | @file(LeanDLRA/Research/ImplicitBUGStiffLocal.lean) |
| one-sided, runs, sharp factor | factor one on `e₀`; closed form | `e₀ + ∑ (‖δ_j‖ + ϑ_j + c h μ λ_j)`; growth `(1 + c² (h μ)²/16)^N` | @file(LeanDLRA/Research/ImplicitBUGStiffSharpRun.lean) |
| one-sided, semilinear `G(Z) - Z CᵀC` | run bound with `ℓ` | factors `(1 - h ℓ)⁻¹` | @file(LeanDLRA/Research/ImplicitBUGStiffSemilinear.lean) |
| two-sided `N Z + Z N`, one step, `2 × 2`, rank `1` | counterexample: no `C₁ e₀ + C₂ h` uniform in `lam` | loss `1 / 11` for every `h > 0`, `h lam s⁶ = 1` | @file(LeanDLRA/Research/ImplicitBUGStiffTwoSided.lean) |
| two-sided, bases augmented, `3 × 2`, rank `1` | counterexample: augmentation does not remove the loss | loss `1 / 3` for every `h` | @file(LeanDLRA/Research/ImplicitBUGStiffAugmented.lean) |
| two-sided, `-BᵀB Z - Z CᵀC`, one step | S-step is the energy projection of the full step | equality of energies | @file(LeanDLRA/Research/ImplicitBUGEnergyProjection.lean) |
| two-sided, rational Krylov bases | energy error at most the squared ADI residual | example: `‖Y₀ - X‖ + 2 abs (s t)` | @file(LeanDLRA/Research/ImplicitBUGRationalKrylov.lean) |
| one- and two-sided, any sequence | exact damped representation; damped a posteriori bounds | minimum of two resolvent powers, part by part | @file(LeanDLRA/Research/ImplicitBUGStiffDamped.lean), @file(LeanDLRA/Research/ImplicitBUGTwoSidedDamped.lean) |
| one-sided, truncation by left projectors | error inside and outside the column space; run bound | `(h μ + γ_j) ‖A_j - T_j A_j‖` per step | @file(LeanDLRA/Research/ImplicitBUGStiffColumnSpace.lean) |
| the same, against the best approximation | comparison through angles; counterexample without angles | `‖A - T A‖ ≤ ‖A - P A‖ + s ‖P A‖` | @file(LeanDLRA/Research/ImplicitBUGStiffColumnAngle.lean) |
| the same, weighted norm `‖Z S‖` | stationary reference: error not increasing; Frobenius counterexample | factor one | @file(LeanDLRA/Research/ImplicitBUGStiffWeighted.lean) |
| two-sided `-BᵀB Z - Z CᵀC`, runs with truncation by orthogonal projectors | summable stiff energies: `‖Y_N‖²/2 + ∑ h (‖B Y_{j+1}‖² + ‖Y_{j+1} Cᵀ‖²) ≤ ‖Y₀‖²/2`; run bound with residuals `a ‖Y_j‖ + b (energy)^{1/2}` | `N a ‖Y₀‖ + b (E₀^{1/2} + (N/2)^{1/2} ‖Y₀‖)`, `E₀` the stiff energy of `Y₀` | @file(LeanDLRA/Research/ImplicitBUGRunEnergy.lean), [section 3.9](#39-optimality-of-low-rank-time-integration) |
| one-sided `M Z - Z CᵀC`, implicit midpoint Galerkin steps, any sequence | run bounds with factor one; Galerkin step quasi-optimal in the energy norm | `1 + τ μ`; local terms computable | @file(LeanDLRA/Research/ImplicitMidpointBUGStiff.lean), [section 7.8](#78-implicit-midpoint-galerkin-steps-for-a-stiff-row-operator) |
| a field `S + G`, any step | comparison of a Galerkin substep with a reference | `(1 - h ℓ)`, defect, block `P S (1 - P) u₁` | @file(LeanDLRA/Stiff/ImplicitGalerkinTangential.lean) |

What is not shown. The one-step counterexamples are for `2 × 2` and `3 × 2` matrices of rank `1`.
The run bounds hold in the classes of the table: the core does not show a stiffness-uniform bound
for a run of the integrator for stiffness on both sides, or for one-sided stiffness with a
reference whose rows are neither in the kernel nor smooth. The weighted functional of the kernel
class and the weighted norm of the last rows are tools for the stationary reference, not a bound
for a moving one. The a posteriori bounds are for any sequence and are not bounds for the
integrator before the residuals are bounded. The constants (`4`, `18`, `5`, `27 / 4`, `9`) are
those of the proofs.

Runs with truncation for `-BᵀB Z - Z CᵀC` with summable stiff energies are in [section
3.9](#39-optimality-of-low-rank-time-integration); the implicit midpoint rule is in section 7.8.

Literature. The run device of the sharp-factor rows (compare each step with the backward Euler
step of the full problem from the same start value, propagate by the contractive full scheme) is
that of the analysis of parametrized implicit integrators in [LubichNick2025], Theorem 5.1 (arXiv
2501.12118), and of Feischl, Lasser, Lubich and Nick, arXiv 2403.19234, §9.5.3; their local terms
are defect sizes that are available a posteriori. For the BUG step the files bound the local term
a priori, uniformly in the stiff operator and the singular values and without a step-size
restriction; the nearest published local bound for a compressed implicit Euler step depends on the
spectral radius of the stiff matrix (Kieri and Vandereycken, preprint 2017, Theorem 9, which is
not in [KieriVandereycken2019]). Run bounds uniform in the stiffness are published for other
integrators: Ostermann, Piazzola and Walach, arXiv 1803.10473, Theorem 1; Scalone and Guglielmi,
arXiv 2602.07437, Theorem 1; Hu and Yu, arXiv 2610.41606, Theorems 5.2 and 6.2. For BUG
integrators, Hauck, Kusch and Schotthöfer (arXiv 2608.27749, §8.2) and the review of Einkemmer et
al., arXiv 2412.05912, §8, say that no rigorous error bound is available. That the
projector-splitting and BUG integrators are not robust to stiffness in general is observed
numerically, with accurate substeps, in [CarrelVandereycken2023], §2.3 and Figure 1; the
counterexamples above are proved and show the mechanism (the compression `V₀ᵀ N V₀`). For
stiffness on both sides the loss is a damping, consistent with published unconditional norm
stability of a low-rank integrator (Saha, Yang and Yin, arXiv 2610.18419, Theorem 3.6). Published
a posteriori bounds for time-dependent problems damp propagated residuals by scalars (Zhang, Chen,
Vanden-Eijnden and Peherstorfer, arXiv 2404.01145, Proposition 6; Lakkis, Makridakis and Pryer,
arXiv 0709.0916) or by the norms of both propagators (Kirsten and Simoncini, arXiv 1905.12119,
Proposition 5.3), or drop the damping (Koskela and Mena, arXiv 1705.07507); for Sylvester-type
backward Euler the files bound each propagated residual by the better one-sided resolvent power
applied to it. The module docstrings cite [CerutiLubich2022] and [CerutiKuschLubich2022] for the
integrator.

### 7.8 Implicit midpoint Galerkin steps for a stiff row operator

For `F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ` and `C` arbitrary, the file
@file(LeanDLRA/Research/ImplicitMidpointBUGStiff.lean) studies runs of a BUG-type step whose
substeps are resolvent solves. The implicit midpoint step of size `2 τ` from `Y` is `2 W - Y`,
where `W` is the backward Euler step of size `τ` from `Y` (the value at the midpoint). The
reflection `Y ↦ 2 W - Y` does not increase the Frobenius norm
(`ImplicitMidpointBUGStiff.sq_norm_two_smul_sub_add_le_of_backwardEuler`: `‖2 W - R‖² + 4 τ ‖W Cᵀ‖²
≤ ‖R‖²`). So the error of any sequence against a reference that satisfies the implicit midpoint
rule up to defects `d_j` is the start error plus the defects plus the sum of the local errors,
with the factor one on the start error and no restriction on the step size:

@stmt LeanDLRA/Research/ImplicitMidpointBUGStiff.lean norm_sub_le_add_sum_of_implicitMidpoint ImplicitMidpointBUGStiff.norm_sub_le_add_sum_of_implicitMidpoint

A low-rank step that computes the midpoint value `Ym` by a Galerkin backward Euler step in a space
of matrices `P Z Q` has twice the error of this Galerkin step as its local error
(`‖Y (j+1) - (2 Ym j - Y j)‖ ≤ ϑ j`), and the Galerkin step is quasi-optimal in the energy norm
`(‖Z‖² + τ ‖Z Cᵀ‖²)^{1/2}`:

@stmt LeanDLRA/Research/ImplicitMidpointBUGStiff.lean sqrt_sq_norm_galerkin_sub_add_le ImplicitMidpointBUGStiff.sqrt_sq_norm_galerkin_sub_add_le

Here `Yg` is the Galerkin step, `W` the backward Euler step, and `Z` any matrix in the Galerkin
space. The constant is `1 + τ μ`, and no singular value and no norm of `C` enters. The run bound
with a Galerkin space `P j`, `Q j` that contains a matrix `Z j`:

@stmt LeanDLRA/Research/ImplicitMidpointBUGStiff.lean norm_galerkinMidpoint_run_sub_le ImplicitMidpointBUGStiff.norm_galerkinMidpoint_run_sub_le

For bases built from two levels of K- and L-steps the combination `YK + YL - Y₁` of the
level-two K- and L-steps and the level-one Galerkin step lies in the Galerkin space, and its
residual in the equation of the full problem is a sum of two terms that are computable along the
run:

@stmt LeanDLRA/Research/ImplicitMidpointBUGStiff.lean sqrt_sq_norm_backwardEuler_sub_combination_add_le ImplicitMidpointBUGStiff.sqrt_sq_norm_backwardEuler_sub_combination_add_le

@stmt LeanDLRA/Research/ImplicitMidpointBUGStiff.lean norm_twoLevelMidpoint_run_sub_le ImplicitMidpointBUGStiff.norm_twoLevelMidpoint_run_sub_le

No constant depends on `C` or on a singular value. What is not shown: a second order in the step
size is not proved; the local terms of the run bounds are computable, and an a priori bound of
them of the order `τ³` is open. The bounds are for the field `M Z - Z CᵀC`, not for stiffness on
both sides, and the bases are hypotheses of the statements. Literature. Second-order error bounds
that are robust to stiffness (not depending on the Lipschitz constant of the stiff part) are
published for low-rank Strang splitting ([ScaloneGuglielmi2026], Theorem 1), for projected
exponential Runge methods ([CarrelVandereycken2023], Theorem 11, with a term for the rank-`r`
approximation error) and for parametric Gauss and Radau IIA methods, the implicit midpoint rule
included ([LubichNick2025], Theorem 7.1, against the non-parametric Runge–Kutta values with a
posteriori defects). For a BUG integrator with an implicit midpoint Galerkin step and resolvent
solves only, the files give a run bound with the factor one whose local terms are computable and
uniform in the stiff operator and in the singular values. The run device (compare with the full
scheme from the same value) is that of [LubichNick2025], as in section 7.7. The module docstring
cites [CerutiEtAl2024b] for the midpoint BUG integrator with augmented bases and
[CerutiLubich2022] for the K-, L- and Galerkin steps.

### 7.9 A certified companion encloses the error of a run

Let `A` be a reference, `Y` a run whose error is wanted, and `Y'` a companion (a run of higher rank
or with smaller steps) with a certified bound `‖Y' - A‖ ≤ β`. In
@file(LeanDLRA/Stiff/CompanionEnclosure.lean):

@stmt LeanDLRA/Stiff/CompanionEnclosure.lean abs_norm_sub_sub_norm_sub_le_of_norm_sub_le abs_norm_sub_sub_norm_sub_le_of_norm_sub_le

that is, `‖Y - Y'‖ - β ≤ ‖Y - A‖ ≤ ‖Y - Y'‖ + β`, in any seminormed group, with the distance
`‖Y - Y'‖` computed from the factors of `Y` and `Y'`. When the companion is much more accurate
than the run, the enclosure is narrow even if `β` overestimates the error of the companion by a
large factor: both sides are within `2 β` of the error of `Y`. The certificate can be any of the
a posteriori bounds of the library. For a companion sequence against the implicit Euler scheme,
with the residuals of the companion:

@stmt LeanDLRA/Stiff/CompanionEnclosure.lean abs_norm_sub_sub_norm_sub_le_of_implicitEuler abs_norm_sub_sub_norm_sub_le_of_implicitEuler

and with a stepwise defect bound of a continuous curve through the companion's iterates (one-sided
Lipschitz field) and the recursion `q (n + 1) ≥ gronwallBound (q n) ℓ (η n) h`:

@stmt LeanDLRA/Stiff/CompanionEnclosure.lean abs_norm_sub_sub_norm_sub_le_of_defect_steps abs_norm_sub_sub_norm_sub_le_of_defect_steps

For an affine field `x ↦ L x + g` the defect of the cubic Hermite interpolant of the iterates on a
step is an explicit polynomial in `θ ∈ [0, 1]`:

@stmt LeanDLRA/Stiff/CompanionEnclosure.lean hermite_defect_eq hermite_defect_eq

The truncated singular value decomposition of the companion, with the certificate
`‖Y' - T_r(Y')‖ + β`, is never worse than the enclosure for a run of rank at most `r`:

@stmt LeanDLRA/Stiff/CompanionEnclosure.lean norm_truncation_sub_le_and_le_norm_sub_add norm_truncation_sub_le_and_le_norm_sub_add

A run certified through the companion at a tolerance has therefore a compressed companion of the
same rank that is certified at that tolerance as well. What is not shown: `β` is a hypothesis;
the statements do not say how accurate a companion has to be, and the enclosure is sharp for the
less accurate of the two sequences only. Literature. The two-sided form is the hierarchical
(saturation) estimator of reduced-basis and finite-element theory, in which a saturation constant
`Θ` bounds the error of the finer solution relative to the coarser one (Hain, Ohlberger, Radic
and Urban, arXiv 1802.03298, Proposition 3.1), with that constant replaced by a certified bound
of the finer solution; the certified form is the triangle inequality, and error estimation by a
second solution (reintegration) is classical for ordinary differential equations. Companions of
higher rank are used in dynamical low-rank approximation as error indicators or for step
rejection (Hochbruck, Neher and Schrammer, BIT 2023; [CerutiKuschLubich2024]); none of the
sources read uses one in a certified two-sided enclosure.

## 8. Tensors

A tensor with mode index types `ι k` is an element of `Tensor ι`, the Euclidean space of
functions on the multi-indices. `unfold p X` is the unfolding (matricization) of `X` with
respect to the set of modes `p`: the rows are indexed by the part of the multi-index in `p`, the
columns by the rest. The core has the following results.

### 8.1 Tensor trains

@stmt LeanDLRA/Tensor/TT/Basic.lean unfold_tt Tensor.unfold_tt

@stmt LeanDLRA/Tensor/TT/Basic.lean rank_unfold_tt_le Tensor.rank_unfold_tt_le

For a tensor train `tt G` with cores `G` and bond index types `β k`, and for `k ≤ d`, the
unfolding with the first `k` modes as rows is the product of the left interface matrix
`ttLeft G k` and the transpose of the right interface matrix `ttRight G k`; its rank is at most
the number `Fintype.card (β k)` of elements of the `k`-th bond index type.

Source: arXiv 2402.18721, Eq. (16), as cited in the docstring of the first theorem.

@stmt LeanDLRA/Tensor/TT/TangentProjector.lean isOrthProj_ttTangentProj Tensor.isOrthProj_ttTangentProj

For left-orthogonal cores `A` (`hA`) and right-orthogonal cores `B` (`hB`) of a tensor train
whose boundary bond index types `β 0` and `β d` have one element, the operator
`ttTangentProj A B` is an orthogonal projector (`IsOrthProj`: idempotent and symmetric). The
docstring calls it the tangent projector of the tensor train format; the theorem does not relate
it to a tangent space.

Source: Lubich, Oseledets and Vandereycken, arXiv 1407.2042, Theorem 3.1 and Corollary 3.2, as
cited in the docstring.

**The tensor-train projector-splitting integrator.**

@stmt LeanDLRA/Tensor/TT/ProjectorSplittingExactness.lean exact Tensor.IsTTKSLStep.exact

@stmt LeanDLRA/Tensor/TT/ProjectorSplittingError.lean local_error Tensor.IsTTKSLStep.local_error

@stmt LeanDLRA/Tensor/TT/ProjectorSplittingError.lean tt_ksl_global_error Tensor.tt_ksl_global_error

`Tensor.IsTTKSLStep F U V t₀ t₁ Y₀ YK YS` is one step of the tensor-train projector-splitting
integrator: for the cores `k = 0, …, d - 1` a forward substep, and for the bonds a backward
substep, with new left-orthogonal cores `U` and old right-orthogonal cores `V`
(`LeanDLRA/Tensor/TT/ProjectorSplitting.lean`). The result of the step is `YK (d - 1) t₁`.

*Exactness.* For a field that does not depend on the state, `F(t, Y) = A'(t)`
(`IsDerivRHS F A t₀ t₁`), every substep is an explicit increment and the signed substep
projectors add up to the tangent projector of the format: one step returns
`Y₁ = Y₀ + ttTangentProj U V (A t₁ - A t₀)` (`Tensor.IsTTKSLStep.eq_add_ttTangentProj`), without
any rank condition. The first theorem: if `Y₀ = A t₀` and `A t₁` is recoverable at every inner
bond from the projection on the right modes (`hrec`, in the abstract form `Exactness.IsRecoverable`
that the matrix and tree cases use), the step is exact, `Y₁ = A t₁`.
`Tensor.IsTTKSLStep.exact_of_isUnit` derives the condition from invertible overlaps
`(W k)ᵀ ttRight V k`, where `A t₁` unfolds as `Uf k * S k * (W k)ᵀ` at bond `k`. Only the right
overlaps are used and the middle factor may be singular (module docstring). The second-order
sweep (forward and backward) is not treated. The file has an example on `ℝ² ⊗ ℝ² ⊗ ℝ²` with bond
dimension one (`TTKSLExample`) in which the hypotheses hold and the step is exact, although its
backward substeps end off the curve; with a doubly normal part added to the field
(`F = c + n`) the step misses the exact solution by `n`.

*Robust error.* If the field is `L`-Lipschitz, bounded by `B` and continuous in time, and the
normal bound `ε` holds at the forward substep values `YK k t₁` in the form
`‖(1 - ttLeftProj U (k + 1)) ((1 - ttRightProj V (k + 1)) (F t (YK k t₁)))‖ ≤ ε`, then for a step
started on the exact solution

`‖Y₁ - A t₁‖ ≤ c_d(h) h (11 L B h + ε)`, `c_d(h) = ∑_{j<d-1} (2 + 3 L h)^j`,

and for `N` steps with `h ≤ H` and `n h ≤ T` (`tt_ksl_global_error`)

`‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} c_d ε + 11 L B T e^{L T} c_d h`,
`c_d = ∑_{j<d-1} (2 + 3 L H)^j`.

The constants depend on the number `d` of cores, `L`, `B`, `T` and `H`, and on no singular value.
The constant `c_d` grows like `2^{d-1}`; it is the constant of the proof, and "robust" refers to
the independence of singular values, not to the dependence on `d`. The proof treats the sweep
from core `k` as one step of the matrix projector-splitting integrator for the field `P_{≤k} F`
whose L-step is solved inexactly by the sweep from core `k + 1`; for `d = 2` it is the matrix
bound. The step is not a step of the tree tensor network integrator on the linear tree
(section 8.3): there every inner node has an additional backward substep and a core step, so the
bound of section 8.3 does not apply to it directly.

Source: the module docstrings cite [LubichOseledetsVandereycken2015], Theorem 4.1 for the
substeps and Theorem 5.1 and Lemma 5.2 for exactness, and [KieriLubichWalach2016], §2.6.3 for the
inexact substeps.

**The tangent projector of tensor trains and quasi-optimality.** Let `X` and `Y` be tensor
trains with `d` modes and the same bond dimensions, with tangent projectors `P(X)`, `P(Y)`
(`ttTangentProj`), and let `ρ` be a lower bound of the singular values `σ_{|β k|}` of the
unfoldings of `X` and of `Y`. The file @file(LeanDLRA/Tensor/TT/TangentNormal.lean) shows, for
all tensors `Z` and without a smallness condition on `‖X - Y‖`:

@stmt LeanDLRA/Tensor/TT/TangentNormal.lean norm_ttTangentProj_sub_le Tensor.norm_ttTangentProj_sub_le

The constant `2` does not depend on the number of modes. A vector in the range of the alternating
sum of nested interface projectors is tangent at every interface, and
`∑_{k < n} ‖(Ql k - Ql (k + 1)) z‖² ≤ ‖z‖²` for nested orthogonal projectors; these are the two
facts on which the bound rests. The bounds of the difference of the projectors in
[BachmayrEisenmannUschmajew2025, Prop. 4.11] and in Budzinskiy and Zamarashkin (arXiv 2110.03975,
Lemma 3.1) have the constants `4 d` and `2 (d - 1)`. The lemmas
`Tensor.norm_sub_ttTangentProj_apply_le_add` and
`Tensor.mul_norm_sub_ttTangentProj_apply_le_two_mul` of the file are the bound for a vector
tangent at `X` and the bound for an arbitrary `Z` in terms of `‖Z - P(X) Z‖`.

The normal component of a nearby tensor train is of second order with a constant that does not
depend on the number of modes. For `Y = tt A` with left-orthogonal cores `A` and right-orthogonal
cores `B` (`tt B = tt A`) and `e = ‖X - Y‖`, in
@file(LeanDLRA/Tensor/TT/NormalSecondOrderTrain.lean):

@stmt LeanDLRA/Tensor/TT/NormalSecondOrderTrain.lean norm_sub_ttTangentProj_tt_le Tensor.norm_sub_ttTangentProj_tt_le

To leading order in `e` the constant is `1 / √2`. The normal projector is the orthogonal sum
`1 - P = ∑_{k < n} (Ql k - Ql (k + 1)) (1 - Qr (k + 1))` over the interfaces
(@file(LeanDLRA/Tensor/TT/NormalSecondOrder.lean)); the hypothesis at every interface is the
inequality `‖A M B‖ ≤ ρ⁻¹ ‖A M‖ ‖M B‖` for the `k`-th unfolding `M`, whose rank is at most the
`k`-th bond dimension. The bound of [BachmayrEisenmannUschmajew2025, Prop. 4.11] has the factor
`√(d - 1)` and the bound of Budzinskiy and Zamarashkin (arXiv 2110.03975, Lemma 3.1) the factor
`d - 1`, both for all `e`; the bound above needs `2 e < ρ` and has `ρ` at `Y` (the variant with
`ρ` at `X` is `Tensor.norm_sub_ttTangentProj_tt_le_of_le_singularValues_tt`).

For a solution `Y` of `Ẏ = P(Y) F(t, Y)` on the manifold of tensor trains of fixed bond
dimensions and a curve `X` of such tensor trains, the file
@file(LeanDLRA/Tensor/TT/QuasiOptimalityNormalVelocity.lean) has the analogue of the rate of
section 3.8 in a tube `‖Y - X‖ ≤ ε < ρ/2`, with `ρ` a lower bound of the singular values of the
unfoldings of `X` only, `ν ≥ ‖(1 - P(X)) F(t, A)‖`, `ν' ≥ ‖(1 - P(Y)) F(t, A)‖`,
`g ≥ ‖P(X) F(t, A) - Ẋ‖`, and the rate `k = L + (ν + ν') / √(2 ρ (ρ - 2 ε))`:

@stmt LeanDLRA/Tensor/TT/QuasiOptimalityNormalVelocity.lean norm_tt_sub_tt_le_integral_exp_integral Tensor.norm_tt_sub_tt_le_integral_exp_integral

The second theorem of the file, `…_of_norm_ttTangentProj_le`, has the rate
`L + (2 ν + 2 ε μ/ρ) / √(2 ρ (ρ - 2 ε))` with `μ ≥ ‖P(X) F(t, A)‖`: all data are taken at the curve
`X`. No constant depends on the number `d` of modes; to leading order in `ε` the rate is
`L + √2 ν/ρ`. Not shown: the existence of the solution `Y` on the manifold of tensor trains is a
hypothesis of the theorems, as in section 3.7, and so is the tube condition `‖Y - X‖ ≤ ε`.

### 8.2 Tucker tensors

@stmt LeanDLRA/Tensor/Tucker/Tangent.lean tuckerTangentProj_eq_starProjection Tensor.tuckerTangentProj_eq_starProjection

The theorem has one more hypothesis than the quoted text shows: `hU : ∀ k, (U k)ᵀ * U k = 1`
(every basis matrix `U k` has orthonormal columns) is a variable of the section, declared with
`variable` and included with `include hU` before the theorem. At a Tucker tensor `tucker C U` with such basis matrices,
let `PC` be an orthogonal projector on the space of cores (`hPC`), and let `W k` be matrices
whose columns are combinations of the columns of the unfolding of `tucker C U` with respect to
the modes other than `k` (`hWB`), such that `W k * (W k)ᵀ`, acting on the modes other than `k`,
fixes `tucker C U` (`hWX`). Then the operator `tuckerTangentProj U PC W` is the orthogonal
projection onto `tuckerTangentSpace U C PC`. This space is defined in the same file as the span
of the tensors `tucker Ċ U + ∑ k, tucker C (Function.update U k (U̇ k))` with `PC Ċ = Ċ` and
`(U k)ᵀ * U̇ k = 0`; the manifold itself is not formalized (module docstring of the file).

Source: Bachmayr, Eisenmann and Uschmajew, arXiv 2308.16720, Proposition 4.2, as cited in the
docstring.

@stmt LeanDLRA/Integrators/TuckerBUG.lean IsTuckerBUGStep IsTuckerBUGStep

@stmt LeanDLRA/Integrators/TuckerBUG.lean tucker_global_error_le tucker_global_error_le

The BUG integrator for Tucker tensors with `d` modes, in projector form on a general state
space: one K-step for every mode `i` with the projector `Q₀ i`, new mode projectors `P₁ i` that
commute and capture the K-step results, and a Galerkin step with the product of the new
projectors. The field `kNormal` bounds `(1 - P₁ i) (1 - Q₀ i) F` at the K-step results by `ε`.
The error theorem has the older form (global assumptions, given steps, exact solutions started
at the numerical values). Conclusion: for `n * h ≤ T`

`‖Y n - A (t₀ + n * h)‖ ≤ e^{L T} δ + T e^{L T} (tuckerC₁ d L H ε + tuckerC₂ d L B H h)`.

The constants depend on `L`, `B`, the bound `H` on the step size, `T` and the number `d` of
modes (docstring of the theorem); no singular value appears in the statement.

Source: [CerutiLubich2022] (arXiv 2010.02022), Theorem 7, as cited in the docstring. The same
bound for a field that is Lipschitz and bounded only on a tube around the solution is
`tucker_global_error_le_of_tube`
([`LeanDLRA/Integrators/TuckerBUGCore.lean`](../LeanDLRA/Integrators/TuckerBUGCore.lean)); it
also has the older form, with given steps and given exact solutions.

@stmt LeanDLRA/Tensor/Tucker/BUGStep.lean stepRel TuckerBUG.stepRel

@stmt LeanDLRA/Tensor/Tucker/BUGRun.lean isTubeLocal_stepRel TuckerBUG.isTubeLocal_stepRel

@stmt LeanDLRA/Tensor/Tucker/BUGRun.lean exists_run_norm_sub_le TuckerBUG.exists_run_norm_sub_le

The Tucker BUG step as a relation between tensors, and its runs. For every mode `i` the K-step
solves `Ẏ = Q₀ i F(t, Y)` from `Y₀`, where the projector `Q₀ i` belongs to a co-range basis with
`r i` orthonormal columns that fixes `Y₀`; the updated mode basis `U₁ i` has `r i` orthonormal
columns and its mode projector fixes the result of the K-step; the Galerkin step solves
`Ẏ = Π F(t, Y)` from `Π Y₀`, with `Π` the product of the mode projectors. Admissible values are
the tensors of multilinear rank at most `r` (`Tensor.ModeRankLE`). The method is tube-local with
margin constant `d + 2` (`TuckerBUG.isTubeLocal_stepRel`; for two modes this is 4, that of the
matrix BUG integrator). The run theorem has the hypotheses of section 5.2 on the tube and a bound
`ε` on the normal part at the normal triples of the tube (`TuckerBUG.normalTriples r`): for every
mode `i` and every tensor `Y` fixed by a mode projector `P` and a co-range projector `Q`, both of
rank `r i`, `‖(1 - P) ((1 - Q) F(t, Y))‖ ≤ ε`. Conclusion: for a start value of multilinear rank
at most `r` a run exists, all its values have multilinear rank at most `r`, and

`‖Y n - A (t₀ + n * h)‖ ≤ e^{L T} δ + T e^{L T} (tuckerC₁ d L H ε + tuckerC₂ d L B H h)`

if this bound plus `(d + 2) * B * h` is smaller than `ρ`. The constants do not depend on the
singular values of the unfoldings. `TuckerBUG.IsRun.norm_sub_le` gives the bound for every run.
In contrast to `tucker_global_error_le` and `tucker_global_error_le_of_tube`, the steps are shown
to exist and no exact solutions through the numerical values are assumed.

Source: [CerutiLubich2022] (arXiv 2010.02022), §5 and Theorem 7, as cited in the docstrings.

@stmt LeanDLRA/Tensor/TTN/Abstract/ProjectorSplittingExactness.lean tucker_ksl_exact tucker_ksl_exact

Exactness of the nested projector-splitting integrator for Tucker tensors, in projector form on
a general state space. `IsTuckerKSLStep` is one step of the integrator with given values `K i`
of the K-substeps, and `IsExactKSteps` says that these are the exact substep values (both in
[`LeanDLRA/Tensor/Steps.lean`](../LeanDLRA/Tensor/Steps.lean)). Let the field be the derivative
of a given curve `A` (`hA`, `IsDerivRHS`), and let the step start at `A t₀`. If for every mode
`i` the value `A t₁` is recoverable from `Q₀ i (A t₁)` with respect to a class `𝓛 i` of
operators that contains the new projector `P₁ i` (`h𝓛`, `hrec`; `Exactness.IsRecoverable`), the
result of the step is `A t₁`. The recoverability takes the place of the invertibility condition
of the paper (docstring of the theorem).

Source: [LubichVandereyckenWalach2018, Thm. 3].

**The tangent projector of Tucker tensors: Lipschitz constant, lower bound and sharp constant.**
Let `X = C ×ₖ Uₖ` and `Y = C' ×ₖ U'ₖ` be Tucker tensors with `d` modes and the same multilinear
rank, with tangent projectors `P(X)`, `P(Y)` (`tuckerTangentProj` with the core projector `1`,
[BachmayrEisenmannUschmajew2025, Prop. 4.2]), and let `ρ` be a lower bound of the smallest nonzero
singular values of the `d` matricizations of `X`. In
@file(LeanDLRA/Tensor/Tucker/ProjectorLipschitz.lean):

@stmt LeanDLRA/Tensor/Tucker/ProjectorLipschitz.lean norm_tuckerTangentProj_sub_le Tensor.norm_tuckerTangentProj_sub_le

The bound is `‖P(Y) B - P(X) B‖ ≤ √d ρ⁻¹ ‖Y - X‖ ‖B‖` for all tensors `B`, in Frobenius norms,
without a smallness condition on `‖Y - X‖` and with `ρ` at `X` only. It rests on a comparison of
the normal component of the tangent projector with the `d` normal components of the tangent
projectors of the matricizations (@file(LeanDLRA/Tensor/Tucker/TangentNormal.lean)):
`‖z - P z‖² ≤ ∑ᵢ ‖z - Tᵢ z‖²`. The bound of [BachmayrEisenmannUschmajew2025, Prop. 4.7] (also
global, in the operator norm, for constrained core manifolds) has the constant
`2 (√2 + 1) d` for the Tucker manifold. For matrices (`d = 2`) the constant is `1`
(`norm_tangentProjAt_sub_le_inv_mul`); the constant `√d` is not claimed to be optimal.

The constant `1` of the matrix case is not valid for three modes. The file
@file(LeanDLRA/Tensor/Tucker/ProjectorLowerBound.lean) has tensors of multilinear rank `(1, 1, 1)`
in `ℝ^{2 × 2 × 2}` with `ρ = 1`:

@stmt LeanDLRA/Tensor/Tucker/ProjectorLowerBound.lean exists_mul_le_norm_tuckerTangentProj_sub Tensor.exists_mul_le_norm_tuckerTangentProj_sub

So every constant `c` in `‖P(Y) B - P(X) B‖ ≤ c ρ⁻¹ ‖Y - X‖ ‖B‖` for three modes satisfies
`c ≥ 23/20`, while `norm_tuckerTangentProj_sub_le` has `c = √3`. The example is
`X = e₁ ⊗ e₁ ⊗ e₁`, `Y = v ⊗ v ⊗ v` with `v = (840/841, 41/841)` and the tangent vector
`B = e₂ ⊗ e₁ ⊗ e₁ + e₁ ⊗ e₂ ⊗ e₁ + e₁ ⊗ e₁ ⊗ e₂` at `X`; the quotient `|⟪B, N⟫|/(‖Y - X‖ ‖B‖ ‖N‖)`
for the normal vector `N` at `Y` tends to `2 / √3` as the angle tends to zero, the norm of the
second fundamental form of the manifold of tensors of rank one with three modes at a tensor of
norm one.

For tensors of multilinear rank `(1, …, 1)` (elementary tensors, the cone over the Segre manifold)
with `d ≥ 2` modes the constant is `√(2 (d - 1)/d)`, in
@file(LeanDLRA/Tensor/Tucker/ProjectorLipschitzRankOne.lean):

@stmt LeanDLRA/Tensor/Tucker/ProjectorLipschitzRankOne.lean norm_tuckerTangentProj_sub_le_of_unique Tensor.norm_tuckerTangentProj_sub_le_of_unique

Here `‖X‖` is the nonzero singular value of every matricization of `X`, and the constant
`√(2 (d - 1)/d) < √2` replaces `√d`; for `d = 2` it is `1`. The value is the maximal curvature of
the geodesics of the Segre manifold in the unit sphere (Breiding and Eggleston, arXiv 2307.04224,
Theorem 1.2). The proof has three parts: the distance `(1 - ∏ₖ cₖ²) ‖X‖² ≤ ‖Y - X‖²` with the
cosines `cₖ` of the angles of the factors; the inequality `‖Z - P(Y) Z‖² ≤ 2 (d - 1)/d
(1 - ∏ₖ cₖ²) ‖Z‖²` for `Z` tangent at `X`; and the bound of the difference of two orthogonal
projectors by the two one-sided bounds. The constant cannot be lowered
(@file(LeanDLRA/Tensor/Tucker/ProjectorLipschitzRankOneSharp.lean)):

@stmt LeanDLRA/Tensor/Tucker/ProjectorLipschitzRankOneSharp.lean exists_mul_lt_norm_tuckerTangentProj_sub_of_unique Tensor.exists_mul_lt_norm_tuckerTangentProj_sub_of_unique

For every `d ≥ 2` and every `q < √(2 (d - 1)/d)` there are such tensors in `ℝ^{2 × ⋯ × 2}` and a
tensor `B` with `q ‖X‖⁻¹ ‖Y - X‖ ‖B‖ < ‖P(Y) B - P(X) B‖`
(`Tensor.sqrt_le_of_forall_norm_tuckerTangentProj_sub_le` says that every valid constant is at
least `√(2 (d - 1)/d)`). Not shown: the optimal constant for `d ≥ 3` over all multilinear
ranks; for `d = 3` it lies between `23 / 20` and `√3`.

**The normal component of a nearby Tucker tensor.** With `ρ` a lower bound of the smallest
nonzero singular values of the matricizations of `Y` and `e = ‖X - Y‖`, in
@file(LeanDLRA/Tensor/Tucker/NormalSecondOrder.lean):

@stmt LeanDLRA/Tensor/Tucker/NormalSecondOrder.lean norm_sub_tuckerTangentProj_tucker_le Tensor.norm_sub_tuckerTangentProj_tucker_le

The normal component of `X` at `Y` is of second order in `e` with a constant that does not depend
on the number of modes; to leading order the constant is `1 / √2`. The bound of
[BachmayrEisenmannUschmajew2025, Prop. 4.9] is `√d e²/ρ` (for all `e`, with `ρ` at the other
point). The proof uses the prefix products `P₀ 0 ⋯ P₀ (i - 1)` of the mode projectors and the
inequality `‖A M B‖ ≤ ρ⁻¹ ‖A M‖ ‖M B‖` for a matrix `M` of rank at most `q` with `ρ ≤ σ_{q-1}(M)`.
The abstract form of the comparison of tangent vectors at two frames without the factor `√d` is
in @file(LeanDLRA/Tensor/Tucker/TangentNormalPrefix.lean); there the bound
`σ ‖T - P T‖ ≤ 2 ‖x - y‖ ‖T‖` holds under two hypotheses per mode that are instances of the
inequality above, and the file does not carry out the matricization.

**Quasi-optimality of Tucker DLRA with the normal velocity as growth rate.** For a solution `Y`
of `Ẏ = P(Y) F(t, Y)` in the tube `‖Y - X‖ ≤ ε < ρ/2` around a curve `X` of Tucker tensors, with
`ν ≥ ‖(1 - P(X)) F(t, A)‖`, `ν' ≥ ‖(1 - P(Y)) F(t, A)‖`, `g ≥ ‖P(X) F(t, A) - Ẋ‖` and `ρ` a lower
bound of the smallest nonzero singular values of all matricizations of `X` and of `Y`, the file
@file(LeanDLRA/Tensor/Tucker/QuasiOptimalityNormalVelocity.lean) has the bound of section 3.8
with the rate `k = L + (ν + ν') / √(2 ρ (ρ - 2 ε))`, which does not depend on `d`:

@stmt LeanDLRA/Tensor/Tucker/QuasiOptimalityNormalVelocity.lean norm_tucker_sub_tucker_le_integral_exp_integral Tensor.norm_tucker_sub_tucker_le_integral_exp_integral

To leading order in `ε` the rate is `L + √2 ν/ρ`. The error bound in a real inner product space for
a curve `Y` with `Ẏ = P_Y(t) F(t, Y)` and any rate `κ` with
`⟪Y - X, (P_Y - P_X) F(t, A)⟫ ≤ κ ‖Y - X‖²` is
`LeanDLRA.norm_sub_le_integral_exp_integral_of_inner_apply_sub_apply_le`, and for Tucker tensors
`Tensor.inner_sub_tuckerTangentProj_sub_le` gives the pairing with the factor
`1/√(2 ρ (ρ - 2 ‖Y - X‖))`. What is not shown: the existence of the solution `Y` is a hypothesis,
as is the tube condition.

### 8.3 Tree tensor networks

The integrators for tree tensor networks are stated on two levels. On the projector level a
step is a recursive predicate on a general real inner product space:
`IsTTNKSLStep` (projector splitting) over a tree shape `TreeShape`, and `IsTTNBUGStep`,
`IsAugTTNBUGStep`, `IsParTTNBUGStep` (fixed-rank, rank-adaptive and parallel BUG) over a frame
`TTNFrame`, the tree with its old projectors and the classes of admissible new projectors. The
predicates are defined in [`LeanDLRA/Tensor/Steps.lean`](../LeanDLRA/Tensor/Steps.lean), the
theorems about them are in the folder
[`LeanDLRA/Tensor/TTN/Abstract`](../LeanDLRA/Tensor/TTN/Abstract). On the second level the
steps act on tensors over a dimension tree (`DimTree`), in the folder
[`LeanDLRA/Tensor/TTN`](../LeanDLRA/Tensor/TTN). Each of the four steps on tensors is an
instance of its predicate of the projector level
(`DimTree.IsProjectorSplittingStep.isTTNKSLStep`,
`DimTree.BasisFrame.IsBUGStep.isTTNBUGStep`, `DimTree.BasisFrame.IsAugBUGStep.isAugTTNBUGStep`,
`DimTree.BasisFrame.IsParBUGStep.isParTTNBUGStep`), so the four error bounds hold for tensors.

@stmt LeanDLRA/Tensor/TTN/ProjectorSplitting.lean projectorSplitting_global_error DimTree.projectorSplitting_global_error

The recursive projector-splitting integrator on tensors over a dimension tree `τ`. For `τ` and
`L, B, T ≥ 0` there are constants `c₀`, `c₁`, `c₂` such that for all mode index types and all
fields that are Lipschitz with constant `L`, bounded by `B` and continuous in time, `N` given
steps of size `h ≥ 0` with `N * h ≤ T` satisfy `‖Y n - A (t₀ + n * h)‖ ≤ c₀ δ + c₁ ε + c₂ h`
for `n ≤ N`. The constants are chosen before the mode index types, the field and the data of
the run, so they depend on `τ`, `L`, `B` and `T` only; their values are not given. `ε` is the
bound of the step predicate `DimTree.IsProjectorSplittingStep`. The theorem is derived from the
projector-level theorem `ttn_ksl_global_error`.

Source: Ceruti, Lubich and Walach, arXiv 2002.11392, Theorem 6.1, as cited in the docstring;
the docstring of `ttn_ksl_global_error` cites [CerutiLubichWalach2021, Thm. 6.1].

@stmt LeanDLRA/Tensor/TTN/Abstract/BUG.lean ttn_global_error_le ttn_global_error_le

@stmt LeanDLRA/Tensor/TTN/Abstract/RankAdaptiveBUG.lean augTTN_global_error_le augTTN_global_error_le

The fixed-rank and the rank-adaptive BUG integrator, on the projector level. The field is
Lipschitz with constant `L`, bounded by `B` and continuous in time, on the whole space, which
has to be complete. The steps are given (`hstep`), with frames `fr n` that have at most `s`
nodes and height at most `ℓ` (`hsize`, `hheight`), and the step size satisfies
`2 * L * h * ℓ ≤ 1` (`hLh`). `ε` is the bound of the step predicate and `ϑ` the truncation
tolerance of the rank-adaptive step. Conclusions: for `n ≤ N` with `n * h ≤ T`

`‖Y n - A (t₀ + n * h)‖ ≤ e^{L T} (δ + 3 s T (ε + 6 L B h))` (fixed rank),

`‖Y n - A (t₀ + n * h)‖ ≤ e^{L T} (δ + 3 s T (ε + 6 L B h) + 3 s n ϑ)` (rank-adaptive).

The constants are explicit and depend on `L`, `B`, `T` and the number of nodes; no singular
value appears in the statements.

Source: the docstring of the first theorem calls it the analogue for the BUG integrator of
[CerutiLubichWalach2021, Thm. 6.1], which treats the projector-splitting integrator. The
docstring of the second names [CerutiLubichSulz2023] for the integrator and cites no theorem of
a paper for the bound.

@stmt LeanDLRA/Tensor/TTN/BUG.lean bug_global_error DimTree.BasisFrame.bug_global_error

@stmt LeanDLRA/Tensor/TTN/RankAdaptiveBUG.lean augBUG_global_error DimTree.BasisFrame.augBUG_global_error

The same two bounds on tensors over a valid dimension tree `τ` (`hv`), for the steps
`DimTree.BasisFrame.IsBUGStep` and `DimTree.BasisFrame.IsAugBUGStep` with basis frames `f n` of
the tree. The number of nodes is `τ.nodeCount`, and the condition on the step size is
`2 * L * h * τ.treeHeight ≤ 1` (`hLh`). In the rank-adaptive step the truncation is the clause
`‖Y₁ - YS t₁‖ ≤ ϑ` of the step predicate; the core has no truncation of a tree tensor network
that is proved to satisfy it (section "TODO" of the two module docstrings).

@stmt LeanDLRA/Tensor/TTN/ParallelBUG.lean parBUG_global_error DimTree.BasisFrame.parBUG_global_error

The parallel BUG integrator for tree tensor networks. `τ` is a dimension tree (`DimTree`) that
is valid (`hv`), with `τ.nodeCount` nodes and height `τ.treeHeight`; a step is
`DimTree.BasisFrame.IsParBUGStep` for a basis frame `f n` of the tree. The field is Lipschitz
with constant `L`, bounded by `B`, continuous in time and Lipschitz in time with constant `Lt`
(`hF`, `hB`, `hcont`, `hFt`); the step size satisfies `2 * L * h * τ.treeHeight ≤ 1` (`hLh`). The
steps are given (`hstep`); `ε` is the bound on the normal component and `ϑ` the truncation
tolerance at every node (docstring of the theorem). Conclusion: for `n * h ≤ T`

`‖Y n - A (t₀ + n * h)‖ ≤ e^{L T} (δ + 3 s T (2 ε + (9 L B + Lt) h) + 3 s n ϑ)`, `s = τ.nodeCount`.

The constants depend on `L`, `Lt`, `B`, `T` and the number of nodes (leaves included); no
singular value of a matricization of a connecting tensor appears in the statement.

Source: Ceruti, Kusch, Lubich and Sulz, arXiv 2412.00858, Theorem 4.5, as cited in the
docstring. The theorem is derived from the projector-level theorem `parTTN_global_error_le`
([`LeanDLRA/Tensor/TTN/Abstract/ParallelBUG.lean`](../LeanDLRA/Tensor/TTN/Abstract/ParallelBUG.lean)),
whose docstring cites the same theorem as [CerutiEtAl2024, Thm. 4.5].

**The factor `√(s - 1)` in place of `s`.** The robust bounds above multiply the doubly normal bound
`ε` by the number `s` of nodes. The file @file(LeanDLRA/Tensor/TTN/BUGSqrtNodes.lean) replaces this
factor by `√(s - 1)` for the fixed-rank BUG integrator, on the projector level for frames that
satisfy the commutation predicate `TTNFrame.IsCoRangeCommuting`
(@file(LeanDLRA/Tensor/TTN/Defs.lean)):

@stmt LeanDLRA/Tensor/TTN/Defs.lean TTNFrame.IsCoRangeCommuting TTNFrame.IsCoRangeCommuting

At every inner node the admissible mode operators of every child commute with the co-range
projector of that child. Two orthogonalities are used. At one inner node the capture defects of
the commuting mode projectors of the updated bases add in squares
(`norm_sub_modeProd_apply_le_sqrt`). Along a branch, the defect `(1 - P₁) A(t₁)` of a child splits
with the co-range projector `Q₀` of that child into the part `(1 - Q₀)`, the doubly normal part of
the field (of size `h ε`), and the part `Q₀`, the error of the subtree (of size `η`); if `P₁`
commutes with `Q₀` the parts are orthogonal:

@stmt LeanDLRA/Tensor/TTN/BUGSqrtNodes.lean kstep_capture_inexact_sqrt kstep_capture_inexact_sqrt

The local error of one step and the global error are:

@stmt LeanDLRA/Tensor/TTN/BUGSqrtNodes.lean ttn_local_error_le_sqrt ttn_local_error_le_sqrt

@stmt LeanDLRA/Tensor/TTN/BUGSqrtNodes.lean ttn_global_error_le_sqrt ttn_global_error_le_sqrt

`fr.size` is the number of nodes, `fr.height` the height, `κ = e^{L h}(1 + L h)` is the factor
per level, and `ttn_local_error_le_sqrt_size` gives `3 h (√(s - 1) ε + 6 s L B h)` for one step
if `2 L h · height ≤ 1`. The `h`-term keeps the factor `s`. On tensors the commutation holds for
every basis frame (`DimTree.BasisFrame.isCoRangeCommuting_toTTNFrame`): the projector of a child
acts on the modes of its subtree and its co-range projector on the other modes. So for a valid
dimension tree `τ` with `τ.nodeCount` nodes:

@stmt LeanDLRA/Tensor/TTN/BUGSqrtNodes.lean bug_global_error_sqrt DimTree.BasisFrame.bug_global_error_sqrt

The factor of `ε` cannot be lowered in the local error. For a star with `m` leaves
(`SqrtNodesExample.starFrame_size`: `m + 1` nodes), orthonormal directions `n i` orthogonal to
`Y₀` and the constant field `ε ∑ᵢ nᵢ`, the step of the fixed-rank BUG integrator on the star
frame stays at `Y₀` (`SqrtNodesExample.isTTNBUGStep_starFrame`), while the exact solution has
moved by

@stmt LeanDLRA/Tensor/TTN/BUGSqrtNodes.lean norm_sub_starFrame_exact SqrtNodesExample.norm_sub_starFrame_exact

that is, `√(s - 1) h ε` with `s = m + 1`. What is not shown: the square root is for the
`ε`-term of the fixed-rank integrator; the rank-adaptive and the parallel integrators keep the
factor `s`, and the bound for `ε` summed over the nodes with the node-resolved values
`h √(∑ ε_v²)` is not in the core. The sharpness is shown for the abstract frame, not for tensors.

Literature. The published bounds for tree tensor networks state that their constants depend on
the tree and on the bounds of the field (Ceruti, Lubich and Walach, [CerutiLubichWalach2021],
Theorem 6.1; [CerutiLubichSulz2023], Theorem 5.1); the dependence on the tree is not made
explicit there. A square root of the number of matricizations is the quasi-optimality constant of
hierarchical singular value truncation (Bachmayr and Dahmen, [BachmayrDahmen2013], Remark 5,
(45): `κ_P = √m` for the Tucker format and `√(2m - 3)` for the hierarchical format;
Kieri and Vandereycken [KieriVandereycken2019] for the tensor train singular value decomposition,
`C_R = √(d - 1)`). The factor of `ε` in the local error of the BUG step is `√(s - 1)`, of the same
order as this constant; the files do not claim an independence of the tree.

## 9. Kinetic equations: vocabulary

For kinetic equations the core contains definitions, identities between them and the rank of
the low-rank ansatz, and no error theorem. The definitions are in
[`LeanDLRA/Kinetic/Defs.lean`](../LeanDLRA/Kinetic/Defs.lean), namespace `Kinetic`. A kinetic
density `f(x, v)` on a grid in phase space is a matrix with the space nodes as rows and the
velocity nodes as columns; on a continuous phase space it is a function of two variables.

@stmt LeanDLRA/Kinetic/Defs.lean Quadrature Kinetic.Quadrature

@stmt LeanDLRA/Kinetic/Defs.lean quadMoment Kinetic.quadMoment

@stmt LeanDLRA/Kinetic/Defs.lean density Kinetic.density

@stmt LeanDLRA/Kinetic/Defs.lean streaming Kinetic.streaming

@stmt LeanDLRA/Kinetic/Defs.lean lowRankAnsatz Kinetic.lowRankAnsatz

@stmt LeanDLRA/Kinetic/Defs.lean maxwellian Kinetic.maxwellian

A quadrature has nodes and positive weights that sum to one. `Kinetic.quadMoment w ζ f` is the
moment of `f` with the velocity weights `w` and the velocity function `ζ`, and `Kinetic.density`
is the moment with `ζ = 1`; it equals the matrix–vector product of `f` and `w`
(`Kinetic.density_eq_mulVec`). `Kinetic.streaming D M` is the operator `f ↦ ∑ k, D k * f * M k`
with matrices `D k` that act on the space index from the left and matrices `M k` that act on the
velocity index from the right (`Kinetic.streaming_apply`); in the docstring `D k` is a spatial
difference matrix and `M k` typically the diagonal matrix of the `k`-th velocity component.
`Kinetic.lowRankAnsatz w X S V` is the function `w(v) ∑ X_i(x) S_ij V_j(v)`; with weight one,
and with the basis functions stored as the rows of matrices `X` and `V`, it is the matrix
product `Xᵀ * S * V` entry by entry (`Kinetic.lowRankAnsatz_one_eq_mul`).
`Kinetic.maxwellian R ρ T u` is the Maxwellian with gas constant `R`, density `ρ`, temperature
`T` and mean velocity `u`; it is positive for positive `R`, `ρ` and `T`
(`Kinetic.maxwellian_pos`). The file also defines `Kinetic.PhaseGrid` (positive weights for the
space nodes and the velocity nodes), the continuous moment `Kinetic.velocityMoment`,
orthonormality of a velocity basis with respect to a measure (`Kinetic.IsOrthonormalWrt`; it
holds if and only if every basis function is in the `L²` space of the measure and the classes of
the basis functions are orthonormal there, `Kinetic.isOrthonormalWrt_iff_orthonormal_toLp`), and
the periodic difference matrices `Kinetic.fwdDiff`, `Kinetic.bwdDiff`, `Kinetic.centralDiff`,
`Kinetic.secondDiff` with the identities `Kinetic.centralDiff_eq` and `Kinetic.secondDiff_eq`.

@stmt LeanDLRA/Kinetic/Stencils.lean fwdDiff_mul_apply Kinetic.fwdDiff_mul_apply

@stmt LeanDLRA/Kinetic/Stencils.lean fwdDiff_transpose Kinetic.fwdDiff_transpose

[`LeanDLRA/Kinetic/Stencils.lean`](../LeanDLRA/Kinetic/Stencils.lean) gives the products of the
four difference matrices with a matrix `u` whose rows are indexed by the cells `ZMod N` of the
periodic grid, entry by entry: the forward difference quoted above, and
`Kinetic.bwdDiff_mul_apply`, `Kinetic.centralDiff_mul_apply` and `Kinetic.secondDiff_mul_apply`
for the three others. It also gives the transposes: the transpose of the forward difference is
minus the backward difference and conversely (`Kinetic.bwdDiff_transpose`), the central
difference is skew-symmetric (`Kinetic.centralDiff_transpose`) and the second difference is
symmetric (`Kinetic.secondDiff_transpose`). The module docstring calls these identities the
matrix form of summation by parts on a periodic grid. For cells numbered by `Fin N` the file
gives the entries of the four matrices read through the ring isomorphism `ZMod.finEquiv N`
(`Kinetic.fwdDiff_submatrix_finEquiv` and the three analogues) and their stencils
(`Kinetic.fwdDiff_submatrix_finEquiv_mulVec` and the three analogues). No paper is cited.

@stmt LeanDLRA/Kinetic/LowRank.lean hasSepRankLE_iff_exists_lowRankAnsatz Kinetic.hasSepRankLE_iff_exists_lowRankAnsatz

@stmt LeanDLRA/Kinetic/LowRank.lean rank_lowRankAnsatz_le Kinetic.rank_lowRankAnsatz_le

[`LeanDLRA/Kinetic/LowRank.lean`](../LeanDLRA/Kinetic/LowRank.lean) relates the ansatz to the
separation rank of section 2.5. A real function of two variables has separation rank at most `r`
if and only if it is a low-rank ansatz with `r` basis functions in each variable, the weight one
and the identity matrix as core. On finite index types the matrix of an ansatz has rank at most
the smaller of the two numbers of basis functions; the weight `w` and the core `S` are
arbitrary.

Results of single papers on kinetic equations (asymptotic-preserving schemes, conservation,
stability of discretizations) are in the catalogue, in the folder `LeanDLRA/Literature/Kinetic`,
and are not part of the core.

## 10. Training, filtering, control

For these three applications the core has the results below. Each of them is stated on a general
state space with orthogonal projectors or for matrices, and none of them is an instance of the
run theorem of section 4.3.

### 10.1 Training

@stmt LeanDLRA/Training/Defs.lean projGradStep projGradStep

@stmt LeanDLRA/Training/Descent.lean loss_projGradStep_le loss_projGradStep_le

The projected gradient step is `x - h P (g x)`. Let the loss `ℒ` have the gradient `g` (`hℒ`)
and let `g` be Lipschitz with constant `β` (`hg`). For every orthogonal projector `P` and every
`h` the loss after the step is at most `ℒ x - h (1 - β h / 2) ‖P (g x)‖²`. The only constant is
`β`.

Source: Kusch, Schotthöfer and Walter, arXiv 2502.03006, Theorem 5.8, and arXiv 2410.18720,
eqs. (22)–(25), as cited in the docstring.

@stmt LeanDLRA/Training/Descent.lean exists_projGrad_sq_le exists_projGrad_sq_le

Existence of a value where the projected gradient is small. The hypotheses on `ℒ` and `g` are
those of the first theorem, and every `P k` is an orthogonal projector (`hP`). Let the values
`x k` be projected gradient steps followed by a change of norm at most `ϑ` (`htr`), let
`‖g‖ ≤ G` on the segment between the step and the changed value (`hG`), let `ℒinf` be a lower
bound of the loss along the sequence (`hinf`), let `h (1 - β h / 2) > 0` (`hh`) and `n > 0`
(`hn`). Then among the first `n` values there is one with

`‖P k (g (x k))‖² ≤ (ℒ (x 0) - ℒinf) / (n h (1 - β h / 2)) + G ϑ / (h (1 - β h / 2))`.

Source: Schotthöfer and Laiu, arXiv 2406.17887, Theorem 3 (for one client and one local step),
as cited in the docstring.

@stmt LeanDLRA/Training/FederatedDescent.lean loss_fedRound_le_one loss_fedRound_le_one

Loss descent of one round of a federated scheme. `fedRound P gc g lr sstar x`
([`LeanDLRA/Training/Defs.lean`](../LeanDLRA/Training/Defs.lean)) is the average over the
clients `c` of the results of `sstar` local steps from `x` with step size `lr`; a local step
uses the client gradient `gc c`, corrected by the difference of the global gradient `g` and the
client gradient at `x`, and the orthogonal projector `P`. Let `ℒ` have the gradient `g` (`hℒ`),
let `g` and every `gc c` be Lipschitz with constant `β` (`hg`, `hgc`), and let
`lr * β * sstar ≤ 1` (`hs`). Then the loss after the round is at most
`ℒ x - A (1 - A β) ‖P (g x)‖²` with `A = sstar * lr`. In the same file,
`fedRound_constant_one_sharp` shows on the loss `‖x‖² / 2` with one client that the factor one
in front of `A β` cannot be replaced by a smaller number in a bound of this form.

Source: the setting is that of Schotthöfer and Laiu, arXiv 2406.17887, Theorem 8, before
truncation, as cited in the docstring. The module docstring compares the bound with
`loss_fedRound_le`, which has the factor 12 in the place of the factor one. In the same file,
`loss_fedRound_le_two_ninths` gives a descent by `2 A a² / 9` on the whole range
`lr * β * sstar ≤ 1`, and `exists_fedRound_no_descent` gives a loss, a global gradient and one
client for which the loss does not decrease when `3 ≤ (1 + lr)^sstar` (with `β = 1`); in that
example the global gradient is not the average of the client gradients.

@stmt LeanDLRA/Research/FederatedDescentThreshold.lean loss_fedRound_le_of_pow_le_three FederatedThreshold.loss_fedRound_le_of_pow_le_three

@stmt LeanDLRA/Research/FederatedDescentThreshold.lean exists_fedRound_ascent FederatedThreshold.exists_fedRound_ascent

@stmt LeanDLRA/Research/FederatedDescentThreshold.lean loss_fedRound_le_of_convex FederatedThreshold.loss_fedRound_le_of_convex

@stmt LeanDLRA/Research/FederatedDescentThreshold.lean loss_le_loss_fedRound_linear FederatedThreshold.loss_le_loss_fedRound_linear

The descent threshold of one round
([`LeanDLRA/Research/FederatedDescentThreshold.lean`]
(../LeanDLRA/Research/FederatedDescentThreshold.lean)).
The hypotheses of the first two statements are those of `loss_fedRound_le_one`: the global
gradient and the client gradients are independent data with the Lipschitz constant `β`, and the
step size is not restricted. First theorem: the loss does not increase when `(1 + lr * β)^sstar ≤ 3`
(`FederatedThreshold.loss_fedRound_lt_of_pow_lt_three` gives a decrease for `< 3` and a non-zero
projected gradient). Second theorem: for every `v ≠ 0` there are a loss, a global gradient and one
client gradient with Lipschitz constant 1 for which every round with `3 < (1 + lr)^sstar`
increases the loss; the bound of `FederatedThreshold.loss_fedRound_le_of_one_le` is attained for
this client (`FederatedThreshold.loss_fedRound_neg_eq`). So `(1 + lr * β)^sstar ≤ 3` is the exact
condition under which a round cannot increase the loss in this generality, and the example has
a client with a concave loss and a global loss that is convex. For convex clients (the gradient
inequality of each client loss) the third theorem gives a descent for `(sstar + 1) * lr * β ≤ 2`;
the amount of descent is proportional to `lr`, not to `sstar * lr`, and the range
`2 - lr * β ≤ sstar * lr * β < 2` is not decided (module docstring). The fourth theorem concerns
the setting of the paper, where the global gradient is the average of the client gradients:
for clients with the gradients `z ↦ h_c z + v` the round is a step of a length `m` and the loss
does not decrease when `(mean h) * m ≥ 2`; two `example`s show Hessians `-1, 1, 1, 1` at
`sstar * lr * β = 3` and a convex pair at 15/2. The statements are about one round before
truncation and with exact client gradients.

Source: the module docstring names Schotthöfer and Laiu, arXiv 2406.17887, Theorem 2 and
Theorem 8, as the setting.

**Thresholds for convex clients, and for two and three local steps.**

@stmt LeanDLRA/Research/FederatedConvexThreshold.lean loss_fedRound_lt_of_convex_of_lr_mul_le_one loss_fedRound_lt_of_convex_of_lr_mul_le_one

@stmt LeanDLRA/Research/FederatedTwoSteps.lean loss_fedRound_two_lt loss_fedRound_two_lt

@stmt LeanDLRA/Research/FederatedThreeSteps.lean loss_fedRound_three_lt_of_convex loss_fedRound_three_lt_of_convex

@stmt LeanDLRA/Research/FederatedThreeSteps.lean loss_le_loss_fedRound_three_quadratic loss_le_loss_fedRound_three_quadratic

Three files fill in the case of convex clients of the previous paragraph. In all of them
`fedRound P gc g lr sstar x` is the round of the older statement, `β` is the Lipschitz constant
of the client gradients, and the round is considered before truncation and with exact gradients.

*Convex clients, `lr β ≤ 1`* ([`LeanDLRA/Research/FederatedConvexThreshold.lean`]
(../LeanDLRA/Research/FederatedConvexThreshold.lean)). The global gradient `g` is a given gradient
of the loss and need not be the average of the client gradients; every client loss satisfies the
gradient inequality `hconv`. If `lr β ≤ 1` and `sstar lr β < 2`, the round decreases the loss
whenever `P (g x) ≠ 0` (first theorem). The file also gives the amount,
`ℒ (fedRound …) ≤ ℒ x - lr (1 - sstar lr β / 2) ‖P (g x)‖²`
(`loss_fedRound_le_of_convex_of_lr_mul_le_one`). The third theorem of the previous paragraph had
the condition `(sstar + 1) lr β ≤ 2`; for `sstar ≥ 2` the condition `sstar lr β < 2` implies
`lr β ≤ 1`, so the gap between the two conditions is closed there. For `sstar = 1` with the
global gradient used by all clients the round is one projected gradient step, and the range
`1 < lr β < 2` is the descent lemma; it is not covered by this file. A constant-gradient client
shows that there is no descent in general for `sstar lr β ≥ 2` without the averaging hypothesis
(`loss_le_loss_fedRound_zero`, as cited in the module docstring).

*Two local steps, averaged gradients* ([`LeanDLRA/Research/FederatedTwoSteps.lean`]
(../LeanDLRA/Research/FederatedTwoSteps.lean)). In the setting of the paper the global gradient is
the average of the client gradients (`hmean`). For `sstar = 2` the correction terms average to
zero, so the round is exactly two projected gradient steps for the global loss
(`fedRound_two_eq_projGradStep`). Hence (second theorem) the loss decreases when `0 < lr` and
`lr β < 2`, that is `sstar lr β < 4`, for every loss with a `β`-Lipschitz gradient; the client
losses need not be convex and their gradients need not be Lipschitz. For `lr β ≥ 2` there is no
descent in general: `loss_le_loss_fedRound_two_quadratic` gives identical clients with the loss
`⟪v, y⟫ + ‖y‖² / 2` (`β = 1`) and `lr ≥ 2` for which a round from `0` does not decrease the
loss. The threshold `sstar lr β < 4` is therefore exact for `sstar = 2`.

*Three local steps, averaged gradients* ([`LeanDLRA/Research/FederatedThreeSteps.lean`]
(../LeanDLRA/Research/FederatedThreeSteps.lean)). The global loss is the average of convex client
losses (`hℒmean`) with `β`-Lipschitz gradients and the global gradient is the average of the
client gradients. For `sstar = 3` the round decreases the loss if `0 < lr` and `lr β < 15/8`, that
is `sstar lr β < 45/8` (third theorem; the proof is a weighted sum of four gradient inequalities
of every client along the chain `x → z¹ → z²_c → x⋆` and the pair `x → x⋆`, with a fifth for `lr β
> 5/3`). For `lr β ≤ 5/3` the file gives an amount (`loss_fedRound_three_le_of_convex`); that
constant is not the best one. The fourth theorem shows that the bound 15/8 on `lr β` cannot be
raised: for `lr β = 15/8` it gives `45` quadratic clients (`32` with Hessian `1` and `13` with
Hessian `0`, so `β = 1`) for which a round from `0` does not decrease the loss. So `sstar lr β <
45/8` is the exact condition for descent of a round with three local steps, for convex clients
with averaged gradients. The constant for `5/3 ≤ lr β ≤ 15/8`
(`loss_fedRound_three_le_of_convex_of_sq`) is the loss change of clients with Hessians `0` and `1`
for one proportion of the two kinds; the file proves that only at `lr β = 15/8`. For `sstar ≥ 4`
the exact threshold with averaged gradients is not determined in the core; quadratic clients
bound it from above (`FederatedThreshold.loss_le_loss_fedRound_linear`), and the next file
bounds it from below.

@stmt LeanDLRA/Research/FederatedManySteps.lean loss_fedRound_lt_of_convex_of_mul_lt_four loss_fedRound_lt_of_convex_of_mul_lt_four

*Every number of local steps* ([`LeanDLRA/Research/FederatedManySteps.lean`]
(../LeanDLRA/Research/FederatedManySteps.lean)). In the setting of the previous paragraph (the
global loss is the average of convex client losses with `β`-Lipschitz gradients) the round
decreases the loss for every `sstar ≥ 2`, every `0 < lr` and `sstar lr β < 4`, if
`P (g x) ≠ 0` (the theorem above). Where `lr β ≤ 1` the file gives an amount
(`loss_fedRound_le_of_convex_of_mul_le_four`): the descent is at least
`lr (243 + 189 u - 222 u² - 164 u³) / ((9 + 8 u) (9 + 11 u)²) ‖Π ∇ℒ(x)‖²` with `u = lr β`, which
tends to `lr / 3` as `lr β → 0`; the constant is not the best one. For `sstar = 2` and `sstar = 3`
the condition `lr β ≤ 1` is not needed, by the two files above. The proof uses three points per
client, `x`, the last local iterate `z_c` and the average `x⋆`, whatever the number of local
steps: gradient inequalities for the pairs `x → x⋆`, `z_c → x⋆` and `z_c → x`, and the bounds
`‖z_c - x‖² ≤ sstar lr² ∑_{j<sstar} ‖G_j‖²` and `‖G_0‖² ≤ ∑_{j<sstar} ‖G_j‖²`
(`add_sum_norm_sq_proj_le_of_convex` for the descent along the local steps). What is not shown:
the condition `sstar lr β < 4` is sufficient and not necessary for `sstar ≥ 3`; for `sstar = 3`
the exact threshold is `sstar lr β < 45/8` (above), and for `sstar ≥ 4` the exact threshold is not
known to
the core. The clients are averaged with equal weights, as in `fedRound`.

Source: the setting is that of Schotthöfer and Laiu, arXiv 2406.17887 ([SchotthoferLaiu2024]),
before truncation, as cited in the module docstrings. The statements cite no theorem of a paper.

**Training: rates, fixed points of federated rounds, and the explicit Euler splitting step.**

@stmt LeanDLRA/Training/ConvergenceRates.lean loss_sub_le_exp_of_projGradFlow_PL loss_sub_le_exp_of_projGradFlow_PL

@stmt LeanDLRA/Training/FederatedFixedPoints.lean exists_fedAvgRound_fixed_ne_stationary exists_fedAvgRound_fixed_ne_stationary

@stmt LeanDLRA/Training/ProjectorSplittingDescent.lean loss_kslEulerStep_le_of_smooth_quarter loss_kslEulerStep_le_of_smooth_quarter

@stmt LeanDLRA/Training/ProjectorSplittingDescent.lean loss_kslEulerStep_gt_of_goldenRatio_lt loss_kslEulerStep_gt_of_goldenRatio_lt

Four statements from three files, all for a loss `ℒ` with gradient `g`.

@file(LeanDLRA/Training/ConvergenceRates.lean): along the projected gradient flow
`y' = -Π(t) g(y)` with orthogonal projectors `Π(t)`, the condition
`2 μ (ℒ(y) - ℒ⋆) ≤ ‖Π g(y)‖²` (of Polyak–Łojasiewicz type) gives the exponential decay
`ℒ(y t) - ℒ⋆ ≤ e^{-2 μ (t - a)} (ℒ(y a) - ℒ⋆)`. The file has further statements of this kind for
truncated steps with an augmented projector (`loss_sub_le_pow_of_riemannianPL_truncated`), for a
projector that is refreshed every `T` steps (`exists_grad_sq_le_of_lazyRefresh`), for random
projectors (`sum_loss_projGradStep_le_of_isotropic`) and for the federated round without variance
correction (`loss_fedAvgRound_le`, which has a term in the spread `ζ` of the client gradients that
the round with variance correction does not have).

@file(LeanDLRA/Training/FederatedFixedPoints.lean): for the round with variance correction a fixed
point is stationary for the projected gradient (`apply_grad_eq_zero_of_fedRound_eq_self`, under
`e · lr β sstar < 1`). The quoted theorem shows that the round without the correction can have a
fixed point where the sum of the client gradients does not vanish, for every number `sstar ≥ 2` of
local steps (client drift); the statement is about two quadratic clients on `ℝ`.

@file(LeanDLRA/Training/ProjectorSplittingDescent.lean): the projector-splitting integrator with
one explicit Euler step per substep, applied to the gradient flow (`kslEulerStep` of
@file(LeanDLRA/Stability/Energy.lean)), with exact gradients and a new basis that captures the
K-step. If the gradient is `β`-Lipschitz and `β h ≤ 1/4`, the loss decreases by at least
`(h / 8) ‖T₁ g(x)‖²`, where `T₁` is the tangent projector of the step; the constants do not depend
on the state. For the quadratic loss the step decreases the loss for `0 ≤ h ≤ φ`, the golden
ratio (`loss_kslEulerStep_quadratic_le`), and the last theorem shows that this cannot be relaxed:
for every `h > φ` there is a state for which the loss increases, while the gradient step
decreases it for `h < 2`. Stochastic gradients, truncation of the rank and the loss of rank
during training are not treated (module docstring).

Source: the module docstrings cite arXiv 2307.05695, 2403.03507, 2401.03748 and 2406.17887 (the
training methods) and arXiv 2502.03006, Sections 3.2, 3.3 and 5 (the splitting step).

@stmt LeanDLRA/Training/GradientFlowConvergence.lean projectedGradient_global_error GradientFlowConvergence.projectedGradient_global_error

Distance of the iteration to the gradient flow. `A` solves `W' = -G(W)`, where `G` is Lipschitz
with constant `β` and bounded by `B`; the step size (learning rate) is `lr`. The iteration is
`W (n+1) ≈ W n - lr P_n g_n` up to a change of norm at most `ϑ` (`hstep`), with gradient
estimates `g n` within `σ` of `G (W n)` (`hσ`) and with the part of the gradient outside the
range of the orthogonal projector `Pr n` bounded by `ε` (`hε`); `ε ≥ 0`, `σ ≥ 0` and `lr ≥ 0`.
The theorem has the older form: it assumes solutions `Φ n` of the gradient flow that start at
the values `W n` (`hΦ`, `hΦ₀`). Conclusion: for `n * lr ≤ T`

`‖W n - A (t₀ + n * lr)‖ ≤ e^{β T} (‖W 0 - A t₀‖ + T (β B lr / 2 + ε + σ) + n ϑ)`.

The constants are `β`, `B` and `T`; no singular value appears in the statement. The bound
contains the factor `e^{β T}`, and the term `T σ` does not go to zero with the step size
(docstring of the theorem).

Source: the docstring names arXiv 2306.01485, Theorem 1; arXiv 2410.18720, Theorem 3;
arXiv 2502.03006, Theorem 5.6; arXiv 2406.17887, Theorem 5.

### 10.2 Filtering

@stmt LeanDLRA/Filtering/Defs.lean riccatiField#1 KalmanBucy.riccatiField

@stmt LeanDLRA/Stochastic/KalmanBucy.lean dlrKalmanBucy_covariance_error_uniform KalmanBucy.dlrKalmanBucy_covariance_error_uniform

`KalmanBucy.riccatiField A ρ Qn` is the field `P ↦ A P + P Aᵀ - ρ P² + Qn` of the Riccati
equation for the covariance of the Kalman–Bucy filter with full observation `ρ I` (docstring of
the definition); here `ρ ≥ 0` (`hρ`) is this factor and not a tube radius, and `Qn` is the
covariance of the model noise. `P` solves this equation and `PD` solves it with the noise
`PU t * Qn * PU t`; in the docstring `PU t` is the projector of the low-rank filter, and the
statement does not use that `PU t` is a projector. If the drift is strictly dissipative (`hA`
with `μ < 0`), both solutions are positive semidefinite (`hpsd`) and
`‖Qn - PU t * Qn * PU t‖ ≤ η` (`hη`), then

`‖PD t - P t‖ ≤ e^{μ (t - a)} ‖PD a - P a‖ + η / (-μ)` on `[a, b]`.

The bound does not grow with time. The constants are `μ` and `η` only.

Source: the docstring names arXiv 2509.11210, Section 4, for the filter.

@stmt LeanDLRA/Filtering/Defs.lean analysisCov KalmanBucy.analysisCov

@stmt LeanDLRA/Stochastic/KalmanBucy.lean analysisCov_mono KalmanBucy.analysisCov_mono

`KalmanBucy.analysisCov C R Pi` is the analysis (posterior) covariance
`Pi - Pi Cᵀ S⁻¹ C Pi` of a Kalman analysis step with `S = C Pi Cᵀ + R`, for a prior covariance
`Pi` and the covariance `R` of the observation noise. If the prior `Pir` is positive
semidefinite and below `Pi` in the Loewner order (`h`), and `R` is positive definite, the
analysis covariance of `Pir` is below that of `Pi`. No constants.

Source: the docstring names arXiv 2306.07774, Section 5, and arXiv 2602.06614, Section 3.1.2.

### 10.3 Control

@stmt LeanDLRA/Control/AdjointDLRA.lean abs_reducedGrad_sub_le AdjointDLRA.abs_reducedGrad_sub_le

The reduced gradient of a control problem in the form `(1/(N+1)) ∑ ⟪B (f k), g k⟫` with state
values `f k` and adjoint values `g k` (in the statement: `gg k`), compared with the same
expression for approximations `fr k`, `gr k`. The difference is bounded by the sum of
`‖f k - fr k‖ ‖gr k‖ + ‖f k‖ ‖gg k - gr k‖`, times `‖B‖ / (N + 1)`. There are no hypotheses: the
statement is an inequality for arbitrary sequences, and that the gradient has this form is not
part of it.

@stmt LeanDLRA/Control/AdjointDLRA.lean IsKSLStep.reverse_eq AdjointDLRA.IsKSLStep.reverse_eq

Reversal of a projector-splitting step in projector form (`IsKSLStep`): if the three substeps
are run backward in the reverse order, with the time-reversed field and the same projectors
`P₁`, `Q₀`, the result is the start value `Y₀`. The field is Lipschitz and jointly continuous
(`hF`, `hFc`), and `t₀ ≤ t₁`. The projectors are held fixed in this statement.

Source: for the first statement the module docstring of the file names arXiv 2506.21405,
Section 5, arXiv 2610.29554, Section 7, and arXiv 2409.14938, Section 5; for the second
statement the docstring names arXiv 2010.02022, Section 1, and arXiv 2608.21545, Section 3.

## 11. Results of single papers in the core

The modules of this part started as files of the catalogue of paper results and were promoted to
the core: their definitions are the core definitions or are proven equal to them
([STRUCTURE.md](STRUCTURE.md), paragraph "Promotion"). Each has the folder of its topic as a path.
The namespace of a theorem still names the paper (the arXiv number 2503.18271 gives the namespace
of `Literature.P2503_18271.tdb_velocity_gauge_free`); the statements below are quoted with it. The other promoted
modules of the same step are quoted in their topic sections:
@file(LeanDLRA/FixedRank/TangentStepTruncation.lean) in section 2.4,
@file(LeanDLRA/Matrix/LowRankDistanceFlow.lean) in section 6.8,
@file(LeanDLRA/Integrators/RankSelection.lean) and
@file(LeanDLRA/Integrators/RankAdaptiveBUGAposteriori.lean) in section 6.3,
@file(LeanDLRA/Training/ConvergenceRates.lean), @file(LeanDLRA/Training/FederatedFixedPoints.lean)
and @file(LeanDLRA/Training/ProjectorSplittingDescent.lean) in section 10.1.

### 11.1 Norm balance of one step

@stmt LeanDLRA/Stability/NormBalance.lean IsBUGStep.norm_sq_add_defect_sq_and_defect_le IsBUGStep.norm_sq_add_defect_sq_and_defect_le

@stmt LeanDLRA/Stability/NormBalance.lean IsKSLStep.norm_eq IsKSLStep.norm_eq

For a field with `⟪F t x, x⟫ = 0` the exact flow conserves the norm. The fixed-rank BUG step
loses exactly the projection defect of its start value: `‖YS t₁‖² + ‖Y₀ - P₁ (Q₁ Y₀)‖² = ‖Y₀‖²`,
and the defect is at most `2 B (t₁ - t₀)` for a field bounded by `B`. The projector-splitting
(KSL) step conserves the norm exactly if the projectors commute and `Q₀ Y₀ = Y₀`; the file also
has the energy `ℰ` for `F(t, x) = J ∇ℰ(x)` with skew `J` (`IsKSLStep.energy_eq_of_skew`) and
the statement that the untruncated parallel BUG step can only gain norm
(`IsParallelBUGStep.norm_sq_eq`). The theorems are for one step and for the step structures of
the core; they are not a statement on the whole run.

### 11.2 Gauge, interpolation, mixtures, Gramians, orthonormality

@stmt LeanDLRA/DLRA/GaugeInvariance.lean tdb_velocity_gauge_free Literature.P2503_18271.tdb_velocity_gauge_free

@stmt LeanDLRA/Randomized/CrossInterpolation.lean obliqueTangentProj_eq_of_mem_range Literature.P2402_18721.obliqueTangentProj_eq_of_mem_range

@stmt LeanDLRA/Kinetic/MaterialMixtureCollision.lean material_mixture_isLipschitz Literature.P2508_04484.material_mixture_isLipschitz

@stmt LeanDLRA/Stochastic/GramianLowerBound.lean projected_step_gram_lower_bound Literature.P2601_21428.projected_step_gram_lower_bound

@stmt LeanDLRA/Tensor/TTN/BasisOrthonormality.lean basis_transpose_mul_self_iff Literature.P2002_11392.basis_transpose_mul_self_iff

Five statements, one for each of five promoted modules.

*Gauge* (arXiv 2503.18271, Sections 2 and 3). Write the factor velocities with an arbitrary matrix
`A` (in `U̇`) and a skew matrix `B` (in `Ẏ`), both of size `r × r`. Then the velocity of the
product `U Σ Yᵀ` is the tangent-space projection `tangentProj U Y M` of the right-hand side `M`,
and the gauge terms cancel: the velocity does not depend on the gauge. The paper derives the
factor equations from the velocity condition; the theorem proves the converse direction (the
factor equations give the velocity), without assuming `Uᵀ U = 1` or `Yᵀ Y = 1`; `Σ` must be
invertible. `tdb_velocity_gauge_invariant` is the consequence that two gauge choices give the same
velocity.

*Interpolation* (arXiv 2402.18721, Eq. (5)). For selection matrices `S_U`, `S_V` of index sets
`I`, `J` with nonsingular `S_Uᵀ U` and `S_Vᵀ V`, the oblique tangent projector reproduces `Z` in
every row of `I` and every column of `J`. Orthonormality of `U`, `V` is not assumed.

*Mixtures* (arXiv 2508.04484). The collision field `u ↦ ∑ᵢ Dᵢ u Cᵢ + B(t)` for a finite family of
materials is Lipschitz in `u` with constant `L` if `∑ᵢ ‖Dᵢ‖ ‖Cᵢ‖ ≤ L` at every time. The constant is
derived in the file; the paper states no bound. The file also evaluates the field on the factors
(`material_mixture_factorized`) and shows that the collided L-step is a Galerkin projection
(`collided_L_step_galerkin`); the operation count of the paper is not formalized.

*Gramian bound* (arXiv 2601.21428, Propositions 5.2 and 6.2, first inequalities). For one step of
a projector-splitting scheme for stochastic low-rank approximation, the Gram matrix of the new
random modes `Ynext` satisfies `σ Δt (vᵀ v) ≤ vᵀ C v` for all `v`, where `σ` bounds the diffusion
from below. Three facts of the stochastic analysis are hypotheses (martingale orthogonality
`horth`, the Itô isometry `hiso`, the lower bound `hB`), because the library has no stochastic
calculus; only the non-strict inequality is proved, and the uniform-step bounds of the paper are
not.

*Orthonormality* (arXiv 2002.11392, Lemma 2.4). For a node of a valid dimension tree whose
children have orthonormal bases, the basis of the tree tensor network with connecting tensor `C`
is orthonormal if and only if `C Cᵀ = 1`. The module docstring lists where the other results of
the paper are in the library.

## 12. Citation keys

The keys in square brackets are entries of [`docs/references.bib`](references.bib), which gives
the authors, the title, the journal and the arXiv identifier of each paper.
`uv run -q scripts/docgen.py keys` lists the keys that the core and the pages of `docs/` use
and that have no entry. Where a docstring cites a paper by its arXiv number or by the names of
its authors, this page does the same.
