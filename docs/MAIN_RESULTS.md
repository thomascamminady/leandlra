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
files and were compared with them at commit 8a194f2 (2026-11-18). A theorem is quoted from its
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

`SVD.exists_svd` in [`LeanDLRA/Classical/SVD.lean`, lines 292–295](../LeanDLRA/Classical/SVD.lean#L292-L295):

```lean
theorem exists_svd (A : Matrix m n ℝ) {r : ℕ} (hr : A.rank = r) :
    ∃ (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (σ : Fin r → ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ Antitone σ ∧ (∀ i, 0 < σ i) ∧
      (∀ i, σ i = (toEuclideanLin A).singularValues i) ∧ A = U * diagonal σ * Vᵀ
```

A real matrix `A` of rank `r` is a product `U * diagonal σ * Vᵀ` in which `U` and `V` have `r`
orthonormal columns each and `σ` is a nonincreasing family of positive numbers. The numbers `σ i`
are the first `r` singular values of the linear map of `A` in the sense of Mathlib
(`(Matrix.toEuclideanLin A).singularValues i`). There are no constants. The hypothesis `hr` only
names the rank.

### 2.2 Best approximation of rank at most r (Eckart–Young–Mirsky)

`EckartYoung.truncation` in [`LeanDLRA/LinearAlgebra/SVD/Defs.lean`, lines 99–100](../LeanDLRA/LinearAlgebra/SVD/Defs.lean#L99-L100):

```lean
noncomputable def truncation (A : Matrix m n ℝ) (r : ℕ) : Matrix m n ℝ :=
  A * topRightSingularVectors A r * (topRightSingularVectors A r)ᵀ
```

`EckartYoung.rank_truncation_le` in [`LeanDLRA/Classical/EckartYoung.lean`, line 309](../LeanDLRA/Classical/EckartYoung.lean#L309):

```lean
theorem rank_truncation_le (A : Matrix m n ℝ) (r : ℕ) : (truncation A r).rank ≤ r
```

`EckartYoung.sum_sq_singularValues_le_sq_norm_sub` in [`LeanDLRA/Classical/EckartYoung.lean`, lines 397–398](../LeanDLRA/Classical/EckartYoung.lean#L397-L398):

```lean
theorem sum_sq_singularValues_le_sq_norm_sub (A B : Matrix m n ℝ) {r : ℕ} (hB : B.rank ≤ r) :
    ∑ i ∈ Ico r (Fintype.card n), (toEuclideanLin A).singularValues i ^ 2 ≤ ‖A - B‖ ^ 2
```

`EckartYoung.sq_norm_sub_truncation` in [`LeanDLRA/Classical/EckartYoung.lean`, lines 433–435](../LeanDLRA/Classical/EckartYoung.lean#L433-L435):

```lean
theorem sq_norm_sub_truncation (A : Matrix m n ℝ) (r : ℕ) :
    ‖A - truncation A r‖ ^ 2 =
      ∑ i ∈ Ico r (Fintype.card n), (toEuclideanLin A).singularValues i ^ 2
```

`EckartYoung.infDist_setOf_rank_le` in [`LeanDLRA/Classical/EckartYoung.lean`, lines 466–468](../LeanDLRA/Classical/EckartYoung.lean#L466-L468):

```lean
theorem infDist_setOf_rank_le (A : Matrix m n ℝ) (r : ℕ) :
    Metric.infDist A {B : Matrix m n ℝ | B.rank ≤ r} =
      √(∑ i ∈ Ico r (Fintype.card n), (toEuclideanLin A).singularValues i ^ 2)
```

The truncation of `A` to rank `r` is the product of `A` with the orthogonal projector onto the
span of its first `r` right singular vectors. It has rank at most `r`. Every matrix `B` of rank
at most `r` satisfies `‖A - B‖² ≥ ∑ σ_i(A)²`, the sum taken over the indices `i` from `r` to the
number of columns minus one, and the truncation attains this value. Hence the distance in the
Frobenius norm from `A` to the set of matrices of rank at most `r` is the square root of that
sum. The singular values are those of Mathlib, indexed from zero in nonincreasing order. There
are no hypotheses besides the rank bound on `B`.

Source: the docstrings name Schmidt (1907), Eckart and Young (1936) and Mirsky (1960).

### 2.3 The tangent projector of the fixed-rank matrices

`tangentProj` in [`LeanDLRA/FixedRank/Defs.lean`, lines 81–83](../LeanDLRA/FixedRank/Defs.lean#L81-L83):

```lean
noncomputable def tangentProj (U : Matrix m k ℝ) (V : Matrix n k' ℝ) :
    Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  tangent (leftProj U) (rightProj V)
```

`isOrthProj_tangentProj` in [`LeanDLRA/Matrix/Projectors.lean`, lines 195–197](../LeanDLRA/Matrix/Projectors.lean#L195-L197):

```lean
theorem isOrthProj_tangentProj [DecidableEq k] [DecidableEq k'] {U : Matrix m k ℝ}
    {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    IsOrthProj (tangentProj U V : Matrix m n ℝ →L[ℝ] Matrix m n ℝ)
```

For matrices `U` and `V`, `tangentProj U V` is the map `Z ↦ U Uᵀ Z + Z V Vᵀ - U Uᵀ Z V Vᵀ`
(`tangentProj_apply`). It is built from the left projector `leftProj U`, the right projector
`rightProj V` and the combination `tangent L R = L + R - L * R`. If `U` and `V` have orthonormal
columns (`hU`, `hV`), it is an orthogonal projector. For `Y = U S Vᵀ` with invertible `S` its
range is the tangent space at `Y` of the manifold of matrices of the rank of `Y`; the theorem
quoted here states only the projector property.

Source: [KochLubich2007, Lemma 4.1].

`tangentProjAt` in [`LeanDLRA/FixedRank/TangentSpace/Defs.lean`, lines 51–52](../LeanDLRA/FixedRank/TangentSpace/Defs.lean#L51-L52):

```lean
noncomputable def tangentProjAt (Y : Matrix m n ℝ) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  tangent (Frobenius.leftMulCLM Y.rangeProj) (Frobenius.rightMulCLM Yᵀ.rangeProj)
```

`tangentSpaceAt` in [`LeanDLRA/FixedRank/TangentSpace/Defs.lean`, lines 58–66](../LeanDLRA/FixedRank/TangentSpace/Defs.lean#L58-L66):

```lean
def tangentSpaceAt (Y : Matrix m n ℝ) : Submodule ℝ (Matrix m n ℝ) where
  carrier := {Z | ∃ (A : Matrix m m ℝ) (B : Matrix n n ℝ), Z = A * Y + Y * B}
  add_mem' := by
    rintro _ _ ⟨A, B, rfl⟩ ⟨A', B', rfl⟩
    exact ⟨A + A', B + B', by simp only [Matrix.add_mul, Matrix.mul_add]; abel⟩
  zero_mem' := ⟨0, 0, by simp⟩
  smul_mem' := by
    rintro c _ ⟨A, B, rfl⟩
    exact ⟨c • A, c • B, by simp [Matrix.smul_mul, Matrix.mul_smul, smul_add]⟩
```

`tangentProjAt_eq_starProjection` in [`LeanDLRA/FixedRank/TangentSpace.lean`, lines 122–123](../LeanDLRA/FixedRank/TangentSpace.lean#L122-L123):

```lean
theorem tangentProjAt_eq_starProjection (Y : Matrix m n ℝ) :
    tangentProjAt Y = (tangentSpaceAt Y).starProjection
```

`tangentProjAt_eq_tangentProj` in [`LeanDLRA/FixedRank/TangentSpace.lean`, lines 134–136](../LeanDLRA/FixedRank/TangentSpace.lean#L134-L136):

```lean
theorem tangentProjAt_eq_tangentProj [DecidableEq k] {U : Matrix m k ℝ} {S : Matrix k k ℝ}
    {V : Matrix n k ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S.det) :
    tangentProjAt (U * S * Vᵀ) = tangentProj U V
```

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

`Curvature.koch_lubich_tangent_frob` in [`LeanDLRA/Matrix/Curvature.lean`, lines 1182–1187](../LeanDLRA/Matrix/Curvature.lean#L1182-L1187):

```lean
theorem koch_lubich_tangent_frob {U U' : Matrix m k ℝ} {V V' : Matrix n k ℝ}
    {S S' : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) (B : Matrix m n ℝ) :
    ‖tangentProjMat (U' * U'ᵀ) (V' * V'ᵀ) B - tangentProjMat (U * Uᵀ) (V * Vᵀ) B‖ ≤
      2 * ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖B‖
```

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
[`FixedRank/TangentSpace/Curvature.lean`](../LeanDLRA/FixedRank/TangentSpace/Curvature.lean) states the same estimates for `tangentProjAt`. The lower bound `ρ` is now one for the `r`-th
singular value `σ_{r-1}(X)` of a matrix `X` of rank `r` (singular values `σ₀ ≥ σ₁ ≥ ⋯`,
indexed from zero as in Mathlib):

`norm_tangentProj_sub_tangentProjAt_le` in [`LeanDLRA/FixedRank/TangentSpace/Curvature.lean`, lines 59–63](../LeanDLRA/FixedRank/TangentSpace/Curvature.lean#L59-L63):

```lean
theorem norm_tangentProj_sub_tangentProjAt_le {r : ℕ} {X : Matrix m n ℝ} (hX : X.rank = r)
    {ρ : ℝ} (hρ : 0 < ρ) (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1))
    {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (S : Matrix (Fin r) (Fin r) ℝ) (B : Matrix m n ℝ) :
    ‖tangentProj U V B - tangentProjAt X B‖ ≤ 2 * ρ⁻¹ * ‖U * S * Vᵀ - X‖ * ‖B‖
```

`norm_tangentProjAt_sub_le` in [`LeanDLRA/FixedRank/TangentSpace/Curvature.lean`, lines 74–77](../LeanDLRA/FixedRank/TangentSpace/Curvature.lean#L74-L77):

```lean
theorem norm_tangentProjAt_sub_le {r : ℕ} {X Y : Matrix m n ℝ} (hX : X.rank = r)
    (hY : Y.rank = r) {ρ : ℝ} (hρ : 0 < ρ) (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1))
    (B : Matrix m n ℝ) :
    ‖tangentProjAt Y B - tangentProjAt X B‖ ≤ 2 * ρ⁻¹ * ‖Y - X‖ * ‖B‖
```

The first theorem compares the projector of orthonormal factors `U`, `V` with the projector at
the matrix `X`; the core `S` may be any matrix, invertible or not. The second is the Lipschitz
bound of `Y ↦ tangentProjAt Y` between matrices of rank `r`. In both, the lower bound is needed
at one of the two points only, and there is no smallness condition on `‖Y - X‖`.

`mem_tangentSpaceAt_of_hasDerivWithinAt` in [`LeanDLRA/FixedRank/TangentSpace/Curvature.lean`, lines 139–143](../LeanDLRA/FixedRank/TangentSpace/Curvature.lean#L139-L143):

```lean
theorem mem_tangentSpaceAt_of_hasDerivWithinAt {r : ℕ} {X : ℝ → Matrix m n ℝ}
    {X' : Matrix m n ℝ} {s : Set ℝ} {t ρ : ℝ} (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s)
    (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ) (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ : ∀ u ∈ s, ρ ≤ (toEuclideanLin (X u)).singularValues (r - 1)) :
    X' ∈ tangentSpaceAt (X t)
```

`tangentProjAt_sub_eq_zero_of_forall_norm_sub_le` in [`LeanDLRA/FixedRank/TangentSpace/Curvature.lean`, lines 166–168](../LeanDLRA/FixedRank/TangentSpace/Curvature.lean#L166-L168):

```lean
theorem tangentProjAt_sub_eq_zero_of_forall_norm_sub_le {r : ℕ} {A X : Matrix m n ℝ}
    (hX : X.rank ≤ r) (hbest : ∀ Z : Matrix m n ℝ, Z.rank ≤ r → ‖A - X‖ ≤ ‖A - Z‖) :
    tangentProjAt X (A - X) = 0
```

`tangentProjAt_truncation_sub_eq_zero` in [`LeanDLRA/FixedRank/TangentSpace/Curvature.lean`, lines 204–205](../LeanDLRA/FixedRank/TangentSpace/Curvature.lean#L204-L205):

```lean
theorem tangentProjAt_truncation_sub_eq_zero (A : Matrix m n ℝ) (r : ℕ) :
    tangentProjAt (EckartYoung.truncation A r) (A - EckartYoung.truncation A r) = 0
```

The derivative of a curve of matrices of rank `r` with `σ_{r-1} ≥ ρ > 0` lies in the tangent
space at the curve (`s` is a set of times such as `Set.Ici t`, so the derivative may be a right
derivative). A best approximation `X` of `A` among the matrices of rank at most `r`
(`hbest`) satisfies the first-order condition `P(X) (A - X) = 0`, and so does the truncated
singular value decomposition. The proof of the second uses the curve `(1 + ε M) X (1 + ε N)`,
whose velocity at `ε = 0` is the tangent vector `M X + X N`; no factorization of `X` is chosen.
The module docstring also has `norm_one_sub_tangentProjAt_apply_sub_le`,
`‖(1 - P(Y)) (Y - X)‖ ≤ ρ⁻¹ ‖Y - X‖²`, which is not quoted here.

Source: the module docstring cites [KochLubich2007, §2 and Lemma 4.2].

`tailNorm_add_tangent_le` in [`LeanDLRA/FixedRank/TangentStepTruncation.lean`, lines 119–123](../LeanDLRA/FixedRank/TangentStepTruncation.lean#L119-L123):

```lean
theorem tailNorm_add_tangent_le {r : ℕ} {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
    {S : Matrix (Fin r) (Fin r) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {ρ : ℝ} (hρ : 0 < ρ)
    (hS : ρ ≤ (toEuclideanLin S).singularValues (r - 1)) {Z : Matrix m n ℝ}
    (hZ : (1 - U * Uᵀ) * Z * (1 - V * Vᵀ) = 0) (hZρ : ‖Z‖ ≤ ρ / 2) :
    WeylSingular.tailNorm (U * S * Vᵀ + Z) r ≤ ‖Z‖ ^ 2 / ρ
```

An explicit step along a tangent direction leaves the matrices of rank at most `r`, but only to
second order. Let `X = U S Vᵀ` with orthonormal `U`, `V` and `ρ ≤ σ_{r-1}(S)`, and let `Z` be a
tangent matrix at `X`, `(1 - U Uᵀ) Z (1 - V Vᵀ) = 0`, with `‖Z‖ ≤ ρ / 2`. Then the Frobenius norm
of the singular values of `X + Z` beyond the first `r`, which is the distance of `X + Z` to the
matrices of rank at most `r` (`WeylSingular.tailNorm_eq_infDist`), is at most `‖Z‖² / ρ`. The
constant contains the lower bound `ρ`; the bound concerns one tangent step of a given size.

Source: the module docstring cites arXiv 2111.14540, Sections 6 and 7 (retraction of a tangent
step by the truncated singular value decomposition).

**The constant 1.** The constant `2` of the two theorems above can be replaced by `1`. The file
[`FixedRank/TangentSpace/ProjectorLipschitz.lean`](../LeanDLRA/FixedRank/TangentSpace/ProjectorLipschitz.lean) proves the Lipschitz bound with
`1`, first for factors and then at a matrix:

`Curvature.norm_tangentProjMat_sub_le_inv_mul` in [`LeanDLRA/FixedRank/TangentSpace/ProjectorLipschitz.lean`, lines 411–416](../LeanDLRA/FixedRank/TangentSpace/ProjectorLipschitz.lean#L411-L416):

```lean
theorem norm_tangentProjMat_sub_le_inv_mul {U U' : Matrix m k ℝ} {V V' : Matrix n k ℝ}
    {S S' : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) (B : Matrix m n ℝ) :
    ‖tangentProjMat (U' * U'ᵀ) (V' * V'ᵀ) B - tangentProjMat (U * Uᵀ) (V * Vᵀ) B‖ ≤
      ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖B‖
```

`norm_tangentProjAt_sub_le_inv_mul` in [`LeanDLRA/FixedRank/TangentSpace/ProjectorLipschitz.lean`, lines 579–582](../LeanDLRA/FixedRank/TangentSpace/ProjectorLipschitz.lean#L579-L582):

```lean
theorem norm_tangentProjAt_sub_le_inv_mul {r : ℕ} {X Y : Matrix m n ℝ} (hX : X.rank = r)
    (hY : Y.rank = r) {ρ : ℝ} (hρ : 0 < ρ) (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1))
    (B : Matrix m n ℝ) :
    ‖tangentProjAt Y B - tangentProjAt X B‖ ≤ ρ⁻¹ * ‖Y - X‖ * ‖B‖
```

The hypotheses are those of `Curvature.koch_lubich_tangent_frob`, and of `norm_tangentProjAt_sub_le`
in the second statement: `X` and `Y` have rank `r`, and the lower bound `ρ` is needed at `X`
only. There is no smallness condition on `‖Y - X‖`; all norms are Frobenius norms. The proof
splits `P(Y) B - P(X) B` into the orthogonal pieces `P(Y) (1 - P(X)) B` and
`-(1 - P(Y)) P(X) B`, and bounds each by `ρ⁻¹ ‖Y - X‖` times the norm of the vector it is applied
to. The two bounds on normal vectors are

`norm_tangentProjAt_apply_le_of_tangentProjAt_eq_zero` in [`LeanDLRA/FixedRank/TangentSpace/ProjectorLipschitz.lean`, lines 567–571](../LeanDLRA/FixedRank/TangentSpace/ProjectorLipschitz.lean#L567-L571):

```lean
theorem norm_tangentProjAt_apply_le_of_tangentProjAt_eq_zero {r : ℕ} {X Y : Matrix m n ℝ}
    (hX : X.rank = r) (hY : Y.rank = r) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) {N : Matrix m n ℝ}
    (hN : tangentProjAt Y N = 0) :
    ‖tangentProjAt X N‖ ≤ ρ⁻¹ * ‖Y - X‖ * ‖N‖
```

`norm_tangentProj_apply_le_of_tangentProjAt_eq_zero` in [`LeanDLRA/FixedRank/TangentSpace/ProjectorLipschitz.lean`, lines 521–525](../LeanDLRA/FixedRank/TangentSpace/ProjectorLipschitz.lean#L521-L525):

```lean
theorem norm_tangentProj_apply_le_of_tangentProjAt_eq_zero {r : ℕ} {X : Matrix m n ℝ}
    (hX : X.rank = r) {ρ : ℝ} (hρ : 0 < ρ) (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1))
    {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (S : Matrix (Fin r) (Fin r) ℝ) {N : Matrix m n ℝ} (hN : tangentProjAt X N = 0) :
    ‖tangentProj U V N‖ ≤ ρ⁻¹ * ‖U * S * Vᵀ - X‖ * ‖N‖
```

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
[`FixedRank/TangentSpace/ProjectorSpectral.lean`](../LeanDLRA/FixedRank/TangentSpace/ProjectorSpectral.lean) bounds `‖P(X) N‖` by the spectral
norm `‖N‖₂ = specNorm N` of the normal vector `N` (`P(Y) N = 0`); `‖P(X) N‖` and `‖Y - X‖` stay
Frobenius norms:

`norm_tangentProjAt_apply_le_one_add_mul_specNorm_of_tangentProjAt_eq_zero` in [`LeanDLRA/FixedRank/TangentSpace/ProjectorSpectral.lean`, lines 355–360](../LeanDLRA/FixedRank/TangentSpace/ProjectorSpectral.lean#L355-L360):

```lean
theorem norm_tangentProjAt_apply_le_one_add_mul_specNorm_of_tangentProjAt_eq_zero {r : ℕ}
    {X Y : Matrix m n ℝ} (hX : X.rank = r) (hY : Y.rank = r) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) {N : Matrix m n ℝ}
    (hN : tangentProjAt Y N = 0) :
    ‖tangentProjAt X N‖ ≤
      ρ⁻¹ * ‖Y - X‖ * (1 + ρ⁻¹ * ‖Y - X‖) * Curvature.specNorm N
```

`norm_tangentProjAt_apply_le_sqrt_two_mul_specNorm_of_tangentProjAt_eq_zero` in [`LeanDLRA/FixedRank/TangentSpace/ProjectorSpectral.lean`, lines 377–381](../LeanDLRA/FixedRank/TangentSpace/ProjectorSpectral.lean#L377-L381):

```lean
theorem norm_tangentProjAt_apply_le_sqrt_two_mul_specNorm_of_tangentProjAt_eq_zero {r : ℕ}
    {X Y : Matrix m n ℝ} (hX : X.rank = r) (hY : Y.rank = r) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) {N : Matrix m n ℝ}
    (hN : tangentProjAt Y N = 0) :
    ‖tangentProjAt X N‖ ≤ Real.sqrt 2 * ρ⁻¹ * ‖Y - X‖ * Curvature.specNorm N
```

The factor in the first bound is `1` to first order in `‖Y - X‖`, and it is the bound that the
derivative of the first-order condition of section 3.7 needs. In the second bound the constant is
`√2` for all `Y`. The two constants are not those of section 2.4: the module docstring says that
the bound with the constant `1` and `‖N‖₂` does not hold, with a family of examples in which the
quotient `‖P(X) N‖² / ‖Y - X‖²` tends to `2`; this family is not formalized in the core. The
squared form with the factor `1 + (ρ⁻¹ ‖Y - X‖)²` and the factor-level bounds are in the file.

### 2.5 Separation rank and the fixed-rank set

`lowRankSet` in [`LeanDLRA/LinearAlgebra/LowRank/Defs.lean`, line 83](../LeanDLRA/LinearAlgebra/LowRank/Defs.lean#L83):

```lean
def lowRankSet (m n : Type*) [Fintype n] (r : ℕ) : Set (Matrix m n ℝ) := {Y | Y.rank ≤ r}
```

`HasSepRankLE` in [`LeanDLRA/LinearAlgebra/LowRank/SepRank.lean`, lines 64–65](../LeanDLRA/LinearAlgebra/LowRank/SepRank.lean#L64-L65):

```lean
def HasSepRankLE (R : Type*) [Semiring R] (f : X → Y → R) (r : ℕ) : Prop :=
  ∃ (U : Fin r → X → R) (V : Fin r → Y → R), ∀ x y, f x y = ∑ k, U k x * V k y
```

`HasSepRankLE.rank_le` in [`LeanDLRA/LinearAlgebra/LowRank/SepRank.lean`, lines 91–93](../LeanDLRA/LinearAlgebra/LowRank/SepRank.lean#L91-L93):

```lean
theorem HasSepRankLE.rank_le [CommRing R] [StrongRankCondition R] {p q : Type*} [Finite p]
    [Fintype q] {f : X → Y → R} {r : ℕ} (h : HasSepRankLE R f r) (xs : p → X) (ys : q → Y) :
    (Matrix.of fun i j => f (xs i) (ys j)).rank ≤ r
```

`hasSepRankLE_iff_rank_le` in [`LeanDLRA/LinearAlgebra/LowRank/SepRank.lean`, lines 125–126](../LeanDLRA/LinearAlgebra/LowRank/SepRank.lean#L125-L126):

```lean
theorem hasSepRankLE_iff_rank_le {m n K : Type*} [Finite m] [Fintype n] [Field K]
    (f : m → n → K) (r : ℕ) : HasSepRankLE K f r ↔ (Matrix.of f).rank ≤ r
```

`hasSepRankLE_iff_mem_lowRankSet` in [`LeanDLRA/LinearAlgebra/LowRank/SepRank.lean`, lines 131–132](../LeanDLRA/LinearAlgebra/LowRank/SepRank.lean#L131-L132):

```lean
theorem hasSepRankLE_iff_mem_lowRankSet {m n : Type*} [Finite m] [Fintype n]
    (A : Matrix m n ℝ) (r : ℕ) : HasSepRankLE ℝ (fun i j => A i j) r ↔ A ∈ lowRankSet m n r
```

`fixedRankSet` in [`LeanDLRA/LinearAlgebra/LowRank/SepRank.lean`, line 161](../LeanDLRA/LinearAlgebra/LowRank/SepRank.lean#L161):

```lean
def fixedRankSet (m n : Type*) [Fintype n] (r : ℕ) : Set (Matrix m n ℝ) := {Y | Y.rank = r}
```

`mem_lowRankSet_iff_exists_mem_fixedRankSet` in [`LeanDLRA/LinearAlgebra/LowRank/SepRank.lean`, lines 172–173](../LeanDLRA/LinearAlgebra/LowRank/SepRank.lean#L172-L173):

```lean
theorem mem_lowRankSet_iff_exists_mem_fixedRankSet {Y : Matrix m n ℝ} :
    Y ∈ lowRankSet m n r ↔ ∃ s ≤ r, Y ∈ fixedRankSet m n s
```

`mem_fixedRankSet_of_factor` in [`LeanDLRA/LinearAlgebra/LowRank/SepRank.lean`, lines 178–180](../LeanDLRA/LinearAlgebra/LowRank/SepRank.lean#L178-L180):

```lean
theorem mem_fixedRankSet_of_factor {k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    {U : Matrix m k ℝ} {S : Matrix k k ℝ} {V : Matrix n k ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hS : IsUnit S) : U * S * Vᵀ ∈ fixedRankSet m n (Fintype.card k)
```

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

`LinearMap.le_singularValues_of_mul_norm_le` in [`LeanDLRA/LinearAlgebra/SVD/MinMax.lean`, lines 40–42](../LeanDLRA/LinearAlgebra/SVD/MinMax.lean#L40-L42):

```lean
theorem le_singularValues_of_mul_norm_le (T : E →ₗ[𝕜] F) {W : Submodule 𝕜 E} {k : ℕ}
    (hW : k + 1 ≤ finrank 𝕜 W) {ρ : ℝ} (hρ : ∀ y ∈ W, ρ * ‖y‖ ≤ ‖T y‖) :
    ρ ≤ T.singularValues k
```

`SVD.le_singularValues_of_eq_mul` in [`LeanDLRA/LinearAlgebra/SVD/MinMax.lean`, lines 70–74](../LeanDLRA/LinearAlgebra/SVD/MinMax.lean#L70-L74):

```lean
theorem SVD.le_singularValues_of_eq_mul {r : ℕ} (hr : 0 < r) {X : Matrix m n ℝ}
    {U : Matrix m (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hX : X = U * S * Vᵀ) {ρ : ℝ}
    (hS : ∀ w, ρ * ‖w‖ ≤ ‖toEuclideanLin S w‖) :
    ρ ≤ (toEuclideanLin X).singularValues (r - 1)
```

`EckartYoung.truncation_eq_self` in [`LeanDLRA/LinearAlgebra/SVD/MinMax.lean`, lines 93–94](../LeanDLRA/LinearAlgebra/SVD/MinMax.lean#L93-L94):

```lean
theorem EckartYoung.truncation_eq_self {r : ℕ} {A : Matrix m n ℝ} (hA : A.rank ≤ r) :
    EckartYoung.truncation A r = A
```

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

`norm_sub_le_of_isOrthProjMat` in [`LeanDLRA/LinearAlgebra/SVD/TruncationDeriv.lean`, lines 239–247](../LeanDLRA/LinearAlgebra/SVD/TruncationDeriv.lean#L239-L247):

```lean
theorem norm_sub_le_of_isOrthProjMat {A B : Matrix m n ℝ} {P P' : Matrix n n ℝ}
    {α β α' β' : ℝ} (hP : IsOrthProjMat P) (hP' : IsOrthProjMat P')
    (hPc : Aᵀ * A * P = P * (Aᵀ * A)) (hP'c : Bᵀ * B * P' = P' * (Bᵀ * B))
    (hα : ∀ Z : Matrix n n ℝ, P * Z = Z → α * ‖Z‖ ≤ ‖A * Z‖)
    (hβ : ∀ Z : Matrix n n ℝ, P * Z = 0 → ‖A * Z‖ ≤ β * ‖Z‖)
    (hα' : ∀ Z : Matrix n n ℝ, P' * Z = Z → α' * ‖Z‖ ≤ ‖B * Z‖)
    (hβ' : ∀ Z : Matrix n n ℝ, P' * Z = 0 → ‖B * Z‖ ≤ β' * ‖Z‖) (hβ0 : 0 ≤ β) (hβ'0 : 0 ≤ β')
    (hβα' : β < α') (hβ'α : β' < α) :
    ‖P' - P‖ ≤ ‖Bᵀ * B - Aᵀ * A‖ * (1 / (α' ^ 2 - β ^ 2) + 1 / (α ^ 2 - β' ^ 2))
```

`EckartYoung.hasFDerivAt_truncation` in [`LeanDLRA/LinearAlgebra/SVD/TruncationDeriv.lean`, lines 549–553](../LeanDLRA/LinearAlgebra/SVD/TruncationDeriv.lean#L549-L553):

```lean
theorem EckartYoung.hasFDerivAt_truncation {A : Matrix m n ℝ} {r : ℕ}
    (hgap : (toEuclideanLin A).singularValues r < (toEuclideanLin A).singularValues (r - 1)) :
    ∃ L : Matrix m n ℝ →L[ℝ] Matrix m n ℝ, HasFDerivAt (fun B => truncation B r) L A ∧
      ∀ H, ‖L H‖ ≤ (1 + 4 * ‖A‖ ^ 2 / ((toEuclideanLin A).singularValues (r - 1) ^ 2 -
        (toEuclideanLin A).singularValues r ^ 2)) * ‖H‖
```

`EckartYoung.hasDerivWithinAt_truncation` in [`LeanDLRA/LinearAlgebra/SVD/TruncationDeriv.lean`, lines 734–739](../LeanDLRA/LinearAlgebra/SVD/TruncationDeriv.lean#L734-L739):

```lean
theorem EckartYoung.hasDerivWithinAt_truncation {A : ℝ → Matrix m n ℝ} {A' : Matrix m n ℝ}
    {s : Set ℝ} {t : ℝ} {r : ℕ} (hA : HasDerivWithinAt A A' s t)
    (hgap : (toEuclideanLin (A t)).singularValues r <
      (toEuclideanLin (A t)).singularValues (r - 1)) :
    HasDerivWithinAt (fun u => truncation (A u) r)
      (fderiv ℝ (fun B => truncation B r) (A t) A') s t
```

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

`SinTheta.wedin_frobenius` in [`LeanDLRA/LinearAlgebra/SVD/SinTheta.lean`, lines 258–262](../LeanDLRA/LinearAlgebra/SVD/SinTheta.lean#L258-L262):

```lean
theorem wedin_frobenius (A B : Matrix m n ℝ) (r : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : (toEuclideanLin A).singularValues (r + 1) + δ ≤
      (toEuclideanLin B).singularValues r) :
    ‖(1 - topRightSingularVectors A (r + 1) * (topRightSingularVectors A (r + 1))ᵀ) *
        topRightSingularVectors B (r + 1)‖ ≤ √2 * ‖B - A‖ / δ
```

`SinTheta.norm_truncation_sub_le_of_gap` in [`LeanDLRA/LinearAlgebra/SVD/SinTheta.lean`, lines 355–360](../LeanDLRA/LinearAlgebra/SVD/SinTheta.lean#L355-L360):

```lean
theorem norm_truncation_sub_le_of_gap (A B : Matrix m n ℝ) (r : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : (toEuclideanLin A).singularValues (r + 1) + δ ≤
      (toEuclideanLin B).singularValues r) :
    ‖truncation B (r + 1) - truncation A (r + 1)‖ ≤
      (1 + √2 * ((toEuclideanLin A).singularValues 0 +
        (toEuclideanLin A).singularValues (r + 1)) / δ) * ‖B - A‖
```

`SinTheta.davisKahan` in [`LeanDLRA/LinearAlgebra/SVD/SinTheta.lean`, lines 470–476](../LeanDLRA/LinearAlgebra/SVD/SinTheta.lean#L470-L476):

```lean
theorem davisKahan {d r : ℕ} (hn : finrank ℝ E = d) {T T' : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hT' : T'.IsSymmetric) {ε δ : ℝ} (hδ : 0 < δ) (hε : ∀ x, ‖T' x - T x‖ ≤ ε * ‖x‖)
    (hr : r + 1 < d)
    (hgap : hT.eigenvalues hn ⟨r + 1, hr⟩ + δ ≤ hT'.eigenvalues hn ⟨r, by omega⟩) {x : E}
    (hx : x ∈ Submodule.span ℝ (hT'.eigenvectorBasis hn '' {i | (i : ℕ) ≤ r})) :
    ∑ j ∈ univ.filter (fun j : Fin d ↦ r < (j : ℕ)), ⟪hT.eigenvectorBasis hn j, x⟫ ^ 2 ≤
      (ε * ‖x‖ / δ) ^ 2
```

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

`ODESolution` in [`LeanDLRA/Analysis/Defs.lean`, lines 85–89](../LeanDLRA/Analysis/Defs.lean#L85-L89):

```lean
structure ODESolution (f : ℝ → E → E) (y : ℝ → E) (a b : ℝ) : Prop where
  /-- `y` is continuous on `[a, b]`. -/
  cont : ContinuousOn y (Icc a b)
  /-- `y` has right derivative `f t (y t)` at every `t ∈ [a, b)`. -/
  deriv : ∀ t ∈ Ico a b, HasDerivWithinAt y (f t (y t)) (Ici t) t
```

`IsLipschitzField` in [`LeanDLRA/Analysis/Defs.lean`, lines 92–93](../LeanDLRA/Analysis/Defs.lean#L92-L93):

```lean
def IsLipschitzField (f : ℝ → E → E) (L : ℝ) : Prop :=
  ∀ t x y, ‖f t x - f t y‖ ≤ L * ‖x - y‖
```

`IsBoundedField` in [`LeanDLRA/Analysis/Defs.lean`, lines 96–97](../LeanDLRA/Analysis/Defs.lean#L96-L97):

```lean
def IsBoundedField (f : ℝ → E → E) (B : ℝ) : Prop :=
  ∀ t x, ‖f t x‖ ≤ B
```

`tubeSet` in [`LeanDLRA/Analysis/Defs.lean`, lines 156–157](../LeanDLRA/Analysis/Defs.lean#L156-L157):

```lean
def tubeSet (A : ℝ → E) (a b ρ : ℝ) : Set (ℝ × E) :=
  {p | p.1 ∈ Icc a b ∧ ‖p.2 - A p.1‖ ≤ ρ}
```

These are the definitions behind the terms "solution", "Lipschitz constant", "bound" and "tube"
of section 1. `IsLipschitzField` and `IsBoundedField` are global: they speak about all times and
all states. Their forms on a tube are `IsLipschitzOnTube` and `IsBoundedOnTube`.

`exists_ODESolution` in [`LeanDLRA/Foundations/Existence.lean`, lines 170–172](../LeanDLRA/Foundations/Existence.lean#L170-L172):

```lean
theorem exists_ODESolution (hL : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) {a b : ℝ} (hab : a ≤ b) (y₀ : E) :
    ∃ y : ℝ → E, ODESolution F y a b ∧ y a = y₀
```

Existence of solutions (Picard–Lindelöf): if the field is globally Lipschitz in the state (`hL`),
bounded (`hB`) and continuous in time for every fixed state (`hcont`), then for every interval
`[a, b]` and every start value `y₀` there is a solution on `[a, b]` with `y a = y₀`. The space
`E` has to be complete. No constant appears in the conclusion.

### 3.2 The bundle `DLRAProblem`

`DLRAProblem` in [`LeanDLRA/DLRA/Defs.lean`, lines 69–79](../LeanDLRA/DLRA/Defs.lean#L69-L79):

```lean
structure DLRAProblem (F : ℝ → E → E) (A : ℝ → E) (a b ρ L B : ℝ) : Prop where
  /-- `A` solves `y' = F(t, y)` on `[a, b]`. -/
  sol : ODESolution F A a b
  /-- The Lipschitz constant is nonnegative. -/
  L_nonneg : 0 ≤ L
  /-- The bound is nonnegative. -/
  B_nonneg : 0 ≤ B
  /-- `F` is `L`-Lipschitz in the state on the tube of radius `ρ` around `A`. -/
  lipschitz : IsLipschitzOnTube F A a b ρ L
  /-- `F` is bounded by `B` on the tube of radius `ρ` around `A`. -/
  bounded : IsBoundedOnTube F A a b ρ B
```

`DLRAProblem.of_global` in [`LeanDLRA/DLRA/Defs.lean`, lines 86–87](../LeanDLRA/DLRA/Defs.lean#L86-L87):

```lean
theorem DLRAProblem.of_global (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hA : ODESolution F A a b) (ρ : ℝ) : DLRAProblem F A a b ρ L B
```

`DLRAProblem F A a b ρ L B` collects the standing assumptions of the error analysis: `A` is a
solution of `Y' = F(t, Y)` on `[a, b]`, the constants `L` and `B` are nonnegative, and on the
tube of radius `ρ` around `A` the field is `L`-Lipschitz and bounded by `B`. Nothing is assumed
outside the tube. The constants are arguments of the structure, so that they can appear in the
conclusions of theorems. `DLRAProblem.of_global` builds the bundle, for every radius, from a
field that is Lipschitz and bounded everywhere.

Source: the assumptions on a tube are those of [ZhaoOstermannGu2021, Property 1(b)]; the global
ones are the standing assumptions of [CerutiLubich2022] and [KieriLubichWalach2016].

`DLRAProblem.tubeExt` in [`LeanDLRA/Integrators/Tube.lean`, lines 116–119](../LeanDLRA/Integrators/Tube.lean#L116-L119):

```lean
theorem DLRAProblem.tubeExt {a b ρ L B : ℝ} (hP : DLRAProblem F A a b ρ L B) (hρ : 0 ≤ ρ) :
    IsLipschitzField (LeanDLRA.tubeExt F A a b ρ) L ∧
      IsBoundedField (LeanDLRA.tubeExt F A a b ρ) B ∧
      ODESolution (LeanDLRA.tubeExt F A a b ρ) A a b
```

The extension of the field from the tube. `tubeExt F A a b ρ` is the field that evaluates `F` at
the nearest point of the ball of radius `ρ` around `A t` for `t` in `[a, b]`, and is zero for
other times. Under a `DLRAProblem` with `0 ≤ ρ` this field is globally `L`-Lipschitz, globally
bounded by `B`, and has the same exact solution `A`. It agrees with `F` on the tube
(`tubeExt_eq`). This is the device by which theorems for global assumptions are applied to
fields that satisfy them only near the exact solution. The constants `L` and `B` do not change.

### 3.3 The normal component

`NormalBoundOn` in [`LeanDLRA/DLRA/Defs.lean`, lines 165–167](../LeanDLRA/DLRA/Defs.lean#L165-L167):

```lean
def NormalBoundOn (F : ℝ → E → E) (𝒯 : Set ((E →L[ℝ] E) × (E →L[ℝ] E) × E))
    (D : Set (ℝ × E)) (ε : ℝ) : Prop :=
  ∀ t P Q Y, (P, Q, Y) ∈ 𝒯 → (t, Y) ∈ D → ‖(1 - P) ((1 - Q) (F t Y))‖ ≤ ε
```

`FactoredNormalBoundOn` in [`LeanDLRA/Integrators/Matrix/Defs.lean`, lines 141–145](../LeanDLRA/Integrators/Matrix/Defs.lean#L141-L145):

```lean
def FactoredNormalBoundOn (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ)
    (D : Set (ℝ × Matrix m n ℝ)) (ε : ℝ) : Prop :=
  ∀ t (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ),
    Uᵀ * U = 1 → Vᵀ * V = 1 → (t, U * S * Vᵀ) ∈ D →
      ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε
```

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

`ODESolution.dlra_norm_sub_le_gronwallBound` in [`LeanDLRA/Dynamics/ContinuousDLRA.lean`, lines 255–258](../LeanDLRA/Dynamics/ContinuousDLRA.lean#L255-L258):

```lean
theorem dlra_norm_sub_le_gronwallBound {L : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hA : ODESolution F A a b) (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hε : ∀ t ∈ Ico a b, ‖(1 - P t) (F t (Y t))‖ ≤ ε) (hδ : ‖Y a - A a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ gronwallBound δ L ε (t - a)
```

The error of the time-continuous approximation. Let `F` be `L`-Lipschitz with `0 ≤ L`, let `A`
solve `A' = F(t, A)` and let `Y` solve the projected equation `Y' = P(t) F(t, Y)` on `[a, b]`,
where `P t` is any family of continuous linear maps. If the neglected part `(1 - P t) F(t, Y t)`
has norm at most `ε` along `Y` (`hε`) and the initial error is at most `δ` (`hδ`), then
`‖Y t - A t‖ ≤ gronwallBound δ L ε (t - a)` on `[a, b]`. `gronwallBound` is the function of
Mathlib; for `L ≠ 0` its value is `δ e^{L(t-a)} + ε (e^{L(t-a)} - 1) / L`. The constants are `L`,
`ε` and `δ` only; no singular value and no property of the maps `P t` enters.

Source: Kieri, Lubich and Walach 2016 [KieriLubichWalach2016]; Carrel, Gander and Vandereycken,
arXiv 2203.08455, Theorem 2.3, as cited in the docstring.

`dlra_norm_sub_truncation_le_integral` in [`LeanDLRA/DLRA/QuasiOptimality.lean`, lines 537–548](../LeanDLRA/DLRA/QuasiOptimality.lean#L537-L548):

```lean
theorem dlra_norm_sub_truncation_le_integral {r : ℕ} (hr : 0 < r)
    {A A' X X' Y : ℝ → Matrix m n ℝ} {T μ ρ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ t ∈ Icc 0 T, HasDerivAt A (A' t) t)
    (hμ : ∀ t ∈ Icc 0 T, ‖A' t‖ ≤ μ) (hXbest : ∀ t ∈ Icc 0 T, X t = truncation (A t) r)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (X' t) t)
    (hσ : ∀ t ∈ Icc 0 T, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1))
    (hd : ∀ t ∈ Icc 0 T, ‖X t - A t‖ ≤ ρ / 16)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc 0 T, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t _ => tangentProj (U t) (V t) (A' t)) Y 0 T) (hY₀ : Y 0 = X 0) :
    ∀ t ∈ Icc 0 T, ‖Y t - X t‖ ≤
      2 * (8 * μ / ρ) * Real.exp (8 * μ / ρ * t) * ∫ s in (0 : ℝ)..t, ‖X s - A s‖
```

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

`IsDLRASolution` in [`LeanDLRA/DLRA/Defs.lean`, lines 218–220](../LeanDLRA/DLRA/Defs.lean#L218-L220):

```lean
def IsDLRASolution (r : ℕ) (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (Y : ℝ → Matrix m n ℝ)
    (a b : ℝ) : Prop :=
  ODESolution (fun t x => tangentProjAt x (F t x)) Y a b ∧ ∀ t ∈ Icc a b, (Y t).rank = r
```

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

`DynamicallyOrthogonal.isDLRASolution_iff_hasDerivWithinAt` in [`LeanDLRA/DLRA/DynamicallyOrthogonal.lean`, lines 251–258](../LeanDLRA/DLRA/DynamicallyOrthogonal.lean#L251-L258):

```lean
theorem isDLRASolution_iff_hasDerivWithinAt {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {a b : ℝ} {U : ℝ → Matrix m (Fin r) ℝ} {Z : ℝ → Matrix n (Fin r) ℝ}
    (hUG : ∀ t ∈ Icc a b, IsUnit ((U t)ᵀ * U t).det)
    (hZG : ∀ t ∈ Icc a b, IsUnit ((Z t)ᵀ * Z t).det) :
    IsDLRASolution r F (fun t => U t * (Z t)ᵀ) a b ↔
      ContinuousOn (fun t => U t * (Z t)ᵀ) (Icc a b) ∧ ∀ t ∈ Ico a b,
        HasDerivWithinAt (fun t => U t * (Z t)ᵀ)
          (tangentProjAt (U t * (Z t)ᵀ) (F t (U t * (Z t)ᵀ))) (Ici t) t
```

If `U t` and `Z t` have full column rank on `[a, b]`, then `U Zᵀ` is a DLRA solution of rank `r`
if and only if it is continuous on `[a, b]` and has the right derivative
`tangentProjAt (U Zᵀ) (F t (U Zᵀ))` on `[a, b)`: the rank condition is automatic for factors of
full rank.

`DynamicallyOrthogonal.doSystem_iff_isDLRASolution` in [`LeanDLRA/DLRA/DynamicallyOrthogonal.lean`, lines 313–321](../LeanDLRA/DLRA/DynamicallyOrthogonal.lean#L313-L321):

```lean
theorem doSystem_iff_isDLRASolution [DecidableEq m] {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {a b : ℝ} {U U' : ℝ → Matrix m (Fin r) ℝ}
    {Z Z' : ℝ → Matrix n (Fin r) ℝ} (hUc : ContinuousOn U (Icc a b))
    (hZc : ContinuousOn Z (Icc a b)) (hU : ∀ t ∈ Ico a b, HasDerivWithinAt U (U' t) (Ici t) t)
    (hZ : ∀ t ∈ Ico a b, HasDerivWithinAt Z (Z' t) (Ici t) t)
    (hUo : ∀ t ∈ Icc a b, (U t)ᵀ * U t = 1) (hG : ∀ t ∈ Icc a b, IsUnit ((Z t)ᵀ * Z t).det) :
    (∀ t ∈ Ico a b, (U t)ᵀ * U' t = 0 ∧ Z' t = (F t (U t * (Z t)ᵀ))ᵀ * U t ∧
        U' t * ((Z t)ᵀ * Z t) = (1 - U t * (U t)ᵀ) * F t (U t * (Z t)ᵀ) * Z t) ↔
      IsDLRASolution r F (fun t => U t * (Z t)ᵀ) a b ∧ ∀ t ∈ Ico a b, (U t)ᵀ * U' t = 0
```

`DynamicallyOrthogonal.ddoSystem_iff_isDLRASolution` in [`LeanDLRA/DLRA/DynamicallyOrthogonal.lean`, lines 339–347](../LeanDLRA/DLRA/DynamicallyOrthogonal.lean#L339-L347):

```lean
theorem ddoSystem_iff_isDLRASolution [DecidableEq n] {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {a b : ℝ} {Z Z' : ℝ → Matrix m (Fin r) ℝ}
    {V V' : ℝ → Matrix n (Fin r) ℝ} (hZc : ContinuousOn Z (Icc a b))
    (hVc : ContinuousOn V (Icc a b)) (hZ : ∀ t ∈ Ico a b, HasDerivWithinAt Z (Z' t) (Ici t) t)
    (hV : ∀ t ∈ Ico a b, HasDerivWithinAt V (V' t) (Ici t) t)
    (hVo : ∀ t ∈ Icc a b, (V t)ᵀ * V t = 1) (hG : ∀ t ∈ Icc a b, IsUnit ((Z t)ᵀ * Z t).det) :
    (∀ t ∈ Ico a b, (V t)ᵀ * V' t = 0 ∧ Z' t = F t (Z t * (V t)ᵀ) * V t ∧
        V' t * ((Z t)ᵀ * Z t) = (1 - V t * (V t)ᵀ) * (F t (Z t * (V t)ᵀ))ᵀ * Z t) ↔
      IsDLRASolution r F (fun t => Z t * (V t)ᵀ) a b ∧ ∀ t ∈ Ico a b, (V t)ᵀ * V' t = 0
```

The DO formulation: let `U`, `Z` be continuous on `[a, b]` with right derivatives `U̇`, `Ż` on
`[a, b)`, `Uᵀ U = 1` and `Zᵀ Z` invertible on `[a, b]`. The DO system (`Uᵀ U̇ = 0`,
`Ż = (F(t, Y))ᵀ U`, `U̇ (Zᵀ Z) = (1 - U Uᵀ) F(t, Y) Z`, `Y = U Zᵀ`) holds on `[a, b)` if and only
if `Y` is a DLRA solution of rank `r` that satisfies the gauge condition `Uᵀ U̇ = 0` on `[a, b)`.
The DDO statement is the mirror image for `Y = Z Vᵀ` with `Vᵀ V = 1`. In both, the hypotheses on
the factors are required on the closed interval `[a, b]`, because `IsDLRASolution` asks for rank
`r` at `b` too. The factors are given and differentiable: the theorems translate between two
descriptions of a given pair of factors and do not construct them.

`DynamicallyOrthogonal.isDLRASolution_of_bo` in [`LeanDLRA/DLRA/DynamicallyOrthogonal.lean`, lines 366–376](../LeanDLRA/DLRA/DynamicallyOrthogonal.lean#L366-L376):

```lean
theorem isDLRASolution_of_bo [DecidableEq n] {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {a b : ℝ} {U U' : ℝ → Matrix m (Fin r) ℝ} {Z Z' : ℝ → Matrix n (Fin r) ℝ}
    {Ω : ℝ → Matrix (Fin r) (Fin r) ℝ} (hUc : ContinuousOn U (Icc a b))
    (hZc : ContinuousOn Z (Icc a b)) (hU : ∀ t ∈ Ico a b, HasDerivWithinAt U (U' t) (Ici t) t)
    (hZ : ∀ t ∈ Ico a b, HasDerivWithinAt Z (Z' t) (Ici t) t)
    (hZo : ∀ t ∈ Icc a b, (Z t)ᵀ * Z t = 1) (hD : ∀ t ∈ Icc a b, IsUnit ((U t)ᵀ * U t).det)
    (hΩ : ∀ t ∈ Ico a b, (Ω t)ᵀ = -Ω t)
    (hU' : ∀ t ∈ Ico a b, U' t = F t (U t * (Z t)ᵀ) * Z t + U t * Ω t)
    (hZ' : ∀ t ∈ Ico a b, Z' t = Z t * Ω t +
      (1 - Z t * (Z t)ᵀ) * (F t (U t * (Z t)ᵀ))ᵀ * U t * ((U t)ᵀ * U t)⁻¹) :
    IsDLRASolution r F (fun t => U t * (Z t)ᵀ) a b
```

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

`exists_ODESolution_of_apriori_sublevel` in [`LeanDLRA/Foundations/AprioriExistence.lean`, lines 135–143](../LeanDLRA/Foundations/AprioriExistence.lean#L135-L143):

```lean
theorem exists_ODESolution_of_apriori_sublevel {g : E → ℝ} {Lg δ₁ δ₂ L M a b : ℝ} {y₀ : E}
    (hg : ∀ x y, |g x - g y| ≤ Lg * ‖x - y‖) (hδ : δ₁ < δ₂)
    (hL : IsLipschitzFieldOn f (univ ×ˢ {x | g x ≤ δ₂}) L)
    (hM : IsBoundedFieldOn f (univ ×ˢ {x | g x ≤ δ₂}) M)
    (hc : ∀ x, g x ≤ δ₂ → Continuous fun t => f t x) (hab : a ≤ b)
    (hpri : ∀ (c : E → ℝ) (y : ℝ → E), (∀ x, 0 ≤ c x) → (∀ x, c x ≤ 1) →
      (∀ x, δ₂ < g x → c x = 0) → y a = y₀ → ODESolution (fun t x => c x • f t x) y a b →
      ∀ t ∈ Icc a b, g (y t) ≤ δ₁) :
    ∃ y : ℝ → E, ODESolution f y a b ∧ y a = y₀ ∧ ∀ t ∈ Icc a b, g (y t) ≤ δ₁
```

`exists_ODESolution_of_closedBall` in [`LeanDLRA/Foundations/AprioriExistence.lean`, lines 191–196](../LeanDLRA/Foundations/AprioriExistence.lean#L191-L196):

```lean
theorem exists_ODESolution_of_closedBall {y₀ : E} {δ L M a b : ℝ}
    (hL : IsLipschitzFieldOn f (univ ×ˢ closedBall y₀ δ) L)
    (hM : IsBoundedFieldOn f (univ ×ˢ closedBall y₀ δ) M) (hM0 : 0 ≤ M)
    (hc : ∀ x ∈ closedBall y₀ δ, Continuous fun t => f t x) (hab : a ≤ b)
    (hδ : M * (b - a) < δ) :
    ∃ y : ℝ → E, ODESolution f y a b ∧ y a = y₀ ∧ ∀ t ∈ Icc a b, ‖y t - y₀‖ ≤ M * (t - a)
```

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

`IsDLRASolution.sub_le_singularValues` in [`LeanDLRA/DLRA/Existence.lean`, lines 256–259](../LeanDLRA/DLRA/Existence.lean#L256-L259):

```lean
theorem IsDLRASolution.sub_le_singularValues (hB : IsBoundedField F B)
    (hY : IsDLRASolution r F Y a b) : ∀ t ∈ Icc a b,
      (toEuclideanLin (Y a)).singularValues (r - 1) - B * (t - a) ≤
        (toEuclideanLin (Y t)).singularValues (r - 1)
```

`IsDLRASolution.eqOn` in [`LeanDLRA/DLRA/Existence.lean`, lines 296–298](../LeanDLRA/DLRA/Existence.lean#L296-L298):

```lean
theorem IsDLRASolution.eqOn (hF : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hY : IsDLRASolution r F Y a b) (hZ : IsDLRASolution r F Z a b) (h0 : Y a = Z a) :
    EqOn Y Z (Icc a b)
```

`exists_isDLRASolution` in [`LeanDLRA/DLRA/Existence.lean`, lines 698–704](../LeanDLRA/DLRA/Existence.lean#L698-L704):

```lean
theorem exists_isDLRASolution (hF : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank = r) (hab : a ≤ b)
    (hρ : B * (b - a) < (toEuclideanLin Y₀).singularValues (r - 1)) :
    ∃ Y : ℝ → Matrix m n ℝ, Y a = Y₀ ∧ IsDLRASolution r F Y a b ∧
      (∀ t ∈ Icc a b, (toEuclideanLin Y₀).singularValues (r - 1) - B * (t - a) ≤
        (toEuclideanLin (Y t)).singularValues (r - 1)) ∧
      ∀ Z : ℝ → Matrix m n ℝ, Z a = Y₀ → IsDLRASolution r F Z a b → EqOn Z Y (Icc a b)
```

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

`exists_factors_isDLRASolution` in [`LeanDLRA/DLRA/Existence.lean`, lines 520–534](../LeanDLRA/DLRA/Existence.lean#L520-L534):

```lean
theorem exists_factors_isDLRASolution [DecidableEq m] (hF : IsLipschitzField F L)
    (hB : IsBoundedField F B) (hc : ∀ Y, Continuous fun t => F t Y)
    {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {ρ : ℝ}
    (hS₀ : ∀ v : EuclideanSpace ℝ (Fin r), ρ * ‖v‖ ≤ ‖toEuclideanLin S₀ v‖) (hab : a ≤ b)
    (hρ : B * (b - a) < ρ) :
    ∃ (U : ℝ → Matrix m (Fin r) ℝ) (S : ℝ → Matrix (Fin r) (Fin r) ℝ)
      (V : ℝ → Matrix n (Fin r) ℝ), U a = U₀ ∧ S a = S₀ ∧ V a = V₀ ∧
      (∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ IsUnit (S t).det ∧
        ∀ v : EuclideanSpace ℝ (Fin r), (ρ - B * (t - a)) * ‖v‖ ≤ ‖toEuclideanLin (S t) v‖) ∧
      ODESolution (fun t X => (1 - X * Xᵀ) * F t (U t * S t * (V t)ᵀ) * V t * (S t)⁻¹) U a b ∧
      ODESolution (fun t _ => (U t)ᵀ * F t (U t * S t * (V t)ᵀ) * V t) S a b ∧
      ODESolution (fun t X => (1 - X * Xᵀ) * (F t (U t * S t * (V t)ᵀ))ᵀ * U t * ((S t)⁻¹)ᵀ)
        V a b ∧
      IsDLRASolution r F (fun t => U t * S t * (V t)ᵀ) a b
```

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

`IsDLRASolution.norm_sub_le_integral` in [`LeanDLRA/DLRA/QuasiOptimality.lean`, lines 393–403](../LeanDLRA/DLRA/QuasiOptimality.lean#L393-L403):

```lean
theorem IsDLRASolution.norm_sub_le_integral {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ δ : ℝ} (hY : IsDLRASolution r F Y a b)
    (hρ : 0 < ρ) (hL : 0 ≤ L) (hF : IsLipschitzField F L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ ρ / 4) (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) * (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖)
```

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

`IsDLRASolution.norm_sub_le_integral_of_isLipschitzOnTube` in [`LeanDLRA/DLRA/QuasiOptimalityTube.lean`, lines 133–146](../LeanDLRA/DLRA/QuasiOptimalityTube.lean#L133-L146):

```lean
theorem IsDLRASolution.norm_sub_le_integral_of_isLipschitzOnTube {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ δ R : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hF : IsLipschitzOnTube F A a b R L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ ρ / 4) (hδ : ‖Y a - X a‖ ≤ δ)
    (hsmall : ∀ t ∈ Icc a b, ‖X t - A t‖ + Real.exp ((L + 6 * μ / ρ) * (t - a)) *
      (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖) < R) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) * (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖)
```

The same bound for a field that is `L`-Lipschitz only on the tube of radius `R` around `A`
(`IsLipschitzOnTube`), under the condition `hsmall` that the right-hand side added to
`‖X t - A t‖` stays below `R`. `IsDLRASolution.norm_sub_lt_of_isLipschitzOnTube` shows that then
the DLRA solution never leaves the tube, `‖Y t - A t‖ < R`. The proof extends the field to the
whole space (`tubeExt`) and uses a continuity argument (`bootstrap_of_continuousOn`); the
constants are those of the global case.

`IsDLRASolution.norm_sub_truncation_le_integral_of_gap` in [`LeanDLRA/DLRA/QuasiOptimalityGap.lean`, lines 74–84](../LeanDLRA/DLRA/QuasiOptimalityGap.lean#L74-L84):

```lean
theorem IsDLRASolution.norm_sub_truncation_le_integral_of_gap {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A Y : ℝ → Matrix m n ℝ} {a b L μ ρ δ : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hA : ODESolution F A a b) (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ)
    (hgap : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1) -
      (toEuclideanLin (A t)).singularValues r)
    (hd : ∀ t ∈ Icc a b, ‖truncation (A t) r - A t‖ ≤ ρ / 4)
    (hδ : ‖Y a - truncation (A a) r‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - truncation (A t) r‖ ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) *
        (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖truncation (A s) r - A s‖)
```

The curve `X` is the truncated singular value decomposition of the exact solution,
`X t = truncation (A t) r`, and the hypotheses on `X` are replaced by a gap
`ρ ≤ σ_{r-1}(A t) - σ_r(A t)` along the solution. Under the gap the truncation is
differentiable (section 2.7), so `t ↦ truncation (A t) r` has right derivatives; it is a best
approximation (section 2.2), and `σ_{r-1}(truncation (A t) r) ≥ ρ` (Weyl). The variant on a tube
is `IsDLRASolution.norm_sub_truncation_le_integral_of_gap_of_isLipschitzOnTube`.

`IsDLRASolution.norm_sub_le_integral_of_margin` in [`LeanDLRA/DLRA/QuasiOptimalityMargin.lean`, lines 284–295](../LeanDLRA/DLRA/QuasiOptimalityMargin.lean#L284-L295):

```lean
theorem IsDLRASolution.norm_sub_le_integral_of_margin {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ θ δ : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hA : ODESolution F A a b) (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ)
    (hXc : ContinuousOn X (Icc a b)) (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0) (hθ : 2 * θ < 1)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ θ * ρ) (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + 2 * μ / ρ + 2 * μ / ((1 - 2 * θ) * ρ)) * (t - a)) *
        (δ + (L + 2 * μ / ((1 - 2 * θ) * ρ)) * ∫ s in a..t, ‖X s - A s‖)
```

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
argument works for every margin `θ < 1`. The file [`DLRA/QuasiOptimalityNormal.lean`](../LeanDLRA/DLRA/QuasiOptimalityNormal.lean)
differentiates the first-order condition with the constant `1`,
`‖P(X) (Ȧ - Ẋ)‖ ≤ ρ⁻¹ ‖Ẋ‖ ‖A - X‖` (`norm_tangentProjAt_sub_le_inv_mul_of_hasDerivWithinAt`),
which gives `‖Ẋ‖ ≤ μ / (1 - θ)` under `‖X - A‖ ≤ θ ρ`
(`norm_le_div_one_sub_of_tangentProjAt_sub_eq_zero`). The theorem:

`IsDLRASolution.norm_sub_le_integral_of_margin_lt_one` in [`LeanDLRA/DLRA/QuasiOptimalityNormal.lean`, lines 315–326](../LeanDLRA/DLRA/QuasiOptimalityNormal.lean#L315-L326):

```lean
theorem IsDLRASolution.norm_sub_le_integral_of_margin_lt_one {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ θ δ : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hA : ODESolution F A a b) (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ)
    (hXc : ContinuousOn X (Icc a b)) (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ θ * ρ) (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + μ / ρ + μ / ((1 - θ) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - θ) * ρ)) * ∫ s in a..t, ‖X s - A s‖)
```

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

**The other forms of the theorem.** The file [`DLRA/QuasiOptimalitySharp.lean`](../LeanDLRA/DLRA/QuasiOptimalitySharp.lean) carries
the bound with the margin `θ ρ`, `θ < 1`, to the forms that section 3.7 has with the margin
`ρ / 4`: the bound for the error against `A`
(`dlra_norm_sub_le_add_integral_of_margin_lt_one`), a curve `X` of best approximations of rank at
most `r` (`IsDLRASolution.norm_sub_le_integral_of_forall_norm_sub_le_of_margin_lt_one`), a field
that is Lipschitz on a tube only
(`IsDLRASolution.norm_sub_lt_of_isLipschitzOnTube_of_margin_lt_one`,
`IsDLRASolution.norm_sub_le_integral_of_isLipschitzOnTube_of_margin_lt_one`,
`IsDLRASolution.norm_sub_le_integral_of_forall_norm_sub_le_of_isLipschitzOnTube_of_lt_one`), and
the truncated singular value decomposition under a gap:

`IsDLRASolution.norm_sub_truncation_le_integral_of_gap_of_margin_lt_one` in [`LeanDLRA/DLRA/QuasiOptimalitySharp.lean`, lines 282–292](../LeanDLRA/DLRA/QuasiOptimalitySharp.lean#L282-L292):

```lean
theorem IsDLRASolution.norm_sub_truncation_le_integral_of_gap_of_margin_lt_one {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A Y : ℝ → Matrix m n ℝ} {a b L μ ρ θ δ : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hA : ODESolution F A a b) (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ)
    (hgap : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1) -
      (toEuclideanLin (A t)).singularValues r) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc a b, ‖truncation (A t) r - A t‖ ≤ θ * ρ)
    (hδ : ‖Y a - truncation (A a) r‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - truncation (A t) r‖ ≤
      Real.exp ((L + μ / ρ + μ / ((1 - θ) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - θ) * ρ)) * ∫ s in a..t, ‖truncation (A s) r - A s‖)
```

Here `X t = truncation (A t) r`, the gap condition `ρ ≤ σ_{r-1}(A t) - σ_r(A t)` is that of
`IsDLRASolution.norm_sub_truncation_le_integral_of_gap`, the margin is
`‖truncation (A t) r - A t‖ ≤ θ ρ`, and the constants are those of the previous theorem. The
variant on a tube is
`IsDLRASolution.norm_sub_truncation_le_integral_of_gap_of_isLipschitzOnTube_of_lt_one`.
The file also has the Lipschitz constant of the projected field:

`norm_tangentProjAt_field_sub_le_inv_mul` in [`LeanDLRA/DLRA/QuasiOptimalitySharp.lean`, lines 327–331](../LeanDLRA/DLRA/QuasiOptimalitySharp.lean#L327-L331):

```lean
theorem norm_tangentProjAt_field_sub_le_inv_mul {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {L B : ℝ} (hF : IsLipschitzField F L) (hB : IsBoundedField F B) {X Y : Matrix m n ℝ}
    (hX : X.rank = r) (hY : Y.rank = r) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) (t : ℝ) :
    ‖tangentProjAt Y (F t Y) - tangentProjAt X (F t X)‖ ≤ (ρ⁻¹ * B + L) * ‖Y - X‖
```

For `F` that is `L`-Lipschitz and bounded by `B` (`hF`, `hB`) and `X`, `Y` of rank `r` with
`ρ ≤ σ_{r-1}(X)` the projected field `Y ↦ P(Y) F(t, Y)` is Lipschitz with the constant
`B / ρ + L`, in place of `2 B / ρ + L`. The `example`s of the file restate the theorems of the
files of the margin `ρ / 4` and prove them from the theorems of this file with `θ = 1 / 4`.

**The truncated singular value decomposition has rank `r`.** The theorems for
`X t = truncation (A t) r` need that `X t` has rank `r` and that `ρ ≤ σ_{r-1}(X t)` when
`ρ ≤ σ_{r-1}(A t)`. The file [`DLRA/QuasiOptimality.lean`](../LeanDLRA/DLRA/QuasiOptimality.lean) has these as lemmas, with a
factorization of the truncation:

`EckartYoung.exists_truncation_eq_mul_diagonal_mul_transpose` in [`LeanDLRA/DLRA/QuasiOptimality.lean`, lines 450–453](../LeanDLRA/DLRA/QuasiOptimality.lean#L450-L453):

```lean
theorem EckartYoung.exists_truncation_eq_mul_diagonal_mul_transpose {r : ℕ} {A : Matrix m n ℝ}
    {ρ : ℝ} (hρ : 0 < ρ) (hσ : ρ ≤ (toEuclideanLin A).singularValues (r - 1)) :
    ∃ (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (σ : Fin r → ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ (∀ i, ρ ≤ σ i) ∧ truncation A r = U * diagonal σ * Vᵀ
```

`EckartYoung.rank_truncation_of_le_singularValues` in [`LeanDLRA/DLRA/QuasiOptimality.lean`, lines 513–515](../LeanDLRA/DLRA/QuasiOptimality.lean#L513-L515):

```lean
theorem EckartYoung.rank_truncation_of_le_singularValues {r : ℕ} {A : Matrix m n ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (hσ : ρ ≤ (toEuclideanLin A).singularValues (r - 1)) :
    (truncation A r).rank = r
```

`EckartYoung.le_singularValues_truncation` in [`LeanDLRA/DLRA/QuasiOptimality.lean`, lines 524–526](../LeanDLRA/DLRA/QuasiOptimality.lean#L524-L526):

```lean
theorem EckartYoung.le_singularValues_truncation {r : ℕ} (hr : 0 < r) {A : Matrix m n ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (hσ : ρ ≤ (toEuclideanLin A).singularValues (r - 1)) :
    ρ ≤ (toEuclideanLin (truncation A r)).singularValues (r - 1)
```

If the `r`-th singular value of `A` is at least `ρ > 0`, then `truncation A r` is `U diag(σ) Vᵀ`
with `r` orthonormal columns of `U` and of `V` and `σ i ≥ ρ`; hence it has rank `r` (and not only
at most `r`, `EckartYoung.rank_truncation_le`), and its `r`-th singular value is at least `ρ`
(for `0 < r`).

**The truncated singular value decomposition with the margin `θ ρ`.** For the case
`F(t, Y) = Ȧ(t)`, `X t = truncation (A t) r` of section 3.4 the file
[`DLRA/QuasiOptimalityTruncation.lean`](../LeanDLRA/DLRA/QuasiOptimalityTruncation.lean) has the bound for every `θ < 1`, and the
corollary with the margin `ρ / 2`:

`dlra_norm_sub_truncation_le_integral_of_margin_lt_one` in [`LeanDLRA/DLRA/QuasiOptimalityTruncation.lean`, lines 62–74](../LeanDLRA/DLRA/QuasiOptimalityTruncation.lean#L62-L74):

```lean
theorem dlra_norm_sub_truncation_le_integral_of_margin_lt_one {r : ℕ} (hr : 0 < r)
    {A A' X X' Y : ℝ → Matrix m n ℝ} {T μ ρ θ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ t ∈ Icc 0 T, HasDerivAt A (A' t) t)
    (hμ : ∀ t ∈ Icc 0 T, ‖A' t‖ ≤ μ) (hXbest : ∀ t ∈ Icc 0 T, X t = truncation (A t) r)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (X' t) t)
    (hσ : ∀ t ∈ Icc 0 T, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1)) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc 0 T, ‖X t - A t‖ ≤ θ * ρ)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc 0 T, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t _ => tangentProj (U t) (V t) (A' t)) Y 0 T) (hY₀ : Y 0 = X 0) :
    ∀ t ∈ Icc 0 T, ‖Y t - X t‖ ≤
      μ / ((1 - θ) * ρ) * Real.exp ((μ / ρ + μ / ((1 - θ) * ρ)) * t) *
        ∫ s in (0 : ℝ)..t, ‖X s - A s‖
```

`dlra_norm_sub_truncation_le_integral_of_norm_sub_le_half` in [`LeanDLRA/DLRA/QuasiOptimalityTruncation.lean`, lines 105–116](../LeanDLRA/DLRA/QuasiOptimalityTruncation.lean#L105-L116):

```lean
theorem dlra_norm_sub_truncation_le_integral_of_norm_sub_le_half {r : ℕ} (hr : 0 < r)
    {A A' X X' Y : ℝ → Matrix m n ℝ} {T μ ρ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ t ∈ Icc 0 T, HasDerivAt A (A' t) t)
    (hμ : ∀ t ∈ Icc 0 T, ‖A' t‖ ≤ μ) (hXbest : ∀ t ∈ Icc 0 T, X t = truncation (A t) r)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (X' t) t)
    (hσ : ∀ t ∈ Icc 0 T, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1))
    (hd : ∀ t ∈ Icc 0 T, ‖X t - A t‖ ≤ ρ / 2)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc 0 T, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t _ => tangentProj (U t) (V t) (A' t)) Y 0 T) (hY₀ : Y 0 = X 0) :
    ∀ t ∈ Icc 0 T, ‖Y t - X t‖ ≤
      2 * μ / ρ * Real.exp (3 * μ / ρ * t) * ∫ s in (0 : ℝ)..t, ‖X s - A s‖
```

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
[`DLRA/QuasiOptimalitySpectral.lean`](../LeanDLRA/DLRA/QuasiOptimalitySpectral.lean) uses the spectral norm `‖A - X‖₂ = specNorm`
where the differentiated first-order condition allows it, by means of the bounds of
section 2.4 on normal vectors with `‖N‖₂`:

`norm_le_div_one_sub_of_specNorm_sub_le` in [`LeanDLRA/DLRA/QuasiOptimalitySpectral.lean`, lines 163–169](../LeanDLRA/DLRA/QuasiOptimalitySpectral.lean#L163-L169):

```lean
theorem norm_le_div_one_sub_of_specNorm_sub_le {r : ℕ} {A X : ℝ → Matrix m n ℝ}
    {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ μ θ : ℝ} (hA : HasDerivWithinAt A A' s t)
    (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s) (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ)
    (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ : ∀ u ∈ s, ρ ≤ (toEuclideanLin (X u)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) (hμ : ‖A'‖ ≤ μ) (hθ : θ < 1)
    (hd : Curvature.specNorm (X t - A t) ≤ θ * ρ) : ‖X'‖ ≤ μ / (1 - θ)
```

The speed of a curve `X` of critical points (`P(X u) (A u - X u) = 0` on `s`, rank `r`,
`ρ ≤ σ_{r-1}(X u)`) with `‖Ȧ‖ ≤ μ` in the Frobenius norm is at most `μ / (1 - θ)` if
`‖X t - A t‖₂ ≤ θ ρ`, `θ < 1`. The file has the velocity bound
`‖X' - P(X t) A'‖ ≤ μ / ((1 - θ) ρ) ‖A t - X t‖₂`
(`norm_sub_tangentProjAt_le_div_one_sub_mul_specNorm`), and the quasi-optimality theorem:

`dlra_norm_sub_le_integral_of_specNorm_sub_le` in [`LeanDLRA/DLRA/QuasiOptimalitySpectral.lean`, lines 224–240](../LeanDLRA/DLRA/QuasiOptimalitySpectral.lean#L224-L240):

```lean
theorem dlra_norm_sub_le_integral_of_specNorm_sub_le {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ θ δ : ℝ}
    (hρ : 0 < ρ) (hL : 0 ≤ L) (hF : IsLipschitzField F L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc a b, Curvature.specNorm (X t - A t) ≤ θ * ρ)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t x => tangentProj (U t) (V t) (F t x)) Y a b)
    (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + μ / ρ) * (t - a)) *
        (δ + L * (∫ s in a..t, ‖X s - A s‖) +
          μ / ((1 - θ) * ρ) * ∫ s in a..t, Curvature.specNorm (X s - A s))
```

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

`specNorm_sub_truncation` in [`LeanDLRA/Classical/EckartYoung.lean`, lines 554–555](../LeanDLRA/Classical/EckartYoung.lean#L554-L555):

```lean
theorem specNorm_sub_truncation (A : Matrix m n ℝ) (r : ℕ) :
    specNorm (A - truncation A r) = (toEuclideanLin A).singularValues r
```

so that the margin is a condition on the singular values, `σ_r(A t) ≤ θ ρ` with
`ρ ≤ σ_{r-1}(A t)` (singular values are indexed from zero). The theorem for `F(t, Y) = Ȧ(t)`:

`dlra_norm_sub_truncation_le_integral_of_singularValues_le` in [`LeanDLRA/DLRA/QuasiOptimalitySpectral.lean`, lines 425–437](../LeanDLRA/DLRA/QuasiOptimalitySpectral.lean#L425-L437):

```lean
theorem dlra_norm_sub_truncation_le_integral_of_singularValues_le {r : ℕ} (hr : 0 < r)
    {A A' X X' Y : ℝ → Matrix m n ℝ} {T μ ρ θ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ t ∈ Icc 0 T, HasDerivAt A (A' t) t)
    (hμ : ∀ t ∈ Icc 0 T, ‖A' t‖ ≤ μ) (hXbest : ∀ t ∈ Icc 0 T, X t = truncation (A t) r)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (X' t) t)
    (hσ : ∀ t ∈ Icc 0 T, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1)) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc 0 T, (toEuclideanLin (A t)).singularValues r ≤ θ * ρ)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc 0 T, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t _ => tangentProj (U t) (V t) (A' t)) Y 0 T) (hY₀ : Y 0 = X 0) :
    ∀ t ∈ Icc 0 T, ‖Y t - X t‖ ≤
      μ / ((1 - θ) * ρ) * Real.exp (μ / ρ * t) *
        ∫ s in (0 : ℝ)..t, (toEuclideanLin (A s)).singularValues r
```

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
| `IsDLRASolution.norm_sub_le_integral` | `‖X - A‖ ≤ ρ / 4` | `L + 4 μ/ρ`; `L + 6 μ/ρ` | `‖X - A‖` | [`DLRA/QuasiOptimality.lean`](../LeanDLRA/DLRA/QuasiOptimality.lean) |
| `IsDLRASolution.norm_sub_le_integral_of_margin` | `‖X - A‖ ≤ θ ρ`, `2 θ < 1` | `L + κ₁`; `L + 2 μ/ρ + κ₁` | `‖X - A‖` | [`DLRA/QuasiOptimalityMargin.lean`](../LeanDLRA/DLRA/QuasiOptimalityMargin.lean) |
| `IsDLRASolution.norm_sub_le_integral_of_margin_lt_one` | `‖X - A‖ ≤ θ ρ`, `θ < 1` | `L + κ`; `L + μ/ρ + κ` | `‖X - A‖` | [`DLRA/QuasiOptimalityNormal.lean`](../LeanDLRA/DLRA/QuasiOptimalityNormal.lean) |
| `IsDLRASolution.norm_sub_le_integral_of_specNorm_sub_le` | `‖X - A‖₂ ≤ θ ρ`, `θ < 1` | `L` and `κ`; `L + μ/ρ` | `‖X - A‖` with `L`, `‖X - A‖₂` with `κ` | [`DLRA/QuasiOptimalitySpectral.lean`](../LeanDLRA/DLRA/QuasiOptimalitySpectral.lean) |
| `dlra_norm_sub_truncation_le_integral` | `‖X - A‖ ≤ ρ / 16` | `16 μ/ρ`; `8 μ/ρ` | `‖X - A‖` | [`DLRA/QuasiOptimality.lean`](../LeanDLRA/DLRA/QuasiOptimality.lean) |
| `dlra_norm_sub_truncation_le_integral_of_margin_lt_one` | `‖X - A‖ ≤ θ ρ`, `θ < 1` | `κ`; `μ/ρ + κ` | `‖X - A‖` | [`DLRA/QuasiOptimalityTruncation.lean`](../LeanDLRA/DLRA/QuasiOptimalityTruncation.lean) |
| `dlra_norm_sub_truncation_le_integral_of_norm_sub_le_half` | `‖X - A‖ ≤ ρ / 2` | `2 μ/ρ`; `3 μ/ρ` | `‖X - A‖` | [`DLRA/QuasiOptimalityTruncation.lean`](../LeanDLRA/DLRA/QuasiOptimalityTruncation.lean) |
| `dlra_norm_sub_truncation_le_integral_of_specNorm_sub_le` | `‖X - A‖₂ ≤ θ ρ`, `θ < 1` | `κ`; `μ / ρ` | `‖X - A‖₂` | [`DLRA/QuasiOptimalitySpectral.lean`](../LeanDLRA/DLRA/QuasiOptimalitySpectral.lean) |
| `dlra_norm_sub_truncation_le_integral_of_singularValues_le` | `σ_r(A) ≤ θ ρ`, `θ < 1` | `κ`; `μ / ρ` | `σ_r(A)` | [`DLRA/QuasiOptimalitySpectral.lean`](../LeanDLRA/DLRA/QuasiOptimalitySpectral.lean) |

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
table above lists the constants of the proofs, not optimal ones.

## 4. Steps, runs and the global error

This section is independent of low rank. It contains the argument that turns a bound for the
local error of a method into a bound for the global error, and its last entry is the theorem of
which the integrators of sections 5 and 6 are instances.

### 4.1 Definitions

`StepRel` in [`LeanDLRA/Integrators/Defs.lean`, line 232](../LeanDLRA/Integrators/Defs.lean#L232):

```lean
abbrev StepRel (E : Type*) : Type _ := ℝ → ℝ → E → E → Prop
```

`IsGrid` in [`LeanDLRA/Integrators/Defs.lean`, lines 65–67](../LeanDLRA/Integrators/Defs.lean#L65-L67):

```lean
structure IsGrid (τ : ℕ → ℝ) (N : ℕ) : Prop where
  /-- The grid times are nondecreasing up to step `N`. -/
  mono : ∀ n < N, τ n ≤ τ (n + 1)
```

`uniformGrid` in [`LeanDLRA/Integrators/Defs.lean`, line 70](../LeanDLRA/Integrators/Defs.lean#L70):

```lean
abbrev uniformGrid (t₀ h : ℝ) : ℕ → ℝ := fun n => t₀ + n * h
```

`IsRun` in [`LeanDLRA/Integrators/Defs.lean`, lines 239–243](../LeanDLRA/Integrators/Defs.lean#L239-L243):

```lean
structure IsRun (M : StepRel E) (τ : ℕ → ℝ) (N : ℕ) (Y : ℕ → E) : Prop where
  /-- `τ` is a grid with `N` steps. -/
  grid : IsGrid τ N
  /-- Step `n` of the run is a step of `M`. -/
  step : ∀ n < N, M (τ n) (τ (n + 1)) (Y n) (Y (n + 1))
```

`HasLocalError` in [`LeanDLRA/Integrators/Defs.lean`, lines 133–134](../LeanDLRA/Integrators/Defs.lean#L133-L134):

```lean
def HasLocalError (F : ℝ → E → E) (t₀ t₁ : ℝ) (Y₀ Y₁ : E) (δ : ℝ) : Prop :=
  ∀ Φ : ℝ → E, ODESolution F Φ t₀ t₁ → Φ t₀ = Y₀ → ‖Y₁ - Φ t₁‖ ≤ δ
```

`StepRel.HasLocalErrorOn` in [`LeanDLRA/Integrators/Defs.lean`, lines 278–280](../LeanDLRA/Integrators/Defs.lean#L278-L280):

```lean
def StepRel.HasLocalErrorOn (M : StepRel E) (F : ℝ → E → E) (D : Set (ℝ × E))
    (δ : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃t₀ t₁ Y₀ Y₁⦄, t₀ ≤ t₁ → (t₀, Y₀) ∈ D → M t₀ t₁ Y₀ Y₁ → HasLocalError F t₀ t₁ Y₀ Y₁ (δ t₀ t₁)
```

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

`IsLipschitzField.norm_sub_le_of_hasLocalError` in [`LeanDLRA/Integrators/GlobalError.lean`, lines 258–264](../LeanDLRA/Integrators/GlobalError.lean#L258-L264):

```lean
theorem IsLipschitzField.norm_sub_le_of_hasLocalError {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {F : ℝ → E → E} {A : ℝ → E} {τ : ℕ → ℝ} {N : ℕ}
    {Y : ℕ → E} {L : ℝ} {δ : ℕ → ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hc : ∀ x, Continuous fun t => F t x) (hτ : IsGrid τ N) (hA : ODESolution F A (τ 0) (τ N))
    (hloc : ∀ n < N, HasLocalError F (τ n) (τ (n + 1)) (Y n) (Y (n + 1)) (δ n)) :
    ∀ n ≤ N, ‖Y n - A (τ n)‖ ≤ Real.exp (L * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k
```

Global assumptions. Let `F` be globally `L`-Lipschitz with `0 ≤ L` and continuous in time
(`hc`), `τ` a grid, `A` a solution on `[τ 0, τ N]`, and `Y` any sequence whose `k`-th step has
local error `δ k` (`hloc`). Then for all `n ≤ N`

`‖Y n - A (τ n)‖ ≤ e^{L (τ n - τ 0)} ‖Y 0 - A (τ 0)‖ + ∑_{k<n} e^{L (τ n - τ (k+1))} δ k`.

The space `E` has to be complete. The constants are the Lipschitz constant and the grid only.
This is the classical argument known as Lady Windermere's fan; no paper is cited.

`IsRun.norm_sub_le_of_tube` in [`LeanDLRA/Integrators/Tube.lean`, lines 274–283](../LeanDLRA/Integrators/Tube.lean#L274-L283):

```lean
theorem IsRun.norm_sub_le_of_tube [CompleteSpace E] {M : StepRel E} (hY : IsRun M τ N Y)
    (hP : DLRAProblem F A (τ 0) (τ N) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A (τ 0) (τ N) ρ))
    (hM : ∀ n < N, ∀ Y₀ Y₁, ‖Y₀ - A (τ n)‖ ≤ R n → M (τ n) (τ (n + 1)) Y₀ Y₁ →
      HasLocalError F (τ n) (τ (n + 1)) Y₀ Y₁ (δ n))
    (hR : ∀ n < N, Real.exp (L * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k ≤ R n)
    (hsmall : ∀ n < N, R n + 2 * B * (τ (n + 1) - τ n) < ρ) :
    ∀ n ≤ N, ‖Y n - A (τ n)‖ ≤ Real.exp (L * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k
```

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

`StepMethod` in [`LeanDLRA/Integrators/Method.lean`, line 350](../LeanDLRA/Integrators/Method.lean#L350):

```lean
abbrev StepMethod (E : Type*) : Type _ := (ℝ → E → E) → StepRel E
```

`StepMethod.IsTubeLocal` in [`LeanDLRA/Integrators/Method.lean`, lines 357–371](../LeanDLRA/Integrators/Method.lean#L357-L371):

```lean
structure StepMethod.IsTubeLocal (M : StepMethod E) (Adm : E → Prop) (κ : ℝ) : Prop where
  /-- (E) A step exists from every value with `Adm`, for every globally Lipschitz field that is
  continuous in time on the step interval. No bound on the field is assumed. -/
  exists_step : ∀ {G : ℝ → E → E} {L t₀ t₁ : ℝ} {Y₀ : E}, IsLipschitzField G L →
    (∀ x, ContinuousOn (fun t => G t x) (Icc t₀ t₁)) → t₀ ≤ t₁ → Adm Y₀ → ∃ Y₁, M G t₀ t₁ Y₀ Y₁
  /-- (I) A forward step from a value with `Adm` ends at a value with `Adm`. -/
  adm_of_step : ∀ {G : ℝ → E → E} {t₀ t₁ : ℝ} {Y₀ Y₁ : E}, t₀ ≤ t₁ → Adm Y₀ →
    M G t₀ t₁ Y₀ Y₁ → Adm Y₁
  /-- (T) If `F` is bounded by `B` on the tube of radius `ρ` around a solution `A` and the start
  value has the margin `‖Y₀ - A t₀‖ + κ B (t₁ - t₀) < ρ`, then a step of the extended field
  `tubeExt F A a b ρ` from `Y₀` is a step of `F`. -/
  step_of_tubeExt : ∀ {F : ℝ → E → E} {A : ℝ → E} {a b ρ B t₀ t₁ : ℝ} {Y₀ Y₁ : E},
    IsBoundedOnTube F A a b ρ B → 0 ≤ B → a ≤ t₀ → t₁ ≤ b → t₀ ≤ t₁ → ODESolution F A t₀ t₁ →
    Adm Y₀ → ‖Y₀ - A t₀‖ + κ * B * (t₁ - t₀) < ρ → M (tubeExt F A a b ρ) t₀ t₁ Y₀ Y₁ →
    M F t₀ t₁ Y₀ Y₁
```

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

`StepMethod.IsTubeLocal.exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Method.lean`, lines 403–414](../LeanDLRA/Integrators/Method.lean#L403-L414):

```lean
theorem StepMethod.IsTubeLocal.exists_run_norm_sub_le [CompleteSpace E]
    (hM : M.IsTubeLocal Adm κ) (hκ : 2 ≤ κ) (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hloc : ∀ n < N, ∀ Y₀ Y₁, Adm Y₀ →
      ‖Y₀ - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) * c →
      M F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ →
      HasLocalError F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ (h * c))
    (hc₀ : 0 ≤ c) (hh : 0 ≤ h) (hNT : N * h ≤ T) {Y₀ : E} (hY₀ : Adm Y₀)
    (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) * c + κ * B * h < ρ) :
    ∃ Y : ℕ → E, Y 0 = Y₀ ∧ IsRun (M F) (uniformGrid t₀ h) N Y ∧ ∀ n ≤ N, Adm (Y n) ∧
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) * c
```

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

`StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_isGrid` in [`LeanDLRA/Integrators/MethodGrid.lean`, lines 62–74](../LeanDLRA/Integrators/MethodGrid.lean#L62-L74):

```lean
theorem StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_isGrid [CompleteSpace E]
    (hM : M.IsTubeLocal Adm κ) (hκ : 2 ≤ κ) (hτ : IsGrid τ N)
    (hP : DLRAProblem F A (τ 0) (τ N) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A (τ 0) (τ N) ρ))
    (hloc : ∀ n < N, ∀ Y₀ Y₁, Adm Y₀ → ‖Y₀ - A (τ n)‖ ≤ R n → M F (τ n) (τ (n + 1)) Y₀ Y₁ →
      HasLocalError F (τ n) (τ (n + 1)) Y₀ Y₁ (δ n))
    {Y₀ : E} (hY₀ : Adm Y₀)
    (hR : ∀ n < N, Real.exp (L * (τ n - τ 0)) * ‖Y₀ - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k ≤ R n)
    (hsmall : ∀ n < N, R n + κ * B * (τ (n + 1) - τ n) < ρ) :
    ∃ Y : ℕ → E, Y 0 = Y₀ ∧ IsRun (M F) τ N Y ∧ ∀ n ≤ N, Adm (Y n) ∧
      ‖Y n - A (τ n)‖ ≤ Real.exp (L * (τ n - τ 0)) * ‖Y₀ - A (τ 0)‖ +
        ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k
```

`StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_tol` in [`LeanDLRA/Integrators/MethodTolerance.lean`, lines 88–99](../LeanDLRA/Integrators/MethodTolerance.lean#L88-L99):

```lean
theorem StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_tol [CompleteSpace E]
    (hM : M.IsTubeLocal Adm κ) (hκ : 2 ≤ κ) (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hloc : ∀ n < N, ∀ Y₀ Y₁, Adm Y₀ →
      ‖Y₀ - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * (δ + N * ϑ) + T * Real.exp (L * T) * c →
      M F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ →
      HasLocalError F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ (h * c + ϑ))
    (hc₀ : 0 ≤ c) (hϑ : 0 ≤ ϑ) (hh : 0 ≤ h) (hNT : N * h ≤ T) {Y₀ : E} (hY₀ : Adm Y₀)
    (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * (δ + N * ϑ) + T * Real.exp (L * T) * c + κ * B * h < ρ) :
    ∃ Y : ℕ → E, Y 0 = Y₀ ∧ IsRun (M F) (uniformGrid t₀ h) N Y ∧ ∀ n ≤ N, Adm (Y n) ∧
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * (δ + n * ϑ) + T * Real.exp (L * T) * c
```

`StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_oneSided` in [`LeanDLRA/Integrators/MethodOneSided.lean`, lines 427–439](../LeanDLRA/Integrators/MethodOneSided.lean#L427-L439):

```lean
theorem StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_oneSided [CompleteSpace E]
    (hM : M.IsTubeLocal Adm κ) (hκ : 2 ≤ κ) (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hℓ : IsOneSidedLipschitzFieldOn F (tubeSet A t₀ (t₀ + N * h) ρ) ℓ) (hℓ₀ : 0 ≤ ℓ)
    (hloc : ∀ n < N, ∀ Y₀ Y₁, Adm Y₀ →
      ‖Y₀ - A (t₀ + n * h)‖ ≤ Real.exp (ℓ * T) * δ + T * Real.exp (ℓ * T) * c →
      M F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ →
      HasLocalError F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ (h * c))
    (hc₀ : 0 ≤ c) (hh : 0 ≤ h) (hNT : N * h ≤ T) {Y₀ : E} (hY₀ : Adm Y₀)
    (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (ℓ * T) * δ + T * Real.exp (ℓ * T) * c + κ * B * h < ρ) :
    ∃ Y : ℕ → E, Y 0 = Y₀ ∧ IsRun (M F) (uniformGrid t₀ h) N Y ∧ ∀ n ≤ N, Adm (Y n) ∧
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (ℓ * T) * δ + T * Real.exp (ℓ * T) * c
```

`StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_oneSided_neg` in [`LeanDLRA/Integrators/MethodOneSided.lean`, lines 466–476](../LeanDLRA/Integrators/MethodOneSided.lean#L466-L476):

```lean
theorem StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_oneSided_neg [CompleteSpace E]
    (hM : M.IsTubeLocal Adm κ) (hκ : 2 ≤ κ) (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hℓ : IsOneSidedLipschitzFieldOn F (tubeSet A t₀ (t₀ + N * h) ρ) ℓ) (hℓ₀ : ℓ < 0)
    (hloc : ∀ n < N, ∀ Y₀ Y₁, Adm Y₀ → ‖Y₀ - A (t₀ + n * h)‖ ≤ δ + (h - ℓ⁻¹) * c →
      M F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ →
      HasLocalError F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ (h * c))
    (hc₀ : 0 ≤ c) (hh : 0 ≤ h) {Y₀ : E} (hY₀ : Adm Y₀) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : δ + (h - ℓ⁻¹) * c + κ * B * h < ρ) :
    ∃ Y : ℕ → E, Y 0 = Y₀ ∧ IsRun (M F) (uniformGrid t₀ h) N Y ∧ ∀ n ≤ N, Adm (Y n) ∧
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (ℓ * (n * h)) * δ + (h - ℓ⁻¹) * c
```

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

`MatrixBUG.IsStep` in [`LeanDLRA/Integrators/Matrix/BUG.lean`, lines 372–393](../LeanDLRA/Integrators/Matrix/BUG.lean#L372-L393):

```lean
structure IsStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ) (U₀ : Matrix m (Fin r) ℝ)
    (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ) (U₁ : Matrix m (Fin r) ℝ)
    (V₁ : Matrix n (Fin r) ℝ) (K : ℝ → Matrix m (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ)
    (S : ℝ → Matrix (Fin r) (Fin r) ℝ) : Prop where
  orthU₀ : U₀ᵀ * U₀ = 1
  orthV₀ : V₀ᵀ * V₀ = 1
  /-- K-step `K' = F(t, K V₀ᵀ) V₀`. -/
  kSol : ODESolution (kField V₀ F) K t₀ t₁
  kStart : K t₀ = U₀ * S₀
  /-- L-step `L' = F(t, U₀ Lᵀ)ᵀ U₀`. -/
  lSol : ODESolution (lField U₀ F) Lf t₀ t₁
  lStart : Lf t₀ = V₀ * S₀ᵀ
  orthU₁ : U₁ᵀ * U₁ = 1
  /-- The new left basis captures `K(t₁)` (QR step). -/
  kCap : U₁ * U₁ᵀ * K t₁ = K t₁
  orthV₁ : V₁ᵀ * V₁ = 1
  /-- The new right basis captures `L(t₁)` (QR step). -/
  lCap : V₁ * V₁ᵀ * Lf t₁ = Lf t₁
  /-- Galerkin S-step `S' = U₁ᵀ F(t, U₁ S V₁ᵀ) V₁`. -/
  sSol : ODESolution (sField U₁ V₁ F) S t₀ t₁
  /-- `S(t₀) = M S₀ Nᵀ` with `M = U₁ᵀ U₀`, `N = V₁ᵀ V₀`. -/
  sStart : S t₀ = U₁ᵀ * U₀ * S₀ * (V₀ᵀ * V₁)
```

`MatrixBUG.stepRel` in [`LeanDLRA/Integrators/Matrix/BUGStep.lean`, lines 72–77](../LeanDLRA/Integrators/Matrix/BUGStep.lean#L72-L77):

```lean
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
      (U₁ : Matrix m (Fin r) ℝ) (V₁ : Matrix n (Fin r) ℝ) (K : ℝ → Matrix m (Fin r) ℝ)
      (Lf : ℝ → Matrix n (Fin r) ℝ) (S : ℝ → Matrix (Fin r) (Fin r) ℝ),
      Y₀ = U₀ * S₀ * V₀ᵀ ∧ IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S ∧ Y₁ = U₁ * S t₁ * V₁ᵀ
```

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

`MatrixBUG.exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Matrix/BUGRun.lean`, lines 280–289](../LeanDLRA/Integrators/Matrix/BUGRun.lean#L280-L289):

```lean
theorem exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : bugGlobalBound L B H T δ ε h + 4 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤ bugGlobalBound L B H T δ ε h
```

`bugGlobalBound` in [`LeanDLRA/Foundations/Localization.lean`, lines 563–565](../LeanDLRA/Foundations/Localization.lean#L563-L565):

```lean
noncomputable def bugGlobalBound (L B H T δ ε h : ℝ) : ℝ :=
  Real.exp (L * T) * δ + T * Real.exp (L * T) * bugC₁ L H * ε
    + T * Real.exp (L * T) * bugC₂ L B H * h
```

`bugC₁` in [`LeanDLRA/Integrators/Defs.lean`, line 359](../LeanDLRA/Integrators/Defs.lean#L359):

```lean
noncomputable def bugC₁ (L H : ℝ) : ℝ := 2 + 2 * L * H * Real.exp (L * H)
```

`bugC₂` in [`LeanDLRA/Integrators/Defs.lean`, line 363](../LeanDLRA/Integrators/Defs.lean#L363):

```lean
noncomputable def bugC₂ (L B H : ℝ) : ℝ := L * B * (8 + Real.exp (L * H) * (1 + 8 * L * H))
```

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

`MatrixBUG.isTubeLocal_stepRel` in [`LeanDLRA/Integrators/Matrix/BUGRun.lean`, lines 249–251](../LeanDLRA/Integrators/Matrix/BUGRun.lean#L249-L251):

```lean
theorem isTubeLocal_stepRel (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) :
    StepMethod.IsTubeLocal (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => stepRel G r)
      (fun Y => Y.rank ≤ r) 4
```

The admissible values are the matrices of rank at most `r` and the margin constant is 4.

`MatrixBUG.IsRun.norm_sub_le` in [`LeanDLRA/Integrators/Matrix/BUGRun.lean`, lines 190–197](../LeanDLRA/Integrators/Matrix/BUGRun.lean#L190-L197):

```lean
theorem IsRun.norm_sub_le {Y : ℕ → Matrix m n ℝ}
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hsmall : bugGlobalBound L B H T δ ε h + 4 * B * h < ρ)
    (hY : IsRun (stepRel F r) (uniformGrid t₀ h) N Y) (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ bugGlobalBound L B H T δ ε h
```

The same bound for every run, not only for the one constructed: under the same hypotheses on the
field, every run `Y` of the BUG integrator with `‖Y 0 - A t₀‖ ≤ δ` satisfies the error bound.
Here no rank condition on the start value is needed, because a step from `Y 0` exists only if
`Y 0` has rank at most `r` (`MatrixBUG.exists_stepRel_iff`).

`exists_bugGlobalBound_lt` in [`LeanDLRA/Integrators/Matrix/BUGRun.lean`, lines 315–317](../LeanDLRA/Integrators/Matrix/BUGRun.lean#L315-L317):

```lean
theorem exists_bugGlobalBound_lt {L B H T ε ρ : ℝ} (hH : 0 < H)
    (hε : T * Real.exp (L * T) * bugC₁ L H * ε < ρ) :
    ∃ δ > 0, ∃ h > 0, h ≤ H ∧ bugGlobalBound L B H T δ ε h + 4 * B * h < ρ
```

The smallness condition can be met: if the part of the bound that comes from the normal
component is smaller than the tube radius, `T e^{L T} c₁ ε < ρ`, and `0 < H`, then there are a
positive `δ` and a positive `h ≤ H` for which `hsmall` holds.

Source: [CerutiLubich2022, Thm. 4]. The paper states the bound for a field that is Lipschitz
and bounded everywhere and for a given sequence of steps; the form quoted here assumes these
properties on a tube only and also proves that the steps exist. The form with global
assumptions is `MatrixBUG.global_error_le` in
[`LeanDLRA/Integrators/Matrix/BUG.lean`](../LeanDLRA/Integrators/Matrix/BUG.lean).

### 5.3 The BUG integrator with smaller local constants and a one-sided Lipschitz constant

Two files improve the bound of section 5.2 in two independent ways. The statements are about the
same step and the same hypotheses on `F` and `A`; the older theorems stay as they are.

`kstep_capture_two_mul` in [`LeanDLRA/Integrators/BUGCapture.lean`, lines 67–73](../LeanDLRA/Integrators/BUGCapture.lean#L67-L73):

```lean
theorem kstep_capture_two_mul (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = A t₀)
    (hKcap : P₁ (YK t₁) = YK t₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε) :
    ‖(1 - P₁) (A t₁)‖ ≤ h * (2 * L * B * h + ε)
```

`bug_capture_two_mul` in [`LeanDLRA/Integrators/BUGCapture.lean`, lines 135–145](../LeanDLRA/Integrators/BUGCapture.lean#L135-L145):

```lean
theorem bug_capture_two_mul {P₀ Q₁ : E →L[ℝ] E} {YL : ℝ → E} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (hP₀ : IsOrthProj P₀) (hQ₀ : IsOrthProj Q₀)
    (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = A t₀)
    (hKcap : P₁ (YK t₁) = YK t₁)
    (hεK : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε)
    (hLs : ODESolution (fun t x => P₀ (F t x)) YL t₀ t₁) (hL₀ : YL t₀ = A t₀)
    (hLcap : Q₁ (YL t₁) = YL t₁)
    (hεL : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε) :
    ‖A t₁ - P₁ (Q₁ (A t₁))‖ ≤ √2 * (h * (2 * L * B * h + ε))
```

`IsBUGStep.local_error_two_mul` in [`LeanDLRA/Integrators/BUGCapture.lean`, lines 179–183](../LeanDLRA/Integrators/BUGCapture.lean#L179-L183):

```lean
theorem local_error_two_mul (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + √2 * (h * (2 * L * B * h + ε)))
      + √2 * (h * (2 * L * B * h + ε))
```

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

`MatrixBUG.exists_run_norm_sub_le_of_oneSided` in [`LeanDLRA/Integrators/Matrix/BUGRunOneSided.lean`, lines 90–104](../LeanDLRA/Integrators/Matrix/BUGRunOneSided.lean#L90-L104):

```lean
theorem exists_run_norm_sub_le_of_oneSided
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hℓ : IsOneSidedLipschitzFieldOn F (tubeSet A t₀ (t₀ + N * h) ρ) ℓ) (hℓ₀ : 0 ≤ ℓ)
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (ℓ * T) * δ + T * Real.exp (ℓ * T) * (√2 * (1 + L * H * Real.exp (L * H))
      * ε + L * B * (Real.exp (L * H) + 2 * √2 * (1 + L * H * Real.exp (L * H))) * h)
      + 4 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (ℓ * T) * δ
        + T * Real.exp (ℓ * T) * (√2 * (1 + L * H * Real.exp (L * H)) * ε
          + L * B * (Real.exp (L * H) + 2 * √2 * (1 + L * H * Real.exp (L * H))) * h)
```

`MatrixBUG.exists_run_norm_sub_le_of_oneSided_neg` in [`LeanDLRA/Integrators/Matrix/BUGRunOneSided.lean`, lines 131–144](../LeanDLRA/Integrators/Matrix/BUGRunOneSided.lean#L131-L144):

```lean
theorem exists_run_norm_sub_le_of_oneSided_neg
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hℓ : IsOneSidedLipschitzFieldOn F (tubeSet A t₀ (t₀ + N * h) ρ) ℓ) (hℓ₀ : ℓ < 0)
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : δ + (h - ℓ⁻¹) * (√2 * (1 + L * H * Real.exp (L * H)) * ε
      + L * B * (Real.exp (L * H) + 2 * √2 * (1 + L * H * Real.exp (L * H))) * h)
      + 4 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (ℓ * (n * h)) * δ
        + (h - ℓ⁻¹) * (√2 * (1 + L * H * Real.exp (L * H)) * ε
          + L * B * (Real.exp (L * H) + 2 * √2 * (1 + L * H * Real.exp (L * H))) * h)
```

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

## 6. Projector splitting and variants of the BUG integrator

### 6.1 The projector-splitting integrator

The projector-splitting integrator of [LubichOseledets2014], also called the KSL integrator,
performs the K-step, then an S-step backward in time, then the L-step, each starting from the
result of the one before.

`MatrixKSL.IsStep` in [`LeanDLRA/Integrators/Matrix/ProjectorSplitting.lean`, lines 318–333](../LeanDLRA/Integrators/Matrix/ProjectorSplitting.lean#L318-L333):

```lean
structure IsStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ) (U₀ : Matrix m r ℝ)
    (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) (U₁ : Matrix m r ℝ) (Ŝ₁ : Matrix r r ℝ)
    (K : ℝ → Matrix m r ℝ) (S : ℝ → Matrix r r ℝ) (Lf : ℝ → Matrix n r ℝ) : Prop where
  orthV₀ : V₀ᵀ * V₀ = 1
  /-- K-step `K' = F(t, K V₀ᵀ) V₀`. -/
  kSol : ODESolution (kField V₀ F) K t₀ t₁
  kStart : K t₀ = U₀ * S₀
  orthU₁ : U₁ᵀ * U₁ = 1
  /-- QR factorization of the K-step result. -/
  kQR : K t₁ = U₁ * Ŝ₁
  /-- Backward S-step `S' = -U₁ᵀ F(t, U₁ S V₀ᵀ) V₀`. -/
  sSol : ODESolution (sField U₁ V₀ F) S t₀ t₁
  sStart : S t₀ = Ŝ₁
  /-- L-step `L' = F(t, U₁ Lᵀ)ᵀ U₁`. -/
  lSol : ODESolution (lField U₁ F) Lf t₀ t₁
  lStart : Lf t₀ = V₀ * (S t₁)ᵀ
```

`MatrixKSL.stepRel` in [`LeanDLRA/Integrators/Matrix/KSLStep.lean`, lines 82–87](../LeanDLRA/Integrators/Matrix/KSLStep.lean#L82-L87):

```lean
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
      (U₁ : Matrix m (Fin r) ℝ) (Ŝ₁ : Matrix (Fin r) (Fin r) ℝ) (K : ℝ → Matrix m (Fin r) ℝ)
      (S : ℝ → Matrix (Fin r) (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ),
      Y₀ = U₀ * S₀ * V₀ᵀ ∧ IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf ∧ Y₁ = U₁ * (Lf t₁)ᵀ
```

`MatrixKSL.isTubeLocal_stepRel` in [`LeanDLRA/Integrators/Matrix/KSLRun.lean`, lines 271–273](../LeanDLRA/Integrators/Matrix/KSLRun.lean#L271-L273):

```lean
theorem isTubeLocal_stepRel (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) :
    StepMethod.IsTubeLocal (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => stepRel G r)
      (fun Y => Y.rank ≤ r) 4
```

`MatrixKSL.exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Matrix/KSLRun.lean`, lines 303–313](../LeanDLRA/Integrators/Matrix/KSLRun.lean#L303-L313):

```lean
theorem exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) * (10 * L * B * h + ε) + 4 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * δ + T * Real.exp (L * T) * (10 * L * B * h + ε)
```

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

`MatrixParallelBUG.IsStep` in [`LeanDLRA/Integrators/Matrix/ParallelBUG.lean`, lines 233–256](../LeanDLRA/Integrators/Matrix/ParallelBUG.lean#L233-L256):

```lean
structure IsStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ) (U₀ : Matrix m r ℝ)
    (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) (U₁ : Matrix m s ℝ) (V₁ : Matrix n s' ℝ)
    (K : ℝ → Matrix m r ℝ) (Lf : ℝ → Matrix n r ℝ) (Sb : ℝ → Matrix r r ℝ) : Prop where
  orthU₀ : U₀ᵀ * U₀ = 1
  orthV₀ : V₀ᵀ * V₀ = 1
  /-- K-step (3.1): `K' = F(t, K V₀ᵀ) V₀`. -/
  kSol : ODESolution (kField V₀ F) K t₀ t₁
  kStart : K t₀ = U₀ * S₀
  /-- L-step (3.2): `L' = F(t, U₀ Lᵀ)ᵀ U₀`. -/
  lSol : ODESolution (lField U₀ F) Lf t₀ t₁
  lStart : Lf t₀ = V₀ * S₀ᵀ
  /-- S-step (3.3): `S̄' = U₀ᵀ F(t, U₀ S̄ V₀ᵀ) V₀`. -/
  sSol : ODESolution (sField U₀ V₀ F) Sb t₀ t₁
  sStart : Sb t₀ = S₀
  /-- The new left directions are orthogonal to `U₀`. -/
  perpU : U₁ᵀ * U₀ = 0
  /-- `Û = (U₀, Ũ₁)` captures `(U₀, K(t₁))`: its range contains the range of `(U₀, K(t₁))`
  (`Ũ₁` may contain further directions and need not be orthonormal). -/
  capU : U₁ * U₁ᵀ * ((1 - U₀ * U₀ᵀ) * K t₁) = (1 - U₀ * U₀ᵀ) * K t₁
  /-- The new right directions are orthogonal to `V₀`. -/
  perpV : V₁ᵀ * V₀ = 0
  /-- `V̂ = (V₀, Ṽ₁)` captures `(V₀, L(t₁))`: its range contains the range of `(V₀, L(t₁))`
  (`Ṽ₁` may contain further directions and need not be orthonormal). -/
  capV : V₁ * V₁ᵀ * ((1 - V₀ * V₀ᵀ) * Lf t₁) = (1 - V₀ * V₀ᵀ) * Lf t₁
```

`MatrixParallelBUG.augmentedRel` in [`LeanDLRA/Integrators/Matrix/ParallelBUGStep.lean`, lines 176–182](../LeanDLRA/Integrators/Matrix/ParallelBUGStep.lean#L176-L182):

```lean
def augmentedRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
      (K : ℝ → Matrix m (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ)
      (Sb : ℝ → Matrix (Fin r) (Fin r) ℝ),
      Y₀ = U₀ * S₀ * V₀ᵀ ∧ IsStep F t₀ t₁ U₀ S₀ V₀ (1 - U₀ * U₀ᵀ) (1 - V₀ * V₀ᵀ) K Lf Sb ∧
        Y₁ = augmented U₀ (1 - U₀ * U₀ᵀ) V₀ (1 - V₀ * V₀ᵀ) (Sb t₁) (K t₁) (Lf t₁)
```

`MatrixParallelBUG.stepRel` in [`LeanDLRA/Integrators/Matrix/ParallelBUGStep.lean`, lines 189–191](../LeanDLRA/Integrators/Matrix/ParallelBUGStep.lean#L189-L191):

```lean
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ Yh : Matrix m n ℝ, augmentedRel F r t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧ ‖Y₁ - Yh‖ ≤ distLR r Yh
```

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

`MatrixParallelBUG.isTubeLocal_stepRel` in [`LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean`, lines 289–291](../LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean#L289-L291):

```lean
theorem isTubeLocal_stepRel (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) :
    StepMethod.IsTubeLocal (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => stepRel G r)
      (fun Y => Y.rank ≤ r) 2
```

`MatrixParallelBUG.exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean`, lines 323–334](../LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean#L323-L334):

```lean
theorem exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) * (24 * L * B * h + 3 * ε)
      + 2 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * δ + T * Real.exp (L * T) * (24 * L * B * h + 3 * ε)
```

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

`MatrixParallelBUG.global_error_paper` in [`LeanDLRA/Integrators/Matrix/ParallelBUG.lean`, lines 510–530](../LeanDLRA/Integrators/Matrix/ParallelBUG.lean#L510-L530):

```lean
theorem global_error_paper {rk sU sV : ℕ → ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {L B ε Lt : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hε0 : 0 ≤ ε) (hLt : 0 ≤ Lt) (hFt : ∀ t s x, ‖F t x - F s x‖ ≤ Lt * |t - s|)
    {t₀ h : ℝ} (hh : 0 < h) {N : ℕ} {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {U : (k : ℕ) → Matrix m (Fin (rk k)) ℝ}
    {V : (k : ℕ) → Matrix n (Fin (rk k)) ℝ} {S : (k : ℕ) → Matrix (Fin (rk k)) (Fin (rk k)) ℝ}
    {W : (k : ℕ) → Matrix m (Fin (sU k)) ℝ} {Z : (k : ℕ) → Matrix n (Fin (sV k)) ℝ}
    {K : (k : ℕ) → ℝ → Matrix m (Fin (rk k)) ℝ} {Lf : (k : ℕ) → ℝ → Matrix n (Fin (rk k)) ℝ}
    {Sb : (k : ℕ) → ℝ → Matrix (Fin (rk k)) (Fin (rk k)) ℝ} {Φ : ℕ → ℝ → Matrix m n ℝ}
    (hstep : ∀ k < N, IsStep F (t₀ + k * h) (t₀ + (k + 1) * h) (U k) (S k) (V k) (W k) (Z k)
      (K k) (Lf k) (Sb k))
    (hε : ∀ k < N,
      ‖(1 - U k * (U k)ᵀ) * F (t₀ + k * h) (U k * S k * (V k)ᵀ) * (1 - V k * (V k)ᵀ)‖ ≤ ε)
    (hΦ : ∀ k < N, ODESolution F (Φ k) (t₀ + k * h) (t₀ + (k + 1) * h))
    (hΦ₀ : ∀ k < N, Φ k (t₀ + k * h) = U k * S k * (V k)ᵀ) {ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (htr : ∀ k < N, ‖U (k + 1) * S (k + 1) * (V (k + 1))ᵀ - augmented (U k) (W k) (V k) (Z k)
      (Sb k (t₀ + (k + 1) * h)) (K k (t₀ + (k + 1) * h)) (Lf k (t₀ + (k + 1) * h))‖ ≤ ϑ)
    {δ T : ℝ} (hδ : ‖U 0 * S 0 * (V 0)ᵀ - A t₀‖ ≤ δ) :
    ∀ k ≤ N, (k : ℝ) * h ≤ T → ‖U k * S k * (V k)ᵀ - A (t₀ + k * h)‖ ≤
      Real.exp (L * T) * δ + (7 * L * B + Lt) * T * Real.exp (L * T) * h
        + T * Real.exp (L * T) * ε + T * Real.exp (L * T) * (ϑ / h)
```

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

`MatrixParallelBUG.adaptiveStepRel` in [`LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean`, lines 115–117](../LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean#L115-L117):

```lean
def adaptiveStepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (R : Set ℕ) (ϑ : ℝ) :
    StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ => ∃ r ∈ R, ∃ Yh : Matrix m n ℝ, augmentedRel F r t₀ t₁ Y₀ Yh ∧ ‖Y₁ - Yh‖ ≤ ϑ
```

`MatrixParallelBUG.isTubeLocal_adaptiveStepRel_Ici` in [`LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean`, lines 264–268](../LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean#L264-L268):

```lean
theorem isTubeLocal_adaptiveStepRel_Ici (hϑ : 0 ≤ ϑ) (hrm : r₀ ≤ Fintype.card m)
    (hrn : r₀ ≤ Fintype.card n) :
    StepMethod.IsTubeLocal
      (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => adaptiveStepRel G (Set.Ici r₀) ϑ)
      (fun _ => True) 2
```

`MatrixParallelBUG.adaptive_exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean`, lines 428–440](../LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean#L428-L440):

```lean
theorem adaptive_exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : ∀ r ∈ Set.Ici r₀, FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε)
    (hε₀ : 0 ≤ ε) (hϑ : 0 ≤ ϑ) (hh : 0 ≤ h) (hNT : N * h ≤ T)
    (hrm : r₀ ≤ Fintype.card m) (hrn : r₀ ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * (δ + N * ϑ) + T * Real.exp (L * T) * (7 * L * B * h + ε) +
      2 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (adaptiveStepRel F (Set.Ici r₀) ϑ) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * (δ + n * ϑ) + T * Real.exp (L * T) * (7 * L * B * h + ε)
```

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

`MatrixBUG.IsRankAdaptiveStep` in [`LeanDLRA/Integrators/Matrix/BUG.lean`, lines 682–709](../LeanDLRA/Integrators/Matrix/BUG.lean#L682-L709):

```lean
structure IsRankAdaptiveStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (ϑ : ℝ) (t₀ t₁ : ℝ)
    (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (Ua : Matrix m k ℝ) (Va : Matrix n k' ℝ) (K : ℝ → Matrix m (Fin r) ℝ)
    (Lf : ℝ → Matrix n (Fin r) ℝ) (Sa : ℝ → Matrix k k' ℝ) (Y₁ : Matrix m n ℝ) : Prop where
  orthU₀ : U₀ᵀ * U₀ = 1
  orthV₀ : V₀ᵀ * V₀ = 1
  /-- K-step `K' = F(t, K V₀ᵀ) V₀`. -/
  kSol : ODESolution (kField V₀ F) K t₀ t₁
  kStart : K t₀ = U₀ * S₀
  /-- L-step `L' = F(t, U₀ Lᵀ)ᵀ U₀`. -/
  lSol : ODESolution (lField U₀ F) Lf t₀ t₁
  lStart : Lf t₀ = V₀ * S₀ᵀ
  orthUa : Uaᵀ * Ua = 1
  /-- `Û` captures `K(t₁)`. -/
  kCap : Ua * Uaᵀ * K t₁ = K t₁
  /-- `Û` captures `U₀` (augmentation). -/
  augU : Ua * Uaᵀ * U₀ = U₀
  orthVa : Vaᵀ * Va = 1
  /-- `V̂` captures `L(t₁)`. -/
  lCap : Va * Vaᵀ * Lf t₁ = Lf t₁
  /-- `V̂` captures `V₀` (augmentation). -/
  augV : Va * Vaᵀ * V₀ = V₀
  /-- Galerkin S-step `Ŝ' = Ûᵀ F(t, Û Ŝ V̂ᵀ) V̂` in the augmented bases. -/
  sSol : ODESolution (sField Ua Va F) Sa t₀ t₁
  /-- `Ŝ(t₀) = M̂ S₀ N̂ᵀ` with `M̂ = Ûᵀ U₀`, `N̂ = V̂ᵀ V₀`. -/
  sStart : Sa t₀ = Uaᵀ * U₀ * S₀ * (V₀ᵀ * Va)
  /-- Truncation to the tolerance `ϑ`. -/
  trunc : ‖Y₁ - Ua * Sa t₁ * Vaᵀ‖ ≤ ϑ
```

`MatrixBUG.rankAdaptive_global_error_le` in [`LeanDLRA/Integrators/Matrix/BUG.lean`, lines 860–877](../LeanDLRA/Integrators/Matrix/BUG.lean#L860-L877):

```lean
theorem rankAdaptive_global_error_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε₀ : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ}
    {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ (t₀ + N * h)) {r ka kb : ℕ → ℕ}
    {U : (j : ℕ) → Matrix m (Fin (r j)) ℝ} {Sm : (j : ℕ) → Matrix (Fin (r j)) (Fin (r j)) ℝ}
    {V : (j : ℕ) → Matrix n (Fin (r j)) ℝ} {Ua : (j : ℕ) → Matrix m (Fin (ka j)) ℝ}
    {Va : (j : ℕ) → Matrix n (Fin (kb j)) ℝ} {K : (j : ℕ) → ℝ → Matrix m (Fin (r j)) ℝ}
    {Lf : (j : ℕ) → ℝ → Matrix n (Fin (r j)) ℝ}
    {Sa : (j : ℕ) → ℝ → Matrix (Fin (ka j)) (Fin (kb j)) ℝ} {Φ : ℕ → ℝ → Matrix m n ℝ}
    (hε : ∀ j < N, FactoredNormalBound F (r j) ε)
    (hstep : ∀ j < N, IsRankAdaptiveStep F ϑ (t₀ + j * h) (t₀ + (j + 1) * h) (U j) (Sm j) (V j)
      (Ua j) (Va j) (K j) (Lf j) (Sa j) (U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = U j * Sm j * (V j)ᵀ) {δ T : ℝ}
    (hδ : ‖U 0 * Sm 0 * (V 0)ᵀ - A t₀‖ ≤ δ) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖U j * Sm j * (V j)ᵀ - A (t₀ + j * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * bugC₁ L H * ε + T * Real.exp (L * T) * bugC₂ L B H * h
        + Real.exp (L * T) * j * ϑ
```

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

`AugmentationRank.exists_error_ge_of_isRankAdaptiveStep` in [`LeanDLRA/Research/AugmentationRank.lean`, lines 598–614](../LeanDLRA/Research/AugmentationRank.lean#L598-L614):

```lean
theorem exists_error_ge_of_isRankAdaptiveStep.{u} :
    ∃ (F : Matrix (Fin 3) (Fin 2) ℝ → Matrix (Fin 3) (Fin 2) ℝ)
      (U₀ : Matrix (Fin 3) (Fin 1) ℝ) (V₀ : Matrix (Fin 2) (Fin 1) ℝ)
      (A : ℝ → Matrix (Fin 3) (Fin 2) ℝ),
      FactoredNormalBoundOn (fun _ => F) 1 Set.univ 0 ∧
      U₀ᵀ * U₀ = 1 ∧ V₀ᵀ * V₀ = 1 ∧ A 0 = U₀ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * V₀ᵀ ∧
      (∀ h : ℝ, ODESolution (fun _ => F) A 0 h) ∧
      (∀ h : ℝ, ∃ (Ua : Matrix (Fin 3) (Fin 2) ℝ) (Va : Matrix (Fin 2) (Fin 2) ℝ)
        (K : ℝ → Matrix (Fin 3) (Fin 1) ℝ) (Lf : ℝ → Matrix (Fin 2) (Fin 1) ℝ)
        (Sa : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (Y₁ : Matrix (Fin 3) (Fin 2) ℝ),
        IsRankAdaptiveStep (fun _ => F) 0 0 h U₀ 1 V₀ Ua Va K Lf Sa Y₁) ∧
      ∀ (h ϑ : ℝ), 0 < h → ∀ (k' : Type u) [Fintype k'] [DecidableEq k']
        (Ua : Matrix (Fin 3) (Fin 2) ℝ) (Va : Matrix (Fin 2) k' ℝ)
        (K : ℝ → Matrix (Fin 3) (Fin 1) ℝ) (Lf : ℝ → Matrix (Fin 2) (Fin 1) ℝ)
        (Sa : ℝ → Matrix (Fin 2) k' ℝ) (Y₁ : Matrix (Fin 3) (Fin 2) ℝ),
        IsRankAdaptiveStep (fun _ => F) ϑ 0 h U₀ 1 V₀ Ua Va K Lf Sa Y₁ →
        h ^ 2 / 2 - ϑ ≤ ‖Y₁ - A h‖
```

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

`MatrixBUG.truncStepRel` in [`LeanDLRA/Integrators/Matrix/AdaptiveBUGStep.lean`, lines 366–369](../LeanDLRA/Integrators/Matrix/AdaptiveBUGStep.lean#L366-L369):

```lean
def truncStepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) (κ : ℝ) :
    StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ => ∃ Yh : Matrix m n ℝ, augmentedRel F r t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧
    ‖Y₁ - Yh‖ ≤ κ * distLR r Yh
```

`MatrixBUG.trunc_exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Matrix/TruncBUGRun.lean`, lines 239–251](../LeanDLRA/Integrators/Matrix/TruncBUGRun.lean#L239-L251):

```lean
theorem trunc_exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hκ : 1 ≤ κ) (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) *
      (κ * (10 * L * B * h + ε) + (1 + κ) * (bugC₁ L H * ε + bugC₂ L B H * h)) + 4 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (truncStepRel F r κ) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ +
        T * Real.exp (L * T) *
          (κ * (10 * L * B * h + ε) + (1 + κ) * (bugC₁ L H * ε + bugC₂ L B H * h))
```

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

`MatrixBUG.isTubeLocal_adaptiveStepRel_Ici` in [`LeanDLRA/Integrators/Matrix/AdaptiveBUGRun.lean`, lines 126–130](../LeanDLRA/Integrators/Matrix/AdaptiveBUGRun.lean#L126-L130):

```lean
theorem isTubeLocal_adaptiveStepRel_Ici (hϑ : 0 ≤ ϑ) (hrm : r₀ ≤ Fintype.card m)
    (hrn : r₀ ≤ Fintype.card n) :
    StepMethod.IsTubeLocal
      (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => adaptiveStepRel G (Set.Ici r₀) ϑ)
      (fun _ => True) 4
```

`MatrixBUG.adaptive_exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Matrix/AdaptiveBUGRun.lean`, lines 236–247](../LeanDLRA/Integrators/Matrix/AdaptiveBUGRun.lean#L236-L247):

```lean
theorem adaptive_exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : ∀ r ∈ Set.Ici r₀, FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε)
    (hε₀ : 0 ≤ ε) (hϑ : 0 ≤ ϑ) (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hrm : r₀ ≤ Fintype.card m) (hrn : r₀ ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : bugGlobalBound L B H T δ ε h + Real.exp (L * T) * (N * ϑ) + 4 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (adaptiveStepRel F (Set.Ici r₀) ϑ) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
        bugGlobalBound L B H T δ ε h + Real.exp (L * T) * (n * ϑ)
```

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

`rankAdaptiveBUG_aposteriori_global_error` in [`LeanDLRA/Integrators/RankAdaptiveBUGAposteriori.lean`, lines 306–314](../LeanDLRA/Integrators/RankAdaptiveBUGAposteriori.lean#L306-L314):

```lean
theorem rankAdaptiveBUG_aposteriori_global_error (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h))
    {P Q Pa Qa : ℕ → E →L[ℝ] E} {Y : ℕ → E} {YK YL YS : ℕ → ℝ → E} {ϑ η : ℕ → ℝ}
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε (ϑ n) (P n) (Q n) (Pa n) (Qa n) (t₀ + n * h)
      (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hη : ∀ n < N, ∀ t ∈ Icc (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖F t (YS n t) - Pa n (Qa n (F t (YS n t)))‖ ≤ η n) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (L * (n * h)) * (‖Y 0 - A t₀‖ + ∑ k ∈ range n, (ϑ k + h * η k))
```

`rankAdaptiveBUG_global_error_of_tol` in [`LeanDLRA/Integrators/RankAdaptiveBUGAposteriori.lean`, lines 394–405](../LeanDLRA/Integrators/RankAdaptiveBUGAposteriori.lean#L394-L405):

```lean
theorem rankAdaptiveBUG_global_error_of_tol (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ}
    {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q Pa Qa : ℕ → E →L[ℝ] E}
    {Y : ℕ → E} {YK YL YS Φ : ℕ → ℝ → E} {ϑ : ℕ → ℝ}
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε (ϑ n) (P n) (Q n) (Pa n) (Qa n) (t₀ + n * h)
      (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {τ : ℝ} (hτ : 0 ≤ τ)
    (hϑ : ∀ n < N, ϑ n ≤ τ * h ^ 2) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * (δ + T * (bugC₁ L H * ε + (bugC₂ L B H + τ) * h))
```

`singularValues_pred_epsRank_gt` in [`LeanDLRA/Integrators/RankSelection.lean`, lines 49–52](../LeanDLRA/Integrators/RankSelection.lean#L49-L52):

```lean
theorem singularValues_pred_epsRank_gt [DecidableEq n] (A : Matrix m n ℝ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hpos : 0 < epsRank θ A) :
    θ / √((Fintype.card n - epsRank θ A + 1 : ℕ) : ℝ) <
      (toEuclideanLin A).singularValues (epsRank θ A - 1)
```

The two files [`Integrators/RankAdaptiveBUGAposteriori.lean`](../LeanDLRA/Integrators/RankAdaptiveBUGAposteriori.lean) and
[`Integrators/RankSelection.lean`](../LeanDLRA/Integrators/RankSelection.lean) extend the global bound of this section on the
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

### 6.4 The BUG integrator with explicit Euler substeps

`MatrixEulerBUG.IsStep` in [`LeanDLRA/Integrators/Matrix/EulerBUGStep.lean`, lines 150–170](../LeanDLRA/Integrators/Matrix/EulerBUGStep.lean#L150-L170):

```lean
structure IsStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ) (U₀ : Matrix m k ℝ)
    (S₀ : Matrix k k ℝ) (V₀ : Matrix n k ℝ) (Ua : Matrix m s ℝ) (Sa : Matrix s s' ℝ)
    (Va : Matrix n s' ℝ) : Prop where
  /-- The old column basis is orthonormal. -/
  orthU₀ : U₀ᵀ * U₀ = 1
  /-- The old row basis is orthonormal. -/
  orthV₀ : V₀ᵀ * V₀ = 1
  /-- The new column basis is orthonormal. -/
  orthUa : Uaᵀ * Ua = 1
  /-- The new row basis is orthonormal. -/
  orthVa : Vaᵀ * Va = 1
  /-- The range of the new column basis contains the old column basis. -/
  capU : Ua * Uaᵀ * U₀ = U₀
  /-- K-step: the range of the new column basis contains the columns of `F₀ V₀`. -/
  capK : Ua * Uaᵀ * (F t₀ (U₀ * S₀ * V₀ᵀ) * V₀) = F t₀ (U₀ * S₀ * V₀ᵀ) * V₀
  /-- The range of the new row basis contains the old row basis. -/
  capV : Va * Vaᵀ * V₀ = V₀
  /-- L-step: the range of the new row basis contains the columns of `F₀ᵀ U₀`. -/
  capL : Va * Vaᵀ * ((F t₀ (U₀ * S₀ * V₀ᵀ))ᵀ * U₀) = (F t₀ (U₀ * S₀ * V₀ᵀ))ᵀ * U₀
  /-- S-step: the Galerkin projection of the explicit Euler step onto the new bases. -/
  sStep : Sa = Uaᵀ * (U₀ * S₀ * V₀ᵀ + (t₁ - t₀) • F t₀ (U₀ * S₀ * V₀ᵀ)) * Va
```

`MatrixEulerBUG.augmentedRel` in [`LeanDLRA/Integrators/Matrix/EulerBUGStep.lean`, lines 289–295](../LeanDLRA/Integrators/Matrix/EulerBUGStep.lean#L289-L295):

```lean
def augmentedRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
      (s s' : ℕ) (Ua : Matrix m (Fin s) ℝ) (Sa : Matrix (Fin s) (Fin s') ℝ)
      (Va : Matrix n (Fin s') ℝ),
      Y₀ = U₀ * S₀ * V₀ᵀ ∧ s ≤ 2 * r ∧ s' ≤ 2 * r ∧ IsStep F t₀ t₁ U₀ S₀ V₀ Ua Sa Va ∧
        Y₁ = Ua * Sa * Vaᵀ
```

`MatrixEulerBUG.stepRel` in [`LeanDLRA/Integrators/Matrix/EulerBUGStep.lean`, lines 304–306](../LeanDLRA/Integrators/Matrix/EulerBUGStep.lean#L304-L306):

```lean
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ => ∃ Yh : Matrix m n ℝ, augmentedRel F r t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧
    ‖Y₁ - Yh‖ ≤ distLR r Yh
```

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

`MatrixEulerBUG.exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Matrix/EulerBUGRun.lean`, lines 343–357](../LeanDLRA/Integrators/Matrix/EulerBUGRun.lean#L343-L357):

```lean
theorem exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → (s, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ →
      (t, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ → ‖F t x - F s x‖ ≤ Lt * (t - s))
    (hh : 0 ≤ h) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ +
      T * Real.exp (L * T) * ((11 * L * B + Lt) * h + 3 * ε) + 2 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * δ + T * Real.exp (L * T) * ((11 * L * B + Lt) * h + 3 * ε)
```

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

`midpointBUG_global_error_le` in [`LeanDLRA/HighOrder/MidpointBUGGlobal.lean`, lines 385–405](../LeanDLRA/HighOrder/MidpointBUGGlobal.lean#L385-L405):

```lean
theorem midpointBUG_global_error_le {F : ℝ → E → E} {L B M₁ M₂ ε ε₂ ϑ : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hF₂ : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂) (hε : 0 ≤ ε) (hε₂ : 0 ≤ ε₂)
    {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q Ph Qh R : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YK YL YH YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsMidpointBUGStep F ε ε₂ ϑ (P n) (Q n) (Ph n) (Qh n) (R n) (t₀ + n * h) h
      (Y n) (YK n) (YL n) (YH n) (YS n) (Y (n + 1)))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H
          * ε₂
        + T * Real.exp (L * T) * midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H
          * (h * ε)
        + T * Real.exp (L * T) * midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H
          * h ^ 2
        + Real.exp (L * T) * n * ϑ
```

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

`MatrixMidpointBUG.augmentedRel` in [`LeanDLRA/HighOrder/Defs.lean`, lines 97–105](../LeanDLRA/HighOrder/Defs.lean#L97-L105):

```lean
def augmentedRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
      (Uh : Matrix m (Fin (2 * r)) ℝ) (Vh : Matrix n (Fin (2 * r)) ℝ)
      (K : ℝ → Matrix m (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ)
      (Sh : ℝ → Matrix (Fin (2 * r)) (Fin (2 * r)) ℝ) (l l' : ℕ) (Ub : Matrix m (Fin l) ℝ)
      (Vb : Matrix n (Fin l') ℝ) (Sb : ℝ → Matrix (Fin l) (Fin l') ℝ),
      Y₀ = U₀ * S₀ * V₀ᵀ ∧ l ≤ 4 * r ∧ l' ≤ 4 * r ∧
        IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb ∧ Y₁ = Ub * Sb t₁ * Vbᵀ
```

`MatrixMidpointBUG.stepRel` in [`LeanDLRA/HighOrder/Defs.lean`, lines 114–116](../LeanDLRA/HighOrder/Defs.lean#L114-L116):

```lean
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ => ∃ Yh : Matrix m n ℝ, augmentedRel F r t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧
    ‖Y₁ - Yh‖ ≤ distLR r Yh
```

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

`MatrixMidpointBUG.stepRel.hasLocalError` in [`LeanDLRA/HighOrder/MidpointBUGStep.lean`, lines 518–530](../LeanDLRA/HighOrder/MidpointBUGStep.lean#L518-L530):

```lean
theorem stepRel.hasLocalError (h : stepRel F r t₀ t₁ Y₀ Y₁)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε) (hε₀ : 0 ≤ ε)
    (hε₂ : FactoredNormalBoundOn F (2 * r) (tubeSet A a b ρ) ε₂)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hF₂ : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂)
    (hAc : ContinuousOn A (Icc a b)) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁)
    (hH : t₁ - t₀ ≤ H) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 3 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Y₁ ((t₁ - t₀) * (Real.exp (L * H) * ε +
      2 * MidpointBUG.midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H *
        ((t₁ - t₀) ^ 2 + (t₁ - t₀) * ε + ε₂)))
```

The local error of one step. The normal bounds `ε` at rank `r` and `ε₂` at rank `2 r` hold on a
tube around a solution `A` (`FactoredNormalBoundOn`); `F` is `L`-Lipschitz, bounded by `B` and
of class `C²` with `‖DF‖ ≤ M₁` and `‖D²F‖ ≤ M₂` as a map of `(t, Y)`; the start value is near the
solution (`hsmall`). Then the local error is at most
`h (e^{L H} ε + 2 C (h² + h ε + ε₂))` with `h = t₁ - t₀ ≤ H` and the constant `C` of the theorem
above. The step without truncation has the local error `C h (h² + h ε + ε₂)`
(`MatrixMidpointBUG.augmentedRel.hasLocalError`). Both are taken from the projector form
(`MatrixMidpointBUG.IsStep.isMidpointBUGStep` is the bridge) and are not proved a second time.

`MatrixMidpointBUG.isTubeLocal_stepRel` in [`LeanDLRA/HighOrder/MidpointBUGRun.lean`, lines 208–210](../LeanDLRA/HighOrder/MidpointBUGRun.lean#L208-L210):

```lean
theorem isTubeLocal_stepRel (hrm : 2 * r ≤ Fintype.card m) (hrn : 2 * r ≤ Fintype.card n) :
    StepMethod.IsTubeLocal (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => stepRel G r)
      (fun Y => Y.rank ≤ r) 2
```

`MatrixMidpointBUG.exists_run_norm_sub_le` in [`LeanDLRA/HighOrder/MidpointBUGRun.lean`, lines 328–346](../LeanDLRA/HighOrder/MidpointBUGRun.lean#L328-L346):

```lean
theorem exists_run_norm_sub_le
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hF₂ : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂)
    (hA : ODESolution F A t₀ (t₀ + N * h))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hε₂ : FactoredNormalBoundOn F (2 * r) (tubeSet A t₀ (t₀ + N * h) ρ) ε₂) (hε₂₀ : 0 ≤ ε₂)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hrm : 2 * r ≤ Fintype.card m) (hrn : 2 * r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) * (Real.exp (L * H) * ε +
      2 * MidpointBUG.midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H *
        (h ^ 2 + h * ε + ε₂)) + 3 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ +
        T * Real.exp (L * T) * (Real.exp (L * H) * ε +
          2 * MidpointBUG.midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H *
            (h ^ 2 + h * ε + ε₂))
```

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

`ODESolution.norm_midpoint_defect_le` in [`LeanDLRA/Research/ExplicitMidpointGalerkin.lean`, lines 87–91](../LeanDLRA/Research/ExplicitMidpointGalerkin.lean#L87-L91):

```lean
theorem ODESolution.norm_midpoint_defect_le [InnerProductSpace ℝ E] {F : ℝ → E → E}
    {A : ℝ → E} {t₀ h M₃ : ℝ} (hh : 0 < h) (hA : ODESolution F A t₀ (t₀ + h))
    (hA3 : ContDiffOn ℝ 3 A (Icc t₀ (t₀ + h)))
    (hM₃ : ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 3 A (Icc t₀ (t₀ + h)) t‖ ≤ M₃) :
    ‖A (t₀ + h) - A t₀ - h • F (t₀ + h / 2) (A (t₀ + h / 2))‖ ≤ M₃ * h ^ 3 / 24
```

Midpoint-rule defect of an exact solution: if `A` solves `y' = F(t, y)` on `[t₀, t₀ + h]`, is of
class `C³` there and its third derivative is bounded by `M₃`, then the defect is at most
`M₃ h³ / 24`. The constant is the sharp one of `MidpointBUG.midpoint_defect_le_sharp`. The
companion `ODESolution.norm_half_step_sub_le` gives, for `C²` and the bound `M₂` of the second
derivative, `‖A(t₀ + h/2) - A t₀ - (h/2) F(t₀, A t₀)‖ ≤ M₂ h² / 8`.

`ExplicitMidpoint.norm_one_sub_galerkinProj_le_of_capture` in [`LeanDLRA/Research/ExplicitMidpointGalerkin.lean`, lines 180–184](../LeanDLRA/Research/ExplicitMidpointGalerkin.lean#L180-L184):

```lean
theorem norm_one_sub_galerkinProj_le_of_capture [DecidableEq k] (hUa : Uaᵀ * Ua = 1)
    (kCap : Ua * Uaᵀ * (G * V₀) = G * V₀) (lCap : Va * Vaᵀ * (Gᵀ * U₀) = Gᵀ * U₀) {θ θ' : ℝ}
    (hθ : ‖(1 - Ua * Uaᵀ) * G * (1 - V₀ * V₀ᵀ)‖ ≤ θ)
    (hθ' : ‖(1 - U₀ * U₀ᵀ) * G * (1 - Va * Vaᵀ)‖ ≤ θ') :
    ‖(1 - galerkinProj Ua Va) G‖ ≤ θ + θ'
```

`ExplicitMidpoint.norm_predictor_sub_le` in [`LeanDLRA/Research/ExplicitMidpointGalerkin.lean`, lines 202–211](../LeanDLRA/Research/ExplicitMidpointGalerkin.lean#L202-L211):

```lean
theorem norm_predictor_sub_le {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {D : Set (ℝ × Matrix m n ℝ)} {ε M₂ : ℝ} (hN : FactoredNormalBoundOn F r D ε)
    {S₀ : Matrix (Fin r) (Fin r) ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {t₀ h : ℝ}
    (hh : 0 < h) (hD₀ : (t₀, U₀ * S₀ * V₀ᵀ) ∈ D) {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t₀ (t₀ + h)) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    (hA2 : ContDiffOn ℝ 2 A (Icc t₀ (t₀ + h)))
    (hM₂ : ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 2 A (Icc t₀ (t₀ + h)) t‖ ≤ M₂)
    {Z : Matrix m n ℝ}
    (hZ : Z = U₀ * S₀ * V₀ᵀ + (h / 2) • tangentProj U₀ V₀ (F t₀ (U₀ * S₀ * V₀ᵀ))) :
    ‖Z - A (t₀ + h / 2)‖ ≤ M₂ * h ^ 2 / 8 + h / 2 * ε
```

Two ingredients. If `Ua`, `Va` capture `G V₀` and `Gᵀ U₀` and the capture defects are at most `θ`
and `θ'`, then `G` is at most `θ + θ'` away from the Galerkin space of `Ua`, `Va`; the identity
behind it splits `G - galerkinProj Ua Va G` into one term for each defect
(`ExplicitMidpoint.sub_galerkin_eq_of_capture`). If the normal component of `F` is at most `ε` at
the factored point `Y₀`, the predictor is within `M₂ h² / 8 + (h/2) ε` of the exact solution at
the midpoint of the step.

`ExplicitMidpoint.galerkin_local_error` in [`LeanDLRA/Research/ExplicitMidpointGalerkin.lean`, lines 237–259](../LeanDLRA/Research/ExplicitMidpointGalerkin.lean#L237-L259):

```lean
theorem galerkin_local_error [DecidableEq k] [DecidableEq k']
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {D : Set (ℝ × Matrix m n ℝ)}
    {L Lₜ B ε M₂ M₃ θ θ' : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hFt : ∀ s t x, ‖F s x - F t x‖ ≤ Lₜ * |s - t|)
    (hN : FactoredNormalBoundOn F r D ε) {S₀ : Matrix (Fin r) (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {t₀ h : ℝ} (hh : 0 < h)
    (hD₀ : (t₀, U₀ * S₀ * V₀ᵀ) ∈ D) {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ (t₀ + h))
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) (hA3 : ContDiffOn ℝ 3 A (Icc t₀ (t₀ + h)))
    (hM₂ : ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 2 A (Icc t₀ (t₀ + h)) t‖ ≤ M₂)
    (hM₃ : ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 3 A (Icc t₀ (t₀ + h)) t‖ ≤ M₃)
    {Z : Matrix m n ℝ}
    (hZ : Z = U₀ * S₀ * V₀ᵀ + (h / 2) • tangentProj U₀ V₀ (F t₀ (U₀ * S₀ * V₀ᵀ)))
    (hG : G = F (t₀ + h / 2) Z) (hUa : Uaᵀ * Ua = 1) (hVa : Vaᵀ * Va = 1)
    (augU : Ua * Uaᵀ * U₀ = U₀) (augV : Va * Vaᵀ * V₀ = V₀)
    (kCap : Ua * Uaᵀ * (G * V₀) = G * V₀) (lCap : Va * Vaᵀ * (Gᵀ * U₀) = Gᵀ * U₀)
    (hθ : ‖(1 - Ua * Uaᵀ) * G * (1 - V₀ * V₀ᵀ)‖ ≤ θ)
    (hθ' : ‖(1 - U₀ * U₀ᵀ) * G * (1 - Va * Vaᵀ)‖ ≤ θ') {YS : ℝ → Matrix m n ℝ}
    (hS : ODESolution (fun t X => galerkinProj Ua Va (F t X)) YS t₀ (t₀ + h))
    (hS₀ : YS t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖YS (t₀ + h) - A (t₀ + h)‖ ≤
      (Real.exp (L * h) - 1) *
          (h * ((L * B + Lₜ) * h / 2 + L * (M₂ * h ^ 2 / 8 + h / 2 * ε) + (θ + θ'))) +
        (h * (L * (M₂ * h ^ 2 / 8 + h / 2 * ε) + (θ + θ')) + M₃ * h ^ 3 / 24)
```

The local error of the Galerkin step. With `η = M₂ h² / 8 + (h/2) ε` it is at most
`(e^{L h} - 1) h ((L B + Lₜ) h / 2 + L η + θ + θ') + h (L η + θ + θ') + M₃ h³ / 24`. The
hypotheses on the field are those of section 6.5: `F` is `L`-Lipschitz, bounded by `B` and
`Lₜ`-Lipschitz in time. The statement is an instance of `MidpointBUG.midpointGalerkin_local_error`
with the predictor of this section in place of a half step of the BUG integrator.

`ExplicitMidpoint.norm_update_sub_le` in [`LeanDLRA/Research/ExplicitMidpointGalerkin.lean`, lines 280–296](../LeanDLRA/Research/ExplicitMidpointGalerkin.lean#L280-L296):

```lean
theorem norm_update_sub_le [DecidableEq k] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {D : Set (ℝ × Matrix m n ℝ)} {L ε M₂ M₃ θ θ' : ℝ} (hF : IsLipschitzFieldOn F D L)
    (hL : 0 ≤ L) (hN : FactoredNormalBoundOn F r D ε) {S₀ : Matrix (Fin r) (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {t₀ h : ℝ} (hh : 0 < h)
    (hD₀ : (t₀, U₀ * S₀ * V₀ᵀ) ∈ D) {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ (t₀ + h))
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) (hA3 : ContDiffOn ℝ 3 A (Icc t₀ (t₀ + h)))
    (hM₂ : ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 2 A (Icc t₀ (t₀ + h)) t‖ ≤ M₂)
    (hM₃ : ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 3 A (Icc t₀ (t₀ + h)) t‖ ≤ M₃)
    {Z : Matrix m n ℝ}
    (hZ : Z = U₀ * S₀ * V₀ᵀ + (h / 2) • tangentProj U₀ V₀ (F t₀ (U₀ * S₀ * V₀ᵀ)))
    (hDZ : (t₀ + h / 2, Z) ∈ D) (hDA : (t₀ + h / 2, A (t₀ + h / 2)) ∈ D)
    (hG : G = F (t₀ + h / 2) Z) (hUa : Uaᵀ * Ua = 1)
    (kCap : Ua * Uaᵀ * (G * V₀) = G * V₀) (lCap : Va * Vaᵀ * (Gᵀ * U₀) = Gᵀ * U₀)
    (hθ : ‖(1 - Ua * Uaᵀ) * G * (1 - V₀ * V₀ᵀ)‖ ≤ θ)
    (hθ' : ‖(1 - U₀ * U₀ᵀ) * G * (1 - Va * Vaᵀ)‖ ≤ θ') :
    ‖U₀ * S₀ * V₀ᵀ + h • galerkinProj Ua Va G - A (t₀ + h)‖ ≤
      h * (θ + θ') + L * h ^ 2 * ε / 2 + h ^ 3 * (M₃ / 24 + L * M₂ / 8)
```

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

`norm_capture_defect_le` in [`LeanDLRA/Research/ExplicitMidpointCapture.lean`, lines 646–663](../LeanDLRA/Research/ExplicitMidpointCapture.lean#L646-L663):

```lean
theorem norm_capture_defect_le {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {r : ℕ}
    {D : Set (ℝ × Matrix m n ℝ)} {ε L Lₜ B ρ τ κ e δ : ℝ}
    (hN : FactoredNormalBoundOn F r D ε) (hL : IsLipschitzFieldOn F D L) (hL0 : 0 ≤ L)
    (hB : IsBoundedFieldOn F D B)
    (hFt : ∀ s t X, (s, X) ∈ D → (t, X) ∈ D → ‖F s X - F t X‖ ≤ Lₜ * |s - t|)
    (hrm : r < Fintype.card m) (hrn : r < Fintype.card n)
    {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {t₀ h : ℝ} (hh : 0 ≤ h) (hρ : 0 < ρ)
    (hD : ∀ t ∈ Icc t₀ (t₀ + h), ∀ X, ‖X - U₀ * S₀ * V₀ᵀ‖ ≤ ρ → (t, X) ∈ D)
    (hτ : 0 < τ) (hκ : Real.sqrt r * (ε / (2 * τ) + max L (2 * B / ρ)) ≤ κ)
    (he : Real.sqrt r * (ε + max L (2 * B / ρ) * τ / 2) ≤ e)
    (hδ : h * e + (h / 2) ^ 2 * (2 * κ * B + κ ^ 2 * ‖S₀‖) + (h / 2) ^ 3 * (κ ^ 2 * B) ≤ δ)
    (hsmall : h / 2 * B + δ ≤ ρ / 2) {Z G : Matrix m n ℝ}
    (hZ : Z = U₀ * S₀ * V₀ᵀ + (h / 2) • tangentProj U₀ V₀ (F t₀ (U₀ * S₀ * V₀ᵀ)))
    (hG : G = F (t₀ + h / 2) Z) {k : Type*} [Fintype k] [DecidableEq k] {Ua : Matrix m k ℝ}
    (hUa : Uaᵀ * Ua = 1) (augU : Ua * Uaᵀ * U₀ = U₀) (kCap : Ua * Uaᵀ * (G * V₀) = G * V₀) :
    ‖(1 - Ua * Uaᵀ) * G * (1 - V₀ * V₀ᵀ)‖ ≤
      (L + κ + h / 2 * L * κ) * δ + ε + e + (h / 2) ^ 2 * κ * (L * B + Lₜ + B * κ)
```

`norm_capture_defect_right_le` in [`LeanDLRA/Research/ExplicitMidpointCapture.lean`, lines 896–913](../LeanDLRA/Research/ExplicitMidpointCapture.lean#L896-L913):

```lean
theorem norm_capture_defect_right_le {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {r : ℕ}
    {D : Set (ℝ × Matrix m n ℝ)} {ε L Lₜ B ρ τ κ e δ : ℝ}
    (hN : FactoredNormalBoundOn F r D ε) (hL : IsLipschitzFieldOn F D L) (hL0 : 0 ≤ L)
    (hB : IsBoundedFieldOn F D B)
    (hFt : ∀ s t X, (s, X) ∈ D → (t, X) ∈ D → ‖F s X - F t X‖ ≤ Lₜ * |s - t|)
    (hrm : r < Fintype.card m) (hrn : r < Fintype.card n)
    {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {t₀ h : ℝ} (hh : 0 ≤ h) (hρ : 0 < ρ)
    (hD : ∀ t ∈ Icc t₀ (t₀ + h), ∀ X, ‖X - U₀ * S₀ * V₀ᵀ‖ ≤ ρ → (t, X) ∈ D)
    (hτ : 0 < τ) (hκ : Real.sqrt r * (ε / (2 * τ) + max L (2 * B / ρ)) ≤ κ)
    (he : Real.sqrt r * (ε + max L (2 * B / ρ) * τ / 2) ≤ e)
    (hδ : h * e + (h / 2) ^ 2 * (2 * κ * B + κ ^ 2 * ‖S₀‖) + (h / 2) ^ 3 * (κ ^ 2 * B) ≤ δ)
    (hsmall : h / 2 * B + δ ≤ ρ / 2) {Z G : Matrix m n ℝ}
    (hZ : Z = U₀ * S₀ * V₀ᵀ + (h / 2) • tangentProj U₀ V₀ (F t₀ (U₀ * S₀ * V₀ᵀ)))
    (hG : G = F (t₀ + h / 2) Z) {k : Type*} [Fintype k] [DecidableEq k] {Va : Matrix n k ℝ}
    (hVa : Vaᵀ * Va = 1) (augV : Va * Vaᵀ * V₀ = V₀) (lCap : Va * Vaᵀ * (Gᵀ * U₀) = Gᵀ * U₀) :
    ‖(1 - U₀ * U₀ᵀ) * G * (1 - Va * Vaᵀ)‖ ≤
      (L + κ + h / 2 * L * κ) * δ + ε + e + (h / 2) ^ 2 * κ * (L * B + Lₜ + B * κ)
```

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

`norm_capture_defect_le_sq_add` in [`LeanDLRA/Research/ExplicitMidpointCapture.lean`, lines 1038–1058](../LeanDLRA/Research/ExplicitMidpointCapture.lean#L1038-L1058):

```lean
theorem norm_capture_defect_le_sq_add {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {r : ℕ}
    {D : Set (ℝ × Matrix m n ℝ)} {ε L Lₜ B ρ H κ D₁ D₂ : ℝ}
    (hN : FactoredNormalBoundOn F r D ε) (hL : IsLipschitzFieldOn F D L) (hL0 : 0 ≤ L)
    (hB : IsBoundedFieldOn F D B)
    (hFt : ∀ s t X, (s, X) ∈ D → (t, X) ∈ D → ‖F s X - F t X‖ ≤ Lₜ * |s - t|)
    (hrm : r < Fintype.card m) (hrn : r < Fintype.card n)
    {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {t₀ h : ℝ} (hh : 0 < h) (hH : h ≤ H) (hρ : 0 < ρ)
    (hD : ∀ t ∈ Icc t₀ (t₀ + h), ∀ X, ‖X - U₀ * S₀ * V₀ᵀ‖ ≤ ρ → (t, X) ∈ D)
    (hκ : Real.sqrt r * (1 / 2 + max L (2 * B / ρ)) ≤ κ)
    (hD₁ : Real.sqrt r * H * max L (2 * B / ρ) / 2 + (2 * κ * B + κ ^ 2 * ‖S₀‖) / 4 +
      H * κ ^ 2 * B / 8 ≤ D₁)
    (hD₂ : Real.sqrt r * H * (1 + max L (2 * B / ρ) / 2) ≤ D₂)
    (hsmall : h / 2 * B + (D₁ * h ^ 2 + D₂ * ε) ≤ ρ / 2) {Z G : Matrix m n ℝ}
    (hZ : Z = U₀ * S₀ * V₀ᵀ + (h / 2) • tangentProj U₀ V₀ (F t₀ (U₀ * S₀ * V₀ᵀ)))
    (hG : G = F (t₀ + h / 2) Z) {k : Type*} [Fintype k] [DecidableEq k] {Ua : Matrix m k ℝ}
    (hUa : Uaᵀ * Ua = 1) (augU : Ua * Uaᵀ * U₀ = U₀) (kCap : Ua * Uaᵀ * (G * V₀) = G * V₀) :
    ‖(1 - Ua * Uaᵀ) * G * (1 - V₀ * V₀ᵀ)‖ ≤
      ((L + κ + H / 2 * L * κ) * D₁ + Real.sqrt r * max L (2 * B / ρ) / 2 +
          κ * (L * B + Lₜ + B * κ) / 4) * h ^ 2 +
        ((L + κ + H / 2 * L * κ) * D₂ + 1 + Real.sqrt r * (1 + max L (2 * B / ρ) / 2)) * ε
```

`norm_capture_defect_right_le_sq_add` in [`LeanDLRA/Research/ExplicitMidpointCapture.lean`, lines 1070–1090](../LeanDLRA/Research/ExplicitMidpointCapture.lean#L1070-L1090):

```lean
theorem norm_capture_defect_right_le_sq_add {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {r : ℕ}
    {D : Set (ℝ × Matrix m n ℝ)} {ε L Lₜ B ρ H κ D₁ D₂ : ℝ}
    (hN : FactoredNormalBoundOn F r D ε) (hL : IsLipschitzFieldOn F D L) (hL0 : 0 ≤ L)
    (hB : IsBoundedFieldOn F D B)
    (hFt : ∀ s t X, (s, X) ∈ D → (t, X) ∈ D → ‖F s X - F t X‖ ≤ Lₜ * |s - t|)
    (hrm : r < Fintype.card m) (hrn : r < Fintype.card n)
    {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {t₀ h : ℝ} (hh : 0 < h) (hH : h ≤ H) (hρ : 0 < ρ)
    (hD : ∀ t ∈ Icc t₀ (t₀ + h), ∀ X, ‖X - U₀ * S₀ * V₀ᵀ‖ ≤ ρ → (t, X) ∈ D)
    (hκ : Real.sqrt r * (1 / 2 + max L (2 * B / ρ)) ≤ κ)
    (hD₁ : Real.sqrt r * H * max L (2 * B / ρ) / 2 + (2 * κ * B + κ ^ 2 * ‖S₀‖) / 4 +
      H * κ ^ 2 * B / 8 ≤ D₁)
    (hD₂ : Real.sqrt r * H * (1 + max L (2 * B / ρ) / 2) ≤ D₂)
    (hsmall : h / 2 * B + (D₁ * h ^ 2 + D₂ * ε) ≤ ρ / 2) {Z G : Matrix m n ℝ}
    (hZ : Z = U₀ * S₀ * V₀ᵀ + (h / 2) • tangentProj U₀ V₀ (F t₀ (U₀ * S₀ * V₀ᵀ)))
    (hG : G = F (t₀ + h / 2) Z) {k : Type*} [Fintype k] [DecidableEq k] {Va : Matrix n k ℝ}
    (hVa : Vaᵀ * Va = 1) (augV : Va * Vaᵀ * V₀ = V₀) (lCap : Va * Vaᵀ * (Gᵀ * U₀) = Gᵀ * U₀) :
    ‖(1 - U₀ * U₀ᵀ) * G * (1 - Va * Vaᵀ)‖ ≤
      ((L + κ + H / 2 * L * κ) * D₁ + Real.sqrt r * max L (2 * B / ρ) / 2 +
          κ * (L * B + Lₜ + B * κ) / 4) * h ^ 2 +
        ((L + κ + H / 2 * L * κ) * D₂ + 1 + Real.sqrt r * (1 + max L (2 * B / ρ) / 2)) * ε
```

`ExplicitMidpoint.norm_update_sub_le_cube_add` in [`LeanDLRA/Research/ExplicitMidpointGalerkin.lean`, lines 331–358](../LeanDLRA/Research/ExplicitMidpointGalerkin.lean#L331-L358):

```lean
theorem norm_update_sub_le_cube_add [DecidableEq k] [DecidableEq k']
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {D : Set (ℝ × Matrix m n ℝ)}
    {ε L Lₜ B ρ H κ D₁ D₂ M₂ M₃ : ℝ}
    (hN : FactoredNormalBoundOn F r D ε) (hL : IsLipschitzFieldOn F D L) (hL0 : 0 ≤ L)
    (hB : IsBoundedFieldOn F D B)
    (hFt : ∀ s t X, (s, X) ∈ D → (t, X) ∈ D → ‖F s X - F t X‖ ≤ Lₜ * |s - t|)
    (hrm : r < Fintype.card m) (hrn : r < Fintype.card n) {S₀ : Matrix (Fin r) (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {t₀ h : ℝ} (hh : 0 < h) (hH : h ≤ H) (hρ : 0 < ρ)
    (hD : ∀ t ∈ Icc t₀ (t₀ + h), ∀ X, ‖X - U₀ * S₀ * V₀ᵀ‖ ≤ ρ → (t, X) ∈ D)
    (hκ : Real.sqrt r * (1 / 2 + max L (2 * B / ρ)) ≤ κ)
    (hD₁ : Real.sqrt r * H * max L (2 * B / ρ) / 2 + (2 * κ * B + κ ^ 2 * ‖S₀‖) / 4 +
      H * κ ^ 2 * B / 8 ≤ D₁)
    (hD₂ : Real.sqrt r * H * (1 + max L (2 * B / ρ) / 2) ≤ D₂)
    (hsmall : h / 2 * B + (D₁ * h ^ 2 + D₂ * ε) ≤ ρ / 2) {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t₀ (t₀ + h)) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    (hA3 : ContDiffOn ℝ 3 A (Icc t₀ (t₀ + h)))
    (hM₂ : ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 2 A (Icc t₀ (t₀ + h)) t‖ ≤ M₂)
    (hM₃ : ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 3 A (Icc t₀ (t₀ + h)) t‖ ≤ M₃)
    (hDA : (t₀ + h / 2, A (t₀ + h / 2)) ∈ D) {Z : Matrix m n ℝ}
    (hZ : Z = U₀ * S₀ * V₀ᵀ + (h / 2) • tangentProj U₀ V₀ (F t₀ (U₀ * S₀ * V₀ᵀ)))
    (hG : G = F (t₀ + h / 2) Z) (hUa : Uaᵀ * Ua = 1) (hVa : Vaᵀ * Va = 1)
    (augU : Ua * Uaᵀ * U₀ = U₀) (augV : Va * Vaᵀ * V₀ = V₀)
    (kCap : Ua * Uaᵀ * (G * V₀) = G * V₀) (lCap : Va * Vaᵀ * (Gᵀ * U₀) = Gᵀ * U₀) :
    ‖U₀ * S₀ * V₀ᵀ + h • galerkinProj Ua Va G - A (t₀ + h)‖ ≤
      h ^ 3 * (2 * ((L + κ + H / 2 * L * κ) * D₁ + Real.sqrt r * max L (2 * B / ρ) / 2 +
          κ * (L * B + Lₜ + B * κ) / 4) + M₃ / 24 + L * M₂ / 8) +
        h * ε * (2 * ((L + κ + H / 2 * L * κ) * D₂ + 1 +
          Real.sqrt r * (1 + max L (2 * B / ρ) / 2)) + L * h / 2)
```

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

`ExplicitMidpoint.stepRel` in [`LeanDLRA/HighOrder/Defs.lean`, lines 202–204](../LeanDLRA/HighOrder/Defs.lean#L202-L204):

```lean
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ => ∃ Yh : Matrix m n ℝ, augmentedRel F r t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧
    ‖Y₁ - Yh‖ ≤ distLR r Yh
```

`ExplicitMidpoint.exists_stepRel` in [`LeanDLRA/Research/ExplicitMidpointRun.lean`, lines 217–219](../LeanDLRA/Research/ExplicitMidpointRun.lean#L217-L219):

```lean
theorem exists_stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ)
    (hrm : 2 * r ≤ Fintype.card m) (hrn : 2 * r ≤ Fintype.card n) (hY₀ : Y₀.rank ≤ r) :
    ∃ Y₁, stepRel F r t₀ t₁ Y₀ Y₁
```

`ExplicitMidpoint.isTubeLocal_stepRel` in [`LeanDLRA/Research/ExplicitMidpointRun.lean`, lines 335–337](../LeanDLRA/Research/ExplicitMidpointRun.lean#L335-L337):

```lean
theorem isTubeLocal_stepRel (hrm : 2 * r ≤ Fintype.card m) (hrn : 2 * r ≤ Fintype.card n) :
    StepMethod.IsTubeLocal (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => stepRel G r)
      (fun Y => Y.rank ≤ r) 2
```

`ExplicitMidpoint.exists_run_norm_sub_le` in [`LeanDLRA/Research/ExplicitMidpointRun.lean`, lines 622–646](../LeanDLRA/Research/ExplicitMidpointRun.lean#L622-L646):

```lean
theorem exists_run_norm_sub_le {N : ℕ} {h T δ : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hF₂ : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂)
    (hA : ODESolution F A t₀ (t₀ + N * h))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (hr : 0 < r) (hrm : 2 * r ≤ Fintype.card m) (hrn : 2 * r ≤ Fintype.card n)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hσ : 0 < σ) (hκ : Real.sqrt r * (1 / 2 + max L (2 * B / σ)) ≤ κ)
    (hD₁ : Real.sqrt r * H * max L (2 * B / σ) / 2 +
      (2 * κ * B + κ ^ 2 * (‖A t₀‖ + B * T + ρ)) / 4 + H * κ ^ 2 * B / 8 ≤ D₁)
    (hD₂ : Real.sqrt r * H * (1 + max L (2 * B / σ) / 2) ≤ D₂)
    (hC₁ : 2 * (2 * ((L + κ + H / 2 * L * κ) * D₁ + Real.sqrt r * max L (2 * B / σ) / 2 +
        κ * (L * B + M₁ + B * κ) / 4) + (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) / 24 +
        L * (M₁ * (1 + B)) / 8) ≤ C₁)
    (hC₂ : Real.exp (L * H) + 2 * (2 * ((L + κ + H / 2 * L * κ) * D₂ + 1 +
        Real.sqrt r * (1 + max L (2 * B / σ) / 2))) + L * H ≤ C₂)
    (hstepσ : h / 2 * B + (D₁ * h ^ 2 + D₂ * ε) ≤ σ / 2)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) * (C₁ * h ^ 2 + C₂ * ε) +
      3 * B * h + σ < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * δ + T * Real.exp (L * T) * (C₁ * h ^ 2 + C₂ * ε)
```

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

`MatrixDRSVD.augmentedRel` in [`LeanDLRA/Randomized/DRSVDStep.lean`, lines 96–103](../LeanDLRA/Randomized/DRSVDStep.lean#L96-L103):

```lean
def augmentedRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (k l : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Yh =>
    ∃ (W : Matrix n (Fin k) ℝ) (Q : Matrix m (Fin l) ℝ) (Bs : ℝ → Matrix m (Fin k) ℝ)
      (Cs : ℝ → Matrix n (Fin l) ℝ),
      Wᵀ * W = 1 ∧ Y₀ * W * Wᵀ = Y₀ ∧ ODESolution (fun t X => F t (X * Wᵀ) * W) Bs t₀ t₁ ∧
        Bs t₀ = Y₀ * W ∧ Qᵀ * Q = 1 ∧ Q * Qᵀ * Bs t₁ = Bs t₁ ∧
        ODESolution (fun t C => (F t (Q * Cᵀ))ᵀ * Q) Cs t₀ t₁ ∧ Cs t₀ = Y₀ᵀ * Q ∧
        Yh = Q * (Cs t₁)ᵀ
```

`MatrixDRSVD.stepRel` in [`LeanDLRA/Randomized/DRSVDStep.lean`, lines 111–113](../LeanDLRA/Randomized/DRSVDStep.lean#L111-L113):

```lean
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r k l : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ Yh : Matrix m n ℝ, augmentedRel F k l t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧ ‖Y₁ - Yh‖ ≤ distLR r Yh
```

`MatrixDRSVD.stepRel.hasLocalError_of_tube` in [`LeanDLRA/Randomized/DRSVDStep.lean`, lines 391–400](../LeanDLRA/Randomized/DRSVDStep.lean#L391-L400):

```lean
theorem stepRel.hasLocalError_of_tube (h : stepRel F r k l t₀ t₁ Y₀ Y₁) (hkl : k ≤ l)
    (hY₀ : Y₀.rank ≤ r)
    (hε : ∀ s ∈ ({r, k} : Set ℕ), FactoredNormalBoundOn F s (tubeSet A a b ρ) ε) (hε₀ : 0 ≤ ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (hc : ContinuousOn (Function.uncurry F) (tubeSet A a b ρ))
    (hAc : ContinuousOn A (Icc a b)) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁)
    (hH : t₁ - t₀ ≤ H) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 3 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Y₁ ((t₁ - t₀) *
      ((2 * bugC₁ L H + 1) * ε + (2 * bugC₂ L B H + 10 * L * B) * (t₁ - t₀)))
```

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

`MatrixDRSVD.isTubeLocal_stepRel` in [`LeanDLRA/Randomized/DRSVDRun.lean`, lines 167–170](../LeanDLRA/Randomized/DRSVDRun.lean#L167-L170):

```lean
theorem isTubeLocal_stepRel (hrk : r ≤ k) (hkn : k ≤ Fintype.card n) (hkl : k ≤ l)
    (hlm : l ≤ Fintype.card m) :
    StepMethod.IsTubeLocal (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => stepRel G r k l)
      (fun Y => Y.rank ≤ r) 3
```

`MatrixDRSVD.exists_run_norm_sub_le` in [`LeanDLRA/Randomized/DRSVDRun.lean`, lines 278–289](../LeanDLRA/Randomized/DRSVDRun.lean#L278-L289):

```lean
theorem exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : ∀ s ∈ ({r, k} : Set ℕ), FactoredNormalBoundOn F s (tubeSet A t₀ (t₀ + N * h) ρ) ε)
    (hε₀ : 0 ≤ ε) (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T) (hrk : r ≤ k)
    (hkn : k ≤ Fintype.card n) (hkl : k ≤ l) (hlm : l ≤ Fintype.card m)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) *
      ((2 * bugC₁ L H + 1) * ε + (2 * bugC₂ L B H + 10 * L * B) * h) + 3 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r k l) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ +
        T * Real.exp (L * T) * ((2 * bugC₁ L H + 1) * ε + (2 * bugC₂ L B H + 10 * L * B) * h)
```

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

`distLR_flow_le_exp_of_tube` in [`LeanDLRA/Integrators/Matrix/FlowDistance.lean`, lines 143–150](../LeanDLRA/Integrators/Matrix/FlowDistance.lean#L143-L150):

```lean
theorem distLR_flow_le_exp_of_tube (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε)
    (hε₀ : 0 ≤ ε) (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A a b ρ)) (hAc : ContinuousOn A (Icc a b))
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hΦ : ODESolution F Φ t₀ t₁) (hrank : (Φ t₀).rank ≤ r)
    (hsmall : ‖Φ t₀ - A t₀‖ + 3 * B * (t₁ - t₀) < ρ) :
    distLR r (Φ t₁) ≤ (t₁ - t₀) * ε * Real.exp (L * (t₁ - t₀))
```

`distLR_flow_le_exp` in [`LeanDLRA/Matrix/LowRankDistance.lean`, lines 1365–1369](../LeanDLRA/Matrix/LowRankDistance.lean#L1365-L1369):

```lean
theorem distLR_flow_le_exp (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hε0 : 0 ≤ ε)
    (hε : MatrixBUG.FactoredNormalBound F r ε) {t₀ t₁ h : ℝ} (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hrank : (A t₀).rank ≤ r) :
    distLR r (A t₁) ≤ h * ε * Real.exp (L * h)
```

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

`distLR_flow_le_sharp` in [`LeanDLRA/Matrix/LowRankDistanceFlow.lean`, lines 72–76](../LeanDLRA/Matrix/LowRankDistanceFlow.lean#L72-L76):

```lean
theorem distLR_flow_le_sharp (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) (hε0 : 0 ≤ ε) (hε : MatrixBUG.FactoredNormalBound F r ε)
    (hA : ODESolution F A t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, distLR r (A t) ≤
      Real.exp (L * (t - t₀)) * distLR r (A t₀) + ε * (t - t₀) * Real.exp (L * (t - t₀))
```

The same distance along an exact solution `A` on `[t₀, t₁]` for a start value of any rank:
`distLR r (A t) ≤ e^{L (t - t₀)} distLR r (A t₀) + ε (t - t₀) e^{L (t - t₀)}`, with the constant
one in front of `ε`. The field is `L`-Lipschitz, bounded, continuous in time and has the normal
bound `ε` at the factored matrices of rank `r`. The module docstring says that the bound itself is
`distLR_flow_le_exp_mul_add` in `LeanDLRA/Matrix/LowRankDistance.lean` and that this file keeps
the recorded form of the statement; for a start of rank at most `r` it gives
`h ε e^{L h}` after time `h`, which is `distLR_flow_le_exp`. That the constant one cannot be
lowered is not proved there; the docstring names a constant field for which the library
certifies a lower bound `t / 3`.

`MatrixProjEuler.stepRel` in [`LeanDLRA/Integrators/Matrix/ProjectedEuler.lean`, lines 114–116](../LeanDLRA/Integrators/Matrix/ProjectedEuler.lean#L114-L116):

```lean
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) (κ : ℝ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ => ∃ X : Matrix m n ℝ, tangentRel F r t₀ t₁ Y₀ X ∧ Y₁.rank ≤ r ∧
    ‖Y₁ - X‖ ≤ κ * distLR r X
```

`MatrixProjEuler.stepRel.hasLocalError_of_tube` in [`LeanDLRA/Integrators/Matrix/ProjectedEuler.lean`, lines 268–277](../LeanDLRA/Integrators/Matrix/ProjectedEuler.lean#L268-L277):

```lean
theorem stepRel.hasLocalError_of_tube (h : stepRel F r κ t₀ t₁ Y₀ Y₁) (hκ : 0 ≤ κ)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε) (hε₀ : 0 ≤ ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (hc : ContinuousOn (Function.uncurry F) (tubeSet A a b ρ))
    (hAc : ContinuousOn A (Icc a b)) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀))
    (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Y₁ ((t₁ - t₀) *
      ((10 * κ * L * B + (1 + κ) * (L * B + Lt) / 2) * (t₁ - t₀) + (1 + 2 * κ) * ε))
```

`MatrixProjEuler.exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Matrix/ProjectedEuler.lean`, lines 418–433](../LeanDLRA/Integrators/Matrix/ProjectedEuler.lean#L418-L433):

```lean
theorem exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → (s, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ →
      (t, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ → ‖F t x - F s x‖ ≤ Lt * (t - s))
    (hκ : 1 ≤ κ) (hh : 0 ≤ h) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) *
      ((10 * κ * L * B + (1 + κ) * (L * B + Lt) / 2) * h + (1 + 2 * κ) * ε) + 2 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r κ) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ +
        T * Real.exp (L * T) *
          ((10 * κ * L * B + (1 + κ) * (L * B + Lt) / 2) * h + (1 + 2 * κ) * ε)
```

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

`MatrixPRK.stepRel` in [`LeanDLRA/HighOrder/Defs.lean`, lines 153–161](../LeanDLRA/HighOrder/Defs.lean#L153-L161):

```lean
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) (κ : ℝ) (a : Fin s → Fin s → ℝ)
    (b c : Fin s → ℝ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ => ∃ (U : Fin s → Matrix m (Fin r) ℝ) (S : Fin s → Matrix (Fin r) (Fin r) ℝ)
    (V : Fin s → Matrix n (Fin r) ℝ), (∀ j, (U j)ᵀ * U j = 1 ∧ (V j)ᵀ * V j = 1) ∧
    (∀ j, ‖U j * S j * (V j)ᵀ - stageSum F c t₀ (t₁ - t₀) Y₀ (a j) U S V‖ ≤
      κ * distLR r (stageSum F c t₀ (t₁ - t₀) Y₀ (a j) U S V)) ∧
    Y₁.rank ≤ r ∧
    ‖Y₁ - stageSum F c t₀ (t₁ - t₀) Y₀ b U S V‖ ≤
      κ * distLR r (stageSum F c t₀ (t₁ - t₀) Y₀ b U S V)
```

`MatrixPRK.exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Matrix/ProjectedRK.lean`, lines 531–556](../LeanDLRA/Integrators/Matrix/ProjectedRK.lean#L531-L556):

```lean
theorem exists_run_norm_sub_le
    (ha : ∀ i j, i ≤ j → a i j = 0) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ 1)
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hcont : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hκ : 1 ≤ κ) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) (hK : 0 ≤ K)
    {q : Fin s → ℕ} {q₂ p q' : ℕ} (hq : ∀ j : Fin s, 0 < j.val → q₂ ≤ q j) (hqp : q' ≤ p)
    (hqb : ∀ j : Fin s, 0 < j.val → b j ≠ 0 → q' ≤ min (q j) (q₂ + 1) + 1)
    (hRK : ∀ k < N, ∀ Z₀ : Matrix m n ℝ, Z₀.rank ≤ r →
      ‖Z₀ - A (t₀ + k * h)‖ ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) *
        (localErrorConst a b L κ * (ε + ε * Real.exp (L * h) + K * h ^ q')) →
      ∀ (Zt : Fin s → Matrix m n ℝ) (zt : Matrix m n ℝ),
      IsGalerkinRKStep F a b c (fun _ => 1) 1 (t₀ + k * h) h Z₀ Zt zt →
      ∀ Φ : ℝ → Matrix m n ℝ, ODESolution F Φ (t₀ + k * h) (t₀ + (k + 1) * h) →
        Φ (t₀ + k * h) = Z₀ →
        (∀ j : Fin s, 0 < j.val → ‖Zt j - Φ (t₀ + k * h + c j * h)‖ ≤ K * h ^ (q j + 1)) ∧
        ‖zt - Φ (t₀ + (k + 1) * h)‖ ≤ K * h ^ (p + 1))
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) *
      (localErrorConst a b L κ * (ε + ε * Real.exp (L * h) + K * h ^ q')) +
        ((1 + κ) * tabWeight a b + 3) * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r κ a b c) (uniformGrid t₀ h) N Y ∧
      ∀ k ≤ N, (Y k).rank ≤ r ∧ ‖Y k - A (t₀ + k * h)‖ ≤ Real.exp (L * T) * δ +
        T * Real.exp (L * T) *
          (localErrorConst a b L κ * (ε + ε * Real.exp (L * h) + K * h ^ q'))
```

`ProjectedRK.norm_sub_le_of_stages` in [`LeanDLRA/HighOrder/ProjectedRK.lean`, lines 334–347](../LeanDLRA/HighOrder/ProjectedRK.lean#L334-L347):

```lean
theorem norm_sub_le_of_stages (ha : ∀ i j, i ≤ j → a i j = 0) (hκ : 0 ≤ κ) (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (hg : 0 ≤ g) (hK : 0 ≤ K) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hy : y ∈ ℳ)
    (hZ : ∀ j, Z j = y + h • ∑ l, a j l • e l)
    (hη : ∀ j, ∀ z ∈ ℳ, ‖η j - Z j‖ ≤ κ * ‖z - Z j‖)
    (he : ∀ j, ‖e j - Fη j‖ ≤ ε) (hLip : ∀ j, ‖Fη j - FZt j‖ ≤ L * ‖η j - Zt j‖)
    (hZt : ∀ j, Zt j = y + h • ∑ l, a j l • FZt l) {q : Fin s → ℕ} {q₂ p q' : ℕ}
    (hq : ∀ j : Fin s, 0 < j.val → q₂ ≤ q j)
    (hw : ∀ j : Fin s, 0 < j.val → ‖Zt j - w j‖ ≤ K * h ^ (q j + 1))
    (hM : ∀ j : Fin s, 0 < j.val → ∃ z ∈ ℳ, ‖z - w j‖ ≤ h * g) {y₁ zt wf : E}
    (hy₁ : ∀ z ∈ ℳ, ‖y₁ - (y + h • ∑ j, b j • e j)‖ ≤ κ * ‖z - (y + h • ∑ j, b j • e j)‖)
    (hzt : zt = y + h • ∑ j, b j • FZt j) (hp : ‖zt - wf‖ ≤ K * h ^ (p + 1))
    (hMf : ∃ z ∈ ℳ, ‖z - wf‖ ≤ h * g) (hqp : q' ≤ p)
    (hqb : ∀ j : Fin s, 0 < j.val → b j ≠ 0 → q' ≤ min (q j) (q₂ + 1) + 1) :
    ‖y₁ - wf‖ ≤ h * (localErrorConst a b L κ * (ε + g + K * h ^ q'))
```

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

`AugmentationRank.error_le_of_twoSided` in [`LeanDLRA/Research/TwoSidedLeak.lean`, lines 660–707](../LeanDLRA/Research/TwoSidedLeak.lean#L660-L707):

```lean
theorem error_le_of_twoSided [DecidableEq m] [DecidableEq n] {k k' : Type*} [Fintype k]
    [Fintype k'] [DecidableEq k]
    [DecidableEq k'] {Ua : Matrix m k ℝ} {Va : Matrix n k' ℝ} {K : ℝ → Matrix m (Fin r) ℝ}
    {Lf : ℝ → Matrix n (Fin r) ℝ} {Sa : ℝ → Matrix k k' ℝ} {Y₁ : Matrix m n ℝ} {ϑ L h : ℝ}
    (hFS : ∀ t Y, F t Y = 𝒜 * Y + Y * ℬ + C * Y * D) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    {P : ℝ → Matrix (Fin r) n ℝ}
    (hP : ODESolution (fun _ X => X * ℬ - V₀ᵀ * ℬ * V₀ * X) P t₀ t₁) (hP₀ : P t₀ = V₀ᵀ)
    {Z : ℝ → Matrix (Fin r) n ℝ}
    (hZ : ODESolution
      (fun t X => X * ℬ - U₀ᵀ * (C * K t * (V₀ᵀ * D * V₀ * P t - P t * D))) Z t₀ t₁)
    (hZ₀ : Z t₀ = 0) {Q : ℝ → Matrix m (Fin r) ℝ}
    (hQ : ODESolution (fun _ X => 𝒜 * X - X * (U₀ᵀ * 𝒜 * U₀)) Q t₀ t₁) (hQ₀ : Q t₀ = U₀)
    {Zr : ℝ → Matrix m (Fin r) ℝ}
    (hZr : ODESolution
      (fun t X => 𝒜 * X - (Q t * (U₀ᵀ * C * U₀) - C * Q t) * (Lf t)ᵀ * D * V₀) Zr t₀ t₁)
    (hZr₀ : Zr t₀ = 0) {a₂ : ℝ → Matrix m n ℝ} {M₂ : ℝ}
    (ha : ContinuousOn (fun t => F t (A t)) (Icc t₀ t₁))
    (ha' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => F t (A t)) (a₂ s) (Ici s) s)
    (hM₂ : ∀ s ∈ Ico t₀ t₁, ‖a₂ s‖ ≤ M₂) {a b c δ σ κ κ₂ π ε₀ νC νD ℓC ℓD Γ₁ Γ₂ θ : ℝ}
    (h𝒜 : ‖𝒜‖ ≤ a) (hℬ : ‖ℬ‖ ≤ b) (hC : ‖C‖ ≤ c) (hD : ‖D‖ ≤ δ) (hσ : ‖S₀‖ ≤ σ)
    (hκ : 0 ≤ κ) (hκ₂ : 0 ≤ κ₂) (hπ : 0 ≤ π)
    (hK₁ : ∀ t ∈ Icc t₀ t₁, ‖K t - U₀ * S₀‖ ≤ κ * (t - t₀))
    (hK₂ : ∀ t ∈ Icc t₀ t₁,
      ‖K t - U₀ * S₀ - (t - t₀) • kField V₀ F t₀ (U₀ * S₀)‖ ≤ κ₂ * (t - t₀) ^ 2)
    (hL₁ : ∀ t ∈ Icc t₀ t₁, ‖Lf t - V₀ * S₀ᵀ‖ ≤ κ * (t - t₀))
    (hL₂ : ∀ t ∈ Icc t₀ t₁,
      ‖Lf t - V₀ * S₀ᵀ - (t - t₀) • lField U₀ F t₀ (V₀ * S₀ᵀ)‖ ≤ κ₂ * (t - t₀) ^ 2)
    (hPπ : ∀ t ∈ Icc t₀ t₁, ‖P t - V₀ᵀ‖ ≤ π * (t - t₀))
    (hQπ : ∀ t ∈ Icc t₀ t₁, ‖Q t - U₀‖ ≤ π * (t - t₀))
    (hε₀ : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε₀)
    (hνC : ‖(1 - U₀ * U₀ᵀ) * C * U₀ * S₀‖ ≤ νC)
    (hνD : ‖S₀ * V₀ᵀ * D * (1 - V₀ * V₀ᵀ)‖ ≤ νD)
    (hℓC : ‖(1 - U₀ * U₀ᵀ) * C * U₀‖ ≤ ℓC) (hℓD : ‖V₀ᵀ * D * (1 - V₀ * V₀ᵀ)‖ ≤ ℓD)
    (hΓ₁ : 2 * δ * π + c * δ ^ 2 + c * a + (a + c * δ) * c * Real.exp (b * h) + κ ≤ Γ₁)
    (hΓ₂ : 2 * c * δ * π * κ + 2 * c * δ * π * σ * (a + c * δ) + c * κ₂ * δ
      + (a + c * δ) * Real.exp (b * h) * (2 * c * σ * δ * π + c * κ * δ)
      + h * (2 * c * κ₂ * δ * π + (a + c * δ) * Real.exp (b * h) * (2 * c * κ * δ * π))
        ≤ Γ₂)
    (hΓ₁' : 2 * c * π + δ * c ^ 2 + δ * b + (b + δ * c) * δ * Real.exp (a * h) + κ ≤ Γ₁)
    (hΓ₂' : 2 * δ * c * π * κ + 2 * δ * c * π * σ * (b + δ * c) + δ * κ₂ * c
      + (b + δ * c) * Real.exp (a * h) * (2 * δ * σ * c * π + δ * κ * c)
      + h * (2 * δ * κ₂ * c * π + (b + δ * c) * Real.exp (a * h) * (2 * δ * κ * c * π))
        ≤ Γ₂)
    (hθ : θ = 2 * (h * Real.exp (L * h) * (ε₀ + h * Γ₁ * (νC + νD + ℓC * ℓD) + h ^ 2 * Γ₂))) :
    ‖Y₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (θ + M₂ * h ^ 2) + θ + ϑ
```

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

`AugmentationRank.error_le_of_twoSided_of_leaks_eq_zero` in [`LeanDLRA/Research/TwoSidedPadded.lean`, lines 128–173](../LeanDLRA/Research/TwoSidedPadded.lean#L128-L173):

```lean
theorem error_le_of_twoSided_of_leaks_eq_zero [DecidableEq m] [DecidableEq n] {k k' : Type*}
    [Fintype k] [Fintype k'] [DecidableEq k] [DecidableEq k'] {Ua : Matrix m k ℝ}
    {Va : Matrix n k' ℝ} {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ}
    {Sa : ℝ → Matrix k k' ℝ} {Y₁ : Matrix m n ℝ} {ϑ L h : ℝ}
    (hFS : ∀ t Y, F t Y = 𝒜 * Y + Y * ℬ + C * Y * D) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    {P : ℝ → Matrix (Fin r) n ℝ}
    (hP : ODESolution (fun _ X => X * ℬ - V₀ᵀ * ℬ * V₀ * X) P t₀ t₁) (hP₀ : P t₀ = V₀ᵀ)
    {Z : ℝ → Matrix (Fin r) n ℝ}
    (hZ : ODESolution
      (fun t X => X * ℬ - U₀ᵀ * (C * K t * (V₀ᵀ * D * V₀ * P t - P t * D))) Z t₀ t₁)
    (hZ₀ : Z t₀ = 0) {Q : ℝ → Matrix m (Fin r) ℝ}
    (hQ : ODESolution (fun _ X => 𝒜 * X - X * (U₀ᵀ * 𝒜 * U₀)) Q t₀ t₁) (hQ₀ : Q t₀ = U₀)
    {Zr : ℝ → Matrix m (Fin r) ℝ}
    (hZr : ODESolution
      (fun t X => 𝒜 * X - (Q t * (U₀ᵀ * C * U₀) - C * Q t) * (Lf t)ᵀ * D * V₀) Zr t₀ t₁)
    (hZr₀ : Zr t₀ = 0) {a₂ : ℝ → Matrix m n ℝ} {M₂ : ℝ}
    (ha : ContinuousOn (fun t => F t (A t)) (Icc t₀ t₁))
    (ha' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => F t (A t)) (a₂ s) (Ici s) s)
    (hM₂ : ∀ s ∈ Ico t₀ t₁, ‖a₂ s‖ ≤ M₂) {a b c δ σ κ κ₂ π ℓC ℓD Γ₁ Γ₂ θ : ℝ}
    (h𝒜 : ‖𝒜‖ ≤ a) (hℬ : ‖ℬ‖ ≤ b) (hC : ‖C‖ ≤ c) (hD : ‖D‖ ≤ δ) (hσ : ‖S₀‖ ≤ σ)
    (hκ : 0 ≤ κ) (hκ₂ : 0 ≤ κ₂) (hπ : 0 ≤ π)
    (hK₁ : ∀ t ∈ Icc t₀ t₁, ‖K t - U₀ * S₀‖ ≤ κ * (t - t₀))
    (hK₂ : ∀ t ∈ Icc t₀ t₁,
      ‖K t - U₀ * S₀ - (t - t₀) • kField V₀ F t₀ (U₀ * S₀)‖ ≤ κ₂ * (t - t₀) ^ 2)
    (hL₁ : ∀ t ∈ Icc t₀ t₁, ‖Lf t - V₀ * S₀ᵀ‖ ≤ κ * (t - t₀))
    (hL₂ : ∀ t ∈ Icc t₀ t₁,
      ‖Lf t - V₀ * S₀ᵀ - (t - t₀) • lField U₀ F t₀ (V₀ * S₀ᵀ)‖ ≤ κ₂ * (t - t₀) ^ 2)
    (hPπ : ∀ t ∈ Icc t₀ t₁, ‖P t - V₀ᵀ‖ ≤ π * (t - t₀))
    (hQπ : ∀ t ∈ Icc t₀ t₁, ‖Q t - U₀‖ ≤ π * (t - t₀))
    (hνC : (1 - U₀ * U₀ᵀ) * C * U₀ * S₀ = 0) (hνD : S₀ * V₀ᵀ * D * (1 - V₀ * V₀ᵀ) = 0)
    (hℓC : ‖(1 - U₀ * U₀ᵀ) * C * U₀‖ ≤ ℓC) (hℓD : ‖V₀ᵀ * D * (1 - V₀ * V₀ᵀ)‖ ≤ ℓD)
    (hΓ₁ : 2 * δ * π + c * δ ^ 2 + c * a + (a + c * δ) * c * Real.exp (b * h) + κ ≤ Γ₁)
    (hΓ₂ : 2 * c * δ * π * κ + 2 * c * δ * π * σ * (a + c * δ) + c * κ₂ * δ
      + (a + c * δ) * Real.exp (b * h) * (2 * c * σ * δ * π + c * κ * δ)
      + h * (2 * c * κ₂ * δ * π + (a + c * δ) * Real.exp (b * h) * (2 * c * κ * δ * π))
        ≤ Γ₂)
    (hΓ₁' : 2 * c * π + δ * c ^ 2 + δ * b + (b + δ * c) * δ * Real.exp (a * h) + κ ≤ Γ₁)
    (hΓ₂' : 2 * δ * c * π * κ + 2 * δ * c * π * σ * (b + δ * c) + δ * κ₂ * c
      + (b + δ * c) * Real.exp (a * h) * (2 * δ * σ * c * π + δ * κ * c)
      + h * (2 * δ * κ₂ * c * π + (b + δ * c) * Real.exp (a * h) * (2 * δ * κ * c * π))
        ≤ Γ₂)
    (hθ : θ = 2 * (h * Real.exp (L * h) * (h * Γ₁ * (ℓC * ℓD) + h ^ 2 * Γ₂))) :
    ‖Y₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (θ + M₂ * h ^ 2) + θ + ϑ
```

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

`AugmentationRank.exists_odeSolution_sylvester` in [`LeanDLRA/Research/SylvesterFlows.lean`, lines 67–71](../LeanDLRA/Research/SylvesterFlows.lean#L67-L71):

```lean
theorem exists_odeSolution_sylvester {C : ℝ → Matrix p p ℝ} {D : ℝ → Matrix q q ℝ} {t₀ t₁ : ℝ}
    (hC : ContinuousOn C (Icc t₀ t₁)) (hD : ContinuousOn D (Icc t₀ t₁)) (ht : t₀ ≤ t₁)
    (X₀ : Matrix p q ℝ) :
    ∃ X : ℝ → Matrix p q ℝ,
      ODESolution (fun t Y => C t * Y + Y * D t) X t₀ t₁ ∧ X t₀ = X₀
```

`AugmentationRank.capture_of_sylvester_of_continuousOn` in [`LeanDLRA/Research/SylvesterFlows.lean`, lines 170–175](../LeanDLRA/Research/SylvesterFlows.lean#L170-L175):

```lean
theorem capture_of_sylvester_of_continuousOn (hFS : ∀ t Y, F t Y = 𝒜 t * Y + Y * ℬ t)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (h𝒜 : ContinuousOn 𝒜 (Icc t₀ t₁))
    (hℬ : ContinuousOn ℬ (Icc t₀ t₁))
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁) (ht : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    Ua * Uaᵀ * A t₁ = A t₁ ∧ A t₁ * Va * Vaᵀ = A t₁
```

`AugmentationRank.error_le_of_sylvester_of_continuousOn` in [`LeanDLRA/Research/SylvesterFlows.lean`, lines 190–198](../LeanDLRA/Research/SylvesterFlows.lean#L190-L198):

```lean
theorem error_le_of_sylvester_of_continuousOn {h : ℝ}
    (hFS : ∀ t Y, F t Y = 𝒜 t * Y + Y * ℬ t) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (h𝒜 : ContinuousOn 𝒜 (Icc t₀ t₁)) (hℬ : ContinuousOn ℬ (Icc t₀ t₁)) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) {a₂ : ℝ → Matrix m n ℝ} {M₂ : ℝ}
    (ha : ContinuousOn (fun t => F t (A t)) (Icc t₀ t₁))
    (ha' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => F t (A t)) (a₂ s) (Ici s) s)
    (hM₂ : ∀ s ∈ Ico t₀ t₁, ‖a₂ s‖ ≤ M₂) :
    ‖Y₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (M₂ * h ^ 2) + ϑ
```

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

`AugmentationRank.rankAdaptive_global_error_le_of_sylvester` in [`LeanDLRA/Research/SylvesterGlobal.lean`, lines 56–78](../LeanDLRA/Research/SylvesterGlobal.lean#L56-L78):

```lean
theorem rankAdaptive_global_error_le_of_sylvester (hFS : ∀ t Y, F t Y = 𝒜 t * Y + Y * ℬ t)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ}
    (h𝒜 : ContinuousOn 𝒜 (Icc t₀ (t₀ + N * h))) (hℬ : ContinuousOn ℬ (Icc t₀ (t₀ + N * h)))
    {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ (t₀ + N * h)) {r ka kb : ℕ → ℕ}
    {U : (j : ℕ) → Matrix m (Fin (r j)) ℝ} {Sm : (j : ℕ) → Matrix (Fin (r j)) (Fin (r j)) ℝ}
    {V : (j : ℕ) → Matrix n (Fin (r j)) ℝ} {Ua : (j : ℕ) → Matrix m (Fin (ka j)) ℝ}
    {Va : (j : ℕ) → Matrix n (Fin (kb j)) ℝ} {K : (j : ℕ) → ℝ → Matrix m (Fin (r j)) ℝ}
    {Lf : (j : ℕ) → ℝ → Matrix n (Fin (r j)) ℝ}
    {Sa : (j : ℕ) → ℝ → Matrix (Fin (ka j)) (Fin (kb j)) ℝ} {Y : ℕ → Matrix m n ℝ}
    {Φ : ℕ → ℝ → Matrix m n ℝ} (hY : ∀ j < N, Y j = U j * Sm j * (V j)ᵀ)
    (hstep : ∀ j < N, IsRankAdaptiveStep F ϑ (t₀ + j * h) (t₀ + (j + 1) * h) (U j) (Sm j) (V j)
      (Ua j) (Va j) (K j) (Lf j) (Sa j) (Y (j + 1)))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = Y j) {a₂ : ℕ → ℝ → Matrix m n ℝ} {M₂ : ℝ}
    (hM₂0 : 0 ≤ M₂)
    (ha : ∀ j < N, ContinuousOn (fun t => F t (Φ j t)) (Icc (t₀ + j * h) (t₀ + (j + 1) * h)))
    (ha' : ∀ j < N, ∀ s ∈ Ico (t₀ + j * h) (t₀ + (j + 1) * h),
      HasDerivWithinAt (fun t => F t (Φ j t)) (a₂ j s) (Ici s) s)
    (hM₂ : ∀ j < N, ∀ s ∈ Ico (t₀ + j * h) (t₀ + (j + 1) * h), ‖a₂ j s‖ ≤ M₂) {δ T : ℝ}
    (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖Y j - A (t₀ + j * h)‖
        ≤ Real.exp (L * T) * (δ + T * (L * Real.exp (L * h) * M₂ * h ^ 2) + j * ϑ)
```

The global error. `N` steps of the rank-adaptive BUG integrator with step size `h`, truncation
tolerance `ϑ` and ranks that may change from step to step; the exact solutions `Φ j` start at the
numerical values (`hΦ`, `hΦ₀`, the older form) and `M₂` bounds the derivative of
`t ↦ F(t, Φ j t)` along them. For `j h ≤ T`

`‖Y j - A (t₀ + j h)‖ ≤ e^{L T} (δ + T L e^{L h} M₂ h² + j ϑ)`,

with `δ` the initial error. So on these fields the integrator has global order two up to the
truncation term `j ϑ`, without a normal component and without a singular value in the bound. The
proof is Lady Windermere's fan with the local bound above.

`AugmentationRank.error_le_of_perturbedSylvester` in [`LeanDLRA/Research/PerturbedSylvester.lean`, lines 562–574](../LeanDLRA/Research/PerturbedSylvester.lean#L562-L574):

```lean
theorem error_le_of_perturbedSylvester {ϑ L g h : ℝ}
    (hFS : ∀ t Y, F t Y = 𝒜 * Y + Y * ℬ + G Y) (hG : ∀ X Y, ‖G X - G Y‖ ≤ g * ‖X - Y‖)
    (hg : 0 ≤ g) (hF : IsLipschitzField F L) (hL : 0 ≤ L) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) {a₂ : ℝ → Matrix m n ℝ} {M₂ : ℝ}
    (ha : ContinuousOn (fun t => F t (A t)) (Icc t₀ t₁))
    (ha' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => F t (A t)) (a₂ s) (Ici s) s)
    (hM₂ : ∀ s ∈ Ico t₀ t₁, ‖a₂ s‖ ≤ M₂) {a b B γ₀ ε₀ θ : ℝ} (h𝒜 : ‖𝒜‖ ≤ a) (hℬ : ‖ℬ‖ ≤ b)
    (hBA : ∀ t ∈ Ico t₀ t₁, ‖F t (A t)‖ ≤ B) (hBK : ∀ t ∈ Ico t₀ t₁, ‖F t (K t * V₀ᵀ)‖ ≤ B)
    (hBL : ∀ t ∈ Ico t₀ t₁, ‖F t (U₀ * (Lf t)ᵀ)‖ ≤ B) (hγ₀ : ‖G (U₀ * S₀ * V₀ᵀ)‖ ≤ γ₀)
    (hε₀ : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε₀)
    (hθ : θ = 2 * h * ε₀ + 4 * Real.exp (3 * (a + b) * h) * h ^ 2 * (g * B + (a + b) * γ₀)) :
    ‖Y₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (θ + M₂ * h ^ 2) + θ + ϑ
```

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

`AugmentationRank.sq_div_le_error_of_rankOne_galerkin` in [`LeanDLRA/Research/RankOneGalerkinBarrier.lean`, lines 230–234](../LeanDLRA/Research/RankOneGalerkinBarrier.lean#L230-L234):

```lean
theorem sq_div_le_error_of_rankOne_galerkin (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {h : ℝ}
    (hh : 0 ≤ h) (hπ : h ≤ Real.pi) {YS : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hS : ODESolution (fun _ Y => galerkinProj U V (rotGen * Y)) YS 0 h)
    (hS₀ : YS 0 = galerkinProj U V rotStart) :
    h ^ 2 / Real.pi ^ 2 ≤ ‖YS h - rotSolution h‖
```

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

`IsOneSidedLipschitzField` in [`LeanDLRA/Analysis/Defs.lean`, lines 126–127](../LeanDLRA/Analysis/Defs.lean#L126-L127):

```lean
def IsOneSidedLipschitzField (F : ℝ → E → E) (ℓ : ℝ) : Prop :=
  ∀ t x y, ⟪F t x - F t y, x - y⟫ ≤ ℓ * ‖x - y‖ ^ 2
```

### 7.1 The implicit BUG integrator

`IsImplicitBUGStep` in [`LeanDLRA/Stiff/ImplicitBUG.lean`, lines 351–365](../LeanDLRA/Stiff/ImplicitBUG.lean#L351-L365):

```lean
structure IsImplicitBUGStep (F : ℝ → E → E) (ε τ ϑ : ℝ) (P₀ Q₀ P₁ Q₁ : E →L[ℝ] E)
    (t₁ h : ℝ) (Y₀ YK YL xS Y₁ : E) : Prop where
  hP₀ : IsOrthProj P₀
  hQ₀ : IsOrthProj Q₀
  hP₁ : IsOrthProj P₁
  hQ₁ : IsOrthProj Q₁
  comm : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)
  kstep : YK = Y₀ + h • Q₀ (F t₁ YK)
  lstep : YL = Y₀ + h • P₀ (F t₁ YL)
  kcap : ‖(1 - P₁) YK‖ ≤ τ
  lcap : ‖(1 - Q₁) YL‖ ≤ τ
  knormal : ‖(1 - P₁) ((1 - Q₀) (F t₁ YK))‖ ≤ ε
  lnormal : ‖(1 - Q₁) ((1 - P₀) (F t₁ YL))‖ ≤ ε
  sstep : xS = (P₁ * Q₁) (Y₀ + h • F t₁ xS)
  trunc : ‖Y₁ - xS‖ ≤ ϑ
```

One step of the BUG integrator with backward Euler substeps, in projector form on a general
state space: implicit K-step and L-step (`kstep`, `lstep`), new projectors `P₁`, `Q₁` that
capture their results up to a tolerance `τ` (`kcap`, `lcap`), bounds `ε` for the normal
components at these results, an implicit Galerkin step (`sstep`) and a truncation with tolerance
`ϑ` (`trunc`).

`implicitBUG_wellPosed` in [`LeanDLRA/Stiff/ImplicitSolvability.lean`, lines 1571–1578](../LeanDLRA/Stiff/ImplicitSolvability.lean#L1571-L1578):

```lean
theorem implicitBUG_wellPosed [CompleteSpace E] {F : ℝ → E → E} {ℓ L h : ℝ}
    (hF : IsOneSidedLipschitzField F ℓ) (hL : IsLipschitzField F L) (hh : 0 ≤ h)
    (hhℓ : h * ℓ < 1) (t : ℝ) {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} (hP₀ : IsOrthProj P₀)
    (hQ₀ : IsOrthProj Q₀) (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁)
    (hc : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)) (hF0 : ∀ y, ⟪F t y, y⟫ ≤ ℓ * ‖y‖ ^ 2) (Y₀ : E) :
    (∃! YK, YK = Q₀ (Y₀ + h • F t YK)) ∧ (∃! YL, YL = P₀ (Y₀ + h • F t YL)) ∧
      (∃! YS, YS = (P₁ * Q₁) ((P₁ * Q₁) Y₀ + h • F t YS)) ∧
      ∀ YS, YS = (P₁ * Q₁) ((P₁ * Q₁) Y₀ + h • F t YS) → (1 - h * ℓ) * ‖YS‖ ≤ ‖Y₀‖
```

Solvability of the substeps. Let the field be one-sided Lipschitz with constant `ℓ` and Lipschitz
(with any constant), and let `h ≥ 0` with `h * ℓ < 1`. Then each of the three implicit equations
of a step has exactly one solution, for any orthogonal projectors, and under the additional
hypothesis `hF0` (`⟪F t y, y⟫ ≤ ℓ * ‖y‖²`) the solution `YS` of the Galerkin equation satisfies
`(1 - h * ℓ) * ‖YS‖ ≤ ‖Y₀‖`. The condition on the step size involves `ℓ` and not `L`; for
`ℓ ≤ 0` every step size is allowed. The space has to be complete.

`implicitBUG_global_error_le` in [`LeanDLRA/Stiff/ImplicitBUG.lean`, lines 1184–1195](../LeanDLRA/Stiff/ImplicitBUG.lean#L1184-L1195):

```lean
theorem implicitBUG_global_error_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hFt : ∀ s t x, ‖F s x - F t x‖ ≤ Lₜ * |s - t|) (hLt : 0 ≤ Lₜ) (hB : IsBoundedField F B)
    (hos : IsOneSidedLipschitzField F ℓ) (hhL : h * L ≤ 1) (hhℓ : h * ℓ ≤ 1 / 2) (hh : 0 ≤ h)
    (hε : 0 ≤ ε) (hτ : 0 ≤ τ) (hϑ : 0 ≤ ϑ) {N : ℕ}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    (hstep : ∀ n < N, ∃ P₀ Q₀ P₁ Q₁ : E →L[ℝ] E, ∃ YK YL xS : E,
      IsImplicitBUGStep F ε τ ϑ P₀ Q₀ P₁ Q₁ (t₀ + (n + 1) * h) h (Y n) YK YL xS (Y (n + 1)))
    {T : ℝ} :
    ∀ n ≤ N, (n : ℝ) * h ≤ T → ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) *
      (‖Y 0 - A t₀‖ + T * ((14 * L * B + 8 * Lₜ) * h + 6 * ε) + n * (6 * τ + ϑ))
```

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

`MatrixImplicitBUG.IsStep` in [`LeanDLRA/Stiff/Defs.lean`, lines 64–94](../LeanDLRA/Stiff/Defs.lean#L64-L94):

```lean
structure IsStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ) (U₀ : Matrix m (Fin r) ℝ)
    (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ) (K₁ : Matrix m (Fin r) ℝ)
    (L₁ : Matrix n (Fin r) ℝ) (U₁ : Matrix m (Fin r) ℝ) (V₁ : Matrix n (Fin r) ℝ)
    (S₁ : Matrix (Fin r) (Fin r) ℝ) : Prop where
  /-- The old column basis is orthonormal. -/
  orthU₀ : U₀ᵀ * U₀ = 1
  /-- The old row basis is orthonormal. -/
  orthV₀ : V₀ᵀ * V₀ = 1
  /-- Backward Euler K-step. -/
  kStep : K₁ = U₀ * S₀ + (t₁ - t₀) • (F t₁ (K₁ * V₀ᵀ) * V₀)
  /-- The K-stage is the limit of the fixed-point iteration started at `U₀ S₀`. -/
  kIter : Tendsto (fun j => (fun K => U₀ * S₀ + (t₁ - t₀) • (F t₁ (K * V₀ᵀ) * V₀))^[j]
    (U₀ * S₀)) atTop (𝓝 K₁)
  /-- Backward Euler L-step. -/
  lStep : L₁ = V₀ * S₀ᵀ + (t₁ - t₀) • ((F t₁ (U₀ * L₁ᵀ))ᵀ * U₀)
  /-- The L-stage is the limit of the fixed-point iteration started at `V₀ S₀ᵀ`. -/
  lIter : Tendsto (fun j => (fun L => V₀ * S₀ᵀ + (t₁ - t₀) • ((F t₁ (U₀ * Lᵀ))ᵀ * U₀))^[j]
    (V₀ * S₀ᵀ)) atTop (𝓝 L₁)
  /-- The new column basis is orthonormal. -/
  orthU₁ : U₁ᵀ * U₁ = 1
  /-- The range of the new column basis contains the columns of `K₁`. -/
  kCap : U₁ * U₁ᵀ * K₁ = K₁
  /-- The new row basis is orthonormal. -/
  orthV₁ : V₁ᵀ * V₁ = 1
  /-- The range of the new row basis contains the columns of `L₁`. -/
  lCap : V₁ * V₁ᵀ * L₁ = L₁
  /-- Backward Euler Galerkin S-step. -/
  sStep : S₁ = U₁ᵀ * (U₀ * S₀ * V₀ᵀ + (t₁ - t₀) • F t₁ (U₁ * S₁ * V₁ᵀ)) * V₁
  /-- The S-stage is the limit of the fixed-point iteration started at `U₁ᵀ U₀ S₀ V₀ᵀ V₁`. -/
  sIter : Tendsto (fun j => (fun S => U₁ᵀ * (U₀ * S₀ * V₀ᵀ + (t₁ - t₀) •
    F t₁ (U₁ * S * V₁ᵀ)) * V₁)^[j] (U₁ᵀ * U₀ * S₀ * (V₀ᵀ * V₁))) atTop (𝓝 S₁)
```

`MatrixImplicitBUG.stepRel` in [`LeanDLRA/Stiff/Defs.lean`, lines 100–105](../LeanDLRA/Stiff/Defs.lean#L100-L105):

```lean
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
      (K₁ : Matrix m (Fin r) ℝ) (L₁ : Matrix n (Fin r) ℝ) (U₁ : Matrix m (Fin r) ℝ)
      (V₁ : Matrix n (Fin r) ℝ) (S₁ : Matrix (Fin r) (Fin r) ℝ),
      Y₀ = U₀ * S₀ * V₀ᵀ ∧ IsStep F t₀ t₁ U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ ∧ Y₁ = U₁ * S₁ * V₁ᵀ
```

`MatrixImplicitBUG.exists_stepRel` in [`LeanDLRA/Stiff/ImplicitBUGStep.lean`, lines 787–789](../LeanDLRA/Stiff/ImplicitBUGStep.lean#L787-L789):

```lean
theorem exists_stepRel (hG : IsLipschitzField G L) (h01 : t₀ ≤ t₁) (hhL : (t₁ - t₀) * L < 1)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) : ∃ Y₁, stepRel G r t₀ t₁ Y₀ Y₁
```

`MatrixImplicitBUG.exists_run_norm_sub_le` in [`LeanDLRA/Stiff/ImplicitBUGRun.lean`, lines 125–139](../LeanDLRA/Stiff/ImplicitBUGRun.lean#L125-L139):

```lean
theorem exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → (s, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ →
      (t, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ → ‖F t x - F s x‖ ≤ Lt * (t - s))
    (hh : 0 ≤ h) (hhL : h * L ≤ 1 / 2) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) * ((14 * L * B + 8 * Lt) * h + 6 * ε) +
      4 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * δ + T * Real.exp (L * T) * ((14 * L * B + 8 * Lt) * h + 6 * ε)
```

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

`primalDual_error_identity` in [`LeanDLRA/Stiff/DualWeightedResidual.lean`, lines 141–145](../LeanDLRA/Stiff/DualWeightedResidual.lean#L141-L145):

```lean
theorem primalDual_error_identity (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hA : ∀ k < N, A (k + 1) - h • 𝓛 k (A (k + 1)) = A k + h • q k) :
    ∀ n ≤ N, ⟪ψ n, Y n - A n⟫ = ⟪ψ 0, Y 0 - A 0⟫
      + ∑ k ∈ range n, ⟪ψ k, Y (k + 1) - Y k - h • (𝓛 k (Y (k + 1)) + q k)⟫
      - ∑ k ∈ range n, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), Y (k + 1) - A (k + 1)⟫
```

`dual_error_representation` in [`LeanDLRA/Stiff/DualWeightedResidual.lean`, lines 160–164](../LeanDLRA/Stiff/DualWeightedResidual.lean#L160-L164):

```lean
theorem dual_error_representation (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hA : ∀ k < N, A (k + 1) - h • 𝓛 k (A (k + 1)) = A k + h • q k)
    (hψ : ∀ k < N, ψ k - h • 𝓛' k (ψ k) = ψ (k + 1)) :
    ⟪ψ N, Y N - A N⟫ = ⟪ψ 0, Y 0 - A 0⟫
      + ∑ k ∈ range N, ⟪ψ k, Y (k + 1) - Y k - h • (𝓛 k (Y (k + 1)) + q k)⟫
```

The identity holds for arbitrary sequences `Y` and `ψ`: the error of `Y` weighted by `ψ n`
equals the weighted initial error, plus the primal residuals weighted by `ψ`, minus the dual
residuals paired with the errors. If `ψ` solves the discrete adjoint equation exactly (`hψ`, the
dual residuals vanish), the output error is exactly the weighted initial error plus the sum of
the weighted primal residuals. No constants appear, and the identities are equalities: no
singular value, no Lipschitz constant and no step size restriction enters. The reference `A`
is the implicit Euler sequence of the full problem and not the exact solution of the
differential equation.

`abs_corrected_output_sub_le` in [`LeanDLRA/Stiff/DualWeightedResidual.lean`, lines 223–230](../LeanDLRA/Stiff/DualWeightedResidual.lean#L223-L230):

```lean
theorem abs_corrected_output_sub_le (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hA : ∀ k < N, A (k + 1) - h • 𝓛 k (A (k + 1)) = A k + h • q k) (hh : 0 ≤ h) {ℓ : ℝ}
    (hℓ : h * ℓ < 1) (hdis : ∀ k x, ⟪𝓛 k x, x⟫ ≤ ℓ * ‖x‖ ^ 2) :
    |⟪ψ N, Y N⟫ - ∑ k ∈ range N, ⟪ψ k, Y (k + 1) - Y k - h • (𝓛 k (Y (k + 1)) + q k)⟫
        - ⟪ψ N, A N⟫|
      ≤ ‖ψ 0‖ * ‖Y 0 - A 0‖ + ∑ k ∈ range N, ‖ψ k - h • 𝓛' k (ψ k) - ψ (k + 1)‖
          * (max 1 (1 - h * ℓ)⁻¹ ^ (k + 1) * (‖Y 0 - A 0‖
            + ∑ j ∈ range (k + 1), ‖Y (j + 1) - Y j - h • (𝓛 j (Y (j + 1)) + q j)‖))
```

The product bound. If `⟪𝓛 k x, x⟫ ≤ ℓ * ‖x‖²`, `h ≥ 0` and `h * ℓ < 1`, the output corrected by
the weighted primal residuals differs from the reference output `⟪ψ N, A N⟫` by at most the
initial term `‖ψ 0‖ * ‖Y 0 - A 0‖` plus a sum of products: the norm of the `k`-th dual residual
times the initial error plus the norms of the primal residuals up to index `k`, with the
stability factor `a = max 1 (1 - h * ℓ)⁻¹` to the power `k + 1`. The factor depends on `h` and
`ℓ` and not on a Lipschitz constant.

`galerkin_output_error` in [`LeanDLRA/Stiff/DualWeightedResidual.lean`, lines 425–431](../LeanDLRA/Stiff/DualWeightedResidual.lean#L425-L431):

```lean
theorem galerkin_output_error {P : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k))
    (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hA : ∀ k < N, A (k + 1) - h • 𝓛 k (A (k + 1)) = A k + h • q k)
    (hY : ∀ k < N, Y (k + 1) = P k (Y k + h • (𝓛 k (Y (k + 1)) + q k)))
    (hψP : ∀ k < N, P k (ψ k) = ψ k) :
    ⟪ψ N, Y N - A N⟫ = ⟪ψ 0, Y 0 - A 0⟫
      - ∑ k ∈ range N, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), Y (k + 1) - A (k + 1)⟫
```

`implicitBUG_dualConsistent_output_error` in [`LeanDLRA/Stiff/DualWeightedResidual.lean`, lines 623–634](../LeanDLRA/Stiff/DualWeightedResidual.lean#L623-L634):

```lean
theorem implicitBUG_dualConsistent_output_error {ε τ ϑ t : ℕ → ℝ}
    {P₀ Q₀ P₁ Q₁ C : ℕ → E →L[ℝ] E} {YK YL : ℕ → E} {T : ℕ → E → E}
    (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hA : ∀ k < N, A (k + 1) - h • 𝓛 k (A (k + 1)) = A k + h • q k)
    (hs : ∀ k < N, IsImplicitBUGStep (fun _ x => 𝓛 k x + q k) (ε k) (τ k) (ϑ k) (P₀ k) (Q₀ k)
      (P₁ k) (Q₁ k) (t k) h (Y k) (YK k) (YL k) (X k) (Y (k + 1)))
    (hψ : ∀ k < N, (P₁ k * Q₁ k) (ψ k) = ψ k)
    (hC : ∀ k < N, IsOrthProj (C k)) (hCψ : ∀ k < N, C k (ψ (k + 1)) = ψ (k + 1))
    (hT : ∀ k < N, C k (T k (X k - C k (X k))) = 0)
    (hY : ∀ k < N, Y (k + 1) = consTrunc (C k) (T k) (X k)) :
    ⟪ψ N, Y N - A N⟫ = ⟪ψ 0, Y 0 - A 0⟫
      - ∑ k ∈ range N, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), X k - A (k + 1)⟫
```

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

`consTrunc` in [`LeanDLRA/Stability/Conservation.lean`, line 292](../LeanDLRA/Stability/Conservation.lean#L292):

```lean
def consTrunc (C : E →L[ℝ] E) (T : E → E) (Y : E) : E := C Y + T (Y - C Y)
```

### 7.3 One step for a field with a stiff linear part: coupling numbers

`IsRankAdaptiveBUGStep.stiff_local_error` in [`LeanDLRA/Stiff/CouplingLocalError.lean`, lines 425–439](../LeanDLRA/Stiff/CouplingLocalError.lean#L425-L439):

```lean
theorem IsRankAdaptiveBUGStep.stiff_local_error {F G : ℝ → E → E} {𝓛 P₀ Q₀ P₁ Q₁ : E →L[ℝ] E}
    {ℓ LG κ κh B₁ B₂ ε ϑ : ℝ} {A YK YL YS : ℝ → E} {Y₀ Y₁ : E} {t₀ t₁ h : ℝ}
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hF : IsOneSidedLipschitzField F ℓ) (hsplit : ∀ t x, F t x = 𝓛 x + G t x)
    (hG : IsLipschitzField G LG) (hLG : 0 ≤ LG) (hκ0 : 0 ≤ κ) (hκh0 : 0 ≤ κh)
    (hκQ : ∀ x, ‖Q₀ (𝓛 (x - Q₀ x))‖ ≤ κ * ‖x - Q₀ x‖)
    (hκQ' : ∀ x, ‖𝓛 (Q₀ x) - Q₀ (𝓛 (Q₀ x))‖ ≤ κ * ‖Q₀ x‖)
    (hκP : ∀ x, ‖P₀ (𝓛 (x - P₀ x))‖ ≤ κ * ‖x - P₀ x‖)
    (hκP' : ∀ x, ‖𝓛 (P₀ x) - P₀ (𝓛 (P₀ x))‖ ≤ κ * ‖P₀ x‖)
    (hκh : ∀ x, ‖(P₁ * Q₁) (𝓛 (x - (P₁ * Q₁) x))‖ ≤ κh * ‖x - (P₁ * Q₁) x‖)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hB₁ : ∀ t ∈ Icc t₀ t₁, ‖F t (A t)‖ ≤ B₁) (hB₂ : ∀ t ∈ Icc t₀ t₁, ‖𝓛 (F t (A t))‖ ≤ B₂)
    (hP₀Y : P₀ Y₀ = Y₀) (hQ₀Y : Q₀ Y₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ (κh + LG) * (h * B₁) * h * max 1 (Real.exp (ℓ * h))
      + 2 * stiffCapture ℓ LG κ B₁ B₂ ε h + ϑ
```

`stiffCaptureConst` in [`LeanDLRA/Stiff/CouplingLocalError.lean`, lines 144–145](../LeanDLRA/Stiff/CouplingLocalError.lean#L144-L145):

```lean
noncomputable def stiffCaptureConst (ℓ LG κ B₁ B₂ h : ℝ) : ℝ :=
  (κ + LG) * B₁ * max 1 (Real.exp (ℓ * h)) * (1 + h * (κ + LG)) + 2 * B₂ + (κ + 2 * LG) * B₁
```

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

`StiffOrderReduction.Example.not_exists_uniform_bound` in [`LeanDLRA/Research/StiffOrderReduction.lean`, lines 881–884](../LeanDLRA/Research/StiffOrderReduction.lean#L881-L884):

```lean
theorem not_exists_uniform_bound :
    ¬ ∃ K : ℝ, ∀ c s lam σ h : ℝ, c ^ 2 + s ^ 2 = 1 → 0 < lam → s ≠ 0 → 0 < h → h ≤ 1 / 2 →
      ‖result c s lam σ h - exact U₀ (S₀ σ) (V₀ c s) D h‖
        ≤ K * (h * normalDefect c s lam σ + h ^ 2)
```

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

`StiffGlobalCycle.half_le_norm_sub_exactState` in [`LeanDLRA/Research/StiffGlobalCycle.lean`, lines 544–546](../LeanDLRA/Research/StiffGlobalCycle.lean#L544-L546):

```lean
theorem half_le_norm_sub_exactState (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0)
    (hx : 2 ≤ lam * s ^ 2 * h) (J : ℕ) :
    J * h / 2 ≤ ‖state c s σ 0 0 - exactState c s lam σ h J‖
```

`StiffGlobalCycle.not_exists_uniform_global_bound` in [`LeanDLRA/Research/StiffGlobalCycle.lean`, lines 688–691](../LeanDLRA/Research/StiffGlobalCycle.lean#L688-L691):

```lean
theorem not_exists_uniform_global_bound :
    ¬ ∃ K : ℝ, ∀ (c s lam σ h : ℝ) (J : ℕ), c ^ 2 + s ^ 2 = 1 → 0 < lam → 0 < s → 0 < h →
      0 < σ → σ * lam ≤ 1 → 2 ≤ lam * s ^ 2 * h → 3 * (J : ℝ) * h ≤ 1 →
      ‖state c s σ 0 0 - exactState c s lam σ h J‖ ≤ K * (h * (1 + |Real.log h|) + s)
```

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

`StiffGlobalCycle.variation_mul_le_norm_sub_exactState` in [`LeanDLRA/Research/StiffGlobalVariation.lean`, lines 99–104](../LeanDLRA/Research/StiffGlobalVariation.lean#L99-L104):

```lean
theorem variation_mul_le_norm_sub_exactState (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam)
    (hs : s ≠ 0) (hh : 0 < h) (hx : 2 ≤ lam * s ^ 2 * h) (J : ℕ) :
    h / 12 * (J * (‖cycleForcing c s lam σ h 1 - cycleForcing c s lam σ h 0‖ +
      ‖cycleForcing c s lam σ h 2 - cycleForcing c s lam σ h 1‖ +
        ‖cycleForcing c s lam σ h 0 - cycleForcing c s lam σ h 2‖)) ≤
      ‖state c s σ 0 0 - exactState c s lam σ h J‖
```

Lower bound in terms of the variation. `StiffGlobalCycle` (section 7.5) uses a forcing that is
piecewise constant with period `3 h`, `cycleForcing c s lam σ h k`, on `2 × 2` matrices. The
three jumps of one cycle have norms that add up to at most 6, for every stiffness `lam` and step
size (`StiffGlobalCycle.variation_cycleForcing_le`). If `lam s² h ≥ 2`, the error after `J` cycles
is at least `h / 12` times `J` times the sum of the three jumps, that is at least `h / 12` times
the variation of the forcing over these cycles. Hence a bound that is uniform in the stiffness and
contains the variation of the forcing must contain it at least in the form `h · Var g`, with a
factor at least `1 / 12`; a bound `C h (1 + Var g)^γ` with `γ < 1` is excluded. The theorem does
not decide whether `C (h (1 + Var g) + ε + n ϑ)` holds uniformly in the stiffness.

`IsRankAdaptiveBUGStep.stiff_energy_error` in [`LeanDLRA/Research/StiffEnergyGalerkin.lean`, lines 135–143](../LeanDLRA/Research/StiffEnergyGalerkin.lean#L135-L143):

```lean
theorem IsRankAdaptiveBUGStep.stiff_energy_error {F : ℝ → E → E} {g : ℝ → E}
    {𝓛 P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {ε ϑ γ θ : ℝ} {A YK YL YS : ℝ → E} {Y₀ Y₁ : E} {t₀ t₁ : ℝ}
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hsplit : ∀ t x, F t x = 𝓛 x + g t) (hsym : ∀ x y, ⟪𝓛 x, y⟫ = ⟪x, 𝓛 y⟫)
    (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0) (hle : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁) (hγ0 : 0 ≤ γ)
    (hγ : ∀ t ∈ Ico t₀ t₁,
      -⟪𝓛 (A t - (P₁ * Q₁) (A t)), A t - (P₁ * Q₁) (A t)⟫ ≤ γ ^ 2)
    (hθ : ‖A t₁ - (P₁ * Q₁) (A t₁)‖ ≤ θ) :
    ‖Y₁ - A t₁‖ ≤ ‖Y₀ - A t₀‖ + γ * √((t₁ - t₀) / 2) + θ + ϑ
```

`stiff_energy_global_error` in [`LeanDLRA/Research/StiffEnergyGalerkin.lean`, lines 192–204](../LeanDLRA/Research/StiffEnergyGalerkin.lean#L192-L204):

```lean
theorem stiff_energy_global_error {F : ℝ → E → E} {g : ℝ → E} {𝓛 : E →L[ℝ] E} {ε : ℝ}
    {ϑ γ θ : ℕ → ℝ} {τ : ℕ → ℝ} {N : ℕ} {P Q Pa Qa : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YK YL YS : ℕ → ℝ → E} {A : ℝ → E}
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε (ϑ n) (P n) (Q n) (Pa n) (Qa n) (τ n)
      (τ (n + 1)) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hτ : ∀ n < N, τ n ≤ τ (n + 1)) (hsplit : ∀ t x, F t x = 𝓛 x + g t)
    (hsym : ∀ x y, ⟪𝓛 x, y⟫ = ⟪x, 𝓛 y⟫) (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hA : ∀ n < N, ODESolution F A (τ n) (τ (n + 1))) (hγ0 : ∀ n < N, 0 ≤ γ n)
    (hγ : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)),
      -⟪𝓛 (A t - (Pa n * Qa n) (A t)), A t - (Pa n * Qa n) (A t)⟫ ≤ γ n ^ 2)
    (hθ : ∀ n < N, ‖A (τ (n + 1)) - (Pa n * Qa n) (A (τ (n + 1)))‖ ≤ θ n) :
    ‖Y N - A (τ N)‖ ≤ ‖Y 0 - A (τ 0)‖
      + ∑ n ∈ Finset.range N, (γ n * √((τ (n + 1) - τ n) / 2) + θ n + ϑ n)
```

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

`IsRankAdaptiveBUGStep.stiff_error_of_comm_left` in [`LeanDLRA/Research/StiffOldColumnGalerkin.lean`, lines 148–154](../LeanDLRA/Research/StiffOldColumnGalerkin.lean#L148-L154):

```lean
theorem stiff_error_of_comm_left
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hsplit : ∀ t x, F t x = 𝓛 x + g t) (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hP𝓛 : ∀ x, P₀ (𝓛 x) = 𝓛 (P₀ x)) (hY₀ : P₀ Y₀ = Y₀) (hle : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁) (hβ : ∀ t ∈ Ico t₀ t₁, ‖g t - P₀ (g t)‖ ≤ β) :
    ‖Y₁ - A t₁‖ ≤ ‖Y₀ - A t₀‖ + ‖P₀ (YS t₁) - YL t₁‖ + ‖YS t₁ - P₀ (YS t₁)‖
      + β * (t₁ - t₀) + ϑ
```

`stiff_global_error_of_comm_left` in [`LeanDLRA/Research/StiffOldColumnGalerkin.lean`, lines 379–392](../LeanDLRA/Research/StiffOldColumnGalerkin.lean#L379-L392):

```lean
theorem stiff_global_error_of_comm_left {F : ℝ → E → E} {g : ℝ → E} {𝓛 : E →L[ℝ] E} {ε : ℝ}
    {ϑ β : ℕ → ℝ} {τ : ℕ → ℝ} {N : ℕ} {P Q Pa Qa : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YK YL YS : ℕ → ℝ → E} {A : ℝ → E}
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε (ϑ n) (P n) (Q n) (Pa n) (Qa n) (τ n)
      (τ (n + 1)) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hτ : ∀ n < N, τ n ≤ τ (n + 1)) (hsplit : ∀ t x, F t x = 𝓛 x + g t)
    (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0) (hP𝓛 : ∀ n < N, ∀ x, P n (𝓛 x) = 𝓛 (P n x))
    (hPP : ∀ n < N, ∀ x, P n (Pa n x) = Pa n (P n x))
    (hPQ : ∀ n < N, ∀ x, P n (Qa n x) = Qa n (P n x)) (hY : ∀ n < N, P n (Y n) = Y n)
    (hA : ∀ n < N, ODESolution F A (τ n) (τ (n + 1)))
    (hβ : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)), ‖g t - P n (g t)‖ ≤ β n) :
    ‖Y N - A (τ N)‖ ≤ ‖Y 0 - A (τ 0)‖
      + ∑ n ∈ Finset.range N, (‖P n (YS n (τ (n + 1))) - YL n (τ (n + 1))‖
        + 2 * β n * (τ (n + 1) - τ n) + ϑ n)
```

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

`stiff_global_error_of_piecewise_const_uniform` in [`LeanDLRA/Research/StiffOldColumnVariation.lean`, lines 311–327](../LeanDLRA/Research/StiffOldColumnVariation.lean#L311-L327):

```lean
theorem stiff_global_error_of_piecewise_const_uniform
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε (ϑ n) (P n) (Q n) (Pa n) (Qa n) (τ n)
      (τ (n + 1)) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hh : 0 < h) (hτ : ∀ n < N, τ (n + 1) - τ n = h) (hsplit : ∀ t x, F t x = 𝓛 x + g t)
    (hconst : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)), g t = c n)
    (hsym : ∀ x y, ⟪𝓛 x, y⟫ = ⟪x, 𝓛 y⟫) (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hP𝓛 : ∀ n < N, ∀ x, P n (𝓛 x) = 𝓛 (P n x))
    (hPa𝓛 : ∀ n < N, ∀ x, Pa n (𝓛 x) = 𝓛 (Pa n x))
    (hnest : ∀ n < N, ∀ x, Pa n (P n x) = P n x)
    (hPQ : ∀ n < N, ∀ x, P n (Qa n x) = Qa n (P n x))
    (hPaQ : ∀ n < N, ∀ x, Pa n (Q n x) = Q n (Pa n x)) (hY : ∀ n < N, P n (Y n) = Y n)
    (hA : ∀ n < N, ODESolution F A (τ n) (τ (n + 1)))
    (hcol : ∀ n, n + 1 < N → Pa n (c n) = P (n + 1) (c n)) :
    ‖Y N - A (τ N)‖ ≤ ‖Y 0 - A (τ 0)‖
      + ∑ n ∈ Finset.range N, (‖P n (YS n (τ (n + 1))) - YL n (τ (n + 1))‖ + ϑ n)
      + 2 * h * (‖c 0 - P 0 (c 0)‖ + ∑ n ∈ Finset.range (N - 1), ‖c (n + 1) - c n‖)
      + 2 * h * N * ε
```

`IsRankAdaptiveBUGStep.norm_left_galerkin_sub_lstep_le` in [`LeanDLRA/Research/StiffOldColumnVariation.lean`, lines 123–129](../LeanDLRA/Research/StiffOldColumnVariation.lean#L123-L129):

```lean
theorem norm_left_galerkin_sub_lstep_le
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hsplit : ∀ t ∈ Ico t₀ t₁, ∀ x, F t x = 𝓛 x + c) (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hP𝓛 : ∀ x, P₀ (𝓛 x) = 𝓛 (P₀ x)) (hnest : ∀ x, P₁ (P₀ x) = P₀ x)
    (hPQ : ∀ x, P₀ (Q₁ x) = Q₁ (P₀ x)) (hY₀ : P₀ Y₀ = Y₀) (hlt : t₀ < t₁)
    (hμ : ∀ t ∈ Icc t₀ t₁, ‖𝓛 (YL t - Y₀)‖ ≤ μ) :
    ‖P₀ (YS t₁) - YL t₁‖ ≤ 2 * μ * (t₁ - t₀)
```

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

`StiffVelocityVariation.sqrt_mul_norm_le_sum_norm_map_sub` in [`LeanDLRA/Research/StiffVelocityVariation.lean`, lines 267–272](../LeanDLRA/Research/StiffVelocityVariation.lean#L267-L272):

```lean
theorem sqrt_mul_norm_le_sum_norm_map_sub (hh : 0 < h)
    (he : ∀ j < K, ∀ k < K, ⟪e j, e k⟫ = if j = k then 1 else 0)
    (h𝓛 : ∀ k < K, 𝓛 (e k) = -(dyadicRate h k) • e k) (hc : 𝓛 xs + c = 0) :
    √K / 4 * ‖𝓛 (dyadicTrajectory e xs h K 0) + c‖
      ≤ ∑ n ∈ Finset.range (2 ^ K), ‖𝓛 (dyadicTrajectory e xs h K ((n + 1) * h)
        - dyadicTrajectory e xs h K (n * h))‖
```

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

`IsRankAdaptiveBUGStep.stiff_error_of_invariant_galerkin` in [`LeanDLRA/Research/StiffInvariantGalerkin.lean`, lines 114–121](../LeanDLRA/Research/StiffInvariantGalerkin.lean#L114-L121):

```lean
theorem stiff_error_of_invariant_galerkin
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hsplit : ∀ t x, F t x = 𝓛 x + f t x) (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hf : ∀ t ∈ Ico t₀ t₁, ⟪f t (YS t) - f t (A t), YS t - A t⟫ ≤ ℓ * ‖YS t - A t‖ ^ 2)
    (hinv : ∀ x, P₁ (Q₁ x) = x → P₁ (Q₁ (𝓛 x)) = 𝓛 x) (hle : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁)
    (hη : ∀ t ∈ Ico t₀ t₁, ‖f t (YS t) - P₁ (Q₁ (f t (YS t)))‖ ≤ η) :
    ‖Y₁ - A t₁‖ ≤ gronwallBound ‖Y₀ - A t₀‖ ℓ η (t₁ - t₀) + ϑ
```

`stiff_global_error_of_invariant_galerkin` in [`LeanDLRA/Research/StiffInvariantGalerkin.lean`, lines 238–249](../LeanDLRA/Research/StiffInvariantGalerkin.lean#L238-L249):

```lean
theorem stiff_global_error_of_invariant_galerkin {F : ℝ → E → E} {g : ℝ → E} {𝓛 : E →L[ℝ] E}
    {ε : ℝ} {ϑ η : ℕ → ℝ} {τ : ℕ → ℝ} {N : ℕ} {P Q Pa Qa : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YK YL YS : ℕ → ℝ → E} {A : ℝ → E}
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε (ϑ n) (P n) (Q n) (Pa n) (Qa n) (τ n)
      (τ (n + 1)) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hτ : ∀ n < N, τ n ≤ τ (n + 1)) (hsplit : ∀ t x, F t x = 𝓛 x + g t)
    (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hinv : ∀ n < N, ∀ x, Pa n (Qa n x) = x → Pa n (Qa n (𝓛 x)) = 𝓛 x)
    (hA : ∀ n < N, ODESolution F A (τ n) (τ (n + 1)))
    (hη : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)), ‖g t - Pa n (Qa n (g t))‖ ≤ η n) :
    ‖Y N - A (τ N)‖ ≤ ‖Y 0 - A (τ 0)‖
      + ∑ n ∈ Finset.range N, (η n * (τ (n + 1) - τ n) + ϑ n)
```

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

## 8. Tensors

A tensor with mode index types `ι k` is an element of `Tensor ι`, the Euclidean space of
functions on the multi-indices. `unfold p X` is the unfolding (matricization) of `X` with
respect to the set of modes `p`: the rows are indexed by the part of the multi-index in `p`, the
columns by the rest. The core has the following results.

### 8.1 Tensor trains

`Tensor.unfold_tt` in [`LeanDLRA/Tensor/TT/Basic.lean`, lines 157–158](../LeanDLRA/Tensor/TT/Basic.lean#L157-L158):

```lean
theorem unfold_tt (k : ℕ) (hk : k ≤ d) :
    unfold (fun i : Fin d => i.val < k) (tt G) = ttLeft G k * (ttRight G k)ᵀ
```

`Tensor.rank_unfold_tt_le` in [`LeanDLRA/Tensor/TT/Basic.lean`, lines 164–165](../LeanDLRA/Tensor/TT/Basic.lean#L164-L165):

```lean
theorem rank_unfold_tt_le [∀ i, Fintype (ι i)] (k : ℕ) (hk : k ≤ d) :
    (unfold (fun i : Fin d => i.val < k) (tt G)).rank ≤ Fintype.card (β k)
```

For a tensor train `tt G` with cores `G` and bond index types `β k`, and for `k ≤ d`, the
unfolding with the first `k` modes as rows is the product of the left interface matrix
`ttLeft G k` and the transpose of the right interface matrix `ttRight G k`; its rank is at most
the number `Fintype.card (β k)` of elements of the `k`-th bond index type.

Source: arXiv 2402.18721, Eq. (16), as cited in the docstring of the first theorem.

`Tensor.isOrthProj_ttTangentProj` in [`LeanDLRA/Tensor/TT/TangentProjector.lean`, lines 367–369](../LeanDLRA/Tensor/TT/TangentProjector.lean#L367-L369):

```lean
theorem isOrthProj_ttTangentProj [Unique (β 0)] [Unique (β d)] {A B : TTCores ι β}
    (hA : ∀ i, IsLeftOrth A i) (hB : ∀ i, IsRightOrth B i) :
    IsOrthProj (ttTangentProj A B)
```

For left-orthogonal cores `A` (`hA`) and right-orthogonal cores `B` (`hB`) of a tensor train
whose boundary bond index types `β 0` and `β d` have one element, the operator
`ttTangentProj A B` is an orthogonal projector (`IsOrthProj`: idempotent and symmetric). The
docstring calls it the tangent projector of the tensor train format; the theorem does not relate
it to a tangent space.

Source: Lubich, Oseledets and Vandereycken, arXiv 1407.2042, Theorem 3.1 and Corollary 3.2, as
cited in the docstring.

**The tensor-train projector-splitting integrator.**

`Tensor.IsTTKSLStep.exact` in [`LeanDLRA/Tensor/TT/ProjectorSplittingExactness.lean`, lines 254–259](../LeanDLRA/Tensor/TT/ProjectorSplittingExactness.lean#L254-L259):

```lean
theorem exact (hs : IsTTKSLStep F U V t₀ t₁ Y₀ YK YS) (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) (hY₀ : Y₀ = A t₀)
    (hrec : ∀ k, k + 1 < d → Exactness.IsRecoverable
      (Set.range (actOn (ι := ι) fun i : Fin d => i.val < k + 1)) (ttRightProj V (k + 1))
      (A t₁)) (hd : 0 < d) :
    YK (d - 1) t₁ = A t₁
```

`Tensor.IsTTKSLStep.local_error` in [`LeanDLRA/Tensor/TT/ProjectorSplittingError.lean`, lines 159–167](../LeanDLRA/Tensor/TT/ProjectorSplittingError.lean#L159-L167):

```lean
theorem local_error (hs : IsTTKSLStep F U V t₀ t₁ Y₀ YK YS) {L B ε h : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x)
    (hε : ∀ k, k + 1 < d → ∀ t ∈ Icc t₀ t₁,
      ‖(1 - ttLeftProj U (k + 1)) ((1 - ttRightProj V (k + 1)) (F t (YK k t₁)))‖ ≤ ε)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {A : ℝ → Tensor ι} (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = Y₀) (hd : 0 < d) :
    ‖YK (d - 1) t₁ - A t₁‖ ≤
      (∑ j ∈ Finset.range (d - 1), (2 + 3 * L * h) ^ j) * (h * (11 * L * B * h + ε))
```

`Tensor.tt_ksl_global_error` in [`LeanDLRA/Tensor/TT/ProjectorSplittingError.lean`, lines 185–201](../LeanDLRA/Tensor/TT/ProjectorSplittingError.lean#L185-L201):

```lean
theorem tt_ksl_global_error {F : ℝ → Tensor ι → Tensor ι} {L B ε : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (hcont : ∀ x, Continuous fun t => F t x)
    (hε₀ : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → Tensor ι}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {U V : ℕ → TTCores ι β} {Y : ℕ → Tensor ι}
    {YK YS : ℕ → ℕ → ℝ → Tensor ι}
    (hstep : ∀ n < N, IsTTKSLStep F (U n) (V n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (YK n)
      (YS n))
    (hY : ∀ n < N, Y (n + 1) = YK n (d - 1) (t₀ + (n + 1) * h))
    (hε : ∀ n < N, ∀ k, k + 1 < d → ∀ t ∈ Icc (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖(1 - ttLeftProj (U n) (k + 1)) ((1 - ttRightProj (V n) (k + 1))
        (F t (YK n k (t₀ + (n + 1) * h))))‖ ≤ ε)
    {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) (hd : 0 < d) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ +
        T * Real.exp (L * T) * (∑ j ∈ Finset.range (d - 1), (2 + 3 * L * H) ^ j) * ε +
        11 * L * B * T * Real.exp (L * T) * (∑ j ∈ Finset.range (d - 1), (2 + 3 * L * H) ^ j) *
          h
```

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

### 8.2 Tucker tensors

`Tensor.tuckerTangentProj_eq_starProjection` in [`LeanDLRA/Tensor/Tucker/Tangent.lean`, lines 360–364](../LeanDLRA/Tensor/Tucker/Tangent.lean#L360-L364):

```lean
theorem tuckerTangentProj_eq_starProjection (hPC : IsOrthProj PC) {s : Fin d → Type*}
    [∀ k, Fintype (s k)] {W : ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s k) ℝ}
    (hWX : ∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U)
    (hWB : ∀ k, ∃ B : Matrix _ (s k) ℝ, W k = unfold (· ≠ k) (tucker C U) * B) :
    tuckerTangentProj U PC W = (tuckerTangentSpace U C PC).starProjection
```

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

`IsTuckerBUGStep` in [`LeanDLRA/Integrators/TuckerBUG.lean`, lines 724–738](../LeanDLRA/Integrators/TuckerBUG.lean#L724-L738):

```lean
structure IsTuckerBUGStep (F : ℝ → E → E) (ε : ℝ) {d : ℕ} (Q₀ P₁ : Fin d → E →L[ℝ] E)
    (t₀ t₁ : ℝ) (Y₀ : E) (YK : Fin d → ℝ → E) (YS : ℝ → E) : Prop where
  projQ₀ : ∀ i, IsOrthProj (Q₀ i)
  projP₁ : ∀ i, IsOrthProj (P₁ i)
  /-- The new mode projectors act on different modes and commute. -/
  comm₁ : ∀ i j x, P₁ i (P₁ j x) = P₁ j (P₁ i x)
  /-- Mode-`i` K-step: `YK i' = Q₀ i F(t, YK i)` (the matrix K-step `K̇ᵢ = Fᵢ(t, Kᵢ V⁰ᵢᵀ) V⁰ᵢ`). -/
  kSol : ∀ i, ODESolution (fun t x => Q₀ i (F t x)) (YK i) t₀ t₁
  kStart : ∀ i, YK i t₀ = Y₀
  /-- The new mode-`i` basis captures `Kᵢ(t₁)`. -/
  kCap : ∀ i, P₁ i (YK i t₁) = YK i t₁
  kNormal : ∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁ i) ((1 - Q₀ i) (F t (YK i t₁)))‖ ≤ ε
  /-- Core (Galerkin) step: `YS' = Π F(t, YS)` with `Π = P₁ 0 ∘ ⋯ ∘ P₁ (d-1)`. -/
  sSol : ODESolution (fun t x => modeProd P₁ (F t x)) YS t₀ t₁
  sStart : YS t₀ = modeProd P₁ Y₀
```

`tucker_global_error_le` in [`LeanDLRA/Integrators/TuckerBUG.lean`, lines 873–885](../LeanDLRA/Integrators/TuckerBUG.lean#L873-L885):

```lean
theorem tucker_global_error_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ}
    {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {Q P : ℕ → Fin d → E →L[ℝ] E}
    {Y : ℕ → E} {YK : ℕ → Fin d → ℝ → E} {YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsTuckerBUGStep F ε (Q n) (P n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
      (YK n) (YS n))
    (hY : ∀ n < N, Y (n + 1) = YS n (t₀ + (n + 1) * h))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * tuckerC₁ d L H * ε
        + T * Real.exp (L * T) * tuckerC₂ d L B H * h
```

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

`TuckerBUG.stepRel` in [`LeanDLRA/Tensor/Tucker/BUGStep.lean`, lines 253–262](../LeanDLRA/Tensor/Tucker/BUGStep.lean#L253-L262):

```lean
def stepRel (F : ℝ → Tensor ι → Tensor ι) (r : Fin d → ℕ) : StepRel (Tensor ι) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ (V₀ : ∀ i, Matrix (∀ k : {k : Fin d // k ≠ i}, ι k) (Fin (r i)) ℝ)
      (U₁ : ∀ i, Matrix (ι i) (Fin (r i)) ℝ) (YK : Fin d → ℝ → Tensor ι) (YS : ℝ → Tensor ι),
      (∀ i, (V₀ i)ᵀ * V₀ i = 1) ∧ (∀ i, actOn (· ≠ i) (V₀ i * (V₀ i)ᵀ) Y₀ = Y₀) ∧
      (∀ i, (U₁ i)ᵀ * U₁ i = 1) ∧
      (∀ i, ODESolution (fun t x => actOn (· ≠ i) (V₀ i * (V₀ i)ᵀ) (F t x)) (YK i) t₀ t₁) ∧
      (∀ i, YK i t₀ = Y₀) ∧ (∀ i, modeProj i (U₁ i) (YK i t₁) = YK i t₁) ∧
      ODESolution (fun t x => modeProd (fun i => modeProj i (U₁ i)) (F t x)) YS t₀ t₁ ∧
      YS t₀ = modeProd (fun i => modeProj i (U₁ i)) Y₀ ∧ Y₁ = YS t₁
```

`TuckerBUG.isTubeLocal_stepRel` in [`LeanDLRA/Tensor/Tucker/BUGRun.lean`, lines 144–147](../LeanDLRA/Tensor/Tucker/BUGRun.lean#L144-L147):

```lean
theorem isTubeLocal_stepRel (hr : ∀ i, r i ≤ Fintype.card (ι i))
    (hr' : ∀ i, r i ≤ Fintype.card (∀ k : {k : Fin d // k ≠ i}, ι k)) :
    StepMethod.IsTubeLocal (fun G : ℝ → Tensor ι → Tensor ι => stepRel G r) (ModeRankLE r)
      (d + 2)
```

`TuckerBUG.exists_run_norm_sub_le` in [`LeanDLRA/Tensor/Tucker/BUGRun.lean`, lines 234–247](../LeanDLRA/Tensor/Tucker/BUGRun.lean#L234-L247):

```lean
theorem exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : NormalBoundOn F (normalTriples r) (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hr : ∀ i, r i ≤ Fintype.card (ι i))
    (hr' : ∀ i, r i ≤ Fintype.card (∀ k : {k : Fin d // k ≠ i}, ι k))
    {Y₀ : Tensor ι} (hY₀ : ModeRankLE r Y₀) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ +
      T * Real.exp (L * T) * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) + (d + 2) * B * h < ρ) :
    ∃ Y : ℕ → Tensor ι, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, ModeRankLE r (Y n) ∧ ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * δ +
          T * Real.exp (L * T) * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h)
```

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

`tucker_ksl_exact` in [`LeanDLRA/Tensor/TTN/Abstract/ProjectorSplittingExactness.lean`, lines 82–88](../LeanDLRA/Tensor/TTN/Abstract/ProjectorSplittingExactness.lean#L82-L88):

```lean
theorem tucker_ksl_exact {d : ℕ} {F : ℝ → E → E} {A : ℝ → E} {ε t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {Q₀ P₁ : Fin d → E →L[ℝ] E} {X : Fin (d + 1) → E}
    {K : Fin d → E} {YS : Fin d → ℝ → E} {YC : ℝ → E}
    (hs : IsTuckerKSLStep F ε Q₀ P₁ t₀ t₁ (A t₀) X K YS YC)
    (hK : IsExactKSteps F Q₀ P₁ t₀ t₁ X K) {𝓛 : Fin d → Set (E →L[ℝ] E)}
    (h𝓛 : ∀ i, P₁ i ∈ 𝓛 i) (hrec : ∀ i, Exactness.IsRecoverable (𝓛 i) (Q₀ i) (A t₁)) :
    YC t₁ = A t₁
```

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

`DimTree.projectorSplitting_global_error` in [`LeanDLRA/Tensor/TTN/ProjectorSplitting.lean`, lines 207–216](../LeanDLRA/Tensor/TTN/ProjectorSplitting.lean#L207-L216):

```lean
theorem projectorSplitting_global_error.{v} (τ : DimTree κ) {L B T : ℝ} (hL : 0 ≤ L)
    (hB : 0 ≤ B) (hT : 0 ≤ T) :
    ∃ c₀ c₁ c₂ : ℝ, ∀ {ι : κ → Type v} [∀ k, Fintype (ι k)] {F : ℝ → Tensor ι → Tensor ι}
      {ε δ t₀ h : ℝ} {N : ℕ} {A : ℝ → Tensor ι} {Y : ℕ → Tensor ι},
      IsLipschitzField F L → IsBoundedField F B → (∀ x, Continuous fun t => F t x) → 0 ≤ ε →
      0 ≤ h → (N : ℝ) * h ≤ T → ODESolution F A t₀ (t₀ + N * h) →
      (∀ n < N, τ.IsProjectorSplittingStep F ε (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
        (Y (n + 1))) →
      ‖Y 0 - A t₀‖ ≤ δ →
      ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ c₀ * δ + c₁ * ε + c₂ * h
```

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

`ttn_global_error_le` in [`LeanDLRA/Tensor/TTN/Abstract/BUG.lean`, lines 351–359](../LeanDLRA/Tensor/TTN/Abstract/BUG.lean#L351-L359):

```lean
theorem ttn_global_error_le [CompleteSpace E] (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hcont : ∀ x, Continuous fun t => F t x) (hε : 0 ≤ ε)
    {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h))
    {fr : ℕ → TTNFrame E} {Y : ℕ → E} {s ℓ : ℕ} (hsize : ∀ n < N, (fr n).size ≤ s)
    (hheight : ∀ n < N, (fr n).height ≤ ℓ) (hLh : 2 * L * h * ℓ ≤ 1)
    (hstep : ∀ n < N, IsTTNBUGStep (fr n) F ε (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (Y (n + 1)))
    {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * (δ + T * (3 * s * (ε + 6 * L * B * h)))
```

`augTTN_global_error_le` in [`LeanDLRA/Tensor/TTN/Abstract/RankAdaptiveBUG.lean`, lines 403–414](../LeanDLRA/Tensor/TTN/Abstract/RankAdaptiveBUG.lean#L403-L414):

```lean
theorem augTTN_global_error_le [CompleteSpace E] (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hcont : ∀ x, Continuous fun t => F t x) (hε : 0 ≤ ε)
    (hϑ : 0 ≤ ϑ) {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {fr : ℕ → TTNFrame E} {Y : ℕ → E} {s ℓ : ℕ}
    (hsize : ∀ n < N, (fr n).size ≤ s) (hheight : ∀ n < N, (fr n).height ≤ ℓ)
    (hLh : 2 * L * h * ℓ ≤ 1)
    (hstep : ∀ n < N,
      IsAugTTNBUGStep (fr n) F ε ϑ (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (Y (n + 1)))
    {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * (δ + T * (3 * s * (ε + 6 * L * B * h)) + 3 * s * (n * ϑ))
```

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

`DimTree.BasisFrame.bug_global_error` in [`LeanDLRA/Tensor/TTN/BUG.lean`, lines 117–127](../LeanDLRA/Tensor/TTN/BUG.lean#L117-L127):

```lean
theorem bug_global_error {τ : DimTree κ} (hv : τ.IsValid) {F : ℝ → Tensor ι → Tensor ι}
    {L B ε : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) (hε : 0 ≤ ε)
    {t₀ h : ℝ} (hh : 0 ≤ h) (hLh : 2 * L * h * τ.treeHeight ≤ 1) {N : ℕ}
    {A : ℝ → Tensor ι} (hA : ODESolution F A t₀ (t₀ + N * h)) {f : ℕ → BasisFrame ι τ}
    {Y : ℕ → Tensor ι}
    (hstep : ∀ n < N, (f n).IsBUGStep F ε (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (Y (n + 1)))
    {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * (δ + T * (3 * τ.nodeCount * (ε + 6 * L * B * h)))
```

`DimTree.BasisFrame.augBUG_global_error` in [`LeanDLRA/Tensor/TTN/RankAdaptiveBUG.lean`, lines 147–157](../LeanDLRA/Tensor/TTN/RankAdaptiveBUG.lean#L147-L157):

```lean
theorem augBUG_global_error {τ : DimTree κ} (hv : τ.IsValid) {F : ℝ → Tensor ι → Tensor ι}
    {L B ε ϑ : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) (hε : 0 ≤ ε) (hϑ : 0 ≤ ϑ)
    {t₀ h : ℝ} (hh : 0 ≤ h) (hLh : 2 * L * h * τ.treeHeight ≤ 1) {N : ℕ}
    {A : ℝ → Tensor ι} (hA : ODESolution F A t₀ (t₀ + N * h)) {f : ℕ → BasisFrame ι τ}
    {Y : ℕ → Tensor ι}
    (hstep : ∀ n < N, (f n).IsAugBUGStep F ε ϑ (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (Y (n + 1)))
    {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) *
        (δ + T * (3 * τ.nodeCount * (ε + 6 * L * B * h)) + 3 * τ.nodeCount * (n * ϑ))
```

The same two bounds on tensors over a valid dimension tree `τ` (`hv`), for the steps
`DimTree.BasisFrame.IsBUGStep` and `DimTree.BasisFrame.IsAugBUGStep` with basis frames `f n` of
the tree. The number of nodes is `τ.nodeCount`, and the condition on the step size is
`2 * L * h * τ.treeHeight ≤ 1` (`hLh`). In the rank-adaptive step the truncation is the clause
`‖Y₁ - YS t₁‖ ≤ ϑ` of the step predicate; the core has no truncation of a tree tensor network
that is proved to satisfy it (section "TODO" of the two module docstrings).

`DimTree.BasisFrame.parBUG_global_error` in [`LeanDLRA/Tensor/TTN/ParallelBUG.lean`, lines 226–238](../LeanDLRA/Tensor/TTN/ParallelBUG.lean#L226-L238):

```lean
theorem parBUG_global_error {τ : DimTree κ} (hv : τ.IsValid) {F : ℝ → Tensor ι → Tensor ι}
    {L B Lt ε ϑ : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → ‖F t x - F s x‖ ≤ Lt * (t - s)) (hε : 0 ≤ ε) (hϑ : 0 ≤ ϑ)
    {t₀ h : ℝ} (hh : 0 ≤ h) (hLh : 2 * L * h * τ.treeHeight ≤ 1) {N : ℕ}
    {A : ℝ → Tensor ι} (hA : ODESolution F A t₀ (t₀ + N * h)) {f : ℕ → BasisFrame ι τ}
    {Y : ℕ → Tensor ι}
    (hstep : ∀ n < N, (f n).IsParBUGStep F ε ϑ (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (Y (n + 1)))
    {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) *
        (δ + T * (3 * τ.nodeCount * (2 * ε + (9 * L * B + Lt) * h)) +
          3 * τ.nodeCount * (n * ϑ))
```

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

## 9. Kinetic equations: vocabulary

For kinetic equations the core contains definitions, identities between them and the rank of
the low-rank ansatz, and no error theorem. The definitions are in
[`LeanDLRA/Kinetic/Defs.lean`](../LeanDLRA/Kinetic/Defs.lean), namespace `Kinetic`. A kinetic
density `f(x, v)` on a grid in phase space is a matrix with the space nodes as rows and the
velocity nodes as columns; on a continuous phase space it is a function of two variables.

`Kinetic.Quadrature` in [`LeanDLRA/Kinetic/Defs.lean`, lines 55–61](../LeanDLRA/Kinetic/Defs.lean#L55-L61):

```lean
structure Quadrature (V : Type*) [Fintype V] where
  /-- the nodes -/
  μ : V → ℝ
  /-- the weights -/
  w : V → ℝ
  w_pos : ∀ v, 0 < w v
  sum_w : ∑ v, w v = 1
```

`Kinetic.quadMoment` in [`LeanDLRA/Kinetic/Defs.lean`, line 121](../LeanDLRA/Kinetic/Defs.lean#L121):

```lean
def quadMoment (w ζ : V → ℝ) (f : Matrix X V ℝ) : X → ℝ := fun x => ∑ v, w v * ζ v * f x v
```

`Kinetic.density` in [`LeanDLRA/Kinetic/Defs.lean`, line 125](../LeanDLRA/Kinetic/Defs.lean#L125):

```lean
def density (w : V → ℝ) (f : Matrix X V ℝ) : X → ℝ := quadMoment w 1 f
```

`Kinetic.streaming` in [`LeanDLRA/Kinetic/Defs.lean`, lines 199–201](../LeanDLRA/Kinetic/Defs.lean#L199-L201):

```lean
noncomputable def streaming (D : κ → Matrix X X ℝ) (M : κ → Matrix V V ℝ) :
    Matrix X V ℝ →L[ℝ] Matrix X V ℝ :=
  ∑ k, Frobenius.sandwichCLM (D k) (M k)
```

`Kinetic.lowRankAnsatz` in [`LeanDLRA/Kinetic/Defs.lean`, lines 225–227](../LeanDLRA/Kinetic/Defs.lean#L225-L227):

```lean
def lowRankAnsatz (w : 𝒱 → ℝ) (X : ι → 𝒳 → ℝ) (S : Matrix ι κ ℝ) (V : κ → 𝒱 → ℝ) :
    𝒳 → 𝒱 → ℝ :=
  fun x v => w v * ∑ i, ∑ j, X i x * S i j * V j v
```

`Kinetic.maxwellian` in [`LeanDLRA/Kinetic/Defs.lean`, lines 396–397](../LeanDLRA/Kinetic/Defs.lean#L396-L397):

```lean
noncomputable def maxwellian (R ρ T : ℝ) (u v : EuclideanSpace ℝ ι) : ℝ :=
  ρ / (2 * Real.pi * R * T) ^ ((Fintype.card ι : ℝ) / 2) * Real.exp (-‖v - u‖ ^ 2 / (2 * R * T))
```

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

`Kinetic.fwdDiff_mul_apply` in [`LeanDLRA/Kinetic/Stencils.lean`, lines 112–113](../LeanDLRA/Kinetic/Stencils.lean#L112-L113):

```lean
theorem fwdDiff_mul_apply (u : Matrix (ZMod N) κ ℝ) (i : ZMod N) (k : κ) :
    (fwdDiff N h * u) i k = (u (i + 1) k - u i k) / h
```

`Kinetic.fwdDiff_transpose` in [`LeanDLRA/Kinetic/Stencils.lean`, line 64](../LeanDLRA/Kinetic/Stencils.lean#L64):

```lean
theorem fwdDiff_transpose : (fwdDiff N h)ᵀ = -bwdDiff N h
```

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

`Kinetic.hasSepRankLE_iff_exists_lowRankAnsatz` in [`LeanDLRA/Kinetic/LowRank.lean`, lines 55–57](../LeanDLRA/Kinetic/LowRank.lean#L55-L57):

```lean
theorem hasSepRankLE_iff_exists_lowRankAnsatz (f : 𝒳 → 𝒱 → ℝ) (r : ℕ) :
    HasSepRankLE ℝ f r ↔
      ∃ (X : Fin r → 𝒳 → ℝ) (V : Fin r → 𝒱 → ℝ), f = lowRankAnsatz 1 X 1 V
```

`Kinetic.rank_lowRankAnsatz_le` in [`LeanDLRA/Kinetic/LowRank.lean`, lines 63–65](../LeanDLRA/Kinetic/LowRank.lean#L63-L65):

```lean
theorem rank_lowRankAnsatz_le [Finite 𝒳] [Fintype 𝒱] (w : 𝒱 → ℝ) (X : ι → 𝒳 → ℝ)
    (S : Matrix ι κ ℝ) (V : κ → 𝒱 → ℝ) :
    (Matrix.of (lowRankAnsatz w X S V)).rank ≤ min (Fintype.card ι) (Fintype.card κ)
```

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

`projGradStep` in [`LeanDLRA/Training/Defs.lean`, line 45](../LeanDLRA/Training/Defs.lean#L45):

```lean
def projGradStep (P : E →L[ℝ] E) (g : E → E) (h : ℝ) (x : E) : E := x - h • P (g x)
```

`loss_projGradStep_le` in [`LeanDLRA/Training/Descent.lean`, lines 277–279](../LeanDLRA/Training/Descent.lean#L277-L279):

```lean
theorem loss_projGradStep_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hP : IsOrthProj P) (h : ℝ) (x : E) :
    ℒ (projGradStep P g h x) ≤ ℒ x - h * (1 - β * h / 2) * ‖P (g x)‖ ^ 2
```

The projected gradient step is `x - h P (g x)`. Let the loss `ℒ` have the gradient `g` (`hℒ`)
and let `g` be Lipschitz with constant `β` (`hg`). For every orthogonal projector `P` and every
`h` the loss after the step is at most `ℒ x - h (1 - β h / 2) ‖P (g x)‖²`. The only constant is
`β`.

Source: Kusch, Schotthöfer and Walter, arXiv 2502.03006, Theorem 5.8, and arXiv 2410.18720,
eqs. (22)–(25), as cited in the docstring.

`exists_projGrad_sq_le` in [`LeanDLRA/Training/Descent.lean`, lines 403–410](../LeanDLRA/Training/Descent.lean#L403-L410):

```lean
theorem exists_projGrad_sq_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {P : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k))
    {x : ℕ → E} {h ϑ G ℒinf : ℝ}
    (htr : ∀ k, ‖x (k + 1) - projGradStep (P k) g h (x k)‖ ≤ ϑ)
    (hG : ∀ k, ∀ w ∈ segment ℝ (projGradStep (P k) g h (x k)) (x (k + 1)), ‖g w‖ ≤ G)
    (hinf : ∀ k, ℒinf ≤ ℒ (x k)) (hh : 0 < h * (1 - β * h / 2)) {n : ℕ} (hn : 0 < n) :
    ∃ k < n, ‖P k (g (x k))‖ ^ 2 ≤
      (ℒ (x 0) - ℒinf) / (n * (h * (1 - β * h / 2))) + G * ϑ / (h * (1 - β * h / 2))
```

Existence of a value where the projected gradient is small. The hypotheses on `ℒ` and `g` are
those of the first theorem, and every `P k` is an orthogonal projector (`hP`). Let the values
`x k` be projected gradient steps followed by a change of norm at most `ϑ` (`htr`), let
`‖g‖ ≤ G` on the segment between the step and the changed value (`hG`), let `ℒinf` be a lower
bound of the loss along the sequence (`hinf`), let `h (1 - β h / 2) > 0` (`hh`) and `n > 0`
(`hn`). Then among the first `n` values there is one with

`‖P k (g (x k))‖² ≤ (ℒ (x 0) - ℒinf) / (n h (1 - β h / 2)) + G ϑ / (h (1 - β h / 2))`.

Source: Schotthöfer and Laiu, arXiv 2406.17887, Theorem 3 (for one client and one local step),
as cited in the docstring.

`loss_fedRound_le_one` in [`LeanDLRA/Training/FederatedDescent.lean`, lines 220–226](../LeanDLRA/Training/FederatedDescent.lean#L220-L226):

```lean
theorem loss_fedRound_le_one [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {sstar : ℕ} (hs : lr * β * sstar ≤ 1)
    (x : E) :
    ℒ (fedRound P gc g lr sstar x) ≤
      ℒ x - sstar * lr * (1 - sstar * lr * β) * ‖P (g x)‖ ^ 2
```

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

`FederatedThreshold.loss_fedRound_le_of_pow_le_three` in [`LeanDLRA/Research/FederatedDescentThreshold.lean`, lines 181–186](../LeanDLRA/Research/FederatedDescentThreshold.lean#L181-L186):

```lean
theorem loss_fedRound_le_of_pow_le_three [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {sstar : ℕ}
    (h3 : (1 + lr * β) ^ sstar ≤ 3) (x : E) :
    ℒ (fedRound P gc g lr sstar x) ≤ ℒ x
```

`FederatedThreshold.exists_fedRound_ascent` in [`LeanDLRA/Research/FederatedDescentThreshold.lean`, lines 268–273](../LeanDLRA/Research/FederatedDescentThreshold.lean#L268-L273):

```lean
theorem exists_fedRound_ascent {v : E} (hv : v ≠ 0) :
    ∃ (ℒ : E → ℝ) (g : E → E) (gc : Unit → E → E),
      (∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) ∧ (∀ x y, ‖g x - g y‖ ≤ 1 * ‖x - y‖) ∧
      (∀ c x y, ‖gc c x - gc c y‖ ≤ 1 * ‖x - y‖) ∧
      ∀ (lr : ℝ) (sstar : ℕ), 3 < (1 + lr * 1) ^ sstar →
        ℒ 0 < ℒ (fedRound (1 : E →L[ℝ] E) gc g lr sstar 0)
```

`FederatedThreshold.loss_fedRound_le_of_convex` in [`LeanDLRA/Research/FederatedDescentThreshold.lean`, lines 396–405](../LeanDLRA/Research/FederatedDescentThreshold.lean#L396-L405):

```lean
theorem loss_fedRound_le_of_convex [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hℒc : ∀ c x, HasFDerivAt (ℒc c) (innerSL ℝ (gc c x)) x)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hconv : ∀ c x y, ℒc c x + ⟪gc c x, y - x⟫ ≤ ℒc c y)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {sstar : ℕ} (hs0 : 0 < sstar)
    (hs : lr * β * (sstar + 1) ≤ 2) (x : E) :
    ℒ (fedRound P gc g lr sstar x) ≤
      ℒ x - lr / 2 * (2 - lr * β * (sstar + 1)) * ‖P (g x)‖ ^ 2
```

`FederatedThreshold.loss_le_loss_fedRound_linear` in [`LeanDLRA/Research/FederatedDescentThreshold.lean`, lines 570–578](../LeanDLRA/Research/FederatedDescentThreshold.lean#L570-L578):

```lean
theorem loss_le_loss_fedRound_linear [Fintype ι] (h : ι → ℝ) (hbar : ℝ) (v : E) (lr : ℝ)
    (sstar : ℕ)
    (hm0 : 0 ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ c, lr * ∑ i ∈ range sstar, (1 - lr * h c) ^ i)
    (hm : 2 ≤ hbar *
      ((Fintype.card ι : ℝ)⁻¹ * ∑ c, lr * ∑ i ∈ range sstar, (1 - lr * h c) ^ i)) :
    ⟪v, (0 : E)⟫ + hbar * (‖(0 : E)‖ ^ 2 / 2) ≤
      ⟪v, fedRound (1 : E →L[ℝ] E) (fun c z => h c • z + v) (fun y => v + hbar • y) lr sstar
        0⟫ + hbar * (‖fedRound (1 : E →L[ℝ] E) (fun c z => h c • z + v)
          (fun y => v + hbar • y) lr sstar 0‖ ^ 2 / 2)
```

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

`loss_fedRound_lt_of_convex_of_lr_mul_le_one` in [`LeanDLRA/Research/FederatedConvexThreshold.lean`, lines 255–263](../LeanDLRA/Research/FederatedConvexThreshold.lean#L255-L263):

```lean
theorem loss_fedRound_lt_of_convex_of_lr_mul_le_one [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hℒc : ∀ c x, HasFDerivAt (ℒc c) (innerSL ℝ (gc c x)) x)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hconv : ∀ c x y, ℒc c x + ⟪gc c x, y - x⟫ ≤ ℒc c y)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 < lr) (hlrβ : lr * β ≤ 1) {sstar : ℕ}
    (hs0 : 0 < sstar) (hs : lr * β * sstar < 2) {x : E} (hx : P (g x) ≠ 0) :
    ℒ (fedRound P gc g lr sstar x) < ℒ x
```

`loss_fedRound_two_lt` in [`LeanDLRA/Research/FederatedTwoSteps.lean`, lines 93–98](../LeanDLRA/Research/FederatedTwoSteps.lean#L93-L98):

```lean
theorem loss_fedRound_two_lt [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hP : IsOrthProj P)
    (hmean : ∀ y, g y = (Fintype.card ι : ℝ)⁻¹ • ∑ c, gc c y) (hlr : 0 < lr)
    (hlrβ : lr * β < 2) {x : E} (hx : P (g x) ≠ 0) :
    ℒ (fedRound P gc g lr 2 x) < ℒ x
```

`loss_fedRound_three_lt_of_convex` in [`LeanDLRA/Research/FederatedThreeSteps.lean`, lines 610–618](../LeanDLRA/Research/FederatedThreeSteps.lean#L610-L618):

```lean
theorem loss_fedRound_three_lt_of_convex [Fintype ι] [Nonempty ι]
    (hℒc : ∀ c x, HasFDerivAt (ℒc c) (innerSL ℝ (gc c x)) x)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hconv : ∀ c x y, ℒc c x + ⟪gc c x, y - x⟫ ≤ ℒc c y)
    (hP : IsOrthProj P) (hβ : 0 < β)
    (hℒmean : ∀ y, ℒ y = (Fintype.card ι : ℝ)⁻¹ * ∑ c, ℒc c y)
    (hmean : ∀ y, g y = (Fintype.card ι : ℝ)⁻¹ • ∑ c, gc c y) (hlr : 0 < lr)
    (hu : lr * β < 15 / 8) {x : E} (hx : P (g x) ≠ 0) :
    ℒ (fedRound P gc g lr 3 x) < ℒ x
```

`loss_le_loss_fedRound_three_quadratic` in [`LeanDLRA/Research/FederatedThreeSteps.lean`, lines 646–653](../LeanDLRA/Research/FederatedThreeSteps.lean#L646-L653):

```lean
theorem loss_le_loss_fedRound_three_quadratic (v : E) :
    ⟪v, (0 : E)⟫ + 16 / 45 * ‖(0 : E)‖ ^ 2 ≤
      ⟪v, fedRound (1 : E →L[ℝ] E)
          (Sum.elim (fun _ : Fin 32 => fun z => v + z) (fun _ : Fin 13 => fun _ => v))
          (fun y => v + (32 / 45 : ℝ) • y) (15 / 8) 3 0⟫
        + 16 / 45 * ‖fedRound (1 : E →L[ℝ] E)
          (Sum.elim (fun _ : Fin 32 => fun z => v + z) (fun _ : Fin 13 => fun _ => v))
          (fun y => v + (32 / 45 : ℝ) • y) (15 / 8) 3 0‖ ^ 2
```

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

`loss_fedRound_lt_of_convex_of_mul_lt_four` in [`LeanDLRA/Research/FederatedManySteps.lean`, lines 397–405](../LeanDLRA/Research/FederatedManySteps.lean#L397-L405):

```lean
theorem loss_fedRound_lt_of_convex_of_mul_lt_four [Fintype ι] [Nonempty ι]
    (hℒc : ∀ c x, HasFDerivAt (ℒc c) (innerSL ℝ (gc c x)) x)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hconv : ∀ c x y, ℒc c x + ⟪gc c x, y - x⟫ ≤ ℒc c y)
    (hP : IsOrthProj P) (hβ : 0 < β)
    (hℒmean : ∀ y, ℒ y = (Fintype.card ι : ℝ)⁻¹ * ∑ c, ℒc c y)
    (hmean : ∀ y, g y = (Fintype.card ι : ℝ)⁻¹ • ∑ c, gc c y) (hlr : 0 < lr) {sstar : ℕ}
    (hs2 : 2 ≤ sstar) (hs : lr * β * sstar < 4) {x : E} (hx : P (g x) ≠ 0) :
    ℒ (fedRound P gc g lr sstar x) < ℒ x
```

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

`loss_sub_le_exp_of_projGradFlow_PL` in [`LeanDLRA/Training/ConvergenceRates.lean`, lines 64–69](../LeanDLRA/Training/ConvergenceRates.lean#L64-L69):

```lean
theorem loss_sub_le_exp_of_projGradFlow_PL (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    {P : ℝ → E →L[ℝ] E} (hP : ∀ t, IsOrthProj (P t)) {y : ℝ → E} {a b : ℝ}
    (hyc : ContinuousOn y (Icc a b))
    (hy : ∀ t ∈ Ico a b, HasDerivWithinAt y (-P t (g (y t))) (Ici t) t) {μ ℒstar : ℝ}
    (hPL : ∀ t ∈ Ico a b, 2 * μ * (ℒ (y t) - ℒstar) ≤ ‖P t (g (y t))‖ ^ 2) :
    ∀ t ∈ Icc a b, ℒ (y t) - ℒstar ≤ Real.exp (-(2 * μ) * (t - a)) * (ℒ (y a) - ℒstar)
```

`exists_fedAvgRound_fixed_ne_stationary` in [`LeanDLRA/Training/FederatedFixedPoints.lean`, lines 130–133](../LeanDLRA/Training/FederatedFixedPoints.lean#L130-L133):

```lean
theorem exists_fedAvgRound_fixed_ne_stationary {sstar : ℕ} (hs : 2 ≤ sstar) :
    ∃ (gc : Fin 2 → ℝ → ℝ) (lr β x : ℝ), 0 < lr ∧ lr * β < 1 ∧
      (∀ c y z, ‖gc c y - gc c z‖ ≤ β * ‖y - z‖) ∧
      fedAvgRound (1 : ℝ →L[ℝ] ℝ) gc lr sstar x = x ∧ ∑ c, gc c x ≠ 0
```

`loss_kslEulerStep_le_of_smooth_quarter` in [`LeanDLRA/Training/ProjectorSplittingDescent.lean`, lines 233–237](../LeanDLRA/Training/ProjectorSplittingDescent.lean#L233-L237):

```lean
theorem loss_kslEulerStep_le_of_smooth_quarter (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (hβ : 0 ≤ β) (hh : 0 ≤ h) (hβh : β * h ≤ 1 / 4) {x : E}
    (hcap : P₁ (x - h • Q₀ (g x)) = x - h • Q₀ (g x)) :
    ℒ (kslEulerStep P₁ Q₀ (fun y => -g y) h x) ≤ ℒ x - h / 8 * ‖tangent P₁ Q₀ (g x)‖ ^ 2
```

`loss_kslEulerStep_gt_of_goldenRatio_lt` in [`LeanDLRA/Training/ProjectorSplittingDescent.lean`, lines 396–399](../LeanDLRA/Training/ProjectorSplittingDescent.lean#L396-L399):

```lean
theorem loss_kslEulerStep_gt_of_goldenRatio_lt {x : E} (hx0 : x ≠ 0) (h₁ : P₁ x = x)
    (h₀ : Q₀ x = x) (hφ : Real.goldenRatio < h) :
    1 / 2 * ‖x‖ ^ 2 < 1 / 2 * ‖kslEulerStep P₁ Q₀ (fun y => -(y - 0)) h x‖ ^ 2 ∧
      (h < 2 → 1 / 2 * ‖x - h • (x - 0)‖ ^ 2 < 1 / 2 * ‖x‖ ^ 2)
```

Four statements from three files, all for a loss `ℒ` with gradient `g`.

[`Training/ConvergenceRates.lean`](../LeanDLRA/Training/ConvergenceRates.lean): along the projected gradient flow
`y' = -Π(t) g(y)` with orthogonal projectors `Π(t)`, the condition
`2 μ (ℒ(y) - ℒ⋆) ≤ ‖Π g(y)‖²` (of Polyak–Łojasiewicz type) gives the exponential decay
`ℒ(y t) - ℒ⋆ ≤ e^{-2 μ (t - a)} (ℒ(y a) - ℒ⋆)`. The file has further statements of this kind for
truncated steps with an augmented projector (`loss_sub_le_pow_of_riemannianPL_truncated`), for a
projector that is refreshed every `T` steps (`exists_grad_sq_le_of_lazyRefresh`), for random
projectors (`sum_loss_projGradStep_le_of_isotropic`) and for the federated round without variance
correction (`loss_fedAvgRound_le`, which has a term in the spread `ζ` of the client gradients that
the round with variance correction does not have).

[`Training/FederatedFixedPoints.lean`](../LeanDLRA/Training/FederatedFixedPoints.lean): for the round with variance correction a fixed
point is stationary for the projected gradient (`apply_grad_eq_zero_of_fedRound_eq_self`, under
`e · lr β sstar < 1`). The quoted theorem shows that the round without the correction can have a
fixed point where the sum of the client gradients does not vanish, for every number `sstar ≥ 2` of
local steps (client drift); the statement is about two quadratic clients on `ℝ`.

[`Training/ProjectorSplittingDescent.lean`](../LeanDLRA/Training/ProjectorSplittingDescent.lean): the projector-splitting integrator with
one explicit Euler step per substep, applied to the gradient flow (`kslEulerStep` of
[`Stability/Energy.lean`](../LeanDLRA/Stability/Energy.lean)), with exact gradients and a new basis that captures the
K-step. If the gradient is `β`-Lipschitz and `β h ≤ 1/4`, the loss decreases by at least
`(h / 8) ‖T₁ g(x)‖²`, where `T₁` is the tangent projector of the step; the constants do not depend
on the state. For the quadratic loss the step decreases the loss for `0 ≤ h ≤ φ`, the golden
ratio (`loss_kslEulerStep_quadratic_le`), and the last theorem shows that this cannot be relaxed:
for every `h > φ` there is a state for which the loss increases, while the gradient step
decreases it for `h < 2`. Stochastic gradients, truncation of the rank and the loss of rank
during training are not treated (module docstring).

Source: the module docstrings cite arXiv 2307.05695, 2403.03507, 2401.03748 and 2406.17887 (the
training methods) and arXiv 2502.03006, Sections 3.2, 3.3 and 5 (the splitting step).

`GradientFlowConvergence.projectedGradient_global_error` in [`LeanDLRA/Training/GradientFlowConvergence.lean`, lines 238–249](../LeanDLRA/Training/GradientFlowConvergence.lean#L238-L249):

```lean
theorem projectedGradient_global_error {G : E → E} {β B ε σ ϑ lr t₀ : ℝ}
    (hG : ∀ x y, ‖G x - G y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hB : ∀ x, ‖G x‖ ≤ B) (hlr : 0 ≤ lr)
    (hε0 : 0 ≤ ε) (hσ0 : 0 ≤ σ)
    {N : ℕ} {A : ℝ → E} (hA : ODESolution (fun _ x => -G x) A t₀ (t₀ + N * lr))
    {W g : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ n < N, ODESolution (fun _ x => -G x) (Φ n) (t₀ + n * lr) (t₀ + (n + 1) * lr))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * lr) = W n) {Pr : ℕ → E →L[ℝ] E}
    (hPr : ∀ n, IsOrthProj (Pr n)) (hε : ∀ n < N, ‖(1 - Pr n) (G (W n))‖ ≤ ε)
    (hσ : ∀ n < N, ‖g n - G (W n)‖ ≤ σ)
    (hstep : ∀ n < N, ‖W (n + 1) - (W n - lr • Pr n (g n))‖ ≤ ϑ) {T : ℝ} :
    ∀ n ≤ N, (n : ℝ) * lr ≤ T → ‖W n - A (t₀ + n * lr)‖ ≤
      Real.exp (β * T) * (‖W 0 - A t₀‖ + T * (β * B * lr / 2 + ε + σ) + n * ϑ)
```

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

`KalmanBucy.riccatiField` in [`LeanDLRA/Filtering/Defs.lean`, lines 93–95](../LeanDLRA/Filtering/Defs.lean#L93-L95):

```lean
def riccatiField (A : Matrix (Fin d) (Fin d) ℝ) (ρ : ℝ) (Qn : Matrix (Fin d) (Fin d) ℝ) :
    ℝ → Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ :=
  fun _ P => A * P + P * Aᵀ - ρ • (P * P) + Qn
```

`KalmanBucy.dlrKalmanBucy_covariance_error_uniform` in [`LeanDLRA/Stochastic/KalmanBucy.lean`, lines 227–234](../LeanDLRA/Stochastic/KalmanBucy.lean#L227-L234):

```lean
theorem dlrKalmanBucy_covariance_error_uniform {A Qn : Matrix (Fin d) (Fin d) ℝ} {ρ μ η a b : ℝ}
    (hA : ∀ x : Fin d → ℝ, x ⬝ᵥ ((A + Aᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (hμ : μ < 0) (hρ : 0 ≤ ρ)
    {PU : ℝ → Matrix (Fin d) (Fin d) ℝ} {P PD : ℝ → Matrix (Fin d) (Fin d) ℝ}
    (hP : ODESolution (riccatiField A ρ Qn) P a b)
    (hPD : ODESolution (fun t X => riccatiField A ρ (PU t * Qn * PU t) t X) PD a b)
    (hpsd : ∀ t ∈ Icc a b, (P t).PosSemidef ∧ (PD t).PosSemidef) (hη0 : 0 ≤ η)
    (hη : ∀ t ∈ Ico a b, ‖Qn - PU t * Qn * PU t‖ ≤ η) :
    ∀ t ∈ Icc a b, ‖PD t - P t‖ ≤ Real.exp (μ * (t - a)) * ‖PD a - P a‖ + η / (-μ)
```

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

`KalmanBucy.analysisCov` in [`LeanDLRA/Filtering/Defs.lean`, lines 67–69](../LeanDLRA/Filtering/Defs.lean#L67-L69):

```lean
noncomputable def analysisCov (C : Matrix (Fin p) (Fin d) ℝ) (R : Matrix (Fin p) (Fin p) ℝ)
    (Pi : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Pi - Pi * Cᵀ * (innovCov C R Pi)⁻¹ * C * Pi
```

`KalmanBucy.analysisCov_mono` in [`LeanDLRA/Stochastic/KalmanBucy.lean`, lines 495–497](../LeanDLRA/Stochastic/KalmanBucy.lean#L495-L497):

```lean
theorem analysisCov_mono {C : Matrix (Fin p) (Fin d) ℝ} {R : Matrix (Fin p) (Fin p) ℝ}
    {Pi Pir : Matrix (Fin d) (Fin d) ℝ} (hr : Pir.PosSemidef) (h : (Pi - Pir).PosSemidef)
    (hR : R.PosDef) : (analysisCov C R Pi - analysisCov C R Pir).PosSemidef
```

`KalmanBucy.analysisCov C R Pi` is the analysis (posterior) covariance
`Pi - Pi Cᵀ S⁻¹ C Pi` of a Kalman analysis step with `S = C Pi Cᵀ + R`, for a prior covariance
`Pi` and the covariance `R` of the observation noise. If the prior `Pir` is positive
semidefinite and below `Pi` in the Loewner order (`h`), and `R` is positive definite, the
analysis covariance of `Pir` is below that of `Pi`. No constants.

Source: the docstring names arXiv 2306.07774, Section 5, and arXiv 2602.06614, Section 3.1.2.

### 10.3 Control

`AdjointDLRA.abs_reducedGrad_sub_le` in [`LeanDLRA/Control/AdjointDLRA.lean`, lines 70–74](../LeanDLRA/Control/AdjointDLRA.lean#L70-L74):

```lean
theorem abs_reducedGrad_sub_le (N : ℕ) (B : E →L[ℝ] E) (f fr gg gr : ℕ → E) :
    |(∑ k ∈ range (N + 1), ⟪B (f k), gg k⟫) / (N + 1) -
        (∑ k ∈ range (N + 1), ⟪B (fr k), gr k⟫) / (N + 1)| ≤
      (∑ k ∈ range (N + 1), (‖f k - fr k‖ * ‖gr k‖ + ‖f k‖ * ‖gg k - gr k‖)) * ‖B‖ /
        (N + 1)
```

The reduced gradient of a control problem in the form `(1/(N+1)) ∑ ⟪B (f k), g k⟫` with state
values `f k` and adjoint values `g k` (in the statement: `gg k`), compared with the same
expression for approximations `fr k`, `gr k`. The difference is bounded by the sum of
`‖f k - fr k‖ ‖gr k‖ + ‖f k‖ ‖gg k - gr k‖`, times `‖B‖ / (N + 1)`. There are no hypotheses: the
statement is an inequality for arbitrary sequences, and that the gradient has this form is not
part of it.

`AdjointDLRA.IsKSLStep.reverse_eq` in [`LeanDLRA/Control/AdjointDLRA.lean`, lines 299–306](../LeanDLRA/Control/AdjointDLRA.lean#L299-L306):

```lean
theorem IsKSLStep.reverse_eq {F : ℝ → E → E} {ε L : ℝ} {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E}
    {YK YS YL : ℝ → E} (hs : IsKSLStep F ε P₁ Q₀ t₀ t₁ Y₀ YK YS YL) (h01 : t₀ ≤ t₁)
    (hF : IsLipschitzField F L) (hFc : Continuous (Function.uncurry F)) {ZL ZS ZK : ℝ → E}
    (hZL : ODESolution (fun s x => -P₁ (F (t₀ + t₁ - s) x)) ZL t₀ t₁) (hZL₀ : ZL t₀ = YL t₁)
    (hZS : ODESolution (fun s x => P₁ (Q₀ (F (t₀ + t₁ - s) x))) ZS t₀ t₁)
    (hZS₀ : ZS t₀ = ZL t₁)
    (hZK : ODESolution (fun s x => -Q₀ (F (t₀ + t₁ - s) x)) ZK t₀ t₁) (hZK₀ : ZK t₀ = ZS t₁) :
    ZK t₁ = Y₀
```

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
[`FixedRank/TangentStepTruncation.lean`](../LeanDLRA/FixedRank/TangentStepTruncation.lean) in section 2.4,
[`Matrix/LowRankDistanceFlow.lean`](../LeanDLRA/Matrix/LowRankDistanceFlow.lean) in section 6.8,
[`Integrators/RankSelection.lean`](../LeanDLRA/Integrators/RankSelection.lean) and
[`Integrators/RankAdaptiveBUGAposteriori.lean`](../LeanDLRA/Integrators/RankAdaptiveBUGAposteriori.lean) in section 6.3,
[`Training/ConvergenceRates.lean`](../LeanDLRA/Training/ConvergenceRates.lean), [`Training/FederatedFixedPoints.lean`](../LeanDLRA/Training/FederatedFixedPoints.lean)
and [`Training/ProjectorSplittingDescent.lean`](../LeanDLRA/Training/ProjectorSplittingDescent.lean) in section 10.1.

### 11.1 Norm balance of one step

`IsBUGStep.norm_sq_add_defect_sq_and_defect_le` in [`LeanDLRA/Stability/NormBalance.lean`, lines 61–66](../LeanDLRA/Stability/NormBalance.lean#L61-L66):

```lean
theorem IsBUGStep.norm_sq_add_defect_sq_and_defect_le {F : ℝ → E → E} {ε B : ℝ}
    {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E} {YK YL YS : ℝ → E}
    (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS) (h01 : t₀ ≤ t₁)
    (hB : IsBoundedField F B) (hF : ∀ t x, ⟪F t x, x⟫ = 0) :
    ‖YS t₁‖ ^ 2 + ‖Y₀ - P₁ (Q₁ Y₀)‖ ^ 2 = ‖Y₀‖ ^ 2 ∧
      ‖Y₀ - P₁ (Q₁ Y₀)‖ ≤ 2 * B * (t₁ - t₀)
```

`IsKSLStep.norm_eq` in [`LeanDLRA/Stability/NormBalance.lean`, lines 125–128](../LeanDLRA/Stability/NormBalance.lean#L125-L128):

```lean
theorem IsKSLStep.norm_eq {F : ℝ → E → E} {ε : ℝ} {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E}
    {YK YS YL : ℝ → E} (hs : IsKSLStep F ε P₁ Q₀ t₀ t₁ Y₀ YK YS YL) (h01 : t₀ ≤ t₁)
    (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (hY₀ : Q₀ Y₀ = Y₀) (hF : ∀ t x, ⟪F t x, x⟫ = 0) :
    ‖YL t₁‖ = ‖Y₀‖
```

For a field with `⟪F t x, x⟫ = 0` the exact flow conserves the norm. The fixed-rank BUG step
loses exactly the projection defect of its start value: `‖YS t₁‖² + ‖Y₀ - P₁ (Q₁ Y₀)‖² = ‖Y₀‖²`,
and the defect is at most `2 B (t₁ - t₀)` for a field bounded by `B`. The projector-splitting
(KSL) step conserves the norm exactly if the projectors commute and `Q₀ Y₀ = Y₀`; the file also
has the energy `ℰ` for `F(t, x) = J ∇ℰ(x)` with skew `J` (`IsKSLStep.energy_eq_of_skew`) and
the statement that the untruncated parallel BUG step can only gain norm
(`IsParallelBUGStep.norm_sq_eq`). The theorems are for one step and for the step structures of
the core; they are not a statement on the whole run.

### 11.2 Gauge, interpolation, mixtures, Gramians, orthonormality

`Literature.P2503_18271.tdb_velocity_gauge_free` in [`LeanDLRA/DLRA/GaugeInvariance.lean`, lines 105–112](../LeanDLRA/DLRA/GaugeInvariance.lean#L105-L112):

```lean
theorem tdb_velocity_gauge_free [DecidableEq n] [DecidableEq nc] [DecidableEq r]
    (U : Matrix n r ℝ) (Sg : Matrix r r ℝ) (Y : Matrix nc r ℝ) (M : Matrix n nc ℝ)
    (hSg : Sg.det ≠ 0)
    (U' : Matrix n r ℝ) (Sg' : Matrix r r ℝ) (Y' : Matrix nc r ℝ) (A B : Matrix r r ℝ)
    (hU' : U' = (1 - U * Uᵀ) * (M * Y * Sg⁻¹) + U * A)
    (hY' : Y' = (1 - Y * Yᵀ) * (Mᵀ * U * (Sg⁻¹)ᵀ) + Y * B)
    (hSg' : Sg' = Uᵀ * M * Y + Sg * B - A * Sg) (hB : Bᵀ = -B) :
    U' * Sg * Yᵀ + U * Sg' * Yᵀ + U * Sg * Y'ᵀ = tangentProj U Y M
```

`Literature.P2402_18721.obliqueTangentProj_eq_of_mem_range` in [`LeanDLRA/Randomized/CrossInterpolation.lean`, lines 67–73](../LeanDLRA/Randomized/CrossInterpolation.lean#L67-L73):

```lean
theorem obliqueTangentProj_eq_of_mem_range (U SU : Matrix m k ℝ) (V SV : Matrix n l ℝ)
    (I : k → m) (J : l → n)
    (hI : ∀ i a, SU i a = if i = I a then 1 else 0)
    (hJ : ∀ j b, SV j b = if j = J b then 1 else 0)
    (hSU : IsUnit (SUᵀ * U).det) (hSV : IsUnit (SVᵀ * V).det) (Z : Matrix m n ℝ)
    (i : m) (j : n) (h : i ∈ Set.range I ∨ j ∈ Set.range J) :
    LeanDLRA.obliqueTangentProj U SU V SV Z i j = Z i j
```

`Literature.P2508_04484.material_mixture_isLipschitz` in [`LeanDLRA/Kinetic/MaterialMixtureCollision.lean`, lines 65–67](../LeanDLRA/Kinetic/MaterialMixtureCollision.lean#L65-L67):

```lean
theorem material_mixture_isLipschitz (D : ℝ → ι → Matrix ρ ρ ℝ) (C : ℝ → ι → Matrix κ κ ℝ)
    (B : ℝ → Matrix ρ κ ℝ) {L : ℝ} (hL : ∀ t, ∑ i, ‖D t i‖ * ‖C t i‖ ≤ L) :
    IsLipschitzField (fun t u => (∑ i, D t i * u * C t i) + B t) L
```

`Literature.P2601_21428.projected_step_gram_lower_bound` in [`LeanDLRA/Stochastic/GramianLowerBound.lean`, lines 113–126](../LeanDLRA/Stochastic/GramianLowerBound.lean#L113-L126):

```lean
theorem projected_step_gram_lower_bound
    {U : Matrix (Fin k) (Fin d) ℝ} (hU : U * Uᵀ = 1)
    {Yp ζ Yt : PiLp 2 fun _ : Fin k => H} (hsplit : ∀ i, Yt i = Yp i + ζ i)
    (horth : ∀ i j, ⟪Yp i, ζ j⟫ = 0)
    {B : Matrix (Fin d) (Fin d) ℝ} {σ Δt : ℝ} (hσ : 0 < σ) (hΔt : 0 < Δt)
    (hB : ∀ w : Fin d → ℝ, σ * (w ⬝ᵥ w) ≤ w ⬝ᵥ (B *ᵥ w))
    (hiso : LeanDLRA.gramMatrix ζ = Δt • (U * B * Uᵀ))
    {G Ut : Matrix (Fin k) (Fin d) ℝ}
    (hUt : LeanDLRA.gramMatrix Yt * Ut = LeanDLRA.gramMatrix Yt * U + G * (1 - Uᵀ * U))
    {Q : Matrix (Fin d) (Fin k) ℝ} {R : Matrix (Fin k) (Fin k) ℝ}
    (hQR : Utᵀ = Q * R) (hQ : Qᵀ * Q = 1)
    {Ynext : PiLp 2 fun _ : Fin k => H} (hY : ∀ i, Ynext i = ∑ j, R i j • Yt j) :
    (∀ r : Fin d, ∑ i, Q r i • Ynext i = ∑ j, Utᵀ r j • Yt j) ∧
      ∀ v : Fin k → ℝ, σ * Δt * (v ⬝ᵥ v) ≤ v ⬝ᵥ (LeanDLRA.gramMatrix Ynext *ᵥ v)
```

`Literature.P2002_11392.basis_transpose_mul_self_iff` in [`LeanDLRA/Tensor/TTN/BasisOrthonormality.lean`, lines 70–73](../LeanDLRA/Tensor/TTN/BasisOrthonormality.lean#L70-L73):

```lean
theorem basis_transpose_mul_self_iff {m : ℕ} {cs : Fin m → DimTree κ}
    (hv : (DimTree.node cs).IsValid) {rs : Fin m → ℕ} {r : ℕ} (ds : ∀ i, TTN ι (cs i) (rs i))
    (C : Matrix (Fin r) (∀ i, Fin (rs i)) ℝ) (hds : ∀ i, ((ds i).basis)ᵀ * (ds i).basis = 1) :
    ((TTN.node ds C).basis)ᵀ * (TTN.node ds C).basis = 1 ↔ C * Cᵀ = 1
```

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
