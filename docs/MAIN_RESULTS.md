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
files and were compared with them at commit 64d393b (2026-11-17). A theorem is quoted from its
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
11. [Citation keys](#11-citation-keys)

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

### 2.4 Curvature: the tangent projector depends on the point with constant 2/ρ

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

`dlra_norm_sub_truncation_le_integral` in [`LeanDLRA/DLRA/QuasiOptimality.lean`, lines 513–524](../LeanDLRA/DLRA/QuasiOptimality.lean#L513-L524):

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
`[0, T]` in the factored form is a hypothesis.

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
| BUG for Tucker tensors, fixed multilinear rank | `TuckerBUG.isTubeLocal_stepRel` | `d + 2` | `TuckerBUG.exists_run_norm_sub_le` | 8.2 |

In the first five rows and in the rows for the dynamical randomized SVD and the projected
methods the admissible values are the matrices of rank at most `r`; for the integrators with a
truncation tolerance every matrix is admissible (the set of the numbers of columns of a start
factorization is `Set.Ici r₀`); for the Tucker integrator they are the tensors of multilinear
rank at most `r`. The hypotheses on `F` and `A` are the same in all rows, in the same order: a
`DLRAProblem` on the tube, joint continuity of `F` there, and a bound `ε` on the normal part of
`F` at the factored points of the tube. The theorems of sections 6.4 and 6.8 have more, on the
dependence of the field on time; the theorem for the projected Runge–Kutta methods has
hypotheses on the order of the classical scheme (section 6.8). The run theorem asks for a
margin constant of at least 2 (`hκ`). For the integrators whose constant is smaller (sections
6.4 and 6.8, constant 0 or `(1 + κ) α + 1`), it is used with a larger constant
(`StepMethod.IsTubeLocal.mono`). The integrators with a truncation tolerance are instances of
the form of the theorem with a tolerance for every step, the second theorem below
(`StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_tol`), because the local error of a step is
`h c + ϑ`.

The integrators of sections 6 to 8 that are not rows of the table (midpoint BUG, implicit BUG,
the integrators for tree tensor networks) and the tensor theorems `tucker_global_error_le`,
`tucker_global_error_le_of_tube` have error theorems of an older form, in which the field
satisfies global assumptions or the steps and the exact solutions through the numerical values
are hypotheses.

**To get an error bound for a method** that is a row of the table, apply its run theorem; the
guide ([GUIDE.md](GUIDE.md), sections 1 and 2) lists the steps. A method that is not a row has to
be shown to be tube-local first: existence of a step from every admissible value, invariance of
the admissible set, and locality (the three fields of `StepMethod.IsTubeLocal`).

Two more forms of the run theorem are in files of their own.

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

`MatrixBUG.exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Matrix/BUGRun.lean`, lines 279–288](../LeanDLRA/Integrators/Matrix/BUGRun.lean#L279-L288):

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

`MatrixBUG.isTubeLocal_stepRel` in [`LeanDLRA/Integrators/Matrix/BUGRun.lean`, lines 248–250](../LeanDLRA/Integrators/Matrix/BUGRun.lean#L248-L250):

```lean
theorem isTubeLocal_stepRel (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) :
    StepMethod.IsTubeLocal (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => stepRel G r)
      (fun Y => Y.rank ≤ r) 4
```

The admissible values are the matrices of rank at most `r` and the margin constant is 4.

`MatrixBUG.IsRun.norm_sub_le` in [`LeanDLRA/Integrators/Matrix/BUGRun.lean`, lines 189–196](../LeanDLRA/Integrators/Matrix/BUGRun.lean#L189-L196):

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

`exists_bugGlobalBound_lt` in [`LeanDLRA/Integrators/Matrix/BUGRun.lean`, lines 314–316](../LeanDLRA/Integrators/Matrix/BUGRun.lean#L314-L316):

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

`MatrixKSL.isTubeLocal_stepRel` in [`LeanDLRA/Integrators/Matrix/KSLRun.lean`, lines 270–272](../LeanDLRA/Integrators/Matrix/KSLRun.lean#L270-L272):

```lean
theorem isTubeLocal_stepRel (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) :
    StepMethod.IsTubeLocal (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => stepRel G r)
      (fun Y => Y.rank ≤ r) 4
```

`MatrixKSL.exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Matrix/KSLRun.lean`, lines 302–312](../LeanDLRA/Integrators/Matrix/KSLRun.lean#L302-L312):

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

`MatrixParallelBUG.isTubeLocal_stepRel` in [`LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean`, lines 288–290](../LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean#L288-L290):

```lean
theorem isTubeLocal_stepRel (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) :
    StepMethod.IsTubeLocal (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => stepRel G r)
      (fun Y => Y.rank ≤ r) 2
```

`MatrixParallelBUG.exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean`, lines 322–333](../LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean#L322-L333):

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

`MatrixParallelBUG.adaptiveStepRel` in [`LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean`, lines 114–116](../LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean#L114-L116):

```lean
def adaptiveStepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (R : Set ℕ) (ϑ : ℝ) :
    StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ => ∃ r ∈ R, ∃ Yh : Matrix m n ℝ, augmentedRel F r t₀ t₁ Y₀ Yh ∧ ‖Y₁ - Yh‖ ≤ ϑ
```

`MatrixParallelBUG.isTubeLocal_adaptiveStepRel_Ici` in [`LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean`, lines 263–267](../LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean#L263-L267):

```lean
theorem isTubeLocal_adaptiveStepRel_Ici (hϑ : 0 ≤ ϑ) (hrm : r₀ ≤ Fintype.card m)
    (hrn : r₀ ≤ Fintype.card n) :
    StepMethod.IsTubeLocal
      (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => adaptiveStepRel G (Set.Ici r₀) ϑ)
      (fun _ => True) 2
```

`MatrixParallelBUG.adaptive_exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean`, lines 427–439](../LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean#L427-L439):

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

A lower bound for one step. There are a field `F` on `3 × 2` matrices that does not depend on
time and whose normal component vanishes at every point `U S Vᵀ` with one column in `U` and `V`
(`FactoredNormalBoundOn` with `ε = 0` on the whole space), a start `U₀ V₀ᵀ` of rank one with
orthonormal factors, and a solution `A` of the differential equation from this start, such that
every rank-adaptive step of size `h > 0` from the start whose augmented left basis `Ua` has two
columns has error at least `h² / 2 - ϑ`, where `ϑ` is the truncation tolerance of the step; and
such a step with tolerance zero exists for every `h`. The field of the example is a polynomial
of degree two and is not globally Lipschitz (module docstring of the file). The same file has an
upper bound for a Galerkin step whose space contains a point close to the exact solution
(`AugmentationRank.galerkin_error_of_predictor`) and an upper bound for fields of the form
`𝒜(t) Y + Y ℬ(t)` (`AugmentationRank.error_le_of_sylvester`); they are not quoted here. The
theorem cites no theorem of a paper.

`MatrixBUG.truncStepRel` in [`LeanDLRA/Integrators/Matrix/AdaptiveBUGStep.lean`, lines 365–368](../LeanDLRA/Integrators/Matrix/AdaptiveBUGStep.lean#L365-L368):

```lean
def truncStepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) (κ : ℝ) :
    StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ => ∃ Yh : Matrix m n ℝ, augmentedRel F r t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧
    ‖Y₁ - Yh‖ ≤ κ * distLR r Yh
```

`MatrixBUG.trunc_exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Matrix/TruncBUGRun.lean`, lines 238–250](../LeanDLRA/Integrators/Matrix/TruncBUGRun.lean#L238-L250):

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

`MatrixBUG.isTubeLocal_adaptiveStepRel_Ici` in [`LeanDLRA/Integrators/Matrix/AdaptiveBUGRun.lean`, lines 125–129](../LeanDLRA/Integrators/Matrix/AdaptiveBUGRun.lean#L125-L129):

```lean
theorem isTubeLocal_adaptiveStepRel_Ici (hϑ : 0 ≤ ϑ) (hrm : r₀ ≤ Fintype.card m)
    (hrn : r₀ ≤ Fintype.card n) :
    StepMethod.IsTubeLocal
      (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => adaptiveStepRel G (Set.Ici r₀) ϑ)
      (fun _ => True) 4
```

`MatrixBUG.adaptive_exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Matrix/AdaptiveBUGRun.lean`, lines 235–246](../LeanDLRA/Integrators/Matrix/AdaptiveBUGRun.lean#L235-L246):

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

`MatrixEulerBUG.exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Matrix/EulerBUGRun.lean`, lines 342–356](../LeanDLRA/Integrators/Matrix/EulerBUGRun.lean#L342-L356):

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
are hypotheses (`hθ`, `hθ'`) of every statement of that file: the bases are given. The size of
`θ` is bounded in a second file, at the end of this section.

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
the factors `√r`. The module docstring summarizes the bound as `C₁ h² + C₂ ε`; the theorem
states it with the free parameter `τ`, and the page does not derive `C₁` and `C₂` from it. The
second theorem is the same bound for `θ'`, by transposition. The file has `example`s for the
hypotheses of both. Together with `norm_update_sub_le`, the local error of the explicit update
is therefore bounded by terms in `ε`, `h` and `‖S₀‖`; no global error of the update is stated.

The module docstring cites no paper for the capture defect.

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

`MatrixDRSVD.isTubeLocal_stepRel` in [`LeanDLRA/Randomized/DRSVDRun.lean`, lines 166–169](../LeanDLRA/Randomized/DRSVDRun.lean#L166-L169):

```lean
theorem isTubeLocal_stepRel (hrk : r ≤ k) (hkn : k ≤ Fintype.card n) (hkl : k ≤ l)
    (hlm : l ≤ Fintype.card m) :
    StepMethod.IsTubeLocal (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => stepRel G r k l)
      (fun Y => Y.rank ≤ r) 3
```

`MatrixDRSVD.exists_run_norm_sub_le` in [`LeanDLRA/Randomized/DRSVDRun.lean`, lines 277–288](../LeanDLRA/Randomized/DRSVDRun.lean#L277-L288):

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

`distLR_flow_le_exp_of_tube` in [`LeanDLRA/Integrators/Matrix/FlowDistance.lean`, lines 142–149](../LeanDLRA/Integrators/Matrix/FlowDistance.lean#L142-L149):

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

`MatrixProjEuler.stepRel` in [`LeanDLRA/Integrators/Matrix/ProjectedEuler.lean`, lines 113–115](../LeanDLRA/Integrators/Matrix/ProjectedEuler.lean#L113-L115):

```lean
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) (κ : ℝ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ => ∃ X : Matrix m n ℝ, tangentRel F r t₀ t₁ Y₀ X ∧ Y₁.rank ≤ r ∧
    ‖Y₁ - X‖ ≤ κ * distLR r X
```

`MatrixProjEuler.stepRel.hasLocalError_of_tube` in [`LeanDLRA/Integrators/Matrix/ProjectedEuler.lean`, lines 267–276](../LeanDLRA/Integrators/Matrix/ProjectedEuler.lean#L267-L276):

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

`MatrixProjEuler.exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Matrix/ProjectedEuler.lean`, lines 417–432](../LeanDLRA/Integrators/Matrix/ProjectedEuler.lean#L417-L432):

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

`MatrixPRK.stepRel` in [`LeanDLRA/Integrators/Matrix/ProjectedRK.lean`, lines 99–107](../LeanDLRA/Integrators/Matrix/ProjectedRK.lean#L99-L107):

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

`MatrixPRK.exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Matrix/ProjectedRK.lean`, lines 558–583](../LeanDLRA/Integrators/Matrix/ProjectedRK.lean#L558-L583):

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

`AugmentationRank.error_le_of_twoSided` in [`LeanDLRA/Research/TwoSidedLeak.lean`, lines 657–704](../LeanDLRA/Research/TwoSidedLeak.lean#L657-L704):

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
hypotheses; their existence is not formalized. The theorem is a bound for one step: it gives no
global error. The file ends with a step on `2 × 2` matrices for which the leak of `C` is 1 and
the hypotheses hold (`AugmentationRank.isRankAdaptiveStep_leakLeft`,
`AugmentationRank.leak_leakLeft`).

Source: the module docstring cites Ceruti, Kusch and Lubich, arXiv 2104.05247, and Ceruti,
Einkemmer, Kusch and Lubich, arXiv 2402.08607, Section 5.2.

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

`StiffOrderReduction.Example.not_exists_uniform_bound` in [`LeanDLRA/Research/StiffOrderReduction.lean`, lines 880–883](../LeanDLRA/Research/StiffOrderReduction.lean#L880-L883):

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
step.

Source: the theorem cites no theorem of a paper. The module docstring refers to the smoothing
estimates of arXiv 1803.10473, Assumption 1(a).

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

## 11. Citation keys

The keys in square brackets are entries of [`docs/references.bib`](references.bib), which gives
the authors, the title, the journal and the arXiv identifier of each paper.
`uv run -q scripts/docgen.py keys` lists the keys that the core and the pages of `docs/` use
and that have no entry. Where a docstring cites a paper by its arXiv number or by the names of
its authors, this page does the same.
