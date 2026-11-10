import LeanDLRA.LinearAlgebra.LowRank.Defs

/-!
# Separation rank and the fixed-rank set

Two rank notions next to the low-rank set `LeanDLRA.lowRankSet` of
`LeanDLRA/LinearAlgebra/LowRank/Defs.lean`.

A function `f` of two variables has *separation rank at most `r`* if it is a sum of `r` products of
a function of the first variable and a function of the second variable. This is the rank of a
function `f(x, v)` on phase space before any discretization. It is stated over a semiring, so that
real and complex functions are covered by one definition. The Mathlib notion behind it is
`Matrix.rank`: on finite index types and over a field, separation rank at most `r` is matrix rank
at most `r`, and for arbitrary types it bounds the rank of every matrix of samples.

The *fixed-rank set* `{Y : rank Y = r}` is the set on which the equations of dynamical low-rank
approximation are posed; `lowRankSet m n r` is the union of the fixed-rank sets of rank at most
`r`.

## Main definitions

* `LeanDLRA.HasSepRankLE R f r`: `f x y = ∑ k : Fin r, U k x * V k y` for some `U`, `V` with values
  in the semiring `R`.
* `LeanDLRA.fixedRankSet m n r`: the set of real `m × n` matrices of rank exactly `r`.

## Main statements

* `LeanDLRA.HasSepRankLE.of_sum`: a sum of products over any finite index type with at most `r`
  elements has separation rank at most `r`; `LeanDLRA.HasSepRankLE.mono` is monotonicity in `r`.
* `LeanDLRA.HasSepRankLE.rank_le`: every matrix of samples `f (xs i) (ys j)` has rank at most `r`.
* `LeanDLRA.hasSepRankLE_iff_rank_le`: over a field and on finite types,
  `HasSepRankLE K f r ↔ (Matrix.of f).rank ≤ r`.
* `LeanDLRA.hasSepRankLE_iff_mem_lowRankSet`: for a real matrix `A`, the entries have separation
  rank at most `r` if and only if `A ∈ lowRankSet m n r`.
* `LeanDLRA.mem_lowRankSet_iff_exists_mem_fixedRankSet`: `lowRankSet m n r` is the union of the
  sets `fixedRankSet m n s`, `s ≤ r`.
* `LeanDLRA.mem_fixedRankSet_of_factor`: `U * S * Vᵀ` with orthonormal columns in `U` and `V` and
  an invertible core `S` has rank exactly the number of columns.

## Implementation notes

The file is a leaf above `LowRank/Defs.lean`: the definitions are not placed in that file, whose
import closure and auxiliary proofs then stay as they are.

The converse of `mem_fixedRankSet_of_factor` (rank `r` forces an injective core) is
`LeanDLRA.injective_of_eq_mul` of `LeanDLRA/Classical/SVD.lean`.
-/

open scoped Matrix

namespace LeanDLRA

/-! ### Separation rank -/

section SepRank

open Finset

variable {X Y R : Type*}

/-- `f` has separation rank at most `r` over the semiring `R`: it is a sum of `r` products of a
function of the first variable and a function of the second variable,
`f x y = ∑ k : Fin r, U k x * V k y`. -/
def HasSepRankLE (R : Type*) [Semiring R] (f : X → Y → R) (r : ℕ) : Prop :=
  ∃ (U : Fin r → X → R) (V : Fin r → Y → R), ∀ x y, f x y = ∑ k, U k x * V k y

/-- A sum of products over a finite index type with at most `r` elements has separation rank at
most `r`: the terms are numbered by an embedding into `Fin r` and padded with zeros. -/
theorem HasSepRankLE.of_sum [Semiring R] {ι : Type*} [Fintype ι] {f : X → Y → R} {r : ℕ}
    (a : ι → X → R) (b : ι → Y → R) (h : ∀ x y, f x y = ∑ i, a i x * b i y)
    (hr : Fintype.card ι ≤ r) : HasSepRankLE R f r := by
  classical
  obtain ⟨e⟩ : Nonempty (ι ↪ Fin r) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hr)
  refine ⟨fun k x => Function.extend e (fun i => a i x) 0 k,
    fun k y => Function.extend e (fun i => b i y) 0 k, fun x y => ?_⟩
  rw [h, ← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)), Finset.sum_map]
  · exact Finset.sum_congr rfl fun i _ => by simp [e.injective.extend_apply]
  · intro k _ hk
    have hk' : ¬ ∃ i, e i = k := by simpa using hk
    simp [Function.extend_apply' _ _ _ hk']

/-- Separation rank at most `r` is monotone in `r`. -/
theorem HasSepRankLE.mono [Semiring R] {f : X → Y → R} {r s : ℕ} (h : HasSepRankLE R f r)
    (hrs : r ≤ s) : HasSepRankLE R f s := by
  obtain ⟨U, V, hUV⟩ := h
  exact HasSepRankLE.of_sum U V hUV (by simpa using hrs)

/-- Separation rank at most `r` bounds the rank of every matrix of samples `f (xs i) (ys j)`: what
a grid stores of `f` has matrix rank at most `r`. -/
theorem HasSepRankLE.rank_le [CommRing R] [StrongRankCondition R] {p q : Type*} [Finite p]
    [Fintype q] {f : X → Y → R} {r : ℕ} (h : HasSepRankLE R f r) (xs : p → X) (ys : q → Y) :
    (Matrix.of fun i j => f (xs i) (ys j)).rank ≤ r := by
  classical
  have := Fintype.ofFinite p
  obtain ⟨U, V, hUV⟩ := h
  have hfac : (Matrix.of fun i j => f (xs i) (ys j)) =
      (Matrix.of fun i k => U k (xs i) : Matrix p (Fin r) R) *
        (Matrix.of fun k j => V k (ys j) : Matrix (Fin r) q R) := by
    ext i j
    simp [Matrix.mul_apply, hUV]
  rw [hfac]
  refine (Matrix.rank_mul_le_left _ _).trans ?_
  simpa using Matrix.rank_le_card_width (Matrix.of fun i k => U k (xs i) : Matrix p (Fin r) R)

/-- Over a field, the entries of a matrix of rank at most `r` have separation rank at most `r`:
the columns are expanded in a basis of the column space. -/
theorem hasSepRankLE_of_rank_le {m n K : Type*} [Finite m] [Fintype n] [Field K]
    {A : Matrix m n K} {r : ℕ} (h : A.rank ≤ r) : HasSepRankLE K (fun i j => A i j) r := by
  classical
  let W : Submodule K (m → K) := LinearMap.range A.mulVecLin
  let b := Module.finBasis K W
  have hcol : ∀ j, A.col j ∈ W := fun j =>
    ⟨Pi.single j 1, by simp⟩
  refine HasSepRankLE.of_sum (fun k i => (b k : m → K) i)
    (fun k j => b.repr ⟨A.col j, hcol j⟩ k) (fun i j => ?_) (by simpa [Matrix.rank] using h)
  have h1 := congrArg (fun w : W => (w : m → K) i) (b.sum_repr ⟨A.col j, hcol j⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h1
  rw [show A i j = A.col j i from rfl, ← h1]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **Separation rank is matrix rank.** Over a field and on finite index types, `f` has separation
rank at most `r` if and only if the matrix `Matrix.of f` has rank at most `r`. -/
theorem hasSepRankLE_iff_rank_le {m n K : Type*} [Finite m] [Fintype n] [Field K]
    (f : m → n → K) (r : ℕ) : HasSepRankLE K f r ↔ (Matrix.of f).rank ≤ r :=
  ⟨fun h => h.rank_le id id, fun h => hasSepRankLE_of_rank_le h⟩

/-- For a real matrix `A`, the entries have separation rank at most `r` if and only if `A` lies in
the low-rank set `lowRankSet m n r`. -/
theorem hasSepRankLE_iff_mem_lowRankSet {m n : Type*} [Finite m] [Fintype n]
    (A : Matrix m n ℝ) (r : ℕ) : HasSepRankLE ℝ (fun i j => A i j) r ↔ A ∈ lowRankSet m n r :=
  hasSepRankLE_iff_rank_le (fun i j => A i j) r

/-- The function `x y + 1` on `ℝ × ℝ` has separation rank at most two. -/
example : HasSepRankLE ℝ (fun x y : ℝ => x * y + 1) 2 :=
  ⟨![fun x => x, fun _ => 1], ![fun y => y, fun _ => 1], fun x y => by simp [Fin.sum_univ_two]⟩

/-- Every matrix of samples of `x y + 1` has rank at most two. -/
example (xs : Fin 4 → ℝ) (ys : Fin 5 → ℝ) : (Matrix.of fun i j => xs i * ys j + 1).rank ≤ 2 :=
  HasSepRankLE.rank_le (f := fun x y : ℝ => x * y + 1)
    ⟨![fun x => x, fun _ => 1], ![fun y => y, fun _ => 1], fun x y => by simp [Fin.sum_univ_two]⟩
    xs ys

/-- The `3 × 3` matrix with the nonzero entries `(i + 1) (j + 2)` lies in the set of matrices of
rank at most one. -/
example : (Matrix.of fun i j : Fin 3 => ((i : ℝ) + 1) * ((j : ℝ) + 2)) ∈
    lowRankSet (Fin 3) (Fin 3) 1 :=
  (hasSepRankLE_iff_mem_lowRankSet _ 1).1
    ⟨fun _ i => (i : ℝ) + 1, fun _ j => (j : ℝ) + 2, fun i j => by simp⟩

end SepRank

/-! ### The fixed-rank set -/

section FixedRank

variable {m n : Type*} [Fintype n] {r : ℕ}

/-- The set of real `m × n` matrices of rank exactly `r`. -/
def fixedRankSet (m n : Type*) [Fintype n] (r : ℕ) : Set (Matrix m n ℝ) := {Y | Y.rank = r}

/-- Membership in the fixed-rank set. -/
@[simp] lemma mem_fixedRankSet {Y : Matrix m n ℝ} : Y ∈ fixedRankSet m n r ↔ Y.rank = r :=
  Iff.rfl

/-- A matrix of rank `r` has rank at most `r`. -/
theorem fixedRankSet_subset_lowRankSet (m n : Type*) [Fintype n] (r : ℕ) :
    fixedRankSet m n r ⊆ lowRankSet m n r := fun _ h => le_of_eq h

/-- The low-rank set is the union of the fixed-rank sets of rank at most `r`. -/
theorem mem_lowRankSet_iff_exists_mem_fixedRankSet {Y : Matrix m n ℝ} :
    Y ∈ lowRankSet m n r ↔ ∃ s ≤ r, Y ∈ fixedRankSet m n s :=
  ⟨fun h => ⟨Y.rank, h, rfl⟩, fun ⟨_, hs, h⟩ => (le_of_eq h).trans hs⟩

/-- A factorization `U S Vᵀ` with orthonormal columns in `U` and `V` and an invertible core `S`
has rank exactly the number of columns. -/
theorem mem_fixedRankSet_of_factor {k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    {U : Matrix m k ℝ} {S : Matrix k k ℝ} {V : Matrix n k ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hS : IsUnit S) : U * S * Vᵀ ∈ fixedRankSet m n (Fintype.card k) := by
  rw [mem_fixedRankSet]
  refine le_antisymm ?_ ?_
  · calc (U * S * Vᵀ).rank ≤ (U * S).rank := Matrix.rank_mul_le_left _ _
      _ ≤ U.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card k := U.rank_le_card_width
  · have hSeq : Uᵀ * (U * S * Vᵀ) * V = S := by
      calc Uᵀ * (U * S * Vᵀ) * V = Uᵀ * U * S * (Vᵀ * V) := by simp only [Matrix.mul_assoc]
        _ = S := by rw [hU, hV, Matrix.one_mul, Matrix.mul_one]
    calc Fintype.card k = S.rank := (Matrix.rank_of_isUnit S hS).symm
      _ = (Uᵀ * (U * S * Vᵀ) * V).rank := by rw [hSeq]
      _ ≤ (Uᵀ * (U * S * Vᵀ)).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (U * S * Vᵀ).rank := Matrix.rank_mul_le_right _ _

/-- The diagonal matrix with the entries `2`, `3` has rank exactly two, and with it rank at most
two. -/
example : Matrix.diagonal ![(2 : ℝ), 3] ∈ fixedRankSet (Fin 2) (Fin 2) 2 ∧
    Matrix.diagonal ![(2 : ℝ), 3] ∈ lowRankSet (Fin 2) (Fin 2) 2 := by
  have hS : IsUnit (Matrix.diagonal ![(2 : ℝ), 3]) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
    simp [Fin.prod_univ_two]
  have h := mem_fixedRankSet_of_factor (m := Fin 2) (n := Fin 2)
    (U := 1) (V := 1) (by simp) (by simp) hS
  have h' : Matrix.diagonal ![(2 : ℝ), 3] ∈ fixedRankSet (Fin 2) (Fin 2) 2 := by simpa using h
  exact ⟨h', fixedRankSet_subset_lowRankSet _ _ _ h'⟩

end FixedRank

end LeanDLRA
