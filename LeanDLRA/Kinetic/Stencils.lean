import LeanDLRA.Kinetic.Defs

/-!
# Periodic difference matrices: action on matrices and transposes

The periodic difference matrices `fwdDiff`, `bwdDiff`, `centralDiff` and `secondDiff` of
`LeanDLRA/Kinetic/Defs.lean` act on a kinetic unknown `u ∈ ℝ^{N × κ}` (cells times velocity
modes or nodes) by multiplication from the left, column by column. This file gives the stencils
of these products and the transposes of the four matrices, which are the matrix form of
summation by parts on a periodic grid.

## Main statements

* `LeanDLRA.Kinetic.fwdDiff_mul_apply`, `bwdDiff_mul_apply`, `centralDiff_mul_apply`,
  `secondDiff_mul_apply`: the entries of `D * u`, for example
  `(fwdDiff N h * u) i k = (u (i + 1) k - u i k) / h`.
* `LeanDLRA.Kinetic.fwdDiff_transpose`, `bwdDiff_transpose`: `(D⁺)ᵀ = -D⁻` and `(D⁻)ᵀ = -D⁺`.
* `LeanDLRA.Kinetic.centralDiff_transpose`: the central difference is skew.
* `LeanDLRA.Kinetic.secondDiff_transpose`: the second difference is symmetric.
* `LeanDLRA.Kinetic.fwdDiff_submatrix_finEquiv`, `bwdDiff_submatrix_finEquiv`,
  `centralDiff_submatrix_finEquiv`, `secondDiff_submatrix_finEquiv`: the four matrices with the
  cells numbered by `Fin N`, entry by entry.
* `LeanDLRA.Kinetic.fwdDiff_submatrix_finEquiv_mulVec` and the three analogues: their stencils on
  `Fin N`, for example `(ψ (i + 1) - ψ i) / h`.

## Cells numbered by `Fin N`

The periodic grid of the core is `ZMod N`, so that `i + 1` and `i - 1` wrap around. A stencil
written on `Fin N` (whose addition wraps around as well) is the core stencil read through Mathlib's
ring isomorphism `ZMod.finEquiv N : Fin N ≃+* ZMod N` on both sides, that is
`(fwdDiff N h).submatrix (ZMod.finEquiv N) (ZMod.finEquiv N)`; on `Fin (n + 1)` take
`N = n + 1`. Statements do not use the definitional equality of `ZMod (n + 1)` and `Fin (n + 1)`.
-/

open Finset
open scoped Matrix

namespace LeanDLRA.Kinetic

/-! ### Transposes -/

section Transpose

/-- Moving the shift across an equation in `ZMod N`. -/
private theorem eq_add_one_iff {N : ℕ} (i j : ZMod N) : i = j + 1 ↔ j = i - 1 :=
  ⟨fun h => by rw [h]; ring, fun h => by rw [h]; ring⟩

/-- Moving the shift across an equation in `ZMod N`. -/
private theorem eq_sub_one_iff {N : ℕ} (i j : ZMod N) : i = j - 1 ↔ j = i + 1 :=
  ⟨fun h => by rw [h]; ring, fun h => by rw [h]; ring⟩

variable {N : ℕ} {h : ℝ}

/-- The transpose of the periodic backward difference is minus the forward difference:
summation by parts on a periodic grid, in matrix form. -/
theorem bwdDiff_transpose : (bwdDiff N h)ᵀ = -fwdDiff N h := by
  ext i j
  have h2 := eq_sub_one_iff i j
  have h3 : i = j ↔ j = i := eq_comm
  simp only [Matrix.transpose_apply, bwdDiff, fwdDiff, Matrix.of_apply, Matrix.neg_apply, h2, h3]
  ring

/-- The transpose of the periodic forward difference is minus the backward difference. -/
theorem fwdDiff_transpose : (fwdDiff N h)ᵀ = -bwdDiff N h := by
  rw [← neg_eq_iff_eq_neg, ← Matrix.transpose_neg, ← bwdDiff_transpose,
    Matrix.transpose_transpose]

/-- The periodic central difference is skew. -/
theorem centralDiff_transpose : (centralDiff N h)ᵀ = -centralDiff N h := by
  ext i j
  have h1 := eq_add_one_iff i j
  have h2 := eq_sub_one_iff i j
  simp only [Matrix.transpose_apply, centralDiff, Matrix.of_apply, Matrix.neg_apply, h1, h2]
  ring

/-- The periodic second difference is symmetric. -/
theorem secondDiff_transpose : (secondDiff N h)ᵀ = secondDiff N h := by
  ext i j
  have h1 := eq_add_one_iff i j
  have h2 := eq_sub_one_iff i j
  have h3 : i = j ↔ j = i := eq_comm
  simp only [Matrix.transpose_apply, secondDiff, Matrix.of_apply, h1, h2, h3]
  ring

/-- On three cells with `h = 1/2`: the entry `(0, 1)` of `(D⁻)ᵀ` is `-D⁺(0, 1) = -2`, and the
entry `(0, 1)` of `(D⁰)ᵀ` is `-D⁰(0, 1) = -1`. -/
example : (bwdDiff 3 (1 / 2))ᵀ 0 1 = -2 ∧ (centralDiff 3 (1 / 2))ᵀ 0 1 = -1 := by
  rw [bwdDiff_transpose, centralDiff_transpose, Matrix.neg_apply, Matrix.neg_apply, fwdDiff,
    centralDiff, Matrix.of_apply, Matrix.of_apply, ite_eq_left (by decide),
    ite_eq_right (by decide), ite_eq_right (by decide)]
  norm_num

/-- On three cells with `h = 1/2`: the entry `(0, 1)` of `(D⁺)ᵀ` is `-D⁻(0, 1) = 0`, the entry
`(1, 0)` is `-D⁻(1, 0) = 2`, and `(D²)ᵀ(0, 1) = D²(0, 1) = 4`. -/
example : (fwdDiff 3 (1 / 2))ᵀ 0 1 = 0 ∧ (fwdDiff 3 (1 / 2))ᵀ 1 0 = 2 ∧
    (secondDiff 3 (1 / 2))ᵀ 0 1 = 4 := by
  rw [fwdDiff_transpose, secondDiff_transpose, Matrix.neg_apply, Matrix.neg_apply, bwdDiff,
    secondDiff, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide),
    ite_eq_left (by decide)]
  norm_num

end Transpose

/-! ### The stencils of the products -/

section Mul

variable {N : ℕ} [NeZero N] {κ : Type*} {h : ℝ}

/-- The forward difference acts on the columns of `u`. -/
theorem fwdDiff_mul_apply (u : Matrix (ZMod N) κ ℝ) (i : ZMod N) (k : κ) :
    (fwdDiff N h * u) i k = (u (i + 1) k - u i k) / h := by
  simp only [Matrix.mul_apply, fwdDiff, Matrix.of_apply, div_mul_eq_mul_div, ← Finset.sum_div,
    sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- The backward difference acts on the columns of `u`. -/
theorem bwdDiff_mul_apply (u : Matrix (ZMod N) κ ℝ) (i : ZMod N) (k : κ) :
    (bwdDiff N h * u) i k = (u i k - u (i - 1) k) / h := by
  simp only [Matrix.mul_apply, bwdDiff, Matrix.of_apply, div_mul_eq_mul_div, ← Finset.sum_div,
    sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- The central difference acts on the columns of `u`. -/
theorem centralDiff_mul_apply (u : Matrix (ZMod N) κ ℝ) (i : ZMod N) (k : κ) :
    (centralDiff N h * u) i k = (u (i + 1) k - u (i - 1) k) / (2 * h) := by
  simp only [Matrix.mul_apply, centralDiff, Matrix.of_apply, div_mul_eq_mul_div, ← Finset.sum_div,
    sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- The second difference acts on the columns of `u`. -/
theorem secondDiff_mul_apply (u : Matrix (ZMod N) κ ℝ) (i : ZMod N) (k : κ) :
    (secondDiff N h * u) i k = (u (i + 1) k - 2 * u i k + u (i - 1) k) / h ^ 2 := by
  simp only [Matrix.mul_apply, secondDiff, Matrix.of_apply, div_mul_eq_mul_div, ← Finset.sum_div,
    add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    mul_assoc, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- On three cells with `h = 1/2` and the column `u = e₁`: `(D⁺ u)₀ = 2`, `(D⁻ u)₁ = 2`,
`(D⁰ u)₀ = 1` and `(D² u)₁ = -8`. -/
example (u : Matrix (ZMod 3) Unit ℝ) (hu : u = Matrix.of fun i _ => if i = 1 then 1 else 0) :
    (fwdDiff 3 (1 / 2) * u) 0 () = 2 ∧ (bwdDiff 3 (1 / 2) * u) 1 () = 2 ∧
      (centralDiff 3 (1 / 2) * u) 0 () = 1 ∧ (secondDiff 3 (1 / 2) * u) 1 () = -8 := by
  have h0 : u 0 () = 0 := by rw [hu, Matrix.of_apply, ite_eq_right (by decide)]
  have h1 : u 1 () = 1 := by rw [hu, Matrix.of_apply, ite_eq_left rfl]
  have h2 : u 2 () = 0 := by rw [hu, Matrix.of_apply, ite_eq_right (by decide)]
  have e1 : (0 : ZMod 3) + 1 = 1 := by decide
  have e2 : (0 : ZMod 3) - 1 = 2 := by decide
  have e3 : (1 : ZMod 3) - 1 = 0 := by decide
  have e4 : (1 : ZMod 3) + 1 = 2 := by decide
  rw [fwdDiff_mul_apply, bwdDiff_mul_apply, centralDiff_mul_apply, secondDiff_mul_apply, e1, e2,
    e3, e4, h0, h1, h2]
  norm_num

end Mul

/-! ### Cells numbered by `Fin N` -/

section FinIndex

variable {N : ℕ} [NeZero N] {h : ℝ}

/-- Moving `ZMod.finEquiv` across a shift to the right. -/
private theorem finEquiv_eq_add_one_iff (i j : Fin N) :
    ZMod.finEquiv N j = ZMod.finEquiv N i + 1 ↔ j = i + 1 := by
  rw [← map_one (ZMod.finEquiv N), ← map_add, (ZMod.finEquiv N).injective.eq_iff]

/-- Moving `ZMod.finEquiv` across a shift to the left. -/
private theorem finEquiv_eq_sub_one_iff (i j : Fin N) :
    ZMod.finEquiv N j = ZMod.finEquiv N i - 1 ↔ j = i - 1 := by
  rw [← map_one (ZMod.finEquiv N), ← map_sub, (ZMod.finEquiv N).injective.eq_iff]

/-- The forward difference with the cells numbered by `Fin N`. -/
theorem fwdDiff_submatrix_finEquiv :
    (fwdDiff N h).submatrix (ZMod.finEquiv N) (ZMod.finEquiv N) =
      Matrix.of fun i j : Fin N =>
        ((if j = i + 1 then 1 else 0) - (if j = i then 1 else 0)) / h := by
  ext i j
  simp only [Matrix.submatrix_apply, fwdDiff, Matrix.of_apply, finEquiv_eq_add_one_iff,
    (ZMod.finEquiv N).injective.eq_iff]

/-- The backward difference with the cells numbered by `Fin N`. -/
theorem bwdDiff_submatrix_finEquiv :
    (bwdDiff N h).submatrix (ZMod.finEquiv N) (ZMod.finEquiv N) =
      Matrix.of fun i j : Fin N =>
        ((if j = i then 1 else 0) - (if j = i - 1 then 1 else 0)) / h := by
  ext i j
  simp only [Matrix.submatrix_apply, bwdDiff, Matrix.of_apply, finEquiv_eq_sub_one_iff,
    (ZMod.finEquiv N).injective.eq_iff]

/-- The central difference with the cells numbered by `Fin N`. -/
theorem centralDiff_submatrix_finEquiv :
    (centralDiff N h).submatrix (ZMod.finEquiv N) (ZMod.finEquiv N) =
      Matrix.of fun i j : Fin N =>
        ((if j = i + 1 then 1 else 0) - (if j = i - 1 then 1 else 0)) / (2 * h) := by
  ext i j
  simp only [Matrix.submatrix_apply, centralDiff, Matrix.of_apply, finEquiv_eq_add_one_iff,
    finEquiv_eq_sub_one_iff]

/-- The second difference with the cells numbered by `Fin N`. -/
theorem secondDiff_submatrix_finEquiv :
    (secondDiff N h).submatrix (ZMod.finEquiv N) (ZMod.finEquiv N) =
      Matrix.of fun i j : Fin N =>
        ((if j = i + 1 then 1 else 0) - 2 * (if j = i then 1 else 0) +
          (if j = i - 1 then 1 else 0)) / h ^ 2 := by
  ext i j
  simp only [Matrix.submatrix_apply, secondDiff, Matrix.of_apply, finEquiv_eq_add_one_iff,
    finEquiv_eq_sub_one_iff, (ZMod.finEquiv N).injective.eq_iff]

/-- The stencil of the forward difference on `Fin N`. -/
theorem fwdDiff_submatrix_finEquiv_mulVec (ψ : Fin N → ℝ) :
    (fwdDiff N h).submatrix (ZMod.finEquiv N) (ZMod.finEquiv N) *ᵥ ψ =
      fun i => (ψ (i + 1) - ψ i) / h := by
  rw [fwdDiff_submatrix_finEquiv]
  ext i
  simp [Matrix.mulVec, dotProduct, sub_div, sub_mul, ite_mul, div_mul_eq_mul_div,
    ← Finset.sum_div]

/-- The stencil of the backward difference on `Fin N`. -/
theorem bwdDiff_submatrix_finEquiv_mulVec (ψ : Fin N → ℝ) :
    (bwdDiff N h).submatrix (ZMod.finEquiv N) (ZMod.finEquiv N) *ᵥ ψ =
      fun i => (ψ i - ψ (i - 1)) / h := by
  rw [bwdDiff_submatrix_finEquiv]
  ext i
  simp [Matrix.mulVec, dotProduct, sub_div, sub_mul, ite_mul, div_mul_eq_mul_div,
    ← Finset.sum_div]

/-- The stencil of the central difference on `Fin N`. -/
theorem centralDiff_submatrix_finEquiv_mulVec (ψ : Fin N → ℝ) :
    (centralDiff N h).submatrix (ZMod.finEquiv N) (ZMod.finEquiv N) *ᵥ ψ =
      fun i => (ψ (i + 1) - ψ (i - 1)) / (2 * h) := by
  rw [centralDiff_submatrix_finEquiv]
  ext i
  simp [Matrix.mulVec, dotProduct, sub_div, sub_mul, ite_mul, div_mul_eq_mul_div,
    ← Finset.sum_div]

/-- The stencil of the second difference on `Fin N`. -/
theorem secondDiff_submatrix_finEquiv_mulVec (ψ : Fin N → ℝ) :
    (secondDiff N h).submatrix (ZMod.finEquiv N) (ZMod.finEquiv N) *ᵥ ψ =
      fun i => (ψ (i + 1) - 2 * ψ i + ψ (i - 1)) / h ^ 2 := by
  rw [secondDiff_submatrix_finEquiv]
  ext i
  simp [Matrix.mulVec, dotProduct, add_div, sub_div, add_mul, sub_mul, ite_mul,
    div_mul_eq_mul_div, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]

/-- On `Fin 3` with `h = 1/2`: the wrap-around entry `D⁺(2, 0) = 2`, `D⁻(0, 2) = -2`,
`D⁰(0, 1) = 1` and `D²(1, 1) = -8`, read through `ZMod.finEquiv 3`. -/
example :
    (fwdDiff 3 (1 / 2)).submatrix (ZMod.finEquiv 3) (ZMod.finEquiv 3) 2 0 = 2 ∧
      (bwdDiff 3 (1 / 2)).submatrix (ZMod.finEquiv 3) (ZMod.finEquiv 3) 0 2 = -2 ∧
      (centralDiff 3 (1 / 2)).submatrix (ZMod.finEquiv 3) (ZMod.finEquiv 3) 0 1 = 1 ∧
      (secondDiff 3 (1 / 2)).submatrix (ZMod.finEquiv 3) (ZMod.finEquiv 3) 1 1 = -8 := by
  rw [fwdDiff_submatrix_finEquiv, bwdDiff_submatrix_finEquiv, centralDiff_submatrix_finEquiv,
    secondDiff_submatrix_finEquiv]
  simp only [Matrix.of_apply]
  norm_num [Fin.ext_iff]

/-- On `Fin 3` with `h = 1/2` and the indicator `ψ` of cell `1`: `(D⁺ ψ)₀ = 2`, `(D⁻ ψ)₁ = 2`,
`(D⁰ ψ)₀ = 1` and `(D² ψ)₁ = -8`. -/
example (ψ : Fin 3 → ℝ) (hψ : ψ = fun i => if i = 1 then 1 else 0) :
    ((fwdDiff 3 (1 / 2)).submatrix (ZMod.finEquiv 3) (ZMod.finEquiv 3) *ᵥ ψ) 0 = 2 ∧
      ((bwdDiff 3 (1 / 2)).submatrix (ZMod.finEquiv 3) (ZMod.finEquiv 3) *ᵥ ψ) 1 = 2 ∧
      ((centralDiff 3 (1 / 2)).submatrix (ZMod.finEquiv 3) (ZMod.finEquiv 3) *ᵥ ψ) 0 = 1 ∧
      ((secondDiff 3 (1 / 2)).submatrix (ZMod.finEquiv 3) (ZMod.finEquiv 3) *ᵥ ψ) 1 = -8 := by
  rw [fwdDiff_submatrix_finEquiv_mulVec, bwdDiff_submatrix_finEquiv_mulVec,
    centralDiff_submatrix_finEquiv_mulVec, secondDiff_submatrix_finEquiv_mulVec, hψ]
  norm_num [Fin.ext_iff]

end FinIndex

end LeanDLRA.Kinetic
