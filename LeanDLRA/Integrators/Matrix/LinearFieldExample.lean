import LeanDLRA.Integrators.Defs
import LeanDLRA.Integrators.Matrix.Defs
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A concrete instance of the linear test field

The non-vacuity examples of the matrix integrators use the linear field
`F(t, Y) = M Y + Y Nᵀ + G` with a stationary point `C` (`M C + C Nᵀ + G = 0`), see
`LeanDLRA.dlraProblem_linear` and `LeanDLRA.factoredNormalBoundOn_linear`. This file fixes one
instance of it, so that the concrete examples of the integrators all treat the same problem:
on `2 × 2` matrices, with `E = e₁ e₁ᵀ` (written `Matrix.vecMulVec ![1, 0] ![1, 0]`),

* `M = -E`, `N = 0`, `G = C = E`; since `E² = E`, `C = E` is a stationary point;
* the Lipschitz constant is `‖M‖ + ‖N‖ = 1`, the normal bound `‖G‖ = 1`, and on the tube of
  radius `ρ` around the constant solution `A(t) = E` the field is bounded by `ρ`;
* the start value is `Y₀ = (5/4) E = e₁ (5/4) e₁ᵀ`, of rank one, with `‖Y₀ - C‖ = 1/4`.

The examples take the rank `r = 1`, `K = 10` steps of size `h = 1/100` up to `T = 1/10` and the
tube radius `ρ = 4`; the facts on the constants of the error bounds for these values are here
too.

## Main results

* `LeanDLRA.LinearFieldExample.norm_vecMulVec_one_zero`: `‖E‖ = 1`.
* `LeanDLRA.LinearFieldExample.stationary_vecMulVec_one_zero`: `-E E + E 0ᵀ + E = 0`.
* `LeanDLRA.LinearFieldExample.norm_start_sub_le`: `‖Y₀ - E‖ ≤ 1/4`.
  `LeanDLRA.LinearFieldExample.col_mul_mul_col_transpose_eq_vecMulVec`: the start value in
  factored form `e₁ (5/4) e₁ᵀ`, with the orthonormal column `e₁`.
* `LeanDLRA.LinearFieldExample.dlraProblem`, `LeanDLRA.LinearFieldExample.isLipschitzField`,
  `LeanDLRA.LinearFieldExample.factoredNormalBoundOn`: the hypotheses of the error theorems
  for this field, with `L = 1`, `B = ρ` and `ε = 1`.
* `LeanDLRA.LinearFieldExample.exp_le_three`, `LeanDLRA.LinearFieldExample.bugC₁_le`,
  `LeanDLRA.LinearFieldExample.bugC₂_le`: bounds of the constants of the error bounds for
  `L = 1`, `B = 4`, `T = 1/10` and `H = 1/100`.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace LinearFieldExample

/-- The rank-one matrix `E = e₁ e₁ᵀ` on `ℝ²` has norm `1`. -/
theorem norm_vecMulVec_one_zero : ‖Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]‖ = 1 := by
  have h2 : ‖Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]‖ ^ 2 = 1 := by
    rw [Frobenius.norm_sq_eq_sum]
    norm_num [Matrix.vecMulVec_apply, Fin.sum_univ_two]
  have h0 := norm_nonneg (Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0])
  nlinarith

/-- `C = E = e₁ e₁ᵀ` is a stationary point of `F(t, Y) = -E Y + Y 0ᵀ + E`, since `E² = E`. -/
theorem stationary_vecMulVec_one_zero :
    -Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0] * Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0] +
      Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0] * (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ +
      Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0] = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The Lipschitz constant `‖M‖ + ‖N‖` of the linear field with `M = -E`, `N = 0` is `1`. -/
theorem norm_neg_vecMulVec_add_norm_zero :
    ‖-Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]‖ + ‖(0 : Matrix (Fin 2) (Fin 2) ℝ)‖ = 1 := by
  rw [norm_neg, norm_zero, norm_vecMulVec_one_zero, add_zero]

/-- The start value `Y₀ = (5/4) e₁ e₁ᵀ` is at distance `1/4` from the stationary point `E`. -/
theorem norm_start_sub_le :
    ‖Matrix.vecMulVec ![(5 / 4 : ℝ), 0] ![1, 0] - Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]‖ ≤
      1 / 4 := by
  have h2 : ‖Matrix.vecMulVec ![(5 / 4 : ℝ), 0] ![1, 0] -
      Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]‖ ^ 2 = 1 / 16 := by
    rw [Frobenius.norm_sq_eq_sum]
    norm_num [Matrix.vecMulVec_apply, Fin.sum_univ_two]
  nlinarith [norm_nonneg (Matrix.vecMulVec ![(5 / 4 : ℝ), 0] ![1, 0] -
    Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0])]

/-- The start value in factored form: `e₁ (5/4) e₁ᵀ = (5/4) e₁ e₁ᵀ`. -/
theorem col_mul_mul_col_transpose_eq_vecMulVec :
    (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) * (!![5 / 4] : Matrix (Fin 1) (Fin 1) ℝ) *
      (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ = Matrix.vecMulVec ![5 / 4, 0] ![1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.vecMulVec_apply, Fin.sum_univ_two, Matrix.vecHead,
      Function.swap]

/-- The field `F(t, Y) = -E Y + Y 0ᵀ + E` is globally Lipschitz with constant `1`. -/
theorem isLipschitzField :
    IsLipschitzField (fun _ (Y : Matrix (Fin 2) (Fin 2) ℝ) =>
      -Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0] * Y + Y * (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ +
        Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]) 1 := by
  have h := isLipschitzField_linear (-Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0])
    (0 : Matrix (Fin 2) (Fin 2) ℝ) (Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0])
  rwa [norm_neg_vecMulVec_add_norm_zero] at h

/-- Around its stationary point `E` the field `F(t, Y) = -E Y + Y 0ᵀ + E` is a `DLRAProblem` on
the tube of every radius `ρ ≥ 0`, with Lipschitz constant `1` and bound `ρ`. -/
theorem dlraProblem (a b : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    DLRAProblem (fun _ (Y : Matrix (Fin 2) (Fin 2) ℝ) =>
      -Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0] * Y + Y * (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ +
        Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0])
      (fun _ => Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]) a b ρ 1 ρ := by
  have h := dlraProblem_linear (-Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0])
    (0 : Matrix (Fin 2) (Fin 2) ℝ) (Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0])
    (Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]) stationary_vecMulVec_one_zero a b hρ
  rwa [norm_neg_vecMulVec_add_norm_zero, one_mul] at h

/-- The normal component of `F(t, Y) = -E Y + Y 0ᵀ + E` at the factored matrices with any number
`r` of columns is at most `‖E‖ = 1`, on every region `D`. -/
theorem factoredNormalBoundOn (r : ℕ) (D : Set (ℝ × Matrix (Fin 2) (Fin 2) ℝ)) :
    FactoredNormalBoundOn (fun _ (Y : Matrix (Fin 2) (Fin 2) ℝ) =>
      -Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0] * Y + Y * (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ +
        Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]) r D 1 := by
  have h := factoredNormalBoundOn_linear (r := r) (-Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0])
    (0 : Matrix (Fin 2) (Fin 2) ℝ) (Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]) D
  rwa [norm_vecMulVec_one_zero] at h

/-- The exponential factor `e^{L T}` of the error bounds for `L = 1` and `T = 1/10` is at most
`3`. -/
theorem exp_le_three : Real.exp (1 * (1 / 10)) ≤ 3 :=
  (Real.exp_le_exp.2 (by norm_num : (1 : ℝ) * (1 / 10) ≤ 1)).trans Real.exp_one_lt_three.le

/-- The constant `bugC₁ L H` of the BUG error bound for `L = 1` and `H = 1/100` is at most
`21/10`. -/
theorem bugC₁_le : bugC₁ 1 (1 / 100) ≤ 21 / 10 := by
  have h : Real.exp (1 * (1 / 100)) ≤ 3 :=
    (Real.exp_le_exp.2 (by norm_num : (1 : ℝ) * (1 / 100) ≤ 1)).trans Real.exp_one_lt_three.le
  unfold bugC₁
  linarith

/-- The constant `bugC₂ L B H` of the BUG error bound for `L = 1`, `B = 4` and `H = 1/100` is at
most `45`. -/
theorem bugC₂_le : bugC₂ 1 4 (1 / 100) ≤ 45 := by
  have h : Real.exp (1 * (1 / 100)) ≤ 3 :=
    (Real.exp_le_exp.2 (by norm_num : (1 : ℝ) * (1 / 100) ≤ 1)).trans Real.exp_one_lt_three.le
  unfold bugC₂
  nlinarith

end LinearFieldExample

end LeanDLRA
