import LeanDLRA.Research.AugmentationRank
import LeanDLRA.Stochastic.KalmanBucy

/-!
# No Galerkin step in a fixed rank-one space is of second order

## Setting

`F(Y) = W Y` on `2 × 2` matrices with the rotation generator `W = [[0, -1], [1, 0]]`
(`KalmanBucy.rotGen`), and the
starting value `Y₀ = e₁ e₁ᵀ` (rank one, singular value `1`).  The field is of Sylvester type, so
it is tangent to the rank-one matrices (`factoredNormalBoundOn_rotField`), and the exact solution
is `A(t) = (cos t, sin t)ᵀ e₁ᵀ`.  A *Galerkin step in a fixed rank-one space* takes orthonormal
`u, v ∈ ℝ²` and solves `Ŷ' = u uᵀ (W Ŷ) v vᵀ`, `Ŷ(0) = u uᵀ Y₀ v vᵀ`.

## Main results

* `galerkin_eq_start_of_rankOne`: the Galerkin solution does not move, `Ŷ(h) = u uᵀ Y₀ v vᵀ`,
  because `uᵀ W u = 0`.
* `error_ge_of_rankOne_galerkin`: `‖Ŷ(h) - A(h)‖ ≥ (1 - cos h) / 2` for every choice of `u`, `v`.
* `sq_div_le_error_of_rankOne_galerkin`: `‖Ŷ(h) - A(h)‖ ≥ h² / π²` for `0 ≤ h ≤ π`.

So the local error of every such step is of size `h²` at least: a method of second order at
rank `r` cannot be a Galerkin step in one fixed space of rank `r`.  The rank-adaptive BUG
integrator, which uses a space of rank `2 r`, is exact up to `O(h³)` on this field
(`error_le_of_sylvester`).

## Implementation notes

The lower bound is not the smallest error over `u`, `v`, which is
`(5/4 - cos h)^{1/2} - 1/2`; the stated bound is below it and has a polynomial proof.

## References

* Ceruti–Kusch–Lubich, arXiv:2104.05247 (rank-adaptive BUG integrator).
* Ceruti–Einkemmer–Kusch–Lubich, arXiv:2402.08607 (second-order BUG integrators).
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace AugmentationRank

namespace Examples

open KalmanBucy (rotGen)

/-- The starting value `Y₀ = e₁ e₁ᵀ`. -/
noncomputable def rotStart : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- The matrix `W Y₀ = e₂ e₁ᵀ`. -/
noncomputable def rotVelocity : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- The exact solution `A(t) = (cos t, sin t)ᵀ e₁ᵀ` of `A' = W A`, `A(0) = e₁ e₁ᵀ`. -/
noncomputable def rotSolution (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Real.cos t • rotStart + Real.sin t • rotVelocity

end Examples

section RankOne

open MatrixBUG Examples
open KalmanBucy (rotGen)

private theorem rotGen_mul_rotStart : rotGen * rotStart = rotVelocity := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotGen, rotStart, rotVelocity, Matrix.mul_apply]

private theorem rotGen_mul_rotVelocity : rotGen * rotVelocity = -rotStart := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotGen, rotStart, rotVelocity, Matrix.mul_apply]

private theorem hasDerivAt_rotSolution (t : ℝ) :
    HasDerivAt rotSolution (rotGen * rotSolution t) t := by
  have h1 : HasDerivAt (fun s => Real.cos s • rotStart) ((-Real.sin t) • rotStart) t :=
    (Real.hasDerivAt_cos t).smul_const rotStart
  have h2 : HasDerivAt (fun s => Real.sin s • rotVelocity) (Real.cos t • rotVelocity) t :=
    (Real.hasDerivAt_sin t).smul_const rotVelocity
  have he : rotGen * rotSolution t = (-Real.sin t) • rotStart + Real.cos t • rotVelocity := by
    rw [rotSolution, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, rotGen_mul_rotStart,
      rotGen_mul_rotVelocity, smul_neg, neg_smul]
    abel
  rw [he]
  exact h1.add h2

/-- `rotSolution` solves `A' = W A` on every interval `[0, h]`. -/
theorem odeSolution_rotSolution (h : ℝ) :
    ODESolution (fun _ Y => rotGen * Y) rotSolution 0 h where
  cont := fun t _ => (hasDerivAt_rotSolution t).continuousAt.continuousWithinAt
  deriv := fun t _ => (hasDerivAt_rotSolution t).hasDerivWithinAt

/-- `rotSolution 0 = e₁ e₁ᵀ`. -/
theorem rotSolution_zero : rotSolution 0 = rotStart := by
  simp [rotSolution]

/-- The field `Y ↦ W Y` is tangent to the matrices of rank at most `r`, for every `r`: its
normal component vanishes at every `U S Vᵀ`. -/
theorem factoredNormalBoundOn_rotField (r : ℕ) :
    FactoredNormalBoundOn (fun _ Y => rotGen * Y) r Set.univ 0 := by
  intro t U V S _ hV _
  have hV0 : Vᵀ * (1 - V * Vᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hV, Matrix.one_mul, sub_self]
  simp only [Matrix.mul_assoc, hV0, Matrix.mul_zero, norm_zero, le_refl]

/-- `uᵀ W u = 0` for every vector `u ∈ ℝ²`: `W` is skew-symmetric. -/
private theorem transpose_mul_rotGen_mul_self (U : Matrix (Fin 2) (Fin 1) ℝ) :
    Uᵀ * rotGen * U = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, Fin.sum_univ_two, rotGen]
  ring

variable {U V : Matrix (Fin 2) (Fin 1) ℝ}

/-- The constant curve `u uᵀ Y₀ v vᵀ` solves the Galerkin equation `Ŷ' = u uᵀ (W Ŷ) v vᵀ` of a
rank-one space, for every starting value. -/
theorem odeSolution_const_of_rankOne (U V : Matrix (Fin 2) (Fin 1) ℝ)
    (Y₀ : Matrix (Fin 2) (Fin 2) ℝ) (h : ℝ) :
    ODESolution (fun _ Y => galerkinProj U V (rotGen * Y)) (fun _ => galerkinProj U V Y₀) 0 h where
  cont := continuousOn_const
  deriv t _ := by
    have hskew : ∀ X : Matrix (Fin 1) (Fin 2) ℝ, Uᵀ * (rotGen * (U * X)) = 0 := fun X => by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, transpose_mul_rotGen_mul_self, Matrix.zero_mul]
    have hz : galerkinProj U V (rotGen * galerkinProj U V Y₀) = 0 := by
      simp only [galerkinProj_apply, Matrix.mul_assoc, hskew, Matrix.mul_zero, Matrix.zero_mul]
    change HasDerivWithinAt (fun _ : ℝ => galerkinProj U V Y₀)
      (galerkinProj U V (rotGen * galerkinProj U V Y₀)) (Ici t) t
    rw [hz]
    exact hasDerivWithinAt_const _ _ _

/-- **A Galerkin step in a fixed rank-one space does not move** on the rotation field: every
solution of `Ŷ' = u uᵀ (W Ŷ) v vᵀ`, `Ŷ(0) = u uᵀ Y₀ v vᵀ` with orthonormal `u`, `v` is
constant. -/
theorem galerkin_eq_start_of_rankOne (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {h : ℝ} (hh : 0 ≤ h)
    {Y₀ : Matrix (Fin 2) (Fin 2) ℝ} {YS : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hS : ODESolution (fun _ Y => galerkinProj U V (rotGen * Y)) YS 0 h)
    (hS₀ : YS 0 = galerkinProj U V Y₀) : YS h = galerkinProj U V Y₀ := by
  have hR : IsOrthProj (galerkinProj U V :
      Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ) := isOrthProj_galerkinProj hU hV
  have hlip : IsLipschitzField
      (fun (_ : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) => galerkinProj U V (rotGen * Y)) ‖rotGen‖ :=
    fun _ X Y => by
      change ‖galerkinProj U V (rotGen * X) - galerkinProj U V (rotGen * Y)‖ ≤ ‖rotGen‖ * ‖X - Y‖
      rw [← map_sub, ← Matrix.mul_sub]
      exact (hR.norm_le _).trans (Frobenius.norm_mul_le _ _)
  exact hS.eqOn (odeSolution_const_of_rankOne U V Y₀ h) hlip (norm_nonneg _) hS₀
    (right_mem_Icc.2 hh)

/-- The polynomial inequality behind `error_ge_of_rankOne_galerkin`: the squared distance of
`(u₁ v₁) u vᵀ` from `(C, S)ᵀ e₁ᵀ` for unit vectors `u`, `v`, `(C, S)`. -/
private theorem rankOne_sq_ge {u₁ u₂ v₁ v₂ C S : ℝ} (hu : u₁ * u₁ + u₂ * u₂ = 1)
    (hv : v₁ * v₁ + v₂ * v₂ = 1) (hc : C ^ 2 + S ^ 2 = 1) :
    ((1 - C) / 2) ^ 2 ≤ (u₁ * v₁ * u₁ * v₁ - C) ^ 2 + (u₁ * v₁ * u₁ * v₂) ^ 2
      + (u₁ * v₁ * u₂ * v₁ - S) ^ 2 + (u₁ * v₁ * u₂ * v₂) ^ 2 := by
  have hC1 : 0 ≤ 1 - C := by nlinarith [sq_nonneg S]
  have hC2 : 0 ≤ 1 + C := by nlinarith [sq_nonneg S]
  have hw : 0 ≤ 1 - v₁ ^ 2 := by nlinarith [sq_nonneg v₂]
  have hid : (u₁ * v₁ * u₁ * v₁ - C) ^ 2 + (u₁ * v₁ * u₁ * v₂) ^ 2
      + (u₁ * v₁ * u₂ * v₁ - S) ^ 2 + (u₁ * v₁ * u₂ * v₂) ^ 2
      = 1 + v₁ ^ 2 * (u₁ ^ 2 - 2 * u₁ ^ 2 * C - 2 * u₁ * u₂ * S) := by
    linear_combination (u₁ * v₁) ^ 2 * (v₁ ^ 2 + v₂ ^ 2) * hu + (u₁ * v₁) ^ 2 * hv + hc
  have hab : (u₁ ^ 2 - 1 / 2) ^ 2 + (u₁ * u₂) ^ 2 = 1 / 4 := by
    linear_combination u₁ ^ 2 * hu
  have hpq : (1 - 2 * C) ^ 2 + (2 * S) ^ 2 = 5 - 4 * C := by linear_combination 4 * hc
  have hcs : ((u₁ ^ 2 - 1 / 2) * (1 - 2 * C) - 2 * (u₁ * u₂) * S) ^ 2
      + ((u₁ ^ 2 - 1 / 2) * (2 * S) + u₁ * u₂ * (1 - 2 * C)) ^ 2
      = ((u₁ ^ 2 - 1 / 2) ^ 2 + (u₁ * u₂) ^ 2) * ((1 - 2 * C) ^ 2 + (2 * S) ^ 2) := by ring
  rw [hab, hpq] at hcs
  have hbr : ((u₁ ^ 2 - 1 / 2) * (1 - 2 * C) - 2 * (u₁ * u₂) * S) ^ 2 ≤ (5 - 4 * C) / 4 := by
    nlinarith [sq_nonneg ((u₁ ^ 2 - 1 / 2) * (2 * S) + u₁ * u₂ * (1 - 2 * C))]
  have hK0 : 0 ≤ 3 / 2 - C - (1 - C) ^ 2 / 4 := by nlinarith [mul_nonneg hC1 hC2]
  have hK2 : (5 - 4 * C) / 4 ≤ (3 / 2 - C - (1 - C) ^ 2 / 4) ^ 2 := by
    have e : (3 / 2 - C - (1 - C) ^ 2 / 4) ^ 2 - (5 - 4 * C) / 4
        = (1 - C) ^ 2 * (1 + C) * (5 + C) / 16 := by ring
    have hp : 0 ≤ (1 - C) ^ 2 * (1 + C) * (5 + C) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hC2) (by linarith)
    linarith
  have habs := abs_le_of_sq_le_sq' (hbr.trans hK2) hK0
  have hone : 0 ≤ 1 + (u₁ ^ 2 - 2 * u₁ ^ 2 * C - 2 * u₁ * u₂ * S) - (1 - C) ^ 2 / 4 := by
    have e : 1 + (u₁ ^ 2 - 2 * u₁ ^ 2 * C - 2 * u₁ * u₂ * S) - (1 - C) ^ 2 / 4
        = (3 / 2 - C - (1 - C) ^ 2 / 4)
          + ((u₁ ^ 2 - 1 / 2) * (1 - 2 * C) - 2 * (u₁ * u₂) * S) := by ring
    rw [e]
    linarith [habs.1]
  have hx : 0 ≤ 1 - (1 - C) ^ 2 / 4 := by nlinarith [mul_nonneg hC1 hC2]
  rw [hid]
  nlinarith [mul_nonneg (sq_nonneg v₁) hone, mul_nonneg hw hx]

/-- The squared distance of `u uᵀ Y₀ v vᵀ` from `C Y₀ + S W Y₀`, entry by entry. -/
private theorem norm_sq_galerkinProj_rotStart_sub (U V : Matrix (Fin 2) (Fin 1) ℝ) (C S : ℝ) :
    ‖galerkinProj U V rotStart - (C • rotStart + S • rotVelocity)‖ ^ 2
      = (U 0 0 * V 0 0 * U 0 0 * V 0 0 - C) ^ 2 + (U 0 0 * V 0 0 * U 0 0 * V 1 0) ^ 2
        + (U 0 0 * V 0 0 * U 1 0 * V 0 0 - S) ^ 2 + (U 0 0 * V 0 0 * U 1 0 * V 1 0) ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  simp [Fin.sum_univ_two, galerkinProj_apply, Matrix.mul_apply, rotStart, rotVelocity]
  ring

/-- **No Galerkin step in a fixed rank-one space is of second order.**  For the rotation field
`F(Y) = W Y` (tangent to the rank-one matrices) and `Y₀ = e₁ e₁ᵀ`, every Galerkin step in a
space `{s u vᵀ}` with orthonormal `u`, `v`, that is, every solution of
`Ŷ' = u uᵀ (W Ŷ) v vᵀ`, `Ŷ(0) = u uᵀ Y₀ v vᵀ`, has the error

    ‖Ŷ(h) - A(h)‖ ≥ (1 - cos h) / 2,

whatever `u` and `v` are (they may depend on `h`, and on the exact solution). -/
theorem error_ge_of_rankOne_galerkin (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {h : ℝ} (hh : 0 ≤ h)
    {YS : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hS : ODESolution (fun _ Y => galerkinProj U V (rotGen * Y)) YS 0 h)
    (hS₀ : YS 0 = galerkinProj U V rotStart) :
    (1 - Real.cos h) / 2 ≤ ‖YS h - rotSolution h‖ := by
  have hu : U 0 0 * U 0 0 + U 1 0 * U 1 0 = 1 := by
    have := congrFun (congrFun hU 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hv : V 0 0 * V 0 0 + V 1 0 * V 1 0 = 1 := by
    have := congrFun (congrFun hV 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hsq : ((1 - Real.cos h) / 2) ^ 2 ≤ ‖YS h - rotSolution h‖ ^ 2 := by
    rw [galerkin_eq_start_of_rankOne hU hV hh hS hS₀, rotSolution,
      norm_sq_galerkinProj_rotStart_sub]
    exact rankOne_sq_ge hu hv (Real.cos_sq_add_sin_sq h)
  have h0 : 0 ≤ (1 - Real.cos h) / 2 := by linarith [Real.cos_le_one h]
  exact (pow_le_pow_iff_left₀ h0 (norm_nonneg _) two_ne_zero).1 hsq

/-- The lower bound of `error_ge_of_rankOne_galerkin` in powers of the step size:
`‖Ŷ(h) - A(h)‖ ≥ h² / π²` for `0 ≤ h ≤ π`.  The local error of a method of second order is
`O(h³)`. -/
theorem sq_div_le_error_of_rankOne_galerkin (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {h : ℝ}
    (hh : 0 ≤ h) (hπ : h ≤ Real.pi) {YS : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hS : ODESolution (fun _ Y => galerkinProj U V (rotGen * Y)) YS 0 h)
    (hS₀ : YS 0 = galerkinProj U V rotStart) :
    h ^ 2 / Real.pi ^ 2 ≤ ‖YS h - rotSolution h‖ := by
  have h1 := Real.cos_le_one_sub_mul_cos_sq (x := h) (by rw [abs_of_nonneg hh]; exact hπ)
  have h2 := error_ge_of_rankOne_galerkin hU hV hh hS hS₀
  have e : h ^ 2 / Real.pi ^ 2 = 2 / Real.pi ^ 2 * h ^ 2 / 2 := by ring
  rw [e]
  linarith

/-- Non-vacuity of `error_ge_of_rankOne_galerkin` and `sq_div_le_error_of_rankOne_galerkin`: the
space spanned by `e₁ e₁ᵀ` (`u = v = e₁`), in which the Galerkin step exists
(`odeSolution_const_of_rankOne`). -/
example (h : ℝ) (hh : 0 ≤ h) (hπ : h ≤ Real.pi) :
    (1 - Real.cos h) / 2 ≤ ‖galerkinProj startRight startRight rotStart - rotSolution h‖ ∧
      h ^ 2 / Real.pi ^ 2 ≤ ‖galerkinProj startRight startRight rotStart - rotSolution h‖ :=
  ⟨error_ge_of_rankOne_galerkin (YS := fun _ => galerkinProj startRight startRight rotStart)
      startRight_orth startRight_orth hh (odeSolution_const_of_rankOne _ _ _ h) rfl,
    sq_div_le_error_of_rankOne_galerkin
      (YS := fun _ => galerkinProj startRight startRight rotStart) startRight_orth
      startRight_orth hh hπ (odeSolution_const_of_rankOne _ _ _ h) rfl⟩

end RankOne

end AugmentationRank

end LeanDLRA
