import LeanDLRA.DLRA.QuasiOptimalityNormal
import LeanDLRA.DLRA.QuasiOptimalityTimeLocal

/-!
# The speed and velocity bounds of a curve of critical points are attained

For a curve `X` of critical points of rank `r` of the distance to `A` (`P(X) (A - X) = 0`), with
`0 < ρ ≤ σ_r(X)`, `‖Ȧ‖ ≤ μ` and the margin `‖X - A‖ ≤ θ ρ`, `θ < 1`, the file
`LeanDLRA/DLRA/QuasiOptimalityNormal.lean` proves

  `‖P(X) (Ȧ - Ẋ)‖ ≤ ρ⁻¹ ‖Ẋ‖ ‖A - X‖`,   `‖Ẋ‖ ≤ μ / (1 - θ)`,
  `‖Ẋ - P(X) Ȧ‖ ≤ μ / ((1 - θ) ρ) ‖A - X‖`.

This file shows that the three bounds are equalities, for every `θ` with `0 ≤ θ < 1` and at every
time, for the rotating projector of rank one in `ℝ²`,

  `X t = u(t) u(t)ᵀ`,   `A t = θ • 1 + (1 - θ) • X t`,   `u(t) = (cos t, sin t)`,

with `r = 1`, `ρ = 1`, `μ = (1 - θ) √2`: here `‖A - X‖ = θ`, `Ȧ = (1 - θ) Ẋ` and `‖Ẋ‖ = √2`.

## Main results

* `QuasiOptimalitySpeedExample.hypotheses`: the hypotheses of the three bounds for the family.
* `QuasiOptimalitySpeedExample.norm_rotProjDeriv_eq_div`: `‖Ẋ‖ = μ / (1 - θ)`.
* `QuasiOptimalitySpeedExample.norm_sub_tangentProjAt_eq`:
  `‖Ẋ - P(X) Ȧ‖ = μ / ((1 - θ) ρ) ‖A - X‖`.
* `QuasiOptimalitySpeedExample.norm_tangentProjAt_sub_eq`:
  `‖P(X) (Ȧ - Ẋ)‖ = ρ⁻¹ ‖Ẋ‖ ‖A - X‖`.
* `QuasiOptimalitySpeedExample.specNorm_rotData_sub`: `‖A - X‖₂ = θ`, so that the bounds with
  the spectral norm of the tail, `norm_le_div_one_sub_of_specNorm_sub_le`,
  `norm_sub_tangentProjAt_le_div_one_sub_mul_specNorm` and
  `norm_sub_tangentProjAt_le_div_sub_mul_specNorm`, are equalities for the family as well.
* `exists_mul_div_lt_norm_deriv`: for `0 ≤ θ < 1` and `c < 1` there are curves that satisfy the
  hypotheses of `norm_le_div_one_sub_of_tangentProjAt_sub_eq_zero` with `μ > 0` and
  `c μ / (1 - θ) < ‖Ẋ‖`.

## Implementation notes

The tail `A - X = θ (1 - u uᵀ)` has the singular value `θ`, and `X` has the singular value `1`:
the margin `θ < 1` is the gap condition, and at `θ = 1` the data `A = 1` do not move while `X`
does. The `example`s apply the theorems of the library to the family. The quasi-optimality
bounds that are derived from the velocity bound with Grönwall's inequality are not shown to be
attained.
-/

open Set Matrix Filter
open scoped Topology

namespace LeanDLRA

namespace QuasiOptimalitySpeedExample

open scoped LeanDLRA.Frobenius

/-- The unit column `u(t) = (cos t, sin t)`. -/
noncomputable def rotCol (t : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := !![Real.cos t; Real.sin t]

/-- The projector `X t = u(t) u(t)ᵀ` of rank one. -/
noncomputable def rotProj (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := rotCol t * (rotCol t)ᵀ

/-- The derivative of `rotProj`. -/
noncomputable def rotProjDeriv (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-(2 * Real.cos t * Real.sin t), Real.cos t ^ 2 - Real.sin t ^ 2;
    Real.cos t ^ 2 - Real.sin t ^ 2, 2 * Real.cos t * Real.sin t]

/-- The data `A t = θ • 1 + (1 - θ) • X t`. -/
noncomputable def rotData (θ t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  θ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (1 - θ) • rotProj t

/-- `u(t)ᵀ u(t) = 1`. -/
theorem rotCol_transpose_mul_self (t : ℝ) : (rotCol t)ᵀ * rotCol t = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp only [rotCol, Matrix.mul_apply, Fin.sum_univ_two]
  simp
  nlinarith [Real.cos_sq_add_sin_sq t]

/-- `X t = u(t) 1 u(t)ᵀ`: a factorization with the `1 × 1` core `1`. -/
theorem rotProj_eq (t : ℝ) :
    rotProj t = rotCol t * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (rotCol t)ᵀ := by
  rw [Matrix.mul_one, rotProj]

/-- The entries of `X t`. -/
theorem rotProj_eq_of (t : ℝ) :
    rotProj t = !![Real.cos t ^ 2, Real.cos t * Real.sin t;
      Real.cos t * Real.sin t, Real.sin t ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotProj, rotCol, Matrix.mul_apply, pow_two, mul_comm]

/-- `X t` is idempotent. -/
theorem rotProj_mul_self (t : ℝ) : rotProj t * rotProj t = rotProj t := by
  simp only [rotProj]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (rotCol t)ᵀ, rotCol_transpose_mul_self, Matrix.one_mul]

/-- `X t` has rank `1`. -/
theorem rank_rotProj (t : ℝ) : (rotProj t).rank = 1 :=
  (SVD.rank_eq_iff_exists_factor _).2 ⟨rotCol t, 1, rotCol t, rotCol_transpose_mul_self t,
    rotCol_transpose_mul_self t, by simp, rotProj_eq t⟩

/-- `σ₀(X t) ≥ 1`. -/
theorem one_le_singularValues_rotProj (t : ℝ) :
    (1 : ℝ) ≤ (toEuclideanLin (rotProj t)).singularValues (1 - 1) := by
  refine SVD.le_singularValues_of_eq_mul one_pos (rotCol_transpose_mul_self t)
    (rotCol_transpose_mul_self t) (rotProj_eq t) fun w => ?_
  rw [toLpLin_one]
  simp

/-- The tangent projector at `X t`: `P(X) Z = X Z + Z X - X Z X`. -/
theorem tangentProjAt_rotProj (t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    tangentProjAt (rotProj t) Z = rotProj t * Z + Z * rotProj t - rotProj t * Z * rotProj t := by
  have h := tangentProjAt_eq_tangentProj (S := (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (rotCol_transpose_mul_self t) (rotCol_transpose_mul_self t) (by simp)
  rw [← rotProj_eq] at h
  rw [h, tangentProj_apply]
  simp only [rotProj, Matrix.mul_assoc]

/-- The tail `A t - X t = θ (1 - X t)` is normal at `X t`. -/
theorem tangentProjAt_rotData_sub (θ t : ℝ) :
    tangentProjAt (rotProj t) (rotData θ t - rotProj t) = 0 := by
  have e : rotData θ t - rotProj t = θ • (1 - rotProj t) := by
    simp only [rotData]
    module
  have h1 : rotProj t * (θ • (1 - rotProj t)) = 0 := by
    rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, rotProj_mul_self, sub_self, smul_zero]
  have h2 : (θ • (1 - rotProj t)) * rotProj t = 0 := by
    rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, rotProj_mul_self, sub_self, smul_zero]
  rw [e, tangentProjAt_rotProj, h1, h2, Matrix.zero_mul]
  simp

/-- The derivative of `X`. -/
theorem hasDerivAt_rotProj (t : ℝ) : HasDerivAt rotProj (rotProjDeriv t) t := by
  have e : rotProj = fun s : ℝ =>
      (Real.cos s ^ 2) • (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
        + (Real.cos s * Real.sin s) • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)
        + (Real.sin s ^ 2) • (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
    funext s
    rw [rotProj_eq_of]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hc := Real.hasDerivAt_cos t
  have hs := Real.hasDerivAt_sin t
  have h := (((hc.pow 2).smul_const (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)).add
    ((hc.mul hs).smul_const (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ))).add
    ((hs.pow 2).smul_const (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ))
  rw [e]
  convert h using 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotProjDeriv] <;> ring

/-- The derivative of `A`: `Ȧ = (1 - θ) Ẋ`. -/
theorem hasDerivAt_rotData (θ t : ℝ) :
    HasDerivAt (rotData θ) ((1 - θ) • rotProjDeriv t) t :=
  ((hasDerivAt_rotProj t).const_smul (1 - θ)).const_add (θ • (1 : Matrix (Fin 2) (Fin 2) ℝ))

/-- `‖Ẋ‖ = √2`. -/
theorem norm_rotProjDeriv (t : ℝ) : ‖rotProjDeriv t‖ = √2 := by
  have h : ‖rotProjDeriv t‖ ^ 2 = 2 := by
    rw [Curvature.frob_sq]
    simp only [rotProjDeriv, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have h1 := Real.cos_sq_add_sin_sq t
    have e : (-(2 * Real.cos t * Real.sin t)) ^ 2 + (Real.cos t ^ 2 - Real.sin t ^ 2) ^ 2
        + ((Real.cos t ^ 2 - Real.sin t ^ 2) ^ 2 + (2 * Real.cos t * Real.sin t) ^ 2) =
        2 * (Real.cos t ^ 2 + Real.sin t ^ 2) ^ 2 := by ring
    rw [e, h1]
    norm_num
  rw [← Real.sqrt_sq (norm_nonneg (rotProjDeriv t)), h]

/-- `‖1 - X t‖ = 1`. -/
theorem norm_one_sub_rotProj (t : ℝ) : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ) - rotProj t‖ = 1 := by
  have h : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ) - rotProj t‖ ^ 2 = 1 := by
    rw [Curvature.frob_sq, rotProj_eq_of]
    simp only [Fin.sum_univ_two, Matrix.sub_apply, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, zero_ne_one,
      one_ne_zero, not_false_eq_true, Fin.isValue]
    have h1 := Real.cos_sq_add_sin_sq t
    have e : (1 - Real.cos t ^ 2) ^ 2 + (0 - Real.cos t * Real.sin t) ^ 2
        + ((0 - Real.cos t * Real.sin t) ^ 2 + (1 - Real.sin t ^ 2) ^ 2) =
        (1 - (Real.cos t ^ 2 + Real.sin t ^ 2)) ^ 2 + 1 := by ring
    rw [e, h1]
    norm_num
  rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_one]

/-- `‖A t - X t‖ = θ` for `θ ≥ 0`. -/
theorem norm_rotData_sub {θ : ℝ} (hθ : 0 ≤ θ) (t : ℝ) : ‖rotData θ t - rotProj t‖ = θ := by
  have e : rotData θ t - rotProj t = θ • (1 - rotProj t) := by
    simp only [rotData]
    module
  rw [e, norm_smul, norm_one_sub_rotProj, mul_one, Real.norm_eq_abs, abs_of_nonneg hθ]

/-- `Ẋ` is tangent at `X t`. -/
theorem tangentProjAt_rotProjDeriv (t : ℝ) :
    tangentProjAt (rotProj t) (rotProjDeriv t) = rotProjDeriv t := by
  have hs : (𝓝[univ \ {t}] t).NeBot := by
    rw [← compl_eq_univ_sdiff]
    infer_instance
  exact tangentProjAt_eq_self_iff.mpr (mem_tangentSpaceAt_of_hasDerivWithinAt (r := 1)
    (hasDerivAt_rotProj t).hasDerivWithinAt (mem_univ t) hs one_pos (fun u _ => rank_rotProj u)
    (fun u _ => one_le_singularValues_rotProj u))

/-- **The hypotheses of the speed and velocity bounds for the rotating projector**, on `univ`
with `r = 1`, `ρ = 1`, `μ = (1 - θ) √2` and the margin `θ`. -/
theorem hypotheses {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1) (t : ℝ) :
    HasDerivWithinAt (rotData θ) ((1 - θ) • rotProjDeriv t) univ t ∧
      HasDerivWithinAt rotProj (rotProjDeriv t) univ t ∧ (𝓝[univ \ {t}] t).NeBot ∧
      (∀ u ∈ (univ : Set ℝ), (rotProj u).rank = 1) ∧
      (∀ u ∈ (univ : Set ℝ), (1 : ℝ) ≤ (toEuclideanLin (rotProj u)).singularValues (1 - 1)) ∧
      (∀ u ∈ (univ : Set ℝ), tangentProjAt (rotProj u) (rotData θ u - rotProj u) = 0) ∧
      ‖(1 - θ) • rotProjDeriv t‖ ≤ (1 - θ) * √2 ∧ ‖rotProj t - rotData θ t‖ ≤ θ * 1 := by
  refine ⟨(hasDerivAt_rotData θ t).hasDerivWithinAt, (hasDerivAt_rotProj t).hasDerivWithinAt, ?_,
    fun u _ => rank_rotProj u, fun u _ => one_le_singularValues_rotProj u,
    fun u _ => tangentProjAt_rotData_sub θ u, ?_, ?_⟩
  · rw [← compl_eq_univ_sdiff]
    infer_instance
  · rw [norm_smul, norm_rotProjDeriv, Real.norm_eq_abs, abs_of_pos (by linarith)]
  · rw [norm_sub_rev, norm_rotData_sub hθ0, mul_one]

/-- **The speed bound is attained:** `‖Ẋ‖ = μ / (1 - θ)` with `μ = (1 - θ) √2`. -/
theorem norm_rotProjDeriv_eq_div {θ : ℝ} (hθ : θ < 1) (t : ℝ) :
    ‖rotProjDeriv t‖ = (1 - θ) * √2 / (1 - θ) := by
  have h : (1 - θ) ≠ 0 := by linarith
  rw [norm_rotProjDeriv, mul_div_cancel_left₀ _ h]

/-- **The velocity bound is attained:** `‖Ẋ - P(X) Ȧ‖ = μ / ((1 - θ) ρ) ‖A - X‖` with
`μ = (1 - θ) √2` and `ρ = 1`; both sides are `√2 θ`. -/
theorem norm_sub_tangentProjAt_eq {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1) (t : ℝ) :
    ‖rotProjDeriv t - tangentProjAt (rotProj t) ((1 - θ) • rotProjDeriv t)‖ =
      (1 - θ) * √2 / ((1 - θ) * 1) * ‖rotData θ t - rotProj t‖ := by
  have h : (1 - θ) ≠ 0 := by linarith
  have e : rotProjDeriv t - tangentProjAt (rotProj t) ((1 - θ) • rotProjDeriv t) =
      θ • rotProjDeriv t := by
    rw [map_smul, tangentProjAt_rotProjDeriv]
    module
  rw [e, norm_smul, norm_rotProjDeriv, norm_rotData_sub hθ0, Real.norm_eq_abs,
    abs_of_nonneg hθ0, mul_one, mul_div_cancel_left₀ _ h]
  ring

/-- **The differentiated first-order condition is attained:**
`‖P(X) (Ȧ - Ẋ)‖ = ρ⁻¹ ‖Ẋ‖ ‖A - X‖` with `ρ = 1`; both sides are `√2 θ`. -/
theorem norm_tangentProjAt_sub_eq {θ : ℝ} (hθ0 : 0 ≤ θ) (t : ℝ) :
    ‖tangentProjAt (rotProj t) ((1 - θ) • rotProjDeriv t - rotProjDeriv t)‖ =
      (1 : ℝ)⁻¹ * ‖rotProjDeriv t‖ * ‖rotData θ t - rotProj t‖ := by
  have e : (1 - θ) • rotProjDeriv t - rotProjDeriv t = (-θ) • rotProjDeriv t := by module
  rw [e, map_smul, tangentProjAt_rotProjDeriv, norm_smul, norm_rotProjDeriv,
    norm_rotData_sub hθ0, Real.norm_eq_abs, abs_neg, abs_of_nonneg hθ0]
  ring

/-- `norm_le_div_one_sub_of_tangentProjAt_sub_eq_zero`,
`norm_sub_tangentProjAt_le_div_one_sub_of_tangentProjAt_sub_eq_zero` and
`norm_tangentProjAt_sub_le_inv_mul_of_hasDerivWithinAt` apply to the family. By
`norm_rotProjDeriv_eq_div`, `norm_sub_tangentProjAt_eq` and `norm_tangentProjAt_sub_eq` the
three inequalities are equalities. -/
example {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1) (t : ℝ) :
    ‖rotProjDeriv t‖ ≤ (1 - θ) * √2 / (1 - θ) ∧
      ‖rotProjDeriv t - tangentProjAt (rotProj t) ((1 - θ) • rotProjDeriv t)‖ ≤
        (1 - θ) * √2 / ((1 - θ) * 1) * ‖rotData θ t - rotProj t‖ ∧
      ‖tangentProjAt (rotProj t) ((1 - θ) • rotProjDeriv t - rotProjDeriv t)‖ ≤
        (1 : ℝ)⁻¹ * ‖rotProjDeriv t‖ * ‖rotData θ t - rotProj t‖ := by
  obtain ⟨hA, hX, hs, hr, hσ, ho, hμ, hd⟩ := hypotheses hθ0 hθ t
  exact ⟨norm_le_div_one_sub_of_tangentProjAt_sub_eq_zero hA hX (mem_univ t) hs one_pos hr hσ ho
      hμ hθ hd,
    norm_sub_tangentProjAt_le_div_one_sub_of_tangentProjAt_sub_eq_zero hA hX (mem_univ t) hs
      one_pos hr hσ ho hμ hθ hd,
    norm_tangentProjAt_sub_le_inv_mul_of_hasDerivWithinAt hA hX (mem_univ t) hs one_pos hr
      (hσ t (mem_univ t)) ho⟩

/-- **The spectral norm of the tail is `θ`.** The upper bound is the Frobenius norm, and the
lower bound is the velocity bound `norm_sub_tangentProjAt_le_div_one_sub_mul_specNorm` for the
family, whose left-hand side is `√2 θ`. -/
theorem specNorm_rotData_sub {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1) (t : ℝ) :
    Curvature.specNorm (rotData θ t - rotProj t) = θ := by
  obtain ⟨hA, hX, hs, hr, hσ, ho, hμ, hd⟩ := hypotheses hθ0 hθ t
  have hup : Curvature.specNorm (rotData θ t - rotProj t) ≤ θ :=
    (Curvature.specNorm_le_frob _).trans_eq (norm_rotData_sub hθ0 t)
  have hd' : Curvature.specNorm (rotProj t - rotData θ t) ≤ θ * 1 := by
    rw [Curvature.specNorm_sub_comm, mul_one]
    exact hup
  have h := norm_sub_tangentProjAt_le_div_one_sub_mul_specNorm hA hX (mem_univ t) hs one_pos hr hσ
    ho hμ hθ hd'
  have h1θ : (1 - θ) ≠ 0 := by linarith
  have e : rotProjDeriv t - tangentProjAt (rotProj t) ((1 - θ) • rotProjDeriv t) =
      θ • rotProjDeriv t := by
    rw [map_smul, tangentProjAt_rotProjDeriv]
    module
  rw [e, norm_smul, norm_rotProjDeriv, Real.norm_eq_abs, abs_of_nonneg hθ0, mul_one,
    mul_div_cancel_left₀ _ h1θ] at h
  have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.2 zero_lt_two
  have h3 : θ ≤ Curvature.specNorm (rotData θ t - rotProj t) := by
    by_contra hlt
    have hlt' := not_le.mp hlt
    nlinarith
  exact le_antisymm hup h3

/-- **The velocity bound with the constants at one time is attained:**
`‖Ẋ - P(X) Ȧ‖ = μ / (ρ - ‖X - A‖₂) ‖X - A‖₂` for the family; both sides are `√2 θ`. The
theorem `norm_sub_tangentProjAt_le_div_sub_mul_specNorm` applies with `ρ₀ = ρ = 1`. -/
theorem norm_sub_tangentProjAt_eq_div_sub_mul_specNorm {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (t : ℝ) :
    ‖rotProjDeriv t - tangentProjAt (rotProj t) ((1 - θ) • rotProjDeriv t)‖ =
      (1 - θ) * √2 / (1 - Curvature.specNorm (rotProj t - rotData θ t)) *
        Curvature.specNorm (rotProj t - rotData θ t) := by
  rw [Curvature.specNorm_sub_comm, specNorm_rotData_sub hθ0 hθ, norm_sub_tangentProjAt_eq hθ0 hθ,
    norm_rotData_sub hθ0, mul_one]

example {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1) (t : ℝ) :
    ‖rotProjDeriv t - tangentProjAt (rotProj t) ((1 - θ) • rotProjDeriv t)‖ ≤
      (1 - θ) * √2 / (1 - Curvature.specNorm (rotProj t - rotData θ t)) *
        Curvature.specNorm (rotProj t - rotData θ t) := by
  obtain ⟨hA, hX, hs, hr, hσ, ho, hμ, -⟩ := hypotheses hθ0 hθ t
  refine norm_sub_tangentProjAt_le_div_sub_mul_specNorm hA hX (mem_univ t) hs one_pos hr hσ
    (hσ t (mem_univ t)) ho hμ ?_
  rw [Curvature.specNorm_sub_comm, specNorm_rotData_sub hθ0 hθ]
  exact hθ

end QuasiOptimalitySpeedExample

open QuasiOptimalitySpeedExample in
open scoped LeanDLRA.Frobenius in
/-- **The speed bound `‖Ẋ‖ ≤ μ / (1 - θ)` cannot be improved.** For every margin `θ` with
`0 ≤ θ < 1` and every `c < 1` there are curves `A`, `X` of `2 × 2` matrices that satisfy the
hypotheses of `norm_le_div_one_sub_of_tangentProjAt_sub_eq_zero` at `t = 0` within `univ`, with
`r = 1`, `ρ = 1` and a bound `μ > 0` of `‖Ȧ‖`, such that `c μ / (1 - θ) < ‖Ẋ‖`. -/
theorem exists_mul_div_lt_norm_deriv {θ c : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1) (hc : c < 1) :
    ∃ (A X : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (A' X' : Matrix (Fin 2) (Fin 2) ℝ) (μ : ℝ),
      0 < μ ∧ HasDerivWithinAt A A' univ 0 ∧ HasDerivWithinAt X X' univ 0 ∧
        (∀ u ∈ (univ : Set ℝ), (X u).rank = 1) ∧
        (∀ u ∈ (univ : Set ℝ), (1 : ℝ) ≤ (toEuclideanLin (X u)).singularValues (1 - 1)) ∧
        (∀ u ∈ (univ : Set ℝ), tangentProjAt (X u) (A u - X u) = 0) ∧ ‖A'‖ ≤ μ ∧
        ‖X 0 - A 0‖ ≤ θ * 1 ∧ c * (μ / (1 - θ)) < ‖X'‖ := by
  obtain ⟨hA, hX, -, hr, hσ, ho, hμ, hd⟩ := hypotheses hθ0 hθ 0
  have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.2 zero_lt_two
  refine ⟨rotData θ, rotProj, _, _, (1 - θ) * √2, mul_pos (by linarith) h2, hA, hX, hr, hσ, ho,
    hμ, hd, ?_⟩
  rw [← norm_rotProjDeriv_eq_div hθ 0, norm_rotProjDeriv]
  nlinarith

end LeanDLRA
