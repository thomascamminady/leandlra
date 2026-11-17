import LeanDLRA.Integrators.Matrix.FactoredNormalBound
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Integrators.Matrix.BUG

/-!
# The capture defect of the explicit midpoint step

From the factored point `Y₀ = U₀ S₀ V₀ᵀ` the explicit midpoint step evaluates the field at the
predictor `Z = Y₀ + (h/2) P₀ F(t₀, Y₀)`, `P₀ = tangentProj U₀ V₀`, and augments the left basis
by `G V₀`, `G = F(t₀ + h/2, Z)`. This file bounds the capture defect

`θ = ‖(1 - Û Ûᵀ) G (1 - V₀ V₀ᵀ)‖`

of every orthonormal `Û` whose range contains those of `U₀` and `G V₀`. The general bound
(`norm_capture_defect_le`) has free parameters `τ > 0`, `κ`, `e`, `δ`; the choice `τ = h² + ε`
gives `θ ≤ C₁ h² + C₂ ε` for `0 < h ≤ H` (`norm_capture_defect_le_sq_add`), with explicit
constants that contain the norm of `S₀` but no inverse of `S₀`: they do not depend on the small
singular values of `S₀`. The same holds for the capture defect on the right,
`θ' = ‖(1 - U₀ U₀ᵀ) G (1 - Va Vaᵀ)‖` (`norm_capture_defect_right_le_sq_add`).

The capture defects bounded here are the parameters `θ`, `θ'` of the local error bounds of
`LeanDLRA.Research.ExplicitMidpointGalerkin`; for the explicit update the two are combined there
(`ExplicitMidpoint.norm_update_sub_le_cube_add`).

## Main statements

* `LeanDLRA.norm_sq_eq_sum_norm_mul_single`: the squared Frobenius norm is the sum of the
  squared norms of the columns.
* `LeanDLRA.mul_inv_mul_transpose_mul_add`, `LeanDLRA.norm_mul_inv_mul_transpose_le`,
  `LeanDLRA.norm_smul_mul_inv_le`: a matrix `K` whose columns satisfy
  `‖K c‖ ≤ ε ‖c‖ + L ‖S c‖` factors as `K = K' S + E` with `‖K'‖ ≤ √r (ε/(2τ) + L)` and
  `‖E‖ ≤ √r (ε + L τ/2)`, for every `τ > 0`; `K' = K Γ⁻¹ Sᵀ`, `E = τ² K Γ⁻¹`,
  `Γ = Sᵀ S + τ² 1`. No singular value decomposition is used.
* `LeanDLRA.norm_normal_mul_field_mul_le_of_ball`,
  `LeanDLRA.norm_transpose_mul_field_mul_normal_le_of_ball`: the mixed components of the field
  with the Lipschitz constant `max L (2B/ρ)` when only the ball of radius `ρ/2` around the
  factored point lies in the region.
* `LeanDLRA.norm_one_sub_mul_mul_mul_one_sub_le`: at a factored point `W = Ut S_W Vtᵀ`, the part of
  the mixed component `Ut Utᵀ F(t, W) (1 - Vt Vtᵀ)` outside the range of another basis `Û` is at
  most `κ ‖(1 - Û Ûᵀ) W‖ + e`.
* `LeanDLRA.norm_capture_defect_le`, `LeanDLRA.norm_capture_defect_right_le`: the bound of the
  capture defects in the free parameters `τ`, `κ`, `e`, `δ`.
* `LeanDLRA.norm_capture_defect_le_sq_add`, `LeanDLRA.norm_capture_defect_right_le_sq_add`:
  with `τ = h² + ε`, the capture defects are at most `C₁ h² + C₂ ε`.

## Implementation notes

The splitting `K = K' S + E` replaces a singular value decomposition of `S` with a threshold
(the usual pen-and-paper route to such bounds) by the regularized inverse `(Sᵀ S + τ² 1)⁻¹`; the
bounds follow from the identity `‖S D‖² + τ² ‖D‖² = ⟪D, (Sᵀ S + τ² 1) D⟫`. All norms are
Frobenius norms, so the constants carry factors `√r` that bounds in the spectral norm would not
have.

## References

* [CerutiEtAl2024b] (the second-order BUG integrator based on the midpoint rule).
-/

open Set
open scoped Matrix LeanDLRA.Frobenius RealInnerProductSpace

namespace LeanDLRA

/-! ### Columns -/

section Columns

variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq q]

/-- The squared Frobenius norm is the sum of the squared norms of the columns `M eⱼ`, with the
unit columns `eⱼ = Matrix.single j 0 1`. -/
theorem norm_sq_eq_sum_norm_mul_single (M : Matrix p q ℝ) :
    ‖M‖ ^ 2 = ∑ j, ‖M * (Matrix.single j 0 1 : Matrix q (Fin 1) ℝ)‖ ^ 2 := by
  have h : ∀ j, ‖M * (Matrix.single j 0 1 : Matrix q (Fin 1) ℝ)‖ ^ 2 = ∑ i, M i j ^ 2 :=
      fun j => by
    rw [Frobenius.norm_sq_eq_sum]
    simp
  rw [Finset.sum_congr rfl fun j _ => h j, Frobenius.norm_sq_eq_sum, Finset.sum_comm]

/-- A unit column has norm one. -/
theorem norm_single_one (j : q) : ‖(Matrix.single j 0 1 : Matrix q (Fin 1) ℝ)‖ = 1 := by
  have h1 : ‖(Matrix.single j 0 1 : Matrix q (Fin 1) ℝ)‖ ^ 2 = 1 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp only [Fin.sum_univ_one]
    simp [Matrix.single_apply]
  nlinarith [norm_nonneg (Matrix.single j 0 1 : Matrix q (Fin 1) ℝ)]

/-- Bounds of the columns give a bound of the Frobenius norm. -/
theorem norm_le_sqrt_card_mul_of_forall_mul_single_le {M : Matrix p q ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j, ‖M * (Matrix.single j 0 1 : Matrix q (Fin 1) ℝ)‖ ≤ c) :
    ‖M‖ ≤ Real.sqrt (Fintype.card q) * c := by
  have hsq : ‖M‖ ^ 2 ≤ (Real.sqrt (Fintype.card q) * c) ^ 2 := by
    rw [norm_sq_eq_sum_norm_mul_single, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    calc ∑ j, ‖M * (Matrix.single j 0 1 : Matrix q (Fin 1) ℝ)‖ ^ 2 ≤ ∑ _j : q, c ^ 2 :=
          Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (h j) 2
      _ = (Fintype.card q) * c ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

end Columns

/-! ### The regularized splitting `K = K' S + E` -/

section Tikhonov

variable {p : Type*} [Fintype p] {r : ℕ}

/-- `Sᵀ S + τ² 1` is invertible for `τ ≠ 0`. -/
theorem isUnit_transpose_mul_self_add_smul_one (S : Matrix p (Fin r) ℝ) {τ : ℝ} (hτ : τ ≠ 0) :
    IsUnit (Sᵀ * S + τ ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ)) := by
  have h1 : (Sᵀ * S).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self S
  exact (Matrix.PosDef.posSemidef_add h1 (Matrix.PosDef.one.smul (by positivity))).isUnit

/-- The energy identity of the regularized normal equations: if `(Sᵀ S + τ² 1) D = B`, then
`‖S D‖² + τ² ‖D‖² = ⟪D, B⟫`. -/
theorem norm_sq_add_sq_mul_norm_sq_eq_inner (S : Matrix p (Fin r) ℝ) (τ : ℝ) {q : Type*}
    [Fintype q] {D B : Matrix (Fin r) q ℝ}
    (hD : (Sᵀ * S + τ ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ)) * D = B) :
    ‖S * D‖ ^ 2 + τ ^ 2 * ‖D‖ ^ 2 = ⟪D, B⟫ := by
  rw [← hD, Matrix.add_mul, inner_add_right, Matrix.smul_mul, Matrix.one_mul,
    real_inner_smul_right, Matrix.mul_assoc, Frobenius.inner_mul_left',
    Matrix.transpose_transpose, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- If `(Sᵀ S + τ² 1) D = Sᵀ X`, then `‖S D‖ ≤ ‖X‖` and `2 τ ‖D‖ ≤ ‖X‖`. -/
theorem norm_mul_le_and_of_eq_transpose_mul (S : Matrix p (Fin r) ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    {q : Type*} [Fintype q] {D : Matrix (Fin r) q ℝ} {X : Matrix p q ℝ}
    (hD : (Sᵀ * S + τ ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ)) * D = Sᵀ * X) :
    ‖S * D‖ ≤ ‖X‖ ∧ 2 * τ * ‖D‖ ≤ ‖X‖ := by
  have h := norm_sq_add_sq_mul_norm_sq_eq_inner S τ hD
  rw [Frobenius.inner_mul_left', Matrix.transpose_transpose] at h
  have hi := real_inner_le_norm (S * D) X
  have hSD := norm_nonneg (S * D)
  have hX := norm_nonneg X
  have hDn := norm_nonneg D
  have h1 : ‖S * D‖ ≤ ‖X‖ := by nlinarith
  refine ⟨h1, ?_⟩
  have h2 : (2 * τ * ‖D‖) ^ 2 ≤ ‖X‖ ^ 2 := by nlinarith [sq_nonneg (‖X‖ - 2 * ‖S * D‖)]
  exact (pow_le_pow_iff_left₀ (by positivity) hX two_ne_zero).1 h2

/-- If `(Sᵀ S + τ² 1) D = τ² X` with `τ ≠ 0`, then `‖D‖ ≤ ‖X‖` and `2 ‖S D‖ ≤ |τ| ‖X‖`. -/
theorem norm_le_and_of_eq_smul (S : Matrix p (Fin r) ℝ) {τ : ℝ} (hτ : τ ≠ 0) {q : Type*}
    [Fintype q] {D X : Matrix (Fin r) q ℝ}
    (hD : (Sᵀ * S + τ ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ)) * D = τ ^ 2 • X) :
    ‖D‖ ≤ ‖X‖ ∧ 2 * ‖S * D‖ ≤ |τ| * ‖X‖ := by
  have h := norm_sq_add_sq_mul_norm_sq_eq_inner S τ hD
  rw [real_inner_smul_right] at h
  have hi := real_inner_le_norm D X
  have hSD := norm_nonneg (S * D)
  have hX := norm_nonneg X
  have hDn := norm_nonneg D
  have hτ2 : 0 < τ ^ 2 := by positivity
  have h1 : ‖D‖ ≤ ‖X‖ := by
    have : τ ^ 2 * ‖D‖ ^ 2 ≤ τ ^ 2 * (‖D‖ * ‖X‖) := by nlinarith
    have h' : ‖D‖ ^ 2 ≤ ‖D‖ * ‖X‖ := le_of_mul_le_mul_left this hτ2
    nlinarith
  refine ⟨h1, ?_⟩
  have h2 : (2 * ‖S * D‖) ^ 2 ≤ (|τ| * ‖X‖) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]
    nlinarith [sq_nonneg (‖X‖ - 2 * ‖D‖), mul_le_mul_of_nonneg_left hi hτ2.le]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h2

variable {K : Matrix p (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ} {ε L τ : ℝ}

omit [Fintype p] in
/-- The regularized splitting is exact: `K = K Γ⁻¹ Sᵀ S + τ² K Γ⁻¹` for `Γ = Sᵀ S + τ² 1`,
`τ ≠ 0`. -/
theorem mul_inv_mul_transpose_mul_add (hτ : τ ≠ 0) :
    K = K * ((Sᵀ * S + τ ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ))⁻¹ * Sᵀ) * S +
      τ ^ 2 • (K * (Sᵀ * S + τ ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ))⁻¹) := by
  set Γ := Sᵀ * S + τ ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ) with hΓ
  have hu := (Matrix.isUnit_iff_isUnit_det Γ).1 (isUnit_transpose_mul_self_add_smul_one S hτ)
  calc K = K * (Γ⁻¹ * Γ) := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
    _ = _ := by
        rw [hΓ, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
          ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_smul]

/-- **Bound of the factor `K'`.** If the columns of `K` satisfy `‖K c‖ ≤ ε ‖c‖ + L ‖S c‖`, then
`‖K Γ⁻¹ Sᵀ‖ ≤ √r (ε/(2τ) + L)`, `Γ = Sᵀ S + τ² 1`, `τ > 0`. -/
theorem norm_mul_inv_mul_transpose_le (hε : 0 ≤ ε) (hL : 0 ≤ L) (hτ : 0 < τ)
    (hK : ∀ c : Matrix (Fin r) (Fin 1) ℝ, ‖K * c‖ ≤ ε * ‖c‖ + L * ‖S * c‖) :
    ‖K * ((Sᵀ * S + τ ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ))⁻¹ * Sᵀ)‖ ≤
      Real.sqrt r * (ε / (2 * τ) + L) := by
  set Γ := Sᵀ * S + τ ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ) with hΓ
  have hu := (Matrix.isUnit_iff_isUnit_det Γ).1
    (isUnit_transpose_mul_self_add_smul_one S hτ.ne')
  have key := norm_le_sqrt_card_mul_of_forall_mul_single_le (M := K * (Γ⁻¹ * Sᵀ))
    (c := ε / (2 * τ) + L) (by positivity) fun j => by
      set e := (Matrix.single j 0 1 : Matrix (Fin r) (Fin 1) ℝ)
      have hD : Γ * (Γ⁻¹ * Sᵀ * e) = Sᵀ * e := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
          Matrix.one_mul]
      obtain ⟨h1, h2⟩ := norm_mul_le_and_of_eq_transpose_mul S hτ.le hD
      rw [norm_single_one] at h1 h2
      have h2' : ‖Γ⁻¹ * Sᵀ * e‖ ≤ 1 / (2 * τ) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      calc ‖K * (Γ⁻¹ * Sᵀ) * e‖ = ‖K * (Γ⁻¹ * Sᵀ * e)‖ := by rw [Matrix.mul_assoc]
        _ ≤ ε * ‖Γ⁻¹ * Sᵀ * e‖ + L * ‖S * (Γ⁻¹ * Sᵀ * e)‖ := hK _
        _ ≤ ε * (1 / (2 * τ)) + L * 1 := by gcongr
        _ = ε / (2 * τ) + L := by ring
  simpa using key

/-- **Bound of the remainder `E`.** Under the hypotheses of `norm_mul_inv_mul_transpose_le`,
`‖τ² K Γ⁻¹‖ ≤ √r (ε + L τ/2)`. -/
theorem norm_smul_mul_inv_le (hε : 0 ≤ ε) (hL : 0 ≤ L) (hτ : 0 < τ)
    (hK : ∀ c : Matrix (Fin r) (Fin 1) ℝ, ‖K * c‖ ≤ ε * ‖c‖ + L * ‖S * c‖) :
    ‖τ ^ 2 • (K * (Sᵀ * S + τ ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ))⁻¹)‖ ≤
      Real.sqrt r * (ε + L * τ / 2) := by
  set Γ := Sᵀ * S + τ ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ) with hΓ
  have hu := (Matrix.isUnit_iff_isUnit_det Γ).1
    (isUnit_transpose_mul_self_add_smul_one S hτ.ne')
  have key := norm_le_sqrt_card_mul_of_forall_mul_single_le (M := τ ^ 2 • (K * Γ⁻¹))
    (c := ε + L * τ / 2) (by positivity) fun j => by
      set e := (Matrix.single j 0 1 : Matrix (Fin r) (Fin 1) ℝ)
      have hD : Γ * (τ ^ 2 • (Γ⁻¹ * e)) = τ ^ 2 • e := by
        rw [Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
      obtain ⟨h1, h2⟩ := norm_le_and_of_eq_smul S hτ.ne' hD
      rw [norm_single_one] at h1 h2
      rw [abs_of_pos hτ] at h2
      calc ‖τ ^ 2 • (K * Γ⁻¹) * e‖ = ‖K * (τ ^ 2 • (Γ⁻¹ * e))‖ := by
            rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
        _ ≤ ε * ‖τ ^ 2 • (Γ⁻¹ * e)‖ + L * ‖S * (τ ^ 2 • (Γ⁻¹ * e))‖ := hK _
        _ ≤ ε * 1 + L * (τ / 2) := by gcongr; linarith
        _ = ε + L * τ / 2 := by ring
  simpa using key

end Tikhonov

/-! ### Mixed components with the constant `max L (2B/ρ)` -/

section Mixed

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {r : ℕ} {D : Set (ℝ × Matrix m n ℝ)} {ε L B ρ : ℝ}
  {t : ℝ} {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ}

omit [DecidableEq m] [DecidableEq n] in
/-- For a column `c`, the `1 × 1` matrix `cᵀ c` is `‖c‖²`. -/
private theorem transpose_mul_self_col (c : Matrix (Fin r) (Fin 1) ℝ) :
    cᵀ * c = (‖c‖ ^ 2) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  rw [Frobenius.norm_sq_eq_sum]
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim i 0
  obtain rfl : j = 0 := Subsingleton.elim j 0
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, Fin.sum_univ_one, pow_two]

omit [DecidableEq m] [DecidableEq n] in
/-- A nonzero column is its norm times a unit column. -/
private theorem exists_unit_col_eq_smul {c : Matrix (Fin r) (Fin 1) ℝ} (hc : c ≠ 0) :
    ∃ b : Matrix (Fin r) (Fin 1) ℝ, bᵀ * b = 1 ∧ ‖c‖ • b = c := by
  have hc' : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  refine ⟨‖c‖⁻¹ • c, ?_, ?_⟩
  · have h : ‖c‖⁻¹ * ‖c‖⁻¹ * ‖c‖ ^ 2 = 1 := by
      rw [pow_two, mul_mul_mul_comm, inv_mul_cancel₀ hc', mul_one]
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      transpose_mul_self_col, smul_smul, h, one_smul]
  · rw [smul_smul, mul_inv_cancel₀ hc', one_smul]

/-- The column form of `norm_normal_mul_field_mul_le_of_ball` for a unit column `b`. -/
private theorem norm_normal_mul_field_mul_col_le_of_ball (hN : FactoredNormalBoundOn F r D ε)
    (hL : IsLipschitzFieldOn F D L) (hB : IsBoundedFieldOn F D B) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {v' : Matrix n (Fin 1) ℝ} (hv' : v'ᵀ * v' = 1) (hVv' : Vᵀ * v' = 0)
    (hρ : 0 < ρ) (hD : ∀ X, ‖X - U * S * Vᵀ‖ ≤ ρ / 2 → (t, X) ∈ D)
    {b : Matrix (Fin r) (Fin 1) ℝ} (hb : bᵀ * b = 1) :
    ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (V * b)‖ ≤ ε + max L (2 * B / ρ) * ‖S * b‖ := by
  have hW : (t, U * S * Vᵀ) ∈ D := hD _ (by rw [sub_self, norm_zero]; positivity)
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hN t U V S hU hV hW)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB hW)
  have hSb := norm_nonneg (S * b)
  by_cases hs : ‖S * b‖ ≤ ρ / 2
  · have h := norm_normal_mul_field_mul_col_le hN hL hU hV hb hv' hVv' hW
      (hD _ (by rw [norm_deflate_right_sub hU hV hb]; exact hs))
    calc _ ≤ ε + L * ‖S * b‖ := h
      _ ≤ ε + max L (2 * B / ρ) * ‖S * b‖ := by gcongr; exact le_max_left _ _
  · push Not at hs
    have hVb : (V * b)ᵀ * (V * b) = 1 := by
      rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul, hb]
    calc ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (V * b)‖
        ≤ ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ)‖ := norm_mul_le_of_orthonormal hVb _
      _ ≤ ‖F t (U * S * Vᵀ)‖ := by
          rw [← one_sub_leftProj_apply]
          exact (isOrthProj_leftProj hU).compl.norm_le _
      _ ≤ B := hB hW
      _ = 2 * B / ρ * (ρ / 2) := by field_simp
      _ ≤ 2 * B / ρ * ‖S * b‖ := by gcongr
      _ ≤ max L (2 * B / ρ) * ‖S * b‖ := by gcongr; exact le_max_right _ _
      _ ≤ ε + max L (2 * B / ρ) * ‖S * b‖ := le_add_of_nonneg_left hε

/-- **Mixed component along the rows, on a ball.** If the ball of radius `ρ/2` around the
factored point `U S Vᵀ` lies in the region (at time `t`), then for every column `c`
`‖(1 - U Uᵀ) F(t, U S Vᵀ) (V c)‖ ≤ ε ‖c‖ + max L (2B/ρ) ‖S c‖`: a deflated point outside the
region is `‖S b‖ > ρ/2` away, and there the bound `B` of the field is used. -/
theorem norm_normal_mul_field_mul_le_of_ball (hN : FactoredNormalBoundOn F r D ε)
    (hL : IsLipschitzFieldOn F D L) (hB : IsBoundedFieldOn F D B) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {v' : Matrix n (Fin 1) ℝ} (hv' : v'ᵀ * v' = 1) (hVv' : Vᵀ * v' = 0)
    (hρ : 0 < ρ) (hD : ∀ X, ‖X - U * S * Vᵀ‖ ≤ ρ / 2 → (t, X) ∈ D)
    (c : Matrix (Fin r) (Fin 1) ℝ) :
    ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (V * c)‖ ≤ ε * ‖c‖ + max L (2 * B / ρ) * ‖S * c‖ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · obtain ⟨b, hb, hcb⟩ := exists_unit_col_eq_smul hc
    have key := norm_normal_mul_field_mul_col_le_of_ball hN hL hB hU hV hv' hVv' hρ hD hb
    have h₁ : (1 - U * Uᵀ) * F t (U * S * Vᵀ) * (V * c) =
        ‖c‖ • ((1 - U * Uᵀ) * F t (U * S * Vᵀ) * (V * b)) := by
      rw [← Matrix.mul_smul, ← Matrix.mul_smul, hcb]
    have h₂ : S * c = ‖c‖ • (S * b) := by rw [← Matrix.mul_smul, hcb]
    rw [h₁, h₂, norm_smul, norm_smul, norm_norm]
    calc ‖c‖ * ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (V * b)‖
        ≤ ‖c‖ * (ε + max L (2 * B / ρ) * ‖S * b‖) :=
          mul_le_mul_of_nonneg_left key (norm_nonneg c)
      _ = ε * ‖c‖ + max L (2 * B / ρ) * (‖c‖ * ‖S * b‖) := by ring

/-- The column form of `norm_transpose_mul_field_mul_normal_le_of_ball` for a unit column. -/
private theorem norm_col_transpose_mul_field_mul_normal_le_of_ball
    (hN : FactoredNormalBoundOn F r D ε) (hL : IsLipschitzFieldOn F D L)
    (hB : IsBoundedFieldOn F D B) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {u' : Matrix m (Fin 1) ℝ} (hu' : u'ᵀ * u' = 1) (hUu' : Uᵀ * u' = 0) (hρ : 0 < ρ)
    (hD : ∀ X, ‖X - U * S * Vᵀ‖ ≤ ρ / 2 → (t, X) ∈ D)
    {a : Matrix (Fin r) (Fin 1) ℝ} (ha : aᵀ * a = 1) :
    ‖(U * a)ᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε + max L (2 * B / ρ) * ‖aᵀ * S‖ := by
  have hW : (t, U * S * Vᵀ) ∈ D := hD _ (by rw [sub_self, norm_zero]; positivity)
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hN t U V S hU hV hW)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB hW)
  have haS := norm_nonneg (aᵀ * S)
  by_cases hs : ‖aᵀ * S‖ ≤ ρ / 2
  · have h := norm_col_transpose_mul_field_mul_normal_le hN hL hU hV ha hu' hUu' hW
      (hD _ (by rw [norm_deflate_left_sub hU hV ha]; exact hs))
    calc _ ≤ ε + L * ‖aᵀ * S‖ := h
      _ ≤ ε + max L (2 * B / ρ) * ‖aᵀ * S‖ := by gcongr; exact le_max_left _ _
  · push Not at hs
    have hUa : (U * a)ᵀ * (U * a) = 1 := by
      rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul, ha]
    calc ‖(U * a)ᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖
        ≤ ‖(U * a)ᵀ * F t (U * S * Vᵀ)‖ := by
          rw [← one_sub_rightProj_apply]
          exact (isOrthProj_rightProj hV).compl.norm_le _
      _ ≤ ‖F t (U * S * Vᵀ)‖ := norm_transpose_mul_le hUa _
      _ ≤ B := hB hW
      _ = 2 * B / ρ * (ρ / 2) := by field_simp
      _ ≤ 2 * B / ρ * ‖aᵀ * S‖ := by gcongr
      _ ≤ max L (2 * B / ρ) * ‖aᵀ * S‖ := by gcongr; exact le_max_right _ _
      _ ≤ ε + max L (2 * B / ρ) * ‖aᵀ * S‖ := le_add_of_nonneg_left hε

/-- **Mixed component along the columns, on a ball.** If the ball of radius `ρ/2` around the
factored point `U S Vᵀ` lies in the region (at time `t`), then for every column `c`
`‖(U c)ᵀ F(t, U S Vᵀ) (1 - V Vᵀ)‖ ≤ ε ‖c‖ + max L (2B/ρ) ‖cᵀ S‖`. -/
theorem norm_transpose_mul_field_mul_normal_le_of_ball (hN : FactoredNormalBoundOn F r D ε)
    (hL : IsLipschitzFieldOn F D L) (hB : IsBoundedFieldOn F D B) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {u' : Matrix m (Fin 1) ℝ} (hu' : u'ᵀ * u' = 1) (hUu' : Uᵀ * u' = 0)
    (hρ : 0 < ρ) (hD : ∀ X, ‖X - U * S * Vᵀ‖ ≤ ρ / 2 → (t, X) ∈ D)
    (c : Matrix (Fin r) (Fin 1) ℝ) :
    ‖(U * c)ᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤
      ε * ‖c‖ + max L (2 * B / ρ) * ‖cᵀ * S‖ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · obtain ⟨a, ha, hca⟩ := exists_unit_col_eq_smul hc
    have key := norm_col_transpose_mul_field_mul_normal_le_of_ball hN hL hB hU hV hu' hUu' hρ
      hD ha
    have h₁ : (U * c)ᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ) =
        ‖c‖ • ((U * a)ᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ)) := by
      rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, ← Matrix.mul_smul, hca]
    have h₂ : cᵀ * S = ‖c‖ • (aᵀ * S) := by
      rw [← Matrix.smul_mul, ← Matrix.transpose_smul, hca]
    rw [h₁, h₂, norm_smul, norm_smul, norm_norm]
    calc ‖c‖ * ‖(U * a)ᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖
        ≤ ‖c‖ * (ε + max L (2 * B / ρ) * ‖aᵀ * S‖) :=
          mul_le_mul_of_nonneg_left key (norm_nonneg c)
      _ = ε * ‖c‖ + max L (2 * B / ρ) * (‖c‖ * ‖aᵀ * S‖) := by ring

/-- The columns of the transposed mixed component `(Uᵀ F(t, U S Vᵀ) (1 - V Vᵀ))ᵀ` satisfy the
bound `ε ‖c‖ + max L (2B/ρ) ‖Sᵀ c‖` (`norm_transpose_mul_field_mul_normal_le_of_ball`). -/
private theorem norm_transpose_mixed_mul_le_of_ball (hN : FactoredNormalBoundOn F r D ε)
    (hL : IsLipschitzFieldOn F D L) (hB : IsBoundedFieldOn F D B) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {u' : Matrix m (Fin 1) ℝ} (hu' : u'ᵀ * u' = 1) (hUu' : Uᵀ * u' = 0)
    (hρ : 0 < ρ) (hD : ∀ X, ‖X - U * S * Vᵀ‖ ≤ ρ / 2 → (t, X) ∈ D)
    (c : Matrix (Fin r) (Fin 1) ℝ) :
    ‖(Uᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ))ᵀ * c‖ ≤
      ε * ‖c‖ + max L (2 * B / ρ) * ‖Sᵀ * c‖ := by
  have h := norm_transpose_mul_field_mul_normal_le_of_ball hN hL hB hU hV hu' hUu' hρ hD c
  have e1 : (Uᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ))ᵀ * c =
      ((U * c)ᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ))ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have e2 : ‖Sᵀ * c‖ = ‖cᵀ * S‖ := by
    rw [← Frobenius.norm_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [e1, Frobenius.norm_transpose, e2]
  exact h

/-- **The mixed component seen from another basis.** Let `W = U S Vᵀ` be a factored point whose
ball of radius `ρ/2` lies in the region, and let `Ua` have orthonormal columns. The part of the
mixed component `U Uᵀ F(t, W) (1 - V Vᵀ)` outside the range of `Ua` is at most
`κ ‖(1 - Ua Uaᵀ) W‖ + e` with `κ = √r (ε/(2τ) + L̃)`, `e = √r (ε + L̃ τ/2)`,
`L̃ = max L (2B/ρ)`, for every `τ > 0`: the component is `S N + E` with `‖N‖ ≤ κ`, `‖E‖ ≤ e`, and
`U S = W V`. -/
theorem norm_one_sub_mul_mul_mul_one_sub_le (hN : FactoredNormalBoundOn F r D ε)
    (hL : IsLipschitzFieldOn F D L) (hL0 : 0 ≤ L) (hB : IsBoundedFieldOn F D B)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {u' : Matrix m (Fin 1) ℝ} (hu' : u'ᵀ * u' = 1)
    (hUu' : Uᵀ * u' = 0) (hρ : 0 < ρ) (hD : ∀ X, ‖X - U * S * Vᵀ‖ ≤ ρ / 2 → (t, X) ∈ D)
    {τ : ℝ} (hτ : 0 < τ) {k : Type*} [Fintype k] [DecidableEq k] {Ua : Matrix m k ℝ}
    (hUa : Uaᵀ * Ua = 1) :
    ‖(1 - Ua * Uaᵀ) * (U * Uᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ))‖ ≤
      Real.sqrt r * (ε / (2 * τ) + max L (2 * B / ρ)) * ‖(1 - Ua * Uaᵀ) * (U * S * Vᵀ)‖ +
        Real.sqrt r * (ε + max L (2 * B / ρ) * τ / 2) := by
  have hW : (t, U * S * Vᵀ) ∈ D := hD _ (by rw [sub_self, norm_zero]; positivity)
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hN t U V S hU hV hW)
  have hL' : 0 ≤ max L (2 * B / ρ) := hL0.trans (le_max_left _ _)
  set Q := Uᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ) with hQ
  have hcol : ∀ c : Matrix (Fin r) (Fin 1) ℝ,
      ‖Qᵀ * c‖ ≤ ε * ‖c‖ + max L (2 * B / ρ) * ‖Sᵀ * c‖ :=
    norm_transpose_mixed_mul_le_of_ball hN hL hB hU hV hu' hUu' hρ hD
  set Γ := Sᵀᵀ * Sᵀ + τ ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ) with hΓ
  set N := Qᵀ * (Γ⁻¹ * Sᵀᵀ) with hNdef
  set E := τ ^ 2 • (Qᵀ * Γ⁻¹) with hEdef
  have hsplit : Qᵀ = N * Sᵀ + E := mul_inv_mul_transpose_mul_add hτ.ne'
  have hNb : ‖N‖ ≤ Real.sqrt r * (ε / (2 * τ) + max L (2 * B / ρ)) :=
    norm_mul_inv_mul_transpose_le hε hL' hτ hcol
  have hEb : ‖E‖ ≤ Real.sqrt r * (ε + max L (2 * B / ρ) * τ / 2) :=
    norm_smul_mul_inv_le hε hL' hτ hcol
  have hQ' : Q = S * Nᵀ + Eᵀ := by
    rw [← Matrix.transpose_transpose Q, hsplit, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  have hUS : U * S = U * S * Vᵀ * V := by rw [Matrix.mul_assoc _ Vᵀ, hV, Matrix.mul_one]
  have e : (1 - Ua * Uaᵀ) * (U * Uᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ)) =
      (1 - Ua * Uaᵀ) * (U * S * Vᵀ) * V * Nᵀ + (1 - Ua * Uaᵀ) * (U * Eᵀ) := by
    have : U * Uᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ) = U * Q := by
      rw [hQ, Matrix.mul_assoc U Uᵀ, Matrix.mul_assoc U]
    have h2 : U * Q = U * S * Vᵀ * V * Nᵀ + U * Eᵀ := by
      rw [hQ', Matrix.mul_add, ← Matrix.mul_assoc U S, ← hUS]
    rw [this, h2, Matrix.mul_add]
    simp only [Matrix.mul_assoc]
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · calc ‖(1 - Ua * Uaᵀ) * (U * S * Vᵀ) * V * Nᵀ‖
        ≤ ‖(1 - Ua * Uaᵀ) * (U * S * Vᵀ) * V‖ * ‖Nᵀ‖ := Frobenius.norm_mul_le _ _
      _ ≤ ‖(1 - Ua * Uaᵀ) * (U * S * Vᵀ)‖ * ‖N‖ := by
          rw [Frobenius.norm_transpose]
          gcongr
          exact norm_mul_le_of_orthonormal hV _
      _ ≤ _ := by rw [mul_comm]; gcongr
  · calc ‖(1 - Ua * Uaᵀ) * (U * Eᵀ)‖ ≤ ‖U * Eᵀ‖ := by
          rw [← one_sub_leftProj_apply]
          exact (isOrthProj_leftProj hUa).compl.norm_le _
      _ = ‖E‖ := by rw [Frobenius.norm_mul_of_orthonormal hU, Frobenius.norm_transpose]
      _ ≤ _ := hEb

end Mixed

/-! ### Algebra of the predictor -/

section Predictor

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}

/-- The tangent projection split into its three blocks:
`P₀ X = U₀ (U₀ᵀ X V₀) V₀ᵀ + (1 - U₀ U₀ᵀ) X V₀ V₀ᵀ + U₀ (U₀ᵀ X (1 - V₀ V₀ᵀ))`. -/
theorem tangentProj_eq_add_add (U₀ : Matrix m (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (X : Matrix m n ℝ) :
    tangentProj U₀ V₀ X = U₀ * (U₀ᵀ * X * V₀) * V₀ᵀ + (1 - U₀ * U₀ᵀ) * X * V₀ * V₀ᵀ +
      U₀ * (U₀ᵀ * X * (1 - V₀ * V₀ᵀ)) := by
  rw [tangentProj_apply]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- **The predictor minus a rank-`r` point.** With the splittings `K = K' S₀ + E_K` and
`Λ = Λ' S₀ᵀ + E_Λ` of the two mixed blocks, the predictor `U₀ S₀ V₀ᵀ + a (U₀ M V₀ᵀ + K V₀ᵀ + U₀ Λᵀ)`
differs from `(U₀ + a K') (S₀ + a M) (V₀ + a Λ')ᵀ` by terms of order `a` in `E_K`, `E_Λ` and of
order `a²`. -/
theorem predictor_sub_factored_eq (U₀ : Matrix m (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (S₀ M : Matrix (Fin r) (Fin r) ℝ) (K' EK : Matrix m (Fin r) ℝ) (Λ' EL : Matrix n (Fin r) ℝ)
    (a : ℝ) :
    U₀ * S₀ * V₀ᵀ + a • (U₀ * M * V₀ᵀ + (K' * S₀ + EK) * V₀ᵀ + U₀ * (Λ' * S₀ᵀ + EL)ᵀ) -
        (U₀ + a • K') * (S₀ + a • M) * (V₀ + a • Λ')ᵀ =
      a • (EK * V₀ᵀ + U₀ * ELᵀ) - a ^ 2 • (K' * M * V₀ᵀ + U₀ * M * Λ'ᵀ + K' * S₀ * Λ'ᵀ) -
        a ^ 3 • (K' * M * Λ'ᵀ) := by
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_add, smul_smul, Matrix.mul_assoc]
  module

omit [DecidableEq m] [DecidableEq n] in
/-- Bound of the difference in `predictor_sub_factored_eq`. -/
theorem norm_predictor_sub_factored_le {U₀ : Matrix m (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {S₀ M : Matrix (Fin r) (Fin r) ℝ}
    {K' EK : Matrix m (Fin r) ℝ} {Λ' EL : Matrix n (Fin r) ℝ} {a κ e B : ℝ} (ha : 0 ≤ a)
    (hK' : ‖K'‖ ≤ κ) (hΛ' : ‖Λ'‖ ≤ κ) (hEK : ‖EK‖ ≤ e) (hEL : ‖EL‖ ≤ e) (hM : ‖M‖ ≤ B) :
    ‖a • (EK * V₀ᵀ + U₀ * ELᵀ) - a ^ 2 • (K' * M * V₀ᵀ + U₀ * M * Λ'ᵀ + K' * S₀ * Λ'ᵀ) -
        a ^ 3 • (K' * M * Λ'ᵀ)‖ ≤
      2 * a * e + a ^ 2 * (2 * κ * B + κ ^ 2 * ‖S₀‖) + a ^ 3 * (κ ^ 2 * B) := by
  have hκ : 0 ≤ κ := (norm_nonneg _).trans hK'
  have hB : 0 ≤ B := (norm_nonneg _).trans hM
  have h1 : ‖EK * V₀ᵀ + U₀ * ELᵀ‖ ≤ 2 * e := by
    refine (norm_add_le _ _).trans ?_
    rw [Frobenius.norm_mul_transpose_of_orthonormal hV₀, Frobenius.norm_mul_of_orthonormal hU₀,
      Frobenius.norm_transpose]
    linarith
  have h2 : ‖K' * M * V₀ᵀ + U₀ * M * Λ'ᵀ + K' * S₀ * Λ'ᵀ‖ ≤ 2 * κ * B + κ ^ 2 * ‖S₀‖ := by
    have e1 : ‖K' * M * V₀ᵀ‖ ≤ κ * B := by
      rw [Frobenius.norm_mul_transpose_of_orthonormal hV₀]
      exact (Frobenius.norm_mul_le _ _).trans (mul_le_mul hK' hM (norm_nonneg _) hκ)
    have e2 : ‖U₀ * M * Λ'ᵀ‖ ≤ κ * B := by
      rw [Matrix.mul_assoc, Frobenius.norm_mul_of_orthonormal hU₀]
      refine (Frobenius.norm_mul_le _ _).trans ?_
      rw [Frobenius.norm_transpose, mul_comm]
      exact mul_le_mul hΛ' hM (norm_nonneg _) hκ
    have e3 : ‖K' * S₀ * Λ'ᵀ‖ ≤ κ ^ 2 * ‖S₀‖ := by
      refine (Frobenius.norm_mul_le _ _).trans ?_
      rw [Frobenius.norm_transpose]
      calc ‖K' * S₀‖ * ‖Λ'‖ ≤ (κ * ‖S₀‖) * κ :=
            mul_le_mul ((Frobenius.norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right hK' (norm_nonneg _))) hΛ' (norm_nonneg _)
              (by positivity)
        _ = κ ^ 2 * ‖S₀‖ := by ring
    calc _ ≤ ‖K' * M * V₀ᵀ‖ + ‖U₀ * M * Λ'ᵀ‖ + ‖K' * S₀ * Λ'ᵀ‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ κ * B + κ * B + κ ^ 2 * ‖S₀‖ := by gcongr
      _ = _ := by ring
  have h3 : ‖K' * M * Λ'ᵀ‖ ≤ κ ^ 2 * B := by
    refine (Frobenius.norm_mul_le _ _).trans ?_
    rw [Frobenius.norm_transpose]
    calc ‖K' * M‖ * ‖Λ'‖ ≤ (κ * B) * κ :=
          mul_le_mul ((Frobenius.norm_mul_le _ _).trans (mul_le_mul hK' hM (norm_nonneg _) hκ))
            hΛ' (norm_nonneg _) (by positivity)
      _ = κ ^ 2 * B := by ring
  calc _ ≤ ‖a • (EK * V₀ᵀ + U₀ * ELᵀ)‖ +
        ‖a ^ 2 • (K' * M * V₀ᵀ + U₀ * M * Λ'ᵀ + K' * S₀ * Λ'ᵀ)‖ + ‖a ^ 3 • (K' * M * Λ'ᵀ)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ a * (2 * e) + a ^ 2 * (2 * κ * B + κ ^ 2 * ‖S₀‖) + a ^ 3 * (κ ^ 2 * B) := by
        rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg (by positivity),
          abs_of_nonneg (by positivity)]
        gcongr
    _ = _ := by ring

omit [DecidableEq m] [DecidableEq n] in
/-- Right multiplication by `(Sᵀ S + 1)⁻¹` does not increase the Frobenius norm. -/
theorem norm_mul_inv_transpose_mul_self_add_one_le {p : Type*} [Fintype p]
    (S : Matrix p (Fin r) ℝ) {q : Type*} [Fintype q] (A : Matrix q (Fin r) ℝ) :
    ‖A * (Sᵀ * S + (1 : ℝ) ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ))⁻¹‖ ≤ ‖A‖ := by
  set Γ := Sᵀ * S + (1 : ℝ) ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ) with hΓ
  have hu := (Matrix.isUnit_iff_isUnit_det Γ).1
    (isUnit_transpose_mul_self_add_smul_one S one_ne_zero)
  have hsymm : Γᵀ = Γ := by
    rw [hΓ, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_smul, Matrix.transpose_one]
  have hD : Γ * (Γ⁻¹ * Aᵀ) = (1 : ℝ) ^ 2 • Aᵀ := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, one_pow, one_smul]
  have h := (norm_le_and_of_eq_smul S one_ne_zero hD).1
  calc ‖A * Γ⁻¹‖ = ‖Γ⁻¹ * Aᵀ‖ := by
        rw [← Frobenius.norm_transpose, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
          hsymm]
    _ ≤ ‖Aᵀ‖ := h
    _ = ‖A‖ := Frobenius.norm_transpose A

omit [DecidableEq n] in
/-- **Projector onto the range of `V₀ + a Λ'`.** If `V₀ᵀ V₀ = 1`, `V₀ᵀ Λ' = 0` and `Vt` is an
orthonormal frame with `r` columns that captures `Y = V₀ + a Λ'`, then
`Vt Vtᵀ = Y (Yᵀ Y)⁻¹ Yᵀ` with `Yᵀ Y = (a Λ')ᵀ (a Λ') + 1`. -/
theorem mul_transpose_eq_of_capture_add {V₀ Λ' : Matrix n (Fin r) ℝ} (hV₀ : V₀ᵀ * V₀ = 1)
    (hVΛ : V₀ᵀ * Λ' = 0) (a : ℝ) {Vt : Matrix n (Fin r) ℝ}
    (hcap : Vt * Vtᵀ * (V₀ + a • Λ') = V₀ + a • Λ') :
    Vt * Vtᵀ = (V₀ + a • Λ') *
      ((a • Λ')ᵀ * (a • Λ') + (1 : ℝ) ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ))⁻¹ *
        (V₀ + a • Λ')ᵀ := by
  set Y := V₀ + a • Λ' with hY
  set Γ := (a • Λ')ᵀ * (a • Λ') + (1 : ℝ) ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ) with hΓ
  have hΛV : Λ'ᵀ * V₀ = 0 := by
    rw [← Matrix.transpose_transpose (Λ'ᵀ * V₀), Matrix.transpose_mul,
      Matrix.transpose_transpose, hVΛ, Matrix.transpose_zero]
  have hYY : Yᵀ * Y = Γ := by
    simp only [hY, hΓ, Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hV₀, hVΛ, hΛV, smul_zero, add_zero,
      one_pow, one_smul]
    abel
  set R := Vtᵀ * Y with hR
  have hYR : Y = Vt * R := by rw [hR, ← Matrix.mul_assoc]; exact hcap.symm
  have hRR : Rᵀ * R = Γ := by
    rw [← hYY, hR, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Vt, hcap]
  have hu := (Matrix.isUnit_iff_isUnit_det Γ).1
    (isUnit_transpose_mul_self_add_smul_one (a • Λ') one_ne_zero)
  have hsymm : Γᵀ = Γ := by
    simp only [hΓ, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_smul, Matrix.transpose_one]
  have hleft : Γ⁻¹ * Rᵀ * R = 1 := by
    rw [Matrix.mul_assoc, hRR, Matrix.nonsing_inv_mul _ hu]
  have hright : R * (Γ⁻¹ * Rᵀ) = 1 := mul_eq_one_comm.mp hleft
  have hVt : Vt = Y * (Γ⁻¹ * Rᵀ) := by
    rw [hYR, Matrix.mul_assoc, hright, Matrix.mul_one]
  calc Vt * Vtᵀ = Y * (Γ⁻¹ * Rᵀ) * (Y * (Γ⁻¹ * Rᵀ))ᵀ := by rw [← hVt]
    _ = Y * Γ⁻¹ * (Rᵀ * R) * (Γ⁻¹)ᵀ * Yᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = Y * Γ⁻¹ * Yᵀ := by
        rw [hRR, Matrix.transpose_nonsing_inv, hsymm, Matrix.mul_assoc Y Γ⁻¹ Γ,
          Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

end Predictor

/-! ### The capture defect -/

section Capture

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Left multiplication by `1 - U Uᵀ` does not increase the Frobenius norm. -/
private theorem norm_one_sub_mul_le_of_orthonormal {k l : Type*} [Fintype k] [DecidableEq k]
    [Fintype l] {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) (X : Matrix m l ℝ) :
    ‖(1 - U * Uᵀ) * X‖ ≤ ‖X‖ := by
  rw [← one_sub_leftProj_apply]
  exact (isOrthProj_leftProj hU).compl.norm_le _

/-- Right multiplication by `1 - V Vᵀ` does not increase the Frobenius norm. -/
private theorem norm_mul_one_sub_le_of_orthonormal {k l : Type*} [Fintype k] [DecidableEq k]
    [Fintype l] {V : Matrix n k ℝ} (hV : Vᵀ * V = 1) (X : Matrix l n ℝ) :
    ‖X * (1 - V * Vᵀ)‖ ≤ ‖X‖ := by
  rw [← one_sub_rightProj_apply]
  exact (isOrthProj_rightProj hV).compl.norm_le _

omit [DecidableEq m] in
/-- A unit column orthogonal to the range of `U` when `U` has fewer columns than rows. -/
private theorem exists_unit_col_orthogonal {r : ℕ} {U : Matrix m (Fin r) ℝ} (hU : Uᵀ * U = 1)
    (hr : r < Fintype.card m) : ∃ u : Matrix m (Fin 1) ℝ, uᵀ * u = 1 ∧ Uᵀ * u = 0 := by
  classical
  obtain ⟨u, hu, huU, -⟩ := exists_orthonormal_capture_compl U hU (0 : Matrix m (Fin 1) ℝ)
    (s := 1) (by simp) (by rw [Fintype.card_fin]; exact hr)
  refine ⟨u, hu, ?_⟩
  rw [← Matrix.transpose_transpose (Uᵀ * u), Matrix.transpose_mul, Matrix.transpose_transpose,
    huU, Matrix.transpose_zero]

/-- **Capture defect of the explicit midpoint step.** Let `F` satisfy, on a region `D` that
contains `[t₀, t₀ + h] × closedBall (U₀ S₀ V₀ᵀ) ρ`, the factored normal bound with defect `ε`,
a Lipschitz bound `L`, a bound `B` and a Lipschitz bound `Lₜ` in time, and let `r` be smaller
than both dimensions. Let `Z = Y₀ + (h/2) P₀ F(t₀, Y₀)` be the explicit predictor,
`G = F(t₀ + h/2, Z)`, and let `Ua` have orthonormal columns whose range contains those of `U₀`
and `G V₀`. With `L̃ = max L (2B/ρ)`, any `τ > 0`, `κ ≥ √r (ε/(2τ) + L̃)`,
`e ≥ √r (ε + L̃ τ/2)`, `δ ≥ h e + (h/2)² (2κB + κ²‖S₀‖) + (h/2)³ κ² B` and `h B/2 + δ ≤ ρ/2`,

`‖(1 - Ua Uaᵀ) G (1 - V₀ V₀ᵀ)‖ ≤ (L + κ + (h/2) L κ) δ + ε + e + (h/2)² κ (L B + Lₜ + B κ)`.

The constants contain `‖S₀‖` but no inverse of `S₀`. The proof compares `G` with the field at
the rank-`r` point `W = (U₀ + (h/2) K') (S₀ + (h/2) M) (V₀ + (h/2) Λ')ᵀ`, where `K' S₀` and
`Λ' S₀ᵀ` approximate the mixed blocks of `F(t₀, Y₀)` (`mul_inv_mul_transpose_mul_add`), and
bounds the three parts of `F(t₀ + h/2, W) (1 - V₀ V₀ᵀ)` outside `Ua`. -/
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
      (L + κ + h / 2 * L * κ) * δ + ε + e + (h / 2) ^ 2 * κ * (L * B + Lₜ + B * κ) := by
  -- notation and first bounds
  set a := h / 2 with ha
  have ha0 : 0 ≤ a := div_nonneg hh zero_le_two
  have h2a : h = 2 * a := by rw [ha]; ring
  set Y₀ := U₀ * S₀ * V₀ᵀ with hY₀
  set F₁ := F t₀ Y₀ with hF₁
  have hLm0 : 0 ≤ max L (2 * B / ρ) := hL0.trans (le_max_left _ _)
  have ht₀ : t₀ ∈ Icc t₀ (t₀ + h) := ⟨le_rfl, by linarith⟩
  have htm : t₀ + a ∈ Icc t₀ (t₀ + h) := ⟨by linarith, by linarith⟩
  have hY₀D : (t₀, Y₀) ∈ D := hD t₀ ht₀ _ (by rw [sub_self, norm_zero]; exact hρ.le)
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hN t₀ U₀ V₀ S₀ hU₀ hV₀ hY₀D)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB hY₀D)
  have hF₁B : ‖F₁‖ ≤ B := hB hY₀D
  have hκ0 : 0 ≤ κ :=
    le_trans (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (div_nonneg hε (by positivity)) hLm0)) hκ
  have he0 : 0 ≤ e := le_trans (mul_nonneg (Real.sqrt_nonneg _)
    (add_nonneg hε (div_nonneg (mul_nonneg hLm0 hτ.le) zero_le_two))) he
  have hδ0 : 0 ≤ δ := le_trans (add_nonneg (add_nonneg (mul_nonneg hh he0)
    (mul_nonneg (pow_nonneg ha0 2) (add_nonneg (mul_nonneg (mul_nonneg zero_le_two hκ0) hB0)
      (mul_nonneg (pow_nonneg hκ0 2) (norm_nonneg _)))))
    (mul_nonneg (pow_nonneg ha0 3) (mul_nonneg (pow_nonneg hκ0 2) hB0))) hδ
  have hZY : ‖Z - Y₀‖ ≤ a * B := by
    rw [hZ, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left
      (((isOrthProj_tangentProj hU₀ hV₀).norm_le _).trans hF₁B) ha0
  have hZD : ∀ t ∈ Icc t₀ (t₀ + h), (t, Z) ∈ D := fun t ht => hD t ht _ (by linarith)
  have hball₀ : ∀ X, ‖X - Y₀‖ ≤ ρ / 2 → (t₀, X) ∈ D := fun X hX => hD t₀ ht₀ X (by linarith)
  obtain ⟨u₀, hu₀, hU₀u⟩ := exists_unit_col_orthogonal hU₀ hrm
  obtain ⟨v₀, hv₀, hV₀v⟩ := exists_unit_col_orthogonal hV₀ hrn
  -- the three blocks of the tangent projection
  set M := U₀ᵀ * F₁ * V₀ with hMdef
  set K := (1 - U₀ * U₀ᵀ) * F₁ * V₀ with hKdef
  set Lt := U₀ᵀ * F₁ * (1 - V₀ * V₀ᵀ) with hLtdef
  have hMB : ‖M‖ ≤ B :=
    ((norm_mul_le_of_orthonormal hV₀ _).trans (norm_transpose_mul_le hU₀ _)).trans hF₁B
  have hKcol : ∀ c : Matrix (Fin r) (Fin 1) ℝ,
      ‖K * c‖ ≤ ε * ‖c‖ + max L (2 * B / ρ) * ‖S₀ * c‖ := fun c => by
    rw [hKdef, Matrix.mul_assoc _ V₀ c]
    exact norm_normal_mul_field_mul_le_of_ball hN hL hB hU₀ hV₀ hv₀ hV₀v hρ hball₀ c
  have hLcol : ∀ c : Matrix (Fin r) (Fin 1) ℝ,
      ‖Ltᵀ * c‖ ≤ ε * ‖c‖ + max L (2 * B / ρ) * ‖S₀ᵀ * c‖ :=
    norm_transpose_mixed_mul_le_of_ball hN hL hB hU₀ hV₀ hu₀ hU₀u hρ hball₀
  -- the regularized splittings `K = K' S₀ + E_K`, `Ltᵀ = Λ' S₀ᵀ + E_L`
  set K' := K * ((S₀ᵀ * S₀ + τ ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ))⁻¹ * S₀ᵀ) with hK'def
  set EK := τ ^ 2 • (K * (S₀ᵀ * S₀ + τ ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ))⁻¹) with hEKdef
  have hKsplit : K = K' * S₀ + EK := mul_inv_mul_transpose_mul_add hτ.ne'
  have hK'b : ‖K'‖ ≤ κ := (norm_mul_inv_mul_transpose_le hε hLm0 hτ hKcol).trans hκ
  have hEKb : ‖EK‖ ≤ e := (norm_smul_mul_inv_le hε hLm0 hτ hKcol).trans he
  set Λ' := Ltᵀ * ((S₀ᵀᵀ * S₀ᵀ + τ ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ))⁻¹ * S₀ᵀᵀ)
    with hΛ'def
  set EL := τ ^ 2 • (Ltᵀ * (S₀ᵀᵀ * S₀ᵀ + τ ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ))⁻¹)
    with hELdef
  have hLsplit : Ltᵀ = Λ' * S₀ᵀ + EL := mul_inv_mul_transpose_mul_add hτ.ne'
  have hΛ'b : ‖Λ'‖ ≤ κ := by
    have h := (norm_mul_inv_mul_transpose_le hε hLm0 hτ hLcol).trans hκ
    exact h
  have hELb : ‖EL‖ ≤ e := (norm_smul_mul_inv_le hε hLm0 hτ hLcol).trans he
  have hV₀P : V₀ᵀ * (1 - V₀ * V₀ᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hV₀, Matrix.one_mul, sub_self]
  have hV₀Λ' : V₀ᵀ * Λ' = 0 := by
    have hV₀Lt : V₀ᵀ * Ltᵀ = 0 := by
      rw [hLtdef]
      simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.transpose_transpose, ← Matrix.mul_assoc, hV₀P, Matrix.zero_mul]
    rw [hΛ'def, ← Matrix.mul_assoc, hV₀Lt, Matrix.zero_mul]
  -- the predictor and the rank-`r` point `W`
  have hZ₀ : Z = Y₀ + a • (U₀ * M * V₀ᵀ + K * V₀ᵀ + U₀ * Lt) := by
    rw [hZ, tangentProj_eq_add_add, ← hMdef, ← hKdef, ← hLtdef]
  have hZexp : Z = Y₀ + a • (U₀ * M * V₀ᵀ + (K' * S₀ + EK) * V₀ᵀ + U₀ * (Λ' * S₀ᵀ + EL)ᵀ) := by
    rw [hZ₀, ← hKsplit, ← hLsplit, Matrix.transpose_transpose]
  set X := U₀ + a • K' with hXdef
  set Yv := V₀ + a • Λ' with hYvdef
  set W := X * (S₀ + a • M) * Yvᵀ with hWdef
  have hZWb : ‖Z - W‖ ≤ δ := by
    rw [hZexp, hY₀, hWdef, hXdef, hYvdef, predictor_sub_factored_eq]
    refine (norm_predictor_sub_factored_le hU₀ hV₀ ha0 hK'b hΛ'b hEKb hELb hMB).trans ?_
    rw [h2a] at hδ
    linarith
  obtain ⟨Ut, hUt, hUtX⟩ := exists_orthonormal_capture_of_le_card X hrm.le
  obtain ⟨Vt, hVt, hVtY⟩ := exists_orthonormal_capture_of_le_card Yv hrn.le
  set SW := Utᵀ * X * (S₀ + a • M) * (Yvᵀ * Vt) with hSW
  have hWfac : W = Ut * SW * Vtᵀ := by
    have hYt : Yvᵀ * (Vt * Vtᵀ) = Yvᵀ := by
      have := congrArg Matrix.transpose hVtY
      rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at this
    calc W = Ut * Utᵀ * X * (S₀ + a • M) * (Yvᵀ * (Vt * Vtᵀ)) := by rw [hUtX, hYt, hWdef]
      _ = Ut * SW * Vtᵀ := by simp only [hSW, Matrix.mul_assoc]
  have hWY : ‖W - Y₀‖ ≤ ρ / 2 := by
    calc ‖W - Y₀‖ ≤ ‖W - Z‖ + ‖Z - Y₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ δ + a * B := by rw [norm_sub_rev]; exact add_le_add hZWb hZY
      _ ≤ ρ / 2 := by linarith
  have hWD : (t₀ + a, W) ∈ D := hD _ htm W (by linarith)
  have hballW : ∀ X', ‖X' - Ut * SW * Vtᵀ‖ ≤ ρ / 2 → (t₀ + a, X') ∈ D := fun X' hX' => by
    rw [← hWfac] at hX'
    exact hD _ htm X' (by linarith [norm_sub_le_norm_sub_add_norm_sub X' W Y₀])
  obtain ⟨u₁, hu₁, hUtu⟩ := exists_unit_col_orthogonal hUt hrm
  -- the part of the predictor outside `Ua`
  have hPU : (1 - Ua * Uaᵀ) * U₀ = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, augU, sub_self]
  have hPGV : (1 - Ua * Uaᵀ) * (G * V₀) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, kCap, sub_self]
  have hF₁G : ‖F₁ - G‖ ≤ a * (L * B + Lₜ) := by
    have h1 : ‖F₁ - F t₀ Z‖ ≤ L * ‖Y₀ - Z‖ := hL hY₀D (hZD t₀ ht₀)
    have h2 : ‖F t₀ Z - F (t₀ + a) Z‖ ≤ Lₜ * |t₀ - (t₀ + a)| :=
      hFt _ _ _ (hZD t₀ ht₀) (hZD _ htm)
    rw [show t₀ - (t₀ + a) = -a by ring, abs_neg, abs_of_nonneg ha0] at h2
    rw [norm_sub_rev Y₀ Z] at h1
    calc ‖F₁ - G‖ = ‖(F₁ - F t₀ Z) + (F t₀ Z - F (t₀ + a) Z)‖ := by rw [hG]; abel_nf
      _ ≤ L * ‖Z - Y₀‖ + Lₜ * a := (norm_add_le _ _).trans (add_le_add h1 h2)
      _ ≤ L * (a * B) + Lₜ * a := by gcongr
      _ = a * (L * B + Lₜ) := by ring
  have hPK : (1 - Ua * Uaᵀ) * K = (1 - Ua * Uaᵀ) * ((F₁ - G) * V₀) := by
    have e1 : (1 - U₀ * U₀ᵀ) * F₁ * V₀ = F₁ * V₀ - U₀ * (U₀ᵀ * F₁ * V₀) := by
      simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    rw [hKdef, e1, Matrix.mul_sub, ← Matrix.mul_assoc (1 - Ua * Uaᵀ) U₀, hPU, Matrix.zero_mul,
      sub_zero, Matrix.sub_mul F₁ G V₀, Matrix.mul_sub (1 - Ua * Uaᵀ) (F₁ * V₀) (G * V₀), hPGV,
      sub_zero]
  have hPKb : ‖(1 - Ua * Uaᵀ) * K‖ ≤ a * (L * B + Lₜ) := by
    rw [hPK]
    exact ((norm_one_sub_mul_le_of_orthonormal hUa _).trans
      (norm_mul_le_of_orthonormal hV₀ _)).trans hF₁G
  have hPZ : (1 - Ua * Uaᵀ) * Z = a • ((1 - Ua * Uaᵀ) * K * V₀ᵀ) := by
    rw [hZ₀, hY₀]
    simp only [Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, hPU, Matrix.zero_mul,
      zero_add, add_zero]
  have hPW : ‖(1 - Ua * Uaᵀ) * W‖ ≤ a ^ 2 * (L * B + Lₜ) + δ := by
    have e1 : (1 - Ua * Uaᵀ) * W = (1 - Ua * Uaᵀ) * Z - (1 - Ua * Uaᵀ) * (Z - W) := by
      rw [Matrix.mul_sub]; abel
    rw [e1]
    refine (norm_sub_le _ _).trans
      (add_le_add ?_ ((norm_one_sub_mul_le_of_orthonormal hUa _).trans hZWb))
    rw [hPZ, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0,
      Frobenius.norm_mul_transpose_of_orthonormal hV₀]
    calc a * ‖(1 - Ua * Uaᵀ) * K‖ ≤ a * (a * (L * B + Lₜ)) :=
          mul_le_mul_of_nonneg_left hPKb ha0
      _ = a ^ 2 * (L * B + Lₜ) := by ring
  -- the field at `W`
  set FW := F (t₀ + a) W with hFW
  have hGFW : ‖G - FW‖ ≤ L * δ := by
    rw [hG]
    exact (hL (hZD _ htm) hWD).trans (mul_le_mul_of_nonneg_left hZWb hL0)
  have hFWB : ‖FW‖ ≤ B := hB hWD
  -- the decomposition into four parts
  have hdec : (1 - Ua * Uaᵀ) * G * (1 - V₀ * V₀ᵀ) =
      (1 - Ua * Uaᵀ) * (G - FW) * (1 - V₀ * V₀ᵀ) +
        (1 - Ua * Uaᵀ) * (Ut * Utᵀ * FW * (1 - Vt * Vtᵀ)) * (1 - V₀ * V₀ᵀ) +
        (1 - Ua * Uaᵀ) * ((1 - Ut * Utᵀ) * FW * (1 - Vt * Vtᵀ)) * (1 - V₀ * V₀ᵀ) +
        (1 - Ua * Uaᵀ) * FW * (Vt * Vtᵀ) * (1 - V₀ * V₀ᵀ) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  rw [hdec]
  -- part 0: `G - F_W`
  have hT0 : ‖(1 - Ua * Uaᵀ) * (G - FW) * (1 - V₀ * V₀ᵀ)‖ ≤ L * δ :=
    ((norm_mul_one_sub_le_of_orthonormal hV₀ _).trans
      (norm_one_sub_mul_le_of_orthonormal hUa _)).trans hGFW
  -- part 1: the mixed component at `W`
  have hT1 : ‖(1 - Ua * Uaᵀ) * (Ut * Utᵀ * FW * (1 - Vt * Vtᵀ)) * (1 - V₀ * V₀ᵀ)‖ ≤
      κ * (a ^ 2 * (L * B + Lₜ) + δ) + e := by
    refine (norm_mul_one_sub_le_of_orthonormal hV₀ _).trans ?_
    have h := norm_one_sub_mul_mul_mul_one_sub_le hN hL hL0 hB hUt hVt hu₁ hUtu hρ hballW hτ hUa
    rw [← hWfac] at h
    refine h.trans (add_le_add ?_ he)
    exact mul_le_mul hκ hPW (norm_nonneg _) hκ0
  -- part 2: the normal component at `W`
  have hT2 : ‖(1 - Ua * Uaᵀ) * ((1 - Ut * Utᵀ) * FW * (1 - Vt * Vtᵀ)) * (1 - V₀ * V₀ᵀ)‖ ≤ ε := by
    refine ((norm_mul_one_sub_le_of_orthonormal hV₀ _).trans
      (norm_one_sub_mul_le_of_orthonormal hUa _)).trans ?_
    have h := hN (t₀ + a) Ut Vt SW hUt hVt (by rw [← hWfac]; exact hWD)
    rw [← hWfac] at h
    exact h
  -- part 3: the row space of `W` against `V₀`
  have hT3 : ‖(1 - Ua * Uaᵀ) * FW * (Vt * Vtᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤
      a * κ * (L * δ + a * B * κ) := by
    have hΛV : Λ'ᵀ * V₀ = 0 := by
      rw [← Matrix.transpose_transpose (Λ'ᵀ * V₀), Matrix.transpose_mul,
        Matrix.transpose_transpose, hV₀Λ', Matrix.transpose_zero]
    have hYP : Yvᵀ * (1 - V₀ * V₀ᵀ) = a • Λ'ᵀ := by
      rw [hYvdef, Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, hV₀P, zero_add,
        Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hΛV,
        Matrix.zero_mul, sub_zero]
    set Γv := (a • Λ')ᵀ * (a • Λ') + (1 : ℝ) ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ) with hΓv
    have hproj : Vt * Vtᵀ = Yv * Γv⁻¹ * Yvᵀ := mul_transpose_eq_of_capture_add hV₀ hV₀Λ' a hVtY
    have e1 : (1 - Ua * Uaᵀ) * FW * (Vt * Vtᵀ) * (1 - V₀ * V₀ᵀ) =
        a • ((1 - Ua * Uaᵀ) * FW * Yv * Γv⁻¹ * Λ'ᵀ) := by
      rw [hproj]
      simp only [Matrix.mul_assoc]
      rw [hYP]
      simp only [Matrix.mul_smul]
    have hYvF : ‖(1 - Ua * Uaᵀ) * FW * Yv‖ ≤ L * δ + a * B * κ := by
      have e2 : (1 - Ua * Uaᵀ) * FW * Yv =
          (1 - Ua * Uaᵀ) * ((FW - G) * V₀) + a • ((1 - Ua * Uaᵀ) * FW * Λ') := by
        rw [hYvdef, Matrix.mul_add, Matrix.mul_smul, Matrix.sub_mul FW G V₀,
          Matrix.mul_sub (1 - Ua * Uaᵀ) (FW * V₀) (G * V₀), hPGV, sub_zero,
          Matrix.mul_assoc (1 - Ua * Uaᵀ) FW V₀]
      rw [e2]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine ((norm_one_sub_mul_le_of_orthonormal hUa _).trans
          (norm_mul_le_of_orthonormal hV₀ _)).trans ?_
        rw [norm_sub_rev]
        exact hGFW
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0, Matrix.mul_assoc]
        calc a * ‖(1 - Ua * Uaᵀ) * (FW * Λ')‖ ≤ a * ‖FW * Λ'‖ :=
              mul_le_mul_of_nonneg_left (norm_one_sub_mul_le_of_orthonormal hUa _) ha0
          _ ≤ a * (B * κ) := by
              gcongr
              exact (Frobenius.norm_mul_le _ _).trans (mul_le_mul hFWB hΛ'b (norm_nonneg _) hB0)
          _ = a * B * κ := by ring
    rw [e1, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0]
    calc a * ‖(1 - Ua * Uaᵀ) * FW * Yv * Γv⁻¹ * Λ'ᵀ‖
        ≤ a * (‖(1 - Ua * Uaᵀ) * FW * Yv * Γv⁻¹‖ * ‖Λ'ᵀ‖) :=
          mul_le_mul_of_nonneg_left (Frobenius.norm_mul_le _ _) ha0
      _ ≤ a * ((L * δ + a * B * κ) * κ) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul
            ((norm_mul_inv_transpose_mul_self_add_one_le (a • Λ') _).trans hYvF)
            (by rw [Frobenius.norm_transpose]; exact hΛ'b) (norm_nonneg _)
            (add_nonneg (mul_nonneg hL0 hδ0) (mul_nonneg (mul_nonneg ha0 hB0) hκ0))) ha0
      _ = a * κ * (L * δ + a * B * κ) := by ring
  -- assembly
  calc _ ≤ ‖(1 - Ua * Uaᵀ) * (G - FW) * (1 - V₀ * V₀ᵀ)‖ +
        ‖(1 - Ua * Uaᵀ) * (Ut * Utᵀ * FW * (1 - Vt * Vtᵀ)) * (1 - V₀ * V₀ᵀ)‖ +
        ‖(1 - Ua * Uaᵀ) * ((1 - Ut * Utᵀ) * FW * (1 - Vt * Vtᵀ)) * (1 - V₀ * V₀ᵀ)‖ +
        ‖(1 - Ua * Uaᵀ) * FW * (Vt * Vtᵀ) * (1 - V₀ * V₀ᵀ)‖ :=
        (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ L * δ + (κ * (a ^ 2 * (L * B + Lₜ) + δ) + e) + ε + a * κ * (L * δ + a * B * κ) := by
        gcongr
    _ = _ := by ring


/-- **Capture defect on the right**, the transposed form of `norm_capture_defect_le`: under its
hypotheses on `F`, the predictor and `G`, for every `Va` with orthonormal columns whose range
contains those of `V₀` and `Gᵀ U₀`, `‖(1 - U₀ U₀ᵀ) G (1 - Va Vaᵀ)‖` has the same bound. The
proof applies `norm_capture_defect_le` to the transposed field `X ↦ F(t, Xᵀ)ᵀ`. -/
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
      (L + κ + h / 2 * L * κ) * δ + ε + e + (h / 2) ^ 2 * κ * (L * B + Lₜ + B * κ) := by
  have hpt : (V₀ * S₀ᵀ * U₀ᵀ)ᵀ = U₀ * S₀ * V₀ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  have hpt' : (U₀ * S₀ * V₀ᵀ)ᵀ = V₀ * S₀ᵀ * U₀ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have key := norm_capture_defect_le (F := fun t (X : Matrix n m ℝ) => (F t Xᵀ)ᵀ)
    (D := {p : ℝ × Matrix n m ℝ | (p.1, p.2ᵀ) ∈ D}) (U₀ := V₀) (V₀ := U₀) (S₀ := S₀ᵀ)
    (Z := Zᵀ) (G := Gᵀ) (Ua := Va) hN.transpose hL.transpose hL0
    (fun t X hX => by rw [Frobenius.norm_transpose]; exact hB hX)
    (fun s t X hs ht => by
      rw [← Matrix.transpose_sub, Frobenius.norm_transpose]
      exact hFt s t Xᵀ hs ht)
    hrn hrm hV₀ hU₀ hh hρ
    (fun t ht X hX => by
      change (t, Xᵀ) ∈ D
      refine hD t ht Xᵀ ?_
      rw [← hpt, ← Matrix.transpose_sub, Frobenius.norm_transpose]
      exact hX)
    hτ hκ he (by rw [Frobenius.norm_transpose]; exact hδ) hsmall
    (by rw [hZ, Matrix.transpose_add, hpt', Matrix.transpose_smul, transpose_tangentProj, hpt])
    (by rw [hG, Matrix.transpose_transpose]) hVa augV lCap
  have e1 : ((1 - U₀ * U₀ᵀ) * G * (1 - Va * Vaᵀ))ᵀ = (1 - Va * Vaᵀ) * Gᵀ * (1 - U₀ * U₀ᵀ) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [← Frobenius.norm_transpose, e1]
  exact key

/-- The choice `τ = h² + ε` of the free parameters of `norm_capture_defect_le`: it satisfies the
conditions on `τ`, `κ`, `e`, `δ` there, the resulting `δ` is at most `D₁ h² + D₂ ε`, and the
resulting bound is at most `C₁ h² + C₂ ε`. -/
private theorem capture_params_sq_add {r : ℕ} {ε L Lₜ B ρ H κ D₁ D₂ h s : ℝ} (hε : 0 ≤ ε)
    (hB0 : 0 ≤ B) (hL0 : 0 ≤ L) (hs : 0 ≤ s) (hh : 0 < h) (hH : h ≤ H)
    (hκ : Real.sqrt r * (1 / 2 + max L (2 * B / ρ)) ≤ κ)
    (hD₁ : Real.sqrt r * H * max L (2 * B / ρ) / 2 + (2 * κ * B + κ ^ 2 * s) / 4 +
      H * κ ^ 2 * B / 8 ≤ D₁)
    (hD₂ : Real.sqrt r * H * (1 + max L (2 * B / ρ) / 2) ≤ D₂) :
    ∃ τ e δ : ℝ, 0 < τ ∧ Real.sqrt r * (ε / (2 * τ) + max L (2 * B / ρ)) ≤ κ ∧
      Real.sqrt r * (ε + max L (2 * B / ρ) * τ / 2) ≤ e ∧
      h * e + (h / 2) ^ 2 * (2 * κ * B + κ ^ 2 * s) + (h / 2) ^ 3 * (κ ^ 2 * B) ≤ δ ∧
      δ ≤ D₁ * h ^ 2 + D₂ * ε ∧
      (L + κ + h / 2 * L * κ) * δ + ε + e + (h / 2) ^ 2 * κ * (L * B + Lₜ + B * κ) ≤
        ((L + κ + H / 2 * L * κ) * D₁ + Real.sqrt r * max L (2 * B / ρ) / 2 +
            κ * (L * B + Lₜ + B * κ) / 4) * h ^ 2 +
          ((L + κ + H / 2 * L * κ) * D₂ + 1 + Real.sqrt r * (1 + max L (2 * B / ρ) / 2)) * ε := by
  have hLm0 : 0 ≤ max L (2 * B / ρ) := hL0.trans (le_max_left _ _)
  have hq0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg _
  have hH0 : 0 ≤ H := hh.le.trans hH
  have hHh : 0 ≤ H - h := sub_nonneg.2 hH
  have hτ : 0 < h ^ 2 + ε := by positivity
  have hκ0 : 0 ≤ κ := le_trans (mul_nonneg hq0 (by linarith)) hκ
  generalize max L (2 * B / ρ) = Lm at hLm0 hκ hD₁ hD₂ ⊢
  generalize Real.sqrt r = q at hq0 hκ hD₁ hD₂ ⊢
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = q * (ε + Lm * (h ^ 2 + ε) / 2) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ,
      δ = h * e + (h / 2) ^ 2 * (2 * κ * B + κ ^ 2 * s) + (h / 2) ^ 3 * (κ ^ 2 * B) :=
    ⟨_, rfl⟩
  have he0 : 0 ≤ e := by
    rw [he]
    exact mul_nonneg hq0 (add_nonneg hε (div_nonneg (mul_nonneg hLm0 hτ.le) two_pos.le))
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    exact add_nonneg (add_nonneg (mul_nonneg hh.le he0) (mul_nonneg (sq_nonneg _)
      (add_nonneg (mul_nonneg (mul_nonneg two_pos.le hκ0) hB0) (mul_nonneg (sq_nonneg κ) hs))))
      (mul_nonneg (pow_nonneg (by linarith) 3) (mul_nonneg (sq_nonneg κ) hB0))
  have hhalf : ε / (2 * (h ^ 2 + ε)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) two_pos]
    nlinarith [sq_nonneg h]
  have hδb : δ ≤ D₁ * h ^ 2 + D₂ * ε := by
    have h1 : 0 ≤ (H - h) * (q * ε * (1 + Lm / 2)) :=
      mul_nonneg hHh (mul_nonneg (mul_nonneg hq0 hε) (by linarith))
    have h2 : 0 ≤ (H - h) * (h ^ 2 * (q * Lm / 2)) :=
      mul_nonneg hHh (mul_nonneg (sq_nonneg h) (div_nonneg (mul_nonneg hq0 hLm0) two_pos.le))
    have h3 : 0 ≤ (H - h) * (h ^ 2 * (κ ^ 2 * B / 8)) :=
      mul_nonneg hHh (mul_nonneg (sq_nonneg h) (div_nonneg (mul_nonneg (sq_nonneg κ) hB0)
        (by norm_num)))
    have h4 : (q * H * Lm / 2 + (2 * κ * B + κ ^ 2 * s) / 4 + H * κ ^ 2 * B / 8) * h ^ 2 ≤
        D₁ * h ^ 2 := mul_le_mul_of_nonneg_right hD₁ (sq_nonneg h)
    have h5 : q * H * (1 + Lm / 2) * ε ≤ D₂ * ε := mul_le_mul_of_nonneg_right hD₂ hε
    have h6 : δ = (q * H * Lm / 2 + (2 * κ * B + κ ^ 2 * s) / 4 + H * κ ^ 2 * B / 8) * h ^ 2 +
        q * H * (1 + Lm / 2) * ε - (H - h) * (q * ε * (1 + Lm / 2)) -
        (H - h) * (h ^ 2 * (q * Lm / 2)) - (H - h) * (h ^ 2 * (κ ^ 2 * B / 8)) := by
      rw [hδ, he]
      ring
    linarith
  refine ⟨h ^ 2 + ε, e, δ, hτ, ?_, he.symm.le, hδ.symm.le, hδb, ?_⟩
  · exact le_trans (mul_le_mul_of_nonneg_left (by linarith) hq0) hκ
  · have hA0 : 0 ≤ L + κ + H / 2 * L * κ :=
      add_nonneg (add_nonneg hL0 hκ0) (mul_nonneg (mul_nonneg (div_nonneg hH0 two_pos.le) hL0) hκ0)
    have h1 : (L + κ + h / 2 * L * κ) * δ ≤ (L + κ + H / 2 * L * κ) * δ := by
      refine mul_le_mul_of_nonneg_right ?_ hδ0
      have : 0 ≤ (H - h) / 2 * L * κ :=
        mul_nonneg (mul_nonneg (div_nonneg hHh two_pos.le) hL0) hκ0
      linarith
    have h2 : (L + κ + H / 2 * L * κ) * δ ≤ (L + κ + H / 2 * L * κ) * (D₁ * h ^ 2 + D₂ * ε) :=
      mul_le_mul_of_nonneg_left hδb hA0
    have h3 : e = q * Lm / 2 * h ^ 2 + q * (1 + Lm / 2) * ε := by
      rw [he]
      ring
    have h4 : (h / 2) ^ 2 * κ * (L * B + Lₜ + B * κ) = κ * (L * B + Lₜ + B * κ) / 4 * h ^ 2 := by
      ring
    have h5 : (L + κ + H / 2 * L * κ) * (D₁ * h ^ 2 + D₂ * ε) =
        (L + κ + H / 2 * L * κ) * D₁ * h ^ 2 + (L + κ + H / 2 * L * κ) * D₂ * ε := by
      ring
    have h6 : ((L + κ + H / 2 * L * κ) * D₁ + q * Lm / 2 + κ * (L * B + Lₜ + B * κ) / 4) * h ^ 2 +
        ((L + κ + H / 2 * L * κ) * D₂ + 1 + q * (1 + Lm / 2)) * ε =
        (L + κ + H / 2 * L * κ) * D₁ * h ^ 2 + (L + κ + H / 2 * L * κ) * D₂ * ε + ε +
          (q * Lm / 2 * h ^ 2 + q * (1 + Lm / 2) * ε) +
          κ * (L * B + Lₜ + B * κ) / 4 * h ^ 2 := by
      ring
    rw [h6, h4, h3]
    linarith

/-- **The capture defect is of order `h² + ε`.** The choice `τ = h² + ε` in
`norm_capture_defect_le`. Under its hypotheses on `F`, the predictor `Z`, `G` and `Ua`, let
`0 < h ≤ H`, `L̃ = max L (2B/ρ)`, `κ ≥ √r (1/2 + L̃)`,
`D₁ ≥ √r H L̃/2 + (2κB + κ²‖S₀‖)/4 + H κ² B/8`, `D₂ ≥ √r H (1 + L̃/2)`, and
`h B/2 + D₁ h² + D₂ ε ≤ ρ/2`. Then

`‖(1 - Ua Uaᵀ) G (1 - V₀ V₀ᵀ)‖ ≤ C₁ h² + C₂ ε`,

`C₁ = (L + κ + (H/2) L κ) D₁ + √r L̃/2 + κ (L B + Lₜ + B κ)/4`,
`C₂ = (L + κ + (H/2) L κ) D₂ + 1 + √r (1 + L̃/2)`.

The constants depend on `r`, `L`, `Lₜ`, `B`, `ρ`, `H` and `‖S₀‖`, and on no inverse of `S₀`. -/
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
        ((L + κ + H / 2 * L * κ) * D₂ + 1 + Real.sqrt r * (1 + max L (2 * B / ρ) / 2)) * ε := by
  have hY₀D : (t₀, U₀ * S₀ * V₀ᵀ) ∈ D :=
    hD t₀ ⟨le_rfl, by linarith⟩ _ (by rw [sub_self, norm_zero]; exact hρ.le)
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hN t₀ U₀ V₀ S₀ hU₀ hV₀ hY₀D)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB hY₀D)
  obtain ⟨τ, e, δ, hτ, hκ', he, hδ, hδb, hbound⟩ := capture_params_sq_add (Lₜ := Lₜ) hε hB0 hL0
    (norm_nonneg S₀) hh hH hκ hD₁ hD₂
  exact (norm_capture_defect_le hN hL hL0 hB hFt hrm hrn hU₀ hV₀ hh.le hρ hD hτ hκ' he hδ
    (by linarith) hZ hG hUa augU kCap).trans hbound

/-- **The capture defect on the right is of order `h² + ε`**: the choice `τ = h² + ε` in
`norm_capture_defect_right_le`, with the constants of `norm_capture_defect_le_sq_add`. -/
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
        ((L + κ + H / 2 * L * κ) * D₂ + 1 + Real.sqrt r * (1 + max L (2 * B / ρ) / 2)) * ε := by
  have hY₀D : (t₀, U₀ * S₀ * V₀ᵀ) ∈ D :=
    hD t₀ ⟨le_rfl, by linarith⟩ _ (by rw [sub_self, norm_zero]; exact hρ.le)
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hN t₀ U₀ V₀ S₀ hU₀ hV₀ hY₀D)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB hY₀D)
  obtain ⟨τ, e, δ, hτ, hκ', he, hδ, hδb, hbound⟩ := capture_params_sq_add (Lₜ := Lₜ) hε hB0 hL0
    (norm_nonneg S₀) hh hH hκ hD₁ hD₂
  exact (norm_capture_defect_right_le hN hL hL0 hB hFt hrm hrn hU₀ hV₀ hh.le hρ hD hτ hκ' he hδ
    (by linarith) hZ hG hVa augV lCap).trans hbound

end Capture

/-! ### Non-vacuity -/

namespace CaptureDefectExamples

/-- The first unit column of `ℝ³`. -/
private noncomputable def e₁ : Matrix (Fin 3) (Fin 1) ℝ := !![1; 0; 0]

/-- The first unit column of `ℝ²`. -/
private noncomputable def f₁ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The second unit column of `ℝ²`. -/
private noncomputable def f₂ : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]

/-- The orthonormal unit column `(4/5, 3/5)` of `ℝ²`. -/
private noncomputable def g₁ : Matrix (Fin 2) (Fin 1) ℝ := !![4 / 5; 3 / 5]

/-- The left basis `[e₁, e₂]` of `ℝ³`. -/
private noncomputable def left₂ : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; 0, 0]

/-- A constant field whose third row leaves the left basis `[e₁, e₂]`. -/
private noncomputable def C : Matrix (Fin 3) (Fin 2) ℝ := !![0, 1 / 2; 1 / 2, 0; 0, 1 / 2]

private theorem e₁_orth : e₁ᵀ * e₁ = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  fin_cases i; fin_cases j
  norm_num [e₁]

private theorem f₁_orth : f₁ᵀ * f₁ = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  fin_cases i; fin_cases j
  norm_num [f₁]

private theorem left₂_orth : left₂ᵀ * left₂ = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> norm_num [left₂]

private theorem left₂_augU : left₂ * left₂ᵀ * e₁ = e₁ := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> norm_num [left₂, e₁]

private theorem left₂_kCap : left₂ * left₂ᵀ * (C * f₁) = C * f₁ := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> norm_num [left₂, C, f₁]

private theorem norm_C_sq : ‖C‖ ^ 2 = 3 / 4 := by
  rw [Frobenius.norm_sq_eq_sum]
  simp only [Fin.sum_univ_three, Fin.sum_univ_two]
  norm_num [C]

private theorem norm_one_one : ‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖ = 1 := by
  have h : ‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖ ^ 2 = 1 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp
  nlinarith [norm_nonneg (1 : Matrix (Fin 1) (Fin 1) ℝ)]

/-- **Non-vacuity of `norm_capture_defect_le`** with the constants written out: the constant
field `F ≡ C = [[0, 1/2], [1/2, 0], [0, 1/2]]` (`ε = B = ‖C‖ = √3/2`, `L = Lₜ = 0`) on the whole
space, the start `Y₀ = e₁ f₁ᵀ`, `h = 1`, `ρ = 8`, `τ = 1`, the basis `Ua = [e₁, e₂]`, and
`κ = 3‖C‖/4`, `e = 9‖C‖/8`, `δ = 9‖C‖/8 + 33‖C‖²/64 + 9‖C‖³/128`. -/
example : ‖(1 - left₂ * left₂ᵀ) * C * (1 - f₁ * f₁ᵀ)‖ ≤
    (0 + 3 / 4 * ‖C‖ + 1 / 2 * 0 * (3 / 4 * ‖C‖)) *
        (9 / 8 * ‖C‖ + 33 / 64 * ‖C‖ ^ 2 + 9 / 128 * ‖C‖ ^ 3) +
      ‖C‖ + 9 / 8 * ‖C‖ + (1 / 2) ^ 2 * (3 / 4 * ‖C‖) * (0 * ‖C‖ + 0 + ‖C‖ * (3 / 4 * ‖C‖)) := by
  have hc0 := norm_nonneg C
  have hc1 : ‖C‖ ≤ 1 := by nlinarith [norm_C_sq]
  have hc2 : ‖C‖ ^ 2 ≤ 1 := by nlinarith
  have hc3 : ‖C‖ ^ 3 ≤ 1 := by nlinarith
  have hmax : max (0 : ℝ) (2 * ‖C‖ / 8) = ‖C‖ / 4 := by
    rw [max_eq_right (by positivity)]; ring
  have hsq : Real.sqrt ((1 : ℕ) : ℝ) = 1 := by simp
  refine norm_capture_defect_le (F := fun _ _ => C) (D := univ) (L := 0) (Lₜ := 0)
    (B := ‖C‖) (ρ := 8) (τ := 1) (r := 1) (U₀ := e₁) (S₀ := 1) (V₀ := f₁) (t₀ := 0) (h := 1)
    (G := C) (Ua := left₂) (κ := 3 / 4 * ‖C‖) (e := 9 / 8 * ‖C‖)
    (δ := 9 / 8 * ‖C‖ + 33 / 64 * ‖C‖ ^ 2 + 9 / 128 * ‖C‖ ^ 3)
    (factoredNormalBound_iff_univ.1 (MatrixBUG.factoredNormalBound_const C 1))
    (by intro _ _ _ _ _; simp) le_rfl (by intro _ _ _; exact le_rfl) (fun _ _ _ _ _ => by simp)
    (by simp) (by simp) e₁_orth f₁_orth zero_le_one (by norm_num) (fun _ _ _ _ => mem_univ _)
    one_pos ?_ ?_ ?_ ?_ rfl rfl left₂_orth left₂_augU left₂_kCap
  · rw [hsq, hmax]; linarith
  · rw [hsq, hmax]; linarith
  · rw [norm_one_one]; exact le_of_eq (by ring)
  · linarith

/-- **Non-vacuity of `norm_capture_defect_right_le`** on the transposed data, with the constants
of the previous example: the constant field `F ≡ Cᵀ` on `2 × 3` matrices (`ε = B = ‖Cᵀ‖ = ‖C‖`),
the start `f₁ e₁ᵀ`, the right basis `Va = [e₁, e₂]`. -/
example : ‖(1 - f₁ * f₁ᵀ) * Cᵀ * (1 - left₂ * left₂ᵀ)‖ ≤
    (0 + 3 / 4 * ‖C‖ + 1 / 2 * 0 * (3 / 4 * ‖C‖)) *
        (9 / 8 * ‖C‖ + 33 / 64 * ‖C‖ ^ 2 + 9 / 128 * ‖C‖ ^ 3) +
      ‖C‖ + 9 / 8 * ‖C‖ + (1 / 2) ^ 2 * (3 / 4 * ‖C‖) * (0 * ‖C‖ + 0 + ‖C‖ * (3 / 4 * ‖C‖)) := by
  have hc0 := norm_nonneg C
  have hc1 : ‖C‖ ≤ 1 := by nlinarith [norm_C_sq]
  have hc2 : ‖C‖ ^ 2 ≤ 1 := by nlinarith
  have hc3 : ‖C‖ ^ 3 ≤ 1 := by nlinarith
  have hmax : max (0 : ℝ) (2 * ‖C‖ / 8) = ‖C‖ / 4 := by
    rw [max_eq_right (by positivity)]; ring
  have hsq : Real.sqrt ((1 : ℕ) : ℝ) = 1 := by simp
  have hCt : ‖Cᵀ‖ = ‖C‖ := Frobenius.norm_transpose C
  refine norm_capture_defect_right_le (F := fun _ _ => Cᵀ) (D := univ) (L := 0)
    (Lₜ := 0) (B := ‖C‖) (ρ := 8) (τ := 1) (r := 1) (U₀ := f₁) (S₀ := 1) (V₀ := e₁) (t₀ := 0)
    (h := 1) (G := Cᵀ) (Va := left₂) (ε := ‖C‖) (κ := 3 / 4 * ‖C‖) (e := 9 / 8 * ‖C‖)
    (δ := 9 / 8 * ‖C‖ + 33 / 64 * ‖C‖ ^ 2 + 9 / 128 * ‖C‖ ^ 3)
    (hCt ▸ factoredNormalBound_iff_univ.1 (MatrixBUG.factoredNormalBound_const Cᵀ 1))
    (by intro _ _ _ _ _; simp) le_rfl (by intro _ _ _; exact hCt.le) (fun _ _ _ _ _ => by simp)
    (by simp) (by simp) f₁_orth e₁_orth zero_le_one (by norm_num) (fun _ _ _ _ => mem_univ _)
    one_pos ?_ ?_ ?_ ?_ rfl rfl left₂_orth left₂_augU
    (by rw [Matrix.transpose_transpose]; exact left₂_kCap)
  · rw [hsq, hmax]; linarith
  · rw [hsq, hmax]; linarith
  · rw [norm_one_one]; exact le_of_eq (by ring)
  · linarith

/-- **Non-vacuity of `norm_capture_defect_le_sq_add`**: the data of the example for
`norm_capture_defect_le` (constant field `F ≡ C`, `ε = B = ‖C‖`, `L = Lₜ = 0`, start
`Y₀ = e₁ f₁ᵀ`, basis `Ua = [e₁, e₂]`, `ρ = 8`) with `h = H = 1/2`, `κ = D₁ = D₂ = 1`. The left
side is `1/2` (the entry `(e₃, f₂)` of `C`). -/
example : ‖(1 - left₂ * left₂ᵀ) * C * (1 - f₁ * f₁ᵀ)‖ ≤
    (1 + 3 / 8 * ‖C‖) / 4 + (3 + ‖C‖ / 8) * ‖C‖ := by
  have hc0 := norm_nonneg C
  have hc1 : ‖C‖ ≤ 1 := by nlinarith [norm_C_sq]
  have hmax : max (0 : ℝ) (2 * ‖C‖ / 8) = ‖C‖ / 4 := by
    rw [max_eq_right (by positivity)]; ring
  have hsq : Real.sqrt ((1 : ℕ) : ℝ) = 1 := by simp
  refine (norm_capture_defect_le_sq_add (F := fun _ _ => C) (D := univ) (L := 0) (Lₜ := 0)
    (B := ‖C‖) (ρ := 8) (H := 1 / 2) (κ := 1) (D₁ := 1) (D₂ := 1) (r := 1) (U₀ := e₁)
    (S₀ := 1) (V₀ := f₁) (t₀ := 0) (h := 1 / 2) (G := C) (Ua := left₂)
    (factoredNormalBound_iff_univ.1 (MatrixBUG.factoredNormalBound_const C 1))
    (by intro _ _ _ _ _; simp) le_rfl (by intro _ _ _; exact le_rfl) (fun _ _ _ _ _ => by simp)
    (by simp) (by simp) e₁_orth f₁_orth (by norm_num) le_rfl (by norm_num)
    (fun _ _ _ _ => mem_univ _) ?_ ?_ ?_ ?_ rfl rfl left₂_orth left₂_augU left₂_kCap).trans ?_
  · rw [hsq, hmax]
    linarith
  · rw [hsq, hmax, norm_one_one]
    nlinarith
  · rw [hsq, hmax]
    nlinarith
  · nlinarith
  · rw [hsq, hmax]
    nlinarith

/-- **Non-vacuity of `norm_capture_defect_right_le_sq_add`** on the transposed data: the constant
field `F ≡ Cᵀ` on `2 × 3` matrices, the start `f₁ e₁ᵀ`, the right basis `Va = [e₁, e₂]`, and the
parameters of the previous example. -/
example : ‖(1 - f₁ * f₁ᵀ) * Cᵀ * (1 - left₂ * left₂ᵀ)‖ ≤
    (1 + 3 / 8 * ‖C‖) / 4 + (3 + ‖C‖ / 8) * ‖C‖ := by
  have hc0 := norm_nonneg C
  have hc1 : ‖C‖ ≤ 1 := by nlinarith [norm_C_sq]
  have hmax : max (0 : ℝ) (2 * ‖C‖ / 8) = ‖C‖ / 4 := by
    rw [max_eq_right (by positivity)]; ring
  have hsq : Real.sqrt ((1 : ℕ) : ℝ) = 1 := by simp
  have hCt : ‖Cᵀ‖ = ‖C‖ := Frobenius.norm_transpose C
  refine (norm_capture_defect_right_le_sq_add (F := fun _ _ => Cᵀ) (D := univ) (L := 0)
    (Lₜ := 0) (B := ‖C‖) (ρ := 8) (H := 1 / 2) (κ := 1) (D₁ := 1) (D₂ := 1) (r := 1)
    (U₀ := f₁) (S₀ := 1) (V₀ := e₁) (t₀ := 0) (h := 1 / 2) (G := Cᵀ) (Va := left₂) (ε := ‖C‖)
    (hCt ▸ factoredNormalBound_iff_univ.1 (MatrixBUG.factoredNormalBound_const Cᵀ 1))
    (by intro _ _ _ _ _; simp) le_rfl (by intro _ _ _; exact hCt.le) (fun _ _ _ _ _ => by simp)
    (by simp) (by simp) f₁_orth e₁_orth (by norm_num) le_rfl (by norm_num)
    (fun _ _ _ _ => mem_univ _) ?_ ?_ ?_ ?_ rfl rfl left₂_orth left₂_augU
    (by rw [Matrix.transpose_transpose]; exact left₂_kCap)).trans ?_
  · rw [hsq, hmax]
    linarith
  · rw [hsq, hmax, norm_one_one]
    nlinarith
  · rw [hsq, hmax]
    nlinarith
  · nlinarith
  · rw [hsq, hmax]
    nlinarith


/-- **Non-vacuity of the regularized splitting** (`norm_mul_inv_mul_transpose_le`,
`norm_smul_mul_inv_le`): `K = S = I₂` satisfies the column bound with `ε = 0`, `L = 1`. -/
example :
    ‖(1 : Matrix (Fin 2) (Fin 2) ℝ) * (((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1 +
        (1 : ℝ) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)‖ ≤
        Real.sqrt (2 : ℕ) * (0 / (2 * 1) + 1) ∧
      ‖(1 : ℝ) ^ 2 • ((1 : Matrix (Fin 2) (Fin 2) ℝ) * ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1 +
        (1 : ℝ) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹)‖ ≤ Real.sqrt (2 : ℕ) * (0 + 1 * 1 / 2) :=
  ⟨norm_mul_inv_mul_transpose_le le_rfl zero_le_one one_pos fun c => by simp,
    norm_smul_mul_inv_le le_rfl zero_le_one one_pos fun c => by simp⟩

/-- **Non-vacuity of `norm_le_sqrt_card_mul_of_forall_mul_single_le`**: the identity of `ℝ²`. -/
example : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤ Real.sqrt (Fintype.card (Fin 2)) * 1 :=
  norm_le_sqrt_card_mul_of_forall_mul_single_le zero_le_one fun j => by
    rw [Matrix.one_mul, norm_single_one]

/-- **Non-vacuity of `mul_transpose_eq_of_capture_add`**: `V₀ = f₁`, `Λ' = f₂`, `a = 3/4`; the
column `(4/5, 3/5)` is an orthonormal basis of the range of `f₁ + (3/4) f₂`. -/
example : g₁ * g₁ᵀ = (f₁ + (3 / 4 : ℝ) • f₂) *
    (((3 / 4 : ℝ) • f₂)ᵀ * ((3 / 4 : ℝ) • f₂) + (1 : ℝ) ^ 2 • (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ *
      (f₁ + (3 / 4 : ℝ) • f₂)ᵀ := by
  refine mul_transpose_eq_of_capture_add f₁_orth ?_ _ ?_
  · ext i j
    fin_cases i; fin_cases j
    simp [f₁, f₂, Matrix.mul_apply]
  · ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.transpose_apply,
      Matrix.add_apply, Matrix.smul_apply]
    fin_cases i <;> fin_cases j <;> norm_num [g₁, f₁, f₂]

end CaptureDefectExamples

end LeanDLRA
