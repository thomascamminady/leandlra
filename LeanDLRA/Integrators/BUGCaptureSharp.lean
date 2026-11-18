import LeanDLRA.Integrators.BUGCapture
import LeanDLRA.Integrators.ProjectorSplitting

/-!
# Lower bounds for the constants of the BUG capture estimate and of the local error

The local error bound of the BUG integrator (`IsBUGStep.local_error_two_mul`) is

  `‖Y₁ - A(t₁)‖ ≤ (e^{L h} - 1) (B h + √2 ϑ) + √2 ϑ`,   `ϑ = h (2 L B h + ε)`,

and it rests on the capture estimate `‖(1 - P₁) A(t₁)‖ ≤ h (2 L B h + ε)`
(`kstep_capture_two_mul`). This file has examples on `ℂ`, as a real inner product space of
dimension two, that bound the constants from below.

## Main results

* `BUGCaptureExample.isBUGStep_const`, `BUGCaptureExample.norm_sub_eq_local_error_two_mul`: for
  the constant field `ε (1 + i)` (`L = 0`), the zero old projectors and the new projectors onto
  the real and the imaginary axis, the bound of `IsBUGStep.local_error_two_mul` is an equality,
  `‖Y₁ - A(t₁)‖ = √2 h ε`, for every `ε ≥ 0` and `h ≥ 0`.
* `exists_isBUGStep_mul_lt_norm_sub`: for every `c < √2` there is a BUG step with `L = 0` and
  `c h ε < ‖Y₁ - A(t₁)‖`. The factor `√2` of `ε` cannot be lowered.
* `BUGCaptureExample.kstep_hypotheses`, `BUGCaptureExample.norm_one_sub_reProj_curve`: for the
  field `F(x) = 1 + i L min(|Re x|, 1)`, which is `L`-Lipschitz and bounded by `√(1 + L²)`, the
  hypotheses of `kstep_capture_two_mul` hold with `h = 1`, `ε = 0`, and
  `‖(1 - P₁) A(t₁)‖ = L / 2`.
* `exists_kstep_mul_lt_norm`: for every `c < 1 / 2` there are data with `ε = 0` and
  `h (c L B h) < ‖(1 - P₁) A(t₁)‖`. The constant `2` of `kstep_capture_two_mul` cannot be
  replaced by a number below `1 / 2`.

## Implementation notes

In the first example the two capture errors `(1 - P₁) A(t₁)` and `P₁ (1 - Q₁) A(t₁)` are
orthogonal and both of the size `h ε`, which is the case of equality in the orthogonal
combination behind `bug_capture_two_mul`. The projectors `P₁`, `Q₁` commute and `P₁ Q₁ = 0`; for
matrices the same configuration is `F = ε (e₂ e₃ᵀ + e₃ e₂ᵀ)` at `Y₀ = e₁ e₁ᵀ` with the left and
the right projector onto the span of `e₁`, `e₂`, which is not formalized here. Whether a
constant between `1 / 2` and `2` is the smallest one in the capture estimate is not settled
here.
-/

open Set

namespace LeanDLRA

namespace BUGCaptureExample

open KSLExample

/-- The complement of the projector onto the real axis is the projector onto the imaginary
axis. -/
lemma one_sub_reProj_apply (z : ℂ) : (1 - reProj) z = (z.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [reProj_apply]

/-- The zero curve solves `y' = F(t, y)` if `F(t, 0) = 0`. -/
lemma odeSolution_zero {F : ℝ → ℂ → ℂ} (hF : ∀ t, F t 0 = 0) (a b : ℝ) :
    ODESolution F (fun _ => (0 : ℂ)) a b :=
  ⟨continuousOn_const, fun t _ => by rw [hF]; exact hasDerivWithinAt_const _ _ _⟩

/-- **A BUG step with orthogonal capture errors.** On `ℂ` with the constant field `ε (1 + i)`,
the old projectors `P₀ = Q₀ = 0`, the new projectors `P₁` onto the real axis and `Q₁ = 1 - P₁`
onto the imaginary axis, and all three substep trajectories equal to zero. The normal components
`(1 - P₁) (1 - Q₀) F = ε i` and `(1 - Q₁) (1 - P₀) F = ε` have the norm `ε`. -/
theorem isBUGStep_const {ε : ℝ} (hε : 0 ≤ ε) (h : ℝ) :
    IsBUGStep (E := ℂ) (fun _ _ => (ε : ℂ) * (1 + Complex.I)) ε 0 0 reProj (1 - reProj) 0 h 0
      (fun _ => 0) (fun _ => 0) (fun _ => 0) where
  projP₀ := IsOrthProj.zero
  projQ₀ := IsOrthProj.zero
  projP₁ := isOrthProj_reProj
  projQ₁ := isOrthProj_reProj.compl
  comm₁ x := by
    rw [one_sub_reProj_apply, one_sub_reProj_apply]
    simp [reProj_apply]
  kSol := odeSolution_zero (fun _ => by simp) _ _
  kStart := rfl
  kCap := by simp
  kNormal _ _ := by
    rw [one_sub_reProj_apply]
    simp [abs_of_nonneg hε]
  lSol := odeSolution_zero (fun _ => by simp) _ _
  lStart := rfl
  lCap := by simp
  lNormal _ _ := by
    simp [reProj_apply, abs_of_nonneg hε]
  sSol := odeSolution_zero (fun _ => by
    rw [one_sub_reProj_apply]
    simp [reProj_apply]) _ _
  sStart := by simp

/-- `‖ε (1 + i)‖ = √2 ε` for `ε ≥ 0`. -/
lemma norm_mul_one_add_I {ε : ℝ} (hε : 0 ≤ ε) : ‖(ε : ℂ) * (1 + Complex.I)‖ = √2 * ε := by
  have h1 : ‖(1 : ℂ) + Complex.I‖ = √2 := by
    have h := Complex.norm_add_mul_I 1 1
    simp only [Complex.ofReal_one, one_mul, one_pow] at h
    rw [h]
    norm_num
  rw [norm_mul, h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε, mul_comm]

/-- **The local error bound of the BUG integrator is attained for `L = 0`.** For the step
`isBUGStep_const` and the exact solution `A t = t ε (1 + i)` the bound of
`IsBUGStep.local_error_two_mul` with `L = 0` and `B = √2 ε` is an equality. -/
theorem norm_sub_eq_local_error_two_mul {ε h : ℝ} (hε : 0 ≤ ε) (hh : 0 ≤ h) :
    ‖(fun _ : ℝ => (0 : ℂ)) h - (fun t : ℝ => 0 + (t : ℂ) * ((ε : ℂ) * (1 + Complex.I))) h‖ =
      (Real.exp (0 * h) - 1) * (√2 * ε * h + √2 * (h * (2 * 0 * (√2 * ε) * h + ε)))
        + √2 * (h * (2 * 0 * (√2 * ε) * h + ε)) := by
  have h1 : ‖(fun _ : ℝ => (0 : ℂ)) h -
      (fun t : ℝ => 0 + (t : ℂ) * ((ε : ℂ) * (1 + Complex.I))) h‖ = h * (√2 * ε) := by
    simp only [zero_add, zero_sub, norm_neg]
    rw [norm_mul, norm_mul_one_add_I hε, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh]
  rw [h1]
  simp
  ring

/-- The constant field `ε (1 + i)` is Lipschitz with the constant `0` and bounded by `√2 ε`, and
`A t = t ε (1 + i)` is the solution from `0`. -/
theorem field_const_hypotheses {ε : ℝ} (hε : 0 ≤ ε) (h : ℝ) :
    IsLipschitzField (E := ℂ) (fun _ _ => (ε : ℂ) * (1 + Complex.I)) 0 ∧
      IsBoundedField (E := ℂ) (fun _ _ => (ε : ℂ) * (1 + Complex.I)) (√2 * ε) ∧
      ODESolution (fun _ _ => (ε : ℂ) * (1 + Complex.I))
        (fun t : ℝ => 0 + (t : ℂ) * ((ε : ℂ) * (1 + Complex.I))) 0 h :=
  ⟨fun _ _ _ => by simp, fun _ _ => (norm_mul_one_add_I hε).le,
    odeSolution_affine (fun _ _ => rfl) _ _ _⟩

/-- `IsBUGStep.local_error_two_mul` applies to the step `isBUGStep_const`, and its bound is the
norm of the error. -/
example {ε h : ℝ} (hε : 0 ≤ ε) (hh : 0 ≤ h) :
    ‖(fun _ : ℝ => (0 : ℂ)) h - (fun t : ℝ => 0 + (t : ℂ) * ((ε : ℂ) * (1 + Complex.I))) h‖ ≤
      (Real.exp (0 * h) - 1) * (√2 * ε * h + √2 * (h * (2 * 0 * (√2 * ε) * h + ε)))
        + √2 * (h * (2 * 0 * (√2 * ε) * h + ε)) := by
  have hf := field_const_hypotheses hε h
  exact (isBUGStep_const hε h).local_error_two_mul (L := 0) (B := √2 * ε) (h := h)
    (A := fun t : ℝ => 0 + (t : ℂ) * ((ε : ℂ) * (1 + Complex.I))) hf.1 le_rfl hf.2.1
    (zero_add h).symm hh hf.2.2 (by simp)

/-! ### The capture estimate -/

/-- The field `F(x) = 1 + i L min(|Re x|, 1)`. -/
noncomputable def shearField (L : ℝ) : ℝ → ℂ → ℂ :=
  fun _ x => 1 + ((L * min |x.re| 1 : ℝ) : ℂ) * Complex.I

/-- The solution `A t = t + i L t² / 2` of `Ȧ = shearField L A` from `0`, on `[0, 1]`. -/
noncomputable def shearCurve (L : ℝ) : ℝ → ℂ :=
  fun t => (t : ℂ) + ((L * t ^ 2 / 2 : ℝ) : ℂ) * Complex.I

/-- The field `shearField L` is `L`-Lipschitz. -/
theorem isLipschitzField_shearField {L : ℝ} (hL : 0 ≤ L) : IsLipschitzField (shearField L) L := by
  intro t x y
  have e : shearField L t x - shearField L t y =
      ((L * (min |x.re| 1 - min |y.re| 1) : ℝ) : ℂ) * Complex.I := by
    simp only [shearField]
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hL]
  refine mul_le_mul_of_nonneg_left ?_ hL
  have h1 : |min |x.re| 1 - min |y.re| 1| ≤ max |(|x.re| - |y.re|)| |(1 : ℝ) - 1| :=
    abs_min_sub_min_le_max _ _ _ _
  have h2 : |(|x.re| - |y.re|)| ≤ |x.re - y.re| := abs_abs_sub_abs_le _ _
  have h3 : |x.re - y.re| ≤ ‖x - y‖ := by
    rw [← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at h1
  linarith

/-- The field `shearField L` is bounded by `√(1 + L²)`. -/
theorem isBoundedField_shearField {L : ℝ} (hL : 0 ≤ L) :
    IsBoundedField (shearField L) √(1 + L ^ 2) := by
  intro t x
  have h := Complex.norm_add_mul_I 1 (L * min |x.re| 1)
  simp only [Complex.ofReal_one] at h
  simp only [shearField]
  rw [h]
  refine Real.sqrt_le_sqrt ?_
  have h0 : 0 ≤ min |x.re| 1 := le_min (abs_nonneg _) zero_le_one
  have h1 : min |x.re| 1 ≤ 1 := min_le_right _ _
  nlinarith [mul_nonneg hL h0, mul_le_mul_of_nonneg_left h1 hL]

/-- The curve `shearCurve L` solves `Ȧ = shearField L A` on `[0, 1]`. -/
theorem odeSolution_shearCurve (L : ℝ) : ODESolution (shearField L) (shearCurve L) 0 1 := by
  have hd : ∀ t : ℝ, HasDerivAt (shearCurve L) (1 + ((L * t : ℝ) : ℂ) * Complex.I) t := by
    intro t
    have hf : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have hg : HasDerivAt (fun s : ℝ => L * s ^ 2 / 2) (L * t) t := by
      have h := (hasDerivAt_pow 2 t).const_mul (L / 2)
      convert h using 1
      · funext s
        ring
      · simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
        ring
    have h3 := hf.ofReal_comp.add (hg.ofReal_comp.mul_const Complex.I)
    have e : (1 : ℂ) + ((L * t : ℝ) : ℂ) * Complex.I =
        ((1 : ℝ) : ℂ) + ((L * t : ℝ) : ℂ) * Complex.I := by
      rw [Complex.ofReal_one]
    rw [e]
    exact h3
  refine ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t ht => ?_⟩
  have e : shearField L t (shearCurve L t) = 1 + ((L * t : ℝ) : ℂ) * Complex.I := by
    simp only [shearField, shearCurve]
    have hre : ((t : ℂ) + ((L * t ^ 2 / 2 : ℝ) : ℂ) * Complex.I).re = t := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im]
      ring
    rw [hre, abs_of_nonneg ht.1, min_eq_left ht.2.le]
  rw [e]
  exact (hd t).hasDerivWithinAt

/-- **The hypotheses of `kstep_capture_two_mul` for the field `shearField L`**, with `Q₀ = 0`,
the K-step trajectory `0`, `P₁` the projector onto the real axis, `h = 1` and `ε = 0`. -/
theorem kstep_hypotheses {L : ℝ} (hL : 0 ≤ L) :
    IsLipschitzField (shearField L) L ∧ IsBoundedField (shearField L) √(1 + L ^ 2) ∧
      ODESolution (shearField L) (shearCurve L) 0 1 ∧
      ODESolution (fun t x => (0 : ℂ →L[ℝ] ℂ) (shearField L t x)) (fun _ => (0 : ℂ)) 0 1 ∧
      (fun _ : ℝ => (0 : ℂ)) 0 = shearCurve L 0 ∧
      reProj ((fun _ : ℝ => (0 : ℂ)) 1) = (fun _ : ℝ => (0 : ℂ)) 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ‖(1 - reProj) ((1 - (0 : ℂ →L[ℝ] ℂ))
        (shearField L t ((fun _ : ℝ => (0 : ℂ)) 1)))‖ ≤ 0 := by
  refine ⟨isLipschitzField_shearField hL, isBoundedField_shearField hL, odeSolution_shearCurve L,
    odeSolution_zero (fun _ => by simp) _ _, by simp [shearCurve], by simp, fun t _ => ?_⟩
  rw [one_sub_reProj_apply]
  simp [shearField]

/-- **The capture error of the field `shearField L`** is `‖(1 - P₁) A(1)‖ = L / 2`. -/
theorem norm_one_sub_reProj_curve {L : ℝ} (hL : 0 ≤ L) :
    ‖(1 - reProj) (shearCurve L 1)‖ = L / 2 := by
  rw [one_sub_reProj_apply]
  simp only [shearCurve]
  have him : (((1 : ℝ) : ℂ) + ((L * 1 ^ 2 / 2 : ℝ) : ℂ) * Complex.I).im = L / 2 := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.ofReal_re, Complex.I_im]
    ring
  rw [him, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

/-- `kstep_capture_two_mul` applies to the field `shearField L`: `L / 2 ≤ 2 L √(1 + L²)`. -/
example {L : ℝ} (hL : 0 ≤ L) :
    ‖(1 - reProj) (shearCurve L 1)‖ ≤ 1 * (2 * L * √(1 + L ^ 2) * 1 + 0) := by
  obtain ⟨hF, hB, hA, hK, hK₀, hKcap, hε⟩ := kstep_hypotheses hL
  exact kstep_capture_two_mul hF hL hB isOrthProj_reProj IsOrthProj.zero (zero_add 1).symm
    zero_le_one hA hK hK₀ hKcap hε

end BUGCaptureExample

open BUGCaptureExample KSLExample

/-- **The factor `√2` of `ε` in the local error bound of the BUG integrator cannot be lowered.**
For every `c < √2` there is a BUG step on `[0, 1]` with normal components bounded by `ε = 1`,
for a field with the Lipschitz constant `L = 0`, such that the error exceeds `c h ε = c`, where
`IsBUGStep.local_error_two_mul` gives the bound `√2 h ε`. -/
theorem exists_isBUGStep_mul_lt_norm_sub {c : ℝ} (hc : c < √2) :
    ∃ (F : ℝ → ℂ → ℂ) (P₀ Q₀ P₁ Q₁ : ℂ →L[ℝ] ℂ) (YK YL YS A : ℝ → ℂ) (B : ℝ),
      IsBUGStep F 1 P₀ Q₀ P₁ Q₁ 0 1 0 YK YL YS ∧ IsLipschitzField F 0 ∧ IsBoundedField F B ∧
        ODESolution F A 0 1 ∧ A 0 = 0 ∧ c * (1 * 1) < ‖YS 1 - A 1‖ := by
  have hf := field_const_hypotheses (ε := 1) zero_le_one 1
  have hn := norm_sub_eq_local_error_two_mul (ε := 1) (h := 1) zero_le_one zero_le_one
  refine ⟨_, _, _, _, _, _, _, _, _, _, isBUGStep_const zero_le_one 1, hf.1, hf.2.1, hf.2.2,
    by simp, ?_⟩
  rw [hn]
  simp only [zero_mul, Real.exp_zero, sub_self, mul_zero, zero_add, mul_one]
  linarith

/-- **The constant `2` of the K-step capture estimate cannot be replaced by a number below
`1 / 2`.** For every `c < 1 / 2` there are a field with a Lipschitz constant `L > 0` and a bound
`B`, and data that satisfy the hypotheses of `kstep_capture_two_mul` with `h = 1` and `ε = 0`,
such that `h (c L B h + ε) < ‖(1 - P₁) A(t₁)‖`. -/
theorem exists_kstep_mul_lt_norm {c : ℝ} (hc : c < 1 / 2) :
    ∃ (F : ℝ → ℂ → ℂ) (P₁ Q₀ : ℂ →L[ℝ] ℂ) (YK A : ℝ → ℂ) (L B : ℝ),
      0 < L ∧ IsLipschitzField F L ∧ IsBoundedField F B ∧ IsOrthProj P₁ ∧ IsOrthProj Q₀ ∧
        ODESolution F A 0 1 ∧ ODESolution (fun t x => Q₀ (F t x)) YK 0 1 ∧ YK 0 = A 0 ∧
        P₁ (YK 1) = YK 1 ∧ (∀ t ∈ Icc (0 : ℝ) 1, ‖(1 - P₁) ((1 - Q₀) (F t (YK 1)))‖ ≤ 0) ∧
        1 * (c * L * B * 1 + 0) < ‖(1 - P₁) (A 1)‖ := by
  obtain ⟨L, hL, hLc⟩ : ∃ L : ℝ, 0 < L ∧ c * (1 + L) < 1 / 2 := by
    rcases le_or_gt c 0 with h0 | h0
    · exact ⟨1, one_pos, by nlinarith⟩
    · refine ⟨(1 / (2 * c) - 1) / 2, ?_, ?_⟩
      · have : 1 < 1 / (2 * c) := by
          rw [lt_div_iff₀ (by positivity)]
          linarith
        linarith
      · have h1 : c * (1 / (2 * c)) = 1 / 2 := by
          field_simp
        nlinarith
  obtain ⟨hF, hB, hA, hK, hK₀, hKcap, hε⟩ := kstep_hypotheses hL.le
  refine ⟨_, _, _, _, _, L, _, hL, hF, hB, isOrthProj_reProj, IsOrthProj.zero, hA, hK, hK₀,
    hKcap, hε, ?_⟩
  rw [norm_one_sub_reProj_curve hL.le]
  have hs : √(1 + L ^ 2) ≤ 1 + L := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hs0 : 0 ≤ √(1 + L ^ 2) := Real.sqrt_nonneg _
  rcases le_or_gt c 0 with h0 | h0
  · have : c * L * √(1 + L ^ 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h0 hL.le) hs0
    linarith
  · have h1 : c * L * √(1 + L ^ 2) ≤ c * L * (1 + L) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    nlinarith

end LeanDLRA
