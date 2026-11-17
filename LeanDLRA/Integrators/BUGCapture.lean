import LeanDLRA.Integrators.BUGCore
import LeanDLRA.Classical.CommutingProjectorTelescoping

/-!
# The capture estimate of the BUG integrator with smaller constants

The robust local error bound of the BUG integrator ([CerutiLubich2022, Lemmas 2–4];
`IsBUGStep.local_error`) rests on the K-step capture estimate
`‖(1 - P₁) A(t₁)‖ ≤ h (4 L B h + ε)` (`kstep_capture`). This file proves the same estimate with
`2 L B h` in place of `4 L B h`, and combines it with the orthogonal (Pythagorean) combination of
the left and the right capture errors (`IsOrthProj.norm_sub_apply_sq`). The result is the local
error bound

  `‖Y₁ - A(t₁)‖ ≤ (e^{L h} - 1) (B h + √2 ϑ) + √2 ϑ`,   `ϑ = h (2 L B h + ε)`,

compared with `ϑ = h (4 L B h + ε)` and the factor `2` in place of `√2` in
`IsBUGStep.local_error`. In the `O`-form `h (c₁ ε + c₂ h)` the constants become
`c₁ = √2 (1 + L H e^{L H})` (for `bugC₁ L H = 2 (1 + L H e^{L H})`) and
`c₂ = L B (e^{L H} + 2 √2 (1 + L H e^{L H}))`
(for `bugC₂ L B H = L B (e^{L H} + 8 (1 + L H e^{L H}))`).

## Main results

* `kstep_capture_two_mul`: `‖(1 - P₁) A(t₁)‖ ≤ h (2 L B h + ε)`.
* `bug_capture_two_mul`: `‖A(t₁) - P₁ Q₁ A(t₁)‖ ≤ √2 h (2 L B h + ε)`.
* `IsBUGStep.local_error_two_mul`, `IsBUGStep.local_error_le_two_mul`: the local error bound in
  the explicit form and in the `O`-form.
* `IsBUGStepCore.hasLocalError_of_tube_two_mul`: the local error of a step near a reference
  solution, for a field that is Lipschitz and bounded only on a tube.

## Proof of the capture estimate

For `g = (1 - P₁) (A - YK)` the derivative is split at the end point `YK(t₁)` of the K-step,

`g' = (1 - P₁) (F(t, A) - F(t, YK(t₁))) + (1 - P₁)(1 - Q₀) F(t, YK(t₁))
      + (1 - P₁) Q₀ (F(t, YK(t₁)) - F(t, YK))`,

and the distances are bounded with the time at which they are taken:
`‖A(t) - YK(t₁)‖ ≤ B (t - t₀) + B h` and `‖YK(t₁) - YK(t)‖ ≤ B (t₁ - t)`, which add up to `2 B h`
for every `t`. The proof of `kstep_capture` compares `F(t, A)` with `F(t, YK)` and `F(t, YK(t₁))`,
both at distance up to `2 B h`.

The `example`s at the end prove `kstep_capture`, `IsBUGStep.local_error_le` and
`IsBUGStep.local_error_sqrt_two` (all restated verbatim) from the results of this file.
-/

open Set

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Capture

variable {F : ℝ → E → E} {L B ε : ℝ} {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ h : ℝ} {A YK : ℝ → E}

/-- **K-step capture with the constant `2`.** Under the hypotheses of `kstep_capture`: `F`
`L`-Lipschitz (`L ≥ 0`) and bounded by `B`, `A` a solution on `[t₀, t₁]`, `t₁ = t₀ + h`, `h ≥ 0`,
the K-step trajectory `YK' = Q₀ F(t, YK)` with `YK t₀ = A t₀`, `P₁ (YK t₁) = YK t₁`, and
`‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε` on `[t₀, t₁]`, the new basis captures the exact solution
up to

    ‖(1 - P₁) (A t₁)‖ ≤ h (2 L B h + ε). -/
theorem kstep_capture_two_mul (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = A t₀)
    (hKcap : P₁ (YK t₁) = YK t₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε) :
    ‖(1 - P₁) (A t₁)‖ ≤ h * (2 * L * B * h + ε) := by
  have hle : t₀ ≤ t₁ := by linarith
  have hBK : IsBoundedField (fun t x => Q₀ (F t x)) B := hB.comp_contraction Q₀ hQ₀.norm_le
  set g : ℝ → E := fun t => (1 - P₁) (A t - YK t) with hg
  have hgc : ContinuousOn g (Icc t₀ t₁) :=
    (1 - P₁).continuous.comp_continuousOn (hA.cont.sub hK.cont)
  have hgd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt g ((1 - P₁) (F t (A t) - Q₀ (F t (YK t))))
      (Ici t) t := fun t ht =>
    (1 - P₁).hasFDerivAt.comp_hasDerivWithinAt t ((hA.deriv t ht).sub (hK.deriv t ht))
  have hbound : ∀ t ∈ Ico t₀ t₁, ‖(1 - P₁) (F t (A t) - Q₀ (F t (YK t)))‖
      ≤ 2 * L * B * h + ε := by
    intro t ht
    have htI : t ∈ Icc t₀ t₁ := Ico_subset_Icc_self ht
    have hA1 : ‖A t - A t₀‖ ≤ B * (t - t₀) := hA.norm_sub_le_of_bounded hB t htI
    have hK1 : ‖YK t₁ - YK t₀‖ ≤ B * (t₁ - t₀) :=
      hK.norm_sub_le_of_bounded hBK t₁ ⟨hle, le_rfl⟩
    have hK2 : ‖YK t₁ - YK t‖ ≤ B * (t₁ - t) :=
      (hK.mono htI.1 le_rfl).norm_sub_le_of_bounded hBK t₁ ⟨htI.2, le_rfl⟩
    have hd1 : ‖A t - YK t₁‖ ≤ B * (t - t₀) + B * (t₁ - t₀) := by
      have e : A t - YK t₁ = (A t - A t₀) - (YK t₁ - YK t₀) := by rw [hK₀]; abel
      rw [e]
      exact (norm_sub_le _ _).trans (add_le_add hA1 hK1)
    have hsplit : (1 - P₁) (F t (A t) - Q₀ (F t (YK t))) =
        (1 - P₁) (F t (A t) - F t (YK t₁)) + (1 - P₁) ((1 - Q₀) (F t (YK t₁)))
          + (1 - P₁) (Q₀ (F t (YK t₁) - F t (YK t))) := by
      rw [← map_add, ← map_add]
      congr 1
      simp only [sub_apply, one_apply_eq_self, map_sub]
      abel
    have hc1 : ‖(1 - P₁) (F t (A t) - F t (YK t₁))‖ ≤ L * (B * (t - t₀) + B * (t₁ - t₀)) :=
      calc _ ≤ ‖F t (A t) - F t (YK t₁)‖ := hP₁.compl.norm_le _
        _ ≤ L * ‖A t - YK t₁‖ := hF t _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hd1 hL
    have hc3 : ‖(1 - P₁) (Q₀ (F t (YK t₁) - F t (YK t)))‖ ≤ L * (B * (t₁ - t)) :=
      calc _ ≤ ‖Q₀ (F t (YK t₁) - F t (YK t))‖ := hP₁.compl.norm_le _
        _ ≤ ‖F t (YK t₁) - F t (YK t)‖ := hQ₀.norm_le _
        _ ≤ L * ‖YK t₁ - YK t‖ := hF t _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hK2 hL
    rw [hsplit]
    have h3 := norm_add₃_le (a := (1 - P₁) (F t (A t) - F t (YK t₁)))
      (b := (1 - P₁) ((1 - Q₀) (F t (YK t₁)))) (c := (1 - P₁) (Q₀ (F t (YK t₁) - F t (YK t))))
    have hε' := hε t htI
    have hsum : L * (B * (t - t₀) + B * (t₁ - t₀)) + L * (B * (t₁ - t)) = 2 * L * B * h := by
      rw [ht₁]
      ring
    linarith
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd hbound t₁ ⟨hle, le_rfl⟩
  have hg₀ : g t₀ = 0 := by simp [hg, hK₀]
  have hg₁ : g t₁ = (1 - P₁) (A t₁) := by
    simp only [hg, map_sub, sub_apply, one_apply_eq_self, hKcap, sub_self, sub_zero]
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [hg₀, hg₁, sub_zero, hlen] at hmvt
  rw [mul_comm h]
  exact hmvt

/-- **Capture of the BUG integrator with `√2` and the constant `2`.** If the K-step and the L-step
satisfy the hypotheses of `kstep_capture_two_mul` (the L-step with the roles of the left and the
right projectors exchanged), the new left and right bases together capture the exact solution:

    ‖A t₁ - P₁ Q₁ A t₁‖ ≤ √2 h (2 L B h + ε).

The left and the right capture errors are combined orthogonally; no commutation is needed. -/
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
    ‖A t₁ - P₁ (Q₁ (A t₁))‖ ≤ √2 * (h * (2 * L * B * h + ε)) := by
  have h1 := kstep_capture_two_mul hF hL hB hP₁ hQ₀ ht₁ hh hA hK hK₀ hKcap hεK
  have h2 := kstep_capture_two_mul hF hL hB hQ₁ hP₀ ht₁ hh hA hLs hL₀ hLcap hεL
  simp only [sub_apply, one_apply_eq_self] at h1 h2
  have hϑ : 0 ≤ h * (2 * L * B * h + ε) := (norm_nonneg _).trans h1
  have hsq := hP₁.norm_sub_apply_sq (A t₁) (Q₁ (A t₁))
  have hP : ‖P₁ (A t₁ - Q₁ (A t₁))‖ ≤ ‖A t₁ - Q₁ (A t₁)‖ := hP₁.norm_le _
  have ha := mul_le_mul h1 h1 (norm_nonneg _) hϑ
  have hb := mul_le_mul (hP.trans h2) (hP.trans h2) (norm_nonneg _) hϑ
  have hle : ‖A t₁ - P₁ (Q₁ (A t₁))‖ ^ 2 ≤ 2 * (h * (2 * L * B * h + ε)) ^ 2 := by
    rw [hsq]
    nlinarith
  calc ‖A t₁ - P₁ (Q₁ (A t₁))‖ = √(‖A t₁ - P₁ (Q₁ (A t₁))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(2 * (h * (2 * L * B * h + ε)) ^ 2) := Real.sqrt_le_sqrt hle
    _ = √2 * (h * (2 * L * B * h + ε)) := by
        rw [Real.sqrt_mul zero_le_two, Real.sqrt_sq hϑ]

end Capture

/-! ### The local error -/

namespace IsBUGStep

variable {F : ℝ → E → E} {L B ε : ℝ} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {t₀ t₁ h : ℝ} {Y₀ : E}
  {YK YL YS A : ℝ → E}

/-- **Local error of the BUG integrator with `√2` and the constant `2`.** Under the hypotheses of
`IsBUGStep.local_error` (`F` `L`-Lipschitz, `L ≥ 0`, bounded by `B`, `t₁ = t₀ + h`, `h ≥ 0`, `A`
a solution with `A t₀ = Y₀`), with `ϑ = h (2 L B h + ε)`,

    ‖YS t₁ - A t₁‖ ≤ (e^{L h} - 1) (B h + √2 ϑ) + √2 ϑ.

`IsBUGStep.local_error` has `2 ϑ` with `ϑ = h (4 L B h + ε)`. -/
theorem local_error_two_mul (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + √2 * (h * (2 * L * B * h + ε)))
      + √2 * (h * (2 * L * B * h + ε)) := by
  have hcap := bug_capture_two_mul hF hL hB hs.projP₀ hs.projQ₀ hs.projP₁ hs.projQ₁ ht₁ hh hA
    hs.kSol (hs.kStart.trans hA₀.symm) hs.kCap hs.kNormal hs.lSol (hs.lStart.trans hA₀.symm)
    hs.lCap hs.lNormal
  exact galerkin_step_error (R := P₁ * Q₁) (hs.projP₁.mul hs.projQ₁ hs.comm₁) hF hL hB ht₁ hh hA
    hs.sSol (by rw [hs.sStart, hA₀]; rfl) hcap

/-- **Local error of the BUG integrator, `O`-form with smaller constants.** Under the hypotheses
of `IsBUGStep.local_error_two_mul` and `h ≤ H`,

    ‖YS t₁ - A t₁‖ ≤ h (c₁ ε + c₂ h),
    c₁ = √2 (1 + L H e^{L H}),   c₂ = L B (e^{L H} + 2 √2 (1 + L H e^{L H})).

These constants are at most `bugC₁ L H = 2 (1 + L H e^{L H})` and
`bugC₂ L B H = L B (e^{L H} + 8 (1 + L H e^{L H}))` of `IsBUGStep.local_error_le`. -/
theorem local_error_le_two_mul (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤ h * (√2 * (1 + L * H * Real.exp (L * H)) * ε
      + L * B * (Real.exp (L * H) + 2 * √2 * (1 + L * H * Real.exp (L * H))) * h) := by
  have hε := hs.eps_nonneg (by linarith : t₀ ≤ t₁)
  have hB0 := hB.nonneg
  have hs0 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have he0 : 0 ≤ Real.exp (L * H) := (Real.exp_pos _).le
  have hθ : 0 ≤ √2 * (h * (2 * L * B * h + ε)) := by positivity
  have h1 : Real.exp (L * h) - 1 ≤ L * h * Real.exp (L * H) :=
    (exp_sub_one_le_mul_exp (L * h)).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hL)) (mul_nonneg hL hh))
  have h2 := mul_le_mul_of_nonneg_right h1 (add_nonneg (mul_nonneg hB0 hh) hθ)
  have h3 : L * h * Real.exp (L * H) * (√2 * (h * (2 * L * B * h + ε))) ≤
      L * H * Real.exp (L * H) * (√2 * (h * (2 * L * B * h + ε))) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhH hL) he0) hθ
  have hid : h * (√2 * (1 + L * H * Real.exp (L * H)) * ε
      + L * B * (Real.exp (L * H) + 2 * √2 * (1 + L * H * Real.exp (L * H))) * h) =
      L * h * Real.exp (L * H) * (B * h)
        + L * H * Real.exp (L * H) * (√2 * (h * (2 * L * B * h + ε)))
        + √2 * (h * (2 * L * B * h + ε)) := by ring
  rw [hid]
  have h4 := hs.local_error_two_mul hF hL hB ht₁ hh hA hA₀
  linarith

end IsBUGStep

/-! ### Steps near a reference solution -/

section Near

variable {F : ℝ → E → E} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E} {YK YL YS A : ℝ → E}
  {a b ρ L B ε H : ℝ}

/-- **Local error of a BUG step near a reference solution, smaller constants.** Under the
hypotheses of `IsBUGStepCore.hasLocalError_of_tube` (`F` `L`-Lipschitz and bounded by `B` on the
tube of radius `ρ` around `A` over `[a, b]`, `[t₀, t₁] ⊆ [a, b]`, `t₁ - t₀ ≤ H`,
`‖Y₀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, normal parts at most `ε`), the result `YS t₁` differs from the
exact solution through `(t₀, Y₀)` by at most `(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))` with
`c₁ = √2 (1 + L H e^{L H})` and `c₂ = L B (e^{L H} + 2 √2 (1 + L H e^{L H}))`. -/
theorem IsBUGStepCore.hasLocalError_of_tube_two_mul
    (hs : IsBUGStepCore F P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS)
    (hεK : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε)
    (hεL : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hH : t₁ - t₀ ≤ H)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ (YS t₁)
      ((t₁ - t₀) * (√2 * (1 + L * H * Real.exp (L * H)) * ε
        + L * B * (Real.exp (L * H) + 2 * √2 * (1 + L * H * Real.exp (L * H))) * (t₁ - t₀))) := by
  intro Φ hΦ hΦ₀
  have hh : 0 ≤ t₁ - t₀ := sub_nonneg.2 h01
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB hh
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (Y₀ - A t₀)]
  have ht₁ : t₁ = t₀ + (t₁ - t₀) := by ring
  have hΦG : ODESolution (tubeExt F A a b ρ) Φ t₀ t₁ :=
    hΦ.tubeExt_of_near hFB hB hh ha hb ht₁ hA (by rw [hΦ₀]; linarith)
  exact ((isBUGStep_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).2
    (hs.isBUGStep hεK hεL)).local_error_le_two_mul (isLipschitzField_tubeExt hFL hL hρ) hL
    (isBoundedField_tubeExt hFB hB hρ) ht₁ hh hH hΦG hΦ₀

end Near

/-! ### The theorems with the larger constants, and non-vacuity -/

/-- The constants of `IsBUGStep.local_error_le_two_mul` are at most those of
`IsBUGStep.local_error_le`: `√2 (1 + L H e^{L H}) ε + L B (e^{L H} + 2 √2 (1 + L H e^{L H})) h ≤
bugC₁ L H ε + bugC₂ L B H h`. -/
theorem bugConstants_two_mul_le {L B H ε h : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hε : 0 ≤ ε) (hh : 0 ≤ h) :
    √2 * (1 + L * H * Real.exp (L * H)) * ε
        + L * B * (Real.exp (L * H) + 2 * √2 * (1 + L * H * Real.exp (L * H))) * h ≤
      bugC₁ L H * ε + bugC₂ L B H * h := by
  have hs2 : √2 ≤ 2 := by
    have h1 := Real.sq_sqrt (zero_le_two : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2]
  have hX : 0 ≤ 1 + L * H * Real.exp (L * H) := by positivity
  have hc₁ : √2 * (1 + L * H * Real.exp (L * H)) ≤ bugC₁ L H := by
    unfold bugC₁
    nlinarith
  have hc₂ : L * B * (Real.exp (L * H) + 2 * √2 * (1 + L * H * Real.exp (L * H))) ≤
      bugC₂ L B H := by
    unfold bugC₂
    have hLB : 0 ≤ L * B := mul_nonneg hL hB
    have : 2 * √2 * (1 + L * H * Real.exp (L * H)) ≤ 8 * (1 + L * H * Real.exp (L * H)) := by
      nlinarith
    nlinarith
  have := mul_le_mul_of_nonneg_right hc₁ hε
  have := mul_le_mul_of_nonneg_right hc₂ hh
  linarith

section Examples

variable {F : ℝ → E → E} {L B ε : ℝ} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {t₀ t₁ h : ℝ} {Y₀ : E}
  {YK YL YS A : ℝ → E}

/-- `kstep_capture`, restated verbatim, follows from `kstep_capture_two_mul`. -/
example (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁)
    (hK₀ : YK t₀ = A t₀) (hKcap : P₁ (YK t₁) = YK t₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε) :
    ‖(1 - P₁) (A t₁)‖ ≤ h * (4 * L * B * h + ε) := by
  have h1 := kstep_capture_two_mul hF hL hB hP₁ hQ₀ ht₁ hh hA hK hK₀ hKcap hε
  have h2 : 0 ≤ h * (2 * L * B * h) := by have := hB.nonneg; positivity
  linarith

/-- `IsBUGStep.local_error_le`, restated verbatim, follows from
`IsBUGStep.local_error_le_two_mul`: its constants are larger. -/
example (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤ h * (bugC₁ L H * ε + bugC₂ L B H * h) := by
  refine (hs.local_error_le_two_mul hF hL hB ht₁ hh hhH hA hA₀).trans ?_
  exact mul_le_mul_of_nonneg_left (bugConstants_two_mul_le hL hB.nonneg (hh.trans hhH)
    (hs.eps_nonneg (by linarith)) hh) hh

/-- `IsBUGStep.local_error_sqrt_two`, restated verbatim, follows from
`IsBUGStep.local_error_two_mul`. -/
example (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + √2 * (h * (4 * L * B * h + ε)))
      + √2 * (h * (4 * L * B * h + ε)) := by
  refine (hs.local_error_two_mul hF hL hB ht₁ hh hA hA₀).trans ?_
  have hB0 := hB.nonneg
  have hd : 0 ≤ √2 * (h * (2 * L * B * h)) := by positivity
  have he : 0 ≤ Real.exp (L * h) - 1 := by
    have := Real.add_one_le_exp (L * h)
    nlinarith [mul_nonneg hL hh]
  have := mul_nonneg he hd
  nlinarith

/-- **Non-vacuity of `kstep_capture_two_mul`** with a nonzero field: on `ℝ` with `F(t, y) = 1`
(`L = 0`, `B = 1`), `A t = t`, `Q₀ = 1`, `YK = A`, `P₁ = 1`, `ε = 0` on `[0, 1]`. -/
example : ‖((1 : ℝ →L[ℝ] ℝ) - 1) ((fun t : ℝ => t) 1)‖ ≤ 1 * (2 * 0 * 1 * 1 + 0) :=
  kstep_capture_two_mul (E := ℝ) (F := fun _ _ => 1) (fun _ _ _ => by simp) le_rfl
    (fun _ _ => by simp) IsOrthProj.one IsOrthProj.one (t₀ := 0) (t₁ := 1) (h := 1)
    (by norm_num) zero_le_one (odeSolution_id_of_eq_one (fun _ _ => rfl) _ _)
    (odeSolution_id_of_eq_one (fun _ _ => by simp) _ _) rfl (by simp) (fun _ _ => by simp)

/-- **Non-vacuity of `IsBUGStep.local_error_two_mul` and `IsBUGStep.local_error_le_two_mul`**: the
step of the integrator on `ℝ` for `F(t, y) = 1` with all projectors the identity and all
trajectories `t ↦ t` on `[0, 1]` satisfies their hypotheses (`L = 0`, `B = 1`, `ε = 0`). -/
example : ‖(fun t : ℝ => t) 1 - (fun t : ℝ => t) 1‖ ≤
    1 * (√2 * (1 + 0 * 1 * Real.exp (0 * 1)) * 0
      + 0 * 1 * (Real.exp (0 * 1) + 2 * √2 * (1 + 0 * 1 * Real.exp (0 * 1))) * 1) :=
  IsBUGStep.local_error_le_two_mul (E := ℝ) (F := fun _ _ => 1) (P₀ := 1) (Q₀ := 1) (P₁ := 1)
    (Q₁ := 1) (YK := fun t => t) (YL := fun t => t) (YS := fun t => t) (Y₀ := 0)
    { projP₀ := IsOrthProj.one
      projQ₀ := IsOrthProj.one
      projP₁ := IsOrthProj.one
      projQ₁ := IsOrthProj.one
      comm₁ := fun _ => rfl
      kSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
      kStart := rfl
      kCap := rfl
      kNormal := fun _ _ => by simp
      lSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
      lStart := rfl
      lCap := rfl
      lNormal := fun _ _ => by simp
      sSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
      sStart := rfl }
    (fun _ _ _ => by simp) le_rfl (fun _ _ => by simp) (t₀ := 0) (t₁ := 1) (h := 1)
    (by norm_num) zero_le_one le_rfl (odeSolution_id_of_eq_one (fun _ _ => rfl) _ _) rfl

end Examples

end LeanDLRA
