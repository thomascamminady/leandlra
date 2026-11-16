import LeanDLRA.Integrators.InexactSubsteps
import LeanDLRA.Integrators.Method

/-!
# The BUG integrator with inexact substeps near a reference solution

The BUG step with substep defects (`InexactSubsteps.IsDefectBUGStep`) allows inexact K- and
L-steps (capture defects `ηK`, `ηL` of the new bases) and an inexact S-step or truncation (error
`ηS`). Its local and global errors are proved in `LeanDLRA/Integrators/InexactSubsteps.lean` for
fields that are Lipschitz and bounded everywhere, with the exact flows started at the numerical
values as hypotheses. This file proves the global error bound for a field that is Lipschitz and
bounded only on a tube around a reference solution, without such flows: the local error is
transferred to the tube (`InexactSubsteps.IsDefectBUGStep.hasLocalError_of_tube`), and the
chain of steps is a run of the step relation "a defect BUG step with defects at most `η`", to
which the tube theorem `IsRun.norm_sub_le_of_tube_uniformGrid` applies.

## Main results

* `InexactSubsteps.IsDefectBUGStep.norm_sub_lt_of_near`: with the margin
  `‖Y₀ - A t₀‖ + 4 B (t₁ - t₀) + ηK + ηL < ρ`, all substeps stay in the tube.
* `InexactSubsteps.IsDefectBUGStep.tubeExt_of_near`: such a step is a step for the tube extension.
* `InexactSubsteps.IsDefectBUGStep.hasLocalError_of_tube`: the local error
  `h (c₁ ε + c₂ h) + e^{L H} (ηK + ηL) + ηS` near the reference solution.
* `InexactSubsteps.defectBUG_norm_sub_le_of_tube`: the global error bound
  `e^{L T} δ + T e^{L T} (c₁ ε + c₂ h + (2 e^{L H} + 1) η / h)` for a chain of defect steps with
  defects at most `η`.

## Implementation notes

The Galerkin step of a defect step starts at `P₁ Q₁ Y₀`, which differs from `Y₀` by at most
`2 B h + ηK + ηL`. The margin is therefore `4 B h + ηK + ηL` and not a multiple of `B h`: the
step does not fit `StepMethod.IsTubeLocal`, whose margin is `κ B h`, and the bound is proved for
given chains of steps through the tube theorem for runs. The defect sum is written as
`T (2 e^{L H} + 1) η / h` (`h > 0`); for `n h ≤ T` it is at least the sum
`n (2 e^{L H} + 1) η` of `defectBUG_global_error_le`, with equality for `n h = T`. Existence of
steps is not shown: exact BUG steps are defect steps with zero defects
(`InexactSubsteps.ofBUGStep`).
-/

open Set
open scoped RealInnerProductSpace

namespace LeanDLRA.InexactSubsteps

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace IsDefectBUGStep

variable {F : ℝ → E → E} {ε ηK ηL ηS : ℝ} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E}
  {YK YL YS : ℝ → E} {Y₁ : E} {A : ℝ → E} {a b ρ L B H : ℝ}

/-- `‖(1 - P) z‖ ≤ ‖z‖` for an orthogonal projector `P`. -/
private theorem norm_one_sub_apply_le_aux {P : E →L[ℝ] E} (hP : IsOrthProj P) (z : E) :
    ‖(1 - P) z‖ ≤ ‖z‖ := by
  simpa using hP.norm_sub_le z

/-- **The substeps of a defect step stay in the tube.** Let `F` be bounded by `B` on the tube of
radius `ρ` around a solution `A` over `[a, b] ⊇ [t₀, t₁]`. If
`‖Y₀ - A t₀‖ + 4 B (t₁ - t₀) + ηK + ηL < ρ`, then the K- and L-step trajectories, their end
values at every time of the step, and the Galerkin trajectory lie strictly inside the tube. -/
theorem norm_sub_lt_of_near (hs : IsDefectBUGStep F ε ηK ηL ηS P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b)
    (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) + (ηK + ηL) < ρ) :
    (∀ t ∈ Icc t₀ t₁, ‖YK t - A t‖ < ρ) ∧ (∀ t ∈ Icc t₀ t₁, ‖YK t₁ - A t‖ < ρ) ∧
      (∀ t ∈ Icc t₀ t₁, ‖YL t - A t‖ < ρ) ∧ (∀ t ∈ Icc t₀ t₁, ‖YL t₁ - A t‖ < ρ) ∧
        ∀ t ∈ Icc t₀ t₁, ‖YS t - A t‖ < ρ := by
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hη : 0 ≤ ηK + ηL := add_nonneg hs.etaK_nonneg hs.etaL_nonneg
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (Y₀ - A t₀)]
  have h2 : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ := by linarith
  have hK := ODESolution.near_of_comp_proj (Ψ := Q₀) hs.kSol hs.projQ₀.norm_le hFB hB ha hb hA
    (by rw [hs.kStart]; exact h2)
  have hL := ODESolution.near_of_comp_proj (Ψ := P₀) hs.lSol hs.projP₀.norm_le hFB hB ha hb hA
    (by rw [hs.lStart]; exact h2)
  have hmem : t₁ ∈ Icc t₀ t₁ := ⟨h01, le_rfl⟩
  have hK1 : ‖YK t₁ - Y₀‖ ≤ B * (t₁ - t₀) := by
    have := (hK t₁ hmem).2
    rwa [hs.kStart] at this
  have hL1 : ‖YL t₁ - Y₀‖ ≤ B * (t₁ - t₀) := by
    have := (hL t₁ hmem).2
    rwa [hs.lStart] at this
  -- the end values of the K- and L-step, compared with `A t`
  have hend : ∀ Z : E, ‖Z - Y₀‖ ≤ B * (t₁ - t₀) → ∀ t ∈ Icc t₀ t₁, ‖Z - A t‖ < ρ := by
    intro Z hZ t ht
    have hAt := hA.norm_sub_le (hFB.along hρ ha hb) t ht
    have h3 : B * (t - t₀) ≤ B * (t₁ - t₀) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 t₀) hB
    have e : Z - A t = (Z - Y₀) + (Y₀ - A t₀) - (A t - A t₀) := by abel
    rw [e]
    have h4 := norm_sub_le ((Z - Y₀) + (Y₀ - A t₀)) (A t - A t₀)
    have h5 := norm_add_le (Z - Y₀) (Y₀ - A t₀)
    linarith
  -- the start value of the Galerkin step
  have hcK : ‖(1 - P₁) Y₀‖ ≤ B * (t₁ - t₀) + ηK := by
    have e : (1 - P₁) Y₀ = (1 - P₁) (Y₀ - YK t₁) + (1 - P₁) (YK t₁) := by
      rw [← map_add, sub_add_cancel]
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ hs.kDefect)
    exact (norm_one_sub_apply_le_aux hs.projP₁ _).trans (by rw [norm_sub_rev]; exact hK1)
  have hcL : ‖(1 - Q₁) Y₀‖ ≤ B * (t₁ - t₀) + ηL := by
    have e : (1 - Q₁) Y₀ = (1 - Q₁) (Y₀ - YL t₁) + (1 - Q₁) (YL t₁) := by
      rw [← map_add, sub_add_cancel]
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ hs.lDefect)
    exact (norm_one_sub_apply_le_aux hs.projQ₁ _).trans (by rw [norm_sub_rev]; exact hL1)
  have hS₀ : ‖YS t₀ - A t₀‖ ≤ ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) + (ηK + ηL) := by
    have h1 := norm_sub_apply_apply_le (Q := Q₁) hs.projP₁ Y₀
    have e : YS t₀ - A t₀ = (Y₀ - A t₀) - (Y₀ - P₁ (Q₁ Y₀)) := by rw [hs.sStart]; abel
    rw [e]
    have h2' := norm_sub_le (Y₀ - A t₀) (Y₀ - P₁ (Q₁ Y₀))
    linarith
  have hS := ODESolution.near_of_comp_proj (Ψ := fun x => P₁ (Q₁ x)) hs.sSol
    (fun x => (hs.projP₁.norm_le _).trans (hs.projQ₁.norm_le x)) hFB hB ha hb hA
    (by linarith)
  exact ⟨fun t ht => (hK t ht).1, hend _ hK1, fun t ht => (hL t ht).1, hend _ hL1,
    fun t ht => (hS t ht).1⟩

/-- **A defect step near the reference solution is a defect step for the tube extension.** Under
the hypotheses of `InexactSubsteps.IsDefectBUGStep.norm_sub_lt_of_near`, the step is a step
`IsDefectBUGStep` for `tubeExt F A a b ρ` with the same projectors, trajectories and defects:
the extension agrees with `F` at every point where the step evaluates the field. -/
theorem tubeExt_of_near (hs : IsDefectBUGStep F ε ηK ηL ηS P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b)
    (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) + (ηK + ηL) < ρ) :
    IsDefectBUGStep (tubeExt F A a b ρ) ε ηK ηL ηS P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁ := by
  obtain ⟨hK, hK1, hL, hL1, hS⟩ := hs.norm_sub_lt_of_near hFB hB ha hb h01 hA hsmall
  have hmem : ∀ t ∈ Icc t₀ t₁, t ∈ Icc a b := fun t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩
  exact
    { projP₀ := hs.projP₀
      projQ₀ := hs.projQ₀
      projP₁ := hs.projP₁
      projQ₁ := hs.projQ₁
      comm₁ := hs.comm₁
      kSol := (odeSolution_comp_tubeExt_iff (fun x => Q₀ x) ha hb
        fun t ht => (hK t (Ico_subset_Icc_self ht)).le).2 hs.kSol
      kStart := hs.kStart
      kNormal := fun t ht => by
        rw [tubeExt_eq (hmem t ht) (hK1 t ht).le]
        exact hs.kNormal t ht
      kDefect := hs.kDefect
      lSol := (odeSolution_comp_tubeExt_iff (fun x => P₀ x) ha hb
        fun t ht => (hL t (Ico_subset_Icc_self ht)).le).2 hs.lSol
      lStart := hs.lStart
      lNormal := fun t ht => by
        rw [tubeExt_eq (hmem t ht) (hL1 t ht).le]
        exact hs.lNormal t ht
      lDefect := hs.lDefect
      sSol := (odeSolution_comp_tubeExt_iff (fun x => P₁ (Q₁ x)) ha hb
        fun t ht => (hS t (Ico_subset_Icc_self ht)).le).2 hs.sSol
      sStart := hs.sStart
      sErr := hs.sErr }

/-- **Local error of a defect step near a reference solution.** Let `F` be `L`-Lipschitz and
bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b] ⊇ [t₀, t₁]`. If
`0 ≤ t₁ - t₀ ≤ H` and `‖Y₀ - A t₀‖ + 4 B (t₁ - t₀) + ηK + ηL < ρ`, the step has local error
`(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀)) + e^{L H} (ηK + ηL) + ηS` with `c₁ = bugC₁ L H`,
`c₂ = bugC₂ L B H`: this is `InexactSubsteps.IsDefectBUGStep.local_error_le` for the tube
extension. Nothing is assumed about `F` outside the tube. -/
theorem hasLocalError_of_tube
    (hs : IsDefectBUGStep F ε ηK ηL ηS P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hH : t₁ - t₀ ≤ H)
    (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) + (ηK + ηL) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Y₁ ((t₁ - t₀) * (bugC₁ L H * ε + bugC₂ L B H * (t₁ - t₀)) +
      Real.exp (L * H) * (ηK + ηL) + ηS) := by
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hη : 0 ≤ ηK + ηL := add_nonneg hs.etaK_nonneg hs.etaL_nonneg
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (Y₀ - A t₀)]
  have hG := hs.tubeExt_of_near hFB hB ha hb h01 hA hsmall
  refine HasLocalError.of_tubeExt (fun Φ hΦ hΦ₀ => ?_) hFB hB ha hb h01 hA (by linarith)
  exact hG.local_error_le (isLipschitzField_tubeExt hFL hL hρ) hL
    (isBoundedField_tubeExt hFB hB hρ) (by ring) (sub_nonneg.2 h01) hH hΦ hΦ₀

end IsDefectBUGStep

/-! ### The global error near a reference solution -/

section Global

variable {F : ℝ → E → E} {A : ℝ → E} {t₀ h H T ρ L B ε η δ : ℝ} {N : ℕ}

/-- **Global error of the BUG integrator with inexact substeps near a reference solution.** Let
`(F, A)` be a problem on the tube of radius `ρ` over `[t₀, t₀ + N h]` (`DLRAProblem`), with `F`
continuous on the tube. Let `Y 0, …, Y N` be obtained by steps `IsDefectBUGStep` of size
`0 < h ≤ H` with normal bound `ε ≥ 0` and all defects `ηK n`, `ηL n`, `ηS n` at most `η`, let
`N h ≤ T` and `‖Y 0 - A t₀‖ ≤ δ`. If the bound below plus `4 B h + 2 η` is smaller than `ρ`, then
for all `n ≤ N`

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (c₁ ε + c₂ h + (2 e^{L H} + 1) η / h)`,

`c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`. This is the tube form of `defectBUG_global_error_le`: the
field is controlled only near `A`, and no exact flows started at the numerical values appear. -/
theorem defectBUG_norm_sub_le_of_tube [CompleteSpace E]
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ)) (hε : 0 ≤ ε)
    (hη : 0 ≤ η) (hh : 0 < h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    {P Q P' Q' : ℕ → E →L[ℝ] E} {Y : ℕ → E} {YK YL YS : ℕ → ℝ → E} {ηK ηL ηS : ℕ → ℝ}
    (hstep : ∀ n < N, IsDefectBUGStep F ε (ηK n) (ηL n) (ηS n) (P n) (Q n) (P' n) (Q' n)
      (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hηK : ∀ n < N, ηK n ≤ η) (hηL : ∀ n < N, ηL n ≤ η) (hηS : ∀ n < N, ηS n ≤ η)
    (hδ : ‖Y 0 - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) * (bugC₁ L H * ε + bugC₂ L B H * h +
      (2 * Real.exp (L * H) + 1) * η / h) + 4 * B * h + 2 * η < ρ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) *
      (bugC₁ L H * ε + bugC₂ L B H * h + (2 * Real.exp (L * H) + 1) * η / h) := by
  have hH : 0 ≤ H := hh.le.trans hhH
  have hBh : 0 ≤ B * h := mul_nonneg hP.B_nonneg hh.le
  have hc₀ : 0 ≤ bugC₁ L H * ε + bugC₂ L B H * h + (2 * Real.exp (L * H) + 1) * η / h :=
    add_nonneg (add_nonneg (mul_nonneg (bugC₁_nonneg hP.L_nonneg hH) hε)
      (mul_nonneg (bugC₂_nonneg hP.L_nonneg hP.B_nonneg hH) hh.le))
      (div_nonneg (mul_nonneg (by positivity) hη) hh.le)
  -- the chain is a run of the relation "a defect step with defects at most `η`"
  have hrun : IsRun (fun s s' Z Z' => ∃ (a b c : ℝ) (p q p' q' : E →L[ℝ] E) (zK zL zS : ℝ → E),
      a ≤ η ∧ b ≤ η ∧ c ≤ η ∧ IsDefectBUGStep F ε a b c p q p' q' s s' Z zK zL zS Z')
      (uniformGrid t₀ h) N Y := (isRun_uniformGrid_iff hh.le).2 fun n hn =>
    ⟨_, _, _, _, _, _, _, _, _, _, hηK n hn, hηL n hn, hηS n hn, hstep n hn⟩
  refine hrun.norm_sub_le_of_tube_uniformGrid hP hc (fun n hn Z₀ Z₁ hnear hZ => ?_) hc₀ hδ hNT
    (by linarith)
  obtain ⟨a, b, c, p, q, p', q', zK, zL, zS, ha, hb, hc', hs⟩ := hZ
  obtain ⟨h0, h01, h1, hsub⟩ := uniformGrid_step (t₀ := t₀) hh.le hn
  have hloc := hs.hasLocalError_of_tube hP.lipschitz hP.L_nonneg hP.bounded hP.B_nonneg h0 h1 h01
    (hsub.le.trans hhH) (hP.sol.mono h0 h1) (by rw [hsub]; linarith)
  rw [hsub] at hloc
  intro Φ hΦ hΦ₀
  refine (hloc Φ hΦ hΦ₀).trans ?_
  have hexp : 0 ≤ Real.exp (L * H) := (Real.exp_pos _).le
  have e : h * (bugC₁ L H * ε + bugC₂ L B H * h + (2 * Real.exp (L * H) + 1) * η / h) =
      h * (bugC₁ L H * ε + bugC₂ L B H * h) + (2 * Real.exp (L * H) * η + η) := by
    have hh0 : h ≠ 0 := hh.ne'
    field_simp
  rw [e]
  linarith [mul_le_mul_of_nonneg_left (add_le_add ha hb) hexp]

end Global

/-! ### Non-vacuity -/

section Examples

/-- **Non-vacuity of `InexactSubsteps.defectBUG_norm_sub_le_of_tube`**, for the nonzero constant
field `F t x = v` with the solution `A t = x₀ + (t - t₀) v`, the identity as all four projectors
and S-step results that are perturbed by at most `η`. Every sequence with
`‖Y (n + 1) - (Y n + h v)‖ ≤ η` is a chain of defect steps with `ηK = ηL = 0` and `ηS = η`: the
K-, L- and S-trajectories of step `n` are the straight line `Y n + (t - t₀ - n h) v`. The field
is Lipschitz with constant `0` and bounded by `‖v‖`, so `c₁ ε = 0` (`ε = 0`) and `c₂ = 0`, and
the theorem gives the bound `δ + T · 3 η / h`. -/
example [CompleteSpace E] (v x₀ : E) {t₀ h T δ η ρ : ℝ} {N : ℕ} (hh : 0 < h) (hη : 0 ≤ η)
    (hNT : N * h ≤ T) {Y : ℕ → E} (hY : ∀ n < N, ‖Y (n + 1) - (Y n + h • v)‖ ≤ η)
    (hδ : ‖Y 0 - x₀‖ ≤ δ) (hsmall : δ + T * (3 * η / h) + 4 * ‖v‖ * h + 2 * η < ρ) :
    ∀ n ≤ N, ‖Y n - (x₀ + ((n : ℝ) * h) • v)‖ ≤ δ + T * (3 * η / h) := by
  have aff : ∀ (y₀ : E) (a b : ℝ),
      ODESolution (fun _ _ => v) (fun t => y₀ + (t - a) • v) a b := fun y₀ a b =>
    ⟨by fun_prop, fun t _ => by
      have hd : HasDerivAt (fun t : ℝ => y₀ + (t - a) • v) v t := by
        simpa using (((hasDerivAt_id t).sub_const a).smul_const v).const_add y₀
      exact hd.hasDerivWithinAt⟩
  have hP : DLRAProblem (fun _ _ => v) (fun t => x₀ + (t - t₀) • v) t₀ (t₀ + N * h) ρ 0 ‖v‖ :=
    ⟨aff x₀ t₀ _, le_rfl, norm_nonneg v, fun t _ x y _ _ => by simp, fun t _ x _ => le_rfl⟩
  have hstep : ∀ n < N, IsDefectBUGStep (fun _ _ => v) 0 0 0 η 1 1 1 1 (t₀ + n * h)
      (t₀ + (n + 1) * h) (Y n) (fun t => Y n + (t - (t₀ + n * h)) • v)
      (fun t => Y n + (t - (t₀ + n * h)) • v) (fun t => Y n + (t - (t₀ + n * h)) • v)
      (Y (n + 1)) := by
    intro n hn
    have hsol := aff (Y n) (t₀ + n * h) (t₀ + (n + 1) * h)
    have e : t₀ + ((n : ℝ) + 1) * h - (t₀ + n * h) = h := by ring
    exact
      { projP₀ := IsOrthProj.one
        projQ₀ := IsOrthProj.one
        projP₁ := IsOrthProj.one
        projQ₁ := IsOrthProj.one
        comm₁ := fun _ => rfl
        kSol := by simpa only [one_apply_eq_self] using hsol
        kStart := by simp
        kNormal := fun _ _ => by simp
        kDefect := by simp
        lSol := by simpa only [one_apply_eq_self] using hsol
        lStart := by simp
        lNormal := fun _ _ => by simp
        lDefect := by simp
        sSol := by simpa only [one_apply_eq_self] using hsol
        sStart := by simp
        sErr := by simpa only [e] using hY n hn }
  have e : Real.exp (0 * T) * δ + T * Real.exp (0 * T) * (bugC₁ 0 h * 0 + bugC₂ 0 ‖v‖ h * h +
      (2 * Real.exp (0 * h) + 1) * η / h) = δ + T * (3 * η / h) := by
    simp only [bugC₂, zero_mul, mul_zero, Real.exp_zero, one_mul, zero_add]
    ring
  have key := defectBUG_norm_sub_le_of_tube (ε := 0) (H := h) (T := T) (δ := δ) hP
    continuousOn_const le_rfl hη hh le_rfl hNT hstep (ηK := fun _ => 0) (ηL := fun _ => 0)
    (ηS := fun _ => η) (fun _ _ => hη) (fun _ _ => hη) (fun _ _ => le_rfl) (by simpa using hδ)
    (by rw [e]; linarith)
  intro n hn
  have hn' := key n hn
  rw [e] at hn'
  simpa only [add_sub_cancel_left] using hn'

end Examples

end LeanDLRA.InexactSubsteps
