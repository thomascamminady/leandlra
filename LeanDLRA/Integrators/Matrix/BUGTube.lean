import LeanDLRA.Integrators.Matrix.BUGStep
import LeanDLRA.Integrators.Tube

/-!
# The BUG integrator near the solution: global error from tube hypotheses

The robust error bound of the fixed-rank BUG integrator [CerutiLubich2022, Thm. 4] is stated in
`LeanDLRA/Integrators/Matrix/BUG.lean` (`MatrixBUG.global_error_le`) for a field that is
Lipschitz and bounded on the whole space and whose normal part is small at all rank-`r`
matrices. This file proves it from hypotheses on the tube `‖Y - A t‖ ≤ ρ` around the solution
`A` only, for a chain of factor steps `MatrixBUG.IsStep`.

The proof has two ingredients and no computation of its own:

* the local error of one step that starts near `A` (`MatrixBUG.IsStep.hasLocalError_of_tube` in
  `LeanDLRA/Integrators/Matrix/BUGStep.lean`): the substeps stay in the tube, so the normal
  bound on the tube applies to their results;
* the tube theorem `IsLipschitzOnTube.norm_sub_le_of_fan_uniformGrid` of
  `LeanDLRA/Integrators/Tube.lean`: a method whose error bound stays below the tube radius
  never leaves the tube.

## Main results

* `bugGlobalBound_eq`: the bound `bugGlobalBound L B H T δ ε h` in the form
  `e^{L T} δ + T e^{L T} (c₁ ε + c₂ h)` of the tube theorem.
* `MatrixBUG.norm_sub_le_of_tube`: the error bound for a chain of factor steps with the
  Lipschitz bound, the bound of the field and the normal bound assumed on the tube only.

The older theorems `bug_global_error_le_of_tube` (`LeanDLRA/Foundations/Localization.lean`) and
`MatrixBUG.global_error_le` are recovered as instances at the end of each section.

## Implementation notes

The exact solutions `Φ j` on the steps are hypotheses here, as in the older theorems, so that
neither completeness nor continuity of `F` in time is needed. The form without `Φ`, for runs of
`MatrixBUG.stepRel`, is in `LeanDLRA/Integrators/Matrix/BUGRun.lean`.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

/-- The global error bound of the BUG integrator, written as initial error plus accumulated local
errors `h (c₁ ε + c₂ h)` with `c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`. -/
theorem bugGlobalBound_eq (L B H T δ ε h : ℝ) :
    bugGlobalBound L B H T δ ε h =
      Real.exp (L * T) * δ + T * Real.exp (L * T) * (bugC₁ L H * ε + bugC₂ L B H * h) := by
  unfold bugGlobalBound
  ring

/-- The tube form `bug_global_error_le_of_tube` of the error bound of the abstract BUG integrator
is an instance of the tube theorem `IsLipschitzOnTube.norm_sub_le_of_fan_uniformGrid`: the local
error of a step that starts near `A` is `IsBUGStepCore.hasLocalError_of_tube`. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : ℝ → E → E} {A : ℝ → E}
    {ρ B ε L H t₀ h : ℝ} {N : ℕ} (hFL : IsLipschitzOnTube F A t₀ (t₀ + N * h) ρ L) (hL : 0 ≤ L)
    (hFB : IsBoundedOnTube F A t₀ (t₀ + N * h) ρ B) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H)
    (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YK YL YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsBUGStep F ε (P n) (Q n) (P (n + 1)) (Q (n + 1)) (t₀ + n * h)
      (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n))
    (hY : ∀ n < N, Y (n + 1) = YS n (t₀ + (n + 1) * h))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ)
    (hNT : N * h ≤ T) (hsmall : bugGlobalBound L B H T δ ε h + 4 * B * h < ρ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ bugGlobalBound L B H T δ ε h := by
  rw [bugGlobalBound_eq] at hsmall ⊢
  have hH : 0 ≤ H := hh.trans hhH
  have hc : 0 ≤ bugC₁ L H * ε + bugC₂ L B H * h :=
    add_nonneg (mul_nonneg (bugC₁_nonneg hL hH) hε) (mul_nonneg (bugC₂_nonneg hL hB hH) hh)
  have hBh : 0 ≤ B * h := mul_nonneg hB hh
  refine hFL.norm_sub_le_of_fan_uniformGrid (Φ := Φ) (T := T) (δ₀ := δ)
    (c := bugC₁ L H * ε + bugC₂ L B H * h) hL hFB hB hh hA
    (fun n hn hnear => ⟨hΦ n hn, hΦ₀ n hn, ?_⟩) hc hδ hNT (by linarith)
  obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hn
  obtain ⟨hcore, hεK, hεL⟩ := isBUGStep_iff.1 (hstep n hn)
  have hloc := hcore.hasLocalError_of_tube hεK hεL hFL hL hFB hB ha hb h01 (hsub.le.trans hhH)
    (hA.mono ha hb) (by rw [hsub]; linarith)
  rw [hsub] at hloc
  rw [hY n hn]
  exact hloc (Φ n) (hΦ n hn) (hΦ₀ n hn)

namespace MatrixBUG

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {L B ε ρ H T δ t₀ h : ℝ} {N : ℕ}
  {U : ℕ → Matrix m (Fin r) ℝ} {Sm : ℕ → Matrix (Fin r) (Fin r) ℝ} {V : ℕ → Matrix n (Fin r) ℝ}
  {K : ℕ → ℝ → Matrix m (Fin r) ℝ} {Lf : ℕ → ℝ → Matrix n (Fin r) ℝ}
  {S : ℕ → ℝ → Matrix (Fin r) (Fin r) ℝ} {Φ : ℕ → ℝ → Matrix m n ℝ}

/-- **Robust error bound of the matrix BUG integrator from hypotheses near the solution**
[CerutiLubich2022, Thm. 4]. Let `A` solve `Ȧ = F(t, A)` on `[t₀, t₀ + N h]`, and on the tube of
radius `ρ` around `A` let `F` be `L`-Lipschitz and bounded by `B` and let its normal part be at
most `ε` at the rank-`r` points (`FactoredNormalBoundOn`). For `j < N` let step `j` of the BUG
integrator (`MatrixBUG.IsStep`) with step size `0 ≤ h ≤ H` go from `Y j = U j * Sm j * (V j)ᵀ`
to `Y (j + 1)`, and let `Φ j` be the exact solution on step `j` started at `Y j`. If
`‖Y 0 - A t₀‖ ≤ δ`, `N h ≤ T` and the bound
`bugGlobalBound L B H T δ ε h = e^{L T} δ + T e^{L T} (c₁ ε + c₂ h)` plus `4 B h` is below `ρ`,
then

  `‖Y j - A (t₀ + j h)‖ ≤ bugGlobalBound L B H T δ ε h` for all `j ≤ N`.

Nothing is assumed about `F` outside the tube. -/
theorem norm_sub_le_of_tube (hFL : IsLipschitzOnTube F A t₀ (t₀ + N * h) ρ L) (hL : 0 ≤ L)
    (hFB : IsBoundedOnTube F A t₀ (t₀ + N * h) ρ B) (hB : 0 ≤ B)
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hA : ODESolution F A t₀ (t₀ + N * h))
    (hstep : ∀ j < N, IsStep F (t₀ + j * h) (t₀ + (j + 1) * h) (U j) (Sm j) (V j) (U (j + 1))
      (V (j + 1)) (K j) (Lf j) (S j))
    (hS : ∀ j < N, Sm (j + 1) = S j (t₀ + (j + 1) * h))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = U j * Sm j * (V j)ᵀ)
    (hδ : ‖U 0 * Sm 0 * (V 0)ᵀ - A t₀‖ ≤ δ) (hNT : N * h ≤ T)
    (hsmall : bugGlobalBound L B H T δ ε h + 4 * B * h < ρ) :
    ∀ j ≤ N, ‖U j * Sm j * (V j)ᵀ - A (t₀ + j * h)‖ ≤ bugGlobalBound L B H T δ ε h := by
  rw [bugGlobalBound_eq] at hsmall ⊢
  have hH : 0 ≤ H := hh.trans hhH
  have hc : 0 ≤ bugC₁ L H * ε + bugC₂ L B H * h :=
    add_nonneg (mul_nonneg (bugC₁_nonneg hL hH) hε₀) (mul_nonneg (bugC₂_nonneg hL hB hH) hh)
  have hBh : 0 ≤ B * h := mul_nonneg hB hh
  refine hFL.norm_sub_le_of_fan_uniformGrid (Y := fun j => U j * Sm j * (V j)ᵀ) (Φ := Φ)
    (T := T) (δ₀ := δ) (c := bugC₁ L H * ε + bugC₂ L B H * h) hL hFB hB hh hA
    (fun j hj hnear => ⟨hΦ j hj, hΦ₀ j hj, ?_⟩) hc hδ hNT (by linarith)
  have hnear' : ‖U j * Sm j * (V j)ᵀ - A (t₀ + j * h)‖ ≤
      Real.exp (L * T) * δ + T * Real.exp (L * T) * (bugC₁ L H * ε + bugC₂ L B H * h) := hnear
  obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hj
  have hloc := (hstep j hj).hasLocalError_of_tube hε hFL hL hFB hB ha hb h01
    (hsub.le.trans hhH) (hA.mono ha hb) (by rw [hsub]; linarith)
  rw [hsub] at hloc
  have hle := hloc (Φ j) (hΦ j hj) (hΦ₀ j hj)
  rw [← hS j hj] at hle
  exact hle

/-- The robust error bound `MatrixBUG.global_error_le` for a field that is Lipschitz and bounded
on the whole space, with the normal bound at all rank-`r` matrices, is the instance of
`MatrixBUG.norm_sub_le_of_tube` in which the tube is so wide that the smallness condition holds
trivially. -/
example (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hε : FactoredNormalBound F r ε) (hε₀ : 0 ≤ ε) (hh : 0 ≤ h) (hhH : h ≤ H)
    (hA : ODESolution F A t₀ (t₀ + N * h))
    (hstep : ∀ j < N, IsStep F (t₀ + j * h) (t₀ + (j + 1) * h) (U j) (Sm j) (V j) (U (j + 1))
      (V (j + 1)) (K j) (Lf j) (S j))
    (hS : ∀ j < N, Sm (j + 1) = S j (t₀ + (j + 1) * h))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = U j * Sm j * (V j)ᵀ)
    (hδ : ‖U 0 * Sm 0 * (V 0)ᵀ - A t₀‖ ≤ δ) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖U j * Sm j * (V j)ᵀ - A (t₀ + j * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * bugC₁ L H * ε + T * Real.exp (L * T) * bugC₂ L B H * h := by
  intro j hj hjT
  have hjN : t₀ + j * h ≤ t₀ + N * h := by
    have hle : (j : ℝ) * h ≤ N * h := mul_le_mul_of_nonneg_right (Nat.cast_le.2 hj) hh
    linarith
  change ‖U j * Sm j * (V j)ᵀ - A (t₀ + j * h)‖ ≤ bugGlobalBound L B H T δ ε h
  exact norm_sub_le_of_tube (ρ := bugGlobalBound L B H T δ ε h + 4 * B * h + 1) (N := j)
    (hF.isLipschitzOnTube A _ _ _) hL (hB.isBoundedOnTube A _ _ _) hB.nonneg
    ((factoredNormalBound_iff_univ.1 hε).mono (subset_univ _) le_rfl) hε₀ hh hhH
    (hA.mono le_rfl hjN) (fun i hi => hstep i (hi.trans_le hj))
    (fun i hi => hS i (hi.trans_le hj)) (fun i hi => hΦ i (hi.trans_le hj))
    (fun i hi => hΦ₀ i (hi.trans_le hj)) hδ hjT (lt_add_one _) j le_rfl

end MatrixBUG

end LeanDLRA
