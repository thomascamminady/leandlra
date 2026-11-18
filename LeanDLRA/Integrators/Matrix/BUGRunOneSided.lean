import LeanDLRA.Integrators.Matrix.BUGRun
import LeanDLRA.Integrators.MethodOneSided
import LeanDLRA.Integrators.BUGCapture

/-!
# The fixed-rank BUG integrator: runs with a one-sided Lipschitz constant and smaller constants

`MatrixBUG.exists_run_norm_sub_le` gives a run of the fixed-rank BUG integrator near a solution
`A` with the robust error bound `e^{L T} δ + T e^{L T} (bugC₁ L H ε + bugC₂ L B H h)`
[CerutiLubich2022, Thm. 4]. This file improves the bound in two independent ways:

* the propagation factor `e^{L T}` becomes `e^{ℓ T}`, with `ℓ ≤ L` a one-sided Lipschitz constant
  of `F` on the tube (`StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_oneSided`); for `ℓ < 0`
  the bound and the smallness condition do not contain the final time at all
  (`StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_oneSided_neg`);
* the constants of the local error become `c₁ = √2 (1 + L H e^{L H})` and
  `c₂ = L B (e^{L H} + 2 √2 (1 + L H e^{L H}))` (`IsBUGStepCore.hasLocalError_of_tube_two_mul`),
  at most `bugC₁ L H` and `bugC₂ L B H` (`bugConstants_two_mul_le`).

The Lipschitz constant `L` remains in the local error and in the hypotheses (existence of the
steps); only the propagation of errors from step to step uses `ℓ`.

## Main results

* `MatrixBUG.stepRel.hasLocalError_of_tube_two_mul`: local error of a step near `A`.
* `MatrixBUG.exists_run_norm_sub_le_of_oneSided`: for `0 ≤ ℓ`,
  `‖Y n - A (t₀ + n h)‖ ≤ e^{ℓ T} δ + T e^{ℓ T} (c₁ ε + c₂ h)`.
* `MatrixBUG.exists_run_norm_sub_le_of_oneSided_neg`: for `ℓ < 0`, runs of every length with
  `‖Y n - A (t₀ + n h)‖ ≤ e^{ℓ n h} δ + (h - ℓ⁻¹) (c₁ ε + c₂ h)`.

The `example`s at the end prove `MatrixBUG.exists_run_norm_sub_le` (restated verbatim) from
`MatrixBUG.exists_run_norm_sub_le_of_oneSided`, and show that the hypotheses of the theorem for
`ℓ < 0` hold for the dissipative field `F(t, Y) = -Y`.

## References

* [CerutiLubich2022] G. Ceruti, Ch. Lubich, *An unconventional robust integrator for dynamical
  low-rank approximation*, BIT Numer. Math. 62 (2022), Theorem 4.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixBUG

section Error

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {t₀ h H T ρ ℓ L B ε δ : ℝ}
  {N : ℕ}

/-- **Local error of the matrix BUG step relation near a reference solution, smaller
constants.** Under the hypotheses of `MatrixBUG.stepRel.hasLocalError_of_tube`, every step of
`MatrixBUG.stepRel` from `Y₀` has local error at most `(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))` with
`c₁ = √2 (1 + L H e^{L H})` and `c₂ = L B (e^{L H} + 2 √2 (1 + L H e^{L H}))`. -/
theorem stepRel.hasLocalError_of_tube_two_mul {t₀ t₁ a b : ℝ} {Y₀ Y₁ : Matrix m n ℝ}
    (h : stepRel F r t₀ t₁ Y₀ Y₁) (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hH : t₁ - t₀ ≤ H)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Y₁
      ((t₁ - t₀) * (√2 * (1 + L * H * Real.exp (L * H)) * ε
        + L * B * (Real.exp (L * H) + 2 * √2 * (1 + L * H * Real.exp (L * H))) * (t₁ - t₀))) := by
  obtain ⟨U₀, S₀, V₀, U₁, V₁, K, Lf, S, rfl, hs, rfl⟩ := h
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have h2 : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ := by linarith
  have hmem := hs.isBUGStepCore.toBasisUpdate.mem_tubeSet_of_near hFB hB ha hb h01 hA h2
  refine hs.isBUGStepCore.hasLocalError_of_tube_two_mul (fun t ht => ?_) (fun t ht => ?_) hFL hL
    hFB hB ha hb h01 hH hA hsmall
  · rw [one_sub_leftProj_one_sub_rightProj_apply]
    exact hs.norm_kNormal_le hε (hmem 0 t ht)
  · rw [one_sub_rightProj_one_sub_leftProj_apply]
    exact hs.norm_lNormal_le hε (hmem 1 t ht)

/-- **Existence and error bound for the fixed-rank BUG integrator with a one-sided Lipschitz
constant.** Under the hypotheses of `MatrixBUG.exists_run_norm_sub_le`, let `ℓ ≥ 0` be a one-sided
Lipschitz constant of `F` on the tube. With `c₁ = √2 (1 + L H e^{L H})` and
`c₂ = L B (e^{L H} + 2 √2 (1 + L H e^{L H}))`, if

  `e^{ℓ T} δ + T e^{ℓ T} (c₁ ε + c₂ h) + 4 B h < ρ`,

then the integrator can be run from `Y₀`: there are `Y 0 = Y₀, Y 1, …, Y N`, each obtained from
the previous one by a BUG step of size `h`, all of rank at most `r`, with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{ℓ T} δ + T e^{ℓ T} (c₁ ε + c₂ h)` for all `n ≤ N`.

With `ℓ = L` the bound is at most `bugGlobalBound L B H T δ ε h`. -/
theorem exists_run_norm_sub_le_of_oneSided
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hℓ : IsOneSidedLipschitzFieldOn F (tubeSet A t₀ (t₀ + N * h) ρ) ℓ) (hℓ₀ : 0 ≤ ℓ)
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (ℓ * T) * δ + T * Real.exp (ℓ * T) * (√2 * (1 + L * H * Real.exp (L * H))
      * ε + L * B * (Real.exp (L * H) + 2 * √2 * (1 + L * H * Real.exp (L * H))) * h)
      + 4 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (ℓ * T) * δ
        + T * Real.exp (ℓ * T) * (√2 * (1 + L * H * Real.exp (L * H)) * ε
          + L * B * (Real.exp (L * H) + 2 * √2 * (1 + L * H * Real.exp (L * H))) * h) := by
  have hH : 0 ≤ H := hh.trans hhH
  have hL := hP.L_nonneg
  have hB := hP.B_nonneg
  have hc₀ : 0 ≤ √2 * (1 + L * H * Real.exp (L * H)) * ε
      + L * B * (Real.exp (L * H) + 2 * √2 * (1 + L * H * Real.exp (L * H))) * h := by
    positivity
  have hBh : 0 ≤ B * h := mul_nonneg hB hh
  refine (isTubeLocal_stepRel hrm hrn).exists_run_norm_sub_le_of_oneSided (by norm_num) hP hc hℓ
    hℓ₀ (fun k hk Z₀ Z₁ _ hnear hstep => ?_) hc₀ hh hNT hY₀ hδ hsmall
  obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hk
  have hloc := stepRel.hasLocalError_of_tube_two_mul hstep hε hP.lipschitz hL hP.bounded hB ha hb
    h01 (hsub.le.trans hhH) (hP.sol.mono ha hb) (by rw [hsub]; linarith)
  rwa [hsub] at hloc

/-- **Runs of every length of the fixed-rank BUG integrator for a dissipative problem.** Under
the hypotheses of `MatrixBUG.exists_run_norm_sub_le`, let `ℓ < 0` be a one-sided Lipschitz
constant of `F` on the tube. With `c₁ = √2 (1 + L H e^{L H})`,
`c₂ = L B (e^{L H} + 2 √2 (1 + L H e^{L H}))` and `η = (h - ℓ⁻¹) (c₁ ε + c₂ h)`, if

  `δ + η + 4 B h < ρ`,

then the integrator can be run from `Y₀` for `N` steps, all values of rank at most `r`, with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{ℓ n h} δ + η` for all `n ≤ N`.

Neither the smallness condition nor the bound depends on `N`. -/
theorem exists_run_norm_sub_le_of_oneSided_neg
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hℓ : IsOneSidedLipschitzFieldOn F (tubeSet A t₀ (t₀ + N * h) ρ) ℓ) (hℓ₀ : ℓ < 0)
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : δ + (h - ℓ⁻¹) * (√2 * (1 + L * H * Real.exp (L * H)) * ε
      + L * B * (Real.exp (L * H) + 2 * √2 * (1 + L * H * Real.exp (L * H))) * h)
      + 4 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (ℓ * (n * h)) * δ
        + (h - ℓ⁻¹) * (√2 * (1 + L * H * Real.exp (L * H)) * ε
          + L * B * (Real.exp (L * H) + 2 * √2 * (1 + L * H * Real.exp (L * H))) * h) := by
  have hH : 0 ≤ H := hh.trans hhH
  have hL := hP.L_nonneg
  have hB := hP.B_nonneg
  have hc₀ : 0 ≤ √2 * (1 + L * H * Real.exp (L * H)) * ε
      + L * B * (Real.exp (L * H) + 2 * √2 * (1 + L * H * Real.exp (L * H))) * h := by
    positivity
  have hBh : 0 ≤ B * h := mul_nonneg hB hh
  refine (isTubeLocal_stepRel hrm hrn).exists_run_norm_sub_le_of_oneSided_neg (by norm_num) hP hc
    hℓ hℓ₀ (fun k hk Z₀ Z₁ _ hnear hstep => ?_) hc₀ hh hY₀ hδ hsmall
  obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hk
  have hloc := stepRel.hasLocalError_of_tube_two_mul hstep hε hP.lipschitz hL hP.bounded hB ha hb
    h01 (hsub.le.trans hhH) (hP.sol.mono ha hb) (by rw [hsub]; linarith)
  rwa [hsub] at hloc

end Error

/-! ### The theorem with the Lipschitz constant, and non-vacuity -/

section Examples

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}

/-- `MatrixBUG.exists_run_norm_sub_le`, restated verbatim, follows from
`MatrixBUG.exists_run_norm_sub_le_of_oneSided` with `ℓ = L` and `bugConstants_two_mul_le`. -/
example {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {t₀ h H T ρ L B ε δ : ℝ}
    {N : ℕ} (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : bugGlobalBound L B H T δ ε h + 4 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤ bugGlobalBound L B H T δ ε h := by
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg N) hh).trans hNT
  have hle := mul_le_mul_of_nonneg_left (bugConstants_two_mul_le hP.L_nonneg hP.B_nonneg
    (hh.trans hhH) hε₀ hh) (mul_nonneg hT (Real.exp_pos (L * T)).le)
  rw [bugGlobalBound_eq] at hsmall ⊢
  obtain ⟨Y, hY0, hY, hbd⟩ := exists_run_norm_sub_le_of_oneSided hP hc
    hP.isOneSidedLipschitzFieldOn hP.L_nonneg hε hε₀ hh hhH hNT hrm hrn hY₀ hδ (by linarith)
  exact ⟨Y, hY0, hY, fun n hn => ⟨(hbd n hn).1, (hbd n hn).2.trans (by linarith)⟩⟩

/-- The field `F(t, Y) = -Y` has no normal component at the matrices `U S Vᵀ`. -/
private theorem factoredNormalBoundOn_neg (D : Set (ℝ × Matrix m n ℝ)) :
    FactoredNormalBoundOn (fun _ (Y : Matrix m n ℝ) => (-1 : ℝ) • Y) r D 0 := by
  intro t U V S hU _ _
  have hU' : (1 - U * Uᵀ) * U = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one, sub_self]
  have h0 : (1 - U * Uᵀ) * ((-1 : ℝ) • (U * S * Vᵀ)) * (1 - V * Vᵀ) = 0 := by
    simp only [Matrix.mul_smul, ← Matrix.mul_assoc, hU', Matrix.zero_mul, smul_zero]
  change ‖(1 - U * Uᵀ) * ((-1 : ℝ) • (U * S * Vᵀ)) * (1 - V * Vᵀ)‖ ≤ 0
  rw [h0, norm_zero]

/-- The rank-one start value `(1/4, 0)ᵀ (1, 0)` of the examples has norm at most `1/4`. -/
private theorem norm_vecMulVec_quarter_le :
    ‖Matrix.vecMulVec ![(1 / 4 : ℝ), 0] ![1, 0]‖ ≤ 1 / 4 := by
  have h2 : ‖Matrix.vecMulVec ![(1 / 4 : ℝ), 0] ![1, 0]‖ ^ 2 = 1 / 16 := by
    rw [Frobenius.norm_sq_eq_sum]
    norm_num [Matrix.vecMulVec_apply, Fin.sum_univ_two]
  nlinarith [norm_nonneg (Matrix.vecMulVec ![(1 / 4 : ℝ), 0] ![1, 0])]

/-- The term `c₂ h` of the local error for `L = B = 1` and `h = H = 1/100` is at most `7/100`:
`e^{1/100} ≤ 3` and `√2 ≤ 3/2`. -/
private theorem localErrorConst_le :
    1 * 1 * (Real.exp (1 * (1 / 100)) + 2 * √2 * (1 + 1 * (1 / 100) * Real.exp (1 * (1 / 100))))
      * (1 / 100) ≤ (7 / 100 : ℝ) := by
  have he : Real.exp (1 * (1 / 100)) ≤ 3 :=
    (Real.exp_le_exp.2 (by norm_num : (1 : ℝ) * (1 / 100) ≤ 1)).trans
      (Real.exp_one_lt_d9.le.trans (by norm_num))
  have he0 := Real.exp_pos (1 * (1 / 100))
  have hs0 := Real.sqrt_nonneg 2
  have hs : √2 ≤ 3 / 2 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  nlinarith [mul_le_mul hs he he0.le (by norm_num : (0 : ℝ) ≤ 3 / 2)]

/-- **Non-vacuity of `MatrixBUG.exists_run_norm_sub_le_of_oneSided_neg`**, for the dissipative
field `F(t, Y) = -Y` on `2 × 2` matrices with the solution `A = 0` (Lipschitz constant `1`, bound
`ρ = 1` on the tube of radius `1`, one-sided Lipschitz constant `-1`, no normal component, so
`ε = 0`), rank `r = 1`, step size `h = H = 1/100` and the rank-one start value
`Y₀ = (1/4, 0)ᵀ (1, 0)` with `δ = 1/4`. Here `c₂ h ≤ 7/100`, so the smallness condition holds,
and for every number of steps `N` the theorem gives a run of the BUG integrator of rank at most
`1` with `‖Y n‖ ≤ e^{-n/100} / 4 + 1/10`. -/
example (t₀ : ℝ) (N : ℕ) :
    ∃ Y : ℕ → Matrix (Fin 2) (Fin 2) ℝ, Y 0 = Matrix.vecMulVec ![1 / 4, 0] ![1, 0] ∧
      IsRun (stepRel (fun _ Y => (-1 : ℝ) • Y) 1) (uniformGrid t₀ (1 / 100)) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ 1 ∧ ‖Y n‖ ≤ Real.exp (-(n / 100)) / 4 + 1 / 10 := by
  have hP : DLRAProblem (fun _ (Y : Matrix (Fin 2) (Fin 2) ℝ) => (-1 : ℝ) • Y) (fun _ => 0) t₀
      (t₀ + N * (1 / 100)) 1 1 1 := by
    refine ⟨⟨continuousOn_const, fun t _ => ?_⟩, zero_le_one, zero_le_one, fun t _ x y _ _ => ?_,
      fun t _ x hx => ?_⟩
    · simpa using hasDerivWithinAt_const t (Ici t) (0 : Matrix (Fin 2) (Fin 2) ℝ)
    · exact le_of_eq (by rw [← smul_sub, norm_smul, norm_neg, norm_one, one_mul])
    · simpa [norm_smul] using hx
  have hc := localErrorConst_le
  obtain ⟨Y, hY0, hY, hbd⟩ := exists_run_norm_sub_le_of_oneSided_neg hP
    (continuous_snd.const_smul (-1 : ℝ)).continuousOn
    (fun t x y _ _ => isOneSidedLipschitzField_smul_id (-1) t x y) (by norm_num)
    (factoredNormalBoundOn_neg _) le_rfl (by norm_num) (le_refl (1 / 100 : ℝ)) (by simp)
    (by simp) (Y₀ := Matrix.vecMulVec ![(1 / 4 : ℝ), 0] ![1, 0])
    (Matrix.rank_vecMulVec_le _ _) (δ := 1 / 4)
    (by simp only [sub_zero]; exact norm_vecMulVec_quarter_le) (by linarith)
  refine ⟨Y, hY0, hY, fun n hn => ⟨(hbd n hn).1, ?_⟩⟩
  have h1 := (hbd n hn).2
  have hexp : Real.exp (-1 * (n * (1 / 100))) = Real.exp (-(n / 100)) := by
    congr 1
    ring
  rw [sub_zero, hexp] at h1
  linarith

/-- **Non-vacuity of `MatrixBUG.stepRel.hasLocalError_of_tube_two_mul`** for the dissipative
field `F(t, Y) = -Y` on `2 × 2` matrices with the solution `A = 0` (Lipschitz constant `1`, bound
`ρ = 1` on the tube of radius `1`, no normal component, `ε = 0`), rank `r = 1` and the rank-one
start value `Y₀ = (1/4, 0)ᵀ (1, 0)`: the margin `‖Y₀‖ + 4 ρ (t₁ - t₀) < ρ` holds for the step size
`t₁ - t₀ = H = 1/100`, there is a BUG step, and every such step has local error at most
`(1/100) (7/100)`. -/
example (t₀ : ℝ) :
    ∃ Y₁, stepRel (fun _ Y => (-1 : ℝ) • Y) 1 t₀ (t₀ + 1 / 100)
        (Matrix.vecMulVec ![(1 / 4 : ℝ), 0] ![1, 0]) Y₁ ∧
      HasLocalError (fun _ Y => (-1 : ℝ) • Y) t₀ (t₀ + 1 / 100)
        (Matrix.vecMulVec ![(1 / 4 : ℝ), 0] ![1, 0]) Y₁ (1 / 100 * (7 / 100)) := by
  have h01 : t₀ ≤ t₀ + 1 / 100 := by linarith
  have hsub : t₀ + 1 / 100 - t₀ = 1 / 100 := add_sub_cancel_left t₀ (1 / 100)
  have hP : DLRAProblem (fun _ (Y : Matrix (Fin 2) (Fin 2) ℝ) => (-1 : ℝ) • Y) (fun _ => 0) t₀
      (t₀ + 1 / 100) 1 1 1 := by
    refine ⟨⟨continuousOn_const, fun t _ => ?_⟩, zero_le_one, zero_le_one, fun t _ x y _ _ => ?_,
      fun t _ x hx => ?_⟩
    · simpa using hasDerivWithinAt_const t (Ici t) (0 : Matrix (Fin 2) (Fin 2) ℝ)
    · exact le_of_eq (by rw [← smul_sub, norm_smul, norm_neg, norm_one, one_mul])
    · simpa [norm_smul] using hx
  have hlip : IsLipschitzField (fun _ (Y : Matrix (Fin 2) (Fin 2) ℝ) => (-1 : ℝ) • Y) 1 :=
    fun _ x y => le_of_eq (by rw [← smul_sub, norm_smul, norm_neg, norm_one, one_mul])
  obtain ⟨Y₁, hstep⟩ := exists_stepRel hlip (fun _ => continuousOn_const) h01 (by simp) (by simp)
    (Matrix.rank_vecMulVec_le ![(1 / 4 : ℝ), 0] ![1, 0])
  refine ⟨Y₁, hstep, (hstep.hasLocalError_of_tube_two_mul (H := 1 / 100)
    (factoredNormalBoundOn_neg _) hP.lipschitz zero_le_one hP.bounded zero_le_one le_rfl le_rfl
    h01 hsub.le hP.sol ?_).mono ?_⟩
  · simp only [hsub, sub_zero]
    linarith [norm_vecMulVec_quarter_le]
  · rw [hsub]
    linarith [localErrorConst_le]

end Examples

end MatrixBUG

end LeanDLRA
