import LeanDLRA.Integrators.MethodGrid

/-!
# Tube-local methods with a tolerance per step

Many low-rank integrators end a step with a truncation to a tolerance `ϑ`: the result of the step
is replaced by a value of lower rank at distance at most `ϑ`. The distance does not depend on the
step size, so a truncated step has local error `h c + ϑ`, where `h c` is the local error of the
step without the truncation. The run theorem `StepMethod.IsTubeLocal.exists_run_norm_sub_le`
requires a local error of the form `h c`. This file adds the run theorem for local errors
`h c + ϑ`: the run exists and satisfies

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} (δ + n ϑ) + T e^{L T} c`.

Since `n h ≤ T`, the term `n ϑ` is at most `(T / h) ϑ` for `h > 0`: this is the term of the form
tolerance over step size in the error bounds of integrators with truncation, for example the term
`ϑ / h` of `parallelBUG_global_error_paper`. No definition is added: a method with truncation is
a step relation like any other, and `StepMethod.IsTubeLocal` keeps its meaning.

## Main results

* `HasLocalError.add_of_norm_sub_le`: if `Yh` has local error `δ` as the result of a step and
  `‖Y₁ - Yh‖ ≤ ϑ`, then `Y₁` has local error `δ + ϑ`.
* `StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_tol`: a tube-local method with margin
  constant `κ ≥ 2` whose steps have local error `h c + ϑ` can be run for `N` steps of size `h`,
  and the run satisfies `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} (δ + n ϑ) + T e^{L T} c`, if
  `e^{L T} (δ + N ϑ) + T e^{L T} c + κ B h < ρ`.

## Implementation notes

The run theorem is the case of `StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_isGrid` for the
uniform grid and the local error bounds `δ n = h c + ϑ`. The part `h c` of the local errors is
summed by `uniformGrid_errorBound_le`; each of the `n` tolerances is amplified by at most
`e^{L T}`. The tolerances enter the bound `n` times, not `n h` times: for a fixed tolerance the
bound grows with the number of steps. For the bound to be of size `ϑ₀` at time `T` the tolerance
has to be chosen proportional to the step size, `ϑ = h ϑ₀ / T`.
-/

open Set Finset

namespace LeanDLRA

/-! ### Local error after a perturbation -/

section Perturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Local error after a perturbation.** If `Yh` has local error `δ` as the result of a step from
`Y₀`, then every `Y₁` with `‖Y₁ - Yh‖ ≤ ϑ` has local error `δ + ϑ`. This is the local error of a
step that is followed by a truncation to the tolerance `ϑ`. -/
theorem HasLocalError.add_of_norm_sub_le {F : ℝ → E → E} {t₀ t₁ δ ϑ : ℝ} {Y₀ Yh Y₁ : E}
    (h : HasLocalError F t₀ t₁ Y₀ Yh δ) (hY₁ : ‖Y₁ - Yh‖ ≤ ϑ) :
    HasLocalError F t₀ t₁ Y₀ Y₁ (δ + ϑ) := fun Φ hΦ hΦ₀ => by
  have h1 := h Φ hΦ hΦ₀
  have h2 := norm_sub_le_norm_sub_add_norm_sub Y₁ Yh (Φ t₁)
  linarith

end Perturbation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The run theorem with a tolerance per step -/

section Tolerance

variable {F : ℝ → E → E} {A : ℝ → E} {M : StepMethod E} {Adm : E → Prop} {κ : ℝ} {N : ℕ}
  {t₀ h T c δ ϑ ρ L B : ℝ}

/-- **Existence of a run and error bound for a tube-local method with a tolerance per step.** Let
`A` solve `y' = F(t, y)` on `[t₀, t₀ + N h]`, and let `F` be `L`-Lipschitz and bounded by `B` on
the tube of radius `ρ` around `A` (`DLRAProblem`) and continuous there. Let the method `M` be
tube-local with admissible values `Adm` and margin constant `κ ≥ 2` (`StepMethod.IsTubeLocal`),
and suppose that every step `n` of `M F` whose start value satisfies `Adm` and lies within
`e^{L T} (δ + N ϑ) + T e^{L T} c` of `A (t₀ + n h)` has local error `h c + ϑ`. Let `0 ≤ c`,
`0 ≤ ϑ`, `0 ≤ h`, `N h ≤ T`, and let `Y₀` satisfy `Adm Y₀` and `‖Y₀ - A t₀‖ ≤ δ`. If

  `e^{L T} (δ + N ϑ) + T e^{L T} c + κ B h < ρ`,

then the method can be run from `Y₀`: there are `Y 0 = Y₀, Y 1, …, Y N`, each obtained from the
previous one by a step of `M F` of size `h`, with

  `Adm (Y n)` and `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} (δ + n ϑ) + T e^{L T} c` for all `n ≤ N`.

Nothing is assumed about `F` outside the tube. This is the case of
`StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_isGrid` for the uniform grid and the local error
bounds `δ n = h c + ϑ`; for `ϑ = 0` it is `StepMethod.IsTubeLocal.exists_run_norm_sub_le`. -/
theorem StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_tol [CompleteSpace E]
    (hM : M.IsTubeLocal Adm κ) (hκ : 2 ≤ κ) (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hloc : ∀ n < N, ∀ Y₀ Y₁, Adm Y₀ →
      ‖Y₀ - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * (δ + N * ϑ) + T * Real.exp (L * T) * c →
      M F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ →
      HasLocalError F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ (h * c + ϑ))
    (hc₀ : 0 ≤ c) (hϑ : 0 ≤ ϑ) (hh : 0 ≤ h) (hNT : N * h ≤ T) {Y₀ : E} (hY₀ : Adm Y₀)
    (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * (δ + N * ϑ) + T * Real.exp (L * T) * c + κ * B * h < ρ) :
    ∃ Y : ℕ → E, Y 0 = Y₀ ∧ IsRun (M F) (uniformGrid t₀ h) N Y ∧ ∀ n ≤ N, Adm (Y n) ∧
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * (δ + n * ϑ) + T * Real.exp (L * T) * c := by
  have e : ∀ n : ℕ, uniformGrid t₀ h (n + 1) = t₀ + ((n : ℝ) + 1) * h := fun n => by
    simp [uniformGrid]
  have e0 : uniformGrid t₀ h 0 = t₀ := by simp [uniformGrid]
  have hP0 : DLRAProblem F A (uniformGrid t₀ h 0) (uniformGrid t₀ h N) ρ L B := by
    rw [e0]
    exact hP
  have hc0 : ContinuousOn (Function.uncurry F)
      (tubeSet A (uniformGrid t₀ h 0) (uniformGrid t₀ h N) ρ) := by
    rw [e0]
    exact hc
  have hE : 0 ≤ Real.exp (L * T) := (Real.exp_pos _).le
  -- the error bound of the grid theorem is at most the bound of the statement
  have hb : ∀ k ≤ N, Real.exp (L * (uniformGrid t₀ h k - uniformGrid t₀ h 0)) *
      ‖Y₀ - A (uniformGrid t₀ h 0)‖ + ∑ j ∈ range k,
        Real.exp (L * (uniformGrid t₀ h k - uniformGrid t₀ h (j + 1))) * (h * c + ϑ) ≤
      Real.exp (L * T) * (δ + k * ϑ) + T * Real.exp (L * T) * c := fun k hk => by
    have hkT : (k : ℝ) * h ≤ T :=
      (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) hh).trans hNT
    have h1 := uniformGrid_errorBound_le (c := c) (δ₀ := δ) t₀ (n := k) hP.L_nonneg hh hc₀ hkT
      (norm_nonneg (Y₀ - A (uniformGrid t₀ h 0))) (by rw [e0]; exact hδ)
    have h2 : ∑ j ∈ range k,
        Real.exp (L * (uniformGrid t₀ h k - uniformGrid t₀ h (j + 1))) * ϑ ≤
        ∑ _j ∈ range k, Real.exp (L * T) * ϑ := by
      refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hP.L_nonneg)) hϑ
      have hjk : uniformGrid t₀ h k - uniformGrid t₀ h (j + 1) = k * h - (j + 1) * h := by
        simp only [uniformGrid, Nat.cast_add, Nat.cast_one]
        ring
      have hj : 0 ≤ ((j : ℝ) + 1) * h := mul_nonneg (by positivity) hh
      rw [hjk]
      linarith
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    have h3 : ∑ j ∈ range k,
        Real.exp (L * (uniformGrid t₀ h k - uniformGrid t₀ h (j + 1))) * (h * c + ϑ) =
        ∑ j ∈ range k, Real.exp (L * (uniformGrid t₀ h k - uniformGrid t₀ h (j + 1))) * (h * c) +
          ∑ j ∈ range k, Real.exp (L * (uniformGrid t₀ h k - uniformGrid t₀ h (j + 1))) * ϑ := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => mul_add _ _ _
    rw [h3]
    have h4 : Real.exp (L * T) * (δ + k * ϑ) =
        Real.exp (L * T) * δ + k * (Real.exp (L * T) * ϑ) := by ring
    rw [h4]
    linarith
  have hmono : ∀ k ≤ N, Real.exp (L * T) * (δ + k * ϑ) + T * Real.exp (L * T) * c ≤
      Real.exp (L * T) * (δ + N * ϑ) + T * Real.exp (L * T) * c := fun k hk => by
    have hkN : (k : ℝ) * ϑ ≤ N * ϑ := mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) hϑ
    have h1 : δ + k * ϑ ≤ δ + N * ϑ := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hE
    linarith
  obtain ⟨Y, hY0, hY, hbd⟩ := StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_isGrid
    (R := fun _ => Real.exp (L * T) * (δ + N * ϑ) + T * Real.exp (L * T) * c)
    (δ := fun _ => h * c + ϑ) hM hκ (isGrid_uniformGrid hh N) hP0 hc0
    (fun k hk Z₀ Z₁ hZ₀ hnear hstep => by
      rw [e k] at hstep ⊢
      exact hloc k hk Z₀ Z₁ hZ₀ hnear hstep)
    hY₀ (fun k hk => (hb k hk.le).trans (hmono k hk.le))
    (fun k _ => by
      rw [uniformGrid_succ_sub]
      exact hsmall)
  exact ⟨Y, hY0, hY, fun n hn => ⟨(hbd n hn).1, (hbd n hn).2.trans (hb n hn)⟩⟩

end Tolerance

/-! ### Non-vacuity: explicit Euler steps followed by rounding -/

section Examples

/-- The affine function `t ↦ y₀ + (t - a) v` solves `y' = v`. -/
private theorem odeSolution_affine_aux (v y₀ : E) (a b : ℝ) :
    ODESolution (fun _ _ => v) (fun t => y₀ + (t - a) • v) a b :=
  ⟨by fun_prop, fun t _ => by
    have hd : HasDerivAt (fun t : ℝ => y₀ + (t - a) • v) v t := by
      simpa using (((hasDerivAt_id t).sub_const a).smul_const v).const_add y₀
    exact hd.hasDerivWithinAt⟩

/-- For the constant field `F t x = v` the explicit Euler step is exact: it has local error
`0`. -/
private theorem hasLocalError_euler_const_aux (v Y₀ : E) {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁) :
    HasLocalError (fun _ _ => v) t₀ t₁ Y₀ (Y₀ + (t₁ - t₀) • v) 0 := fun Φ hΦ hΦ₀ => by
  have hΨ := odeSolution_affine_aux v Y₀ t₀ t₁
  have hd := dist_le_of_trajectories_ODE (v := fun _ _ => v) (K := 0) (δ := 0)
    (fun _ => LipschitzWith.const v) hΨ.cont hΨ.deriv hΦ.cont hΦ.deriv (by simp [hΦ₀])
    t₁ (right_mem_Icc.2 h01)
  rw [zero_mul, dist_le_zero] at hd
  rw [← hd]
  simp

/-- The explicit Euler method followed by a perturbation of size at most `ϑ` (a rounding of the
result), `‖Y₁ - (Y₀ + (t₁ - t₀) G(t₀, Y₀))‖ ≤ ϑ`, is tube-local for every margin constant
`κ ≥ 0`, with every value admissible: the step evaluates the field only at the start value. -/
private theorem isTubeLocal_roundedEuler_aux {ϑ κ : ℝ} (hϑ : 0 ≤ ϑ) (hκ : 0 ≤ κ) :
    StepMethod.IsTubeLocal (E := E)
      (fun G s₀ s₁ Y₀ Y₁ => ‖Y₁ - (Y₀ + (s₁ - s₀) • G s₀ Y₀)‖ ≤ ϑ) (fun _ => True) κ where
  exists_step := @fun G _ t₀ t₁ Y₀ _ _ _ _ => ⟨Y₀ + (t₁ - t₀) • G t₀ Y₀, by simpa using hϑ⟩
  adm_of_step := fun _ _ _ => trivial
  step_of_tubeExt := @fun F A a b ρ B t₀ t₁ Y₀ Y₁ _ hB ha hb h01 _ _ hsmall hstep => by
    have h0 : 0 ≤ κ * B * (t₁ - t₀) := mul_nonneg (mul_nonneg hκ hB) (sub_nonneg.2 h01)
    have hmem : t₀ ∈ Icc a b := ⟨ha, h01.trans hb⟩
    have hnear : ‖Y₀ - A t₀‖ ≤ ρ := by linarith
    simpa only [tubeExt_eq hmem hnear] using hstep

/-- **Non-vacuity of `HasLocalError.add_of_norm_sub_le`**, for the nonzero constant field
`F t x = v`: the explicit Euler step `Y₀ + (t₁ - t₀) v` is exact, so every `Y₁` within `ϑ` of it
has local error `ϑ`. -/
example (v Y₀ Y₁ : E) {t₀ t₁ ϑ : ℝ} (h01 : t₀ ≤ t₁) (hY₁ : ‖Y₁ - (Y₀ + (t₁ - t₀) • v)‖ ≤ ϑ) :
    HasLocalError (fun _ _ => v) t₀ t₁ Y₀ Y₁ ϑ :=
  ((hasLocalError_euler_const_aux v Y₀ h01).add_of_norm_sub_le hY₁).mono (zero_add ϑ).le

/-- **Non-vacuity of `StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_tol`**, for the explicit
Euler method followed by a perturbation of size at most `ϑ` and the nonzero constant field
`F t x = v` with the solution `A t = x₀ + (t - t₀) v`. The field is Lipschitz with constant `0`
and bounded by `‖v‖` on every tube, and an exact Euler step is exact, so every step has local
error `h · 0 + ϑ` with a positive tolerance `ϑ`. The theorem gives a run from every `Y₀` with
`‖Y₀ - x₀‖ ≤ δ`, with `‖Y n - A (t₀ + n h)‖ ≤ δ + n ϑ`, if `δ + N ϑ + 2 ‖v‖ h < ρ`. -/
example [CompleteSpace E] (v x₀ Y₀ : E) {t₀ h T δ ϑ ρ : ℝ} {N : ℕ} (hϑ : 0 ≤ ϑ) (hh : 0 ≤ h)
    (hNT : N * h ≤ T) (hδ : ‖Y₀ - x₀‖ ≤ δ) (hsmall : δ + N * ϑ + 2 * ‖v‖ * h < ρ) :
    ∃ Y : ℕ → E, Y 0 = Y₀ ∧
      IsRun (fun s₀ s₁ Y₀ Y₁ => ‖Y₁ - (Y₀ + (s₁ - s₀) • v)‖ ≤ ϑ) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, ‖Y n - (x₀ + ((n : ℝ) * h) • v)‖ ≤ δ + n * ϑ := by
  have hP : DLRAProblem (fun _ _ => v) (fun t => x₀ + (t - t₀) • v) t₀ (t₀ + N * h) ρ 0 ‖v‖ :=
    ⟨odeSolution_affine_aux v x₀ t₀ _, le_rfl, norm_nonneg v, fun t _ x y _ _ => by simp,
      fun t _ x _ => le_rfl⟩
  obtain ⟨Y, hY0, hY, hbd⟩ :=
    (isTubeLocal_roundedEuler_aux (E := E) hϑ zero_le_two).exists_run_norm_sub_le_of_tol
      le_rfl hP continuousOn_const (c := 0) (T := T) (δ := δ) (ϑ := ϑ)
      (fun n hn Z₀ Z₁ _ _ hstep =>
        ((hasLocalError_euler_const_aux v Z₀
          (uniformGrid_step (t₀ := t₀) hh hn).2.1).add_of_norm_sub_le hstep).mono (by simp))
      le_rfl hϑ hh hNT trivial (by simpa using hδ) (by simpa using hsmall)
  exact ⟨Y, hY0, hY, fun n hn => by simpa using (hbd n hn).2⟩

end Examples

end LeanDLRA
