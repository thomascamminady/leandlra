import LeanDLRA.Integrators.Method

/-!
# Tube-local methods on general grids

`StepMethod.IsTubeLocal.exists_run_norm_sub_le` runs a tube-local method on the uniform grid
`t₀ + n h`, with the same local error bound `h c` in every step. This file adds the run theorem
for a grid `τ 0 ≤ τ 1 ≤ ⋯ ≤ τ N` with variable step sizes and a local error bound `δ n` that may
depend on the step. This is the form needed for step-size control and for steps whose local
error is not proportional to the step size.

## Main results

* `StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_isGrid`: a tube-local method with margin
  constant `κ ≥ 2` can be run on a grid `τ` from every admissible start value `Y₀`, and the run
  satisfies
  `‖Y n - A (τ n)‖ ≤ e^{L (τ n - τ 0)} ‖Y₀ - A (τ 0)‖ + ∑_{k<n} e^{L (τ n - τ (k + 1))} δ k`,
  if this bound, increased by the margin `κ B (τ (n + 1) - τ n)` of step `n`, stays below the
  radius of the tube.

## Implementation notes

The theorem is `exists_isRun_norm_sub_le_of_tube` for the step relation `M F` of a tube-local
method `M`: the properties (E) and (T) of `StepMethod.IsTubeLocal` give a step of `F` from every
admissible value well inside the tube, and the property (I) gives the invariant. As in that
theorem, the numbers `R n` are any upper bounds of the error bound; the local error has to be
shown only for steps that start within `R n` of the solution.
-/

open Set Finset

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The run theorem on a grid -/

section Grid

variable {F : ℝ → E → E} {A : ℝ → E} {M : StepMethod E} {Adm : E → Prop} {κ : ℝ} {N : ℕ}
  {τ : ℕ → ℝ} {R δ : ℕ → ℝ} {ρ L B : ℝ}

/-- **Existence of a run and error bound for a tube-local method on a grid.** Let `τ` be a grid
with `N` steps, let `A` solve `y' = F(t, y)` on `[τ 0, τ N]`, and let `F` be `L`-Lipschitz and
bounded by `B` on the tube of radius `ρ` around `A` (`DLRAProblem`) and continuous there. Let the
method `M` be tube-local with admissible values `Adm` and margin constant `κ ≥ 2`
(`StepMethod.IsTubeLocal`), and suppose that every step `n` of `M F` whose start value satisfies
`Adm` and lies within `R n` of `A (τ n)` has local error `δ n`. Let `Adm Y₀`. If for all `n < N`

  `e^{L (τ n - τ 0)} ‖Y₀ - A (τ 0)‖ + ∑_{k<n} e^{L (τ n - τ (k + 1))} δ k ≤ R n` and
  `R n + κ B (τ (n + 1) - τ n) < ρ`,

then the method can be run from `Y₀` on the grid: there are `Y 0 = Y₀, Y 1, …, Y N`, each
obtained from the previous one by a step of `M F` from `τ n` to `τ (n + 1)`, with

  `Adm (Y n)` and
  `‖Y n - A (τ n)‖ ≤ e^{L (τ n - τ 0)} ‖Y₀ - A (τ 0)‖ + ∑_{k<n} e^{L (τ n - τ (k + 1))} δ k`

for all `n ≤ N`. Nothing is assumed about `F` outside the tube. On the uniform grid with
`δ n = h c`, the estimate `uniformGrid_errorBound_le` of the right-hand side gives the bound of
`StepMethod.IsTubeLocal.exists_run_norm_sub_le`. -/
theorem StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_isGrid [CompleteSpace E]
    (hM : M.IsTubeLocal Adm κ) (hκ : 2 ≤ κ) (hτ : IsGrid τ N)
    (hP : DLRAProblem F A (τ 0) (τ N) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A (τ 0) (τ N) ρ))
    (hloc : ∀ n < N, ∀ Y₀ Y₁, Adm Y₀ → ‖Y₀ - A (τ n)‖ ≤ R n → M F (τ n) (τ (n + 1)) Y₀ Y₁ →
      HasLocalError F (τ n) (τ (n + 1)) Y₀ Y₁ (δ n))
    {Y₀ : E} (hY₀ : Adm Y₀)
    (hR : ∀ n < N, Real.exp (L * (τ n - τ 0)) * ‖Y₀ - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k ≤ R n)
    (hsmall : ∀ n < N, R n + κ * B * (τ (n + 1) - τ n) < ρ) :
    ∃ Y : ℕ → E, Y 0 = Y₀ ∧ IsRun (M F) τ N Y ∧ ∀ n ≤ N, Adm (Y n) ∧
      ‖Y n - A (τ n)‖ ≤ Real.exp (L * (τ n - τ 0)) * ‖Y₀ - A (τ 0)‖ +
        ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k := by
  have hstepB : ∀ n < N, 2 * B * (τ (n + 1) - τ n) ≤ κ * B * (τ (n + 1) - τ n) := fun n hn =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hκ hP.B_nonneg)
      (sub_nonneg.2 (hτ.mono n hn))
  refine exists_isRun_norm_sub_le_of_tube (M := M F) (Adm := fun _ => Adm) hτ hP hc
    (fun n hn Z₀ hZ₀ hnear => ?_) (fun n hn Z₀ Z₁ hZ₀ _ hstep => ?_) hloc hY₀ hR
    (fun n hn => by linarith [hstepB n hn, hsmall n hn])
  · -- a step of the extended field exists, and it is a step of `F`
    have h01 : τ n ≤ τ (n + 1) := hτ.mono n hn
    have ha : τ 0 ≤ τ n := hτ.le_of_le (Nat.zero_le n) hn.le
    have hb : τ (n + 1) ≤ τ N := hτ.le_of_le (Nat.succ_le_of_lt hn) le_rfl
    have h2 : 0 ≤ 2 * B * (τ (n + 1) - τ n) :=
      mul_nonneg (mul_nonneg zero_le_two hP.B_nonneg) (sub_nonneg.2 h01)
    have hR0 : 0 ≤ R n := (norm_nonneg _).trans hnear
    have hρ : 0 ≤ ρ := by linarith [hstepB n hn, hsmall n hn]
    have hGL : IsLipschitzField (tubeExt F A (τ 0) (τ N) ρ) L :=
      isLipschitzField_tubeExt hP.lipschitz hP.L_nonneg hρ
    have hGc : ∀ x, ContinuousOn (fun t => tubeExt F A (τ 0) (τ N) ρ t x) (Icc (τ 0) (τ N)) :=
      fun x => continuousOn_tubeExt hc hP.sol.cont hρ x
    obtain ⟨Y₁, hY₁⟩ := hM.exists_step hGL (fun x => (hGc x).mono (Icc_subset_Icc ha hb)) h01
      hZ₀
    exact ⟨Y₁, hM.step_of_tubeExt hP.bounded hP.B_nonneg ha hb h01 (hP.sol.mono ha hb) hZ₀
      (by linarith [hsmall n hn]) hY₁⟩
  · exact hM.adm_of_step (hτ.mono n hn) hZ₀ hstep

end Grid

/-! ### Non-vacuity: inexact Euler steps on a grid -/

section Examples

/-- The explicit Euler method with an error of at most `θ (t₁ - t₀)` in the step from `t₀` to
`t₁`, `‖Y₁ - (Y₀ + (t₁ - t₀) G(t₀, Y₀))‖ ≤ θ (t₁ - t₀)`, is tube-local for every margin constant
`κ ≥ 0`, with every value admissible: the step evaluates the field only at the start value. -/
private theorem isTubeLocal_inexactEuler_aux {θ κ : ℝ} (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) :
    StepMethod.IsTubeLocal (E := E)
      (fun G s₀ s₁ Y₀ Y₁ => ‖Y₁ - (Y₀ + (s₁ - s₀) • G s₀ Y₀)‖ ≤ θ * (s₁ - s₀))
      (fun _ => True) κ where
  exists_step := @fun G _ t₀ t₁ Y₀ _ _ h01 _ =>
    ⟨Y₀ + (t₁ - t₀) • G t₀ Y₀, by simpa using mul_nonneg hθ (sub_nonneg.2 h01)⟩
  adm_of_step := fun _ _ _ => trivial
  step_of_tubeExt := @fun F A a b ρ B t₀ t₁ Y₀ Y₁ _ hB ha hb h01 _ _ hsmall hstep => by
    have h0 : 0 ≤ κ * B * (t₁ - t₀) := mul_nonneg (mul_nonneg hκ hB) (sub_nonneg.2 h01)
    have hmem : t₀ ∈ Icc a b := ⟨ha, h01.trans hb⟩
    have hnear : ‖Y₀ - A t₀‖ ≤ ρ := by linarith
    simpa only [tubeExt_eq hmem hnear] using hstep

/-- **Non-vacuity of `StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_isGrid`**, for the
explicit Euler method with an error of at most `θ (t₁ - t₀)` per step, the nonzero constant field
`F t x = v` with the solution `A t = x₀ + (t - τ 0) v`, and an arbitrary grid `τ` (for example
the squares `τ n = n²`). The field is Lipschitz with constant `0` and bounded by `‖v‖` on every
tube, and an exact Euler step is exact, so step `n` has local error `θ (τ (n + 1) - τ n)`, which
depends on the step. The sum of the local errors telescopes: the theorem gives a run from every
`Y₀` with `‖Y n - A (τ n)‖ ≤ ‖Y₀ - x₀‖ + θ (τ n - τ 0)`, if
`‖Y₀ - x₀‖ + θ (τ N - τ 0) + 2 ‖v‖ (τ (n + 1) - τ n) < ρ` for every step. -/
example [CompleteSpace E] (v x₀ Y₀ : E) {τ : ℕ → ℝ} {N : ℕ} {θ ρ : ℝ} (hτ : IsGrid τ N)
    (hθ : 0 ≤ θ)
    (hsmall : ∀ n < N, ‖Y₀ - x₀‖ + θ * (τ N - τ 0) + 2 * ‖v‖ * (τ (n + 1) - τ n) < ρ) :
    ∃ Y : ℕ → E, Y 0 = Y₀ ∧
      IsRun (fun s₀ s₁ Y₀ Y₁ => ‖Y₁ - (Y₀ + (s₁ - s₀) • v)‖ ≤ θ * (s₁ - s₀)) τ N Y ∧
      ∀ n ≤ N, ‖Y n - (x₀ + (τ n - τ 0) • v)‖ ≤ ‖Y₀ - x₀‖ + θ * (τ n - τ 0) := by
  have aff : ∀ (y₀ : E) (a b : ℝ),
      ODESolution (fun _ _ => v) (fun t => y₀ + (t - a) • v) a b := fun y₀ a b =>
    ⟨by fun_prop, fun t _ => by
      have hd : HasDerivAt (fun t : ℝ => y₀ + (t - a) • v) v t := by
        simpa using (((hasDerivAt_id t).sub_const a).smul_const v).const_add y₀
      exact hd.hasDerivWithinAt⟩
  have hP : DLRAProblem (fun _ _ => v) (fun t => x₀ + (t - τ 0) • v) (τ 0) (τ N) ρ 0 ‖v‖ :=
    ⟨aff x₀ (τ 0) _, le_rfl, norm_nonneg v, fun t _ x y _ _ => by simp, fun t _ x _ => le_rfl⟩
  -- the error bound of the theorem, with the telescoping sum evaluated
  have hsum : ∀ n : ℕ, Real.exp (0 * (τ n - τ 0)) * ‖Y₀ - (x₀ + (τ 0 - τ 0) • v)‖ +
      ∑ k ∈ range n, Real.exp (0 * (τ n - τ (k + 1))) * (θ * (τ (k + 1) - τ k)) =
      ‖Y₀ - x₀‖ + θ * (τ n - τ 0) := fun n => by
    have h1 : ∑ k ∈ range n, Real.exp (0 * (τ n - τ (k + 1))) * (θ * (τ (k + 1) - τ k)) =
        θ * ∑ k ∈ range n, (τ (k + 1) - τ k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [zero_mul, Real.exp_zero, one_mul]
    rw [h1, Finset.sum_range_sub, zero_mul, Real.exp_zero, one_mul, sub_self, zero_smul,
      add_zero]
  obtain ⟨Y, hY0, hY, hbd⟩ :=
    (isTubeLocal_inexactEuler_aux (E := E) hθ zero_le_two).exists_run_norm_sub_le_of_isGrid
      le_rfl hτ hP continuousOn_const (R := fun _ => ‖Y₀ - x₀‖ + θ * (τ N - τ 0))
      (δ := fun n => θ * (τ (n + 1) - τ n))
      (fun n hn Z₀ Z₁ _ _ hstep Φ hΦ hΦ₀ => by
        have hΨ := aff Z₀ (τ n) (τ (n + 1))
        have hd := dist_le_of_trajectories_ODE (v := fun _ _ => v) (K := 0) (δ := 0)
          (fun _ => LipschitzWith.const v) hΨ.cont hΨ.deriv hΦ.cont hΦ.deriv (by simp [hΦ₀])
          (τ (n + 1)) (right_mem_Icc.2 (hτ.mono n hn))
        rw [zero_mul, dist_le_zero] at hd
        rw [← hd]
        exact hstep)
      trivial
      (fun n hn => (hsum n).le.trans (by
        have hle := mul_le_mul_of_nonneg_left
          (sub_le_sub_right (hτ.le_of_le hn.le le_rfl) (τ 0)) hθ
        linarith))
      hsmall
  exact ⟨Y, hY0, hY, fun n hn => (hbd n hn).2.trans (hsum n).le⟩

end Examples

end LeanDLRA
