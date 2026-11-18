import LeanDLRA.Foundations.OneSided

/-!
# A posteriori error bound through a lagged sweep

Let `A' = F(t, A)` with `F = M + N`, `F` one-sided Lipschitz with constant `ℓ` and `N` Lipschitz
with constant `κ`. Let `Y` be any curve (for example the interpolant of the iterates of a
low-rank integrator; no differentiability is needed) and let `Z` solve the equation in which
the part `N` is evaluated along `Y`,

  `Z' = M(t, Z) + N(t, Y t)`.

The defect of `Z` in the full equation is `N(t, Y) - N(t, Z)`, of norm at most `κ ‖Y - Z‖`.
With the stability theorem for one-sided Lipschitz fields this gives a bound for `‖Y - A‖` in
terms of the computable distance `‖Y - Z‖` alone:

  `‖Y t - A t‖ ≤ ‖Y t - Z t‖ + gronwallBound δ ℓ (κ ρ) (t - a)`

for `‖Y - Z‖ ≤ ρ` and `‖Z a - A a‖ ≤ δ`.

The distance `Y - Z` is the residual of `Y` integrated with the flow of `M`, so the bound sees
the norm of the integrated residual and not the integral of its norm, and only the constant `κ`
of the part `N` enters next to `ℓ`. For `M = 0` the curve `Z` is the Picard iterate of `Y`.
The mechanism is that of Picard iteration and waveform relaxation; the residual bound for
a moving reduced space is [BillaudFriessNouy2017, Prop. 1].

## Main results

* `norm_sub_le_gronwallBound_of_sweep`: `‖Z t - A t‖ ≤ gronwallBound δ ℓ (κ ρ) (t - a)`.
* `norm_sub_le_add_gronwallBound_of_sweep`: the bound for `‖Y t - A t‖`.
* `norm_sub_le_add_of_sweep_steps`: the bound on a time grid, with a bound `ρ n` for
  `‖Y - Z‖` on the `n`-th step and the recursion
  `q (n + 1) ≥ gronwallBound (q n) ℓ (κ ρ n) h`: `‖Y tₙ - A tₙ‖ ≤ ‖Y tₙ - Z tₙ‖ + q n`.
-/

open Set

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F M N : ℝ → E → E} {ℓ κ : ℝ} {A Y Z : ℝ → E}

/-- **Error of a lagged sweep.** Let `F = M + N` with `F` one-sided Lipschitz with constant `ℓ`
and `N` Lipschitz with constant `κ`, let `A' = F(t, A)` and `Z' = M(t, Z) + N(t, Y t)` for a
curve `Y` with `‖Y - Z‖ ≤ ρ` on `[a, b)`. Then
`‖Z t - A t‖ ≤ gronwallBound δ ℓ (κ ρ) (t - a)` whenever `‖Z a - A a‖ ≤ δ`. -/
theorem norm_sub_le_gronwallBound_of_sweep (hF : IsOneSidedLipschitzField F ℓ)
    (hN : IsLipschitzField N κ) (hκ : 0 ≤ κ) (hsplit : ∀ t x, F t x = M t x + N t x)
    {a b δ ρ : ℝ} (hA : ODESolution F A a b)
    (hZ : ODESolution (fun t z => M t z + N t (Y t)) Z a b)
    (hρ : ∀ t ∈ Ico a b, ‖Y t - Z t‖ ≤ ρ) (h0 : ‖Z a - A a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Z t - A t‖ ≤ gronwallBound δ ℓ (κ * ρ) (t - a) := by
  have h := norm_sub_le_gronwallBound_of_oneSided hF (ηy := κ * ρ) (ηz := 0) hZ.cont hZ.deriv
    (fun t ht => ?_) hA.cont hA.deriv (fun t _ => by simp) h0
  · simpa using h
  · have h1 : M t (Z t) + N t (Y t) - F t (Z t) = N t (Y t) - N t (Z t) := by
      rw [hsplit]; abel
    rw [h1]
    exact (hN t (Y t) (Z t)).trans (mul_le_mul_of_nonneg_left (hρ t ht) hκ)

/-- **A posteriori bound through a lagged sweep.** In the setting of
`norm_sub_le_gronwallBound_of_sweep`,
`‖Y t - A t‖ ≤ ‖Y t - Z t‖ + gronwallBound δ ℓ (κ ρ) (t - a)`: the error of an arbitrary
curve `Y` is bounded by its distance to the sweep `Z` and the constants `ℓ`, `κ`. -/
theorem norm_sub_le_add_gronwallBound_of_sweep (hF : IsOneSidedLipschitzField F ℓ)
    (hN : IsLipschitzField N κ) (hκ : 0 ≤ κ) (hsplit : ∀ t x, F t x = M t x + N t x)
    {a b δ ρ : ℝ} (hA : ODESolution F A a b)
    (hZ : ODESolution (fun t z => M t z + N t (Y t)) Z a b)
    (hρ : ∀ t ∈ Ico a b, ‖Y t - Z t‖ ≤ ρ) (h0 : ‖Z a - A a‖ ≤ δ) :
    ∀ t ∈ Icc a b,
      ‖Y t - A t‖ ≤ ‖Y t - Z t‖ + gronwallBound δ ℓ (κ * ρ) (t - a) := by
  intro t ht
  have h1 := norm_sub_le_gronwallBound_of_sweep hF hN hκ hsplit hA hZ hρ h0 t ht
  have h2 := norm_sub_le_norm_sub_add_norm_sub (Y t) (Z t) (A t)
  linarith

/-- **A posteriori bound through a lagged sweep, on a time grid.** With the grid
`tₙ = t₀ + n h`, a bound `ρ n` for `‖Y - Z‖` on the `n`-th step and numbers `q n` with
`‖Z t₀ - A t₀‖ ≤ q 0` and `gronwallBound (q n) ℓ (κ ρ n) h ≤ q (n + 1)`,
`‖Y tₙ - A tₙ‖ ≤ ‖Y tₙ - Z tₙ‖ + q n` for all `n ≤ K`. All quantities on the right are
computed from `Y`, `Z` and the constants `ℓ`, `κ`. -/
theorem norm_sub_le_add_of_sweep_steps (hF : IsOneSidedLipschitzField F ℓ)
    (hN : IsLipschitzField N κ) (hκ : 0 ≤ κ) (hsplit : ∀ t x, F t x = M t x + N t x)
    {t₀ h : ℝ} (hh : 0 ≤ h) {K : ℕ} (hA : ODESolution F A t₀ (t₀ + K * h))
    (hZ : ODESolution (fun t z => M t z + N t (Y t)) Z t₀ (t₀ + K * h)) {ρ q : ℕ → ℝ}
    (hρ : ∀ n < K, ∀ t ∈ Ico (t₀ + n * h) (t₀ + (n + 1) * h), ‖Y t - Z t‖ ≤ ρ n)
    (h0 : ‖Z t₀ - A t₀‖ ≤ q 0)
    (hq : ∀ n < K, gronwallBound (q n) ℓ (κ * ρ n) h ≤ q (n + 1)) :
    ∀ n ≤ K, ‖Y (t₀ + n * h) - A (t₀ + n * h)‖ ≤
      ‖Y (t₀ + n * h) - Z (t₀ + n * h)‖ + q n := by
  have key : ∀ n ≤ K, ‖Z (t₀ + n * h) - A (t₀ + n * h)‖ ≤ q n := by
    intro n
    induction n with
    | zero => intro _; simpa using h0
    | succ n ih =>
      intro hn
      have hnK : n < K := hn
      have hn' : (n : ℝ) + 1 ≤ K := by exact_mod_cast hn
      have hnh : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg n) hh
      have hKh : ((n : ℝ) + 1) * h ≤ K * h := mul_le_mul_of_nonneg_right hn' hh
      have hle : t₀ + n * h ≤ t₀ + (n + 1) * h := by nlinarith
      have hAn : ODESolution F A (t₀ + n * h) (t₀ + (n + 1) * h) :=
        hA.mono (by linarith) (by linarith)
      have hZn : ODESolution (fun t z => M t z + N t (Y t)) Z (t₀ + n * h) (t₀ + (n + 1) * h) :=
        hZ.mono (by linarith) (by linarith)
      have h1 := norm_sub_le_gronwallBound_of_sweep hF hN hκ hsplit hAn hZn (hρ n hnK)
        (ih hnK.le) (t₀ + (n + 1) * h) (right_mem_Icc.2 hle)
      have h2 : t₀ + ((n : ℝ) + 1) * h - (t₀ + n * h) = h := by ring
      rw [h2] at h1
      have hcast : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
      rw [hcast]
      exact h1.trans (hq n hnK)
  intro n hn
  have h2 := norm_sub_le_norm_sub_add_norm_sub (Y (t₀ + n * h)) (Z (t₀ + n * h))
    (A (t₀ + n * h))
  linarith [key n hn]

/-- The hypotheses of `norm_sub_le_add_gronwallBound_of_sweep` hold with nonzero constants: for
`x' = x` on `[0, 1]` with `M = 0`, `N = id` (`ℓ = κ = 1`), the constant curve `Y = 1` has the
sweep `Z t = 1 + t`, `‖Y - Z‖ ≤ 1`, and the theorem bounds `|1 - exp t|`. -/
example : ∀ t ∈ Icc (0 : ℝ) 1,
    ‖(1 : ℝ) - Real.exp t‖ ≤
      ‖(1 : ℝ) - (1 + t)‖ + gronwallBound 0 1 (1 * 1) (t - 0) := by
  refine norm_sub_le_add_gronwallBound_of_sweep (F := fun _ x => x) (M := fun _ _ => 0)
    (N := fun _ x => x) (ℓ := 1) (κ := 1) (A := Real.exp) (Y := fun _ => 1)
    (Z := fun t => 1 + t) (fun t x y => ?_) (fun t x y => by simp) zero_le_one
    (fun t x => by simp) ⟨Real.continuous_exp.continuousOn, fun t _ =>
      (Real.hasDerivAt_exp t).hasDerivWithinAt⟩
    ⟨by fun_prop, fun t _ => ?_⟩ (fun t ht => ?_) (by simp)
  · rw [real_inner_self_eq_norm_sq, one_mul]
  · simpa using ((hasDerivAt_id t).const_add (1 : ℝ)).hasDerivWithinAt
  · have h1 : (1 : ℝ) - (1 + t) = -t := by ring
    rw [h1, norm_neg, Real.norm_of_nonneg ht.1]
    exact ht.2.le

end LeanDLRA
