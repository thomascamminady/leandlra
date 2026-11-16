import LeanDLRA.Research.StiffGlobalCycle

/-!
# The global error of the rank-adaptive BUG integrator grows with the variation of the forcing

`StiffGlobalCycle` applies the rank-adaptive BUG integrator with step size `h` to
`Y' = Y N + G(t)`, `N = -diag(0, λ)`, with a forcing that is piecewise constant with period
`3 h` (`cycleForcing`), and shows that the error after `J` cycles is at least `J h / 2` when
`λ s² h ≥ 2`. This file measures that error against the variation of the forcing in time: the
three jumps of one cycle have norms that add up to at most `6`, whatever the stiffness `λ` and
the step size are. Hence the error after `J` cycles is at least `h / 12` times the variation
of the forcing over these cycles.

So a global error bound for this integrator that is uniform in the stiffness and contains the
variation `Var G` of the forcing in time must contain it at least in the form `h · Var G`, with
a factor at least `1 / 12`; a bound of the form `C h (1 + Var G)^γ` with `γ < 1` is excluded by
the family. The family runs `J` cycles for any `J` with `3 J h ≤ T`, so every value of the
variation up to `2 T / h` occurs.

## Main results

* `norm_sq_forcing_sub`: `‖forcing … p q - forcing … p' q'‖² = (p - p')² + (q - q')²`.
* `variation_cycleForcing_le`: the three jumps of one cycle add up to at most `6`.
* `variation_mul_le_norm_sub_exactState`:
  `(h / 12) · (J · V) ≤ ‖state … 0 0 - exactState … J‖` for `λ s² h ≥ 2`, where `V` is the sum
  of the norms of the three jumps of one cycle.

## Remarks

* Whether the bound `C (h (1 + Var G) + ε + n ϑ)` holds uniformly in the stiffness is not
  decided here; this file shows that the term `h · Var G` cannot be weakened.
* The numerical state after `J` cycles is the start `state c s σ 0 0` by `exists_cycle`, as in
  `half_le_norm_sub_exactState`.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace StiffGlobalCycle

variable {c s lam σ h : ℝ}

/-- The difference of two forcings of the family lives in the lower row. -/
theorem norm_sq_forcing_sub (s lam σ p q p' q' : ℝ) :
    ‖forcing s lam σ p q - forcing s lam σ p' q'‖ ^ 2 = (p - p') ^ 2 + (q - q') ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  simp only [forcing, Matrix.sub_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- A norm whose square is at most four is at most two. -/
private lemma norm_le_two_of_sq_le {X : Matrix (Fin 2) (Fin 2) ℝ} (hX : ‖X‖ ^ 2 ≤ 4) :
    ‖X‖ ≤ 2 :=
  not_lt.1 fun hc : 2 < ‖X‖ => by nlinarith [norm_nonneg X]

/-- **The variation of the forcing over one cycle is at most six**, for every stiffness and
every step size: the jumps from the active to the free step, from the free to the return step
and from the return step to the next active step. -/
theorem variation_cycleForcing_le (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0)
    (hh : 0 < h) :
    ‖cycleForcing c s lam σ h 1 - cycleForcing c s lam σ h 0‖ +
      ‖cycleForcing c s lam σ h 2 - cycleForcing c s lam σ h 1‖ +
        ‖cycleForcing c s lam σ h 0 - cycleForcing c s lam σ h 2‖ ≤ 6 := by
  have e0 : cycleForcing c s lam σ h 0 = forcing s lam σ 1 0 := by simp [cycleForcing]
  have e1 : cycleForcing c s lam σ h 1 = forcing s lam σ 0 (kill c s lam h) := by
    simp [cycleForcing]
  have e2 : cycleForcing c s lam σ h 2 = forcing s lam σ (-(gain c s lam h * c / h)) 0 := by
    simp [cycleForcing]
  have hk := abs_kill_le hcs hl hs hh
  have hg := abs_le.1 (abs_gain_mul_div_le hcs hl hs hh)
  have hs1 : s ^ 2 ≤ 1 := by nlinarith [sq_nonneg c]
  have hk2 : kill c s lam h ^ 2 ≤ 1 := by
    have h1 : kill c s lam h ^ 2 ≤ s ^ 2 := by
      rw [← sq_abs (kill c s lam h), ← sq_abs s]
      exact pow_le_pow_left₀ (abs_nonneg _) hk 2
    linarith
  have h1 : ‖forcing s lam σ 0 (kill c s lam h) - forcing s lam σ 1 0‖ ≤ 2 := by
    refine norm_le_two_of_sq_le ?_
    rw [norm_sq_forcing_sub]
    nlinarith
  have h2 : ‖forcing s lam σ (-(gain c s lam h * c / h)) 0 -
      forcing s lam σ 0 (kill c s lam h)‖ ≤ 2 := by
    refine norm_le_two_of_sq_le ?_
    rw [norm_sq_forcing_sub]
    nlinarith [hg.1, hg.2]
  have h3 : ‖forcing s lam σ 1 0 - forcing s lam σ (-(gain c s lam h * c / h)) 0‖ ≤ 2 := by
    refine norm_le_two_of_sq_le ?_
    rw [norm_sq_forcing_sub]
    nlinarith [hg.1, hg.2]
  rw [e0, e1, e2]
  linarith

/-- **The error is at least `h / 12` times the variation of the forcing.** For `λ s² h ≥ 2` the
distance between the numerical state after `J` cycles (the start, by `exists_cycle`) and the
exact solution is at least `(h / 12) · J · V`, where `V` is the variation of the forcing over
one cycle. The constant does not depend on the stiffness `λ`. -/
theorem variation_mul_le_norm_sub_exactState (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam)
    (hs : s ≠ 0) (hh : 0 < h) (hx : 2 ≤ lam * s ^ 2 * h) (J : ℕ) :
    h / 12 * (J * (‖cycleForcing c s lam σ h 1 - cycleForcing c s lam σ h 0‖ +
      ‖cycleForcing c s lam σ h 2 - cycleForcing c s lam σ h 1‖ +
        ‖cycleForcing c s lam σ h 0 - cycleForcing c s lam σ h 2‖)) ≤
      ‖state c s σ 0 0 - exactState c s lam σ h J‖ := by
  have h1 := half_le_norm_sub_exactState (σ := σ) hcs hl hs hx J
  have h2 := variation_cycleForcing_le (σ := σ) hcs hl hs hh
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have h3 := mul_le_mul_of_nonneg_left h2 hJ
  have h4 := mul_le_mul_of_nonneg_left h3 (div_nonneg hh.le (by norm_num : (0 : ℝ) ≤ 12))
  have h5 : h / 12 * ((J : ℝ) * 6) = J * h / 2 := by ring
  linarith

/-- The hypotheses hold with `c = 3/5`, `s = 4/5`, `λ = 25`, `h = 1/8` (`λ s² h = 2`): after
eight cycles (time `3`) the error is at least `1/96` times the variation of the forcing. -/
example (σ : ℝ) :
    (1 / 8 : ℝ) / 12 * ((8 : ℕ) * (‖cycleForcing (3 / 5) (4 / 5) 25 σ (1 / 8) 1 -
      cycleForcing (3 / 5) (4 / 5) 25 σ (1 / 8) 0‖ +
        ‖cycleForcing (3 / 5) (4 / 5) 25 σ (1 / 8) 2 -
          cycleForcing (3 / 5) (4 / 5) 25 σ (1 / 8) 1‖ +
          ‖cycleForcing (3 / 5) (4 / 5) 25 σ (1 / 8) 0 -
            cycleForcing (3 / 5) (4 / 5) 25 σ (1 / 8) 2‖)) ≤
      ‖state (3 / 5) (4 / 5) σ 0 0 - exactState (3 / 5) (4 / 5) 25 σ (1 / 8) 8‖ :=
  variation_mul_le_norm_sub_exactState (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 8

end StiffGlobalCycle

end LeanDLRA
