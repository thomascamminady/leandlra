import LeanDLRA.Training.Descent
import LeanDLRA.Matrix.Projectors

/-!
# Fixed points of federated low-rank training with and without variance correction

Two statements on the federated rounds `fedRound` (with variance correction) and `fedAvgRound`
(without) of `LeanDLRA/Training/Defs.lean`. A fixed point of the corrected round is a stationary
point of the projected gradient; the round without the correction can have a fixed point where
the sum of the client gradients does not vanish (client drift).

## Main results

* `apply_grad_eq_zero_of_fedRound_eq_self`: if the client gradients are `β`-Lipschitz,
  `e λ β s⋆ < 1` and `s⋆ > 0`, then `fedRound x = x` implies `Π g(x) = 0` for the correction
  field `g` of the round.
* `exists_fedAvgRound_fixed_ne_stationary`: for every number `s⋆ ≥ 2` of local steps there are
  two quadratic clients on `ℝ` for which `fedAvgRound` has a fixed point `x` with
  `∑ c, gc c x ≠ 0`.

## References

* arXiv 2406.17887 (FeDLRT), Sec. 3.2: variance correction.
-/

open Set Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section PL

variable {ℒ : E → ℝ} {g : E → E} {β : ℝ}

end PL

section Refresh

variable {ℒ : E → ℝ} {g : E → E} {β : ℝ}

end Refresh

section RefreshMatrix

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n]

end RefreshMatrix

section Precond

variable {ℒ : E → ℝ} {g : E → E} {β : ℝ}

end Precond

section Federated

variable {ι : Type*} {ℒ : E → ℝ} {g : E → E} {β lr : ℝ} {P : E →L[ℝ] E} {gc : ι → E → E}

/-- **Fixed points of the variance-corrected FeDLRT round are stationary** (source:
arXiv 2406.17887 §3.2; OP-TR-11, positive half). If `e λ β s⋆ < 1` and `s⋆ > 0`, a fixed point
`fedRound x = x` satisfies `Π ∇ℒ(x) = 0`. -/
theorem apply_grad_eq_zero_of_fedRound_eq_self [Fintype ι] [Nonempty ι] (hP : IsOrthProj P)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hlr : 0 < lr)
    {sstar : ℕ} (hs0 : 0 < sstar) (hs : Real.exp 1 * (lr * β * sstar) < 1) {x : E}
    (hfix : fedRound P gc g lr sstar x = x) : P (g x) = 0 := by
  have he : (1 : ℝ) ≤ Real.exp 1 := by simp
  have hb : 0 ≤ lr * β * sstar := by positivity
  have hs1 : lr * β * sstar ≤ 1 := by nlinarith
  have hw := norm_fedDrift_le (g := g) hP hgc hβ hlr.le hs1 x
  rw [fedRound_eq] at hfix
  have h1 : lr • (((sstar : ℝ)) • P (g x) + P (fedDrift P gc g lr sstar x)) = 0 := by
    have : x - ((sstar : ℝ) * lr) • P (g x) - lr • P (fedDrift P gc g lr sstar x) - x = 0 := by
      rw [hfix]; simp
    rw [show lr • (((sstar : ℝ)) • P (g x) + P (fedDrift P gc g lr sstar x)) =
      -(x - ((sstar : ℝ) * lr) • P (g x) - lr • P (fedDrift P gc g lr sstar x) - x) by module,
      this, neg_zero]
  have h2 : ((sstar : ℝ)) • P (g x) = -P (fedDrift P gc g lr sstar x) := by
    rcases smul_eq_zero.1 h1 with h | h
    · exact absurd h hlr.ne'
    · exact eq_neg_of_add_eq_zero_left h
  have h3 : (sstar : ℝ) * ‖P (g x)‖ ≤ sstar * (β * (Real.exp 1 * (sstar * lr) * ‖P (g x)‖)) := by
    have : (sstar : ℝ) * ‖P (g x)‖ = ‖P (fedDrift P gc g lr sstar x)‖ := by
      have := congrArg norm h2
      rwa [norm_smul, Real.norm_natCast, norm_neg] at this
    rw [this]
    exact (hP.norm_le _).trans hw
  have hsp : (0 : ℝ) < sstar := by exact_mod_cast hs0
  have h4 : ‖P (g x)‖ * (1 - Real.exp 1 * (lr * β * sstar)) ≤ 0 := by
    have := (mul_le_mul_iff_of_pos_left hsp).1
      (show (sstar : ℝ) * ‖P (g x)‖ ≤ sstar * (β * (Real.exp 1 * (sstar * lr) * ‖P (g x)‖)) from h3)
    nlinarith
  have h5 : ‖P (g x)‖ ≤ 0 := by
    by_contra hc
    replace hc := not_le.1 hc
    nlinarith
  exact norm_le_zero_iff.1 h5

end Federated

private theorem fedAvgClientIter_affine (a b lr x : ℝ) (c : Fin 2) (gc : Fin 2 → ℝ → ℝ)
    (hgc : ∀ y, gc c y = a * (y - b)) (s : ℕ) :
    fedAvgClientIter (1 : ℝ →L[ℝ] ℝ) gc lr x c s = b + (1 - lr * a) ^ s * (x - b) := by
  induction s with
  | zero => simp [fedAvgClientIter]
  | succ s ih =>
    rw [fedAvgClientIter, ih, hgc]
    simp only [one_apply_eq_self, smul_eq_mul, pow_succ]
    ring

private theorem three_pow_lt_aux (s : ℕ) (hs : 2 ≤ s) :
    3 * (7 / 8 : ℝ) ^ s - (5 / 8 : ℝ) ^ s < 2 := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    have hB : (5 / 8 : ℝ) ^ s ≤ 5 / 8 := by
      calc (5 / 8 : ℝ) ^ s ≤ (5 / 8 : ℝ) ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 5 / 8 := by norm_num
    rw [pow_succ, pow_succ]
    nlinarith

/-- **Client drift biases uncorrected federated training** (source: arXiv 2406.17887,
numerical evidence; OP-TR-11, negative half). For every number `s⋆ ≥ 2` of local steps there are
two quadratic clients on `ℝ` (e.g. `ℒ₀ = y²/2`, `ℒ₁ = 3(y - 1)²/2`, `λ = 1/8`) such that the
uncorrected round has a fixed point at which the global gradient does not vanish. -/
theorem exists_fedAvgRound_fixed_ne_stationary {sstar : ℕ} (hs : 2 ≤ sstar) :
    ∃ (gc : Fin 2 → ℝ → ℝ) (lr β x : ℝ), 0 < lr ∧ lr * β < 1 ∧
      (∀ c y z, ‖gc c y - gc c z‖ ≤ β * ‖y - z‖) ∧
      fedAvgRound (1 : ℝ →L[ℝ] ℝ) gc lr sstar x = x ∧ ∑ c, gc c x ≠ 0 := by
  set A : ℝ := (7 / 8 : ℝ) ^ sstar with hA
  set B : ℝ := (5 / 8 : ℝ) ^ sstar with hB
  have hA1 : A < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hB1 : B < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hlt : 3 * A - B < 2 := three_pow_lt_aux sstar hs
  let gc : Fin 2 → ℝ → ℝ := ![fun y => y, fun y => 3 * (y - 1)]
  have h0 : ∀ y, gc 0 y = 1 * (y - 0) := by intro y; simp [gc]
  have h1 : ∀ y, gc 1 y = 3 * (y - 1) := by intro y; simp [gc]
  have hden : 2 - A - B ≠ 0 := by linarith
  refine ⟨gc, 1 / 8, 3, (1 - B) / (2 - A - B), by norm_num, by norm_num, ?_, ?_, ?_⟩
  · intro c y z
    fin_cases c
    · simp only [gc]
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      simp
      nlinarith [abs_nonneg (y - z)]
    · simp only [gc]
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      simp [← mul_sub, abs_mul]
  · rw [fedAvgRound, Fin.sum_univ_two,
      fedAvgClientIter_affine 1 0 (1 / 8) _ 0 gc h0,
      fedAvgClientIter_affine 3 1 (1 / 8) _ 1 gc h1]
    simp only [Fintype.card_fin, smul_eq_mul]
    norm_num
    rw [← hA, ← hB]
    field_simp
    ring
  · rw [Fin.sum_univ_two, h0, h1]
    intro h
    have : (1 - B) / (2 - A - B) = 3 / 4 := by
      field_simp
      field_simp at h
      linarith
    rw [div_eq_iff hden] at this
    linarith

end LeanDLRA
