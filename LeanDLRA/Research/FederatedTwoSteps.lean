import LeanDLRA.Training.FederatedDescent

/-!
# FeDLRT with averaged gradients: two local steps are two global gradient steps

One aggregated round of FeDLRT with variance correction (Schotthöfer–Laiu, arXiv 2406.17887,
before truncation) is `fedRound`: `s⋆` local steps of length `λ` on every client, then the
average. In the setting of the paper the global gradient is the average of the client gradients.
This file treats that setting for `s⋆ = 2`.

The first corrected local step is the same for all clients, `z¹ = x - λ Π ∇ℒ(x)`, and the
average of the second corrected steps is `z¹ - λ Π ∇ℒ(z¹)`, because the correction terms
average to zero. So the round is exactly two projected gradient steps for the global loss. It
follows that the round decreases the loss when `λ β < 2`, that is `s⋆ λ β < 4`, for every loss
with `β`-Lipschitz gradient; the client losses need not be convex and their gradients need not
be Lipschitz. For `λ β ≥ 2` there is no descent in general.

## Main results

* `fedRound_two_eq_projGradStep`: if `g` is the average of the `gc c`, then
  `fedRound Π gc g λ 2 x = projGradStep Π g λ (projGradStep Π g λ x)`.
* `loss_fedRound_two_le`: `ℒ(x⋆) ≤ ℒ(x) - λ (1 - β λ / 2) (‖Π ∇ℒ(x)‖² + ‖Π ∇ℒ(z¹)‖²)`.
* `loss_fedRound_two_lt`: `ℒ(x⋆) < ℒ(x)` for `0 < λ`, `λ β < 2` and `Π ∇ℒ(x) ≠ 0`.
* `loss_le_loss_fedRound_two_quadratic`: for identical clients with the loss
  `⟪v, y⟫ + ‖y‖² / 2` (`β = 1`) and `λ ≥ 2` the round from `0` does not decrease the loss.

## Remarks on the hypotheses

* The statements are for `s⋆ = 2` only. For `s⋆ ≥ 3` the second iterates of the clients differ
  and the round is not a sequence of gradient steps of the global loss.
* Without the hypothesis that the global gradient is the average of the client gradients the
  condition for convex clients is `s⋆ λ β < 2`: a constant-gradient client gives no descent
  for `s⋆ λ β ≥ 2`.
* The example without descent is the classical one for gradient descent with step `2 / β`.
-/

open Set Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section FederatedTwoSteps

variable {ι : Type*} {ℒ : E → ℝ} {g : E → E} {gc : ι → E → E} {β lr : ℝ}
  {P : E →L[ℝ] E}

/-- **Two local steps with averaged gradients.** If the global gradient is the average of the
client gradients, the FeDLRT round with `s⋆ = 2` is two projected gradient steps of the global
loss: `x⋆ = z¹ - λ Π ∇ℒ(z¹)` with `z¹ = x - λ Π ∇ℒ(x)`. -/
theorem fedRound_two_eq_projGradStep [Fintype ι] [Nonempty ι] (P : E →L[ℝ] E)
    (hmean : ∀ y, g y = (Fintype.card ι : ℝ)⁻¹ • ∑ c, gc c y) (lr : ℝ) (x : E) :
    fedRound P gc g lr 2 x = projGradStep P g lr (projGradStep P g lr x) := by
  have hC : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  obtain ⟨z, hz⟩ : ∃ z : E, z = projGradStep P g lr x := ⟨_, rfl⟩
  have h1 : ∀ c, fedClientIter P gc g lr x c 2 = z - lr • P (gc c z - gc c x + g x) := by
    intro c
    have e1 : fedClientIter P gc g lr x c 1 = z := by
      rw [fedClientIter_succ, hz, projGradStep]
      simp [fedClientIter]
    rw [fedClientIter_succ, e1]
  have h2 : (Fintype.card ι : ℝ)⁻¹ • ∑ c, (gc c z - gc c x + g x) = g z := by
    rw [sum_add_distrib, sum_sub_distrib, sum_const, card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_add, smul_sub, smul_smul, inv_mul_cancel₀ hC, one_smul, ← hmean, ← hmean]
    abel
  have h3 : (Fintype.card ι : ℝ)⁻¹ • ∑ c, lr • P (gc c z - gc c x + g x)
      = lr • P ((Fintype.card ι : ℝ)⁻¹ • ∑ c, (gc c z - gc c x + g x)) := by
    rw [← smul_sum, ← map_sum, smul_comm, map_smul]
  rw [fedRound, ← hz]
  simp_rw [h1]
  rw [sum_sub_distrib, sum_const, card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul,
    inv_mul_cancel₀ hC, one_smul, h3, h2, projGradStep]

/-- **Loss descent of the FeDLRT round with two local steps and averaged gradients.** If the
global loss has a `β`-Lipschitz gradient that is the average of the client gradients, then for
every step size `λ`
`ℒ(x⋆) ≤ ℒ(x) - λ (1 - β λ / 2) (‖Π ∇ℒ(x)‖² + ‖Π ∇ℒ(z¹)‖²)`, `z¹ = x - λ Π ∇ℒ(x)`.
No assumption on the client losses is needed. -/
theorem loss_fedRound_two_le [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hP : IsOrthProj P)
    (hmean : ∀ y, g y = (Fintype.card ι : ℝ)⁻¹ • ∑ c, gc c y) (lr : ℝ) (x : E) :
    ℒ (fedRound P gc g lr 2 x) ≤ ℒ x - lr * (1 - β * lr / 2) *
      (‖P (g x)‖ ^ 2 + ‖P (g (projGradStep P g lr x))‖ ^ 2) := by
  rw [fedRound_two_eq_projGradStep P hmean]
  have h1 := loss_projGradStep_le hℒ hg hP lr x
  have h2 := loss_projGradStep_le hℒ hg hP lr (projGradStep P g lr x)
  linarith

/-- **The FeDLRT round with two local steps and averaged gradients decreases the loss when
`λ β < 2`**, that is `s⋆ λ β < 4`, and the projected gradient does not vanish. -/
theorem loss_fedRound_two_lt [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hP : IsOrthProj P)
    (hmean : ∀ y, g y = (Fintype.card ι : ℝ)⁻¹ • ∑ c, gc c y) (hlr : 0 < lr)
    (hlrβ : lr * β < 2) {x : E} (hx : P (g x) ≠ 0) :
    ℒ (fedRound P gc g lr 2 x) < ℒ x := by
  have h := loss_fedRound_two_le (gc := gc) hℒ hg hP hmean lr x
  have hc : 0 < lr * (1 - β * lr / 2) := mul_pos hlr (by nlinarith)
  have h1 : 0 < ‖P (g x)‖ ^ 2 := pow_pos (norm_pos_iff.2 hx) 2
  have h2 := sq_nonneg ‖P (g (projGradStep P g lr x))‖
  nlinarith [mul_pos hc h1, mul_nonneg hc.le h2]

/-- **No descent for `λ β ≥ 2`.** For identical clients with the loss
`ℒ(y) = ⟪v, y⟫ + ‖y‖² / 2` (gradient `y ↦ v + y`, `β = 1`, `Π = 1`) and `λ ≥ 2`, the FeDLRT
round with two local steps started at `0` does not decrease the loss. The global gradient is the
average of the client gradients. -/
theorem loss_le_loss_fedRound_two_quadratic [Fintype ι] [Nonempty ι] (v : E) {lr : ℝ}
    (h2 : 2 ≤ lr) :
    ⟪v, (0 : E)⟫ + ‖(0 : E)‖ ^ 2 / 2 ≤
      ⟪v, fedRound (1 : E →L[ℝ] E) (fun _ : ι => fun z => v + z) (fun y => v + y) lr 2 0⟫
        + ‖fedRound (1 : E →L[ℝ] E) (fun _ : ι => fun z => v + z) (fun y => v + y) lr 2 0‖ ^ 2
          / 2 := by
  have hC : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hmean : ∀ y : E, (fun y => v + y) y
      = (Fintype.card ι : ℝ)⁻¹ • ∑ c : ι, (fun _ : ι => fun z => v + z) c y := by
    intro y
    rw [sum_const, card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hC,
      one_smul]
  have e : fedRound (1 : E →L[ℝ] E) (fun _ : ι => fun z => v + z) (fun y => v + y) lr 2 0
      = -((lr * (2 - lr)) • v) := by
    rw [fedRound_two_eq_projGradStep _ hmean]
    simp only [projGradStep, one_apply_eq_self, add_zero, zero_sub]
    module
  have hm : lr * (2 - lr) ≤ 0 := by nlinarith
  rw [e, inner_zero_right, norm_zero, inner_neg_right, norm_neg, norm_smul,
    real_inner_smul_right, real_inner_self_eq_norm_sq, mul_pow, Real.norm_eq_abs, sq_abs]
  nlinarith [mul_nonneg (neg_nonneg.2 hm) (sq_nonneg ‖v‖),
    mul_nonneg (sq_nonneg (lr * (2 - lr))) (sq_nonneg ‖v‖)]

/-- Non-vacuity of `loss_fedRound_two_lt`: two clients with the losses `⟪v, y⟫` and
`⟪v, y⟫ + ‖y‖²` (Hessians `0` and `2`, mean `1`), the global loss `⟪v, y⟫ + ‖y‖² / 2`, `β = 1`
and `λ = 3/2`, so `s⋆ λ β = 3`; the round from `0` decreases the loss if `v ≠ 0`. -/
example {v : E} (hv : v ≠ 0) :
    ⟪v, fedRound (1 : E →L[ℝ] E)
        (fun c : Fin 2 => fun z => v + (if c = 0 then (0 : ℝ) else 2) • z) (fun y => v + y)
        (3 / 2) 2 0⟫
      + ‖fedRound (1 : E →L[ℝ] E)
        (fun c : Fin 2 => fun z => v + (if c = 0 then (0 : ℝ) else 2) • z) (fun y => v + y)
        (3 / 2) 2 0‖ ^ 2 / 2 < ⟪v, (0 : E)⟫ + ‖(0 : E)‖ ^ 2 / 2 := by
  refine loss_fedRound_two_lt (ℒ := fun y : E => ⟪v, y⟫ + ‖y‖ ^ 2 / 2) (β := 1)
    (fun x => hasFDerivAt_inner_add_half_norm_sq v x) (fun x y => ?_) IsOrthProj.one
    (fun y => ?_) (by norm_num) (by norm_num) (x := 0) ?_
  · rw [add_sub_add_left_eq_sub, one_mul]
  · rw [Fin.sum_univ_two]
    simp only [Fintype.card_fin, Fin.isValue, ↓reduceIte, one_ne_zero, zero_smul, add_zero]
    module
  · simpa using hv

end FederatedTwoSteps

end LeanDLRA
