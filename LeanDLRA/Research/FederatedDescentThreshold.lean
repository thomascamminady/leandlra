import LeanDLRA.Training.FederatedDescent

/-!
# The descent threshold of the FeDLRT round

One aggregated round of FeDLRT with variance correction (Schotthöfer–Laiu, arXiv 2406.17887,
Thm 2 and Thm 8, before truncation) is `fedRound`: `s⋆` local steps of length `λ` on every
client, then the average. `loss_fedRound_le_one` proves a loss descent for `s⋆ λ β ≤ 1`, and
`exists_fedRound_no_descent` shows that there is none in general when `(1 + λ β)^{s⋆} ≥ 3`.
This file closes the gap between the two statements and treats convex clients.

## Notation

`A = s⋆ λ`, `θ = β A`, `a = ‖Π ∇ℒ(x)‖`, `q = (1 + λ β)^{s⋆}`,
`T = λ ∑_{i<s⋆} (1 + λ β)^i` (so `β T = q - 1`) and `R = λ ∑_{j<s⋆} ((1 + λ β)^j - 1) = T - A`.

## Main results

Hypotheses of `loss_fedRound_le` (the global gradient and the client gradients are independent
data with the Lipschitz constant `β`), without a restriction on the step size:

* `loss_fedRound_le_geom`: `ℒ(x⋆) ≤ ℒ(x) - (A - β A²/2 - |β A - 1| R - β R²/2) a²`.
* `loss_fedRound_le_of_one_le`: for `θ ≥ 1` this is `ℒ(x⋆) ≤ ℒ(x) - T (3 - q)/2 · a²`.
* `loss_fedRound_le_of_pow_le_three`, `loss_fedRound_lt_of_pow_lt_three`: the loss does not
  increase when `q ≤ 3`, and it decreases when `q < 3` and `Π ∇ℒ(x) ≠ 0`.
* `loss_fedRound_neg_eq`: for a client with the gradient `z ↦ -z` and the loss
  `⟪v, y⟫ + ‖y‖²/2` the bound of `loss_fedRound_le_of_one_le` is an equality, for every step
  size and every number of local steps. `loss_lt_loss_fedRound_neg`, `exists_fedRound_ascent`:
  the loss increases when `q > 3`. So `q ≤ 3` is the exact condition under which the round
  cannot increase the loss in this generality.

Convex clients (client losses that satisfy the gradient inequality
`ℒ_c(x) + ⟪∇ℒ_c(x), y - x⟫ ≤ ℒ_c(y)`), global gradient still independent of the client gradients:

* `inner_fedClientIter_sub_le`: the local steps are gradient steps for a convex function whose
  gradient at `x` is `∇ℒ(x)`, so `⟪∇ℒ(x), z^s - x⟫ ≤ -λ (1 - λ β/2) ∑_{j<s} ‖Π G_j‖²` with the
  projected local gradients `Π G_j`, while `‖z^s - x‖² ≤ λ² s ∑_{j<s} ‖Π G_j‖²`
  (`norm_sq_fedClientIter_sub_le`).
* `loss_fedRound_le_of_convex`, `loss_fedRound_lt_of_convex`:
  `ℒ(x⋆) ≤ ℒ(x) - (λ/2) (2 - (s⋆ + 1) λ β) a²` for `(s⋆ + 1) λ β ≤ 2`.
* `loss_le_loss_fedRound_zero`: a client with vanishing gradient and the loss `‖y‖²/2` show
  that there is no descent for `s⋆ λ β ≥ 2`.

Global gradient equal to the average of the client gradients (the setting of the paper):

* `loss_le_loss_fedRound_linear`, with `fedRound_linear` and `inv_card_smul_sum_linear`: for
  clients with the gradients `z ↦ h_c z + v` the round is a step of length `m`, the mean of
  `λ ∑_{i<s⋆} (1 - λ h_c)^i`, and the loss does not decrease when `(mean h) m ≥ 2`. The two
  examples after it: Hessians `-1, 1, 1, 1` at `s⋆ λ β = 3`, and the convex pair `0, 1` at
  `s⋆ λ β = 15/2`.

## Remarks on the hypotheses

* The statements are about one round before truncation, with exact client gradients.
* The global gradient need not be the average of the client gradients. The equality case of
  the first group uses this freedom: there the client is concave and the global loss convex.
* For convex clients the range `2 - λ β ≤ s⋆ λ β < 2` is not decided, and the amount of descent
  that is proved is proportional to `λ`, not to `s⋆ λ`.
-/

open Set Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section FederatedThreshold

variable {ι : Type*} {ℒ : E → ℝ} {g : E → E} {gc : ι → E → E} {β lr : ℝ}
  {P : E →L[ℝ] E}

/-! ### The descent lemma along one round -/

/-- The descent lemma for one FeDLRT round, with the exact square of the displacement
`x⋆ - x = -(s⋆ λ Π ∇ℒ(x) + λ Π w)`, where `w = fedDrift` is the averaged drift. -/
lemma loss_fedRound_le_expansion [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hP : IsOrthProj P) (hlr : 0 ≤ lr) (sstar : ℕ)
    (x : E) :
    ℒ (fedRound P gc g lr sstar x) ≤ ℒ x
        - (sstar * lr * ‖P (g x)‖ ^ 2 + lr * ⟪g x, P (fedDrift P gc g lr sstar x)⟫)
        + β / 2 * ‖fedRound P gc g lr sstar x - x‖ ^ 2 ∧
      ‖fedRound P gc g lr sstar x - x‖ ^ 2 = (sstar * lr * ‖P (g x)‖) ^ 2
        + 2 * (sstar * lr * (lr * ⟪g x, P (fedDrift P gc g lr sstar x)⟫))
        + (lr * ‖P (fedDrift P gc g lr sstar x)‖) ^ 2 := by
  have hA0 : 0 ≤ (sstar : ℝ) * lr := mul_nonneg (Nat.cast_nonneg _) hlr
  have hdx : fedRound P gc g lr sstar x - x =
      -(((sstar : ℝ) * lr) • P (g x) + lr • P (fedDrift P gc g lr sstar x)) := by
    rw [fedRound_eq]; abel
  have h1 : ⟪g x, P (g x)⟫ = ‖P (g x)‖ ^ 2 := by rw [real_inner_comm, hP.inner_self_apply]
  have h2 : ⟪P (g x), P (fedDrift P gc g lr sstar x)⟫ =
      ⟪g x, P (fedDrift P gc g lr sstar x)⟫ := by rw [hP.inner_comp, hP.symm]
  constructor
  · have hd := descent_lemma hℒ hg x (fedRound P gc g lr sstar x)
    have hi : ⟪g x, fedRound P gc g lr sstar x - x⟫ =
        -(sstar * lr * ‖P (g x)‖ ^ 2 + lr * ⟪g x, P (fedDrift P gc g lr sstar x)⟫) := by
      rw [hdx, inner_neg_right, inner_add_right, inner_smul_right, inner_smul_right, h1]
    rw [hi] at hd
    linarith
  · rw [hdx, norm_neg, norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
      real_inner_smul_right, Real.norm_of_nonneg hA0, Real.norm_of_nonneg hlr, h2]

/-- The cross term of the round: `|λ ⟪∇ℒ(x), Π w⟫| ≤ ‖Π ∇ℒ(x)‖ (λ ‖w‖)`. -/
lemma abs_lr_inner_proj_le (hP : IsOrthProj P) (hlr : 0 ≤ lr) (u w : E) :
    |lr * ⟪u, P w⟫| ≤ ‖P u‖ * (lr * ‖w‖) := by
  rw [abs_mul, abs_of_nonneg hlr, ← hP.symm]
  calc lr * |⟪P u, w⟫| ≤ lr * (‖P u‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm (P u) w) hlr
    _ = ‖P u‖ * (lr * ‖w‖) := by ring

/-! ### The general class: a bound without a restriction on the step size -/

/-- The scalar inequality behind `loss_fedRound_le_geom`. Here `m` stands for
`λ ⟪∇ℒ(x), Π w⟫`, `n` for `λ ‖Π w‖` and `r` for `λ ‖w‖`. -/
lemma fed_geom_scalar {β A a R r m n : ℝ} (hβ : 0 ≤ β) (ha : 0 ≤ a) (hm : |m| ≤ a * r)
    (hn0 : 0 ≤ n) (hn : n ≤ r) (hr : r ≤ R * a) :
    -(A * a ^ 2 + m) + β / 2 * ((A * a) ^ 2 + 2 * (A * m) + n ^ 2) ≤
      -((A - β / 2 * A ^ 2 - |β * A - 1| * R - β / 2 * R ^ 2) * a ^ 2) := by
  have h1 : (β * A - 1) * m ≤ |β * A - 1| * (R * a ^ 2) :=
    calc (β * A - 1) * m ≤ |(β * A - 1) * m| := le_abs_self _
      _ = |β * A - 1| * |m| := abs_mul _ _
      _ ≤ |β * A - 1| * (a * (R * a)) :=
          mul_le_mul_of_nonneg_left (hm.trans (mul_le_mul_of_nonneg_left hr ha)) (abs_nonneg _)
      _ = |β * A - 1| * (R * a ^ 2) := by ring
  have h2 : n ^ 2 ≤ (R * a) ^ 2 := pow_le_pow_left₀ hn0 (hn.trans hr) 2
  have h3 := mul_le_mul_of_nonneg_left h2 (div_nonneg hβ zero_le_two)
  linarith

/-- **Loss change of the aggregated FeDLRT round without a restriction on the step size**
(hypotheses of `loss_fedRound_le`): with `A = s⋆ λ`, `a = ‖Π ∇ℒ(x)‖` and
`R = λ ∑_{j<s⋆} ((1 + λ β)^j - 1)`,
`ℒ(x⋆) ≤ ℒ(x) - (A - β A²/2 - |β A - 1| R - β R²/2) a²`. -/
theorem loss_fedRound_le_geom [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) (sstar : ℕ) (x : E) :
    ℒ (fedRound P gc g lr sstar x) ≤ ℒ x - (sstar * lr - β / 2 * (sstar * lr) ^ 2
      - |β * (sstar * lr) - 1| * (lr * ∑ j ∈ range sstar, ((1 + lr * β) ^ j - 1))
      - β / 2 * (lr * ∑ j ∈ range sstar, ((1 + lr * β) ^ j - 1)) ^ 2) * ‖P (g x)‖ ^ 2 := by
  obtain ⟨hd, hsq⟩ := loss_fedRound_le_expansion (gc := gc) hℒ hg hP hlr sstar x
  have hw : lr * ‖fedDrift P gc g lr sstar x‖ ≤
      lr * (∑ j ∈ range sstar, ((1 + lr * β) ^ j - 1)) * ‖P (g x)‖ := by
    have h := mul_le_mul_of_nonneg_left
      (norm_fedDrift_le_geom (g := g) hP hgc hβ hlr sstar x) hlr
    exact h.trans (le_of_eq (by ring))
  have hn : lr * ‖P (fedDrift P gc g lr sstar x)‖ ≤ lr * ‖fedDrift P gc g lr sstar x‖ :=
    mul_le_mul_of_nonneg_left (hP.norm_le _) hlr
  have hsc := fed_geom_scalar (A := sstar * lr) hβ (norm_nonneg (P (g x)))
    (abs_lr_inner_proj_le hP hlr (g x) (fedDrift P gc g lr sstar x))
    (mul_nonneg hlr (norm_nonneg _)) hn hw
  rw [hsq] at hd
  linarith

/-- **Loss change of the aggregated FeDLRT round for long rounds** (hypotheses of
`loss_fedRound_le`, with `s⋆ λ β ≥ 1` in place of `s⋆ λ β ≤ 1`): with
`T = λ ∑_{i<s⋆} (1 + λ β)^i` and `q = (1 + λ β)^{s⋆}`,
`ℒ(x⋆) ≤ ℒ(x) - T (3 - q)/2 · ‖Π ∇ℒ(x)‖²`. -/
theorem loss_fedRound_le_of_one_le [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {sstar : ℕ}
    (hs : 1 ≤ β * (sstar * lr)) (x : E) :
    ℒ (fedRound P gc g lr sstar x) ≤ ℒ x - lr * (∑ i ∈ range sstar, (1 + lr * β) ^ i) *
      ((3 - (1 + lr * β) ^ sstar) / 2) * ‖P (g x)‖ ^ 2 := by
  have h := loss_fedRound_le_geom hℒ hg hgc hP hβ hlr sstar x
  have hR : ∑ j ∈ range sstar, ((1 + lr * β) ^ j - 1) =
      (∑ i ∈ range sstar, (1 + lr * β) ^ i) - sstar := by
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
  have hgeo := geom_sum_mul (1 + lr * β) sstar
  have hq : (1 + lr * β) ^ sstar = (∑ i ∈ range sstar, (1 + lr * β) ^ i) * (lr * β) + 1 := by
    linear_combination -hgeo
  rw [abs_of_nonneg (sub_nonneg.2 hs), hR] at h
  rw [hq]
  linarith

/-- **The FeDLRT round does not increase the loss when `(1 + λ β)^{s⋆} ≤ 3`** (hypotheses of
`loss_fedRound_le`, no other restriction on the step size). -/
theorem loss_fedRound_le_of_pow_le_three [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {sstar : ℕ}
    (h3 : (1 + lr * β) ^ sstar ≤ 3) (x : E) :
    ℒ (fedRound P gc g lr sstar x) ≤ ℒ x := by
  have hb : 0 ≤ 1 + lr * β := add_nonneg zero_le_one (mul_nonneg hlr hβ)
  rcases le_total (lr * β * sstar) 1 with hs | hs
  · have h := loss_fedRound_le_two_ninths hℒ hg hgc hP hβ hlr hs x
    have h0 : 0 ≤ 2 / 9 * (sstar * lr) * ‖P (g x)‖ ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) hlr)) (sq_nonneg _)
    linarith
  · have hs' : 1 ≤ β * (sstar * lr) := by
      have e : β * (sstar * lr) = lr * β * sstar := by ring
      rw [e]; exact hs
    have h := loss_fedRound_le_of_one_le hℒ hg hgc hP hβ hlr hs' x
    have hS : 0 ≤ ∑ i ∈ range sstar, (1 + lr * β) ^ i :=
      sum_nonneg fun i _ => pow_nonneg hb i
    have h0 : 0 ≤ lr * (∑ i ∈ range sstar, (1 + lr * β) ^ i) *
        ((3 - (1 + lr * β) ^ sstar) / 2) * ‖P (g x)‖ ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg hlr hS) (by linarith)) (sq_nonneg _)
    linarith

/-- **The FeDLRT round decreases the loss when `(1 + λ β)^{s⋆} < 3`** and the projected gradient
does not vanish (hypotheses of `loss_fedRound_le`, no other restriction on the step size). -/
theorem loss_fedRound_lt_of_pow_lt_three [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 < lr) {sstar : ℕ} (hs0 : 0 < sstar)
    (h3 : (1 + lr * β) ^ sstar < 3) {x : E} (hx : P (g x) ≠ 0) :
    ℒ (fedRound P gc g lr sstar x) < ℒ x := by
  have hb : 0 < 1 + lr * β := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hlr.le hβ)
  have ha : 0 < ‖P (g x)‖ ^ 2 := pow_pos (norm_pos_iff.2 hx) 2
  have hsr : (0 : ℝ) < sstar := Nat.cast_pos.2 hs0
  rcases le_total (lr * β * sstar) 1 with hs | hs
  · have h := loss_fedRound_le_two_ninths hℒ hg hgc hP hβ hlr.le hs x
    have h0 : 0 < 2 / 9 * (sstar * lr) * ‖P (g x)‖ ^ 2 :=
      mul_pos (mul_pos (by norm_num) (mul_pos hsr hlr)) ha
    linarith
  · have hs' : 1 ≤ β * (sstar * lr) := by
      have e : β * (sstar * lr) = lr * β * sstar := by ring
      rw [e]; exact hs
    have h := loss_fedRound_le_of_one_le hℒ hg hgc hP hβ hlr.le hs' x
    have hS : 0 < ∑ i ∈ range sstar, (1 + lr * β) ^ i :=
      sum_pos (fun i _ => pow_pos hb i) (nonempty_range_iff.2 hs0.ne')
    have h0 : 0 < lr * (∑ i ∈ range sstar, (1 + lr * β) ^ i) *
        ((3 - (1 + lr * β) ^ sstar) / 2) * ‖P (g x)‖ ^ 2 :=
      mul_pos (mul_pos (mul_pos hlr hS) (by linarith)) ha
    linarith

/-! ### The bound is attained, and the threshold is exact -/

/-- **The bound of `loss_fedRound_le_of_one_le` is attained** for every step size and every
number of local steps: for a client with the gradient `z ↦ -z` (`β = 1`), the loss
`ℒ(y) = ⟪v, y⟫ + ‖y‖²/2`, `Π = 1` and `x = 0`,
`ℒ(x⋆) = ℒ(0) - T (3 - q)/2 · ‖Π ∇ℒ(0)‖²`. -/
theorem loss_fedRound_neg_eq (v : E) (lr : ℝ) (sstar : ℕ) :
    ⟪v, fedRound (1 : E →L[ℝ] E) (fun _ : Unit => fun z : E => -z) (fun y => v + y) lr sstar
        0⟫ + ‖fedRound (1 : E →L[ℝ] E) (fun _ : Unit => fun z : E => -z) (fun y => v + y) lr
          sstar 0‖ ^ 2 / 2 =
      ⟪v, (0 : E)⟫ + ‖(0 : E)‖ ^ 2 / 2 - lr * (∑ i ∈ range sstar, (1 + lr * 1) ^ i) *
        ((3 - (1 + lr * 1) ^ sstar) / 2) * ‖(1 : E →L[ℝ] E) (v + 0)‖ ^ 2 := by
  have hgeo := geom_sum_mul (1 + lr) sstar
  rw [fedRound_neg_unit, inner_zero_right, norm_zero, inner_neg_right, norm_neg, norm_smul,
    real_inner_smul_right, real_inner_self_eq_norm_sq, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [one_apply_eq_self, add_zero, mul_one]
  linear_combination ((3 - (1 + lr) ^ sstar) / 2 * ‖v‖ ^ 2) * hgeo

/-- With a client gradient `z ↦ -z` and the loss `ℒ(y) = ⟪v, y⟫ + ‖y‖²/2` (`β = 1`), `v ≠ 0`, a
FeDLRT round from `x = 0` increases the loss as soon as `(1 + λ)^{s⋆} > 3`. -/
theorem loss_lt_loss_fedRound_neg {v : E} (hv : v ≠ 0) {lr : ℝ} {sstar : ℕ}
    (h3 : 3 < (1 + lr) ^ sstar) :
    ⟪v, (0 : E)⟫ + ‖(0 : E)‖ ^ 2 / 2 <
      ⟪v, fedRound (1 : E →L[ℝ] E) (fun _ : Unit => fun z : E => -z) (fun y => v + y) lr sstar
        0⟫ + ‖fedRound (1 : E →L[ℝ] E) (fun _ : Unit => fun z : E => -z) (fun y => v + y) lr
          sstar 0‖ ^ 2 / 2 := by
  rw [fedRound_neg_unit, inner_zero_right, norm_zero, inner_neg_right, norm_neg, norm_smul,
    real_inner_smul_right, real_inner_self_eq_norm_sq, mul_pow, Real.norm_eq_abs, sq_abs]
  have h2 : 0 < ((1 + lr) ^ sstar - 1) * ((1 + lr) ^ sstar - 3) :=
    mul_pos (by linarith) (by linarith)
  have h := mul_pos h2 (pow_pos (norm_pos_iff.2 hv) 2)
  linarith

/-- **The condition `(1 + λ β)^{s⋆} ≤ 3` of `loss_fedRound_le_of_pow_le_three` is necessary in
its generality.** For every `v ≠ 0` there are a loss, a global gradient and one client gradient
with the Lipschitz constant `1` for which every round with `(1 + λ)^{s⋆} > 3` increases the
loss. The global gradient `y ↦ v + y` is not the average of the client gradient `z ↦ -z`. -/
theorem exists_fedRound_ascent {v : E} (hv : v ≠ 0) :
    ∃ (ℒ : E → ℝ) (g : E → E) (gc : Unit → E → E),
      (∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) ∧ (∀ x y, ‖g x - g y‖ ≤ 1 * ‖x - y‖) ∧
      (∀ c x y, ‖gc c x - gc c y‖ ≤ 1 * ‖x - y‖) ∧
      ∀ (lr : ℝ) (sstar : ℕ), 3 < (1 + lr * 1) ^ sstar →
        ℒ 0 < ℒ (fedRound (1 : E →L[ℝ] E) gc g lr sstar 0) := by
  refine ⟨fun y => ⟪v, y⟫ + ‖y‖ ^ 2 / 2, fun y => v + y, fun _ z => -z,
    hasFDerivAt_inner_add_half_norm_sq v, fun x y => le_of_eq ?_, fun _ x y => le_of_eq ?_,
    fun lr sstar h3 => loss_lt_loss_fedRound_neg hv (by rwa [mul_one] at h3)⟩
  · rw [add_sub_add_left_eq_sub, one_mul]
  · rw [neg_sub_neg, one_mul, norm_sub_rev]

/-- `loss_fedRound_lt_of_pow_lt_three` beyond the range `λ β s⋆ ≤ 1`: two identical clients, two
local steps of length `3/5` on the quadratic loss, so that `λ β s⋆ = 6/5` and
`(1 + λ β)^{s⋆} = 64/25 < 3`. -/
example {x : E} (hx : x ≠ 0) :
    ‖fedRound (1 : E →L[ℝ] E) (fun _ : Fin 2 => id) id (3 / 5) 2 x‖ ^ 2 / 2 < ‖x‖ ^ 2 / 2 :=
  loss_fedRound_lt_of_pow_lt_three (ℒ := fun x : E => ‖x‖ ^ 2 / 2) hasFDerivAt_half_norm_sq
    lipschitz_id_grad (fun _ => lipschitz_id_grad) IsOrthProj.one zero_le_one (by norm_num)
    (by norm_num) (by norm_num) hx

/-- The hypotheses of `loss_fedRound_le_of_one_le` hold for two identical clients and two local
steps of length `3/5` on the quadratic loss (`λ β s⋆ = 6/5`). -/
example (x : E) :
    ‖fedRound (1 : E →L[ℝ] E) (fun _ : Fin 2 => id) id (3 / 5) 2 x‖ ^ 2 / 2 ≤
      ‖x‖ ^ 2 / 2 - 3 / 5 * (∑ i ∈ range 2, (1 + 3 / 5 * 1 : ℝ) ^ i) *
        ((3 - (1 + 3 / 5 * 1) ^ 2) / 2) * ‖(1 : E →L[ℝ] E) (id x)‖ ^ 2 :=
  loss_fedRound_le_of_one_le (ℒ := fun x : E => ‖x‖ ^ 2 / 2) hasFDerivAt_half_norm_sq
    lipschitz_id_grad (fun _ => lipschitz_id_grad) IsOrthProj.one zero_le_one (by norm_num)
    (by norm_num) x

/-! ### Convex clients -/

section ConvexClients

/-- The displacement of a client after `s` local steps is `-λ` times the sum of the projected
local gradients `Π (∇ℒ_c(z^j) - ∇ℒ_c(x) + ∇ℒ(x))`. -/
lemma fedClientIter_sub_eq_sum (P : E →L[ℝ] E) (gc : ι → E → E) (g : E → E) (lr : ℝ) (x : E)
    (c : ι) (s : ℕ) :
    fedClientIter P gc g lr x c s - x =
      -(lr • ∑ j ∈ range s, P (gc c (fedClientIter P gc g lr x c j) - gc c x + g x)) := by
  induction s with
  | zero => simp [fedClientIter]
  | succ s ih =>
    rw [fedClientIter_succ, sub_right_comm, ih, sum_range_succ, smul_add, neg_add,
      sub_eq_add_neg]

/-- The squared displacement of a client is at most `λ² s` times the sum of the squared
projected local gradients. -/
lemma norm_sq_fedClientIter_sub_le (P : E →L[ℝ] E) (gc : ι → E → E) (g : E → E) (lr : ℝ)
    (x : E) (c : ι) (s : ℕ) :
    ‖fedClientIter P gc g lr x c s - x‖ ^ 2 ≤ lr ^ 2 * (s *
      ∑ j ∈ range s, ‖P (gc c (fedClientIter P gc g lr x c j) - gc c x + g x)‖ ^ 2) := by
  rw [fedClientIter_sub_eq_sum, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg lr)
  calc ‖∑ j ∈ range s, P (gc c (fedClientIter P gc g lr x c j) - gc c x + g x)‖ ^ 2
      ≤ (∑ j ∈ range s, ‖P (gc c (fedClientIter P gc g lr x c j) - gc c x + g x)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (range s).card *
          ∑ j ∈ range s, ‖P (gc c (fedClientIter P gc g lr x c j) - gc c x + g x)‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ = s * ∑ j ∈ range s, ‖P (gc c (fedClientIter P gc g lr x c j) - gc c x + g x)‖ ^ 2 := by
        rw [card_range]

/-- **Local steps of a convex client move against the global gradient.** Let the client loss
`f` be convex (in the form of the gradient inequality) with a `β`-Lipschitz gradient `∇ℒ_c`.
The local steps are gradient steps for `f + ⟪∇ℒ(x) - ∇ℒ_c(x), ·⟫`, whose gradient at `x` is
`∇ℒ(x)`; so `⟪∇ℒ(x), z^s - x⟫ ≤ -λ (1 - λ β/2) ∑_{j<s} ‖Π (∇ℒ_c(z^j) - ∇ℒ_c(x) + ∇ℒ(x))‖²`. -/
lemma inner_fedClientIter_sub_le {c : ι} {f : E → ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (gc c y)) y)
    (hgc : ∀ y z, ‖gc c y - gc c z‖ ≤ β * ‖y - z‖)
    (hconv : ∀ y z, f y + ⟪gc c y, z - y⟫ ≤ f z) (hP : IsOrthProj P) (x : E) (s : ℕ) :
    ⟪g x, fedClientIter P gc g lr x c s - x⟫ ≤ -(lr * (1 - lr * β / 2) *
      ∑ j ∈ range s, ‖P (gc c (fedClientIter P gc g lr x c j) - gc c x + g x)‖ ^ 2) := by
  have key : ∀ s : ℕ, f (fedClientIter P gc g lr x c s) +
      ⟪g x - gc c x, fedClientIter P gc g lr x c s⟫ ≤ f x + ⟪g x - gc c x, x⟫ -
        lr * (1 - lr * β / 2) *
          ∑ j ∈ range s, ‖P (gc c (fedClientIter P gc g lr x c j) - gc c x + g x)‖ ^ 2 := by
    intro s
    induction s with
    | zero => simp [fedClientIter]
    | succ s ih =>
      have hd := descent_lemma hf hgc (fedClientIter P gc g lr x c s)
        (fedClientIter P gc g lr x c (s + 1))
      have hstep : fedClientIter P gc g lr x c (s + 1) - fedClientIter P gc g lr x c s =
          -(lr • P (gc c (fedClientIter P gc g lr x c s) - gc c x + g x)) := by
        rw [fedClientIter_succ, sub_sub_cancel_left]
      rw [hstep, inner_neg_right, inner_smul_right, norm_neg, norm_smul, mul_pow,
        Real.norm_eq_abs, sq_abs] at hd
      have hl : ⟪g x - gc c x, fedClientIter P gc g lr x c (s + 1)⟫ =
          ⟪g x - gc c x, fedClientIter P gc g lr x c s⟫ - lr * ⟪g x - gc c x,
            P (gc c (fedClientIter P gc g lr x c s) - gc c x + g x)⟫ := by
        rw [fedClientIter_succ, inner_sub_right, inner_smul_right]
      have hAB : gc c (fedClientIter P gc g lr x c s) + (g x - gc c x) =
          gc c (fedClientIter P gc g lr x c s) - gc c x + g x := by abel
      have hG : lr * ⟪gc c (fedClientIter P gc g lr x c s),
            P (gc c (fedClientIter P gc g lr x c s) - gc c x + g x)⟫ +
          lr * ⟪g x - gc c x, P (gc c (fedClientIter P gc g lr x c s) - gc c x + g x)⟫ =
          lr * ‖P (gc c (fedClientIter P gc g lr x c s) - gc c x + g x)‖ ^ 2 := by
        rw [← mul_add, ← inner_add_left, hAB, real_inner_comm, hP.inner_self_apply]
      rw [sum_range_succ]
      linarith
  have h1 := key s
  have h2 := hconv x (fedClientIter P gc g lr x c s)
  have h3 : ⟪g x, fedClientIter P gc g lr x c s - x⟫ =
      ⟪g x - gc c x, fedClientIter P gc g lr x c s⟫ - ⟪g x - gc c x, x⟫ +
        ⟪gc c x, fedClientIter P gc g lr x c s - x⟫ := by
    rw [← inner_sub_right, ← inner_add_left, sub_add_cancel]
  linarith

/-- The displacement of the round is the average of the displacements of the clients. -/
lemma fedRound_sub_eq [Fintype ι] [Nonempty ι] (P : E →L[ℝ] E) (gc : ι → E → E) (g : E → E)
    (lr : ℝ) (sstar : ℕ) (x : E) :
    fedRound P gc g lr sstar x - x =
      (Fintype.card ι : ℝ)⁻¹ • ∑ c, (fedClientIter P gc g lr x c sstar - x) := by
  have hC : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [fedRound, sum_sub_distrib, sum_const, card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub,
    smul_smul, inv_mul_cancel₀ hC, one_smul]

variable {ℒc : ι → E → ℝ}

/-- **Loss descent of the aggregated FeDLRT round for convex clients.** Let the global loss and
the client losses have `β`-Lipschitz gradients and let every client loss be convex (in the form
of the gradient inequality); the global gradient need not be the average of the client
gradients. If `(s⋆ + 1) λ β ≤ 2`, then
`ℒ(x⋆) ≤ ℒ(x) - (λ/2) (2 - (s⋆ + 1) λ β) ‖Π ∇ℒ(x)‖²`.
Without convexity the loss can increase as soon as `(1 + λ β)^{s⋆} > 3`
(`exists_fedRound_ascent`), which happens for `s⋆ λ β` slightly above `log 3`. -/
theorem loss_fedRound_le_of_convex [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hℒc : ∀ c x, HasFDerivAt (ℒc c) (innerSL ℝ (gc c x)) x)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hconv : ∀ c x y, ℒc c x + ⟪gc c x, y - x⟫ ≤ ℒc c y)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {sstar : ℕ} (hs0 : 0 < sstar)
    (hs : lr * β * (sstar + 1) ≤ 2) (x : E) :
    ℒ (fedRound P gc g lr sstar x) ≤
      ℒ x - lr / 2 * (2 - lr * β * (sstar + 1)) * ‖P (g x)‖ ^ 2 := by
  have hC : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  -- one client
  have hcl : ∀ c, ⟪g x, fedClientIter P gc g lr x c sstar - x⟫ +
      β / 2 * ‖fedClientIter P gc g lr x c sstar - x‖ ^ 2 ≤
        -(lr / 2 * (2 - lr * β * (sstar + 1)) * ‖P (g x)‖ ^ 2) := by
    intro c
    have h1 := inner_fedClientIter_sub_le (gc := gc) (g := g) (lr := lr) (c := c) (hℒc c)
      (hgc c) (hconv c) hP x sstar
    have h2 := mul_le_mul_of_nonneg_left (norm_sq_fedClientIter_sub_le P gc g lr x c sstar)
      (div_nonneg hβ zero_le_two)
    have hQ : ‖P (g x)‖ ^ 2 ≤
        ∑ j ∈ range sstar, ‖P (gc c (fedClientIter P gc g lr x c j) - gc c x + g x)‖ ^ 2 := by
      have h := single_le_sum
        (f := fun j => ‖P (gc c (fedClientIter P gc g lr x c j) - gc c x + g x)‖ ^ 2)
        (fun j _ => sq_nonneg _) (mem_range.2 hs0)
      simpa [fedClientIter] using h
    have h4 : 0 ≤ lr / 2 * (2 - lr * β * (sstar + 1)) :=
      mul_nonneg (div_nonneg hlr zero_le_two) (sub_nonneg.2 hs)
    have h5 := mul_le_mul_of_nonneg_left hQ h4
    linarith
  -- the average
  have hd := descent_lemma hℒ hg x (fedRound P gc g lr sstar x)
  have hin : ⟪g x, fedRound P gc g lr sstar x - x⟫ =
      (Fintype.card ι : ℝ)⁻¹ * ∑ c, ⟪g x, fedClientIter P gc g lr x c sstar - x⟫ := by
    rw [fedRound_sub_eq, inner_smul_right, inner_sum]
  have hnorm : ‖fedRound P gc g lr sstar x - x‖ ^ 2 ≤
      (Fintype.card ι : ℝ)⁻¹ * ∑ c, ‖fedClientIter P gc g lr x c sstar - x‖ ^ 2 := by
    rw [fedRound_sub_eq, norm_smul, mul_pow, norm_inv, Real.norm_natCast]
    calc ((Fintype.card ι : ℝ)⁻¹) ^ 2 * ‖∑ c, (fedClientIter P gc g lr x c sstar - x)‖ ^ 2
        ≤ ((Fintype.card ι : ℝ)⁻¹) ^ 2 * ((Fintype.card ι : ℝ) *
            ∑ c, ‖fedClientIter P gc g lr x c sstar - x‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          calc ‖∑ c, (fedClientIter P gc g lr x c sstar - x)‖ ^ 2
              ≤ (∑ c, ‖fedClientIter P gc g lr x c sstar - x‖) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
            _ ≤ (univ : Finset ι).card * ∑ c, ‖fedClientIter P gc g lr x c sstar - x‖ ^ 2 :=
                sq_sum_le_card_mul_sum_sq
            _ = (Fintype.card ι : ℝ) * ∑ c, ‖fedClientIter P gc g lr x c sstar - x‖ ^ 2 := by
                rw [card_univ]
      _ = (Fintype.card ι : ℝ)⁻¹ * ∑ c, ‖fedClientIter P gc g lr x c sstar - x‖ ^ 2 := by
          rw [pow_two, mul_assoc, inv_mul_cancel_left₀ hC.ne']
  have hsum : ∑ c, (⟪g x, fedClientIter P gc g lr x c sstar - x⟫ +
      β / 2 * ‖fedClientIter P gc g lr x c sstar - x‖ ^ 2) ≤
        ∑ _c : ι, -(lr / 2 * (2 - lr * β * (sstar + 1)) * ‖P (g x)‖ ^ 2) :=
    sum_le_sum fun c _ => hcl c
  rw [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul] at hsum
  have h6 := mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hC.le)
  rw [inv_mul_cancel_left₀ hC.ne'] at h6
  have h7 := mul_le_mul_of_nonneg_left hnorm (div_nonneg hβ zero_le_two)
  rw [hin] at hd
  linarith

/-- **The FeDLRT round decreases the loss for convex clients when `(s⋆ + 1) λ β < 2`** and the
projected gradient does not vanish. -/
theorem loss_fedRound_lt_of_convex [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hℒc : ∀ c x, HasFDerivAt (ℒc c) (innerSL ℝ (gc c x)) x)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hconv : ∀ c x y, ℒc c x + ⟪gc c x, y - x⟫ ≤ ℒc c y)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 < lr) {sstar : ℕ} (hs0 : 0 < sstar)
    (hs : lr * β * (sstar + 1) < 2) {x : E} (hx : P (g x) ≠ 0) :
    ℒ (fedRound P gc g lr sstar x) < ℒ x := by
  have h := loss_fedRound_le_of_convex hℒ hg hℒc hgc hconv hP hβ hlr.le hs0 hs.le x
  have h0 : 0 < lr / 2 * (2 - lr * β * (sstar + 1)) * ‖P (g x)‖ ^ 2 :=
    mul_pos (mul_pos (half_pos hlr) (sub_pos.2 hs)) (pow_pos (norm_pos_iff.2 hx) 2)
  linarith

/-- With clients whose gradient vanishes identically (convex, `β = 1` admissible), `Π = 1` and
the global gradient `y ↦ y`, the client iterates are `z^s = (1 - s λ) x`. -/
lemma fedClientIter_zero_id (lr : ℝ) (x : E) (c : ι) (s : ℕ) :
    fedClientIter (1 : E →L[ℝ] E) (fun _ : ι => fun _ : E => (0 : E)) id lr x c s =
      (1 - s * lr) • x := by
  induction s with
  | zero => simp [fedClientIter]
  | succ s ih =>
    rw [fedClientIter_succ, ih]
    simp only [sub_self, zero_add, id_eq, one_apply_eq_self]
    push_cast
    module

/-- **For convex clients no descent is possible when `s⋆ λ β ≥ 2`**: with one client whose
gradient vanishes identically and the loss `‖y‖²/2` (`β = 1`), a FeDLRT round does not decrease
the loss. So the condition `(s⋆ + 1) λ β < 2` of `loss_fedRound_lt_of_convex` cannot be weakened
beyond `s⋆ λ β < 2`. -/
theorem loss_le_loss_fedRound_zero {lr : ℝ} {sstar : ℕ} (h2 : 2 ≤ sstar * lr) (x : E) :
    ‖x‖ ^ 2 / 2 ≤ ‖fedRound (1 : E →L[ℝ] E) (fun _ : Unit => fun _ : E => (0 : E)) id lr sstar
      x‖ ^ 2 / 2 := by
  have e : fedRound (1 : E →L[ℝ] E) (fun _ : Unit => fun _ : E => (0 : E)) id lr sstar x =
      (1 - sstar * lr) • x := by
    simp [fedRound, fedClientIter_zero_id]
  rw [e, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have h1 : 1 ≤ (1 - sstar * lr) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (zero_le_two.trans h2)]
  have h := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖x‖)
  linarith

/-- The hypotheses of `loss_fedRound_lt_of_convex` hold beyond the range of the general class:
two identical clients with the convex loss `‖y‖²/2`, four local steps of length `3/8`, so that
`s⋆ λ β = 3/2` and `(1 + λ β)^{s⋆} > 3`. -/
example {x : E} (hx : x ≠ 0) :
    ‖fedRound (1 : E →L[ℝ] E) (fun _ : Fin 2 => id) id (3 / 8) 4 x‖ ^ 2 / 2 < ‖x‖ ^ 2 / 2 := by
  refine loss_fedRound_lt_of_convex (ℒ := fun x : E => ‖x‖ ^ 2 / 2)
    (ℒc := fun _ : Fin 2 => fun x : E => ‖x‖ ^ 2 / 2) (β := 1) hasFDerivAt_half_norm_sq
    lipschitz_id_grad (fun _ => hasFDerivAt_half_norm_sq) (fun _ => lipschitz_id_grad)
    (fun _ y z => ?_) IsOrthProj.one zero_le_one (by norm_num) (by norm_num) (by norm_num) hx
  have h := sq_nonneg ‖z - y‖
  have e : ‖z‖ ^ 2 = ‖y + (z - y)‖ ^ 2 := by rw [add_sub_cancel]
  rw [norm_add_sq_real] at e
  change ‖y‖ ^ 2 / 2 + ⟪y, z - y⟫ ≤ ‖z‖ ^ 2 / 2
  linarith

end ConvexClients

/-! ### When the global gradient is the average of the client gradients

Clients with the gradients `z ↦ h_c z + v` and the global gradient `y ↦ v + h̄ y`. If `h̄` is the
mean of the `h_c`, the global gradient is the average of the client gradients
(`inv_card_smul_sum_linear`), which is the setting of arXiv 2406.17887. Many local steps turn
the step of client `c` into `φ_c v` with `φ_c = λ ∑_{i<s⋆} (1 - λ h_c)^i`, close to `v / h_c` for
`h_c > 0`, so the round is a step of length `m = mean φ_c`, and the loss does not decrease when
`h̄ m ≥ 2`. -/

section AveragedClients

/-- `ℒ(y) = ⟪v, y⟫ + h̄ ‖y‖²/2` has the gradient `y ↦ v + h̄ y`. -/
lemma hasFDerivAt_inner_add_mul_half_norm_sq (v : E) (hbar : ℝ) (x : E) :
    HasFDerivAt (fun y : E => ⟪v, y⟫ + hbar * (‖y‖ ^ 2 / 2)) (innerSL ℝ (v + hbar • x)) x :=
  (((innerSL ℝ v).hasFDerivAt (x := x)).add
    ((hasFDerivAt_half_norm_sq x).const_mul hbar)).congr_fderiv
      (by ext y; simp)

/-- The average of the client gradients `z ↦ h_c z + v` is `y ↦ v + (mean h) y`. -/
lemma inv_card_smul_sum_linear [Fintype ι] [Nonempty ι] (h : ι → ℝ) (v y : E) :
    (Fintype.card ι : ℝ)⁻¹ • ∑ c, (h c • y + v) =
      v + ((Fintype.card ι : ℝ)⁻¹ * ∑ c, h c) • y := by
  have hC : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [sum_add_distrib, ← sum_smul, sum_const, card_univ, smul_add,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul, inv_mul_cancel₀ hC, one_smul, add_comm]

/-- With `Π = 1`, client gradients `z ↦ h_c z + v` and global gradient `y ↦ v + h̄ y`, the client
iterates of FeDLRT started at `0` are `z^s = -(λ ∑_{i<s} (1 - λ h_c)^i) v`. -/
lemma fedClientIter_linear (h : ι → ℝ) (hbar : ℝ) (v : E) (lr : ℝ) (c : ι) (s : ℕ) :
    fedClientIter (1 : E →L[ℝ] E) (fun c z => h c • z + v) (fun y => v + hbar • y) lr 0 c s =
      -((lr * ∑ i ∈ range s, (1 - lr * h c) ^ i) • v) := by
  induction s with
  | zero => simp [fedClientIter]
  | succ s ih =>
    rw [fedClientIter_succ, ih, geom_sum_succ]
    simp only [one_apply_eq_self, smul_zero, add_zero, zero_add]
    module

/-- The FeDLRT round for the clients of `fedClientIter_linear` is a step of length
`m = mean_c (λ ∑_{i<s⋆} (1 - λ h_c)^i)` along `-v`. -/
lemma fedRound_linear [Fintype ι] (h : ι → ℝ) (hbar : ℝ) (v : E) (lr : ℝ) (sstar : ℕ) :
    fedRound (1 : E →L[ℝ] E) (fun c z => h c • z + v) (fun y => v + hbar • y) lr sstar 0 =
      -(((Fintype.card ι : ℝ)⁻¹ * ∑ c, lr * ∑ i ∈ range sstar, (1 - lr * h c) ^ i) • v) := by
  rw [fedRound]
  simp_rw [fedClientIter_linear]
  rw [sum_neg_distrib, ← sum_smul, smul_neg, smul_smul]

/-- **No descent with averaged gradients.** For the clients of `fedClientIter_linear` and the
loss `ℒ(y) = ⟪v, y⟫ + h̄ ‖y‖²/2`, a FeDLRT round from `0` does not decrease the loss when
`h̄ m ≥ 2`, where `m ≥ 0` is the length of the round (`fedRound_linear`). -/
theorem loss_le_loss_fedRound_linear [Fintype ι] (h : ι → ℝ) (hbar : ℝ) (v : E) (lr : ℝ)
    (sstar : ℕ)
    (hm0 : 0 ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ c, lr * ∑ i ∈ range sstar, (1 - lr * h c) ^ i)
    (hm : 2 ≤ hbar *
      ((Fintype.card ι : ℝ)⁻¹ * ∑ c, lr * ∑ i ∈ range sstar, (1 - lr * h c) ^ i)) :
    ⟪v, (0 : E)⟫ + hbar * (‖(0 : E)‖ ^ 2 / 2) ≤
      ⟪v, fedRound (1 : E →L[ℝ] E) (fun c z => h c • z + v) (fun y => v + hbar • y) lr sstar
        0⟫ + hbar * (‖fedRound (1 : E →L[ℝ] E) (fun c z => h c • z + v)
          (fun y => v + hbar • y) lr sstar 0‖ ^ 2 / 2) := by
  rw [fedRound_linear, inner_zero_right, norm_zero, inner_neg_right, norm_neg, norm_smul,
    real_inner_smul_right, real_inner_self_eq_norm_sq, mul_pow, Real.norm_eq_abs, sq_abs]
  have h1 := mul_nonneg (mul_nonneg hm0 (sub_nonneg.2 hm)) (sq_nonneg ‖v‖)
  linarith

/-- **Averaged gradients, one concave client among four**: Hessians `-1, 1, 1, 1` (mean `1/2`,
all client gradients `1`-Lipschitz), `λ = 1/4` and `s⋆ = 12`, so `s⋆ λ β = 3`: no descent. -/
example (v : E) :
    ⟪v, (0 : E)⟫ + 1 / 2 * (‖(0 : E)‖ ^ 2 / 2) ≤
      ⟪v, fedRound (1 : E →L[ℝ] E)
        (fun c : Fin 4 => fun z => (if c = 0 then (-1 : ℝ) else 1) • z + v)
        (fun y => v + (1 / 2 : ℝ) • y) (1 / 4) 12 0⟫ + 1 / 2 *
          (‖fedRound (1 : E →L[ℝ] E)
            (fun c : Fin 4 => fun z => (if c = 0 then (-1 : ℝ) else 1) • z + v)
            (fun y => v + (1 / 2 : ℝ) • y) (1 / 4) 12 0‖ ^ 2 / 2) :=
  loss_le_loss_fedRound_linear (fun c : Fin 4 => if c = 0 then (-1 : ℝ) else 1) (1 / 2) v
    (1 / 4) 12 (by norm_num [Fin.sum_univ_four, sum_range_succ])
    (by norm_num [Fin.sum_univ_four, sum_range_succ])

/-- **Averaged gradients, convex clients**: Hessians `0, 1` (mean `1/2`), `λ = 1/2` and
`s⋆ = 15`, so `s⋆ λ β = 15/2`: no descent. -/
example (v : E) :
    ⟪v, (0 : E)⟫ + 1 / 2 * (‖(0 : E)‖ ^ 2 / 2) ≤
      ⟪v, fedRound (1 : E →L[ℝ] E)
        (fun c : Fin 2 => fun z => (if c = 0 then (0 : ℝ) else 1) • z + v)
        (fun y => v + (1 / 2 : ℝ) • y) (1 / 2) 15 0⟫ + 1 / 2 *
          (‖fedRound (1 : E →L[ℝ] E)
            (fun c : Fin 2 => fun z => (if c = 0 then (0 : ℝ) else 1) • z + v)
            (fun y => v + (1 / 2 : ℝ) • y) (1 / 2) 15 0‖ ^ 2 / 2) :=
  loss_le_loss_fedRound_linear (fun c : Fin 2 => if c = 0 then (0 : ℝ) else 1) (1 / 2) v
    (1 / 2) 15 (by norm_num [Fin.sum_univ_two, sum_range_succ])
    (by norm_num [Fin.sum_univ_two, sum_range_succ])

end AveragedClients

end FederatedThreshold

end LeanDLRA
