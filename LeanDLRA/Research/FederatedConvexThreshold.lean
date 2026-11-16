import LeanDLRA.Research.FederatedDescentThreshold

/-!
# FeDLRT with convex clients: descent up to `s⋆ λ β < 2`

One aggregated round of FeDLRT with variance correction (Schotthöfer–Laiu, arXiv 2406.17887,
before truncation) is `fedRound`: `s⋆` local steps of length `λ` on every client, then the
average. For convex client losses `loss_fedRound_le_of_convex` proves a loss descent for
`(s⋆ + 1) λ β < 2`, and `loss_le_loss_fedRound_zero` shows that there is none in general for
`s⋆ λ β ≥ 2`. This file removes the gap between the two conditions: for `λ β ≤ 1` the round
decreases the loss as soon as `s⋆ λ β < 2`.

## Notation

`z^j` are the local iterates of one client, `G_j = Π (∇ℒ_c(z^j) - ∇ℒ_c(x) + ∇ℒ(x))` the projected
local gradients (so `G_0 = Π ∇ℒ(x)` and `z^s - x = -λ ∑_{j<s} G_j`), and `a = ‖Π ∇ℒ(x)‖`.

## Main results

* `add_inner_add_norm_sq_le_of_convex`: for a convex function with `β`-Lipschitz gradient and
  `0 ≤ λ`, `λ β ≤ 1`: `f(y) + ⟪∇f(y), z - y⟫ + (λ/2) ‖∇f(z) - ∇f(y)‖² ≤ f(z)`.
* `inner_fedClientIter_sub_le_neg_sum`: `⟪∇ℒ(x), z^s - x⟫ ≤ -λ ∑_{j<s} ‖G_j‖²` for `λ β ≤ 1`.
  Compare `inner_fedClientIter_sub_le`, which has the factor `1 - λ β / 2` on the right.
* `loss_fedRound_le_of_forall_client`: the round inherits a bound that holds for the
  displacement of every client.
* `loss_fedRound_le_of_convex_of_lr_mul_le_one`:
  `ℒ(x⋆) ≤ ℒ(x) - λ (1 - s⋆ λ β / 2) a²` for `λ β ≤ 1` and `s⋆ λ β ≤ 2`, and
  `loss_fedRound_lt_of_convex_of_lr_mul_le_one`: the loss decreases when `s⋆ λ β < 2` and
  `Π ∇ℒ(x) ≠ 0`.

## Remarks on the hypotheses

* As in `loss_fedRound_le_of_convex`, the global gradient need not be the average of the client
  gradients, and the client losses are convex in the form of the gradient inequality.
* For `s⋆ ≥ 2` the condition `s⋆ λ β < 2` implies `λ β ≤ 1`. For `s⋆ = 1` the round is one
  projected gradient step when the global gradient is used by all clients, and the range
  `1 < λ β < 2` is the descent lemma; it is not covered here.
* The proof adds the inequality of the first item along the closed chain
  `x, z^1, …, z^j, x`: the function values cancel, and the squared gradient differences cancel
  against the inner products of consecutive gradients.
* When the global gradient is the average of the client gradients (the setting of the paper),
  the condition is far from necessary. A numerical computation of the worst case over convex
  clients (performance estimation, a semidefinite program in the Gram matrix of the gradients)
  gives descent for `s⋆ λ β` below `4.00`, `5.63`, `6.84` for `s⋆ = 2, 3, 4` and below `6.83` for
  `s⋆ = 6, …, 16`, which is the value `4 + 2√2` of the quadratic clients with Hessians `0` and
  `1` (`loss_le_loss_fedRound_linear`). This is an observation, not a theorem of this file.
-/

open Set Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section FederatedConvexThreshold

variable {ι : Type*} {ℒ : E → ℝ} {g : E → E} {gc : ι → E → E} {β lr : ℝ}
  {P : E →L[ℝ] E}

/-- **Gradient inequality of a convex function with Lipschitz gradient, with a step size.** If
`f` is convex (in the form of the gradient inequality), its gradient is `β`-Lipschitz, and
`0 ≤ λ`, `λ β ≤ 1`, then `f(y) + ⟪∇f(y), z - y⟫ + (λ/2) ‖∇f(z) - ∇f(y)‖² ≤ f(z)`. For `β > 0`
and `λ = 1/β` this is the usual lower bound with `1/(2β)`. -/
lemma add_inner_add_norm_sq_le_of_convex {f : E → ℝ} {gf : E → E}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (gf y)) y)
    (hgf : ∀ y z, ‖gf y - gf z‖ ≤ β * ‖y - z‖)
    (hconv : ∀ y z, f y + ⟪gf y, z - y⟫ ≤ f z) (hlr : 0 ≤ lr) (hlrβ : lr * β ≤ 1) (y z : E) :
    f y + ⟪gf y, z - y⟫ + lr / 2 * ‖gf z - gf y‖ ^ 2 ≤ f z := by
  obtain ⟨d, hd⟩ : ∃ d : E, d = gf z - gf y := ⟨_, rfl⟩
  rw [← hd]
  have h1 := descent_lemma hf hgf z (z - lr • d)
  have h2 := hconv y (z - lr • d)
  have e1 : z - lr • d - z = -(lr • d) := by abel
  have e2 : z - lr • d - y = z - y - lr • d := by abel
  rw [e1, inner_neg_right, inner_smul_right, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs] at h1
  rw [e2, inner_sub_right, inner_smul_right] at h2
  have h3 : lr * ⟪gf z, d⟫ - lr * ⟪gf y, d⟫ = lr * ‖d‖ ^ 2 := by
    rw [← mul_sub, ← inner_sub_left, ← hd, real_inner_self_eq_norm_sq]
  have h0 : lr * (lr * β) ≤ lr := by
    have h := mul_le_mul_of_nonneg_left hlrβ hlr
    rwa [mul_one] at h
  have h4 : β / 2 * (lr ^ 2 * ‖d‖ ^ 2) ≤ lr / 2 * ‖d‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_right h0 (div_nonneg (sq_nonneg ‖d‖) zero_le_two)
    calc β / 2 * (lr ^ 2 * ‖d‖ ^ 2) = lr * (lr * β) * (‖d‖ ^ 2 / 2) := by ring
      _ ≤ lr * (‖d‖ ^ 2 / 2) := h
      _ = lr / 2 * ‖d‖ ^ 2 := by ring
  linarith

/-- **Local steps of a convex client move against the global gradient, without loss in the
constant.** Let the client loss `f` be convex (in the form of the gradient inequality) with a
`β`-Lipschitz gradient `∇ℒ_c`, and let `0 ≤ λ`, `λ β ≤ 1`. With the projected local gradients
`G_j = Π (∇ℒ_c(z^j) - ∇ℒ_c(x) + ∇ℒ(x))`, `⟪∇ℒ(x), z^s - x⟫ ≤ -λ ∑_{j<s} ‖G_j‖²`. A client with
constant gradient attains equality. -/
lemma inner_fedClientIter_sub_le_neg_sum {c : ι} {f : E → ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (gc c y)) y)
    (hgc : ∀ y z, ‖gc c y - gc c z‖ ≤ β * ‖y - z‖)
    (hconv : ∀ y z, f y + ⟪gc c y, z - y⟫ ≤ f z) (hP : IsOrthProj P) (hlr : 0 ≤ lr)
    (hlrβ : lr * β ≤ 1) (x : E) (s : ℕ) :
    ⟪g x, fedClientIter P gc g lr x c s - x⟫ ≤
      -(lr * ∑ j ∈ range s, ‖P (gc c (fedClientIter P gc g lr x c j) - gc c x + g x)‖ ^ 2) := by
  obtain ⟨z, hz⟩ : ∃ z : ℕ → E, z = fedClientIter P gc g lr x c := ⟨_, rfl⟩
  rw [← hz]
  have hz0 : z 0 = x := by rw [hz]; rfl
  have hzs : ∀ j, z (j + 1) = z j - lr • P (gc c (z j) - gc c x + g x) := by
    intro j; rw [hz]; exact fedClientIter_succ P gc g lr x c j
  obtain ⟨G, hG⟩ : ∃ G : ℕ → E, ∀ j, G j = P (gc c (z j) - gc c x + g x) :=
    ⟨fun j => P (gc c (z j) - gc c x + g x), fun _ => rfl⟩
  have hsum : ∑ j ∈ range s, ‖P (gc c (z j) - gc c x + g x)‖ ^ 2 = ∑ j ∈ range s, ‖G j‖ ^ 2 :=
    sum_congr rfl fun j _ => by rw [hG]
  rw [hsum]
  have hzs' : ∀ j, z (j + 1) = z j - lr • G j := fun j => by rw [hG]; exact hzs j
  have hG0 : G 0 = P (g x) := by rw [hG, hz0, sub_self, zero_add]
  -- inner products with the projected gradients
  have hin : ∀ (w : E) (j : ℕ), ⟪w, G j⟫ = ⟪P w, G j⟫ := by
    intro w j
    rw [hG j, hP.inner_comp w, hP.symm w]
  have hpol : ∀ a b : E, lr * ⟪a, b⟫ =
      lr / 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) - lr / 2 * ‖a - b‖ ^ 2 := by
    intro a b
    rw [norm_sub_sq_real]; ring
  -- one local step
  have hstep : ∀ j, f (z (j + 1)) + ⟪g x - gc c x, z (j + 1)⟫ +
      lr / 2 * (‖G j‖ ^ 2 + ‖G (j + 1)‖ ^ 2) ≤ f (z j) + ⟪g x - gc c x, z j⟫ := by
    intro j
    have h1 := add_inner_add_norm_sq_le_of_convex hf hgc hconv hlr hlrβ (z (j + 1)) (z j)
    have e1 : z j - z (j + 1) = lr • G j := by rw [hzs']; abel
    rw [e1, inner_smul_right] at h1
    have h2 : ⟪g x - gc c x, z (j + 1)⟫ =
        ⟪g x - gc c x, z j⟫ - lr * ⟪g x - gc c x, G j⟫ := by
      rw [hzs', inner_sub_right, inner_smul_right]
    have h3 : lr * ⟪gc c (z (j + 1)), G j⟫ + lr * ⟪g x - gc c x, G j⟫ =
        lr * ⟪G (j + 1), G j⟫ := by
      have e : gc c (z (j + 1)) + (g x - gc c x) = gc c (z (j + 1)) - gc c x + g x := by abel
      rw [← mul_add, ← inner_add_left, e, hin (gc c (z (j + 1)) - gc c x + g x) j, hG (j + 1)]
    have h4 : lr / 2 * ‖G (j + 1) - G j‖ ^ 2 ≤ lr / 2 * ‖gc c (z j) - gc c (z (j + 1))‖ ^ 2 := by
      have e : G (j + 1) - G j = P (gc c (z (j + 1)) - gc c (z j)) := by
        rw [hG, hG, ← map_sub]; congr 1; abel
      rw [e, norm_sub_rev (gc c (z j))]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hP.norm_le _) 2) (div_nonneg hlr zero_le_two)
    have h5 := hpol (G (j + 1)) (G j)
    linarith
  -- the chain from `x` to `z^j`
  have hchain : ∀ j, f (z j) + ⟪g x - gc c x, z j⟫ +
      lr / 2 * (2 * ∑ k ∈ range (j + 1), ‖G k‖ ^ 2 - ‖G 0‖ ^ 2 - ‖G j‖ ^ 2) ≤
        f x + ⟪g x - gc c x, x⟫ := by
    intro j
    induction j with
    | zero =>
      simp only [zero_add, sum_range_one]
      rw [hz0]
      linarith
    | succ j ih =>
      have h1 := hstep j
      rw [sum_range_succ _ (j + 1)]
      linarith
  cases s with
  | zero => simp [hz0]
  | succ j =>
    have h1 := hchain j
    have h2 := add_inner_add_norm_sq_le_of_convex hf hgc hconv hlr hlrβ x (z j)
    have h3 : lr / 2 * ‖G j - G 0‖ ^ 2 ≤ lr / 2 * ‖gc c (z j) - gc c x‖ ^ 2 := by
      have e : G j - G 0 = P (gc c (z j) - gc c x) := by
        rw [hG, hG, hz0, ← map_sub]; congr 1; abel
      rw [e]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hP.norm_le _) 2) (div_nonneg hlr zero_le_two)
    have h4 : ⟪g x, z j - x⟫ =
        ⟪gc c x, z j - x⟫ + (⟪g x - gc c x, z j⟫ - ⟪g x - gc c x, x⟫) := by
      rw [← inner_sub_right, ← inner_add_left, add_sub_cancel]
    have h5 : ⟪g x, z (j + 1) - x⟫ = ⟪g x, z j - x⟫ - lr * ⟪G j, G 0⟫ := by
      rw [hzs', sub_right_comm, inner_sub_right (g x) (z j - x) (lr • G j), inner_smul_right,
        hin (g x) j, ← hG0, real_inner_comm (G j) (G 0)]
    have h6 := hpol (G j) (G 0)
    linarith

/-- **The round inherits a bound for the displacement of every client.** If the global loss has
a `β`-Lipschitz gradient and every client satisfies
`⟪∇ℒ(x), z_c - x⟫ + (β/2) ‖z_c - x‖² ≤ -K` for its last iterate `z_c`, then
`ℒ(x⋆) ≤ ℒ(x) - K` for the average `x⋆` of the `z_c`. -/
theorem loss_fedRound_le_of_forall_client [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {sstar : ℕ} {x : E} {K : ℝ}
    (hcl : ∀ c, ⟪g x, fedClientIter P gc g lr x c sstar - x⟫ +
      β / 2 * ‖fedClientIter P gc g lr x c sstar - x‖ ^ 2 ≤ -K) :
    ℒ (fedRound P gc g lr sstar x) ≤ ℒ x - K := by
  have hC : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
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
      β / 2 * ‖fedClientIter P gc g lr x c sstar - x‖ ^ 2) ≤ ∑ _c : ι, -K :=
    sum_le_sum fun c _ => hcl c
  rw [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul] at hsum
  have h6 := mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hC.le)
  rw [inv_mul_cancel_left₀ hC.ne'] at h6
  have h7 := mul_le_mul_of_nonneg_left hnorm (div_nonneg hβ zero_le_two)
  rw [hin] at hd
  linarith

variable {ℒc : ι → E → ℝ}

/-- **Loss descent of the aggregated FeDLRT round for convex clients, up to `s⋆ λ β = 2`.** Let
the global loss and the client losses have `β`-Lipschitz gradients and let every client loss be
convex (in the form of the gradient inequality); the global gradient need not be the average of
the client gradients. If `λ β ≤ 1` and `s⋆ λ β ≤ 2`, then
`ℒ(x⋆) ≤ ℒ(x) - λ (1 - s⋆ λ β / 2) ‖Π ∇ℒ(x)‖²`.
By `loss_le_loss_fedRound_zero` there is no descent in this class for `s⋆ λ β ≥ 2`. -/
theorem loss_fedRound_le_of_convex_of_lr_mul_le_one [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hℒc : ∀ c x, HasFDerivAt (ℒc c) (innerSL ℝ (gc c x)) x)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hconv : ∀ c x y, ℒc c x + ⟪gc c x, y - x⟫ ≤ ℒc c y)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) (hlrβ : lr * β ≤ 1) {sstar : ℕ}
    (hs0 : 0 < sstar) (hs : lr * β * sstar ≤ 2) (x : E) :
    ℒ (fedRound P gc g lr sstar x) ≤
      ℒ x - lr * (1 - lr * β * sstar / 2) * ‖P (g x)‖ ^ 2 := by
  refine loss_fedRound_le_of_forall_client hℒ hg hβ fun c => ?_
  have h1 := inner_fedClientIter_sub_le_neg_sum (gc := gc) (g := g) (lr := lr) (c := c)
    (hℒc c) (hgc c) (hconv c) hP hlr hlrβ x sstar
  have h2 := mul_le_mul_of_nonneg_left (norm_sq_fedClientIter_sub_le P gc g lr x c sstar)
    (div_nonneg hβ zero_le_two)
  have hQ : ‖P (g x)‖ ^ 2 ≤
      ∑ j ∈ range sstar, ‖P (gc c (fedClientIter P gc g lr x c j) - gc c x + g x)‖ ^ 2 := by
    have h := single_le_sum
      (f := fun j => ‖P (gc c (fedClientIter P gc g lr x c j) - gc c x + g x)‖ ^ 2)
      (fun j _ => sq_nonneg _) (mem_range.2 hs0)
    simpa [fedClientIter] using h
  have h4 : 0 ≤ lr * (1 - lr * β * sstar / 2) := mul_nonneg hlr (by linarith)
  have h5 := mul_le_mul_of_nonneg_left hQ h4
  linarith

/-- **The FeDLRT round decreases the loss for convex clients when `λ β ≤ 1` and
`s⋆ λ β < 2`** and the projected gradient does not vanish. -/
theorem loss_fedRound_lt_of_convex_of_lr_mul_le_one [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hℒc : ∀ c x, HasFDerivAt (ℒc c) (innerSL ℝ (gc c x)) x)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hconv : ∀ c x y, ℒc c x + ⟪gc c x, y - x⟫ ≤ ℒc c y)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 < lr) (hlrβ : lr * β ≤ 1) {sstar : ℕ}
    (hs0 : 0 < sstar) (hs : lr * β * sstar < 2) {x : E} (hx : P (g x) ≠ 0) :
    ℒ (fedRound P gc g lr sstar x) < ℒ x := by
  have h := loss_fedRound_le_of_convex_of_lr_mul_le_one hℒ hg hℒc hgc hconv hP hβ hlr.le hlrβ
    hs0 hs.le x
  have h0 : 0 < lr * (1 - lr * β * sstar / 2) * ‖P (g x)‖ ^ 2 :=
    mul_pos (mul_pos hlr (by linarith)) (pow_pos (norm_pos_iff.2 hx) 2)
  linarith

/-- The hypotheses of `loss_fedRound_lt_of_convex_of_lr_mul_le_one` hold where
`loss_fedRound_lt_of_convex` does not apply: two identical clients with the convex loss
`‖y‖²/2`, four local steps of length `15/32`, so that `s⋆ λ β = 15/8` and
`(s⋆ + 1) λ β = 75/32 > 2`. -/
example {x : E} (hx : x ≠ 0) :
    ‖fedRound (1 : E →L[ℝ] E) (fun _ : Fin 2 => id) id (15 / 32) 4 x‖ ^ 2 / 2 < ‖x‖ ^ 2 / 2 := by
  refine loss_fedRound_lt_of_convex_of_lr_mul_le_one (ℒ := fun x : E => ‖x‖ ^ 2 / 2)
    (ℒc := fun _ : Fin 2 => fun x : E => ‖x‖ ^ 2 / 2) (β := 1) hasFDerivAt_half_norm_sq
    lipschitz_id_grad (fun _ => hasFDerivAt_half_norm_sq) (fun _ => lipschitz_id_grad)
    (fun _ y z => ?_) IsOrthProj.one zero_le_one (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hx
  have h := sq_nonneg ‖z - y‖
  have e : ‖z‖ ^ 2 = ‖y + (z - y)‖ ^ 2 := by rw [add_sub_cancel]
  rw [norm_add_sq_real] at e
  change ‖y‖ ^ 2 / 2 + ⟪y, z - y⟫ ≤ ‖z‖ ^ 2 / 2
  linarith

end FederatedConvexThreshold

end LeanDLRA
