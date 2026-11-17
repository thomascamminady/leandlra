import LeanDLRA.Training.Descent

/-!
# The step-size constant of the FeDLRT descent bound

`loss_fedRound_le` states the loss descent of one aggregated FeDLRT round (Schotthöfer–Laiu,
[SchotthoferLaiu2024, Thm. 2] and Thm 8) as
`ℒ(x⋆) ≤ ℒ(x) - s⋆ λ (1 - 12 s⋆ λ β) ‖Π ∇ℒ(x)‖²` under `λ β s⋆ ≤ 1`.  The bound is a descent
statement only for `s⋆ λ β < 1/12`.  This file replaces the constant `12` by `1`, under the same
hypotheses, shows that `1` cannot be replaced by a smaller number in a bound of this form, and
shows how far the hypothesis `λ β s⋆ ≤ 1` is from necessary.

## Notation

`A = s⋆ λ` is the length of the round, `θ = β A`, `u = λ β`, `a = ‖Π ∇ℒ(x)‖`, and
`w = fedDrift` is the averaged accumulated gradient difference, so that
`x⋆ = x - A Π ∇ℒ(x) - λ Π w` (`fedRound_eq`).

## Main results

* `norm_fedClientIter_sub_le_geom`: the client drift is bounded by a geometric sum,
  `‖z^s - x‖ ≤ λ (∑_{i<s} (1 + u)^i) a`, without a restriction on the step size.
  `norm_fedClientIter_neg_sub` shows that the bound is an equality for clients with
  gradient `z ↦ -z`.
* `norm_fedDrift_le_geom`: `‖w‖ ≤ (∑_{j<s⋆} ((1 + u)^j - 1)) a`, and `sum_pow_sub_one_le`:
  for `s u ≤ 1` the sum is at most `s (s u) (1/2 + (2/9) s u)`.
* `loss_fedRound_le_fine`: `ℒ(x⋆) ≤ ℒ(x) - A (1 - θ (1 - (5/18) θ + (1/18) θ²)) a²` for
  `θ ≤ 1`.  The cross term between the gradient step and the drift enters with the factor
  `1 - θ`, which is why no triangle inequality for `‖x⋆ - x‖` is needed.
* `loss_fedRound_le_one`: `ℒ(x⋆) ≤ ℒ(x) - A (1 - A β) a²` (the constant `12` replaced by `1`),
  and `loss_fedRound_le_two_ninths`: `ℒ(x⋆) ≤ ℒ(x) - (2/9) A a²` on the whole range
  `λ β s⋆ ≤ 1`.  `loss_truncated_fedRound_le_one` adds the truncation, and
  `exists_fedGrad_sq_le_one`, `exists_fedGrad_sq_le_of_lr_half` are the resulting convergence
  bounds, the latter with `4 β / n` at `s⋆ λ β = 1/2` (compare `exists_fedGrad_sq_le_of_lr`).
* `fedRound_constant_one_sharp`: for every `c < 1` the bound
  `ℒ(x⋆) ≤ ℒ(x) - A (1 - c A β) a²` fails for some `s⋆`, `λ` with `λ β s⋆ ≤ 1` on the quadratic
  loss with identical clients.
* `loss_le_loss_fedRound_neg`, `exists_fedRound_no_descent`: for a client with gradient `z ↦ -z`
  and a global loss with `1`-Lipschitz gradient the loss does not decrease as soon as
  `3 ≤ (1 + λ)^{s⋆}`, for example at `s⋆ = 8`, `λ β s⋆ = 6/5`.  There the global gradient is
  not the average of the client gradients; the hypotheses of `loss_fedRound_le` allow this.
-/

open Set Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section FederatedConstant

variable {ι : Type*} {ℒ : E → ℝ} {g : E → E} {gc : ι → E → E} {β lr : ℝ}
  {P : E →L[ℝ] E}

/-- Drift of the variance-corrected client iterates as a geometric sum:
`‖z^s - x‖ ≤ λ (∑_{i<s} (1 + λ β)^i) ‖Π ∇ℒ(x)‖`.  The recursion behind it is
`‖z^{s+1} - x‖ ≤ (1 + λ β) ‖z^s - x‖ + λ ‖Π ∇ℒ(x)‖`; compare `norm_fedClientIter_sub_le`, which
bounds the sum by `s (1 + λ β)^s`. -/
lemma norm_fedClientIter_sub_le_geom (hP : IsOrthProj P)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) (x : E)
    (c : ι) (s : ℕ) :
    ‖fedClientIter P gc g lr x c s - x‖ ≤
      lr * (∑ i ∈ range s, (1 + lr * β) ^ i) * ‖P (g x)‖ := by
  induction s with
  | zero => simp [fedClientIter]
  | succ s ih =>
    set z := fedClientIter P gc g lr x c s
    have h1 : fedClientIter P gc g lr x c (s + 1) - x =
        (z - x) - lr • P (gc c z - gc c x) - lr • P (g x) := by
      rw [fedClientIter_succ, map_add]
      module
    have h2 : ‖P (gc c z - gc c x)‖ ≤ β * ‖z - x‖ := (hP.norm_le _).trans (hgc c z x)
    have hb : 0 ≤ 1 + lr * β := by nlinarith
    rw [h1, geom_sum_succ]
    calc ‖(z - x) - lr • P (gc c z - gc c x) - lr • P (g x)‖
        ≤ ‖z - x‖ + lr * (β * ‖z - x‖) + lr * ‖P (g x)‖ := by
          refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
            (add_le_add le_rfl ?_)) ?_)
          · rw [norm_smul, Real.norm_of_nonneg hlr]; exact mul_le_mul_of_nonneg_left h2 hlr
          · rw [norm_smul, Real.norm_of_nonneg hlr]
      _ = (1 + lr * β) * ‖z - x‖ + lr * ‖P (g x)‖ := by ring
      _ ≤ (1 + lr * β) * (lr * (∑ i ∈ range s, (1 + lr * β) ^ i) * ‖P (g x)‖) +
            lr * ‖P (g x)‖ := by
          gcongr
      _ = lr * ((1 + lr * β) * (∑ i ∈ range s, (1 + lr * β) ^ i) + 1) * ‖P (g x)‖ := by ring

/-- Bound on the averaged drift by a geometric sum:
`‖w‖ ≤ (∑_{j<s⋆} ((1 + λ β)^j - 1)) ‖Π ∇ℒ(x)‖`, without a restriction on the step size. -/
lemma norm_fedDrift_le_geom [Fintype ι] [Nonempty ι] (hP : IsOrthProj P)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) (sstar : ℕ)
    (x : E) :
    ‖fedDrift P gc g lr sstar x‖ ≤
      (∑ j ∈ range sstar, ((1 + lr * β) ^ j - 1)) * ‖P (g x)‖ := by
  have hterm : ∀ c, ∀ j ∈ range sstar, ‖gc c (fedClientIter P gc g lr x c j) - gc c x‖ ≤
      ((1 + lr * β) ^ j - 1) * ‖P (g x)‖ := by
    intro c j _
    have h := mul_le_mul_of_nonneg_left
      (norm_fedClientIter_sub_le_geom (g := g) hP hgc hβ hlr x c j) hβ
    have hgeo := geom_sum_mul (1 + lr * β) j
    exact (hgc c _ _).trans (h.trans (le_of_eq (by linear_combination ‖P (g x)‖ * hgeo)))
  have hC : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  rw [fedDrift, norm_smul, norm_inv, Real.norm_natCast]
  calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ c, ∑ j ∈ range sstar,
        (gc c (fedClientIter P gc g lr x c j) - gc c x)‖
      ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _c : ι, ∑ j ∈ range sstar,
          ((1 + lr * β) ^ j - 1) * ‖P (g x)‖ := by
        gcongr
        exact (norm_sum_le _ _).trans (sum_le_sum fun c _ =>
          (norm_sum_le _ _).trans (sum_le_sum (hterm c)))
    _ = (∑ j ∈ range sstar, ((1 + lr * β) ^ j - 1)) * ‖P (g x)‖ := by
        rw [sum_const, card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ hC.ne', sum_mul]

/-- For `u ≥ 0` and `s u ≤ 1`:
`∑_{j<s} ((1 + u)^j - 1) ≤ s (s u) (1/2 + (2/9) s u)`.  The sum equals
`((1 + u)^s - 1 - s u) / u`, and `(1 + u)^s ≤ exp (s u) ≤ 1 + s u + (s u)²/2 + (2/9) (s u)³`. -/
lemma sum_pow_sub_one_le {u : ℝ} (hu : 0 ≤ u) {s : ℕ} (hs : s * u ≤ 1) :
    ∑ j ∈ range s, ((1 + u) ^ j - 1) ≤ s * (s * u) * (1 / 2 + 2 / 9 * (s * u)) := by
  rcases hu.eq_or_lt with h0 | hpos
  · subst h0
    simp
  · have hθ0 : 0 ≤ (s : ℝ) * u := by positivity
    have hexp : (1 + u) ^ s ≤ 1 + s * u + (s * u) ^ 2 / 2 + 2 / 9 * (s * u) ^ 3 := by
      have h1 : (1 + u) ^ s ≤ Real.exp u ^ s :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp u]) s
      have h2 : Real.exp u ^ s = Real.exp (s * u) := (Real.exp_nat_mul u s).symm
      have h3 := Real.exp_bound' hθ0 hs (n := 3) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at h3
      rw [h2] at h1
      linarith
    have hgeo := geom_sum_mul (1 + u) s
    have hsum : u * ∑ j ∈ range s, ((1 + u) ^ j - 1) = (1 + u) ^ s - 1 - s * u := by
      rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
      linear_combination hgeo
    have hrhs : u * (s * (s * u) * (1 / 2 + 2 / 9 * (s * u))) =
        (s * u) ^ 2 / 2 + 2 / 9 * (s * u) ^ 3 := by ring
    refine le_of_mul_le_mul_left ?_ hpos
    rw [hsum, hrhs]
    linarith

/-- The scalar inequality behind `loss_fedRound_le_fine`.  Here `m` stands for
`λ ⟪∇ℒ(x), Π w⟫`, `n` for `λ ‖Π w‖` and `r` for `λ ‖w‖`; the cross term `m` enters with the
factor `β A - 1 ≤ 0`, so only its lower bound `-(a r) ≤ m` is used. -/
lemma fed_descent_scalar {β A a r m n : ℝ} (hβ : 0 ≤ β) (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hθ : β * A ≤ 1) (hm : -(a * r) ≤ m) (hn0 : 0 ≤ n) (hn : n ≤ r)
    (hr : r ≤ A * (β * A) * (1 / 2 + 2 / 9 * (β * A)) * a) :
    -(A * a ^ 2 + m) + β / 2 * (A ^ 2 * a ^ 2 + 2 * (A * m) + n ^ 2) ≤
      -(A * (1 - β * A * (1 - 5 / 18 * (β * A) + 1 / 18 * (β * A) ^ 2)) * a ^ 2) := by
  have hθ0 : 0 ≤ β * A := mul_nonneg hβ hA
  have hk : (1 / 2 + 2 / 9 * (β * A)) ^ 2 ≤ 5 / 9 := by
    nlinarith [mul_nonneg hθ0 (sub_nonneg.2 hθ)]
  have s1 : 0 ≤ (1 - β * A) * (m + a * r) := mul_nonneg (sub_nonneg.2 hθ) (by linarith)
  have s2 := mul_le_mul_of_nonneg_left hr (mul_nonneg (sub_nonneg.2 hθ) ha)
  have s3 : n ^ 2 ≤ (A * (β * A) * (1 / 2 + 2 / 9 * (β * A)) * a) ^ 2 :=
    pow_le_pow_left₀ hn0 (hn.trans hr) 2
  have s4 := mul_le_mul_of_nonneg_left s3 (div_nonneg hβ zero_le_two)
  have s5 : 0 ≤ A * (β * A) * a ^ 2 *
      ((β * A) ^ 2 / 2 * (5 / 9 - (1 / 2 + 2 / 9 * (β * A)) ^ 2)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hA hθ0) (sq_nonneg a))
      (mul_nonneg (by positivity) (sub_nonneg.2 hk))
  linarith

/-- **Loss descent of the aggregated FeDLRT round, fine form** (setting of Schotthöfer–Laiu,
[SchotthoferLaiu2024, Thm. 8], before truncation; hypotheses of `loss_fedRound_le`): with `A = s⋆ λ`
and `θ = β A ≤ 1`,
`ℒ(x⋆) ≤ ℒ(x) - A (1 - θ (1 - (5/18) θ + (1/18) θ²)) ‖Π ∇ℒ(x)‖²`. -/
theorem loss_fedRound_le_fine [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {sstar : ℕ} (hs : lr * β * sstar ≤ 1)
    (x : E) :
    ℒ (fedRound P gc g lr sstar x) ≤ ℒ x - sstar * lr * (1 - β * (sstar * lr) *
      (1 - 5 / 18 * (β * (sstar * lr)) + 1 / 18 * (β * (sstar * lr)) ^ 2)) * ‖P (g x)‖ ^ 2 := by
  have hA0 : 0 ≤ (sstar : ℝ) * lr := by positivity
  have hθ : β * (sstar * lr) ≤ 1 := by
    have e : β * (sstar * lr) = lr * β * sstar := by ring
    rw [e]; exact hs
  have hsu : (sstar : ℝ) * (lr * β) ≤ 1 := by
    have e : (sstar : ℝ) * (lr * β) = lr * β * sstar := by ring
    rw [e]; exact hs
  -- the drift, measured in the step length
  have hw : lr * ‖fedDrift P gc g lr sstar x‖ ≤ sstar * lr * (β * (sstar * lr)) *
      (1 / 2 + 2 / 9 * (β * (sstar * lr))) * ‖P (g x)‖ := by
    have h := mul_le_mul_of_nonneg_left
      ((norm_fedDrift_le_geom (g := g) hP hgc hβ hlr sstar x).trans
        (mul_le_mul_of_nonneg_right (sum_pow_sub_one_le (mul_nonneg hlr hβ) hsu)
          (norm_nonneg _))) hlr
    exact h.trans (le_of_eq (by ring))
  -- the cross term and the projected drift
  have hcs : -(‖P (g x)‖ * ‖fedDrift P gc g lr sstar x‖) ≤
      ⟪g x, P (fedDrift P gc g lr sstar x)⟫ := by
    rw [← hP.symm]
    have h := abs_real_inner_le_norm (P (g x)) (fedDrift P gc g lr sstar x)
    linarith [neg_abs_le ⟪P (g x), fedDrift P gc g lr sstar x⟫]
  have hm : -(‖P (g x)‖ * (lr * ‖fedDrift P gc g lr sstar x‖)) ≤
      lr * ⟪g x, P (fedDrift P gc g lr sstar x)⟫ := by
    have h := mul_le_mul_of_nonneg_left hcs hlr
    linarith
  have hn : lr * ‖P (fedDrift P gc g lr sstar x)‖ ≤ lr * ‖fedDrift P gc g lr sstar x‖ :=
    mul_le_mul_of_nonneg_left (hP.norm_le _) hlr
  have hsc := fed_descent_scalar hβ hA0 (norm_nonneg (P (g x))) hθ hm
    (mul_nonneg hlr (norm_nonneg _)) hn hw
  -- the descent lemma with the exact square
  have hd := descent_lemma hℒ hg x (fedRound P gc g lr sstar x)
  have hdx : fedRound P gc g lr sstar x - x =
      -(((sstar : ℝ) * lr) • P (g x) + lr • P (fedDrift P gc g lr sstar x)) := by
    rw [fedRound_eq]; abel
  have h1 : ⟪g x, P (g x)⟫ = ‖P (g x)‖ ^ 2 := by rw [real_inner_comm, hP.inner_self_apply]
  have h2 : ⟪P (g x), P (fedDrift P gc g lr sstar x)⟫ =
      ⟪g x, P (fedDrift P gc g lr sstar x)⟫ := by rw [hP.inner_comp, hP.symm]
  rw [hdx, inner_neg_right, inner_add_right, inner_smul_right, inner_smul_right, norm_neg,
    norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    Real.norm_of_nonneg hA0, Real.norm_of_nonneg hlr, h1, h2] at hd
  linarith

/-- **Loss descent of the aggregated FeDLRT round with the constant one** (setting of
Schotthöfer–Laiu, [SchotthoferLaiu2024, Thm. 8], before truncation): under the hypotheses of
`loss_fedRound_le`, `ℒ(x⋆) ≤ ℒ(x) - s⋆ λ (1 - s⋆ λ β) ‖Π ∇ℒ(x)‖²`.  The loss decreases strictly
for `s⋆ λ β < 1` whenever `Π ∇ℒ(x) ≠ 0`. -/
theorem loss_fedRound_le_one [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {sstar : ℕ} (hs : lr * β * sstar ≤ 1)
    (x : E) :
    ℒ (fedRound P gc g lr sstar x) ≤
      ℒ x - sstar * lr * (1 - sstar * lr * β) * ‖P (g x)‖ ^ 2 := by
  have h := loss_fedRound_le_fine hℒ hg hgc hP hβ hlr hs x
  have hA0 : 0 ≤ (sstar : ℝ) * lr := by positivity
  have hθ0 : 0 ≤ β * (sstar * lr) := mul_nonneg hβ hA0
  have hθ : β * (sstar * lr) ≤ 1 := by
    have e : β * (sstar * lr) = lr * β * sstar := by ring
    rw [e]; exact hs
  have hq : 0 ≤ 5 / 18 - 1 / 18 * (β * (sstar * lr)) := by linarith
  have key : 0 ≤ sstar * lr * ‖P (g x)‖ ^ 2 *
      (β * (sstar * lr) * (β * (sstar * lr) * (5 / 18 - 1 / 18 * (β * (sstar * lr))))) :=
    mul_nonneg (mul_nonneg hA0 (sq_nonneg _)) (mul_nonneg hθ0 (mul_nonneg hθ0 hq))
  linarith

/-- **Uniform loss descent of the aggregated FeDLRT round**: on the whole range `λ β s⋆ ≤ 1`,
`ℒ(x⋆) ≤ ℒ(x) - (2/9) s⋆ λ ‖Π ∇ℒ(x)‖²`. -/
theorem loss_fedRound_le_two_ninths [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {sstar : ℕ} (hs : lr * β * sstar ≤ 1)
    (x : E) :
    ℒ (fedRound P gc g lr sstar x) ≤ ℒ x - 2 / 9 * (sstar * lr) * ‖P (g x)‖ ^ 2 := by
  have h := loss_fedRound_le_fine hℒ hg hgc hP hβ hlr hs x
  have hA0 : 0 ≤ (sstar : ℝ) * lr := by positivity
  have hθ : β * (sstar * lr) ≤ 1 := by
    have e : β * (sstar * lr) = lr * β * sstar := by ring
    rw [e]; exact hs
  have hq : 0 ≤ 14 - 4 * (β * (sstar * lr)) + (β * (sstar * lr)) ^ 2 := by
    linarith [sq_nonneg (β * (sstar * lr) - 2)]
  have key : 0 ≤ sstar * lr * ‖P (g x)‖ ^ 2 * ((1 - β * (sstar * lr)) *
      (14 - 4 * (β * (sstar * lr)) + (β * (sstar * lr)) ^ 2)) :=
    mul_nonneg (mul_nonneg hA0 (sq_nonneg _)) (mul_nonneg (sub_nonneg.2 hθ) hq)
  linarith

/-- **Global loss descent of FeDLRT with the constant one** (setting of Schotthöfer–Laiu,
[SchotthoferLaiu2024, Thm. 2], deterministic).  Corollary of `loss_fedRound_le_one`: a round with
aggregation and a truncation `‖x₁ - x⋆‖ ≤ ϑ` (with `‖∇ℒ‖ ≤ G` on `[x⋆, x₁]`) satisfies
`ℒ(x₁) - ℒ(x) ≤ -s⋆ λ (1 - s⋆ λ β) ‖Π ∇ℒ(x)‖² + G ϑ`. -/
theorem loss_truncated_fedRound_le_one [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {sstar : ℕ} (hs : lr * β * sstar ≤ 1)
    (x : E) {x₁ : E} {ϑ G : ℝ} (htr : ‖x₁ - fedRound P gc g lr sstar x‖ ≤ ϑ)
    (hG : ∀ w ∈ segment ℝ (fedRound P gc g lr sstar x) x₁, ‖g w‖ ≤ G) :
    ℒ x₁ ≤ ℒ x - sstar * lr * (1 - sstar * lr * β) * ‖P (g x)‖ ^ 2 + G * ϑ := by
  have h1 := loss_fedRound_le_one hℒ hg hgc hP hβ hlr hs x
  have h2 := abs_energy_sub_le hℒ hG
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG _ (left_mem_segment ℝ _ _))
  have h3 : G * ‖x₁ - fedRound P gc g lr sstar x‖ ≤ G * ϑ := mul_le_mul_of_nonneg_left htr hG0
  have h4 := (abs_le.1 h2).2
  linarith

/-- **Global convergence of FeDLRT with the constant one** (setting of Schotthöfer–Laiu,
[SchotthoferLaiu2024, Thm. 3], general learning rate). Corollary of
`loss_truncated_fedRound_le_one`: after `n > 0` rounds with round-dependent projectors `Π_k`,
`min_{k<n} ‖Π_k ∇ℒ(x_k)‖² ≤ (ℒ(x₀) - ℒ(x_n)) / (n c) + G ϑ / c` with `c = s⋆ λ (1 - s⋆ λ β) > 0`,
that is, for every learning rate with `0 < s⋆ λ β < 1`. -/
theorem exists_fedGrad_sq_le_one [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    {P : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k)) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {sstar : ℕ}
    {x : ℕ → E} {ϑ G : ℝ} (htr : ∀ k, ‖x (k + 1) - fedRound (P k) gc g lr sstar (x k)‖ ≤ ϑ)
    (hG : ∀ k, ∀ w ∈ segment ℝ (fedRound (P k) gc g lr sstar (x k)) (x (k + 1)), ‖g w‖ ≤ G)
    (hpos : 0 < sstar * lr * (1 - sstar * lr * β)) {n : ℕ} (hn : 0 < n) :
    ∃ k < n, ‖P k (g (x k))‖ ^ 2 ≤
      (ℒ (x 0) - ℒ (x n)) / (n * (sstar * lr * (1 - sstar * lr * β))) +
        G * ϑ / (sstar * lr * (1 - sstar * lr * β)) := by
  have hA0 : 0 ≤ (sstar : ℝ) * lr := by positivity
  have hs : lr * β * sstar ≤ 1 := by
    have h1 : 0 < 1 - sstar * lr * β := by
      by_contra hcon
      have := not_lt.1 hcon
      nlinarith
    linarith
  refine exists_le_of_mul_sum_le hpos hn ?_
  have hsum := sum_le_of_le_sub_add (u := fun k => ℒ (x k))
    (a := fun k => sstar * lr * (1 - sstar * lr * β) * ‖P k (g (x k))‖ ^ 2)
    (e := fun _ => G * ϑ) (fun k => by
      have := loss_truncated_fedRound_le_one hℒ hg hgc (hP k) hβ hlr hs (x k) (htr k) (hG k)
      linarith) n
  rw [← mul_sum, sum_const, card_range, nsmul_eq_mul] at hsum
  linarith

/-- **Global convergence of FeDLRT at the learning rate `s⋆ λ = 1 / (2 β)`** (setting of
Schotthöfer–Laiu, [SchotthoferLaiu2024, Thm. 3]).  Corollary of `exists_fedGrad_sq_le_one` at the
learning rate that maximises `s⋆ λ (1 - s⋆ λ β)`:
`min_{k<n} ‖Π_k ∇ℒ(x_k)‖² ≤ 4 β / n (ℒ(x₀) - ℒ(x_n)) + 4 β G ϑ`. -/
theorem exists_fedGrad_sq_le_of_lr_half [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    {P : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k)) (hβ : 0 < β) (hlr : 0 ≤ lr) {sstar : ℕ}
    (hlr2 : sstar * lr * β = 1 / 2)
    {x : ℕ → E} {ϑ G : ℝ} (htr : ∀ k, ‖x (k + 1) - fedRound (P k) gc g lr sstar (x k)‖ ≤ ϑ)
    (hG : ∀ k, ∀ w ∈ segment ℝ (fedRound (P k) gc g lr sstar (x k)) (x (k + 1)), ‖g w‖ ≤ G)
    {n : ℕ} (hn : 0 < n) :
    ∃ k < n, ‖P k (g (x k))‖ ^ 2 ≤ 4 * β / n * (ℒ (x 0) - ℒ (x n)) + 4 * β * G * ϑ := by
  have hc : (sstar : ℝ) * lr * (1 - sstar * lr * β) = 1 / (4 * β) := by
    rw [hlr2, eq_div_iff (by positivity)]; linarith
  obtain ⟨k, hk, hle⟩ := exists_fedGrad_sq_le_one hℒ hg hgc hP hβ.le hlr htr hG
    (by rw [hc]; positivity) hn
  refine ⟨k, hk, hle.trans (le_of_eq ?_)⟩
  rw [hc]
  have : (0 : ℝ) < n := Nat.cast_pos.2 hn
  field_simp

/-! ### The constant one cannot be lowered -/

/-- A lower bound for `(1 - u)ⁿ` with the exact terms up to the second order:
`1 - n u + n (n - 1) / 2 u² - n³ / 6 u³ ≤ (1 - u)ⁿ` for `0 ≤ u ≤ 1`. -/
lemma one_sub_pow_ge_cubic {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (n : ℕ) :
    1 - n * u + n * (n - 1) / 2 * u ^ 2 - n ^ 3 / 6 * u ^ 3 ≤ (1 - u) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h1 := mul_le_mul_of_nonneg_right ih (sub_nonneg.2 hu1)
    have e1 : 0 ≤ (n : ℝ) * u ^ 3 := by positivity
    have e2 : 0 ≤ u ^ 3 := by positivity
    have e3 : 0 ≤ (n : ℝ) ^ 3 * u ^ 4 := by positivity
    rw [pow_succ (1 - u) n]
    push_cast
    linarith

/-- With `Π = 1`, `∇ℒ = id` and identical clients `∇ℒ_c = id`, the client iterates of FeDLRT
are `z^s = (1 - λ)^s x`. -/
lemma fedClientIter_one_id (lr : ℝ) (x : E) (c : ι) (s : ℕ) :
    fedClientIter (1 : E →L[ℝ] E) (fun _ : ι => id) id lr x c s = (1 - lr) ^ s • x := by
  induction s with
  | zero => simp [fedClientIter]
  | succ s ih =>
    rw [fedClientIter_succ, ih]
    change (1 - lr) ^ s • x - lr • ((1 - lr) ^ s • x - x + x) = (1 - lr) ^ (s + 1) • x
    rw [sub_add_cancel, pow_succ' (1 - lr) s, mul_smul, sub_smul, one_smul]

/-- A FeDLRT round with one client, `s⋆` local steps, `Π = 1` and `∇ℒ = id` is
`x ↦ (1 - λ)^{s⋆} x`; for `s⋆ = 1` this is `fedRound_one_id_unit`. -/
lemma fedRound_one_id_unit_pow (lr : ℝ) (s : ℕ) (x : E) :
    fedRound (1 : E →L[ℝ] E) (fun _ : Unit => id) id lr s x = (1 - lr) ^ s • x := by
  simp [fedRound, fedClientIter_one_id]

/-- **The constant one of `loss_fedRound_le_one` is the smallest possible.**  For every `c < 1`
and every `x ≠ 0` there are `s⋆` and `λ > 0` with `λ β s⋆ ≤ 1` (here `β = 1`) for which the
bound `ℒ(x⋆) ≤ ℒ(x) - s⋆ λ (1 - c s⋆ λ β) ‖Π ∇ℒ(x)‖²` fails, on `ℒ = ‖·‖² / 2` with one client,
`∇ℒ_c = ∇ℒ = id` and `Π = 1`: there `x⋆ = (1 - λ)^{s⋆} x`, and `λ = 1 / s⋆²` with
`s⋆ > 2 / (1 - c)` violates the bound. -/
theorem fedRound_constant_one_sharp {c : ℝ} (hc : c < 1) {x : E} (hx : x ≠ 0) :
    ∃ (sstar : ℕ) (lr : ℝ), 0 < lr ∧ lr * 1 * sstar ≤ 1 ∧
      ‖x‖ ^ 2 / 2 - sstar * lr * (1 - c * (sstar * lr) * 1) * ‖(1 : E →L[ℝ] E) (id x)‖ ^ 2 <
        ‖fedRound (1 : E →L[ℝ] E) (fun _ : Unit => id) id lr sstar x‖ ^ 2 / 2 := by
  have hδ : 0 < 1 - c := sub_pos.2 hc
  obtain ⟨s, hs⟩ := exists_nat_gt (2 / (1 - c))
  have hσ0 : (0 : ℝ) < s := (div_pos two_pos hδ).trans hs
  have hσ1 : (1 : ℝ) ≤ s := Nat.one_le_cast.2 (Nat.succ_le_of_lt (Nat.cast_pos.1 hσ0))
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (s : ℝ)⁻¹ := ⟨_, rfl⟩
  have hσt : (s : ℝ) * t = 1 := by rw [ht]; exact mul_inv_cancel₀ hσ0.ne'
  have ht0 : 0 < t := by rw [ht]; exact inv_pos.2 hσ0
  have ht1 : t ≤ 1 := by
    have h := mul_nonneg (sub_nonneg.2 hσ1) ht0.le
    linarith
  have ht2 : 2 * t < 1 - c := by
    have h := mul_lt_mul_of_pos_left ((div_lt_iff₀ hδ).1 hs) ht0
    have e : t * ((s : ℝ) * (1 - c)) = 1 - c := by linear_combination (1 - c) * hσt
    rw [e] at h
    linarith
  -- the cubic lower bound at `u = t²`, `n = 2 s`, reduced with `s t = 1`
  have hpoly : 1 - 2 * t + 2 * t ^ 2 - 7 / 3 * t ^ 3 ≤ (1 - t ^ 2) ^ (s * 2) := by
    refine le_trans (le_of_eq ?_)
      (one_sub_pow_ge_cubic (u := t ^ 2) (by positivity) (pow_le_one₀ ht0.le ht1) (s * 2))
    push_cast
    linear_combination (2 * t - 2 * t ^ 2 * (s * t + 1) + t ^ 3 +
      4 / 3 * t ^ 3 * (s ^ 2 * t ^ 2 + s * t + 1)) * hσt
  have hgap : 0 < t ^ 2 * (2 * (1 - c) - 7 / 3 * t) := mul_pos (pow_pos ht0 2) (by linarith)
  have hlt : 1 - 2 * t + 2 * c * t ^ 2 < (1 - t ^ 2) ^ (s * 2) := by linarith
  have hN : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.2 hx) 2
  have hA : (s : ℝ) * t ^ 2 = t := by linear_combination t * hσt
  refine ⟨s, t ^ 2, pow_pos ht0 2, ?_, ?_⟩
  · have e : t ^ 2 * 1 * (s : ℝ) = t := by linear_combination t * hσt
    rw [e]; exact ht1
  · rw [fedRound_one_id_unit_pow, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← pow_mul, hA]
    change ‖x‖ ^ 2 / 2 - t * (1 - c * t * 1) * ‖x‖ ^ 2 < (1 - t ^ 2) ^ (s * 2) * ‖x‖ ^ 2 / 2
    have h := mul_lt_mul_of_pos_right hlt (half_pos hN)
    linarith

/-! ### Concave clients: the drift bound is attained and the threshold is nearly necessary

In `loss_fedRound_le` and in the statements above the client gradients `∇ℒ_c` and the global
gradient `∇ℒ` are independent data with the same Lipschitz constant.  In this setting clients
with the gradient `z ↦ -z` attain the drift bound, and they stop the descent as soon as
`(1 + λ β)^{s⋆} ≥ 3`. -/

/-- `ℒ(y) = ⟪v, y⟫ + ‖y‖² / 2` has the gradient `y ↦ v + y`. -/
lemma hasFDerivAt_inner_add_half_norm_sq (v x : E) :
    HasFDerivAt (fun y : E => ⟪v, y⟫ + ‖y‖ ^ 2 / 2) (innerSL ℝ (v + x)) x :=
  (((innerSL ℝ v).hasFDerivAt (x := x)).add (hasFDerivAt_half_norm_sq x)).congr_fderiv
    ((innerSL ℝ).map_add v x).symm

/-- With `Π = 1`, client gradients `z ↦ -z` and global gradient `y ↦ v + y`, the client
iterates of FeDLRT started at `0` are `z^s = -((1 + λ)^s - 1) v`. -/
lemma fedClientIter_neg (v : E) (lr : ℝ) (c : ι) (s : ℕ) :
    fedClientIter (1 : E →L[ℝ] E) (fun _ : ι => fun z : E => -z) (fun y => v + y) lr 0 c s =
      -(((1 + lr) ^ s - 1) • v) := by
  induction s with
  | zero => simp [fedClientIter]
  | succ s ih =>
    rw [fedClientIter_succ, ih]
    change -(((1 + lr) ^ s - 1) • v) -
      lr • (-(-(((1 + lr) ^ s - 1) • v)) - -(0 : E) + (v + 0)) = -(((1 + lr) ^ (s + 1) - 1) • v)
    rw [pow_succ (1 + lr) s]
    module

/-- **The drift bound `norm_fedClientIter_sub_le_geom` is attained**: for client gradients
`z ↦ -z` (so `β = 1`), global gradient `y ↦ v + y`, `Π = 1` and `x = 0` it is an equality, for
every number of local steps. -/
theorem norm_fedClientIter_neg_sub (v : E) {lr : ℝ} (hlr : 0 ≤ lr) (c : ι) (s : ℕ) :
    ‖fedClientIter (1 : E →L[ℝ] E) (fun _ : ι => fun z : E => -z) (fun y => v + y) lr 0 c s
        - 0‖ = lr * (∑ i ∈ range s, (1 + lr * 1) ^ i) * ‖(1 : E →L[ℝ] E) (v + 0)‖ := by
  have hE : 0 ≤ (1 + lr) ^ s - 1 := sub_nonneg.2 (one_le_pow₀ (by linarith))
  have hgeo := geom_sum_mul (1 + lr) s
  rw [fedClientIter_neg, sub_zero, norm_neg, norm_smul, Real.norm_of_nonneg hE, mul_one]
  change ((1 + lr) ^ s - 1) * ‖v‖ = lr * (∑ i ∈ range s, (1 + lr) ^ i) * ‖v + 0‖
  rw [add_zero]
  linear_combination (-‖v‖) * hgeo

/-- A FeDLRT round with one client with gradient `z ↦ -z`, global gradient `y ↦ v + y`, `Π = 1`
and start `0` ends at `-((1 + λ)^{s⋆} - 1) v`. -/
lemma fedRound_neg_unit (v : E) (lr : ℝ) (s : ℕ) :
    fedRound (1 : E →L[ℝ] E) (fun _ : Unit => fun z : E => -z) (fun y => v + y) lr s 0 =
      -(((1 + lr) ^ s - 1) • v) := by
  simp [fedRound, fedClientIter_neg]

/-- With a client gradient `z ↦ -z` and the loss `ℒ(y) = ⟪v, y⟫ + ‖y‖² / 2` (`β = 1`), a FeDLRT
round from `x = 0` does not decrease the loss as soon as `(1 + λ)^{s⋆} ≥ 3`:
`ℒ(x⋆) - ℒ(0) = ‖v‖² (q - 1) (q - 3) / 2` with `q = (1 + λ)^{s⋆}`. -/
theorem loss_le_loss_fedRound_neg (v : E) {lr : ℝ} {sstar : ℕ} (h3 : 3 ≤ (1 + lr) ^ sstar) :
    ⟪v, (0 : E)⟫ + ‖(0 : E)‖ ^ 2 / 2 ≤
      ⟪v, fedRound (1 : E →L[ℝ] E) (fun _ : Unit => fun z : E => -z) (fun y => v + y) lr sstar
        0⟫ + ‖fedRound (1 : E →L[ℝ] E) (fun _ : Unit => fun z : E => -z) (fun y => v + y) lr
          sstar 0‖ ^ 2 / 2 := by
  rw [fedRound_neg_unit, inner_zero_right, norm_zero, inner_neg_right, norm_neg, norm_smul,
    real_inner_smul_right, real_inner_self_eq_norm_sq, mul_pow, Real.norm_eq_abs, sq_abs]
  have h2 : 0 ≤ ((1 + lr) ^ sstar - 1) * ((1 + lr) ^ sstar - 3) :=
    mul_nonneg (by linarith) (by linarith)
  have h := mul_nonneg h2 (sq_nonneg ‖v‖)
  linarith

/-- **The step-size restriction of `loss_fedRound_le_one` is nearly necessary in its own
generality.**  For every `v ≠ 0` there are a loss, a global gradient and one client gradient
that satisfy all hypotheses of `loss_fedRound_le_one` with `β = 1` except the restriction
`λ β s⋆ ≤ 1`, with `Π ∇ℒ(0) ≠ 0`, for which no round with `(1 + λ)^{s⋆} ≥ 3` decreases the
loss.  The global gradient `y ↦ v + y` is not the average of the client gradient `z ↦ -z`;
the hypotheses allow this.  So, in that generality, the largest admissible `λ β s⋆` lies
between `1` and `s⋆ (3^{1/s⋆} - 1)`, which decreases to `log 3` as `s⋆` grows.  When the
global gradient is the client average, this theorem says nothing about the threshold. -/
theorem exists_fedRound_no_descent {v : E} (hv : v ≠ 0) :
    ∃ (ℒ : E → ℝ) (g : E → E) (gc : Unit → E → E),
      (∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) ∧ (∀ x y, ‖g x - g y‖ ≤ 1 * ‖x - y‖) ∧
      (∀ c x y, ‖gc c x - gc c y‖ ≤ 1 * ‖x - y‖) ∧ (1 : E →L[ℝ] E) (g 0) ≠ 0 ∧
      ∀ (lr : ℝ) (sstar : ℕ), 3 ≤ (1 + lr) ^ sstar →
        ℒ 0 ≤ ℒ (fedRound (1 : E →L[ℝ] E) gc g lr sstar 0) := by
  refine ⟨fun y => ⟪v, y⟫ + ‖y‖ ^ 2 / 2, fun y => v + y, fun _ z => -z,
    hasFDerivAt_inner_add_half_norm_sq v, fun x y => le_of_eq ?_, fun _ x y => le_of_eq ?_, ?_,
    fun lr sstar h3 => loss_le_loss_fedRound_neg v h3⟩
  · rw [add_sub_add_left_eq_sub, one_mul]
  · rw [neg_sub_neg, one_mul, norm_sub_rev]
  · change v + 0 ≠ 0
    rwa [add_zero]

/-! ### Examples: the hypotheses are jointly satisfiable -/

/-- One FeDLRT round with two identical clients and two local steps at `λ β s⋆ = 1/2` on the
quadratic loss satisfies the hypotheses of `loss_fedRound_le_one`, with a nonzero projected
gradient.  The factor `1 - 12 s⋆ λ β` of `loss_fedRound_le` is negative at this step size. -/
example {x : E} (hx : x ≠ 0) :
    ‖(1 : E →L[ℝ] E) (id x)‖ ≠ 0 ∧
      ‖fedRound (1 : E →L[ℝ] E) (fun _ : Fin 2 => id) id (1 / 4) 2 x‖ ^ 2 / 2 ≤
        ‖x‖ ^ 2 / 2 - (2 : ℕ) * (1 / 4) * (1 - (2 : ℕ) * (1 / 4) * 1) *
          ‖(1 : E →L[ℝ] E) (id x)‖ ^ 2 :=
  ⟨norm_ne_zero_iff.2 hx,
    loss_fedRound_le_one (ℒ := fun x : E => ‖x‖ ^ 2 / 2) hasFDerivAt_half_norm_sq
      lipschitz_id_grad (fun _ => lipschitz_id_grad) IsOrthProj.one zero_le_one (by norm_num)
      (by norm_num) x⟩

/-- The uniform bound `loss_fedRound_le_two_ninths` at the end `λ β s⋆ = 1` of the admissible
range, for two identical clients and two local steps on the quadratic loss. -/
example (x : E) :
    ‖fedRound (1 : E →L[ℝ] E) (fun _ : Fin 2 => id) id (1 / 2) 2 x‖ ^ 2 / 2 ≤
      ‖x‖ ^ 2 / 2 - 2 / 9 * ((2 : ℕ) * (1 / 2)) * ‖(1 : E →L[ℝ] E) (id x)‖ ^ 2 :=
  loss_fedRound_le_two_ninths (ℒ := fun x : E => ‖x‖ ^ 2 / 2) hasFDerivAt_half_norm_sq
    lipschitz_id_grad (fun _ => lipschitz_id_grad) IsOrthProj.one zero_le_one (by norm_num)
    (by norm_num) x

/-- A FeDLRT run on `ℒ = ‖·‖² / 2` with `s⋆ λ β = 1/2` that truncates to rank zero after the
first round (`x₀ = v`, `x_k = 0` for `k ≥ 1`) satisfies all hypotheses of
`exists_fedGrad_sq_le_of_lr_half`, with truncation tolerance `ϑ = ‖v‖` and gradient bound
`G = ‖v‖`. -/
example (v : E) {n : ℕ} (hn : 0 < n) :
    ∃ k < n, ‖(1 : E →L[ℝ] E) (id (if k = 0 then v else 0))‖ ^ 2 ≤
      4 * 1 / n * (‖if 0 = 0 then v else 0‖ ^ 2 / 2 - ‖if n = 0 then v else (0 : E)‖ ^ 2 / 2) +
        4 * 1 * ‖v‖ * ‖v‖ := by
  have hx : ∀ k : ℕ, ‖(if k = 0 then v else (0 : E))‖ ≤ ‖v‖ := fun k => by
    split_ifs <;> simp
  have h0 : (0 : ℝ) ≤ (1 - 1 / 2) ^ 1 := by norm_num
  have hhalf : ∀ y : E, ‖(1 - 1 / 2 : ℝ) ^ 1 • y‖ ≤ ‖y‖ := fun y => by
    rw [norm_smul, Real.norm_of_nonneg h0]
    exact mul_le_of_le_one_left (norm_nonneg y) (by norm_num)
  refine exists_fedGrad_sq_le_of_lr_half (ℒ := fun x : E => ‖x‖ ^ 2 / 2) (ι := Unit) (sstar := 1)
    (lr := 1 / 2) (x := fun k => if k = 0 then v else 0) hasFDerivAt_half_norm_sq
    lipschitz_id_grad (fun _ => lipschitz_id_grad) (fun _ => IsOrthProj.one) one_pos
    (by norm_num) (by norm_num) (fun k => ?_) (fun k w hw => ?_) hn
  · change ‖(if k + 1 = 0 then v else (0 : E)) - fedRound (1 : E →L[ℝ] E) (fun _ : Unit => id) id
      (1 / 2) 1 (if k = 0 then v else 0)‖ ≤ ‖v‖
    rw [ite_eq_right (Nat.add_one_ne_zero k), zero_sub, norm_neg, fedRound_one_id_unit_pow]
    exact (hhalf _).trans (hx k)
  · change w ∈ segment ℝ (fedRound (1 : E →L[ℝ] E) (fun _ : Unit => id) id (1 / 2) 1
      (if k = 0 then v else 0)) (if k + 1 = 0 then v else (0 : E)) at hw
    rw [ite_eq_right (Nat.add_one_ne_zero k), fedRound_one_id_unit_pow] at hw
    have hball : segment ℝ ((1 - 1 / 2 : ℝ) ^ 1 • (if k = 0 then v else (0 : E))) 0 ⊆
        Metric.closedBall (0 : E) ‖v‖ := by
      refine (convex_closedBall (0 : E) ‖v‖).segment_subset ?_ ?_
      · rw [mem_closedBall_zero_iff]
        exact (hhalf _).trans (hx k)
      · rw [mem_closedBall_zero_iff, norm_zero]
        exact norm_nonneg v
    exact mem_closedBall_zero_iff.1 (hball hw)

/-- `fedRound_constant_one_sharp` on the real line with `c = 1/2`. -/
example : ∃ (sstar : ℕ) (lr : ℝ), 0 < lr ∧ lr * 1 * sstar ≤ 1 ∧
    ‖(1 : ℝ)‖ ^ 2 / 2 - sstar * lr * (1 - 1 / 2 * (sstar * lr) * 1) *
      ‖(1 : ℝ →L[ℝ] ℝ) (id 1)‖ ^ 2 <
      ‖fedRound (1 : ℝ →L[ℝ] ℝ) (fun _ : Unit => id) id lr sstar 1‖ ^ 2 / 2 :=
  fedRound_constant_one_sharp (by norm_num) one_ne_zero

/-- No descent at `s⋆ = 8`, `λ = 3/20`, that is `λ β s⋆ = 6/5`: there `(23/20)^8 ≥ 3`. -/
example (v : E) :
    ⟪v, (0 : E)⟫ + ‖(0 : E)‖ ^ 2 / 2 ≤
      ⟪v, fedRound (1 : E →L[ℝ] E) (fun _ : Unit => fun z : E => -z) (fun y => v + y) (3 / 20) 8
        0⟫ + ‖fedRound (1 : E →L[ℝ] E) (fun _ : Unit => fun z : E => -z) (fun y => v + y)
          (3 / 20) 8 0‖ ^ 2 / 2 :=
  loss_le_loss_fedRound_neg v (by norm_num)

end FederatedConstant

end LeanDLRA
