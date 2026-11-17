import LeanDLRA.Research.FederatedThreeSteps
import LeanDLRA.Research.FederatedTwoSteps

/-!
# FeDLRT with averaged gradients: descent for every number of local steps

One aggregated round of FeDLRT with variance correction ([SchotthoferLaiu2024], before
truncation) is `fedRound`: `s⋆` local steps of length `λ` on every client, then the average.
This file treats the setting of the paper, in which the global loss is the average of the
client losses, for convex client losses with `β`-Lipschitz gradients and an arbitrary number
of local steps: the round decreases the loss as soon as `s⋆ λ β < 4` and `s⋆ ≥ 2`.

## Notation

`u = λ β`. For a client `c` let `h_c(y) = ℒ_c(y) - ⟪∇ℒ_c(x) - ∇ℒ(x), y⟫`; the local steps are
projected gradient steps of `h_c`, and the average of the `h_c` is `ℒ`. `z_c` is the last local
iterate, `G_j = Π ∇h_c(z_c^j)` (so `G_0 = Π ∇ℒ(x)`), and `x⋆` is the average of the `z_c`.

## Main results

* `add_sum_norm_sq_proj_le_of_convex`: `s` projected gradient steps with `λ β ≤ 1` on a convex
  function satisfy `f(z^s) + λ ∑_{j<s} ‖G_j‖² + (λ/2) ‖G_s‖² ≤ f(z^0) + (λ/2) ‖G_0‖²`.
* `loss_fedRound_le_of_convex_of_mul_le_four`: for `λ β ≤ 1` and `s⋆ λ β ≤ 4`, `s⋆ ≥ 1`,
  `ℒ(x⋆) ≤ ℒ(x) - λ (243 + 189u - 222u² - 164u³) / ((9 + 8u) (9 + 11u)²) ‖Π ∇ℒ(x)‖²`.
* `loss_fedRound_lt_of_convex_of_mul_lt_four`: `ℒ(x⋆) < ℒ(x)` for every `s⋆ ≥ 2`, `0 < λ`,
  `s⋆ λ β < 4` and `Π ∇ℒ(x) ≠ 0`.

## Remarks on the hypotheses

* The proof for `λ β ≤ 1` uses three points per client, `x`, `z_c` and `x⋆`, whatever the
  number of local steps: the gradient inequalities for the pairs `x → x⋆`, `z_c → x⋆` and
  `z_c → x`, the inequality of the first item, the bound `‖z_c - x‖² ≤ s⋆ λ² ∑_{j<s⋆} ‖G_j‖²`
  and `‖G_0‖² ≤ ∑_{j<s⋆} ‖G_j‖²`. The weighted sum of the six is a sum of squares of the
  deviations from the client averages, a sum of squares of the averages, a multiple of
  `‖Π ∇ℒ(x)‖²`, and terms that are linear in the deviations and vanish in the average.
* The constant is not the best one. As `λ β → 0` it tends to `λ / 3`.
* `s⋆ = 1` is excluded in the last item: the round is then one projected gradient step, which
  decreases the loss for `λ β < 2`. For `s⋆ = 2` and `s⋆ = 3` the last item follows from
  `loss_fedRound_two_lt` and `loss_fedRound_three_lt_of_convex_of_le`; there `λ β` may
  exceed `1`.
* The condition `s⋆ λ β < 4` is sufficient, not necessary: for `s⋆ = 3` the round decreases
  the loss up to `s⋆ λ β < 45/8` (`loss_fedRound_three_lt_of_convex`).
* Without the hypothesis that the global gradient is the average of the client gradients the
  condition for convex clients is `s⋆ λ β < 2` (`loss_fedRound_lt_of_convex_of_lr_mul_le_one`,
  `loss_le_loss_fedRound_zero`).
* The clients are averaged with equal weights, as in `fedRound`.
-/

open Set Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section FederatedManySteps

variable {ι : Type*} {ℒ : E → ℝ} {g : E → E} {gc : ι → E → E} {ℒc : ι → E → ℝ} {β lr : ℝ}
  {P : E →L[ℝ] E}

/-- **Projected gradient steps on a convex function with Lipschitz gradient.** If `f` is convex
(in the form of the gradient inequality), its gradient is `β`-Lipschitz, `0 ≤ λ`, `λ β ≤ 1` and
`z^{j+1} = z^j - λ Π ∇f(z^j)` for an orthogonal projector `Π`, then with `G_j = Π ∇f(z^j)`
`f(z^s) + λ ∑_{j<s} ‖G_j‖² + (λ/2) ‖G_s‖² ≤ f(z^0) + (λ/2) ‖G_0‖²`. -/
lemma add_sum_norm_sq_proj_le_of_convex {f : E → ℝ} {gf : E → E}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (gf y)) y)
    (hgf : ∀ y z, ‖gf y - gf z‖ ≤ β * ‖y - z‖)
    (hconv : ∀ y z, f y + ⟪gf y, z - y⟫ ≤ f z) (hP : IsOrthProj P) (hlr : 0 ≤ lr)
    (hlrβ : lr * β ≤ 1) {z : ℕ → E} (hz : ∀ j, z (j + 1) = z j - lr • P (gf (z j))) (s : ℕ) :
    f (z s) + lr * ∑ j ∈ range s, ‖P (gf (z j))‖ ^ 2 + lr / 2 * ‖P (gf (z s))‖ ^ 2 ≤
      f (z 0) + lr / 2 * ‖P (gf (z 0))‖ ^ 2 := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h1 := add_inner_add_norm_sq_le_of_convex hf hgf hconv hlr hlrβ (z (s + 1)) (z s)
    have e1 : z s - z (s + 1) = lr • P (gf (z s)) := by rw [hz, sub_sub_cancel]
    have e2 : ⟪gf (z (s + 1)), P (gf (z s))⟫ = ⟪P (gf (z (s + 1))), P (gf (z s))⟫ := by
      rw [hP.symm, hP.idem]
    have e3 : ‖P (gf (z s)) - P (gf (z (s + 1)))‖ ^ 2 ≤ ‖gf (z s) - gf (z (s + 1))‖ ^ 2 := by
      rw [← map_sub]
      exact pow_le_pow_left₀ (norm_nonneg _) (hP.norm_le _) 2
    have e4 := mul_le_mul_of_nonneg_left e3 (div_nonneg hlr zero_le_two)
    rw [norm_sub_sq_real] at e4
    rw [e1, inner_smul_right, e2, real_inner_comm (P (gf (z s))) (P (gf (z (s + 1))))] at h1
    rw [sum_range_succ]
    linarith

/-- **The certificate for one client and any number of local steps.** `D`, `q`, `G` stand for
`β (x - z_c)`, `Π ∇h_c(x⋆)`, `Π ∇h_c(z_c)` of one client, `Dm`, `qm`, `Gm` for their averages
over the clients and `m` for `Π ∇ℒ(x)`; `u = λ β`. The weighted sum of the remainders of the six
inequalities is bounded below by a multiple of `‖m‖²` plus terms that are linear in the
deviations from the averages; the difference is a sum of six squares. -/
lemma fedMany_client_form_ge (D q G Dm qm Gm m : E) {u : ℝ} (hu0 : 0 ≤ u) :
    2 * u * (243 + 189 * u - 222 * u ^ 2 - 164 * u ^ 3) * ‖m‖ ^ 2
      + (⟪D - Dm, -((9 + 8 * u) * (9 + 11 * u) ^ 2) • qm
            - ((9 + 8 * u) * (9 + 11 * u) * (9 + 5 * u)) • m
            + (2 * ((3 + 2 * u) * (9 + 11 * u) ^ 2)) • Dm⟫
        + ⟪q - qm, ((9 + 8 * u) * (9 + 11 * u) ^ 2) • Dm
            + ((9 + 8 * u) * (9 + 11 * u) ^ 2) • (qm - m)
            + ((9 + 8 * u) * (9 + 11 * u) ^ 2) • (qm - Gm)⟫
        + ⟪G - Gm, ((9 + 8 * u) * (9 + 11 * u) ^ 2) • (Gm - qm)
            + ((9 + 8 * u) * (9 + 11 * u) * (9 + 5 * u)) • (Gm - m)
            + (2 * (9 + 8 * u) ^ 2 * (9 + 11 * u) * u) • Gm⟫) ≤
      (9 + 8 * u) * (9 + 11 * u) ^ 2 * (⟪q, Dm⟫ + 1 / 2 * ‖m - q‖ ^ 2)
        + (9 + 8 * u) * (9 + 11 * u) ^ 2 * (⟪q, Dm - D⟫ + 1 / 2 * ‖G - q‖ ^ 2)
        + (9 + 8 * u) * (9 + 11 * u) * (9 + 5 * u) * (-⟪m, D⟫ + 1 / 2 * ‖G - m‖ ^ 2)
        + 2 * (9 + 8 * u) ^ 2 * (9 + 11 * u) * (-(u / 2) * (‖m‖ ^ 2 - ‖G‖ ^ 2))
        + (3 + 2 * u) * (9 + 11 * u) ^ 2 * ‖D‖ ^ 2
        + 2 * (9 + 11 * u) * (27 + 42 * u + 20 * u ^ 2) * (u * ‖m‖ ^ 2) := by
  have hA1 : 0 ≤ 9 + 8 * u := by linarith
  have hA2 : 0 ≤ 9 + 11 * u := by linarith
  have hB : 0 ≤ 3 + 2 * u := by linarith
  have hU : 0 ≤ 8 * (9 + 8 * u) * (3 + 2 * u) * (9 + 11 * u) * u ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA1) hB) hA2) (sq_nonneg u)
  have h1 := real_inner_self_nonneg
    (x := (2 * (3 + 2 * u)) • (D - Dm) - (9 + 8 * u) • (q - qm))
  have h2 := real_inner_self_nonneg
    (x := (3 : ℝ) • (q - qm) - (2 * (3 + 2 * u)) • (G - Gm))
  have h3 := real_inner_self_nonneg (x := G - Gm)
  have h4 := real_inner_self_nonneg
    (x := (2 * (3 + 2 * u) * (9 + 11 * u)) • Dm + ((9 + 8 * u) * (9 + 11 * u)) • (qm - m)
      + (6 * u * (9 + 8 * u)) • m)
  have h5 := real_inner_self_nonneg
    (x := (3 * (9 + 11 * u)) • (qm - m) - (2 * (3 + 2 * u) * (9 + 11 * u)) • (Gm - m)
      - (6 * (9 + 8 * u) * u) • m)
  have h6 := real_inner_self_nonneg (x := Gm - m)
  have h := add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (sq_nonneg (9 + 11 * u))) h1)
    (mul_nonneg (mul_nonneg hA1 (sq_nonneg (9 + 11 * u))) h2)) (mul_nonneg hU h3))
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) h4)) (mul_nonneg hA1 h5)) (mul_nonneg hU h6)
  rw [← sub_nonneg]
  refine nonneg_of_mul_nonneg_right ?_ (by linarith : (0 : ℝ) < 12 * (3 + 2 * u))
  convert h using 1
  simp only [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm D q, real_inner_comm D Dm, real_inner_comm D qm,
    real_inner_comm D m, real_inner_comm q G, real_inner_comm q Dm, real_inner_comm q qm,
    real_inner_comm q Gm, real_inner_comm q m, real_inner_comm G qm, real_inner_comm G Gm,
    real_inner_comm G m, real_inner_comm Dm qm, real_inner_comm Dm m, real_inner_comm qm Gm,
    real_inner_comm qm m, real_inner_comm Gm m]
  ring

/-- **Loss descent of the FeDLRT round with averaged convex clients for any number of local
steps.** Let the global loss be the average of the client losses, let every client loss be
convex (in the form of the gradient inequality) with a `β`-Lipschitz gradient, and let `0 ≤ λ`,
`u = λ β ≤ 1`, `s⋆ ≥ 1` and `s⋆ λ β ≤ 4`. Then
`ℒ(x⋆) ≤ ℒ(x) - λ (243 + 189u - 222u² - 164u³) / ((9 + 8u) (9 + 11u)²) ‖Π ∇ℒ(x)‖²`. -/
theorem loss_fedRound_le_of_convex_of_mul_le_four [Fintype ι] [Nonempty ι]
    (hℒc : ∀ c x, HasFDerivAt (ℒc c) (innerSL ℝ (gc c x)) x)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hconv : ∀ c x y, ℒc c x + ⟪gc c x, y - x⟫ ≤ ℒc c y)
    (hP : IsOrthProj P) (hβ : 0 < β)
    (hℒmean : ∀ y, ℒ y = (Fintype.card ι : ℝ)⁻¹ * ∑ c, ℒc c y)
    (hmean : ∀ y, g y = (Fintype.card ι : ℝ)⁻¹ • ∑ c, gc c y) (hlr : 0 ≤ lr)
    (hlrβ : lr * β ≤ 1) {sstar : ℕ} (hs0 : 0 < sstar) (hs : lr * β * sstar ≤ 4) (x : E) :
    ℒ (fedRound P gc g lr sstar x) ≤ ℒ x - lr * ((243 + 189 * (lr * β) - 222 * (lr * β) ^ 2
        - 164 * (lr * β) ^ 3) / ((9 + 8 * (lr * β)) * (9 + 11 * (lr * β)) ^ 2))
          * ‖P (g x)‖ ^ 2 := by
  have hC : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = lr * β := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; exact mul_nonneg hlr hβ.le
  have hus : u * sstar ≤ 4 := by rw [hu]; exact hs
  -- the client losses with the correction term, their gradients, and the iterates
  obtain ⟨hc, hhc⟩ : ∃ hc : ι → E → ℝ, ∀ k y, hc k y = ℒc k y - ⟪gc k x - g x, y⟫ :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨gh, hgh⟩ : ∃ gh : ι → E → E, ∀ k y, gh k y = gc k y - gc k x + g x :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ι → ℕ → E, ∀ k j, z k j = fedClientIter P gc g lr x k j :=
    ⟨_, fun _ _ => rfl⟩
  have hD : ∀ k y, HasFDerivAt (hc k) (innerSL ℝ (gh k y)) y := by
    intro k y
    have e : hc k = fun y => ℒc k y - ⟪gc k x - g x, y⟫ := funext (hhc k)
    have e2 : gc k y - (gc k x - g x) = gh k y := by rw [hgh]; abel
    rw [e]
    refine ((hℒc k y).fun_sub ((innerSL ℝ (gc k x - g x)).hasFDerivAt (x := y))).congr_fderiv ?_
    rw [← e2]
    simp only [map_sub]
  have hLip : ∀ k y w, ‖gh k y - gh k w‖ ≤ β * ‖y - w‖ := by
    intro k y w
    rw [hgh, hgh, add_sub_add_right_eq_sub, sub_sub_sub_cancel_right]
    exact hgc k y w
  have hcv : ∀ k y w, hc k y + ⟪gh k y, w - y⟫ ≤ hc k w := by
    intro k y w
    have h := hconv k y w
    rw [inner_sub_right] at h
    rw [hhc, hhc, hgh]
    simp only [inner_add_left, inner_sub_left, inner_sub_right]
    linarith
  have hsum : ∀ y, ∑ k, hc k y = (Fintype.card ι : ℝ) * ℒ y := by
    intro y
    simp_rw [hhc]
    rw [sum_sub_distrib, ← sum_inner, sum_sub_distrib, sum_const, card_univ,
      ← Nat.cast_smul_eq_nsmul ℝ, hmean x, smul_smul, mul_inv_cancel₀ hC.ne', one_smul, sub_self,
      inner_zero_left, sub_zero, hℒmean y, mul_inv_cancel_left₀ hC.ne']
  have hz0 : ∀ k, z k 0 = x := fun k => by rw [hz]; rfl
  have hzs : ∀ k j, z k (j + 1) = z k j - lr • P (gh k (z k j)) := by
    intro k j
    rw [hz, hz, hgh]
    exact fedClientIter_succ P gc g lr x k j
  -- names for the vectors of the certificate
  obtain ⟨m, hm⟩ : ∃ m : E, m = P (g x) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ι → E, ∀ k, Q k = ∑ j ∈ range sstar, P (gh k (z k j)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ι → ℝ, ∀ k, S k = ∑ j ∈ range sstar, ‖P (gh k (z k j))‖ ^ 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ι → E, ∀ k, G k = P (gh k (z k sstar)) := ⟨_, fun _ => rfl⟩
  obtain ⟨xs, hxs⟩ : ∃ xs : E, xs = fedRound P gc g lr sstar x := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ι → E, ∀ k, q k = P (gh k xs) := ⟨_, fun _ => rfl⟩
  obtain ⟨Qm, hQm⟩ : ∃ Qm : E, Qm = (Fintype.card ι : ℝ)⁻¹ • ∑ k, Q k := ⟨_, rfl⟩
  obtain ⟨qm, hqm⟩ : ∃ qm : E, qm = (Fintype.card ι : ℝ)⁻¹ • ∑ k, q k := ⟨_, rfl⟩
  obtain ⟨Gm, hGm⟩ : ∃ Gm : E, Gm = (Fintype.card ι : ℝ)⁻¹ • ∑ k, G k := ⟨_, rfl⟩
  obtain ⟨D, hDd⟩ : ∃ D : ι → E, ∀ k, D k = u • Q k := ⟨_, fun _ => rfl⟩
  obtain ⟨Dm, hDm⟩ : ∃ Dm : E, Dm = u • Qm := ⟨_, rfl⟩
  have hm0 : ∀ k, P (gh k x) = m := fun k => by rw [hgh, sub_self, zero_add, hm]
  have hSnn : ∀ k, 0 ≤ S k := fun k => by rw [hS]; exact sum_nonneg fun j _ => sq_nonneg _
  have hSm : ∀ k, ‖m‖ ^ 2 ≤ S k := by
    intro k
    have h := single_le_sum (f := fun j => ‖P (gh k (z k j))‖ ^ 2) (fun j _ => sq_nonneg _)
      (mem_range.2 hs0)
    simp only [hz0, hm0] at h
    rw [hS]
    exact h
  -- the last local iterates and the result of the round
  have hzk : ∀ k, z k sstar = x - lr • Q k := by
    intro k
    have h := fedClientIter_sub_eq_sum P gc g lr x k sstar
    have h2 : z k sstar - x = -(lr • Q k) := by
      rw [hQ, hz]
      simp only [hgh, hz]
      exact h
    rw [sub_eq_iff_eq_add] at h2
    rw [h2]
    abel
  have hSQ : ∑ k, Q k = (Fintype.card ι : ℝ) • Qm := by
    rw [hQm, smul_smul, mul_inv_cancel₀ hC.ne', one_smul]
  have hxsQ : xs = x - lr • Qm := by
    have h := fedRound_sub_eq P gc g lr sstar x
    have e : ∑ c, (fedClientIter P gc g lr x c sstar - x) = -(lr • ∑ c, Q c) := by
      rw [smul_sum, ← sum_neg_distrib]
      exact sum_congr rfl fun k _ => by rw [← hz, hzk]; abel
    rw [← hxs, e, sub_eq_iff_eq_add] at h
    rw [h, hQm, smul_neg, smul_comm (Fintype.card ι : ℝ)⁻¹ lr]
    abel
  have PQ : ∀ k, P (Q k) = Q k := by
    intro k
    rw [hQ, map_sum]
    exact sum_congr rfl fun j _ => hP.idem _
  have PQm : P Qm = Qm := by
    rw [hQm, map_smul, map_sum]
    simp_rw [PQ]
  -- sums of the client vectors
  have hSD : ∑ k, D k = (Fintype.card ι : ℝ) • Dm := by
    simp_rw [hDd]
    rw [← smul_sum, hSQ, hDm, smul_comm]
  have hSq : ∑ k, q k = (Fintype.card ι : ℝ) • qm := by
    rw [hqm, smul_smul, mul_inv_cancel₀ hC.ne', one_smul]
  have hSG : ∑ k, G k = (Fintype.card ι : ℝ) • Gm := by
    rw [hGm, smul_smul, mul_inv_cancel₀ hC.ne', one_smul]
  -- weights
  have hA1 : 0 ≤ 9 + 8 * u := by linarith
  have hA2 : 0 ≤ 9 + 11 * u := by linarith
  have hw1 : 0 ≤ (9 + 8 * u) * (9 + 11 * u) ^ 2 := mul_nonneg hA1 (sq_nonneg _)
  have hw3 : 0 ≤ (9 + 8 * u) * (9 + 11 * u) * (9 + 5 * u) :=
    mul_nonneg (mul_nonneg hA1 hA2) (by linarith)
  have hw4 : 0 ≤ 2 * (9 + 8 * u) ^ 2 * (9 + 11 * u) :=
    mul_nonneg (mul_nonneg zero_le_two (sq_nonneg _)) hA2
  have hw5 : 0 ≤ (3 + 2 * u) * (9 + 11 * u) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hw6 : 0 ≤ 2 * (9 + 11 * u) * (27 + 42 * u + 20 * u ^ 2) :=
    mul_nonneg (mul_nonneg zero_le_two hA2) (by nlinarith [sq_nonneg u])
  -- the weighted inequalities of one client
  have hcl : ∀ k, 2 * u * (243 + 189 * u - 222 * u ^ 2 - 164 * u ^ 3) * ‖m‖ ^ 2
      + (⟪D k - Dm, -((9 + 8 * u) * (9 + 11 * u) ^ 2) • qm
            - ((9 + 8 * u) * (9 + 11 * u) * (9 + 5 * u)) • m
            + (2 * ((3 + 2 * u) * (9 + 11 * u) ^ 2)) • Dm⟫
        + ⟪q k - qm, ((9 + 8 * u) * (9 + 11 * u) ^ 2) • Dm
            + ((9 + 8 * u) * (9 + 11 * u) ^ 2) • (qm - m)
            + ((9 + 8 * u) * (9 + 11 * u) ^ 2) • (qm - Gm)⟫
        + ⟪G k - Gm, ((9 + 8 * u) * (9 + 11 * u) ^ 2) • (Gm - qm)
            + ((9 + 8 * u) * (9 + 11 * u) * (9 + 5 * u)) • (Gm - m)
            + (2 * (9 + 8 * u) ^ 2 * (9 + 11 * u) * u) • Gm⟫)
      ≤ 2 * ((9 + 8 * u) * (9 + 11 * u) ^ 2) * β * (hc k x - hc k xs) := by
    intro k
    have I1 := mul_add_inner_proj_add_norm_sq_le_of_convex (lr := lr) (hD k) (hLip k) (hcv k)
      hP hβ (y := xs) (z := x) PQm (by rw [hxsQ, sub_sub_cancel])
    have I2 := mul_add_inner_proj_add_norm_sq_le_of_convex (lr := lr) (hD k) (hLip k) (hcv k)
      hP hβ (y := xs) (z := z k sstar) (v := Qm - Q k) (by rw [map_sub, PQm, PQ])
      (by rw [hzk, hxsQ]; module)
    have I3 := mul_add_inner_proj_add_norm_sq_le_of_convex (lr := lr) (hD k) (hLip k) (hcv k)
      hP hβ (y := x) (z := z k sstar) (v := -Q k) (by rw [map_neg, PQ])
      (by rw [hzk]; module)
    have c1 : lr * β * ⟪q k, Qm⟫ = ⟪q k, Dm⟫ := by rw [hDm, inner_smul_right, hu]
    have c2 : lr * β * ⟪q k, Qm - Q k⟫ = ⟪q k, Dm - D k⟫ := by
      rw [hDm, hDd, ← smul_sub, inner_smul_right, hu]
    have c3 : lr * β * ⟪m, -Q k⟫ = -⟪m, D k⟫ := by
      rw [hDd, inner_neg_right, inner_smul_right, hu, mul_neg]
    rw [← hq, hm0, c1] at I1
    rw [← hq, ← hG, c2] at I2
    rw [← hG, hm0, c3] at I3
    have hA := add_sum_norm_sq_proj_le_of_convex (hD k) (hLip k) (hcv k) hP hlr hlrβ (hzs k)
      sstar
    rw [← hS, ← hG, hz0, hm0] at hA
    have I4 : β * hc k (z k sstar) + u * S k + u / 2 * ‖G k‖ ^ 2 ≤
        β * hc k x + u / 2 * ‖m‖ ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hA hβ.le
      rw [hu]
      linarith
    have I5 : ‖D k‖ ^ 2 ≤ 4 * (u * S k) := by
      have h := norm_sq_fedClientIter_sub_le P gc g lr x k sstar
      have eS : ∑ j ∈ range sstar, ‖P (gc k (fedClientIter P gc g lr x k j) - gc k x + g x)‖ ^ 2
          = S k := by
        rw [hS]
        exact sum_congr rfl fun j _ => by rw [hgh, hz]
      rw [eS, ← hz, hzk, sub_sub_cancel_left, norm_neg] at h
      have a1 : ‖D k‖ ^ 2 = β ^ 2 * ‖lr • Q k‖ ^ 2 := by
        rw [hDd, hu, mul_comm lr β, ← smul_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have a2 := mul_le_mul_of_nonneg_left h (sq_nonneg β)
      have a3 : β ^ 2 * (lr ^ 2 * (sstar * S k)) = u * sstar * (u * S k) := by
        rw [hu]
        ring
      have a4 := mul_le_mul_of_nonneg_right hus (mul_nonneg hu0 (hSnn k))
      linarith
    have I6 : u * ‖m‖ ^ 2 ≤ u * S k := mul_le_mul_of_nonneg_left (hSm k) hu0
    have t1 := mul_le_mul_of_nonneg_left I1 hw1
    have t2 := mul_le_mul_of_nonneg_left I2 hw1
    have t3 := mul_le_mul_of_nonneg_left I3 hw3
    have t4 := mul_le_mul_of_nonneg_left I4 hw4
    have t5 := mul_le_mul_of_nonneg_left I5 hw5
    have t6 := mul_le_mul_of_nonneg_left I6 hw6
    have hk := fedMany_client_form_ge (D k) (q k) (G k) Dm qm Gm m hu0
    linarith
  -- the terms that are linear in the deviations vanish in the sum over the clients
  have zD : ∀ n : E, ∑ k, ⟪D k - Dm, n⟫ = 0 := fun n => by
    rw [← sum_inner, sum_sub_distrib, hSD, sum_const, card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
      sub_self, inner_zero_left]
  have zq : ∀ n : E, ∑ k, ⟪q k - qm, n⟫ = 0 := fun n => by
    rw [← sum_inner, sum_sub_distrib, hSq, sum_const, card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
      sub_self, inner_zero_left]
  have zG : ∀ n : E, ∑ k, ⟪G k - Gm, n⟫ = 0 := fun n => by
    rw [← sum_inner, sum_sub_distrib, hSG, sum_const, card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
      sub_self, inner_zero_left]
  have hall := sum_le_sum fun k (_ : k ∈ (univ : Finset ι)) => hcl k
  simp only [sum_add_distrib, zD, zq, zG, add_zero, sum_const, card_univ, nsmul_eq_mul,
    ← mul_sum, sum_sub_distrib] at hall
  rw [hsum x, hsum xs] at hall
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = 243 + 189 * u - 222 * u ^ 2 - 164 * u ^ 3 := ⟨_, rfl⟩
  obtain ⟨Dn, hDn⟩ : ∃ Dn : ℝ, Dn = (9 + 8 * u) * (9 + 11 * u) ^ 2 := ⟨_, rfl⟩
  have hDnpos : 0 < Dn := by
    rw [hDn]
    exact mul_pos (by linarith) (pow_pos (by linarith) 2)
  rw [← hW, ← hDn] at hall
  have h1 : 2 * u * W * ‖m‖ ^ 2 ≤ 2 * Dn * β * (ℒ x - ℒ xs) := by
    have h : (Fintype.card ι : ℝ) * (2 * u * W * ‖m‖ ^ 2) ≤
        (Fintype.card ι : ℝ) * (2 * Dn * β * (ℒ x - ℒ xs)) := by
      linarith
    exact le_of_mul_le_mul_left h hC
  rw [hu] at h1
  rw [← hu, ← hW, ← hDn, ← hxs, ← hm]
  have h3 : lr * (W / Dn) * ‖m‖ ^ 2 ≤ ℒ x - ℒ xs := by
    rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ hDnpos]
    have h : β * (lr * W * ‖m‖ ^ 2) ≤ β * ((ℒ x - ℒ xs) * Dn) := by linarith
    exact le_of_mul_le_mul_left h hβ
  linarith

/-- **The FeDLRT round with averaged convex clients decreases the loss when `λ β ≤ 1` and
`s⋆ λ β ≤ 4`**, for every number `s⋆ ≥ 1` of local steps, if the projected gradient does not
vanish. -/
theorem loss_fedRound_lt_of_convex_of_mul_le_four [Fintype ι] [Nonempty ι]
    (hℒc : ∀ c x, HasFDerivAt (ℒc c) (innerSL ℝ (gc c x)) x)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hconv : ∀ c x y, ℒc c x + ⟪gc c x, y - x⟫ ≤ ℒc c y)
    (hP : IsOrthProj P) (hβ : 0 < β)
    (hℒmean : ∀ y, ℒ y = (Fintype.card ι : ℝ)⁻¹ * ∑ c, ℒc c y)
    (hmean : ∀ y, g y = (Fintype.card ι : ℝ)⁻¹ • ∑ c, gc c y) (hlr : 0 < lr)
    (hlrβ : lr * β ≤ 1) {sstar : ℕ} (hs0 : 0 < sstar) (hs : lr * β * sstar ≤ 4) {x : E}
    (hx : P (g x) ≠ 0) :
    ℒ (fedRound P gc g lr sstar x) < ℒ x := by
  have h := loss_fedRound_le_of_convex_of_mul_le_four hℒc hgc hconv hP hβ hℒmean hmean hlr.le
    hlrβ hs0 hs x
  have hu0 : 0 ≤ lr * β := mul_nonneg hlr.le hβ.le
  have h2 : (lr * β) ^ 2 ≤ lr * β := by nlinarith
  have h3 : (lr * β) ^ 3 ≤ (lr * β) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (lr * β)) (sub_nonneg.2 hlrβ)]
  have hN : 0 < 243 + 189 * (lr * β) - 222 * (lr * β) ^ 2 - 164 * (lr * β) ^ 3 := by linarith
  have hDn : 0 < (9 + 8 * (lr * β)) * (9 + 11 * (lr * β)) ^ 2 :=
    mul_pos (by linarith) (pow_pos (by linarith) 2)
  have hpos : 0 < lr * ((243 + 189 * (lr * β) - 222 * (lr * β) ^ 2 - 164 * (lr * β) ^ 3)
      / ((9 + 8 * (lr * β)) * (9 + 11 * (lr * β)) ^ 2)) * ‖P (g x)‖ ^ 2 :=
    mul_pos (mul_pos hlr (div_pos hN hDn)) (pow_pos (norm_pos_iff.2 hx) 2)
  linarith

/-- **The FeDLRT round with averaged convex clients decreases the loss when `s⋆ λ β < 4`**, for
every number `s⋆ ≥ 2` of local steps: the global loss is the average of the client losses, every
client loss is convex (in the form of the gradient inequality) with a `β`-Lipschitz gradient,
`0 < λ`, and the projected gradient does not vanish. For `s⋆ = 2` and `s⋆ = 3` this is
`loss_fedRound_two_lt` and `loss_fedRound_three_lt_of_convex_of_le`. -/
theorem loss_fedRound_lt_of_convex_of_mul_lt_four [Fintype ι] [Nonempty ι]
    (hℒc : ∀ c x, HasFDerivAt (ℒc c) (innerSL ℝ (gc c x)) x)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hconv : ∀ c x y, ℒc c x + ⟪gc c x, y - x⟫ ≤ ℒc c y)
    (hP : IsOrthProj P) (hβ : 0 < β)
    (hℒmean : ∀ y, ℒ y = (Fintype.card ι : ℝ)⁻¹ * ∑ c, ℒc c y)
    (hmean : ∀ y, g y = (Fintype.card ι : ℝ)⁻¹ • ∑ c, gc c y) (hlr : 0 < lr) {sstar : ℕ}
    (hs2 : 2 ≤ sstar) (hs : lr * β * sstar < 4) {x : E} (hx : P (g x) ≠ 0) :
    ℒ (fedRound P gc g lr sstar x) < ℒ x := by
  have hC : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hu0 : 0 ≤ lr * β := mul_nonneg hlr.le hβ.le
  obtain rfl | rfl | h4 : sstar = 2 ∨ sstar = 3 ∨ 4 ≤ sstar := by omega
  · -- two local steps are two projected gradient steps of the global loss
    have hℒ : ∀ y, HasFDerivAt ℒ (innerSL ℝ (g y)) y := by
      intro y
      have e : ℒ = fun y => (Fintype.card ι : ℝ)⁻¹ * ∑ c, ℒc c y := funext hℒmean
      rw [e]
      refine ((HasFDerivAt.fun_sum (u := univ) fun c _ => hℒc c y).const_mul
        (Fintype.card ι : ℝ)⁻¹).congr_fderiv ?_
      ext v
      rw [hmean y]
      simp
    have hg : ∀ y w, ‖g y - g w‖ ≤ β * ‖y - w‖ := by
      intro y w
      rw [hmean y, hmean w, ← smul_sub, ← sum_sub_distrib, norm_smul, norm_inv,
        Real.norm_natCast]
      calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ c, (gc c y - gc c w)‖
          ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ c, ‖gc c y - gc c w‖ :=
            mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.2 hC.le)
        _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _c : ι, β * ‖y - w‖ :=
            mul_le_mul_of_nonneg_left (sum_le_sum fun c _ => hgc c y w) (inv_nonneg.2 hC.le)
        _ = β * ‖y - w‖ := by
            rw [sum_const, card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ hC.ne']
    have h2 : lr * β < 2 := by
      push_cast at hs
      linarith
    exact loss_fedRound_two_lt (gc := gc) hℒ hg hP hmean hlr h2 hx
  · have h3 : lr * β ≤ 5 / 3 := by
      push_cast at hs
      linarith
    exact loss_fedRound_three_lt_of_convex_of_le hℒc hgc hconv hP hβ hℒmean hmean hlr h3 hx
  · have h4' : (4 : ℝ) ≤ sstar := by exact_mod_cast h4
    have h5 := mul_le_mul_of_nonneg_left h4' hu0
    exact loss_fedRound_lt_of_convex_of_mul_le_four hℒc hgc hconv hP hβ hℒmean hmean hlr
      (by linarith) (by omega) hs.le hx

/-- Non-vacuity of `loss_fedRound_lt_of_convex_of_mul_lt_four` beyond `s⋆ λ β = 2`: one client
with the convex loss `⟪v, y⟫ + ‖y‖² / 2` (`β = 1`, `Π = 1`), eight local steps of length `3/8`,
so `s⋆ λ β = 3`; the round from `0` decreases the loss if `v ≠ 0`. -/
example {v : E} (hv : v ≠ 0) :
    ⟪v, fedRound (1 : E →L[ℝ] E) (fun _ : Unit => fun z => v + z) (fun y => v + y) (3 / 8) 8 0⟫
      + ‖fedRound (1 : E →L[ℝ] E) (fun _ : Unit => fun z => v + z) (fun y => v + y) (3 / 8) 8
        0‖ ^ 2 / 2 < ⟪v, (0 : E)⟫ + ‖(0 : E)‖ ^ 2 / 2 := by
  refine loss_fedRound_lt_of_convex_of_mul_lt_four (ℒ := fun y : E => ⟪v, y⟫ + ‖y‖ ^ 2 / 2)
    (ℒc := fun _ : Unit => fun y : E => ⟪v, y⟫ + ‖y‖ ^ 2 / 2) (β := 1)
    (fun _ x => hasFDerivAt_inner_add_half_norm_sq v x) (fun _ x y => ?_) (fun _ x y => ?_)
    IsOrthProj.one one_pos (fun y => ?_) (fun y => ?_) (by norm_num) (by norm_num)
    (by norm_num) (x := 0) ?_
  · rw [add_sub_add_left_eq_sub, one_mul]
  · have h := sq_nonneg ‖y - x‖
    rw [norm_sub_sq_real] at h
    simp only [inner_add_left, inner_sub_right, real_inner_self_eq_norm_sq]
    linarith [real_inner_comm x y]
  · simp
  · simp
  · simpa using hv

end FederatedManySteps

end LeanDLRA
