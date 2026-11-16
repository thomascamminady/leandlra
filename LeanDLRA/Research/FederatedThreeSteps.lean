import LeanDLRA.Research.FederatedConvexThreshold

/-!
# FeDLRT with averaged gradients: three local steps

One aggregated round of FeDLRT with variance correction (Schotthöfer–Laiu, arXiv 2406.17887,
before truncation) is `fedRound`. This file treats `s⋆ = 3` when the global loss is the average
of convex client losses with `β`-Lipschitz gradients.

The proof is a weighted sum of four gradient inequalities of every client loss, between the
points `x`, `z¹`, `z²_c` and `x⋆`: the chain `x → z¹ → z²_c → x⋆` with weight `2/3` and the pair
`x → x⋆` with weight `1/3`. With `p_k` the projected client gradients at the four points and
`m_k` their averages over the clients, the remainder is a sum of squares of combinations of the
deviations `p_k - m_k`, a sum of squares of combinations of the `m_k`, and terms that are linear
in the deviations and vanish in the average.

## Main results

* `loss_fedRound_three_le_of_certificate`: the reduction of the descent bound to an inequality
  between the projected client gradients and their averages.
* `loss_fedRound_three_le_of_convex`: for `0 ≤ λ`, `u = λ β ≤ 5/3`,
  `ℒ(x⋆) ≤ ℒ(x) - λ (4u³ + u² - 65u + 90) / (6 (3u³ - 18u² + 20u + 5)) ‖Π ∇ℒ(x)‖²`.
* `loss_fedRound_three_le_of_convex_of_sq`: for `λ β = (q² + 9)/6`, `1 ≤ q ≤ 3/2`, that is
  `5/3 ≤ λ β ≤ 15/8`, with a fifth gradient inequality (`z²_c → x`),
  `ℒ(x⋆) ≤ ℒ(x) - (q + 3)(3 - 2q)(q² + 9) / (54 (3 - q) β) ‖Π ∇ℒ(x)‖²`.
* `loss_fedRound_three_lt_of_convex`: `ℒ(x⋆) < ℒ(x)` for `0 < λ`, `λ β < 15/8`, `Π ∇ℒ(x) ≠ 0`.
* `loss_le_loss_fedRound_three_quadratic`: for `λ β = 15/8` there are `45` quadratic clients
  for which the round does not decrease the loss.

## Remarks on the hypotheses

* The statements are for `s⋆ = 3`; the condition is `s⋆ λ β < 45/8`.
* The constant for `λ β ≤ 5/3` is not the best one. The constant for `5/3 ≤ λ β ≤ 15/8` is the
  loss change of clients with Hessians `0` and `1` for one particular proportion of the two
  kinds; this file proves that only at `λ β = 15/8`, where the proportion is `32 : 13`.
* The global loss enters only through the two averaging hypotheses; its differentiability is
  not used.
* The clients are averaged with equal weights, as in `fedRound`.
-/

open Set Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section FederatedThreeSteps

variable {ι : Type*} {ℒ : E → ℝ} {g : E → E} {gc : ι → E → E} {ℒc : ι → E → ℝ} {β lr : ℝ}
  {P : E →L[ℝ] E}

/-- The quadratic form of the client deviations in the three-step certificate is a sum of three
squares for `u ≤ 5/3`. -/
lemma fedThree_deviation_form_nonneg (d0 d1 d2 d3 : E) {u : ℝ} (hu : u ≤ 5 / 3) (hu0 : 0 ≤ u) :
    0 ≤ 1 / 2 * ⟪d0, d0⟫ + -2 / 3 * ⟪d0, d1⟫ + -2 * u / 3 * ⟪d0, d2⟫
      + (2 * u - 1) / 3 * ⟪d0, d3⟫ + 2 / 3 * ⟪d1, d1⟫ + 2 * (u - 1) / 3 * ⟪d1, d2⟫
      + -2 * u / 3 * ⟪d1, d3⟫ + 2 / 3 * ⟪d2, d2⟫ + -2 / 3 * ⟪d2, d3⟫ + 1 / 2 * ⟪d3, d3⟫ := by
  have h1 := real_inner_self_nonneg (x := -d0 + (2 : ℝ) • d1 + (u - 1) • d2 - u • d3)
  have h2 := real_inner_self_nonneg (x := d0 + (u - 3) • d2 + (2 - u) • d3)
  have h3 := real_inner_self_nonneg (x := d0 - d3)
  have h := add_nonneg (add_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 3 - u) h1)
    (mul_nonneg (by linarith : (0 : ℝ) ≤ u + 1) h2))
    (mul_nonneg (by linarith : (0 : ℝ) ≤ 5 - 3 * u) h3)
  refine nonneg_of_mul_nonneg_right ?_ (by linarith : (0 : ℝ) < 6 * (3 - u))
  convert h using 1
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_neg_left,
    inner_neg_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm d0 d1, real_inner_comm d0 d2, real_inner_comm d0 d3,
    real_inner_comm d1 d2, real_inner_comm d1 d3, real_inner_comm d2 d3]
  ring

/-- The quadratic form of the averaged client gradients in the three-step certificate dominates
a multiple of `‖m₀‖²` for `0 ≤ u ≤ 5/3`; the difference is a sum of three squares. -/
lemma fedThree_mean_form_ge (m0 m1 m2 m3 : E) {u : ℝ} (hu : u ≤ 5 / 3) (hu0 : 0 ≤ u) :
    u * (4 * u ^ 3 + u ^ 2 - 65 * u + 90) / (6 * (3 * u ^ 3 - 18 * u ^ 2 + 20 * u + 5))
        * ⟪m0, m0⟫ ≤
      1 / 2 * ⟪m0, m0⟫ + 2 * (u - 1) / 3 * ⟪m0, m1⟫ + (u - 1) / 3 * ⟪m0, m3⟫
        + 2 / 3 * ⟪m1, m1⟫ + 2 * (u - 1) / 3 * ⟪m1, m2⟫ + u / 3 * ⟪m1, m3⟫
        + 2 / 3 * ⟪m2, m2⟫ + (3 * u - 2) / 3 * ⟪m2, m3⟫ + 1 / 2 * ⟪m3, m3⟫ := by
  have hE : 0 < 8 + 12 * u - 9 * u ^ 2 := by nlinarith [mul_nonneg hu0 (sub_nonneg.2 hu)]
  have h13 : 0 ≤ 13 * u + 5 / 3 - 3 * u ^ 2 := by nlinarith [mul_nonneg hu0 (sub_nonneg.2 hu)]
  have hD : 0 < 3 * u ^ 3 - 18 * u ^ 2 + 20 * u + 5 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hu) h13]
  have h1 := real_inner_self_nonneg
    (x := (u - 1) • m0 + u • m1 + (3 * u - 2) • m2 + (3 : ℝ) • m3)
  have h2 := real_inner_self_nonneg
    (x := ((u - 1) * (3 * u - 2)) • m0 + (3 * u ^ 2 - 8 * u + 6) • m1
      - (8 + 12 * u - 9 * u ^ 2) • m2)
  have h3 := real_inner_self_nonneg
    (x := (2 * (3 * u ^ 3 - 18 * u ^ 2 + 20 * u + 5)) • m1
      - ((u - 1) * (6 * u ^ 2 - 5 * u - 10)) • m0)
  have h := add_nonneg (add_nonneg (mul_nonneg (mul_pos hE hD).le h1) (mul_nonneg hD.le h2))
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) h3)
  have hpoly : 0 ≤ 6 * (3 * u ^ 3 - 18 * u ^ 2 + 20 * u + 5)
      * (1 / 2 * ⟪m0, m0⟫ + 2 * (u - 1) / 3 * ⟪m0, m1⟫ + (u - 1) / 3 * ⟪m0, m3⟫
        + 2 / 3 * ⟪m1, m1⟫ + 2 * (u - 1) / 3 * ⟪m1, m2⟫ + u / 3 * ⟪m1, m3⟫
        + 2 / 3 * ⟪m2, m2⟫ + (3 * u - 2) / 3 * ⟪m2, m3⟫ + 1 / 2 * ⟪m3, m3⟫)
      - u * (4 * u ^ 3 + u ^ 2 - 65 * u + 90) * ⟪m0, m0⟫ := by
    refine nonneg_of_mul_nonneg_right ?_ (mul_pos (by norm_num : (0 : ℝ) < 3) hE)
    convert h using 1
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right]
    simp only [real_inner_comm m0 m1, real_inner_comm m0 m2, real_inner_comm m0 m3,
      real_inner_comm m1 m2, real_inner_comm m1 m3, real_inner_comm m2 m3]
    ring
  rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 6) hD)]
  linarith

/-- **The three-step certificate for one client.** `p₀, …, p₃` stand for the projected
gradients of a client at `x`, `z¹`, `z²_c`, `x⋆` and `m₀, …, m₃` for their averages over the
clients. The weighted sum of the four gradient inequalities is bounded below by a multiple of
`‖m₀‖²` plus terms that are linear in the deviations `p_k - m_k`. -/
lemma fedThree_client_form_ge (p0 p1 p2 p3 m0 m1 m2 m3 : E) {u : ℝ} (hu : u ≤ 5 / 3)
    (hu0 : 0 ≤ u) :
    u * (4 * u ^ 3 + u ^ 2 - 65 * u + 90) / (6 * (3 * u ^ 3 - 18 * u ^ 2 + 20 * u + 5))
        * ‖m0‖ ^ 2
      + (⟪p0 - m0, m0 - (2 / 3 : ℝ) • m1 - (2 * u / 3) • m2 + ((2 * u - 1) / 3) • m3⟫
        + ⟪p1 - m1, (2 * (u - 1) / 3) • m0 + (4 / 3 : ℝ) • m1 + (2 * (u - 1) / 3) • m2
            - (2 * u / 3) • m3⟫
        + ⟪p2 - m2, (2 * (u - 1) / 3) • m1 + (4 / 3 : ℝ) • m2 - (2 / 3 : ℝ) • m3⟫
        + ⟪p3 - m3, ((u - 1) / 3) • m0 + (u / 3) • m1 + ((3 * u - 2) / 3) • m2 + m3⟫) ≤
      u * (2 / 3 * ⟪p1, m0⟫ + 2 / 3 * ⟪p2, p1 - p0 + m0⟫
          + 2 / 3 * ⟪p3, m1 + m2 - m0 - p1 + p0⟫ + 1 / 3 * ⟪p3, m0 + m1 + m2⟫)
        + 1 / 2 * (2 / 3 * ‖p0 - p1‖ ^ 2 + 2 / 3 * ‖p1 - p2‖ ^ 2 + 2 / 3 * ‖p2 - p3‖ ^ 2
          + 1 / 3 * ‖p0 - p3‖ ^ 2) := by
  have hd := fedThree_deviation_form_nonneg (p0 - m0) (p1 - m1) (p2 - m2) (p3 - m3) hu hu0
  have hm := fedThree_mean_form_ge m0 m1 m2 m3 hu hu0
  have key : u * (2 / 3 * ⟪p1, m0⟫ + 2 / 3 * ⟪p2, p1 - p0 + m0⟫
          + 2 / 3 * ⟪p3, m1 + m2 - m0 - p1 + p0⟫ + 1 / 3 * ⟪p3, m0 + m1 + m2⟫)
        + 1 / 2 * (2 / 3 * ⟪p0 - p1, p0 - p1⟫ + 2 / 3 * ⟪p1 - p2, p1 - p2⟫
          + 2 / 3 * ⟪p2 - p3, p2 - p3⟫ + 1 / 3 * ⟪p0 - p3, p0 - p3⟫)
      = (1 / 2 * ⟪p0 - m0, p0 - m0⟫ + -2 / 3 * ⟪p0 - m0, p1 - m1⟫
          + -2 * u / 3 * ⟪p0 - m0, p2 - m2⟫ + (2 * u - 1) / 3 * ⟪p0 - m0, p3 - m3⟫
          + 2 / 3 * ⟪p1 - m1, p1 - m1⟫ + 2 * (u - 1) / 3 * ⟪p1 - m1, p2 - m2⟫
          + -2 * u / 3 * ⟪p1 - m1, p3 - m3⟫ + 2 / 3 * ⟪p2 - m2, p2 - m2⟫
          + -2 / 3 * ⟪p2 - m2, p3 - m3⟫ + 1 / 2 * ⟪p3 - m3, p3 - m3⟫)
        + (1 / 2 * ⟪m0, m0⟫ + 2 * (u - 1) / 3 * ⟪m0, m1⟫ + (u - 1) / 3 * ⟪m0, m3⟫
          + 2 / 3 * ⟪m1, m1⟫ + 2 * (u - 1) / 3 * ⟪m1, m2⟫ + u / 3 * ⟪m1, m3⟫
          + 2 / 3 * ⟪m2, m2⟫ + (3 * u - 2) / 3 * ⟪m2, m3⟫ + 1 / 2 * ⟪m3, m3⟫)
        + (⟪p0 - m0, m0 - (2 / 3 : ℝ) • m1 - (2 * u / 3) • m2 + ((2 * u - 1) / 3) • m3⟫
          + ⟪p1 - m1, (2 * (u - 1) / 3) • m0 + (4 / 3 : ℝ) • m1 + (2 * (u - 1) / 3) • m2
              - (2 * u / 3) • m3⟫
          + ⟪p2 - m2, (2 * (u - 1) / 3) • m1 + (4 / 3 : ℝ) • m2 - (2 / 3 : ℝ) • m3⟫
          + ⟪p3 - m3, ((u - 1) / 3) • m0 + (u / 3) • m1 + ((3 * u - 2) / 3) • m2 + m3⟫) := by
    simp only [inner_add_right, inner_sub_left, inner_sub_right, real_inner_smul_right]
    simp only [real_inner_comm p0 p1, real_inner_comm p0 p2, real_inner_comm p0 p3,
      real_inner_comm p1 p2, real_inner_comm p1 p3, real_inner_comm p2 p3,
      real_inner_comm m0 m1, real_inner_comm m0 m3, real_inner_comm m1 m2,
      real_inner_comm m1 m3, real_inner_comm m2 m3, real_inner_comm p0 m0,
      real_inner_comm p1 m0, real_inner_comm p1 m1, real_inner_comm p2 m0,
      real_inner_comm p2 m1, real_inner_comm p2 m2, real_inner_comm p3 m0,
      real_inner_comm p3 m1, real_inner_comm p3 m2, real_inner_comm p3 m3]
    ring
  simp only [real_inner_self_eq_norm_sq] at key hm hd
  rw [key]
  linarith

/-- **Gradient inequality of a convex function with `β`-Lipschitz gradient along a direction in
the range of an orthogonal projector**, multiplied by `β`. If `z - y = λ v` with `Π v = v`, then
`β f(y) + λ β ⟪Π ∇f(y), v⟫ + ‖Π ∇f(z) - Π ∇f(y)‖² / 2 ≤ β f(z)`. -/
lemma mul_add_inner_proj_add_norm_sq_le_of_convex {f : E → ℝ} {gf : E → E}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (gf y)) y)
    (hgf : ∀ y z, ‖gf y - gf z‖ ≤ β * ‖y - z‖)
    (hconv : ∀ y z, f y + ⟪gf y, z - y⟫ ≤ f z) (hP : IsOrthProj P) (hβ : 0 < β) {y z v : E}
    (hv : P v = v) (hzy : z - y = lr • v) :
    β * f y + lr * β * ⟪P (gf y), v⟫ + 1 / 2 * ‖P (gf z) - P (gf y)‖ ^ 2 ≤ β * f z := by
  have h := add_inner_add_norm_sq_le_of_convex (lr := 1 / β) hf hgf hconv (by positivity)
    (le_of_eq (one_div_mul_cancel hβ.ne')) y z
  have e1 : ⟪gf y, z - y⟫ = lr * ⟪P (gf y), v⟫ := by
    rw [hzy, inner_smul_right, hP.symm, hv]
  have e2 : ‖P (gf z) - P (gf y)‖ ^ 2 ≤ ‖gf z - gf y‖ ^ 2 := by
    rw [← map_sub]
    exact pow_le_pow_left₀ (norm_nonneg _) (hP.norm_le _) 2
  have e3 : β * (1 / β / 2 * ‖gf z - gf y‖ ^ 2) = 1 / 2 * ‖gf z - gf y‖ ^ 2 := by
    field_simp
  rw [e1] at h
  have h' := mul_le_mul_of_nonneg_left h hβ.le
  rw [mul_add, e3] at h'
  linarith

/-- **Loss descent of the FeDLRT round with three local steps from a certificate.** Let the
global loss be the average of convex client losses with `β`-Lipschitz gradients. Take the five
gradient inequalities of a client loss for the pairs `x → z¹`, `z¹ → z²_c` (weight `b + e`),
`z²_c → x` (weight `b`), `x → x⋆` (weight `c`) and `z²_c → x⋆` (weight `e`). If the weighted sum
of their remainders, written in the projected client gradients `p_k` and their averages `m_k`,
is bounded below by `κ ‖m₀‖²` plus terms that are linear in the deviations `p_k - m_k`, then
`ℒ(x⋆) ≤ ℒ(x) - κ / ((c + e) β) ‖Π ∇ℒ(x)‖²`. -/
theorem loss_fedRound_three_le_of_certificate [Fintype ι] [Nonempty ι]
    (hℒc : ∀ c x, HasFDerivAt (ℒc c) (innerSL ℝ (gc c x)) x)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hconv : ∀ c x y, ℒc c x + ⟪gc c x, y - x⟫ ≤ ℒc c y)
    (hP : IsOrthProj P) (hβ : 0 < β)
    (hℒmean : ∀ y, ℒ y = (Fintype.card ι : ℝ)⁻¹ * ∑ c, ℒc c y)
    (hmean : ∀ y, g y = (Fintype.card ι : ℝ)⁻¹ • ∑ c, gc c y) {b c e κ : ℝ} (hb : 0 ≤ b)
    (hc : 0 ≤ c) (he : 0 ≤ e) (hw : 0 < c + e)
    (hform : ∀ m0 m1 m2 m3 : E, ∃ n0 n1 n2 n3 : E, ∀ p0 p1 p2 p3 : E,
      κ * ‖m0‖ ^ 2
        + (⟪p0 - m0, n0⟫ + ⟪p1 - m1, n1⟫ + ⟪p2 - m2, n2⟫ + ⟪p3 - m3, n3⟫) ≤
      lr * β * ((b + e) * ⟪p1, m0⟫ + (b + e) * ⟪p2, p1 - p0 + m0⟫
          + b * ⟪p0, -(m0 + (p1 - p0 + m0))⟫ + c * ⟪p3, m0 + m1 + m2⟫
          + e * ⟪p3, m1 + m2 - m0 - p1 + p0⟫)
        + 1 / 2 * ((b + e) * ‖p0 - p1‖ ^ 2 + (b + e) * ‖p1 - p2‖ ^ 2 + b * ‖p2 - p0‖ ^ 2
          + c * ‖p0 - p3‖ ^ 2 + e * ‖p2 - p3‖ ^ 2)) (x : E) :
    ℒ (fedRound P gc g lr 3 x) ≤ ℒ x - κ / ((c + e) * β) * ‖P (g x)‖ ^ 2 := by
  have hC : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hPg : ∀ y, P (g y) = (Fintype.card ι : ℝ)⁻¹ • ∑ c, P (gc c y) := fun y => by
    rw [hmean y, map_smul, map_sum]
  -- names for the points, the projected client gradients and their averages
  obtain ⟨m0, hm0⟩ : ∃ m0 : E, m0 = P (g x) := ⟨_, rfl⟩
  obtain ⟨z1, hz1⟩ : ∃ z1 : E, z1 = x - lr • m0 := ⟨_, rfl⟩
  obtain ⟨m1, hm1⟩ : ∃ m1 : E, m1 = P (g z1) := ⟨_, rfl⟩
  obtain ⟨p0, hp0⟩ : ∃ p0 : ι → E, ∀ c, p0 c = P (gc c x) := ⟨_, fun _ => rfl⟩
  obtain ⟨p1, hp1⟩ : ∃ p1 : ι → E, ∀ c, p1 c = P (gc c z1) := ⟨_, fun _ => rfl⟩
  obtain ⟨z2, hz2⟩ : ∃ z2 : ι → E, ∀ c, z2 c = x - lr • m0 - lr • (p1 c - p0 c + m0) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ p2 : ι → E, ∀ c, p2 c = P (gc c (z2 c)) := ⟨_, fun _ => rfl⟩
  obtain ⟨m2, hm2⟩ : ∃ m2 : E, m2 = (Fintype.card ι : ℝ)⁻¹ • ∑ c, p2 c := ⟨_, rfl⟩
  obtain ⟨xs, hxs⟩ : ∃ xs : E, xs = fedRound P gc g lr 3 x := ⟨_, rfl⟩
  obtain ⟨m3, hm3⟩ : ∃ m3 : E, m3 = P (g xs) := ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ p3 : ι → E, ∀ c, p3 c = P (gc c xs) := ⟨_, fun _ => rfl⟩
  obtain ⟨n0, n1, n2, n3, hn⟩ := hform m0 m1 m2 m3
  -- the client iterates
  have i1 : ∀ c, fedClientIter P gc g lr x c 1 = z1 := by
    intro c
    rw [fedClientIter_succ, hz1, hm0]
    simp [fedClientIter]
  have i2 : ∀ c, fedClientIter P gc g lr x c 2 = z2 c := by
    intro c
    rw [fedClientIter_succ, i1, map_add, map_sub, ← hp1, ← hp0, ← hm0, hz2, hz1]
  have i3 : ∀ c, fedClientIter P gc g lr x c 3 = z2 c - lr • (p2 c - p0 c + m0) := by
    intro c
    rw [fedClientIter_succ, i2, map_add, map_sub, ← hp2, ← hp0, ← hm0]
  -- sums of the projected client gradients
  have hS0 : ∑ c, p0 c = (Fintype.card ι : ℝ) • m0 := by
    simp_rw [hp0, hm0, hPg, smul_smul, mul_inv_cancel₀ hC.ne', one_smul]
  have hS1 : ∑ c, p1 c = (Fintype.card ι : ℝ) • m1 := by
    simp_rw [hp1, hm1, hPg, smul_smul, mul_inv_cancel₀ hC.ne', one_smul]
  have hS2 : ∑ c, p2 c = (Fintype.card ι : ℝ) • m2 := by
    rw [hm2, smul_smul, mul_inv_cancel₀ hC.ne', one_smul]
  have hS3 : ∑ c, p3 c = (Fintype.card ι : ℝ) • m3 := by
    simp_rw [hp3, hm3, hPg, smul_smul, mul_inv_cancel₀ hC.ne', one_smul]
  have hxs' : xs = x - lr • (m0 + m1 + m2) := by
    have e : ∑ c, fedClientIter P gc g lr x c 3 =
        (Fintype.card ι : ℝ) • (x - lr • (m0 + m1 + m2)) := by
      simp_rw [i3, hz2]
      simp only [sum_sub_distrib, sum_add_distrib, ← smul_sum, sum_const, card_univ, hS0, hS1,
        hS2, ← Nat.cast_smul_eq_nsmul ℝ]
      module
    rw [hxs, fedRound, e, smul_smul, inv_mul_cancel₀ hC.ne', one_smul]
  -- fixed points of the projector
  have q0 : P m0 = m0 := by rw [hm0, hP.idem]
  have q1 : P m1 = m1 := by rw [hm1, hP.idem]
  have r0 : ∀ c, P (p0 c) = p0 c := fun c => by rw [hp0, hP.idem]
  have r1 : ∀ c, P (p1 c) = p1 c := fun c => by rw [hp1, hP.idem]
  have r2 : ∀ c, P (p2 c) = p2 c := fun c => by rw [hp2, hP.idem]
  have q2 : P m2 = m2 := by
    rw [hm2, map_smul, map_sum]
    simp_rw [r2]
  -- the weighted gradient inequalities of one client
  have hcl : ∀ k, κ * ‖m0‖ ^ 2
      + (⟪p0 k - m0, n0⟫ + ⟪p1 k - m1, n1⟫ + ⟪p2 k - m2, n2⟫ + ⟪p3 k - m3, n3⟫)
      ≤ (c + e) * β * (ℒc k x - ℒc k xs) := by
    intro k
    have I01 := mul_add_inner_proj_add_norm_sq_le_of_convex (lr := lr) (hℒc k) (hgc k)
      (hconv k) hP hβ (y := z1) (z := x) q0 (by rw [hz1, sub_sub_cancel])
    have I12 := mul_add_inner_proj_add_norm_sq_le_of_convex (lr := lr) (hℒc k) (hgc k)
      (hconv k) hP hβ (y := z2 k) (z := z1) (v := p1 k - p0 k + m0)
      (by rw [map_add, map_sub, r1, r0, q0]) (by rw [hz2, hz1]; module)
    have I20 := mul_add_inner_proj_add_norm_sq_le_of_convex (lr := lr) (hℒc k) (hgc k)
      (hconv k) hP hβ (y := x) (z := z2 k) (v := -(m0 + (p1 k - p0 k + m0)))
      (by simp only [map_neg, map_add, map_sub, r1, r0, q0]) (by rw [hz2]; module)
    have I23 := mul_add_inner_proj_add_norm_sq_le_of_convex (lr := lr) (hℒc k) (hgc k)
      (hconv k) hP hβ (y := xs) (z := z2 k) (v := m1 + m2 - m0 - p1 k + p0 k)
      (by simp only [map_add, map_sub, r1, r0, q0, q1, q2]) (by rw [hz2, hxs']; module)
    have I03 := mul_add_inner_proj_add_norm_sq_le_of_convex (lr := lr) (hℒc k) (hgc k)
      (hconv k) hP hβ (y := xs) (z := x) (v := m0 + m1 + m2)
      (by simp only [map_add, q0, q1, q2]) (by rw [hxs']; module)
    rw [← hp1, ← hp0] at I01
    rw [← hp1, ← hp2] at I12
    rw [← hp2, ← hp0] at I20
    rw [← hp2, ← hp3] at I23
    rw [← hp0, ← hp3] at I03
    have t01 := mul_le_mul_of_nonneg_left I01 (add_nonneg hb he)
    have t12 := mul_le_mul_of_nonneg_left I12 (add_nonneg hb he)
    have t20 := mul_le_mul_of_nonneg_left I20 hb
    have t03 := mul_le_mul_of_nonneg_left I03 hc
    have t23 := mul_le_mul_of_nonneg_left I23 he
    have hk := hn (p0 k) (p1 k) (p2 k) (p3 k)
    linarith
  -- the terms that are linear in the deviations vanish in the sum over the clients
  have z0 : ∀ n : E, ∑ c, ⟪p0 c - m0, n⟫ = 0 := fun n => by
    rw [← sum_inner, sum_sub_distrib, hS0, sum_const, card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
      sub_self, inner_zero_left]
  have z1' : ∀ n : E, ∑ c, ⟪p1 c - m1, n⟫ = 0 := fun n => by
    rw [← sum_inner, sum_sub_distrib, hS1, sum_const, card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
      sub_self, inner_zero_left]
  have z2' : ∀ n : E, ∑ c, ⟪p2 c - m2, n⟫ = 0 := fun n => by
    rw [← sum_inner, sum_sub_distrib, hS2, sum_const, card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
      sub_self, inner_zero_left]
  have z3' : ∀ n : E, ∑ c, ⟪p3 c - m3, n⟫ = 0 := fun n => by
    rw [← sum_inner, sum_sub_distrib, hS3, sum_const, card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
      sub_self, inner_zero_left]
  have hall := sum_le_sum fun k (_ : k ∈ (univ : Finset ι)) => hcl k
  simp only [sum_add_distrib, z0, z1', z2', z3', add_zero, sum_const, card_univ, nsmul_eq_mul,
    ← mul_sum, sum_sub_distrib] at hall
  have s1 : ∑ c, ℒc c x = (Fintype.card ι : ℝ) * ℒ x := by
    rw [hℒmean x, mul_inv_cancel_left₀ hC.ne']
  have s2 : ∑ c, ℒc c xs = (Fintype.card ι : ℝ) * ℒ xs := by
    rw [hℒmean xs, mul_inv_cancel_left₀ hC.ne']
  rw [s1, s2] at hall
  have hfin : (Fintype.card ι : ℝ) * (κ * ‖m0‖ ^ 2) ≤
      (Fintype.card ι : ℝ) * ((c + e) * β * (ℒ x - ℒ xs)) := by
    linarith
  have h := le_of_mul_le_mul_left hfin hC
  have h2 : κ / ((c + e) * β) * ‖m0‖ ^ 2 ≤ ℒ x - ℒ xs := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos hw hβ)]
    linarith
  rw [← hxs, ← hm0]
  linarith

/-- **Loss descent of the FeDLRT round with three local steps and averaged convex clients.** Let
the global loss be the average of the client losses, let every client loss be convex (in the
form of the gradient inequality) with a `β`-Lipschitz gradient, and let `0 ≤ λ`,
`u = λ β ≤ 5/3`. Then
`ℒ(x⋆) ≤ ℒ(x) - λ (4u³ + u² - 65u + 90) / (6 (3u³ - 18u² + 20u + 5)) ‖Π ∇ℒ(x)‖²`. -/
theorem loss_fedRound_three_le_of_convex [Fintype ι] [Nonempty ι]
    (hℒc : ∀ c x, HasFDerivAt (ℒc c) (innerSL ℝ (gc c x)) x)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hconv : ∀ c x y, ℒc c x + ⟪gc c x, y - x⟫ ≤ ℒc c y)
    (hP : IsOrthProj P) (hβ : 0 < β)
    (hℒmean : ∀ y, ℒ y = (Fintype.card ι : ℝ)⁻¹ * ∑ c, ℒc c y)
    (hmean : ∀ y, g y = (Fintype.card ι : ℝ)⁻¹ • ∑ c, gc c y) (hlr : 0 ≤ lr)
    (hu : lr * β ≤ 5 / 3) (x : E) :
    ℒ (fedRound P gc g lr 3 x) ≤ ℒ x - lr * ((4 * (lr * β) ^ 3 + (lr * β) ^ 2 - 65 * (lr * β) + 90)
        / (6 * (3 * (lr * β) ^ 3 - 18 * (lr * β) ^ 2 + 20 * (lr * β) + 5))) * ‖P (g x)‖ ^ 2 := by
  have hu0 : 0 ≤ lr * β := mul_nonneg hlr hβ.le
  have h := loss_fedRound_three_le_of_certificate (lr := lr) (b := 0) (c := 1 / 3) (e := 2 / 3)
    (κ := lr * β * (4 * (lr * β) ^ 3 + (lr * β) ^ 2 - 65 * (lr * β) + 90)
      / (6 * (3 * (lr * β) ^ 3 - 18 * (lr * β) ^ 2 + 20 * (lr * β) + 5))) hℒc hgc hconv hP
    hβ hℒmean hmean le_rfl (by norm_num) (by norm_num) (by norm_num)
    (fun m0 m1 m2 m3 =>
      ⟨m0 - (2 / 3 : ℝ) • m1 - (2 * (lr * β) / 3) • m2 + ((2 * (lr * β) - 1) / 3) • m3,
        (2 * (lr * β - 1) / 3) • m0 + (4 / 3 : ℝ) • m1 + (2 * (lr * β - 1) / 3) • m2
          - (2 * (lr * β) / 3) • m3,
        (2 * (lr * β - 1) / 3) • m1 + (4 / 3 : ℝ) • m2 - (2 / 3 : ℝ) • m3,
        ((lr * β - 1) / 3) • m0 + (lr * β / 3) • m1 + ((3 * (lr * β) - 2) / 3) • m2 + m3,
        fun p0 p1 p2 p3 => by
          have h := fedThree_client_form_ge p0 p1 p2 p3 m0 m1 m2 m3 hu hu0
          linarith⟩) x
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (4 * (lr * β) ^ 3 + (lr * β) ^ 2 - 65 * (lr * β) + 90)
      / (6 * (3 * (lr * β) ^ 3 - 18 * (lr * β) ^ 2 + 20 * (lr * β) + 5)) := ⟨_, rfl⟩
  have e : lr * β * (4 * (lr * β) ^ 3 + (lr * β) ^ 2 - 65 * (lr * β) + 90)
      / (6 * (3 * (lr * β) ^ 3 - 18 * (lr * β) ^ 2 + 20 * (lr * β) + 5)) / ((1 / 3 + 2 / 3) * β)
      = lr * K := by
    rw [mul_div_assoc, ← hK, div_eq_iff (mul_pos (by norm_num) hβ).ne']
    ring
  rw [e] at h
  rw [← hK]
  exact h

/-- **The FeDLRT round with three local steps and averaged convex clients decreases the loss
when `λ β ≤ 5/3`**, that is `s⋆ λ β ≤ 5`, and the projected gradient does not vanish. -/
theorem loss_fedRound_three_lt_of_convex_of_le [Fintype ι] [Nonempty ι]
    (hℒc : ∀ c x, HasFDerivAt (ℒc c) (innerSL ℝ (gc c x)) x)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hconv : ∀ c x y, ℒc c x + ⟪gc c x, y - x⟫ ≤ ℒc c y)
    (hP : IsOrthProj P) (hβ : 0 < β)
    (hℒmean : ∀ y, ℒ y = (Fintype.card ι : ℝ)⁻¹ * ∑ c, ℒc c y)
    (hmean : ∀ y, g y = (Fintype.card ι : ℝ)⁻¹ • ∑ c, gc c y) (hlr : 0 < lr)
    (hu : lr * β ≤ 5 / 3) {x : E} (hx : P (g x) ≠ 0) :
    ℒ (fedRound P gc g lr 3 x) < ℒ x := by
  have h := loss_fedRound_three_le_of_convex hℒc hgc hconv hP hβ hℒmean hmean hlr.le hu x
  have hu0 : 0 ≤ lr * β := mul_nonneg hlr.le hβ.le
  have h47 : 0 ≤ 470 / 9 - 23 / 3 * (lr * β) - 4 * (lr * β) ^ 2 := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.2 hu)]
  have hN : 0 < 4 * (lr * β) ^ 3 + (lr * β) ^ 2 - 65 * (lr * β) + 90 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hu) h47]
  have h13 : 0 ≤ 13 * (lr * β) + 5 / 3 - 3 * (lr * β) ^ 2 := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.2 hu)]
  have hD : 0 < 3 * (lr * β) ^ 3 - 18 * (lr * β) ^ 2 + 20 * (lr * β) + 5 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hu) h13]
  have hpos : 0 < lr * ((4 * (lr * β) ^ 3 + (lr * β) ^ 2 - 65 * (lr * β) + 90)
      / (6 * (3 * (lr * β) ^ 3 - 18 * (lr * β) ^ 2 + 20 * (lr * β) + 5))) * ‖P (g x)‖ ^ 2 :=
    mul_pos (mul_pos hlr (div_pos hN (mul_pos (by norm_num) hD)))
      (pow_pos (norm_pos_iff.2 hx) 2)
  linarith

/-- Non-vacuity of `loss_fedRound_three_lt_of_convex_of_le`: one client with the convex loss
`⟪v, y⟫ + ‖y‖² / 2` (`β = 1`, `Π = 1`) and `λ = 3/2`, so `s⋆ λ β = 9/2`; the round from `0`
decreases the loss if `v ≠ 0`. -/
example {v : E} (hv : v ≠ 0) :
    ⟪v, fedRound (1 : E →L[ℝ] E) (fun _ : Unit => fun z => v + z) (fun y => v + y) (3 / 2) 3 0⟫
      + ‖fedRound (1 : E →L[ℝ] E) (fun _ : Unit => fun z => v + z) (fun y => v + y) (3 / 2) 3
        0‖ ^ 2 / 2 < ⟪v, (0 : E)⟫ + ‖(0 : E)‖ ^ 2 / 2 := by
  refine loss_fedRound_three_lt_of_convex_of_le (ℒ := fun y : E => ⟪v, y⟫ + ‖y‖ ^ 2 / 2)
    (ℒc := fun _ : Unit => fun y : E => ⟪v, y⟫ + ‖y‖ ^ 2 / 2) (β := 1)
    (fun _ x => hasFDerivAt_inner_add_half_norm_sq v x) (fun _ x y => ?_) (fun _ x y => ?_)
    IsOrthProj.one one_pos (fun y => ?_) (fun y => ?_) (by norm_num) (by norm_num) (x := 0) ?_
  · rw [add_sub_add_left_eq_sub, one_mul]
  · have h := sq_nonneg ‖y - x‖
    rw [norm_sub_sq_real] at h
    simp only [inner_add_left, inner_sub_right, real_inner_self_eq_norm_sq]
    linarith [real_inner_comm x y]
  · simp
  · simp
  · simpa using hv

/-- The quadratic form of the client deviations in the three-step certificate with the weights
of the range `5/3 ≤ λ β ≤ 15/8` (`λ β = (q² + 9)/6`, `1 ≤ q ≤ 3/2`) is a sum of two squares. -/
lemma fedThree_deviation_form_nonneg_of_sq (d0 d1 d2 d3 : E) {q : ℝ} (hq : q ≤ 3 / 2)
    (hq1 : 1 ≤ q) :
    0 ≤
      (q ^ 4 / 6 + q ^ 3 / 3 + 2 * q ^ 2 + 2 * q + 3 / 2) * ⟪d0, d0⟫
        + (-q ^ 4 / 6 - q ^ 3 / 3 - q ^ 2 - 5 * q - 3 / 2) * ⟪d0, d1⟫
        + (-q ^ 3 / 3 - 2 * q ^ 2 - 5 * q - 6) * ⟪d0, d2⟫
        + (-q ^ 4 / 6 - q ^ 2 + 6 * q + 9 / 2) * ⟪d0, d3⟫ + (2 * q + 6) * ⟪d1, d1⟫
        + (q ^ 3 / 3 + q ^ 2 + q + 3) * ⟪d1, d2⟫ + (q ^ 4 / 6 - 27 / 2) * ⟪d1, d3⟫
        + (2 * q + 6) * ⟪d2, d2⟫ + (q ^ 2 - 9) * ⟪d2, d3⟫ + (9 - 3 * q) * ⟪d3, d3⟫ := by
  have h1 := real_inner_self_nonneg
    (x :=
      (-q ^ 3 + q ^ 2 - 9 * q - 3 : ℝ) • d0 + (24 : ℝ) • d1 + (2 * q ^ 2 + 6 : ℝ) • d2
        + (q ^ 3 - 3 * q ^ 2 + 9 * q - 27 : ℝ) • d3)
  have h2 := real_inner_self_nonneg
    (x :=
      (-q ^ 2 - 2 * q - 3 : ℝ) • d0 + (2 * q + 6 : ℝ) • d2 + (q ^ 2 - 3 : ℝ) • d3)
  have h := add_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ q + 3) h1)
    (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 3 - q)
      (by positivity : (0 : ℝ) ≤ q ^ 2 + 15)) h2)
  refine nonneg_of_mul_nonneg_right ?_ (by norm_num : (0 : ℝ) < 288)
  convert h using 1
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm d0 d1, real_inner_comm d0 d2, real_inner_comm d0 d3,
    real_inner_comm d1 d2, real_inner_comm d1 d3, real_inner_comm d2 d3]
  ring

/-- The quadratic form of the averaged client gradients in the three-step certificate with the
weights of the range `λ β = (q² + 9)/6`, `1 ≤ q ≤ 3/2`, dominates a multiple of `‖m₀‖²`; the
difference is a sum of three squares. -/
lemma fedThree_mean_form_ge_of_sq (m0 m1 m2 m3 : E) {q : ℝ} (hq : q ≤ 3 / 2) (hq1 : 1 ≤ q) :
    (-2 * q ^ 4 / 9 - q ^ 3 / 3 - q ^ 2 - 3 * q + 9) * ⟪m0, m0⟫ ≤
      (-q ^ 4 / 6 - q ^ 3 / 3 - 4 * q + 21 / 2) * ⟪m0, m0⟫
        + (-q ^ 4 / 6 - 2 * q + 15 / 2) * ⟪m0, m1⟫ + (-q ^ 2 - 2 * q + 3) * ⟪m0, m2⟫
        + (q ^ 4 / 6 - q ^ 3 + 2 * q ^ 2 - 3 * q + 9 / 2) * ⟪m0, m3⟫ + (2 * q + 6) * ⟪m1, m1⟫
        + (q ^ 3 / 3 + q ^ 2 + q + 3) * ⟪m1, m2⟫
        + (q ^ 4 / 6 - q ^ 3 + 3 * q ^ 2 - 9 * q + 27 / 2) * ⟪m1, m3⟫ + (2 * q + 6) * ⟪m2, m2⟫
        + (-q ^ 3 + 4 * q ^ 2 - 9 * q + 18) * ⟪m2, m3⟫ + (9 - 3 * q) * ⟪m3, m3⟫ := by
  have ht : 0 ≤ q - 1 := sub_nonneg.2 hq1
  have hF : 0 < q ^ 5 - 5 * q ^ 4 + 19 * q ^ 3 - 51 * q ^ 2 + 96 * q - 36 := by
    nlinarith [mul_nonneg ht (by linarith : (0 : ℝ) ≤ 36 - 14 * (q - 1)), pow_nonneg ht 3,
      pow_nonneg ht 5]
  have hC : 0 < q ^ 3 - 3 * q ^ 2 + 15 * q - 9 := by nlinarith [pow_nonneg ht 3]
  have h1 := real_inner_self_nonneg
    (x :=
      (-q ^ 3 + 3 * q ^ 2 - 3 * q + 9 : ℝ) • m0 + (-q ^ 3 + 3 * q ^ 2 - 9 * q + 27 : ℝ) • m1
        + (6 * q ^ 2 - 6 * q + 36 : ℝ) • m2 + (36 : ℝ) • m3)
  have h2 := real_inner_self_nonneg
    (x :=
      (-q ^ 6 + 7 * q ^ 5 - 24 * q ^ 4 + 66 * q ^ 3 - 153 * q ^ 2 + 63 * q - 54 : ℝ) • m0
        + (-q ^ 6 + 7 * q ^ 5 - 30 * q ^ 4 + 120 * q ^ 3 - 207 * q ^ 2 + 441 * q - 378 : ℝ) • m1
        + (6 * q ^ 5 - 30 * q ^ 4 + 114 * q ^ 3 - 306 * q ^ 2 + 576 * q - 216 : ℝ) • m2)
  have h3 := real_inner_self_nonneg
    (x :=
      (-q ^ 2 + 2 * q - 3 : ℝ) • m0 + (q ^ 2 - 9 : ℝ) • m1)
  have h := add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 3 - q)
    hF.le) h1) h2) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24)
    (by positivity : (0 : ℝ) ≤ q ^ 2 + 9)) hC.le) h3)
  rw [← sub_nonneg]
  refine nonneg_of_mul_nonneg_right ?_ (mul_pos (by norm_num : (0 : ℝ) < 432) hF)
  convert h using 1
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm m0 m1, real_inner_comm m0 m2, real_inner_comm m0 m3,
    real_inner_comm m1 m2, real_inner_comm m1 m3, real_inner_comm m2 m3]
  ring

/-- **The three-step certificate for one client on the range `5/3 ≤ λ β ≤ 15/8`.** With
`λ β = (q² + 9)/6`, `1 ≤ q ≤ 3/2`, and the weights `(3 + q)(q - 1)`, `(3 - q)²`, `(3 + q)(3 - q)`
the weighted sum of the five gradient inequalities is bounded below by
`(q + 3)(3 - 2q)(q² + 9)/9 ‖m₀‖²` plus terms that are linear in the deviations `p_k - m_k`. -/
lemma fedThree_client_form_ge_of_sq (p0 p1 p2 p3 m0 m1 m2 m3 : E) {q : ℝ} (hq : q ≤ 3 / 2)
    (hq1 : 1 ≤ q) :
    (-2 * q ^ 4 / 9 - q ^ 3 / 3 - q ^ 2 - 3 * q + 9) * ‖m0‖ ^ 2
      + (⟪p0 - m0,
          (2 * q ^ 2 - 2 * q + 12 : ℝ) • m0
            + (-q ^ 4 / 6 - q ^ 3 / 3 - q ^ 2 - 5 * q - 3 / 2 : ℝ) • m1
            + (-q ^ 3 / 3 - 2 * q ^ 2 - 5 * q - 6 : ℝ) • m2
            + (-q ^ 4 / 6 - q ^ 2 + 6 * q + 9 / 2 : ℝ) • m3⟫
        + ⟪p1 - m1,
          (-q ^ 4 / 6 - 2 * q + 15 / 2 : ℝ) • m0 + (4 * q + 12 : ℝ) • m1
            + (q ^ 3 / 3 + q ^ 2 + q + 3 : ℝ) • m2 + (q ^ 4 / 6 - 27 / 2 : ℝ) • m3⟫
        + ⟪p2 - m2,
          (-q ^ 2 - 2 * q + 3 : ℝ) • m0 + (q ^ 3 / 3 + q ^ 2 + q + 3 : ℝ) • m1
            + (4 * q + 12 : ℝ) • m2 + (q ^ 2 - 9 : ℝ) • m3⟫
        + ⟪p3 - m3,
          (q ^ 4 / 6 - q ^ 3 + 2 * q ^ 2 - 3 * q + 9 / 2 : ℝ) • m0
            + (q ^ 4 / 6 - q ^ 3 + 3 * q ^ 2 - 9 * q + 27 / 2 : ℝ) • m1
            + (-q ^ 3 + 4 * q ^ 2 - 9 * q + 18 : ℝ) • m2 + (18 - 6 * q : ℝ) • m3⟫) ≤
      (q ^ 2 + 9) / 6 * (((3 + q) * (q - 1) + (3 + q) * (3 - q)) * ⟪p1, m0⟫
          + ((3 + q) * (q - 1) + (3 + q) * (3 - q)) * ⟪p2, p1 - p0 + m0⟫
          + (3 + q) * (q - 1) * ⟪p0, -(m0 + (p1 - p0 + m0))⟫ + (3 - q) ^ 2 * ⟪p3, m0 + m1 + m2⟫
          + (3 + q) * (3 - q) * ⟪p3, m1 + m2 - m0 - p1 + p0⟫)
        + 1 / 2 * (((3 + q) * (q - 1) + (3 + q) * (3 - q)) * ‖p0 - p1‖ ^ 2
          + ((3 + q) * (q - 1) + (3 + q) * (3 - q)) * ‖p1 - p2‖ ^ 2
          + (3 + q) * (q - 1) * ‖p2 - p0‖ ^ 2 + (3 - q) ^ 2 * ‖p0 - p3‖ ^ 2
          + (3 + q) * (3 - q) * ‖p2 - p3‖ ^ 2) := by
  have hd := fedThree_deviation_form_nonneg_of_sq (p0 - m0) (p1 - m1) (p2 - m2) (p3 - m3) hq hq1
  have hm := fedThree_mean_form_ge_of_sq m0 m1 m2 m3 hq hq1
  have key : (q ^ 2 + 9) / 6 * (((3 + q) * (q - 1) + (3 + q) * (3 - q)) * ⟪p1, m0⟫
          + ((3 + q) * (q - 1) + (3 + q) * (3 - q)) * ⟪p2, p1 - p0 + m0⟫
          + (3 + q) * (q - 1) * ⟪p0, -(m0 + (p1 - p0 + m0))⟫ + (3 - q) ^ 2 * ⟪p3, m0 + m1 + m2⟫
          + (3 + q) * (3 - q) * ⟪p3, m1 + m2 - m0 - p1 + p0⟫)
        + 1 / 2 * (((3 + q) * (q - 1) + (3 + q) * (3 - q)) * ⟪p0 - p1, p0 - p1⟫
          + ((3 + q) * (q - 1) + (3 + q) * (3 - q)) * ⟪p1 - p2, p1 - p2⟫
          + (3 + q) * (q - 1) * ⟪p2 - p0, p2 - p0⟫ + (3 - q) ^ 2 * ⟪p0 - p3, p0 - p3⟫
          + (3 + q) * (3 - q) * ⟪p2 - p3, p2 - p3⟫)
      = (
        (q ^ 4 / 6 + q ^ 3 / 3 + 2 * q ^ 2 + 2 * q + 3 / 2) * ⟪(p0 - m0), (p0 - m0)⟫
          + (-q ^ 4 / 6 - q ^ 3 / 3 - q ^ 2 - 5 * q - 3 / 2) * ⟪(p0 - m0), (p1 - m1)⟫
          + (-q ^ 3 / 3 - 2 * q ^ 2 - 5 * q - 6) * ⟪(p0 - m0), (p2 - m2)⟫
          + (-q ^ 4 / 6 - q ^ 2 + 6 * q + 9 / 2) * ⟪(p0 - m0), (p3 - m3)⟫
          + (2 * q + 6) * ⟪(p1 - m1), (p1 - m1)⟫
          + (q ^ 3 / 3 + q ^ 2 + q + 3) * ⟪(p1 - m1), (p2 - m2)⟫
          + (q ^ 4 / 6 - 27 / 2) * ⟪(p1 - m1), (p3 - m3)⟫
          + (2 * q + 6) * ⟪(p2 - m2), (p2 - m2)⟫ + (q ^ 2 - 9) * ⟪(p2 - m2), (p3 - m3)⟫
          + (9 - 3 * q) * ⟪(p3 - m3), (p3 - m3)⟫)
        + (
        (-q ^ 4 / 6 - q ^ 3 / 3 - 4 * q + 21 / 2) * ⟪m0, m0⟫
          + (-q ^ 4 / 6 - 2 * q + 15 / 2) * ⟪m0, m1⟫ + (-q ^ 2 - 2 * q + 3) * ⟪m0, m2⟫
          + (q ^ 4 / 6 - q ^ 3 + 2 * q ^ 2 - 3 * q + 9 / 2) * ⟪m0, m3⟫ + (2 * q + 6) * ⟪m1, m1⟫
          + (q ^ 3 / 3 + q ^ 2 + q + 3) * ⟪m1, m2⟫
          + (q ^ 4 / 6 - q ^ 3 + 3 * q ^ 2 - 9 * q + 27 / 2) * ⟪m1, m3⟫
          + (2 * q + 6) * ⟪m2, m2⟫ + (-q ^ 3 + 4 * q ^ 2 - 9 * q + 18) * ⟪m2, m3⟫
          + (9 - 3 * q) * ⟪m3, m3⟫)
        + (⟪p0 - m0,
          (2 * q ^ 2 - 2 * q + 12 : ℝ) • m0
            + (-q ^ 4 / 6 - q ^ 3 / 3 - q ^ 2 - 5 * q - 3 / 2 : ℝ) • m1
            + (-q ^ 3 / 3 - 2 * q ^ 2 - 5 * q - 6 : ℝ) • m2
            + (-q ^ 4 / 6 - q ^ 2 + 6 * q + 9 / 2 : ℝ) • m3⟫
        + ⟪p1 - m1,
          (-q ^ 4 / 6 - 2 * q + 15 / 2 : ℝ) • m0 + (4 * q + 12 : ℝ) • m1
            + (q ^ 3 / 3 + q ^ 2 + q + 3 : ℝ) • m2 + (q ^ 4 / 6 - 27 / 2 : ℝ) • m3⟫
        + ⟪p2 - m2,
          (-q ^ 2 - 2 * q + 3 : ℝ) • m0 + (q ^ 3 / 3 + q ^ 2 + q + 3 : ℝ) • m1
            + (4 * q + 12 : ℝ) • m2 + (q ^ 2 - 9 : ℝ) • m3⟫
        + ⟪p3 - m3,
          (q ^ 4 / 6 - q ^ 3 + 2 * q ^ 2 - 3 * q + 9 / 2 : ℝ) • m0
            + (q ^ 4 / 6 - q ^ 3 + 3 * q ^ 2 - 9 * q + 27 / 2 : ℝ) • m1
            + (-q ^ 3 + 4 * q ^ 2 - 9 * q + 18 : ℝ) • m2 + (18 - 6 * q : ℝ) • m3⟫) := by
    simp only [inner_add_right, inner_sub_left, inner_sub_right, inner_neg_right,
      real_inner_smul_right]
    simp only [real_inner_comm p0 p1, real_inner_comm p0 p2, real_inner_comm p0 p3,
      real_inner_comm p1 p2, real_inner_comm p1 p3, real_inner_comm p2 p3,
      real_inner_comm m0 m1, real_inner_comm m0 m2, real_inner_comm m0 m3,
      real_inner_comm m1 m2, real_inner_comm m1 m3, real_inner_comm m2 m3,
      real_inner_comm p0 m0, real_inner_comm p1 m0, real_inner_comm p1 m1,
      real_inner_comm p2 m0, real_inner_comm p2 m1, real_inner_comm p2 m2,
      real_inner_comm p3 m0, real_inner_comm p3 m1, real_inner_comm p3 m2,
      real_inner_comm p3 m3]
    ring
  simp only [real_inner_self_eq_norm_sq] at key hm hd
  rw [key]
  linarith

/-- **Loss descent of the FeDLRT round with three local steps and averaged convex clients on the
range `5/3 ≤ λ β ≤ 15/8`.** Let the global loss be the average of convex client losses with
`β`-Lipschitz gradients and let `λ β = (q² + 9)/6` with `1 ≤ q ≤ 3/2`. Then
`ℒ(x⋆) ≤ ℒ(x) - (q + 3)(3 - 2q)(q² + 9) / (54 (3 - q) β) ‖Π ∇ℒ(x)‖²`. The constant vanishes at
`q = 3/2`, that is at `λ β = 15/8`. -/
theorem loss_fedRound_three_le_of_convex_of_sq [Fintype ι] [Nonempty ι]
    (hℒc : ∀ c x, HasFDerivAt (ℒc c) (innerSL ℝ (gc c x)) x)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hconv : ∀ c x y, ℒc c x + ⟪gc c x, y - x⟫ ≤ ℒc c y)
    (hP : IsOrthProj P) (hβ : 0 < β)
    (hℒmean : ∀ y, ℒ y = (Fintype.card ι : ℝ)⁻¹ * ∑ c, ℒc c y)
    (hmean : ∀ y, g y = (Fintype.card ι : ℝ)⁻¹ • ∑ c, gc c y) {q : ℝ} (hq1 : 1 ≤ q)
    (hq : q ≤ 3 / 2) (hlrq : lr * β = (q ^ 2 + 9) / 6) (x : E) :
    ℒ (fedRound P gc g lr 3 x) ≤
      ℒ x - (q + 3) * (3 - 2 * q) * (q ^ 2 + 9) / (54 * (3 - q) * β) * ‖P (g x)‖ ^ 2 := by
  have h3 : (0 : ℝ) < 3 - q := by linarith
  have hw : 0 < (3 - q) ^ 2 + (3 + q) * (3 - q) := by nlinarith
  have h := loss_fedRound_three_le_of_certificate (lr := lr) (b := (3 + q) * (q - 1))
    (c := (3 - q) ^ 2) (e := (3 + q) * (3 - q))
    (κ := -2 * q ^ 4 / 9 - q ^ 3 / 3 - q ^ 2 - 3 * q + 9) hℒc hgc hconv hP hβ hℒmean hmean
    (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _) (mul_nonneg (by linarith) h3.le) hw
    (fun m0 m1 m2 m3 => ⟨
        (2 * q ^ 2 - 2 * q + 12 : ℝ) • m0
          + (-q ^ 4 / 6 - q ^ 3 / 3 - q ^ 2 - 5 * q - 3 / 2 : ℝ) • m1
          + (-q ^ 3 / 3 - 2 * q ^ 2 - 5 * q - 6 : ℝ) • m2
          + (-q ^ 4 / 6 - q ^ 2 + 6 * q + 9 / 2 : ℝ) • m3,
        (-q ^ 4 / 6 - 2 * q + 15 / 2 : ℝ) • m0 + (4 * q + 12 : ℝ) • m1
          + (q ^ 3 / 3 + q ^ 2 + q + 3 : ℝ) • m2 + (q ^ 4 / 6 - 27 / 2 : ℝ) • m3,
        (-q ^ 2 - 2 * q + 3 : ℝ) • m0 + (q ^ 3 / 3 + q ^ 2 + q + 3 : ℝ) • m1
          + (4 * q + 12 : ℝ) • m2 + (q ^ 2 - 9 : ℝ) • m3,
        (q ^ 4 / 6 - q ^ 3 + 2 * q ^ 2 - 3 * q + 9 / 2 : ℝ) • m0
          + (q ^ 4 / 6 - q ^ 3 + 3 * q ^ 2 - 9 * q + 27 / 2 : ℝ) • m1
          + (-q ^ 3 + 4 * q ^ 2 - 9 * q + 18 : ℝ) • m2 + (18 - 6 * q : ℝ) • m3,
        fun p0 p1 p2 p3 => by
          rw [hlrq]
          exact fedThree_client_form_ge_of_sq p0 p1 p2 p3 m0 m1 m2 m3 hq hq1⟩) x
  have e : (-2 * q ^ 4 / 9 - q ^ 3 / 3 - q ^ 2 - 3 * q + 9)
      / (((3 - q) ^ 2 + (3 + q) * (3 - q)) * β)
      = (q + 3) * (3 - 2 * q) * (q ^ 2 + 9) / (54 * (3 - q) * β) := by
    rw [div_eq_div_iff (mul_pos hw hβ).ne' (mul_pos (mul_pos (by norm_num) h3) hβ).ne']
    ring
  rw [e] at h
  exact h

/-- **The FeDLRT round with three local steps and averaged convex clients decreases the loss
when `λ β < 15/8`**, that is `s⋆ λ β < 45/8`, and the projected gradient does not vanish. -/
theorem loss_fedRound_three_lt_of_convex [Fintype ι] [Nonempty ι]
    (hℒc : ∀ c x, HasFDerivAt (ℒc c) (innerSL ℝ (gc c x)) x)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hconv : ∀ c x y, ℒc c x + ⟪gc c x, y - x⟫ ≤ ℒc c y)
    (hP : IsOrthProj P) (hβ : 0 < β)
    (hℒmean : ∀ y, ℒ y = (Fintype.card ι : ℝ)⁻¹ * ∑ c, ℒc c y)
    (hmean : ∀ y, g y = (Fintype.card ι : ℝ)⁻¹ • ∑ c, gc c y) (hlr : 0 < lr)
    (hu : lr * β < 15 / 8) {x : E} (hx : P (g x) ≠ 0) :
    ℒ (fedRound P gc g lr 3 x) < ℒ x := by
  rcases le_or_gt (lr * β) (5 / 3) with h53 | h53
  · exact loss_fedRound_three_lt_of_convex_of_le hℒc hgc hconv hP hβ hℒmean hmean hlr h53 hx
  · obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = √(6 * (lr * β) - 9) := ⟨_, rfl⟩
    have hq2 : q ^ 2 = 6 * (lr * β) - 9 := by
      rw [hqdef, Real.sq_sqrt (by linarith)]
    have hq1 : 1 ≤ q := by
      rw [hqdef, Real.le_sqrt' one_pos]
      linarith
    have hq : q < 3 / 2 := by
      rw [hqdef, Real.sqrt_lt' (by norm_num)]
      linarith
    have hlrq : lr * β = (q ^ 2 + 9) / 6 := by
      rw [hq2]
      ring
    have h := loss_fedRound_three_le_of_convex_of_sq hℒc hgc hconv hP hβ hℒmean hmean hq1 hq.le
      hlrq x
    have hpos : 0 < (q + 3) * (3 - 2 * q) * (q ^ 2 + 9) / (54 * (3 - q) * β) * ‖P (g x)‖ ^ 2 :=
      mul_pos (div_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by positivity))
        (mul_pos (mul_pos (by norm_num) (by linarith)) hβ)) (pow_pos (norm_pos_iff.2 hx) 2)
    linarith

/-- **No descent at `λ β = 15/8`.** Take `45` clients, `32` with the loss `⟪v, y⟫ + ‖y‖² / 2`
(gradient `v + y`) and `13` with the loss `⟪v, y⟫` (gradient `v`); all are convex with
`1`-Lipschitz gradients, the global loss is `⟪v, y⟫ + (16/45) ‖y‖²` and its gradient
`v + (32/45) y` is the average of the client gradients. For `λ = 15/8` and `Π = 1` the round
with three local steps started at `0` ends at `-(45/16) v`, where the loss equals the loss
at `0`. -/
theorem loss_le_loss_fedRound_three_quadratic (v : E) :
    ⟪v, (0 : E)⟫ + 16 / 45 * ‖(0 : E)‖ ^ 2 ≤
      ⟪v, fedRound (1 : E →L[ℝ] E)
          (Sum.elim (fun _ : Fin 32 => fun z => v + z) (fun _ : Fin 13 => fun _ => v))
          (fun y => v + (32 / 45 : ℝ) • y) (15 / 8) 3 0⟫
        + 16 / 45 * ‖fedRound (1 : E →L[ℝ] E)
          (Sum.elim (fun _ : Fin 32 => fun z => v + z) (fun _ : Fin 13 => fun _ => v))
          (fun y => v + (32 / 45 : ℝ) • y) (15 / 8) 3 0‖ ^ 2 := by
  have hl : ∀ i : Fin 32, fedClientIter (1 : E →L[ℝ] E)
      (Sum.elim (fun _ : Fin 32 => fun z => v + z) (fun _ : Fin 13 => fun _ => v))
      (fun y => v + (32 / 45 : ℝ) • y) (15 / 8) 0 (Sum.inl i) 3 = -((855 / 512 : ℝ) • v) := by
    intro i
    simp only [fedClientIter, Sum.elim_inl, one_apply_eq_self, smul_zero, add_zero]
    module
  have hr : ∀ i : Fin 13, fedClientIter (1 : E →L[ℝ] E)
      (Sum.elim (fun _ : Fin 32 => fun z => v + z) (fun _ : Fin 13 => fun _ => v))
      (fun y => v + (32 / 45 : ℝ) • y) (15 / 8) 0 (Sum.inr i) 3 = -((45 / 8 : ℝ) • v) := by
    intro i
    simp only [fedClientIter, Sum.elim_inr, one_apply_eq_self, smul_zero, add_zero]
    module
  have e : fedRound (1 : E →L[ℝ] E)
      (Sum.elim (fun _ : Fin 32 => fun z => v + z) (fun _ : Fin 13 => fun _ => v))
      (fun y => v + (32 / 45 : ℝ) • y) (15 / 8) 3 0 = -((45 / 16 : ℝ) • v) := by
    rw [fedRound, Fintype.sum_sum_type]
    simp only [hl, hr, sum_const, card_univ, Fintype.card_fin, Fintype.card_sum]
    push_cast
    module
  rw [e, inner_zero_right, norm_zero, inner_neg_right, norm_neg, norm_smul,
    real_inner_smul_right, real_inner_self_eq_norm_sq, mul_pow, Real.norm_eq_abs, sq_abs]
  exact le_of_eq (by ring)

end FederatedThreeSteps

end LeanDLRA
