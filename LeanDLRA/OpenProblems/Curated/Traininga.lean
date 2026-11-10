import LeanDLRA.Training.Defs
import LeanDLRA.Training.Descent
import LeanDLRA.Matrix.Projectors

/-!
# Convergence of low-rank training: PL rates, lazy projectors, random subspaces, federated rounds

Convergence statements for training by projected gradient steps
`projGradStep Π g h x = x - h Π g(x)` with an orthogonal projector `Π`, on top of the descent
lemmas of `LeanDLRA/Training/Descent.lean`. The loss `ℒ` has the gradient `g`
(`HasFDerivAt ℒ (innerSL ℝ (g x)) x`), and `g` is `β`-Lipschitz where a step size condition
appears. The projector is the tangent or the augmented projector of dynamical low-rank training,
a projector that is refreshed only every `T` steps, a random projector, or the projector of a
federated round.

## Main results

* `loss_sub_le_exp_of_projGradFlow_PL`: along the projected gradient flow `ẏ = -Π(t) g(y)`, if
  `2 μ (ℒ(y) - ℒ⋆) ≤ ‖Π g(y)‖²`, then `ℒ(y t) - ℒ⋆ ≤ e^{-2 μ (t - a)} (ℒ(y a) - ℒ⋆)`.
* `loss_sub_le_pow_of_riemannianPL_truncated`: steps with an augmented projector `Q k` that
  fixes the tangent gradient `T k g(x k)`, followed by a truncation of size `ϑ`, satisfy under
  `2 μ (ℒ(x k) - ℒ⋆) ≤ ‖T k g(x k)‖²` the bound
  `ℒ(xₙ) - ℒ⋆ ≤ (1 - 2 μ c)ⁿ (ℒ(x₀) - ℒ⋆) + G ϑ / (2 μ c)`, `c = h (1 - β h / 2)`, where `G`
  bounds the gradient on the truncation segments.
* `loss_sub_le_of_riemannianPL_truncated`: the same statement with the additional hypothesis
  `ℒ⋆ ≤ ℒ(x k)` for all `k`.
* `exists_grad_sq_le_of_lazyRefresh`: if the projector `R j` is kept for the `T` steps after the
  refresh iterate `x (j T)`, captures the fraction `γ` of the gradient energy there, and
  `2 T β h ≤ 1`, then `γ ‖g(x (j T))‖² ≤ 8 (ℒ(x₀) - ℒ_inf) / (n T h)` for some `j < n`.
* `sum_loss_projGradStep_le_of_isotropic`: for a random projector `Π_ξ` with law `p` and
  `∑ p_ξ Π_ξ = γ · 1`, the expected loss after one step is at most
  `ℒ(x) - h (1 - β h / 2) γ ‖g(x)‖²`.
* `exists_leftProj_energy_ge`: for every `G ∈ ℝ^{m×n}` and `r ≤ m` there is `U` with `r`
  orthonormal columns and `r ‖G‖² ≤ m ‖leftProj U G‖²`.
* `loss_fedAvgRound_le`: for the federated round without variance correction (`fedAvgRound`),
  client gradients within `ζ` of their average `g` and `λ β s⋆ ≤ 1`, with `A = s⋆ λ`,
  `ℒ(x⁺) ≤ ℒ(x) - A (1 - 20 A β) ‖Π g(x)‖² + 17 β A² ζ²`. The round with variance correction
  has no `ζ` term (`loss_fedRound_le`).

## References

* arXiv 2307.05695 (ReLoRA) and arXiv 2403.03507 (GaLore): projectors refreshed every `T` steps;
  arXiv 2607.05872: their analysis.
* arXiv 2401.03748 (CoLR): random subspaces.
* arXiv 2406.17887 (FeDLRT): federated dynamical low-rank training, Sec. 3.1.
-/

open Set Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section PL

variable {ℒ : E → ℝ} {g : E → E} {β : ℝ}

/-- **Exponential loss decay of the DLRT gradient flow under a Riemannian PL inequality**
(source: research idea; continuous counterpart of OP-TR-05 and OP-TR-02 (ii)). If along the
projected gradient flow `ẏ = -Π(t) ∇ℒ(y)` (e.g. `Π(t) = P(y t)`, the low-rank gradient flow) the
projected gradient dominates the optimality gap, `2μ (ℒ(y) - ℒ⋆) ≤ ‖Π ∇ℒ(y)‖²`, then the gap
decays like `e^{-2μ(t-a)}`. -/
theorem loss_sub_le_exp_of_projGradFlow_PL (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    {P : ℝ → E →L[ℝ] E} (hP : ∀ t, IsOrthProj (P t)) {y : ℝ → E} {a b : ℝ}
    (hyc : ContinuousOn y (Icc a b))
    (hy : ∀ t ∈ Ico a b, HasDerivWithinAt y (-P t (g (y t))) (Ici t) t) {μ ℒstar : ℝ}
    (hPL : ∀ t ∈ Ico a b, 2 * μ * (ℒ (y t) - ℒstar) ≤ ‖P t (g (y t))‖ ^ 2) :
    ∀ t ∈ Icc a b, ℒ (y t) - ℒstar ≤ Real.exp (-(2 * μ) * (t - a)) * (ℒ (y a) - ℒstar) := by
  have hℒc : Continuous ℒ := continuous_iff_continuousAt.2 fun x => (hℒ x).continuousAt
  have hLc : ContinuousOn (fun t => ℒ (y t)) (Icc a b) := hℒc.comp_continuousOn hyc
  have hL' : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => ℒ (y t)) (-‖P t (g (y t))‖ ^ 2)
      (Ici t) t := by
    intro t ht
    have h1 := (hℒ (y t)).comp_hasDerivWithinAt t (hy t ht)
    have h2 : innerSL ℝ (g (y t)) (-P t (g (y t))) = -‖P t (g (y t))‖ ^ 2 := by
      rw [innerSL_apply_apply, inner_neg_right, real_inner_comm, (hP t).inner_self_apply]
    rwa [h2] at h1
  set ψ : ℝ → ℝ := fun t => Real.exp (2 * μ * (t - a)) * (ℒ (y t) - ℒstar) with hψ
  have hE : ∀ t, HasDerivAt (fun t => Real.exp (2 * μ * (t - a))) (Real.exp (2 * μ * (t - a)) *
      (2 * μ)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => 2 * μ * (t - a)) (2 * μ) t := by
      simpa using ((hasDerivAt_id t).sub_const a).const_mul (2 * μ)
    exact h1.exp
  have hψc : ContinuousOn ψ (Icc a b) := by
    refine ContinuousOn.mul ?_ (hLc.sub continuousOn_const)
    have hc : Continuous fun t : ℝ => 2 * μ * (t - a) := by fun_prop
    exact (Real.continuous_exp.comp hc).continuousOn
  have hψ' : ∀ t ∈ Ico a b, HasDerivWithinAt ψ (Real.exp (2 * μ * (t - a)) *
      (2 * μ * (ℒ (y t) - ℒstar) - ‖P t (g (y t))‖ ^ 2)) (Ici t) t := by
    intro t ht
    have := ((hE t).hasDerivWithinAt (s := Ici t)).mul ((hL' t ht).sub_const ℒstar)
    convert this using 1
    ring
  have hle : ∀ t ∈ Icc a b, ψ t ≤ ψ a := by
    intro t ht
    refine image_le_of_deriv_right_le_deriv_boundary (f := ψ) hψc hψ' (B := fun _ => ψ a)
      (B' := fun _ => 0) le_rfl continuousOn_const (fun x _ => hasDerivWithinAt_const _ _ _)
      (fun x hx => ?_) ht
    have := hPL x hx
    have h0 := Real.exp_pos (2 * μ * (x - a))
    exact mul_nonpos_of_nonneg_of_nonpos h0.le (by linarith)
  intro t ht
  have := hle t ht
  simp only [hψ, sub_self, mul_zero, Real.exp_zero, one_mul] at this
  have h0 := Real.exp_pos (2 * μ * (t - a))
  have e : Real.exp (-(2 * μ) * (t - a)) * Real.exp (2 * μ * (t - a)) = 1 := by
    rw [← Real.exp_add]; simp
  calc ℒ (y t) - ℒstar = Real.exp (-(2 * μ) * (t - a)) *
        (Real.exp (2 * μ * (t - a)) * (ℒ (y t) - ℒstar)) := by rw [← mul_assoc, e, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left this (Real.exp_pos _).le

/-- **Linear convergence of truncated DLRT / GeoLoRA under a Riemannian PL inequality, for any
reference value `ℒ⋆`** (the statement of `loss_sub_le_of_riemannianPL_truncated`, whose docstring
names the sources, without the hypothesis `ℒ⋆ ≤ ℒ(x_k)`). Augmented steps
`x̂ = x - h Q_k ∇ℒ(x)` whose augmented projector `Q_k` absorbs the tangent gradient
`T_k ∇ℒ(x_k)`, followed by a truncation of size `ϑ`, satisfy under
`2μ (ℒ(x_k) - ℒ⋆) ≤ ‖T_k ∇ℒ(x_k)‖²` the bound
`ℒ(x_n) - ℒ⋆ ≤ (1 - 2μc)^n (ℒ(x₀) - ℒ⋆) + G ϑ / (2μc)` with `c = h (1 - β h / 2)`. The number
`ℒ⋆` is any real number for which the PL inequality holds along the iteration; that it is a
lower bound of the loss is not assumed. -/
theorem loss_sub_le_pow_of_riemannianPL_truncated
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {T Q : ℕ → E →L[ℝ] E}
    (hT : ∀ k, IsOrthProj (T k)) (hQ : ∀ k, IsOrthProj (Q k)) {x : ℕ → E}
    (habs : ∀ k, Q k (T k (g (x k))) = T k (g (x k))) {h ϑ G μ ℒstar : ℝ}
    (htr : ∀ k, ‖x (k + 1) - projGradStep (Q k) g h (x k)‖ ≤ ϑ)
    (hG : ∀ k, ∀ w ∈ segment ℝ (projGradStep (Q k) g h (x k)) (x (k + 1)), ‖g w‖ ≤ G)
    (hPL : ∀ k, 2 * μ * (ℒ (x k) - ℒstar) ≤ ‖T k (g (x k))‖ ^ 2)
    (hμ : 0 < μ) (hh : 0 < h * (1 - β * h / 2))
    (hq : 2 * μ * (h * (1 - β * h / 2)) ≤ 1) (n : ℕ) :
    ℒ (x n) - ℒstar ≤ (1 - 2 * μ * (h * (1 - β * h / 2))) ^ n * (ℒ (x 0) - ℒstar) +
      G * ϑ / (2 * μ * (h * (1 - β * h / 2))) := by
  set c : ℝ := h * (1 - β * h / 2) with hc
  have hq0 : 0 < 2 * μ * c := by positivity
  set q : ℝ := 2 * μ * c with hqdef
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0 _ (left_mem_segment ℝ _ _))
  have hϑ0 : 0 ≤ ϑ := (norm_nonneg _).trans (htr 0)
  have hD : 0 ≤ G * ϑ := mul_nonneg hG0 hϑ0
  have hstep : ∀ k, ℒ (x (k + 1)) - ℒstar ≤ (1 - q) * (ℒ (x k) - ℒstar) + G * ϑ := by
    intro k
    have h1 := loss_truncated_projGradStep_le hℒ hg (hQ k) h (x k) (htr k) (hG k)
    have h2 : ‖T k (g (x k))‖ ≤ ‖Q k (g (x k))‖ := norm_apply_le_of_absorbs (hT k) (hQ k) (habs k)
    have h3 : ‖T k (g (x k))‖ ^ 2 ≤ ‖Q k (g (x k))‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have h4 := mul_le_mul_of_nonneg_left (hPL k) hh.le
    have h5 := mul_le_mul_of_nonneg_left h3 hh.le
    rw [hqdef]
    nlinarith
  have key : ∀ n : ℕ, ℒ (x n) - ℒstar ≤ (1 - q) ^ n * (ℒ (x 0) - ℒstar) +
      G * ϑ * (1 - (1 - q) ^ n) / q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hq1 : 0 ≤ 1 - q := by linarith
      have h1 := mul_le_mul_of_nonneg_left ih hq1
      have h2 := hstep n
      have h3 : (1 - q) * ((1 - q) ^ n * (ℒ (x 0) - ℒstar) + G * ϑ * (1 - (1 - q) ^ n) / q) +
          G * ϑ = (1 - q) ^ (n + 1) * (ℒ (x 0) - ℒstar) +
            G * ϑ * (1 - (1 - q) ^ (n + 1)) / q := by
        field_simp
        ring
      linarith
  have := key n
  have hr : 0 ≤ (1 - q) ^ n := pow_nonneg (by linarith) n
  have h6 : G * ϑ * (1 - (1 - q) ^ n) / q ≤ G * ϑ / q := by
    apply div_le_div_of_nonneg_right _ hq0.le
    nlinarith
  linarith

/-- **Linear convergence of truncated DLRT / GeoLoRA under a Riemannian PL inequality**
(source: research idea; OP-HO-14, OP-TR-30). Augmented steps `x̂ = x - h Q_k ∇ℒ(x)` whose
augmented projector `Q_k` absorbs the tangent gradient `T_k ∇ℒ(x_k)`, followed by a truncation of
size `ϑ`, converge linearly to a `G ϑ`-neighbourhood of the optimal value when
`2μ (ℒ(x_k) - ℒ⋆) ≤ ‖T_k ∇ℒ(x_k)‖²`:
`ℒ(x_n) - ℒ⋆ ≤ (1 - 2μc)^n (ℒ(x₀) - ℒ⋆) + G ϑ / (2μc)` with `c = h (1 - β h / 2)`.
This is the recorded form of the statement, with the redundant hypothesis `ℒ⋆ ≤ ℒ(x_k)`;
`loss_sub_le_pow_of_riemannianPL_truncated` is the same statement without it. -/
theorem loss_sub_le_of_riemannianPL_truncated (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {T Q : ℕ → E →L[ℝ] E}
    (hT : ∀ k, IsOrthProj (T k)) (hQ : ∀ k, IsOrthProj (Q k)) {x : ℕ → E}
    (habs : ∀ k, Q k (T k (g (x k))) = T k (g (x k))) {h ϑ G μ ℒstar : ℝ}
    (htr : ∀ k, ‖x (k + 1) - projGradStep (Q k) g h (x k)‖ ≤ ϑ)
    (hG : ∀ k, ∀ w ∈ segment ℝ (projGradStep (Q k) g h (x k)) (x (k + 1)), ‖g w‖ ≤ G)
    (hPL : ∀ k, 2 * μ * (ℒ (x k) - ℒstar) ≤ ‖T k (g (x k))‖ ^ 2)
    (hstar : ∀ k, ℒstar ≤ ℒ (x k)) (hμ : 0 < μ) (hh : 0 < h * (1 - β * h / 2))
    (hq : 2 * μ * (h * (1 - β * h / 2)) ≤ 1) (n : ℕ) :
    ℒ (x n) - ℒstar ≤ (1 - 2 * μ * (h * (1 - β * h / 2))) ^ n * (ℒ (x 0) - ℒstar) +
      G * ϑ / (2 * μ * (h * (1 - β * h / 2))) := by
  have _ := hstar 0
  exact loss_sub_le_pow_of_riemannianPL_truncated hℒ hg hT hQ habs htr hG hPL hμ hh hq n

end PL

section Refresh

variable {ℒ : E → ℝ} {g : E → E} {β : ℝ}

private theorem lazy_block_descent (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {R : E →L[ℝ] E} (hR : IsOrthProj R)
    {T : ℕ} (hT : 0 < T) {h : ℝ} (hh : 0 < h) (hTh : 2 * T * β * h ≤ 1) {y : ℕ → E}
    (hy : ∀ i < T, y (i + 1) = projGradStep R g h (y i)) :
    (T * h / 8) * ‖R (g (y 0))‖ ^ 2 ≤ ℒ (y 0) - ℒ (y T) := by
  set v : ℕ → ℝ := fun i => ‖R (g (y i))‖ with hv
  set a : ℝ := ‖R (g (y 0))‖ with ha
  have hv0 : ∀ i, 0 ≤ v i := fun i => norm_nonneg _
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hβh : 0 ≤ β * h := mul_nonneg hβ hh.le
  have hTβh : (T : ℝ) * (β * h) ≤ 1 / 2 := by nlinarith
  have hβh2 : β * h ≤ 1 / 2 := by nlinarith
  -- descent
  have hdesc : ∀ i < T, h * (1 - β * h / 2) * v i ^ 2 ≤ ℒ (y i) - ℒ (y (i + 1)) := by
    intro i hi
    have := loss_projGradStep_le hℒ hg hR h (y i)
    rw [← hy i hi] at this
    simp only [hv]
    linarith
  have hsumdesc : h * (1 - β * h / 2) * ∑ i ∈ range T, v i ^ 2 ≤ ℒ (y 0) - ℒ (y T) := by
    rw [mul_sum]
    calc ∑ i ∈ range T, h * (1 - β * h / 2) * v i ^ 2
        ≤ ∑ i ∈ range T, (ℒ (y i) - ℒ (y (i + 1))) :=
          sum_le_sum fun i hi => hdesc i (mem_range.1 hi)
      _ = ℒ (y 0) - ℒ (y T) := sum_range_sub' (fun i => ℒ (y i)) T
  -- displacement
  have hdisp : ∀ i ≤ T, ‖y i - y 0‖ ≤ h * ∑ l ∈ range i, v l := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have hi' : i < T := hi
      have ih' := ih hi'.le
      have : y (i + 1) - y 0 = (y i - y 0) - h • R (g (y i)) := by
        rw [hy i hi', projGradStep]; abel
      rw [this, sum_range_succ, mul_add]
      calc ‖(y i - y 0) - h • R (g (y i))‖ ≤ ‖y i - y 0‖ + ‖h • R (g (y i))‖ := norm_sub_le _ _
        _ ≤ _ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
          linarith
  set S : ℝ := ∑ l ∈ range T, v l with hS
  have hS0 : 0 ≤ S := sum_nonneg fun l _ => hv0 l
  have hpers : ∀ i < T, a ≤ v i + β * h * S := by
    intro i hi
    have h1 : R (g (y 0)) = R (g (y i)) - R (g (y i) - g (y 0)) := by rw [map_sub]; abel
    have h2 : a ≤ v i + ‖g (y i) - g (y 0)‖ := by
      calc a = ‖R (g (y i)) - R (g (y i) - g (y 0))‖ := by rw [ha, h1]
        _ ≤ ‖R (g (y i))‖ + ‖R (g (y i) - g (y 0))‖ := norm_sub_le _ _
        _ ≤ v i + ‖g (y i) - g (y 0)‖ := add_le_add le_rfl (hR.norm_le _)
    have h3 := hg (y i) (y 0)
    have h4 := hdisp i hi.le
    have h5 : ∑ l ∈ range i, v l ≤ S :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hi.le) fun l _ _ => hv0 l
    have h6 := mul_le_mul_of_nonneg_left h4 hβ
    have h7 := mul_le_mul_of_nonneg_left h5 hh.le
    have h8 := mul_le_mul_of_nonneg_left h7 hβ
    nlinarith
  have hsumv : (T : ℝ) * a ≤ S + T * (β * h) * S := by
    have := sum_le_sum (s := range T) (fun i hi => hpers i (mem_range.1 hi))
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, sum_const, card_range,
      nsmul_eq_mul] at this
    linarith
  have hS2 : 2 * T * a / 3 ≤ S := by nlinarith
  have hCS : S ^ 2 ≤ T * ∑ i ∈ range T, v i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := range T) (f := v)
    rwa [card_range] at this
  have ha0 : 0 ≤ a := norm_nonneg _
  have hsq : (2 * T * a / 3) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (by positivity) hS2 2
  have hQ : 4 * T * a ^ 2 / 9 ≤ ∑ i ∈ range T, v i ^ 2 := by
    have hT0 : (0 : ℝ) < T := by linarith
    by_contra hcon
    rw [not_le] at hcon
    have := mul_lt_mul_of_pos_left hcon hT0
    nlinarith
  have hc : 3 * h / 4 ≤ h * (1 - β * h / 2) := by nlinarith
  have hQ0 : 0 ≤ ∑ i ∈ range T, v i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  have h9 := mul_le_mul hc hQ (by positivity) (by nlinarith)
  have h10 : 0 ≤ (T : ℝ) * h * a ^ 2 := by positivity
  nlinarith

/-- **Convergence with lazily refreshed projectors** (source: GaLore arXiv 2403.03507 and
ReLoRA arXiv 2307.05695 as analysed in arXiv 2607.05872; OP-RS-28, OP-TR-29). The projector
`R_j` is computed once at the refresh iterate `x_{jT}` and kept for the `T` steps
`x_{k+1} = x_k - h R_{⌊k/T⌋} ∇ℒ(x_k)`. If it captures a fraction `γ` of the gradient energy at
the refresh time and `2 T β h ≤ 1`, then some refresh iterate satisfies
`γ ‖∇ℒ(x_{jT})‖² ≤ 8 (ℒ(x₀) - ℒ_inf) / (n T h)`. (For ReLoRA / LoRA-FA with an orthonormal
frozen factor `A_j`, `R_j = rightProj A_jᵀ`.) -/
theorem exists_grad_sq_le_of_lazyRefresh (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {R : ℕ → E →L[ℝ] E}
    (hR : ∀ j, IsOrthProj (R j)) {T : ℕ} (hT : 0 < T) {h γ ℒinf : ℝ} (hh : 0 < h)
    (hTh : 2 * T * β * h ≤ 1) {x : ℕ → E}
    (hx : ∀ k, x (k + 1) = projGradStep (R (k / T)) g h (x k))
    (hcap : ∀ j, γ * ‖g (x (j * T))‖ ^ 2 ≤ ‖R j (g (x (j * T)))‖ ^ 2)
    (hinf : ∀ k, ℒinf ≤ ℒ (x k)) {n : ℕ} (hn : 0 < n) :
    ∃ j < n, γ * ‖g (x (j * T))‖ ^ 2 ≤ 8 * (ℒ (x 0) - ℒinf) / (n * T * h) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hblock : ∀ j, (T * h / 8) * (γ * ‖g (x (j * T))‖ ^ 2) ≤
      ℒ (x (j * T)) - ℒ (x ((j + 1) * T)) := by
    intro j
    have := lazy_block_descent (ℒ := ℒ) (y := fun i => x (j * T + i)) hℒ hg hβ (hR j) hT hh hTh
      (fun i hi => by
        have e : (j * T + i) / T = j := by
          rw [mul_comm j T, Nat.mul_add_div hT, Nat.div_eq_of_lt hi, add_zero]
        simp only [← add_assoc]
        rw [hx, e])
    simp only [add_zero, add_mul, one_mul] at this ⊢
    have h2 := mul_le_mul_of_nonneg_left (hcap j) (by positivity : 0 ≤ (T : ℝ) * h / 8)
    linarith
  have hsum : (T * h / 8) * ∑ j ∈ range n, γ * ‖g (x (j * T))‖ ^ 2 ≤
      (ℒ (x 0) - ℒinf) + n * 0 := by
    rw [mul_sum]
    have := sum_le_sum (s := range n) (fun j _ => hblock j)
    rw [sum_range_sub' (fun j => ℒ (x (j * T))) n] at this
    simp only [zero_mul] at this
    have := hinf (n * T)
    linarith
  obtain ⟨j, hj, hle⟩ := exists_le_of_mul_sum_le (by positivity) hn hsum
  refine ⟨j, hj, hle.trans (le_of_eq ?_)⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp
  ring

/-- **Expected descent with isotropic random subspaces** (source: CoLR arXiv 2401.03748,
OP-TR-18; random-projection variants of GaLore and ReLoRA). If a random orthogonal projector
`Π_ξ` (law `p`) is isotropic, `E[Π_ξ] = γ I` (e.g. `γ = r/d` for a uniformly random
`r`-dimensional coordinate or Haar subspace), the expected loss after one projected step satisfies
`E ℒ(x - h Π_ξ ∇ℒ(x)) ≤ ℒ(x) - h (1 - β h / 2) γ ‖∇ℒ(x)‖²`. -/
theorem sum_loss_projGradStep_le_of_isotropic (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {Ξ : Type*} [Fintype Ξ] {P : Ξ → E →L[ℝ] E}
    (hP : ∀ ξ, IsOrthProj (P ξ)) {p : Ξ → ℝ} (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1)
    {γ : ℝ} (hiso : ∀ v, ∑ ξ, p ξ • P ξ v = γ • v) (h : ℝ) (x : E) :
    ∑ ξ, p ξ * ℒ (projGradStep (P ξ) g h x) ≤ ℒ x - h * (1 - β * h / 2) * γ * ‖g x‖ ^ 2 := by
  have h1 : ∀ ξ, p ξ * ℒ (projGradStep (P ξ) g h x) ≤
      p ξ * (ℒ x - h * (1 - β * h / 2) * ‖P ξ (g x)‖ ^ 2) := fun ξ =>
    mul_le_mul_of_nonneg_left (loss_projGradStep_le hℒ hg (hP ξ) h x) (hp ξ)
  have h2 : ∑ ξ, p ξ * ‖P ξ (g x)‖ ^ 2 = γ * ‖g x‖ ^ 2 := by
    have h3 : ∀ ξ, p ξ * ‖P ξ (g x)‖ ^ 2 = ⟪p ξ • P ξ (g x), g x⟫ := fun ξ => by
      rw [real_inner_smul_left, (hP ξ).inner_self_apply]
    simp_rw [h3]
    rw [← sum_inner, hiso, inner_smul_left, real_inner_self_eq_norm_sq]
    simp
  calc ∑ ξ, p ξ * ℒ (projGradStep (P ξ) g h x)
      ≤ ∑ ξ, p ξ * (ℒ x - h * (1 - β * h / 2) * ‖P ξ (g x)‖ ^ 2) := sum_le_sum fun ξ _ => h1 ξ
    _ = ℒ x - h * (1 - β * h / 2) * γ * ‖g x‖ ^ 2 := by
      have : ∀ ξ, p ξ * (ℒ x - h * (1 - β * h / 2) * ‖P ξ (g x)‖ ^ 2) =
          p ξ * ℒ x - h * (1 - β * h / 2) * (p ξ * ‖P ξ (g x)‖ ^ 2) := fun ξ => by ring
      simp_rw [this]
      rw [sum_sub_distrib, ← sum_mul, hp1, ← mul_sum, h2]; ring

end Refresh

section RefreshMatrix

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n]

private theorem coord_transpose_mul {r : ℕ} [DecidableEq m] (idx : Fin r → m)
    (hidx : Function.Injective idx) :
    (Matrix.of fun (i : m) (j : Fin r) => if i = idx j then (1 : ℝ) else 0)ᵀ *
      (Matrix.of fun (i : m) (j : Fin r) => if i = idx j then (1 : ℝ) else 0) = 1 := by
  ext j j'
  by_cases h : j = j'
  · subst h
    simp [Matrix.mul_apply]
  · have h' : ¬ j' = j := fun e => h e.symm
    simp [Matrix.mul_apply, h, h', hidx.eq_iff]

private theorem coord_leftProj_apply {r : ℕ} [DecidableEq m] (idx : Fin r → m)
    (G : Matrix m n ℝ) (i : m) (j' : n) :
    leftProj (Matrix.of fun (i : m) (j : Fin r) => if i = idx j then (1 : ℝ) else 0) G i j' =
      (∑ j, if i = idx j then (1 : ℝ) else 0) * G i j' := by
  simp only [leftProj_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j1 _ => ?_
  by_cases h : i = idx j1
  · subst h
    simp
  · simp [h]

private theorem norm_sq_coord_leftProj {r : ℕ} [DecidableEq m] (idx : Fin r → m)
    (hidx : Function.Injective idx) (G : Matrix m n ℝ) :
    ‖leftProj (Matrix.of fun (i : m) (j : Fin r) => if i = idx j then (1 : ℝ) else 0) G‖ ^ 2 =
      ∑ j, ∑ j', G (idx j) j' ^ 2 := by
  have hχ : ∀ i, (∑ j, if i = idx j then (1 : ℝ) else 0) =
      if i ∈ Finset.univ.image idx then 1 else 0 := by
    intro i
    by_cases h : i ∈ Finset.univ.image idx
    · obtain ⟨j0, _, rfl⟩ := mem_image.1 h
      simp only [h, ↓reduceIte]
      rw [sum_eq_single j0]
      · simp
      · intro j _ hj
        exact ite_eq_right_iff.2 fun e => absurd (hidx e.symm) hj
      · simp
    · simp only [h, ↓reduceIte]
      exact sum_eq_zero fun j _ =>
        ite_eq_right_iff.2 fun e => absurd (mem_image.2 ⟨j, mem_univ _, e.symm⟩) h
  rw [Frobenius.norm_sq_eq_sum]
  simp_rw [coord_leftProj_apply, hχ]
  calc ∑ i, ∑ j', ((if i ∈ Finset.univ.image idx then (1 : ℝ) else 0) * G i j') ^ 2
      = ∑ i, if i ∈ Finset.univ.image idx then ∑ j', G i j' ^ 2 else 0 :=
        sum_congr rfl fun i _ => by split_ifs <;> simp
    _ = ∑ i ∈ Finset.univ.image idx, ∑ j', G i j' ^ 2 := by
        rw [sum_ite_mem, Finset.univ_inter]
    _ = _ := sum_image fun a _ b _ h => hidx h

/-- **A rank-`r` left projector captures at least `r/m` of the gradient energy** (source:
GaLore arXiv 2403.03507 refresh step; arXiv 2607.05872, eq. (3); OP-RS-28). For every gradient
`G ∈ ℝ^{m×n}` and `r ≤ m` there is `U` with `r` orthonormal columns and
`r ‖G‖² ≤ m ‖U Uᵀ G‖²` (the top-`r` left singular vectors, or the best `r` coordinate rows,
achieve it). Combined with `exists_grad_sq_le_of_lazyRefresh` this gives GaLore convergence with
`γ = r/m`. -/
theorem exists_leftProj_energy_ge (G : Matrix m n ℝ) {r : ℕ} (hr : r ≤ Fintype.card m) :
    ∃ U : Matrix m (Fin r) ℝ, Uᵀ * U = 1 ∧
      (r : ℝ) * ‖G‖ ^ 2 ≤ Fintype.card m * ‖leftProj U G‖ ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card m) with hM | hM
  · obtain rfl : r = 0 := by omega
    refine ⟨0, ?_, ?_⟩
    · ext i
      exact i.elim0
    · simp [hM]
  · have : NeZero (Fintype.card m) := ⟨hM.ne'⟩
    set M := Fintype.card m with hMdef
    let e : m ≃ Fin M := Fintype.equivFin m
    let idx : Fin M → Fin r → m := fun k j => e.symm (k + Fin.castLE hr j)
    have hinj : ∀ k, Function.Injective (idx k) := by
      intro k j j' h
      have h1 := e.symm.injective h
      exact Fin.castLE_injective hr (add_left_cancel h1)
    let a : m → ℝ := fun i => ∑ j', G i j' ^ 2
    have hkey : ∀ k, ‖leftProj (Matrix.of fun (i : m) (j : Fin r) =>
        if i = idx k j then (1 : ℝ) else 0) G‖ ^ 2 = ∑ j, a (idx k j) :=
      fun k => norm_sq_coord_leftProj (idx k) (hinj k) G
    have htot : ∑ k : Fin M, ∑ j : Fin r, a (idx k j) = r * ‖G‖ ^ 2 := by
      rw [sum_comm, Frobenius.norm_sq_eq_sum]
      have : ∀ j : Fin r, ∑ k : Fin M, a (idx k j) = ∑ i, a i := fun j => by
        have h1 := Equiv.sum_comp (Equiv.addRight (Fin.castLE hr j)) (fun k => a (e.symm k))
        have h2 := Equiv.sum_comp e.symm a
        simp only [Equiv.coe_addRight] at h1
        exact h1.trans h2
      simp_rw [this]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rfl
    by_contra hcon
    have hlt : ∀ k : Fin M, (M : ℝ) * ‖leftProj (Matrix.of fun (i : m) (j : Fin r) =>
        if i = idx k j then (1 : ℝ) else 0) G‖ ^ 2 < r * ‖G‖ ^ 2 := by
      intro k
      by_contra hk
      exact hcon ⟨_, coord_transpose_mul (idx k) (hinj k), not_lt.1 hk⟩
    have hs := sum_lt_sum_of_nonempty (univ_nonempty (α := Fin M)) fun k _ => hlt k
    rw [← mul_sum] at hs
    simp_rw [hkey] at hs
    rw [htot] at hs
    simp at hs

end RefreshMatrix

section Precond

variable {ℒ : E → ℝ} {g : E → E} {β : ℝ}

end Precond

section Federated

variable {ι : Type*} {ℒ : E → ℝ} {g : E → E} {β lr : ℝ} {P : E →L[ℝ] E} {gc : ι → E → E}

private theorem fedAvgClientIter_sub_self (P : E →L[ℝ] E) (gc : ι → E → E) (lr : ℝ) (x : E)
    (c : ι) (s : ℕ) : fedAvgClientIter P gc lr x c s - x =
      -(lr • ∑ i ∈ range s, P (gc c (fedAvgClientIter P gc lr x c i))) := by
  induction s with
  | zero => simp [fedAvgClientIter]
  | succ s ih =>
    rw [sum_range_succ, smul_add, neg_add, ← ih]
    simp only [fedAvgClientIter]
    abel

private theorem norm_fedAvgClientIter_sub_le (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {ζ : ℝ} (x : E) (c : ι)
    (hζ : ‖gc c x - g x‖ ≤ ζ) (s : ℕ) :
    ‖fedAvgClientIter P gc lr x c s - x‖ ≤
      lr * (‖P (g x)‖ + ζ) * ∑ i ∈ range s, (1 + lr * β) ^ i := by
  induction s with
  | zero => simp [fedAvgClientIter]
  | succ s ih =>
    set z := fedAvgClientIter P gc lr x c s with hz
    have e1 : fedAvgClientIter P gc lr x c (s + 1) - x = (z - x) - lr • P (gc c z) := by
      simp only [fedAvgClientIter, hz]; abel
    have e2 : P (gc c z) = P (g x) + P (gc c z - gc c x) + P (gc c x - g x) := by
      rw [← map_add, ← map_add]; congr 1; abel
    have h1 : ‖P (gc c z)‖ ≤ ‖P (g x)‖ + β * ‖z - x‖ + ζ := by
      rw [e2]
      calc _ ≤ ‖P (g x) + P (gc c z - gc c x)‖ + ‖P (gc c x - g x)‖ := norm_add_le _ _
        _ ≤ ‖P (g x)‖ + ‖P (gc c z - gc c x)‖ + ‖P (gc c x - g x)‖ :=
          add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := by
          have := hP.norm_le (gc c z - gc c x)
          have := hgc c z x
          have := hP.norm_le (gc c x - g x)
          linarith
    have h2 : ‖fedAvgClientIter P gc lr x c (s + 1) - x‖ ≤ ‖z - x‖ + lr * ‖P (gc c z)‖ := by
      rw [e1]
      calc _ ≤ ‖z - x‖ + ‖lr • P (gc c z)‖ := norm_sub_le _ _
        _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlr]
    have h3 := mul_le_mul_of_nonneg_left h1 hlr
    have hsum : ∑ i ∈ range (s + 1), (1 + lr * β) ^ i =
        1 + (1 + lr * β) * ∑ i ∈ range s, (1 + lr * β) ^ i := by
      rw [sum_range_succ', mul_sum]
      simp only [pow_succ, pow_zero]
      rw [add_comm]
      congr 1
      exact sum_congr rfl fun i _ => by ring
    rw [hsum]
    have h5 := mul_le_mul_of_nonneg_left ih (by positivity : 0 ≤ 1 + lr * β)
    nlinarith

private theorem pow_one_add_le (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {sstar : ℕ}
    (hs : lr * β * sstar ≤ 1) {i : ℕ} (hi : i ≤ sstar) : (1 + lr * β) ^ i ≤ 68 / 25 := by
  have h1 : 1 + lr * β ≤ Real.exp (lr * β) := by linarith [Real.add_one_le_exp (lr * β)]
  have h2 : (1 + lr * β) ^ i ≤ Real.exp (lr * β) ^ i :=
    pow_le_pow_left₀ (by positivity) h1 i
  have h3 : Real.exp (lr * β) ^ i = Real.exp (i * (lr * β)) := (Real.exp_nat_mul _ _).symm
  have h4 : (i : ℝ) * (lr * β) ≤ 1 := by
    have : (i : ℝ) ≤ sstar := by exact_mod_cast hi
    nlinarith [mul_nonneg hlr hβ]
  have h5 : Real.exp (i * (lr * β)) ≤ Real.exp 1 := Real.exp_le_exp.2 h4
  have h6 := Real.exp_one_lt_d9
  linarith

private theorem norm_fedAvgClientIter_sub_le' (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {ζ : ℝ} (x : E) (c : ι)
    (hζ : ‖gc c x - g x‖ ≤ ζ) {sstar : ℕ} (hs : lr * β * sstar ≤ 1) {s : ℕ} (hsle : s ≤ sstar) :
    ‖fedAvgClientIter P gc lr x c s - x‖ ≤ 68 / 25 * (lr * sstar) * (‖P (g x)‖ + ζ) := by
  have h1 := norm_fedAvgClientIter_sub_le hgc hP hβ hlr x c hζ s
  have hζ0 : 0 ≤ ζ := (norm_nonneg _).trans hζ
  have hp : 0 ≤ lr * (‖P (g x)‖ + ζ) := by positivity
  have h2 : ∑ i ∈ range s, (1 + lr * β) ^ i ≤ 68 / 25 * sstar := by
    calc _ ≤ ∑ i ∈ range s, (68 / 25 : ℝ) :=
          sum_le_sum fun i hi => pow_one_add_le hβ hlr hs (by have := mem_range.1 hi; omega)
      _ = 68 / 25 * s := by simp [mul_comm]
      _ ≤ 68 / 25 * sstar := by
          have : (s : ℝ) ≤ sstar := by exact_mod_cast hsle
          linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hp
  calc _ ≤ _ := h1
    _ ≤ lr * (‖P (g x)‖ + ζ) * (68 / 25 * sstar) := h3
    _ = _ := by ring

/-- **Descent of uncorrected federated low-rank training up to a heterogeneity floor**
(source: arXiv 2406.17887 §3.1, FedAvg-type client update without variance correction;
OP-TR-11). If the global gradient is the client
average and client gradients deviate from it by at most `ζ`, then with `A = s⋆ λ`, `λ β s⋆ ≤ 1`,
`ℒ(x⁺) ≤ ℒ(x) - A (1 - 20 A β) ‖Π ∇ℒ(x)‖² + 17 β A² ζ²`. The `ζ²` term is the client drift that
the variance correction of FeDLRT removes (`loss_fedRound_le`). -/
theorem loss_fedAvgRound_le [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (havg : ∀ x, g x = (Fintype.card ι : ℝ)⁻¹ • ∑ c, gc c x) {ζ : ℝ}
    (hζ : ∀ c x, ‖gc c x - g x‖ ≤ ζ) (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 ≤ lr)
    {sstar : ℕ} (hs : lr * β * sstar ≤ 1) (x : E) :
    ℒ (fedAvgRound P gc lr sstar x) ≤
      ℒ x - sstar * lr * (1 - 20 * (sstar * lr) * β) * ‖P (g x)‖ ^ 2 +
        17 * β * (sstar * lr) ^ 2 * ζ ^ 2 := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  have hn : 0 < n := by
    have : 0 < Fintype.card ι := Fintype.card_pos
    rw [hn_def]
    exact_mod_cast this
  set z : ι → ℕ → E := fun c s => fedAvgClientIter P gc lr x c s with hz
  set p : ℝ := ‖P (g x)‖ with hp_def
  set A : ℝ := (sstar : ℝ) * lr with hA_def
  have hA0 : 0 ≤ A := by positivity
  have hp0 : 0 ≤ p := norm_nonneg _
  have hζ0 : 0 ≤ ζ := (norm_nonneg _).trans (hζ (Classical.arbitrary ι) x)
  have hsum_c : ∑ c, gc c x = n • g x := by
    have := havg x
    rw [this, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  set w' : E := lr • (n⁻¹ • ∑ c, ∑ s ∈ range sstar, (gc c (z c s) - gc c x)) with hw'
  have hδ : fedAvgRound P gc lr sstar x - x = -(A • P (g x)) - P w' := by
    have e1 : fedAvgRound P gc lr sstar x - x = n⁻¹ • ∑ c, (z c sstar - x) := by
      rw [sum_sub_distrib, smul_sub, sum_const, card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
        ← hn_def, inv_mul_cancel₀ hn.ne', one_smul]
      rfl
    have e2 : ∀ c, z c sstar - x = -(lr • ∑ s ∈ range sstar, P (gc c (z c s))) := fun c =>
      fedAvgClientIter_sub_self P gc lr x c sstar
    have e3 : ∀ c, ∑ s ∈ range sstar, P (gc c (z c s)) =
        ∑ s ∈ range sstar, P (gc c (z c s) - gc c x) + (sstar : ℝ) • P (gc c x) := by
      intro c
      calc ∑ s ∈ range sstar, P (gc c (z c s))
          = ∑ s ∈ range sstar, (P (gc c (z c s) - gc c x) + P (gc c x)) :=
            sum_congr rfl fun s _ => by rw [← map_add]; congr 1; abel
        _ = _ := by
          rw [sum_add_distrib, sum_const, card_range, Nat.cast_smul_eq_nsmul]
    have e4 : ∑ c, ∑ s ∈ range sstar, P (gc c (z c s)) =
        ∑ c, ∑ s ∈ range sstar, P (gc c (z c s) - gc c x) + (sstar : ℝ) • (n • P (g x)) := by
      rw [sum_congr rfl fun c _ => e3 c, sum_add_distrib, ← smul_sum, ← map_sum, hsum_c,
        map_smul]
    have e5 : P w' = lr • n⁻¹ • ∑ c, ∑ s ∈ range sstar, P (gc c (z c s) - gc c x) := by
      rw [hw', map_smul, map_smul, map_sum]
      simp only [map_sum]
    have hnn : n⁻¹ * n = 1 := inv_mul_cancel₀ hn.ne'
    rw [e1, sum_congr rfl fun c _ => e2 c, sum_neg_distrib, ← smul_sum, e4, e5]
    set Q : E := ∑ c, ∑ s ∈ range sstar, P (gc c (z c s) - gc c x)
    have : n⁻¹ • -(lr • (Q + (sstar : ℝ) • n • P (g x))) =
        -(lr • n⁻¹ • Q) - ((n⁻¹ * n) * (lr * sstar)) • P (g x) := by module
    rw [this, hnn, one_mul, hA_def, mul_comm lr]
    abel
  set E' : ℝ := β * (68 / 25 * (lr * sstar) * (p + ζ)) with hE'
  have hterm : ∀ c, ∀ s ∈ range sstar, ‖gc c (z c s) - gc c x‖ ≤ E' := by
    intro c s hs'
    have h1 := hgc c (z c s) x
    have h2 := norm_fedAvgClientIter_sub_le' (g := g) hgc hP hβ hlr x c (hζ c x) hs
      (mem_range.1 hs').le
    have h3 := mul_le_mul_of_nonneg_left h2 hβ
    exact h1.trans h3
  have hinner : ∀ c, ‖∑ s ∈ range sstar, (gc c (z c s) - gc c x)‖ ≤ sstar * E' := by
    intro c
    refine (norm_sum_le_of_le _ (hterm c)).trans ?_
    simp
  have houter : ‖∑ c, ∑ s ∈ range sstar, (gc c (z c s) - gc c x)‖ ≤ n * (sstar * E') := by
    refine (norm_sum_le_of_le _ fun c _ => hinner c).trans ?_
    simp [hn_def]
  have hw'n : ‖w'‖ ≤ A * E' := by
    rw [hw', norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlr, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.2 hn.le)]
    have h1 := mul_le_mul_of_nonneg_left houter (inv_nonneg.2 hn.le)
    have h2 := mul_le_mul_of_nonneg_left h1 hlr
    calc _ ≤ _ := h2
      _ = A * E' := by rw [hA_def]; field_simp
  have hβA : β * A ≤ 1 := by
    have : β * A = lr * β * sstar := by rw [hA_def]; ring
    linarith
  have hE0 : 0 ≤ E' := by
    rw [hE']; positivity
  have hEle : E' ≤ 68 / 25 * (p + ζ) := by
    have : E' = (β * A) * (68 / 25 * (p + ζ)) := by rw [hE', hA_def]; ring
    rw [this]
    have : 0 ≤ 68 / 25 * (p + ζ) := by positivity
    nlinarith
  have hd := descent_lemma hℒ hg x (fedAvgRound P gc lr sstar x)
  have hinner_g : ⟪g x, fedAvgRound P gc lr sstar x - x⟫ ≤ -(A * p ^ 2) + p * (A * E') := by
    have i1 : ⟪g x, P (g x)⟫ = p ^ 2 := by rw [real_inner_comm, hP.inner_self_apply]
    have i2 : ⟪g x, P w'⟫ = ⟪P (g x), w'⟫ := (hP.symm (g x) w').symm
    rw [hδ, inner_sub_right, inner_neg_right, inner_smul_right, i1, i2]
    have h1 : -⟪P (g x), w'⟫ ≤ p * ‖w'‖ := by
      have := neg_le_abs ⟪P (g x), w'⟫
      exact this.trans ((abs_real_inner_le_norm _ _).trans le_rfl)
    have h2 : p * ‖w'‖ ≤ p * (A * E') := mul_le_mul_of_nonneg_left hw'n hp0
    linarith
  have hnorm_δ : ‖fedAvgRound P gc lr sstar x - x‖ ≤ A * (p + E') := by
    rw [hδ]
    calc ‖-(A • P (g x)) - P w'‖ ≤ ‖-(A • P (g x))‖ + ‖P w'‖ := norm_sub_le _ _
      _ ≤ A * p + A * E' := by
        rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hA0]
        exact add_le_add le_rfl ((hP.norm_le _).trans hw'n)
      _ = _ := by ring
  have hT1 : 0 ≤ β * A ^ 2 := by positivity
  have hsq : ‖fedAvgRound P gc lr sstar x - x‖ ^ 2 ≤ A ^ 2 * (p + 68 / 25 * (p + ζ)) ^ 2 := by
    have h1 : ‖fedAvgRound P gc lr sstar x - x‖ ≤ A * (p + 68 / 25 * (p + ζ)) :=
      hnorm_δ.trans (mul_le_mul_of_nonneg_left (by linarith) hA0)
    calc _ ≤ (A * (p + 68 / 25 * (p + ζ))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = _ := by ring
  have hpoly : 68 / 25 * (p * (p + ζ)) + (p + 68 / 25 * (p + ζ)) ^ 2 / 2 ≤
      20 * p ^ 2 + 17 * ζ ^ 2 := by
    nlinarith [sq_nonneg (p - ζ), sq_nonneg p, sq_nonneg ζ, sq_nonneg (p + ζ)]
  have hmain := mul_le_mul_of_nonneg_left hpoly hT1
  have hpE : p * (A * E') = 68 / 25 * (β * A ^ 2) * (p * (p + ζ)) := by
    rw [hE', hA_def]; ring
  have hsq' := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ β / 2)
  rw [hpE] at hinner_g
  have e : sstar * lr * (1 - 20 * (sstar * lr) * β) * ‖P (g x)‖ ^ 2 =
      A * (1 - 20 * A * β) * p ^ 2 := by
    rw [hA_def]
  rw [e]
  nlinarith

end Federated

end LeanDLRA
