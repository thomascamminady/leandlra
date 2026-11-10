import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Research.SameMinibatchAugmentation
import LeanDLRA.Training.Descent

/-!
# Same-minibatch augmentation bias and its repair

`LeanDLRA/Research/SameMinibatchAugmentation.lean` shows on a two-point example that building the
augmented basis and the step from one minibatch can ascend. This module gives the general picture.
Notation: `G = ∇ℒ(W₀)`, `g_ξ` unbiased minibatch gradients, `P = P(W₀)` the tangent projector, `N(Z)
= Z - P Z` the doubly-normal part, `Π_A` the Galerkin projector of `Û = orth[U₀, A V₀]`, `V̂ =
orth[V₀, Aᵀ U₀]`. Expectations are finite weighted sums.

## Main results

* **Where the bias lives.**  `sum_inner_eq_add_bias`, `bias_eq_covariance`, `abs_bias_le` are the
  general bias formula.  For the actual same-batch step, `sum_inner_augmented` is the closed form
  `E ⟪G, Π_ξ g_ξ⟫ = ‖P G‖² + E ⟪N(G), Π_ξ N(g_ξ)⟫`: the tangent part has no bias at all.
  `le_sum_inner_sameBatch` gives the necessary condition `‖P G‖² < ‖N(G)‖ σ_N` for first-order
  ascent, `sum_inner_sameBatch_sub_decoupled` splits the difference to a decoupled scheme into a
  non-negative tangent gain and a doubly-normal term, and `sum_sum_inner_of_block_indep` shows there
  is no ascent when the doubly-normal noise is independent of the tangent noise.
* **What decoupling captures.**  Bases from a batch `ζ` do not contain `P G`.  `div_le_capture`,
  `div_le_capture_augmented`: `E ‖Π_ζ G‖² ≥ ‖P G‖⁴ / (‖P G‖² + σ_P²)`, sharp for every
  signal-to-noise ratio by `sharp_decoupled_capture`; `sum_sum_loss_le_snr` is the resulting
  descent bound.
  `norm_sq_tangent_le` is the deterministic form `‖P G‖² ≤ ‖Π_m G‖² + ‖P (m - G)‖²`.
* **A repair with the full rate.**  `blockProj`, `sum_loss_block_le`: keep the whole tangent part of
  the fresh gradient and restrict only its doubly-normal part to the stale bases, giving the full
  `‖P G‖²` for any stale source; `rank_block_step_le` bounds the rank.
* **Several steps.**  `chainExp` is the expectation along the chain of a scheme, and
  `chainExp_eq_sum_path` identifies it with the sum over i.i.d. sample paths.
  `exists_tangent_sq_le_ema_augmented`: the decoupled step with an EMA buffer reaches Riemannian
  stationarity, up to a floor `(β h + 4 α + 8 (β h / α)²) σ²`, without any assumption on the
  curvature of the manifold.  At `α = 1` (previous batch) the floor `4 σ²` does not vanish.
  `exists_tangent_sq_le_block_augmented`: the block step with any buffer has floor `O(β h σ²)`.
  `exists_snr_le_heldout` is the held-out batch version.  Truncation is included in all of them.
  `ema_instance` shows that the hypotheses can be met.
* **Robbins-Monro.**  `frequently_tangent_sq_lt_geoLoRA` and `frequently_tangent_sq_lt_block`:
  `liminf E ‖P(W_t) ∇ℒ(W_t)‖² = 0` for the tangent step with one batch and for the block step
  with any stale bases, the expectation being taken along the whole chain (OP-TR-08).

## Summary of results

* The capture hypothesis of Theorem D fails for decoupled bases, and the Riemannian descent drawn
  from it is false: `decoupled_not_capture`, `decoupled_riemannian_bound_false`.  The repair is the
  signal-to-noise bound above or the block step.
* Theorem C does not apply to GeoLoRA, whose lower-right block is zero: its step is the tangent
  step and has no same-batch bias (`sum_inner_tangent`).  It does apply to augmented Galerkin steps
  and to abc-PSI (`abcPSI_first_order`).
* Truncation can remove the ascent (`truncation_removes_ascent`): the
  biased block is the one that a truncation back to the old rank deletes.
* The bias has no fixed sign, and same-batch can beat decoupling at every noise level
  (`sharp_gain_sameBatch`, `family_first_orders`); the ascent needs tangent and doubly-normal noise
  to be coupled (`decorrelated_first_order`).
* "The bias vanishes for `r ≥ rank g_ξ`" is false (`RankExample.first_order_neg`); the true
  condition is `IsAugmented.apply_self_of_factor`, and `IsAugmented.apply_self_of_batch` covers
  batches of at most `r` samples in general position, where the same-batch step is exactly SGD.
* "Decoupling restores descent" needs a step size condition: `decoupled_lt_iff`.
* The gap does not always close like `1 / B`: `family_gap`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Novel.MinibatchBias

open LeanDLRA.StochasticDescent
open Matrix (IsOrthBasisOf)

/-! ### Part I: the first-order bias of a minibatch-dependent projector -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Ξ : Type*} [Fintype Ξ]

/-- Weighted Cauchy-Schwarz: `(∑ p a b)² ≤ (∑ p a²) (∑ p b²)` for `p ≥ 0`. -/
lemma sq_sum_mul_le {p : Ξ → ℝ} (hp : ∀ ξ, 0 ≤ p ξ) (a b : Ξ → ℝ) :
    (∑ ξ, p ξ * (a ξ * b ξ)) ^ 2 ≤ (∑ ξ, p ξ * a ξ ^ 2) * ∑ ξ, p ξ * b ξ ^ 2 :=
  Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun ξ _ => mul_nonneg (hp ξ) (sq_nonneg _))
    (fun ξ _ => mul_nonneg (hp ξ) (sq_nonneg _)) (fun ξ _ => le_of_eq (by ring))

/-- `∑ p a ≤ √(∑ p a²)` for a probability weight `p`. -/
lemma sum_mul_le_sqrt {p : Ξ → ℝ} (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1) (a : Ξ → ℝ) :
    ∑ ξ, p ξ * a ξ ≤ √(∑ ξ, p ξ * a ξ ^ 2) := by
  have h := sq_sum_mul_le hp (fun _ => 1) a
  simp only [one_mul, one_pow, mul_one, hp1] at h
  exact Real.le_sqrt_of_sq_le h

/-- **First-order decomposition.**  For orthogonal projectors `Π_ξ` and any vectors `g_ξ`,
`E ⟪G, Π_ξ g_ξ⟫ = E ‖Π_ξ G‖² + E ⟪G, Π_ξ (g_ξ - G)⟫`.  The first term is what a
minibatch-independent projector would give; the second is the bias. -/
theorem sum_inner_eq_add_bias {p : Ξ → ℝ} {Pi : Ξ → E →L[ℝ] E} (hPi : ∀ ξ, IsOrthProj (Pi ξ))
    (gs : Ξ → E) (G : E) :
    ∑ ξ, p ξ * ⟪G, Pi ξ (gs ξ)⟫ =
      ∑ ξ, p ξ * ‖Pi ξ G‖ ^ 2 + ∑ ξ, p ξ * ⟪G, Pi ξ (gs ξ - G)⟫ := by
  rw [← sum_add_distrib]
  refine sum_congr rfl fun ξ _ => ?_
  rw [map_sub, inner_sub_right, real_inner_comm (Pi ξ G) G, (hPi ξ).inner_self_apply]
  ring

/-- The mean projector `Π̄ = E Π_ξ`. -/
noncomputable def meanProj (p : Ξ → ℝ) (Pi : Ξ → E →L[ℝ] E) : E →L[ℝ] E := ∑ ξ, p ξ • Pi ξ

/-- **The bias is a covariance**: `E ⟪G, Π_ξ (g_ξ - G)⟫ = E ⟪G, (Π_ξ - Π̄) (g_ξ - G)⟫`.  It vanishes
as soon as `Π_ξ` is deterministic. -/
theorem bias_eq_covariance {p : Ξ → ℝ} (hp1 : ∑ ξ, p ξ = 1) (Pi : Ξ → E →L[ℝ] E) {gs : Ξ → E}
    {G : E} (hmean : ∑ ξ, p ξ • gs ξ = G) :
    ∑ ξ, p ξ * ⟪G, Pi ξ (gs ξ - G)⟫ =
      ∑ ξ, p ξ * ⟪G, (Pi ξ - meanProj p Pi) (gs ξ - G)⟫ := by
  have h0 := sum_inner_apply_eq (sum_smul_sub_eq_zero hp1 hmean) (meanProj p Pi) G
  rw [map_zero, inner_zero_right] at h0
  have : ∀ ξ, p ξ * ⟪G, (Pi ξ - meanProj p Pi) (gs ξ - G)⟫ =
      p ξ * ⟪G, Pi ξ (gs ξ - G)⟫ - p ξ * ⟪G, meanProj p Pi (gs ξ - G)⟫ := fun ξ => by
    rw [sub_apply, inner_sub_right]; ring
  simp only [this, sum_sub_distrib, h0, sub_zero]

/-- **Size of the bias**: `|bias| ≤ ‖G‖ E ‖(Π_ξ - Π̄) (g_ξ - G)‖`. -/
theorem abs_bias_le {p : Ξ → ℝ} (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1) (Pi : Ξ → E →L[ℝ] E)
    {gs : Ξ → E} {G : E} (hmean : ∑ ξ, p ξ • gs ξ = G) :
    |∑ ξ, p ξ * ⟪G, Pi ξ (gs ξ - G)⟫| ≤
      ‖G‖ * ∑ ξ, p ξ * ‖(Pi ξ - meanProj p Pi) (gs ξ - G)‖ := by
  rw [bias_eq_covariance hp1 Pi hmean, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ξ _ => ?_)
  rw [abs_mul, abs_of_nonneg (hp ξ), mul_left_comm]
  exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (hp ξ)

/-- **Exact first order expansion of the expected loss.**  For every `β`-smooth loss and any
directions `d_ξ`,
`|E ℒ(x - h d_ξ) - (ℒ(x) - h E ⟪∇ℒ(x), d_ξ⟫)| ≤ β h² / 2 E ‖d_ξ‖²`, so the sign of
`E ⟪∇ℒ(x), d_ξ⟫` decides between descent and ascent for small `h`, whatever the direction law. -/
theorem abs_sum_loss_sub_le {ℒ : E → ℝ} {g : E → E} {β : ℝ}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    {p : Ξ → ℝ} (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1) (ds : Ξ → E) (x : E) (h : ℝ) :
    |∑ ξ, p ξ * ℒ (x - h • ds ξ) - (ℒ x - h * ∑ ξ, p ξ * ⟪g x, ds ξ⟫)| ≤
      β * h ^ 2 / 2 * ∑ ξ, p ξ * ‖ds ξ‖ ^ 2 := by
  have e : ℒ x - h * ∑ ξ, p ξ * ⟪g x, ds ξ⟫ = ∑ ξ, p ξ * (ℒ x - h * ⟪g x, ds ξ⟫) := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hp1, one_mul, mul_sum]
    refine congrArg _ (sum_congr rfl fun ξ _ => by ring)
  rw [e, ← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ξ _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (hp ξ), mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (hp ξ)
  rw [abs_le]
  have h1 := loss_sub_smul_le hℒ hg x (ds ξ) h
  have h2 := le_loss_sub_smul hℒ hg x (ds ξ) h
  constructor <;> linarith

/-- **Independence removes the bias exactly**: if `Π_ζ` is independent of the unbiased `g_ξ`,
`E_ζ E_ξ ⟪G, Π_ζ g_ξ⟫ = E_ζ ‖Π_ζ G‖² ≥ 0`.  So the first-order term cannot point uphill. -/
theorem sum_sum_inner_of_indep {Z : Type*} [Fintype Z] {q : Z → ℝ} {Pi : Z → E →L[ℝ] E}
    (hPi : ∀ ζ, IsOrthProj (Pi ζ)) {p : Ξ → ℝ} {gs : Ξ → E} {G : E}
    (hmean : ∑ ξ, p ξ • gs ξ = G) :
    ∑ ζ, q ζ * ∑ ξ, p ξ * ⟪G, Pi ζ (gs ξ)⟫ = ∑ ζ, q ζ * ‖Pi ζ G‖ ^ 2 := by
  refine sum_congr rfl fun ζ _ => ?_
  rw [sum_inner_apply_eq hmean, real_inner_comm, (hPi ζ).inner_self_apply]

/-! ### Part II: where the bias lives -/

/-- `T` (the tangent projector `P(W₀)`) and `Π` (an augmented projector) are orthogonal projectors
that commute.  This holds for the Galerkin projector `Z ↦ Û Ûᵀ Z V̂ V̂ᵀ` and for the left projector
`Z ↦ Û Ûᵀ Z` of the abc-PSI step whenever the augmented bases contain the old ones
(`IsAugmented.compatible`). -/
structure Compatible (T Pi : E →L[ℝ] E) : Prop where
  tan : IsOrthProj T
  proj : IsOrthProj Pi
  comm : ∀ x, Pi (T x) = T (Pi x)

namespace Compatible

variable {T Pi : E →L[ℝ] E}

/-- With `v - T v` the doubly-normal part, `Π v = T v + Π (v - T v)` when `Π` captures `T v`. -/
lemma apply_eq {v : E} (hcap : Pi (T v) = T v) : Pi v = T v + Pi (v - T v) := by
  rw [map_sub, hcap]; abel

/-- `Π` maps the doubly-normal space to itself. -/
lemma tan_apply_normal (hc : Compatible T Pi) (v : E) : T (Pi (v - T v)) = 0 := by
  rw [← hc.comm, map_sub, hc.tan.idem, sub_self, map_zero]

/-- Only the doubly-normal part of `G` sees the doubly-normal part of a direction. -/
lemma inner_normal (hc : Compatible T Pi) (G v : E) :
    ⟪G, Pi (v - T v)⟫ = ⟪G - T G, Pi (v - T v)⟫ := by
  rw [inner_sub_left, hc.tan.symm, hc.tan_apply_normal, inner_zero_right, sub_zero]

/-- Doubly-normal and tangent parts stay orthogonal under `Π`:
`‖Π G‖² = ‖Π T G‖² + ‖Π (G - T G)‖²`. -/
lemma norm_sq_apply (hc : Compatible T Pi) (G : E) :
    ‖Pi G‖ ^ 2 = ‖Pi (T G)‖ ^ 2 + ‖Pi (G - T G)‖ ^ 2 := by
  have h : Pi G = Pi (T G) + Pi (G - T G) := by rw [← map_add, add_sub_cancel]
  have h0 : ⟪Pi (T G), Pi (G - T G)⟫ = 0 := by
    rw [hc.comm, hc.tan.symm, hc.tan_apply_normal, inner_zero_right]
  rw [h, norm_add_sq_real, h0]; ring

/-- The doubly-normal term expanded around `G`:
`⟪G - T G, Π N⟫ = ‖Π (G - T G)‖² + ⟪Π (G - T G), N - (G - T G)⟫`. -/
lemma inner_normal_expand (hc : Compatible T Pi) (G N : E) :
    ⟪G - T G, Pi N⟫ = ‖Pi (G - T G)‖ ^ 2 + ⟪Pi (G - T G), N - (G - T G)⟫ := by
  rw [inner_sub_right, hc.proj.inner_self_apply, ← hc.proj.symm]; ring

end Compatible

variable {T : E →L[ℝ] E} {Pi : Ξ → E →L[ℝ] E} {p : Ξ → ℝ} {gs : Ξ → E} {G : E}

/-- **Exact same-minibatch first-order term.**  If the bases of `Π_ξ` are built from `g_ξ` itself
(so that `Π_ξ` captures `T g_ξ`), then
`E ⟪G, Π_ξ g_ξ⟫ = ‖T G‖² + E ⟪G - T G, Π_ξ (g_ξ - T g_ξ)⟫`.
All of the sign trouble sits in the doubly-normal block: the tangent part of the step is unbiased.
For the example of `SameMinibatchAugmentation.lean` this reads `-1 = 4 - 5`.  This sharpens the
two-term decomposition `sum_inner_eq_add_bias`. -/
theorem sum_inner_sameBatch (hT : IsOrthProj T) (hc : ∀ ξ, Compatible T (Pi ξ))
    (hcap : ∀ ξ, Pi ξ (T (gs ξ)) = T (gs ξ)) (hmean : ∑ ξ, p ξ • gs ξ = G) :
    ∑ ξ, p ξ * ⟪G, Pi ξ (gs ξ)⟫ =
      ‖T G‖ ^ 2 + ∑ ξ, p ξ * ⟪G - T G, Pi ξ (gs ξ - T (gs ξ))⟫ := by
  have h1 : ∀ ξ, p ξ * ⟪G, Pi ξ (gs ξ)⟫ =
      p ξ * ⟪G, T (gs ξ)⟫ + p ξ * ⟪G - T G, Pi ξ (gs ξ - T (gs ξ))⟫ := fun ξ => by
    rw [Compatible.apply_eq (hcap ξ), inner_add_right, (hc ξ).inner_normal]; ring
  simp only [h1, sum_add_distrib]
  rw [sum_inner_apply_eq hmean, real_inner_comm, hT.inner_self_apply]

/-- **The bias splits into two competing terms.**  With `N_ξ = g_ξ - T g_ξ`, `N = G - T G`, the
same-minibatch first-order term exceeds the first-order term of a decoupled projector with the
same law by
`E ⟪G, Π_ξ g_ξ⟫ - E ‖Π_ξ G‖² = E ‖T G - Π_ξ T G‖² + E ⟪Π_ξ N, N_ξ - N⟫`.
The first term is a *gain*, never negative: the same batch captures its own tangent part, a
decoupled projector does not capture `T G`.  Only the second term can be negative, and it requires
the doubly-normal noise of a batch to correlate with the bases that this batch selects.  So the
bias has no fixed sign; see `sharp_gain_sameBatch` for an instance where
same-batch beats decoupling. -/
theorem sum_inner_sameBatch_sub_decoupled (hT : IsOrthProj T) (hc : ∀ ξ, Compatible T (Pi ξ))
    (hcap : ∀ ξ, Pi ξ (T (gs ξ)) = T (gs ξ)) (hp1 : ∑ ξ, p ξ = 1)
    (hmean : ∑ ξ, p ξ • gs ξ = G) :
    ∑ ξ, p ξ * ⟪G, Pi ξ (gs ξ)⟫ - ∑ ξ, p ξ * ‖Pi ξ G‖ ^ 2 =
      ∑ ξ, p ξ * ‖T G - Pi ξ (T G)‖ ^ 2 +
        ∑ ξ, p ξ * ⟪Pi ξ (G - T G), (gs ξ - T (gs ξ)) - (G - T G)⟫ := by
  rw [sum_inner_sameBatch hT hc hcap hmean]
  have h1 : ‖T G‖ ^ 2 = ∑ ξ, p ξ * ‖T G‖ ^ 2 := by rw [← sum_mul, hp1, one_mul]
  rw [h1, ← sum_add_distrib, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun ξ _ => ?_
  have h2 := (hc ξ).proj.norm_sq_add (T G)
  rw [(hc ξ).inner_normal_expand G, (hc ξ).norm_sq_apply G]
  rw [← h2]; ring

/-- **A necessary condition for first-order ascent.**  For the same-minibatch step,
`E ⟪G, Π_ξ g_ξ⟫ ≥ ‖T G‖² - ‖N‖ σ_N`, with `N = G - T G` the doubly-normal part of the full gradient
and `σ_N² = E ‖N_ξ - N‖²` the variance of the doubly-normal block.  So ascent at first order needs
`‖T G‖² < ‖N‖ σ_N`: it needs both a non-zero doubly-normal gradient and doubly-normal noise, and in
particular the same-minibatch step has `E ⟪G, Π_ξ g_ξ⟫ ≥ ‖T G‖²` if `N = 0` or `σ_N = 0`. -/
theorem le_sum_inner_sameBatch (hT : IsOrthProj T) (hc : ∀ ξ, Compatible T (Pi ξ))
    (hcap : ∀ ξ, Pi ξ (T (gs ξ)) = T (gs ξ)) (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1)
    (hmean : ∑ ξ, p ξ • gs ξ = G) :
    ‖T G‖ ^ 2 - ‖G - T G‖ * √(∑ ξ, p ξ * ‖(gs ξ - T (gs ξ)) - (G - T G)‖ ^ 2) ≤
      ∑ ξ, p ξ * ⟪G, Pi ξ (gs ξ)⟫ := by
  rw [sum_inner_sameBatch hT hc hcap hmean, sub_eq_add_neg]
  refine add_le_add_right ?_ _
  have h1 : ∀ ξ, -(‖G - T G‖ * (p ξ * ‖(gs ξ - T (gs ξ)) - (G - T G)‖)) ≤
      p ξ * ⟪G - T G, Pi ξ (gs ξ - T (gs ξ))⟫ := fun ξ => by
    rw [(hc ξ).inner_normal_expand G]
    have h3 : -(‖Pi ξ (G - T G)‖ * ‖(gs ξ - T (gs ξ)) - (G - T G)‖) ≤
        ⟪Pi ξ (G - T G), (gs ξ - T (gs ξ)) - (G - T G)⟫ :=
      neg_le_of_abs_le (abs_real_inner_le_norm _ _)
    have h4 := mul_le_mul_of_nonneg_right ((hc ξ).proj.norm_le (G - T G))
      (norm_nonneg ((gs ξ - T (gs ξ)) - (G - T G)))
    have h5 : 0 ≤ ‖Pi ξ (G - T G)‖ ^ 2 := sq_nonneg _
    have h6 := mul_nonneg (hp ξ) (by linarith :
      0 ≤ ‖G - T G‖ * ‖(gs ξ - T (gs ξ)) - (G - T G)‖ +
        ‖Pi ξ (G - T G)‖ ^ 2 + ⟪Pi ξ (G - T G), (gs ξ - T (gs ξ)) - (G - T G)⟫)
    nlinarith
  have h2 := sum_mul_le_sqrt hp hp1 fun ξ => ‖(gs ξ - T (gs ξ)) - (G - T G)‖
  calc -(‖G - T G‖ * √(∑ ξ, p ξ * ‖(gs ξ - T (gs ξ)) - (G - T G)‖ ^ 2))
      ≤ -(‖G - T G‖ * ∑ ξ, p ξ * ‖(gs ξ - T (gs ξ)) - (G - T G)‖) :=
        neg_le_neg (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    _ = ∑ ξ, -(‖G - T G‖ * (p ξ * ‖(gs ξ - T (gs ξ)) - (G - T G)‖)) := by
        rw [mul_sum, sum_neg_distrib]
    _ ≤ _ := sum_le_sum fun ξ _ => h1 ξ

/-- **No bias without tangent/doubly-normal coupling.**  Let the sample be a pair `(ξ₁, ξ₂)` of
independent parts, let the projector depend on `ξ₁` only, and let the doubly-normal block of the
gradient be conditionally unbiased given `ξ₁`.  (This is the finite-support analogue of centred
noise whose tangent and doubly-normal blocks are independent, such as isotropic Gaussian noise; the
same regime in which GoLore, arXiv 2410.11289, reports convergence.)  Then
`E ⟪G, Π g⟫ = ‖T G‖² + E ‖Π (G - T G)‖² ≥ ‖T G‖²`, so there is no first-order ascent, and the
two-point example of `SameMinibatchAugmentation.lean` owes its ascent to the correlation between the
tangent and doubly-normal noise of one batch. -/
theorem sum_sum_inner_of_block_indep {Ξ₁ Ξ₂ : Type*} [Fintype Ξ₁] [Fintype Ξ₂] {p₁ : Ξ₁ → ℝ}
    {p₂ : Ξ₂ → ℝ} {Pi : Ξ₁ → E →L[ℝ] E} {gs : Ξ₁ → Ξ₂ → E} (hT : IsOrthProj T)
    (hc : ∀ ξ, Compatible T (Pi ξ)) (hcap : ∀ ξ₁ ξ₂, Pi ξ₁ (T (gs ξ₁ ξ₂)) = T (gs ξ₁ ξ₂))
    (hmean : ∑ ξ₁, p₁ ξ₁ • ∑ ξ₂, p₂ ξ₂ • gs ξ₁ ξ₂ = G)
    (hnormal : ∀ ξ₁, ∑ ξ₂, p₂ ξ₂ • (gs ξ₁ ξ₂ - T (gs ξ₁ ξ₂)) = G - T G) :
    ∑ ξ₁, p₁ ξ₁ * ∑ ξ₂, p₂ ξ₂ * ⟪G, Pi ξ₁ (gs ξ₁ ξ₂)⟫ =
      ‖T G‖ ^ 2 + ∑ ξ₁, p₁ ξ₁ * ‖Pi ξ₁ (G - T G)‖ ^ 2 := by
  have h1 : ∀ ξ₁, ∑ ξ₂, p₂ ξ₂ * ⟪G, Pi ξ₁ (gs ξ₁ ξ₂)⟫ =
      ⟪G, T (∑ ξ₂, p₂ ξ₂ • gs ξ₁ ξ₂)⟫ + ‖Pi ξ₁ (G - T G)‖ ^ 2 := fun ξ₁ => by
    have h2 : ∀ ξ₂, p₂ ξ₂ * ⟪G, Pi ξ₁ (gs ξ₁ ξ₂)⟫ = p₂ ξ₂ * ⟪G, T (gs ξ₁ ξ₂)⟫ +
        p₂ ξ₂ * ⟪G - T G, Pi ξ₁ (gs ξ₁ ξ₂ - T (gs ξ₁ ξ₂))⟫ := fun ξ₂ => by
      rw [Compatible.apply_eq (hcap ξ₁ ξ₂), inner_add_right, (hc ξ₁).inner_normal]; ring
    simp only [h2, sum_add_distrib]
    rw [sum_inner_apply_eq (hnormal ξ₁), real_inner_comm, (hc ξ₁).proj.inner_self_apply, map_sum,
      inner_sum]
    simp [map_smul, inner_smul_right]
  simp only [h1, mul_add, sum_add_distrib]
  congr 1
  have h3 := sum_inner_apply_eq hmean T G
  rw [real_inner_comm, hT.inner_self_apply] at h3
  simpa [map_sum, inner_sum, map_smul, inner_smul_right, mul_sum] using h3

/-- **The tangent step has no bias**, whatever batch it uses: `E ⟪G, T g_ξ⟫ = ‖T G‖²`.  This is the
step of GeoLoRA (arXiv 2410.18720), whose assembled coefficient matrix has a zero lower-right block
(`geoLoRADir_eq_tangent`), so the same-minibatch ascent (Theorem C) does not apply to
GeoLoRA: it needs the doubly-normal block. -/
theorem sum_inner_tangent (hT : IsOrthProj T) (hmean : ∑ ξ, p ξ • gs ξ = G) :
    ∑ ξ, p ξ * ⟪G, T (gs ξ)⟫ = ‖T G‖ ^ 2 := by
  rw [sum_inner_apply_eq hmean, real_inner_comm, hT.inner_self_apply]

/-! ### Part III: decoupled augmentation, what is captured -/

section Capture

variable {Z : Type*} [Fintype Z] {q : Z → ℝ} {Pi : Z → E →L[ℝ] E} {ms : Z → E}

/-- **Capture of a full gradient by a source-built projector: Cauchy-Schwarz form.**  Let `Π_ζ`
capture the tangent part of a source `m_ζ` (`Π_ζ T m_ζ = T m_ζ`), but with no relation assumed
between the law of `m_ζ` and `G`.  Then
`(E ⟪G, T m_ζ⟫)² ≤ E ‖Π_ζ G‖² · E ‖T m_ζ‖²`.
The only way to control `E ‖Π_ζ G‖²` from below by the tangent gradient is through the alignment of
the source with `G`; capture of `T G` itself is not available, see `decoupled_not_capture`. -/
theorem sq_sum_inner_le_capture (hPi : ∀ ζ, IsOrthProj (Pi ζ)) (hq : ∀ ζ, 0 ≤ q ζ)
    (hcap : ∀ ζ, Pi ζ (T (ms ζ)) = T (ms ζ)) (G : E) :
    (∑ ζ, q ζ * ⟪G, T (ms ζ)⟫) ^ 2 ≤
      (∑ ζ, q ζ * ‖Pi ζ G‖ ^ 2) * ∑ ζ, q ζ * ‖T (ms ζ)‖ ^ 2 := by
  have h1 : ∀ ζ, ⟪G, T (ms ζ)⟫ = ⟪Pi ζ G, T (ms ζ)⟫ := fun ζ => by
    rw [(hPi ζ).symm, hcap]
  refine le_trans ?_ (sq_sum_mul_le hq (fun ζ => ‖Pi ζ G‖) fun ζ => ‖T (ms ζ)‖)
  rw [← sq_abs (∑ ζ, q ζ * ⟪G, T (ms ζ)⟫)]
  refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ζ _ => ?_)
  rw [abs_mul, abs_of_nonneg (hq ζ), h1]
  exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (hq ζ)

/-- **Signal-to-noise capture bound.**  If the source is unbiased, `E m_ζ = G`, then
`‖T G‖⁴ ≤ E ‖Π_ζ G‖² · (‖T G‖² + σ_T²)`, with `σ_T² = E ‖T (m_ζ - G)‖²`.  This replaces the capture
property `Π_ζ ⊇ P(W₀)`, which fails for decoupled augmentation. -/
theorem pow_four_le_capture (hT : IsOrthProj T) (hPi : ∀ ζ, IsOrthProj (Pi ζ)) (hq : ∀ ζ, 0 ≤ q ζ)
    (hq1 : ∑ ζ, q ζ = 1) (hcap : ∀ ζ, Pi ζ (T (ms ζ)) = T (ms ζ))
    (hmean : ∑ ζ, q ζ • ms ζ = G) :
    ‖T G‖ ^ 4 ≤ (∑ ζ, q ζ * ‖Pi ζ G‖ ^ 2) * (‖T G‖ ^ 2 + ∑ ζ, q ζ * ‖T (ms ζ - G)‖ ^ 2) := by
  have h1 := sq_sum_inner_le_capture hPi hq hcap G
  rw [sum_inner_apply_eq hmean, real_inner_comm, hT.inner_self_apply,
    sum_norm_sq_apply_eq hq1 hmean] at h1
  calc ‖T G‖ ^ 4 = (‖T G‖ ^ 2) ^ 2 := by ring
    _ ≤ _ := h1

/-- `pow_four_le_capture` as a lower bound:
`E ‖Π_ζ G‖² ≥ ‖T G‖² · SNR / (1 + SNR)`, with `SNR = ‖T G‖² / σ_T²`, in the form
`‖T G‖⁴ / (‖T G‖² + σ_T²) ≤ E ‖Π_ζ G‖²`. -/
theorem div_le_capture (hT : IsOrthProj T) (hPi : ∀ ζ, IsOrthProj (Pi ζ)) (hq : ∀ ζ, 0 ≤ q ζ)
    (hq1 : ∑ ζ, q ζ = 1) (hcap : ∀ ζ, Pi ζ (T (ms ζ)) = T (ms ζ))
    (hmean : ∑ ζ, q ζ • ms ζ = G) :
    ‖T G‖ ^ 4 / (‖T G‖ ^ 2 + ∑ ζ, q ζ * ‖T (ms ζ - G)‖ ^ 2) ≤ ∑ ζ, q ζ * ‖Pi ζ G‖ ^ 2 := by
  have h0 : 0 ≤ ∑ ζ, q ζ * ‖Pi ζ G‖ ^ 2 := sum_nonneg fun ζ _ => mul_nonneg (hq ζ) (sq_nonneg _)
  have hσ : 0 ≤ ∑ ζ, q ζ * ‖T (ms ζ - G)‖ ^ 2 :=
    sum_nonneg fun ζ _ => mul_nonneg (hq ζ) (sq_nonneg _)
  rcases (add_nonneg (sq_nonneg ‖T G‖) hσ).eq_or_lt with h | h
  · rw [← h, div_zero]; exact h0
  · rw [div_le_iff₀ h]; exact pow_four_le_capture hT hPi hq hq1 hcap hmean

end Capture

/-- **Capture deficit, for a single source.**  If `Π` captures `T m` for any `m` whatsoever, then
`‖T G‖² ≤ ‖Π G‖² + ‖T (m - G)‖²`: the tangent energy of `G` is captured up to the tangent error of
the source.  This is the deterministic counterpart of `pow_four_le_capture`, needs no law on `m`,
and drives the analysis of the EMA buffer. -/
theorem norm_sq_tangent_le {Pi : E →L[ℝ] E} (hc : Compatible T Pi) {m : E}
    (hcap : Pi (T m) = T m) (G : E) : ‖T G‖ ^ 2 ≤ ‖Pi G‖ ^ 2 + ‖T (m - G)‖ ^ 2 := by
  have h1 := hc.proj.norm_sq_add (T G)
  have h2 : ‖Pi (T G)‖ ≤ ‖Pi G‖ := by
    rw [hc.comm]; exact hc.tan.norm_le _
  have h3 : T G - Pi (T G) = T (G - m) - Pi (T (G - m)) := by
    simp only [map_sub, hcap]; abel
  have h4 : ‖T G - Pi (T G)‖ ≤ ‖T (m - G)‖ := by
    rw [h3, ← norm_neg (T (m - G)), ← map_neg, neg_sub]
    exact hc.proj.norm_sub_le _
  have h5 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h6 := pow_le_pow_left₀ (norm_nonneg _) h4 2
  linarith

/-- Relative-error form of `norm_sq_tangent_le`: a source tracking the tangent gradient to relative
accuracy `θ` captures the fraction `1 - θ²` of the tangent energy. -/
theorem capture_of_relative_error {Pi : E →L[ℝ] E} (hc : Compatible T Pi) {m : E}
    (hcap : Pi (T m) = T m) {G : E} {θ : ℝ} (hθ : ‖T (m - G)‖ ≤ θ * ‖T G‖) :
    (1 - θ ^ 2) * ‖T G‖ ^ 2 ≤ ‖Pi G‖ ^ 2 := by
  have h1 := norm_sq_tangent_le hc hcap G
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hθ 2
  rw [mul_pow] at h2
  linarith

/-! ### The block step: tangent part from the fresh batch, doubly-normal part on stale bases -/

/-- The block projector `T + Π (1 - T)`: the fresh gradient keeps its whole tangent part, and only
its doubly-normal part is restricted to the (stale) augmented bases. -/
noncomputable def blockProj (T Pi : E →L[ℝ] E) : E →L[ℝ] E := T + Pi * (1 - T)

lemma blockProj_apply (T Pi : E →L[ℝ] E) (x : E) : blockProj T Pi x = T x + Pi (x - T x) := rfl

namespace Compatible

variable {T Pi : E →L[ℝ] E}

/-- The block projector is an orthogonal projector. -/
lemma isOrthProj_blockProj (hc : Compatible T Pi) : IsOrthProj (blockProj T Pi) where
  idem x := by
    have h1 : T (T x + Pi (x - T x)) = T x := by
      rw [map_add, hc.tan.idem, hc.tan_apply_normal, add_zero]
    rw [blockProj_apply, blockProj_apply, h1, add_sub_cancel_left, hc.proj.idem]
  symm x y := by
    have hq : IsOrthProj (Pi * (1 - T)) := hc.proj.mul hc.tan.compl fun z => by
      simp only [sub_apply, one_apply_eq_self, map_sub, hc.comm]
    change ⟪T x + (Pi * (1 - T)) x, y⟫ = ⟪x, T y + (Pi * (1 - T)) y⟫
    rw [inner_add_left, inner_add_right, hc.tan.symm, hq.symm]

/-- The block projector contains the whole tangent space. -/
lemma blockProj_tan (hc : Compatible T Pi) (x : E) : blockProj T Pi (T x) = T x := by
  rw [blockProj_apply, hc.tan.idem, sub_self, map_zero, add_zero]

/-- `‖B G‖² = ‖T G‖² + ‖Π (G - T G)‖²` for the block projector `B = T + Π (1 - T)`. -/
lemma norm_sq_blockProj (hc : Compatible T Pi) (G : E) :
    ‖blockProj T Pi G‖ ^ 2 = ‖T G‖ ^ 2 + ‖Pi (G - T G)‖ ^ 2 := by
  have h0 : ⟪T G, Pi (G - T G)⟫ = 0 := by
    rw [hc.tan.symm, hc.tan_apply_normal, inner_zero_right]
  rw [blockProj_apply, norm_add_sq_real, h0]; ring

end Compatible

variable {ℒ : E → ℝ} {g : E → E} {β : ℝ}

/-- **Riemannian descent of the block step.**  Let `Π` be any augmented projector compatible with
the tangent projector `T` and independent of the step batch `ξ` (for instance built from the
previous gradient or an EMA buffer; no capture property and no accuracy of the source is needed).
With
`B = T + Π (1 - T)`, the step `x - h B g_ξ` satisfies
`E ℒ(x - h B g_ξ) ≤ ℒ(x) - h (1 - β h / 2) (‖T ∇ℒ‖² + ‖Π N‖²) + β h² / 2 · E ‖B (g_ξ - ∇ℒ)‖²`,
with `N` the doubly-normal part of `∇ℒ(x)`.  Unlike the decoupled step `x - h Π g_ξ` of
Theorem D, this has the full `‖T ∇ℒ‖²` and no signal-to-noise penalty: it is the Riemannian descent
that the capture property would give (OP-TR-08, one step, no truncation). -/
theorem sum_loss_block_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {Pi : E →L[ℝ] E} (hc : Compatible T Pi)
    (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1) {x : E} (hmean : ∑ ξ, p ξ • gs ξ = g x) (h : ℝ) :
    ∑ ξ, p ξ * ℒ (x - h • blockProj T Pi (gs ξ)) ≤
      ℒ x - h * (1 - β * h / 2) * (‖T (g x)‖ ^ 2 + ‖Pi (g x - T (g x))‖ ^ 2) +
        β * h ^ 2 / 2 * ∑ ξ, p ξ * ‖blockProj T Pi (gs ξ - g x)‖ ^ 2 := by
  have h1 := sum_loss_sub_smul_apply_le hℒ hg hc.isOrthProj_blockProj hp hp1 hmean h
  rwa [hc.norm_sq_blockProj] at h1

/-- **Signal-to-noise descent of the decoupled step `x - h Π_ζ g_ξ`** (Theorem D with
its capture hypothesis repaired).  Bases built from an unbiased batch `ζ` independent of `ξ`:
`E ℒ(x - h Π_ζ g_ξ) ≤ ℒ(x) - h (1 - β h / 2) ‖T ∇ℒ‖⁴ / (‖T ∇ℒ‖² + σ_T²) + β h² / 2 · σ²`.
The first-order rate carries the factor `SNR / (1 + SNR)`, which is sharp by
`sharp_decoupled_capture`. -/
theorem sum_sum_loss_le_snr {Z : Type*} [Fintype Z] {q : Z → ℝ} {Pi : Z → E →L[ℝ] E}
    {ms : Z → E} (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hT : IsOrthProj T)
    (hPi : ∀ ζ, IsOrthProj (Pi ζ)) (hq : ∀ ζ, 0 ≤ q ζ) (hq1 : ∑ ζ, q ζ = 1)
    (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1) {x : E} (hmean : ∑ ξ, p ξ • gs ξ = g x)
    (hcap : ∀ ζ, Pi ζ (T (ms ζ)) = T (ms ζ)) (hmean' : ∑ ζ, q ζ • ms ζ = g x) {h : ℝ}
    (hh : 0 ≤ h * (1 - β * h / 2)) {σsq : ℝ} (hσ : ∑ ξ, p ξ * ‖gs ξ - g x‖ ^ 2 ≤ σsq) :
    ∑ ζ, q ζ * ∑ ξ, p ξ * ℒ (x - h • Pi ζ (gs ξ)) ≤
      ℒ x - h * (1 - β * h / 2) *
          (‖T (g x)‖ ^ 4 / (‖T (g x)‖ ^ 2 + ∑ ζ, q ζ * ‖T (ms ζ - g x)‖ ^ 2)) +
        β * h ^ 2 / 2 * σsq := by
  have h1 := sum_sum_loss_le_of_indep hℒ hg hPi hq hq1 hp hp1 hmean h
  have h2 := div_le_capture hT hPi hq hq1 hcap hmean'
  have h3 : ∑ ζ, q ζ * ∑ ξ, p ξ * ‖Pi ζ (gs ξ - g x)‖ ^ 2 ≤ σsq := by
    calc _ ≤ ∑ ζ, q ζ * σsq := sum_le_sum fun ζ _ => mul_le_mul_of_nonneg_left
          ((sum_norm_sq_apply_sub_le (hPi ζ) hp gs (g x)).trans hσ) (hq ζ)
      _ = σsq := by rw [← sum_mul, hq1, one_mul]
  have h4 := mul_le_mul_of_nonneg_left h2 hh
  have h5 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ β * h ^ 2 / 2)
  linarith

end Abstract

/-! ### Part IV: several steps, previous-batch and EMA augmentation

A previous batch is not independent of the current iterate, which was computed from it, so the
fixed-point form `E_ζ E_ξ` of `sum_sum_loss_le_of_indep` is the wrong statement for it.  What is
true is that the fresh batch is independent of the whole past.  We therefore work with the Markov
chain `s_{t+1} = next s_t ξ_t`, `ξ_t` i.i.d. with weights `p`, on a state `s` that contains
everything the scheme stores (iterate, gradient buffer). -/

section Chain

variable {S Ξ : Type*} [Fintype Ξ]

/-- `chainExp next p t f s` is the expectation of `f(s_t)` for the chain `s_{k+1} = next s_k ξ_k`
started at `s_0 = s`, with `ξ_k` i.i.d. with weights `p`; see `chainExp_eq_sum_path`. -/
noncomputable def chainExp (next : S → Ξ → S) (p : Ξ → ℝ) : ℕ → (S → ℝ) → S → ℝ
  | 0, f, s => f s
  | t + 1, f, s => ∑ ξ, p ξ * chainExp next p t f (next s ξ)

/-- The state reached along a sample path. -/
def runPath (next : S → Ξ → S) : (t : ℕ) → S → (Fin t → Ξ) → S
  | 0, s, _ => s
  | t + 1, s, ω => runPath next t (next s (ω 0)) (Fin.tail ω)

/-- **`chainExp` is the path expectation for i.i.d. samples**:
`chainExp next p t f s = ∑_ω (∏_i p (ω i)) f(run ω)`.  The samples `ω i` are independent because the
path weight is a product. -/
theorem chainExp_eq_sum_path (next : S → Ξ → S) (p : Ξ → ℝ) (f : S → ℝ) (t : ℕ) (s : S) :
    chainExp next p t f s = ∑ ω : Fin t → Ξ, (∏ i, p (ω i)) * f (runPath next t s ω) := by
  classical
  induction t generalizing s with
  | zero => simp [chainExp, runPath]
  | succ t ih =>
    simp only [chainExp, ih]
    rw [← (Fin.consEquiv (fun _ => Ξ)).sum_comp, Fintype.sum_prod_type]
    refine sum_congr rfl fun ξ _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun ω _ => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ, runPath, mul_assoc]

variable {next : S → Ξ → S} {p : Ξ → ℝ}

lemma chainExp_mono (hp : ∀ ξ, 0 ≤ p ξ) {f f' : S → ℝ} (h : ∀ s, f s ≤ f' s) (t : ℕ) (s : S) :
    chainExp next p t f s ≤ chainExp next p t f' s := by
  induction t generalizing s with
  | zero => exact h s
  | succ t ih => exact sum_le_sum fun ξ _ => mul_le_mul_of_nonneg_left (ih _) (hp ξ)

lemma chainExp_const (hp1 : ∑ ξ, p ξ = 1) (c : ℝ) (t : ℕ) (s : S) :
    chainExp next p t (fun _ => c) s = c := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih => simp only [chainExp, ih, ← sum_mul, hp1, one_mul]

lemma chainExp_add (f f' : S → ℝ) (t : ℕ) (s : S) :
    chainExp next p t (fun s => f s + f' s) s =
      chainExp next p t f s + chainExp next p t f' s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih => simp only [chainExp, ih, mul_add, sum_add_distrib]

lemma chainExp_const_mul (c : ℝ) (f : S → ℝ) (t : ℕ) (s : S) :
    chainExp next p t (fun s => c * f s) s = c * chainExp next p t f s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih => simp only [chainExp, ih, mul_sum, mul_left_comm]

/-- The tower property: conditioning on the state before the last sample. -/
lemma chainExp_succ' (f : S → ℝ) (t : ℕ) (s : S) :
    chainExp next p (t + 1) f s = chainExp next p t (fun s' => ∑ ξ, p ξ * f (next s' ξ)) s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    rw [chainExp]
    simp only [ih]
    rfl

/-- **Telescoping a Lyapunov inequality along the chain.**  If
`E [Φ(s') | s] ≤ Φ(s) - a(s) + b` for every state, then
`∑_{t<K} E a(s_t) ≤ Φ(s_0) - E Φ(s_K) + K b`. -/
theorem sum_chainExp_le (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1) {Φ a : S → ℝ} {b : ℝ}
    (hstep : ∀ s, ∑ ξ, p ξ * Φ (next s ξ) ≤ Φ s - a s + b) (K : ℕ) (s : S) :
    ∑ t ∈ Finset.range K, chainExp next p t a s ≤
      Φ s - chainExp next p K Φ s + K * b := by
  induction K with
  | zero => simp [chainExp]
  | succ K ih =>
    rw [sum_range_succ]
    have h1 : chainExp next p (K + 1) Φ s ≤
        chainExp next p K Φ s - chainExp next p K a s + b := by
      rw [chainExp_succ']
      refine (chainExp_mono hp hstep K s).trans (le_of_eq ?_)
      have e : (fun s => Φ s - a s + b) = fun s => (Φ s + (-1) * a s) + b := by
        funext s'; ring
      rw [e, chainExp_add, chainExp_add, chainExp_const_mul, chainExp_const hp1]
      ring
    push_cast
    linarith

/-- The minimum over the first `K` steps of an expected stationarity measure:
if `E [Φ(s') | s] ≤ Φ(s) - c a(s) + b` with `c > 0` and `Φ ≥ Φ_inf`, some `t < K` has
`E a(s_t) ≤ (Φ(s_0) - Φ_inf) / (c K) + b / c`. -/
theorem exists_chainExp_le (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1) {Φ a : S → ℝ} {b c Φinf : ℝ}
    (hc : 0 < c) (hinf : ∀ s, Φinf ≤ Φ s)
    (hstep : ∀ s, ∑ ξ, p ξ * Φ (next s ξ) ≤ Φ s - c * a s + b) {K : ℕ} (hK : 0 < K) (s : S) :
    ∃ t < K, chainExp next p t a s ≤ (Φ s - Φinf) / (K * c) + b / c := by
  have h1 := sum_chainExp_le hp hp1 (a := fun s => c * a s) hstep K s
  have h2 : Φinf ≤ chainExp next p K Φ s := by
    have := chainExp_mono hp (next := next) hinf K s
    rwa [chainExp_const hp1] at this
  simp only [chainExp_const_mul, ← mul_sum] at h1
  exact exists_le_of_mul_sum_le hc hK (by linarith)

end Chain

section Schemes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Ξ : Type*} [Fintype Ξ]

/-- One step of the stale-augmentation scheme, on states `s = (W, m)` of iterate and gradient
buffer.  The direction `D s` depends on the state only, so it is chosen before the batch `ξ` is
drawn; then
`W' = R (W - h D(s) g_ξ(W))`, `m' = (1 - α) m + α g_ξ(W)`.
Here `R` is the rank truncation.  `α = 1` is previous-batch augmentation (`m'` is the last minibatch
gradient), `0 < α < 1` is an EMA buffer. -/
def staleStep (gb : E → Ξ → E) (D : E × E → E →L[ℝ] E) (R : E → E) (h α : ℝ) (s : E × E)
    (ξ : Ξ) : E × E :=
  (R (s.1 - h • D s (gb s.1 ξ)), (1 - α) • s.2 + α • gb s.1 ξ)

variable {ℒ : E → ℝ} {g : E → E} {β : ℝ} {gb : E → Ξ → E} {D : E × E → E →L[ℝ] E} {R : E → E}
  {p : Ξ → ℝ} {h α ϑ ε σsq : ℝ}

/-- One-step loss estimate of any stale direction `D`. -/
theorem sum_loss_staleStep_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hp : ∀ ξ, 0 ≤ p ξ)
    (hp1 : ∑ ξ, p ξ = 1) (hmean : ∀ W, ∑ ξ, p ξ • gb W ξ = g W)
    (hσ : ∀ W, ∑ ξ, p ξ * ‖gb W ξ - g W‖ ^ 2 ≤ σsq) (hloss : ∀ x, ℒ (R x) ≤ ℒ x + ε)
    {s : E × E} (hD : IsOrthProj (D s)) :
    ∑ ξ, p ξ * ℒ (staleStep gb D R h α s ξ).1 ≤
      ℒ s.1 - h * (1 - β * h / 2) * ‖D s (g s.1)‖ ^ 2 + β * h ^ 2 / 2 * σsq + ε := by
  have h1 := sum_loss_sub_smul_apply_le_variance hℒ hg hβ hD hp hp1 (hmean s.1) h (hσ s.1)
  have h2 : ∑ ξ, p ξ * ℒ (staleStep gb D R h α s ξ).1 ≤
      ∑ ξ, p ξ * ℒ (s.1 - h • D s (gb s.1 ξ)) + ε := by
    calc _ ≤ ∑ ξ, p ξ * (ℒ (s.1 - h • D s (gb s.1 ξ)) + ε) :=
          sum_le_sum fun ξ _ => mul_le_mul_of_nonneg_left (hloss _) (hp ξ)
      _ = _ := by simp only [mul_add, sum_add_distrib, ← sum_mul, hp1, one_mul]
  linarith

/-- **Previous-batch and EMA buffers restore Riemannian descent for the block step.**
Take `D s = T(s) + Π(s) (1 - T(s))`, any compatible stale `Π(s)`.  Then, for every buffer rule,
`E ℒ(W') ≤ ℒ(W) - h (1 - β h / 2) ‖T(s) ∇ℒ(W)‖² + β h² σ² / 2 + ε`, and over `K` steps,
for `0 < h`, `β h < 2`,
`min_{t<K} E ‖T(s_t) ∇ℒ(W_t)‖² ≤ (ℒ(W₀) - ℒ_inf) / (K h (1 - β h / 2))
  + (β h² σ² / 2 + ε) / (h (1 - β h / 2))`.
Only the noise floor of SGD remains, of order `β h σ²`; compare `exists_tangent_sq_le_ema`. -/
theorem exists_tangent_sq_le_block (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hp : ∀ ξ, 0 ≤ p ξ)
    (hp1 : ∑ ξ, p ξ = 1) (hmean : ∀ W, ∑ ξ, p ξ • gb W ξ = g W)
    (hσ : ∀ W, ∑ ξ, p ξ * ‖gb W ξ - g W‖ ^ 2 ≤ σsq) (hloss : ∀ x, ℒ (R x) ≤ ℒ x + ε)
    {T Pi : E × E → E →L[ℝ] E} (hc : ∀ s, Compatible (T s) (Pi s)) {ℒinf : ℝ}
    (hinf : ∀ x, ℒinf ≤ ℒ x) (hh : 0 < h) (hβh : β * h < 2) {K : ℕ} (hK : 0 < K) (s₀ : E × E) :
    ∃ t < K, chainExp (staleStep gb (fun s => blockProj (T s) (Pi s)) R h α) p t
        (fun s => ‖T s (g s.1)‖ ^ 2) s₀ ≤
      (ℒ s₀.1 - ℒinf) / (K * (h * (1 - β * h / 2))) +
        (β * h ^ 2 / 2 * σsq + ε) / (h * (1 - β * h / 2)) := by
  have hc0 : 0 < h * (1 - β * h / 2) := mul_pos hh (by linarith)
  refine exists_chainExp_le hp hp1 (Φ := fun s => ℒ s.1) hc0 (fun s => hinf s.1) (fun s => ?_) hK s₀
  have h1 := sum_loss_staleStep_le hℒ hg hβ hp hp1 hmean hσ hloss (α := α) (h := h)
    (D := fun s => blockProj (T s) (Pi s)) (hc s).isOrthProj_blockProj
  rw [(hc s).norm_sq_blockProj] at h1
  have h2 := mul_nonneg hc0.le (sq_nonneg ‖Pi s (g s.1 - T s (g s.1))‖)
  nlinarith

/-- **Tracking error of the buffer.**  For `0 < α ≤ 1`, a state `s = (W, m)` and a stale orthogonal
projector `Π = D s`, with `e = m - ∇ℒ(W)` and `κ = ‖Π ∇ℒ(W)‖²`,
`E ‖e'‖² ≤ (1 - α) ‖e‖² + 2 α² σ² + (4 β² / α) (h² (κ + σ²) + ϑ²)`.
No Lipschitz property of the tangent projectors is involved. -/
theorem sum_norm_sq_tracking_le (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β)
    (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1) (hmean : ∀ W, ∑ ξ, p ξ • gb W ξ = g W)
    (hσ : ∀ W, ∑ ξ, p ξ * ‖gb W ξ - g W‖ ^ 2 ≤ σsq) (htr : ∀ x, ‖R x - x‖ ≤ ϑ)
    (hα : 0 < α) (hα1 : α ≤ 1) {s : E × E} (hD : IsOrthProj (D s)) :
    ∑ ξ, p ξ * ‖(staleStep gb D R h α s ξ).2 - g (staleStep gb D R h α s ξ).1‖ ^ 2 ≤
      (1 - α) * ‖s.2 - g s.1‖ ^ 2 + 2 * α ^ 2 * σsq +
        4 * β ^ 2 / α * (h ^ 2 * (‖D s (g s.1)‖ ^ 2 + σsq) + ϑ ^ 2) := by
  set G := g s.1 with hG
  set e := s.2 - G with he
  set n : Ξ → E := fun ξ => gb s.1 ξ - G with hn
  set d : Ξ → E := fun ξ => D s (gb s.1 ξ) with hd
  set W' : Ξ → E := fun ξ => (staleStep gb D R h α s ξ).1 with hW'
  have hσsq : 0 ≤ σsq := (sum_nonneg fun ξ _ => mul_nonneg (hp ξ) (sq_nonneg _)).trans (hσ s.1)
  -- pointwise estimate
  have hpt : ∀ ξ, ‖(staleStep gb D R h α s ξ).2 - g (W' ξ)‖ ^ 2 ≤
      (1 + α) * ‖(1 - α) • e + α • n ξ‖ ^ 2 +
        (2 / α) * (2 * β ^ 2 * (h ^ 2 * ‖d ξ‖ ^ 2 + ϑ ^ 2)) := by
    intro ξ
    have e1 : (staleStep gb D R h α s ξ).2 - g (W' ξ) =
        ((1 - α) • e + α • n ξ) + (G - g (W' ξ)) := by
      simp only [staleStep, he, hn, smul_sub, sub_smul, one_smul, hW']
      abel
    have hdelta : ‖G - g (W' ξ)‖ ≤ β * (‖h • d ξ‖ + ϑ) := by
      refine (hg _ _).trans (mul_le_mul_of_nonneg_left ?_ hβ)
      have e2 : s.1 - W' ξ = h • d ξ - (R (s.1 - h • d ξ) - (s.1 - h • d ξ)) := by
        simp only [hW', staleStep, hd]; abel
      rw [e2]
      exact (norm_sub_le _ _).trans (by gcongr; exact htr _)
    have hdelta2 : ‖G - g (W' ξ)‖ ^ 2 ≤ 2 * β ^ 2 * (h ^ 2 * ‖d ξ‖ ^ 2 + ϑ ^ 2) := by
      have h1 := pow_le_pow_left₀ (norm_nonneg _) hdelta 2
      rw [norm_smul, Real.norm_eq_abs] at h1
      have h2 : (|h| * ‖d ξ‖) ^ 2 = h ^ 2 * ‖d ξ‖ ^ 2 := by rw [mul_pow, sq_abs]
      nlinarith [mul_nonneg (sq_nonneg β) (sq_nonneg (|h| * ‖d ξ‖ - ϑ))]
    rw [e1]
    set u := (1 - α) • e + α • n ξ
    set δ := G - g (W' ξ)
    have h3 : 2 * ⟪u, δ⟫ ≤ α * ‖u‖ ^ 2 + ‖δ‖ ^ 2 / α := by
      have h4 : ⟪u, δ⟫ ≤ ‖u‖ * ‖δ‖ := real_inner_le_norm _ _
      have h5 : 0 ≤ (α * ‖u‖ - ‖δ‖) ^ 2 / α := by positivity
      have h6 : (α * ‖u‖ - ‖δ‖) ^ 2 / α = α * ‖u‖ ^ 2 - 2 * (‖u‖ * ‖δ‖) + ‖δ‖ ^ 2 / α := by
        field_simp; ring
      linarith
    have h7 : (1 + 1 / α) * ‖δ‖ ^ 2 ≤ 2 / α * ‖δ‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rw [show 2 / α = 1 / α + 1 / α by ring]
      have : 1 ≤ 1 / α := by rw [le_div_iff₀ hα]; linarith
      linarith
    have h8 : 2 / α * ‖δ‖ ^ 2 ≤ 2 / α * (2 * β ^ 2 * (h ^ 2 * ‖d ξ‖ ^ 2 + ϑ ^ 2)) :=
      mul_le_mul_of_nonneg_left hdelta2 (by positivity)
    rw [norm_add_sq_real]
    have h9 : (1 + 1 / α) * ‖δ‖ ^ 2 = ‖δ‖ ^ 2 + ‖δ‖ ^ 2 / α := by ring
    nlinarith
  -- the noise part
  have hmean0 : ∑ ξ, p ξ • n ξ = 0 := sum_smul_sub_eq_zero hp1 (hmean s.1)
  have hu : ∑ ξ, p ξ * ‖(1 - α) • e + α • n ξ‖ ^ 2 ≤ (1 - α) ^ 2 * ‖e‖ ^ 2 + α ^ 2 * σsq := by
    have h1 : ∀ ξ, p ξ * ‖(1 - α) • e + α • n ξ‖ ^ 2 =
        p ξ * (1 - α) ^ 2 * ‖e‖ ^ 2 + 2 * (1 - α) * α * (p ξ * ⟪e, n ξ⟫) +
          α ^ 2 * (p ξ * ‖n ξ‖ ^ 2) := fun ξ => by
      rw [norm_add_sq_real, inner_smul_left, inner_smul_right, norm_smul, norm_smul, mul_pow,
        mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
      simp only [conj_trivial]
      ring
    have h2 : ∑ ξ, p ξ * ⟪e, n ξ⟫ = 0 := by
      have := sum_inner_apply_eq hmean0 (ContinuousLinearMap.id ℝ E) e
      simpa using this
    simp only [h1, sum_add_distrib, ← sum_mul, hp1, one_mul, ← mul_sum, h2, mul_zero, add_zero]
    have h3 := hσ s.1
    nlinarith [sq_nonneg α]
  -- the step size part
  have hdsq : ∑ ξ, p ξ * ‖d ξ‖ ^ 2 ≤ ‖D s G‖ ^ 2 + σsq := by
    have h1 := sum_norm_sq_apply_eq hp1 (hmean s.1) (D s)
    have h2 := (sum_norm_sq_apply_sub_le hD hp (gb s.1) (g s.1)).trans (hσ s.1)
    simp only [hd]
    linarith
  have hsum : ∑ ξ, p ξ * ‖(staleStep gb D R h α s ξ).2 - g (W' ξ)‖ ^ 2 ≤
      ∑ ξ, p ξ * ((1 + α) * ‖(1 - α) • e + α • n ξ‖ ^ 2 +
        (2 / α) * (2 * β ^ 2 * (h ^ 2 * ‖d ξ‖ ^ 2 + ϑ ^ 2))) :=
    sum_le_sum fun ξ _ => mul_le_mul_of_nonneg_left (hpt ξ) (hp ξ)
  have hexp : ∑ ξ, p ξ * ((1 + α) * ‖(1 - α) • e + α • n ξ‖ ^ 2 +
      (2 / α) * (2 * β ^ 2 * (h ^ 2 * ‖d ξ‖ ^ 2 + ϑ ^ 2))) =
      (1 + α) * ∑ ξ, p ξ * ‖(1 - α) • e + α • n ξ‖ ^ 2 +
        (2 / α) * (2 * β ^ 2 * (h ^ 2 * ∑ ξ, p ξ * ‖d ξ‖ ^ 2 + ϑ ^ 2)) := by
    simp only [mul_add, sum_add_distrib, ← sum_mul, hp1, one_mul, mul_sum]
    congr 1
    · exact sum_congr rfl fun ξ _ => by ring
    · congr 1
      · exact sum_congr rfl fun ξ _ => by ring
  rw [hexp] at hsum
  have h10 : (1 + α) * ∑ ξ, p ξ * ‖(1 - α) • e + α • n ξ‖ ^ 2 ≤
      (1 - α) * ‖e‖ ^ 2 + 2 * α ^ 2 * σsq := by
    have h11 := mul_le_mul_of_nonneg_left hu (by linarith : 0 ≤ 1 + α)
    have h12 : (1 + α) * ((1 - α) ^ 2 * ‖e‖ ^ 2) ≤ (1 - α) * ‖e‖ ^ 2 := by
      have : (1 - α) * ‖e‖ ^ 2 - (1 + α) * ((1 - α) ^ 2 * ‖e‖ ^ 2) =
          α ^ 2 * ((1 - α) * ‖e‖ ^ 2) := by ring
      have h13 : 0 ≤ α ^ 2 * ((1 - α) * ‖e‖ ^ 2) :=
        mul_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
      linarith
    have h14 : (1 + α) * (α ^ 2 * σsq) ≤ 2 * α ^ 2 * σsq := by
      have : 2 * α ^ 2 * σsq - (1 + α) * (α ^ 2 * σsq) = (1 - α) * (α ^ 2 * σsq) := by ring
      have h15 : 0 ≤ (1 - α) * (α ^ 2 * σsq) :=
        mul_nonneg (by linarith) (mul_nonneg (sq_nonneg _) hσsq)
      linarith
    nlinarith
  have h16 : (2 / α) * (2 * β ^ 2 * (h ^ 2 * ∑ ξ, p ξ * ‖d ξ‖ ^ 2 + ϑ ^ 2)) ≤
      4 * β ^ 2 / α * (h ^ 2 * (‖D s G‖ ^ 2 + σsq) + ϑ ^ 2) := by
    have h17 : h ^ 2 * ∑ ξ, p ξ * ‖d ξ‖ ^ 2 ≤ h ^ 2 * (‖D s G‖ ^ 2 + σsq) :=
      mul_le_mul_of_nonneg_left hdsq (sq_nonneg _)
    have h18 : 0 ≤ 4 * β ^ 2 / α := by positivity
    calc (2 / α) * (2 * β ^ 2 * (h ^ 2 * ∑ ξ, p ξ * ‖d ξ‖ ^ 2 + ϑ ^ 2))
        = 4 * β ^ 2 / α * (h ^ 2 * ∑ ξ, p ξ * ‖d ξ‖ ^ 2 + ϑ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) h18
  linarith

/-- **EMA augmentation of the decoupled step `W - h Π g_ξ` reaches Riemannian stationarity.**
Consider the step `W' = R (W - h Π(s) g_ξ(W))`, `m' = (1 - α) m + α g_ξ(W)`, where the stale
projector `Π(s)` captures the tangent part of the buffer, `Π(s) T(s) m = T(s) m`, and `T(s)` is the
tangent projector.  If `0 < α ≤ 1` and `4 β h ≤ α`, then for `Φ₀ = ℒ(W₀) + (h / α) ‖m₀ - ∇ℒ(W₀)‖²`,
`min_{t<K} E ‖T(s_t) ∇ℒ(W_t)‖² ≤ 2 (Φ₀ - ℒ_inf) / (K h)
  + (β h + 4 α + 8 β² h² / α²) σ² + 2 ε / h + 8 β² ϑ² / α²`.
The noise floor vanishes as `h → 0`, `α → 0`, `β h / α → 0`, so an EMA buffer gives true Riemannian
stationarity, with no assumption on the curvature of the manifold or on `σ_r`; the truncation pays
`ε` in the loss and `ϑ` in the tracking.  For previous-batch augmentation, `α = 1`, the bound still
holds but its floor `4 σ²` does not vanish: that is the price of the source noise in `Π`, compare
`sharp_decoupled_capture` and the block step `exists_tangent_sq_le_block`, which has no such floor.
This makes Theorem D precise. -/
theorem exists_tangent_sq_le_ema (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hp : ∀ ξ, 0 ≤ p ξ)
    (hp1 : ∑ ξ, p ξ = 1) (hmean : ∀ W, ∑ ξ, p ξ • gb W ξ = g W)
    (hσ : ∀ W, ∑ ξ, p ξ * ‖gb W ξ - g W‖ ^ 2 ≤ σsq) (htr : ∀ x, ‖R x - x‖ ≤ ϑ)
    (hloss : ∀ x, ℒ (R x) ≤ ℒ x + ε) {T Pi : E × E → E →L[ℝ] E}
    (hc : ∀ s, Compatible (T s) (Pi s)) (hcap : ∀ s, Pi s (T s s.2) = T s s.2) {ℒinf : ℝ}
    (hinf : ∀ x, ℒinf ≤ ℒ x) (hh : 0 < h) (hα : 0 < α) (hα1 : α ≤ 1) (hβh : 4 * (β * h) ≤ α)
    {K : ℕ} (hK : 0 < K) (s₀ : E × E) :
    ∃ t < K, chainExp (staleStep gb Pi R h α) p t (fun s => ‖T s (g s.1)‖ ^ 2) s₀ ≤
      2 * (ℒ s₀.1 + h / α * ‖s₀.2 - g s₀.1‖ ^ 2 - ℒinf) / (K * h) +
        (β * h + 4 * α + 8 * β ^ 2 * h ^ 2 / α ^ 2) * σsq + 2 * ε / h +
          8 * β ^ 2 * ϑ ^ 2 / α ^ 2 := by
  have hc0 : 0 < h / 2 := by positivity
  set b : ℝ := (β * h ^ 2 / 2 + 2 * h * α + 4 * β ^ 2 * h ^ 3 / α ^ 2) * σsq + ε +
    4 * β ^ 2 * h * ϑ ^ 2 / α ^ 2 with hb
  set Φ : E × E → ℝ := fun s => ℒ s.1 + h / α * ‖s.2 - g s.1‖ ^ 2 with hΦ
  have hstep : ∀ s, ∑ ξ, p ξ * Φ (staleStep gb Pi R h α s ξ) ≤
      Φ s - h / 2 * ‖T s (g s.1)‖ ^ 2 + b := by
    intro s
    have h1 := sum_loss_staleStep_le hℒ hg hβ hp hp1 hmean hσ hloss (α := α) (h := h) (D := Pi)
      (s := s) (hc s).proj
    have h2 := sum_norm_sq_tracking_le hg hβ hp hp1 hmean hσ htr (h := h) (D := Pi) hα hα1
      (s := s) (hc s).proj
    have h3 := norm_sq_tangent_le (hc s) (hcap s) (g s.1)
    have h4 : ‖T s (s.2 - g s.1)‖ ≤ ‖s.2 - g s.1‖ := (hc s).tan.norm_le _
    have h5 := pow_le_pow_left₀ (norm_nonneg _) h4 2
    set κ := ‖Pi s (g s.1)‖ ^ 2 with hκ
    set er := ‖s.2 - g s.1‖ ^ 2 with her
    have hκ0 : 0 ≤ κ := sq_nonneg _
    have her0 : 0 ≤ er := sq_nonneg _
    have hsum : ∑ ξ, p ξ * Φ (staleStep gb Pi R h α s ξ) =
        ∑ ξ, p ξ * ℒ (staleStep gb Pi R h α s ξ).1 + h / α *
          ∑ ξ, p ξ * ‖(staleStep gb Pi R h α s ξ).2 - g (staleStep gb Pi R h α s ξ).1‖ ^ 2 := by
      simp only [hΦ, mul_add, sum_add_distrib, mul_sum]
      congr 1
      exact sum_congr rfl fun ξ _ => by ring
    have h6 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ h / α)
    have hx : β ^ 2 * h ^ 2 ≤ α ^ 2 / 16 := by
      have : (β * h) ^ 2 ≤ (α / 4) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hβ hh.le) (by linarith) 2
      nlinarith
    have hx1 : 4 * β ^ 2 * h ^ 3 / α ^ 2 ≤ h / 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have e1 : h / α * ((1 - α) * er + 2 * α ^ 2 * σsq +
          4 * β ^ 2 / α * (h ^ 2 * (κ + σsq) + ϑ ^ 2)) =
        h / α * er - h * er + 2 * h * α * σsq + 4 * β ^ 2 * h ^ 3 / α ^ 2 * κ +
          4 * β ^ 2 * h ^ 3 / α ^ 2 * σsq + 4 * β ^ 2 * h * ϑ ^ 2 / α ^ 2 := by
      field_simp
      ring
    have h7 : β * h ≤ 1 / 4 := by linarith
    have h8 : h * (β * h) ≤ h * (1 / 4) := mul_le_mul_of_nonneg_left h7 hh.le
    have h9 : κ * (4 * β ^ 2 * h ^ 3 / α ^ 2) ≤ κ * (h / 4) :=
      mul_le_mul_of_nonneg_left hx1 hκ0
    have h10 : κ * (h * (β * h)) ≤ κ * (h * (1 / 4)) := mul_le_mul_of_nonneg_left h8 hκ0
    rw [hsum]
    simp only [hΦ, hb]
    rw [e1] at h6
    have h11 : 0 ≤ h * er := mul_nonneg hh.le her0
    have h12 : ‖T s (g s.1)‖ ^ 2 ≤ κ + er := by linarith
    have h13 := mul_le_mul_of_nonneg_left h12 hc0.le
    nlinarith
  obtain ⟨t, ht, hle⟩ := exists_chainExp_le hp hp1 (Φ := Φ) (Φinf := ℒinf) hc0
    (fun s => by
      have : 0 ≤ h / α * ‖s.2 - g s.1‖ ^ 2 := by positivity
      simp only [hΦ]
      linarith [hinf s.1]) hstep hK s₀
  refine ⟨t, ht, hle.trans (le_of_eq ?_)⟩
  simp only [hΦ, hb]
  have hK' : (K : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- **Held-out batch.**  Two batches per step: at `W` draw `ζ` (weights `q`) for the bases and an
independent `ξ` (weights `p`) for the step, `W' = R (W - h Π(W, ζ) g_ξ(W))`.  The whole chain then
satisfies, with `ψ(x) = x² / (x + σ_T²)`,
`min_{t<K} E ψ(‖T ∇ℒ(W_t)‖²) ≤ (ℒ(W₀) - ℒ_inf) / (K h (1 - β h / 2))
  + (β h² σ² / 2 + ε) / (h (1 - β h / 2))`.
So decoupling by a fresh batch does give Riemannian descent, measured by `ψ` and not by the
identity: near stationarity `ψ(x) ≈ x² / σ_T²`, which is the price of `sharp_decoupled_capture`. -/
theorem exists_snr_le_heldout {Z : Type*} [Fintype Z] {q : Z → ℝ} (hq : ∀ ζ, 0 ≤ q ζ)
    (hq1 : ∑ ζ, q ζ = 1) {ms : E → Z → E} (hms : ∀ W, ∑ ζ, q ζ • ms W ζ = g W) {σT : ℝ}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hp : ∀ ξ, 0 ≤ p ξ)
    (hp1 : ∑ ξ, p ξ = 1) (hmean : ∀ W, ∑ ξ, p ξ • gb W ξ = g W)
    (hσ : ∀ W, ∑ ξ, p ξ * ‖gb W ξ - g W‖ ^ 2 ≤ σsq) (hloss : ∀ x, ℒ (R x) ≤ ℒ x + ε)
    {T : E → E →L[ℝ] E} {Pi : E → Z → E →L[ℝ] E} (hT : ∀ W, IsOrthProj (T W))
    (hPi : ∀ W ζ, IsOrthProj (Pi W ζ)) (hcap : ∀ W ζ, Pi W ζ (T W (ms W ζ)) = T W (ms W ζ))
    (hσT : ∀ W, ∑ ζ, q ζ * ‖T W (ms W ζ - g W)‖ ^ 2 ≤ σT) {ℒinf : ℝ}
    (hinf : ∀ x, ℒinf ≤ ℒ x) (hh : 0 < h) (hβh : β * h < 2) {K : ℕ} (hK : 0 < K)
    (W₀ : E) :
    ∃ t < K, chainExp (fun W (z : Z × Ξ) => R (W - h • Pi W z.1 (gb W z.2)))
        (fun z => q z.1 * p z.2) t (fun W => ‖T W (g W)‖ ^ 4 / (‖T W (g W)‖ ^ 2 + σT)) W₀ ≤
      (ℒ W₀ - ℒinf) / (K * (h * (1 - β * h / 2))) +
        (β * h ^ 2 / 2 * σsq + ε) / (h * (1 - β * h / 2)) := by
  have hc0 : 0 < h * (1 - β * h / 2) := mul_pos hh (by linarith)
  have hw : ∀ z : Z × Ξ, 0 ≤ q z.1 * p z.2 := fun z => mul_nonneg (hq _) (hp _)
  have hw1 : ∑ z : Z × Ξ, q z.1 * p z.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, hp1, mul_one, hq1]
  refine exists_chainExp_le hw hw1 (Φ := ℒ) hc0 hinf (fun W => ?_) hK W₀
  have h1 := sum_sum_loss_le_snr hℒ hg hβ (hT W) (hPi W) hq hq1 hp hp1 (hmean W) (hcap W) (hms W)
    hc0.le (hσ W)
  have hσ0 := hσT W
  have hσ1 : 0 ≤ ∑ ζ, q ζ * ‖T W (ms W ζ - g W)‖ ^ 2 :=
    sum_nonneg fun ζ _ => mul_nonneg (hq ζ) (sq_nonneg _)
  have h2 : ‖T W (g W)‖ ^ 4 / (‖T W (g W)‖ ^ 2 + σT) ≤
      ‖T W (g W)‖ ^ 4 / (‖T W (g W)‖ ^ 2 + ∑ ζ, q ζ * ‖T W (ms W ζ - g W)‖ ^ 2) := by
    rcases (add_nonneg (sq_nonneg ‖T W (g W)‖) hσ1).eq_or_lt with h0 | h0
    · have : ‖T W (g W)‖ ^ 2 = 0 := by
        have := sq_nonneg ‖T W (g W)‖
        linarith
      have h4 : ‖T W (g W)‖ ^ 4 = 0 := by
        rw [show ‖T W (g W)‖ ^ 4 = (‖T W (g W)‖ ^ 2) ^ 2 by ring, this]; norm_num
      simp [h4]
    · exact div_le_div_of_nonneg_left (by positivity) h0 (by linarith)
  have h3 := mul_le_mul_of_nonneg_left h2 hc0.le
  have hloss' : ∑ z : Z × Ξ, q z.1 * p z.2 * ℒ (R (W - h • Pi W z.1 (gb W z.2))) ≤
      ∑ ζ, q ζ * ∑ ξ, p ξ * ℒ (W - h • Pi W ζ (gb W ξ)) + ε := by
    calc _ ≤ ∑ z : Z × Ξ, q z.1 * p z.2 * (ℒ (W - h • Pi W z.1 (gb W z.2)) + ε) :=
          sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hloss _) (hw z)
      _ = _ := by
          rw [Fintype.sum_prod_type]
          have : ∀ ζ, ∑ ξ, q ζ * p ξ * (ℒ (W - h • Pi W ζ (gb W ξ)) + ε) =
              q ζ * ∑ ξ, p ξ * ℒ (W - h • Pi W ζ (gb W ξ)) + q ζ * ε := fun ζ => by
            have h5 : ∑ ξ, q ζ * p ξ * ε = q ζ * ε := by rw [← sum_mul, ← mul_sum, hp1, mul_one]
            rw [mul_sum, ← h5, ← sum_add_distrib]
            exact sum_congr rfl fun ξ _ => by ring
          simp only [this, sum_add_distrib, ← sum_mul, hq1, one_mul]
  linarith

end Schemes

/-! ### Robbins-Monro step sizes -/

section RobbinsMonro

section Timed

variable {S Ξ : Type*} [Fintype Ξ] {next : ℕ × S → Ξ → ℕ × S} {p : Ξ → ℝ}

/-- For a chain whose first component is the time, a time-dependent weight factors out of the
expectation, since the time is deterministic. -/
lemma chainExp_time_mul (hnext : ∀ z ξ, (next z ξ).1 = z.1 + 1) (w : ℕ → ℝ) (f : ℕ × S → ℝ)
    (t : ℕ) (z : ℕ × S) :
    chainExp next p t (fun z => w z.1 * f z) z = w (z.1 + t) * chainExp next p t f z := by
  induction t generalizing z with
  | zero => rfl
  | succ t ih =>
    simp only [chainExp, ih, hnext, mul_sum]
    refine sum_congr rfl fun ξ _ => ?_
    rw [show z.1 + 1 + t = z.1 + (t + 1) by omega]
    ring

lemma chainExp_time (hnext : ∀ z ξ, (next z ξ).1 = z.1 + 1) (hp1 : ∑ ξ, p ξ = 1) (b : ℕ → ℝ)
    (t : ℕ) (z : ℕ × S) : chainExp next p t (fun z => b z.1) z = b (z.1 + t) := by
  have h := chainExp_time_mul (p := p) hnext b (fun _ => 1) t z
  simpa only [mul_one, chainExp_const hp1] using h

/-- The telescoping `sum_chainExp_le` with a time-dependent additive term. -/
theorem sum_chainExp_le_timed (hnext : ∀ z ξ, (next z ξ).1 = z.1 + 1) (hp : ∀ ξ, 0 ≤ p ξ)
    (hp1 : ∑ ξ, p ξ = 1) {Φ a : ℕ × S → ℝ} {b : ℕ → ℝ}
    (hstep : ∀ z, ∑ ξ, p ξ * Φ (next z ξ) ≤ Φ z - a z + b z.1) (K : ℕ) (z : ℕ × S) :
    ∑ t ∈ Finset.range K, chainExp next p t a z ≤
      Φ z - chainExp next p K Φ z + ∑ t ∈ Finset.range K, b (z.1 + t) := by
  induction K with
  | zero => simp [chainExp]
  | succ K ih =>
    rw [sum_range_succ, sum_range_succ]
    have h1 : chainExp next p (K + 1) Φ z ≤
        chainExp next p K Φ z - chainExp next p K a z + b (z.1 + K) := by
      rw [chainExp_succ']
      refine (chainExp_mono hp hstep K z).trans (le_of_eq ?_)
      have e : (fun z' => Φ z' - a z' + b z'.1) = fun z' => (Φ z' + (-1) * a z') + b z'.1 := by
        funext z'; ring
      rw [e, chainExp_add, chainExp_add, chainExp_const_mul, chainExp_time hnext hp1]
      ring
    linarith

end Timed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ξ : Type*} [Fintype Ξ]

/-- The stale step with a time-dependent learning rate and truncation, on states `(t, W, m)`. -/
def timedStep (gb : E → Ξ → E) (D : ℕ × (E × E) → E →L[ℝ] E) (R : ℕ → E → E) (lr : ℕ → ℝ)
    (α : ℝ) (z : ℕ × (E × E)) (ξ : Ξ) : ℕ × (E × E) :=
  (z.1 + 1, staleStep gb (fun _ => D z) (R z.1) (lr z.1) α z.2 ξ)

variable {ℒ : E → ℝ} {g : E → E} {β σsq α : ℝ} {gb : E → Ξ → E} {p : Ξ → ℝ} {R : ℕ → E → E}
  {εs lr : ℕ → ℝ}

/-- **Robbins-Monro convergence for any direction chosen before the batch is drawn.**  If the
orthogonal projector `D(z)` depends on the state only and dominates the stationarity measure,
`‖T(z) ∇ℒ‖ ≤ ‖D(z) ∇ℒ‖`, and `∑ λ_t = ∞`, `∑ λ_t² < ∞`, `β λ_t ≤ 1`, with summable truncation
losses, then `liminf E ‖T(z_t) ∇ℒ(W_t)‖² = 0`: for all `ε₀ > 0`, `N` there is `t ≥ N` with
`E ‖T(z_t) ∇ℒ(W_t)‖² < ε₀`.  This is the stochastic statement of OP-TR-08, with the expectation
along the whole chain. -/
theorem frequently_sq_lt (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hp : ∀ ξ, 0 ≤ p ξ)
    (hp1 : ∑ ξ, p ξ = 1) (hmean : ∀ W, ∑ ξ, p ξ • gb W ξ = g W)
    (hσ : ∀ W, ∑ ξ, p ξ * ‖gb W ξ - g W‖ ^ 2 ≤ σsq) (hloss : ∀ k x, ℒ (R k x) ≤ ℒ x + εs k)
    (hε0 : ∀ k, 0 ≤ εs k) (hε : Summable εs) (hlr : ∀ k, 0 < lr k) (hβlr : ∀ k, β * lr k ≤ 1)
    (hdiv : ¬ Summable lr) (hsq : Summable fun k => lr k ^ 2)
    {D T : ℕ × (E × E) → E →L[ℝ] E} (hD : ∀ z, IsOrthProj (D z))
    (hT : ∀ z, ‖T z (g z.2.1)‖ ≤ ‖D z (g z.2.1)‖) {ℒinf : ℝ} (hinf : ∀ x, ℒinf ≤ ℒ x)
    (s₀ : E × E) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (N : ℕ) :
    ∃ t, N ≤ t ∧ chainExp (timedStep gb D R lr α) p t (fun z => ‖T z (g z.2.1)‖ ^ 2) (0, s₀) <
      ε₀ := by
  have hσ0 : 0 ≤ σsq :=
    (sum_nonneg fun ξ _ => mul_nonneg (hp ξ) (sq_nonneg _)).trans (hσ s₀.1)
  set c : ℕ → ℝ := fun k => β / 2 * σsq * lr k ^ 2 + εs k with hc
  have hcs : Summable c := (hsq.mul_left _).add hε
  have hc0 : ∀ k, 0 ≤ c k := fun k => add_nonneg (by positivity) (hε0 k)
  have hnext : ∀ (z : ℕ × (E × E)) (ξ : Ξ), (timedStep gb D R lr α z ξ).1 = z.1 + 1 :=
    fun _ _ => rfl
  have hstep : ∀ z : ℕ × (E × E), ∑ ξ, p ξ * ℒ (timedStep gb D R lr α z ξ).2.1 ≤
      ℒ z.2.1 - (lr z.1 / 2) * ‖T z (g z.2.1)‖ ^ 2 + c z.1 := by
    intro z
    have h1 := sum_loss_staleStep_le hℒ hg hβ hp hp1 hmean hσ (hloss z.1) (α := α) (h := lr z.1)
      (D := fun _ => D z) (s := z.2) (hD z)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (hT z) 2
    have h3 := hlr z.1
    have h4 := hβlr z.1
    have h5 : lr z.1 / 2 ≤ lr z.1 * (1 - β * lr z.1 / 2) := by nlinarith
    have h6 := mul_le_mul h5 h2 (sq_nonneg _) (by nlinarith)
    change ∑ ξ, p ξ * ℒ (staleStep gb (fun _ => D z) (R z.1) (lr z.1) α z.2 ξ).1 ≤ _
    simp only [hc]
    nlinarith
  have hsum := fun K => sum_chainExp_le_timed (p := p) hnext hp hp1
    (Φ := fun z => ℒ z.2.1) (a := fun z => (lr z.1 / 2) * ‖T z (g z.2.1)‖ ^ 2) hstep K (0, s₀)
  have ha : ∀ t, 0 ≤ chainExp (timedStep gb D R lr α) p t (fun z => ‖T z (g z.2.1)‖ ^ 2)
      (0, s₀) := fun t => by
    have h1 := chainExp_mono (next := timedStep gb D R lr α) hp
      (f := fun _ => (0 : ℝ)) (f' := fun z => ‖T z (g z.2.1)‖ ^ 2) (fun _ => sq_nonneg _) t (0, s₀)
    rwa [chainExp_const hp1] at h1
  have hw : ¬ Summable fun k => lr k / 2 := fun h =>
    hdiv ((h.mul_right 2).congr fun k => by ring)
  have h4 : ∀ t, chainExp (timedStep gb D R lr α) p t
      (fun z => lr z.1 / 2 * ‖T z (g z.2.1)‖ ^ 2) (0, s₀) = lr t / 2 *
        chainExp (timedStep gb D R lr α) p t (fun z => ‖T z (g z.2.1)‖ ^ 2) (0, s₀) := fun t => by
    have h5 := chainExp_time_mul (p := p) hnext (fun k => lr k / 2)
      (fun z => ‖T z (g z.2.1)‖ ^ 2) t (0, s₀)
    simpa only [zero_add] using h5
  refine exists_lt_of_sum_mul_le (fun k => div_nonneg (hlr k).le (by norm_num)) ha hw
    (C := ℒ s₀.1 - ℒinf + ∑' k, c k) (fun K => ?_) hε₀ N
  have h1 := hsum K
  have h2 : ℒinf ≤ chainExp (timedStep gb D R lr α) p K (fun z => ℒ z.2.1) (0, s₀) := by
    have h3 := chainExp_mono (next := timedStep gb D R lr α) hp
      (f := fun _ => ℒinf) (f' := fun z => ℒ z.2.1) (fun z => hinf _) K (0, s₀)
    rwa [chainExp_const hp1] at h3
  have h3 : ∑ t ∈ Finset.range K, c t ≤ ∑' k, c k := hcs.sum_le_tsum _ fun k _ => hc0 k
  simp only [h4, zero_add] at h1
  linarith

/-- **GeoLoRA with minibatch gradients** (arXiv 2410.18720, Thm 2; OP-TR-08, route (a)): the tangent
step `W' = R (W - λ_t P g_ξ)`, the same batch being used for all blocks, satisfies
`liminf E ‖P(W_t) ∇ℒ(W_t)‖² = 0` under Robbins-Monro step sizes and summable truncation losses.
So the conclusion of GeoLoRA survives the same-batch reuse; what its published bound misses is the
variance term (`geoLoRA_bound_false`).  For matrices take `T z = tangentProj (U z) (V z)`, which
is an orthogonal projector by `isOrthProj_tangentProj`. -/
theorem frequently_tangent_sq_lt_geoLoRA (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hp : ∀ ξ, 0 ≤ p ξ)
    (hp1 : ∑ ξ, p ξ = 1) (hmean : ∀ W, ∑ ξ, p ξ • gb W ξ = g W)
    (hσ : ∀ W, ∑ ξ, p ξ * ‖gb W ξ - g W‖ ^ 2 ≤ σsq) (hloss : ∀ k x, ℒ (R k x) ≤ ℒ x + εs k)
    (hε0 : ∀ k, 0 ≤ εs k) (hε : Summable εs) (hlr : ∀ k, 0 < lr k) (hβlr : ∀ k, β * lr k ≤ 1)
    (hdiv : ¬ Summable lr) (hsq : Summable fun k => lr k ^ 2)
    {T : ℕ × (E × E) → E →L[ℝ] E} (hT : ∀ z, IsOrthProj (T z)) {ℒinf : ℝ}
    (hinf : ∀ x, ℒinf ≤ ℒ x) (s₀ : E × E) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (N : ℕ) :
    ∃ t, N ≤ t ∧ chainExp (timedStep gb T R lr α) p t (fun z => ‖T z (g z.2.1)‖ ^ 2) (0, s₀) <
      ε₀ :=
  frequently_sq_lt hℒ hg hβ hp hp1 hmean hσ hloss hε0 hε hlr hβlr hdiv hsq hT (fun _ => le_rfl) hinf
    s₀ hε₀ N

/-- **The block step under Robbins-Monro step sizes**: `liminf E ‖T(z_t) ∇ℒ(W_t)‖² = 0` for any
stale augmentation, in particular previous-batch or EMA; for matrices `IsAugmented.compatible`
gives the hypothesis.  (OP-TR-08, route (b) asks this of the decoupled step `Π_ζ g_ξ`, for which
`decoupled_riemannian_bound_false` shows the one-step bound fails; the block step repairs the
route.) -/
theorem frequently_tangent_sq_lt_block (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hp : ∀ ξ, 0 ≤ p ξ)
    (hp1 : ∑ ξ, p ξ = 1) (hmean : ∀ W, ∑ ξ, p ξ • gb W ξ = g W)
    (hσ : ∀ W, ∑ ξ, p ξ * ‖gb W ξ - g W‖ ^ 2 ≤ σsq) (hloss : ∀ k x, ℒ (R k x) ≤ ℒ x + εs k)
    (hε0 : ∀ k, 0 ≤ εs k) (hε : Summable εs) (hlr : ∀ k, 0 < lr k) (hβlr : ∀ k, β * lr k ≤ 1)
    (hdiv : ¬ Summable lr) (hsq : Summable fun k => lr k ^ 2)
    {T Pi : ℕ × (E × E) → E →L[ℝ] E} (hc : ∀ z, Compatible (T z) (Pi z)) {ℒinf : ℝ}
    (hinf : ∀ x, ℒinf ≤ ℒ x) (s₀ : E × E) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (N : ℕ) :
    ∃ t, N ≤ t ∧ chainExp (timedStep gb (fun z => blockProj (T z) (Pi z)) R lr α) p t
        (fun z => ‖T z (g z.2.1)‖ ^ 2) (0, s₀) < ε₀ :=
  frequently_sq_lt hℒ hg hβ hp hp1 hmean hσ hloss hε0 hε hlr hβlr hdiv hsq
    (fun z => (hc z).isOrthProj_blockProj)
    (fun z => norm_apply_le_of_absorbs (hc z).tan (hc z).isOrthProj_blockProj
      ((hc z).blockProj_tan _)) hinf s₀ hε₀ N

end RobbinsMonro

/-! ### Part V: the actual augmented step on matrices -/

section Matrices

open scoped LeanDLRA.Frobenius

variable {m n r r' k k' : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype r'] [Fintype k]
  [Fintype k'] [DecidableEq r] [DecidableEq r'] [DecidableEq k] [DecidableEq k']

/-- `Û, V̂` have orthonormal columns and their ranges contain `U₀`, `A V₀`, resp. `V₀`, `Aᵀ U₀`:
the augmentation `Û = orth[U₀, A V₀]`, `V̂ = orth[V₀, Aᵀ U₀]` with source `A`.  The source is the
minibatch gradient in the same-batch scheme and a previous gradient or EMA buffer in the stale
schemes.  (Taking `V̂ = 1` gives the left-augmented step of abc-PSI.)  Such bases exist for every
source, with the exact rank: `exists_isAugmented`. -/
structure IsAugmented (U₀ : Matrix m r ℝ) (V₀ : Matrix n r' ℝ) (A : Matrix m n ℝ)
    (Uh : Matrix m k ℝ) (Vh : Matrix n k' ℝ) : Prop where
  orth_left : Uhᵀ * Uh = 1
  orth_right : Vhᵀ * Vh = 1
  contains_left : Uh * Uhᵀ * U₀ = U₀
  contains_right : Vh * Vhᵀ * V₀ = V₀
  capture_left : Uh * Uhᵀ * (A * V₀) = A * V₀
  capture_right : Vh * Vhᵀ * (Aᵀ * U₀) = Aᵀ * U₀

omit [DecidableEq r] [DecidableEq r'] [Fintype k] [Fintype k'] [DecidableEq k] [DecidableEq k'] in
/-- **`orth` exists**: augmented bases with exactly `rank [A V₀, U₀]` and `rank [Aᵀ U₀, V₀]`
columns exist for every source `A`, so `IsAugmented` is not an assumption on the data. -/
theorem exists_isAugmented (U₀ : Matrix m r ℝ) (V₀ : Matrix n r' ℝ) (A : Matrix m n ℝ) :
    ∃ (Uh : Matrix m (Fin (Matrix.fromCols (A * V₀) U₀).rank) ℝ)
      (Vh : Matrix n (Fin (Matrix.fromCols (Aᵀ * U₀) V₀).rank) ℝ), IsAugmented U₀ V₀ A Uh Vh := by
  obtain ⟨Uh, h1, h2, h3⟩ := exists_orthonormal_capture_fromCols (A * V₀) U₀ le_rfl
    (Matrix.rank_le_card_height _)
  obtain ⟨Vh, h4, h5, h6⟩ := exists_orthonormal_capture_fromCols (Aᵀ * U₀) V₀ le_rfl
    (Matrix.rank_le_card_height _)
  exact ⟨Uh, Vh, h1, h4, h3, h6, h2, h5⟩

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Commuting left and right projectors, with the augmented ones absorbing the old ones. -/
lemma compatible_mul {L₀ R₀ L R : E →L[ℝ] E} (hL₀ : IsOrthProj L₀) (hR₀ : IsOrthProj R₀)
    (hL : IsOrthProj L) (hR : IsOrthProj R) (c₀ : ∀ x, L₀ (R₀ x) = R₀ (L₀ x))
    (c₁ : ∀ x, L (R₀ x) = R₀ (L x)) (c₂ : ∀ x, L₀ (R x) = R (L₀ x))
    (c₃ : ∀ x, L (R x) = R (L x)) (h₁ : ∀ x, L (L₀ x) = L₀ x) (h₂ : ∀ x, L₀ (L x) = L₀ x)
    (h₃ : ∀ x, R (R₀ x) = R₀ x) (h₄ : ∀ x, R₀ (R x) = R₀ x) :
    Compatible (tangent L₀ R₀) (L * R) where
  tan := hL₀.tangent hR₀ c₀
  proj := hL.mul hR c₃
  comm x := by
    change L (R (tangent L₀ R₀ x)) = tangent L₀ R₀ (L (R x))
    simp only [tangent_apply, map_add, map_sub]
    rw [← c₂ x, h₁, h₃, ← c₂ (R₀ x), h₁, h₃, h₂, ← c₁ (R x), h₄, h₂]

end Calculus

namespace IsAugmented

variable {U₀ : Matrix m r ℝ} {V₀ : Matrix n r' ℝ} {A : Matrix m n ℝ} {Uh : Matrix m k ℝ}
  {Vh : Matrix n k' ℝ}

/-- The Galerkin projector of augmented bases is compatible with the tangent projector. -/
lemma compatible (h : IsAugmented U₀ V₀ A Uh Vh) (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) :
    Compatible (tangentProj U₀ V₀) (galerkinProj Uh Vh) :=
  compatible_mul (isOrthProj_leftProj hU₀) (isOrthProj_rightProj hV₀)
    (isOrthProj_leftProj h.orth_left) (isOrthProj_rightProj h.orth_right)
    (leftProj_rightProj_comm _ _) (leftProj_rightProj_comm _ _) (leftProj_rightProj_comm _ _)
    (leftProj_rightProj_comm _ _) (leftProj_leftProj_of_mul h.contains_left)
    (leftProj_leftProj_of_mul' h.contains_left) (rightProj_rightProj_of_mul h.contains_right)
    (rightProj_rightProj_of_mul' h.contains_right)

omit [Fintype r] [Fintype r'] [DecidableEq r] [DecidableEq r'] in
/-- `U₀ᵀ A V̂ V̂ᵀ = U₀ᵀ A`, the transpose of `capture_right`. -/
lemma capture_right' (h : IsAugmented U₀ V₀ A Uh Vh) : U₀ᵀ * A * (Vh * Vhᵀ) = U₀ᵀ * A := by
  have h1 := congrArg Matrix.transpose h.capture_right
  simpa [Matrix.transpose_mul, Matrix.mul_assoc] using h1

omit [Fintype r] [Fintype r'] [DecidableEq r] [DecidableEq r'] in
/-- `V₀ᵀ V̂ V̂ᵀ = V₀ᵀ`, the transpose of `contains_right`. -/
lemma contains_right' (h : IsAugmented U₀ V₀ A Uh Vh) : V₀ᵀ * (Vh * Vhᵀ) = V₀ᵀ := by
  have h1 := congrArg Matrix.transpose h.contains_right
  simpa [Matrix.transpose_mul, Matrix.mul_assoc] using h1

omit [DecidableEq r] [DecidableEq r'] in
/-- **Capture**: bases built from the source `A` capture the tangent part of `A`, and of `A` only:
`Π (P A) = P A`.  For the same batch this is the capture property; it says nothing
about `Π (P G)` for another matrix `G`, see `decoupled_not_capture`. -/
lemma capture (h : IsAugmented U₀ V₀ A Uh Vh) :
    galerkinProj Uh Vh (tangentProj U₀ V₀ A) = tangentProj U₀ V₀ A := by
  have h1 := h.contains_left
  have h2 := h.capture_left
  have h3 := h.capture_right'
  have h4 := h.contains_right'
  rw [galerkinProj_apply, tangentProj_apply]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]
  have t1 : Uh * Uhᵀ * (U₀ * U₀ᵀ * A) * (Vh * Vhᵀ) = U₀ * U₀ᵀ * A := by
    calc _ = (Uh * Uhᵀ * U₀) * (U₀ᵀ * A * (Vh * Vhᵀ)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, h3, Matrix.mul_assoc]
  have t2 : Uh * Uhᵀ * (A * V₀ * V₀ᵀ) * (Vh * Vhᵀ) = A * V₀ * V₀ᵀ := by
    calc _ = (Uh * Uhᵀ * (A * V₀)) * (V₀ᵀ * (Vh * Vhᵀ)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, h4]
  have t3 : Uh * Uhᵀ * (U₀ * U₀ᵀ * A * V₀ * V₀ᵀ) * (Vh * Vhᵀ) = U₀ * U₀ᵀ * A * V₀ * V₀ᵀ := by
    calc _ = (Uh * Uhᵀ * U₀) * (U₀ᵀ * A * V₀) * (V₀ᵀ * (Vh * Vhᵀ)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, h4]; simp only [Matrix.mul_assoc]
  rw [t1, t2, t3]

omit [DecidableEq r] [DecidableEq r'] in
/-- **The actual augmented step** is the projected step: with `W₀ = U₀ S₀ V₀ᵀ`,
`Û Ûᵀ (W₀ - λ g) V̂ V̂ᵀ = W₀ - λ Π g`.  So the abstract `x - h Π g` is what the S-step computes. -/
lemma step_eq (h : IsAugmented U₀ V₀ A Uh Vh) (S₀ : Matrix r r' ℝ) (g : Matrix m n ℝ) (lr : ℝ) :
    Uh * Uhᵀ * (U₀ * S₀ * V₀ᵀ - lr • g) * (Vh * Vhᵀ) =
      U₀ * S₀ * V₀ᵀ - lr • galerkinProj Uh Vh g := by
  rw [galerkinProj_apply, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = (Uh * Uhᵀ * U₀) * S₀ * (V₀ᵀ * (Vh * Vhᵀ)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h.contains_left, h.contains_right']

omit [DecidableEq r] [DecidableEq r'] in
/-- **When the same-batch step is plain SGD.**  If the columns of `g` are combinations of those of
`g V₀` and its rows combinations of those of `U₀ᵀ g`, the augmented projector of `g` fixes `g`.
This is the true form of the remark "`r ≥ rank g_ξ`", which is false
as stated: see `RankExample`. -/
lemma apply_self_of_factor (h : IsAugmented U₀ V₀ A Uh Vh) {C : Matrix r' n ℝ} {D : Matrix m r ℝ}
    (hC : A * V₀ * C = A) (hD : D * (U₀ᵀ * A) = A) : galerkinProj Uh Vh A = A := by
  rw [galerkinProj_apply]
  have h1 : Uh * Uhᵀ * A = A := by
    conv_lhs => rw [← hC]
    rw [← Matrix.mul_assoc, h.capture_left, hC]
  have h2 : A * (Vh * Vhᵀ) = A := by
    conv_lhs => rw [← hD]
    rw [Matrix.mul_assoc, h.capture_right', hD]
  rw [h1, h2]

omit [DecidableEq r] [DecidableEq r'] in
/-- **Small batches: the same-batch step is exactly SGD.**  Let `g = a cᵀ`, where the `b` columns of
`a` and `c` are the residuals and inputs of a batch of `b` samples of a linear layer.  If the
`b × r` matrices `cᵀ V₀`, `aᵀ U₀` have right inverses (so `b ≤ r` and the samples are in general
position with respect to the bases), then `Π g = g`.  Hence for batches of at most `r` samples the
same-batch scheme has no bias at all and full first-order progress `E ⟪G, Π_ξ g_ξ⟫ = ‖G‖²`. -/
lemma apply_self_of_batch {b : Type*} [Fintype b] [DecidableEq b] {a : Matrix m b ℝ}
    {c : Matrix n b ℝ} (h : IsAugmented U₀ V₀ (a * cᵀ) Uh Vh) {R₁ : Matrix r' b ℝ}
    {R₂ : Matrix r b ℝ} (hR₁ : cᵀ * V₀ * R₁ = 1) (hR₂ : aᵀ * U₀ * R₂ = 1) :
    galerkinProj Uh Vh (a * cᵀ) = a * cᵀ := by
  refine h.apply_self_of_factor (C := R₁ * cᵀ) (D := a * R₂ᵀ) ?_ ?_
  · calc a * cᵀ * V₀ * (R₁ * cᵀ) = a * (cᵀ * V₀ * R₁) * cᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hR₁, Matrix.mul_one]
  · have h1 : R₂ᵀ * (U₀ᵀ * a) = 1 := by
      have := congrArg Matrix.transpose hR₂
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
    calc a * R₂ᵀ * (U₀ᵀ * (a * cᵀ)) = a * (R₂ᵀ * (U₀ᵀ * a)) * cᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]

omit [Fintype r] [Fintype r'] [Fintype k] [DecidableEq k] [DecidableEq r] [DecidableEq r'] in
/-- The left-augmented step of abc-PSI (arXiv 2502.03006, Thm 5.8) is the case `V̂ = 1` of
`IsAugmented`: the left projector is a Galerkin projector with trivial right basis. -/
lemma left [Fintype k] [DecidableEq k] [DecidableEq n] (hU : Uhᵀ * Uh = 1)
    (hc : Uh * Uhᵀ * U₀ = U₀) (hK : Uh * Uhᵀ * (A * V₀) = A * V₀) :
    IsAugmented U₀ V₀ A Uh (1 : Matrix n n ℝ) :=
  ⟨hU, by simp, hc, by simp, hK, by simp⟩

omit [Fintype k'] [DecidableEq k'] [DecidableEq k] [DecidableEq r] [DecidableEq r'] in
lemma galerkinProj_one [DecidableEq n] (X : Matrix m n ℝ) :
    galerkinProj Uh (1 : Matrix n n ℝ) X = leftProj Uh X := by
  rw [galerkinProj_apply, leftProj_apply]; simp

omit [DecidableEq r] [DecidableEq r'] in
/-- **Rank of the block step.**  The block step is cheap: with `W₀ = U₀ S₀ V₀ᵀ`, its columns lie in
`[Û, g V₀]`, so `rank (W₀ - λ B g) ≤ dim Û + r'`.  With `Û = orth[U₀, m V₀]`, `r' = r`, this is
`3 r` against `2 r` for the same-batch step, before truncation. -/
theorem rank_block_step_le (h : IsAugmented U₀ V₀ A Uh Vh) (S₀ : Matrix r r' ℝ)
    (g : Matrix m n ℝ) (lr : ℝ) :
    (U₀ * S₀ * V₀ᵀ - lr • blockProj (tangentProj U₀ V₀) (galerkinProj Uh Vh) g).rank ≤
      Fintype.card k + Fintype.card r' := by
  set X₁ : Matrix m n ℝ := U₀ * (S₀ * V₀ᵀ - lr • (U₀ᵀ * g - U₀ᵀ * g * V₀ * V₀ᵀ)) with hX₁
  set X₂ : Matrix m n ℝ :=
    lr • leftProj Uh (rightProj Vh (g - tangentProj U₀ V₀ g)) with hX₂
  have e0 : tangentProj U₀ V₀ g = U₀ * (U₀ᵀ * g - U₀ᵀ * g * V₀ * V₀ᵀ) + g * V₀ * V₀ᵀ := by
    rw [tangentProj_apply, Matrix.mul_sub]
    simp only [Matrix.mul_assoc]
    abel
  have e : U₀ * S₀ * V₀ᵀ - lr • blockProj (tangentProj U₀ V₀) (galerkinProj Uh Vh) g =
      (X₁ - X₂) + (g * V₀) * (-lr • V₀ᵀ) := by
    have e1 : U₀ * S₀ * V₀ᵀ = U₀ * (S₀ * V₀ᵀ) := Matrix.mul_assoc _ _ _
    have e2 : galerkinProj Uh Vh (g - tangentProj U₀ V₀ g) =
        leftProj Uh (rightProj Vh (g - tangentProj U₀ V₀ g)) := rfl
    have e3 : (g * V₀) * (-lr • V₀ᵀ) = -(lr • (g * V₀ * V₀ᵀ)) := by
      rw [Matrix.mul_smul, neg_smul]
    rw [blockProj_apply, e2, hX₁, hX₂, Matrix.mul_sub, Matrix.mul_smul, e1, e3]
    generalize leftProj Uh (rightProj Vh (g - tangentProj U₀ V₀ g)) = Y
    rw [e0]
    generalize U₀ * (U₀ᵀ * g - U₀ᵀ * g * V₀ * V₀ᵀ) = Y₁
    generalize g * V₀ * V₀ᵀ = Y₂
    generalize U₀ * (S₀ * V₀ᵀ) = Y₃
    module
  have hL : ∀ X : Matrix r n ℝ, Uh * Uhᵀ * (U₀ * X) = U₀ * X := fun X => by
    rw [← Matrix.mul_assoc, h.contains_left]
  have h1 : X₁ - X₂ = Uh * (Uhᵀ * (X₁ - X₂)) := by
    have h2 : leftProj Uh (X₁ - X₂) = X₁ - X₂ := by
      rw [map_sub, hX₂, map_smul, (isOrthProj_leftProj h.orth_left).idem, leftProj_apply, hX₁,
        hL]
    rw [← Matrix.mul_assoc, ← leftProj_apply, h2]
  rw [e]
  refine (EckartYoung.rank_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [h1]
    refine (Matrix.rank_mul_le_left _ _).trans ?_
    exact Matrix.rank_le_card_width _
  · refine (Matrix.rank_mul_le_left _ _).trans ?_
    exact Matrix.rank_le_card_width _

end IsAugmented

section Concrete

variable [DecidableEq m] [DecidableEq n] {Ξ : Type*} [Fintype Ξ] {κ κ' : Ξ → Type*}
  [∀ ξ, Fintype (κ ξ)] [∀ ξ, Fintype (κ' ξ)] [∀ ξ, DecidableEq (κ ξ)] [∀ ξ, DecidableEq (κ' ξ)]
  {U₀ : Matrix m r ℝ} {V₀ : Matrix n r' ℝ} {Uh : ∀ ξ, Matrix m (κ ξ) ℝ}
  {Vh : ∀ ξ, Matrix n (κ' ξ) ℝ} {p : Ξ → ℝ} {gs : Ξ → Matrix m n ℝ} {G : Matrix m n ℝ}

omit [DecidableEq r] [DecidableEq r'] [DecidableEq m] [DecidableEq n] in
lemma sub_tangentProj [DecidableEq m] [DecidableEq n] (Z : Matrix m n ℝ) :
    Z - tangentProj U₀ V₀ Z = (1 - U₀ * U₀ᵀ) * Z * (1 - V₀ * V₀ᵀ) := by
  have := tangentProj_add_normal U₀ V₀ Z
  exact sub_eq_of_eq_add' this.symm

/-- **The same-minibatch first-order term of the actual augmented step.**  For bases augmented
with the minibatch gradient itself, with `N(Z) = (1 - U₀U₀ᵀ) Z (1 - V₀V₀ᵀ)`,
`E ⟪G, Π_ξ g_ξ⟫ = ‖P(W₀) G‖² + E ⟪N(G), Π_ξ N(g_ξ)⟫`.
This is the general bias formula in closed form. The tangent part has no
bias; the expected ascent of `SameMinibatchAugmentation.lean` is entirely a doubly-normal effect. -/
theorem sum_inner_augmented (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    (haug : ∀ ξ, IsAugmented U₀ V₀ (gs ξ) (Uh ξ) (Vh ξ)) (hmean : ∑ ξ, p ξ • gs ξ = G) :
    ∑ ξ, p ξ * ⟪G, galerkinProj (Uh ξ) (Vh ξ) (gs ξ)⟫ =
      ‖tangentProj U₀ V₀ G‖ ^ 2 + ∑ ξ, p ξ * ⟪(1 - U₀ * U₀ᵀ) * G * (1 - V₀ * V₀ᵀ),
        galerkinProj (Uh ξ) (Vh ξ) ((1 - U₀ * U₀ᵀ) * gs ξ * (1 - V₀ * V₀ᵀ))⟫ := by
  have h := sum_inner_sameBatch (isOrthProj_tangentProj hU₀ hV₀)
    (fun ξ => (haug ξ).compatible hU₀ hV₀) (fun ξ => (haug ξ).capture) hmean
  simpa only [sub_tangentProj] using h

omit [DecidableEq m] [DecidableEq n] in
/-- **Signal-to-noise capture for the actual decoupled bases.**  If `Û_ζ, V̂_ζ` are augmented with
an unbiased source `m_ζ`, then
`‖P G‖⁴ / (‖P G‖² + E ‖P (m_ζ - G)‖²) ≤ E ‖Π_ζ G‖²`.  Equality can hold for every signal-to-noise
ratio: `sharp_decoupled_capture`. -/
theorem div_le_capture_augmented {q : Ξ → ℝ} {ms : Ξ → Matrix m n ℝ} (hU₀ : U₀ᵀ * U₀ = 1)
    (hV₀ : V₀ᵀ * V₀ = 1) (haug : ∀ ζ, IsAugmented U₀ V₀ (ms ζ) (Uh ζ) (Vh ζ)) (hq : ∀ ζ, 0 ≤ q ζ)
    (hq1 : ∑ ζ, q ζ = 1) (hmean : ∑ ζ, q ζ • ms ζ = G) :
    ‖tangentProj U₀ V₀ G‖ ^ 4 /
        (‖tangentProj U₀ V₀ G‖ ^ 2 + ∑ ζ, q ζ * ‖tangentProj U₀ V₀ (ms ζ - G)‖ ^ 2) ≤
      ∑ ζ, q ζ * ‖galerkinProj (Uh ζ) (Vh ζ) G‖ ^ 2 :=
  div_le_capture (isOrthProj_tangentProj hU₀ hV₀)
    (fun ζ => ((haug ζ).compatible hU₀ hV₀).proj) hq hq1 (fun ζ => (haug ζ).capture) hmean

end Concrete

section Schemes

variable [DecidableEq m] [DecidableEq n] {Ξ : Type*} [Fintype Ξ]

variable {κ κ' : Matrix m n ℝ × Matrix m n ℝ → Type*} [∀ s, Fintype (κ s)]
  [∀ s, Fintype (κ' s)] [∀ s, DecidableEq (κ s)] [∀ s, DecidableEq (κ' s)]
  {U : Matrix m n ℝ × Matrix m n ℝ → Matrix m r ℝ}
  {V : Matrix m n ℝ × Matrix m n ℝ → Matrix n r' ℝ} {Uh : ∀ s, Matrix m (κ s) ℝ}
  {Vh : ∀ s, Matrix n (κ' s) ℝ} {ℒ : Matrix m n ℝ → ℝ} {g : Matrix m n ℝ → Matrix m n ℝ}
  {gb : Matrix m n ℝ → Ξ → Matrix m n ℝ} {R : Matrix m n ℝ → Matrix m n ℝ} {p : Ξ → ℝ}
  {β h α ϑ ε σsq ℒinf : ℝ}

omit [DecidableEq m] [DecidableEq n] in
/-- **The EMA theorem for the actual augmented bases.**  Iterates `W`, buffer `m`, current
orthonormal factors `U(s), V(s)`, and bases `Û(s) = orth[U(s), m V(s)]`,
`V̂(s) = orth[V(s), mᵀ U(s)]`, which are fixed before the batch is drawn; the step is
`W' = R (W - h Û Ûᵀ g_ξ(W) V̂ V̂ᵀ)` and `m' = (1 - α) m + α g_ξ(W)`.  Then for `0 < α ≤ 1`,
`4 β h ≤ α`, the conclusion of `exists_tangent_sq_le_ema` holds for the Riemannian gradient
`P(U, V) ∇ℒ(W)`.  This is Theorem D for EMA and previous-batch augmentation. -/
theorem exists_tangent_sq_le_ema_augmented (hU : ∀ s, (U s)ᵀ * U s = 1)
    (hV : ∀ s, (V s)ᵀ * V s = 1) (haug : ∀ s, IsAugmented (U s) (V s) s.2 (Uh s) (Vh s))
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hβ : 0 ≤ β) (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1) (hmean : ∀ W, ∑ ξ, p ξ • gb W ξ = g W)
    (hσ : ∀ W, ∑ ξ, p ξ * ‖gb W ξ - g W‖ ^ 2 ≤ σsq) (htr : ∀ x, ‖R x - x‖ ≤ ϑ)
    (hloss : ∀ x, ℒ (R x) ≤ ℒ x + ε) (hinf : ∀ x, ℒinf ≤ ℒ x) (hh : 0 < h) (hα : 0 < α)
    (hα1 : α ≤ 1) (hβh : 4 * (β * h) ≤ α) {K : ℕ} (hK : 0 < K) (s₀ : Matrix m n ℝ × Matrix m n ℝ) :
    ∃ t < K, chainExp (staleStep gb (fun s => galerkinProj (Uh s) (Vh s)) R h α) p t
        (fun s => ‖tangentProj (U s) (V s) (g s.1)‖ ^ 2) s₀ ≤
      2 * (ℒ s₀.1 + h / α * ‖s₀.2 - g s₀.1‖ ^ 2 - ℒinf) / (K * h) +
        (β * h + 4 * α + 8 * β ^ 2 * h ^ 2 / α ^ 2) * σsq + 2 * ε / h +
          8 * β ^ 2 * ϑ ^ 2 / α ^ 2 :=
  exists_tangent_sq_le_ema hℒ hg hβ hp hp1 hmean hσ htr hloss
    (fun s => (haug s).compatible (hU s) (hV s)) (fun s => (haug s).capture) hinf hh hα hα1 hβh hK
    s₀

omit [DecidableEq m] [DecidableEq n] in
/-- **The block step for the actual augmented bases**:
`W' = R (W - h [P(U, V) g + Û Ûᵀ N(g) V̂ V̂ᵀ])` with `g = g_ξ(W)` and `N` the doubly-normal part;
for every buffer rule, in particular previous-batch `α = 1`, the Riemannian bound of
`exists_tangent_sq_le_block` holds. -/
theorem exists_tangent_sq_le_block_augmented (hU : ∀ s, (U s)ᵀ * U s = 1)
    (hV : ∀ s, (V s)ᵀ * V s = 1) (haug : ∀ s, IsAugmented (U s) (V s) s.2 (Uh s) (Vh s))
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hβ : 0 ≤ β) (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1) (hmean : ∀ W, ∑ ξ, p ξ • gb W ξ = g W)
    (hσ : ∀ W, ∑ ξ, p ξ * ‖gb W ξ - g W‖ ^ 2 ≤ σsq) (hloss : ∀ x, ℒ (R x) ≤ ℒ x + ε)
    (hinf : ∀ x, ℒinf ≤ ℒ x) (hh : 0 < h) (hβh : β * h < 2) {K : ℕ} (hK : 0 < K)
    (s₀ : Matrix m n ℝ × Matrix m n ℝ) :
    ∃ t < K, chainExp (staleStep gb
          (fun s => blockProj (tangentProj (U s) (V s)) (galerkinProj (Uh s) (Vh s))) R h α) p t
        (fun s => ‖tangentProj (U s) (V s) (g s.1)‖ ^ 2) s₀ ≤
      (ℒ s₀.1 - ℒinf) / (K * (h * (1 - β * h / 2))) +
        (β * h ^ 2 / 2 * σsq + ε) / (h * (1 - β * h / 2)) :=
  exists_tangent_sq_le_block hℒ hg hβ hp hp1 hmean hσ hloss
    (fun s => (haug s).compatible (hU s) (hV s)) hinf hh hβh hK s₀

end Schemes

section Instance

variable {Ξ : Type*} [Fintype Ξ]

/-- A choice of left augmented basis for the source `A`. -/
noncomputable def augL (U₀ : Matrix m r ℝ) (V₀ : Matrix n r' ℝ) (A : Matrix m n ℝ) :
    Matrix m (Fin (Matrix.fromCols (A * V₀) U₀).rank) ℝ :=
  (exists_isAugmented U₀ V₀ A).choose

/-- A choice of right augmented basis for the source `A`. -/
noncomputable def augR (U₀ : Matrix m r ℝ) (V₀ : Matrix n r' ℝ) (A : Matrix m n ℝ) :
    Matrix n (Fin (Matrix.fromCols (Aᵀ * U₀) V₀).rank) ℝ :=
  (exists_isAugmented U₀ V₀ A).choose_spec.choose

omit [DecidableEq r] [DecidableEq r'] in
lemma isAugmented_aug (U₀ : Matrix m r ℝ) (V₀ : Matrix n r' ℝ) (A : Matrix m n ℝ) :
    IsAugmented U₀ V₀ A (augL U₀ V₀ A) (augR U₀ V₀ A) :=
  (exists_isAugmented U₀ V₀ A).choose_spec.choose_spec

/-- **The hypotheses of the EMA theorem can all be met**: the strongly convex quadratic
`ℒ(W) = ‖W - c‖² / 2` with additive noise `g_ξ(W) = W - c + n_ξ`, `E n_ξ = 0`, fixed orthonormal
factors, and no truncation. -/
theorem ema_instance {U₀ : Matrix m r ℝ} {V₀ : Matrix n r' ℝ} (hU₀ : U₀ᵀ * U₀ = 1)
    (hV₀ : V₀ᵀ * V₀ = 1) (c : Matrix m n ℝ) {p : Ξ → ℝ} (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1)
    {ns : Ξ → Matrix m n ℝ} (hns : ∑ ξ, p ξ • ns ξ = 0) {h α : ℝ} (hh : 0 < h) (hα : 0 < α)
    (hα1 : α ≤ 1) (hβh : 4 * h ≤ α) {K : ℕ} (hK : 0 < K) (s₀ : Matrix m n ℝ × Matrix m n ℝ) :
    ∃ t < K, chainExp (staleStep (fun W ξ => W - c + ns ξ)
          (fun s => galerkinProj (augL U₀ V₀ s.2) (augR U₀ V₀ s.2)) id h α) p t
        (fun s => ‖tangentProj U₀ V₀ (s.1 - c)‖ ^ 2) s₀ ≤
      2 * (‖s₀.1 - c‖ ^ 2 / 2 + h / α * ‖s₀.2 - (s₀.1 - c)‖ ^ 2) / (K * h) +
        (h + 4 * α + 8 * h ^ 2 / α ^ 2) * ∑ ξ, p ξ * ‖ns ξ‖ ^ 2 := by
  obtain ⟨t, ht, hle⟩ := exists_tangent_sq_le_ema_augmented (ℒ := fun W => ‖W - c‖ ^ 2 / 2)
    (g := fun W => W - c) (gb := fun W ξ => W - c + ns ξ) (R := id) (U := fun _ => U₀)
    (V := fun _ => V₀) (Uh := fun s => augL U₀ V₀ s.2) (Vh := fun s => augR U₀ V₀ s.2) (β := 1)
    (ϑ := 0) (ε := 0) (ℒinf := 0) (σsq := ∑ ξ, p ξ * ‖ns ξ‖ ^ 2) (fun _ => hU₀) (fun _ => hV₀)
    (fun s => isAugmented_aug U₀ V₀ s.2) (hasFDerivAt_half_norm_sq_sub c) (fun x y => by simp)
    zero_le_one hp hp1
    (fun W => by simp only [smul_add, sum_add_distrib, hns, add_zero, ← sum_smul, hp1, one_smul])
    (fun W => by simp) (fun x => by simp) (fun x => by simp) (fun x => by positivity) hh hα hα1
    (by linarith) hK s₀
  exact ⟨t, ht, hle.trans_eq (by ring)⟩

end Instance

end Matrices

section Truncation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ℒ : E → ℝ} {g : E → E}
  {β : ℝ} {R : E → E} {ϑ B : ℝ}

/-- The truncation hypothesis `ℒ (R x) ≤ ℒ x + ε` of the schemes follows from a gradient bound,
with `ε = B ϑ + β ϑ² / 2`. -/
theorem loss_trunc_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (htr : ∀ x, ‖R x - x‖ ≤ ϑ)
    (hB : ∀ x, ‖g x‖ ≤ B) (x : E) : ℒ (R x) ≤ ℒ x + (B * ϑ + β * ϑ ^ 2 / 2) := by
  have h1 := descent_lemma hℒ hg x (R x)
  have h2 : ⟪g x, R x - x⟫ ≤ B * ϑ :=
    (real_inner_le_norm _ _).trans (mul_le_mul (hB x) (htr x) (norm_nonneg _)
      ((norm_nonneg _).trans (hB x)))
  have h3 : β / 2 * ‖R x - x‖ ^ 2 ≤ β / 2 * ϑ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (htr x) 2) (by positivity)
  linarith

end Truncation

/-! ### Part VI: exact numbers -/

namespace Examples

open scoped LeanDLRA.Frobenius
open SameBatchExample

section Original

/-! The two-point example of `SameMinibatchAugmentation.lean`, now with all the fixes. -/

variable {Uh Vh Uh' Vh' : Matrix (Fin 3) (Fin 2) ℝ}

lemma inner_G_plus_Gm (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁)) : ⟪G, galerkinProj Uh Vh Gm⟫ = 7 := by
  rw [galerkinProj_plus hU hV, Pp_conj, Frobenius.inner_def]
  norm_num [G, Gm, N, Fin.sum_univ_three]

lemma norm_sq_plus_Gm (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁)) : ‖galerkinProj Uh Vh Gm‖ ^ 2 = 49 := by
  rw [galerkinProj_plus hU hV, Pp_conj, Frobenius.norm_sq_eq_sum]
  norm_num [G, Gm, N, Fin.sum_univ_three]

lemma inner_G_minus_Gp (hU : IsOrthBasisOf Uh (augBasis e₁ Gm e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gmᵀ e₁)) : ⟪G, galerkinProj Uh Vh Gp⟫ = 7 := by
  rw [galerkinProj_minus hU hV, Pm_conj, Frobenius.inner_def]
  norm_num [G, Gp, N, Fin.sum_univ_three]

lemma norm_sq_minus_Gp (hU : IsOrthBasisOf Uh (augBasis e₁ Gm e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gmᵀ e₁)) : ‖galerkinProj Uh Vh Gp‖ ^ 2 = 49 := by
  rw [galerkinProj_minus hU hV, Pm_conj, Frobenius.norm_sq_eq_sum]
  norm_num [G, Gp, N, Fin.sum_univ_three]

lemma norm_sq_plus_noise' (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁)) : ‖galerkinProj Uh Vh (Gm - G)‖ ^ 2 = 38 := by
  rw [galerkinProj_plus hU hV, Pp_conj, Frobenius.norm_sq_eq_sum]
  norm_num [G, Gm, N, Fin.sum_univ_three]

lemma norm_sq_minus_noise' (hU : IsOrthBasisOf Uh (augBasis e₁ Gm e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gmᵀ e₁)) : ‖galerkinProj Uh Vh (Gp - G)‖ ^ 2 = 38 := by
  rw [galerkinProj_minus hU hV, Pm_conj, Frobenius.norm_sq_eq_sum]
  norm_num [G, Gp, N, Fin.sum_univ_three]

lemma tangent_G : tangentProj e₁ e₁ G = !![0, 1, 1; 1, 0, 0; 1, 0, 0] := by
  rw [tangentProj_e₁_apply]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [G, W₀, Matrix.mul_apply, Fin.sum_univ_three]

lemma tangent_Gp : tangentProj e₁ e₁ Gp = !![0, 2, 0; 2, 0, 0; 0, 0, 0] := by
  rw [tangentProj_e₁_apply]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Gp, G, N, W₀, Matrix.mul_apply, Fin.sum_univ_three]

lemma tangent_Gm : tangentProj e₁ e₁ Gm = !![0, 0, 2; 0, 0, 0; 2, 0, 0] := by
  rw [tangentProj_e₁_apply]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Gm, G, N, W₀, Matrix.mul_apply, Fin.sum_univ_three]

lemma norm_sq_tangent_G : ‖tangentProj e₁ e₁ G‖ ^ 2 = 4 := by
  rw [tangent_G, Frobenius.norm_sq_eq_sum]
  norm_num [Fin.sum_univ_three]

/-- The ascent of the example is entirely doubly-normal, the first-order term `-1` of the
minibatch `+` is `4 - 5`: the tangent part contributes `4`, the block
`⟪N(G), Π₊ N(G₊)⟫` contributes `-5`. -/
theorem split_plus (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁)) :
    ⟪G, tangentProj e₁ e₁ Gp⟫ = 4 ∧
      ⟪G - tangentProj e₁ e₁ G, galerkinProj Uh Vh (Gp - tangentProj e₁ e₁ Gp)⟫ = -5 := by
  refine ⟨tangent_plus.1, ?_⟩
  rw [galerkinProj_plus hU hV, Pp_conj, tangent_G, tangent_Gp, Frobenius.inner_def]
  norm_num [G, Gp, N, Fin.sum_univ_three]

/-- **Decoupled augmentation, exact expected loss.**  With the bases drawn from one minibatch and
the step from an independent one, the four outcomes average to
`E ℒ = ℒ(W₀) - 3 η + 41/2 η²`.  Compare the same-minibatch scheme, `ℒ(W₀) + η + 33/2 η²`
(`loss_sameBatch_plus`), and the tangent step, `ℒ(W₀) - 4 η + 4 η²` (`expected_loss_tangent`). -/
theorem expected_loss_decoupled (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁)) (hU' : IsOrthBasisOf Uh' (augBasis e₁ Gm e₁))
    (hV' : IsOrthBasisOf Vh' (augBasis e₁ Gmᵀ e₁)) (η : ℝ) :
    1 / 4 * (loss (W₀ - η • galerkinProj Uh Vh Gp) + loss (W₀ - η • galerkinProj Uh Vh Gm) +
        loss (W₀ - η • galerkinProj Uh' Vh' Gp) + loss (W₀ - η • galerkinProj Uh' Vh' Gm)) =
      loss W₀ - 3 * η + 41 / 2 * η ^ 2 := by
  rw [loss_W₀_sub_smul, loss_W₀_sub_smul, loss_W₀_sub_smul, loss_W₀_sub_smul,
    inner_G_plus hU hV, norm_sq_plus hU hV, inner_G_plus_Gm hU hV, norm_sq_plus_Gm hU hV,
    inner_G_minus_Gp hU' hV', norm_sq_minus_Gp hU' hV', inner_G_minus hU' hV',
    norm_sq_minus hU' hV']
  ring

/-- **Decoupling restores descent only below a step-size threshold**: in the example, the expected
loss of the decoupled scheme decreases iff `η < 6/41`.  (The same-minibatch scheme increases the
loss for every `η > 0`, `loss_W₀_lt_sameBatch`.)  Above the threshold the variance term wins, which
is why "restores descent" has to carry a step size condition. -/
theorem decoupled_lt_iff (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁)) (hU' : IsOrthBasisOf Uh' (augBasis e₁ Gm e₁))
    (hV' : IsOrthBasisOf Vh' (augBasis e₁ Gmᵀ e₁)) {η : ℝ} (hη : 0 < η) :
    1 / 4 * (loss (W₀ - η • galerkinProj Uh Vh Gp) + loss (W₀ - η • galerkinProj Uh Vh Gm) +
        loss (W₀ - η • galerkinProj Uh' Vh' Gp) + loss (W₀ - η • galerkinProj Uh' Vh' Gm)) <
      loss W₀ ↔ η < 6 / 41 := by
  rw [expected_loss_decoupled hU hV hU' hV']
  constructor
  · intro h
    by_contra hcon
    have hcon' := not_lt.1 hcon
    nlinarith
  · intro h
    nlinarith

/-- **The capture property is false for decoupled augmentation.**  The
bases `Π₊, Π₋` built from one minibatch do not contain the tangent gradient of the *full* gradient,
and they capture only `E ‖Π_ζ G‖² = 3` of its energy `‖P(W₀) G‖² = 4`. -/
theorem decoupled_not_capture (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁)) (hU' : IsOrthBasisOf Uh' (augBasis e₁ Gm e₁))
    (hV' : IsOrthBasisOf Vh' (augBasis e₁ Gmᵀ e₁)) :
    galerkinProj Uh Vh (tangentProj e₁ e₁ G) ≠ tangentProj e₁ e₁ G ∧
      1 / 2 * ‖galerkinProj Uh Vh G‖ ^ 2 + 1 / 2 * ‖galerkinProj Uh' Vh' G‖ ^ 2 = 3 ∧
      ‖tangentProj e₁ e₁ G‖ ^ 2 = 4 := by
  refine ⟨fun h => ?_, ?_, norm_sq_tangent_G⟩
  · have h1 := congrFun (congrFun h 0) 2
    rw [galerkinProj_plus hU hV, Pp_conj, tangent_G] at h1
    norm_num at h1
  · rw [norm_sq_plus_G hU hV, norm_sq_minus_G hU' hV']; norm_num

/-- **The Riemannian descent claimed for decoupled augmentation is false.**  The bound
`E ℒ ≤ ℒ(W₀) - η (1 - β η / 2) ‖P(W₀) G‖² + β η² / 2 · E ‖Π_ζ (g_ξ - G)‖²`, which follows
from the capture property, fails in the example for every `0 < η < 2`. -/
theorem decoupled_riemannian_bound_false (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁)) (hU' : IsOrthBasisOf Uh' (augBasis e₁ Gm e₁))
    (hV' : IsOrthBasisOf Vh' (augBasis e₁ Gmᵀ e₁)) {η : ℝ} (hη : 0 < η) (hη' : η < 2) :
    loss W₀ - η * (1 - 1 * η / 2) * ‖tangentProj e₁ e₁ (grad W₀)‖ ^ 2 +
        1 * η ^ 2 / 2 * (1 / 4 * (‖galerkinProj Uh Vh (Gp - grad W₀)‖ ^ 2 +
          ‖galerkinProj Uh Vh (Gm - grad W₀)‖ ^ 2 + ‖galerkinProj Uh' Vh' (Gp - grad W₀)‖ ^ 2 +
          ‖galerkinProj Uh' Vh' (Gm - grad W₀)‖ ^ 2)) <
      1 / 4 * (loss (W₀ - η • galerkinProj Uh Vh Gp) + loss (W₀ - η • galerkinProj Uh Vh Gm) +
        loss (W₀ - η • galerkinProj Uh' Vh' Gp) + loss (W₀ - η • galerkinProj Uh' Vh' Gm)) := by
  rw [expected_loss_decoupled hU hV hU' hV', grad_W₀, norm_sq_tangent_G, norm_sq_plus_noise hU hV,
    norm_sq_plus_noise' hU hV, norm_sq_minus_noise' hU' hV', norm_sq_minus_noise hU' hV']
  nlinarith [mul_pos hη (by linarith : (0 : ℝ) < 2 - η)]

lemma block_plus_Gp (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁)) :
    blockProj (tangentProj e₁ e₁) (galerkinProj Uh Vh) Gp =
      !![0, 2, 0; 2, -5, 0; 0, 0, 0] := by
  rw [blockProj_apply, galerkinProj_plus hU hV, Pp_conj, tangent_Gp]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Gp, G, N]

lemma block_plus_Gm (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁)) :
    blockProj (tangentProj e₁ e₁) (galerkinProj Uh Vh) Gm =
      !![0, 0, 2; 0, 7, 0; 2, 0, 0] := by
  rw [blockProj_apply, galerkinProj_plus hU hV, Pp_conj, tangent_Gm]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Gm, G, N]

lemma block_minus_Gp (hU : IsOrthBasisOf Uh (augBasis e₁ Gm e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gmᵀ e₁)) :
    blockProj (tangentProj e₁ e₁) (galerkinProj Uh Vh) Gp =
      !![0, 2, 0; 2, 0, 0; 0, 0, 7] := by
  rw [blockProj_apply, galerkinProj_minus hU hV, Pm_conj, tangent_Gp]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Gp, G, N]

lemma block_minus_Gm (hU : IsOrthBasisOf Uh (augBasis e₁ Gm e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gmᵀ e₁)) :
    blockProj (tangentProj e₁ e₁) (galerkinProj Uh Vh) Gm =
      !![0, 0, 2; 0, 0, 0; 2, 0, -5] := by
  rw [blockProj_apply, galerkinProj_minus hU hV, Pm_conj, tangent_Gm]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Gm, G, N]

/-- **The block step in the example**: `E ℒ = ℒ(W₀) - 5 η + 45/2 η²`.  The first-order rate `5`
is at least `‖P(W₀) G‖² = 4`, as `sum_loss_block_le` guarantees, while the decoupled step only
reaches `3`.  Here the rate `5` includes `E ‖Π_ζ N(G)‖² = 1`; the price is the larger second-order
term from the doubly-normal noise, which is deliberately large in this example. -/
theorem expected_loss_block (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁)) (hU' : IsOrthBasisOf Uh' (augBasis e₁ Gm e₁))
    (hV' : IsOrthBasisOf Vh' (augBasis e₁ Gmᵀ e₁)) (η : ℝ) :
    1 / 4 * (loss (W₀ - η • blockProj (tangentProj e₁ e₁) (galerkinProj Uh Vh) Gp) +
        loss (W₀ - η • blockProj (tangentProj e₁ e₁) (galerkinProj Uh Vh) Gm) +
        loss (W₀ - η • blockProj (tangentProj e₁ e₁) (galerkinProj Uh' Vh') Gp) +
        loss (W₀ - η • blockProj (tangentProj e₁ e₁) (galerkinProj Uh' Vh') Gm)) =
      loss W₀ - 5 * η + 45 / 2 * η ^ 2 := by
  rw [block_plus_Gp hU hV, block_plus_Gm hU hV, block_minus_Gp hU' hV', block_minus_Gm hU' hV',
    loss_W₀_sub_smul, loss_W₀_sub_smul, loss_W₀_sub_smul, loss_W₀_sub_smul]
  simp only [Frobenius.inner_def, Frobenius.norm_sq_eq_sum]
  norm_num [G, Fin.sum_univ_three]
  ring

/-- The decorrelated outcome: tangent part of `G₊`, doubly-normal part of `G₋`. -/
noncomputable def Gpm : Matrix (Fin 3) (Fin 3) ℝ := !![0, 2, 0; 2, 7, 0; 0, 0, -5]

/-- The decorrelated outcome: tangent part of `G₋`, doubly-normal part of `G₊`. -/
noncomputable def Gmp : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 2; 0, -5, 0; 2, 0, 7]

/-- **The ascent of the example comes from coupling, not from the noise level.**  Keep the marginal
laws of the tangent block and of the doubly-normal block of the example, and make them independent:
the four outcomes `G₊, G_{+-}, G_{-+}, G₋` are unbiased, the bases depend on the tangent block only,
and the same-minibatch first-order term becomes `+5` instead of `-1`
(an instance of `sum_sum_inner_of_block_indep`). -/
theorem decorrelated_first_order (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁)) (hU' : IsOrthBasisOf Uh' (augBasis e₁ Gm e₁))
    (hV' : IsOrthBasisOf Vh' (augBasis e₁ Gmᵀ e₁)) :
    (1 / 4 : ℝ) • (Gp + Gpm + Gmp + Gm) = G ∧
      1 / 4 * (⟪G, galerkinProj Uh Vh Gp⟫ + ⟪G, galerkinProj Uh Vh Gpm⟫ +
        ⟪G, galerkinProj Uh' Vh' Gmp⟫ + ⟪G, galerkinProj Uh' Vh' Gm⟫) = 5 := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Gp, Gm, Gpm, Gmp, G, N]
  · rw [inner_G_plus hU hV, inner_G_minus hU' hV', galerkinProj_plus hU hV,
      galerkinProj_minus hU' hV', Pp_conj, Pm_conj, Frobenius.inner_def, Frobenius.inner_def]
    norm_num [G, Gpm, Gmp, Fin.sum_univ_three]

/-- **The left-augmented step ascends as well.**  In the same example, the same-minibatch step of
abc-PSI (arXiv 2502.03006), `Y₁ = Y₀ - h P_Û g_ξ` with `Û = orth[U₀, g_ξ V₀]`, has expected
first-order term `-1`.  So the negative result concerns abc-PSI and augmented Galerkin steps, not
GeoLoRA (`sum_inner_tangent`). -/
theorem abcPSI_first_order (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁))
    (hU' : IsOrthBasisOf Uh' (augBasis e₁ Gm e₁)) :
    1 / 2 * ⟪grad W₀, leftProj Uh Gp⟫ + 1 / 2 * ⟪grad W₀, leftProj Uh' Gm⟫ = -1 := by
  rw [leftProj_apply, leftProj_apply,
    (hU.mul_transpose_eq_mul_transpose augBasis_Gp Up_orth).trans Up_mul_transpose,
    (hU'.mul_transpose_eq_mul_transpose augBasis_Gm Um_orth).trans Um_mul_transpose, grad_W₀,
    Frobenius.inner_def, Frobenius.inner_def]
  norm_num [G, Gp, Gm, N, Pp, Pm, Matrix.mul_apply, Fin.sum_univ_three]

/-- The rank-one iterate `(e₁ - 2 η e₂) (e₁ - 2 η e₂)ᵀ`. -/
noncomputable def WTp (η : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, -2 * η, 0; -2 * η, 4 * η ^ 2, 0; 0, 0, 0]

/-- The rank-one iterate `(e₁ - 2 η e₃) (e₁ - 2 η e₃)ᵀ`. -/
noncomputable def WTm (η : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, -2 * η; 0, 0, 0; -2 * η, 0, 4 * η ^ 2]

lemma rank_WTp (η : ℝ) : (WTp η).rank ≤ 1 := by
  have h : WTp η = (!![1; -2 * η; 0] : Matrix (Fin 3) (Fin 1) ℝ) *
      (!![1, -2 * η, 0] : Matrix (Fin 1) (Fin 3) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [WTp]
    ring
  rw [h]
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))

lemma rank_WTm (η : ℝ) : (WTm η).rank ≤ 1 := by
  have h : WTm η = (!![1; 0; -2 * η] : Matrix (Fin 3) (Fin 1) ℝ) *
      (!![1, 0, -2 * η] : Matrix (Fin 1) (Fin 3) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [WTm]
    ring
  rw [h]
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))

/-- **Truncation back to the old rank removes the ascent.** In the example, both same-minibatch
iterates `Ŵ_± = W₀ - η Π_± G_±` are within `ϑ = 5 η` of a rank-one matrix `W_±` (the only change is
in the doubly-normal block, whose entry is `O(η)`), and `ℒ(W_±) = 3 - 4 η + 8 η² + 8 η⁴ < 3 = ℒ(W₀)`
for `0 < η ≤ 1/4`, while `ℒ(Ŵ_±) > ℒ(W₀)`. So Theorem C is a statement about the iterate before
truncation, or a rank-growing step that retains the new direction: the biased block is exactly the
one a truncation with `ϑ ≳ η ‖N‖` deletes. -/
theorem truncation_removes_ascent (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁)) (hU' : IsOrthBasisOf Uh' (augBasis e₁ Gm e₁))
    (hV' : IsOrthBasisOf Vh' (augBasis e₁ Gmᵀ e₁)) {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 4) :
    ‖WTp η - (W₀ - η • galerkinProj Uh Vh Gp)‖ ≤ 5 * η ∧
      ‖WTm η - (W₀ - η • galerkinProj Uh' Vh' Gm)‖ ≤ 5 * η ∧
      loss (WTp η) < loss W₀ ∧ loss (WTm η) < loss W₀ ∧
      loss W₀ < loss (W₀ - η • galerkinProj Uh Vh Gp) ∧
      loss W₀ < loss (W₀ - η • galerkinProj Uh' Vh' Gm) := by
  have hlossG : ∀ D : Matrix (Fin 3) (Fin 3) ℝ, loss (W₀ - (1 : ℝ) • D) =
      loss W₀ - 1 * ⟪G, D⟫ + 1 ^ 2 / 2 * ‖D‖ ^ 2 := fun D => loss_W₀_sub_smul D 1
  have hp : WTp η = W₀ - (1 : ℝ) • (!![0, 2 * η, 0; 2 * η, -(4 * η ^ 2), 0; 0, 0, 0]) := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [WTp, W₀]
  have hm : WTm η = W₀ - (1 : ℝ) • (!![0, 0, 2 * η; 0, 0, 0; 2 * η, 0, -(4 * η ^ 2)]) := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [WTm, W₀]
  have hηsmall : 8 * η + 8 * η ^ 3 < 4 := by nlinarith [mul_pos hη hη, mul_pos (mul_pos hη hη) hη]
  have hdiff : ∀ {X : Matrix (Fin 3) (Fin 3) ℝ},
      ‖X‖ ^ 2 = (5 * η - 4 * η ^ 2) ^ 2 → ‖X‖ ≤ 5 * η := fun {X} h => by
    have h1 : (5 * η - 4 * η ^ 2) ^ 2 ≤ (5 * η) ^ 2 := by
      have h2 : 0 ≤ η ^ 3 * (5 - 2 * η) := mul_nonneg (by positivity) (by linarith)
      nlinarith [sq_nonneg (η ^ 2)]
    exact le_of_sq_le_sq (by rw [h]; exact h1) (by positivity)
  have hasc := loss_W₀_lt_sameBatch hU hV hU' hV' hη
  refine ⟨hdiff ?_, hdiff ?_, ?_, ?_, hasc.1, hasc.2⟩
  · rw [galerkinProj_plus hU hV, Pp_conj, Frobenius.norm_sq_eq_sum]
    norm_num [WTp, W₀, G, Gp, N, Fin.sum_univ_three]
    ring
  · rw [galerkinProj_minus hU' hV', Pm_conj, Frobenius.norm_sq_eq_sum]
    norm_num [WTm, W₀, G, Gm, N, Fin.sum_univ_three]
    ring
  · rw [hp, hlossG, Frobenius.inner_def, Frobenius.norm_sq_eq_sum]
    norm_num [G, Fin.sum_univ_three]
    nlinarith [mul_pos hη hη]
  · rw [hm, hlossG, Frobenius.inner_def, Frobenius.norm_sq_eq_sum]
    norm_num [G, Fin.sum_univ_three]
    nlinarith [mul_pos hη hη]

end Original

section Family

/-! A two-parameter family containing the example of `SameMinibatchAugmentation.lean`, `δ = 1`,
`c = 6`.  Tangent signal and tangent noise have the common size `δ`, the doubly-normal gradient is
fixed, and the doubly-normal noise has size `c`. -/

variable (δ c : ℝ)

/-- The full gradient of the family. -/
noncomputable def famG : Matrix (Fin 3) (Fin 3) ℝ := !![0, δ, δ; δ, 1, 0; δ, 0, 1]

/-- The minibatch gradient `+` of the family. -/
noncomputable def famP : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 2 * δ, 0; 2 * δ, 1 - c, 0; 0, 0, 1 + c]

/-- The minibatch gradient `-` of the family. -/
noncomputable def famM : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 2 * δ; 0, 1 + c, 0; 2 * δ, 0, 1 - c]

lemma fam_mean : (1 / 2 : ℝ) • famP δ c + (1 / 2 : ℝ) • famM δ c = famG δ := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [famP, famM, famG] <;> ring

lemma famP_aug : augBasis e₁ (famP δ c) e₁ = Up * !![1, 0; 0, 2 * δ] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [augBasis, e₁, famP, Up, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

lemma famP_aug' : augBasis e₁ (famP δ c)ᵀ e₁ = Up * !![1, 0; 0, 2 * δ] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [augBasis, e₁, famP, Up, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

lemma famM_aug : augBasis e₁ (famM δ c) e₁ = Um * !![1, 0; 0, 2 * δ] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [augBasis, e₁, famM, Um, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

lemma famM_aug' : augBasis e₁ (famM δ c)ᵀ e₁ = Um * !![1, 0; 0, 2 * δ] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [augBasis, e₁, famM, Um, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

variable {δ c} {Uh Vh Uh' Vh' : Matrix (Fin 3) (Fin 2) ℝ}

lemma fam_galerkin_plus (hU : IsOrthBasisOf Uh (augBasis e₁ (famP δ c) e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ (famP δ c)ᵀ e₁)) (X : Matrix (Fin 3) (Fin 3) ℝ) :
    galerkinProj Uh Vh X = Pp * X * Pp := by
  rw [galerkinProj_apply,
    (hU.mul_transpose_eq_mul_transpose (famP_aug δ c) Up_orth).trans Up_mul_transpose,
    (hV.mul_transpose_eq_mul_transpose (famP_aug' δ c) Up_orth).trans Up_mul_transpose]

lemma fam_galerkin_minus (hU : IsOrthBasisOf Uh (augBasis e₁ (famM δ c) e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ (famM δ c)ᵀ e₁)) (X : Matrix (Fin 3) (Fin 3) ℝ) :
    galerkinProj Uh Vh X = Pm * X * Pm := by
  rw [galerkinProj_apply,
    (hU.mul_transpose_eq_mul_transpose (famM_aug δ c) Um_orth).trans Um_mul_transpose,
    (hV.mul_transpose_eq_mul_transpose (famM_aug' δ c) Um_orth).trans Um_mul_transpose]

/-- The bases of the family exist as soon as `δ ≠ 0`. -/
lemma fam_isOrthBasisOf (hδ : δ ≠ 0) :
    IsOrthBasisOf Up (augBasis e₁ (famP δ c) e₁) ∧ IsOrthBasisOf Up (augBasis e₁ (famP δ c)ᵀ e₁) ∧
      IsOrthBasisOf Um (augBasis e₁ (famM δ c) e₁) ∧
        IsOrthBasisOf Um (augBasis e₁ (famM δ c)ᵀ e₁) := by
  obtain ⟨w, hw⟩ : ∃ w, 2 * δ * w = 1 :=
    ⟨(2 * δ)⁻¹, mul_inv_cancel₀ (mul_ne_zero two_ne_zero hδ)⟩
  have h1 : !![1, 0; 0, 2 * δ] * !![1, 0; 0, w] = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hw]
  refine ⟨isOrthBasisOf_iff.1 ⟨Up_orth, !![1, 0; 0, w], ?_⟩,
    isOrthBasisOf_iff.1 ⟨Up_orth, !![1, 0; 0, w], ?_⟩,
    isOrthBasisOf_iff.1 ⟨Um_orth, !![1, 0; 0, w], ?_⟩,
    isOrthBasisOf_iff.1 ⟨Um_orth, !![1, 0; 0, w], ?_⟩⟩
  · rw [famP_aug, Matrix.mul_assoc, h1, Matrix.mul_one]
  · rw [famP_aug', Matrix.mul_assoc, h1, Matrix.mul_one]
  · rw [famM_aug, Matrix.mul_assoc, h1, Matrix.mul_one]
  · rw [famM_aug', Matrix.mul_assoc, h1, Matrix.mul_one]

/-- **The family: same-minibatch, decoupled and tangent first-order terms.**
`E ⟪G, Π_ξ g_ξ⟫ = 4 δ² + 1 - c`, `E ‖Π_ζ G‖² = 2 δ² + 1`, `‖P G‖² = 4 δ²`.  So the bias relative to
a decoupled projector is `2 δ² - c`, the tangent gain `2 δ²` against the doubly-normal term `c` of
`sum_inner_sameBatch_sub_decoupled`, and it has either sign. -/
theorem family_first_orders (hU : IsOrthBasisOf Uh (augBasis e₁ (famP δ c) e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ (famP δ c)ᵀ e₁))
    (hU' : IsOrthBasisOf Uh' (augBasis e₁ (famM δ c) e₁))
    (hV' : IsOrthBasisOf Vh' (augBasis e₁ (famM δ c)ᵀ e₁)) :
    1 / 2 * ⟪famG δ, galerkinProj Uh Vh (famP δ c)⟫ +
        1 / 2 * ⟪famG δ, galerkinProj Uh' Vh' (famM δ c)⟫ = 4 * δ ^ 2 + 1 - c ∧
      1 / 2 * ‖galerkinProj Uh Vh (famG δ)‖ ^ 2 + 1 / 2 * ‖galerkinProj Uh' Vh' (famG δ)‖ ^ 2 =
        2 * δ ^ 2 + 1 ∧
      ‖tangentProj e₁ e₁ (famG δ)‖ ^ 2 = 4 * δ ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [fam_galerkin_plus hU hV, fam_galerkin_minus hU' hV', Pp_conj, Pm_conj,
      Frobenius.inner_def, Frobenius.inner_def]
    norm_num [famG, famP, famM, Fin.sum_univ_three]
    ring
  · rw [fam_galerkin_plus hU hV, fam_galerkin_minus hU' hV', Pp_conj, Pm_conj,
      Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum]
    norm_num [famG, Fin.sum_univ_three]
    ring
  · rw [tangentProj_e₁_apply, Frobenius.norm_sq_eq_sum]
    norm_num [famG, W₀, Matrix.mul_apply, Fin.sum_univ_three]
    ring

/-- **The size of the bias is first order in the noise when the tangent signal is at noise
level.**  Scale the family as noise of a batch of size `B`, `δ = δ₀ / √B`, `c = c₀ / √B`.  The gap
between same-batch and decoupled first-order terms is
`2 δ₀² / B - c₀ / √B`, which is of order `1 / √B`, not `1 / B`.  So "the gap closes
like `1 / B`" is not universal (it is the behaviour when the tangent
signal dominates).  This is a noise-scaling model, not a literal `B`-fold average. -/
theorem family_gap {δ₀ c₀ B : ℝ} (hB : 0 < B) :
    2 * (δ₀ / √B) ^ 2 - c₀ / √B = 2 * δ₀ ^ 2 / B - c₀ / √B := by
  rw [div_pow, Real.sq_sqrt hB.le]; ring

/-- **Ascent in the family happens exactly for `c > 1 + 4 δ²`.** -/
theorem family_ascent_iff (hU : IsOrthBasisOf Uh (augBasis e₁ (famP δ c) e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ (famP δ c)ᵀ e₁))
    (hU' : IsOrthBasisOf Uh' (augBasis e₁ (famM δ c) e₁))
    (hV' : IsOrthBasisOf Vh' (augBasis e₁ (famM δ c)ᵀ e₁)) :
    1 / 2 * ⟪famG δ, galerkinProj Uh Vh (famP δ c)⟫ +
        1 / 2 * ⟪famG δ, galerkinProj Uh' Vh' (famM δ c)⟫ < 0 ↔ 1 + 4 * δ ^ 2 < c := by
  rw [(family_first_orders hU hV hU' hV').1]
  constructor <;> intro h <;> linarith

end Family

section Sharp

/-! The sharpness family: gradient and noise purely tangent, so that same-batch bases capture
everything while decoupled bases lose the factor `1 + s²`. -/

/-- `shG` is the tangent gradient `e₂ e₁ᵀ + e₁ e₂ᵀ`, and `shg s` adds the tangent noise
`s (e₃ e₁ᵀ + e₁ e₃ᵀ)`: `shG = shg 0`, the two minibatch gradients are `shg s` and `shg (-s)`. -/
noncomputable def shg (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, s; 1, 0, 0; s, 0, 0]

/-- Reference basis for the bases built from `shg s`. -/
noncomputable def shU (s : ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  !![1, 0; 0, (√(1 + s ^ 2))⁻¹; 0, s * (√(1 + s ^ 2))⁻¹]

/-- Change of basis. -/
noncomputable def shD (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, √(1 + s ^ 2)]

/-- The left and right projector of the bases built from `shg s`. -/
noncomputable def shQ (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, (1 + s ^ 2)⁻¹, s * (1 + s ^ 2)⁻¹; 0, s * (1 + s ^ 2)⁻¹, s ^ 2 * (1 + s ^ 2)⁻¹]

lemma one_add_sq_pos (s : ℝ) : 0 < 1 + s ^ 2 := by positivity

lemma inv_sqrt_mul_self (s : ℝ) :
    (√(1 + s ^ 2))⁻¹ * (√(1 + s ^ 2))⁻¹ = (1 + s ^ 2)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (one_add_sq_pos s).le]

lemma inv_sqrt_mul_sqrt (s : ℝ) : (√(1 + s ^ 2))⁻¹ * √(1 + s ^ 2) = 1 :=
  inv_mul_cancel₀ (Real.sqrt_pos.2 (one_add_sq_pos s)).ne'

lemma shU_orth (s : ℝ) : (shU s)ᵀ * shU s = 1 := by
  have hw : (√(1 + s ^ 2))⁻¹ * (√(1 + s ^ 2))⁻¹ * (1 + s ^ 2) = 1 := by
    rw [inv_sqrt_mul_self]; exact inv_mul_cancel₀ (one_add_sq_pos s).ne'
  unfold shU
  generalize (√(1 + s ^ 2))⁻¹ = w at hw ⊢
  have h1 : (!![1, 0; 0, w; 0, s * w] : Matrix (Fin 3) (Fin 2) ℝ)ᵀ * !![1, 0; 0, w; 0, s * w] =
      !![1, 0; 0, w * w * (1 + s ^ 2)] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]
    ring
  rw [h1, hw]
  ext i j; fin_cases i <;> fin_cases j <;> simp

lemma shU_mul_transpose (s : ℝ) : shU s * (shU s)ᵀ = shQ s := by
  have h := inv_sqrt_mul_self s
  unfold shU shQ
  generalize (√(1 + s ^ 2))⁻¹ = w at h ⊢
  generalize (1 + s ^ 2)⁻¹ = a at h ⊢
  subst h
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma sh_aug (s : ℝ) : augBasis e₁ (shg s) e₁ = shU s * shD s := by
  have h := inv_sqrt_mul_sqrt s
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [augBasis, e₁, shg, shU, shD, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_two, h, mul_assoc]

lemma sh_aug' (s : ℝ) : augBasis e₁ (shg s)ᵀ e₁ = shU s * shD s := by
  have h := inv_sqrt_mul_sqrt s
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [augBasis, e₁, shg, shU, shD, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_two, h, mul_assoc]

/-- The reference bases are admissible for every `s`. -/
lemma sh_isOrthBasisOf (s : ℝ) :
    IsOrthBasisOf (shU s) (augBasis e₁ (shg s) e₁) ∧
      IsOrthBasisOf (shU s) (augBasis e₁ (shg s)ᵀ e₁) := by
  have h := inv_sqrt_mul_sqrt s
  have h1 : shD s * !![1, 0; 0, (√(1 + s ^ 2))⁻¹] = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    have h' : √(1 + s ^ 2) * (√(1 + s ^ 2))⁻¹ = 1 := by rw [mul_comm]; exact h
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [shD, Matrix.mul_apply, Fin.sum_univ_two, h']
  refine ⟨isOrthBasisOf_iff.1 ⟨shU_orth s, !![1, 0; 0, (√(1 + s ^ 2))⁻¹], ?_⟩,
    isOrthBasisOf_iff.1 ⟨shU_orth s, !![1, 0; 0, (√(1 + s ^ 2))⁻¹], ?_⟩⟩
  · rw [sh_aug, Matrix.mul_assoc, h1, Matrix.mul_one]
  · rw [sh_aug', Matrix.mul_assoc, h1, Matrix.mul_one]

variable {s : ℝ} {Uh Vh Uh' Vh' : Matrix (Fin 3) (Fin 2) ℝ}

lemma sh_galerkin (hU : IsOrthBasisOf Uh (augBasis e₁ (shg s) e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ (shg s)ᵀ e₁)) (X : Matrix (Fin 3) (Fin 3) ℝ) :
    galerkinProj Uh Vh X = shQ s * X * shQ s := by
  rw [galerkinProj_apply,
    (hU.mul_transpose_eq_mul_transpose (sh_aug s) (shU_orth s)).trans (shU_mul_transpose s),
    (hV.mul_transpose_eq_mul_transpose (sh_aug' s) (shU_orth s)).trans (shU_mul_transpose s)]

/-- `Q (shg t) Q`: only the first row and column survive. -/
lemma shQ_conj (s t : ℝ) : shQ s * shg t * shQ s =
    !![0, (1 + s * t) * (1 + s ^ 2)⁻¹, s * (1 + s * t) * (1 + s ^ 2)⁻¹;
      (1 + s * t) * (1 + s ^ 2)⁻¹, 0, 0;
      s * (1 + s * t) * (1 + s ^ 2)⁻¹, 0, 0] := by
  unfold shQ shg
  generalize (1 + s ^ 2)⁻¹ = a
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

lemma inner_sh (s t u : ℝ) :
    ⟪shg u, shQ s * shg t * shQ s⟫ = 2 * (1 + s * t) * (1 + s * u) * (1 + s ^ 2)⁻¹ := by
  rw [shQ_conj, Frobenius.inner_def]
  norm_num [shg, Fin.sum_univ_three]
  ring

lemma norm_sq_sh (s t : ℝ) :
    ‖shQ s * shg t * shQ s‖ ^ 2 = 2 * (1 + s * t) ^ 2 * (1 + s ^ 2)⁻¹ := by
  have h1 : (1 + s ^ 2)⁻¹ * (1 + s ^ 2) = 1 := inv_mul_cancel₀ (one_add_sq_pos s).ne'
  rw [shQ_conj, Frobenius.norm_sq_eq_sum]
  norm_num [Fin.sum_univ_three]
  generalize (1 + s ^ 2)⁻¹ = a at h1 ⊢
  linear_combination 2 * (1 + s * t) ^ 2 * a * h1

lemma tangent_shg (t : ℝ) : tangentProj e₁ e₁ (shg t) = shg t := by
  rw [tangentProj_e₁_apply]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [shg, W₀, Matrix.mul_apply, Fin.sum_univ_three]

lemma norm_sq_shg (t : ℝ) : ‖shg t‖ ^ 2 = 2 + 2 * t ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  norm_num [shg, Fin.sum_univ_three]
  ring

lemma norm_sq_tangent_sh (s : ℝ) : ‖tangentProj e₁ e₁ (shg s - shg 0)‖ ^ 2 = 2 * s ^ 2 := by
  rw [map_sub, tangent_shg, tangent_shg, Frobenius.norm_sq_eq_sum]
  norm_num [shg, Fin.sum_univ_three]
  ring

/-- The two minibatch gradients `shg s`, `shg (-s)` are unbiased for `shg 0`. -/
lemma shg_mean (s : ℝ) : (1 / 2 : ℝ) • shg s + (1 / 2 : ℝ) • shg (-s) = shg 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [shg]

/-- **The signal-to-noise capture bound is sharp for every signal-to-noise ratio.**  With the
tangent gradient `shg 0`, `‖P G‖² = 2`, and tangent noise `E ‖P (g_ζ - G)‖² = 2 s²`, the bases built
from either minibatch capture exactly
`E ‖Π_ζ G‖² = 2 / (1 + s²) = ‖P G‖⁴ / (‖P G‖² + σ_P²)`.
So `div_le_capture_augmented` cannot be improved, and the loss against `‖P G‖²`
is by the full factor `1 + SNR⁻¹`, unbounded as the noise grows. -/
theorem sharp_decoupled_capture (hU : IsOrthBasisOf Uh (augBasis e₁ (shg s) e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ (shg s)ᵀ e₁))
    (hU' : IsOrthBasisOf Uh' (augBasis e₁ (shg (-s)) e₁))
    (hV' : IsOrthBasisOf Vh' (augBasis e₁ (shg (-s))ᵀ e₁)) :
    1 / 2 * ‖galerkinProj Uh Vh (shg 0)‖ ^ 2 + 1 / 2 * ‖galerkinProj Uh' Vh' (shg 0)‖ ^ 2 =
        2 / (1 + s ^ 2) ∧
      ‖tangentProj e₁ e₁ (shg 0)‖ ^ 4 / (‖tangentProj e₁ e₁ (shg 0)‖ ^ 2 +
        (1 / 2 * ‖tangentProj e₁ e₁ (shg s - shg 0)‖ ^ 2 +
          1 / 2 * ‖tangentProj e₁ e₁ (shg (-s) - shg 0)‖ ^ 2)) = 2 / (1 + s ^ 2) := by
  have h1 := (one_add_sq_pos s).ne'
  have hT : ‖tangentProj e₁ e₁ (shg 0)‖ ^ 2 = 2 := by
    rw [tangent_shg, norm_sq_shg]; ring
  have hT4 : ‖tangentProj e₁ e₁ (shg 0)‖ ^ 4 = 4 := by
    rw [show ‖tangentProj e₁ e₁ (shg 0)‖ ^ 4 = (‖tangentProj e₁ e₁ (shg 0)‖ ^ 2) ^ 2 by ring, hT]
    norm_num
  constructor
  · rw [sh_galerkin hU hV, sh_galerkin hU' hV', norm_sq_sh, norm_sq_sh]
    simp only [mul_zero, add_zero, neg_sq, one_pow, mul_one]
    field_simp
    ring
  · rw [hT, hT4, norm_sq_tangent_sh, norm_sq_tangent_sh]
    simp only [neg_sq]
    field_simp
    ring

/-- The same-minibatch step captures everything in this family: `Π_± g_± = g_±`, so
`E ⟪G, Π_ξ g_ξ⟫ = ‖P G‖² = 2`, against `2 / (1 + s²)` for decoupled bases. -/
theorem sharp_sameBatch_inner (hU : IsOrthBasisOf Uh (augBasis e₁ (shg s) e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ (shg s)ᵀ e₁))
    (hU' : IsOrthBasisOf Uh' (augBasis e₁ (shg (-s)) e₁))
    (hV' : IsOrthBasisOf Vh' (augBasis e₁ (shg (-s))ᵀ e₁)) :
    1 / 2 * ⟪shg 0, galerkinProj Uh Vh (shg s)⟫ +
      1 / 2 * ⟪shg 0, galerkinProj Uh' Vh' (shg (-s))⟫ = 2 := by
  have h1 := (one_add_sq_pos s).ne'
  rw [sh_galerkin hU hV, sh_galerkin hU' hV', inner_sh, inner_sh]
  simp only [mul_zero, add_zero, mul_one, neg_mul, neg_sq]
  field_simp
  ring

/-- The quadratic loss of the sharpness family, `ℒ(W) = ½ ‖W - W₀ + shg 0‖²`. -/
noncomputable def shLoss (W : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := ‖W - (W₀ - shg 0)‖ ^ 2 / 2

lemma shLoss_sub_smul (D : Matrix (Fin 3) (Fin 3) ℝ) (η : ℝ) :
    shLoss (W₀ - η • D) = shLoss W₀ - η * ⟪shg 0, D⟫ + η ^ 2 / 2 * ‖D‖ ^ 2 := by
  rw [shLoss, sub_sub_sub_cancel_left, half_norm_sq_sub_smul, shLoss, sub_sub_cancel]

/-- **Same-batch can beat decoupling, at every noise level.**  In the sharpness family, for every
learning rate,
`E ℒ(same-batch) - E ℒ(decoupled) = - 2 s² / (1 + s²) · η (1 - η)`,
so for `s ≠ 0`, `0 < η < 1` the same-minibatch scheme is strictly better.  Thus decoupling is a
worst-case repair, not an improvement: that same-batch
is slower than decoupled augmentation at small batch sizes is not a theorem. -/
theorem sharp_gain_sameBatch (hU : IsOrthBasisOf Uh (augBasis e₁ (shg s) e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ (shg s)ᵀ e₁))
    (hU' : IsOrthBasisOf Uh' (augBasis e₁ (shg (-s)) e₁))
    (hV' : IsOrthBasisOf Vh' (augBasis e₁ (shg (-s))ᵀ e₁)) (η : ℝ) :
    (1 / 2 * shLoss (W₀ - η • galerkinProj Uh Vh (shg s)) +
        1 / 2 * shLoss (W₀ - η • galerkinProj Uh' Vh' (shg (-s)))) -
      1 / 4 * (shLoss (W₀ - η • galerkinProj Uh Vh (shg s)) +
        shLoss (W₀ - η • galerkinProj Uh Vh (shg (-s))) +
        shLoss (W₀ - η • galerkinProj Uh' Vh' (shg s)) +
        shLoss (W₀ - η • galerkinProj Uh' Vh' (shg (-s)))) =
      -(2 * s ^ 2 / (1 + s ^ 2) * (η * (1 - η))) := by
  have h1 := (one_add_sq_pos s).ne'
  simp only [sh_galerkin hU hV, sh_galerkin hU' hV', shLoss_sub_smul, inner_sh, norm_sq_sh]
  simp only [mul_zero, add_zero, mul_one, mul_neg, neg_mul, neg_neg, neg_sq]
  field_simp
  ring

end Sharp

namespace RankExample

/-! The bias does not vanish in general when `r ≥ rank g_ξ`. -/

/-- A rank-one minibatch gradient with invertible `S`-block. -/
noncomputable def g₁ : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; 1, -1]

/-- A rank-one minibatch gradient with vanishing `K`- and `L`-blocks. -/
noncomputable def g₂ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 5]

/-- The full gradient `(g₁ + g₂) / 2`. -/
noncomputable def G : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, -1 / 2; 1 / 2, 2]

/-- The rank-one bases `U₀ = V₀ = e₁`. -/
noncomputable def e : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

lemma rank_g₁ : g₁.rank ≤ 1 := by
  have h : g₁ = (!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ) * (!![1, -1] : Matrix (Fin 1) (Fin 2) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [g₁]
  rw [h]
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))

lemma rank_g₂ : g₂.rank ≤ 1 := by
  have h : g₂ = (!![0; 5] : Matrix (Fin 2) (Fin 1) ℝ) * (!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [g₂]
  rw [h]
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))

lemma isAugmented₁ :
    IsAugmented e e g₁ (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  constructor <;> simp

lemma isAugmented₂ : IsAugmented e e g₂ e e := by
  have he : eᵀ * e = 1 := by
    ext i j; fin_cases i; fin_cases j; simp [e, Matrix.mul_apply, Fin.sum_univ_two]
  have h2 : g₂ * e = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [g₂, e, Matrix.mul_apply, Fin.sum_univ_two]
  have h3 : g₂ᵀ * e = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [g₂, e, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨he, he, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, he, Matrix.mul_one]
  · rw [Matrix.mul_assoc, he, Matrix.mul_one]
  · rw [h2, Matrix.mul_zero]
  · rw [h3, Matrix.mul_zero]

/-- The bases of `isAugmented₁` span exactly `[e, g₁ e]`, and the basis `e` of `isAugmented₂` lies
in the span of `[e, g₂ e]`: both are honest `orth`, not larger spaces. -/
lemma bases_exact :
    (∃ C : Matrix (Fin 2) (Fin 2) ℝ, (1 : Matrix (Fin 2) (Fin 2) ℝ) =
        (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * C) ∧
      (g₁ * e = !![1; 1]) ∧
      (∃ C : Matrix (Fin 2) (Fin 1) ℝ, e = (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * C) ∧
      g₂ * e = 0 := by
  refine ⟨⟨!![1, -1; 0, 1], ?_⟩, ?_, ⟨!![1; 0], ?_⟩, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [g₁, g₂, e, Matrix.mul_apply, Fin.sum_univ_two]

/-- **"`r ≥ rank g_ξ` implies no bias" is false.**  With `r = 1`, both unbiased minibatch gradients
have rank one, yet the second is annihilated by its own augmented projector, and the expected
first-order term is `-1/4 < 0`.  The true condition is `IsAugmented.apply_self_of_factor`.  The
example is not robust: it relies on `g₂ e = 0`, and for generic rank-one `g₂` the conclusion of
`IsAugmented.apply_self_of_batch` holds. -/
theorem first_order_neg :
    g₁.rank ≤ 1 ∧ g₂.rank ≤ 1 ∧ (1 / 2 : ℝ) • g₁ + (1 / 2 : ℝ) • g₂ = G ∧
      galerkinProj e e g₂ ≠ g₂ ∧
      1 / 2 * ⟪G, galerkinProj (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) g₁⟫ +
        1 / 2 * ⟪G, galerkinProj e e g₂⟫ = -(1 / 4) := by
  have h1 : galerkinProj (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) g₁ = g₁ := by
    rw [galerkinProj_apply]; simp
  have h2 : galerkinProj e e g₂ = 0 := by
    rw [galerkinProj_apply]
    have h3 : g₂ * e = 0 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [g₂, e, Matrix.mul_apply, Fin.sum_univ_two]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc g₂, h3, Matrix.zero_mul, Matrix.mul_zero]
  refine ⟨rank_g₁, rank_g₂, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [g₁, g₂, G]
  · rw [h2]
    intro h
    have := congrFun (congrFun h 1) 1
    norm_num [g₂] at this
  · rw [h1, h2, inner_zero_right, Frobenius.inner_def]
    norm_num [G, g₁, Fin.sum_univ_two]

end RankExample

end Examples

end LeanDLRA.Novel.MinibatchBias
