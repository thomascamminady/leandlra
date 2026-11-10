import LeanDLRA.Stability.Energy
import LeanDLRA.Training.Descent
import LeanDLRA.Foundations.Projector
import LeanDLRA.Matrix.Projectors

/-!
# Loss descent of the explicit Euler projector-splitting training step

The projector-splitting integrator with one explicit Euler step per substep, applied to the
gradient flow of a loss `ℒ` with gradient `g`, is the step
`kslEulerStep P₁ Q₀ (fun y => -g y) h` of `LeanDLRA/Stability/Energy.lean`: K-step, backward
S-step and L-step, where `P₁` projects onto the new left basis and `Q₀` onto the old right
basis (the training step of arXiv 2502.03006, Sec. 3.2). This module bounds the loss after one
such step, for the quadratic loss `½ ‖x - a‖²` and for losses with a `β`-Lipschitz gradient,
and after one step of the backward-corrected variant (arXiv 2502.03006, Sec. 3.3), in which
the S-step is replaced by the projection onto the new left basis.

Unless stated otherwise, `P₁` and `Q₀` are commuting orthogonal projectors, the new basis
captures the K-step, `P₁ (x - h Q₀ g(x)) = x - h Q₀ g(x)` (the property that a QR factorisation
of the K-step result provides), `y` is the result of the step,
`T₁ = tangent P₁ Q₀ = P₁ + Q₀ - P₁ Q₀`, and gradients are exact. The state `x` need not lie in
the range of `Q₀`; only `loss_kslEulerStep_gt_of_goldenRatio_lt` assumes `Q₀ x = x`.

## Main definitions

* `bcPsiStep P₁ g h x`: the backward-corrected step `P₁ x - h P₁ g(P₁ x)`. It equals
  `projGradStep P₁ g h (P₁ x)` (`bcPsiStep_eq_projGradStep`).
* `psiTrainStep g h U₀ S₀ V₀ U₁`, `bcPsiTrainStep g h U₀ S₀ V₀ U₁`: the two steps on the factors
  of `U₀ S₀ V₀ᵀ` with a new left basis `U₁`. With `P₁ = leftProj U₁` and `Q₀ = rightProj V₀`
  they equal `kslEulerStep` (`psiTrainStep_eq_kslEulerStep`, if `U₁ U₁ᵀ K₁ = K₁` for the K-step
  result `K₁`) and `bcPsiStep` (`bcPsiTrainStep_eq`).

## Main results

* `kslEulerStep_frobenius_sq_identity`: for the quadratic loss and `e = x - a`,
  `‖y - a‖² - ‖x - a‖² = -h (2 - h) ‖T₁ e‖² - h² (1 - h)² (2 - h²) ‖P₁ Q₀ e‖²`.
  No singular value of the state appears.
* `loss_kslEulerStep_quadratic_le`: for the quadratic loss and `0 ≤ h ≤ φ`, the golden ratio
  `φ = (1 + √5) / 2`, `ℒ(y) ≤ ℒ(x) - (h / 2) (1 + h - h²) ‖T₁ g(x)‖²`.
* `loss_kslEulerStep_gt_of_goldenRatio_lt`: the condition `h ≤ φ` cannot be relaxed. For
  `ℒ(x) = ½ ‖x‖²`, a nonzero `x` with `P₁ x = x` and `Q₀ x = x`, and every `h > φ`, the loss
  after the step is larger than before, while for `h < 2` the gradient step `x - h g(x)`
  decreases it.
* `loss_kslEulerStep_le_of_smooth`: for a `β`-Lipschitz gradient and `0 ≤ h`,
  `ℒ(y) ≤ ℒ(x) - h (1 - β h (2 + β h) - (β h / 2) (1 + β h)⁴) ‖T₁ g(x)‖²`.
* `loss_kslEulerStep_le_of_smooth_quarter`: for `β h ≤ 1/4` this is
  `ℒ(y) ≤ ℒ(x) - (h / 8) ‖T₁ g(x)‖²`. The constants do not depend on the state.
* `exists_tangentGrad_sq_le_of_psi`: along an iteration of such steps with `0 < h`,
  `β h ≤ 1/4` and `ℒinf ≤ ℒ(x_k)` for all `k`, some `k < n` satisfies
  `‖T_k g(x_k)‖² ≤ 8 (ℒ(x₀) - ℒinf) / (n h)`.
* `loss_bcPsiStep_le`: for the backward-corrected step, a `β`-Lipschitz gradient, every `h`
  and every `x`, `ℒ(y) ≤ ℒ(x) - h (1 - β h / 2) (‖(1 - P₁) Q₀ g(x)‖² + ‖P₁ g(P₁ x)‖²)`.
* `loss_psiTrainStep_le`, `loss_bcPsiTrainStep_le`: the bounds of
  `loss_kslEulerStep_le_of_smooth_quarter` and of `loss_bcPsiStep_le` for the steps on the
  factors, for `U₁ᵀ U₁ = 1`, `V₀ᵀ V₀ = 1` and with `tangentProj U₁ V₀` in the place of `T₁`.

## Implementation notes

Every theorem is about one deterministic step with exact gradients, a gradient that is
Lipschitz on the whole space and a new basis that captures the K-step. Stochastic gradients,
truncation of the rank and the loss of rank during training are not treated.

## References

* arXiv 2502.03006, Sec. 3.2 and 3.3 (the two training steps), Sec. 5 (Lemmas 5.1 and 5.4).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Novel.OpSB64

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The PSI training step in full-space form -/

section Abstract

variable {P₁ Q₀ : E →L[ℝ] E} {ℒ : E → ℝ} {g : E → E} {β h : ℝ}

/-- K-step with the gradient-flow field `F = -g`: `x ↦ x - h Q₀ g(x)`. -/
lemma kslK_neg (Q₀ : E →L[ℝ] E) (g : E → E) (h : ℝ) (x : E) :
    kslK Q₀ (fun y => -g y) h x = x - h • Q₀ (g x) := by
  simp [kslK, sub_eq_add_neg]

/-- Backward S-step with `F = -g` from a point of the new basis: `z ↦ z + h P₁ Q₀ g(z)`. -/
lemma kslS_neg (g : E → E) (h : ℝ) {z : E} (hz : P₁ z = z) :
    kslS P₁ Q₀ (fun y => -g y) h z = z + h • P₁ (Q₀ (g z)) := by
  simp [kslS, hz, sub_eq_add_neg]

/-- L-step with `F = -g`: `w ↦ w - h P₁ g(w)`. -/
lemma kslL_neg (P₁ : E →L[ℝ] E) (g : E → E) (h : ℝ) (w : E) :
    kslL P₁ (fun y => -g y) h w = w - h • P₁ (g w) := by
  simp [kslL, sub_eq_add_neg]

/-- The PSI step unfolded: with `k = x - h Q₀ g(x)` (K-step), `s = k + h P₁ Q₀ g(k)` (backward
S-step) and `y = s - h P₁ g(s)` (L-step), `y = kslEulerStep P₁ Q₀ (-g) h x`, provided the new
basis captures the K-step result (`P₁ k = k`). -/
lemma kslEulerStep_neg_eq (g : E → E) (h : ℝ) {x : E}
    (hcap : P₁ (x - h • Q₀ (g x)) = x - h • Q₀ (g x)) :
    kslEulerStep P₁ Q₀ (fun y => -g y) h x =
      (x - h • Q₀ (g x) + h • P₁ (Q₀ (g (x - h • Q₀ (g x))))) -
        h • P₁ (g (x - h • Q₀ (g x) + h • P₁ (Q₀ (g (x - h • Q₀ (g x)))))) := by
  rw [kslEulerStep, kslK_neg, kslS_neg g h hcap, kslL_neg]

/-- The displacement of one PSI step is `-h T₁ ∇ℒ(x)` plus gradient-variation remainders:
`y - x = -h T₁ g(x) + h (P₁ Q₀ (g k - g x) - P₁ (g s - g x))`. -/
lemma kslEulerStep_neg_sub (g : E → E) (h : ℝ) {x : E}
    (hcap : P₁ (x - h • Q₀ (g x)) = x - h • Q₀ (g x)) :
    kslEulerStep P₁ Q₀ (fun y => -g y) h x - x =
      -(h • tangent P₁ Q₀ (g x)) +
        h • (P₁ (Q₀ (g (x - h • Q₀ (g x)) - g x)) -
          P₁ (g (x - h • Q₀ (g x) + h • P₁ (Q₀ (g (x - h • Q₀ (g x))))) - g x)) := by
  rw [kslEulerStep_neg_eq g h hcap]
  simp only [tangent_apply, map_sub, smul_sub, smul_add]
  abel

/-- Components of a vector dominated by its tangent projection: `‖Q₀ v‖ ≤ ‖T₁ v‖`,
`‖P₁ v‖ ≤ ‖T₁ v‖`, `‖P₁ Q₀ v‖ ≤ ‖T₁ v‖` and `‖(1 - P₁) Q₀ v‖ ≤ ‖T₁ v‖`. -/
lemma norm_components_le_tangent (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (v : E) :
    ‖Q₀ v‖ ≤ ‖tangent P₁ Q₀ v‖ ∧ ‖P₁ v‖ ≤ ‖tangent P₁ Q₀ v‖ ∧
      ‖P₁ (Q₀ v)‖ ≤ ‖tangent P₁ Q₀ v‖ ∧ ‖Q₀ v - P₁ (Q₀ v)‖ ≤ ‖tangent P₁ Q₀ v‖ := by
  have hQT : Q₀ (tangent P₁ Q₀ v) = Q₀ v := by
    simp only [tangent_apply, map_add, map_sub, ← hc, hQ₀.idem]
    abel
  have hPT : P₁ (tangent P₁ Q₀ v) = P₁ v := by
    simp only [tangent_apply, map_add, map_sub, hP₁.idem]
    abel
  have h1 : ‖Q₀ v‖ ≤ ‖tangent P₁ Q₀ v‖ := by rw [← hQT]; exact hQ₀.norm_le _
  have h2 : ‖P₁ v‖ ≤ ‖tangent P₁ Q₀ v‖ := by rw [← hPT]; exact hP₁.norm_le _
  exact ⟨h1, h2, (hP₁.norm_le _).trans h1, (hP₁.norm_sub_le _).trans h1⟩

/-- **Robust loss descent of the explicit Euler PSI training step** (the training algorithm of
arXiv 2502.03006, Sec. 3.2).  Let `ℒ` be `β`-smooth, let
`P₁, Q₀` be commuting orthogonal projectors (new left basis, old right basis),
and let the new basis capture the K-step result.  Then, with `T₁ = P₁ + Q₀ - P₁ Q₀`,

`ℒ(y) ≤ ℒ(x) - h (1 - βh(2 + βh) - (βh/2)(1 + βh)⁴) ‖T₁ ∇ℒ(x)‖²`.

The constants are absolute: the anti-dissipative S-step undoes only the core part of the K-step,
and every remainder is bounded by `‖Q₀ ∇ℒ‖, ‖P₁ ∇ℒ‖ ≤ ‖T₁ ∇ℒ‖`.  No singular value of the
iterate enters, so descent is robust.  Compare the bound `-h α_K² + h α_S² - h α_L²` of
arXiv 2502.03006, Lemma 5.1, which cannot be signed. -/
theorem loss_kslEulerStep_le_of_smooth (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (hβ : 0 ≤ β) (hh : 0 ≤ h) {x : E}
    (hcap : P₁ (x - h • Q₀ (g x)) = x - h • Q₀ (g x)) :
    ℒ (kslEulerStep P₁ Q₀ (fun y => -g y) h x) ≤
      ℒ x - h * (1 - β * h * (2 + β * h) - β * h / 2 * (1 + β * h) ^ 4) *
        ‖tangent P₁ Q₀ (g x)‖ ^ 2 := by
  set y := kslEulerStep P₁ Q₀ (fun y => -g y) h x with hy
  set k := x - h • Q₀ (g x) with hk
  set s := k + h • P₁ (Q₀ (g k)) with hs
  set d₁ := g k - g x with hd₁
  set d₂ := g s - g x with hd₂
  set r := P₁ (Q₀ d₁) - P₁ d₂ with hr
  set t := ‖tangent P₁ Q₀ (g x)‖ with ht
  set a := ‖Q₀ (g x)‖ with ha
  have hT := hP₁.tangent hQ₀ hc
  obtain ⟨hat, hbt, hpqt, hnt⟩ := norm_components_le_tangent hP₁ hQ₀ hc (g x)
  have hdisp : y - x = -(h • tangent P₁ Q₀ (g x)) + h • r :=
    kslEulerStep_neg_sub g h hcap
  have ht0 : 0 ≤ t := norm_nonneg _
  -- remainders
  have hd₁n : ‖d₁‖ ≤ β * h * a := by
    have := hg k x
    rwa [hk, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hh, ← mul_assoc]
      at this
  have hsx : ‖s - x‖ ≤ h * a + h * (β * h * a) := by
    have heq : s - x = -(h • (Q₀ (g x) - P₁ (Q₀ (g x)))) + h • P₁ (Q₀ d₁) := by
      simp only [hs, hk, hd₁, map_sub, smul_sub]
      abel
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_smul, norm_smul, Real.norm_of_nonneg hh]
    have h1 : ‖Q₀ (g x) - P₁ (Q₀ (g x))‖ ≤ a := hP₁.norm_sub_le _
    have h2 : ‖P₁ (Q₀ d₁)‖ ≤ β * h * a := ((hP₁.norm_le _).trans (hQ₀.norm_le _)).trans hd₁n
    nlinarith
  have hd₂n : ‖d₂‖ ≤ β * (h * a + h * (β * h * a)) :=
    (hg s x).trans (mul_le_mul_of_nonneg_left hsx hβ)
  have hrn : ‖r‖ ≤ β * h * a * (2 + β * h) := by
    rw [hr]
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖P₁ (Q₀ d₁)‖ ≤ β * h * a := ((hP₁.norm_le _).trans (hQ₀.norm_le _)).trans hd₁n
    have h2 : ‖P₁ d₂‖ ≤ β * (h * a + h * (β * h * a)) := (hP₁.norm_le _).trans hd₂n
    nlinarith
  -- first-order term
  have hinT : ⟪g x, tangent P₁ Q₀ (g x)⟫ = t ^ 2 := by
    rw [real_inner_comm, hT.inner_self_apply]
  have hinr : ⟪g x, r⟫ ≤ β * h * a * (a + ‖P₁ (g x)‖ * (1 + β * h)) := by
    have e1 : ⟪g x, P₁ (Q₀ d₁)⟫ = ⟪P₁ (Q₀ (g x)), d₁⟫ := by
      rw [← hP₁.symm, ← hQ₀.symm, hc]
    have e2 : ⟪g x, P₁ d₂⟫ = ⟪P₁ (g x), d₂⟫ := by rw [← hP₁.symm]
    have i1 : ⟪P₁ (Q₀ (g x)), d₁⟫ ≤ ‖P₁ (Q₀ (g x))‖ * ‖d₁‖ := real_inner_le_norm _ _
    have i2 : -⟪P₁ (g x), d₂⟫ ≤ ‖P₁ (g x)‖ * ‖d₂‖ := by
      rw [← inner_neg_right]
      exact (real_inner_le_norm _ _).trans (by rw [norm_neg])
    have hpq : ‖P₁ (Q₀ (g x))‖ ≤ a := hP₁.norm_le _
    rw [hr, inner_sub_right, e1, e2]
    have ha0 : 0 ≤ a := norm_nonneg _
    have hb0 : 0 ≤ ‖P₁ (g x)‖ := norm_nonneg _
    nlinarith [mul_le_mul hpq hd₁n (norm_nonneg _) ha0,
      mul_le_mul_of_nonneg_left hd₂n hb0]
  -- the descent lemma
  have hdl := descent_lemma hℒ hg x y
  rw [hdisp, inner_add_right, inner_neg_right, inner_smul_right, inner_smul_right, hinT] at hdl
  have hnorm : ‖-(h • tangent P₁ Q₀ (g x)) + h • r‖ ≤ h * t * (1 + β * h) ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_smul, norm_smul, Real.norm_of_nonneg hh]
    have : h * ‖r‖ ≤ h * (β * h * t * (2 + β * h)) := by
      refine mul_le_mul_of_nonneg_left (hrn.trans ?_) hh
      have := mul_le_mul_of_nonneg_right hat (show 0 ≤ β * h * (2 + β * h) by positivity)
      nlinarith [mul_nonneg hβ hh]
    nlinarith
  have hsq : ‖-(h • tangent P₁ Q₀ (g x)) + h • r‖ ^ 2 ≤ (h * t * (1 + β * h) ^ 2) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hinr' : h * ⟪g x, r⟫ ≤ h * (β * h * t * (2 + β * h) * t) := by
    refine mul_le_mul_of_nonneg_left (hinr.trans ?_) hh
    have hb0 : 0 ≤ ‖P₁ (g x)‖ := norm_nonneg _
    have ha0 : 0 ≤ a := norm_nonneg _
    have hβh : 0 ≤ β * h := mul_nonneg hβ hh
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul hat hat ha0 ht0) hβh,
      mul_le_mul_of_nonneg_left (mul_le_mul hat hbt hb0 ht0) hβh,
      mul_le_mul_of_nonneg_left (mul_le_mul hat hbt hb0 ht0) (mul_nonneg hβh hβh)]
  have hβh : 0 ≤ β * h := mul_nonneg hβ hh
  nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ β / 2 by positivity)]

/-- **Descent of the PSI training step for `βh ≤ 1/4`**: `ℒ(y) ≤ ℒ(x) - (h/8)‖T₁ ∇ℒ(x)‖²`.
The step-size condition involves only the smoothness constant, not the singular values of the
iterate: PSI descends robustly, with a window at least one eighth of that of projected
gradient descent (`loss_projGradStep_le_self`). -/
theorem loss_kslEulerStep_le_of_smooth_quarter (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (hβ : 0 ≤ β) (hh : 0 ≤ h) (hβh : β * h ≤ 1 / 4) {x : E}
    (hcap : P₁ (x - h • Q₀ (g x)) = x - h • Q₀ (g x)) :
    ℒ (kslEulerStep P₁ Q₀ (fun y => -g y) h x) ≤ ℒ x - h / 8 * ‖tangent P₁ Q₀ (g x)‖ ^ 2 := by
  have h0 := loss_kslEulerStep_le_of_smooth hℒ hg hP₁ hQ₀ hc hβ hh hcap
  set X := β * h with hX
  have hX0 : 0 ≤ X := mul_nonneg hβ hh
  have hX2 : X ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ hX0 hβh 2
  have hX3 : X ^ 3 ≤ (1 / 4) ^ 3 := pow_le_pow_left₀ hX0 hβh 3
  have hX4 : X ^ 4 ≤ (1 / 4) ^ 4 := pow_le_pow_left₀ hX0 hβh 4
  have hX5 : X ^ 5 ≤ (1 / 4) ^ 5 := pow_le_pow_left₀ hX0 hβh 5
  have hpoly : 1 / 8 ≤ 1 - X * (2 + X) - X / 2 * (1 + X) ^ 4 := by nlinarith
  have hT0 : 0 ≤ ‖tangent P₁ Q₀ (g x)‖ ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hpoly (mul_nonneg hh hT0)]

/-- **Convergence of PSI training to tangent stationarity**.  Along an
iteration `x_{k+1} = kslEulerStep (P k) (Q k) (-∇ℒ) h x_k` with commuting orthogonal
projectors, QR capture at every step, `βh ≤ 1/4` and a lower bound `ℒinf`,
`min_{k<n} ‖T_k ∇ℒ(x_k)‖² ≤ 8 (ℒ(x₀) - ℒinf) / (n h)`, where `T_k = P_k + Q_k - P_k Q_k`.  In
particular `‖∇ℒ(x_k) V_k‖` and `‖U_{k+1}ᵀ ∇ℒ(x_k)‖` (both `≤ ‖T_k ∇ℒ(x_k)‖`,
`norm_components_le_tangent`) tend to zero along a subsequence, with a rate that does not involve
the singular values of the iterates. -/
theorem exists_tangentGrad_sq_le_of_psi (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {P Q : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k))
    (hQ : ∀ k, IsOrthProj (Q k)) (hc : ∀ k x, P k (Q k x) = Q k (P k x)) {x : ℕ → E}
    {ℒinf : ℝ} (hβ : 0 ≤ β) (hh : 0 < h) (hβh : β * h ≤ 1 / 4)
    (hcap : ∀ k, P k (x k - h • Q k (g (x k))) = x k - h • Q k (g (x k)))
    (hstep : ∀ k, x (k + 1) = kslEulerStep (P k) (Q k) (fun y => -g y) h (x k))
    (hinf : ∀ k, ℒinf ≤ ℒ (x k)) {n : ℕ} (hn : 0 < n) :
    ∃ k < n, ‖tangent (P k) (Q k) (g (x k))‖ ^ 2 ≤ 8 * (ℒ (x 0) - ℒinf) / (n * h) := by
  have hc8 : 0 < h / 8 := by positivity
  obtain ⟨k, hk, hle⟩ := exists_le_of_mul_sum_le (a := fun k => ‖tangent (P k) (Q k) (g (x k))‖ ^ 2)
    (A := ℒ (x 0) - ℒinf) (e := 0) hc8 hn (by
      have hs := sum_le_of_le_sub_add (u := fun k => ℒ (x k))
        (a := fun k => h / 8 * ‖tangent (P k) (Q k) (g (x k))‖ ^ 2) (e := fun _ => 0)
        (fun k => by
          have := loss_kslEulerStep_le_of_smooth_quarter hℒ hg (hP k) (hQ k) (hc k) hβ hh.le hβh
            (hcap k)
          rw [← hstep k] at this
          simp only [add_zero]
          linarith) n
      rw [sum_const_zero, add_zero, ← mul_sum] at hs
      have := hinf n
      simp only [mul_zero, add_zero]
      linarith)
  refine ⟨k, hk, hle.trans (le_of_eq ?_)⟩
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  field_simp
  ring

end Abstract

/-! ### The Frobenius quadratic: exact identity and the golden-ratio threshold -/

section Quadratic

variable {P₁ Q₀ : E →L[ℝ] E} {h : ℝ}

/-- For the quadratic `ℒ(x) = ½‖x - a‖²` (gradient `x - a`), the PSI step is the affine map
`y - a = E - h T₁ E - h²(1 - h) P₁ Q₀ E`, `E = x - a`. -/
lemma kslEulerStep_quadratic_sub (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀) (a : E) {x : E}
    (hcap : P₁ (x - h • Q₀ (x - a)) = x - h • Q₀ (x - a)) :
    kslEulerStep P₁ Q₀ (fun y => -(y - a)) h x - a =
      (x - a) - h • tangent P₁ Q₀ (x - a) - (h ^ 2 * (1 - h)) • P₁ (Q₀ (x - a)) := by
  rw [kslEulerStep_neg_eq (fun y => y - a) h hcap]
  simp only [tangent_apply, map_sub, map_add, map_smul, smul_sub, smul_add, smul_smul,
    hQ₀.idem, hP₁.idem]
  module

/-- `P₁ Q₀` is absorbed by the tangent projector: `T₁ (P₁ Q₀ v) = P₁ Q₀ v`. -/
lemma tangent_apply_mul (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (v : E) :
    tangent P₁ Q₀ (P₁ (Q₀ v)) = P₁ (Q₀ v) := by
  simp only [tangent_apply, hP₁.idem, ← hc, hQ₀.idem]
  abel

/-- **Exact loss identity of the PSI step on the Frobenius quadratic**.  For
`ℒ(x) = ½‖x - a‖²`, `E = x - a`, `T₁ = P₁ + Q₀ - P₁ Q₀`:

`‖y - a‖² - ‖x - a‖² = -h(2 - h)‖T₁ E‖² - h²(1 - h)²(2 - h²)‖P₁ Q₀ E‖²`.

The first term is the gain of a projected gradient step with projector `T₁`; the second is the
net effect of the backward S-step on the core, negative for `h ≤ √2`.  The basis rotation
`U₀ → U₁` (which carries the factor `1/σ_r`) enters only through `T₁` and does not produce a
term of indefinite sign: no singular value of the state enters the identity. -/
theorem kslEulerStep_frobenius_sq_identity (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (a : E) {x : E}
    (hcap : P₁ (x - h • Q₀ (x - a)) = x - h • Q₀ (x - a)) :
    ‖kslEulerStep P₁ Q₀ (fun y => -(y - a)) h x - a‖ ^ 2 - ‖x - a‖ ^ 2 =
      -(h * (2 - h)) * ‖tangent P₁ Q₀ (x - a)‖ ^ 2 -
        h ^ 2 * (1 - h) ^ 2 * (2 - h ^ 2) * ‖P₁ (Q₀ (x - a))‖ ^ 2 := by
  rw [kslEulerStep_quadratic_sub hP₁ hQ₀ a hcap]
  set e := x - a
  set T := tangent P₁ Q₀ with hT
  have hTo := hP₁.tangent hQ₀ hc
  have hM : IsOrthProj (P₁ * Q₀) := hP₁.mul hQ₀ hc
  have hMa : (P₁ * Q₀) e = P₁ (Q₀ e) := rfl
  have i1 : ⟪e, T e⟫ = ‖T e‖ ^ 2 := by rw [real_inner_comm, hTo.inner_self_apply]
  have i2 : ⟪e, P₁ (Q₀ e)⟫ = ‖P₁ (Q₀ e)‖ ^ 2 := by
    rw [← hMa, real_inner_comm, hM.inner_self_apply]
  have i3 : ⟪T e, P₁ (Q₀ e)⟫ = ‖P₁ (Q₀ e)‖ ^ 2 := by
    rw [hTo.symm, tangent_apply_mul hP₁ hQ₀ hc, i2]
  rw [sub_sub, norm_sub_sq_real, norm_add_sq_real, inner_add_right, norm_smul, norm_smul,
    inner_smul_right, inner_smul_right, inner_smul_left, inner_smul_right, i1, i2, i3,
    Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  simp only [RCLike.conj_to_real]
  ring

/-- `‖P₁ Q₀ v‖ ≤ ‖T₁ v‖`. -/
lemma norm_mul_apply_le_tangent (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (v : E) :
    ‖P₁ (Q₀ v)‖ ≤ ‖tangent P₁ Q₀ v‖ :=
  (norm_components_le_tangent hP₁ hQ₀ hc v).2.2.1

/-- **Descent of the PSI step on the Frobenius quadratic up to the golden ratio**. For `ℒ(x) = ½‖x -
a‖²` and every `0 ≤ h ≤ φ = (1 + √5)/2`,

`ℒ(y) ≤ ℒ(x) - (h/2)(1 + h - h²) ‖T₁ ∇ℒ(x)‖²`.

The factor `1 + h - h²` vanishes exactly at `h = φ`.  For comparison, a projected gradient step
with the same projector gains `(h/2)(2 - h)‖T₁ ∇ℒ‖²` for `h ≤ 2` (`loss_projGradStep_le`);
since `2 - h ≥ 1 + h - h²`, the guaranteed PSI gain is never larger, with equality only at
`h = 1`.
Descent is unconditional in the singular values of the iterate. -/
theorem loss_kslEulerStep_quadratic_le (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (hh : 0 ≤ h) (hφ : h ≤ Real.goldenRatio) (a : E)
    {x : E} (hcap : P₁ (x - h • Q₀ (x - a)) = x - h • Q₀ (x - a)) :
    1 / 2 * ‖kslEulerStep P₁ Q₀ (fun y => -(y - a)) h x - a‖ ^ 2 ≤
      1 / 2 * ‖x - a‖ ^ 2 - h / 2 * (1 + h - h ^ 2) * ‖tangent P₁ Q₀ (x - a)‖ ^ 2 := by
  have hid := kslEulerStep_frobenius_sq_identity hP₁ hQ₀ hc a hcap
  set t := ‖tangent P₁ Q₀ (x - a)‖ ^ 2 with ht
  set p := ‖P₁ (Q₀ (x - a))‖ ^ 2 with hp
  have hpt : p ≤ t := pow_le_pow_left₀ (norm_nonneg _) (norm_mul_apply_le_tangent hP₁ hQ₀ hc _) 2
  have hp0 : 0 ≤ p := sq_nonneg _
  have ht0 : 0 ≤ t := sq_nonneg _
  -- `t + h (2 - h²) p ≥ 0` for `0 ≤ h ≤ φ`
  have hφ2 : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  have hφ1 : 1 < Real.goldenRatio := Real.one_lt_goldenRatio
  have hcube : 0 ≤ 1 + 2 * h - h ^ 3 := by
    have h1 : 0 ≤ Real.goldenRatio - h := by linarith
    have h2 : 0 ≤ h ^ 2 + Real.goldenRatio * h + Real.goldenRatio - 1 := by nlinarith
    have : 1 + 2 * h - h ^ 3 =
        (Real.goldenRatio - h) * (h ^ 2 + Real.goldenRatio * h + Real.goldenRatio - 1) -
          (1 + h) * (Real.goldenRatio ^ 2 - Real.goldenRatio - 1) := by ring
    rw [this, hφ2]
    nlinarith [mul_nonneg h1 h2]
  have hkey : 0 ≤ t + h * (2 - h ^ 2) * p := by
    rcases le_or_gt 0 (2 - h ^ 2) with h2 | h2
    · positivity
    · have : h * (2 - h ^ 2) * t ≤ h * (2 - h ^ 2) * p :=
        mul_le_mul_of_nonpos_left hpt (mul_nonpos_of_nonneg_of_nonpos hh h2.le)
      nlinarith [mul_nonneg ht0 hcube]
  have hsq : 0 ≤ h * (1 - h) ^ 2 := by positivity
  nlinarith [mul_nonneg hsq hkey]

/-- **Sharpness of the golden-ratio threshold** (the mode is that of
`kslEulerStep_smul`).  For `ℒ(x) = ½‖x‖²` and a nonzero state `x` in both bases
(`P₁ x = x`, `Q₀ x = x`; the capture condition of the PSI step then holds automatically),
the PSI step with any `h > φ` *increases* the loss, `ℒ(y) = ((1 - h)²(1 + h))² ℒ(x) > ℒ(x)`,
while for `h < 2` the full gradient step `x - h ∇ℒ(x)` still decreases it.  Together with
`loss_kslEulerStep_quadratic_le`, PSI descends on Frobenius quadratics exactly for
`h ≤ φ ≈ 1.618`, against `h ≤ 2` for (projected) gradient descent. -/
theorem loss_kslEulerStep_gt_of_goldenRatio_lt {x : E} (hx0 : x ≠ 0) (h₁ : P₁ x = x)
    (h₀ : Q₀ x = x) (hφ : Real.goldenRatio < h) :
    1 / 2 * ‖x‖ ^ 2 < 1 / 2 * ‖kslEulerStep P₁ Q₀ (fun y => -(y - 0)) h x‖ ^ 2 ∧
      (h < 2 → 1 / 2 * ‖x - h • (x - 0)‖ ^ 2 < 1 / 2 * ‖x‖ ^ 2) := by
  have hfun : (fun y : E => -(y - 0)) = fun y => -(1 : ℝ) • y := by
    funext y; simp
  obtain ⟨hE, hK⟩ := kslEulerStep_smul (P₁ := P₁) (Q₀ := Q₀) (1 : ℝ) h h₁ h₀
  have hh : 0 ≤ h := by linarith [Real.goldenRatio_pos]
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hamp : 1 < (1 - h * 1) ^ 2 * (1 + h * 1) := by
    have := (ksl_scalar_amplification_le_one_iff hh).not
    rw [not_le, not_le] at this
    have hφ' : (1 + √5) / 2 < h := by
      have : Real.goldenRatio = (1 + √5) / 2 := rfl
      rw [← this]; exact hφ
    simpa using this.2 hφ'
  refine ⟨?_, fun h2 => ?_⟩
  · rw [hfun, hK, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have : 1 < ((1 - h * 1) ^ 2 * (1 + h * 1)) ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_right this (pow_pos hxn 2)]
  · have : x - h • (x - 0) = (1 - h) • x := by rw [sub_zero, sub_smul, one_smul]
    rw [this, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have h1 : (1 - h) ^ 2 < 1 := by nlinarith [Real.one_lt_goldenRatio]
    nlinarith [mul_lt_mul_of_pos_right h1 (pow_pos hxn 2)]

end Quadratic

/-! ### The backward-corrected PSI step -/

section BackwardCorrected

variable {P₁ Q₀ : E →L[ℝ] E} {ℒ : E → ℝ} {g : E → E} {β h : ℝ}

/-- The backward-corrected PSI step of arXiv 2502.03006, Sec. 3.3, in full-space form: the
K-step only serves to build the new basis `P₁`; the S-step is replaced by the projection
`x ↦ P₁ x` of the old iterate onto the new basis (`S̄₁ = U₁ᵀ U₀ S₀`); then the L-step
`w ↦ w - h P₁ ∇ℒ(w)`. -/
def bcPsiStep (P₁ : E →L[ℝ] E) (g : E → E) (h : ℝ) (x : E) : E := P₁ x - h • P₁ (g (P₁ x))

lemma bcPsiStep_eq_projGradStep (P₁ : E →L[ℝ] E) (g : E → E) (h : ℝ) (x : E) :
    bcPsiStep P₁ g h x = projGradStep P₁ g h (P₁ x) := rfl

/-- The projection onto the new basis moves the iterate by `-h (1 - P₁) Q₀ ∇ℒ(x)`, a descent
direction: `P₁ x - x = -h (Q₀ g(x) - P₁ Q₀ g(x))` when `P₁` captures the K-step result. -/
lemma proj_sub_self_of_capture (g : E → E) (h : ℝ) {x : E}
    (hcap : P₁ (x - h • Q₀ (g x)) = x - h • Q₀ (g x)) :
    P₁ x - x = -(h • (Q₀ (g x) - P₁ (Q₀ (g x)))) := by
  have hcap' : P₁ x - h • P₁ (Q₀ (g x)) = x - h • Q₀ (g x) := by
    simpa only [map_sub, map_smul] using hcap
  have e : P₁ x - x = (P₁ x - h • P₁ (Q₀ (g x))) - (x - h • Q₀ (g x)) -
      (h • Q₀ (g x) - h • P₁ (Q₀ (g x))) := by abel
  rw [e, hcap', sub_self, zero_sub, smul_sub]

/-- **Loss descent of the backward-corrected PSI step**.  arXiv 2502.03006,
Lemma 5.4, bounds the loss by `ℓ(Y₀) + B‖(I - U₁U₁ᵀ)Y₀‖ + (c_ℓ/2)‖(I - U₁U₁ᵀ)Y₀‖² - hα_L²` and
leaves descent open because of the positive term.  In fact `(I - U₁U₁ᵀ)Y₀ = h (1 - P₁) Q₀ ∇ℓ(Y₀)`
is a descent direction, and for every `β`-smooth loss

`ℒ(Y₁) ≤ ℒ(Y₀) - h(1 - βh/2) (‖(1 - P₁) Q₀ ∇ℒ(Y₀)‖² + ‖P₁ ∇ℒ(P₁ Y₀)‖²)`:

the same step-size window `βh ≤ 2` as projected gradient descent, with constants independent of
the singular values. -/
theorem loss_bcPsiStep_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (h : ℝ) {x : E}
    (hcap : P₁ (x - h • Q₀ (g x)) = x - h • Q₀ (g x)) :
    ℒ (bcPsiStep P₁ g h x) ≤
      ℒ x - h * (1 - β * h / 2) *
        (‖Q₀ (g x) - P₁ (Q₀ (g x))‖ ^ 2 + ‖P₁ (g (P₁ x))‖ ^ 2) := by
  have h1 := loss_projGradStep_le hℒ hg hP₁ h (P₁ x)
  rw [← bcPsiStep_eq_projGradStep] at h1
  have hR : IsOrthProj ((1 - P₁) * Q₀) :=
    hP₁.compl.mul hQ₀ fun v => by
      change Q₀ v - P₁ (Q₀ v) = Q₀ (v - P₁ v)
      rw [map_sub, hc]
  have hRa : ((1 - P₁) * Q₀) (g x) = Q₀ (g x) - P₁ (Q₀ (g x)) := rfl
  have h2 := descent_lemma hℒ hg x (P₁ x)
  rw [proj_sub_self_of_capture g h hcap, inner_neg_right, inner_smul_right, ← hRa,
    real_inner_comm, hR.inner_self_apply, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, hRa] at h2
  nlinarith

end BackwardCorrected

/-! ### The factored training steps on `U S Vᵀ` -/

section MatrixStep

open scoped LeanDLRA.Frobenius

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]

/-- The projector-splitting training step on the factors (arXiv 2502.03006, Sec. 3.2, one
explicit Euler step per substep, as in Algorithm 1): `K₁ = U₀S₀ - h ∇ℒ(W₀) V₀`, new basis `U₁`
(from a QR factorisation of `K₁`, encoded by the hypothesis `U₁ U₁ᵀ K₁ = K₁`), `S̃ = U₁ᵀ K₁`,
backward S-step `S̃₀ = S̃ + h U₁ᵀ ∇ℒ(U₁ S̃ V₀ᵀ) V₀`, L-step
`L₁ = V₀ S̃₀ᵀ - h ∇ℒ(U₁ S̃₀ V₀ᵀ)ᵀ U₁`, output `W₁ = U₁ L₁ᵀ` (which equals `U₁ S₁ V₁ᵀ` for any
orthonormal `V₁` spanning `L₁`). -/
noncomputable def psiTrainStep (g : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ) (U₀ : Matrix m r ℝ)
    (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) (U₁ : Matrix m r ℝ) : Matrix m n ℝ :=
  let K₁ := U₀ * S₀ - h • (g (U₀ * S₀ * V₀ᵀ) * V₀)
  let S' := U₁ᵀ * K₁
  let S'' := S' + h • (U₁ᵀ * g (U₁ * S' * V₀ᵀ) * V₀)
  let L₁ := V₀ * S''ᵀ - h • ((g (U₁ * S'' * V₀ᵀ))ᵀ * U₁)
  U₁ * L₁ᵀ

/-- The backward-corrected PSI training step on the factors (arXiv 2502.03006, Sec. 3.3):
`S̄₁ = U₁ᵀ U₀ S₀`, `L₁ = V₀ S̄₁ᵀ - h ∇ℒ(U₁ S̄₁ V₀ᵀ)ᵀ U₁`, `W₁ = U₁ L₁ᵀ`. -/
noncomputable def bcPsiTrainStep (g : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ) (U₀ : Matrix m r ℝ)
    (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) (U₁ : Matrix m r ℝ) : Matrix m n ℝ :=
  let S' := U₁ᵀ * (U₀ * S₀)
  let L₁ := V₀ * S'ᵀ - h • ((g (U₁ * S' * V₀ᵀ))ᵀ * U₁)
  U₁ * L₁ᵀ

/-- The K-step result in full-space form is `K₁ V₀ᵀ`. -/
lemma kStep_eq (g : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ) (U₀ : Matrix m r ℝ)
    (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) :
    U₀ * S₀ * V₀ᵀ - h • rightProj V₀ (g (U₀ * S₀ * V₀ᵀ)) =
      (U₀ * S₀ - h • (g (U₀ * S₀ * V₀ᵀ) * V₀)) * V₀ᵀ := by
  simp only [rightProj_apply, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc]

/-- The QR capture `U₁ U₁ᵀ K₁ = K₁` gives the abstract capture hypothesis. -/
lemma capture_of_mul (g : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ) {U₀ : Matrix m r ℝ}
    {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ} {U₁ : Matrix m r ℝ}
    (hcap : U₁ * U₁ᵀ * (U₀ * S₀ - h • (g (U₀ * S₀ * V₀ᵀ) * V₀)) =
      U₀ * S₀ - h • (g (U₀ * S₀ * V₀ᵀ) * V₀)) :
    leftProj U₁ (U₀ * S₀ * V₀ᵀ - h • rightProj V₀ (g (U₀ * S₀ * V₀ᵀ))) =
      U₀ * S₀ * V₀ᵀ - h • rightProj V₀ (g (U₀ * S₀ * V₀ᵀ)) := by
  rw [kStep_eq, leftProj_apply, ← Matrix.mul_assoc, hcap]

/-- **The factored PSI training step is the abstract PSI step** with `P₁ = U₁U₁ᵀ`,
`Q₀ = V₀V₀ᵀ` and the field `-∇ℒ`, under the QR capture `U₁ U₁ᵀ K₁ = K₁`. -/
theorem psiTrainStep_eq_kslEulerStep (g : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ)
    {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ} {U₁ : Matrix m r ℝ}
    (hcap : U₁ * U₁ᵀ * (U₀ * S₀ - h • (g (U₀ * S₀ * V₀ᵀ) * V₀)) =
      U₀ * S₀ - h • (g (U₀ * S₀ * V₀ᵀ) * V₀)) :
    psiTrainStep g h U₀ S₀ V₀ U₁ =
      kslEulerStep (leftProj U₁) (rightProj V₀) (fun y => -g y) h (U₀ * S₀ * V₀ᵀ) := by
  rw [kslEulerStep_neg_eq g h (capture_of_mul g h hcap), kStep_eq]
  simp only [psiTrainStep]
  obtain ⟨K₁, hK₁⟩ : ∃ K₁, K₁ = U₀ * S₀ - h • (g (U₀ * S₀ * V₀ᵀ) * V₀) := ⟨_, rfl⟩
  rw [← hK₁] at hcap ⊢
  have hk : U₁ * (U₁ᵀ * (K₁ * V₀ᵀ)) = K₁ * V₀ᵀ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hcap]
  simp only [leftProj_apply, rightProj_apply, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hk]

/-- **The factored bc-PSI training step is the abstract step `bcPsiStep`** with `P₁ = U₁U₁ᵀ`;
no hypothesis on the factors is needed. -/
theorem bcPsiTrainStep_eq (g : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ) (U₀ : Matrix m r ℝ)
    (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) (U₁ : Matrix m r ℝ) :
    bcPsiTrainStep g h U₀ S₀ V₀ U₁ = bcPsiStep (leftProj U₁) g h (U₀ * S₀ * V₀ᵀ) := by
  simp only [bcPsiTrainStep, bcPsiStep, leftProj_apply, Matrix.transpose_sub,
    Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_sub,
    Matrix.mul_smul, Matrix.mul_assoc]

/-- **Robust descent of the factored PSI training step**: for a `β`-smooth loss
on `ℝ^{m×n}`, orthonormal `U₁`, `V₀`, the QR capture `U₁U₁ᵀK₁ = K₁` and `βh ≤ 1/4`,
`ℒ(W₁) ≤ ℒ(W₀) - (h/8) ‖P_{U₁,V₀} ∇ℒ(W₀)‖²` with the tangent projector
`P_{U₁,V₀} Z = U₁U₁ᵀ Z + Z V₀V₀ᵀ - U₁U₁ᵀ Z V₀V₀ᵀ`.  Nothing depends on `S₀`. -/
theorem loss_psiTrainStep_le [DecidableEq r] {ℒ : Matrix m n ℝ → ℝ}
    {g : Matrix m n ℝ → Matrix m n ℝ} {β h : ℝ} (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hh : 0 ≤ h) (hβh : β * h ≤ 1 / 4)
    {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ}
    {V₀ : Matrix n r ℝ} {U₁ : Matrix m r ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    (hcap : U₁ * U₁ᵀ * (U₀ * S₀ - h • (g (U₀ * S₀ * V₀ᵀ) * V₀)) =
      U₀ * S₀ - h • (g (U₀ * S₀ * V₀ᵀ) * V₀)) :
    ℒ (psiTrainStep g h U₀ S₀ V₀ U₁) ≤
      ℒ (U₀ * S₀ * V₀ᵀ) - h / 8 * ‖tangentProj U₁ V₀ (g (U₀ * S₀ * V₀ᵀ))‖ ^ 2 := by
  rw [psiTrainStep_eq_kslEulerStep g h hcap]
  exact loss_kslEulerStep_le_of_smooth_quarter hℒ hg (isOrthProj_leftProj hU₁)
    (isOrthProj_rightProj hV₀) (leftProj_rightProj_comm U₁ V₀) hβ hh hβh
    (capture_of_mul g h hcap)

/-- **Descent of the factored bc-PSI training step**: for a `β`-smooth loss,
orthonormal `U₁`, `V₀` and the QR capture, for every `h`,
`ℒ(W₁) ≤ ℒ(W₀) - h(1 - βh/2)(‖(1 - U₁U₁ᵀ)∇ℒ(W₀)V₀V₀ᵀ‖² + ‖U₁U₁ᵀ∇ℒ(U₁U₁ᵀW₀)‖²)`. -/
theorem loss_bcPsiTrainStep_le [DecidableEq r] {ℒ : Matrix m n ℝ → ℝ}
    {g : Matrix m n ℝ → Matrix m n ℝ} {β h : ℝ} (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ}
    {V₀ : Matrix n r ℝ} {U₁ : Matrix m r ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    (hcap : U₁ * U₁ᵀ * (U₀ * S₀ - h • (g (U₀ * S₀ * V₀ᵀ) * V₀)) =
      U₀ * S₀ - h • (g (U₀ * S₀ * V₀ᵀ) * V₀)) :
    ℒ (bcPsiTrainStep g h U₀ S₀ V₀ U₁) ≤
      ℒ (U₀ * S₀ * V₀ᵀ) - h * (1 - β * h / 2) *
        (‖rightProj V₀ (g (U₀ * S₀ * V₀ᵀ)) -
            leftProj U₁ (rightProj V₀ (g (U₀ * S₀ * V₀ᵀ)))‖ ^ 2 +
          ‖leftProj U₁ (g (leftProj U₁ (U₀ * S₀ * V₀ᵀ)))‖ ^ 2) := by
  rw [bcPsiTrainStep_eq]
  exact loss_bcPsiStep_le hℒ hg (isOrthProj_leftProj hU₁) (isOrthProj_rightProj hV₀)
    (leftProj_rightProj_comm U₁ V₀) h (capture_of_mul g h hcap)

end MatrixStep

end LeanDLRA.Novel.OpSB64
