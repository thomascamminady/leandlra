import LeanDLRA.Training.Descent
import LeanDLRA.Matrix.Projectors
import LeanDLRA.LinearAlgebra.Factorization.Defs

/-!
# Stochastic descent of DLRT: same-minibatch augmentation (draft)
-/

open Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

namespace StochasticDescent

/-! ### Weighted averages of projected stochastic gradients -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Ξ : Type*} [Fintype Ξ]

/-- The weighted deviations from the mean sum to zero. -/
lemma sum_smul_sub_eq_zero {p : Ξ → ℝ} (hp1 : ∑ ξ, p ξ = 1) {gs : Ξ → E} {g₀ : E}
    (hmean : ∑ ξ, p ξ • gs ξ = g₀) : ∑ ξ, p ξ • (gs ξ - g₀) = 0 := by
  simp only [smul_sub, sum_sub_distrib, hmean, ← sum_smul, hp1, one_smul, sub_self]

/-- Unbiasedness survives a fixed linear map: `∑ p_ξ ⟪v, P g_ξ⟫ = ⟪v, P g⟫`. -/
lemma sum_inner_apply_eq {p : Ξ → ℝ} {gs : Ξ → E} {g₀ : E}
    (hmean : ∑ ξ, p ξ • gs ξ = g₀) (P : E →L[ℝ] E) (v : E) :
    ∑ ξ, p ξ * ⟪v, P (gs ξ)⟫ = ⟪v, P g₀⟫ := by
  rw [← hmean, map_sum, inner_sum]
  simp [map_smul, inner_smul_right]

/-- **Bias–variance decomposition** of the projected stochastic gradient:
`∑ p_ξ ‖P g_ξ‖² = ‖P g‖² + ∑ p_ξ ‖P (g_ξ - g)‖²` for a fixed linear map `P`. -/
lemma sum_norm_sq_apply_eq {p : Ξ → ℝ} (hp1 : ∑ ξ, p ξ = 1) {gs : Ξ → E} {g₀ : E}
    (hmean : ∑ ξ, p ξ • gs ξ = g₀) (P : E →L[ℝ] E) :
    ∑ ξ, p ξ * ‖P (gs ξ)‖ ^ 2 = ‖P g₀‖ ^ 2 + ∑ ξ, p ξ * ‖P (gs ξ - g₀)‖ ^ 2 := by
  have hexp : ∀ ξ, p ξ * ‖P (gs ξ)‖ ^ 2 =
      p ξ * ‖P g₀‖ ^ 2 + 2 * (p ξ * ⟪P g₀, P (gs ξ - g₀)⟫) + p ξ * ‖P (gs ξ - g₀)‖ ^ 2 := by
    intro ξ
    have h : P (gs ξ) = P g₀ + P (gs ξ - g₀) := by rw [← map_add, add_sub_cancel]
    rw [h, norm_add_sq_real]
    ring
  have hcross : ∑ ξ, p ξ * ⟪P g₀, P (gs ξ - g₀)⟫ = 0 := by
    rw [sum_inner_apply_eq (sum_smul_sub_eq_zero hp1 hmean) P (P g₀), map_zero, inner_zero_right]
  simp only [hexp, sum_add_distrib, ← sum_mul, hp1, one_mul, ← mul_sum, hcross, mul_zero,
    add_zero]

/-- **Projection reduces variance**: `∑ p_ξ ‖Π (g_ξ - g)‖² ≤ ∑ p_ξ ‖g_ξ - g‖²`. -/
lemma sum_norm_sq_apply_sub_le {P : E →L[ℝ] E} (hP : IsOrthProj P) {p : Ξ → ℝ}
    (hp : ∀ ξ, 0 ≤ p ξ) (gs : Ξ → E) (g₀ : E) :
    ∑ ξ, p ξ * ‖P (gs ξ - g₀)‖ ^ 2 ≤ ∑ ξ, p ξ * ‖gs ξ - g₀‖ ^ 2 :=
  sum_le_sum fun ξ _ => mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (hP.norm_le _) 2) (hp ξ)

variable {ℒ : E → ℝ} {g : E → E} {β : ℝ}

/-- The descent lemma along a step `x - h d`:
`ℒ(x - h d) ≤ ℒ(x) - h ⟪∇ℒ(x), d⟫ + β h² / 2 ‖d‖²`. -/
theorem loss_sub_smul_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (x d : E) (h : ℝ) :
    ℒ (x - h • d) ≤ ℒ x - h * ⟪g x, d⟫ + β * h ^ 2 / 2 * ‖d‖ ^ 2 := by
  have hd := descent_lemma hℒ hg x (x - h • d)
  rw [sub_sub_cancel_left, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs] at hd
  linarith

/-- The lower descent lemma along a step `x - h d`:
`ℒ(x) - h ⟪∇ℒ(x), d⟫ - β h² / 2 ‖d‖² ≤ ℒ(x - h d)`. -/
theorem le_loss_sub_smul (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (x d : E) (h : ℝ) :
    ℒ x - h * ⟪g x, d⟫ - β * h ^ 2 / 2 * ‖d‖ ^ 2 ≤ ℒ (x - h • d) := by
  have hd := descent_lemma_lower hℒ hg x (x - h • d)
  rw [sub_sub_cancel_left, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs] at hd
  linarith

/-- **Expected loss descent of projected SGD with a minibatch-independent projector.**
If the minibatch gradients `g_ξ` are unbiased at `x` (`∑ p_ξ g_ξ = ∇ℒ(x)`) and the orthogonal
projector `Π` does not depend on `ξ`, then
`∑ p_ξ ℒ(x - h Π g_ξ) ≤ ℒ(x) - h (1 - β h / 2) ‖Π ∇ℒ(x)‖² + β h² / 2 · ∑ p_ξ ‖Π (g_ξ - ∇ℒ(x))‖²`.
-/
theorem sum_loss_sub_smul_apply_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {P : E →L[ℝ] E} (hP : IsOrthProj P)
    {p : Ξ → ℝ} (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1) {gs : Ξ → E} {x : E}
    (hmean : ∑ ξ, p ξ • gs ξ = g x) (h : ℝ) :
    ∑ ξ, p ξ * ℒ (x - h • P (gs ξ)) ≤
      ℒ x - h * (1 - β * h / 2) * ‖P (g x)‖ ^ 2 +
        β * h ^ 2 / 2 * ∑ ξ, p ξ * ‖P (gs ξ - g x)‖ ^ 2 := by
  have hstep : ∀ ξ ∈ univ, p ξ * ℒ (x - h • P (gs ξ)) ≤
      p ξ * ℒ x - h * (p ξ * ⟪g x, P (gs ξ)⟫) + β * h ^ 2 / 2 * (p ξ * ‖P (gs ξ)‖ ^ 2) := by
    intro ξ _
    calc p ξ * ℒ (x - h • P (gs ξ))
        ≤ p ξ * (ℒ x - h * ⟪g x, P (gs ξ)⟫ + β * h ^ 2 / 2 * ‖P (gs ξ)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (loss_sub_smul_le hℒ hg x _ h) (hp ξ)
      _ = _ := by ring
  have hsum := sum_le_sum hstep
  rw [sum_add_distrib, sum_sub_distrib, ← sum_mul, hp1, one_mul, ← mul_sum, ← mul_sum,
    sum_inner_apply_eq hmean, sum_norm_sq_apply_eq hp1 hmean, real_inner_comm,
    hP.inner_self_apply] at hsum
  calc _ ≤ _ := hsum
    _ = _ := by ring

/-- Variance form of `sum_loss_sub_smul_apply_le`: with `σ² ≥ ∑ p_ξ ‖g_ξ - ∇ℒ(x)‖²`,
`∑ p_ξ ℒ(x - h Π g_ξ) ≤ ℒ(x) - h (1 - β h / 2) ‖Π ∇ℒ(x)‖² + β h² σ² / 2`. -/
theorem sum_loss_sub_smul_apply_le_variance (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {P : E →L[ℝ] E} (hP : IsOrthProj P)
    {p : Ξ → ℝ} (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1) {gs : Ξ → E} {x : E}
    (hmean : ∑ ξ, p ξ • gs ξ = g x) (h : ℝ) {σsq : ℝ}
    (hσ : ∑ ξ, p ξ * ‖gs ξ - g x‖ ^ 2 ≤ σsq) :
    ∑ ξ, p ξ * ℒ (x - h • P (gs ξ)) ≤
      ℒ x - h * (1 - β * h / 2) * ‖P (g x)‖ ^ 2 + β * h ^ 2 / 2 * σsq := by
  have h1 := sum_loss_sub_smul_apply_le hℒ hg hP hp hp1 hmean h
  have h2 := mul_le_mul_of_nonneg_left ((sum_norm_sq_apply_sub_le hP hp gs (g x)).trans hσ)
    (by positivity : 0 ≤ β * h ^ 2 / 2)
  linarith

/-- **Augmentation with an independent minibatch.**  If the projector `Π_ζ` is built from a
minibatch `ζ` (weights `q_ζ`) drawn independently of the step minibatch `ξ` (weights `p_ξ`),
then, averaging over both,
`∑_ζ q_ζ ∑_ξ p_ξ ℒ(x - h Π_ζ g_ξ) ≤ ℒ(x) - h (1 - β h / 2) ∑_ζ q_ζ ‖Π_ζ ∇ℒ(x)‖²
  + β h² / 2 · ∑_ζ q_ζ ∑_ξ p_ξ ‖Π_ζ (g_ξ - ∇ℒ(x))‖²`. -/
theorem sum_sum_loss_le_of_indep {Ξ' : Type*} [Fintype Ξ']
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {Pi : Ξ' → E →L[ℝ] E}
    (hPi : ∀ ζ, IsOrthProj (Pi ζ)) {q : Ξ' → ℝ} (hq : ∀ ζ, 0 ≤ q ζ) (hq1 : ∑ ζ, q ζ = 1)
    {p : Ξ → ℝ} (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1) {gs : Ξ → E} {x : E}
    (hmean : ∑ ξ, p ξ • gs ξ = g x) (h : ℝ) :
    ∑ ζ, q ζ * ∑ ξ, p ξ * ℒ (x - h • Pi ζ (gs ξ)) ≤
      ℒ x - h * (1 - β * h / 2) * ∑ ζ, q ζ * ‖Pi ζ (g x)‖ ^ 2 +
        β * h ^ 2 / 2 * ∑ ζ, q ζ * ∑ ξ, p ξ * ‖Pi ζ (gs ξ - g x)‖ ^ 2 := by
  have hstep : ∀ ζ ∈ univ, q ζ * ∑ ξ, p ξ * ℒ (x - h • Pi ζ (gs ξ)) ≤
      q ζ * ℒ x - h * (1 - β * h / 2) * (q ζ * ‖Pi ζ (g x)‖ ^ 2) +
        β * h ^ 2 / 2 * (q ζ * ∑ ξ, p ξ * ‖Pi ζ (gs ξ - g x)‖ ^ 2) := by
    intro ζ _
    calc q ζ * ∑ ξ, p ξ * ℒ (x - h • Pi ζ (gs ξ))
        ≤ q ζ * (ℒ x - h * (1 - β * h / 2) * ‖Pi ζ (g x)‖ ^ 2 +
            β * h ^ 2 / 2 * ∑ ξ, p ξ * ‖Pi ζ (gs ξ - g x)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (sum_loss_sub_smul_apply_le hℒ hg (hPi ζ) hp hp1 hmean h)
            (hq ζ)
      _ = _ := by ring
  calc _ ≤ _ := sum_le_sum hstep
    _ = _ := by
      rw [sum_add_distrib, sum_sub_distrib, ← sum_mul, hq1, one_mul, ← mul_sum, ← mul_sum]

/-- **Descent with independent augmentation, Riemannian form.**  If every augmented projector
`Π_ζ` contains the range of a fixed orthogonal projector `T` applied to the gradient
(`Π_ζ T ∇ℒ(x) = T ∇ℒ(x)`, e.g. `T Z = U₀U₀ᵀ Z V₀V₀ᵀ` since the augmented bases contain the old
ones), then for `h (1 - β h / 2) ≥ 0`
`∑_ζ q_ζ ∑_ξ p_ξ ℒ(x - h Π_ζ g_ξ) ≤ ℒ(x) - h (1 - β h / 2) ‖T ∇ℒ(x)‖² + β h² σ² / 2`. -/
theorem sum_sum_loss_le_of_indep_of_absorbs {Ξ' : Type*} [Fintype Ξ']
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {Pi : Ξ' → E →L[ℝ] E}
    (hPi : ∀ ζ, IsOrthProj (Pi ζ)) {q : Ξ' → ℝ} (hq : ∀ ζ, 0 ≤ q ζ) (hq1 : ∑ ζ, q ζ = 1)
    {p : Ξ → ℝ} (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1) {gs : Ξ → E} {x : E}
    (hmean : ∑ ξ, p ξ • gs ξ = g x) {T : E →L[ℝ] E} (hT : IsOrthProj T)
    (habs : ∀ ζ, Pi ζ (T (g x)) = T (g x)) {h : ℝ} (hh : 0 ≤ h * (1 - β * h / 2))
    {σsq : ℝ} (hσ : ∑ ξ, p ξ * ‖gs ξ - g x‖ ^ 2 ≤ σsq) :
    ∑ ζ, q ζ * ∑ ξ, p ξ * ℒ (x - h • Pi ζ (gs ξ)) ≤
      ℒ x - h * (1 - β * h / 2) * ‖T (g x)‖ ^ 2 + β * h ^ 2 / 2 * σsq := by
  have h1 := sum_sum_loss_le_of_indep hℒ hg hPi hq hq1 hp hp1 hmean h
  have h2 : ‖T (g x)‖ ^ 2 ≤ ∑ ζ, q ζ * ‖Pi ζ (g x)‖ ^ 2 := by
    calc ‖T (g x)‖ ^ 2 = ∑ ζ, q ζ * ‖T (g x)‖ ^ 2 := by rw [← sum_mul, hq1, one_mul]
      _ ≤ _ := sum_le_sum fun ζ _ => mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (norm_apply_le_of_absorbs hT (hPi ζ) (habs ζ)) 2)
          (hq ζ)
  have h3 : ∑ ζ, q ζ * ∑ ξ, p ξ * ‖Pi ζ (gs ξ - g x)‖ ^ 2 ≤ σsq := by
    calc _ ≤ ∑ ζ, q ζ * σsq := sum_le_sum fun ζ _ => mul_le_mul_of_nonneg_left
          ((sum_norm_sq_apply_sub_le (hPi ζ) hp gs (g x)).trans hσ) (hq ζ)
      _ = σsq := by rw [← sum_mul, hq1, one_mul]
  have h4 := mul_le_mul_of_nonneg_left h2 hh
  have h5 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ β * h ^ 2 / 2)
  linarith

/-- **A single step ascends if the direction is an ascent direction.**  If
`β h / 2 ‖d‖² < -⟪∇ℒ(x), d⟫` and `h > 0`, then `ℒ(x) < ℒ(x - h d)`. -/
theorem lt_loss_sub_smul (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {x d : E} {h : ℝ} (hh : 0 < h)
    (hd : β * h / 2 * ‖d‖ ^ 2 < -⟪g x, d⟫) : ℒ x < ℒ (x - h • d) := by
  have h1 := le_loss_sub_smul hℒ hg x d h
  have h2 := mul_lt_mul_of_pos_left hd hh
  have e : β * h ^ 2 / 2 * ‖d‖ ^ 2 = h * (β * h / 2 * ‖d‖ ^ 2) := by ring
  linarith

/-- **Same-minibatch projectors: a negative bias forces expected ascent.**  If the projector
`Π_ξ` depends on the minibatch and the expected first-order term
`∑ p_ξ ⟪∇ℒ(x), Π_ξ g_ξ⟫` is negative, then for every step size
`0 < h < 2 |∑ p_ξ ⟪∇ℒ(x), Π_ξ g_ξ⟫| / (β ∑ p_ξ ‖Π_ξ g_ξ‖²)` the expected loss *increases*,
for every `β`-smooth loss with these gradient samples. -/
theorem lt_sum_loss_of_bias_neg (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {Pi : Ξ → E →L[ℝ] E} {p : Ξ → ℝ}
    (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1) (gs : Ξ → E) (x : E) {h : ℝ} (hh : 0 < h)
    (hbias : β * h / 2 * ∑ ξ, p ξ * ‖Pi ξ (gs ξ)‖ ^ 2 < -∑ ξ, p ξ * ⟪g x, Pi ξ (gs ξ)⟫) :
    ℒ x < ∑ ξ, p ξ * ℒ (x - h • Pi ξ (gs ξ)) := by
  have hstep : ∀ ξ ∈ univ, p ξ * ℒ x - h * (p ξ * ⟪g x, Pi ξ (gs ξ)⟫) -
      β * h ^ 2 / 2 * (p ξ * ‖Pi ξ (gs ξ)‖ ^ 2) ≤ p ξ * ℒ (x - h • Pi ξ (gs ξ)) := by
    intro ξ _
    calc _ = p ξ * (ℒ x - h * ⟪g x, Pi ξ (gs ξ)⟫ - β * h ^ 2 / 2 * ‖Pi ξ (gs ξ)‖ ^ 2) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_loss_sub_smul hℒ hg x _ h) (hp ξ)
  have hsum := sum_le_sum hstep
  rw [sum_sub_distrib, sum_sub_distrib, ← sum_mul, hp1, one_mul, ← mul_sum, ← mul_sum] at hsum
  have h2 := mul_lt_mul_of_pos_left hbias hh
  have e : β * h ^ 2 / 2 * ∑ ξ, p ξ * ‖Pi ξ (gs ξ)‖ ^ 2 =
      h * (β * h / 2 * ∑ ξ, p ξ * ‖Pi ξ (gs ξ)‖ ^ 2) := by ring
  linarith

/-- The quadratic loss `‖x - c‖² / 2` has gradient `x - c`. -/
theorem hasFDerivAt_half_norm_sq_sub (c x : E) :
    HasFDerivAt (fun x : E => ‖x - c‖ ^ 2 / 2) (innerSL ℝ (x - c)) x := by
  have h := (hasFDerivAt_half_norm_sq (x - c)).comp x ((hasFDerivAt_id x).sub_const c)
  simpa [Function.comp_def] using h

/-- Exact expansion of the quadratic loss along a step:
`‖a - h d‖² / 2 = ‖a‖² / 2 - h ⟪a, d⟫ + h² / 2 ‖d‖²`. -/
lemma half_norm_sq_sub_smul (a d : E) (h : ℝ) :
    ‖a - h • d‖ ^ 2 / 2 = ‖a‖ ^ 2 / 2 - h * ⟪a, d⟫ + h ^ 2 / 2 * ‖d‖ ^ 2 := by
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

end Abstract


/-! ### Orthonormal bases of an augmented span -/

section Bases

open scoped Matrix LeanDLRA.Frobenius

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k'] [DecidableEq k]

/-- The same-minibatch augmentation `[U₀, A V₀]` of a rank-one basis by the (minibatch)
gradient `A`, as in `Û = orth[U₀, G_ξ V₀]`. -/
def augBasis (U₀ : Matrix m (Fin 1) ℝ) (A : Matrix m n ℝ) (V₀ : Matrix n (Fin 1) ℝ) :
    Matrix m (Fin 2) ℝ :=
  Matrix.of fun i => ![U₀ i 0, (A * V₀) i 0]

/-- `Û` is an orthonormal basis whose columns lie in the column space of `K`
(`Ûᵀ Û = 1`, `Û = K C`); for `K` of full column rank this is `Û = orth(K)` up to a rotation. -/
def IsOrthBasisOf (Û K : Matrix m k ℝ) : Prop :=
  Ûᵀ * Û = 1 ∧ ∃ C : Matrix k k ℝ, Û = K * C

/-- **Bridge.** For bases with the same number of columns, `IsOrthBasisOf Û K` is the core
`Matrix.IsOrthBasisOf Û K`: the capture `Û Ûᵀ K = K` that the core predicate also asks for follows,
because `Ûᵀ K C = Ûᵀ Û = 1` makes the square matrix `C` invertible. -/
theorem isOrthBasisOf_iff {Û K : Matrix m k ℝ} : IsOrthBasisOf Û K ↔ Matrix.IsOrthBasisOf Û K := by
  constructor
  · rintro ⟨hÛ, C, hC⟩
    have h1 : Ûᵀ * K * C = 1 := by rw [Matrix.mul_assoc, ← hC, hÛ]
    have h2 : C * (Ûᵀ * K) = 1 := mul_eq_one_comm.1 h1
    refine ⟨hÛ, ?_, C, hC⟩
    calc Û * Ûᵀ * K = K * (C * (Ûᵀ * K)) := by rw [hC]; simp only [Matrix.mul_assoc]
      _ = K := by rw [h2, Matrix.mul_one]
  · rintro ⟨hÛ, -, hspan⟩
    exact ⟨hÛ, hspan⟩

/-- Two orthonormal bases with the same number of columns and `U = U' C` span the same space, so
they define the same orthogonal projector `U Uᵀ = U' U'ᵀ`. -/
lemma mul_transpose_eq_of_eq_mul {U U' : Matrix m k ℝ} (hU : Uᵀ * U = 1)
    {C : Matrix k k ℝ} (hC : U = U' * C) (hU' : U'ᵀ * U' = 1) : U * Uᵀ = U' * U'ᵀ := by
  have h1 : Cᵀ * C = 1 := by
    have e : Uᵀ * U = Cᵀ * (U'ᵀ * U') * C := by
      rw [hC, Matrix.transpose_mul]; simp [Matrix.mul_assoc]
    rwa [hU', Matrix.mul_one, hU, eq_comm] at e
  have h2 : C * Cᵀ = 1 := mul_eq_one_comm.1 h1
  rw [hC, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc C, h2, Matrix.one_mul]

/-- The projector of an orthonormal basis of the column space of `K = U' D` is `U' U'ᵀ`, for any
reference orthonormal basis `U'`: the Galerkin projector does not depend on how `orth` is
computed. -/
lemma IsOrthBasisOf.mul_transpose_eq {Û K U' : Matrix m k ℝ} (h : IsOrthBasisOf Û K)
    {D : Matrix k k ℝ} (hK : K = U' * D) (hU' : U'ᵀ * U' = 1) : Û * Ûᵀ = U' * U'ᵀ := by
  obtain ⟨hÛ, C, hC⟩ := h
  exact mul_transpose_eq_of_eq_mul hÛ (C := D * C) (by rw [hC, hK, Matrix.mul_assoc]) hU'

/-! The Galerkin projector `Z ↦ U Uᵀ Z V Vᵀ` onto `{U S Vᵀ}` is the core `LeanDLRA.galerkinProj`
(`galerkinProj_apply`, `isOrthProj_galerkinProj`); the local copy of an earlier version of this
file was the same definition (unification batch C2). -/

end Bases

/-! ### The counterexample -/

namespace SameBatchExample

open scoped Matrix LeanDLRA.Frobenius

/-- The current weight `W₀ = e₁ e₁ᵀ`. -/
noncomputable def W₀ : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, 0; 0, 0, 0]

/-- The full gradient `∇ℒ(W₀) = G`. -/
noncomputable def G : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 1; 1, 1, 0; 1, 0, 1]

/-- The minibatch noise `N`. -/
noncomputable def N : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, -1; 1, -6, 0; -1, 0, 6]

/-- The minibatch gradient `G₊ = G + N`. -/
noncomputable def Gp : Matrix (Fin 3) (Fin 3) ℝ := G + N

/-- The minibatch gradient `G₋ = G - N`. -/
noncomputable def Gm : Matrix (Fin 3) (Fin 3) ℝ := G - N

/-- The two equally likely minibatch gradients, indexed by `Bool`. -/
noncomputable def gs (ξ : Bool) : Matrix (Fin 3) (Fin 3) ℝ := if ξ then Gp else Gm

/-- The rank-one bases `U₀ = V₀ = e₁`. -/
noncomputable def e₁ : Matrix (Fin 3) (Fin 1) ℝ := !![1; 0; 0]

/-- Reference basis `[e₁, e₂]` for the `+` augmentation. -/
noncomputable def Up : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; 0, 0]

/-- Reference basis `[e₁, e₃]` for the `-` augmentation. -/
noncomputable def Um : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 0; 0, 1]

/-- Reference basis `[e₁, (e₂ + e₃)/√2]` for the deterministic augmentation. -/
noncomputable def Ud : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, (√2)⁻¹; 0, (√2)⁻¹]

/-- The change of basis `diag(1, 2)`. -/
noncomputable def D2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 2]

/-- The change of basis `diag(1, √2)`. -/
noncomputable def Ds : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, √2]

/-- The projector `diag(1, 1, 0)`. -/
noncomputable def Pp : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0; 0, 0, 0]

/-- The projector `diag(1, 0, 1)`. -/
noncomputable def Pm : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, 0; 0, 0, 1]

/-- The projector onto `span{e₁, (e₂ + e₃)/√2}`. -/
noncomputable def Pd : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1/2, 1/2; 0, 1/2, 1/2]

lemma Up_orth : Upᵀ * Up = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Up, Matrix.mul_apply, Fin.sum_univ_three]

lemma Um_orth : Umᵀ * Um = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Um, Matrix.mul_apply, Fin.sum_univ_three]

lemma inv_sqrt_two_mul_self : (√2)⁻¹ * (√2)⁻¹ = (1 / 2 : ℝ) := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma inv_sqrt_two_mul_sqrt_two : (√2)⁻¹ * √2 = (1 : ℝ) :=
  inv_mul_cancel₀ (by positivity)

lemma Ud_orth : Udᵀ * Ud = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Ud, Matrix.mul_apply, Fin.sum_univ_three, inv_sqrt_two_mul_self]

lemma Up_mul_transpose : Up * Upᵀ = Pp := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Up, Pp, Matrix.mul_apply, Fin.sum_univ_two]

lemma Um_mul_transpose : Um * Umᵀ = Pm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Um, Pm, Matrix.mul_apply, Fin.sum_univ_two]

lemma Ud_mul_transpose : Ud * Udᵀ = Pd := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Ud, Pd, Matrix.mul_apply, Fin.sum_univ_two, inv_sqrt_two_mul_self]

lemma augBasis_Gp : augBasis e₁ Gp e₁ = Up * D2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [augBasis, e₁, Gp, G, N, Up, D2, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_two]

lemma augBasis_Gp_transpose : augBasis e₁ Gpᵀ e₁ = Up * D2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [augBasis, e₁, Gp, G, N, Up, D2, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_two]

lemma augBasis_Gm : augBasis e₁ Gm e₁ = Um * D2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [augBasis, e₁, Gm, G, N, Um, D2, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_two]

lemma augBasis_Gm_transpose : augBasis e₁ Gmᵀ e₁ = Um * D2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [augBasis, e₁, Gm, G, N, Um, D2, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_two]

lemma augBasis_G : augBasis e₁ G e₁ = Ud * Ds := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [augBasis, e₁, G, Ud, Ds, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two,
      inv_sqrt_two_mul_sqrt_two]

lemma augBasis_G_transpose : augBasis e₁ Gᵀ e₁ = Ud * Ds := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [augBasis, e₁, G, Ud, Ds, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two,
      inv_sqrt_two_mul_sqrt_two]

lemma Pp_conj (X : Matrix (Fin 3) (Fin 3) ℝ) :
    Pp * X * Pp = !![X 0 0, X 0 1, 0; X 1 0, X 1 1, 0; 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Pp, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

lemma Pm_conj (X : Matrix (Fin 3) (Fin 3) ℝ) :
    Pm * X * Pm = !![X 0 0, 0, X 0 2; 0, 0, 0; X 2 0, 0, X 2 2] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Pm, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

lemma Pd_conj (X : Matrix (Fin 3) (Fin 3) ℝ) :
    Pd * X * Pd = !![X 0 0, (X 0 1 + X 0 2) / 2, (X 0 1 + X 0 2) / 2;
      (X 1 0 + X 2 0) / 2, (X 1 1 + X 1 2 + X 2 1 + X 2 2) / 4,
        (X 1 1 + X 1 2 + X 2 1 + X 2 2) / 4;
      (X 1 0 + X 2 0) / 2, (X 1 1 + X 1 2 + X 2 1 + X 2 2) / 4,
        (X 1 1 + X 1 2 + X 2 1 + X 2 2) / 4] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Pd, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;> ring

/-- The same-minibatch Galerkin projector of outcome `+` keeps the `{1,2} × {1,2}` block. -/
lemma galerkinProj_plus {Û Vh : Matrix (Fin 3) (Fin 2) ℝ}
    (hÛ : IsOrthBasisOf Û (augBasis e₁ Gp e₁)) (hVh : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁))
    (X : Matrix (Fin 3) (Fin 3) ℝ) : galerkinProj Û Vh X = Pp * X * Pp := by
  rw [galerkinProj_apply, (hÛ.mul_transpose_eq augBasis_Gp Up_orth).trans Up_mul_transpose,
    (hVh.mul_transpose_eq augBasis_Gp_transpose Up_orth).trans Up_mul_transpose]

/-- The same-minibatch Galerkin projector of outcome `-` keeps the `{1,3} × {1,3}` block. -/
lemma galerkinProj_minus {Û Vh : Matrix (Fin 3) (Fin 2) ℝ}
    (hÛ : IsOrthBasisOf Û (augBasis e₁ Gm e₁)) (hVh : IsOrthBasisOf Vh (augBasis e₁ Gmᵀ e₁))
    (X : Matrix (Fin 3) (Fin 3) ℝ) : galerkinProj Û Vh X = Pm * X * Pm := by
  rw [galerkinProj_apply, (hÛ.mul_transpose_eq augBasis_Gm Um_orth).trans Um_mul_transpose,
    (hVh.mul_transpose_eq augBasis_Gm_transpose Um_orth).trans Um_mul_transpose]

/-- The deterministic augmented Galerkin projector (bases augmented with the full gradient). -/
lemma galerkinProj_det {Û Vh : Matrix (Fin 3) (Fin 2) ℝ}
    (hÛ : IsOrthBasisOf Û (augBasis e₁ G e₁)) (hVh : IsOrthBasisOf Vh (augBasis e₁ Gᵀ e₁))
    (X : Matrix (Fin 3) (Fin 3) ℝ) : galerkinProj Û Vh X = Pd * X * Pd := by
  rw [galerkinProj_apply, (hÛ.mul_transpose_eq augBasis_G Ud_orth).trans Ud_mul_transpose,
    (hVh.mul_transpose_eq augBasis_G_transpose Ud_orth).trans Ud_mul_transpose]

/-- The reference bases are admissible. -/
lemma isOrthBasisOf_Up : IsOrthBasisOf Up (augBasis e₁ Gp e₁) :=
  ⟨Up_orth, !![1, 0; 0, 1 / 2], by
    rw [augBasis_Gp, Matrix.mul_assoc]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Up, D2, Matrix.mul_apply, Fin.sum_univ_two]⟩

lemma isOrthBasisOf_Up' : IsOrthBasisOf Up (augBasis e₁ Gpᵀ e₁) := by
  rw [augBasis_Gp_transpose, ← augBasis_Gp]; exact isOrthBasisOf_Up

lemma isOrthBasisOf_Um : IsOrthBasisOf Um (augBasis e₁ Gm e₁) :=
  ⟨Um_orth, !![1, 0; 0, 1 / 2], by
    rw [augBasis_Gm, Matrix.mul_assoc]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Um, D2, Matrix.mul_apply, Fin.sum_univ_two]⟩

lemma isOrthBasisOf_Um' : IsOrthBasisOf Um (augBasis e₁ Gmᵀ e₁) := by
  rw [augBasis_Gm_transpose, ← augBasis_Gm]; exact isOrthBasisOf_Um

/-! #### The loss `ℒ(W) = ½‖W - W₀ + G‖²` -/

/-- The quadratic loss `ℒ(W) = ½ ‖W - W₀ + G‖²` (identity Hessian, `β = 1`). -/
noncomputable def loss (W : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := ‖W - (W₀ - G)‖ ^ 2 / 2

/-- Its gradient `∇ℒ(W) = W - W₀ + G`. -/
noncomputable def grad (W : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ := W - (W₀ - G)

lemma hasFDerivAt_loss (W : Matrix (Fin 3) (Fin 3) ℝ) :
    HasFDerivAt loss (innerSL ℝ (grad W)) W :=
  hasFDerivAt_half_norm_sq_sub (W₀ - G) W

lemma grad_lipschitz (X Y : Matrix (Fin 3) (Fin 3) ℝ) : ‖grad X - grad Y‖ ≤ 1 * ‖X - Y‖ := by
  simp [grad]

lemma grad_W₀ : grad W₀ = G := sub_sub_cancel _ _

/-- The two minibatch gradients are unbiased: `½ G₊ + ½ G₋ = G`. -/
lemma sum_gs : ∑ ξ : Bool, (1 / 2 : ℝ) • gs ξ = grad W₀ := by
  rw [grad_W₀, Fintype.sum_bool]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [gs, Gp, Gm, G, N]

lemma norm_sq_G : ‖G‖ ^ 2 = 6 := by
  rw [Frobenius.norm_sq_eq_sum]; norm_num [G, Fin.sum_univ_three]

lemma loss_W₀ : loss W₀ = 3 := by
  rw [loss, sub_sub_cancel, norm_sq_G]; norm_num

/-- The loss along a step from `W₀` is an exact quadratic:
`ℒ(W₀ - η D) = ℒ(W₀) - η ⟪G, D⟫ + η² / 2 ‖D‖²`. -/
lemma loss_W₀_sub_smul (D : Matrix (Fin 3) (Fin 3) ℝ) (η : ℝ) :
    loss (W₀ - η • D) = loss W₀ - η * ⟪G, D⟫ + η ^ 2 / 2 * ‖D‖ ^ 2 := by
  rw [loss, sub_sub_sub_cancel_left, half_norm_sq_sub_smul, loss, sub_sub_cancel]

/-! #### The same-minibatch steps -/

section SameBatch

variable {Uh Vh : Matrix (Fin 3) (Fin 2) ℝ}

lemma inner_G_plus (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁)) : ⟪G, galerkinProj Uh Vh Gp⟫ = -1 := by
  rw [galerkinProj_plus hU hV, Pp_conj, Frobenius.inner_def]
  norm_num [G, Gp, N, Fin.sum_univ_three]

lemma norm_sq_plus (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁)) : ‖galerkinProj Uh Vh Gp‖ ^ 2 = 33 := by
  rw [galerkinProj_plus hU hV, Pp_conj, Frobenius.norm_sq_eq_sum]
  norm_num [G, Gp, N, Fin.sum_univ_three]

lemma inner_G_minus (hU : IsOrthBasisOf Uh (augBasis e₁ Gm e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gmᵀ e₁)) : ⟪G, galerkinProj Uh Vh Gm⟫ = -1 := by
  rw [galerkinProj_minus hU hV, Pm_conj, Frobenius.inner_def]
  norm_num [G, Gm, N, Fin.sum_univ_three]

lemma norm_sq_minus (hU : IsOrthBasisOf Uh (augBasis e₁ Gm e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gmᵀ e₁)) : ‖galerkinProj Uh Vh Gm‖ ^ 2 = 33 := by
  rw [galerkinProj_minus hU hV, Pm_conj, Frobenius.norm_sq_eq_sum]
  norm_num [G, Gm, N, Fin.sum_univ_three]

/-- `‖Π₊ G‖² = 3`. -/
lemma norm_sq_plus_G (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁)) : ‖galerkinProj Uh Vh G‖ ^ 2 = 3 := by
  rw [galerkinProj_plus hU hV, Pp_conj, Frobenius.norm_sq_eq_sum]
  norm_num [G, Fin.sum_univ_three]

/-- `‖Π₋ G‖² = 3`. -/
lemma norm_sq_minus_G (hU : IsOrthBasisOf Uh (augBasis e₁ Gm e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gmᵀ e₁)) : ‖galerkinProj Uh Vh G‖ ^ 2 = 3 := by
  rw [galerkinProj_minus hU hV, Pm_conj, Frobenius.norm_sq_eq_sum]
  norm_num [G, Fin.sum_univ_three]

/-- Projected noise `‖Π₊ (G₊ - G)‖² = 38`. -/
lemma norm_sq_plus_noise (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁)) : ‖galerkinProj Uh Vh (Gp - G)‖ ^ 2 = 38 := by
  rw [galerkinProj_plus hU hV, Pp_conj, Frobenius.norm_sq_eq_sum]
  norm_num [G, Gp, N, Fin.sum_univ_three]

/-- Projected noise `‖Π₋ (G₋ - G)‖² = 38`. -/
lemma norm_sq_minus_noise (hU : IsOrthBasisOf Uh (augBasis e₁ Gm e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gmᵀ e₁)) : ‖galerkinProj Uh Vh (Gm - G)‖ ^ 2 = 38 := by
  rw [galerkinProj_minus hU hV, Pm_conj, Frobenius.norm_sq_eq_sum]
  norm_num [G, Gm, N, Fin.sum_univ_three]

/-- Unprojected noise `‖G₊ - G‖² = ‖N‖² = 76`. -/
lemma norm_sq_noise_plus : ‖Gp - G‖ ^ 2 = 76 := by
  rw [Frobenius.norm_sq_eq_sum]; norm_num [G, Gp, N, Fin.sum_univ_three]

/-- Unprojected noise `‖G₋ - G‖² = ‖N‖² = 76`. -/
lemma norm_sq_noise_minus : ‖Gm - G‖ ^ 2 = 76 := by
  rw [Frobenius.norm_sq_eq_sum]; norm_num [G, Gm, N, Fin.sum_univ_three]

/-- **Counterexample, outcome `+`.**  For every orthonormal basis `Û₊` of `span[U₀, G₊V₀]` and
`V̂₊` of `span[V₀, G₊ᵀU₀]`, the same-minibatch step `W₀ - η Π₊ G₊` has
`ℒ(W₀ - η Π₊ G₊) = ℒ(W₀) + η + 33 η² / 2`. -/
theorem loss_sameBatch_plus (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁)) (η : ℝ) :
    loss (W₀ - η • galerkinProj Uh Vh Gp) = loss W₀ + η + 33 / 2 * η ^ 2 := by
  rw [loss_W₀_sub_smul, inner_G_plus hU hV, norm_sq_plus hU hV]; ring

/-- **Counterexample, outcome `-`**: `ℒ(W₀ - η Π₋ G₋) = ℒ(W₀) + η + 33 η² / 2`. -/
theorem loss_sameBatch_minus (hU : IsOrthBasisOf Uh (augBasis e₁ Gm e₁))
    (hV : IsOrthBasisOf Vh (augBasis e₁ Gmᵀ e₁)) (η : ℝ) :
    loss (W₀ - η • galerkinProj Uh Vh Gm) = loss W₀ + η + 33 / 2 * η ^ 2 := by
  rw [loss_W₀_sub_smul, inner_G_minus hU hV, norm_sq_minus hU hV]; ring

/-- **Every realisation ascends**: for every learning rate `η > 0`, both same-minibatch steps
increase the loss. -/
theorem loss_W₀_lt_sameBatch {Uh' Vh' : Matrix (Fin 3) (Fin 2) ℝ}
    (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁)) (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁))
    (hU' : IsOrthBasisOf Uh' (augBasis e₁ Gm e₁)) (hV' : IsOrthBasisOf Vh' (augBasis e₁ Gmᵀ e₁))
    {η : ℝ} (hη : 0 < η) :
    loss W₀ < loss (W₀ - η • galerkinProj Uh Vh Gp) ∧
      loss W₀ < loss (W₀ - η • galerkinProj Uh' Vh' Gm) := by
  rw [loss_sameBatch_plus hU hV, loss_sameBatch_minus hU' hV']
  constructor <;> nlinarith

/-- **The expected first-order term is negative**: `E ⟪∇ℒ(W₀), Π_ξ G_ξ⟫ = -1`, although
`E G_ξ = ∇ℒ(W₀)`. -/
theorem expected_inner_sameBatch {Uh' Vh' : Matrix (Fin 3) (Fin 2) ℝ}
    (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁)) (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁))
    (hU' : IsOrthBasisOf Uh' (augBasis e₁ Gm e₁)) (hV' : IsOrthBasisOf Vh' (augBasis e₁ Gmᵀ e₁)) :
    1 / 2 * ⟪grad W₀, galerkinProj Uh Vh Gp⟫ + 1 / 2 * ⟪grad W₀, galerkinProj Uh' Vh' Gm⟫ =
      -1 := by
  rw [grad_W₀, inner_G_plus hU hV, inner_G_minus hU' hV']; norm_num

/-- **Loss-independent form**: for *every* `β`-smooth loss whose gradient at `W₀` is `G` (and
in particular for every loss with minibatch gradients `G_±` at `W₀`), both same-minibatch steps
increase the loss for `0 < η < 2 / (33 β)`. -/
theorem lt_loss_sameBatch_of_smooth {E' : Matrix (Fin 3) (Fin 3) ℝ → ℝ}
    {g : Matrix (Fin 3) (Fin 3) ℝ → Matrix (Fin 3) (Fin 3) ℝ} {β : ℝ}
    (hℒ : ∀ x, HasFDerivAt E' (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hgW₀ : g W₀ = G) {Uh' Vh' : Matrix (Fin 3) (Fin 2) ℝ}
    (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁)) (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁))
    (hU' : IsOrthBasisOf Uh' (augBasis e₁ Gm e₁)) (hV' : IsOrthBasisOf Vh' (augBasis e₁ Gmᵀ e₁))
    {η : ℝ} (hη : 0 < η) (hβη : β * η * 33 < 2) :
    E' W₀ < E' (W₀ - η • galerkinProj Uh Vh Gp) ∧
      E' W₀ < E' (W₀ - η • galerkinProj Uh' Vh' Gm) := by
  constructor
  · refine lt_loss_sub_smul hℒ hg hη ?_
    rw [hgW₀, inner_G_plus hU hV, norm_sq_plus hU hV]; linarith
  · refine lt_loss_sub_smul hℒ hg hη ?_
    rw [hgW₀, inner_G_minus hU' hV', norm_sq_minus hU' hV']; linarith

/-- **The published-style expected descent bound is false.**  With `β = 1`,
`E ‖Π_ξ ∇ℒ‖² = 3` and the gradient variance `σ² = E ‖G_ξ - G‖² = 76`, the inequality
`E ℒ(W₊) ≤ ℒ(W₀) - η (1 - β η / 2) E ‖Π_ξ ∇ℒ(W₀)‖² + β η² σ² / 2` fails for every
`0 < η < 4/23`. -/
theorem published_bound_false {Uh' Vh' : Matrix (Fin 3) (Fin 2) ℝ}
    (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁)) (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁))
    (hU' : IsOrthBasisOf Uh' (augBasis e₁ Gm e₁)) (hV' : IsOrthBasisOf Vh' (augBasis e₁ Gmᵀ e₁))
    {η : ℝ} (hη : 0 < η) (hη' : η < 4 / 23) :
    loss W₀ - η * (1 - 1 * η / 2) *
        (1 / 2 * ‖galerkinProj Uh Vh (grad W₀)‖ ^ 2 +
          1 / 2 * ‖galerkinProj Uh' Vh' (grad W₀)‖ ^ 2) +
      1 * η ^ 2 / 2 * (1 / 2 * ‖gs true - grad W₀‖ ^ 2 + 1 / 2 * ‖gs false - grad W₀‖ ^ 2) <
    1 / 2 * loss (W₀ - η • galerkinProj Uh Vh (gs true)) +
      1 / 2 * loss (W₀ - η • galerkinProj Uh' Vh' (gs false)) := by
  simp only [gs, ite_true, Bool.false_eq_true, ite_false, grad_W₀]
  rw [loss_sameBatch_plus hU hV, loss_sameBatch_minus hU' hV', norm_sq_plus_G hU hV,
    norm_sq_minus_G hU' hV', norm_sq_noise_plus, norm_sq_noise_minus]
  nlinarith [mul_pos hη (by linarith : (0 : ℝ) < 4 - 23 * η)]

/-- The bound also fails with the *projected* variance `σ_Π² = E ‖Π_ξ (G_ξ - G)‖² = 38`
(the form stated in the open problem), now for every `0 < η < 1`. -/
theorem published_bound_false_projVar {Uh' Vh' : Matrix (Fin 3) (Fin 2) ℝ}
    (hU : IsOrthBasisOf Uh (augBasis e₁ Gp e₁)) (hV : IsOrthBasisOf Vh (augBasis e₁ Gpᵀ e₁))
    (hU' : IsOrthBasisOf Uh' (augBasis e₁ Gm e₁)) (hV' : IsOrthBasisOf Vh' (augBasis e₁ Gmᵀ e₁))
    {η : ℝ} (hη : 0 < η) (hη' : η < 1) :
    loss W₀ - η * (1 - 1 * η / 2) *
        (1 / 2 * ‖galerkinProj Uh Vh (grad W₀)‖ ^ 2 +
          1 / 2 * ‖galerkinProj Uh' Vh' (grad W₀)‖ ^ 2) +
      1 * η ^ 2 / 2 * (1 / 2 * ‖galerkinProj Uh Vh (gs true - grad W₀)‖ ^ 2 +
        1 / 2 * ‖galerkinProj Uh' Vh' (gs false - grad W₀)‖ ^ 2) <
    1 / 2 * loss (W₀ - η • galerkinProj Uh Vh (gs true)) +
      1 / 2 * loss (W₀ - η • galerkinProj Uh' Vh' (gs false)) := by
  simp only [gs, ite_true, Bool.false_eq_true, ite_false, grad_W₀]
  rw [loss_sameBatch_plus hU hV, loss_sameBatch_minus hU' hV', norm_sq_plus_G hU hV,
    norm_sq_minus_G hU' hV', norm_sq_plus_noise hU hV, norm_sq_minus_noise hU' hV']
  nlinarith [mul_pos hη (by linarith : (0 : ℝ) < 1 - η)]

end SameBatch

/-! #### Contrast: deterministic augmentation and the tangent step -/

/-- With the bases augmented by the *full* gradient (`Û = orth[U₀, G V₀]`), the first-order
term is `⟪G, Π_G G⟫ = ‖Π_G G‖² = 5 > 0`. -/
theorem inner_G_det {Uh Vh : Matrix (Fin 3) (Fin 2) ℝ}
    (hU : IsOrthBasisOf Uh (augBasis e₁ G e₁)) (hV : IsOrthBasisOf Vh (augBasis e₁ Gᵀ e₁)) :
    ⟪G, galerkinProj Uh Vh G⟫ = 5 ∧ ‖galerkinProj Uh Vh G‖ ^ 2 = 5 := by
  rw [galerkinProj_det hU hV, Pd_conj, Frobenius.inner_def, Frobenius.norm_sq_eq_sum]
  constructor <;> norm_num [G, Fin.sum_univ_three]

lemma e₁_mul_transpose : e₁ * e₁ᵀ = W₀ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₁, W₀, Matrix.mul_apply]

lemma tangentProj_e₁_apply (X : Matrix (Fin 3) (Fin 3) ℝ) :
    tangentProj e₁ e₁ X = W₀ * X + X * W₀ - W₀ * (X * W₀) := by
  simp only [tangentProj, tangent_apply, leftProj_apply, rightProj_apply', e₁_mul_transpose]

/-- **The tangent (GeoLoRA) step stays unbiased**: `P(W₀)` does not depend on the minibatch, so
`E ⟪G, P(W₀) G_ξ⟫ = ⟪G, P(W₀) G⟫ = ‖P(W₀) G‖² = 4 > 0`. -/
theorem expected_inner_tangent :
    1 / 2 * ⟪grad W₀, tangentProj e₁ e₁ Gp⟫ + 1 / 2 * ⟪grad W₀, tangentProj e₁ e₁ Gm⟫ = 4 ∧
      ‖tangentProj e₁ e₁ (grad W₀)‖ ^ 2 = 4 := by
  have hsum := sum_inner_apply_eq sum_gs (tangentProj e₁ e₁) (grad W₀)
  rw [Fintype.sum_bool] at hsum
  simp only [gs, ite_true, Bool.false_eq_true, ite_false] at hsum
  rw [hsum, grad_W₀, tangentProj_e₁_apply, Frobenius.inner_def, Frobenius.norm_sq_eq_sum]
  constructor <;> norm_num [G, W₀, Matrix.mul_apply, Fin.sum_univ_three]

/-- `P(W₀) G₊ = [[0,2,0],[2,0,0],[0,0,0]]`: `⟪G, P(W₀) G₊⟫ = 4`, `‖P(W₀) G₊‖² = 8`. -/
lemma tangent_plus : ⟪G, tangentProj e₁ e₁ Gp⟫ = 4 ∧ ‖tangentProj e₁ e₁ Gp‖ ^ 2 = 8 := by
  rw [tangentProj_e₁_apply, Frobenius.inner_def, Frobenius.norm_sq_eq_sum]
  constructor <;> norm_num [G, Gp, N, W₀, Matrix.mul_apply, Fin.sum_univ_three]

/-- `P(W₀) G₋ = [[0,0,2],[0,0,0],[2,0,0]]`: `⟪G, P(W₀) G₋⟫ = 4`, `‖P(W₀) G₋‖² = 8`. -/
lemma tangent_minus : ⟪G, tangentProj e₁ e₁ Gm⟫ = 4 ∧ ‖tangentProj e₁ e₁ Gm‖ ^ 2 = 8 := by
  rw [tangentProj_e₁_apply, Frobenius.inner_def, Frobenius.norm_sq_eq_sum]
  constructor <;> norm_num [G, Gm, N, W₀, Matrix.mul_apply, Fin.sum_univ_three]

/-- Projected variance of the tangent step: `‖P(W₀)(G_± - G)‖² = ‖P(W₀) N‖² = 4`. -/
lemma tangent_noise : ‖tangentProj e₁ e₁ (Gp - G)‖ ^ 2 = 4 ∧
    ‖tangentProj e₁ e₁ (Gm - G)‖ ^ 2 = 4 := by
  rw [tangentProj_e₁_apply, tangentProj_e₁_apply, Frobenius.norm_sq_eq_sum,
    Frobenius.norm_sq_eq_sum]
  constructor <;> norm_num [G, Gp, Gm, N, W₀, Matrix.mul_apply, Fin.sum_univ_three]

/-- Exact expected loss of the tangent (GeoLoRA) step with minibatch gradients:
`E ℒ(W₀ - η P(W₀) G_ξ) = ℒ(W₀) - 4 η + 4 η²`. -/
lemma expected_loss_tangent (η : ℝ) :
    1 / 2 * loss (W₀ - η • tangentProj e₁ e₁ Gp) +
      1 / 2 * loss (W₀ - η • tangentProj e₁ e₁ Gm) = loss W₀ - 4 * η + 4 * η ^ 2 := by
  rw [loss_W₀_sub_smul, loss_W₀_sub_smul, tangent_plus.1, tangent_plus.2, tangent_minus.1,
    tangent_minus.2]
  ring

/-- **Sharpness of the corrected bound.**  For the tangent step, whose projector does not depend
on the minibatch, the bound of `sum_loss_sub_smul_apply_le` is an *equality* here:
`E ℒ(W₀ - η P G_ξ) = ℒ(W₀) - η (1 - η/2) ‖P G‖² + η²/2 · E ‖P (G_ξ - G)‖²`. -/
theorem tangent_bound_sharp (η : ℝ) :
    1 / 2 * loss (W₀ - η • tangentProj e₁ e₁ Gp) +
      1 / 2 * loss (W₀ - η • tangentProj e₁ e₁ Gm) =
    loss W₀ - η * (1 - 1 * η / 2) * ‖tangentProj e₁ e₁ (grad W₀)‖ ^ 2 +
      1 * η ^ 2 / 2 * (1 / 2 * ‖tangentProj e₁ e₁ (Gp - grad W₀)‖ ^ 2 +
        1 / 2 * ‖tangentProj e₁ e₁ (Gm - grad W₀)‖ ^ 2) := by
  have hPG : ‖tangentProj e₁ e₁ G‖ ^ 2 = 4 := by
    have h := expected_inner_tangent.2
    rwa [grad_W₀] at h
  rw [expected_loss_tangent, grad_W₀, hPG, tangent_noise.1, tangent_noise.2]
  ring

/-- **The variance-free GeoLoRA-type bound is false even for the tangent projector.**  The bound
`E ℒ(W₊) ≤ ℒ(W₀) - η (1 - β η / 2) E ‖P(W₀) G_ξ‖²` (the form of eq. (11) of arXiv 2410.18720 as
used in its proof, without truncation) fails for every `η > 0`: the left side is
`3 - 4η + 4η²`, the right side `3 - 8η + 4η²`.  The missing term is the variance. -/
theorem geoLoRA_bound_false {η : ℝ} (hη : 0 < η) :
    loss W₀ - η * (1 - 1 * η / 2) *
        (1 / 2 * ‖tangentProj e₁ e₁ Gp‖ ^ 2 + 1 / 2 * ‖tangentProj e₁ e₁ Gm‖ ^ 2) <
      1 / 2 * loss (W₀ - η • tangentProj e₁ e₁ Gp) +
        1 / 2 * loss (W₀ - η • tangentProj e₁ e₁ Gm) := by
  rw [expected_loss_tangent, tangent_plus.2, tangent_minus.2]
  nlinarith

/-- The main-text factor `1 - β η² / 2` of arXiv 2410.18720, Thm 1, fails as well, for every
`0 < η ≤ 3/2` (the left side is `3 - 4η + 4η²`, the right side `3 - 8η + 4η³`). -/
theorem geoLoRA_bound_false_mainText {η : ℝ} (hη : 0 < η) (hη' : η ≤ 3 / 2) :
    loss W₀ - η * (1 - 1 * η ^ 2 / 2) *
        (1 / 2 * ‖tangentProj e₁ e₁ Gp‖ ^ 2 + 1 / 2 * ‖tangentProj e₁ e₁ Gm‖ ^ 2) <
      1 / 2 * loss (W₀ - η • tangentProj e₁ e₁ Gp) +
        1 / 2 * loss (W₀ - η • tangentProj e₁ e₁ Gm) := by
  rw [expected_loss_tangent, tangent_plus.2, tangent_minus.2]
  nlinarith [mul_pos hη hη, mul_nonneg hη.le (by linarith : (0 : ℝ) ≤ 3 / 2 - η)]

/-- **The correct theorem applies** to the same data once the projector is frozen: with the
`ξ`-independent projector `Π₊` (e.g. built from an independent minibatch that happened to be
`+`), the expected loss obeys the bound of `sum_loss_sub_smul_apply_le_variance`. -/
example (η : ℝ) :
    ∑ ξ : Bool, (1 / 2 : ℝ) * loss (W₀ - η • galerkinProj Up Up (gs ξ)) ≤
      loss W₀ - η * (1 - 1 * η / 2) * ‖galerkinProj Up Up (grad W₀)‖ ^ 2 +
        1 * η ^ 2 / 2 * 76 := by
  refine sum_loss_sub_smul_apply_le_variance hasFDerivAt_loss grad_lipschitz zero_le_one
    (isOrthProj_galerkinProj Up_orth Up_orth) (fun _ => by norm_num) (by simp)
    sum_gs η ?_
  rw [Fintype.sum_bool]
  simp only [gs, ite_true, Bool.false_eq_true, ite_false, grad_W₀]
  rw [norm_sq_noise_plus, norm_sq_noise_minus]; norm_num

/-- The admissible bases of the counterexample exist (the hypotheses are satisfiable). -/
example : loss W₀ < loss (W₀ - (1 / 10 : ℝ) • galerkinProj Up Up Gp) ∧
    loss W₀ < loss (W₀ - (1 / 10 : ℝ) • galerkinProj Um Um Gm) :=
  loss_W₀_lt_sameBatch isOrthBasisOf_Up isOrthBasisOf_Up' isOrthBasisOf_Um isOrthBasisOf_Um'
    (by norm_num)

end SameBatchExample

/-- The local Galerkin projector of this file, replaced by the core `LeanDLRA.galerkinProj` (same
definition `leftProj U * rightProj V`). -/
@[deprecated (since := "2026-11-09")] alias galerkinProj := LeanDLRA.galerkinProj

/-- Replaced by the core `LeanDLRA.galerkinProj_apply`. -/
@[deprecated (since := "2026-11-09")] alias galerkinProj_apply := LeanDLRA.galerkinProj_apply

/-- Replaced by the core `LeanDLRA.isOrthProj_galerkinProj`. -/
@[deprecated (since := "2026-11-09")] alias isOrthProj_galerkinProj :=
  LeanDLRA.isOrthProj_galerkinProj

end StochasticDescent

end LeanDLRA
