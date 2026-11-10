import LeanDLRA.Research.SameMinibatchAugmentation
import LeanDLRA.Training.Defs

/-!
# Low-rank training with inexact values and gradients

In DLRA-constrained optimisation (optimal control, inverse problems and low-rank training of
neural networks) the objective `ℒ` and its gradient are only available through a dynamical
low-rank solve: the values `ℒ̃` and gradients `g̃` carry errors `|ℒ̃ - ℒ| ≤ δ`,
`‖g̃ - ∇ℒ‖ ≤ η`, where `η`, `δ` are controlled by the robust integrator bounds
`c₁ ε + c₂ h + c₃ n ϑ` (`bug_global_error_le`, `ksl_global_error_le` for the forward and adjoint
runs), by a finite-difference step or by a surrogate bias.  This file proves that the standard
descent guarantees survive these errors, in the abstract calculus of `Training/Descent.lean`
(a real inner product space `E`, a `β`-smooth loss `ℒ` with gradient `g`, orthogonal projectors
`Π` with `IsOrthProj`).

## Main results

**OP-TR-02 (inexact-gradient descent; arXiv 2506.21405 Alg. 2, arXiv 2409.14938 Algs. 2–3,
arXiv 2610.29554 Sec. 6.3, arXiv 2509.15113 Sec. 5).**
* `loss_inexact_step_le`: for `0 ≤ h`, `β h ≤ 1`,
  `ℒ(x - h Π g̃) ≤ ℒ(x) - (h/2) ‖Π ∇ℒ(x)‖² + (h/2) ‖Π (g̃ - ∇ℒ(x))‖²`
  (descent lemma plus polarization `2⟪a, b⟫ = ‖a‖² + ‖b‖² - ‖a - b‖²`).
* `exists_projGrad_sq_le_of_inexact` (claim (i)):
  `min_{k<n} ‖Π_k ∇ℒ(x_k)‖² ≤ 2 (ℒ(x₀) - ℒ_inf) / (n h) + η²`.
* `exists_projGrad_sq_le_of_relInexact` (claim (iii), tolerance coupled to the gradient size,
  `‖Π(g̃ - ∇ℒ)‖ ≤ ρ ‖Π ∇ℒ‖`, `ρ < 1`): the exact rate
  `min_{k<n} ‖Π_k ∇ℒ(x_k)‖² ≤ 2 (ℒ(x₀) - ℒ_inf) / (n h (1 - ρ²))` is kept.
* `loss_sub_le_of_PL_inexact` (claim (ii)): under the (Riemannian) PL inequality
  `2μ (ℒ(x_k) - ℒ⋆) ≤ ‖Π_k ∇ℒ(x_k)‖²` (implied by `μ`-strong convexity, e.g. linear-quadratic
  control), `ℒ(x_n) - ℒ⋆ ≤ (1 - μh)ⁿ (ℒ(x₀) - ℒ⋆) + η² / (2μ)`: linear convergence to an
  `O(η²/μ)` neighbourhood in loss; `norm_sub_sq_le_of_PL_inexact`: under quadratic growth the
  iterates converge linearly to the ball of radius `η/μ` around `z⋆`.
* Armijo backtracking with inexact values and gradients (claim (iii)):
  `armijoTest_of_le` gives explicit sufficient conditions (`β s ≤ 1 - c`,
  `4η ≤ (1 - c)‖g̃‖`, `8δ ≤ (1 - c) s ‖g̃‖²`) under which the inexact test
  `ℒ̃(x - s g̃) ≤ ℒ̃(x) - c s ‖g̃‖²` passes; `exists_armijo_backtracking` proves that halving
  from `s₀` terminates at the first accepted step `s₀ / 2ʲ ≥ min(s₀, (1-c)/(2β))` as long as
  `16 β δ ≤ (1-c)² ‖g̃‖²` and `8δ ≤ (1-c) s₀ ‖g̃‖²` (the gradient dominates `η` and `δ`);
  `exists_dir_sq_le_of_armijo` gives convergence of the accepted Armijo iteration to a
  `2δ/(c s_min)` neighbourhood.  Before this file the tolerance rules of 2506.21405 and
  2409.14938 were heuristic and convergence was observed only numerically.

**OP-TR-04 (discrete S-step solvers; arXiv 2104.05247 Sec. 3.3 after Thm 5).**
* explicit Euler is `loss_projGradStep_le` (Descent.lean);
* `loss_implicitEuler_le`: the implicit Euler (proximal) Galerkin step
  `x₁ = x₀ - h Π ∇ℒ(x₁)` satisfies `ℒ(x₁) ≤ ℒ(x₀) - h (1 - βh/2) ‖Π ∇ℒ(x₁)‖²`, i.e. descent for
  `h < 2/β`; `loss_implicitEuler_le_of_convex`: unconditional descent
  `ℒ(x₁) ≤ ℒ(x₀) - h ‖Π ∇ℒ(x₁)‖²` for convex `ℒ`; `exists_implicitEuler`: the implicit stage
  exists for `h β < 1` (Banach fixed point) in a complete space;
* `loss_discreteGradient_eq`: a discrete-gradient step decreases the loss exactly by
  `h ‖Π ∇̄ℒ‖²` (`isDiscreteGradient_midpoint` is a non-degenerate example);
* every variant with the truncation term `G ϑ`
  (`loss_truncated_implicitEuler_le`, `loss_truncated_discreteGradient_le`), and a perturbed
  (e.g. higher-order explicit) step `‖x₁ - (x₀ - hΠ∇ℒ(x₀))‖ ≤ C h²` loses at most `G C h²`
  (`loss_perturbedStep_le`).

**OP-TR-08 (stochastic descent; arXiv 2410.18720 Thm 1, arXiv 2502.03006 Thms 5.8–5.9).**
* `sum_loss_truncated_le_variance`: for unbiased minibatch gradients on a finite probability
  space and a projector `Π` independent of the minibatch, the truncated SGD step satisfies
  `E ℒ(W₊) ≤ ℒ(W) - λ(1 - βλ/2) ‖Π∇ℒ(W)‖² + βλ²σ²/2 + Gϑ` (the one-step bound of the
  open problem, with the gradient bound `G`, not `β`, in the truncation term).
* `variance_term_necessary`: the variance term cannot be dropped (the flaw of the published
  proofs): for `ℒ = x²/2` on `ℝ` and samples `±1`, the expected loss strictly increases.
* `frequently_lt_of_expected_descent`: the Robbins–Monro conclusion
  `liminf_k E ‖Π_k ∇ℒ(W_k)‖² = 0` for any sequences of expectations obeying the one-step
  bound.  **What remains**: the passage from the conditional one-step bound to the
  unconditional recursion for `a_k = E ℒ(W_k)`, `b_k = E ‖Π_k ∇ℒ(W_k)‖²` (tower property for a
  filtration) is not formalized; it is a hypothesis of `frequently_lt_of_expected_descent`.
  With minibatch-dependent projectors the unbiasedness identity fails
  (`lt_sum_loss_of_bias_neg`, `published_bound_false` in `Research/SameMinibatchAugmentation`).

**Online projected gradient with perturbed gradients (arXiv 2009.03887, Thm 1 and Eq. (15)).**
* `regret_le_of_perturbed`: for convex-feasible-set projections (nonexpansive towards `w⋆`),
  `c`-strongly convex losses (inequality (8)), gradient perturbations
  `‖ε_t‖ ≤ (c/2) ‖w_t - w⋆‖` (sufficient condition (15)), `‖g̃_t‖ ≤ G + E`, diameter `D` and
  nonincreasing `η_t > 0`: `R(T) ≤ D²/(2 η_{T-1}) + (G+E)²/2 ∑ η_t`.
* `regret_le_sqrt`: with `η_t = 1/√(t+1)`, `R(T) ≤ (D²/2) √T + (G+E)² (√T - 1/2)`, which is
  exactly Theorem 1 of 2009.03887.

The statements `exists_projGrad_sq_le_of_inexact`, `exists_projGrad_sq_le_of_relInexact`
and `loss_sub_le_of_PL_inexact` are proved here (same names, in the
namespace `LeanDLRA.InexactGradient`).
-/

open Set Finset Filter
open scoped RealInnerProductSpace

namespace LeanDLRA.InexactGradient

open LeanDLRA LeanDLRA.StochasticDescent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### OP-TR-02: inexact projected gradient descent -/

section Inexact

variable {ℒ : E → ℝ} {g : E → E} {β : ℝ}

/-- **Inexact projected gradient step** (OP-TR-02, the key one-step estimate): for an
orthogonal projector `Π`, `0 ≤ h` and `β h ≤ 1`, the step with an arbitrary gradient surrogate
`g̃` satisfies
`ℒ(x - h Π g̃) ≤ ℒ(x) - (h/2) ‖Π ∇ℒ(x)‖² + (h/2) ‖Π (g̃ - ∇ℒ(x))‖²`. -/
theorem loss_inexact_step_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {P : E →L[ℝ] E} (hP : IsOrthProj P) {h : ℝ}
    (hh : 0 ≤ h) (hβh : β * h ≤ 1) (x gt : E) :
    ℒ (x - h • P gt) ≤ ℒ x - h / 2 * ‖P (g x)‖ ^ 2 + h / 2 * ‖P (gt - g x)‖ ^ 2 := by
  have hd := loss_sub_smul_le hℒ hg x (P gt) h
  have e2 : ⟪g x, P gt⟫ = ⟪P (g x), P gt⟫ := by rw [hP.symm, hP.idem]
  have e3 : ‖P (gt - g x)‖ ^ 2 = ‖P gt‖ ^ 2 - 2 * ⟪P gt, P (g x)⟫ + ‖P (g x)‖ ^ 2 := by
    rw [map_sub, norm_sub_sq_real]
  have hpos : 0 ≤ h * (1 - β * h) * ‖P gt‖ ^ 2 :=
    mul_nonneg (mul_nonneg hh (by linarith)) (sq_nonneg _)
  rw [e2, real_inner_comm] at hd
  rw [e3]
  nlinarith

/-- **Inexact gradient descent, claim (i) of OP-TR-02**: if the projected gradient errors are at
most `η` and `0 < h`, `β h ≤ 1`, then
`min_{k<n} ‖Π_k ∇ℒ(x_k)‖² ≤ 2 (ℒ(x₀) - ℒ_inf) / (n h) + η²`.  With `η = c₁ε + c₂h + c₃nϑ` from
the robust DLRA error bounds this quantifies the stationarity reached by DLRA-based
optimisation (arXiv 2506.21405, 2409.14938, 2610.29554, 2509.15113). -/
theorem exists_projGrad_sq_le_of_inexact (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {P : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k))
    {x gt : ℕ → E} {h η ℒinf : ℝ} (hh : 0 < h) (hβh : β * h ≤ 1)
    (hx : ∀ k, x (k + 1) = x k - h • P k (gt k)) (hη : ∀ k, ‖P k (gt k - g (x k))‖ ≤ η)
    (hinf : ∀ k, ℒinf ≤ ℒ (x k)) {n : ℕ} (hn : 0 < n) :
    ∃ k < n, ‖P k (g (x k))‖ ^ 2 ≤ 2 * (ℒ (x 0) - ℒinf) / (n * h) + η ^ 2 := by
  have hstep : ∀ k, h / 2 * ‖P k (g (x k))‖ ^ 2 ≤
      ℒ (x k) - ℒ (x (k + 1)) + h / 2 * η ^ 2 := by
    intro k
    have h1 := loss_inexact_step_le hℒ hg (hP k) hh.le hβh (x k) (gt k)
    have h2 : ‖P k (gt k - g (x k))‖ ^ 2 ≤ η ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hη k) 2
    have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ h / 2)
    rw [hx k]
    linarith
  have hsum := sum_le_of_le_sub_add (u := fun k => ℒ (x k)) hstep n
  rw [← mul_sum, sum_const, card_range, nsmul_eq_mul] at hsum
  have hsum' : h / 2 * ∑ k ∈ range n, ‖P k (g (x k))‖ ^ 2 ≤
      (ℒ (x 0) - ℒinf) + n * (h / 2 * η ^ 2) := by linarith [hinf n]
  obtain ⟨k, hk, hle⟩ := exists_le_of_mul_sum_le (by linarith : 0 < h / 2) hn hsum'
  refine ⟨k, hk, hle.trans_eq ?_⟩
  field_simp

/-- **Relative-error gradients keep the exact rate** (claim (iii) of OP-TR-02, tolerance
coupled to the gradient size as in arXiv 2506.21405 and the adaptive tolerances of
arXiv 2610.29554): if
`‖Π_k (g̃_k - ∇ℒ(x_k))‖ ≤ ρ ‖Π_k ∇ℒ(x_k)‖` with `0 ≤ ρ < 1`, then
`min_{k<n} ‖Π_k ∇ℒ(x_k)‖² ≤ 2 (ℒ(x₀) - ℒ_inf) / (n h (1 - ρ²))`. -/
theorem exists_projGrad_sq_le_of_relInexact (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {P : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k))
    {x gt : ℕ → E} {h ρ ℒinf : ℝ} (hh : 0 < h) (hβh : β * h ≤ 1) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hx : ∀ k, x (k + 1) = x k - h • P k (gt k))
    (hη : ∀ k, ‖P k (gt k - g (x k))‖ ≤ ρ * ‖P k (g (x k))‖)
    (hinf : ∀ k, ℒinf ≤ ℒ (x k)) {n : ℕ} (hn : 0 < n) :
    ∃ k < n, ‖P k (g (x k))‖ ^ 2 ≤ 2 * (ℒ (x 0) - ℒinf) / (n * h * (1 - ρ ^ 2)) := by
  have hc : 0 < h / 2 * (1 - ρ ^ 2) := mul_pos (by linarith) (by nlinarith)
  have hstep : ∀ k, h / 2 * (1 - ρ ^ 2) * ‖P k (g (x k))‖ ^ 2 ≤
      ℒ (x k) - ℒ (x (k + 1)) + 0 := by
    intro k
    have h1 := loss_inexact_step_le hℒ hg (hP k) hh.le hβh (x k) (gt k)
    have h2 : ‖P k (gt k - g (x k))‖ ^ 2 ≤ (ρ * ‖P k (g (x k))‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hη k) 2
    have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ h / 2)
    rw [hx k]
    nlinarith
  have hsum := sum_le_of_le_sub_add (u := fun k => ℒ (x k)) hstep n
  rw [← mul_sum, sum_const_zero] at hsum
  have hsum' : h / 2 * (1 - ρ ^ 2) * ∑ k ∈ range n, ‖P k (g (x k))‖ ^ 2 ≤
      (ℒ (x 0) - ℒinf) + n * 0 := by linarith [hinf n]
  obtain ⟨k, hk, hle⟩ := exists_le_of_mul_sum_le hc hn hsum'
  refine ⟨k, hk, hle.trans_eq ?_⟩
  have h1ρ : (1 - ρ ^ 2) ≠ 0 := by nlinarith
  field_simp
  ring

/-- **Linear convergence to an `η²`-ball under PL with inexact gradients** (claim (ii) of
OP-TR-02).  Under the (Riemannian) PL
inequality `2μ (ℒ(x_k) - ℒ⋆) ≤ ‖Π_k ∇ℒ(x_k)‖²` (implied by `μ`-strong convexity when `Π = 1`,
e.g. the linear-quadratic control problems of arXiv 2509.15113 and 2610.29554), `β h ≤ 1` and
`μ h ≤ 1`: `ℒ(x_n) - ℒ⋆ ≤ (1 - μh)ⁿ (ℒ(x₀) - ℒ⋆) + η² / (2μ)`. -/
theorem loss_sub_le_of_PL_inexact (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {P : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k))
    {x gt : ℕ → E} {h η μ ℒstar : ℝ} (hh : 0 < h) (hβh : β * h ≤ 1) (hμ : 0 < μ)
    (hμh : μ * h ≤ 1) (hx : ∀ k, x (k + 1) = x k - h • P k (gt k))
    (hη : ∀ k, ‖P k (gt k - g (x k))‖ ≤ η)
    (hPL : ∀ k, 2 * μ * (ℒ (x k) - ℒstar) ≤ ‖P k (g (x k))‖ ^ 2) (n : ℕ) :
    ℒ (x n) - ℒstar ≤ (1 - μ * h) ^ n * (ℒ (x 0) - ℒstar) + η ^ 2 / (2 * μ) := by
  have hstep : ∀ k, ℒ (x (k + 1)) - ℒstar ≤
      (1 - μ * h) * (ℒ (x k) - ℒstar) + h / 2 * η ^ 2 := by
    intro k
    have h1 := loss_inexact_step_le hℒ hg (hP k) hh.le hβh (x k) (gt k)
    have h2 : ‖P k (gt k - g (x k))‖ ^ 2 ≤ η ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hη k) 2
    have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ h / 2)
    have h4 := mul_le_mul_of_nonneg_left (hPL k) (by linarith : 0 ≤ h / 2)
    rw [hx k]
    nlinarith
  have hq : 0 ≤ 1 - μ * h := by linarith
  have e : η ^ 2 / (2 * μ) = (1 - μ * h) * (η ^ 2 / (2 * μ)) + h / 2 * η ^ 2 := by
    field_simp
    ring
  induction n with
  | zero => simp only [pow_zero, one_mul]; have := div_nonneg (sq_nonneg η) (by linarith :
      (0 : ℝ) ≤ 2 * μ); linarith
  | succ n ih =>
    calc ℒ (x (n + 1)) - ℒstar ≤ (1 - μ * h) * (ℒ (x n) - ℒstar) + h / 2 * η ^ 2 := hstep n
      _ ≤ (1 - μ * h) * ((1 - μ * h) ^ n * (ℒ (x 0) - ℒstar) + η ^ 2 / (2 * μ)) +
          h / 2 * η ^ 2 := by gcongr
      _ = _ := by rw [pow_succ]; linear_combination (-1 : ℝ) * e

/-- **Convergence of the iterates to an `O(η/μ)` ball** (claim (ii) of OP-TR-02, iterate
form): if moreover the quadratic growth `μ/2 ‖x - z⋆‖² ≤ ℒ(x) - ℒ⋆` holds (a consequence of
`μ`-strong convexity), then
`‖x_n - z⋆‖² ≤ (2/μ) ((1 - μh)ⁿ (ℒ(x₀) - ℒ⋆)) + η² / μ²`. -/
theorem norm_sub_sq_le_of_PL_inexact (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {P : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k))
    {x gt : ℕ → E} {h η μ ℒstar : ℝ} {zstar : E} (hh : 0 < h) (hβh : β * h ≤ 1) (hμ : 0 < μ)
    (hμh : μ * h ≤ 1) (hx : ∀ k, x (k + 1) = x k - h • P k (gt k))
    (hη : ∀ k, ‖P k (gt k - g (x k))‖ ≤ η)
    (hPL : ∀ k, 2 * μ * (ℒ (x k) - ℒstar) ≤ ‖P k (g (x k))‖ ^ 2)
    (hgrowth : ∀ y, μ / 2 * ‖y - zstar‖ ^ 2 ≤ ℒ y - ℒstar) (n : ℕ) :
    ‖x n - zstar‖ ^ 2 ≤ 2 / μ * ((1 - μ * h) ^ n * (ℒ (x 0) - ℒstar)) + η ^ 2 / μ ^ 2 := by
  have h1 := loss_sub_le_of_PL_inexact hℒ hg hP hh hβh hμ hμh hx hη hPL n
  have h2 := hgrowth (x n)
  have e : ‖x n - zstar‖ ^ 2 = 2 / μ * (μ / 2 * ‖x n - zstar‖ ^ 2) := by field_simp
  have e2 : η ^ 2 / μ ^ 2 = 2 / μ * (η ^ 2 / (2 * μ)) := by field_simp
  rw [e, e2, ← mul_add]
  exact mul_le_mul_of_nonneg_left (h2.trans h1) (by positivity)

end Inexact

/-! ### OP-TR-02 (iii): Armijo backtracking with inexact values and gradients -/

section Armijo

variable {ℒ ℒt : E → ℝ} {g : E → E} {β : ℝ}

/-- The inexact test along the inexact direction: if `|ℒ̃ - ℒ| ≤ δ` at `x` and at `x - s d`,
`‖d - ∇ℒ(x)‖ ≤ η` and `s ≥ 0`, then
`ℒ̃(x - s d) ≤ ℒ̃(x) - s ‖d‖² + s η ‖d‖ + β s²/2 ‖d‖² + 2δ`. -/
theorem lossT_sub_smul_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {x d : E} {s η δ : ℝ} (hs : 0 ≤ s)
    (hd : ‖d - g x‖ ≤ η) (hδx : |ℒt x - ℒ x| ≤ δ) (hδs : |ℒt (x - s • d) - ℒ (x - s • d)| ≤ δ) :
    ℒt (x - s • d) ≤ ℒt x - s * ‖d‖ ^ 2 + s * η * ‖d‖ + β * s ^ 2 / 2 * ‖d‖ ^ 2 + 2 * δ := by
  have h1 := loss_sub_smul_le hℒ hg x d s
  have h2 : ⟪d - g x, d⟫ ≤ η * ‖d‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 hs
  have h4 := (abs_le.1 hδx).1
  have h5 := (abs_le.1 hδs).2
  nlinarith

/-- **Explicit acceptance region of the inexact Armijo test.**  If `0 ≤ s`, `β s ≤ 1 - c`,
`4 η ≤ (1 - c) ‖d‖` and `8 δ ≤ (1 - c) s ‖d‖²`, the inexact test
`ℒ̃(x - s d) ≤ ℒ̃(x) - c s ‖d‖²` passes.  So every step in
`[8δ / ((1-c)‖d‖²), (1-c)/β]` is accepted. -/
theorem armijoTest_of_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {x d : E} {s η δ c : ℝ} (hs : 0 ≤ s)
    (hd : ‖d - g x‖ ≤ η) (hδ : ∀ y, |ℒt y - ℒ y| ≤ δ) (hβs : β * s ≤ 1 - c)
    (hη : 4 * η ≤ (1 - c) * ‖d‖) (hδs : 8 * δ ≤ (1 - c) * s * ‖d‖ ^ 2) :
    ArmijoTest ℒt c x d s := by
  have h1 := lossT_sub_smul_le hℒ hg hs hd (hδ x) (hδ _)
  have h2 : s * η * ‖d‖ ≤ s * ((1 - c) / 4 * ‖d‖) * ‖d‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hs) (norm_nonneg _)
  have h3 : 0 ≤ s * (1 - c - β * s) * ‖d‖ ^ 2 :=
    mul_nonneg (mul_nonneg hs (by linarith)) (sq_nonneg _)
  unfold ArmijoTest
  nlinarith

/-- **Termination of inexact Armijo backtracking** (OP-TR-02 (iii); arXiv 2506.21405 Alg. 2,
arXiv 2409.14938 Algs. 2–3).  Let `β > 0`, `0 < c < 1`, `s₀ > 0`, values with error `δ`, and
a direction `d = g̃` with `‖d - ∇ℒ(x)‖ ≤ η`.  If the direction dominates the errors,
`4η ≤ (1-c)‖d‖` and `16 β δ ≤ (1-c)² ‖d‖²`, and `8δ ≤ (1-c) s₀ ‖d‖²`, then backtracking
`s_j = s₀ / 2ʲ` terminates: there is a first index `j` whose step passes the test, and the
accepted step satisfies `min(s₀, (1-c)/(2β)) ≤ s₀ / 2ʲ`. -/
theorem exists_armijo_backtracking (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 < β) {x d : E} {s₀ η δ c : ℝ}
    (hs₀ : 0 < s₀) (hc1 : c < 1) (hd : ‖d - g x‖ ≤ η) (hδ : ∀ y, |ℒt y - ℒ y| ≤ δ)
    (hη : 4 * η ≤ (1 - c) * ‖d‖) (hdom : 16 * β * δ ≤ (1 - c) ^ 2 * ‖d‖ ^ 2)
    (hδs₀ : 8 * δ ≤ (1 - c) * s₀ * ‖d‖ ^ 2) :
    ∃ j : ℕ, ArmijoTest ℒt c x d (s₀ * (1 / 2) ^ j) ∧
      (∀ i < j, ¬ ArmijoTest ℒt c x d (s₀ * (1 / 2) ^ i)) ∧
      min s₀ ((1 - c) / (2 * β)) ≤ s₀ * (1 / 2) ^ j := by
  classical
  set smax := (1 - c) / β with hsmax
  have hc' : 0 < 1 - c := by linarith
  have hsmax0 : 0 < smax := div_pos hc' hβ
  -- the first halving below `smax`
  have hex : ∃ j : ℕ, s₀ * (1 / 2) ^ j ≤ smax := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hsmax0 hs₀) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, ?_⟩
    rw [lt_div_iff₀ hs₀] at hn
    linarith
  set J := Nat.find hex with hJ
  have hJle : s₀ * (1 / 2) ^ J ≤ smax := Nat.find_spec hex
  have hpos : ∀ j : ℕ, 0 < s₀ * (1 / 2 : ℝ) ^ j := fun j => by positivity
  have hJlow : 8 * δ ≤ (1 - c) * (s₀ * (1 / 2) ^ J) * ‖d‖ ^ 2 ∧
      min s₀ ((1 - c) / (2 * β)) ≤ s₀ * (1 / 2) ^ J := by
    rcases Nat.eq_zero_or_pos J with h0 | hpos'
    · rw [h0, pow_zero, mul_one]
      exact ⟨hδs₀, min_le_left _ _⟩
    · obtain ⟨i, hi⟩ : ∃ i, J = i + 1 := ⟨J - 1, by omega⟩
      have hnot : ¬ s₀ * (1 / 2) ^ i ≤ smax := Nat.find_min hex (by omega)
      have hgt : smax / 2 < s₀ * (1 / 2) ^ J := by
        rw [hi, pow_succ]; have := not_le.1 hnot; linarith
      have e : smax / 2 = (1 - c) / (2 * β) := by rw [hsmax]; field_simp
      refine ⟨?_, (min_le_right _ _).trans (e ▸ hgt.le)⟩
      have h1 : (1 - c) * (smax / 2) * ‖d‖ ^ 2 ≤ (1 - c) * (s₀ * (1 / 2) ^ J) * ‖d‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgt.le hc'.le) (sq_nonneg _)
      have h2 : (1 - c) * (smax / 2) * ‖d‖ ^ 2 = (1 - c) ^ 2 * ‖d‖ ^ 2 / (2 * β) := by
        rw [hsmax]; field_simp
      have h3 : 8 * δ ≤ (1 - c) ^ 2 * ‖d‖ ^ 2 / (2 * β) := by
        rw [le_div_iff₀ (by linarith)]; linarith
      linarith
  have htestJ : ArmijoTest ℒt c x d (s₀ * (1 / 2) ^ J) := by
    refine armijoTest_of_le hℒ hg (hpos J).le hd hδ ?_ hη hJlow.1
    have := mul_le_mul_of_nonneg_left hJle hβ.le
    rw [hsmax, mul_div_cancel₀ _ hβ.ne'] at this
    exact this
  have hex' : ∃ j, ArmijoTest ℒt c x d (s₀ * (1 / 2) ^ j) := ⟨J, htestJ⟩
  refine ⟨Nat.find hex', Nat.find_spec hex', fun i hi => Nat.find_min hex' hi, ?_⟩
  refine hJlow.2.trans ?_
  have hle : Nat.find hex' ≤ J := Nat.find_min' hex' htestJ
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hle) hs₀.le

/-- An accepted inexact Armijo step decreases the *true* loss up to `2δ`:
`ℒ(x - s d) ≤ ℒ(x) - c s ‖d‖² + 2δ`. -/
theorem loss_le_of_armijoTest {x d : E} {s c δ : ℝ} (hδ : ∀ y, |ℒt y - ℒ y| ≤ δ)
    (ht : ArmijoTest ℒt c x d s) : ℒ (x - s • d) ≤ ℒ x - c * s * ‖d‖ ^ 2 + 2 * δ := by
  unfold ArmijoTest at ht
  have h1 := (abs_le.1 (hδ x)).2
  have h2 := (abs_le.1 (hδ (x - s • d))).1
  linarith

/-- **Convergence of inexact Armijo descent to a neighbourhood**: if every accepted step
`s_k ≥ s_min > 0` passes the inexact test (e.g. `s_min = min(s₀, (1-c)/(2β))` from
`exists_armijo_backtracking`), `c > 0` and `ℒ ≥ ℒ_inf`, then
`min_{k<n} ‖g̃_k‖² ≤ (ℒ(x₀) - ℒ_inf) / (n c s_min) + 2δ / (c s_min)`; since
`‖∇ℒ(x_k)‖ ≤ ‖g̃_k‖ + η`, the true gradients reach the `O(η + √(δ / (c s_min)))` level. -/
theorem exists_dir_sq_le_of_armijo {x d : ℕ → E} {s : ℕ → ℝ} {c δ smin ℒinf : ℝ}
    (hc : 0 < c) (hsmin : 0 < smin) (hs : ∀ k, smin ≤ s k)
    (hδ : ∀ y, |ℒt y - ℒ y| ≤ δ) (hx : ∀ k, x (k + 1) = x k - s k • d k)
    (ht : ∀ k, ArmijoTest ℒt c (x k) (d k) (s k)) (hinf : ∀ k, ℒinf ≤ ℒ (x k)) {n : ℕ}
    (hn : 0 < n) :
    ∃ k < n, ‖d k‖ ^ 2 ≤ (ℒ (x 0) - ℒinf) / (n * (c * smin)) + 2 * δ / (c * smin) := by
  have hstep : ∀ k, c * smin * ‖d k‖ ^ 2 ≤ ℒ (x k) - ℒ (x (k + 1)) + 2 * δ := by
    intro k
    have h1 := loss_le_of_armijoTest hδ (ht k)
    have h2 : c * smin * ‖d k‖ ^ 2 ≤ c * s k * ‖d k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hs k) hc.le) (sq_nonneg _)
    rw [hx k]
    linarith
  have hsum := sum_le_of_le_sub_add (u := fun k => ℒ (x k)) hstep n
  rw [← mul_sum, sum_const, card_range, nsmul_eq_mul] at hsum
  have hsum' : c * smin * ∑ k ∈ range n, ‖d k‖ ^ 2 ≤ (ℒ (x 0) - ℒinf) + n * (2 * δ) := by
    linarith [hinf n]
  exact exists_le_of_mul_sum_le (mul_pos hc hsmin) hn hsum'

end Armijo

/-! ### OP-TR-04: discrete S-step solvers -/

section SStep

variable {ℒ : E → ℝ} {g : E → E} {β : ℝ} {P : E →L[ℝ] E}

/-- **Implicit Euler (proximal) Galerkin step** (OP-TR-04 (b), arXiv 2104.05247 Sec. 3.3): if
`x₁ = x₀ - h Π ∇ℒ(x₁)`, then `ℒ(x₁) ≤ ℒ(x₀) - h (1 - β h / 2) ‖Π ∇ℒ(x₁)‖²`; in particular the
loss decreases for `0 ≤ h ≤ 2/β`. -/
theorem loss_implicitEuler_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hP : IsOrthProj P) {h : ℝ} {x₀ x₁ : E}
    (hx : x₁ = x₀ - h • P (g x₁)) :
    ℒ x₁ ≤ ℒ x₀ - h * (1 - β * h / 2) * ‖P (g x₁)‖ ^ 2 := by
  have hd := descent_lemma_lower hℒ hg x₁ x₀
  have e : x₀ - x₁ = h • P (g x₁) := by
    have := eq_sub_iff_add_eq.1 hx; rw [← this]; abel
  rw [e, inner_smul_right, real_inner_comm, hP.inner_self_apply, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs] at hd
  linarith

/-- **Unconditional descent of the implicit Euler step for convex losses** (OP-TR-04 (b)): if
`ℒ` satisfies the first-order convexity inequality `ℒ x + ⟪∇ℒ(x), y - x⟫ ≤ ℒ y`, then for
every `h`, `ℒ(x₁) ≤ ℒ(x₀) - h ‖Π ∇ℒ(x₁)‖²`. -/
theorem loss_implicitEuler_le_of_convex (hconv : ∀ x y, ℒ x + ⟪g x, y - x⟫ ≤ ℒ y)
    (hP : IsOrthProj P) {h : ℝ} {x₀ x₁ : E} (hx : x₁ = x₀ - h • P (g x₁)) :
    ℒ x₁ ≤ ℒ x₀ - h * ‖P (g x₁)‖ ^ 2 := by
  have hd := hconv x₁ x₀
  have e : x₀ - x₁ = h • P (g x₁) := by
    have := eq_sub_iff_add_eq.1 hx; rw [← this]; abel
  rw [e, inner_smul_right, real_inner_comm, hP.inner_self_apply] at hd
  linarith

/-- **Existence of the implicit Euler stage** (OP-TR-04 (b)): in a complete space, for
`0 ≤ h` and `h β < 1`, the map `y ↦ x₀ - h Π ∇ℒ(y)` is a contraction, so the implicit Galerkin
step `x₁ = x₀ - h Π ∇ℒ(x₁)` has a solution (unique by `implicitEuler_unique`). -/
theorem exists_implicitEuler [CompleteSpace E] (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hP : IsOrthProj P) {h : ℝ} (hh : 0 ≤ h) (hhβ : h * β < 1) (x₀ : E) :
    ∃ x₁, x₁ = x₀ - h • P (g x₁) := by
  set F : E → E := fun y => x₀ - h • P (g y) with hF
  have hK0 : 0 ≤ h * max β 0 := mul_nonneg hh (le_max_right _ _)
  have hKlt : h * max β 0 < 1 := by
    rcases le_total β 0 with hb | hb
    · rw [max_eq_right hb, mul_zero]; exact one_pos
    · rw [max_eq_left hb]; linarith
  have hC : ContractingWith (h * max β 0).toNNReal F := by
    refine ⟨Real.toNNReal_lt_one.2 hKlt, LipschitzWith.of_dist_le_mul fun y z => ?_⟩
    simp only [Real.coe_toNNReal _ hK0, dist_eq_norm, hF]
    have e : x₀ - h • P (g y) - (x₀ - h • P (g z)) = h • P (g z - g y) := by
      rw [map_sub, smul_sub]; abel
    rw [e, norm_smul, Real.norm_of_nonneg hh, norm_sub_rev y z]
    calc h * ‖P (g z - g y)‖ ≤ h * (β * ‖z - y‖) :=
          mul_le_mul_of_nonneg_left ((hP.norm_le _).trans (hg z y)) hh
      _ ≤ h * (max β 0 * ‖z - y‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (norm_nonneg _)) hh
      _ = _ := by ring
  have : Nonempty E := ⟨x₀⟩
  exact ⟨ContractingWith.fixedPoint F hC, (ContractingWith.fixedPoint_isFixedPt hC).symm⟩

/-- A truncation after any step with loss bound `B` costs at most `G ϑ`: if `ℒ(x₁) ≤ B`,
`‖x₁' - x₁‖ ≤ ϑ` and `‖∇ℒ‖ ≤ G` on `[x₁, x₁']`, then `ℒ(x₁') ≤ B + G ϑ`. -/
theorem loss_truncated_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) {x₁ x₁' : E}
    {B ϑ G : ℝ} (hB : ℒ x₁ ≤ B) (htr : ‖x₁' - x₁‖ ≤ ϑ)
    (hG : ∀ w ∈ segment ℝ x₁ x₁', ‖g w‖ ≤ G) : ℒ x₁' ≤ B + G * ϑ := by
  have h2 := abs_energy_sub_le hℒ hG
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG _ (left_mem_segment ℝ _ _))
  have h3 : G * ‖x₁' - x₁‖ ≤ G * ϑ := mul_le_mul_of_nonneg_left htr hG0
  have h4 := (abs_le.1 h2).2
  linarith

/-- **Implicit Euler S-step followed by truncation** (OP-TR-04 (b) with the truncation term):
`ℒ(x₁') ≤ ℒ(x₀) - h (1 - βh/2) ‖Π ∇ℒ(x₁)‖² + G ϑ`. -/
theorem loss_truncated_implicitEuler_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hP : IsOrthProj P) {h : ℝ} {x₀ x₁ x₁' : E}
    (hx : x₁ = x₀ - h • P (g x₁)) {ϑ G : ℝ} (htr : ‖x₁' - x₁‖ ≤ ϑ)
    (hG : ∀ w ∈ segment ℝ x₁ x₁', ‖g w‖ ≤ G) :
    ℒ x₁' ≤ ℒ x₀ - h * (1 - β * h / 2) * ‖P (g x₁)‖ ^ 2 + G * ϑ :=
  loss_truncated_le hℒ (loss_implicitEuler_le hℒ hg hP hx) htr hG

/-- The midpoint discrete gradient `(x + y)/2` of the quadratic loss `‖x‖²/2`
(a non-degenerate instance of `IsDiscreteGradient`). -/
theorem isDiscreteGradient_midpoint :
    IsDiscreteGradient (fun x : E => ‖x‖ ^ 2 / 2) (fun x y => (1 / 2 : ℝ) • (x + y)) := by
  intro x y
  simp only
  rw [real_inner_smul_left, inner_add_left, inner_sub_right, inner_sub_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm y x]
  ring

/-- **Discrete-gradient S-step** (OP-TR-04 (c)): if `x₁ = x₀ - h Π ∇̄ℒ(x₀, x₁)`, the loss
decreases *exactly* by `h ‖Π ∇̄ℒ(x₀, x₁)‖²`, for every `h` (no step size restriction). -/
theorem loss_discreteGradient_eq {gb : E → E → E} (hdg : IsDiscreteGradient ℒ gb)
    (hP : IsOrthProj P) {h : ℝ} {x₀ x₁ : E} (hx : x₁ = x₀ - h • P (gb x₀ x₁)) :
    ℒ x₁ = ℒ x₀ - h * ‖P (gb x₀ x₁)‖ ^ 2 := by
  have hd := hdg x₀ x₁
  have e : x₁ - x₀ = -(h • P (gb x₀ x₁)) := by
    rw [sub_eq_iff_eq_add]; conv_lhs => rw [hx]
    abel
  rw [e, inner_neg_right, inner_smul_right, real_inner_comm, hP.inner_self_apply] at hd
  linarith

/-- **Discrete-gradient S-step followed by truncation** (OP-TR-04 (c) with the truncation
term): `ℒ(x₁') ≤ ℒ(x₀) - h ‖Π ∇̄ℒ(x₀, x₁)‖² + G ϑ`. -/
theorem loss_truncated_discreteGradient_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    {gb : E → E → E} (hdg : IsDiscreteGradient ℒ gb) (hP : IsOrthProj P) {h : ℝ}
    {x₀ x₁ x₁' : E} (hx : x₁ = x₀ - h • P (gb x₀ x₁)) {ϑ G : ℝ} (htr : ‖x₁' - x₁‖ ≤ ϑ)
    (hG : ∀ w ∈ segment ℝ x₁ x₁', ‖g w‖ ≤ G) :
    ℒ x₁' ≤ ℒ x₀ - h * ‖P (gb x₀ x₁)‖ ^ 2 + G * ϑ :=
  loss_truncated_le hℒ (loss_discreteGradient_eq hdg hP hx).le htr hG

/-- **Sufficiently accurate (e.g. higher-order explicit) S-steps** (OP-TR-04, last claim): if
the computed S-step `x₁` is within `C h²` of the explicit Euler Galerkin step and `‖∇ℒ‖ ≤ G`
in between, then `ℒ(x₁) ≤ ℒ(x₀) - h (1 - βh/2) ‖Π∇ℒ(x₀)‖² + G C h²`. -/
theorem loss_perturbedStep_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hP : IsOrthProj P) {h C G : ℝ} {x₀ x₁ : E}
    (hacc : ‖x₁ - projGradStep P g h x₀‖ ≤ C * h ^ 2)
    (hG : ∀ w ∈ segment ℝ (projGradStep P g h x₀) x₁, ‖g w‖ ≤ G) :
    ℒ x₁ ≤ ℒ x₀ - h * (1 - β * h / 2) * ‖P (g x₀)‖ ^ 2 + G * (C * h ^ 2) :=
  loss_truncated_projGradStep_le hℒ hg hP h x₀ hacc hG

/-- Strict decrease of a sufficiently accurate S-step: if moreover `0 < h` and
`G C h < (1 - βh/2) ‖Π∇ℒ(x₀)‖²`, then `ℒ(x₁) < ℒ(x₀)`. -/
theorem loss_perturbedStep_lt (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hP : IsOrthProj P) {h C G : ℝ} {x₀ x₁ : E}
    (hh : 0 < h) (hacc : ‖x₁ - projGradStep P g h x₀‖ ≤ C * h ^ 2)
    (hG : ∀ w ∈ segment ℝ (projGradStep P g h x₀) x₁, ‖g w‖ ≤ G)
    (hdom : G * C * h < (1 - β * h / 2) * ‖P (g x₀)‖ ^ 2) : ℒ x₁ < ℒ x₀ := by
  have h1 := loss_perturbedStep_le hℒ hg hP hacc hG
  have h2 := mul_lt_mul_of_pos_left hdom hh
  nlinarith

end SStep

/-! ### OP-TR-08: stochastic descent -/

section Stochastic

variable {Ξ : Type*} [Fintype Ξ] {ℒ : E → ℝ} {g : E → E} {β : ℝ}

/-- **Expected loss descent of truncated projected SGD** (OP-TR-08, one-step bound; corrects
arXiv 2410.18720 Thm 1 and arXiv 2502.03006 Thm 5.8): for unbiased minibatch gradients
`∑ p_ξ g_ξ = ∇ℒ(x)` with variance `∑ p_ξ ‖g_ξ - ∇ℒ(x)‖² ≤ σ²`, a projector `Π` independent of
`ξ`, and truncations `‖x₁(ξ) - (x - λ Π g_ξ)‖ ≤ ϑ` with `‖∇ℒ‖ ≤ G` in between,
`E ℒ(x₁) ≤ ℒ(x) - λ(1 - βλ/2) ‖Π∇ℒ(x)‖² + βλ²σ²/2 + G ϑ`. -/
theorem sum_loss_truncated_le_variance (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {P : E →L[ℝ] E} (hP : IsOrthProj P)
    {p : Ξ → ℝ} (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1) {gs : Ξ → E} {x : E}
    (hmean : ∑ ξ, p ξ • gs ξ = g x) (lr : ℝ) {σsq : ℝ}
    (hσ : ∑ ξ, p ξ * ‖gs ξ - g x‖ ^ 2 ≤ σsq) {x₁ : Ξ → E} {ϑ G : ℝ}
    (htr : ∀ ξ, ‖x₁ ξ - (x - lr • P (gs ξ))‖ ≤ ϑ)
    (hG : ∀ ξ, ∀ w ∈ segment ℝ (x - lr • P (gs ξ)) (x₁ ξ), ‖g w‖ ≤ G) :
    ∑ ξ, p ξ * ℒ (x₁ ξ) ≤
      ℒ x - lr * (1 - β * lr / 2) * ‖P (g x)‖ ^ 2 + β * lr ^ 2 / 2 * σsq + G * ϑ := by
  have h1 := sum_loss_sub_smul_apply_le_variance hℒ hg hβ hP hp hp1 hmean lr hσ
  have hstep : ∀ ξ ∈ Finset.univ, p ξ * ℒ (x₁ ξ) ≤ p ξ * ℒ (x - lr • P (gs ξ)) + p ξ * (G * ϑ) := by
    intro ξ _
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (loss_truncated_le hℒ le_rfl (htr ξ) (hG ξ)) (hp ξ)
  have h2 := sum_le_sum hstep
  rw [sum_add_distrib, ← sum_mul, hp1, one_mul] at h2
  linarith

/-- **The variance term is necessary** (OP-TR-08: the published proofs, which use the same
minibatch in the step and in the descent lemma, effectively drop it).  For `ℒ(x) = x²/2` on `ℝ`
(`β = 1`, `Π = 1`) at `x = 0`, with the unbiased samples `g_ξ = ±1` (probability `1/2` each),
every nonzero step `λ` strictly *increases* the expected loss, while the variance-free bound
would claim `E ℒ(x₁) ≤ ℒ(0) - λ(1 - λ/2) ‖∇ℒ(0)‖² = 0`. -/
theorem variance_term_necessary {lr : ℝ} (hlr : lr ≠ 0) :
    ∑ ξ : Bool, (1 / 2 : ℝ) • (if ξ then (1 : ℝ) else -1) = 0 ∧
    ‖(0 : ℝ)‖ ^ 2 / 2 - lr * (1 - 1 * lr / 2) * ‖(1 : ℝ →L[ℝ] ℝ) 0‖ ^ 2 <
      ∑ ξ : Bool, (1 / 2 : ℝ) *
        (‖(0 : ℝ) - lr • (1 : ℝ →L[ℝ] ℝ) (if ξ then (1 : ℝ) else -1)‖ ^ 2 / 2) := by
  refine ⟨by simp, ?_⟩
  norm_num [Fintype.sum_bool]
  positivity

/-- **Robbins–Monro convergence of the expected projected gradient** (OP-TR-08, second claim,
in expectation form): if the expected losses `a_k = E ℒ(W_k)` and the expected squared
projected gradients `b_k = E ‖Π_k ∇ℒ(W_k)‖²` satisfy the unconditional one-step bound
`a_{k+1} ≤ a_k - λ_k(1 - βλ_k/2) b_k + βλ_k²σ²/2 + G ϑ_k` (obtained from
`sum_loss_truncated_le_variance` conditionally on the past and the tower property — this
passage is not formalized here), `a_k ≥ a_inf`, `∑ λ_k = ∞`, `∑ λ_k² < ∞`, `β λ_k ≤ 2` and
`∑ ϑ_k ≤ D`, then `liminf_k b_k = 0`: `b_k < ε` for infinitely many `k`. -/
theorem frequently_lt_of_expected_descent {a b lr ϑ : ℕ → ℝ} {β σsq G D ainf : ℝ}
    (hβ : 0 ≤ β) (hσ : 0 ≤ σsq) (hG : 0 ≤ G) (hb : ∀ k, 0 ≤ b k)
    (hrec : ∀ k, a (k + 1) ≤
      a k - lr k * (1 - β * lr k / 2) * b k + β * σsq / 2 * lr k ^ 2 + G * ϑ k)
    (hD : ∀ n, ∑ k ∈ range n, ϑ k ≤ D) (hinf : ∀ k, ainf ≤ a k) (hlr0 : ∀ k, 0 ≤ lr k)
    (hlr2 : ∀ k, β * lr k ≤ 2) (hdiv : ¬ Summable lr) (hsq : Summable fun k => lr k ^ 2)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) : ∃ k, N ≤ k ∧ b k < ε := by
  have hw : ∀ k, 0 ≤ lr k * (1 - β * lr k / 2) := fun k =>
    mul_nonneg (hlr0 k) (by linarith [hlr2 k])
  have hwdiv : ¬ Summable fun k => lr k * (1 - β * lr k / 2) := by
    intro hs
    apply hdiv
    have e : lr = fun k => lr k * (1 - β * lr k / 2) + β / 2 * lr k ^ 2 := by
      funext k; ring
    rw [e]
    exact hs.add (hsq.mul_left (β / 2))
  refine exists_lt_of_sum_mul_le hw hb hwdiv
    (C := a 0 - ainf + β * σsq / 2 * ∑' k, lr k ^ 2 + G * D) (fun n => ?_) hε N
  have hstep : ∀ k, lr k * (1 - β * lr k / 2) * b k ≤
      a k - a (k + 1) + (β * σsq / 2 * lr k ^ 2 + G * ϑ k) := fun k => by linarith [hrec k]
  have hs := sum_le_of_le_sub_add hstep n
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hs
  have h1 := hinf n
  have h2 : G * ∑ k ∈ range n, ϑ k ≤ G * D := mul_le_mul_of_nonneg_left (hD n) hG
  have h3 : β * σsq / 2 * ∑ k ∈ range n, lr k ^ 2 ≤ β * σsq / 2 * ∑' k, lr k ^ 2 :=
    mul_le_mul_of_nonneg_left (hsq.sum_le_tsum _ fun k _ => sq_nonneg _) (by positivity)
  linarith

end Stochastic

/-! ### Online projected gradient with perturbed gradients (arXiv 2009.03887, Thm 1) -/

section Regret

/-- Telescoping with nonincreasing positive weights: if `A_t ≤ D²` and `η_t > 0` is
nonincreasing, `∑_{t ≤ T} (A_t - A_{t+1}) / η_t ≤ (D² - A_{T+1}) / η_T`. -/
lemma sum_sub_div_le {A η : ℕ → ℝ} {Dsq : ℝ} (hAD : ∀ t, A t ≤ Dsq)
    (hη : ∀ t, 0 < η t) (hanti : ∀ t, η (t + 1) ≤ η t) (T : ℕ) :
    ∑ t ∈ range (T + 1), (A t - A (t + 1)) / η t ≤ (Dsq - A (T + 1)) / η T := by
  induction T with
  | zero =>
    simp only [zero_add, sum_range_one]
    exact div_le_div_of_nonneg_right (by linarith [hAD 0]) (hη 0).le
  | succ T ih =>
    rw [sum_range_succ]
    have h1 : (Dsq - A (T + 1)) / η T ≤ (Dsq - A (T + 1)) / η (T + 1) :=
      div_le_div_of_nonneg_left (by linarith [hAD (T + 1)]) (hη _) (hanti T)
    have e : (Dsq - A (T + 1)) / η (T + 1) + (A (T + 1) - A (T + 1 + 1)) / η (T + 1) =
        (Dsq - A (T + 1 + 1)) / η (T + 1) := by rw [← add_div]; ring_nf
    linarith

/-- **Regret of online projected gradient descent with perturbed (low-rank) gradients**
(arXiv 2009.03887, Appendix A, inequality (12)).  Let `proj` be nonexpansive towards the
comparator `w⋆` (true for the metric projection onto a closed convex set containing `w⋆`), the
iterates stay within `D` of `w⋆`, the losses satisfy the strong-convexity inequality (8)
`f_t(w_t) - f_t(w⋆) ≤ ⟪g_t, w_t - w⋆⟫ - (c/2) ‖w_t - w⋆‖²`, the gradient perturbations satisfy
the sufficient condition (15) `‖g̃_t - g_t‖ ≤ (c/2) ‖w_t - w⋆‖`, `‖g̃_t‖ ≤ G + E`, and the step
sizes `η_t > 0` are nonincreasing.  Then over `T + 1` rounds
`R ≤ D² / (2 η_T) + (G + E)²/2 · ∑_{t ≤ T} η_t`. -/
theorem regret_le_of_perturbed {f : ℕ → E → ℝ} {w gr gt : ℕ → E} {wstar : E} {proj : E → E}
    {η : ℕ → ℝ} {c D G Eb : ℝ} (hproj : ∀ u, ‖proj u - wstar‖ ≤ ‖u - wstar‖)
    (hw : ∀ t, w (t + 1) = proj (w t - η t • gt t)) (hD : ∀ t, ‖w t - wstar‖ ≤ D)
    (hsc : ∀ t, f t (w t) - f t wstar ≤ ⟪gr t, w t - wstar⟫ - c / 2 * ‖w t - wstar‖ ^ 2)
    (hε : ∀ t, ‖gt t - gr t‖ ≤ c / 2 * ‖w t - wstar‖) (hgt : ∀ t, ‖gt t‖ ≤ G + Eb)
    (hη : ∀ t, 0 < η t) (hanti : ∀ t, η (t + 1) ≤ η t) (T : ℕ) :
    ∑ t ∈ range (T + 1), (f t (w t) - f t wstar) ≤
      D ^ 2 / (2 * η T) + (G + Eb) ^ 2 / 2 * ∑ t ∈ range (T + 1), η t := by
  set A : ℕ → ℝ := fun t => ‖w t - wstar‖ ^ 2 with hAdef
  have hstep : ∀ t, f t (w t) - f t wstar ≤
      (A t - A (t + 1)) / η t / 2 + (G + Eb) ^ 2 / 2 * η t := by
    intro t
    set v := w t - wstar
    -- step 1: the perturbed gradient still controls the regret term
    have h1 : f t (w t) - f t wstar ≤ ⟪gt t, v⟫ := by
      have hc : ⟪gr t - gt t, v⟫ ≤ c / 2 * ‖v‖ * ‖v‖ :=
        (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
          (by rw [norm_sub_rev]; exact hε t) (norm_nonneg _))
      rw [inner_sub_left] at hc
      have := hsc t
      nlinarith
    -- step 2: the projected step
    have h2 : A (t + 1) ≤ A t - 2 * η t * ⟪gt t, v⟫ + η t ^ 2 * (G + Eb) ^ 2 := by
      have hp := hproj (w t - η t • gt t)
      rw [← hw t] at hp
      have e : w t - η t • gt t - wstar = v - η t • gt t := by simp only [v]; abel
      rw [e] at hp
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hp 2
      rw [norm_sub_sq_real v (η t • gt t), inner_smul_right, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs, real_inner_comm] at hsq
      have hg2 : ‖gt t‖ ^ 2 ≤ (G + Eb) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hgt t) 2
      have := mul_le_mul_of_nonneg_left hg2 (sq_nonneg (η t))
      simp only [hAdef]
      linarith
    have hηt := hη t
    have h3 : ⟪gt t, v⟫ ≤ (A t - A (t + 1)) / η t / 2 + (G + Eb) ^ 2 / 2 * η t := by
      rw [show (A t - A (t + 1)) / η t / 2 + (G + Eb) ^ 2 / 2 * η t =
        ((A t - A (t + 1)) + η t ^ 2 * (G + Eb) ^ 2) / (2 * η t) by field_simp,
        le_div_iff₀ (by positivity)]
      linarith
    linarith
  have hsum := sum_le_sum fun t (_ : t ∈ range (T + 1)) => hstep t
  rw [sum_add_distrib, ← mul_sum, ← sum_div] at hsum
  have htel := sum_sub_div_le (A := A) (η := η) (Dsq := D ^ 2)
    (fun t => pow_le_pow_left₀ (norm_nonneg _) (hD t) 2) hη hanti T
  have hA : 0 ≤ A (T + 1) := sq_nonneg _
  have h4 : (D ^ 2 - A (T + 1)) / η T ≤ D ^ 2 / η T :=
    div_le_div_of_nonneg_right (by linarith) (hη T).le
  have e : D ^ 2 / (2 * η T) = D ^ 2 / η T / 2 := by rw [div_div, mul_comm]
  rw [e]
  linarith

/-- `∑_{t ≤ T} 1/√(t+1) ≤ 2 √(T+1) - 1` (Zinkevich 2003, used in arXiv 2009.03887). -/
lemma sum_inv_sqrt_le (T : ℕ) :
    ∑ t ∈ range (T + 1), 1 / √((t : ℝ) + 1) ≤ 2 * √((T : ℝ) + 1) - 1 := by
  induction T with
  | zero => norm_num
  | succ T ih =>
    rw [sum_range_succ]
    push_cast
    set a := √((T : ℝ) + 1)
    set b := √((T : ℝ) + 1 + 1)
    have ha : 0 ≤ a := Real.sqrt_nonneg _
    have hb : 0 < b := Real.sqrt_pos.2 (by positivity)
    have ha2 : a ^ 2 = (T : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hb2 : b ^ 2 = (T : ℝ) + 1 + 1 := Real.sq_sqrt (by positivity)
    have key : 1 / b ≤ 2 * b - 2 * a := by
      rw [div_le_iff₀ hb]
      nlinarith [sq_nonneg (a - b)]
    linarith

/-- **Theorem 1 of arXiv 2009.03887** (sublinear regret of LRT-based SGD): with
`η_t = 1/√(t+1)`, under the hypotheses of `regret_le_of_perturbed`, after `T + 1` rounds
`R ≤ (D²/2) √(T+1) + (G + E)² (√(T+1) - 1/2)`. -/
theorem regret_le_sqrt {f : ℕ → E → ℝ} {w gr gt : ℕ → E} {wstar : E} {proj : E → E}
    {c D G Eb : ℝ} (hproj : ∀ u, ‖proj u - wstar‖ ≤ ‖u - wstar‖)
    (hw : ∀ t, w (t + 1) = proj (w t - (1 / √((t : ℝ) + 1)) • gt t))
    (hD : ∀ t, ‖w t - wstar‖ ≤ D)
    (hsc : ∀ t, f t (w t) - f t wstar ≤ ⟪gr t, w t - wstar⟫ - c / 2 * ‖w t - wstar‖ ^ 2)
    (hε : ∀ t, ‖gt t - gr t‖ ≤ c / 2 * ‖w t - wstar‖) (hgt : ∀ t, ‖gt t‖ ≤ G + Eb) (T : ℕ) :
    ∑ t ∈ range (T + 1), (f t (w t) - f t wstar) ≤
      D ^ 2 / 2 * √((T : ℝ) + 1) + (G + Eb) ^ 2 * (√((T : ℝ) + 1) - 1 / 2) := by
  have hη : ∀ t : ℕ, 0 < 1 / √((t : ℝ) + 1) := fun t =>
    one_div_pos.2 (Real.sqrt_pos.2 (by positivity))
  have hanti : ∀ t : ℕ, 1 / √(((t + 1 : ℕ) : ℝ) + 1) ≤ 1 / √((t : ℝ) + 1) := fun t => by
    apply one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity))
    exact Real.sqrt_le_sqrt (by push_cast; linarith)
  have h := regret_le_of_perturbed (η := fun t : ℕ => 1 / √((t : ℝ) + 1)) hproj hw hD hsc hε
    hgt hη hanti T
  have hs := sum_inv_sqrt_le T
  have hsq : 0 < √((T : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have e : D ^ 2 / (2 * (1 / √((T : ℝ) + 1))) = D ^ 2 / 2 * √((T : ℝ) + 1) := by
    field_simp
  rw [e] at h
  have h2 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (G + Eb) ^ 2 / 2)
  linarith

end Regret

/-! ### Non-degenerate instances -/

section Examples

/-- The hypotheses of `exists_projGrad_sq_le_of_inexact` are satisfiable with a nonzero
gradient error: `ℒ = x²/2` on `ℝ`, `β = h = η = 1`, `x_k = -1` and the (wrong) gradient
surrogate `g̃_k = 0`, whose error is `1` at every step. -/
example {n : ℕ} (hn : 0 < n) :
    ∃ k < n, ‖(1 : ℝ →L[ℝ] ℝ) (id ((fun _ : ℕ => (-1 : ℝ)) k))‖ ^ 2 ≤
      2 * (‖(-1 : ℝ)‖ ^ 2 / 2 - 0) / (n * 1) + 1 ^ 2 :=
  exists_projGrad_sq_le_of_inexact (ℒ := fun x : ℝ => ‖x‖ ^ 2 / 2) (g := id) (β := 1)
    (P := fun _ => 1) (x := fun _ => -1) (gt := fun _ => 0) (h := 1) (η := 1) (ℒinf := 0)
    hasFDerivAt_half_norm_sq (fun x y => by simp) (fun _ => IsOrthProj.one) one_pos
    (by norm_num) (fun _ => by simp) (fun _ => by simp) (fun _ => by positivity) hn

/-- The hypotheses of `exists_armijo_backtracking` are satisfiable with genuinely inexact data:
`ℒ = x²/2` on `ℝ` observed through `ℒ̃ = ℒ + δ cos` (`δ = 1/100`), at `x = 1` with the inexact
direction `d = 9/8` (`η = 1/8`), `c = 1/2`, `β = 1`, `s₀ = 1`. -/
example : ∃ j : ℕ, ArmijoTest (fun y : ℝ => ‖y‖ ^ 2 / 2 + 1 / 100 * Real.cos y) (1 / 2) 1 (9 / 8)
      (1 * (1 / 2) ^ j) :=
  let ⟨j, hj, _⟩ := exists_armijo_backtracking (ℒ := fun x : ℝ => ‖x‖ ^ 2 / 2) (g := id)
    (β := 1) (η := 1 / 8) (δ := 1 / 100) hasFDerivAt_half_norm_sq (fun x y => by simp)
    one_pos one_pos (by norm_num) (by norm_num [Real.norm_eq_abs, abs_of_pos])
    (fun y => by
      simp only [add_sub_cancel_left, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 100)]
      exact mul_le_of_le_one_right (by norm_num) (Real.abs_cos_le_one y))
    (by norm_num [Real.norm_eq_abs]) (by norm_num [Real.norm_eq_abs])
    (by norm_num [Real.norm_eq_abs])
  ⟨j, hj⟩

/-- The hypotheses of `regret_le_of_perturbed` are satisfiable with a nonzero gradient
perturbation: `f_t = ‖w‖²/2` on `ℝ` (`c = 1`, `w⋆ = 0`), `g̃_t = g_t / 2` (so
`‖g̃_t - g_t‖ = ‖w_t‖ / 2`, the boundary case of condition (15)), `η_t = 2`, `proj = id`. -/
example (T : ℕ) :
    ∑ t ∈ range (T + 1), ((fun _ (w : ℝ) => ‖w‖ ^ 2 / 2) t
        ((fun t : ℕ => if t = 0 then (1 : ℝ) else 0) t) -
      (fun _ (w : ℝ) => ‖w‖ ^ 2 / 2) t 0) ≤
      1 ^ 2 / (2 * (fun _ : ℕ => (2 : ℝ)) T) +
        (1 / 2 + 0) ^ 2 / 2 * ∑ t ∈ range (T + 1), (fun _ : ℕ => (2 : ℝ)) t :=
  regret_le_of_perturbed (f := fun _ (w : ℝ) => ‖w‖ ^ 2 / 2)
    (w := fun t : ℕ => if t = 0 then (1 : ℝ) else 0) (wstar := 0) (η := fun _ => 2) (D := 1)
    (G := 1 / 2) (Eb := 0) (gr := fun t : ℕ => if t = 0 then (1 : ℝ) else 0)
    (gt := fun t : ℕ => (1 / 2 : ℝ) • (if t = 0 then (1 : ℝ) else 0)) (proj := id) (c := 1)
    (fun u => le_rfl) (fun t => by rcases t with _ | t <;> norm_num)
    (fun t => by rcases t with _ | t <;> norm_num) (fun t => by rcases t with _ | t <;> norm_num)
    (fun t => by rcases t with _ | t <;> norm_num) (fun t => by rcases t with _ | t <;> norm_num)
    (fun _ => two_pos) (fun _ => le_rfl) T

end Examples

end LeanDLRA.InexactGradient
