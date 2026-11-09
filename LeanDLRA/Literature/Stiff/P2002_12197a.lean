import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Stiff.ImplicitSolvability

/-!
# Lemma 4.4 of arXiv 2002.12197: energy estimates for the Rothe scheme

Bounded-operator form of the discrete energy estimate (4.1) of Bachmayr, Eisenmann, Kieri and
Uschmajew for the backward-Euler (Rothe) scheme on a cone `M`. The time-discrete functional is the
paper's (3.3), `F(v) = ‖v - u_i‖² / (2h) + ½ a(v, v) - ⟪f, v⟫`, with the symmetric form written as
`a(u, v) = ⟪A u, v⟫` for a bounded self-adjoint operator `A` on `H` (the paper's `A(t)` maps
`V → V*` and need not be bounded on `H`). The paper's `V` is taken to be the ambient real inner
product space `E` (any dimension) with its inner product as `H`, and the `V`-norm is an abstract
function `ν` satisfying the paper's coercivity `a(u, u) ≥ μ ν(u)²` and dual bound
`⟪f, u⟫ ≤ φ ν(u)`.
Minimality of `u_{i+1}` over the cone `S` (assumption A1) gives the optimality identity (3.1) with
`v = u_{i+1}`. This identity is derived here from minimality (through the library's
`rothe_cone_optimality`), not assumed; it is then fed into `rothe_energy_step`, and the one-step
estimates are summed by `rothe_energy_sum`.

Proved: the optimality identity of the Rothe step (`rothe_optimality_of_minimizer`), its one-step
energy estimate (`rothe_energy_step_of_minimizer`), the telescoped estimate (4.1) for a whole
sequence (`rothe_energy_estimate`), and non-vacuity examples for the first and the last.

Core definitions used: `rothe_cone_optimality`, `rothe_energy_step`, `rothe_energy_sum`
(`LeanDLRA/Stiff/ImplicitSolvability.lean`). Local definition: `rotheFunctional`, the functional
(3.3) in this setting.

Left out: the estimates (4.2) and (4.3) of Lemma 4.4; the Sobolev, Bochner and `L²(0,T;H)`
setting (the paper's constant `C₁` becomes the explicit `h/μ` against the discrete `φᵢ`); the
parts of the paper's Problem 2.1 and the tangent-space formulation (3.1) beyond the minimisation
property used in the proof; the other results listed in the earlier version of this header
(Prop. 5.1, (2.6), Lemma A.2 and Cor. A.3, Theorem 4.1), which are not part of this slice.
-/

open scoped RealInnerProductSpace

namespace LeanDLRA.Literature.P2002_12197

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The time-discrete functional of arXiv 2002.12197, eq. (3.3), with `a(u, v) = ⟪A u, v⟫`:
`F(v) = ‖v - u₀‖² / (2h) + ½ a(v, v) - ⟪f, v⟫` (here `h` is the time step `t_{i+1} - t_i`). -/
noncomputable def rotheFunctional (A : E →L[ℝ] E) (f u₀ : E) (h : ℝ) (v : E) : ℝ :=
  ‖v - u₀‖ ^ 2 / (2 * h) + (⟪A v, v⟫ / 2 - ⟪f, v⟫)

/-- **Optimality identity of a Rothe step** (arXiv 2002.12197, proof of Lemma 4.4, eq. (3.1) with
`v = u_{i+1}`). Let `S` be a cone (assumption A1: `s • u ∈ S` for `u ∈ S`, `s > 0`), `A` a
self-adjoint bounded operator, `h > 0`, and let `u₁ ∈ S` minimise the functional (3.3) over `S`.
Then `⟪u₁ - u₀, u₁⟫ + h a(u₁, u₁) = h ⟪f, u₁⟫`. The identity is derived from minimality
(via `rothe_cone_optimality`), not assumed. -/
theorem rothe_optimality_of_minimizer {S : Set E} (hS : ∀ u ∈ S, ∀ s : ℝ, 0 < s → s • u ∈ S)
    {A : E →L[ℝ] E} (hA : ∀ u w : E, ⟪A u, w⟫ = ⟪u, A w⟫) {f u₀ u₁ : E} {h : ℝ} (hh : 0 < h)
    (hu₁ : u₁ ∈ S) (hmin : ∀ v ∈ S, rotheFunctional A f u₀ h u₁ ≤ rotheFunctional A f u₀ h v) :
    ⟪u₁ - u₀, u₁⟫ + h * ⟪A u₁, u₁⟫ = h * ⟪f, u₁⟫ := by
  set Ψ : E → ℝ := fun v => 1 / 2 * ⟪A v, v⟫ - ⟪f, v⟫ with hΨdef
  have hF : ∀ v, h * rotheFunctional A f u₀ h v = ‖v - u₀‖ ^ 2 / 2 + h * Ψ v := by
    intro v
    unfold rotheFunctional
    rw [hΨdef]
    field_simp
  have hmin' : ∀ v ∈ S, ‖u₁ - u₀‖ ^ 2 / 2 + h * Ψ u₁ ≤ ‖v - u₀‖ ^ 2 / 2 + h * Ψ v := by
    intro v hv
    rw [← hF, ← hF]
    exact mul_le_mul_of_nonneg_left (hmin v hv) hh.le
  have hq := (A.hasFDerivAt).inner ℝ (hasFDerivAt_id u₁)
  have hl : HasFDerivAt (fun v => ⟪f, v⟫) (innerSL ℝ f) u₁ := (innerSL ℝ f).hasFDerivAt
  have hΨd : HasFDerivAt Ψ (innerSL ℝ (A u₁ - f)) u₁ := by
    refine ((hq.const_mul (1 / 2 : ℝ)).sub hl).congr_fderiv ?_
    ext w
    have h3 : ⟪A w, u₁⟫ = ⟪A u₁, w⟫ := by rw [hA, real_inner_comm]
    simp only [one_div, id_eq, sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, fderivInnerCLM_apply,
      smul_eq_mul, coe_innerSL_apply, map_sub, sub_left_inj]
    rw [h3]
    ring
  have hopt := rothe_cone_optimality hS hu₁ hmin' hΨd
  have h2 : ⟪A u₁ - f, u₁⟫ = ⟪A u₁, u₁⟫ - ⟪f, u₁⟫ := inner_sub_left _ _ _
  rw [innerSL_apply_apply, h2] at hopt
  linear_combination hopt

/-- **One-step energy estimate of the Rothe scheme** (arXiv 2002.12197, proof of Lemma 4.4, the
estimate before the summation over `i`), with the optimality identity derived from minimality
rather than assumed. Here `ν` is the
`V`-norm, `μ > 0` the coercivity constant (`a(u, u) ≥ μ ν(u)²`), and `φ` bounds the dual
norm of `f` (`⟪f, u⟫ ≤ φ ν(u)`). Conclusion:
`‖u₁‖² - ‖u₀‖² + ‖u₁ - u₀‖² + h μ ν(u₁)² ≤ h φ² / μ`. -/
theorem rothe_energy_step_of_minimizer {S : Set E} (hS : ∀ u ∈ S, ∀ s : ℝ, 0 < s → s • u ∈ S)
    {A : E →L[ℝ] E} (hA : ∀ u w : E, ⟪A u, w⟫ = ⟪u, A w⟫) {f u₀ u₁ : E} {h μ φ : ℝ}
    {ν : E → ℝ} (hh : 0 < h) (hμ : 0 < μ) (hu₁ : u₁ ∈ S)
    (hmin : ∀ v ∈ S, rotheFunctional A f u₀ h u₁ ≤ rotheFunctional A f u₀ h v)
    (hcoer : ∀ w, μ * ν w ^ 2 ≤ ⟪A w, w⟫) (hdual : ∀ w, ⟪f, w⟫ ≤ φ * ν w) :
    ‖u₁‖ ^ 2 - ‖u₀‖ ^ 2 + ‖u₁ - u₀‖ ^ 2 + h * μ * ν u₁ ^ 2 ≤ h * φ ^ 2 / μ :=
  rothe_energy_step hh.le hμ (rothe_optimality_of_minimizer hS hA hh hu₁ hmin) (hcoer u₁)
    (hdual u₁)

/-- **Energy estimate (4.1) of the Rothe scheme** (arXiv 2002.12197, Lemma 4.4), for a sequence
`u i` of minimising-movement steps with uniform step `h > 0`. Step `i + 1` minimises the functional
(3.3) with time-dependent operator `A (i + 1)` and data `f (i + 1)` over the cone `S`, starting from
`u i`. The coercivity and dual-norm bounds hold at every step. Then for every `N`
`‖u_N‖² + Σ_{i<N} ‖u_{i+1} - u_i‖² + h μ Σ_{i<N} ν(u_{i+1})² ≤ ‖u₀‖² + (h/μ) Σ_{i<N} φ_{i+1}²`.
The constant is explicit (`h/μ` against the discrete `φ_{i+1}²`), and `u 0 ∈ S` is not needed. -/
theorem rothe_energy_estimate {S : Set E} (hS : ∀ u ∈ S, ∀ s : ℝ, 0 < s → s • u ∈ S)
    {A : ℕ → E →L[ℝ] E} (hA : ∀ (i : ℕ) (u w : E), ⟪A i u, w⟫ = ⟪u, A i w⟫) {f u : ℕ → E}
    {h μ : ℝ} {ν : E → ℝ} {φ : ℕ → ℝ} (hh : 0 < h) (hμ : 0 < μ) (hu : ∀ i, u (i + 1) ∈ S)
    (hmin : ∀ i, ∀ v ∈ S, rotheFunctional (A (i + 1)) (f (i + 1)) (u i) h (u (i + 1)) ≤
      rotheFunctional (A (i + 1)) (f (i + 1)) (u i) h v)
    (hcoer : ∀ (i : ℕ) (w : E), μ * ν w ^ 2 ≤ ⟪A (i + 1) w, w⟫)
    (hdual : ∀ (i : ℕ) (w : E), ⟪f (i + 1), w⟫ ≤ φ (i + 1) * ν w) (N : ℕ) :
    ‖u N‖ ^ 2 + ∑ i ∈ Finset.range N, ‖u (i + 1) - u i‖ ^ 2 +
        h * μ * ∑ i ∈ Finset.range N, ν (u (i + 1)) ^ 2 ≤
      ‖u 0‖ ^ 2 + h / μ * ∑ i ∈ Finset.range N, φ (i + 1) ^ 2 := by
  have hstep : ∀ i, ‖u (i + 1)‖ ^ 2 - ‖u i‖ ^ 2 + ‖u (i + 1) - u i‖ ^ 2 +
      h * μ * (fun j => ν (u j)) (i + 1) ^ 2 ≤ h * φ (i + 1) ^ 2 / μ := fun i =>
    rothe_energy_step_of_minimizer hS (hA (i + 1)) hh hμ (hu i) (hmin i) (hcoer i) (hdual i)
  exact rothe_energy_sum (v := fun j => ν (u j)) (φ := φ) (h := h) (μ := μ) hstep N

/-- Non-vacuity: on `E = ℝ` with `S = ℝ`, `A = id`, `f = 0`, `u₀ = 1`, `h = 1` the functional is
`(v - 1)²/2 + v²/2`, minimised at `u₁ = 1/2`, and the optimality identity holds there. -/
example : ⟪(1 / 2 : ℝ) - 1, (1 / 2 : ℝ)⟫ + 1 * ⟪ContinuousLinearMap.id ℝ ℝ (1 / 2 : ℝ), 1 / 2⟫ =
    1 * ⟪(0 : ℝ), 1 / 2⟫ :=
  rothe_optimality_of_minimizer (S := Set.univ) (fun _ _ _ _ => Set.mem_univ _)
    (A := ContinuousLinearMap.id ℝ ℝ) (fun _ _ => rfl) (f := 0) (u₀ := 1)
    (u₁ := 1 / 2) one_pos (Set.mem_univ _) fun v _ => by
      simp [rotheFunctional, RCLike.inner_apply, Real.norm_eq_abs, sq_abs]
      nlinarith [sq_nonneg (v - 1 / 2)]

/-- Non-vacuity of `rothe_energy_estimate`: on `E = ℝ` with `S = ℝ`, `A = id`, `f = 0`, `h = 1`,
`μ = 1`, `ν = id` and `φ = 0`, the halving sequence `u i = (1/2)^i` consists of minimisers of the
functional (3.3), so all hypotheses hold. -/
example (N : ℕ) :
    ‖((1 / 2 : ℝ) ^ N)‖ ^ 2 + ∑ i ∈ Finset.range N, ‖(1 / 2 : ℝ) ^ (i + 1) - (1 / 2) ^ i‖ ^ 2 +
        1 * 1 * ∑ i ∈ Finset.range N, id ((1 / 2 : ℝ) ^ (i + 1)) ^ 2 ≤
      ‖((1 / 2 : ℝ) ^ 0)‖ ^ 2 + 1 / 1 * ∑ i ∈ Finset.range N, (fun _ : ℕ => (0 : ℝ)) (i + 1) ^ 2 :=
  rothe_energy_estimate (S := Set.univ) (fun _ _ _ _ => Set.mem_univ _)
    (A := fun _ => ContinuousLinearMap.id ℝ ℝ) (fun _ _ _ => rfl) (f := fun _ => 0)
    (u := fun i => (1 / 2 : ℝ) ^ i) (ν := id) (φ := fun _ => 0) one_pos one_pos
    (fun _ => Set.mem_univ _)
    (fun i v _ => by
      have e : (1 / 2 : ℝ) ^ (i + 1) = (1 / 2) ^ i / 2 := by rw [pow_succ]; ring
      simp only [rotheFunctional, ContinuousLinearMap.id_apply, RCLike.inner_apply, conj_trivial,
        Real.norm_eq_abs, sq_abs, e]
      nlinarith [sq_nonneg (v - (1 / 2 : ℝ) ^ i / 2)])
    (fun _ w => by simp [sq])
    (fun _ w => by simp) N

end LeanDLRA.Literature.P2002_12197
