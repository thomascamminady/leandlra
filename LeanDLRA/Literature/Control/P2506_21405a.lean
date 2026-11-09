import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2506.21405: Adaptive DLR optimizer for kinetic parameter identification

This module formalizes the discrete adjoint consistency of the explicit Euler forward and backward
schemes of arXiv 2506.21405, Sec. 3.3, eqs. (19)–(20), in the abstract form that the paper's
stencils instantiate: for a linear generator `L` on a real inner product space, with forward Euler
`u^{n+1} = u^n + Δt L u^n` and backward Euler `w^n = w^{n+1} + Δt L† w^{n+1}` (where `L†` is the
Mathlib adjoint), the pairing `⟪w^n, u^n⟫` is constant in `n`. The paper does not state this
identity; it is the discrete counterpart of the duality between the forward problem (3) and the
adjoint problem (5). Nothing is claimed here about the gradient formula (21).

**Proved (new):**
* `euler_adjoint_inner_step`: one-step identity `⟪w^n, u^n⟫ = ⟪w^{n+1}, u^{n+1}⟫`.
* `euler_adjoint_inner_const`: the telescoped form, `⟪w^n, u^n⟫ = ⟪w^N, u^N⟫` for all `n ≤ N`.
* `euler_adjoint_example`: non-vacuity, the recursions hold for `L = c • id` on `ℝ` with `N = 1`.

**Abstraction and differences from the paper.** The paper's operator (19)–(20) acts on the
coefficient arrays `u_{jkm}`, `w_{jkm}` with the centred stencils `D^x`, `D^{xx}`, the matrices
`A`, `|A|`, `E`, and the cross section `σ_j`. Here these are replaced by one linear map `L`,
and the paper's backward operator is the adjoint `L†`. Eq. (20) uses the same stencils as (19)
with the sign of the `D^x` term flipped; it is the adjoint of (19) because the periodic `D^x` is
antisymmetric and `D^{xx}`, `A`, `|A|` are symmetric. That check is NOT formalized: the theorems
apply to any `L`, and the paper's specific `L` is an instance only once it is verified. The time
index runs over `ℕ` with the forward and the backward recursion on `n < N`, matching the time
cells `t_0, …, t_{N_t}`.

**Core definitions used.** Only Mathlib's `ContinuousLinearMap.adjoint` and the real inner product
are used. No local definitions are added.

**Already in the library (not duplicated).**
* Algorithm 2 (backtracking line search with Armijo condition, Sec. 4.2): `ArmijoTest`,
  `armijoTest_of_le`, `exists_armijo_backtracking` in `LeanDLRA/Training/InexactGradient.lean`,
  which cite arXiv 2506.21405 Alg. 2. The paper's parameter update
  `θ = max(h₁, min(h₂, η h₃ ‖∇J‖_∞))` and the reduction factor `p` are not formalized there.
* Augmented BUG with truncation to tolerance `ϑ` (Sec. 4.1–4.2): `IsRankAdaptiveBUGStep`,
  `rankAdaptiveBUG_global_error` in `LeanDLRA/Integrators/RankAdaptiveBUG.lean`. The paper's
  concrete factor recursions (24a)–(24c) and the adjoint version are not formalized.

**Not formalized, and why.**
* Sec. 2.1–2.2: the continuous Lagrangian, the adjoint PDE (5), and the gradient identities (6)–(7)
  and (10) need the PDE in weak or classical form, which the library does not have; left out.
* Sec. 3.1–3.2 and eqs. (11)–(18): the Legendre expansion, the centred finite-difference stencils
  and the spatial discretization of the gradient are concrete-operator computations; left out.
* Eq. (21) and Algorithm 1 (the fully discrete gradient and descent loop): the gradient formula
  and the convergence claims were not proved here; only the adjoint consistency above is.
* Sec. 5 numerical results: not mathematical claims; left out.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2506_21405

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **One-step discrete adjoint identity (arXiv 2506.21405, Sec. 3.3, eqs. (19)–(20)).**
If `u` solves the explicit Euler step `u^{n+1} = u^n + Δt L u^n` (eq. (19) abstracted to a linear
generator `L`) and `w` solves the backward explicit Euler step `w^n = w^{n+1} + Δt L† w^{n+1}`
(eq. (20) abstracted, with `L†` the Mathlib adjoint in place of the paper's transposed stencils),
then `⟪w^n, u^n⟫ = ⟪w^{n+1}, u^{n+1}⟫`. The paper does not state this identity. -/
theorem euler_adjoint_inner_step (L : E →L[ℝ] E) (dt : ℝ) (u w : ℕ → E) (n : ℕ)
    (hu : u (n + 1) = u n + dt • L (u n))
    (hw : w n = w (n + 1) + dt • ContinuousLinearMap.adjoint L (w (n + 1))) :
    ⟪w n, u n⟫ = ⟪w (n + 1), u (n + 1)⟫ := by
  rw [hu, hw, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    ContinuousLinearMap.adjoint_inner_left]

/-- **Discrete adjoint consistency over the whole time grid (arXiv 2506.21405, Sec. 3.3).**
With `N` time cells, forward Euler `u^{n+1} = u^n + Δt L u^n` and backward Euler
`w^n = w^{n+1} + Δt L† w^{n+1}` for `n < N`, the pairing is constant:
`⟪w^n, u^n⟫ = ⟪w^N, u^N⟫` for every `n ≤ N`. Not stated in the paper (see the module docstring). -/
theorem euler_adjoint_inner_const (L : E →L[ℝ] E) (dt : ℝ) (N : ℕ) (u w : ℕ → E)
    (hu : ∀ n < N, u (n + 1) = u n + dt • L (u n))
    (hw : ∀ n < N, w n = w (n + 1) + dt • ContinuousLinearMap.adjoint L (w (n + 1))) :
    ∀ n ≤ N, ⟪w n, u n⟫ = ⟪w N, u N⟫ := by
  have key : ∀ m, m ≤ N → ⟪w (N - m), u (N - m)⟫ = ⟪w N, u N⟫ := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have hlt : N - (m + 1) < N := by omega
      have hs : N - (m + 1) + 1 = N - m := by omega
      have h2 := euler_adjoint_inner_step L dt u w (N - (m + 1)) (hu _ hlt) (hw _ hlt)
      rw [hs] at h2
      rw [h2]
      exact h1
  intro n hn
  have h := key (N - n) (Nat.sub_le N n)
  rwa [Nat.sub_sub_self hn] at h

/-- **Non-vacuity of the adjoint recursions (arXiv 2506.21405, Sec. 3.3).** For `L = c • id` on `ℝ`
and `N = 1`, the forward solution `u^n = (1 + Δt c)^n x` and the backward solution
`w^n = (1 + Δt c)^(1 - n) y` satisfy the recursion hypotheses of `euler_adjoint_inner_const`
(for `n < 1`). -/
theorem euler_adjoint_example (c dt x y : ℝ) :
    let L : ℝ →L[ℝ] ℝ := c • ContinuousLinearMap.id ℝ ℝ
    let u : ℕ → ℝ := fun n => (1 + dt * c) ^ n * x
    let w : ℕ → ℝ := fun n => (1 + dt * c) ^ (1 - n) * y
    (∀ n < 1, u (n + 1) = u n + dt • L (u n)) ∧
    (∀ n < 1, w n = w (n + 1) + dt • ContinuousLinearMap.adjoint L (w (n + 1))) := by
  intro L u w
  constructor
  · intro n hn
    obtain rfl : n = 0 := by omega
    simp [L, u]
    ring
  · intro n hn
    obtain rfl : n = 0 := by omega
    simp [L, w, ContinuousLinearMap.adjoint_id]
    ring

end LeanDLRA.Literature.P2506_21405
