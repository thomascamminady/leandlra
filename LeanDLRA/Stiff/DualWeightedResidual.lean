import LeanDLRA.Stiff.ImplicitBUG
import LeanDLRA.Stability.Conservation

/-!
# Dual-weighted residual identities for low-rank implicit Euler steps

Setting: a linear, possibly time-dependent problem `Ȧ = 𝓛(t) A + q(t)` (nonlinear problems: see
the section on the linearisation remainder) discretised by the
**full-rank implicit Euler scheme** `A_{k+1} - h 𝓛_k A_{k+1} = A_k + h q_k` (the reference), and
**any** sequence `Y_k` (a low-rank integrator: implicit BUG, merged step-truncation, a Krylov
solve with truncation, ...).  Two computable quantities:

* the primal residual `R_k = Y_{k+1} - Y_k - h (𝓛_k Y_{k+1} + q_k)`,
* for any sequence `ψ_k` (a low-rank approximation of the discrete adjoint solution), the dual
  residual `ρ_k = ψ_k - h 𝓛'_k ψ_k - ψ_{k+1}`.

Main results.  None of them has a rank, singular-value gap, curvature or smoothness hypothesis.
The identities need no hypothesis beyond adjointness; the bounds use a one-sided bound
`⟪𝓛_k x, x⟫ ≤ ℓ ‖x‖²` with `h ℓ < 1`; the efficiency and enrichment lemmas use a Lipschitz, resp.
one-sided Lipschitz, inequality at the pair of points that occurs.

* `inner_eq_sum_inner_defect`: summation by parts against a dual sequence, the common kernel of
  the identities below.
* `primalDual_error_identity`: the exact identity
  `⟪ψ_N, Y_N - A_N⟫ = ⟪ψ_0, Y_0 - A_0⟫ + ∑ ⟪ψ_k, R_k⟫ - ∑ ⟪ρ_k, Y_{k+1} - A_{k+1}⟫`.
* `dual_error_representation`: for the exact discrete adjoint (`ρ = 0`) the output error is the
  dual-weighted residual sum, with no remainder.
* `corrected_output_error`, `abs_corrected_output_sub_le`: the adjoint-corrected output
  `⟪ψ_N, Y_N⟫ - ∑ ⟪ψ_k, R_k⟫` has error at most
  `‖ψ_0‖ ‖e_0‖ + ∑ ‖ρ_k‖ aᵏ⁺¹ (‖e_0‖ + ∑_{j ≤ k} ‖R_j‖)` with `e_0 = Y_0 - A_0` and
  `a = max 1 (1 - h ℓ)⁻¹`: a sum of **products** of dual and primal residuals
  (`abs_corrected_output_sub_le_of_dissipative`: `a = 1` for `ℓ ≤ 0`).
* `primalDual_error_identity_of_linearization`, `corrected_output_error_of_linearization`,
  `abs_corrected_output_sub_le_of_linearization`: the same for a **nonlinear** problem
  `Ȧ = F(t, A)` and any linearisation `𝓛_k`; the identity gains the term `h ∑ ⟪ψ_k, r_k⟫` with the
  linearisation remainder `r_k = F_k(Y_{k+1}) - F_k(A_{k+1}) - 𝓛_k e_{k+1}`, and for
  `‖r_k‖ ≤ M ‖e_{k+1}‖²` the corrected output has error at most
  `‖ψ_0‖ E_0 + ∑ ‖ρ_k‖ E_{k+1} + h M ∑ ‖ψ_k‖ E_{k+1}²` for any primal certificate `E`
  (`norm_sub_nonlinear_reference_le`).  Quadratic fields (Riccati, Burgers, Vlasov–Poisson)
  satisfy the remainder hypothesis: `norm_quadratic_linearization_remainder_le`.
* `inner_galerkin_residual_eq_zero`, `galerkin_output_error`: if the step is a Galerkin step in a
  space that contains the dual iterate, the correction vanishes and the plain output already has
  the product accuracy (no `1 / σ_r`).
* `IsImplicitBUGStep.inner_sstep_residual_eq_zero`,
  `IsImplicitBUGStep.inner_residual_eq_truncation`, `IsImplicitBUGStep.abs_inner_residual_le`:
  for an implicit BUG step whose bases contain the dual iterate, the dual-weighted residual of
  the Galerkin stage is zero, and that of the truncated step is `⟪ψ - h 𝓛' ψ, Y₁ - xS⟫`, at most
  `‖ψ - h 𝓛' ψ‖ ϑ`.
* `dualConsistent_balance`, `dualConsistent_output_error`, `abs_dualConsistent_output_error_le`:
  if in addition the truncation keeps the pairing with the next dual iterate
  (`⟪ψ_{k+1}, Y_{k+1} - X_k⟫ = 0`, **dual-consistent truncation**), the truncation tolerance
  leaves the output error altogether: `⟪ψ_N, e_N⟫ = ⟪ψ_0, e_0⟫ - ∑ ⟪ρ_k, X_k - A_{k+1}⟫` with the
  Galerkin stages `X_k`.  `inner_consTrunc_sub_eq_zero`: the conservative truncation `consTrunc`
  with respect to directions that contain `ψ_{k+1}` is dual-consistent;
  `implicitBUG_dualConsistent_output_error` is the statement for implicit BUG steps.
* `dualConsistent_inner_eq`, `dualConsistent_output_error_of_dual`,
  `dualConsistent_inner_eq_of_stationary`: for the exact discrete adjoint the integrator has the
  balance law `⟪ψ_N, Y_N⟫ = ⟪ψ_0, Y_0⟫ + h ∑ ⟪ψ_k, q_k⟫` of the full-rank scheme for every rank and
  tolerance; conservation of a linear invariant is the stationary case `𝓛' c = 0`.
* `implicitEuler_residual_le`: efficiency of the residual (it is bounded by the errors), the
  converse of `implicitEuler_stability`.
* `enrichment_step_sub_le`, `enrichment_defect_le`, `norm_sq_enrichment_split`: enlarging the
  Galerkin space from `P` to `P' ≥ P` moves the step by at most the captured defect and leaves
  the defect `‖(1 - P') w‖ + h L / (1 - h ℓ) ‖(1 - P) w‖`.

The primal certificate against the exact solution is `residual_global_error` (OP-ST-04); the
continuous weak-error identity is `Novel.OpOT60`.

## Relation to the literature

The mechanism is classical and no novelty is claimed for it: dual-weighted residual error
representations (Becker and Rannacher, Acta Numerica 10, 2001), adjoint correction of output
functionals (Pierce and Giles, SIAM Review 42, 2000), and primal–dual output bounds for reduced
bases.  The statements here are formulated for arbitrary sequences `Y` and `ψ`, with the full-rank
implicit Euler sequence as reference, so that they apply to every low-rank integrator and to every
low-rank approximation of the discrete adjoint.  `inner_galerkin_residual_eq_zero` is the form for
Galerkin steps of BUG type: a basis that is enriched by the dual iterate makes the correction
vanish.  The dual-consistent truncation is the conservative truncation of Einkemmer, Ostermann
and Scalone (arXiv 2206.09374; `consTrunc` in `Stability/Conservation.lean`) with the dual
iterate in place of the conserved directions: conserved quantities are stationary adjoint
solutions, and a time-dependent adjoint solution is kept in the same way.
-/

open Set Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The primal–dual error identity -/

section PrimalDual

variable {𝓛 𝓛' : ℕ → E →ₗ[ℝ] E} {h : ℝ} {N : ℕ} {A Y ψ q : ℕ → E}

/-- **Summation by parts against a dual sequence.**  If `e_{k+1} - h 𝓛_k e_{k+1} = e_k + d_k`
and `𝓛' k` is adjoint to `𝓛 k`, then for **any** sequence `ψ`, with
`ρ_k = ψ_k - h 𝓛'_k ψ_k - ψ_{k+1}`,
`⟪ψ_n, e_n⟫ = ⟪ψ_0, e_0⟫ + ∑_{k<n} ⟪ψ_k, d_k⟫ - ∑_{k<n} ⟪ρ_k, e_{k+1}⟫`. -/
theorem inner_eq_sum_inner_defect {e d : ℕ → E} (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (he : ∀ k < N, e (k + 1) - h • 𝓛 k (e (k + 1)) = e k + d k) :
    ∀ n ≤ N, ⟪ψ n, e n⟫ = ⟪ψ 0, e 0⟫ + ∑ k ∈ range n, ⟪ψ k, d k⟫
      - ∑ k ∈ range n, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), e (k + 1)⟫ := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hn' : n < N := by omega
    have hadj' : ∀ x y, ⟪x, 𝓛 n y⟫ = ⟪𝓛' n x, y⟫ := fun x y =>
      (real_inner_comm _ _).trans ((hadj n y x).trans (real_inner_comm _ _))
    have e1 : ⟪ψ n, e n⟫ + ⟪ψ n, d n⟫
        = ⟪ψ n, e (n + 1)⟫ - h * ⟪𝓛' n (ψ n), e (n + 1)⟫ := by
      rw [← inner_add_right, ← he n hn', inner_sub_right, real_inner_smul_right, hadj']
    have e2 : ⟪ψ n - h • 𝓛' n (ψ n) - ψ (n + 1), e (n + 1)⟫
        = ⟪ψ n, e (n + 1)⟫ - h * ⟪𝓛' n (ψ n), e (n + 1)⟫ - ⟪ψ (n + 1), e (n + 1)⟫ := by
      rw [inner_sub_left, inner_sub_left, real_inner_smul_left]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith [ih (by omega)]

/-- **Primal–dual error identity.**  Let `A` be the full implicit Euler sequence of
`Ȧ = 𝓛 A + q` and let `𝓛' k` be adjoint to `𝓛 k`.  For **any** sequences `Y` (primal) and `ψ`
(dual), with primal residuals `R_k = Y_{k+1} - Y_k - h (𝓛_k Y_{k+1} + q_k)` and dual residuals
`ρ_k = ψ_k - h 𝓛'_k ψ_k - ψ_{k+1}`,
`⟪ψ_n, Y_n - A_n⟫ = ⟪ψ_0, Y_0 - A_0⟫ + ∑_{k<n} ⟪ψ_k, R_k⟫ - ∑_{k<n} ⟪ρ_k, Y_{k+1} - A_{k+1}⟫`. -/
theorem primalDual_error_identity (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hA : ∀ k < N, A (k + 1) - h • 𝓛 k (A (k + 1)) = A k + h • q k) :
    ∀ n ≤ N, ⟪ψ n, Y n - A n⟫ = ⟪ψ 0, Y 0 - A 0⟫
      + ∑ k ∈ range n, ⟪ψ k, Y (k + 1) - Y k - h • (𝓛 k (Y (k + 1)) + q k)⟫
      - ∑ k ∈ range n, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), Y (k + 1) - A (k + 1)⟫ := by
  have he : ∀ k < N, (Y (k + 1) - A (k + 1)) - h • 𝓛 k (Y (k + 1) - A (k + 1))
      = Y k - A k + (Y (k + 1) - Y k - h • (𝓛 k (Y (k + 1)) + q k)) := by
    intro k hk
    have hAk : A k = A (k + 1) - h • 𝓛 k (A (k + 1)) - h • q k := by
      rw [hA k hk]; abel
    rw [hAk]
    simp only [map_sub, smul_sub, smul_add]
    abel
  exact inner_eq_sum_inner_defect (e := fun k => Y k - A k)
    (d := fun k => Y (k + 1) - Y k - h • (𝓛 k (Y (k + 1)) + q k)) hadj he

/-- **Exact dual-weighted residual representation.**  If `ψ` is the discrete adjoint solution
(`ψ_k - h 𝓛'_k ψ_k = ψ_{k+1}`, final value `ψ_N = g`), the output error of any sequence `Y` is
exactly the residual sum weighted by `ψ`. -/
theorem dual_error_representation (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hA : ∀ k < N, A (k + 1) - h • 𝓛 k (A (k + 1)) = A k + h • q k)
    (hψ : ∀ k < N, ψ k - h • 𝓛' k (ψ k) = ψ (k + 1)) :
    ⟪ψ N, Y N - A N⟫ = ⟪ψ 0, Y 0 - A 0⟫
      + ∑ k ∈ range N, ⟪ψ k, Y (k + 1) - Y k - h • (𝓛 k (Y (k + 1)) + q k)⟫ := by
  have h1 := primalDual_error_identity (Y := Y) (ψ := ψ) hadj hA N le_rfl
  have h2 : ∑ k ∈ range N, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), Y (k + 1) - A (k + 1)⟫ = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [hψ k (Finset.mem_range.1 hk), sub_self, inner_zero_left]
  rw [h1, h2, sub_zero]

/-- **Adjoint-corrected output.**  Subtracting the computable dual-weighted residual sum from the
output leaves an error that only sees the dual residuals paired with the primal errors. -/
theorem corrected_output_error (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hA : ∀ k < N, A (k + 1) - h • 𝓛 k (A (k + 1)) = A k + h • q k) :
    ⟪ψ N, Y N⟫ - ∑ k ∈ range N, ⟪ψ k, Y (k + 1) - Y k - h • (𝓛 k (Y (k + 1)) + q k)⟫
        - ⟪ψ N, A N⟫
      = ⟪ψ 0, Y 0 - A 0⟫
        - ∑ k ∈ range N, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), Y (k + 1) - A (k + 1)⟫ := by
  have h1 := primalDual_error_identity (Y := Y) (ψ := ψ) hadj hA N le_rfl
  rw [inner_sub_right] at h1
  linarith

/-- A one-sided bound `⟪T x, x⟫ ≤ ℓ ‖x‖²` makes `1 - h T` expanding up to `1 - h ℓ`
(`implicitEuler_stability` with zero reference). -/
lemma one_sub_mul_norm_le_norm_sub_smul {T : E →ₗ[ℝ] E} {ℓ : ℝ} (hh : 0 ≤ h) {x : E}
    (hT : ⟪T x, x⟫ ≤ ℓ * ‖x‖ ^ 2) : (1 - h * ℓ) * ‖x‖ ≤ ‖x - h • T x‖ := by
  have key := implicitEuler_stability (F := fun _ z => T z) (ℓ := ℓ) (t := 0) hh
    (x₀ := 0) (y₀ := 0) (x₁ := x) (y₁ := 0) (r := x - h • T x) (s := 0)
    (by simpa using hT) (by simp) (by simp)
  simpa using key

/-- **Primal certificate against the full implicit Euler scheme.**  If `⟪𝓛_k x, x⟫ ≤ ℓ ‖x‖²` and
`h ℓ < 1`, any sequence `Y` satisfies
`‖Y_n - A_n‖ ≤ max(1, (1 - h ℓ)⁻¹)ⁿ (‖Y_0 - A_0‖ + ∑_{k<n} ‖R_k‖)`. -/
theorem norm_sub_reference_le (hh : 0 ≤ h) {ℓ : ℝ} (hℓ : h * ℓ < 1)
    (hdis : ∀ k x, ⟪𝓛 k x, x⟫ ≤ ℓ * ‖x‖ ^ 2)
    (hA : ∀ k < N, A (k + 1) - h • 𝓛 k (A (k + 1)) = A k + h • q k) :
    ∀ n ≤ N, ‖Y n - A n‖ ≤ max 1 (1 - h * ℓ)⁻¹ ^ n * (‖Y 0 - A 0‖
      + ∑ k ∈ range n, ‖Y (k + 1) - Y k - h • (𝓛 k (Y (k + 1)) + q k)‖) := by
  have hpos : 0 < 1 - h * ℓ := by linarith
  refine amplified_sum_le (e := fun n => ‖Y n - A n‖)
    (c := fun k => ‖Y (k + 1) - Y k - h • (𝓛 k (Y (k + 1)) + q k)‖) (a := (1 - h * ℓ)⁻¹)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) fun n hn => ?_
  have hkey : (Y (n + 1) - A (n + 1)) - h • 𝓛 n (Y (n + 1) - A (n + 1))
      = Y n - A n + (Y (n + 1) - Y n - h • (𝓛 n (Y (n + 1)) + q n)) := by
    have hAn : A n = A (n + 1) - h • 𝓛 n (A (n + 1)) - h • q n := by
      rw [hA n hn]; abel
    rw [hAn]
    simp only [map_sub, smul_sub, smul_add]
    abel
  have h1 := one_sub_mul_norm_le_norm_sub_smul (h := h) hh (hdis n (Y (n + 1) - A (n + 1)))
  rw [hkey] at h1
  have h2 := h1.trans (norm_add_le _ _)
  change ‖Y (n + 1) - A (n + 1)‖ ≤ (1 - h * ℓ)⁻¹
    * (‖Y n - A n‖ + ‖Y (n + 1) - Y n - h • (𝓛 n (Y (n + 1)) + q n)‖)
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  linarith

/-- **Product bound for the adjoint-corrected output.**  With `⟪𝓛_k x, x⟫ ≤ ℓ ‖x‖²`, `h ℓ < 1`,
the corrected output `⟪ψ_N, Y_N⟫ - ∑ ⟪ψ_k, R_k⟫` misses the reference output `⟪ψ_N, A_N⟫` by at
most `‖ψ_0‖ ‖e_0‖ + ∑_k ‖ρ_k‖ aᵏ⁺¹ (‖e_0‖ + ∑_{j ≤ k} ‖R_j‖)`, `a = max(1, (1 - h ℓ)⁻¹)`: every
term is a dual residual times a primal residual (or the initial error). -/
theorem abs_corrected_output_sub_le (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hA : ∀ k < N, A (k + 1) - h • 𝓛 k (A (k + 1)) = A k + h • q k) (hh : 0 ≤ h) {ℓ : ℝ}
    (hℓ : h * ℓ < 1) (hdis : ∀ k x, ⟪𝓛 k x, x⟫ ≤ ℓ * ‖x‖ ^ 2) :
    |⟪ψ N, Y N⟫ - ∑ k ∈ range N, ⟪ψ k, Y (k + 1) - Y k - h • (𝓛 k (Y (k + 1)) + q k)⟫
        - ⟪ψ N, A N⟫|
      ≤ ‖ψ 0‖ * ‖Y 0 - A 0‖ + ∑ k ∈ range N, ‖ψ k - h • 𝓛' k (ψ k) - ψ (k + 1)‖
          * (max 1 (1 - h * ℓ)⁻¹ ^ (k + 1) * (‖Y 0 - A 0‖
            + ∑ j ∈ range (k + 1), ‖Y (j + 1) - Y j - h • (𝓛 j (Y (j + 1)) + q j)‖)) := by
  rw [corrected_output_error hadj hA]
  have h0 := abs_real_inner_le_norm (ψ 0) (Y 0 - A 0)
  have hS : |∑ k ∈ range N, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), Y (k + 1) - A (k + 1)⟫|
      ≤ ∑ k ∈ range N, ‖ψ k - h • 𝓛' k (ψ k) - ψ (k + 1)‖
          * (max 1 (1 - h * ℓ)⁻¹ ^ (k + 1) * (‖Y 0 - A 0‖
            + ∑ j ∈ range (k + 1), ‖Y (j + 1) - Y j - h • (𝓛 j (Y (j + 1)) + q j)‖)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    have hk' : k + 1 ≤ N := Finset.mem_range.1 hk
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (norm_sub_reference_le hh hℓ hdis hA (k + 1) hk') (norm_nonneg _))
  rw [abs_le] at h0 hS ⊢
  constructor <;> linarith [h0.1, h0.2, hS.1, hS.2]

/-- Dissipative case (`⟪𝓛_k x, x⟫ ≤ 0`, e.g. transport, collisions, diffusion): no amplification,
the bound is the plain double sum `∑_k ‖ρ_k‖ (‖e_0‖ + ∑_{j ≤ k} ‖R_j‖)`. -/
theorem abs_corrected_output_sub_le_of_dissipative
    (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hA : ∀ k < N, A (k + 1) - h • 𝓛 k (A (k + 1)) = A k + h • q k) (hh : 0 ≤ h)
    (hdis : ∀ k x, ⟪𝓛 k x, x⟫ ≤ 0) :
    |⟪ψ N, Y N⟫ - ∑ k ∈ range N, ⟪ψ k, Y (k + 1) - Y k - h • (𝓛 k (Y (k + 1)) + q k)⟫
        - ⟪ψ N, A N⟫|
      ≤ ‖ψ 0‖ * ‖Y 0 - A 0‖ + ∑ k ∈ range N, ‖ψ k - h • 𝓛' k (ψ k) - ψ (k + 1)‖
          * (‖Y 0 - A 0‖
            + ∑ j ∈ range (k + 1), ‖Y (j + 1) - Y j - h • (𝓛 j (Y (j + 1)) + q j)‖) := by
  have key := abs_corrected_output_sub_le (Y := Y) (ψ := ψ) hadj hA hh (ℓ := 0) (by simp)
    (by simpa using hdis)
  simpa using key

end PrimalDual

/-! ### Nonlinear problems: the linearisation remainder -/

section Nonlinear

variable {F : ℕ → E → E} {𝓛 𝓛' : ℕ → E →ₗ[ℝ] E} {h : ℝ} {N : ℕ} {A Y ψ : ℕ → E}

/-- **Primal–dual error identity for a nonlinear problem.**  Let `A` be the full implicit Euler
sequence of `Ȧ = F(t, A)`, `A_{k+1} = A_k + h F_k(A_{k+1})`, and let `𝓛 k` be **any** linear map
(a linearisation of `F k`, for instance its derivative at `Y_{k+1}`) with adjoint `𝓛' k`.  For any
sequences `Y` and `ψ`, with `R_k = Y_{k+1} - Y_k - h F_k(Y_{k+1})`, `e_k = Y_k - A_k`, the
linearisation remainder `r_k = F_k(Y_{k+1}) - F_k(A_{k+1}) - 𝓛_k e_{k+1}` and
`ρ_k = ψ_k - h 𝓛'_k ψ_k - ψ_{k+1}`,
`⟪ψ_n, e_n⟫ = ⟪ψ_0, e_0⟫ + ∑ ⟪ψ_k, R_k⟫ + h ∑ ⟪ψ_k, r_k⟫ - ∑ ⟪ρ_k, e_{k+1}⟫`. -/
theorem primalDual_error_identity_of_linearization
    (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hA : ∀ k < N, A (k + 1) = A k + h • F k (A (k + 1))) :
    ∀ n ≤ N, ⟪ψ n, Y n - A n⟫ = ⟪ψ 0, Y 0 - A 0⟫
      + ∑ k ∈ range n, ⟪ψ k, Y (k + 1) - Y k - h • F k (Y (k + 1))⟫
      + h * ∑ k ∈ range n,
          ⟪ψ k, F k (Y (k + 1)) - F k (A (k + 1)) - 𝓛 k (Y (k + 1) - A (k + 1))⟫
      - ∑ k ∈ range n, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), Y (k + 1) - A (k + 1)⟫ := by
  intro n hn
  have he : ∀ k < N, (Y (k + 1) - A (k + 1)) - h • 𝓛 k (Y (k + 1) - A (k + 1))
      = Y k - A k + (Y (k + 1) - Y k - h • F k (Y (k + 1))
        + h • (F k (Y (k + 1)) - F k (A (k + 1)) - 𝓛 k (Y (k + 1) - A (k + 1)))) := by
    intro k hk
    rw [eq_sub_of_add_eq (hA k hk).symm]
    module
  have key : ⟪ψ n, Y n - A n⟫ = ⟪ψ 0, Y 0 - A 0⟫
      + ∑ k ∈ range n, ⟪ψ k, Y (k + 1) - Y k - h • F k (Y (k + 1))
        + h • (F k (Y (k + 1)) - F k (A (k + 1)) - 𝓛 k (Y (k + 1) - A (k + 1)))⟫
      - ∑ k ∈ range n, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), Y (k + 1) - A (k + 1)⟫ :=
    inner_eq_sum_inner_defect (e := fun k => Y k - A k)
      (d := fun k => Y (k + 1) - Y k - h • F k (Y (k + 1))
        + h • (F k (Y (k + 1)) - F k (A (k + 1)) - 𝓛 k (Y (k + 1) - A (k + 1)))) hadj he n hn
  have hsplit : ∑ k ∈ range n, ⟪ψ k, Y (k + 1) - Y k - h • F k (Y (k + 1))
        + h • (F k (Y (k + 1)) - F k (A (k + 1)) - 𝓛 k (Y (k + 1) - A (k + 1)))⟫
      = ∑ k ∈ range n, ⟪ψ k, Y (k + 1) - Y k - h • F k (Y (k + 1))⟫
        + h * ∑ k ∈ range n,
          ⟪ψ k, F k (Y (k + 1)) - F k (A (k + 1)) - 𝓛 k (Y (k + 1) - A (k + 1))⟫ := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [inner_add_right, real_inner_smul_right]
  linarith

/-- **Primal certificate, nonlinear problem.**  If `F k` satisfies the one-sided Lipschitz
inequality with constant `ℓ` at the pairs `(Y_{k+1}, A_{k+1})` and `h ℓ < 1`, then
`‖Y_n - A_n‖ ≤ max(1, (1 - h ℓ)⁻¹)ⁿ (‖Y_0 - A_0‖ + ∑_{k<n} ‖R_k‖)`. -/
theorem norm_sub_nonlinear_reference_le (hh : 0 ≤ h) {ℓ : ℝ} (hℓ : h * ℓ < 1)
    (hF : ∀ k < N, ⟪F k (Y (k + 1)) - F k (A (k + 1)), Y (k + 1) - A (k + 1)⟫
      ≤ ℓ * ‖Y (k + 1) - A (k + 1)‖ ^ 2)
    (hA : ∀ k < N, A (k + 1) = A k + h • F k (A (k + 1))) :
    ∀ n ≤ N, ‖Y n - A n‖ ≤ max 1 (1 - h * ℓ)⁻¹ ^ n * (‖Y 0 - A 0‖
      + ∑ k ∈ range n, ‖Y (k + 1) - Y k - h • F k (Y (k + 1))‖) := by
  have hpos : 0 < 1 - h * ℓ := by linarith
  refine amplified_sum_le (e := fun n => ‖Y n - A n‖)
    (c := fun k => ‖Y (k + 1) - Y k - h • F k (Y (k + 1))‖) (a := (1 - h * ℓ)⁻¹)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) fun n hn => ?_
  have h1 : (1 - h * ℓ) * ‖Y (n + 1) - A (n + 1)‖
      ≤ ‖Y n - A n‖ + ‖Y (n + 1) - Y n - h • F n (Y (n + 1)) - 0‖ :=
    implicitEuler_stability (F := fun _ z => F n z) (t := 0) hh (hF n hn)
      (show Y (n + 1) = Y n + h • F n (Y (n + 1)) + (Y (n + 1) - Y n - h • F n (Y (n + 1))) by
        abel)
      (show A (n + 1) = A n + h • F n (A (n + 1)) + 0 by rw [add_zero]; exact hA n hn)
  rw [sub_zero] at h1
  change ‖Y (n + 1) - A (n + 1)‖ ≤ (1 - h * ℓ)⁻¹
    * (‖Y n - A n‖ + ‖Y (n + 1) - Y n - h • F n (Y (n + 1))‖)
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  linarith

/-- **Adjoint-corrected output, nonlinear problem.**  The corrected output misses the reference
output by the dual residuals paired with the primal errors, plus `h` times the dual-weighted
linearisation remainders. -/
theorem corrected_output_error_of_linearization
    (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hA : ∀ k < N, A (k + 1) = A k + h • F k (A (k + 1))) :
    ⟪ψ N, Y N⟫ - ∑ k ∈ range N, ⟪ψ k, Y (k + 1) - Y k - h • F k (Y (k + 1))⟫ - ⟪ψ N, A N⟫
      = ⟪ψ 0, Y 0 - A 0⟫
        + h * ∑ k ∈ range N,
            ⟪ψ k, F k (Y (k + 1)) - F k (A (k + 1)) - 𝓛 k (Y (k + 1) - A (k + 1))⟫
        - ∑ k ∈ range N, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), Y (k + 1) - A (k + 1)⟫ := by
  have h1 := primalDual_error_identity_of_linearization (Y := Y) (ψ := ψ) hadj hA N le_rfl
  have h2 : ⟪ψ N, Y N - A N⟫ = ⟪ψ N, Y N⟫ - ⟪ψ N, A N⟫ := inner_sub_right _ _ _
  linarith

/-- **Bound for the adjoint-corrected output, nonlinear problem.**  Let `E` be any primal
certificate, `‖Y_n - A_n‖ ≤ E n` (for instance that of `norm_sub_nonlinear_reference_le`), and
let the linearisation remainder be quadratic, `‖r_k‖ ≤ M ‖e_{k+1}‖²`.  Then the corrected output
misses the reference output by at most
`‖ψ_0‖ E_0 + ∑ ‖ρ_k‖ E_{k+1} + h ∑ ‖ψ_k‖ M E_{k+1}²`:
dual residual times primal error, plus a term that is quadratic in the primal error. -/
theorem abs_corrected_output_sub_le_of_linearization
    (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hA : ∀ k < N, A (k + 1) = A k + h • F k (A (k + 1))) (hh : 0 ≤ h) {M : ℝ} (hM : 0 ≤ M)
    {E : ℕ → ℝ} (hE : ∀ n ≤ N, ‖Y n - A n‖ ≤ E n)
    (hr : ∀ k < N, ‖F k (Y (k + 1)) - F k (A (k + 1)) - 𝓛 k (Y (k + 1) - A (k + 1))‖
      ≤ M * ‖Y (k + 1) - A (k + 1)‖ ^ 2) :
    |⟪ψ N, Y N⟫ - ∑ k ∈ range N, ⟪ψ k, Y (k + 1) - Y k - h • F k (Y (k + 1))⟫ - ⟪ψ N, A N⟫|
      ≤ ‖ψ 0‖ * E 0 + ∑ k ∈ range N, ‖ψ k - h • 𝓛' k (ψ k) - ψ (k + 1)‖ * E (k + 1)
        + h * ∑ k ∈ range N, ‖ψ k‖ * (M * E (k + 1) ^ 2) := by
  rw [corrected_output_error_of_linearization hadj hA]
  have h0 : |⟪ψ 0, Y 0 - A 0⟫| ≤ ‖ψ 0‖ * E 0 :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hE 0 (Nat.zero_le N)) (norm_nonneg _))
  have hS : |∑ k ∈ range N, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), Y (k + 1) - A (k + 1)⟫|
      ≤ ∑ k ∈ range N, ‖ψ k - h • 𝓛' k (ψ k) - ψ (k + 1)‖ * E (k + 1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    have hk' : k + 1 ≤ N := Finset.mem_range.1 hk
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hE (k + 1) hk') (norm_nonneg _))
  have hR : |∑ k ∈ range N,
        ⟪ψ k, F k (Y (k + 1)) - F k (A (k + 1)) - 𝓛 k (Y (k + 1) - A (k + 1))⟫|
      ≤ ∑ k ∈ range N, ‖ψ k‖ * (M * E (k + 1) ^ 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    have hk' : k < N := Finset.mem_range.1 hk
    have hsq : ‖Y (k + 1) - A (k + 1)‖ ^ 2 ≤ E (k + 1) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hE (k + 1) (Nat.succ_le_of_lt hk')) 2
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      ((hr k hk').trans (mul_le_mul_of_nonneg_left hsq hM)) (norm_nonneg _))
  have hhR : |h * ∑ k ∈ range N,
        ⟪ψ k, F k (Y (k + 1)) - F k (A (k + 1)) - 𝓛 k (Y (k + 1) - A (k + 1))⟫|
      ≤ h * ∑ k ∈ range N, ‖ψ k‖ * (M * E (k + 1) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left hR hh
  rw [abs_le] at h0 hS hhR ⊢
  constructor <;> linarith [h0.1, h0.2, hS.1, hS.2, hhR.1, hhR.2]

/-- **Quadratic fields.**  For `F x = L x + b x x + q` with `b` bilinear (Riccati, Burgers,
Vlasov–Poisson), the linearisation at `y`, `𝓛 = L + b y · + b · y`, has remainder exactly
`-b (y - a) (y - a)`. -/
theorem quadratic_linearization_remainder (L : E →ₗ[ℝ] E) (b : E →ₗ[ℝ] E →ₗ[ℝ] E) (q y a : E) :
    L y + b y y + q - (L a + b a a + q) - (L (y - a) + b y (y - a) + b (y - a) y)
      = -b (y - a) (y - a) := by
  simp only [map_sub, LinearMap.sub_apply]
  abel

/-- For a quadratic field with `‖b x x‖ ≤ M ‖x‖²` the linearisation remainder is at most
`M ‖y - a‖²`: the hypothesis `hr` of `abs_corrected_output_sub_le_of_linearization`. -/
theorem norm_quadratic_linearization_remainder_le (L : E →ₗ[ℝ] E) {b : E →ₗ[ℝ] E →ₗ[ℝ] E}
    {M : ℝ} (hb : ∀ x, ‖b x x‖ ≤ M * ‖x‖ ^ 2) (q y a : E) :
    ‖L y + b y y + q - (L a + b a a + q) - (L (y - a) + b y (y - a) + b (y - a) y)‖
      ≤ M * ‖y - a‖ ^ 2 := by
  rw [quadratic_linearization_remainder, norm_neg]
  exact hb _

end Nonlinear

/-! ### Galerkin steps: the correction vanishes when the space contains the dual -/

section Galerkin

/-- **Galerkin orthogonality of the implicit residual.**  For a Galerkin step
`Y₁ = P (Y₀ + h f)` the residual `Y₁ - Y₀ - h f` is orthogonal to `range P`.  This is the forward
direction of `implicitGalerkin_iff_variational`, in the form used for dual weights. -/
theorem inner_galerkin_residual_eq_zero {P : E →L[ℝ] E} (hP : IsOrthProj P) {h : ℝ}
    {Y₀ Y₁ f z : E} (hY : Y₁ = P (Y₀ + h • f)) (hz : P z = z) :
    ⟪z, Y₁ - Y₀ - h • f⟫ = 0 :=
  (real_inner_comm _ _).trans (((implicitGalerkin_iff_variational hP Y₀ Y₁ f h).1 hY).2 z hz)

variable {𝓛 𝓛' : ℕ → E →ₗ[ℝ] E} {h : ℝ} {N : ℕ} {A Y ψ q : ℕ → E}

/-- **Output error of a dual-consistent Galerkin integrator.**  If every step is an implicit
Galerkin step in `range (P k)` and the dual iterate `ψ k` lies in `range (P k)`, the plain output
error has no first-order residual term:
`⟪ψ_N, Y_N - A_N⟫ = ⟪ψ_0, Y_0 - A_0⟫ - ∑_k ⟪ρ_k, Y_{k+1} - A_{k+1}⟫`. -/
theorem galerkin_output_error {P : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k))
    (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hA : ∀ k < N, A (k + 1) - h • 𝓛 k (A (k + 1)) = A k + h • q k)
    (hY : ∀ k < N, Y (k + 1) = P k (Y k + h • (𝓛 k (Y (k + 1)) + q k)))
    (hψP : ∀ k < N, P k (ψ k) = ψ k) :
    ⟪ψ N, Y N - A N⟫ = ⟪ψ 0, Y 0 - A 0⟫
      - ∑ k ∈ range N, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), Y (k + 1) - A (k + 1)⟫ := by
  have h1 := primalDual_error_identity (Y := Y) (ψ := ψ) hadj hA N le_rfl
  have h2 : ∑ k ∈ range N, ⟪ψ k, Y (k + 1) - Y k - h • (𝓛 k (Y (k + 1)) + q k)⟫ = 0 :=
    Finset.sum_eq_zero fun k hk =>
      inner_galerkin_residual_eq_zero (hP k) (hY k (Finset.mem_range.1 hk))
        (hψP k (Finset.mem_range.1 hk))
  rw [h1, h2, add_zero]

end Galerkin

/-! ### Implicit BUG steps with dual-enriched bases -/

section ImplicitBUG

variable {ε τ ϑ t₁ h : ℝ} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {Y₀ YK YL xS Y₁ : E}

/-- **Galerkin stage of an implicit BUG step.**  The residual of the Galerkin stage `xS` is
orthogonal to every `z` in the range of the two-sided projector `P₁ Q₁`.  If the (augmented)
bases contain a dual iterate, its dual-weighted residual at the Galerkin stage is zero. -/
theorem IsImplicitBUGStep.inner_sstep_residual_eq_zero {F : ℝ → E → E}
    (hs : IsImplicitBUGStep F ε τ ϑ P₀ Q₀ P₁ Q₁ t₁ h Y₀ YK YL xS Y₁) {z : E}
    (hz : (P₁ * Q₁) z = z) : ⟪z, xS - Y₀ - h • F t₁ xS⟫ = 0 :=
  inner_galerkin_residual_eq_zero hs.proj hs.sstep hz

variable {𝓛 𝓛' : E →ₗ[ℝ] E} {q ψ : E}

/-- **Dual-weighted residual of a dual-enriched implicit BUG step.**  For the linear field
`F t x = 𝓛 x + q` and a dual iterate `ψ` in the range of `P₁ Q₁`, only the truncation
contributes: `⟪ψ, Y₁ - Y₀ - h (𝓛 Y₁ + q)⟫ = ⟪ψ - h 𝓛' ψ, Y₁ - xS⟫`. -/
theorem IsImplicitBUGStep.inner_residual_eq_truncation
    (hs : IsImplicitBUGStep (fun _ x => 𝓛 x + q) ε τ ϑ P₀ Q₀ P₁ Q₁ t₁ h Y₀ YK YL xS Y₁)
    (hadj : ∀ x y, ⟪𝓛 x, y⟫ = ⟪x, 𝓛' y⟫) (hψ : (P₁ * Q₁) ψ = ψ) :
    ⟪ψ, Y₁ - Y₀ - h • (𝓛 Y₁ + q)⟫ = ⟪ψ - h • 𝓛' ψ, Y₁ - xS⟫ := by
  have h0 : ⟪ψ, xS - Y₀ - h • (𝓛 xS + q)⟫ = 0 := hs.inner_sstep_residual_eq_zero hψ
  have hadj' : ∀ y, ⟪ψ, 𝓛 y⟫ = ⟪𝓛' ψ, y⟫ := fun y =>
    (real_inner_comm _ _).trans ((hadj y ψ).trans (real_inner_comm _ _))
  have a1 := hadj' Y₁
  have a2 := hadj' xS
  simp only [inner_sub_left, inner_sub_right, inner_add_right, real_inner_smul_left,
    real_inner_smul_right] at h0 ⊢
  linear_combination h0 + h * a2 - h * a1

/-- The dual-weighted residual of a dual-enriched implicit BUG step is at most the truncation
tolerance times `‖ψ - h 𝓛' ψ‖`. -/
theorem IsImplicitBUGStep.abs_inner_residual_le
    (hs : IsImplicitBUGStep (fun _ x => 𝓛 x + q) ε τ ϑ P₀ Q₀ P₁ Q₁ t₁ h Y₀ YK YL xS Y₁)
    (hadj : ∀ x y, ⟪𝓛 x, y⟫ = ⟪x, 𝓛' y⟫) (hψ : (P₁ * Q₁) ψ = ψ) :
    |⟪ψ, Y₁ - Y₀ - h • (𝓛 Y₁ + q)⟫| ≤ ‖ψ - h • 𝓛' ψ‖ * ϑ := by
  rw [hs.inner_residual_eq_truncation hadj hψ]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hs.trunc (norm_nonneg _))

end ImplicitBUG

/-! ### Dual-consistent truncation: the output error without the truncation tolerance -/

section DualConsistent

variable {𝓛 𝓛' : ℕ → E →ₗ[ℝ] E} {h : ℝ} {N : ℕ} {A X Y ψ q : ℕ → E}

/-- **Balance law of a dual-consistent step sequence.**  Let the stage `X k` of step `k` satisfy
the implicit Euler equation tested with the dual iterate,
`⟪ψ_k, X_k - Y_k - h (𝓛_k X_k + q_k)⟫ = 0` (a Galerkin stage in a space that contains `ψ_k`), and
let the truncation `X_k ↦ Y_{k+1}` keep the pairing with the next dual iterate,
`⟪ψ_{k+1}, Y_{k+1} - X_k⟫ = 0`.  Then the pairing obeys the balance law of the full-rank scheme up
to the dual residual `ρ_k = ψ_k - h 𝓛'_k ψ_k - ψ_{k+1}`:
`⟪ψ_n, Y_n⟫ = ⟪ψ_0, Y_0⟫ + h ∑ ⟪ψ_k, q_k⟫ - ∑ ⟪ρ_k, X_k⟫`.  No reference solution occurs. -/
theorem dualConsistent_balance (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hgal : ∀ k < N, ⟪ψ k, X k - Y k - h • (𝓛 k (X k) + q k)⟫ = 0)
    (htr : ∀ k < N, ⟪ψ (k + 1), Y (k + 1) - X k⟫ = 0) :
    ∀ n ≤ N, ⟪ψ n, Y n⟫ = ⟪ψ 0, Y 0⟫ + h * ∑ k ∈ range n, ⟪ψ k, q k⟫
      - ∑ k ∈ range n, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), X k⟫ := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hn' : n < N := by omega
    have a1 : ⟪ψ n, 𝓛 n (X n)⟫ = ⟪𝓛' n (ψ n), X n⟫ :=
      (real_inner_comm _ _).trans ((hadj n (X n) (ψ n)).trans (real_inner_comm _ _))
    have g := hgal n hn'
    have t := htr n hn'
    rw [inner_sub_right, inner_sub_right, real_inner_smul_right, inner_add_right, a1] at g
    rw [inner_sub_right] at t
    have r : ⟪ψ n - h • 𝓛' n (ψ n) - ψ (n + 1), X n⟫
        = ⟪ψ n, X n⟫ - h * ⟪𝓛' n (ψ n), X n⟫ - ⟪ψ (n + 1), X n⟫ := by
      rw [inner_sub_left, inner_sub_left, real_inner_smul_left]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith [ih (by omega)]

/-- **Output error of a dual-consistent low-rank integrator.**  Under the hypotheses of
`dualConsistent_balance`, against the full-rank implicit Euler reference `A`:
`⟪ψ_N, Y_N - A_N⟫ = ⟪ψ_0, Y_0 - A_0⟫ - ∑_k ⟪ρ_k, X_k - A_{k+1}⟫`.
The truncation does not enter: the output error is the dual residual tested with the error of the
Galerkin stage.  Compare `galerkin_output_error` (no truncation) and
`IsImplicitBUGStep.inner_residual_eq_truncation` (a truncation that is not dual-consistent
contributes `⟪ψ - h 𝓛' ψ, Y₁ - xS⟫` per step). -/
theorem dualConsistent_output_error (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hA : ∀ k < N, A (k + 1) - h • 𝓛 k (A (k + 1)) = A k + h • q k)
    (hgal : ∀ k < N, ⟪ψ k, X k - Y k - h • (𝓛 k (X k) + q k)⟫ = 0)
    (htr : ∀ k < N, ⟪ψ (k + 1), Y (k + 1) - X k⟫ = 0) :
    ⟪ψ N, Y N - A N⟫ = ⟪ψ 0, Y 0 - A 0⟫
      - ∑ k ∈ range N, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), X k - A (k + 1)⟫ := by
  have hYb := dualConsistent_balance hadj hgal htr N le_rfl
  have hA0 : ∀ k < N, ⟪ψ k, A (k + 1) - A k - h • (𝓛 k (A (k + 1)) + q k)⟫ = 0 := by
    intro k hk
    have e : A (k + 1) - A k - h • (𝓛 k (A (k + 1)) + q k)
        = A (k + 1) - h • 𝓛 k (A (k + 1)) - (A k + h • q k) := by module
    rw [e, hA k hk, sub_self, inner_zero_right]
  have hAb : ⟪ψ N, A N⟫ = ⟪ψ 0, A 0⟫ + h * ∑ k ∈ range N, ⟪ψ k, q k⟫
      - ∑ k ∈ range N, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), A (k + 1)⟫ :=
    dualConsistent_balance (X := fun k => A (k + 1)) (Y := A) hadj hA0
      (fun k _ => by simp) N le_rfl
  have hsum : ∑ k ∈ range N, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), X k - A (k + 1)⟫
      = ∑ k ∈ range N, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), X k⟫
        - ∑ k ∈ range N, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), A (k + 1)⟫ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => inner_sub_right _ _ _
  have h1 : ⟪ψ N, Y N - A N⟫ = ⟪ψ N, Y N⟫ - ⟪ψ N, A N⟫ := inner_sub_right _ _ _
  have h0 : ⟪ψ 0, Y 0 - A 0⟫ = ⟪ψ 0, Y 0⟫ - ⟪ψ 0, A 0⟫ := inner_sub_right _ _ _
  linarith

/-- Bound form of `dualConsistent_output_error`: the output error of a dual-consistent integrator
is at most `‖ψ_0‖ ‖e_0‖ + ∑_k ‖ρ_k‖ ‖X_k - A_{k+1}‖`, a sum of products of the dual residual and
the error of the Galerkin stage. -/
theorem abs_dualConsistent_output_error_le (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hA : ∀ k < N, A (k + 1) - h • 𝓛 k (A (k + 1)) = A k + h • q k)
    (hgal : ∀ k < N, ⟪ψ k, X k - Y k - h • (𝓛 k (X k) + q k)⟫ = 0)
    (htr : ∀ k < N, ⟪ψ (k + 1), Y (k + 1) - X k⟫ = 0) :
    |⟪ψ N, Y N - A N⟫| ≤ ‖ψ 0‖ * ‖Y 0 - A 0‖
      + ∑ k ∈ range N, ‖ψ k - h • 𝓛' k (ψ k) - ψ (k + 1)‖ * ‖X k - A (k + 1)‖ := by
  rw [dualConsistent_output_error hadj hA hgal htr]
  have h0 := abs_real_inner_le_norm (ψ 0) (Y 0 - A 0)
  have hS : |∑ k ∈ range N, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), X k - A (k + 1)⟫|
      ≤ ∑ k ∈ range N, ‖ψ k - h • 𝓛' k (ψ k) - ψ (k + 1)‖ * ‖X k - A (k + 1)‖ :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun k _ => abs_real_inner_le_norm _ _)
  rw [abs_le] at h0 hS ⊢
  constructor <;> linarith [h0.1, h0.2, hS.1, hS.2]

/-- **A dual-consistent integrator transports adjoint invariants exactly.**  If `ψ` is the exact
discrete adjoint sequence, `ψ_{k+1} = ψ_k - h 𝓛'_k ψ_k`, the pairing satisfies the balance law of
the full-rank implicit Euler scheme, `⟪ψ_N, Y_N⟫ = ⟪ψ_0, Y_0⟫ + h ∑ ⟪ψ_k, q_k⟫`, for every rank and
every truncation tolerance. -/
theorem dualConsistent_inner_eq (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hgal : ∀ k < N, ⟪ψ k, X k - Y k - h • (𝓛 k (X k) + q k)⟫ = 0)
    (htr : ∀ k < N, ⟪ψ (k + 1), Y (k + 1) - X k⟫ = 0)
    (hψ : ∀ k < N, ψ (k + 1) = ψ k - h • 𝓛' k (ψ k)) :
    ⟪ψ N, Y N⟫ = ⟪ψ 0, Y 0⟫ + h * ∑ k ∈ range N, ⟪ψ k, q k⟫ := by
  have hb := dualConsistent_balance hadj hgal htr N le_rfl
  have h0 : ∑ k ∈ range N, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), X k⟫ = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [← hψ k (Finset.mem_range.1 hk), sub_self, inner_zero_left]
  linarith

/-- For the exact discrete adjoint sequence, a dual-consistent integrator has the output of the
full-rank implicit Euler scheme up to the initial error: `⟪ψ_N, Y_N - A_N⟫ = ⟪ψ_0, Y_0 - A_0⟫`. -/
theorem dualConsistent_output_error_of_dual (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hA : ∀ k < N, A (k + 1) - h • 𝓛 k (A (k + 1)) = A k + h • q k)
    (hgal : ∀ k < N, ⟪ψ k, X k - Y k - h • (𝓛 k (X k) + q k)⟫ = 0)
    (htr : ∀ k < N, ⟪ψ (k + 1), Y (k + 1) - X k⟫ = 0)
    (hψ : ∀ k < N, ψ (k + 1) = ψ k - h • 𝓛' k (ψ k)) :
    ⟪ψ N, Y N - A N⟫ = ⟪ψ 0, Y 0 - A 0⟫ := by
  have h1 := dualConsistent_output_error hadj hA hgal htr
  have h0 : ∑ k ∈ range N, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), X k - A (k + 1)⟫ = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [← hψ k (Finset.mem_range.1 hk), sub_self, inner_zero_left]
  linarith

/-- **Conservation is the stationary case.**  A fixed `c` with `𝓛'_k c = 0` is its own discrete
adjoint sequence.  If the Galerkin spaces contain `c` and the truncation keeps `⟪c, ·⟫` (the
conservative integrators of `Stability/Conservation.lean`: `consTrunc_inner`), then
`⟪c, Y_N⟫ = ⟪c, Y_0⟫ + h ∑ ⟪c, q_k⟫`; for `⟪c, q_k⟫ = 0` the functional `⟪c, ·⟫` is conserved. -/
theorem dualConsistent_inner_eq_of_stationary {c : E}
    (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫) (hc : ∀ k < N, 𝓛' k c = 0)
    (hgal : ∀ k < N, ⟪c, X k - Y k - h • (𝓛 k (X k) + q k)⟫ = 0)
    (htr : ∀ k < N, ⟪c, Y (k + 1) - X k⟫ = 0) :
    ⟪c, Y N⟫ = ⟪c, Y 0⟫ + h * ∑ k ∈ range N, ⟪c, q k⟫ :=
  dualConsistent_inner_eq (ψ := fun _ => c) hadj hgal htr fun k hk => by simp [hc k hk]

/-- **The conservative truncation is dual-consistent.**  If the kept directions `range C` contain
`ψ`, the conservative truncation `consTrunc C T` (keep `C x`, truncate the remainder) does not
change the pairing with `ψ`.  With `C` a projector onto directions that contain the next dual
iterate this is the truncation hypothesis of `dualConsistent_output_error`. -/
theorem inner_consTrunc_sub_eq_zero {C : E →L[ℝ] E} (hC : IsOrthProj C) {T : E → E} {x ψ : E}
    (hT : C (T (x - C x)) = 0) (hψ : C ψ = ψ) : ⟪ψ, consTrunc C T x - x⟫ = 0 := by
  rw [inner_sub_right, consTrunc_inner hC hT hψ, sub_self]

/-- **Output error of the dual-consistent implicit BUG integrator.**  Every step is an implicit
BUG step for `F x = 𝓛_k x + q_k` whose (augmented) bases contain the dual iterate `ψ_k`, followed
by the conservative truncation with respect to a projector `C k` whose range contains `ψ_{k+1}`.
Then `⟪ψ_N, Y_N - A_N⟫ = ⟪ψ_0, Y_0 - A_0⟫ - ∑_k ⟪ρ_k, X_k - A_{k+1}⟫` with the Galerkin stages
`X_k`: neither the truncation tolerances `ϑ k` nor a singular value occurs. -/
theorem implicitBUG_dualConsistent_output_error {ε τ ϑ t : ℕ → ℝ}
    {P₀ Q₀ P₁ Q₁ C : ℕ → E →L[ℝ] E} {YK YL : ℕ → E} {T : ℕ → E → E}
    (hadj : ∀ k x y, ⟪𝓛 k x, y⟫ = ⟪x, 𝓛' k y⟫)
    (hA : ∀ k < N, A (k + 1) - h • 𝓛 k (A (k + 1)) = A k + h • q k)
    (hs : ∀ k < N, IsImplicitBUGStep (fun _ x => 𝓛 k x + q k) (ε k) (τ k) (ϑ k) (P₀ k) (Q₀ k)
      (P₁ k) (Q₁ k) (t k) h (Y k) (YK k) (YL k) (X k) (Y (k + 1)))
    (hψ : ∀ k < N, (P₁ k * Q₁ k) (ψ k) = ψ k)
    (hC : ∀ k < N, IsOrthProj (C k)) (hCψ : ∀ k < N, C k (ψ (k + 1)) = ψ (k + 1))
    (hT : ∀ k < N, C k (T k (X k - C k (X k))) = 0)
    (hY : ∀ k < N, Y (k + 1) = consTrunc (C k) (T k) (X k)) :
    ⟪ψ N, Y N - A N⟫ = ⟪ψ 0, Y 0 - A 0⟫
      - ∑ k ∈ range N, ⟪ψ k - h • 𝓛' k (ψ k) - ψ (k + 1), X k - A (k + 1)⟫ :=
  dualConsistent_output_error hadj hA
    (fun k hk => (hs k hk).inner_sstep_residual_eq_zero (hψ k hk))
    (fun k hk => by
      rw [hY k hk]
      exact inner_consTrunc_sub_eq_zero (hC k hk) (hT k hk) (hCψ k hk))

end DualConsistent

/-! ### Efficiency of the residual -/

section Efficiency

/-- **Efficiency of the implicit Euler residual.**  If `y₁ = y₀ + h F(t, y₁)` is the exact
implicit step and `F(t, ·)` is `L`-Lipschitz at the pair `(x₁, y₁)`, the residual of any `x₁` is
bounded by the errors: `‖x₁ - x₀ - h F(t, x₁)‖ ≤ (1 + h L) ‖x₁ - y₁‖ + ‖x₀ - y₀‖`.  With
`implicitEuler_stability` (`(1 - h ℓ) ‖x₁ - y₁‖ ≤ ‖x₀ - y₀‖ + ‖residual‖`) the residual is a
two-sided error estimator. -/
theorem implicitEuler_residual_le {F : ℝ → E → E} {L h t : ℝ} (hh : 0 ≤ h) {x₀ y₀ x₁ y₁ : E}
    (hL : ‖F t x₁ - F t y₁‖ ≤ L * ‖x₁ - y₁‖) (hy : y₁ = y₀ + h • F t y₁) :
    ‖x₁ - x₀ - h • F t x₁‖ ≤ (1 + h * L) * ‖x₁ - y₁‖ + ‖x₀ - y₀‖ := by
  have hy₀ : y₀ = y₁ - h • F t y₁ := eq_sub_of_add_eq hy.symm
  have h1 : x₁ - x₀ - h • F t x₁ = (x₁ - y₁) - (x₀ - y₀) - h • (F t x₁ - F t y₁) := by
    rw [hy₀, smul_sub]; abel
  rw [h1]
  calc ‖(x₁ - y₁) - (x₀ - y₀) - h • (F t x₁ - F t y₁)‖
      ≤ ‖(x₁ - y₁) - (x₀ - y₀)‖ + ‖h • (F t x₁ - F t y₁)‖ := _root_.norm_sub_le _ _
    _ ≤ (‖x₁ - y₁‖ + ‖x₀ - y₀‖) + h * (L * ‖x₁ - y₁‖) := by
        refine add_le_add (_root_.norm_sub_le _ _) ?_
        rw [norm_smul, Real.norm_of_nonneg hh]
        exact mul_le_mul_of_nonneg_left hL hh
    _ = (1 + h * L) * ‖x₁ - y₁‖ + ‖x₀ - y₀‖ := by ring

end Efficiency

/-! ### Enrichment: enlarging the Galerkin space contracts the defect -/

section Enrichment

variable {P P' : E →L[ℝ] E}

/-- **Enrichment splits the defect** (Pythagoras): for `P ≤ P'`,
`‖P' w - P w‖² + ‖w - P' w‖² = ‖w - P w‖²`. -/
theorem norm_sq_enrichment_split (hP' : IsOrthProj P') (hPP' : ∀ x, P' (P x) = P x) (w : E) :
    ‖P' w - P w‖ ^ 2 + ‖w - P' w‖ ^ 2 = ‖w - P w‖ ^ 2 := by
  have h1 := hP'.norm_sq_add (w - P w)
  have h2 : P' (w - P w) = P' w - P w := by rw [map_sub, hPP']
  have h3 : w - P w - (P' w - P w) = w - P' w := by abel
  rwa [h2, h3] at h1

/-- **An enriched implicit Galerkin step moves by at most the captured defect.**  Let
`X = P (Y₀ + h F(X))` and `X' = P' (Y₀ + h F(X'))` with `P ≤ P'` and `F` one-sided Lipschitz at
the pair.  Then `(1 - h ℓ) ‖X' - X‖ ≤ ‖(P' - P)(Y₀ + h F(X))‖`. -/
theorem enrichment_step_sub_le (hP' : IsOrthProj P') (hPP' : ∀ x, P' (P x) = P x) {F : E → E}
    {ℓ h : ℝ} (hh : 0 ≤ h) {Y₀ X X' : E} (hX : X = P (Y₀ + h • F X))
    (hX' : X' = P' (Y₀ + h • F X')) (hF : ⟪F X' - F X, X' - X⟫ ≤ ℓ * ‖X' - X‖ ^ 2) :
    (1 - h * ℓ) * ‖X' - X‖ ≤ ‖P' (Y₀ + h • F X) - P (Y₀ + h • F X)‖ := by
  obtain ⟨w, hw⟩ : ∃ w, w = Y₀ + h • F X := ⟨_, rfl⟩
  rw [← hw] at hX ⊢
  have hy : X = P' ((Y₀ - (P' w - P w)) + h • F X) := by
    have e : (Y₀ - (P' w - P w)) + h • F X = w - (P' w - P w) := by rw [hw]; abel
    rw [e, map_sub, map_sub, hP'.idem, hPP', sub_sub_cancel]
    exact hX
  have key := proj_implicit_step_stability hP' hh hX' hy hF
  rwa [sub_sub_cancel] at key

/-- **Defect after enrichment.**  With `w = Y₀ + h F(X)` (old step) and `w' = Y₀ + h F(X')`
(enriched step), `‖(1 - P') w'‖ ≤ ‖(1 - P') w‖ + h L / (1 - h ℓ) ‖(1 - P) w‖`: what the
enrichment did not capture, plus a factor `O(h)` times the old defect. -/
theorem enrichment_defect_le (hP' : IsOrthProj P') (hPP' : ∀ x, P' (P x) = P x) {F : E → E}
    {ℓ L h : ℝ} (hh : 0 ≤ h) (hℓ : h * ℓ < 1) (hL0 : 0 ≤ L) {Y₀ X X' : E}
    (hX : X = P (Y₀ + h • F X)) (hX' : X' = P' (Y₀ + h • F X'))
    (hF : ⟪F X' - F X, X' - X⟫ ≤ ℓ * ‖X' - X‖ ^ 2) (hL : ‖F X' - F X‖ ≤ L * ‖X' - X‖) :
    ‖(Y₀ + h • F X') - P' (Y₀ + h • F X')‖ ≤ ‖(Y₀ + h • F X) - P' (Y₀ + h • F X)‖
      + h * L / (1 - h * ℓ) * ‖(Y₀ + h • F X) - P (Y₀ + h • F X)‖ := by
  have hstab := enrichment_step_sub_le hP' hPP' hh hX hX' hF
  obtain ⟨w, hw⟩ : ∃ w, w = Y₀ + h • F X := ⟨_, rfl⟩
  rw [← hw] at hstab ⊢
  have hpos : 0 < 1 - h * ℓ := by linarith
  have hw' : Y₀ + h • F X' = w + h • (F X' - F X) := by rw [hw, smul_sub]; abel
  have h1 : (Y₀ + h • F X') - P' (Y₀ + h • F X')
      = (w - P' w) + h • ((F X' - F X) - P' (F X' - F X)) := by
    rw [hw', map_add, map_smul]
    simp only [smul_sub]
    abel
  have h2 : ‖P' w - P w‖ ≤ ‖w - P w‖ := by
    have e : P' w - P w = P' (w - P w) := by rw [map_sub, hPP']
    rw [e]; exact hP'.norm_le _
  have h3 : ‖X' - X‖ ≤ ‖w - P w‖ / (1 - h * ℓ) := by
    rw [le_div_iff₀ hpos]; linarith
  have h4 : ‖(F X' - F X) - P' (F X' - F X)‖ ≤ L * (‖w - P w‖ / (1 - h * ℓ)) :=
    (hP'.norm_sub_le _).trans (hL.trans (mul_le_mul_of_nonneg_left h3 hL0))
  rw [h1]
  calc ‖(w - P' w) + h • ((F X' - F X) - P' (F X' - F X))‖
      ≤ ‖w - P' w‖ + ‖h • ((F X' - F X) - P' (F X' - F X))‖ := norm_add_le _ _
    _ ≤ ‖w - P' w‖ + h * (L * (‖w - P w‖ / (1 - h * ℓ))) := by
        rw [norm_smul, Real.norm_of_nonneg hh]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h4 hh)
    _ = ‖w - P' w‖ + h * L / (1 - h * ℓ) * ‖w - P w‖ := by ring

end Enrichment

end LeanDLRA
