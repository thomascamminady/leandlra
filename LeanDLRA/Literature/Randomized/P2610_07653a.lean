import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Foundations.Gronwall

/-!
# Results of arXiv 2610.07653: Low-rank SI-DSA and GMRES-DSA for radiative transfer

This module formalizes the adaptive accuracy result for inexact fixed-point iterations that
underlies the low-rank SI-DSA tolerance schedule (arXiv 2610.07653). The main theorem
`inexact_iteration_error` is stated for an arbitrary normed space `E` and a `ρ`-contraction `T`
with fixed point `x*`. For `x (k+1) = T (x k) + e k` with `‖e k‖ ≤ τ k` it gives
`‖x k - x*‖ ≤ ρ^k ‖x 0 - x*‖ + ∑_{j<k} ρ^(k-1-j) τ j`, which is a discrete Grönwall bound from
`LeanDLRA.discrete_gronwall_le`. The example `inexact_iteration_error_example` checks that the
hypotheses can hold, using `T x = x / 2` on `ℝ`.

Not formalized here, and not claimed:

* The two-stage hybrid sampling (randomized greedy, then DEIM) is already in the library.
  The DEIM error bound `‖X - 𝒫 X‖ ≤ ‖(Sᵀ U)⁻¹‖ ‖X - U Uᵀ X‖` for orthonormal selections is
  `LeanDLRA.norm_sub_obliqueProj_mul_le_of_orthonormal` in `LeanDLRA/Matrix/Interpolation.lean`.
  A vector `x` is the case of one column. The switching heuristic is not a theorem and is not
  formalized.
* The inexact flexible GMRES-DSA result, with the residual gap `≤ ∑ ‖E_k‖ |y_k|`, is left out.
  It needs Arnoldi and GMRES theory, which Mathlib lacks, so it is out of scope for this slice.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2610_07653

/-- **Adaptive accuracy control for inexact fixed-point iterations** (arXiv 2610.07653, low-rank
SI-DSA; the abstract core of its tolerance argument). Let `T` be a `ρ`-contraction with `0 ≤ ρ`
and fixed point `x*`. If `x (k+1) = T (x k) + e k` with `‖e k‖ ≤ τ k`, then
`‖x k - x*‖ ≤ ρ^k ‖x 0 - x*‖ + ∑_{j<k} ρ^(k-1-j) τ j`.
The paper states this informally. Here `T` and `x*` are arbitrary and the sign of `τ` is not
assumed. The RTE-specific sweep error is not modelled. -/
theorem inexact_iteration_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E → E) {ρ : ℝ} (hρ : 0 ≤ ρ) (hT : ∀ x y : E, ‖T x - T y‖ ≤ ρ * ‖x - y‖)
    (xstar : E) (hfix : T xstar = xstar) (x e : ℕ → E) (τ : ℕ → ℝ)
    (hx : ∀ k, x (k + 1) = T (x k) + e k) (hτ : ∀ k, ‖e k‖ ≤ τ k) (k : ℕ) :
    ‖x k - xstar‖ ≤ ρ ^ k * ‖x 0 - xstar‖ + ∑ j ∈ range k, ρ ^ (k - 1 - j) * τ j := by
  have hstep : ∀ n < k, ‖x (n + 1) - xstar‖ ≤ ρ * ‖x n - xstar‖ + τ n := by
    intro n _
    calc ‖x (n + 1) - xstar‖ = ‖(T (x n) - T xstar) + e n‖ := by
          rw [hx n, hfix]
          congr 1
          abel
      _ ≤ ‖T (x n) - T xstar‖ + ‖e n‖ := norm_add_le _ _
      _ ≤ ρ * ‖x n - xstar‖ + τ n := add_le_add (hT _ _) (hτ n)
  exact LeanDLRA.discrete_gronwall_le (e := fun n => ‖x n - xstar‖) (b := τ) hρ hstep k le_rfl

/-- Non-vacuity of `inexact_iteration_error`: the contraction `T x = x / 2` on `ℝ` with fixed point
`0`, exact iterates `x n = (1/2)^n` and no error (`e = τ = 0`) satisfies the hypotheses. -/
theorem inexact_iteration_error_example (k : ℕ) :
    ‖(fun n : ℕ => (1 / 2 : ℝ) ^ n) k - 0‖ ≤
      (1 / 2 : ℝ) ^ k * ‖(fun n : ℕ => (1 / 2 : ℝ) ^ n) 0 - 0‖ +
        ∑ j ∈ range k, (1 / 2 : ℝ) ^ (k - 1 - j) * (fun _ : ℕ => (0 : ℝ)) j :=
  inexact_iteration_error (E := ℝ) (fun x => (1 / 2 : ℝ) * x) (ρ := 1 / 2) (by norm_num)
    (fun x y => by
      rw [← mul_sub, norm_mul]
      norm_num)
    0 (by simp) (fun n => (1 / 2 : ℝ) ^ n) (fun _ => 0) (fun _ => 0)
    (fun n => by simp [pow_succ]; ring) (fun _ => by simp) k

end LeanDLRA.Literature.P2610_07653
