import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.LowRankDistance

/-!
# Results of arXiv 2606.24190: DLR methods for the Wigner equation I: separable difference potential

This module formalizes one result of arXiv 2606.24190 (Shao and Shao), Sec. 4.1, on the best
rank-`r` approximation. The paper states, as a remark on its numerical test, that the solution
of its DLRA algorithm cannot be more accurate than the best rank-`r` approximation of the
reference solution. Here `distLR r X` (from `LeanDLRA.Matrix.LowRankDistance`) is that best
error. The theorem `distLR_le_norm_sub_factored` proves the lower bound for every approximant
of DLRA form `U * S * Vᵀ` with `U : m × r`, `S : r × r`, `V : n × r`, which covers any
rank-`r` factorization such as `X(t) S(t) K(t)ᵀ` in the paper's (3.8). The identification of
`distLR r X` with the `(r+1)`-th singular value (Eckart–Young, stated in the paper) is not
formalized. The example checks that the statement applies to arbitrary factors.

Core definitions used: `LeanDLRA.distLR` and `LeanDLRA.lowRankSet` (Frobenius norm, via
`open scoped LeanDLRA.Frobenius`). No local definitions are added.

Not formalized: the KSL substep equations (1.17)-(1.19) and the discrete scheme (3.1), (3.4),
(3.7). They are stated in the paper for the L²-projector `P_f` and for the coefficient
matrices `A_u`, `B_u`, `C_s`, `D_s` of the separable difference potential (2.3), which need
L² inner products over `Ω_x × Ω_k`, and the core `IsKSLStep` covers only the abstract splitting.
Also not formalized: the cost statements of Sec. 3.3, which are out of scope.
-/

namespace LeanDLRA.Literature.P2606_24190

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **Best rank-`r` lower bound for DLRA factorizations (arXiv 2606.24190, Sec. 4.1).**
For a matrix `X` and any factors `U : m × r`, `S : r × r`, `V : n × r`, the error of the
approximant `U * S * Vᵀ` is at least the best rank-`r` error `distLR r X`. The paper's remark
concerns the rank-`r` solution of its DLRA algorithm, which has this form; the paper gives no
proof and this file proves the inequality from the definition of `distLR`. -/
theorem distLR_le_norm_sub_factored {r : ℕ} (X : Matrix m n ℝ) (U : Matrix m (Fin r) ℝ)
    (S : Matrix (Fin r) (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) :
    LeanDLRA.distLR r X ≤ ‖X - U * S * V.transpose‖ := by
  apply LeanDLRA.distLR_le_norm_sub
  refine le_trans (Matrix.rank_mul_le_left (U * S) V.transpose) ?_
  simpa using Matrix.rank_le_card_width (U * S)

/-- Non-vacuity: the bound applies to arbitrary `2 × 1` factors `U` and `V` with `S = 1`. -/
example (X : Matrix (Fin 2) (Fin 2) ℝ) (U V : Matrix (Fin 2) (Fin 1) ℝ) :
    LeanDLRA.distLR 1 X ≤ ‖X - U * (1 : Matrix (Fin 1) (Fin 1) ℝ) * V.transpose‖ :=
  distLR_le_norm_sub_factored X U 1 V

end LeanDLRA.Literature.P2606_24190
