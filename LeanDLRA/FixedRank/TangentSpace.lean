import LeanDLRA.Matrix.Projectors

/-!
# Tangent vectors of the fixed-rank manifold

Results about the tangent space `T_Y 𝓜_r = range P(Y)` at `Y = U S Vᵀ` (orthonormal `U`, `V`) that
several papers use, stated once in the core vocabulary (`LeanDLRA.tangentProj`,
`LeanDLRA.mem_range_tangentProj`).

## Main results

* `LeanDLRA.mul_add_mul_mem_range_tangentProj`: the Sylvester-type field `A_x Y + Y A_y` is tangent
  at `Y = U S Vᵀ` for all square `A_x`, `A_y` and every core `S` (invertible or not). The stiff
  flows of arXiv 2010.05249 (`A_x X + X A_y`) and arXiv 1803.10473 (`A Y + Y Aᵀ`) are instances
  (`P2010_05249.stiff_derivative_mem_tangent'`, `P1803_10473.stiff_derivative_mem_tangent`).
-/

open scoped Matrix

namespace LeanDLRA

variable {k k' m n : Type*} [Fintype k] [Fintype k'] [Fintype m] [Fintype n]

/-- **Sylvester-type fields are tangent.** For `Y = U S Vᵀ` with orthonormal `U`, `V`, the matrix
`A_x Y + Y A_y = (A_x U S) Vᵀ + U (S Vᵀ A_y)` lies in the range of the tangent projector `P(Y)`
of the rank-`r` manifold, for arbitrary square `A_x`, `A_y` and any (not necessarily
invertible) `S`. -/
theorem mul_add_mul_mem_range_tangentProj [DecidableEq k] [DecidableEq k'] {U : Matrix m k ℝ}
    {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (S : Matrix k k' ℝ)
    (Ax : Matrix m m ℝ) (Ay : Matrix n n ℝ) :
    Ax * (U * S * Vᵀ) + (U * S * Vᵀ) * Ay ∈
      LinearMap.range (tangentProj U V : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ) := by
  rw [mem_range_tangentProj hU hV]
  refine ⟨S * Vᵀ * Ay, Ax * U * S, ?_⟩
  simp only [Matrix.mul_assoc]
  abel

end LeanDLRA
