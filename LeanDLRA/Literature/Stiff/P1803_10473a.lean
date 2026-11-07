import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 1803.10473: Low-rank Lie-Trotter splitting for stiff matrix ODEs

This module formalizes the rank and tangent-space facts of Sec. 3.2 and Sec. 8 of arXiv 1803.10473
for real square matrices `m × m`, with `Y = U S Vᵀ` and orthonormal columns `Uᵀ U = 1`, `Vᵀ V = 1`:

* `stiff_derivative_mem_tangent` (Sec. 3.2, tangent part): `A Y + Y Aᵀ` is the explicit sum
  `U B + C Vᵀ` and lies in the range of the tangent projector `P(Y)`.
* `rank_exp_congr` (Sec. 3.2, rank part): `e^{tA} Y e^{tAᵀ}` has the same rank as `Y` for all `t`.
  The paper cites Helmke–Moore for this claim and does not prove it; the statement is proved here.
* `riccati_term_tangent` (Sec. 8): `P(Y)(Y K Y) = Y K Y` for any square `K`, the identity the paper
  uses to split `G = Q - Y K Y` into the tangential part `P(Y)Q - YKY` and the residual
  `R = Q - P(Y)Q`. The residual bound `‖R‖ ≤ ε` is an assumption in the paper and is not formalized.

Not formalized: Lemma 1 (one-step error of the full versus low-rank nonlinear substep),
Proposition 2 (low-rank versus full-rank splitting) and Theorem 1 (global error of the low-rank
Lie-Trotter splitting). They need the local error bounds of the substeps and the parabolic
smoothing estimate `‖e^{tA}(AZ + ZA*)e^{tA*}‖ ≤ C_s e^{tω}‖Z‖ / t`, which are not in the library,
so they are left out. The rank-invariance statement is proved only for the congruence flow
`e^{tA} Y e^{tAᵀ}` with the exact matrix exponential; no Lie-Trotter splitting is involved.
The paper's real matrices use `Aᵀ` for its conjugate transpose `A*`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P1803_10473

variable {k k' m : Type*} [Fintype k] [Fintype k'] [Fintype m]

/-- **arXiv 1803.10473, Sec. 3.2 (tangent part).** For `Y = U S Vᵀ` with orthonormal `U`, `V`, the
matrix `A Y + Y Aᵀ = (A U) S Vᵀ + U (S (A V)ᵀ)` is a tangent vector at `Y`: it lies in the range of
the tangent projector `P(Y)` of the rank-`r` manifold. -/
theorem stiff_derivative_mem_tangent [DecidableEq k] [DecidableEq k'] {U : Matrix m k ℝ}
    {V : Matrix m k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (S : Matrix k k' ℝ)
    (A : Matrix m m ℝ) :
    A * (U * S * Vᵀ) + (U * S * Vᵀ) * Aᵀ ∈
      LinearMap.range (tangentProj U V : Matrix m m ℝ →ₗ[ℝ] Matrix m m ℝ) := by
  rw [mem_range_tangentProj hU hV]
  refine ⟨S * (A * V)ᵀ, A * U * S, ?_⟩
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  abel

/-- **arXiv 1803.10473, Sec. 3.2 (rank part).** The congruence flow `Y ↦ e^{tA} Y e^{tAᵀ}` preserves
the rank of `Y = U S Vᵀ` for every `t`, since `e^{tA}` and `e^{tAᵀ}` are invertible. -/
theorem rank_exp_congr [DecidableEq m] {U : Matrix m k ℝ} {V : Matrix m k' ℝ}
    (S : Matrix k k' ℝ) (A : Matrix m m ℝ) (t : ℝ) :
    (NormedSpace.exp (t • A) * (U * S * Vᵀ) * NormedSpace.exp (t • Aᵀ)).rank =
      (U * S * Vᵀ).rank := by
  have hA : IsUnit (NormedSpace.exp (t • A)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp (𝔸 := ℝ) _)
  have hB : IsUnit (NormedSpace.exp (t • Aᵀ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp (𝔸 := ℝ) _)
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hB,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hA]

/-- **arXiv 1803.10473, Sec. 8: the Riccati term is tangent.** For `Y = U S Vᵀ` with orthonormal
`U` and any square `K`, the tangent projector fixes `Y K Y`, i.e. `P(Y)(Y K Y) = Y K Y`. -/
theorem riccati_term_tangent [DecidableEq k] {U : Matrix m k ℝ} {V : Matrix m k' ℝ}
    (hU : Uᵀ * U = 1) (S : Matrix k k' ℝ) (K : Matrix m m ℝ) :
    tangentProj U V (U * S * Vᵀ * K * (U * S * Vᵀ)) = U * S * Vᵀ * K * (U * S * Vᵀ) := by
  have h : U * S * Vᵀ * K * (U * S * Vᵀ) = U * (S * Vᵀ * K * U * S * Vᵀ) := by
    simp only [Matrix.mul_assoc]
  rw [h]
  exact tangentProj_mul_left hU V _

/-- Non-vacuity: the orthonormality hypotheses hold for the identity bases, so the tangent and
Riccati statements apply, e.g. with `U = V = 1`, `S = 1`. -/
example (K : Matrix (Fin 2) (Fin 2) ℝ) :
    tangentProj (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ) *
          (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * K * ((1 : Matrix (Fin 2) (Fin 2) ℝ) *
          (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ) *
          (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * K * ((1 : Matrix (Fin 2) (Fin 2) ℝ) *
          (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ) :=
  riccati_term_tangent (V := (1 : Matrix (Fin 2) (Fin 2) ℝ)) (by simp) _ K

end LeanDLRA.Literature.P1803_10473
