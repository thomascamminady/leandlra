import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2308.08888: Low-rank Strang splitting for strongly damped wave equations

The paper states no theorem.  This module formalizes a property implicit in its algorithms, that
of the first QR step of Algorithm 3.1 `DLR_L`.

Algorithm 3.1 computes `Ũ₁ Ŝ = Δ₁ Ṽ₀` (step 1) and returns a new basis `Ũ₁`. The module proves,
for any `Δ₁`, any `V₀` and any `Ũ₁` with orthonormal columns and `Ũ₁ Ŝ = Δ₁ V₀` for some `Ŝ`:

* `dlrL_implicit`: `(I - Ũ₁Ũ₁ᵀ) Δ₁ = (I - Ũ₁Ũ₁ᵀ) Δ₁ (I - V₀V₀ᵀ)` and
  `‖Δ₁ - Ũ₁Ũ₁ᵀ Δ₁‖ ≤ ‖Δ₁ (I - V₀V₀ᵀ)‖` (Frobenius norm).

The paper does not state this property; it is a direct consequence of step 1 of Algorithm 3.1
(the capture property of a K-step). The hypotheses are the QR relation of step 1
and orthonormality of `Ũ₁`, nothing else. Orthonormality of `V₀` is not needed, and the rank `r`
and the Stiefel conditions of the paper are not used.

Core definitions used: `leftProj`, `isOrthProj_leftProj` (from `LeanDLRA.Matrix.Projectors`),
`IsOrthProj.norm_sub_le_of_mem_range` (from `LeanDLRA.Foundations.Projector`), and the
Frobenius norm (`open scoped LeanDLRA.Frobenius`). Local definitions added: none.

Not formalized, and why:
* Scheme (3.6), the low-rank Strang composition `L_{τ,r}` of the substeps `Φ̃ˣ, Φ̃ʸ, Φ̃ᶠ`, is a
  definition of a numerical scheme, not a theorem. The paper states no error theorem for it;
  its convergence orders are only tested numerically (Tables 1 and 2). Nothing is proved here.
* The paper's Algorithms 3.2 to 3.4 (`DLR_FN`, `DLR_FL`) are algorithms without claims.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2308_08888

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

/-- **Algorithm 3.1 `DLR_L`, implicit property** (arXiv 2308.08888, Algorithm 3.1, step 1
`Ũ₁ Ŝ = Δ₁ Ṽ₀`, with `Ũ₁` having orthonormal columns).  The projector `I - Ũ₁Ũ₁ᵀ` onto the
orthogonal complement of `range Ũ₁` annihilates the columns of `Δ₁ V₀`, so
`(I - Ũ₁Ũ₁ᵀ) Δ₁ = (I - Ũ₁Ũ₁ᵀ) Δ₁ (I - V₀V₀ᵀ)`, and the remainder is bounded by the normal part
`‖Δ₁ (I - V₀V₀ᵀ)‖` in the Frobenius norm.  Only the QR relation and `Ũ₁ᵀ Ũ₁ = 1` are assumed;
`V₀` is arbitrary. -/
theorem dlrL_implicit [DecidableEq m] [DecidableEq n] [DecidableEq k]
    (Δ₁ : Matrix m n ℝ) (V₀ : Matrix n k ℝ) {U₁ : Matrix m k ℝ} {S : Matrix k k ℝ}
    (hU₁ : U₁ᵀ * U₁ = 1) (hQR : U₁ * S = Δ₁ * V₀) :
    (1 - U₁ * U₁ᵀ) * Δ₁ = (1 - U₁ * U₁ᵀ) * Δ₁ * (1 - V₀ * V₀ᵀ) ∧
      ‖Δ₁ - U₁ * U₁ᵀ * Δ₁‖ ≤ ‖Δ₁ * (1 - V₀ * V₀ᵀ)‖ := by
  have hUS : (1 - U₁ * U₁ᵀ) * (Δ₁ * V₀) = 0 := by
    rw [← hQR]
    rw [show (1 - U₁ * U₁ᵀ) * (U₁ * S) = (U₁ - U₁ * (U₁ᵀ * U₁)) * S by
      simp [Matrix.sub_mul, Matrix.mul_assoc], hU₁]
    simp
  have h2 : (1 - U₁ * U₁ᵀ) * Δ₁ * V₀ = 0 := by
    rw [Matrix.mul_assoc]
    exact hUS
  have hid : (1 - U₁ * U₁ᵀ) * Δ₁ = (1 - U₁ * U₁ᵀ) * Δ₁ * (1 - V₀ * V₀ᵀ) := by
    simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h2, Matrix.zero_mul,
      sub_zero]
  refine ⟨hid, ?_⟩
  have hsub : Δ₁ - U₁ * U₁ᵀ * Δ₁ = (1 - U₁ * U₁ᵀ) * Δ₁ := by
    simp [Matrix.sub_mul]
  rw [hsub, hid]
  have hP : IsOrthProj (leftProj U₁ : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
    isOrthProj_leftProj hU₁
  have h := hP.norm_sub_le_of_mem_range (Δ₁ * (1 - V₀ * V₀ᵀ)) 0 (map_zero _)
  have hrw : (1 - U₁ * U₁ᵀ) * Δ₁ * (1 - V₀ * V₀ᵀ) =
      Δ₁ * (1 - V₀ * V₀ᵀ) - leftProj U₁ (Δ₁ * (1 - V₀ * V₀ᵀ)) := by
    simp only [leftProj_apply, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [hrw]
  simpa only [sub_zero] using h

/-- Non-vacuity: `Δ₁ = [[0,1],[1,0]]`, `V₀ = (0,1)ᵀ`, `Ũ₁ = (1,0)ᵀ`, `Ŝ = 1` satisfy the
hypotheses of `dlrL_implicit`, so its conclusion applies to this instance (there the remainder
`(I - Ũ₁Ũ₁ᵀ) Δ₁ = [[0,0],[1,0]]` is nonzero). -/
example := by
  have hU : (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) =
      1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hQR : (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) * (!![1] : Matrix (Fin 1) (Fin 1) ℝ) =
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) * (!![0; 1] : Matrix (Fin 2) (Fin 1) ℝ) := by
    ext i j
    fin_cases i
    · fin_cases j
      simp
    · fin_cases j
      simp
  exact dlrL_implicit (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)
    (!![0; 1] : Matrix (Fin 2) (Fin 1) ℝ) hU hQR

end LeanDLRA.Literature.P2308_08888
