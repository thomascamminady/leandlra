import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2201.12340: Low-rank power iteration for neutron criticality

Formalized here: the closed form of the simplified power iteration of Sec. 3 (display after
eq. (20)). For `C̃ = V Λ V⁻¹` and `D̃ = U⁻¹ Σ U` with `V`, `U` invertible, the map
`φ ↦ C̃ φ D̃` sends `V α U` to `V Λ α Σ U`, so its `k`-th iterate is `V Λᵏ α Σᵏ U`.
Matrices are real and carried by `Matrix (Fin n) (Fin m) ℝ`; no core definition applies to this
map, so it is defined locally as `powMap`.

Not formalized: the convergence statements (Lemma 3.1, Lemma 3.2, Theorem 3.3) and the
dynamical low-rank iteration of Sec. 2, which the paper states with a derivation that is not
checked here.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2201_12340

variable {n m : ℕ}

/-- The map `φ ↦ C̃ φ D̃` of Sec. 3 (eq. (19)), with `C̃ = V Λ V⁻¹` and `D̃ = U⁻¹ Σ U`.
Here `Λ = diag lam` and `Σ = diag sig`. -/
noncomputable def powMap (V : Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin m) (Fin m) ℝ)
    (lam : Fin n → ℝ) (sig : Fin m → ℝ) (φ : Matrix (Fin n) (Fin m) ℝ) :
    Matrix (Fin n) (Fin m) ℝ :=
  (V * Matrix.diagonal lam * V⁻¹) * φ * (U⁻¹ * Matrix.diagonal sig * U)

/-- **Closed form of the simplified power iteration** (arXiv 2201.12340, Sec. 3, display after
(20)). With `C̃ = V Λ V⁻¹`, `D̃ = U⁻¹ Σ U`, `k` applications of the map to `V α U` give
`V Λᵏ α Σᵏ U`. -/
theorem powMap_iterate (V : Matrix (Fin n) (Fin n) ℝ) (hV : IsUnit V)
    (U : Matrix (Fin m) (Fin m) ℝ) (hU : IsUnit U)
    (lam : Fin n → ℝ) (sig : Fin m → ℝ) (α : Matrix (Fin n) (Fin m) ℝ) (k : ℕ) :
    (powMap V U lam sig)^[k] (V * α * U) =
      V * (Matrix.diagonal (fun i => lam i ^ k) * α *
        Matrix.diagonal (fun j => sig j ^ k)) * U := by
  have hV' : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V ((Matrix.isUnit_iff_isUnit_det V).mp hV)
  have hU' : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det U).mp hU)
  have hV'' : ∀ Y : Matrix (Fin n) (Fin m) ℝ, V⁻¹ * (V * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hV', Matrix.one_mul]
  have hU'' : ∀ Y : Matrix (Fin m) (Fin m) ℝ, U * (U⁻¹ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hU', Matrix.one_mul]
  have h1 : ∀ k : ℕ, Matrix.diagonal lam * Matrix.diagonal (fun i => lam i ^ k) =
      Matrix.diagonal (fun i => lam i ^ (k + 1)) := fun k => by
    simp only [Matrix.diagonal_mul_diagonal, pow_succ']
  have h2 : ∀ k : ℕ, Matrix.diagonal (fun j => sig j ^ k) * Matrix.diagonal sig =
      Matrix.diagonal (fun j => sig j ^ (k + 1)) := fun k => by
    simp only [Matrix.diagonal_mul_diagonal, pow_succ]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold powMap
    simp only [Matrix.mul_assoc, hV'', hU'']
    rw [← Matrix.mul_assoc (Matrix.diagonal lam) (Matrix.diagonal (fun i => lam i ^ k)), h1 k,
      ← Matrix.mul_assoc (Matrix.diagonal (fun j => sig j ^ k)) (Matrix.diagonal sig), h2 k]

end LeanDLRA.Literature.P2201_12340
