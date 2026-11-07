import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2602.06808: DLRA for semiclassical Schrödinger with uncertainty

This module formalizes one result of arXiv 2602.06808 (Liu, Xu, Zhu), Lemma 2.2, equation (6), in a
finite-dimensional complex setting. The spatial variable has `m` grid points and the random
variable `n` grid points, so the inner product `⟨η, X_i W_j⟩_{x,ξ}` becomes the counting-measure
sum `∑ a, ∑ b, η a b * conj (X a i * W b j)`, with the paper's weights `dx` and `π(ξ) dξ`
absorbed into the counting measure. The tangent vector `η` is given by its components
`η_X, η_S, η_W` as in Lemma 2.1, the factors `X`, `W` have orthonormal columns, and the gauge
conditions (5) are assumed. The lemma proved here is the determination
`η_S,ij = ⟨η, X_i W_j⟩` from `η` under the gauge (eq. (6)).

Not formalized (left out, with reasons):
* Eqs. (7) and (8) of Lemma 2.2: they determine `η_W` and `η_X` and are not proved here.
* Theorem 2.1 (Galerkin projection equivalent to the factor equations): it lives in complex weighted
  `L²(ℝᵐ × ℝⁿ, π)` with a tensor-product structure that the library does not have, so it is
  left out.
* Lemma 2.3 (KSL substeps reduce to the K-, S- and L-equations): these are time-dependent evolution
  equations in infinite dimensions and are left out.
* Algorithm 2 (unconventional integrator): it is an algorithm, not a theorem, and is left out.

Core definitions: none are used. The tangent parametrization, the gauge conditions and the
inner product are written directly as complex matrix expressions, since the core library has no
complex tangent-space object for this factorization.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2602_06808

/-- **Lemma 2.2, eq. (6)** of arXiv 2602.06808, finite-dimensional complex version. Let
`ψ = X S Wᵀ` with orthonormal columns `Xᴴ X = 1`, `Wᴴ W = 1`, and let the tangent vector
`η = ηX S Wᵀ + X ηS Wᵀ + X S ηWᵀ` satisfy the gauge conditions `Xᴴ ηX = 0`, `Wᴴ ηW = 0`
(eq. (5)). Then `ηS i j = ⟨η, X_i W_j⟩`, where the inner product is the discrete `∑ a, ∑ b, η a b *
conj (X a i * W b j)`. The paper's `ξ`-weights are absorbed into the counting measure. -/
theorem gauge_S_component_eq_inner {m n r : ℕ}
    (X : Matrix (Fin m) (Fin r) ℂ) (W : Matrix (Fin n) (Fin r) ℂ)
    (S : Matrix (Fin r) (Fin r) ℂ)
    (ηX : Matrix (Fin m) (Fin r) ℂ) (ηS : Matrix (Fin r) (Fin r) ℂ)
    (ηW : Matrix (Fin n) (Fin r) ℂ) (η : Matrix (Fin m) (Fin n) ℂ)
    (hX : Xᴴ * X = 1) (hW : Wᴴ * W = 1)
    (hgX : Xᴴ * ηX = 0) (hgW : Wᴴ * ηW = 0)
    (hη : η = ηX * S * Wᵀ + X * ηS * Wᵀ + X * S * ηWᵀ) :
    ∀ i j, ηS i j = ∑ a, ∑ b, η a b * star (X a i * W b j) := by
  have hWT : Wᵀ * (Wᴴ)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hW, Matrix.transpose_one]
  have hηW : ηWᵀ * (Wᴴ)ᵀ = 0 := by
    rw [← Matrix.transpose_mul, hgW, Matrix.transpose_zero]
  have e1 : Xᴴ * (ηX * S * Wᵀ) * (Wᴴ)ᵀ = 0 := by
    have : Xᴴ * (ηX * S * Wᵀ) * (Wᴴ)ᵀ = (Xᴴ * ηX) * (S * (Wᵀ * (Wᴴ)ᵀ)) := by
      simp only [Matrix.mul_assoc]
    rw [this, hgX, hWT]
    simp
  have e2 : Xᴴ * (X * ηS * Wᵀ) * (Wᴴ)ᵀ = ηS := by
    have : Xᴴ * (X * ηS * Wᵀ) * (Wᴴ)ᵀ = (Xᴴ * X) * (ηS * (Wᵀ * (Wᴴ)ᵀ)) := by
      simp only [Matrix.mul_assoc]
    rw [this, hX, hWT]
    simp
  have e3 : Xᴴ * (X * S * ηWᵀ) * (Wᴴ)ᵀ = 0 := by
    have : Xᴴ * (X * S * ηWᵀ) * (Wᴴ)ᵀ = (Xᴴ * X) * (S * (ηWᵀ * (Wᴴ)ᵀ)) := by
      simp only [Matrix.mul_assoc]
    rw [this, hX, hηW]
    simp
  have key : ηS = Xᴴ * η * (Wᴴ)ᵀ := by
    have hsplit : Xᴴ * (ηX * S * Wᵀ + X * ηS * Wᵀ + X * S * ηWᵀ) * (Wᴴ)ᵀ
        = Xᴴ * (ηX * S * Wᵀ) * (Wᴴ)ᵀ + Xᴴ * (X * ηS * Wᵀ) * (Wᴴ)ᵀ
          + Xᴴ * (X * S * ηWᵀ) * (Wᴴ)ᵀ := by
      simp only [Matrix.mul_add, Matrix.add_mul]
    rw [hη, hsplit, e1, e2, e3, zero_add, add_zero]
  intro i j
  rw [key]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, star_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Non-vacuity: the hypotheses of `gauge_S_component_eq_inner` hold for `m = n = r = 1` with
`X = W = 1`, `ηX = ηW = 0`, `ηS = 3` and `η = X ηS Wᵀ`. -/
example : ∀ i j, (!![3] : Matrix (Fin 1) (Fin 1) ℂ) i j
    = ∑ a, ∑ b, (!![3] : Matrix (Fin 1) (Fin 1) ℂ) a b * star ((1 : Matrix (Fin 1) (Fin 1) ℂ) a i
      * (1 : Matrix (Fin 1) (Fin 1) ℂ) b j) :=
  gauge_S_component_eq_inner (X := 1) (W := 1) (S := 1) (ηX := 0) (ηS := !![3]) (ηW := 0)
    (η := !![3]) (by simp) (by simp) (by simp) (by simp) (by simp)

end LeanDLRA.Literature.P2602_06808
