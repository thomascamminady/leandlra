import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2610.36257: Dynamical tensor-train approximation for Wigner–Fokker–Planck

This module formalizes the abstract matrix-layer core of the projected Wigner operator (arXiv
2610.36257, Secs. 3.2 and 4.1–4.3). It proves `galerkin_cp_core`: for an operator in
Kronecker (CP) form `X ↦ ∑ₛ Aₛ X Bₛ` on `ℝ^{m × n}`, the Galerkin compression
`P = leftProj U * rightProj V` onto the matrices `U C Vᵀ` acts on coefficients as
`C ↦ ∑ₛ (Uᵀ Aₛ U) C (Vᵀ Bₛ V)`, with `P` an orthogonal projector when `Uᵀ U = 1` and `Vᵀ V = 1`.
The `example` after `galerkin_cp_core` checks that the orthonormality hypotheses can hold.

Differences from the paper and what is left out:

* The Wigner-specific form is not formalized. In Fourier variables the operator is multiplication
  by `(i/ħ) δV(x, η)`, a PDE setting that Mathlib does not cover. Only its abstract CP-form
  Kronecker structure, with arbitrary matrices `Aₛ`, `Bₛ` and real scalars, is proved here.
* The TT (ranks `λ`) form of `δV` and the operation-count claims `O(ρ r³)` and `O(λ² r³)` are
  not formalized. They are complexity statements, and the TT form needs a TT-level recursion
  that this slice does not build.
* Section 4 (TT projector splitting). The d = 1 case is matrix KSL. Its robust error bound is
  already proved in the library as `LeanDLRA.ksl_global_error` in
  `LeanDLRA/Integrators/ProjectorSplitting.lean`, so it is not duplicated here. The interleaved
  TT sweep (2d forward and 2d − 1 backward steps) is not formalized.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2610_36257

variable {k k' m n : Type*} [Fintype k] [Fintype k'] [Fintype m] [Fintype n]

/-- **Galerkin compression of a CP-form (Kronecker) operator** (arXiv 2610.36257, Secs. 3.2 and
4.1–4.3, abstract core). Let `Uᵀ U = 1` and `Vᵀ V = 1`, and let `P = leftProj U * rightProj V`
be the orthogonal projector onto the matrices `U C Vᵀ`. Then `P` is an orthogonal projector, and
for the operator `X ↦ ∑ₛ Aₛ X Bₛ` applied to `U C Vᵀ` the projection has the coefficient form
`U K Vᵀ` with `K = ∑ₛ (Uᵀ Aₛ U) C (Vᵀ Bₛ V)`. This is the projected core operator of the
paper, with `K` the compressed core of size `k × k'`. -/
theorem galerkin_cp_core [DecidableEq k] [DecidableEq k'] {ρ : ℕ} {U : Matrix m k ℝ}
    {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (A : Fin ρ → Matrix m m ℝ) (B : Fin ρ → Matrix n n ℝ) (C : Matrix k k' ℝ) :
    IsOrthProj (leftProj U * rightProj V : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) ∧
    (leftProj U * rightProj V : Matrix m n ℝ →L[ℝ] Matrix m n ℝ)
        (∑ s, A s * (U * C * Vᵀ) * B s)
      = U * (∑ s, (Uᵀ * A s * U) * C * (Vᵀ * B s * V)) * Vᵀ := by
  refine ⟨isOrthProj_leftProj_mul_rightProj hU hV, ?_⟩
  simp only [mul_apply_eq_comp, leftProj_apply, rightProj_apply, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_assoc]

/-- Non-vacuity of `galerkin_cp_core`: the identity matrices on `Fin 2` are orthonormal, and the
projector formula applies to the one-term operator `X ↦ X`. -/
example : IsOrthProj (leftProj (1 : Matrix (Fin 2) (Fin 2) ℝ) *
      rightProj (1 : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ]
        Matrix (Fin 2) (Fin 2) ℝ) :=
  (galerkin_cp_core (U := (1 : Matrix (Fin 2) (Fin 2) ℝ)) (V := (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (by simp) (by simp) (fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℝ)) 1).1

end LeanDLRA.Literature.P2610_36257
