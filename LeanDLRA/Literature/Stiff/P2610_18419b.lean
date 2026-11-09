import Mathlib

/-!
# Results of arXiv 2610.18419: Non-iterative Sylvester solvers for implicit DLRA

This module formalizes the linear-algebra core of Section 4 of arXiv 2610.18419 (Saha, Yang, Yin),
for real matrices. It uses only Mathlib: the statements concern generic matrices, and the
library has no Sylvester or Woodbury object to reuse.

* `shift_mul_inv_isUnit` (abstract core of Lemma 4.3 (i)): for a positive definite `M` and a
  positive semidefinite `S`, and scalars `Δt > 0`, `λ > 0`, the matrix `Δt M⁻¹ S + λ I` is
  invertible. The paper applies this to `Â_j = Δt M_x⁻¹ Â_x + λ_j I` and to
  `Â_j + Û V̂ᵀ = A + λ_j I = Δt M_x⁻¹ A_x + λ_j I` in (4.18) (K-equation; `M_y`, `A_y`, `Â_y` for
  the L-equation).
* `bDiag_posDef` (part of Lemma 4.3 (i)): for `Δt > 0`, `α ≤ 0` and `A_y ⪰ 0`, the matrix
  `B = (1 - Δt α) I + Δt Vᵀ A_y V` is positive definite. Its eigenvalues are the shifts `λ_j`.
* `capacitance_isUnit` (Lemma 4.3 (ii)): if `Â` and `Â + Û V̂ᵀ` are invertible, then the
  capacitance matrix `I + V̂ᵀ Â⁻¹ Û` is invertible (Sylvester's determinant identity).
* `woodbury_inv` (Lemma 4.4, Eq. (4.19)): the Sherman-Morrison-Woodbury formula
  `(Â + Û V̂ᵀ)⁻¹ = Â⁻¹ - Â⁻¹ Û (I + V̂ᵀ Â⁻¹ Û)⁻¹ V̂ᵀ Â⁻¹`, from Mathlib's Woodbury identity
  with `C = I`.
* `solution_formula` (Eq. (4.20)): the solution `y = (Â + Û V̂ᵀ)⁻¹ c` in explicit form.
* `example`: a concrete `2 × 2` instance in which the capacitance hypothesis holds.

The paper's `Û, V̂ ∈ ℝ^{m×2}` are the case `p = Fin 2`. The lemmas here take an arbitrary
index type `p` for the rank.

Not formalized (left out):
* Lemma 4.2, that the periodic stiffness matrices `A_x`, `A_y` and their `(2k+1)`-banded parts
  are positive semidefinite. Its proof uses the periodic finite element assembly, which the
  library does not have. So the PSD hypotheses of Lemma 4.3 (i) are not derived here:
  `shift_mul_inv_isUnit` takes a general PSD `S`, and Lemma 4.2 must supply it.
* The periodic wrap-around structure (4.12)-(4.16) of `A`, the identification
  `A = Â + Û V̂ᵀ` and the claim that `Â_j` is banded.
* The complexity and storage counts, and the Algorithms 4.1 and 4.2 as procedures.
* The Sherman-Morrison-Woodbury solve in (4.21)-(4.23) as a numerical algorithm.

Core definitions: none. The file imports only Mathlib, because the paper's Sylvester and Woodbury
objects have no counterpart in the library's `Foundations/`, `Integrators/` or `Matrix/` modules.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2610_18419

variable {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]

/-- **Lemma 4.3 (i), abstract core** (arXiv 2610.18419, Lemma 4.3 (i)).
For a positive definite `M` (the mass matrix `M_x` or `M_y`), a positive semidefinite `S` (the
stiffness matrix `A_x` or `A_y`, or its banded part), `Δt > 0` and `λ > 0`, the matrix
`Δt M⁻¹ S + λ I` is invertible. The paper applies it to `Â_j = Δt M_x⁻¹ Â_x + λ_j I` and to
`Â_j + Û V̂ᵀ = A + λ_j I = Δt M_x⁻¹ A_x + λ_j I` (K-equation; with `M_y`, `A_y`, `Â_y` for the
L-equation). The PSD property of `A_x`, `Â_x` (and `A_y`, `Â_y`) is Lemma 4.2, which is not
formalized here, so it enters as the hypothesis `hS`. -/
theorem shift_mul_inv_isUnit {M S : Matrix m m ℝ} {Δt lam : ℝ} (hM : M.PosDef)
    (hS : S.PosSemidef) (hΔ : 0 < Δt) (hl : 0 < lam) :
    IsUnit (Δt • (M⁻¹ * S) + lam • (1 : Matrix m m ℝ)) := by
  have hMinv : M⁻¹ * M = 1 :=
    Matrix.nonsing_inv_mul M ((Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit)
  have key : Δt • (M⁻¹ * S) + lam • (1 : Matrix m m ℝ) = M⁻¹ * (Δt • S + lam • M) := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hMinv]
  have hP : (Δt • S + lam • M).PosDef := by
    rw [add_comm]
    exact (hM.smul hl).add_posSemidef (hS.smul hΔ.le)
  rw [key]
  exact hM.inv.isUnit.mul hP.isUnit

omit [DecidableEq m] in
/-- **Lemma 4.3 (i), the matrix `B`** (arXiv 2610.18419, proof of Lemma 4.3 (i)).
For `Δt > 0`, `α ≤ 0` and a positive semidefinite `A_y`, the matrix
`B = (1 - Δt α) I_r + Δt Vᵀ A_y V` is positive definite, for any `V : Matrix m (Fin r) ℝ`. -/
theorem bDiag_posDef {r : ℕ} {A : Matrix m m ℝ} {V : Matrix m (Fin r) ℝ}
    {Δt α : ℝ} (hΔ : 0 < Δt) (hα : α ≤ 0) (hA : A.PosSemidef) :
    ((1 - Δt * α) • (1 : Matrix (Fin r) (Fin r) ℝ) + Δt • (Vᵀ * A * V)).PosDef := by
  have hc : 0 < 1 - Δt * α := by nlinarith
  have hV : (Vᵀ * A * V).PosSemidef := by
    have := Matrix.PosSemidef.conjTranspose_mul_mul_same hA V
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  exact (Matrix.PosDef.one.smul hc).add_posSemidef (hV.smul hΔ.le)

/-- **Lemma 4.3 (ii)** (arXiv 2610.18419, Lemma 4.3 (ii)).
If `Â` and `Â + Û V̂ᵀ` are invertible, then `I + V̂ᵀ Â⁻¹ Û` is invertible. The paper proves this
by the determinant identity. Here `Û, V̂ : Matrix m p ℝ`, and `p = Fin 2` in the paper. -/
theorem capacitance_isUnit {A : Matrix m m ℝ} {U V : Matrix m p ℝ} (hA : IsUnit A)
    (hAUV : IsUnit (A + U * Vᵀ)) : IsUnit (1 + Vᵀ * A⁻¹ * U) := by
  have hdetA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdetA
  have hfac' : A + U * Vᵀ = A * (1 + A⁻¹ * U * Vᵀ) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAinv,
      Matrix.one_mul]
  have hfac : (A + U * Vᵀ).det = A.det * (1 + Vᵀ * (A⁻¹ * U)).det := by
    rw [hfac', Matrix.det_mul, Matrix.det_one_add_mul_comm]
  have hdet : IsUnit ((A + U * Vᵀ).det) := (Matrix.isUnit_iff_isUnit_det _).mp hAUV
  rw [hfac] at hdet
  have hcap : IsUnit (1 + Vᵀ * (A⁻¹ * U)).det := isUnit_of_mul_isUnit_right hdet
  have heq : (1 + Vᵀ * A⁻¹ * U : Matrix p p ℝ) = 1 + Vᵀ * (A⁻¹ * U) := by
    simp [Matrix.mul_assoc]
  rw [heq]
  exact (Matrix.isUnit_iff_isUnit_det _).mpr hcap

/-- **Lemma 4.4** (arXiv 2610.18419, Lemma 4.4, Sherman-Morrison-Woodbury, Eq. (4.19)).
If `Â` is invertible and `I + V̂ᵀ Â⁻¹ Û` is invertible, then
`(Â + Û V̂ᵀ)⁻¹ = Â⁻¹ - Â⁻¹ Û (I + V̂ᵀ Â⁻¹ Û)⁻¹ V̂ᵀ Â⁻¹`. -/
theorem woodbury_inv {A : Matrix m m ℝ} {U V : Matrix m p ℝ} (hA : IsUnit A)
    (hcap : IsUnit (1 + Vᵀ * A⁻¹ * U)) :
    (A + U * Vᵀ)⁻¹ = A⁻¹ - A⁻¹ * U * (1 + Vᵀ * A⁻¹ * U)⁻¹ * Vᵀ * A⁻¹ := by
  have h := Matrix.add_mul_mul_inv_eq_sub A U (1 : Matrix p p ℝ) Vᵀ hA isUnit_one
    (by simpa using hcap)
  simpa [Matrix.mul_one] using h

/-- **Eq. (4.20)** (arXiv 2610.18419): under the hypotheses of `woodbury_inv`, the solution of
`(Â + Û V̂ᵀ) y = c` is `y = Â⁻¹ c - Â⁻¹ Û (I + V̂ᵀ Â⁻¹ Û)⁻¹ (V̂ᵀ Â⁻¹ c)`. -/
theorem solution_formula {A : Matrix m m ℝ} {U V : Matrix m p ℝ} {r : Type*}
    (hA : IsUnit A) (hcap : IsUnit (1 + Vᵀ * A⁻¹ * U)) (c : Matrix m r ℝ) :
    (A + U * Vᵀ)⁻¹ * c =
      A⁻¹ * c - A⁻¹ * U * (1 + Vᵀ * A⁻¹ * U)⁻¹ * (Vᵀ * A⁻¹ * c) := by
  rw [woodbury_inv hA hcap]
  simp [Matrix.sub_mul, Matrix.mul_assoc]

/-- Non-vacuity: for `A = I`, `U = V = I` on `Fin 2` the capacitance `I + Vᵀ A⁻¹ U` is `2 I`,
which is invertible, so `capacitance_isUnit` and `woodbury_inv` apply. -/
example : IsUnit (1 + (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
    * (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp [Matrix.det_fin_two]

end LeanDLRA.Literature.P2610_18419
