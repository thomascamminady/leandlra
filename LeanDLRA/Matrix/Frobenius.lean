import Mathlib
import LeanDLRA.LinearAlgebra.Frobenius.Defs

/-!
# The Frobenius inner product on real matrices

Dynamical low-rank approximation (DLRA) works on the space `ℝ^{m × n}` equipped with the
Frobenius inner product `⟪A, B⟫ = ∑ᵢ ∑ⱼ Aᵢⱼ Bᵢⱼ = tr (Aᵀ B)` [KochLubich2007, §2]. The scoped
instances (`open scoped LeanDLRA.Frobenius`) and the matrix operations as continuous linear maps
are defined in `LeanDLRA/LinearAlgebra/Frobenius/Defs.lean`. This file proves their properties.

## Main results

* `LeanDLRA.Frobenius.inner_eq_trace`: `⟪A, B⟫ = tr (Aᵀ B)`.
* `LeanDLRA.Frobenius.inner_mul_left`, `inner_mul_right`: the adjoint identities
  `⟪A B, C⟫ = ⟪B, Aᵀ C⟫ = ⟪A, C Bᵀ⟫`.
* `LeanDLRA.Frobenius.inner_transpose`, `norm_mul_of_orthonormal`,
  `norm_mul_transpose_of_orthonormal`: invariance under transposition and under multiplication by
  matrices with orthonormal columns.
* `LeanDLRA.Frobenius.hasDerivWithinAt_mul`, `hasDerivWithinAt_mul_mul`,
  `hasDerivWithinAt_transpose`: product rule for matrix-valued curves and differentiation of the
  transpose, as needed for the gauge-fixed factor ODEs [KochLubich2007, Prop. 2.1] and for
  factor-level integrators.

## References

* [KochLubich2007]
* [LubichOseledets2014, §2]
* [CerutiLubich2022, §2]
-/

open scoped Matrix RealInnerProductSpace

namespace LeanDLRA.Frobenius

variable {k l m n : Type*} [Fintype k] [Fintype l] [Fintype m] [Fintype n]

/-! ### The Frobenius inner product -/

/-- The Frobenius inner product as a trace: `⟪A, B⟫ = tr (Aᵀ B)`. -/
theorem inner_eq_trace (A B : Matrix m n ℝ) : ⟪A, B⟫ = Matrix.trace (Aᵀ * B) := by
  simp only [inner_def, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- Left multiplication is adjoint to left multiplication by the transpose:
`⟪A B, C⟫ = ⟪B, Aᵀ C⟫`. -/
theorem inner_mul_left (A : Matrix m l ℝ) (B : Matrix l n ℝ) (C : Matrix m n ℝ) :
    ⟪A * B, C⟫ = ⟪B, Aᵀ * C⟫ := by
  rw [inner_eq_trace, inner_eq_trace, Matrix.transpose_mul, Matrix.mul_assoc]

/-- Right multiplication is adjoint to right multiplication by the transpose:
`⟪A B, C⟫ = ⟪A, C Bᵀ⟫`. -/
theorem inner_mul_right (A : Matrix m l ℝ) (B : Matrix l n ℝ) (C : Matrix m n ℝ) :
    ⟪A * B, C⟫ = ⟪A, C * Bᵀ⟫ := by
  rw [inner_eq_trace, inner_eq_trace, Matrix.transpose_mul, ← Matrix.mul_assoc Aᵀ C Bᵀ,
    Matrix.trace_mul_cycle Aᵀ C Bᵀ]

/-- Moving a left factor out of the second argument: `⟪A, B C⟫ = ⟪Bᵀ A, C⟫`. -/
theorem inner_mul_left' (A : Matrix m n ℝ) (B : Matrix m l ℝ) (C : Matrix l n ℝ) :
    ⟪A, B * C⟫ = ⟪Bᵀ * A, C⟫ := by
  rw [real_inner_comm, inner_mul_left, real_inner_comm]

/-- Moving a right factor out of the second argument: `⟪A, B C⟫ = ⟪A Cᵀ, B⟫`. -/
theorem inner_mul_right' (A : Matrix m n ℝ) (B : Matrix m l ℝ) (C : Matrix l n ℝ) :
    ⟪A, B * C⟫ = ⟪A * Cᵀ, B⟫ := by
  rw [real_inner_comm, inner_mul_right, real_inner_comm]

/-- Transposition preserves the Frobenius inner product. -/
theorem inner_transpose (A B : Matrix m n ℝ) : ⟪Aᵀ, Bᵀ⟫ = ⟪A, B⟫ := by
  simp only [inner_def, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- An entry is bounded by the Frobenius norm. -/
theorem abs_apply_le_norm (A : Matrix m n ℝ) (i : m) (j : n) : |A i j| ≤ ‖A‖ :=
  Matrix.norm_apply_le_frobenius_norm A i j

/-! ### Isometries: matrices with orthonormal columns -/

/-- Left multiplication by a matrix with orthonormal columns (`Uᵀ U = 1`) is an isometry. -/
theorem norm_mul_of_orthonormal [DecidableEq k] {U : Matrix m k ℝ} (hU : Uᵀ * U = 1)
    (X : Matrix k n ℝ) : ‖U * X‖ = ‖X‖ := by
  have h : ‖U * X‖ ^ 2 = ‖X‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_mul_left,
      ← Matrix.mul_assoc, hU, Matrix.one_mul]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- Right multiplication by the transpose of a matrix with orthonormal columns (`Vᵀ V = 1`)
is an isometry. -/
theorem norm_mul_transpose_of_orthonormal [DecidableEq k] {V : Matrix n k ℝ} (hV : Vᵀ * V = 1)
    (X : Matrix m k ℝ) : ‖X * Vᵀ‖ = ‖X‖ := by
  rw [← norm_transpose, Matrix.transpose_mul, Matrix.transpose_transpose,
    norm_mul_of_orthonormal hV, norm_transpose]

/-- Inner products are preserved by left multiplication with orthonormal columns. -/
theorem inner_mul_mul_of_orthonormal [DecidableEq k] {U : Matrix m k ℝ} (hU : Uᵀ * U = 1)
    (X Y : Matrix k n ℝ) : ⟪U * X, U * Y⟫ = ⟪X, Y⟫ := by
  rw [inner_mul_left, ← Matrix.mul_assoc, hU, Matrix.one_mul]

/-! ### Derivatives of matrix-valued curves -/

section Deriv

variable {s : Set ℝ} {t : ℝ}

/-- Product rule for (rectangular) matrix-valued curves, within a set. -/
theorem hasDerivWithinAt_mul {K : ℝ → Matrix m l ℝ} {L : ℝ → Matrix l n ℝ}
    {K' : Matrix m l ℝ} {L' : Matrix l n ℝ} (hK : HasDerivWithinAt K K' s t)
    (hL : HasDerivWithinAt L L' s t) :
    HasDerivWithinAt (fun t => K t * L t) (K' * L t + K t * L') s t := by
  have h := (mulCLM : Matrix m l ℝ →L[ℝ] Matrix l n ℝ →L[ℝ] Matrix m n ℝ)
    |>.hasDerivWithinAt_of_bilinear hK hL
  simp only [mulCLM_apply] at h
  rwa [add_comm] at h

/-- Product rule for (rectangular) matrix-valued curves. -/
theorem hasDerivAt_mul {K : ℝ → Matrix m l ℝ} {L : ℝ → Matrix l n ℝ}
    {K' : Matrix m l ℝ} {L' : Matrix l n ℝ} (hK : HasDerivAt K K' t) (hL : HasDerivAt L L' t) :
    HasDerivAt (fun t => K t * L t) (K' * L t + K t * L') t := by
  rw [← hasDerivWithinAt_univ] at hK hL ⊢
  exact hasDerivWithinAt_mul hK hL

/-- Product rule for a triple product `K L M` of matrix-valued curves (e.g. `U S Vᵀ`), within a
set. -/
theorem hasDerivWithinAt_mul_mul {K : ℝ → Matrix m k ℝ} {L : ℝ → Matrix k l ℝ}
    {M : ℝ → Matrix l n ℝ} {K' : Matrix m k ℝ} {L' : Matrix k l ℝ} {M' : Matrix l n ℝ}
    (hK : HasDerivWithinAt K K' s t) (hL : HasDerivWithinAt L L' s t)
    (hM : HasDerivWithinAt M M' s t) :
    HasDerivWithinAt (fun t => K t * L t * M t)
      (K' * L t * M t + K t * L' * M t + K t * L t * M') s t := by
  have h := hasDerivWithinAt_mul (hasDerivWithinAt_mul hK hL) hM
  rwa [Matrix.add_mul] at h

/-- Product rule for a triple product `K L M` of matrix-valued curves. -/
theorem hasDerivAt_mul_mul {K : ℝ → Matrix m k ℝ} {L : ℝ → Matrix k l ℝ}
    {M : ℝ → Matrix l n ℝ} {K' : Matrix m k ℝ} {L' : Matrix k l ℝ} {M' : Matrix l n ℝ}
    (hK : HasDerivAt K K' t) (hL : HasDerivAt L L' t) (hM : HasDerivAt M M' t) :
    HasDerivAt (fun t => K t * L t * M t)
      (K' * L t * M t + K t * L' * M t + K t * L t * M') t := by
  have h := hasDerivAt_mul (hasDerivAt_mul hK hL) hM
  rwa [Matrix.add_mul] at h

/-- A constant left factor passes through the derivative, within a set. -/
theorem hasDerivWithinAt_const_mul (M : Matrix m l ℝ) {K : ℝ → Matrix l n ℝ}
    {K' : Matrix l n ℝ} (hK : HasDerivWithinAt K K' s t) :
    HasDerivWithinAt (fun t => M * K t) (M * K') s t := by
  simpa using hasDerivWithinAt_mul (hasDerivWithinAt_const t s M) hK

/-- A constant left factor passes through the derivative. -/
theorem hasDerivAt_const_mul (M : Matrix m l ℝ) {K : ℝ → Matrix l n ℝ}
    {K' : Matrix l n ℝ} (hK : HasDerivAt K K' t) :
    HasDerivAt (fun t => M * K t) (M * K') t := by
  simpa using hasDerivAt_mul (hasDerivAt_const t M) hK

/-- A constant right factor passes through the derivative, within a set. -/
theorem hasDerivWithinAt_mul_const (M : Matrix l n ℝ) {K : ℝ → Matrix m l ℝ}
    {K' : Matrix m l ℝ} (hK : HasDerivWithinAt K K' s t) :
    HasDerivWithinAt (fun t => K t * M) (K' * M) s t := by
  simpa using hasDerivWithinAt_mul hK (hasDerivWithinAt_const t s M)

/-- A constant right factor passes through the derivative. -/
theorem hasDerivAt_mul_const (M : Matrix l n ℝ) {K : ℝ → Matrix m l ℝ}
    {K' : Matrix m l ℝ} (hK : HasDerivAt K K' t) :
    HasDerivAt (fun t => K t * M) (K' * M) t := by
  simpa using hasDerivAt_mul hK (hasDerivAt_const t M)

/-- Transposition commutes with differentiation, within a set. -/
theorem hasDerivWithinAt_transpose {K : ℝ → Matrix m n ℝ} {K' : Matrix m n ℝ}
    (hK : HasDerivWithinAt K K' s t) : HasDerivWithinAt (fun t => (K t)ᵀ) K'ᵀ s t := by
  simpa using (hasDerivWithinAt_const t s
    (transposeCLM : Matrix m n ℝ →L[ℝ] Matrix n m ℝ)).clm_apply hK

/-- Transposition commutes with differentiation. -/
theorem hasDerivAt_transpose {K : ℝ → Matrix m n ℝ} {K' : Matrix m n ℝ}
    (hK : HasDerivAt K K' t) : HasDerivAt (fun t => (K t)ᵀ) K'ᵀ t := by
  rw [← hasDerivWithinAt_univ] at hK ⊢
  exact hasDerivWithinAt_transpose hK

end Deriv

end LeanDLRA.Frobenius
