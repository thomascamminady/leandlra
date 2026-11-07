import LeanDLRA.Matrix.Curvature

/-!
# Results of arXiv 2308.11581: DLRA for SDEs: DO/DLR well-posedness

This module formalizes the matrix core of **Lemma A.4** of arXiv 2308.11581 (Kazashi, Nobile,
Zoccolan, *Dynamical Low-Rank Approximation for Stochastic Differential Equations*, v4), at a single
time, on real matrices with the Frobenius norm `‖·‖` and spectral norm `specNorm`.

Let `U, Ũ ∈ ℝ^{m×n}` be such that `U Uᵀ` and `Ũ Ũᵀ` are invertible (the paper says that
invertibility is implicit) and `‖(U Uᵀ)⁻¹‖_F ≤ γ`, `‖(Ũ Ũᵀ)⁻¹‖_F ≤ γ` for some `γ > 0`. Write
`P_U = Uᵀ (U Uᵀ)⁻¹ U` for the orthogonal projector onto the rows of `U`. Then

  `‖P_U − P_Ũ‖_F ≤ √(2γ) ‖U − Ũ‖_F`,

and in particular there is a constant `C₁ > 0` (namely `√(2γ)`, depending only on `γ`) with
`‖P_U − P_Ũ‖_F ≤ C₁ ‖U − Ũ‖_F`.  This is the paper's Lemma A.4 for one time `t`; the paper's
supremum over `t ∈ [0, T]` follows by taking the supremum of this pointwise bound.

**Differences from the paper.**
* The paper's class `B_{γ,N}` also requires `sup_s ‖U_s‖_F < √N`. That bound is not used by the
  proof, so it is omitted; the statement proved here is therefore stronger.
* Time is fixed: the statement is for matrices, not for functions `t ↦ U_t` on `[0, T]`.
* The constant is explicit, `√(2γ)`, instead of an unspecified `C₁`.

**Left out.** The following results of the same paper are not formalized here:
* Proposition A.1 (Gram-inverse perturbation on a Hilbert space `[H]^R`, with `η(ρ, γ)`). Its proof
  is an ODE comparison along `s ↦ Y₀ + s δ`, which is not formalized.
* Lemma A.2 and Proposition A.3 (Lipschitz continuity of the projectors `P_U`, `P_V` on `L²(Ω; H)`
  for finite-rank functions). They need the representation (A.2) and the operator theory on
  `L²(Ω; H)`, which the library does not have.
* The stochastic projector `P_Y` of Lemma A.4 (the `𝔹̃_{γ̃,M}` class and the `L²(Ω)` bound).

**Core definitions used.** `LeanDLRA.Curvature.specNorm`, `IsOrthProjMat`, `isOrthProjMat_rowProj`,
`specNorm_le_frob`, `specNorm_transpose_mul_self`, `norm_rowProj_sub_le_of_trace`
(`LeanDLRA/Matrix/Curvature.lean`). The file adds no new structures or definitions.
-/

open Set Filter Topology Finset Matrix
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2308_11581

open LeanDLRA.Curvature

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-- The Gram inverse `(U Uᵀ)⁻¹` is symmetric. -/
lemma gram_inv_transpose (U : Matrix m n ℝ) : ((U * Uᵀ)⁻¹)ᵀ = (U * Uᵀ)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- `Uᵀ (U Uᵀ)⁻¹ U` is an orthogonal projector onto the rows of `U`, and `U` is fixed by it. -/
lemma rowProj_left (U : Matrix m n ℝ) (hU : (U * Uᵀ).det ≠ 0) :
    U * (Uᵀ * (U * Uᵀ)⁻¹) * U = U := by
  have key : U * Uᵀ * (U * Uᵀ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hU)
  rw [← Matrix.mul_assoc U Uᵀ, key, Matrix.one_mul]

/-- The row projector `Uᵀ (U Uᵀ)⁻¹ U` is symmetric-compatible: `(G X)ᵀ = G X`. -/
lemma rowProj_symm (U : Matrix m n ℝ) :
    (Uᵀ * (U * Uᵀ)⁻¹ * U)ᵀ = Uᵀ * (U * Uᵀ)⁻¹ * U := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, gram_inv_transpose,
    Matrix.mul_assoc]

/-- The trace of the row projector equals the number of rows. -/
lemma trace_rowProj (U : Matrix m n ℝ) (hU : (U * Uᵀ).det ≠ 0) :
    Matrix.trace (Uᵀ * (U * Uᵀ)⁻¹ * U) = Fintype.card m := by
  have key : U * Uᵀ * (U * Uᵀ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hU)
  rw [Matrix.trace_mul_comm (Uᵀ * (U * Uᵀ)⁻¹) U, ← Matrix.mul_assoc, key, Matrix.trace_one]

/-- The generalized inverse `G = Uᵀ (U Uᵀ)⁻¹` has spectral norm at most `√γ` when
`‖(U Uᵀ)⁻¹‖_F ≤ γ`. -/
lemma specNorm_gram_le {U : Matrix m n ℝ} {γ : ℝ} (hU : (U * Uᵀ).det ≠ 0)
    (hγ : ‖(U * Uᵀ)⁻¹‖ ≤ γ) : specNorm (Uᵀ * (U * Uᵀ)⁻¹) ≤ √γ := by
  have hunit : IsUnit (U * Uᵀ).det := isUnit_iff_ne_zero.mpr hU
  have hinv : (U * Uᵀ)⁻¹ * (U * Uᵀ) = 1 := Matrix.nonsing_inv_mul _ hunit
  have hGG : (Uᵀ * (U * Uᵀ)⁻¹)ᵀ * (Uᵀ * (U * Uᵀ)⁻¹) = (U * Uᵀ)⁻¹ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, gram_inv_transpose,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᵀ (U * Uᵀ)⁻¹,
      ← Matrix.mul_assoc (U * Uᵀ)⁻¹ (U * Uᵀ) (U * Uᵀ)⁻¹, hinv, Matrix.one_mul]
  have hsq : specNorm (Uᵀ * (U * Uᵀ)⁻¹) * specNorm (Uᵀ * (U * Uᵀ)⁻¹) ≤ γ := by
    rw [← specNorm_transpose_mul_self, hGG]
    exact (specNorm_le_frob _).trans hγ
  rw [← Real.sqrt_mul_self (specNorm_nonneg (Uᵀ * (U * Uᵀ)⁻¹))]
  exact Real.sqrt_le_sqrt hsq

/-- **Lemma A.4 (matrix core, one time).** Let `U, Ũ ∈ ℝ^{m×n}` with invertible Gram matrices and
`‖(U Uᵀ)⁻¹‖_F ≤ γ`, `‖(Ũ Ũᵀ)⁻¹‖_F ≤ γ`, where `γ > 0`. With `P_U = Uᵀ (U Uᵀ)⁻¹ U` the orthogonal
projector onto the rows of `U`, we have `‖P_U − P_Ũ‖_F ≤ √(2γ) ‖U − Ũ‖_F`.
(arXiv 2308.11581, Lemma A.4, pointwise in time; the constant is `√(2γ)`.) -/
theorem rowProj_sub_le {U Ũ : Matrix m n ℝ} {γ : ℝ} (_hγ : 0 < γ)
    (hU : (U * Uᵀ).det ≠ 0) (hŨ : (Ũ * Ũᵀ).det ≠ 0)
    (hUγ : ‖(U * Uᵀ)⁻¹‖ ≤ γ) (_hŨγ : ‖(Ũ * Ũᵀ)⁻¹‖ ≤ γ) :
    ‖Uᵀ * (U * Uᵀ)⁻¹ * U - Ũᵀ * (Ũ * Ũᵀ)⁻¹ * Ũ‖ ≤ √(2 * γ) * ‖U - Ũ‖ := by
  have hP : IsOrthProjMat (Ũᵀ * (Ũ * Ũᵀ)⁻¹ * Ũ) :=
    isOrthProjMat_rowProj (rowProj_left Ũ hŨ) (rowProj_symm Ũ)
  have hY : Ũ * (Ũᵀ * (Ũ * Ũᵀ)⁻¹ * Ũ) = Ũ :=
    (Matrix.mul_assoc _ _ _).symm.trans (rowProj_left Ũ hŨ)
  have h := norm_rowProj_sub_le_of_trace (rowProj_left U hU) (rowProj_symm U) hP hY
    ((trace_rowProj U hU).trans (trace_rowProj Ũ hŨ).symm)
  have hG := specNorm_gram_le hU hUγ
  calc ‖Uᵀ * (U * Uᵀ)⁻¹ * U - Ũᵀ * (Ũ * Ũᵀ)⁻¹ * Ũ‖
      ≤ √2 * specNorm (Uᵀ * (U * Uᵀ)⁻¹) * ‖U - Ũ‖ := h
    _ ≤ √2 * √γ * ‖U - Ũ‖ := by gcongr
    _ = √(2 * γ) * ‖U - Ũ‖ := by rw [Real.sqrt_mul (by norm_num)]

/-- **Lemma A.4, existence form.** There is a constant `C₁ > 0`, depending only on `γ`, such that
`‖P_U − P_Ũ‖_F ≤ C₁ ‖U − Ũ‖_F` for all `U, Ũ` in the class defined by `γ`. -/
theorem exists_rowProj_lipschitz {γ : ℝ} (hγ : 0 < γ) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ U Ũ : Matrix m n ℝ, (U * Uᵀ).det ≠ 0 → (Ũ * Ũᵀ).det ≠ 0 →
      ‖(U * Uᵀ)⁻¹‖ ≤ γ → ‖(Ũ * Ũᵀ)⁻¹‖ ≤ γ →
      ‖Uᵀ * (U * Uᵀ)⁻¹ * U - Ũᵀ * (Ũ * Ũᵀ)⁻¹ * Ũ‖ ≤ C₁ * ‖U - Ũ‖ :=
  ⟨√(2 * γ), Real.sqrt_pos.mpr (by linarith), fun _ _ hU hŨ hUγ hŨγ =>
    rowProj_sub_le hγ hU hŨ hUγ hŨγ⟩

end LeanDLRA.Literature.P2308_11581
