import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2601.18705: SN-like and PN-like DLRA for thermal radiative transfer

This module formalizes the algebraic core of the PN-like claim: if the even-parity operator is
represented by a symmetric positive-definite matrix `M`, then for an orthonormal basis `U`
(`Uᵀ U = 1`) the reduced low-rank system matrix `Uᵀ M U` is again symmetric positive definite at
every step, so each reduced linear system has a unique solution. The theorems are
`posDef_transpose_mul_mul_of_orthonormal` and `reduced_system_unique`, with an `example`
exhibiting an instance. The paper's concrete even-parity operator and its time stepping are not
formalized; the matrix `M` is an arbitrary SPD input.

Not formalized, and left out on purpose: the SN-like claim (angle selection from the evolving
angular basis, with each step becoming SN transport sweeps at the selected angles). Its algebraic
oblique-projector part is already in `LeanDLRA/Matrix/Interpolation.lean`
(`isObliqueProj_leftOblique`, `norm_sub_obliqueProj_mul_le`), but the coupled nonlinear
thermal-radiative-transfer scheme with Planck coupling has no error theorem in the library, so
that part is not proved here.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2601_18705

variable {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]

set_option linter.unusedFintypeInType false in
/-- **Even-parity reduced systems are SPD** (arXiv 2601.18705, PN-like DLR; abstract core).
If `M` is symmetric positive definite and the columns of `U` are orthonormal (`Uᵀ U = 1`), then
the Galerkin-reduced matrix `Uᵀ M U` is symmetric positive definite. -/
theorem posDef_transpose_mul_mul_of_orthonormal {M : Matrix m m ℝ} (hM : M.PosDef)
    {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) : (Uᵀ * M * U).PosDef := by
  have hinj : Function.Injective U.mulVec := by
    intro x y hxy
    have h := congrArg (Uᵀ.mulVec) hxy
    simpa [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec] using h
  have h := hM.conjTranspose_mul_mul_same hinj
  simpa using h

/-- **Reduced linear systems are uniquely solvable** (arXiv 2601.18705, PN-like DLR; abstract core).
Under the hypotheses of `posDef_transpose_mul_mul_of_orthonormal`, for every right-hand side `b`
the system `(Uᵀ M U) x = b` has exactly one solution. -/
theorem reduced_system_unique {M : Matrix m m ℝ} (hM : M.PosDef)
    {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) (b : k → ℝ) :
    ∃! x : k → ℝ, (Uᵀ * M * U) *ᵥ x = b := by
  have hA : (Uᵀ * M * U).PosDef := posDef_transpose_mul_mul_of_orthonormal hM hU
  have hdet : IsUnit (Uᵀ * M * U).det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hex : (Uᵀ * M * U) *ᵥ ((Uᵀ * M * U)⁻¹ *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  exact ⟨(Uᵀ * M * U)⁻¹ *ᵥ b, hex, fun y hy => hA.mulVec_injective (hy.trans hex.symm)⟩

/-- Instance of `reduced_system_unique`: with `M = I` and `U = (1, 0)ᵀ` the reduced system is
the scalar equation `1 · x = 3`, uniquely solvable. -/
example : ∃! x : Fin 1 → ℝ,
    ((!![(1 : ℝ); 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ)
      * !![(1 : ℝ); 0]) *ᵥ x = ![3] := by
  apply reduced_system_unique Matrix.PosDef.one
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]

end LeanDLRA.Literature.P2601_18705
