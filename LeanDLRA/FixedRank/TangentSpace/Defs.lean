import LeanDLRA.FixedRank.Defs
import LeanDLRA.LinearAlgebra.Factorization.Defs

/-!
# Definitions: tangent projector and tangent space at a point of the fixed-rank manifold

`LeanDLRA/FixedRank/Defs.lean` has the tangent projector for given factors (`tangentProj U V`) and
for given projector matrices (`Curvature.tangentProjMat Pu Pv`). This file adds the two objects
that depend on the matrix `Y` alone: no factorization is chosen and no rank is assumed.

* The **tangent projector at `Y`** is `Z ↦ P Z + Z Q - P Z Q` with `P = Y.rangeProj` the
  orthogonal projector onto the column space of `Y` and `Q = Yᵀ.rangeProj` the one onto its row
  space. Both are functions of `Y` (`Matrix.rangeProj` is `Y Y⁺`), so the projector is defined for
  every matrix.
* The **tangent space at `Y`** is the subspace `{A Y + Y B}` of all matrices of this form with
  square `A`, `B`. For `Y` of rank `r` it is the tangent space of the manifold of rank-`r`
  matrices at `Y` [KochLubich2007, §2.1].

The theorems about them are in `LeanDLRA/FixedRank/TangentSpace.lean`: the projector is the
orthogonal projector onto the tangent space, and for `Y = U S Vᵀ` with orthonormal `U`, `V` and
invertible `S` it is `tangentProj U V`.

## Main definitions

* `LeanDLRA.tangentProjAt Y`: the tangent projector at `Y`, a continuous linear map of the
  Frobenius space.
* `LeanDLRA.tangentSpaceAt Y`: the tangent space at `Y`, a submodule.

## Main results

* `LeanDLRA.tangentProjAt_apply`: `tangentProjAt Y Z = P Z + Z Q - P Z Q`.
* `LeanDLRA.mem_tangentSpaceAt`: `Z ∈ tangentSpaceAt Y ↔ ∃ A B, Z = A Y + Y B`.

## References

* [KochLubich2007, §2.1 and Lemma 4.1]
-/

open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The **tangent projector at `Y`** of the fixed-rank manifold, written without a factorization:
`P(Y) Z = P Z + Z Q - P Z Q` with the orthogonal projectors `P = Y.rangeProj` onto the column
space and `Q = Yᵀ.rangeProj` onto the row space of `Y`. It is defined for every `Y`, is an
orthogonal projector of the Frobenius space (`isOrthProj_tangentProjAt`) with range
`tangentSpaceAt Y` (`range_tangentProjAt`), and for `Y = U S Vᵀ` with orthonormal `U`, `V` and
invertible `S` it is `tangentProj U V` (`tangentProjAt_eq_tangentProj`). -/
noncomputable def tangentProjAt (Y : Matrix m n ℝ) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  tangent (Frobenius.leftMulCLM Y.rangeProj) (Frobenius.rightMulCLM Yᵀ.rangeProj)

/-- The **tangent space at `Y`** of the fixed-rank manifold, written without a factorization: all
matrices `A Y + Y B` with square `A`, `B`. It is the range of `tangentProjAt Y`
(`range_tangentProjAt`); at `Y = U S Vᵀ` with orthonormal `U`, `V` and invertible `S` it consists
of the matrices `U B + C Vᵀ` (`mem_tangentSpaceAt_mul_mul_transpose`). -/
def tangentSpaceAt (Y : Matrix m n ℝ) : Submodule ℝ (Matrix m n ℝ) where
  carrier := {Z | ∃ (A : Matrix m m ℝ) (B : Matrix n n ℝ), Z = A * Y + Y * B}
  add_mem' := by
    rintro _ _ ⟨A, B, rfl⟩ ⟨A', B', rfl⟩
    exact ⟨A + A', B + B', by simp only [Matrix.add_mul, Matrix.mul_add]; abel⟩
  zero_mem' := ⟨0, 0, by simp⟩
  smul_mem' := by
    rintro c _ ⟨A, B, rfl⟩
    exact ⟨c • A, c • B, by simp [Matrix.smul_mul, Matrix.mul_smul, smul_add]⟩

/-- Explicit formula for the tangent projector at `Y`. -/
theorem tangentProjAt_apply (Y Z : Matrix m n ℝ) :
    tangentProjAt Y Z =
      Y.rangeProj * Z + Z * Yᵀ.rangeProj - Y.rangeProj * Z * Yᵀ.rangeProj := by
  simp only [tangentProjAt, tangent_apply, Frobenius.leftMulCLM_apply,
    Frobenius.rightMulCLM_apply, Matrix.mul_assoc]

/-- Membership in the tangent space at `Y`. -/
theorem mem_tangentSpaceAt {Y Z : Matrix m n ℝ} :
    Z ∈ tangentSpaceAt Y ↔ ∃ (A : Matrix m m ℝ) (B : Matrix n n ℝ), Z = A * Y + Y * B :=
  Iff.rfl

end LeanDLRA
