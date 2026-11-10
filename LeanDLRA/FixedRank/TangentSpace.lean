import LeanDLRA.FixedRank.TangentSpace.Defs
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Projectors

/-!
# Tangent vectors of the fixed-rank manifold

Results about the tangent space `T_Y 𝓜_r = range P(Y)` at `Y = U S Vᵀ` (orthonormal `U`, `V`)
that several papers use, stated once in the core vocabulary (`LeanDLRA.tangentProj`,
`LeanDLRA.mem_range_tangentProj`), and the interface of the two objects that depend on `Y` alone,
`LeanDLRA.tangentProjAt Y` and `LeanDLRA.tangentSpaceAt Y`
(`LeanDLRA/FixedRank/TangentSpace/Defs.lean`).

## Main results

* `LeanDLRA.mul_add_mul_mem_range_tangentProj`: the Sylvester-type field `A_x Y + Y A_y` is tangent
  at `Y = U S Vᵀ` for all square `A_x`, `A_y` and every core `S` (invertible or not). The stiff
  flows of arXiv 2010.05249 (`A_x X + X A_y`) and arXiv 1803.10473 (`A Y + Y Aᵀ`) are instances
  (`P2010_05249.stiff_derivative_mem_tangent'`, `P1803_10473.stiff_derivative_mem_tangent`).
* `LeanDLRA.isOrthProj_tangentProjAt`: `tangentProjAt Y` is an orthogonal projector, for every `Y`.
* `LeanDLRA.tangentProjAt_eq_self_iff`, `LeanDLRA.range_tangentProjAt`: its fixed points and its
  range are the tangent space `tangentSpaceAt Y = {A Y + Y B}`;
  `LeanDLRA.tangentProjAt_eq_starProjection`: it is the orthogonal projection onto that subspace.
* `LeanDLRA.tangentProjAt_eq_tangentProj`: at `Y = U S Vᵀ` with orthonormal `U`, `V` and
  invertible `S` it is `tangentProj U V`, so every theorem about `tangentProj` applies at a point;
  `LeanDLRA.mem_tangentSpaceAt_mul_mul_transpose`: the tangent space there is `{U B + C Vᵀ}`.
* `LeanDLRA.tangentProjAt_apply_eq_tangentProjMat`: it is `Curvature.tangentProjMat` of the two
  projector matrices `Y.rangeProj`, `Yᵀ.rangeProj`.
* `LeanDLRA.one_sub_tangentProjAt_apply`, `LeanDLRA.isOrthProj_one_sub_tangentProjAt`: the normal
  projector `1 - tangentProjAt Y` is `Z ↦ (1 - P) Z (1 - Q)`, an orthogonal projector.

A point of the manifold of rank-`r` matrices is a point of `LeanDLRA.fixedRankSet m n r`
(`LeanDLRA/LinearAlgebra/LowRank/SepRank.lean`). The statements about `tangentProjAt` and
`tangentSpaceAt` below hold for every matrix `Y`, so none of them has a rank hypothesis.
-/

open scoped Matrix

namespace LeanDLRA

variable {k k' m n : Type*} [Fintype k] [Fintype k'] [Fintype m] [Fintype n]

/-- **Sylvester-type fields are tangent.** For `Y = U S Vᵀ` with orthonormal `U`, `V`, the matrix
`A_x Y + Y A_y = (A_x U S) Vᵀ + U (S Vᵀ A_y)` lies in the range of the tangent projector `P(Y)`
of the rank-`r` manifold, for arbitrary square `A_x`, `A_y` and any (not necessarily
invertible) `S`. -/
theorem mul_add_mul_mem_range_tangentProj [DecidableEq k] [DecidableEq k'] {U : Matrix m k ℝ}
    {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (S : Matrix k k' ℝ)
    (Ax : Matrix m m ℝ) (Ay : Matrix n n ℝ) :
    Ax * (U * S * Vᵀ) + (U * S * Vᵀ) * Ay ∈
      LinearMap.range (tangentProj U V : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ) := by
  rw [mem_range_tangentProj hU hV]
  refine ⟨S * Vᵀ * Ay, Ax * U * S, ?_⟩
  simp only [Matrix.mul_assoc]
  abel

/-! ### The tangent projector and the tangent space at a point -/

section AtPoint

open scoped LeanDLRA.Frobenius

/-- The tangent projector at `Y` is an orthogonal projector of the Frobenius space, for every
matrix `Y` (no rank hypothesis). -/
theorem isOrthProj_tangentProjAt (Y : Matrix m n ℝ) : IsOrthProj (tangentProjAt Y) :=
  (Matrix.isOrthProjMat_rangeProj Y).isOrthProj_tangent (Matrix.isOrthProjMat_rangeProj Yᵀ)

/-- The tangent projector at `Y` is `Curvature.tangentProjMat` of the projector matrices onto the
column space and the row space of `Y`. -/
theorem tangentProjAt_apply_eq_tangentProjMat (Y Z : Matrix m n ℝ) :
    tangentProjAt Y Z = Curvature.tangentProjMat Y.rangeProj Yᵀ.rangeProj Z :=
  (Curvature.tangentProjMat_eq_tangent Y.rangeProj Yᵀ.rangeProj Z).symm

/-- The fixed points of the tangent projector at `Y` are exactly the tangent vectors
`A Y + Y B`. -/
theorem tangentProjAt_eq_self_iff {Y Z : Matrix m n ℝ} :
    tangentProjAt Y Z = Z ↔ Z ∈ tangentSpaceAt Y := by
  have hP : Y.rangeProj * Y = Y := Matrix.rangeProj_mul_self Y
  have hQ : Y * Yᵀ.rangeProj = Y := by
    have h := congrArg Matrix.transpose (Matrix.rangeProj_mul_self Yᵀ)
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_rangeProj] at h
  constructor
  · intro h
    obtain ⟨C, hC⟩ := Matrix.exists_rangeProj_eq_mul Y
    obtain ⟨D, hD⟩ := Matrix.exists_rangeProj_eq_mul Yᵀ
    have hD' : Yᵀ.rangeProj = Dᵀ * Y := by
      have h' := congrArg Matrix.transpose hD
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_rangeProj] at h'
    refine ⟨(Z - Y.rangeProj * Z) * Dᵀ, C * Z, ?_⟩
    rw [Matrix.mul_assoc _ Dᵀ Y, ← hD', ← Matrix.mul_assoc Y C Z, ← hC, Matrix.sub_mul]
    rw [tangentProjAt_apply] at h
    exact h.symm.trans (by abel)
  · rintro ⟨A, B, rfl⟩
    have hP' : ∀ X : Matrix n n ℝ, Y.rangeProj * (Y * X) = Y * X := fun X => by
      rw [← Matrix.mul_assoc, hP]
    rw [tangentProjAt_apply]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hQ, hP']
    abel

/-- The range of the tangent projector at `Y` is the tangent space at `Y`. -/
theorem range_tangentProjAt (Y : Matrix m n ℝ) :
    LinearMap.range (tangentProjAt Y : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ) =
      tangentSpaceAt Y := by
  ext Z
  rw [LinearMap.mem_range, ← tangentProjAt_eq_self_iff]
  simp only [ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨X, rfl⟩
    exact (isOrthProj_tangentProjAt Y).idem X
  · intro h
    exact ⟨Z, h⟩

/-- `Y` is a tangent vector at `Y`. -/
theorem self_mem_tangentSpaceAt (Y : Matrix m n ℝ) : Y ∈ tangentSpaceAt Y :=
  ⟨Y.rangeProj, 0, by rw [Matrix.rangeProj_mul_self, Matrix.mul_zero, add_zero]⟩

/-- The tangent projector at `Y` fixes `Y`. -/
theorem tangentProjAt_self (Y : Matrix m n ℝ) : tangentProjAt Y Y = Y :=
  tangentProjAt_eq_self_iff.2 (self_mem_tangentSpaceAt Y)

/-- The tangent projector at `Y` is the orthogonal projection onto the tangent space at `Y`. -/
theorem tangentProjAt_eq_starProjection (Y : Matrix m n ℝ) :
    tangentProjAt Y = (tangentSpaceAt Y).starProjection := by
  have hP := isOrthProj_tangentProjAt Y
  refine ContinuousLinearMap.ext fun Z => ?_
  refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun W hW => ?_).symm
  · exact tangentProjAt_eq_self_iff.1 (hP.idem Z)
  · rw [← tangentProjAt_eq_self_iff.2 hW, ← hP.symm, map_sub, hP.idem, sub_self,
      inner_zero_left]

/-- **The tangent projector at a factorized point.** For `Y = U S Vᵀ` with orthonormal `U`, `V`
and invertible `S`, the tangent projector at `Y` is `tangentProj U V`: the column space of `Y` is
that of `U` and its row space that of `V`. -/
theorem tangentProjAt_eq_tangentProj [DecidableEq k] {U : Matrix m k ℝ} {S : Matrix k k ℝ}
    {V : Matrix n k ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S.det) :
    tangentProjAt (U * S * Vᵀ) = tangentProj U V := by
  have h1 : (U * S * Vᵀ).rangeProj = U * Uᵀ := by
    rw [← Matrix.rangeProj_eq_mul_transpose hU]
    refine Matrix.rangeProj_eq_rangeProj_of_mul (C := S * Vᵀ) (D := V * S⁻¹)
      (Matrix.mul_assoc _ _ _) ?_
    rw [Matrix.mul_assoc (U * S), ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hS, Matrix.mul_one]
  have h2 : (U * S * Vᵀ)ᵀ.rangeProj = V * Vᵀ := by
    rw [← Matrix.rangeProj_eq_mul_transpose hV]
    refine Matrix.rangeProj_eq_rangeProj_of_mul (C := Sᵀ * Uᵀ) (D := U * (S⁻¹)ᵀ) ?_ ?_
    · simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    · simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul, ← Matrix.transpose_mul,
        Matrix.nonsing_inv_mul _ hS, Matrix.transpose_one, Matrix.mul_one]
  rw [tangentProjAt, h1, h2]
  rfl

/-- **The tangent space at a factorized point.** For `Y = U S Vᵀ` with orthonormal `U`, `V` and
invertible `S`, the tangent vectors at `Y` are exactly the matrices `U B + C Vᵀ`
[KochLubich2007, §2.1]. -/
theorem mem_tangentSpaceAt_mul_mul_transpose [DecidableEq k] {U : Matrix m k ℝ}
    {S : Matrix k k ℝ} {V : Matrix n k ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hS : IsUnit S.det) (Z : Matrix m n ℝ) :
    Z ∈ tangentSpaceAt (U * S * Vᵀ) ↔
      ∃ (B : Matrix k n ℝ) (C : Matrix m k ℝ), Z = U * B + C * Vᵀ := by
  rw [← tangentProjAt_eq_self_iff, tangentProjAt_eq_tangentProj hU hV hS,
    tangentProj_eq_self_iff hU hV]

/-- Without invertibility of the core, one inclusion remains: the tangent space at `U S Vᵀ`
(orthonormal `U`, `V`, any `S`) lies in the range of `tangentProj U V`. -/
theorem tangentSpaceAt_mul_mul_transpose_le [DecidableEq k] [DecidableEq k'] {U : Matrix m k ℝ}
    {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (S : Matrix k k' ℝ) :
    tangentSpaceAt (U * S * Vᵀ) ≤
      LinearMap.range (tangentProj U V : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ) := by
  rintro _ ⟨A, B, rfl⟩
  exact mul_add_mul_mem_range_tangentProj hU hV S A B

/-- The normal projector at `Y`: `(1 - P(Y)) Z = (1 - P) Z (1 - Q)` with `P = Y.rangeProj` and
`Q = Yᵀ.rangeProj`. -/
theorem one_sub_tangentProjAt_apply [DecidableEq m] [DecidableEq n] (Y Z : Matrix m n ℝ) :
    (1 - tangentProjAt Y) Z = (1 - Y.rangeProj) * Z * (1 - Yᵀ.rangeProj) := by
  rw [sub_apply, one_apply_eq_self, tangentProjAt_apply]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
  abel

/-- The normal projector `1 - tangentProjAt Y` is an orthogonal projector. -/
theorem isOrthProj_one_sub_tangentProjAt (Y : Matrix m n ℝ) : IsOrthProj (1 - tangentProjAt Y) :=
  (isOrthProj_tangentProjAt Y).compl

/-- A rank-one point: at `Y = diag(1, 0)` the tangent projector keeps the first row and the first
column of `Z` and removes the entry `Z₂₂`, which is the normal part. -/
example : tangentProjAt (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) !![1, 2; 3, 4] =
    !![1, 2; 3, 0] := by
  have ht : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = !![1, 0; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hsq : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 0; 0, 0] = !![1, 0; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hP : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).rangeProj = !![1, 0; 0, 0] :=
    (Matrix.eq_rangeProj_of_mul_self (C := !![1, 0; 0, 0]) ht hsq hsq.symm).symm
  rw [tangentProjAt_apply, ht, hP]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The hypotheses of `tangentProjAt_eq_tangentProj` and `mem_tangentSpaceAt_mul_mul_transpose`
hold at the rank-one point `e₁ e₁ᵀ` of the `2 × 2` matrices (`U = V = e₁`, `S = 1`). -/
example :
    tangentProjAt ((!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) *
      (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ) =
      tangentProj (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) :=
  have h : (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) =
      1 := by
    ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  tangentProjAt_eq_tangentProj h h (by simp)

end AtPoint

end LeanDLRA
