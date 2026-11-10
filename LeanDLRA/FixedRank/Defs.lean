import LeanDLRA.LinearAlgebra.Projection.Defs

/-!
# Definitions: tangent and normal projectors of the fixed-rank manifold

The vocabulary of layer 3 (`FixedRank/`). The orthogonal projector onto the tangent space of the
manifold of rank-`r` matrices at `Y = U S Vᵀ` is [KochLubich2007, Lemma 4.1]

  `P(Y) Z = U Uᵀ Z + Z V Vᵀ - U Uᵀ Z V Vᵀ`,

and its normal part is `(I - U Uᵀ) Z (I - V Vᵀ)`. Abstractly, for a left projector `L` and a right
projector `R` on a real inner product space, the tangent projector is `L + R - L R` and the normal
projector `(1 - L) (1 - R)`. Interpolatory and sketched methods replace the orthogonal projectors
`U Uᵀ`, `V Vᵀ` by oblique ones.

The theorems about these objects are in `LeanDLRA/Foundations/Projector.lean` (abstract
calculus), `LeanDLRA/Matrix/Projectors.lean` (`tangentProj`), `LeanDLRA/Matrix/Curvature.lean`
(`tangentProjMat`, curvature bounds) and `LeanDLRA/Matrix/Interpolation.lean` (oblique tangent
projectors).

## Main definitions

* `LeanDLRA.tangent L R = L + R - L * R`, `LeanDLRA.normal L R = (1 - L) * (1 - R)`.
* `LeanDLRA.tangentProj U V = tangent (leftProj U) (rightProj V)`: the tangent-space projector
  at `Y = U S Vᵀ`.
* `LeanDLRA.Curvature.tangentProjMat Pu Pv B = Pu B + B Pv - Pu B Pv`: the same projector written
  with the projector matrices `Pu = U Uᵀ`, `Pv = V Vᵀ`.
* `LeanDLRA.obliqueTangentProj U SU V SV`: the oblique (interpolatory) tangent-space projector
  `𝒫_U Z + Z 𝒫_Vᵀ - 𝒫_U Z 𝒫_Vᵀ`; `LeanDLRA.sketchTangentProj`: its sketched instance.

## Main results

* `LeanDLRA.tangentProj_apply`: `tangentProj U V Z = U Uᵀ Z + Z V Vᵀ - U Uᵀ Z V Vᵀ`.
* `LeanDLRA.Curvature.tangentProjMat_eq_tangent`: `tangentProjMat Pu Pv` is the abstract tangent
  projector of the left and right multiplications by `Pu` and `Pv`.

## References

* [KochLubich2007, Lemma 4.1]
* [CarrelEtAl2025, eq. (13)] (oblique tangent projector)
-/

namespace LeanDLRA

/-! ### Abstract tangent and normal projectors -/

section Abstract

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The tangent-space projector built from a left and a right projector: `L + R - L R`. -/
def tangent (L R : E →L[ℝ] E) : E →L[ℝ] E := L + R - L * R

/-- The normal-space projector built from a left and a right projector: `(1 - L) (1 - R)`. -/
def normal (L R : E →L[ℝ] E) : E →L[ℝ] E := (1 - L) * (1 - R)

/-- `tangent L R x = L x + R x - L (R x)`. -/
@[simp] lemma tangent_apply (L R : E →L[ℝ] E) (x : E) :
    tangent L R x = L x + R x - L (R x) := by
  simp [tangent]

/-- `normal L R x = (x - R x) - L (x - R x)`. -/
@[simp] lemma normal_apply (L R : E →L[ℝ] E) (x : E) :
    normal L R x = (x - R x) - L (x - R x) := by
  simp [normal]

end Abstract

/-! ### The tangent-space projector on matrices -/

section Matrices

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

variable {k k' m n : Type*} [Fintype k] [Fintype k'] [Fintype m] [Fintype n]

/-- The orthogonal projector onto the tangent space at `Y = U S Vᵀ` of the manifold of rank-`r`
matrices: `P(Y) Z = U Uᵀ Z + Z V Vᵀ - U Uᵀ Z V Vᵀ`. -/
noncomputable def tangentProj (U : Matrix m k ℝ) (V : Matrix n k' ℝ) :
    Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  tangent (leftProj U) (rightProj V)

/-- Explicit formula for the tangent-space projector. -/
theorem tangentProj_apply (U : Matrix m k ℝ) (V : Matrix n k' ℝ) (Z : Matrix m n ℝ) :
    tangentProj U V Z = U * Uᵀ * Z + Z * V * Vᵀ - U * Uᵀ * Z * V * Vᵀ := by
  simp [tangentProj, Matrix.mul_assoc]

end Matrices

/-! ### The tangent-space projector in terms of projector matrices -/

namespace Curvature

open Matrix WithLp

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

section Frobenius

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

variable [DecidableEq m] [DecidableEq n] [DecidableEq k]

/-- The tangent-space projector `P(Y) B = Pu B + B Pv - Pu B Pv` at a matrix `Y` whose column
(row) space is the range of the orthogonal projector `Pu` (`Pv`); for `Y = U S Vᵀ`,
`Pu = U Uᵀ` and `Pv = V Vᵀ`, and then it is `LeanDLRA.tangentProj U V`
(`tangentProjMat_eq_tangentProj`). -/
def tangentProjMat (Pu : Matrix m m ℝ) (Pv : Matrix n n ℝ) (B : Matrix m n ℝ) : Matrix m n ℝ :=
  Pu * B + B * Pv - Pu * B * Pv

end Frobenius

open scoped LeanDLRA.Frobenius in
/-- `tangentProjMat Pu Pv` is the abstract tangent projector `tangent L R` of the left
multiplication `L = (Pu * ·)` and the right multiplication `R = (· * Pv)`. -/
theorem tangentProjMat_eq_tangent (Pu : Matrix m m ℝ) (Pv : Matrix n n ℝ) (B : Matrix m n ℝ) :
    tangentProjMat Pu Pv B =
      tangent (Frobenius.leftMulCLM Pu) (Frobenius.rightMulCLM Pv) B := by
  simp [tangentProjMat, Matrix.mul_assoc]

end Curvature

/-! ### Oblique tangent-space projectors -/

section Oblique

open Matrix Curvature
open scoped LeanDLRA.Frobenius

variable {k l m n : Type*}

variable [Fintype k] [DecidableEq k] [Fintype l] [DecidableEq l] [Fintype m] [Fintype n]
  {U SU : Matrix m k ℝ} {V SV : Matrix n l ℝ}

/-- The **oblique (interpolatory) tangent-space projector** at `Y = U Σ Vᵀ`
[CarrelEtAl2025, eq. (13)]: `P^∠(Y) Z = 𝒫_U Z + Z 𝒫_Vᵀ - 𝒫_U Z 𝒫_Vᵀ`. -/
noncomputable def obliqueTangentProj (U SU : Matrix m k ℝ) (V SV : Matrix n l ℝ) :
    Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  LeanDLRA.tangent (leftOblique U SU) (rightOblique V SV)

/-- Explicit formula for the oblique tangent-space projector. -/
theorem obliqueTangentProj_apply (U SU : Matrix m k ℝ) (V SV : Matrix n l ℝ)
    (Z : Matrix m n ℝ) :
    obliqueTangentProj U SU V SV Z = obliqueProj U SU * Z + Z * (obliqueProj V SV)ᵀ -
      obliqueProj U SU * Z * (obliqueProj V SV)ᵀ := by
  simp [obliqueTangentProj, Matrix.mul_assoc]

/-- The oblique sketch tangent projector `P^{Θ,Ω}_Y Z = P^Θ_{Im Y} Z + Z (P^Ω_{Im Yᵀ})ᵀ - …`
[CarrelGrigori2026, Lemma 4.2], for bases `P`, `W` of `Y = P S Wᵀ`, written with the oblique
projectors `obliqueProj P (Θᵀ Θ P)` (which equal `P (ΘP)⁺ Θ` for sketch-orthonormal `P`,
`obliqueProj_sketch_eq`). -/
noncomputable abbrev sketchTangentProj {p q : Type*} [Fintype p] [Fintype q] (Θ : Matrix p m ℝ)
    (Ω : Matrix q n ℝ) (P : Matrix m k ℝ) (W : Matrix n l ℝ) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  obliqueTangentProj P (Θᵀ * Θ * P) W (Ωᵀ * Ω * W)

end Oblique

end LeanDLRA
