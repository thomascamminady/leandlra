import LeanDLRA.LinearAlgebra.Frobenius.Defs
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Definitions: orthogonal and oblique projectors

The projector vocabulary of layer 1 (`LinearAlgebra/`). Every robust integrator for dynamical
low-rank approximation is built from orthogonal projectors on a real inner product space; on
matrices with the Frobenius inner product they are the left projector `X ↦ U Uᵀ X` and the right
projector `X ↦ X V Vᵀ`. Interpolatory (DEIM) and sketched methods use oblique projectors instead.

The theorems about these objects are in `LeanDLRA/Foundations/Projector.lean` (abstract
orthogonal projectors), `LeanDLRA/Matrix/Projectors.lean` (`leftProj`, `rightProj`),
`LeanDLRA/Matrix/Interpolation.lean` (oblique projectors) and `LeanDLRA/Matrix/Curvature.lean`
(projector matrices).

## Main definitions

* `LeanDLRA.IsOrthProj P`: `P` is an orthogonal projector (idempotent and symmetric).
* `LeanDLRA.IsObliqueProj P Q`: `P` is an oblique projector onto the range of the orthogonal
  projector `Q`.
* `LeanDLRA.rankOneProj e`: the projector `x ↦ ⟪e, x⟫ e`.
* `LeanDLRA.leftProj U`, `LeanDLRA.rightProj V`: `X ↦ U Uᵀ X` and `X ↦ X V Vᵀ` on matrices.
* `LeanDLRA.Curvature.IsOrthProjMat P`: the real square matrix `P` is symmetric and idempotent.
* `LeanDLRA.obliqueProj U S`: the oblique (DEIM) projector matrix `U (Sᵀ U)⁻¹ Sᵀ`;
  `LeanDLRA.leftOblique`, `LeanDLRA.rightOblique`: the induced maps on `m × n` matrices.

## Main results

* `LeanDLRA.isOrthProj_iff_isSymmetricProjection`: `IsOrthProj` is Mathlib's
  `LinearMap.IsSymmetricProjection`.
* `LeanDLRA.IsOrthProj.restrictScalars`: a symmetric projection of a complex (or `RCLike`) inner
  product space is a real orthogonal projector of its realification.

## Implementation notes

The projector layer is real (decision of 2026-11-09, `docs/CONVENTIONS.md` §5). Complex problems
are treated by realification; `IsOrthProj.restrictScalars` connects to Mathlib's complex
projections, and the realification only has to agree with the real part of the complex inner
product (`hre`), which covers both `InnerProductSpace.rclikeToReal` and `EuclideanSpace ℂ ι`.
-/

open scoped Matrix RealInnerProductSpace

namespace LeanDLRA

/-! ### Abstract projectors -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `P` is an orthogonal projector: idempotent and symmetric. -/
structure IsOrthProj (P : E →L[ℝ] E) : Prop where
  /-- `P` is idempotent: `P (P x) = P x`. -/
  idem : ∀ x, P (P x) = P x
  /-- `P` is symmetric: `⟪P x, y⟫ = ⟪x, P y⟫`. -/
  symm : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫

/-- The identity is an orthogonal projector, so `IsOrthProj` is satisfiable. -/
example : IsOrthProj (1 : E →L[ℝ] E) := ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- `IsOrthProj` is Mathlib's notion of a symmetric projection (`LinearMap.IsSymmetricProjection`:
an idempotent symmetric linear map). -/
theorem isOrthProj_iff_isSymmetricProjection {P : E →L[ℝ] E} :
    IsOrthProj P ↔ (P : E →ₗ[ℝ] E).IsSymmetricProjection := by
  constructor
  · intro hP
    exact ⟨LinearMap.ext fun x => hP.idem x, fun x y => hP.symm x y⟩
  · intro hP
    exact ⟨fun x => LinearMap.congr_fun hP.isIdempotentElem.eq x, fun x y => hP.isSymmetric x y⟩

/-- **Realification.** Let `G` be an inner product space over `𝕜 = ℝ` or `ℂ` that also carries a
real inner product space structure whose inner product is the real part of the `𝕜` one. Then
every symmetric projection `P` over `𝕜` (for example `K.starProjection` for a complex subspace
`K`) is a real orthogonal projector `P.restrictScalars ℝ`. -/
theorem IsOrthProj.restrictScalars {𝕜 G : Type*} [RCLike 𝕜] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] [InnerProductSpace ℝ G] [IsScalarTower ℝ 𝕜 G]
    (hre : ∀ x y : G, ⟪x, y⟫ = RCLike.re (inner 𝕜 x y)) {P : G →L[𝕜] G}
    (hP : (P : G →ₗ[𝕜] G).IsSymmetricProjection) : IsOrthProj (P.restrictScalars ℝ) where
  idem x := LinearMap.congr_fun hP.isIdempotentElem.eq x
  symm x y := by
    simp only [ContinuousLinearMap.coe_restrictScalars', hre]
    exact congrArg RCLike.re (hP.isSymmetric x y)

/-- The realification of a complex star projection on `ℂⁿ` is a real orthogonal projector. -/
example {n : ℕ} (K : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    IsOrthProj (K.starProjection.restrictScalars ℝ) :=
  IsOrthProj.restrictScalars (fun x y => by simp [PiLp.inner_apply, Complex.inner, mul_comm])
    K.isSymmetricProjection_starProjection

/-- `P` is an *oblique projector onto the range of the orthogonal projector `Q`*: `P` fixes the
range of `Q` (`P Q = Q`) and maps into it (`Q P = P`). For `Q = U Uᵀ` this is the DEIM / sketched
projector `U (Sᵀ U)⁻¹ Sᵀ` (`obliqueProj`). -/
structure IsObliqueProj (P Q : E →L[ℝ] E) : Prop where
  /-- `Q` is an orthogonal projector. -/
  orth : IsOrthProj Q
  /-- `P` fixes the range of `Q`. -/
  fix : ∀ x, P (Q x) = Q x
  /-- `P` maps into the range of `Q`. -/
  range : ∀ x, Q (P x) = P x

/-- An orthogonal projector is an oblique projector onto its own range, so `IsObliqueProj` is
satisfiable. -/
example : IsObliqueProj (1 : E →L[ℝ] E) 1 :=
  ⟨⟨fun _ => rfl, fun _ _ => rfl⟩, fun _ => rfl, fun _ => rfl⟩

/-- The projector `x ↦ ⟪e, x⟫ e` onto the line spanned by `e` (orthogonal if `‖e‖ = 1`). -/
noncomputable def rankOneProj (e : E) : E →L[ℝ] E := (innerSL ℝ e).smulRight e

/-- `rankOneProj e x = ⟪e, x⟫ e`. -/
@[simp] lemma rankOneProj_apply (e x : E) : rankOneProj e x = ⟪e, x⟫ • e := by
  simp [rankOneProj]

end Abstract

/-! ### Left and right projectors on matrices -/

section Matrices

open scoped LeanDLRA.Frobenius

variable {k k' m n : Type*} [Fintype k] [Fintype k'] [Fintype m] [Fintype n]

/-- The left projector `X ↦ U Uᵀ X`. It is an orthogonal projector when `Uᵀ U = 1`
(`isOrthProj_leftProj`). -/
noncomputable def leftProj (U : Matrix m k ℝ) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  Frobenius.leftMulCLM (U * Uᵀ)

/-- The right projector `X ↦ X V Vᵀ`. It is an orthogonal projector when `Vᵀ V = 1`
(`isOrthProj_rightProj`). -/
noncomputable def rightProj (V : Matrix n k ℝ) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  Frobenius.rightMulCLM (V * Vᵀ)

/-- `leftProj U X = U Uᵀ X`. -/
@[simp] lemma leftProj_apply (U : Matrix m k ℝ) (X : Matrix m n ℝ) :
    leftProj U X = U * Uᵀ * X := rfl

/-- `rightProj V X = X V Vᵀ`. -/
@[simp] lemma rightProj_apply (V : Matrix n k ℝ) (X : Matrix m n ℝ) :
    rightProj V X = X * V * Vᵀ := by
  simp [rightProj, Matrix.mul_assoc]

/-- `rightProj V X = X (V Vᵀ)`, the defining form. -/
lemma rightProj_apply' (V : Matrix n k ℝ) (X : Matrix m n ℝ) :
    rightProj V X = X * (V * Vᵀ) := rfl

end Matrices

/-! ### Projector matrices -/

namespace Curvature

open Matrix WithLp

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

/-- A real square matrix is an orthogonal projector: symmetric and idempotent. -/
structure IsOrthProjMat (P : Matrix n n ℝ) : Prop where
  /-- `P` is symmetric. -/
  symm : Pᵀ = P
  /-- `P` is idempotent. -/
  idem : P * P = P

/-- The identity matrix is an orthogonal projector, so `IsOrthProjMat` is satisfiable. -/
example [DecidableEq n] : IsOrthProjMat (1 : Matrix n n ℝ) := ⟨transpose_one, Matrix.mul_one 1⟩

end Curvature

/-! ### Oblique projectors on matrices -/

section ObliqueMatrices

open Matrix Curvature
open scoped LeanDLRA.Frobenius

variable {k l m n : Type*}

/-- The interpolatory (DEIM) / sketched **oblique projector** `𝒫 = U (Sᵀ U)⁻¹ Sᵀ`
[CarrelEtAl2025, eq. (12)]; with `S = Θᵀ Θ U` it is the sketched projector `U (ΘU)⁺ Θ`. -/
noncomputable def obliqueProj [Fintype m] [Fintype k] [DecidableEq k] (U S : Matrix m k ℝ) :
    Matrix m m ℝ :=
  U * (Sᵀ * U)⁻¹ * Sᵀ

variable [Fintype k] [DecidableEq k] [Fintype l] [DecidableEq l] [Fintype m] [Fintype n]
  {U S : Matrix m k ℝ}

/-- The left oblique projector `X ↦ 𝒫 X` on `m × n` matrices (Frobenius norm). -/
noncomputable def leftOblique (U S : Matrix m k ℝ) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  Frobenius.leftMulCLM (obliqueProj U S)

/-- The right oblique projector `X ↦ X 𝒫_Vᵀ = X S (VᵀS)⁻¹ Vᵀ` on `m × n` matrices. -/
noncomputable def rightOblique (V S : Matrix n l ℝ) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  Frobenius.rightMulCLM (obliqueProj V S)ᵀ

/-- `leftOblique U S X = 𝒫 X`. -/
@[simp] lemma leftOblique_apply (U S : Matrix m k ℝ) (X : Matrix m n ℝ) :
    leftOblique U S X = obliqueProj U S * X := rfl

/-- `rightOblique V S X = X 𝒫_Vᵀ`. -/
@[simp] lemma rightOblique_apply (V S : Matrix n l ℝ) (X : Matrix m n ℝ) :
    rightOblique V S X = X * (obliqueProj V S)ᵀ := rfl

end ObliqueMatrices

end LeanDLRA
