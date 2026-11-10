import LeanDLRA.LinearAlgebra.LowRank.Defs
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Definitions: singular vectors and the truncated SVD

The vocabulary of the SVD layer (`LinearAlgebra/SVD/`). Mathlib provides the singular values
`LinearMap.singularValues` of a linear map between finite-dimensional inner product spaces (the
square roots of the eigenvalues of `T† T`, sorted decreasingly and indexed from `0`), but no
singular vectors. This file defines the singular vectors of a linear map and the right singular
vectors and the truncated SVD `A V_r V_rᵀ` of a real matrix.

The theorems about these objects are in `LeanDLRA/Classical/SVD.lean` (thin SVD, smallest singular
value) and `LeanDLRA/Classical/EckartYoung.lean` (optimality of the truncated SVD). The
singular-value tail `WeylSingular.tailNorm` and the POD basis `KyFan.podBasis` are defined in
`LeanDLRA/LinearAlgebra/LowRank/Defs.lean`.

## Main definitions

* `LinearMap.rightSingularBasis T`: an orthonormal eigenbasis `e₀, …, e_{d-1}` of `T† T`, sorted
  so that `T† T eᵢ = σᵢ² eᵢ` (`d = dim E`); `LinearMap.rightSingularVectors T`: `vᵢ = eᵢ` for
  `i < r = dim range T`; `LinearMap.leftSingularVectors T`: `uᵢ = σᵢ⁻¹ T vᵢ` for `i < r`.
* `LeanDLRA.EckartYoung.rightSingularVectors A`: the right singular vectors of a real matrix `A`,
  an orthonormal eigenbasis of `Aᵀ A`; `LeanDLRA.EckartYoung.topRightSingularVectors A r`: the
  matrix `V_r` of the first `r` of them; `LeanDLRA.EckartYoung.truncation A r = A V_r V_rᵀ`: the
  truncated SVD of rank at most `r`.

## Main results

* `LinearMap.finrank_range_le_finrank`: `dim range T ≤ dim E`.

## Implementation notes

The eigenbases are indexed by `Fin (finrank ℝ (EuclideanSpace ℝ n))`, as produced by
`LinearMap.IsSymmetric.eigenvectorBasis` with `hn := rfl`, which is also how
`LinearMap.singularValues` is defined. The names in the namespace `EckartYoung` are kept from the
file that uses them.
-/

/-! ### Singular vectors of a linear map -/

section SingularVectors

open Module Submodule
open scoped InnerProductSpace ComplexConjugate

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

/-- The **right singular basis** of `T`: an orthonormal eigenbasis `e₀, …, e_{d-1}` of `T† T`,
sorted so that the eigenvalues `σᵢ(T)²` decrease (`d = dim E`). -/
noncomputable def rightSingularBasis : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

omit [FiniteDimensional 𝕜 F] in
/-- `dim range T ≤ dim E`. -/
theorem finrank_range_le_finrank : finrank 𝕜 (range T) ≤ finrank 𝕜 E :=
  T.finrank_range_le

/-- The **right singular vectors** `vᵢ = eᵢ`, `i < r = dim range T`. -/
noncomputable def rightSingularVectors : Fin (finrank 𝕜 (range T)) → E :=
  fun i => T.rightSingularBasis (Fin.castLE T.finrank_range_le_finrank i)

/-- The **left singular vectors** `uᵢ = σᵢ⁻¹ T vᵢ`, `i < r = dim range T`. -/
noncomputable def leftSingularVectors : Fin (finrank 𝕜 (range T)) → F :=
  fun i => ((T.singularValues i : ℝ) : 𝕜)⁻¹ • T (T.rightSingularVectors i)

end LinearMap

end SingularVectors

/-! ### Right singular vectors and the truncated SVD of a real matrix -/

section Truncation

open Matrix WithLp Module Finset
open scoped RealInnerProductSpace

namespace LeanDLRA.EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The right singular vectors of `A`: an orthonormal eigenbasis of `Aᵀ A` (as the operator
`T† T`, `T = toEuclideanLin A`), sorted so that the eigenvalues `σ_i(A)²` decrease. -/
noncomputable def rightSingularVectors (A : Matrix m n ℝ) :
    OrthonormalBasis (Fin (finrank ℝ (EuclideanSpace ℝ n))) ℝ (EuclideanSpace ℝ n) :=
  (toEuclideanLin A).isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

/-- `V_r`: the matrix whose columns are the right singular vectors `e_i`, `i < r`. -/
noncomputable def topRightSingularVectors (A : Matrix m n ℝ) (r : ℕ) :
    Matrix n {i : Fin (finrank ℝ (EuclideanSpace ℝ n)) // (i : ℕ) < r} ℝ :=
  fun j i ↦ rightSingularVectors A i j

/-- The **truncated SVD** `B⋆ = A V_r V_rᵀ` of rank `≤ r`. -/
noncomputable def truncation (A : Matrix m n ℝ) (r : ℕ) : Matrix m n ℝ :=
  A * topRightSingularVectors A r * (topRightSingularVectors A r)ᵀ

end LeanDLRA.EckartYoung

end Truncation
