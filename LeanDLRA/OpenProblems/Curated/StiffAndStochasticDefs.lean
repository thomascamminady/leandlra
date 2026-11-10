import LeanDLRA.Foundations.OneSided
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Integrators.BUG
import LeanDLRA.Dynamics.ContinuousDLRA
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Filtering.Defs

/-!
# Definitions for StiffAndStochastic

Local definitions used by the theorems of the corresponding modules.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

section Fan

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : ℝ → E → E} {ℓ : ℝ}

end Fan

section Stiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : ℝ → E → E} {ℓ : ℝ}

/-- The 2-dimensional model space `ℝ^{1 × 2}` of the stiff BUG counterexample. -/
abbrev CexSpace := EuclideanSpace ℝ (Fin 2)

/-- The stiff right action `Y ↦ Y diag(0, -κ)` on `1 × 2` matrices (counterexample of
OP-ST-16): linear, one-sided Lipschitz with constant `0`, and tangent to every rank-1 manifold
point, but with Lipschitz constant `κ`. -/
noncomputable def stiffRightField (κ : ℝ) : ℝ → CexSpace → CexSpace :=
  fun _ x => (-κ * x 1) • EuclideanSpace.single 1 (1 : ℝ)

/-- The initial right basis vector `v₀ = (1, 1)/√2` of the counterexample. -/
noncomputable def cexV₀ : CexSpace :=
  (Real.sqrt 2)⁻¹ • (EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 (1 : ℝ))

end Stiff

section AP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The low-rank equilibria of a relaxation operator `C` representable in the Galerkin space of
the projector `Pg`: the subspace `range Pg ⊓ ker C`. -/
def apEquilibria (Pg C : E →L[ℝ] E) : Submodule ℝ E :=
  LinearMap.range (Pg : E →ₗ[ℝ] E) ⊓ LinearMap.ker (C : E →ₗ[ℝ] E)

end AP

section Riccati

open scoped Matrix LeanDLRA.Frobenius

variable {d : ℕ}

/- The field `riccatiField` is defined in `LeanDLRA/Filtering/Defs.lean`.
Proved in `LeanDLRA/Stochastic/KalmanBucy.lean` (OP-SL-01):
`LeanDLRA.KalmanBucy.riccatiField_isOneSidedLipschitzOn` (one-sided Lipschitz on the PSD cone)
and `LeanDLRA.KalmanBucy.dlrKalmanBucy_covariance_error_uniform` (uniform-in-time DLR-KBP
covariance error), with the JMCO variant `jmcoKalmanBucy_covariance_error_uniform`. -/

end Riccati

section Adjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Adjoint

end LeanDLRA
