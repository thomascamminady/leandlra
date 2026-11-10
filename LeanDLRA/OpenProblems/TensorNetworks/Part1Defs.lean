import LeanDLRA.Integrators.ProjectorSplitting
import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Classical.CommutingProjectorTelescoping
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Tensor.Steps

/-!
# Definitions for TensorNetworks Part1

The constants of the counterexample of OP-TN-05 (`cxA`, `cxAdot`, `ce₁`, `ce₂`, `cxQ₀`, `cxP₁`).
The step predicates of the nested Tucker and of the recursive TTN projector-splitting integrator
(`kslModeField`, `IsTuckerKSLStep`, `IsExactKSteps`, `IsTTNKSLStep`) are defined in
`LeanDLRA/Tensor/Steps.lean`, the tree shapes `TreeShape` in `LeanDLRA/Tensor/Defs.lean`.
-/

open Set Finset
open scoped RealInnerProductSpace

universe u

namespace LeanDLRA.OpenProblems.TensorNetworks

open LeanDLRA

section Defect

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Defect

section Factored

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end Factored

section Truncation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Truncation

section Exactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Exactness

section Counterexample

open scoped Matrix LeanDLRA.Frobenius

/-- The rank-one path `A(t) = e₂ v(t)ᵀ`, `v(t) = cos t e₁ + sin t e₂`, of OP-TN-05. -/
noncomputable def cxA (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; Real.cos t, Real.sin t]

/-- Its derivative `Ȧ(t) = e₂ v'(t)ᵀ`. -/
noncomputable def cxAdot (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0; -Real.sin t, Real.cos t]

/-- The unit column `e₁`. -/
def ce₁ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The unit column `e₂`. -/
def ce₂ : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]

/-- The `K`-step projectors of the counterexample: mode `0` (columns) uses the row space `e₁` of
`A(0)`, mode `1` (rows) the column space `e₁` of the new mode-`0` basis. -/
noncomputable def cxQ₀ : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  ![rightProj ce₁, leftProj ce₁]

/-- The new bases of the counterexample: both `K`-values vanish, so any orthonormal basis is a
valid QR factor; the mode-`0` basis `e₁` is chosen. -/
noncomputable def cxP₁ : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  ![leftProj ce₁, rightProj ce₂]

end Counterexample

section Augmented

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Augmented

section CME

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end CME

end LeanDLRA.OpenProblems.TensorNetworks
