import LeanDLRA.Training.Descent
import LeanDLRA.Training.Defs
import LeanDLRA.Matrix.Projectors

/-!
# Definitions for Training

Local definitions used by the theorems of the corresponding modules. The uncorrected federated
iterates `fedAvgClientIter`, `fedAvgRound` are defined in `LeanDLRA/Training/Defs.lean`.
-/

open Set Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section PL

variable {ℒ : E → ℝ} {g : E → E} {β : ℝ}

end PL

section Refresh

variable {ℒ : E → ℝ} {g : E → E} {β : ℝ}

end Refresh

section RefreshMatrix

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n]

end RefreshMatrix

section Precond

variable {ℒ : E → ℝ} {g : E → E} {β : ℝ}

end Precond

section Federated

variable {ι : Type*} {ℒ : E → ℝ} {g : E → E} {β lr : ℝ} {P : E →L[ℝ] E} {gc : ι → E → E}

end Federated

end LeanDLRA
