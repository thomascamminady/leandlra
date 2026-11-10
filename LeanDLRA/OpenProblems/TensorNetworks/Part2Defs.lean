import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Stability.Energy
import LeanDLRA.Tensor.Defs
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Definitions for TensorNetworks Part2

Local definitions used by the theorems of the corresponding modules. The alternating sum
`ttTangentSum` is `Tensor.ttTangentSum` of the core (`ttTangentSum_eq_tensor`).
-/

open Set Finset
open scoped RealInnerProductSpace

universe u

namespace LeanDLRA.OpenProblems.TensorNetworks

open LeanDLRA

section Training

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n]

end Training

section TrainingAbstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end TrainingAbstract

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : ℝ → E → E} {ε t₀ t₁ : ℝ} {d : ℕ}

end Transfer

section RankAdaptive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end RankAdaptive

section TTTangent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The alternating sum of TT interface projectors
`P_Y = ∑_{k=1}^{d} P_{≤k-1} P_{>k} - ∑_{k=1}^{d-1} P_{≤k} P_{>k}` (arXiv 2402.18721, Prop. 4.1;
Lubich–Oseledets–Vandereycken, arXiv 1407.2042, Thm 3.1), with left interface projectors `Pl k`
(`P_{≤k}`, acting on the modes `1, …, k`, `Pl 0 = 1`) and right interface projectors `Pr k`
(`P_{>k}`, acting on the modes `k+1, …, d`, `Pr d = 1`), all in full-space form. -/
def ttTangentSum (Pl Pr : ℕ → E →L[ℝ] E) (d : ℕ) : E →L[ℝ] E :=
  (∑ k ∈ range d, Pl k * Pr (k + 1)) - ∑ k ∈ range (d - 1), Pl (k + 1) * Pr (k + 1)

/-- **Bridge to the core.** The alternating sum `ttTangentSum` of this file is
`Tensor.ttTangentSum` of the core: the same expression, which the core states for every normed
space. -/
theorem ttTangentSum_eq_tensor (Pl Pr : ℕ → E →L[ℝ] E) (d : ℕ) :
    ttTangentSum Pl Pr d = Tensor.ttTangentSum Pl Pr d :=
  rfl

/-- Non-vacuity of `ttTangentSum_eq_tensor` with nonzero data: for identity interface operators on
`ℝ` and two modes both sides are the identity. -/
example : ttTangentSum (fun _ => (1 : ℝ →L[ℝ] ℝ)) (fun _ => 1) 2 = 1 := by
  rw [ttTangentSum_eq_tensor]
  norm_num [Tensor.ttTangentSum]

end TTTangent

section Schmidt

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The linear map `X ↦ ∑ₖ Bₖ X Cₖᵀ` on `m × n` matrices: a generator of operator Schmidt rank
`≤ s` across the cut between the row and the column species groups. -/
noncomputable def schmidtOp {s : ℕ} (B : Fin s → Matrix m m ℝ) (C : Fin s → Matrix n n ℝ) :
    Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  ∑ k, (Frobenius.leftMulCLM (B k)).comp (Frobenius.rightMulCLM (C k)ᵀ)

end Schmidt

section Hybrid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One step of the parallel Tucker BUG integrator (`IsParTuckerBUGStep`) in which the new
directions `Pa i` may be missing (e.g. `Pa i = 0` for frozen classical–quantum bonds of hybrid
tensor networks): the augmented basis `P₀ i + Pa i` captures the `K`-value only up to `η i`. -/
structure IsDefectParTuckerStep (F : ℝ → E → E) (ε : ℝ) {d : ℕ} (Q₀ P₀ Pa : Fin d → E →L[ℝ] E)
    (η : Fin d → ℝ) (t₀ t₁ : ℝ) (Y₀ : E) (YK : Fin d → ℝ → E) (YC : ℝ → E) : Prop where
  projQ₀ : ∀ i, IsOrthProj (Q₀ i)
  projP₀ : ∀ i, IsOrthProj (P₀ i)
  projPa : ∀ i, IsOrthProj (Pa i)
  orth : ∀ i x, P₀ i (Pa i x) = 0
  comm₀₀ : ∀ i j x, P₀ i (P₀ j x) = P₀ j (P₀ i x)
  comm₀a : ∀ i j x, P₀ i (Pa j x) = Pa j (P₀ i x)
  commaa : ∀ i j x, Pa i (Pa j x) = Pa j (Pa i x)
  start₀ : ∀ i, P₀ i Y₀ = Y₀
  kSol : ∀ i, ODESolution (fun t x => Q₀ i (F t x)) (YK i) t₀ t₁
  kStart : ∀ i, YK i t₀ = Y₀
  /-- Capture with defect `η i` (`η i = 0` for augmented modes). -/
  kDef : ∀ i, ‖(1 - (P₀ i + Pa i)) (YK i t₁)‖ ≤ η i
  kNormal : ∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - (P₀ i + Pa i)) ((1 - Q₀ i) (F t (YK i t₁)))‖ ≤ ε
  cSol : ODESolution (fun t x => modeProd P₀ (F t x)) YC t₀ t₁
  cStart : YC t₀ = Y₀
  normal₀ : ‖F t₀ Y₀ - modeProdLeOne P₀ (fun i => 1 - P₀ i) (F t₀ Y₀)‖ ≤ ε

end Hybrid

section Stiff

open scoped Matrix

end Stiff

end LeanDLRA.OpenProblems.TensorNetworks
