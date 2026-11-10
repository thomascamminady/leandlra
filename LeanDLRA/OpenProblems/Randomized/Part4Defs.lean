import LeanDLRA.Matrix.Interpolation
import LeanDLRA.Tensor.Defs

/-!
# Definitions for Randomized Part4

Local definitions used by the theorems of the corresponding modules. The operator `ttTangent` is
the alternating sum `Tensor.ttTangentSum` of the core with shifted right interface operators
(`ttTangent_eq_ttTangentSum`).
-/

open Set
open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

universe u

namespace LeanDLRA.OpenProblems.Randomized

open LeanDLRA.Curvature

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **tensor-train tangent-space projector** built from left interface projectors `L k`
(`P_{≤k}`, acting on the first `k` modes, `L 0 = I`) and right interface projectors `R k`
(`P_{≥k}`, `R (d + 1) = I`) (Lubich–Oseledets–Vandereycken):
`P = ∑_{k=1}^{d} L_{k-1} R_{k+1} - ∑_{k=1}^{d-1} L_k R_{k+1}` (OP-RS-30). -/
noncomputable def ttTangent (d : ℕ) (L R : ℕ → E →L[ℝ] E) : E →L[ℝ] E :=
  ∑ k ∈ Finset.Icc 1 d, L (k - 1) * R (k + 1) - ∑ k ∈ Finset.Icc 1 (d - 1), L k * R (k + 1)

/-- Shifting the summation index: `∑_{k=1}^{n} f k = ∑_{k<n} f (k + 1)`. -/
private theorem sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 n), ih, Finset.sum_range_succ]

/-- **Bridge to the core.** `ttTangent d L R` is the alternating sum `Tensor.ttTangentSum` of the
core with the right interface operators shifted by one index: here `R k` is `P_{≥k}`, while the
right operator with index `k` of `Tensor.ttTangentSum` is `P_{>k}`. -/
theorem ttTangent_eq_ttTangentSum (d : ℕ) (L R : ℕ → E →L[ℝ] E) :
    ttTangent d L R = Tensor.ttTangentSum L (fun k => R (k + 1)) d := by
  unfold ttTangent Tensor.ttTangentSum
  rw [sum_Icc_one_eq_sum_range (fun k => L (k - 1) * R (k + 1)) d,
    sum_Icc_one_eq_sum_range (fun k => L k * R (k + 1)) (d - 1)]
  simp only [Nat.add_sub_cancel]

/-- Non-vacuity of `ttTangent_eq_ttTangentSum` with nonzero data: for identity interface operators
on `ℝ` and two modes both sides are the identity. -/
example : ttTangent 2 (fun _ => (1 : ℝ →L[ℝ] ℝ)) (fun _ => 1) = 1 := by
  rw [ttTangent_eq_ttTangentSum]
  norm_num [Tensor.ttTangentSum]

end Abstract

end LeanDLRA.OpenProblems.Randomized
