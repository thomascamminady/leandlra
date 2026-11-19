import LeanDLRA.Tensor.Defs

/-!
# Tree tensor network frames: further definitions

Predicates on the frames of tree tensor network steps (`TTNFrame`, defined in
`LeanDLRA.Tensor.Defs`) that the error analysis of the TTN BUG integrator uses.

## Main definitions

* `TTNFrame.IsCoRangeCommuting`: at every inner node, the admissible mode operators of every
  child commute with the co-range projector of that child.
-/

universe u

namespace LeanDLRA

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- At every inner node of the frame, the admissible mode operators of every child (the class
that contains the new mode projector `P₁ i`) commute with the co-range projector `Q₀ i` of that
child. On tensors the former act on the modes of the subtree and the latter on the other
modes. -/
def TTNFrame.IsCoRangeCommuting : TTNFrame E → Prop
  | .leaf => True
  | .node _ _ Q₀ 𝓛 cs =>
      ∀ i, (∀ M ∈ 𝓛 i, ∀ x, Q₀ i (M x) = M (Q₀ i x)) ∧ (cs i).IsCoRangeCommuting

end LeanDLRA
