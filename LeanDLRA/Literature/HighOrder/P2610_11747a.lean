import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Integrators.TuckerBUG

/-!
# Results of arXiv 2610.11747: Robust second-order TTN/Tucker BUG

This module proves the abstract core of **Lemma 3.4** (the pre-augmented bases `Û⁰_i =
orth[U⁰_i, F_i(Y0) V⁰_i]` capture `F(Y0)` up to the sum of the normal-component bounds). On an
abstract real inner product space `E` (tensors with the Euclidean norm), `P0 i`, `Q0 i` are the
commuting orthogonal projectors onto the column space / co-range of the `i`-th matricization of
`Y0`, `Phat i` the orthogonal projector onto the augmented basis, and `T i` a map with range in
the matrix tangent space at `Y0`. The scalars are real; the paper's tensors are complex.

Not in this module: Theorems 3.3, 4.1 and 5.3 are proved, in an abstract projector form, in the
companion module `P2610_11747b`, which uses adapted forms of Lemmas 3.5-3.8 as private steps and
does not state them separately. Theorems 4.3-4.5 are not restated. The
library has abstract analogues for a Galerkin step from `Y⁰` on augmented bases, stated for
arXiv 2104.05247 in `LeanDLRA.Integrators.TuckerBUG`: `IsAugTuckerBUGStep.norm_eq`, `norm_sub_le`
(Thm 4.3), `energy_eq_of_skew`, `energy_sub_le_of_skew` (Thm 4.4), `energy_le`,
`energy_le_trunc` (Thm 4.5 without the decrease `α² h`). There the truncation enters as
`‖Y₁ - Ŷ₁‖ ≤ ϑ`, not through the paper's constant `c = ‖C⁰‖(d - 1) + 1`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2610_11747

open LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Single-mode step of Lemma 3.4: if `Phat` fixes the range of `P0` and the vector `Q0 F`, then
`(1 - Phat) F = (1 - Phat)(1 - P0)(1 - Q0) F`, hence the bound by the doubly-normal part. -/
theorem norm_sub_apply_le_normal {P0 Q0 Phat : E →L[ℝ] E} (hPhat : IsOrthProj Phat)
    (hP0 : ∀ x, Phat (P0 x) = P0 x) (z : E) (hQ0 : Phat (Q0 z) = Q0 z) :
    ‖z - Phat z‖ ≤ ‖(1 - P0) ((1 - Q0) z)‖ := by
  have h1 : z - Phat z = (1 - Phat) ((1 - P0) ((1 - Q0) z)) := by
    simp only [sub_apply, one_apply_eq_self, map_sub, hP0, hQ0]
    abel
  rw [h1]
  exact hPhat.compl.norm_le _

/-- **Lemma 3.4 (pre-augmented basis captures `F(Y0)`)**, arXiv 2610.11747, abstract form.
Let `Fy0 = F(Y0) ∈ E`. For every mode `j : Fin d` let `P0 j`, `Q0 j` be commuting orthogonal
projectors (column space and co-range of `Mat_j(Y0)`), `Phat j` the orthogonal projector onto the
augmented basis, which fixes the range of `P0 j` (`U⁰_j ⊂ Û⁰_j`) and the range of `Q0 j`
applied to `Fy0` (the columns of `F_j(Y0) V⁰_j`), and `T j` a map with range in the matrix
tangent space `P0 j + Q0 j - P0 j Q0 j` (the Tucker tangent space at `Y0` lies in it) with normal
bound `‖Fy0 - T j Fy0‖ ≤ ε j` (the paper's `ε^{(j)}_{r_j}`: with `T j` the paper's `M_j` of
(12), this is `‖R_j(Y⁰_j)‖ ≤ ε^{(j)}_{r_j}` from A2). Then
`‖F(Y0) - F(Y0) ×_j Û⁰_j Û⁰_jᵀ‖ ≤ ∑_j ε j` (14), the product being `modeProd Phat`.
Differences from the paper: real scalars (the paper's tensors are complex); tensors and
matricizations are abstracted to projectors, as in `LeanDLRA.Integrators.TuckerBUG`; no
commutation of the `Phat j` is needed. The matricized form (15) is not stated separately. -/
theorem lemma_3_4 {d : ℕ} {P0 Q0 Phat T : Fin d → E →L[ℝ] E} {ε : Fin d → ℝ} (Fy0 : E)
    (hP0 : ∀ j, IsOrthProj (P0 j)) (hQ0 : ∀ j, IsOrthProj (Q0 j))
    (hc : ∀ j x, P0 j (Q0 j x) = Q0 j (P0 j x)) (hPhat : ∀ j, IsOrthProj (Phat j))
    (hPP : ∀ j x, Phat j (P0 j x) = P0 j x) (hPQ : ∀ j, Phat j (Q0 j Fy0) = Q0 j Fy0)
    (hT : ∀ j y, tangent (P0 j) (Q0 j) (T j y) = T j y)
    (hε : ∀ j, ‖Fy0 - T j Fy0‖ ≤ ε j) :
    ‖Fy0 - modeProd Phat Fy0‖ ≤ ∑ j, ε j := by
  refine (norm_sub_modeProd_apply_le (fun j => (hPhat j).norm_le) Fy0).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  exact (norm_sub_apply_le_normal (hPhat j) (hPP j) Fy0 (hPQ j)).trans
    ((norm_normal_le_of_tangent (hP0 j) (hQ0 j) (hc j) (hT j) Fy0).trans (hε j))

/-- Non-vacuity: on `ℝ` with one mode, `P0 = Q0 = 0`, `Phat = 1`, `T = 0` satisfy all
hypotheses of `lemma_3_4` with `ε = ‖Fy0‖`. -/
example (Fy0 : ℝ) : ‖Fy0 - modeProd (fun _ : Fin 1 => (1 : ℝ →L[ℝ] ℝ)) Fy0‖ ≤ ∑ _j : Fin 1, ‖Fy0‖ :=
  lemma_3_4 (P0 := fun _ => 0) (Q0 := fun _ => 0) (T := fun _ => 0) (ε := fun _ => ‖Fy0‖) Fy0
    (fun _ => ⟨fun x => by simp, fun x y => by simp⟩)
    (fun _ => ⟨fun x => by simp, fun x y => by simp⟩) (fun _ x => by simp)
    (fun _ => ⟨fun x => by simp, fun x y => by simp⟩) (fun _ x => by simp) (fun _ => by simp)
    (fun _ y => by simp) (fun _ => by simp)

end LeanDLRA.Literature.P2610_11747
