import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2002.11392: Time integration of tree tensor networks

This module formalizes the abstract core of two results of Ceruti–Lubich–Walach,
arXiv 2002.11392, in the setting of real inner product spaces `E` (the big space, e.g. a
tensor space) and `F` (the small space of a tree node). The prolongation `π : F →L[ℝ] E` is an
isometric embedding in the sense `π† (π Y) = Y`, and `π† = π.adjoint` is its restriction.

* **Lemma 4.1 restriction/prolongation** (`restriction_prolongation`).
  Given `π† (π Y) = Y` for all `Y`, we prove `π† (π Y) = Y`, `⟪π Y, Z⟫ = ⟪Y, π† Z⟫`,
  `‖π Y‖ = ‖Y‖` and `‖π† Z‖ ≤ ‖Z‖`. **Conditional** on (4.8): the hypothesis `π† π = 1` is the
  first claim of the paper's lemma, which the paper derives from `V⁰ᵀ V⁰ = 1`; for the concrete
  prolongation it is proved in the tensor core (`DimTree.restrict_prolong`). An `example` exhibits
  an instance (the identity on `ℝ`).

* **Lemma 6.2, `L` and `B` parts** (`reduced_field_lipschitz_bounded`).
  If `G` is `L`-Lipschitz and bounded by `B` on `S`, and `π` maps `T` into `S`, then the reduced
  field `π† ∘ G ∘ π` is `L`-Lipschitz and bounded by `B` on `T`. The `ε`-part
  (`‖F − P(Y)F‖ ≤ ε`) is NOT formalized: it needs the tangent spaces of the reduced manifold,
  which are not modelled here.

The other results of the paper are in part b (`P2002_11392b.lean`) and in the tensor core:
Lemma 2.4 (`P2002_11392.basis_transpose_mul_self_iff`, `TTN.basis_transpose_mul_self`), the
concrete prolongation and restriction of Lemma 4.1 and Definition 4.2
(`LeanDLRA/Tensor/TTN/Prolongation.lean`), Theorem 5.1
(`DimTree.IsNondegenerateProjectorSplittingStep.eq`) and Theorem 6.1
(`DimTree.projectorSplitting_global_error`); part b lists what is not formalized (Lemmas 2.5,
3.1, 4.3, 4.4, 6.3 and the `ε`-part of Lemma 6.2).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2002_11392

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The isometry property `π† (π y) = y` implies `‖π y‖ = ‖y‖`. -/
private lemma norm_prolong_eq {π : F →L[ℝ] E} (hπ : ∀ y, π.adjoint (π y) = y) (y : F) :
    ‖π y‖ = ‖y‖ := by
  have h : ‖π y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← ContinuousLinearMap.adjoint_inner_right, hπ]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- **Lemma 4.1 (restriction/prolongation), arXiv 2002.11392.**
For a continuous linear map `π : F → E` between real Hilbert spaces with `π† (π Y) = Y` for all
`Y` (the abstract isometry `J* J = I`, i.e. (4.8) itself, which the paper derives from
`V⁰ᵀ V⁰ = 1`; see `DimTree.restrict_prolong` for the concrete maps), the four identities hold:
`π† (π Y) = Y`, `⟪π Y, Z⟫ = ⟪Y, π† Z⟫`, `‖π Y‖ = ‖Y‖` and `‖π† Z‖ ≤ ‖Z‖`. -/
theorem restriction_prolongation (π : F →L[ℝ] E) (hπ : ∀ Y, π.adjoint (π Y) = Y) :
    (∀ Y, π.adjoint (π Y) = Y) ∧
    (∀ (Y : F) (Z : E), ⟪π Y, Z⟫ = ⟪Y, π.adjoint Z⟫) ∧
    (∀ Y, ‖π Y‖ = ‖Y‖) ∧
    (∀ Z : E, ‖π.adjoint Z‖ ≤ ‖Z‖) := by
  refine ⟨hπ, fun Y Z => (ContinuousLinearMap.adjoint_inner_right π Y Z).symm,
    norm_prolong_eq hπ, fun Z => ?_⟩
  have e1 := ContinuousLinearMap.adjoint_inner_right π (π.adjoint Z) Z
  have h1 : ‖π.adjoint Z‖ * ‖π.adjoint Z‖ ≤ ‖π.adjoint Z‖ * ‖Z‖ := by
    calc ‖π.adjoint Z‖ * ‖π.adjoint Z‖ = ⟪π.adjoint Z, π.adjoint Z⟫ :=
          (real_inner_self_eq_norm_mul_norm _).symm
      _ = ⟪π (π.adjoint Z), Z⟫ := e1
      _ ≤ ‖π (π.adjoint Z)‖ * ‖Z‖ := real_inner_le_norm _ _
      _ = ‖π.adjoint Z‖ * ‖Z‖ := by rw [norm_prolong_eq hπ]
  rcases (norm_nonneg (π.adjoint Z)).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg Z
  · exact le_of_mul_le_mul_left h1 hpos

/-- Example (non-vacuity): the identity on `ℝ` satisfies the hypothesis of Lemma 4.1. -/
example : ∀ Y : ℝ, (ContinuousLinearMap.id ℝ ℝ).adjoint (ContinuousLinearMap.id ℝ ℝ Y) = Y :=
  fun Y => by rw [ContinuousLinearMap.adjoint_id]; rfl

/-- **Lemma 6.2, Lipschitz and bound parts (arXiv 2002.11392).**
Let `π : F → E` satisfy `π† (π Y) = Y`. Let `G : ℝ → E → E` be `L`-Lipschitz and bounded by `B`
on a set `S ⊆ E`, and let `π` map `T ⊆ F` into `S`. Then the reduced field `π† ∘ G ∘ π` is
`L`-Lipschitz on `T` and bounded by `B` on `T`. The `ε`-part (6.7) of the paper is not
formalized. -/
theorem reduced_field_lipschitz_bounded (π : F →L[ℝ] E) (hπ : ∀ Y, π.adjoint (π Y) = Y)
    {S : Set E} {T : Set F} (hT : ∀ y ∈ T, π y ∈ S) {L B : ℝ} {G : ℝ → E → E}
    (hL : ∀ t, ∀ x ∈ S, ∀ x' ∈ S, ‖G t x - G t x'‖ ≤ L * ‖x - x'‖)
    (hB : ∀ t, ∀ x ∈ S, ‖G t x‖ ≤ B) :
    (∀ t, ∀ y ∈ T, ∀ y' ∈ T,
      ‖π.adjoint (G t (π y)) - π.adjoint (G t (π y'))‖ ≤ L * ‖y - y'‖) ∧
    (∀ t, ∀ y ∈ T, ‖π.adjoint (G t (π y))‖ ≤ B) := by
  refine ⟨fun t y hy y' hy' => ?_, fun t y hy => ?_⟩
  · rw [← map_sub]
    calc ‖π.adjoint (G t (π y) - G t (π y'))‖ ≤ ‖G t (π y) - G t (π y')‖ :=
          (restriction_prolongation π hπ).2.2.2 _
      _ ≤ L * ‖π y - π y'‖ := hL t _ (hT y hy) _ (hT y' hy')
      _ = L * ‖y - y'‖ := by rw [← map_sub, norm_prolong_eq hπ]
  · exact ((restriction_prolongation π hπ).2.2.2 _).trans (hB t _ (hT y hy))

end LeanDLRA.Literature.P2002_11392
