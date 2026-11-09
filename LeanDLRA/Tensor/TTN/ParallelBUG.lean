import LeanDLRA.Tensor.TTN.Integrators
import LeanDLRA.OpenProblems.Curated.TensorNetworksHardParTTNglobalerrorle

/-!
# Basis frames and the parallel BUG integrator on concrete tree tensor networks

The rank-adaptive and parallel tree tensor network (TTN) BUG integrators of the library are stated
over an abstract `TTNFrame`: a tree whose inner nodes carry, for every child `i`, the old basis
projector `P₀ i`, the co-range projector `Q₀ i` of the `K`-step and a class of operators acting on
the child; the parallel TTN BUG step `IsParTTNBUGStep` (Ceruti–Kusch–Lubich–Sulz,
arXiv 2412.00858, §4) assumes these projectors to be orthogonal and to commute. This file builds
such frames from actual tree tensor network data on a dimension tree `τ : DimTree κ`:

* a **basis frame** (`DimTree.BasisFrame`) carries at every inner node `τ = (τ₁, …, τ_m)` an old
  subtree basis `U⁰ᵢ` (rows indexed by the modes of `τᵢ`, `U⁰_{τᵢ} = Mat₀(X⁰_{τᵢ})ᵀ` in the paper)
  and a co-range basis `V⁰ᵢ` (rows indexed by the complementary modes; the matrix `V⁰_{τᵢ}` of the
  paper's restriction `π†_{τ,i}`, prolongated to the full tensor space) for every child, and a
  basis frame of every child;
* its abstract frame (`BasisFrame.toTTNFrame`) has the subtree projectors
  `P₀ i = (τᵢ).subtreeProj U⁰ᵢ`, the co-range projectors `Q₀ i = actOn {k ∉ τᵢ} (V⁰ᵢ V⁰ᵢᵀ)` and the
  operators acting on the modes of `τᵢ` as the class of child `i`;
* a **concrete parallel TTN BUG step** (`BasisFrame.IsParBUGStep`) uses new directions `Ũᵢ` with
  orthonormal columns and `U⁰ᵢᵀ Ũᵢ = 0` (the augmented basis `Ûᵢ = (U⁰ᵢ, Ũᵢ)` of Algorithms 2
  and 4), and is an abstract `IsParTTNBUGStep` on a valid tree: orthogonality of all projectors,
  `P₀ i Pa i = 0` and all commutations are derived from the orthonormality of the matrices and the
  disjointness of the subtrees.

The robust global error bound of the parallel TTN BUG integrator (arXiv 2412.00858, Thm 4.5;
`parTTN_global_error_le`) therefore holds for concrete tree tensor networks
(`BasisFrame.parBUG_global_error`), with constants depending only on `L`, `B`, `Lₜ`, `T` and the
number of nodes of the tree.

## Main definitions

* `DimTree.nodeCount`, `DimTree.treeHeight`: the number of nodes (leaves included) and the height
  of a dimension tree (arXiv 2002.11392, proof of Thm 5.1).
* `DimTree.BasisFrame`, `DimTree.BasisFrame.toTTNFrame`, `DimTree.BasisFrame.IsParBUGStep`.

## Main results

* `DimTree.subtreeProj_subtreeProj_of_orth`: projectors of mutually orthogonal bases of the same
  subtree annihilate each other.
* `DimTree.BasisFrame.toTTNFrame_size`, `DimTree.BasisFrame.toTTNFrame_height`.
* `DimTree.BasisFrame.IsParBUGStep.isParTTNBUGStep`: concrete steps are abstract steps.
* `DimTree.BasisFrame.parBUG_global_error`: Theorem 4.5 of arXiv 2412.00858 on concrete tree
  tensor networks.
-/

open Set
open scoped Matrix RealInnerProductSpace

universe u v

namespace LeanDLRA

namespace DimTree

/-! ### Size and height of a dimension tree -/

section Size

variable {κ : Type*}

/-- The number of nodes of a dimension tree, leaves included (`TTNFrame.size`). -/
def nodeCount : DimTree κ → ℕ
  | leaf _ => 1
  | node cs => 1 + ∑ i, (cs i).nodeCount

/-- The height of a dimension tree: `0` for a leaf, `1 + max` of the heights of the subtrees for
an inner node (arXiv 2002.11392, proof of Thm 5.1; `TTNFrame.height`). -/
def treeHeight : DimTree κ → ℕ
  | leaf _ => 0
  | node cs => (Finset.univ.sup fun i => (cs i).treeHeight) + 1

@[simp] lemma nodeCount_leaf (k : κ) : (leaf k).nodeCount = 1 := rfl

@[simp] lemma treeHeight_leaf (k : κ) : (leaf k).treeHeight = 0 := rfl

lemma nodeCount_node {m : ℕ} (cs : Fin m → DimTree κ) :
    (node cs).nodeCount = 1 + ∑ i, (cs i).nodeCount := rfl

lemma treeHeight_node {m : ℕ} (cs : Fin m → DimTree κ) :
    (node cs).treeHeight = (Finset.univ.sup fun i => (cs i).treeHeight) + 1 := rfl

end Size

variable {κ : Type u} [DecidableEq κ]

/-! ### Basis frames -/

/-- A **basis frame** of a dimension tree `τ`: at every inner node `(τ₁, …, τ_m)` an old subtree
basis `U i` (rows indexed by the modes of `τᵢ`, rank `r i`) and a co-range basis `V i` (rows
indexed by the modes outside `τᵢ`, `s i` columns) for every child, and a basis frame of every
child. These are the matrices `U⁰_{τᵢ}` and `V⁰_{τᵢ}` that the old approximation `Y⁰` determines in
the TTN integrators of arXiv 2002.11392 (§4.2) and arXiv 2412.00858 (§4.1), prolongated to the full
tensor space. -/
inductive BasisFrame (ι : κ → Type v) : DimTree κ → Type (max u v)
  | leaf (k : κ) : BasisFrame ι (.leaf k)
  | node {m : ℕ} {cs : Fin m → DimTree κ} (r s : Fin m → ℕ)
      (U : ∀ i, Matrix (∀ k : {k // k ∈ (cs i).modes}, ι k) (Fin (r i)) ℝ)
      (V : ∀ i, Matrix (∀ k : {k // k ∉ (cs i).modes}, ι k) (Fin (s i)) ℝ)
      (fs : ∀ i, BasisFrame ι (cs i)) : BasisFrame ι (.node cs)

variable [Fintype κ] {ι : κ → Type v} [∀ k, Fintype (ι k)]

/-- Projectors of mutually orthogonal bases of the same subtree annihilate each other. -/
theorem subtreeProj_subtreeProj_of_orth (τ : DimTree κ) {r s : Type*} [Fintype r] [Fintype s]
    {U : Matrix (∀ k : {k // k ∈ τ.modes}, ι k) r ℝ}
    {V : Matrix (∀ k : {k // k ∈ τ.modes}, ι k) s ℝ} (h : Uᵀ * V = 0) (X : Tensor ι) :
    τ.subtreeProj U (τ.subtreeProj V X) = 0 := by
  have h' : U * Uᵀ * (V * Vᵀ) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, h, Matrix.zero_mul, Matrix.mul_zero]
  unfold subtreeProj
  rw [Tensor.actOn_actOn]
  convert congrArg (fun M => Tensor.actOn (ι := ι) (· ∈ τ.modes) M X) h' using 1
  · congr!
  · simp

namespace BasisFrame

/-- The **abstract frame** of a basis frame: the subtree projectors `P₀ i = (τᵢ).subtreeProj U i`,
the co-range projectors `Q₀ i = actOn {k ∉ τᵢ} (V i (V i)ᵀ)`, the operators acting on the modes
of `τᵢ` as the admissible class of child `i`, and the abstract frames of the children. -/
noncomputable def toTTNFrame : {τ : DimTree κ} → BasisFrame ι τ → TTNFrame (Tensor ι)
  | _, .leaf _ => .leaf
  | _, .node (m := m) (cs := cs) _ _ U V fs =>
      .node m (fun i => (cs i).subtreeProj (U i))
        (fun i => Tensor.actOn (· ∉ (cs i).modes) (V i * (V i)ᵀ))
        (fun i => Set.range (Tensor.actOn (ι := ι) (· ∈ (cs i).modes)))
        (fun i => (fs i).toTTNFrame)

/-- The abstract frame has as many nodes as the dimension tree. -/
theorem toTTNFrame_size : ∀ {τ : DimTree κ} (f : BasisFrame ι τ),
    f.toTTNFrame.size = τ.nodeCount
  | _, .leaf _ => rfl
  | _, .node _ _ _ _ fs => by
    simp only [toTTNFrame, TTNFrame.size, nodeCount_node, fun i => toTTNFrame_size (fs i)]

/-- The abstract frame has the height of the dimension tree. -/
theorem toTTNFrame_height : ∀ {τ : DimTree κ} (f : BasisFrame ι τ),
    f.toTTNFrame.height = τ.treeHeight
  | _, .leaf _ => rfl
  | _, .node _ _ _ _ fs => by
    simp only [toTTNFrame, TTNFrame.height, treeHeight_node, fun i => toTTNFrame_height (fs i)]

/-- One step of the **parallel TTN BUG integrator** (Ceruti–Kusch–Lubich–Sulz, arXiv 2412.00858,
§4, Algorithms 1–4) on concrete tree tensor networks with basis frame `f`, for the field `G` on
the full tensor space, doubly-normal bound `ε` and truncation tolerance `ϑ`, from `(t₀, Y₀)` to
`(t₁, Y₁)`:

* at a **leaf** the exact flow of `G`;
* at an **inner node** the old bases `U i` and co-range bases `V i` have orthonormal columns and
  their projectors `P₀ i`, `Q₀ i` fix `Y₀`; there are new directions `Ũᵢ` with orthonormal columns
  and `U iᵀ Ũᵢ = 0` (projectors `Pa i`), subtree results `K i` computed by the same integrator on
  the children for the `K`-step fields `Q₀ i G` from `Y₀`, captured by the augmented bases
  (`(P₀ i + Pa i) K i = K i`) with doubly-normal component at most `ε`; the core step
  `YC' = (∏ P₀ i) G(t, YC)` in the old bases from `Y₀` (Algorithm 3); the normal component of
  `G(t₀, Y₀)` with respect to the tangent hull is at most `ε`; and `Y₁` is within `ϑ` of the
  augmented tensor `parTuckerBUG P₀ Pa (YC t₁) (t₁ - t₀) (G t₀ Y₀)` (Algorithm 4, blocks
  (4.1)–(4.2), followed by a truncation). -/
def IsParBUGStep : {τ : DimTree κ} → BasisFrame ι τ → (ℝ → Tensor ι → Tensor ι) → ℝ → ℝ → ℝ →
    ℝ → Tensor ι → Tensor ι → Prop
  | _, .leaf _, G, _, _, t₀, t₁, Y₀, Y₁ =>
      ∃ y : ℝ → Tensor ι, ODESolution G y t₀ t₁ ∧ y t₀ = Y₀ ∧ y t₁ = Y₁
  | _, .node (m := m) (cs := cs) _ _ U V fs, G, ε, ϑ, t₀, t₁, Y₀, Y₁ =>
      (∀ i, (U i)ᵀ * U i = 1) ∧ (∀ i, (V i)ᵀ * V i = 1) ∧
      (∀ i, (cs i).subtreeProj (U i) Y₀ = Y₀) ∧
      (∀ i, Tensor.actOn (· ∉ (cs i).modes) (V i * (V i)ᵀ) Y₀ = Y₀) ∧
      ∃ (ra : Fin m → ℕ) (Ua : ∀ i, Matrix (∀ k : {k // k ∈ (cs i).modes}, ι k) (Fin (ra i)) ℝ)
        (K : Fin m → Tensor ι) (YC : ℝ → Tensor ι),
        (∀ i, (Ua i)ᵀ * Ua i = 1) ∧ (∀ i, (U i)ᵀ * Ua i = 0) ∧
        (∀ i, IsParBUGStep (fs i)
          (fun t x => Tensor.actOn (· ∉ (cs i).modes) (V i * (V i)ᵀ) (G t x)) ε ϑ t₀ t₁ Y₀
          (K i)) ∧
        (∀ i, ((cs i).subtreeProj (U i) + (cs i).subtreeProj (Ua i)) (K i) = K i) ∧
        (∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - ((cs i).subtreeProj (U i) + (cs i).subtreeProj (Ua i)))
          ((1 - Tensor.actOn (· ∉ (cs i).modes) (V i * (V i)ᵀ)) (G t (K i)))‖ ≤ ε) ∧
        ODESolution (fun t x => modeProd (fun i => (cs i).subtreeProj (U i)) (G t x)) YC t₀ t₁ ∧
        YC t₀ = Y₀ ∧
        ‖G t₀ Y₀ - modeProdLeOne (fun i => (cs i).subtreeProj (U i))
          (fun i => 1 - (cs i).subtreeProj (U i)) (G t₀ Y₀)‖ ≤ ε ∧
        ‖Y₁ - parTuckerBUG (fun i => (cs i).subtreeProj (U i))
          (fun i => (cs i).subtreeProj (Ua i)) (YC t₁) (t₁ - t₀) (G t₀ Y₀)‖ ≤ ϑ

/-- **Concrete parallel TTN BUG steps are abstract steps.** On a valid dimension tree, every
concrete parallel TTN BUG step with basis frame `f` is an `IsParTTNBUGStep` with the abstract
frame `f.toTTNFrame`: the orthogonality of all projectors, `P₀ i Pa i = 0` and the commutation of
`P₀ i`, `Pa j` are derived from the orthonormality of the bases and the disjointness of the
subtrees of a valid tree. -/
theorem IsParBUGStep.isParTTNBUGStep : ∀ {τ : DimTree κ} (f : BasisFrame ι τ)
    {G : ℝ → Tensor ι → Tensor ι} {ε ϑ t₀ t₁ : ℝ} {Y₀ Y₁ : Tensor ι}, τ.IsValid →
    f.IsParBUGStep G ε ϑ t₀ t₁ Y₀ Y₁ → IsParTTNBUGStep f.toTTNFrame G ε ϑ t₀ t₁ Y₀ Y₁ := by
  intro τ f
  induction f with
  | leaf k => intro G ε ϑ t₀ t₁ Y₀ Y₁ _ h; exact h
  | node r s U V fs ih =>
    rename_i m cs
    intro G ε ϑ t₀ t₁ Y₀ Y₁ hv h
    obtain ⟨hU, hV, hP, hQ, _, Ua, K, YC, hUa, horth, hch, hcap, hn, hC, hC₀, hn₀, htr⟩ := h
    have horth' : ∀ i, (Ua i)ᵀ * U i = 0 := fun i => by
      rw [← Matrix.transpose_transpose (U i), ← Matrix.transpose_mul, horth i,
        Matrix.transpose_zero]
    refine ⟨fun i => isOrthProj_subtreeProj _ (hU i), fun i => isOrthProj_coRangeProj _ (hV i),
      hP, hQ, fun i => (cs i).subtreeProj (Ua i), K, YC,
      fun i => isOrthProj_subtreeProj _ (hUa i),
      fun i x => subtreeProj_subtreeProj_of_orth _ (horth i) x, hv.subtreeProj_comm U,
      fun i j x => ?_, hv.subtreeProj_comm Ua,
      fun i => ih i (hv.child i) (hch i), hcap, hn, hC, hC₀, hn₀, htr⟩
    by_cases hij : i = j
    · subst hij
      rw [subtreeProj_subtreeProj_of_orth _ (horth i),
        subtreeProj_subtreeProj_of_orth _ (horth' i)]
    · exact subtreeProj_comm_of_disjoint (hv.disjoint hij) _ _ x

/-- **Robust global error of the parallel TTN BUG integrator on concrete tree tensor networks**
(Ceruti–Kusch–Lubich–Sulz, arXiv 2412.00858, Theorem 4.5). Let `τ` be a valid dimension tree with
`s` nodes and height `ℓ`, `F` a field on the tensor space that is `L`-Lipschitz, bounded by `B`,
continuous in time and `Lₜ`-Lipschitz in time, `tₙ = t₀ + n h` with `2 L h ℓ ≤ 1`, and `A` the
exact solution on `[t₀, t_N]`. If every step `n < N` is a concrete parallel TTN BUG step with some
basis frame of `τ`, doubly-normal bound `ε ≥ 0` and truncation tolerance `ϑ ≥ 0` at every node,
then for `n ≤ N` with `n h ≤ T`

    ‖Yₙ - A(tₙ)‖ ≤ e^{L T} (δ + 3 s T (2 ε + (9 L B + Lₜ) h) + 3 s n ϑ),

independently of the singular values of the matricizations of the connecting tensors. -/
theorem parBUG_global_error {τ : DimTree κ} (hv : τ.IsValid) {F : ℝ → Tensor ι → Tensor ι}
    {L B Lt ε ϑ : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → ‖F t x - F s x‖ ≤ Lt * (t - s)) (hε : 0 ≤ ε) (hϑ : 0 ≤ ϑ)
    {t₀ h : ℝ} (hh : 0 ≤ h) (hLh : 2 * L * h * τ.treeHeight ≤ 1) {N : ℕ}
    {A : ℝ → Tensor ι} (hA : ODESolution F A t₀ (t₀ + N * h)) {f : ℕ → BasisFrame ι τ}
    {Y : ℕ → Tensor ι}
    (hstep : ∀ n < N, (f n).IsParBUGStep F ε ϑ (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (Y (n + 1)))
    {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) *
        (δ + T * (3 * τ.nodeCount * (2 * ε + (9 * L * B + Lt) * h)) +
          3 * τ.nodeCount * (n * ϑ)) :=
  parTTN_global_error_le hF hL hB hcont hLt hFt hε hϑ hh hA (fr := fun n => (f n).toTTNFrame)
    (fun n _ => (toTTNFrame_size (f n)).le) (fun n _ => (toTTNFrame_height (f n)).le) hLh
    (fun n hn => (hstep n hn).isParTTNBUGStep (f n) hv) hδ

end BasisFrame

/-! ### Non-vacuity -/

/-- Non-vacuity of `BasisFrame.IsParBUGStep` at an inner node: on the valid tree with two leaves
(modes `0` and `1` of dimension one), the zero field with the zero tensor, rank-zero bases and no
new directions is a parallel TTN BUG step. -/
example : (BasisFrame.node (ι := fun _ : Fin 2 => Fin 1) (cs := fun i : Fin 2 => leaf i)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun i => BasisFrame.leaf i)).IsParBUGStep
      (fun _ _ => 0) 0 0 0 1 0 0 := by
  have hz : ODESolution (fun _ _ => (0 : Tensor (fun _ : Fin 2 => Fin 1))) (fun _ => 0) 0 1 :=
    ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) _⟩
  refine ⟨fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _, fun _ => map_zero _,
    fun _ => map_zero _, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
    fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _, fun i => ?_,
    fun _ => map_zero _, fun _ t _ => by simp, by simpa using hz, rfl, by simp,
    by simp [parTuckerBUG]⟩
  refine ⟨fun _ => 0, ?_, rfl, rfl⟩
  convert hz using 1
  funext t x
  simp

/-- The dimension tree with two leaves `0` and `1` of the non-vacuity example is valid, so the
example step is an abstract parallel TTN BUG step. -/
example : (node fun i : Fin 2 => leaf i).IsValid :=
  ⟨fun _ => trivial, fun _ _ hij => Finset.disjoint_singleton.2 hij⟩

end DimTree

end LeanDLRA
