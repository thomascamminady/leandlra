import LeanDLRA.Tensor.TTN.ParallelBUG
import LeanDLRA.Tensor.TTN.Abstract.RankAdaptiveBUG

/-!
# The rank-adaptive BUG integrator on concrete tree tensor networks

The rank-adaptive tree tensor network (TTN) BUG integrator of Ceruti–Lubich–Sulz (SINUM 2023) is
stated in the library over an abstract `TTNFrame` (`IsAugTTNBUGStep`), and its error bound is
proved at that level (`augTTN_global_error_le`). This file states the step on actual tree tensor
network data, over a basis frame `f : DimTree.BasisFrame ι τ` of a dimension tree `τ`:

* a **concrete rank-adaptive TTN BUG step** (`BasisFrame.IsAugBUGStep`) uses at every inner node
  new directions `Ũᵢ` with orthonormal columns and `U⁰ᵢᵀ Ũᵢ = 0`, so that `Ûᵢ = (U⁰ᵢ, Ũᵢ)` is the
  augmented basis, and is an abstract `IsAugTTNBUGStep` with the frame `f.toTTNFrame` on a valid
  tree: the projector `P₁ i = P₀ i + Pa i` of the augmented basis is orthogonal, contains the old
  one (`P₁ i P₀ i = P₀ i`) and acts on the modes of `τᵢ`, and the projectors of different
  children commute; all of this is derived from the orthonormality of the matrices and the
  disjointness of the subtrees.

The robust global error bound of the rank-adaptive TTN BUG integrator therefore holds for concrete
tree tensor networks (`BasisFrame.augBUG_global_error`), with constants depending only on `L`,
`B`, `T` and the number of nodes of the tree.

## Main definitions

* `DimTree.BasisFrame.IsAugBUGStep`: one step of the rank-adaptive TTN BUG integrator on concrete
  tree tensor networks.

## Main results

* `DimTree.BasisFrame.IsAugBUGStep.isAugTTNBUGStep`: concrete steps are abstract steps.
* `DimTree.BasisFrame.augBUG_global_error`: the robust global error bound on concrete tree tensor
  networks.

## TODO

The library has no truncation lemma for tree tensor networks yet: no rank truncation of a tree
tensor network is proved to satisfy the clause `‖Y₁ - YS t₁‖ ≤ ϑ` of `BasisFrame.IsAugBUGStep`.
-/

open Set
open scoped Matrix

universe u v

namespace LeanDLRA

namespace DimTree

variable {κ : Type u} [DecidableEq κ] [Fintype κ] {ι : κ → Type v} [∀ k, Fintype (ι k)]

namespace BasisFrame

/-- One step of the **rank-adaptive TTN BUG integrator** (Ceruti–Lubich–Sulz, SINUM 2023) on
concrete tree tensor networks with basis frame `f`, for the field `G` on the full tensor space,
doubly-normal bound `ε` and truncation tolerance `ϑ`, from `(t₀, Y₀)` to `(t₁, Y₁)`:

* at a **leaf** the exact flow of `G`;
* at an **inner node** the old bases `U i` and co-range bases `V i` have orthonormal columns and
  their projectors `P₀ i`, `Q₀ i` fix `Y₀`; there are new directions `Ũᵢ` with orthonormal columns
  and `U iᵀ Ũᵢ = 0` (projectors `Pa i`), so that `Ûᵢ = (U i, Ũᵢ)` is the augmented basis with
  projector `P₁ i = P₀ i + Pa i`; subtree results `K i` computed by the same integrator on the
  children for the `K`-step fields `Q₀ i G` from `Y₀`, captured by the augmented bases
  (`P₁ i (K i) = K i`) with doubly-normal component `(1 - P₁ i) (1 - Q₀ i) G(t, K i)` at most `ε`
  on `[t₀, t₁]`; the Galerkin step `YS' = (∏ P₁ i) G(t, YS)` in the augmented bases from
  `YS t₀ = Y₀`; and `‖Y₁ - YS t₁‖ ≤ ϑ`.

The last clause contains every truncation of the Galerkin result `YS t₁` with error at most `ϑ` in
the Frobenius norm: the predicate does not fix a truncation algorithm, and `Y₁ = YS t₁` (no
truncation) satisfies it for every `ϑ ≥ 0`. -/
def IsAugBUGStep : {τ : DimTree κ} → BasisFrame ι τ → (ℝ → Tensor ι → Tensor ι) → ℝ → ℝ → ℝ →
    ℝ → Tensor ι → Tensor ι → Prop
  | _, .leaf _, G, _, _, t₀, t₁, Y₀, Y₁ =>
      ∃ y : ℝ → Tensor ι, ODESolution G y t₀ t₁ ∧ y t₀ = Y₀ ∧ y t₁ = Y₁
  | _, .node (m := m) (cs := cs) _ _ U V fs, G, ε, ϑ, t₀, t₁, Y₀, Y₁ =>
      (∀ i, (U i)ᵀ * U i = 1) ∧ (∀ i, (V i)ᵀ * V i = 1) ∧
      (∀ i, (cs i).subtreeProj (U i) Y₀ = Y₀) ∧
      (∀ i, Tensor.actOn (· ∉ (cs i).modes) (V i * (V i)ᵀ) Y₀ = Y₀) ∧
      ∃ (ra : Fin m → ℕ) (Ua : ∀ i, Matrix (∀ k : {k // k ∈ (cs i).modes}, ι k) (Fin (ra i)) ℝ)
        (K : Fin m → Tensor ι) (YS : ℝ → Tensor ι),
        (∀ i, (Ua i)ᵀ * Ua i = 1) ∧ (∀ i, (U i)ᵀ * Ua i = 0) ∧
        (∀ i, IsAugBUGStep (fs i)
          (fun t x => Tensor.actOn (· ∉ (cs i).modes) (V i * (V i)ᵀ) (G t x)) ε ϑ t₀ t₁ Y₀
          (K i)) ∧
        (∀ i, ((cs i).subtreeProj (U i) + (cs i).subtreeProj (Ua i)) (K i) = K i) ∧
        (∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - ((cs i).subtreeProj (U i) + (cs i).subtreeProj (Ua i)))
          ((1 - Tensor.actOn (· ∉ (cs i).modes) (V i * (V i)ᵀ)) (G t (K i)))‖ ≤ ε) ∧
        ODESolution (fun t x => modeProd
          (fun i => (cs i).subtreeProj (U i) + (cs i).subtreeProj (Ua i)) (G t x)) YS t₀ t₁ ∧
        YS t₀ = Y₀ ∧ ‖Y₁ - YS t₁‖ ≤ ϑ

/-- **Concrete rank-adaptive TTN BUG steps are abstract steps.** On a valid dimension tree, every
concrete rank-adaptive TTN BUG step with basis frame `f` is an `IsAugTTNBUGStep` with the abstract
frame `f.toTTNFrame`: the projectors `P₁ i = P₀ i + Pa i` of the augmented bases are orthogonal,
act on the modes of the subtree `i`, commute and contain the old ones (`P₁ i P₀ i = P₀ i`); this
is derived from the orthonormality of the bases and the disjointness of the subtrees of a valid
tree. -/
theorem IsAugBUGStep.isAugTTNBUGStep : ∀ {τ : DimTree κ} (f : BasisFrame ι τ)
    {G : ℝ → Tensor ι → Tensor ι} {ε ϑ t₀ t₁ : ℝ} {Y₀ Y₁ : Tensor ι}, τ.IsValid →
    f.IsAugBUGStep G ε ϑ t₀ t₁ Y₀ Y₁ → IsAugTTNBUGStep f.toTTNFrame G ε ϑ t₀ t₁ Y₀ Y₁ := by
  intro τ f
  induction f with
  | leaf k => intro G ε ϑ t₀ t₁ Y₀ Y₁ _ h; exact h
  | node r s U V fs ih =>
    rename_i m cs
    intro G ε ϑ t₀ t₁ Y₀ Y₁ hv h
    obtain ⟨hU, hV, hP, hQ, _, Ua, K, YS, hUa, horth, hch, hcap, hn, hS, hS₀, hS₁⟩ := h
    have horth' : ∀ i, (Ua i)ᵀ * U i = 0 := fun i => by
      rw [← Matrix.transpose_transpose (U i), ← Matrix.transpose_mul, horth i,
        Matrix.transpose_zero]
    have hP₀ : ∀ i, IsOrthProj ((cs i).subtreeProj (U i)) := fun i =>
      isOrthProj_subtreeProj _ (hU i)
    have hsum : ∀ i, (cs i).subtreeProj (U i) + (cs i).subtreeProj (Ua i) =
        Tensor.actOn (· ∈ (cs i).modes) (U i * (U i)ᵀ + Ua i * (Ua i)ᵀ) := fun i =>
      (Tensor.actOn_add _ _ _).symm
    have hcomm : ∀ i j x, ((cs i).subtreeProj (U i) + (cs i).subtreeProj (Ua i))
        (((cs j).subtreeProj (U j) + (cs j).subtreeProj (Ua j)) x) =
        ((cs j).subtreeProj (U j) + (cs j).subtreeProj (Ua j))
          (((cs i).subtreeProj (U i) + (cs i).subtreeProj (Ua i)) x) := fun i j x => by
      by_cases hij : i = j
      · subst hij; rfl
      · rw [hsum i, hsum j]
        exact Tensor.actOn_comm_of_disjoint _
          (fun _ hk hk' => Finset.disjoint_left.1 (hv.disjoint hij) hk hk') _ _ x
    have hold : ∀ i x, ((cs i).subtreeProj (U i) + (cs i).subtreeProj (Ua i))
        ((cs i).subtreeProj (U i) x) = (cs i).subtreeProj (U i) x := fun i x => by
      rw [add_apply, (hP₀ i).idem,
        subtreeProj_subtreeProj_of_orth _ (horth' i), add_zero]
    exact ⟨hP₀, fun i => isOrthProj_coRangeProj _ (hV i), hP, hQ,
      fun i => (cs i).subtreeProj (U i) + (cs i).subtreeProj (Ua i), K, YS,
      fun i => (hP₀ i).add_of_orth (isOrthProj_subtreeProj _ (hUa i)) fun x =>
        subtreeProj_subtreeProj_of_orth _ (horth i) x,
      fun i => ⟨U i * (U i)ᵀ + Ua i * (Ua i)ᵀ, (hsum i).symm⟩, hcomm, hold,
      fun i => ih i (hv.child i) (hch i), hcap, hn, hS, hS₀, hS₁⟩

/-- **Robust global error of the rank-adaptive TTN BUG integrator on concrete tree tensor
networks.** Let `τ` be a valid dimension tree with `s` nodes and height `ℓ`, `F` a field on the
tensor space that is `L`-Lipschitz, bounded by `B` and continuous in time, `tₙ = t₀ + n h` with
`2 L h ℓ ≤ 1`, and `A` the exact solution on `[t₀, t_N]`. If every step `n < N` is a concrete
rank-adaptive TTN BUG step with some basis frame of `τ`, doubly-normal bound `ε ≥ 0` and
truncation tolerance `ϑ ≥ 0` at every node, then for `n ≤ N` with `n h ≤ T`

    ‖Yₙ - A(tₙ)‖ ≤ e^{L T} (δ + 3 s T (ε + 6 L B h) + 3 s n ϑ),

independently of the singular values of the matricizations of the connecting tensors. This is
`augTTN_global_error_le` for the abstract frames `(f n).toTTNFrame`. -/
theorem augBUG_global_error {τ : DimTree κ} (hv : τ.IsValid) {F : ℝ → Tensor ι → Tensor ι}
    {L B ε ϑ : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) (hε : 0 ≤ ε) (hϑ : 0 ≤ ϑ)
    {t₀ h : ℝ} (hh : 0 ≤ h) (hLh : 2 * L * h * τ.treeHeight ≤ 1) {N : ℕ}
    {A : ℝ → Tensor ι} (hA : ODESolution F A t₀ (t₀ + N * h)) {f : ℕ → BasisFrame ι τ}
    {Y : ℕ → Tensor ι}
    (hstep : ∀ n < N, (f n).IsAugBUGStep F ε ϑ (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (Y (n + 1)))
    {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) *
        (δ + T * (3 * τ.nodeCount * (ε + 6 * L * B * h)) + 3 * τ.nodeCount * (n * ϑ)) :=
  augTTN_global_error_le hF hL hB hcont hε hϑ hh hA (fr := fun n => (f n).toTTNFrame)
    (fun n _ => (toTTNFrame_size (f n)).le) (fun n _ => (toTTNFrame_height (f n)).le) hLh
    (fun n hn => (hstep n hn).isAugTTNBUGStep (f n) hv) hδ

end BasisFrame

/-! ### Non-vacuity -/

/-- Non-vacuity of `BasisFrame.IsAugBUGStep` at an inner node: on the tree with two leaves (modes
`0` and `1` of dimension one), the zero field with the zero tensor, rank-zero bases and no new
directions is a rank-adaptive TTN BUG step on every time interval. -/
private theorem isAugBUGStep_zero_aux (t₀ t₁ : ℝ) :
    (BasisFrame.node (ι := fun _ : Fin 2 => Fin 1) (cs := fun i : Fin 2 => leaf i)
      (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
      (fun i => BasisFrame.leaf i)).IsAugBUGStep (fun _ _ => 0) 0 0 t₀ t₁ 0 0 := by
  have hz : ODESolution (fun _ _ => (0 : Tensor (fun _ : Fin 2 => Fin 1))) (fun _ => 0) t₀ t₁ :=
    ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) _⟩
  refine ⟨fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _, fun _ => map_zero _,
    fun _ => map_zero _, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
    fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _, fun i => ?_,
    fun _ => map_zero _, fun _ t _ => by simp, by simpa using hz, rfl, by simp⟩
  refine ⟨fun _ => 0, ?_, rfl, rfl⟩
  convert hz using 1
  funext t x
  simp

/-- The dimension tree with two leaves `0` and `1` is valid, so the step of the non-vacuity
example is an abstract rank-adaptive TTN BUG step. -/
example := (isAugBUGStep_zero_aux 0 1).isAugTTNBUGStep _
  (show (node fun i : Fin 2 => leaf i).IsValid from
    ⟨fun _ => trivial, fun _ _ hij => Finset.disjoint_singleton.2 hij⟩)

/-- The hypotheses of `BasisFrame.augBUG_global_error` are satisfiable: `N` steps of size `1` of
the non-vacuity example, with the zero field (`L = B = ε = ϑ = 0`) and the zero solution. -/
example (N : ℕ) := BasisFrame.augBUG_global_error
  (show (node fun i : Fin 2 => leaf i).IsValid from
    ⟨fun _ => trivial, fun _ _ hij => Finset.disjoint_singleton.2 hij⟩)
  (F := fun _ _ => (0 : Tensor (fun _ : Fin 2 => Fin 1))) (L := 0) (B := 0) (ε := 0) (ϑ := 0)
  (fun _ _ _ => by simp) le_rfl (fun _ _ => by simp) (fun _ => continuous_const) le_rfl le_rfl
  (t₀ := 0) (h := 1) zero_le_one (by simp) (N := N) (A := fun _ => 0)
  ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) _⟩
  (Y := fun _ => 0) (fun _ _ => isAugBUGStep_zero_aux _ _) (δ := 0) (T := N) (by simp)

end DimTree

end LeanDLRA
