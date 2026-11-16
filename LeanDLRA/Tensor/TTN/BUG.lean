import LeanDLRA.Tensor.TTN.ParallelBUG
import LeanDLRA.Tensor.TTN.Abstract.BUG

/-!
# The fixed-rank BUG integrator on concrete tree tensor networks

The fixed-rank tree tensor network (TTN) BUG integrator of the library is stated over an abstract
`TTNFrame` (`IsTTNBUGStep`: the rank-adaptive TTN integrator of Ceruti–Lubich–Sulz, SINUM 2023,
without augmentation and truncation), and its error bound is proved at that level
(`ttn_global_error_le`). This file states the step on actual tree tensor network data, over a
basis frame `f : DimTree.BasisFrame ι τ` of a dimension tree `τ`:

* a **concrete TTN BUG step** (`BasisFrame.IsBUGStep`) uses at every inner node new subtree bases
  `U¹ᵢ` with orthonormal columns and as many columns as the old bases `U⁰ᵢ`, and is an abstract
  `IsTTNBUGStep` with the frame `f.toTTNFrame` on a valid tree: the orthogonality of all
  projectors and the commutation of the new projectors are derived from the orthonormality of the
  matrices and the disjointness of the subtrees, and the new projector of child `i` acts on the
  modes of `τᵢ`.

The robust global error bound of the fixed-rank TTN BUG integrator therefore holds for concrete
tree tensor networks (`BasisFrame.bug_global_error`), with constants depending only on `L`, `B`,
`T` and the number of nodes of the tree.

## Main definitions

* `DimTree.BasisFrame.IsBUGStep`: one step of the fixed-rank TTN BUG integrator on concrete tree
  tensor networks.

## Main results

* `DimTree.BasisFrame.IsBUGStep.isTTNBUGStep`: concrete steps are abstract steps.
* `DimTree.BasisFrame.bug_global_error`: the robust global error bound on concrete tree tensor
  networks.

## TODO

The library has no truncation lemma for tree tensor networks yet.
-/

open Set
open scoped Matrix

universe u v

namespace LeanDLRA

namespace DimTree

variable {κ : Type u} [DecidableEq κ] [Fintype κ] {ι : κ → Type v} [∀ k, Fintype (ι k)]

namespace BasisFrame

/-- One step of the **fixed-rank TTN BUG integrator** (the rank-adaptive TTN integrator of
Ceruti–Lubich–Sulz, SINUM 2023, without augmentation and truncation) on concrete tree tensor
networks with basis frame `f`, for the field `G` on the full tensor space and doubly-normal bound
`ε`, from `(t₀, Y₀)` to `(t₁, Y₁)`:

* at a **leaf** the exact flow of `G`;
* at an **inner node** the old bases `U i` and co-range bases `V i` have orthonormal columns and
  their projectors `P₀ i`, `Q₀ i` fix `Y₀`; there are new bases `U¹ᵢ` with orthonormal columns and
  the rank `r i` of the old bases (projectors `P₁ i`), subtree results `K i` computed by the same
  integrator on the children for the `K`-step fields `Q₀ i G` from `Y₀`, captured by the new
  bases (`P₁ i (K i) = K i`) with doubly-normal component `(1 - P₁ i) (1 - Q₀ i) G(t, K i)` at
  most `ε` on `[t₀, t₁]`; and `Y₁` is the value at `t₁` of the Galerkin step
  `YS' = (∏ P₁ i) G(t, YS)` in the new bases from `YS t₀ = (∏ P₁ i) Y₀`. -/
def IsBUGStep : {τ : DimTree κ} → BasisFrame ι τ → (ℝ → Tensor ι → Tensor ι) → ℝ → ℝ → ℝ →
    Tensor ι → Tensor ι → Prop
  | _, .leaf _, G, _, t₀, t₁, Y₀, Y₁ =>
      ∃ y : ℝ → Tensor ι, ODESolution G y t₀ t₁ ∧ y t₀ = Y₀ ∧ y t₁ = Y₁
  | _, .node (m := m) (cs := cs) r _ U V fs, G, ε, t₀, t₁, Y₀, Y₁ =>
      (∀ i, (U i)ᵀ * U i = 1) ∧ (∀ i, (V i)ᵀ * V i = 1) ∧
      (∀ i, (cs i).subtreeProj (U i) Y₀ = Y₀) ∧
      (∀ i, Tensor.actOn (· ∉ (cs i).modes) (V i * (V i)ᵀ) Y₀ = Y₀) ∧
      ∃ (U₁ : ∀ i, Matrix (∀ k : {k // k ∈ (cs i).modes}, ι k) (Fin (r i)) ℝ)
        (K : Fin m → Tensor ι) (YS : ℝ → Tensor ι),
        (∀ i, (U₁ i)ᵀ * U₁ i = 1) ∧
        (∀ i, IsBUGStep (fs i)
          (fun t x => Tensor.actOn (· ∉ (cs i).modes) (V i * (V i)ᵀ) (G t x)) ε t₀ t₁ Y₀
          (K i)) ∧
        (∀ i, (cs i).subtreeProj (U₁ i) (K i) = K i) ∧
        (∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - (cs i).subtreeProj (U₁ i))
          ((1 - Tensor.actOn (· ∉ (cs i).modes) (V i * (V i)ᵀ)) (G t (K i)))‖ ≤ ε) ∧
        ODESolution (fun t x => modeProd (fun i => (cs i).subtreeProj (U₁ i)) (G t x)) YS t₀ t₁ ∧
        YS t₀ = modeProd (fun i => (cs i).subtreeProj (U₁ i)) Y₀ ∧ YS t₁ = Y₁

/-- **Concrete TTN BUG steps are abstract steps.** On a valid dimension tree, every concrete TTN
BUG step with basis frame `f` is an `IsTTNBUGStep` with the abstract frame `f.toTTNFrame`: the
orthogonality of all projectors and the commutation of the new projectors `P₁ i` are derived from
the orthonormality of the bases and the disjointness of the subtrees of a valid tree, and `P₁ i`
acts on the modes of the subtree `i`. -/
theorem IsBUGStep.isTTNBUGStep : ∀ {τ : DimTree κ} (f : BasisFrame ι τ)
    {G : ℝ → Tensor ι → Tensor ι} {ε t₀ t₁ : ℝ} {Y₀ Y₁ : Tensor ι}, τ.IsValid →
    f.IsBUGStep G ε t₀ t₁ Y₀ Y₁ → IsTTNBUGStep f.toTTNFrame G ε t₀ t₁ Y₀ Y₁ := by
  intro τ f
  induction f with
  | leaf k => intro G ε t₀ t₁ Y₀ Y₁ _ h; exact h
  | node r s U V fs ih =>
    rename_i m cs
    intro G ε t₀ t₁ Y₀ Y₁ hv h
    obtain ⟨hU, hV, hP, hQ, U₁, K, YS, hU₁, hch, hcap, hn, hS, hS₀, hS₁⟩ := h
    exact ⟨fun i => isOrthProj_subtreeProj _ (hU i), fun i => isOrthProj_coRangeProj _ (hV i),
      hP, hQ, fun i => (cs i).subtreeProj (U₁ i), K, YS,
      fun i => isOrthProj_subtreeProj _ (hU₁ i), fun i => ⟨U₁ i * (U₁ i)ᵀ, rfl⟩,
      hv.subtreeProj_comm U₁, fun i => ih i (hv.child i) (hch i), hcap, hn, hS, hS₀, hS₁⟩

/-- **Robust global error of the fixed-rank TTN BUG integrator on concrete tree tensor networks.**
Let `τ` be a valid dimension tree with `s` nodes and height `ℓ`, `F` a field on the tensor space
that is `L`-Lipschitz, bounded by `B` and continuous in time, `tₙ = t₀ + n h` with
`2 L h ℓ ≤ 1`, and `A` the exact solution on `[t₀, t_N]`. If every step `n < N` is a concrete TTN
BUG step with some basis frame of `τ` and doubly-normal bound `ε ≥ 0` at every node, then for
`n ≤ N` with `n h ≤ T`

    ‖Yₙ - A(tₙ)‖ ≤ e^{L T} (δ + 3 s T (ε + 6 L B h)),

independently of the singular values of the matricizations of the connecting tensors. This is
`ttn_global_error_le` for the abstract frames `(f n).toTTNFrame`. -/
theorem bug_global_error {τ : DimTree κ} (hv : τ.IsValid) {F : ℝ → Tensor ι → Tensor ι}
    {L B ε : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) (hε : 0 ≤ ε)
    {t₀ h : ℝ} (hh : 0 ≤ h) (hLh : 2 * L * h * τ.treeHeight ≤ 1) {N : ℕ}
    {A : ℝ → Tensor ι} (hA : ODESolution F A t₀ (t₀ + N * h)) {f : ℕ → BasisFrame ι τ}
    {Y : ℕ → Tensor ι}
    (hstep : ∀ n < N, (f n).IsBUGStep F ε (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (Y (n + 1)))
    {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * (δ + T * (3 * τ.nodeCount * (ε + 6 * L * B * h))) :=
  ttn_global_error_le hF hL hB hcont hε hh hA (fr := fun n => (f n).toTTNFrame)
    (fun n _ => (toTTNFrame_size (f n)).le) (fun n _ => (toTTNFrame_height (f n)).le) hLh
    (fun n hn => (hstep n hn).isTTNBUGStep (f n) hv) hδ

end BasisFrame

/-! ### Non-vacuity -/

/-- Non-vacuity of `BasisFrame.IsBUGStep` at an inner node: on the tree with two leaves (modes `0`
and `1` of dimension one), the zero field with the zero tensor and rank-zero bases is a TTN BUG
step on every time interval. -/
private theorem isBUGStep_zero_aux (t₀ t₁ : ℝ) :
    (BasisFrame.node (ι := fun _ : Fin 2 => Fin 1) (cs := fun i : Fin 2 => leaf i)
      (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun i => BasisFrame.leaf i)).IsBUGStep
      (fun _ _ => 0) 0 t₀ t₁ 0 0 := by
  have hz : ODESolution (fun _ _ => (0 : Tensor (fun _ : Fin 2 => Fin 1))) (fun _ => 0) t₀ t₁ :=
    ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) _⟩
  refine ⟨fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _, fun _ => map_zero _,
    fun _ => map_zero _, fun _ => 0, fun _ => 0, fun _ => 0,
    fun _ => Subsingleton.elim _ _, fun i => ?_,
    fun _ => map_zero _, fun _ t _ => by simp, by simpa using hz, (map_zero _).symm, rfl⟩
  refine ⟨fun _ => 0, ?_, rfl, rfl⟩
  convert hz using 1
  funext t x
  simp

/-- The dimension tree with two leaves `0` and `1` is valid, so the step of the non-vacuity
example is an abstract TTN BUG step. -/
example := (isBUGStep_zero_aux 0 1).isTTNBUGStep _
  (show (node fun i : Fin 2 => leaf i).IsValid from
    ⟨fun _ => trivial, fun _ _ hij => Finset.disjoint_singleton.2 hij⟩)

/-- The hypotheses of `BasisFrame.bug_global_error` are satisfiable: `N` steps of size `1` of the
non-vacuity example, with the zero field (`L = B = ε = 0`) and the zero solution. -/
example (N : ℕ) := BasisFrame.bug_global_error
  (show (node fun i : Fin 2 => leaf i).IsValid from
    ⟨fun _ => trivial, fun _ _ hij => Finset.disjoint_singleton.2 hij⟩)
  (F := fun _ _ => (0 : Tensor (fun _ : Fin 2 => Fin 1))) (L := 0) (B := 0) (ε := 0)
  (fun _ _ _ => by simp) le_rfl (fun _ _ => by simp) (fun _ => continuous_const) le_rfl
  (t₀ := 0) (h := 1) zero_le_one (by simp) (N := N) (A := fun _ => 0)
  ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) _⟩
  (Y := fun _ => 0) (fun _ _ => isBUGStep_zero_aux _ _) (δ := 0) (T := N) (by simp)

end DimTree

end LeanDLRA
