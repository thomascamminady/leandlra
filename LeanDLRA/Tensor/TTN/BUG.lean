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

/-! ### Non-vacuity: a step on two modes of size two -/

namespace BUGExample

open Tensor

/-- The elementary tensor `a ⊗ b` on two modes of size two. -/
noncomputable def elem (a b : Fin 2 → ℝ) : Tensor (fun _ : Fin 2 => Fin 2) :=
  WithLp.toLp 2 fun x => a (x 0) * b (x 1)

/-- Two tensors on two modes of size two agree if they agree at every pair of indices. -/
theorem tensor_ext {X Y : Tensor (fun _ : Fin 2 => Fin 2)}
    (h : ∀ i j : Fin 2, X ![i, j] = Y ![i, j]) : X = Y := by
  ext x
  have hx : x = ![x 0, x 1] := by
    funext k
    fin_cases k <;> rfl
  rw [hx]
  exact h _ _

/-- Sums over the multi-indices of a set of modes consisting of mode `j` alone. -/
private theorem sum_pi_unique {p : Fin 2 → Prop} [Fintype {k // p k}] {j : Fin 2} (hj : p j)
    (hp : ∀ k, p k → k = j) (F : Fin 2 → ℝ) :
    ∑ w : {k // p k} → Fin 2, F (w ⟨j, hj⟩) = ∑ c, F c :=
  Fintype.sum_equiv
    { toFun := fun w => w ⟨j, hj⟩
      invFun := fun c _ => c
      left_inv := fun w => funext fun ⟨k, hk⟩ => by obtain rfl := hp k hk; rfl
      right_inv := fun _ => rfl } _ _ fun _ => rfl

/-- The Gram matrix of two basis columns on the set of modes `{j}`. -/
private theorem transpose_mul_of_apply {p : Fin 2 → Prop} [Fintype {k // p k}] {j : Fin 2}
    (hj : p j) (hp : ∀ k, p k → k = j) {u v : Fin 2 → ℝ}
    {U V : Matrix ({k // p k} → Fin 2) (Fin 1) ℝ} (hU : ∀ y b, U y b = u (y ⟨j, hj⟩))
    (hV : ∀ y b, V y b = v (y ⟨j, hj⟩)) : Uᵀ * V = (∑ c, u c * v c) • 1 := by
  ext a b
  rw [Matrix.mul_apply, Subsingleton.elim a 0, Subsingleton.elim b 0]
  simp only [Matrix.transpose_apply, hU, hV, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one]
  exact sum_pi_unique hj hp fun c => u c * v c

/-- A basis column on the set of modes `{0}` acting on `a ⊗ b`. -/
private theorem actOn_elem_zero {p : Fin 2 → Prop} [DecidablePred p] (hj : p 0)
    (hp : ∀ k, p k → k = 0) {u : Fin 2 → ℝ} {U : Matrix ({k // p k} → Fin 2) (Fin 1) ℝ}
    (hU : ∀ y b, U y b = u (y ⟨0, hj⟩)) (a b : Fin 2 → ℝ) :
    actOn p (U * Uᵀ) (elem a b) = (∑ c, u c * a c) • elem u b := by
  have h1 : ¬ p 1 := fun h => absurd (hp 1 h) (by decide)
  ext x
  rw [actOn_mul_transpose_apply]
  simp only [Fin.sum_univ_one, hU, elem, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul,
    Subtype.restrict_apply, override_apply_of p hj, override_apply_of_not p h1]
  have key : ∑ w : {k // p k} → Fin 2, u (w ⟨0, hj⟩) * (a (w ⟨0, hj⟩) * b (x 1)) =
      ∑ c, u c * (a c * b (x 1)) := sum_pi_unique hj hp fun c => u c * (a c * b (x 1))
  rw [key]
  simp only [Fin.sum_univ_two]
  ring

/-- A basis column on the set of modes `{1}` acting on `a ⊗ b`. -/
private theorem actOn_elem_one {p : Fin 2 → Prop} [DecidablePred p] (hj : p 1)
    (hp : ∀ k, p k → k = 1) {u : Fin 2 → ℝ} {U : Matrix ({k // p k} → Fin 2) (Fin 1) ℝ}
    (hU : ∀ y b, U y b = u (y ⟨1, hj⟩)) (a b : Fin 2 → ℝ) :
    actOn p (U * Uᵀ) (elem a b) = (∑ c, u c * b c) • elem a u := by
  have h0 : ¬ p 0 := fun h => absurd (hp 0 h) (by decide)
  ext x
  rw [actOn_mul_transpose_apply]
  simp only [Fin.sum_univ_one, hU, elem, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul,
    Subtype.restrict_apply, override_apply_of p hj, override_apply_of_not p h0]
  have key : ∑ w : {k // p k} → Fin 2, u (w ⟨1, hj⟩) * (a (x 0) * b (w ⟨1, hj⟩)) =
      ∑ c, u c * (a (x 0) * b c) := sum_pi_unique hj hp fun c => u c * (a (x 0) * b c)
  rw [key]
  simp only [Fin.sum_univ_two]
  ring

/-- The leaf `i` does not contain the other mode `1 - i`. -/
theorem one_sub_notMem_leaf (i : Fin 2) : 1 - i ∉ (leaf i : DimTree (Fin 2)).modes := by
  fin_cases i <;> simp [DimTree.modes]

/-- The basis column of the vector `u` on the leaf `i`. -/
def leafCol (i : Fin 2) (u : Fin 2 → ℝ) :
    Matrix ({k // k ∈ (leaf i : DimTree (Fin 2)).modes} → Fin 2) (Fin 1) ℝ :=
  fun y _ => u (y ⟨i, Finset.mem_singleton_self i⟩)

/-- The co-range column of the vector `u` on the mode `1 - i` outside the leaf `i`. -/
def coCol (i : Fin 2) (u : Fin 2 → ℝ) :
    Matrix ({k // k ∉ (leaf i : DimTree (Fin 2)).modes} → Fin 2) (Fin 1) ℝ :=
  fun y _ => u (y ⟨1 - i, one_sub_notMem_leaf i⟩)

private theorem mem_leaf_eq {i k : Fin 2} (hk : k ∈ (leaf i : DimTree (Fin 2)).modes) : k = i :=
  Finset.mem_singleton.1 hk

private theorem notMem_leaf_eq {i k : Fin 2} (hk : k ∉ (leaf i : DimTree (Fin 2)).modes) :
    k = 1 - i := by
  fin_cases i <;> fin_cases k <;> simp_all [DimTree.modes]

/-- `(leafCol i u)ᵀ (leafCol i v) = ⟨u, v⟩ • 1`. -/
theorem leafCol_transpose_mul (i : Fin 2) (u v : Fin 2 → ℝ) :
    (leafCol i u)ᵀ * leafCol i v = (∑ c, u c * v c) • 1 :=
  transpose_mul_of_apply (j := i) (Finset.mem_singleton_self i) (fun _ hk => mem_leaf_eq hk)
    (u := u) (v := v) (fun _ _ => rfl) (fun _ _ => rfl)

/-- `(coCol i u)ᵀ (coCol i v) = ⟨u, v⟩ • 1`. -/
theorem coCol_transpose_mul (i : Fin 2) (u v : Fin 2 → ℝ) :
    (coCol i u)ᵀ * coCol i v = (∑ c, u c * v c) • 1 :=
  transpose_mul_of_apply (j := 1 - i) (one_sub_notMem_leaf i) (fun _ hk => notMem_leaf_eq hk)
    (u := u) (v := v) (fun _ _ => rfl) (fun _ _ => rfl)

/-- The subtree projector of the leaf `0` with basis `u` maps `a ⊗ b` to `⟨u, a⟩ u ⊗ b`. -/
theorem subtreeProj_leafCol_zero (u a b : Fin 2 → ℝ) :
    (leaf (0 : Fin 2)).subtreeProj (leafCol 0 u) (elem a b) = (∑ c, u c * a c) • elem u b :=
  actOn_elem_zero (Finset.mem_singleton_self 0) (fun _ hk => mem_leaf_eq hk) (u := u)
    (fun _ _ => rfl) a b

/-- The subtree projector of the leaf `1` with basis `u` maps `a ⊗ b` to `⟨u, b⟩ a ⊗ u`. -/
theorem subtreeProj_leafCol_one (u a b : Fin 2 → ℝ) :
    (leaf (1 : Fin 2)).subtreeProj (leafCol 1 u) (elem a b) = (∑ c, u c * b c) • elem a u :=
  actOn_elem_one (Finset.mem_singleton_self 1) (fun _ hk => mem_leaf_eq hk) (u := u)
    (fun _ _ => rfl) a b

/-- The co-range projector of the leaf `0` acts on mode `1`. -/
theorem actOn_coCol_zero (v a b : Fin 2 → ℝ) :
    actOn (· ∉ (leaf (0 : Fin 2)).modes) (coCol 0 v * (coCol 0 v)ᵀ) (elem a b) =
      (∑ c, v c * b c) • elem a v :=
  actOn_elem_one (one_sub_notMem_leaf 0) (fun _ hk => notMem_leaf_eq hk) (u := v)
    (fun _ _ => rfl) a b

/-- The co-range projector of the leaf `1` acts on mode `0`. -/
theorem actOn_coCol_one (v a b : Fin 2 → ℝ) :
    actOn (· ∉ (leaf (1 : Fin 2)).modes) (coCol 1 v * (coCol 1 v)ᵀ) (elem a b) =
      (∑ c, v c * a c) • elem v b :=
  actOn_elem_zero (one_sub_notMem_leaf 1) (fun _ hk => notMem_leaf_eq hk) (u := v)
    (fun _ _ => rfl) a b

/-- The basis frame of the start value `e₀ ⊗ e₀` on the tree with the two leaves `0`, `1`: the
bases `e₀` on both leaves and the co-range bases `e₀` on the other mode (`e₀ = (1, 0)`). -/
noncomputable def frame : BasisFrame (fun _ : Fin 2 => Fin 2) (node fun i : Fin 2 => leaf i) :=
  BasisFrame.node (fun _ => 1) (fun _ => 1) (fun i => leafCol i ![1, 0])
    (fun i => coCol i ![1, 0]) fun i => BasisFrame.leaf i

/-- The tree with the two leaves `0` and `1` is valid. -/
theorem isValid_node : (node fun i : Fin 2 => leaf i).IsValid :=
  ⟨fun _ => trivial, fun _ _ hij => Finset.disjoint_singleton.2 hij⟩

/-- The field `g = (2, 4) ⊗ e₀ + e₁ ⊗ e₁` of the example (`e₁ = (0, 1)`); its part `e₁ ⊗ e₁` is
doubly normal to both leaves. -/
noncomputable def field : Tensor (fun _ : Fin 2 => Fin 2) :=
  elem ![2, 4] ![1, 0] + elem ![0, 1] ![0, 1]

/-- `e₀ ⊗ e₀ + (2, 4) ⊗ e₀ = 5 (u ⊗ e₀)` with `u = (3/5, 4/5)`. -/
theorem elem_add_elem :
    elem ![1, 0] ![1, 0] + (1 : ℝ) • elem ![2, 4] ![1, 0] =
      (5 : ℝ) • elem ![3 / 5, 4 / 5] ![1, 0] :=
  tensor_ext fun i j => by fin_cases i <;> fin_cases j <;> norm_num [elem]


/-- The co-range projector of the leaf `0` maps the field `g` to `(2, 4) ⊗ e₀`. -/
theorem actOn_coCol_zero_field :
    actOn (· ∉ (leaf (0 : Fin 2)).modes) (coCol 0 ![1, 0] * (coCol 0 ![1, 0])ᵀ) field =
      elem ![2, 4] ![1, 0] := by
  rw [field, map_add, actOn_coCol_zero, actOn_coCol_zero]
  norm_num [Fin.sum_univ_two]

/-- The co-range projector of the leaf `1` maps the field `g` to `2 e₀ ⊗ e₀`. -/
theorem actOn_coCol_one_field :
    actOn (· ∉ (leaf (1 : Fin 2)).modes) (coCol 1 ![1, 0] * (coCol 1 ![1, 0])ᵀ) field =
      (2 : ℝ) • elem ![1, 0] ![1, 0] := by
  rw [field, map_add, actOn_coCol_one, actOn_coCol_one]
  norm_num [Fin.sum_univ_two]

private theorem p0g : (leaf (0 : Fin 2)).subtreeProj (leafCol 0 ![3 / 5, 4 / 5])
    (elem ![2, 4] ![1, 0]) = (22 / 5 : ℝ) • elem ![3 / 5, 4 / 5] ![1, 0] := by
  rw [subtreeProj_leafCol_zero]
  norm_num [Fin.sum_univ_two]

private theorem p0u : (leaf (0 : Fin 2)).subtreeProj (leafCol 0 ![3 / 5, 4 / 5])
    (elem ![3 / 5, 4 / 5] ![1, 0]) = elem ![3 / 5, 4 / 5] ![1, 0] := by
  rw [subtreeProj_leafCol_zero]
  norm_num [Fin.sum_univ_two]

private theorem p0e : (leaf (0 : Fin 2)).subtreeProj (leafCol 0 ![3 / 5, 4 / 5])
    (elem ![1, 0] ![1, 0]) = (3 / 5 : ℝ) • elem ![3 / 5, 4 / 5] ![1, 0] := by
  rw [subtreeProj_leafCol_zero]
  norm_num [Fin.sum_univ_two]

private theorem p1c : (leaf (1 : Fin 2)).subtreeProj (leafCol 1 ![1, 0]) (elem ![2, 4] ![1, 0]) =
    elem ![2, 4] ![1, 0] := by
  rw [subtreeProj_leafCol_one]
  norm_num [Fin.sum_univ_two]

private theorem p1e : (leaf (1 : Fin 2)).subtreeProj (leafCol 1 ![1, 0]) (elem ![1, 0] ![1, 0]) =
    elem ![1, 0] ![1, 0] := by
  rw [subtreeProj_leafCol_one]
  norm_num [Fin.sum_univ_two]

private theorem p1n : (leaf (1 : Fin 2)).subtreeProj (leafCol 1 ![1, 0]) (elem ![0, 1] ![0, 1]) =
    0 := by
  rw [subtreeProj_leafCol_one]
  norm_num [Fin.sum_univ_two]

private theorem hU₁0 : (leafCol 0 ![3 / 5, 4 / 5])ᵀ * leafCol 0 ![3 / 5, 4 / 5] = 1 := by
  rw [leafCol_transpose_mul]
  norm_num [Fin.sum_univ_two]

/-- The doubly normal part at the leaf `0` before the new projector: `e₁ ⊗ e₁`. -/
private theorem coNormal_zero :
    (1 - actOn (ι := fun _ : Fin 2 => Fin 2) (· ∉ (leaf (0 : Fin 2)).modes)
      (coCol 0 ![1, 0] * (coCol 0 ![1, 0])ᵀ)) field = elem ![0, 1] ![0, 1] := by
  rw [_root_.sub_apply, one_apply_eq_self, actOn_coCol_zero_field, field, add_sub_cancel_left]

/-- The doubly normal part at the leaf `1` is `e₁ ⊗ e₁`. -/
private theorem normal_one :
    (1 - (leaf (1 : Fin 2)).subtreeProj (ι := fun _ : Fin 2 => Fin 2) (leafCol 1 ![1, 0]))
      ((1 - actOn (ι := fun _ : Fin 2 => Fin 2) (· ∉ (leaf (1 : Fin 2)).modes)
        (coCol 1 ![1, 0] * (coCol 1 ![1, 0])ᵀ)) field) = elem ![0, 1] ![0, 1] := by
  rw [_root_.sub_apply, one_apply_eq_self, _root_.sub_apply, one_apply_eq_self,
    actOn_coCol_one_field, field, map_sub, map_add, map_smul, p1c, p1n, p1e]
  abel

/-- **Non-vacuity of `BasisFrame.IsBUGStep` at an inner node with rank one.** On the tree with
the two leaves `0`, `1` and modes of size two, the step of size `1` from `e₀ ⊗ e₀` with the
bases `frame` and the constant field `g = (2, 4) ⊗ e₀ + e₁ ⊗ e₁`: the K-steps end at
`5 (u ⊗ e₀)` and `3 (e₀ ⊗ e₀)`, the new bases are `u = (3/5, 4/5)` and `e₀`, the doubly normal
parts are at most `‖e₁ ⊗ e₁‖`, and the Galerkin step moves from `(3/5) u ⊗ e₀` along
`(22/5) u ⊗ e₀` to `5 (u ⊗ e₀)`. -/
theorem isBUGStep_frame :
    frame.IsBUGStep (fun _ _ => field) ‖elem ![0, 1] ![0, 1]‖ 0 1 (elem ![1, 0] ![1, 0])
      ((3 / 5 : ℝ) • elem ![3 / 5, 4 / 5] ![1, 0] +
        (1 : ℝ) • ((22 / 5 : ℝ) • elem ![3 / 5, 4 / 5] ![1, 0])) := by
  -- the K-steps
  have hK0 : ∃ y : ℝ → Tensor (fun _ : Fin 2 => Fin 2),
      ODESolution (fun _ _ => actOn (· ∉ (leaf (0 : Fin 2)).modes)
        (coCol 0 ![1, 0] * (coCol 0 ![1, 0])ᵀ) field) y 0 1 ∧
      y 0 = elem ![1, 0] ![1, 0] ∧ y 1 = (5 : ℝ) • elem ![3 / 5, 4 / 5] ![1, 0] :=
    ⟨_, Exactness.odeSolution_add_smul_of_const (fun _ _ => actOn_coCol_zero_field)
      (elem ![1, 0] ![1, 0]) 0 1, by simp, elem_add_elem⟩
  have hK1 : ∃ y : ℝ → Tensor (fun _ : Fin 2 => Fin 2),
      ODESolution (fun _ _ => actOn (· ∉ (leaf (1 : Fin 2)).modes)
        (coCol 1 ![1, 0] * (coCol 1 ![1, 0])ᵀ) field) y 0 1 ∧
      y 0 = elem ![1, 0] ![1, 0] ∧ y 1 = (3 : ℝ) • elem ![1, 0] ![1, 0] :=
    ⟨_, Exactness.odeSolution_add_smul_of_const (fun _ _ => actOn_coCol_one_field)
      (elem ![1, 0] ![1, 0]) 0 1, by simp, by
        change elem ![1, 0] ![1, 0] + (1 : ℝ) • ((2 : ℝ) • elem ![1, 0] ![1, 0]) =
          (3 : ℝ) • elem ![1, 0] ![1, 0]
        module⟩
  refine ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩,
    Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩,
    fun i => leafCol i (![![3 / 5, 4 / 5], ![1, 0]] i),
    ![(5 : ℝ) • elem ![3 / 5, 4 / 5] ![1, 0], (3 : ℝ) • elem ![1, 0] ![1, 0]],
    fun t => (3 / 5 : ℝ) • elem ![3 / 5, 4 / 5] ![1, 0] +
      t • ((22 / 5 : ℝ) • elem ![3 / 5, 4 / 5] ![1, 0]),
    Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨hK0, hK1⟩,
    Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩, ?_, ?_, rfl⟩
  -- orthonormal old bases and co-range bases
  · rw [leafCol_transpose_mul]; norm_num [Fin.sum_univ_two]
  · rw [leafCol_transpose_mul]; norm_num [Fin.sum_univ_two]
  · rw [coCol_transpose_mul]; norm_num [Fin.sum_univ_two]
  · rw [coCol_transpose_mul]; norm_num [Fin.sum_univ_two]
  -- the old projectors fix the start value
  · rw [subtreeProj_leafCol_zero]; norm_num [Fin.sum_univ_two]
  · exact p1e
  · rw [actOn_coCol_zero]; norm_num [Fin.sum_univ_two]
  · rw [actOn_coCol_one]; norm_num [Fin.sum_univ_two]
  -- orthonormal new bases
  · exact hU₁0
  · rw [leafCol_transpose_mul]; norm_num [Fin.sum_univ_two]
  -- capture
  · change (leaf (0 : Fin 2)).subtreeProj (leafCol 0 ![3 / 5, 4 / 5])
      ((5 : ℝ) • elem ![3 / 5, 4 / 5] ![1, 0]) = (5 : ℝ) • elem ![3 / 5, 4 / 5] ![1, 0]
    rw [map_smul, p0u]
  · change (leaf (1 : Fin 2)).subtreeProj (leafCol 1 ![1, 0])
      ((3 : ℝ) • elem ![1, 0] ![1, 0]) = (3 : ℝ) • elem ![1, 0] ![1, 0]
    rw [map_smul, p1e]
  -- the doubly normal parts
  · intro t _
    simp only [Matrix.cons_val_zero]
    rw [coNormal_zero, _root_.sub_apply, one_apply_eq_self]
    exact (isOrthProj_subtreeProj _ hU₁0).norm_sub_le _
  · intro t _
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [normal_one]
  -- the Galerkin step
  · refine Exactness.odeSolution_add_smul_of_const (fun _ _ => ?_) _ 0 1
    dsimp only
    rw [modeProd_succ, modeProd_succ, modeProd_zero, mul_apply_eq_comp, mul_apply_eq_comp,
      one_apply_eq_self]
    simp only [Fin.succ_zero_eq_one, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [field, map_add, p1c, p1n, add_zero, p0g]
  · dsimp only
    rw [modeProd_succ, modeProd_succ, modeProd_zero, mul_apply_eq_comp, mul_apply_eq_comp,
      one_apply_eq_self]
    simp only [Fin.succ_zero_eq_one, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [p1e, p0e, zero_smul, add_zero]

/-- The step `isBUGStep_frame` is an abstract TTN BUG step. -/
example := isBUGStep_frame.isTTNBUGStep _ isValid_node

/-- The numerical solution of `isBUGStep_frame` misses the exact solution
`A(t) = e₀ ⊗ e₀ + t g` by `-e₁ ⊗ e₁` after one step. -/
example : ((3 / 5 : ℝ) • elem ![3 / 5, 4 / 5] ![1, 0] +
      (1 : ℝ) • ((22 / 5 : ℝ) • elem ![3 / 5, 4 / 5] ![1, 0])) -
    (elem ![1, 0] ![1, 0] + (1 : ℝ) • field) = -elem ![0, 1] ![0, 1] := by
  have h := elem_add_elem
  rw [one_smul, ← eq_sub_iff_add_eq] at h
  rw [field, h]
  module

/-- Non-vacuity of `BasisFrame.bug_global_error` with an error that is not zero: one step of
`isBUGStep_frame` (`L = 0`, `B = ‖g‖`, `ε = ‖e₁ ⊗ e₁‖`, `δ = 0`) against the exact solution
`A(t) = e₀ ⊗ e₀ + t g`; the left-hand side at `n = 1` is `‖e₁ ⊗ e₁‖` (previous example). -/
example : ∀ n : ℕ, n ≤ 1 → (n : ℝ) * 1 ≤ 1 →
    ‖(if n = 0 then elem ![1, 0] ![1, 0] else (3 / 5 : ℝ) • elem ![3 / 5, 4 / 5] ![1, 0] +
        (1 : ℝ) • ((22 / 5 : ℝ) • elem ![3 / 5, 4 / 5] ![1, 0])) -
      (elem ![1, 0] ![1, 0] + (0 + (n : ℝ) * 1) • field)‖ ≤
      Real.exp (0 * 1) * (0 + 1 * (3 * (node fun i : Fin 2 => leaf i).nodeCount *
        (‖elem ![0, 1] ![0, 1]‖ + 6 * 0 * ‖field‖ * 1))) :=
  BasisFrame.bug_global_error isValid_node (F := fun _ _ => field) (L := 0) (B := ‖field‖)
    (ε := ‖elem ![0, 1] ![0, 1]‖) (fun _ _ _ => by simp) le_rfl (fun _ _ => le_rfl)
    (fun _ => continuous_const) (norm_nonneg _) (t₀ := 0) (h := 1) zero_le_one (by simp)
    (N := 1) (A := fun t => elem ![1, 0] ![1, 0] + t • field)
    (Exactness.odeSolution_add_smul_of_const (fun _ _ => rfl) _ _ _) (f := fun _ => frame)
    (Y := fun n => if n = 0 then elem ![1, 0] ![1, 0] else (3 / 5 : ℝ) •
      elem ![3 / 5, 4 / 5] ![1, 0] + (1 : ℝ) • ((22 / 5 : ℝ) • elem ![3 / 5, 4 / 5] ![1, 0]))
    (fun n hn => by
      obtain rfl : n = 0 := by omega
      simpa using isBUGStep_frame)
    (δ := 0) (T := 1) (by simp)

end BUGExample

end DimTree

end LeanDLRA
