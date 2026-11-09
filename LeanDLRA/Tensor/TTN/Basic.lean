import LeanDLRA.Tensor.Unfolding

/-!
# Tree tensor networks: subtree projectors and nested orthonormal bases

For a dimension tree `τ` (`LeanDLRA.DimTree`) this file proves the structural facts on which the
tree tensor network integrators rest (Ceruti–Lubich–Walach, arXiv 2002.11392, §2):

* the subtree projectors `Z ↦ Ten_τ(U_τ U_τᵀ Mat_τ(Z))` are orthogonal projectors for orthonormal
  bases, the projectors of disjoint subtrees commute (in particular those of the children of a
  node of a valid tree), and a subtree projector commutes with every map acting on the
  complementary modes (the co-range projectors `Q₀ i` of the `K`-steps);
* **nested orthonormal bases**: if every leaf basis has orthonormal columns and every connecting
  tensor has orthonormal rows of its root matricization, then every basis matrix
  `U_τ(x, a) = ∑_b C(a, b) ∏ᵢ U_{τᵢ}(x_{τᵢ}, bᵢ)` has orthonormal columns
  (arXiv 2002.11392, Lemma 2.4 in the orthonormal case); hence the tensor of an orthonormal
  tree tensor network of root rank one has norm `‖C_root‖ = 1`.

## Main results

* `DimTree.IsValid.disjoint`, `DimTree.IsValid.child`: validity of a node.
* `DimTree.isOrthProj_subtreeProj`, `DimTree.subtreeProj_comm_of_disjoint`,
  `DimTree.IsValid.subtreeProj_comm`, `DimTree.subtreeProj_comm_actOn_compl`.
* `DimTree.IsValid.sum_prod_restrict`: a sum over the multi-indices of a valid node factorizes
  over its subtrees.
* `TTN.basis_node_eq`: `U_τ = (⊗ᵢ U_{τᵢ}) Mat₀(C)ᵀ`.
* `TTN.basis_transpose_mul_self`: orthonormal tree tensor networks on valid trees have
  orthonormal basis matrices; `TTN.norm_toTensor`: their tensors have norm one.
-/

open scoped Matrix RealInnerProductSpace

namespace LeanDLRA

namespace DimTree

variable {κ : Type*} [DecidableEq κ]

/-- The modes of a leaf. -/
@[simp] lemma modes_leaf (k : κ) : (leaf k).modes = {k} := rfl

/-- The modes of a node are the union of the modes of its subtrees. -/
lemma modes_node {m : ℕ} (cs : Fin m → DimTree κ) :
    (node cs).modes = Finset.univ.biUnion fun i => (cs i).modes := rfl

/-- A mode belongs to a node iff it belongs to one of its subtrees. -/
lemma mem_modes_node_iff {m : ℕ} {cs : Fin m → DimTree κ} {k : κ} :
    k ∈ (node cs).modes ↔ ∃ i, k ∈ (cs i).modes := by
  simp [modes_node]

/-- The subtrees of a valid node are valid. -/
lemma IsValid.child {m : ℕ} {cs : Fin m → DimTree κ} (h : (node cs).IsValid) (i : Fin m) :
    (cs i).IsValid :=
  h.1 i

/-- Different subtrees of a valid node have disjoint mode sets. -/
lemma IsValid.disjoint {m : ℕ} {cs : Fin m → DimTree κ} (h : (node cs).IsValid) {i j : Fin m}
    (hij : i ≠ j) : Disjoint (cs i).modes (cs j).modes :=
  h.2 hij

/-- In a valid node, a mode lies in at most one subtree. -/
lemma IsValid.eq_of_mem {m : ℕ} {cs : Fin m → DimTree κ} (h : (node cs).IsValid) {i j : Fin m}
    {k : κ} (hi : k ∈ (cs i).modes) (hj : k ∈ (cs j).modes) : i = j := by
  by_contra hij
  exact Finset.disjoint_left.1 (h.disjoint hij) hi hj

variable [Fintype κ] {ι : κ → Type*} [∀ k, Fintype (ι k)]

/-- A subtree projector of an orthonormal basis is an orthogonal projector. -/
theorem isOrthProj_subtreeProj (τ : DimTree κ) {r : Type*} [Fintype r] [DecidableEq r]
    {U : Matrix (∀ k : {k // k ∈ τ.modes}, ι k) r ℝ} (hU : Uᵀ * U = 1) :
    IsOrthProj (τ.subtreeProj U) :=
  Tensor.isOrthProj_actOn_mul_transpose _ (by convert hU)

/-- Projectors of subtrees with disjoint mode sets commute. -/
theorem subtreeProj_comm_of_disjoint {τ σ : DimTree κ} (h : Disjoint τ.modes σ.modes)
    {r s : Type*} [Fintype r] [Fintype s] (U : Matrix (∀ k : {k // k ∈ τ.modes}, ι k) r ℝ)
    (V : Matrix (∀ k : {k // k ∈ σ.modes}, ι k) s ℝ) (X : Tensor ι) :
    τ.subtreeProj U (σ.subtreeProj V X) = σ.subtreeProj V (τ.subtreeProj U X) :=
  Tensor.actOn_comm_of_disjoint _ (fun _ hk hk' => Finset.disjoint_left.1 h hk hk') _ _ X

/-- **The projectors of the children of a valid node commute** (the new-basis projectors
`P₁ i` of the TTN integrators). -/
theorem IsValid.subtreeProj_comm {m : ℕ} {cs : Fin m → DimTree κ} (h : (node cs).IsValid)
    {r : Fin m → Type*} [∀ i, Fintype (r i)]
    (U : ∀ i, Matrix (∀ k : {k // k ∈ (cs i).modes}, ι k) (r i) ℝ) (i j : Fin m) (X : Tensor ι) :
    (cs i).subtreeProj (U i) ((cs j).subtreeProj (U j) X) =
      (cs j).subtreeProj (U j) ((cs i).subtreeProj (U i) X) := by
  by_cases hij : i = j
  · subst hij; rfl
  · exact subtreeProj_comm_of_disjoint (h.disjoint hij) _ _ X

/-- A subtree projector commutes with every map acting on the complementary modes (such as the
co-range projector `Q₀` of the `K`-step of the subtree). -/
theorem subtreeProj_comm_actOn_compl (τ : DimTree κ) {r : Type*} [Fintype r]
    (U : Matrix (∀ k : {k // k ∈ τ.modes}, ι k) r ℝ)
    (M : Matrix (∀ k : {k // k ∉ τ.modes}, ι k) (∀ k : {k // k ∉ τ.modes}, ι k) ℝ)
    (X : Tensor ι) :
    τ.subtreeProj U (Tensor.actOn (· ∉ τ.modes) M X) =
      Tensor.actOn (· ∉ τ.modes) M (τ.subtreeProj U X) :=
  Tensor.actOn_comm_of_disjoint _ (fun _ hk hk' => hk' hk) _ _ X

omit [Fintype κ] in
/-- **Fubini over the subtrees of a valid node**: summing a product of functions of the parts of a
multi-index over the modes of the node is the product of the sums over the subtrees. -/
theorem IsValid.sum_prod_restrict {m : ℕ} {cs : Fin m → DimTree κ} (h : (node cs).IsValid)
    (f : ∀ i, (∀ k : {k // k ∈ (cs i).modes}, ι k) → ℝ) :
    ∑ x : (∀ k : {k // k ∈ (node cs).modes}, ι k),
        ∏ i, f i (fun k => x ⟨k.1, mem_modes_node i k.2⟩) =
      ∏ i, ∑ y, f i y := by
  rw [Fintype.prod_sum]
  refine Fintype.sum_bijective
    (fun x i (k : {k // k ∈ (cs i).modes}) => x ⟨k.1, mem_modes_node i k.2⟩) ⟨?_, ?_⟩ _ _
    fun x => rfl
  · intro x x' hxx'
    funext k
    obtain ⟨i, hi⟩ := mem_modes_node_iff.1 k.2
    exact congrFun (congrFun hxx' i) ⟨k.1, hi⟩
  · intro y
    have hidx : ∀ k : {k // k ∈ (node cs).modes}, ∃ i, k.1 ∈ (cs i).modes := fun k =>
      mem_modes_node_iff.1 k.2
    refine ⟨fun k => y (hidx k).choose ⟨k.1, (hidx k).choose_spec⟩, ?_⟩
    funext i k
    have key : ∀ j (hj : j = i) (hk : k.1 ∈ (cs j).modes), y j ⟨k.1, hk⟩ = y i k := by
      rintro j rfl hk; rfl
    exact key _ (h.eq_of_mem (hidx ⟨k.1, mem_modes_node i k.2⟩).choose_spec k.2) _

end DimTree

namespace TTN

variable {κ : Type*} [DecidableEq κ] {ι : κ → Type*}

/-- The basis matrix of a leaf. -/
@[simp] lemma basis_leaf {k : κ} {r : ℕ} (U : Matrix (ι k) (Fin r) ℝ)
    (x : ∀ k' : {k' // k' ∈ (DimTree.leaf k).modes}, ι k') (a : Fin r) :
    (TTN.leaf U).basis x a = U (x ⟨k, Finset.mem_singleton_self k⟩) a := rfl

/-- The basis matrix of an inner node. -/
lemma basis_node {m : ℕ} {cs : Fin m → DimTree κ} {rs : Fin m → ℕ} {r : ℕ}
    (ds : ∀ i, TTN ι (cs i) (rs i)) (C : Matrix (Fin r) (∀ i, Fin (rs i)) ℝ)
    (x : ∀ k : {k // k ∈ (DimTree.node cs).modes}, ι k) (a : Fin r) :
    (TTN.node ds C).basis x a =
      ∑ b, C a b * ∏ i, (ds i).basis (fun k => x ⟨k.1, DimTree.mem_modes_node i k.2⟩) (b i) :=
  rfl

/-- `U_τ = (⊗ᵢ U_{τᵢ}) Mat₀(C)ᵀ`: the basis matrix of an inner node is the Kronecker product of
the subtree bases (restricted to the parts of the multi-index) times the transposed root
matricization of the connecting tensor. -/
theorem basis_node_eq {m : ℕ} {cs : Fin m → DimTree κ} {rs : Fin m → ℕ} {r : ℕ}
    (ds : ∀ i, TTN ι (cs i) (rs i)) (C : Matrix (Fin r) (∀ i, Fin (rs i)) ℝ) :
    (TTN.node ds C).basis = (Matrix.of fun (x : ∀ k : {k // k ∈ (DimTree.node cs).modes}, ι k)
      (b : ∀ i, Fin (rs i)) =>
        ∏ i, (ds i).basis (fun k => x ⟨k.1, DimTree.mem_modes_node i k.2⟩) (b i)) * Cᵀ := by
  ext x a
  simp only [basis_node, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

variable [∀ k, Fintype (ι k)]

/-- **Nested orthonormal bases** (arXiv 2002.11392, Lemma 2.4, orthonormal case): for a valid
dimension tree, if every leaf basis has orthonormal columns and every connecting tensor
satisfies `Mat₀(C) Mat₀(C)ᵀ = 1`, then every basis matrix `U_τ` has orthonormal columns. -/
theorem basis_transpose_mul_self :
    ∀ {τ : DimTree κ} {r : ℕ} (t : TTN ι τ r), τ.IsValid → t.IsOrthonormal →
      (t.basis)ᵀ * t.basis = 1
  | .leaf k, r, .leaf U, _, hU => by
    have hbij : Function.Bijective
        fun x : (∀ k' : {k' // k' ∈ (DimTree.leaf k).modes}, ι k') =>
          x ⟨k, Finset.mem_singleton_self k⟩ := by
      refine ⟨fun x x' hxx' => funext fun k' => ?_, fun c => ?_⟩
      · obtain ⟨k', hk'⟩ := k'
        obtain rfl := Finset.mem_singleton.1 hk'
        exact hxx'
      · exact ⟨fun k' => cast (congrArg ι (Finset.mem_singleton.1 k'.2).symm) c, rfl⟩
    ext a a'
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, basis_leaf]
    rw [Fintype.sum_bijective _ hbij (fun x => U (x ⟨k, Finset.mem_singleton_self k⟩) a *
      U (x ⟨k, Finset.mem_singleton_self k⟩) a') (fun c => U c a * U c a') fun _ => rfl]
    have := congrFun (congrFun (show Uᵀ * U = 1 from hU) a) a'
    simpa [Matrix.mul_apply] using this
  | .node cs, r, .node (rs := rs) ds C, hv, hon => by
    obtain ⟨hds, hC⟩ := hon
    have ih : ∀ i, ((ds i).basis)ᵀ * (ds i).basis = 1 := fun i =>
      basis_transpose_mul_self (ds i) (hv.child i) (hds i)
    set P : Matrix (∀ k : {k // k ∈ (DimTree.node cs).modes}, ι k) (∀ i, Fin (rs i)) ℝ :=
      Matrix.of fun x b => ∏ i, (ds i).basis (fun k => x ⟨k.1, DimTree.mem_modes_node i k.2⟩)
        (b i) with hP
    have hPP : Pᵀ * P = 1 := by
      ext b b'
      rw [Matrix.mul_apply]
      simp only [hP, Matrix.transpose_apply, Matrix.of_apply, ← Finset.prod_mul_distrib]
      rw [hv.sum_prod_restrict (fun i y => (ds i).basis y (b i) * (ds i).basis y (b' i))]
      have hi : ∀ i, ∑ y, (ds i).basis y (b i) * (ds i).basis y (b' i) =
          if b i = b' i then 1 else 0 := fun i => by
        have := congrFun (congrFun (ih i) (b i)) (b' i)
        simpa [Matrix.mul_apply, Matrix.one_apply] using this
      simp only [hi, Matrix.one_apply]
      by_cases hb : b = b'
      · subst hb; simp
      · obtain ⟨i, hi'⟩ := Function.ne_iff.mp hb
        rw [ite_eq_right_iff.mpr fun h => (hb h).elim]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi'])
    rw [basis_node_eq, ← hP, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Pᵀ, hPP, Matrix.one_mul]
    exact hC

/-- **Unit norm of orthonormal tree tensor networks**: if the tree is valid, covers all modes
and the network (root rank one) is orthonormal, the represented tensor has norm one, i.e. it is
an isometric image of its root connecting tensor (`‖Y‖ = ‖Mat₀(C_root)‖ = 1`). -/
theorem norm_toTensor [Fintype κ] {τ : DimTree κ} (t : TTN ι τ 1) (hτ : τ.IsValid)
    (ht : t.IsOrthonormal) (hall : ∀ k, k ∈ τ.modes) : ‖t.toTensor‖ = 1 := by
  have hbij : Function.Bijective
      fun (x : ∀ k, ι k) (k : {k // k ∈ τ.modes}) => x k.1 :=
    ⟨fun x x' h => funext fun k => congrFun h ⟨k, hall k⟩,
      fun y => ⟨fun k => y ⟨k, hall k⟩, rfl⟩⟩
  have h1 := congrFun (congrFun (basis_transpose_mul_self t hτ ht) 0) 0
  rw [Matrix.mul_apply] at h1
  have hsq : ‖t.toTensor‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, Tensor.inner_eq_sum]
    change ∑ x : ∀ k, ι k, t.basis (fun k => x k.1) 0 * t.basis (fun k => x k.1) 0 = 1
    rw [Fintype.sum_bijective _ hbij (fun x => t.basis (fun k => x k.1) 0 *
      t.basis (fun k => x k.1) 0) (fun y => t.basis y 0 * t.basis y 0) fun _ => rfl]
    simpa using h1
  have h0 : 0 ≤ ‖t.toTensor‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖t.toTensor‖ - 1)]

end TTN

/-! ### Example -/

/-- The Tucker-shaped dimension tree with two leaves `0` and `1` is valid. -/
example : (DimTree.node ![DimTree.leaf (0 : Fin 2), DimTree.leaf 1]).IsValid := by
  refine ⟨fun i => by fin_cases i <;> trivial, fun i j hij => ?_⟩
  fin_cases i <;> fin_cases j <;> simp_all

/-- Non-vacuity of `TTN.basis_transpose_mul_self`: a leaf with an orthonormal basis. -/
example :
    ((TTN.leaf (ι := fun _ : Fin 2 => Fin 2) (k := 0) (1 : Matrix (Fin 2) (Fin 2) ℝ)).basis)ᵀ *
      (TTN.leaf (ι := fun _ : Fin 2 => Fin 2) (k := 0) (1 : Matrix (Fin 2) (Fin 2) ℝ)).basis =
      1 :=
  TTN.basis_transpose_mul_self _ trivial (by simp [TTN.IsOrthonormal])

end LeanDLRA
