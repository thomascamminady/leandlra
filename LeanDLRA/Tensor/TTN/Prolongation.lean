import LeanDLRA.Tensor.TTN.ProjectorSplitting

/-!
# Prolongation and restriction for tree tensor network subproblems

The tree tensor network (TTN) integrators of Ceruti–Lubich–Walach (arXiv 2002.11392, §4.2) and
Ceruti–Kusch–Lubich–Sulz (arXiv 2412.00858, §4.1) pose the subproblem of a child `τᵢ` of a node
on the reduced space `V_{τᵢ} = ℝ^{r} ⊗ ⨂_{k ∈ τᵢ} ℝ^{n_k}` (an extra root index of dimension
`r = r_{τᵢ}`), through the prolongation and the restriction

  `π(Y) = Tenᵢ((V⁰ Mat₀(Y))ᵀ)`,   `π†(Z) = Ten₀((Matᵢ(Z) V⁰)ᵀ)`,

where `V⁰` has orthonormal columns and rows indexed by the modes outside `τᵢ`. This file defines
them for a subtree `τ` of a tree whose root has rank one, i.e. for maps between the reduced space
`EuclideanSpace ℝ (s × ∏_{k ∈ τ} ι k)` and the full tensor space `Tensor ι`
(`(π Y)(x) = ∑ₐ V⁰(x_{∉τ}, a) Y(a, x_τ)`), and proves Lemma 4.1 of arXiv 2002.11392 for them:
`π† π = 1`, `π† = π*`, `‖π Y‖ = ‖Y‖` and `‖π† Z‖ ≤ ‖Z‖`. Moreover `π π†` is the co-range projector
`Q₀ = actOn {k ∉ τ} (V⁰ V⁰ᵀ)` of the `K`-step, so the reduced problem `ẏ = π† F(t, π y)` with the
reduced initial value `π†(Y⁰)` (Definition 4.2) is conjugate to the `K`-step problem
`ż = Q₀ F(t, z)` on the full tensor space that the library's TTN integrators use
(`odeSolution_kStep_of_reduced`, `odeSolution_reduced_of_kStep`). Deeper subtrees are reached by
composing such maps; their composite prolongations are again of this form with a composite basis
`W = (V⁰ ⊗ 1) Ṽ`.

## Main definitions

* `DimTree.prolong τ V`, `DimTree.restrict τ V`.

## Main results

* `DimTree.restrict_prolong`, `DimTree.inner_prolong`, `DimTree.adjoint_prolong`,
  `DimTree.norm_prolong`, `DimTree.norm_restrict_le`: Lemma 4.1 of arXiv 2002.11392.
* `DimTree.prolong_restrict`, `DimTree.prolong_comp_adjoint`: `π π† = Q₀`.
* `DimTree.odeSolution_kStep_of_reduced`, `DimTree.odeSolution_reduced_of_kStep`: the reduced
  subproblem and the `K`-step problem are conjugate.
-/

open Set
open scoped Matrix RealInnerProductSpace

namespace LeanDLRA

namespace DimTree

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : κ → Type*} [∀ k, Fintype (ι k)]
  {s : Type*} [Fintype s]

/-- The **prolongation** `π(Y) = Tenᵢ((V Mat₀(Y))ᵀ)` (arXiv 2002.11392, (4.6)) from the reduced
space of the subtree `τ` (root index `a : s`, then the modes of `τ`) to the full tensor space:
`(π Y)(x) = ∑ₐ V(x_{∉τ}, a) Y(a, x_τ)`. -/
noncomputable def prolong (τ : DimTree κ) (V : Matrix (∀ k : {k // k ∉ τ.modes}, ι k) s ℝ) :
    EuclideanSpace ℝ (s × ∀ k : {k // k ∈ τ.modes}, ι k) →L[ℝ] Tensor ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Y => WithLp.toLp 2 fun x =>
        ∑ a, V (Subtype.restrict (· ∉ τ.modes) x) a * Y (a, Subtype.restrict (· ∈ τ.modes) x)
      map_add' := fun Y Z => by
        ext x; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c Y => by
        ext x; simp [Finset.mul_sum, mul_left_comm] }

/-- The **restriction** `π†(Z) = Ten₀((Matᵢ(Z) V)ᵀ)` (arXiv 2002.11392, (4.7)) from the full
tensor space to the reduced space of the subtree `τ`:
`(π† Z)(a, y) = ∑_z V(z, a) Z(y, z)`, where `(y, z)` is the multi-index with `τ`-part `y`. -/
noncomputable def restrict (τ : DimTree κ) (V : Matrix (∀ k : {k // k ∉ τ.modes}, ι k) s ℝ) :
    Tensor ι →L[ℝ] EuclideanSpace ℝ (s × ∀ k : {k // k ∈ τ.modes}, ι k) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Z => WithLp.toLp 2 fun ay =>
        ∑ z, V z ay.1 * Z (Tensor.merge (· ∈ τ.modes) ay.2 z)
      map_add' := fun Y Z => by
        ext x; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c Y => by
        ext x; simp [Finset.mul_sum, mul_left_comm] }

/-- The entries of the prolongation. -/
@[simp] lemma prolong_apply (τ : DimTree κ) (V : Matrix (∀ k : {k // k ∉ τ.modes}, ι k) s ℝ)
    (Y : EuclideanSpace ℝ (s × ∀ k : {k // k ∈ τ.modes}, ι k)) (x : ∀ k, ι k) :
    prolong τ V Y x =
      ∑ a, V (Subtype.restrict (· ∉ τ.modes) x) a * Y (a, Subtype.restrict (· ∈ τ.modes) x) :=
  rfl

/-- The entries of the restriction. -/
@[simp] lemma restrict_apply (τ : DimTree κ) (V : Matrix (∀ k : {k // k ∉ τ.modes}, ι k) s ℝ)
    (Z : Tensor ι) (a : s) (y : ∀ k : {k // k ∈ τ.modes}, ι k) :
    restrict τ V Z (a, y) = ∑ z, V z a * Z (Tensor.merge (· ∈ τ.modes) y z) :=
  rfl

/-- **Restriction after prolongation is the identity** (arXiv 2002.11392, Lemma 4.1, (4.8)). -/
theorem restrict_prolong [DecidableEq s] (τ : DimTree κ)
    {V : Matrix (∀ k : {k // k ∉ τ.modes}, ι k) s ℝ} (hV : Vᵀ * V = 1)
    (Y : EuclideanSpace ℝ (s × ∀ k : {k // k ∈ τ.modes}, ι k)) :
    restrict τ V (prolong τ V Y) = Y := by
  ext ⟨a, y⟩
  rw [restrict_apply]
  simp only [prolong_apply, Tensor.restrict_merge, Tensor.restrict_not_merge, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ b, ∑ z, V z a * (V z b * Y (b, y)) = (1 : Matrix s s ℝ) a b * Y (b, y) := fun b => by
    rw [← hV, Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ => by rw [Matrix.transpose_apply]; ring
  simp only [h, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- **The restriction is the adjoint of the prolongation** (arXiv 2002.11392, Lemma 4.1, (4.9)):
`⟪π Y, Z⟫ = ⟪Y, π† Z⟫`. -/
theorem inner_prolong (τ : DimTree κ) (V : Matrix (∀ k : {k // k ∉ τ.modes}, ι k) s ℝ)
    (Y : EuclideanSpace ℝ (s × ∀ k : {k // k ∈ τ.modes}, ι k)) (Z : Tensor ι) :
    ⟪prolong τ V Y, Z⟫ = ⟪Y, restrict τ V Z⟫ := by
  have hR : ⟪Y, restrict τ V Z⟫ =
      ∑ a, ∑ y, Y (a, y) * ∑ z, V z a * Z (Tensor.merge (· ∈ τ.modes) y z) := by
    simp [PiLp.inner_apply, Fintype.sum_prod_type, mul_comm]
  rw [hR, Tensor.inner_eq_sum, Tensor.sum_eq_sum_merge (· ∈ τ.modes)]
  simp only [prolong_apply, Tensor.restrict_merge, Tensor.restrict_not_merge, Finset.sum_mul,
    Finset.mul_sum]
  conv_lhs => arg 2; ext y; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  have hu : ∀ i₁ i₂ : Fintype (∀ k : {k // k ∈ τ.modes}, ι k),
      @Finset.univ _ i₁ = @Finset.univ _ i₂ := fun i₁ i₂ => by rw [Subsingleton.elim i₁ i₂]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr (hu _ _) fun y _ =>
    Finset.sum_congr rfl fun z _ => ?_
  ring

/-- `π† = π*` as continuous linear maps. -/
theorem adjoint_prolong (τ : DimTree κ) (V : Matrix (∀ k : {k // k ∉ τ.modes}, ι k) s ℝ) :
    (prolong τ V).adjoint = restrict τ V :=
  ((ContinuousLinearMap.eq_adjoint_iff (restrict τ V) (prolong τ V)).2 fun Z Y => by
    rw [real_inner_comm, ← inner_prolong, real_inner_comm]).symm

/-- **The prolongation is an isometry** (arXiv 2002.11392, Lemma 4.1). -/
theorem norm_prolong [DecidableEq s] (τ : DimTree κ)
    {V : Matrix (∀ k : {k // k ∉ τ.modes}, ι k) s ℝ} (hV : Vᵀ * V = 1)
    (Y : EuclideanSpace ℝ (s × ∀ k : {k // k ∈ τ.modes}, ι k)) :
    ‖prolong τ V Y‖ = ‖Y‖ := by
  have h : ‖prolong τ V Y‖ ^ 2 = ‖Y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_prolong,
      restrict_prolong τ hV]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- **The restriction does not increase the norm** (arXiv 2002.11392, Lemma 4.1). -/
theorem norm_restrict_le [DecidableEq s] (τ : DimTree κ)
    {V : Matrix (∀ k : {k // k ∉ τ.modes}, ι k) s ℝ} (hV : Vᵀ * V = 1) (Z : Tensor ι) :
    ‖restrict τ V Z‖ ≤ ‖Z‖ := by
  have h1 : ‖restrict τ V Z‖ * ‖restrict τ V Z‖ ≤ ‖restrict τ V Z‖ * ‖Z‖ := by
    calc ‖restrict τ V Z‖ * ‖restrict τ V Z‖ = ⟪restrict τ V Z, restrict τ V Z⟫ :=
          (real_inner_self_eq_norm_mul_norm _).symm
      _ = ⟪prolong τ V (restrict τ V Z), Z⟫ := (inner_prolong τ V _ Z).symm
      _ ≤ ‖prolong τ V (restrict τ V Z)‖ * ‖Z‖ := real_inner_le_norm _ _
      _ = ‖restrict τ V Z‖ * ‖Z‖ := by rw [norm_prolong τ hV]
  rcases (norm_nonneg (restrict τ V Z)).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg Z
  · exact le_of_mul_le_mul_left h1 hpos

/-- **Prolongation after restriction is the co-range projector** `Q₀ = actOn {k ∉ τ} (V Vᵀ)` of the
`K`-step: `π π† Z = Ten_τ(Mat_τ(Z) V Vᵀ)`. -/
theorem prolong_restrict (τ : DimTree κ) (V : Matrix (∀ k : {k // k ∉ τ.modes}, ι k) s ℝ)
    (Z : Tensor ι) :
    prolong τ V (restrict τ V Z) = Tensor.actOn (· ∉ τ.modes) (V * Vᵀ) Z := by
  ext x
  rw [prolong_apply, Tensor.actOn_apply]
  simp only [restrict_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hx : Tensor.merge (· ∈ τ.modes) (Subtype.restrict (· ∈ τ.modes) x) z =
      Tensor.override (· ∉ τ.modes) x z := by
    funext k
    by_cases hk : k ∈ τ.modes
    · simp [Tensor.merge, Tensor.override, hk, Subtype.restrict]
    · simp [Tensor.merge, Tensor.override, hk]
  rw [hx, Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by rw [Matrix.transpose_apply]; ring

/-- `π π† = Q₀` as continuous linear maps. -/
theorem prolong_comp_adjoint (τ : DimTree κ) (V : Matrix (∀ k : {k // k ∉ τ.modes}, ι k) s ℝ) :
    (prolong τ V).comp (prolong τ V).adjoint = Tensor.actOn (· ∉ τ.modes) (V * Vᵀ) := by
  ext1 Z
  rw [ContinuousLinearMap.comp_apply, adjoint_prolong, prolong_restrict]

/-- **Reduced subproblems are `K`-step problems** (arXiv 2002.11392, Definition 4.2 and
(4.3)–(4.5)): if `y` solves the reduced problem `ẏ = π† G(t, π y)`, then `π y` solves the
`K`-step problem `ż = Q₀ G(t, z)` on the full tensor space, `Q₀ = actOn {k ∉ τ} (V Vᵀ)`. -/
theorem odeSolution_kStep_of_reduced (τ : DimTree κ)
    (V : Matrix (∀ k : {k // k ∉ τ.modes}, ι k) s ℝ) {G : ℝ → Tensor ι → Tensor ι} {t₀ t₁ : ℝ}
    {y : ℝ → EuclideanSpace ℝ (s × ∀ k : {k // k ∈ τ.modes}, ι k)}
    (hy : ODESolution (fun t x => restrict τ V (G t (prolong τ V x))) y t₀ t₁) :
    ODESolution (fun t z => Tensor.actOn (· ∉ τ.modes) (V * Vᵀ) (G t z))
      (fun t => prolong τ V (y t)) t₀ t₁ := by
  have h := odeSolution_prolong (prolong τ V) (G := G) (by simpa only [adjoint_prolong] using hy)
  simpa only [prolong_comp_adjoint] using h

/-- **`K`-step problems are reduced subproblems** (arXiv 2002.11392, Definition 4.2): let `V` have
orthonormal columns. If `z` solves the `K`-step problem `ż = Q₀ G(t, z)`,
`Q₀ = actOn {k ∉ τ} (V Vᵀ)`, from `z t₀ = π y₀`, then `y = π† z` solves the reduced problem
`ẏ = π† G(t, π y)` with `y t₀ = y₀` (the reduced initial value `π†(Y⁰)`), and `z = π y`
on `[t₀, t₁]`. -/
theorem odeSolution_reduced_of_kStep [DecidableEq s] (τ : DimTree κ)
    {V : Matrix (∀ k : {k // k ∉ τ.modes}, ι k) s ℝ} (hV : Vᵀ * V = 1)
    {G : ℝ → Tensor ι → Tensor ι} {t₀ t₁ : ℝ} {z : ℝ → Tensor ι}
    (hz : ODESolution (fun t x => Tensor.actOn (· ∉ τ.modes) (V * Vᵀ) (G t x)) z t₀ t₁)
    {y₀ : EuclideanSpace ℝ (s × ∀ k : {k // k ∈ τ.modes}, ι k)} (hz₀ : z t₀ = prolong τ V y₀) :
    ODESolution (fun t y => restrict τ V (G t (prolong τ V y))) (fun t => restrict τ V (z t))
        t₀ t₁ ∧ restrict τ V (z t₀) = y₀ ∧
      ∀ t ∈ Icc t₀ t₁, prolong τ V (restrict τ V (z t)) = z t := by
  have hπ : ∀ y, (prolong τ V).adjoint (prolong τ V y) = y := fun y => by
    rw [adjoint_prolong, restrict_prolong τ hV]
  have h := odeSolution_restrict (prolong τ V) hπ (G := G) (z := z)
    (by simpa only [prolong_comp_adjoint] using hz) hz₀
  simpa only [adjoint_prolong] using h

end DimTree

end LeanDLRA
