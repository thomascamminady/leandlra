import LeanDLRA.Tensor.TTN.Basic
import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.OpenProblems.TensorNetworks.Part1Defs
import LeanDLRA.Classical.CommutingProjectorTelescoping

/-!
# Tree tensor network integrators on concrete tree tensor networks

The recursive tree tensor network integrators of the library are stated on an abstract inner
product space with families of projectors per inner node:

* the TTN projector-splitting integrator `OpenProblems.TensorNetworks.IsTTNKSLStep` over a
  `TreeShape` (Ceruti–Lubich–Walach, arXiv 2002.11392, §4; robust error bound
  `ttn_ksl_global_error`, Thm 6.1), whose nodes are nested Tucker KSL steps
  (`IsTuckerKSLStep`);
* the TTN BUG, rank-adaptive and parallel TTN BUG integrators over a `TTNFrame`
  (Ceruti–Lubich–Sulz, SINUM 2023; arXiv 2412.00858, §4), whose nodes are Tucker BUG steps
  (`IsTuckerBUGStep`, `IsParTuckerBUGStep`).

At an inner node `τ = (τ₁, …, τ_m)` of a dimension tree, the projectors are the subtree
projectors `P₁ i = Ten_{τᵢ}(U¹ᵢ U¹ᵢᵀ Mat_{τᵢ}(·))` of the new bases and the co-range projectors
`Q₀ i = Ten_{τᵢ}(Mat_{τᵢ}(·) V⁰ᵢ V⁰ᵢᵀ)` of the matricizations of the old approximation. This file
proves that these concrete projectors satisfy the structural hypotheses of the abstract node
steps (orthogonality, commutation of the projectors of different subtrees), so that every node
step built from orthonormal bases on a valid dimension tree is an instance, and that an
orthonormal tree tensor network is fixed by the subtree projectors of its own bases.

## Main definitions

* `DimTree.toTreeShape`: the shape of a dimension tree (bridge to
  `OpenProblems.TensorNetworks.TreeShape`, which forgets the mode labels).

## Main results

* `DimTree.IsValid.isTuckerBUGStep`: a node step of the TTN BUG integrator built from
  orthonormal subtree bases is an `IsTuckerBUGStep`.
* `DimTree.IsValid.isTuckerKSLStep`: a node step of the TTN projector-splitting integrator built
  from orthonormal subtree bases is an `IsTuckerKSLStep`.
* `TTN.subtreeProj_toTensor`: `P₀ i Y₀ = Y₀` for the tensor `Y₀` of an orthonormal tree tensor
  network and the projectors `P₀ i` of the bases of the subtrees of its root.
-/

open scoped Matrix RealInnerProductSpace

namespace LeanDLRA

namespace DimTree

/-- The shape of a dimension tree, forgetting the mode labels of the leaves (bridge to the
`TreeShape` of the abstract TTN projector-splitting integrator). -/
def toTreeShape {κ : Type*} : DimTree κ → OpenProblems.TensorNetworks.TreeShape
  | leaf _ => .leaf
  | @node _ m cs => .node m fun i => (cs i).toTreeShape

/-- The shape of a leaf. -/
@[simp] lemma toTreeShape_leaf {κ : Type*} (k : κ) :
    (leaf k).toTreeShape = OpenProblems.TensorNetworks.TreeShape.leaf := rfl

/-- The shape of an inner node. -/
@[simp] lemma toTreeShape_node {κ : Type*} {m : ℕ} (cs : Fin m → DimTree κ) :
    (node cs).toTreeShape =
      OpenProblems.TensorNetworks.TreeShape.node m fun i => (cs i).toTreeShape := rfl

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : κ → Type*} [∀ k, Fintype (ι k)]

/-- The co-range projector of a subtree, acting on the complementary modes, is an orthogonal
projector for a basis with orthonormal columns. -/
theorem isOrthProj_coRangeProj (τ : DimTree κ) {s : Type*} [Fintype s] [DecidableEq s]
    {V : Matrix (∀ k : {k // k ∉ τ.modes}, ι k) s ℝ} (hV : Vᵀ * V = 1) :
    IsOrthProj (Tensor.actOn (· ∉ τ.modes) (V * Vᵀ)) :=
  Tensor.isOrthProj_actOn_mul_transpose _ hV

/-- **Concrete TTN BUG node steps.** At an inner node of a valid dimension tree, a step with new
subtree bases `U¹ᵢ` and co-range bases `V⁰ᵢ` with orthonormal columns satisfies
`IsTuckerBUGStep` with the subtree projectors `P₁ i` and co-range projectors `Q₀ i`, given the
`K`-step, capture, normal-component and Galerkin conditions. Orthogonality of all projectors and
commutation of the `P₁ i` (which act on disjoint sets of modes) are derived. -/
theorem IsValid.isTuckerBUGStep {m : ℕ} {cs : Fin m → DimTree κ} (hv : (node cs).IsValid)
    {r s : Fin m → Type*} [∀ i, Fintype (r i)] [∀ i, DecidableEq (r i)] [∀ i, Fintype (s i)]
    [∀ i, DecidableEq (s i)]
    {U₁ : ∀ i, Matrix (∀ k : {k // k ∈ (cs i).modes}, ι k) (r i) ℝ}
    (hU₁ : ∀ i, (U₁ i)ᵀ * U₁ i = 1)
    {V₀ : ∀ i, Matrix (∀ k : {k // k ∉ (cs i).modes}, ι k) (s i) ℝ}
    (hV₀ : ∀ i, (V₀ i)ᵀ * V₀ i = 1) {F : ℝ → Tensor ι → Tensor ι} {ε t₀ t₁ : ℝ}
    {Y₀ : Tensor ι} {YK : Fin m → ℝ → Tensor ι} {YS : ℝ → Tensor ι}
    (hK : ∀ i, ODESolution (fun t x => Tensor.actOn (· ∉ (cs i).modes) (V₀ i * (V₀ i)ᵀ) (F t x))
      (YK i) t₀ t₁)
    (hK₀ : ∀ i, YK i t₀ = Y₀) (hcap : ∀ i, (cs i).subtreeProj (U₁ i) (YK i t₁) = YK i t₁)
    (hε : ∀ i, ∀ t ∈ Set.Icc t₀ t₁, ‖(1 - (cs i).subtreeProj (U₁ i))
      ((1 - Tensor.actOn (· ∉ (cs i).modes) (V₀ i * (V₀ i)ᵀ)) (F t (YK i t₁)))‖ ≤ ε)
    (hS : ODESolution (fun t x => modeProd (fun i => (cs i).subtreeProj (U₁ i)) (F t x)) YS t₀ t₁)
    (hS₀ : YS t₀ = modeProd (fun i => (cs i).subtreeProj (U₁ i)) Y₀) :
    IsTuckerBUGStep F ε (fun i => Tensor.actOn (· ∉ (cs i).modes) (V₀ i * (V₀ i)ᵀ))
      (fun i => (cs i).subtreeProj (U₁ i)) t₀ t₁ Y₀ YK YS where
  projQ₀ i := isOrthProj_coRangeProj (cs i) (hV₀ i)
  projP₁ i := isOrthProj_subtreeProj (cs i) (hU₁ i)
  comm₁ := hv.subtreeProj_comm U₁
  kSol := hK
  kStart := hK₀
  kCap := hcap
  kNormal := hε
  sSol := hS
  sStart := hS₀

/-- **Concrete TTN projector-splitting node steps.** At an inner node of a valid dimension tree,
a nested Tucker KSL step with new subtree bases `U¹ᵢ` and co-range bases `V⁰ᵢ` with orthonormal
columns satisfies `IsTuckerKSLStep` (arXiv 2002.11392, §4) once its substep conditions hold;
orthogonality and commutation of the projectors are derived. -/
theorem IsValid.isTuckerKSLStep {m : ℕ} {cs : Fin m → DimTree κ} (hv : (node cs).IsValid)
    {r s : Fin m → Type*} [∀ i, Fintype (r i)] [∀ i, DecidableEq (r i)] [∀ i, Fintype (s i)]
    [∀ i, DecidableEq (s i)]
    {U₁ : ∀ i, Matrix (∀ k : {k // k ∈ (cs i).modes}, ι k) (r i) ℝ}
    (hU₁ : ∀ i, (U₁ i)ᵀ * U₁ i = 1)
    {V₀ : ∀ i, Matrix (∀ k : {k // k ∉ (cs i).modes}, ι k) (s i) ℝ}
    (hV₀ : ∀ i, (V₀ i)ᵀ * V₀ i = 1) {F : ℝ → Tensor ι → Tensor ι} {ε t₀ t₁ : ℝ}
    {Y₀ : Tensor ι} {X : Fin (m + 1) → Tensor ι} {K : Fin m → Tensor ι}
    {YS : Fin m → ℝ → Tensor ι} {YC : ℝ → Tensor ι}
    (start : X 0 = Y₀)
    (qFix : ∀ i, Tensor.actOn (· ∉ (cs i).modes) (V₀ i * (V₀ i)ᵀ) (X i.castSucc) = X i.castSucc)
    (kCap : ∀ i, (cs i).subtreeProj (U₁ i) (K i) = K i)
    (kNormal : ∀ i, ∀ t ∈ Set.Icc t₀ t₁, ‖(1 - (cs i).subtreeProj (U₁ i))
      ((1 - Tensor.actOn (· ∉ (cs i).modes) (V₀ i * (V₀ i)ᵀ))
        (modePrefix (fun i => (cs i).subtreeProj (U₁ i)) (i : ℕ)
          (F t (K i))))‖ ≤ ε)
    (sSol : ∀ i, ODESolution (fun t x => -((cs i).subtreeProj (U₁ i)
      (Tensor.actOn (· ∉ (cs i).modes) (V₀ i * (V₀ i)ᵀ)
        (modePrefix (fun i => (cs i).subtreeProj (U₁ i)) (i : ℕ)
          (F t x))))) (YS i) t₀ t₁)
    (sStart : ∀ i, YS i t₀ = K i) (next : ∀ i, X i.succ = YS i t₁)
    (cSol : ODESolution (fun t x => modeProd (fun i => (cs i).subtreeProj (U₁ i)) (F t x)) YC t₀ t₁)
    (cStart : YC t₀ = X (Fin.last m)) :
    OpenProblems.TensorNetworks.IsTuckerKSLStep F ε
      (fun i => Tensor.actOn (· ∉ (cs i).modes) (V₀ i * (V₀ i)ᵀ))
      (fun i => (cs i).subtreeProj (U₁ i)) t₀ t₁ Y₀ X K YS YC where
  projQ₀ i := isOrthProj_coRangeProj (cs i) (hV₀ i)
  projP₁ i := isOrthProj_subtreeProj (cs i) (hU₁ i)
  comm₁ := hv.subtreeProj_comm U₁
  start := start
  qFix := qFix
  kCap := kCap
  kNormal := kNormal
  sSol := sSol
  sStart := sStart
  next := next
  cSol := cSol
  cStart := cStart

end DimTree

namespace TTN

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : κ → Type*} [∀ k, Fintype (ι k)]

/-- **An orthonormal tree tensor network is fixed by the projectors of its subtree bases**: for
`Y₀ = C_τ ×ᵢ U_{τᵢ}` (root rank one) on a valid tree, `P₀ i Y₀ = Y₀` with
`P₀ i = Ten_{τᵢ}(U_{τᵢ} U_{τᵢ}ᵀ Mat_{τᵢ}(·))` (the hypothesis `P₀ i Y₀ = Y₀` of the TTN BUG and
parallel TTN BUG node steps). -/
theorem subtreeProj_toTensor {m : ℕ} {cs : Fin m → DimTree κ} {rs : Fin m → ℕ}
    (ds : ∀ i, TTN ι (cs i) (rs i)) (C : Matrix (Fin 1) (∀ i, Fin (rs i)) ℝ)
    (hv : (DimTree.node cs).IsValid) (hds : ∀ i, (ds i).IsOrthonormal) (i : Fin m) :
    (cs i).subtreeProj (ds i).basis (TTN.node ds C).toTensor = (TTN.node ds C).toTensor := by
  have hU := basis_transpose_mul_self (ds i) (hv.child i) (hds i)
  refine Tensor.actOn_mul_transpose_apply_eq_self_of _ (by convert hU)
    (fun c x => ∑ b, if b i = c then C 0 b * ∏ j ∈ Finset.univ.erase i,
      (ds j).basis (fun k => x k.1) (b j) else 0) (fun c x z => ?_) (fun x => ?_)
  · refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    refine congrArg (C 0 b * ·) (Finset.prod_congr rfl fun j hj => ?_)
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    congr 1
    funext k
    exact Tensor.override_apply_of_not _
      (fun hk => Finset.disjoint_left.1 (hv.disjoint hji) k.2 hk)
  · change ∑ b, C 0 b * ∏ j, (ds j).basis (fun k => x k.1) (b j) = _
    simp only [Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hr : Subtype.restrict (fun k => k ∈ (cs i).modes) x =
        fun (k : {k // k ∈ (cs i).modes}) => x k.1 := rfl
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, hr]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    ring

end TTN

end LeanDLRA
