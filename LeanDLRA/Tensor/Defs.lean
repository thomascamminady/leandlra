import LeanDLRA.Foundations.Projector
import LeanDLRA.Matrix.Frobenius

/-!
# Tensors, unfoldings and tensor formats: definitions

This file fixes the vocabulary of the tensor layer of LeanDLRA: real tensors with an arbitrary
finite set of modes, their unfoldings (matricizations) with respect to any set of modes, linear
maps acting on a set of modes, and the three tensor formats of dynamical low-rank approximation:
Tucker tensors, tensor trains (matrix product states) and tree tensor networks.

## Conventions

* The modes are a finite type `κ`; mode `k` carries the finite index type `ι k`. A *multi-index*
  is an element `x : ∀ k, ι k` and a tensor is a function of multi-indices, as an element of
  `Tensor ι = EuclideanSpace ℝ (∀ k, ι k)`. Its norm is the Euclidean (Frobenius) norm of the
  entries, `‖X‖² = ∑ₓ X(x)²`, which is the norm of all DLRA papers on tensors (Koch–Lubich 2010,
  Lubich–Rohwedder–Schneider–Vandereycken 2013, Lubich–Oseledets–Vandereycken 2015,
  Ceruti–Lubich–Walach 2021).
* A set of modes is a decidable predicate `p : κ → Prop`. The `p`-part of a multi-index `x` is
  `Subtype.restrict p x : ∀ k : Subtype p, ι k`. Tensor trains have modes `Fin d`; the left
  interface at cut `k` is the set `{i | i < k}` (the paper's modes `1, …, k`) and the right
  interface the set `{i | k ≤ i}` (the paper's modes `k + 1, …, d`).
* The unfolding `unfold p X` is the matrix with rows indexed by the `p`-part and columns by the
  rest; for a single mode it is the mode-`k` matricization `Matₖ`, for a TT cut it is the
  unfolding `Y⟨k⟩`, and for a subtree of a dimension tree it is the matricization `Mat_τ`. Rows and
  columns are indexed by multi-indices, not by (co)lexicographic integers, so no ordering
  convention is needed.
* Linear maps acting on a set of modes are `actOn p M` for a matrix `M` on the `p`-part:
  `(actOn p M X)(x) = ∑_z M(x_p, z) X(x with p-part z)`, i.e. `unfold p (actOn p M X) =
  M * unfold p X`. Mode projectors, TT interface projectors and TTN subtree projectors are all of
  this form, which is what makes them commute when they act on disjoint sets of modes.

## Main definitions

* `LeanDLRA.Tensor ι`: real tensors with modes `κ` and mode index types `ι`.
* `Tensor.merge`, `Tensor.override`: assembling multi-indices from parts.
* `Tensor.unfold p X`, `Tensor.fold p A`: unfolding and its inverse.
* `Tensor.actOn p M`: the matrix `M` acting on the modes in `p`, as a continuous linear map.
* `Tensor.modeEquiv`, `Tensor.modeAct k A`, `Tensor.modeProj k U`: a matrix acting on mode `k`,
  and the mode-`k` projector `X ↦ X ×ₖ U Uᵀ`.
* `Tensor.restrictLE`: restriction of a partial multi-index to fewer modes.
* `Tensor.tucker C U`: the Tucker tensor `C ×₁ U₁ ⋯ ×_d U_d`.
* `Tensor.TTCores`, `Tensor.ttLeft`, `Tensor.ttRight`, `Tensor.tt`: tensor-train cores, the
  partial products `X_{≤k}`, `X_{>k}` (interface matrices) and the TT tensor `C₁(i₁) ⋯ C_d(i_d)`;
  `Tensor.prefixSuccEquiv`, `Tensor.suffixSuccEquiv` split interface multi-indices.
* `Tensor.IsLeftOrth`, `Tensor.IsRightOrth`: left- and right-orthogonality of a TT core.
* `Tensor.ttLeftProj`, `Tensor.ttRightProj`: the interface projectors `P_{≤k}`, `P_{>k}`.
* `Tensor.ttTangentSum`: the alternating sum of TT interface operators (any families).
* `Tensor.ttTangentProj`: the TT tangent projector
  `P_Y = ∑_{k=1}^{d} P_{≤k-1} P_{>k} - ∑_{k=1}^{d-1} P_{≤k} P_{>k}`.
* `LeanDLRA.DimTree κ`: dimension trees with leaves labelled by modes, with `DimTree.modes`,
  `DimTree.IsValid` and `DimTree.subtreeProj`.
* `LeanDLRA.TTN ι τ r`: tree tensor networks on a dimension tree (leaf bases and connecting
  tensors), with the nested basis matrices `TTN.basis`, orthonormality `TTN.IsOrthonormal` and
  the represented tensor `TTN.toTensor`.
* `LeanDLRA.modePrefix P k`: the ordered prefix product `P 0 * ⋯ * P (k - 1)` of mode operators on
  an abstract normed space (the full product is `LeanDLRA.modeProd`, `Integrators/TuckerBUG.lean`).
* `LeanDLRA.tuckerSqrtC₁`, `LeanDLRA.tuckerSqrtC₂`: the constants `√d (1 + L H e^{L H})` and
  `L B (4 √d + e^{L H} (1 + 4 √d L H))` of the `√d` local error bound of the Tucker BUG integrator.
* `LeanDLRA.TTNFrame E`: the abstract frame of one step of a tree tensor network integrator on a
  real inner product space `E` (old mode projectors, `K`-step projectors and admissible operator
  classes at every inner node), with `TTNFrame.height`, `TTNFrame.size`, the recursive local
  error bound `ttnErrBound`, and the (recursive) augmented recoverability conditions
  `IsAugRecoverable`, `IsTTNAugRecoverable`. The TTN step predicates on frames (`IsTTNBUGStep`,
  `IsAugTTNBUGStep`, `IsParTTNBUGStep`, `IsTTNRecoverable`) and the abstract `modeTangentProj`
  are in `Tensor/Steps.lean`: they use `modeProd`, `modeProdLeOne`, `parTuckerBUG` and
  `Exactness.IsRecoverable`, which are not yet in a `Defs.lean`.
* `LeanDLRA.TreeShape`: the shape of a dimension tree without mode labels (a leaf, or an inner
  node with `m` children), over which the recursive projector-splitting step `IsTTNKSLStep`
  (`Tensor/Steps.lean`) is defined; `DimTree.toTreeShape` (`Tensor/TTN/Integrators.lean`) forgets
  the labels of a dimension tree.
-/

open scoped Matrix RealInnerProductSpace

namespace LeanDLRA

/-- **Real tensors** with modes `κ` and index type `ι k` in mode `k`: functions of multi-indices
`x : ∀ k, ι k` with the Euclidean (Frobenius) inner product `⟪X, Y⟫ = ∑ₓ X(x) Y(x)`. -/
abbrev Tensor {κ : Type*} (ι : κ → Type*) : Type _ := EuclideanSpace ℝ (∀ k, ι k)

namespace Tensor

variable {κ : Type*} {ι : κ → Type*}

/-! ### Multi-indices -/

/-- The multi-index with `p`-part `a` and remaining part `b`. -/
def merge (p : κ → Prop) [DecidablePred p] (a : ∀ k : Subtype p, ι k)
    (b : ∀ k : {k // ¬ p k}, ι k) : ∀ k, ι k :=
  fun k => if h : p k then a ⟨k, h⟩ else b ⟨k, h⟩

/-- The multi-index `x` with its `p`-part replaced by `z`. -/
def override (p : κ → Prop) [DecidablePred p] (x : ∀ k, ι k) (z : ∀ k : Subtype p, ι k) :
    ∀ k, ι k :=
  fun k => if h : p k then z ⟨k, h⟩ else x k

/-- Restriction of a `q`-part to a smaller set `p` of modes (`p ≤ q`). -/
def restrictLE {p q : κ → Prop} (hpq : ∀ k, p k → q k) (y : ∀ k : Subtype q, ι k) :
    ∀ k : Subtype p, ι k :=
  fun k => y ⟨k.1, hpq k.1 k.2⟩

/-- Restricting the `q`-part of `x` further to `p` gives the `p`-part of `x`. -/
@[simp] lemma restrictLE_restrict {p q : κ → Prop} (hpq : ∀ k, p k → q k) (x : ∀ k, ι k) :
    restrictLE hpq (Subtype.restrict q x) = Subtype.restrict p x := rfl

section MultiIndex

variable (p : κ → Prop) [DecidablePred p]

/-- The `p`-part of `x` overridden by `z` is `z`. -/
@[simp] lemma restrict_override (x : ∀ k, ι k) (z : ∀ k : Subtype p, ι k) :
    Subtype.restrict p (override p x z) = z := by
  funext k; simp [override, Subtype.restrict, k.2]

/-- Overriding the `p`-part of `x` by itself gives `x`. -/
@[simp] lemma override_restrict (x : ∀ k, ι k) : override p x (Subtype.restrict p x) = x := by
  funext k; by_cases h : p k <;> simp [override, h, Subtype.restrict]

/-- Overriding the `p`-part twice keeps only the second override. -/
@[simp] lemma override_override (x : ∀ k, ι k) (z w : ∀ k : Subtype p, ι k) :
    override p (override p x z) w = override p x w := by
  funext k; by_cases h : p k <;> simp [override, h]

/-- The `p`-part of `merge p a b` is `a`. -/
@[simp] lemma restrict_merge (a : ∀ k : Subtype p, ι k) (b : ∀ k : {k // ¬ p k}, ι k) :
    Subtype.restrict p (merge p a b) = a := by
  funext k; simp [merge, Subtype.restrict, k.2]

/-- The part of `merge p a b` outside `p` is `b`. -/
@[simp] lemma restrict_not_merge (a : ∀ k : Subtype p, ι k) (b : ∀ k : {k // ¬ p k}, ι k) :
    Subtype.restrict (fun k => ¬ p k) (merge p a b) = b := by
  funext k; simp [merge, Subtype.restrict, k.2]

/-- A multi-index is the merge of its `p`-part and the rest. -/
@[simp] lemma merge_restrict (x : ∀ k, ι k) :
    merge p (Subtype.restrict p x) (Subtype.restrict (fun k => ¬ p k) x) = x := by
  funext k; by_cases h : p k <;> simp [merge, h, Subtype.restrict]

/-- Overriding the `p`-part is merging the new part with the old rest. -/
lemma override_eq_merge (x : ∀ k, ι k) (z : ∀ k : Subtype p, ι k) :
    override p x z = merge p z (Subtype.restrict (fun k => ¬ p k) x) := by
  funext k; by_cases h : p k <;> simp [merge, override, h, Subtype.restrict]

/-- Outside `p`, an overridden multi-index keeps its entries. -/
lemma override_apply_of_not {x : ∀ k, ι k} {z : ∀ k : Subtype p, ι k} {k : κ} (h : ¬ p k) :
    override p x z k = x k := by simp [override, h]

/-- On `p`, an overridden multi-index takes the new entries. -/
lemma override_apply_of {x : ∀ k, ι k} {z : ∀ k : Subtype p, ι k} {k : κ} (h : p k) :
    override p x z k = z ⟨k, h⟩ := by simp [override, h]

/-- The multi-indices with the same `p`-complement as `x` are exactly the `override p x z`. -/
lemma override_restrict_of_restrict_not_eq {x y : ∀ k, ι k}
    (h : Subtype.restrict (fun k => ¬ p k) y = Subtype.restrict (fun k => ¬ p k) x) :
    override p x (Subtype.restrict p y) = y := by
  funext k
  by_cases hk : p k
  · simp [override, hk, Subtype.restrict]
  · simp only [override, hk, dite_false]
    exact (congrFun h ⟨k, hk⟩).symm

variable {p}

/-- Overriding the `p`-part does not change the part on a disjoint set `q`. -/
lemma restrict_override_of_disjoint {q : κ → Prop} (hpq : ∀ k, p k → ¬ q k) (x : ∀ k, ι k)
    (z : ∀ k : Subtype p, ι k) :
    Subtype.restrict q (override p x z) = Subtype.restrict q x := by
  funext k
  have : ¬ p k.1 := fun h => hpq k.1 h k.2
  simp [Subtype.restrict, override, this]

/-- Overrides on disjoint sets of modes commute. -/
lemma override_comm_of_disjoint {q : κ → Prop} [DecidablePred q] (hpq : ∀ k, p k → ¬ q k)
    (x : ∀ k, ι k) (z : ∀ k : Subtype p, ι k) (w : ∀ k : Subtype q, ι k) :
    override q (override p x z) w = override p (override q x w) z := by
  funext k
  by_cases hp : p k
  · simp [override, hp, hpq k hp]
  · by_cases hq : q k <;> simp [override, hp, hq]

end MultiIndex

/-! ### Unfoldings and linear maps acting on a set of modes -/

variable [Fintype κ] [DecidableEq κ] [∀ k, Fintype (ι k)]

/-- The **unfolding** (matricization) of a tensor with respect to the set of modes `p`: rows are
indexed by the `p`-part of the multi-index, columns by the rest. For `p = {k}` this is the
mode-`k` matricization `Matₖ(X)`, for `p = {i | i < k}` in a tensor train the `k`-th unfolding
`X⟨k⟩`. -/
def unfold (p : κ → Prop) [DecidablePred p] (X : Tensor ι) :
    Matrix (∀ k : Subtype p, ι k) (∀ k : {k // ¬ p k}, ι k) ℝ :=
  Matrix.of fun a b => X (merge p a b)

/-- The **tensorization** `Ten_p`, inverse of `unfold p`. -/
def fold (p : κ → Prop) [DecidablePred p]
    (A : Matrix (∀ k : Subtype p, ι k) (∀ k : {k // ¬ p k}, ι k) ℝ) : Tensor ι :=
  WithLp.toLp 2 fun x => A (Subtype.restrict p x) (Subtype.restrict (fun k => ¬ p k) x)

/-- The matrix `M` **acting on the modes in `p`**:
`(actOn p M X)(x) = ∑_z M(x_p, z) X(x with p-part z)`, so that
`unfold p (actOn p M X) = M * unfold p X` (`unfold_actOn`). -/
noncomputable def actOn (p : κ → Prop) [DecidablePred p]
    (M : Matrix (∀ k : Subtype p, ι k) (∀ k : Subtype p, ι k) ℝ) : Tensor ι →L[ℝ] Tensor ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => WithLp.toLp 2 fun x =>
        ∑ z, M (Subtype.restrict p x) z * X (override p x z)
      map_add' := fun X Y => by
        ext x; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c X => by
        ext x; simp [Finset.mul_sum, mul_left_comm] }

/-- The entries of `actOn p M X`. -/
@[simp] lemma actOn_apply (p : κ → Prop) [DecidablePred p]
    (M : Matrix (∀ k : Subtype p, ι k) (∀ k : Subtype p, ι k) ℝ) (X : Tensor ι)
    (x : ∀ k, ι k) : actOn p M X x = ∑ z, M (Subtype.restrict p x) z * X (override p x z) :=
  rfl

/-- The multi-indices of the single mode `k` are the indices of mode `k`. -/
def modeEquiv (k : κ) : (∀ j : {j // j = k}, ι j) ≃ ι k where
  toFun z := z ⟨k, rfl⟩
  invFun c j := cast (congrArg ι j.2.symm) c
  left_inv z := by funext ⟨j, hj⟩; subst hj; rfl
  right_inv _ := rfl

/-- The matrix `A` acting on mode `k` only: `X ↦ X ×ₖ A`,
`(X ×ₖ A)(x) = ∑_c A(xₖ, c) X(x with xₖ replaced by c)`. -/
noncomputable def modeAct (k : κ) (A : Matrix (ι k) (ι k) ℝ) : Tensor ι →L[ℝ] Tensor ι :=
  actOn (· = k) (A.submatrix (modeEquiv k) (modeEquiv k))

/-- The **mode-`k` projector** `X ↦ X ×ₖ U Uᵀ` onto the tensors whose mode-`k` fibres lie in the
column space of `U` (an orthogonal projector when `Uᵀ U = 1`). -/
noncomputable def modeProj {r : Type*} [Fintype r] (k : κ) (U : Matrix (ι k) r ℝ) :
    Tensor ι →L[ℝ] Tensor ι :=
  modeAct k (U * Uᵀ)

/-- The **Tucker tensor** `C ×₁ U₁ ×₂ ⋯ ×_d U_d`,
`(C ×ₖ Uₖ)(x) = ∑_y (∏ₖ Uₖ(xₖ, yₖ)) C(y)`, with core `C` (mode sizes `ρ k`) and basis matrices
`U k : ι k × ρ k`. -/
def tucker {ρ : κ → Type*} [∀ k, Fintype (ρ k)] (C : Tensor ρ)
    (U : ∀ k, Matrix (ι k) (ρ k) ℝ) : Tensor ι :=
  WithLp.toLp 2 fun x => ∑ y, (∏ k, U k (x k) (y k)) * C y

end Tensor

/-! ### The alternating sum of interface operators -/

namespace Tensor

/-- The **alternating sum of interface operators** of a tensor train with `d` modes,
`∑_{k=1}^{d} P_{≤k-1} P_{>k} - ∑_{k=1}^{d-1} P_{≤k} P_{>k}`, for arbitrary families `Pl k`
(acting on the modes `< k`) and `Pr k` (acting on the modes `≥ k`). With the orthogonal
interface projectors it is the TT tangent projector (`ttTangentProj`), with oblique
(interpolatory) ones the oblique tangent projector of Dektor–Peng–Venturi (arXiv 2402.18721,
Eq. (24)). -/
noncomputable def ttTangentSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Pl Pr : ℕ → E →L[ℝ] E) (d : ℕ) : E →L[ℝ] E :=
  (∑ k ∈ Finset.range d, Pl k * Pr (k + 1)) -
    ∑ k ∈ Finset.range (d - 1), Pl (k + 1) * Pr (k + 1)

end Tensor

/-! ### Tensor trains -/

namespace Tensor

variable {d : ℕ} {ι : Fin d → Type*} {β : ℕ → Type*}

/-- **Tensor-train (TT / MPS) cores**: core `i` is a three-way array `Cᵢ(α, x, α')` with left bond
index `α : β i`, physical index `x : ι i` and right bond index `α' : β (i + 1)`. The ordinary TT
format has one-element boundary bond types `β 0` and `β d`. -/
abbrev TTCores (ι : Fin d → Type*) (β : ℕ → Type*) : Type _ :=
  ∀ i : Fin d, β i → ι i → β (i + 1) → ℝ

variable [∀ k, Fintype (β k)]

/-- The **left interface matrix** `X_{≤k}` (the partial product `C₁(i₁) ⋯ C_k(i_k)` as a matrix
with rows indexed by the first `k` physical indices and columns by the bond `β k`), defined by
`X_{≤0} = 1` and `X_{≤k+1}(y, α') = ∑_α X_{≤k}(y_{<k}, α) C_{k+1}(α, y_k, α')`. -/
def ttLeft (G : TTCores ι β) : (k : ℕ) → Matrix (∀ i : {i : Fin d // i.val < k}, ι i) (β k) ℝ
  | 0 => fun _ _ => 1
  | k + 1 => fun y b =>
      if h : k < d then
        ∑ a, ttLeft G k (restrictLE (fun i (hi : i.val < k) => Nat.lt_succ_of_lt hi) y) a *
          G ⟨k, h⟩ a (y ⟨⟨k, h⟩, Nat.lt_succ_self k⟩) b
      else 0

/-- The **right interface matrix** `X_{>k}` (the partial product `C_{k+1}(i_{k+1}) ⋯ C_d(i_d)`,
transposed, with rows indexed by the physical indices of the modes `k, …, d - 1` (in 0-based
numbering, the set `{i | ¬ i < k}`, so that `X⟨k⟩ = X_{≤k} X_{>k}ᵀ`) and columns by the bond
`β k`), defined by `X_{>d} = 1` and
`X_{>k}(y, α) = ∑_{α'} C_{k+1}(α, y_k, α') X_{>k+1}(y_{>k}, α')`. -/
def ttRight (G : TTCores ι β) (k : ℕ) :
    Matrix (∀ i : {i : Fin d // ¬ i.val < k}, ι i) (β k) ℝ := fun y a =>
  if h : k < d then
    ∑ b, G ⟨k, h⟩ a (y ⟨⟨k, h⟩, lt_irrefl k⟩) b *
      ttRight G (k + 1)
        (restrictLE (fun i (hi : ¬ i.val < k + 1) hk => hi (Nat.lt_succ_of_lt hk)) y) b
  else 1
termination_by d - k

/-- Splitting a multi-index of the first `k + 1` modes into one of the first `k` modes and the
index of mode `k`. -/
def prefixSuccEquiv (k : ℕ) (h : k < d) :
    (∀ i : {i : Fin d // i.val < k + 1}, ι i) ≃
      (∀ i : {i : Fin d // i.val < k}, ι i) × ι ⟨k, h⟩ where
  toFun y := (restrictLE (fun i (hi : i.val < k) => Nat.lt_succ_of_lt hi) y,
    y ⟨⟨k, h⟩, Nat.lt_succ_self k⟩)
  invFun yc i := if hi : i.1.val < k then yc.1 ⟨i.1, hi⟩ else
    cast (congrArg ι (Fin.ext (show k = i.1.val by have := i.2; omega))) yc.2
  left_inv y := by
    funext ⟨⟨j, hj⟩, hjk⟩
    by_cases hi : j < k
    · simp [hi, restrictLE]
    · have hjk' : j < k + 1 := hjk
      obtain rfl : j = k := by omega
      simp
  right_inv yc := by
    obtain ⟨y, c⟩ := yc
    ext i
    · simp [restrictLE, i.2]
    · simp

/-- Splitting a multi-index of the modes `k, …, d - 1` into the index of mode `k` and one of the
modes `k + 1, …, d - 1`. -/
def suffixSuccEquiv (k : ℕ) (h : k < d) :
    (∀ i : {i : Fin d // ¬ i.val < k}, ι i) ≃
      ι ⟨k, h⟩ × (∀ i : {i : Fin d // ¬ i.val < k + 1}, ι i) where
  toFun y := (y ⟨⟨k, h⟩, lt_irrefl k⟩,
    restrictLE (fun i (hi : ¬ i.val < k + 1) hk => hi (Nat.lt_succ_of_lt hk)) y)
  invFun cy i := if hi : i.1.val = k then cast (congrArg ι (Fin.ext hi.symm)) cy.1 else
    cy.2 ⟨i.1, by have := i.2; omega⟩
  left_inv y := by
    funext ⟨⟨j, hj⟩, hjk⟩
    by_cases hi : j = k
    · subst hi
      simp
    · simp [hi, restrictLE]
  right_inv cy := by
    obtain ⟨c, y⟩ := cy
    ext i
    · simp
    · have : i.1.val ≠ k := by have := i.2; omega
      simp [restrictLE, this]

variable [∀ i, Fintype (ι i)]

/-- The **tensor train** `Y(x) = C₁(x₁) C₂(x₂) ⋯ C_d(x_d)` with cores `G`, i.e. the sum of the
last left interface matrix over the final bond (one term in the ordinary TT format). -/
def tt (G : TTCores ι β) : Tensor ι :=
  WithLp.toLp 2 fun x => ∑ b, ttLeft G d (Subtype.restrict (fun i : Fin d => i.val < d) x) b

/-- Core `i` is **left-orthogonal**: its left unfolding `C^{<l>}` (rows `(α, x)`, columns `α'`)
has orthonormal columns, `∑_{α, x} Cᵢ(α, x, α') Cᵢ(α, x, α'') = δ_{α'α''}`. -/
def IsLeftOrth [∀ k, DecidableEq (β k)] (G : TTCores ι β) (i : Fin d) : Prop :=
  ∀ b b' : β (i + 1), ∑ a, ∑ x, G i a x b * G i a x b' = (1 : Matrix (β (i + 1)) _ ℝ) b b'

/-- Core `i` is **right-orthogonal**: its right unfolding `C^{<r>}` (rows `α`, columns `(x, α')`)
has orthonormal rows, `∑_{x, α'} Cᵢ(α, x, α') Cᵢ(α'', x, α') = δ_{αα''}`. -/
def IsRightOrth [∀ k, DecidableEq (β k)] (G : TTCores ι β) (i : Fin d) : Prop :=
  ∀ a a' : β i, ∑ x, ∑ b, G i a x b * G i a' x b = (1 : Matrix (β i) _ ℝ) a a'

/-- The **left interface projector** `P_{≤k} Z = Ten_k(X_{≤k} X_{≤k}ᵀ Z⟨k⟩)` of the cores `G`
(an orthogonal projector when the first `k` cores are left-orthogonal). -/
noncomputable def ttLeftProj (G : TTCores ι β) (k : ℕ) : Tensor ι →L[ℝ] Tensor ι :=
  actOn (fun i : Fin d => i.val < k) (ttLeft G k * (ttLeft G k)ᵀ)

/-- The **right interface projector** `P_{>k} Z = Ten_k(Z⟨k⟩ X_{>k} X_{>k}ᵀ)` of the cores `G`
(an orthogonal projector when the cores `k + 1, …, d` are right-orthogonal). -/
noncomputable def ttRightProj (G : TTCores ι β) (k : ℕ) : Tensor ι →L[ℝ] Tensor ι :=
  actOn (fun i : Fin d => ¬ i.val < k) (ttRight G k * (ttRight G k)ᵀ)

/-- The **TT tangent projector** (Lubich–Oseledets–Vandereycken, arXiv 1407.2042, Thm 3.1 and
Cor. 3.2) at a tensor train with left-orthogonal cores `A` and right-orthogonal cores `B`:
`P_Y = ∑_{k=1}^{d} P_{≤k-1} P_{>k} - ∑_{k=1}^{d-1} P_{≤k} P_{>k}` with `P_{≤0} = P_{>d} = 1`. -/
noncomputable def ttTangentProj (A B : TTCores ι β) : Tensor ι →L[ℝ] Tensor ι :=
  ttTangentSum (ttLeftProj A) (ttRightProj B) d

end Tensor

/-! ### Dimension trees -/

/-- A **dimension tree** whose leaves are labelled by modes `κ`: a leaf is one physical mode, an
inner node has `m` subtrees (Ceruti–Lubich–Walach, arXiv 2002.11392, Def. 2.1). A tensor train
with `d` modes corresponds to a comb (each inner node has a leaf and one inner subtree), a Tucker
tensor to a single inner node with `d` leaves. -/
inductive DimTree (κ : Type*) : Type _
  | leaf (k : κ) : DimTree κ
  | node {m : ℕ} (cs : Fin m → DimTree κ) : DimTree κ

namespace DimTree

variable {κ : Type*} [DecidableEq κ]

/-- The set of modes (leaves) of a dimension tree. -/
def modes : DimTree κ → Finset κ
  | leaf k => {k}
  | node cs => Finset.univ.biUnion fun i => (cs i).modes

/-- A dimension tree is **valid** when the mode sets of the subtrees of every inner node are
pairwise disjoint (every mode is a leaf at most once). -/
def IsValid : DimTree κ → Prop
  | leaf _ => True
  | node cs => (∀ i, (cs i).IsValid) ∧ Pairwise fun i j => Disjoint (cs i).modes (cs j).modes

/-- A mode of a subtree is a mode of the node. -/
theorem mem_modes_node {m : ℕ} {cs : Fin m → DimTree κ} {k : κ} (i : Fin m)
    (hk : k ∈ (cs i).modes) : k ∈ (node cs).modes :=
  Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, hk⟩

/-- The orthogonal **subtree projector** `Z ↦ Ten_τ(U_τ U_τᵀ Mat_τ(Z))` of a subtree `τ` with
basis matrix `U` (rows indexed by the modes of `τ`). -/
noncomputable def subtreeProj [Fintype κ] {ι : κ → Type*} [∀ k, Fintype (ι k)] (τ : DimTree κ)
    {r : Type*} [Fintype r] (U : Matrix (∀ k : {k // k ∈ τ.modes}, ι k) r ℝ) :
    Tensor ι →L[ℝ] Tensor ι :=
  Tensor.actOn (· ∈ τ.modes) (U * Uᵀ)

end DimTree

/-! ### Tree tensor networks -/

universe u v

/-- A **tree tensor network** on the dimension tree `τ` with rank `r` at the root
(Ceruti–Lubich–Walach, arXiv 2002.11392, Def. 2.2). A leaf `k` carries a basis matrix
`U : ι k × Fin r`; an inner node with subtrees `cs i` carries tree tensor networks `ds i` of ranks
`rs i` on the subtrees and a connecting tensor, stored as its matricization in the root
dimension, `Mat₀(C) : Fin r × ∏ᵢ Fin (rs i)`. -/
inductive TTN {κ : Type u} (ι : κ → Type v) : DimTree κ → ℕ → Type (max u v)
  | leaf {k : κ} {r : ℕ} (U : Matrix (ι k) (Fin r) ℝ) : TTN ι (.leaf k) r
  | node {m : ℕ} {cs : Fin m → DimTree κ} {rs : Fin m → ℕ} {r : ℕ}
      (ds : ∀ i, TTN ι (cs i) (rs i)) (C : Matrix (Fin r) (∀ i, Fin (rs i)) ℝ) :
      TTN ι (.node cs) r

namespace TTN

variable {κ : Type u} [DecidableEq κ] {ι : κ → Type v}

/-- The **basis matrix** `U_τ` of a tree tensor network (rows indexed by the modes of `τ`,
columns by the rank): `U_ℓ = U` at a leaf and, at an inner node,
`U_τ(x, a) = ∑_b C(a, b) ∏ᵢ U_{τᵢ}(x_{τᵢ}, bᵢ)`, i.e. `U_τᵀ = Mat₀(C ×ᵢ U_{τᵢ})`
(arXiv 2002.11392, Eq. (2.3)). -/
noncomputable def basis :
    {τ : DimTree κ} → {r : ℕ} → TTN ι τ r → Matrix (∀ k : {k // k ∈ τ.modes}, ι k) (Fin r) ℝ
  | .leaf k, _, .leaf U => fun x a => U (x ⟨k, Finset.mem_singleton_self k⟩) a
  | .node _, _, .node ds C => fun x a =>
      ∑ b, C a b * ∏ i, (ds i).basis (fun k => x ⟨k.1, DimTree.mem_modes_node i k.2⟩) (b i)

/-- A tree tensor network is **orthonormal** when every leaf basis has orthonormal columns and
every connecting tensor has orthonormal rows of its root matricization, `Mat₀(C) Mat₀(C)ᵀ = 1`
(arXiv 2002.11392, Def. 2.4). -/
def IsOrthonormal [∀ k, Fintype (ι k)] : {τ : DimTree κ} → {r : ℕ} → TTN ι τ r → Prop
  | .leaf _, _, .leaf U => Uᵀ * U = 1
  | .node _, _, .node ds C => (∀ i, (ds i).IsOrthonormal) ∧ C * Cᵀ = 1

/-- The tensor represented by a tree tensor network of root rank one:
`Y(x) = U_τ(x_τ, 0)`. -/
noncomputable def toTensor {τ : DimTree κ} (t : TTN ι τ 1) : Tensor ι :=
  WithLp.toLp 2 fun x => t.basis (fun k => x k.1) 0

end TTN

/-! ### Products of mode operators and constants of the Tucker BUG bounds -/

section ModeOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The prefix product `P 0 * P 1 * ⋯ * P (k - 1)` of the first `k` mode operators (the full
product `LeanDLRA.modeProd P` when `d ≤ k`). -/
def modePrefix {d : ℕ} (P : Fin d → E →L[ℝ] E) (k : ℕ) : E →L[ℝ] E :=
  ((List.ofFn P).take k).prod

end ModeOperators

section TuckerConstants

/-- The improved constant `c₁ = √d (1 + L H e^{L H})` in front of `ε` in the local error bound of
the Tucker BUG integrator with `d` modes (step sizes `h ≤ H`). -/
noncomputable def tuckerSqrtC₁ (d : ℕ) (L H : ℝ) : ℝ :=
  √(d : ℝ) * (1 + L * H * Real.exp (L * H))

/-- The improved constant `c₂ = L B (4 √d + e^{L H} (1 + 4 √d L H))` in front of `h` in the local
error bound of the Tucker BUG integrator with `d` modes (step sizes `h ≤ H`). -/
noncomputable def tuckerSqrtC₂ (d : ℕ) (L B H : ℝ) : ℝ :=
  L * B * (4 * √(d : ℝ) + Real.exp (L * H) * (1 + 4 * √(d : ℝ) * L * H))

end TuckerConstants

/-! ### Frames of tree tensor network steps -/

/-- The **frame of a tree tensor network step**: a rooted tree whose inner nodes carry the data
determined by the old approximation `Y₀`.  An inner node with `m` children carries, for each child
`i : Fin m`, the old mode projector `P₀ i = U⁰ᵢU⁰ᵢᵀ` (onto the old basis of mode `i` of the
connecting tensor), the co-range projector `Q₀ i` of the `i`-th matricization of `Y₀` (the
`K`-step projector), a class `𝓛 i` of admissible mode-`i` operators (the operators acting on
mode `i` only; used for exactness, see `Exactness.IsRecoverable`) and the frame of the subtree
`i`.  A leaf is a physical mode whose basis matrix is integrated without approximation. -/
inductive TTNFrame (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Type u
  | leaf : TTNFrame E
  | node (m : ℕ) (P₀ Q₀ : Fin m → E →L[ℝ] E) (𝓛 : Fin m → Set (E →L[ℝ] E))
      (cs : Fin m → TTNFrame E) : TTNFrame E

namespace TTNFrame

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The height of the tree (`0` for a leaf, `1` for a Tucker tensor, `d - 1` for a tensor train
with `d` cores). -/
def height : TTNFrame E → ℕ
  | .leaf => 0
  | .node _ _ _ _ cs => (Finset.univ.sup fun i => (cs i).height) + 1

/-- The number of nodes of the tree (leaves included). -/
def size : TTNFrame E → ℕ
  | .leaf => 1
  | .node _ _ _ _ cs => 1 + ∑ i, (cs i).size

end TTNFrame

section Frame

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **recursive local error bound** of the TTN BUG integrator for a step of length `h`: `0` at
a leaf; at an inner node, with the child bounds `ηᵢ`, the capture defects
`θᵢ = h (4 L B h + L ηᵢ + ε) + ηᵢ` (capture with an inexact `K`-step, `kstep_capture_inexact`),
`Θ = ∑ᵢ θᵢ` (telescoping) and the Galerkin bound `(e^{L h} - 1)(B h + Θ) + Θ`. -/
noncomputable def ttnErrBound (L B ε h : ℝ) : TTNFrame E → ℝ
  | .leaf => 0
  | .node _ _ _ _ cs =>
      (Real.exp (L * h) - 1) *
          (B * h + ∑ i, (h * (4 * L * B * h + L * ttnErrBound L B ε h (cs i) + ε) +
            ttnErrBound L B ε h (cs i))) +
        ∑ i, (h * (4 * L * B * h + L * ttnErrBound L B ε h (cs i) + ε) +
          ttnErrBound L B ε h (cs i))

/-- **Augmented recoverability** of `x` from `Q x` and the old basis `P₀` modulo the class `𝓛`:
`x = T (Q x) + S (P₀ z)` for some `z` and maps `T`, `S` commuting with every operator of `𝓛`.
For matrices (`𝓛` the left multiplications, `T`, `S` right multiplications) this says
`col(A₁) ⊆ col(A₁ V₀) + col(U₀)`, which is implied by `Exactness.IsRecoverable` (`S = 0`) but
also holds e.g. for `A(t) = e₂ v(t)ᵀ`, `v(t₁) ⊥ v(t₀)`, `U₀ = e₂` (the counterexample of
OP-TN-05, where the non-augmented integrator fails). -/
def IsAugRecoverable (𝓛 : Set (E →L[ℝ] E)) (P₀ Q : E →L[ℝ] E) (x : E) : Prop :=
  ∃ T S : E →L[ℝ] E, (∀ L ∈ 𝓛, ∀ y, L (T y) = T (L y)) ∧ (∀ L ∈ 𝓛, ∀ y, L (S y) = S (L y)) ∧
    ∃ z, x = T (Q x) + S (P₀ z)

/-- Recursive augmented recoverability along a frame (see `IsAugRecoverable`). -/
def IsTTNAugRecoverable : TTNFrame E → E → Prop
  | .leaf, _ => True
  | .node _ P₀ Q₀ 𝓛 cs, x => ∀ i, IsAugRecoverable (𝓛 i) (P₀ i) (Q₀ i) x ∧
      IsTTNAugRecoverable (cs i) (Q₀ i x)

end Frame

/-! ### Shapes of dimension trees -/

/-- The shape of a dimension tree: a leaf (a physical mode, integrated exactly) or an inner node
with `m` children. -/
inductive TreeShape : Type
  | leaf : TreeShape
  | node (m : ℕ) (cs : Fin m → TreeShape) : TreeShape

/-- A tree shape: the root with two leaves (the shape of the matrix case). -/
example : TreeShape := .node 2 fun _ => .leaf

end LeanDLRA
