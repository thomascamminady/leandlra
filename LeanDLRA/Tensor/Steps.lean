import LeanDLRA.Tensor.Defs
import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Integrators.Exactness

/-!
# Step predicates of the Tucker and tree tensor network integrators

One step of each recursive tensor integrator of the library is a predicate on an abstract real
inner product space `E`, with the projectors of the modes given as continuous linear maps. The
instances on tensors `Tensor ι` over a dimension tree are in `Tensor/TTN/`.

## Main definitions

* `kslModeField`, `IsTuckerKSLStep`, `IsExactKSteps`: the nested Tucker projector-splitting
  integrator (Lubich–Vandereycken–Walach, arXiv 1709.02594, §4): the field of the `K`-substep of
  a mode, one step with given `K`-values, and the condition that the `K`-values are the exact
  substep values.
* `IsTTNKSLStep`: one step of the recursive TTN projector-splitting integrator
  (Ceruti–Lubich–Walach, arXiv 2002.11392, §4) over a `TreeShape`.
* `IsTTNBUGStep`, `IsAugTTNBUGStep`, `IsParTTNBUGStep`: one step of the fixed-rank, the
  rank-adaptive and the parallel TTN BUG integrator over a `TTNFrame` (Ceruti–Lubich–Sulz,
  SINUM 2023; arXiv 2412.00858, §4).
* `IsTTNRecoverable`: recursive recoverability along a frame.
* `modeTangentProj`: the tangent projector of the Tucker manifold in terms of abstract mode
  projectors, `∏ᵢ P₀ i + ∑ᵢ (1 - P₀ i) Q₀ i`.

These definitions are not in `Tensor/Defs.lean` because they use `modeProd`, `modeProdLeOne`,
`parTuckerBUG` (`Integrators/TuckerBUG.lean`) and `Exactness.IsRecoverable`
(`Integrators/Exactness.lean`), which are declared in files with theorems. `TreeShape`, `TTNFrame`
and `modePrefix` are in `Tensor/Defs.lean`.
-/

open Set Finset
open scoped RealInnerProductSpace

universe u

namespace LeanDLRA

/-! ### The nested Tucker projector-splitting integrator -/

section NestedKSL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The field of the mode-`i` `K`-substep of the nested Tucker projector-splitting integrator:
`x ↦ Q₀ i (P₁ 0 ⋯ P₁ (i-1)) F(t, x)`, i.e. the `K`-step projector of mode `i` applied to the
field already projected onto the new bases of the modes `< i`. -/
def kslModeField {d : ℕ} (Q₀ P₁ : Fin d → E →L[ℝ] E) (F : ℝ → E → E) (i : Fin d) :
    ℝ → E → E :=
  fun t x => Q₀ i (modePrefix P₁ (i : ℕ) (F t x))

/-- One step of the **nested Tucker projector-splitting integrator** (Lubich–Vandereycken–Walach,
arXiv 1709.02594, §4) from `(t₀, Y₀)` to `(t₁, YC t₁)`, with the `K`-values `K i` *given* (exact
or computed by a sub-integrator).  The modes are processed in the order `0, …, d-1`; `X i` is the
state before mode `i` (`X 0 = Y₀`):

* `Q₀ i` is the co-range projector of the mode-`i` matricization of `X i` (`Q₀ i (X i) = X i`);
* the new mode basis `P₁ i` captures the mode-`i` `K`-value, with doubly-normal component of the
  mode field at most `ε` there;
* the backward `S`-step `YS' = -P₁ i Q₀ i Π_{<i} F(t, YS)` runs from `K i` and produces `X (i+1)`;
* the final core step is the Galerkin step `YC' = (∏ P₁ i) F(t, YC)` from `X d`. -/
structure IsTuckerKSLStep (F : ℝ → E → E) (ε : ℝ) {d : ℕ} (Q₀ P₁ : Fin d → E →L[ℝ] E)
    (t₀ t₁ : ℝ) (Y₀ : E) (X : Fin (d + 1) → E) (K : Fin d → E) (YS : Fin d → ℝ → E)
    (YC : ℝ → E) : Prop where
  projQ₀ : ∀ i, IsOrthProj (Q₀ i)
  projP₁ : ∀ i, IsOrthProj (P₁ i)
  comm₁ : ∀ i j x, P₁ i (P₁ j x) = P₁ j (P₁ i x)
  start : X 0 = Y₀
  qFix : ∀ i, Q₀ i (X i.castSucc) = X i.castSucc
  kCap : ∀ i, P₁ i (K i) = K i
  kNormal : ∀ i, ∀ t ∈ Icc t₀ t₁,
    ‖(1 - P₁ i) ((1 - Q₀ i) (modePrefix P₁ (i : ℕ) (F t (K i))))‖ ≤ ε
  sSol : ∀ i, ODESolution (fun t x => -(P₁ i (Q₀ i (modePrefix P₁ (i : ℕ) (F t x)))))
    (YS i) t₀ t₁
  sStart : ∀ i, YS i t₀ = K i
  next : ∀ i, X i.succ = YS i t₁
  cSol : ODESolution (fun t x => modeProd P₁ (F t x)) YC t₀ t₁
  cStart : YC t₀ = X (Fin.last d)

/-- The `K`-values of a nested Tucker KSL step are the **exact** `K`-substep values: `K i` is the
value at `t₁` of the mode-`i` `K`-step trajectory started at `X i`. -/
def IsExactKSteps {d : ℕ} (F : ℝ → E → E) (Q₀ P₁ : Fin d → E →L[ℝ] E) (t₀ t₁ : ℝ)
    (X : Fin (d + 1) → E) (K : Fin d → E) : Prop :=
  ∀ i, ∃ y : ℝ → E, ODESolution (kslModeField Q₀ P₁ F i) y t₀ t₁ ∧ y t₀ = X i.castSucc ∧
    y t₁ = K i

/-- The structure `IsTuckerKSLStep` is inhabited: for the zero field and identity projectors the
constant trajectories at an arbitrary `Y₀` form a step with defect bound `0`, for every number of
modes. -/
example {d : ℕ} (Y₀ : E) (t₀ t₁ : ℝ) :
    IsTuckerKSLStep (fun _ _ => (0 : E)) 0 (fun _ : Fin d => (1 : E →L[ℝ] E)) (fun _ => 1)
      t₀ t₁ Y₀ (fun _ => Y₀) (fun _ => Y₀) (fun _ _ => Y₀) (fun _ => Y₀) where
  projQ₀ _ := IsOrthProj.one
  projP₁ _ := IsOrthProj.one
  comm₁ _ _ _ := rfl
  start := rfl
  qFix _ := by simp
  kCap _ := by simp
  kNormal _ _ _ := by simp
  sSol _ := ⟨continuousOn_const, fun t _ =>
    (hasDerivWithinAt_const t _ Y₀).congr_deriv (by simp)⟩
  sStart _ := rfl
  next _ := rfl
  cSol := ⟨continuousOn_const, fun t _ =>
    (hasDerivWithinAt_const t _ Y₀).congr_deriv (by simp)⟩
  cStart := rfl

end NestedKSL

/-! ### The recursive TTN projector-splitting integrator -/

section TTNKSL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One step of the **recursive TTN projector-splitting integrator** (Ceruti–Lubich–Walach,
arXiv 2002.11392, §4; for comb trees the TT/MPS integrator of Lubich–Oseledets–Vandereycken,
arXiv 1407.2042) with tree shape `τ`, field `F` and doubly-normal bound `ε`, from `(t₀, Y₀)` to
`(t₁, Y₁)`: exact flow at a leaf; at an inner node a nested Tucker KSL step (`IsTuckerKSLStep`)
whose `K`-values are computed by the same integrator applied to the subtree problems (fields
`kslModeField Q₀ P₁ F i`, started at `X i`). -/
def IsTTNKSLStep : TreeShape → (ℝ → E → E) → ℝ → ℝ → ℝ → E → E → Prop
  | .leaf, F, _, t₀, t₁, Y₀, Y₁ => ∃ y : ℝ → E, ODESolution F y t₀ t₁ ∧ y t₀ = Y₀ ∧ y t₁ = Y₁
  | .node m cs, F, ε, t₀, t₁, Y₀, Y₁ =>
      ∃ (Q₀ P₁ : Fin m → E →L[ℝ] E) (X : Fin (m + 1) → E) (K : Fin m → E)
        (YS : Fin m → ℝ → E) (YC : ℝ → E),
        IsTuckerKSLStep F ε Q₀ P₁ t₀ t₁ Y₀ X K YS YC ∧
        (∀ i, IsTTNKSLStep (cs i) (kslModeField Q₀ P₁ F i) ε t₀ t₁ (X i.castSucc) (K i)) ∧
        YC t₁ = Y₁

end TTNKSL

/-! ### The TTN BUG integrators on frames -/

section TTNBUG

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One step of the **(fixed-rank) TTN BUG integrator** (the rank-adaptive TTN integrator of
Ceruti–Lubich–Sulz, SINUM 2023, without augmentation and truncation; recursive structure of the
projector-splitting TTN integrator of Ceruti–Lubich–Walach, arXiv 2002.11392, §4) for the field `G`
from `(t₀, Y₀)` to `(t₁, Y₁)` with frame `fr` and doubly-normal bound `ε`, as a recursive predicate:

* at a **leaf** the step is the exact flow of `G`;
* at an **inner node** with old projectors `P₀ i`, `Q₀ i` (which fix `Y₀`), there are new mode
  projectors `P₁ i ∈ 𝓛 i` (orthogonal, commuting), computed subtree results `K i` (a TTN step of
  the subtree `i` for the `K`-step field `Q₀ i G` from `Y₀`), captured by the new bases,
  `P₁ i (K i) = K i`, with doubly-normal component at most `ε` at `K i`, and the Galerkin
  core step `YS' = (∏ P₁ i) G(t, YS)`, `YS t₀ = (∏ P₁ i) Y₀`, `Y₁ = YS t₁`. -/
def IsTTNBUGStep : TTNFrame E → (ℝ → E → E) → ℝ → ℝ → ℝ → E → E → Prop
  | .leaf, G, _, t₀, t₁, Y₀, Y₁ => ∃ y : ℝ → E, ODESolution G y t₀ t₁ ∧ y t₀ = Y₀ ∧ y t₁ = Y₁
  | .node m P₀ Q₀ 𝓛 cs, G, ε, t₀, t₁, Y₀, Y₁ =>
      (∀ i, IsOrthProj (P₀ i)) ∧ (∀ i, IsOrthProj (Q₀ i)) ∧ (∀ i, P₀ i Y₀ = Y₀) ∧
      (∀ i, Q₀ i Y₀ = Y₀) ∧
      ∃ (P₁ : Fin m → E →L[ℝ] E) (K : Fin m → E) (YS : ℝ → E),
        (∀ i, IsOrthProj (P₁ i)) ∧ (∀ i, P₁ i ∈ 𝓛 i) ∧
        (∀ i j x, P₁ i (P₁ j x) = P₁ j (P₁ i x)) ∧
        (∀ i, IsTTNBUGStep (cs i) (fun t x => Q₀ i (G t x)) ε t₀ t₁ Y₀ (K i)) ∧
        (∀ i, P₁ i (K i) = K i) ∧
        (∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁ i) ((1 - Q₀ i) (G t (K i)))‖ ≤ ε) ∧
        ODESolution (fun t x => modeProd P₁ (G t x)) YS t₀ t₁ ∧
        YS t₀ = modeProd P₁ Y₀ ∧ YS t₁ = Y₁

/-- One step of the **rank-adaptive TTN BUG integrator** (Ceruti–Lubich–Sulz, *Rank-adaptive time
integration of tree tensor networks*, SINUM 2023, Algorithms 4–6) with truncation tolerance `ϑ`
at every inner node: as `IsTTNBUGStep`, but the new bases contain the old ones
(`P₁ i P₀ i = P₀ i`, the QR of `(K i, U⁰ᵢ)`), the subtree steps are again rank-adaptive, the
Galerkin step starts at `Y₀` itself, and the result `Y₁` is any truncation of the Galerkin result
with `‖Y₁ - YS t₁‖ ≤ ϑ`. -/
def IsAugTTNBUGStep : TTNFrame E → (ℝ → E → E) → ℝ → ℝ → ℝ → ℝ → E → E → Prop
  | .leaf, G, _, _, t₀, t₁, Y₀, Y₁ =>
      ∃ y : ℝ → E, ODESolution G y t₀ t₁ ∧ y t₀ = Y₀ ∧ y t₁ = Y₁
  | .node m P₀ Q₀ 𝓛 cs, G, ε, ϑ, t₀, t₁, Y₀, Y₁ =>
      (∀ i, IsOrthProj (P₀ i)) ∧ (∀ i, IsOrthProj (Q₀ i)) ∧ (∀ i, P₀ i Y₀ = Y₀) ∧
      (∀ i, Q₀ i Y₀ = Y₀) ∧
      ∃ (P₁ : Fin m → E →L[ℝ] E) (K : Fin m → E) (YS : ℝ → E),
        (∀ i, IsOrthProj (P₁ i)) ∧ (∀ i, P₁ i ∈ 𝓛 i) ∧
        (∀ i j x, P₁ i (P₁ j x) = P₁ j (P₁ i x)) ∧
        (∀ i x, P₁ i (P₀ i x) = P₀ i x) ∧
        (∀ i, IsAugTTNBUGStep (cs i) (fun t x => Q₀ i (G t x)) ε ϑ t₀ t₁ Y₀ (K i)) ∧
        (∀ i, P₁ i (K i) = K i) ∧
        (∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁ i) ((1 - Q₀ i) (G t (K i)))‖ ≤ ε) ∧
        ODESolution (fun t x => modeProd P₁ (G t x)) YS t₀ t₁ ∧
        YS t₀ = Y₀ ∧ ‖Y₁ - YS t₁‖ ≤ ϑ

/-- One step of the **parallel TTN BUG integrator** (Ceruti–Kusch–Lubich–Sulz, arXiv 2412.00858,
§4, Algorithms 3–4) with truncation tolerance `ϑ` at every inner node.  At an inner node: new
directions `Pa i` orthogonal to the old bases (`P₀ i Pa i = 0`; all projectors commute), the
subtree steps (again parallel) for the `K`-step fields give `K i`, captured by the augmented bases
`P₀ i + Pa i` with doubly-normal component `≤ ε`; the core step `YC' = (∏ P₀ i) G(t, YC)` in the
*old* bases runs in parallel from `YC t₀ = Y₀`; the normal component of `G(t₀, Y₀)` with respect
to the tangent hull is `≤ ε` (as `IsParTuckerBUGStep.normal₀`); and `Y₁` is a truncation of the
assembled augmented tensor `parTuckerBUG P₀ Pa (YC t₁) (t₁ - t₀) (G t₀ Y₀)` up to `ϑ`. -/
def IsParTTNBUGStep : TTNFrame E → (ℝ → E → E) → ℝ → ℝ → ℝ → ℝ → E → E → Prop
  | .leaf, G, _, _, t₀, t₁, Y₀, Y₁ =>
      ∃ y : ℝ → E, ODESolution G y t₀ t₁ ∧ y t₀ = Y₀ ∧ y t₁ = Y₁
  | .node m P₀ Q₀ _ cs, G, ε, ϑ, t₀, t₁, Y₀, Y₁ =>
      (∀ i, IsOrthProj (P₀ i)) ∧ (∀ i, IsOrthProj (Q₀ i)) ∧ (∀ i, P₀ i Y₀ = Y₀) ∧
      (∀ i, Q₀ i Y₀ = Y₀) ∧
      ∃ (Pa : Fin m → E →L[ℝ] E) (K : Fin m → E) (YC : ℝ → E),
        (∀ i, IsOrthProj (Pa i)) ∧ (∀ i x, P₀ i (Pa i x) = 0) ∧
        (∀ i j x, P₀ i (P₀ j x) = P₀ j (P₀ i x)) ∧
        (∀ i j x, P₀ i (Pa j x) = Pa j (P₀ i x)) ∧
        (∀ i j x, Pa i (Pa j x) = Pa j (Pa i x)) ∧
        (∀ i, IsParTTNBUGStep (cs i) (fun t x => Q₀ i (G t x)) ε ϑ t₀ t₁ Y₀ (K i)) ∧
        (∀ i, (P₀ i + Pa i) (K i) = K i) ∧
        (∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - (P₀ i + Pa i)) ((1 - Q₀ i) (G t (K i)))‖ ≤ ε) ∧
        ODESolution (fun t x => modeProd P₀ (G t x)) YC t₀ t₁ ∧ YC t₀ = Y₀ ∧
        ‖G t₀ Y₀ - modeProdLeOne P₀ (fun i => 1 - P₀ i) (G t₀ Y₀)‖ ≤ ε ∧
        ‖Y₁ - parTuckerBUG P₀ Pa (YC t₁) (t₁ - t₀) (G t₀ Y₀)‖ ≤ ϑ

/-- **Recursive recoverability** of `x` along a frame: at every inner node, `x` is recoverable
from its `K`-step projection `Q₀ i x` modulo the mode class `𝓛 i` (`Exactness.IsRecoverable`,
the abstract form of the overlap condition `Uᵢ(t₁)ᵀUᵢ(t₀)` invertible), and recursively so for
`Q₀ i x` along the subtree.  This is the abstract analogue of condition (5.2) of CLW Thm 5.1. -/
def IsTTNRecoverable : TTNFrame E → E → Prop
  | .leaf, _ => True
  | .node _ _ Q₀ 𝓛 cs, x => ∀ i, Exactness.IsRecoverable (𝓛 i) (Q₀ i) x ∧
      IsTTNRecoverable (cs i) (Q₀ i x)

/-- The **tangent projector of the Tucker manifold** at `Y₀ = C ×ᵢ U⁰ᵢ`:
`T = ∏ᵢ P₀ i + ∑ᵢ (1 - P₀ i) Q₀ i`.  The first term is the core variation `δC ×ᵢ U⁰ᵢ`, the
`i`-th summand the basis variation `C ×ᵢ δUᵢ ×_{j ≠ i} U⁰ⱼ` (`δUᵢ ⊥ U⁰ᵢ`, row space of the `i`-th
matricization in the co-range of `Matᵢ(Y₀)`).  Unlike the tangent hull
`modeProdLeOne P₀ (1 - P₀)` it is the exact tangent projector also for `d ≥ 3`. -/
noncomputable def modeTangentProj {d : ℕ} (P₀ Q₀ : Fin d → E →L[ℝ] E) : E →L[ℝ] E :=
  modeProd P₀ + ∑ i, (1 - P₀ i) * Q₀ i

end TTNBUG

end LeanDLRA
