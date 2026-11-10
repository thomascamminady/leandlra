import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Classical.CommutingProjectorTelescoping
import LeanDLRA.Tensor.Defs

/-!
# Definitions for TensorNetworks

Local definitions used by the theorems of the corresponding modules. The frames `TTNFrame`, the
bound `ttnErrBound` and the augmented recoverability `IsAugRecoverable`, `IsTTNAugRecoverable`
are defined in `LeanDLRA/Tensor/Defs.lean`.
-/

open Set Finset
open scoped RealInnerProductSpace

universe u

namespace LeanDLRA

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
noncomputable def tuckerTangentProj {d : ℕ} (P₀ Q₀ : Fin d → E →L[ℝ] E) : E →L[ℝ] E :=
  modeProd P₀ + ∑ i, (1 - P₀ i) * Q₀ i

section Inexact

variable {F : ℝ → E → E} {L B ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

end Inexact

section TTN

variable {G : ℝ → E → E} {L B ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

end TTN

section TTNGlobal

variable {F : ℝ → E → E} {L B ε : ℝ}

end TTNGlobal

section Exact

variable {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ}

end Exact

section AugTTN

variable {G : ℝ → E → E} {L B ε ϑ : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

end AugTTN

section AugTTNGlobal

variable {F : ℝ → E → E} {L B ε ϑ : ℝ}

end AugTTNGlobal

section ParTTN

variable {G : ℝ → E → E} {L B Lt ε ϑ : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

end ParTTN

section ParTTNGlobal

variable {F : ℝ → E → E} {L B Lt ε ϑ : ℝ}

end ParTTNGlobal

section DIndependent

variable {F : ℝ → E → E} {L B ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

end DIndependent

end LeanDLRA
