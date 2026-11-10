import LeanDLRA.LinearAlgebra.Projection.Defs

/-!
# Dynamical low-rank training: definitions

The vocabulary of the training layer: optimisation steps of dynamical low-rank training (DLRT) on
an abstract real inner product space `E` with a loss `ℒ : E → ℝ` and its gradient `g = ∇ℒ`, the
preconditioner of factor-wise (LoRA) gradient descent on `W = U S Vᵀ`, and the tests used by
inexact line searches. The theorems about these objects are in `Training/Descent.lean`,
`Training/FactorizedDynamics.lean`, `Training/InexactGradient.lean` and
`OpenProblems/Curated/Training*.lean`.

## Main definitions

* `projGradStep P g h x = x - h • P (g x)`: the projected (Galerkin) gradient step.
* `geoLoRADir`, `geoLoRAStep`, `IsGeoLoRABases`: the GeoLoRA update direction, the GeoLoRA
  iterate before truncation and the relations between its bases (arXiv 2410.18720).
* `fedClientIter`, `fedRound`, `fedDrift`: variance-corrected client iterates, one round and the
  averaged drift of federated DLRT (FeDLRT, arXiv 2406.17887); `fedAvgClientIter`, `fedAvgRound`:
  the uncorrected (FedAvg-type) iterates and round.
* `FactorizedDynamics.loraPrecond U S V`: the operator `P̂` with `Ẇ = -P̂ ∇ℒ(W)` for simultaneous
  gradient flow in the factors `(U, S, V)`.
* `InexactGradient.ArmijoTest`: the inexact Armijo sufficient-decrease test;
  `InexactGradient.IsDiscreteGradient`: discrete gradients in the sense of Gonzalez and
  McLachlan–Quispel–Robidoux.

The names and namespaces are those of the files the definitions come from (Phase B of
`wip/UNIFY.md`: moves only). `GradientFlowConvergence.precondM`, a concrete operator on the
example space `EnergyExamples.E2` of `Stability/Energy.lean`, stays in
`Training/GradientFlowConvergence.lean`.
-/

open Set Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Projected gradient steps -/

/-- The projected (Galerkin) gradient step `x ↦ x - h Π ∇ℒ(x)` of dynamical low-rank training
(the update before truncation, `Ŵ = W - λ P(W) ∇ℒ(W)` in arXiv 2410.18720, eq. (18), and
`Ŷ₁ = Y₀ - h P_{Û₁} ∇ℓ(Y₀)` in arXiv 2502.03006, proof of Thm 5.8). -/
def projGradStep (P : E →L[ℝ] E) (g : E → E) (h : ℝ) (x : E) : E := x - h • P (g x)

/-! ### GeoLoRA -/

/-- The update direction of one GeoLoRA step (Schotthöfer–Zangrando–Ceruti–Tudisco–Kusch,
arXiv 2410.18720, eqs. (6)–(8)): with the left/right projectors `P₀ = U₀U₀ᵀ(·)`,
`Q₀ = (·)V₀V₀ᵀ` and the projectors `P̃ = ŨŨᵀ(·)`, `Q̃ = (·)ṼṼᵀ` onto the new basis directions,
the assembled `2r × 2r` coefficient matrix `Ŝ = [[S^new, L^new,ᵀṼ], [Ũᵀ K^new, 0]]` changes the
weights by `-λ (P₀ Q₀ ∇ℒ + P̃ Q₀ ∇ℒ + P₀ Q̃ ∇ℒ)` (the `S`-, `K`- and `L`-blocks; the lower
right block is zero), see the proof of Thm 1 (Thm 4 in the appendix) there. -/
def geoLoRADir (P₀ Q₀ Pt Qt : E →L[ℝ] E) (v : E) : E := P₀ (Q₀ v) + Pt (Q₀ v) + P₀ (Qt v)

/-- The bases of one GeoLoRA step for the gradient `v = ∇ℒ(W₀)` (arXiv 2410.18720, Algorithm 1):
commuting orthogonal left/right projectors `P₀ = U₀U₀ᵀ(·)`, `Q₀ = (·)V₀V₀ᵀ`, new directions
`P̃ = ŨŨᵀ(·)` with `ŨᵀU₀ = 0` and `Q̃ = (·)ṼṼᵀ` with `ṼᵀV₀ = 0` (left and right multiplications
commute), and the augmented bases `[U₀, Ũ]`, `[V₀, Ṽ]` capture the gradient directions of the `K`-
and `L`-steps.  Only these relations are used (`P̃`, `Q̃` need not be projectors here). -/
structure IsGeoLoRABases (P₀ Q₀ Pt Qt : E →L[ℝ] E) (v : E) : Prop where
  orthProj_left : IsOrthProj P₀
  orthProj_right : IsOrthProj Q₀
  comm : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x)
  comm_aug : ∀ x, P₀ (Qt x) = Qt (P₀ x)
  left_orth : ∀ x, Pt (P₀ x) = 0
  right_orth : ∀ x, Qt (Q₀ x) = 0
  left_capture : Pt (Q₀ v - P₀ (Q₀ v)) = Q₀ v - P₀ (Q₀ v)
  right_capture : Qt (P₀ v - Q₀ (P₀ v)) = P₀ v - Q₀ (P₀ v)

/-- The GeoLoRA iterate before truncation, `Ŵ = W₀ - λ (P₀ Q₀ + P̃ Q₀ + P₀ Q̃) ∇ℒ(W₀)`
(arXiv 2410.18720, eq. (8)). -/
def geoLoRAStep (P₀ Q₀ Pt Qt : E →L[ℝ] E) (g : E → E) (lr : ℝ) (w : E) : E :=
  w - lr • geoLoRADir P₀ Q₀ Pt Qt (g w)

/-! ### Federated dynamical low-rank training -/

section Federated

variable {ι : Type*}

/-- Variance-corrected local iterates of client `c` in FeDLRT (Schotthöfer–Laiu, arXiv 2406.17887,
eq. (8)), written for the full weights `z = Ũ S̃ Ṽᵀ` in the shared augmented space with Galerkin
projector `Π = Ũ Ũᵀ (·) Ṽ Ṽᵀ`:
`z⁰ = x`, `z^{s+1} = z^s - λ Π (∇ℒ_c(z^s) - ∇ℒ_c(x) + ∇ℒ(x))`.
(In coefficients, `S̃^{s+1} = S̃^s - λ (∇_S̃ ℒ_c(Ũ S̃^s Ṽᵀ) + G_S̃ - G_S̃,c)`, since
`Ũ (∇_S̃ ℒ) Ṽᵀ = Π ∇ℒ`.) -/
def fedClientIter (P : E →L[ℝ] E) (gc : ι → E → E) (g : E → E) (lr : ℝ) (x : E) (c : ι) :
    ℕ → E
  | 0 => x
  | s + 1 => fedClientIter P gc g lr x c s -
      lr • P (gc c (fedClientIter P gc g lr x c s) - gc c x + g x)

/-- One FeDLRT round before truncation: `s⋆` variance-corrected local steps on every client,
followed by averaging over the clients (the FedAvg aggregation `S̃⋆ = (1/C) ∑_c S̃_c^{s⋆}`,
eq. (10) of arXiv 2406.17887). -/
noncomputable def fedRound [Fintype ι] (P : E →L[ℝ] E) (gc : ι → E → E) (g : E → E) (lr : ℝ)
    (sstar : ℕ) (x : E) : E :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ c, fedClientIter P gc g lr x c sstar

/-- The client-averaged accumulated gradient difference
`(1/C) ∑_c ∑_{j<s⋆} (∇ℒ_c(z_c^j) - ∇ℒ_c(x))` of one FeDLRT round. -/
noncomputable def fedDrift [Fintype ι] (P : E →L[ℝ] E) (gc : ι → E → E) (g : E → E) (lr : ℝ)
    (sstar : ℕ) (x : E) : E :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ c, ∑ j ∈ range sstar, (gc c (fedClientIter P gc g lr x c j) - gc c x)

/-- Local iterates of client `c` in uncorrected (FedAvg-type) federated low-rank training on a
shared Galerkin space with projector `Π`: `z⁰ = x`, `z^{s+1} = z^s - λ Π ∇ℒ_c(z^s)` (no variance
correction, compare `fedClientIter`). -/
def fedAvgClientIter (P : E →L[ℝ] E) (gc : ι → E → E) (lr : ℝ) (x : E) (c : ι) : ℕ → E
  | 0 => x
  | s + 1 => fedAvgClientIter P gc lr x c s - lr • P (gc c (fedAvgClientIter P gc lr x c s))

/-- One uncorrected federated round: `s⋆` local projected steps per client, then averaging. -/
noncomputable def fedAvgRound [Fintype ι] (P : E →L[ℝ] E) (gc : ι → E → E) (lr : ℝ)
    (sstar : ℕ) (x : E) : E :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ c, fedAvgClientIter P gc lr x c sstar

end Federated

end LeanDLRA

/-! ### Factor-wise (LoRA) gradient descent -/

namespace LeanDLRA.FactorizedDynamics

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

open LeanDLRA

variable {k k' m n : Type*} [Fintype k] [Fintype k'] [Fintype m] [Fintype n]

/-- The operator of factor-wise (LoRA-style) gradient descent on `W = U S Vᵀ`: simultaneous
gradient flow in `(U, S, V)` induces `Ẇ = -P̂ ∇L(W)` with
`P̂ Z = Z V SᵀS Vᵀ + U Uᵀ Z V Vᵀ + U S Sᵀ Uᵀ Z` (OP-TR-14; from `U̇ = -Z V Sᵀ`, `Ṡ = -Uᵀ Z V`,
`V̇ = -Zᵀ U S` and the product rule; arXiv 2410.18720, Sec. 3, prints the middle term with a minus
sign).  Unlike `tangentProj U V` it depends on the singular values in `S`. -/
noncomputable def loraPrecond (U : Matrix m k ℝ) (S : Matrix k k' ℝ) (V : Matrix n k' ℝ)
    (Z : Matrix m n ℝ) : Matrix m n ℝ :=
  Z * V * (Sᵀ * S) * Vᵀ + U * Uᵀ * Z * V * Vᵀ + U * (S * Sᵀ) * Uᵀ * Z

end LeanDLRA.FactorizedDynamics

/-! ### Inexact gradients -/

namespace LeanDLRA.InexactGradient

open Set Finset Filter
open scoped RealInnerProductSpace

open LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inexact Armijo sufficient-decrease test `ℒ̃(x - s d) ≤ ℒ̃(x) - c s ‖d‖²` used by the
backtracking line searches of arXiv 2506.21405 (Alg. 2) and arXiv 2409.14938 (Algs. 2–3),
with inexact values `ℒ̃` and an inexact search direction `d = g̃`. -/
def ArmijoTest (ℒt : E → ℝ) (c : ℝ) (x d : E) (s : ℝ) : Prop :=
  ℒt (x - s • d) ≤ ℒt x - c * s * ‖d‖ ^ 2

/-- A **discrete gradient** of `ℒ` (Gonzalez, McLachlan–Quispel–Robidoux): a map `∇̄ℒ(x, y)`
with `ℒ(y) - ℒ(x) = ⟪∇̄ℒ(x, y), y - x⟫` for all `x, y`. -/
def IsDiscreteGradient (ℒ : E → ℝ) (gb : E → E → E) : Prop :=
  ∀ x y, ℒ y - ℒ x = ⟪gb x y, y - x⟫

end LeanDLRA.InexactGradient
