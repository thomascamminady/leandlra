import LeanDLRA.Analysis.Defs
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Curvature

/-!
# Definitions for HighOrder Part3

Local definitions used by the theorems of the corresponding modules.
-/

open Set
open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

universe u

namespace LeanDLRA.OpenProblems.HighOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **a posteriori normal component** of a BUG step: the largest doubly normal component of
`F(t, ·)` at the computed K- and L-endpoints `K`, `L` over the step. -/
noncomputable def aposterioriEps (F : ℝ → E → E) (P₀ Q₀ P₁ Q₁ : E →L[ℝ] E) (t₀ t₁ : ℝ)
    (K L : E) : ℝ :=
  max (sSup ((fun t => ‖(1 - P₁) ((1 - Q₀) (F t K))‖) '' Icc t₀ t₁))
    (sSup ((fun t => ‖(1 - Q₁) ((1 - P₀) (F t L))‖) '' Icc t₀ t₁))

section Matrix

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]

end Matrix

/-- One step of an **augmented conservative BUG integrator** (conservative unconventional
integrator / arXiv 2206.09374, abstract form): a BUG step whose new co-range projector contains the
conserved direction `c` (`P₁ c = Q₁ c = c`; matrices: the velocity basis contains the conserved
moments), followed by a conservative truncation (`‖Y₁ - YS(t₁)‖ ≤ ϑ`, `⟪c, Y₁⟫ = ⟪c, YS(t₁)⟫`).  The
normal-component bound `ε` of the BUG step is the `ε_cons` of the constrained manifold. -/
structure IsConservativeBUGStep (F : ℝ → E → E) (ε ϑ : ℝ) (c : E) (P₀ Q₀ P₁ Q₁ : E →L[ℝ] E)
    (t₀ t₁ : ℝ) (Y₀ : E) (YK YL YS : ℝ → E) (Y₁ : E) : Prop where
  bug : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS
  fixP : P₁ c = c
  fixQ : Q₁ c = c
  trunc : ‖Y₁ - YS t₁‖ ≤ ϑ
  truncCons : ⟪c, Y₁⟫ = ⟪c, YS t₁⟫

/-- Butcher matrix of **Ketcheson's SSPRK(10,4)** (the scheme displayed in arXiv 2608.27749 in
low-storage Shu–Osher form with steps `h/6` and weights `3/5, 2/5, 1/25, 9/25`):
`aᵢⱼ = 1/6` for `j < i < 5`, `aᵢⱼ = 1/15` for `j < 5 ≤ i`, `aᵢⱼ = 1/6` for `5 ≤ j < i`
(0-based indices). -/
def ssprk104A : Fin 10 → Fin 10 → ℚ := fun i j =>
  if j < i then (if i.val < 5 then 1 / 6 else if j.val < 5 then 1 / 15 else 1 / 6) else 0

/-- Weights of SSPRK(10,4): all equal to `1/10`. -/
def ssprk104b : Fin 10 → ℚ := fun _ => 1 / 10

/-- Nodes of SSPRK(10,4): `cᵢ = ∑ⱼ aᵢⱼ`. -/
def ssprk104c : Fin 10 → ℚ := fun i => ∑ j, ssprk104A i j

/-- **Bridge.** `ssprk104A`, `ssprk104b`, `ssprk104c` are the arrays of the core tableau
`ButcherTableau.ssprk104` over `ℚ` (same definitions). They are kept under their names because the
catalogue statements of OP-HO-12 are phrased with them. -/
theorem ssprk104A_eq : ssprk104A = (ButcherTableau.ssprk104 : ButcherTableau ℚ 10).a := rfl

/-- The weights of SSPRK(10,4) are those of the core tableau `ButcherTableau.ssprk104`. -/
theorem ssprk104b_eq : ssprk104b = (ButcherTableau.ssprk104 : ButcherTableau ℚ 10).b := rfl

/-- The nodes of SSPRK(10,4) are those of the core tableau `ButcherTableau.ssprk104`. -/
theorem ssprk104c_eq : ssprk104c = (ButcherTableau.ssprk104 : ButcherTableau ℚ 10).c := rfl

/-- The first unit vector of `ℝ³` as a `3 × 1` orthonormal basis. -/
def e₁₃ : Matrix (Fin 3) (Fin 1) ℝ := fun i _ => if i = 0 then 1 else 0

/-- The first two unit vectors of `ℝ³` as a `3 × 2` orthonormal basis (buffer direction `e₂`). -/
def e₁₂₃ : Matrix (Fin 3) (Fin 2) ℝ := fun i j => if i.val = j.val then 1 else 0

/-- The companion matrix `[[1 + λ, λ²/2], [1, λ/2]]` of the recursion on `(ρⁿ, ρ^{n-1/2})` of the
limiting scheme (3.45) of arXiv 2005.06571, `λ = Δt μ`, `μ ≤ 0` an eigenvalue of the discrete
diffusion operator.  Its characteristic polynomial is `z² - (1 + 3λ/2) z + λ/2`. -/
noncomputable def apCompanion (lam : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + lam, lam ^ 2 / 2; 1, lam / 2]

end LeanDLRA.OpenProblems.HighOrder
