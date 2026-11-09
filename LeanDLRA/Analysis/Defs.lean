import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

/-!
# Definitions: ODE solutions and conditions on vector fields

The vocabulary of layer 2 (`Analysis/`). All error analysis of dynamical low-rank integrators is
phrased through solutions of ODEs `y' = F(t, y)` on a normed space and a few conditions on the
right-hand side `F`. The theorems about these objects are in `LeanDLRA/Foundations/ODE.lean`
(speed bounds, uniqueness, Grönwall), `LeanDLRA/Foundations/OneSided.lean` (one-sided Lipschitz
calculus) and `LeanDLRA/Integrators/Exactness.lean` (state-independent right-hand sides).

## Main definitions

* `LeanDLRA.ODESolution F y a b`: `y` solves `y' = F t y` on `[a, b]` (continuity on `Icc a b`,
  right derivatives on `Ico a b`), the convention of Mathlib's uniqueness and Grönwall theorems.
* `LeanDLRA.IsLipschitzField F L`: `‖F t x - F t y‖ ≤ L ‖x - y‖` for all `t x y`.
* `LeanDLRA.IsBoundedField F B`: `‖F t x‖ ≤ B` for all `t x`.
* `LeanDLRA.IsOneSidedLipschitzField F ℓ`: `⟪F t x - F t y, x - y⟫ ≤ ℓ ‖x - y‖²` for all `t x y`,
  with `ℓ` of any sign; `LeanDLRA.IsOneSidedLipschitzOn F K ℓ`: the same for states in `K`.
* `LeanDLRA.IsDerivRHS F A t₀ t₁`: `F t Y = Ȧ(t)` on `[t₀, t₁]` for every state `Y` (the setting
  of the exactness theorems).

## Implementation notes

Nonnegativity of constants is a separate hypothesis (`hL : 0 ≤ L`), not part of the predicates
(`docs/CONVENTIONS.md` §6.1).

`Mathlib.Analysis.LocallyConvex.AbsConvexOpen` is imported so that the `PolynormableSpace`
argument of `HasDerivWithinAt` is found as `LocallyConvexSpace.toPolynormableSpace`, as with all
of Mathlib imported; otherwise the elaborated types of `ODESolution` and `IsDerivRHS` would differ
from those of the files that use them.

## References

* [CarrelVandereycken2023, Def. 1] (one-sided Lipschitz fields)
-/

open Set
open scoped RealInnerProductSpace

namespace LeanDLRA

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `y` solves the ODE `y' = f t (y t)` on `[a, b]` (right derivatives on `[a, b)`, continuity on
`[a, b]`), the convention of Mathlib's `ODE_solution_unique` and Grönwall bounds. -/
structure ODESolution (f : ℝ → E → E) (y : ℝ → E) (a b : ℝ) : Prop where
  /-- `y` is continuous on `[a, b]`. -/
  cont : ContinuousOn y (Icc a b)
  /-- `y` has right derivative `f t (y t)` at every `t ∈ [a, b)`. -/
  deriv : ∀ t ∈ Ico a b, HasDerivWithinAt y (f t (y t)) (Ici t) t

/-- The vector field `f` is Lipschitz in the state variable with constant `L`, uniformly in time. -/
def IsLipschitzField (f : ℝ → E → E) (L : ℝ) : Prop :=
  ∀ t x y, ‖f t x - f t y‖ ≤ L * ‖x - y‖

/-- The vector field `f` is bounded by `B`. -/
def IsBoundedField (f : ℝ → E → E) (B : ℝ) : Prop :=
  ∀ t x, ‖f t x‖ ≤ B

/-- The right-hand side `F` equals `Ȧ(t)` on `[t₀, t₁]`, independently of the state: `A` is
continuous on `[t₀, t₁]` and has right derivative `F t Y` at every `t ∈ [t₀, t₁)`, for every
state `Y`. -/
structure IsDerivRHS (F : ℝ → E → E) (A : ℝ → E) (t₀ t₁ : ℝ) : Prop where
  /-- `A` is continuous on `[t₀, t₁]`. -/
  cont : ContinuousOn A (Icc t₀ t₁)
  /-- `A` has right derivative `F t Y` at every `t ∈ [t₀, t₁)`, for every state `Y`. -/
  deriv : ∀ t ∈ Ico t₀ t₁, ∀ Y, HasDerivWithinAt A (F t Y) (Ici t) t

/-- A constant curve solves `y' = 0`, so `ODESolution` is satisfiable. -/
example (x : E) (a b : ℝ) : ODESolution (fun _ _ => (0 : E)) (fun _ => x) a b :=
  ⟨continuousOn_const, fun _ _ => hasDerivWithinAt_const _ _ _⟩

/-- A constant curve has the state-independent right-hand side `0`, so `IsDerivRHS` is
satisfiable. -/
example (x : E) (t₀ t₁ : ℝ) : IsDerivRHS (fun _ _ => (0 : E)) (fun _ => x) t₀ t₁ :=
  ⟨continuousOn_const, fun _ _ _ => hasDerivWithinAt_const _ _ _⟩

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The vector field `F` is **one-sided Lipschitz** with constant `ℓ` (uniformly in time):
`⟪F t x - F t y, x - y⟫ ≤ ℓ ‖x - y‖²` for all `t, x, y` [CarrelVandereycken2023, Def. 1].
The constant `ℓ` may be negative (dissipative problems). -/
def IsOneSidedLipschitzField (F : ℝ → E → E) (ℓ : ℝ) : Prop :=
  ∀ t x y, ⟪F t x - F t y, x - y⟫ ≤ ℓ * ‖x - y‖ ^ 2

/-- Localised one-sided Lipschitz condition: the one-sided inequality holds for states in the set
`K` only (one-sided stability in an energy-localised region, [HuYu2026, eqs. (3.3), (5.1)]). -/
def IsOneSidedLipschitzOn (F : ℝ → E → E) (K : Set E) (ℓ : ℝ) : Prop :=
  ∀ t, ∀ x ∈ K, ∀ y ∈ K, ⟪F t x - F t y, x - y⟫ ≤ ℓ * ‖x - y‖ ^ 2

end InnerProductSpace

end LeanDLRA
