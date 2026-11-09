import LeanDLRA.LinearAlgebra.Frobenius.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Definitions: ODE solutions and conditions on vector fields

The vocabulary of layer 2 (`Analysis/`). All error analysis of dynamical low-rank integrators is
phrased through solutions of ODEs `y' = F(t, y)` on a normed space and a few conditions on the
right-hand side `F`. The theorems about these objects are in `LeanDLRA/Foundations/ODE.lean`
(speed bounds, uniqueness, Grönwall), `LeanDLRA/Foundations/OneSided.lean` (one-sided Lipschitz
calculus), `LeanDLRA/Integrators/Exactness.lean` (state-independent right-hand sides),
`LeanDLRA/Foundations/Localization.lean` (localization in tubes),
`LeanDLRA/Foundations/Galerkin.lean` and `LeanDLRA/Stability/Energy.lean` (Euler steps) and
`LeanDLRA/Dynamics/ContinuousDLRA.lean` (Grönwall with a time-dependent source).

## Main definitions

* `LeanDLRA.ODESolution F y a b`: `y` solves `y' = F t y` on `[a, b]` (continuity on `Icc a b`,
  right derivatives on `Ico a b`), the convention of Mathlib's uniqueness and Grönwall theorems.
* `LeanDLRA.IsLipschitzField F L`: `‖F t x - F t y‖ ≤ L ‖x - y‖` for all `t x y`.
* `LeanDLRA.IsBoundedField F B`: `‖F t x‖ ≤ B` for all `t x`.
* `LeanDLRA.IsOneSidedLipschitzField F ℓ`: `⟪F t x - F t y, x - y⟫ ≤ ℓ ‖x - y‖²` for all `t x y`,
  with `ℓ` of any sign; `LeanDLRA.IsOneSidedLipschitzOn F K ℓ`: the same for states in `K`.
* `LeanDLRA.IsDerivRHS F A t₀ t₁`: `F t Y = Ȧ(t)` on `[t₀, t₁]` for every state `Y` (the setting
  of the exactness theorems).
* `LeanDLRA.IsLipschitzOnTube`, `LeanDLRA.IsBoundedOnTube`, `LeanDLRA.tubeSet`: Lipschitz and
  boundedness conditions on the tube of radius `ρ` around a curve `A`;
  `LeanDLRA.ballRetract`, `LeanDLRA.radialRetract`: the radial retraction onto a closed ball;
  `LeanDLRA.tubeExt`: the global extension of a field given on a tube.
* `LeanDLRA.eulerStep`, `LeanDLRA.projEuler`, `LeanDLRA.projEulerIter`: the explicit Euler step
  `x ↦ x + h F(x)`, the projected Euler step `x ↦ x + h P F(t, x)` and its iterates.
* `LeanDLRA.gronwallIntegralBound`: the solution of `u' = K u + η(t)`, `u(a) = δ`.
* `LeanDLRA.gramMatrix`, `LeanDLRA.crossGram`: Gram matrices `(⟪Zʲ, Zˡ⟫)` of tuples of vectors.
* `LeanDLRA.entrywiseCubic`: the entrywise cubic nonlinearity `Xᵢⱼ ↦ Xᵢⱼ³` on matrices.

## Implementation notes

Nonnegativity of constants is a separate hypothesis (`hL : 0 ≤ L`), not part of the predicates
(`docs/CONVENTIONS.md` §6.1).

`Mathlib.Analysis.LocallyConvex.AbsConvexOpen` is imported so that the `PolynormableSpace`
argument of `HasDerivWithinAt` is found as `LocallyConvexSpace.toPolynormableSpace`, as with all
of Mathlib imported; otherwise the elaborated types of `ODESolution` and `IsDerivRHS` would differ
from those of the files that use them.

## References

* [CarrelVandereycken2023, Def. 1] (one-sided Lipschitz fields)
* [ZhaoOstermannGu2021, Property 1(b)] (tube conditions)
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

/-! ### Tubes around a curve -/

section Tube

open Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `F` is `L`-Lipschitz in the state on the tube of radius `ρ` around the curve `A` over the
time interval `[a, b]`: `‖F t x - F t y‖ ≤ L ‖x - y‖` whenever `t ∈ [a, b]`,
`‖x - A t‖ ≤ ρ` and `‖y - A t‖ ≤ ρ` [ZhaoOstermannGu2021, Property 1(b), eq. (3.3)]. -/
def IsLipschitzOnTube (F : ℝ → E → E) (A : ℝ → E) (a b ρ L : ℝ) : Prop :=
  ∀ t ∈ Icc a b, ∀ x y, ‖x - A t‖ ≤ ρ → ‖y - A t‖ ≤ ρ → ‖F t x - F t y‖ ≤ L * ‖x - y‖

/-- `F` is bounded by `B` on the tube of radius `ρ` around `A` over `[a, b]`
[ZhaoOstermannGu2021, Property 1(b), eq. (3.3)]. -/
def IsBoundedOnTube (F : ℝ → E → E) (A : ℝ → E) (a b ρ B : ℝ) : Prop :=
  ∀ t ∈ Icc a b, ∀ x, ‖x - A t‖ ≤ ρ → ‖F t x‖ ≤ B

/-- The tube `{(t, x) | t ∈ [a, b], ‖x - A t‖ ≤ ρ}` as a subset of `ℝ × E`. -/
def tubeSet (A : ℝ → E) (a b ρ : ℝ) : Set (ℝ × E) :=
  {p | p.1 ∈ Icc a b ∧ ‖p.2 - A p.1‖ ≤ ρ}

/-- The radial retraction of `E` onto the closed ball of radius `ρ` around `c`:
`x ↦ c + min 1 (ρ / ‖x - c‖) • (x - c)`. It is the metric projection onto the ball. -/
noncomputable def ballRetract (c : E) (ρ : ℝ) (x : E) : E :=
  c + min 1 (ρ / ‖x - c‖) • (x - c)

/-- The radial retraction onto the ball of radius `ρ` around `0`. -/
noncomputable def radialRetract (ρ : ℝ) (z : E) : E := min 1 (ρ / ‖z‖) • z

/-- The retraction onto a ball around `c` is the retraction around `0`, shifted by `c`. -/
lemma ballRetract_eq (c : E) (ρ : ℝ) (x : E) :
    ballRetract c ρ x = c + radialRetract ρ (x - c) := rfl

open Classical in
/-- **Global extension of a field given on a tube.** For `t ∈ [a, b]`,
`tubeExt F A a b ρ t x = F t (r_t x)` with `r_t` the radial retraction onto the closed ball of
radius `ρ` around `A t`; outside `[a, b]` the extension is `0` (solutions on subintervals of
`[a, b]` never see these values). It agrees with `F` on the tube and is globally Lipschitz and
bounded with the *same* constants as `F` on the tube (`LeanDLRA/Foundations/Localization.lean`). -/
noncomputable def tubeExt (F : ℝ → E → E) (A : ℝ → E) (a b ρ : ℝ) (t : ℝ) (x : E) : E :=
  if t ∈ Icc a b then F t (ballRetract (A t) ρ x) else 0

end Tube

/-! ### Explicit Euler steps -/

section Euler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The full explicit Euler step `x ↦ x + h F(x)` of the (frozen-time) field `F`. -/
def eulerStep (F : E → E) (h : ℝ) (x : E) : E := x + h • F x

/-- The projected forward Euler step `x ↦ x + h P F(t, x)`. -/
def projEuler (P : E →L[ℝ] E) (F : ℝ → E → E) (h t : ℝ) (x : E) : E := x + h • P (F t x)

/-- Iterates of the projected forward Euler method on the grid `t₀ + n h`. -/
def projEulerIter (P : E →L[ℝ] E) (F : ℝ → E → E) (h t₀ : ℝ) (x₀ : E) : ℕ → E
  | 0 => x₀
  | n + 1 => projEuler P F h (t₀ + n * h) (projEulerIter P F h t₀ x₀ n)

end Euler

/-! ### Grönwall's inequality with a time-dependent source term -/

/-- The solution `e^{K(x-a)} (δ + ∫ₐˣ e^{-K(s-a)} η(s) ds)` of the scalar comparison equation
`u' = K u + η(t)`, `u(a) = δ`; for constant `η` it equals `gronwallBound δ K η (x - a)`. -/
noncomputable def gronwallIntegralBound (δ K : ℝ) (η : ℝ → ℝ) (a x : ℝ) : ℝ :=
  Real.exp (K * (x - a)) * (δ + ∫ s in a..x, Real.exp (-(K * (s - a))) * η s)

/-! ### Gram matrices and the entrywise cubic nonlinearity -/

section Gram

open scoped LeanDLRA.Frobenius Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The Gram matrix `C_Z = (⟪Zʲ, Zˡ⟫)_{j,l}` of a `k`-tuple `Z ∈ [H]^k`. -/
def gramMatrix (Z : PiLp 2 fun _ : ι => H) : Matrix ι ι ℝ := Matrix.of fun j l => ⟪Z j, Z l⟫

/-- The cross-Gram matrix `(⟪aʲ, bˡ⟫)_{j,l}`. -/
def crossGram (a b : PiLp 2 fun _ : ι => H) : Matrix ι ι ℝ := Matrix.of fun j l => ⟪a j, b l⟫

end Gram

section Cubic

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The entrywise cubic nonlinearity `G(X)ᵢⱼ = |Xᵢⱼ|² Xᵢⱼ = Xᵢⱼ³` on real matrices. -/
def entrywiseCubic (X : Matrix m n ℝ) : Matrix m n ℝ := fun i j => X i j ^ 3

end Cubic

end LeanDLRA
