import LeanDLRA.LinearAlgebra.Frobenius.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Convex.Hull

/-!
# Definitions: ODE solutions and conditions on vector fields

The vocabulary of layer 2 (`Analysis/`). All error analysis of dynamical low-rank integrators is
phrased through solutions of ODEs `y' = F(t, y)` on a normed space and a few conditions on the
right-hand side `F`. The theorems about these objects are in `LeanDLRA/Foundations/ODE.lean`
(speed bounds, uniqueness, Grönwall), `LeanDLRA/Foundations/OneSided.lean` (one-sided Lipschitz
calculus), `LeanDLRA/Integrators/Exactness.lean` (state-independent right-hand sides),
`LeanDLRA/Foundations/Localization.lean` (localization in tubes),
`LeanDLRA/Foundations/Galerkin.lean` and `LeanDLRA/Stability/Energy.lean` (Euler steps) and
`LeanDLRA/Dynamics/ContinuousDLRA.lean` (Grönwall with a time-dependent source) and
`LeanDLRA/Matrix/Interpolation.lean` (Filippov sets).

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
* `LeanDLRA.filippov f M y`: the Filippov regularisation `⋂_{δ > 0} cl conv f(B(y, δ) ∩ M)` of a
  possibly discontinuous vector field.
* `LeanDLRA.IsLipschitzFieldOn F D L`, `LeanDLRA.IsBoundedFieldOn F D B`,
  `LeanDLRA.IsOneSidedLipschitzFieldOn F D ℓ`: the three conditions on `F` above, required only at
  the points `(t, x)` of a region `D ⊆ ℝ × E` (for example the tube around a reference solution).

## Main results

* `LeanDLRA.isLipschitzField_iff_univ`, `LeanDLRA.isBoundedField_iff_univ`,
  `LeanDLRA.isOneSidedLipschitzField_iff_univ`: the global conditions are the region conditions
  for `D = univ`.
* `LeanDLRA.isLipschitzOnTube_iff`, `LeanDLRA.isBoundedOnTube_iff`: the tube conditions are the
  region conditions for `D = tubeSet A a b ρ`; `LeanDLRA.isOneSidedLipschitzOn_iff`: the condition
  on a set `K` of states is the region condition for `D = univ ×ˢ K`.
* `LeanDLRA.isLipschitzFieldOn_iff_lipschitzOnWith`: the region condition in terms of Mathlib's
  `LipschitzOnWith`.

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
* [CarrelEtAl2025, eq. (16)] (Filippov regularisation)
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

/-! ### Filippov regularisation -/

section Filippov

open Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Filippov set-valued regularisation of a (possibly discontinuous) vector field `f`
restricted to a set `ℳ` [CarrelEtAl2025, eq. (16)]:
`𝓕(y) = ⋂_{δ > 0} cl conv f(B(y, δ) ∩ ℳ)`. -/
def filippov (f : E → E) (M : Set E) (y : E) : Set E :=
  ⋂ δ > 0, closure (convexHull ℝ (f '' (ball y δ ∩ M)))

end Filippov

/-! ### Runge–Kutta tableaux -/

section RungeKutta

/-- A **Butcher tableau** with `s` stages and coefficients in `R`: the Runge–Kutta matrix `a`, the
weights `b` and the nodes `c`. The Runge–Kutta step structures of the library take the three
arrays as separate arguments (`RungeKuttaBUG.IsGalerkinRKStep F T.a T.b T.c …`); the order
conditions of a tableau are statements about `T.a`, `T.b`, `T.c`. -/
structure ButcherTableau (R : Type*) (s : ℕ) where
  /-- The Runge–Kutta matrix `(aᵢⱼ)`. -/
  a : Fin s → Fin s → R
  /-- The weights `bᵢ`. -/
  b : Fin s → R
  /-- The nodes `cᵢ`. -/
  c : Fin s → R

namespace ButcherTableau

variable {R : Type*} {s : ℕ}

/-- The tableau is **explicit**: `aᵢⱼ = 0` for `i ≤ j`, so every stage uses only the earlier
ones. -/
def IsExplicit [Zero R] (T : ButcherTableau R s) : Prop :=
  ∀ i j, i ≤ j → T.a i j = 0

/-- The nodes are the row sums of the Runge–Kutta matrix, `cᵢ = ∑ⱼ aᵢⱼ`. -/
def IsRowSum [AddCommMonoid R] (T : ButcherTableau R s) : Prop :=
  ∀ i, T.c i = ∑ j, T.a i j

/-- The explicit Euler method `y₁ = y + h F(t, y)`. -/
def euler [Zero R] [One R] : ButcherTableau R 1 :=
  ⟨fun _ _ => 0, fun _ => 1, fun _ => 0⟩

/-- The classical fourth-order Runge–Kutta method: `a₂₁ = a₃₂ = 1/2`, `a₄₃ = 1`,
`b = (1/6, 1/3, 1/3, 1/6)`, `c = (0, 1/2, 1/2, 1)`. -/
def rk4 [DivisionRing R] : ButcherTableau R 4 :=
  ⟨![![0, 0, 0, 0], ![1 / 2, 0, 0, 0], ![0, 1 / 2, 0, 0], ![0, 0, 1, 0]],
    ![1 / 6, 1 / 3, 1 / 3, 1 / 6], ![0, 1 / 2, 1 / 2, 1]⟩

/-- **Ketcheson's SSPRK(10,4)** in Butcher form (0-based indices): `aᵢⱼ = 1/6` for `j < i < 5`,
`aᵢⱼ = 1/15` for `j < 5 ≤ i`, `aᵢⱼ = 1/6` for `5 ≤ j < i`, all weights `1/10`, and the nodes the
row sums. -/
def ssprk104 [DivisionRing R] : ButcherTableau R 10 where
  a i j := if j < i then (if i.val < 5 then 1 / 6 else if j.val < 5 then 1 / 15 else 1 / 6) else 0
  b _ := 1 / 10
  c i := ∑ j, if j < i then (if i.val < 5 then 1 / 6 else if j.val < 5 then 1 / 15 else 1 / 6)
    else 0

theorem euler_isExplicit [Zero R] [One R] : (euler : ButcherTableau R 1).IsExplicit :=
  fun _ _ _ => rfl

theorem rk4_isExplicit [DivisionRing R] : (rk4 : ButcherTableau R 4).IsExplicit := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)

theorem rk4_isRowSum [DivisionRing R] : (rk4 : ButcherTableau R 4).IsRowSum := by
  intro i
  fin_cases i <;> simp [rk4, Fin.sum_univ_four]

theorem ssprk104_isExplicit [DivisionRing R] : (ssprk104 : ButcherTableau R 10).IsExplicit :=
  fun _ _ hij => by simp [ssprk104, not_lt.2 hij]

theorem ssprk104_isRowSum [DivisionRing R] : (ssprk104 : ButcherTableau R 10).IsRowSum :=
  fun _ => rfl

end ButcherTableau

end RungeKutta

/-! ### The functions `φ₁`, `φ₂` of exponential integrators -/

/-- `φ₁(z) = (eᶻ - 1)/z`, `φ₁(0) = 1`, the first `φ`-function of exponential integrators
(`eᶻ = 1 + z φ₁(z)`). -/
noncomputable def phi1 (z : ℝ) : ℝ := if z = 0 then 1 else (Real.exp z - 1) / z

/-- `φ₂(z) = (eᶻ - 1 - z)/z²`, `φ₂(0) = 1/2`, the second `φ`-function of exponential
integrators. -/
noncomputable def phi2 (z : ℝ) : ℝ := if z = 0 then 1 / 2 else (Real.exp z - 1 - z) / z ^ 2

/-! ### Conditions on a vector field on a region of `ℝ × E` -/

section Region

variable {E : Type*} [NormedAddCommGroup E]

/-- The vector field `F` is **Lipschitz on the region** `D ⊆ ℝ × E` with constant `L`:
`‖F t x - F t y‖ ≤ L ‖x - y‖` whenever `(t, x) ∈ D` and `(t, y) ∈ D`. Only states at the same
time `t` are compared, so the region may move with time; the typical region is the tube
`tubeSet A a b ρ` of radius `ρ` around a reference solution `A`. For `D = univ` this is
`IsLipschitzField` (`isLipschitzField_iff_univ`), for the tube it is `IsLipschitzOnTube`
(`isLipschitzOnTube_iff`). Nonnegativity of `L` is not part of the condition. -/
def IsLipschitzFieldOn (F : ℝ → E → E) (D : Set (ℝ × E)) (L : ℝ) : Prop :=
  ∀ ⦃t x y⦄, (t, x) ∈ D → (t, y) ∈ D → ‖F t x - F t y‖ ≤ L * ‖x - y‖

/-- The vector field `F` is **bounded by `B` on the region** `D ⊆ ℝ × E`: `‖F t x‖ ≤ B` for every
`(t, x) ∈ D`. For `D = univ` this is `IsBoundedField` (`isBoundedField_iff_univ`), for the tube
around a curve it is `IsBoundedOnTube` (`isBoundedOnTube_iff`). -/
def IsBoundedFieldOn (F : ℝ → E → E) (D : Set (ℝ × E)) (B : ℝ) : Prop :=
  ∀ ⦃t x⦄, (t, x) ∈ D → ‖F t x‖ ≤ B

variable {F : ℝ → E → E} {A : ℝ → E} {D D' : Set (ℝ × E)} {a b ρ L L' B B' : ℝ}

/-- The Lipschitz condition passes to smaller regions and larger constants. -/
theorem IsLipschitzFieldOn.mono (h : IsLipschitzFieldOn F D L) (hD : D' ⊆ D) (hL : L ≤ L') :
    IsLipschitzFieldOn F D' L' := fun _ _ _ hx hy =>
  (h (hD hx) (hD hy)).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

/-- The bound passes to smaller regions and larger constants. -/
theorem IsBoundedFieldOn.mono (h : IsBoundedFieldOn F D B) (hD : D' ⊆ D) (hB : B ≤ B') :
    IsBoundedFieldOn F D' B' := fun _ _ hx => (h (hD hx)).trans hB

/-- For `0 ≤ L`, the Lipschitz condition on a region says that every time slice `F t` is
`L`-Lipschitz in Mathlib's sense (`LipschitzOnWith`) on the slice `{x | (t, x) ∈ D}`. -/
theorem isLipschitzFieldOn_iff_lipschitzOnWith (hL : 0 ≤ L) :
    IsLipschitzFieldOn F D L ↔
      ∀ t, LipschitzOnWith (Real.toNNReal L) (F t) {x | (t, x) ∈ D} := by
  refine ⟨fun h t => lipschitzOnWith_iff_norm_sub_le.2 fun x hx y hy => ?_,
    fun h t x y hx hy => ?_⟩
  · rw [Real.coe_toNNReal _ hL]
    exact h hx hy
  · have := lipschitzOnWith_iff_norm_sub_le.1 (h t) hx hy
    rwa [Real.coe_toNNReal _ hL] at this

/-- The global Lipschitz condition is the Lipschitz condition on the region `univ`. -/
theorem isLipschitzField_iff_univ : IsLipschitzField F L ↔ IsLipschitzFieldOn F univ L :=
  ⟨fun h t x y _ _ => h t x y, fun h _ _ _ => h (mem_univ _) (mem_univ _)⟩

/-- The global bound is the bound on the region `univ`. -/
theorem isBoundedField_iff_univ : IsBoundedField F B ↔ IsBoundedFieldOn F univ B :=
  ⟨fun h t x _ => h t x, fun h _ _ => h (mem_univ _)⟩

/-- The Lipschitz condition on the tube around `A` is the Lipschitz condition on the region
`tubeSet A a b ρ`. -/
theorem isLipschitzOnTube_iff :
    IsLipschitzOnTube F A a b ρ L ↔ IsLipschitzFieldOn F (tubeSet A a b ρ) L :=
  ⟨fun h t x y hx hy => h t hx.1 x y hx.2 hy.2,
    fun h t ht x y hx hy => h (t := t) (x := x) (y := y) ⟨ht, hx⟩ ⟨ht, hy⟩⟩

/-- The bound on the tube around `A` is the bound on the region `tubeSet A a b ρ`. -/
theorem isBoundedOnTube_iff :
    IsBoundedOnTube F A a b ρ B ↔ IsBoundedFieldOn F (tubeSet A a b ρ) B :=
  ⟨fun h t x hx => h t hx.1 x hx.2, fun h t ht x hx => h (t := t) (x := x) ⟨ht, hx⟩⟩

end Region

section RegionInner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The vector field `F` is **one-sided Lipschitz on the region** `D ⊆ ℝ × E` with constant `ℓ`:
`⟪F t x - F t y, x - y⟫ ≤ ℓ ‖x - y‖²` whenever `(t, x) ∈ D` and `(t, y) ∈ D`. The constant may be
negative (dissipative problems) and can be much smaller than a Lipschitz constant, which makes it
the natural condition for stiff problems. For `D = univ` this is `IsOneSidedLipschitzField`
(`isOneSidedLipschitzField_iff_univ`), for the region `univ ×ˢ K` given by a set `K` of states it
is `IsOneSidedLipschitzOn` (`isOneSidedLipschitzOn_iff`). -/
def IsOneSidedLipschitzFieldOn (F : ℝ → E → E) (D : Set (ℝ × E)) (ℓ : ℝ) : Prop :=
  ∀ ⦃t x y⦄, (t, x) ∈ D → (t, y) ∈ D → ⟪F t x - F t y, x - y⟫ ≤ ℓ * ‖x - y‖ ^ 2

variable {F : ℝ → E → E} {D D' : Set (ℝ × E)} {L ℓ ℓ' : ℝ}

/-- The one-sided Lipschitz condition passes to smaller regions and larger constants. -/
theorem IsOneSidedLipschitzFieldOn.mono (h : IsOneSidedLipschitzFieldOn F D ℓ) (hD : D' ⊆ D)
    (hℓ : ℓ ≤ ℓ') : IsOneSidedLipschitzFieldOn F D' ℓ' := fun _ _ _ hx hy =>
  (h (hD hx) (hD hy)).trans (mul_le_mul_of_nonneg_right hℓ (sq_nonneg _))

/-- An `L`-Lipschitz field on a region is one-sided Lipschitz there with constant `L`
(Cauchy–Schwarz). -/
theorem IsLipschitzFieldOn.isOneSidedLipschitzFieldOn (h : IsLipschitzFieldOn F D L) :
    IsOneSidedLipschitzFieldOn F D L := fun t x y hx hy =>
  calc ⟪F t x - F t y, x - y⟫ ≤ ‖F t x - F t y‖ * ‖x - y‖ := real_inner_le_norm _ _
    _ ≤ L * ‖x - y‖ * ‖x - y‖ := mul_le_mul_of_nonneg_right (h hx hy) (norm_nonneg _)
    _ = L * ‖x - y‖ ^ 2 := by ring

/-- The global one-sided Lipschitz condition is the condition on the region `univ`. -/
theorem isOneSidedLipschitzField_iff_univ :
    IsOneSidedLipschitzField F ℓ ↔ IsOneSidedLipschitzFieldOn F univ ℓ :=
  ⟨fun h t x y _ _ => h t x y, fun h _ _ _ => h (mem_univ _) (mem_univ _)⟩

/-- The one-sided Lipschitz condition on a set `K` of states (for all times) is the condition on
the region `univ ×ˢ K`. -/
theorem isOneSidedLipschitzOn_iff {K : Set E} :
    IsOneSidedLipschitzOn F K ℓ ↔ IsOneSidedLipschitzFieldOn F (univ ×ˢ K) ℓ :=
  ⟨fun h t x y hx hy => h t x hx.2 y hy.2,
    fun h t x hx y hy => h (t := t) (x := x) (y := y) ⟨mem_univ t, hx⟩ ⟨mem_univ t, hy⟩⟩

/-! Non-vacuity: linear fields `F(t, x) = T x + g`. For matrices, `T Y = M Y + Y Nᵀ` gives the
field `M Y + Y Nᵀ + G` of Lyapunov and Sylvester type, with `‖T‖ ≤ ‖M‖ + ‖N‖`. -/

/-- A linear field `F(t, x) = T x + g` (`T` a continuous linear map, `g` a constant source) is
Lipschitz with constant `‖T‖` on every region. -/
example (T : E →L[ℝ] E) (g : E) (D : Set (ℝ × E)) :
    IsLipschitzFieldOn (fun _ x => T x + g) D ‖T‖ := fun _ x y _ _ => by
  rw [add_sub_add_right_eq_sub, ← map_sub]
  exact T.le_opNorm _

/-- On the tube of radius `ρ` around the constant curve `c`, the linear field `T x + g` is
bounded by `‖T‖ ρ + ‖T c + g‖`. -/
example (T : E →L[ℝ] E) (g c : E) (a b ρ : ℝ) :
    IsBoundedFieldOn (fun _ x => T x + g) (tubeSet (fun _ => c) a b ρ) (‖T‖ * ρ + ‖T c + g‖) := by
  intro t x hx
  have hx' : ‖x - c‖ ≤ ρ := hx.2
  calc ‖T x + g‖ = ‖T (x - c) + (T c + g)‖ := by rw [map_sub]; congr 1; abel
    _ ≤ ‖T (x - c)‖ + ‖T c + g‖ := norm_add_le _ _
    _ ≤ ‖T‖ * ρ + ‖T c + g‖ := by
        gcongr
        exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left hx' (norm_nonneg _))

/-- The linear field `F(t, x) = c x + g` is one-sided Lipschitz on every region with constant `c`,
of either sign; for `c < 0` it is dissipative. -/
example (c : ℝ) (g : E) (D : Set (ℝ × E)) :
    IsOneSidedLipschitzFieldOn (fun _ x => c • x + g) D c := fun _ x y _ _ => by
  rw [add_sub_add_right_eq_sub, ← smul_sub, real_inner_smul_left, real_inner_self_eq_norm_sq]

end RegionInner

end LeanDLRA
