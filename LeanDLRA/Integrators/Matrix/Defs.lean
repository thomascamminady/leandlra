import LeanDLRA.LinearAlgebra.Frobenius.Defs
import Mathlib.Order.Interval.Set.Defs

/-!
# Definitions: normal-component bounds for matrix integrators

The vocabulary of the matrix integrator layer (`Integrators/Matrix/`). The error of dynamical
low-rank approximation is controlled by the size `ε` of the part of the vector field `F` that is
normal to the manifold of rank-`r` matrices. For `Y = U S Vᵀ` with orthonormal `U`, `V` and
invertible `S`, the normal part of `Z` at `Y` is `(I - U Uᵀ) Z (I - V Vᵀ)`; the bounds below ask
this doubly-normal part of `F(t, U S Vᵀ)` to be at most `ε`, for all factors (global form) or for
factors near a given matrix (localized form). Both are stated for arbitrary, possibly singular,
`S`.

The theorems that use these bounds are in `LeanDLRA/Integrators/Matrix/BUG.lean` (error of the
matrix BUG integrator) and `LeanDLRA/Matrix/LowRankDistance.lean` (robust capture of the exact
flow).

## Main definitions

* `LeanDLRA.MatrixBUG.FactoredNormalBound F r ε`: `‖(I - U Uᵀ) F(t, U S Vᵀ) (I - V Vᵀ)‖ ≤ ε` for
  all `t`, all `U : m × r`, `V : n × r` with orthonormal columns and all `S : r × r`.
* `LeanDLRA.NearNormalBound F r ε t₀ t₁ Y ρ`: the same for `t ∈ [t₀, t₁]` and factors with
  `‖U S Vᵀ - Y‖ ≤ ρ` only.

## Main results

* `LeanDLRA.nearNormalBound_of_factored`: the global bound implies the localized one.

## References

* [CerutiLubich2022, Thm. 2]
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixBUG

section NormalBound

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The **factored normal-component assumption** at rank `r` (assumption 2 of
[CerutiLubich2022, Thm. 2], in factored global form):

    ∀ t U V S, Uᵀ U = 1 → Vᵀ V = 1 → ‖(I - U Uᵀ) F(t, U S Vᵀ) (I - V Vᵀ)‖ ≤ ε

for `U : m × r`, `V : n × r`, `S : r × r`. For `Y = U S Vᵀ` with invertible `S`,
`(I - U Uᵀ) Z (I - V Vᵀ) = (I - P(Y)) Z` is the normal part of `Z` at `Y ∈ M_r`. -/
def FactoredNormalBound (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) (ε : ℝ) : Prop :=
  ∀ t (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ),
    Uᵀ * U = 1 → Vᵀ * V = 1 → ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε

end NormalBound

end MatrixBUG

section NearNormalBound

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}

/-- The **localized factored normal-component assumption**: on `[t₀, t₁]`, the doubly-normal
part `(I - U Uᵀ) F(t, U S Vᵀ) (I - V Vᵀ)` is `ε`-small at all points `U S Vᵀ` (orthonormal
`U : m × r`, `V : n × r`, arbitrary `S`) within distance `ρ` of `Y`. This is assumption 2 of
[CerutiLubich2022, Thm. 2] ("for `Y ∈ M_r` in a neighbourhood of `A(t)`"), imposed only near
the starting value; `MatrixBUG.FactoredNormalBound` is the global version. -/
def NearNormalBound (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) (ε t₀ t₁ : ℝ)
    (Y : Matrix m n ℝ) (ρ : ℝ) : Prop :=
  ∀ t ∈ Icc t₀ t₁, ∀ (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ)
    (S : Matrix (Fin r) (Fin r) ℝ), Uᵀ * U = 1 → Vᵀ * V = 1 → ‖U * S * Vᵀ - Y‖ ≤ ρ →
      ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε

/-- The global factored assumption implies the localized one. -/
theorem nearNormalBound_of_factored {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {ε : ℝ} (hε : MatrixBUG.FactoredNormalBound F r ε) (t₀ t₁ : ℝ) (Y : Matrix m n ℝ) (ρ : ℝ) :
    NearNormalBound F r ε t₀ t₁ Y ρ :=
  fun t _ U V S hU hV _ => hε t U V S hU hV

end NearNormalBound

/-! ### Non-vacuity -/

/-- The identity field `F(t, Y) = Y` has no normal component at any `U S Vᵀ`, so it satisfies the
factored normal-component assumption with `ε = 0`. -/
example (r : ℕ) :
    MatrixBUG.FactoredNormalBound (fun _ (Y : Matrix (Fin 3) (Fin 2) ℝ) => Y) r 0 := by
  intro t U V S hU hV
  have h : U * Uᵀ * (U * S * Vᵀ) = U * S * Vᵀ := by
    rw [show U * Uᵀ * (U * S * Vᵀ) = U * (Uᵀ * U) * S * Vᵀ by simp only [Matrix.mul_assoc], hU,
      Matrix.mul_one]
  simp [Matrix.sub_mul, h]

/-- The localized assumption follows for every `Y`, `ρ`. -/
example (r : ℕ) (Y₀ : Matrix (Fin 3) (Fin 2) ℝ) :
    NearNormalBound (fun _ (Y : Matrix (Fin 3) (Fin 2) ℝ) => Y) r 0 0 1 Y₀ 1 := by
  refine nearNormalBound_of_factored (fun t U V S hU hV => ?_) 0 1 Y₀ 1
  have h : U * Uᵀ * (U * S * Vᵀ) = U * S * Vᵀ := by
    rw [show U * Uᵀ * (U * S * Vᵀ) = U * (Uᵀ * U) * S * Vᵀ by simp only [Matrix.mul_assoc], hU,
      Matrix.mul_one]
  simp [Matrix.sub_mul, h]

end LeanDLRA
