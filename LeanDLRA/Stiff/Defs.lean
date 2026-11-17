import LeanDLRA.Integrators.Defs
import LeanDLRA.LinearAlgebra.Frobenius.Defs

/-!
# Implicit low-rank integrators: definitions

The step of the fixed-rank basis-update & Galerkin (BUG) integrator with backward Euler substeps
for matrices, at the level of the factors (`MatrixImplicitBUG.IsStep`), and its step relation
(`MatrixImplicitBUG.stepRel`). The theorems about them are in
`LeanDLRA/Stiff/ImplicitBUGStep.lean` (locality, local error, existence of a step) and
`LeanDLRA/Stiff/ImplicitBUGRun.lean` (runs and their error bound). The error analysis at the
level of orthogonal projectors is in `LeanDLRA/Stiff/ImplicitBUG.lean`.

## Main definitions

* `MatrixImplicitBUG.IsStep F t₀ t₁ U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁`: one step from `U₀ S₀ V₀ᵀ` to
  `U₁ S₁ V₁ᵀ`: backward Euler K-, L- and S-steps whose solutions are the limits of the
  fixed-point iterations from the start values, and new bases that contain the results of the
  K- and L-step.
* `MatrixImplicitBUG.stepRel F r`: the step relation of the rank-`r` integrator.

## Implementation notes

The stage equations of a backward Euler step can have several solutions. For a field that is
Lipschitz and bounded only near a reference solution, a solution far away from the start value
carries no information. The step therefore asks for the solution that the fixed-point iteration
`K ↦ U₀ S₀ + h F(t₁, K V₀ᵀ) V₀` reaches from `U₀ S₀`, and likewise for the L- and S-step. For a
field that is Lipschitz with constant `L` on the whole space and `h L < 1` the iteration is a
contraction, and its limit is the only solution of the stage equation
(`MatrixImplicitBUG.IsStep.of_lipschitz`): the condition then asks nothing beyond the equations.
The stage equations are stated explicitly as well, so that no continuity of the field is needed
to use them.

## References

* [CerutiLubich2022] for the fixed-rank BUG integrator; backward Euler substeps as in the
  BE-BUG integrator of arXiv 2610.18419, Algorithm 3.1.
-/

open Filter Topology
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixImplicitBUG

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}

/-- **One step of the fixed-rank BUG integrator with backward Euler substeps, at the level of
the factors.** The start value is `Y₀ = U₀ S₀ V₀ᵀ` with orthonormal `U₀`, `V₀`, the step size is
`h = t₁ - t₀`, and the field is evaluated at the end time `t₁`.

* K-step: `K₁ = U₀ S₀ + h F(t₁, K₁ V₀ᵀ) V₀`, and `K₁` is the limit of the fixed-point iteration
  of this equation started at `U₀ S₀`.
* L-step: `L₁ = V₀ S₀ᵀ + h F(t₁, U₀ L₁ᵀ)ᵀ U₀`, and `L₁` is the limit of the fixed-point iteration
  started at `V₀ S₀ᵀ`.
* New bases: `U₁`, `V₁` have orthonormal columns, the range of `U₁` contains the columns of `K₁`
  and the range of `V₁` those of `L₁` (QR steps).
* S-step (Galerkin): `S₁ = U₁ᵀ (Y₀ + h F(t₁, U₁ S₁ V₁ᵀ)) V₁`, and `S₁` is the limit of the
  fixed-point iteration started at `U₁ᵀ U₀ S₀ V₀ᵀ V₁`.

The result of the step is `U₁ S₁ V₁ᵀ`. The predicate contains the algorithm only; the bounds of
the error analysis are hypotheses of the theorems. -/
structure IsStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ) (U₀ : Matrix m (Fin r) ℝ)
    (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ) (K₁ : Matrix m (Fin r) ℝ)
    (L₁ : Matrix n (Fin r) ℝ) (U₁ : Matrix m (Fin r) ℝ) (V₁ : Matrix n (Fin r) ℝ)
    (S₁ : Matrix (Fin r) (Fin r) ℝ) : Prop where
  /-- The old column basis is orthonormal. -/
  orthU₀ : U₀ᵀ * U₀ = 1
  /-- The old row basis is orthonormal. -/
  orthV₀ : V₀ᵀ * V₀ = 1
  /-- Backward Euler K-step. -/
  kStep : K₁ = U₀ * S₀ + (t₁ - t₀) • (F t₁ (K₁ * V₀ᵀ) * V₀)
  /-- The K-stage is the limit of the fixed-point iteration started at `U₀ S₀`. -/
  kIter : Tendsto (fun j => (fun K => U₀ * S₀ + (t₁ - t₀) • (F t₁ (K * V₀ᵀ) * V₀))^[j]
    (U₀ * S₀)) atTop (𝓝 K₁)
  /-- Backward Euler L-step. -/
  lStep : L₁ = V₀ * S₀ᵀ + (t₁ - t₀) • ((F t₁ (U₀ * L₁ᵀ))ᵀ * U₀)
  /-- The L-stage is the limit of the fixed-point iteration started at `V₀ S₀ᵀ`. -/
  lIter : Tendsto (fun j => (fun L => V₀ * S₀ᵀ + (t₁ - t₀) • ((F t₁ (U₀ * Lᵀ))ᵀ * U₀))^[j]
    (V₀ * S₀ᵀ)) atTop (𝓝 L₁)
  /-- The new column basis is orthonormal. -/
  orthU₁ : U₁ᵀ * U₁ = 1
  /-- The range of the new column basis contains the columns of `K₁`. -/
  kCap : U₁ * U₁ᵀ * K₁ = K₁
  /-- The new row basis is orthonormal. -/
  orthV₁ : V₁ᵀ * V₁ = 1
  /-- The range of the new row basis contains the columns of `L₁`. -/
  lCap : V₁ * V₁ᵀ * L₁ = L₁
  /-- Backward Euler Galerkin S-step. -/
  sStep : S₁ = U₁ᵀ * (U₀ * S₀ * V₀ᵀ + (t₁ - t₀) • F t₁ (U₁ * S₁ * V₁ᵀ)) * V₁
  /-- The S-stage is the limit of the fixed-point iteration started at `U₁ᵀ U₀ S₀ V₀ᵀ V₁`. -/
  sIter : Tendsto (fun j => (fun S => U₁ᵀ * (U₀ * S₀ * V₀ᵀ + (t₁ - t₀) •
    F t₁ (U₁ * S * V₁ᵀ)) * V₁)^[j] (U₁ᵀ * U₀ * S₀ * (V₀ᵀ * V₁))) atTop (𝓝 S₁)

/-- **The step relation of the rank-`r` BUG integrator with backward Euler substeps.**
`stepRel F r t₀ t₁ Y₀ Y₁` holds if `Y₀ = U₀ S₀ V₀ᵀ` for some factors with orthonormal `U₀`, `V₀`
and `Y₁ = U₁ S₁ V₁ᵀ` is the result of a step (`MatrixImplicitBUG.IsStep`) over `[t₀, t₁]`
started from these factors. The relation contains no constants of the error analysis. -/
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
      (K₁ : Matrix m (Fin r) ℝ) (L₁ : Matrix n (Fin r) ℝ) (U₁ : Matrix m (Fin r) ℝ)
      (V₁ : Matrix n (Fin r) ℝ) (S₁ : Matrix (Fin r) (Fin r) ℝ),
      Y₀ = U₀ * S₀ * V₀ᵀ ∧ IsStep F t₀ t₁ U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ ∧ Y₁ = U₁ * S₁ * V₁ᵀ

end MatrixImplicitBUG

end LeanDLRA
