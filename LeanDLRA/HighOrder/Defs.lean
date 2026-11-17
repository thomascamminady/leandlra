import LeanDLRA.Integrators.Defs
import LeanDLRA.Integrators.Matrix.BUG
import LeanDLRA.LinearAlgebra.LowRank.Defs

/-!
# Definitions: high-order integrators for matrices

The step of the midpoint basis-update & Galerkin (BUG) integrator for matrices, at the level
of the factors and as a relation between the old and the new value. The theorems on these
definitions are in `LeanDLRA/HighOrder/MidpointBUGStep.lean`.

## Main definitions

* `LeanDLRA.MatrixMidpointBUG.IsStep`: one step at the level of the factors, without
  truncation.
* `LeanDLRA.MatrixMidpointBUG.augmentedRel`: the step without truncation as a `StepRel`.
* `LeanDLRA.MatrixMidpointBUG.stepRel`: the step with truncation to rank `r` as a `StepRel`.

## References

* [CerutiEtAl2024b]
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixMidpointBUG

section Step

variable {m n k k' l l' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k'] [Fintype l]
  [Fintype l'] [DecidableEq k] [DecidableEq k'] [DecidableEq l] [DecidableEq l'] {r : ℕ}

/-- **One step of the midpoint BUG integrator at the level of the factors** (Ceruti, Einkemmer,
Kusch and Lubich, [CerutiEtAl2024b, §3], Algorithm 1, steps 1 and 2) from `Y₀ = U₀ S₀ V₀ᵀ` at
`t₀` to `t₁`, without truncation. With `t½ = (t₀ + t₁) / 2`:

* `half`: an augmented BUG step over `[t₀, t½]` without truncation, with bases `Uh`, `Vh`; its
  result is the midpoint predictor `Yh = Uh Sh(t½) Vhᵀ`;
* the bases `Ub`, `Vb` have orthonormal columns, the range of `Ub` contains the columns of `Uh`
  and of `F(t½, Yh) Vh`, the range of `Vb` those of `Vh` and of `F(t½, Yh)ᵀ Uh`;
* `Sb` solves the Galerkin equation `Sb' = Ubᵀ F(t, Ub Sb Vbᵀ) Vb` on `[t₀, t₁]` with
  `Sb(t₀) = Ubᵀ U₀ S₀ V₀ᵀ Vb`.

The result of the step is `Ub Sb(t₁) Vbᵀ`. The bases are any orthonormal bases whose ranges
contain the named columns; the algorithm takes orthonormal bases of the spans. -/
structure IsStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ) (U₀ : Matrix m (Fin r) ℝ)
    (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ) (Uh : Matrix m k ℝ)
    (Vh : Matrix n k' ℝ) (K : ℝ → Matrix m (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ)
    (Sh : ℝ → Matrix k k' ℝ) (Ub : Matrix m l ℝ) (Vb : Matrix n l' ℝ) (Sb : ℝ → Matrix l l' ℝ) :
    Prop where
  /-- The augmented BUG half step over `[t₀, (t₀ + t₁) / 2]`, without truncation. -/
  half : MatrixBUG.IsRankAdaptiveStep F 0 t₀ ((t₀ + t₁) / 2) U₀ S₀ V₀ Uh Vh K Lf Sh
    (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ)
  orthUb : Ubᵀ * Ub = 1
  orthVb : Vbᵀ * Vb = 1
  /-- The range of `Ub` contains the columns of `Uh`. -/
  capU : Ub * Ubᵀ * Uh = Uh
  /-- The range of `Vb` contains the columns of `Vh`. -/
  capV : Vb * Vbᵀ * Vh = Vh
  /-- The range of `Ub` contains the columns of `F(t½, Yh) Vh`. -/
  capF : Ub * Ubᵀ * (F ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ) * Vh) =
    F ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ) * Vh
  /-- The range of `Vb` contains the columns of `F(t½, Yh)ᵀ Uh`. -/
  capFt : Vb * Vbᵀ * ((F ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ))ᵀ * Uh) =
    (F ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ))ᵀ * Uh
  /-- The Galerkin step `Sb' = Ubᵀ F(t, Ub Sb Vbᵀ) Vb` on the whole step. -/
  sSol : ODESolution (MatrixBUG.sField Ub Vb F) Sb t₀ t₁
  /-- `Sb(t₀) = Ubᵀ U₀ S₀ V₀ᵀ Vb`. -/
  sStart : Sb t₀ = Ubᵀ * U₀ * S₀ * (V₀ᵀ * Vb)

end Step

section Rel

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}

/-- **The midpoint BUG step without truncation, as a relation between matrices.**
`augmentedRel F r t₀ t₁ Y₀ Ȳ` holds if `Y₀ = U₀ S₀ V₀ᵀ` for factors with `r` columns and
orthonormal `U₀`, `V₀`, and `Ȳ = Ub Sb(t₁) Vbᵀ` for a step `MatrixMidpointBUG.IsStep` of these
factors over `[t₀, t₁]` in which the half step has exactly `2 r` columns and the Galerkin bases
`Ub`, `Vb` have at most `4 r` columns ([CerutiEtAl2024b, §3], Algorithm 1 (4r), before the
truncation). When the columns of `(K(t½), U₀)` span less than `2 r` dimensions, the bases of the
half step are completed by further orthonormal columns. -/
def augmentedRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
      (Uh : Matrix m (Fin (2 * r)) ℝ) (Vh : Matrix n (Fin (2 * r)) ℝ)
      (K : ℝ → Matrix m (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ)
      (Sh : ℝ → Matrix (Fin (2 * r)) (Fin (2 * r)) ℝ) (l l' : ℕ) (Ub : Matrix m (Fin l) ℝ)
      (Vb : Matrix n (Fin l') ℝ) (Sb : ℝ → Matrix (Fin l) (Fin l') ℝ),
      Y₀ = U₀ * S₀ * V₀ᵀ ∧ l ≤ 4 * r ∧ l' ≤ 4 * r ∧
        IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb ∧ Y₁ = Ub * Sb t₁ * Vbᵀ

/-- **The step of the fixed-rank midpoint BUG integrator, as a relation between matrices**
([CerutiEtAl2024b, §3], Algorithm 1 (4r), with truncation to rank `r`). `stepRel F r t₀ t₁ Y₀ Y₁`
holds if `Y₁` is a best approximation of rank at most `r` to a result `Ȳ` of the step without
truncation from `Y₀` over `[t₀, t₁]` (`MatrixMidpointBUG.augmentedRel`): `Y₁` has rank at most
`r`, and `‖Y₁ - Ȳ‖` is at most the distance `distLR r Ȳ` of `Ȳ` to the matrices of rank at most
`r`. The relation contains every truncation with this property, in particular the truncated
singular value decomposition of `Ȳ` (`MatrixMidpointBUG.augmentedRel.stepRel_truncation`). -/
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ => ∃ Yh : Matrix m n ℝ, augmentedRel F r t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧
    ‖Y₁ - Yh‖ ≤ distLR r Yh

end Rel

end MatrixMidpointBUG

end LeanDLRA
