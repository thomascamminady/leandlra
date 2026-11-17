import LeanDLRA.Integrators.Defs
import LeanDLRA.Integrators.Matrix.BUG
import LeanDLRA.LinearAlgebra.LowRank.Defs

/-!
# Definitions: high-order integrators for matrices

The step of the midpoint basis-update & Galerkin (BUG) integrator for matrices, at the level
of the factors and as a relation between the old and the new value, and the step of the
projected Runge–Kutta methods and of the explicit midpoint method in augmented bases for
matrices. The theorems on these definitions are in `LeanDLRA/HighOrder/MidpointBUGStep.lean`,
`LeanDLRA/Integrators/Matrix/ProjectedRK.lean` and `LeanDLRA/Research/ExplicitMidpointRun.lean`.

## Main definitions

* `LeanDLRA.MatrixMidpointBUG.IsStep`: one step at the level of the factors, without
  truncation.
* `LeanDLRA.MatrixMidpointBUG.augmentedRel`: the step without truncation as a `StepRel`.
* `LeanDLRA.MatrixMidpointBUG.stepRel`: the step with truncation to rank `r` as a `StepRel`.
* `LeanDLRA.MatrixPRK.stageDeriv`, `LeanDLRA.MatrixPRK.stageSum`, `LeanDLRA.MatrixPRK.stepRel`:
  the projected stage derivative, the argument of a retraction and the step relation of the
  projected Runge–Kutta methods.
* `LeanDLRA.ExplicitMidpoint.augmentedRel`: the explicit midpoint step in bases with `2 r`
  columns, without truncation, as a `StepRel`.
* `LeanDLRA.ExplicitMidpoint.stepRel`: the same step followed by a best approximation of rank
  `r`.

## References

* [CerutiEtAl2024b]
* [KieriVandereycken2019]
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

/-! ### The step of the projected Runge–Kutta methods -/

namespace MatrixPRK

section Rel

variable {m n : Type*} [Fintype m] [Fintype n] {r s : ℕ}

/-- The **projected stage derivative** `P(η_l) F(t₀ + c_l h, η_l)` at the stage
`η_l = U_l S_l V_lᵀ`, with the tangent projector `P(η_l) = tangentProj U_l V_l`. -/
noncomputable def stageDeriv (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (c : Fin s → ℝ) (t₀ h : ℝ)
    (U : Fin s → Matrix m (Fin r) ℝ) (S : Fin s → Matrix (Fin r) (Fin r) ℝ)
    (V : Fin s → Matrix n (Fin r) ℝ) (l : Fin s) : Matrix m n ℝ :=
  tangentProj (U l) (V l) (F (t₀ + c l * h) (U l * S l * (V l)ᵀ))

/-- The **argument of a retraction** in a projected Runge–Kutta step:
`Y₀ + h ∑_l w_l P(η_l) F(t₀ + c_l h, η_l)` with weights `w` (a row of `a`, or `b`). -/
noncomputable def stageSum (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (c : Fin s → ℝ) (t₀ h : ℝ)
    (Y₀ : Matrix m n ℝ) (w : Fin s → ℝ) (U : Fin s → Matrix m (Fin r) ℝ)
    (S : Fin s → Matrix (Fin r) (Fin r) ℝ) (V : Fin s → Matrix n (Fin r) ℝ) : Matrix m n ℝ :=
  Y₀ + h • ∑ l, w l • stageDeriv F c t₀ h U S V l

/-- **One step of the projected Runge–Kutta method** ([KieriVandereycken2019], eqs. (26),
(27)) with tableau `(a, b, c)` and a `κ`-quasi-optimal retraction to rank `r`:
`stepRel F r κ a b c t₀ t₁ Y₀ Y₁` holds if there are stages `η_j = U_j S_j V_jᵀ` with orthonormal
`U_j`, `V_j` such that, with `h = t₁ - t₀` and the projected stage derivatives
`d_l = stageDeriv F c t₀ h U S V l`, each `η_j` is `κ`-quasi-optimal for
`Y₀ + h ∑_l a_{jl} d_l` (`stageSum F c t₀ h Y₀ (a j) U S V`), and `Y₁` has rank at most `r` and
is `κ`-quasi-optimal for `Y₀ + h ∑_j b_j d_j`. For an explicit tableau the stages are
determined one after the other (`MatrixPRK.exists_stepRel`); the relation allows every choice of
best approximations and of factorizations. -/
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) (κ : ℝ) (a : Fin s → Fin s → ℝ)
    (b c : Fin s → ℝ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ => ∃ (U : Fin s → Matrix m (Fin r) ℝ) (S : Fin s → Matrix (Fin r) (Fin r) ℝ)
    (V : Fin s → Matrix n (Fin r) ℝ), (∀ j, (U j)ᵀ * U j = 1 ∧ (V j)ᵀ * V j = 1) ∧
    (∀ j, ‖U j * S j * (V j)ᵀ - stageSum F c t₀ (t₁ - t₀) Y₀ (a j) U S V‖ ≤
      κ * distLR r (stageSum F c t₀ (t₁ - t₀) Y₀ (a j) U S V)) ∧
    Y₁.rank ≤ r ∧
    ‖Y₁ - stageSum F c t₀ (t₁ - t₀) Y₀ b U S V‖ ≤
      κ * distLR r (stageSum F c t₀ (t₁ - t₀) Y₀ b U S V)

end Rel

end MatrixPRK

namespace ExplicitMidpoint

section Rel

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **The explicit midpoint step in augmented bases, without truncation, as a relation between
matrices.** `augmentedRel F r t₀ t₁ Y₀ Ȳ` holds if, with `h = t₁ - t₀`,

* `Y₀ = U₀ S₀ V₀ᵀ` with `r` orthonormal columns in `U₀` and in `V₀`;
* `Z = Y₀ + (h/2) P₀ F(t₀, Y₀)` is the explicit predictor, with the tangent projector
  `P₀ = tangentProj U₀ V₀`, and `G = F(t₀ + h/2, Z)`;
* `Ua`, `Va` have `2 r` orthonormal columns, the range of `Ua` contains the columns of `U₀` and
  of `G V₀`, and the range of `Va` those of `V₀` and of `Gᵀ U₀`;
* `Ȳ = Y₀ + h Ua Uaᵀ G Va Vaᵀ` (`galerkinProj Ua Va`).

The step evaluates `F` twice and solves no differential equation; `Ȳ` has rank at most `2 r`.
The bases are any orthonormal bases with these properties, and the factorization of `Y₀` is any
factorization with orthonormal `U₀`, `V₀`. -/
def augmentedRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
      (Ua : Matrix m (Fin (2 * r)) ℝ) (Va : Matrix n (Fin (2 * r)) ℝ) (Z G : Matrix m n ℝ),
      U₀ᵀ * U₀ = 1 ∧ V₀ᵀ * V₀ = 1 ∧ Y₀ = U₀ * S₀ * V₀ᵀ ∧
      Z = Y₀ + ((t₁ - t₀) / 2) • tangentProj U₀ V₀ (F t₀ Y₀) ∧
      G = F (t₀ + (t₁ - t₀) / 2) Z ∧
      Uaᵀ * Ua = 1 ∧ Vaᵀ * Va = 1 ∧ Ua * Uaᵀ * U₀ = U₀ ∧ Va * Vaᵀ * V₀ = V₀ ∧
      Ua * Uaᵀ * (G * V₀) = G * V₀ ∧ Va * Vaᵀ * (Gᵀ * U₀) = Gᵀ * U₀ ∧
      Y₁ = Y₀ + (t₁ - t₀) • galerkinProj Ua Va G

/-- **The step of the explicit midpoint method with rank `r`, as a relation between matrices.**
`stepRel F r t₀ t₁ Y₀ Y₁` holds if `Y₁` is a best approximation of rank at most `r` to a result
`Ȳ` of the explicit midpoint step in augmented bases from `Y₀` over `[t₀, t₁]`
(`ExplicitMidpoint.augmentedRel`): `Y₁` has rank at most `r`, and `‖Y₁ - Ȳ‖` is at most the
distance `distLR r Ȳ` of `Ȳ` to the matrices of rank at most `r`. -/
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ => ∃ Yh : Matrix m n ℝ, augmentedRel F r t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧
    ‖Y₁ - Yh‖ ≤ distLR r Yh

end Rel

end ExplicitMidpoint

end LeanDLRA
