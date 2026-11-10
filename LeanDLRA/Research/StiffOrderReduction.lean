import LeanDLRA.Integrators.Matrix.BUGStep

/-!
# Order reduction of the BUG step for stiff problems: an exact family

One step of the BUG integrator, in the fixed-rank form `MatrixBUG.IsStep` and in the
rank-adaptive form `MatrixBUG.IsRankAdaptiveStep` (K-step, L-step, augmented bases, Galerkin
step), is applied to a stiff linear matrix differential equation `Y' = Y N + C`. The step starts
on the exact solution `A`, which has rank `r` at the start. The question is whether the error of
the step is bounded by `K (h ε + h²)`, where `h` is the step size and `ε` the norm of the normal
component of the field at the start, with a constant `K` that depends on the smoothness of the
exact solution but not on the norm of the stiff operator `N`.

This file gives a family of data for which every substep is known in closed form, and proves
that for this family the answer is no. The exact solution of every member of the family is
affine in time, with the same derivative of norm `√2`. Still, for every step size `h ≤ 1/2`
there are members with `ε ≤ h` for which the error of the step is at least `(√3 / 4) h`. So no
constant `K` works for the whole family (`StiffOrderReduction.Example.not_exists_uniform_bound`).
The only quantity that is not bounded over the family is `‖N‖`.

## Setting

The field is `F(t, Y) = Y N + C` (`StiffOrderReduction.field`), the start is `Y₀ = U₀ S₀ V₀ᵀ`,
and `D = Y₀ N + C = F(t₀, Y₀)`.

Assumptions on the data (`StiffOrderReduction.Data`):

* `V₀ᵀ N V₀ = -μ • 1` with `μ > 0` (the stiff operator compressed to the old row space is `-μ`),
* `D N = 0` (the derivative is in the kernel of the stiff operator).

Then the exact solution is `A(t) = Y₀ + t D` (`StiffOrderReduction.exact`,
`Data.odeSolution_exact`). It is affine in time, so `A' = D` and `A'' = 0`, and `A' N = 0`: the
quantities that describe its smoothness do not depend on `N`. The K-step is
`K(t) = U₀ S₀ + g(t) D V₀` with `g(t) = (1 - e^{-μ t}) / μ` (`StiffOrderReduction.damp`), the
L-step is `L(t) = V₀ S₀ᵀ + t Dᵀ U₀`.

Assumptions on the new bases `Û`, `V̂` (`StiffOrderReduction.Bases`): orthonormal columns, `Û`
captures `K(h)`, `V̂` captures `V₀` and `Dᵀ U₀` (hence `L(h)`), and the stiff operator sees of
`V̂` only the old directions: `N V̂ = N V₀ V₀ᵀ V̂`, `V̂ᵀ N V₀ = -μ V̂ᵀ V₀` (the directions added
to `V₀` are in the kernel of `N`). Then the Galerkin step in `Û`, `V̂` is

  `S(t) = Ûᵀ (K(t) V₀ᵀ V̂ + t D (V̂ - V₀ V₀ᵀ V̂))`.

## Main results

* `StiffOrderReduction.isRankAdaptiveStep`: the factor trajectories form a step
  `MatrixBUG.IsRankAdaptiveStep` (augmented bases of any width, truncation tolerance zero), with
  the result `Y₁ = Û S(h) V̂ᵀ`.
* `StiffOrderReduction.isStep`: if `Dᵀ U₀ = 0` they form a fixed-rank step `MatrixBUG.IsStep`
  with the new right basis `V₀`.
* `Data.rightProj_result_sub_exact`, `Data.le_norm_result_sub_exact`: with `Q₀ X = X V₀ V₀ᵀ`,
  the part of the error in the old row space is `Q₀ (Y₁ - A(h)) = -(h - g(h)) Q₀ D`, so that
  `‖Y₁ - A(h)‖ ≥ (h - 1/μ) ‖Q₀ D‖`.
* `Data.result_sub_exact`, `Data.norm_sq_result_sub_exact`: if `Û` also captures
  `D (V̂ - V₀ V₀ᵀ V̂)`, then with `Q̂ X = X V̂ V̂ᵀ`
  `Y₁ - A(h) = -(h - g(h)) Q₀ D - h (D - Q̂ D)` and
  `‖Y₁ - A(h)‖² = (h - g(h))² ‖Q₀ D‖² + h² ‖D - Q̂ D‖²`.
  The second term is the distance of `A(h)` from the Galerkin space. The first term is of the
  size `h ‖Q₀ A'‖` as soon as `h μ ≥ 2`, however small the normal component of the field is.
* `StiffOrderReduction.Example`: a `2 × 3` family of rank one with the parameters `c² + s² = 1`,
  `λ > 0` and `σ`, with augmented bases of width two, `μ = λ s²`, and a nonzero coupling of the
  stiff operator with the old row space (`Example.coupling_ne_zero`). It is a rank-adaptive step
  (`Example.isRankAdaptiveStep`) with `‖Y₁ - A(h)‖² = (h - g(h))² c² + h² s²`
  (`Example.norm_sq_result_sub_exact`), hence `‖Y₁ - A(h)‖ ≥ (h/2) |c|` for `λ s² h ≥ 2`
  (`Example.half_mul_le_norm_result_sub_exact`). The normal component of the field is `|s|`
  (`Example.norm_normal_field_start`), `‖A'‖² = 2` (`Example.norm_sq_D`), `‖N‖ = λ`
  (`Example.norm_sq_N`), and the best approximation of `A(h)` in the new row space has the error
  `|h| |s|` (`Example.norm_exact_sub_rightProj`).
* `Example.order_reduction_explicit`: for `0 < h ≤ 1/2`, `λ ≥ 2 / h³`, `s = √(2 / (h λ))` and
  `c = √(1 - s²)` the normal component of the field is at most `h` and the error is at least
  `(√3 / 4) h`, while `h ε + h² ≤ 2 h²`.
* `Example.not_exists_uniform_bound`: there is no `K` with `‖Y₁ - A(h)‖ ≤ K (h ε + h²)` for all
  members of the family and all `h ≤ 1/2`.
* `Example.norm_sq_C_scaled`, `Example.norm_start_mul_N_scaled`: with the start scaled as
  `σ = 1 / (λ s)` the forcing has norm `√3` and `‖A₀ N‖ = 1` for all members.
* `Example.exists_isStep_le_norm`: the lower bound `(h - 1/(λ s²)) |c|` for a fixed-rank step
  (a variant of the family in which the row basis does not change).

## Remarks on the hypotheses

* The statements are about one step with exact substeps that starts on the exact solution. In
  the rank-adaptive step the truncation tolerance is zero. Nothing is said about several steps.
* The family is special: the stiff operator acts from the right only, the forcing is constant,
  the rank is one. All norms are Frobenius norms.
* Only a constant that is uniform over the family is excluded. Bounds whose constants contain
  other quantities of the stiff operator, for example its compression to the bases of the step,
  are not excluded.

## Relation to the literature

The local error bound of this library for the BUG step, `MatrixBUG.IsStep.hasLocalError` (after
[CerutiLubich2022]; for the rank-adaptive integrator see [CerutiKuschLubich2022]), has the form
`h (c₁ ε + c₂ h)` with constants that depend on the Lipschitz constant and on a bound of the
whole field. For the fields of this file the Lipschitz constant is `‖N‖`. The statements of this
file are consistent with such bounds: they show that for this family the dependence of the
constant on `‖N‖` can not be replaced by a dependence on the smoothness of the exact solution
alone. The behaviour of low-rank integrators for stiff problems is discussed in
[CarrelVandereycken2023, §2.3].
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace StiffOrderReduction

open MatrixBUG

/-! ### The damping function -/

/-- `g(t) = (1 - e^{-μ t}) / μ`, the solution of `g' = 1 - μ g`, `g(0) = 0`. -/
noncomputable def damp (μ t : ℝ) : ℝ := (1 - Real.exp (-(μ * t))) / μ

@[simp] lemma damp_zero (μ : ℝ) : damp μ 0 = 0 := by simp [damp]

lemma one_sub_mul_damp {μ : ℝ} (hμ : μ ≠ 0) (t : ℝ) : 1 - μ * damp μ t = Real.exp (-(μ * t)) := by
  unfold damp
  field_simp
  ring

lemma hasDerivAt_damp {μ : ℝ} (hμ : μ ≠ 0) (t : ℝ) :
    HasDerivAt (damp μ) (Real.exp (-(μ * t))) t := by
  have h1 : HasDerivAt (fun s : ℝ => -(μ * s)) (-μ) t := by
    have h0 := (hasDerivAt_id' t).const_mul (-μ)
    simpa [neg_mul] using h0
  have h2 := (h1.exp.const_sub 1).div_const μ
  have h3 : -(Real.exp (-(μ * t)) * -μ) / μ = Real.exp (-(μ * t)) := by
    field_simp
  rw [h3] at h2
  exact h2

lemma damp_le_inv {μ : ℝ} (hμ : 0 < μ) (t : ℝ) : damp μ t ≤ 1 / μ := by
  unfold damp
  have := Real.exp_pos (-(μ * t))
  gcongr
  linarith

lemma damp_le_self {μ : ℝ} (hμ : 0 < μ) (t : ℝ) : damp μ t ≤ t := by
  unfold damp
  rw [div_le_iff₀ hμ]
  have := Real.add_one_le_exp (-(μ * t))
  linarith

/-! ### The family -/

section Family

variable {m n r k k' p : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

/-- The field `F(t, Y) = Y N + C`: a stiff linear part acting from the right and a constant
forcing. -/
def field (N : Matrix n n ℝ) (C : Matrix m n ℝ) : ℝ → Matrix m n ℝ → Matrix m n ℝ :=
  fun _ Y => Y * N + C

/-- The assumptions on the data. `D` is the value of the field at the start `U₀ S₀ V₀ᵀ`. -/
structure Data (U₀ : Matrix m r ℝ) (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) (N : Matrix n n ℝ)
    (C D : Matrix m n ℝ) (μ : ℝ) : Prop where
  orthU₀ : U₀ᵀ * U₀ = 1
  orthV₀ : V₀ᵀ * V₀ = 1
  pos : 0 < μ
  /-- The stiff operator compressed to the old row space is `-μ`. -/
  compr : V₀ᵀ * N * V₀ = -(μ • (1 : Matrix r r ℝ))
  /-- `D` is the field at the start. -/
  deriv : D = U₀ * S₀ * V₀ᵀ * N + C
  /-- `D` is in the kernel of the stiff operator. -/
  ker : D * N = 0

/-- The assumptions on the new bases `Û = Ua`, `V̂ = Va`; `K₁` is the value of the K-step at the
end of the step. -/
structure Bases [Fintype k] [DecidableEq k] [Fintype k'] [DecidableEq k'] (U₀ : Matrix m r ℝ)
    (V₀ : Matrix n r ℝ) (N : Matrix n n ℝ) (D : Matrix m n ℝ) (μ : ℝ) (K₁ : Matrix m r ℝ)
    (Ua : Matrix m k ℝ) (Va : Matrix n k' ℝ) : Prop where
  orthUa : Uaᵀ * Ua = 1
  /-- `Û` captures `K(h)`. -/
  kCap : Ua * Uaᵀ * K₁ = K₁
  orthVa : Vaᵀ * Va = 1
  /-- `V̂` captures `V₀`. -/
  augV : Va * Vaᵀ * V₀ = V₀
  /-- `V̂` captures the increment `Dᵀ U₀` of the L-step. -/
  lCap : Va * Vaᵀ * (Dᵀ * U₀) = Dᵀ * U₀
  /-- The stiff operator sees of `V̂` only the old directions. -/
  kerR : N * Va = N * V₀ * (V₀ᵀ * Va)
  /-- The same from the left. -/
  kerL : Vaᵀ * N * V₀ = -(μ • (Vaᵀ * V₀))

/-- The exact solution `A(t) = U₀ S₀ V₀ᵀ + t D`. -/
def exact (U₀ : Matrix m r ℝ) (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) (D : Matrix m n ℝ)
    (t : ℝ) : Matrix m n ℝ :=
  U₀ * S₀ * V₀ᵀ + t • D

/-- The K-step `K(t) = U₀ S₀ + g(t) D V₀`. -/
noncomputable def kTraj (U₀ : Matrix m r ℝ) (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ)
    (D : Matrix m n ℝ) (μ t : ℝ) : Matrix m r ℝ :=
  U₀ * S₀ + damp μ t • (D * V₀)

/-- The L-step `L(t) = V₀ S₀ᵀ + t Dᵀ U₀`. -/
def lTraj (U₀ : Matrix m r ℝ) (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) (D : Matrix m n ℝ)
    (t : ℝ) : Matrix n r ℝ :=
  V₀ * S₀ᵀ + t • (Dᵀ * U₀)

/-- The Galerkin step before the projection onto the new left basis:
`X(t) = K(t) V₀ᵀ V̂ + t D (V̂ - V₀ V₀ᵀ V̂)`; the S-step is `S(t) = Ûᵀ X(t)`. -/
noncomputable def xTraj (Va : Matrix n k' ℝ) (U₀ : Matrix m r ℝ) (S₀ : Matrix r r ℝ)
    (V₀ : Matrix n r ℝ) (D : Matrix m n ℝ) (μ t : ℝ) : Matrix m k' ℝ :=
  kTraj U₀ S₀ V₀ D μ t * (V₀ᵀ * Va) + t • (D * (Va - V₀ * (V₀ᵀ * Va)))

omit [Fintype m] [DecidableEq r] in
lemma kTraj_zero (U₀ : Matrix m r ℝ) (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) (D : Matrix m n ℝ)
    (μ : ℝ) : kTraj U₀ S₀ V₀ D μ 0 = U₀ * S₀ := by
  simp [kTraj]

variable {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ} {N : Matrix n n ℝ}
  {C D : Matrix m n ℝ} {μ : ℝ}

namespace Data

/-- `X V₀ᵀ N V₀ = -μ X`. -/
lemma mul_compr (hd : Data U₀ S₀ V₀ N C D μ) (X : Matrix p r ℝ) :
    X * V₀ᵀ * N * V₀ = -(μ • X) := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc V₀ᵀ, hd.compr, Matrix.mul_neg,
    Matrix.mul_smul, Matrix.mul_one]

/-- `C V₀ = D V₀ + μ U₀ S₀`. -/
lemma forcing_mul (hd : Data U₀ S₀ V₀ N C D μ) : C * V₀ = D * V₀ + μ • (U₀ * S₀) := by
  have h : D * V₀ = -(μ • (U₀ * S₀)) + C * V₀ := by
    rw [hd.deriv, Matrix.add_mul, hd.mul_compr]
  rw [h]
  module

/-- The field at the start is `D`. -/
lemma field_start (hd : Data U₀ S₀ V₀ N C D μ) (t : ℝ) : field N C t (U₀ * S₀ * V₀ᵀ) = D := by
  rw [hd.deriv]
  rfl

/-- **The exact solution** is `A(t) = Y₀ + t D`. -/
theorem odeSolution_exact (hd : Data U₀ S₀ V₀ N C D μ) (a b : ℝ) :
    ODESolution (field N C) (exact U₀ S₀ V₀ D) a b := by
  refine ODESolution.of_hasDerivAt (fun t => ?_) a b
  have h1 : HasDerivAt (fun s : ℝ => U₀ * S₀ * V₀ᵀ + s • D) ((1 : ℝ) • D) t :=
    ((hasDerivAt_id t).smul_const D).const_add _
  have h2 : field N C t (exact U₀ S₀ V₀ D t) = (1 : ℝ) • D := by
    simp only [field, exact, Matrix.add_mul, Matrix.smul_mul, hd.ker, smul_zero, add_zero,
      one_smul]
    exact hd.deriv.symm
  rw [h2]
  exact h1

/-- The K-step field along `K(t)` is `e^{-μ t} D V₀`. -/
lemma kField_kTraj (hd : Data U₀ S₀ V₀ N C D μ) (t : ℝ) :
    kField V₀ (field N C) t (kTraj U₀ S₀ V₀ D μ t) = Real.exp (-(μ * t)) • (D * V₀) := by
  have h : kField V₀ (field N C) t (kTraj U₀ S₀ V₀ D μ t)
      = -(μ • kTraj U₀ S₀ V₀ D μ t) + C * V₀ := by
    simp only [kField, field]
    rw [Matrix.add_mul, hd.mul_compr]
  rw [h, hd.forcing_mul, ← one_sub_mul_damp hd.pos.ne']
  unfold kTraj
  module

/-- **The K-step** `K' = F(t, K V₀ᵀ) V₀`. -/
theorem odeSolution_kTraj (hd : Data U₀ S₀ V₀ N C D μ) (a b : ℝ) :
    ODESolution (kField V₀ (field N C)) (kTraj U₀ S₀ V₀ D μ) a b := by
  refine ODESolution.of_hasDerivAt (fun t => ?_) a b
  rw [hd.kField_kTraj]
  exact ((hasDerivAt_damp hd.pos.ne' t).smul_const (D * V₀)).const_add _

/-- The L-step field along `L(t)` is `Dᵀ U₀`. -/
lemma lField_lTraj (hd : Data U₀ S₀ V₀ N C D μ) (t : ℝ) :
    lField U₀ (field N C) t (lTraj U₀ S₀ V₀ D t) = Dᵀ * U₀ := by
  have h : U₀ * (lTraj U₀ S₀ V₀ D t)ᵀ * N + C = D := by
    simp only [lTraj, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc, hd.ker, Matrix.mul_zero, smul_zero, add_zero]
    rw [hd.deriv]
    simp only [Matrix.mul_assoc]
  simp only [lField, field]
  rw [h]

/-- **The L-step** `L' = F(t, U₀ Lᵀ)ᵀ U₀`. -/
theorem odeSolution_lTraj (hd : Data U₀ S₀ V₀ N C D μ) (a b : ℝ) :
    ODESolution (lField U₀ (field N C)) (lTraj U₀ S₀ V₀ D) a b := by
  refine ODESolution.of_hasDerivAt (fun t => ?_) a b
  rw [hd.lField_lTraj]
  have h1 : HasDerivAt (fun s : ℝ => V₀ * S₀ᵀ + s • (Dᵀ * U₀)) ((1 : ℝ) • (Dᵀ * U₀)) t :=
    ((hasDerivAt_id t).smul_const _).const_add _
  rw [one_smul] at h1
  exact h1

section Aug

variable [Fintype k] [DecidableEq k] [Fintype k'] [DecidableEq k'] {K₁ : Matrix m r ℝ}
  {Ua : Matrix m k ℝ} {Va : Matrix n k' ℝ}

/-- `V₀ᵀ V̂ V̂ᵀ V₀ = 1`. -/
lemma gram (hd : Data U₀ S₀ V₀ N C D μ) (hb : Bases U₀ V₀ N D μ K₁ Ua Va) :
    V₀ᵀ * Va * (Vaᵀ * V₀) = 1 := by
  have h : V₀ᵀ * Va * (Vaᵀ * V₀) = V₀ᵀ * (Va * Vaᵀ * V₀) := by simp only [Matrix.mul_assoc]
  rw [h, hb.augV, hd.orthV₀]

/-- `X(t) V̂ᵀ V₀ = K(t)`. -/
lemma xTraj_mul (hd : Data U₀ S₀ V₀ N C D μ) (hb : Bases U₀ V₀ N D μ K₁ Ua Va) (t : ℝ) :
    xTraj Va U₀ S₀ V₀ D μ t * (Vaᵀ * V₀) = kTraj U₀ S₀ V₀ D μ t := by
  have h0 : (Va - V₀ * (V₀ᵀ * Va)) * (Vaᵀ * V₀) = 0 := by
    rw [Matrix.sub_mul, ← Matrix.mul_assoc Va, hb.augV, Matrix.mul_assoc V₀, hd.gram hb,
      Matrix.mul_one, sub_self]
  rw [xTraj, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc (kTraj U₀ S₀ V₀ D μ t),
    hd.gram hb, Matrix.mul_one, Matrix.mul_assoc D, h0, Matrix.mul_zero, smul_zero, add_zero]

omit [DecidableEq r] in
/-- The stiff operator compressed to the new row space. -/
lemma compr_aug (hb : Bases U₀ V₀ N D μ K₁ Ua Va) :
    Vaᵀ * N * Va = -(μ • (Vaᵀ * V₀ * (V₀ᵀ * Va))) := by
  have h : Vaᵀ * N * Va = Vaᵀ * N * V₀ * (V₀ᵀ * Va) := by
    rw [Matrix.mul_assoc Vaᵀ N Va, hb.kerR]
    simp only [Matrix.mul_assoc]
  rw [h, hb.kerL, Matrix.neg_mul, Matrix.smul_mul]

/-- `X(t) V̂ᵀ N V̂ = -μ K(t) V₀ᵀ V̂`. -/
lemma xTraj_mul_compr (hd : Data U₀ S₀ V₀ N C D μ) (hb : Bases U₀ V₀ N D μ K₁ Ua Va) (t : ℝ) :
    xTraj Va U₀ S₀ V₀ D μ t * (Vaᵀ * N * Va) = -(μ • (kTraj U₀ S₀ V₀ D μ t * (V₀ᵀ * Va))) := by
  rw [compr_aug hb, Matrix.mul_neg, Matrix.mul_smul, ← Matrix.mul_assoc, hd.xTraj_mul hb]

/-- `C V̂ = D V̂ + μ U₀ S₀ V₀ᵀ V̂`. -/
lemma forcing_mul_aug (hd : Data U₀ S₀ V₀ N C D μ) (hb : Bases U₀ V₀ N D μ K₁ Ua Va) :
    C * Va = D * Va + μ • (U₀ * S₀ * (V₀ᵀ * Va)) := by
  have h1 : U₀ * S₀ * V₀ᵀ * N * Va = -(μ • (U₀ * S₀ * (V₀ᵀ * Va))) := by
    have e : U₀ * S₀ * V₀ᵀ * N * Va = U₀ * S₀ * V₀ᵀ * N * V₀ * (V₀ᵀ * Va) := by
      rw [Matrix.mul_assoc (U₀ * S₀ * V₀ᵀ) N Va, hb.kerR]
      simp only [Matrix.mul_assoc]
    rw [e, hd.mul_compr, Matrix.neg_mul, Matrix.smul_mul]
  have h2 : D * Va = -(μ • (U₀ * S₀ * (V₀ᵀ * Va))) + C * Va := by
    rw [hd.deriv, Matrix.add_mul, h1]
  rw [h2]
  module

/-- The S-step field along `S(t) = Ûᵀ X(t)`. -/
lemma sField_sTraj (hd : Data U₀ S₀ V₀ N C D μ) (hb : Bases U₀ V₀ N D μ K₁ Ua Va) (t : ℝ) :
    sField Ua Va (field N C) t (Uaᵀ * xTraj Va U₀ S₀ V₀ D μ t)
      = Uaᵀ * (Real.exp (-(μ * t)) • (D * V₀ * (V₀ᵀ * Va)) + D * (Va - V₀ * (V₀ᵀ * Va))) := by
  simp only [sField, field]
  have e1 : Uaᵀ * (Ua * (Uaᵀ * xTraj Va U₀ S₀ V₀ D μ t) * Vaᵀ * N + C) * Va
      = Uaᵀ * Ua * (Uaᵀ * (xTraj Va U₀ S₀ V₀ D μ t * (Vaᵀ * N * Va))) + Uaᵀ * (C * Va) := by
    rw [Matrix.mul_add, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
  rw [e1, hb.orthUa, Matrix.one_mul, hd.xTraj_mul_compr hb, hd.forcing_mul_aug hb,
    ← Matrix.mul_add]
  congr 1
  rw [← one_sub_mul_damp hd.pos.ne' t, kTraj, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_sub,
    ← Matrix.mul_assoc D V₀]
  module

/-- **The Galerkin step** with the bases `Û`, `V̂` is `S(t) = Ûᵀ X(t)`. -/
theorem odeSolution_sTraj (hd : Data U₀ S₀ V₀ N C D μ) (hb : Bases U₀ V₀ N D μ K₁ Ua Va)
    (a b : ℝ) :
    ODESolution (sField Ua Va (field N C)) (fun t => Uaᵀ * xTraj Va U₀ S₀ V₀ D μ t) a b := by
  refine ODESolution.of_hasDerivAt (fun t => ?_) a b
  rw [hd.sField_sTraj hb]
  have h1 : HasDerivAt (fun s : ℝ => Uaᵀ * (U₀ * S₀ * (V₀ᵀ * Va))
        + (damp μ s • (Uaᵀ * (D * V₀ * (V₀ᵀ * Va)))
          + s • (Uaᵀ * (D * (Va - V₀ * (V₀ᵀ * Va))))))
      (Real.exp (-(μ * t)) • (Uaᵀ * (D * V₀ * (V₀ᵀ * Va)))
        + (1 : ℝ) • (Uaᵀ * (D * (Va - V₀ * (V₀ᵀ * Va))))) t :=
    (((hasDerivAt_damp hd.pos.ne' t).smul_const _).add
      ((hasDerivAt_id t).smul_const _)).const_add _
  have h2 : (fun s => Uaᵀ * xTraj Va U₀ S₀ V₀ D μ s)
      = fun s : ℝ => Uaᵀ * (U₀ * S₀ * (V₀ᵀ * Va))
        + (damp μ s • (Uaᵀ * (D * V₀ * (V₀ᵀ * Va)))
          + s • (Uaᵀ * (D * (Va - V₀ * (V₀ᵀ * Va))))) := by
    funext s
    rw [xTraj, kTraj, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_add,
      Matrix.mul_smul, Matrix.mul_smul, add_assoc]
  rw [h2, Matrix.mul_add, Matrix.mul_smul]
  rw [one_smul] at h1
  exact h1

omit [DecidableEq r] in
/-- `V₀ᵀ V̂ V̂ᵀ = V₀ᵀ`. -/
lemma transpose_augV (hb : Bases U₀ V₀ N D μ K₁ Ua Va) : V₀ᵀ * (Va * Vaᵀ) = V₀ᵀ := by
  have h := congrArg Matrix.transpose hb.augV
  simpa [Matrix.transpose_mul, Matrix.mul_assoc] using h

/-- The old right basis is admissible as the new right basis if `Dᵀ U₀ = 0` (then the L-step is
stationary). -/
lemma bases_self (hd : Data U₀ S₀ V₀ N C D μ) (hleft : Dᵀ * U₀ = 0) (hU : Uaᵀ * Ua = 1)
    (hcap : Ua * Uaᵀ * K₁ = K₁) : Bases U₀ V₀ N D μ K₁ Ua V₀ where
  orthUa := hU
  kCap := hcap
  orthVa := hd.orthV₀
  augV := by rw [Matrix.mul_assoc, hd.orthV₀, Matrix.mul_one]
  lCap := by rw [hleft, Matrix.mul_zero]
  kerR := by rw [hd.orthV₀, Matrix.mul_one]
  kerL := by rw [hd.compr, hd.orthV₀]

/-! ### The error -/

variable {h : ℝ}

/-- **The error in the old row space:** `Q₀ (Y₁ - A(h)) = -(h - g(h)) Q₀ D`. -/
theorem rightProj_result_sub_exact (hd : Data U₀ S₀ V₀ N C D μ)
    (hb : Bases U₀ V₀ N D μ (kTraj U₀ S₀ V₀ D μ h) Ua Va) :
    rightProj V₀ (Ua * (Uaᵀ * xTraj Va U₀ S₀ V₀ D μ h) * Vaᵀ - exact U₀ S₀ V₀ D h)
      = -((h - damp μ h) • rightProj V₀ D) := by
  have hY : Ua * (Uaᵀ * xTraj Va U₀ S₀ V₀ D μ h) * Vaᵀ * V₀ * V₀ᵀ
      = kTraj U₀ S₀ V₀ D μ h * V₀ᵀ := by
    have e : Ua * (Uaᵀ * xTraj Va U₀ S₀ V₀ D μ h) * Vaᵀ * V₀
        = Ua * Uaᵀ * (xTraj Va U₀ S₀ V₀ D μ h * (Vaᵀ * V₀)) := by
      simp only [Matrix.mul_assoc]
    rw [e, hd.xTraj_mul hb, hb.kCap]
  have hA : exact U₀ S₀ V₀ D h * V₀ * V₀ᵀ = U₀ * S₀ * V₀ᵀ + h • (D * V₀ * V₀ᵀ) := by
    rw [exact, Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_assoc (U₀ * S₀) V₀ᵀ V₀, hd.orthV₀, Matrix.mul_one]
  simp only [map_sub, rightProj_apply]
  rw [hY, hA, kTraj, Matrix.add_mul, Matrix.smul_mul]
  module

/-- **Lower bound.** The error is at least `(h - 1/μ) ‖Q₀ D‖`: of the size `h ‖Q₀ A'‖` for
`h μ ≥ 2`, whatever the normal component of the field is. -/
theorem le_norm_result_sub_exact (hd : Data U₀ S₀ V₀ N C D μ)
    (hb : Bases U₀ V₀ N D μ (kTraj U₀ S₀ V₀ D μ h) Ua Va) :
    (h - 1 / μ) * ‖rightProj V₀ D‖
      ≤ ‖Ua * (Uaᵀ * xTraj Va U₀ S₀ V₀ D μ h) * Vaᵀ - exact U₀ S₀ V₀ D h‖ := by
  have h1 := (isOrthProj_rightProj (m := m) hd.orthV₀).norm_le
    (Ua * (Uaᵀ * xTraj Va U₀ S₀ V₀ D μ h) * Vaᵀ - exact U₀ S₀ V₀ D h)
  have h0 : 0 ≤ h - damp μ h := sub_nonneg.2 (damp_le_self hd.pos h)
  rw [hd.rightProj_result_sub_exact hb, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg h0] at h1
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) h1
  linarith [damp_le_inv hd.pos h]

omit [DecidableEq r] in
/-- **The error of the step**, if `Û` also captures the increment of the Galerkin step in the new
row directions: `Y₁ - A(h) = -(h - g(h)) Q₀ D - h (D - Q̂ D)`. -/
theorem result_sub_exact (hb : Bases U₀ V₀ N D μ (kTraj U₀ S₀ V₀ D μ h) Ua Va)
    (hX : Ua * Uaᵀ * (D * (Va - V₀ * (V₀ᵀ * Va))) = D * (Va - V₀ * (V₀ᵀ * Va))) :
    Ua * (Uaᵀ * xTraj Va U₀ S₀ V₀ D μ h) * Vaᵀ - exact U₀ S₀ V₀ D h
      = -((h - damp μ h) • rightProj V₀ D) - h • (D - rightProj Va D) := by
  have hT := transpose_augV hb
  have e : Ua * (Uaᵀ * xTraj Va U₀ S₀ V₀ D μ h) = xTraj Va U₀ S₀ V₀ D μ h := by
    rw [← Matrix.mul_assoc, xTraj, Matrix.mul_add, Matrix.mul_smul, hX,
      ← Matrix.mul_assoc (Ua * Uaᵀ), hb.kCap]
  have e2 : xTraj Va U₀ S₀ V₀ D μ h * Vaᵀ
      = kTraj U₀ S₀ V₀ D μ h * V₀ᵀ + h • (D * Va * Vaᵀ - D * V₀ * V₀ᵀ) := by
    rw [xTraj, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc (kTraj U₀ S₀ V₀ D μ h),
      Matrix.mul_assoc V₀ᵀ, hT, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc, hT]
  rw [e, e2, rightProj_apply, rightProj_apply, exact, kTraj, Matrix.add_mul, Matrix.smul_mul]
  module

omit [DecidableEq r] in
/-- The distance of the exact solution from the new row space:
`A(t) - Q̂ A(t) = t (D - Q̂ D)`. -/
lemma exact_sub_rightProj (hb : Bases U₀ V₀ N D μ K₁ Ua Va) (t : ℝ) :
    exact U₀ S₀ V₀ D t - rightProj Va (exact U₀ S₀ V₀ D t) = t • (D - rightProj Va D) := by
  have hT := transpose_augV hb
  simp only [rightProj_apply, exact, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, hT]
  module

/-- **The norm of the error:**
`‖Y₁ - A(h)‖² = (h - g(h))² ‖Q₀ D‖² + h² ‖D - Q̂ D‖²`. -/
theorem norm_sq_result_sub_exact (hd : Data U₀ S₀ V₀ N C D μ)
    (hb : Bases U₀ V₀ N D μ (kTraj U₀ S₀ V₀ D μ h) Ua Va)
    (hX : Ua * Uaᵀ * (D * (Va - V₀ * (V₀ᵀ * Va))) = D * (Va - V₀ * (V₀ᵀ * Va))) :
    ‖Ua * (Uaᵀ * xTraj Va U₀ S₀ V₀ D μ h) * Vaᵀ - exact U₀ S₀ V₀ D h‖ ^ 2
      = (h - damp μ h) ^ 2 * ‖rightProj V₀ D‖ ^ 2 + h ^ 2 * ‖D - rightProj Va D‖ ^ 2 := by
  have key := (isOrthProj_rightProj (m := m) hd.orthV₀).norm_sq_add
    (Ua * (Uaᵀ * xTraj Va U₀ S₀ V₀ D μ h) * Vaᵀ - exact U₀ S₀ V₀ D h)
  rw [hd.rightProj_result_sub_exact hb] at key
  have e2 : Ua * (Uaᵀ * xTraj Va U₀ S₀ V₀ D μ h) * Vaᵀ - exact U₀ S₀ V₀ D h
      - -((h - damp μ h) • rightProj V₀ D) = -(h • (D - rightProj Va D)) := by
    rw [result_sub_exact hb hX]
    abel
  rw [e2, norm_neg, norm_neg, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs] at key
  exact key.symm

end Aug

end Data

end Family

/-! ### The steps of the integrator -/

section Steps

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k'] [DecidableEq k]
  [DecidableEq k'] {r : ℕ} {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ}
  {V₀ : Matrix n (Fin r) ℝ} {N : Matrix n n ℝ} {C D : Matrix m n ℝ} {μ h : ℝ}

/-- **The rank-adaptive step.** For new bases `Û`, `V̂` (of any widths) as in `Bases`, with `Û`
capturing `U₀`, the trajectories `K`, `L`, `S = Ûᵀ X` form a step of the rank-adaptive BUG
integrator, with truncation tolerance zero and result `Y₁ = Û S(h) V̂ᵀ`. -/
theorem isRankAdaptiveStep (hd : Data U₀ S₀ V₀ N C D μ) {Ua : Matrix m k ℝ} {Va : Matrix n k' ℝ}
    (hb : Bases U₀ V₀ N D μ (kTraj U₀ S₀ V₀ D μ h) Ua Va) (haug : Ua * Uaᵀ * U₀ = U₀) :
    IsRankAdaptiveStep (field N C) 0 0 h U₀ S₀ V₀ Ua Va (kTraj U₀ S₀ V₀ D μ) (lTraj U₀ S₀ V₀ D)
      (fun t => Uaᵀ * xTraj Va U₀ S₀ V₀ D μ t)
      (Ua * (Uaᵀ * xTraj Va U₀ S₀ V₀ D μ h) * Vaᵀ) where
  orthU₀ := hd.orthU₀
  orthV₀ := hd.orthV₀
  kSol := hd.odeSolution_kTraj 0 h
  kStart := kTraj_zero U₀ S₀ V₀ D μ
  lSol := hd.odeSolution_lTraj 0 h
  lStart := by simp [lTraj]
  orthUa := hb.orthUa
  kCap := hb.kCap
  augU := haug
  orthVa := hb.orthVa
  lCap := by
    rw [lTraj, Matrix.mul_add, Matrix.mul_smul, hb.lCap, ← Matrix.mul_assoc (Va * Vaᵀ) V₀,
      hb.augV]
  augV := hb.augV
  sSol := hd.odeSolution_sTraj hb 0 h
  sStart := by
    show Uaᵀ * xTraj Va U₀ S₀ V₀ D μ 0 = _
    rw [xTraj, kTraj_zero, zero_smul, add_zero]
    simp only [Matrix.mul_assoc]
  trunc := by simp

/-- **The fixed-rank step.** If `Dᵀ U₀ = 0`, then for every `U₁` with orthonormal columns that
captures `K(h)` the trajectories `K`, `L`, `S = U₁ᵀ X` form a step of the BUG integrator with the
new bases `U₁`, `V₀`. -/
theorem isStep (hd : Data U₀ S₀ V₀ N C D μ) (hleft : Dᵀ * U₀ = 0) {U₁ : Matrix m (Fin r) ℝ}
    (hU : U₁ᵀ * U₁ = 1) (hcap : U₁ * U₁ᵀ * kTraj U₀ S₀ V₀ D μ h = kTraj U₀ S₀ V₀ D μ h) :
    IsStep (field N C) 0 h U₀ S₀ V₀ U₁ V₀ (kTraj U₀ S₀ V₀ D μ) (lTraj U₀ S₀ V₀ D)
      (fun t => U₁ᵀ * xTraj V₀ U₀ S₀ V₀ D μ t) where
  orthU₀ := hd.orthU₀
  orthV₀ := hd.orthV₀
  kSol := hd.odeSolution_kTraj 0 h
  kStart := kTraj_zero U₀ S₀ V₀ D μ
  lSol := hd.odeSolution_lTraj 0 h
  lStart := by simp [lTraj]
  orthU₁ := hU
  kCap := hcap
  orthV₁ := hd.orthV₀
  lCap := by
    rw [lTraj, hleft, smul_zero, add_zero, Matrix.mul_assoc V₀ V₀ᵀ, ← Matrix.mul_assoc V₀ᵀ,
      hd.orthV₀, Matrix.one_mul]
  sSol := hd.odeSolution_sTraj (hd.bases_self hleft hU hcap) 0 h
  sStart := by
    show U₁ᵀ * xTraj V₀ U₀ S₀ V₀ D μ 0 = _
    rw [xTraj, kTraj_zero, zero_smul, add_zero]
    simp only [Matrix.mul_assoc]

end Steps

/-! ### A `2 × 3` family of rank one

`U₀ = e₁`, `V₀ = (c, s, 0)` with `c² + s² = 1`, `N = -diag(0, λ, 0)`, start `σ e₁ V₀ᵀ`, exact
solution `A(t) = σ e₁ V₀ᵀ + t (e₂ e₁ᵀ + e₁ e₃ᵀ)`. The augmented bases of the step are the whole
column space (spanned by `U₀ = e₁` and `K(h) = (σ, c g(h))`) and `V̂ = [V₀, e₃]` (spanned by `V₀`
and `L(h) = σ V₀ + h e₃`). -/

namespace Example

/-- The old left basis `e₁`. -/
def U₀ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The singular value `σ` of the start. -/
def S₀ (σ : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := !![σ]

/-- The old right basis `(c, s, 0)`: it mixes a smooth and a stiff eigenvector of `N`. -/
def V₀ (c s : ℝ) : Matrix (Fin 3) (Fin 1) ℝ := !![c; s; 0]

/-- The stiff operator `N = -diag(0, λ, 0)`. -/
def N (lam : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, -lam, 0; 0, 0, 0]

/-- The forcing. -/
def C (s lam σ : ℝ) : Matrix (Fin 2) (Fin 3) ℝ := !![0, σ * lam * s, 1; 1, 0, 0]

/-- The derivative of the exact solution. -/
def D : Matrix (Fin 2) (Fin 3) ℝ := !![0, 0, 1; 1, 0, 0]

/-- The augmented right basis `[V₀, e₃]`. -/
def Va (c s : ℝ) : Matrix (Fin 3) (Fin 2) ℝ := !![c, 0; s, 0; 0, 1]

/-- The part of `D` in the old row space, `Q₀ D`. -/
def Qm (c s : ℝ) : Matrix (Fin 2) (Fin 3) ℝ := !![0, 0, 0; c * c, c * s, 0]

/-- The part of `D` outside the new row space, `D - Q̂ D`; it is also the doubly normal part
`(1 - P₀)(1 - Q₀) D`. -/
def Rm (c s : ℝ) : Matrix (Fin 2) (Fin 3) ℝ := !![0, 0, 0; 1 - c * c, -(c * s), 0]

/-- The forcing of the variant without the new row direction. -/
def C' (s lam σ : ℝ) : Matrix (Fin 2) (Fin 3) ℝ := !![0, σ * lam * s, 0; 1, 0, 0]

/-- The derivative of the exact solution of the variant without the new row direction. -/
def D' : Matrix (Fin 2) (Fin 3) ℝ := !![0, 0, 0; 1, 0, 0]

/-- A vector `(a, b)` as new left basis of the fixed-rank step. -/
def U₁ (a b : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := !![a; b]

/-- Entrywise evaluation of an identity between small explicit matrices. -/
local macro "entries" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Fin.sum_univ_three, U₀, S₀, V₀, N, C, D, Va, Qm, Rm, C', D', U₁] <;> try ring1))

variable {c s lam σ : ℝ}

/-- The family satisfies the hypotheses on the data, with `μ = λ s²`. -/
theorem data (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0) :
    Data U₀ (S₀ σ) (V₀ c s) (N lam) (C s lam σ) D (lam * s ^ 2) where
  orthU₀ := by entries
  orthV₀ := by
    entries
    linear_combination hcs
  pos := by positivity
  compr := by entries
  deriv := by entries
  ker := by entries

lemma Va_transpose_mul_V₀ (hcs : c ^ 2 + s ^ 2 = 1) : (Va c s)ᵀ * V₀ c s = !![1; 0] := by
  entries
  linear_combination hcs

lemma V₀_transpose_mul_Va (hcs : c ^ 2 + s ^ 2 = 1) : (V₀ c s)ᵀ * Va c s = !![1, 0] := by
  entries
  linear_combination hcs

/-- The whole column space and `V̂ = [V₀, e₃]` satisfy the hypotheses on the bases. -/
theorem bases (hcs : c ^ 2 + s ^ 2 = 1) (K₁ : Matrix (Fin 2) (Fin 1) ℝ) :
    Bases U₀ (V₀ c s) (N lam) D (lam * s ^ 2) K₁ (1 : Matrix (Fin 2) (Fin 2) ℝ) (Va c s) where
  orthUa := by simp
  kCap := by simp
  orthVa := by
    entries
    linear_combination hcs
  augV := by
    rw [Matrix.mul_assoc, Va_transpose_mul_V₀ hcs]
    entries
  lCap := by entries
  kerR := by
    rw [V₀_transpose_mul_Va hcs]
    entries
  kerL := by
    rw [Va_transpose_mul_V₀ hcs]
    entries

/-- The result of the augmented step of size `h`, before truncation. -/
noncomputable def result (c s lam σ h : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  (1 : Matrix (Fin 2) (Fin 2) ℝ) * ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *
    xTraj (Va c s) U₀ (S₀ σ) (V₀ c s) D (lam * s ^ 2) h) * (Va c s)ᵀ

/-- **The family is a rank-adaptive BUG step** in the sense of the library (tolerance zero),
for every step size. -/
theorem isRankAdaptiveStep (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0) (h : ℝ) :
    IsRankAdaptiveStep (field (N lam) (C s lam σ)) 0 0 h U₀ (S₀ σ) (V₀ c s)
      (1 : Matrix (Fin 2) (Fin 2) ℝ) (Va c s)
      (kTraj U₀ (S₀ σ) (V₀ c s) D (lam * s ^ 2)) (lTraj U₀ (S₀ σ) (V₀ c s) D)
      (fun t => (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *
        xTraj (Va c s) U₀ (S₀ σ) (V₀ c s) D (lam * s ^ 2) t)
      (result c s lam σ h) := by
  unfold result
  exact StiffOrderReduction.isRankAdaptiveStep (data hcs hl hs) (bases hcs _) (by simp)

lemma rightProj_V₀_D : rightProj (V₀ c s) D = Qm c s := by
  rw [rightProj_apply]
  entries

lemma D_sub_rightProj_Va : D - rightProj (Va c s) D = Rm c s := by
  rw [rightProj_apply]
  entries

lemma norm_sq_Qm (hcs : c ^ 2 + s ^ 2 = 1) : ‖Qm c s‖ ^ 2 = c ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  simp [Qm]
  linear_combination c ^ 2 * hcs

lemma norm_sq_Rm (hcs : c ^ 2 + s ^ 2 = 1) : ‖Rm c s‖ ^ 2 = s ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  simp [Rm]
  linear_combination (c ^ 2 - 1) * hcs

lemma norm_Qm (hcs : c ^ 2 + s ^ 2 = 1) : ‖Qm c s‖ = |c| := by
  rw [← Real.sqrt_sq (norm_nonneg (Qm c s)), norm_sq_Qm hcs, Real.sqrt_sq_eq_abs]

lemma norm_Rm (hcs : c ^ 2 + s ^ 2 = 1) : ‖Rm c s‖ = |s| := by
  rw [← Real.sqrt_sq (norm_nonneg (Rm c s)), norm_sq_Rm hcs, Real.sqrt_sq_eq_abs]

/-- **The error of the step, exactly:** `‖Y₁ - A(h)‖² = (h - g(h))² c² + h² s²`. -/
theorem norm_sq_result_sub_exact (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0) (h : ℝ) :
    ‖result c s lam σ h - exact U₀ (S₀ σ) (V₀ c s) D h‖ ^ 2
      = (h - damp (lam * s ^ 2) h) ^ 2 * c ^ 2 + h ^ 2 * s ^ 2 := by
  rw [result, (data (σ := σ) hcs hl hs).norm_sq_result_sub_exact (bases hcs _) (by simp),
    rightProj_V₀_D, norm_sq_Qm hcs, D_sub_rightProj_Va, norm_sq_Rm hcs]

/-- **Order reduction:** the error is at least `(h - 1/(λ s²)) |c|`. -/
theorem le_norm_result_sub_exact (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0) (h : ℝ) :
    (h - 1 / (lam * s ^ 2)) * |c|
      ≤ ‖result c s lam σ h - exact U₀ (S₀ σ) (V₀ c s) D h‖ := by
  rw [result, ← norm_Qm hcs, ← rightProj_V₀_D]
  exact (data hcs hl hs).le_norm_result_sub_exact (bases hcs _)

/-- **Order reduction, in the stiff regime:** if `λ s² h ≥ 2`, the error is at least `(h/2) |c|`,
whatever the normal component `|s|` of the field is. -/
theorem half_mul_le_norm_result_sub_exact (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0)
    {h : ℝ} (hμ : 2 ≤ lam * s ^ 2 * h) :
    h / 2 * |c| ≤ ‖result c s lam σ h - exact U₀ (S₀ σ) (V₀ c s) D h‖ := by
  have hpos : 0 < lam * s ^ 2 := by positivity
  have h1 : 1 / (lam * s ^ 2) ≤ h / 2 := by
    rw [div_le_iff₀ hpos]
    linarith
  calc h / 2 * |c| ≤ (h - 1 / (lam * s ^ 2)) * |c| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg c)
    _ ≤ ‖result c s lam σ h - exact U₀ (S₀ σ) (V₀ c s) D h‖ :=
        le_norm_result_sub_exact hcs hl hs h

/-- A concrete member of the family: `c = 3/5`, `s = 4/5`, `λ = 25`, `σ = 1`, so that
`μ = λ s² = 16`. -/
example (h : ℝ) :
    ‖result (3 / 5) (4 / 5) 25 1 h - exact U₀ (S₀ 1) (V₀ (3 / 5) (4 / 5)) D h‖ ^ 2
      = (h - damp (25 * (4 / 5) ^ 2) h) ^ 2 * (3 / 5) ^ 2 + h ^ 2 * (4 / 5) ^ 2 :=
  norm_sq_result_sub_exact (by norm_num) (by norm_num) (by norm_num) h

/-- The best approximation of the exact solution in the new row space has error `h |s|`: the
Galerkin space of the step is good, the Galerkin step in it is not. -/
theorem norm_exact_sub_rightProj (hcs : c ^ 2 + s ^ 2 = 1) (h : ℝ) :
    ‖exact U₀ (S₀ σ) (V₀ c s) D h - rightProj (Va c s) (exact U₀ (S₀ σ) (V₀ c s) D h)‖
      = |h| * |s| := by
  rw [Data.exact_sub_rightProj (bases (lam := 1) hcs (0 : Matrix (Fin 2) (Fin 1) ℝ)) h,
    D_sub_rightProj_Va, norm_smul, Real.norm_eq_abs, norm_Rm hcs]

lemma D_sub_rightProj_V₀ :
    D - rightProj (V₀ c s) D = !![0, 0, 1; 1 - c * c, -(c * s), 0] := by
  rw [rightProj_apply]
  entries

lemma sub_leftProj_U₀ (x y z : ℝ) :
    (!![0, 0, 1; x, y, z] : Matrix (Fin 2) (Fin 3) ℝ) - leftProj U₀ !![0, 0, 1; x, y, z]
      = !![0, 0, 0; x, y, z] := by
  rw [leftProj_apply]
  entries

lemma normal_D :
    D - rightProj (V₀ c s) D - leftProj U₀ (D - rightProj (V₀ c s) D) = Rm c s := by
  rw [D_sub_rightProj_V₀, sub_leftProj_U₀, Rm]

/-- **The normal component of the field at the start is `|s|`**, for every `λ` and `σ`. -/
theorem norm_normal_field_start (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0) (t : ℝ) :
    ‖(1 - leftProj (n := Fin 3) U₀) ((1 - rightProj (m := Fin 2) (V₀ c s))
        (field (N lam) (C s lam σ) t (U₀ * S₀ σ * (V₀ c s)ᵀ)))‖ = |s| := by
  rw [(data hcs hl hs).field_start t]
  simp only [sub_apply, one_apply_eq_self]
  rw [normal_D, norm_Rm hcs]

/-- The derivative of the exact solution has norm `√2`, for every `λ` and `σ`. -/
theorem norm_sq_D : ‖D‖ ^ 2 = 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  norm_num [D, Fin.sum_univ_two, Fin.sum_univ_three]

lemma coupling_eq :
    (V₀ c s)ᵀ * N lam * (1 - V₀ c s * (V₀ c s)ᵀ)
      = !![lam * s ^ 2 * c, -(lam * s * (1 - s * s)), 0] := by
  entries
  exact Or.inl (mul_comm s lam)

/-- **The coupling of the stiff operator with the old row space is not zero.** -/
theorem coupling_ne_zero (hc : c ≠ 0) (hs : s ≠ 0) (hl : lam ≠ 0) :
    (V₀ c s)ᵀ * N lam * (1 - V₀ c s * (V₀ c s)ᵀ) ≠ 0 := by
  rw [coupling_eq]
  intro h0
  have h1 := congrFun (congrFun h0 0) 0
  simp [hl, hs, hc] at h1

/-! #### No error constant that is uniform in the stiff operator

For a step size `h ≤ 1/2` and a stiffness `λ ≥ 2 / h³` choose `s = √(2 / (h λ))` and
`c = √(1 - s²)`. Then `λ s² h = 2`, the normal component of the field is at most `h`, and the
error of the step is at least `(√3 / 4) h`, while `h ε + h² ≤ 2 h²`. -/

/-- The normal component of the field at the start value,
`ε = ‖(1 - P₀) (1 - Q₀) F(0, Y₀)‖`, with the projectors `P₀`, `Q₀` onto the old column and row
spaces. -/
noncomputable def normalDefect (c s lam σ : ℝ) : ℝ :=
  ‖(1 - leftProj (n := Fin 3) U₀) ((1 - rightProj (m := Fin 2) (V₀ c s))
      (field (N lam) (C s lam σ) 0 (U₀ * S₀ σ * (V₀ c s)ᵀ)))‖

lemma normalDefect_eq (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0) :
    normalDefect c s lam σ = |s| :=
  norm_normal_field_start hcs hl hs 0

lemma normalDefect_nonneg (c s lam σ : ℝ) : 0 ≤ normalDefect c s lam σ :=
  norm_nonneg _

/-- The stiff operator has norm `λ`. -/
theorem norm_sq_N : ‖N lam‖ ^ 2 = lam ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  norm_num [N, Fin.sum_univ_three]

/-- **Order reduction for an explicit choice of the parameters.** Let `0 < h ≤ 1/2`,
`λ ≥ 2 / h³`, `s = √(2 / (h λ))` and `c = √(1 - s²)`. Then the parameters are admissible
(`c² + s² = 1`, `λ > 0`, `s ≠ 0`), `λ s² h = 2`, the normal component of the field is at most
`h`, the error of the rank-adaptive step `Example.isRankAdaptiveStep` is at least `(√3 / 4) h`,
and `h ε + h² ≤ 2 h²`. So the error divided by `h ε + h²` is at least `√3 / (8 h)`. -/
theorem order_reduction_explicit {h : ℝ} (h0 : 0 < h) (h2 : h ≤ 1 / 2) (hlam : 2 / h ^ 3 ≤ lam)
    (hs : s = Real.sqrt (2 / (h * lam))) (hc : c = Real.sqrt (1 - s ^ 2)) :
    c ^ 2 + s ^ 2 = 1 ∧ 0 < lam ∧ s ≠ 0 ∧ lam * s ^ 2 * h = 2 ∧
      normalDefect c s lam σ ≤ h ∧
      Real.sqrt 3 / 4 * h ≤ ‖result c s lam σ h - exact U₀ (S₀ σ) (V₀ c s) D h‖ ∧
      h * normalDefect c s lam σ + h ^ 2 ≤ 2 * h ^ 2 := by
  have hl : 0 < lam := lt_of_lt_of_le (div_pos zero_lt_two (pow_pos h0 3)) hlam
  have hhl : 0 < h * lam := mul_pos h0 hl
  have hlam' : 2 ≤ lam * h ^ 3 := (div_le_iff₀ (pow_pos h0 3)).1 hlam
  have hs2 : s ^ 2 = 2 / (h * lam) := by
    rw [hs, Real.sq_sqrt (div_nonneg zero_le_two hhl.le)]
  have hs0 : 0 < s := by
    rw [hs]
    exact Real.sqrt_pos.2 (div_pos zero_lt_two hhl)
  have hsh2 : s ^ 2 ≤ h ^ 2 := by
    rw [hs2, div_le_iff₀ hhl]
    calc (2 : ℝ) ≤ lam * h ^ 3 := hlam'
      _ = h ^ 2 * (h * lam) := by ring
  have hsh : s ≤ h := by
    by_contra hlt
    rw [not_le] at hlt
    nlinarith [mul_pos (sub_pos.2 hlt) (add_pos hs0 h0)]
  have hh2 : h ^ 2 ≤ 1 / 4 := by nlinarith [mul_nonneg (sub_nonneg.2 h2) h0.le]
  have hc2 : c ^ 2 = 1 - s ^ 2 := by
    rw [hc, Real.sq_sqrt (by linarith)]
  have hcn : 0 ≤ c := by
    rw [hc]
    exact Real.sqrt_nonneg _
  have hcs : c ^ 2 + s ^ 2 = 1 := by rw [hc2]; ring
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc0 : Real.sqrt 3 / 2 ≤ c := by
    rw [hc]
    have e : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
      rw [div_pow, h3]
      norm_num
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    rw [e]
    linarith
  have hμ : lam * s ^ 2 * h = 2 := by
    rw [hs2, mul_div_assoc', div_mul_eq_mul_div, div_eq_iff hhl.ne']
    ring
  have heps : normalDefect c s lam σ = s := by
    rw [normalDefect_eq hcs hl hs0.ne', abs_of_pos hs0]
  have herr := half_mul_le_norm_result_sub_exact (σ := σ) hcs hl hs0.ne' (le_of_eq hμ.symm)
  rw [abs_of_nonneg hcn] at herr
  have hprod := mul_le_mul_of_nonneg_left hc0 h0.le
  have hprod' := mul_le_mul_of_nonneg_left hsh h0.le
  refine ⟨hcs, hl, hs0.ne', hμ, ?_, ?_, ?_⟩
  · rw [heps]
    exact hsh
  · linarith
  · rw [heps]
    linarith

/-- A concrete instance of `order_reduction_explicit`: `h = 1/2`, `λ = 676/25`, so that
`s = 5/13` and `c = 12/13`, with `σ = 1`. The normal component of the field is `5/13`. -/
example :
    normalDefect (12 / 13) (5 / 13) (676 / 25) 1 ≤ 1 / 2 ∧
      Real.sqrt 3 / 4 * (1 / 2)
        ≤ ‖result (12 / 13) (5 / 13) (676 / 25) 1 (1 / 2)
            - exact U₀ (S₀ 1) (V₀ (12 / 13) (5 / 13)) D (1 / 2)‖ := by
  have hs : (5 / 13 : ℝ) = Real.sqrt (2 / (1 / 2 * (676 / 25))) := by
    rw [show (2 / (1 / 2 * (676 / 25)) : ℝ) = (5 / 13) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5 / 13)]
  have hc : (12 / 13 : ℝ) = Real.sqrt (1 - (5 / 13) ^ 2) := by
    rw [show (1 - (5 / 13) ^ 2 : ℝ) = (12 / 13) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 12 / 13)]
  have key := order_reduction_explicit (σ := 1) (h := 1 / 2) (lam := 676 / 25)
    (by norm_num) le_rfl (by norm_num) hs hc
  exact ⟨key.2.2.2.2.1, key.2.2.2.2.2.1⟩

/-- **No constant works for the whole family.** There is no `K` such that the error of the
rank-adaptive step is at most `K (h ε + h²)` for all admissible parameters of the family and all
step sizes `h ≤ 1/2`, where `ε = normalDefect` is the normal component of the field at the start
(equal to `|s|` by `normalDefect_eq`).

The quantities that describe the smoothness of the exact solution are the same for all members
of the family: the exact solution is `exact`, affine in time, with the constant derivative `D`
of norm `√2` (`norm_sq_D`), so that its second derivative vanishes, and `D * N = 0` (the field
`ker` of `data`). The only quantity that is not bounded over the family is the norm of the stiff
operator, `‖N‖ = λ` (`norm_sq_N`); in the proof `λ = 2 / h³` with `h = 1 / (8 (|K| + 1))`. A
bound of the form `K (h ε + h²)` for this family therefore has a constant that depends on `‖N‖`,
as the constants of error bounds in terms of the Lipschitz constant of the whole field do. -/
theorem not_exists_uniform_bound :
    ¬ ∃ K : ℝ, ∀ c s lam σ h : ℝ, c ^ 2 + s ^ 2 = 1 → 0 < lam → s ≠ 0 → 0 < h → h ≤ 1 / 2 →
      ‖result c s lam σ h - exact U₀ (S₀ σ) (V₀ c s) D h‖
        ≤ K * (h * normalDefect c s lam σ + h ^ 2) := by
  rintro ⟨K, hK⟩
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = 1 / (8 * (|K| + 1)) := ⟨_, rfl⟩
  have hK1 : 0 < 8 * (|K| + 1) := by positivity
  have h0 : 0 < h := by
    rw [hh]
    exact one_div_pos.2 hK1
  have hh8 : 8 * |K| * h + 8 * h = 1 := by
    have e : 8 * (|K| + 1) * h = 1 := by
      rw [hh]
      exact mul_one_div_cancel hK1.ne'
    rw [← e]
    ring
  have hKh : 0 ≤ |K| * h := mul_nonneg (abs_nonneg K) h0.le
  have h2 : h ≤ 1 / 2 := by linarith
  obtain ⟨hcs, hl, hs, -, -, hlow, hup⟩ :=
    order_reduction_explicit (σ := 0) (lam := 2 / h ^ 3) h0 h2 le_rfl rfl rfl
  have h1 := hK _ _ _ 0 h hcs hl hs h0 h2
  have hx : 0 ≤ h * normalDefect (Real.sqrt (1 - Real.sqrt (2 / (h * (2 / h ^ 3))) ^ 2))
      (Real.sqrt (2 / (h * (2 / h ^ 3)))) (2 / h ^ 3) 0 + h ^ 2 :=
    add_nonneg (mul_nonneg h0.le (normalDefect_nonneg _ _ _ _)) (sq_nonneg h)
  have h3 : Real.sqrt 3 / 4 * h ≤ 2 * |K| * h * h :=
    calc Real.sqrt 3 / 4 * h ≤ _ := hlow
      _ ≤ _ := h1
      _ ≤ |K| * _ := mul_le_mul_of_nonneg_right (le_abs_self K) hx
      _ ≤ |K| * (2 * h ^ 2) := mul_le_mul_of_nonneg_left hup (abs_nonneg K)
      _ = 2 * |K| * h * h := by ring
  have h4 : Real.sqrt 3 / 4 ≤ 2 * |K| * h := le_of_mul_le_mul_right h3 h0
  have h31 : 1 ≤ Real.sqrt 3 := by
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    norm_num
  linarith

/-! #### A variant with bounded data

With the start scaled as `σ = 1 / (λ s)` the forcing does not depend on `λ` (`C_scaled`) and
`‖A₀ N‖ = 1` (`norm_start_mul_N_scaled`). The statements above hold for every `σ`, so also for
this one: in this variant the forcing, the derivative of the exact solution and `A₀ N` are
bounded over the family, and `‖N‖ = λ` is not. -/

/-- With `σ = 1 / (λ s)` the forcing is the same for all members of the family. -/
lemma C_scaled (hl : lam ≠ 0) (hs : s ≠ 0) :
    C s lam (1 / (lam * s)) = !![0, 1, 1; 1, 0, 0] := by
  rw [C, mul_assoc, one_div_mul_cancel (mul_ne_zero hl hs)]

/-- With `σ = 1 / (λ s)` the forcing has norm `√3`. -/
theorem norm_sq_C_scaled (hl : lam ≠ 0) (hs : s ≠ 0) : ‖C s lam (1 / (lam * s))‖ ^ 2 = 3 := by
  rw [C_scaled hl hs, Frobenius.norm_sq_eq_sum]
  norm_num [Fin.sum_univ_two, Fin.sum_univ_three]

lemma start_mul_N :
    U₀ * S₀ σ * (V₀ c s)ᵀ * N lam = !![0, -(σ * lam * s), 0; 0, 0, 0] := by
  entries

/-- The stiff operator applied to the start value: `‖A₀ N‖ = |σ λ s|`. -/
theorem norm_sq_start_mul_N : ‖U₀ * S₀ σ * (V₀ c s)ᵀ * N lam‖ ^ 2 = (σ * lam * s) ^ 2 := by
  rw [start_mul_N, Frobenius.norm_sq_eq_sum]
  norm_num [Fin.sum_univ_two, Fin.sum_univ_three]

/-- With `σ = 1 / (λ s)`: `‖A₀ N‖ = 1`. -/
theorem norm_start_mul_N_scaled (hl : lam ≠ 0) (hs : s ≠ 0) :
    ‖U₀ * S₀ (1 / (lam * s)) * (V₀ c s)ᵀ * N lam‖ = 1 := by
  have h1 : ‖U₀ * S₀ (1 / (lam * s)) * (V₀ c s)ᵀ * N lam‖ ^ 2 = 1 := by
    rw [norm_sq_start_mul_N, mul_assoc, one_div_mul_cancel (mul_ne_zero hl hs), one_pow]
  rw [← Real.sqrt_sq (norm_nonneg (U₀ * S₀ (1 / (lam * s)) * (V₀ c s)ᵀ * N lam)), h1,
    Real.sqrt_one]

/-! #### The fixed-rank step

Without the entry `e₁ e₃ᵀ` of the forcing the L-step is stationary, `V₁ = V₀`, and a unit vector
`(a, b)` parallel to `K(h) = (σ, c g(h))` is the new left basis. -/

theorem data' (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0) :
    Data U₀ (S₀ σ) (V₀ c s) (N lam) (C' s lam σ) D' (lam * s ^ 2) where
  orthU₀ := by entries
  orthV₀ := by
    entries
    linear_combination hcs
  pos := by positivity
  compr := by entries
  deriv := by entries
  ker := by entries

lemma left' : D'ᵀ * U₀ = 0 := by entries

lemma orthU₁ {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) : (U₁ a b)ᵀ * U₁ a b = 1 := by
  entries
  linear_combination hab

lemma cap {a b h : ℝ} (hab : a ^ 2 + b ^ 2 = 1)
    (hσ : σ * b = damp (lam * s ^ 2) h * c * a) :
    U₁ a b * (U₁ a b)ᵀ * kTraj U₀ (S₀ σ) (V₀ c s) D' (lam * s ^ 2) h
      = kTraj U₀ (S₀ σ) (V₀ c s) D' (lam * s ^ 2) h := by
  rw [kTraj]
  entries
  · linear_combination σ * hab - b * hσ
  · linear_combination (damp (lam * s ^ 2) h * c) * hab + a * hσ

/-- **The variant is a fixed-rank BUG step** in the sense of the library. -/
theorem isStep (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0) {a b h : ℝ}
    (hab : a ^ 2 + b ^ 2 = 1) (hσ : σ * b = damp (lam * s ^ 2) h * c * a) :
    IsStep (field (N lam) (C' s lam σ)) 0 h U₀ (S₀ σ) (V₀ c s) (U₁ a b) (V₀ c s)
      (kTraj U₀ (S₀ σ) (V₀ c s) D' (lam * s ^ 2)) (lTraj U₀ (S₀ σ) (V₀ c s) D')
      (fun t => (U₁ a b)ᵀ * xTraj (V₀ c s) U₀ (S₀ σ) (V₀ c s) D' (lam * s ^ 2) t) :=
  StiffOrderReduction.isStep (data' hcs hl hs) left' (orthU₁ hab) (cap hab hσ)

lemma rightProj_V₀_D' : rightProj (V₀ c s) D' = Qm c s := by
  rw [rightProj_apply]
  entries

/-- **Order reduction of the fixed-rank step:** its error is at least `(h - 1/(λ s²)) |c|`. -/
theorem le_norm_fixed_sub_exact (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0)
    {a b h : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (hσ : σ * b = damp (lam * s ^ 2) h * c * a) :
    (h - 1 / (lam * s ^ 2)) * |c|
      ≤ ‖U₁ a b * ((U₁ a b)ᵀ * xTraj (V₀ c s) U₀ (S₀ σ) (V₀ c s) D' (lam * s ^ 2) h)
          * (V₀ c s)ᵀ - exact U₀ (S₀ σ) (V₀ c s) D' h‖ := by
  rw [← norm_Qm hcs, ← rightProj_V₀_D']
  exact (data' (σ := σ) hcs hl hs).le_norm_result_sub_exact
    ((data' (σ := σ) hcs hl hs).bases_self left' (orthU₁ hab) (cap hab hσ))

/-- A unit vector of the plane parallel to a given vector (any unit vector if it vanishes). -/
lemma exists_unit_parallel (x y : ℝ) : ∃ a b : ℝ, a ^ 2 + b ^ 2 = 1 ∧ x * b = y * a := by
  by_cases h0 : x ^ 2 + y ^ 2 = 0
  · have hx2 : x ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy2 : y ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hx : x = 0 := by simpa using hx2
    have hy : y = 0 := by simpa using hy2
    exact ⟨1, 0, by norm_num, by simp [hx, hy]⟩
  · have hpos : 0 < x ^ 2 + y ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    have hsq : Real.sqrt (x ^ 2 + y ^ 2) ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt hpos.le
    refine ⟨x / Real.sqrt (x ^ 2 + y ^ 2), y / Real.sqrt (x ^ 2 + y ^ 2), ?_, ?_⟩
    · rw [div_pow, div_pow, ← add_div, hsq, div_self hpos.ne']
    · ring

/-- **The fixed-rank variant with every hypothesis instantiated:** for every step size there is
a new left basis for which the trajectories form a fixed-rank BUG step, and the error of that
step is at least `(h - 1/(λ s²)) |c|`. -/
theorem exists_isStep_le_norm (hcs : c ^ 2 + s ^ 2 = 1) (hl : 0 < lam) (hs : s ≠ 0) (h : ℝ) :
    ∃ a b : ℝ,
      IsStep (field (N lam) (C' s lam σ)) 0 h U₀ (S₀ σ) (V₀ c s) (U₁ a b) (V₀ c s)
        (kTraj U₀ (S₀ σ) (V₀ c s) D' (lam * s ^ 2)) (lTraj U₀ (S₀ σ) (V₀ c s) D')
        (fun t => (U₁ a b)ᵀ * xTraj (V₀ c s) U₀ (S₀ σ) (V₀ c s) D' (lam * s ^ 2) t) ∧
      (h - 1 / (lam * s ^ 2)) * |c|
        ≤ ‖U₁ a b * ((U₁ a b)ᵀ * xTraj (V₀ c s) U₀ (S₀ σ) (V₀ c s) D' (lam * s ^ 2) h)
            * (V₀ c s)ᵀ - exact U₀ (S₀ σ) (V₀ c s) D' h‖ := by
  obtain ⟨a, b, hab, hσ⟩ := exists_unit_parallel σ (damp (lam * s ^ 2) h * c)
  exact ⟨a, b, isStep hcs hl hs hab hσ, le_norm_fixed_sub_exact hcs hl hs hab hσ⟩

end Example

end StiffOrderReduction

end LeanDLRA
