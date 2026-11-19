import LeanDLRA.Research.ImplicitBUGStiffSemilinear

/-!
# Implicit midpoint Galerkin steps for a stiff row operator: run bounds with the factor one

Let `F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ` and `C` arbitrary. The implicit
midpoint step of size `2 τ` from `Y` is `2 W - Y`, where `W` is the backward Euler step of size `τ`
from `Y` (the value at the midpoint). The reflection `Y ↦ 2 W - Y` does not increase the Frobenius
norm, so the error of any sequence against a reference that satisfies the implicit midpoint rule
up to defects is the start error plus the defects plus the sum of the local errors, with the
factor one on the start error and no restriction on the step size. A low-rank step that computes
the midpoint value by a Galerkin backward Euler step in a space of matrices `P Z Q` has twice the
error of this Galerkin step as its local error, and the Galerkin step is quasi-optimal in the
energy norm `(‖Z‖² + τ ‖Z Cᵀ‖²)^{1/2}`. For bases built from two levels of K- and L-steps the
combination `Y_K + Y_L - Y₁` of the second-level K- and L-steps and the first-level Galerkin step
lies in the Galerkin space, and its residual in the equation of the full problem is a sum of two
terms that are computable along the run. No constant depends on `C` or on singular values.

## Main results

* `ImplicitMidpointBUGStiff.sq_norm_two_smul_sub_add_le_of_backwardEuler`: the reflection at the
  backward Euler value, `‖2 W - R‖² + 4 τ ‖W Cᵀ‖² ≤ ‖R‖²`.
* `ImplicitMidpointBUGStiff.norm_sub_le_add_sum_of_implicitMidpoint`: for every sequence,
  `‖Y_N - X_N‖ ≤ ‖Y₀ - X₀‖ + ∑ (‖d_j‖ + ‖Y_{j+1} - (2 W_j - Y_j)‖)`.
* `ImplicitMidpointBUGStiff.sqrt_sq_norm_galerkin_sub_add_le`: quasi-optimality of the Galerkin
  backward Euler step in the energy norm, with the constant `1 + τ μ`.
* `ImplicitMidpointBUGStiff.sqrt_sq_norm_backwardEuler_sub_combination_add_le`: the residual of
  the combination of two levels.
* `ImplicitMidpointBUGStiff.norm_galerkinMidpoint_run_sub_le` and
  `ImplicitMidpointBUGStiff.norm_twoLevelMidpoint_run_sub_le`: the run bounds.

## References

* [CerutiEtAl2024b] for the midpoint BUG integrator with augmented bases;
  [CerutiLubich2022] for the K-, L- and Galerkin steps.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius
open Matrix Finset

namespace LeanDLRA

open ImplicitBUGStiffLemmas ImplicitBUGStiffLocal ImplicitBUGStiffSemilinear

namespace ImplicitMidpointBUGStiff

section Lemmas

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] {M : Matrix m m ℝ}
  {C : Matrix k n ℝ} {τ μ : ℝ}

/-- **The reflection at the backward Euler value does not increase the norm.** If
`W - τ M W + τ W CᵀC = R` with `M` dissipative, then `‖2 W - R‖² + 4 τ ‖W Cᵀ‖² ≤ ‖R‖²`: the implicit
midpoint step of size `2 τ` from `R` is `2 W - R`. -/
theorem sq_norm_two_smul_sub_add_le_of_backwardEuler
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hτ : 0 ≤ τ) {W R : Matrix m n ℝ}
    (heq : W - τ • (M * W) + τ • (W * (Cᵀ * C)) = R) :
    ‖(2 : ℝ) • W - R‖ ^ 2 + 4 * (τ * ‖W * Cᵀ‖ ^ 2) ≤ ‖R‖ ^ 2 := by
  have h1 : ⟪W, W⟫ - τ * ⟪M * W, W⟫ + τ * ⟪W * Cᵀ, W * Cᵀ⟫ = ⟪R, W⟫ := by
    have h0 := congrArg (fun X => ⟪X, W⟫) heq
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left] at h0
    rwa [← Matrix.mul_assoc W, Frobenius.inner_mul_right (W * Cᵀ) C W] at h0
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1
  have h2 : ‖(2 : ℝ) • W‖ = 2 * ‖W‖ := by rw [norm_smul]; norm_num
  rw [norm_sub_sq_real, h2, real_inner_smul_left, real_inner_comm R W]
  have h3 := mul_nonpos_of_nonneg_of_nonpos hτ (inner_mul_self_nonpos hdiss W)
  nlinarith [h1, h3]

/-- The implicit midpoint step of the full problem, written as the reflection at the backward
Euler value, does not increase the Frobenius norm. -/
theorem norm_two_smul_sub_le_of_backwardEuler
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hτ : 0 ≤ τ) {W R : Matrix m n ℝ}
    (heq : W - τ • (M * W) + τ • (W * (Cᵀ * C)) = R) : ‖(2 : ℝ) • W - R‖ ≤ ‖R‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  have h1 := sq_norm_two_smul_sub_add_le_of_backwardEuler hdiss hτ heq
  have h2 : 0 ≤ τ * ‖W * Cᵀ‖ ^ 2 := mul_nonneg hτ (sq_nonneg _)
  linarith

/-- A backward Euler step of the full problem does not increase the energy norm
`(‖Z‖² + τ ‖Z Cᵀ‖²)^{1/2}` measured against the Frobenius norm of the right-hand side. -/
theorem sqrt_sq_norm_add_le_of_backwardEuler_of_nonneg
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hτ : 0 ≤ τ) {W R : Matrix m n ℝ}
    (heq : W - τ • (M * W) + τ • (W * (Cᵀ * C)) = R) :
    √(‖W‖ ^ 2 + τ * ‖W * Cᵀ‖ ^ 2) ≤ ‖R‖ := by
  refine Real.sqrt_le_iff.2 ⟨norm_nonneg R, ?_⟩
  have h1 := sq_norm_add_le_of_backwardEuler hdiss hτ heq
  have h2 : 0 ≤ τ * ‖W * Cᵀ‖ ^ 2 := mul_nonneg hτ (sq_nonneg _)
  linarith

/-- Stability of the implicit midpoint step against a reference given by its midpoint value:
if `W` is the backward Euler value from `Y` and `Xm - τ M Xm + τ Xm CᵀC = X + d / 2`, then
`‖(2 W - Y) - (2 Xm - X)‖ ≤ ‖Y - X‖ + ‖d‖`. -/
theorem norm_two_smul_sub_sub_le_of_midpoint
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hτ : 0 ≤ τ) {Y W X Xm d : Matrix m n ℝ}
    (hW : W - τ • (M * W) + τ • (W * (Cᵀ * C)) = Y)
    (hXm : Xm - τ • (M * Xm) + τ • (Xm * (Cᵀ * C)) = X + (1 / 2 : ℝ) • d) :
    ‖(2 : ℝ) • W - Y - ((2 : ℝ) • Xm - X)‖ ≤ ‖Y - X‖ + ‖d‖ := by
  have e : W - Xm - τ • (M * (W - Xm)) + τ • ((W - Xm) * (Cᵀ * C)) =
      Y - (X + (1 / 2 : ℝ) • d) := by
    rw [← hW, ← hXm]
    simp only [Matrix.mul_sub, Matrix.sub_mul, smul_sub]
    abel
  have n1 := norm_two_smul_sub_le_of_backwardEuler hdiss hτ e
  have e2 : (2 : ℝ) • W - Y - ((2 : ℝ) • Xm - X) =
      (2 : ℝ) • (W - Xm) - (Y - (X + (1 / 2 : ℝ) • d)) - (1 / 2 : ℝ) • d := by
    module
  have n2 : ‖(1 / 2 : ℝ) • d‖ = 1 / 2 * ‖d‖ := by rw [norm_smul]; norm_num
  have n3 : ‖Y - (X + (1 / 2 : ℝ) • d)‖ ≤ ‖Y - X‖ + ‖(1 / 2 : ℝ) • d‖ := by
    rw [← sub_sub]; exact norm_sub_le _ _
  have n4 := norm_sub_le ((2 : ℝ) • (W - Xm) - (Y - (X + (1 / 2 : ℝ) • d))) ((1 / 2 : ℝ) • d)
  rw [e2]
  linarith

/-- **Stability of the implicit midpoint step with a defect.** If `W` is the backward Euler value
of size `τ` from `Y` and `X₁ - X₀ - 2 τ F((X₀ + X₁) / 2) = d` for `F(Z) = M Z - Z CᵀC` with `M`
dissipative, then `‖(2 W - Y) - X₁‖ ≤ ‖Y - X₀‖ + ‖d‖`. -/
theorem norm_two_smul_sub_sub_le_of_implicitMidpoint
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hτ : 0 ≤ τ) {Y W X₀ X₁ d : Matrix m n ℝ}
    (hW : W - τ • (M * W) + τ • (W * (Cᵀ * C)) = Y)
    (hX : X₁ - X₀ - (2 * τ) • (M * ((1 / 2 : ℝ) • (X₀ + X₁)) -
      (1 / 2 : ℝ) • (X₀ + X₁) * (Cᵀ * C)) = d) :
    ‖(2 : ℝ) • W - Y - X₁‖ ≤ ‖Y - X₀‖ + ‖d‖ := by
  have hXm : (1 / 2 : ℝ) • (X₀ + X₁) - τ • (M * ((1 / 2 : ℝ) • (X₀ + X₁))) +
      τ • ((1 / 2 : ℝ) • (X₀ + X₁) * (Cᵀ * C)) = X₀ + (1 / 2 : ℝ) • d := by
    rw [← hX]
    generalize M * ((1 / 2 : ℝ) • (X₀ + X₁)) = p
    generalize (1 / 2 : ℝ) • (X₀ + X₁) * (Cᵀ * C) = q
    module
  have h1 := norm_two_smul_sub_sub_le_of_midpoint hdiss hτ hW hXm
  have e : (2 : ℝ) • ((1 / 2 : ℝ) • (X₀ + X₁)) - X₀ = X₁ := by module
  rwa [e] at h1

/-- **Error of any sequence against an implicit midpoint reference: the factor one.** Let
`F(Z) = M Z - Z CᵀC` with `M` dissipative, let `X_{j+1} - X_j - 2 τ F((X_j + X_{j+1}) / 2) = d_j`
and let `W_j` be the backward Euler step of size `τ` of the full problem from `Y_j`, so that
`2 W_j - Y_j` is the implicit midpoint step of size `2 τ`. Then

  `‖Y_N - X_N‖ ≤ ‖Y₀ - X₀‖ + ∑_{j<N} (‖d_j‖ + ‖Y_{j+1} - (2 W_j - Y_j)‖)`.

The start error is not amplified, whatever the sequence `Y_j` and the step size are. -/
theorem norm_sub_le_add_sum_of_implicitMidpoint {N : ℕ} {Y W X d : ℕ → Matrix m n ℝ}
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hτ : 0 ≤ τ)
    (hW : ∀ j < N, W j - τ • (M * W j) + τ • (W j * (Cᵀ * C)) = Y j)
    (hX : ∀ j < N, X (j + 1) - X j - (2 * τ) • (M * ((1 / 2 : ℝ) • (X j + X (j + 1))) -
      (1 / 2 : ℝ) • (X j + X (j + 1)) * (Cᵀ * C)) = d j) :
    ‖Y N - X N‖ ≤
      ‖Y 0 - X 0‖ + ∑ j ∈ range N, (‖d j‖ + ‖Y (j + 1) - ((2 : ℝ) • W j - Y j)‖) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun j hj => hW j (Nat.lt_succ_of_lt hj))
      fun j hj => hX j (Nat.lt_succ_of_lt hj)
    have n1 := norm_two_smul_sub_sub_le_of_implicitMidpoint hdiss hτ (hW n (Nat.lt_succ_self n))
      (hX n (Nat.lt_succ_self n))
    have e3 : Y (n + 1) - X (n + 1) =
        Y (n + 1) - ((2 : ℝ) • W n - Y n) + ((2 : ℝ) • W n - Y n - X (n + 1)) := by abel
    have n3 := norm_add_le (Y (n + 1) - ((2 : ℝ) • W n - Y n)) ((2 : ℝ) • W n - Y n - X (n + 1))
    rw [← e3] at n3
    rw [Finset.sum_range_succ]
    linarith

variable {P Q : Matrix m m ℝ}

/-- **Quasi-optimality of a Galerkin backward Euler step in the energy norm.** Let
`F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ`, let `P`, `Q` be symmetric, let
`Y_g = P Y_g Q` solve the Galerkin equation `Y_g = P (Y₀ + τ F(Y_g)) Q` and let `W` be the backward
Euler step of the full problem from `Y₀`. Then for every `Z = P Z Q`

  `√(‖Y_g - Z‖² + τ ‖(Y_g - Z) Cᵀ‖²) ≤ (1 + τ μ) √(‖W - Z‖² + τ ‖(W - Z) Cᵀ‖²)`.

The start value need not lie in the Galerkin space, and `C` does not enter the constant. -/
theorem sqrt_sq_norm_galerkin_sub_add_le {P : Matrix m m ℝ} {Q : Matrix n n ℝ}
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hτ : 0 ≤ τ)
    (hPt : Pᵀ = P) (hQt : Qᵀ = Q) {Y₀ Yg W Z : Matrix m n ℝ}
    (gEq : Yg = P * (Y₀ + τ • (M * Yg - Yg * (Cᵀ * C))) * Q) (gP : P * Yg = Yg)
    (gQ : Yg * Q = Yg) (hW : W - τ • (M * W) + τ • (W * (Cᵀ * C)) = Y₀)
    (zP : P * Z = Z) (zQ : Z * Q = Z) :
    √(‖Yg - Z‖ ^ 2 + τ * ‖(Yg - Z) * Cᵀ‖ ^ 2) ≤
      (1 + τ * μ) * √(‖W - Z‖ ^ 2 + τ * ‖(W - Z) * Cᵀ‖ ^ 2) := by
  obtain ⟨r, hr⟩ : ∃ r, r = Yg - (Y₀ + τ • (M * Yg - Yg * (Cᵀ * C))) := ⟨_, rfl⟩
  have hr0 : P * r * Q = 0 := by
    rw [hr, Matrix.mul_sub, Matrix.sub_mul, ← gEq, gP, gQ, sub_self]
  have hθ : P * ((Yg - Z) * Q) = Yg - Z := by
    rw [Matrix.sub_mul, Matrix.mul_sub, gQ, zQ, gP, zP]
  have h0 : ⟪r, Yg - Z⟫ = 0 := by
    have h1 : ⟪P * r * Q, Yg - Z⟫ = ⟪r, Yg - Z⟫ := by
      rw [inner_mul_proj hQt, inner_proj_mul hPt, hθ]
    rw [← h1, hr0, inner_zero_left]
  have hr2 : r = (Yg - Z + τ • ((Yg - Z) * (Cᵀ * C))) - τ • (M * (Yg - Z)) -
      ((W - Z + τ • ((W - Z) * (Cᵀ * C))) - τ • (M * (W - Z))) := by
    rw [hr, ← hW]
    simp only [Matrix.mul_sub, Matrix.sub_mul, smul_sub]
    abel
  rw [hr2] at h0
  simp only [inner_sub_left, real_inner_smul_left] at h0
  rw [inner_add_smul_mul_gram_self] at h0
  have c1 := inner_add_smul_mul_gram_le C hτ (W - Z) (Yg - Z)
  have c2 : -⟪M * (W - Z), Yg - Z⟫ ≤ μ * ‖W - Z‖ * ‖Yg - Z‖ :=
    ((neg_le_abs _).trans (abs_real_inner_le_norm _ _)).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le_mul_norm hμ0 hμ (W - Z)) (norm_nonneg _))
  have c3 := inner_mul_self_nonpos hdiss (Yg - Z)
  have a1 := norm_le_sqrt_sq_norm_add C hτ (W - Z)
  have a2 := norm_le_sqrt_sq_norm_add C hτ (Yg - Z)
  have s0 : 0 ≤ ‖Yg - Z‖ ^ 2 + τ * ‖(Yg - Z) * Cᵀ‖ ^ 2 :=
    add_nonneg (sq_nonneg _) (mul_nonneg hτ (sq_nonneg _))
  have s1 := Real.sq_sqrt s0
  have s2 := Real.sqrt_nonneg (‖Yg - Z‖ ^ 2 + τ * ‖(Yg - Z) * Cᵀ‖ ^ 2)
  have s3 := Real.sqrt_nonneg (‖W - Z‖ ^ 2 + τ * ‖(W - Z) * Cᵀ‖ ^ 2)
  have c4 : μ * ‖W - Z‖ * ‖Yg - Z‖ ≤ μ * √(‖W - Z‖ ^ 2 + τ * ‖(W - Z) * Cᵀ‖ ^ 2) *
      √(‖Yg - Z‖ ^ 2 + τ * ‖(Yg - Z) * Cᵀ‖ ^ 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_left a1 hμ0) a2 (norm_nonneg _) (mul_nonneg hμ0 s3)
  have c5 := mul_nonpos_of_nonneg_of_nonpos hτ c3
  have c6 := mul_le_mul_of_nonneg_left (c2.trans c4) hτ
  refine le_of_sq_le_mul (mul_nonneg (by positivity) s3) ?_
  linarith [h0, c1, c5, c6, s1]

/-- The Galerkin backward Euler step against the backward Euler step of the full problem in the
Frobenius norm: `‖Y_g - W‖ ≤ (2 + τ μ) √(‖W - Z‖² + τ ‖(W - Z) Cᵀ‖²)` for every `Z = P Z Q`. -/
theorem norm_galerkin_sub_backwardEuler_le {P : Matrix m m ℝ} {Q : Matrix n n ℝ}
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hτ : 0 ≤ τ)
    (hPt : Pᵀ = P) (hQt : Qᵀ = Q) {Y₀ Yg W Z : Matrix m n ℝ}
    (gEq : Yg = P * (Y₀ + τ • (M * Yg - Yg * (Cᵀ * C))) * Q) (gP : P * Yg = Yg)
    (gQ : Yg * Q = Yg) (hW : W - τ • (M * W) + τ • (W * (Cᵀ * C)) = Y₀)
    (zP : P * Z = Z) (zQ : Z * Q = Z) :
    ‖Yg - W‖ ≤ (2 + τ * μ) * √(‖W - Z‖ ^ 2 + τ * ‖(W - Z) * Cᵀ‖ ^ 2) := by
  have h1 := sqrt_sq_norm_galerkin_sub_add_le hdiss hμ0 hμ hτ hPt hQt gEq gP gQ hW zP zQ
  have a1 := norm_le_sqrt_sq_norm_add C hτ (W - Z)
  have a2 := norm_le_sqrt_sq_norm_add C hτ (Yg - Z)
  have e : Yg - W = Yg - Z - (W - Z) := by abel
  have n1 := norm_sub_le (Yg - Z) (W - Z)
  rw [← e] at n1
  linarith

end Lemmas

section TwoLevel

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] {M : Matrix m m ℝ}
  {C : Matrix k n ℝ} {τ μ : ℝ} {P₁ : Matrix m m ℝ} {Q₁ : Matrix n n ℝ}
  {Y₀ YK YL Y₁ W : Matrix m n ℝ}

/-- **The residual of the combination of two levels.** Let `Y₀ = P₁ Y₀ Q₁`, let `Y_K` be the K-step
with the rows projected by `Q₁`, `Y_L` the L-step with the columns projected by `P₁` and `Y₁` the
Galerkin step with `P₁`, `Q₁`, all backward Euler steps of size `τ` from `Y₀` for
`F(Z) = M Z - Z CᵀC`, and let `W` be the backward Euler step of the full problem. Then
`D = W - (Y_K + Y_L - Y₁)` satisfies

  `D - τ M D + τ D CᵀC = τ (1 - P₁) M (Y_L - Y₁) - τ (Y_K - Y₁) CᵀC (1 - Q₁)`.

The right-hand side consists of differences of steps of the first level; `P₁`, `Q₁` need not be
projectors. -/
theorem backwardEuler_sub_combination_eq (yP : P₁ * Y₀ = Y₀) (yQ : Y₀ * Q₁ = Y₀)
    (kEq : YK = Y₀ + τ • ((M * YK - YK * (Cᵀ * C)) * Q₁)) (kQ : YK * Q₁ = YK)
    (lEq : YL = Y₀ + τ • (P₁ * (M * YL - YL * (Cᵀ * C)))) (lP : P₁ * YL = YL)
    (sEq : Y₁ = P₁ * (Y₀ + τ • (M * Y₁ - Y₁ * (Cᵀ * C))) * Q₁) (sP : P₁ * Y₁ = Y₁)
    (sQ : Y₁ * Q₁ = Y₁) (hW : W - τ • (M * W) + τ • (W * (Cᵀ * C)) = Y₀) :
    W - (YK + YL - Y₁) - τ • (M * (W - (YK + YL - Y₁))) +
        τ • ((W - (YK + YL - Y₁)) * (Cᵀ * C)) =
      τ • (M * (YL - Y₁) - P₁ * (M * (YL - Y₁))) -
        τ • ((YK - Y₁) * (Cᵀ * C) - (YK - Y₁) * (Cᵀ * C) * Q₁) := by
  have k0 : (M * YK - YK * (Cᵀ * C)) * Q₁ = M * YK - YK * (Cᵀ * C) * Q₁ := by
    rw [Matrix.sub_mul, Matrix.mul_assoc M, kQ]
  have l0 : P₁ * (M * YL - YL * (Cᵀ * C)) = P₁ * (M * YL) - YL * (Cᵀ * C) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc P₁ YL, lP]
  have s0 : P₁ * (Y₀ + τ • (M * Y₁ - Y₁ * (Cᵀ * C))) * Q₁ =
      Y₀ + τ • (P₁ * (M * Y₁) - Y₁ * (Cᵀ * C) * Q₁) := by
    rw [Matrix.mul_add, Matrix.add_mul, yP, yQ, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc P₁ (M * Y₁) Q₁, Matrix.mul_assoc M Y₁ Q₁,
      sQ, ← Matrix.mul_assoc P₁ Y₁, sP]
  rw [k0] at kEq
  rw [l0] at lEq
  rw [s0] at sEq
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul]
  linear_combination (norm := module) hW - kEq - lEq + sEq

/-- **The combination of two levels approximates the backward Euler step of the full problem**
in the energy norm, with a bound by two computable terms:

  `√(‖D‖² + τ ‖D Cᵀ‖²) ≤ ‖τ (1 - P₁) M (Y_L - Y₁)‖ + ‖τ (Y_K - Y₁) CᵀC (1 - Q₁)‖`,

`D = W - (Y_K + Y_L - Y₁)`, for a dissipative `M`. -/
theorem sqrt_sq_norm_backwardEuler_sub_combination_add_le
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hτ : 0 ≤ τ) (yP : P₁ * Y₀ = Y₀)
    (yQ : Y₀ * Q₁ = Y₀)
    (kEq : YK = Y₀ + τ • ((M * YK - YK * (Cᵀ * C)) * Q₁)) (kQ : YK * Q₁ = YK)
    (lEq : YL = Y₀ + τ • (P₁ * (M * YL - YL * (Cᵀ * C)))) (lP : P₁ * YL = YL)
    (sEq : Y₁ = P₁ * (Y₀ + τ • (M * Y₁ - Y₁ * (Cᵀ * C))) * Q₁) (sP : P₁ * Y₁ = Y₁)
    (sQ : Y₁ * Q₁ = Y₁) (hW : W - τ • (M * W) + τ • (W * (Cᵀ * C)) = Y₀) :
    √(‖W - (YK + YL - Y₁)‖ ^ 2 + τ * ‖(W - (YK + YL - Y₁)) * Cᵀ‖ ^ 2) ≤
      ‖τ • (M * (YL - Y₁) - P₁ * (M * (YL - Y₁)))‖ +
        ‖τ • ((YK - Y₁) * (Cᵀ * C) - (YK - Y₁) * (Cᵀ * C) * Q₁)‖ :=
  (sqrt_sq_norm_add_le_of_backwardEuler_of_nonneg hdiss hτ
    (backwardEuler_sub_combination_eq yP yQ kEq kQ lEq lP sEq sP sQ hW)).trans (norm_sub_le _ _)

end TwoLevel

section Run

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] {M : Matrix m m ℝ}
  {C : Matrix k n ℝ} {τ μ : ℝ} {N : ℕ} {ϑ : ℕ → ℝ} {P P₁ : ℕ → Matrix m m ℝ}
  {Q Q₁ : ℕ → Matrix n n ℝ} {Y Ym W Z X d YK YL Y₁ : ℕ → Matrix m n ℝ}

/-- **Run bound for implicit midpoint Galerkin steps, with the factor one on the start error.**
Let `F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ`, and let the reference satisfy
`X_{j+1} - X_j - 2 τ F((X_j + X_{j+1}) / 2) = d_j`. In step `j` let `Ym_j = P_j Ym_j Q_j` be the
Galerkin backward Euler step of size `τ` from `Y_j` with symmetric `P_j`, `Q_j`, and let `Y_{j+1}`
differ from `2 Ym_j - Y_j` by at most `ϑ_j` (any truncation). Then for the backward Euler steps
`W_j` of the full problem from `Y_j` and all `Z_j = P_j Z_j Q_j`

  `‖Y_N - X_N‖ ≤ ‖Y₀ - X₀‖ + ∑_{j<N} (‖d_j‖ + ϑ_j +`
  `    2 (2 + τ μ) √(‖W_j - Z_j‖² + τ ‖(W_j - Z_j) Cᵀ‖²))`.

The local error is the distance in the energy norm of the midpoint value of the full step to the
Galerkin space; nothing depends on `C`, on singular values or on the size of `τ μ`. -/
theorem norm_galerkinMidpoint_run_sub_le
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hτ : 0 ≤ τ)
    (hstep : ∀ j < N, (P j)ᵀ = P j ∧ (Q j)ᵀ = Q j ∧ P j * Ym j = Ym j ∧ Ym j * Q j = Ym j ∧
      Ym j = P j * (Y j + τ • (M * Ym j - Ym j * (Cᵀ * C))) * Q j ∧ P j * Z j = Z j ∧
      Z j * Q j = Z j ∧ ‖Y (j + 1) - ((2 : ℝ) • Ym j - Y j)‖ ≤ ϑ j)
    (hW : ∀ j < N, W j - τ • (M * W j) + τ • (W j * (Cᵀ * C)) = Y j)
    (hX : ∀ j < N, X (j + 1) - X j - (2 * τ) • (M * ((1 / 2 : ℝ) • (X j + X (j + 1))) -
      (1 / 2 : ℝ) • (X j + X (j + 1)) * (Cᵀ * C)) = d j) :
    ‖Y N - X N‖ ≤ ‖Y 0 - X 0‖ + ∑ j ∈ range N, (‖d j‖ + ϑ j +
      2 * ((2 + τ * μ) * √(‖W j - Z j‖ ^ 2 + τ * ‖(W j - Z j) * Cᵀ‖ ^ 2))) := by
  refine (norm_sub_le_add_sum_of_implicitMidpoint hdiss hτ hW hX).trans ?_
  refine add_le_add le_rfl (Finset.sum_le_sum fun j hj => ?_)
  have hj' := Finset.mem_range.1 hj
  obtain ⟨hPt, hQt, gP, gQ, gEq, zP, zQ, hϑ⟩ := hstep j hj'
  have h1 := norm_galerkin_sub_backwardEuler_le hdiss hμ0 hμ hτ hPt hQt gEq gP gQ (hW j hj') zP zQ
  have e : Y (j + 1) - ((2 : ℝ) • W j - Y j) =
      Y (j + 1) - ((2 : ℝ) • Ym j - Y j) + (2 : ℝ) • (Ym j - W j) := by module
  have n1 := norm_add_le (Y (j + 1) - ((2 : ℝ) • Ym j - Y j)) ((2 : ℝ) • (Ym j - W j))
  have n2 : ‖(2 : ℝ) • (Ym j - W j)‖ = 2 * ‖Ym j - W j‖ := by rw [norm_smul]; norm_num
  rw [e]
  linarith

/-- **Run bound for the implicit midpoint Galerkin step in bases of two levels.** Let
`F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ`, and let the reference satisfy
`X_{j+1} - X_j - 2 τ F((X_j + X_{j+1}) / 2) = d_j`. In step `j` let `Y_j = P₁ Y_j Q₁`, let `Y_K`,
`Y_L`, `Y₁` be the K-step with rows in `Q₁`, the L-step with columns in `P₁` and the Galerkin step
with `P₁`, `Q₁` (backward Euler of size `τ` from `Y_j`), let the symmetric `P`, `Q` capture all
three, let
`Ym = P Ym Q` be the Galerkin backward Euler step of size `τ` with `P`, `Q`, and let `Y_{j+1}`
differ from `2 Ym - Y_j` by at most `ϑ_j`. Then

  `‖Y_N - X_N‖ ≤ ‖Y₀ - X₀‖ + ∑_{j<N} (‖d_j‖ + ϑ_j +`
  `    2 (2 + τ μ) (‖τ (1 - P₁) M (Y_L - Y₁)‖ + ‖τ (Y_K - Y₁) CᵀC (1 - Q₁)‖))`.

Every term of the sum can be evaluated along the run. -/
theorem norm_twoLevelMidpoint_run_sub_le
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hτ : 0 ≤ τ)
    (hlevel : ∀ j < N, P₁ j * Y j = Y j ∧ Y j * Q₁ j = Y j ∧
      YK j = Y j + τ • ((M * YK j - YK j * (Cᵀ * C)) * Q₁ j) ∧ YK j * Q₁ j = YK j ∧
      YL j = Y j + τ • (P₁ j * (M * YL j - YL j * (Cᵀ * C))) ∧ P₁ j * YL j = YL j ∧
      Y₁ j = P₁ j * (Y j + τ • (M * Y₁ j - Y₁ j * (Cᵀ * C))) * Q₁ j ∧ P₁ j * Y₁ j = Y₁ j ∧
      Y₁ j * Q₁ j = Y₁ j)
    (hcap : ∀ j < N, P j * YK j = YK j ∧ P j * YL j = YL j ∧ P j * Y₁ j = Y₁ j ∧
      YK j * Q j = YK j ∧ YL j * Q j = YL j ∧ Y₁ j * Q j = Y₁ j)
    (hstep : ∀ j < N, (P j)ᵀ = P j ∧ (Q j)ᵀ = Q j ∧ P j * Ym j = Ym j ∧ Ym j * Q j = Ym j ∧
      Ym j = P j * (Y j + τ • (M * Ym j - Ym j * (Cᵀ * C))) * Q j ∧
      ‖Y (j + 1) - ((2 : ℝ) • Ym j - Y j)‖ ≤ ϑ j)
    (hX : ∀ j < N, X (j + 1) - X j - (2 * τ) • (M * ((1 / 2 : ℝ) • (X j + X (j + 1))) -
      (1 / 2 : ℝ) • (X j + X (j + 1)) * (Cᵀ * C)) = d j) :
    ‖Y N - X N‖ ≤ ‖Y 0 - X 0‖ + ∑ j ∈ range N, (‖d j‖ + ϑ j + 2 * ((2 + τ * μ) *
      (‖τ • (M * (YL j - Y₁ j) - P₁ j * (M * (YL j - Y₁ j)))‖ +
        ‖τ • ((YK j - Y₁ j) * (Cᵀ * C) - (YK j - Y₁ j) * (Cᵀ * C) * Q₁ j)‖))) := by
  choose W hW using fun j => exists_backwardEuler (M := M) (C := C) (h := τ) hdiss hτ (Y j)
  have h1 := norm_galerkinMidpoint_run_sub_le (Z := fun j => YK j + YL j - Y₁ j) (W := W) (X := X)
    (d := d) (ϑ := ϑ) (P := P) (Q := Q) (Ym := Ym) (Y := Y) (N := N) hdiss hμ0 hμ hτ
    (fun j hj => by
      obtain ⟨hPt, hQt, gP, gQ, gEq, hϑ⟩ := hstep j hj
      obtain ⟨pK, pL, pS, qK, qL, qS⟩ := hcap j hj
      refine ⟨hPt, hQt, gP, gQ, gEq, ?_, ?_, hϑ⟩
      · rw [Matrix.mul_sub, Matrix.mul_add, pK, pL, pS]
      · rw [Matrix.sub_mul, Matrix.add_mul, qK, qL, qS])
    (fun j _ => hW j) hX
  refine h1.trans (add_le_add le_rfl (Finset.sum_le_sum fun j hj => ?_))
  obtain ⟨yP, yQ, kEq, kQ, lEq, lP, sEq, sP, sQ⟩ := hlevel j (Finset.mem_range.1 hj)
  have h2 := sqrt_sq_norm_backwardEuler_sub_combination_add_le hdiss hτ yP yQ kEq kQ lEq lP sEq
    sP sQ (hW j)
  have h3 : 0 ≤ 2 + τ * μ := by positivity
  have h4 := mul_le_mul_of_nonneg_left h2 h3
  linarith

end Run

end ImplicitMidpointBUGStiff

/-! ### The hypotheses can hold -/

namespace ImplicitMidpointBUGStiffExample

open ImplicitMidpointBUGStiff

/-- The hypotheses of `ImplicitMidpointBUGStiff.norm_twoLevelMidpoint_run_sub_le` hold for one step
from any start value, for every dissipative `M`, every `C` and every `τ ≥ 0`, with the identity as
projectors of both levels: all steps are then the backward Euler step of the full problem. -/
example {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n]
    {M : Matrix m m ℝ} {C : Matrix k n ℝ} {τ : ℝ} (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
    (hτ : 0 ≤ τ) (Y₀ : Matrix m n ℝ) :
    ∃ (Y Ym YK YL Y₁ : ℕ → Matrix m n ℝ) (P P₁ : ℕ → Matrix m m ℝ) (Q Q₁ : ℕ → Matrix n n ℝ),
      Y 0 = Y₀ ∧
      (∀ j < 1, P₁ j * Y j = Y j ∧ Y j * Q₁ j = Y j ∧
        YK j = Y j + τ • ((M * YK j - YK j * (Cᵀ * C)) * Q₁ j) ∧ YK j * Q₁ j = YK j ∧
        YL j = Y j + τ • (P₁ j * (M * YL j - YL j * (Cᵀ * C))) ∧ P₁ j * YL j = YL j ∧
        Y₁ j = P₁ j * (Y j + τ • (M * Y₁ j - Y₁ j * (Cᵀ * C))) * Q₁ j ∧ P₁ j * Y₁ j = Y₁ j ∧
        Y₁ j * Q₁ j = Y₁ j) ∧
      (∀ j < 1, P j * YK j = YK j ∧ P j * YL j = YL j ∧ P j * Y₁ j = Y₁ j ∧
        YK j * Q j = YK j ∧ YL j * Q j = YL j ∧ Y₁ j * Q j = Y₁ j) ∧
      ∀ j < 1, (P j)ᵀ = P j ∧ (Q j)ᵀ = Q j ∧ P j * Ym j = Ym j ∧ Ym j * Q j = Ym j ∧
        Ym j = P j * (Y j + τ • (M * Ym j - Ym j * (Cᵀ * C))) * Q j ∧
        ‖Y (j + 1) - ((2 : ℝ) • Ym j - Y j)‖ ≤ 0 := by
  obtain ⟨W, hW⟩ := ImplicitBUGStiffLocal.exists_backwardEuler (C := C) hdiss hτ Y₀
  have e : W = Y₀ + τ • (M * W - W * (Cᵀ * C)) := by
    rw [← hW, smul_sub]; abel
  refine ⟨fun j => if j = 0 then Y₀ else (2 : ℝ) • W - Y₀, fun _ => W, fun _ => W, fun _ => W,
    fun _ => W, fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 1, by simp, ?_, ?_, ?_⟩
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp only [ite_true, Matrix.one_mul, Matrix.mul_one, true_and, and_true]
    exact ⟨e, e, e⟩
  · intro j _
    simp only [Matrix.one_mul, Matrix.mul_one, and_self]
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp only [ite_true, Matrix.one_mul, Matrix.mul_one, Matrix.transpose_one, true_and,
      zero_add, one_ne_zero, ite_false, sub_self, norm_zero, le_refl, and_true]
    exact e

end ImplicitMidpointBUGStiffExample

end LeanDLRA
