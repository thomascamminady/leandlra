import LeanDLRA.Research.ImplicitBUGStiffRows

/-!
# The implicit BUG integrator with a stiff row operator: a weighted Lyapunov functional

Let `F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ` and `C` arbitrary: the matrix
`N = -CᵀC` acting on the rows is symmetric negative semidefinite of any norm (the stiffness). A
step of the fixed-rank BUG integrator with backward Euler substeps can lose `≈ h μ ‖Y₀‖` from a
start error `≈ (h ‖N‖)^{-1/2}` (`StiffRowsExample.not_exists_forall_norm_sub_le`), so no one-step
bound `C₁ e₀ + C₂ h²` holds uniformly in `‖N‖`. This file shows for every rank that runs are
nevertheless uniform in the stiffness if the reference has its rows in the kernel of `N`: let `Q`
be an orthogonal projector with `C Q = 0`. Then, for every `C`,

  `‖Y₁ (1 - Q)‖² + 2 h ‖U₀ L₁ᵀ Cᵀ‖² ≤ (1 + 5 h μ) ‖Y₀ (1 - Q)‖²`       (one step),
  `‖Y_N - X_N‖ ≤ ‖Y₀ Q - X₀‖ + 2 h μ ‖Y₀‖ + (1 + 4 h μ √N) √((1 + 5 h μ)^N) ‖Y₀ (1 - Q)‖`

for backward Euler steps `X_{j+1} - h M X_{j+1} = X_j` of a reference with rows in the range of
`Q`. The Lyapunov functional is `‖Y (1 - Q)‖²`: the angles between the numerical row space and
the range of `Q`, weighted by the singular values of `Y`. Its decrease pays the stiff energy
`h ‖Y Cᵀ‖²` of all later steps, and the loss of a step is `h μ` times the square root of a stiff
energy.

## Main results

* `IsMatrixImplicitBUGStep.sq_norm_mul_compl_add_le_of_sylvester`: the Lyapunov inequality of
  one step.
* `IsMatrixImplicitBUGStep.norm_mul_transpose_le_of_sylvester`: the stiff energy after a step
  against the stiff energy of the L-step result (no kernel condition).
* `IsMatrixImplicitBUGStep.norm_mul_sub_le_of_sylvester`: the part on the range of `Q` after one
  step against a backward Euler step of the reference.
* `sq_norm_implicitBUG_run_mul_compl_add_le_of_sylvester`: the Lyapunov inequality along a run.
* `norm_implicitBUG_run_sub_le_of_sylvester`: the run bound.

## Implementation notes

The proofs work with the orthogonal projectors `P₀ = U₀ U₀ᵀ`, `P₁ = U₁ U₁ᵀ`, `Q₀`, `Q₁` and the
matrices `Y_K = K₁ V₀ᵀ`, `Y_L = U₀ L₁ᵀ`, `Y₁ = U₁ S₁ V₁ᵀ`. Subtracting the L-step from the S-step
gives `Y₁ - P₁ Y_L = P₁ (h M (Y₁ - P₁ Y_L) - h (Y₁ - P₁ Y_L) CᵀC + h (M P₁ - P₀ M) Y_L) Q₁`: the
stiff terms of the two substeps cancel. With the Galerkin resolvent `Ξ` of the new column space,
`Ξ - h P₁ M Ξ = P₁ (1 - h P₀ M)`, the remainder `D = Y₁ - Ξ Y_L` solves a Galerkin equation with
the source `-h (Ξ - P₁) Y_L CᵀC`, and its energy estimate gives `‖D‖ ≤ h μ √h ‖Y_L Cᵀ‖`. The
dissipativity and the bound of `M` are stated for vectors, so that they apply to matrices with
any number of columns.

## References

* [CerutiLubich2022] for the BUG integrator; backward Euler substeps as in arXiv 2610.18419.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius
open Matrix

namespace LeanDLRA

namespace ImplicitBUGWeightedRows

private theorem orth_mul_cancel {m k p : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) (X : Matrix k p ℝ) : Uᵀ * (U * X) = X := by
  rw [← Matrix.mul_assoc, hU, Matrix.one_mul]

section Lemmas

variable {m n k p : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype p]

/-- A matrix with nonpositive quadratic form is dissipative on matrices with any number of
columns, in the Frobenius inner product. -/
private theorem inner_mul_self_nonpos {M : Matrix m m ℝ} (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
    (Z : Matrix m p ℝ) : ⟪M * Z, Z⟫ ≤ 0 := by
  rw [Frobenius.inner_def, Finset.sum_comm]
  refine Finset.sum_nonpos fun j _ => ?_
  have h := hdiss fun i => Z i j
  have e : ∑ i, (M * Z) i j * Z i j = (fun i => Z i j) ⬝ᵥ M *ᵥ fun i => Z i j := by
    simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  exact h

/-- A bound of the quadratic form of `Mᵀ M` bounds left multiplication by `M` in the Frobenius
norm. -/
private theorem norm_mul_le_mul_norm {M : Matrix m m ℝ} {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (Z : Matrix m p ℝ) :
    ‖M * Z‖ ≤ μ * ‖Z‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hμ0 (norm_nonneg _)) two_ne_zero).1 ?_
  rw [mul_pow, Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum, Finset.sum_comm,
    Finset.sum_comm (f := fun i j => Z i j ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h := hμ fun i => Z i j
  have e1 : ∑ i, (M * Z) i j ^ 2 = (M *ᵥ fun i => Z i j) ⬝ᵥ (M *ᵥ fun i => Z i j) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply, sq]
  have e2 : ∑ i, Z i j ^ 2 = (fun i => Z i j) ⬝ᵥ fun i => Z i j := by
    simp only [dotProduct, sq]
  rw [e1, e2]
  exact h

/-- Left multiplication by a symmetric idempotent matrix is self-adjoint. -/
private theorem inner_proj_mul {P : Matrix m m ℝ} (hPt : Pᵀ = P) (A B : Matrix m p ℝ) :
    ⟪P * A, B⟫ = ⟪A, P * B⟫ := by
  rw [Frobenius.inner_mul_left, hPt]

/-- Right multiplication by a symmetric idempotent matrix is self-adjoint. -/
private theorem inner_mul_proj {Q : Matrix n n ℝ} (hQt : Qᵀ = Q) (A B : Matrix m n ℝ) :
    ⟪A * Q, B⟫ = ⟪A, B * Q⟫ := by
  rw [Frobenius.inner_mul_right, hQt]

private theorem le_of_sq_le_mul {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b * a) :
    a ≤ b := by
  by_contra hc
  rw [not_le] at hc
  nlinarith [hb, h, hc]

/-- Left multiplication by an orthogonal projector does not increase the Frobenius norm. -/
private theorem norm_proj_mul_le {P : Matrix m m ℝ} (hP : P * P = P) (hPt : Pᵀ = P)
    (A : Matrix m p ℝ) : ‖P * A‖ ≤ ‖A‖ := by
  refine le_of_sq_le_mul (norm_nonneg _) ?_
  rw [← real_inner_self_eq_norm_sq, inner_proj_mul hPt, ← Matrix.mul_assoc, hP]
  exact real_inner_le_norm _ _

/-- Right multiplication by an orthogonal projector does not increase the Frobenius norm. -/
private theorem norm_mul_proj_le {Q : Matrix n n ℝ} (hQ : Q * Q = Q) (hQt : Qᵀ = Q)
    (A : Matrix m n ℝ) : ‖A * Q‖ ≤ ‖A‖ := by
  refine le_of_sq_le_mul (norm_nonneg _) ?_
  rw [← real_inner_self_eq_norm_sq, inner_mul_proj hQt, Matrix.mul_assoc, hQ]
  exact real_inner_le_norm _ _

/-- **Energy estimate of a Galerkin backward Euler step** for a dissipative `M` on the range of
an orthogonal projector `P`: if `W = P W` and `W - h P M W = P R`, then `‖W‖ ≤ ‖R‖`. -/
private theorem norm_le_of_galerkin {M P : Matrix m m ℝ} {h : ℝ}
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hPt : Pᵀ = P) (hh : 0 ≤ h) {W R : Matrix m p ℝ}
    (hW : P * W = W) (heq : W - h • (P * (M * W)) = P * R) : ‖W‖ ≤ ‖R‖ := by
  refine le_of_sq_le_mul (norm_nonneg _) ?_
  have e : W = h • (P * (M * W)) + P * R := by rw [← heq]; abel
  have h1 : ⟪W, W⟫ = h * ⟪M * W, W⟫ + ⟪R, W⟫ := by
    have h0 : ⟪W, W⟫ = ⟪h • (P * (M * W)) + P * R, W⟫ := congrArg (fun X => ⟪X, W⟫) e
    rw [h0, inner_add_left, real_inner_smul_left, inner_proj_mul hPt, inner_proj_mul hPt, hW]
  rw [← real_inner_self_eq_norm_sq, h1]
  nlinarith [inner_mul_self_nonpos hdiss W, real_inner_le_norm R W]

/-- **The Galerkin resolvent exists.** For a dissipative `M`, an orthogonal projector `P` and
`h ≥ 0` the equation `Φ - h P M Φ = P G` has a solution with `P Φ = Φ`. -/
private theorem exists_galerkin_resolvent {M P : Matrix m m ℝ} {h : ℝ}
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hP : P * P = P) (hPt : Pᵀ = P) (hh : 0 ≤ h)
    (G : Matrix m m ℝ) : ∃ Φ : Matrix m m ℝ, P * Φ = Φ ∧ Φ - h • (P * (M * Φ)) = P * G := by
  classical
  have hdet : (1 - h • (P * M)).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv
    set W : Matrix m Unit ℝ := Matrix.replicateCol Unit v with hWdef
    have hAW : (1 - h • (P * M)) * W = 0 := by
      ext i j
      have := congrFun hAv i
      simpa [hWdef, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    have hW1 : W = h • (P * (M * W)) := by
      have := hAW
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc, sub_eq_zero] at this
      exact this
    have hPW : P * W = W := by
      conv_lhs => rw [hW1]
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, hP, ← hW1]
    have hle := norm_le_of_galerkin (R := (0 : Matrix m Unit ℝ)) hdiss hPt hh hPW
      (by rw [Matrix.mul_zero, sub_eq_zero]; exact hW1)
    have hW0 : W = 0 := by simpa using hle
    funext i
    have := congrFun (congrFun hW0 i) ()
    simpa [hWdef] using this
  set Φ := (1 - h • (P * M))⁻¹ * (P * G) with hΦ
  have hA : (1 - h • (P * M)) * Φ = P * G := by
    rw [hΦ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
      Matrix.one_mul]
  have e : Φ = h • (P * (M * Φ)) + P * G := by
    rw [← hA, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc]; abel
  refine ⟨Φ, ?_, ?_⟩
  · have e' : P * Φ = P * (h • (P * (M * Φ)) + P * G) := congrArg (fun X => P * X) e
    rw [e', Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc P P, ← Matrix.mul_assoc P P, hP,
      ← e]
  · rw [← hA, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc]

/-- The three substeps of the integrator for `F(Z) = M Z - Z CᵀC` in terms of the orthogonal
projectors onto the old and new column and row spaces. -/
private structure ProjStep (M : Matrix m m ℝ) (C : Matrix k n ℝ) (h : ℝ) (P₀ P₁ : Matrix m m ℝ)
    (Q₀ Q₁ : Matrix n n ℝ) (Y₀ YK YL Y₁ : Matrix m n ℝ) : Prop where
  hP₀ : P₀ * P₀ = P₀
  hP₀t : P₀ᵀ = P₀
  hP₁ : P₁ * P₁ = P₁
  hP₁t : P₁ᵀ = P₁
  hQ₀t : Q₀ᵀ = Q₀
  hQ₁t : Q₁ᵀ = Q₁
  kEq : YK = Y₀ + h • ((M * YK - YK * (Cᵀ * C)) * Q₀)
  kQ : YK * Q₀ = YK
  kP : P₁ * YK = YK
  yQ : Y₀ * Q₀ = Y₀
  lEq : YL = Y₀ + h • (P₀ * (M * YL - YL * (Cᵀ * C)))
  lP : P₀ * YL = YL
  lQ : YL * Q₁ = YL
  sEq : Y₁ = P₁ * (Y₀ + h • (M * Y₁ - Y₁ * (Cᵀ * C))) * Q₁
  sP : P₁ * Y₁ = Y₁
  sQ : Y₁ * Q₁ = Y₁

variable {M : Matrix m m ℝ} {C : Matrix k n ℝ} {h μ : ℝ} {P₀ P₁ : Matrix m m ℝ}
  {Q₀ Q₁ Q : Matrix n n ℝ} {Y₀ YK YL Y₁ : Matrix m n ℝ}

omit [Fintype k] in
private theorem mul_transpose_eq_zero (hQt : Qᵀ = Q) (hCQ : C * Q = 0) : Q * Cᵀ = 0 := by
  have := congrArg Matrix.transpose hCQ
  rwa [Matrix.transpose_mul, hQt, Matrix.transpose_zero] at this

/-- **The L-step in the kernel class.** The part of the L-step result outside the reference row
space and twice its stiff energy are bounded by the same part of the start value. -/
private theorem ProjStep.lstep_energy [DecidableEq n] (hs : ProjStep M C h P₀ P₁ Q₀ Q₁ Y₀ YK YL Y₁)
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 ≤ h) (hQt : Qᵀ = Q) (hCQ : C * Q = 0) :
    ‖YL * (1 - Q)‖ ^ 2 + 2 * (h * ‖YL * Cᵀ‖ ^ 2) ≤ ‖Y₀ * (1 - Q)‖ ^ 2 := by
  have hQC := mul_transpose_eq_zero hQt hCQ
  set X := YL * (1 - Q) with hX
  have hXC : X * Cᵀ = YL * Cᵀ := by
    rw [hX, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hQC, sub_zero]
  have hCCQ : Cᵀ * C * (1 - Q) = Cᵀ * C := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, hCQ, Matrix.mul_zero, sub_zero]
  have eX : X = Y₀ * (1 - Q) + h • (P₀ * (M * X - YL * (Cᵀ * C))) := by
    have := congrArg (fun A => A * (1 - Q)) hs.lEq
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc P₀, Matrix.sub_mul, Matrix.mul_assoc M,
      Matrix.mul_assoc YL (Cᵀ * C), hCCQ] at this
    exact this
  have hPX : P₀ * X = X := by rw [hX, ← Matrix.mul_assoc, hs.lP]
  have h1 : ⟪X, X⟫ = ⟪Y₀ * (1 - Q), X⟫ + h * (⟪M * X, X⟫ - ⟪YL * Cᵀ, YL * Cᵀ⟫) := by
    have h0 : ⟪X, X⟫ = ⟪Y₀ * (1 - Q) + h • (P₀ * (M * X - YL * (Cᵀ * C))), X⟫ :=
      congrArg (fun A => ⟪A, X⟫) eX
    rw [h0, inner_add_left, real_inner_smul_left, inner_proj_mul hs.hP₀t, hPX, inner_sub_left,
      ← Matrix.mul_assoc YL, Frobenius.inner_mul_right (YL * Cᵀ) C X, hXC]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1
  have h2 := real_inner_le_norm (Y₀ * (1 - Q)) X
  have h3 := inner_mul_self_nonpos hdiss X
  nlinarith [sq_nonneg (‖Y₀ * (1 - Q)‖ - ‖X‖), mul_nonneg hh (sq_nonneg ‖YL * Cᵀ‖),
    mul_nonpos_of_nonneg_of_nonpos hh h3]

omit [Fintype p] in
/-- The equation of the Galerkin resolvent composed with the old column projector, applied to a
matrix. -/
private theorem xi_mul_sub [DecidableEq m] {Ξ : Matrix m m ℝ}
    (hΞ : Ξ - h • (P₁ * (M * Ξ)) = P₁ * (1 - h • (P₀ * M))) (X : Matrix m p ℝ) :
    Ξ * X - h • (P₁ * (M * (Ξ * X))) = P₁ * (X - h • (P₀ * (M * X))) := by
  have := congrArg (fun A => A * X) hΞ
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc P₁, Matrix.mul_assoc M,
    Matrix.mul_assoc P₁, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
    Matrix.mul_assoc P₀] at this
  exact this

/-- The Galerkin resolvent composed with the old column projector is bounded by `1 + h μ`. -/
private theorem norm_xi_mul_le [DecidableEq m] {Ξ : Matrix m m ℝ}
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 ≤ h)
    (hP₀ : P₀ * P₀ = P₀) (hP₀t : P₀ᵀ = P₀) (hP₁t : P₁ᵀ = P₁) (hΞP : P₁ * Ξ = Ξ)
    (hΞ : Ξ - h • (P₁ * (M * Ξ)) = P₁ * (1 - h • (P₀ * M))) (X : Matrix m p ℝ) :
    ‖Ξ * X‖ ≤ (1 + h * μ) * ‖X‖ := by
  have hW : P₁ * (Ξ * X) = Ξ * X := by rw [← Matrix.mul_assoc, hΞP]
  refine (norm_le_of_galerkin hdiss hP₁t hh hW (xi_mul_sub hΞ X)).trans ?_
  have h1 : ‖h • (P₀ * (M * X))‖ ≤ h * (μ * ‖X‖) := by
    rw [norm_smul, Real.norm_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left
      ((norm_proj_mul_le hP₀ hP₀t _).trans (norm_mul_le_mul_norm hμ0 hμ X)) hh
  have := norm_sub_le X (h • (P₀ * (M * X)))
  linarith

/-- **The S-step against the L-step.** The result of the S-step is the Galerkin resolvent `Ξ` of
the new column space applied to the result of the L-step, up to a remainder `D` whose norm is
`h μ` times the square root of the stiff energy of the L-step result. The stiff terms of the two
substeps cancel. -/
private theorem ProjStep.exists_sstep_decomposition [DecidableEq m]
    (hs : ProjStep M C h P₀ P₁ Q₀ Q₁ Y₀ YK YL Y₁) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
    (hμ0 : 0 ≤ μ) (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h) :
    ∃ (Ξ : Matrix m m ℝ) (D : Matrix m n ℝ), P₁ * Ξ = Ξ ∧
      Ξ - h • (P₁ * (M * Ξ)) = P₁ * (1 - h • (P₀ * M)) ∧ Y₁ = Ξ * YL + D ∧
      ‖D‖ ≤ h * μ * (√h * ‖YL * Cᵀ‖) ∧ ‖D * Cᵀ‖ ≤ 2 * (h * μ) * ‖YL * Cᵀ‖ := by
  obtain ⟨Ξ, hΞP, hΞ⟩ := exists_galerkin_resolvent hdiss hs.hP₁ hs.hP₁t hh.le (1 - h • (P₀ * M))
  obtain ⟨D, hD⟩ : ∃ D, D = Y₁ - Ξ * YL := ⟨_, rfl⟩
  refine ⟨Ξ, D, hΞP, hΞ, by rw [hD]; abel, ?_⟩
  have hPD : P₁ * D = D := by
    rw [hD, Matrix.mul_sub, hs.sP, ← Matrix.mul_assoc, hΞP]
  have hDQ : D * Q₁ = D := by
    rw [hD, Matrix.sub_mul, hs.sQ, Matrix.mul_assoc, hs.lQ]
  -- the equation of the remainder
  have e2 : Ξ * YL = P₁ * (h • (M * (Ξ * YL)) + (YL - h • (P₀ * (M * YL)))) * Q₁ := by
    have e : Ξ * YL = P₁ * (h • (M * (Ξ * YL)) + (YL - h • (P₀ * (M * YL)))) := by
      rw [Matrix.mul_add, Matrix.mul_smul]
      exact (sub_eq_iff_eq_add'.1 (xi_mul_sub hΞ YL))
    have e' : Ξ * YL * Q₁ = Ξ * YL := by rw [Matrix.mul_assoc, hs.lQ]
    rw [← e, e']
  have e3 : Y₀ = YL - h • (P₀ * (M * YL)) + h • (YL * (Cᵀ * C)) := by
    have := hs.lEq
    rw [Matrix.mul_sub, ← Matrix.mul_assoc P₀ YL, hs.lP, smul_sub] at this
    have h' : Y₀ = YL - (h • (P₀ * (M * YL)) - h • (YL * (Cᵀ * C))) :=
      eq_sub_of_add_eq this.symm
    rw [h']; abel
  have eD : D = P₁ * (h • (M * D) - h • ((Y₁ - YL) * (Cᵀ * C))) * Q₁ := by
    have h0 : Y₁ - Ξ * YL = P₁ * (Y₀ + h • (M * Y₁ - Y₁ * (Cᵀ * C))) * Q₁ -
        P₁ * (h • (M * (Ξ * YL)) + (YL - h • (P₀ * (M * YL)))) * Q₁ :=
      congrArg₂ (fun A B => A - B) hs.sEq e2
    refine (hD.trans h0).trans ?_
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    congr 2
    rw [e3, hD]
    simp only [Matrix.mul_sub, Matrix.sub_mul, smul_sub]
    abel
  -- energy estimate
  have hDC : D * Cᵀ = P₁ * (D * Cᵀ) := by rw [← Matrix.mul_assoc, hPD]
  obtain ⟨Da, hDa⟩ : ∃ Da, Da = (Ξ - P₁) * YL := ⟨_, rfl⟩
  have hsplit : P₁ * ((Y₁ - YL) * Cᵀ) = D * Cᵀ + Da * Cᵀ := by
    have : Y₁ - Ξ * YL + (Ξ - P₁) * YL = Y₁ - P₁ * YL := by rw [Matrix.sub_mul]; abel
    rw [← Matrix.mul_assoc, Matrix.mul_sub, hs.sP, ← Matrix.add_mul, hD, hDa, this]
  have h1 : ⟪D, D⟫ = h * ⟪M * D, D⟫ - h * (⟪D * Cᵀ, D * Cᵀ⟫ + ⟪Da * Cᵀ, D * Cᵀ⟫) := by
    have h0 : ⟪D, D⟫ = ⟪P₁ * (h • (M * D) - h • ((Y₁ - YL) * (Cᵀ * C))) * Q₁, D⟫ :=
      congrArg (fun A => ⟪A, D⟫) eD
    rw [h0, inner_mul_proj hs.hQ₁t, inner_proj_mul hs.hP₁t, hDQ, hPD, inner_sub_left,
      real_inner_smul_left, real_inner_smul_left, ← Matrix.mul_assoc (Y₁ - YL),
      Frobenius.inner_mul_right ((Y₁ - YL) * Cᵀ) C D, hDC, ← inner_proj_mul hs.hP₁t, hsplit,
      ← hDC, inner_add_left]
  have hDa1 : P₁ * (Da * Cᵀ) = Da * Cᵀ := by
    rw [hDa, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_sub, hΞP, hs.hP₁]
  have hDa2 : Da * Cᵀ - h • (P₁ * (M * (Da * Cᵀ))) =
      P₁ * (h • (M * (P₁ * (YL * Cᵀ)) - P₀ * (M * (YL * Cᵀ)))) := by
    have e : Da * Cᵀ = Ξ * (YL * Cᵀ) - P₁ * (YL * Cᵀ) := by
      rw [hDa, Matrix.mul_assoc, Matrix.sub_mul]
    rw [e, Matrix.mul_sub, Matrix.mul_sub, smul_sub, sub_sub_sub_comm, xi_mul_sub hΞ]
    simp only [Matrix.mul_smul, Matrix.mul_sub, smul_sub]
    abel
  have ha : ‖Da * Cᵀ‖ ≤ 2 * (h * μ) * ‖YL * Cᵀ‖ := by
    refine (norm_le_of_galerkin hdiss hs.hP₁t hh.le hDa1 hDa2).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hh.le]
    have h2 := norm_sub_le (M * (P₁ * (YL * Cᵀ))) (P₀ * (M * (YL * Cᵀ)))
    have h3 := (norm_mul_le_mul_norm hμ0 hμ (P₁ * (YL * Cᵀ))).trans
      (mul_le_mul_of_nonneg_left (norm_proj_mul_le hs.hP₁ hs.hP₁t (YL * Cᵀ)) hμ0)
    have h4 := (norm_proj_mul_le hs.hP₀ hs.hP₀t (M * (YL * Cᵀ))).trans
      (norm_mul_le_mul_norm hμ0 hμ (YL * Cᵀ))
    calc h * ‖M * (P₁ * (YL * Cᵀ)) - P₀ * (M * (YL * Cᵀ))‖
        ≤ h * (μ * ‖YL * Cᵀ‖ + μ * ‖YL * Cᵀ‖) :=
          mul_le_mul_of_nonneg_left (h2.trans (add_le_add h3 h4)) hh.le
      _ = 2 * (h * μ) * ‖YL * Cᵀ‖ := by ring
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1
  have hin : -(‖Da * Cᵀ‖ * ‖D * Cᵀ‖) ≤ ⟪Da * Cᵀ, D * Cᵀ⟫ :=
    neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  have hMD := inner_mul_self_nonpos hdiss D
  have key : ‖D‖ ^ 2 + h * ‖D * Cᵀ‖ ^ 2 ≤ h * (‖Da * Cᵀ‖ * ‖D * Cᵀ‖) := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hh.le hMD, mul_le_mul_of_nonneg_left hin hh.le]
  have hb : ‖D * Cᵀ‖ ≤ ‖Da * Cᵀ‖ := by
    refine le_of_sq_le_mul (norm_nonneg _) ?_
    have : h * ‖D * Cᵀ‖ ^ 2 ≤ h * (‖Da * Cᵀ‖ * ‖D * Cᵀ‖) := by nlinarith [sq_nonneg ‖D‖]
    exact le_of_mul_le_mul_left this hh
  refine ⟨?_, hb.trans ha⟩
  have hw0 : 0 ≤ ‖YL * Cᵀ‖ := norm_nonneg _
  have hs2 : √h ^ 2 = h := Real.sq_sqrt hh.le
  refine (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg hh.le hμ0) (mul_nonneg (Real.sqrt_nonneg h) hw0)) two_ne_zero).1 ?_
  have f2 : ‖Da * Cᵀ‖ * ‖D * Cᵀ‖ - ‖D * Cᵀ‖ ^ 2 ≤ ‖Da * Cᵀ‖ ^ 2 / 4 := by
    nlinarith [sq_nonneg (‖Da * Cᵀ‖ - 2 * ‖D * Cᵀ‖)]
  have f3 : ‖Da * Cᵀ‖ ^ 2 ≤ (2 * (h * μ) * ‖YL * Cᵀ‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) ha 2
  calc ‖D‖ ^ 2 ≤ h * (‖Da * Cᵀ‖ * ‖D * Cᵀ‖ - ‖D * Cᵀ‖ ^ 2) := by linarith
    _ ≤ h * ((2 * (h * μ) * ‖YL * Cᵀ‖) ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left (f2.trans (by linarith)) hh.le
    _ = (h * μ * (√h * ‖YL * Cᵀ‖)) ^ 2 := by
        rw [mul_pow (h * μ), mul_pow √h, hs2]; ring

/-- **The weighted Lyapunov inequality of one step**, in terms of the projectors. -/
private theorem ProjStep.sq_norm_add_le [DecidableEq n]
    (hs : ProjStep M C h P₀ P₁ Q₀ Q₁ Y₀ YK YL Y₁) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
    (hμ0 : 0 ≤ μ) (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hhμ : h * μ ≤ 1) (hQ : Q * Q = Q) (hQt : Qᵀ = Q) (hCQ : C * Q = 0) :
    ‖Y₁ * (1 - Q)‖ ^ 2 + 2 * (h * ‖YL * Cᵀ‖ ^ 2) ≤ (1 + 5 * (h * μ)) * ‖Y₀ * (1 - Q)‖ ^ 2 := by
  classical
  obtain ⟨Ξ, D, hΞP, hΞ, hY, hDn, -⟩ := hs.exists_sstep_decomposition hdiss hμ0 hμ hh
  have hL := hs.lstep_energy hdiss hh.le hQt hCQ
  have hQc : (1 - Q) * (1 - Q) = 1 - Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hQ]; abel
  have hQct : (1 - Q)ᵀ = 1 - Q := by rw [Matrix.transpose_sub, Matrix.transpose_one, hQt]
  have e : Y₁ * (1 - Q) = Ξ * (YL * (1 - Q)) + D * (1 - Q) := by
    have := congrArg (fun A => A * (1 - Q)) hY
    rwa [Matrix.add_mul, Matrix.mul_assoc] at this
  have h1 := norm_xi_mul_le hdiss hμ0 hμ hh.le hs.hP₀ hs.hP₀t hs.hP₁t hΞP hΞ (YL * (1 - Q))
  have h2 := (norm_mul_proj_le hQc hQct D).trans hDn
  have hs2 : √h ^ 2 = h := Real.sq_sqrt hh.le
  obtain ⟨x, hx⟩ : ∃ x, x = ‖YL * (1 - Q)‖ := ⟨_, rfl⟩
  obtain ⟨e', he'⟩ : ∃ e', e' = √h * ‖YL * Cᵀ‖ := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = h * μ := ⟨_, rfl⟩
  have hee : e' ^ 2 = h * ‖YL * Cᵀ‖ ^ 2 := by rw [he', mul_pow, hs2]
  have ha0 : 0 ≤ a := by rw [ha]; exact mul_nonneg hh.le hμ0
  have hx0 : 0 ≤ x := by rw [hx]; exact norm_nonneg _
  have he0 : 0 ≤ e' := by rw [he']; exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  rw [← hx, ← hee] at hL
  rw [← hx, ← ha] at h1
  rw [← he', ← ha] at h2
  rw [← hee, ← ha]
  rw [← ha] at hhμ
  have hy : ‖Y₁ * (1 - Q)‖ ≤ (1 + a) * x + a * e' := by
    rw [e]; exact (norm_add_le _ _).trans (add_le_add h1 h2)
  have hy2 : ‖Y₁ * (1 - Q)‖ ^ 2 ≤ ((1 + a) * x + a * e') ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hy 2
  have h3 : 2 * x * e' ≤ x ^ 2 + e' ^ 2 := by nlinarith [sq_nonneg (x - e')]
  have h4 : a ^ 2 ≤ a := by nlinarith
  have hy3 : ‖Y₁ * (1 - Q)‖ ^ 2 ≤ (1 + 5 * a) * x ^ 2 + 3 * a * e' ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + a) ha0) (sub_nonneg.2 h3),
      mul_nonneg (sub_nonneg.2 h4) (sq_nonneg x), mul_nonneg (sub_nonneg.2 h4) (sq_nonneg e')]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + 5 * a) (sub_nonneg.2 hL),
    mul_nonneg ha0 (sq_nonneg e')]

/-- **The stiff energy after one step** is bounded by the stiff energy of the L-step result. -/
private theorem ProjStep.norm_mul_transpose_le
    (hs : ProjStep M C h P₀ P₁ Q₀ Q₁ Y₀ YK YL Y₁) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
    (hμ0 : 0 ≤ μ) (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hhμ : h * μ ≤ 1) : ‖Y₁ * Cᵀ‖ ≤ 4 * ‖YL * Cᵀ‖ := by
  classical
  obtain ⟨Ξ, D, hΞP, hΞ, hY, -, hDC⟩ := hs.exists_sstep_decomposition hdiss hμ0 hμ hh
  have e : Y₁ * Cᵀ = Ξ * (YL * Cᵀ) + D * Cᵀ := by
    have := congrArg (fun A => A * Cᵀ) hY
    rwa [Matrix.add_mul, Matrix.mul_assoc] at this
  have h1 := norm_xi_mul_le hdiss hμ0 hμ hh.le hs.hP₀ hs.hP₀t hs.hP₁t hΞP hΞ (YL * Cᵀ)
  rw [e]
  refine (norm_add_le _ _).trans ?_
  nlinarith [norm_nonneg (YL * Cᵀ), mul_nonneg hh.le hμ0]

/-- Moving a Gram matrix `CᵀC` and a row projector through the Frobenius inner product. -/
private theorem inner_mul_gram_proj (hQ₀t : Q₀ᵀ = Q₀) {A : Matrix m n ℝ} (hA : A * Q₀ = A)
    (B : Matrix m n ℝ) : ⟪A, B * (Cᵀ * C) * Q₀⟫ = ⟪A * Cᵀ, B * Cᵀ⟫ := by
  rw [Frobenius.inner_mul_right', hQ₀t, hA, ← Matrix.mul_assoc, Frobenius.inner_mul_right']

/-- **The K-step.** The stiff term `Λ = h Y_K CᵀC Q₀` of the K-step is bounded by the start value
and by the square root of its stiff energy. -/
private theorem ProjStep.exists_kstep_term (hs : ProjStep M C h P₀ P₁ Q₀ Q₁ Y₀ YK YL Y₁)
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 < h) :
    ∃ Λ : Matrix m n ℝ, YK + Λ - h • (M * YK) = Y₀ ∧ P₁ * Λ = Λ ∧ ‖Λ‖ ≤ ‖Y₀‖ ∧
      2 * ‖Λ‖ ≤ √h * ‖Y₀ * Cᵀ‖ := by
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = h • (YK * (Cᵀ * C) * Q₀) := ⟨_, rfl⟩
  have eqK : YK + Λ - h • (M * YK) = Y₀ := by
    have := hs.kEq
    rw [Matrix.sub_mul, Matrix.mul_assoc M, hs.kQ, smul_sub, ← hΛ] at this
    calc YK + Λ - h • (M * YK) = Y₀ + (h • (M * YK) - Λ) + Λ - h • (M * YK) := by rw [← this]
      _ = Y₀ := by abel
  have hPΛ : P₁ * Λ = Λ := by
    rw [hΛ, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hs.kP]
  have hI : ⟪YK, Λ⟫ + ⟪Λ, Λ⟫ - h * ⟪M * YK, Λ⟫ = ⟪Y₀, Λ⟫ := by
    have := congrArg (fun A => ⟪A, Λ⟫) eqK
    rwa [inner_sub_left, inner_add_left, real_inner_smul_left] at this
  have hYK : ⟪YK, Λ⟫ = h * ‖YK * Cᵀ‖ ^ 2 := by
    rw [hΛ, real_inner_smul_right, inner_mul_gram_proj hs.hQ₀t hs.kQ, real_inner_self_eq_norm_sq]
  have hMK : ⟪M * YK, Λ⟫ = h * ⟪M * (YK * Cᵀ), YK * Cᵀ⟫ := by
    rw [hΛ, real_inner_smul_right,
      inner_mul_gram_proj hs.hQ₀t (A := M * YK) (by rw [Matrix.mul_assoc, hs.kQ]),
      Matrix.mul_assoc]
  have hY0 : ⟪Y₀, Λ⟫ = h * ⟪Y₀ * Cᵀ, YK * Cᵀ⟫ := by
    rw [hΛ, real_inner_smul_right, inner_mul_gram_proj hs.hQ₀t hs.yQ]
  have hi := inner_mul_self_nonpos hdiss (YK * Cᵀ)
  have hq := real_inner_le_norm (Y₀ * Cᵀ) (YK * Cᵀ)
  have hl := real_inner_le_norm Y₀ Λ
  rw [real_inner_self_eq_norm_sq] at hI
  have hhh : 0 ≤ -(h * (h * ⟪M * (YK * Cᵀ), YK * Cᵀ⟫)) := by
    have := mul_nonpos_of_nonneg_of_nonpos hh.le (mul_nonpos_of_nonneg_of_nonpos hh.le hi)
    linarith
  refine ⟨Λ, eqK, hPΛ, ?_, ?_⟩
  · refine le_of_sq_le_mul (norm_nonneg _) ?_
    nlinarith [mul_nonneg hh.le (sq_nonneg ‖YK * Cᵀ‖)]
  · have hs2 : √h ^ 2 = h := Real.sq_sqrt hh.le
    refine (pow_le_pow_iff_left₀ (mul_nonneg zero_le_two (norm_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg h) (norm_nonneg _)) two_ne_zero).1 ?_
    rw [mul_pow √h, hs2]
    have f1 : ‖Λ‖ ^ 2 ≤ h * (‖Y₀ * Cᵀ‖ * ‖YK * Cᵀ‖ - ‖YK * Cᵀ‖ ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hq hh.le]
    have f2 : ‖Y₀ * Cᵀ‖ * ‖YK * Cᵀ‖ - ‖YK * Cᵀ‖ ^ 2 ≤ ‖Y₀ * Cᵀ‖ ^ 2 / 4 := by
      nlinarith [sq_nonneg (‖Y₀ * Cᵀ‖ - 2 * ‖YK * Cᵀ‖)]
    nlinarith [mul_le_mul_of_nonneg_left f2 hh.le]

/-- **The part on the reference row space after one step**, against a backward Euler step of the
reference. -/
private theorem ProjStep.norm_mul_sub_le
    (hs : ProjStep M C h P₀ P₁ Q₀ Q₁ Y₀ YK YL Y₁) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
    (hμ0 : 0 ≤ μ) (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hQ : Q * Q = Q) (hQt : Qᵀ = Q) (hCQ : C * Q = 0) {X₀ X₁ : Matrix m n ℝ}
    (hX : X₁ - h • (M * X₁) = X₀) :
    ‖Y₁ * Q - X₁‖ ≤ ‖Y₀ * Q - X₀‖ + h * μ * min (2 * ‖Y₀‖) (√h * ‖Y₀ * Cᵀ‖) +
      h * μ * (√h * ‖YL * Cᵀ‖) := by
  classical
  obtain ⟨Ξ, D, hΞP, hΞ, hY, hDn, -⟩ := hs.exists_sstep_decomposition hdiss hμ0 hμ hh
  obtain ⟨Λ, eqK, hPΛ, hΛ1, hΛ2⟩ := hs.exists_kstep_term hdiss hh
  have hCCQ : Cᵀ * C * Q = 0 := by rw [Matrix.mul_assoc, hCQ, Matrix.mul_zero]
  have hYLQ : YL * Q - h • (P₀ * (M * (YL * Q))) = Y₀ * Q := by
    have := congrArg (fun A => A * Q) hs.lEq
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc P₀, Matrix.sub_mul, Matrix.mul_assoc M,
      Matrix.mul_assoc YL, hCCQ, Matrix.mul_zero, sub_zero] at this
    exact sub_eq_of_eq_add this
  obtain ⟨gt, hgtdef⟩ : ∃ gt, gt = Ξ * (YL * Q) := ⟨_, rfl⟩
  have hgt : gt - h • (P₁ * (M * gt)) = P₁ * (Y₀ * Q) := by
    rw [hgtdef, xi_mul_sub hΞ, hYLQ]
  have hPgt : P₁ * gt = gt := by rw [hgtdef, ← Matrix.mul_assoc, hΞP]
  obtain ⟨k', hk⟩ : ∃ k', k' = (YK + Λ) * Q := ⟨_, rfl⟩
  have hPk : P₁ * k' = k' := by
    rw [hk, ← Matrix.mul_assoc, Matrix.mul_add, hs.kP, hPΛ]
  have e1 : YK + Λ = Y₀ + h • (M * YK) := eq_add_of_sub_eq eqK
  have hk1 : k' - h • (M * k') = Y₀ * Q - h • (M * (Λ * Q)) := by
    have ek : k' = (Y₀ + h • (M * YK)) * Q := by rw [hk, e1]
    have ek2 : M * k' = M * (YK * Q) + M * (Λ * Q) := by
      rw [hk, Matrix.add_mul, Matrix.mul_add]
    rw [ek2, ek, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, smul_add]
    abel
  have hk2 : k' - h • (P₁ * (M * k')) = P₁ * (Y₀ * Q - h • (M * (Λ * Q))) := by
    rw [← hk1, Matrix.mul_sub, Matrix.mul_smul, hPk]
  have hd1 : ‖gt - k'‖ ≤ h * μ * ‖Λ‖ := by
    have hP : P₁ * (gt - k') = gt - k' := by rw [Matrix.mul_sub, hPgt, hPk]
    have heq : gt - k' - h • (P₁ * (M * (gt - k'))) = P₁ * (h • (M * (Λ * Q))) := by
      rw [Matrix.mul_sub, Matrix.mul_sub, smul_sub, sub_sub_sub_comm, hgt, hk2, ← Matrix.mul_sub]
      congr 1; abel
    refine (norm_le_of_galerkin hdiss hs.hP₁t hh.le hP heq).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hh.le, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((norm_mul_le_mul_norm hμ0 hμ _).trans
      (mul_le_mul_of_nonneg_left (norm_mul_proj_le hQ hQt Λ) hμ0)) hh.le
  have hd2 : ‖k' - X₁‖ ≤ ‖Y₀ * Q - X₀‖ + h * μ * ‖Λ‖ := by
    have heq : k' - X₁ - h • ((1 : Matrix m m ℝ) * (M * (k' - X₁))) =
        (1 : Matrix m m ℝ) * (Y₀ * Q - X₀ - h • (M * (Λ * Q))) := by
      rw [Matrix.one_mul, Matrix.one_mul, Matrix.mul_sub, smul_sub, sub_sub_sub_comm, hk1, hX]
      abel
    refine (norm_le_of_galerkin hdiss Matrix.transpose_one hh.le (Matrix.one_mul _) heq).trans ?_
    refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_smul, Real.norm_of_nonneg hh.le, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((norm_mul_le_mul_norm hμ0 hμ _).trans
      (mul_le_mul_of_nonneg_left (norm_mul_proj_le hQ hQt Λ) hμ0)) hh.le
  have e : Y₁ * Q - X₁ = gt - k' + (k' - X₁) + D * Q := by
    have := congrArg (fun A => A * Q) hY
    rw [Matrix.add_mul, Matrix.mul_assoc, ← hgtdef] at this
    rw [this]; abel
  have hDQ := (norm_mul_proj_le hQ hQt D).trans hDn
  have hmin : 2 * ‖Λ‖ ≤ min (2 * ‖Y₀‖) (√h * ‖Y₀ * Cᵀ‖) :=
    le_min (by linarith) hΛ2
  have hm := mul_le_mul_of_nonneg_left hmin (mul_nonneg hh.le hμ0)
  rw [e]
  refine (norm_add₃_le).trans ?_
  linarith

end Lemmas

section Conversion

variable {m n k k₁ k₂ : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k₁] [Fintype k₂]
  [DecidableEq m] [DecidableEq n] [DecidableEq k₁] [DecidableEq k₂] {r : ℕ}
  {M : Matrix m m ℝ} {C : Matrix k n ℝ} {Q : Matrix n n ℝ} {ε t₁ h μ : ℝ}
  {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {K₁ : Matrix m (Fin r) ℝ} {L₁ : Matrix n (Fin r) ℝ} {U₁ : Matrix m k₁ ℝ} {V₁ : Matrix n k₂ ℝ}
  {S₁ : Matrix k₁ k₂ ℝ} {Y₁ : Matrix m n ℝ}

/-- A step of the matrix integrator with exact capture and without truncation, for
`F(Z) = M Z - Z CᵀC`, in terms of the projectors. -/
private theorem projStep_of_isMatrixImplicitBUGStep
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) ε 0 0
      t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) :
    ProjStep M C h (U₀ * U₀ᵀ) (U₁ * U₁ᵀ) (V₀ * V₀ᵀ) (V₁ * V₁ᵀ) (U₀ * S₀ * V₀ᵀ) (K₁ * V₀ᵀ)
      (U₀ * L₁ᵀ) (U₁ * S₁ * V₁ᵀ) where
  hP₀ := by simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthU₀]
  hP₀t := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  hP₁ := by simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthU₁]
  hP₁t := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  hQ₀t := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  hQ₁t := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  kEq := by
    have := congrArg (fun A => A * V₀ᵀ) hs.kstep
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc] at this
    simpa only [Matrix.mul_assoc] using this
  kQ := by simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthV₀]
  kP := by
    have := norm_le_zero_iff.1 hs.kcap
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
    exact this.symm
  yQ := by simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthV₀]
  lEq := by
    have := congrArg (fun A => U₀ * Aᵀ) hs.lstep
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc] at this
    simpa only [Matrix.mul_assoc] using this
  lP := by simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthU₀]
  lQ := by
    have := norm_le_zero_iff.1 hs.lcap
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  sEq := by
    have := congrArg (fun A => U₁ * A * V₁ᵀ) hs.sstep
    simp only [Matrix.mul_assoc] at this
    simpa only [Matrix.mul_assoc] using this
  sP := by simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthU₁]
  sQ := by simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthV₁]

end Conversion

end ImplicitBUGWeightedRows

open ImplicitBUGWeightedRows

section Step

variable {m n k k₁ k₂ : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k₁] [Fintype k₂]
  [DecidableEq m] [DecidableEq n] [DecidableEq k₁] [DecidableEq k₂] {r : ℕ}
  {M : Matrix m m ℝ} {C : Matrix k n ℝ} {Q : Matrix n n ℝ} {ε t₁ h μ : ℝ}
  {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {K₁ : Matrix m (Fin r) ℝ} {L₁ : Matrix n (Fin r) ℝ} {U₁ : Matrix m k₁ ℝ} {V₁ : Matrix n k₂ ℝ}
  {S₁ : Matrix k₁ k₂ ℝ} {Y₁ : Matrix m n ℝ}

/-- **The weighted Lyapunov inequality of one step in the kernel class.** Let
`F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ`, `h μ ≤ 1`, and let `Q` be an
orthogonal projector with `C Q = 0` (onto row vectors in the kernel of the stiff matrix). For a
step with exact capture and without truncation, of any rank,

  `‖Y₁ (1 - Q)‖² + 2 h ‖U₀ L₁ᵀ Cᵀ‖² ≤ (1 + 5 h μ) ‖Y₀ (1 - Q)‖²`:

the part of the numerical solution outside the range of `Q` (the row angles weighted by the
singular values) decreases up to the factor `1 + 5 h μ`, and its decrease pays the stiff energy
`h ‖U₀ L₁ᵀ Cᵀ‖²` of the L-step result. Neither `C` nor the singular values of `S₀` enter. -/
theorem IsMatrixImplicitBUGStep.sq_norm_mul_compl_add_le_of_sylvester
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) ε 0 0
      t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h) (hhμ : h * μ ≤ 1)
    (hQ : Q * Q = Q) (hQt : Qᵀ = Q) (hCQ : C * Q = 0) :
    ‖Y₁ * (1 - Q)‖ ^ 2 + 2 * (h * ‖U₀ * L₁ᵀ * Cᵀ‖ ^ 2) ≤
      (1 + 5 * (h * μ)) * ‖U₀ * S₀ * V₀ᵀ * (1 - Q)‖ ^ 2 := by
  rw [sub_eq_zero.1 (norm_le_zero_iff.1 hs.trunc)]
  exact (projStep_of_isMatrixImplicitBUGStep hs).sq_norm_add_le hdiss hμ0 hμ hh hhμ hQ hQt hCQ

/-- **The stiff energy after one step.** For `F(Z) = M Z - Z CᵀC` with `M` dissipative and
bounded by `μ` and `h μ ≤ 1`, the result of a step satisfies `‖Y₁ Cᵀ‖ ≤ 4 ‖U₀ L₁ᵀ Cᵀ‖`. No
kernel condition is needed. -/
theorem IsMatrixImplicitBUGStep.norm_mul_transpose_le_of_sylvester
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) ε 0 0
      t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h) (hhμ : h * μ ≤ 1) :
    ‖Y₁ * Cᵀ‖ ≤ 4 * ‖U₀ * L₁ᵀ * Cᵀ‖ := by
  rw [sub_eq_zero.1 (norm_le_zero_iff.1 hs.trunc)]
  exact (projStep_of_isMatrixImplicitBUGStep hs).norm_mul_transpose_le hdiss hμ0 hμ hh hhμ

/-- **The part on the reference row space after one step.** In the setting of
`IsMatrixImplicitBUGStep.sq_norm_mul_compl_add_le_of_sylvester`, let `X₁ - h M X₁ = X₀` (a backward
Euler step of a reference with rows in the range of `Q`). Then

  `‖Y₁ Q - X₁‖ ≤ ‖Y₀ Q - X₀‖ + h μ min(2 ‖Y₀‖, √h ‖Y₀ Cᵀ‖) + h μ √h ‖U₀ L₁ᵀ Cᵀ‖`.

The old error enters with the factor `1`; the loss is `h μ` times the square roots of the stiff
energies of the start value (K-step) and of the L-step result (S-step), and at most `2 h μ ‖Y₀‖`
from the start value whatever its stiff energy. -/
theorem IsMatrixImplicitBUGStep.norm_mul_sub_le_of_sylvester
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) ε 0 0
      t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hQ : Q * Q = Q) (hQt : Qᵀ = Q) (hCQ : C * Q = 0) {X₀ X₁ : Matrix m n ℝ}
    (hX : X₁ - h • (M * X₁) = X₀) :
    ‖Y₁ * Q - X₁‖ ≤ ‖U₀ * S₀ * V₀ᵀ * Q - X₀‖ +
      h * μ * min (2 * ‖U₀ * S₀ * V₀ᵀ‖) (√h * ‖U₀ * S₀ * V₀ᵀ * Cᵀ‖) +
      h * μ * (√h * ‖U₀ * L₁ᵀ * Cᵀ‖) := by
  rw [sub_eq_zero.1 (norm_le_zero_iff.1 hs.trunc)]
  exact (projStep_of_isMatrixImplicitBUGStep hs).norm_mul_sub_le hdiss hμ0 hμ hh hQ hQt hCQ hX

end Step

section Run

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n]
  {r N : ℕ} {M : Matrix m m ℝ} {C : Matrix k n ℝ} {Q : Matrix n n ℝ} {h μ : ℝ} {ε t : ℕ → ℝ}
  {U K : ℕ → Matrix m (Fin r) ℝ} {L V : ℕ → Matrix n (Fin r) ℝ}
  {S : ℕ → Matrix (Fin r) (Fin r) ℝ} {Y : ℕ → Matrix m n ℝ}

/-- **The weighted Lyapunov inequality along a run in the kernel class.** For `N` steps of the
rank-`r` integrator with backward Euler substeps (exact capture, no truncation) for
`F(Z) = M Z - Z CᵀC`, with `M` dissipative and bounded by `μ`, `h μ ≤ 1`, and an orthogonal
projector `Q` with `C Q = 0`,

  `‖Y_N (1 - Q)‖² + 2 ∑_{j < N} h ‖U_j L_jᵀ Cᵀ‖² ≤ (1 + 5 h μ)^N ‖Y₀ (1 - Q)‖²`,

where `Y_j = U_j S_j V_jᵀ` and `L_j` is the result of the L-step of step `j`. The sum of the stiff
energies over the whole run is bounded by the start value, uniformly in `C` and in the singular
values. -/
theorem sq_norm_implicitBUG_run_mul_compl_add_le_of_sylvester
    (hstep : ∀ j < N, IsMatrixImplicitBUGStep
      (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) (ε j) 0 0 (t j) h (U j) (S j) (V j)
      (K j) (L j) (U (j + 1)) (V (j + 1)) (S (j + 1)) (Y j))
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h) (hhμ : h * μ ≤ 1)
    (hQ : Q * Q = Q) (hQt : Qᵀ = Q) (hCQ : C * Q = 0) :
    ‖U N * S N * (V N)ᵀ * (1 - Q)‖ ^ 2 +
        2 * ∑ j ∈ Finset.range N, h * ‖U j * (L j)ᵀ * Cᵀ‖ ^ 2 ≤
      (1 + 5 * (h * μ)) ^ N * ‖U 0 * S 0 * (V 0)ᵀ * (1 - Q)‖ ^ 2 := by
  have ha0 : 0 ≤ h * μ := mul_nonneg hh.le hμ0
  have key : ∀ n, n ≤ N → ‖U n * S n * (V n)ᵀ * (1 - Q)‖ ^ 2 +
      2 * ∑ j ∈ Finset.range n, h * ‖U j * (L j)ᵀ * Cᵀ‖ ^ 2 ≤
      (1 + 5 * (h * μ)) ^ n * ‖U 0 * S 0 * (V 0)ᵀ * (1 - Q)‖ ^ 2 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have ih' := ih (Nat.le_of_succ_le hn)
      have hs := hstep n (Nat.lt_of_succ_le hn)
      have h1 := hs.sq_norm_mul_compl_add_le_of_sylvester hdiss hμ0 hμ hh hhμ hQ hQt hCQ
      rw [sub_eq_zero.1 (norm_le_zero_iff.1 hs.trunc)] at h1
      have hsum : 0 ≤ ∑ j ∈ Finset.range n, h * ‖U j * (L j)ᵀ * Cᵀ‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => mul_nonneg hh.le (sq_nonneg _)
      rw [Finset.sum_range_succ, pow_succ (1 + 5 * (h * μ)) n]
      nlinarith [h1, mul_le_mul_of_nonneg_left ih' (by linarith : (0 : ℝ) ≤ 1 + 5 * (h * μ)),
        mul_nonneg ha0 hsum]
  exact key N le_rfl

/-- **Run bound in the kernel class, uniform in the stiffness and in the singular values.** Let
`F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ`, `h μ ≤ 1`, let `Q` be an orthogonal
projector with `C Q = 0`, and let `X_j` be backward Euler steps `X_{j+1} - h M X_{j+1} = X_j` of a
reference. For `N` steps of the rank-`r` integrator with backward Euler substeps (exact capture,
no truncation), `Y_j = U_j S_j V_jᵀ`,

  `‖Y_N - X_N‖ ≤ ‖Y₀ Q - X₀‖ + 2 h μ ‖Y₀‖ + (1 + 4 h μ √N) √((1 + 5 h μ)^N) ‖Y₀ (1 - Q)‖`.

The matrix `C` (the stiffness) does not enter, and neither do the singular values of the `S_j`.
The term `2 h μ ‖Y₀‖` is the loss of the first step; all later losses are paid by the decrease of
`‖Y_j (1 - Q)‖²` (`sq_norm_implicitBUG_run_mul_compl_add_le_of_sylvester`). -/
theorem norm_implicitBUG_run_sub_le_of_sylvester {X : ℕ → Matrix m n ℝ}
    (hstep : ∀ j < N, IsMatrixImplicitBUGStep
      (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) (ε j) 0 0 (t j) h (U j) (S j) (V j)
      (K j) (L j) (U (j + 1)) (V (j + 1)) (S (j + 1)) (Y j))
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h) (hhμ : h * μ ≤ 1)
    (hQ : Q * Q = Q) (hQt : Qᵀ = Q) (hCQ : C * Q = 0)
    (hX : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) = X j) :
    ‖U N * S N * (V N)ᵀ - X N‖ ≤ ‖U 0 * S 0 * (V 0)ᵀ * Q - X 0‖ +
      2 * (h * μ) * ‖U 0 * S 0 * (V 0)ᵀ‖ +
      (1 + 4 * (h * μ) * √N) * √((1 + 5 * (h * μ)) ^ N) * ‖U 0 * S 0 * (V 0)ᵀ * (1 - Q)‖ := by
  obtain ⟨a, ha⟩ : ∃ a, a = h * μ := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; exact mul_nonneg hh.le hμ0
  have hs2 : √h ^ 2 = h := Real.sq_sqrt hh.le
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ, e = fun j => √h * ‖U j * (L j)ᵀ * Cᵀ‖ := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ, w = fun j => ‖U j * S j * (V j)ᵀ * Q - X j‖ := ⟨_, rfl⟩
  have he0 : ∀ j, 0 ≤ e j := fun j => by
    rw [he]; exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hYeq : ∀ j < N, Y j = U (j + 1) * S (j + 1) * (V (j + 1))ᵀ := fun j hj =>
    sub_eq_zero.1 (norm_le_zero_iff.1 (hstep j hj).trunc)
  -- the stiff energy of the start value of step `j + 1`
  have hB : ∀ j < N, √h * ‖U (j + 1) * S (j + 1) * (V (j + 1))ᵀ * Cᵀ‖ ≤ 4 * e j := by
    intro j hj
    have := (hstep j hj).norm_mul_transpose_le_of_sylvester hdiss hμ0 hμ hh hhμ
    rw [hYeq j hj] at this
    have := mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg h)
    rw [he]; linarith
  -- one step for the part on the range of `Q`
  have hC : ∀ j < N, w (j + 1) ≤ w j +
      a * min (2 * ‖U j * S j * (V j)ᵀ‖) (√h * ‖U j * S j * (V j)ᵀ * Cᵀ‖) + a * e j := by
    intro j hj
    have := (hstep j hj).norm_mul_sub_le_of_sylvester hdiss hμ0 hμ hh hQ hQt hCQ (hX j hj)
    rw [hYeq j hj, ← ha] at this
    rw [hw, he]; exact this
  have hI : ∀ n, n + 1 ≤ N → w (n + 1) + 4 * a * e n ≤
      w 0 + 2 * a * ‖U 0 * S 0 * (V 0)ᵀ‖ + 5 * a * ∑ j ∈ Finset.range (n + 1), e j := by
    intro n
    induction n with
    | zero =>
      intro hn
      have h1 := hC 0 hn
      have h2 := mul_le_mul_of_nonneg_left
        (min_le_left (2 * ‖U 0 * S 0 * (V 0)ᵀ‖) (√h * ‖U 0 * S 0 * (V 0)ᵀ * Cᵀ‖)) ha0
      rw [Finset.sum_range_one]
      linarith
    | succ n ih =>
      intro hn
      have ih' := ih (Nat.le_of_succ_le hn)
      have h1 := hC (n + 1) hn
      have h2 := mul_le_mul_of_nonneg_left (min_le_right
        (2 * ‖U (n + 1) * S (n + 1) * (V (n + 1))ᵀ‖)
        (√h * ‖U (n + 1) * S (n + 1) * (V (n + 1))ᵀ * Cᵀ‖)) ha0
      have h3 := mul_le_mul_of_nonneg_left (hB n (Nat.lt_of_succ_le (Nat.le_of_succ_le hn))) ha0
      rw [Finset.sum_range_succ]
      linarith
  have hW : w N ≤ w 0 + 2 * a * ‖U 0 * S 0 * (V 0)ᵀ‖ + 5 * a * ∑ j ∈ Finset.range N, e j := by
    cases N with
    | zero =>
      have : 0 ≤ 2 * a * ‖U 0 * S 0 * (V 0)ᵀ‖ :=
        mul_nonneg (mul_nonneg zero_le_two ha0) (norm_nonneg _)
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
      linarith
    | succ n =>
      have := hI n le_rfl
      have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) ha0) (he0 n)
      linarith
  -- the Lyapunov inequality along the run
  have hLy := sq_norm_implicitBUG_run_mul_compl_add_le_of_sylvester hstep hdiss hμ0 hμ hh hhμ hQ
    hQt hCQ
  have hee : ∀ j, h * ‖U j * (L j)ᵀ * Cᵀ‖ ^ 2 = e j ^ 2 := fun j => by
    rw [he]; simp only [mul_pow, hs2]
  simp only [hee] at hLy
  rw [← ha] at hLy ⊢
  obtain ⟨z, hz⟩ : ∃ z, z = ‖U N * S N * (V N)ᵀ * (1 - Q)‖ := ⟨_, rfl⟩
  obtain ⟨z0, hz0⟩ : ∃ z0, z0 = ‖U 0 * S 0 * (V 0)ᵀ * (1 - Q)‖ := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = ∑ j ∈ Finset.range N, e j := ⟨_, rfl⟩
  obtain ⟨q₂, hq2⟩ : ∃ q₂, q₂ = ∑ j ∈ Finset.range N, e j ^ 2 := ⟨_, rfl⟩
  rw [← hz, ← hz0, ← hq2] at hLy
  rw [← hσ] at hW
  rw [← hz0]
  have hz00 : 0 ≤ z0 := by rw [hz0]; exact norm_nonneg _
  have hzn : 0 ≤ z := by rw [hz]; exact norm_nonneg _
  have hσ0 : 0 ≤ σ := by rw [hσ]; exact Finset.sum_nonneg fun j _ => he0 j
  have hq0 : 0 ≤ q₂ := by rw [hq2]; exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hcs : σ ^ 2 ≤ N * q₂ := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range N) (f := e)
    rwa [Finset.card_range, ← hσ, ← hq2] at this
  obtain ⟨G, hG⟩ : ∃ G, G = (1 + 5 * a) ^ N := ⟨_, rfl⟩
  rw [← hG] at hLy ⊢
  have hG0 : 0 ≤ G := by rw [hG]; exact pow_nonneg (by linarith) _
  have hg2 : √G ^ 2 = G := Real.sq_sqrt hG0
  have hn2 : √(N : ℝ) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
  have hg0 := Real.sqrt_nonneg G
  have hn0 := Real.sqrt_nonneg (N : ℝ)
  have hzle : z ≤ √G * z0 := by
    refine (pow_le_pow_iff_left₀ hzn (mul_nonneg hg0 hz00) two_ne_zero).1 ?_
    rw [mul_pow, hg2]; nlinarith
  have hσle : 5 * σ ≤ 4 * √(N : ℝ) * √G * z0 := by
    refine (pow_le_pow_iff_left₀ (mul_nonneg (by norm_num) hσ0)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hn0) hg0) hz00) two_ne_zero).1 ?_
    rw [mul_pow, mul_pow, mul_pow, mul_pow, hg2, hn2]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h5 : (N : ℝ) * (2 * q₂) ≤ N * (G * z0 ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg z]) hN0
    nlinarith
  have hsplit : U N * S N * (V N)ᵀ - X N =
      (U N * S N * (V N)ᵀ * Q - X N) + U N * S N * (V N)ᵀ * (1 - Q) := by
    rw [Matrix.mul_sub, Matrix.mul_one]; abel
  have hfin : ‖U N * S N * (V N)ᵀ - X N‖ ≤ w N + z := by
    rw [hsplit, hw, hz]; exact norm_add_le _ _
  have hw0 : w 0 = ‖U 0 * S 0 * (V 0)ᵀ * Q - X 0‖ := by rw [hw]
  rw [← hw0]
  have h6 := mul_le_mul_of_nonneg_left hσle ha0
  nlinarith

end Run

/-! ### Non-vacuity -/

section Example

/-- The projector onto the first coordinate (the kernel of the stiff row matrix). -/
local notation "Qₑ" => (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)

/-- The factor `(0, √lam)` of the stiff row matrix `diag(0, -lam) = -CᵀC`. -/
local notation "Cₑ" lam => (!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)

/-- The start column basis `(3/5, 4/5)ᵀ`. -/
local notation "uₑ" => (!![3 / 5; 4 / 5] : Matrix (Fin 2) (Fin 1) ℝ)

/-- The hypotheses hold for a family of `2 × 2` steps of rank `1` with an arbitrary stiffness
`lam ≥ 0`: `M = diag(0, -1)`, `C = (0, √lam)` (so `-CᵀC = diag(0, -lam)`), `Q = diag(1, 0)`,
`μ = 1`, start value `(3/5, 4/5)ᵀ (c, s)`; a step exists for every `h ∈ (0, 1]`. -/
example {h lam c s : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hlam : 0 ≤ lam) (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ (L₁ : Matrix (Fin 2) (Fin 1) ℝ) (Y₁ : Matrix (Fin 2) (Fin 2) ℝ),
      ‖Y₁ * (1 - Qₑ)‖ ^ 2 + 2 * (h * ‖uₑ * L₁ᵀ * (Cₑ lam)ᵀ‖ ^ 2) ≤
        (1 + 5 * (h * 1)) *
          ‖uₑ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (!![c; s] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ *
            (1 - Qₑ)‖ ^ 2 := by
  obtain ⟨K₁, L₁, U₁, V₁, S₁, Y₁, ε, hs⟩ :=
    StiffRowsExample.exists_isMatrixImplicitBUGStep hh.le hlam hcs 0
  have hC : (!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * !![0, √lam] = -!![0, 0; 0, -lam] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Real.mul_self_sqrt hlam]
  have hF : (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
      !![0, 0; 0, -1] * Z + Z * !![0, 0; 0, -lam]) = fun _ Z =>
      !![0, 0; 0, -1] * Z - Z * ((!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * !![0, √lam]) := by
    funext _ Z
    rw [hC, Matrix.mul_neg, sub_neg_eq_add]
  rw [hF] at hs
  have hdiss : ∀ x : Fin 2 → ℝ, x ⬝ᵥ (!![0, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x ≤ 0 := by
    intro x
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    nlinarith [mul_self_nonneg (x 1)]
  have hμ : ∀ x : Fin 2 → ℝ, (!![0, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x ⬝ᵥ
      (!![0, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x ≤ 1 ^ 2 * (x ⬝ᵥ x) := by
    intro x
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    nlinarith [mul_self_nonneg (x 0)]
  have hQ : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 0; 0, 0] = !![1, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  have hQt : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = !![1, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  have hCQ : (Cₑ lam) * Qₑ = 0 := by
    ext i j
    fin_cases i
    fin_cases j <;> simp [Matrix.mul_apply]
  exact ⟨L₁, Y₁, hs.sq_norm_mul_compl_add_le_of_sylvester hdiss zero_le_one hμ hh
    (by simpa using hh1) hQ hQt hCQ⟩

end Example

end LeanDLRA
