import LeanDLRA.Research.ImplicitBUGStiffRows

/-!
# The implicit BUG integrator with a stiff row operator: the step lemmas

Let `F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ` and `C` arbitrary (the matrix
`-CᵀC` acting on the rows is the stiffness). This file collects the lemmas of the energy analysis
of one step of the BUG integrator with backward Euler substeps, in terms of the orthogonal
projectors `P₀ = U₀ U₀ᵀ`, `P₁ = U₁ U₁ᵀ`, `Q₀`, `Q₁` onto the old and new column and row spaces
and the matrices `Y_K = K₁ V₀ᵀ`, `Y_L = U₀ L₁ᵀ`, `Y₁ = U₁ S₁ V₁ᵀ`, for bases of any size with
`P₁ Y_K = Y_K` and `Y_L Q₁ = Y_L` (the fixed-rank bases and the augmented ones).

## Main results

* `ImplicitBUGStiffLemmas.exists_kstep_gram_term`: the stiff term `Λ = h Y_K CᵀC Q₀` of the K-step
  satisfies `‖Λ‖ ≤ √h ‖(Y₀ - Z) Cᵀ‖ / 2 + h ‖Z CᵀC‖` for every matrix `Z`.
* `ImplicitBUGStiffLemmas.exists_sstep_decomposition`: the S-step result is the Galerkin resolvent
  of the new column space applied to the L-step result, up to a remainder bounded in the norm
  and in the stiff energy.
* `ImplicitBUGStiffLemmas.sqrt_sq_norm_sub_add_le_of_projectors`: the step inequality against a
  backward Euler step of the full problem with a defect, in terms of the projectors.
* `IsMatrixImplicitBUGStep.sqrt_sq_norm_galerkin_sub_add_le_of_sylvester`: the same for a step of
  the matrix integrator, for the result `U₁ S₁ V₁ᵀ` of the Galerkin step before truncation.

## Implementation notes

With the Galerkin resolvent `Ξ` of the new column space, `Ξ - h P₁ M Ξ = P₁ (1 - h P₀ M)`, and
`D = Y₁ - Ξ Y_L`, the residual of the step in the backward Euler equation of the full problem is

  `Y₁ - h M Y₁ + h Y₁ CᵀC - Y₀ = D - h P₁ M D + h (1 - P₁) M (Y_K - Y₁) + h D CᵀC`
  `    + h (Ξ - P₁) Y_L CᵀC`,

and the error equation is tested with the error. The comparison matrix `Z` in the bound of the
stiff term of the K-step is free; a run with truncation by a projector `T` acting from the left
uses `Z = T X₀`.

## References

* [CerutiLubich2022] for the BUG integrator; backward Euler substeps as in arXiv 2610.18419.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius
open Matrix

namespace LeanDLRA

namespace ImplicitBUGStiffLemmas

/-- A matrix with orthonormal columns is cancelled by its transpose from the left. -/
theorem orth_mul_cancel {m k p : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) (X : Matrix k p ℝ) : Uᵀ * (U * X) = X := by
  rw [← Matrix.mul_assoc, hU, Matrix.one_mul]

section Lemmas

variable {m n k p : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype p]

/-- A matrix with nonpositive quadratic form is dissipative on matrices with any number of
columns, in the Frobenius inner product. -/
theorem inner_mul_self_nonpos {M : Matrix m m ℝ} (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
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
theorem norm_mul_le_mul_norm {M : Matrix m m ℝ} {μ : ℝ} (hμ0 : 0 ≤ μ)
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
theorem inner_proj_mul {P : Matrix m m ℝ} (hPt : Pᵀ = P) (A B : Matrix m p ℝ) :
    ⟪P * A, B⟫ = ⟪A, P * B⟫ := by
  rw [Frobenius.inner_mul_left, hPt]

/-- Right multiplication by a symmetric idempotent matrix is self-adjoint. -/
theorem inner_mul_proj {Q : Matrix n n ℝ} (hQt : Qᵀ = Q) (A B : Matrix m n ℝ) :
    ⟪A * Q, B⟫ = ⟪A, B * Q⟫ := by
  rw [Frobenius.inner_mul_right, hQt]

/-- If `a² ≤ b a` with `b ≥ 0`, then `a ≤ b`. -/
theorem le_of_sq_le_mul {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b * a) :
    a ≤ b := by
  by_contra hc
  rw [not_le] at hc
  nlinarith [hb, h, hc]

/-- Left multiplication by an orthogonal projector does not increase the Frobenius norm. -/
theorem norm_proj_mul_le {P : Matrix m m ℝ} (hP : P * P = P) (hPt : Pᵀ = P)
    (A : Matrix m p ℝ) : ‖P * A‖ ≤ ‖A‖ := by
  refine le_of_sq_le_mul (norm_nonneg _) ?_
  rw [← real_inner_self_eq_norm_sq, inner_proj_mul hPt, ← Matrix.mul_assoc, hP]
  exact real_inner_le_norm _ _

/-- Right multiplication by an orthogonal projector does not increase the Frobenius norm. -/
theorem norm_mul_proj_le {Q : Matrix n n ℝ} (hQ : Q * Q = Q) (hQt : Qᵀ = Q)
    (A : Matrix m n ℝ) : ‖A * Q‖ ≤ ‖A‖ := by
  refine le_of_sq_le_mul (norm_nonneg _) ?_
  rw [← real_inner_self_eq_norm_sq, inner_mul_proj hQt, Matrix.mul_assoc, hQ]
  exact real_inner_le_norm _ _

/-- **Energy estimate of a Galerkin backward Euler step** for a dissipative `M` on the range of
an orthogonal projector `P`: if `W = P W` and `W - h P M W = P R`, then `‖W‖ ≤ ‖R‖`. -/
theorem norm_le_of_galerkin {M P : Matrix m m ℝ} {h : ℝ}
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
theorem exists_galerkin_resolvent {M P : Matrix m m ℝ} {h : ℝ}
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

omit [Fintype p] in
/-- The equation of the Galerkin resolvent composed with the old column projector, applied to a
matrix. -/
theorem xi_mul_sub [DecidableEq m] {M P₀ P₁ Ξ : Matrix m m ℝ} {h : ℝ}
    (hΞ : Ξ - h • (P₁ * (M * Ξ)) = P₁ * (1 - h • (P₀ * M))) (X : Matrix m p ℝ) :
    Ξ * X - h • (P₁ * (M * (Ξ * X))) = P₁ * (X - h • (P₀ * (M * X))) := by
  have := congrArg (fun A => A * X) hΞ
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc P₁, Matrix.mul_assoc M,
    Matrix.mul_assoc P₁, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
    Matrix.mul_assoc P₀] at this
  exact this

/-- The complement of an orthogonal projector acting on the left does not increase the Frobenius
norm. -/
theorem norm_sub_proj_mul_le {P : Matrix m m ℝ} (hP : P * P = P)
    (hPt : Pᵀ = P) (A : Matrix m p ℝ) : ‖A - P * A‖ ≤ ‖A‖ := by
  classical
  have hc : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hP]; abel
  have hct : (1 - P)ᵀ = 1 - P := by rw [Matrix.transpose_sub, Matrix.transpose_one, hPt]
  have := norm_proj_mul_le hc hct A
  rwa [Matrix.sub_mul, Matrix.one_mul] at this

/-- The complement of an orthogonal projector acting on the right does not increase the Frobenius
norm. -/
theorem norm_sub_mul_proj_le {Q : Matrix n n ℝ} (hQ : Q * Q = Q)
    (hQt : Qᵀ = Q) (A : Matrix m n ℝ) : ‖A - A * Q‖ ≤ ‖A‖ := by
  classical
  have hc : (1 - Q) * (1 - Q) = 1 - Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hQ]; abel
  have hct : (1 - Q)ᵀ = 1 - Q := by rw [Matrix.transpose_sub, Matrix.transpose_one, hQt]
  have := norm_mul_proj_le hc hct A
  rwa [Matrix.mul_sub, Matrix.mul_one] at this

/-- The Galerkin resolvent composed with the old column projector differs from the new column
projector by at most `2 h μ`. -/
theorem norm_xi_sub_mul_le [DecidableEq m] {M P₀ P₁ Ξ : Matrix m m ℝ} {h μ : ℝ}
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 ≤ h)
    (hP₀ : P₀ * P₀ = P₀) (hP₀t : P₀ᵀ = P₀) (hP₁ : P₁ * P₁ = P₁) (hP₁t : P₁ᵀ = P₁)
    (hΞP : P₁ * Ξ = Ξ) (hΞ : Ξ - h • (P₁ * (M * Ξ)) = P₁ * (1 - h • (P₀ * M)))
    (Z : Matrix m p ℝ) : ‖(Ξ - P₁) * Z‖ ≤ 2 * (h * μ) * ‖Z‖ := by
  have h1 : P₁ * ((Ξ - P₁) * Z) = (Ξ - P₁) * Z := by
    rw [← Matrix.mul_assoc, Matrix.mul_sub, hΞP, hP₁]
  have h2 : (Ξ - P₁) * Z - h • (P₁ * (M * ((Ξ - P₁) * Z))) =
      P₁ * (h • (M * (P₁ * Z) - P₀ * (M * Z))) := by
    have e : (Ξ - P₁) * Z = Ξ * Z - P₁ * Z := Matrix.sub_mul _ _ _
    rw [e, Matrix.mul_sub, Matrix.mul_sub, smul_sub, sub_sub_sub_comm, xi_mul_sub hΞ]
    simp only [Matrix.mul_smul, Matrix.mul_sub, smul_sub]
    abel
  refine (norm_le_of_galerkin hdiss hP₁t hh h1 h2).trans ?_
  rw [norm_smul, Real.norm_of_nonneg hh]
  have h3 := norm_sub_le (M * (P₁ * Z)) (P₀ * (M * Z))
  have h4 := (norm_mul_le_mul_norm hμ0 hμ (P₁ * Z)).trans
    (mul_le_mul_of_nonneg_left (norm_proj_mul_le hP₁ hP₁t Z) hμ0)
  have h5 := (norm_proj_mul_le hP₀ hP₀t (M * Z)).trans (norm_mul_le_mul_norm hμ0 hμ Z)
  calc h * ‖M * (P₁ * Z) - P₀ * (M * Z)‖ ≤ h * (μ * ‖Z‖ + μ * ‖Z‖) :=
        mul_le_mul_of_nonneg_left (h3.trans (add_le_add h4 h5)) hh
    _ = 2 * (h * μ) * ‖Z‖ := by ring

/-- **Energy estimate of a backward Euler step of the full problem**: if
`W - h M W + h W CᵀC = R` with `M` dissipative, then `‖W‖ ≤ ‖R‖`. -/
theorem norm_le_of_backwardEuler {M : Matrix m m ℝ} {C : Matrix k n ℝ} {h : ℝ}
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 ≤ h) {W R : Matrix m n ℝ}
    (heq : W - h • (M * W) + h • (W * (Cᵀ * C)) = R) : ‖W‖ ≤ ‖R‖ := by
  refine le_of_sq_le_mul (norm_nonneg _) ?_
  have h1 : ⟪W, W⟫ - h * ⟪M * W, W⟫ + h * ⟪W * Cᵀ, W * Cᵀ⟫ = ⟪R, W⟫ := by
    have h0 := congrArg (fun X => ⟪X, W⟫) heq
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left] at h0
    rwa [← Matrix.mul_assoc W, Frobenius.inner_mul_right (W * Cᵀ) C W] at h0
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1
  nlinarith [inner_mul_self_nonpos hdiss W, real_inner_le_norm R W,
    mul_nonneg hh (sq_nonneg ‖W * Cᵀ‖), mul_nonpos_of_nonneg_of_nonpos hh
    (inner_mul_self_nonpos hdiss W)]

/-! ### Scalar inequalities -/

/-- `(√h u) (√h v) = h (u v)` for `h ≥ 0`. -/
theorem sqrt_mul_mul_sqrt_mul {h : ℝ} (hh : 0 ≤ h) (u v : ℝ) :
    √h * u * (√h * v) = h * (u * v) := by
  have := Real.mul_self_sqrt hh
  calc √h * u * (√h * v) = √h * √h * (u * v) := by ring
    _ = h * (u * v) := by rw [this]

/-- `d ≤ √(d² + c²)` for `d ≥ 0`. -/
theorem le_sqrt_sq_add_sq_left {d c : ℝ} (hd : 0 ≤ d) : d ≤ √(d ^ 2 + c ^ 2) := by
  have := Real.sqrt_le_sqrt (show d ^ 2 ≤ d ^ 2 + c ^ 2 by nlinarith [sq_nonneg c])
  rwa [Real.sqrt_sq hd] at this

/-- `c ≤ √(d² + c²)` for `c ≥ 0`. -/
theorem le_sqrt_sq_add_sq_right {d c : ℝ} (hc : 0 ≤ c) : c ≤ √(d ^ 2 + c ^ 2) := by
  have := Real.sqrt_le_sqrt (show c ^ 2 ≤ d ^ 2 + c ^ 2 by nlinarith [sq_nonneg d])
  rwa [Real.sqrt_sq hc] at this

/-- The Cauchy–Schwarz inequality in the plane. -/
theorem mul_add_mul_le_sqrt_mul_sqrt {d c x E : ℝ} (hd : 0 ≤ d) (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hE : 0 ≤ E) : d * x + c * E ≤ √(d ^ 2 + c ^ 2) * √(x ^ 2 + E ^ 2) := by
  have h0 : 0 ≤ d * x + c * E := add_nonneg (mul_nonneg hd hx) (mul_nonneg hc hE)
  have h1 : (d * x + c * E) ^ 2 ≤ (d ^ 2 + c ^ 2) * (x ^ 2 + E ^ 2) := by
    nlinarith [sq_nonneg (d * E - c * x)]
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq h0, Real.sqrt_mul (by positivity)] at h2

/-- If `l² + c² ≤ e c + t l`, then `l ≤ e / 2 + t`. -/
theorem le_half_add_of_sq_add_sq_le {l c e t : ℝ} (he : 0 ≤ e) (ht : 0 ≤ t)
    (h : l ^ 2 + c ^ 2 ≤ e * c + t * l) : l ≤ e / 2 + t := by
  have h1 : l ^ 2 ≤ e ^ 2 / 4 + t * l := by nlinarith [sq_nonneg (e - 2 * c)]
  by_contra hcon
  rw [not_le] at hcon
  have h3 : e / 2 < l - t := by linarith
  have h4 : (e / 2 + t) * (e / 2) < l * (l - t) :=
    mul_lt_mul'' hcon h3 (by positivity) (by positivity)
  nlinarith [mul_nonneg ht he]

/-- The scalar form of the step inequality: `x`, `E` are the error and the square root of its
stiff energy after the step, `d`, `c` those of the S-step remainder, `y` the error before the
step, `l` the stiff term of the K-step. -/
theorem step_scalar {x E d c a b y l k ν η eh : ℝ} (hx : 0 ≤ x) (hE : 0 ≤ E)
    (hd : 0 ≤ d) (hc : 0 ≤ c) (hy : 0 ≤ y) (hl : 0 ≤ l) (hk : 0 ≤ k) (hν : 0 ≤ ν) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 2) (heh0 : 0 ≤ eh) (ha : a = 2 * η * eh) (hb : b = 2 * η * k)
    (heh : eh ≤ (y + η * (y + ν)) / 2) (hD : d ^ 2 + c ^ 2 ≤ a * c + b * d)
    (hmain : x ^ 2 + E ^ 2 ≤ y * x + (1 + η) * d * x + c * E + (a * E + b * x) +
      η * x * (l + y + k + (y + ν) + x)) :
    (1 - η) * √(x ^ 2 + E ^ 2) ≤ (1 + 6 * η) * y + η * (l + 6 * k + 3 * ν) := by
  obtain ⟨Δ, hΔ⟩ : ∃ Δ, Δ = √(d ^ 2 + c ^ 2) := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ, Ψ = √(x ^ 2 + E ^ 2) := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hΔ0 : 0 ≤ Δ := by rw [hΔ]; exact Real.sqrt_nonneg _
  have hΨ0 : 0 ≤ Ψ := by rw [hΨ]; exact Real.sqrt_nonneg _
  have hΔ2 : Δ ^ 2 = d ^ 2 + c ^ 2 := by rw [hΔ]; exact Real.sq_sqrt (by positivity)
  have hΨ2 : Ψ ^ 2 = x ^ 2 + E ^ 2 := by rw [hΨ]; exact Real.sq_sqrt (by positivity)
  have hdΔ : d ≤ Δ := by rw [hΔ]; exact le_sqrt_sq_add_sq_left hd
  have hcΔ : c ≤ Δ := by rw [hΔ]; exact le_sqrt_sq_add_sq_right hc
  have hxΨ : x ≤ Ψ := by rw [hΨ]; exact le_sqrt_sq_add_sq_left hx
  have hEΨ : E ≤ Ψ := by rw [hΨ]; exact le_sqrt_sq_add_sq_right hE
  have hΔab : Δ ≤ a + b := by
    refine le_of_sq_le_mul (add_nonneg ha0 hb0) ?_
    linarith [mul_le_mul_of_nonneg_left hcΔ ha0, mul_le_mul_of_nonneg_left hdΔ hb0]
  have hcs : d * x + c * E ≤ Δ * Ψ := by
    rw [hΔ, hΨ]; exact mul_add_mul_le_sqrt_mul_sqrt hd hc hx hE
  have hcs' : d * x + c * E ≤ (a + b) * Ψ := hcs.trans (mul_le_mul_of_nonneg_right hΔab hΨ0)
  have h1 : (1 + η) * d * x + c * E ≤ (1 + η) * ((a + b) * Ψ) := by
    linarith [mul_nonneg hη0 (mul_nonneg hc hE), mul_le_mul_of_nonneg_left hcs'
      (by linarith : (0 : ℝ) ≤ 1 + η)]
  have h2 : a * E + b * x ≤ (a + b) * Ψ := by
    linarith [mul_le_mul_of_nonneg_left hEΨ ha0, mul_le_mul_of_nonneg_left hxΨ hb0]
  have hs0 : 0 ≤ l + y + k + (y + ν) + Ψ := by positivity
  have h3 : η * x * (l + y + k + (y + ν) + x) ≤ η * (l + y + k + (y + ν) + Ψ) * Ψ := by
    have e1 : l + y + k + (y + ν) + x ≤ l + y + k + (y + ν) + Ψ := by linarith
    have e2 := mul_le_mul hxΨ e1 (by positivity) hΨ0
    linarith [mul_le_mul_of_nonneg_left e2 hη0]
  have h4 : y * x ≤ y * Ψ := mul_le_mul_of_nonneg_left hxΨ hy
  have key : Ψ ^ 2 ≤ (y + (2 + η) * (a + b) + η * (l + y + k + (y + ν) + Ψ)) * Ψ := by
    rw [hΨ2]; linarith
  have hΨle : Ψ ≤ y + (2 + η) * (a + b) + η * (l + y + k + (y + ν) + Ψ) :=
    le_of_sq_le_mul (by positivity) key
  have hab : a + b ≤ η * (3 / 2 * y + ν / 2 + 2 * k) := by
    rw [ha, hb]
    have e1 : η * (y + ν) ≤ 1 / 2 * (y + ν) := mul_le_mul_of_nonneg_right hη (by positivity)
    have e2 : eh ≤ (y + 1 / 2 * (y + ν)) / 2 := by linarith
    linarith [mul_le_mul_of_nonneg_left e2 hη0]
  have hq0 : 0 ≤ 3 / 2 * y + ν / 2 + 2 * k := by positivity
  have h5 : (2 + η) * (a + b) ≤ 5 / 2 * (η * (3 / 2 * y + ν / 2 + 2 * k)) := by
    have e1 : (2 + η) * (a + b) ≤ (2 + η) * (η * (3 / 2 * y + ν / 2 + 2 * k)) :=
      mul_le_mul_of_nonneg_left hab (by linarith)
    have e2 : 0 ≤ η * (3 / 2 * y + ν / 2 + 2 * k) := mul_nonneg hη0 hq0
    linarith [mul_le_mul_of_nonneg_right hη e2]
  rw [← hΨ]
  linarith [mul_nonneg hη0 hy, mul_nonneg hη0 hν, mul_nonneg hη0 hk, mul_nonneg hη0 hl]

/-! ### The step in terms of projectors -/

variable {M : Matrix m m ℝ} {C : Matrix k n ℝ} {h μ : ℝ} {P₀ P₁ : Matrix m m ℝ}
  {Q₀ Q₁ : Matrix n n ℝ} {Y₀ YK YL Y₁ X₀ X₁ δ : Matrix m n ℝ}

/-- Moving a Gram matrix `CᵀC` and a row projector through the Frobenius inner product. -/
theorem inner_mul_gram_proj (hQ₀t : Q₀ᵀ = Q₀) {A : Matrix m n ℝ} (hA : A * Q₀ = A)
    (B : Matrix m n ℝ) : ⟪A, B * (Cᵀ * C) * Q₀⟫ = ⟪A * Cᵀ, B * Cᵀ⟫ := by
  rw [Frobenius.inner_mul_right', hQ₀t, hA, ← Matrix.mul_assoc, Frobenius.inner_mul_right']

/-- The L-step equation solved for the start value. -/
theorem start_eq_of_lstep (lEq : YL = Y₀ + h • (P₀ * (M * YL - YL * (Cᵀ * C))))
    (lP : P₀ * YL = YL) :
    Y₀ = YL - h • (P₀ * (M * YL)) + h • (YL * (Cᵀ * C)) := by
  have := lEq
  rw [Matrix.mul_sub, ← Matrix.mul_assoc P₀ YL, lP, smul_sub] at this
  have h' : Y₀ = YL - (h • (P₀ * (M * YL)) - h • (YL * (Cᵀ * C))) :=
    eq_sub_of_add_eq this.symm
  rw [h']; abel

/-- **The K-step.** The stiff term `Λ = h Y_K CᵀC Q₀` of the K-step is bounded by the start
value, and for every matrix `X₀` by half the square root of the stiff energy of `Y₀ - X₀` plus
`h ‖X₀ CᵀC‖`. -/
theorem exists_kstep_gram_term (hQ₀ : Q₀ * Q₀ = Q₀) (hQ₀t : Q₀ᵀ = Q₀)
    (kEq : YK = Y₀ + h • ((M * YK - YK * (Cᵀ * C)) * Q₀))
    (kQ : YK * Q₀ = YK) (kP : P₁ * YK = YK)
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 < h) :
    ∃ Λ : Matrix m n ℝ, YK + Λ - h • (M * YK) = Y₀ ∧ P₁ * Λ = Λ ∧ ‖Λ‖ ≤ ‖Y₀‖ ∧
      ∀ X₀ : Matrix m n ℝ, ‖Λ‖ ≤ √h * ‖(Y₀ - X₀) * Cᵀ‖ / 2 + h * ‖X₀ * (Cᵀ * C)‖ := by
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = h • (YK * (Cᵀ * C) * Q₀) := ⟨_, rfl⟩
  have eqK : YK + Λ - h • (M * YK) = Y₀ := by
    have := kEq
    rw [Matrix.sub_mul, Matrix.mul_assoc M, kQ, smul_sub, ← hΛ] at this
    calc YK + Λ - h • (M * YK) = Y₀ + (h • (M * YK) - Λ) + Λ - h • (M * YK) := by rw [← this]
      _ = Y₀ := by abel
  have hPΛ : P₁ * Λ = Λ := by
    rw [hΛ, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, kP]
  have hΛQ : Λ * Q₀ = Λ := by
    rw [hΛ, Matrix.smul_mul, Matrix.mul_assoc _ Q₀ Q₀, hQ₀]
  have hI : ⟪YK, Λ⟫ + ⟪Λ, Λ⟫ - h * ⟪M * YK, Λ⟫ = ⟪Y₀, Λ⟫ := by
    have := congrArg (fun A => ⟪A, Λ⟫) eqK
    rwa [inner_sub_left, inner_add_left, real_inner_smul_left] at this
  have hYK : ⟪YK, Λ⟫ = h * ‖YK * Cᵀ‖ ^ 2 := by
    rw [hΛ, real_inner_smul_right, inner_mul_gram_proj hQ₀t kQ, real_inner_self_eq_norm_sq]
  have hMK : ⟪M * YK, Λ⟫ = h * ⟪M * (YK * Cᵀ), YK * Cᵀ⟫ := by
    rw [hΛ, real_inner_smul_right,
      inner_mul_gram_proj hQ₀t (A := M * YK) (by rw [Matrix.mul_assoc, kQ]),
      Matrix.mul_assoc]
  have hi := inner_mul_self_nonpos hdiss (YK * Cᵀ)
  have hl := real_inner_le_norm Y₀ Λ
  have hhh : 0 ≤ -(h * (h * ⟪M * (YK * Cᵀ), YK * Cᵀ⟫)) := by
    have := mul_nonpos_of_nonneg_of_nonpos hh.le (mul_nonpos_of_nonneg_of_nonpos hh.le hi)
    linarith
  refine ⟨Λ, eqK, hPΛ, ?_, fun X₀ => ?_⟩
  · rw [real_inner_self_eq_norm_sq] at hI
    refine le_of_sq_le_mul (norm_nonneg _) ?_
    nlinarith [mul_nonneg hh.le (sq_nonneg ‖YK * Cᵀ‖)]
  · -- the equation of `Λ`: the K-step equation multiplied by `h CᵀC Q₀` from the right
    have eΛ : Λ + h • (Λ * (Cᵀ * C) * Q₀) - h • (M * Λ) = h • (Y₀ * (Cᵀ * C) * Q₀) := by
      have := congrArg (fun A => h • (A * (Cᵀ * C) * Q₀)) eqK
      simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, smul_sub, smul_add] at this
      rw [← this, hΛ]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    have hJ : ⟪Λ, Λ⟫ + h * ⟪Λ * Cᵀ, Λ * Cᵀ⟫ - h * ⟪M * Λ, Λ⟫ =
        h * (⟪(Y₀ - X₀) * Cᵀ, Λ * Cᵀ⟫ + ⟪X₀ * (Cᵀ * C), Λ⟫) := by
      have h0 := congrArg (fun A => ⟪Λ, A⟫) eΛ
      simp only [inner_sub_right, inner_add_right, real_inner_smul_right] at h0
      rw [inner_mul_gram_proj hQ₀t hΛQ, inner_mul_gram_proj hQ₀t hΛQ,
        real_inner_comm (M * Λ) Λ] at h0
      rw [h0, ← Matrix.mul_assoc X₀, Frobenius.inner_mul_right (X₀ * Cᵀ) C Λ, ← inner_add_left,
        ← Matrix.add_mul, sub_add_cancel, real_inner_comm (Y₀ * Cᵀ) (Λ * Cᵀ)]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hJ
    have hMΛ := inner_mul_self_nonpos hdiss Λ
    have g1 := real_inner_le_norm ((Y₀ - X₀) * Cᵀ) (Λ * Cᵀ)
    have g2 := real_inner_le_norm (X₀ * (Cᵀ * C)) Λ
    have hs2 : √h ^ 2 = h := Real.sq_sqrt hh.le
    refine le_half_add_of_sq_add_sq_le (c := √h * ‖Λ * Cᵀ‖)
      (mul_nonneg (Real.sqrt_nonneg h) (norm_nonneg _)) (mul_nonneg hh.le (norm_nonneg _)) ?_
    rw [mul_pow, hs2, sqrt_mul_mul_sqrt_mul hh.le]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hh.le hMΛ, mul_le_mul_of_nonneg_left g1 hh.le,
      mul_le_mul_of_nonneg_left g2 hh.le]

/-- **The K-step against the reference.** The K-step result differs from the reference
restricted to the old row space by the stiff term, the error and `h ‖X₁ CᵀC‖`. -/
theorem norm_kstep_sub_le (hQ₀ : Q₀ * Q₀ = Q₀) (hQ₀t : Q₀ᵀ = Q₀) (yQ : Y₀ * Q₀ = Y₀)
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 < h) {Λ : Matrix m n ℝ}
    (eqK : YK + Λ - h • (M * YK) = Y₀)
    (hX : X₁ - h • (M * X₁) + h • (X₁ * (Cᵀ * C)) = X₀ + δ) :
    ‖YK - X₁ * Q₀‖ ≤ ‖Λ‖ + ‖Y₀ - X₀ - δ‖ + h * ‖X₁ * (Cᵀ * C)‖ := by
  classical
  have e1 : X₁ * Q₀ - h • (M * (X₁ * Q₀)) = (X₀ + δ) * Q₀ - h • (X₁ * (Cᵀ * C) * Q₀) := by
    have := congrArg (fun A => A * Q₀) hX
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc] at this
    simp only [Matrix.mul_assoc, Matrix.add_mul]
    rw [← this]; abel
  have heq : YK - X₁ * Q₀ - h • ((1 : Matrix m m ℝ) * (M * (YK - X₁ * Q₀))) =
      (1 : Matrix m m ℝ) * ((Y₀ - X₀ - δ) * Q₀ - Λ + h • (X₁ * (Cᵀ * C) * Q₀)) := by
    rw [Matrix.one_mul, Matrix.one_mul, Matrix.mul_sub, smul_sub, sub_sub_sub_comm, e1]
    have e2 : YK - h • (M * YK) = Y₀ * Q₀ - Λ := by rw [yQ, ← eqK]; abel
    rw [e2]
    simp only [Matrix.sub_mul, Matrix.add_mul]
    abel
  refine (norm_le_of_galerkin hdiss Matrix.transpose_one hh.le (Matrix.one_mul _) heq).trans ?_
  have n1 := norm_mul_proj_le hQ₀ hQ₀t (Y₀ - X₀ - δ)
  have n2 : ‖h • (X₁ * (Cᵀ * C) * Q₀)‖ ≤ h * ‖X₁ * (Cᵀ * C)‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh.le]
    exact mul_le_mul_of_nonneg_left (norm_mul_proj_le hQ₀ hQ₀t _) hh.le
  have n3 := norm_add_le ((Y₀ - X₀ - δ) * Q₀ - Λ) (h • (X₁ * (Cᵀ * C) * Q₀))
  have n4 := norm_sub_le ((Y₀ - X₀ - δ) * Q₀) Λ
  linarith

/-- **The L-step against the reference.** The stiff energy of the L-step result minus the
reference projected onto the old column space is bounded by the error: no stiff constant. -/
theorem sqrt_mul_norm_lstep_sub_le (hP₀ : P₀ * P₀ = P₀) (hP₀t : P₀ᵀ = P₀)
    (yP : P₀ * Y₀ = Y₀) (lEq : YL = Y₀ + h • (P₀ * (M * YL - YL * (Cᵀ * C))))
    (lP : P₀ * YL = YL) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
    (hμ0 : 0 ≤ μ) (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hX : X₁ - h • (M * X₁) + h • (X₁ * (Cᵀ * C)) = X₀ + δ) :
    √h * ‖(YL - P₀ * X₁) * Cᵀ‖ ≤ (‖Y₀ - X₀ - δ‖ + h * μ * ‖X₁ - P₀ * X₁‖) / 2 := by
  obtain ⟨ê, hê⟩ : ∃ ê, ê = YL - P₀ * X₁ := ⟨_, rfl⟩
  rw [← hê]
  have hPê : P₀ * ê = ê := by rw [hê, Matrix.mul_sub, lP, ← Matrix.mul_assoc, hP₀]
  have eX : P₀ * X₁ = P₀ * (X₀ + δ) + h • (P₀ * (M * X₁)) - h • (P₀ * X₁ * (Cᵀ * C)) := by
    have := congrArg (fun A => P₀ * A) hX
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc] at this
    simp only [← Matrix.mul_assoc, Matrix.mul_add]
    rw [← this]; abel
  have eê : ê = P₀ * (Y₀ - X₀ - δ) + h • (P₀ * (M * ê)) - h • (ê * (Cᵀ * C)) -
      h • (P₀ * (M * (X₁ - P₀ * X₁))) := by
    have e1 := lEq
    rw [Matrix.mul_sub, ← Matrix.mul_assoc P₀ YL, lP, smul_sub] at e1
    have e2 : ê = YL - P₀ * X₁ := hê
    rw [e2]
    conv_lhs => rw [e1, eX, ← yP]
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, smul_sub, ← Matrix.mul_assoc]
    abel
  have h1 : ⟪ê, ê⟫ = ⟪Y₀ - X₀ - δ, ê⟫ + h * ⟪M * ê, ê⟫ - h * ⟪ê * Cᵀ, ê * Cᵀ⟫ -
      h * ⟪M * (X₁ - P₀ * X₁), ê⟫ := by
    have h0 : ⟪ê, ê⟫ = ⟪P₀ * (Y₀ - X₀ - δ) + h • (P₀ * (M * ê)) - h • (ê * (Cᵀ * C)) -
        h • (P₀ * (M * (X₁ - P₀ * X₁))), ê⟫ := congrArg (fun A => ⟪A, ê⟫) eê
    rw [h0, inner_sub_left, inner_sub_left, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_left, inner_proj_mul hP₀t,
      inner_proj_mul hP₀t, inner_proj_mul hP₀t, hPê, ← Matrix.mul_assoc ê,
      Frobenius.inner_mul_right (ê * Cᵀ) C ê]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1
  have g1 := real_inner_le_norm (Y₀ - X₀ - δ) ê
  have g2 := inner_mul_self_nonpos hdiss ê
  have g3 : -(μ * ‖X₁ - P₀ * X₁‖ * ‖ê‖) ≤ ⟪M * (X₁ - P₀ * X₁), ê⟫ := by
    have := neg_le_of_abs_le (abs_real_inner_le_norm (M * (X₁ - P₀ * X₁)) ê)
    have := mul_le_mul_of_nonneg_right (norm_mul_le_mul_norm hμ0 hμ (X₁ - P₀ * X₁))
      (norm_nonneg ê)
    linarith
  obtain ⟨g, hg⟩ : ∃ g, g = ‖Y₀ - X₀ - δ‖ + h * μ * ‖X₁ - P₀ * X₁‖ := ⟨_, rfl⟩
  have hg0 : 0 ≤ g := by rw [hg]; positivity
  rw [← hg]
  have key : ‖ê‖ ^ 2 + h * ‖ê * Cᵀ‖ ^ 2 ≤ g * ‖ê‖ := by
    rw [hg]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hh.le g2, mul_le_mul_of_nonneg_left g3 hh.le]
  have hs2 : √h ^ 2 = h := Real.sq_sqrt hh.le
  refine (pow_le_pow_iff_left₀ (mul_nonneg (Real.sqrt_nonneg h) (norm_nonneg _))
    (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, hs2]
  nlinarith [sq_nonneg (g - 2 * ‖ê‖)]

/-- **The stiff source of the S-step remainder.** With `Y_L = (Y_L - P₀ X₁) + P₀ X₁` the source
`h (Ξ - P₁) Y_L CᵀC`, tested with a matrix `Z`, is bounded by `2 h μ` times the stiff energies of
`Y_L - P₀ X₁` and of `Z` plus `2 h μ h ‖X₁ CᵀC‖ ‖Z‖`. -/
theorem inner_xi_sub_mul_gram_le [DecidableEq m] (hP₀ : P₀ * P₀ = P₀) (hP₀t : P₀ᵀ = P₀)
    (hP₁ : P₁ * P₁ = P₁) (hP₁t : P₁ᵀ = P₁) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
    (hμ0 : 0 ≤ μ) (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    {Ξ : Matrix m m ℝ} (hΞP : P₁ * Ξ = Ξ)
    (hΞ : Ξ - h • (P₁ * (M * Ξ)) = P₁ * (1 - h • (P₀ * M))) (YL X₁ Z : Matrix m n ℝ) :
    h * ⟪(Ξ - P₁) * YL * (Cᵀ * C), Z⟫ ≤
      2 * (h * μ) * (√h * ‖(YL - P₀ * X₁) * Cᵀ‖) * (√h * ‖Z * Cᵀ‖) +
        2 * (h * μ) * (h * ‖X₁ * (Cᵀ * C)‖) * ‖Z‖ := by
  have e : (Ξ - P₁) * YL * (Cᵀ * C) = (Ξ - P₁) * ((YL - P₀ * X₁) * Cᵀ) * C +
      (Ξ - P₁) * (P₀ * (X₁ * (Cᵀ * C))) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  have a1 := real_inner_le_norm ((Ξ - P₁) * ((YL - P₀ * X₁) * Cᵀ)) (Z * Cᵀ)
  have a2 := real_inner_le_norm ((Ξ - P₁) * (P₀ * (X₁ * (Cᵀ * C)))) Z
  have hη0 : 0 ≤ 2 * (h * μ) := by positivity
  have b1 := norm_xi_sub_mul_le hdiss hμ0 hμ hh.le hP₀ hP₀t hP₁ hP₁t hΞP hΞ
    ((YL - P₀ * X₁) * Cᵀ)
  have b2 := (norm_xi_sub_mul_le hdiss hμ0 hμ hh.le hP₀ hP₀t hP₁ hP₁t hΞP hΞ
    (P₀ * (X₁ * (Cᵀ * C)))).trans
    (mul_le_mul_of_nonneg_left (norm_proj_mul_le hP₀ hP₀t _) hη0)
  have c1 := a1.trans (mul_le_mul_of_nonneg_right b1 (norm_nonneg _))
  have c2 := a2.trans (mul_le_mul_of_nonneg_right b2 (norm_nonneg _))
  rw [e, inner_add_left, Frobenius.inner_mul_right]
  have f : 2 * (h * μ) * (√h * ‖(YL - P₀ * X₁) * Cᵀ‖) * (√h * ‖Z * Cᵀ‖) =
      h * (2 * (h * μ) * ‖(YL - P₀ * X₁) * Cᵀ‖ * ‖Z * Cᵀ‖) := by
    rw [mul_assoc (2 * (h * μ)), sqrt_mul_mul_sqrt_mul hh.le]; ring
  rw [f]
  have := mul_le_mul_of_nonneg_left (add_le_add c1 c2) hh.le
  linarith

/-- **The S-step against the L-step.** The result of the S-step is the Galerkin resolvent `Ξ` of
the new column space applied to the result of the L-step, up to a remainder `D` whose norm and
stiff energy are bounded by the stiff source `h (Ξ - P₁) Y_L CᵀC` tested with `D`. The stiff
terms of the two substeps cancel. -/
theorem exists_sstep_decomposition [DecidableEq m] (hP₁ : P₁ * P₁ = P₁) (hP₁t : P₁ᵀ = P₁)
    (hQ₁t : Q₁ᵀ = Q₁) (lEq : YL = Y₀ + h • (P₀ * (M * YL - YL * (Cᵀ * C))))
    (lP : P₀ * YL = YL) (lQ : YL * Q₁ = YL)
    (sEq : Y₁ = P₁ * (Y₀ + h • (M * Y₁ - Y₁ * (Cᵀ * C))) * Q₁)
    (sP : P₁ * Y₁ = Y₁) (sQ : Y₁ * Q₁ = Y₁) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
    (hh : 0 < h) :
    ∃ (Ξ : Matrix m m ℝ) (D : Matrix m n ℝ), P₁ * Ξ = Ξ ∧
      Ξ - h • (P₁ * (M * Ξ)) = P₁ * (1 - h • (P₀ * M)) ∧ Y₁ = Ξ * YL + D ∧
      ‖D‖ ^ 2 + h * ‖D * Cᵀ‖ ^ 2 ≤ -(h * ⟪(Ξ - P₁) * YL * (Cᵀ * C), D⟫) := by
  obtain ⟨Ξ, hΞP, hΞ⟩ := exists_galerkin_resolvent hdiss hP₁ hP₁t hh.le (1 - h • (P₀ * M))
  obtain ⟨D, hD⟩ : ∃ D, D = Y₁ - Ξ * YL := ⟨_, rfl⟩
  refine ⟨Ξ, D, hΞP, hΞ, by rw [hD]; abel, ?_⟩
  have hPD : P₁ * D = D := by
    rw [hD, Matrix.mul_sub, sP, ← Matrix.mul_assoc, hΞP]
  have hDQ : D * Q₁ = D := by
    rw [hD, Matrix.sub_mul, sQ, Matrix.mul_assoc, lQ]
  -- the equation of the remainder
  have e2 : Ξ * YL = P₁ * (h • (M * (Ξ * YL)) + (YL - h • (P₀ * (M * YL)))) * Q₁ := by
    have e : Ξ * YL = P₁ * (h • (M * (Ξ * YL)) + (YL - h • (P₀ * (M * YL)))) := by
      rw [Matrix.mul_add, Matrix.mul_smul]
      exact (sub_eq_iff_eq_add'.1 (xi_mul_sub hΞ YL))
    have e' : Ξ * YL * Q₁ = Ξ * YL := by rw [Matrix.mul_assoc, lQ]
    rw [← e, e']
  have e3 := start_eq_of_lstep lEq lP
  have eD : D = P₁ * (h • (M * D) - h • ((Y₁ - YL) * (Cᵀ * C))) * Q₁ := by
    have h0 : Y₁ - Ξ * YL = P₁ * (Y₀ + h • (M * Y₁ - Y₁ * (Cᵀ * C))) * Q₁ -
        P₁ * (h • (M * (Ξ * YL)) + (YL - h • (P₀ * (M * YL)))) * Q₁ :=
      congrArg₂ (fun A B => A - B) sEq e2
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
    rw [← Matrix.mul_assoc, Matrix.mul_sub, sP, ← Matrix.add_mul, hD, hDa, this]
  have h1 : ⟪D, D⟫ = h * ⟪M * D, D⟫ - h * (⟪D * Cᵀ, D * Cᵀ⟫ + ⟪Da * Cᵀ, D * Cᵀ⟫) := by
    have h0 : ⟪D, D⟫ = ⟪P₁ * (h • (M * D) - h • ((Y₁ - YL) * (Cᵀ * C))) * Q₁, D⟫ :=
      congrArg (fun A => ⟪A, D⟫) eD
    rw [h0, inner_mul_proj hQ₁t, inner_proj_mul hP₁t, hDQ, hPD, inner_sub_left,
      real_inner_smul_left, real_inner_smul_left, ← Matrix.mul_assoc (Y₁ - YL),
      Frobenius.inner_mul_right ((Y₁ - YL) * Cᵀ) C D, hDC, ← inner_proj_mul hP₁t, hsplit,
      ← hDC, inner_add_left]
  have h2 : ⟪Da * Cᵀ, D * Cᵀ⟫ = ⟪(Ξ - P₁) * YL * (Cᵀ * C), D⟫ := by
    rw [← hDa, ← Matrix.mul_assoc Da, Frobenius.inner_mul_right (Da * Cᵀ) C D]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, h2] at h1
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hh.le (inner_mul_self_nonpos hdiss D)]

/-- **The step inequality**, in terms of the projectors. -/
theorem sqrt_sq_norm_sub_add_le_of_projectors (hP₀ : P₀ * P₀ = P₀) (hP₀t : P₀ᵀ = P₀)
    (hP₁ : P₁ * P₁ = P₁) (hP₁t : P₁ᵀ = P₁) (hQ₀ : Q₀ * Q₀ = Q₀) (hQ₀t : Q₀ᵀ = Q₀) (hQ₁t : Q₁ᵀ = Q₁)
    (kEq : YK = Y₀ + h • ((M * YK - YK * (Cᵀ * C)) * Q₀))
    (kQ : YK * Q₀ = YK) (kP : P₁ * YK = YK) (yQ : Y₀ * Q₀ = Y₀) (yP : P₀ * Y₀ = Y₀)
    (lEq : YL = Y₀ + h • (P₀ * (M * YL - YL * (Cᵀ * C))))
    (lP : P₀ * YL = YL) (lQ : YL * Q₁ = YL)
    (sEq : Y₁ = P₁ * (Y₀ + h • (M * Y₁ - Y₁ * (Cᵀ * C))) * Q₁)
    (sP : P₁ * Y₁ = Y₁) (sQ : Y₁ * Q₁ = Y₁) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
    (hμ0 : 0 ≤ μ) (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hhμ : h * μ ≤ 1 / 2) (hX : X₁ - h • (M * X₁) + h • (X₁ * (Cᵀ * C)) = X₀ + δ)
    (Z : Matrix m n ℝ) :
    (1 - h * μ) * √(‖Y₁ - X₁‖ ^ 2 + h * ‖(Y₁ - X₁) * Cᵀ‖ ^ 2) ≤
      (1 + 6 * (h * μ)) * (‖Y₀ - X₀‖ + ‖δ‖) +
        h * μ * (min ‖Y₀‖ (√h * ‖(Y₀ - Z) * Cᵀ‖ / 2 + h * ‖Z * (Cᵀ * C)‖) +
          6 * (h * ‖X₁ * (Cᵀ * C)‖) + 3 * ‖X₁ - X₀‖) := by
  classical
  obtain ⟨Ξ, D, hΞP, hΞ, hY, hDe⟩ := exists_sstep_decomposition hP₁ hP₁t hQ₁t lEq lP lQ sEq sP
    sQ hdiss hh
  obtain ⟨Λ, eqK, hPΛ, hΛ1, hΛ2⟩ := exists_kstep_gram_term hQ₀ hQ₀t kEq kQ kP hdiss hh
  obtain ⟨e, he⟩ : ∃ e, e = Y₁ - X₁ := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = M * (YK - Y₁) := ⟨_, rfl⟩
  rw [← he]
  -- the start value in terms of the substeps
  have eP : P₁ * Y₀ = Ξ * YL - h • (P₁ * (M * (Ξ * YL))) + h • (P₁ * (YL * (Cᵀ * C))) := by
    have e1 := xi_mul_sub hΞ YL
    have e2 : YL - h • (P₀ * (M * YL)) = Y₀ - h • (YL * (Cᵀ * C)) :=
      eq_sub_of_add_eq (start_eq_of_lstep lEq lP).symm
    rw [e1, e2, Matrix.mul_sub, Matrix.mul_smul]; abel
  have eC : Y₀ - P₁ * Y₀ = -(h • (M * YK) - P₁ * (h • (M * YK))) := by
    conv_lhs => rw [← eqK]
    rw [Matrix.mul_sub, Matrix.mul_add, kP, hPΛ]; abel
  have eY : Y₀ = Ξ * YL - h • (P₁ * (M * (Ξ * YL))) + h • (P₁ * (YL * (Cᵀ * C))) -
      (h • (M * YK) - P₁ * (h • (M * YK))) := by
    rw [← eP]
    calc Y₀ = P₁ * Y₀ + (Y₀ - P₁ * Y₀) := by abel
      _ = _ := by rw [eC]; abel
  -- the error equation with the residual of the step
  have eρ : e - h • (M * e) + h • (e * (Cᵀ * C)) = Y₀ - X₀ - δ + (D - h • (P₁ * (M * D))) +
      h • (W - P₁ * W) + h • (D * (Cᵀ * C)) + h • ((Ξ - P₁) * YL * (Cᵀ * C)) := by
    have e1 : e - h • (M * e) + h • (e * (Cᵀ * C)) =
        Y₁ - h • (M * Y₁) + h • (Y₁ * (Cᵀ * C)) - (X₀ + δ) := by
      rw [he, ← hX]
      simp only [Matrix.mul_sub, Matrix.sub_mul, smul_sub]
      abel
    rw [e1, hW, hY]
    conv_rhs => rw [eY]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_smul,
      smul_add, smul_sub, Matrix.mul_assoc]
    abel
  have hI : ⟪e, e⟫ - h * ⟪M * e, e⟫ + h * ⟪e * (Cᵀ * C), e⟫ =
      ⟪Y₀ - X₀ - δ, e⟫ + ⟪D - h • (P₁ * (M * D)), e⟫ + h * ⟪W - P₁ * W, e⟫ +
        h * ⟪D * (Cᵀ * C), e⟫ + h * ⟪(Ξ - P₁) * YL * (Cᵀ * C), e⟫ := by
    have h0 := congrArg (fun A => ⟪A, e⟫) eρ
    rw [inner_add_left, inner_add_left, inner_add_left, inner_add_left, inner_add_left,
      inner_sub_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_left] at h0
    exact h0
  have q1 : ⟪e * (Cᵀ * C), e⟫ = ‖e * Cᵀ‖ ^ 2 := by
    rw [← Matrix.mul_assoc, Frobenius.inner_mul_right, real_inner_self_eq_norm_sq]
  have q2 : ⟪D * (Cᵀ * C), e⟫ = ⟪D * Cᵀ, e * Cᵀ⟫ := by
    rw [← Matrix.mul_assoc, Frobenius.inner_mul_right]
  rw [real_inner_self_eq_norm_sq, q1, q2] at hI
  -- the scalars
  obtain ⟨η, hη⟩ : ∃ η, η = h * μ := ⟨_, rfl⟩
  have hη0 : 0 ≤ η := by rw [hη]; exact mul_nonneg hh.le hμ0
  obtain ⟨y, hy⟩ : ∃ y, y = ‖Y₀ - X₀‖ + ‖δ‖ := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hyδ : ‖Y₀ - X₀ - δ‖ ≤ y := by rw [hy]; exact norm_sub_le _ _
  have hXY : ‖X₁ - Y₀‖ ≤ y + ‖X₁ - X₀‖ := by
    have e1 : X₁ - Y₀ = X₁ - X₀ - (Y₀ - X₀) := by abel
    have := norm_sub_le (X₁ - X₀) (Y₀ - X₀)
    rw [e1, hy]; linarith [norm_nonneg δ]
  have hs2 : √h ^ 2 = h := Real.sq_sqrt hh.le
  -- the S-step remainder
  have hD' : ‖D‖ ^ 2 + (√h * ‖D * Cᵀ‖) ^ 2 ≤
      2 * η * (√h * ‖(YL - P₀ * X₁) * Cᵀ‖) * (√h * ‖D * Cᵀ‖) +
        2 * η * (h * ‖X₁ * (Cᵀ * C)‖) * ‖D‖ := by
    have := inner_xi_sub_mul_gram_le (C := C) hP₀ hP₀t hP₁ hP₁t hdiss hμ0 hμ hh hΞP hΞ YL
      X₁ (-D)
    rw [inner_neg_right, Matrix.neg_mul, norm_neg, norm_neg, mul_neg, ← hη] at this
    rw [mul_pow, hs2]
    exact hDe.trans this
  have T4 := inner_xi_sub_mul_gram_le (C := C) hP₀ hP₀t hP₁ hP₁t hdiss hμ0 hμ hh hΞP hΞ YL
      X₁ e
  rw [← hη] at T4
  have T3 : h * ⟪D * Cᵀ, e * Cᵀ⟫ ≤ √h * ‖D * Cᵀ‖ * (√h * ‖e * Cᵀ‖) := by
    rw [sqrt_mul_mul_sqrt_mul hh.le]
    exact mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) hh.le
  have T1 : ⟪D - h • (P₁ * (M * D)), e⟫ ≤ (1 + η) * ‖D‖ * ‖e‖ := by
    refine (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have n1 : ‖h • (P₁ * (M * D))‖ ≤ h * (μ * ‖D‖) := by
      rw [norm_smul, Real.norm_of_nonneg hh.le]
      exact mul_le_mul_of_nonneg_left
        ((norm_proj_mul_le hP₁ hP₁t _).trans (norm_mul_le_mul_norm hμ0 hμ D)) hh.le
    have := norm_sub_le D (h • (P₁ * (M * D)))
    rw [hη]; linarith
  have hYK : ‖YK - Y₁‖ ≤ ‖Λ‖ + y + h * ‖X₁ * (Cᵀ * C)‖ + (y + ‖X₁ - X₀‖) + ‖e‖ := by
    have n1 := norm_kstep_sub_le hQ₀ hQ₀t yQ hdiss hh eqK hX
    have n2 : ‖X₁ - X₁ * Q₀‖ ≤ ‖X₁ - Y₀‖ := by
      have e1 : X₁ - X₁ * Q₀ = X₁ - Y₀ - (X₁ - Y₀) * Q₀ := by rw [Matrix.sub_mul, yQ]; abel
      rw [e1]; exact norm_sub_mul_proj_le hQ₀ hQ₀t _
    have e2 : YK - Y₁ = YK - X₁ * Q₀ - (X₁ - X₁ * Q₀) - e := by rw [he]; abel
    have n3 := norm_sub_le (YK - X₁ * Q₀ - (X₁ - X₁ * Q₀)) e
    have n4 := norm_sub_le (YK - X₁ * Q₀) (X₁ - X₁ * Q₀)
    rw [e2]; linarith
  have T2 : h * ⟪W - P₁ * W, e⟫ ≤
      η * ‖e‖ * (‖Λ‖ + y + h * ‖X₁ * (Cᵀ * C)‖ + (y + ‖X₁ - X₀‖) + ‖e‖) := by
    have n0 : ‖W‖ ≤ μ * ‖YK - Y₁‖ := by rw [hW]; exact norm_mul_le_mul_norm hμ0 hμ (YK - Y₁)
    have n1 := (norm_sub_proj_mul_le hP₁ hP₁t W).trans n0
    have n2 := (real_inner_le_norm (W - P₁ * W) e).trans
      (mul_le_mul_of_nonneg_right (n1.trans (mul_le_mul_of_nonneg_left hYK hμ0)) (norm_nonneg e))
    have := mul_le_mul_of_nonneg_left n2 hh.le
    rw [hη]; linarith
  have heh : √h * ‖(YL - P₀ * X₁) * Cᵀ‖ ≤ (y + η * (y + ‖X₁ - X₀‖)) / 2 := by
    have n1 := sqrt_mul_norm_lstep_sub_le hP₀ hP₀t yP lEq lP hdiss hμ0 hμ hh hX
    have n2 : ‖X₁ - P₀ * X₁‖ ≤ ‖X₁ - Y₀‖ := by
      have e1 : X₁ - P₀ * X₁ = X₁ - Y₀ - P₀ * (X₁ - Y₀) := by rw [Matrix.mul_sub, yP]; abel
      rw [e1]; exact norm_sub_proj_mul_le hP₀ hP₀t _
    have n3 := mul_le_mul_of_nonneg_left (n2.trans hXY) hη0
    rw [← hη] at n1
    linarith
  have T0 : ⟪Y₀ - X₀ - δ, e⟫ ≤ y * ‖e‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hyδ (norm_nonneg e))
  have hMe := mul_nonpos_of_nonneg_of_nonpos hh.le (inner_mul_self_nonpos hdiss e)
  have hmain : ‖e‖ ^ 2 + (√h * ‖e * Cᵀ‖) ^ 2 ≤ y * ‖e‖ + (1 + η) * ‖D‖ * ‖e‖ +
      √h * ‖D * Cᵀ‖ * (√h * ‖e * Cᵀ‖) +
      (2 * η * (√h * ‖(YL - P₀ * X₁) * Cᵀ‖) * (√h * ‖e * Cᵀ‖) +
        2 * η * (h * ‖X₁ * (Cᵀ * C)‖) * ‖e‖) +
      η * ‖e‖ * (‖Λ‖ + y + h * ‖X₁ * (Cᵀ * C)‖ + (y + ‖X₁ - X₀‖) + ‖e‖) := by
    rw [mul_pow, hs2]; linarith
  have hfin := step_scalar (norm_nonneg e) (mul_nonneg (Real.sqrt_nonneg h) (norm_nonneg _))
    (norm_nonneg D) (mul_nonneg (Real.sqrt_nonneg h) (norm_nonneg _)) hy0 (norm_nonneg Λ)
    (mul_nonneg hh.le (norm_nonneg _)) (norm_nonneg (X₁ - X₀)) hη0 (by rw [hη]; exact hhμ)
    (mul_nonneg (Real.sqrt_nonneg h) (norm_nonneg _)) rfl rfl heh hD' hmain
  rw [mul_pow, hs2] at hfin
  have hmin : ‖Λ‖ ≤ min ‖Y₀‖ (√h * ‖(Y₀ - Z) * Cᵀ‖ / 2 + h * ‖Z * (Cᵀ * C)‖) :=
    le_min hΛ1 (hΛ2 Z)
  have := mul_le_mul_of_nonneg_left hmin hη0
  rw [← hη, ← hy]
  linarith

end Lemmas

end ImplicitBUGStiffLemmas

open ImplicitBUGStiffLemmas

section Step

variable {m n k k₁ k₂ : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k₁] [Fintype k₂]
  [DecidableEq m] [DecidableEq n] [DecidableEq k₁] [DecidableEq k₂] {r : ℕ}
  {M : Matrix m m ℝ} {C : Matrix k n ℝ} {ε ϑ t₁ h μ : ℝ}
  {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {K₁ : Matrix m (Fin r) ℝ} {L₁ : Matrix n (Fin r) ℝ} {U₁ : Matrix m k₁ ℝ} {V₁ : Matrix n k₂ ℝ}
  {S₁ : Matrix k₁ k₂ ℝ} {Y₁ X₀ X₁ δ : Matrix m n ℝ}

/-- **The step inequality for the Galerkin step, with a free comparison matrix.** Let
`F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ`, `h μ ≤ 1/2`, and let
`X₁ - h M X₁ + h X₁ CᵀC = X₀ + δ` (a backward Euler step of the full problem with defect `δ`).
For a step from `Y₀ = U₀ S₀ V₀ᵀ` with exact capture, new bases of any size (fixed rank or
augmented), any normal defect and any truncation tolerance, the result `Ŷ₁ = U₁ S₁ V₁ᵀ` of the
Galerkin step before truncation satisfies, for every matrix `Z`,

  `(1 - h μ) √(‖Ŷ₁ - X₁‖² + h ‖(Ŷ₁ - X₁) Cᵀ‖²) ≤ (1 + 6 h μ) (‖Y₀ - X₀‖ + ‖δ‖) +`
  `    h μ (min(‖Y₀‖, √h ‖(Y₀ - Z) Cᵀ‖ / 2 + h ‖Z CᵀC‖) + 6 h ‖X₁ CᵀC‖ + 3 ‖X₁ - X₀‖)`.

The matrix `C` enters only through stiff energies and through `‖X CᵀC‖`, `‖Z CᵀC‖`, and the
singular values of `S₀` do not enter. -/
theorem IsMatrixImplicitBUGStep.sqrt_sq_norm_galerkin_sub_add_le_of_sylvester
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) ε 0 ϑ
      t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hhμ : h * μ ≤ 1 / 2) (hX : X₁ - h • (M * X₁) + h • (X₁ * (Cᵀ * C)) = X₀ + δ)
    (Z : Matrix m n ℝ) :
    (1 - h * μ) * √(‖U₁ * S₁ * V₁ᵀ - X₁‖ ^ 2 + h * ‖(U₁ * S₁ * V₁ᵀ - X₁) * Cᵀ‖ ^ 2) ≤
      (1 + 6 * (h * μ)) * (‖U₀ * S₀ * V₀ᵀ - X₀‖ + ‖δ‖) +
        h * μ * (min ‖U₀ * S₀ * V₀ᵀ‖
          (√h * ‖(U₀ * S₀ * V₀ᵀ - Z) * Cᵀ‖ / 2 + h * ‖Z * (Cᵀ * C)‖) +
          6 * (h * ‖X₁ * (Cᵀ * C)‖) + 3 * ‖X₁ - X₀‖) := by
  have hP₀ : U₀ * U₀ᵀ * (U₀ * U₀ᵀ) = U₀ * U₀ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthU₀]
  have hP₁ : U₁ * U₁ᵀ * (U₁ * U₁ᵀ) = U₁ * U₁ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthU₁]
  have hQ₀ : V₀ * V₀ᵀ * (V₀ * V₀ᵀ) = V₀ * V₀ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthV₀]
  have hP₀t : (U₀ * U₀ᵀ)ᵀ = U₀ * U₀ᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hP₁t : (U₁ * U₁ᵀ)ᵀ = U₁ * U₁ᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hQ₀t : (V₀ * V₀ᵀ)ᵀ = V₀ * V₀ᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hQ₁t : (V₁ * V₁ᵀ)ᵀ = V₁ * V₁ᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have kEq : K₁ * V₀ᵀ = U₀ * S₀ * V₀ᵀ +
      h • ((M * (K₁ * V₀ᵀ) - K₁ * V₀ᵀ * (Cᵀ * C)) * (V₀ * V₀ᵀ)) := by
    have := congrArg (fun A => A * V₀ᵀ) hs.kstep
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc] at this
    simpa only [Matrix.mul_assoc] using this
  have kQ : K₁ * V₀ᵀ * (V₀ * V₀ᵀ) = K₁ * V₀ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthV₀]
  have kP : U₁ * U₁ᵀ * (K₁ * V₀ᵀ) = K₁ * V₀ᵀ := by
    have := norm_le_zero_iff.1 hs.kcap
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
    exact this.symm
  have yQ : U₀ * S₀ * V₀ᵀ * (V₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthV₀]
  have yP : U₀ * U₀ᵀ * (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthU₀]
  have lEq : U₀ * L₁ᵀ = U₀ * S₀ * V₀ᵀ +
      h • (U₀ * U₀ᵀ * (M * (U₀ * L₁ᵀ) - U₀ * L₁ᵀ * (Cᵀ * C))) := by
    have := congrArg (fun A => U₀ * Aᵀ) hs.lstep
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc] at this
    simpa only [Matrix.mul_assoc] using this
  have lP : U₀ * U₀ᵀ * (U₀ * L₁ᵀ) = U₀ * L₁ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthU₀]
  have lQ : U₀ * L₁ᵀ * (V₁ * V₁ᵀ) = U₀ * L₁ᵀ := by
    have := norm_le_zero_iff.1 hs.lcap
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  have sEq : U₁ * S₁ * V₁ᵀ = U₁ * U₁ᵀ * (U₀ * S₀ * V₀ᵀ +
      h • (M * (U₁ * S₁ * V₁ᵀ) - U₁ * S₁ * V₁ᵀ * (Cᵀ * C))) * (V₁ * V₁ᵀ) := by
    have := congrArg (fun A => U₁ * A * V₁ᵀ) hs.sstep
    simp only [Matrix.mul_assoc] at this
    simpa only [Matrix.mul_assoc] using this
  have sP : U₁ * U₁ᵀ * (U₁ * S₁ * V₁ᵀ) = U₁ * S₁ * V₁ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthU₁]
  have sQ : U₁ * S₁ * V₁ᵀ * (V₁ * V₁ᵀ) = U₁ * S₁ * V₁ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthV₁]
  exact sqrt_sq_norm_sub_add_le_of_projectors hP₀ hP₀t hP₁ hP₁t hQ₀ hQ₀t hQ₁t kEq kQ kP yQ yP lEq
    lP lQ sEq sP sQ hdiss hμ0 hμ hh hhμ hX Z

end Step

/-! ### Non-vacuity -/

namespace ImplicitBUGStiffLemmasExample

local notation "Mₑ" => (!![0, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Cₑ" lam => (!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)

/-- The Gram matrix of `C = (0, √lam)` is `diag(0, lam)`. -/
theorem transpose_mul_self_eq (lam : ℝ) (hlam : 0 ≤ lam) :
    (Cₑ lam)ᵀ * (Cₑ lam) = -!![0, 0; 0, -lam] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Real.mul_self_sqrt hlam]

/-- `M = diag(0, -1)` is dissipative. -/
theorem dotProduct_mulVec_nonpos (x : Fin 2 → ℝ) : x ⬝ᵥ Mₑ *ᵥ x ≤ 0 := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  nlinarith [mul_self_nonneg (x 1)]

/-- `M = diag(0, -1)` is bounded by `1`. -/
theorem dotProduct_mulVec_mulVec_le (x : Fin 2 → ℝ) : Mₑ *ᵥ x ⬝ᵥ Mₑ *ᵥ x ≤ 1 ^ 2 * (x ⬝ᵥ x) := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  nlinarith [mul_self_nonneg (x 0)]

/-- A step from `(3/5, 4/5)ᵀ (1, 0)` exists for the family `M = diag(0, -1)`, `C = (0, √lam)`. -/
theorem exists_isMatrixImplicitBUGStep {h lam : ℝ} (hh : 0 < h) (hlam : 0 ≤ lam) :
    ∃ (K₁ L₁ U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ) (S₁ : Matrix (Fin 1) (Fin 1) ℝ)
      (Y₁ : Matrix (Fin 2) (Fin 2) ℝ) (ε : ℝ),
      IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
        Mₑ * Z - Z * ((Cₑ lam)ᵀ * (Cₑ lam))) ε 0 0 0 h !![3 / 5; 4 / 5] 1 !![1; 0] K₁ L₁ U₁ V₁
        S₁ Y₁ := by
  obtain ⟨K₁, L₁, U₁, V₁, S₁, Y₁, ε, hs⟩ := StiffRowsExample.exists_isMatrixImplicitBUGStep
    (c := 1) (s := 0) hh.le hlam (by norm_num) 0
  have hF : (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
      !![0, 0; 0, -1] * Z + Z * !![0, 0; 0, -lam]) = fun _ Z =>
      Mₑ * Z - Z * ((Cₑ lam)ᵀ * (Cₑ lam)) := by
    funext _ Z
    rw [transpose_mul_self_eq lam hlam, Matrix.mul_neg, sub_neg_eq_add]
  rw [hF] at hs
  exact ⟨K₁, L₁, U₁, V₁, S₁, Y₁, ε, hs⟩

/-- The hypotheses of the step inequality hold for this family, for every stiffness `lam ≥ 0`
and `h ∈ (0, 1/2]`, with the zero reference and every comparison matrix. -/
example {h lam : ℝ} (hh : 0 < h) (hh1 : h ≤ 1 / 2) (hlam : 0 ≤ lam) :
    ∃ (U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ) (S₁ : Matrix (Fin 1) (Fin 1) ℝ),
      ∀ Z : Matrix (Fin 2) (Fin 2) ℝ,
        (1 - h * 1) * √(‖U₁ * S₁ * V₁ᵀ - 0‖ ^ 2 + h * ‖(U₁ * S₁ * V₁ᵀ - 0) * (Cₑ lam)ᵀ‖ ^ 2) ≤
          (1 + 6 * (h * 1)) *
            (‖(!![3 / 5; 4 / 5] : Matrix (Fin 2) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) *
              (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ - 0‖ + ‖(0 : Matrix (Fin 2) (Fin 2) ℝ)‖) +
            h * 1 * (min ‖(!![3 / 5; 4 / 5] : Matrix (Fin 2) (Fin 1) ℝ) *
                (1 : Matrix (Fin 1) (Fin 1) ℝ) * (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ‖
              (√h * ‖((!![3 / 5; 4 / 5] : Matrix (Fin 2) (Fin 1) ℝ) *
                (1 : Matrix (Fin 1) (Fin 1) ℝ) * (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ - Z) *
                  (Cₑ lam)ᵀ‖ / 2 + h * ‖Z * ((Cₑ lam)ᵀ * (Cₑ lam))‖) +
              6 * (h * ‖(0 : Matrix (Fin 2) (Fin 2) ℝ) * ((Cₑ lam)ᵀ * (Cₑ lam))‖) +
              3 * ‖(0 : Matrix (Fin 2) (Fin 2) ℝ) - 0‖) := by
  obtain ⟨K₁, L₁, U₁, V₁, S₁, Y₁, ε, hs⟩ := exists_isMatrixImplicitBUGStep hh hlam
  exact ⟨U₁, V₁, S₁, fun Z => hs.sqrt_sq_norm_galerkin_sub_add_le_of_sylvester
    dotProduct_mulVec_nonpos zero_le_one dotProduct_mulVec_mulVec_le hh (by simpa using hh1)
    (by simp) Z⟩

end ImplicitBUGStiffLemmasExample

end LeanDLRA
