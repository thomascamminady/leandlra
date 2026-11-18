import LeanDLRA.Research.ImplicitBUGStiffLocal

/-!
# The implicit BUG integrator for a semilinear problem with a stiff row operator

Let `F(Z) = G(Z) - Z CᵀC` with a nonlinear `G` and `C` arbitrary. This file compares one step of
the BUG integrator with backward Euler substeps with the backward Euler step `Ỹ` of the full
nonlinear problem from the same start value, `Ỹ - h G(Ỹ) + h Ỹ CᵀC = Y₀`, and sums the local errors
with the stability of the nonlinear backward Euler step.

## Main results

* `ImplicitBUGStiffSemilinear.one_sub_mul_norm_sub_le_of_backwardEuler`: two backward Euler steps
  of the full problem satisfy `(1 - h ℓ) ‖W - W'‖ ≤ ‖R - R'‖` if `G` is one-sided Lipschitz with
  constant `ℓ` at the pair.
* `ImplicitBUGStiffSemilinear.norm_sub_le_of_backwardEuler_of_oneSided`: for every sequence `Y_j`,
  `‖Y_N - X_N‖ ≤ q^N ‖Y₀ - X₀‖ + ∑ q^(N-j) ‖δ_j‖ + ∑ q^(N-1-j) ‖Y_{j+1} - W_j‖`, `q = (1 - h ℓ)⁻¹`,
  with `W_j` the backward Euler step of the full problem from `Y_j`.
* `ImplicitBUGStiffSemilinear.one_sub_mul_sqrt_sq_norm_sub_backwardEuler_add_le_of_defect`: the
  local error in the energy norm is bounded by the normal part of the K-step and by the defect of
  any comparison matrix of the Galerkin space in the linear stiff equation with frozen `G`.
* `IsMatrixImplicitBUGStep.energy_norm_galerkin_sub_backwardEuler_le_of_semilinear`: for a step
  of the matrix integrator,
  `(1 - h ℓ) √(‖Ŷ₁ - Ỹ‖² + h ‖(Ŷ₁ - Ỹ) Cᵀ‖²) ≤ h (‖G(Ŷ₁) - G(Y_K)‖ + ‖G(Ŷ₁) - G(Y_L)‖ + 2 ε + σ)`,
  `σ = ‖h (1 - P₀) G(Y_L) Q₁ CᵀC‖`; no constant depends on `C` or on the singular values.
* `IsMatrixImplicitBUGStep.energy_norm_galerkin_sub_backwardEuler_le_of_mul`:
  if `G(Y_L) = W Y_L` with `W` bounded by `ω`, then `σ ≤ ω ‖h Y_L CᵀC‖`.
* `ImplicitBUGStiffSemilinear.norm_implicitBUG_run_sub_le_of_semilinear`: the run bound with these
  local errors.

## Implementation notes

The Galerkin step `Ŷ₁` solves the linear stiff equation `Y + h Y CᵀC = P₁ (Y₀ + h G(Ŷ₁))` in the
row space of `Q₁` in the Galerkin sense. With `τ + h τ CᵀC = ρ` for the residual `ρ` of `Ŷ₁` in the
equation of the full problem, `⟪ρ, τ⟫` is the square of the energy norm of `τ`; the part of `ρ`
outside the new column space is the normal part of the K-step, and the part inside is orthogonal
to the Galerkin space, so that it can be tested with `τ` minus any matrix of this space.

## References

* [CerutiLubich2022] for the BUG integrator; backward Euler substeps as in arXiv 2610.18419.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius
open Matrix Finset

namespace LeanDLRA

open ImplicitBUGStiffLemmas ImplicitBUGStiffLocal

namespace ImplicitBUGStiffSemilinear

section Lemmas

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

/-- Right multiplication by a Gram matrix in the Frobenius inner product. -/
theorem inner_mul_gram (C : Matrix k n ℝ) (X Z : Matrix m n ℝ) :
    ⟪X * (Cᵀ * C), Z⟫ = ⟪X * Cᵀ, Z * Cᵀ⟫ := by
  rw [← Matrix.mul_assoc, Frobenius.inner_mul_right]

/-- The bilinear form `⟪X + h X CᵀC, Z⟫` is symmetric. -/
theorem inner_add_smul_mul_gram_comm (C : Matrix k n ℝ) (h : ℝ) (X Z : Matrix m n ℝ) :
    ⟪X + h • (X * (Cᵀ * C)), Z⟫ = ⟪X, Z + h • (Z * (Cᵀ * C))⟫ := by
  rw [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_mul_gram, real_inner_comm (Z * (Cᵀ * C)) X, inner_mul_gram,
    real_inner_comm (X * Cᵀ) (Z * Cᵀ)]

/-- The bilinear form `⟪X + h X CᵀC, X⟫` is the square of the energy norm. -/
theorem inner_add_smul_mul_gram_self (C : Matrix k n ℝ) (h : ℝ) (X : Matrix m n ℝ) :
    ⟪X + h • (X * (Cᵀ * C)), X⟫ = ‖X‖ ^ 2 + h * ‖X * Cᵀ‖ ^ 2 := by
  rw [inner_add_left, real_inner_smul_left, inner_mul_gram, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]

/-- The Cauchy–Schwarz inequality for the bilinear form `⟪X + h X CᵀC, Z⟫`. -/
theorem inner_add_smul_mul_gram_le (C : Matrix k n ℝ) {h : ℝ} (hh : 0 ≤ h)
    (X Z : Matrix m n ℝ) :
    ⟪X + h • (X * (Cᵀ * C)), Z⟫ ≤
      √(‖X‖ ^ 2 + h * ‖X * Cᵀ‖ ^ 2) * √(‖Z‖ ^ 2 + h * ‖Z * Cᵀ‖ ^ 2) := by
  rw [inner_add_left, real_inner_smul_left, inner_mul_gram,
    ← Real.sqrt_mul (add_nonneg (sq_nonneg _) (mul_nonneg hh (sq_nonneg _)))]
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  have h1 := abs_real_inner_le_norm X Z
  have h2 := abs_real_inner_le_norm (X * Cᵀ) (Z * Cᵀ)
  have h3 : |⟪X, Z⟫ + h * ⟪X * Cᵀ, Z * Cᵀ⟫| ≤ ‖X‖ * ‖Z‖ + h * (‖X * Cᵀ‖ * ‖Z * Cᵀ‖) := by
    refine (abs_add_le _ _).trans (add_le_add h1 ?_)
    rw [abs_mul, abs_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left h2 hh
  have h4 : (⟪X, Z⟫ + h * ⟪X * Cᵀ, Z * Cᵀ⟫) ^ 2 ≤
      (‖X‖ * ‖Z‖ + h * (‖X * Cᵀ‖ * ‖Z * Cᵀ‖)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  have h5 : (‖X‖ ^ 2 + h * ‖X * Cᵀ‖ ^ 2) * (‖Z‖ ^ 2 + h * ‖Z * Cᵀ‖ ^ 2) -
      (‖X‖ * ‖Z‖ + h * (‖X * Cᵀ‖ * ‖Z * Cᵀ‖)) ^ 2 =
      h * (‖X‖ * ‖Z * Cᵀ‖ - ‖X * Cᵀ‖ * ‖Z‖) ^ 2 := by ring
  have h6 := mul_nonneg hh (sq_nonneg (‖X‖ * ‖Z * Cᵀ‖ - ‖X * Cᵀ‖ * ‖Z‖))
  linarith

/-- The Frobenius norm is bounded by the energy norm. -/
theorem norm_le_sqrt_sq_norm_add (C : Matrix k n ℝ) {h : ℝ} (hh : 0 ≤ h) (X : Matrix m n ℝ) :
    ‖X‖ ≤ √(‖X‖ ^ 2 + h * ‖X * Cᵀ‖ ^ 2) :=
  Real.le_sqrt_of_sq_le (by
    have : 0 ≤ h * ‖X * Cᵀ‖ ^ 2 := mul_nonneg hh (sq_nonneg _)
    linarith)

/-- If `c a² ≤ b a` with `a, b ≥ 0`, then `c a ≤ b`. -/
theorem mul_le_of_mul_sq_le_mul {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : c * a ^ 2 ≤ b * a) : c * a ≤ b := by
  by_contra hc
  rw [not_le] at hc
  have hpos : 0 < a := by
    rcases ha.eq_or_lt with h0 | h0
    · rw [← h0, mul_zero] at hc
      linarith
    · exact h0
  nlinarith [mul_lt_mul_of_pos_right hc hpos]

variable {G : Matrix m n ℝ → Matrix m n ℝ} {C : Matrix k n ℝ} {h ℓ : ℝ}

/-- **Stability of the nonlinear backward Euler step of the full problem.** If
`W - h G(W) + h W CᵀC = R`, `W' - h G(W') + h W' CᵀC = R'` and `G` is one-sided Lipschitz with
constant `ℓ` at the pair `W`, `W'`, then `(1 - h ℓ) ‖W - W'‖ ≤ ‖R - R'‖`. The matrix `C` does not
enter. -/
theorem one_sub_mul_norm_sub_le_of_backwardEuler (hh : 0 ≤ h) {W W' R R' : Matrix m n ℝ}
    (hos : ⟪G W - G W', W - W'⟫ ≤ ℓ * ‖W - W'‖ ^ 2)
    (hW : W - h • G W + h • (W * (Cᵀ * C)) = R)
    (hW' : W' - h • G W' + h • (W' * (Cᵀ * C)) = R') :
    (1 - h * ℓ) * ‖W - W'‖ ≤ ‖R - R'‖ := by
  have e : R - R' = (W - W') + h • ((W - W') * (Cᵀ * C)) - h • (G W - G W') := by
    rw [← hW, ← hW']
    simp only [Matrix.sub_mul, smul_sub]
    abel
  have h1 : ⟪R - R', W - W'⟫ = ‖W - W'‖ ^ 2 + h * ‖(W - W') * Cᵀ‖ ^ 2 -
      h * ⟪G W - G W', W - W'⟫ := by
    rw [e, inner_sub_left, inner_add_smul_mul_gram_self, real_inner_smul_left]
  have h2 := real_inner_le_norm (R - R') (W - W')
  have h3 := mul_le_mul_of_nonneg_left hos hh
  have h4 : 0 ≤ h * ‖(W - W') * Cᵀ‖ ^ 2 := mul_nonneg hh (sq_nonneg _)
  exact mul_le_of_mul_sq_le_mul (norm_nonneg _) (norm_nonneg _) (by linarith)

/-- **Local errors of any sequence against nonlinear backward Euler.** Let
`X_{j+1} - h G(X_{j+1}) + h X_{j+1} CᵀC = X_j + δ_j`, let `W_j` be the backward Euler step of the
full problem from `Y_j`, and let `G` be one-sided Lipschitz with constant `ℓ`, `h ℓ < 1`, at the
pairs `W_j`, `X_{j+1}`. Then, with `q = (1 - h ℓ)⁻¹`,

  `‖Y_N - X_N‖ ≤ q^N ‖Y₀ - X₀‖ + ∑_{j<N} q^(N-j) ‖δ_j‖ + ∑_{j<N} q^(N-1-j) ‖Y_{j+1} - W_j‖`.

For `ℓ < 0` the weights decay. -/
theorem norm_sub_le_of_backwardEuler_of_oneSided {N : ℕ} {Y W X δ : ℕ → Matrix m n ℝ}
    (hh : 0 ≤ h) (hhℓ : h * ℓ < 1)
    (hos : ∀ j < N, ⟪G (W j) - G (X (j + 1)), W j - X (j + 1)⟫ ≤ ℓ * ‖W j - X (j + 1)‖ ^ 2)
    (hW : ∀ j < N, W j - h • G (W j) + h • (W j * (Cᵀ * C)) = Y j)
    (hX : ∀ j < N, X (j + 1) - h • G (X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j + δ j) :
    ‖Y N - X N‖ ≤ (1 - h * ℓ)⁻¹ ^ N * ‖Y 0 - X 0‖ +
      ∑ j ∈ range N, (1 - h * ℓ)⁻¹ ^ (N - j) * ‖δ j‖ +
      ∑ j ∈ range N, (1 - h * ℓ)⁻¹ ^ (N - 1 - j) * ‖Y (j + 1) - W j‖ := by
  have hpos : 0 < 1 - h * ℓ := by linarith
  obtain ⟨q, hq⟩ : ∃ q, q = (1 - h * ℓ)⁻¹ := ⟨_, rfl⟩
  rw [← hq]
  have hq0 : 0 ≤ q := by rw [hq]; exact (inv_pos.2 hpos).le
  have hq1 : q * (1 - h * ℓ) = 1 := by rw [hq]; exact inv_mul_cancel₀ hpos.ne'
  induction N with
  | zero => simp
  | succ N ih =>
    have ih' := ih (fun j hj => hos j (Nat.lt_succ_of_lt hj))
      (fun j hj => hW j (Nat.lt_succ_of_lt hj)) fun j hj => hX j (Nat.lt_succ_of_lt hj)
    have n1 := one_sub_mul_norm_sub_le_of_backwardEuler hh (hos N (Nat.lt_succ_self N))
      (hW N (Nat.lt_succ_self N)) (hX N (Nat.lt_succ_self N))
    have n1' : ‖W N - X (N + 1)‖ ≤ q * ‖Y N - (X N + δ N)‖ := by
      calc ‖W N - X (N + 1)‖ = q * ((1 - h * ℓ) * ‖W N - X (N + 1)‖) := by
            rw [← mul_assoc, hq1, one_mul]
        _ ≤ q * ‖Y N - (X N + δ N)‖ := mul_le_mul_of_nonneg_left n1 hq0
    have n2 : ‖Y N - (X N + δ N)‖ ≤ ‖Y N - X N‖ + ‖δ N‖ := by
      rw [← sub_sub]; exact norm_sub_le _ _
    have e3 : Y (N + 1) - X (N + 1) = Y (N + 1) - W N + (W N - X (N + 1)) := by abel
    have n3 := norm_add_le (Y (N + 1) - W N) (W N - X (N + 1))
    rw [← e3] at n3
    have e1 : ∀ j ∈ range N, q ^ (N + 1 - j) * ‖δ j‖ = q * (q ^ (N - j) * ‖δ j‖) := fun j hj => by
      have : N + 1 - j = N - j + 1 := by have := Finset.mem_range.1 hj; omega
      rw [this, pow_succ]; ring
    have e2 : ∀ j ∈ range N, q ^ (N + 1 - 1 - j) * ‖Y (j + 1) - W j‖ =
        q * (q ^ (N - 1 - j) * ‖Y (j + 1) - W j‖) := fun j hj => by
      have : N + 1 - 1 - j = N - 1 - j + 1 := by have := Finset.mem_range.1 hj; omega
      rw [this, pow_succ]; ring
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_congr rfl e1,
      Finset.sum_congr rfl e2, ← Finset.mul_sum, ← Finset.mul_sum, pow_succ]
    have e4 : N + 1 - N = 1 := by omega
    have e5 : N + 1 - 1 - N = 0 := by omega
    rw [e4, e5, pow_one, pow_zero, one_mul]
    have n4 := mul_le_mul_of_nonneg_left ih' hq0
    have n5 := mul_le_mul_of_nonneg_left n2 hq0
    linarith

/-- **Run bound with the factor `(1 - h ℓ)^{-N}`** for `ℓ ≥ 0`: in the setting of
`norm_sub_le_of_backwardEuler_of_oneSided`,

  `‖Y_N - X_N‖ ≤ (1 - h ℓ)^{-N} (‖Y₀ - X₀‖ + ∑_{j<N} (‖δ_j‖ + ‖Y_{j+1} - W_j‖))`. -/
theorem norm_sub_le_inv_pow_mul_of_backwardEuler_of_oneSided {N : ℕ}
    {Y W X δ : ℕ → Matrix m n ℝ} (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ) (hhℓ : h * ℓ < 1)
    (hos : ∀ j < N, ⟪G (W j) - G (X (j + 1)), W j - X (j + 1)⟫ ≤ ℓ * ‖W j - X (j + 1)‖ ^ 2)
    (hW : ∀ j < N, W j - h • G (W j) + h • (W j * (Cᵀ * C)) = Y j)
    (hX : ∀ j < N, X (j + 1) - h • G (X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j + δ j) :
    ‖Y N - X N‖ ≤ (1 - h * ℓ)⁻¹ ^ N *
      (‖Y 0 - X 0‖ + ∑ j ∈ range N, (‖δ j‖ + ‖Y (j + 1) - W j‖)) := by
  have hpos : 0 < 1 - h * ℓ := by linarith
  have hq1 : 1 ≤ (1 - h * ℓ)⁻¹ :=
    (one_le_inv₀ hpos).2 (by have := mul_nonneg hh hℓ; linarith)
  refine (norm_sub_le_of_backwardEuler_of_oneSided hh hhℓ hos hW hX).trans ?_
  rw [mul_add, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
  refine add_le_add le_rfl (Finset.sum_le_sum fun j _ => ?_)
  rw [mul_add]
  exact add_le_add
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq1 (Nat.sub_le _ _)) (norm_nonneg _))
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq1 ((Nat.sub_le _ _).trans (Nat.sub_le _ _)))
      (norm_nonneg _))

variable {P₀ P₁ : Matrix m m ℝ} {Q₀ Q₁ : Matrix n n ℝ} {Y₀ YK YL Y₁ Yt : Matrix m n ℝ}

/-- **The local error against nonlinear backward Euler and the defect of a comparison matrix.**
Let `F(Z) = G(Z) - Z CᵀC`, let `Y_K`, `Y₁` solve the K- and S-step equations in projector form
(exact capture, new projectors of any rank), and let `Ỹ - h G(Ỹ) + h Ỹ CᵀC = Y₀`, with `G` one-sided
Lipschitz with constant `ℓ ≥ 0` at the pair `Y₁`, `Ỹ`. Then for every matrix `Z₀ = P₁ Z₀ Q₁`

  `(1 - h ℓ) √(‖Y₁ - Ỹ‖² + h ‖(Y₁ - Ỹ) Cᵀ‖²) ≤`
  `    ‖h (1 - P₁) (G(Y₁) - G(Y_K) Q₀)‖ + ‖P₁ (Y₀ + h G(Y₁)) - Z₀ - h Z₀ CᵀC‖`.

The second term is the defect of `Z₀` in the linear stiff equation with the frozen value
`G(Y₁)`: the Galerkin step is quasi-optimal in the energy norm. -/
theorem one_sub_mul_sqrt_sq_norm_sub_backwardEuler_add_le_of_defect (hP₁t : P₁ᵀ = P₁)
    (hQ₁t : Q₁ᵀ = Q₁)
    (kEq : YK = Y₀ + h • ((G YK - YK * (Cᵀ * C)) * Q₀)) (kP : P₁ * YK = YK)
    (sEq : Y₁ = P₁ * (Y₀ + h • (G Y₁ - Y₁ * (Cᵀ * C))) * Q₁) (sP : P₁ * Y₁ = Y₁)
    (sQ : Y₁ * Q₁ = Y₁) (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ)
    (hos : ⟪G Y₁ - G Yt, Y₁ - Yt⟫ ≤ ℓ * ‖Y₁ - Yt‖ ^ 2)
    (hYt : Yt - h • G Yt + h • (Yt * (Cᵀ * C)) = Y₀) {Z₀ : Matrix m n ℝ}
    (hZP : P₁ * Z₀ = Z₀) (hZQ : Z₀ * Q₁ = Z₀) :
    (1 - h * ℓ) * √(‖Y₁ - Yt‖ ^ 2 + h * ‖(Y₁ - Yt) * Cᵀ‖ ^ 2) ≤
      ‖h • (G Y₁ - G YK * Q₀ - P₁ * (G Y₁ - G YK * Q₀))‖ +
        ‖P₁ * (Y₀ + h • G Y₁) - Z₀ - h • (Z₀ * (Cᵀ * C))‖ := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = Y₁ + h • (Y₁ * (Cᵀ * C)) - h • G Y₁ - Y₀ := ⟨_, rfl⟩
  obtain ⟨τ, hτ0⟩ := exists_backwardEuler (M := (0 : Matrix m m ℝ)) (C := C) (h := h)
    (fun x => by simp) hh ρ
  have hτ : τ + h • (τ * (Cᵀ * C)) = ρ := by
    rwa [Matrix.zero_mul, smul_zero, sub_zero] at hτ0
  -- the start value outside the new column space
  have hY₀ : Y₀ = YK - h • (G YK * Q₀) + h • (YK * (Cᵀ * C) * Q₀) := by
    calc Y₀ = Y₀ + h • ((G YK - YK * (Cᵀ * C)) * Q₀) - h • ((G YK - YK * (Cᵀ * C)) * Q₀) := by
          abel
      _ = YK - h • ((G YK - YK * (Cᵀ * C)) * Q₀) := by rw [← kEq]
      _ = YK - h • (G YK * Q₀) + h • (YK * (Cᵀ * C) * Q₀) := by
          rw [Matrix.sub_mul, smul_sub]; abel
  have e1 : P₁ * ρ = Y₁ + h • (Y₁ * (Cᵀ * C)) - h • (P₁ * G Y₁) - P₁ * Y₀ := by
    rw [hρ]
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, sP]
  have e2 : P₁ * Y₀ = YK - h • (P₁ * (G YK * Q₀)) + h • (YK * (Cᵀ * C) * Q₀) := by
    conv_lhs => rw [hY₀]
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, kP]
  have hN : ρ - P₁ * ρ = -(h • (G Y₁ - G YK * Q₀ - P₁ * (G Y₁ - G YK * Q₀))) := by
    rw [e1, e2, hρ]
    conv_lhs => rw [hY₀]
    simp only [Matrix.mul_sub, smul_sub]
    abel
  -- Galerkin orthogonality
  have hG : P₁ * ρ * Q₁ = 0 := by
    have e : P₁ * ρ * Q₁ =
        P₁ * Y₁ * Q₁ - P₁ * (Y₀ + h • (G Y₁ - Y₁ * (Cᵀ * C))) * Q₁ := by
      rw [hρ]
      simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul,
        Matrix.mul_smul, Matrix.smul_mul, smul_sub]
      abel
    rw [e, ← sEq, sP, sQ, sub_self]
  have hXP : P₁ * (Y₁ - Z₀) = Y₁ - Z₀ := by rw [Matrix.mul_sub, sP, hZP]
  have hXQ : (Y₁ - Z₀) * Q₁ = Y₁ - Z₀ := by rw [Matrix.sub_mul, sQ, hZQ]
  have hort : ⟪ρ, Y₁ - Z₀⟫ = 0 := by
    have e : ⟪P₁ * ρ * Q₁, Y₁ - Z₀⟫ = ⟪ρ, Y₁ - Z₀⟫ := by
      rw [inner_mul_proj hQ₁t, inner_proj_mul hP₁t, hXQ, hXP]
    rw [← e, hG, inner_zero_left]
  -- the defect of the comparison matrix
  have eX : (Y₁ - Z₀ - P₁ * τ) + h • ((Y₁ - Z₀ - P₁ * τ) * (Cᵀ * C)) =
      P₁ * (Y₀ + h • G Y₁) - Z₀ - h • (Z₀ * (Cᵀ * C)) := by
    have e : (Y₁ - Z₀ - P₁ * τ) + h • ((Y₁ - Z₀ - P₁ * τ) * (Cᵀ * C)) =
        Y₁ + h • (Y₁ * (Cᵀ * C)) - (Z₀ + h • (Z₀ * (Cᵀ * C))) -
          P₁ * (τ + h • (τ * (Cᵀ * C))) := by
      simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_smul, smul_sub, Matrix.mul_assoc]
      abel
    rw [e, hτ, e1]
    simp only [Matrix.mul_add, Matrix.mul_smul]
    abel
  have h1 : ⟪P₁ * ρ, τ⟫ = -⟪τ, P₁ * (Y₀ + h • G Y₁) - Z₀ - h • (Z₀ * (Cᵀ * C))⟫ := by
    have e : P₁ * τ = (Y₁ - Z₀) - (Y₁ - Z₀ - P₁ * τ) := by abel
    rw [inner_proj_mul hP₁t, e, inner_sub_right, hort, zero_sub]
    conv_lhs => rw [← hτ]
    rw [inner_add_smul_mul_gram_comm, eX]
  have h2 : ⟪ρ, τ⟫ ≤ (‖h • (G Y₁ - G YK * Q₀ - P₁ * (G Y₁ - G YK * Q₀))‖ +
      ‖P₁ * (Y₀ + h • G Y₁) - Z₀ - h • (Z₀ * (Cᵀ * C))‖) * ‖τ‖ := by
    have e : ⟪ρ, τ⟫ = ⟪ρ - P₁ * ρ, τ⟫ + ⟪P₁ * ρ, τ⟫ := by rw [inner_sub_left]; ring
    have a1 := real_inner_le_norm (ρ - P₁ * ρ) τ
    rw [hN, norm_neg] at a1
    have a2 := abs_real_inner_le_norm τ (P₁ * (Y₀ + h • G Y₁) - Z₀ - h • (Z₀ * (Cᵀ * C)))
    have a3 := neg_abs_le ⟪τ, P₁ * (Y₀ + h • G Y₁) - Z₀ - h • (Z₀ * (Cᵀ * C))⟫
    rw [e, h1, hN]
    nlinarith
  -- the energy norm of `τ`
  have hτn := norm_le_sqrt_sq_norm_add C hh τ
  have hτs : √(‖τ‖ ^ 2 + h * ‖τ * Cᵀ‖ ^ 2) ^ 2 = ⟪ρ, τ⟫ := by
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (mul_nonneg hh (sq_nonneg _))),
      ← inner_add_smul_mul_gram_self, hτ]
  have hβ : 0 ≤ ‖h • (G Y₁ - G YK * Q₀ - P₁ * (G Y₁ - G YK * Q₀))‖ +
      ‖P₁ * (Y₀ + h • G Y₁) - Z₀ - h • (Z₀ * (Cᵀ * C))‖ :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hτb : √(‖τ‖ ^ 2 + h * ‖τ * Cᵀ‖ ^ 2) ≤
      ‖h • (G Y₁ - G YK * Q₀ - P₁ * (G Y₁ - G YK * Q₀))‖ +
        ‖P₁ * (Y₀ + h • G Y₁) - Z₀ - h • (Z₀ * (Cᵀ * C))‖ :=
    le_of_sq_le_mul hβ (by
      rw [hτs]
      exact h2.trans (mul_le_mul_of_nonneg_left hτn hβ))
  -- the error equation, tested with the error
  have hE : ρ = (Y₁ - Yt) + h • ((Y₁ - Yt) * (Cᵀ * C)) - h • (G Y₁ - G Yt) := by
    rw [hρ, ← hYt]
    simp only [Matrix.sub_mul, smul_sub]
    abel
  have t1 : ⟪ρ, Y₁ - Yt⟫ = ‖Y₁ - Yt‖ ^ 2 + h * ‖(Y₁ - Yt) * Cᵀ‖ ^ 2 -
      h * ⟪G Y₁ - G Yt, Y₁ - Yt⟫ := by
    conv_lhs => rw [hE]
    rw [inner_sub_left, inner_add_smul_mul_gram_self, real_inner_smul_left]
  have t2 : ⟪ρ, Y₁ - Yt⟫ ≤ √(‖τ‖ ^ 2 + h * ‖τ * Cᵀ‖ ^ 2) *
      √(‖Y₁ - Yt‖ ^ 2 + h * ‖(Y₁ - Yt) * Cᵀ‖ ^ 2) := by
    rw [← hτ]
    exact inner_add_smul_mul_gram_le C hh τ (Y₁ - Yt)
  have hs0 := Real.sqrt_nonneg (‖Y₁ - Yt‖ ^ 2 + h * ‖(Y₁ - Yt) * Cᵀ‖ ^ 2)
  have hs2 : √(‖Y₁ - Yt‖ ^ 2 + h * ‖(Y₁ - Yt) * Cᵀ‖ ^ 2) ^ 2 =
      ‖Y₁ - Yt‖ ^ 2 + h * ‖(Y₁ - Yt) * Cᵀ‖ ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (mul_nonneg hh (sq_nonneg _)))
  have t3 := mul_le_mul_of_nonneg_left hos hh
  have t4 := mul_le_mul_of_nonneg_right hτb hs0
  have t5 : 0 ≤ h * ℓ * (h * ‖(Y₁ - Yt) * Cᵀ‖ ^ 2) :=
    mul_nonneg (mul_nonneg hh hℓ) (mul_nonneg hh (sq_nonneg _))
  exact mul_le_of_mul_sq_le_mul hs0 hβ (by rw [hs2]; nlinarith)

/-- **The local error of a step in projector form.** In the setting of
`one_sub_mul_sqrt_sq_norm_sub_backwardEuler_add_le_of_defect`, with the L-step `Y_L` and bounds
`ε_K`, `ε_L` of the normal parts of `G` at `Y_K` and `Y_L`,

  `(1 - h ℓ) √(‖Y₁ - Ỹ‖² + h ‖(Y₁ - Ỹ) Cᵀ‖²) ≤ h (‖G(Y₁) - G(Y_K)‖ + ‖G(Y₁) - G(Y_L)‖ + ε_K + ε_L`
  `    + ‖h (1 - P₀) G(Y_L) Q₁ CᵀC‖)`.

The comparison matrix is `P₁ (Y_L + h (1 - P₀) G(Y_L) Q₁)`. -/
theorem one_sub_mul_sqrt_sq_norm_sub_backwardEuler_add_le_of_projectors {εK εL : ℝ}
    (hP₁ : P₁ * P₁ = P₁) (hP₁t : P₁ᵀ = P₁) (hQ₁ : Q₁ * Q₁ = Q₁) (hQ₁t : Q₁ᵀ = Q₁)
    (kEq : YK = Y₀ + h • ((G YK - YK * (Cᵀ * C)) * Q₀)) (kP : P₁ * YK = YK)
    (lEq : YL = Y₀ + h • (P₀ * (G YL - YL * (Cᵀ * C)))) (lP : P₀ * YL = YL)
    (lQ : YL * Q₁ = YL)
    (sEq : Y₁ = P₁ * (Y₀ + h • (G Y₁ - Y₁ * (Cᵀ * C))) * Q₁) (sP : P₁ * Y₁ = Y₁)
    (sQ : Y₁ * Q₁ = Y₁)
    (hεK : ‖G YK - P₁ * G YK - (G YK - P₁ * G YK) * Q₀‖ ≤ εK)
    (hεL : ‖G YL - P₀ * G YL - (G YL - P₀ * G YL) * Q₁‖ ≤ εL) (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ)
    (hos : ⟪G Y₁ - G Yt, Y₁ - Yt⟫ ≤ ℓ * ‖Y₁ - Yt‖ ^ 2)
    (hYt : Yt - h • G Yt + h • (Yt * (Cᵀ * C)) = Y₀) :
    (1 - h * ℓ) * √(‖Y₁ - Yt‖ ^ 2 + h * ‖(Y₁ - Yt) * Cᵀ‖ ^ 2) ≤
      h * (‖G Y₁ - G YK‖ + ‖G Y₁ - G YL‖ + εK + εL +
        ‖h • ((G YL - P₀ * G YL) * Q₁ * (Cᵀ * C))‖) := by
  obtain ⟨Z₀, hZ₀⟩ : ∃ Z₀, Z₀ = P₁ * (YL + h • ((G YL - P₀ * G YL) * Q₁)) := ⟨_, rfl⟩
  have hZP : P₁ * Z₀ = Z₀ := by rw [hZ₀, ← Matrix.mul_assoc, hP₁]
  have hZQ : Z₀ * Q₁ = Z₀ := by
    rw [hZ₀, Matrix.mul_assoc, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc _ Q₁ Q₁, hQ₁, lQ]
  have key := one_sub_mul_sqrt_sq_norm_sub_backwardEuler_add_le_of_defect hP₁t hQ₁t kEq kP sEq sP
    sQ hh hℓ hos hYt hZP hZQ
  -- the start value from the L-step
  have hY₀ : Y₀ = YL - h • (P₀ * G YL) + h • (YL * (Cᵀ * C)) := by
    have e : P₀ * (YL * (Cᵀ * C)) = YL * (Cᵀ * C) := by rw [← Matrix.mul_assoc, lP]
    calc Y₀ = Y₀ + h • (P₀ * (G YL - YL * (Cᵀ * C))) - h • (P₀ * (G YL - YL * (Cᵀ * C))) := by
          abel
      _ = YL - h • (P₀ * (G YL - YL * (Cᵀ * C))) := by rw [← lEq]
      _ = YL - h • (P₀ * G YL) + h • (YL * (Cᵀ * C)) := by
          rw [Matrix.mul_sub, smul_sub, e]; abel
  have eΔ : P₁ * (Y₀ + h • G Y₁) - Z₀ - h • (Z₀ * (Cᵀ * C)) =
      h • (P₁ * (G Y₁ - G YL)) +
        h • (P₁ * (G YL - P₀ * G YL - (G YL - P₀ * G YL) * Q₁)) -
        h • (P₁ * (h • ((G YL - P₀ * G YL) * Q₁ * (Cᵀ * C)))) := by
    rw [hZ₀]
    conv_lhs => rw [hY₀]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      smul_sub, smul_add, Matrix.mul_assoc]
    abel
  have eN : G Y₁ - G YK * Q₀ - P₁ * (G Y₁ - G YK * Q₀) =
      (G Y₁ - G YK - P₁ * (G Y₁ - G YK)) + (G YK - P₁ * G YK - (G YK - P₁ * G YK) * Q₀) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  have hh' : ‖h‖ = h := by rw [Real.norm_eq_abs, abs_of_nonneg hh]
  have n1 : ‖h • (G Y₁ - G YK * Q₀ - P₁ * (G Y₁ - G YK * Q₀))‖ ≤ h * (‖G Y₁ - G YK‖ + εK) := by
    rw [norm_smul, hh', eN]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
      (add_le_add (norm_sub_proj_mul_le hP₁ hP₁t _) hεK)) hh
  have n2 : ‖P₁ * (Y₀ + h • G Y₁) - Z₀ - h • (Z₀ * (Cᵀ * C))‖ ≤
      h * (‖G Y₁ - G YL‖ + εL + ‖h • ((G YL - P₀ * G YL) * Q₁ * (Cᵀ * C))‖) := by
    rw [eΔ, ← smul_add, ← smul_sub, norm_smul, hh']
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (norm_proj_mul_le hP₁ hP₁t _) ?_))
      (norm_proj_mul_le hP₁ hP₁t _))) hh
    exact (norm_proj_mul_le hP₁ hP₁t _).trans hεL
  linarith

/-- The normal part of `X - Y A` between the complements of two projectors does not contain
`Y A` if `Y` lies in the range of the left projector. -/
theorem one_sub_mul_sub_mul_one_sub [DecidableEq m] [DecidableEq n] (P : Matrix m m ℝ)
    (Q A : Matrix n n ℝ) {Y : Matrix m n ℝ} (hPY : P * Y = Y) (X : Matrix m n ℝ) :
    (1 - P) * (X - Y * A) * (1 - Q) = X - P * X - (X - P * X) * Q := by
  have e : P * (Y * A) = Y * A := by rw [← Matrix.mul_assoc, hPY]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, e]
  abel

/-- **The stiff term of the estimator for a left multiplication.** If `G(Y_L) = W Y_L` with `W`
bounded by `ω`, then `‖h (1 - P₀) G(Y_L) Q₁ CᵀC‖ ≤ ω ‖h Y_L CᵀC‖`. -/
theorem norm_smul_sub_proj_mul_mul_gram_le {W : Matrix m m ℝ} {ω : ℝ} (hP₀ : P₀ * P₀ = P₀)
    (hP₀t : P₀ᵀ = P₀) (hω0 : 0 ≤ ω) (hω : ∀ x : m → ℝ, W *ᵥ x ⬝ᵥ W *ᵥ x ≤ ω ^ 2 * (x ⬝ᵥ x))
    (lQ : YL * Q₁ = YL) :
    ‖h • ((W * YL - P₀ * (W * YL)) * Q₁ * (Cᵀ * C))‖ ≤ ω * ‖h • (YL * (Cᵀ * C))‖ := by
  have a1 : W * YL * Q₁ * (Cᵀ * C) = W * (YL * (Cᵀ * C)) := by
    rw [Matrix.mul_assoc W YL Q₁, lQ, Matrix.mul_assoc]
  have a2 : P₀ * (W * YL) * Q₁ * (Cᵀ * C) = P₀ * (W * (YL * (Cᵀ * C))) := by
    rw [Matrix.mul_assoc P₀, Matrix.mul_assoc P₀, a1]
  have e : h • ((W * YL - P₀ * (W * YL)) * Q₁ * (Cᵀ * C)) =
      W * (h • (YL * (Cᵀ * C))) - P₀ * (W * (h • (YL * (Cᵀ * C)))) := by
    rw [Matrix.sub_mul, Matrix.sub_mul, a1, a2, smul_sub]
    simp only [Matrix.mul_smul]
  rw [e]
  exact (norm_sub_proj_mul_le hP₀ hP₀t _).trans (norm_mul_le_mul_norm hω0 hω _)

end Lemmas

end ImplicitBUGStiffSemilinear

open ImplicitBUGStiffSemilinear

section Step

variable {m n k k₁ k₂ : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k₁] [Fintype k₂]
  [DecidableEq m] [DecidableEq n] [DecidableEq k₁] [DecidableEq k₂] {r : ℕ}
  {G : ℝ → Matrix m n ℝ → Matrix m n ℝ} {C : Matrix k n ℝ} {ε ϑ t₁ h ℓ : ℝ}
  {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {K₁ : Matrix m (Fin r) ℝ} {L₁ : Matrix n (Fin r) ℝ} {U₁ : Matrix m k₁ ℝ} {V₁ : Matrix n k₂ ℝ}
  {S₁ : Matrix k₁ k₂ ℝ} {Y₁ Yt : Matrix m n ℝ}

/-- **The local error of a step of the matrix integrator for a semilinear problem.** Let
`F(t, Z) = G(t, Z) - Z CᵀC` and let `Ỹ - h G(t₁, Ỹ) + h Ỹ CᵀC = U₀ S₀ V₀ᵀ` (the nonlinear backward
Euler step of the full problem from the start value of the step), with `G` one-sided Lipschitz
with constant `ℓ ≥ 0` at the pair `Ŷ₁`, `Ỹ`. For a step with exact capture, new bases of any size,
normal defect `ε` and any truncation tolerance, the result `Ŷ₁ = U₁ S₁ V₁ᵀ` of the Galerkin step
satisfies, with `Y_K = K₁ V₀ᵀ`, `Y_L = U₀ L₁ᵀ`, `P₀ = U₀ U₀ᵀ`, `Q₁ = V₁ V₁ᵀ`,

  `(1 - h ℓ) √(‖Ŷ₁ - Ỹ‖² + h ‖(Ŷ₁ - Ỹ) Cᵀ‖²) ≤`
  `    h (‖G(Ŷ₁) - G(Y_K)‖ + ‖G(Ŷ₁) - G(Y_L)‖ + 2 ε + ‖h (1 - P₀) G(Y_L) Q₁ CᵀC‖)`.

The right-hand side contains quantities of the step only; no constant depends on `C` or on the
singular values of `S₀`. -/
theorem IsMatrixImplicitBUGStep.energy_norm_galerkin_sub_backwardEuler_le_of_semilinear
    (hs : IsMatrixImplicitBUGStep (fun (t : ℝ) (Z : Matrix m n ℝ) => G t Z - Z * (Cᵀ * C)) ε 0 ϑ
      t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ)
    (hos : ⟪G t₁ (U₁ * S₁ * V₁ᵀ) - G t₁ Yt, U₁ * S₁ * V₁ᵀ - Yt⟫ ≤
      ℓ * ‖U₁ * S₁ * V₁ᵀ - Yt‖ ^ 2)
    (hYt : Yt - h • G t₁ Yt + h • (Yt * (Cᵀ * C)) = U₀ * S₀ * V₀ᵀ) :
    (1 - h * ℓ) * √(‖U₁ * S₁ * V₁ᵀ - Yt‖ ^ 2 + h * ‖(U₁ * S₁ * V₁ᵀ - Yt) * Cᵀ‖ ^ 2) ≤
      h * (‖G t₁ (U₁ * S₁ * V₁ᵀ) - G t₁ (K₁ * V₀ᵀ)‖ +
        ‖G t₁ (U₁ * S₁ * V₁ᵀ) - G t₁ (U₀ * L₁ᵀ)‖ + 2 * ε +
        ‖h • ((G t₁ (U₀ * L₁ᵀ) - U₀ * U₀ᵀ * G t₁ (U₀ * L₁ᵀ)) * (V₁ * V₁ᵀ) * (Cᵀ * C))‖) := by
  have hP₁ : U₁ * U₁ᵀ * (U₁ * U₁ᵀ) = U₁ * U₁ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthU₁]
  have hQ₁ : V₁ * V₁ᵀ * (V₁ * V₁ᵀ) = V₁ * V₁ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthV₁]
  have hP₁t : (U₁ * U₁ᵀ)ᵀ = U₁ * U₁ᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hQ₁t : (V₁ * V₁ᵀ)ᵀ = V₁ * V₁ᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have kEq : K₁ * V₀ᵀ = U₀ * S₀ * V₀ᵀ +
      h • ((G t₁ (K₁ * V₀ᵀ) - K₁ * V₀ᵀ * (Cᵀ * C)) * (V₀ * V₀ᵀ)) := by
    have := congrArg (fun A => A * V₀ᵀ) hs.kstep
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc] at this
    simpa only [Matrix.mul_assoc] using this
  have kP : U₁ * U₁ᵀ * (K₁ * V₀ᵀ) = K₁ * V₀ᵀ := by
    have := norm_le_zero_iff.1 hs.kcap
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
    exact this.symm
  have lEq : U₀ * L₁ᵀ = U₀ * S₀ * V₀ᵀ +
      h • (U₀ * U₀ᵀ * (G t₁ (U₀ * L₁ᵀ) - U₀ * L₁ᵀ * (Cᵀ * C))) := by
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
      h • (G t₁ (U₁ * S₁ * V₁ᵀ) - U₁ * S₁ * V₁ᵀ * (Cᵀ * C))) * (V₁ * V₁ᵀ) := by
    have := congrArg (fun A => U₁ * A * V₁ᵀ) hs.sstep
    simp only [Matrix.mul_assoc] at this
    simpa only [Matrix.mul_assoc] using this
  have sP : U₁ * U₁ᵀ * (U₁ * S₁ * V₁ᵀ) = U₁ * S₁ * V₁ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthU₁]
  have sQ : U₁ * S₁ * V₁ᵀ * (V₁ * V₁ᵀ) = U₁ * S₁ * V₁ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthV₁]
  have hεK : ‖(1 - U₁ * U₁ᵀ) * (G t₁ (K₁ * V₀ᵀ) - K₁ * V₀ᵀ * (Cᵀ * C)) * (1 - V₀ * V₀ᵀ)‖ ≤ ε :=
    hs.knormal
  rw [one_sub_mul_sub_mul_one_sub _ _ _ kP] at hεK
  have hεL : ‖(1 - U₀ * U₀ᵀ) * (G t₁ (U₀ * L₁ᵀ) - U₀ * L₁ᵀ * (Cᵀ * C)) * (1 - V₁ * V₁ᵀ)‖ ≤ ε :=
    hs.lnormal
  rw [one_sub_mul_sub_mul_one_sub _ _ _ lP] at hεL
  have key := one_sub_mul_sqrt_sq_norm_sub_backwardEuler_add_le_of_projectors (G := G t₁) hP₁
    hP₁t hQ₁ hQ₁t kEq kP lEq lP lQ sEq sP sQ hεK hεL hh hℓ hos hYt
  have e : ε + ε = 2 * ε := by ring
  rwa [add_assoc (‖G t₁ (U₁ * S₁ * V₁ᵀ) - G t₁ (K₁ * V₀ᵀ)‖ +
    ‖G t₁ (U₁ * S₁ * V₁ᵀ) - G t₁ (U₀ * L₁ᵀ)‖) ε ε, e] at key

/-- **The local error for a Lipschitz `G`.** In the setting of
`IsMatrixImplicitBUGStep.energy_norm_galerkin_sub_backwardEuler_le_of_semilinear`, if `G` is
Lipschitz with constant `L` and one-sided Lipschitz with constant `ℓ ≥ 0`, then

  `(1 - h ℓ) √(‖Ŷ₁ - Ỹ‖² + h ‖(Ŷ₁ - Ỹ) Cᵀ‖²) ≤`
  `    h (L (‖Ŷ₁ - Y_K‖ + ‖Ŷ₁ - Y_L‖) + 2 ε + ‖h (1 - P₀) G(Y_L) Q₁ CᵀC‖)`. -/
theorem IsMatrixImplicitBUGStep.energy_norm_galerkin_sub_backwardEuler_le_of_lipschitz {L : ℝ}
    (hs : IsMatrixImplicitBUGStep (fun (t : ℝ) (Z : Matrix m n ℝ) => G t Z - Z * (Cᵀ * C)) ε 0 ϑ
      t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ) (hL : IsLipschitzField G L)
    (hos : IsOneSidedLipschitzField G ℓ)
    (hYt : Yt - h • G t₁ Yt + h • (Yt * (Cᵀ * C)) = U₀ * S₀ * V₀ᵀ) :
    (1 - h * ℓ) * √(‖U₁ * S₁ * V₁ᵀ - Yt‖ ^ 2 + h * ‖(U₁ * S₁ * V₁ᵀ - Yt) * Cᵀ‖ ^ 2) ≤
      h * (L * (‖U₁ * S₁ * V₁ᵀ - K₁ * V₀ᵀ‖ + ‖U₁ * S₁ * V₁ᵀ - U₀ * L₁ᵀ‖) + 2 * ε +
        ‖h • ((G t₁ (U₀ * L₁ᵀ) - U₀ * U₀ᵀ * G t₁ (U₀ * L₁ᵀ)) * (V₁ * V₁ᵀ) * (Cᵀ * C))‖) := by
  refine (hs.energy_norm_galerkin_sub_backwardEuler_le_of_semilinear hh hℓ (hos t₁ _ _)
    hYt).trans (mul_le_mul_of_nonneg_left ?_ hh)
  have h1 := hL t₁ (U₁ * S₁ * V₁ᵀ) (K₁ * V₀ᵀ)
  have h2 := hL t₁ (U₁ * S₁ * V₁ᵀ) (U₀ * L₁ᵀ)
  linarith

/-- **The local error for a left multiplication.** In the setting of
`IsMatrixImplicitBUGStep.energy_norm_galerkin_sub_backwardEuler_le_of_semilinear`, if
`G(t₁, Y_L) = W Y_L` with a matrix `W` bounded by `ω` (as for `G(Z) = W(Z) Z`), then the stiff term
of the estimator is bounded by `ω ‖h Y_L CᵀC‖`, the stiff term of the L-step:

  `(1 - h ℓ) √(‖Ŷ₁ - Ỹ‖² + h ‖(Ŷ₁ - Ỹ) Cᵀ‖²) ≤`
  `    h (‖G(Ŷ₁) - G(Y_K)‖ + ‖G(Ŷ₁) - G(Y_L)‖ + 2 ε + ω ‖h Y_L CᵀC‖)`. -/
theorem IsMatrixImplicitBUGStep.energy_norm_galerkin_sub_backwardEuler_le_of_mul
    {W : Matrix m m ℝ} {ω : ℝ}
    (hs : IsMatrixImplicitBUGStep (fun (t : ℝ) (Z : Matrix m n ℝ) => G t Z - Z * (Cᵀ * C)) ε 0 ϑ
      t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ)
    (hos : ⟪G t₁ (U₁ * S₁ * V₁ᵀ) - G t₁ Yt, U₁ * S₁ * V₁ᵀ - Yt⟫ ≤
      ℓ * ‖U₁ * S₁ * V₁ᵀ - Yt‖ ^ 2)
    (hYt : Yt - h • G t₁ Yt + h • (Yt * (Cᵀ * C)) = U₀ * S₀ * V₀ᵀ)
    (hW : G t₁ (U₀ * L₁ᵀ) = W * (U₀ * L₁ᵀ)) (hω0 : 0 ≤ ω)
    (hω : ∀ x : m → ℝ, W *ᵥ x ⬝ᵥ W *ᵥ x ≤ ω ^ 2 * (x ⬝ᵥ x)) :
    (1 - h * ℓ) * √(‖U₁ * S₁ * V₁ᵀ - Yt‖ ^ 2 + h * ‖(U₁ * S₁ * V₁ᵀ - Yt) * Cᵀ‖ ^ 2) ≤
      h * (‖G t₁ (U₁ * S₁ * V₁ᵀ) - G t₁ (K₁ * V₀ᵀ)‖ +
        ‖G t₁ (U₁ * S₁ * V₁ᵀ) - G t₁ (U₀ * L₁ᵀ)‖ + 2 * ε +
        ω * ‖h • (U₀ * L₁ᵀ * (Cᵀ * C))‖) := by
  have hP₀ : U₀ * U₀ᵀ * (U₀ * U₀ᵀ) = U₀ * U₀ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthU₀]
  have hP₀t : (U₀ * U₀ᵀ)ᵀ = U₀ * U₀ᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have lQ : U₀ * L₁ᵀ * (V₁ * V₁ᵀ) = U₀ * L₁ᵀ := by
    have := norm_le_zero_iff.1 hs.lcap
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  have h1 := norm_smul_sub_proj_mul_mul_gram_le (C := C) (h := h) hP₀ hP₀t hω0 hω lQ
  rw [← hW] at h1
  refine (hs.energy_norm_galerkin_sub_backwardEuler_le_of_semilinear hh hℓ hos hYt).trans
    (mul_le_mul_of_nonneg_left ?_ hh)
  linarith

end Step

namespace ImplicitBUGStiffSemilinear

section Run

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n]
  {N : ℕ} {G : Matrix m n ℝ → Matrix m n ℝ} {C : Matrix k n ℝ} {h ℓ : ℝ} {ϑ b : ℕ → ℝ}
  {Y W X δ : ℕ → Matrix m n ℝ}

/-- **Run bound for the integrator with backward Euler substeps and a semilinear right-hand
side.** Let `F(Z) = G(Z) - Z CᵀC`, let `X_{j+1} - h G(X_{j+1}) + h X_{j+1} CᵀC = X_j + δ_j` be a
reference and `W_j` the nonlinear backward Euler step of the full problem from `Y_j`, with `G`
one-sided Lipschitz with constant `ℓ ≥ 0`, `h ℓ < 1`, at the pairs `W_j`, `X_{j+1}` and
`Ŷ_{j+1}`, `W_j`. Let step `j` of the integrator start from `Y_j` (in any factorisation, of any
rank), with exact capture by bases of any size, and let `Y_{j+1}` differ from the result
`Ŷ_{j+1} = U₁ S₁ V₁ᵀ` of the Galerkin step by at most `ϑ_j`. If the estimator of step `j` is
bounded by `(1 - h ℓ) b_j`,

  `h (‖G(Ŷ_{j+1}) - G(Y_K)‖ + ‖G(Ŷ_{j+1}) - G(Y_L)‖ + 2 ε + ‖h (1 - P₀) G(Y_L) Q₁ CᵀC‖)`
  `    ≤ (1 - h ℓ) b_j`,

then

  `‖Y_N - X_N‖ ≤ (1 - h ℓ)^{-N} (‖Y₀ - X₀‖ + ∑_{j<N} (‖δ_j‖ + ϑ_j + b_j))`. -/
theorem norm_implicitBUG_run_sub_le_of_semilinear
    (hstep : ∀ j < N, ∃ (r k₁ k₂ : ℕ) (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
      (V₀ : Matrix n (Fin r) ℝ) (K₁ : Matrix m (Fin r) ℝ) (L₁ : Matrix n (Fin r) ℝ)
      (U₁ : Matrix m (Fin k₁) ℝ) (V₁ : Matrix n (Fin k₂) ℝ) (S₁ : Matrix (Fin k₁) (Fin k₂) ℝ)
      (ε t : ℝ), Y j = U₀ * S₀ * V₀ᵀ ∧
        IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) => G Z - Z * (Cᵀ * C)) ε 0
          (ϑ j) t h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ (Y (j + 1)) ∧
        ⟪G (U₁ * S₁ * V₁ᵀ) - G (W j), U₁ * S₁ * V₁ᵀ - W j⟫ ≤ ℓ * ‖U₁ * S₁ * V₁ᵀ - W j‖ ^ 2 ∧
        h * (‖G (U₁ * S₁ * V₁ᵀ) - G (K₁ * V₀ᵀ)‖ + ‖G (U₁ * S₁ * V₁ᵀ) - G (U₀ * L₁ᵀ)‖ + 2 * ε +
          ‖h • ((G (U₀ * L₁ᵀ) - U₀ * U₀ᵀ * G (U₀ * L₁ᵀ)) * (V₁ * V₁ᵀ) * (Cᵀ * C))‖) ≤
          (1 - h * ℓ) * b j)
    (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ) (hhℓ : h * ℓ < 1)
    (hos : ∀ j < N, ⟪G (W j) - G (X (j + 1)), W j - X (j + 1)⟫ ≤ ℓ * ‖W j - X (j + 1)‖ ^ 2)
    (hW : ∀ j < N, W j - h • G (W j) + h • (W j * (Cᵀ * C)) = Y j)
    (hX : ∀ j < N, X (j + 1) - h • G (X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j + δ j) :
    ‖Y N - X N‖ ≤ (1 - h * ℓ)⁻¹ ^ N *
      (‖Y 0 - X 0‖ + ∑ j ∈ range N, (‖δ j‖ + ϑ j + b j)) := by
  have hpos : 0 < 1 - h * ℓ := by linarith
  refine (norm_sub_le_inv_pow_mul_of_backwardEuler_of_oneSided hh hℓ hhℓ hos hW hX).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl (Finset.sum_le_sum fun j hj => ?_))
      (pow_nonneg (inv_pos.2 hpos).le N))
  have hjN : j < N := Finset.mem_range.1 hj
  obtain ⟨r, k₁, k₂, U₀, S₀, V₀, K₁, L₁, U₁, V₁, S₁, ε, t, hY, hs, hos₁, hb⟩ := hstep j hjN
  have h1 := hs.energy_norm_galerkin_sub_backwardEuler_le_of_semilinear
    (G := fun _ => G) (Yt := W j) hh hℓ hos₁ (by rw [← hY]; exact hW j hjN)
  have h2 := norm_le_sqrt_sq_norm_add C hh (U₁ * S₁ * V₁ᵀ - W j)
  have h3 : ‖U₁ * S₁ * V₁ᵀ - W j‖ ≤ b j :=
    le_of_mul_le_mul_left ((mul_le_mul_of_nonneg_left h2 hpos.le).trans (h1.trans hb)) hpos
  have e : Y (j + 1) - W j = Y (j + 1) - U₁ * S₁ * V₁ᵀ + (U₁ * S₁ * V₁ᵀ - W j) := by abel
  have h4 := norm_add_le (Y (j + 1) - U₁ * S₁ * V₁ᵀ) (U₁ * S₁ * V₁ᵀ - W j)
  rw [← e] at h4
  have h5 := hs.trunc
  linarith

end Run

end ImplicitBUGStiffSemilinear

/-! ### Non-vacuity -/

namespace ImplicitBUGStiffSemilinearExample

open ImplicitBUGStiffLemmasExample

local notation "Cₙ" lam => (!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)

local notation "Eₙ" => (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "uₙ" => (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)

local notation "vₙ" => (!![0; 1] : Matrix (Fin 2) (Fin 1) ℝ)

local notation "Gₙ" => fun (Z : Matrix (Fin 2) (Fin 2) ℝ) => -(Z 0 1 ^ 2 • Z)

/-- The transpose of a column with two entries. -/
theorem transpose_col (a b : ℝ) : (!![a; b] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ = !![a, b] := by
  ext i j
  fin_cases i
  fin_cases j <;> rfl

/-- The cubic map `Z ↦ -Z₀₁² Z` is not linear. -/
theorem map_two_smul_ne : Gₙ ((2 : ℝ) • Eₙ) ≠ (2 : ℝ) • Gₙ Eₙ := fun h0 => by
  have e := congrFun (congrFun h0 0) 1
  norm_num at e

/-- The rows of the start value `s uₙ vₙᵀ` are not in the kernel of `CᵀC` for `lam > 0`, `s > 0`. -/
theorem start_mul_gram_ne_zero {lam s : ℝ} (hlam : 0 < lam) (hs : 0 < s) :
    uₙ * !![s] * vₙᵀ * ((Cₙ lam)ᵀ * (Cₙ lam)) ≠ 0 := by
  rw [transpose_mul_self_eq lam hlam.le, transpose_col]
  intro h0
  have e : (uₙ * !![s] * (!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ) * -!![0, 0; 0, -lam]) 0 1 =
      s * lam := by
    simp
  rw [h0, Matrix.zero_apply] at e
  have : 0 < s * lam := mul_pos hs hlam
  linarith

/-- The right-hand side `G(Z) - Z CᵀC` at the matrix unit `Eₙ`. -/
theorem field_apply (lam : ℝ) :
    Gₙ Eₙ - Eₙ * -!![0, 0; 0, -lam] = -((1 + lam) • Eₙ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  ring

/-- A step of the integrator for the cubic `G(Z) = -Z₀₁² Z` and `C = (0, √lam)` from the start
value `(1 + h + h lam) uₙ vₙᵀ`, whose rows are not in the kernel of `CᵀC`. -/
theorem isMatrixImplicitBUGStep {h lam : ℝ} (hlam : 0 ≤ lam) :
    IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
      Gₙ Z - Z * ((Cₙ lam)ᵀ * (Cₙ lam))) 0 0 0 0 h uₙ !![1 + h + h * lam] vₙ uₙ vₙ uₙ vₙ
      (1 : Matrix (Fin 1) (Fin 1) ℝ) Eₙ := by
  have hE : uₙ * vₙᵀ = Eₙ := by
    rw [transpose_col]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hF := field_apply lam
  have hu : uₙᵀ * uₙ = 1 := by
    rw [transpose_col]
    ext i j
    fin_cases i
    fin_cases j
    simp
  have hv : vₙᵀ * vₙ = 1 := by
    rw [transpose_col]
    ext i j
    fin_cases i
    fin_cases j
    simp
  have hS : (!![1 + h + h * lam] : Matrix (Fin 1) (Fin 1) ℝ)ᵀ = !![1 + h + h * lam] := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  have hEt : Eₙᵀ = !![0, 0; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hPu : (1 - uₙ * uₙᵀ) * Eₙ = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero, transpose_col]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hPv : Eₙ * (1 - vₙ * vₙᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, transpose_col]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  exact
    { orthU₀ := hu
      orthV₀ := hv
      kstep := by
        rw [transpose_mul_self_eq lam hlam, hE, hF]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
        ring
      lstep := by
        rw [transpose_mul_self_eq lam hlam, hE, hF, hS, Matrix.transpose_neg,
          Matrix.transpose_smul, hEt]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
        ring
      orthU₁ := hu
      orthV₁ := hv
      kcap := by rw [hE, hPu, norm_zero]
      lcap := by rw [hE, hPv, norm_zero]
      knormal := by
        rw [transpose_mul_self_eq lam hlam, hE, hF, Matrix.mul_neg, Matrix.mul_smul, hPu,
          smul_zero, neg_zero, Matrix.zero_mul, norm_zero]
      lnormal := by
        rw [transpose_mul_self_eq lam hlam, hE, hF, Matrix.mul_assoc, Matrix.neg_mul,
          Matrix.smul_mul, hPv, smul_zero, neg_zero, Matrix.mul_zero, norm_zero]
      sstep := by
        rw [transpose_mul_self_eq lam hlam, Matrix.mul_one, hE, hF, transpose_col, transpose_col]
        ext i j
        fin_cases i
        fin_cases j
        simp
        ring
      trunc := by rw [Matrix.mul_one, hE, sub_self, norm_zero] }

/-- The hypotheses of the local error bound hold for a cubic `G` and every stiffness `lam > 0`
and every `h > 0`, with a start value whose rows are not in the kernel of `CᵀC`; the matrix `Eₙ`
is the nonlinear backward Euler step of the full problem from the same start value. -/
example {h lam : ℝ} (hh : 0 < h) (hlam : 0 < lam) :
    uₙ * !![1 + h + h * lam] * vₙᵀ * ((Cₙ lam)ᵀ * (Cₙ lam)) ≠ 0 ∧
    Gₙ ((2 : ℝ) • Eₙ) ≠ (2 : ℝ) • Gₙ Eₙ ∧
    Eₙ - h • Gₙ Eₙ + h • (Eₙ * ((Cₙ lam)ᵀ * (Cₙ lam))) = uₙ * !![1 + h + h * lam] * vₙᵀ ∧
    (1 - h * 0) * √(‖uₙ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * vₙᵀ - Eₙ‖ ^ 2 +
        h * ‖(uₙ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * vₙᵀ - Eₙ) * (Cₙ lam)ᵀ‖ ^ 2) ≤
      h * (‖Gₙ (uₙ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * vₙᵀ) - Gₙ (uₙ * vₙᵀ)‖ +
        ‖Gₙ (uₙ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * vₙᵀ) - Gₙ (uₙ * vₙᵀ)‖ + 2 * 0 +
        ‖h • ((Gₙ (uₙ * vₙᵀ) - uₙ * uₙᵀ * Gₙ (uₙ * vₙᵀ)) * (vₙ * vₙᵀ) *
          ((Cₙ lam)ᵀ * (Cₙ lam)))‖) := by
  have hYt : Eₙ - h • Gₙ Eₙ + h • (Eₙ * ((Cₙ lam)ᵀ * (Cₙ lam))) =
      uₙ * !![1 + h + h * lam] * vₙᵀ := by
    rw [transpose_mul_self_eq lam hlam.le, transpose_col]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hE : uₙ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * vₙᵀ = Eₙ := by
    rw [Matrix.mul_one, transpose_col]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨start_mul_gram_ne_zero hlam (by positivity), map_two_smul_ne, hYt, ?_⟩
  exact (isMatrixImplicitBUGStep hlam.le).energy_norm_galerkin_sub_backwardEuler_le_of_semilinear
    (G := fun _ => Gₙ) (Yt := Eₙ) hh.le le_rfl
    (by rw [hE, sub_self, sub_self, inner_zero_left, norm_zero]; norm_num) hYt

end ImplicitBUGStiffSemilinearExample

end LeanDLRA
