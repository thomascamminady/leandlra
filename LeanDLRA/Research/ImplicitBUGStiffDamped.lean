import LeanDLRA.Research.ImplicitBUGStiffLocal

/-!
# A posteriori error bounds with damping for backward Euler of a stiff linear problem

Let `F(Z) = M Z - Z CᵀC` with `M` dissipative (`x ⬝ᵥ M x ≤ 0`, not necessarily normal) and `C`
arbitrary, and let `𝒫 Z = Z - h M Z + h Z CᵀC` be the operator of a backward Euler step, `R = 𝒫⁻¹`.
For any sequence `Y_j` with the residuals `ρ_j = Y_j - 𝒫 Y_{j+1}` and a backward Euler reference
`𝒫 X_{j+1} = X_j + δ_j` the error is exactly

  `Y_N - X_N = R^N (Y₀ - X₀) - ∑_{j<N} R^(N-j) (ρ_j + δ_j)`,

so each local residual is damped by the steps that follow it. The powers of `R` are bounded by the
powers of the two one-sided resolvents `(1 - h M)⁻¹` (from the left) and `(1 + h CᵀC)⁻¹` (from the
right), which are applied to factors of a low-rank matrix one side at a time. The resulting bound
holds for every sequence `Y_j`: no hypothesis on the integrator, the truncation or the tolerance
that produced it.

## Main results

* `ImplicitBUGStiffDamped.norm_le_norm_mul_inv_of_backwardEuler`,
  `norm_le_norm_inv_mul_of_backwardEuler`: `‖R ρ‖ ≤ ‖ρ (1 + h CᵀC)⁻¹‖` and
  `‖R ρ‖ ≤ ‖(1 - h M)⁻¹ ρ‖`.
* `norm_le_norm_mul_inv_pow_of_backwardEuler`, `norm_le_norm_inv_pow_mul_of_backwardEuler`:
  the same for `k` steps, `‖R^k ρ‖ ≤ ‖ρ (1 + h CᵀC)⁻¹ ^ k‖` and `‖R^k ρ‖ ≤ ‖(1 - h M)⁻¹ ^ k ρ‖`.
* `sub_eq_sub_sum_of_backwardEuler`: the exact damped representation of the error of any sequence,
  and `norm_sub_le_add_sum_of_backwardEuler_iterates` its norm form.
* `norm_sub_le_sum_min_add_sum_min_of_backwardEuler`: the run bound with splittings of the start
  error and of the residuals, and `norm_sub_le_min_add_sum_min_of_backwardEuler`: for any splitting
  `ρ_j + δ_j = ∑_a P_{j,a}`,
  `‖Y_N - X_N‖ ≤ min(‖(1 - h M)⁻¹ ^ N e₀‖, ‖e₀ (1 + h CᵀC)⁻¹ ^ N‖) +
  ∑_j ∑_a min(‖(1 - h M)⁻¹ ^ (N-j) P_{j,a}‖, ‖P_{j,a} (1 + h CᵀC)⁻¹ ^ (N-j)‖)`, `e₀ = Y₀ - X₀`.
* `norm_sub_le_min_add_sum_min_of_backwardEuler_residual`: the same with the residual and the
  defect as the two parts.

## Implementation notes

Powers of `R` are written as chains `W_{i+1} - h M W_{i+1} + h W_{i+1} CᵀC = W_i`, which exist and
are unique; the run bounds do not mention them. The bound from the right uses that
`(1 + h CᵀC)⁻¹` is symmetric positive semidefinite; for a right operator that is dissipative but
not symmetric the corresponding bound fails.

## References

* [CerutiLubich2022], [CerutiKuschLubich2022] for the BUG integrator, whose runs are the intended
  sequences `Y_j`; backward Euler substeps as in arXiv 2610.18419.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius
open Matrix Finset

namespace LeanDLRA

open ImplicitBUGStiffLemmas ImplicitBUGStiffLocal

namespace ImplicitBUGStiffDamped

variable {m n k p : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype p]
  {M : Matrix m m ℝ} {C : Matrix k n ℝ} {h : ℝ}

/-- The negative of a Gram matrix is dissipative. -/
theorem dotProduct_neg_gram_mulVec_nonpos (C : Matrix k n ℝ) (x : n → ℝ) :
    x ⬝ᵥ (-(Cᵀ * C)) *ᵥ x ≤ 0 := by
  rw [Matrix.neg_mulVec, dotProduct_neg, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, neg_nonpos]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg ((C *ᵥ x) i)

section Resolvent

variable [DecidableEq m] [DecidableEq n]

/-! ### The one-sided resolvents -/

/-- For a dissipative `M` and `h ≥ 0` the matrix `1 - h M` is invertible. -/
theorem isUnit_det_one_sub_smul (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 ≤ h) :
    IsUnit (1 - h • M).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ x : m → ℝ, (1 - h • M) *ᵥ x = 0 → x = 0 := by
    intro x hx
    have h1 : x ⬝ᵥ ((1 - h • M) *ᵥ x) = 0 := by rw [hx, dotProduct_zero]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul] at h1
    have h2 := mul_nonpos_of_nonneg_of_nonpos hh (hdiss x)
    have h3 : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
    exact dotProduct_self_eq_zero.1 (by linarith)
  intro x y hxy
  exact sub_eq_zero.1 (key (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self]))

/-- For `h ≥ 0` the matrix `1 + h CᵀC` is invertible. -/
theorem isUnit_det_one_add_smul_gram (C : Matrix k n ℝ) (hh : 0 ≤ h) :
    IsUnit (1 + h • (Cᵀ * C)).det := by
  have e : 1 + h • (Cᵀ * C) = 1 - h • (-(Cᵀ * C)) := by rw [smul_neg, sub_neg_eq_add]
  rw [e]
  exact isUnit_det_one_sub_smul (dotProduct_neg_gram_mulVec_nonpos C) hh

/-- The resolvent `(1 - h M)⁻¹` of a dissipative matrix has a nonnegative quadratic form on
matrices with any number of columns. -/
theorem inner_inv_one_sub_smul_mul_self_nonneg (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
    (hh : 0 ≤ h) (Z : Matrix m p ℝ) : 0 ≤ ⟪(1 - h • M)⁻¹ * Z, Z⟫ := by
  have hu := isUnit_det_one_sub_smul hdiss hh
  obtain ⟨V, hV⟩ : ∃ V, V = (1 - h • M)⁻¹ * Z := ⟨_, rfl⟩
  have e : Z = V - h • (M * V) :=
    calc Z = (1 - h • M) * ((1 - h • M)⁻¹ * Z) := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
      _ = V - h • (M * V) := by rw [← hV, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  have h1 : ⟪V, M * V⟫ ≤ 0 := by
    rw [real_inner_comm]
    exact inner_mul_self_nonpos hdiss V
  rw [← hV, e, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ‖V‖, mul_nonpos_of_nonneg_of_nonpos hh h1]

/-- The inverse of a matrix commutes with every matrix that commutes with it. -/
theorem commute_nonsing_inv {A B : Matrix n n ℝ} (hu : IsUnit A.det) (hc : Commute A B) :
    Commute A⁻¹ B := by
  have e : A⁻¹ * B = A⁻¹ * (B * A) * A⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have e2 : A⁻¹ * (B * A) * A⁻¹ = B * A⁻¹ := by
    rw [← hc.eq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  exact e.trans e2

end Resolvent

/-! ### Linearity, uniqueness and commuting factors of the backward Euler step -/

/-- The backward Euler step of a difference. -/
theorem backwardEuler_sub {A B R₁ R₂ : Matrix m n ℝ}
    (hA : A - h • (M * A) + h • (A * (Cᵀ * C)) = R₁)
    (hB : B - h • (M * B) + h • (B * (Cᵀ * C)) = R₂) :
    A - B - h • (M * (A - B)) + h • ((A - B) * (Cᵀ * C)) = R₁ - R₂ := by
  rw [← hA, ← hB]
  simp only [Matrix.mul_sub, Matrix.sub_mul, smul_sub]
  abel

/-- The backward Euler step of a finite sum. -/
theorem backwardEuler_sum {ι : Type*} (s : Finset ι) {A R : ι → Matrix m n ℝ}
    (hA : ∀ a ∈ s, A a - h • (M * A a) + h • (A a * (Cᵀ * C)) = R a) :
    ∑ a ∈ s, A a - h • (M * ∑ a ∈ s, A a) + h • ((∑ a ∈ s, A a) * (Cᵀ * C)) = ∑ a ∈ s, R a := by
  rw [Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl hA

/-- The backward Euler step of the full problem is unique. -/
theorem eq_of_backwardEuler_eq (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 ≤ h)
    {A B R : Matrix m n ℝ} (hA : A - h • (M * A) + h • (A * (Cᵀ * C)) = R)
    (hB : B - h • (M * B) + h • (B * (Cᵀ * C)) = R) : A = B := by
  have h0 := backwardEuler_sub hA hB
  rw [sub_self] at h0
  have := norm_le_of_backwardEuler hdiss hh h0
  rw [norm_zero] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-- Right multiplication by a matrix that commutes with `CᵀC` commutes with the backward Euler
step. -/
theorem backwardEuler_mul_right {W R : Matrix m n ℝ} {T : Matrix n n ℝ}
    (hT : Commute T (Cᵀ * C)) (heq : W - h • (M * W) + h • (W * (Cᵀ * C)) = R) :
    W * T - h • (M * (W * T)) + h • (W * T * (Cᵀ * C)) = R * T := by
  rw [← heq, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc M,
    Matrix.mul_assoc W T, hT.eq, Matrix.mul_assoc W (Cᵀ * C) T]

/-- Left multiplication by a matrix that commutes with `M` commutes with the backward Euler
step. -/
theorem backwardEuler_mul_left {W R : Matrix m n ℝ} {T : Matrix m m ℝ}
    (hT : Commute T M) (heq : W - h • (M * W) + h • (W * (Cᵀ * C)) = R) :
    T * W - h • (M * (T * W)) + h • (T * W * (Cᵀ * C)) = T * R := by
  rw [← heq, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
    ← Matrix.mul_assoc T M, hT.eq, Matrix.mul_assoc M T, Matrix.mul_assoc T W]

/-- Chains of backward Euler steps exist: `W₀ = R` and `W_{i+1} - h M W_{i+1} + h W_{i+1} CᵀC = W_i`
for all `i`. -/
theorem exists_backwardEuler_iterates (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 ≤ h)
    (C : Matrix k n ℝ) (R : Matrix m n ℝ) :
    ∃ W : ℕ → Matrix m n ℝ, W 0 = R ∧
      ∀ i, W (i + 1) - h • (M * W (i + 1)) + h • (W (i + 1) * (Cᵀ * C)) = W i := by
  choose f hf using fun R : Matrix m n ℝ => exists_backwardEuler (C := C) hdiss hh R
  refine ⟨fun i => f^[i] R, rfl, fun i => ?_⟩
  simp only [Function.iterate_succ_apply']
  exact hf _

/-! ### The exact damped representation -/

/-- **Exact damped representation of the error of any sequence.** Let `𝒫 Z = Z - h M Z + h Z CᵀC`
with `M` dissipative and `R = 𝒫⁻¹`. For any sequence `Y_j` and a reference with
`𝒫 X_{j+1} = X_j + δ_j`, let `E_i = R^i (Y₀ - X₀)` and `W_{j,i} = R^i (Y_j - 𝒫 Y_{j+1} + δ_j)`. Then

  `Y_N - X_N = E_N - ∑_{j<N} W_{j,N-j}`:

the residual of step `j` enters through `N - j` backward Euler steps. -/
theorem sub_eq_sub_sum_of_backwardEuler {N : ℕ} {Y X δ E : ℕ → Matrix m n ℝ}
    {W : ℕ → ℕ → Matrix m n ℝ} (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 ≤ h)
    (hX : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j + δ j)
    (hE0 : E 0 = Y 0 - X 0)
    (hE : ∀ i < N, E (i + 1) - h • (M * E (i + 1)) + h • (E (i + 1) * (Cᵀ * C)) = E i)
    (hW0 : ∀ j < N, W j 0 =
      Y j - (Y (j + 1) - h • (M * Y (j + 1)) + h • (Y (j + 1) * (Cᵀ * C))) + δ j)
    (hW : ∀ j < N, ∀ i < N - j,
      W j (i + 1) - h • (M * W j (i + 1)) + h • (W j (i + 1) * (Cᵀ * C)) = W j i) :
    Y N - X N = E N - ∑ j ∈ range N, W j (N - j) := by
  induction N with
  | zero => simp [hE0]
  | succ n ih =>
    have ih' := ih (fun j hj => hX j (Nat.lt_succ_of_lt hj))
      (fun i hi => hE i (Nat.lt_succ_of_lt hi)) (fun j hj => hW0 j (Nat.lt_succ_of_lt hj))
      fun j hj i hi => hW j (Nat.lt_succ_of_lt hj) i (by omega)
    have hS : ∑ j ∈ range (n + 1), W j (n + 1 - j) -
        h • (M * ∑ j ∈ range (n + 1), W j (n + 1 - j)) +
        h • ((∑ j ∈ range (n + 1), W j (n + 1 - j)) * (Cᵀ * C)) =
        ∑ j ∈ range (n + 1), W j (n - j) := by
      refine backwardEuler_sum _ fun j hj => ?_
      have hj' : j < n + 1 := Finset.mem_range.1 hj
      have e : n + 1 - j = n - j + 1 := by omega
      rw [e]
      exact hW j hj' (n - j) (by omega)
    have h1 := backwardEuler_sub (hE n (Nat.lt_succ_self n)) hS
    have h2 := backwardEuler_sub (R₁ := Y (n + 1) - h • (M * Y (n + 1)) +
      h • (Y (n + 1) * (Cᵀ * C))) rfl (hX n (Nat.lt_succ_self n))
    refine eq_of_backwardEuler_eq hdiss hh h2 ?_
    rw [h1, Finset.sum_range_succ, Nat.sub_self, hW0 n (Nat.lt_succ_self n)]
    have e3 : E n = Y n - X n + ∑ j ∈ range n, W j (n - j) := by rw [ih']; abel
    rw [e3]
    abel

/-- **The damped error bound in terms of the exact iterates**: with the notation of
`sub_eq_sub_sum_of_backwardEuler`, `‖Y_N - X_N‖ ≤ ‖R^N (Y₀ - X₀)‖ + ∑_{j<N} ‖R^(N-j) (ρ_j + δ_j)‖`,
`ρ_j = Y_j - 𝒫 Y_{j+1}`. Only the triangle inequality is used. -/
theorem norm_sub_le_add_sum_of_backwardEuler_iterates {N : ℕ} {Y X δ E : ℕ → Matrix m n ℝ}
    {W : ℕ → ℕ → Matrix m n ℝ} (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 ≤ h)
    (hX : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j + δ j)
    (hE0 : E 0 = Y 0 - X 0)
    (hE : ∀ i < N, E (i + 1) - h • (M * E (i + 1)) + h • (E (i + 1) * (Cᵀ * C)) = E i)
    (hW0 : ∀ j < N, W j 0 =
      Y j - (Y (j + 1) - h • (M * Y (j + 1)) + h • (Y (j + 1) * (Cᵀ * C))) + δ j)
    (hW : ∀ j < N, ∀ i < N - j,
      W j (i + 1) - h • (M * W j (i + 1)) + h • (W j (i + 1) * (Cᵀ * C)) = W j i) :
    ‖Y N - X N‖ ≤ ‖E N‖ + ∑ j ∈ range N, ‖W j (N - j)‖ := by
  rw [sub_eq_sub_sum_of_backwardEuler hdiss hh hX hE0 hE hW0 hW]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))

/-! ### Damping by the one-sided resolvents -/

section Right

variable [DecidableEq n]

/-- **A backward Euler step is bounded by the right resolvent**: if `W - h M W + h W CᵀC = R` with
`M` dissipative (not necessarily normal), then `‖W‖ ≤ ‖R (1 + h CᵀC)⁻¹‖`. -/
theorem norm_le_norm_mul_inv_of_backwardEuler (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
    (hh : 0 ≤ h) {W R : Matrix m n ℝ} (heq : W - h • (M * W) + h • (W * (Cᵀ * C)) = R) :
    ‖W‖ ≤ ‖R * (1 + h • (Cᵀ * C))⁻¹‖ := by
  have hu := isUnit_det_one_add_smul_gram C hh
  obtain ⟨V, hV⟩ : ∃ V, V = W * (1 + h • (Cᵀ * C))⁻¹ := ⟨_, rfl⟩
  have hW : V + h • (V * (Cᵀ * C)) = W :=
    calc V + h • (V * (Cᵀ * C)) = V * (1 + h • (Cᵀ * C)) := by
          rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
      _ = W := by rw [hV, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  have hR : R * (1 + h • (Cᵀ * C))⁻¹ = W - h • (M * V) := by
    have e : R = W * (1 + h • (Cᵀ * C)) - h • (M * W) := by
      rw [← heq, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
      abel
    rw [e, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_assoc, ← hV]
  have h1 : ⟪M * V, V * (Cᵀ * C)⟫ = ⟪M * (V * Cᵀ), V * Cᵀ⟫ := by
    rw [← Matrix.mul_assoc V, Frobenius.inner_mul_right', Matrix.mul_assoc]
  have h2 : ⟪M * V, W⟫ ≤ 0 := by
    rw [← hW, inner_add_right, real_inner_smul_right, h1]
    nlinarith [inner_mul_self_nonpos hdiss V, mul_nonpos_of_nonneg_of_nonpos hh
      (inner_mul_self_nonpos hdiss (V * Cᵀ))]
  have h3 : ⟪R * (1 + h • (Cᵀ * C))⁻¹, W⟫ = ‖W‖ ^ 2 - h * ⟪M * V, W⟫ := by
    rw [hR, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  refine le_of_sq_le_mul (norm_nonneg _) ?_
  nlinarith [real_inner_le_norm (R * (1 + h • (Cᵀ * C))⁻¹) W,
    mul_nonpos_of_nonneg_of_nonpos hh h2]

/-- **Damping from the right over `k` steps**: for a chain `W_{i+1} - h M W_{i+1} + h W_{i+1} CᵀC =
W_i` of backward Euler steps, `‖W_k‖ ≤ ‖W₀ (1 + h CᵀC)⁻¹ ^ k‖`. -/
theorem norm_le_norm_mul_inv_pow_of_backwardEuler (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
    (hh : 0 ≤ h) {K : ℕ} {W : ℕ → Matrix m n ℝ}
    (hW : ∀ i < K, W (i + 1) - h • (M * W (i + 1)) + h • (W (i + 1) * (Cᵀ * C)) = W i) :
    ‖W K‖ ≤ ‖W 0 * (1 + h • (Cᵀ * C))⁻¹ ^ K‖ := by
  have hu := isUnit_det_one_add_smul_gram C hh
  have hc : Commute (1 + h • (Cᵀ * C))⁻¹ (Cᵀ * C) :=
    commute_nonsing_inv hu ((Commute.one_left _).add_left ((Commute.refl _).smul_left h))
  have key : ∀ j : ℕ, ‖W K * (1 + h • (Cᵀ * C))⁻¹ ^ j‖ ≤
      ‖W 0 * (1 + h • (Cᵀ * C))⁻¹ ^ (K + j)‖ := by
    induction K with
    | zero => intro j; rw [Nat.zero_add]
    | succ i ih =>
      intro j
      have h1 := norm_le_norm_mul_inv_of_backwardEuler hdiss hh
        (backwardEuler_mul_right (hc.pow_left j) (hW i (Nat.lt_succ_self i)))
      rw [Matrix.mul_assoc, ← pow_succ] at h1
      have h2 := ih (fun l hl => hW l (Nat.lt_succ_of_lt hl)) (j + 1)
      rw [show i + 1 + j = i + (j + 1) by omega]
      exact h1.trans h2
  simpa using key 0

end Right

section Left

variable [DecidableEq m]

/-- **A backward Euler step is bounded by the left resolvent**: if `W - h M W + h W CᵀC = R` with
`M` dissipative (not necessarily normal), then `‖W‖ ≤ ‖(1 - h M)⁻¹ R‖`. -/
theorem norm_le_norm_inv_mul_of_backwardEuler (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
    (hh : 0 ≤ h) {W R : Matrix m n ℝ} (heq : W - h • (M * W) + h • (W * (Cᵀ * C)) = R) :
    ‖W‖ ≤ ‖(1 - h • M)⁻¹ * R‖ := by
  have hu := isUnit_det_one_sub_smul hdiss hh
  have hR : (1 - h • M)⁻¹ * R = W + h • ((1 - h • M)⁻¹ * (W * Cᵀ) * C) := by
    have e : R = (1 - h • M) * W + h • (W * (Cᵀ * C)) := by
      rw [← heq, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [e, Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
      Matrix.mul_smul]
    simp only [Matrix.mul_assoc]
  have h1 : ⟪(1 - h • M)⁻¹ * R, W⟫ =
      ‖W‖ ^ 2 + h * ⟪(1 - h • M)⁻¹ * (W * Cᵀ), W * Cᵀ⟫ := by
    rw [hR, inner_add_left, real_inner_smul_left, Frobenius.inner_mul_right,
      real_inner_self_eq_norm_sq]
  refine le_of_sq_le_mul (norm_nonneg _) ?_
  nlinarith [real_inner_le_norm ((1 - h • M)⁻¹ * R) W,
    mul_nonneg hh (inner_inv_one_sub_smul_mul_self_nonneg hdiss hh (W * Cᵀ))]

/-- **Damping from the left over `k` steps**: for a chain `W_{i+1} - h M W_{i+1} + h W_{i+1} CᵀC =
W_i` of backward Euler steps, `‖W_k‖ ≤ ‖(1 - h M)⁻¹ ^ k W₀‖`. -/
theorem norm_le_norm_inv_pow_mul_of_backwardEuler (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
    (hh : 0 ≤ h) {K : ℕ} {W : ℕ → Matrix m n ℝ}
    (hW : ∀ i < K, W (i + 1) - h • (M * W (i + 1)) + h • (W (i + 1) * (Cᵀ * C)) = W i) :
    ‖W K‖ ≤ ‖(1 - h • M)⁻¹ ^ K * W 0‖ := by
  have hu := isUnit_det_one_sub_smul hdiss hh
  have hc : Commute (1 - h • M)⁻¹ M :=
    commute_nonsing_inv hu ((Commute.one_left _).sub_left ((Commute.refl _).smul_left h))
  have key : ∀ j : ℕ, ‖(1 - h • M)⁻¹ ^ j * W K‖ ≤ ‖(1 - h • M)⁻¹ ^ (K + j) * W 0‖ := by
    induction K with
    | zero => intro j; rw [Nat.zero_add]
    | succ i ih =>
      intro j
      have h1 := norm_le_norm_inv_mul_of_backwardEuler hdiss hh
        (backwardEuler_mul_left (C := C) (hc.pow_left j) (hW i (Nat.lt_succ_self i)))
      rw [← Matrix.mul_assoc, ← pow_succ'] at h1
      have h2 := ih (fun l hl => hW l (Nat.lt_succ_of_lt hl)) (j + 1)
      rw [show i + 1 + j = i + (j + 1) by omega]
      exact h1.trans h2
  simpa using key 0

end Left

section Run

variable [DecidableEq m] [DecidableEq n]

/-! ### The run bound -/

/-- **Damped a posteriori bound for any sequence, with splittings of the start error and of the
residuals.** Let `F(Z) = M Z - Z CᵀC` with `M` dissipative, `𝒫 Z = Z - h M Z + h Z CᵀC`, let `X` be
a backward Euler reference with defects, `𝒫 X_{j+1} = X_j + δ_j`, and let `Y_j` be any sequence.
For all splittings `Y₀ - X₀ = ∑_b Q_b` and `Y_j - 𝒫 Y_{j+1} + δ_j = ∑_a P_{j,a}` into finitely many
parts,

  `‖Y_N - X_N‖ ≤ ∑_b min(‖(1 - h M)⁻¹ ^ N Q_b‖, ‖Q_b (1 + h CᵀC)⁻¹ ^ N‖)
    + ∑_{j<N} ∑_a min(‖(1 - h M)⁻¹ ^ (N-j) P_{j,a}‖, ‖P_{j,a} (1 + h CᵀC)⁻¹ ^ (N-j)‖)`.

Nothing is assumed on how `Y_j` was computed. The right-hand side needs solves with the one
matrix `1 - h M` or `1 + h CᵀC` only, applied to the factors of each part. -/
theorem norm_sub_le_sum_min_add_sum_min_of_backwardEuler {ι κ : Type*} (s : Finset ι)
    (t : Finset κ) {N : ℕ} {Y X δ : ℕ → Matrix m n ℝ} {P : ℕ → ι → Matrix m n ℝ}
    {Q : κ → Matrix m n ℝ} (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 ≤ h)
    (hX : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j + δ j)
    (hQ : ∑ b ∈ t, Q b = Y 0 - X 0)
    (hP : ∀ j < N, ∑ a ∈ s, P j a =
      Y j - (Y (j + 1) - h • (M * Y (j + 1)) + h • (Y (j + 1) * (Cᵀ * C))) + δ j) :
    ‖Y N - X N‖ ≤
      ∑ b ∈ t, min ‖(1 - h • M)⁻¹ ^ N * Q b‖ ‖Q b * (1 + h • (Cᵀ * C))⁻¹ ^ N‖ +
      ∑ j ∈ range N, ∑ a ∈ s, min ‖(1 - h • M)⁻¹ ^ (N - j) * P j a‖
        ‖P j a * (1 + h • (Cᵀ * C))⁻¹ ^ (N - j)‖ := by
  choose E hE0 hE using fun b : κ => exists_backwardEuler_iterates hdiss hh C (Q b)
  choose V hV0 hV using fun (j : ℕ) (a : ι) =>
    exists_backwardEuler_iterates hdiss hh C (P j a)
  have hrep := norm_sub_le_add_sum_of_backwardEuler_iterates
    (E := fun i => ∑ b ∈ t, E b i) (W := fun j i => ∑ a ∈ s, V j a i) hdiss hh hX
    ((Finset.sum_congr rfl fun b _ => hE0 b).trans hQ)
    (fun i _ => backwardEuler_sum t fun b _ => hE b i)
    (fun j hj => (Finset.sum_congr rfl fun a _ => hV0 j a).trans (hP j hj))
    (fun j _ i _ => backwardEuler_sum s fun a _ => hV j a i)
  refine hrep.trans (add_le_add ?_ (Finset.sum_le_sum fun j _ => ?_))
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [← hE0 b]
    exact le_min (norm_le_norm_inv_pow_mul_of_backwardEuler hdiss hh fun i _ => hE b i)
      (norm_le_norm_mul_inv_pow_of_backwardEuler hdiss hh fun i _ => hE b i)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [← hV0 j a]
    exact le_min (norm_le_norm_inv_pow_mul_of_backwardEuler hdiss hh fun i _ => hV j a i)
      (norm_le_norm_mul_inv_pow_of_backwardEuler hdiss hh fun i _ => hV j a i)

/-- **Damped a posteriori bound for any sequence, with a splitting of the residuals.** In the
setting of `norm_sub_le_sum_min_add_sum_min_of_backwardEuler`, without a splitting of the start
error:

  `‖Y_N - X_N‖ ≤ min(‖(1 - h M)⁻¹ ^ N (Y₀ - X₀)‖, ‖(Y₀ - X₀) (1 + h CᵀC)⁻¹ ^ N‖)
    + ∑_{j<N} ∑_a min(‖(1 - h M)⁻¹ ^ (N-j) P_{j,a}‖, ‖P_{j,a} (1 + h CᵀC)⁻¹ ^ (N-j)‖)`. -/
theorem norm_sub_le_min_add_sum_min_of_backwardEuler {ι : Type*} (s : Finset ι) {N : ℕ}
    {Y X δ : ℕ → Matrix m n ℝ} {P : ℕ → ι → Matrix m n ℝ}
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 ≤ h)
    (hX : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j + δ j)
    (hP : ∀ j < N, ∑ a ∈ s, P j a =
      Y j - (Y (j + 1) - h • (M * Y (j + 1)) + h • (Y (j + 1) * (Cᵀ * C))) + δ j) :
    ‖Y N - X N‖ ≤
      min ‖(1 - h • M)⁻¹ ^ N * (Y 0 - X 0)‖ ‖(Y 0 - X 0) * (1 + h • (Cᵀ * C))⁻¹ ^ N‖ +
      ∑ j ∈ range N, ∑ a ∈ s, min ‖(1 - h • M)⁻¹ ^ (N - j) * P j a‖
        ‖P j a * (1 + h • (Cᵀ * C))⁻¹ ^ (N - j)‖ := by
  have key := norm_sub_le_sum_min_add_sum_min_of_backwardEuler s ({()} : Finset Unit)
    (Q := fun _ => Y 0 - X 0) hdiss hh hX (Finset.sum_singleton _ _) hP
  simpa only [Finset.sum_singleton] using key

/-- **Damped a posteriori bound for any sequence: residual and defect.** In the setting of
`norm_sub_le_min_add_sum_min_of_backwardEuler`, with the residuals
`ρ_j = Y_j - (Y_{j+1} - h M Y_{j+1} + h Y_{j+1} CᵀC)` of the sequence,

  `‖Y_N - X_N‖ ≤ min(‖(1 - h M)⁻¹ ^ N (Y₀ - X₀)‖, ‖(Y₀ - X₀) (1 + h CᵀC)⁻¹ ^ N‖)
    + ∑_{j<N} (min(‖(1 - h M)⁻¹ ^ (N-j) ρ_j‖, ‖ρ_j (1 + h CᵀC)⁻¹ ^ (N-j)‖)
      + min(‖(1 - h M)⁻¹ ^ (N-j) δ_j‖, ‖δ_j (1 + h CᵀC)⁻¹ ^ (N-j)‖))`. -/
theorem norm_sub_le_min_add_sum_min_of_backwardEuler_residual {N : ℕ}
    {Y X δ : ℕ → Matrix m n ℝ} (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 ≤ h)
    (hX : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j + δ j) :
    ‖Y N - X N‖ ≤
      min ‖(1 - h • M)⁻¹ ^ N * (Y 0 - X 0)‖ ‖(Y 0 - X 0) * (1 + h • (Cᵀ * C))⁻¹ ^ N‖ +
      ∑ j ∈ range N,
        (min ‖(1 - h • M)⁻¹ ^ (N - j) *
            (Y j - (Y (j + 1) - h • (M * Y (j + 1)) + h • (Y (j + 1) * (Cᵀ * C))))‖
          ‖(Y j - (Y (j + 1) - h • (M * Y (j + 1)) + h • (Y (j + 1) * (Cᵀ * C)))) *
            (1 + h • (Cᵀ * C))⁻¹ ^ (N - j)‖ +
        min ‖(1 - h • M)⁻¹ ^ (N - j) * δ j‖ ‖δ j * (1 + h • (Cᵀ * C))⁻¹ ^ (N - j)‖) := by
  have key := norm_sub_le_min_add_sum_min_of_backwardEuler (Finset.univ : Finset Bool)
    (P := fun j b => cond b
      (Y j - (Y (j + 1) - h • (M * Y (j + 1)) + h • (Y (j + 1) * (Cᵀ * C)))) (δ j))
    hdiss hh hX fun j _ => by rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false]
  simpa only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false] using key

omit [DecidableEq m] in
/-- **Damped a posteriori bound for any sequence, from the right only**:

  `‖Y_N - X_N‖ ≤ ‖(Y₀ - X₀) (1 + h CᵀC)⁻¹ ^ N‖
    + ∑_{j<N} (‖ρ_j (1 + h CᵀC)⁻¹ ^ (N-j)‖ + ‖δ_j (1 + h CᵀC)⁻¹ ^ (N-j)‖)`,

with the residuals `ρ_j = Y_j - (Y_{j+1} - h M Y_{j+1} + h Y_{j+1} CᵀC)`. No solve with `M` is
needed. -/
theorem norm_sub_le_add_sum_norm_mul_inv_pow_of_backwardEuler {N : ℕ}
    {Y X δ : ℕ → Matrix m n ℝ} (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 ≤ h)
    (hX : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j + δ j) :
    ‖Y N - X N‖ ≤ ‖(Y 0 - X 0) * (1 + h • (Cᵀ * C))⁻¹ ^ N‖ +
      ∑ j ∈ range N,
        (‖(Y j - (Y (j + 1) - h • (M * Y (j + 1)) + h • (Y (j + 1) * (Cᵀ * C)))) *
            (1 + h • (Cᵀ * C))⁻¹ ^ (N - j)‖ + ‖δ j * (1 + h • (Cᵀ * C))⁻¹ ^ (N - j)‖) := by
  classical
  exact (norm_sub_le_min_add_sum_min_of_backwardEuler_residual hdiss hh hX).trans
    (add_le_add (min_le_right _ _) (Finset.sum_le_sum fun _ _ =>
      add_le_add (min_le_right _ _) (min_le_right _ _)))

end Run

end ImplicitBUGStiffDamped

/-! ### Non-vacuity -/

namespace ImplicitBUGStiffDampedExample

/-- The matrix `(0, 1; -1, -1)` is dissipative; it is not normal. -/
theorem dotProduct_mulVec_nonpos (x : Fin 2 → ℝ) :
    x ⬝ᵥ (!![0, 1; -1, -1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x ≤ 0 := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  nlinarith [mul_self_nonneg (x 1)]

/-- The hypotheses of the damped run bounds hold for a non-normal dissipative `M` with a nonzero
start error and a nonzero residual. -/
example {h : ℝ} (hh : 0 < h) : ∃ (Y X δ : ℕ → Matrix (Fin 2) (Fin 2) ℝ),
    (∀ j < 2, X (j + 1) - h • ((!![0, 1; -1, -1] : Matrix (Fin 2) (Fin 2) ℝ) * X (j + 1)) +
      h • (X (j + 1) * ((!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ *
        (!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ))) = X j + δ j) ∧
    Y 0 - X 0 ≠ 0 ∧
    Y 0 - (Y 1 - h • ((!![0, 1; -1, -1] : Matrix (Fin 2) (Fin 2) ℝ) * Y 1) +
      h • (Y 1 * ((!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ *
        (!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ)))) ≠ 0 := by
  refine ⟨fun _ => 1, fun _ => 0, fun _ => 0, fun j _ => by simp, by simp, fun hc => ?_⟩
  have h01 : h = 0 := by simpa [Matrix.mul_apply] using congrFun (congrFun hc 0) 1
  exact hh.ne' h01

end ImplicitBUGStiffDampedExample

end LeanDLRA
