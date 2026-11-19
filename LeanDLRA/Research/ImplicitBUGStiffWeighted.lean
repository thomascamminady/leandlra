import LeanDLRA.Research.ImplicitBUGStiffColumnSpace

/-!
# Backward Euler of a stiff linear problem: the error in norms weighted on the rows

Let `F(Z) = M Z - Z CᵀC + G` and let `S` commute with `CᵀC`. A backward Euler step
`W - h M W + h W CᵀC = R` commutes with the multiplication by `S` from the right, and so does a
projector acting from the left. Hence every bound of the error inside and outside the column
space of a truncated run holds verbatim in the weighted norm `‖Z S‖`
(`norm_sub_proj_mul_mul_le_add_sum_of_backwardEuler`, `norm_sub_mul_le_sqrt_add_of_backwardEuler`).

For `M = 0` the truncation itself has a weight. Let `R Rᵀ = (1 + h CᵀC)⁻¹` and
`S Sᵀ = 1 - R Rᵀ = h CᵀC (1 + h CᵀC)⁻¹` (`exists_weights`). With the errors `E = Y - A` before and
`z = Z - A₁` after a step of the reference, the backward Euler step `W` from `Y` has
`W - A₁ = E R Rᵀ` and

  `‖Z - W‖² = ‖z S‖² + ‖(z - E) R‖² + c(E)`      (`sq_norm_sub_mul_eq`),

so a step `Y₁` that is at most as far from `W` as a competitor `Z` satisfies

  `‖(Y₁ - A₁) S‖² + ‖(Y₁ - A₁ - E) R‖² ≤ ‖(Z - A₁) S‖² + ‖(Z - A₁ - E) R‖²`.

A best approximation of `W` of rank `r` is at most as far from `W` as every matrix of rank `r`,
in particular as the old value `Y` or as `Y + D` with an increment `D` that keeps the rank.
Consequences: for a stationary reference the error in the norm `‖Z S‖` does not increase
(`norm_sub_mul_le_of_norm_sub_le_of_stationary`), whatever `C` and `h` are; for a moving
reference it grows at most by the weighted increments of the reference that the competitor does
not follow (`norm_sub_mul_le_add_sum_of_norm_sub_le`).

The example namespace contains a stationary relaxation with two row modes whose stationary
truncated sequence is far from the best approximation in the Frobenius norm and is the best
approximation in the weighted norm, and one whose stationary sequence is the best approximation
in the Frobenius norm and not in the weighted norm.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius
open Matrix Finset

namespace LeanDLRA

open ImplicitBUGStiffLemmas ImplicitBUGStiffLocal ImplicitBUGStiffColumnSpace Curvature

namespace ImplicitBUGStiffWeighted

variable {m n k p q : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype p] [Fintype q]
  {M : Matrix m m ℝ} {C : Matrix k n ℝ} {h μ : ℝ}

/-! ### Weights that commute with the stiff operator -/

/-- **A backward Euler step commutes with a weight on the rows**: if `S` commutes with `CᵀC` and
`W - h M W + h W CᵀC = R`, then `W S` is the backward Euler step with the right-hand side
`R S`. -/
theorem backwardEuler_mul_right {S : Matrix n n ℝ} (hS : Cᵀ * C * S = S * (Cᵀ * C))
    {W R : Matrix m n ℝ} (heq : W - h • (M * W) + h • (W * (Cᵀ * C)) = R) :
    W * S - h • (M * (W * S)) + h • (W * S * (Cᵀ * C)) = R * S := by
  rw [← heq, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_assoc M W S, Matrix.mul_assoc W S, ← hS, Matrix.mul_assoc W (Cᵀ * C) S]

section Run

variable [DecidableEq m] {N : ℕ} {Y W A g δ : ℕ → Matrix m n ℝ} {T : ℕ → Matrix m m ℝ}
  {γ : ℕ → ℝ} {S : Matrix n n ℝ}

/-- **Run bound for the error inside the range in a weighted norm.** Let `F(Z) = M Z - Z CᵀC`
with `M` dissipative and bounded by `μ`, `𝒫 Z = Z - h M Z + h Z CᵀC`, let `A` be a reference with
`𝒫 A_{j+1} = A_j + g_j + δ_j`, let `Y_j` be any sequence, `𝒫 W_j = Y_j + g_j`, let `T_j` be
orthogonal projectors with `‖T_{j+1} (1 - T_j)‖₂ ≤ γ_j`, and let `S` commute with `CᵀC`. Then

  `‖(Y_N - T_N A_N) S‖ ≤ ‖(Y₀ - T₀ A₀) S‖`
  `    + ∑_{j<N} ((h μ + γ_j) ‖(A_j - T_j A_j) S‖ + ‖δ_j S‖ + ‖(Y_{j+1} - T_{j+1} W_j) S‖)`. -/
theorem norm_sub_proj_mul_mul_le_add_sum_of_backwardEuler
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 ≤ h)
    (hS : Cᵀ * C * S = S * (Cᵀ * C)) (hT : ∀ j ≤ N, IsOrthProjMat (T j))
    (hW : ∀ j < N, W j - h • (M * W j) + h • (W j * (Cᵀ * C)) = Y j + g j)
    (hA : ∀ j < N,
      A (j + 1) - h • (M * A (j + 1)) + h • (A (j + 1) * (Cᵀ * C)) = A j + g j + δ j)
    (hγ : ∀ j < N, specNorm (T (j + 1) * (1 - T j)) ≤ γ j) :
    ‖(Y N - T N * A N) * S‖ ≤ ‖(Y 0 - T 0 * A 0) * S‖ + ∑ j ∈ range N,
      ((h * μ + γ j) * ‖(A j - T j * A j) * S‖ + ‖δ j * S‖ +
        ‖(Y (j + 1) - T (j + 1) * W j) * S‖) := by
  have h1 := norm_sub_proj_mul_le_add_sum_of_backwardEuler (Y := fun j => Y j * S)
    (W := fun j => W j * S) (A := fun j => A j * S) (g := fun j => g j * S)
    (δ := fun j => δ j * S) hdiss hμ0 hμ hh hT
    (fun j hj => by simpa only [Matrix.add_mul] using backwardEuler_mul_right hS (hW j hj))
    (fun j hj => by simpa only [Matrix.add_mul] using backwardEuler_mul_right hS (hA j hj)) hγ
  simpa only [Matrix.sub_mul, Matrix.mul_assoc] using h1

/-- **Error bound in a weighted norm.** In the setting of
`norm_sub_proj_mul_mul_le_add_sum_of_backwardEuler`, if `T_N Y_N = Y_N`, then

  `‖(Y_N - A_N) S‖ ≤ √(B² + ‖(A_N - T_N A_N) S‖²)`,

with `B` the right-hand side of that bound. -/
theorem norm_sub_mul_le_sqrt_add_of_backwardEuler
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 ≤ h)
    (hS : Cᵀ * C * S = S * (Cᵀ * C)) (hT : ∀ j ≤ N, IsOrthProjMat (T j))
    (hYN : T N * Y N = Y N)
    (hW : ∀ j < N, W j - h • (M * W j) + h • (W j * (Cᵀ * C)) = Y j + g j)
    (hA : ∀ j < N,
      A (j + 1) - h • (M * A (j + 1)) + h • (A (j + 1) * (Cᵀ * C)) = A j + g j + δ j)
    (hγ : ∀ j < N, specNorm (T (j + 1) * (1 - T j)) ≤ γ j) :
    ‖(Y N - A N) * S‖ ≤ √((‖(Y 0 - T 0 * A 0) * S‖ + ∑ j ∈ range N,
      ((h * μ + γ j) * ‖(A j - T j * A j) * S‖ + ‖δ j * S‖ +
        ‖(Y (j + 1) - T (j + 1) * W j) * S‖)) ^ 2 + ‖(A N - T N * A N) * S‖ ^ 2) := by
  have h1 := norm_sub_proj_mul_mul_le_add_sum_of_backwardEuler hdiss hμ0 hμ hh hS hT hW hA hγ
  have h2 := sq_norm_sub_eq_sq_norm_sub_proj_mul_add (hT N le_rfl) (Y := Y N * S)
    (A := A N * S) (by rw [← Matrix.mul_assoc, hYN])
  simp only [← Matrix.mul_assoc, ← Matrix.sub_mul] at h2
  refine Real.le_sqrt_of_sq_le ?_
  rw [h2]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) h1 2) le_rfl

end Run

/-! ### The weight of the truncation -/

section Weight

variable {S : Matrix n p ℝ} {R : Matrix n q ℝ}

/-- Two weights with `S Sᵀ + R Rᵀ = 1` split the square of the Frobenius norm. -/
theorem sq_norm_mul_add_sq_norm_mul [DecidableEq n] (hSR : S * Sᵀ + R * Rᵀ = 1)
    (D : Matrix m n ℝ) : ‖D * S‖ ^ 2 + ‖D * R‖ ^ 2 = ‖D‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    Frobenius.inner_mul_right' (D * S), Frobenius.inner_mul_right' (D * R), ← inner_add_left,
    Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, hSR, Matrix.mul_one]

/-- **The distance from a backward Euler step in the two weights.** If `S Sᵀ + R Rᵀ = 1`, then
for all `z` and `E`

  `‖z - E R Rᵀ‖² = ‖z S‖² + ‖(z - E) R‖² + (‖E R Rᵀ‖² - ‖E R‖²)`. -/
theorem sq_norm_sub_mul_eq [DecidableEq n] (hSR : S * Sᵀ + R * Rᵀ = 1) (z E : Matrix m n ℝ) :
    ‖z - E * (R * Rᵀ)‖ ^ 2 =
      ‖z * S‖ ^ 2 + ‖(z - E) * R‖ ^ 2 + (‖E * (R * Rᵀ)‖ ^ 2 - ‖E * R‖ ^ 2) := by
  have h1 := sq_norm_mul_add_sq_norm_mul hSR z
  have h2 : ⟪z, E * (R * Rᵀ)⟫ = ⟪z * R, E * R⟫ := by
    rw [← Matrix.mul_assoc, Frobenius.inner_mul_right', Matrix.transpose_transpose]
  rw [norm_sub_sq_real, h2, Matrix.sub_mul, norm_sub_sq_real]
  linarith

/-- **A step that is at most as far from the backward Euler step as a competitor.** Let
`S Sᵀ + R Rᵀ = 1` and `W - A₁ = E R Rᵀ` (for a backward Euler step with `M = 0`: `E = Y - A` is
the error before the step and `R Rᵀ = (1 + h CᵀC)⁻¹`). If `‖Y₁ - W‖ ≤ ‖Z - W‖`, then

  `‖(Y₁ - A₁) S‖² + ‖(Y₁ - A₁ - E) R‖² ≤ ‖(Z - A₁) S‖² + ‖(Z - A₁ - E) R‖²`. -/
theorem sq_norm_sub_mul_add_le_of_norm_sub_le [DecidableEq n] (hSR : S * Sᵀ + R * Rᵀ = 1)
    {Y₁ Z W A₁ E : Matrix m n ℝ} (hW : W - A₁ = E * (R * Rᵀ)) (hle : ‖Y₁ - W‖ ≤ ‖Z - W‖) :
    ‖(Y₁ - A₁) * S‖ ^ 2 + ‖(Y₁ - A₁ - E) * R‖ ^ 2 ≤
      ‖(Z - A₁) * S‖ ^ 2 + ‖(Z - A₁ - E) * R‖ ^ 2 := by
  have e : ∀ X : Matrix m n ℝ, X - W = X - A₁ - E * (R * Rᵀ) := fun X => by
    rw [← hW]
    abel
  have h1 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [e Y₁, e Z, sq_norm_sub_mul_eq hSR, sq_norm_sub_mul_eq hSR] at h1
  linarith

omit [Fintype m] in
/-- **The backward Euler steps from two values differ by the resolvent of the difference**: if
`W + h W CᵀC = Y + g`, `A₁ + h A₁ CᵀC = A + g` and `(1 + h CᵀC) G = 1`, then
`W - A₁ = (Y - A) G`. -/
theorem sub_eq_mul_of_backwardEuler [DecidableEq n] {G : Matrix n n ℝ}
    (hG : (1 + h • (Cᵀ * C)) * G = 1) {W A₁ Y A g : Matrix m n ℝ}
    (hW : W + h • (W * (Cᵀ * C)) = Y + g) (hA : A₁ + h • (A₁ * (Cᵀ * C)) = A + g) :
    W - A₁ = (Y - A) * G := by
  have e : (W - A₁) * (1 + h • (Cᵀ * C)) = Y - A := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.sub_mul, smul_sub]
    calc W - A₁ + (h • (W * (Cᵀ * C)) - h • (A₁ * (Cᵀ * C)))
        = W + h • (W * (Cᵀ * C)) - (A₁ + h • (A₁ * (Cᵀ * C))) := by abel
      _ = Y - A := by rw [hW, hA]; abel
  rw [← e, Matrix.mul_assoc, hG, Matrix.mul_one]

/-- The weight `S Sᵀ` is `h CᵀC (1 + h CᵀC)⁻¹`: if `S Sᵀ + R Rᵀ = 1` and
`(1 + h CᵀC) R Rᵀ = 1`, then `(1 + h CᵀC) S Sᵀ = h CᵀC`. -/
theorem one_add_smul_mul_weight [DecidableEq n] (hSR : S * Sᵀ + R * Rᵀ = 1)
    (hG : (1 + h • (Cᵀ * C)) * (R * Rᵀ) = 1) :
    (1 + h • (Cᵀ * C)) * (S * Sᵀ) = h • (Cᵀ * C) := by
  have e : S * Sᵀ = 1 - R * Rᵀ := eq_sub_of_add_eq hSR
  rw [e, Matrix.mul_sub, hG, Matrix.mul_one, add_sub_cancel_left]

/-- **The error of a step in the weight of the truncation, with a competitor.** Let `M = 0`,
`S Sᵀ + R Rᵀ = 1`, `(1 + h CᵀC) R Rᵀ = 1`, `W + h W CᵀC = Y + g` and `A₁ + h A₁ CᵀC = A + g`. If
`Y₁` is at most as far from `W` as `Y + D`, then

  `‖(Y₁ - A₁) S‖ ≤ ‖(Y - A) S‖ + ‖(A₁ - A - D) S‖ + ‖(A₁ - A - D) R‖`. -/
theorem norm_sub_mul_le_add_of_norm_sub_le [DecidableEq n] (hSR : S * Sᵀ + R * Rᵀ = 1)
    (hG : (1 + h • (Cᵀ * C)) * (R * Rᵀ) = 1) {W A₁ Y A g Y₁ D : Matrix m n ℝ}
    (hW : W + h • (W * (Cᵀ * C)) = Y + g) (hA : A₁ + h • (A₁ * (Cᵀ * C)) = A + g)
    (hle : ‖Y₁ - W‖ ≤ ‖Y + D - W‖) :
    ‖(Y₁ - A₁) * S‖ ≤ ‖(Y - A) * S‖ + ‖(A₁ - A - D) * S‖ + ‖(A₁ - A - D) * R‖ := by
  have h1 := sq_norm_sub_mul_add_le_of_norm_sub_le hSR (S := S)
    (sub_eq_mul_of_backwardEuler hG hW hA) hle
  have e1 : Y + D - A₁ = Y - A - (A₁ - A - D) := by abel
  have e2 : Y + D - A₁ - (Y - A) = -(A₁ - A - D) := by abel
  rw [e2, Matrix.neg_mul, norm_neg, e1, Matrix.sub_mul (Y - A)] at h1
  have t := norm_sub_le ((Y - A) * S) ((A₁ - A - D) * S)
  have hx := pow_le_pow_left₀ (norm_nonneg _) t 2
  have hb := sq_nonneg ‖(Y₁ - A₁ - (Y - A)) * R‖
  have hm := mul_nonneg (add_nonneg (norm_nonneg ((Y - A) * S)) (norm_nonneg ((A₁ - A - D) * S)))
    (norm_nonneg ((A₁ - A - D) * R))
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  nlinarith

/-- **The error of a step with a stationary reference does not increase in the weight of the
truncation.** Let `M = 0`, `S Sᵀ + R Rᵀ = 1`, `(1 + h CᵀC) R Rᵀ = 1`, and let `W` be the backward
Euler step of the relaxation `F(Z) = -(Z - A) CᵀC` from `Y`. If `Y₁` is at most as far from `W`
as `Y`, then `‖(Y₁ - A) S‖² + ‖(Y₁ - Y) R‖² ≤ ‖(Y - A) S‖²`. -/
theorem sq_norm_sub_mul_add_le_of_stationary [DecidableEq n] (hSR : S * Sᵀ + R * Rᵀ = 1)
    (hG : (1 + h • (Cᵀ * C)) * (R * Rᵀ) = 1) {W Y A Y₁ : Matrix m n ℝ}
    (hW : W + h • (W * (Cᵀ * C)) = Y + h • (A * (Cᵀ * C))) (hle : ‖Y₁ - W‖ ≤ ‖Y - W‖) :
    ‖(Y₁ - A) * S‖ ^ 2 + ‖(Y₁ - Y) * R‖ ^ 2 ≤ ‖(Y - A) * S‖ ^ 2 := by
  have h1 := sq_norm_sub_mul_add_le_of_norm_sub_le hSR (S := S)
    (sub_eq_mul_of_backwardEuler hG hW rfl) hle
  have e1 : Y₁ - A - (Y - A) = Y₁ - Y := by abel
  rw [e1, sub_self, Matrix.zero_mul, norm_zero] at h1
  linarith

section WeightRun

variable {N : ℕ} {Y W A g D : ℕ → Matrix m n ℝ}

/-- **Run bound in the weight of the truncation.** Let `M = 0`, `S Sᵀ + R Rᵀ = 1`,
`(1 + h CᵀC) R Rᵀ = 1`, let `A` be a backward Euler reference,
`A_{j+1} + h A_{j+1} CᵀC = A_j + g_j`, and `W_j + h W_j CᵀC = Y_j + g_j` the backward Euler steps
from a sequence `Y_j` such that
`Y_{j+1}` is at most as far from `W_j` as `Y_j + D_j` (for a best approximation of `W_j` of rank
`r`: every `D_j` such that `Y_j + D_j` has rank at most `r`). Then

  `‖(Y_N - A_N) S‖ ≤ ‖(Y₀ - A₀) S‖`
  `    + ∑_{j<N} (‖(A_{j+1} - A_j - D_j) S‖ + ‖(A_{j+1} - A_j - D_j) R‖)`,

whatever `C` is. -/
theorem norm_sub_mul_le_add_sum_of_norm_sub_le [DecidableEq n] (hSR : S * Sᵀ + R * Rᵀ = 1)
    (hG : (1 + h • (Cᵀ * C)) * (R * Rᵀ) = 1)
    (hW : ∀ j < N, W j + h • (W j * (Cᵀ * C)) = Y j + g j)
    (hA : ∀ j < N, A (j + 1) + h • (A (j + 1) * (Cᵀ * C)) = A j + g j)
    (hstep : ∀ j < N, ‖Y (j + 1) - W j‖ ≤ ‖Y j + D j - W j‖) :
    ‖(Y N - A N) * S‖ ≤ ‖(Y 0 - A 0) * S‖ + ∑ j ∈ range N,
      (‖(A (j + 1) - A j - D j) * S‖ + ‖(A (j + 1) - A j - D j) * R‖) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun j hj => hW j (Nat.lt_succ_of_lt hj))
      (fun j hj => hA j (Nat.lt_succ_of_lt hj)) fun j hj => hstep j (Nat.lt_succ_of_lt hj)
    have hn := Nat.lt_succ_self n
    have h1 := norm_sub_mul_le_add_of_norm_sub_le hSR hG (hW n hn) (hA n hn) (hstep n hn)
    rw [Finset.sum_range_succ]
    linarith

/-- **With a stationary reference the error of a truncated run does not increase in the weight
of the truncation.** Let `M = 0`, `S Sᵀ + R Rᵀ = 1`, `(1 + h CᵀC) R Rᵀ = 1`, and let `W_j` be the
backward Euler steps of the relaxation `F(Z) = -(Z - A) CᵀC` from a sequence `Y_j` such that
`Y_{j+1}` is at most as far from `W_j` as `Y_j`. Then `‖(Y_N - A) S‖ ≤ ‖(Y₀ - A) S‖`, whatever
`C`, `h` and `N` are. -/
theorem norm_sub_mul_le_of_norm_sub_le_of_stationary [DecidableEq n] {A : Matrix m n ℝ}
    (hSR : S * Sᵀ + R * Rᵀ = 1) (hG : (1 + h • (Cᵀ * C)) * (R * Rᵀ) = 1)
    (hW : ∀ j < N, W j + h • (W j * (Cᵀ * C)) = Y j + h • (A * (Cᵀ * C)))
    (hstep : ∀ j < N, ‖Y (j + 1) - W j‖ ≤ ‖Y j - W j‖) :
    ‖(Y N - A) * S‖ ≤ ‖(Y 0 - A) * S‖ := by
  have h1 := norm_sub_mul_le_add_sum_of_norm_sub_le (A := fun _ => A)
    (g := fun _ => h • (A * (Cᵀ * C))) (D := fun _ => 0) hSR hG hW (fun _ _ => rfl)
    fun j hj => by simpa using hstep j hj
  simpa using h1

end WeightRun

end Weight

/-- **The weights of the truncation exist**: for every `C` and `h ≥ 0` there are `S` and `R`
with `S Sᵀ + R Rᵀ = 1` and `(1 + h CᵀC) R Rᵀ = 1`. -/
theorem exists_weights [DecidableEq n] (C : Matrix k n ℝ) (hh : 0 ≤ h) :
    ∃ (S : Matrix n (k ⊕ n) ℝ) (R : Matrix n (n ⊕ k) ℝ),
      S * Sᵀ + R * Rᵀ = 1 ∧ (1 + h • (Cᵀ * C)) * (R * Rᵀ) = 1 := by
  obtain ⟨G, hG0⟩ := exists_backwardEuler (M := (0 : Matrix n n ℝ)) (C := C)
    (fun x => by simp) hh (1 : Matrix n n ℝ)
  set K : Matrix n n ℝ := h • (Cᵀ * C) with hK
  have hG1 : G * (1 + K) = 1 := by
    rw [Matrix.mul_add, Matrix.mul_one, hK, Matrix.mul_smul]
    simpa using hG0
  have hG2 : (1 + K) * G = 1 := mul_eq_one_comm.1 hG1
  have hKt : Kᵀ = K := by
    rw [hK, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hGt : Gᵀ = G := by
    have e : Gᵀ * (1 + K) = 1 := by
      have e0 := congrArg Matrix.transpose hG2
      rwa [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_one, hKt] at e0
    calc Gᵀ = Gᵀ * ((1 + K) * G) := by rw [hG2, Matrix.mul_one]
      _ = G := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]
  have hB : (√h • C)ᵀ * (√h • C) = K := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Real.mul_self_sqrt hh]
  have hGG : G * G + G * (K * G) = G := by
    calc G * G + G * (K * G) = G * ((1 + K) * G) := by noncomm_ring
      _ = G := by rw [hG2, Matrix.mul_one]
  have hR : fromCols G (G * (√h • C)ᵀ) * (fromCols G (G * (√h • C)ᵀ))ᵀ = G := by
    rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows, Matrix.transpose_mul,
      Matrix.transpose_transpose, hGt, Matrix.mul_assoc G, ← Matrix.mul_assoc _ (√h • C) G, hB,
      hGG]
  refine ⟨fromCols (G * (√h • C)ᵀ) (G * K), fromCols G (G * (√h • C)ᵀ), ?_, ?_⟩
  · rw [hR, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose, hGt, hKt, Matrix.mul_assoc G (√h • C)ᵀ,
      ← Matrix.mul_assoc _ (√h • C) G, hB]
    calc G * (K * G) + G * K * (K * G) + G
        = G * (K * G) + G * K * (K * G) + (G * G + G * (K * G)) := by rw [hGG]
      _ = G * (1 + K) * ((1 + K) * G) := by noncomm_ring
      _ = 1 := by rw [hG1, hG2, Matrix.one_mul]
  · rw [hR]
    exact hG2

end ImplicitBUGStiffWeighted

open ImplicitBUGStiffWeighted

/-! ### Examples -/

namespace ImplicitBUGStiffWeightedExample

open ImplicitBUGStiffColumnSpaceExample

local notation "Aʷ[" c ", " d ", " δ "]" =>
  (!![δ * d ^ 2 * (1 + c ^ 2), -(c ^ 2 * (1 + d ^ 2)); 1, δ] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Yʷ[" δ "]" => (!![0, 0; 1, δ] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Qʷ[" c ", " d "]" =>
  (!![c ^ 2 / (1 + c ^ 2), 0; 0, d ^ 2 / (1 + d ^ 2)] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Cʷ[" c ", " d "]" => (!![c, 0; 0, d] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Bʷ[" L "]" => (!![L, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Zʷ[" L "]" => (!![L, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Vʷ[" L "]" => (!![L, 0; 0, 1 / 2] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Dʷ" => (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Hʷ" => (!![1 / 2, 1 / 2; 1 / 2, 1 / 2] : Matrix (Fin 2) (Fin 2) ℝ)

/-- For the row modes with the rates `c²` and `d²` and `h = 1` the weight of the truncation is
`Q = diag(c² / (1 + c²), d² / (1 + d²))`: `(1 + CᵀC) Q = CᵀC`. -/
theorem one_add_gram_mul_weight (c d : ℝ) :
    (1 + (1 : ℝ) • (Cʷ[c, d]ᵀ * Cʷ[c, d])) * Qʷ[c, d] = (1 : ℝ) • (Cʷ[c, d]ᵀ * Cʷ[c, d]) := by
  have hc : 1 + c ^ 2 ≠ 0 := by positivity
  have hd : 1 + d ^ 2 ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

/-- **The rows of the reference are orthogonal in the weight of the truncation.** For the
stationary relaxation with the reference `A = (δ d² (1 + c²), -c² (1 + d²); 1, δ)`,

  `A Q Aᵀ = diag(c² d² b, b / ((1 + c²) (1 + d²)))`,   `b = δ² d² (1 + c²) + c² (1 + d²)`,

so the left singular vectors of `A Q^{1/2}` are the coordinate vectors. -/
theorem reference_mul_weight_mul_transpose (c d δ : ℝ) :
    Aʷ[c, d, δ] * Qʷ[c, d] * Aʷ[c, d, δ]ᵀ =
      !![c ^ 2 * d ^ 2 * (δ ^ 2 * d ^ 2 * (1 + c ^ 2) + c ^ 2 * (1 + d ^ 2)), 0; 0,
        (δ ^ 2 * d ^ 2 * (1 + c ^ 2) + c ^ 2 * (1 + d ^ 2)) / ((1 + c ^ 2) * (1 + d ^ 2))] := by
  have hc : 1 + c ^ 2 ≠ 0 := by positivity
  have hd : 1 + d ^ 2 ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    ring

/-- **The weighted error of the stationary sequence.** The stationary truncated sequence
`Y = (0, 0; 1, δ)` (the second row of `A`) has `(A - Y) Q (A - Y)ᵀ = diag(c² d² b, 0)`: the
square of its error in the weight of the truncation is the first diagonal entry of `A Q Aᵀ`. -/
theorem sub_mul_weight_mul_transpose (c d δ : ℝ) :
    (Aʷ[c, d, δ] - Yʷ[δ]) * Qʷ[c, d] * (Aʷ[c, d, δ] - Yʷ[δ])ᵀ =
      !![c ^ 2 * d ^ 2 * (δ ^ 2 * d ^ 2 * (1 + c ^ 2) + c ^ 2 * (1 + d ^ 2)), 0; 0, 0] := by
  have hc : 1 + c ^ 2 ≠ 0 := by positivity
  have hd : 1 + d ^ 2 ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

/-- **The stationary sequence is the best approximation in the weight of the truncation.** If
`c² d² (1 + c²) (1 + d²) ≤ 1`, the first diagonal entry of `A Q Aᵀ` is the smaller one: the
weighted error of the stationary sequence is the weighted error of the best rank-one
approximation of `A`. For `d = 1`, `δ = c` and small `c` the same sequence is farther from `A`
in the Frobenius norm than any given multiple of the best rank-one approximation. -/
theorem weighted_error_le_weighted_tail {c d : ℝ} (δ : ℝ)
    (hcd : c ^ 2 * d ^ 2 * (1 + c ^ 2) * (1 + d ^ 2) ≤ 1) :
    c ^ 2 * d ^ 2 * (δ ^ 2 * d ^ 2 * (1 + c ^ 2) + c ^ 2 * (1 + d ^ 2)) ≤
      (δ ^ 2 * d ^ 2 * (1 + c ^ 2) + c ^ 2 * (1 + d ^ 2)) / ((1 + c ^ 2) * (1 + d ^ 2)) := by
  rw [le_div_iff₀ (by positivity)]
  calc c ^ 2 * d ^ 2 * (δ ^ 2 * d ^ 2 * (1 + c ^ 2) + c ^ 2 * (1 + d ^ 2)) *
        ((1 + c ^ 2) * (1 + d ^ 2))
      = (δ ^ 2 * d ^ 2 * (1 + c ^ 2) + c ^ 2 * (1 + d ^ 2)) *
        (c ^ 2 * d ^ 2 * (1 + c ^ 2) * (1 + d ^ 2)) := by ring
    _ ≤ (δ ^ 2 * d ^ 2 * (1 + c ^ 2) + c ^ 2 * (1 + d ^ 2)) * 1 :=
      mul_le_mul_of_nonneg_left hcd (by positivity)
    _ = δ ^ 2 * d ^ 2 * (1 + c ^ 2) + c ^ 2 * (1 + d ^ 2) := mul_one _

/-- **A stationary sequence that is not the best approximation in the weight.** For the
stationary relaxation with the reference `B = diag(L, 1)`, the rates `c²` and `1` and `h = 1`,
the backward Euler step from `Z = diag(L, 0)` is `V = diag(L, 1/2)`. -/
theorem backwardEuler_step_diag (c L : ℝ) :
    Vʷ[L] + (1 : ℝ) • (Vʷ[L] * (Cʷ[c, 1]ᵀ * Cʷ[c, 1])) =
      Zʷ[L] + (1 : ℝ) • (Bʷ[L] * (Cʷ[c, 1]ᵀ * Cʷ[c, 1])) := by
  have hN : Cʷ[c, 1]ᵀ * Cʷ[c, 1] = !![c ^ 2, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_two]
  rw [hN]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  norm_num

/-- The rows of the step `V = diag(L, 1/2)` are orthogonal, `V Vᵀ = diag(L², 1/4)`, and the
projection of `V` onto the first coordinate is `Z`: for `L > 1/2` the sequence `Z` is stationary
for the truncation to rank one, and for `L ≥ 1` it is a best rank-one approximation of `B` in
the Frobenius norm. -/
theorem step_diag_mul_transpose (L : ℝ) :
    Vʷ[L] * Vʷ[L]ᵀ = !![L ^ 2, 0; 0, 1 / 4] ∧ Dʷ * Vʷ[L] = Zʷ[L] := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- In the weight of the truncation the rows of `B = diag(L, 1)` have the squared norms
`L² c² / (1 + c²)` and `1/2`, and the squared weighted error of `Z` is `1/2`. -/
theorem diag_mul_weight_mul_transpose (c L : ℝ) :
    Bʷ[L] * Qʷ[c, 1] * Bʷ[L]ᵀ = !![L ^ 2 * c ^ 2 / (1 + c ^ 2), 0; 0, 1 / 2] ∧
      (Bʷ[L] - Zʷ[L]) * Qʷ[c, 1] * (Bʷ[L] - Zʷ[L])ᵀ = !![0, 0; 0, 1 / 2] := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **The weighted error of that stationary sequence is far from the weighted best
approximation**: if `2 K L² c² < 1`, the squared weighted error `1/2` of `Z` exceeds `K` times
the squared weighted error `L² c² / (1 + c²)` of the rank-one matrix `diag(0, 1)`. -/
theorem mul_weighted_tail_lt_weighted_error {c L K : ℝ} (hK : 0 ≤ K)
    (hKL : 2 * K * (L ^ 2 * c ^ 2) < 1) : K * (L ^ 2 * c ^ 2 / (1 + c ^ 2)) < 1 / 2 := by
  have h1 : L ^ 2 * c ^ 2 / (1 + c ^ 2) ≤ L ^ 2 * c ^ 2 :=
    div_le_self (by positivity) (by nlinarith [sq_nonneg c])
  nlinarith [mul_le_mul_of_nonneg_left h1 hK]

/-- The hypotheses of the weighted run bounds hold for every `M`, `C` and `h` with the weight
`S = 1 + h CᵀC`, a reference with a part outside the first range and a range that rotates. -/
example (M : Matrix (Fin 2) (Fin 2) ℝ) (C : Matrix (Fin 1) (Fin 2) ℝ) (h : ℝ) :
    ∃ (Y W A g δ : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (T : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (γ : ℕ → ℝ)
      (S : Matrix (Fin 2) (Fin 2) ℝ), S = 1 + h • (Cᵀ * C) ∧ Cᵀ * C * S = S * (Cᵀ * C) ∧
      (∀ j ≤ 1, IsOrthProjMat (T j)) ∧ T 1 * Y 1 = Y 1 ∧
      (∀ j < 1, W j - h • (M * W j) + h • (W j * (Cᵀ * C)) = Y j + g j) ∧
      (∀ j < 1, A (j + 1) - h • (M * A (j + 1)) + h • (A (j + 1) * (Cᵀ * C)) =
        A j + g j + δ j) ∧
      (∀ j < 1, specNorm (T (j + 1) * (1 - T j)) ≤ γ j) ∧
      A 0 - T 0 * A 0 ≠ 0 ∧ T 1 * (1 - T 0) ≠ 0 := by
  refine ⟨fun j => if j = 0 then Dʷ else Hʷ, fun j => if j = 0 then Dʷ else Hʷ, fun _ => 1,
    fun _ => Dʷ - h • (M * Dʷ) + h • (Dʷ * (Cᵀ * C)) - Dʷ,
    fun _ => 1 - h • (M * 1) + h • (1 * (Cᵀ * C)) -
      (1 + (Dʷ - h • (M * Dʷ) + h • (Dʷ * (Cᵀ * C)) - Dʷ)),
    fun j => if j = 0 then Dʷ else Hʷ, fun _ => specNorm (Hʷ * (1 - Dʷ)), 1 + h • (Cᵀ * C), rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  · intro j _
    by_cases hj : j = 0
    · simp only [hj, ite_true]; exact isOrthProjMat_diag
    · simp only [hj, ite_false]; exact isOrthProjMat_half
  · simp only [one_ne_zero, ite_false]
    exact isOrthProjMat_half.idem
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp only [ite_true]
    abel
  · intro j hj
    exact (add_sub_cancel _ _).symm
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp only [zero_add, one_ne_zero, ite_false, ite_true]
    exact le_rfl
  · simp only [ite_true]
    exact one_sub_diag_mul_one_ne_zero
  · simp only [one_ne_zero, ite_false, ite_true]
    exact half_mul_one_sub_diag_ne_zero

/-- The hypotheses of the run bound in the weight of the truncation hold for every `C`, `h ≥ 0`,
initial value, initial reference, forcing and increment of the competitor, with the step
`Y₁ = W₀`. -/
example {h : ℝ} (hh : 0 ≤ h) (C : Matrix (Fin 1) (Fin 2) ℝ)
    (Y₀ A₀ g₀ D₀ : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ (S : Matrix (Fin 2) (Fin 1 ⊕ Fin 2) ℝ) (R : Matrix (Fin 2) (Fin 2 ⊕ Fin 1) ℝ)
      (Y W A g D : ℕ → Matrix (Fin 2) (Fin 2) ℝ),
      S * Sᵀ + R * Rᵀ = 1 ∧ (1 + h • (Cᵀ * C)) * (R * Rᵀ) = 1 ∧
      (∀ j < 1, W j + h • (W j * (Cᵀ * C)) = Y j + g j) ∧
      (∀ j < 1, A (j + 1) + h • (A (j + 1) * (Cᵀ * C)) = A j + g j) ∧
      (∀ j < 1, ‖Y (j + 1) - W j‖ ≤ ‖Y j + D j - W j‖) ∧
      Y 0 = Y₀ ∧ A 0 = A₀ ∧ g 0 = g₀ ∧ D 0 = D₀ := by
  obtain ⟨S, R, hSR, hG⟩ := exists_weights C hh
  obtain ⟨W₀, hW₀⟩ := exists_backwardEuler (M := (0 : Matrix (Fin 2) (Fin 2) ℝ)) (C := C)
    (fun x => by simp) hh (Y₀ + g₀)
  obtain ⟨A₁, hA₁⟩ := exists_backwardEuler (M := (0 : Matrix (Fin 2) (Fin 2) ℝ)) (C := C)
    (fun x => by simp) hh (A₀ + g₀)
  refine ⟨S, R, fun j => if j = 0 then Y₀ else W₀, fun _ => W₀,
    fun j => if j = 0 then A₀ else A₁, fun _ => g₀, fun _ => D₀, hSR, hG, ?_, ?_, ?_, by simp,
    by simp, rfl, rfl⟩
  · intro j hj
    obtain rfl : j = 0 := by omega
    simpa using hW₀
  · intro j hj
    obtain rfl : j = 0 := by omega
    simpa using hA₁
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp

end ImplicitBUGStiffWeightedExample

end LeanDLRA
