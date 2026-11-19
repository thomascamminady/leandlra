import LeanDLRA.Research.ImplicitBUGStiffColumnSpace

/-!
# Backward Euler of a stiff linear problem: the angle to the best-approximation column space

Let `F(Z) = M Z - Z CᵀC + G` with `M` dissipative and bounded by `μ`, let
`𝒫 Z = Z - h M Z + h Z CᵀC`, let `A_j` be a reference with `𝒫 A_{j+1} = A_j + g_j + δ_j`, `Y_j` a
sequence and `T_j` orthogonal
projectors acting from the left (the projectors onto the column spaces of `Y_j`). The run bound of
`ImplicitBUGStiffColumnSpace` contains the part `‖A_j - T_j A_j‖` of the reference outside the
range of `T_j` and the rotation `‖T_{j+1} (1 - T_j)‖₂` of the ranges. This file compares both with
the same quantities for a second family of orthogonal projectors `P_j` (the projectors onto the
dominant left singular vectors of `A_j`, for which `‖A_j - P_j A_j‖` is the error of the best
approximation): with `s_j ≥ ‖(1 - T_j) P_j‖₂` and `s_j ≥ ‖T_j (1 - P_j)‖₂` (the sine of the largest
angle between the two ranges),

  `‖A_j - T_j A_j‖ ≤ ‖A_j - P_j A_j‖ + s_j ‖P_j A_j‖`,
  `‖T_{j+1} (1 - T_j)‖₂ ≤ ‖P_{j+1} (1 - P_j)‖₂ + s_{j+1} + s_j`,

so the run bound holds with the data `‖A_j - P_j A_j‖`, `‖P_{j+1} (1 - P_j)‖₂` and the angles.

The angles cannot be removed: the last section gives a stationary reference and a stationary
sequence that is reproduced exactly by a backward Euler step followed by the truncation to the
dominant left singular vector, with `M = 0`, no defect and no local error, whose distance from the
reference is at least `δ / (δ² + w)` times the error of a rank-one approximation, where `w` is
the quotient of the weights `h λ / (1 + h λ)` of the slowest and of the fastest row mode. The run
bound of `ImplicitBUGStiffColumnSpace` does therefore not hold with `‖A_j - T_j A_j‖` replaced by
a multiple of the error of the best approximation, with a constant that depends neither on the
stiff operator nor on the step size.

## Main results

* `ImplicitBUGStiffColumnAngle.norm_sub_proj_mul_le_add_specNorm_mul`,
  `specNorm_proj_mul_compl_le`: the two comparisons.
* `ImplicitBUGStiffColumnAngle.specNorm_compl_mul_le_of_mul_eq`: the angle is at most
  `‖A - Y‖₂ ‖K‖₂` if `P = A K` and `T Y = Y`; no gap enters.
* `ImplicitBUGStiffColumnAngle.norm_sub_proj_mul_le_add_sum_of_backwardEuler_of_specNorm_le`,
  `norm_sub_le_sqrt_add_of_backwardEuler_of_specNorm_le`: the run bounds with the data and the
  angles.
* `ImplicitBUGStiffColumnAngleExample.backwardEuler_step`, `proj_mul_step`,
  `step_mul_transpose`, `mul_norm_reference_sub_rankOne_lt_norm_sub`: the stationary sequence.

## References

* [CerutiLubich2022], [CerutiKuschLubich2022] for the BUG integrator and its rank-adaptive
  variant; [Wedin1972] for the angles between singular subspaces.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius
open Matrix Finset

namespace LeanDLRA

open ImplicitBUGStiffLemmas ImplicitBUGStiffLocal ImplicitBUGStiffDamped Curvature
  ImplicitBUGStiffColumnSpace

namespace ImplicitBUGStiffColumnAngle

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m]
  {M : Matrix m m ℝ} {C : Matrix k n ℝ} {h μ : ℝ}

/-! ### The two comparisons -/

/-- **The part of a matrix outside one range against the part outside another.** For orthogonal
projectors `T`, `P`: `‖A - T A‖ ≤ ‖A - P A‖ + ‖(1 - T) P‖₂ ‖P A‖`. -/
theorem norm_sub_proj_mul_le_add_specNorm_mul {T P : Matrix m m ℝ} (hT : IsOrthProjMat T)
    (hP : IsOrthProjMat P) (A : Matrix m n ℝ) :
    ‖A - T * A‖ ≤ ‖A - P * A‖ + specNorm ((1 - T) * P) * ‖P * A‖ := by
  have e : A - T * A = A - P * A - T * (A - P * A) + (1 - T) * P * (P * A) := by
    rw [Matrix.mul_assoc (1 - T) P, ← Matrix.mul_assoc P P, hP.idem, Matrix.sub_mul,
      Matrix.one_mul, Matrix.mul_sub]
    abel
  rw [e]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_sub_proj_mul_le hT.idem hT.symm _) (frob_mul_le _ _))

/-- **The rotation of one family of ranges against the rotation of another.** For orthogonal
projectors `T₀`, `T₁`, `P₀`, `P₁`:
`‖T₁ (1 - T₀)‖₂ ≤ ‖P₁ (1 - P₀)‖₂ + ‖T₁ (1 - P₁)‖₂ + ‖P₀ (1 - T₀)‖₂`. -/
theorem specNorm_proj_mul_compl_le {T₀ T₁ P₀ P₁ : Matrix m m ℝ} (hT₀ : IsOrthProjMat T₀)
    (hT₁ : IsOrthProjMat T₁) (hP₁ : IsOrthProjMat P₁) :
    specNorm (T₁ * (1 - T₀)) ≤
      specNorm (P₁ * (1 - P₀)) + specNorm (T₁ * (1 - P₁)) + specNorm (P₀ * (1 - T₀)) := by
  have hadd : ∀ X Z : Matrix m m ℝ, specNorm (X + Z) ≤ specNorm X + specNorm Z := fun X Z => by
    unfold specNorm
    rw [map_add, map_add]
    exact norm_add_le _ _
  have e : T₁ * (1 - T₀) = T₁ * (1 - P₁) * (1 - T₀) +
      (T₁ * (P₁ * (1 - P₀)) * (1 - T₀) + T₁ * P₁ * (P₀ * (1 - T₀))) := by
    noncomm_ring
  have c₀ := hT₀.compl.specNorm_le_one
  have t₁ := hT₁.specNorm_le_one
  have p₁ := hP₁.specNorm_le_one
  have n1 : specNorm (T₁ * (1 - P₁) * (1 - T₀)) ≤ specNorm (T₁ * (1 - P₁)) :=
    (specNorm_mul_le _ _).trans (mul_le_of_le_one_right (specNorm_nonneg _) c₀)
  have n2 : specNorm (T₁ * (P₁ * (1 - P₀)) * (1 - T₀)) ≤ specNorm (P₁ * (1 - P₀)) :=
    calc specNorm (T₁ * (P₁ * (1 - P₀)) * (1 - T₀))
        ≤ specNorm (T₁ * (P₁ * (1 - P₀))) * specNorm (1 - T₀) := specNorm_mul_le _ _
      _ ≤ specNorm (T₁ * (P₁ * (1 - P₀))) := mul_le_of_le_one_right (specNorm_nonneg _) c₀
      _ ≤ specNorm T₁ * specNorm (P₁ * (1 - P₀)) := specNorm_mul_le _ _
      _ ≤ specNorm (P₁ * (1 - P₀)) := mul_le_of_le_one_left (specNorm_nonneg _) t₁
  have n3 : specNorm (T₁ * P₁ * (P₀ * (1 - T₀))) ≤ specNorm (P₀ * (1 - T₀)) :=
    calc specNorm (T₁ * P₁ * (P₀ * (1 - T₀)))
        ≤ specNorm (T₁ * P₁) * specNorm (P₀ * (1 - T₀)) := specNorm_mul_le _ _
      _ ≤ specNorm (P₀ * (1 - T₀)) := mul_le_of_le_one_left (specNorm_nonneg _)
          ((specNorm_mul_le _ _).trans
            ((mul_le_mul t₁ p₁ (specNorm_nonneg _) zero_le_one).trans (mul_one 1).le))
  rw [e]
  have a1 := hadd (T₁ * (1 - P₁) * (1 - T₀))
    (T₁ * (P₁ * (1 - P₀)) * (1 - T₀) + T₁ * P₁ * (P₀ * (1 - T₀)))
  have a2 := hadd (T₁ * (P₁ * (1 - P₀)) * (1 - T₀)) (T₁ * P₁ * (P₀ * (1 - T₀)))
  linarith

/-- **The angle without a gap.** Let `T` be an orthogonal projector with `T Y = Y` and let
`P = A K` (for the projector onto the dominant `r` left singular vectors of `A`, `K` is the
pseudoinverse of the best rank-`r` approximation, `‖K‖₂ = 1 / σ_r(A)`). Then
`‖(1 - T) P‖₂ ≤ ‖A - Y‖₂ ‖K‖₂`. -/
theorem specNorm_compl_mul_le_of_mul_eq [DecidableEq n] {T P : Matrix m m ℝ}
    (hT : IsOrthProjMat T) {Y A : Matrix m n ℝ} {K : Matrix n m ℝ} (hY : T * Y = Y)
    (hP : P = A * K) : specNorm ((1 - T) * P) ≤ specNorm (A - Y) * specNorm K := by
  have e : (1 - T) * P = (1 - T) * (A - Y) * K := by
    rw [hP, Matrix.mul_sub (1 - T) A Y, Matrix.sub_mul 1 T Y, Matrix.one_mul, hY, sub_self,
      sub_zero, Matrix.mul_assoc]
  rw [e]
  calc specNorm ((1 - T) * (A - Y) * K)
      ≤ specNorm ((1 - T) * (A - Y)) * specNorm K := specNorm_mul_le _ _
    _ ≤ specNorm (A - Y) * specNorm K :=
      mul_le_mul_of_nonneg_right ((specNorm_mul_le _ _).trans
        (mul_le_of_le_one_left (specNorm_nonneg _) hT.compl.specNorm_le_one)) (specNorm_nonneg _)

/-! ### The run bounds with the data and the angles -/

section Run

variable {N : ℕ} {Y W A g δ : ℕ → Matrix m n ℝ} {T P : ℕ → Matrix m m ℝ} {γ s : ℕ → ℝ}

/-- **Run bound for the error inside the range with the data of a second family of ranges.** In
the setting of `ImplicitBUGStiffColumnSpace.norm_sub_proj_mul_le_add_sum_of_backwardEuler` let
`P_j` be orthogonal projectors with `‖P_{j+1} (1 - P_j)‖₂ ≤ γ_j`, and let `s_j` bound the sine of
the largest angle between the ranges of `T_j` and `P_j`: `‖(1 - T_j) P_j‖₂ ≤ s_j` and
`‖T_j (1 - P_j)‖₂ ≤ s_j`. Then

  `‖Y_N - T_N A_N‖ ≤ ‖Y₀ - T₀ A₀‖ + ∑_{j<N} ((h μ + γ_j + s_j + s_{j+1})`
  `    (‖A_j - P_j A_j‖ + s_j ‖P_j A_j‖) + ‖δ_j‖ + ‖Y_{j+1} - T_{j+1} W_j‖)`.

For the projectors `P_j` onto the dominant left singular vectors of `A_j` the terms
`‖A_j - P_j A_j‖` are the errors of the best approximation and `γ_j` is a quantity of the data. -/
theorem norm_sub_proj_mul_le_add_sum_of_backwardEuler_of_specNorm_le
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 ≤ h)
    (hT : ∀ j ≤ N, IsOrthProjMat (T j)) (hP : ∀ j ≤ N, IsOrthProjMat (P j))
    (hW : ∀ j < N, W j - h • (M * W j) + h • (W j * (Cᵀ * C)) = Y j + g j)
    (hA : ∀ j < N,
      A (j + 1) - h • (M * A (j + 1)) + h • (A (j + 1) * (Cᵀ * C)) = A j + g j + δ j)
    (hγ : ∀ j < N, specNorm (P (j + 1) * (1 - P j)) ≤ γ j)
    (hs : ∀ j ≤ N, specNorm ((1 - T j) * P j) ≤ s j)
    (hs' : ∀ j ≤ N, specNorm (T j * (1 - P j)) ≤ s j) :
    ‖Y N - T N * A N‖ ≤ ‖Y 0 - T 0 * A 0‖ + ∑ j ∈ range N,
      ((h * μ + (γ j + s j + s (j + 1))) * (‖A j - P j * A j‖ + s j * ‖P j * A j‖) + ‖δ j‖ +
        ‖Y (j + 1) - T (j + 1) * W j‖) := by
  have hrot : ∀ j < N, specNorm (T (j + 1) * (1 - T j)) ≤ γ j + s (j + 1) + s j := fun j hj => by
    have h1 := specNorm_proj_mul_compl_le (P₀ := P j) (hT j hj.le) (hT (j + 1) hj)
      (hP (j + 1) hj)
    have h2 : specNorm (P j * (1 - T j)) = specNorm ((1 - T j) * P j) := by
      rw [← specNorm_transpose ((1 - T j) * P j), Matrix.transpose_mul, Matrix.transpose_sub,
        Matrix.transpose_one, (hT j hj.le).symm, (hP j hj.le).symm]
    have h3 := hγ j hj
    have h4 := hs' (j + 1) hj
    have h5 := hs j hj.le
    linarith
  refine (norm_sub_proj_mul_le_add_sum_of_backwardEuler hdiss hμ0 hμ hh hT hW hA hrot).trans
    (add_le_add le_rfl (Finset.sum_le_sum fun j hj => ?_))
  have hjN : j < N := Finset.mem_range.1 hj
  have h1 := norm_sub_proj_mul_le_add_specNorm_mul (hT j hjN.le) (hP j hjN.le) (A j)
  have h2 : specNorm ((1 - T j) * P j) * ‖P j * A j‖ ≤ s j * ‖P j * A j‖ :=
    mul_le_mul_of_nonneg_right (hs j hjN.le) (norm_nonneg _)
  have hγ0 : 0 ≤ γ j := (specNorm_nonneg _).trans (hγ j hjN)
  have hs0 : 0 ≤ s j := (specNorm_nonneg _).trans (hs j hjN.le)
  have hs1 : 0 ≤ s (j + 1) := (specNorm_nonneg _).trans (hs (j + 1) hjN)
  have hc : 0 ≤ h * μ + (γ j + s (j + 1) + s j) := by
    have := mul_nonneg hh hμ0
    linarith
  have h3 := mul_le_mul_of_nonneg_left (h1.trans (add_le_add le_rfl h2)) hc
  have e : h * μ + (γ j + s j + s (j + 1)) = h * μ + (γ j + s (j + 1) + s j) := by ring
  rw [e]
  linarith

/-- **Run bound for the whole error with the data of a second family of ranges.** In the setting
of `norm_sub_proj_mul_le_add_sum_of_backwardEuler_of_specNorm_le`, if `T_N Y_N = Y_N`, then

  `‖Y_N - A_N‖ ≤ √(B² + (‖A_N - P_N A_N‖ + s_N ‖P_N A_N‖)²)`,

with `B` the right-hand side of that bound. -/
theorem norm_sub_le_sqrt_add_of_backwardEuler_of_specNorm_le
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 ≤ h)
    (hT : ∀ j ≤ N, IsOrthProjMat (T j)) (hP : ∀ j ≤ N, IsOrthProjMat (P j))
    (hYN : T N * Y N = Y N)
    (hW : ∀ j < N, W j - h • (M * W j) + h • (W j * (Cᵀ * C)) = Y j + g j)
    (hA : ∀ j < N,
      A (j + 1) - h • (M * A (j + 1)) + h • (A (j + 1) * (Cᵀ * C)) = A j + g j + δ j)
    (hγ : ∀ j < N, specNorm (P (j + 1) * (1 - P j)) ≤ γ j)
    (hs : ∀ j ≤ N, specNorm ((1 - T j) * P j) ≤ s j)
    (hs' : ∀ j ≤ N, specNorm (T j * (1 - P j)) ≤ s j) :
    ‖Y N - A N‖ ≤ √((‖Y 0 - T 0 * A 0‖ + ∑ j ∈ range N,
      ((h * μ + (γ j + s j + s (j + 1))) * (‖A j - P j * A j‖ + s j * ‖P j * A j‖) + ‖δ j‖ +
        ‖Y (j + 1) - T (j + 1) * W j‖)) ^ 2 + (‖A N - P N * A N‖ + s N * ‖P N * A N‖) ^ 2) := by
  have h1 := norm_sub_proj_mul_le_add_sum_of_backwardEuler_of_specNorm_le hdiss hμ0 hμ hh hT hP
    hW hA hγ hs hs'
  have h2 := norm_sub_proj_mul_le_add_specNorm_mul (hT N le_rfl) (hP N le_rfl) (A N)
  have h3 : specNorm ((1 - T N) * P N) * ‖P N * A N‖ ≤ s N * ‖P N * A N‖ :=
    mul_le_mul_of_nonneg_right (hs N le_rfl) (norm_nonneg _)
  refine Real.le_sqrt_of_sq_le ?_
  rw [sq_norm_sub_eq_sq_norm_sub_proj_mul_add (hT N le_rfl) hYN]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) h1 2)
    (pow_le_pow_left₀ (norm_nonneg _) (h2.trans (add_le_add le_rfl h3)) 2)

end Run

end ImplicitBUGStiffColumnAngle

/-! ### A stationary sequence far from the best approximation, and non-vacuity -/

namespace ImplicitBUGStiffColumnAngleExample

open ImplicitBUGStiffColumnAngle ImplicitBUGStiffColumnSpaceExample

local notation "Aᵍ[" c ", " d ", " δ "]" =>
  (!![δ * d ^ 2 * (1 + c ^ 2), -(c ^ 2 * (1 + d ^ 2)); 1, δ] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Wᵍ[" c ", " d ", " δ "]" =>
  (!![c ^ 2 * d ^ 2 * δ, -(c ^ 2 * d ^ 2); 1, δ] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Yᵍ[" δ "]" => (!![0, 0; 1, δ] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Cᵍ[" c ", " d "]" => (!![c, 0; 0, d] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Tᵍ" => (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Xᵍ[" c ", " d ", " δ "]" =>
  ((!![δ * d ^ 2 * (1 + c ^ 2); 1] : Matrix (Fin 2) (Fin 1) ℝ) *
    (!![1; δ] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ)

local notation "Dᵍ" => (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Hᵍ" => (!![1 / 2, 1 / 2; 1 / 2, 1 / 2] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Bᵍ" => (!![9 / 25, 12 / 25; 12 / 25, 16 / 25] : Matrix (Fin 2) (Fin 2) ℝ)

/-- `diag(0, 1)` is an orthogonal projector. -/
theorem isOrthProjMat_low : IsOrthProjMat Tᵍ := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- `CᵀC = diag(c², d²)` for `C = diag(c, d)`. -/
theorem transpose_mul_self (c d : ℝ) :
    Cᵍ[c, d]ᵀ * Cᵍ[c, d] = !![c ^ 2, 0; 0, d ^ 2] := by
  have e : Cᵍ[c, d]ᵀ = Cᵍ[c, d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [e]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_two]

/-- **The reference is stationary.** With `M = 0`, `C = diag(c, d)`, `h = 1` and the forcing
`g = A CᵀC`, the matrix `A = (δ d² (1 + c²), -c² (1 + d²); 1, δ)` satisfies
`A - h M A + h A CᵀC = A + g + 0`. -/
theorem backwardEuler_reference (c d δ : ℝ) :
    Aᵍ[c, d, δ] - (1 : ℝ) • ((0 : Matrix (Fin 2) (Fin 2) ℝ) * Aᵍ[c, d, δ]) +
      (1 : ℝ) • (Aᵍ[c, d, δ] * (Cᵍ[c, d]ᵀ * Cᵍ[c, d])) =
      Aᵍ[c, d, δ] + Aᵍ[c, d, δ] * (Cᵍ[c, d]ᵀ * Cᵍ[c, d]) + 0 := by
  simp

/-- **The backward Euler step from the stationary sequence.** `W = (c² d² δ, -c² d²; 1, δ)` is the
backward Euler step of the full problem from `Y = (0, 0; 1, δ)`:
`W - h M W + h W CᵀC = Y + g`. -/
theorem backwardEuler_step (c d δ : ℝ) :
    Wᵍ[c, d, δ] - (1 : ℝ) • ((0 : Matrix (Fin 2) (Fin 2) ℝ) * Wᵍ[c, d, δ]) +
      (1 : ℝ) • (Wᵍ[c, d, δ] * (Cᵍ[c, d]ᵀ * Cᵍ[c, d])) =
      Yᵍ[δ] + Aᵍ[c, d, δ] * (Cᵍ[c, d]ᵀ * Cᵍ[c, d]) := by
  rw [transpose_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- **The truncation reproduces the sequence.** `T W = Y` for `T = diag(0, 1)`: the step followed
by the projection onto the second coordinate returns `Y`, without a local error. -/
theorem proj_mul_step (c d δ : ℝ) : Tᵍ * Wᵍ[c, d, δ] = Yᵍ[δ] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The stationary sequence is the part of the reference inside the range: `T A = Y`. -/
theorem proj_mul_reference (c d δ : ℝ) : Tᵍ * Aᵍ[c, d, δ] = Yᵍ[δ] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **The projection is the truncation.** `W Wᵀ = diag(c⁴ d⁴ (1 + δ²), 1 + δ²)`: the rows of `W`
are orthogonal, so the left singular vectors of `W` are the coordinate vectors, and for
`c d < 1` the dominant one is the second: `T W` is the best rank-one approximation of `W`. -/
theorem step_mul_transpose (c d δ : ℝ) :
    Wᵍ[c, d, δ] * Wᵍ[c, d, δ]ᵀ = !![c ^ 4 * d ^ 4 * (1 + δ ^ 2), 0; 0, 1 + δ ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The squared distance of the stationary sequence from the reference. -/
theorem sq_norm_sub_reference (c d δ : ℝ) :
    ‖Yᵍ[δ] - Aᵍ[c, d, δ]‖ ^ 2 = (δ * d ^ 2 * (1 + c ^ 2)) ^ 2 + (c ^ 2 * (1 + d ^ 2)) ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  simp [Fin.sum_univ_two]

/-- **A rank-one approximation of the reference.** The distance of `A` from the rank-one matrix
`(δ d² (1 + c²), 1)ᵀ (1, δ)` is `c² (1 + d²) + δ² d² (1 + c²)`; the error of the best rank-one
approximation is at most this. -/
theorem norm_reference_sub_rankOne (c d δ : ℝ) :
    ‖Aᵍ[c, d, δ] - Xᵍ[c, d, δ]‖ = c ^ 2 * (1 + d ^ 2) + δ ^ 2 * d ^ 2 * (1 + c ^ 2) := by
  have h0 : 0 ≤ c ^ 2 * (1 + d ^ 2) + δ ^ 2 * d ^ 2 * (1 + c ^ 2) := by positivity
  refine (sq_eq_sq₀ (norm_nonneg _) h0).1 ?_
  rw [Frobenius.norm_sq_eq_sum]
  simp [Fin.sum_univ_two, Matrix.vecHead, Function.swap]
  ring

/-- **The stationary sequence is far from the best approximation.** For `d = 1`, `δ = c` with
`0 < c ≤ 1` (the row modes have the rates `c²` and `1`, so `c⁻²` is the condition number of the
stiff operator) and every `K ≥ 0` with `4 K c < 1`, the distance of the stationary sequence `Y`
from the reference `A` exceeds `K` times the distance of `A` from a rank-one matrix. -/
theorem mul_norm_reference_sub_rankOne_lt_norm_sub {c K : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hK0 : 0 ≤ K) (hK : 4 * K * c < 1) :
    K * ‖Aᵍ[c, 1, c] - Xᵍ[c, 1, c]‖ < ‖Yᵍ[c] - Aᵍ[c, 1, c]‖ := by
  have h1 := norm_reference_sub_rankOne c 1 c
  have h2 := sq_norm_sub_reference c 1 c
  have h3 : c ^ 2 ≤ ‖Yᵍ[c] - Aᵍ[c, 1, c]‖ ^ 2 := by
    rw [h2]
    nlinarith [sq_nonneg (c ^ 2), sq_nonneg (c * (1 + c ^ 2)), sq_nonneg c, pow_pos hc 4]
  have h4 : c ≤ ‖Yᵍ[c] - Aᵍ[c, 1, c]‖ :=
    (pow_le_pow_iff_left₀ hc.le (norm_nonneg _) two_ne_zero).1 h3
  have h5 : ‖Aᵍ[c, 1, c] - Xᵍ[c, 1, c]‖ ≤ 4 * c ^ 2 := by
    rw [h1]
    nlinarith [pow_pos hc 2, pow_le_one₀ hc.le hc1 (n := 2)]
  have h6 : K * ‖Aᵍ[c, 1, c] - Xᵍ[c, 1, c]‖ ≤ K * (4 * c ^ 2) :=
    mul_le_mul_of_nonneg_left h5 hK0
  nlinarith

/-- The hypotheses of `norm_sub_proj_mul_le_add_specNorm_mul` and of
`specNorm_proj_mul_compl_le` hold with projectors whose ranges differ. -/
example : ∃ T P : Matrix (Fin 2) (Fin 2) ℝ, IsOrthProjMat T ∧ IsOrthProjMat P ∧
    (1 - T) * P ≠ 0 := by
  refine ⟨Dᵍ, Hᵍ, isOrthProjMat_diag, isOrthProjMat_half, fun hc => ?_⟩
  have := congrFun (congrFun hc 1) 1
  simp [Matrix.mul_apply] at this

/-- The hypotheses of `specNorm_compl_mul_le_of_mul_eq` hold with `A ≠ Y` and a range of `P`
that is not in the range of `T`: `T = Y = diag(1, 0)`, `A = 1`, `P = K` the projector onto the
span of `(1, 1)`. -/
example : ∃ (T P Y A K : Matrix (Fin 2) (Fin 2) ℝ), IsOrthProjMat T ∧ T * Y = Y ∧ P = A * K ∧
    (1 - T) * P ≠ 0 := by
  refine ⟨Dᵍ, Hᵍ, Dᵍ, 1, Hᵍ, isOrthProjMat_diag, isOrthProjMat_diag.idem, (Matrix.one_mul _).symm,
    fun hc => ?_⟩
  have := congrFun (congrFun hc 1) 1
  simp [Matrix.mul_apply] at this

/-- The hypotheses of the run bounds with the data and the angles hold for every `M`, `C` and `h`
with ranges `T_j` that rotate, a second family `P_j` whose range differs from both, and a
reference with a part outside the range of `P₀`: `T₀ = diag(1, 0)`, `T₁` the projector onto the
span of `(1, 1)`, `P_j` the projector onto the span of `(3/5, 4/5)`, `A_j = 1`, `Y_j = T_j`. -/
example (M : Matrix (Fin 2) (Fin 2) ℝ) (C : Matrix (Fin 1) (Fin 2) ℝ) (h : ℝ) :
    ∃ (Y W A g δ : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (T P : ℕ → Matrix (Fin 2) (Fin 2) ℝ)
      (γ s : ℕ → ℝ),
      (∀ j ≤ 1, IsOrthProjMat (T j)) ∧ (∀ j ≤ 1, IsOrthProjMat (P j)) ∧ T 1 * Y 1 = Y 1 ∧
      (∀ j < 1, W j - h • (M * W j) + h • (W j * (Cᵀ * C)) = Y j + g j) ∧
      (∀ j < 1, A (j + 1) - h • (M * A (j + 1)) + h • (A (j + 1) * (Cᵀ * C)) =
        A j + g j + δ j) ∧
      (∀ j < 1, specNorm (P (j + 1) * (1 - P j)) ≤ γ j) ∧
      (∀ j ≤ 1, specNorm ((1 - T j) * P j) ≤ s j) ∧
      (∀ j ≤ 1, specNorm (T j * (1 - P j)) ≤ s j) ∧
      A 0 - P 0 * A 0 ≠ 0 ∧ (1 - T 0) * P 0 ≠ 0 := by
  refine ⟨fun j => if j = 0 then Dᵍ else Hᵍ, fun j => if j = 0 then Dᵍ else Hᵍ, fun _ => 1,
    fun _ => Dᵍ - h • (M * Dᵍ) + h • (Dᵍ * (Cᵀ * C)) - Dᵍ,
    fun _ => 1 - h • (M * 1) + h • (1 * (Cᵀ * C)) -
      (1 + (Dᵍ - h • (M * Dᵍ) + h • (Dᵍ * (Cᵀ * C)) - Dᵍ)),
    fun j => if j = 0 then Dᵍ else Hᵍ, fun _ => Bᵍ, fun _ => specNorm (Bᵍ * (1 - Bᵍ)),
    fun j => specNorm ((1 - (if j = 0 then Dᵍ else Hᵍ)) * Bᵍ) +
      specNorm ((if j = 0 then Dᵍ else Hᵍ) * (1 - Bᵍ)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j _
    by_cases hj : j = 0
    · simp only [hj, ite_true]; exact isOrthProjMat_diag
    · simp only [hj, ite_false]; exact isOrthProjMat_half
  · intro j _
    exact isOrthProjMat_start
  · simp only [one_ne_zero, ite_false]
    exact isOrthProjMat_half.idem
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp only [ite_true]
    abel
  · intro j hj
    exact (add_sub_cancel _ _).symm
  · intro j hj
    exact le_rfl
  · intro j _
    exact le_add_of_nonneg_right (specNorm_nonneg _)
  · intro j _
    exact le_add_of_nonneg_left (specNorm_nonneg _)
  · intro hc
    have := congrFun (congrFun hc 0) 1
    simp at this
  · simp only [ite_true]
    intro hc
    have := congrFun (congrFun hc 1) 1
    simp [Matrix.mul_apply] at this

end ImplicitBUGStiffColumnAngleExample

end LeanDLRA
