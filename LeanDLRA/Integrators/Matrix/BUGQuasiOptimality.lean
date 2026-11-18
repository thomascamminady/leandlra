import LeanDLRA.Integrators.Exactness
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Foundations.Gronwall

/-!
# Quasi-optimality of the BUG integrator for given data

For the matrix approximation problem the field is `F(t, Y) = Ȧ(t)` for given data `A(t)`, and one
step of the BUG integrator of [CerutiLubich2022] from `Y₀` with the orthogonal projectors `P₀`,
`Q₀` onto its column and row space is

  `Y₁ = P₁ (Y₀ + (A₁ - A₀)) Q₁`,

where the range of `P₁` contains the range of `(Y₀ + (A₁ - A₀)) Q₀` (K-step) and the range of `Q₁`
contains the row space of `P₀ (Y₀ + (A₁ - A₀))` (L-step). This file compares `Y₁` with a reference
`X₁` of rank `r`, for example the truncated singular value decomposition of `A₁`, and bounds
`‖Y₁ - X₁‖` by `‖Y₀ - X₀‖` and the spectral norm of the tail `A₁ - X₁` times the increment of the
reference. All norms `‖·‖` are Frobenius norms and `‖·‖₂` is the spectral norm.

The references are described by generalized inverses: `X G X = X` with `X G` and `G X` symmetric
(the orthogonal projectors onto the column and the row space of `X`) and `‖G‖₂ ≤ g`, so that
`g⁻¹` is a lower bound of the smallest nonzero singular value of `X`; the tail `A - X` is
orthogonal to the column and the row space of `X` (`(A - X) G = 0`, `G (A - X) = 0`), as it is for
the truncated singular value decomposition.

## Main results

* `MatrixBUG.projStep_eq_add_sub`: the step is
  `Y₁ = Y₀ + D - (1 - P₁) D (1 - Q₀) - P₁ (1 - P₀) D (1 - Q₁)` with `D = A₁ - A₀`.
* `MatrixBUG.norm_one_sub_mul_le_of_capture`, `MatrixBUG.norm_mul_one_sub_le_of_capture`: the new
  bases capture the reference up to the mismatch `Y₀ + D - X₁ = (Y₀ - X₀) + ΔR`,
  `ΔR = (A₁ - X₁) - (A₀ - X₀)`, seen from the old bases. For `Y₀ = A₀` and `A₁ = X₁` this is the
  capture lemma behind the exactness property.
* `MatrixBUG.norm_projStep_sub_le`: `‖Y₁ - X₁‖ ≤ ‖Y₀ - X₀‖ + ‖P₁ ΔR Q₁‖ + ‖ΔR Q₀‖ + ‖P₀ ΔR‖
  + g ξ (‖(1 - P₁) X₁‖ + ‖X₁ (1 - Q₁)‖ + 2 ‖Y₀ - X₀‖)` with `ξ ≥ ‖X₁ - X₀‖₂`.
* `MatrixBUG.norm_tail_sub_mul_le`, `MatrixBUG.norm_mul_tail_sub_le`: the tail increment seen from
  the old bases, `‖ΔR Q₀‖ ≤ δ γ ‖Y₀ - X₀‖ + τ g ‖X₁ - X₀‖` with `δ ≥ ‖ΔR‖₂`, `τ ≥ ‖A₁ - X₁‖₂` and
  `γ ≥ ‖G_Y‖₂` for a generalized inverse of `Y₀`.
* `MatrixBUG.norm_projStep_sub_le_tail`: the one-step bound
  `‖Y₁ - X₁‖ ≤ a ‖Y₀ - X₀‖ + 2 (2 + c g ξ) τ g ‖X₁ - X₀‖ + d_K d_L ‖ΔR‖` with
  `a = 1 + 2 (1 + c) g ξ + 2 (2 + c g ξ) δ γ`.
* `MatrixBUG.norm_projRun_sub_le`: `N` steps,
  `‖Y_n - X_n‖ ≤ aⁿ ‖Y₀ - X₀‖ + ∑_{k<n} a^{n-1-k} b_k`.
* `Exactness.IsBUGIncrementStep.norm_sub_le_tail`: the one-step bound for the factors of the BUG
  step.

## Implementation notes

In the bound `τ ‖X₁ - X₀‖` is the tail times the path length of the reference in one step, so the
sum over the steps is a Riemann sum of `∫ σ_{r+1}(A) ‖Ẋ‖ dt` for the truncated singular value
decomposition. The term `d_K d_L ‖ΔR‖` has the sines `d_K ≥ ‖P₁ (1 - P₀)‖₂`,
`d_L ≥ ‖(1 - Q₀) Q₁‖₂` of the angles between the old and the new bases; both are of the size of the
step. All terms vanish with the tail, which is the exactness property of [CerutiLubich2022,
Theorem 3] and [LubichOseledets2014, Theorem 4.1]. The robust error bound of
[CerutiLubich2022, Theorem 4] has the normal component of the field in place of the tail; for
given data this is the size of the derivative of the tail. Here the derivative of the tail enters
only through `δ` in the factor `a`. The constants `c ≥ ‖M‖₂, ‖N‖₂` bound the inverses of the
overlaps between the old bases and the new reference (`X₁ Q₀ M = X₁`, `N P₀ X₁ = X₁`); they are
the reciprocals of the cosines of the largest angles, as in the non-degeneracy assumption of the
exactness property.

The continuous counterpart is `dlra_norm_sub_truncation_le_integral_of_singularValues_le` in
`LeanDLRA/DLRA/QuasiOptimalitySpectral.lean`.

`MatrixBUG.projStep_eq_add_sub` is `DataDriven.bug_err_succ` of
`LeanDLRA/Research/DataDrivenErrorRecursion.lean` for matrices and projectors given as matrices.
The augmented step before the truncation satisfies the same captures, but there `d_K` and `d_L`
are not small, and the truncation is not treated here.

## References

* [CerutiLubich2022]
* [LubichOseledets2014]
-/

open Finset Matrix
open scoped LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixBUG

open Curvature

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-! ### The step in terms of the increment -/

section Step

variable {P P₀ : Matrix m m ℝ} {Q Q₀ : Matrix n n ℝ} {Y₀ D : Matrix m n ℝ}

/-- The K-step capture `P₁ (Y₀ + D) Q₀ = (Y₀ + D) Q₀` and `Y₀ Q₀ = Y₀` give
`(1 - P₁) (Y₀ + D) = (1 - P₁) D (1 - Q₀)`. -/
theorem one_sub_mul_step_eq (hY₀Q : Y₀ * Q₀ = Y₀)
    (hK : P * ((Y₀ + D) * Q₀) = (Y₀ + D) * Q₀) :
    (1 - P) * (Y₀ + D) = (1 - P) * D * (1 - Q₀) := by
  have h1 : (1 - P) * ((Y₀ + D) * Q₀) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hK, sub_self]
  have h2 : (Y₀ + D) * (1 - Q₀) = D * (1 - Q₀) := by
    rw [Matrix.add_mul, Matrix.mul_sub Y₀, Matrix.mul_one, hY₀Q, sub_self, zero_add]
  calc (1 - P) * (Y₀ + D)
      = (1 - P) * ((Y₀ + D) * Q₀) + (1 - P) * ((Y₀ + D) * (1 - Q₀)) := by
        rw [← Matrix.mul_add, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]
    _ = (1 - P) * D * (1 - Q₀) := by rw [h1, h2, zero_add, Matrix.mul_assoc]

/-- The L-step capture `P₀ (Y₀ + D) Q₁ = P₀ (Y₀ + D)` and `P₀ Y₀ = Y₀` give
`(Y₀ + D) (1 - Q₁) = (1 - P₀) D (1 - Q₁)`. -/
theorem step_mul_one_sub_eq (hY₀P : P₀ * Y₀ = Y₀)
    (hL : P₀ * (Y₀ + D) * Q = P₀ * (Y₀ + D)) :
    (Y₀ + D) * (1 - Q) = (1 - P₀) * D * (1 - Q) := by
  have h1 : P₀ * (Y₀ + D) * (1 - Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hL, sub_self]
  have h2 : (1 - P₀) * (Y₀ + D) = (1 - P₀) * D := by
    rw [Matrix.mul_add, Matrix.sub_mul 1 P₀ Y₀, Matrix.one_mul, hY₀P, sub_self, zero_add]
  calc (Y₀ + D) * (1 - Q)
      = P₀ * (Y₀ + D) * (1 - Q) + (1 - P₀) * (Y₀ + D) * (1 - Q) := by
        rw [← Matrix.add_mul, ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
    _ = (1 - P₀) * D * (1 - Q) := by rw [h1, h2, zero_add]

/-- **The BUG step for given data in terms of the increment.** With the captures of the K- and
the L-step, `P₁ (Y₀ + D) Q₁ = Y₀ + D - (1 - P₁) D (1 - Q₀) - P₁ (1 - P₀) D (1 - Q₁)`. -/
theorem projStep_eq_add_sub (hY₀P : P₀ * Y₀ = Y₀) (hY₀Q : Y₀ * Q₀ = Y₀)
    (hK : P * ((Y₀ + D) * Q₀) = (Y₀ + D) * Q₀) (hL : P₀ * (Y₀ + D) * Q = P₀ * (Y₀ + D)) :
    P * (Y₀ + D) * Q =
      Y₀ + D - (1 - P) * D * (1 - Q₀) - P * ((1 - P₀) * D * (1 - Q)) := by
  have e : P * (Y₀ + D) * Q = Y₀ + D - (1 - P) * (Y₀ + D) - P * ((Y₀ + D) * (1 - Q)) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  rw [e, one_sub_mul_step_eq hY₀Q hK, step_mul_one_sub_eq hY₀P hL]

end Step

/-! ### Capture of a reference of rank `r` up to the mismatch -/

section Capture

variable {P P₀ N : Matrix m m ℝ} {Q Q₀ M : Matrix n n ℝ} {Y₀ D X₁ : Matrix m n ℝ}

/-- **Capture with a tail (K-step).** If the range of `P₁` contains the range of `(Y₀ + D) Q₀` and
the row space of `X₁` is reached from the old row space, `X₁ Q₀ M = X₁`, then
`‖(1 - P₁) X₁‖ ≤ ‖(Y₀ + D - X₁) Q₀‖ ‖M‖₂`. For `Y₀ + D = X₁` this is the capture lemma of the
exactness property ([CerutiLubich2022, Lemma 1]). -/
theorem norm_one_sub_mul_le_of_capture (hP : IsOrthProjMat P)
    (hK : P * ((Y₀ + D) * Q₀) = (Y₀ + D) * Q₀) (hM : X₁ * Q₀ * M = X₁) :
    ‖(1 - P) * X₁‖ ≤ ‖(Y₀ + D - X₁) * Q₀‖ * specNorm M := by
  have h0 : (1 - P) * ((Y₀ + D) * Q₀) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hK, sub_self]
  have h1 : (1 - P) * X₁ = -((1 - P) * ((Y₀ + D - X₁) * Q₀) * M) :=
    calc (1 - P) * X₁ = (1 - P) * (X₁ * Q₀ * M) := by rw [hM]
      _ = (1 - P) * (X₁ * Q₀) * M := (Matrix.mul_assoc _ _ _).symm
      _ = -((1 - P) * ((Y₀ + D - X₁) * Q₀)) * M := by
        rw [Matrix.sub_mul (Y₀ + D) X₁ Q₀, Matrix.mul_sub, h0, zero_sub, neg_neg]
      _ = -((1 - P) * ((Y₀ + D - X₁) * Q₀) * M) := Matrix.neg_mul _ _
  rw [h1, norm_neg]
  exact (frob_mul_le' _ _).trans
    (mul_le_mul_of_nonneg_right (hP.compl.norm_mul_le _) (specNorm_nonneg M))

/-- **Capture with a tail (L-step).** If the range of `Q₁` contains the row space of
`P₀ (Y₀ + D)` and the column space of `X₁` is reached from the old column space,
`N P₀ X₁ = X₁`, then `‖X₁ (1 - Q₁)‖ ≤ ‖N‖₂ ‖P₀ (Y₀ + D - X₁)‖`. -/
theorem norm_mul_one_sub_le_of_capture (hQ : IsOrthProjMat Q)
    (hL : P₀ * (Y₀ + D) * Q = P₀ * (Y₀ + D)) (hN : N * P₀ * X₁ = X₁) :
    ‖X₁ * (1 - Q)‖ ≤ specNorm N * ‖P₀ * (Y₀ + D - X₁)‖ := by
  have h0 : P₀ * (Y₀ + D) * (1 - Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hL, sub_self]
  have h1 : X₁ * (1 - Q) = -(N * (P₀ * (Y₀ + D - X₁) * (1 - Q))) :=
    calc X₁ * (1 - Q) = N * P₀ * X₁ * (1 - Q) := by rw [hN]
      _ = N * (P₀ * X₁ * (1 - Q)) := by simp only [Matrix.mul_assoc]
      _ = N * -(P₀ * (Y₀ + D - X₁) * (1 - Q)) := by
        rw [Matrix.mul_sub P₀ (Y₀ + D) X₁, Matrix.sub_mul, h0, zero_sub, neg_neg]
      _ = -(N * (P₀ * (Y₀ + D - X₁) * (1 - Q))) := Matrix.mul_neg _ _
  rw [h1, norm_neg]
  exact (frob_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (hQ.compl.norm_mul_le' _) (specNorm_nonneg N))

end Capture

/-! ### The increment of the reference is almost tangent -/

section Tangent

variable {X₀ X₁ : Matrix m n ℝ} {G₀ G₁ : Matrix n m ℝ}

omit [DecidableEq n] in
/-- The part of `X₁ - X₀` outside the column space of `X₁` has its rows in the row space of
`X₀`. -/
theorem one_sub_colProj_mul_sub_eq (hX₀ : X₀ * G₀ * X₀ = X₀) (hX₁ : X₁ * G₁ * X₁ = X₁) :
    (1 - X₁ * G₁) * (X₁ - X₀) = (1 - X₁ * G₁) * (X₁ - X₀) * (G₀ * X₀) := by
  have a : (1 - X₁ * G₁) * X₁ = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hX₁, sub_self]
  have b : X₀ * (G₀ * X₀) = X₀ := by rw [← Matrix.mul_assoc, hX₀]
  rw [Matrix.mul_assoc (1 - X₁ * G₁) (X₁ - X₀) (G₀ * X₀), Matrix.sub_mul X₁ X₀ (G₀ * X₀), b,
    Matrix.mul_sub (1 - X₁ * G₁) (X₁ * (G₀ * X₀)) X₀,
    ← Matrix.mul_assoc (1 - X₁ * G₁) X₁ (G₀ * X₀), Matrix.mul_sub (1 - X₁ * G₁) X₁ X₀, a,
    Matrix.zero_mul]

omit [DecidableEq m] in
/-- The part of `X₁ - X₀` outside the row space of `X₁` has its columns in the column space of
`X₀`. -/
theorem sub_mul_one_sub_rowProj_eq (hX₀ : X₀ * G₀ * X₀ = X₀) (hX₁ : X₁ * G₁ * X₁ = X₁) :
    (X₁ - X₀) * (1 - G₁ * X₁) = X₀ * G₀ * ((X₁ - X₀) * (1 - G₁ * X₁)) := by
  have a : X₁ * (1 - G₁ * X₁) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hX₁, sub_self]
  rw [Matrix.sub_mul X₁ X₀ (1 - G₁ * X₁), a, zero_sub, Matrix.mul_neg,
    ← Matrix.mul_assoc (X₀ * G₀) X₀ (1 - G₁ * X₁), hX₀]


omit [DecidableEq m] in
/-- `‖A B‖₂ ≤ a b` from `‖A‖₂ ≤ a` and `‖B‖₂ ≤ b`. -/
private theorem specNorm_mul_le_mul {k : Type*} [Fintype k] [DecidableEq k] {A : Matrix m n ℝ}
    {B : Matrix n k ℝ} {a b : ℝ} (hA : specNorm A ≤ a) (hB : specNorm B ≤ b) :
    specNorm (A * B) ≤ a * b :=
  (specNorm_mul_le A B).trans
    (mul_le_mul hA hB (specNorm_nonneg B) ((specNorm_nonneg A).trans hA))

variable {P P₀ : Matrix m m ℝ} {Q Q₀ : Matrix n n ℝ} {Y₀ : Matrix m n ℝ} {g ξ : ℝ}

/-- **The increment of the reference between the new left and the old right basis.** With
`‖G₀‖₂, ‖G₁‖₂ ≤ g` and `‖X₁ - X₀‖₂ ≤ ξ`,
`‖(1 - P₁) (X₁ - X₀) (1 - Q₀)‖ ≤ g ξ (‖(1 - P₁) X₁‖ + ‖Y₀ - X₀‖)`. -/
theorem norm_one_sub_mul_sub_mul_one_sub_le (hP : IsOrthProjMat P) (hQ₀ : IsOrthProjMat Q₀)
    (hY₀Q : Y₀ * Q₀ = Y₀) (hX₀ : X₀ * G₀ * X₀ = X₀) (hX₁ : X₁ * G₁ * X₁ = X₁)
    (hc₁ : (X₁ * G₁)ᵀ = X₁ * G₁) (hG₀ : specNorm G₀ ≤ g) (hG₁ : specNorm G₁ ≤ g)
    (hξ : specNorm (X₁ - X₀) ≤ ξ) :
    ‖(1 - P) * (X₁ - X₀) * (1 - Q₀)‖ ≤ g * ξ * (‖(1 - P) * X₁‖ + ‖Y₀ - X₀‖) := by
  have dec : X₁ - X₀ =
      X₁ * (G₁ * (X₁ - X₀)) + (1 - X₁ * G₁) * (X₁ - X₀) * (G₀ * X₀) := by
    rw [← one_sub_colProj_mul_sub_eq hX₀ hX₁, Matrix.sub_mul 1 (X₁ * G₁) (X₁ - X₀),
      Matrix.one_mul, Matrix.mul_assoc X₁ G₁ (X₁ - X₀)]
    abel
  have hx0 : (Y₀ - X₀) * (1 - Q₀) = -(X₀ * (1 - Q₀)) := by
    rw [Matrix.sub_mul Y₀ X₀, Matrix.mul_sub Y₀ 1 Q₀, Matrix.mul_one, hY₀Q, sub_self, zero_sub]
  have split : (1 - P) * (X₁ - X₀) * (1 - Q₀) =
      (1 - P) * X₁ * (G₁ * (X₁ - X₀) * (1 - Q₀)) +
        -((1 - P) * ((1 - X₁ * G₁) * (X₁ - X₀) * G₀ * ((Y₀ - X₀) * (1 - Q₀)))) :=
    calc (1 - P) * (X₁ - X₀) * (1 - Q₀)
        = (1 - P) * (X₁ * (G₁ * (X₁ - X₀)) + (1 - X₁ * G₁) * (X₁ - X₀) * (G₀ * X₀)) *
            (1 - Q₀) := by rw [← dec]
      _ = _ := by
        rw [Matrix.mul_add, Matrix.add_mul]
        congr 1
        · simp only [Matrix.mul_assoc]
        · rw [hx0, Matrix.mul_neg, Matrix.mul_neg, neg_neg]
          simp only [Matrix.mul_assoc]
  have h1 : specNorm (G₁ * (X₁ - X₀) * (1 - Q₀)) ≤ g * ξ * 1 :=
    specNorm_mul_le_mul (specNorm_mul_le_mul hG₁ hξ) hQ₀.compl.specNorm_le_one
  have h2 : specNorm ((1 - X₁ * G₁) * (X₁ - X₀) * G₀) ≤ 1 * ξ * g :=
    specNorm_mul_le_mul
      (specNorm_mul_le_mul (isOrthProjMat_colProj hX₁ hc₁).compl.specNorm_le_one hξ) hG₀
  have n1 : ‖(1 - P) * X₁ * (G₁ * (X₁ - X₀) * (1 - Q₀))‖ ≤ ‖(1 - P) * X₁‖ * (g * ξ * 1) :=
    (frob_mul_le' _ _).trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
  have n2 : ‖(1 - P) * ((1 - X₁ * G₁) * (X₁ - X₀) * G₀ * ((Y₀ - X₀) * (1 - Q₀)))‖ ≤
      1 * ξ * g * ‖Y₀ - X₀‖ :=
    calc ‖(1 - P) * ((1 - X₁ * G₁) * (X₁ - X₀) * G₀ * ((Y₀ - X₀) * (1 - Q₀)))‖
        ≤ ‖(1 - X₁ * G₁) * (X₁ - X₀) * G₀ * ((Y₀ - X₀) * (1 - Q₀))‖ := hP.compl.norm_mul_le _
      _ ≤ specNorm ((1 - X₁ * G₁) * (X₁ - X₀) * G₀) * ‖(Y₀ - X₀) * (1 - Q₀)‖ := frob_mul_le _ _
      _ ≤ 1 * ξ * g * ‖Y₀ - X₀‖ :=
        mul_le_mul h2 (hQ₀.compl.norm_mul_le' _) (norm_nonneg _)
          ((specNorm_nonneg _).trans h2)
  rw [split]
  have n3 := norm_add_le ((1 - P) * X₁ * (G₁ * (X₁ - X₀) * (1 - Q₀)))
    (-((1 - P) * ((1 - X₁ * G₁) * (X₁ - X₀) * G₀ * ((Y₀ - X₀) * (1 - Q₀)))))
  rw [norm_neg] at n3
  linarith

/-- **The increment of the reference between the old left and the new right basis.**
`‖P₁ (1 - P₀) (X₁ - X₀) (1 - Q₁)‖ ≤ g ξ (‖X₁ (1 - Q₁)‖ + ‖Y₀ - X₀‖)`. -/
theorem norm_mul_one_sub_mul_sub_mul_one_sub_le (hP : IsOrthProjMat P)
    (hP₀ : IsOrthProjMat P₀) (hQ : IsOrthProjMat Q) (hY₀P : P₀ * Y₀ = Y₀)
    (hX₀ : X₀ * G₀ * X₀ = X₀) (hX₁ : X₁ * G₁ * X₁ = X₁) (hr₁ : (G₁ * X₁)ᵀ = G₁ * X₁)
    (hG₀ : specNorm G₀ ≤ g) (hG₁ : specNorm G₁ ≤ g) (hξ : specNorm (X₁ - X₀) ≤ ξ) :
    ‖P * ((1 - P₀) * (X₁ - X₀) * (1 - Q))‖ ≤ g * ξ * (‖X₁ * (1 - Q)‖ + ‖Y₀ - X₀‖) := by
  have dec : X₁ - X₀ =
      (X₁ - X₀) * G₁ * X₁ + X₀ * G₀ * ((X₁ - X₀) * (1 - G₁ * X₁)) := by
    rw [← sub_mul_one_sub_rowProj_eq hX₀ hX₁, Matrix.mul_sub (X₁ - X₀) 1 (G₁ * X₁),
      Matrix.mul_one, ← Matrix.mul_assoc (X₁ - X₀) G₁ X₁]
    abel
  have hx0 : (1 - P₀) * (Y₀ - X₀) = -((1 - P₀) * X₀) := by
    rw [Matrix.mul_sub (1 - P₀) Y₀ X₀, Matrix.sub_mul 1 P₀ Y₀, Matrix.one_mul, hY₀P, sub_self,
      zero_sub]
  have split : (1 - P₀) * (X₁ - X₀) * (1 - Q) =
      (1 - P₀) * (X₁ - X₀) * G₁ * (X₁ * (1 - Q)) +
        -((1 - P₀) * (Y₀ - X₀) * (G₀ * ((X₁ - X₀) * (1 - G₁ * X₁))) * (1 - Q)) :=
    calc (1 - P₀) * (X₁ - X₀) * (1 - Q)
        = (1 - P₀) * ((X₁ - X₀) * G₁ * X₁ + X₀ * G₀ * ((X₁ - X₀) * (1 - G₁ * X₁))) *
            (1 - Q) := by rw [← dec]
      _ = _ := by
        rw [Matrix.mul_add, Matrix.add_mul]
        congr 1
        · simp only [Matrix.mul_assoc]
        · rw [hx0, Matrix.neg_mul, Matrix.neg_mul, neg_neg]
          simp only [Matrix.mul_assoc]
  have h1 : specNorm ((1 - P₀) * (X₁ - X₀) * G₁) ≤ 1 * ξ * g :=
    specNorm_mul_le_mul (specNorm_mul_le_mul hP₀.compl.specNorm_le_one hξ) hG₁
  have h2 : specNorm (G₀ * ((X₁ - X₀) * (1 - G₁ * X₁))) ≤ g * (ξ * 1) :=
    specNorm_mul_le_mul hG₀
      (specNorm_mul_le_mul hξ (isOrthProjMat_rowProj hX₁ hr₁).compl.specNorm_le_one)
  have n1 : ‖(1 - P₀) * (X₁ - X₀) * G₁ * (X₁ * (1 - Q))‖ ≤ 1 * ξ * g * ‖X₁ * (1 - Q)‖ :=
    (frob_mul_le _ _).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
  have n2 : ‖(1 - P₀) * (Y₀ - X₀) * (G₀ * ((X₁ - X₀) * (1 - G₁ * X₁))) * (1 - Q)‖ ≤
      ‖Y₀ - X₀‖ * (g * (ξ * 1)) :=
    calc ‖(1 - P₀) * (Y₀ - X₀) * (G₀ * ((X₁ - X₀) * (1 - G₁ * X₁))) * (1 - Q)‖
        ≤ ‖(1 - P₀) * (Y₀ - X₀) * (G₀ * ((X₁ - X₀) * (1 - G₁ * X₁)))‖ :=
          hQ.compl.norm_mul_le' _
      _ ≤ ‖(1 - P₀) * (Y₀ - X₀)‖ * specNorm (G₀ * ((X₁ - X₀) * (1 - G₁ * X₁))) :=
          frob_mul_le' _ _
      _ ≤ ‖Y₀ - X₀‖ * (g * (ξ * 1)) :=
        mul_le_mul (hP₀.compl.norm_mul_le _) h2 (specNorm_nonneg _) (norm_nonneg _)
  have n3 := hP.norm_mul_le ((1 - P₀) * (X₁ - X₀) * (1 - Q))
  rw [split] at n3 ⊢
  have n4 := norm_add_le ((1 - P₀) * (X₁ - X₀) * G₁ * (X₁ * (1 - Q)))
    (-((1 - P₀) * (Y₀ - X₀) * (G₀ * ((X₁ - X₀) * (1 - G₁ * X₁))) * (1 - Q)))
  rw [norm_neg] at n4
  linarith

end Tangent

/-! ### One step against a reference -/

section OneStep

variable {P P₀ : Matrix m m ℝ} {Q Q₀ : Matrix n n ℝ} {Y₀ A₀ A₁ X₀ X₁ : Matrix m n ℝ}
  {G₀ G₁ : Matrix n m ℝ} {g ξ : ℝ}

/-- The error of the step, split into the old error, the tail increment and the increment of the
reference. -/
private theorem err_split (P P₀ : Matrix m m ℝ) (Q Q₀ : Matrix n n ℝ)
    (Y₀ X₀ Dx R : Matrix m n ℝ) :
    Y₀ + (Dx + R) - (1 - P) * (Dx + R) * (1 - Q₀) - P * ((1 - P₀) * (Dx + R) * (1 - Q)) -
        (X₀ + Dx) =
      Y₀ - X₀ + ((1 - P) * (R * Q₀) + P * (P₀ * R) * (1 - Q) + P * R * Q) -
        (1 - P) * Dx * (1 - Q₀) - P * ((1 - P₀) * Dx * (1 - Q)) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_one, Matrix.mul_assoc]
  abel

/-- **One BUG step for given data against a reference.** Let `Y₁ = P₁ (Y₀ + (A₁ - A₀)) Q₁` with
the captures of the K- and the L-step, and let `X₀`, `X₁` have generalized inverses with
`‖G₀‖₂, ‖G₁‖₂ ≤ g` and `‖X₁ - X₀‖₂ ≤ ξ`. With the tail increment
`ΔR = (A₁ - X₁) - (A₀ - X₀)`,

  `‖Y₁ - X₁‖ ≤ ‖Y₀ - X₀‖ + ‖P₁ ΔR Q₁‖ + ‖ΔR Q₀‖ + ‖P₀ ΔR‖
      + g ξ (‖(1 - P₁) X₁‖ + ‖X₁ (1 - Q₁)‖ + 2 ‖Y₀ - X₀‖)`.

The old error enters with the factor `1 + 2 g ξ`, and the increment of the reference only through
the two capture defects of `X₁`. -/
theorem norm_projStep_sub_le (hP : IsOrthProjMat P) (hQ : IsOrthProjMat Q)
    (hP₀ : IsOrthProjMat P₀) (hQ₀ : IsOrthProjMat Q₀) (hY₀P : P₀ * Y₀ = Y₀)
    (hY₀Q : Y₀ * Q₀ = Y₀)
    (hK : P * ((Y₀ + (A₁ - A₀)) * Q₀) = (Y₀ + (A₁ - A₀)) * Q₀)
    (hL : P₀ * (Y₀ + (A₁ - A₀)) * Q = P₀ * (Y₀ + (A₁ - A₀)))
    (hX₀ : X₀ * G₀ * X₀ = X₀) (hX₁ : X₁ * G₁ * X₁ = X₁) (hc₁ : (X₁ * G₁)ᵀ = X₁ * G₁)
    (hr₁ : (G₁ * X₁)ᵀ = G₁ * X₁) (hG₀ : specNorm G₀ ≤ g) (hG₁ : specNorm G₁ ≤ g)
    (hξ : specNorm (X₁ - X₀) ≤ ξ) :
    ‖P * (Y₀ + (A₁ - A₀)) * Q - X₁‖ ≤
      ‖Y₀ - X₀‖ + ‖P * (A₁ - X₁ - (A₀ - X₀)) * Q‖ + ‖(A₁ - X₁ - (A₀ - X₀)) * Q₀‖ +
        ‖P₀ * (A₁ - X₁ - (A₀ - X₀))‖ +
        g * ξ * (‖(1 - P) * X₁‖ + ‖X₁ * (1 - Q)‖ + 2 * ‖Y₀ - X₀‖) := by
  have e1 : A₁ - A₀ = X₁ - X₀ + (A₁ - X₁ - (A₀ - X₀)) := by abel
  have e2 : X₁ = X₀ + (X₁ - X₀) := by abel
  have key : P * (Y₀ + (A₁ - A₀)) * Q - X₁ =
      Y₀ - X₀ + ((1 - P) * ((A₁ - X₁ - (A₀ - X₀)) * Q₀) +
        P * (P₀ * (A₁ - X₁ - (A₀ - X₀))) * (1 - Q) + P * (A₁ - X₁ - (A₀ - X₀)) * Q) -
        (1 - P) * (X₁ - X₀) * (1 - Q₀) - P * ((1 - P₀) * (X₁ - X₀) * (1 - Q)) := by
    rw [projStep_eq_add_sub hY₀P hY₀Q hK hL]
    have h := err_split P P₀ Q Q₀ Y₀ X₀ (X₁ - X₀) (A₁ - X₁ - (A₀ - X₀))
    rwa [← e1, ← e2] at h
  have t1 := norm_one_sub_mul_sub_mul_one_sub_le hP hQ₀ hY₀Q hX₀ hX₁ hc₁ hG₀ hG₁ hξ
  have t2 := norm_mul_one_sub_mul_sub_mul_one_sub_le hP hP₀ hQ hY₀P hX₀ hX₁ hr₁ hG₀ hG₁ hξ
  have r1 : ‖(1 - P) * ((A₁ - X₁ - (A₀ - X₀)) * Q₀)‖ ≤ ‖(A₁ - X₁ - (A₀ - X₀)) * Q₀‖ :=
    hP.compl.norm_mul_le _
  have r2 : ‖P * (P₀ * (A₁ - X₁ - (A₀ - X₀))) * (1 - Q)‖ ≤ ‖P₀ * (A₁ - X₁ - (A₀ - X₀))‖ :=
    (hQ.compl.norm_mul_le' _).trans (hP.norm_mul_le _)
  rw [key]
  have s1 := norm_sub_le (Y₀ - X₀ + ((1 - P) * ((A₁ - X₁ - (A₀ - X₀)) * Q₀) +
      P * (P₀ * (A₁ - X₁ - (A₀ - X₀))) * (1 - Q) + P * (A₁ - X₁ - (A₀ - X₀)) * Q) -
      (1 - P) * (X₁ - X₀) * (1 - Q₀)) (P * ((1 - P₀) * (X₁ - X₀) * (1 - Q)))
  have s2 := norm_sub_le (Y₀ - X₀ + ((1 - P) * ((A₁ - X₁ - (A₀ - X₀)) * Q₀) +
      P * (P₀ * (A₁ - X₁ - (A₀ - X₀))) * (1 - Q) + P * (A₁ - X₁ - (A₀ - X₀)) * Q))
      ((1 - P) * (X₁ - X₀) * (1 - Q₀))
  have s3 := norm_add_le (Y₀ - X₀) ((1 - P) * ((A₁ - X₁ - (A₀ - X₀)) * Q₀) +
      P * (P₀ * (A₁ - X₁ - (A₀ - X₀))) * (1 - Q) + P * (A₁ - X₁ - (A₀ - X₀)) * Q)
  have s4 := norm_add_le ((1 - P) * ((A₁ - X₁ - (A₀ - X₀)) * Q₀) +
      P * (P₀ * (A₁ - X₁ - (A₀ - X₀))) * (1 - Q)) (P * (A₁ - X₁ - (A₀ - X₀)) * Q)
  have s5 := norm_add_le ((1 - P) * ((A₁ - X₁ - (A₀ - X₀)) * Q₀))
      (P * (P₀ * (A₁ - X₁ - (A₀ - X₀))) * (1 - Q))
  linarith

end OneStep

/-! ### The tail increment seen from the old bases -/

section Tail

variable {Y₀ X₀ X₁ R₀ R₁ : Matrix m n ℝ} {G₀ G₁ GY : Matrix n m ℝ} {g γ τ δ : ℝ}

/-- **The tail increment on the old row space.** Let the tails `R₀`, `R₁` be orthogonal to the
row spaces of the references (`R₀ G₀ = 0`, `R₁ G₁ = 0`), and let `Q₀ = G_Y Y₀` be the orthogonal
projector onto the row space of `Y₀`. Then

  `‖(R₁ - R₀) Q₀‖ ≤ δ γ ‖Y₀ - X₀‖ + τ g ‖X₁ - X₀‖`

with `δ ≥ ‖R₁ - R₀‖₂`, `γ ≥ ‖G_Y‖₂`, `τ ≥ ‖R₁‖₂` and `g ≥ ‖G₀‖₂`: the tail acts on the old row
space only through the angle between the row spaces of `Y₀` and `X₀` and through the rotation of
the row space of the reference. -/
theorem norm_tail_sub_mul_le {Q₀ : Matrix n n ℝ} (hQ₀ : IsOrthProjMat Q₀) (hGY : GY * Y₀ = Q₀)
    (hX₀ : X₀ * G₀ * X₀ = X₀) (hr₀ : (G₀ * X₀)ᵀ = G₀ * X₀) (hX₁ : X₁ * G₁ * X₁ = X₁)
    (hr₁ : (G₁ * X₁)ᵀ = G₁ * X₁) (hR₀ : R₀ * G₀ = 0) (hR₁ : R₁ * G₁ = 0)
    (hγ : specNorm GY ≤ γ) (hG₀ : specNorm G₀ ≤ g) (hτ : specNorm R₁ ≤ τ)
    (hδ : specNorm (R₁ - R₀) ≤ δ) :
    ‖(R₁ - R₀) * Q₀‖ ≤ δ * γ * ‖Y₀ - X₀‖ + τ * g * ‖X₁ - X₀‖ := by
  have hXt : (1 - G₀ * X₀) * X₀ᵀ = 0 := by
    have h : X₀ᵀ = G₀ * X₀ * X₀ᵀ := by
      conv_lhs => rw [← hX₀]
      rw [Matrix.mul_assoc X₀ G₀ X₀, Matrix.transpose_mul, hr₀]
    rw [Matrix.sub_mul, Matrix.one_mul, ← h, sub_self]
  have hQt : Q₀ = Y₀ᵀ * GYᵀ := by rw [← Matrix.transpose_mul, hGY, hQ₀.symm]
  have h1 : (1 - G₀ * X₀) * Q₀ = (1 - G₀ * X₀) * (Y₀ - X₀)ᵀ * GYᵀ := by
    rw [Matrix.transpose_sub, Matrix.mul_sub, hXt, sub_zero, Matrix.mul_assoc, ← hQt]
  have h2 : (R₁ - R₀) * (G₀ * X₀) = R₁ * ((1 - G₁ * X₁) * (G₀ * X₀)) := by
    rw [Matrix.sub_mul R₁ R₀, ← Matrix.mul_assoc R₀ G₀ X₀, hR₀, Matrix.zero_mul, sub_zero,
      ← Matrix.mul_assoc R₁ (1 - G₁ * X₁), Matrix.mul_sub R₁ 1 (G₁ * X₁), Matrix.mul_one,
      ← Matrix.mul_assoc R₁ G₁ X₁, hR₁, Matrix.zero_mul, sub_zero]
  have h3 : (1 - G₁ * X₁) * (G₀ * X₀) = -(G₀ * ((X₁ - X₀) * (1 - G₁ * X₁)))ᵀ := by
    have a : X₁ * (1 - G₁ * X₁) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hX₁, sub_self]
    have b : G₀ * ((X₁ - X₀) * (1 - G₁ * X₁)) = -(G₀ * X₀ * (1 - G₁ * X₁)) := by
      rw [Matrix.sub_mul X₁ X₀, a, zero_sub, Matrix.mul_neg, Matrix.mul_assoc]
    rw [b, Matrix.transpose_neg, neg_neg, Matrix.transpose_mul, Matrix.transpose_sub,
      Matrix.transpose_one, hr₁, hr₀]
  have dec : (R₁ - R₀) * Q₀ =
      (R₁ - R₀) * ((1 - G₀ * X₀) * (Y₀ - X₀)ᵀ * GYᵀ) +
        -(R₁ * ((G₀ * ((X₁ - X₀) * (1 - G₁ * X₁)))ᵀ * Q₀)) :=
    calc (R₁ - R₀) * Q₀
        = (R₁ - R₀) * ((1 - G₀ * X₀) * Q₀) + (R₁ - R₀) * (G₀ * X₀) * Q₀ := by
          rw [Matrix.sub_mul 1 (G₀ * X₀) Q₀, Matrix.one_mul, Matrix.mul_sub (R₁ - R₀) Q₀,
            Matrix.mul_assoc (R₁ - R₀) (G₀ * X₀) Q₀]
          abel
      _ = _ := by rw [h1, h2, h3, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc R₁]
  have ha : ‖(1 - G₀ * X₀) * (Y₀ - X₀)ᵀ‖ ≤ ‖Y₀ - X₀‖ :=
    ((isOrthProjMat_rowProj hX₀ hr₀).compl.norm_mul_le _).trans_eq (Frobenius.norm_transpose _)
  have hb : specNorm GYᵀ ≤ γ := by rw [specNorm_transpose]; exact hγ
  have hin : ‖(1 - G₀ * X₀) * (Y₀ - X₀)ᵀ * GYᵀ‖ ≤ ‖Y₀ - X₀‖ * γ :=
    (frob_mul_le' _ _).trans (mul_le_mul ha hb (specNorm_nonneg _) (norm_nonneg _))
  have n1 : ‖(R₁ - R₀) * ((1 - G₀ * X₀) * (Y₀ - X₀)ᵀ * GYᵀ)‖ ≤ δ * (‖Y₀ - X₀‖ * γ) :=
    (frob_mul_le _ _).trans
      (mul_le_mul hδ hin (norm_nonneg _) ((specNorm_nonneg _).trans hδ))
  have hz : ‖(G₀ * ((X₁ - X₀) * (1 - G₁ * X₁)))ᵀ * Q₀‖ ≤ g * ‖X₁ - X₀‖ :=
    calc ‖(G₀ * ((X₁ - X₀) * (1 - G₁ * X₁)))ᵀ * Q₀‖
        ≤ ‖(G₀ * ((X₁ - X₀) * (1 - G₁ * X₁)))ᵀ‖ := hQ₀.norm_mul_le' _
      _ = ‖G₀ * ((X₁ - X₀) * (1 - G₁ * X₁))‖ := Frobenius.norm_transpose _
      _ ≤ specNorm G₀ * ‖(X₁ - X₀) * (1 - G₁ * X₁)‖ := frob_mul_le _ _
      _ ≤ g * ‖X₁ - X₀‖ :=
        mul_le_mul hG₀ ((isOrthProjMat_rowProj hX₁ hr₁).compl.norm_mul_le' _) (norm_nonneg _)
          ((specNorm_nonneg _).trans hG₀)
  have n2 : ‖R₁ * ((G₀ * ((X₁ - X₀) * (1 - G₁ * X₁)))ᵀ * Q₀)‖ ≤ τ * (g * ‖X₁ - X₀‖) :=
    (frob_mul_le _ _).trans
      (mul_le_mul hτ hz (norm_nonneg _) ((specNorm_nonneg _).trans hτ))
  rw [dec]
  have n3 := norm_add_le ((R₁ - R₀) * ((1 - G₀ * X₀) * (Y₀ - X₀)ᵀ * GYᵀ))
    (-(R₁ * ((G₀ * ((X₁ - X₀) * (1 - G₁ * X₁)))ᵀ * Q₀)))
  rw [norm_neg] at n3
  linarith

/-- **The tail increment on the old column space.** The transposed statement: with
`G₀ R₀ = 0`, `G₁ R₁ = 0` and the orthogonal projector `P₀ = Y₀ G_Y` onto the column space of `Y₀`,
`‖P₀ (R₁ - R₀)‖ ≤ δ γ ‖Y₀ - X₀‖ + τ g ‖X₁ - X₀‖`. -/
theorem norm_mul_tail_sub_le {P₀ : Matrix m m ℝ} (hP₀ : IsOrthProjMat P₀) (hGY : Y₀ * GY = P₀)
    (hX₀ : X₀ * G₀ * X₀ = X₀) (hc₀ : (X₀ * G₀)ᵀ = X₀ * G₀) (hX₁ : X₁ * G₁ * X₁ = X₁)
    (hc₁ : (X₁ * G₁)ᵀ = X₁ * G₁) (hR₀ : G₀ * R₀ = 0) (hR₁ : G₁ * R₁ = 0)
    (hγ : specNorm GY ≤ γ) (hG₀ : specNorm G₀ ≤ g) (hτ : specNorm R₁ ≤ τ)
    (hδ : specNorm (R₁ - R₀) ≤ δ) :
    ‖P₀ * (R₁ - R₀)‖ ≤ δ * γ * ‖Y₀ - X₀‖ + τ * g * ‖X₁ - X₀‖ := by
  have hX₀' : X₀ᵀ * G₀ᵀ * X₀ᵀ = X₀ᵀ := by
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.mul_assoc, hX₀]
  have hX₁' : X₁ᵀ * G₁ᵀ * X₁ᵀ = X₁ᵀ := by
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.mul_assoc, hX₁]
  have hr₀' : (G₀ᵀ * X₀ᵀ)ᵀ = G₀ᵀ * X₀ᵀ := by rw [← Matrix.transpose_mul, hc₀, hc₀]
  have hr₁' : (G₁ᵀ * X₁ᵀ)ᵀ = G₁ᵀ * X₁ᵀ := by rw [← Matrix.transpose_mul, hc₁, hc₁]
  have h := norm_tail_sub_mul_le (Y₀ := Y₀ᵀ) (X₀ := X₀ᵀ) (X₁ := X₁ᵀ) (R₀ := R₀ᵀ) (R₁ := R₁ᵀ)
    (G₀ := G₀ᵀ) (G₁ := G₁ᵀ) (GY := GYᵀ) (g := g) (γ := γ) (τ := τ) (δ := δ) hP₀
    (by rw [← Matrix.transpose_mul, hGY, hP₀.symm]) hX₀' hr₀' hX₁' hr₁'
    (by rw [← Matrix.transpose_mul, hR₀, Matrix.transpose_zero])
    (by rw [← Matrix.transpose_mul, hR₁, Matrix.transpose_zero])
    (by rw [specNorm_transpose]; exact hγ) (by rw [specNorm_transpose]; exact hG₀)
    (by rw [specNorm_transpose]; exact hτ)
    (by rw [← Matrix.transpose_sub, specNorm_transpose]; exact hδ)
  have e : (R₁ᵀ - R₀ᵀ) * P₀ = (P₀ * (R₁ - R₀))ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_sub, hP₀.symm]
  rw [e, ← Matrix.transpose_sub, ← Matrix.transpose_sub, Frobenius.norm_transpose,
    Frobenius.norm_transpose, Frobenius.norm_transpose] at h
  exact h

end Tail

/-! ### The tail increment between the new bases -/

section Drift

variable {P P₀ : Matrix m m ℝ} {Q Q₀ : Matrix n n ℝ} {dK dL : ℝ}

/-- **The tail increment between the new bases.** With the sines
`‖P₁ (1 - P₀)‖₂ ≤ d_K`, `‖(1 - Q₀) Q₁‖₂ ≤ d_L` of the angles between the old and the new bases,
`‖P₁ R Q₁‖ ≤ ‖P₀ R‖ + ‖R Q₀‖ + d_K d_L ‖R‖`. -/
theorem norm_mul_mul_le_of_drift (hP : IsOrthProjMat P) (hQ : IsOrthProjMat Q)
    (hP₀ : IsOrthProjMat P₀) (hdK : specNorm (P * (1 - P₀)) ≤ dK)
    (hdL : specNorm ((1 - Q₀) * Q) ≤ dL) (R : Matrix m n ℝ) :
    ‖P * R * Q‖ ≤ ‖P₀ * R‖ + ‖R * Q₀‖ + dK * dL * ‖R‖ := by
  have split : P * R * Q =
      P * (P₀ * R) * Q + P * ((1 - P₀) * (R * Q₀)) * Q + P * (1 - P₀) * R * ((1 - Q₀) * Q) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have n1 : ‖P * (P₀ * R) * Q‖ ≤ ‖P₀ * R‖ := (hQ.norm_mul_le' _).trans (hP.norm_mul_le _)
  have n2 : ‖P * ((1 - P₀) * (R * Q₀)) * Q‖ ≤ ‖R * Q₀‖ :=
    (hQ.norm_mul_le' _).trans ((hP.norm_mul_le _).trans (hP₀.compl.norm_mul_le _))
  have n3 : ‖P * (1 - P₀) * R * ((1 - Q₀) * Q)‖ ≤ dK * dL * ‖R‖ :=
    calc ‖P * (1 - P₀) * R * ((1 - Q₀) * Q)‖
        ≤ ‖P * (1 - P₀) * R‖ * specNorm ((1 - Q₀) * Q) := frob_mul_le' _ _
      _ ≤ dK * ‖R‖ * dL :=
        mul_le_mul ((frob_mul_le _ _).trans (mul_le_mul_of_nonneg_right hdK (norm_nonneg _)))
          hdL (specNorm_nonneg _)
          (mul_nonneg ((specNorm_nonneg _).trans hdK) (norm_nonneg _))
      _ = dK * dL * ‖R‖ := by ring
  rw [split]
  have s1 := norm_add_le (P * (P₀ * R) * Q + P * ((1 - P₀) * (R * Q₀)) * Q)
    (P * (1 - P₀) * R * ((1 - Q₀) * Q))
  have s2 := norm_add_le (P * (P₀ * R) * Q) (P * ((1 - P₀) * (R * Q₀)) * Q)
  linarith

end Drift

/-! ### The one-step bound with the tail, and `N` steps -/

section Main

/-- The arithmetic of the one-step bound. -/
private theorem step_arith {e p a b u v k c s d L : ℝ} (hk : 0 ≤ k) (hc : 0 ≤ c)
    (H4 : L ≤ e + p + a + b + k * (u + v + 2 * e)) (H2 : u ≤ (e + a) * c)
    (H2' : v ≤ c * (e + b)) (H6 : p ≤ b + a + d) (H5 : a ≤ s) (H5' : b ≤ s) :
    L ≤ (1 + 2 * (1 + c) * k) * e + 2 * (2 + c * k) * s + d := by
  have h1 : k * (u + v + 2 * e) ≤ k * ((e + a) * c + c * (e + b) + 2 * e) :=
    mul_le_mul_of_nonneg_left (by linarith) hk
  have h2 : (2 + c * k) * (a + b) ≤ (2 + c * k) * (2 * s) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

variable {P P₀ N : Matrix m m ℝ} {Q Q₀ M : Matrix n n ℝ} {Y₀ A₀ A₁ X₀ X₁ : Matrix m n ℝ}
  {G₀ G₁ GY : Matrix n m ℝ} {c g γ ξ τ δ dK dL : ℝ}

/-- **One BUG step for given data: the error against a reference with an orthogonal tail.**
Let `Y₁ = P₁ (Y₀ + (A₁ - A₀)) Q₁` be a BUG step (captures `hK`, `hL`) from `Y₀` with the orthogonal
projectors `P₀ = Y₀ G_Y`, `Q₀ = G_Y Y₀`. Let `X₀`, `X₁` have generalized inverses `G₀`, `G₁` with
symmetric `X G`, `G X`, and tails orthogonal to their column and row spaces. Let
`‖M‖₂, ‖N‖₂ ≤ c` for the overlaps `X₁ Q₀ M = X₁`, `N P₀ X₁ = X₁`, and `‖G₀‖₂, ‖G₁‖₂ ≤ g`,
`‖G_Y‖₂ ≤ γ`, `‖X₁ - X₀‖₂ ≤ ξ`, `‖A₁ - X₁‖₂ ≤ τ`, `‖ΔR‖₂ ≤ δ` for
`ΔR = (A₁ - X₁) - (A₀ - X₀)`, `‖P₁ (1 - P₀)‖₂ ≤ d_K`, `‖(1 - Q₀) Q₁‖₂ ≤ d_L`. Then

  `‖Y₁ - X₁‖ ≤ (1 + 2 (1 + c) g ξ + 2 (2 + c g ξ) δ γ) ‖Y₀ - X₀‖
      + 2 (2 + c g ξ) τ g ‖X₁ - X₀‖ + d_K d_L ‖ΔR‖`.

For the truncated singular value decomposition `τ = σ_{r+1}(A₁)`, so the step adds the tail times
the path length of the reference, and a term of second order in the rotation of the bases times
the tail increment; nothing is added when the tails vanish. -/
theorem norm_projStep_sub_le_tail (hP : IsOrthProjMat P) (hQ : IsOrthProjMat Q)
    (hP₀ : IsOrthProjMat P₀) (hQ₀ : IsOrthProjMat Q₀) (hY₀P : P₀ * Y₀ = Y₀)
    (hY₀Q : Y₀ * Q₀ = Y₀) (hGYP : Y₀ * GY = P₀) (hGYQ : GY * Y₀ = Q₀)
    (hK : P * ((Y₀ + (A₁ - A₀)) * Q₀) = (Y₀ + (A₁ - A₀)) * Q₀)
    (hL : P₀ * (Y₀ + (A₁ - A₀)) * Q = P₀ * (Y₀ + (A₁ - A₀)))
    (hX₀ : X₀ * G₀ * X₀ = X₀) (hc₀ : (X₀ * G₀)ᵀ = X₀ * G₀) (hr₀ : (G₀ * X₀)ᵀ = G₀ * X₀)
    (hX₁ : X₁ * G₁ * X₁ = X₁) (hc₁ : (X₁ * G₁)ᵀ = X₁ * G₁) (hr₁ : (G₁ * X₁)ᵀ = G₁ * X₁)
    (hRG₀ : (A₀ - X₀) * G₀ = 0) (hGR₀ : G₀ * (A₀ - X₀) = 0) (hRG₁ : (A₁ - X₁) * G₁ = 0)
    (hGR₁ : G₁ * (A₁ - X₁) = 0) (hM : X₁ * Q₀ * M = X₁) (hN : N * P₀ * X₁ = X₁)
    (hMc : specNorm M ≤ c) (hNc : specNorm N ≤ c) (hG₀ : specNorm G₀ ≤ g)
    (hG₁ : specNorm G₁ ≤ g) (hγ : specNorm GY ≤ γ) (hξ : specNorm (X₁ - X₀) ≤ ξ)
    (hτ : specNorm (A₁ - X₁) ≤ τ) (hδ : specNorm (A₁ - X₁ - (A₀ - X₀)) ≤ δ)
    (hdK : specNorm (P * (1 - P₀)) ≤ dK) (hdL : specNorm ((1 - Q₀) * Q) ≤ dL) :
    ‖P * (Y₀ + (A₁ - A₀)) * Q - X₁‖ ≤
      (1 + 2 * (1 + c) * (g * ξ) + 2 * (2 + c * (g * ξ)) * (δ * γ)) * ‖Y₀ - X₀‖ +
        2 * (2 + c * (g * ξ)) * (τ * g * ‖X₁ - X₀‖) +
        dK * dL * ‖A₁ - X₁ - (A₀ - X₀)‖ := by
  have hc : 0 ≤ c := (specNorm_nonneg M).trans hMc
  have hk : 0 ≤ g * ξ :=
    mul_nonneg ((specNorm_nonneg G₀).trans hG₀) ((specNorm_nonneg _).trans hξ)
  have H4 := norm_projStep_sub_le hP hQ hP₀ hQ₀ hY₀P hY₀Q hK hL hX₀ hX₁ hc₁ hr₁ hG₀ hG₁ hξ
  have hmis : Y₀ + (A₁ - A₀) - X₁ = Y₀ - X₀ + (A₁ - X₁ - (A₀ - X₀)) := by abel
  have H2 := norm_one_sub_mul_le_of_capture hP hK hM
  have H2' := norm_mul_one_sub_le_of_capture hQ hL hN
  rw [hmis] at H2 H2'
  have ea : ‖(Y₀ - X₀ + (A₁ - X₁ - (A₀ - X₀))) * Q₀‖ ≤
      ‖Y₀ - X₀‖ + ‖(A₁ - X₁ - (A₀ - X₀)) * Q₀‖ := by
    rw [Matrix.add_mul]
    have h1 := norm_add_le ((Y₀ - X₀) * Q₀) ((A₁ - X₁ - (A₀ - X₀)) * Q₀)
    have h2 := hQ₀.norm_mul_le' (Y₀ - X₀)
    linarith
  have eb : ‖P₀ * (Y₀ - X₀ + (A₁ - X₁ - (A₀ - X₀)))‖ ≤
      ‖Y₀ - X₀‖ + ‖P₀ * (A₁ - X₁ - (A₀ - X₀))‖ := by
    rw [Matrix.mul_add]
    have h1 := norm_add_le (P₀ * (Y₀ - X₀)) (P₀ * (A₁ - X₁ - (A₀ - X₀)))
    have h2 := hP₀.norm_mul_le (Y₀ - X₀)
    linarith
  have H2a : ‖(1 - P) * X₁‖ ≤ (‖Y₀ - X₀‖ + ‖(A₁ - X₁ - (A₀ - X₀)) * Q₀‖) * c :=
    H2.trans (mul_le_mul ea hMc (specNorm_nonneg _) (by positivity))
  have H2b : ‖X₁ * (1 - Q)‖ ≤ c * (‖Y₀ - X₀‖ + ‖P₀ * (A₁ - X₁ - (A₀ - X₀))‖) :=
    H2'.trans (mul_le_mul hNc eb (norm_nonneg _) hc)
  have H6 := norm_mul_mul_le_of_drift (Q₀ := Q₀) hP hQ hP₀ hdK hdL (A₁ - X₁ - (A₀ - X₀))
  have H5 := norm_tail_sub_mul_le hQ₀ hGYQ hX₀ hr₀ hX₁ hr₁ hRG₀ hRG₁ hγ hG₀ hτ hδ
  have H5' := norm_mul_tail_sub_le hP₀ hGYP hX₀ hc₀ hX₁ hc₁ hGR₀ hGR₁ hγ hG₀ hτ hδ
  calc ‖P * (Y₀ + (A₁ - A₀)) * Q - X₁‖
      ≤ (1 + 2 * (1 + c) * (g * ξ)) * ‖Y₀ - X₀‖ +
          2 * (2 + c * (g * ξ)) * (δ * γ * ‖Y₀ - X₀‖ + τ * g * ‖X₁ - X₀‖) +
          dK * dL * ‖A₁ - X₁ - (A₀ - X₀)‖ := step_arith hk hc H4 H2a H2b H6 H5 H5'
    _ = _ := by ring

end Main

section Run

variable {A X Y : ℕ → Matrix m n ℝ} {G GY : ℕ → Matrix n m ℝ} {P Nl : ℕ → Matrix m m ℝ}
  {Q M : ℕ → Matrix n n ℝ} {c g γ ξ δ dK dL : ℝ} {τ : ℕ → ℝ}

/-- **Quasi-optimality of the BUG integrator for given data.** Let
`Y (k + 1) = P (k + 1) (Y k + (A (k + 1) - A k)) Q (k + 1)` be `N` BUG steps with the captures of
the K- and the L-step, where `P k = Y k G_Y k` and `Q k = G_Y k Y k` are the orthogonal projectors
onto the column and the row space of `Y k`. Let the references `X k` have generalized inverses
`G k` with symmetric `X G`, `G X`, `‖G k‖₂ ≤ g` and tails `A k - X k` orthogonal to their column
and row spaces. With the constants of `norm_projStep_sub_le_tail`, uniform in the steps, and
`τ k ≥ ‖A (k + 1) - X (k + 1)‖₂`, for `a = 1 + 2 (1 + c) g ξ + 2 (2 + c g ξ) δ γ` and `n ≤ N`

  `‖Y n - X n‖ ≤ aⁿ ‖Y 0 - X 0‖ + ∑_{k<n} a^{n-1-k} (2 (2 + c g ξ) τ k g ‖X (k + 1) - X k‖
      + d_K d_L ‖(A (k + 1) - X (k + 1)) - (A k - X k)‖)`.

For `X k = T_r(A(t_k))` the sum is a Riemann sum of `σ_{r+1}(A) ‖Ẋ‖` plus a term of the size of
the step times the tail, and `aⁿ ≤ exp(n (a - 1))` is bounded in terms of the path lengths of the
reference and of the tail. -/
theorem norm_projRun_sub_le {N : ℕ} (hP : ∀ k ≤ N, IsOrthProjMat (P k))
    (hQ : ∀ k ≤ N, IsOrthProjMat (Q k)) (hYGY : ∀ k < N, Y k * GY k * Y k = Y k)
    (hGYP : ∀ k < N, Y k * GY k = P k) (hGYQ : ∀ k < N, GY k * Y k = Q k)
    (hK : ∀ k < N, P (k + 1) * ((Y k + (A (k + 1) - A k)) * Q k) =
      (Y k + (A (k + 1) - A k)) * Q k)
    (hL : ∀ k < N, P k * (Y k + (A (k + 1) - A k)) * Q (k + 1) =
      P k * (Y k + (A (k + 1) - A k)))
    (hY : ∀ k < N, Y (k + 1) = P (k + 1) * (Y k + (A (k + 1) - A k)) * Q (k + 1))
    (hX : ∀ k ≤ N, X k * G k * X k = X k) (hXc : ∀ k ≤ N, (X k * G k)ᵀ = X k * G k)
    (hXr : ∀ k ≤ N, (G k * X k)ᵀ = G k * X k) (hRG : ∀ k ≤ N, (A k - X k) * G k = 0)
    (hGR : ∀ k ≤ N, G k * (A k - X k) = 0)
    (hM : ∀ k < N, X (k + 1) * Q k * M k = X (k + 1))
    (hNl : ∀ k < N, Nl k * P k * X (k + 1) = X (k + 1))
    (hMc : ∀ k < N, specNorm (M k) ≤ c) (hNc : ∀ k < N, specNorm (Nl k) ≤ c)
    (hG : ∀ k ≤ N, specNorm (G k) ≤ g) (hγ : ∀ k < N, specNorm (GY k) ≤ γ)
    (hξ : ∀ k < N, specNorm (X (k + 1) - X k) ≤ ξ)
    (hτ : ∀ k < N, specNorm (A (k + 1) - X (k + 1)) ≤ τ k)
    (hδ : ∀ k < N, specNorm (A (k + 1) - X (k + 1) - (A k - X k)) ≤ δ)
    (hdK : ∀ k < N, specNorm (P (k + 1) * (1 - P k)) ≤ dK)
    (hdL : ∀ k < N, specNorm ((1 - Q k) * Q (k + 1)) ≤ dL) :
    ∀ n ≤ N, ‖Y n - X n‖ ≤
      (1 + 2 * (1 + c) * (g * ξ) + 2 * (2 + c * (g * ξ)) * (δ * γ)) ^ n * ‖Y 0 - X 0‖ +
        ∑ k ∈ range n,
          (1 + 2 * (1 + c) * (g * ξ) + 2 * (2 + c * (g * ξ)) * (δ * γ)) ^ (n - 1 - k) *
            (2 * (2 + c * (g * ξ)) * (τ k * g * ‖X (k + 1) - X k‖) +
              dK * dL * ‖A (k + 1) - X (k + 1) - (A k - X k)‖) := by
  intro n hn
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    obtain rfl : n = 0 := Nat.le_zero.mp hn
    simp
  · have hc : 0 ≤ c := (specNorm_nonneg _).trans (hMc 0 hN)
    have hg : 0 ≤ g := (specNorm_nonneg _).trans (hG 0 (Nat.zero_le N))
    have hξ0 : 0 ≤ ξ := (specNorm_nonneg _).trans (hξ 0 hN)
    have hδ0 : 0 ≤ δ := (specNorm_nonneg _).trans (hδ 0 hN)
    have hγ0 : 0 ≤ γ := (specNorm_nonneg _).trans (hγ 0 hN)
    have ha : 0 ≤ 1 + 2 * (1 + c) * (g * ξ) + 2 * (2 + c * (g * ξ)) * (δ * γ) := by positivity
    refine discrete_gronwall_le (e := fun k => ‖Y k - X k‖)
      (b := fun k => 2 * (2 + c * (g * ξ)) * (τ k * g * ‖X (k + 1) - X k‖) +
        dK * dL * ‖A (k + 1) - X (k + 1) - (A k - X k)‖) ha (fun k hk => ?_) n hn
    have hk1 : k + 1 ≤ N := hk
    have hPY : P k * Y k = Y k := by rw [← hGYP k hk, hYGY k hk]
    have hYQ : Y k * Q k = Y k := by rw [← hGYQ k hk, ← Matrix.mul_assoc, hYGY k hk]
    have h := norm_projStep_sub_le_tail (hP (k + 1) hk1) (hQ (k + 1) hk1) (hP k hk.le)
      (hQ k hk.le) hPY hYQ (hGYP k hk) (hGYQ k hk) (hK k hk) (hL k hk) (hX k hk.le)
      (hXc k hk.le) (hXr k hk.le) (hX (k + 1) hk1) (hXc (k + 1) hk1) (hXr (k + 1) hk1)
      (hRG k hk.le) (hGR k hk.le) (hRG (k + 1) hk1) (hGR (k + 1) hk1) (hM k hk) (hNl k hk)
      (hMc k hk) (hNc k hk) (hG k hk.le) (hG (k + 1) hk1) (hγ k hk) (hξ k hk) (hτ k hk)
      (hδ k hk) (hdK k hk) (hdL k hk)
    rw [← hY k hk] at h
    exact h.trans_eq (add_assoc _ _ _)

end Run

end MatrixBUG

/-! ### The step in the factors -/

namespace Exactness.IsBUGIncrementStep

open Curvature MatrixBUG

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n]
  [DecidableEq r] {A₀ A₁ X₀ X₁ : Matrix m n ℝ} {U₀ U₁ : Matrix m r ℝ} {S₀ S₁ : Matrix r r ℝ}
  {V₀ V₁ : Matrix n r ℝ}

omit [DecidableEq m] [DecidableEq n] [DecidableEq r] in
/-- The result of the BUG step for given data is the Galerkin projection of `Y₀ + (A₁ - A₀)`:
`U₁ S₁ V₁ᵀ = U₁ U₁ᵀ (U₀ S₀ V₀ᵀ + (A₁ - A₀)) V₁ V₁ᵀ`. -/
theorem eq_proj_mul (hs : IsBUGIncrementStep A₀ A₁ U₀ S₀ V₀ U₁ S₁ V₁) :
    U₁ * S₁ * V₁ᵀ = U₁ * U₁ᵀ * (U₀ * S₀ * V₀ᵀ + (A₁ - A₀)) * (V₁ * V₁ᵀ) := by
  rw [hs.sStep]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc]

omit [DecidableEq m] [DecidableEq n] in
/-- The K-step capture in terms of the projectors: `U₁ U₁ᵀ (Y₀ + D) V₀ V₀ᵀ = (Y₀ + D) V₀ V₀ᵀ`. -/
theorem proj_capK (hs : IsBUGIncrementStep A₀ A₁ U₀ S₀ V₀ U₁ S₁ V₁) (hV₀ : V₀ᵀ * V₀ = 1) :
    U₁ * U₁ᵀ * ((U₀ * S₀ * V₀ᵀ + (A₁ - A₀)) * (V₀ * V₀ᵀ)) =
      (U₀ * S₀ * V₀ᵀ + (A₁ - A₀)) * (V₀ * V₀ᵀ) := by
  have e : (U₀ * S₀ * V₀ᵀ + (A₁ - A₀)) * (V₀ * V₀ᵀ) = (U₀ * S₀ + (A₁ - A₀) * V₀) * V₀ᵀ := by
    rw [← Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_assoc (U₀ * S₀) V₀ᵀ V₀, hV₀,
      Matrix.mul_one]
  rw [e, ← Matrix.mul_assoc, hs.capK]

omit [DecidableEq m] [DecidableEq n] in
/-- The L-step capture in terms of the projectors: `U₀ U₀ᵀ (Y₀ + D) V₁ V₁ᵀ = U₀ U₀ᵀ (Y₀ + D)`. -/
theorem proj_capL (hs : IsBUGIncrementStep A₀ A₁ U₀ S₀ V₀ U₁ S₁ V₁) (hU₀ : U₀ᵀ * U₀ = 1) :
    U₀ * U₀ᵀ * (U₀ * S₀ * V₀ᵀ + (A₁ - A₀)) * (V₁ * V₁ᵀ) =
      U₀ * U₀ᵀ * (U₀ * S₀ * V₀ᵀ + (A₁ - A₀)) := by
  have eL : U₀ᵀ * (U₀ * S₀ * V₀ᵀ + (A₁ - A₀)) = (V₀ * S₀ᵀ + (A₁ - A₀)ᵀ * U₀)ᵀ := by
    simp only [Matrix.mul_add, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose, ← Matrix.mul_assoc, hU₀, Matrix.one_mul]
  have t : (V₀ * S₀ᵀ + (A₁ - A₀)ᵀ * U₀)ᵀ * (V₁ * V₁ᵀ) = (V₀ * S₀ᵀ + (A₁ - A₀)ᵀ * U₀)ᵀ := by
    have h := congrArg Matrix.transpose hs.capL
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h
  calc U₀ * U₀ᵀ * (U₀ * S₀ * V₀ᵀ + (A₁ - A₀)) * (V₁ * V₁ᵀ)
      = U₀ * (U₀ᵀ * (U₀ * S₀ * V₀ᵀ + (A₁ - A₀)) * (V₁ * V₁ᵀ)) := by
        simp only [Matrix.mul_assoc]
    _ = U₀ * (U₀ᵀ * (U₀ * S₀ * V₀ᵀ + (A₁ - A₀))) := by rw [eL, t]
    _ = U₀ * U₀ᵀ * (U₀ * S₀ * V₀ᵀ + (A₁ - A₀)) := (Matrix.mul_assoc _ _ _).symm

/-- **One BUG step for given data, in the factors.** For a BUG step
`(U₀, S₀, V₀) ↦ (U₁, S₁, V₁)` with exact substeps for `F(t, Y) = Ȧ(t)`, orthonormal bases and
invertible `S₀`, the bound of `MatrixBUG.norm_projStep_sub_le_tail` holds with `P = U Uᵀ`,
`Q = V Vᵀ` and `G_Y = V₀ S₀⁻¹ U₀ᵀ`:

  `‖U₁ S₁ V₁ᵀ - X₁‖ ≤ (1 + 2 (1 + c) g ξ + 2 (2 + c g ξ) δ γ) ‖U₀ S₀ V₀ᵀ - X₀‖
      + 2 (2 + c g ξ) τ g ‖X₁ - X₀‖ + d_K d_L ‖(A₁ - X₁) - (A₀ - X₀)‖`. -/
theorem norm_sub_le_tail {G₀ G₁ : Matrix n m ℝ} {N : Matrix m m ℝ} {M : Matrix n n ℝ}
    {c g γ ξ τ δ dK dL : ℝ} (hs : IsBUGIncrementStep A₀ A₁ U₀ S₀ V₀ U₁ S₁ V₁)
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1)
    (hS₀ : IsUnit S₀.det)
    (hX₀ : X₀ * G₀ * X₀ = X₀) (hc₀ : (X₀ * G₀)ᵀ = X₀ * G₀) (hr₀ : (G₀ * X₀)ᵀ = G₀ * X₀)
    (hX₁ : X₁ * G₁ * X₁ = X₁) (hc₁ : (X₁ * G₁)ᵀ = X₁ * G₁) (hr₁ : (G₁ * X₁)ᵀ = G₁ * X₁)
    (hRG₀ : (A₀ - X₀) * G₀ = 0) (hGR₀ : G₀ * (A₀ - X₀) = 0) (hRG₁ : (A₁ - X₁) * G₁ = 0)
    (hGR₁ : G₁ * (A₁ - X₁) = 0) (hM : X₁ * (V₀ * V₀ᵀ) * M = X₁)
    (hN : N * (U₀ * U₀ᵀ) * X₁ = X₁) (hMc : specNorm M ≤ c) (hNc : specNorm N ≤ c)
    (hG₀ : specNorm G₀ ≤ g) (hG₁ : specNorm G₁ ≤ g)
    (hγ : specNorm (V₀ * S₀⁻¹ * U₀ᵀ) ≤ γ) (hξ : specNorm (X₁ - X₀) ≤ ξ)
    (hτ : specNorm (A₁ - X₁) ≤ τ) (hδ : specNorm (A₁ - X₁ - (A₀ - X₀)) ≤ δ)
    (hdK : specNorm (U₁ * U₁ᵀ * (1 - U₀ * U₀ᵀ)) ≤ dK)
    (hdL : specNorm ((1 - V₀ * V₀ᵀ) * (V₁ * V₁ᵀ)) ≤ dL) :
    ‖U₁ * S₁ * V₁ᵀ - X₁‖ ≤
      (1 + 2 * (1 + c) * (g * ξ) + 2 * (2 + c * (g * ξ)) * (δ * γ)) * ‖U₀ * S₀ * V₀ᵀ - X₀‖ +
        2 * (2 + c * (g * ξ)) * (τ * g * ‖X₁ - X₀‖) +
        dK * dL * ‖A₁ - X₁ - (A₀ - X₀)‖ := by
  rw [hs.eq_proj_mul]
  exact norm_projStep_sub_le_tail (isOrthProjMat_mul_transpose hU₁)
    (isOrthProjMat_mul_transpose hV₁) (isOrthProjMat_mul_transpose hU₀)
    (isOrthProjMat_mul_transpose hV₀) (colProj_mul_factor hU₀) (factor_mul_rowProj hV₀)
    (factor_mul_ginv hV₀ hS₀) (ginv_mul_factor hU₀ hS₀) (hs.proj_capK hV₀) (hs.proj_capL hU₀)
    hX₀ hc₀ hr₀ hX₁ hc₁ hr₁ hRG₀ hGR₀ hRG₁ hGR₁ hM hN hMc hNc hG₀ hG₁ hγ hξ hτ hδ hdK hdL

end Exactness.IsBUGIncrementStep

/-! ### Examples -/

namespace BUGQuasiOptimalityExamples

open Curvature

/-- The first unit vector of `ℝ²` as a column. -/
def e₁ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The matrix `diag(s, t)`. -/
def dg (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![s, 0; 0, t]

theorem e₁_orth : e₁ᵀ * e₁ = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [e₁, Matrix.mul_apply]

theorem e₁_mul_transpose : e₁ * e₁ᵀ = dg 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e₁, dg, Matrix.mul_apply]

theorem dg_mul (s t s' t' : ℝ) : dg s t * dg s' t' = dg (s * s') (t * t') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_two]

theorem dg_sub (s t s' t' : ℝ) : dg s t - dg s' t' = dg (s - s') (t - t') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg]

theorem dg_add (s t s' t' : ℝ) : dg s t + dg s' t' = dg (s + s') (t + t') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg]

theorem dg_transpose (s t : ℝ) : (dg s t)ᵀ = dg s t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg]

theorem dg_zero : dg 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg]

theorem isOrthProjMat_dg : IsOrthProjMat (dg 1 0) :=
  ⟨dg_transpose 1 0, by rw [dg_mul]; norm_num⟩

/-- **Non-vacuity of `MatrixBUG.norm_projRun_sub_le`** for any number of steps: the data
`A k = diag(1, k)` with the reference `X k = diag(1, 0)` and the tail `diag(0, k)`, which moves,
and the iterates `Y k = diag(3, 0) ≠ X k`. All hypotheses hold with `P k = Q k = diag(1, 0)`. -/
example (N : ℕ) : ∀ n ≤ N, ‖dg 3 0 - dg 1 0‖ ≤
    (1 + 2 * (1 + specNorm (dg 1 0)) * (specNorm (dg 1 0) * specNorm (dg 0 0)) +
        2 * (2 + specNorm (dg 1 0) * (specNorm (dg 1 0) * specNorm (dg 0 0))) *
          (specNorm (dg 0 1) * specNorm (dg 3⁻¹ 0))) ^ n * ‖dg 3 0 - dg 1 0‖ +
      ∑ k ∈ range n,
        (1 + 2 * (1 + specNorm (dg 1 0)) * (specNorm (dg 1 0) * specNorm (dg 0 0)) +
          2 * (2 + specNorm (dg 1 0) * (specNorm (dg 1 0) * specNorm (dg 0 0))) *
            (specNorm (dg 0 1) * specNorm (dg 3⁻¹ 0))) ^ (n - 1 - k) *
          (2 * (2 + specNorm (dg 1 0) * (specNorm (dg 1 0) * specNorm (dg 0 0))) *
              (specNorm (dg 1 ((k + 1 : ℕ) : ℝ) - dg 1 0) * specNorm (dg 1 0) *
                ‖dg 1 0 - dg 1 0‖) +
            specNorm (dg 1 0 * (1 - dg 1 0)) * specNorm ((1 - dg 1 0) * dg 1 0) *
              ‖dg 1 ((k + 1 : ℕ) : ℝ) - dg 1 0 - (dg 1 (k : ℝ) - dg 1 0)‖) := by
  have hΔ : ∀ k : ℕ, dg 1 ((k + 1 : ℕ) : ℝ) - dg 1 (k : ℝ) = dg 0 1 := fun k => by
    rw [dg_sub]; push_cast; norm_num
  have hK : ∀ k : ℕ, dg 3 0 + (dg 1 ((k + 1 : ℕ) : ℝ) - dg 1 (k : ℝ)) = dg 3 1 := fun k => by
    rw [hΔ, dg_add]; norm_num
  have hδ : ∀ k : ℕ, dg 1 ((k + 1 : ℕ) : ℝ) - dg 1 0 - (dg 1 (k : ℝ) - dg 1 0) = dg 0 1 :=
    fun k => by rw [dg_sub, dg_sub, dg_sub]; push_cast; norm_num
  exact MatrixBUG.norm_projRun_sub_le (A := fun k => dg 1 (k : ℝ)) (X := fun _ => dg 1 0)
    (Y := fun _ => dg 3 0) (G := fun _ => dg 1 0) (GY := fun _ => dg 3⁻¹ 0)
    (P := fun _ => dg 1 0) (Q := fun _ => dg 1 0) (M := fun _ => dg 1 0)
    (Nl := fun _ => dg 1 0) (τ := fun k => specNorm (dg 1 ((k + 1 : ℕ) : ℝ) - dg 1 0))
    (fun _ _ => isOrthProjMat_dg) (fun _ _ => isOrthProjMat_dg)
    (fun _ _ => by rw [dg_mul, dg_mul]; norm_num)
    (fun _ _ => by rw [dg_mul]; norm_num) (fun _ _ => by rw [dg_mul]; norm_num)
    (fun k _ => by rw [hK, dg_mul, dg_mul]; norm_num)
    (fun k _ => by rw [hK, dg_mul, dg_mul]; norm_num)
    (fun k _ => by rw [hK, dg_mul, dg_mul]; norm_num)
    (fun _ _ => by rw [dg_mul, dg_mul]; norm_num)
    (fun _ _ => by rw [dg_mul, dg_transpose]) (fun _ _ => by rw [dg_mul, dg_transpose])
    (fun _ _ => by rw [dg_sub, dg_mul, ← dg_zero]; norm_num)
    (fun _ _ => by rw [dg_sub, dg_mul, ← dg_zero]; norm_num)
    (fun _ _ => by rw [dg_mul, dg_mul]; norm_num)
    (fun _ _ => by rw [dg_mul, dg_mul]; norm_num)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun _ _ => by rw [dg_sub]; norm_num) (fun _ _ => le_rfl)
    (fun k _ => by rw [hδ]) (fun _ _ => le_rfl) (fun _ _ => le_rfl)

/-- The `1 × 1` matrix with the entry `s`. -/
def sc (s : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := !![s]

theorem sc_add (s t : ℝ) : sc s + sc t = sc (s + t) := by
  ext i j
  fin_cases i; fin_cases j
  simp [sc]

theorem sc_transpose (s : ℝ) : (sc s)ᵀ = sc s := by
  ext i j
  fin_cases i; fin_cases j
  simp [sc]

theorem dg_mul_e₁ (s t : ℝ) : dg s t * e₁ = e₁ * sc s := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e₁, dg, sc, Matrix.mul_apply, Fin.sum_univ_two]

/-- A BUG step with exact substeps from `Y₀ = diag(3, 0)` for the data `A₀ = diag(1, 1/2)`,
`A₁ = diag(2, 1/4)`, with the result `Y₁ = diag(4, 0)`. -/
theorem isBUGIncrementStep_dg :
    Exactness.IsBUGIncrementStep (dg 1 2⁻¹) (dg 2 4⁻¹) e₁ (sc 3) e₁ e₁ (sc 4) e₁ := by
  have hk : e₁ * sc 3 + (dg 2 4⁻¹ - dg 1 2⁻¹) * e₁ = e₁ * sc 4 := by
    rw [dg_sub, dg_mul_e₁, ← Matrix.mul_add, sc_add]
    norm_num
  have hcap : e₁ * e₁ᵀ * (e₁ * sc 4) = e₁ * sc 4 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc e₁ᵀ, e₁_orth, Matrix.one_mul]
  refine ⟨by rw [hk, hcap], ?_, ?_⟩
  · rw [sc_transpose, dg_sub, dg_transpose, ← dg_sub, hk, hcap]
  · rw [e₁_orth, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, dg_sub,
      Matrix.mul_assoc, dg_mul_e₁, ← Matrix.mul_assoc, e₁_orth, Matrix.one_mul, sc_add]
    norm_num

/-- **Non-vacuity of `Exactness.IsBUGIncrementStep.norm_sub_le_tail`** (and of
`MatrixBUG.norm_projStep_sub_le_tail` and the lemmas it uses): the step `isBUGIncrementStep_dg`
against the references `X₀ = diag(1, 0)`, `X₁ = diag(2, 0)`, which move, with the nonzero tails
`diag(0, 1/2)`, `diag(0, 1/4)` and the nonzero error `Y₁ - X₁ = diag(2, 0)`. -/
example : ‖e₁ * sc 4 * e₁ᵀ - dg 2 0‖ ≤
    (1 + 2 * (1 + specNorm (dg 1 0)) *
          (max (specNorm (dg 1 0)) (specNorm (dg 2⁻¹ 0)) * specNorm (dg 2 0 - dg 1 0)) +
        2 * (2 + specNorm (dg 1 0) *
          (max (specNorm (dg 1 0)) (specNorm (dg 2⁻¹ 0)) * specNorm (dg 2 0 - dg 1 0))) *
          (specNorm (dg 2 4⁻¹ - dg 2 0 - (dg 1 2⁻¹ - dg 1 0)) *
            specNorm (e₁ * (sc 3)⁻¹ * e₁ᵀ))) *
        ‖e₁ * sc 3 * e₁ᵀ - dg 1 0‖ +
      2 * (2 + specNorm (dg 1 0) *
          (max (specNorm (dg 1 0)) (specNorm (dg 2⁻¹ 0)) * specNorm (dg 2 0 - dg 1 0))) *
        (specNorm (dg 2 4⁻¹ - dg 2 0) * max (specNorm (dg 1 0)) (specNorm (dg 2⁻¹ 0)) *
          ‖dg 2 0 - dg 1 0‖) +
      specNorm (e₁ * e₁ᵀ * (1 - e₁ * e₁ᵀ)) * specNorm ((1 - e₁ * e₁ᵀ) * (e₁ * e₁ᵀ)) *
        ‖dg 2 4⁻¹ - dg 2 0 - (dg 1 2⁻¹ - dg 1 0)‖ :=
  isBUGIncrementStep_dg.norm_sub_le_tail (G₀ := dg 1 0) (G₁ := dg 2⁻¹ 0) (N := dg 1 0)
    (M := dg 1 0) e₁_orth e₁_orth e₁_orth e₁_orth
    (isUnit_iff_ne_zero.mpr (by simp [sc]))
    (by rw [dg_mul, dg_mul]; norm_num) (by rw [dg_mul, dg_transpose])
    (by rw [dg_mul, dg_transpose]) (by rw [dg_mul, dg_mul]; norm_num)
    (by rw [dg_mul, dg_transpose]) (by rw [dg_mul, dg_transpose])
    (by rw [dg_sub, dg_mul, ← dg_zero]; norm_num) (by rw [dg_sub, dg_mul, ← dg_zero]; norm_num)
    (by rw [dg_sub, dg_mul, ← dg_zero]; norm_num) (by rw [dg_sub, dg_mul, ← dg_zero]; norm_num)
    (by rw [e₁_mul_transpose, dg_mul, dg_mul]; norm_num)
    (by rw [e₁_mul_transpose, dg_mul, dg_mul]; norm_num) le_rfl le_rfl (le_max_left _ _)
    (le_max_right _ _) le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl

end BUGQuasiOptimalityExamples

end LeanDLRA
