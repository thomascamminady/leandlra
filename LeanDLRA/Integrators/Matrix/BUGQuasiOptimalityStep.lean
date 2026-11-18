import LeanDLRA.Integrators.Matrix.BUGQuasiOptimality

/-!
# One BUG step for given data: the bound in the step, the gap and the tail

`MatrixBUG.norm_projStep_sub_le_tail` bounds one step `Y₁ = P₁ (Y₀ + (A₁ - A₀)) Q₁` of the BUG
integrator of [CerutiLubich2022] against a reference `X₁` of the same rank, with constants for the
overlaps of the old bases with the reference, for a generalized inverse of `Y₀` and for the sines
of the angles between the old and the new bases. In this file these constants are derived from
the distance `‖Y₀ - X₀‖` and from the increments, for projectors of equal trace (bases with the
same number of columns as the rank of the reference). With `‖G₀‖₂, ‖G₁‖₂ ≤ g` for the generalized
inverses of the references (`g⁻¹` is a lower bound of their smallest nonzero singular value) and a
numbers `η_X ≤ η_F ≤ 1/16` and `η_R` with

  `g ‖X₁ - X₀‖₂ ≤ η_X`, `g ‖ΔR‖₂ ≤ η_R`, `g ‖X₁ - X₀‖ ≤ η_F`, `g ‖A₁ - A₀‖ ≤ η_F`,
  `g ‖Y₀ - X₀‖ ≤ 1/16`,

where `ΔR = (A₁ - X₁) - (A₀ - X₀)` is the increment of the tail, the step satisfies

  `‖Y₁ - X₁‖ ≤ (1 + 23/10 η_X + 43/20 η_R) ‖Y₀ - X₀‖ + 11/5 η_F ‖A₁ - X₁‖₂ + 4/3 η_F² ‖ΔR‖₂`.

All norms `‖·‖` are Frobenius norms and `‖·‖₂` is the spectral norm.

## Main results

* `MatrixBUG.norm_one_sub_mul_eq_of_trace_eq`: for orthogonal projectors of equal trace,
  `‖(1 - R) P‖ = ‖(1 - P) R‖`.
* `MatrixBUG.norm_le_of_mul_colProj_eq`, `MatrixBUG.norm_le_of_rowProj_mul_eq`: `Y₀` is bounded
  below on its column and its row space, `(1 - 2 g ‖Y₀ - X₀‖) ‖Z‖ ≤ g ‖Z Y₀‖` for `Z P₀ = Z`.
* `MatrixBUG.one_sub_mul_norm_mul_one_sub_le_of_capture`,
  `MatrixBUG.one_sub_mul_norm_one_sub_mul_le_of_capture`: the sines of the angles between the old
  and the new bases are at most `g ‖A₁ - A₀‖ / (1 - 2 g ‖Y₀ - X₀‖)`.
* `MatrixBUG.one_sub_mul_norm_one_sub_mul_le`, `MatrixBUG.one_sub_mul_norm_mul_one_sub_le`: the
  new bases capture the reference, `(1 - s) ‖(1 - P₁) X₁‖ ≤ ‖(Y₀ + D - X₁) Q₀‖` with
  `s = ‖G₁‖₂ ‖X₁ - Y₀‖₂`.
* `MatrixBUG.norm_tail_sub_mul_le_of_trace`, `MatrixBUG.norm_mul_tail_sub_le_of_trace`: the tail
  increment seen from the old bases, with the generalized inverse of the reference only.
* `MatrixBUG.norm_projStep_sub_le_of_trace`: the one-step bound above.

## Implementation notes

The factors `23/10`, `43/20` of the old error and the factor `11/5` of the tail are `2`, `2` and
`2` up to the terms of higher order in the step numbers and in `g ‖Y₀ - X₀‖`; the factors of
`MatrixBUG.norm_projStep_sub_le_tail` are `4`, `4` and `4` in the same limit. The gain is in two
places: the part `P₁ (1 - P₀) ΔX (1 - Q₁)` of the increment of the reference carries the sine of
the angle between the old and the new left basis, and so does the part of `P₁ ΔR Q₁` that is not
seen from the old bases. No generalized inverse of `Y₀` is used: the lower bound of `Y₀` on its
row and column space follows from that of `X₀` and from the equality of the traces. The
hypotheses hold in the example of `LeanDLRA/Integrators/Matrix/BUGQuasiOptimalityTruncation.lean`
(a moving reference, a tail and an error that are not zero).

## References

* [CerutiLubich2022]
-/

open Finset Matrix
open scoped LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixBUG

open Curvature

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-! ### Projectors of equal trace -/

section Trace

/-- For orthogonal projectors `P`, `R` of equal trace (equal rank) the two sines agree in the
Frobenius norm: `‖(1 - R) P‖ = ‖(1 - P) R‖`. -/
theorem norm_one_sub_mul_eq_of_trace_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P R : Matrix ι ι ℝ} (hP : IsOrthProjMat P) (hR : IsOrthProjMat R)
    (htr : trace P = trace R) : ‖(1 - R) * P‖ = ‖(1 - P) * R‖ := by
  have h : ‖(1 - R) * P‖ ^ 2 = ‖(1 - P) * R‖ ^ 2 := by
    rw [hP.norm_compl_mul_sq hR, hR.norm_compl_mul_sq hP, trace_mul_comm R P, htr]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

variable {P₀ : Matrix m m ℝ} {Q₀ : Matrix n n ℝ} {Y₀ X₀ : Matrix m n ℝ} {G₀ : Matrix n m ℝ}
  {g : ℝ}

omit [DecidableEq n] in
/-- The sine of the angle between the column spaces of `Y₀` and of a reference `X₀` of the same
rank: `‖P₀ (1 - X₀ G₀)‖ ≤ g ‖Y₀ - X₀‖` for `P₀ Y₀ = Y₀`, `tr P₀ = tr (X₀ G₀)` and `‖G₀‖₂ ≤ g`. -/
theorem norm_mul_one_sub_colProj_le (hP₀ : IsOrthProjMat P₀) (hY₀P : P₀ * Y₀ = Y₀)
    (hX₀ : X₀ * G₀ * X₀ = X₀) (hc₀ : (X₀ * G₀)ᵀ = X₀ * G₀) (htr : trace P₀ = trace (X₀ * G₀))
    (hG₀ : specNorm G₀ ≤ g) : ‖P₀ * (1 - X₀ * G₀)‖ ≤ g * ‖Y₀ - X₀‖ := by
  have hPX := isOrthProjMat_colProj hX₀ hc₀
  have t : ‖P₀ * (1 - X₀ * G₀)‖ = ‖(1 - X₀ * G₀) * P₀‖ := by
    rw [← Frobenius.norm_transpose, Matrix.transpose_mul, hPX.compl.symm, hP₀.symm]
  rw [t, norm_one_sub_mul_eq_of_trace_eq hP₀ hPX htr, norm_sub_rev Y₀ X₀]
  exact (norm_compl_mul_colProj_le (X := X₀) G₀ hP₀ hY₀P).trans
    (mul_le_mul_of_nonneg_right hG₀ (norm_nonneg _))

/-- The sine of the angle between the row spaces of `Y₀` and of a reference `X₀` of the same
rank: `‖(1 - G₀ X₀) Q₀‖ ≤ g ‖Y₀ - X₀‖` for `Y₀ Q₀ = Y₀`, `tr Q₀ = tr (G₀ X₀)` and `‖G₀‖₂ ≤ g`. -/
theorem norm_one_sub_rowProj_mul_le (hQ₀ : IsOrthProjMat Q₀) (hY₀Q : Y₀ * Q₀ = Y₀)
    (hX₀ : X₀ * G₀ * X₀ = X₀) (hr₀ : (G₀ * X₀)ᵀ = G₀ * X₀) (htr : trace Q₀ = trace (G₀ * X₀))
    (hG₀ : specNorm G₀ ≤ g) : ‖(1 - G₀ * X₀) * Q₀‖ ≤ g * ‖Y₀ - X₀‖ := by
  have hQX := isOrthProjMat_rowProj hX₀ hr₀
  have hy : Y₀ * (1 - Q₀) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hY₀Q, sub_self]
  have e : G₀ * X₀ * (1 - Q₀) = G₀ * ((X₀ - Y₀) * (1 - Q₀)) := by
    rw [Matrix.sub_mul X₀ Y₀, hy, sub_zero, Matrix.mul_assoc]
  have t : ‖(1 - Q₀) * (G₀ * X₀)‖ = ‖G₀ * X₀ * (1 - Q₀)‖ := by
    rw [← Frobenius.norm_transpose, Matrix.transpose_mul, hr₀, hQ₀.compl.symm]
  rw [norm_one_sub_mul_eq_of_trace_eq hQ₀ hQX htr, t, e, norm_sub_rev Y₀ X₀]
  exact (frob_mul_le _ _).trans
    (mul_le_mul hG₀ (hQ₀.compl.norm_mul_le' _) (norm_nonneg _) ((specNorm_nonneg _).trans hG₀))

omit [DecidableEq n] in
/-- **`Y₀` is bounded below on its column space.** Let `X₀` have the generalized inverse `G₀`
with `‖G₀‖₂ ≤ g`, and let `P₀` be an orthogonal projector with `P₀ Y₀ = Y₀` and
`tr P₀ = tr (X₀ G₀)`. Then `‖Z‖ ≤ g ‖Z Y₀‖ + 2 g ‖Y₀ - X₀‖ ‖Z‖` for every `Z` with
`Z P₀ = Z`. -/
theorem norm_le_of_mul_colProj_eq {k : Type*} [Fintype k] {Z : Matrix k m ℝ}
    (hP₀ : IsOrthProjMat P₀) (hY₀P : P₀ * Y₀ = Y₀) (hX₀ : X₀ * G₀ * X₀ = X₀)
    (hc₀ : (X₀ * G₀)ᵀ = X₀ * G₀) (htr : trace P₀ = trace (X₀ * G₀)) (hG₀ : specNorm G₀ ≤ g)
    (hZ : Z * P₀ = Z) : ‖Z‖ ≤ g * ‖Z * Y₀‖ + 2 * (g * ‖Y₀ - X₀‖) * ‖Z‖ := by
  classical
  have hs := norm_mul_one_sub_colProj_le hP₀ hY₀P hX₀ hc₀ htr hG₀
  have dec : Z = (Z * Y₀ - Z * (Y₀ - X₀)) * G₀ + Z * (P₀ * (1 - X₀ * G₀)) := by
    have h1 : Z * (P₀ * (1 - X₀ * G₀)) = Z - Z * (X₀ * G₀) := by
      rw [← Matrix.mul_assoc, hZ, Matrix.mul_sub, Matrix.mul_one]
    rw [h1, ← Matrix.mul_sub, sub_sub_cancel, Matrix.mul_assoc]
    abel
  have n1 : ‖(Z * Y₀ - Z * (Y₀ - X₀)) * G₀‖ ≤ (‖Z * Y₀‖ + ‖Z‖ * ‖Y₀ - X₀‖) * g :=
    (frob_mul_le' _ _).trans (mul_le_mul
      ((norm_sub_le _ _).trans (add_le_add le_rfl ((frob_mul_le' Z (Y₀ - X₀)).trans
        (mul_le_mul_of_nonneg_left (specNorm_le_frob _) (norm_nonneg _)))))
      hG₀ (specNorm_nonneg _) (by positivity))
  have n2 : ‖Z * (P₀ * (1 - X₀ * G₀))‖ ≤ ‖Z‖ * (g * ‖Y₀ - X₀‖) :=
    (frob_mul_le' _ _).trans (mul_le_mul_of_nonneg_left ((specNorm_le_frob _).trans hs)
      (norm_nonneg _))
  calc ‖Z‖ = ‖(Z * Y₀ - Z * (Y₀ - X₀)) * G₀ + Z * (P₀ * (1 - X₀ * G₀))‖ :=
        congrArg (fun M => ‖M‖) dec
    _ ≤ (‖Z * Y₀‖ + ‖Z‖ * ‖Y₀ - X₀‖) * g + ‖Z‖ * (g * ‖Y₀ - X₀‖) :=
        (norm_add_le _ _).trans (add_le_add n1 n2)
    _ = g * ‖Z * Y₀‖ + 2 * (g * ‖Y₀ - X₀‖) * ‖Z‖ := by ring

omit [DecidableEq n] in
/-- **`Y₀` is bounded below on its row space.** The transposed statement:
`‖Z‖ ≤ g ‖Y₀ Z‖ + 2 g ‖Y₀ - X₀‖ ‖Z‖` for every `Z` with `Q₀ Z = Z`, where `Y₀ Q₀ = Y₀` and
`tr Q₀ = tr (G₀ X₀)`. -/
theorem norm_le_of_rowProj_mul_eq {k : Type*} [Fintype k] {Z : Matrix n k ℝ}
    (hQ₀ : IsOrthProjMat Q₀) (hY₀Q : Y₀ * Q₀ = Y₀) (hX₀ : X₀ * G₀ * X₀ = X₀)
    (hr₀ : (G₀ * X₀)ᵀ = G₀ * X₀) (htr : trace Q₀ = trace (G₀ * X₀)) (hG₀ : specNorm G₀ ≤ g)
    (hZ : Q₀ * Z = Z) : ‖Z‖ ≤ g * ‖Y₀ * Z‖ + 2 * (g * ‖Y₀ - X₀‖) * ‖Z‖ := by
  classical
  have hs := norm_one_sub_rowProj_mul_le hQ₀ hY₀Q hX₀ hr₀ htr hG₀
  have dec : Z = G₀ * (Y₀ * Z - (Y₀ - X₀) * Z) + (1 - G₀ * X₀) * Q₀ * Z := by
    have h1 : (1 - G₀ * X₀) * Q₀ * Z = Z - G₀ * X₀ * Z := by
      rw [Matrix.mul_assoc, hZ, Matrix.sub_mul, Matrix.one_mul]
    rw [h1, ← Matrix.sub_mul, sub_sub_cancel, ← Matrix.mul_assoc]
    abel
  have n1 : ‖G₀ * (Y₀ * Z - (Y₀ - X₀) * Z)‖ ≤ g * (‖Y₀ * Z‖ + ‖Y₀ - X₀‖ * ‖Z‖) :=
    (frob_mul_le _ _).trans (mul_le_mul hG₀
      ((norm_sub_le _ _).trans (add_le_add le_rfl ((frob_mul_le (Y₀ - X₀) Z).trans
        (mul_le_mul_of_nonneg_right (specNorm_le_frob _) (norm_nonneg _)))))
      (norm_nonneg _) ((specNorm_nonneg _).trans hG₀))
  have n2 : ‖(1 - G₀ * X₀) * Q₀ * Z‖ ≤ g * ‖Y₀ - X₀‖ * ‖Z‖ :=
    (frob_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((specNorm_le_frob _).trans hs)
      (norm_nonneg _))
  calc ‖Z‖ = ‖G₀ * (Y₀ * Z - (Y₀ - X₀) * Z) + (1 - G₀ * X₀) * Q₀ * Z‖ :=
        congrArg (fun M => ‖M‖) dec
    _ ≤ g * (‖Y₀ * Z‖ + ‖Y₀ - X₀‖ * ‖Z‖) + g * ‖Y₀ - X₀‖ * ‖Z‖ :=
        (norm_add_le _ _).trans (add_le_add n1 n2)
    _ = g * ‖Y₀ * Z‖ + 2 * (g * ‖Y₀ - X₀‖) * ‖Z‖ := by ring

end Trace

/-! ### The angles between the old and the new bases -/

section Drift

variable {P P₀ : Matrix m m ℝ} {Q Q₀ : Matrix n n ℝ} {Y₀ X₀ D : Matrix m n ℝ}
  {G₀ : Matrix n m ℝ} {g : ℝ}

omit [DecidableEq n] in
/-- **The angle between the old and the new left basis.** For the K-step capture
`P₁ (Y₀ + D) Q₀ = (Y₀ + D) Q₀` with projectors of equal trace,
`(1 - 2 g ‖Y₀ - X₀‖) ‖P₁ (1 - P₀)‖ ≤ g ‖D‖`: the left basis turns by at most the increment over
the smallest singular value of `Y₀`. -/
theorem one_sub_mul_norm_mul_one_sub_le_of_capture (hP : IsOrthProjMat P)
    (hP₀ : IsOrthProjMat P₀) (hQ₀ : IsOrthProjMat Q₀) (hY₀P : P₀ * Y₀ = Y₀)
    (hY₀Q : Y₀ * Q₀ = Y₀) (hK : P * ((Y₀ + D) * Q₀) = (Y₀ + D) * Q₀)
    (hX₀ : X₀ * G₀ * X₀ = X₀) (hc₀ : (X₀ * G₀)ᵀ = X₀ * G₀) (htrP : trace P = trace P₀)
    (htr : trace P₀ = trace (X₀ * G₀)) (hG₀ : specNorm G₀ ≤ g) :
    (1 - 2 * (g * ‖Y₀ - X₀‖)) * ‖P * (1 - P₀)‖ ≤ g * ‖D‖ := by
  classical
  have hg : 0 ≤ g := (specNorm_nonneg _).trans hG₀
  have t : ‖P * (1 - P₀)‖ = ‖(1 - P) * P₀‖ := by
    rw [← norm_one_sub_mul_eq_of_trace_eq hP hP₀ htrP, ← Frobenius.norm_transpose,
      Matrix.transpose_mul, hP₀.compl.symm, hP.symm]
  have hZ : (1 - P) * P₀ * P₀ = (1 - P) * P₀ := by rw [Matrix.mul_assoc, hP₀.idem]
  have h0 : (1 - P) * ((Y₀ + D) * Q₀) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hK, sub_self]
  have hZY : (1 - P) * P₀ * Y₀ = -((1 - P) * (D * Q₀)) := by
    rw [Matrix.add_mul, hY₀Q, Matrix.mul_add] at h0
    rw [Matrix.mul_assoc, hY₀P]
    exact eq_neg_of_add_eq_zero_left h0
  have h := norm_le_of_mul_colProj_eq hP₀ hY₀P hX₀ hc₀ htr hG₀ hZ
  rw [hZY, norm_neg] at h
  have hD : ‖(1 - P) * (D * Q₀)‖ ≤ ‖D‖ :=
    (hP.compl.norm_mul_le _).trans (hQ₀.norm_mul_le' _)
  have hgD := mul_le_mul_of_nonneg_left hD hg
  rw [t]
  have e : (1 - 2 * (g * ‖Y₀ - X₀‖)) * ‖(1 - P) * P₀‖ =
      ‖(1 - P) * P₀‖ - 2 * (g * ‖Y₀ - X₀‖) * ‖(1 - P) * P₀‖ := by ring
  rw [e]
  linarith

/-- **The angle between the old and the new right basis.** For the L-step capture
`P₀ (Y₀ + D) Q₁ = P₀ (Y₀ + D)` with projectors of equal trace,
`(1 - 2 g ‖Y₀ - X₀‖) ‖(1 - Q₀) Q₁‖ ≤ g ‖D‖`. -/
theorem one_sub_mul_norm_one_sub_mul_le_of_capture (hQ : IsOrthProjMat Q)
    (hP₀ : IsOrthProjMat P₀) (hQ₀ : IsOrthProjMat Q₀) (hY₀P : P₀ * Y₀ = Y₀)
    (hY₀Q : Y₀ * Q₀ = Y₀) (hL : P₀ * (Y₀ + D) * Q = P₀ * (Y₀ + D))
    (hX₀ : X₀ * G₀ * X₀ = X₀) (hr₀ : (G₀ * X₀)ᵀ = G₀ * X₀) (htrQ : trace Q = trace Q₀)
    (htr : trace Q₀ = trace (G₀ * X₀)) (hG₀ : specNorm G₀ ≤ g) :
    (1 - 2 * (g * ‖Y₀ - X₀‖)) * ‖(1 - Q₀) * Q‖ ≤ g * ‖D‖ := by
  have hg : 0 ≤ g := (specNorm_nonneg _).trans hG₀
  have t : ‖(1 - Q₀) * Q‖ = ‖Q₀ * (1 - Q)‖ := by
    rw [norm_one_sub_mul_eq_of_trace_eq hQ hQ₀ htrQ, ← Frobenius.norm_transpose,
      Matrix.transpose_mul, hQ₀.symm, hQ.compl.symm]
  have hZ : Q₀ * (Q₀ * (1 - Q)) = Q₀ * (1 - Q) := by rw [← Matrix.mul_assoc, hQ₀.idem]
  have h0 : P₀ * (Y₀ + D) * (1 - Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hL, sub_self]
  have hZY : Y₀ * (Q₀ * (1 - Q)) = -(P₀ * D * (1 - Q)) := by
    rw [Matrix.mul_add, hY₀P, Matrix.add_mul] at h0
    rw [← Matrix.mul_assoc, hY₀Q]
    exact eq_neg_of_add_eq_zero_left h0
  have h := norm_le_of_rowProj_mul_eq hQ₀ hY₀Q hX₀ hr₀ htr hG₀ hZ
  rw [hZY, norm_neg] at h
  have hD : ‖P₀ * D * (1 - Q)‖ ≤ ‖D‖ :=
    (hQ.compl.norm_mul_le' _).trans (hP₀.norm_mul_le _)
  have hgD := mul_le_mul_of_nonneg_left hD hg
  rw [t]
  have e : (1 - 2 * (g * ‖Y₀ - X₀‖)) * ‖Q₀ * (1 - Q)‖ =
      ‖Q₀ * (1 - Q)‖ - 2 * (g * ‖Y₀ - X₀‖) * ‖Q₀ * (1 - Q)‖ := by ring
  rw [e]
  linarith

end Drift

/-! ### Capture of the reference by the new bases -/

section Capture

variable {P P₀ : Matrix m m ℝ} {Q Q₀ : Matrix n n ℝ} {Y₀ D X₁ : Matrix m n ℝ}
  {G₁ : Matrix n m ℝ} {s : ℝ}

/-- **Capture with a tail (K-step), without an inverse of the overlap.** If the range of `P₁`
contains the range of `(Y₀ + D) Q₀` and `‖G₁‖₂ ‖X₁ - Y₀‖₂ ≤ s` for a generalized inverse `G₁` of
`X₁`, then `(1 - s) ‖(1 - P₁) X₁‖ ≤ ‖(Y₀ + D - X₁) Q₀‖`. -/
theorem one_sub_mul_norm_one_sub_mul_le (hP : IsOrthProjMat P) (hQ₀ : IsOrthProjMat Q₀)
    (hY₀Q : Y₀ * Q₀ = Y₀) (hK : P * ((Y₀ + D) * Q₀) = (Y₀ + D) * Q₀)
    (hX₁ : X₁ * G₁ * X₁ = X₁) (hs : specNorm G₁ * specNorm (X₁ - Y₀) ≤ s) :
    (1 - s) * ‖(1 - P) * X₁‖ ≤ ‖(Y₀ + D - X₁) * Q₀‖ := by
  have h0 : (1 - P) * ((Y₀ + D) * Q₀) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hK, sub_self]
  have hy : Y₀ * (1 - Q₀) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hY₀Q, sub_self]
  have hx : X₁ * (1 - Q₀) = X₁ * (G₁ * (X₁ - Y₀) * (1 - Q₀)) := by
    rw [Matrix.mul_assoc G₁, Matrix.sub_mul X₁ Y₀, hy, sub_zero, ← Matrix.mul_assoc G₁,
      ← Matrix.mul_assoc X₁, ← Matrix.mul_assoc X₁ G₁, hX₁]
  have dec : (1 - P) * X₁ =
      -((1 - P) * ((Y₀ + D - X₁) * Q₀)) + (1 - P) * X₁ * (G₁ * (X₁ - Y₀) * (1 - Q₀)) := by
    have e1 : (1 - P) * ((Y₀ + D - X₁) * Q₀) = -((1 - P) * (X₁ * Q₀)) := by
      rw [Matrix.sub_mul (Y₀ + D) X₁ Q₀, Matrix.mul_sub, h0, zero_sub]
    rw [e1, neg_neg, Matrix.mul_assoc (1 - P) X₁, ← hx, ← Matrix.mul_add, ← Matrix.mul_add,
      add_sub_cancel, Matrix.mul_one]
  have hsp : specNorm (G₁ * (X₁ - Y₀) * (1 - Q₀)) ≤ s :=
    calc specNorm (G₁ * (X₁ - Y₀) * (1 - Q₀))
        ≤ specNorm (G₁ * (X₁ - Y₀)) * specNorm (1 - Q₀) := specNorm_mul_le _ _
      _ ≤ specNorm G₁ * specNorm (X₁ - Y₀) * 1 :=
        mul_le_mul (specNorm_mul_le _ _) hQ₀.compl.specNorm_le_one (specNorm_nonneg _)
          (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _))
      _ ≤ s := by rw [mul_one]; exact hs
  have n1 : ‖(1 - P) * ((Y₀ + D - X₁) * Q₀)‖ ≤ ‖(Y₀ + D - X₁) * Q₀‖ := hP.compl.norm_mul_le _
  have n2 : ‖(1 - P) * X₁ * (G₁ * (X₁ - Y₀) * (1 - Q₀))‖ ≤ ‖(1 - P) * X₁‖ * s :=
    (frob_mul_le' _ _).trans (mul_le_mul_of_nonneg_left hsp (norm_nonneg _))
  have h := norm_add_le (-((1 - P) * ((Y₀ + D - X₁) * Q₀)))
    ((1 - P) * X₁ * (G₁ * (X₁ - Y₀) * (1 - Q₀)))
  rw [← dec, norm_neg] at h
  have e : (1 - s) * ‖(1 - P) * X₁‖ = ‖(1 - P) * X₁‖ - ‖(1 - P) * X₁‖ * s := by ring
  rw [e]
  linarith

/-- **Capture with a tail (L-step), without an inverse of the overlap.** If the range of `Q₁`
contains the row space of `P₀ (Y₀ + D)` and `‖G₁‖₂ ‖X₁ - Y₀‖₂ ≤ s`, then
`(1 - s) ‖X₁ (1 - Q₁)‖ ≤ ‖P₀ (Y₀ + D - X₁)‖`. -/
theorem one_sub_mul_norm_mul_one_sub_le (hQ : IsOrthProjMat Q) (hP₀ : IsOrthProjMat P₀)
    (hY₀P : P₀ * Y₀ = Y₀) (hL : P₀ * (Y₀ + D) * Q = P₀ * (Y₀ + D))
    (hX₁ : X₁ * G₁ * X₁ = X₁) (hs : specNorm G₁ * specNorm (X₁ - Y₀) ≤ s) :
    (1 - s) * ‖X₁ * (1 - Q)‖ ≤ ‖P₀ * (Y₀ + D - X₁)‖ := by
  have h0 : P₀ * (Y₀ + D) * (1 - Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hL, sub_self]
  have hy : (1 - P₀) * Y₀ = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hY₀P, sub_self]
  have hx : (1 - P₀) * X₁ = (1 - P₀) * (X₁ - Y₀) * G₁ * X₁ := by
    rw [Matrix.mul_sub (1 - P₀) X₁ Y₀, hy, sub_zero, Matrix.mul_assoc (1 - P₀) X₁ G₁,
      Matrix.mul_assoc (1 - P₀) (X₁ * G₁) X₁, hX₁]
  have dec : X₁ * (1 - Q) =
      -(P₀ * (Y₀ + D - X₁) * (1 - Q)) + (1 - P₀) * (X₁ - Y₀) * G₁ * (X₁ * (1 - Q)) := by
    have e1 : P₀ * (Y₀ + D - X₁) * (1 - Q) = -(P₀ * X₁ * (1 - Q)) := by
      rw [Matrix.mul_sub P₀ (Y₀ + D) X₁, Matrix.sub_mul, h0, zero_sub]
    rw [e1, neg_neg, ← Matrix.mul_assoc ((1 - P₀) * (X₁ - Y₀) * G₁) X₁ (1 - Q), ← hx,
      ← Matrix.add_mul, ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
  have hsp : specNorm ((1 - P₀) * (X₁ - Y₀) * G₁) ≤ s :=
    calc specNorm ((1 - P₀) * (X₁ - Y₀) * G₁)
        ≤ specNorm ((1 - P₀) * (X₁ - Y₀)) * specNorm G₁ := specNorm_mul_le _ _
      _ ≤ 1 * specNorm (X₁ - Y₀) * specNorm G₁ :=
        mul_le_mul_of_nonneg_right ((specNorm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right hP₀.compl.specNorm_le_one (specNorm_nonneg _)))
          (specNorm_nonneg _)
      _ ≤ s := by rw [one_mul, mul_comm]; exact hs
  have n1 : ‖P₀ * (Y₀ + D - X₁) * (1 - Q)‖ ≤ ‖P₀ * (Y₀ + D - X₁)‖ := hQ.compl.norm_mul_le' _
  have n2 : ‖(1 - P₀) * (X₁ - Y₀) * G₁ * (X₁ * (1 - Q))‖ ≤ s * ‖X₁ * (1 - Q)‖ :=
    (frob_mul_le _ _).trans (mul_le_mul_of_nonneg_right hsp (norm_nonneg _))
  have h := norm_add_le (-(P₀ * (Y₀ + D - X₁) * (1 - Q)))
    ((1 - P₀) * (X₁ - Y₀) * G₁ * (X₁ * (1 - Q)))
  rw [← dec, norm_neg] at h
  have e : (1 - s) * ‖X₁ * (1 - Q)‖ = ‖X₁ * (1 - Q)‖ - s * ‖X₁ * (1 - Q)‖ := by ring
  rw [e]
  linarith

end Capture

/-! ### The tail increment seen from the old bases -/

section Tail

variable {Y₀ X₀ X₁ R₀ R₁ : Matrix m n ℝ} {G₀ G₁ : Matrix n m ℝ} {g τ δ : ℝ}

/-- **The tail increment on the old row space, with the reference only.** As
`MatrixBUG.norm_tail_sub_mul_le`, with the generalized inverse of `X₀` in place of one of `Y₀`:
for an orthogonal projector `Q₀` with `Y₀ Q₀ = Y₀` and `tr Q₀ = tr (G₀ X₀)`,
`‖(R₁ - R₀) Q₀‖ ≤ δ g ‖Y₀ - X₀‖ + τ g ‖X₁ - X₀‖`. -/
theorem norm_tail_sub_mul_le_of_trace {Q₀ : Matrix n n ℝ} (hQ₀ : IsOrthProjMat Q₀)
    (hY₀Q : Y₀ * Q₀ = Y₀) (hX₀ : X₀ * G₀ * X₀ = X₀) (hr₀ : (G₀ * X₀)ᵀ = G₀ * X₀)
    (htr : trace Q₀ = trace (G₀ * X₀)) (hX₁ : X₁ * G₁ * X₁ = X₁)
    (hr₁ : (G₁ * X₁)ᵀ = G₁ * X₁) (hR₀ : R₀ * G₀ = 0) (hR₁ : R₁ * G₁ = 0)
    (hG₀ : specNorm G₀ ≤ g) (hτ : specNorm R₁ ≤ τ) (hδ : specNorm (R₁ - R₀) ≤ δ) :
    ‖(R₁ - R₀) * Q₀‖ ≤ δ * (g * ‖Y₀ - X₀‖) + τ * g * ‖X₁ - X₀‖ := by
  have hQX := isOrthProjMat_rowProj hX₀ hr₀
  have hδ0 : 0 ≤ δ := (specNorm_nonneg _).trans hδ
  have h2 := norm_tail_sub_mul_le (Y₀ := X₀) (GY := G₀) (γ := g) hQX rfl hX₀ hr₀ hX₁ hr₁ hR₀
    hR₁ hG₀ hG₀ hτ hδ
  rw [sub_self X₀, norm_zero, mul_zero, zero_add] at h2
  have hs := norm_one_sub_rowProj_mul_le hQ₀ hY₀Q hX₀ hr₀ htr hG₀
  have dec : (R₁ - R₀) * Q₀ =
      (R₁ - R₀) * ((1 - G₀ * X₀) * Q₀) + (R₁ - R₀) * (G₀ * X₀) * Q₀ := by
    rw [Matrix.sub_mul 1 (G₀ * X₀) Q₀, Matrix.one_mul, Matrix.mul_sub (R₁ - R₀) Q₀,
      Matrix.mul_assoc (R₁ - R₀) (G₀ * X₀) Q₀]
    abel
  have n1 : ‖(R₁ - R₀) * ((1 - G₀ * X₀) * Q₀)‖ ≤ δ * (g * ‖Y₀ - X₀‖) :=
    (frob_mul_le _ _).trans (mul_le_mul hδ hs (norm_nonneg _) hδ0)
  have n2 : ‖(R₁ - R₀) * (G₀ * X₀) * Q₀‖ ≤ τ * g * ‖X₁ - X₀‖ :=
    (hQ₀.norm_mul_le' _).trans h2
  rw [dec]
  exact (norm_add_le _ _).trans (add_le_add n1 n2)

/-- **The tail increment on the old column space, with the reference only.** The transposed
statement: for an orthogonal projector `P₀` with `P₀ Y₀ = Y₀` and `tr P₀ = tr (X₀ G₀)`,
`‖P₀ (R₁ - R₀)‖ ≤ δ g ‖Y₀ - X₀‖ + τ g ‖X₁ - X₀‖`. -/
theorem norm_mul_tail_sub_le_of_trace {P₀ : Matrix m m ℝ} (hP₀ : IsOrthProjMat P₀)
    (hY₀P : P₀ * Y₀ = Y₀) (hX₀ : X₀ * G₀ * X₀ = X₀) (hc₀ : (X₀ * G₀)ᵀ = X₀ * G₀)
    (htr : trace P₀ = trace (X₀ * G₀)) (hX₁ : X₁ * G₁ * X₁ = X₁)
    (hc₁ : (X₁ * G₁)ᵀ = X₁ * G₁) (hR₀ : G₀ * R₀ = 0) (hR₁ : G₁ * R₁ = 0)
    (hG₀ : specNorm G₀ ≤ g) (hτ : specNorm R₁ ≤ τ) (hδ : specNorm (R₁ - R₀) ≤ δ) :
    ‖P₀ * (R₁ - R₀)‖ ≤ δ * (g * ‖Y₀ - X₀‖) + τ * g * ‖X₁ - X₀‖ := by
  have hPX := isOrthProjMat_colProj hX₀ hc₀
  have hδ0 : 0 ≤ δ := (specNorm_nonneg _).trans hδ
  have h2 := norm_mul_tail_sub_le (Y₀ := X₀) (GY := G₀) (γ := g) hPX rfl hX₀ hc₀ hX₁ hc₁ hR₀
    hR₁ hG₀ hG₀ hτ hδ
  rw [sub_self X₀, norm_zero, mul_zero, zero_add] at h2
  have hs := norm_mul_one_sub_colProj_le hP₀ hY₀P hX₀ hc₀ htr hG₀
  have dec : P₀ * (R₁ - R₀) =
      P₀ * (1 - X₀ * G₀) * (R₁ - R₀) + P₀ * (X₀ * G₀ * (R₁ - R₀)) := by
    rw [Matrix.mul_sub P₀ 1 (X₀ * G₀), Matrix.mul_one, Matrix.sub_mul P₀,
      Matrix.mul_assoc P₀ (X₀ * G₀) (R₁ - R₀)]
    abel
  have n1 : ‖P₀ * (1 - X₀ * G₀) * (R₁ - R₀)‖ ≤ g * ‖Y₀ - X₀‖ * δ :=
    (frob_mul_le' _ _).trans (mul_le_mul hs hδ (specNorm_nonneg _)
      ((norm_nonneg _).trans hs))
  have n2 : ‖P₀ * (X₀ * G₀ * (R₁ - R₀))‖ ≤ τ * g * ‖X₁ - X₀‖ :=
    (hP₀.norm_mul_le _).trans h2
  rw [dec]
  refine (norm_add_le _ _).trans ?_
  linarith

end Tail

/-! ### The one-step bound -/

section Main

/-- The error of the step: the old error, the tail increment seen from the old bases and through
the angles between the old and the new bases, and the increment of the reference. -/
private theorem err_split_drift (P P₀ : Matrix m m ℝ) (Q Q₀ : Matrix n n ℝ)
    (Y₀ X₀ Dx R : Matrix m n ℝ) :
    Y₀ + (Dx + R) - (1 - P) * (Dx + R) * (1 - Q₀) - P * ((1 - P₀) * (Dx + R) * (1 - Q)) -
        (X₀ + Dx) =
      Y₀ - X₀ + ((1 - P) * (R * Q₀) + P * (P₀ * R) + P * (1 - P₀) * (R * Q₀) * Q +
        P * (1 - P₀) * R * ((1 - Q₀) * Q)) -
        (1 - P) * Dx * (1 - Q₀) - P * ((1 - P₀) * Dx * (1 - Q)) := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc]
  abel

/-- The arithmetic of the one-step bound. -/
private theorem step_arith_drift {e a b u v dK dL k ηX ηR ηF τ δ L : ℝ} (he : 0 ≤ e)
    (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (ha0 : 0 ≤ a) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hdL0 : 0 ≤ dL)
    (hk0 : 0 ≤ k) (hηR0 : 0 ≤ ηR) (hηF : ηF ≤ 1 / 16) (hηX : ηX ≤ ηF) (hk : k ≤ ηX)
    (H : L ≤ e + (a + b + dK * a + dK * δ * dL) + k * (u + e) + dK * (k * (v + e)))
    (ha : a ≤ ηR * e + ηF * τ) (hb : b ≤ ηR * e + ηF * τ) (hu : 7 / 8 * u ≤ e + a)
    (hv : 7 / 8 * v ≤ e + b) (hdK : 7 / 8 * dK ≤ ηF) (hdL : 7 / 8 * dL ≤ ηF) :
    L ≤ (1 + 23 / 10 * ηX + 43 / 20 * ηR) * e + 11 / 5 * ηF * τ + 4 / 3 * ηF ^ 2 * δ := by
  have hηX0 : 0 ≤ ηX := hk0.trans hk
  have hηF0 : 0 ≤ ηF := hηX0.trans hηX
  have hηX16 : ηX ≤ 1 / 16 := hηX.trans hηF
  have hx0 : 0 ≤ ηX * e := mul_nonneg hηX0 he
  have hz0 : 0 ≤ ηR * e := mul_nonneg hηR0 he
  have hy0 : 0 ≤ ηF * τ := mul_nonneg hηF0 hτ
  have hdK' : dK ≤ 8 / 7 * ηF := by linarith
  have hdL' : dL ≤ 8 / 7 * ηF := by linarith
  have hdK14 : dK ≤ 1 / 14 := by linarith
  have hu' : u + e ≤ 15 / 7 * e + 8 / 7 * (ηR * e + ηF * τ) := by linarith
  have hv' : v + e ≤ 15 / 7 * e + 8 / 7 * (ηR * e + ηF * τ) := by linarith
  have hηα : ηX * (ηR * e + ηF * τ) ≤ 1 / 16 * (ηR * e + ηF * τ) :=
    mul_le_mul_of_nonneg_right hηX16 (by positivity)
  have hW : ηX * (15 / 7 * e + 8 / 7 * (ηR * e + ηF * τ)) ≤
      15 / 7 * (ηX * e) + 1 / 14 * (ηR * e + ηF * τ) := by
    have h : ηX * (15 / 7 * e + 8 / 7 * (ηR * e + ηF * τ)) =
        15 / 7 * (ηX * e) + 8 / 7 * (ηX * (ηR * e + ηF * τ)) := by ring
    linarith
  have f1 : dK * a ≤ 1 / 14 * (ηR * e + ηF * τ) := mul_le_mul hdK14 ha ha0 (by norm_num)
  have f2 : dK * δ * dL ≤ 4 / 3 * ηF ^ 2 * δ := by
    have h1 : dK * δ * dL ≤ 8 / 7 * ηF * δ * (8 / 7 * ηF) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hdK' hδ) hdL' hdL0
        (mul_nonneg (by positivity) hδ)
    have h2 : 0 ≤ ηF ^ 2 * δ := mul_nonneg (sq_nonneg ηF) hδ
    have h3 : 8 / 7 * ηF * δ * (8 / 7 * ηF) = 64 / 49 * (ηF ^ 2 * δ) := by ring
    have h4 : 4 / 3 * ηF ^ 2 * δ = 4 / 3 * (ηF ^ 2 * δ) := by ring
    linarith
  have f3 : k * (u + e) ≤ 15 / 7 * (ηX * e) + 1 / 14 * (ηR * e + ηF * τ) :=
    (mul_le_mul hk hu' (add_nonneg hu0 he) hηX0).trans hW
  have f4 : k * (v + e) ≤ 15 / 7 * (ηX * e) + 1 / 14 * (ηR * e + ηF * τ) :=
    (mul_le_mul hk hv' (add_nonneg hv0 he) hηX0).trans hW
  have f5 : dK * (k * (v + e)) ≤
      1 / 14 * (15 / 7 * (ηX * e) + 1 / 14 * (ηR * e + ηF * τ)) :=
    mul_le_mul hdK14 f4 (mul_nonneg hk0 (add_nonneg hv0 he)) (by norm_num)
  have e1 : (1 + 23 / 10 * ηX + 43 / 20 * ηR) * e =
      e + 23 / 10 * (ηX * e) + 43 / 20 * (ηR * e) := by ring
  have e2 : 11 / 5 * ηF * τ = 11 / 5 * (ηF * τ) := by ring
  rw [e1, e2]
  linarith

variable {P P₀ : Matrix m m ℝ} {Q Q₀ : Matrix n n ℝ} {Y₀ A₀ A₁ X₀ X₁ : Matrix m n ℝ}
  {G₀ G₁ : Matrix n m ℝ} {g ηX ηR ηF τ : ℝ}

/-- **One BUG step for given data: the bound in the step, the gap and the tail.** Let
`Y₁ = P₁ (Y₀ + (A₁ - A₀)) Q₁` be a BUG step (captures `hK`, `hL`) from `Y₀ = P₀ Y₀ Q₀`, with
orthogonal projectors of the trace of the projectors of the references. Let `X₀`, `X₁` have
generalized inverses `G₀`, `G₁` with symmetric `X G`, `G X`, `‖G₀‖₂, ‖G₁‖₂ ≤ g`, and tails
orthogonal to their column and row spaces. If, with `ΔR = (A₁ - X₁) - (A₀ - X₀)`,

  `g ‖X₁ - X₀‖₂ ≤ η_X`, `g ‖ΔR‖₂ ≤ η_R`, `g ‖X₁ - X₀‖ ≤ η_F`, `g ‖A₁ - A₀‖ ≤ η_F`,
  `η_X ≤ η_F ≤ 1/16`, `g ‖Y₀ - X₀‖ ≤ 1/16`

and `‖A₁ - X₁‖₂ ≤ τ`, then

  `‖Y₁ - X₁‖ ≤ (1 + 23/10 η_X + 43/20 η_R) ‖Y₀ - X₀‖ + 11/5 η_F τ + 4/3 η_F² ‖ΔR‖₂`.

The factor of the old error has the increments of the reference and of the tail in the spectral
norm only. For the truncated singular value decomposition of data with `‖Ȧ‖ ≤ μ`, `σ_r ≥ ρ` and
`σ_{r+1} ≤ τ̄ < ρ` one has `g = 1/ρ` and may take `η_X = η_R = η_F = h μ / (ρ - τ̄)` for the step
size `h`. -/
theorem norm_projStep_sub_le_of_trace (hP : IsOrthProjMat P) (hQ : IsOrthProjMat Q)
    (hP₀ : IsOrthProjMat P₀) (hQ₀ : IsOrthProjMat Q₀) (hY₀P : P₀ * Y₀ = Y₀)
    (hY₀Q : Y₀ * Q₀ = Y₀)
    (hK : P * ((Y₀ + (A₁ - A₀)) * Q₀) = (Y₀ + (A₁ - A₀)) * Q₀)
    (hL : P₀ * (Y₀ + (A₁ - A₀)) * Q = P₀ * (Y₀ + (A₁ - A₀)))
    (hX₀ : X₀ * G₀ * X₀ = X₀) (hc₀ : (X₀ * G₀)ᵀ = X₀ * G₀) (hr₀ : (G₀ * X₀)ᵀ = G₀ * X₀)
    (hX₁ : X₁ * G₁ * X₁ = X₁) (hc₁ : (X₁ * G₁)ᵀ = X₁ * G₁) (hr₁ : (G₁ * X₁)ᵀ = G₁ * X₁)
    (hRG₀ : (A₀ - X₀) * G₀ = 0) (hGR₀ : G₀ * (A₀ - X₀) = 0) (hRG₁ : (A₁ - X₁) * G₁ = 0)
    (hGR₁ : G₁ * (A₁ - X₁) = 0) (htrP : trace P = trace P₀) (htrQ : trace Q = trace Q₀)
    (htrP₀ : trace P₀ = trace (X₀ * G₀)) (htrQ₀ : trace Q₀ = trace (G₀ * X₀))
    (hG₀ : specNorm G₀ ≤ g) (hG₁ : specNorm G₁ ≤ g) (hξ₂ : g * specNorm (X₁ - X₀) ≤ ηX)
    (hδ : g * specNorm (A₁ - X₁ - (A₀ - X₀)) ≤ ηR) (hξ : g * ‖X₁ - X₀‖ ≤ ηF)
    (hν : g * ‖A₁ - A₀‖ ≤ ηF) (hηX : ηX ≤ ηF) (hηF : ηF ≤ 1 / 16)
    (he : g * ‖Y₀ - X₀‖ ≤ 1 / 16) (hτ : specNorm (A₁ - X₁) ≤ τ) :
    ‖P * (Y₀ + (A₁ - A₀)) * Q - X₁‖ ≤
      (1 + 23 / 10 * ηX + 43 / 20 * ηR) * ‖Y₀ - X₀‖ + 11 / 5 * ηF * τ +
        4 / 3 * ηF ^ 2 * specNorm (A₁ - X₁ - (A₀ - X₀)) := by
  have hg : 0 ≤ g := (specNorm_nonneg _).trans hG₀
  have hτ0 : 0 ≤ τ := (specNorm_nonneg _).trans hτ
  have hmis : Y₀ + (A₁ - A₀) - X₁ = Y₀ - X₀ + (A₁ - X₁ - (A₀ - X₀)) := by abel
  have hD : A₁ - A₀ = X₁ - X₀ + (A₁ - X₁ - (A₀ - X₀)) := by abel
  -- the tail increment seen from the old bases
  have ha0 := norm_tail_sub_mul_le_of_trace hQ₀ hY₀Q hX₀ hr₀ htrQ₀ hX₁ hr₁ hRG₀ hRG₁ hG₀ hτ
    le_rfl
  have hb0 := norm_mul_tail_sub_le_of_trace hP₀ hY₀P hX₀ hc₀ htrP₀ hX₁ hc₁ hGR₀ hGR₁ hG₀ hτ
    le_rfl
  have hαle : specNorm (A₁ - X₁ - (A₀ - X₀)) * (g * ‖Y₀ - X₀‖) + τ * g * ‖X₁ - X₀‖ ≤
      ηR * ‖Y₀ - X₀‖ + ηF * τ := by
    have h1 : specNorm (A₁ - X₁ - (A₀ - X₀)) * (g * ‖Y₀ - X₀‖) =
        g * specNorm (A₁ - X₁ - (A₀ - X₀)) * ‖Y₀ - X₀‖ := by ring
    have h2 : τ * g * ‖X₁ - X₀‖ = g * ‖X₁ - X₀‖ * τ := by ring
    rw [h1, h2]
    exact add_le_add (mul_le_mul_of_nonneg_right hδ (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hξ hτ0)
  have ha := ha0.trans hαle
  have hb := hb0.trans hαle
  -- the angles between the old and the new bases
  have hdK := one_sub_mul_norm_mul_one_sub_le_of_capture hP hP₀ hQ₀ hY₀P hY₀Q hK hX₀ hc₀ htrP
    htrP₀ hG₀
  have hdL := one_sub_mul_norm_one_sub_mul_le_of_capture hQ hP₀ hQ₀ hY₀P hY₀Q hL hX₀ hr₀ htrQ
    htrQ₀ hG₀
  have hdK' : 7 / 8 * ‖P * (1 - P₀)‖ ≤ ηF := by
    have := mul_le_mul_of_nonneg_right (by linarith : 7 / 8 ≤ 1 - 2 * (g * ‖Y₀ - X₀‖))
      (norm_nonneg (P * (1 - P₀)))
    linarith
  have hdL' : 7 / 8 * ‖(1 - Q₀) * Q‖ ≤ ηF := by
    have := mul_le_mul_of_nonneg_right (by linarith : 7 / 8 ≤ 1 - 2 * (g * ‖Y₀ - X₀‖))
      (norm_nonneg ((1 - Q₀) * Q))
    linarith
  -- capture of the reference
  have hs : specNorm G₁ * specNorm (X₁ - Y₀) ≤ 1 / 8 := by
    have h1 : specNorm (X₁ - Y₀) ≤ ‖X₁ - X₀‖ + ‖Y₀ - X₀‖ :=
      (specNorm_le_frob _).trans ((norm_sub_le_norm_sub_add_norm_sub X₁ X₀ Y₀).trans_eq
        (by rw [norm_sub_rev X₀ Y₀]))
    have h2 : specNorm G₁ * specNorm (X₁ - Y₀) ≤ g * (‖X₁ - X₀‖ + ‖Y₀ - X₀‖) :=
      mul_le_mul hG₁ h1 (specNorm_nonneg _) hg
    linarith
  have hu0 := one_sub_mul_norm_one_sub_mul_le hP hQ₀ hY₀Q hK hX₁ hs
  have hv0 := one_sub_mul_norm_mul_one_sub_le hQ hP₀ hY₀P hL hX₁ hs
  rw [hmis] at hu0 hv0
  have hu : 7 / 8 * ‖(1 - P) * X₁‖ ≤ ‖Y₀ - X₀‖ + ‖(A₁ - X₁ - (A₀ - X₀)) * Q₀‖ := by
    have h1 : ‖(Y₀ - X₀ + (A₁ - X₁ - (A₀ - X₀))) * Q₀‖ ≤
        ‖Y₀ - X₀‖ + ‖(A₁ - X₁ - (A₀ - X₀)) * Q₀‖ := by
      rw [Matrix.add_mul]
      exact (norm_add_le _ _).trans (add_le_add (hQ₀.norm_mul_le' _) le_rfl)
    norm_num at hu0
    linarith
  have hv : 7 / 8 * ‖X₁ * (1 - Q)‖ ≤ ‖Y₀ - X₀‖ + ‖P₀ * (A₁ - X₁ - (A₀ - X₀))‖ := by
    have h1 : ‖P₀ * (Y₀ - X₀ + (A₁ - X₁ - (A₀ - X₀)))‖ ≤
        ‖Y₀ - X₀‖ + ‖P₀ * (A₁ - X₁ - (A₀ - X₀))‖ := by
      rw [Matrix.mul_add]
      exact (norm_add_le _ _).trans (add_le_add (hP₀.norm_mul_le _) le_rfl)
    norm_num at hv0
    linarith
  -- the increment of the reference between the bases
  have ht5 := norm_one_sub_mul_sub_mul_one_sub_le hP hQ₀ hY₀Q hX₀ hX₁ hc₁ hG₀ hG₁
    (le_refl (specNorm (X₁ - X₀)))
  have ht6 := norm_mul_one_sub_mul_sub_mul_one_sub_le (P := 1)
    ⟨Matrix.transpose_one, Matrix.mul_one 1⟩ hP₀ hQ hY₀P hX₀ hX₁ hr₁ hG₀ hG₁
    (le_refl (specNorm (X₁ - X₀)))
  rw [Matrix.one_mul] at ht6
  have hW : (1 - P₀) * ((1 - P₀) * (X₁ - X₀) * (1 - Q)) = (1 - P₀) * (X₁ - X₀) * (1 - Q) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP₀.compl.idem]
  have n6 : ‖P * ((1 - P₀) * (X₁ - X₀) * (1 - Q))‖ ≤
      ‖P * (1 - P₀)‖ * (g * specNorm (X₁ - X₀) * (‖X₁ * (1 - Q)‖ + ‖Y₀ - X₀‖)) := by
    rw [← hW, ← Matrix.mul_assoc P (1 - P₀)]
    exact (frob_mul_le _ _).trans
      (mul_le_mul (specNorm_le_frob _) ht6 (norm_nonneg _) (norm_nonneg _))
  -- the tail increment through the new bases
  have n1 : ‖(1 - P) * ((A₁ - X₁ - (A₀ - X₀)) * Q₀)‖ ≤ ‖(A₁ - X₁ - (A₀ - X₀)) * Q₀‖ :=
    hP.compl.norm_mul_le _
  have n2 : ‖P * (P₀ * (A₁ - X₁ - (A₀ - X₀)))‖ ≤ ‖P₀ * (A₁ - X₁ - (A₀ - X₀))‖ :=
    hP.norm_mul_le _
  have n3 : ‖P * (1 - P₀) * ((A₁ - X₁ - (A₀ - X₀)) * Q₀) * Q‖ ≤
      ‖P * (1 - P₀)‖ * ‖(A₁ - X₁ - (A₀ - X₀)) * Q₀‖ :=
    (hQ.norm_mul_le' _).trans ((frob_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (specNorm_le_frob _) (norm_nonneg _)))
  have n4 : ‖P * (1 - P₀) * (A₁ - X₁ - (A₀ - X₀)) * ((1 - Q₀) * Q)‖ ≤
      ‖P * (1 - P₀)‖ * specNorm (A₁ - X₁ - (A₀ - X₀)) * ‖(1 - Q₀) * Q‖ :=
    (frob_mul_le' _ _).trans (mul_le_mul (frob_mul_le' _ _) (specNorm_le_frob _)
      (specNorm_nonneg _) (mul_nonneg (norm_nonneg _) (specNorm_nonneg _)))
  -- the error of the step
  have hstep : P * (Y₀ + (A₁ - A₀)) * Q - X₁ =
      Y₀ - X₀ + ((1 - P) * ((A₁ - X₁ - (A₀ - X₀)) * Q₀) + P * (P₀ * (A₁ - X₁ - (A₀ - X₀))) +
        P * (1 - P₀) * ((A₁ - X₁ - (A₀ - X₀)) * Q₀) * Q +
        P * (1 - P₀) * (A₁ - X₁ - (A₀ - X₀)) * ((1 - Q₀) * Q)) -
        (1 - P) * (X₁ - X₀) * (1 - Q₀) - P * ((1 - P₀) * (X₁ - X₀) * (1 - Q)) := by
    rw [projStep_eq_add_sub hY₀P hY₀Q hK hL, ← err_split_drift, ← hD]
    abel
  have H : ‖P * (Y₀ + (A₁ - A₀)) * Q - X₁‖ ≤
      ‖Y₀ - X₀‖ + (‖(A₁ - X₁ - (A₀ - X₀)) * Q₀‖ + ‖P₀ * (A₁ - X₁ - (A₀ - X₀))‖ +
        ‖P * (1 - P₀)‖ * ‖(A₁ - X₁ - (A₀ - X₀)) * Q₀‖ +
        ‖P * (1 - P₀)‖ * specNorm (A₁ - X₁ - (A₀ - X₀)) * ‖(1 - Q₀) * Q‖) +
        g * specNorm (X₁ - X₀) * (‖(1 - P) * X₁‖ + ‖Y₀ - X₀‖) +
        ‖P * (1 - P₀)‖ * (g * specNorm (X₁ - X₀) * (‖X₁ * (1 - Q)‖ + ‖Y₀ - X₀‖)) := by
    rw [hstep]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add le_rfl ?_)) ht5)) n6)
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add n1 n2)) n3)) n4)
  exact step_arith_drift (norm_nonneg _) hτ0 (specNorm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (mul_nonneg hg (specNorm_nonneg _))
    ((mul_nonneg hg (specNorm_nonneg _)).trans hδ) hηF hηX hξ₂ H ha hb hu hv hdK' hdL'

end Main

end MatrixBUG

end LeanDLRA
