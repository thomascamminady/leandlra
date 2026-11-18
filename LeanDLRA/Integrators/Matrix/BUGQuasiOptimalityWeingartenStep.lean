import LeanDLRA.Integrators.Matrix.BUGQuasiOptimalityNormalStep

/-!
# One BUG step for given data: the tail seen from the old reference as source

`MatrixBUG.norm_projStep_sub_le_of_trace_of_ginv_mul_norm_le` bounds one step
`Y₁ = P₁ (Y₀ + (A₁ - A₀)) Q₁` of the BUG integrator of [CerutiLubich2022] against a reference
`X₁` of the same rank with the source `9/4 η_F ‖A₁ - X₁‖₂` (the spectral norm of the tail times
the Frobenius norm of the whole increment) in a tube `g ‖Y₀ - X₀‖ ≤ θ ≤ 1/16`. In this file the
source is the tail at the new time seen from the row and the column space of the old reference,

  `ω² ≥ ‖(A₁ - X₁) Pv₀‖² + ‖Pu₀ (A₁ - X₁)‖²`,   `Pu₀ = X₀ G₀`, `Pv₀ = G₀ X₀`,

with the factor `1` at first order, and the radius of the tube is any `θ < 1/2` with
`η_F + θ < 1`: with `c ≥ 1/(1 - 2 θ)`, `d ≥ 1/(1 - η_F - θ)`, `κ = η_X (η_X + θ) d (1 + d)` and
`β² ≥ 2 κ`,

  `‖Y₁ - X₁‖ ≤ (1 + 3/2 η_R + κ (1 + η_R)² + c η_F (η_R + η_X (d (1 + η_R) + 1))) ‖Y₀ - X₀‖
      + (1 + β + c η_F (1 + d η_X)) ω + c² η_F² ‖ΔR‖₂`.

Here `g ‖X₁ - X₀‖₂ ≤ η_X`, `g ‖ΔR‖₂ ≤ η_R`, `g ‖X₁ - X₀‖ ≤ η_F`, `g ‖A₁ - A₀‖ ≤ η_F`,
`ΔR = (A₁ - X₁) - (A₀ - X₀)`, `‖G₀‖₂, ‖G₁‖₂ ≤ g`. All norms `‖·‖` are Frobenius norms and `‖·‖₂`
is the spectral norm. The source has a form in the increment of the data: with a reflexive
generalized inverse `G₀` and `g ‖A₁ - X₁‖₂ ≤ q ≤ 1`,

  `(1 - q)² (‖(A₁ - X₁) Pv₀‖² + ‖Pu₀ (A₁ - X₁)‖²)
      ≤ ‖(A₁ - X₁) (A₁ - A₀)ᵀ G₀ᵀ‖² + ‖G₀ᵀ (A₁ - A₀)ᵀ (A₁ - X₁)‖²`,

the two parts of the map `Z ↦ G₀ᵀ Zᵀ R + R Zᵀ G₀ᵀ` of
`LeanDLRA/DLRA/QuasiOptimalityDefect.lean` at the increment `Z = A₁ - A₀`, with the tail
`R = A₁ - X₁` at the new time and the inverse at the old time.

## Main results

* `MatrixBUG.norm_tail_sub_mul_le_add_norm_mul_rowProj`,
  `MatrixBUG.norm_mul_tail_sub_le_add_norm_colProj_mul`: the tail increment seen from the old
  bases is the tail seen from the old reference up to `‖ΔR‖₂ g ‖Y₀ - X₀‖`.
* `MatrixBUG.norm_one_sub_mul_add_mul_sq_le`: `‖(1 - P) A + P B‖² ≤ ‖A‖² + ‖B‖²`.
* `MatrixBUG.norm_tail_mul_rowProj_le`, `MatrixBUG.norm_colProj_mul_tail_le`,
  `MatrixBUG.sq_mul_norm_tail_mul_rowProj_sq_add_le`: the source in the increment of the data.
* `MatrixBUG.norm_projStep_sub_le_of_trace_of_norm_tail_sq_le`: the one-step bound above.

## Implementation notes

In the identity of the step (`MatrixBUG.projStep_eq_add_sub`) the two terms of first order with
the tail increment are `(1 - P₁) ΔR Q₀` and `P₁ P₀ ΔR`. Their ranges are orthogonal, so their
sum is bounded by the root of the sum of the squares, and each is the tail at the new time seen
from the reference, `ΔR Pv₀ = (A₁ - X₁) Pv₀`, up to the angle between the bases and the
reference. No orthogonality of the tail to the new reference is used in the step. The constants
`c`, `d` are the only places where the radius `θ` enters besides `κ`: the angle between the old
and the new bases needs `θ < 1/2` (`MatrixBUG.norm_le_of_mul_colProj_eq`), the capture of the
new reference `η_F + θ < 1`. The factor `β` of the source comes from the component of the new
reference normal to the new left and the old right basis.

## References

* [CerutiLubich2022]
-/

open Finset Matrix
open scoped LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixBUG

open Curvature

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-! ### The tail increment seen from the old bases and from the old reference -/

section Tail

variable {Y₀ X₀ R₀ R₁ : Matrix m n ℝ} {G₀ : Matrix n m ℝ} {g δ : ℝ}

/-- **The tail increment on the old row space and the tail on the row space of the reference.**
For an orthogonal projector `Q₀` with `Y₀ Q₀ = Y₀` and `tr Q₀ = tr (G₀ X₀)`, and `R₀ G₀ = 0`,
`‖(R₁ - R₀) Q₀‖ ≤ δ g ‖Y₀ - X₀‖ + ‖R₁ (G₀ X₀)‖` with `δ ≥ ‖R₁ - R₀‖₂`. -/
theorem norm_tail_sub_mul_le_add_norm_mul_rowProj {Q₀ : Matrix n n ℝ} (hQ₀ : IsOrthProjMat Q₀)
    (hY₀Q : Y₀ * Q₀ = Y₀) (hX₀ : X₀ * G₀ * X₀ = X₀) (hr₀ : (G₀ * X₀)ᵀ = G₀ * X₀)
    (htr : trace Q₀ = trace (G₀ * X₀)) (hR₀ : R₀ * G₀ = 0) (hG₀ : specNorm G₀ ≤ g)
    (hδ : specNorm (R₁ - R₀) ≤ δ) :
    ‖(R₁ - R₀) * Q₀‖ ≤ δ * (g * ‖Y₀ - X₀‖) + ‖R₁ * (G₀ * X₀)‖ := by
  have hδ0 : 0 ≤ δ := (specNorm_nonneg _).trans hδ
  have hs := norm_one_sub_rowProj_mul_le hQ₀ hY₀Q hX₀ hr₀ htr hG₀
  have hRP : (R₁ - R₀) * (G₀ * X₀) = R₁ * (G₀ * X₀) := by
    rw [Matrix.sub_mul, ← Matrix.mul_assoc R₀, hR₀, Matrix.zero_mul, sub_zero]
  have dec : (R₁ - R₀) * Q₀ =
      (R₁ - R₀) * ((1 - G₀ * X₀) * Q₀) + (R₁ - R₀) * (G₀ * X₀) * Q₀ := by
    rw [Matrix.sub_mul 1 (G₀ * X₀) Q₀, Matrix.one_mul, Matrix.mul_sub (R₁ - R₀) Q₀,
      Matrix.mul_assoc (R₁ - R₀) (G₀ * X₀) Q₀]
    abel
  have n1 : ‖(R₁ - R₀) * ((1 - G₀ * X₀) * Q₀)‖ ≤ δ * (g * ‖Y₀ - X₀‖) :=
    (frob_mul_le _ _).trans (mul_le_mul hδ hs (norm_nonneg _) hδ0)
  have n2 : ‖(R₁ - R₀) * (G₀ * X₀) * Q₀‖ ≤ ‖R₁ * (G₀ * X₀)‖ := by
    rw [hRP]
    exact hQ₀.norm_mul_le' _
  rw [dec]
  exact (norm_add_le _ _).trans (add_le_add n1 n2)

/-- **The tail increment on the old column space and the tail on the column space of the
reference.** The transposed statement: for `P₀ Y₀ = Y₀`, `tr P₀ = tr (X₀ G₀)` and `G₀ R₀ = 0`,
`‖P₀ (R₁ - R₀)‖ ≤ δ g ‖Y₀ - X₀‖ + ‖X₀ G₀ R₁‖`. -/
theorem norm_mul_tail_sub_le_add_norm_colProj_mul {P₀ : Matrix m m ℝ} (hP₀ : IsOrthProjMat P₀)
    (hY₀P : P₀ * Y₀ = Y₀) (hX₀ : X₀ * G₀ * X₀ = X₀) (hc₀ : (X₀ * G₀)ᵀ = X₀ * G₀)
    (htr : trace P₀ = trace (X₀ * G₀)) (hR₀ : G₀ * R₀ = 0) (hG₀ : specNorm G₀ ≤ g)
    (hδ : specNorm (R₁ - R₀) ≤ δ) :
    ‖P₀ * (R₁ - R₀)‖ ≤ δ * (g * ‖Y₀ - X₀‖) + ‖X₀ * G₀ * R₁‖ := by
  have hs := norm_mul_one_sub_colProj_le hP₀ hY₀P hX₀ hc₀ htr hG₀
  have hRP : X₀ * G₀ * (R₁ - R₀) = X₀ * G₀ * R₁ := by
    rw [Matrix.mul_sub, Matrix.mul_assoc X₀ G₀ R₀, hR₀, Matrix.mul_zero, sub_zero]
  have dec : P₀ * (R₁ - R₀) =
      P₀ * (1 - X₀ * G₀) * (R₁ - R₀) + P₀ * (X₀ * G₀ * (R₁ - R₀)) := by
    rw [Matrix.mul_sub P₀ 1 (X₀ * G₀), Matrix.mul_one, Matrix.sub_mul P₀,
      Matrix.mul_assoc P₀ (X₀ * G₀) (R₁ - R₀)]
    abel
  have n1 : ‖P₀ * (1 - X₀ * G₀) * (R₁ - R₀)‖ ≤ g * ‖Y₀ - X₀‖ * δ :=
    (frob_mul_le' _ _).trans (mul_le_mul hs hδ (specNorm_nonneg _)
      ((norm_nonneg _).trans hs))
  have n2 : ‖P₀ * (X₀ * G₀ * (R₁ - R₀))‖ ≤ ‖X₀ * G₀ * R₁‖ := by
    rw [hRP]
    exact hP₀.norm_mul_le _
  rw [dec]
  refine (norm_add_le _ _).trans ?_
  linarith

end Tail

omit [DecidableEq n] in
/-- **Two matrices with orthogonal column spaces.** For an orthogonal projector `P`,
`‖(1 - P) A + P B‖² ≤ ‖A‖² + ‖B‖²`. -/
theorem norm_one_sub_mul_add_mul_sq_le {P : Matrix m m ℝ} (hP : IsOrthProjMat P)
    (A B : Matrix m n ℝ) : ‖(1 - P) * A + P * B‖ ^ 2 ≤ ‖A‖ ^ 2 + ‖B‖ ^ 2 := by
  have h := (hP.isOrthProj_leftMulCLM (l := n)).norm_sq_add ((1 - P) * A + P * B)
  have e1 : P * ((1 - P) * A + P * B) = P * B := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one,
      hP.idem, sub_self, Matrix.zero_mul, zero_add]
  simp only [Frobenius.leftMulCLM_apply] at h
  rw [e1, add_sub_cancel_right] at h
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (hP.norm_mul_le B) 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (hP.compl.norm_mul_le A) 2
  linarith

/-! ### The source in the increment of the data -/

section Weingarten

variable {A₀ A₁ X₀ X₁ : Matrix m n ℝ} {G₀ G₁ : Matrix n m ℝ} {g τ q : ℝ}

omit [DecidableEq m] [DecidableEq n] in
/-- The increment of the data against the tail, from the right: the reference at the new time
and the tail at the old time drop out. -/
private theorem tail_mul_transpose_mul_eq {R X₁ X₀ R₀ D : Matrix m n ℝ} {G : Matrix n m ℝ}
    (hD : D = X₁ + R - X₀ - R₀) (h1 : R * X₁ᵀ = 0) (h3 : R₀ᵀ * Gᵀ = 0) :
    R * Dᵀ * Gᵀ = R * Rᵀ * Gᵀ - R * X₀ᵀ * Gᵀ := by
  subst hD
  rw [Matrix.transpose_sub, Matrix.transpose_sub, Matrix.transpose_add, Matrix.mul_sub,
    Matrix.mul_sub, Matrix.mul_add, h1, zero_add, Matrix.sub_mul, Matrix.sub_mul,
    Matrix.mul_assoc R R₀ᵀ Gᵀ, h3, Matrix.mul_zero, sub_zero]

omit [DecidableEq m] [DecidableEq n] in
/-- The increment of the data against the tail, from the left. -/
private theorem transpose_mul_transpose_mul_tail_eq {R X₁ X₀ R₀ D : Matrix m n ℝ}
    {G : Matrix n m ℝ} (hD : D = X₁ + R - X₀ - R₀) (h1 : X₁ᵀ * R = 0) (h3 : Gᵀ * R₀ᵀ = 0) :
    Gᵀ * Dᵀ * R = Gᵀ * Rᵀ * R - Gᵀ * X₀ᵀ * R := by
  subst hD
  rw [Matrix.transpose_sub, Matrix.transpose_sub, Matrix.transpose_add, Matrix.mul_sub,
    Matrix.mul_sub, Matrix.mul_add, h3, sub_zero, Matrix.sub_mul, Matrix.add_mul,
    Matrix.mul_assoc Gᵀ X₁ᵀ R, h1, Matrix.mul_zero, zero_add]

/-- **The tail on the row space of the old reference, in the increment of the data.** For a
reflexive generalized inverse `G₀` of `X₀` with symmetric `G₀ X₀`, tails with
`G₀ (A₀ - X₀) = 0`, `(A₁ - X₁) G₁ = 0`, and `‖G₀‖₂ ≤ g`, `‖A₁ - X₁‖₂ ≤ τ`,
`‖(A₁ - X₁) (G₀ X₀)‖ ≤ ‖(A₁ - X₁) (A₁ - A₀)ᵀ G₀ᵀ‖ + τ g ‖X₀ G₀ (A₁ - X₁)‖`. -/
theorem norm_tail_mul_rowProj_le (hG₀X : G₀ * X₀ * G₀ = G₀) (hr₀ : (G₀ * X₀)ᵀ = G₀ * X₀)
    (hX₁ : X₁ * G₁ * X₁ = X₁) (hr₁ : (G₁ * X₁)ᵀ = G₁ * X₁) (hGR₀ : G₀ * (A₀ - X₀) = 0)
    (hRG₁ : (A₁ - X₁) * G₁ = 0) (hG₀ : specNorm G₀ ≤ g) (hτ : specNorm (A₁ - X₁) ≤ τ) :
    ‖(A₁ - X₁) * (G₀ * X₀)‖ ≤
      ‖(A₁ - X₁) * (A₁ - A₀)ᵀ * G₀ᵀ‖ + τ * g * ‖X₀ * G₀ * (A₁ - X₁)‖ := by
  have hτ0 : 0 ≤ τ := (specNorm_nonneg _).trans hτ
  have hXt : X₁ᵀ = G₁ * X₁ * X₁ᵀ := by
    conv_lhs => rw [← hX₁]
    rw [Matrix.mul_assoc X₁ G₁ X₁, Matrix.transpose_mul, hr₁]
  have hRX₁ : (A₁ - X₁) * X₁ᵀ = 0 := by
    rw [hXt, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hRG₁, Matrix.zero_mul, Matrix.zero_mul]
  have h1 : (G₀ * (X₀ * G₀ * (A₁ - X₁)))ᵀ = (A₁ - X₁)ᵀ * G₀ᵀ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hG₀X, Matrix.transpose_mul]
  have h2 : (A₁ - X₁) * (G₀ * X₀) = (A₁ - X₁) * X₀ᵀ * G₀ᵀ := by
    conv_lhs => rw [← hr₀]
    rw [Matrix.transpose_mul, Matrix.mul_assoc]
  have h3 : (A₀ - X₀)ᵀ * G₀ᵀ = 0 := by
    rw [← Matrix.transpose_mul, hGR₀, Matrix.transpose_zero]
  have hD : (A₁ - X₁) * (A₁ - A₀)ᵀ * G₀ᵀ =
      (A₁ - X₁) * (A₁ - X₁)ᵀ * G₀ᵀ - (A₁ - X₁) * X₀ᵀ * G₀ᵀ :=
    tail_mul_transpose_mul_eq (by abel) hRX₁ h3
  have key : (A₁ - X₁) * (G₀ * X₀) =
      -((A₁ - X₁) * (A₁ - A₀)ᵀ * G₀ᵀ) + (A₁ - X₁) * (G₀ * (X₀ * G₀ * (A₁ - X₁)))ᵀ := by
    rw [h1, h2, hD, ← Matrix.mul_assoc (A₁ - X₁) (A₁ - X₁)ᵀ G₀ᵀ]
    abel
  have n1 : ‖(A₁ - X₁) * (G₀ * (X₀ * G₀ * (A₁ - X₁)))ᵀ‖ ≤
      τ * g * ‖X₀ * G₀ * (A₁ - X₁)‖ := by
    refine (frob_mul_le _ _).trans ?_
    rw [Frobenius.norm_transpose, mul_assoc]
    exact mul_le_mul hτ ((frob_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right hG₀ (norm_nonneg _))) (norm_nonneg _) hτ0
  rw [key]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  exact add_le_add le_rfl n1

/-- **The tail on the column space of the old reference, in the increment of the data.** The
transposed statement:
`‖X₀ G₀ (A₁ - X₁)‖ ≤ ‖G₀ᵀ (A₁ - A₀)ᵀ (A₁ - X₁)‖ + τ g ‖(A₁ - X₁) (G₀ X₀)‖`. -/
theorem norm_colProj_mul_tail_le (hG₀X : G₀ * X₀ * G₀ = G₀) (hc₀ : (X₀ * G₀)ᵀ = X₀ * G₀)
    (hX₁ : X₁ * G₁ * X₁ = X₁) (hc₁ : (X₁ * G₁)ᵀ = X₁ * G₁) (hRG₀ : (A₀ - X₀) * G₀ = 0)
    (hGR₁ : G₁ * (A₁ - X₁) = 0) (hG₀ : specNorm G₀ ≤ g) (hτ : specNorm (A₁ - X₁) ≤ τ) :
    ‖X₀ * G₀ * (A₁ - X₁)‖ ≤
      ‖G₀ᵀ * (A₁ - A₀)ᵀ * (A₁ - X₁)‖ + τ * g * ‖(A₁ - X₁) * (G₀ * X₀)‖ := by
  have hτ0 : 0 ≤ τ := (specNorm_nonneg _).trans hτ
  have hg : 0 ≤ g := (specNorm_nonneg _).trans hG₀
  have hXt : X₁ᵀ = X₁ᵀ * (X₁ * G₁) := by
    conv_lhs => rw [← hX₁]
    rw [Matrix.transpose_mul, hc₁]
  have hXR₁ : X₁ᵀ * (A₁ - X₁) = 0 := by
    rw [hXt, Matrix.mul_assoc, Matrix.mul_assoc, hGR₁, Matrix.mul_zero, Matrix.mul_zero]
  have h1 : ((A₁ - X₁) * (G₀ * X₀) * G₀)ᵀ = G₀ᵀ * (A₁ - X₁)ᵀ := by
    rw [Matrix.mul_assoc, hG₀X, Matrix.transpose_mul]
  have h2 : X₀ * G₀ * (A₁ - X₁) = G₀ᵀ * X₀ᵀ * (A₁ - X₁) := by
    conv_lhs => rw [← hc₀]
    rw [Matrix.transpose_mul]
  have h3 : G₀ᵀ * (A₀ - X₀)ᵀ = 0 := by
    rw [← Matrix.transpose_mul, hRG₀, Matrix.transpose_zero]
  have hD : G₀ᵀ * (A₁ - A₀)ᵀ * (A₁ - X₁) =
      G₀ᵀ * (A₁ - X₁)ᵀ * (A₁ - X₁) - G₀ᵀ * X₀ᵀ * (A₁ - X₁) :=
    transpose_mul_transpose_mul_tail_eq (by abel) hXR₁ h3
  have key : X₀ * G₀ * (A₁ - X₁) =
      -(G₀ᵀ * (A₁ - A₀)ᵀ * (A₁ - X₁)) + ((A₁ - X₁) * (G₀ * X₀) * G₀)ᵀ * (A₁ - X₁) := by
    rw [h1, h2, hD]
    abel
  have n1 : ‖((A₁ - X₁) * (G₀ * X₀) * G₀)ᵀ * (A₁ - X₁)‖ ≤
      τ * g * ‖(A₁ - X₁) * (G₀ * X₀)‖ := by
    refine (frob_mul_le' _ _).trans ?_
    rw [Frobenius.norm_transpose]
    have h4 : ‖(A₁ - X₁) * (G₀ * X₀) * G₀‖ ≤ ‖(A₁ - X₁) * (G₀ * X₀)‖ * g :=
      (frob_mul_le' _ _).trans (mul_le_mul_of_nonneg_left hG₀ (norm_nonneg _))
    calc ‖(A₁ - X₁) * (G₀ * X₀) * G₀‖ * specNorm (A₁ - X₁)
        ≤ ‖(A₁ - X₁) * (G₀ * X₀)‖ * g * τ :=
          mul_le_mul h4 hτ (specNorm_nonneg _) (mul_nonneg (norm_nonneg _) hg)
      _ = τ * g * ‖(A₁ - X₁) * (G₀ * X₀)‖ := by ring
  rw [key]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  exact add_le_add le_rfl n1

/-- Two numbers that bound each other up to a factor `q ≤ 1`:
`(1 - q)² (a² + b²) ≤ x² + y²` from `a ≤ x + q b` and `b ≤ y + q a`. -/
private theorem sq_mul_sq_add_sq_le {a b x y q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq0 : 0 ≤ q) (hq : q ≤ 1) (h1 : a ≤ x + q * b) (h2 : b ≤ y + q * a) :
    (1 - q) ^ 2 * (a ^ 2 + b ^ 2) ≤ x ^ 2 + y ^ 2 := by
  have h3 : (1 - q) * (a ^ 2 + b ^ 2) ≤ a * x + b * y := by
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb,
      mul_nonneg hq0 (sq_nonneg (a - b))]
  have h4 : (a * x + b * y) ^ 2 ≤ (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (a * y - b * x)]
  have h5 : 0 ≤ (1 - q) * (a ^ 2 + b ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hq) (add_nonneg (sq_nonneg a) (sq_nonneg b))
  have h6 : ((1 - q) * (a ^ 2 + b ^ 2)) ^ 2 ≤ (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) :=
    (pow_le_pow_left₀ h5 h3 2).trans h4
  rcases (add_nonneg (sq_nonneg a) (sq_nonneg b)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact add_nonneg (sq_nonneg x) (sq_nonneg y)
  · refine le_of_mul_le_mul_right ?_ hpos
    calc (1 - q) ^ 2 * (a ^ 2 + b ^ 2) * (a ^ 2 + b ^ 2)
        = ((1 - q) * (a ^ 2 + b ^ 2)) ^ 2 := by ring
      _ ≤ (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := h6
      _ = (x ^ 2 + y ^ 2) * (a ^ 2 + b ^ 2) := by ring

/-- **The tail seen from the old reference, in the increment of the data.** Let `G₀` be a
reflexive generalized inverse of `X₀` with symmetric `X₀ G₀`, `G₀ X₀` and `‖G₀‖₂ ≤ g`, let the
tails `A₀ - X₀`, `A₁ - X₁` be orthogonal to the references, and let `g ‖A₁ - X₁‖₂ ≤ q ≤ 1`.
Then, with the projectors `Pu₀ = X₀ G₀`, `Pv₀ = G₀ X₀` and `R = A₁ - X₁`,

  `(1 - q)² (‖R Pv₀‖² + ‖Pu₀ R‖²) ≤ ‖R (A₁ - A₀)ᵀ G₀ᵀ‖² + ‖G₀ᵀ (A₁ - A₀)ᵀ R‖²`:

the source of the step is at most `1/(1 - q)` times the two parts of the map
`Z ↦ G₀ᵀ Zᵀ R + R Zᵀ G₀ᵀ` at the increment `Z = A₁ - A₀` of the data. -/
theorem sq_mul_norm_tail_mul_rowProj_sq_add_le (hG₀X : G₀ * X₀ * G₀ = G₀)
    (hc₀ : (X₀ * G₀)ᵀ = X₀ * G₀) (hr₀ : (G₀ * X₀)ᵀ = G₀ * X₀) (hX₁ : X₁ * G₁ * X₁ = X₁)
    (hc₁ : (X₁ * G₁)ᵀ = X₁ * G₁) (hr₁ : (G₁ * X₁)ᵀ = G₁ * X₁) (hRG₀ : (A₀ - X₀) * G₀ = 0)
    (hGR₀ : G₀ * (A₀ - X₀) = 0) (hRG₁ : (A₁ - X₁) * G₁ = 0) (hGR₁ : G₁ * (A₁ - X₁) = 0)
    (hG₀ : specNorm G₀ ≤ g) (hq : g * specNorm (A₁ - X₁) ≤ q) (hq1 : q ≤ 1) :
    (1 - q) ^ 2 * (‖(A₁ - X₁) * (G₀ * X₀)‖ ^ 2 + ‖X₀ * G₀ * (A₁ - X₁)‖ ^ 2) ≤
      ‖(A₁ - X₁) * (A₁ - A₀)ᵀ * G₀ᵀ‖ ^ 2 + ‖G₀ᵀ * (A₁ - A₀)ᵀ * (A₁ - X₁)‖ ^ 2 := by
  have hg : 0 ≤ g := (specNorm_nonneg _).trans hG₀
  have hq0 : 0 ≤ q := (mul_nonneg hg (specNorm_nonneg _)).trans hq
  have ha := norm_tail_mul_rowProj_le hG₀X hr₀ hX₁ hr₁ hGR₀ hRG₁ hG₀ (le_refl _)
  have hb := norm_colProj_mul_tail_le hG₀X hc₀ hX₁ hc₁ hRG₀ hGR₁ hG₀ (le_refl _)
  have e : ∀ x : ℝ, specNorm (A₁ - X₁) * g * x = g * specNorm (A₁ - X₁) * x := fun x => by ring
  rw [e] at ha hb
  exact sq_mul_sq_add_sq_le (norm_nonneg _) (norm_nonneg _) hq0 hq1
    (ha.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hq (norm_nonneg _))))
    (hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hq (norm_nonneg _))))

end Weingarten

/-! ### The one-step bound -/

section Main

/-- `x ≤ c y` from `(1 - s) x ≤ y` and `1 ≤ (1 - s) c`. -/
private theorem le_mul_of_one_sub_mul_le {x y s c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c)
    (h1 : 1 ≤ (1 - s) * c) (h : (1 - s) * x ≤ y) : x ≤ c * y := by
  nlinarith [mul_le_mul_of_nonneg_right h1 hx, mul_le_mul_of_nonneg_left h hc]

/-- The two tail terms with orthogonal ranges: `T ≤ ω + 3/2 x` from `T² ≤ a² + b²`,
`a ≤ x + s`, `b ≤ x + t` and `s² + t² ≤ ω²`. -/
private theorem le_add_of_sq_le_sq_add_sq {T a b x s t ω : ℝ} (hT0 : 0 ≤ T) (ha0 : 0 ≤ a)
    (hb0 : 0 ≤ b) (hx : 0 ≤ x) (hs : 0 ≤ s) (ht : 0 ≤ t) (hω0 : 0 ≤ ω)
    (hT : T ^ 2 ≤ a ^ 2 + b ^ 2) (ha : a ≤ x + s) (hb : b ≤ x + t)
    (hω : s ^ 2 + t ^ 2 ≤ ω ^ 2) : T ≤ ω + 3 / 2 * x := by
  have h1 : s + t ≤ 3 / 2 * ω := by
    refine (pow_le_pow_iff_left₀ (add_nonneg hs ht) (by positivity) two_ne_zero).mp ?_
    nlinarith [sq_nonneg (s - t), sq_nonneg ω]
  have h2 := pow_le_pow_left₀ ha0 ha 2
  have h3 := pow_le_pow_left₀ hb0 hb 2
  refine (pow_le_pow_iff_left₀ hT0 (by positivity) two_ne_zero).mp (hT.trans ?_)
  nlinarith [mul_le_mul_of_nonneg_left h1 hx, sq_nonneg x]

/-- The old error with the exchanged normal component: `M ≤ (1 + κ p²) e + β ω` from
`M² ≤ e² + 2 κ (p e + ω)²` and `2 κ ≤ β²`. -/
private theorem le_of_sq_le_add_two_mul_sq {M e ω κ p β : ℝ} (hM0 : 0 ≤ M) (he : 0 ≤ e)
    (hω : 0 ≤ ω) (hκ : 0 ≤ κ) (hp : 0 ≤ p) (hβ0 : 0 ≤ β) (hβ : 2 * κ ≤ β ^ 2)
    (hM : M ^ 2 ≤ e ^ 2 + 2 * κ * (p * e + ω) ^ 2) : M ≤ (1 + κ * p ^ 2) * e + β * ω := by
  have hk : (2 * κ * p) ^ 2 ≤ ((1 + κ * p ^ 2) * β) ^ 2 := by
    have h1 : (2 * κ * p) ^ 2 ≤ 2 * κ * (1 + κ * p ^ 2) ^ 2 := by
      nlinarith [mul_nonneg hκ (sq_nonneg (κ * p ^ 2))]
    have h2 : 2 * κ * (1 + κ * p ^ 2) ^ 2 ≤ β ^ 2 * (1 + κ * p ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_right hβ (sq_nonneg _)
    calc (2 * κ * p) ^ 2 ≤ β ^ 2 * (1 + κ * p ^ 2) ^ 2 := h1.trans h2
      _ = ((1 + κ * p ^ 2) * β) ^ 2 := by ring
  have key : 2 * κ * p ≤ (1 + κ * p ^ 2) * β :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hk
  refine (pow_le_pow_iff_left₀ hM0 (by positivity) two_ne_zero).mp (hM.trans ?_)
  nlinarith [mul_nonneg (mul_nonneg he hω) (sub_nonneg.mpr key),
    mul_nonneg (sub_nonneg.mpr hβ) (sq_nonneg ω), sq_nonneg (κ * p ^ 2 * e)]

/-- The arithmetic of the one-step bound. -/
private theorem step_arith_source {e a b sa sb u v dK dL k ηX ηR ηF θ c d β ω δ L M T nb w : ℝ}
    (he : 0 ≤ e) (hδ : 0 ≤ δ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hsa0 : 0 ≤ sa) (hsb0 : 0 ≤ sb)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hdL0 : 0 ≤ dL) (hk0 : 0 ≤ k) (hηR0 : 0 ≤ ηR)
    (hηF0 : 0 ≤ ηF) (hM0 : 0 ≤ M) (hT0 : 0 ≤ T) (hw0 : 0 ≤ w) (hθ0 : 0 ≤ θ) (hc0 : 0 ≤ c)
    (hd0 : 0 ≤ d) (hβ0 : 0 ≤ β) (hω0 : 0 ≤ ω) (hk : k ≤ ηX)
    (hβ : 2 * (ηX * (ηX + θ) * d * (1 + d)) ≤ β ^ 2)
    (H : L ≤ M + (T + dK * a + dK * δ * dL) + dK * (k * (v + e)))
    (hM : M ^ 2 ≤ e ^ 2 + 2 * nb * w) (hnb : nb ≤ u * (k + θ)) (hw : w ≤ k * (u + e))
    (hT : T ^ 2 ≤ a ^ 2 + b ^ 2) (ha : a ≤ ηR * e + sa) (hb : b ≤ ηR * e + sb)
    (hω : sa ^ 2 + sb ^ 2 ≤ ω ^ 2) (hu : u ≤ d * (e + a)) (hv : v ≤ d * (e + b))
    (hdK : dK ≤ c * ηF) (hdL : dL ≤ c * ηF) :
    L ≤ (1 + 3 / 2 * ηR + ηX * (ηX + θ) * d * (1 + d) * (1 + ηR) ^ 2 +
        c * ηF * (ηR + ηX * (d * (1 + ηR) + 1))) * e +
      (1 + β + c * ηF * (1 + d * ηX)) * ω + c ^ 2 * ηF ^ 2 * δ := by
  have hηX0 : 0 ≤ ηX := hk0.trans hk
  have hx0 : 0 ≤ ηR * e := mul_nonneg hηR0 he
  have hsa : sa ≤ ω :=
    (pow_le_pow_iff_left₀ hsa0 hω0 two_ne_zero).mp (by nlinarith [sq_nonneg sb])
  have hsb : sb ≤ ω :=
    (pow_le_pow_iff_left₀ hsb0 hω0 two_ne_zero).mp (by nlinarith [sq_nonneg sa])
  have ha' : a ≤ ηR * e + ω := by linarith
  have hb' : b ≤ ηR * e + ω := by linarith
  have hE0 : 0 ≤ e + (ηR * e + ω) := by positivity
  have hu' : u ≤ d * (e + (ηR * e + ω)) :=
    hu.trans (mul_le_mul_of_nonneg_left (by linarith) hd0)
  have hv' : v ≤ d * (e + (ηR * e + ω)) :=
    hv.trans (mul_le_mul_of_nonneg_left (by linarith) hd0)
  have hcF0 : 0 ≤ c * ηF := mul_nonneg hc0 hηF0
  -- the two tail terms of first order
  have hTle := le_add_of_sq_le_sq_add_sq hT0 ha0 hb0 hx0 hsa0 hsb0 hω0 hT ha hb hω
  -- the old error with the exchanged normal component
  have h1 : nb * w ≤ u * (k + θ) * (k * (u + e)) :=
    mul_le_mul hnb hw hw0 (mul_nonneg hu0 (add_nonneg hk0 hθ0))
  have h2 : u * (k + θ) ≤ d * (e + (ηR * e + ω)) * (ηX + θ) :=
    mul_le_mul hu' (by linarith) (add_nonneg hk0 hθ0) (mul_nonneg hd0 hE0)
  have h3 : k * (u + e) ≤ ηX * (d * (e + (ηR * e + ω)) + (e + (ηR * e + ω))) :=
    mul_le_mul hk (by linarith) (add_nonneg hu0 he) hηX0
  have h4 : u * (k + θ) * (k * (u + e)) ≤
      d * (e + (ηR * e + ω)) * (ηX + θ) *
        (ηX * (d * (e + (ηR * e + ω)) + (e + (ηR * e + ω)))) :=
    mul_le_mul h2 h3 (mul_nonneg hk0 (add_nonneg hu0 he))
      (mul_nonneg (mul_nonneg hd0 hE0) (add_nonneg hηX0 hθ0))
  have e5 : d * (e + (ηR * e + ω)) * (ηX + θ) *
      (ηX * (d * (e + (ηR * e + ω)) + (e + (ηR * e + ω)))) =
      ηX * (ηX + θ) * d * (1 + d) * ((1 + ηR) * e + ω) ^ 2 := by ring
  have hM' : M ^ 2 ≤ e ^ 2 + 2 * (ηX * (ηX + θ) * d * (1 + d)) * ((1 + ηR) * e + ω) ^ 2 := by
    rw [e5] at h4
    have e6 : 2 * nb * w = 2 * (nb * w) := by ring
    rw [e6] at hM
    linarith
  have hκ0 : 0 ≤ ηX * (ηX + θ) * d * (1 + d) := by positivity
  have hMle := le_of_sq_le_add_two_mul_sq hM0 he hω0 hκ0 (by linarith : (0 : ℝ) ≤ 1 + ηR) hβ0 hβ
    hM'
  -- the terms of second order
  have f1 : dK * a ≤ c * ηF * (ηR * e + ω) := mul_le_mul hdK ha' ha0 hcF0
  have f2 : dK * δ * dL ≤ c * ηF * δ * (c * ηF) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hdK hδ) hdL hdL0 (mul_nonneg hcF0 hδ)
  have f3 : k * (v + e) ≤ ηX * (d * (e + (ηR * e + ω)) + e) :=
    mul_le_mul hk (by linarith) (add_nonneg hv0 he) hηX0
  have f4 : dK * (k * (v + e)) ≤ c * ηF * (ηX * (d * (e + (ηR * e + ω)) + e)) :=
    mul_le_mul hdK f3 (mul_nonneg hk0 (add_nonneg hv0 he)) hcF0
  have e7 : (1 + 3 / 2 * ηR + ηX * (ηX + θ) * d * (1 + d) * (1 + ηR) ^ 2 +
        c * ηF * (ηR + ηX * (d * (1 + ηR) + 1))) * e +
      (1 + β + c * ηF * (1 + d * ηX)) * ω + c ^ 2 * ηF ^ 2 * δ =
      ((1 + ηX * (ηX + θ) * d * (1 + d) * (1 + ηR) ^ 2) * e + β * ω) +
        (ω + 3 / 2 * (ηR * e)) + c * ηF * (ηR * e + ω) + c * ηF * δ * (c * ηF) +
        c * ηF * (ηX * (d * (e + (ηR * e + ω)) + e)) := by ring
  rw [e7]
  linarith

variable {P P₀ : Matrix m m ℝ} {Q Q₀ : Matrix n n ℝ} {Y₀ A₀ A₁ X₀ X₁ : Matrix m n ℝ}
  {G₀ G₁ : Matrix n m ℝ} {g ηX ηR ηF θ c d β ω : ℝ}

/-- **One BUG step for given data: the tail seen from the old reference as source, in a tube of
relative radius below `1/2`.** Let `Y₁ = P₁ (Y₀ + (A₁ - A₀)) Q₁` be a BUG step from
`Y₀ = P₀ Y₀ Q₀` with orthogonal projectors of the trace of the projectors `Pu₀ = X₀ G₀`,
`Pv₀ = G₀ X₀` of a reference `X₀`; let `G₀`, `G₁` be generalized inverses of the references
`X₀`, `X₁` with symmetric `X G`, `G X` and `‖G₀‖₂, ‖G₁‖₂ ≤ g`, let the tail `A₀ - X₀` be
orthogonal to `X₀`, and with `ΔR = (A₁ - X₁) - (A₀ - X₀)` let

  `g ‖X₁ - X₀‖₂ ≤ η_X`, `g ‖ΔR‖₂ ≤ η_R`, `g ‖X₁ - X₀‖ ≤ η_F`, `g ‖A₁ - A₀‖ ≤ η_F`,
  `g ‖Y₀ - X₀‖ ≤ θ`, `1 ≤ (1 - 2 θ) c`, `1 ≤ (1 - (η_F + θ)) d`,
  `2 η_X (η_X + θ) d (1 + d) ≤ β²`, `‖(A₁ - X₁) Pv₀‖² + ‖Pu₀ (A₁ - X₁)‖² ≤ ω²`.

Then

  `‖Y₁ - X₁‖ ≤ (1 + 3/2 η_R + η_X (η_X + θ) d (1 + d) (1 + η_R)²
        + c η_F (η_R + η_X (d (1 + η_R) + 1))) ‖Y₀ - X₀‖
      + (1 + β + c η_F (1 + d η_X)) ω + c² η_F² ‖ΔR‖₂`.

At first order in the step the factor of the old error is `1 + 3/2 η_R + η_X θ d (1 + d)` and the
source is `ω`, the tail at the new time seen from the row and the column space of the old
reference. The radius `θ` is restricted by `θ < 1/2` and `η_F + θ < 1` only (through `c` and
`d`). -/
theorem norm_projStep_sub_le_of_trace_of_norm_tail_sq_le (hP : IsOrthProjMat P)
    (hQ : IsOrthProjMat Q) (hP₀ : IsOrthProjMat P₀) (hQ₀ : IsOrthProjMat Q₀)
    (hY₀P : P₀ * Y₀ = Y₀) (hY₀Q : Y₀ * Q₀ = Y₀)
    (hK : P * ((Y₀ + (A₁ - A₀)) * Q₀) = (Y₀ + (A₁ - A₀)) * Q₀)
    (hL : P₀ * (Y₀ + (A₁ - A₀)) * Q = P₀ * (Y₀ + (A₁ - A₀)))
    (hX₀ : X₀ * G₀ * X₀ = X₀) (hc₀ : (X₀ * G₀)ᵀ = X₀ * G₀) (hr₀ : (G₀ * X₀)ᵀ = G₀ * X₀)
    (hX₁ : X₁ * G₁ * X₁ = X₁) (hc₁ : (X₁ * G₁)ᵀ = X₁ * G₁) (hr₁ : (G₁ * X₁)ᵀ = G₁ * X₁)
    (hRG₀ : (A₀ - X₀) * G₀ = 0) (hGR₀ : G₀ * (A₀ - X₀) = 0)
    (htrP : trace P = trace P₀) (htrQ : trace Q = trace Q₀)
    (htrP₀ : trace P₀ = trace (X₀ * G₀)) (htrQ₀ : trace Q₀ = trace (G₀ * X₀))
    (hG₀ : specNorm G₀ ≤ g) (hG₁ : specNorm G₁ ≤ g) (hξ₂ : g * specNorm (X₁ - X₀) ≤ ηX)
    (hδ : g * specNorm (A₁ - X₁ - (A₀ - X₀)) ≤ ηR) (hξ : g * ‖X₁ - X₀‖ ≤ ηF)
    (hν : g * ‖A₁ - A₀‖ ≤ ηF) (he : g * ‖Y₀ - X₀‖ ≤ θ) (hc0 : 0 ≤ c)
    (hc : 1 ≤ (1 - 2 * θ) * c) (hd0 : 0 ≤ d) (hd : 1 ≤ (1 - (ηF + θ)) * d) (hβ0 : 0 ≤ β)
    (hβ : 2 * (ηX * (ηX + θ) * d * (1 + d)) ≤ β ^ 2) (hω0 : 0 ≤ ω)
    (hω : ‖(A₁ - X₁) * (G₀ * X₀)‖ ^ 2 + ‖X₀ * G₀ * (A₁ - X₁)‖ ^ 2 ≤ ω ^ 2) :
    ‖P * (Y₀ + (A₁ - A₀)) * Q - X₁‖ ≤
      (1 + 3 / 2 * ηR + ηX * (ηX + θ) * d * (1 + d) * (1 + ηR) ^ 2 +
          c * ηF * (ηR + ηX * (d * (1 + ηR) + 1))) * ‖Y₀ - X₀‖ +
        (1 + β + c * ηF * (1 + d * ηX)) * ω +
        c ^ 2 * ηF ^ 2 * specNorm (A₁ - X₁ - (A₀ - X₀)) := by
  have hg : 0 ≤ g := (specNorm_nonneg _).trans hG₀
  have hθ0 : 0 ≤ θ := (mul_nonneg hg (norm_nonneg _)).trans he
  have hηF0 : 0 ≤ ηF := (mul_nonneg hg (norm_nonneg _)).trans hξ
  have hmis : Y₀ + (A₁ - A₀) - X₁ = Y₀ - X₀ + (A₁ - X₁ - (A₀ - X₀)) := by abel
  have hD : A₁ - A₀ = X₁ - X₀ + (A₁ - X₁ - (A₀ - X₀)) := by abel
  -- the tail increment seen from the old bases
  have ha0 := norm_tail_sub_mul_le_add_norm_mul_rowProj (R₁ := A₁ - X₁) hQ₀ hY₀Q hX₀ hr₀ htrQ₀
    hRG₀ hG₀ le_rfl
  have hb0 := norm_mul_tail_sub_le_add_norm_colProj_mul (R₁ := A₁ - X₁) hP₀ hY₀P hX₀ hc₀ htrP₀
    hGR₀ hG₀ le_rfl
  have hαle : specNorm (A₁ - X₁ - (A₀ - X₀)) * (g * ‖Y₀ - X₀‖) ≤ ηR * ‖Y₀ - X₀‖ := by
    have h1 : specNorm (A₁ - X₁ - (A₀ - X₀)) * (g * ‖Y₀ - X₀‖) =
        g * specNorm (A₁ - X₁ - (A₀ - X₀)) * ‖Y₀ - X₀‖ := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right hδ (norm_nonneg _)
  have ha := ha0.trans (add_le_add hαle le_rfl)
  have hb := hb0.trans (add_le_add hαle le_rfl)
  -- the angles between the old and the new bases
  have hdK := one_sub_mul_norm_mul_one_sub_le_of_capture hP hP₀ hQ₀ hY₀P hY₀Q hK hX₀ hc₀ htrP
    htrP₀ hG₀
  have hdL := one_sub_mul_norm_one_sub_mul_le_of_capture hQ hP₀ hQ₀ hY₀P hY₀Q hL hX₀ hr₀ htrQ
    htrQ₀ hG₀
  have hdK' : ‖P * (1 - P₀)‖ ≤ c * ηF := by
    refine le_mul_of_one_sub_mul_le (norm_nonneg _) hc0 hc ?_
    have := mul_le_mul_of_nonneg_right
      (by linarith : 1 - 2 * θ ≤ 1 - 2 * (g * ‖Y₀ - X₀‖)) (norm_nonneg (P * (1 - P₀)))
    linarith
  have hdL' : ‖(1 - Q₀) * Q‖ ≤ c * ηF := by
    refine le_mul_of_one_sub_mul_le (norm_nonneg _) hc0 hc ?_
    have := mul_le_mul_of_nonneg_right
      (by linarith : 1 - 2 * θ ≤ 1 - 2 * (g * ‖Y₀ - X₀‖)) (norm_nonneg ((1 - Q₀) * Q))
    linarith
  -- capture of the reference
  have hs : specNorm G₁ * specNorm (X₁ - Y₀) ≤ ηF + θ := by
    have h1 : specNorm (X₁ - Y₀) ≤ ‖X₁ - X₀‖ + ‖Y₀ - X₀‖ :=
      (specNorm_le_frob _).trans ((norm_sub_le_norm_sub_add_norm_sub X₁ X₀ Y₀).trans_eq
        (by rw [norm_sub_rev X₀ Y₀]))
    have h2 : specNorm G₁ * specNorm (X₁ - Y₀) ≤ g * (‖X₁ - X₀‖ + ‖Y₀ - X₀‖) :=
      mul_le_mul hG₁ h1 (specNorm_nonneg _) hg
    linarith
  have hu0 := one_sub_mul_norm_one_sub_mul_le hP hQ₀ hY₀Q hK hX₁ hs
  have hv0 := one_sub_mul_norm_mul_one_sub_le hQ hP₀ hY₀P hL hX₁ hs
  rw [hmis] at hu0 hv0
  have hu : ‖(1 - P) * X₁‖ ≤ d * (‖Y₀ - X₀‖ + ‖(A₁ - X₁ - (A₀ - X₀)) * Q₀‖) := by
    refine le_mul_of_one_sub_mul_le (norm_nonneg _) hd0 hd (hu0.trans ?_)
    rw [Matrix.add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hQ₀.norm_mul_le' _) le_rfl)
  have hv : ‖X₁ * (1 - Q)‖ ≤ d * (‖Y₀ - X₀‖ + ‖P₀ * (A₁ - X₁ - (A₀ - X₀))‖) := by
    refine le_mul_of_one_sub_mul_le (norm_nonneg _) hd0 hd (hv0.trans ?_)
    rw [Matrix.mul_add]
    exact (norm_add_le _ _).trans (add_le_add (hP₀.norm_mul_le _) le_rfl)
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
  -- the normal component of the reference and the exchanged old error
  have hsq := norm_sub_sub_one_sub_mul_sub_mul_one_sub_sq_le (X₀ := X₀) (X₁ := X₁) hP hQ₀ hY₀Q
  have hnb : ‖(1 - P) * X₁ * (1 - Q₀)‖ ≤ ‖(1 - P) * X₁‖ * (g * specNorm (X₁ - X₀) + θ) := by
    refine (norm_one_sub_mul_mul_one_sub_le (X₀ := X₀) hQ₀ hY₀Q hX₁ hG₁).trans
      (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [mul_add]
    linarith
  -- the tail increment through the new bases
  have n12 := norm_one_sub_mul_add_mul_sq_le hP ((A₁ - X₁ - (A₀ - X₀)) * Q₀)
    (P₀ * (A₁ - X₁ - (A₀ - X₀)))
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
      Y₀ - X₀ - (1 - P) * (X₁ - X₀) * (1 - Q₀) +
        ((1 - P) * ((A₁ - X₁ - (A₀ - X₀)) * Q₀) + P * (P₀ * (A₁ - X₁ - (A₀ - X₀))) +
        P * (1 - P₀) * ((A₁ - X₁ - (A₀ - X₀)) * Q₀) * Q +
        P * (1 - P₀) * (A₁ - X₁ - (A₀ - X₀)) * ((1 - Q₀) * Q)) -
        P * ((1 - P₀) * (X₁ - X₀) * (1 - Q)) := by
    rw [projStep_eq_add_sub hY₀P hY₀Q hK hL]
    have hXX : X₁ = X₀ + (X₁ - X₀) := by abel
    conv_lhs => rw [hD, hXX]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc]
    abel
  have H : ‖P * (Y₀ + (A₁ - A₀)) * Q - X₁‖ ≤
      ‖Y₀ - X₀ - (1 - P) * (X₁ - X₀) * (1 - Q₀)‖ +
        (‖(1 - P) * ((A₁ - X₁ - (A₀ - X₀)) * Q₀) + P * (P₀ * (A₁ - X₁ - (A₀ - X₀)))‖ +
        ‖P * (1 - P₀)‖ * ‖(A₁ - X₁ - (A₀ - X₀)) * Q₀‖ +
        ‖P * (1 - P₀)‖ * specNorm (A₁ - X₁ - (A₀ - X₀)) * ‖(1 - Q₀) * Q‖) +
        ‖P * (1 - P₀)‖ * (g * specNorm (X₁ - X₀) * (‖X₁ * (1 - Q)‖ + ‖Y₀ - X₀‖)) := by
    rw [hstep]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add le_rfl ?_)) n6)
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add le_rfl n3)) n4)
  exact step_arith_source (norm_nonneg _) (specNorm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (mul_nonneg hg (specNorm_nonneg _))
    ((mul_nonneg hg (specNorm_nonneg _)).trans hδ) hηF0 (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) hθ0 hc0 hd0 hβ0 hω0 hξ₂ hβ H hsq hnb ht5 n12 ha hb hω hu hv hdK' hdL'

end Main

end MatrixBUG

end LeanDLRA
