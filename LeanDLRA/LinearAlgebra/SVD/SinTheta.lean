import LeanDLRA.Classical.WeylSingular
import LeanDLRA.Classical.SVD
import LeanDLRA.Classical.BestApproximation

/-!
# Sin-Θ theorems: Wedin and Davis–Kahan

Perturbation bounds for singular and eigen subspaces. For real matrices `A`, `B` let `V`, `Ṽ` be
the top-`(r + 1)` right singular vectors (`EckartYoung.topRightSingularVectors`), and assume the
gap `σ_{r+1}(A) + δ ≤ σ_r(B)` with `δ > 0` (singular values `0`-indexed and decreasing). Then the
part of `Ṽ` outside the range of `V` has Frobenius norm at most `√2 ‖B - A‖ / δ`, and the
truncated singular value decomposition satisfies a Lipschitz bound with an explicit constant.
For symmetric operators the same holds for eigenvectors (Davis–Kahan).

## Main results

* `LeanDLRA.SinTheta.wedin_frobenius`: `‖(1 - V Vᵀ) Ṽ‖_F ≤ √2 ‖B - A‖_F / δ`.
* `LeanDLRA.SinTheta.wedin_specNorm`: `‖(1 - V Vᵀ) Ṽ‖₂ ≤ ‖B - A‖₂ / δ`.
* `LeanDLRA.SinTheta.norm_truncation_sub_le_of_gap`:
  `‖T_{r+1}(B) - T_{r+1}(A)‖_F ≤ (1 + √2 (σ_0(A) + σ_{r+1}(A)) / δ) ‖B - A‖_F`.
* `LeanDLRA.SinTheta.davisKahan`: for symmetric `T`, `T'` on a finite-dimensional real inner
  product space with `‖T' x - T x‖ ≤ ε ‖x‖` and `λ_{r+1}(T) + δ ≤ λ_r(T')`, a vector in the
  top-`(r + 1)` eigenspace of `T'` has a component of norm at most `ε ‖x‖ / δ` in the bottom
  eigenspace of `T`.

## Implementation notes

`norm_sub_le_of_isOrthProjMat` in `LeanDLRA/LinearAlgebra/SVD/TruncationDeriv.lean` is a
Davis–Kahan bound of another form: it bounds `‖P' - P‖` by `‖Bᵀ B - Aᵀ A‖` for any orthogonal
projectors `P`, `P'` that commute with `Aᵀ A`, `Bᵀ B`, under gaps on both sides. Neither result
implies the other. The bounds of this file need the gap on one side only and are stated in
`‖B - A‖` (the Lipschitz bound of the truncation passes from one side to both through the equal
rank of the two projectors); the bound there holds for projectors that are not given by singular
vectors, which the uniqueness of the spectral projector under a gap needs.

## References

* P.-Å. Wedin, *Perturbation bounds in connection with singular value decomposition*, BIT 12
  (1972)
* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*, SIAM J. Numer.
  Anal. 7 (1970)
* G. W. Stewart and J.-G. Sun, *Matrix Perturbation Theory*, Academic Press 1990, §V.4
-/

open Matrix WithLp Module Finset
open scoped RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA.SinTheta

open EckartYoung Curvature

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- The columns of `V_k` are eigenvectors of `Aᵀ A`: `Aᵀ A V_k = V_k diag(σ_i²)`. -/
private theorem transpose_mul_self_mul_top (A : Matrix m n ℝ) (k : ℕ) :
    Aᵀ * A * topRightSingularVectors A k = topRightSingularVectors A k *
      (diagonal fun i : {i : Fin (finrank ℝ (EuclideanSpace ℝ n)) // (i : ℕ) < k} ↦
        (toEuclideanLin A).singularValues i ^ 2 : Matrix _ _ ℝ) := by
  ext j i
  have h := congrFun (transpose_mul_self_mulVec_rightSingularVectors A i.1) j
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  simp only [topRightSingularVectors]
  rw [h, mul_comm]

omit [DecidableEq m] in
/-- The projector `V_k V_kᵀ` commutes with `Aᵀ A`. -/
private theorem proj_comm (A : Matrix m n ℝ) (k : ℕ) :
    (1 - topRightSingularVectors A k * (topRightSingularVectors A k)ᵀ) * (Aᵀ * A) =
      (Aᵀ * A) * (1 - topRightSingularVectors A k * (topRightSingularVectors A k)ᵀ) := by
  have h := transpose_mul_self_mul_top A k
  have h' := congrArg Matrix.transpose h
  rw [transpose_mul, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose] at h'
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, h',
    ← Matrix.mul_assoc (Aᵀ * A), h, Matrix.mul_assoc]

omit [DecidableEq m] [DecidableEq n] in
/-- The algebra behind Wedin's theorem: eliminating the left singular vectors.  With
`A₂ = A Q`, `X = Q Y`, `B = A + F`, the relations `Bᵀ U = Y D`, `U = B Y W` give the Sylvester
equation `X D = A₂ᵀ A₂ X W + A₂ᵀ F Y W + Q Fᵀ U`. -/
private theorem wedin_identity {ι : Type*} [Fintype ι] {A F : Matrix m n ℝ} {Q : Matrix n n ℝ}
    (hQ : IsOrthProjMat Q) (hcomm : Q * (Aᵀ * A) = (Aᵀ * A) * Q)
    {Y : Matrix n ι ℝ} {U : Matrix m ι ℝ} {D W : Matrix ι ι ℝ}
    (h1 : (A + F)ᵀ * U = Y * D) (h2 : U = (A + F) * Y * W) :
    Q * Y * D = (A * Q)ᵀ * (A * Q) * (Q * Y) * W + (A * Q)ᵀ * F * Y * W + Q * Fᵀ * U := by
  have hA2 : (A * Q)ᵀ = Q * Aᵀ := by rw [transpose_mul, hQ.symm]
  have hmain : (A * Q)ᵀ * A = (A * Q)ᵀ * (A * Q) := by
    rw [hA2]
    calc Q * Aᵀ * A = Q * (Aᵀ * A) := Matrix.mul_assoc ..
      _ = (Q * Q) * (Aᵀ * A) := by rw [hQ.idem]
      _ = Q * ((Aᵀ * A) * Q) := by rw [Matrix.mul_assoc, hcomm]
      _ = Q * Aᵀ * (A * Q) := by simp only [Matrix.mul_assoc]
  have hX : (A * Q) * (Q * Y) = (A * Q) * Y := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Q, hQ.idem]
  have h3 : (A * Q)ᵀ * U = (A * Q)ᵀ * (A * Q) * (Q * Y) * W + (A * Q)ᵀ * F * Y * W := by
    have e1 : (A * Q)ᵀ * ((A + F) * Y * W) = (A * Q)ᵀ * A * Y * W + (A * Q)ᵀ * F * Y * W := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    have e2 : (A * Q)ᵀ * (A * Q) * (Q * Y) = (A * Q)ᵀ * (A * Q) * Y := by
      rw [Matrix.mul_assoc, hX, ← Matrix.mul_assoc]
    rw [h2, e1, hmain, e2]
  calc Q * Y * D = Q * (Y * D) := Matrix.mul_assoc ..
    _ = Q * (A + F)ᵀ * U := by rw [← h1, Matrix.mul_assoc]
    _ = (A * Q)ᵀ * U + Q * Fᵀ * U := by
        rw [transpose_add, Matrix.mul_add, Matrix.add_mul, hA2]
    _ = _ := by rw [h3]

/-- The real arithmetic closing Wedin's bound. -/
private theorem wedin_real {α δ s x f : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ) (hs : α + δ ≤ s) (hx : 0 ≤ x)
    (h : x ≤ (α * α * x * s⁻¹ + α * f * s⁻¹ + f) * s⁻¹) : δ * x ≤ f := by
  have hs0 : 0 < s := by linarith
  have h1 : s * s * x ≤ α * α * x + α * f + s * f := by
    have := mul_le_mul_of_nonneg_left h (mul_pos hs0 hs0).le
    have e : s * s * ((α * α * x * s⁻¹ + α * f * s⁻¹ + f) * s⁻¹) =
        α * α * x + α * f + s * f := by
      field_simp
    rwa [e] at this
  have h2 : (s + α) * ((s - α) * x) ≤ (s + α) * f := by nlinarith
  have h3 : (s - α) * x ≤ f := le_of_mul_le_mul_left h2 (by linarith)
  have h4 : δ * x ≤ (s - α) * x := mul_le_mul_of_nonneg_right (by linarith) hx
  linarith

/-- A diagonal matrix with entries of absolute value at most `c` has spectral norm at most `c`. -/
private theorem specNorm_diagonal_le {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i, |d i| ≤ c) : specNorm (diagonal d) ≤ c := by
  refine specNorm_le_of hc fun x ↦ ?_
  have hsq : ‖toEuclideanLin (diagonal d) x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    simp only [Matrix.toLpLin_apply, mulVec_diagonal, Real.norm_eq_abs, sq_abs, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs (d i)]
    exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

omit [DecidableEq m] in
/-- The Sylvester equation of Wedin's theorem for the top `r + 1` right singular vectors `Y` of
`B`: the left singular vectors are `U = B Y W`, `W = D⁻¹`, `D = diag(σ_i(B)) ≥ s > 0`. -/
private theorem wedin_setup (A B : Matrix m n ℝ) (r : ℕ) {s : ℝ} (hs : 0 < s)
    (hsB : s ≤ (toEuclideanLin B).singularValues r) :
    ∃ (U : Matrix m {i : Fin (finrank ℝ (EuclideanSpace ℝ n)) // (i : ℕ) < r + 1} ℝ)
      (D W : Matrix {i : Fin (finrank ℝ (EuclideanSpace ℝ n)) // (i : ℕ) < r + 1}
        {i : Fin (finrank ℝ (EuclideanSpace ℝ n)) // (i : ℕ) < r + 1} ℝ),
      specNorm U ≤ 1 ∧ D * W = 1 ∧ specNorm W ≤ s⁻¹ ∧
      (1 - topRightSingularVectors A (r + 1) * (topRightSingularVectors A (r + 1))ᵀ) *
          topRightSingularVectors B (r + 1) * D =
        (A * (1 - topRightSingularVectors A (r + 1) * (topRightSingularVectors A (r + 1))ᵀ))ᵀ *
            (A * (1 - topRightSingularVectors A (r + 1) * (topRightSingularVectors A (r + 1))ᵀ)) *
            ((1 - topRightSingularVectors A (r + 1) * (topRightSingularVectors A (r + 1))ᵀ) *
              topRightSingularVectors B (r + 1)) * W +
          (A * (1 - topRightSingularVectors A (r + 1) * (topRightSingularVectors A (r + 1))ᵀ))ᵀ *
            (B - A) * topRightSingularVectors B (r + 1) * W +
          (1 - topRightSingularVectors A (r + 1) * (topRightSingularVectors A (r + 1))ᵀ) *
            (B - A)ᵀ * U := by
  set Y := topRightSingularVectors B (r + 1) with hYdef
  have hY : Yᵀ * Y = 1 := transpose_mul_topRightSingularVectors B (r + 1)
  have hQ : IsOrthProjMat
      (1 - topRightSingularVectors A (r + 1) * (topRightSingularVectors A (r + 1))ᵀ) :=
    (isOrthProjMat_mul_transpose (transpose_mul_topRightSingularVectors A (r + 1))).compl
  set σ : {i : Fin (finrank ℝ (EuclideanSpace ℝ n)) // (i : ℕ) < r + 1} → ℝ :=
    fun i ↦ (toEuclideanLin B).singularValues i with hσdef
  have hσ : ∀ i, s ≤ σ i := fun i ↦ hsB.trans
    ((toEuclideanLin B).singularValues_antitone (Nat.lt_succ_iff.mp i.2))
  have hσ0 : ∀ i, σ i ≠ 0 := fun i ↦ (hs.trans_le (hσ i)).ne'
  have hBY : Bᵀ * B * Y = Y * diagonal fun i ↦ σ i ^ 2 := transpose_mul_self_mul_top B (r + 1)
  have hDW : diagonal σ * diagonal (fun i ↦ (σ i)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun i ↦ mul_inv_cancel₀ (hσ0 i))
  have hS : (diagonal fun i ↦ σ i ^ 2) * diagonal (fun i ↦ (σ i)⁻¹) = diagonal σ := by
    rw [diagonal_mul_diagonal]
    exact congrArg diagonal (funext fun i ↦ by rw [sq, mul_assoc, mul_inv_cancel₀ (hσ0 i), mul_one])
  have hBU : Bᵀ * (B * Y * diagonal fun i ↦ (σ i)⁻¹) = Y * diagonal σ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBY, Matrix.mul_assoc, hS]
  have hUU : (B * Y * diagonal fun i ↦ (σ i)⁻¹)ᵀ * (B * Y * diagonal fun i ↦ (σ i)⁻¹) = 1 := by
    rw [transpose_mul, transpose_mul, diagonal_transpose, Matrix.mul_assoc, Matrix.mul_assoc, hBU,
      ← Matrix.mul_assoc Yᵀ, hY, Matrix.one_mul]
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun i ↦ inv_mul_cancel₀ (hσ0 i))
  have hF : A + (B - A) = B := add_sub_cancel _ _
  refine ⟨B * Y * diagonal fun i ↦ (σ i)⁻¹, diagonal σ, diagonal fun i ↦ (σ i)⁻¹,
    specNorm_le_one_of_orthonormal hUU, hDW, specNorm_diagonal_le _ (inv_nonneg.mpr hs.le)
      fun i ↦ ?_, wedin_identity hQ (proj_comm A (r + 1)) (by rw [hF]; exact hBU) (by rw [hF])⟩
  rw [abs_of_pos (inv_pos.mpr (hs.trans_le (hσ i)))]
  exact inv_anti₀ hs (hσ i)

omit [DecidableEq m] in
/-- `A (1 - V Vᵀ) = A - T_k(A)` has spectral norm `σ_k(A)`. -/
private theorem specNorm_mul_compl (A : Matrix m n ℝ) (k : ℕ) :
    specNorm (A * (1 - topRightSingularVectors A k * (topRightSingularVectors A k)ᵀ)) =
      (toEuclideanLin A).singularValues k := by
  rw [← specNorm_sub_truncation A k, truncation, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]

omit [DecidableEq m] in
/-- Wedin's theorem in the Frobenius norm, without the factor `√2`:
`δ ‖(1 - V Vᵀ) Ṽ‖_F ≤ ‖B - A‖_F`. -/
private theorem wedin_frobenius_aux (A B : Matrix m n ℝ) (r : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : (toEuclideanLin A).singularValues (r + 1) + δ ≤
      (toEuclideanLin B).singularValues r) :
    δ * ‖(1 - topRightSingularVectors A (r + 1) * (topRightSingularVectors A (r + 1))ᵀ) *
        topRightSingularVectors B (r + 1)‖ ≤ ‖B - A‖ := by
  classical
  have hα0 := (toEuclideanLin A).singularValues_nonneg (r + 1)
  have hs : 0 < (toEuclideanLin B).singularValues r := by linarith
  obtain ⟨U, D, W, hU, hDW, hW, hid⟩ := wedin_setup A B r hs le_rfl
  set s := (toEuclideanLin B).singularValues r
  have hα := specNorm_mul_compl A (r + 1)
  set α := (toEuclideanLin A).singularValues (r + 1)
  set Y := topRightSingularVectors B (r + 1) with hYdef
  have hY : specNorm Y ≤ 1 :=
    specNorm_le_one_of_orthonormal (transpose_mul_topRightSingularVectors B (r + 1))
  have hQ : specNorm
      (1 - topRightSingularVectors A (r + 1) * (topRightSingularVectors A (r + 1))ᵀ) ≤ 1 :=
    IsOrthProjMat.specNorm_le_one
      (isOrthProjMat_mul_transpose (transpose_mul_topRightSingularVectors A (r + 1))).compl
  set Q := 1 - topRightSingularVectors A (r + 1) * (topRightSingularVectors A (r + 1))ᵀ with hQdef
  set T := A * Q with hTdef
  set F := B - A with hFdef
  set X := Q * Y with hXdef
  have hTt : specNorm Tᵀ = α := by rw [specNorm_transpose, hα]
  have hsi : 0 ≤ s⁻¹ := (inv_pos.mpr hs).le
  refine wedin_real hα0 hδ hgap (norm_nonneg _) ?_
  have hXD : ‖X * D‖ ≤ α * α * ‖X‖ * s⁻¹ + α * ‖F‖ * s⁻¹ + ‖F‖ := by
    rw [hid]
    have ha : ‖Tᵀ * T * X * W‖ ≤ α * α * ‖X‖ * s⁻¹ := by
      calc ‖Tᵀ * T * X * W‖ ≤ ‖Tᵀ * T * X‖ * specNorm W := frob_mul_le' _ _
        _ ≤ α * α * ‖X‖ * s⁻¹ := by
          refine mul_le_mul ?_ hW (specNorm_nonneg _) (by positivity)
          rw [Matrix.mul_assoc]
          refine (frob_mul_le _ _).trans ?_
          rw [hTt, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hα0
          rw [← hα]
          exact frob_mul_le _ _
    have hb : ‖Tᵀ * F * Y * W‖ ≤ α * ‖F‖ * s⁻¹ := by
      calc ‖Tᵀ * F * Y * W‖ ≤ ‖Tᵀ * F * Y‖ * specNorm W := frob_mul_le' _ _
        _ ≤ α * ‖F‖ * s⁻¹ := by
          refine mul_le_mul ?_ hW (specNorm_nonneg _) (by positivity)
          calc ‖Tᵀ * F * Y‖ ≤ ‖Tᵀ * F‖ * specNorm Y := frob_mul_le' _ _
            _ ≤ ‖Tᵀ * F‖ * 1 := mul_le_mul_of_nonneg_left hY (norm_nonneg _)
            _ ≤ α * ‖F‖ := by rw [mul_one, ← hTt]; exact frob_mul_le _ _
    have hc : ‖Q * Fᵀ * U‖ ≤ ‖F‖ := by
      calc ‖Q * Fᵀ * U‖ ≤ ‖Q * Fᵀ‖ * specNorm U := frob_mul_le' _ _
        _ ≤ ‖Q * Fᵀ‖ * 1 := mul_le_mul_of_nonneg_left hU (norm_nonneg _)
        _ ≤ specNorm Q * ‖Fᵀ‖ := by rw [mul_one]; exact frob_mul_le _ _
        _ ≤ 1 * ‖Fᵀ‖ := mul_le_mul_of_nonneg_right hQ (norm_nonneg _)
        _ = ‖F‖ := by rw [one_mul, Frobenius.norm_transpose]
    exact (norm_add₃_le).trans (add_le_add (add_le_add ha hb) hc)
  calc ‖X‖ = ‖X * D * W‖ := by rw [Matrix.mul_assoc, hDW, Matrix.mul_one]
    _ ≤ ‖X * D‖ * specNorm W := frob_mul_le' _ _
    _ ≤ _ := mul_le_mul hXD hW (specNorm_nonneg _) (by positivity)

omit [DecidableEq m] in
/-- **Wedin's sin-Θ theorem, Frobenius norm** (source: Wedin 1972, BIT 12; OP-RA-45).  Let
`V`, `Ṽ` be the top-`(r+1)` right singular vectors of `A` and `B`
(`EckartYoung.topRightSingularVectors`).  If `σ_{r+1}(A) + δ ≤ σ_r(B)` with `δ > 0`, then
`‖(1 - V Vᵀ) Ṽ‖_F ≤ √2 ‖B - A‖_F / δ`. -/
theorem wedin_frobenius (A B : Matrix m n ℝ) (r : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : (toEuclideanLin A).singularValues (r + 1) + δ ≤
      (toEuclideanLin B).singularValues r) :
    ‖(1 - topRightSingularVectors A (r + 1) * (topRightSingularVectors A (r + 1))ᵀ) *
        topRightSingularVectors B (r + 1)‖ ≤ √2 * ‖B - A‖ / δ := by
  have h := wedin_frobenius_aux A B r hδ hgap
  rw [le_div_iff₀ hδ, mul_comm]
  have h1 : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
  nlinarith [norm_nonneg (B - A)]

omit [DecidableEq m] in
/-- **Wedin's sin-Θ theorem, spectral norm** (source: Wedin 1972, BIT 12; Stewart–Sun, *Matrix
Perturbation Theory*, Thm. V.4.4).  Under the
gap `σ_{r+1}(A) + δ ≤ σ_r(B)`, `‖(1 - V Vᵀ) Ṽ‖₂ ≤ ‖B - A‖₂ / δ`. -/
theorem wedin_specNorm (A B : Matrix m n ℝ) (r : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : (toEuclideanLin A).singularValues (r + 1) + δ ≤
      (toEuclideanLin B).singularValues r) :
    specNorm ((1 - topRightSingularVectors A (r + 1) * (topRightSingularVectors A (r + 1))ᵀ) *
        topRightSingularVectors B (r + 1)) ≤ specNorm (B - A) / δ := by
  classical
  have hα0 := (toEuclideanLin A).singularValues_nonneg (r + 1)
  have hs : 0 < (toEuclideanLin B).singularValues r := by linarith
  obtain ⟨U, D, W, hU, hDW, hW, hid⟩ := wedin_setup A B r hs le_rfl
  set s := (toEuclideanLin B).singularValues r
  have hα := specNorm_mul_compl A (r + 1)
  set α := (toEuclideanLin A).singularValues (r + 1)
  set Y := topRightSingularVectors B (r + 1) with hYdef
  have hY : specNorm Y ≤ 1 :=
    specNorm_le_one_of_orthonormal (transpose_mul_topRightSingularVectors B (r + 1))
  have hQ : specNorm
      (1 - topRightSingularVectors A (r + 1) * (topRightSingularVectors A (r + 1))ᵀ) ≤ 1 :=
    IsOrthProjMat.specNorm_le_one
      (isOrthProjMat_mul_transpose (transpose_mul_topRightSingularVectors A (r + 1))).compl
  set Q := 1 - topRightSingularVectors A (r + 1) * (topRightSingularVectors A (r + 1))ᵀ with hQdef
  set T := A * Q with hTdef
  set F := B - A with hFdef
  set X := Q * Y with hXdef
  have hTt : specNorm Tᵀ = α := by rw [specNorm_transpose, hα]
  have hsi : 0 ≤ s⁻¹ := (inv_pos.mpr hs).le
  have hF0 := specNorm_nonneg F
  have hX0 := specNorm_nonneg X
  rw [le_div_iff₀ hδ, mul_comm]
  refine wedin_real hα0 hδ hgap hX0 ?_
  have hXD : specNorm (X * D) ≤ α * α * specNorm X * s⁻¹ + α * specNorm F * s⁻¹ + specNorm F := by
    rw [hid]
    have ha : specNorm (Tᵀ * T * X * W) ≤ α * α * specNorm X * s⁻¹ := by
      calc specNorm (Tᵀ * T * X * W) ≤ specNorm (Tᵀ * T * X) * specNorm W := specNorm_mul_le _ _
        _ ≤ α * α * specNorm X * s⁻¹ := by
          refine mul_le_mul ?_ hW (specNorm_nonneg _) (by positivity)
          rw [Matrix.mul_assoc]
          refine (specNorm_mul_le _ _).trans ?_
          rw [hTt, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hα0
          rw [← hα]
          exact specNorm_mul_le _ _
    have hb : specNorm (Tᵀ * F * Y * W) ≤ α * specNorm F * s⁻¹ := by
      calc specNorm (Tᵀ * F * Y * W) ≤ specNorm (Tᵀ * F * Y) * specNorm W := specNorm_mul_le _ _
        _ ≤ α * specNorm F * s⁻¹ := by
          refine mul_le_mul ?_ hW (specNorm_nonneg _) (by positivity)
          calc specNorm (Tᵀ * F * Y) ≤ specNorm (Tᵀ * F) * specNorm Y := specNorm_mul_le _ _
            _ ≤ specNorm (Tᵀ * F) * 1 := mul_le_mul_of_nonneg_left hY (specNorm_nonneg _)
            _ ≤ α * specNorm F := by rw [mul_one, ← hTt]; exact specNorm_mul_le _ _
    have hc : specNorm (Q * Fᵀ * U) ≤ specNorm F := by
      calc specNorm (Q * Fᵀ * U) ≤ specNorm (Q * Fᵀ) * specNorm U := specNorm_mul_le _ _
        _ ≤ specNorm (Q * Fᵀ) * 1 := mul_le_mul_of_nonneg_left hU (specNorm_nonneg _)
        _ ≤ specNorm Q * specNorm Fᵀ := by rw [mul_one]; exact specNorm_mul_le _ _
        _ ≤ 1 * specNorm Fᵀ := mul_le_mul_of_nonneg_right hQ (specNorm_nonneg _)
        _ = specNorm F := by rw [one_mul, specNorm_transpose]
    have h1 := WeylSingular.specNorm_add_le (Tᵀ * T * X * W + Tᵀ * F * Y * W) (Q * Fᵀ * U)
    have h2 := WeylSingular.specNorm_add_le (Tᵀ * T * X * W) (Tᵀ * F * Y * W)
    linarith
  calc specNorm X = specNorm (X * D * W) := by rw [Matrix.mul_assoc, hDW, Matrix.mul_one]
    _ ≤ specNorm (X * D) * specNorm W := specNorm_mul_le _ _
    _ ≤ _ := mul_le_mul hXD hW (specNorm_nonneg _) (by positivity)

/-- Two orthogonal projectors of equal trace: `‖P (1 - R)‖_F = ‖(1 - P) R‖_F`. -/
private theorem norm_proj_mul_compl_eq {P R : Matrix n n ℝ} (hP : IsOrthProjMat P)
    (hR : IsOrthProjMat R) (htr : trace P = trace R) : ‖P * (1 - R)‖ = ‖(1 - P) * R‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [Curvature.frob_sq_eq_trace, Curvature.frob_sq_eq_trace]
  have h1 : (P * (1 - R))ᵀ * (P * (1 - R)) = (1 - R) * (P * (1 - R)) := by
    rw [transpose_mul, hP.symm, hR.compl.symm, Matrix.mul_assoc, ← Matrix.mul_assoc P P, hP.idem]
  have h2 : ((1 - P) * R)ᵀ * ((1 - P) * R) = R * ((1 - P) * R) := by
    rw [transpose_mul, hR.symm, hP.compl.symm, Matrix.mul_assoc,
      ← Matrix.mul_assoc (1 - P) (1 - P), hP.compl.idem]
  have h3 : trace ((1 - R) * (P * (1 - R))) = trace P - trace (R * P) := by
    rw [trace_mul_comm, Matrix.mul_assoc, hR.compl.idem, Matrix.mul_sub, Matrix.mul_one, trace_sub,
      trace_mul_comm P R]
  have h4 : trace (R * ((1 - P) * R)) = trace R - trace (R * P) := by
    rw [trace_mul_comm, Matrix.mul_assoc, hR.idem, Matrix.sub_mul, Matrix.one_mul, trace_sub,
      trace_mul_comm P R]
  rw [h1, h2, h3, h4, htr]

omit [DecidableEq m] in
/-- **Local Lipschitz continuity of the truncated SVD under a gap** (source: OP-RA-45, positive
direction; constant not sharp).  If `σ_{r+1}(A) + δ ≤ σ_r(B)`, `δ > 0`, then
`‖T_{r+1}(B) - T_{r+1}(A)‖_F ≤ (1 + √2 (σ_0(A) + σ_{r+1}(A)) / δ) ‖B - A‖_F`. -/
theorem norm_truncation_sub_le_of_gap (A B : Matrix m n ℝ) (r : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : (toEuclideanLin A).singularValues (r + 1) + δ ≤
      (toEuclideanLin B).singularValues r) :
    ‖truncation B (r + 1) - truncation A (r + 1)‖ ≤
      (1 + √2 * ((toEuclideanLin A).singularValues 0 +
        (toEuclideanLin A).singularValues (r + 1)) / δ) * ‖B - A‖ := by
  have hw := wedin_frobenius A B r hδ hgap
  have hV := transpose_mul_topRightSingularVectors A (r + 1)
  have hY := transpose_mul_topRightSingularVectors B (r + 1)
  have hP := isOrthProjMat_mul_transpose hV
  have hR := isOrthProjMat_mul_transpose hY
  have hα := specNorm_mul_compl A (r + 1)
  have hA0 := specNorm_eq_singularValues_zero A
  have htrunc : ∀ C : Matrix m n ℝ, truncation C (r + 1) = C * (topRightSingularVectors C (r + 1) *
      (topRightSingularVectors C (r + 1))ᵀ) := fun C ↦ by rw [truncation, Matrix.mul_assoc]
  rw [htrunc, htrunc]
  set V := topRightSingularVectors A (r + 1) with hVdef
  set Y := topRightSingularVectors B (r + 1) with hYdef
  set P := V * Vᵀ with hPdef
  set R := Y * Yᵀ with hRdef
  have hPR : ‖P * (1 - R)‖ = ‖(1 - P) * R‖ := norm_proj_mul_compl_eq hP hR (by
    rw [hPdef, hRdef, trace_mul_transpose hV, trace_mul_transpose hY])
  have hRn : ‖(1 - P) * R‖ ≤ √2 * ‖B - A‖ / δ := by
    rw [hRdef, ← Matrix.mul_assoc, Frobenius.norm_mul_transpose_of_orthonormal hY]
    exact hw
  set w := √2 * ‖B - A‖ / δ with hwdef
  set a₀ := (toEuclideanLin A).singularValues 0
  set α := (toEuclideanLin A).singularValues (r + 1)
  have ha₀ : 0 ≤ a₀ := (toEuclideanLin A).singularValues_nonneg 0
  have hα0 : 0 ≤ α := (toEuclideanLin A).singularValues_nonneg (r + 1)
  have hdec : B * R - A * P = (B - A) * R - A * (P * (1 - R)) + A * ((1 - P) * ((1 - P) * R)) := by
    have hidem : (1 - P) * ((1 - P) * R) = (1 - P) * R := by
      rw [← Matrix.mul_assoc, hP.compl.idem]
    rw [hidem]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  have h1 : ‖(B - A) * R‖ ≤ ‖B - A‖ := by
    calc ‖(B - A) * R‖ ≤ ‖B - A‖ * specNorm R := frob_mul_le' _ _
      _ ≤ ‖B - A‖ * 1 := mul_le_mul_of_nonneg_left hR.specNorm_le_one (norm_nonneg _)
      _ = ‖B - A‖ := mul_one _
  have h2 : ‖A * (P * (1 - R))‖ ≤ a₀ * w := by
    calc ‖A * (P * (1 - R))‖ ≤ specNorm A * ‖P * (1 - R)‖ := frob_mul_le _ _
      _ ≤ a₀ * w := by
        rw [hA0, hPR]
        exact mul_le_mul_of_nonneg_left hRn ha₀
  have h3 : ‖A * ((1 - P) * ((1 - P) * R))‖ ≤ α * w := by
    rw [← Matrix.mul_assoc]
    calc ‖A * (1 - P) * ((1 - P) * R)‖ ≤ specNorm (A * (1 - P)) * ‖(1 - P) * R‖ := frob_mul_le _ _
      _ ≤ α * w := by
        rw [hα]
        exact mul_le_mul_of_nonneg_left hRn hα0
  rw [hdec]
  have h4 := norm_add_le ((B - A) * R - A * (P * (1 - R))) (A * ((1 - P) * ((1 - P) * R)))
  have h5 := norm_sub_le ((B - A) * R) (A * (P * (1 - R)))
  have e : (1 + √2 * (a₀ + α) / δ) * ‖B - A‖ = ‖B - A‖ + a₀ * w + α * w := by
    rw [hwdef]; ring
  rw [e]
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The separation bound for the Sylvester equation in coordinates: if `G j i = (μ i - ν j) C j i`
with `μ ≥ c`, `t ≤ ν ≤ a`, `a + δ ≤ c`, then `δ ‖C‖₂ ≤ ‖G‖₂`. -/
private theorem mul_specNorm_le_of_sylvester {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    {C G : Matrix J I ℝ} {μ : I → ℝ} {ν : J → ℝ} {a c t δ : ℝ} (hδ : 0 < δ)
    (hac : a + δ ≤ c) (hta : t ≤ a) (hμ : ∀ i, c ≤ μ i) (hν : ∀ j, t ≤ ν j ∧ ν j ≤ a)
    (hG : ∀ j i, G j i = (μ i - ν j) * C j i) : δ * specNorm C ≤ specNorm G := by
  classical
  have hct : 0 < c - t := by linarith
  have hC : C = (G + diagonal (fun j ↦ ν j - t) * C) * diagonal fun i ↦ (μ i - t)⁻¹ := by
    ext j i
    have h0 : μ i - t ≠ 0 := by have := hμ i; linarith
    rw [Matrix.mul_diagonal, Matrix.add_apply, Matrix.diagonal_mul, hG]
    field_simp
    ring
  have hW : specNorm (diagonal fun i ↦ (μ i - t)⁻¹) ≤ (c - t)⁻¹ := by
    refine specNorm_diagonal_le _ (inv_pos.mpr hct).le fun i ↦ ?_
    have h1 : c - t ≤ μ i - t := by have := hμ i; linarith
    rw [abs_of_pos (inv_pos.mpr (hct.trans_le h1))]
    exact inv_anti₀ hct h1
  have hD : specNorm (diagonal fun j ↦ ν j - t) ≤ a - t := by
    refine specNorm_diagonal_le _ (by linarith) fun j ↦ ?_
    rw [abs_of_nonneg (by linarith [(hν j).1])]
    linarith [(hν j).2]
  have h1 : specNorm C ≤ (specNorm G + (a - t) * specNorm C) * (c - t)⁻¹ := by
    calc specNorm C ≤ specNorm (G + diagonal (fun j ↦ ν j - t) * C) *
          specNorm (diagonal fun i ↦ (μ i - t)⁻¹) := by
          conv_lhs => rw [hC]
          exact specNorm_mul_le _ _
      _ ≤ (specNorm G + (a - t) * specNorm C) * (c - t)⁻¹ := by
          refine mul_le_mul ?_ hW (specNorm_nonneg _)
            (add_nonneg (specNorm_nonneg _) (mul_nonneg (by linarith) (specNorm_nonneg _)))
          refine (WeylSingular.specNorm_add_le _ _).trans (add_le_add le_rfl ?_)
          exact (specNorm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right hD (specNorm_nonneg _))
  have h2 : (c - t) * specNorm C ≤ specNorm G + (a - t) * specNorm C := by
    rwa [← div_eq_mul_inv, le_div_iff₀ hct, mul_comm] at h1
  have h3 := specNorm_nonneg C
  nlinarith

omit [FiniteDimensional ℝ E] in
/-- Bessel's inequality for a part of an orthonormal basis. -/
private theorem sum_subtype_sq_inner_le {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E)
    (p : Fin d → Prop) [DecidablePred p] (w : E) :
    ∑ j : {j // p j}, ⟪b j, w⟫ ^ 2 ≤ ‖w‖ ^ 2 := by
  rw [← b.sum_sq_inner_right w,
    ← Finset.sum_subtype (univ.filter p) (by simp) fun j ↦ ⟪b j, w⟫ ^ 2]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun _ _ _ ↦ sq_nonneg _

/-- **Davis–Kahan sin-Θ theorem** (source: Davis–Kahan 1970, SIAM J. Numer. Anal. 7).  Let `T`,
`T'` be symmetric on a `d`-dimensional real inner product space with sorted eigenbases `eᵢ`, `e'ᵢ`
and `‖T' x - T x‖ ≤ ε ‖x‖`.  If `λ_{r+1}(T) + δ ≤ λ_r(T')`, `δ > 0`, then every `x` in the
top-`(r+1)` eigenspace of `T'` has a component of norm at most `ε ‖x‖ / δ` in the bottom
eigenspace `span {e_j : j > r}` of `T`. -/
theorem davisKahan {d r : ℕ} (hn : finrank ℝ E = d) {T T' : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hT' : T'.IsSymmetric) {ε δ : ℝ} (hδ : 0 < δ) (hε : ∀ x, ‖T' x - T x‖ ≤ ε * ‖x‖)
    (hr : r + 1 < d)
    (hgap : hT.eigenvalues hn ⟨r + 1, hr⟩ + δ ≤ hT'.eigenvalues hn ⟨r, by omega⟩) {x : E}
    (hx : x ∈ Submodule.span ℝ (hT'.eigenvectorBasis hn '' {i | (i : ℕ) ≤ r})) :
    ∑ j ∈ univ.filter (fun j : Fin d ↦ r < (j : ℕ)), ⟪hT.eigenvectorBasis hn j, x⟫ ^ 2 ≤
      (ε * ‖x‖ / δ) ^ 2 := by
  classical
  have hanti := hT.eigenvalues_antitone hn
  have hanti' := hT'.eigenvalues_antitone hn
  set b := hT.eigenvectorBasis hn with hbdef
  set b' := hT'.eigenvectorBasis hn with hb'def
  set lam := hT.eigenvalues hn with hlam
  set lam' := hT'.eigenvalues hn with hlam'
  have hb : ∀ i, T (b i) = lam i • b i := hT.apply_eigenvectorBasis hn
  have hb' : ∀ i, T' (b' i) = lam' i • b' i := hT'.apply_eigenvectorBasis hn
  have hε0 : 0 ≤ ε := by
    have h := hε (b ⟨0, by omega⟩)
    rw [b.orthonormal.1, mul_one] at h
    exact (norm_nonneg _).trans h
  -- the matrix of the angles between the two eigenbases
  let C : Matrix {j : Fin d // r < (j : ℕ)} {i : Fin d // (i : ℕ) ≤ r} ℝ :=
    Matrix.of fun j i ↦ ⟪b j, b' i⟫
  let G : Matrix {j : Fin d // r < (j : ℕ)} {i : Fin d // (i : ℕ) ≤ r} ℝ :=
    Matrix.of fun j i ↦ ⟪b j, T' (b' i) - T (b' i)⟫
  have hG : ∀ j i, G j i = (lam' i - lam j) * C j i := fun j i ↦ by
    change ⟪b j, T' (b' i) - T (b' i)⟫ = (lam' i - lam j) * ⟪b j, b' i⟫
    rw [inner_sub_right, ← hT (b j) (b' i), hb, hb', inner_smul_right, inner_smul_left]
    simp only [conj_trivial]
    ring
  have hsep : δ * specNorm C ≤ specNorm G := by
    refine mul_specNorm_le_of_sylvester (μ := fun i : {i : Fin d // (i : ℕ) ≤ r} ↦ lam' i)
      (ν := fun j : {j : Fin d // r < (j : ℕ)} ↦ lam j)
      (t := lam ⟨d - 1, by omega⟩) (a := lam ⟨r + 1, hr⟩) hδ hgap
      (hanti (Fin.mk_le_mk.mpr (by omega))) (fun i ↦ hanti' (Fin.le_def.mpr i.2))
      (fun j ↦ ⟨hanti (Fin.le_def.mpr (by have := j.1.2; simp only; omega)),
        hanti (Fin.le_def.mpr j.2)⟩) hG
  have hGn : specNorm G ≤ ε := by
    refine specNorm_le_of hε0 fun ξ ↦ ?_
    have ho : Orthonormal ℝ fun i : {i : Fin d // (i : ℕ) ≤ r} ↦ b' i.1 :=
      b'.orthonormal.comp _ Subtype.val_injective
    set y : E := ∑ i, ξ i • b' i.1 with hy
    have hyn : ‖y‖ ^ 2 = ‖ξ‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hy, ho.inner_sum, EuclideanSpace.norm_sq_eq]
      simp [sq]
    have hGξ : ∀ j, toEuclideanLin G ξ j = ⟪b j.1, T' y - T y⟫ := fun j ↦ by
      rw [Matrix.toLpLin_apply, hy, map_sum, map_sum, ← Finset.sum_sub_distrib, inner_sum]
      simp only [mulVec, dotProduct, map_smul, ← smul_sub, inner_smul_right]
      exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    have hsq : ‖toEuclideanLin G ξ‖ ^ 2 ≤ (ε * ‖ξ‖) ^ 2 := by
      calc ‖toEuclideanLin G ξ‖ ^ 2 = ∑ j : {j : Fin d // r < (j : ℕ)}, ⟪b j, T' y - T y⟫ ^ 2 := by
            rw [EuclideanSpace.norm_sq_eq]
            exact Finset.sum_congr rfl fun j _ ↦ by rw [hGξ, Real.norm_eq_abs, sq_abs]
        _ ≤ ‖T' y - T y‖ ^ 2 := sum_subtype_sq_inner_le b _ _
        _ ≤ (ε * ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hε y) 2
        _ = (ε * ‖ξ‖) ^ 2 := by rw [mul_pow, mul_pow, hyn]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  set ξ : EuclideanSpace ℝ {i : Fin d // (i : ℕ) ≤ r} := toLp 2 fun i ↦ ⟪b' i.1, x⟫ with hξ
  have hxξ : ∑ i, ξ i • b' i.1 = x := by
    have h1 : ∑ i ∈ univ.filter (fun i : Fin d ↦ (i : ℕ) ≤ r), ⟪b' i, x⟫ • b' i =
        ∑ i, ⟪b' i, x⟫ • b' i :=
      Finset.sum_subset (Finset.filter_subset _ _) fun i _ hi ↦ by
        have hi' : i ∉ {i : Fin d | (i : ℕ) ≤ r} := by simpa using hi
        have h0 := b'.repr_eq_zero_of_mem_span_image hx hi'
        rw [b'.repr_apply_apply] at h0
        rw [h0, zero_smul]
    rw [b'.sum_repr' x,
      Finset.sum_subtype (p := fun i : Fin d ↦ (i : ℕ) ≤ r) (univ.filter _) (by simp)] at h1
    exact h1
  have hξn : ‖ξ‖ ≤ ‖x‖ := by
    have h : ‖ξ‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      refine le_trans (le_of_eq ?_) (sum_subtype_sq_inner_le b' (fun i ↦ (i : ℕ) ≤ r) x)
      rw [EuclideanSpace.norm_sq_eq]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [Real.norm_eq_abs, sq_abs]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  have hCξ : ∀ j, toEuclideanLin C ξ j = ⟪b j.1, x⟫ := fun j ↦ by
    rw [Matrix.toLpLin_apply]
    conv_rhs => rw [← hxξ]
    rw [inner_sum]
    simp only [mulVec, dotProduct, inner_smul_right]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  have hsum : ∑ j ∈ univ.filter (fun j : Fin d ↦ r < (j : ℕ)), ⟪b j, x⟫ ^ 2 =
      ‖toEuclideanLin C ξ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq,
      Finset.sum_subtype (p := fun j : Fin d ↦ r < (j : ℕ)) (univ.filter _) (by simp)]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hCξ, Real.norm_eq_abs, sq_abs]
  rw [hsum]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  have hCn : specNorm C ≤ ε / δ := by
    rw [le_div_iff₀ hδ, mul_comm]
    exact hsep.trans hGn
  calc ‖toEuclideanLin C ξ‖ ≤ specNorm C * ‖ξ‖ := norm_toEuclideanLin_le _ _
    _ ≤ ε / δ * ‖x‖ := mul_le_mul hCn hξn (norm_nonneg _) (by positivity)
    _ = ε * ‖x‖ / δ := by ring

/-! ### Examples -/

section Examples

/-- The `2 × 2` matrix `e₁ e₁ᵀ`. -/
local notation "A₂" => (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)

/-- A `2 × 2` matrix with first column `e₁` that is not a multiple of `e₁ e₁ᵀ`. -/
local notation "B₂" => (!![1, 1 / 2; 0, 1 / 4] : Matrix (Fin 2) (Fin 2) ℝ)

/-- `σ₁(e₁ e₁ᵀ) = 0`: the matrix has rank one. -/
private theorem singularValues_one_le_zero : (toEuclideanLin A₂).singularValues (0 + 1) ≤ 0 := by
  have hA : A₂ = !![(1 : ℝ); 0] * (!![(1 : ℝ); 0])ᵀ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  have hr : (A₂).rank ≤ 0 + 1 := by
    rw [hA]
    exact (rank_mul_le_left _ _).trans ((rank_le_width _).trans (by simp))
  have h := singularValues_le_specNorm_sub A₂ _ hr
  rw [sub_self] at h
  simpa [specNorm] using h

/-- `σ₀(B₂) ≥ 1`: `B₂ e₁ = e₁`. -/
private theorem one_le_singularValues_zero : (1 : ℝ) ≤ (toEuclideanLin B₂).singularValues 0 := by
  rw [← specNorm_eq_singularValues_zero]
  have hs : toEuclideanLin B₂ (EuclideanSpace.single 0 1) = EuclideanSpace.single 0 1 := by
    ext i
    fin_cases i <;> simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  have h := norm_toEuclideanLin_le B₂ (EuclideanSpace.single 0 1)
  rw [hs] at h
  simpa using h

/-- `wedin_frobenius`, `wedin_specNorm` and `norm_truncation_sub_le_of_gap` for the `2 × 2`
matrices `A = e₁ e₁ᵀ` and `B = [1, 1/2; 0, 1/4]` with `r = 0`: `σ₁(A) = 0` and `σ₀(B) ≥ 1`, so
the gap holds with `δ = 1`. -/
example :
    ‖(1 - topRightSingularVectors A₂ (0 + 1) * (topRightSingularVectors A₂ (0 + 1))ᵀ) *
        topRightSingularVectors B₂ (0 + 1)‖ ≤ √2 * ‖B₂ - A₂‖ / 1 ∧
    specNorm ((1 - topRightSingularVectors A₂ (0 + 1) * (topRightSingularVectors A₂ (0 + 1))ᵀ) *
        topRightSingularVectors B₂ (0 + 1)) ≤ specNorm (B₂ - A₂) / 1 ∧
    ‖truncation B₂ (0 + 1) - truncation A₂ (0 + 1)‖ ≤
      (1 + √2 * ((toEuclideanLin A₂).singularValues 0 +
        (toEuclideanLin A₂).singularValues (0 + 1)) / 1) * ‖B₂ - A₂‖ := by
  have hgap : (toEuclideanLin A₂).singularValues (0 + 1) + 1 ≤
      (toEuclideanLin B₂).singularValues 0 := by
    linarith [singularValues_one_le_zero, one_le_singularValues_zero]
  exact ⟨wedin_frobenius _ _ 0 one_pos hgap, wedin_specNorm _ _ 0 one_pos hgap,
    norm_truncation_sub_le_of_gap _ _ 0 one_pos hgap⟩

/-- `davisKahan` on `ℝ²` with `r = 0`: `T = diag(1, 0)` and `T' = T + (1/10) id` are symmetric,
`‖T' x - T x‖ = ‖x‖ / 10`, `λ₁(T) ≤ 0` and `λ₀(T') ≥ 11/10`, so the gap holds with `δ = 1`. The
top eigenvector of `T'` has a squared component of at most `1/100` in the bottom eigenspace
of `T`. -/
example :
    let T := toEuclideanLin A₂
    let T' := T + (1 / 10 : ℝ) • LinearMap.id
    ∃ (hT : T.IsSymmetric) (hT' : T'.IsSymmetric) (hn : finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2),
      ∑ j ∈ univ.filter (fun j : Fin 2 ↦ 0 < (j : ℕ)),
          ⟪hT.eigenvectorBasis hn j, hT'.eigenvectorBasis hn 0⟫ ^ 2 ≤
        (1 / 10 * ‖hT'.eigenvectorBasis hn 0‖ / 1) ^ 2 := by
  intro T T'
  have hT : T.IsSymmetric := by
    refine Matrix.isSymmetric_toEuclideanLin_iff.mpr ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hT' : T'.IsSymmetric := hT.add (LinearMap.IsSymmetric.id.smul (by simp))
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  refine ⟨hT, hT', hn, ?_⟩
  have hε : ∀ x, ‖T' x - T x‖ ≤ 1 / 10 * ‖x‖ := fun x => by
    have e : T' x - T x = (1 / 10 : ℝ) • x := by simp [T']
    rw [e, norm_smul]
    norm_num
  have hu : ∀ i : Fin 2, ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := fun i => by simp
  have e1 : T (EuclideanSpace.single 1 1) = 0 := by
    ext i
    fin_cases i <;> simp [T, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  have e0 : T' (EuclideanSpace.single 0 1) = (11 / 10 : ℝ) • EuclideanSpace.single 0 1 := by
    ext i
    fin_cases i <;> simp [T', T, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
    norm_num
  have hr : 0 + 1 < 2 := by norm_num
  have h1 := hT.le_re_inner_of_repr_eq_zero hn ⟨0 + 1, hr⟩ (x := EuclideanSpace.single 1 1)
    (fun i hi => by fin_cases i <;> simp at hi)
  have h0 := hT'.re_inner_le_of_repr_eq_zero hn ⟨0, by omega⟩ (x := EuclideanSpace.single 0 1)
    (fun i hi => by fin_cases i <;> simp at hi)
  rw [e1, inner_zero_left, hu, one_pow, mul_one, RCLike.re_to_real] at h1
  rw [e0, real_inner_smul_left, real_inner_self_eq_norm_sq, hu, one_pow, mul_one, mul_one,
    RCLike.re_to_real] at h0
  exact davisKahan hn hT hT' one_pos hε hr (by linarith)
    (Submodule.subset_span (Set.mem_image_of_mem _ (by simp)))

end Examples

end LeanDLRA.SinTheta
