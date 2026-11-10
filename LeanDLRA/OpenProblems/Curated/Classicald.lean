import LeanDLRA.Classical.WeylSingular
import LeanDLRA.Classical.SVD
import LeanDLRA.Classical.BestApproximation

/-!
# Truncating a tangent step: the distance to rank `r` is of second order

Let `X = U S Vᵀ` with orthonormal `U`, `V` and smallest singular value of `S` at least `ρ > 0`,
and let `Z` be a tangent matrix at `X`, `(1 - U Uᵀ) Z (1 - V Vᵀ) = 0`. An explicit step `X + Z`
leaves the matrices of rank at most `r`, but only by a term of second order in `Z`. The distance
is measured by `WeylSingular.tailNorm (X + Z) r`, the Frobenius norm of the singular values of
`X + Z` beyond the first `r`; it is the Frobenius distance to the matrices of rank at most `r`
(`WeylSingular.tailNorm_eq_infDist`).

## Main results

* `tailNorm_add_tangent_le`: if `‖Z‖ ≤ ρ / 2` (Frobenius norm), then
  `tailNorm (U S Vᵀ + Z) r ≤ ‖Z‖² / ρ`.

## References

* arXiv 2111.14540, Sec. 6 and 7 (retraction of a tangent step by the truncated SVD).
-/

open Matrix WithLp Module Finset
open scoped RealInnerProductSpace LeanDLRA.Frobenius

noncomputable section

namespace LeanDLRA.SVD

variable {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
  [DecidableEq m] [DecidableEq n] [DecidableEq m'] [DecidableEq n']

end LeanDLRA.SVD

namespace LeanDLRA.EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

end LeanDLRA.EckartYoung

namespace LeanDLRA.Mirsky

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

end LeanDLRA.Mirsky

namespace LeanDLRA.WeylSingular

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]

end LeanDLRA.WeylSingular

namespace LeanDLRA.SinTheta

open EckartYoung Curvature

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

end LeanDLRA.SinTheta

namespace LeanDLRA

variable {m n : Type*} [Fintype m] [Fintype n]

variable [DecidableEq m] [DecidableEq n]

/-- Block decomposition of a tangent matrix `Z` in the bases `[U, U⊥]`, `[V, V⊥]`, with its
Pythagorean identity for the Frobenius norm. -/
private theorem tangent_block_decomp {r : ℕ} {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {Z : Matrix m n ℝ}
    (hZ : (1 - U * Uᵀ) * Z * (1 - V * Vᵀ) = 0) :
    Z = U * (Uᵀ * Z * V) * Vᵀ + U * (Uᵀ * Z * (1 - V * Vᵀ)) + (1 - U * Uᵀ) * Z * V * Vᵀ ∧
      ‖Uᵀ * Z * V‖ ^ 2 + ‖Uᵀ * Z * (1 - V * Vᵀ)‖ ^ 2 + ‖(1 - U * Uᵀ) * Z * V‖ ^ 2 = ‖Z‖ ^ 2 := by
  have hdecomp :
      Z = U * (Uᵀ * Z * V) * Vᵀ + U * (Uᵀ * Z * (1 - V * Vᵀ)) + (1 - U * Uᵀ) * Z * V * Vᵀ := by
    have h : Z - U * (Uᵀ * Z) - Z * (V * Vᵀ) + U * (Uᵀ * (Z * (V * Vᵀ))) = 0 := by
      rw [← hZ]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
      abel
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [← sub_eq_zero, ← h]
    abel
  refine ⟨hdecomp, ?_⟩
  generalize hM : Uᵀ * Z * V = M at hdecomp ⊢
  generalize hB : Uᵀ * Z * (1 - V * Vᵀ) = B at hdecomp ⊢
  have hBV : B * V = 0 := by
    rw [← hB, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc V, hV,
      Matrix.mul_one, sub_self, Matrix.mul_zero]
  have hUC : Uᵀ * ((1 - U * Uᵀ) * Z * V) = 0 := by
    rw [Matrix.mul_assoc (1 - U * Uᵀ), ← Matrix.mul_assoc Uᵀ, Matrix.mul_sub, Matrix.mul_one,
      ← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul, sub_self, Matrix.zero_mul]
  generalize (1 - U * Uᵀ) * Z * V = C at hdecomp hUC ⊢
  have h1 : ⟪U * M * Vᵀ, U * B⟫ = 0 := by
    rw [Matrix.mul_assoc, Frobenius.inner_mul_mul_of_orthonormal hU, Frobenius.inner_mul_right,
      Matrix.transpose_transpose, hBV, inner_zero_right]
  have h2 : ⟪U * M * Vᵀ + U * B, C * Vᵀ⟫ = 0 := by
    rw [Matrix.mul_assoc U M, ← Matrix.mul_add, Frobenius.inner_mul_left, ← Matrix.mul_assoc Uᵀ,
      hUC, Matrix.zero_mul, inner_zero_right]
  have hnM : ‖U * M * Vᵀ‖ = ‖M‖ := by
    rw [Frobenius.norm_mul_transpose_of_orthonormal hV, Frobenius.norm_mul_of_orthonormal hU]
  have hnB : ‖U * B‖ = ‖B‖ := Frobenius.norm_mul_of_orthonormal hU B
  have hnC : ‖C * Vᵀ‖ = ‖C‖ := Frobenius.norm_mul_transpose_of_orthonormal hV C
  have h3 := norm_add_sq_real (U * M * Vᵀ + U * B) (C * Vᵀ)
  have h4 := norm_add_sq_real (U * M * Vᵀ) (U * B)
  rw [h2, ← hdecomp, hnC] at h3
  rw [h1, hnM, hnB] at h4
  rw [h3, h4]
  ring

/-- **Second-order accuracy of the SVD retraction of a tangent step** (source: OP-RA-30,
arXiv 2111.14540 Sec. 6–7).  Let `X = U S Vᵀ` with orthonormal `U, V` and `σ_min(S) ≥ ρ > 0`,
and let `Z` be tangent at `X` (`(1 - U Uᵀ) Z (1 - V Vᵀ) = 0`) with `‖Z‖_F ≤ ρ/2`.  Then
`dist_F(X + Z, M_{≤ r}) = τ_r(X + Z) ≤ ‖Z‖_F² / ρ`, so truncating an explicit tangent step back
to rank `r` costs `O(‖Z‖² / ρ)`. -/
theorem tailNorm_add_tangent_le {r : ℕ} {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
    {S : Matrix (Fin r) (Fin r) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {ρ : ℝ} (hρ : 0 < ρ)
    (hS : ρ ≤ (toEuclideanLin S).singularValues (r - 1)) {Z : Matrix m n ℝ}
    (hZ : (1 - U * Uᵀ) * Z * (1 - V * Vᵀ) = 0) (hZρ : ‖Z‖ ≤ ρ / 2) :
    WeylSingular.tailNorm (U * S * Vᵀ + Z) r ≤ ‖Z‖ ^ 2 / ρ := by
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · have h0 : (toEuclideanLin S).singularValues (0 - 1) = 0 :=
        LinearMap.singularValues_of_finrank_le _ (by simp)
      linarith
    · exact hr
  have hSlow := (SVD.forall_mul_norm_le_iff_fin hr S).2 hS
  obtain ⟨hdecomp, hpyth⟩ := tangent_block_decomp hU hV hZ
  generalize Uᵀ * Z * V = M at hdecomp hpyth
  generalize Uᵀ * Z * (1 - V * Vᵀ) = B at hdecomp hpyth
  generalize (1 - U * Uᵀ) * Z * V = C at hdecomp hpyth
  have hMle : ‖M‖ ≤ ρ / 2 := by
    refine le_trans ?_ hZρ
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    nlinarith [sq_nonneg ‖B‖, sq_nonneg ‖C‖]
  have hAlow : ∀ w, ρ / 2 * ‖w‖ ≤ ‖toEuclideanLin (S + M) w‖ := by
    intro w
    have h1 := hSlow w
    have h2 : ‖toEuclideanLin M w‖ ≤ ρ / 2 * ‖w‖ :=
      (Curvature.norm_toEuclideanLin_le M w).trans (mul_le_mul_of_nonneg_right
        ((Curvature.specNorm_le_frob M).trans hMle) (norm_nonneg _))
    have h3 : toEuclideanLin (S + M) w = toEuclideanLin S w + toEuclideanLin M w := by
      simp
    have h4 : ‖toEuclideanLin S w‖ ≤ ‖toEuclideanLin (S + M) w‖ + ‖toEuclideanLin M w‖ := by
      rw [h3]
      simpa using norm_sub_le (toEuclideanLin S w + toEuclideanLin M w) (toEuclideanLin M w)
    linarith
  have hinj : Function.Injective (S + M).mulVec := by
    intro v w h
    have h0 := hAlow (WithLp.toLp 2 (v - w))
    have h1 : toEuclideanLin (S + M) (WithLp.toLp 2 (v - w)) = 0 := by
      rw [Matrix.toLpLin_toLp, Matrix.toLin'_apply, Matrix.mulVec_sub, h, sub_self]
      rfl
    rw [h1, norm_zero] at h0
    have h2 : ‖(WithLp.toLp 2 (v - w) : EuclideanSpace ℝ (Fin r))‖ = 0 := by
      have := norm_nonneg (WithLp.toLp 2 (v - w) : EuclideanSpace ℝ (Fin r))
      nlinarith
    have h3 : (WithLp.toLp 2 (v - w) : EuclideanSpace ℝ (Fin r)) = 0 := norm_eq_zero.1 h2
    have h4 : v - w = 0 := by simpa using congrArg WithLp.ofLp h3
    exact sub_eq_zero.1 h4
  have hdet : IsUnit (S + M).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_injective_iff_isUnit.1 hinj)
  have hAinvL := Matrix.nonsing_inv_mul _ hdet
  have hAinvR := Matrix.mul_nonsing_inv _ hdet
  have hspec : Curvature.specNorm (S + M)⁻¹ ≤ 2 / ρ := by
    refine Curvature.specNorm_le_of (by positivity) fun x => ?_
    have hx : toEuclideanLin (S + M) (toEuclideanLin (S + M)⁻¹ x) = x := by
      rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, hAinvR, Matrix.toLpLin_one,
        LinearMap.id_apply]
    have h := hAlow (toEuclideanLin (S + M)⁻¹ x)
    rw [hx] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ hρ]
    linarith
  generalize hAdef : S + M = A at hAlow hdet hAinvL hAinvR hspec
  have hrank : ((U * A + C) * (A⁻¹ * (A * Vᵀ + B))).rank ≤ r :=
    (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width (U * A + C))
  have hdiff : U * S * Vᵀ + Z - (U * A + C) * (A⁻¹ * (A * Vᵀ + B)) = -(C * (A⁻¹ * B)) := by
    have h1 : A⁻¹ * (A * Vᵀ + B) = Vᵀ + A⁻¹ * B := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc, hAinvL, Matrix.one_mul]
    have h2 : U * A * (A⁻¹ * B) = U * B := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, hAinvR, Matrix.one_mul]
    have h3 : U * S * Vᵀ + Z = U * A * Vᵀ + U * B + C * Vᵀ := by
      rw [hdecomp, ← hAdef]
      simp only [Matrix.mul_add, Matrix.add_mul]
      abel
    rw [h3, h1]
    simp only [Matrix.mul_add, Matrix.add_mul, h2]
    abel
  calc WeylSingular.tailNorm (U * S * Vᵀ + Z) r
      ≤ ‖U * S * Vᵀ + Z - (U * A + C) * (A⁻¹ * (A * Vᵀ + B))‖ :=
        WeylSingular.tailNorm_le_norm_sub _ _ hrank
    _ = ‖C * (A⁻¹ * B)‖ := by rw [hdiff, norm_neg]
    _ ≤ ‖C‖ * ‖A⁻¹ * B‖ := Frobenius.norm_mul_le _ _
    _ ≤ ‖C‖ * (2 / ρ * ‖B‖) := by
        gcongr
        exact (Curvature.frob_mul_le _ _).trans (by gcongr)
    _ ≤ ‖Z‖ ^ 2 / ρ := by
        rw [le_div_iff₀ hρ]
        have h : ‖C‖ * (2 / ρ * ‖B‖) * ρ = 2 * ‖C‖ * ‖B‖ := by
          field_simp
        rw [h]
        nlinarith [sq_nonneg (‖C‖ - ‖B‖), sq_nonneg ‖M‖]

end LeanDLRA

end
