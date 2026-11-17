import LeanDLRA.Classical.WeylSingular
import LeanDLRA.Classical.SVD
import LeanDLRA.Classical.BestApproximation
import LeanDLRA.LinearAlgebra.SVD.SinTheta

/-!
# Open problems OP-RA-21, OP-RA-45

OP-RA-21: golden-ratio quasi-optimality of a best rank-`r` approximation
(`LeanDLRA.norm_sub_le_goldenRatio_mul`) and the sharpness of the constant
(`LeanDLRA.exists_eq_goldenRatio_mul`). The results on OP-RA-45 (Wedin's and Davis–Kahan's
sin-Θ theorems, Lipschitz continuity of the truncated singular value decomposition under a
gap) are in `LeanDLRA/LinearAlgebra/SVD/SinTheta.lean`.
-/

open Matrix WithLp Module Finset
open scoped RealInnerProductSpace LeanDLRA.Frobenius

noncomputable section

namespace LeanDLRA

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Splitting the Frobenius norm along an orthogonal projector: `‖Z‖² = ‖Q Z‖² + ‖(1 - Q) Z‖²`. -/
private theorem sq_norm_eq_sq_norm_proj_add [DecidableEq m] {Q : Matrix m m ℝ}
    (hQ : Curvature.IsOrthProjMat Q) (Z : Matrix m n ℝ) :
    ‖Z‖ ^ 2 = ‖Q * Z‖ ^ 2 + ‖(1 - Q) * Z‖ ^ 2 := by
  have h1 : (Q * Z)ᵀ * (Q * Z) = Zᵀ * (Q * Z) := by
    rw [transpose_mul, hQ.symm, Matrix.mul_assoc, ← Matrix.mul_assoc Q Q, hQ.idem]
  have h2 : ((1 - Q) * Z)ᵀ * ((1 - Q) * Z) = Zᵀ * ((1 - Q) * Z) := by
    rw [transpose_mul, hQ.compl.symm, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - Q) (1 - Q),
      hQ.compl.idem]
  rw [Curvature.frob_sq_eq_trace, Curvature.frob_sq_eq_trace, Curvature.frob_sq_eq_trace, h1, h2,
    ← trace_add, ← Matrix.mul_add, ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]

/-- **Golden-ratio quasi-optimality of best rank-`r` approximation** (source: OP-RA-21, sharp
constant; numerically supported, adversarial search approaches `φ` from below).  If `T` is a best
rank-`≤ r` approximation of `X` and `rank A ≤ r`, then `‖T - A‖_F ≤ φ ‖X - A‖_F` with
`φ = (1 + √5)/2`.  This is a conjecture: a Nelder–Mead search over sizes up to `5 × 4`,
`r ∈ {1, 2}` (review, 2026-11) found no ratio above `φ`. -/
theorem norm_sub_le_goldenRatio_mul {r : ℕ} {X A T : Matrix m n ℝ}
    (hT : ‖X - T‖ ≤ Metric.infDist X {Z : Matrix m n ℝ | Z.rank ≤ r}) (hTr : T.rank ≤ r)
    (hA : A.rank ≤ r) :
    ‖T - A‖ ≤ Real.goldenRatio * ‖X - A‖ := by
  classical
  obtain ⟨U, S, V, hU, -, -, hTeq⟩ := (SVD.rank_eq_iff_exists_factor (r := T.rank) T).1 rfl
  set Q : Matrix m m ℝ := U * Uᵀ with hQdef
  have hQ : Curvature.IsOrthProjMat Q := Curvature.isOrthProjMat_mul_transpose hU
  have hQT : Q * T = T := by
    have h : Q * (U * S * Vᵀ) = U * S * Vᵀ := by
      rw [hQdef, Matrix.mul_assoc U Uᵀ, ← Matrix.mul_assoc Uᵀ, ← Matrix.mul_assoc Uᵀ, hU,
        Matrix.one_mul, Matrix.mul_assoc U S]
    rwa [← hTeq] at h
  have hinf : ∀ Z : Matrix m n ℝ, Z.rank ≤ r → ‖X - T‖ ≤ ‖X - Z‖ := fun Z hZ ↦ by
    refine hT.trans ?_
    rw [← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem hZ
  -- the first-order condition `Q X = T`
  have hQX : Q * X = T := by
    have hrank : (Q * X).rank ≤ r := by
      refine le_trans ?_ hTr
      rw [hQdef, Matrix.mul_assoc]
      refine (rank_mul_le_left _ _).trans ((rank_le_card_width _).trans ?_)
      simp
    have h1 := sq_norm_eq_sq_norm_proj_add hQ (X - T)
    have e1 : Q * (X - T) = Q * X - T := by rw [Matrix.mul_sub, hQT]
    have e2 : (1 - Q) * (X - T) = X - Q * X := by
      rw [Matrix.sub_mul, Matrix.one_mul, e1]; abel
    rw [e1, e2] at h1
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (hinf _ hrank) 2
    have h3 : ‖Q * X - T‖ ^ 2 ≤ 0 := by linarith
    have h4 : ‖Q * X - T‖ = 0 := by
      nlinarith [norm_nonneg (Q * X - T)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h4)
  set E : Matrix m n ℝ := X - T with hE
  have hQE : Q * E = 0 := by rw [hE, Matrix.mul_sub, hQX, hQT, sub_self]
  set φ : ℝ := Real.goldenRatio with hφ
  have hφ0 : 0 < φ := Real.goldenRatio_pos
  have hφ1 : 1 < φ := Real.one_lt_goldenRatio
  have hφ2 : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
  set M : Matrix m m ℝ := Q + φ⁻¹ • (1 - Q) with hM
  have hc0 : 0 ≤ φ⁻¹ := (inv_pos.mpr hφ0).le
  have hc1 : φ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hφ1.le
  have hQc : Q * (1 - Q) = 0 := by rw [Matrix.mul_sub, hQ.idem]; simp
  have hcQ : (1 - Q) * Q = 0 := by rw [Matrix.sub_mul, hQ.idem]; simp
  have hMQ : Q * M = Q := by
    rw [hM, Matrix.mul_add, hQ.idem, Matrix.mul_smul, hQc, smul_zero, add_zero]
  have hMc : (1 - Q) * M = φ⁻¹ • (1 - Q) := by
    rw [hM, Matrix.mul_add, hcQ, Matrix.mul_smul, hQ.compl.idem, zero_add]
  -- `M` is a contraction
  have hcontr : ∀ Z : Matrix m n ℝ, ‖M * Z‖ ≤ ‖Z‖ := fun Z ↦ by
    have h1 := sq_norm_eq_sq_norm_proj_add hQ (M * Z)
    have h2 := sq_norm_eq_sq_norm_proj_add hQ Z
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMQ, hMc, Matrix.smul_mul, norm_smul, mul_pow,
      Real.norm_of_nonneg hc0] at h1
    have h3 : (φ⁻¹) ^ 2 ≤ 1 := pow_le_one₀ hc0 hc1
    have h4 := sq_nonneg ‖(1 - Q) * Z‖
    have h5 : ‖M * Z‖ ^ 2 ≤ ‖Z‖ ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h5
  have hY : M * (T + φ • E) = X := by
    have h1 : (1 - Q) * T = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hQT, sub_self]
    have h2 : (1 - Q) * E = E := by rw [Matrix.sub_mul, Matrix.one_mul, hQE, sub_zero]
    rw [hM, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_add, hQT, Matrix.mul_smul,
      Matrix.mul_smul, hQE, h1, h2, smul_zero, add_zero, zero_add, smul_smul,
      inv_mul_cancel₀ hφ0.ne', one_smul, hE]
    abel
  have hkey : ‖E‖ ≤ ‖(T + φ • E) - A‖ := by
    have hrank : (M * A).rank ≤ r := (rank_mul_le_right _ _).trans hA
    refine (hinf _ hrank).trans ?_
    have : X - M * A = M * ((T + φ • E) - A) := by
      rw [Matrix.mul_sub, hY]
    rw [this]
    exact hcontr _
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hkey 2
  have e1 : (T + φ • E) - A = (T - A) + φ • E := by abel
  have e2 : X - A = (T - A) + E := by rw [hE]; abel
  rw [e1, norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow,
    Real.norm_of_nonneg hφ0.le] at hsq
  have hgoal : ‖T - A‖ ^ 2 ≤ (φ * ‖X - A‖) ^ 2 := by
    rw [e2, mul_pow, norm_add_sq_real]
    have hE0 := sq_nonneg ‖E‖
    set d := ‖T - A‖ ^ 2
    set c := ⟪T - A, E⟫
    set e := ‖E‖ ^ 2
    have h3 : φ ^ 3 = 2 * φ + 1 := by
      calc φ ^ 3 = φ * φ ^ 2 := by ring
        _ = 2 * φ + 1 := by rw [hφ2]; nlinarith
    -- `φ² ‖D + E‖² - ‖D‖² = φ (‖D + φ E‖² - ‖E‖²)`
    have hid : φ ^ 2 * (d + 2 * c + e) - d = φ * (d + 2 * (φ * c) + φ ^ 2 * e - e) := by
      have : φ * (d + 2 * (φ * c) + φ ^ 2 * e - e) =
          φ * d + 2 * φ ^ 2 * c + φ ^ 3 * e - φ * e := by ring
      rw [this, h3, hφ2]; ring
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hgoal

/-- **Sharpness of the golden ratio** (source: OP-RA-21, lower-bound example `X = I₂`,
`A = diag(0, φ)`, `T = diag(1, 0)`).  The constant of `norm_sub_le_goldenRatio_mul` is attained. -/
theorem exists_eq_goldenRatio_mul :
    ∃ X A T : Matrix (Fin 2) (Fin 2) ℝ,
      ‖X - T‖ ≤ Metric.infDist X {Z : Matrix (Fin 2) (Fin 2) ℝ | Z.rank ≤ 1} ∧ T.rank ≤ 1 ∧
      A.rank ≤ 1 ∧ X ≠ A ∧ ‖T - A‖ = Real.goldenRatio * ‖X - A‖ := by
  have hφ0 : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hφ2 : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  refine ⟨1, vecMulVec ![0, Real.goldenRatio] ![0, 1], vecMulVec ![1, 0] ![1, 0], ?_,
    rank_vecMulVec_le _ _, rank_vecMulVec_le _ _, ?_, ?_⟩
  · have h1 : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ) - vecMulVec ![1, 0] ![1, 0]‖ ≤ 1 := by
      have : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ) - vecMulVec ![1, 0] ![1, 0]‖ ^ 2 = 1 := by
        rw [Frobenius.norm_sq_eq_sum]
        simp [Fin.sum_univ_two, Matrix.one_apply]
      nlinarith [norm_nonneg ((1 : Matrix (Fin 2) (Fin 2) ℝ) - vecMulVec ![1, 0] ![1, 0])]
    refine h1.trans ((Metric.le_infDist ⟨0, by simp⟩).2 fun y hy ↦ ?_)
    have hdet : y.det = 0 := by
      by_contra hne
      have hu : IsUnit y := (isUnit_iff_isUnit_det y).mpr (isUnit_iff_ne_zero.mpr hne)
      have h2 : y.rank = 2 := by rw [rank_of_isUnit y hu, Fintype.card_fin]
      have h3 : y.rank ≤ 1 := hy
      omega
    rw [det_fin_two] at hdet
    rw [dist_eq_norm]
    have h2 : 1 ≤ ‖(1 : Matrix (Fin 2) (Fin 2) ℝ) - y‖ ^ 2 := by
      rw [Frobenius.norm_sq_eq_sum]
      simp only [Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply_eq]
      rw [Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
        Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
      nlinarith [sq_nonneg (y 0 1 + y 1 0), sq_nonneg (y 0 1 - y 1 0),
        sq_nonneg (1 - (y 0 0 + y 1 1))]
    nlinarith [norm_nonneg ((1 : Matrix (Fin 2) (Fin 2) ℝ) - y)]
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [vecMulVec_apply] at this
  · have h1 : ‖vecMulVec ![1, 0] ![1, 0] - vecMulVec ![0, Real.goldenRatio] ![0, 1]‖ ^ 2 =
        1 + Real.goldenRatio ^ 2 := by
      rw [Frobenius.norm_sq_eq_sum]
      simp [Fin.sum_univ_two]
    have h2 : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ) - vecMulVec ![0, Real.goldenRatio] ![0, 1]‖ ^ 2 =
        1 + (1 - Real.goldenRatio) ^ 2 := by
      rw [Frobenius.norm_sq_eq_sum]
      simp [Fin.sum_univ_two, Matrix.one_apply]
    refine (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
    rw [mul_pow, h1, h2, hφ2]
    have h3 : (1 - Real.goldenRatio) ^ 2 = 2 - Real.goldenRatio := by nlinarith
    rw [h3]
    nlinarith

variable [DecidableEq m] [DecidableEq n]

end LeanDLRA

end
