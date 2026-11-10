import LeanDLRA.Literature.Foundations.P2309_06125a
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors

/-!
# The Weingarten term of accelerated forward Euler for ambient-linear fields (OP-HO-38)

Open problem OP-HO-38 of `docs/survey/open-problems.json`: in the experiments
of arXiv 2309.06125, §5.2, Fig. 4(a), the error curves of the accelerated forward Euler scheme
(AFE) for different ranks coincide until the modelling plateau, although the acceleration (39)
contains the Weingarten term `W_Y(Π F, Π⊥ F)`, bounded only by `2 ‖T‖ ‖N‖ / σ_r`
(`LeanDLRA.Literature.P2309_06125.norm_weingarten_le`).

This file isolates the mechanism on actual matrices.  Everything is stated for a factorization
`X = U S Vᵀ` (`IsFactorization`, orthonormal `U`, `V`, invertible `S`), `T = Π(X) F`,
`N = F - Π(X) F`, with `G = V S⁻¹ Uᵀ` the pseudo-inverse of `X` and `‖·‖` the Frobenius norm.

* `weingarten_eq_ginv`: `W_X(T, N) = N Fᵀ Gᵀ + Gᵀ Fᵀ N`.
* `norm_weingarten_le_one`, `norm_curvature_term_le_one`: the sharp general bound is
  `‖W_X(T, N)‖ ≤ ‖T‖ ‖N‖ / σ_r`, constant `1` instead of the `2` of the paper, for every `T` and
  every `N` with `Uᵀ N = 0`; `weingarten_two_by_two` shows that it is attained
  (`‖W‖ = ‖T‖ ‖N‖ / σ` on a `2 × 2` example with `‖N‖ = ε`, `‖W‖ = √2 ε / σ`).
* Ambient-linear fields `F = L A + A R`, which is the form of the vector field (51) of the test
  of §5.2 (`field51_eq`, with `L = Ω_U + U D Uᵀ`, `R = Ω_Vᵀ`, `‖L‖₂ ≤ ‖Ω_U‖₂ + ‖D‖₂`): with
  `E = A - X` the error of the current approximation,
  - `normal_linear_eq`, `norm_normal_linear_le`: `N = (1 - U Uᵀ)(L E + E R)(1 - V Vᵀ)`, so
    `‖N‖ ≤ (‖L‖₂ + ‖R‖₂) ‖E‖`;
  - `weingarten_linear_eq`:
    `W = N (Rᵀ V Vᵀ + (G L E)ᵀ + (G E R)ᵀ) + (U Uᵀ Lᵀ + (L E G)ᵀ + (E R G)ᵀ) N`;
  - `norm_weingarten_linear_le`:
    `‖W‖ ≤ ‖N‖ (‖L‖₂ + ‖R‖₂ + ‖G L E‖₂ + ‖G E R‖₂ + ‖L E G‖₂ + ‖E R G‖₂)`;
  - `norm_weingarten_linear_le_sigma`: `‖W‖ ≤ (‖L‖₂ + ‖R‖₂)² ‖E‖ (1 + 2 ‖E‖ / σ_r)`.
  The pseudo-inverse `G` never meets `A` itself (`G X = V Vᵀ`, `X G = U Uᵀ`), so `σ_r` enters
  only through the *relative* errors `X⁺ L E`, `X⁺ E R`, `L E X⁺`, `E R X⁺`; the curvature term
  is of the size of the modelling error `‖N‖` whenever these are bounded, for instance when
  `‖A - X‖ ≤ c σ_r(X)` (the best rank-`r` approximation of a matrix with `σ_{r+1} ≤ c σ_r`).
* `weingarten_relative_counterexample`: the relative-error factor cannot be removed.  On `3 × 3`
  matrices with `X = diag(1, s, 0)`, `r = 2`, an orthogonal projector `L` (so `‖L‖₂ ≤ 1`), `R = 0`
  and `A = X + δ (e₂ e₃ᵀ + e₃ e₃ᵀ)`, one has `‖N‖ = δ`, `‖X⁺ L E‖ = δ / s` and `‖W‖ = δ² / s`:
  the curvature term exceeds the modelling error by the factor `δ / s`, which is unbounded for
  `s → 0` at fixed small `δ`.  Absolute closeness of `X` to `A` is not enough.

## What stays open

In the experiment of §5.2 the numerical AFE iterates keep the relative errors `‖G E‖₂`, `‖E G‖₂`
of order one while `‖E‖ / σ_r` grows to `10²` (a throwaway computation, not formalized), which is
what the bound above needs; that the AFE recursion preserves bounded relative errors is a statement
about the dynamics and is not proved here.  Nothing is proved about the global error of the scheme.
-/

open Set Finset
open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA.Novel.OpHO38

open LeanDLRA LeanDLRA.Curvature LeanDLRA.Literature.P2309_06125

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

section General

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {X : Matrix m n ℝ} {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
  {S : Matrix (Fin r) (Fin r) ℝ}

/-- The normal part `F - Π(X) F = (1 - U Uᵀ) F (1 - V Vᵀ)`. -/
lemma normal_eq (h : IsFactorization X U S V) (F : Matrix m n ℝ) :
    F - tangentProjAt X F = (1 - U * Uᵀ) * F * (1 - V * Vᵀ) := by
  rw [h.tanProj_apply]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

lemma rowCompl_idem (hV : Vᵀ * V = 1) : (1 - V * Vᵀ) * (1 - V * Vᵀ) = 1 - V * Vᵀ :=
  (isOrthProjMat_mul_transpose hV).compl.idem

lemma colCompl_idem (hU : Uᵀ * U = 1) : (1 - U * Uᵀ) * (1 - U * Uᵀ) = 1 - U * Uᵀ :=
  (isOrthProjMat_mul_transpose hU).compl.idem

omit [DecidableEq m] in
/-- The normal part is fixed by `1 - V Vᵀ` from the right. -/
lemma normal_mul_rowCompl (h : IsFactorization X U S V) (F : Matrix m n ℝ) :
    (F - tangentProjAt X F) * (1 - V * Vᵀ) = F - tangentProjAt X F := by
  classical
  rw [normal_eq h F, Matrix.mul_assoc, rowCompl_idem h.orthV]

omit [DecidableEq n] in
/-- The normal part is fixed by `1 - U Uᵀ` from the left. -/
lemma colCompl_mul_normal (h : IsFactorization X U S V) (F : Matrix m n ℝ) :
    (1 - U * Uᵀ) * (F - tangentProjAt X F) = F - tangentProjAt X F := by
  classical
  rw [normal_eq h F, ← Matrix.mul_assoc, ← Matrix.mul_assoc, colCompl_idem h.orthU]

/-- **The Weingarten term of Prop. 6 in pseudo-inverse form.**  For `X = U S Vᵀ`, `T = Π(X) F`,
`N = F - Π(X) F` and `G = V S⁻¹ Uᵀ` the pseudo-inverse of `X`,
`W_X(T, N) = N Fᵀ Gᵀ + Gᵀ Fᵀ N`.
This is eq. (34) of arXiv 2309.06125 with `U_p = (1 - U Uᵀ) F V`, `V_p = (1 - V Vᵀ) Fᵀ U`
written without the tangent representation; it is the form in which the structure of `F` can be
used. -/
theorem weingarten_eq_ginv (h : IsFactorization X U S V) (F : Matrix m n ℝ) :
    weingarten U S V (tangentProjAt X F) (F - tangentProjAt X F) =
      (F - tangentProjAt X F) * Fᵀ * (U * (S⁻¹)ᵀ * Vᵀ) +
        (U * (S⁻¹)ᵀ * Vᵀ) * Fᵀ * (F - tangentProjAt X F) := by
  set T := tangentProjAt X F with hT
  set N := F - tangentProjAt X F with hN
  have hTU : Tᵀ * U = Fᵀ * U := h.tanProj_transpose_mul_U F
  have hTV : T * V = F * V := h.tanProj_mul_V F
  have hN1 : N * (1 - V * Vᵀ) = N := normal_mul_rowCompl h F
  have hN2 : (1 - U * Uᵀ) * N = N := colCompl_mul_normal h F
  have e1 : N * ((1 - V * Vᵀ) * Tᵀ * U) = N * Fᵀ * U := by
    rw [Matrix.mul_assoc (1 - V * Vᵀ), ← Matrix.mul_assoc N, hN1, hTU, Matrix.mul_assoc]
  have e2 : ((1 - U * Uᵀ) * T * V)ᵀ * N = Vᵀ * Fᵀ * N := by
    have hc : (1 - U * Uᵀ)ᵀ = 1 - U * Uᵀ := (isOrthProjMat_mul_transpose h.orthU).compl.symm
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hc, Matrix.mul_assoc, Matrix.mul_assoc, hN2,
      ← Matrix.mul_assoc, ← Matrix.transpose_mul, hTV, Matrix.transpose_mul]
  unfold weingarten
  rw [e1, Matrix.mul_assoc (U * (S⁻¹)ᵀ), e2]
  simp only [Matrix.mul_assoc]

/-- `‖U_p‖² + ‖V_p‖² ≤ ‖T‖²` for `U_p = (1 - U Uᵀ) T V`, `V_p = (1 - V Vᵀ) Tᵀ U`: the two
off-diagonal blocks of `T` in the splitting by `U Uᵀ` and `V Vᵀ`. -/
lemma sq_Up_add_sq_Vp_le (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (T : Matrix m n ℝ) :
    ‖(1 - U * Uᵀ) * T * V‖ ^ 2 + ‖(1 - V * Vᵀ) * Tᵀ * U‖ ^ 2 ≤ ‖T‖ ^ 2 := by
  have hP : IsOrthProjMat (U * Uᵀ) := isOrthProjMat_mul_transpose hU
  have hQ : IsOrthProjMat (V * Vᵀ) := isOrthProjMat_mul_transpose hV
  have keyV : ∀ Z : Matrix m n ℝ, ‖Z * V‖ ≤ ‖Z * (V * Vᵀ)‖ := fun Z => by
    calc ‖Z * V‖ = ‖Z * (V * Vᵀ) * V‖ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hV, Matrix.mul_one]
      _ ≤ ‖Z * (V * Vᵀ)‖ * specNorm V := frob_mul_le' _ _
      _ ≤ ‖Z * (V * Vᵀ)‖ * 1 := by gcongr; exact specNorm_le_one_of_orthonormal hV
      _ = ‖Z * (V * Vᵀ)‖ := mul_one _
  have keyU : ∀ Z : Matrix n m ℝ, ‖Z * U‖ ≤ ‖Z * (U * Uᵀ)‖ := fun Z => by
    calc ‖Z * U‖ = ‖Z * (U * Uᵀ) * U‖ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hU, Matrix.mul_one]
      _ ≤ ‖Z * (U * Uᵀ)‖ * specNorm U := frob_mul_le' _ _
      _ ≤ ‖Z * (U * Uᵀ)‖ * 1 := by gcongr; exact specNorm_le_one_of_orthonormal hU
      _ = ‖Z * (U * Uᵀ)‖ := mul_one _
  -- `‖T‖² = ‖T Q‖² + ‖T (1 - Q)‖²` through the transpose
  have hsplit : ‖T‖ ^ 2 = ‖T * (V * Vᵀ)‖ ^ 2 + ‖T * (1 - V * Vᵀ)‖ ^ 2 := by
    have e : Tᵀ = (V * Vᵀ) * Tᵀ + (1 - V * Vᵀ) * Tᵀ := by
      rw [← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
    have horth : ((V * Vᵀ) * Tᵀ)ᵀ * ((1 - V * Vᵀ) * Tᵀ) = 0 := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, hQ.symm, Matrix.mul_assoc,
        ← Matrix.mul_assoc (V * Vᵀ), Matrix.mul_sub, Matrix.mul_one, hQ.idem, sub_self,
        Matrix.zero_mul, Matrix.mul_zero]
    have := frob_sq_add_of_orth horth
    rw [← e, Frobenius.norm_transpose] at this
    have e1 : (T * (V * Vᵀ))ᵀ = V * Vᵀ * Tᵀ := by rw [Matrix.transpose_mul, hQ.symm]
    have e2 : (T * (1 - V * Vᵀ))ᵀ = (1 - V * Vᵀ) * Tᵀ := by
      rw [Matrix.transpose_mul, hQ.compl.symm]
    rw [this, ← Frobenius.norm_transpose (T * (V * Vᵀ)), ← Frobenius.norm_transpose
      (T * (1 - V * Vᵀ)), e1, e2]
  -- `‖(1 - P) T Q‖² ≤ ‖T Q‖²`
  have h1 : ‖(1 - U * Uᵀ) * (T * (V * Vᵀ))‖ ^ 2 ≤ ‖T * (V * Vᵀ)‖ ^ 2 := by
    have e : T * (V * Vᵀ) = (1 - U * Uᵀ) * (T * (V * Vᵀ)) + (U * Uᵀ) * (T * (V * Vᵀ)) := by
      rw [← Matrix.add_mul, sub_add_cancel, Matrix.one_mul]
    have horth : ((1 - U * Uᵀ) * (T * (V * Vᵀ)))ᵀ * ((U * Uᵀ) * (T * (V * Vᵀ))) = 0 := by
      rw [Matrix.transpose_mul, hP.compl.symm, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - U * Uᵀ),
        Matrix.sub_mul, Matrix.one_mul, hP.idem, sub_self, Matrix.zero_mul, Matrix.mul_zero]
    have := frob_sq_add_of_orth horth
    rw [← e] at this
    rw [this]
    exact le_add_of_nonneg_right (sq_nonneg _)
  -- `‖P T (1 - Q)‖ ≤ ‖T (1 - Q)‖`
  have h2 : ‖(U * Uᵀ) * (T * (1 - V * Vᵀ))‖ ≤ ‖T * (1 - V * Vᵀ)‖ := hP.norm_mul_le _
  have hUp : ‖(1 - U * Uᵀ) * T * V‖ ≤ ‖(1 - U * Uᵀ) * (T * (V * Vᵀ))‖ := by
    calc ‖(1 - U * Uᵀ) * T * V‖ ≤ ‖(1 - U * Uᵀ) * T * (V * Vᵀ)‖ := keyV _
      _ = ‖(1 - U * Uᵀ) * (T * (V * Vᵀ))‖ := by rw [Matrix.mul_assoc]
  have hVp : ‖(1 - V * Vᵀ) * Tᵀ * U‖ ≤ ‖(U * Uᵀ) * (T * (1 - V * Vᵀ))‖ := by
    calc ‖(1 - V * Vᵀ) * Tᵀ * U‖ ≤ ‖(1 - V * Vᵀ) * Tᵀ * (U * Uᵀ)‖ := keyU _
      _ = ‖(U * Uᵀ) * (T * (1 - V * Vᵀ))‖ := by
          have e : ((1 - V * Vᵀ) * Tᵀ * (U * Uᵀ))ᵀ = U * Uᵀ * (T * (1 - V * Vᵀ)) := by
            rw [Matrix.transpose_mul ((1 - V * Vᵀ) * Tᵀ) (U * Uᵀ), hP.symm,
              Matrix.transpose_mul (1 - V * Vᵀ) Tᵀ, Matrix.transpose_transpose, hQ.compl.symm]
          rw [← Frobenius.norm_transpose, e]
  calc ‖(1 - U * Uᵀ) * T * V‖ ^ 2 + ‖(1 - V * Vᵀ) * Tᵀ * U‖ ^ 2
      ≤ ‖(1 - U * Uᵀ) * (T * (V * Vᵀ))‖ ^ 2 + ‖(U * Uᵀ) * (T * (1 - V * Vᵀ))‖ ^ 2 := by
        gcongr
    _ ≤ ‖T * (V * Vᵀ)‖ ^ 2 + ‖T * (1 - V * Vᵀ)‖ ^ 2 := by gcongr
    _ = ‖T‖ ^ 2 := hsplit.symm

/-- **Sharp form of the bound following (34) of arXiv 2309.06125**:
`‖W_X(T, N)‖ ≤ ‖T‖ ‖N‖ / σ_r` (constant `1`, the paper has `2`) for every `T` and every `N` with
`Uᵀ N = 0`, in particular for every normal `N`.  `ρ` is a lower bound for the singular values of
`S`.  The two terms of (34) are orthogonal in the Frobenius inner product when `Uᵀ N = 0`, and the
blocks `U_p`, `V_p` of `T` satisfy `‖U_p‖² + ‖V_p‖² ≤ ‖T‖²`.  The constant is attained
(`weingarten_two_by_two`). -/
theorem norm_weingarten_le_one (h : IsFactorization X U S V) {ρ : ℝ} (hρ : 0 < ρ)
    (hS : ∀ v : EuclideanSpace ℝ (Fin r), ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖)
    (T N : Matrix m n ℝ) (hN : Uᵀ * N = 0) :
    ‖weingarten U S V T N‖ ≤ ‖T‖ * ‖N‖ / ρ := by
  have hSi : specNorm S⁻¹ ≤ ρ⁻¹ := specNorm_inv_le hρ hS
  have hSit : specNorm (S⁻¹)ᵀ ≤ ρ⁻¹ := by rwa [specNorm_transpose]
  have hUn : specNorm U ≤ 1 := specNorm_le_one_of_orthonormal h.orthU
  have hVt : specNorm Vᵀ ≤ 1 := by
    rw [specNorm_transpose]; exact specNorm_le_one_of_orthonormal h.orthV
  have hi0 : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ.le
  set Up := (1 - U * Uᵀ) * T * V with hUp
  set Vp := (1 - V * Vᵀ) * Tᵀ * U with hVp
  set W₁ := N * Vp * (S⁻¹)ᵀ * Vᵀ with hW₁
  set W₂ := U * (S⁻¹)ᵀ * Upᵀ * N with hW₂
  have hW : weingarten U S V T N = W₁ + W₂ := rfl
  have hNU : Nᵀ * U = 0 := by
    rw [← Matrix.transpose_transpose U, ← Matrix.transpose_mul, hN, Matrix.transpose_zero]
  have horth : W₁ᵀ * W₂ = 0 := by
    rw [hW₁, hW₂]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Nᵀ U, hNU, Matrix.zero_mul]
    simp only [Matrix.mul_zero]
  have hpyth : ‖weingarten U S V T N‖ ^ 2 = ‖W₁‖ ^ 2 + ‖W₂‖ ^ 2 := by
    rw [hW]; exact frob_sq_add_of_orth horth
  have h1 : ‖W₁‖ ≤ ‖N‖ * ‖Vp‖ * ρ⁻¹ := by
    calc ‖W₁‖ = ‖N * Vp * (S⁻¹)ᵀ * Vᵀ‖ := rfl
      _ ≤ ‖N * Vp * (S⁻¹)ᵀ‖ * specNorm Vᵀ := frob_mul_le' _ _
      _ ≤ ‖N * Vp * (S⁻¹)ᵀ‖ * 1 := by gcongr
      _ = ‖N * Vp * (S⁻¹)ᵀ‖ := mul_one _
      _ ≤ ‖N * Vp‖ * specNorm (S⁻¹)ᵀ := frob_mul_le' _ _
      _ ≤ ‖N * Vp‖ * ρ⁻¹ := by gcongr
      _ ≤ ‖N‖ * ‖Vp‖ * ρ⁻¹ := by gcongr; exact Frobenius.norm_mul_le _ _
  have h2 : ‖W₂‖ ≤ ‖N‖ * ‖Up‖ * ρ⁻¹ := by
    have hsp : specNorm (U * (S⁻¹)ᵀ) ≤ ρ⁻¹ := by
      calc specNorm (U * (S⁻¹)ᵀ) ≤ specNorm U * specNorm (S⁻¹)ᵀ := specNorm_mul_le _ _
        _ ≤ 1 * ρ⁻¹ := by
            have := specNorm_nonneg (S⁻¹)ᵀ
            gcongr
        _ = ρ⁻¹ := one_mul _
    calc ‖W₂‖ = ‖U * (S⁻¹)ᵀ * (Upᵀ * N)‖ := by rw [hW₂, Matrix.mul_assoc]
      _ ≤ specNorm (U * (S⁻¹)ᵀ) * ‖Upᵀ * N‖ := frob_mul_le _ _
      _ ≤ ρ⁻¹ * ‖Upᵀ * N‖ := by gcongr
      _ ≤ ρ⁻¹ * (‖Upᵀ‖ * ‖N‖) := by gcongr; exact Frobenius.norm_mul_le _ _
      _ = ‖N‖ * ‖Up‖ * ρ⁻¹ := by rw [Frobenius.norm_transpose]; ring
  have hblocks : ‖Up‖ ^ 2 + ‖Vp‖ ^ 2 ≤ ‖T‖ ^ 2 := sq_Up_add_sq_Vp_le h.orthU h.orthV T
  have hsq : ‖weingarten U S V T N‖ ^ 2 ≤ (‖T‖ * ‖N‖ / ρ) ^ 2 := by
    rw [hpyth]
    have e1 : ‖W₁‖ ^ 2 ≤ (‖N‖ * ‖Vp‖ * ρ⁻¹) ^ 2 := by gcongr
    have e2 : ‖W₂‖ ^ 2 ≤ (‖N‖ * ‖Up‖ * ρ⁻¹) ^ 2 := by gcongr
    have hN0 : 0 ≤ ‖N‖ ^ 2 * ρ⁻¹ ^ 2 := by positivity
    calc ‖W₁‖ ^ 2 + ‖W₂‖ ^ 2
        ≤ (‖N‖ * ‖Vp‖ * ρ⁻¹) ^ 2 + (‖N‖ * ‖Up‖ * ρ⁻¹) ^ 2 := add_le_add e1 e2
      _ = ‖N‖ ^ 2 * ρ⁻¹ ^ 2 * (‖Up‖ ^ 2 + ‖Vp‖ ^ 2) := by ring
      _ ≤ ‖N‖ ^ 2 * ρ⁻¹ ^ 2 * ‖T‖ ^ 2 := by gcongr
      _ = (‖T‖ * ‖N‖ / ρ) ^ 2 := by rw [div_eq_mul_inv]; ring
  have hpos : 0 ≤ ‖T‖ * ‖N‖ / ρ := by positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hpos two_ne_zero).1 hsq

/-- **The curvature term of Prop. 6 of arXiv 2309.06125 is bounded by `B ε / σ_r`**, half of the
bound `norm_curvature_term_le` of the library, where `B` bounds `‖F‖` and `ε` the modelling
error. -/
theorem norm_curvature_term_le_one (h : IsFactorization X U S V) {ρ B ε : ℝ} (hρ : 0 < ρ)
    (hS : ∀ v : EuclideanSpace ℝ (Fin r), ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖)
    {F : Matrix m n ℝ} (hB : ‖F‖ ≤ B) (hε : ‖F - tangentProjAt X F‖ ≤ ε) :
    ‖weingarten U S V (tangentProjAt X F) (F - tangentProjAt X F)‖ ≤ B * ε / ρ := by
  have hN : Uᵀ * (F - tangentProjAt X F) = 0 :=
    h.Ut_mul_normal (by rw [map_sub, (isOrthProj_tanProj X).idem, sub_self])
  refine (norm_weingarten_le_one h hρ hS _ _ hN).trans ?_
  have h1 : ‖tangentProjAt X F‖ ≤ B := ((isOrthProj_tanProj X).norm_le F).trans hB
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  gcongr

end General

section SpecNorm

variable {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]

/-- The spectral norm is subadditive. -/
lemma specNorm_add_le (A B : Matrix m k ℝ) : specNorm (A + B) ≤ specNorm A + specNorm B := by
  refine specNorm_le_of (add_nonneg (specNorm_nonneg A) (specNorm_nonneg B)) fun x => ?_
  have hA := norm_toEuclideanLin_le A x
  have hB := norm_toEuclideanLin_le B x
  rw [Matrix.toLpLin_apply] at hA hB ⊢
  rw [Matrix.add_mulVec, WithLp.toLp_add, add_mul]
  exact (norm_add_le _ _).trans (add_le_add hA hB)

/-- `‖A + B + C‖₂ ≤ ‖A‖₂ + ‖B‖₂ + ‖C‖₂` for the spectral norm. -/
lemma specNorm_add3_le (A B C : Matrix m k ℝ) :
    specNorm (A + B + C) ≤ specNorm A + specNorm B + specNorm C :=
  (specNorm_add_le (A + B) C).trans (add_le_add (specNorm_add_le A B) le_rfl)

end SpecNorm

/-! ### Ambient-linear fields `F = L A + A R` -/

section Linear

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {X A : Matrix m n ℝ} {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
  {S : Matrix (Fin r) (Fin r) ℝ} {L : Matrix m m ℝ} {R : Matrix n n ℝ}

/-- The tangent part of `L X + X R` is all of it, so the normal part of `F = L A + A R` at `X`
only sees the error `E = A - X`: `N = (1 - U Uᵀ) (L E + E R) (1 - V Vᵀ)`. -/
theorem normal_linear_eq (h : IsFactorization X U S V) (L : Matrix m m ℝ) (R : Matrix n n ℝ)
    (A : Matrix m n ℝ) :
    (L * A + A * R) - tangentProjAt X (L * A + A * R) =
      (1 - U * Uᵀ) * (L * (A - X) + (A - X) * R) * (1 - V * Vᵀ) := by
  rw [normal_eq h]
  have e3 : (1 - U * Uᵀ) * X = 0 := by
    rw [h.eq, Matrix.sub_mul, Matrix.one_mul, colProj_mul_factor h.orthU, sub_self]
  have e4 : X * (1 - V * Vᵀ) = 0 := by
    rw [h.eq, Matrix.mul_sub, Matrix.mul_one, factor_mul_rowProj h.orthV, sub_self]
  have key : (1 - U * Uᵀ) * (L * X + X * R) * (1 - V * Vᵀ) = 0 := by
    rw [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc (1 - U * Uᵀ) X R, e3, Matrix.zero_mul,
      Matrix.zero_mul, add_zero, Matrix.mul_assoc, Matrix.mul_assoc L X, e4, Matrix.mul_zero,
      Matrix.mul_zero]
  have e : L * A + A * R = (L * (A - X) + (A - X) * R) + (L * X + X * R) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [e, Matrix.mul_add, Matrix.add_mul, key, add_zero]

/-- `‖N‖ ≤ (‖L‖₂ + ‖R‖₂) ‖A - X‖` for the normal part of `F = L A + A R` at `X`. -/
theorem norm_normal_linear_le (h : IsFactorization X U S V) (L : Matrix m m ℝ) (R : Matrix n n ℝ)
    (A : Matrix m n ℝ) :
    ‖(L * A + A * R) - tangentProjAt X (L * A + A * R)‖ ≤ (specNorm L + specNorm R) * ‖A - X‖ := by
  rw [normal_linear_eq h]
  have hP := (isOrthProjMat_mul_transpose h.orthU).compl
  have hQ := (isOrthProjMat_mul_transpose h.orthV).compl
  calc ‖(1 - U * Uᵀ) * (L * (A - X) + (A - X) * R) * (1 - V * Vᵀ)‖
      ≤ ‖(1 - U * Uᵀ) * (L * (A - X) + (A - X) * R)‖ := hQ.norm_mul_le' _
    _ ≤ ‖L * (A - X) + (A - X) * R‖ := hP.norm_mul_le _
    _ ≤ ‖L * (A - X)‖ + ‖(A - X) * R‖ := norm_add_le _ _
    _ ≤ specNorm L * ‖A - X‖ + ‖A - X‖ * specNorm R :=
        add_le_add (frob_mul_le _ _) (frob_mul_le' _ _)
    _ = (specNorm L + specNorm R) * ‖A - X‖ := by ring

/-- **The Weingarten term for an ambient-linear field.**  For `F = L A + A R`, `X = U S Vᵀ`,
`E = A - X`, `G = V S⁻¹ Uᵀ` and `N = F - Π(X) F`:
`W_X(Π F, N) = N (Rᵀ V Vᵀ + (G L E)ᵀ + (G E R)ᵀ) + (U Uᵀ Lᵀ + (L E G)ᵀ + (E R G)ᵀ) N`.
The pseudo-inverse `G` only meets the error `E`, never `A` itself: `G X = V Vᵀ`, `X G = U Uᵀ`. -/
theorem weingarten_linear_eq (h : IsFactorization X U S V) (L : Matrix m m ℝ) (R : Matrix n n ℝ)
    (A : Matrix m n ℝ) :
    weingarten U S V (tangentProjAt X (L * A + A * R))
        ((L * A + A * R) - tangentProjAt X (L * A + A * R)) =
      ((L * A + A * R) - tangentProjAt X (L * A + A * R)) *
          (Rᵀ * (V * Vᵀ) + (V * S⁻¹ * Uᵀ * L * (A - X))ᵀ + (V * S⁻¹ * Uᵀ * (A - X) * R)ᵀ) +
        (U * Uᵀ * Lᵀ + (L * (A - X) * (V * S⁻¹ * Uᵀ))ᵀ + ((A - X) * R * (V * S⁻¹ * Uᵀ))ᵀ) *
          ((L * A + A * R) - tangentProjAt X (L * A + A * R)) := by
  rw [weingarten_eq_ginv h]
  set F := L * A + A * R with hF
  set N := F - tangentProjAt X F with hN
  set G := V * S⁻¹ * Uᵀ with hG
  set E := A - X with hE
  have hGt : U * (S⁻¹)ᵀ * Vᵀ = Gᵀ := by
    rw [hG, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  have hA : A = X + E := by rw [hE, add_sub_cancel]
  have hNV : N * V = 0 :=
    h.normal_mul_V (by rw [hN, map_sub, (isOrthProj_tanProj X).idem, sub_self])
  have hUN : Uᵀ * N = 0 :=
    h.Ut_mul_normal (by rw [hN, map_sub, (isOrthProj_tanProj X).idem, sub_self])
  have hNX : N * Xᵀ = 0 := by
    rw [h.eq, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hNV, Matrix.zero_mul, Matrix.zero_mul]
  have hXN : Xᵀ * N = 0 := by
    rw [h.eq, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc, Matrix.mul_assoc, hUN, Matrix.mul_zero, Matrix.mul_zero]
  have hXG : Xᵀ * Gᵀ = V * Vᵀ := by
    rw [← Matrix.transpose_mul, hG, h.eq, ginv_mul_factor h.orthU h.det, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  have hGX : Gᵀ * Xᵀ = U * Uᵀ := by
    rw [← Matrix.transpose_mul, hG, h.eq, factor_mul_ginv h.orthV h.det, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  rw [hGt]
  -- the two halves separately
  have hleft : N * Fᵀ * Gᵀ = N * (Rᵀ * (V * Vᵀ) + (G * L * E)ᵀ + (G * E * R)ᵀ) := by
    have : N * Fᵀ * Gᵀ = N * Xᵀ * Lᵀ * Gᵀ + N * (Eᵀ * Lᵀ * Gᵀ) + N * Rᵀ * (Xᵀ * Gᵀ) +
        N * (Rᵀ * Eᵀ * Gᵀ) := by
      rw [hF, hA]
      simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_assoc]
      abel
    rw [this, hNX, Matrix.zero_mul, Matrix.zero_mul, hXG]
    simp only [Matrix.transpose_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  have hright : Gᵀ * Fᵀ * N = (U * Uᵀ * Lᵀ + (L * E * G)ᵀ + (E * R * G)ᵀ) * N := by
    have : Gᵀ * Fᵀ * N = (Gᵀ * Xᵀ) * (Lᵀ * N) + Gᵀ * (Eᵀ * (Lᵀ * N)) +
        Gᵀ * (Rᵀ * (Xᵀ * N)) + Gᵀ * (Rᵀ * (Eᵀ * N)) := by
      rw [hF, hA]
      simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_assoc]
      abel
    rw [this, hGX, hXN, Matrix.mul_zero, Matrix.mul_zero]
    simp only [Matrix.transpose_mul, Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [hleft, hright]

/-- **Robustness mechanism for ambient-linear fields.**  For `F = L A + A R` at `X = U S Vᵀ`
with error `E = A - X`, pseudo-inverse `G = V S⁻¹ Uᵀ` and modelling error `N = F - Π(X) F`:
`‖W_X(Π F, N)‖ ≤ ‖N‖ (‖L‖₂ + ‖R‖₂ + ‖G L E‖₂ + ‖G E R‖₂ + ‖L E G‖₂ + ‖E R G‖₂)`.
The singular values of `X` enter only through the four relative errors `X⁺ L E`, `X⁺ E R`,
`L E X⁺`, `E R X⁺`, the error `E = A - X` seen through the pseudo-inverse of `X`; compare the
general bound `‖Π F‖ ‖N‖ / σ_r` (`norm_weingarten_le_one`). -/
theorem norm_weingarten_linear_le (h : IsFactorization X U S V) (L : Matrix m m ℝ)
    (R : Matrix n n ℝ) (A : Matrix m n ℝ) :
    ‖weingarten U S V (tangentProjAt X (L * A + A * R))
        ((L * A + A * R) - tangentProjAt X (L * A + A * R))‖ ≤
      ‖(L * A + A * R) - tangentProjAt X (L * A + A * R)‖ *
        (specNorm L + specNorm R + specNorm (V * S⁻¹ * Uᵀ * L * (A - X)) +
          specNorm (V * S⁻¹ * Uᵀ * (A - X) * R) + specNorm (L * (A - X) * (V * S⁻¹ * Uᵀ)) +
          specNorm ((A - X) * R * (V * S⁻¹ * Uᵀ))) := by
  rw [weingarten_linear_eq h]
  set F := L * A + A * R with hF
  set N := F - tangentProjAt X F with hN
  set G := V * S⁻¹ * Uᵀ with hG
  set E := A - X with hE
  have hPU : IsOrthProjMat (U * Uᵀ) := isOrthProjMat_mul_transpose h.orthU
  have hPV : IsOrthProjMat (V * Vᵀ) := isOrthProjMat_mul_transpose h.orthV
  have hL := specNorm_nonneg L
  have hR := specNorm_nonneg R
  have hGE := specNorm_nonneg (G * E)
  have hEG := specNorm_nonneg (E * G)
  have c1 : specNorm (Rᵀ * (V * Vᵀ) + (G * L * E)ᵀ + (G * E * R)ᵀ) ≤
      specNorm R + specNorm (G * L * E) + specNorm (G * E * R) := by
    refine (specNorm_add3_le _ _ _).trans ?_
    rw [specNorm_transpose, specNorm_transpose]
    have a1 : specNorm (Rᵀ * (V * Vᵀ)) ≤ specNorm R := by
      calc specNorm (Rᵀ * (V * Vᵀ)) ≤ specNorm Rᵀ * specNorm (V * Vᵀ) := specNorm_mul_le _ _
        _ ≤ specNorm R * 1 := by rw [specNorm_transpose]; gcongr; exact hPV.specNorm_le_one
        _ = specNorm R := mul_one _
    linarith
  have c2 : specNorm (U * Uᵀ * Lᵀ + (L * E * G)ᵀ + (E * R * G)ᵀ) ≤
      specNorm L + specNorm (L * E * G) + specNorm (E * R * G) := by
    refine (specNorm_add3_le _ _ _).trans ?_
    rw [specNorm_transpose, specNorm_transpose]
    have b1 : specNorm (U * Uᵀ * Lᵀ) ≤ specNorm L := by
      calc specNorm (U * Uᵀ * Lᵀ) ≤ specNorm (U * Uᵀ) * specNorm Lᵀ := specNorm_mul_le _ _
        _ ≤ 1 * specNorm L := by
            rw [specNorm_transpose]; gcongr; exact hPU.specNorm_le_one
        _ = specNorm L := one_mul _
    linarith
  calc ‖N * (Rᵀ * (V * Vᵀ) + (G * L * E)ᵀ + (G * E * R)ᵀ) +
        (U * Uᵀ * Lᵀ + (L * E * G)ᵀ + (E * R * G)ᵀ) * N‖
      ≤ ‖N * (Rᵀ * (V * Vᵀ) + (G * L * E)ᵀ + (G * E * R)ᵀ)‖ +
        ‖(U * Uᵀ * Lᵀ + (L * E * G)ᵀ + (E * R * G)ᵀ) * N‖ := norm_add_le _ _
    _ ≤ ‖N‖ * specNorm (Rᵀ * (V * Vᵀ) + (G * L * E)ᵀ + (G * E * R)ᵀ) +
        specNorm (U * Uᵀ * Lᵀ + (L * E * G)ᵀ + (E * R * G)ᵀ) * ‖N‖ :=
        add_le_add (frob_mul_le' _ _) (frob_mul_le _ _)
    _ ≤ ‖N‖ * (specNorm R + specNorm (G * L * E) + specNorm (G * E * R)) +
        (specNorm L + specNorm (L * E * G) + specNorm (E * R * G)) * ‖N‖ :=
        add_le_add (mul_le_mul_of_nonneg_left c1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right c2 (norm_nonneg _))
    _ = ‖N‖ * (specNorm L + specNorm R + specNorm (G * L * E) + specNorm (G * E * R) +
        specNorm (L * E * G) + specNorm (E * R * G)) := by ring

/-- **The curvature term for an ambient-linear field in terms of `σ_r`.**  With `ρ ≤ σ_r(S)`
and `E = A - X`: `‖W_X(Π F, N)‖ ≤ (‖L‖₂ + ‖R‖₂)² ‖E‖ (1 + 2 ‖E‖ / ρ)`.  When `‖E‖ ≤ c ρ`
(the current approximation is within `c σ_r` of the ambient solution, as for the best rank-`r`
approximation of a matrix with `σ_{r+1} ≤ c σ_r`) the curvature term is `O(‖E‖)` with a constant
independent of `σ_r`: the `1 / σ_r` of the general bound is cancelled by the normal part. -/
theorem norm_weingarten_linear_le_sigma (h : IsFactorization X U S V) {ρ : ℝ} (hρ : 0 < ρ)
    (hS : ∀ v : EuclideanSpace ℝ (Fin r), ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖)
    (L : Matrix m m ℝ) (R : Matrix n n ℝ) (A : Matrix m n ℝ) :
    ‖weingarten U S V (tangentProjAt X (L * A + A * R))
        ((L * A + A * R) - tangentProjAt X (L * A + A * R))‖ ≤
      (specNorm L + specNorm R) ^ 2 * ‖A - X‖ * (1 + 2 * ‖A - X‖ / ρ) := by
  refine (norm_weingarten_linear_le h L R A).trans ?_
  set G := V * S⁻¹ * Uᵀ with hG
  set E := A - X with hE
  have hGn : specNorm G ≤ ρ⁻¹ := specNorm_ginv_le hρ h.orthU h.orthV hS
  have hEs : specNorm E ≤ ‖E‖ := specNorm_le_frob E
  have hL := specNorm_nonneg L
  have hR := specNorm_nonneg R
  have hG0 := specNorm_nonneg G
  have hE0 := norm_nonneg E
  have hEs0 := specNorm_nonneg E
  have hi0 : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ.le
  have hN : ‖(L * A + A * R) - tangentProjAt X (L * A + A * R)‖ ≤ (specNorm L + specNorm R) * ‖E‖ :=
    norm_normal_linear_le h L R A
  have t1 : specNorm (G * L * E) ≤ ρ⁻¹ * specNorm L * ‖E‖ := by
    calc specNorm (G * L * E) ≤ specNorm (G * L) * specNorm E := specNorm_mul_le _ _
      _ ≤ specNorm G * specNorm L * specNorm E := by gcongr; exact specNorm_mul_le _ _
      _ ≤ ρ⁻¹ * specNorm L * ‖E‖ := by gcongr
  have t2 : specNorm (G * E * R) ≤ ρ⁻¹ * ‖E‖ * specNorm R := by
    calc specNorm (G * E * R) ≤ specNorm (G * E) * specNorm R := specNorm_mul_le _ _
      _ ≤ specNorm G * specNorm E * specNorm R := by gcongr; exact specNorm_mul_le _ _
      _ ≤ ρ⁻¹ * ‖E‖ * specNorm R := by gcongr
  have t3 : specNorm (L * E * G) ≤ specNorm L * ‖E‖ * ρ⁻¹ := by
    calc specNorm (L * E * G) ≤ specNorm (L * E) * specNorm G := specNorm_mul_le _ _
      _ ≤ specNorm L * specNorm E * specNorm G := by gcongr; exact specNorm_mul_le _ _
      _ ≤ specNorm L * ‖E‖ * ρ⁻¹ := by gcongr
  have t4 : specNorm (E * R * G) ≤ ‖E‖ * specNorm R * ρ⁻¹ := by
    calc specNorm (E * R * G) ≤ specNorm (E * R) * specNorm G := specNorm_mul_le _ _
      _ ≤ specNorm E * specNorm R * specNorm G := by gcongr; exact specNorm_mul_le _ _
      _ ≤ ‖E‖ * specNorm R * ρ⁻¹ := by gcongr
  have hsum : specNorm L + specNorm R + specNorm (G * L * E) + specNorm (G * E * R) +
      specNorm (L * E * G) + specNorm (E * R * G) ≤
      (specNorm L + specNorm R) * (1 + 2 * ‖E‖ / ρ) := by
    rw [div_eq_mul_inv]
    nlinarith [t1, t2, t3, t4]
  have hsum0 : 0 ≤ (specNorm L + specNorm R) * (1 + 2 * ‖E‖ / ρ) := by
    apply mul_nonneg (by linarith); positivity
  have hsix : 0 ≤ specNorm L + specNorm R + specNorm (G * L * E) + specNorm (G * E * R) +
      specNorm (L * E * G) + specNorm (E * R * G) := by
    have := specNorm_nonneg (G * L * E); have := specNorm_nonneg (G * E * R)
    have := specNorm_nonneg (L * E * G); have := specNorm_nonneg (E * R * G)
    linarith
  calc ‖(L * A + A * R) - tangentProjAt X (L * A + A * R)‖ *
        (specNorm L + specNorm R + specNorm (G * L * E) + specNorm (G * E * R) +
          specNorm (L * E * G) + specNorm (E * R * G))
      ≤ (specNorm L + specNorm R) * ‖E‖ * ((specNorm L + specNorm R) * (1 + 2 * ‖E‖ / ρ)) :=
        mul_le_mul hN hsum hsix (mul_nonneg (by linarith) hE0)
    _ = (specNorm L + specNorm R) ^ 2 * ‖E‖ * (1 + 2 * ‖E‖ / ρ) := by ring

end Linear

/-! ### The test problem of §5.2 is ambient-linear -/

section Instance

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The vector field (51) of arXiv 2309.06125 is ambient-linear.**  For the curve
`A(t) = U(t) Σ(t) V(t)ᵀ` of (49)-(50), `U(t) = exp(t Ω_U)`, `Σ(t) = Σ₀ exp(t D)`,
`V(t) = exp(t Ω_V)`, the field (51) is `Ȧ = Ω_U A + U Σ D Vᵀ + A Ω_Vᵀ`.  With orthogonal
`U` and diagonal `Σ`, `D` it equals `L A + A R` with `L = Ω_U + U D Uᵀ` and `R = Ω_Vᵀ`, so that
`norm_weingarten_linear_le` applies with `‖L‖₂ ≤ ‖Ω_U‖₂ + ‖D‖₂`
(`specNorm_field51_L_le`) and `‖R‖₂ = ‖Ω_V‖₂`, independently of the singular values. -/
theorem field51_eq (ΩU ΩV U V : Matrix n n ℝ) (σ d : n → ℝ) (hU : Uᵀ * U = 1) :
    ΩU * (U * Matrix.diagonal σ * Vᵀ) + U * (Matrix.diagonal σ * Matrix.diagonal d) * Vᵀ +
        (U * Matrix.diagonal σ * Vᵀ) * ΩVᵀ =
      (ΩU + U * Matrix.diagonal d * Uᵀ) * (U * Matrix.diagonal σ * Vᵀ) +
        (U * Matrix.diagonal σ * Vᵀ) * ΩVᵀ := by
  have hd : Matrix.diagonal d * Matrix.diagonal σ = Matrix.diagonal σ * Matrix.diagonal d := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; ext i; ring
  have e : U * Matrix.diagonal d * Uᵀ * (U * Matrix.diagonal σ * Vᵀ) =
      U * (Matrix.diagonal σ * Matrix.diagonal d) * Vᵀ := by
    calc U * Matrix.diagonal d * Uᵀ * (U * Matrix.diagonal σ * Vᵀ)
        = U * (Matrix.diagonal d * (Uᵀ * U) * Matrix.diagonal σ) * Vᵀ := by
          simp only [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal σ * Matrix.diagonal d) * Vᵀ := by rw [hU, Matrix.mul_one, hd]
  rw [Matrix.add_mul, e]

/-- `‖Ω_U + U D Uᵀ‖₂ ≤ ‖Ω_U‖₂ + ‖D‖₂` for orthogonal `U`. -/
theorem specNorm_field51_L_le (ΩU U : Matrix n n ℝ) (D : Matrix n n ℝ) (hU : Uᵀ * U = 1) :
    specNorm (ΩU + U * D * Uᵀ) ≤ specNorm ΩU + specNorm D := by
  have hUn : specNorm U ≤ 1 := specNorm_le_one_of_orthonormal hU
  have hUt : specNorm Uᵀ ≤ 1 := by rw [specNorm_transpose]; exact hUn
  have := specNorm_nonneg (U * D)
  have := specNorm_nonneg D
  have h1 : specNorm (U * D * Uᵀ) ≤ specNorm D := by
    calc specNorm (U * D * Uᵀ) ≤ specNorm (U * D) * specNorm Uᵀ := specNorm_mul_le _ _
      _ ≤ specNorm (U * D) * 1 := by gcongr
      _ = specNorm (U * D) := mul_one _
      _ ≤ specNorm U * specNorm D := specNorm_mul_le _ _
      _ ≤ 1 * specNorm D := by gcongr
      _ = specNorm D := one_mul _
  exact (specNorm_add_le _ _).trans (by linarith)

end Instance

/-! ### Two explicit examples -/

section Examples

/-- The rank-one point `X = σ e₁ e₁ᵀ` of `ℝ^{2 × 2}`, as `U S Vᵀ`. -/
private lemma isFactorization_two {σ : ℝ} (hσ : σ ≠ 0) :
    IsFactorization
      ((!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) * !![σ] * (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ)
      !![(1 : ℝ); 0] !![σ] !![(1 : ℝ); 0] where
  orthU := by ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  orthV := by ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  det := by simpa using hσ
  eq := rfl

private lemma inv_one_by_one {σ : ℝ} (hσ : σ ≠ 0) :
    (!![σ] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = !![σ⁻¹] := by
  apply Matrix.inv_eq_left_inv
  ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply, inv_mul_cancel₀ hσ]

/-- **The sharp constant is attained.**  At `X = σ e₁ e₁ᵀ` with the constant field
`F = e₁ e₂ᵀ + e₂ e₁ᵀ + ε e₂ e₂ᵀ`: `Π F = e₁ e₂ᵀ + e₂ e₁ᵀ`, `N = ε e₂ e₂ᵀ` and
`W_X(Π F, N) = (ε / σ) (e₁ e₂ᵀ + e₂ e₁ᵀ)`, so `‖W‖ = ‖Π F‖ ‖N‖ / σ` exactly
(`‖W‖ = √2 ε / σ`): the curvature term of a `Y`-independent field is of size `ε / σ_r`
whenever the normal part `ε` is not of the special form of `normal_linear_eq`. -/
theorem weingarten_two_by_two {σ ε : ℝ} (hσ : 0 < σ) :
    let U : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]
    let S : Matrix (Fin 1) (Fin 1) ℝ := !![σ]
    let X := U * S * Uᵀ
    let F : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, ε]
    tangentProjAt X F = !![0, 1; 1, 0] ∧ F - tangentProjAt X F = !![0, 0; 0, ε] ∧
      weingarten U S U (tangentProjAt X F) (F - tangentProjAt X F) = !![0, ε / σ; ε / σ, 0] ∧
      ‖weingarten U S U (tangentProjAt X F) (F - tangentProjAt X F)‖ =
        ‖tangentProjAt X F‖ * ‖F - tangentProjAt X F‖ / σ := by
  intro U S X F
  have h := isFactorization_two hσ.ne'
  have hT : tangentProjAt X F = !![0, 1; 1, 0] := by
    rw [h.tanProj_apply]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [F, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
        Matrix.transpose_apply]
  have hN : F - tangentProjAt X F = !![0, 0; 0, ε] := by
    rw [hT]; ext i j; fin_cases i <;> fin_cases j <;> simp [F]
  have hW : weingarten U S U (tangentProjAt X F) (F - tangentProjAt X F) =
      !![0, ε / σ; ε / σ, 0] := by
    rw [hN, hT]
    unfold weingarten
    rw [show S⁻¹ = !![σ⁻¹] from inv_one_by_one hσ.ne']
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [U, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
        Matrix.transpose_apply, Matrix.one_apply, div_eq_mul_inv, mul_comm]
  refine ⟨hT, hN, hW, ?_⟩
  rw [hW, hN, hT]
  have e1 : ‖(!![0, ε / σ; ε / σ, 0] : Matrix (Fin 2) (Fin 2) ℝ)‖ ^ 2 = 2 * (ε / σ) ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]; simp [Fin.sum_univ_two]; ring
  have e2 : ‖(!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)‖ ^ 2 = 2 := by
    rw [Frobenius.norm_sq_eq_sum]; simp [Fin.sum_univ_two]; norm_num
  have e3 : ‖(!![0, 0; 0, ε] : Matrix (Fin 2) (Fin 2) ℝ)‖ ^ 2 = ε ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]; simp [Fin.sum_univ_two]
  have hpos : 0 ≤ ‖(!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)‖ *
      ‖(!![0, 0; 0, ε] : Matrix (Fin 2) (Fin 2) ℝ)‖ / σ := by positivity
  refine (pow_left_inj₀ (norm_nonneg _) hpos two_ne_zero).1 ?_
  have e4 : (‖(!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)‖ *
      ‖(!![0, 0; 0, ε] : Matrix (Fin 2) (Fin 2) ℝ)‖ / σ) ^ 2 =
      ‖(!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)‖ ^ 2 *
        ‖(!![0, 0; 0, ε] : Matrix (Fin 2) (Fin 2) ℝ)‖ ^ 2 / σ ^ 2 := by ring
  rw [e1, e4, e2, e3]
  ring

/-- The point `X = diag(1, s, 0)` of `ℝ^{3 × 3}`, rank `2`, as `U S Vᵀ`. -/
private lemma isFactorization_three {s : ℝ} (hs : s ≠ 0) :
    IsFactorization ((!![1, 0; 0, 1; 0, 0] : Matrix (Fin 3) (Fin 2) ℝ) * !![1, 0; 0, s] *
        (!![1, 0; 0, 1; 0, 0] : Matrix (Fin 3) (Fin 2) ℝ)ᵀ)
      !![(1 : ℝ), 0; 0, 1; 0, 0] !![(1 : ℝ), 0; 0, s] !![(1 : ℝ), 0; 0, 1; 0, 0] where
  orthU := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  orthV := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  det := by simpa [Matrix.det_fin_two] using hs
  eq := rfl

private lemma inv_two_by_two {s : ℝ} (hs : s ≠ 0) :
    (!![(1 : ℝ), 0; 0, s] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = !![1, 0; 0, s⁻¹] := by
  apply Matrix.inv_eq_left_inv
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ hs]

/-- **The relative-error factor cannot be removed.**  On `3 × 3` matrices take
`X = diag(1, s, 0)` (rank `2`, `σ_r = s`), the orthogonal projector `L = e₂ e₂ᵀ + e₃ e₃ᵀ`
(`‖L‖₂ ≤ 1`), `R = 0`, and the ambient point `A = X + E`, `E = δ (e₂ e₃ᵀ + e₃ e₃ᵀ)`, so that
`F = L A + A R = L A`.  Then the normal part is `N = δ e₃ e₃ᵀ`, the relative error is
`X⁺ L E = (δ / s) e₂ e₃ᵀ` and the Weingarten term is `W = (δ² / s) e₃ e₂ᵀ`:
`‖W‖ = δ² / s = ‖N‖ ‖X⁺ L E‖`, which exceeds the modelling error `‖N‖ = δ` by the factor
`δ / s`, unbounded as `s → 0` at fixed `δ`.  The field is ambient-linear with `‖L‖₂ + ‖R‖₂ ≤ 1`
and `A` is within `√2 δ` of `X`; only the relative error `‖X⁺ (A - X)‖ = δ / s` is large.  So
`norm_weingarten_linear_le` is sharp in its dependence on the relative errors, and absolute
closeness of the approximation to the ambient solution is not what makes the curvature term
small. -/
theorem weingarten_relative_counterexample {s δ : ℝ} (hs : 0 < s) (hδ : 0 ≤ δ) :
    let U : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; 0, 0]
    let S : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, s]
    let X := U * S * Uᵀ
    let L : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 1, 0; 0, 0, 1]
    let E : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, δ; 0, 0, δ]
    let F := L * (X + E) + (X + E) * 0
    IsOrthProjMat L ∧
      F - tangentProjAt X F = !![0, 0, 0; 0, 0, 0; 0, 0, δ] ∧
      ‖F - tangentProjAt X F‖ = δ ∧
      U * S⁻¹ * Uᵀ * L * E = !![0, 0, 0; 0, 0, δ / s; 0, 0, 0] ∧
      ‖U * S⁻¹ * Uᵀ * L * E‖ = δ / s ∧
      weingarten U S U (tangentProjAt X F) (F - tangentProjAt X F) =
        !![0, 0, 0; 0, 0, 0; 0, δ ^ 2 / s, 0] ∧
      ‖weingarten U S U (tangentProjAt X F) (F - tangentProjAt X F)‖ = δ ^ 2 / s := by
  intro U S X L E F
  have h := isFactorization_three hs.ne'
  have hL : IsOrthProjMat L := by
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [L]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [L, Matrix.mul_apply, Fin.sum_univ_succ]
  have hUt : Uᵀ = !![1, 0, 0; 0, 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [U]
  have hF : F = !![0, 0, 0; 0, s, δ; 0, 0, δ] := by
    change L * (U * S * Uᵀ + E) + (U * S * Uᵀ + E) * 0 = _
    rw [hUt]
    ext i j; fin_cases i <;> fin_cases j <;> simp [L, E, U, S]
  have hN : F - tangentProjAt X F = !![0, 0, 0; 0, 0, 0; 0, 0, δ] := by
    rw [hF, h.tanProj_apply, hUt]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hSi : S⁻¹ = !![1, 0; 0, s⁻¹] := inv_two_by_two hs.ne'
  have hGE : U * S⁻¹ * Uᵀ * L * E = !![0, 0, 0; 0, 0, δ / s; 0, 0, 0] := by
    rw [hSi, hUt]
    ext i j; fin_cases i <;> fin_cases j <;> simp [U, L, E, div_eq_mul_inv, mul_comm]
  have hT : tangentProjAt X F = !![0, 0, 0; 0, s, δ; 0, 0, 0] := by
    rw [hF, h.tanProj_apply, hUt]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hW : weingarten U S U (tangentProjAt X F) (F - tangentProjAt X F) =
      !![0, 0, 0; 0, 0, 0; 0, δ ^ 2 / s, 0] := by
    rw [hN, hT]
    unfold weingarten
    have hC : (1 : Matrix (Fin 3) (Fin 3) ℝ) - U * Uᵀ = !![0, 0, 0; 0, 0, 0; 0, 0, 1] := by
      rw [hUt]
      ext i j; fin_cases i <;> fin_cases j <;> simp [U]
    have hSit : (!![1, 0; 0, s⁻¹] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = !![1, 0; 0, s⁻¹] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have hTt : (!![0, 0, 0; 0, s, δ; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ)ᵀ =
        !![0, 0, 0; 0, s, 0; 0, δ, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [hSi, hC, Matrix.transpose_mul, Matrix.transpose_mul, hSit, hTt, hUt]
    have hCt : (!![0, 0, 0; 0, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ)ᵀ =
        !![0, 0, 0; 0, 0, 0; 0, 0, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [hCt]
    ext i j; fin_cases i <;> fin_cases j <;> simp [U, div_eq_mul_inv, pow_two]
  have hnormN : ‖(!![0, 0, 0; 0, 0, 0; 0, 0, δ] : Matrix (Fin 3) (Fin 3) ℝ)‖ = δ := by
    have e : ∑ i, ∑ j, ((!![0, 0, 0; 0, 0, 0; 0, 0, δ] : Matrix (Fin 3) (Fin 3) ℝ) i j) ^ 2 =
        δ ^ 2 := by simp [Fin.sum_univ_succ]
    rw [Frobenius.norm_def, e]; exact Real.sqrt_sq hδ
  have hnormGE : ‖(!![0, 0, 0; 0, 0, δ / s; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ)‖ = δ / s := by
    have e : ∑ i, ∑ j, ((!![0, 0, 0; 0, 0, δ / s; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ) i j) ^ 2 =
        (δ / s) ^ 2 := by simp [Fin.sum_univ_succ]
    rw [Frobenius.norm_def, e]; exact Real.sqrt_sq (by positivity)
  have hnormW : ‖(!![0, 0, 0; 0, 0, 0; 0, δ ^ 2 / s, 0] : Matrix (Fin 3) (Fin 3) ℝ)‖ =
      δ ^ 2 / s := by
    have e : ∑ i, ∑ j, ((!![0, 0, 0; 0, 0, 0; 0, δ ^ 2 / s, 0] : Matrix (Fin 3) (Fin 3) ℝ) i j) ^ 2
        = (δ ^ 2 / s) ^ 2 := by simp [Fin.sum_univ_succ]
    rw [Frobenius.norm_def, e]; exact Real.sqrt_sq (by positivity)
  exact ⟨hL, hN, by rw [hN, hnormN], hGE, by rw [hGE, hnormGE], hW, by rw [hW, hnormW]⟩

end Examples

end LeanDLRA.Novel.OpHO38
