import LeanDLRA.FixedRank.TangentSpace.ProjectorLipschitz

/-!
# The tangent projector on normal vectors, with the spectral norm of the normal vector

For matrices `X`, `Y` of rank `r` with `0 < ρ ≤ σ_{r-1}(X)` and a matrix `N` normal at `Y`
(`P(Y) N = 0`), `LeanDLRA/FixedRank/TangentSpace/ProjectorLipschitz.lean` shows
`‖P(X) N‖ ≤ ρ⁻¹ ‖Y - X‖ ‖N‖` with Frobenius norms throughout. This file bounds the same quantity
by the spectral norm `‖N‖₂` of the normal vector:

  `‖P(X) N‖² ≤ (ρ⁻¹ ‖Y - X‖)² (1 + (ρ⁻¹ ‖Y - X‖)²) ‖N‖₂²`   and   `‖P(X) N‖ ≤ √2 ρ⁻¹ ‖Y - X‖ ‖N‖₂`.

`‖P(X) N‖` and `‖Y - X‖` are Frobenius norms. The proof splits `P(X) N = Pu N + (1 - Pu) N Pv`
(`Pu`, `Pv` the projectors onto the column and row space of `X`) into two orthogonal pieces, bounds
each by `‖N‖₂` times the Frobenius norm of a product of projectors, `‖Pu (1 - Qu)‖` and
`‖(1 - Qv) Pv‖` (`Qu`, `Qv` the projectors of `Y`), and these by `ρ⁻¹ ‖(1 - Qu) X‖` and
`ρ⁻¹ ‖X (1 - Qv)‖`. The two parts of `X` overlap in the normal component `(1 - Qu) X (1 - Qv)` of
`X` at `Y`, which is of second order in `‖Y - X‖`; this is the factor `1 + (ρ⁻¹ ‖Y - X‖)²`.

## Main results

* `LeanDLRA.Curvature.continuous_specNorm`: the spectral norm is continuous.
* `LeanDLRA.Curvature.norm_sq_tangentProjMat_le_mul_specNorm_sq_of_normal`: projector form,
  `‖Pu N + N Pv - Pu N Pv‖² ≤ (‖Pu (1 - Qu)‖² + ‖(1 - Qv) Pv‖²) ‖N‖₂²` if `Qu N = 0`, `N Qv = 0`.
* `LeanDLRA.Curvature.norm_sq_tangentProjMat_le_mul_specNorm_sq_of_tangentProjMat_eq_zero`,
  `LeanDLRA.Curvature.norm_sq_tangentProjMat_le_two_mul_specNorm_sq_of_tangentProjMat_eq_zero`:
  the two bounds for factored matrices.
* `norm_sq_tangentProjAt_apply_le_mul_specNorm_sq_of_tangentProjAt_eq_zero`,
  `norm_tangentProjAt_apply_le_one_add_mul_specNorm_of_tangentProjAt_eq_zero`,
  `norm_tangentProjAt_apply_le_sqrt_two_mul_specNorm_of_tangentProjAt_eq_zero`: the bounds at
  matrices of rank `r`.

## Implementation notes

The bound `‖P(X) N‖ ≤ ρ⁻¹ ‖Y - X‖ ‖N‖₂` with the constant `1` does not hold: for `X = e₁ e₁ᵀ`,
`Y = cos α cos β u vᵀ` with unit vectors `u`, `v` at the angles `α`, `β` to `e₁`, and a suitable
`N` with `‖N‖₂ = 1`, the quotient `‖P(X) N‖² / ‖Y - X‖²` is `(a + b) / (a + b - a b)` with
`a = sin² α`, `b = sin² β`, which tends to `2` for `α, β → π/2`; this family is not formalized
here. The constant `√2` is therefore the best one in a bound without the second-order factor, and
the first bound has the constant `1` to first order in `‖Y - X‖`, which is what the derivative of
the first-order optimality condition along a curve needs
(`LeanDLRA/DLRA/QuasiOptimalitySpectral.lean`). Examples with `Y ≠ X` and `N ≠ 0` for the bounds
at matrices of rank `r` are in that file.
-/

open Set Filter Matrix

namespace LeanDLRA

namespace Curvature

section NormalVectors

open scoped LeanDLRA.Frobenius

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n]
  [DecidableEq k]

omit [DecidableEq m] in
/-- The spectral norm is a continuous function of the matrix: it is `1`-Lipschitz with respect to
the Frobenius norm. -/
theorem continuous_specNorm : Continuous (specNorm : Matrix m n ℝ → ℝ) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun A B => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul, abs_sub_le_iff]
  have h1 := WeylSingular.specNorm_add_le (A - B) B
  have h2 := WeylSingular.specNorm_add_le (B - A) A
  rw [sub_add_cancel] at h1 h2
  have h3 := specNorm_le_frob (A - B)
  have h4 := specNorm_le_frob (B - A)
  rw [norm_sub_rev] at h4
  constructor <;> linarith

omit [DecidableEq n] in
/-- Pythagoras for a projector on the left: `‖P B‖² + ‖(1 - P) B‖² = ‖B‖²`. -/
private theorem norm_sq_mul_add_norm_sq_compl_mul {P : Matrix m m ℝ} (hP : IsOrthProjMat P)
    (B : Matrix m n ℝ) : ‖P * B‖ ^ 2 + ‖(1 - P) * B‖ ^ 2 = ‖B‖ ^ 2 := by
  have hPP : P * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hP.idem, sub_self]
  have o : (P * B)ᵀ * ((1 - P) * B) = 0 := by
    rw [transpose_mul, hP.symm, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP, Matrix.zero_mul,
      Matrix.mul_zero]
  have s : P * B + (1 - P) * B = B := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    abel
  have e := frob_sq_add_of_orth o
  rw [s] at e
  linarith

/-- **The tangent projector on a normal vector, projector form with the spectral norm.** Let `Pu`
be an orthogonal projector and let `N` be normal with respect to `Qu`, `Qv`: `Qu N = 0` and
`N Qv = 0`. Then, with Frobenius norms of the two products of projectors,
`‖Pu N + N Pv - Pu N Pv‖² ≤ (‖Pu (1 - Qu)‖² + ‖(1 - Qv) Pv‖²) ‖N‖₂²`. -/
theorem norm_sq_tangentProjMat_le_mul_specNorm_sq_of_normal {Pu Qu : Matrix m m ℝ}
    {Pv Qv : Matrix n n ℝ} (hPu : IsOrthProjMat Pu) {N : Matrix m n ℝ} (hu : Qu * N = 0)
    (hv : N * Qv = 0) :
    ‖tangentProjMat Pu Pv N‖ ^ 2 ≤
      (‖Pu * (1 - Qu)‖ ^ 2 + ‖(1 - Qv) * Pv‖ ^ 2) * specNorm N ^ 2 := by
  classical
  have e : tangentProjMat Pu Pv N = Pu * N + (1 - Pu) * N * Pv := by
    simp only [tangentProjMat, Matrix.sub_mul, Matrix.one_mul]
    abel
  have hPP : Pu * (1 - Pu) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hPu.idem, sub_self]
  have horth : (Pu * N)ᵀ * ((1 - Pu) * N * Pv) = 0 := by
    rw [transpose_mul, hPu.symm, Matrix.mul_assoc Nᵀ, Matrix.mul_assoc (1 - Pu),
      ← Matrix.mul_assoc Pu, hPP, Matrix.zero_mul, Matrix.mul_zero]
  have e1 : Pu * N = Pu * (1 - Qu) * N := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hu, sub_zero]
  have e2 : N * Pv = N * ((1 - Qv) * Pv) := by
    rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hv, sub_zero]
  have h1 : ‖Pu * N‖ ≤ ‖Pu * (1 - Qu)‖ * specNorm N := by
    rw [e1]
    exact frob_mul_le' _ _
  have h2 : ‖(1 - Pu) * N * Pv‖ ≤ ‖(1 - Qv) * Pv‖ * specNorm N := by
    rw [Matrix.mul_assoc]
    refine (hPu.compl.norm_mul_le _).trans ?_
    rw [e2, mul_comm]
    exact frob_mul_le _ _
  rw [e, frob_sq_add_of_orth horth]
  have h1' := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2' := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [mul_pow] at h1' h2'
  linarith

omit [DecidableEq m] [DecidableEq n] in
/-- For `X = U S Vᵀ` with orthonormal `U`, `V` and `ρ ‖v‖ ≤ ‖S v‖`:
`‖M U Uᵀ‖ ≤ ρ⁻¹ ‖M X‖` for every `M`, in the Frobenius norm. -/
private theorem norm_mul_colProj_le {U : Matrix m k ℝ} {S : Matrix k k ℝ} {V : Matrix n k ℝ}
    {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) (M : Matrix m m ℝ) :
    ‖M * (U * Uᵀ)‖ ≤ ρ⁻¹ * ‖M * (U * S * Vᵀ)‖ := by
  classical
  have hdet := isUnit_det_of_bounded_below hρ hS
  rw [← factor_mul_ginv (U := U) (S := S) hV hdet, ← Matrix.mul_assoc]
  calc ‖M * (U * S * Vᵀ) * (V * S⁻¹ * Uᵀ)‖
      ≤ ‖M * (U * S * Vᵀ)‖ * specNorm (V * S⁻¹ * Uᵀ) := frob_mul_le' _ _
    _ ≤ ‖M * (U * S * Vᵀ)‖ * ρ⁻¹ :=
        mul_le_mul_of_nonneg_left (specNorm_ginv_le hρ hU hV hS) (norm_nonneg _)
    _ = ρ⁻¹ * ‖M * (U * S * Vᵀ)‖ := mul_comm _ _

omit [DecidableEq m] [DecidableEq n] in
/-- For `X = U S Vᵀ` with orthonormal `U`, `V` and `ρ ‖v‖ ≤ ‖S v‖`:
`‖V Vᵀ M‖ ≤ ρ⁻¹ ‖X M‖` for every `M`, in the Frobenius norm. -/
private theorem norm_rowProj_mul_le {U : Matrix m k ℝ} {S : Matrix k k ℝ} {V : Matrix n k ℝ}
    {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) (M : Matrix n n ℝ) :
    ‖V * Vᵀ * M‖ ≤ ρ⁻¹ * ‖U * S * Vᵀ * M‖ := by
  classical
  have hdet := isUnit_det_of_bounded_below hρ hS
  rw [← ginv_mul_factor (U := U) (S := S) hU hdet, Matrix.mul_assoc]
  calc ‖V * S⁻¹ * Uᵀ * (U * S * Vᵀ * M)‖
      ≤ specNorm (V * S⁻¹ * Uᵀ) * ‖U * S * Vᵀ * M‖ := frob_mul_le _ _
    _ ≤ ρ⁻¹ * ‖U * S * Vᵀ * M‖ :=
        mul_le_mul_of_nonneg_right (specNorm_ginv_le hρ hU hV hS) (norm_nonneg _)

/-- The Frobenius norms of the two products of projectors of `X = U S Vᵀ` (`ρ ‖v‖ ≤ ‖S v‖`) and
`Y = U' S' V'ᵀ`, bounded by the distance `d = ‖Y - X‖`:
`‖Pu (1 - Qu)‖² + ‖(1 - Qv) Pv‖² ≤ (ρ⁻¹ d)² (1 + (ρ⁻¹ d)²)` and `≤ 2 (ρ⁻¹ d)²`. -/
private theorem norm_sq_add_norm_sq_le {U U' : Matrix m k ℝ} {V V' : Matrix n k ℝ}
    {S S' : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) :
    ‖U * Uᵀ * (1 - U' * U'ᵀ)‖ ^ 2 + ‖(1 - V' * V'ᵀ) * (V * Vᵀ)‖ ^ 2 ≤
        (ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖) ^ 2 *
          (1 + (ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖) ^ 2) ∧
      ‖U * Uᵀ * (1 - U' * U'ᵀ)‖ ^ 2 + ‖(1 - V' * V'ᵀ) * (V * Vᵀ)‖ ^ 2 ≤
        2 * (ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖) ^ 2 := by
  classical
  have hP := isOrthProjMat_mul_transpose hU
  have hQ := isOrthProjMat_mul_transpose hV
  have hP' := isOrthProjMat_mul_transpose hU'
  have hQ' := isOrthProjMat_mul_transpose hV'
  have hu : U' * U'ᵀ * (U' * S' * V'ᵀ) = U' * S' * V'ᵀ := colProj_mul_factor hU'
  have hv : U' * S' * V'ᵀ * (V' * V'ᵀ) = U' * S' * V'ᵀ := factor_mul_rowProj hV'
  -- the two products of projectors against the two parts of `X`
  have hA : ‖U * Uᵀ * (1 - U' * U'ᵀ)‖ ≤ ρ⁻¹ * ‖(1 - U' * U'ᵀ) * (U * S * Vᵀ)‖ := by
    rw [← Matrix.frobenius_norm_transpose (U * Uᵀ * (1 - U' * U'ᵀ)), transpose_mul,
      hP'.compl.symm, hP.symm]
    exact norm_mul_colProj_le hρ hU hV hS _
  have hB : ‖(1 - V' * V'ᵀ) * (V * Vᵀ)‖ ≤ ρ⁻¹ * ‖U * S * Vᵀ * (1 - V' * V'ᵀ)‖ := by
    rw [← Matrix.frobenius_norm_transpose ((1 - V' * V'ᵀ) * (V * Vᵀ)), transpose_mul,
      hQ'.compl.symm, hQ.symm]
    exact norm_rowProj_mul_le hρ hU hV hS _
  -- the distance, split by the column projector of `Y`
  have pD := norm_sq_mul_add_norm_sq_compl_mul hP' (U' * S' * V'ᵀ - U * S * Vᵀ)
  have c1 : (1 - U' * U'ᵀ) * (U' * S' * V'ᵀ - U * S * Vᵀ) =
      -((1 - U' * U'ᵀ) * (U * S * Vᵀ)) := by
    rw [← neg_sub (U * S * Vᵀ) (U' * S' * V'ᵀ), Matrix.mul_neg, compl_mul_sub hu]
  rw [c1, norm_neg] at pD
  have c2 : U' * U'ᵀ * (U' * S' * V'ᵀ - U * S * Vᵀ) * (1 - V' * V'ᵀ) =
      -(U' * U'ᵀ * (U * S * Vᵀ * (1 - V' * V'ᵀ))) := by
    rw [Matrix.mul_assoc, ← neg_sub (U * S * Vᵀ) (U' * S' * V'ᵀ), Matrix.neg_mul,
      sub_mul_compl hv, Matrix.mul_neg]
  have c3 : ‖U' * U'ᵀ * (U * S * Vᵀ * (1 - V' * V'ᵀ))‖ ≤
      ‖U' * U'ᵀ * (U' * S' * V'ᵀ - U * S * Vᵀ)‖ := by
    have h := hQ'.compl.norm_mul_le' (U' * U'ᵀ * (U' * S' * V'ᵀ - U * S * Vᵀ))
    rwa [c2, norm_neg] at h
  have pY := norm_sq_mul_add_norm_sq_compl_mul hP' (U * S * Vᵀ * (1 - V' * V'ᵀ))
  have hxy : ‖(1 - U' * U'ᵀ) * (U * S * Vᵀ)‖ ^ 2 + ‖U * S * Vᵀ * (1 - V' * V'ᵀ)‖ ^ 2 ≤
      ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ ^ 2 +
        ‖(1 - U' * U'ᵀ) * (U * S * Vᵀ * (1 - V' * V'ᵀ))‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) c3 2
    linarith
  -- both parts of `X` are below the distance
  have hxd : ‖(1 - U' * U'ᵀ) * (U * S * Vᵀ)‖ ≤ ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ := by
    have h := hP'.compl.norm_mul_le (U' * S' * V'ᵀ - U * S * Vᵀ)
    rwa [c1, norm_neg] at h
  have hyd : ‖U * S * Vᵀ * (1 - V' * V'ᵀ)‖ ≤ ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ := by
    have h := hQ'.compl.norm_mul_le' (U' * S' * V'ᵀ - U * S * Vᵀ)
    have e : (U' * S' * V'ᵀ - U * S * Vᵀ) * (1 - V' * V'ᵀ) =
        -(U * S * Vᵀ * (1 - V' * V'ᵀ)) := by
      rw [← neg_sub (U * S * Vᵀ) (U' * S' * V'ᵀ), Matrix.neg_mul, sub_mul_compl hv]
    rwa [e, norm_neg] at h
  -- the normal component of `X` at `Y`
  have hg1 : ‖(1 - U' * U'ᵀ) * (U * S * Vᵀ * (1 - V' * V'ᵀ))‖ ≤
      ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ :=
    (hP'.compl.norm_mul_le _).trans hyd
  have hρ' : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ.le
  have hg2 : ‖(1 - U' * U'ᵀ) * (U * S * Vᵀ * (1 - V' * V'ᵀ))‖ ≤
      ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ := by
    have e : (1 - U' * U'ᵀ) * (U * S * Vᵀ * (1 - V' * V'ᵀ)) =
        (1 - U' * U'ᵀ) * (U * Uᵀ) * (U * S * Vᵀ * (1 - V' * V'ᵀ)) := by
      rw [Matrix.mul_assoc (1 - U' * U'ᵀ) (U * Uᵀ), ← Matrix.mul_assoc (U * Uᵀ) (U * S * Vᵀ),
        colProj_mul_factor hU]
    rw [e]
    calc ‖(1 - U' * U'ᵀ) * (U * Uᵀ) * (U * S * Vᵀ * (1 - V' * V'ᵀ))‖
        ≤ specNorm ((1 - U' * U'ᵀ) * (U * Uᵀ)) * ‖U * S * Vᵀ * (1 - V' * V'ᵀ)‖ :=
          frob_mul_le _ _
      _ ≤ ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ :=
          mul_le_mul (((specNorm_le_frob _).trans (norm_mul_colProj_le hρ hU hV hS _)).trans
            (mul_le_mul_of_nonneg_left hxd hρ')) hyd (norm_nonneg _)
            (mul_nonneg hρ' (norm_nonneg _))
  have hA2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hB2 := pow_le_pow_left₀ (norm_nonneg _) hB 2
  rw [mul_pow] at hA2 hB2
  have hr : 0 ≤ ρ⁻¹ ^ 2 := sq_nonneg _
  have hsum : ‖U * Uᵀ * (1 - U' * U'ᵀ)‖ ^ 2 + ‖(1 - V' * V'ᵀ) * (V * Vᵀ)‖ ^ 2 ≤
      ρ⁻¹ ^ 2 * (‖U' * S' * V'ᵀ - U * S * Vᵀ‖ ^ 2 +
        ‖(1 - U' * U'ᵀ) * (U * S * Vᵀ * (1 - V' * V'ᵀ))‖ ^ 2) :=
    (add_le_add hA2 hB2).trans
      ((mul_add _ _ _).symm.le.trans (mul_le_mul_of_nonneg_left hxy hr))
  constructor
  · refine hsum.trans ?_
    have h := pow_le_pow_left₀ (norm_nonneg _) hg2 2
    calc ρ⁻¹ ^ 2 * (‖U' * S' * V'ᵀ - U * S * Vᵀ‖ ^ 2 +
          ‖(1 - U' * U'ᵀ) * (U * S * Vᵀ * (1 - V' * V'ᵀ))‖ ^ 2)
        ≤ ρ⁻¹ ^ 2 * (‖U' * S' * V'ᵀ - U * S * Vᵀ‖ ^ 2 +
          (ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖) ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl h) hr
      _ = _ := by ring
  · refine hsum.trans ?_
    have h := pow_le_pow_left₀ (norm_nonneg _) hg1 2
    calc ρ⁻¹ ^ 2 * (‖U' * S' * V'ᵀ - U * S * Vᵀ‖ ^ 2 +
          ‖(1 - U' * U'ᵀ) * (U * S * Vᵀ * (1 - V' * V'ᵀ))‖ ^ 2)
        ≤ ρ⁻¹ ^ 2 * (‖U' * S' * V'ᵀ - U * S * Vᵀ‖ ^ 2 + ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl h) hr
      _ = _ := by ring

omit [DecidableEq m] [DecidableEq n] in
/-- A matrix in the kernel of `tangentProj U V` is annihilated by `U Uᵀ` from the left and by
`V Vᵀ` from the right. -/
private theorem mul_eq_zero_of_tangentProj_eq_zero {U : Matrix m k ℝ} {V : Matrix n k ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {N : Matrix m n ℝ} (h : tangentProj U V N = 0) :
    U * Uᵀ * N = 0 ∧ N * (V * Vᵀ) = 0 := by
  classical
  have hN : (1 - U * Uᵀ) * N * (1 - V * Vᵀ) = N := by
    have h' := tangentProj_add_normal U V N
    rwa [h, zero_add] at h'
  have hP := isOrthProjMat_mul_transpose hU
  have hQ := isOrthProjMat_mul_transpose hV
  have hPP : U * Uᵀ * (1 - U * Uᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hP.idem, sub_self]
  have hQQ : (1 - V * Vᵀ) * (V * Vᵀ) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hQ.idem, sub_self]
  constructor
  · calc U * Uᵀ * N = U * Uᵀ * ((1 - U * Uᵀ) * N * (1 - V * Vᵀ)) := by rw [hN]
      _ = U * Uᵀ * (1 - U * Uᵀ) * N * (1 - V * Vᵀ) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hPP, Matrix.zero_mul, Matrix.zero_mul]
  · calc N * (V * Vᵀ) = (1 - U * Uᵀ) * N * (1 - V * Vᵀ) * (V * Vᵀ) := by rw [hN]
      _ = (1 - U * Uᵀ) * N * ((1 - V * Vᵀ) * (V * Vᵀ)) := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hQQ, Matrix.mul_zero]

omit [DecidableEq m] in
/-- **The tangent projector at `X` on a vector normal at `Y`, factor form with the spectral
norm.** Let `X = U S Vᵀ` and `Y = U' S' V'ᵀ` with orthonormal columns of `U`, `V`, `U'`, `V'` and
`ρ ‖v‖ ≤ ‖S v‖`, `ρ > 0`. If `N` is normal at `Y`, `P(Y) N = 0`, then with `e = ρ⁻¹ ‖Y - X‖`
(Frobenius norm) `‖P(X) N‖² ≤ e² (1 + e²) ‖N‖₂²`. Nothing is assumed on the core `S'`. -/
theorem norm_sq_tangentProjMat_le_mul_specNorm_sq_of_tangentProjMat_eq_zero {U U' : Matrix m k ℝ}
    {V V' : Matrix n k ℝ} {S S' : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) {N : Matrix m n ℝ}
    (hN : tangentProjMat (U' * U'ᵀ) (V' * V'ᵀ) N = 0) :
    ‖tangentProjMat (U * Uᵀ) (V * Vᵀ) N‖ ^ 2 ≤
      (ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖) ^ 2 *
        (1 + (ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖) ^ 2) * specNorm N ^ 2 := by
  classical
  rw [tangentProjMat_eq_tangentProj] at hN
  obtain ⟨h1, h2⟩ := mul_eq_zero_of_tangentProj_eq_zero hU' hV' hN
  exact (norm_sq_tangentProjMat_le_mul_specNorm_sq_of_normal (isOrthProjMat_mul_transpose hU)
    h1 h2).trans (mul_le_mul_of_nonneg_right
      (norm_sq_add_norm_sq_le (S' := S') hρ hU hV hU' hV' hS).1 (sq_nonneg _))

omit [DecidableEq m] in
/-- **The tangent projector at `X` on a vector normal at `Y`, factor form with the spectral norm
and the constant `√2`.** Under the hypotheses of
`norm_sq_tangentProjMat_le_mul_specNorm_sq_of_tangentProjMat_eq_zero`:
`‖P(X) N‖² ≤ 2 (ρ⁻¹ ‖Y - X‖)² ‖N‖₂²`, without a second-order term. -/
theorem norm_sq_tangentProjMat_le_two_mul_specNorm_sq_of_tangentProjMat_eq_zero
    {U U' : Matrix m k ℝ} {V V' : Matrix n k ℝ} {S S' : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) {N : Matrix m n ℝ}
    (hN : tangentProjMat (U' * U'ᵀ) (V' * V'ᵀ) N = 0) :
    ‖tangentProjMat (U * Uᵀ) (V * Vᵀ) N‖ ^ 2 ≤
      2 * (ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖) ^ 2 * specNorm N ^ 2 := by
  classical
  rw [tangentProjMat_eq_tangentProj] at hN
  obtain ⟨h1, h2⟩ := mul_eq_zero_of_tangentProj_eq_zero hU' hV' hN
  exact (norm_sq_tangentProjMat_le_mul_specNorm_sq_of_normal (isOrthProjMat_mul_transpose hU)
    h1 h2).trans (mul_le_mul_of_nonneg_right
      (norm_sq_add_norm_sq_le (S' := S') hρ hU hV hU' hV' hS).2 (sq_nonneg _))

end NormalVectors

end Curvature

section AtPoint

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **The tangent projector at `X` on a vector normal at `Y`, spectral norm of the normal
vector.** For `X`, `Y` of rank `r` with `0 < ρ ≤ σ_{r-1}(X)` and `P(Y) N = 0`, with
`e = ρ⁻¹ ‖Y - X‖` (Frobenius norm): `‖P(X) N‖² ≤ e² (1 + e²) ‖N‖₂²`. -/
theorem norm_sq_tangentProjAt_apply_le_mul_specNorm_sq_of_tangentProjAt_eq_zero {r : ℕ}
    {X Y : Matrix m n ℝ} (hX : X.rank = r) (hY : Y.rank = r) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) {N : Matrix m n ℝ}
    (hN : tangentProjAt Y N = 0) :
    ‖tangentProjAt X N‖ ^ 2 ≤
      (ρ⁻¹ * ‖Y - X‖) ^ 2 * (1 + (ρ⁻¹ * ‖Y - X‖) ^ 2) * Curvature.specNorm N ^ 2 := by
  classical
  obtain ⟨U, S, V, hU, hV, hS, rfl⟩ := (SVD.rank_eq_iff_exists_factor Y).1 hY
  obtain ⟨U₀, S₀, V₀, hU₀, hV₀, hS₀, rfl⟩ := (SVD.rank_eq_iff_exists_factor X).1 hX
  have hb := WeylSingular.mul_norm_le_norm_toEuclideanLin_core hU₀ hV₀ rfl hρ
    (by simpa using hσ)
  rw [tangentProjAt_eq_tangentProj hU hV hS] at hN
  rw [tangentProjAt_eq_tangentProj hU₀ hV₀ hS₀]
  have h := Curvature.norm_sq_tangentProjMat_le_mul_specNorm_sq_of_tangentProjMat_eq_zero
    (S' := S) hρ hU₀ hV₀ hU hV hb (N := N)
    (by rw [Curvature.tangentProjMat_eq_tangentProj]; exact hN)
  rwa [Curvature.tangentProjMat_eq_tangentProj] at h

/-- **The tangent projector at `X` on a vector normal at `Y`, spectral norm, linear form.** Under
the hypotheses of `norm_sq_tangentProjAt_apply_le_mul_specNorm_sq_of_tangentProjAt_eq_zero`:
`‖P(X) N‖ ≤ ρ⁻¹ ‖Y - X‖ (1 + ρ⁻¹ ‖Y - X‖) ‖N‖₂`. The constant is `1` to first order in
`‖Y - X‖`. -/
theorem norm_tangentProjAt_apply_le_one_add_mul_specNorm_of_tangentProjAt_eq_zero {r : ℕ}
    {X Y : Matrix m n ℝ} (hX : X.rank = r) (hY : Y.rank = r) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) {N : Matrix m n ℝ}
    (hN : tangentProjAt Y N = 0) :
    ‖tangentProjAt X N‖ ≤
      ρ⁻¹ * ‖Y - X‖ * (1 + ρ⁻¹ * ‖Y - X‖) * Curvature.specNorm N := by
  have h := norm_sq_tangentProjAt_apply_le_mul_specNorm_sq_of_tangentProjAt_eq_zero hX hY hρ hσ hN
  have he : 0 ≤ ρ⁻¹ * ‖Y - X‖ := mul_nonneg (inv_nonneg.2 hρ.le) (norm_nonneg _)
  have hs := Curvature.specNorm_nonneg N
  have h0 : 0 ≤ ρ⁻¹ * ‖Y - X‖ * (1 + ρ⁻¹ * ‖Y - X‖) * Curvature.specNorm N :=
    mul_nonneg (mul_nonneg he (by linarith)) hs
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).mp (h.trans ?_)
  have h1 : 1 + (ρ⁻¹ * ‖Y - X‖) ^ 2 ≤ (1 + ρ⁻¹ * ‖Y - X‖) ^ 2 := by nlinarith
  calc (ρ⁻¹ * ‖Y - X‖) ^ 2 * (1 + (ρ⁻¹ * ‖Y - X‖) ^ 2) * Curvature.specNorm N ^ 2
      ≤ (ρ⁻¹ * ‖Y - X‖) ^ 2 * (1 + ρ⁻¹ * ‖Y - X‖) ^ 2 * Curvature.specNorm N ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by ring

/-- **The tangent projector at `X` on a vector normal at `Y`, spectral norm, constant `√2`.** For
`X`, `Y` of rank `r` with `0 < ρ ≤ σ_{r-1}(X)` and `P(Y) N = 0`:
`‖P(X) N‖ ≤ √2 ρ⁻¹ ‖Y - X‖ ‖N‖₂`, with the Frobenius norm of `P(X) N` and of `Y - X`. No
smallness of `‖Y - X‖` is needed. -/
theorem norm_tangentProjAt_apply_le_sqrt_two_mul_specNorm_of_tangentProjAt_eq_zero {r : ℕ}
    {X Y : Matrix m n ℝ} (hX : X.rank = r) (hY : Y.rank = r) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) {N : Matrix m n ℝ}
    (hN : tangentProjAt Y N = 0) :
    ‖tangentProjAt X N‖ ≤ Real.sqrt 2 * ρ⁻¹ * ‖Y - X‖ * Curvature.specNorm N := by
  classical
  obtain ⟨U, S, V, hU, hV, hS, rfl⟩ := (SVD.rank_eq_iff_exists_factor Y).1 hY
  obtain ⟨U₀, S₀, V₀, hU₀, hV₀, hS₀, rfl⟩ := (SVD.rank_eq_iff_exists_factor X).1 hX
  have hb := WeylSingular.mul_norm_le_norm_toEuclideanLin_core hU₀ hV₀ rfl hρ
    (by simpa using hσ)
  rw [tangentProjAt_eq_tangentProj hU hV hS] at hN
  rw [tangentProjAt_eq_tangentProj hU₀ hV₀ hS₀]
  have h := Curvature.norm_sq_tangentProjMat_le_two_mul_specNorm_sq_of_tangentProjMat_eq_zero
    (S' := S) hρ hU₀ hV₀ hU hV hb (N := N)
    (by rw [Curvature.tangentProjMat_eq_tangentProj]; exact hN)
  rw [Curvature.tangentProjMat_eq_tangentProj] at h
  have h0 : 0 ≤ Real.sqrt 2 * ρ⁻¹ * ‖U * S * Vᵀ - U₀ * S₀ * V₀ᵀ‖ * Curvature.specNorm N :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.2 hρ.le))
      (norm_nonneg _)) (Curvature.specNorm_nonneg N)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).mp (h.trans (le_of_eq ?_))
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  calc 2 * (ρ⁻¹ * ‖U * S * Vᵀ - U₀ * S₀ * V₀ᵀ‖) ^ 2 * Curvature.specNorm N ^ 2
      = Real.sqrt 2 ^ 2 * (ρ⁻¹ * ‖U * S * Vᵀ - U₀ * S₀ * V₀ᵀ‖) ^ 2 *
          Curvature.specNorm N ^ 2 := by rw [h2]
    _ = _ := by ring

end AtPoint

/-! ### Example -/

namespace ProjectorSpectralExamples

open scoped LeanDLRA.Frobenius

/-- **Non-vacuity of `Curvature.norm_sq_tangentProjMat_le_mul_specNorm_sq_of_normal`** with
`Pu = Pv = diag(1, 0)`, `Qu = Qv = diag(0, 1)` and `N = diag(1, 0) ≠ 0`: the hypotheses hold and
the left-hand side is `‖N‖² = 1`. -/
example :
    ‖Curvature.tangentProjMat (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) !![1, 0; 0, 0]
        !![1, 0; 0, 0]‖ ^ 2 ≤
      (‖(!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * (1 - !![0, 0; 0, 1])‖ ^ 2 +
        ‖(1 - (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)) * !![1, 0; 0, 0]‖ ^ 2) *
          Curvature.specNorm (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 := by
  refine Curvature.norm_sq_tangentProjMat_le_mul_specNorm_sq_of_normal ⟨?_, ?_⟩ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end ProjectorSpectralExamples

end LeanDLRA
