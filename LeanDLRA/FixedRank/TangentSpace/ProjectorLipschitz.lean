import LeanDLRA.FixedRank.TangentSpace.Curvature

/-!
# The Lipschitz constant `1` of the tangent projector

For matrices `X`, `Y` of rank `r` with `0 < ρ ≤ σ_{r-1}(X)` the tangent projector satisfies
`‖P(Y) B - P(X) B‖ ≤ 2 ρ⁻¹ ‖Y - X‖ ‖B‖` (`norm_tangentProjAt_sub_le`). This file shows the bound
with the constant `1`,

  `‖P(Y) B - P(X) B‖ ≤ ρ⁻¹ ‖Y - X‖ ‖B‖`,

from the two bounds on normal vectors: `‖P(X) N‖ ≤ ρ⁻¹ ‖Y - X‖ ‖N‖` for `N` normal at `Y`
(`P(Y) N = 0`), and `‖P(Y) N‖ ≤ ρ⁻¹ ‖Y - X‖ ‖N‖` for `N` normal at `X`. All norms of matrices are
Frobenius norms; the lower bound `ρ` is needed at `X` only, and there is no smallness condition on
`‖Y - X‖`. The constant `1` cannot be lowered: the example at the end has
`‖P(X) N‖ = ρ⁻¹ ‖Y - X‖ ‖N‖`. The bounds are shown first for factored matrices `X = U S Vᵀ`,
`Y = U' S' V'ᵀ` with orthonormal columns indexed by any finite type, in the form of
`Curvature.koch_lubich_tangent_frob`, and then for the tangent projector at a matrix of rank `r`.

The global bound in Frobenius norms, without a smallness condition and with the lower bound at one
point only, is Lemma 4.1 of [WeiCaiChanLeung2016] with the constant `2`. The constant `1` equals
the maximal curvature `1/σ_r` of the manifold of rank-`r` matrices (`σ_r` the smallest nonzero
singular value) [FepponLermusiaux2018, Theorem 24], and it is attained.

## Main results

* `LeanDLRA.Curvature.norm_sq_tangentProjMat_le_of_normal`: for orthogonal projectors and `N`
  with `Qu N = 0`, `N Qv = 0`: `‖P N‖² ≤ (b² + (1 - b²) a²) ‖N‖²` if `‖Pu (1 - Qu)‖₂ ≤ a` and
  `‖(1 - Qv) Pv‖₂ ≤ b ≤ 1`.
* `LeanDLRA.Curvature.norm_tangentProjMat_le_of_tangentProjMat_eq_zero`,
  `LeanDLRA.Curvature.norm_tangentProjMat_le_of_tangentProjMat_eq_zero_symm`,
  `LeanDLRA.Curvature.norm_sub_tangentProjMat_le_of_tangentProjMat_eq_self`: the bounds on normal
  vectors and on the normal component of a tangent vector for factored matrices.
* `LeanDLRA.Curvature.norm_tangentProjMat_sub_le_inv_mul`: the Lipschitz bound with the
  constant `1` for factored matrices, under the hypotheses of
  `Curvature.koch_lubich_tangent_frob`.
* `LeanDLRA.norm_tangentProjAt_apply_le_of_tangentProj_eq_zero`,
  `LeanDLRA.norm_tangentProjAt_apply_le_of_tangentProjAt_eq_zero`: `‖P(X) N‖ ≤ ρ⁻¹ ‖Y - X‖ ‖N‖`
  for `N` normal at `Y`.
* `LeanDLRA.norm_tangentProj_apply_le_of_tangentProjAt_eq_zero`:
  `‖P(Y) N‖ ≤ ρ⁻¹ ‖Y - X‖ ‖N‖` for `N` normal at `X`.
* `LeanDLRA.norm_one_sub_tangentProj_apply_le_of_tangentProjAt_eq_self`: for `Z` tangent at `X`,
  `‖(1 - P(Y)) Z‖ ≤ ρ⁻¹ ‖Y - X‖ ‖Z‖`.
* `LeanDLRA.norm_tangentProj_sub_tangentProjAt_le_inv_mul`,
  `LeanDLRA.norm_tangentProjAt_sub_le_inv_mul`: the Lipschitz bound with the constant `1`.

## Implementation notes

Let `Pu`, `Pv` be the projectors onto the column and the row space of `X` and `Qu`, `Qv` those of
`Y`, and let `a = ‖(1 - Qu) Pu‖₂` and `b = ‖Pv (1 - Qv)‖₂` be the sines of the largest principal
angles. For `N` normal at `Y`, `P(X) N = Pu N + (1 - Pu) N Pv` is an orthogonal sum with
`‖Pu N‖ ≤ a ‖N‖` and `‖(1 - Pu) N Pv‖ ≤ b ‖(1 - Pu) N‖`, so that
`‖P(X) N‖² ≤ (b² + (1 - b²) a²) ‖N‖²`. On the other side, with `E = (1 - Qu) X`,
`‖Y - X‖² ≥ ‖X (1 - Qv)‖² + ‖E Qv‖²`, `‖X (1 - Qv)‖ ≥ ρ b`, `‖E Qv‖² ≥ (1 - b²) ‖E‖²` and
`‖E‖ ≥ ρ a`, so that `ρ² (b² + (1 - b²) a²) ≤ ‖Y - X‖²`. For `N` normal at `X` the roles of the
projectors are exchanged with the symmetry of the principal angles between subspaces of equal
dimension (`Curvature.specNorm_compl_mul_symm`). The Lipschitz bound follows from the orthogonal
decomposition `P(Y) B - P(X) B = P(Y) (1 - P(X)) B - (1 - P(Y)) P(X) B`.

## References

* [KochLubich2007, Lemma 4.2]
* [WeiCaiChanLeung2016, Lemma 4.1]
* [FepponLermusiaux2018, Theorem 24]
-/

open Set Filter Matrix
open scoped Topology RealInnerProductSpace

namespace LeanDLRA

namespace Curvature

section NormalVectors

open scoped LeanDLRA.Frobenius

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n]
  [DecidableEq k]

omit [DecidableEq m] in
/-- Pythagoras for a projector on the right: `‖A Q‖² + ‖A (1 - Q)‖² = ‖A‖²`. -/
private theorem norm_sq_mul_add_norm_sq_mul_compl {Q : Matrix n n ℝ} (hQ : IsOrthProjMat Q)
    (A : Matrix m n ℝ) : ‖A * Q‖ ^ 2 + ‖A * (1 - Q)‖ ^ 2 = ‖A‖ ^ 2 := by
  have t : ∀ B : Matrix m n ℝ, ‖Bᵀ‖ = ‖B‖ := fun B => Matrix.frobenius_norm_transpose B
  have hQQ : Q * (1 - Q) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hQ.idem, sub_self]
  have o : (Q * Aᵀ)ᵀ * ((1 - Q) * Aᵀ) = 0 := by
    rw [transpose_mul, hQ.symm, Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQQ, Matrix.zero_mul,
      Matrix.mul_zero]
  have s : Q * Aᵀ + (1 - Q) * Aᵀ = Aᵀ := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    abel
  have e := frob_sq_add_of_orth o
  rw [s] at e
  have e1 : ‖Q * Aᵀ‖ = ‖A * Q‖ := by rw [← t (A * Q), transpose_mul, hQ.symm]
  have e2 : ‖(1 - Q) * Aᵀ‖ = ‖A * (1 - Q)‖ := by
    rw [← t (A * (1 - Q)), transpose_mul, hQ.compl.symm]
  rw [t A, e1, e2] at e
  linarith

/-- **The tangent projector on a normal vector, projector form.** Let `Pu` be an orthogonal
projector and let `N` be normal with respect to `Qu`, `Qv`: `Qu N = 0` and `N Qv = 0`. If
`‖Pu (1 - Qu)‖₂ ≤ a` and `‖(1 - Qv) Pv‖₂ ≤ b` with `0 ≤ b ≤ 1`, then
`‖Pu N + N Pv - Pu N Pv‖² ≤ (b² + (1 - b²) a²) ‖N‖²`. -/
theorem norm_sq_tangentProjMat_le_of_normal {Pu Qu : Matrix m m ℝ} {Pv Qv : Matrix n n ℝ}
    (hPu : IsOrthProjMat Pu) {N : Matrix m n ℝ} (hu : Qu * N = 0) (hv : N * Qv = 0) {a b : ℝ}
    (ha : specNorm (Pu * (1 - Qu)) ≤ a) (hb : specNorm ((1 - Qv) * Pv) ≤ b) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) :
    ‖tangentProjMat Pu Pv N‖ ^ 2 ≤ (b ^ 2 + (1 - b ^ 2) * a ^ 2) * ‖N‖ ^ 2 := by
  classical
  have e : tangentProjMat Pu Pv N = Pu * N + (1 - Pu) * N * Pv := by
    simp only [tangentProjMat, Matrix.sub_mul, Matrix.one_mul]
    abel
  have hPP : Pu * (1 - Pu) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hPu.idem, sub_self]
  have horth : (Pu * N)ᵀ * ((1 - Pu) * N * Pv) = 0 := by
    rw [transpose_mul, hPu.symm, Matrix.mul_assoc Nᵀ, Matrix.mul_assoc (1 - Pu),
      ← Matrix.mul_assoc Pu, hPP, Matrix.zero_mul, Matrix.mul_zero]
  have o1 : (Pu * N)ᵀ * ((1 - Pu) * N) = 0 := by
    rw [transpose_mul, hPu.symm, Matrix.mul_assoc, ← Matrix.mul_assoc Pu, hPP, Matrix.zero_mul,
      Matrix.mul_zero]
  have s1 : Pu * N + (1 - Pu) * N = N := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    abel
  have pyth := frob_sq_add_of_orth o1
  rw [s1] at pyth
  have e1 : Pu * N = Pu * (1 - Qu) * N := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hu, sub_zero]
  have e2 : N * Pv = N * ((1 - Qv) * Pv) := by
    rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hv, sub_zero]
  have e3 : (1 - Pu) * N * Pv = (1 - Pu) * N * ((1 - Qv) * Pv) := by
    rw [Matrix.mul_assoc (1 - Pu) N Pv, e2, Matrix.mul_assoc (1 - Pu) N]
  have h1 : ‖Pu * N‖ ≤ a * ‖N‖ := by
    rw [e1]
    exact (frob_mul_le _ _).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
  have h2 : ‖(1 - Pu) * N * Pv‖ ≤ ‖(1 - Pu) * N‖ * b := by
    rw [e3]
    exact (frob_mul_le' _ _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  rw [e, frob_sq_add_of_orth horth]
  have h1' := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2' := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [mul_pow] at h1' h2'
  have hz : ‖(1 - Pu) * N‖ ^ 2 = ‖N‖ ^ 2 - ‖Pu * N‖ ^ 2 := by linarith
  rw [hz] at h2'
  have hb2 : b ^ 2 ≤ 1 := pow_le_one₀ hb0 hb1
  nlinarith [mul_nonneg (sub_nonneg.2 hb2) (sub_nonneg.2 h1')]

omit [DecidableEq n] in
/-- For `X = U S Vᵀ` with orthonormal `U`, `V` and `ρ ‖v‖ ≤ ‖S v‖`:
`‖M U Uᵀ‖₂ ≤ ρ⁻¹ ‖M X‖` for every `M`. -/
private theorem specNorm_mul_colProj_le {U : Matrix m k ℝ} {S : Matrix k k ℝ} {V : Matrix n k ℝ}
    {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) (M : Matrix m m ℝ) :
    specNorm (M * (U * Uᵀ)) ≤ ρ⁻¹ * ‖M * (U * S * Vᵀ)‖ := by
  classical
  have hdet := isUnit_det_of_bounded_below hρ hS
  rw [← factor_mul_ginv (U := U) (S := S) hV hdet, ← Matrix.mul_assoc]
  calc specNorm (M * (U * S * Vᵀ) * (V * S⁻¹ * Uᵀ))
      ≤ specNorm (M * (U * S * Vᵀ)) * specNorm (V * S⁻¹ * Uᵀ) := specNorm_mul_le _ _
    _ ≤ ‖M * (U * S * Vᵀ)‖ * ρ⁻¹ :=
        mul_le_mul (specNorm_le_frob _) (specNorm_ginv_le hρ hU hV hS) (specNorm_nonneg _)
          (norm_nonneg _)
    _ = ρ⁻¹ * ‖M * (U * S * Vᵀ)‖ := mul_comm _ _

omit [DecidableEq m] in
/-- For `X = U S Vᵀ` with orthonormal `U`, `V` and `ρ ‖v‖ ≤ ‖S v‖`:
`‖V Vᵀ M‖₂ ≤ ρ⁻¹ ‖X M‖` for every `M`. -/
private theorem specNorm_rowProj_mul_le {U : Matrix m k ℝ} {S : Matrix k k ℝ} {V : Matrix n k ℝ}
    {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) (M : Matrix n n ℝ) :
    specNorm (V * Vᵀ * M) ≤ ρ⁻¹ * ‖U * S * Vᵀ * M‖ := by
  classical
  have hdet := isUnit_det_of_bounded_below hρ hS
  rw [← ginv_mul_factor (U := U) (S := S) hU hdet, Matrix.mul_assoc]
  calc specNorm (V * S⁻¹ * Uᵀ * (U * S * Vᵀ * M))
      ≤ specNorm (V * S⁻¹ * Uᵀ) * specNorm (U * S * Vᵀ * M) := specNorm_mul_le _ _
    _ ≤ ρ⁻¹ * ‖U * S * Vᵀ * M‖ :=
        mul_le_mul (specNorm_ginv_le hρ hU hV hS) (specNorm_le_frob _) (specNorm_nonneg _)
          (inv_nonneg.2 hρ.le)

omit [DecidableEq n] in
/-- **Equal-rank symmetry of the principal angles, projector form.** For `U`, `U'` with the same
number of orthonormal columns, `‖(1 - U' U'ᵀ) U Uᵀ‖₂ ≤ c` implies `‖(1 - U Uᵀ) U' U'ᵀ‖₂ ≤ c`. -/
private theorem specNorm_compl_mul_colProj_symm {U U' : Matrix m k ℝ} (hU : Uᵀ * U = 1)
    (hU' : U'ᵀ * U' = 1) {c : ℝ} (hc : 0 ≤ c) (h : specNorm ((1 - U' * U'ᵀ) * (U * Uᵀ)) ≤ c) :
    specNorm ((1 - U * Uᵀ) * (U' * U'ᵀ)) ≤ c := by
  have h1 : specNorm ((1 - U' * U'ᵀ) * U) ≤ c := by
    have e : (1 - U' * U'ᵀ) * U = (1 - U' * U'ᵀ) * (U * Uᵀ) * U := by
      rw [Matrix.mul_assoc (1 - U' * U'ᵀ) (U * Uᵀ) U, Matrix.mul_assoc U, hU, Matrix.mul_one]
    rw [e]
    calc _ ≤ specNorm ((1 - U' * U'ᵀ) * (U * Uᵀ)) * specNorm U := specNorm_mul_le _ _
      _ ≤ c * 1 := mul_le_mul h (specNorm_le_one_of_orthonormal hU) (specNorm_nonneg _) hc
      _ = c := mul_one _
  have h2 := specNorm_compl_mul_symm hU hU' hc h1
  rw [← Matrix.mul_assoc]
  calc _ ≤ specNorm ((1 - U * Uᵀ) * U') * specNorm U'ᵀ := specNorm_mul_le _ _
    _ ≤ c * 1 :=
        mul_le_mul h2 (by rw [specNorm_transpose]; exact specNorm_le_one_of_orthonormal hU')
          (specNorm_nonneg _) hc
    _ = c := mul_one _

omit [DecidableEq m] [DecidableEq n] in
/-- The bounds on normal vectors for factored matrices `X = U S Vᵀ` (`ρ ‖v‖ ≤ ‖S v‖`) and
`Y = U' S' V'ᵀ`: `‖P(X) N‖ ≤ ρ⁻¹ ‖Y - X‖ ‖N‖` for `N` normal at `Y`, and
`‖P(Y) N‖ ≤ ρ⁻¹ ‖Y - X‖ ‖N‖` for `N` normal at `X`. -/
private theorem normal_bounds {U U' : Matrix m k ℝ} {V V' : Matrix n k ℝ}
    {S S' : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) :
    (∀ N : Matrix m n ℝ, U' * U'ᵀ * N = 0 → N * (V' * V'ᵀ) = 0 →
        ‖tangentProj U V N‖ ≤ ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖N‖) ∧
      (∀ N : Matrix m n ℝ, U * Uᵀ * N = 0 → N * (V * Vᵀ) = 0 →
        ‖tangentProj U' V' N‖ ≤ ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖N‖) := by
  classical
  have hP := isOrthProjMat_mul_transpose hU
  have hQ := isOrthProjMat_mul_transpose hV
  have hP' := isOrthProjMat_mul_transpose hU'
  have hQ' := isOrthProjMat_mul_transpose hV'
  have hu : U' * U'ᵀ * (U' * S' * V'ᵀ) = U' * S' * V'ᵀ := colProj_mul_factor hU'
  have hv : U' * S' * V'ᵀ * (V' * V'ᵀ) = U' * S' * V'ᵀ := factor_mul_rowProj hV'
  -- the sines `a`, `b` of the largest principal angles
  obtain ⟨a, haeq⟩ : ∃ a : ℝ, a = specNorm ((1 - U' * U'ᵀ) * (U * Uᵀ)) := ⟨_, rfl⟩
  obtain ⟨b, hbeq⟩ : ∃ b : ℝ, b = specNorm (V * Vᵀ * (1 - V' * V'ᵀ)) := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by
    rw [haeq]
    exact specNorm_nonneg _
  have hb0 : 0 ≤ b := by
    rw [hbeq]
    exact specNorm_nonneg _
  have hb1 : b ≤ 1 := by
    rw [hbeq]
    exact (specNorm_mul_le _ _).trans ((mul_le_mul hQ.specNorm_le_one
      hQ'.compl.specNorm_le_one (specNorm_nonneg _) zero_le_one).trans (mul_one 1).le)
  have hA : a ≤ ρ⁻¹ * ‖(1 - U' * U'ᵀ) * (U * S * Vᵀ)‖ := by
    rw [haeq]
    exact specNorm_mul_colProj_le hρ hU hV hS _
  have hB : b ≤ ρ⁻¹ * ‖U * S * Vᵀ * (1 - V' * V'ᵀ)‖ := by
    rw [hbeq]
    exact specNorm_rowProj_mul_le hρ hU hV hS _
  have hρa : ρ * a ≤ ‖(1 - U' * U'ᵀ) * (U * S * Vᵀ)‖ := by
    have h := mul_le_mul_of_nonneg_left hA hρ.le
    rwa [← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul] at h
  have hρb : ρ * b ≤ ‖U * S * Vᵀ * (1 - V' * V'ᵀ)‖ := by
    have h := mul_le_mul_of_nonneg_left hB hρ.le
    rwa [← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul] at h
  -- the four spectral bounds
  have hA' : specNorm (U * Uᵀ * (1 - U' * U'ᵀ)) ≤ a := by
    rw [← specNorm_transpose, transpose_mul, hP'.compl.symm, hP.symm]
    exact haeq.ge
  have hB' : specNorm ((1 - V' * V'ᵀ) * (V * Vᵀ)) ≤ b := by
    rw [← specNorm_transpose, transpose_mul, hQ.symm, hQ'.compl.symm]
    exact hbeq.ge
  have hC : specNorm (U' * U'ᵀ * (1 - U * Uᵀ)) ≤ a := by
    rw [← specNorm_transpose, transpose_mul, hP.compl.symm, hP'.symm]
    exact specNorm_compl_mul_colProj_symm hU hU' ha0 haeq.ge
  have hD : specNorm ((1 - V * Vᵀ) * (V' * V'ᵀ)) ≤ b :=
    specNorm_compl_mul_colProj_symm hV hV' hb0 hB'
  -- the distance from below
  have r1 := norm_sq_mul_add_norm_sq_mul_compl hQ' (U' * S' * V'ᵀ - U * S * Vᵀ)
  have c1 : (U' * S' * V'ᵀ - U * S * Vᵀ) * (1 - V' * V'ᵀ) =
      -(U * S * Vᵀ * (1 - V' * V'ᵀ)) := by
    rw [← neg_sub (U * S * Vᵀ) (U' * S' * V'ᵀ), Matrix.neg_mul, sub_mul_compl hv]
  have c2 : (1 - U' * U'ᵀ) * ((U' * S' * V'ᵀ - U * S * Vᵀ) * (V' * V'ᵀ)) =
      -((1 - U' * U'ᵀ) * (U * S * Vᵀ) * (V' * V'ᵀ)) := by
    rw [← Matrix.mul_assoc (1 - U' * U'ᵀ) (U' * S' * V'ᵀ - U * S * Vᵀ) (V' * V'ᵀ),
      ← neg_sub (U * S * Vᵀ) (U' * S' * V'ᵀ), Matrix.mul_neg, Matrix.neg_mul, compl_mul_sub hu]
  have c3 : ‖(1 - U' * U'ᵀ) * (U * S * Vᵀ) * (V' * V'ᵀ)‖ ≤
      ‖(U' * S' * V'ᵀ - U * S * Vᵀ) * (V' * V'ᵀ)‖ := by
    have h := hP'.compl.norm_mul_le ((U' * S' * V'ᵀ - U * S * Vᵀ) * (V' * V'ᵀ))
    rwa [c2, norm_neg] at h
  have r2 := norm_sq_mul_add_norm_sq_mul_compl hQ' ((1 - U' * U'ᵀ) * (U * S * Vᵀ))
  have c4 : (1 - U' * U'ᵀ) * (U * S * Vᵀ) * (1 - V' * V'ᵀ) =
      (1 - U' * U'ᵀ) * (U * S * Vᵀ) * (V * Vᵀ * (1 - V' * V'ᵀ)) := by
    rw [← Matrix.mul_assoc ((1 - U' * U'ᵀ) * (U * S * Vᵀ)) (V * Vᵀ),
      Matrix.mul_assoc (1 - U' * U'ᵀ) (U * S * Vᵀ) (V * Vᵀ), factor_mul_rowProj hV]
  have c5 : ‖(1 - U' * U'ᵀ) * (U * S * Vᵀ) * (1 - V' * V'ᵀ)‖ ≤
      ‖(1 - U' * U'ᵀ) * (U * S * Vᵀ)‖ * b := by
    rw [c4, hbeq]
    exact frob_mul_le' _ _
  rw [c1, norm_neg] at r1
  have hq := pow_le_pow_left₀ (mul_nonneg hρ.le hb0) hρb 2
  have hε := pow_le_pow_left₀ (mul_nonneg hρ.le ha0) hρa 2
  have hg := pow_le_pow_left₀ (norm_nonneg _) c5 2
  have hf := pow_le_pow_left₀ (norm_nonneg _) c3 2
  have hb2 : b ^ 2 ≤ 1 := pow_le_one₀ hb0 hb1
  have hdist : ρ ^ 2 * (b ^ 2 + (1 - b ^ 2) * a ^ 2) ≤ ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ ^ 2 := by
    rw [mul_pow] at hq hε hg
    nlinarith [mul_nonneg (sub_nonneg.2 hb2) (sub_nonneg.2 hε)]
  have hdist' : b ^ 2 + (1 - b ^ 2) * a ^ 2 ≤ ρ⁻¹ ^ 2 * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hdist (sq_nonneg ρ⁻¹)
    rwa [← mul_assoc, ← mul_pow ρ⁻¹ ρ 2, inv_mul_cancel₀ hρ.ne', one_pow, one_mul] at h
  have hfin : ∀ N : Matrix m n ℝ, ∀ x : ℝ, 0 ≤ x →
      x ^ 2 ≤ (b ^ 2 + (1 - b ^ 2) * a ^ 2) * ‖N‖ ^ 2 →
      x ≤ ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖N‖ := fun N x hx h => by
    have h0 : 0 ≤ ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖N‖ :=
      mul_nonneg (mul_nonneg (inv_nonneg.2 hρ.le) (norm_nonneg _)) (norm_nonneg _)
    refine (pow_le_pow_iff_left₀ hx h0 two_ne_zero).mp (h.trans ?_)
    rw [mul_pow, mul_pow]
    exact mul_le_mul_of_nonneg_right hdist' (sq_nonneg _)
  refine ⟨fun N h1 h2 => ?_, fun N h1 h2 => ?_⟩
  · have h := norm_sq_tangentProjMat_le_of_normal hP h1 h2 hA' hB' hb0 hb1
    rw [tangentProjMat_eq_tangentProj] at h
    exact hfin N _ (norm_nonneg _) h
  · have h := norm_sq_tangentProjMat_le_of_normal hP' h1 h2 hC hD hb0 hb1
    rw [tangentProjMat_eq_tangentProj] at h
    exact hfin N _ (norm_nonneg _) h

omit [DecidableEq m] [DecidableEq n] in
/-- A matrix in the kernel of `tangentProj U V` is annihilated by `U Uᵀ` from the left and by
`V Vᵀ` from the right. -/
private theorem mul_eq_zero_of_tangentProj_apply_eq_zero {k' : Type*} [Fintype k']
    [DecidableEq k'] {U : Matrix m k' ℝ} {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {N : Matrix m n ℝ} (h : tangentProj U V N = 0) :
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

omit [DecidableEq m] [DecidableEq n] in
/-- **The tangent projector at `X` on a vector normal at `Y`, factor form.** Let `X = U S Vᵀ` and
`Y = U' S' V'ᵀ` with orthonormal columns of `U`, `V`, `U'`, `V'` (any finite index type `k`) and
`ρ ‖v‖ ≤ ‖S v‖`, `ρ > 0`. If `N` is normal at `Y`, `P(Y) N = 0`, then
`‖P(X) N‖ ≤ ρ⁻¹ ‖Y - X‖ ‖N‖`. Nothing is assumed on the core `S'`. The constant `1` is sharp
(equality example at the end of this file). -/
theorem norm_tangentProjMat_le_of_tangentProjMat_eq_zero {U U' : Matrix m k ℝ}
    {V V' : Matrix n k ℝ} {S S' : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) {N : Matrix m n ℝ}
    (hN : tangentProjMat (U' * U'ᵀ) (V' * V'ᵀ) N = 0) :
    ‖tangentProjMat (U * Uᵀ) (V * Vᵀ) N‖ ≤ ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖N‖ := by
  rw [tangentProjMat_eq_tangentProj] at hN ⊢
  obtain ⟨h1, h2⟩ := mul_eq_zero_of_tangentProj_apply_eq_zero hU' hV' hN
  exact (normal_bounds (S' := S') hρ hU hV hU' hV' hS).1 N h1 h2

omit [DecidableEq m] [DecidableEq n] in
/-- **The tangent projector at `Y` on a vector normal at `X`, factor form.** Under the hypotheses
of `norm_tangentProjMat_le_of_tangentProjMat_eq_zero` (`X = U S Vᵀ`, `Y = U' S' V'ᵀ`,
`ρ ‖v‖ ≤ ‖S v‖`), if `N` is normal at `X`, `P(X) N = 0`, then `‖P(Y) N‖ ≤ ρ⁻¹ ‖Y - X‖ ‖N‖`. The
lower bound `ρ` is needed for the core of `X` only. -/
theorem norm_tangentProjMat_le_of_tangentProjMat_eq_zero_symm {U U' : Matrix m k ℝ}
    {V V' : Matrix n k ℝ} {S S' : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) {N : Matrix m n ℝ}
    (hN : tangentProjMat (U * Uᵀ) (V * Vᵀ) N = 0) :
    ‖tangentProjMat (U' * U'ᵀ) (V' * V'ᵀ) N‖ ≤ ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖N‖ := by
  rw [tangentProjMat_eq_tangentProj] at hN ⊢
  obtain ⟨h1, h2⟩ := mul_eq_zero_of_tangentProj_apply_eq_zero hU hV hN
  exact (normal_bounds (S' := S') hρ hU hV hU' hV' hS).2 N h1 h2

omit [DecidableEq m] [DecidableEq n] in
/-- **The normal component at `Y` of a tangent vector at `X`, factor form.** Under the hypotheses
of `norm_tangentProjMat_le_of_tangentProjMat_eq_zero`, if `Z` is tangent at `X`, `P(X) Z = Z`,
then `‖Z - P(Y) Z‖ ≤ ρ⁻¹ ‖Y - X‖ ‖Z‖`. This is the adjoint form of that bound. -/
theorem norm_sub_tangentProjMat_le_of_tangentProjMat_eq_self {U U' : Matrix m k ℝ}
    {V V' : Matrix n k ℝ} {S S' : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) {Z : Matrix m n ℝ}
    (hZ : tangentProjMat (U * Uᵀ) (V * Vᵀ) Z = Z) :
    ‖Z - tangentProjMat (U' * U'ᵀ) (V' * V'ᵀ) Z‖ ≤
      ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖Z‖ := by
  classical
  rw [tangentProjMat_eq_tangentProj] at hZ ⊢
  have hP := isOrthProj_tangentProj (m := m) (n := n) hU' hV'
  have hQ := isOrthProj_tangentProj (m := m) (n := n) hU hV
  obtain ⟨W, hW⟩ : ∃ W : Matrix m n ℝ, W = Z - tangentProj U' V' Z := ⟨_, rfl⟩
  rw [← hW]
  have hPW : tangentProj U' V' W = 0 := by rw [hW, map_sub, hP.idem, sub_self]
  have h1 : ‖tangentProj U V W‖ ≤ ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖W‖ := by
    have h := norm_tangentProjMat_le_of_tangentProjMat_eq_zero (S' := S') hρ hU hV hU' hV' hS
      (N := W) (by rw [tangentProjMat_eq_tangentProj]; exact hPW)
    rwa [tangentProjMat_eq_tangentProj] at h
  have h2 : ⟪Z - tangentProj U' V' Z, W⟫ = ⟪Z, W⟫ := by
    rw [inner_sub_left, hP.symm, hPW, inner_zero_right, sub_zero]
  have h3 : ‖W‖ ^ 2 ≤ ‖Z‖ * ‖tangentProj U V W‖ :=
    calc ‖W‖ ^ 2 = ⟪W, W⟫ := (real_inner_self_eq_norm_sq W).symm
      _ = ⟪Z - tangentProj U' V' Z, W⟫ := by rw [← hW]
      _ = ⟪tangentProj U V Z, W⟫ := by rw [h2, hZ]
      _ = ⟪Z, tangentProj U V W⟫ := hQ.symm Z W
      _ ≤ ‖Z‖ * ‖tangentProj U V W‖ := real_inner_le_norm _ _
  by_contra hlt
  rw [not_le] at hlt
  have hc : 0 ≤ ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ :=
    mul_nonneg (inv_nonneg.2 hρ.le) (norm_nonneg _)
  have hWpos : 0 < ‖W‖ := lt_of_le_of_lt (mul_nonneg hc (norm_nonneg Z)) hlt
  have h4 : ‖Z‖ * ‖tangentProj U V W‖ ≤ ‖Z‖ * (ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖W‖) :=
    mul_le_mul_of_nonneg_left h1 (norm_nonneg Z)
  have h5 : ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖Z‖ * ‖W‖ < ‖W‖ * ‖W‖ :=
    mul_lt_mul_of_pos_right hlt hWpos
  nlinarith

omit [DecidableEq m] [DecidableEq n] in
/-- **Lipschitz bound of the tangent projector with the constant `1`, factor form.** Under the
hypotheses of `koch_lubich_tangent_frob` (`X = U S Vᵀ` and `Y = U' S' V'ᵀ` with orthonormal
columns of `U`, `V`, `U'`, `V'`, any finite index type `k`, and `ρ ‖v‖ ≤ ‖S v‖`, `ρ > 0`), for
every `B`: `‖P(Y) B - P(X) B‖ ≤ ρ⁻¹ ‖Y - X‖ ‖B‖` in Frobenius norms, the bound of
`koch_lubich_tangent_frob` with `1` in place of `2`. With `N = B - P(X) B` and `Z = P(X) B` the
difference is the orthogonal sum of `P(Y) N` and `-(Z - P(Y) Z)`, and `‖B‖² = ‖N‖² + ‖Z‖²`. -/
theorem norm_tangentProjMat_sub_le_inv_mul {U U' : Matrix m k ℝ} {V V' : Matrix n k ℝ}
    {S S' : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) (B : Matrix m n ℝ) :
    ‖tangentProjMat (U' * U'ᵀ) (V' * V'ᵀ) B - tangentProjMat (U * Uᵀ) (V * Vᵀ) B‖ ≤
      ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖B‖ := by
  classical
  have hP := isOrthProj_tangentProj (m := m) (n := n) hU' hV'
  have hQ := isOrthProj_tangentProj (m := m) (n := n) hU hV
  obtain ⟨N, hN⟩ : ∃ N : Matrix m n ℝ, N = B - tangentProj U V B := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix m n ℝ, Z = tangentProj U V B := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ := ⟨_, rfl⟩
  rw [tangentProjMat_eq_tangentProj, tangentProjMat_eq_tangentProj, ← hc]
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact mul_nonneg (inv_nonneg.2 hρ.le) (norm_nonneg _)
  have hQN : tangentProj U V N = 0 := by rw [hN, map_sub, hQ.idem, sub_self]
  have hQZ : tangentProj U V Z = Z := by rw [hZ, hQ.idem]
  have h1 : ‖tangentProj U' V' N‖ ≤ c * ‖N‖ := by
    have h := norm_tangentProjMat_le_of_tangentProjMat_eq_zero_symm (S' := S') hρ hU hV hU' hV'
      hS (N := N) (by rw [tangentProjMat_eq_tangentProj]; exact hQN)
    rwa [tangentProjMat_eq_tangentProj, ← hc] at h
  have h2 : ‖Z - tangentProj U' V' Z‖ ≤ c * ‖Z‖ := by
    have h := norm_sub_tangentProjMat_le_of_tangentProjMat_eq_self (S' := S') hρ hU hV hU' hV'
      hS (Z := Z) (by rw [tangentProjMat_eq_tangentProj]; exact hQZ)
    rwa [tangentProjMat_eq_tangentProj, ← hc] at h
  have e : tangentProj U' V' B - tangentProj U V B =
      tangentProj U' V' N - (Z - tangentProj U' V' Z) := by
    rw [hN, map_sub, ← hZ]
    abel
  have o1 : ⟪tangentProj U' V' N, Z - tangentProj U' V' Z⟫ = 0 := by
    rw [hP.symm, map_sub, hP.idem, sub_self, inner_zero_right]
  have o2 : ⟪N, Z⟫ = 0 := by
    rw [← hQZ, ← hQ.symm, hQN, inner_zero_left]
  have eB : B = N + Z := by
    rw [hN, hZ]
    abel
  have p1 : ‖tangentProj U' V' B - tangentProj U V B‖ ^ 2 =
      ‖tangentProj U' V' N‖ ^ 2 + ‖Z - tangentProj U' V' Z‖ ^ 2 := by
    rw [e, norm_sub_sq_real (tangentProj U' V' N) (Z - tangentProj U' V' Z), o1]
    ring
  have p2 : ‖B‖ ^ 2 = ‖N‖ ^ 2 + ‖Z‖ ^ 2 := by
    rw [eB, norm_add_sq_real N Z, o2]
    ring
  have h1' := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2' := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [mul_pow] at h1' h2'
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc0 (norm_nonneg _))
    two_ne_zero).mp ?_
  rw [p1, mul_pow, p2]
  nlinarith

/-- `koch_lubich_tangent_frob`, restated verbatim, follows from
`norm_tangentProjMat_sub_le_inv_mul`. -/
example {U U' : Matrix m k ℝ} {V V' : Matrix n k ℝ}
    {S S' : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) (B : Matrix m n ℝ) :
    ‖tangentProjMat (U' * U'ᵀ) (V' * V'ᵀ) B - tangentProjMat (U * Uᵀ) (V * Vᵀ) B‖ ≤
      2 * ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖B‖ := by
  have h := norm_tangentProjMat_sub_le_inv_mul (S' := S') hρ hU hV hU' hV' hS B
  have h0 : 0 ≤ ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖B‖ :=
    mul_nonneg (mul_nonneg (inv_nonneg.2 hρ.le) (norm_nonneg _)) (norm_nonneg _)
  linarith

end NormalVectors

end Curvature

section AtPoint

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The bounds of `Curvature.normal_bounds` at a matrix `X` of rank `r` and a factored matrix
`U S Vᵀ`. -/
private theorem normal_bounds_at {r : ℕ} {X : Matrix m n ℝ} (hX : X.rank = r) {ρ : ℝ}
    (hρ : 0 < ρ) (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1))
    {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (S : Matrix (Fin r) (Fin r) ℝ) :
    (∀ N : Matrix m n ℝ, tangentProj U V N = 0 →
        ‖tangentProjAt X N‖ ≤ ρ⁻¹ * ‖U * S * Vᵀ - X‖ * ‖N‖) ∧
      (∀ N : Matrix m n ℝ, tangentProjAt X N = 0 →
        ‖tangentProj U V N‖ ≤ ρ⁻¹ * ‖U * S * Vᵀ - X‖ * ‖N‖) := by
  classical
  obtain ⟨U₀, S₀, V₀, hU₀, hV₀, hS₀, rfl⟩ := (SVD.rank_eq_iff_exists_factor X).1 hX
  have hb := WeylSingular.mul_norm_le_norm_toEuclideanLin_core hU₀ hV₀ rfl hρ
    (by simpa using hσ)
  rw [tangentProjAt_eq_tangentProj hU₀ hV₀ hS₀]
  obtain ⟨hA, hB⟩ := Curvature.normal_bounds (S' := S) hρ hU₀ hV₀ hU hV hb
  exact ⟨fun N hN => hA N (Curvature.mul_eq_zero_of_tangentProj_apply_eq_zero hU hV hN).1
      (Curvature.mul_eq_zero_of_tangentProj_apply_eq_zero hU hV hN).2,
    fun N hN => hB N (Curvature.mul_eq_zero_of_tangentProj_apply_eq_zero hU₀ hV₀ hN).1
      (Curvature.mul_eq_zero_of_tangentProj_apply_eq_zero hU₀ hV₀ hN).2⟩

/-- **The tangent projector at `X` on a vector normal at `Y`.** Let `X` have rank `r` and
`0 < ρ ≤ σ_{r-1}(X)`, let `U`, `V` have `r` orthonormal columns and let `tangentProj U V N = 0`.
For every core `S` (invertible or not): `‖P(X) N‖ ≤ ρ⁻¹ ‖U S Vᵀ - X‖ ‖N‖`. -/
theorem norm_tangentProjAt_apply_le_of_tangentProj_eq_zero {r : ℕ} {X : Matrix m n ℝ}
    (hX : X.rank = r) {ρ : ℝ} (hρ : 0 < ρ) (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1))
    {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (S : Matrix (Fin r) (Fin r) ℝ) {N : Matrix m n ℝ} (hN : tangentProj U V N = 0) :
    ‖tangentProjAt X N‖ ≤ ρ⁻¹ * ‖U * S * Vᵀ - X‖ * ‖N‖ :=
  (normal_bounds_at hX hρ hσ hU hV S).1 N hN

/-- **The tangent projector at `Y` on a vector normal at `X`.** Let `X` have rank `r` and
`0 < ρ ≤ σ_{r-1}(X)`, let `U`, `V` have `r` orthonormal columns and let `P(X) N = 0`. For every
core `S`: `‖tangentProj U V N‖ ≤ ρ⁻¹ ‖U S Vᵀ - X‖ ‖N‖`. The lower bound `ρ` is needed at `X`
only. -/
theorem norm_tangentProj_apply_le_of_tangentProjAt_eq_zero {r : ℕ} {X : Matrix m n ℝ}
    (hX : X.rank = r) {ρ : ℝ} (hρ : 0 < ρ) (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1))
    {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (S : Matrix (Fin r) (Fin r) ℝ) {N : Matrix m n ℝ} (hN : tangentProjAt X N = 0) :
    ‖tangentProj U V N‖ ≤ ρ⁻¹ * ‖U * S * Vᵀ - X‖ * ‖N‖ :=
  (normal_bounds_at hX hρ hσ hU hV S).2 N hN

/-- **The normal component at `Y` of a tangent vector at `X`.** Let `X` have rank `r` and
`0 < ρ ≤ σ_{r-1}(X)`, let `U`, `V` have `r` orthonormal columns and let `Z` be tangent at `X`,
`P(X) Z = Z`. For every core `S`: `‖(1 - tangentProj U V) Z‖ ≤ ρ⁻¹ ‖U S Vᵀ - X‖ ‖Z‖`. This is the
adjoint form of `norm_tangentProjAt_apply_le_of_tangentProj_eq_zero`. -/
theorem norm_one_sub_tangentProj_apply_le_of_tangentProjAt_eq_self {r : ℕ} {X : Matrix m n ℝ}
    (hX : X.rank = r) {ρ : ℝ} (hρ : 0 < ρ) (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1))
    {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (S : Matrix (Fin r) (Fin r) ℝ) {Z : Matrix m n ℝ} (hZ : tangentProjAt X Z = Z) :
    ‖(1 - tangentProj U V) Z‖ ≤ ρ⁻¹ * ‖U * S * Vᵀ - X‖ * ‖Z‖ := by
  classical
  obtain ⟨U₀, S₀, V₀, hU₀, hV₀, hS₀, rfl⟩ := (SVD.rank_eq_iff_exists_factor X).1 hX
  have hb := WeylSingular.mul_norm_le_norm_toEuclideanLin_core hU₀ hV₀ rfl hρ
    (by simpa using hσ)
  rw [tangentProjAt_eq_tangentProj hU₀ hV₀ hS₀] at hZ
  rw [sub_apply, one_apply_eq_self]
  have h := Curvature.norm_sub_tangentProjMat_le_of_tangentProjMat_eq_self (S' := S) hρ hU₀ hV₀
    hU hV hb (Z := Z) (by rw [Curvature.tangentProjMat_eq_tangentProj]; exact hZ)
  rwa [Curvature.tangentProjMat_eq_tangentProj] at h

/-- **Lipschitz bound of the tangent projector with the constant `1`, factored second point.**
Under the hypotheses of `norm_tangentProj_sub_tangentProjAt_le` (`X` of rank `r`,
`0 < ρ ≤ σ_{r-1}(X)`, orthonormal `U`, `V` with `r` columns, any core `S`), for every `B`:
`‖tangentProj U V B - P(X) B‖ ≤ ρ⁻¹ ‖U S Vᵀ - X‖ ‖B‖`. -/
theorem norm_tangentProj_sub_tangentProjAt_le_inv_mul {r : ℕ} {X : Matrix m n ℝ}
    (hX : X.rank = r) {ρ : ℝ} (hρ : 0 < ρ) (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1))
    {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (S : Matrix (Fin r) (Fin r) ℝ) (B : Matrix m n ℝ) :
    ‖tangentProj U V B - tangentProjAt X B‖ ≤ ρ⁻¹ * ‖U * S * Vᵀ - X‖ * ‖B‖ := by
  classical
  obtain ⟨U₀, S₀, V₀, hU₀, hV₀, hS₀, rfl⟩ := (SVD.rank_eq_iff_exists_factor X).1 hX
  have hb := WeylSingular.mul_norm_le_norm_toEuclideanLin_core hU₀ hV₀ rfl hρ
    (by simpa using hσ)
  rw [tangentProjAt_eq_tangentProj hU₀ hV₀ hS₀]
  have h := Curvature.norm_tangentProjMat_sub_le_inv_mul (S' := S) hρ hU₀ hV₀ hU hV hb B
  rwa [Curvature.tangentProjMat_eq_tangentProj, Curvature.tangentProjMat_eq_tangentProj] at h

/-- **The tangent projector at `X` on a vector normal at `Y`, two matrices of rank `r`.** For
`X`, `Y` of rank `r` with `0 < ρ ≤ σ_{r-1}(X)` and `P(Y) N = 0`:
`‖P(X) N‖ ≤ ρ⁻¹ ‖Y - X‖ ‖N‖`. -/
theorem norm_tangentProjAt_apply_le_of_tangentProjAt_eq_zero {r : ℕ} {X Y : Matrix m n ℝ}
    (hX : X.rank = r) (hY : Y.rank = r) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) {N : Matrix m n ℝ}
    (hN : tangentProjAt Y N = 0) :
    ‖tangentProjAt X N‖ ≤ ρ⁻¹ * ‖Y - X‖ * ‖N‖ := by
  obtain ⟨U, S, V, hU, hV, hS, rfl⟩ := (SVD.rank_eq_iff_exists_factor Y).1 hY
  rw [tangentProjAt_eq_tangentProj hU hV hS] at hN
  exact norm_tangentProjAt_apply_le_of_tangentProj_eq_zero hX hρ hσ hU hV S hN

/-- **Lipschitz bound of the tangent projector at a matrix with the constant `1`.** For `X`, `Y`
of rank `r` with `0 < ρ ≤ σ_{r-1}(X)`: `‖P(Y) B - P(X) B‖ ≤ ρ⁻¹ ‖Y - X‖ ‖B‖`. No smallness of
`‖Y - X‖` is needed. -/
theorem norm_tangentProjAt_sub_le_inv_mul {r : ℕ} {X Y : Matrix m n ℝ} (hX : X.rank = r)
    (hY : Y.rank = r) {ρ : ℝ} (hρ : 0 < ρ) (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1))
    (B : Matrix m n ℝ) :
    ‖tangentProjAt Y B - tangentProjAt X B‖ ≤ ρ⁻¹ * ‖Y - X‖ * ‖B‖ := by
  obtain ⟨U, S, V, hU, hV, hS, rfl⟩ := (SVD.rank_eq_iff_exists_factor Y).1 hY
  rw [tangentProjAt_eq_tangentProj hU hV hS]
  exact norm_tangentProj_sub_tangentProjAt_le_inv_mul hX hρ hσ hU hV S B

/-- `norm_tangentProj_sub_tangentProjAt_le`, restated verbatim, follows from
`norm_tangentProj_sub_tangentProjAt_le_inv_mul`. -/
example {r : ℕ} {X : Matrix m n ℝ} (hX : X.rank = r)
    {ρ : ℝ} (hρ : 0 < ρ) (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1))
    {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (S : Matrix (Fin r) (Fin r) ℝ) (B : Matrix m n ℝ) :
    ‖tangentProj U V B - tangentProjAt X B‖ ≤ 2 * ρ⁻¹ * ‖U * S * Vᵀ - X‖ * ‖B‖ := by
  have h := norm_tangentProj_sub_tangentProjAt_le_inv_mul hX hρ hσ hU hV S B
  have h0 : 0 ≤ ρ⁻¹ * ‖U * S * Vᵀ - X‖ * ‖B‖ :=
    mul_nonneg (mul_nonneg (inv_nonneg.2 hρ.le) (norm_nonneg _)) (norm_nonneg _)
  linarith

end AtPoint

/-! ### Examples -/

namespace ProjectorLipschitzExamples

open scoped LeanDLRA.Frobenius

/-- The first unit column of `ℝ²`. -/
local notation "c₁" => (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)

/-- The unit column `v = (3/5, 4/5)ᵀ` of `ℝ²`. -/
local notation "v₁" => (!![3 / 5; 4 / 5] : Matrix (Fin 2) (Fin 1) ℝ)

/-- The matrix `w wᵀ`, `w = (-4/5, 3/5)ᵀ ⊥ v`: a unit normal vector at `c v vᵀ`. -/
local notation "Nᵥ" => (!![16 / 25, -12 / 25; -12 / 25, 9 / 25] : Matrix (Fin 2) (Fin 2) ℝ)

/-- The matrix `e₂ e₂ᵀ`: a unit normal vector at `e₁ e₁ᵀ`. -/
local notation "N₂" => (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)

/-- The core `9/25` of `Y = (9/25) v vᵀ`. -/
local notation "S₉" => ((9 / 25 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))

private theorem c₁_transpose_mul_self : c₁ᵀ * c₁ = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem v₁_transpose_mul_self : v₁ᵀ * v₁ = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.mul_apply, Fin.sum_univ_two]

private theorem smul_c₁_mul (c : ℝ) :
    c • (c₁ * c₁ᵀ) = c₁ * (c • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * c₁ᵀ := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

private theorem isUnit_det_smul_one {c : ℝ} (hc : c ≠ 0) :
    IsUnit (c • (1 : Matrix (Fin 1) (Fin 1) ℝ)).det := by
  rw [det_smul, det_one, mul_one, Fintype.card_fin, pow_one]
  exact isUnit_iff_ne_zero.mpr hc

/-- `X = e₁ e₁ᵀ` has rank `1`. -/
private theorem rank_c₁ : ((1 : ℝ) • (c₁ * c₁ᵀ)).rank = 1 :=
  (SVD.rank_eq_iff_exists_factor _).2 ⟨c₁, (1 : ℝ) • 1, c₁, c₁_transpose_mul_self,
    c₁_transpose_mul_self, isUnit_det_smul_one one_ne_zero, smul_c₁_mul 1⟩

/-- `σ₀(c e₁ e₁ᵀ) ≥ 1` for `c ≥ 1`: the matrix maps `e₁` to `c e₁`. -/
private theorem one_le_singularValues_smul_c₁ {c : ℝ} (hc : 1 ≤ c) :
    (1 : ℝ) ≤ (toEuclideanLin (c • (c₁ * c₁ᵀ))).singularValues (1 - 1) := by
  have hm : c • (c₁ * c₁ᵀ) = !![c, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.vecMul, dotProduct]
  rw [hm, Nat.sub_self, ← EckartYoung.specNorm_eq_singularValues_zero]
  have hs : toEuclideanLin (!![c, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
      (EuclideanSpace.single 0 1) = EuclideanSpace.single 0 c := by
    ext i
    fin_cases i <;> simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  have h := Curvature.norm_toEuclideanLin_le (!![c, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
    (EuclideanSpace.single 0 1)
  rw [hs] at h
  simp at h
  linarith [le_abs_self c]

/-- `σ₀(e₁ e₁ᵀ) ≥ 1`. -/
private theorem one_le_singularValues_c₁ :
    (1 : ℝ) ≤ (toEuclideanLin ((1 : ℝ) • (c₁ * c₁ᵀ))).singularValues (1 - 1) :=
  one_le_singularValues_smul_c₁ le_rfl

/-- The tangent projector at `e₁ e₁ᵀ` is that of the factors `e₁`, `e₁`. -/
private theorem tangentProjAt_c₁ :
    tangentProjAt ((1 : ℝ) • (c₁ * c₁ᵀ)) = tangentProj c₁ c₁ := by
  rw [smul_c₁_mul]
  exact tangentProjAt_eq_tangentProj c₁_transpose_mul_self c₁_transpose_mul_self
    (isUnit_det_smul_one one_ne_zero)

/-- `w wᵀ` is normal at `c v vᵀ`. -/
private theorem tangentProj_v₁_Nᵥ : tangentProj v₁ v₁ Nᵥ = 0 := by
  rw [tangentProj_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

/-- `e₂ e₂ᵀ` is normal at `e₁ e₁ᵀ`. -/
private theorem tangentProjAt_c₁_N₂ : tangentProjAt ((1 : ℝ) • (c₁ * c₁ᵀ)) N₂ = 0 := by
  rw [tangentProjAt_c₁, tangentProj_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

/-- `P(e₁ e₁ᵀ) (w wᵀ)` in entries. -/
private theorem tangentProjAt_c₁_Nᵥ : tangentProjAt ((1 : ℝ) • (c₁ * c₁ᵀ)) Nᵥ =
    !![16 / 25, -12 / 25; -12 / 25, 0] := by
  rw [tangentProjAt_c₁, tangentProj_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

/-- `(9/25) v vᵀ - e₁ e₁ᵀ` in entries. -/
private theorem sub_eq : v₁ * S₉ * v₁ᵀ - (1 : ℝ) • (c₁ * c₁ᵀ) =
    !![-544 / 625, 108 / 625; 108 / 625, 144 / 625] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

/-- **The constant `1` is attained.** `norm_tangentProjAt_apply_le_of_tangentProj_eq_zero` at
`X = e₁ e₁ᵀ` (`2 × 2`, `r = 1`, `ρ = 1`), `Y = (9/25) v vᵀ` with `v = (3/5, 4/5)ᵀ` and
`N = w wᵀ`, `w = (-4/5, 3/5)ᵀ`, holds with equality: `‖P(X) N‖² = ‖Y - X‖² = 544/625` and
`‖N‖ = 1`. A bound `‖P(X) N‖ ≤ c ρ⁻¹ ‖Y - X‖ ‖N‖` for all `X`, `Y`, `N` needs `c ≥ 1`. -/
example :
    ‖tangentProjAt ((1 : ℝ) • (c₁ * c₁ᵀ)) Nᵥ‖ ≤
      1⁻¹ * ‖v₁ * S₉ * v₁ᵀ - (1 : ℝ) • (c₁ * c₁ᵀ)‖ * ‖Nᵥ‖ ∧
    ‖tangentProjAt ((1 : ℝ) • (c₁ * c₁ᵀ)) Nᵥ‖ =
      1⁻¹ * ‖v₁ * S₉ * v₁ᵀ - (1 : ℝ) • (c₁ * c₁ᵀ)‖ * ‖Nᵥ‖ := by
  refine ⟨norm_tangentProjAt_apply_le_of_tangentProj_eq_zero rank_c₁ one_pos
      one_le_singularValues_c₁ v₁_transpose_mul_self v₁_transpose_mul_self S₉ tangentProj_v₁_Nᵥ,
    ?_⟩
  have hN : ‖Nᵥ‖ ^ 2 = 1 := by
    rw [Curvature.frob_sq]
    norm_num [Fin.sum_univ_two]
  have hN1 : ‖Nᵥ‖ = 1 := by
    rw [← pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero, hN, one_pow]
  rw [← pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero, hN1, tangentProjAt_c₁_Nᵥ,
    sub_eq, inv_one, one_mul, mul_one, Curvature.frob_sq, Curvature.frob_sq]
  norm_num [Fin.sum_univ_two]

/-- The bound for `‖P(Y) N‖`, `N` normal at `X`, the bound for the normal component at `Y` of a
tangent vector at `X`, and the Lipschitz bound: `X = Z = e₁ e₁ᵀ`, `Y = (9/25) v vᵀ` (factors `v`,
`v`), `N = e₂ e₂ᵀ`. -/
example (B : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖tangentProj v₁ v₁ N₂‖ ≤ 1⁻¹ * ‖v₁ * S₉ * v₁ᵀ - (1 : ℝ) • (c₁ * c₁ᵀ)‖ * ‖N₂‖ ∧
    ‖(1 - tangentProj v₁ v₁) ((1 : ℝ) • (c₁ * c₁ᵀ))‖ ≤
      1⁻¹ * ‖v₁ * S₉ * v₁ᵀ - (1 : ℝ) • (c₁ * c₁ᵀ)‖ * ‖(1 : ℝ) • (c₁ * c₁ᵀ)‖ ∧
    ‖tangentProj v₁ v₁ B - tangentProjAt ((1 : ℝ) • (c₁ * c₁ᵀ)) B‖ ≤
      1⁻¹ * ‖v₁ * S₉ * v₁ᵀ - (1 : ℝ) • (c₁ * c₁ᵀ)‖ * ‖B‖ :=
  ⟨norm_tangentProj_apply_le_of_tangentProjAt_eq_zero rank_c₁ one_pos
      one_le_singularValues_c₁ v₁_transpose_mul_self v₁_transpose_mul_self S₉
      tangentProjAt_c₁_N₂,
    norm_one_sub_tangentProj_apply_le_of_tangentProjAt_eq_self rank_c₁ one_pos
      one_le_singularValues_c₁ v₁_transpose_mul_self v₁_transpose_mul_self S₉
      (tangentProjAt_self _),
    norm_tangentProj_sub_tangentProjAt_le_inv_mul rank_c₁ one_pos one_le_singularValues_c₁
      v₁_transpose_mul_self v₁_transpose_mul_self S₉ B⟩

/-- The bounds for two matrices of rank `1`: `X = e₁ e₁ᵀ`, `Y = v vᵀ`, `N = w wᵀ`. -/
example (B : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖tangentProjAt ((1 : ℝ) • (c₁ * c₁ᵀ)) Nᵥ‖ ≤
      1⁻¹ * ‖v₁ * v₁ᵀ - (1 : ℝ) • (c₁ * c₁ᵀ)‖ * ‖Nᵥ‖ ∧
    ‖tangentProjAt (v₁ * v₁ᵀ) B - tangentProjAt ((1 : ℝ) • (c₁ * c₁ᵀ)) B‖ ≤
      1⁻¹ * ‖v₁ * v₁ᵀ - (1 : ℝ) • (c₁ * c₁ᵀ)‖ * ‖B‖ := by
  have hfac : v₁ * v₁ᵀ = v₁ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * v₁ᵀ := by rw [Matrix.mul_one]
  have hrank : (v₁ * v₁ᵀ).rank = 1 :=
    (SVD.rank_eq_iff_exists_factor _).2 ⟨v₁, 1, v₁, v₁_transpose_mul_self,
      v₁_transpose_mul_self, by simp, hfac⟩
  have hN : tangentProjAt (v₁ * v₁ᵀ) Nᵥ = 0 := by
    rw [hfac, tangentProjAt_eq_tangentProj v₁_transpose_mul_self v₁_transpose_mul_self
      (by simp)]
    exact tangentProj_v₁_Nᵥ
  exact ⟨norm_tangentProjAt_apply_le_of_tangentProjAt_eq_zero rank_c₁ hrank one_pos
      one_le_singularValues_c₁ hN,
    norm_tangentProjAt_sub_le_inv_mul rank_c₁ hrank one_pos one_le_singularValues_c₁ B⟩

/-- The core `1` of `X = e₁ 1 e₁ᵀ` is bounded below by `1`. -/
private theorem one_mul_norm_le_core (v : EuclideanSpace ℝ (Fin 1)) :
    (1 : ℝ) * ‖v‖ ≤ ‖Matrix.toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ) v‖ := by
  rw [toLpLin_one]
  simp

/-- The four factor-form bounds for `X = e₁ 1 e₁ᵀ` and `Y = v (9/25) vᵀ` (`2 × 2`, one column,
`ρ = 1`): `P(X) N` for the normal vector `N = w wᵀ` at `Y`, `P(Y) N` for the normal vector
`N = e₂ e₂ᵀ` at `X`, the normal component at `Y` of the tangent vector `e₁ e₁ᵀ` at `X`, and the
Lipschitz bound `Curvature.norm_tangentProjMat_sub_le_inv_mul`. -/
example (B : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖Curvature.tangentProjMat (c₁ * c₁ᵀ) (c₁ * c₁ᵀ) Nᵥ‖ ≤
      1⁻¹ * ‖v₁ * S₉ * v₁ᵀ - c₁ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * c₁ᵀ‖ * ‖Nᵥ‖ ∧
    ‖Curvature.tangentProjMat (v₁ * v₁ᵀ) (v₁ * v₁ᵀ) N₂‖ ≤
      1⁻¹ * ‖v₁ * S₉ * v₁ᵀ - c₁ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * c₁ᵀ‖ * ‖N₂‖ ∧
    ‖c₁ * c₁ᵀ - Curvature.tangentProjMat (v₁ * v₁ᵀ) (v₁ * v₁ᵀ) (c₁ * c₁ᵀ)‖ ≤
      1⁻¹ * ‖v₁ * S₉ * v₁ᵀ - c₁ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * c₁ᵀ‖ * ‖c₁ * c₁ᵀ‖ ∧
    ‖Curvature.tangentProjMat (v₁ * v₁ᵀ) (v₁ * v₁ᵀ) B -
        Curvature.tangentProjMat (c₁ * c₁ᵀ) (c₁ * c₁ᵀ) B‖ ≤
      1⁻¹ * ‖v₁ * S₉ * v₁ᵀ - c₁ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * c₁ᵀ‖ * ‖B‖ := by
  have hNv : Curvature.tangentProjMat (v₁ * v₁ᵀ) (v₁ * v₁ᵀ) Nᵥ = 0 := by
    rw [Curvature.tangentProjMat_eq_tangentProj]
    exact tangentProj_v₁_Nᵥ
  have hN2 : Curvature.tangentProjMat (c₁ * c₁ᵀ) (c₁ * c₁ᵀ) N₂ = 0 := by
    rw [Curvature.tangentProjMat_eq_tangentProj, ← tangentProjAt_c₁]
    exact tangentProjAt_c₁_N₂
  have hZ : Curvature.tangentProjMat (c₁ * c₁ᵀ) (c₁ * c₁ᵀ) (c₁ * c₁ᵀ) = c₁ * c₁ᵀ := by
    rw [Curvature.tangentProjMat_eq_tangentProj, tangentProj_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  exact ⟨Curvature.norm_tangentProjMat_le_of_tangentProjMat_eq_zero one_pos
      c₁_transpose_mul_self c₁_transpose_mul_self v₁_transpose_mul_self v₁_transpose_mul_self
      one_mul_norm_le_core hNv,
    Curvature.norm_tangentProjMat_le_of_tangentProjMat_eq_zero_symm one_pos
      c₁_transpose_mul_self c₁_transpose_mul_self v₁_transpose_mul_self v₁_transpose_mul_self
      one_mul_norm_le_core hN2,
    Curvature.norm_sub_tangentProjMat_le_of_tangentProjMat_eq_self one_pos
      c₁_transpose_mul_self c₁_transpose_mul_self v₁_transpose_mul_self v₁_transpose_mul_self
      one_mul_norm_le_core hZ,
    Curvature.norm_tangentProjMat_sub_le_inv_mul one_pos c₁_transpose_mul_self
      c₁_transpose_mul_self v₁_transpose_mul_self v₁_transpose_mul_self one_mul_norm_le_core B⟩

/-- `Curvature.norm_sq_tangentProjMat_le_of_normal` for the projectors `e₁ e₁ᵀ` and `v vᵀ` of
`ℝ²` and the normal vector `w wᵀ` at `v vᵀ`, with the bounds `a = b = 1`. -/
example :
    ‖Curvature.tangentProjMat (c₁ * c₁ᵀ) (c₁ * c₁ᵀ) Nᵥ‖ ^ 2 ≤
      (1 ^ 2 + (1 - 1 ^ 2) * 1 ^ 2) * ‖Nᵥ‖ ^ 2 := by
  have hP := Curvature.isOrthProjMat_mul_transpose c₁_transpose_mul_self
  have hQ := Curvature.isOrthProjMat_mul_transpose v₁_transpose_mul_self
  have hN := Curvature.mul_eq_zero_of_tangentProj_apply_eq_zero v₁_transpose_mul_self
    v₁_transpose_mul_self tangentProj_v₁_Nᵥ
  have ha : Curvature.specNorm (c₁ * c₁ᵀ * (1 - v₁ * v₁ᵀ)) ≤ 1 :=
    (Curvature.specNorm_mul_le _ _).trans ((mul_le_mul hP.specNorm_le_one
      hQ.compl.specNorm_le_one (Curvature.specNorm_nonneg _) zero_le_one).trans (mul_one 1).le)
  have hb : Curvature.specNorm ((1 - v₁ * v₁ᵀ) * (c₁ * c₁ᵀ)) ≤ 1 :=
    (Curvature.specNorm_mul_le _ _).trans ((mul_le_mul hQ.compl.specNorm_le_one
      hP.specNorm_le_one (Curvature.specNorm_nonneg _) zero_le_one).trans (mul_one 1).le)
  exact Curvature.norm_sq_tangentProjMat_le_of_normal hP hN.1 hN.2 ha hb zero_le_one le_rfl

end ProjectorLipschitzExamples

end LeanDLRA
