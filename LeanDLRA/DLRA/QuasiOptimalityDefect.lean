import LeanDLRA.DLRA.QuasiOptimalityNormalVelocity
import LeanDLRA.DLRA.QuasiOptimalitySpeedSharp

/-!
# The defect of a curve of critical points, to first order in the gap

Let `X` be a curve of matrices of rank `r` with `P(X) (A - X) = 0` (critical points of the
distance to `A`; the truncated SVD `X = T_r(A)` is one), with tail `R = A - X`,
`τ = ‖R‖₂ < ρ ≤ σ_{r-1}(X)`. The defect `P(X) Ȧ - Ẋ` is the source of the quasi-optimality bounds
of `LeanDLRA/DLRA/QuasiOptimalityNormalVelocity.lean`; `LeanDLRA/DLRA/QuasiOptimalityTimeLocal.lean`
bounds it by `μ τ/(ρ - τ)` with `μ ≥ ‖Ȧ‖`. This file has its exact form and bounds in terms of
`A`, `Ȧ` that are sharp up to the factor `(ρ + τ)/(ρ - τ)`.

With the Moore–Penrose inverse `X⁺` and the linear map

  `W(Z) = (X⁺)ᵀ Zᵀ R + R Zᵀ (X⁺)ᵀ`

(the Weingarten map of the manifold of rank-`r` matrices at `X` in the normal direction `R`, on
the part of `Z` that turns the column and the row space of `X`):

  `P(X) (Ȧ - Ẋ) = -W(Ẋ)`,
  `‖W(Ȧ)‖ / (1 + τ/ρ) ≤ ‖P(X) Ȧ - Ẋ‖ ≤ ‖W(Ȧ)‖ / (1 - τ/ρ)`,
  `‖W(Z)‖ ≤ (τ/ρ) ‖P(X) Z - Pu Z Pv‖`,

`Pu`, `Pv` the orthogonal projectors onto the column and the row space of `X`. The matrix
`P(X) Z - Pu Z Pv = Pu Z (1 - Pv) + (1 - Pu) Z Pv` consists of the two mixed blocks of `Z`; in
particular `‖P(X) Ȧ - Ẋ‖ ≤ μ τ/(ρ - τ)` holds with `μ` a bound of the mixed blocks of `Ȧ` only.
All norms of matrices are Frobenius norms, except the spectral norm `τ` of the tail.

## Main results

* `Curvature.tangentProjMat_eq_neg_of_transpose_mul_add_eq_zero`,
  `Curvature.norm_transpose_mul_add_le_mul_norm_mixed`: the two algebraic facts, for a generalized
  inverse `G` of `X` and the projectors `Pu = X G`, `Pv = G X`.
* `pinv_mul_eq_rangeProj_transpose`, `specNorm_pinv_le`: `X⁺ X` is the projector onto the row
  space, and `‖X⁺‖₂ ≤ ρ⁻¹` for `X` of rank `r` with `ρ ≤ σ_{r-1}(X)`.
* `tangentProjAt_sub_eq_neg_pinv_transpose_mul_add_of_hasDerivWithinAt`:
  `P(X) (A' - X') = -W(X')`.
* `rangeProj_mul_sub_mul_rangeProj_eq_zero_of_hasDerivWithinAt`: `Pu (A' - X') Pv = 0`.
* `norm_pinv_transpose_mul_add_le_inv_mul_norm_mixed_mul_specNorm`:
  `‖W(Z)‖ ≤ ρ⁻¹ ‖P(X) Z - Pu Z Pv‖ τ`.
* `norm_tangentProjAt_sub_le_inv_mul_norm_mixed_mul_specNorm_of_hasDerivWithinAt`:
  `‖P(X) (A' - X')‖ ≤ ρ⁻¹ ‖P(X) X' - Pu X' Pv‖ τ`.
* `norm_sub_tangentProjAt_le_div_sub_mul_norm_pinv_transpose_mul_add`,
  `norm_pinv_transpose_mul_add_le_one_add_mul_norm_sub_tangentProjAt`: the two-sided bound of the
  defect by `‖W(A')‖`.
* `norm_sub_tangentProjAt_le_div_sub_mul_specNorm_of_norm_mixed_le`: the bound `μ τ/(ρ - τ)` with
  the mixed blocks of `A'`; `norm_tangentProjAt_sub_rangeProj_mul_mul_rangeProj_le`: the mixed
  blocks of `Z` are not larger than `Z`.
* `norm_tangentProjAt_truncation_sub_fderiv_le_div_sub_mul_norm_pinv`: the defect of the curve
  `T_r(A t)` along a solution with a gap.
* `IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_norm_pinv_le`: quasi-optimality
  against the truncated SVD with the normal velocity as growth rate and the source
  `ω ρ/(ρ - τ)`, `ω ≥ ‖W(F(t, A t))‖`.

## Implementation notes

The first-order condition gives `Xᵀ R = 0` and `R Xᵀ = 0` along the curve. Differentiating,
`Ẋᵀ R + Xᵀ Ṙ = 0` and `Ṙ Xᵀ + R Ẋᵀ = 0`, and multiplying by `(X⁺)ᵀ` gives
`Pu Ṙ = -(X⁺)ᵀ Ẋᵀ R` and `Ṙ Pv = -R Ẋᵀ (X⁺)ᵀ`; no derivative of a projector is taken. The two
summands of `W(Z)` have orthogonal column spaces, so their squared norms add, and each sees one
mixed block of `Z`. With `Ẋ = Ȧ - Ṙ` and the fact that `P(X) Ṙ` equals its own mixed blocks,
`P(X) Ṙ = -W(Ȧ) + W(P(X) Ṙ)` with `‖W(P(X) Ṙ)‖ ≤ (τ/ρ) ‖P(X) Ṙ‖`. The rank of `X` is used at the
time `t` only, for `‖X⁺‖₂ ≤ ρ⁻¹`. The `example`s are the rotating projector of
`LeanDLRA/DLRA/QuasiOptimalitySpeedSharp.lean`, for which the defect does not vanish.

## References

* [KochLubich2007]
* [FepponLermusiaux2018]
-/

open Set Finset Matrix Filter
open scoped Topology RealInnerProductSpace

namespace LeanDLRA

namespace Curvature

section FirstOrder

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
/-- **The tangent projector on the derivative of a normal vector.** Let `G` be a generalized
inverse of `X` with the symmetric projectors `Pu = X G`, `Pv = G X`, let `R Pv = 0`, and let `X'`,
`R'` satisfy the differentiated conditions `X'ᵀ R + Xᵀ R' = 0` and `R' Xᵀ + R X'ᵀ = 0`. Then
`Pu R' + R' Pv - Pu R' Pv = -(Gᵀ X'ᵀ R + R X'ᵀ Gᵀ)`, and `Pu R' Pv = 0`. -/
theorem tangentProjMat_eq_neg_of_transpose_mul_add_eq_zero {X X' R R' : Matrix m n ℝ}
    {G : Matrix n m ℝ} {Pu : Matrix m m ℝ} {Pv : Matrix n n ℝ} (hXG : X * G = Pu)
    (hGX : G * X = Pv) (hPu : IsOrthProjMat Pu) (hPv : IsOrthProjMat Pv) (hRv : R * Pv = 0)
    (hd₁ : X'ᵀ * R + Xᵀ * R' = 0) (hd₂ : R' * Xᵀ + R * X'ᵀ = 0) :
    tangentProjMat Pu Pv R' = -(Gᵀ * X'ᵀ * R + R * X'ᵀ * Gᵀ) ∧ Pu * R' * Pv = 0 := by
  have e1 : Xᵀ * R' = -(X'ᵀ * R) := eq_neg_of_add_eq_zero_right hd₁
  have e2 : R' * Xᵀ = -(R * X'ᵀ) := eq_neg_of_add_eq_zero_left hd₂
  have a : Pu * R' = -(Gᵀ * X'ᵀ * R) := by
    calc Pu * R' = (X * G)ᵀ * R' := by rw [hXG, hPu.symm]
      _ = Gᵀ * (Xᵀ * R') := by rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = -(Gᵀ * X'ᵀ * R) := by rw [e1, Matrix.mul_neg, Matrix.mul_assoc]
  have b : R' * Pv = -(R * X'ᵀ * Gᵀ) := by
    calc R' * Pv = R' * (G * X)ᵀ := by rw [hGX, hPv.symm]
      _ = R' * Xᵀ * Gᵀ := by rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = -(R * X'ᵀ * Gᵀ) := by rw [e2, Matrix.neg_mul]
  have c : Pu * R' * Pv = 0 := by
    rw [a, Matrix.neg_mul, Matrix.mul_assoc, hRv, Matrix.mul_zero, neg_zero]
  refine ⟨?_, c⟩
  rw [tangentProjMat, c, sub_zero, a, b, neg_add]

/-- **The Weingarten map sees the mixed blocks only.** Let `G` be a reflexive generalized inverse
of `X` (`G X G = G`) with the orthogonal projectors `Pu = X G`, `Pv = G X` and `‖G‖₂ ≤ c`, and let
`R` be normal: `Pu R = 0`, `R Pv = 0`. For every `Z`, with Frobenius norms,
`‖Gᵀ Zᵀ R + R Zᵀ Gᵀ‖ ≤ c ‖Pu Z + Z Pv - 2 Pu Z Pv‖ ‖R‖₂`; the matrix
`Pu Z + Z Pv - 2 Pu Z Pv = Pu Z (1 - Pv) + (1 - Pu) Z Pv` consists of the mixed blocks of `Z`. -/
theorem norm_transpose_mul_add_le_mul_norm_mixed {X R : Matrix m n ℝ} {G : Matrix n m ℝ}
    {Pu : Matrix m m ℝ} {Pv : Matrix n n ℝ} {c : ℝ} (hXG : X * G = Pu) (hGX : G * X = Pv)
    (hG : G * X * G = G) (hPu : IsOrthProjMat Pu) (hPv : IsOrthProjMat Pv)
    (hc : specNorm G ≤ c) (hRu : Pu * R = 0) (hRv : R * Pv = 0) (Z : Matrix m n ℝ) :
    ‖Gᵀ * Zᵀ * R + R * Zᵀ * Gᵀ‖ ≤
      c * ‖tangentProjMat Pu Pv Z - Pu * Z * Pv‖ * specNorm R := by
  have hc0 : 0 ≤ c := (specNorm_nonneg G).trans hc
  have hPvG : Pv * G = G := by rw [← hGX]; exact hG
  have hGPu : G * Pu = G := by rw [← hXG, ← Matrix.mul_assoc]; exact hG
  have e2 : Gᵀ * Pv = Gᵀ := by
    have h := congrArg Matrix.transpose hPvG
    rwa [Matrix.transpose_mul, hPv.symm] at h
  have e2' : Pu * Gᵀ = Gᵀ := by
    have h := congrArg Matrix.transpose hGPu
    rwa [Matrix.transpose_mul, hPu.symm] at h
  have e3 : (1 - Pu) * R = R := by rw [Matrix.sub_mul, Matrix.one_mul, hRu, sub_zero]
  have e3' : R * (1 - Pv) = R := by rw [Matrix.mul_sub, Matrix.mul_one, hRv, sub_zero]
  have hGR : G * R = 0 := by
    calc G * R = G * Pu * R := by rw [hGPu]
      _ = 0 := by rw [Matrix.mul_assoc, hRu, Matrix.mul_zero]
  have a : Gᵀ * Zᵀ * R = Gᵀ * (((1 - Pu) * Z * Pv)ᵀ * R) := by
    calc Gᵀ * Zᵀ * R = Gᵀ * Pv * Zᵀ * ((1 - Pu) * R) := by rw [e2, e3]
      _ = Gᵀ * (((1 - Pu) * Z * Pv)ᵀ * R) := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul, hPv.symm, hPu.compl.symm]
          simp only [Matrix.mul_assoc]
  have b : R * Zᵀ * Gᵀ = R * (Pu * Z * (1 - Pv))ᵀ * Gᵀ := by
    calc R * Zᵀ * Gᵀ = R * (1 - Pv) * Zᵀ * (Pu * Gᵀ) := by rw [e2', e3']
      _ = R * (Pu * Z * (1 - Pv))ᵀ * Gᵀ := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul, hPv.compl.symm, hPu.symm]
          simp only [Matrix.mul_assoc]
  have o : (Gᵀ * (((1 - Pu) * Z * Pv)ᵀ * R))ᵀ * (R * (Pu * Z * (1 - Pv))ᵀ * Gᵀ) = 0 := by
    rw [Matrix.transpose_mul (Gᵀ), Matrix.transpose_transpose G]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G R, hGR, Matrix.zero_mul, Matrix.mul_zero]
  have hPP : Pu * (1 - Pu) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hPu.idem, sub_self]
  have e : tangentProjMat Pu Pv Z - Pu * Z * Pv = Pu * Z * (1 - Pv) + (1 - Pu) * Z * Pv := by
    simp only [tangentProjMat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  have o' : (Pu * Z * (1 - Pv))ᵀ * ((1 - Pu) * Z * Pv) = 0 := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hPu.symm]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pu (1 - Pu), hPP, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]
  have na : ‖Gᵀ * (((1 - Pu) * Z * Pv)ᵀ * R)‖ ≤ c * ‖(1 - Pu) * Z * Pv‖ * specNorm R := by
    calc ‖Gᵀ * (((1 - Pu) * Z * Pv)ᵀ * R)‖
        ≤ specNorm Gᵀ * ‖((1 - Pu) * Z * Pv)ᵀ * R‖ := frob_mul_le _ _
      _ ≤ c * (‖((1 - Pu) * Z * Pv)ᵀ‖ * specNorm R) :=
          mul_le_mul (by rw [specNorm_transpose]; exact hc) (frob_mul_le' _ _) (norm_nonneg _) hc0
      _ = c * ‖(1 - Pu) * Z * Pv‖ * specNorm R := by
          rw [Matrix.frobenius_norm_transpose, mul_assoc]
  have nb : ‖R * (Pu * Z * (1 - Pv))ᵀ * Gᵀ‖ ≤ c * ‖Pu * Z * (1 - Pv)‖ * specNorm R := by
    calc ‖R * (Pu * Z * (1 - Pv))ᵀ * Gᵀ‖
        ≤ ‖R * (Pu * Z * (1 - Pv))ᵀ‖ * specNorm Gᵀ := frob_mul_le' _ _
      _ ≤ specNorm R * ‖(Pu * Z * (1 - Pv))ᵀ‖ * c :=
          mul_le_mul (frob_mul_le _ _) (by rw [specNorm_transpose]; exact hc)
            (specNorm_nonneg _) (mul_nonneg (specNorm_nonneg _) (norm_nonneg _))
      _ = c * ‖Pu * Z * (1 - Pv)‖ * specNorm R := by
          rw [Matrix.frobenius_norm_transpose]
          ring
  rw [a, b]
  have h0 : 0 ≤ c * ‖tangentProjMat Pu Pv Z - Pu * Z * Pv‖ * specNorm R :=
    mul_nonneg (mul_nonneg hc0 (norm_nonneg _)) (specNorm_nonneg _)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).mp ?_
  rw [frob_sq_add_of_orth o, e, mul_pow, mul_pow, frob_sq_add_of_orth o']
  have na' := pow_le_pow_left₀ (norm_nonneg _) na 2
  have nb' := pow_le_pow_left₀ (norm_nonneg _) nb 2
  rw [mul_pow, mul_pow] at na' nb'
  calc ‖Gᵀ * (((1 - Pu) * Z * Pv)ᵀ * R)‖ ^ 2 + ‖R * (Pu * Z * (1 - Pv))ᵀ * Gᵀ‖ ^ 2
      ≤ c ^ 2 * ‖(1 - Pu) * Z * Pv‖ ^ 2 * specNorm R ^ 2 +
        c ^ 2 * ‖Pu * Z * (1 - Pv)‖ ^ 2 * specNorm R ^ 2 := add_le_add na' nb'
    _ = _ := by ring

end FirstOrder

end Curvature

section AtPoint

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- `X X⁺` is the projector onto the column space of `X`. -/
private theorem mul_pinv_eq_rangeProj (X : Matrix m n ℝ) : X * X.pinv = X.rangeProj :=
  (Matrix.rangeProj_eq_mul_pinv X).symm

/-- `X⁺ X` is the orthogonal projector onto the row space of `X`. -/
theorem pinv_mul_eq_rangeProj_transpose (X : Matrix m n ℝ) :
    X.pinv * X = Xᵀ.rangeProj := by
  classical
  rw [Matrix.rangeProj_eq_mul_pinv Xᵀ, Matrix.pinv_transpose, ← Matrix.transpose_mul,
    Matrix.transpose_pinv_mul]

/-- **The Moore–Penrose inverse of a matrix of rank `r`**: `‖X⁺‖₂ ≤ ρ⁻¹` for `X` of rank `r`
with `0 < ρ ≤ σ_{r-1}(X)`. -/
theorem specNorm_pinv_le [DecidableEq m] {r : ℕ} {X : Matrix m n ℝ} (hX : X.rank = r)
    {ρ : ℝ} (hρ : 0 < ρ) (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) :
    Curvature.specNorm X.pinv ≤ ρ⁻¹ := by
  classical
  obtain ⟨U, S, V, hU, hV, hS, rfl⟩ := (SVD.rank_eq_iff_exists_factor X).1 hX
  have hb := WeylSingular.mul_norm_le_norm_toEuclideanLin_core hU hV rfl hρ
    (by simpa using hσ)
  rw [Matrix.pinv_mul_mul_transpose hU hV hS]
  exact Curvature.specNorm_ginv_le hρ hU hV hb

omit [DecidableEq n] in
/-- A matrix in the kernel of the tangent projector at `Y` is annihilated by the two projectors
of `Y`. -/
private theorem rangeProj_mul_eq_zero_of_tangentProjAt_eq_zero {Y N : Matrix m n ℝ}
    (h : tangentProjAt Y N = 0) : Y.rangeProj * N = 0 ∧ N * Yᵀ.rangeProj = 0 := by
  rw [tangentProjAt_apply] at h
  have hP := Matrix.rangeProj_mul_rangeProj Y
  have hQ := Matrix.rangeProj_mul_rangeProj Yᵀ
  constructor
  · have h1 := congrArg (fun M => Y.rangeProj * M) h
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_zero, ← Matrix.mul_assoc, hP] at h1
    simpa using h1
  · have h1 := congrArg (fun M => M * Yᵀ.rangeProj) h
    simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.zero_mul, Matrix.mul_assoc, hQ] at h1
    simpa using h1

omit [DecidableEq n] in
/-- The first-order condition `P(X) (A - X) = 0` along a curve, differentiated:
`X'ᵀ R + Xᵀ R' = 0` and `R' Xᵀ + R X'ᵀ = 0` with `R = A - X`, `R' = A' - X'`. -/
private theorem transpose_mul_add_eq_zero_of_hasDerivWithinAt {A X : ℝ → Matrix m n ℝ}
    {A' X' : Matrix m n ℝ} {s : Set ℝ} {t : ℝ} (hA : HasDerivWithinAt A A' s t)
    (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s) (hs : (𝓝[s \ {t}] t).NeBot)
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) :
    X'ᵀ * (A t - X t) + (X t)ᵀ * (A' - X') = 0 ∧
      (A' - X') * (X t)ᵀ + (A t - X t) * X'ᵀ = 0 := by
  have hn := fun u hu => rangeProj_mul_eq_zero_of_tangentProjAt_eq_zero (hopt u hu)
  have z1 : ∀ u ∈ s, (X u)ᵀ * (A u - X u) = 0 := fun u hu => by
    have e : (X u)ᵀ = (X u)ᵀ * (X u).rangeProj := by
      conv_lhs =>
        rw [← Matrix.rangeProj_mul_self (X u), Matrix.transpose_mul, Matrix.transpose_rangeProj]
    rw [e, Matrix.mul_assoc, (hn u hu).1, Matrix.mul_zero]
  have z2 : ∀ u ∈ s, (A u - X u) * (X u)ᵀ = 0 := fun u hu => by
    rw [← Matrix.rangeProj_mul_self (X u)ᵀ, ← Matrix.mul_assoc, (hn u hu).2, Matrix.zero_mul]
  have hφ1 : HasDerivWithinAt (fun u => (X u)ᵀ * (A u - X u))
      (X'ᵀ * (A t - X t) + (X t)ᵀ * (A' - X')) s t :=
    Frobenius.hasDerivWithinAt_mul (Frobenius.hasDerivWithinAt_transpose hX) (hA.sub hX)
  have hφ2 : HasDerivWithinAt (fun u => (A u - X u) * (X u)ᵀ)
      ((A' - X') * (X t)ᵀ + (A t - X t) * X'ᵀ) s t :=
    Frobenius.hasDerivWithinAt_mul (hA.sub hX) (Frobenius.hasDerivWithinAt_transpose hX)
  have hg : ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) s t := continuousWithinAt_const
  constructor
  · have h := norm_deriv_le_of_norm_le_norm_sub_mul hφ1 hX hs (z1 t ht) hg (fun u hu => by
      change ‖(X u)ᵀ * (A u - X u)‖ ≤ ‖X u - X t‖ * 0
      rw [z1 u hu, norm_zero, mul_zero])
    rw [mul_zero] at h
    exact norm_le_zero_iff.mp h
  · have h := norm_deriv_le_of_norm_le_norm_sub_mul hφ2 hX hs (z2 t ht) hg (fun u hu => by
      change ‖(A u - X u) * (X u)ᵀ‖ ≤ ‖X u - X t‖ * 0
      rw [z2 u hu, norm_zero, mul_zero])
    rw [mul_zero] at h
    exact norm_le_zero_iff.mp h

/-- **The tangential part of the velocity of the tail is the Weingarten map of the velocity of
the curve.** Let `X` be a curve with `P(X u) (A u - X u) = 0` on `s`, with derivatives `A'`, `X'`
at `t ∈ s` within `s`. Then, with the Moore–Penrose inverse `X⁺ = (X t).pinv` and the tail
`R = A t - X t`, `P(X t) (A' - X') = -((X⁺)ᵀ X'ᵀ R + R X'ᵀ (X⁺)ᵀ)`. No rank is assumed. -/
theorem tangentProjAt_sub_eq_neg_pinv_transpose_mul_add_of_hasDerivWithinAt
    {A X : ℝ → Matrix m n ℝ} {A' X' : Matrix m n ℝ} {s : Set ℝ} {t : ℝ}
    (hA : HasDerivWithinAt A A' s t) (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s)
    (hs : (𝓝[s \ {t}] t).NeBot) (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) :
    tangentProjAt (X t) (A' - X') =
      -((X t).pinvᵀ * X'ᵀ * (A t - X t) + (A t - X t) * X'ᵀ * (X t).pinvᵀ) := by
  obtain ⟨hd₁, hd₂⟩ := transpose_mul_add_eq_zero_of_hasDerivWithinAt hA hX ht hs hopt
  rw [tangentProjAt_apply_eq_tangentProjMat]
  exact (Curvature.tangentProjMat_eq_neg_of_transpose_mul_add_eq_zero
    (mul_pinv_eq_rangeProj (X t)) (pinv_mul_eq_rangeProj_transpose (X t))
    (Matrix.isOrthProjMat_rangeProj _) (Matrix.isOrthProjMat_rangeProj _)
    (rangeProj_mul_eq_zero_of_tangentProjAt_eq_zero (hopt t ht)).2 hd₁ hd₂).1

omit [DecidableEq n] in
/-- **The velocity of the tail has no component in the corner.** Under the hypotheses of
`tangentProjAt_sub_eq_neg_pinv_transpose_mul_add_of_hasDerivWithinAt`, with the projectors `Pu`,
`Pv` onto the column and the row space of `X t`: `Pu (A' - X') Pv = 0`. Hence `P(X t) (A' - X')`
consists of the two mixed blocks of `A' - X'`. -/
theorem rangeProj_mul_sub_mul_rangeProj_eq_zero_of_hasDerivWithinAt
    {A X : ℝ → Matrix m n ℝ} {A' X' : Matrix m n ℝ} {s : Set ℝ} {t : ℝ}
    (hA : HasDerivWithinAt A A' s t) (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s)
    (hs : (𝓝[s \ {t}] t).NeBot) (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) :
    (X t).rangeProj * (A' - X') * (X t)ᵀ.rangeProj = 0 := by
  classical
  obtain ⟨hd₁, hd₂⟩ := transpose_mul_add_eq_zero_of_hasDerivWithinAt hA hX ht hs hopt
  exact (Curvature.tangentProjMat_eq_neg_of_transpose_mul_add_eq_zero
    (mul_pinv_eq_rangeProj (X t)) (pinv_mul_eq_rangeProj_transpose (X t))
    (Matrix.isOrthProjMat_rangeProj _) (Matrix.isOrthProjMat_rangeProj _)
    (rangeProj_mul_eq_zero_of_tangentProjAt_eq_zero (hopt t ht)).2 hd₁ hd₂).2

/-- **The Weingarten map in a normal direction is bounded by the mixed blocks.** Let `X` have rank
`r` with `0 < ρ ≤ σ_{r-1}(X)`, and let `R` be normal at `X`, `P(X) R = 0`. For every `Z`, with the
projectors `Pu`, `Pv` onto the column and the row space of `X`,

  `‖(X⁺)ᵀ Zᵀ R + R Zᵀ (X⁺)ᵀ‖ ≤ ρ⁻¹ ‖P(X) Z - Pu Z Pv‖ ‖R‖₂`.

`P(X) Z - Pu Z Pv = Pu Z (1 - Pv) + (1 - Pu) Z Pv` consists of the two mixed blocks of `Z`. -/
theorem norm_pinv_transpose_mul_add_le_inv_mul_norm_mixed_mul_specNorm {r : ℕ}
    {X R : Matrix m n ℝ} (hX : X.rank = r) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) (hR : tangentProjAt X R = 0)
    (Z : Matrix m n ℝ) :
    ‖X.pinvᵀ * Zᵀ * R + R * Zᵀ * X.pinvᵀ‖ ≤
      ρ⁻¹ * ‖tangentProjAt X Z - X.rangeProj * Z * Xᵀ.rangeProj‖ * Curvature.specNorm R := by
  classical
  obtain ⟨hu, hv⟩ := rangeProj_mul_eq_zero_of_tangentProjAt_eq_zero hR
  rw [tangentProjAt_apply_eq_tangentProjMat]
  exact Curvature.norm_transpose_mul_add_le_mul_norm_mixed (mul_pinv_eq_rangeProj X)
    (pinv_mul_eq_rangeProj_transpose X) (Matrix.pinv_mul_self_mul_pinv X)
    (Matrix.isOrthProjMat_rangeProj _) (Matrix.isOrthProjMat_rangeProj _)
    (specNorm_pinv_le hX hρ hσ) hu hv Z

/-- **Differentiated first-order optimality, mixed blocks of the velocity.** Let `X` be a curve
with `P(X u) (A u - X u) = 0` on `s`, with derivatives `A'`, `X'` at `t ∈ s` within `s`, and let
`X t` have rank `r` with `0 < ρ ≤ σ_{r-1}(X t)`. Then

  `‖P(X t) (A' - X')‖ ≤ ρ⁻¹ ‖P(X t) X' - Pu X' Pv‖ ‖A t - X t‖₂`:

only the mixed blocks of the velocity `X'`, the part that turns the column and the row space of
`X t`, enter. -/
theorem norm_tangentProjAt_sub_le_inv_mul_norm_mixed_mul_specNorm_of_hasDerivWithinAt {r : ℕ}
    {A X : ℝ → Matrix m n ℝ} {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ : ℝ}
    (hA : HasDerivWithinAt A A' s t) (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s)
    (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ) (hrank : (X t).rank = r)
    (hσ : ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) :
    ‖tangentProjAt (X t) (A' - X')‖ ≤
      ρ⁻¹ * ‖tangentProjAt (X t) X' - (X t).rangeProj * X' * (X t)ᵀ.rangeProj‖ *
        Curvature.specNorm (A t - X t) := by
  rw [tangentProjAt_sub_eq_neg_pinv_transpose_mul_add_of_hasDerivWithinAt hA hX ht hs hopt,
    norm_neg]
  exact norm_pinv_transpose_mul_add_le_inv_mul_norm_mixed_mul_specNorm hrank hρ hσ (hopt t ht) X'

/-- The two-sided comparison of `D = P(X t) (A' - X')` with the Weingarten map `W(A')` of `A'`:
`‖D‖ ≤ ‖W(A')‖ + ρ⁻¹ ‖D‖ τ` and `‖W(A')‖ ≤ ρ⁻¹ ‖D‖ τ + ‖D‖`, `τ = ‖A t - X t‖₂`. -/
private theorem norm_tangentProjAt_sub_le_and_norm_pinv_le {r : ℕ} {A X : ℝ → Matrix m n ℝ}
    {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ : ℝ} (hA : HasDerivWithinAt A A' s t)
    (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s) (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ)
    (hrank : (X t).rank = r) (hσ : ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) :
    ‖tangentProjAt (X t) (A' - X')‖ ≤
        ‖(X t).pinvᵀ * A'ᵀ * (A t - X t) + (A t - X t) * A'ᵀ * (X t).pinvᵀ‖ +
          ρ⁻¹ * ‖tangentProjAt (X t) (A' - X')‖ * Curvature.specNorm (A t - X t) ∧
      ‖(X t).pinvᵀ * A'ᵀ * (A t - X t) + (A t - X t) * A'ᵀ * (X t).pinvᵀ‖ ≤
        ρ⁻¹ * ‖tangentProjAt (X t) (A' - X')‖ * Curvature.specNorm (A t - X t) +
          ‖tangentProjAt (X t) (A' - X')‖ := by
  have hD := tangentProjAt_sub_eq_neg_pinv_transpose_mul_add_of_hasDerivWithinAt hA hX ht hs hopt
  have hz := rangeProj_mul_sub_mul_rangeProj_eq_zero_of_hasDerivWithinAt hA hX ht hs hopt
  have hK := norm_pinv_transpose_mul_add_le_inv_mul_norm_mixed_mul_specNorm hrank hρ hσ
    (hopt t ht) (A' - X')
  rw [hz, sub_zero] at hK
  have hlin : (X t).pinvᵀ * X'ᵀ * (A t - X t) + (A t - X t) * X'ᵀ * (X t).pinvᵀ =
      ((X t).pinvᵀ * A'ᵀ * (A t - X t) + (A t - X t) * A'ᵀ * (X t).pinvᵀ) -
        ((X t).pinvᵀ * (A' - X')ᵀ * (A t - X t) +
          (A t - X t) * (A' - X')ᵀ * (X t).pinvᵀ) := by
    simp only [Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [hlin, neg_sub] at hD
  have key : ∀ (D K W : Matrix m n ℝ) (c : ℝ), D = K - W → ‖K‖ ≤ c →
      ‖D‖ ≤ ‖W‖ + c ∧ ‖W‖ ≤ c + ‖D‖ := by
    rintro D K W c rfl hK
    refine ⟨by linarith [norm_sub_le K W], ?_⟩
    have h2 := norm_sub_le K (K - W)
    rw [sub_sub_cancel] at h2
    linarith
  exact key _ _ _ _ hD hK

/-- **The defect of a curve of critical points is at most the Weingarten map of the data
velocity, up to the factor `ρ/(ρ - τ)`.** Let `X u` have rank `r` with
`P(X u) (A u - X u) = 0` and `0 < ρ₀ ≤ σ_{r-1}(X u)` on `s`, with derivatives `A'`, `X'` at
`t ∈ s` within `s`. If `τ = ‖X t - A t‖₂ < ρ ≤ σ_{r-1}(X t)`, then with `X⁺ = (X t).pinv` and
the tail `R = A t - X t`

  `‖X' - P(X t) A'‖ ≤ ρ/(ρ - τ) ‖(X⁺)ᵀ A'ᵀ R + R A'ᵀ (X⁺)ᵀ‖`.

The right-hand side has the data `A t`, `A'` only. The lower bound `ρ₀` on `s` is used for the
tangency of `X'` only. -/
theorem norm_sub_tangentProjAt_le_div_sub_mul_norm_pinv_transpose_mul_add {r : ℕ}
    {A X : ℝ → Matrix m n ℝ} {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ₀ ρ : ℝ}
    (hA : HasDerivWithinAt A A' s t) (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s)
    (hs : (𝓝[s \ {t}] t).NeBot) (hρ₀ : 0 < ρ₀) (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ₀ : ∀ u ∈ s, ρ₀ ≤ (toEuclideanLin (X u)).singularValues (r - 1))
    (hσ : ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0)
    (hd : Curvature.specNorm (X t - A t) < ρ) :
    ‖X' - tangentProjAt (X t) A'‖ ≤ ρ / (ρ - Curvature.specNorm (X t - A t)) *
      ‖(X t).pinvᵀ * A'ᵀ * (A t - X t) + (A t - X t) * A'ᵀ * (X t).pinvᵀ‖ := by
  have hτ0 := Curvature.specNorm_nonneg (X t - A t)
  have hρ : 0 < ρ := hτ0.trans_lt hd
  have htan : tangentProjAt (X t) X' = X' := tangentProjAt_eq_self_iff.mpr
    (mem_tangentSpaceAt_of_hasDerivWithinAt hX ht hs hρ₀ hrank hσ₀)
  have e' : X' - tangentProjAt (X t) A' = -tangentProjAt (X t) (A' - X') := by
    rw [map_sub, htan]
    abel
  have h := (norm_tangentProjAt_sub_le_and_norm_pinv_le hA hX ht hs hρ (hrank t ht) hσ hopt).1
  rw [Curvature.specNorm_sub_comm] at h
  rw [e', norm_neg, div_mul_eq_mul_div, le_div_iff₀ (sub_pos.2 hd)]
  have h' := mul_le_mul_of_nonneg_left h hρ.le
  have e2 : ρ * (ρ⁻¹ * ‖tangentProjAt (X t) (A' - X')‖ * Curvature.specNorm (X t - A t)) =
      ‖tangentProjAt (X t) (A' - X')‖ * Curvature.specNorm (X t - A t) := by
    field_simp
  rw [mul_add, e2] at h'
  linarith

/-- **The Weingarten map of the data velocity is at most the defect, up to the factor
`1 + τ/ρ`.** Under the hypotheses of
`norm_sub_tangentProjAt_le_div_sub_mul_norm_pinv_transpose_mul_add`, with `0 < ρ ≤ σ_{r-1}(X t)`
and `τ = ‖X t - A t‖₂` (no gap condition):

  `‖(X⁺)ᵀ A'ᵀ R + R A'ᵀ (X⁺)ᵀ‖ ≤ (1 + ρ⁻¹ τ) ‖X' - P(X t) A'‖`.

Together the two bounds determine the defect up to the factor `(ρ + τ)/(ρ - τ)`. -/
theorem norm_pinv_transpose_mul_add_le_one_add_mul_norm_sub_tangentProjAt {r : ℕ}
    {A X : ℝ → Matrix m n ℝ} {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ₀ ρ : ℝ}
    (hA : HasDerivWithinAt A A' s t) (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s)
    (hs : (𝓝[s \ {t}] t).NeBot) (hρ₀ : 0 < ρ₀) (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ₀ : ∀ u ∈ s, ρ₀ ≤ (toEuclideanLin (X u)).singularValues (r - 1)) (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) :
    ‖(X t).pinvᵀ * A'ᵀ * (A t - X t) + (A t - X t) * A'ᵀ * (X t).pinvᵀ‖ ≤
      (1 + ρ⁻¹ * Curvature.specNorm (X t - A t)) * ‖X' - tangentProjAt (X t) A'‖ := by
  have htan : tangentProjAt (X t) X' = X' := tangentProjAt_eq_self_iff.mpr
    (mem_tangentSpaceAt_of_hasDerivWithinAt hX ht hs hρ₀ hrank hσ₀)
  have e' : X' - tangentProjAt (X t) A' = -tangentProjAt (X t) (A' - X') := by
    rw [map_sub, htan]
    abel
  have h := (norm_tangentProjAt_sub_le_and_norm_pinv_le hA hX ht hs hρ (hrank t ht) hσ hopt).2
  rw [Curvature.specNorm_sub_comm] at h
  rw [e', norm_neg]
  calc _ ≤ _ := h
    _ = _ := by ring

omit [DecidableEq n] in
/-- The mixed blocks of `Z` at `X` are not larger than `Z`:
`‖P(X) Z - Pu Z Pv‖ ≤ ‖Z‖`, with the projectors `Pu`, `Pv` onto the column and the row space of
`X`. -/
theorem norm_tangentProjAt_sub_rangeProj_mul_mul_rangeProj_le (X Z : Matrix m n ℝ) :
    ‖tangentProjAt X Z - X.rangeProj * Z * Xᵀ.rangeProj‖ ≤ ‖Z‖ := by
  classical
  have hPu := Matrix.isOrthProjMat_rangeProj X
  have hPv := Matrix.isOrthProjMat_rangeProj Xᵀ
  have hPP : X.rangeProj * (1 - X.rangeProj) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hPu.idem, sub_self]
  have e : tangentProjAt X Z - X.rangeProj * Z * Xᵀ.rangeProj =
      X.rangeProj * Z * (1 - Xᵀ.rangeProj) + (1 - X.rangeProj) * Z * Xᵀ.rangeProj := by
    rw [tangentProjAt_apply]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  have o : (X.rangeProj * Z * (1 - Xᵀ.rangeProj))ᵀ * ((1 - X.rangeProj) * Z * Xᵀ.rangeProj) =
      0 := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hPu.symm]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc X.rangeProj (1 - X.rangeProj), hPP, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.mul_zero]
  have o' : (X.rangeProj * Z)ᵀ * ((1 - X.rangeProj) * Z) = 0 := by
    rw [Matrix.transpose_mul, hPu.symm, Matrix.mul_assoc, ← Matrix.mul_assoc X.rangeProj, hPP,
      Matrix.zero_mul, Matrix.mul_zero]
  have s : X.rangeProj * Z + (1 - X.rangeProj) * Z = Z := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    abel
  have p := Curvature.frob_sq_add_of_orth o'
  rw [s] at p
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (hPv.compl.norm_mul_le' (X.rangeProj * Z)) 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (hPv.norm_mul_le' ((1 - X.rangeProj) * Z)) 2
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [e, Curvature.frob_sq_add_of_orth o]
  linarith

/-- **The velocity of a curve of critical points, mixed blocks of the data velocity.** Under the
hypotheses of `norm_sub_tangentProjAt_le_div_sub_mul_specNorm`, with `μ` a bound of the mixed
blocks of `A'` at `X t` only, `‖P(X t) A' - Pu A' Pv‖ ≤ μ`:

  `‖X' - P(X t) A'‖ ≤ μ / (ρ - ‖X t - A t‖₂) ‖X t - A t‖₂`.

By `norm_tangentProjAt_sub_rangeProj_mul_mul_rangeProj_le` every `μ ≥ ‖A'‖` is admissible. -/
theorem norm_sub_tangentProjAt_le_div_sub_mul_specNorm_of_norm_mixed_le {r : ℕ}
    {A X : ℝ → Matrix m n ℝ} {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ₀ ρ μ : ℝ}
    (hA : HasDerivWithinAt A A' s t) (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s)
    (hs : (𝓝[s \ {t}] t).NeBot) (hρ₀ : 0 < ρ₀) (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ₀ : ∀ u ∈ s, ρ₀ ≤ (toEuclideanLin (X u)).singularValues (r - 1))
    (hσ : ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0)
    (hμ : ‖tangentProjAt (X t) A' - (X t).rangeProj * A' * (X t)ᵀ.rangeProj‖ ≤ μ)
    (hd : Curvature.specNorm (X t - A t) < ρ) :
    ‖X' - tangentProjAt (X t) A'‖ ≤
      μ / (ρ - Curvature.specNorm (X t - A t)) * Curvature.specNorm (X t - A t) := by
  have hτ0 := Curvature.specNorm_nonneg (X t - A t)
  have hρ : 0 < ρ := hτ0.trans_lt hd
  have hgap : 0 < ρ - Curvature.specNorm (X t - A t) := sub_pos.2 hd
  have h1 := norm_sub_tangentProjAt_le_div_sub_mul_norm_pinv_transpose_mul_add hA hX ht hs hρ₀
    hrank hσ₀ hσ hopt hd
  have h2 := norm_pinv_transpose_mul_add_le_inv_mul_norm_mixed_mul_specNorm (hrank t ht) hρ hσ
    (hopt t ht) A'
  rw [Curvature.specNorm_sub_comm] at h2
  have h3 : ρ⁻¹ * ‖tangentProjAt (X t) A' - (X t).rangeProj * A' * (X t)ᵀ.rangeProj‖ *
      Curvature.specNorm (X t - A t) ≤ ρ⁻¹ * μ * Curvature.specNorm (X t - A t) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hμ (inv_nonneg.2 hρ.le)) hτ0
  have hρne := hρ.ne'
  have hgne := hgap.ne'
  calc ‖X' - tangentProjAt (X t) A'‖ ≤ ρ / (ρ - Curvature.specNorm (X t - A t)) *
        ‖(X t).pinvᵀ * A'ᵀ * (A t - X t) + (A t - X t) * A'ᵀ * (X t).pinvᵀ‖ := h1
    _ ≤ ρ / (ρ - Curvature.specNorm (X t - A t)) *
        (ρ⁻¹ * μ * Curvature.specNorm (X t - A t)) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) (div_nonneg hρ.le hgap.le)
    _ = μ / (ρ - Curvature.specNorm (X t - A t)) * Curvature.specNorm (X t - A t) := by
        field_simp

end AtPoint

section Truncation

open scoped LeanDLRA.Frobenius
open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **The defect of the truncated SVD along a solution.** Let `A` solve `Ȧ = F(t, A)` on `[a, b]`
with the gap `σ_r(A t) < σ_{r-1}(A t)`, and `T = T_r(A s)` at a time `s ∈ [a, b)`, with the tail
`R = A s - T`. Then, with `ρ = σ_{r-1}(A s)`, `τ = σ_r(A s)` and `Z = F(s, A s)`,

  `‖P(T) Z - d/ds T_r(A s)‖ ≤ ρ/(ρ - τ) ‖(T⁺)ᵀ Zᵀ R + R Zᵀ (T⁺)ᵀ‖`. -/
theorem norm_tangentProjAt_truncation_sub_fderiv_le_div_sub_mul_norm_pinv {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {a b : ℝ}
    (hA : ODESolution F A a b)
    (hgap : ∀ t ∈ Icc a b, (toEuclideanLin (A t)).singularValues r <
      (toEuclideanLin (A t)).singularValues (r - 1)) {s : ℝ} (hsb : s ∈ Ico a b) :
    ‖tangentProjAt (truncation (A s) r) (F s (A s)) -
        fderiv ℝ (fun B => truncation B r) (A s) (F s (A s))‖ ≤
      (toEuclideanLin (A s)).singularValues (r - 1) /
          ((toEuclideanLin (A s)).singularValues (r - 1) -
            (toEuclideanLin (A s)).singularValues r) *
        ‖(truncation (A s) r).pinvᵀ * (F s (A s))ᵀ * (A s - truncation (A s) r) +
          (A s - truncation (A s) r) * (F s (A s))ᵀ * (truncation (A s) r).pinvᵀ‖ := by
  have hsI := Ico_subset_Icc_self hsb
  have hab : a ≤ b := hsI.1.trans hsI.2
  have hr : 0 < r := Nat.pos_of_ne_zero fun h0 => by
    subst h0
    exact lt_irrefl _ (hgap a ⟨le_rfl, hab⟩)
  have hσpos : ∀ u ∈ Icc a b, 0 < (toEuclideanLin (A u)).singularValues (r - 1) :=
    fun u hu => ((toEuclideanLin (A u)).singularValues_nonneg r).trans_lt (hgap u hu)
  have he : Curvature.specNorm (truncation (A s) r - A s) =
      (toEuclideanLin (A s)).singularValues r := by
    rw [Curvature.specNorm_sub_comm, specNorm_sub_truncation]
  have hσc' : Continuous fun Z : Matrix m n ℝ => (toEuclideanLin Z).singularValues (r - 1) :=
    (LipschitzWith.of_dist_le_mul (K := 1) fun Z Z' => by
      rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
      exact WeylSingular.abs_singularValues_sub_le_frobenius Z Z' (r - 1)).continuous
  have hρc : ContinuousOn (fun t => (toEuclideanLin (A t)).singularValues (r - 1)) (Icc a b) :=
    hσc'.comp_continuousOn hA.cont
  obtain ⟨t₁, ht₁, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) hρc
  have hρ₀ : ∀ u ∈ Icc a b, (toEuclideanLin (A t₁)).singularValues (r - 1) ≤
      (toEuclideanLin (A u)).singularValues (r - 1) := fun u hu => isMinOn_iff.1 hmin u hu
  have hsub : Icc s b ⊆ Icc a b := Icc_subset_Icc_left hsb.1
  have hne : (𝓝[Icc s b \ {s}] s).NeBot := by
    rw [Icc_sdiff_left]
    exact left_nhdsWithin_Ioc_neBot hsb.2
  have hX : HasDerivWithinAt (fun t => truncation (A t) r)
      (fderiv ℝ (fun B => truncation B r) (A s) (F s (A s))) (Ici s) s :=
    hasDerivWithinAt_truncation (hA.deriv s hsb) (hgap s hsI)
  have hbest := norm_sub_tangentProjAt_le_div_sub_mul_norm_pinv_transpose_mul_add (A := A)
    (X := fun t => truncation (A t) r)
    ((hA.deriv s hsb).mono (Icc_subset_Ici_self : Icc s b ⊆ Ici s))
    (hX.mono (Icc_subset_Ici_self : Icc s b ⊆ Ici s)) ⟨le_rfl, hsb.2.le⟩ hne
    (hσpos t₁ ht₁) (fun u hu => rank_truncation_of_le_singularValues (hσpos u (hsub hu)) le_rfl)
    (fun u hu => (hρ₀ u (hsub hu)).trans
      (le_singularValues_truncation hr (hσpos u (hsub hu)) le_rfl))
    (le_singularValues_truncation hr (hσpos s hsI) le_rfl)
    (fun u _ => tangentProjAt_truncation_sub_eq_zero _ _)
    (by
      rw [he]
      exact hgap s hsI)
  rw [he] at hbest
  rw [norm_sub_rev]
  exact hbest

/-- **Quasi-optimality against the truncated SVD: normal velocity as growth rate, Weingarten map
of the field as source.** Let `F` be `L`-Lipschitz, `A` a solution of `Ȧ = F(t, A)` on `[a, b]`
with the gap `σ_r(A t) < σ_{r-1}(A t)`, and `Y` a DLRA solution of rank `r`. Write
`T t = T_r(A t)`, `R t = A t - T t`, `Z t = F(t, A t)`, `ρ = σ_{r-1}(A ·)`, `τ = σ_r(A ·)`. Let
`μ`, `ν`, `ω`, `ε` be continuous with `‖Z t‖ ≤ μ t`, `‖(1 - P(T t)) Z t‖ ≤ ν t`,

  `‖(T⁺)ᵀ Zᵀ R + R Zᵀ (T⁺)ᵀ‖ ≤ ω t`

and `0 ≤ ε t < ρ t`. With `k = L + ν/ρ + ν/(ρ - ε) + μ ε/ρ²`: if `‖Y a - T a‖ ≤ δ` and

  `e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖T s - A s‖ + ρ s/(ρ s - τ s) ω s) ds < ε t`   on `[a, b]`,

then `‖Y t - T t‖` is at most the left-hand side on `[a, b]`. By
`norm_pinv_transpose_mul_add_le_inv_mul_norm_mixed_mul_specNorm` the function
`ω = μ' τ/ρ` is admissible for every `μ'` that bounds the mixed blocks of `Z` at `T`, and the
source is at most `(1 + τ/ρ) ρ/(ρ - τ)` times the defect of the curve `T`
(`norm_pinv_transpose_mul_add_le_one_add_mul_norm_sub_tangentProjAt`). -/
theorem IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_norm_pinv_le {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A Y : ℝ → Matrix m n ℝ} {μ ν ω ε : ℝ → ℝ}
    {a b L δ : ℝ} (hY : IsDLRASolution r F Y a b) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hA : ODESolution F A a b) (hμc : ContinuousOn μ (Icc a b))
    (hνc : ContinuousOn ν (Icc a b)) (hωc : ContinuousOn ω (Icc a b))
    (hεc : ContinuousOn ε (Icc a b)) (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ t)
    (hν : ∀ t ∈ Ico a b,
      ‖F t (A t) - tangentProjAt (truncation (A t) r) (F t (A t))‖ ≤ ν t)
    (hω : ∀ t ∈ Ico a b,
      ‖(truncation (A t) r).pinvᵀ * (F t (A t))ᵀ * (A t - truncation (A t) r) +
        (A t - truncation (A t) r) * (F t (A t))ᵀ * (truncation (A t) r).pinvᵀ‖ ≤ ω t)
    (hgap : ∀ t ∈ Icc a b, (toEuclideanLin (A t)).singularValues r <
      (toEuclideanLin (A t)).singularValues (r - 1))
    (hε0 : ∀ t ∈ Icc a b, 0 ≤ ε t)
    (hερ : ∀ t ∈ Icc a b, ε t < (toEuclideanLin (A t)).singularValues (r - 1))
    (hδ : ‖Y a - truncation (A a) r‖ ≤ δ)
    (hB : ∀ t ∈ Icc a b,
      Real.exp (∫ u in a..t, (L + ν u / (toEuclideanLin (A u)).singularValues (r - 1) +
        ν u / ((toEuclideanLin (A u)).singularValues (r - 1) - ε u) +
        μ u * ε u / (toEuclideanLin (A u)).singularValues (r - 1) ^ 2)) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (L + ν u / (toEuclideanLin (A u)).singularValues (r - 1) +
          ν u / ((toEuclideanLin (A u)).singularValues (r - 1) - ε u) +
          μ u * ε u / (toEuclideanLin (A u)).singularValues (r - 1) ^ 2)) *
          (L * ‖truncation (A s) r - A s‖ +
            (toEuclideanLin (A s)).singularValues (r - 1) /
              ((toEuclideanLin (A s)).singularValues (r - 1) -
                (toEuclideanLin (A s)).singularValues r) * ω s) < ε t) :
    ∀ t ∈ Icc a b, ‖Y t - truncation (A t) r‖ ≤
      Real.exp (∫ u in a..t, (L + ν u / (toEuclideanLin (A u)).singularValues (r - 1) +
        ν u / ((toEuclideanLin (A u)).singularValues (r - 1) - ε u) +
        μ u * ε u / (toEuclideanLin (A u)).singularValues (r - 1) ^ 2)) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (L + ν u / (toEuclideanLin (A u)).singularValues (r - 1) +
          ν u / ((toEuclideanLin (A u)).singularValues (r - 1) - ε u) +
          μ u * ε u / (toEuclideanLin (A u)).singularValues (r - 1) ^ 2)) *
          (L * ‖truncation (A s) r - A s‖ +
            (toEuclideanLin (A s)).singularValues (r - 1) /
              ((toEuclideanLin (A s)).singularValues (r - 1) -
                (toEuclideanLin (A s)).singularValues r) * ω s) := by
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  have hr : 0 < r := Nat.pos_of_ne_zero fun h0 => by
    subst h0
    exact lt_irrefl _ (hgap a ⟨le_rfl, hab⟩)
  have hσpos : ∀ s ∈ Icc a b, 0 < (toEuclideanLin (A s)).singularValues (r - 1) :=
    fun s hs => ((toEuclideanLin (A s)).singularValues_nonneg r).trans_lt (hgap s hs)
  have hσc' : ∀ i : ℕ, Continuous fun Z : Matrix m n ℝ => (toEuclideanLin Z).singularValues i :=
    fun i => (LipschitzWith.of_dist_le_mul (K := 1) fun Z Z' => by
      rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
      exact WeylSingular.abs_singularValues_sub_le_frobenius Z Z' i).continuous
  have hσc : ∀ i : ℕ, ContinuousOn (fun t => (toEuclideanLin (A t)).singularValues i)
      (Icc a b) := fun i => (hσc' i).comp_continuousOn hA.cont
  have hρc := hσc (r - 1)
  have hτc := hσc r
  refine hY.norm_sub_le_integral_exp_integral_of_integral_lt (A := A)
    (X := fun t => truncation (A t) r)
    (X' := fun t => fderiv ℝ (fun B => truncation B r) (A t) (F t (A t)))
    (ρ := fun t => (toEuclideanLin (A t)).singularValues (r - 1)) (μ := μ) (ν := ν)
    (d := fun s => (toEuclideanLin (A s)).singularValues (r - 1) /
      ((toEuclideanLin (A s)).singularValues (r - 1) -
        (toEuclideanLin (A s)).singularValues r) * ω s)
    (ε := ε) hL hF hA.cont hρc hμc hνc
    ((hρc.div (hρc.sub hτc) fun u hu => (sub_pos.2 (hgap u hu)).ne').mul hωc) hεc
    (fun s hs => (continuousAt_truncation (hgap s hs)).comp_continuousWithinAt (hA.cont s hs))
    (fun s hs => hasDerivWithinAt_truncation (hA.deriv s hs) (hgap s (Ico_subset_Icc_self hs)))
    (fun s hs => rank_truncation_of_le_singularValues (hσpos s hs) le_rfl)
    (fun s hs => le_singularValues_truncation hr (hσpos s hs) le_rfl) hμ hν
    (fun s hsb => ?_) hε0 hερ hδ hB t ht
  have hsI := Ico_subset_Icc_self hsb
  exact (norm_tangentProjAt_truncation_sub_fderiv_le_div_sub_mul_norm_pinv hA hgap hsb).trans
    (mul_le_mul_of_nonneg_left (hω s hsb)
      (div_nonneg (hσpos s hsI).le (sub_pos.2 (hgap s hsI)).le))

end Truncation

/-! ### Examples -/

namespace QuasiOptimalityDefectExamples

open scoped LeanDLRA.Frobenius
open QuasiOptimalityExamples QuasiOptimalitySpeedExample

/-- **Non-vacuity of the bounds of the defect at one time** for the rotating projector
`X t = u(t) u(t)ᵀ` of rank one and the data `A t = θ • 1 + (1 - θ) • X t`, `0 ≤ θ < 1`
(`r = 1`, `ρ₀ = ρ = 1`, tail `‖A t - X t‖₂ = θ`, defect `θ Ẋ ≠ 0` for `θ > 0`): the Weingarten
formula, the vanishing corner, the bound by the mixed blocks of `Ẋ`, the two-sided bound by the
Weingarten map of `Ȧ`, and the bound by the mixed blocks of `Ȧ`. The algebraic lemmas
`Curvature.tangentProjMat_eq_neg_of_transpose_mul_add_eq_zero` and
`Curvature.norm_transpose_mul_add_le_mul_norm_mixed` are applied in their proofs with the
Moore–Penrose inverse of `X t`. -/
example {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1) (t : ℝ) :
    tangentProjAt (rotProj t) ((1 - θ) • rotProjDeriv t - rotProjDeriv t) =
        -((rotProj t).pinvᵀ * (rotProjDeriv t)ᵀ * (rotData θ t - rotProj t) +
          (rotData θ t - rotProj t) * (rotProjDeriv t)ᵀ * (rotProj t).pinvᵀ) ∧
      (rotProj t).rangeProj * ((1 - θ) • rotProjDeriv t - rotProjDeriv t) *
        (rotProj t)ᵀ.rangeProj = 0 ∧
      ‖tangentProjAt (rotProj t) ((1 - θ) • rotProjDeriv t - rotProjDeriv t)‖ ≤
        (1 : ℝ)⁻¹ * ‖tangentProjAt (rotProj t) (rotProjDeriv t) -
          (rotProj t).rangeProj * rotProjDeriv t * (rotProj t)ᵀ.rangeProj‖ *
          Curvature.specNorm (rotData θ t - rotProj t) ∧
      ‖rotProjDeriv t - tangentProjAt (rotProj t) ((1 - θ) • rotProjDeriv t)‖ ≤
        1 / (1 - Curvature.specNorm (rotProj t - rotData θ t)) *
          ‖(rotProj t).pinvᵀ * ((1 - θ) • rotProjDeriv t)ᵀ * (rotData θ t - rotProj t) +
            (rotData θ t - rotProj t) * ((1 - θ) • rotProjDeriv t)ᵀ * (rotProj t).pinvᵀ‖ ∧
      ‖(rotProj t).pinvᵀ * ((1 - θ) • rotProjDeriv t)ᵀ * (rotData θ t - rotProj t) +
          (rotData θ t - rotProj t) * ((1 - θ) • rotProjDeriv t)ᵀ * (rotProj t).pinvᵀ‖ ≤
        (1 + (1 : ℝ)⁻¹ * Curvature.specNorm (rotProj t - rotData θ t)) *
          ‖rotProjDeriv t - tangentProjAt (rotProj t) ((1 - θ) • rotProjDeriv t)‖ ∧
      ‖rotProjDeriv t - tangentProjAt (rotProj t) ((1 - θ) • rotProjDeriv t)‖ ≤
        ‖tangentProjAt (rotProj t) ((1 - θ) • rotProjDeriv t) -
          (rotProj t).rangeProj * ((1 - θ) • rotProjDeriv t) * (rotProj t)ᵀ.rangeProj‖ /
          (1 - Curvature.specNorm (rotProj t - rotData θ t)) *
          Curvature.specNorm (rotProj t - rotData θ t) := by
  obtain ⟨hA, hX, hs, hr, hσ, ho, -, -⟩ := hypotheses hθ0 hθ t
  have hd : Curvature.specNorm (rotProj t - rotData θ t) < 1 := by
    rw [Curvature.specNorm_sub_comm, specNorm_rotData_sub hθ0 hθ]
    exact hθ
  exact ⟨tangentProjAt_sub_eq_neg_pinv_transpose_mul_add_of_hasDerivWithinAt hA hX (mem_univ t)
      hs ho,
    rangeProj_mul_sub_mul_rangeProj_eq_zero_of_hasDerivWithinAt hA hX (mem_univ t) hs ho,
    norm_tangentProjAt_sub_le_inv_mul_norm_mixed_mul_specNorm_of_hasDerivWithinAt hA hX
      (mem_univ t) hs one_pos (hr t (mem_univ t)) (hσ t (mem_univ t)) ho,
    norm_sub_tangentProjAt_le_div_sub_mul_norm_pinv_transpose_mul_add hA hX (mem_univ t) hs
      one_pos hr hσ (hσ t (mem_univ t)) ho hd,
    norm_pinv_transpose_mul_add_le_one_add_mul_norm_sub_tangentProjAt hA hX (mem_univ t) hs
      one_pos hr hσ one_pos (hσ t (mem_univ t)) ho,
    norm_sub_tangentProjAt_le_div_sub_mul_specNorm_of_norm_mixed_le hA hX (mem_univ t) hs
      one_pos hr hσ (hσ t (mem_univ t)) ho le_rfl hd⟩

/-- **Non-vacuity of `norm_pinv_transpose_mul_add_le_inv_mul_norm_mixed_mul_specNorm`** at the
rotating projector `X = u(t) u(t)ᵀ` with the normal vector `R = A t - X t = θ (1 - X)` and every
`Z`. -/
example {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1) (t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖(rotProj t).pinvᵀ * Zᵀ * (rotData θ t - rotProj t) +
        (rotData θ t - rotProj t) * Zᵀ * (rotProj t).pinvᵀ‖ ≤
      (1 : ℝ)⁻¹ * ‖tangentProjAt (rotProj t) Z -
        (rotProj t).rangeProj * Z * (rotProj t)ᵀ.rangeProj‖ *
        Curvature.specNorm (rotData θ t - rotProj t) := by
  obtain ⟨-, -, -, hr, hσ, ho, -, -⟩ := hypotheses hθ0 hθ t
  exact norm_pinv_transpose_mul_add_le_inv_mul_norm_mixed_mul_specNorm (hr t (mem_univ t))
    one_pos (hσ t (mem_univ t)) (ho t (mem_univ t)) Z

/-- **Non-vacuity of `specNorm_pinv_le`** at the rotating projector (`r = 1`, `ρ = 1`). -/
example (t : ℝ) : Curvature.specNorm (rotProj t).pinv ≤ (1 : ℝ)⁻¹ :=
  specNorm_pinv_le (rank_rotProj t) one_pos (one_le_singularValues_rotProj t)

/-- `norm_sub_tangentProjAt_le_div_sub_mul_specNorm`, restated verbatim, follows from the bound
with the mixed blocks: `‖P(X t) A' - Pu A' Pv‖ ≤ ‖A'‖ ≤ μ`. -/
example {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] {r : ℕ} {A X : ℝ → Matrix m n ℝ}
    {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ₀ ρ μ : ℝ} (hA : HasDerivWithinAt A A' s t)
    (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s) (hs : (𝓝[s \ {t}] t).NeBot) (hρ₀ : 0 < ρ₀)
    (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ₀ : ∀ u ∈ s, ρ₀ ≤ (toEuclideanLin (X u)).singularValues (r - 1))
    (hσ : ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) (hμ : ‖A'‖ ≤ μ)
    (hd : Curvature.specNorm (X t - A t) < ρ) :
    ‖X' - tangentProjAt (X t) A'‖ ≤
      μ / (ρ - Curvature.specNorm (X t - A t)) * Curvature.specNorm (X t - A t) :=
  norm_sub_tangentProjAt_le_div_sub_mul_specNorm_of_norm_mixed_le hA hX ht hs hρ₀ hrank hσ₀ hσ
    hopt ((norm_tangentProjAt_sub_rangeProj_mul_mul_rangeProj_le _ _).trans hμ) hd

/-- The normal part `diag(0, 1/16)` of the examples. -/
local notation "N₁₆" => (!![0, 0; 0, 1 / 16] : Matrix (Fin 2) (Fin 2) ℝ)

/-- The derivative of `A t = (1 + t) e₁ e₁ᵀ + diag(0, 1/16)` is `e₁ e₁ᵀ`. -/
theorem hasDerivAt_smul_e₁_add_const (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) (e₁ * e₁ᵀ) t := by
  simpa using (hasDerivAt_smul_e₁ 1 t).add_const N₁₆

/-- `σ₁(A t) ≤ 1/16` for `A t = (1 + t) e₁ e₁ᵀ + diag(0, 1/16)`, `t ≥ 0`. -/
theorem singularValues_one_smul_e₁_add_le {t : ℝ} (ht : 0 ≤ t) :
    (toEuclideanLin ((1 + t) • (e₁ * e₁ᵀ) + N₁₆)).singularValues 1 ≤ 1 / 16 := by
  rw [← EckartYoung.specNorm_sub_truncation, truncation_smul_e₁_add ht,
    Curvature.specNorm_sub_comm]
  exact (Curvature.specNorm_le_frob _).trans (norm_smul_e₁_sub_add_le t)

/-- `Y t = (1 + t) e₁ e₁ᵀ` is a DLRA solution of rank `1` for the field `F = e₁ e₁ᵀ`. -/
theorem isDLRASolution_smul_e₁_tangent :
    IsDLRASolution 1 (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ)
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) 0 1 := by
  refine ⟨⟨fun s _ => (hasDerivAt_smul_e₁ 1 s).continuousAt.continuousWithinAt,
    fun s hs => ?_⟩, fun t ht => rank_smul_e₁ (ne_of_gt (by linarith [ht.1]))⟩
  have h := (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt (s := Ici s)
  convert h using 1
  exact tangentProjAt_smul_e₁_apply (ne_of_gt (by linarith [hs.1]))

/-- For `|k| ≤ 1/2` and `|g| ≤ 1/15` on `[0, ∞)` and `t ∈ [0, 1]`:
`∫₀ᵗ e^{∫ₛᵗ k} g(s) ds ≤ e^{1/2} / 15 < 1/2`. -/
theorem integral_exp_integral_mul_lt_half {k g : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hk : ∀ u, 0 ≤ u → |k u| ≤ 1 / 2)
    (hg : ∀ s, 0 ≤ s → |g s| ≤ 1 / 15) :
    ∫ s in (0 : ℝ)..t, Real.exp (∫ u in s..t, k u) * g s < 1 / 2 := by
  have h1 : ∀ s ∈ Set.uIoc (0 : ℝ) t, ‖Real.exp (∫ u in s..t, k u) * g s‖ ≤ 1 / 5 := by
    intro s hs
    rw [uIoc_of_le ht.1] at hs
    have hI : ∫ u in s..t, k u ≤ 1 / 2 := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t)
        (C := 1 / 2) (f := k) (fun u hu => by
          rw [uIoc_of_le hs.2] at hu
          rw [Real.norm_eq_abs]
          exact hk u (hs.1.le.trans hu.1.le))
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hs.2)] at h
      linarith [le_abs_self (∫ u in s..t, k u), hs.1, ht.2]
    have he : Real.exp (∫ u in s..t, k u) ≤ 3 := by
      have h2 := Real.exp_le_exp.2 (hI.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
      linarith [Real.exp_one_lt_d9]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul he (hg s hs.1.le) (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const h1
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at h
  linarith [le_abs_self (∫ s in (0 : ℝ)..t, Real.exp (∫ u in s..t, k u) * g s), ht.2]

/-- **Non-vacuity of `IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_norm_pinv_le`
and of `norm_tangentProjAt_truncation_sub_fderiv_le_div_sub_mul_norm_pinv`** for `2 × 2` matrices,
`r = 1`, `A t = (1 + t) e₁ e₁ᵀ + diag(0, 1/16)` on `[0, 1]` and `F = e₁ e₁ᵀ` (`L = 0`, `μ = 1`,
`ν = 0`, `ω = 1/16`, `ε = 1/2`, `δ = 0`): the gap is `σ₁(A t) ≤ 1/16 < 1 ≤ σ₀(A t)`,
`T₁(A t) = (1 + t) e₁ e₁ᵀ` differs from `A t` and is the DLRA solution `Y`, the rate is at most
`1/2` and the source `ρ/(ρ - τ) ω` at most `1/15`, so that the bound stays below `ε`. -/
example : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(1 + t) • (e₁ * e₁ᵀ) - EckartYoung.truncation ((1 + t) • (e₁ * e₁ᵀ) + N₁₆) 1‖ ≤
      Real.exp (∫ u in (0 : ℝ)..t,
        ((0 : ℝ) + 0 / (toEuclideanLin ((1 + u) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1) +
          0 / ((toEuclideanLin ((1 + u) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1) -
            1 / 2) +
          1 * (1 / 2) /
            (toEuclideanLin ((1 + u) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1) ^ 2)) * 0 +
        ∫ s in (0 : ℝ)..t, Real.exp (∫ u in s..t,
        ((0 : ℝ) + 0 / (toEuclideanLin ((1 + u) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1) +
          0 / ((toEuclideanLin ((1 + u) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1) -
            1 / 2) +
          1 * (1 / 2) /
            (toEuclideanLin ((1 + u) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1) ^ 2)) *
          (0 * ‖EckartYoung.truncation ((1 + s) • (e₁ * e₁ᵀ) + N₁₆) 1 -
              ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)‖ +
            (toEuclideanLin ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1) /
              ((toEuclideanLin ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1) -
                (toEuclideanLin ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)).singularValues 1) * (1 / 16)) :=
  isDLRASolution_smul_e₁_tangent.norm_sub_truncation_le_integral_exp_integral_of_norm_pinv_le
    (A := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) (μ := fun _ => 1) (ν := fun _ => 0)
    (ω := fun _ => 1 / 16) (ε := fun _ => 1 / 2) le_rfl (fun _ _ _ => by simp)
    ⟨fun s _ => (hasDerivAt_smul_e₁_add_const s).continuousAt.continuousWithinAt,
      fun s _ => (hasDerivAt_smul_e₁_add_const s).hasDerivWithinAt⟩
    continuousOn_const continuousOn_const continuousOn_const continuousOn_const
    (fun _ _ => norm_e₁_mul_le)
    (fun t ht => by
      rw [truncation_smul_e₁_add ht.1,
        tangentProjAt_smul_e₁_apply (ne_of_gt (by linarith [ht.1])), sub_self, norm_zero])
    (fun t ht => by
      have t1 : e₁ᵀ * N₁₆ = 0 := by
        ext i j
        fin_cases i
        fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      have t2 : N₁₆ * e₁ = 0 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      have h1 : (e₁ * e₁ᵀ)ᵀ * N₁₆ = 0 := by
        rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, t1,
          Matrix.mul_zero]
      have h2 : N₁₆ * (e₁ * e₁ᵀ)ᵀ = 0 := by
        rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, t2,
          Matrix.zero_mul]
      rw [truncation_smul_e₁_add ht.1, add_sub_cancel_left,
        Matrix.mul_assoc _ (e₁ * e₁ᵀ)ᵀ N₁₆, h1, Matrix.mul_zero, h2, Matrix.zero_mul, add_zero,
        norm_zero]
      norm_num)
    (fun t ht => (singularValues_one_smul_e₁_add_le ht.1).trans_lt
      (lt_of_lt_of_le (by norm_num) (one_le_singularValues_smul_e₁_add ht.1)))
    (fun _ _ => by norm_num)
    (fun t ht => lt_of_lt_of_le (by norm_num) (one_le_singularValues_smul_e₁_add ht.1))
    (by rw [truncation_smul_e₁_add le_rfl, sub_self, norm_zero])
    (fun t ht => by
      rw [mul_zero, zero_add]
      refine integral_exp_integral_mul_lt_half ht (fun u hu => ?_) (fun s hs => ?_)
      · have h1 := one_le_singularValues_smul_e₁_add hu
        simp only [zero_div, add_zero, zero_add, one_mul]
        rw [abs_of_nonneg (by positivity)]
        exact div_le_self (by norm_num) (one_le_pow₀ h1)
      · have h1 := one_le_singularValues_smul_e₁_add hs
        have h2 := singularValues_one_smul_e₁_add_le hs
        have h0 := (toEuclideanLin ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)).singularValues_nonneg 1
        rw [zero_mul, zero_add, abs_of_nonneg
          (mul_nonneg (div_nonneg (by linarith) (by linarith)) (by norm_num)),
          div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        linarith)

end QuasiOptimalityDefectExamples

end LeanDLRA
