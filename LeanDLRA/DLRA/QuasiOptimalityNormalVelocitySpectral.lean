import LeanDLRA.DLRA.QuasiOptimalityDefect

/-!
# Quasi-optimality with the spectral norm of the normal velocity, and the a posteriori form

`LeanDLRA/DLRA/QuasiOptimalityNormalVelocity.lean` bounds the growth of the error `Y - X` of a
DLRA solution `Y` against a curve `X` of rank-`r` matrices through

  `⟪Y - X, (P(Y) - P(X)) Z⟫ ≤ (‖(1 - P(Y)) Z‖/σ_{r-1}(X) + ‖(1 - P(X)) Z‖/σ_{r-1}(Y)) ‖Y - X‖²`

with Frobenius norms of the normal components of `Z = F(t, A t)`. This file has the same bound
with their spectral norms and the factor `(1 + s)/2`,

  `⟪Y - X, (P(Y) - P(X)) Z⟫ ≤ ((1 + s₁)/2 ‖(1 - P(Y)) Z‖₂/σ_{r-1}(X) +
      (1 + s₂)/2 ‖(1 - P(X)) Z‖₂/σ_{r-1}(Y)) ‖Y - X‖²`,

where `s₁ = ‖Pu (1 - Qu)‖₂ ‖Pv (1 - Qv)‖₂` and `s₂ = ‖Qu (1 - Pu)‖₂ ‖Qv (1 - Pv)‖₂` are the
products of the sines of the largest angles between the column spaces and between the row spaces
of `X` and `Y` (`Pu`, `Pv` the projectors of `X`, `Qu`, `Qv` those of `Y`);
`s₁ ≤ min(1, (‖Y - X‖/σ_{r-1}(X))²)` and `s₂ ≤ min(1, (‖Y - X‖/σ_{r-1}(Y))²)`. To first order in
`‖Y - X‖` the growth rate is therefore `‖(1 - P(X)) Z‖₂/σ_{r-1}(X)`, half of the rate of the
Frobenius form and with the spectral norm.

## Main results

* `norm_mul_norm_le_one_add_div_two_mul_norm_sq`: in an inner product space, if `⟪x, k⟫ = ‖k‖²`,
  `⟪x, l⟫ = ‖l‖²` and `⟪k, l⟫ ≤ c ‖k‖ ‖l‖`, then `‖k‖ ‖l‖ ≤ (1 + c)/2 ‖x‖²`.
* `Curvature.inner_normal_le_mul_mul_specNorm`: the normal component of `Y` at `X`, tested with
  `N`, for a reflexive generalized inverse of `Y`.
* `inner_sub_tangentProjAt_le_inv_mul_specNorm`,
  `specNorm_rangeProj_mul_mul_specNorm_rangeProj_mul_le_min`: the same at a matrix of rank `r`,
  and the bound of the product of sines.
* `inner_sub_tangentProjAt_sub_le_half_mul_specNorm`,
  `inner_sub_tangentProjAt_sub_le_of_norm_sub_le_of_specNorm_le`: the two tangent projectors
  tested with the difference; data at both points, and data at `X` with a radius `ε ≥ ‖Y - X‖`.
* `IsDLRASolution.norm_sub_le_integral_exp_integral_of_inner_tangentProjAt_sub_le`: the error
  bound for any rate `κ` with `⟪Y - X, (P(Y) - P(X)) F(t, A t)⟫ ≤ κ ‖Y - X‖²`.
* `IsDLRASolution.norm_sub_le_integral_exp_integral_of_specNorm_sub_tangentProjAt_le`: the
  a posteriori form, with `σ_{r-1}(Y t)`, `‖(1 - P(Y t)) F(t, A t)‖₂` and the sines measured on
  the computed solution `Y`; no smallness condition.
* `IsDLRASolution.norm_sub_le_integral_exp_integral_of_norm_sub_le_of_specNorm_le`,
  `IsDLRASolution.norm_sub_le_integral_exp_integral_of_integral_lt_of_specNorm_le`: the a priori
  forms (tube `‖Y - X‖ ≤ ε`, and the bound itself below `ε`).
* `IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_specNorm_le`:
  against the truncated SVD, with the source of `LeanDLRA/DLRA/QuasiOptimalityDefect.lean`.

## Implementation notes

The normal component of `Y` at `X` is `(1 - Pu) Y (1 - Pv) = K Y⁺ L` with
`K = (1 - Pu) (Y - X) Qv` and `L = Qu (Y - X) (1 - Pv)` (`Curvature.normal_eq_curvature`), so
`⟪K Y⁺ L, N⟫ = ⟪Y⁺ L, Kᵀ N⟫ ≤ ‖Y⁺‖₂ ‖L‖ ‖K‖ ‖N‖₂`: no nuclear norm is needed. `K` and `L` are
images of `Y - X` under two orthogonal projectors of the Frobenius space whose product has norm
`s₂`; hence `‖K‖² + ‖L‖² ≤ (1 + s₂) ‖Y - X‖²` and `‖K‖ ‖L‖ ≤ (1 + s₂)/2 ‖Y - X‖²`. The general
theorem does not assume a rank for `X`: the rank enters only through the rate `κ`. With `s = 1`
and `‖·‖₂ ≤ ‖·‖` the a posteriori form contains the pointwise bound
`inner_sub_tangentProjAt_sub_le_norm_sq_mul` of the Frobenius form.

## References

* [KochLubich2007]
* [FepponLermusiaux2018]
-/

open Set Finset Matrix Filter
open scoped Topology RealInnerProductSpace

namespace LeanDLRA

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Two components of a vector whose inner product is small.** If `⟪x, k⟫ = ‖k‖²`,
`⟪x, l⟫ = ‖l‖²` (as for the images `k`, `l` of `x` under two orthogonal projectors) and
`⟪k, l⟫ ≤ c ‖k‖ ‖l‖` with `c ≥ 0`, then `‖k‖² + ‖l‖² ≤ (1 + c) ‖x‖²`, and in particular
`‖k‖ ‖l‖ ≤ (1 + c)/2 ‖x‖²`. -/
theorem norm_mul_norm_le_one_add_div_two_mul_norm_sq {x k l : E} {c : ℝ} (hc : 0 ≤ c)
    (hk : ⟪x, k⟫ = ‖k‖ ^ 2) (hl : ⟪x, l⟫ = ‖l‖ ^ 2) (hkl : ⟪k, l⟫ ≤ c * ‖k‖ * ‖l‖) :
    ‖k‖ * ‖l‖ ≤ (1 + c) / 2 * ‖x‖ ^ 2 := by
  have hs0 : 0 ≤ ‖k‖ ^ 2 + ‖l‖ ^ 2 := by positivity
  have h2 : 2 * (‖k‖ * ‖l‖) ≤ ‖k‖ ^ 2 + ‖l‖ ^ 2 := by nlinarith [sq_nonneg (‖k‖ - ‖l‖)]
  have hy : ‖k + l‖ ^ 2 ≤ (1 + c) * (‖k‖ ^ 2 + ‖l‖ ^ 2) := by
    rw [norm_add_sq_real]
    have h3 := mul_le_mul_of_nonneg_left h2 hc
    nlinarith
  have hxs : ‖k‖ ^ 2 + ‖l‖ ^ 2 ≤ ‖x‖ * ‖k + l‖ := by
    have h := real_inner_le_norm x (k + l)
    rwa [inner_add_right, hk, hl] at h
  have hsq : (‖k‖ ^ 2 + ‖l‖ ^ 2) ^ 2 ≤ ‖x‖ ^ 2 * ((1 + c) * (‖k‖ ^ 2 + ‖l‖ ^ 2)) := by
    calc (‖k‖ ^ 2 + ‖l‖ ^ 2) ^ 2 ≤ (‖x‖ * ‖k + l‖) ^ 2 := pow_le_pow_left₀ hs0 hxs 2
      _ = ‖x‖ ^ 2 * ‖k + l‖ ^ 2 := mul_pow _ _ _
      _ ≤ ‖x‖ ^ 2 * ((1 + c) * (‖k‖ ^ 2 + ‖l‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hy (sq_nonneg _)
  have hfin : ‖k‖ ^ 2 + ‖l‖ ^ 2 ≤ (1 + c) * ‖x‖ ^ 2 := by
    rcases hs0.eq_or_lt with h | h
    · rw [← h]
      exact mul_nonneg (by linarith) (sq_nonneg _)
    · by_contra hlt
      rw [not_le] at hlt
      nlinarith [mul_pos h (sub_pos.2 hlt)]
  linarith

end Abstract

namespace Curvature

section NormalInner

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Orthogonal projectors on both sides are symmetric for the Frobenius inner product. -/
private theorem inner_mul_mul_eq_inner_mul_mul {P : Matrix m m ℝ} {Q : Matrix n n ℝ}
    (hP : IsOrthProjMat P) (hQ : IsOrthProjMat Q) (E M : Matrix m n ℝ) :
    ⟪E, P * M * Q⟫ = ⟪P * E * Q, M⟫ := by
  rw [Frobenius.inner_mul_right', hQ.symm, Frobenius.inner_mul_left', hP.symm, Matrix.mul_assoc]

/-- `P (P E Q) Q = P E Q` for projectors `P`, `Q`. -/
private theorem mul_mul_mul_mul_eq {P : Matrix m m ℝ} {Q : Matrix n n ℝ}
    (hP : IsOrthProjMat P) (hQ : IsOrthProjMat Q) (E : Matrix m n ℝ) :
    P * (P * E * Q) * Q = P * E * Q := by
  simp only [Matrix.mul_assoc, hQ.idem]
  rw [← Matrix.mul_assoc P P, hP.idem]

/-- `⟪E, P E Q⟫ = ‖P E Q‖²` for orthogonal projectors `P`, `Q`. -/
private theorem inner_mul_mul_self {P : Matrix m m ℝ} {Q : Matrix n n ℝ}
    (hP : IsOrthProjMat P) (hQ : IsOrthProjMat Q) (E : Matrix m n ℝ) :
    ⟪E, P * E * Q⟫ = ‖P * E * Q‖ ^ 2 := by
  have h := inner_mul_mul_eq_inner_mul_mul hP hQ (P * E * Q) E
  rw [mul_mul_mul_mul_eq hP hQ, real_inner_self_eq_norm_sq] at h
  rw [h]
  exact real_inner_comm _ _

variable [DecidableEq m] [DecidableEq n]

private theorem mul_le_one_of_le {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) :
    a * b ≤ 1 :=
  (mul_le_mul ha hb hb0 zero_le_one).trans_eq (one_mul 1)

/-- Two matrices in the ranges of two-sided projectors: if `P₁ K Q₁ = K` and `P₂ L Q₂ = L`, then
`⟪K, L⟫ ≤ ‖P₂ P₁‖₂ ‖Q₁ Q₂‖₂ ‖K‖ ‖L‖`. -/
private theorem inner_le_specNorm_mul_specNorm_mul {P₁ P₂ : Matrix m m ℝ}
    {Q₁ Q₂ : Matrix n n ℝ} (hP₂ : IsOrthProjMat P₂) (hQ₂ : IsOrthProjMat Q₂)
    {K L : Matrix m n ℝ} (hK : P₁ * K * Q₁ = K) (hL : P₂ * L * Q₂ = L) :
    ⟪K, L⟫ ≤ specNorm (P₂ * P₁) * specNorm (Q₁ * Q₂) * ‖K‖ * ‖L‖ := by
  have e : P₂ * K * Q₂ = P₂ * P₁ * K * (Q₁ * Q₂) := by
    conv_lhs => rw [← hK]
    simp only [Matrix.mul_assoc]
  have h1 : ‖P₂ * K * Q₂‖ ≤ specNorm (P₂ * P₁) * ‖K‖ * specNorm (Q₁ * Q₂) := by
    rw [e]
    exact (frob_mul_le' _ _).trans
      (mul_le_mul_of_nonneg_right (frob_mul_le _ _) (specNorm_nonneg _))
  calc ⟪K, L⟫ = ⟪K, P₂ * L * Q₂⟫ := by rw [hL]
    _ = ⟪P₂ * K * Q₂, L⟫ := inner_mul_mul_eq_inner_mul_mul hP₂ hQ₂ K L
    _ ≤ ‖P₂ * K * Q₂‖ * ‖L‖ := real_inner_le_norm _ _
    _ ≤ specNorm (P₂ * P₁) * ‖K‖ * specNorm (Q₁ * Q₂) * ‖L‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = _ := by ring

/-- **The normal component of `Y` at `X`, tested with a matrix, spectral norm.** Let `H` be a
reflexive generalized inverse of `Y` with the orthogonal projectors `Qu = Y H`, `Qv = H Y` and
`‖H‖₂ ≤ c`, and let the orthogonal projectors `Pu`, `Pv` fix `X`: `Pu X = X`, `X Pv = X`. For
every `N`, with the Frobenius inner product and `s = ‖Qu (1 - Pu)‖₂ ‖Qv (1 - Pv)‖₂`,

  `⟪(1 - Pu) Y (1 - Pv), N⟫ ≤ c ((1 + s)/2 ‖Y - X‖²) ‖N‖₂`. -/
theorem inner_normal_le_mul_mul_specNorm {X Y : Matrix m n ℝ} {H : Matrix n m ℝ}
    {Pu Qu : Matrix m m ℝ} {Pv Qv : Matrix n n ℝ} {c : ℝ} (hY : Y * H * Y = Y)
    (hYH : Y * H = Qu) (hHY : H * Y = Qv) (hH : H * Y * H = H) (hQu : IsOrthProjMat Qu)
    (hQv : IsOrthProjMat Qv) (hPu : IsOrthProjMat Pu) (hPv : IsOrthProjMat Pv)
    (hu : Pu * X = X) (hv : X * Pv = X) (hc : specNorm H ≤ c) (N : Matrix m n ℝ) :
    ⟪(1 - Pu) * Y * (1 - Pv), N⟫ ≤
      c * ((1 + specNorm (Qu * (1 - Pu)) * specNorm (Qv * (1 - Pv))) / 2 * ‖Y - X‖ ^ 2) *
        specNorm N := by
  have hc0 : 0 ≤ c := (specNorm_nonneg H).trans hc
  have hQvH : Qv * H = H := by rw [← hHY]; exact hH
  have hHQu : H * Qu = H := by rw [← hYH, ← Matrix.mul_assoc]; exact hH
  have hcurv : (1 - Pu) * Y * (1 - Pv) =
      (1 - Pu) * (Y - X) * Qv * (H * (Qu * (Y - X) * (1 - Pv))) := by
    rw [normal_eq_curvature hY hu hv]
    conv_lhs => rw [← hQvH, ← hHQu]
    simp only [Matrix.mul_assoc]
  have hKL : ‖(1 - Pu) * (Y - X) * Qv‖ * ‖Qu * (Y - X) * (1 - Pv)‖ ≤
      (1 + specNorm (Qu * (1 - Pu)) * specNorm (Qv * (1 - Pv))) / 2 * ‖Y - X‖ ^ 2 :=
    norm_mul_norm_le_one_add_div_two_mul_norm_sq
      (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _))
      (inner_mul_mul_self hPu.compl hQv (Y - X)) (inner_mul_mul_self hQu hPv.compl (Y - X))
      (inner_le_specNorm_mul_specNorm_mul hQu hPv.compl
        (mul_mul_mul_mul_eq hPu.compl hQv (Y - X)) (mul_mul_mul_mul_eq hQu hPv.compl (Y - X)))
  have h1 : ‖H * (Qu * (Y - X) * (1 - Pv))‖ ≤ c * ‖Qu * (Y - X) * (1 - Pv)‖ :=
    (frob_mul_le _ _).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  have h2 : ‖((1 - Pu) * (Y - X) * Qv)ᵀ * N‖ ≤ ‖(1 - Pu) * (Y - X) * Qv‖ * specNorm N := by
    have h := frob_mul_le' ((1 - Pu) * (Y - X) * Qv)ᵀ N
    rwa [Matrix.frobenius_norm_transpose] at h
  rw [hcurv, Frobenius.inner_mul_left]
  calc ⟪H * (Qu * (Y - X) * (1 - Pv)), ((1 - Pu) * (Y - X) * Qv)ᵀ * N⟫
      ≤ ‖H * (Qu * (Y - X) * (1 - Pv))‖ * ‖((1 - Pu) * (Y - X) * Qv)ᵀ * N‖ :=
        real_inner_le_norm _ _
    _ ≤ c * ‖Qu * (Y - X) * (1 - Pv)‖ * (‖(1 - Pu) * (Y - X) * Qv‖ * specNorm N) :=
        mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hc0 (norm_nonneg _))
    _ = c * (‖(1 - Pu) * (Y - X) * Qv‖ * ‖Qu * (Y - X) * (1 - Pv)‖) * specNorm N := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKL hc0)
        (specNorm_nonneg _)

/-- **The product of the sines between the spaces of `X` and `Y`.** Under the hypotheses of
`inner_normal_le_mul_mul_specNorm` on `H`, `Qu`, `Qv`, `Pu`, `Pv`:
`‖Qu (1 - Pu)‖₂ ‖Qv (1 - Pv)‖₂ ≤ min(1, (c ‖Y - X‖)²)`. -/
theorem specNorm_mul_compl_mul_specNorm_mul_compl_le_min {X Y : Matrix m n ℝ}
    {H : Matrix n m ℝ} {Pu Qu : Matrix m m ℝ} {Pv Qv : Matrix n n ℝ} {c : ℝ}
    (hYH : Y * H = Qu) (hHY : H * Y = Qv) (hQu : IsOrthProjMat Qu) (hQv : IsOrthProjMat Qv)
    (hPu : IsOrthProjMat Pu) (hPv : IsOrthProjMat Pv) (hu : Pu * X = X) (hv : X * Pv = X)
    (hc : specNorm H ≤ c) :
    specNorm (Qu * (1 - Pu)) * specNorm (Qv * (1 - Pv)) ≤ min 1 ((c * ‖Y - X‖) ^ 2) := by
  have hc0 : 0 ≤ c := (specNorm_nonneg H).trans hc
  have a1 : specNorm (Qu * (1 - Pu)) ≤ 1 :=
    (specNorm_mul_le _ _).trans (mul_le_one_of_le hQu.specNorm_le_one (specNorm_nonneg _)
      hPu.compl.specNorm_le_one)
  have b1 : specNorm (Qv * (1 - Pv)) ≤ 1 :=
    (specNorm_mul_le _ _).trans (mul_le_one_of_le hQv.specNorm_le_one (specNorm_nonneg _)
      hPv.compl.specNorm_le_one)
  have a2 : specNorm (Qu * (1 - Pu)) ≤ c * ‖Y - X‖ := by
    have e : Qu * (1 - Pu) = ((1 - Pu) * (Y - X) * H)ᵀ := by
      rw [← compl_mul_colProj H hu, hYH, Matrix.transpose_mul, hQu.symm, hPu.compl.symm]
    rw [e, specNorm_transpose]
    calc specNorm ((1 - Pu) * (Y - X) * H) ≤ ‖(1 - Pu) * (Y - X) * H‖ := specNorm_le_frob _
      _ ≤ ‖(1 - Pu) * (Y - X)‖ * specNorm H := frob_mul_le' _ _
      _ ≤ ‖Y - X‖ * c := mul_le_mul (hPu.compl.norm_mul_le _) hc (specNorm_nonneg _)
          (norm_nonneg _)
      _ = c * ‖Y - X‖ := mul_comm _ _
  have b2 : specNorm (Qv * (1 - Pv)) ≤ c * ‖Y - X‖ := by
    have e : Qv * (1 - Pv) = H * ((Y - X) * (1 - Pv)) := by
      rw [sub_mul_compl hv, ← hHY, Matrix.mul_assoc]
    rw [e]
    calc specNorm (H * ((Y - X) * (1 - Pv))) ≤ ‖H * ((Y - X) * (1 - Pv))‖ := specNorm_le_frob _
      _ ≤ specNorm H * ‖(Y - X) * (1 - Pv)‖ := frob_mul_le _ _
      _ ≤ c * ‖Y - X‖ := mul_le_mul hc (hPv.compl.norm_mul_le' _) (norm_nonneg _) hc0
  refine le_min ((mul_le_one_of_le a1 (specNorm_nonneg _) b1)) ?_
  rw [pow_two]
  exact mul_le_mul a2 b2 (specNorm_nonneg _) (mul_nonneg hc0 (norm_nonneg _))

end NormalInner

end Curvature

section AtPoint

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
/-- The projector onto the row space fixes `X` from the right. -/
private theorem mul_rangeProj_transpose_self (X : Matrix m n ℝ) : X * Xᵀ.rangeProj = X := by
  have h := congrArg Matrix.transpose (Matrix.rangeProj_mul_self Xᵀ)
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_rangeProj] at h

/-- `a (1 + s)/2 n ≤ a' (1 + s')/2 n'` for nonnegative reals with `a ≤ a'`, `s ≤ s'`,
`n ≤ n'`. -/
private theorem mul_one_add_div_two_mul_le {a s n a' s' n' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a')
    (hs0 : 0 ≤ s) (hss : s ≤ s') (hn0 : 0 ≤ n) (hnn : n ≤ n') :
    a * ((1 + s) / 2) * n ≤ a' * ((1 + s') / 2) * n' := by
  have h1 : a * ((1 + s) / 2) ≤ a' * ((1 + s') / 2) :=
    mul_le_mul haa (by linarith) (by linarith) (ha.trans haa)
  exact mul_le_mul h1 hnn hn0 (mul_nonneg (ha.trans haa) (by linarith))

/-- **The normal component of `Y` at `X`, tested with a matrix, spectral norm.** Let `Y` have
rank `r` with `0 < ρ ≤ σ_{r-1}(Y)`. For every `X` and `N`, with the projectors `Pu`, `Pv` of `X`
and `Qu`, `Qv` of `Y` onto the column and the row space and `s = ‖Qu (1 - Pu)‖₂ ‖Qv (1 - Pv)‖₂`,

  `⟪Y - P(X) Y, N⟫ ≤ ρ⁻¹ ((1 + s)/2 ‖Y - X‖²) ‖N‖₂`.

No rank is assumed for `X`. -/
theorem inner_sub_tangentProjAt_le_inv_mul_specNorm {r : ℕ} {X Y : Matrix m n ℝ}
    (hY : Y.rank = r) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin Y).singularValues (r - 1)) (N : Matrix m n ℝ) :
    ⟪Y - tangentProjAt X Y, N⟫ ≤
      ρ⁻¹ * ((1 + Curvature.specNorm (Y.rangeProj * (1 - X.rangeProj)) *
        Curvature.specNorm (Yᵀ.rangeProj * (1 - Xᵀ.rangeProj))) / 2 * ‖Y - X‖ ^ 2) *
        Curvature.specNorm N := by
  rw [tangentProjAt_apply_eq_tangentProjMat, Curvature.sub_tangentProjMat]
  exact Curvature.inner_normal_le_mul_mul_specNorm (Matrix.mul_pinv_mul_self Y)
    (Matrix.rangeProj_eq_mul_pinv Y).symm (pinv_mul_eq_rangeProj_transpose Y)
    (Matrix.pinv_mul_self_mul_pinv Y) (Matrix.isOrthProjMat_rangeProj Y)
    (Matrix.isOrthProjMat_rangeProj Yᵀ) (Matrix.isOrthProjMat_rangeProj X)
    (Matrix.isOrthProjMat_rangeProj Xᵀ) (Matrix.rangeProj_mul_self X)
    (mul_rangeProj_transpose_self X) (specNorm_pinv_le hY hρ hσ) N

/-- **The product of the sines between the column spaces and between the row spaces.** Let `Y`
have rank `r` with `0 < ρ ≤ σ_{r-1}(Y)`. For every `X`, with the projectors `Pu`, `Pv` of `X` and
`Qu`, `Qv` of `Y`: `‖Qu (1 - Pu)‖₂ ‖Qv (1 - Pv)‖₂ ≤ min(1, (ρ⁻¹ ‖Y - X‖)²)`. -/
theorem specNorm_rangeProj_mul_mul_specNorm_rangeProj_mul_le_min {r : ℕ} {X Y : Matrix m n ℝ}
    (hY : Y.rank = r) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin Y).singularValues (r - 1)) :
    Curvature.specNorm (Y.rangeProj * (1 - X.rangeProj)) *
        Curvature.specNorm (Yᵀ.rangeProj * (1 - Xᵀ.rangeProj)) ≤
      min 1 ((ρ⁻¹ * ‖Y - X‖) ^ 2) :=
  Curvature.specNorm_mul_compl_mul_specNorm_mul_compl_le_min
    (Matrix.rangeProj_eq_mul_pinv Y).symm (pinv_mul_eq_rangeProj_transpose Y)
    (Matrix.isOrthProjMat_rangeProj Y) (Matrix.isOrthProjMat_rangeProj Yᵀ)
    (Matrix.isOrthProjMat_rangeProj X) (Matrix.isOrthProjMat_rangeProj Xᵀ)
    (Matrix.rangeProj_mul_self X) (mul_rangeProj_transpose_self X) (specNorm_pinv_le hY hρ hσ)

/-- **The tangent projectors at two matrices of rank `r`, tested with their difference, spectral
norm.** Let `X`, `Y` have rank `r` with `0 < ρ ≤ σ_{r-1}(X)` and `0 < ρ' ≤ σ_{r-1}(Y)`. For
every `Z`, with the projectors `Pu`, `Pv` of `X` and `Qu`, `Qv` of `Y`,
`s₁ = ‖Pu (1 - Qu)‖₂ ‖Pv (1 - Qv)‖₂` and `s₂ = ‖Qu (1 - Pu)‖₂ ‖Qv (1 - Pv)‖₂`,

  `⟪Y - X, P(Y) Z - P(X) Z⟫ ≤
    (ρ⁻¹ (1 + s₁)/2 ‖Z - P(Y) Z‖₂ + ρ'⁻¹ (1 + s₂)/2 ‖Z - P(X) Z‖₂) ‖Y - X‖²`. -/
theorem inner_sub_tangentProjAt_sub_le_half_mul_specNorm {r : ℕ} {X Y : Matrix m n ℝ}
    (hX : X.rank = r) (hY : Y.rank = r) {ρ ρ' : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) (hρ' : 0 < ρ')
    (hσ' : ρ' ≤ (toEuclideanLin Y).singularValues (r - 1)) (Z : Matrix m n ℝ) :
    ⟪Y - X, tangentProjAt Y Z - tangentProjAt X Z⟫ ≤
      (ρ⁻¹ * ((1 + Curvature.specNorm (X.rangeProj * (1 - Y.rangeProj)) *
          Curvature.specNorm (Xᵀ.rangeProj * (1 - Yᵀ.rangeProj))) / 2) *
          Curvature.specNorm (Z - tangentProjAt Y Z) +
        ρ'⁻¹ * ((1 + Curvature.specNorm (Y.rangeProj * (1 - X.rangeProj)) *
          Curvature.specNorm (Yᵀ.rangeProj * (1 - Xᵀ.rangeProj))) / 2) *
          Curvature.specNorm (Z - tangentProjAt X Z)) * ‖Y - X‖ ^ 2 := by
  have hid := (isOrthProj_tangentProjAt Y).inner_sub_apply_sub_apply
    (isOrthProj_tangentProjAt X) (tangentProjAt_self Y) (tangentProjAt_self X) Z
  have h1 := inner_sub_tangentProjAt_le_inv_mul_specNorm (X := Y) hX hρ hσ
    (Z - tangentProjAt Y Z)
  have h2 := inner_sub_tangentProjAt_le_inv_mul_specNorm (X := X) hY hρ' hσ'
    (Z - tangentProjAt X Z)
  rw [norm_sub_rev X Y] at h1
  rw [hid]
  calc _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

omit [DecidableEq m] in
/-- **The tangent projectors tested with the difference, spectral norm, data at one point.** Let
`X`, `Y` have rank `r` with `‖Y - X‖ ≤ ε < ρ ≤ σ_{r-1}(X)`, and let `‖Z‖ ≤ μ` and
`‖Z - P(X) Z‖₂ ≤ ν`. Then

  `⟪Y - X, P(Y) Z - P(X) Z⟫ ≤ ((1 + s_X)/2 (ν/ρ + μ ε/ρ²) + (1 + s_Y)/2 ν/(ρ - ε)) ‖Y - X‖²`

with `s_X = min(1, (ε/ρ)²)` and `s_Y = min(1, (ε/(ρ - ε))²)`. To first order in `ε` the factor
is `ν/ρ`. -/
theorem inner_sub_tangentProjAt_sub_le_of_norm_sub_le_of_specNorm_le {r : ℕ}
    {X Y : Matrix m n ℝ} (hX : X.rank = r) (hY : Y.rank = r) {ρ ε μ ν : ℝ}
    (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) (he : ‖Y - X‖ ≤ ε) (hε : ε < ρ)
    {Z : Matrix m n ℝ} (hμ : ‖Z‖ ≤ μ)
    (hν : Curvature.specNorm (Z - tangentProjAt X Z) ≤ ν) :
    ⟪Y - X, tangentProjAt Y Z - tangentProjAt X Z⟫ ≤
      ((1 + min 1 ((ε / ρ) ^ 2)) / 2 * (ν / ρ + μ * ε / ρ ^ 2) +
        (1 + min 1 ((ε / (ρ - ε)) ^ 2)) / 2 * (ν / (ρ - ε))) * ‖Y - X‖ ^ 2 := by
  classical
  have he0 := norm_nonneg (Y - X)
  have hε0 : 0 ≤ ε := he0.trans he
  have hρ : 0 < ρ := hε0.trans_lt hε
  have hρε : 0 < ρ - ε := sub_pos.2 hε
  have hρe : 0 < ρ - ‖Y - X‖ := by linarith
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans hμ
  have hν0 : 0 ≤ ν := (Curvature.specNorm_nonneg _).trans hν
  have hσ' : ρ - ‖Y - X‖ ≤ (toEuclideanLin Y).singularValues (r - 1) := by
    have h := (abs_le.1 (WeylSingular.abs_singularValues_sub_le_frobenius X Y (r - 1))).2
    rw [norm_sub_rev X Y] at h
    linarith
  have h := inner_sub_tangentProjAt_sub_le_half_mul_specNorm hX hY hρ hσ hρe hσ' Z
  have s1 := specNorm_rangeProj_mul_mul_specNorm_rangeProj_mul_le_min (X := Y) hX hρ hσ
  have s2 := specNorm_rangeProj_mul_mul_specNorm_rangeProj_mul_le_min (X := X) hY hρe hσ'
  have hs1 : Curvature.specNorm (X.rangeProj * (1 - Y.rangeProj)) *
      Curvature.specNorm (Xᵀ.rangeProj * (1 - Yᵀ.rangeProj)) ≤ min 1 ((ε / ρ) ^ 2) := by
    refine s1.trans (min_le_min le_rfl (pow_le_pow_left₀
      (mul_nonneg (inv_nonneg.2 hρ.le) (norm_nonneg _)) ?_ 2))
    rw [norm_sub_rev, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left he (inv_nonneg.2 hρ.le)
  have hs2 : Curvature.specNorm (Y.rangeProj * (1 - X.rangeProj)) *
      Curvature.specNorm (Yᵀ.rangeProj * (1 - Xᵀ.rangeProj)) ≤
        min 1 ((ε / (ρ - ε)) ^ 2) := by
    refine s2.trans (min_le_min le_rfl (pow_le_pow_left₀
      (mul_nonneg (inv_nonneg.2 hρe.le) he0) ?_ 2))
    rw [div_eq_inv_mul]
    exact mul_le_mul (inv_anti₀ hρε (by linarith)) he he0 (inv_nonneg.2 hρε.le)
  have hN : Curvature.specNorm (Z - tangentProjAt Y Z) ≤ ν + ρ⁻¹ * ε * μ := by
    have e : Z - tangentProjAt Y Z =
        (Z - tangentProjAt X Z) + -(tangentProjAt Y Z - tangentProjAt X Z) := by abel
    rw [e]
    refine (WeylSingular.specNorm_add_le _ _).trans (add_le_add hν ?_)
    rw [WeylSingular.specNorm_neg]
    refine (Curvature.specNorm_le_frob _).trans
      ((norm_tangentProjAt_sub_le_inv_mul hX hY hρ hσ Z).trans ?_)
    exact mul_le_mul (mul_le_mul_of_nonneg_left he (inv_nonneg.2 hρ.le)) hμ (norm_nonneg _)
      (mul_nonneg (inv_nonneg.2 hρ.le) hε0)
  have t1 := mul_one_add_div_two_mul_le (inv_nonneg.2 hρ.le) le_rfl
    (mul_nonneg (Curvature.specNorm_nonneg _) (Curvature.specNorm_nonneg _)) hs1
    (Curvature.specNorm_nonneg _) hN
  have t2 := mul_one_add_div_two_mul_le (inv_nonneg.2 hρe.le) (inv_anti₀ hρε (by linarith))
    (mul_nonneg (Curvature.specNorm_nonneg _) (Curvature.specNorm_nonneg _)) hs2
    (Curvature.specNorm_nonneg _) hν
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  calc _ ≤ ρ⁻¹ * ((1 + min 1 ((ε / ρ) ^ 2)) / 2) * (ν + ρ⁻¹ * ε * μ) +
        (ρ - ε)⁻¹ * ((1 + min 1 ((ε / (ρ - ε)) ^ 2)) / 2) * ν := add_le_add t1 t2
    _ = _ := by
        rw [div_eq_mul_inv ν ρ, div_eq_mul_inv (μ * ε), div_eq_mul_inv ν (ρ - ε)]
        ring

end AtPoint

section Solutions

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- **Quasi-optimality of matrix DLRA for a given growth rate of the projector term.** Let `F`
be `L`-Lipschitz, `Y` a DLRA solution of rank `r` of `Ẏ = P(Y) F(t, Y)` on `[a, b]`, `A` a
continuous curve and `X` a continuous curve with right derivatives `X'`. Let `κ`, `d` be
continuous on `[a, b]` with

  `⟪Y t - X t, P(Y t) F(t, A t) - P(X t) F(t, A t)⟫ ≤ κ t ‖Y t - X t‖²`

and `‖P(X t) F(t, A t) - X' t‖ ≤ d t` on `[a, b)`. If `‖Y a - X a‖ ≤ δ`, then for `t ∈ [a, b]`

  `‖Y t - X t‖ ≤ e^{∫ₐᵗ (L + κ)} δ + ∫ₐᵗ e^{∫ₛᵗ (L + κ)} (L ‖X s - A s‖ + d s) ds`.

Nothing is assumed on the rank of `X` or on the sign of `κ`. -/
theorem IsDLRASolution.norm_sub_le_integral_exp_integral_of_inner_tangentProjAt_sub_le {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ} {κ d : ℝ → ℝ}
    {a b L δ : ℝ} (hY : IsDLRASolution r F Y a b) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hAc : ContinuousOn A (Icc a b)) (hκc : ContinuousOn κ (Icc a b))
    (hdc : ContinuousOn d (Icc a b)) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hκ : ∀ t ∈ Ico a b,
      ⟪Y t - X t, tangentProjAt (Y t) (F t (A t)) - tangentProjAt (X t) (F t (A t))⟫ ≤
        κ t * ‖Y t - X t‖ ^ 2)
    (hd : ∀ t ∈ Ico a b, ‖tangentProjAt (X t) (F t (A t)) - X' t‖ ≤ d t)
    (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp (∫ u in a..t, (L + κ u)) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t, (L + κ u)) * (L * ‖X s - A s‖ + d s) := by
  intro t0 ht0
  rcases eq_or_lt_of_le ht0.1 with h0 | hpos
  · subst h0
    simpa using hδ
  have hab : a < b := hpos.trans_le ht0.2
  have hIcc : Icc a t0 ⊆ Icc a b := Icc_subset_Icc_right ht0.2
  have hIco : ∀ s ∈ Ico a t0, s ∈ Ico a b := fun s hs => ⟨hs.1, hs.2.trans_le ht0.2⟩
  have hkOn : ContinuousOn (fun u => L + κ u) (Icc a b) := continuousOn_const.add hκc
  have hgOn : ContinuousOn (fun s => L * ‖X s - A s‖ + d s) (Icc a b) :=
    (continuousOn_const.mul (hXc.sub hAc).norm).add hdc
  obtain ⟨kc, hkc, hkeq⟩ : ∃ kc : ℝ → ℝ, Continuous kc ∧ ∀ s ∈ Icc a b, kc s = L + κ s :=
    ⟨fun s => L + κ (projIcc a b hab.le s),
      hkOn.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        fun s => (projIcc a b hab.le s).2,
      fun s hs => by simp only [projIcc_of_mem _ hs]⟩
  obtain ⟨gc, hgc, hgeq⟩ : ∃ gc : ℝ → ℝ, Continuous gc ∧ ∀ s ∈ Icc a b, gc s =
      L * ‖X s - A s‖ + d s :=
    ⟨fun s => L * ‖X (projIcc a b hab.le s) - A (projIcc a b hab.le s)‖ +
        d (projIcc a b hab.le s),
      hgOn.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        fun s => (projIcc a b hab.le s).2,
      fun s hs => by simp only [projIcc_of_mem _ hs]⟩
  have hg0 : ∀ s ∈ Ico a t0, 0 ≤ gc s := fun s hs => by
    rw [hgeq s (Ico_subset_Icc_self (hIco s hs))]
    exact add_nonneg (mul_nonneg hL (norm_nonneg _))
      ((norm_nonneg _).trans (hd s (hIco s hs)))
  have hbound : ∀ s ∈ Ico a t0,
      ⟪Y s - X s, tangentProjAt (Y s) (F s (Y s)) - X' s⟫ ≤
        (kc s * ‖Y s - X s‖ + gc s) * ‖Y s - X s‖ := fun s hs => by
    have hsb := hIco s hs
    have hsI := Ico_subset_Icc_self hsb
    have hsplit : tangentProjAt (Y s) (F s (Y s)) - X' s =
        tangentProjAt (Y s) (F s (Y s) - F s (A s)) +
        (tangentProjAt (Y s) (F s (A s)) - tangentProjAt (X s) (F s (A s))) +
        (tangentProjAt (X s) (F s (A s)) - X' s) := by
      rw [map_sub]
      abel
    have i1 : ⟪Y s - X s, tangentProjAt (Y s) (F s (Y s) - F s (A s))⟫ ≤
        ‖Y s - X s‖ * (L * ‖Y s - X s‖ + L * ‖X s - A s‖) := by
      refine (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      refine ((isOrthProj_tangentProjAt (Y s)).norm_le _).trans ((hF s _ _).trans ?_)
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hL
      calc ‖Y s - A s‖ = ‖(Y s - X s) + (X s - A s)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖Y s - X s‖ + ‖X s - A s‖ := norm_add_le _ _
    have i2 := hκ s hsb
    have i3 : ⟪Y s - X s, tangentProjAt (X s) (F s (A s)) - X' s⟫ ≤ ‖Y s - X s‖ * d s :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hd s hsb) (norm_nonneg _))
    rw [hsplit, inner_add_right, inner_add_right, hkeq s hsI, hgeq s hsI]
    calc _ ≤ ‖Y s - X s‖ * (L * ‖Y s - X s‖ + L * ‖X s - A s‖) +
          κ s * ‖Y s - X s‖ ^ 2 + ‖Y s - X s‖ * d s := add_le_add (add_le_add i1 i2) i3
      _ = _ := by ring
  have hcmp := norm_le_exp_integral_mul_add_integral_exp_integral_mul_of_inner_le
    (f := fun t => Y t - X t)
    (f' := fun t => tangentProjAt (Y t) (F t (Y t)) - X' t) (δ := δ) hkc hgc hg0
    ((hY.1.cont.sub hXc).mono hIcc)
    (fun s hs => (hY.1.deriv s (hIco s hs)).sub (hX s (hIco s hs))) hδ hbound t0
    ⟨ht0.1, le_rfl⟩
  have e1 : ∫ u in a..t0, kc u = ∫ u in a..t0, (L + κ u) :=
    intervalIntegral.integral_congr fun u hu => by
      rw [uIcc_of_le ht0.1] at hu
      exact hkeq u (hIcc hu)
  have e2 : ∫ s in a..t0, Real.exp (∫ u in s..t0, kc u) * gc s =
      ∫ s in a..t0, Real.exp (∫ u in s..t0, (L + κ u)) * (L * ‖X s - A s‖ + d s) :=
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le ht0.1] at hs
      have e3 : ∫ u in s..t0, kc u = ∫ u in s..t0, (L + κ u) :=
        intervalIntegral.integral_congr fun u hu => by
          rw [uIcc_of_le hs.2] at hu
          exact hkeq u ⟨hs.1.trans hu.1, hu.2.trans ht0.2⟩
      change Real.exp (∫ u in s..t0, kc u) * gc s = _
      rw [e3, hgeq s (hIcc hs)]
  rw [e1, e2] at hcmp
  exact hcmp

/-- **Quasi-optimality with the normal velocity as growth rate, a posteriori form.** Let `F` be
`L`-Lipschitz, `Y` a DLRA solution of rank `r` on `[a, b]`, `A` a continuous curve and `X` a
continuous curve of matrices of rank `r` with right derivatives `X'`. Let `ρ`, `ρ'`, `ν`, `ν'`,
`ς`, `d` be continuous on `[a, b]` with, for `Z = F(t, A t)`,

  `0 < ρ t ≤ σ_{r-1}(X t)`,   `0 < ρ' t ≤ σ_{r-1}(Y t)`,
  `‖(1 - P(X t)) Z‖₂ ≤ ν t`,   `‖(1 - P(Y t)) Z‖₂ ≤ ν' t`,   `‖P(X t) Z - X' t‖ ≤ d t`,

and `ς t` a bound of the two products of sines between the column spaces and between the row
spaces of `X t` and `Y t` (`ς = 1` is admissible, and so is `min(1, (‖Y - X‖/min(ρ, ρ'))²)`, by
`specNorm_rangeProj_mul_mul_specNorm_rangeProj_mul_le_min`). If `‖Y a - X a‖ ≤ δ`, then with
`k = L + (1 + ς)/2 (ν'/ρ + ν/ρ')`, for `t ∈ [a, b]`

  `‖Y t - X t‖ ≤ e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖X s - A s‖ + d s) ds`.

The quantities `ρ'`, `ν'`, `ς` are measured on the computed solution `Y`; there is no smallness
condition on `Y - X`. -/
theorem IsDLRASolution.norm_sub_le_integral_exp_integral_of_specNorm_sub_tangentProjAt_le
    [DecidableEq m] {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ}
    {ρ ρ' ν ν' ς d : ℝ → ℝ} {a b L δ : ℝ} (hY : IsDLRASolution r F Y a b) (hL : 0 ≤ L)
    (hF : IsLipschitzField F L) (hAc : ContinuousOn A (Icc a b))
    (hρc : ContinuousOn ρ (Icc a b)) (hρc' : ContinuousOn ρ' (Icc a b))
    (hνc : ContinuousOn ν (Icc a b)) (hνc' : ContinuousOn ν' (Icc a b))
    (hςc : ContinuousOn ς (Icc a b)) (hdc : ContinuousOn d (Icc a b))
    (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r) (hρ : ∀ t ∈ Icc a b, 0 < ρ t)
    (hσ : ∀ t ∈ Icc a b, ρ t ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hρ' : ∀ t ∈ Icc a b, 0 < ρ' t)
    (hσ' : ∀ t ∈ Icc a b, ρ' t ≤ (toEuclideanLin (Y t)).singularValues (r - 1))
    (hν : ∀ t ∈ Ico a b,
      Curvature.specNorm (F t (A t) - tangentProjAt (X t) (F t (A t))) ≤ ν t)
    (hν' : ∀ t ∈ Ico a b,
      Curvature.specNorm (F t (A t) - tangentProjAt (Y t) (F t (A t))) ≤ ν' t)
    (hς : ∀ t ∈ Ico a b,
      Curvature.specNorm ((X t).rangeProj * (1 - (Y t).rangeProj)) *
          Curvature.specNorm ((X t)ᵀ.rangeProj * (1 - (Y t)ᵀ.rangeProj)) ≤ ς t ∧
        Curvature.specNorm ((Y t).rangeProj * (1 - (X t).rangeProj)) *
          Curvature.specNorm ((Y t)ᵀ.rangeProj * (1 - (X t)ᵀ.rangeProj)) ≤ ς t)
    (hd : ∀ t ∈ Ico a b, ‖tangentProjAt (X t) (F t (A t)) - X' t‖ ≤ d t)
    (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp (∫ u in a..t, (L + (1 + ς u) / 2 * (ν' u / ρ u + ν u / ρ' u))) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t, (L + (1 + ς u) / 2 * (ν' u / ρ u + ν u / ρ' u))) *
          (L * ‖X s - A s‖ + d s) := by
  have hκc : ContinuousOn (fun u => (1 + ς u) / 2 * (ν' u / ρ u + ν u / ρ' u)) (Icc a b) :=
    ((continuousOn_const.add hςc).div_const 2).mul
      ((hνc'.div hρc fun u hu => (hρ u hu).ne').add (hνc.div hρc' fun u hu => (hρ' u hu).ne'))
  refine hY.norm_sub_le_integral_exp_integral_of_inner_tangentProjAt_sub_le
    (κ := fun u => (1 + ς u) / 2 * (ν' u / ρ u + ν u / ρ' u)) hL hF hAc hκc hdc hXc hX
    (fun t ht => ?_) hd hδ
  have htI := Ico_subset_Icc_self ht
  have h := inner_sub_tangentProjAt_sub_le_half_mul_specNorm (hXr t htI) (hY.2 t htI)
    (hρ t htI) (hσ t htI) (hρ' t htI) (hσ' t htI) (F t (A t))
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  have t1 := mul_one_add_div_two_mul_le (inv_nonneg.2 (hρ t htI).le) le_rfl
    (mul_nonneg (Curvature.specNorm_nonneg _) (Curvature.specNorm_nonneg _)) (hς t ht).1
    (Curvature.specNorm_nonneg _) (hν' t ht)
  have t2 := mul_one_add_div_two_mul_le (inv_nonneg.2 (hρ' t htI).le) le_rfl
    (mul_nonneg (Curvature.specNorm_nonneg _) (Curvature.specNorm_nonneg _)) (hς t ht).2
    (Curvature.specNorm_nonneg _) (hν t ht)
  calc _ ≤ (ρ t)⁻¹ * ((1 + ς t) / 2) * ν' t + (ρ' t)⁻¹ * ((1 + ς t) / 2) * ν t :=
        add_le_add t1 t2
    _ = _ := by
        rw [div_eq_mul_inv (ν' t), div_eq_mul_inv (ν t)]
        ring

/-- **Quasi-optimality with the spectral norm of the normal velocity as growth rate, tube form.**
Under the hypotheses of
`IsDLRASolution.norm_sub_le_integral_exp_integral_of_norm_sub_tangentProjAt_le` on `F`, `Y`, `A`,
`X` and the continuous functions `ρ`, `μ`, `d`, `ε`, let `ν` be continuous with the spectral norm
of the normal velocity below it, `‖(1 - P(X t)) F(t, A t)‖₂ ≤ ν t`. If `‖Y t - X t‖ ≤ ε t` on
`[a, b)` and `‖Y a - X a‖ ≤ δ`, then with

  `k = L + (1 + s_X)/2 (ν/ρ + μ ε/ρ²) + (1 + s_Y)/2 ν/(ρ - ε)`,
  `s_X = min(1, (ε/ρ)²)`,   `s_Y = min(1, (ε/(ρ - ε))²)`,

for `t ∈ [a, b]`

  `‖Y t - X t‖ ≤ e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖X s - A s‖ + d s) ds`.

To first order in `ε` the rate is `L + ν/ρ`. -/
theorem IsDLRASolution.norm_sub_le_integral_exp_integral_of_norm_sub_le_of_specNorm_le {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ}
    {ρ μ ν d ε : ℝ → ℝ} {a b L δ : ℝ} (hY : IsDLRASolution r F Y a b) (hL : 0 ≤ L)
    (hF : IsLipschitzField F L) (hAc : ContinuousOn A (Icc a b))
    (hρc : ContinuousOn ρ (Icc a b)) (hμc : ContinuousOn μ (Icc a b))
    (hνc : ContinuousOn ν (Icc a b)) (hdc : ContinuousOn d (Icc a b))
    (hεc : ContinuousOn ε (Icc a b)) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ t ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ t)
    (hν : ∀ t ∈ Ico a b,
      Curvature.specNorm (F t (A t) - tangentProjAt (X t) (F t (A t))) ≤ ν t)
    (hd : ∀ t ∈ Ico a b, ‖tangentProjAt (X t) (F t (A t)) - X' t‖ ≤ d t)
    (hε0 : ∀ t ∈ Icc a b, 0 ≤ ε t) (hερ : ∀ t ∈ Icc a b, ε t < ρ t)
    (htube : ∀ t ∈ Ico a b, ‖Y t - X t‖ ≤ ε t) (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp (∫ u in a..t, (L + ((1 + min 1 ((ε u / ρ u) ^ 2)) / 2 * (ν u / ρ u +
      μ u * ε u / ρ u ^ 2) + (1 + min 1 ((ε u / (ρ u - ε u)) ^ 2)) / 2 * (ν u /
      (ρ u - ε u))))) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t, (L + ((1 + min 1 ((ε u / ρ u) ^ 2)) / 2 * (ν u / ρ u +
        μ u * ε u / ρ u ^ 2) + (1 + min 1 ((ε u / (ρ u - ε u)) ^ 2)) / 2 * (ν u / (ρ u - ε u))))) *
          (L * ‖X s - A s‖ + d s) := by
  have hρpos : ∀ u ∈ Icc a b, 0 < ρ u := fun u hu => (hε0 u hu).trans_lt (hερ u hu)
  have hne : ∀ u ∈ Icc a b, ρ u ≠ 0 := fun u hu => (hρpos u hu).ne'
  have hne2 : ∀ u ∈ Icc a b, ρ u ^ 2 ≠ 0 := fun u hu => (pow_pos (hρpos u hu) 2).ne'
  have hne3 : ∀ u ∈ Icc a b, ρ u - ε u ≠ 0 := fun u hu => (sub_pos.2 (hερ u hu)).ne'
  have hκc : ContinuousOn
      (fun u => ((1 + min 1 ((ε u / ρ u) ^ 2)) / 2 * (ν u / ρ u + μ u * ε u / ρ u ^ 2) + (1 +
      min 1 ((ε u / (ρ u - ε u)) ^ 2)) / 2 * (ν u / (ρ u - ε u))))
      (Icc a b) :=
    (((continuousOn_const.add (continuousOn_const.inf ((hεc.div hρc hne).pow 2))).div_const
      2).mul ((hνc.div hρc hne).add ((hμc.mul hεc).div (hρc.pow 2) hne2))).add
      (((continuousOn_const.add (continuousOn_const.inf
        ((hεc.div (hρc.sub hεc) hne3).pow 2))).div_const 2).mul (hνc.div (hρc.sub hεc) hne3))
  exact hY.norm_sub_le_integral_exp_integral_of_inner_tangentProjAt_sub_le
    (κ := fun u => ((1 + min 1 ((ε u / ρ u) ^ 2)) / 2 * (ν u / ρ u + μ u * ε u / ρ u ^ 2) + (1 +
      min 1 ((ε u / (ρ u - ε u)) ^ 2)) / 2 * (ν u / (ρ u - ε u))))
    hL hF hAc hκc hdc hXc hX
    (fun t ht => inner_sub_tangentProjAt_sub_le_of_norm_sub_le_of_specNorm_le
      (hXr t (Ico_subset_Icc_self ht)) (hY.2 t (Ico_subset_Icc_self ht))
      (hσ t (Ico_subset_Icc_self ht)) (htube t ht) (hερ t (Ico_subset_Icc_self ht)) (hμ t ht)
      (hν t ht)) hd hδ

/-- **Quasi-optimality with the spectral norm of the normal velocity as growth rate, a priori
form.** Under the hypotheses of
`IsDLRASolution.norm_sub_le_integral_exp_integral_of_norm_sub_le_of_specNorm_le` on `F`, `A`, `X`
and the functions `ρ`, `μ`, `ν`, `d`, `ε`, the tube condition on `Y` may be replaced by a
condition on the bound: if

  `e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖X s - A s‖ + d s) ds < ε t`   on `[a, b]`,

`k = L + (1 + s_X)/2 (ν/ρ + μ ε/ρ²) + (1 + s_Y)/2 ν/(ρ - ε)`, then `‖Y t - X t‖` is at most the
left-hand side on `[a, b]`. -/
theorem IsDLRASolution.norm_sub_le_integral_exp_integral_of_integral_lt_of_specNorm_le {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ}
    {ρ μ ν d ε : ℝ → ℝ} {a b L δ : ℝ} (hY : IsDLRASolution r F Y a b) (hL : 0 ≤ L)
    (hF : IsLipschitzField F L) (hAc : ContinuousOn A (Icc a b))
    (hρc : ContinuousOn ρ (Icc a b)) (hμc : ContinuousOn μ (Icc a b))
    (hνc : ContinuousOn ν (Icc a b)) (hdc : ContinuousOn d (Icc a b))
    (hεc : ContinuousOn ε (Icc a b)) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ t ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ t)
    (hν : ∀ t ∈ Ico a b,
      Curvature.specNorm (F t (A t) - tangentProjAt (X t) (F t (A t))) ≤ ν t)
    (hd : ∀ t ∈ Ico a b, ‖tangentProjAt (X t) (F t (A t)) - X' t‖ ≤ d t)
    (hε0 : ∀ t ∈ Icc a b, 0 ≤ ε t) (hερ : ∀ t ∈ Icc a b, ε t < ρ t)
    (hδ : ‖Y a - X a‖ ≤ δ)
    (hB : ∀ t ∈ Icc a b,
      Real.exp (∫ u in a..t, (L + ((1 + min 1 ((ε u / ρ u) ^ 2)) / 2 * (ν u / ρ u +
      μ u * ε u / ρ u ^ 2) + (1 + min 1 ((ε u / (ρ u - ε u)) ^ 2)) / 2 * (ν u /
      (ρ u - ε u))))) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t, (L + ((1 + min 1 ((ε u / ρ u) ^ 2)) / 2 * (ν u / ρ u +
        μ u * ε u / ρ u ^ 2) + (1 + min 1 ((ε u / (ρ u - ε u)) ^ 2)) / 2 * (ν u / (ρ u - ε u))))) *
          (L * ‖X s - A s‖ + d s) < ε t) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp (∫ u in a..t, (L + ((1 + min 1 ((ε u / ρ u) ^ 2)) / 2 * (ν u / ρ u +
      μ u * ε u / ρ u ^ 2) + (1 + min 1 ((ε u / (ρ u - ε u)) ^ 2)) / 2 * (ν u /
      (ρ u - ε u))))) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t, (L + ((1 + min 1 ((ε u / ρ u) ^ 2)) / 2 * (ν u / ρ u +
        μ u * ε u / ρ u ^ 2) + (1 + min 1 ((ε u / (ρ u - ε u)) ^ 2)) / 2 * (ν u / (ρ u - ε u))))) *
          (L * ‖X s - A s‖ + d s) := by
  have h := bootstrap_of_continuousOn (e := fun t => ‖Y t - X t‖ - ε t)
    (β := fun t =>
      (
        Real.exp (∫ u in a..t, (L + ((1 + min 1 ((ε u / ρ u) ^ 2)) / 2 * (ν u / ρ u +
        μ u * ε u / ρ u ^ 2) + (1 + min 1 ((ε u / (ρ u - ε u)) ^ 2)) / 2 * (ν u /
        (ρ u - ε u))))) * δ +
          ∫ s in a..t, Real.exp (∫ u in s..t, (L + ((1 + min 1 ((ε u / ρ u) ^ 2)) / 2 * (ν u / ρ u +
          μ u * ε u / ρ u ^ 2) + (1 + min 1 ((ε u / (ρ u - ε u)) ^ 2)) / 2 * (ν u /
          (ρ u - ε u))))) *
            (L * ‖X s - A s‖ + d s)) - ε t)
    (R := 0) ((hY.1.cont.sub hXc).norm.sub hεc)
    (fun t ht => sub_neg.2 (hB t ht)) (fun t ht hs => by
      have hIcc : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
      have hIco : ∀ s ∈ Ico a t, s ∈ Ico a b := fun s hs => ⟨hs.1, hs.2.trans_le ht.2⟩
      have hYt : IsDLRASolution r F Y a t :=
        ⟨⟨hY.1.cont.mono hIcc, fun s hs => hY.1.deriv s (hIco s hs)⟩,
          fun s hs => hY.2 s (hIcc hs)⟩
      have hm := hYt.norm_sub_le_integral_exp_integral_of_norm_sub_le_of_specNorm_le hL hF
        (hAc.mono hIcc) (hρc.mono hIcc) (hμc.mono hIcc) (hνc.mono hIcc) (hdc.mono hIcc)
        (hεc.mono hIcc) (hXc.mono hIcc) (fun s hs => hX s (hIco s hs))
        (fun s hs => hXr s (hIcc hs)) (fun s hs => hσ s (hIcc hs))
        (fun s hs => hμ s (hIco s hs)) (fun s hs => hν s (hIco s hs))
        (fun s hs => hd s (hIco s hs)) (fun s hs => hε0 s (hIcc hs))
        (fun s hs => hερ s (hIcc hs)) (fun s hs' => sub_nonpos.1 (hs s hs')) hδ t
        ⟨ht.1, le_rfl⟩
      exact sub_le_sub_right hm _)
  exact fun t ht => (sub_le_sub_iff_right _).1 (h t ht)

open EckartYoung in
/-- **Quasi-optimality against the truncated SVD: spectral norm of the normal velocity as growth
rate, Weingarten map of the field as source.** Let `F` be `L`-Lipschitz, `A` a solution of
`Ȧ = F(t, A)` on `[a, b]` with the gap `σ_r(A t) < σ_{r-1}(A t)`, and `Y` a DLRA solution of rank
`r`. Write `T t = T_r(A t)`, `R t = A t - T t`, `Z t = F(t, A t)`, `ρ = σ_{r-1}(A ·)`,
`τ = σ_r(A ·)`. Let `μ`, `ν`, `ω`, `ε` be continuous with `‖Z t‖ ≤ μ t`,
`‖(1 - P(T t)) Z t‖₂ ≤ ν t`, `‖(T⁺)ᵀ Zᵀ R + R Zᵀ (T⁺)ᵀ‖ ≤ ω t` and `0 ≤ ε t < ρ t`. With

  `k = L + (1 + s_X)/2 (ν/ρ + μ ε/ρ²) + (1 + s_Y)/2 ν/(ρ - ε)`,
  `s_X = min(1, (ε/ρ)²)`,   `s_Y = min(1, (ε/(ρ - ε))²)`:

if `‖Y a - T a‖ ≤ δ` and

  `e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖T s - A s‖ + ρ s/(ρ s - τ s) ω s) ds < ε t`   on `[a, b]`,

then `‖Y t - T t‖` is at most the left-hand side on `[a, b]`. All data are data of `A` and of
the field along `A`. -/
theorem IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_specNorm_le
    {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A Y : ℝ → Matrix m n ℝ} {μ ν ω ε : ℝ → ℝ}
    {a b L δ : ℝ} (hY : IsDLRASolution r F Y a b) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hA : ODESolution F A a b) (hμc : ContinuousOn μ (Icc a b))
    (hνc : ContinuousOn ν (Icc a b)) (hωc : ContinuousOn ω (Icc a b))
    (hεc : ContinuousOn ε (Icc a b)) (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ t)
    (hν : ∀ t ∈ Ico a b, Curvature.specNorm
      (F t (A t) - tangentProjAt (truncation (A t) r) (F t (A t))) ≤ ν t)
    (hω : ∀ t ∈ Ico a b,
      ‖(truncation (A t) r).pinvᵀ * (F t (A t))ᵀ * (A t - truncation (A t) r) +
        (A t - truncation (A t) r) * (F t (A t))ᵀ * (truncation (A t) r).pinvᵀ‖ ≤ ω t)
    (hgap : ∀ t ∈ Icc a b, (toEuclideanLin (A t)).singularValues r <
      (toEuclideanLin (A t)).singularValues (r - 1))
    (hε0 : ∀ t ∈ Icc a b, 0 ≤ ε t)
    (hερ : ∀ t ∈ Icc a b, ε t < (toEuclideanLin (A t)).singularValues (r - 1))
    (hδ : ‖Y a - truncation (A a) r‖ ≤ δ)
    (hB : ∀ t ∈ Icc a b,
      Real.exp (∫ u in a..t, (L + ((1 + min 1 ((ε u /
      (toEuclideanLin (A u)).singularValues (r - 1)) ^ 2)) / 2 * (ν u /
      (toEuclideanLin (A u)).singularValues (r - 1) + μ u * ε u /
      (toEuclideanLin (A u)).singularValues (r - 1) ^ 2) + (1 + min 1 ((ε u /
      ((toEuclideanLin (A u)).singularValues (r - 1) - ε u)) ^ 2)) / 2 * (ν u /
      ((toEuclideanLin (A u)).singularValues (r - 1) - ε u))))) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t, (L + ((1 + min 1 ((ε u /
        (toEuclideanLin (A u)).singularValues (r - 1)) ^ 2)) / 2 * (ν u /
        (toEuclideanLin (A u)).singularValues (r - 1) + μ u * ε u /
        (toEuclideanLin (A u)).singularValues (r - 1) ^ 2) + (1 + min 1 ((ε u /
        ((toEuclideanLin (A u)).singularValues (r - 1) - ε u)) ^ 2)) / 2 * (ν u /
        ((toEuclideanLin (A u)).singularValues (r - 1) - ε u))))) *
          (L * ‖truncation (A s) r - A s‖ + (toEuclideanLin (A s)).singularValues (r - 1) /
          ((toEuclideanLin (A s)).singularValues (r - 1) -
          (toEuclideanLin (A s)).singularValues r) * ω s) < ε t) :
    ∀ t ∈ Icc a b, ‖Y t - truncation (A t) r‖ ≤
      Real.exp (∫ u in a..t, (L + ((1 + min 1 ((ε u /
      (toEuclideanLin (A u)).singularValues (r - 1)) ^ 2)) / 2 * (ν u /
      (toEuclideanLin (A u)).singularValues (r - 1) + μ u * ε u /
      (toEuclideanLin (A u)).singularValues (r - 1) ^ 2) + (1 + min 1 ((ε u /
      ((toEuclideanLin (A u)).singularValues (r - 1) - ε u)) ^ 2)) / 2 * (ν u /
      ((toEuclideanLin (A u)).singularValues (r - 1) - ε u))))) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t, (L + ((1 + min 1 ((ε u /
        (toEuclideanLin (A u)).singularValues (r - 1)) ^ 2)) / 2 * (ν u /
        (toEuclideanLin (A u)).singularValues (r - 1) + μ u * ε u /
        (toEuclideanLin (A u)).singularValues (r - 1) ^ 2) + (1 + min 1 ((ε u /
        ((toEuclideanLin (A u)).singularValues (r - 1) - ε u)) ^ 2)) / 2 * (ν u /
        ((toEuclideanLin (A u)).singularValues (r - 1) - ε u))))) *
          (L * ‖truncation (A s) r - A s‖ + (toEuclideanLin (A s)).singularValues (r - 1) /
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
  refine hY.norm_sub_le_integral_exp_integral_of_integral_lt_of_specNorm_le (A := A)
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

end Solutions

/-! ### Examples -/

namespace QuasiOptimalityNormalVelocitySpectralExamples

open scoped LeanDLRA.Frobenius
open QuasiOptimalityExamples QuasiOptimalitySpeedExample QuasiOptimalityDefectExamples

/-- **Non-vacuity of `norm_mul_norm_le_one_add_div_two_mul_norm_sq`** in `ℝ` with
`x = k = l = 1` and `c = 1`: both sides are `1`. -/
example : ‖(1 : ℝ)‖ * ‖(1 : ℝ)‖ ≤ (1 + 1) / 2 * ‖(1 : ℝ)‖ ^ 2 :=
  norm_mul_norm_le_one_add_div_two_mul_norm_sq zero_le_one (real_inner_self_eq_norm_sq 1)
    (real_inner_self_eq_norm_sq 1) (by rw [real_inner_self_eq_norm_sq, pow_two, one_mul])

/-- **Non-vacuity of `inner_sub_tangentProjAt_le_inv_mul_specNorm`,
`specNorm_rangeProj_mul_mul_specNorm_rangeProj_mul_le_min` and
`inner_sub_tangentProjAt_sub_le_half_mul_specNorm`** at two positions `X = u(0) u(0)ᵀ` and
`Y = u(t) u(t)ᵀ` of the rotating projector of rank one (`ρ = ρ' = 1`), whose column and row
spaces differ, and every `N`, `Z`. The algebraic lemmas
`Curvature.inner_normal_le_mul_mul_specNorm` and
`Curvature.specNorm_mul_compl_mul_specNorm_mul_compl_le_min` are applied in their proofs with the
Moore–Penrose inverse of `Y`. -/
example (t : ℝ) (N Z : Matrix (Fin 2) (Fin 2) ℝ) :
    ⟪rotProj t - tangentProjAt (rotProj 0) (rotProj t), N⟫ ≤
        (1 : ℝ)⁻¹ * ((1 +
          Curvature.specNorm ((rotProj t).rangeProj * (1 - (rotProj 0).rangeProj)) *
          Curvature.specNorm ((rotProj t)ᵀ.rangeProj * (1 - (rotProj 0)ᵀ.rangeProj))) / 2 *
          ‖rotProj t - rotProj 0‖ ^ 2) * Curvature.specNorm N ∧
      Curvature.specNorm ((rotProj t).rangeProj * (1 - (rotProj 0).rangeProj)) *
          Curvature.specNorm ((rotProj t)ᵀ.rangeProj * (1 - (rotProj 0)ᵀ.rangeProj)) ≤
        min 1 (((1 : ℝ)⁻¹ * ‖rotProj t - rotProj 0‖) ^ 2) ∧
      ⟪rotProj t - rotProj 0, tangentProjAt (rotProj t) Z - tangentProjAt (rotProj 0) Z⟫ ≤
        ((1 : ℝ)⁻¹ * ((1 +
            Curvature.specNorm ((rotProj 0).rangeProj * (1 - (rotProj t).rangeProj)) *
            Curvature.specNorm ((rotProj 0)ᵀ.rangeProj * (1 - (rotProj t)ᵀ.rangeProj))) / 2) *
            Curvature.specNorm (Z - tangentProjAt (rotProj t) Z) +
          (1 : ℝ)⁻¹ * ((1 +
            Curvature.specNorm ((rotProj t).rangeProj * (1 - (rotProj 0).rangeProj)) *
            Curvature.specNorm ((rotProj t)ᵀ.rangeProj * (1 - (rotProj 0)ᵀ.rangeProj))) / 2) *
            Curvature.specNorm (Z - tangentProjAt (rotProj 0) Z)) *
          ‖rotProj t - rotProj 0‖ ^ 2 :=
  ⟨inner_sub_tangentProjAt_le_inv_mul_specNorm (rank_rotProj t) one_pos
      (one_le_singularValues_rotProj t) N,
    specNorm_rangeProj_mul_mul_specNorm_rangeProj_mul_le_min (rank_rotProj t) one_pos
      (one_le_singularValues_rotProj t),
    inner_sub_tangentProjAt_sub_le_half_mul_specNorm (rank_rotProj 0) (rank_rotProj t) one_pos
      (one_le_singularValues_rotProj 0) one_pos (one_le_singularValues_rotProj t) Z⟩

/-- **Non-vacuity of `inner_sub_tangentProjAt_sub_le_of_norm_sub_le_of_specNorm_le`** at
`X = e₁ e₁ᵀ` and `Y = (3/2) e₁ e₁ᵀ ≠ X` (`r = 1`, `ρ = 1`, `ε = 1/2`) and every `Z`, with
`μ = ‖Z‖` and `ν = ‖Z - P(X) Z‖₂`. -/
example (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    ⟪(1 + 1 / 2 : ℝ) • (e₁ * e₁ᵀ) - (1 + 0 : ℝ) • (e₁ * e₁ᵀ),
        tangentProjAt ((1 + 1 / 2 : ℝ) • (e₁ * e₁ᵀ)) Z -
          tangentProjAt ((1 + 0 : ℝ) • (e₁ * e₁ᵀ)) Z⟫ ≤
      ((1 + min 1 ((1 / 2 / 1 : ℝ) ^ 2)) / 2 *
          (Curvature.specNorm (Z - tangentProjAt ((1 + 0 : ℝ) • (e₁ * e₁ᵀ)) Z) / 1 +
            ‖Z‖ * (1 / 2) / 1 ^ 2) +
        (1 + min 1 ((1 / 2 / (1 - 1 / 2) : ℝ) ^ 2)) / 2 *
          (Curvature.specNorm (Z - tangentProjAt ((1 + 0 : ℝ) • (e₁ * e₁ᵀ)) Z) / (1 - 1 / 2))) *
        ‖(1 + 1 / 2 : ℝ) • (e₁ * e₁ᵀ) - (1 + 0 : ℝ) • (e₁ * e₁ᵀ)‖ ^ 2 := by
  have e : (1 + 1 / 2 : ℝ) • (e₁ * e₁ᵀ) - (1 + 0 : ℝ) • (e₁ * e₁ᵀ) =
      (1 / 2 : ℝ) • (e₁ * e₁ᵀ) := by
    rw [← sub_smul]
    norm_num
  have he : ‖(1 + 1 / 2 : ℝ) • (e₁ * e₁ᵀ) - (1 + 0 : ℝ) • (e₁ * e₁ᵀ)‖ ≤ 1 / 2 := by
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    linarith [norm_e₁_mul_le]
  exact inner_sub_tangentProjAt_sub_le_of_norm_sub_le_of_specNorm_le
    (rank_smul_e₁ (by norm_num)) (rank_smul_e₁ (by norm_num))
    (one_le_singularValues_smul_e₁ (by norm_num)) he (by norm_num) le_rfl le_rfl

/-- The normal part `diag(0, 1/16)` of the examples. -/
local notation "N₁₆" => (!![0, 0; 0, 1 / 16] : Matrix (Fin 2) (Fin 2) ℝ)

private theorem norm_N₁₆_le : ‖N₁₆‖ ≤ 1 / 16 := by
  have h := norm_smul_e₁_sub_add_le 0
  rwa [sub_add_cancel_left, norm_neg] at h

private theorem tangentProjAt_smul_e₁_N₁₆ {c : ℝ} (hc : c ≠ 0) :
    tangentProjAt (c • (e₁ * e₁ᵀ)) N₁₆ = 0 := by
  have h1 : e₁ᵀ * N₁₆ = 0 := by
    ext i j
    fin_cases i
    fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h2 : N₁₆ * e₁ = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [tangentProjAt_smul_e₁ hc, tangentProj_apply, Matrix.mul_assoc e₁ e₁ᵀ N₁₆, h1, h2]
  simp

private theorem tangentProjAt_smul_e₁_add_N₁₆ {c : ℝ} (hc : c ≠ 0) :
    tangentProjAt (c • (e₁ * e₁ᵀ)) (e₁ * e₁ᵀ + N₁₆) = e₁ * e₁ᵀ := by
  rw [map_add, tangentProjAt_smul_e₁_apply hc, tangentProjAt_smul_e₁_N₁₆ hc, add_zero]

/-- `Y t = (1 + t) e₁ e₁ᵀ` is a DLRA solution of rank `1` for the field
`F = e₁ e₁ᵀ + diag(0, 1/16)`, whose normal part at `Y t` is `diag(0, 1/16) ≠ 0`. -/
private theorem isDLRASolution_smul_e₁_normal :
    IsDLRASolution 1 (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ + N₁₆)
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) 0 1 := by
  refine ⟨⟨fun s _ => (hasDerivAt_smul_e₁ 1 s).continuousAt.continuousWithinAt,
    fun s hs => ?_⟩, fun t ht => rank_smul_e₁ (ne_of_gt (by linarith [ht.1]))⟩
  have h := (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt (s := Ici s)
  convert h using 1
  exact tangentProjAt_smul_e₁_add_N₁₆ (ne_of_gt (by linarith [hs.1]))

private theorem hasDerivAt_smul_e₁_add_N₁₆ (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ + N₁₆)) (e₁ * e₁ᵀ + N₁₆) t := by
  simpa using ((hasDerivAt_id t).const_add 1).smul_const (e₁ * e₁ᵀ + N₁₆)

/-- The spectral norm of the normal velocity `diag(0, 1/16)` at `X t = (1 + t) e₁ e₁ᵀ`. -/
private theorem specNorm_sub_tangentProjAt_smul_e₁_le {t : ℝ} (ht : 0 ≤ t) :
    Curvature.specNorm (e₁ * e₁ᵀ + N₁₆ -
      tangentProjAt ((1 + t) • (e₁ * e₁ᵀ)) (e₁ * e₁ᵀ + N₁₆)) ≤ 1 / 16 := by
  rw [tangentProjAt_smul_e₁_add_N₁₆ (ne_of_gt (by linarith)), add_sub_cancel_left]
  exact (Curvature.specNorm_le_frob _).trans norm_N₁₆_le

/-- **Non-vacuity of
`IsDLRASolution.norm_sub_le_integral_exp_integral_of_specNorm_sub_tangentProjAt_le` (and of
`IsDLRASolution.norm_sub_le_integral_exp_integral_of_inner_tangentProjAt_sub_le`, through which
it is proved) with a normal velocity that does not vanish**: `2 × 2` matrices, `r = 1`, the field
`F = e₁ e₁ᵀ + diag(0, 1/16)` (`L = 0`), `A t = (1 + t) (e₁ e₁ᵀ + diag(0, 1/16))`, and
`X t = Y t = (1 + t) e₁ e₁ᵀ ≠ A t` on `[0, 1]`; `ρ = ρ' = 1`, `ν = ν' = 1/16`, `ς = 1`, `d = 0`,
`δ = 0`. -/
example : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(1 + t) • (e₁ * e₁ᵀ) - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
      Real.exp (∫ _ in (0 : ℝ)..t,
        ((0 : ℝ) + (1 + 1) / 2 * (1 / 16 / 1 + 1 / 16 / 1))) * 0 +
        ∫ s in (0 : ℝ)..t, Real.exp (∫ _ in s..t,
          ((0 : ℝ) + (1 + 1) / 2 * (1 / 16 / 1 + 1 / 16 / 1))) *
          (0 * ‖(1 + s) • (e₁ * e₁ᵀ) - (1 + s) • (e₁ * e₁ᵀ + N₁₆)‖ + 0) :=
  isDLRASolution_smul_e₁_normal.norm_sub_le_integral_exp_integral_of_specNorm_sub_tangentProjAt_le
    (A := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ + N₁₆))
    (X := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) (X' := fun _ => e₁ * e₁ᵀ)
    (ρ := fun _ => 1) (ρ' := fun _ => 1) (ν := fun _ => 1 / 16) (ν' := fun _ => 1 / 16)
    (ς := fun _ => 1) (d := fun _ => 0) le_rfl (fun _ _ _ => by simp)
    (fun s _ => (hasDerivAt_smul_e₁_add_N₁₆ s).continuousAt.continuousWithinAt)
    continuousOn_const continuousOn_const continuousOn_const continuousOn_const
    continuousOn_const continuousOn_const
    (fun s _ => (hasDerivAt_smul_e₁ 1 s).continuousAt.continuousWithinAt)
    (fun s _ => (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt)
    (fun t ht => rank_smul_e₁ (ne_of_gt (by linarith [ht.1])))
    (fun _ _ => one_pos)
    (fun t ht => one_le_singularValues_smul_e₁ (by linarith [ht.1]))
    (fun _ _ => one_pos)
    (fun t ht => one_le_singularValues_smul_e₁ (by linarith [ht.1]))
    (fun t ht => specNorm_sub_tangentProjAt_smul_e₁_le ht.1)
    (fun t ht => specNorm_sub_tangentProjAt_smul_e₁_le ht.1)
    (fun t ht =>
      ⟨(specNorm_rangeProj_mul_mul_specNorm_rangeProj_mul_le_min
          (rank_smul_e₁ (ne_of_gt (by linarith [ht.1]))) one_pos
          (one_le_singularValues_smul_e₁ (by linarith [ht.1]))).trans (min_le_left _ _),
        (specNorm_rangeProj_mul_mul_specNorm_rangeProj_mul_le_min
          (rank_smul_e₁ (ne_of_gt (by linarith [ht.1]))) one_pos
          (one_le_singularValues_smul_e₁ (by linarith [ht.1]))).trans (min_le_left _ _)⟩)
    (fun t ht => by
      rw [tangentProjAt_smul_e₁_add_N₁₆ (ne_of_gt (by linarith [ht.1])), sub_self, norm_zero])
    (by simp)

/-- **Non-vacuity of
`IsDLRASolution.norm_sub_le_integral_exp_integral_of_norm_sub_le_of_specNorm_le`** on the data
of the preceding example, with `ρ = 1`, `μ = 2`, `ν = 1/16`, `d = 0`, `ε = 1/2`, `δ = 0`. -/
example : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(1 + t) • (e₁ * e₁ᵀ) - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
      Real.exp (∫ _ in (0 : ℝ)..t, ((0 : ℝ) + ((1 + min 1 ((1 / 2 / 1) ^ 2)) / 2 * (1 / 16 / 1 + 2 *
      (1 / 2) / 1 ^ 2) + (1 + min 1 ((1 / 2 / (1 - 1 / 2)) ^ 2)) / 2 * (1 / 16 /
      (1 - 1 / 2))))) * 0 +
        ∫ s in (0 : ℝ)..t, Real.exp (∫ _ in s..t, ((0 : ℝ) + ((1 + min 1 ((1 / 2 / 1) ^ 2)) / 2 *
        (1 / 16 / 1 + 2 * (1 / 2) / 1 ^ 2) + (1 + min 1 ((1 / 2 / (1 - 1 / 2)) ^ 2)) / 2 * (1 / 16 /
        (1 - 1 / 2))))) *
          (0 * ‖(1 + s) • (e₁ * e₁ᵀ) - (1 + s) • (e₁ * e₁ᵀ + N₁₆)‖ + 0) :=
  isDLRASolution_smul_e₁_normal.norm_sub_le_integral_exp_integral_of_norm_sub_le_of_specNorm_le
    (A := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ + N₁₆))
    (X := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) (X' := fun _ => e₁ * e₁ᵀ)
    (ρ := fun _ => 1) (μ := fun _ => 2) (ν := fun _ => 1 / 16) (d := fun _ => 0)
    (ε := fun _ => 1 / 2) le_rfl (fun _ _ _ => by simp)
    (fun s _ => (hasDerivAt_smul_e₁_add_N₁₆ s).continuousAt.continuousWithinAt)
    continuousOn_const continuousOn_const continuousOn_const continuousOn_const
    continuousOn_const
    (fun s _ => (hasDerivAt_smul_e₁ 1 s).continuousAt.continuousWithinAt)
    (fun s _ => (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt)
    (fun t ht => rank_smul_e₁ (ne_of_gt (by linarith [ht.1])))
    (fun t ht => one_le_singularValues_smul_e₁ (by linarith [ht.1]))
    (fun _ _ => (norm_add_le _ _).trans (by linarith [norm_e₁_mul_le, norm_N₁₆_le]))
    (fun t ht => specNorm_sub_tangentProjAt_smul_e₁_le ht.1)
    (fun t ht => by
      rw [tangentProjAt_smul_e₁_add_N₁₆ (ne_of_gt (by linarith [ht.1])), sub_self, norm_zero])
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (fun t _ => by simp) (by simp)

/-- **Non-vacuity of
`IsDLRASolution.norm_sub_le_integral_exp_integral_of_integral_lt_of_specNorm_le`** on the same
data: the bound is `0 < ε = 1/2`. -/
example : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(1 + t) • (e₁ * e₁ᵀ) - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
      Real.exp (∫ _ in (0 : ℝ)..t, ((0 : ℝ) + ((1 + min 1 ((1 / 2 / 1) ^ 2)) / 2 * (1 / 16 / 1 + 2 *
      (1 / 2) / 1 ^ 2) + (1 + min 1 ((1 / 2 / (1 - 1 / 2)) ^ 2)) / 2 * (1 / 16 /
      (1 - 1 / 2))))) * 0 +
        ∫ s in (0 : ℝ)..t, Real.exp (∫ _ in s..t, ((0 : ℝ) + ((1 + min 1 ((1 / 2 / 1) ^ 2)) / 2 *
        (1 / 16 / 1 + 2 * (1 / 2) / 1 ^ 2) + (1 + min 1 ((1 / 2 / (1 - 1 / 2)) ^ 2)) / 2 * (1 / 16 /
        (1 - 1 / 2))))) *
          (0 * ‖(1 + s) • (e₁ * e₁ᵀ) - (1 + s) • (e₁ * e₁ᵀ + N₁₆)‖ + 0) :=
  isDLRASolution_smul_e₁_normal.norm_sub_le_integral_exp_integral_of_integral_lt_of_specNorm_le
    (A := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ + N₁₆))
    (X := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) (X' := fun _ => e₁ * e₁ᵀ)
    (ρ := fun _ => 1) (μ := fun _ => 2) (ν := fun _ => 1 / 16) (d := fun _ => 0)
    (ε := fun _ => 1 / 2) le_rfl (fun _ _ _ => by simp)
    (fun s _ => (hasDerivAt_smul_e₁_add_N₁₆ s).continuousAt.continuousWithinAt)
    continuousOn_const continuousOn_const continuousOn_const continuousOn_const
    continuousOn_const
    (fun s _ => (hasDerivAt_smul_e₁ 1 s).continuousAt.continuousWithinAt)
    (fun s _ => (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt)
    (fun t ht => rank_smul_e₁ (ne_of_gt (by linarith [ht.1])))
    (fun t ht => one_le_singularValues_smul_e₁ (by linarith [ht.1]))
    (fun _ _ => (norm_add_le _ _).trans (by linarith [norm_e₁_mul_le, norm_N₁₆_le]))
    (fun t ht => specNorm_sub_tangentProjAt_smul_e₁_le ht.1)
    (fun t ht => by
      rw [tangentProjAt_smul_e₁_add_N₁₆ (ne_of_gt (by linarith [ht.1])), sub_self, norm_zero])
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (by simp) (fun t _ => by simp)

/-- The rate of the last example is at most `1/2` where `σ₀(A) ≥ 1`. -/
private theorem abs_rate_le_half {σ : ℝ} (hσ : 1 ≤ σ) :
    |(0 : ℝ) + ((1 + min 1 ((1 / 2 / σ) ^ 2)) / 2 * (0 / σ + 1 * (1 / 2) / σ ^ 2) +
      (1 + min 1 ((1 / 2 / (σ - 1 / 2)) ^ 2)) / 2 * (0 / (σ - 1 / 2)))| ≤ 1 / 2 := by
  simp only [zero_div, add_zero, zero_add, mul_zero, one_mul]
  have hm0 : 0 ≤ min 1 ((1 / 2 / σ) ^ 2) := le_min zero_le_one (sq_nonneg _)
  have hm1 : min 1 ((1 / 2 / σ) ^ 2) ≤ 1 := min_le_left _ _
  have hq : 0 ≤ 1 / 2 / σ ^ 2 := by positivity
  rw [abs_of_nonneg (mul_nonneg (by linarith) hq)]
  calc (1 + min 1 ((1 / 2 / σ) ^ 2)) / 2 * (1 / 2 / σ ^ 2) ≤ 1 * (1 / 2 / σ ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hq
    _ ≤ 1 / 2 := by
        rw [one_mul]
        exact div_le_self (by norm_num) (one_le_pow₀ hσ)

/-- **Non-vacuity of
`IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_specNorm_le`** for `2 × 2`
matrices, `r = 1`, `A t = (1 + t) e₁ e₁ᵀ + diag(0, 1/16)` on `[0, 1]` and `F = e₁ e₁ᵀ` (`L = 0`,
`μ = 1`, `ν = 0`, `ω = 1/16`, `ε = 1/2`, `δ = 0`): the gap is `σ₁(A t) ≤ 1/16 < 1 ≤ σ₀(A t)`,
`T₁(A t) = (1 + t) e₁ e₁ᵀ` differs from `A t` and is the DLRA solution `Y`, the rate is at most
`1/2` and the source `ρ/(ρ - τ) ω` at most `1/15`, so that the bound stays below `ε`. -/
example : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(1 + t) • (e₁ * e₁ᵀ) - EckartYoung.truncation ((1 + t) • (e₁ * e₁ᵀ) + N₁₆) 1‖ ≤
      Real.exp (∫ u in (0 : ℝ)..t, ((0 : ℝ) + ((1 + min 1 ((1 / 2 / (toEuclideanLin ((1 +
      u) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1)) ^ 2)) / 2 * (0 / (toEuclideanLin ((1 +
      u) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1) + 1 * (1 / 2) / (toEuclideanLin ((1 +
      u) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1) ^ 2) + (1 + min 1 ((1 / 2 /
      ((toEuclideanLin ((1 + u) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1) - 1 / 2)) ^ 2)) / 2 *
      (0 / ((toEuclideanLin ((1 + u) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1) - 1 / 2))))) * 0 +
        ∫ s in (0 : ℝ)..t, Real.exp (∫ u in s..t, ((0 : ℝ) + ((1 + min 1 ((1 / 2 /
        (toEuclideanLin ((1 + u) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1)) ^ 2)) / 2 * (0 /
        (toEuclideanLin ((1 + u) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1) + 1 * (1 / 2) /
        (toEuclideanLin ((1 + u) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1) ^ 2) + (1 +
        min 1 ((1 / 2 / ((toEuclideanLin ((1 + u) • (e₁ * e₁ᵀ) +
        N₁₆)).singularValues (1 - 1) - 1 / 2)) ^ 2)) / 2 * (0 / ((toEuclideanLin ((1 +
        u) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1) - 1 / 2))))) *
          (0 * ‖EckartYoung.truncation ((1 + s) • (e₁ * e₁ᵀ) + N₁₆) 1 - ((1 + s) • (e₁ * e₁ᵀ) +
          N₁₆)‖ + (toEuclideanLin ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1) /
          ((toEuclideanLin ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1) -
          (toEuclideanLin ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)).singularValues 1) * (1 / 16)) :=
  isDLRASolution_smul_e₁_tangent.norm_sub_truncation_le_integral_exp_integral_of_specNorm_le
    (A := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) (μ := fun _ => 1) (ν := fun _ => 0)
    (ω := fun _ => 1 / 16) (ε := fun _ => 1 / 2) le_rfl (fun _ _ _ => by simp)
    ⟨fun s _ => (hasDerivAt_smul_e₁_add_const s).continuousAt.continuousWithinAt,
      fun s _ => (hasDerivAt_smul_e₁_add_const s).hasDerivWithinAt⟩
    continuousOn_const continuousOn_const continuousOn_const continuousOn_const
    (fun _ _ => norm_e₁_mul_le)
    (fun t ht => by
      rw [truncation_smul_e₁_add ht.1,
        tangentProjAt_smul_e₁_apply (ne_of_gt (by linarith [ht.1])), sub_self]
      exact (Curvature.specNorm_le_frob _).trans (by rw [norm_zero]))
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
      refine integral_exp_integral_mul_lt_half ht
        (fun u hu => abs_rate_le_half (one_le_singularValues_smul_e₁_add hu)) (fun s hs => ?_)
      have h1 := one_le_singularValues_smul_e₁_add hs
      have h2 := singularValues_one_smul_e₁_add_le hs
      have h0 := (toEuclideanLin ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)).singularValues_nonneg 1
      rw [zero_mul, zero_add, abs_of_nonneg
        (mul_nonneg (div_nonneg (by linarith) (by linarith)) (by norm_num)),
        div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      linarith)

end QuasiOptimalityNormalVelocitySpectralExamples

end LeanDLRA
