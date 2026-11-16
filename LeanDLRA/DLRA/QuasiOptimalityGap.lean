import LeanDLRA.DLRA.QuasiOptimalityTube
import LeanDLRA.LinearAlgebra.SVD.TruncationDeriv

/-!
# Quasi-optimality of dynamical low-rank approximation against the truncated SVD under a gap

The quasi-optimality bounds of `LeanDLRA/DLRA/QuasiOptimality.lean` and
`LeanDLRA/DLRA/QuasiOptimalityTube.lean` compare the DLRA solution `Y` with a curve `X` of best
approximations of rank `r` that is continuous and has right derivatives. This file takes
`X t = T_r(A t)`, the truncated SVD of the exact solution, and replaces these hypotheses on `X`
by a gap `ρ ≤ σ_{r-1}(A t) - σ_r(A t)` along the solution: under the gap, `T_r` is
differentiable (`EckartYoung.hasFDerivAt_truncation`), so `t ↦ T_r(A t)` has right derivatives,
it is a best approximation (Eckart–Young), and `σ_{r-1}(T_r(A t)) ≥ ρ` (Weyl).

## Main results

* `IsDLRASolution.norm_sub_truncation_le_integral_of_gap`: for a globally Lipschitz field,
  `‖Y t - T_r(A t)‖ ≤ e^{(L + 6 μ/ρ)(t - a)} (δ + (L + 4 μ/ρ) ∫ₐᵗ ‖T_r(A s) - A s‖ ds)`.
* `IsDLRASolution.norm_sub_truncation_le_integral_of_gap_of_isLipschitzOnTube`: the same for a
  field that is Lipschitz only on a tube around `A`, under the smallness condition of
  `IsDLRASolution.norm_sub_le_integral_of_isLipschitzOnTube`.

## References

* [KochLubich2007]
-/

open Set Matrix Filter
open scoped Topology LeanDLRA.Frobenius

namespace LeanDLRA

open EckartYoung

section Gap

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Under a gap `ρ ≤ σ_{r-1}(A t) - σ_r(A t)` along a solution `A` of `Ȧ = F(t, A)`, the curve
`X t = T_r(A t)` satisfies the hypotheses on `X` of the quasi-optimality theorems: it is
continuous on `[a, b]`, has the right derivatives `D T_r(A t) F(t, A t)` on `[a, b)`, is a best
approximation of rank at most `r`, and `ρ ≤ σ_{r-1}(X t)`. -/
private theorem truncation_hyps_of_gap {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A : ℝ → Matrix m n ℝ} {a b ρ : ℝ} (hρ : 0 < ρ) (hA : ODESolution F A a b)
    (hgap : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1) -
      (toEuclideanLin (A t)).singularValues r) :
    ContinuousOn (fun t => truncation (A t) r) (Icc a b) ∧
    (∀ t ∈ Ico a b, HasDerivWithinAt (fun t => truncation (A t) r)
      (fderiv ℝ (fun B => truncation B r) (A t) (F t (A t))) (Ici t) t) ∧
    (∀ t ∈ Icc a b, (truncation (A t) r).rank ≤ r ∧
      ∀ Z : Matrix m n ℝ, Z.rank ≤ r → ‖A t - truncation (A t) r‖ ≤ ‖A t - Z‖) ∧
    (∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (truncation (A t) r)).singularValues (r - 1)) := by
  have hlt : ∀ t ∈ Icc a b, (toEuclideanLin (A t)).singularValues r <
      (toEuclideanLin (A t)).singularValues (r - 1) := fun t ht => by
    have := hgap t ht
    linarith
  refine ⟨fun t ht => (continuousAt_truncation (hlt t ht)).comp_continuousWithinAt (hA.cont t ht),
    fun t ht => hasDerivWithinAt_truncation (hA.deriv t ht) (hlt t (Ico_subset_Icc_self ht)),
    fun t _ => ⟨rank_truncation_le (A t) r, fun Z hZ => norm_sub_truncation_le (A t) hZ⟩,
    fun t ht => ?_⟩
  have hW := WeylSingular.abs_singularValues_sub_le (A t) (truncation (A t) r) (r - 1)
  rw [specNorm_sub_truncation] at hW
  have := hgap t ht
  linarith [(abs_le.1 hW).2]

/-- **Quasi-optimality of matrix DLRA against the truncated SVD under a gap.** Let `Y` be a DLRA
solution of rank `r` of `Ẏ = P(Y) F(t, Y)` on `[a, b]` (`IsDLRASolution`) and `A` a solution of
`Ȧ = F(t, A)` with `F` `L`-Lipschitz and `‖Ȧ‖ ≤ μ`. If the singular values of `A` have the gap
`ρ ≤ σ_{r-1}(A t) - σ_r(A t)`, `ρ > 0`, and `‖T_r(A t) - A t‖ ≤ ρ / 4` on `[a, b]`, and
`‖Y a - T_r(A a)‖ ≤ δ`, then for `t ∈ [a, b]`
`‖Y t - T_r(A t)‖ ≤ e^{(L + 6 μ/ρ)(t - a)} (δ + (L + 4 μ/ρ) ∫ₐᵗ ‖T_r(A s) - A s‖ ds)`.
No differentiability of the truncated SVD is assumed: it follows from the gap. A bound of this
kind is in [KochLubich2007]; the constants are those of this proof. -/
theorem IsDLRASolution.norm_sub_truncation_le_integral_of_gap {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A Y : ℝ → Matrix m n ℝ} {a b L μ ρ δ : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hA : ODESolution F A a b) (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ)
    (hgap : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1) -
      (toEuclideanLin (A t)).singularValues r)
    (hd : ∀ t ∈ Icc a b, ‖truncation (A t) r - A t‖ ≤ ρ / 4)
    (hδ : ‖Y a - truncation (A a) r‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - truncation (A t) r‖ ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) *
        (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖truncation (A s) r - A s‖) := by
  obtain ⟨hXc, hX, hbest, hσ⟩ := truncation_hyps_of_gap hρ hA hgap
  exact hY.norm_sub_le_integral_of_forall_norm_sub_le hρ hL hF hA hμ hXc hX hbest hσ hd hδ

/-- **The same for a field Lipschitz on a tube.** The bound of
`IsDLRASolution.norm_sub_truncation_le_integral_of_gap` when `F` is `L`-Lipschitz only on the
tube `‖x - A t‖ ≤ R`, provided
`‖T_r(A t) - A t‖ + e^{(L + 6 μ/ρ)(t - a)} (δ + (L + 4 μ/ρ) ∫ₐᵗ ‖T_r(A s) - A s‖ ds) < R` on
`[a, b]` (`IsDLRASolution.norm_sub_le_integral_of_forall_norm_sub_le_of_isLipschitzOnTube`). -/
theorem IsDLRASolution.norm_sub_truncation_le_integral_of_gap_of_isLipschitzOnTube {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A Y : ℝ → Matrix m n ℝ} {a b L μ ρ δ R : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hF : IsLipschitzOnTube F A a b R L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ)
    (hgap : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1) -
      (toEuclideanLin (A t)).singularValues r)
    (hd : ∀ t ∈ Icc a b, ‖truncation (A t) r - A t‖ ≤ ρ / 4)
    (hδ : ‖Y a - truncation (A a) r‖ ≤ δ)
    (hsmall : ∀ t ∈ Icc a b, ‖truncation (A t) r - A t‖ +
      Real.exp ((L + 6 * μ / ρ) * (t - a)) *
        (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖truncation (A s) r - A s‖) < R) :
    ∀ t ∈ Icc a b, ‖Y t - truncation (A t) r‖ ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) *
        (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖truncation (A s) r - A s‖) := by
  obtain ⟨hXc, hX, hbest, hσ⟩ := truncation_hyps_of_gap hρ hA hgap
  exact hY.norm_sub_le_integral_of_forall_norm_sub_le_of_isLipschitzOnTube hρ hL hF hA hμ hXc hX
    hbest hσ hd hδ hsmall

end Gap

/-! ### Example -/

section Examples

/-- The first unit column of `ℝ²`. -/
local notation "e₁" => (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)

private theorem e₁_transpose_mul_self : e₁ᵀ * e₁ = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem smul_e₁_mul (c : ℝ) :
    c • (e₁ * e₁ᵀ) = e₁ * (c • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * e₁ᵀ := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

private theorem isUnit_det_smul_one {c : ℝ} (hc : c ≠ 0) :
    IsUnit (c • (1 : Matrix (Fin 1) (Fin 1) ℝ)).det := by
  rw [det_smul, det_one, mul_one, Fintype.card_fin, pow_one]
  exact isUnit_iff_ne_zero.mpr hc

private theorem rank_smul_e₁ {c : ℝ} (hc : c ≠ 0) : (c • (e₁ * e₁ᵀ)).rank = 1 :=
  (SVD.rank_eq_iff_exists_factor _).2 ⟨e₁, c • 1, e₁, e₁_transpose_mul_self,
    e₁_transpose_mul_self, isUnit_det_smul_one hc, smul_e₁_mul c⟩

private theorem rank_smul_e₁_le (c : ℝ) : (c • (e₁ * e₁ᵀ)).rank ≤ 1 := by
  rw [smul_e₁_mul]
  exact (rank_mul_le_right _ _).trans (by simpa using rank_le_card_height e₁ᵀ)

private theorem tangentProjAt_smul_e₁_apply {c : ℝ} (hc : c ≠ 0) :
    tangentProjAt (c • (e₁ * e₁ᵀ)) (e₁ * e₁ᵀ) = e₁ * e₁ᵀ := by
  have h := tangentProjAt_self (c • (e₁ * e₁ᵀ))
  rw [map_smul] at h
  exact smul_right_injective _ hc h

private theorem norm_e₁_mul_le : ‖e₁ * e₁ᵀ‖ ≤ 1 := by
  have h : ‖e₁ * e₁ᵀ‖ ^ 2 = 1 := by
    rw [Curvature.frob_sq]
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  nlinarith [norm_nonneg (e₁ * e₁ᵀ)]

/-- The gap `σ₀(c e₁ e₁ᵀ) - σ₁(c e₁ e₁ᵀ) ≥ 1` for `c ≥ 1`. -/
private theorem one_le_gap_smul_e₁ {c : ℝ} (hc : 1 ≤ c) :
    (1 : ℝ) ≤ (toEuclideanLin (c • (e₁ * e₁ᵀ))).singularValues (1 - 1) -
      (toEuclideanLin (c • (e₁ * e₁ᵀ))).singularValues 1 := by
  have h0 : (toEuclideanLin (c • (e₁ * e₁ᵀ))).singularValues 1 ≤ 0 := by
    have h := EckartYoung.singularValues_le_specNorm_sub (c • (e₁ * e₁ᵀ)) (c • (e₁ * e₁ᵀ))
      (rank_smul_e₁_le c)
    rw [sub_self] at h
    exact h.trans ((Curvature.specNorm_le_frob 0).trans_eq norm_zero)
  have h1 : (1 : ℝ) ≤ (toEuclideanLin (c • (e₁ * e₁ᵀ))).singularValues (1 - 1) := by
    refine SVD.le_singularValues_of_eq_mul one_pos e₁_transpose_mul_self e₁_transpose_mul_self
      (smul_e₁_mul c) fun w => ?_
    rw [LinearEquiv.map_smul, toLpLin_one]
    change 1 * ‖w‖ ≤ ‖c • w‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    nlinarith [norm_nonneg w]
  linarith

private theorem hasDerivAt_smul_e₁ (c t : ℝ) :
    HasDerivAt (fun t : ℝ => (c + t) • (e₁ * e₁ᵀ)) (e₁ * e₁ᵀ) t := by
  simpa using ((hasDerivAt_id t).const_add c).smul_const (e₁ * e₁ᵀ)

/-- `IsDLRASolution.norm_sub_truncation_le_integral_of_gap` for `A t = (1 + t) e₁ e₁ᵀ`, the
solution of `Ȧ = F(t, A) = e₁ e₁ᵀ` (`L = 0`, `μ = 1`), whose singular values have the gap
`σ₀ - σ₁ ≥ 1 = ρ`, and the DLRA solution `Y t = (17/16 + t) e₁ e₁ᵀ` of rank `1` (`Y ≠ T₁(A)`,
`δ = 1/16`) on `[0, 1]`. -/
example : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(17 / 16 + t) • (e₁ * e₁ᵀ) - truncation ((1 + t) • (e₁ * e₁ᵀ)) 1‖ ≤
      Real.exp ((0 + 6 * 1 / 1) * (t - 0)) * (1 / 16 + (0 + 4 * 1 / 1) *
        ∫ s in (0 : ℝ)..t, ‖truncation ((1 + s) • (e₁ * e₁ᵀ)) 1 - (1 + s) • (e₁ * e₁ᵀ)‖) := by
  have hT : ∀ c : ℝ, truncation (c • (e₁ * e₁ᵀ)) 1 = c • (e₁ * e₁ᵀ) :=
    fun c => EckartYoung.truncation_eq_self (rank_smul_e₁_le c)
  have hY : IsDLRASolution 1 (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ)
      (fun t : ℝ => (17 / 16 + t) • (e₁ * e₁ᵀ)) 0 1 := by
    refine ⟨⟨fun s _ => (hasDerivAt_smul_e₁ (17 / 16) s).continuousAt.continuousWithinAt,
      fun s hs => ?_⟩, fun t ht => rank_smul_e₁ (ne_of_gt (by linarith [ht.1]))⟩
    have h := (hasDerivAt_smul_e₁ (17 / 16) s).hasDerivWithinAt (s := Ici s)
    convert h using 1
    exact tangentProjAt_smul_e₁_apply (ne_of_gt (by linarith [hs.1]))
  have hF : IsLipschitzField (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ) 0 :=
    fun _ _ _ => by simp
  have hA : ODESolution (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ)
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) 0 1 :=
    ⟨fun s _ => (hasDerivAt_smul_e₁ 1 s).continuousAt.continuousWithinAt,
      fun s _ => (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt⟩
  have hμ : ∀ t ∈ Ico (0 : ℝ) 1, ‖(fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ) t
      ((fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) t)‖ ≤ 1 := fun _ _ => norm_e₁_mul_le
  have hgap : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (1 : ℝ) ≤ (toEuclideanLin ((1 + t) • (e₁ * e₁ᵀ))).singularValues (1 - 1) -
        (toEuclideanLin ((1 + t) • (e₁ * e₁ᵀ))).singularValues 1 :=
    fun t ht => one_le_gap_smul_e₁ (by linarith [ht.1])
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖truncation ((1 + t) • (e₁ * e₁ᵀ)) 1 - (1 + t) • (e₁ * e₁ᵀ)‖ ≤ 1 / 4 :=
    fun t _ => by rw [hT, sub_self, norm_zero]; norm_num
  have hδ : ‖(17 / 16 + 0 : ℝ) • (e₁ * e₁ᵀ) - truncation ((1 + 0 : ℝ) • (e₁ * e₁ᵀ)) 1‖ ≤
      1 / 16 := by
    have h : (17 / 16 + 0 : ℝ) - (1 + 0) = 1 / 16 := by norm_num
    rw [hT, ← sub_smul, h, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 16)]
    exact mul_le_of_le_one_right (by norm_num) norm_e₁_mul_le
  have r := hY.norm_sub_truncation_le_integral_of_gap (A := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ))
    one_pos le_rfl hF hA hμ hgap hd hδ
  exact r

end Examples

end LeanDLRA
