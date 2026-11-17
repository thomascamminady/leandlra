import LeanDLRA.DLRA.QuasiOptimalityGap
import LeanDLRA.DLRA.QuasiOptimalityNormal
import LeanDLRA.DLRA.Existence

/-!
# Quasi-optimality of matrix DLRA with the Lipschitz constant `1` of the tangent projector

`LeanDLRA/DLRA/QuasiOptimalityNormal.lean` proves the quasi-optimality bound

  `‖Y t - X t‖ ≤ e^{(L + μ/ρ + κ)(t - a)} (δ + (L + κ) ∫ₐᵗ ‖X s - A s‖ ds)`,
  `κ = μ / ((1 - θ) ρ)`,

under the margin `‖X t - A t‖ ≤ θ ρ`, `θ < 1`, from the Lipschitz bound of the tangent projector
with the constant `1`. This file carries the bound to the other forms of the theorem, which the
library has with the margin `ρ / 4` and the constants `L + 6 μ / ρ` and `L + 4 μ / ρ`: the error
against `A`, a curve of best approximations, a field that is Lipschitz on a tube around `A`, and
the truncated SVD under a gap. It also has the Lipschitz constant `B / ρ + L` of the projected
field `Y ↦ P(Y) F(t, Y)` in place of `2 B / ρ + L`.

## Main results

* `dlra_norm_sub_le_add_integral_of_margin_lt_one`: the bound for `‖Y t - A t‖`.
* `IsDLRASolution.norm_sub_le_integral_of_forall_norm_sub_le_of_margin_lt_one`: `X` a curve of
  best approximations of rank at most `r`.
* `IsDLRASolution.norm_sub_lt_of_isLipschitzOnTube_of_margin_lt_one`,
  `IsDLRASolution.norm_sub_le_integral_of_isLipschitzOnTube_of_margin_lt_one`,
  `IsDLRASolution.norm_sub_le_integral_of_forall_norm_sub_le_of_isLipschitzOnTube_of_lt_one`:
  a field Lipschitz on a tube; the smallness condition is the one with the smaller bound.
* `IsDLRASolution.norm_sub_truncation_le_integral_of_gap_of_margin_lt_one`,
  `IsDLRASolution.norm_sub_truncation_le_integral_of_gap_of_isLipschitzOnTube_of_lt_one`:
  `X t = T_r(A t)` under a gap.
* `norm_tangentProjAt_field_sub_le_inv_mul`:
  `‖P(Y) F(t, Y) - P(X) F(t, X)‖ ≤ (B / ρ + L) ‖Y - X‖`.

## Implementation notes

The proofs are those of `LeanDLRA/DLRA/QuasiOptimality.lean`,
`LeanDLRA/DLRA/QuasiOptimalityTube.lean` and `LeanDLRA/DLRA/QuasiOptimalityGap.lean` with
`IsDLRASolution.norm_sub_le_integral_of_margin_lt_one` in place of
`IsDLRASolution.norm_sub_le_integral`. The `example`s restate the theorems of these files
verbatim and prove them from the theorems of this file with `θ = 1 / 4`: for `μ ≥ 0` the bound
with `L + μ/ρ + 4 μ / (3 ρ)` and `L + 4 μ / (3 ρ)` is at most the bound with `L + 6 μ / ρ` and
`L + 4 μ / ρ`.

## References

* [KochLubich2007]
* [ZhaoOstermannGu2021]
-/

open Set Matrix Filter
open scoped Topology LeanDLRA.Frobenius

namespace LeanDLRA

open EckartYoung

section Sharp

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-! ### The error against `A` and curves of best approximations -/

/-- **Quasi-optimality of matrix DLRA, error against `A`, margin `θ ρ` with `θ < 1`.** Under the
hypotheses of `dlra_norm_sub_le_integral_of_margin_lt_one`, with `κ = μ / ((1 - θ) ρ)`, for
`t ∈ [a, b]`
`‖Y t - A t‖ ≤ ‖X t - A t‖ + e^{(L + μ/ρ + κ)(t - a)} (δ + (L + κ) ∫ₐᵗ ‖X s - A s‖ ds)`. -/
theorem dlra_norm_sub_le_add_integral_of_margin_lt_one {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ θ δ : ℝ}
    (hρ : 0 < ρ) (hL : 0 ≤ L) (hF : IsLipschitzField F L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ θ * ρ)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t x => tangentProj (U t) (V t) (F t x)) Y a b)
    (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ ‖X t - A t‖ +
      Real.exp ((L + μ / ρ + μ / ((1 - θ) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - θ) * ρ)) * ∫ s in a..t, ‖X s - A s‖) := by
  intro t ht
  have h := dlra_norm_sub_le_integral_of_margin_lt_one hρ hL hF hA hμ hXc hX hXr hσ hopt hθ hd
    hUV hY hδ t ht
  calc ‖Y t - A t‖ ≤ ‖Y t - X t‖ + ‖X t - A t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

/-- **Quasi-optimality of matrix DLRA for a curve of best approximations, margin `θ ρ` with
`θ < 1`.** The bound of `IsDLRASolution.norm_sub_le_integral_of_margin_lt_one` for a curve `X` of
best approximations of `A` of rank at most `r` (`‖A t - X t‖ ≤ ‖A t - Z‖` for every `Z` of rank
at most `r`) with `0 < ρ ≤ σ_{r-1}(X t)` and `‖X t - A t‖ ≤ θ ρ`. -/
theorem IsDLRASolution.norm_sub_le_integral_of_forall_norm_sub_le_of_margin_lt_one {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ θ δ : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hbest : ∀ t ∈ Icc a b, (X t).rank ≤ r ∧
      ∀ Z : Matrix m n ℝ, Z.rank ≤ r → ‖A t - X t‖ ≤ ‖A t - Z‖)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1)) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ θ * ρ)
    (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + μ / ρ + μ / ((1 - θ) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - θ) * ρ)) * ∫ s in a..t, ‖X s - A s‖) := by
  have hXr : ∀ t ∈ Icc a b, (X t).rank = r := fun t ht => by
    have hpos : 0 < (toEuclideanLin (X t)).singularValues (r - 1) := hρ.trans_le (hσ t ht)
    rw [LinearMap.singularValues_pos_iff_lt_finrank_range, ← SVD.rank_eq_finrank_range] at hpos
    have := (hbest t ht).1
    omega
  exact hY.norm_sub_le_integral_of_margin_lt_one hρ hL hF hA hμ hXc hX hXr hσ
    (fun t ht => tangentProjAt_sub_eq_zero_of_forall_norm_sub_le (hbest t ht).1 (hbest t ht).2)
    hθ hd hδ

/-! ### A field that is Lipschitz on a tube -/

/-- The bound of `IsDLRASolution.norm_sub_le_integral_of_margin_lt_one` at a time `t₁ ∈ [a, b]`
up to which the solution has stayed in the tube on which `F` is Lipschitz. -/
private theorem norm_sub_le_integral_of_forall_Ico_norm_sub_le_of_margin {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ}
    {a b L μ ρ θ δ R : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hF : IsLipschitzOnTube F A a b R L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ θ * ρ)
    (hδ : ‖Y a - X a‖ ≤ δ) {t : ℝ} (ht : t ∈ Icc a b) (hin : ∀ s ∈ Ico a t, ‖Y s - A s‖ ≤ R) :
    ‖Y t - X t‖ ≤
      Real.exp ((L + μ / ρ + μ / ((1 - θ) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - θ) * ρ)) * ∫ s in a..t, ‖X s - A s‖) := by
  have hIcc : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hIco : ∀ s ∈ Ico a t, s ∈ Ico a b := fun s hs => ⟨hs.1, hs.2.trans_le ht.2⟩
  have hAt : ∀ s ∈ Icc a b, tubeExt F A a b R s (A s) = F s (A s) := fun s hs =>
    tubeExt_eq hs (by rw [sub_self, norm_zero]; exact hR)
  have hAG := hA.tubeExt_self hR
  have hYG : IsDLRASolution r (tubeExt F A a b R) Y a t := by
    refine ⟨⟨hY.1.cont.mono hIcc, fun s hs => ?_⟩, fun s hs => hY.2 s (hIcc hs)⟩
    have h : HasDerivWithinAt Y (tangentProjAt (Y s) (F s (Y s))) (Ici s) s :=
      hY.1.deriv s (hIco s hs)
    change HasDerivWithinAt Y (tangentProjAt (Y s) (tubeExt F A a b R s (Y s))) (Ici s) s
    rwa [tubeExt_eq (Ico_subset_Icc_self (hIco s hs)) (hin s hs)]
  exact hYG.norm_sub_le_integral_of_margin_lt_one hρ hL (isLipschitzField_tubeExt hF hL hR)
    ⟨hAG.cont.mono hIcc, fun s hs => hAG.deriv s (hIco s hs)⟩
    (fun s hs => by rw [hAt s (Ico_subset_Icc_self (hIco s hs))]; exact hμ s (hIco s hs))
    (hXc.mono hIcc) (fun s hs => hX s (hIco s hs)) (fun s hs => hXr s (hIcc hs))
    (fun s hs => hσ s (hIcc hs)) (fun s hs => hopt s (hIcc hs)) hθ (fun s hs => hd s (hIcc hs))
    hδ t ⟨ht.1, le_rfl⟩

/-- **The DLRA solution stays in the tube, margin `θ ρ` with `θ < 1`.** Under the hypotheses of
`IsDLRASolution.norm_sub_lt_of_isLipschitzOnTube`, with the margin `‖X t - A t‖ ≤ θ ρ`, `θ < 1`,
and with the smallness condition for the bound of
`IsDLRASolution.norm_sub_le_integral_of_margin_lt_one`: `‖Y t - A t‖ < R` for `t ∈ [a, b]`. -/
theorem IsDLRASolution.norm_sub_lt_of_isLipschitzOnTube_of_margin_lt_one {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ}
    {a b L μ ρ θ δ R : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hF : IsLipschitzOnTube F A a b R L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ θ * ρ)
    (hδ : ‖Y a - X a‖ ≤ δ)
    (hsmall : ∀ t ∈ Icc a b, ‖X t - A t‖ +
      Real.exp ((L + μ / ρ + μ / ((1 - θ) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - θ) * ρ)) * ∫ s in a..t, ‖X s - A s‖) < R) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ < R := by
  intro t ht
  have hR : 0 ≤ R := by
    have h := hsmall a ⟨le_rfl, ht.1.trans ht.2⟩
    simp only [sub_self, mul_zero, Real.exp_zero, intervalIntegral.integral_same, add_zero,
      one_mul] at h
    linarith [norm_nonneg (X a - A a), norm_nonneg (Y a - X a)]
  have hb := bootstrap_of_continuousOn (e := fun t => ‖Y t - A t‖)
    (β := fun t => ‖X t - A t‖ + Real.exp ((L + μ / ρ + μ / ((1 - θ) * ρ)) * (t - a)) *
      (δ + (L + μ / ((1 - θ) * ρ)) * ∫ s in a..t, ‖X s - A s‖))
    (hY.1.cont.sub hA.cont).norm hsmall fun t ht hin => by
      have h := norm_sub_le_integral_of_forall_Ico_norm_sub_le_of_margin hY hρ hL hR hF hA hμ
        hXc hX hXr hσ hopt hθ hd hδ ht hin
      calc ‖Y t - A t‖ ≤ ‖Y t - X t‖ + ‖X t - A t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ _ := by linarith
  exact (hb t ht).trans_lt (hsmall t ht)

/-- **Quasi-optimality of matrix DLRA for a field Lipschitz on a tube, margin `θ ρ` with
`θ < 1`.** Under the hypotheses of
`IsDLRASolution.norm_sub_lt_of_isLipschitzOnTube_of_margin_lt_one` the bound of
`IsDLRASolution.norm_sub_le_integral_of_margin_lt_one` holds on `[a, b]`. -/
theorem IsDLRASolution.norm_sub_le_integral_of_isLipschitzOnTube_of_margin_lt_one {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ}
    {a b L μ ρ θ δ R : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hF : IsLipschitzOnTube F A a b R L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ θ * ρ)
    (hδ : ‖Y a - X a‖ ≤ δ)
    (hsmall : ∀ t ∈ Icc a b, ‖X t - A t‖ +
      Real.exp ((L + μ / ρ + μ / ((1 - θ) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - θ) * ρ)) * ∫ s in a..t, ‖X s - A s‖) < R) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + μ / ρ + μ / ((1 - θ) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - θ) * ρ)) * ∫ s in a..t, ‖X s - A s‖) := by
  intro t ht
  have hin := hY.norm_sub_lt_of_isLipschitzOnTube_of_margin_lt_one hρ hL hF hA hμ hXc hX hXr hσ
    hopt hθ hd hδ hsmall
  have hR : 0 ≤ R := (norm_nonneg _).trans (hin t ht).le
  exact norm_sub_le_integral_of_forall_Ico_norm_sub_le_of_margin hY hρ hL hR hF hA hμ hXc hX hXr
    hσ hopt hθ hd hδ ht fun s hs => (hin s ⟨hs.1, hs.2.le.trans ht.2⟩).le

/-- **The same for a curve of best approximations.** The bound of
`IsDLRASolution.norm_sub_le_integral_of_isLipschitzOnTube_of_margin_lt_one` for a curve `X` of
best approximations of `A` of rank at most `r`. -/
theorem IsDLRASolution.norm_sub_le_integral_of_forall_norm_sub_le_of_isLipschitzOnTube_of_lt_one
    {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ}
    {a b L μ ρ θ δ R : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hF : IsLipschitzOnTube F A a b R L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hbest : ∀ t ∈ Icc a b, (X t).rank ≤ r ∧
      ∀ Z : Matrix m n ℝ, Z.rank ≤ r → ‖A t - X t‖ ≤ ‖A t - Z‖)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1)) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ θ * ρ)
    (hδ : ‖Y a - X a‖ ≤ δ)
    (hsmall : ∀ t ∈ Icc a b, ‖X t - A t‖ +
      Real.exp ((L + μ / ρ + μ / ((1 - θ) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - θ) * ρ)) * ∫ s in a..t, ‖X s - A s‖) < R) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + μ / ρ + μ / ((1 - θ) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - θ) * ρ)) * ∫ s in a..t, ‖X s - A s‖) := by
  have hXr : ∀ t ∈ Icc a b, (X t).rank = r := fun t ht => by
    have hpos : 0 < (toEuclideanLin (X t)).singularValues (r - 1) := hρ.trans_le (hσ t ht)
    rw [LinearMap.singularValues_pos_iff_lt_finrank_range, ← SVD.rank_eq_finrank_range] at hpos
    have := (hbest t ht).1
    omega
  exact hY.norm_sub_le_integral_of_isLipschitzOnTube_of_margin_lt_one hρ hL hF hA hμ hXc hX hXr hσ
    (fun t ht => tangentProjAt_sub_eq_zero_of_forall_norm_sub_le (hbest t ht).1 (hbest t ht).2)
    hθ hd hδ hsmall

/-! ### The truncated SVD under a gap -/

/-- Under a gap `ρ ≤ σ_{r-1}(A t) - σ_r(A t)` along a solution `A` of `Ȧ = F(t, A)`, the curve
`X t = T_r(A t)` is continuous on `[a, b]`, has right derivatives on `[a, b)`, is a best
approximation of rank at most `r`, and `ρ ≤ σ_{r-1}(X t)`. -/
private theorem truncation_hyps_of_gap_aux {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A : ℝ → Matrix m n ℝ} {a b ρ : ℝ} (hA : ODESolution F A a b)
    (hgap : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1) -
      (toEuclideanLin (A t)).singularValues r) (hρ : 0 < ρ) :
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

/-- **Quasi-optimality of matrix DLRA against the truncated SVD under a gap, margin `θ ρ` with
`θ < 1`.** Under the hypotheses of `IsDLRASolution.norm_sub_truncation_le_integral_of_gap`, with
`‖T_r(A t) - A t‖ ≤ θ ρ`, `θ < 1`, in place of `‖T_r(A t) - A t‖ ≤ ρ / 4`, and with
`κ = μ / ((1 - θ) ρ)`, for `t ∈ [a, b]`
`‖Y t - T_r(A t)‖ ≤ e^{(L + μ/ρ + κ)(t - a)} (δ + (L + κ) ∫ₐᵗ ‖T_r(A s) - A s‖ ds)`. -/
theorem IsDLRASolution.norm_sub_truncation_le_integral_of_gap_of_margin_lt_one {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A Y : ℝ → Matrix m n ℝ} {a b L μ ρ θ δ : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hA : ODESolution F A a b) (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ)
    (hgap : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1) -
      (toEuclideanLin (A t)).singularValues r) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc a b, ‖truncation (A t) r - A t‖ ≤ θ * ρ)
    (hδ : ‖Y a - truncation (A a) r‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - truncation (A t) r‖ ≤
      Real.exp ((L + μ / ρ + μ / ((1 - θ) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - θ) * ρ)) * ∫ s in a..t, ‖truncation (A s) r - A s‖) := by
  obtain ⟨hXc, hX, hbest, hσ⟩ := truncation_hyps_of_gap_aux hA hgap hρ
  exact hY.norm_sub_le_integral_of_forall_norm_sub_le_of_margin_lt_one hρ hL hF hA hμ hXc hX
    hbest hσ hθ hd hδ

/-- **The same for a field Lipschitz on a tube.** The bound of
`IsDLRASolution.norm_sub_truncation_le_integral_of_gap_of_margin_lt_one` when `F` is
`L`-Lipschitz only on the tube `‖x - A t‖ ≤ R`, if the bound plus `‖T_r(A t) - A t‖` stays below
`R` on `[a, b]`. -/
theorem IsDLRASolution.norm_sub_truncation_le_integral_of_gap_of_isLipschitzOnTube_of_lt_one
    {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A Y : ℝ → Matrix m n ℝ}
    {a b L μ ρ θ δ R : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hF : IsLipschitzOnTube F A a b R L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ)
    (hgap : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1) -
      (toEuclideanLin (A t)).singularValues r) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc a b, ‖truncation (A t) r - A t‖ ≤ θ * ρ)
    (hδ : ‖Y a - truncation (A a) r‖ ≤ δ)
    (hsmall : ∀ t ∈ Icc a b, ‖truncation (A t) r - A t‖ +
      Real.exp ((L + μ / ρ + μ / ((1 - θ) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - θ) * ρ)) * ∫ s in a..t, ‖truncation (A s) r - A s‖) < R) :
    ∀ t ∈ Icc a b, ‖Y t - truncation (A t) r‖ ≤
      Real.exp ((L + μ / ρ + μ / ((1 - θ) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - θ) * ρ)) * ∫ s in a..t, ‖truncation (A s) r - A s‖) := by
  obtain ⟨hXc, hX, hbest, hσ⟩ := truncation_hyps_of_gap_aux hA hgap hρ
  exact
    hY.norm_sub_le_integral_of_forall_norm_sub_le_of_isLipschitzOnTube_of_lt_one hρ hL
      hF hA hμ hXc hX hbest hσ hθ hd hδ hsmall

/-! ### The projected field -/

/-- **The projected field is Lipschitz with the constant `B / ρ + L`.** For a field `F` that is
`L`-Lipschitz and bounded by `B`, and `X`, `Y` of rank `r` with `0 < ρ ≤ σ_{r-1}(X)`:
`‖P(Y) F(t, Y) - P(X) F(t, X)‖ ≤ (B / ρ + L) ‖Y - X‖`. -/
theorem norm_tangentProjAt_field_sub_le_inv_mul {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {L B : ℝ} (hF : IsLipschitzField F L) (hB : IsBoundedField F B) {X Y : Matrix m n ℝ}
    (hX : X.rank = r) (hY : Y.rank = r) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) (t : ℝ) :
    ‖tangentProjAt Y (F t Y) - tangentProjAt X (F t X)‖ ≤ (ρ⁻¹ * B + L) * ‖Y - X‖ := by
  have h1 := norm_tangentProjAt_sub_le_inv_mul hX hY hρ hσ (F t Y)
  have h2 : ‖tangentProjAt X (F t Y - F t X)‖ ≤ L * ‖Y - X‖ :=
    ((isOrthProj_tangentProjAt X).norm_le _).trans (hF t Y X)
  have h3 : ρ⁻¹ * ‖Y - X‖ * ‖F t Y‖ ≤ ρ⁻¹ * ‖Y - X‖ * B :=
    mul_le_mul_of_nonneg_left (hB t Y) (mul_nonneg (inv_nonneg.2 hρ.le) (norm_nonneg _))
  calc ‖tangentProjAt Y (F t Y) - tangentProjAt X (F t X)‖
      = ‖(tangentProjAt Y (F t Y) - tangentProjAt X (F t Y)) +
          tangentProjAt X (F t Y - F t X)‖ := by
        rw [map_sub]
        congr 1
        abel
    _ ≤ ‖tangentProjAt Y (F t Y) - tangentProjAt X (F t Y)‖ +
          ‖tangentProjAt X (F t Y - F t X)‖ := norm_add_le _ _
    _ ≤ (ρ⁻¹ * B + L) * ‖Y - X‖ := by linarith

/-! ### The theorems with the margin `ρ / 4` -/

/-- With `θ = 1 / 4` the bound with the constants `L + μ/ρ + μ / ((1 - θ) ρ)` and
`L + μ / ((1 - θ) ρ)` is at most the bound with `L + 6 μ / ρ` and `L + 4 μ / ρ`, if `μ ≥ 0` or
`t = a` (where the integral `I` is zero). -/
private theorem bound_quarter_le {a t L μ ρ δ I : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hat : a ≤ t) (hI : 0 ≤ I) (hμ : a < t → 0 ≤ μ) (h0 : t = a → I = 0) :
    Real.exp ((L + μ / ρ + μ / ((1 - 1 / 4) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - 1 / 4) * ρ)) * I) ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) * (δ + (L + 4 * μ / ρ) * I) := by
  rcases eq_or_lt_of_le hat with h | h
  · rw [h0 h.symm, ← h]
    simp
  · have hμ0 := hμ h
    have e1 : μ / ((1 - 1 / 4) * ρ) = 4 / 3 * μ / ρ := by
      rw [div_eq_div_iff (mul_pos (by norm_num) hρ).ne' hρ.ne']
      ring
    have k0 : 0 ≤ 4 / 3 * μ / ρ := div_nonneg (by linarith) hρ.le
    have k1 : 4 / 3 * μ / ρ ≤ 4 * μ / ρ := div_le_div_of_nonneg_right (by linarith) hρ.le
    have k2 : μ / ρ + 4 / 3 * μ / ρ ≤ 6 * μ / ρ := by
      have e : μ / ρ + 4 / 3 * μ / ρ = 7 / 3 * μ / ρ := by ring
      rw [e]
      exact div_le_div_of_nonneg_right (by linarith) hρ.le
    rw [e1]
    exact mul_le_mul
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) (by linarith)))
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (by linarith) hI))
      (add_nonneg hδ (mul_nonneg (by linarith) hI)) (Real.exp_nonneg _)

/-- `dlra_norm_sub_le_add_integral`, restated verbatim, follows from
`dlra_norm_sub_le_add_integral_of_margin_lt_one` with `θ = 1 / 4`. -/
example {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ δ : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hF : IsLipschitzField F L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ ρ / 4)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t x => tangentProj (U t) (V t) (F t x)) Y a b)
    (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ ‖X t - A t‖ +
      Real.exp ((L + 6 * μ / ρ) * (t - a)) * (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖) := by
  have hm : ∀ t ∈ Icc a b,
      Real.exp ((L + μ / ρ + μ / ((1 - 1 / 4) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - 1 / 4) * ρ)) * ∫ s in a..t, ‖X s - A s‖) ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) *
        (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖) := fun t ht =>
    bound_quarter_le hρ hL ((norm_nonneg _).trans hδ) ht.1
      (intervalIntegral.integral_nonneg ht.1 fun _ _ => norm_nonneg _)
      (fun h => (norm_nonneg _).trans (hμ a ⟨le_rfl, h.trans_le ht.2⟩))
      (fun h => by rw [h, intervalIntegral.integral_same])
  intro t ht
  have h := dlra_norm_sub_le_add_integral_of_margin_lt_one (θ := 1 / 4) hρ hL hF hA hμ hXc hX hXr
    hσ hopt (by norm_num) (fun t ht => (hd t ht).trans_eq (by ring)) hUV hY hδ t ht
  have h' := hm t ht
  linarith

/-- `IsDLRASolution.norm_sub_le_integral_of_forall_norm_sub_le`, restated verbatim, follows from
`IsDLRASolution.norm_sub_le_integral_of_forall_norm_sub_le_of_margin_lt_one` with `θ = 1 / 4`. -/
example {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ δ : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hbest : ∀ t ∈ Icc a b, (X t).rank ≤ r ∧
      ∀ Z : Matrix m n ℝ, Z.rank ≤ r → ‖A t - X t‖ ≤ ‖A t - Z‖)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ ρ / 4) (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) * (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖) := by
  have hm : ∀ t ∈ Icc a b,
      Real.exp ((L + μ / ρ + μ / ((1 - 1 / 4) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - 1 / 4) * ρ)) * ∫ s in a..t, ‖X s - A s‖) ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) *
        (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖) := fun t ht =>
    bound_quarter_le hρ hL ((norm_nonneg _).trans hδ) ht.1
      (intervalIntegral.integral_nonneg ht.1 fun _ _ => norm_nonneg _)
      (fun h => (norm_nonneg _).trans (hμ a ⟨le_rfl, h.trans_le ht.2⟩))
      (fun h => by rw [h, intervalIntegral.integral_same])
  exact fun t ht => (hY.norm_sub_le_integral_of_forall_norm_sub_le_of_margin_lt_one (θ := 1 / 4)
    hρ hL hF hA hμ hXc hX hbest hσ (by norm_num) (fun t ht => (hd t ht).trans_eq (by ring)) hδ t
    ht).trans (hm t ht)

/-- `IsDLRASolution.norm_sub_lt_of_isLipschitzOnTube` and
`IsDLRASolution.norm_sub_le_integral_of_isLipschitzOnTube`, restated verbatim, follow from the
theorems with the margin `θ ρ` with `θ = 1 / 4`: the smallness condition with the constants
`L + 6 μ / ρ`, `L + 4 μ / ρ` implies the one with the smaller constants. -/
example {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ δ R : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hF : IsLipschitzOnTube F A a b R L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ ρ / 4) (hδ : ‖Y a - X a‖ ≤ δ)
    (hsmall : ∀ t ∈ Icc a b, ‖X t - A t‖ + Real.exp ((L + 6 * μ / ρ) * (t - a)) *
      (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖) < R) :
    (∀ t ∈ Icc a b, ‖Y t - A t‖ < R) ∧ ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) * (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖) := by
  have hm : ∀ t ∈ Icc a b,
      Real.exp ((L + μ / ρ + μ / ((1 - 1 / 4) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - 1 / 4) * ρ)) * ∫ s in a..t, ‖X s - A s‖) ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) *
        (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖) := fun t ht =>
    bound_quarter_le hρ hL ((norm_nonneg _).trans hδ) ht.1
      (intervalIntegral.integral_nonneg ht.1 fun _ _ => norm_nonneg _)
      (fun h => (norm_nonneg _).trans (hμ a ⟨le_rfl, h.trans_le ht.2⟩))
      (fun h => by rw [h, intervalIntegral.integral_same])
  have hs : ∀ t ∈ Icc a b, ‖X t - A t‖ +
      Real.exp ((L + μ / ρ + μ / ((1 - 1 / 4) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - 1 / 4) * ρ)) * ∫ s in a..t, ‖X s - A s‖) < R := fun t ht => by
    have h1 := hm t ht
    have h2 := hsmall t ht
    linarith
  exact ⟨hY.norm_sub_lt_of_isLipschitzOnTube_of_margin_lt_one (θ := 1 / 4) hρ hL hF hA hμ hXc hX
      hXr hσ hopt (by norm_num) (fun t ht => (hd t ht).trans_eq (by ring)) hδ hs,
    fun t ht => (hY.norm_sub_le_integral_of_isLipschitzOnTube_of_margin_lt_one (θ := 1 / 4) hρ hL
      hF hA hμ hXc hX hXr hσ hopt (by norm_num) (fun t ht => (hd t ht).trans_eq (by ring)) hδ hs t
      ht).trans (hm t ht)⟩

/-- `IsDLRASolution.norm_sub_le_integral_of_forall_norm_sub_le_of_isLipschitzOnTube`, restated
verbatim, follows from the theorem with the margin `θ ρ` with `θ = 1 / 4`. -/
example {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ δ R : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hF : IsLipschitzOnTube F A a b R L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hbest : ∀ t ∈ Icc a b, (X t).rank ≤ r ∧
      ∀ Z : Matrix m n ℝ, Z.rank ≤ r → ‖A t - X t‖ ≤ ‖A t - Z‖)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ ρ / 4) (hδ : ‖Y a - X a‖ ≤ δ)
    (hsmall : ∀ t ∈ Icc a b, ‖X t - A t‖ + Real.exp ((L + 6 * μ / ρ) * (t - a)) *
      (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖) < R) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) * (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖) := by
  have hm : ∀ t ∈ Icc a b,
      Real.exp ((L + μ / ρ + μ / ((1 - 1 / 4) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - 1 / 4) * ρ)) * ∫ s in a..t, ‖X s - A s‖) ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) *
        (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖) := fun t ht =>
    bound_quarter_le hρ hL ((norm_nonneg _).trans hδ) ht.1
      (intervalIntegral.integral_nonneg ht.1 fun _ _ => norm_nonneg _)
      (fun h => (norm_nonneg _).trans (hμ a ⟨le_rfl, h.trans_le ht.2⟩))
      (fun h => by rw [h, intervalIntegral.integral_same])
  have hs : ∀ t ∈ Icc a b, ‖X t - A t‖ +
      Real.exp ((L + μ / ρ + μ / ((1 - 1 / 4) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - 1 / 4) * ρ)) * ∫ s in a..t, ‖X s - A s‖) < R := fun t ht => by
    have h1 := hm t ht
    have h2 := hsmall t ht
    linarith
  exact fun t ht =>
    (hY.norm_sub_le_integral_of_forall_norm_sub_le_of_isLipschitzOnTube_of_lt_one
      (θ := 1 / 4) hρ hL hF hA hμ hXc hX hbest hσ (by norm_num)
      (fun t ht => (hd t ht).trans_eq (by ring)) hδ hs t ht).trans (hm t ht)

/-- `IsDLRASolution.norm_sub_truncation_le_integral_of_gap` and
`IsDLRASolution.norm_sub_truncation_le_integral_of_gap_of_isLipschitzOnTube`, restated verbatim
(the second with its hypotheses after those of the first), follow from the theorems with the
margin `θ ρ` with `θ = 1 / 4`. -/
example {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A Y : ℝ → Matrix m n ℝ} {a b L μ ρ δ R : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hA : ODESolution F A a b) (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ)
    (hgap : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1) -
      (toEuclideanLin (A t)).singularValues r)
    (hd : ∀ t ∈ Icc a b, ‖truncation (A t) r - A t‖ ≤ ρ / 4)
    (hδ : ‖Y a - truncation (A a) r‖ ≤ δ) :
    (IsLipschitzField F L → ∀ t ∈ Icc a b, ‖Y t - truncation (A t) r‖ ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) *
        (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖truncation (A s) r - A s‖)) ∧
    (IsLipschitzOnTube F A a b R L → (∀ t ∈ Icc a b, ‖truncation (A t) r - A t‖ +
      Real.exp ((L + 6 * μ / ρ) * (t - a)) *
        (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖truncation (A s) r - A s‖) < R) →
      ∀ t ∈ Icc a b, ‖Y t - truncation (A t) r‖ ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) *
        (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖truncation (A s) r - A s‖)) := by
  have hm : ∀ t ∈ Icc a b,
      Real.exp ((L + μ / ρ + μ / ((1 - 1 / 4) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - 1 / 4) * ρ)) * ∫ s in a..t, ‖truncation (A s) r - A s‖) ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) *
        (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖truncation (A s) r - A s‖) := fun t ht =>
    bound_quarter_le hρ hL ((norm_nonneg _).trans hδ) ht.1
      (intervalIntegral.integral_nonneg ht.1 fun _ _ => norm_nonneg _)
      (fun h => (norm_nonneg _).trans (hμ a ⟨le_rfl, h.trans_le ht.2⟩))
      (fun h => by rw [h, intervalIntegral.integral_same])
  refine ⟨fun hF t ht => (hY.norm_sub_truncation_le_integral_of_gap_of_margin_lt_one (θ := 1 / 4)
    hρ hL hF hA hμ hgap (by norm_num) (fun t ht => (hd t ht).trans_eq (by ring)) hδ t ht).trans
    (hm t ht), fun hF hsmall t ht => ?_⟩
  have hs : ∀ t ∈ Icc a b, ‖truncation (A t) r - A t‖ +
      Real.exp ((L + μ / ρ + μ / ((1 - 1 / 4) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - 1 / 4) * ρ)) * ∫ s in a..t, ‖truncation (A s) r - A s‖) < R :=
    fun t ht => by
      have h1 := hm t ht
      have h2 := hsmall t ht
      linarith
  exact (hY.norm_sub_truncation_le_integral_of_gap_of_isLipschitzOnTube_of_lt_one
    (θ := 1 / 4) hρ hL hF hA hμ hgap (by norm_num) (fun t ht => (hd t ht).trans_eq (by ring)) hδ hs
    t ht).trans (hm t ht)

/-- `norm_tangentProjAt_field_sub_le`, restated verbatim, follows from
`norm_tangentProjAt_field_sub_le_inv_mul`. -/
example {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B : ℝ} (hF : IsLipschitzField F L)
    (hB : IsBoundedField F B) {X Y : Matrix m n ℝ} (hX : X.rank = r) (hY : Y.rank = r) {ρ : ℝ}
    (hρ : 0 < ρ) (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) (t : ℝ) :
    ‖tangentProjAt Y (F t Y) - tangentProjAt X (F t X)‖ ≤ (2 * ρ⁻¹ * B + L) * ‖Y - X‖ := by
  have h := norm_tangentProjAt_field_sub_le_inv_mul hF hB hX hY hρ hσ t
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t Y)
  have h0 : 0 ≤ ρ⁻¹ * B * ‖Y - X‖ :=
    mul_nonneg (mul_nonneg (inv_nonneg.2 hρ.le) hB0) (norm_nonneg _)
  linarith

end Sharp

end LeanDLRA
