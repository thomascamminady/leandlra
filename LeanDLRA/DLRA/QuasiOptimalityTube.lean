import LeanDLRA.DLRA.QuasiOptimality
import LeanDLRA.Foundations.Localization

/-!
# Quasi-optimality of dynamical low-rank approximation for a field Lipschitz near the solution

The quasi-optimality bounds of `LeanDLRA/DLRA/QuasiOptimality.lean` assume that the right-hand
side `F` of `Ȧ = F(t, A)` is Lipschitz on the whole space. This file proves the bound for a field
that is `L`-Lipschitz only on the tube `‖x - A t‖ ≤ R` around the exact solution `A`
(`IsLipschitzOnTube`), under the condition that the bound, added to the approximation error
`‖X t - A t‖`, stays below the radius `R` on `[a, b]`. The DLRA solution then never leaves the
tube, and the bound holds with the constants of the global case. All norms are Frobenius norms.

## Main results

* `IsDLRASolution.norm_sub_lt_of_isLipschitzOnTube`: the DLRA solution stays inside the tube,
  `‖Y t - A t‖ < R` on `[a, b]`.
* `IsDLRASolution.norm_sub_le_integral_of_isLipschitzOnTube`: for a DLRA solution `Y` of rank `r`
  of `Ẏ = P(Y) F(t, Y)` and a curve `X` of critical points of the distance to `A`,
  `‖Y t - X t‖ ≤ e^{(L + 6 μ/ρ)(t - a)} (δ + (L + 4 μ/ρ) ∫ₐᵗ ‖X - A‖)`.
* `IsDLRASolution.norm_sub_le_integral_of_forall_norm_sub_le_of_isLipschitzOnTube`: the same for
  a curve `X` of best approximations of rank at most `r`.

## Implementation notes

The field is replaced by its global extension `tubeExt F A a b R`, which is `L`-Lipschitz on the
whole space and agrees with `F` on the tube (`isLipschitzField_tubeExt`, `tubeExt_eq`). On every
interval `[a, t]` on which `Y` has stayed in the tube, `Y` is a DLRA solution of the extended
field, so the global bound `IsDLRASolution.norm_sub_le_integral` applies there; with
`‖Y - A‖ ≤ ‖Y - X‖ + ‖X - A‖` it keeps `Y` strictly inside the tube, and the continuity argument
`bootstrap_of_continuousOn` of `LeanDLRA/Foundations/Localization.lean` extends this to
`[a, b]`. The tube hypotheses are those of
[ZhaoOstermannGu2021]; a bound of this kind for a globally Lipschitz field is in
[KochLubich2007].

## References

* [KochLubich2007]
* [ZhaoOstermannGu2021]
-/

open Set Matrix Filter
open scoped Topology

namespace LeanDLRA

/-! ### Quasi-optimality on a tube -/

section Tube

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The bound of `IsDLRASolution.norm_sub_le_integral` at a time `t₁ ∈ [a, b]` up to which the
solution has stayed in the tube on which `F` is Lipschitz. -/
private theorem norm_sub_le_integral_of_forall_Ico_norm_sub_le {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ δ R : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hF : IsLipschitzOnTube F A a b R L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ ρ / 4) (hδ : ‖Y a - X a‖ ≤ δ) {t₁ : ℝ}
    (ht₁ : t₁ ∈ Icc a b) (hin : ∀ s ∈ Ico a t₁, ‖Y s - A s‖ ≤ R) :
    ‖Y t₁ - X t₁‖ ≤ Real.exp ((L + 6 * μ / ρ) * (t₁ - a)) *
      (δ + (L + 4 * μ / ρ) * ∫ s in a..t₁, ‖X s - A s‖) := by
  have hIcc : Icc a t₁ ⊆ Icc a b := Icc_subset_Icc_right ht₁.2
  have hIco : ∀ s ∈ Ico a t₁, s ∈ Ico a b := fun s hs => ⟨hs.1, hs.2.trans_le ht₁.2⟩
  have hAt : ∀ s ∈ Icc a b, tubeExt F A a b R s (A s) = F s (A s) := fun s hs =>
    tubeExt_eq hs (by rw [sub_self, norm_zero]; exact hR)
  have hAG := hA.tubeExt_self hR
  have hYG : IsDLRASolution r (tubeExt F A a b R) Y a t₁ := by
    refine ⟨⟨hY.1.cont.mono hIcc, fun s hs => ?_⟩, fun s hs => hY.2 s (hIcc hs)⟩
    have h : HasDerivWithinAt Y (tangentProjAt (Y s) (F s (Y s))) (Ici s) s :=
      hY.1.deriv s (hIco s hs)
    change HasDerivWithinAt Y (tangentProjAt (Y s) (tubeExt F A a b R s (Y s))) (Ici s) s
    rwa [tubeExt_eq (Ico_subset_Icc_self (hIco s hs)) (hin s hs)]
  exact hYG.norm_sub_le_integral hρ hL (isLipschitzField_tubeExt hF hL hR)
    ⟨hAG.cont.mono hIcc, fun s hs => hAG.deriv s (hIco s hs)⟩
    (fun s hs => by rw [hAt s (Ico_subset_Icc_self (hIco s hs))]; exact hμ s (hIco s hs))
    (hXc.mono hIcc) (fun s hs => hX s (hIco s hs)) (fun s hs => hXr s (hIcc hs))
    (fun s hs => hσ s (hIcc hs)) (fun s hs => hopt s (hIcc hs)) (fun s hs => hd s (hIcc hs))
    hδ t₁ ⟨ht₁.1, le_rfl⟩

/-- **The DLRA solution stays in the tube.** Let `F` be `L`-Lipschitz on the tube of radius `R`
around a solution `A` of `Ȧ = F(t, A)` on `[a, b]` with `‖Ȧ‖ ≤ μ`, let `X` and `Y` be as in
`IsDLRASolution.norm_sub_le_integral`, and let the bound of that theorem, added to the
approximation error, stay below the radius:
`‖X t - A t‖ + e^{(L + 6 μ/ρ)(t - a)} (δ + (L + 4 μ/ρ) ∫ₐᵗ ‖X s - A s‖ ds) < R` on `[a, b]`.
Then `‖Y t - A t‖ < R` for `t ∈ [a, b]`. -/
theorem IsDLRASolution.norm_sub_lt_of_isLipschitzOnTube {r : ℕ}
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
    ∀ t ∈ Icc a b, ‖Y t - A t‖ < R := by
  intro t ht
  have hR : 0 ≤ R := by
    have h := hsmall a ⟨le_rfl, ht.1.trans ht.2⟩
    simp only [sub_self, mul_zero, Real.exp_zero, intervalIntegral.integral_same, add_zero,
      one_mul] at h
    linarith [norm_nonneg (X a - A a), norm_nonneg (Y a - X a)]
  have hb := bootstrap_of_continuousOn (e := fun t => ‖Y t - A t‖)
    (β := fun t => ‖X t - A t‖ + Real.exp ((L + 6 * μ / ρ) * (t - a)) *
      (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖))
    (hY.1.cont.sub hA.cont).norm hsmall fun t ht hin => by
      have h := norm_sub_le_integral_of_forall_Ico_norm_sub_le hY hρ hL hR hF hA hμ hXc hX hXr
        hσ hopt hd hδ ht hin
      calc ‖Y t - A t‖ ≤ ‖Y t - X t‖ + ‖X t - A t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ _ := by linarith
  exact (hb t ht).trans_lt (hsmall t ht)

/-- **Quasi-optimality of matrix DLRA for a field Lipschitz on a tube.** Let `Y` be a DLRA
solution of rank `r` of `Ẏ = P(Y) F(t, Y)` on `[a, b]` (`IsDLRASolution`), `A` a solution of
`Ȧ = F(t, A)` with `‖Ȧ‖ ≤ μ`, where `F` is `L`-Lipschitz only on the tube `‖x - A t‖ ≤ R`
(`IsLipschitzOnTube`), and `X` a curve of rank `r`, continuous on `[a, b]` with right derivatives,
with `0 < ρ ≤ σ_{r-1}(X t)`, `P(X t) (A t - X t) = 0` and `‖X t - A t‖ ≤ ρ / 4`. If
`‖Y a - X a‖ ≤ δ` and
`‖X t - A t‖ + e^{(L + 6 μ/ρ)(t - a)} (δ + (L + 4 μ/ρ) ∫ₐᵗ ‖X s - A s‖ ds) < R` on `[a, b]`, then
for `t ∈ [a, b]`
`‖Y t - X t‖ ≤ e^{(L + 6 μ/ρ)(t - a)} (δ + (L + 4 μ/ρ) ∫ₐᵗ ‖X s - A s‖ ds)`.
The constants are those of `IsDLRASolution.norm_sub_le_integral`. -/
theorem IsDLRASolution.norm_sub_le_integral_of_isLipschitzOnTube {r : ℕ}
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
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) * (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖) := by
  intro t ht
  have hin := hY.norm_sub_lt_of_isLipschitzOnTube hρ hL hF hA hμ hXc hX hXr hσ hopt hd hδ hsmall
  have hR : 0 ≤ R := (norm_nonneg _).trans (hin t ht).le
  exact norm_sub_le_integral_of_forall_Ico_norm_sub_le hY hρ hL hR hF hA hμ hXc hX hXr hσ hopt hd
    hδ ht fun s hs => (hin s ⟨hs.1, hs.2.le.trans ht.2⟩).le

/-- **Quasi-optimality of matrix DLRA for a curve of best approximations and a field Lipschitz
on a tube.** The bound of `IsDLRASolution.norm_sub_le_integral_of_isLipschitzOnTube` for a curve
`X` of best approximations of `A` of rank at most `r` (`‖A t - X t‖ ≤ ‖A t - Z‖` for every `Z` of
rank at most `r`), continuous on `[a, b]` with right derivatives, with `0 < ρ ≤ σ_{r-1}(X t)` and
`‖X t - A t‖ ≤ ρ / 4`:
`‖Y t - X t‖ ≤ e^{(L + 6 μ/ρ)(t - a)} (δ + (L + 4 μ/ρ) ∫ₐᵗ ‖X s - A s‖ ds)` on `[a, b]`, if the
right side plus `‖X t - A t‖` stays below the radius `R` of the tube on which `F` is
`L`-Lipschitz. -/
theorem IsDLRASolution.norm_sub_le_integral_of_forall_norm_sub_le_of_isLipschitzOnTube {r : ℕ}
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
  have hXr : ∀ t ∈ Icc a b, (X t).rank = r := fun t ht => by
    have hpos : 0 < (toEuclideanLin (X t)).singularValues (r - 1) := hρ.trans_le (hσ t ht)
    rw [LinearMap.singularValues_pos_iff_lt_finrank_range, ← SVD.rank_eq_finrank_range] at hpos
    have := (hbest t ht).1
    omega
  exact hY.norm_sub_le_integral_of_isLipschitzOnTube hρ hL hF hA hμ hXc hX hXr hσ
    (fun t ht => tangentProjAt_sub_eq_zero_of_forall_norm_sub_le (hbest t ht).1 (hbest t ht).2)
    hd hδ hsmall

end Tube

/-! ### Examples -/

section Examples

open scoped LeanDLRA.Frobenius
open QuasiOptimalityExamples

/-- The matrix unit `E₂₂ = diag(0, 1)`. -/
local notation "E₂₂" => (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)

/-- The curve `X t = (1 + t) e₁ e₁ᵀ` of the examples. -/
local notation "Xₑ" => fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)

/-- The curve `A t = X t + diag(0, 1/8)` of the examples. -/
local notation "Aₑ" => fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + (1 / 8 : ℝ) • E₂₂

/-- The DLRA solution `Y t = (17/16 + t) e₁ e₁ᵀ` of the examples (`Y ≠ X`). -/
local notation "Yₑ" => fun t : ℝ => (17 / 16 + t) • (e₁ * e₁ᵀ)

/-- The quadratic field `F(t, x) = e₁ e₁ᵀ + (x₂₂ - 1/8)² E₂₂` of the examples: Lipschitz on every
tube around `A`, not on the whole space. -/
local notation "Fₑ" => fun (_ : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ) =>
  e₁ * e₁ᵀ + (x 1 1 - 1 / 8) ^ 2 • E₂₂

private theorem tangentProjAt_smul_e₁_E₂₂ {c : ℝ} (hc : c ≠ 0) :
    tangentProjAt (c • (e₁ * e₁ᵀ)) E₂₂ = 0 := by
  have h1 : e₁ᵀ * E₂₂ = 0 := by
    ext i j
    fin_cases i
    fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h2 : E₂₂ * e₁ = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [tangentProjAt_smul_e₁ hc, tangentProj_apply, Matrix.mul_assoc e₁ e₁ᵀ E₂₂, h1, h2]
  simp

private theorem norm_E₂₂_le : ‖E₂₂‖ ≤ 1 := by
  have h : ‖E₂₂‖ ^ 2 = 1 := by
    rw [Curvature.frob_sq]
    norm_num [Fin.sum_univ_two]
  nlinarith [norm_nonneg E₂₂]

private theorem norm_smul_E₂₂_le : ‖(1 / 8 : ℝ) • E₂₂‖ ≤ 1 / 8 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  nlinarith [norm_E₂₂_le]

private theorem smul_e₁_add_eq (t : ℝ) :
    (1 + t) • (e₁ * e₁ᵀ) + (1 / 8 : ℝ) • E₂₂ = !![1 + t, 0; 0, 1 / 8] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Function.swap, Matrix.vecHead, Matrix.vecTail]

private theorem smul_e₁_add_apply (t : ℝ) :
    ((1 + t) • (e₁ * e₁ᵀ) + (1 / 8 : ℝ) • E₂₂) 1 1 = 1 / 8 := by
  rw [smul_e₁_add_eq]
  simp

/-- The field of the examples is `2`-Lipschitz on the tube of radius `1` around `A`. -/
private theorem isLipschitzOnTube_example :
    IsLipschitzOnTube Fₑ Aₑ 0 (1 / 8) 1 2 := by
  intro t _ x y hx hy
  have hent : ∀ z : Matrix (Fin 2) (Fin 2) ℝ, ‖z - ((1 + t) • (e₁ * e₁ᵀ) +
      (1 / 8 : ℝ) • E₂₂)‖ ≤ 1 → |z 1 1 - 1 / 8| ≤ 1 := fun z hz => by
    have h := Frobenius.abs_apply_le_norm (z - ((1 + t) • (e₁ * e₁ᵀ) + (1 / 8 : ℝ) • E₂₂)) 1 1
    rw [Matrix.sub_apply, smul_e₁_add_apply] at h
    exact h.trans hz
  have h1 := hent x hx
  have h2 := hent y hy
  have h3 : |x 1 1 - y 1 1| ≤ ‖x - y‖ := by
    simpa using Frobenius.abs_apply_le_norm (x - y) 1 1
  have e : e₁ * e₁ᵀ + (x 1 1 - 1 / 8) ^ 2 • E₂₂ - (e₁ * e₁ᵀ + (y 1 1 - 1 / 8) ^ 2 • E₂₂) =
      ((x 1 1 - y 1 1) * ((x 1 1 - 1 / 8) + (y 1 1 - 1 / 8))) • E₂₂ := by
    rw [add_sub_add_left_eq_sub, ← sub_smul]
    congr 1
    ring
  have h4 : |(x 1 1 - 1 / 8) + (y 1 1 - 1 / 8)| ≤ 2 := (abs_add_le _ _).trans (by linarith)
  change ‖e₁ * e₁ᵀ + (x 1 1 - 1 / 8) ^ 2 • E₂₂ - (e₁ * e₁ᵀ + (y 1 1 - 1 / 8) ^ 2 • E₂₂)‖ ≤
    2 * ‖x - y‖
  rw [e, norm_smul, Real.norm_eq_abs, abs_mul]
  calc |x 1 1 - y 1 1| * |(x 1 1 - 1 / 8) + (y 1 1 - 1 / 8)| * ‖E₂₂‖ ≤ ‖x - y‖ * 2 * 1 :=
        mul_le_mul (mul_le_mul h3 h4 (abs_nonneg _) (norm_nonneg _)) norm_E₂₂_le
          (norm_nonneg _) (by positivity)
    _ = 2 * ‖x - y‖ := by ring

/-- Along `A` and along every multiple of `e₁ e₁ᵀ`, the projected field is `e₁ e₁ᵀ`. -/
private theorem field_example (t : ℝ) :
    Fₑ t ((1 + t) • (e₁ * e₁ᵀ) + (1 / 8 : ℝ) • E₂₂) = e₁ * e₁ᵀ := by
  change e₁ * e₁ᵀ + (((1 + t) • (e₁ * e₁ᵀ) + (1 / 8 : ℝ) • E₂₂) 1 1 - 1 / 8) ^ 2 • E₂₂ = _
  rw [smul_e₁_add_apply]
  simp

private theorem tangentProjAt_field_example {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    tangentProjAt (c • (e₁ * e₁ᵀ)) (Fₑ t (c • (e₁ * e₁ᵀ))) = e₁ * e₁ᵀ := by
  change tangentProjAt (c • (e₁ * e₁ᵀ)) (e₁ * e₁ᵀ + _ • E₂₂) = _
  rw [map_add, map_smul, tangentProjAt_smul_e₁_apply hc, tangentProjAt_smul_e₁_E₂₂ hc, smul_zero,
    add_zero]

private theorem hasDerivAt_smul_e₁_add (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + (1 / 8 : ℝ) • E₂₂) (e₁ * e₁ᵀ) t := by
  simpa using (hasDerivAt_smul_e₁ 1 t).add_const ((1 / 8 : ℝ) • E₂₂)

private theorem tangentProjAt_example_sub {t : ℝ} (ht : 0 ≤ t) :
    tangentProjAt ((1 + t) • (e₁ * e₁ᵀ))
      ((1 + t) • (e₁ * e₁ᵀ) + (1 / 8 : ℝ) • E₂₂ - (1 + t) • (e₁ * e₁ᵀ)) = 0 := by
  rw [add_sub_cancel_left, map_smul, tangentProjAt_smul_e₁_E₂₂ (by linarith), smul_zero]

private theorem norm_example_sub (t : ℝ) :
    ‖(1 + t) • (e₁ * e₁ᵀ) - ((1 + t) • (e₁ * e₁ᵀ) + (1 / 8 : ℝ) • E₂₂)‖ ≤ 1 / 8 := by
  rw [sub_add_cancel_left, norm_neg]
  exact norm_smul_E₂₂_le

/-- `A t = (1 + t) e₁ e₁ᵀ + diag(0, 1/8)` is bounded below by `1/8`. -/
private theorem norm_mul_ge (t : ℝ) (ht : 0 ≤ t) (B : Matrix (Fin 2) Unit ℝ) :
    1 / 8 * ‖B‖ ≤ ‖((1 + t) • (e₁ * e₁ᵀ) + (1 / 8 : ℝ) • E₂₂) * B‖ := by
  rw [smul_e₁_add_eq]
  have hsq : (1 / 8 * ‖B‖) ^ 2 ≤ ‖!![1 + t, 0; 0, 1 / 8] * B‖ ^ 2 := by
    rw [mul_pow, Curvature.frob_sq, Curvature.frob_sq]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    nlinarith [sq_nonneg (B 0 ()), sq_nonneg (B 1 ()), sq_nonneg t,
      mul_nonneg ht (sq_nonneg (B 0 ())), mul_nonneg (mul_nonneg ht ht) (sq_nonneg (B 0 ()))]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp hsq

/-- `X t = (1 + t) e₁ e₁ᵀ` is a best approximation of rank at most `1` of
`A t = X t + diag(0, 1/8)`: `‖A t - X t‖ ≤ 1/8 ≤ σ₁(A t) ≤ ‖A t - Z‖` (Eckart–Young). -/
private theorem isBest_example (t : ℝ) (ht : 0 ≤ t) (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (hZ : Z.rank ≤ 1) :
    ‖(1 + t) • (e₁ * e₁ᵀ) + (1 / 8 : ℝ) • E₂₂ - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
      ‖(1 + t) • (e₁ * e₁ᵀ) + (1 / 8 : ℝ) • E₂₂ - Z‖ := by
  rw [add_sub_cancel_left]
  have h2 : (1 / 8 : ℝ) ≤
      (toEuclideanLin ((1 + t) • (e₁ * e₁ᵀ) + (1 / 8 : ℝ) • E₂₂)).singularValues 1 := by
    have h := (SVD.forall_mul_norm_le_iff ((1 + t) • (e₁ * e₁ᵀ) + (1 / 8 : ℝ) • E₂₂)
      (ρ := 1 / 8)).mp fun v => by
        rw [Curvature.norm_toEuclideanLin_eq_frob, Curvature.norm_eq_frob_replicateCol v]
        exact norm_mul_ge t ht _
    rw [Fintype.card_fin] at h
    exact h
  have h3 := EckartYoung.singularValues_le_specNorm_sub
    ((1 + t) • (e₁ * e₁ᵀ) + (1 / 8 : ℝ) • E₂₂) Z hZ
  have h4 := Curvature.specNorm_le_frob ((1 + t) • (e₁ * e₁ᵀ) + (1 / 8 : ℝ) • E₂₂ - Z)
  linarith [norm_smul_E₂₂_le]

/-- The smallness condition of the examples on `[0, 1/8]` with `L = 2`, `ρ = μ = 1`,
`δ = 1/16`, `R = 1`: `1/8 + e^{8 t} (1/16 + 6 t/8) < 1`. -/
private theorem small_example {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (1 / 8)) :
    ‖(1 + t) • (e₁ * e₁ᵀ) - ((1 + t) • (e₁ * e₁ᵀ) + (1 / 8 : ℝ) • E₂₂)‖ +
      Real.exp ((2 + 6 * 1 / 1) * (t - 0)) * (1 / 16 + (2 + 4 * 1 / 1) *
        ∫ s in (0 : ℝ)..t, ‖(1 + s) • (e₁ * e₁ᵀ) - ((1 + s) • (e₁ * e₁ᵀ) + (1 / 8 : ℝ) • E₂₂)‖)
      < 1 := by
  have hN : ∀ s : ℝ, ‖(1 + s) • (e₁ * e₁ᵀ) - ((1 + s) • (e₁ * e₁ᵀ) + (1 / 8 : ℝ) • E₂₂)‖ =
      ‖(1 / 8 : ℝ) • E₂₂‖ := fun s => by rw [sub_add_cancel_left, norm_neg]
  simp only [hN, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have hN8 := norm_smul_E₂₂_le
  have hN0 := norm_nonneg ((1 / 8 : ℝ) • E₂₂)
  have he : Real.exp ((2 + 6 * 1 / 1) * t) ≤ Real.exp 1 :=
    Real.exp_le_exp.2 (by nlinarith [ht.2])
  have he1 := Real.exp_one_lt_d9
  have htN : t * ‖(1 / 8 : ℝ) • E₂₂‖ ≤ 1 / 8 * (1 / 8) := mul_le_mul ht.2 hN8 hN0 (by norm_num)
  have h0 : 0 ≤ t * ‖(1 / 8 : ℝ) • E₂₂‖ := mul_nonneg ht.1 hN0
  have h1 : 1 / 16 + (2 + 4 * 1 / 1) * (t * ‖(1 / 8 : ℝ) • E₂₂‖) ≤ 5 / 32 := by nlinarith
  have h2 : 0 ≤ 1 / 16 + (2 + 4 * 1 / 1) * (t * ‖(1 / 8 : ℝ) • E₂₂‖) := by nlinarith
  have h3 := mul_le_mul he h1 h2 (Real.exp_pos 1).le
  linarith

/-- The three tube theorems for `A t = (1 + t) e₁ e₁ᵀ + diag(0, 1/8)` solving `Ȧ = F(t, A)` with
the quadratic field `F(t, x) = e₁ e₁ᵀ + (x₂₂ - 1/8)² E₂₂`, which is `2`-Lipschitz on the tube of
radius `R = 1` around `A` and not Lipschitz on the whole space; `X t = (1 + t) e₁ e₁ᵀ` (a best
approximation of rank `1` of `A t`), the DLRA solution `Y t = (17/16 + t) e₁ e₁ᵀ` (`Y ≠ X`,
`δ = 1/16`), `r = 1`, `ρ = μ = 1` on `[0, 1/8]`. -/
example :
    (∀ t ∈ Set.Icc (0 : ℝ) (1 / 8), ‖Yₑ t - Aₑ t‖ < 1) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) (1 / 8), ‖Yₑ t - Xₑ t‖ ≤
      Real.exp ((2 + 6 * 1 / 1) * (t - 0)) * (1 / 16 + (2 + 4 * 1 / 1) *
        ∫ s in (0 : ℝ)..t, ‖Xₑ s - Aₑ s‖)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) (1 / 8), ‖Yₑ t - Xₑ t‖ ≤
      Real.exp ((2 + 6 * 1 / 1) * (t - 0)) * (1 / 16 + (2 + 4 * 1 / 1) *
        ∫ s in (0 : ℝ)..t, ‖Xₑ s - Aₑ s‖)) := by
  have hY : IsDLRASolution 1 Fₑ Yₑ 0 (1 / 8) := by
    refine ⟨⟨fun s _ => (hasDerivAt_smul_e₁ (17 / 16) s).continuousAt.continuousWithinAt,
      fun s hs => ?_⟩, fun t ht => rank_smul_e₁ (ne_of_gt (by linarith [ht.1]))⟩
    have h := (hasDerivAt_smul_e₁ (17 / 16) s).hasDerivWithinAt (s := Ici s)
    convert h using 1
    exact tangentProjAt_field_example (ne_of_gt (by linarith [hs.1])) s
  have hA : ODESolution Fₑ Aₑ 0 (1 / 8) := by
    refine ⟨fun s _ => (hasDerivAt_smul_e₁_add s).continuousAt.continuousWithinAt,
      fun s _ => ?_⟩
    have h := (hasDerivAt_smul_e₁_add s).hasDerivWithinAt (s := Ici s)
    convert h using 1
    exact field_example s
  have hμ : ∀ t ∈ Ico (0 : ℝ) (1 / 8), ‖Fₑ t (Aₑ t)‖ ≤ 1 := fun t _ =>
    (congrArg norm (field_example t)).trans_le norm_e₁_mul_le
  have hXc : ContinuousOn Xₑ (Set.Icc 0 (1 / 8)) :=
    fun s _ => (hasDerivAt_smul_e₁ 1 s).continuousAt.continuousWithinAt
  have hX : ∀ t ∈ Ico (0 : ℝ) (1 / 8), HasDerivWithinAt Xₑ ((fun _ : ℝ => e₁ * e₁ᵀ) t) (Ici t) t :=
    fun s _ => (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt
  have hXr : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 8), (Xₑ t).rank = 1 :=
    fun t ht => rank_smul_e₁ (ne_of_gt (by linarith [ht.1]))
  have hσ : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 8),
      (1 : ℝ) ≤ (toEuclideanLin (Xₑ t)).singularValues (1 - 1) :=
    fun t ht => one_le_singularValues_smul_e₁ (by linarith [ht.1])
  have ho : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 8), tangentProjAt (Xₑ t) (Aₑ t - Xₑ t) = 0 :=
    fun t ht => tangentProjAt_example_sub ht.1
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 8), ‖Xₑ t - Aₑ t‖ ≤ 1 / 4 :=
    fun t _ => (norm_example_sub t).trans (by norm_num)
  have hδ : ‖Yₑ 0 - Xₑ 0‖ ≤ 1 / 16 := by
    change ‖(17 / 16 + 0 : ℝ) • (e₁ * e₁ᵀ) - (1 + 0 : ℝ) • (e₁ * e₁ᵀ)‖ ≤ 1 / 16
    have h : (17 / 16 + 0 : ℝ) - (1 + 0) = 1 / 16 := by norm_num
    rw [← sub_smul, h, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 16)]
    exact mul_le_of_le_one_right (by norm_num) norm_e₁_mul_le
  have hbest : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 8), (Xₑ t).rank ≤ 1 ∧
      ∀ Z : Matrix (Fin 2) (Fin 2) ℝ, Z.rank ≤ 1 → ‖Aₑ t - Xₑ t‖ ≤ ‖Aₑ t - Z‖ :=
    fun t ht => ⟨(hXr t ht).le, isBest_example t ht.1⟩
  have hsmall : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 8), ‖Xₑ t - Aₑ t‖ +
      Real.exp ((2 + 6 * 1 / 1) * (t - 0)) * (1 / 16 + (2 + 4 * 1 / 1) *
        ∫ s in (0 : ℝ)..t, ‖Xₑ s - Aₑ s‖) < 1 :=
    fun t ht => small_example ht
  have hL : (0 : ℝ) ≤ 2 := by norm_num
  have r1 := hY.norm_sub_lt_of_isLipschitzOnTube (X' := fun _ => e₁ * e₁ᵀ) one_pos hL
    isLipschitzOnTube_example hA hμ hXc hX hXr hσ ho hd hδ hsmall
  have r2 := hY.norm_sub_le_integral_of_isLipschitzOnTube (X' := fun _ => e₁ * e₁ᵀ) one_pos hL
    isLipschitzOnTube_example hA hμ hXc hX hXr hσ ho hd hδ hsmall
  have r3 := hY.norm_sub_le_integral_of_forall_norm_sub_le_of_isLipschitzOnTube
    (X' := fun _ => e₁ * e₁ᵀ) one_pos hL isLipschitzOnTube_example hA hμ hXc hX hbest hσ hd hδ
    hsmall
  exact ⟨r1, r2, r3⟩

end Examples

end LeanDLRA
