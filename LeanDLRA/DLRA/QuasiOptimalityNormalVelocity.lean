import LeanDLRA.DLRA.QuasiOptimalityTimeLocal
import LeanDLRA.Foundations.Localization
import LeanDLRA.Analysis.GronwallInner

/-!
# Quasi-optimality of matrix DLRA with the normal velocity as growth rate

The quasi-optimality bounds of `LeanDLRA/DLRA/QuasiOptimalityTimeLocal.lean` have the growth rate
`L + μ/ρ`, with `μ ≥ ‖F(t, A t)‖` the whole velocity of the exact solution and `ρ ≤ σ_{r-1}(X t)`.
This file has the bound with the rate

  `k = L + ν/ρ + ν/(ρ - ε) + μ ε/ρ²`,   `ν ≥ ‖(1 - P(X t)) F(t, A t)‖`,

in which the velocity enters at first order only through its component normal to the manifold of
rank-`r` matrices at `X t`, and the whole velocity `μ` is multiplied by the radius `ε < ρ` of a
tube around `X` that contains the DLRA solution `Y`. The source is the Lipschitz term and the
defect `d ≥ ‖P(X t) F(t, A t) - Ẋ t‖` of the curve `X`:

  `‖Y t - X t‖ ≤ e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖X s - A s‖ + d s) ds`.

All norms of matrices are Frobenius norms.

## Main results

* `IsOrthProj.inner_sub_apply_sub_apply`: for orthogonal projectors `P`, `Q` with `P y = y` and
  `Q x = x`, `⟪y - x, P z - Q z⟫ = ⟪x - P x, z - P z⟫ + ⟪y - Q y, z - Q z⟫`.
* `inner_sub_tangentProjAt_sub_le_norm_sq_mul`: for `X`, `Y` of rank `r`,
  `⟪Y - X, P(Y) Z - P(X) Z⟫ ≤ (‖(1 - P(Y)) Z‖/σ_{r-1}(X) + ‖(1 - P(X)) Z‖/σ_{r-1}(Y)) ‖Y - X‖²`.
* `inner_sub_tangentProjAt_sub_le_of_norm_sub_lt`: the same with data at `X` only, for
  `‖Y - X‖ < ρ ≤ σ_{r-1}(X)`.
* `IsDLRASolution.norm_sub_le_integral_exp_integral_of_norm_sub_tangentProjAt_le`: the bound for
  a DLRA solution that stays in the tube `‖Y t - X t‖ ≤ ε t`.
* `IsDLRASolution.norm_sub_le_integral_exp_integral_of_integral_lt`: the bound without a
  hypothesis on `Y` besides the initial error, if the bound itself stays below `ε`.
* `IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_integral_lt`: the bound against
  the truncated SVD `T_r(A t)` under the gap `σ_r(A t) < σ_{r-1}(A t)`, with `ρ = σ_{r-1}(A t)`
  and the defect bound `μ σ_r/(σ_{r-1} - σ_r)`.

## Implementation notes

Only the component of the derivative of `Y - X` along `Y - X` changes `‖Y - X‖`, so the term
`(P(Y) - P(X)) F(t, A t)` enters through its inner product with `Y - X`
(`norm_le_exp_integral_mul_add_integral_exp_integral_mul_of_inner_le`). By the symmetry of the
projectors this inner product is a sum of inner products of normal components, and the normal
components `(1 - P(Y)) X` and `(1 - P(X)) Y` are of second order in `‖Y - X‖`
(`norm_one_sub_tangentProjAt_apply_sub_le`). The lower bound of `σ_{r-1}(Y)` is
`ρ - ‖Y - X‖` (Weyl), and `‖(1 - P(Y)) Z‖ ≤ ‖(1 - P(X)) Z‖ + ρ⁻¹ ‖Y - X‖ ‖Z‖` by the Lipschitz
bound of the tangent projector with the constant `1`. The curve `X` is any differentiable curve
of rank-`r` matrices; it need not consist of critical points of the distance to `A`, and `A` need
not solve the differential equation: both enter through the defect `d` and the term `‖X - A‖`.
The second-order normal components are bounded in the Frobenius norm; the growth generator at
first order is the Weingarten map of [FepponLermusiaux2018, Proposition 22] in the direction of
the normal velocity.

## References

* [KochLubich2007]
* [FepponLermusiaux2018]
-/

open Set Finset Matrix Filter
open scoped Topology RealInnerProductSpace

namespace LeanDLRA

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The difference of two orthogonal projectors tested with the difference of fixed points.**
Let `P`, `Q` be orthogonal projectors with `P y = y` and `Q x = x`. Then for every `z`
`⟪y - x, P z - Q z⟫ = ⟪x - P x, z - P z⟫ + ⟪y - Q y, z - Q z⟫`: only the components of `z` normal
to the two ranges enter, each paired with the normal component of the other fixed point. -/
theorem IsOrthProj.inner_sub_apply_sub_apply {P Q : E →L[ℝ] E} (hP : IsOrthProj P)
    (hQ : IsOrthProj Q) {x y : E} (hy : P y = y) (hx : Q x = x) (z : E) :
    ⟪y - x, P z - Q z⟫ = ⟪x - P x, z - P z⟫ + ⟪y - Q y, z - Q z⟫ := by
  have h1 : ⟪y - x, P z⟫ = ⟪y - P x, z⟫ := by rw [← hP.symm, map_sub, hy]
  have h2 : ⟪y - x, Q z⟫ = ⟪Q y - x, z⟫ := by rw [← hQ.symm, map_sub, hx]
  have h3 : ⟪x - P x, P z⟫ = 0 := by
    rw [← hP.symm, map_sub, hP.idem, sub_self, inner_zero_left]
  have h4 : ⟪y - Q y, Q z⟫ = 0 := by
    rw [← hQ.symm, map_sub, hQ.idem, sub_self, inner_zero_left]
  rw [inner_sub_right (y - x), h1, h2, inner_sub_right (x - P x), h3,
    inner_sub_right (y - Q y), h4]
  simp only [inner_sub_left]
  ring

end Abstract

section NormalVelocity

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **The tangent projectors at two matrices of rank `r`, tested with their difference.** Let
`X`, `Y` have rank `r` with `0 < ρ ≤ σ_{r-1}(X)` and `0 < ρ' ≤ σ_{r-1}(Y)`. For every `Z`

  `⟪Y - X, P(Y) Z - P(X) Z⟫ ≤ (ρ⁻¹ ‖Z - P(Y) Z‖ + ρ'⁻¹ ‖Z - P(X) Z‖) ‖Y - X‖²`.

The right-hand side is of second order in `‖Y - X‖` and has the normal components of `Z`
only. -/
theorem inner_sub_tangentProjAt_sub_le_norm_sq_mul {r : ℕ} {X Y : Matrix m n ℝ}
    (hX : X.rank = r) (hY : Y.rank = r) {ρ ρ' : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) (hρ' : 0 < ρ')
    (hσ' : ρ' ≤ (toEuclideanLin Y).singularValues (r - 1)) (Z : Matrix m n ℝ) :
    ⟪Y - X, tangentProjAt Y Z - tangentProjAt X Z⟫ ≤
      (ρ⁻¹ * ‖Z - tangentProjAt Y Z‖ + ρ'⁻¹ * ‖Z - tangentProjAt X Z‖) * ‖Y - X‖ ^ 2 := by
  have hid := (isOrthProj_tangentProjAt Y).inner_sub_apply_sub_apply
    (isOrthProj_tangentProjAt X) (tangentProjAt_self Y) (tangentProjAt_self X) Z
  have h1 : ‖X - tangentProjAt Y X‖ ≤ ρ⁻¹ * ‖Y - X‖ ^ 2 := by
    have h := norm_one_sub_tangentProjAt_apply_sub_le hX hY hρ hσ
    have e : (1 - tangentProjAt Y) (Y - X) = -(X - tangentProjAt Y X) := by
      simp only [sub_apply, one_apply_eq_self, map_sub,
        tangentProjAt_self]
      abel
    rwa [e, norm_neg] at h
  have h2 : ‖Y - tangentProjAt X Y‖ ≤ ρ'⁻¹ * ‖Y - X‖ ^ 2 := by
    have h := norm_one_sub_tangentProjAt_apply_sub_le hY hX hρ' hσ'
    have e : (1 - tangentProjAt X) (X - Y) = -(Y - tangentProjAt X Y) := by
      simp only [sub_apply, one_apply_eq_self, map_sub,
        tangentProjAt_self]
      abel
    rwa [e, norm_neg, norm_sub_rev X Y] at h
  rw [hid]
  calc ⟪X - tangentProjAt Y X, Z - tangentProjAt Y Z⟫ +
        ⟪Y - tangentProjAt X Y, Z - tangentProjAt X Z⟫
      ≤ ‖X - tangentProjAt Y X‖ * ‖Z - tangentProjAt Y Z‖ +
        ‖Y - tangentProjAt X Y‖ * ‖Z - tangentProjAt X Z‖ :=
        add_le_add (real_inner_le_norm _ _) (real_inner_le_norm _ _)
    _ ≤ ρ⁻¹ * ‖Y - X‖ ^ 2 * ‖Z - tangentProjAt Y Z‖ +
        ρ'⁻¹ * ‖Y - X‖ ^ 2 * ‖Z - tangentProjAt X Z‖ :=
        add_le_add (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
    _ = _ := by ring

/-- **The tangent projectors tested with the difference, data at one point.** Let `X`, `Y` have
rank `r` with `‖Y - X‖ < ρ ≤ σ_{r-1}(X)`. For every `Z`, with the normal component
`N = Z - P(X) Z` of `Z` at `X`,

  `⟪Y - X, P(Y) Z - P(X) Z⟫ ≤ (‖N‖/ρ + ‖N‖/(ρ - ‖Y - X‖) + ‖Z‖ ‖Y - X‖/ρ²) ‖Y - X‖²`. -/
theorem inner_sub_tangentProjAt_sub_le_of_norm_sub_lt {r : ℕ} {X Y : Matrix m n ℝ}
    (hX : X.rank = r) (hY : Y.rank = r) {ρ : ℝ}
    (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) (he : ‖Y - X‖ < ρ)
    (Z : Matrix m n ℝ) :
    ⟪Y - X, tangentProjAt Y Z - tangentProjAt X Z⟫ ≤
      (‖Z - tangentProjAt X Z‖ / ρ + ‖Z - tangentProjAt X Z‖ / (ρ - ‖Y - X‖) +
        ‖Z‖ * ‖Y - X‖ / ρ ^ 2) * ‖Y - X‖ ^ 2 := by
  have hρ : 0 < ρ := (norm_nonneg _).trans_lt he
  have hρ' : 0 < ρ - ‖Y - X‖ := sub_pos.2 he
  have hσ' : ρ - ‖Y - X‖ ≤ (toEuclideanLin Y).singularValues (r - 1) := by
    have h := (abs_le.1 (WeylSingular.abs_singularValues_sub_le_frobenius X Y (r - 1))).2
    rw [norm_sub_rev X Y] at h
    linarith
  have h := inner_sub_tangentProjAt_sub_le_norm_sq_mul hX hY hρ hσ hρ' hσ' Z
  have hN : ‖Z - tangentProjAt Y Z‖ ≤
      ‖Z - tangentProjAt X Z‖ + ρ⁻¹ * ‖Y - X‖ * ‖Z‖ := by
    have e : Z - tangentProjAt Y Z =
        (Z - tangentProjAt X Z) - (tangentProjAt Y Z - tangentProjAt X Z) := by abel
    rw [e]
    exact (norm_sub_le _ _).trans
      (add_le_add le_rfl (norm_tangentProjAt_sub_le_inv_mul hX hY hρ hσ Z))
  have h3 := mul_le_mul_of_nonneg_left hN (inv_nonneg.2 hρ.le)
  calc ⟪Y - X, tangentProjAt Y Z - tangentProjAt X Z⟫
      ≤ (ρ⁻¹ * ‖Z - tangentProjAt Y Z‖ + (ρ - ‖Y - X‖)⁻¹ * ‖Z - tangentProjAt X Z‖) *
        ‖Y - X‖ ^ 2 := h
    _ ≤ (ρ⁻¹ * (‖Z - tangentProjAt X Z‖ + ρ⁻¹ * ‖Y - X‖ * ‖Z‖) +
        (ρ - ‖Y - X‖)⁻¹ * ‖Z - tangentProjAt X Z‖) * ‖Y - X‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = _ := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        ring

/-- **Quasi-optimality of matrix DLRA with the normal velocity as growth rate, tube form.** Let
`F` be `L`-Lipschitz, `Y` a DLRA solution of rank `r` of `Ẏ = P(Y) F(t, Y)` on `[a, b]`, `A` a
continuous curve and `X` a continuous curve of matrices of rank `r` with right derivatives `X'`.
Let `ρ`, `μ`, `ν`, `d`, `ε` be continuous on `[a, b]` with `ρ t ≤ σ_{r-1}(X t)`,
`‖F(t, A t)‖ ≤ μ t`, `‖(1 - P(X t)) F(t, A t)‖ ≤ ν t`, `‖P(X t) F(t, A t) - X' t‖ ≤ d t` and
`0 ≤ ε t < ρ t`. If `‖Y t - X t‖ ≤ ε t` on `[a, b)` and `‖Y a - X a‖ ≤ δ`, then with
`k = L + ν/ρ + ν/(ρ - ε) + μ ε/ρ²`, for `t ∈ [a, b]`

  `‖Y t - X t‖ ≤ e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖X s - A s‖ + d s) ds`. -/
theorem IsDLRASolution.norm_sub_le_integral_exp_integral_of_norm_sub_tangentProjAt_le {r : ℕ}
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
    (hν : ∀ t ∈ Ico a b, ‖F t (A t) - tangentProjAt (X t) (F t (A t))‖ ≤ ν t)
    (hd : ∀ t ∈ Ico a b, ‖tangentProjAt (X t) (F t (A t)) - X' t‖ ≤ d t)
    (hε0 : ∀ t ∈ Icc a b, 0 ≤ ε t) (hερ : ∀ t ∈ Icc a b, ε t < ρ t)
    (htube : ∀ t ∈ Ico a b, ‖Y t - X t‖ ≤ ε t) (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp (∫ u in a..t,
        (L + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2)) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (L + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2)) *
          (L * ‖X s - A s‖ + d s) := by
  intro t0 ht0
  rcases eq_or_lt_of_le ht0.1 with h0 | hpos
  · subst h0
    simpa using hδ
  have hab : a < b := hpos.trans_le ht0.2
  have hρpos : ∀ u ∈ Icc a b, 0 < ρ u := fun u hu => (hε0 u hu).trans_lt (hερ u hu)
  have hIcc : Icc a t0 ⊆ Icc a b := Icc_subset_Icc_right ht0.2
  have hIco : ∀ s ∈ Ico a t0, s ∈ Ico a b := fun s hs => ⟨hs.1, hs.2.trans_le ht0.2⟩
  have hkOn : ContinuousOn
      (fun u => L + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2) (Icc a b) :=
    ((continuousOn_const.add (hνc.div hρc fun u hu => (hρpos u hu).ne')).add
      (hνc.div (hρc.sub hεc) fun u hu => (sub_pos.2 (hερ u hu)).ne')).add
      ((hμc.mul hεc).div (hρc.pow 2) fun u hu => (pow_pos (hρpos u hu) 2).ne')
  have hgOn : ContinuousOn (fun s => L * ‖X s - A s‖ + d s) (Icc a b) :=
    (continuousOn_const.mul (hXc.sub hAc).norm).add hdc
  obtain ⟨kc, hkc, hkeq⟩ : ∃ kc : ℝ → ℝ, Continuous kc ∧ ∀ s ∈ Icc a b, kc s =
      L + ν s / ρ s + ν s / (ρ s - ε s) + μ s * ε s / ρ s ^ 2 :=
    ⟨fun s => L + ν (projIcc a b hab.le s) / ρ (projIcc a b hab.le s) +
        ν (projIcc a b hab.le s) / (ρ (projIcc a b hab.le s) - ε (projIcc a b hab.le s)) +
        μ (projIcc a b hab.le s) * ε (projIcc a b hab.le s) / ρ (projIcc a b hab.le s) ^ 2,
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
    have hρs := hρpos s hsI
    have hes := htube s hsb
    have hρε : 0 < ρ s - ε s := sub_pos.2 (hερ s hsI)
    have hν0 : 0 ≤ ν s := (norm_nonneg _).trans (hν s hsb)
    have hμ0 : 0 ≤ μ s := (norm_nonneg _).trans (hμ s hsb)
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
    have i2 : ⟪Y s - X s, tangentProjAt (Y s) (F s (A s)) - tangentProjAt (X s) (F s (A s))⟫ ≤
        (ν s / ρ s + ν s / (ρ s - ε s) + μ s * ε s / ρ s ^ 2) * ‖Y s - X s‖ ^ 2 := by
      refine (inner_sub_tangentProjAt_sub_le_of_norm_sub_lt (hXr s hsI) (hY.2 s hsI)
        (hσ s hsI) (hes.trans_lt (hερ s hsI)) (F s (A s))).trans
        (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
      refine add_le_add (add_le_add ?_ ?_) ?_
      · exact div_le_div₀ hν0 (hν s hsb) hρs le_rfl
      · exact div_le_div₀ hν0 (hν s hsb) hρε (by linarith)
      · exact div_le_div₀ (mul_nonneg hμ0 (hε0 s hsI))
          (mul_le_mul (hμ s hsb) hes (norm_nonneg _) hμ0) (pow_pos hρs 2) le_rfl
    have i3 : ⟪Y s - X s, tangentProjAt (X s) (F s (A s)) - X' s⟫ ≤ ‖Y s - X s‖ * d s :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hd s hsb) (norm_nonneg _))
    rw [hsplit, inner_add_right, inner_add_right, hkeq s hsI, hgeq s hsI]
    calc _ ≤ ‖Y s - X s‖ * (L * ‖Y s - X s‖ + L * ‖X s - A s‖) +
          (ν s / ρ s + ν s / (ρ s - ε s) + μ s * ε s / ρ s ^ 2) * ‖Y s - X s‖ ^ 2 +
          ‖Y s - X s‖ * d s := add_le_add (add_le_add i1 i2) i3
      _ = _ := by ring
  have hcmp := norm_le_exp_integral_mul_add_integral_exp_integral_mul_of_inner_le
    (f := fun t => Y t - X t)
    (f' := fun t => tangentProjAt (Y t) (F t (Y t)) - X' t) (δ := δ) hkc hgc hg0
    ((hY.1.cont.sub hXc).mono hIcc)
    (fun s hs => (hY.1.deriv s (hIco s hs)).sub (hX s (hIco s hs))) hδ hbound t0
    ⟨ht0.1, le_rfl⟩
  have e1 : ∫ u in a..t0, kc u =
      ∫ u in a..t0, (L + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2) :=
    intervalIntegral.integral_congr fun u hu => by
      rw [uIcc_of_le ht0.1] at hu
      exact hkeq u (hIcc hu)
  have e2 : ∫ s in a..t0, Real.exp (∫ u in s..t0, kc u) * gc s =
      ∫ s in a..t0, Real.exp (∫ u in s..t0,
        (L + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2)) *
        (L * ‖X s - A s‖ + d s) :=
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le ht0.1] at hs
      have e3 : ∫ u in s..t0, kc u =
          ∫ u in s..t0, (L + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2) :=
        intervalIntegral.integral_congr fun u hu => by
          rw [uIcc_of_le hs.2] at hu
          exact hkeq u ⟨hs.1.trans hu.1, hu.2.trans ht0.2⟩
      change Real.exp (∫ u in s..t0, kc u) * gc s = _
      rw [e3, hgeq s (hIcc hs)]
  rw [e1, e2] at hcmp
  exact hcmp

/-- **Quasi-optimality with the normal velocity as growth rate, a priori form.** Under the
hypotheses of `IsDLRASolution.norm_sub_le_integral_exp_integral_of_norm_sub_tangentProjAt_le` on
`F`, `A`, `X` and the functions `ρ`, `μ`, `ν`, `d`, `ε`, the tube condition on `Y` may be replaced
by a condition on the bound: if

  `e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖X s - A s‖ + d s) ds < ε t`   on `[a, b]`,

`k = L + ν/ρ + ν/(ρ - ε) + μ ε/ρ²`, then `‖Y t - X t‖` is at most the left-hand side on `[a, b]`;
in particular `Y` stays in the tube of radius `ε` around `X`. -/
theorem IsDLRASolution.norm_sub_le_integral_exp_integral_of_integral_lt {r : ℕ}
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
    (hν : ∀ t ∈ Ico a b, ‖F t (A t) - tangentProjAt (X t) (F t (A t))‖ ≤ ν t)
    (hd : ∀ t ∈ Ico a b, ‖tangentProjAt (X t) (F t (A t)) - X' t‖ ≤ d t)
    (hε0 : ∀ t ∈ Icc a b, 0 ≤ ε t) (hερ : ∀ t ∈ Icc a b, ε t < ρ t)
    (hδ : ‖Y a - X a‖ ≤ δ)
    (hB : ∀ t ∈ Icc a b,
      Real.exp (∫ u in a..t,
        (L + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2)) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (L + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2)) *
          (L * ‖X s - A s‖ + d s) < ε t) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp (∫ u in a..t,
        (L + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2)) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (L + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2)) *
          (L * ‖X s - A s‖ + d s) := by
  have h := bootstrap_of_continuousOn (e := fun t => ‖Y t - X t‖ - ε t)
    (β := fun t => (Real.exp (∫ u in a..t,
        (L + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2)) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (L + ν u / ρ u + ν u / (ρ u - ε u) + μ u * ε u / ρ u ^ 2)) *
          (L * ‖X s - A s‖ + d s)) - ε t) (R := 0) ((hY.1.cont.sub hXc).norm.sub hεc)
    (fun t ht => sub_neg.2 (hB t ht)) (fun t ht hs => by
      have hIcc : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
      have hIco : ∀ s ∈ Ico a t, s ∈ Ico a b := fun s hs => ⟨hs.1, hs.2.trans_le ht.2⟩
      have hYt : IsDLRASolution r F Y a t :=
        ⟨⟨hY.1.cont.mono hIcc, fun s hs => hY.1.deriv s (hIco s hs)⟩,
          fun s hs => hY.2 s (hIcc hs)⟩
      have hm := hYt.norm_sub_le_integral_exp_integral_of_norm_sub_tangentProjAt_le hL hF
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
/-- **Quasi-optimality against the truncated SVD with the normal velocity as growth rate.** Let
`F` be `L`-Lipschitz, `A` a solution of `Ȧ = F(t, A)` on `[a, b]` with the gap
`σ_r(A t) < σ_{r-1}(A t)`, and `Y` a DLRA solution of rank `r`. Let `μ`, `ν`, `ε` be continuous
with `‖F(t, A t)‖ ≤ μ t`, `‖(1 - P(T_r(A t))) F(t, A t)‖ ≤ ν t` and `0 ≤ ε t < σ_{r-1}(A t)`. With
`ρ = σ_{r-1}(A ·)`, `τ = σ_r(A ·)` and `k = L + ν/ρ + ν/(ρ - ε) + μ ε/ρ²`: if
`‖Y a - T_r(A a)‖ ≤ δ` and

  `e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖T_r(A s) - A s‖ + μ s/(ρ s - τ s) τ s) ds < ε t`   on `[a, b]`,

then `‖Y t - T_r(A t)‖` is at most the left-hand side on `[a, b]`. The defect of the curve
`T_r(A t)` is bounded by `μ τ/(ρ - τ)` (`norm_sub_tangentProjAt_le_div_sub_mul_specNorm`);
`IsDLRASolution.norm_sub_le_integral_exp_integral_of_integral_lt` takes any bound of the
defect. -/
theorem IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_integral_lt {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A Y : ℝ → Matrix m n ℝ} {μ ν ε : ℝ → ℝ}
    {a b L δ : ℝ} (hY : IsDLRASolution r F Y a b) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hA : ODESolution F A a b) (hμc : ContinuousOn μ (Icc a b))
    (hνc : ContinuousOn ν (Icc a b)) (hεc : ContinuousOn ε (Icc a b))
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ t)
    (hν : ∀ t ∈ Ico a b,
      ‖F t (A t) - tangentProjAt (truncation (A t) r) (F t (A t))‖ ≤ ν t)
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
            μ s / ((toEuclideanLin (A s)).singularValues (r - 1) -
              (toEuclideanLin (A s)).singularValues r) *
              (toEuclideanLin (A s)).singularValues r) < ε t) :
    ∀ t ∈ Icc a b, ‖Y t - truncation (A t) r‖ ≤
      Real.exp (∫ u in a..t, (L + ν u / (toEuclideanLin (A u)).singularValues (r - 1) +
        ν u / ((toEuclideanLin (A u)).singularValues (r - 1) - ε u) +
        μ u * ε u / (toEuclideanLin (A u)).singularValues (r - 1) ^ 2)) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
          (L + ν u / (toEuclideanLin (A u)).singularValues (r - 1) +
          ν u / ((toEuclideanLin (A u)).singularValues (r - 1) - ε u) +
          μ u * ε u / (toEuclideanLin (A u)).singularValues (r - 1) ^ 2)) *
          (L * ‖truncation (A s) r - A s‖ +
            μ s / ((toEuclideanLin (A s)).singularValues (r - 1) -
              (toEuclideanLin (A s)).singularValues r) *
              (toEuclideanLin (A s)).singularValues r) := by
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  have hr : 0 < r := Nat.pos_of_ne_zero fun h0 => by
    subst h0
    exact lt_irrefl _ (hgap a ⟨le_rfl, hab⟩)
  have hσpos : ∀ s ∈ Icc a b, 0 < (toEuclideanLin (A s)).singularValues (r - 1) :=
    fun s hs => ((toEuclideanLin (A s)).singularValues_nonneg r).trans_lt (hgap s hs)
  have he : ∀ s, Curvature.specNorm (truncation (A s) r - A s) =
      (toEuclideanLin (A s)).singularValues r := fun s => by
    rw [Curvature.specNorm_sub_comm, specNorm_sub_truncation]
  have hσc' : ∀ i : ℕ, Continuous fun Z : Matrix m n ℝ => (toEuclideanLin Z).singularValues i :=
    fun i => (LipschitzWith.of_dist_le_mul (K := 1) fun Z Z' => by
      rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
      exact WeylSingular.abs_singularValues_sub_le_frobenius Z Z' i).continuous
  have hσc : ∀ i : ℕ, ContinuousOn (fun t => (toEuclideanLin (A t)).singularValues i)
      (Icc a b) := fun i => (hσc' i).comp_continuousOn hA.cont
  have hρc := hσc (r - 1)
  have hτc := hσc r
  obtain ⟨t₁, ht₁, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) hρc
  have hρ₀ : ∀ u ∈ Icc a b, (toEuclideanLin (A t₁)).singularValues (r - 1) ≤
      (toEuclideanLin (A u)).singularValues (r - 1) := fun u hu => isMinOn_iff.1 hmin u hu
  have hX : ∀ s ∈ Ico a b, HasDerivWithinAt (fun t => truncation (A t) r)
      (fderiv ℝ (fun B => truncation B r) (A s) (F s (A s))) (Ici s) s := fun s hs =>
    hasDerivWithinAt_truncation (hA.deriv s hs) (hgap s (Ico_subset_Icc_self hs))
  refine hY.norm_sub_le_integral_exp_integral_of_integral_lt (A := A)
    (X := fun t => truncation (A t) r)
    (X' := fun t => fderiv ℝ (fun B => truncation B r) (A t) (F t (A t)))
    (ρ := fun t => (toEuclideanLin (A t)).singularValues (r - 1)) (μ := μ) (ν := ν)
    (d := fun s => μ s / ((toEuclideanLin (A s)).singularValues (r - 1) -
      (toEuclideanLin (A s)).singularValues r) * (toEuclideanLin (A s)).singularValues r)
    (ε := ε) hL hF hA.cont hρc hμc hνc
    ((hμc.div (hρc.sub hτc) fun u hu => (sub_pos.2 (hgap u hu)).ne').mul hτc) hεc
    (fun s hs => (continuousAt_truncation (hgap s hs)).comp_continuousWithinAt (hA.cont s hs))
    hX (fun s hs => rank_truncation_of_le_singularValues (hσpos s hs) le_rfl)
    (fun s hs => le_singularValues_truncation hr (hσpos s hs) le_rfl) hμ hν
    (fun s hsb => ?_) hε0 hερ hδ hB t ht
  have hsI := Ico_subset_Icc_self hsb
  have hsub : Icc s b ⊆ Icc a b := Icc_subset_Icc_left hsb.1
  have hne : (𝓝[Icc s b \ {s}] s).NeBot := by
    rw [Icc_sdiff_left]
    exact left_nhdsWithin_Ioc_neBot hsb.2
  have hbest := norm_sub_tangentProjAt_le_div_sub_mul_specNorm (A := A)
    (X := fun t => truncation (A t) r)
    ((hA.deriv s hsb).mono (Icc_subset_Ici_self : Icc s b ⊆ Ici s))
    ((hX s hsb).mono (Icc_subset_Ici_self : Icc s b ⊆ Ici s)) ⟨le_rfl, hsb.2.le⟩ hne
    (hσpos t₁ ht₁) (fun u hu => rank_truncation_of_le_singularValues (hσpos u (hsub hu)) le_rfl)
    (fun u hu => (hρ₀ u (hsub hu)).trans
      (le_singularValues_truncation hr (hσpos u (hsub hu)) le_rfl))
    (le_singularValues_truncation hr (hσpos s hsI) le_rfl)
    (fun u _ => tangentProjAt_truncation_sub_eq_zero _ _) (hμ s hsb)
    (by
      rw [he s]
      exact hgap s hsI)
  rw [he s] at hbest
  rw [norm_sub_rev]
  exact hbest

end NormalVelocity

/-! ### Examples -/

namespace QuasiOptimalityNormalVelocityExamples

open scoped LeanDLRA.Frobenius
open QuasiOptimalityExamples

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

/-- **Non-vacuity of
`IsDLRASolution.norm_sub_le_integral_exp_integral_of_norm_sub_tangentProjAt_le` with a normal
velocity that does not vanish**: `2 × 2` matrices, `r = 1`, the field
`F = e₁ e₁ᵀ + diag(0, 1/16)` (`L = 0`), `A t = (1 + t) (e₁ e₁ᵀ + diag(0, 1/16))`, and
`X t = Y t = (1 + t) e₁ e₁ᵀ ≠ A t` on `[0, 1]`. The normal velocity is
`(1 - P(X t)) Ȧ = diag(0, 1/16) ≠ 0`; `ρ = 1`, `μ = 2`, `ν = 1/16`, `d = 0`, `ε = 1/2`, `δ = 0`. -/
example : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(1 + t) • (e₁ * e₁ᵀ) - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
      Real.exp (∫ _ in (0 : ℝ)..t,
        ((0 : ℝ) + 1 / 16 / 1 + 1 / 16 / (1 - 1 / 2) + 2 * (1 / 2) / 1 ^ 2)) * 0 +
        ∫ s in (0 : ℝ)..t, Real.exp (∫ _ in s..t,
          ((0 : ℝ) + 1 / 16 / 1 + 1 / 16 / (1 - 1 / 2) + 2 * (1 / 2) / 1 ^ 2)) *
          (0 * ‖(1 + s) • (e₁ * e₁ᵀ) - (1 + s) • (e₁ * e₁ᵀ + N₁₆)‖ + 0) :=
  isDLRASolution_smul_e₁_normal.norm_sub_le_integral_exp_integral_of_norm_sub_tangentProjAt_le
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
    (fun t ht => by
      rw [tangentProjAt_smul_e₁_add_N₁₆ (ne_of_gt (by linarith [ht.1])), add_sub_cancel_left]
      exact norm_N₁₆_le)
    (fun t ht => by
      rw [tangentProjAt_smul_e₁_add_N₁₆ (ne_of_gt (by linarith [ht.1])), sub_self, norm_zero])
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (fun t _ => by simp) (by simp)

/-- **Non-vacuity of `IsDLRASolution.norm_sub_le_integral_exp_integral_of_integral_lt`** on the
data of the preceding example: the bound is `0 < ε = 1/2`. -/
example : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(1 + t) • (e₁ * e₁ᵀ) - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
      Real.exp (∫ _ in (0 : ℝ)..t,
        ((0 : ℝ) + 1 / 16 / 1 + 1 / 16 / (1 - 1 / 2) + 2 * (1 / 2) / 1 ^ 2)) * 0 +
        ∫ s in (0 : ℝ)..t, Real.exp (∫ _ in s..t,
          ((0 : ℝ) + 1 / 16 / 1 + 1 / 16 / (1 - 1 / 2) + 2 * (1 / 2) / 1 ^ 2)) *
          (0 * ‖(1 + s) • (e₁ * e₁ᵀ) - (1 + s) • (e₁ * e₁ᵀ + N₁₆)‖ + 0) :=
  isDLRASolution_smul_e₁_normal.norm_sub_le_integral_exp_integral_of_integral_lt
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
    (fun t ht => by
      rw [tangentProjAt_smul_e₁_add_N₁₆ (ne_of_gt (by linarith [ht.1])), add_sub_cancel_left]
      exact norm_N₁₆_le)
    (fun t ht => by
      rw [tangentProjAt_smul_e₁_add_N₁₆ (ne_of_gt (by linarith [ht.1])), sub_self, norm_zero])
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (by simp) (fun t _ => by simp)

private theorem hasDerivAt_smul_e₁_add_const_N₁₆ (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) (e₁ * e₁ᵀ) t := by
  simpa using (hasDerivAt_smul_e₁ 1 t).add_const N₁₆

private theorem singularValues_one_smul_e₁_add_le {t : ℝ} (ht : 0 ≤ t) :
    (toEuclideanLin ((1 + t) • (e₁ * e₁ᵀ) + N₁₆)).singularValues 1 ≤ 1 / 16 := by
  rw [← EckartYoung.specNorm_sub_truncation, truncation_smul_e₁_add ht,
    Curvature.specNorm_sub_comm]
  exact (Curvature.specNorm_le_frob _).trans (norm_smul_e₁_sub_add_le t)

/-- `Y t = (1 + t) e₁ e₁ᵀ` is a DLRA solution of rank `1` for the field `F = e₁ e₁ᵀ`. -/
private theorem isDLRASolution_smul_e₁_tangent :
    IsDLRASolution 1 (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ)
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) 0 1 := by
  refine ⟨⟨fun s _ => (hasDerivAt_smul_e₁ 1 s).continuousAt.continuousWithinAt,
    fun s hs => ?_⟩, fun t ht => rank_smul_e₁ (ne_of_gt (by linarith [ht.1]))⟩
  have h := (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt (s := Ici s)
  convert h using 1
  exact tangentProjAt_smul_e₁_apply (ne_of_gt (by linarith [hs.1]))

/-- For `|k| ≤ 1/2` and `|g| ≤ 1/15` on `[0, ∞)` and `t ∈ [0, 1]`:
`∫₀ᵗ e^{∫ₛᵗ k} g(s) ds ≤ e^{1/2} / 15 < 1/2`. -/
private theorem integral_exp_integral_mul_lt_half {k g : ℝ → ℝ} {t : ℝ}
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

/-- **Non-vacuity of
`IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_integral_lt`** for `2 × 2`
matrices, `r = 1`, `A t = (1 + t) e₁ e₁ᵀ + diag(0, 1/16)` on `[0, 1]` and `F = e₁ e₁ᵀ` (`L = 0`,
`μ = 1`, `ν = 0`, `ε = 1/2`, `δ = 0`): the gap is `σ₁(A t) ≤ 1/16 < 1 ≤ σ₀(A t)`,
`T₁(A t) = (1 + t) e₁ e₁ᵀ` differs from `A t` and is the DLRA solution `Y`, the rate is at most
`1/2` and the source at most `1/15`, so that the bound stays below `ε`. -/
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
            1 / ((toEuclideanLin ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1) -
              (toEuclideanLin ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)).singularValues 1) *
              (toEuclideanLin ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)).singularValues 1) :=
  isDLRASolution_smul_e₁_tangent.norm_sub_truncation_le_integral_exp_integral_of_integral_lt
    (A := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) (μ := fun _ => 1) (ν := fun _ => 0)
    (ε := fun _ => 1 / 2) le_rfl (fun _ _ _ => by simp)
    ⟨fun s _ => (hasDerivAt_smul_e₁_add_const_N₁₆ s).continuousAt.continuousWithinAt,
      fun s _ => (hasDerivAt_smul_e₁_add_const_N₁₆ s).hasDerivWithinAt⟩
    continuousOn_const continuousOn_const continuousOn_const (fun _ _ => norm_e₁_mul_le)
    (fun t ht => by
      rw [truncation_smul_e₁_add ht.1,
        tangentProjAt_smul_e₁_apply (ne_of_gt (by linarith [ht.1])), sub_self, norm_zero])
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
          (mul_nonneg (by rw [one_div]; exact inv_nonneg.2 (by linarith)) h0)]
        exact (mul_le_mul (one_div_le_one_div_of_le (a := 15 / 16) (by norm_num)
          (by linarith)) h2 h0 (by norm_num)).trans (by norm_num))

end QuasiOptimalityNormalVelocityExamples

end LeanDLRA
