import LeanDLRA.DLRA.QuasiOptimalityMargin
import LeanDLRA.FixedRank.TangentSpace.ProjectorLipschitz

/-!
# Quasi-optimality of matrix DLRA with a margin below `ρ`

The quasi-optimality bounds of `LeanDLRA/DLRA/QuasiOptimalityMargin.lean` assume a margin
`‖X t - A t‖ ≤ θ ρ` with `θ < 1 / 2` between the curve `X` of critical points and the exact
solution `A`, where `ρ` is a lower bound of the `r`-th singular value of `X`. The bound
`θ < 1 / 2` comes from the constant `2` of the Lipschitz bound of the tangent projector in the
differentiated first-order condition. With the constant `1` of
`LeanDLRA/FixedRank/TangentSpace/ProjectorLipschitz.lean` the same argument gives

  `‖P(X) (Ȧ - Ẋ)‖ ≤ ρ⁻¹ ‖Ẋ‖ ‖A - X‖`,   `‖Ẋ‖ ≤ μ / (1 - θ)`   for every `θ < 1`,

and

  `‖Y t - X t‖ ≤ e^{(L + μ/ρ + κ)(t - a)} (δ + (L + κ) ∫ₐᵗ ‖X s - A s‖ ds)`,
  `κ = μ / ((1 - θ) ρ)`.

For `θ < 1 / 2` these constants are smaller than those of `dlra_norm_sub_le_integral_of_margin`
(`L + 2 μ/ρ + 2 μ / ((1 - 2 θ) ρ)` and `L + 2 μ / ((1 - 2 θ) ρ)`); for `θ = 1 / 4` they are
`L + 7 μ / (3 ρ)` and `L + 4 μ / (3 ρ)` in place of `L + 6 μ / ρ` and `L + 4 μ / ρ`.

## Main results

* `norm_tangentProjAt_sub_le_inv_mul_of_hasDerivWithinAt`: differentiated first-order
  optimality with the constant `1`, `‖P(X t) (A' - X')‖ ≤ ρ⁻¹ ‖X'‖ ‖A t - X t‖`.
* `norm_le_div_one_sub_of_tangentProjAt_sub_eq_zero`,
  `norm_sub_tangentProjAt_le_div_one_sub_of_tangentProjAt_sub_eq_zero`: `‖X'‖ ≤ μ / (1 - θ)` and
  `‖X' - P(X) A'‖ ≤ μ / ((1 - θ) ρ) ‖A - X‖` under the margin `‖X - A‖ ≤ θ ρ`, `θ < 1`.
* `dlra_norm_sub_le_integral_of_margin_lt_one`,
  `IsDLRASolution.norm_sub_le_integral_of_margin_lt_one`: the quasi-optimality bound under the
  margin `θ ρ`, `θ < 1`.

## Implementation notes

The margin `θ < 1` is where the argument stops: at `θ = 1` the inequality `(1 - θ) ‖Ẋ‖ ≤ μ` says
nothing. The speed bound `‖Ẋ‖ ≤ μ / (1 - θ)` cannot be improved for any `θ < 1`: for a unit
vector `u(t)` of `ℝ²` the curves `X t = u uᵀ` and `A t = θ • 1 + (1 - θ) • u uᵀ` have `ρ = 1`,
`‖A - X‖ = θ` and `Ȧ = (1 - θ) Ẋ`; this family is not formalized here. The `example`s restate
`dlra_norm_sub_le_integral_of_margin` verbatim and prove it from the bound of this file, and
show the hypotheses at the margin `θ = 3 / 4` with `A ≠ X`.
-/

open Set Finset Matrix Filter
open scoped Topology

namespace LeanDLRA

section QuasiOptimal

open scoped LeanDLRA.Frobenius
open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Differentiated first-order optimality, constant `1`.** Under the hypotheses of
`norm_tangentProjAt_sub_le_of_hasDerivWithinAt` (derivatives `A'`, `X'` at `t ∈ s` within `s`,
`X u` of rank `r` with `P(X u) (A u - X u) = 0` on `s`, `0 < ρ ≤ σ_{r-1}(X t)`):
`‖P(X t) (A' - X')‖ ≤ ρ⁻¹ ‖X'‖ ‖A t - X t‖`. -/
theorem norm_tangentProjAt_sub_le_inv_mul_of_hasDerivWithinAt {r : ℕ} {A X : ℝ → Matrix m n ℝ}
    {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ : ℝ} (hA : HasDerivWithinAt A A' s t)
    (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s) (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ)
    (hrank : ∀ u ∈ s, (X u).rank = r) (hσ : ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) :
    ‖tangentProjAt (X t) (A' - X')‖ ≤ ρ⁻¹ * ‖X'‖ * ‖A t - X t‖ := by
  have hφ : HasDerivWithinAt (fun u => tangentProjAt (X t) (A u - X u - (A t - X t)))
      (tangentProjAt (X t) (A' - X')) s t :=
    (tangentProjAt (X t)).hasFDerivAt.comp_hasDerivWithinAt t ((hA.sub hX).sub_const _)
  have hb : ∀ u ∈ s, ‖tangentProjAt (X t) (A u - X u - (A t - X t))‖ ≤
      ‖X u - X t‖ * (ρ⁻¹ * ‖A u - X u‖) := fun u hu => by
    have h := norm_tangentProjAt_apply_le_of_tangentProjAt_eq_zero (hrank t ht)
      (hrank u hu) hρ hσ (hopt u hu)
    rw [map_sub (tangentProjAt (X t)), hopt t ht, sub_zero]
    calc _ ≤ _ := h
      _ = _ := by ring
  have hg : ContinuousWithinAt (fun u => ρ⁻¹ * ‖A u - X u‖) s t :=
    continuousWithinAt_const.mul ((hA.continuousWithinAt.sub hX.continuousWithinAt).norm)
  have h := norm_deriv_le_of_norm_le_norm_sub_mul hφ hX hs (by simp) hg hb
  calc _ ≤ _ := h
    _ = _ := by ring

/-- The two derivative bounds under the margin `θ ρ`, `θ < 1`. -/
private theorem deriv_bounds_of_margin_lt_one {r : ℕ} {A X : ℝ → Matrix m n ℝ}
    {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ μ θ : ℝ} (hA : HasDerivWithinAt A A' s t)
    (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s) (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ)
    (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ : ∀ u ∈ s, ρ ≤ (toEuclideanLin (X u)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) (hμ : ‖A'‖ ≤ μ) (hθ : θ < 1)
    (hd : ‖X t - A t‖ ≤ θ * ρ) :
    ‖X'‖ ≤ μ / (1 - θ) ∧
      ‖X' - tangentProjAt (X t) A'‖ ≤ μ / ((1 - θ) * ρ) * ‖A t - X t‖ := by
  have htan : tangentProjAt (X t) X' = X' := tangentProjAt_eq_self_iff.mpr
    (mem_tangentSpaceAt_of_hasDerivWithinAt hX ht hs hρ hrank hσ)
  have hdef := norm_tangentProjAt_sub_le_inv_mul_of_hasDerivWithinAt hA hX ht hs hρ hrank
    (hσ t ht) hopt
  have hE : ρ⁻¹ * ‖A t - X t‖ ≤ θ := by
    rw [inv_mul_le_iff₀ hρ, norm_sub_rev]
    linarith
  have h1 : ‖tangentProjAt (X t) A'‖ ≤ μ := ((isOrthProj_tangentProjAt _).norm_le _).trans hμ
  have h1θ : 0 < 1 - θ := by linarith
  have hX' : ‖X'‖ ≤ μ / (1 - θ) := by
    have e : X' = tangentProjAt (X t) A' - tangentProjAt (X t) (A' - X') := by
      rw [map_sub, htan]
      abel
    have h3 : ‖X'‖ ≤ ‖tangentProjAt (X t) A'‖ + ‖tangentProjAt (X t) (A' - X')‖ := by
      conv_lhs => rw [e]
      exact norm_sub_le _ _
    have h4 : ρ⁻¹ * ‖X'‖ * ‖A t - X t‖ ≤ θ * ‖X'‖ := by
      have := mul_le_mul_of_nonneg_left hE (norm_nonneg X')
      linarith
    rw [le_div_iff₀ h1θ]
    linarith
  refine ⟨hX', ?_⟩
  have e : X' - tangentProjAt (X t) A' = -tangentProjAt (X t) (A' - X') := by
    rw [map_sub, htan]
    abel
  rw [e, norm_neg]
  refine hdef.trans ?_
  have hρ' : 0 ≤ ρ⁻¹ := by positivity
  calc ρ⁻¹ * ‖X'‖ * ‖A t - X t‖ ≤ ρ⁻¹ * (μ / (1 - θ)) * ‖A t - X t‖ := by gcongr
    _ = μ / ((1 - θ) * ρ) * ‖A t - X t‖ := by
      simp only [div_eq_mul_inv, mul_inv]
      ring

/-- **Speed of a curve of critical points under the margin `θ ρ`, `θ < 1`.** Under the
hypotheses of `norm_le_div_of_tangentProjAt_sub_eq_zero` with `θ < 1` in place of `2 θ < 1`:
`‖X'‖ ≤ μ / (1 - θ)`. -/
theorem norm_le_div_one_sub_of_tangentProjAt_sub_eq_zero {r : ℕ} {A X : ℝ → Matrix m n ℝ}
    {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ μ θ : ℝ} (hA : HasDerivWithinAt A A' s t)
    (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s) (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ)
    (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ : ∀ u ∈ s, ρ ≤ (toEuclideanLin (X u)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) (hμ : ‖A'‖ ≤ μ) (hθ : θ < 1)
    (hd : ‖X t - A t‖ ≤ θ * ρ) : ‖X'‖ ≤ μ / (1 - θ) :=
  (deriv_bounds_of_margin_lt_one hA hX ht hs hρ hrank hσ hopt hμ hθ hd).1

/-- **The velocity of a curve of critical points under the margin `θ ρ`, `θ < 1`.** Under the
hypotheses of `norm_le_div_one_sub_of_tangentProjAt_sub_eq_zero`:
`‖X' - P(X t) A'‖ ≤ μ / ((1 - θ) ρ) ‖A t - X t‖`. -/
theorem norm_sub_tangentProjAt_le_div_one_sub_of_tangentProjAt_sub_eq_zero {r : ℕ}
    {A X : ℝ → Matrix m n ℝ} {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ μ θ : ℝ}
    (hA : HasDerivWithinAt A A' s t) (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s)
    (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ) (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ : ∀ u ∈ s, ρ ≤ (toEuclideanLin (X u)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) (hμ : ‖A'‖ ≤ μ) (hθ : θ < 1)
    (hd : ‖X t - A t‖ ≤ θ * ρ) :
    ‖X' - tangentProjAt (X t) A'‖ ≤ μ / ((1 - θ) * ρ) * ‖A t - X t‖ :=
  (deriv_bounds_of_margin_lt_one hA hX ht hs hρ hrank hσ hopt hμ hθ hd).2

/-- The derivative bounds at a time `t ∈ [a, b)` from right derivatives on `[t, b]`, under the
margin `θ ρ`, `θ < 1`, together with the tangency of `X' t`. -/
private theorem deriv_bounds_on_Ico_of_margin_lt_one {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' : ℝ → Matrix m n ℝ} {a b μ ρ θ : ℝ}
    (hρ : 0 < ρ) (hA : ODESolution F A a b) (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ)
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ θ * ρ) {t : ℝ} (ht : t ∈ Ico a b) :
    tangentProjAt (X t) (X' t) = X' t ∧ ‖X' t‖ ≤ μ / (1 - θ) ∧
      ‖X' t - tangentProjAt (X t) (F t (A t))‖ ≤ μ / ((1 - θ) * ρ) * ‖A t - X t‖ := by
  have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc_left ht.1
  have hts : t ∈ Icc t b := ⟨le_rfl, ht.2.le⟩
  have hs : (𝓝[Icc t b \ {t}] t).NeBot := by
    rw [Icc_sdiff_left]
    exact left_nhdsWithin_Ioc_neBot ht.2
  have hA' := (hA.deriv t ht).mono (Icc_subset_Ici_self : Icc t b ⊆ Ici t)
  have hX' := (hX t ht).mono (Icc_subset_Ici_self : Icc t b ⊆ Ici t)
  have hrank : ∀ u ∈ Icc t b, (X u).rank = r := fun u hu => hXr u (hsub hu)
  have hσ' : ∀ u ∈ Icc t b, ρ ≤ (toEuclideanLin (X u)).singularValues (r - 1) :=
    fun u hu => hσ u (hsub hu)
  have hopt' : ∀ u ∈ Icc t b, tangentProjAt (X u) (A u - X u) = 0 := fun u hu => hopt u (hsub hu)
  exact ⟨tangentProjAt_eq_self_iff.mpr
      (mem_tangentSpaceAt_of_hasDerivWithinAt hX' hts hs hρ hrank hσ'),
    deriv_bounds_of_margin_lt_one hA' hX' hts hs hρ hrank hσ' hopt' (hμ t ht) hθ
      (hd t (Ico_subset_Icc_self ht))⟩

/-- **Quasi-optimality of matrix DLRA along a curve of critical points, margin `θ ρ` with
`θ < 1`.** Under the hypotheses of `dlra_norm_sub_le_integral_of_margin`, with `θ < 1` in place of
`2 θ < 1`, and with `κ = μ / ((1 - θ) ρ)`, for `t ∈ [a, b]`

  `‖Y t - X t‖ ≤ e^{(L + μ/ρ + κ)(t - a)} (δ + (L + κ) ∫ₐᵗ ‖X s - A s‖ ds)`.

For `2 θ < 1` the two constants are below those of `dlra_norm_sub_le_integral_of_margin`. -/
theorem dlra_norm_sub_le_integral_of_margin_lt_one {r : ℕ}
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
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + μ / ρ + μ / ((1 - θ) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - θ) * ρ)) * ∫ s in a..t, ‖X s - A s‖) := by
  intro t0 ht0
  rcases eq_or_lt_of_le ht0.1 with h0 | hpos
  · subst h0
    simpa using hδ
  have hab : a < b := hpos.trans_le ht0.2
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ a ⟨le_rfl, hab⟩)
  have h1θ : 0 < 1 - θ := by linarith
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = μ / ((1 - θ) * ρ) := ⟨_, rfl⟩
  rw [← hκ]
  have hκ0 : 0 ≤ κ := by
    rw [hκ]
    exact div_nonneg hμ0 (mul_pos h1θ hρ).le
  have hκ₁ : 0 ≤ μ / ρ := div_nonneg hμ0 hρ.le
  have hIcc : Icc a t0 ⊆ Icc a b := Icc_subset_Icc_right ht0.2
  have hIco : ∀ s ∈ Ico a t0, s ∈ Ico a b := fun s hs => ⟨hs.1, hs.2.trans_le ht0.2⟩
  obtain ⟨ηc, hηc, hηeq⟩ : ∃ η : ℝ → ℝ, Continuous η ∧ ∀ s ∈ Icc a b, η s = ‖X s - A s‖ :=
    ⟨fun s => ‖X (projIcc a b hab.le s) - A (projIcc a b hab.le s)‖,
      (hXc.sub hA.cont).norm.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        fun s => (projIcc a b hab.le s).2,
      fun s hs => by simp only [projIcc_of_mem _ hs]⟩
  have hb := fun s (hs : s ∈ Ico a b) =>
    deriv_bounds_on_Ico_of_margin_lt_one hρ hA hμ hX hXr hσ hopt hθ hd hs
  have hP : ∀ s ∈ Icc a b,
      IsOrthProj (tangentProj (U s) (V s) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
    fun s hs => isOrthProj_tangentProj (hUV s hs).1 (hUV s hs).2.1
  have hρ' : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ.le
  have h₁ : ∀ s ∈ Ico a t0, ‖tangentProj (U s) (V s) (F s (X s) - X' s)‖ ≤
      μ / ρ * ‖Y s - X s‖ + (L + κ) * ηc s := fun s hs => by
    have hsb := hIco s hs
    have hsI := Ico_subset_Icc_self hsb
    obtain ⟨-, -, hbest⟩ := hb s hsb
    obtain ⟨hU, hV, hYs⟩ := hUV s hsI
    have hsplit : F s (X s) - X' s = (F s (X s) - F s (A s)) +
        (F s (A s) - tangentProjAt (X s) (F s (A s))) -
        (X' s - tangentProjAt (X s) (F s (A s))) := by abel
    have e1 : ‖tangentProj (U s) (V s) (F s (X s) - F s (A s))‖ ≤ L * ηc s :=
      ((hP s hsI).norm_le _).trans ((hF s _ _).trans (le_of_eq (by rw [hηeq s hsI])))
    have e2 : ‖tangentProj (U s) (V s) (F s (A s) - tangentProjAt (X s) (F s (A s)))‖ ≤
        μ / ρ * ‖Y s - X s‖ := by
      have hQ0 : tangentProjAt (X s) (F s (A s) - tangentProjAt (X s) (F s (A s))) = 0 := by
        rw [map_sub, (isOrthProj_tangentProjAt _).idem, sub_self]
      have hN := norm_tangentProj_apply_le_of_tangentProjAt_eq_zero (hXr s hsI) hρ (hσ s hsI)
        hU hV (S s) hQ0
      rw [← hYs] at hN
      refine hN.trans ?_
      have hn : ‖F s (A s) - tangentProjAt (X s) (F s (A s))‖ ≤ μ := by
        have := (isOrthProj_tangentProjAt (X s)).compl.norm_le (F s (A s))
        simp only [sub_apply, one_apply_eq_self] at this
        exact this.trans (hμ s hsb)
      calc ρ⁻¹ * ‖Y s - X s‖ * ‖F s (A s) - tangentProjAt (X s) (F s (A s))‖ ≤
          ρ⁻¹ * ‖Y s - X s‖ * μ :=
            mul_le_mul_of_nonneg_left hn (mul_nonneg hρ' (norm_nonneg _))
        _ = μ / ρ * ‖Y s - X s‖ := by rw [div_eq_mul_inv]; ring
    have e3 : ‖tangentProj (U s) (V s) (X' s - tangentProjAt (X s) (F s (A s)))‖ ≤ κ * ηc s :=
      ((hP s hsI).norm_le _).trans (by
        rw [hηeq s hsI, norm_sub_rev (X s), hκ]
        exact hbest)
    rw [hsplit, map_sub, map_add]
    calc _ ≤ ‖tangentProj (U s) (V s) (F s (X s) - F s (A s))‖ +
          ‖tangentProj (U s) (V s) (F s (A s) - tangentProjAt (X s) (F s (A s)))‖ +
          ‖tangentProj (U s) (V s) (X' s - tangentProjAt (X s) (F s (A s)))‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ L * ηc s + μ / ρ * ‖Y s - X s‖ + κ * ηc s := add_le_add (add_le_add e1 e2) e3
      _ = _ := by ring
  have h₂ : ∀ s ∈ Ico a t0, ‖(1 - tangentProj (U s) (V s)) (X' s)‖ ≤
      κ * ‖Y s - X s‖ + (fun _ : ℝ => (0 : ℝ)) s := fun s hs => by
    have hsb := hIco s hs
    have hsI := Ico_subset_Icc_self hsb
    obtain ⟨htan, hX's, -⟩ := hb s hsb
    obtain ⟨hU, hV, hYs⟩ := hUV s hsI
    have hT := norm_one_sub_tangentProj_apply_le_of_tangentProjAt_eq_self (hXr s hsI) hρ
      (hσ s hsI) hU hV (S s) htan
    rw [← hYs] at hT
    rw [add_zero]
    refine hT.trans ?_
    calc ρ⁻¹ * ‖Y s - X s‖ * ‖X' s‖ ≤ ρ⁻¹ * ‖Y s - X s‖ * (μ / (1 - θ)) :=
          mul_le_mul_of_nonneg_left hX's (mul_nonneg hρ' (norm_nonneg _))
      _ = κ * ‖Y s - X s‖ := by
          rw [hκ]
          simp only [div_eq_mul_inv, mul_inv]
          ring
  have hYsol : ODESolution (fun t x => tangentProj (U t) (V t) (F t x)) Y a t0 :=
    ⟨hY.cont.mono hIcc, fun s hs => hY.deriv s (hIco s hs)⟩
  have hcmp := ODESolution.dlra_norm_sub_le_of_comparison_integral
    (P := fun t => tangentProj (U t) (V t)) (F := F) (Y := Y) (a := a) (b := t0) (L := L)
    (κ₁ := μ / ρ) (κ₂ := κ) (δ := δ)
    (η₁ := fun s => (L + κ) * ηc s) (η₂ := fun _ => 0)
    (continuous_const.mul hηc) continuous_const hF hYsol
    (fun s hs => hP s (hIcc (Ico_subset_Icc_self hs))) (hXc.mono hIcc)
    (fun s hs => hX s (hIco s hs)) h₁ h₂ hδ t0 ⟨ht0.1, le_rfl⟩
  have hK : 0 ≤ L + μ / ρ + κ := by linarith
  have hgb := gronwallIntegralBound_le (δ := δ)
    (η := fun s => (L + κ) * ηc s + (fun _ : ℝ => (0 : ℝ)) s)
    ((continuous_const.mul hηc).add continuous_const) hK ht0.1 (fun s hs => by
      have : 0 ≤ ηc s := by rw [hηeq s (hIcc hs)]; exact norm_nonneg _
      simp only [add_zero]
      exact mul_nonneg (by linarith) this)
  have hJ : ∫ s in a..t0, ((L + κ) * ηc s + (fun _ : ℝ => (0 : ℝ)) s) =
      (L + κ) * ∫ s in a..t0, ‖X s - A s‖ := by
    simp only [add_zero]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht0.1] at hs
    exact hηeq s (hIcc hs)
  refine hcmp.trans (hgb.trans (le_of_eq ?_))
  rw [hJ]

/-- **Quasi-optimality for a DLRA solution of rank `r`, margin `θ ρ` with `θ < 1`.** The bound of
`dlra_norm_sub_le_integral_of_margin_lt_one` for a DLRA solution `Y` of rank `r` of
`Ẏ = P(Y) F(t, Y)` (`IsDLRASolution`): with `κ = μ / ((1 - θ) ρ)`,
`‖Y t - X t‖ ≤ e^{(L + μ/ρ + κ)(t - a)} (δ + (L + κ) ∫ₐᵗ ‖X s - A s‖ ds)`. -/
theorem IsDLRASolution.norm_sub_le_integral_of_margin_lt_one {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ θ δ : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hA : ODESolution F A a b) (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ)
    (hXc : ContinuousOn X (Icc a b)) (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ θ * ρ) (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + μ / ρ + μ / ((1 - θ) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - θ) * ρ)) * ∫ s in a..t, ‖X s - A s‖) := by
  have hfac : ∀ t ∈ Icc a b, ∃ (U : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ)
      (V : Matrix n (Fin r) ℝ), Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ IsUnit S.det ∧ Y t = U * S * Vᵀ :=
    fun t ht => (SVD.rank_eq_iff_exists_factor (Y t)).1 (hY.2 t ht)
  choose! U S V hU hV hS hYeq using hfac
  have hY' : ODESolution (fun t x => tangentProj (U t) (V t) (F t x)) Y a b :=
    ⟨hY.1.cont, fun t ht => have ht' := Ico_subset_Icc_self ht
      DynamicallyOrthogonal.IsDLRASolution.hasDerivWithinAt_tangentProj hY ht (hU t ht')
        (hV t ht') (hS t ht') (hYeq t ht')⟩
  exact dlra_norm_sub_le_integral_of_margin_lt_one hρ hL hF hA hμ hXc hX hXr hσ hopt hθ hd
    (fun t ht => ⟨hU t ht, hV t ht, hYeq t ht⟩) hY' hδ

/-! ### The margins below `ρ / 2` -/

/-- `dlra_norm_sub_le_integral_of_margin`, restated verbatim, follows from
`dlra_norm_sub_le_integral_of_margin_lt_one`: for `2 θ < 1` the constants
`L + μ/ρ + μ / ((1 - θ) ρ)` and `L + μ / ((1 - θ) ρ)` are at most
`L + 2 μ/ρ + 2 μ / ((1 - 2 θ) ρ)` and `L + 2 μ / ((1 - 2 θ) ρ)`. -/
example {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ θ δ : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hF : IsLipschitzField F L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0) (hθ : 2 * θ < 1)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ θ * ρ)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t x => tangentProj (U t) (V t) (F t x)) Y a b)
    (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + 2 * μ / ρ + 2 * μ / ((1 - 2 * θ) * ρ)) * (t - a)) *
        (δ + (L + 2 * μ / ((1 - 2 * θ) * ρ)) * ∫ s in a..t, ‖X s - A s‖) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0
    simpa using hδ
  have hab : a < b := hpos.trans_le ht.2
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ a ⟨le_rfl, hab⟩)
  have hθ0 : 0 ≤ θ :=
    nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hd a ⟨le_rfl, hab.le⟩)) hρ
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have key := dlra_norm_sub_le_integral_of_margin_lt_one (θ := θ) hρ hL hF hA hμ hXc hX hXr hσ
    hopt (by linarith) hd hUV hY hδ t ht
  have hd1 : 0 < (1 - 2 * θ) * ρ := mul_pos (by linarith) hρ
  have hd2 : 0 < (1 - θ) * ρ := mul_pos (by linarith) hρ
  have hle : (1 - 2 * θ) * ρ ≤ (1 - θ) * ρ := mul_le_mul_of_nonneg_right (by linarith) hρ.le
  have k1 : μ / ρ ≤ 2 * μ / ρ := div_le_div_of_nonneg_right (by linarith) hρ.le
  have k3 : μ / ((1 - θ) * ρ) ≤ 2 * μ / ((1 - 2 * θ) * ρ) :=
    (div_le_div_of_nonneg_left hμ0 hd1 hle).trans
      (div_le_div_of_nonneg_right (by linarith) hd1.le)
  have k30 : 0 ≤ μ / ((1 - θ) * ρ) := div_nonneg hμ0 hd2.le
  have hI : 0 ≤ ∫ s in a..t, ‖X s - A s‖ :=
    intervalIntegral.integral_nonneg ht.1 fun _ _ => norm_nonneg _
  exact key.trans (mul_le_mul
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) (by linarith [ht.1])))
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right (by linarith) hI))
    (add_nonneg hδ0 (mul_nonneg (by linarith) hI)) (Real.exp_nonneg _))

end QuasiOptimal

namespace QuasiOptimalityNormalExamples

open scoped LeanDLRA.Frobenius
open QuasiOptimalityExamples

/-- The normal part `diag(0, 3/4)` of the examples: the margin `θ = 3/4`. -/
local notation "N₃" => (!![0, 0; 0, 3 / 4] : Matrix (Fin 2) (Fin 2) ℝ)

private theorem tangentProjAt_smul_e₁_N₃ {c : ℝ} (hc : c ≠ 0) :
    tangentProjAt (c • (e₁ * e₁ᵀ)) N₃ = 0 := by
  have h1 : e₁ᵀ * N₃ = 0 := by
    ext i j
    fin_cases i
    fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h2 : N₃ * e₁ = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [tangentProjAt_smul_e₁ hc, tangentProj_apply, Matrix.mul_assoc e₁ e₁ᵀ N₃, h1, h2]
  simp

private theorem norm_N₃_le : ‖N₃‖ ≤ 3 / 4 := by
  have h : ‖N₃‖ ^ 2 = (3 / 4) ^ 2 := by
    rw [Curvature.frob_sq]
    norm_num [Fin.sum_univ_two]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp h.le

private theorem hasDerivAt_smul_e₁_add_N₃ (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₃) (e₁ * e₁ᵀ) t := by
  simpa using (hasDerivAt_smul_e₁ 1 t).add_const N₃

/-- The hypotheses on `X t = (1 + t) e₁ e₁ᵀ` and `A t = X t + diag(0, 3/4)` for `t ≥ 0`, with
`r = 1`, `ρ = 1` and the margin `θ = 3/4`. -/
private theorem hyps_N₃ {t : ℝ} (ht : 0 ≤ t) :
    ((1 + t) • (e₁ * e₁ᵀ)).rank = 1 ∧
    (1 : ℝ) ≤ (toEuclideanLin ((1 + t) • (e₁ * e₁ᵀ))).singularValues (1 - 1) ∧
    tangentProjAt ((1 + t) • (e₁ * e₁ᵀ)) ((1 + t) • (e₁ * e₁ᵀ) + N₃ - (1 + t) • (e₁ * e₁ᵀ)) = 0 ∧
    ‖(1 + t) • (e₁ * e₁ᵀ) - ((1 + t) • (e₁ * e₁ᵀ) + N₃)‖ ≤ 3 / 4 * 1 := by
  have hc : (1 + t) ≠ 0 := ne_of_gt (by linarith)
  refine ⟨rank_smul_e₁ hc, one_le_singularValues_smul_e₁ (by linarith), ?_, ?_⟩
  · rw [add_sub_cancel_left]
    exact tangentProjAt_smul_e₁_N₃ hc
  · rw [sub_add_cancel_left, norm_neg]
    linarith [norm_N₃_le]

/-- `norm_tangentProjAt_sub_le_inv_mul_of_hasDerivWithinAt`,
`norm_le_div_one_sub_of_tangentProjAt_sub_eq_zero` and
`norm_sub_tangentProjAt_le_div_one_sub_of_tangentProjAt_sub_eq_zero` for the curves
`X t = (1 + t) e₁ e₁ᵀ` and `A t = X t + diag(0, 3/4)` (`r = 1`, `ρ = μ = 1`) at `t = 0` within
`[0, 1]`, with the margin `θ = 3/4`, which is above `1/2`. -/
example :
    ‖tangentProjAt (((1 : ℝ) + 0) • (e₁ * e₁ᵀ)) (e₁ * e₁ᵀ - e₁ * e₁ᵀ)‖ ≤
      1⁻¹ * ‖e₁ * e₁ᵀ‖ * ‖((1 : ℝ) + 0) • (e₁ * e₁ᵀ) + N₃ - ((1 : ℝ) + 0) • (e₁ * e₁ᵀ)‖ ∧
    ‖e₁ * e₁ᵀ‖ ≤ 1 / (1 - 3 / 4) ∧
    ‖e₁ * e₁ᵀ - tangentProjAt (((1 : ℝ) + 0) • (e₁ * e₁ᵀ)) (e₁ * e₁ᵀ)‖ ≤
      1 / ((1 - 3 / 4) * 1) *
        ‖((1 : ℝ) + 0) • (e₁ * e₁ᵀ) + N₃ - ((1 : ℝ) + 0) • (e₁ * e₁ᵀ)‖ := by
  have hs : (𝓝[Set.Icc (0 : ℝ) 1 \ {0}] 0).NeBot := by
    rw [Icc_sdiff_left]
    exact left_nhdsWithin_Ioc_neBot one_pos
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hA := (hasDerivAt_smul_e₁_add_N₃ 0).hasDerivWithinAt (s := Set.Icc (0 : ℝ) 1)
  have hX := (hasDerivAt_smul_e₁ 1 0).hasDerivWithinAt (s := Set.Icc (0 : ℝ) 1)
  have hr : ∀ u ∈ Set.Icc (0 : ℝ) 1, ((fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) u).rank = 1 :=
    fun u hu => (hyps_N₃ hu.1).1
  have hσ : ∀ u ∈ Set.Icc (0 : ℝ) 1, (1 : ℝ) ≤
      (toEuclideanLin ((fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) u)).singularValues (1 - 1) :=
    fun u hu => (hyps_N₃ hu.1).2.1
  have ho : ∀ u ∈ Set.Icc (0 : ℝ) 1, tangentProjAt ((fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) u)
      ((fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₃) u - (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) u) = 0 :=
    fun u hu => (hyps_N₃ hu.1).2.2.1
  have hd := (hyps_N₃ (le_refl (0 : ℝ))).2.2.2
  have r1 := norm_tangentProjAt_sub_le_inv_mul_of_hasDerivWithinAt hA hX h0 hs one_pos hr
    (hσ 0 h0) ho
  have r2 := norm_le_div_one_sub_of_tangentProjAt_sub_eq_zero (θ := 3 / 4) hA hX h0 hs one_pos
    hr hσ ho norm_e₁_mul_le (by norm_num) hd
  have r3 := norm_sub_tangentProjAt_le_div_one_sub_of_tangentProjAt_sub_eq_zero (θ := 3 / 4) hA
    hX h0 hs one_pos hr hσ ho norm_e₁_mul_le (by norm_num) hd
  exact ⟨r1, r2, r3⟩

/-- **Non-vacuity of `dlra_norm_sub_le_integral_of_margin_lt_one` and of
`IsDLRASolution.norm_sub_le_integral_of_margin_lt_one`** at the margin `θ = 3/4`: for
`X t = Y t = (1 + t) e₁ e₁ᵀ` and `A t = X t + diag(0, 3/4)` on `[0, 1]`, `F(t, Y) = e₁ e₁ᵀ`
(`L = 0`), `r = 1`, `ρ = μ = 1` and `δ = 0` the hypotheses hold, with `‖X t - A t‖ = 3/4`. The
margin `2 θ < 1` of `dlra_norm_sub_le_integral_of_margin` does not hold for these curves. -/
example : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(1 + t) • (e₁ * e₁ᵀ) - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
      Real.exp ((0 + 1 / 1 + 1 / ((1 - 3 / 4) * 1)) * (t - 0)) *
        (0 + (0 + 1 / ((1 - 3 / 4) * 1)) *
          ∫ s in (0 : ℝ)..t, ‖(1 + s) • (e₁ * e₁ᵀ) - ((1 + s) • (e₁ * e₁ᵀ) + N₃)‖) := by
  have hc : ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 + t) ≠ 0 := fun t ht => ne_of_gt (by linarith [ht.1])
  have hXc : ContinuousOn (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) (Set.Icc 0 1) :=
    fun s _ => (hasDerivAt_smul_e₁ 1 s).continuousAt.continuousWithinAt
  have hsol : ODESolution (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ)
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₃) 0 1 :=
    ⟨fun s _ => (hasDerivAt_smul_e₁_add_N₃ s).continuousAt.continuousWithinAt,
      fun s _ => (hasDerivAt_smul_e₁_add_N₃ s).hasDerivWithinAt⟩
  have hYd : IsDLRASolution 1 (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ)
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) 0 1 := by
    refine ⟨⟨hXc, fun s hs => ?_⟩, fun t ht => rank_smul_e₁ (hc t ht)⟩
    have h := (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt (s := Ici s)
    convert h using 1
    exact tangentProjAt_smul_e₁_apply (hc s (Ico_subset_Icc_self hs))
  exact hYd.norm_sub_le_integral_of_margin_lt_one
    (A := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₃)
    (X := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) (X' := fun _ => e₁ * e₁ᵀ) (θ := 3 / 4) one_pos
    le_rfl (fun _ _ _ => by simp) hsol (fun _ _ => norm_e₁_mul_le) hXc
    (fun s _ => (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt) (fun t ht => (hyps_N₃ ht.1).1)
    (fun t ht => (hyps_N₃ ht.1).2.1) (fun t ht => (hyps_N₃ ht.1).2.2.1) (by norm_num)
    (fun t ht => (hyps_N₃ ht.1).2.2.2) (by simp)

end QuasiOptimalityNormalExamples

end LeanDLRA
