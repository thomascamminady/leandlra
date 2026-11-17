import LeanDLRA.DLRA.QuasiOptimality

/-!
# Quasi-optimality of matrix DLRA with a margin below `ρ / 2`

The quasi-optimality bounds of `LeanDLRA/DLRA/QuasiOptimality.lean` assume that the approximation
error of the curve `X` of critical points is at most a quarter of the lower bound `ρ` of its
`r`-th singular value, `‖X t - A t‖ ≤ ρ / 4`. In the proof this margin is used once: the
differentiated first-order condition `‖P(X) (Ȧ - Ẋ)‖ ≤ 2 ρ⁻¹ ‖Ẋ‖ ‖A - X‖`
(`norm_tangentProjAt_sub_le_of_hasDerivWithinAt`) is absorbed into the left-hand side of
`‖Ẋ‖ ≤ ‖P(X) Ȧ‖ + ‖P(X) (Ȧ - Ẋ)‖`. Every margin `‖X t - A t‖ ≤ θ ρ` with `θ < 1 / 2` can be
absorbed, and gives `‖Ẋ‖ ≤ μ / (1 - 2 θ)`. The constants of the bound become

  `e^{(L + 2 μ/ρ + κ)(t - a)} (δ + (L + κ) ∫ₐᵗ ‖X s - A s‖ ds)`,   `κ = 2 μ / ((1 - 2 θ) ρ)`,

which for `θ = 1 / 4` are the constants `L + 6 μ / ρ` and `L + 4 μ / ρ` of
`dlra_norm_sub_le_integral`, and are smaller for `θ < 1 / 4`.

## Main results

* `norm_le_div_of_tangentProjAt_sub_eq_zero`,
  `norm_sub_tangentProjAt_le_div_of_tangentProjAt_sub_eq_zero`: `‖Ẋ‖ ≤ μ / (1 - 2 θ)` and
  `‖Ẋ - P(X) Ȧ‖ ≤ 2 μ / ((1 - 2 θ) ρ) ‖A - X‖` under the margin `‖X - A‖ ≤ θ ρ`, `2 θ < 1`.
* `dlra_norm_sub_le_integral_of_margin`, `IsDLRASolution.norm_sub_le_integral_of_margin`: the
  quasi-optimality bound under the margin `θ ρ`.

## Implementation notes

The bound `θ < 1 / 2` is where the argument stops: at `θ = 1 / 2` the inequality
`(1 - 2 θ) ‖Ẋ‖ ≤ μ` says nothing. Whether a margin up to `ρ` suffices (the best approximation
is differentiable as long as the singular values `σ_{r-1} > σ_r` are separated) would need a
curvature bound with a constant below `2` for normal directions; this is not shown here.
The `example`s at the end restate `dlra_norm_sub_le_integral` and
`IsDLRASolution.norm_sub_le_integral` verbatim and prove them from the results with `θ = 1 / 4`.
-/

open Set Finset Matrix Filter
open scoped Topology

namespace LeanDLRA

section QuasiOptimal

open scoped LeanDLRA.Frobenius
open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The two derivative bounds under the margin `θ ρ`. -/
private theorem deriv_bounds_of_margin {r : ℕ} {A X : ℝ → Matrix m n ℝ}
    {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ μ θ : ℝ} (hA : HasDerivWithinAt A A' s t)
    (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s) (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ)
    (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ : ∀ u ∈ s, ρ ≤ (toEuclideanLin (X u)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) (hμ : ‖A'‖ ≤ μ) (hθ : 2 * θ < 1)
    (hd : ‖X t - A t‖ ≤ θ * ρ) :
    ‖X'‖ ≤ μ / (1 - 2 * θ) ∧
      ‖X' - tangentProjAt (X t) A'‖ ≤ 2 * μ / ((1 - 2 * θ) * ρ) * ‖A t - X t‖ := by
  have htan : tangentProjAt (X t) X' = X' := tangentProjAt_eq_self_iff.mpr
    (mem_tangentSpaceAt_of_hasDerivWithinAt hX ht hs hρ hrank hσ)
  have hdef := norm_tangentProjAt_sub_le_of_hasDerivWithinAt hA hX ht hs hρ hrank (hσ t ht) hopt
  have hE : ρ⁻¹ * ‖A t - X t‖ ≤ θ := by
    rw [inv_mul_le_iff₀ hρ, norm_sub_rev]
    linarith
  have h1 : ‖tangentProjAt (X t) A'‖ ≤ μ := ((isOrthProj_tangentProjAt _).norm_le _).trans hμ
  have h1θ : 0 < 1 - 2 * θ := by linarith
  have hX' : ‖X'‖ ≤ μ / (1 - 2 * θ) := by
    have e : X' = tangentProjAt (X t) A' - tangentProjAt (X t) (A' - X') := by
      rw [map_sub, htan]
      abel
    have h3 : ‖X'‖ ≤ ‖tangentProjAt (X t) A'‖ + ‖tangentProjAt (X t) (A' - X')‖ := by
      conv_lhs => rw [e]
      exact norm_sub_le _ _
    have h4 : 2 * ρ⁻¹ * ‖X'‖ * ‖A t - X t‖ ≤ 2 * θ * ‖X'‖ := by
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
  have hρ' : 0 ≤ 2 * ρ⁻¹ := by positivity
  calc 2 * ρ⁻¹ * ‖X'‖ * ‖A t - X t‖ ≤ 2 * ρ⁻¹ * (μ / (1 - 2 * θ)) * ‖A t - X t‖ := by gcongr
    _ = 2 * μ / ((1 - 2 * θ) * ρ) * ‖A t - X t‖ := by
      simp only [div_eq_mul_inv, mul_inv]
      ring

/-- **Speed of a curve of critical points under the margin `θ ρ`.** Under the hypotheses of
`norm_le_of_tangentProjAt_sub_eq_zero` with the margin `‖X t - A t‖ ≤ θ ρ` in place of
`‖X t - A t‖ ≤ ρ / 4`, where `2 θ < 1`: `‖X'‖ ≤ μ / (1 - 2 θ)`. For `θ = 1 / 4` this is
`‖X'‖ ≤ 2 μ`. -/
theorem norm_le_div_of_tangentProjAt_sub_eq_zero {r : ℕ} {A X : ℝ → Matrix m n ℝ}
    {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ μ θ : ℝ} (hA : HasDerivWithinAt A A' s t)
    (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s) (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ)
    (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ : ∀ u ∈ s, ρ ≤ (toEuclideanLin (X u)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) (hμ : ‖A'‖ ≤ μ) (hθ : 2 * θ < 1)
    (hd : ‖X t - A t‖ ≤ θ * ρ) : ‖X'‖ ≤ μ / (1 - 2 * θ) :=
  (deriv_bounds_of_margin hA hX ht hs hρ hrank hσ hopt hμ hθ hd).1

/-- **The velocity of a curve of critical points under the margin `θ ρ`.** Under the hypotheses
of `norm_le_div_of_tangentProjAt_sub_eq_zero`:
`‖X' - P(X t) A'‖ ≤ 2 μ / ((1 - 2 θ) ρ) ‖A t - X t‖`. For `θ = 1 / 4` this is the bound
`4 μ / ρ` of `norm_sub_tangentProjAt_le_of_tangentProjAt_sub_eq_zero`. -/
theorem norm_sub_tangentProjAt_le_div_of_tangentProjAt_sub_eq_zero {r : ℕ}
    {A X : ℝ → Matrix m n ℝ} {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ μ θ : ℝ}
    (hA : HasDerivWithinAt A A' s t) (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s)
    (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ) (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ : ∀ u ∈ s, ρ ≤ (toEuclideanLin (X u)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) (hμ : ‖A'‖ ≤ μ) (hθ : 2 * θ < 1)
    (hd : ‖X t - A t‖ ≤ θ * ρ) :
    ‖X' - tangentProjAt (X t) A'‖ ≤ 2 * μ / ((1 - 2 * θ) * ρ) * ‖A t - X t‖ :=
  (deriv_bounds_of_margin hA hX ht hs hρ hrank hσ hopt hμ hθ hd).2

/-- The derivative bounds at a time `t ∈ [a, b)` from right derivatives on `[t, b]`, under the
margin `θ ρ`, together with the tangency of `X' t`. -/
private theorem deriv_bounds_on_Ico_of_margin {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A X X' : ℝ → Matrix m n ℝ} {a b μ ρ θ : ℝ} (hρ : 0 < ρ) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ)
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0) (hθ : 2 * θ < 1)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ θ * ρ) {t : ℝ} (ht : t ∈ Ico a b) :
    tangentProjAt (X t) (X' t) = X' t ∧ ‖X' t‖ ≤ μ / (1 - 2 * θ) ∧
      ‖X' t - tangentProjAt (X t) (F t (A t))‖ ≤ 2 * μ / ((1 - 2 * θ) * ρ) * ‖A t - X t‖ := by
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
    deriv_bounds_of_margin hA' hX' hts hs hρ hrank hσ' hopt' (hμ t ht) hθ
      (hd t (Ico_subset_Icc_self ht))⟩

/-- **Quasi-optimality of matrix DLRA along a curve of critical points, margin `θ ρ`.** Under the
hypotheses of `dlra_norm_sub_le_integral`, with the margin `‖X t - A t‖ ≤ θ ρ` (`2 θ < 1`) in
place of `‖X t - A t‖ ≤ ρ / 4`, and with `κ = 2 μ / ((1 - 2 θ) ρ)`, for `t ∈ [a, b]`

  `‖Y t - X t‖ ≤ e^{(L + 2 μ/ρ + κ)(t - a)} (δ + (L + κ) ∫ₐᵗ ‖X s - A s‖ ds)`.

For `θ = 1 / 4` the constants are those of `dlra_norm_sub_le_integral`; for `θ < 1 / 4` they are
smaller, and as `θ → 0` they tend to `L + 4 μ / ρ` and `L + 2 μ / ρ`. -/
theorem dlra_norm_sub_le_integral_of_margin {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
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
  intro t0 ht0
  rcases eq_or_lt_of_le ht0.1 with h0 | hpos
  · subst h0
    simpa using hδ
  have hab : a < b := hpos.trans_le ht0.2
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ a ⟨le_rfl, hab⟩)
  have h1θ : 0 < 1 - 2 * θ := by linarith
  set κ := 2 * μ / ((1 - 2 * θ) * ρ) with hκ
  have hκ0 : 0 ≤ κ := div_nonneg (by linarith) (mul_pos h1θ hρ).le
  have hκ₁ : 0 ≤ 2 * μ / ρ := div_nonneg (by linarith) hρ.le
  have hIcc : Icc a t0 ⊆ Icc a b := Icc_subset_Icc_right ht0.2
  have hIco : ∀ s ∈ Ico a t0, s ∈ Ico a b := fun s hs => ⟨hs.1, hs.2.trans_le ht0.2⟩
  obtain ⟨ηc, hηc, hηeq⟩ : ∃ η : ℝ → ℝ, Continuous η ∧ ∀ s ∈ Icc a b, η s = ‖X s - A s‖ :=
    ⟨fun s => ‖X (projIcc a b hab.le s) - A (projIcc a b hab.le s)‖,
      (hXc.sub hA.cont).norm.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        fun s => (projIcc a b hab.le s).2,
      fun s hs => by simp only [projIcc_of_mem _ hs]⟩
  have hb := fun s (hs : s ∈ Ico a b) =>
    deriv_bounds_on_Ico_of_margin hρ hA hμ hX hXr hσ hopt hθ hd hs
  have hP : ∀ s ∈ Icc a b,
      IsOrthProj (tangentProj (U s) (V s) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
    fun s hs => isOrthProj_tangentProj (hUV s hs).1 (hUV s hs).2.1
  have hLip : ∀ s ∈ Icc a b, ∀ B : Matrix m n ℝ,
      ‖tangentProj (U s) (V s) B - tangentProjAt (X s) B‖ ≤ 2 * ρ⁻¹ * ‖Y s - X s‖ * ‖B‖ :=
    fun s hs B => by
      obtain ⟨hU, hV, hYs⟩ := hUV s hs
      rw [hYs]
      exact norm_tangentProj_sub_tangentProjAt_le (hXr s hs) hρ (hσ s hs) hU hV (S s) B
  have h₁ : ∀ s ∈ Ico a t0, ‖tangentProj (U s) (V s) (F s (X s) - X' s)‖ ≤
      2 * μ / ρ * ‖Y s - X s‖ + (L + κ) * ηc s := fun s hs => by
    have hsb := hIco s hs
    have hsI := Ico_subset_Icc_self hsb
    obtain ⟨-, -, hbest⟩ := hb s hsb
    have hsplit : F s (X s) - X' s = (F s (X s) - F s (A s)) +
        (F s (A s) - tangentProjAt (X s) (F s (A s))) -
        (X' s - tangentProjAt (X s) (F s (A s))) := by abel
    have e1 : ‖tangentProj (U s) (V s) (F s (X s) - F s (A s))‖ ≤ L * ηc s :=
      ((hP s hsI).norm_le _).trans ((hF s _ _).trans (le_of_eq (by rw [hηeq s hsI])))
    have e2 : ‖tangentProj (U s) (V s) (F s (A s) - tangentProjAt (X s) (F s (A s)))‖ ≤
        2 * μ / ρ * ‖Y s - X s‖ := by
      have hQ0 : tangentProjAt (X s) (F s (A s) - tangentProjAt (X s) (F s (A s))) = 0 := by
        rw [map_sub, (isOrthProj_tangentProjAt _).idem, sub_self]
      have e : tangentProj (U s) (V s) (F s (A s) - tangentProjAt (X s) (F s (A s))) =
          tangentProj (U s) (V s) (F s (A s) - tangentProjAt (X s) (F s (A s))) -
            tangentProjAt (X s) (F s (A s) - tangentProjAt (X s) (F s (A s))) := by
        rw [hQ0, sub_zero]
      rw [e]
      refine (hLip s hsI _).trans ?_
      have hn : ‖F s (A s) - tangentProjAt (X s) (F s (A s))‖ ≤ μ := by
        have := (isOrthProj_tangentProjAt (X s)).compl.norm_le (F s (A s))
        simp only [sub_apply, one_apply_eq_self] at this
        exact this.trans (hμ s hsb)
      have := norm_nonneg (Y s - X s)
      calc 2 * ρ⁻¹ * ‖Y s - X s‖ * ‖F s (A s) - tangentProjAt (X s) (F s (A s))‖ ≤
          2 * ρ⁻¹ * ‖Y s - X s‖ * μ := by gcongr
        _ = 2 * μ / ρ * ‖Y s - X s‖ := by rw [div_eq_mul_inv]; ring
    have e3 : ‖tangentProj (U s) (V s) (X' s - tangentProjAt (X s) (F s (A s)))‖ ≤ κ * ηc s :=
      ((hP s hsI).norm_le _).trans (by rw [hηeq s hsI, norm_sub_rev (X s)]; exact hbest)
    rw [hsplit, map_sub, map_add]
    calc _ ≤ ‖tangentProj (U s) (V s) (F s (X s) - F s (A s))‖ +
          ‖tangentProj (U s) (V s) (F s (A s) - tangentProjAt (X s) (F s (A s)))‖ +
          ‖tangentProj (U s) (V s) (X' s - tangentProjAt (X s) (F s (A s)))‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ L * ηc s + 2 * μ / ρ * ‖Y s - X s‖ + κ * ηc s := add_le_add (add_le_add e1 e2) e3
      _ = _ := by ring
  have h₂ : ∀ s ∈ Ico a t0, ‖(1 - tangentProj (U s) (V s)) (X' s)‖ ≤
      κ * ‖Y s - X s‖ + (fun _ : ℝ => (0 : ℝ)) s := fun s hs => by
    have hsb := hIco s hs
    have hsI := Ico_subset_Icc_self hsb
    obtain ⟨htan, hX's, -⟩ := hb s hsb
    have e : (1 - tangentProj (U s) (V s)) (X' s) =
        -(tangentProj (U s) (V s) (X' s) - tangentProjAt (X s) (X' s)) := by
      rw [sub_apply, one_apply_eq_self, htan]
      abel
    rw [e, norm_neg, add_zero]
    refine (hLip s hsI _).trans ?_
    have := norm_nonneg (Y s - X s)
    calc 2 * ρ⁻¹ * ‖Y s - X s‖ * ‖X' s‖ ≤ 2 * ρ⁻¹ * ‖Y s - X s‖ * (μ / (1 - 2 * θ)) := by
          gcongr
      _ = κ * ‖Y s - X s‖ := by
          rw [hκ]
          simp only [div_eq_mul_inv, mul_inv]
          ring
  have hYsol : ODESolution (fun t x => tangentProj (U t) (V t) (F t x)) Y a t0 :=
    ⟨hY.cont.mono hIcc, fun s hs => hY.deriv s (hIco s hs)⟩
  have hcmp := ODESolution.dlra_norm_sub_le_of_comparison_integral
    (P := fun t => tangentProj (U t) (V t)) (F := F) (Y := Y) (a := a) (b := t0) (L := L)
    (κ₁ := 2 * μ / ρ) (κ₂ := κ) (δ := δ)
    (η₁ := fun s => (L + κ) * ηc s) (η₂ := fun _ => 0)
    (continuous_const.mul hηc) continuous_const hF hYsol
    (fun s hs => hP s (hIcc (Ico_subset_Icc_self hs))) (hXc.mono hIcc)
    (fun s hs => hX s (hIco s hs)) h₁ h₂ hδ t0 ⟨ht0.1, le_rfl⟩
  have hK : 0 ≤ L + 2 * μ / ρ + κ := by linarith
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

/-- **Quasi-optimality for a DLRA solution of rank `r`, margin `θ ρ`.** The bound of
`dlra_norm_sub_le_integral_of_margin` for a DLRA solution `Y` of rank `r` of
`Ẏ = P(Y) F(t, Y)` (`IsDLRASolution`): with `κ = 2 μ / ((1 - 2 θ) ρ)`,
`‖Y t - X t‖ ≤ e^{(L + 2 μ/ρ + κ)(t - a)} (δ + (L + κ) ∫ₐᵗ ‖X s - A s‖ ds)`. -/
theorem IsDLRASolution.norm_sub_le_integral_of_margin {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ θ δ : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hA : ODESolution F A a b) (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ)
    (hXc : ContinuousOn X (Icc a b)) (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0) (hθ : 2 * θ < 1)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ θ * ρ) (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + 2 * μ / ρ + 2 * μ / ((1 - 2 * θ) * ρ)) * (t - a)) *
        (δ + (L + 2 * μ / ((1 - 2 * θ) * ρ)) * ∫ s in a..t, ‖X s - A s‖) := by
  have hfac : ∀ t ∈ Icc a b, ∃ (U : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ)
      (V : Matrix n (Fin r) ℝ), Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ IsUnit S.det ∧ Y t = U * S * Vᵀ :=
    fun t ht => (SVD.rank_eq_iff_exists_factor (Y t)).1 (hY.2 t ht)
  choose! U S V hU hV hS hYeq using hfac
  have hY' : ODESolution (fun t x => tangentProj (U t) (V t) (F t x)) Y a b :=
    ⟨hY.1.cont, fun t ht => have ht' := Ico_subset_Icc_self ht
      DynamicallyOrthogonal.IsDLRASolution.hasDerivWithinAt_tangentProj hY ht (hU t ht')
        (hV t ht') (hS t ht') (hYeq t ht')⟩
  exact dlra_norm_sub_le_integral_of_margin hρ hL hF hA hμ hXc hX hXr hσ hopt hθ hd
    (fun t ht => ⟨hU t ht, hV t ht, hYeq t ht⟩) hY' hδ

/-! ### The margin `ρ / 4` -/

/-- With `θ = 1 / 4` the constant `2 μ / ((1 - 2 θ) ρ)` is `4 μ / ρ`. -/
private theorem two_mul_div_quarter (μ ρ : ℝ) (hρ : 0 < ρ) :
    2 * μ / ((1 - 2 * (1 / 4 : ℝ)) * ρ) = 4 * μ / ρ := by
  rw [div_eq_div_iff (by norm_num; exact hρ.ne') hρ.ne']
  ring

/-- `dlra_norm_sub_le_integral`, restated verbatim, is the case `θ = 1 / 4` of
`dlra_norm_sub_le_integral_of_margin`. -/
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
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) * (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖) := by
  have key := dlra_norm_sub_le_integral_of_margin (θ := 1 / 4) hρ hL hF hA hμ hXc hX hXr hσ hopt
    (by norm_num) (fun t ht => (hd t ht).trans_eq (by ring)) hUV hY hδ
  have e : L + 2 * μ / ρ + 4 * μ / ρ = L + 6 * μ / ρ := by ring
  rwa [two_mul_div_quarter μ ρ hρ, e] at key

/-- `IsDLRASolution.norm_sub_le_integral`, restated verbatim, is the case `θ = 1 / 4` of
`IsDLRASolution.norm_sub_le_integral_of_margin`. -/
example {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ δ : ℝ} (hY : IsDLRASolution r F Y a b)
    (hρ : 0 < ρ) (hL : 0 ≤ L) (hF : IsLipschitzField F L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ ρ / 4) (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + 6 * μ / ρ) * (t - a)) * (δ + (L + 4 * μ / ρ) * ∫ s in a..t, ‖X s - A s‖) := by
  have key := hY.norm_sub_le_integral_of_margin (θ := 1 / 4) hρ hL hF hA hμ hXc hX hXr hσ hopt
    (by norm_num) (fun t ht => (hd t ht).trans_eq (by ring)) hδ
  have e : L + 2 * μ / ρ + 4 * μ / ρ = L + 6 * μ / ρ := by ring
  rwa [two_mul_div_quarter μ ρ hρ, e] at key

end QuasiOptimal

namespace QuasiOptimalityExamples

open scoped LeanDLRA.Frobenius

/-- **Non-vacuity of `IsDLRASolution.norm_sub_le_integral_of_margin`** with the margin
`θ = 1 / 8`: for `X t = Y t = A t = (1 + t) e₁ e₁ᵀ` on `[0, 1]`, `F(t, Y) = e₁ e₁ᵀ` (`L = 0`),
`r = 1`, `ρ = μ = 1` and `δ = 0` the hypotheses hold; the constants of the bound are
`L + 2 μ / ρ + κ = 14 / 3` and `L + κ = 8 / 3` (`κ = 2 μ / ((1 - 2 θ) ρ) = 8 / 3`), below the
`6` and `4` of the margin `ρ / 4`. -/
example : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(1 + t) • (e₁ * e₁ᵀ) - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
      Real.exp ((0 + 2 * 1 / 1 + 2 * 1 / ((1 - 2 * (1 / 8)) * 1)) * (t - 0)) *
        (0 + (0 + 2 * 1 / ((1 - 2 * (1 / 8)) * 1)) *
          ∫ s in (0 : ℝ)..t, ‖(1 + s) • (e₁ * e₁ᵀ) - (1 + s) • (e₁ * e₁ᵀ)‖) := by
  have hc : ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 + t) ≠ 0 := fun t ht => ne_of_gt (by linarith [ht.1])
  have hXc : ContinuousOn (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) (Set.Icc 0 1) :=
    fun s _ => (hasDerivAt_smul_e₁ 1 s).continuousAt.continuousWithinAt
  have hsol : ODESolution (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ)
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) 0 1 :=
    ⟨hXc, fun s _ => (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt⟩
  have hYd : IsDLRASolution 1 (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ)
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) 0 1 := by
    refine ⟨⟨hXc, fun s hs => ?_⟩, fun t ht => rank_smul_e₁ (hc t ht)⟩
    have h := (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt (s := Ici s)
    convert h using 1
    exact tangentProjAt_smul_e₁_apply (hc s (Ico_subset_Icc_self hs))
  exact hYd.norm_sub_le_integral_of_margin (A := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ))
    (X := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) (X' := fun _ => e₁ * e₁ᵀ) (θ := 1 / 8) one_pos
    le_rfl (fun _ _ _ => by simp) hsol (fun _ _ => norm_e₁_mul_le) hXc
    (fun s _ => (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt) (fun t ht => rank_smul_e₁ (hc t ht))
    (fun t ht => one_le_singularValues_smul_e₁ (by linarith [ht.1]))
    (fun t _ => by simp) (by norm_num) (fun t _ => by simp) (by simp)

end QuasiOptimalityExamples

end LeanDLRA
