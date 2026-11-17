import LeanDLRA.DLRA.QuasiOptimalityTruncation
import LeanDLRA.FixedRank.TangentSpace.ProjectorSpectral

/-!
# Quasi-optimality of matrix DLRA with the spectral norm of the tail

The quasi-optimality bound of `LeanDLRA/DLRA/QuasiOptimalityNormal.lean` along a curve `X` of
critical points of `Z ↦ ‖Z - A t‖` on the matrices of rank `r` uses the Frobenius norm of the tail
`A - X` in two places: in the margin `‖X - A‖ ≤ θ ρ`, `θ < 1`, and in the integrand. Both come from
the differentiated first-order condition `‖P(X) (Ȧ - Ẋ)‖ ≤ ρ⁻¹ ‖Ẋ‖ ‖A - X‖`. This file shows this
step with the spectral norm of the tail,

  `‖P(X) (Ȧ - Ẋ)‖ ≤ ρ⁻¹ ‖Ẋ‖ ‖A - X‖₂`,   `‖Ẋ‖ ≤ μ / (1 - θ)`   if `‖X - A‖₂ ≤ θ ρ`, `θ < 1`,

(`‖P(X) (Ȧ - Ẋ)‖`, `‖Ẋ‖` and `μ ≥ ‖Ȧ‖` in the Frobenius norm) and, with `κ = μ / ((1 - θ) ρ)`,

  `‖Y t - X t‖ ≤ e^{(L + μ/ρ)(t - a)} (δ + L ∫ₐᵗ ‖X s - A s‖ ds + κ ∫ₐᵗ ‖X s - A s‖₂ ds)`.

For the truncated SVD `X t = T_r(A t)` the tail is `‖X t - A t‖₂ = σ_r(A t)` (the singular value
after the `r` largest ones; indices start at `0`), so the margin is a condition on the gap,
`σ_r(A t) ≤ θ ρ` with `ρ ≤ σ_{r-1}(A t)`, and

  `‖Y t - X t‖ ≤ κ e^{(μ/ρ) t} ∫₀ᵗ σ_r(A s) ds`.

## Main results

* `norm_tangentProjAt_sub_le_inv_mul_specNorm_of_hasDerivWithinAt`: the differentiated
  first-order condition with the spectral norm of the tail.
* `norm_le_div_one_sub_of_specNorm_sub_le`, `norm_sub_tangentProjAt_le_div_one_sub_mul_specNorm`:
  `‖X'‖ ≤ μ / (1 - θ)` and `‖X' - P(X) A'‖ ≤ μ / ((1 - θ) ρ) ‖A - X‖₂` under `‖X - A‖₂ ≤ θ ρ`.
* `dlra_norm_sub_le_integral_of_specNorm_sub_le`,
  `IsDLRASolution.norm_sub_le_integral_of_specNorm_sub_le`: the quasi-optimality bound.
* `dlra_norm_sub_truncation_le_integral_of_specNorm_sub_le`,
  `dlra_norm_sub_truncation_le_integral_of_singularValues_le`: the bound against the truncated
  SVD, in terms of `‖X - A‖₂` and of `σ_r(A)`.

## Implementation notes

The derivative bound is not the limit of a bound `‖P(X) N‖ ≤ ρ⁻¹ ‖Y - X‖ ‖N‖₂` between two points:
that bound needs the constant `√2`. It follows from
`norm_tangentProjAt_apply_le_one_add_mul_specNorm_of_tangentProjAt_eq_zero`, whose constant
`1 + ρ⁻¹ ‖Y - X‖` tends to `1`, and the continuity of the spectral norm.

The quasi-optimality bound is Grönwall's inequality for `Y - X` with the splitting

  `P(Y) F(Y) - Ẋ = P(Y) (F(Y) - F(A)) + (P(Y) - P(X)) F(A) + (P(X) F(A) - Ẋ)`

of [FepponLermusiaux2018, Theorem 32]: the three terms are at most `L ‖Y - A‖`,
`(μ/ρ) ‖Y - X‖` (Lipschitz constant `1` of the tangent projector) and `κ ‖A - X‖₂`. The exponent
is therefore `L + μ/ρ`, without the term `κ` of `dlra_norm_sub_le_integral_of_margin_lt_one`, and
`μ` bounds the field in the Frobenius norm; the Lipschitz term keeps the Frobenius norm of the
tail. Since `‖·‖₂ ≤ ‖·‖`, the bounds of `LeanDLRA/DLRA/QuasiOptimalityNormal.lean` follow; two of
them are restated verbatim as `example`s. The constants `ρ`, `μ`, `θ` are uniform on the interval;
[FepponLermusiaux2018, Theorem 32] has pointwise constants, the Frobenius norm of the tail and the
constant `2` in the exponent, and its Lemma 41 is the velocity bound below for the truncated SVD.
The differentiated first-order condition with `‖A - X‖₂` is the bound `σ_r(A)/σ_{r-1}(A)` of the
principal curvatures of the manifold in the normal direction `A - X`
[FepponLermusiaux2018, Theorem 24], and the speed bound `‖Ẋ‖ ≤ μ / (1 - σ_r/σ_{r-1})` is the
first-order perturbation bound of the truncated SVD [FepponLermusiaux2018, Theorem 25],
[CarrelGanderVandereycken2023, Theorem 3.8]. The `example`s show the hypotheses for curves with
`A ≠ X`, and the bounds of `LeanDLRA/FixedRank/TangentSpace/ProjectorSpectral.lean` for `Y ≠ X`.

## References

* [FepponLermusiaux2018]
* [CarrelGanderVandereycken2023]
-/

open Set Finset Matrix Filter
open scoped Topology

namespace LeanDLRA

section Spectral

open scoped LeanDLRA.Frobenius
open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Differentiated first-order optimality, spectral norm of the tail.** Under the hypotheses of
`norm_tangentProjAt_sub_le_inv_mul_of_hasDerivWithinAt` (derivatives `A'`, `X'` at `t ∈ s` within
`s`, `X u` of rank `r` with `P(X u) (A u - X u) = 0` on `s`, `0 < ρ ≤ σ_{r-1}(X t)`):
`‖P(X t) (A' - X')‖ ≤ ρ⁻¹ ‖X'‖ ‖A t - X t‖₂`. -/
theorem norm_tangentProjAt_sub_le_inv_mul_specNorm_of_hasDerivWithinAt {r : ℕ}
    {A X : ℝ → Matrix m n ℝ} {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ : ℝ}
    (hA : HasDerivWithinAt A A' s t) (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s)
    (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ) (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ : ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) :
    ‖tangentProjAt (X t) (A' - X')‖ ≤ ρ⁻¹ * ‖X'‖ * Curvature.specNorm (A t - X t) := by
  have hφ : HasDerivWithinAt (fun u => tangentProjAt (X t) (A u - X u - (A t - X t)))
      (tangentProjAt (X t) (A' - X')) s t :=
    (tangentProjAt (X t)).hasFDerivAt.comp_hasDerivWithinAt t ((hA.sub hX).sub_const _)
  have hb : ∀ u ∈ s, ‖tangentProjAt (X t) (A u - X u - (A t - X t))‖ ≤
      ‖X u - X t‖ * (ρ⁻¹ * (1 + ρ⁻¹ * ‖X u - X t‖) * Curvature.specNorm (A u - X u)) :=
    fun u hu => by
      have h := norm_tangentProjAt_apply_le_one_add_mul_specNorm_of_tangentProjAt_eq_zero
        (hrank t ht) (hrank u hu) hρ hσ (hopt u hu)
      rw [map_sub (tangentProjAt (X t)), hopt t ht, sub_zero]
      calc _ ≤ _ := h
        _ = _ := by ring
  have hg : ContinuousWithinAt
      (fun u => ρ⁻¹ * (1 + ρ⁻¹ * ‖X u - X t‖) * Curvature.specNorm (A u - X u)) s t :=
    (continuousWithinAt_const.mul (continuousWithinAt_const.add (continuousWithinAt_const.mul
      (hX.continuousWithinAt.sub continuousWithinAt_const).norm))).mul
      (Curvature.continuous_specNorm.continuousAt.comp_continuousWithinAt
        (hA.continuousWithinAt.sub hX.continuousWithinAt))
  have h := norm_deriv_le_of_norm_le_norm_sub_mul hφ hX hs (by simp) hg hb
  calc _ ≤ _ := h
    _ = _ := by
      simp only [sub_self, norm_zero, mul_zero, add_zero, mul_one]
      ring

/-- The two derivative bounds under the margin `‖X - A‖₂ ≤ θ ρ`, `θ < 1`. -/
private theorem deriv_bounds_of_specNorm_sub_le {r : ℕ} {A X : ℝ → Matrix m n ℝ}
    {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ μ θ : ℝ} (hA : HasDerivWithinAt A A' s t)
    (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s) (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ)
    (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ : ∀ u ∈ s, ρ ≤ (toEuclideanLin (X u)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) (hμ : ‖A'‖ ≤ μ) (hθ : θ < 1)
    (hd : Curvature.specNorm (X t - A t) ≤ θ * ρ) :
    ‖X'‖ ≤ μ / (1 - θ) ∧
      ‖X' - tangentProjAt (X t) A'‖ ≤ μ / ((1 - θ) * ρ) * Curvature.specNorm (A t - X t) := by
  have htan : tangentProjAt (X t) X' = X' := tangentProjAt_eq_self_iff.mpr
    (mem_tangentSpaceAt_of_hasDerivWithinAt hX ht hs hρ hrank hσ)
  have hdef := norm_tangentProjAt_sub_le_inv_mul_specNorm_of_hasDerivWithinAt hA hX ht hs hρ
    hrank (hσ t ht) hopt
  have hE : ρ⁻¹ * Curvature.specNorm (A t - X t) ≤ θ := by
    rw [inv_mul_le_iff₀ hρ, Curvature.specNorm_sub_comm]
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
    have h4 : ρ⁻¹ * ‖X'‖ * Curvature.specNorm (A t - X t) ≤ θ * ‖X'‖ := by
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
  have hs0 := Curvature.specNorm_nonneg (A t - X t)
  calc ρ⁻¹ * ‖X'‖ * Curvature.specNorm (A t - X t) ≤
      ρ⁻¹ * (μ / (1 - θ)) * Curvature.specNorm (A t - X t) := by gcongr
    _ = μ / ((1 - θ) * ρ) * Curvature.specNorm (A t - X t) := by
      simp only [div_eq_mul_inv, mul_inv]
      ring

/-- **Speed of a curve of critical points under the margin `‖X - A‖₂ ≤ θ ρ`, `θ < 1`.** Under the
hypotheses of `norm_le_div_one_sub_of_tangentProjAt_sub_eq_zero`, with the spectral norm of
`X t - A t` in the margin: `‖X'‖ ≤ μ / (1 - θ)`. -/
theorem norm_le_div_one_sub_of_specNorm_sub_le {r : ℕ} {A X : ℝ → Matrix m n ℝ}
    {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ μ θ : ℝ} (hA : HasDerivWithinAt A A' s t)
    (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s) (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ)
    (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ : ∀ u ∈ s, ρ ≤ (toEuclideanLin (X u)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) (hμ : ‖A'‖ ≤ μ) (hθ : θ < 1)
    (hd : Curvature.specNorm (X t - A t) ≤ θ * ρ) : ‖X'‖ ≤ μ / (1 - θ) :=
  (deriv_bounds_of_specNorm_sub_le hA hX ht hs hρ hrank hσ hopt hμ hθ hd).1

/-- **The velocity of a curve of critical points under the margin `‖X - A‖₂ ≤ θ ρ`, `θ < 1`.**
Under the hypotheses of `norm_le_div_one_sub_of_specNorm_sub_le`:
`‖X' - P(X t) A'‖ ≤ μ / ((1 - θ) ρ) ‖A t - X t‖₂`. -/
theorem norm_sub_tangentProjAt_le_div_one_sub_mul_specNorm {r : ℕ}
    {A X : ℝ → Matrix m n ℝ} {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ μ θ : ℝ}
    (hA : HasDerivWithinAt A A' s t) (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s)
    (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ) (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ : ∀ u ∈ s, ρ ≤ (toEuclideanLin (X u)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) (hμ : ‖A'‖ ≤ μ) (hθ : θ < 1)
    (hd : Curvature.specNorm (X t - A t) ≤ θ * ρ) :
    ‖X' - tangentProjAt (X t) A'‖ ≤ μ / ((1 - θ) * ρ) * Curvature.specNorm (A t - X t) :=
  (deriv_bounds_of_specNorm_sub_le hA hX ht hs hρ hrank hσ hopt hμ hθ hd).2

/-- The derivative bounds at a time `t ∈ [a, b)` from right derivatives on `[t, b]`, under the
margin `‖X - A‖₂ ≤ θ ρ`, `θ < 1`, together with the tangency of `X' t`. -/
private theorem deriv_bounds_on_Ico_of_specNorm_sub_le {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' : ℝ → Matrix m n ℝ} {a b μ ρ θ : ℝ}
    (hρ : 0 < ρ) (hA : ODESolution F A a b) (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ)
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc a b, Curvature.specNorm (X t - A t) ≤ θ * ρ) {t : ℝ} (ht : t ∈ Ico a b) :
    tangentProjAt (X t) (X' t) = X' t ∧ ‖X' t‖ ≤ μ / (1 - θ) ∧
      ‖X' t - tangentProjAt (X t) (F t (A t))‖ ≤
        μ / ((1 - θ) * ρ) * Curvature.specNorm (A t - X t) := by
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
    deriv_bounds_of_specNorm_sub_le hA' hX' hts hs hρ hrank hσ' hopt' (hμ t ht) hθ
      (hd t (Ico_subset_Icc_self ht))⟩

/-- **Quasi-optimality of matrix DLRA along a curve of critical points, spectral norm of the
tail.** Under the hypotheses of `dlra_norm_sub_le_integral_of_margin_lt_one`, with the margin
`‖X t - A t‖₂ ≤ θ ρ`, `θ < 1`, in the spectral norm, and with `κ = μ / ((1 - θ) ρ)`, for
`t ∈ [a, b]`

  `‖Y t - X t‖ ≤ e^{(L + μ/ρ)(t - a)} (δ + L ∫ₐᵗ ‖X s - A s‖ ds + κ ∫ₐᵗ ‖X s - A s‖₂ ds)`.

The Lipschitz term keeps the Frobenius norm of the tail. The exponent `L + μ/ρ` comes from the
splitting `P(Y) F(Y) - Ẋ = P(Y) (F(Y) - F(A)) + (P(Y) - P(X)) F(A) + (P(X) F(A) - Ẋ)` and the
Lipschitz constant `1` of the tangent projector. -/
theorem dlra_norm_sub_le_integral_of_specNorm_sub_le {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ θ δ : ℝ}
    (hρ : 0 < ρ) (hL : 0 ≤ L) (hF : IsLipschitzField F L) (hA : ODESolution F A a b)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc a b, Curvature.specNorm (X t - A t) ≤ θ * ρ)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t x => tangentProj (U t) (V t) (F t x)) Y a b)
    (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + μ / ρ) * (t - a)) *
        (δ + L * (∫ s in a..t, ‖X s - A s‖) +
          μ / ((1 - θ) * ρ) * ∫ s in a..t, Curvature.specNorm (X s - A s)) := by
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
  obtain ⟨ηs, hηs, hηseq⟩ : ∃ η : ℝ → ℝ, Continuous η ∧
      ∀ s ∈ Icc a b, η s = Curvature.specNorm (X s - A s) :=
    ⟨fun s => Curvature.specNorm (X (projIcc a b hab.le s) - A (projIcc a b hab.le s)),
      (Curvature.continuous_specNorm.comp_continuousOn (hXc.sub hA.cont)).comp_continuous
        (continuous_subtype_val.comp continuous_projIcc) fun s => (projIcc a b hab.le s).2,
      fun s hs => by simp only [projIcc_of_mem _ hs]⟩
  have hP : ∀ s ∈ Icc a b,
      IsOrthProj (tangentProj (U s) (V s) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
    fun s hs => isOrthProj_tangentProj (hUV s hs).1 (hUV s hs).2.1
  have hρ' : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ.le
  have hbound : ∀ s ∈ Ico a t0, ‖tangentProj (U s) (V s) (F s (Y s)) - X' s‖ ≤
      (L + μ / ρ) * ‖Y s - X s‖ + (L * ηc s + κ * ηs s) := fun s hs => by
    have hsb := hIco s hs
    have hsI := Ico_subset_Icc_self hsb
    obtain ⟨-, -, hbest⟩ :=
      deriv_bounds_on_Ico_of_specNorm_sub_le hρ hA hμ hX hXr hσ hopt hθ hd hsb
    obtain ⟨hU, hV, hYs⟩ := hUV s hsI
    have hsplit : tangentProj (U s) (V s) (F s (Y s)) - X' s =
        tangentProj (U s) (V s) (F s (Y s) - F s (A s)) +
        (tangentProj (U s) (V s) (F s (A s)) - tangentProjAt (X s) (F s (A s))) -
        (X' s - tangentProjAt (X s) (F s (A s))) := by
      rw [map_sub]
      abel
    have e1 : ‖tangentProj (U s) (V s) (F s (Y s) - F s (A s))‖ ≤
        L * ‖Y s - X s‖ + L * ηc s := by
      refine ((hP s hsI).norm_le _).trans ((hF s _ _).trans ?_)
      rw [hηeq s hsI, ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hL
      calc ‖Y s - A s‖ = ‖(Y s - X s) + (X s - A s)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖Y s - X s‖ + ‖X s - A s‖ := norm_add_le _ _
    have e2 : ‖tangentProj (U s) (V s) (F s (A s)) - tangentProjAt (X s) (F s (A s))‖ ≤
        μ / ρ * ‖Y s - X s‖ := by
      have h := norm_tangentProj_sub_tangentProjAt_le_inv_mul (hXr s hsI) hρ (hσ s hsI) hU hV
        (S s) (F s (A s))
      rw [← hYs] at h
      refine h.trans ?_
      calc ρ⁻¹ * ‖Y s - X s‖ * ‖F s (A s)‖ ≤ ρ⁻¹ * ‖Y s - X s‖ * μ :=
            mul_le_mul_of_nonneg_left (hμ s hsb) (mul_nonneg hρ' (norm_nonneg _))
        _ = μ / ρ * ‖Y s - X s‖ := by rw [div_eq_mul_inv]; ring
    have e3 : ‖X' s - tangentProjAt (X s) (F s (A s))‖ ≤ κ * ηs s := by
      rw [hηseq s hsI, Curvature.specNorm_sub_comm (X s), hκ]
      exact hbest
    rw [hsplit]
    calc _ ≤ ‖tangentProj (U s) (V s) (F s (Y s) - F s (A s))‖ +
          ‖tangentProj (U s) (V s) (F s (A s)) - tangentProjAt (X s) (F s (A s))‖ +
          ‖X' s - tangentProjAt (X s) (F s (A s))‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ L * ‖Y s - X s‖ + L * ηc s + μ / ρ * ‖Y s - X s‖ + κ * ηs s :=
          add_le_add (add_le_add e1 e2) e3
      _ = _ := by ring
  have hη₁ : Continuous fun s => L * ηc s + κ * ηs s :=
    (continuous_const.mul hηc).add (continuous_const.mul hηs)
  have hcmp := norm_le_gronwallIntegralBound (f := fun t => Y t - X t)
    (f' := fun t => tangentProj (U t) (V t) (F t (Y t)) - X' t) (δ := δ) (K := L + μ / ρ) hη₁
    ((hY.cont.sub hXc).mono hIcc)
    (fun s hs => (hY.deriv s (hIco s hs)).sub (hX s (hIco s hs))) hδ hbound t0 ⟨ht0.1, le_rfl⟩
  have hK : 0 ≤ L + μ / ρ := by linarith
  have hgb := gronwallIntegralBound_le (δ := δ) hη₁ hK ht0.1 (fun s hs => by
      have h1 : 0 ≤ ηc s := by rw [hηeq s (hIcc hs)]; exact norm_nonneg _
      have h2 : 0 ≤ ηs s := by rw [hηseq s (hIcc hs)]; exact Curvature.specNorm_nonneg _
      exact add_nonneg (mul_nonneg hL h1) (mul_nonneg hκ0 h2))
  have hJ : ∫ s in a..t0, (L * ηc s + κ * ηs s) =
      L * (∫ s in a..t0, ‖X s - A s‖) +
        κ * ∫ s in a..t0, Curvature.specNorm (X s - A s) := by
    have hi1 : IntervalIntegrable (fun s => L * ηc s) MeasureTheory.volume a t0 :=
      (continuous_const.mul hηc).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun s => κ * ηs s) MeasureTheory.volume a t0 :=
      (continuous_const.mul hηs).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    congr 2
    · refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le ht0.1] at hs
      exact hηeq s (hIcc hs)
    · refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le ht0.1] at hs
      exact hηseq s (hIcc hs)
  refine hcmp.trans (hgb.trans (le_of_eq ?_))
  rw [hJ]
  ring

/-- **Quasi-optimality for a DLRA solution of rank `r`, spectral norm of the tail.** The bound of
`dlra_norm_sub_le_integral_of_specNorm_sub_le` for a DLRA solution `Y` of rank `r` of
`Ẏ = P(Y) F(t, Y)` (`IsDLRASolution`): with `κ = μ / ((1 - θ) ρ)`,
`‖Y t - X t‖ ≤ e^{(L + μ/ρ)(t - a)} (δ + L ∫ₐᵗ ‖X s - A s‖ ds + κ ∫ₐᵗ ‖X s - A s‖₂ ds)`. -/
theorem IsDLRASolution.norm_sub_le_integral_of_specNorm_sub_le {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ θ δ : ℝ}
    (hY : IsDLRASolution r F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hA : ODESolution F A a b) (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ)
    (hXc : ContinuousOn X (Icc a b)) (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc a b, Curvature.specNorm (X t - A t) ≤ θ * ρ) (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp ((L + μ / ρ) * (t - a)) *
        (δ + L * (∫ s in a..t, ‖X s - A s‖) +
          μ / ((1 - θ) * ρ) * ∫ s in a..t, Curvature.specNorm (X s - A s)) := by
  have hfac : ∀ t ∈ Icc a b, ∃ (U : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ)
      (V : Matrix n (Fin r) ℝ), Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ IsUnit S.det ∧ Y t = U * S * Vᵀ :=
    fun t ht => (SVD.rank_eq_iff_exists_factor (Y t)).1 (hY.2 t ht)
  choose! U S V hU hV hS hYeq using hfac
  have hY' : ODESolution (fun t x => tangentProj (U t) (V t) (F t x)) Y a b :=
    ⟨hY.1.cont, fun t ht => have ht' := Ico_subset_Icc_self ht
      DynamicallyOrthogonal.IsDLRASolution.hasDerivWithinAt_tangentProj hY ht (hU t ht')
        (hV t ht') (hS t ht') (hYeq t ht')⟩
  exact dlra_norm_sub_le_integral_of_specNorm_sub_le hρ hL hF hA hμ hXc hX hXr hσ hopt hθ hd
    (fun t ht => ⟨hU t ht, hV t ht, hYeq t ht⟩) hY' hδ

/-- **Quasi-optimality of matrix DLRA against the truncated SVD, spectral norm of the tail.**
Let `X t = T_r(A t)` be differentiable with `ρ ≤ σ_{r-1}(A t)`, `‖X t - A t‖₂ ≤ θ ρ` for a
`θ < 1`, and `‖Ȧ‖ ≤ μ` (Frobenius norm), and let `Y = U S Vᵀ` solve the DLRA equation
`Ẏ = P(Y) Ȧ` with `Y 0 = X 0`. Then, with `κ = μ / ((1 - θ) ρ)`, for every `t ∈ [0, T]`

  `‖Y t - X t‖ ≤ κ e^{(μ/ρ) t} ∫₀ᵗ ‖X s - A s‖₂ ds`.

These are the hypotheses of `dlra_norm_sub_truncation_le_integral_of_margin_lt_one` with the
spectral norm in the margin. -/
theorem dlra_norm_sub_truncation_le_integral_of_specNorm_sub_le {r : ℕ} (hr : 0 < r)
    {A A' X X' Y : ℝ → Matrix m n ℝ} {T μ ρ θ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ t ∈ Icc 0 T, HasDerivAt A (A' t) t)
    (hμ : ∀ t ∈ Icc 0 T, ‖A' t‖ ≤ μ) (hXbest : ∀ t ∈ Icc 0 T, X t = truncation (A t) r)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (X' t) t)
    (hσ : ∀ t ∈ Icc 0 T, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1)) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc 0 T, Curvature.specNorm (X t - A t) ≤ θ * ρ)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc 0 T, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t _ => tangentProj (U t) (V t) (A' t)) Y 0 T) (hY₀ : Y 0 = X 0) :
    ∀ t ∈ Icc 0 T, ‖Y t - X t‖ ≤
      μ / ((1 - θ) * ρ) * Real.exp (μ / ρ * t) *
        ∫ s in (0 : ℝ)..t, Curvature.specNorm (X s - A s) := by
  intro t ht
  have hA' : ODESolution (fun t (_ : Matrix m n ℝ) => A' t) A 0 T :=
    ⟨fun s hs => (hA s hs).continuousAt.continuousWithinAt,
      fun s hs => (hA s (Ico_subset_Icc_self hs)).hasDerivWithinAt⟩
  have h := dlra_norm_sub_le_integral_of_specNorm_sub_le (F := fun t _ => A' t) (L := 0) (δ := 0)
    hρ le_rfl (fun t x y => by simp) hA' (fun s hs => hμ s (Ico_subset_Icc_self hs))
    (fun s hs => (hX s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hX s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (fun s hs => by
      rw [hXbest s hs]
      exact rank_truncation_of_le_singularValues hρ (hσ s hs))
    (fun s hs => by
      rw [hXbest s hs]
      exact le_singularValues_truncation hr hρ (hσ s hs))
    (fun s hs => by
      rw [hXbest s hs]
      exact tangentProjAt_truncation_sub_eq_zero _ _)
    hθ hd hUV hY (by rw [hY₀, sub_self, norm_zero]) t ht
  calc ‖Y t - X t‖ ≤ _ := h
    _ = _ := by
      simp only [zero_add, sub_zero, zero_mul]
      ring

/-- **Quasi-optimality of matrix DLRA against the truncated SVD under a gap condition.** Let
`X t = T_r(A t)` be differentiable with `ρ ≤ σ_{r-1}(A t)` and `σ_r(A t) ≤ θ ρ` for a `θ < 1`
(the `r` largest singular values are at least `ρ`, the next one is at most `θ ρ`), `‖Ȧ‖ ≤ μ`, and
let `Y = U S Vᵀ` solve `Ẏ = P(Y) Ȧ` with `Y 0 = X 0`. Then, with `κ = μ / ((1 - θ) ρ)`, for every
`t ∈ [0, T]`

  `‖Y t - X t‖ ≤ κ e^{(μ/ρ) t} ∫₀ᵗ σ_r(A s) ds`.

It is `dlra_norm_sub_truncation_le_integral_of_specNorm_sub_le` with `‖X t - A t‖₂ = σ_r(A t)`
(`EckartYoung.specNorm_sub_truncation`). -/
theorem dlra_norm_sub_truncation_le_integral_of_singularValues_le {r : ℕ} (hr : 0 < r)
    {A A' X X' Y : ℝ → Matrix m n ℝ} {T μ ρ θ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ t ∈ Icc 0 T, HasDerivAt A (A' t) t)
    (hμ : ∀ t ∈ Icc 0 T, ‖A' t‖ ≤ μ) (hXbest : ∀ t ∈ Icc 0 T, X t = truncation (A t) r)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (X' t) t)
    (hσ : ∀ t ∈ Icc 0 T, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1)) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc 0 T, (toEuclideanLin (A t)).singularValues r ≤ θ * ρ)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc 0 T, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t _ => tangentProj (U t) (V t) (A' t)) Y 0 T) (hY₀ : Y 0 = X 0) :
    ∀ t ∈ Icc 0 T, ‖Y t - X t‖ ≤
      μ / ((1 - θ) * ρ) * Real.exp (μ / ρ * t) *
        ∫ s in (0 : ℝ)..t, (toEuclideanLin (A s)).singularValues r := by
  have he : ∀ s ∈ Icc 0 T, Curvature.specNorm (X s - A s) =
      (toEuclideanLin (A s)).singularValues r := fun s hs => by
    rw [hXbest s hs, Curvature.specNorm_sub_comm, specNorm_sub_truncation]
  intro t ht
  have h := dlra_norm_sub_truncation_le_integral_of_specNorm_sub_le hr hρ hA hμ hXbest hX hσ hθ
    (fun s hs => (he s hs).le.trans (hd s hs)) hUV hY hY₀ t ht
  have hi : ∫ s in (0 : ℝ)..t, Curvature.specNorm (X s - A s) =
      ∫ s in (0 : ℝ)..t, (toEuclideanLin (A s)).singularValues r :=
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le ht.1] at hs
      exact he s ⟨hs.1, hs.2.trans ht.2⟩
  rwa [hi] at h

/-! ### The bounds with the Frobenius norm of the tail -/

/-- `norm_tangentProjAt_sub_le_inv_mul_of_hasDerivWithinAt`, restated verbatim, follows from
`norm_tangentProjAt_sub_le_inv_mul_specNorm_of_hasDerivWithinAt` and `‖·‖₂ ≤ ‖·‖`. -/
example {r : ℕ} {A X : ℝ → Matrix m n ℝ}
    {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ : ℝ} (hA : HasDerivWithinAt A A' s t)
    (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s) (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ)
    (hrank : ∀ u ∈ s, (X u).rank = r) (hσ : ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) :
    ‖tangentProjAt (X t) (A' - X')‖ ≤ ρ⁻¹ * ‖X'‖ * ‖A t - X t‖ :=
  (norm_tangentProjAt_sub_le_inv_mul_specNorm_of_hasDerivWithinAt hA hX ht hs hρ hrank hσ
    hopt).trans (mul_le_mul_of_nonneg_left (Curvature.specNorm_le_frob _)
      (mul_nonneg (inv_nonneg.2 hρ.le) (norm_nonneg _)))

/-- `dlra_norm_sub_le_integral_of_margin_lt_one`, restated verbatim, follows from
`dlra_norm_sub_le_integral_of_specNorm_sub_le`: the margin and the integrand in the Frobenius norm
dominate those in the spectral norm, and the exponent `L + μ/ρ + κ` dominates `L + μ/ρ`. -/
example {r : ℕ}
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
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0
    simpa using hδ
  have hab : a < b := hpos.trans_le ht.2
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ a ⟨le_rfl, hab⟩)
  have key := dlra_norm_sub_le_integral_of_specNorm_sub_le hρ hL hF hA hμ hXc hX hXr hσ hopt hθ
    (fun s hs => (Curvature.specNorm_le_frob _).trans (hd s hs)) hUV hY hδ t ht
  have hκ : 0 ≤ μ / ((1 - θ) * ρ) := div_nonneg hμ0 (mul_pos (by linarith) hρ).le
  have hsub : uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc_right ht.2
  have hc := (hXc.sub hA.cont).mono hsub
  have hI : ∫ s in a..t, Curvature.specNorm (X s - A s) ≤ ∫ s in a..t, ‖X s - A s‖ :=
    intervalIntegral.integral_mono_on ht.1
      (Curvature.continuous_specNorm.comp_continuousOn hc).intervalIntegrable
      hc.norm.intervalIntegrable (fun s _ => Curvature.specNorm_le_frob _)
  have hIF : 0 ≤ ∫ s in a..t, ‖X s - A s‖ :=
    intervalIntegral.integral_nonneg ht.1 fun _ _ => norm_nonneg _
  have h := mul_le_mul_of_nonneg_left hI hκ
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  refine key.trans (mul_le_mul
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) (by linarith [ht.1])))
    (by rw [add_mul]; linarith)
    (add_nonneg (add_nonneg hδ0 (mul_nonneg hL hIF))
      (mul_nonneg hκ (intervalIntegral.integral_nonneg ht.1
        fun _ _ => Curvature.specNorm_nonneg _))) (Real.exp_nonneg _))

end Spectral

/-! ### Examples -/

namespace QuasiOptimalitySpectralExamples

open scoped LeanDLRA.Frobenius
open QuasiOptimalityExamples

/-- The normal part `diag(0, 1/16)` of the examples. -/
local notation "N₁₆" => (!![0, 0; 0, 1 / 16] : Matrix (Fin 2) (Fin 2) ℝ)

private theorem hasDerivAt_smul_e₁_add_N₁₆ (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) (e₁ * e₁ᵀ) t := by
  simpa using (hasDerivAt_smul_e₁ 1 t).add_const N₁₆

/-- The hypotheses on `X t = (1 + t) e₁ e₁ᵀ` and `A t = X t + diag(0, 1/16)` for `t ≥ 0`, with
`r = 1`, `ρ = 1` and the margin `θ = 1/16` in the spectral norm. -/
private theorem hyps_N₁₆ {t : ℝ} (ht : 0 ≤ t) :
    ((1 + t) • (e₁ * e₁ᵀ)).rank = 1 ∧
    (1 : ℝ) ≤ (toEuclideanLin ((1 + t) • (e₁ * e₁ᵀ))).singularValues (1 - 1) ∧
    tangentProjAt ((1 + t) • (e₁ * e₁ᵀ)) ((1 + t) • (e₁ * e₁ᵀ) + N₁₆ - (1 + t) • (e₁ * e₁ᵀ)) = 0 ∧
    Curvature.specNorm ((1 + t) • (e₁ * e₁ᵀ) - ((1 + t) • (e₁ * e₁ᵀ) + N₁₆)) ≤ 1 / 16 * 1 := by
  have hc : (1 + t) ≠ 0 := ne_of_gt (by linarith)
  refine ⟨rank_smul_e₁ hc, one_le_singularValues_smul_e₁ (by linarith), ?_, ?_⟩
  · have h := tangentProjAt_truncation_sub_eq_zero ((1 + t) • (e₁ * e₁ᵀ) + N₁₆) 1
    rwa [truncation_smul_e₁_add ht] at h
  · exact (Curvature.specNorm_le_frob _).trans ((norm_smul_e₁_sub_add_le t).trans_eq (by norm_num))

/-- **Non-vacuity of the bounds of the tangent projector on a normal vector with the spectral
norm** (`norm_sq_tangentProjAt_apply_le_mul_specNorm_sq_of_tangentProjAt_eq_zero` and its two
linear forms): `X = e₁ e₁ᵀ`, `Y = 2 e₁ e₁ᵀ ≠ X` of rank `1`, `ρ = 1`, and `N = diag(0, 1/16) ≠ 0`,
which is normal at `Y`. -/
example :
    ‖tangentProjAt (((1 : ℝ) + 0) • (e₁ * e₁ᵀ))
        (((1 : ℝ) + 1) • (e₁ * e₁ᵀ) + N₁₆ - ((1 : ℝ) + 1) • (e₁ * e₁ᵀ))‖ ^ 2 ≤
      ((1 : ℝ)⁻¹ * ‖((1 : ℝ) + 1) • (e₁ * e₁ᵀ) - ((1 : ℝ) + 0) • (e₁ * e₁ᵀ)‖) ^ 2 *
        (1 + ((1 : ℝ)⁻¹ * ‖((1 : ℝ) + 1) • (e₁ * e₁ᵀ) - ((1 : ℝ) + 0) • (e₁ * e₁ᵀ)‖) ^ 2) *
        Curvature.specNorm
          (((1 : ℝ) + 1) • (e₁ * e₁ᵀ) + N₁₆ - ((1 : ℝ) + 1) • (e₁ * e₁ᵀ)) ^ 2 ∧
    ‖tangentProjAt (((1 : ℝ) + 0) • (e₁ * e₁ᵀ))
        (((1 : ℝ) + 1) • (e₁ * e₁ᵀ) + N₁₆ - ((1 : ℝ) + 1) • (e₁ * e₁ᵀ))‖ ≤
      (1 : ℝ)⁻¹ * ‖((1 : ℝ) + 1) • (e₁ * e₁ᵀ) - ((1 : ℝ) + 0) • (e₁ * e₁ᵀ)‖ *
        (1 + (1 : ℝ)⁻¹ * ‖((1 : ℝ) + 1) • (e₁ * e₁ᵀ) - ((1 : ℝ) + 0) • (e₁ * e₁ᵀ)‖) *
        Curvature.specNorm
          (((1 : ℝ) + 1) • (e₁ * e₁ᵀ) + N₁₆ - ((1 : ℝ) + 1) • (e₁ * e₁ᵀ)) ∧
    ‖tangentProjAt (((1 : ℝ) + 0) • (e₁ * e₁ᵀ))
        (((1 : ℝ) + 1) • (e₁ * e₁ᵀ) + N₁₆ - ((1 : ℝ) + 1) • (e₁ * e₁ᵀ))‖ ≤
      Real.sqrt 2 * (1 : ℝ)⁻¹ * ‖((1 : ℝ) + 1) • (e₁ * e₁ᵀ) - ((1 : ℝ) + 0) • (e₁ * e₁ᵀ)‖ *
        Curvature.specNorm
          (((1 : ℝ) + 1) • (e₁ * e₁ᵀ) + N₁₆ - ((1 : ℝ) + 1) • (e₁ * e₁ᵀ)) := by
  have h0 := hyps_N₁₆ (le_refl (0 : ℝ))
  have h1 := hyps_N₁₆ (zero_le_one : (0 : ℝ) ≤ 1)
  exact ⟨norm_sq_tangentProjAt_apply_le_mul_specNorm_sq_of_tangentProjAt_eq_zero h0.1 h1.1
      one_pos h0.2.1 h1.2.2.1,
    norm_tangentProjAt_apply_le_one_add_mul_specNorm_of_tangentProjAt_eq_zero h0.1 h1.1
      one_pos h0.2.1 h1.2.2.1,
    norm_tangentProjAt_apply_le_sqrt_two_mul_specNorm_of_tangentProjAt_eq_zero h0.1 h1.1
      one_pos h0.2.1 h1.2.2.1⟩

/-- `norm_tangentProjAt_sub_le_inv_mul_specNorm_of_hasDerivWithinAt`,
`norm_le_div_one_sub_of_specNorm_sub_le` and `norm_sub_tangentProjAt_le_div_one_sub_mul_specNorm`
for the curves `X t = (1 + t) e₁ e₁ᵀ` and `A t = X t + diag(0, 1/16) ≠ X t` (`r = 1`,
`ρ = μ = 1`) at `t = 0` within `[0, 1]`, with the margin `θ = 1/16`. -/
example :
    ‖tangentProjAt (((1 : ℝ) + 0) • (e₁ * e₁ᵀ)) (e₁ * e₁ᵀ - e₁ * e₁ᵀ)‖ ≤
      1⁻¹ * ‖e₁ * e₁ᵀ‖ *
        Curvature.specNorm (((1 : ℝ) + 0) • (e₁ * e₁ᵀ) + N₁₆ - ((1 : ℝ) + 0) • (e₁ * e₁ᵀ)) ∧
    ‖e₁ * e₁ᵀ‖ ≤ 1 / (1 - 1 / 16) ∧
    ‖e₁ * e₁ᵀ - tangentProjAt (((1 : ℝ) + 0) • (e₁ * e₁ᵀ)) (e₁ * e₁ᵀ)‖ ≤
      1 / ((1 - 1 / 16) * 1) *
        Curvature.specNorm (((1 : ℝ) + 0) • (e₁ * e₁ᵀ) + N₁₆ - ((1 : ℝ) + 0) • (e₁ * e₁ᵀ)) := by
  have hs : (𝓝[Set.Icc (0 : ℝ) 1 \ {0}] 0).NeBot := by
    rw [Icc_sdiff_left]
    exact left_nhdsWithin_Ioc_neBot one_pos
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hA := (hasDerivAt_smul_e₁_add_N₁₆ 0).hasDerivWithinAt (s := Set.Icc (0 : ℝ) 1)
  have hX := (hasDerivAt_smul_e₁ 1 0).hasDerivWithinAt (s := Set.Icc (0 : ℝ) 1)
  have hr : ∀ u ∈ Set.Icc (0 : ℝ) 1, ((fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) u).rank = 1 :=
    fun u hu => (hyps_N₁₆ hu.1).1
  have hσ : ∀ u ∈ Set.Icc (0 : ℝ) 1, (1 : ℝ) ≤
      (toEuclideanLin ((fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) u)).singularValues (1 - 1) :=
    fun u hu => (hyps_N₁₆ hu.1).2.1
  have ho : ∀ u ∈ Set.Icc (0 : ℝ) 1, tangentProjAt ((fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) u)
      ((fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) u - (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) u) = 0 :=
    fun u hu => (hyps_N₁₆ hu.1).2.2.1
  have hd := (hyps_N₁₆ (le_refl (0 : ℝ))).2.2.2
  have r1 := norm_tangentProjAt_sub_le_inv_mul_specNorm_of_hasDerivWithinAt hA hX h0 hs one_pos
    hr (hσ 0 h0) ho
  have r2 := norm_le_div_one_sub_of_specNorm_sub_le (θ := 1 / 16) hA hX h0 hs one_pos
    hr hσ ho norm_e₁_mul_le (by norm_num) hd
  have r3 := norm_sub_tangentProjAt_le_div_one_sub_mul_specNorm (θ := 1 / 16) hA
    hX h0 hs one_pos hr hσ ho norm_e₁_mul_le (by norm_num) hd
  exact ⟨r1, r2, r3⟩

/-- **Non-vacuity of `dlra_norm_sub_le_integral_of_specNorm_sub_le` and of
`IsDLRASolution.norm_sub_le_integral_of_specNorm_sub_le`**: for `X t = Y t = (1 + t) e₁ e₁ᵀ` and
`A t = X t + diag(0, 1/16) ≠ X t` on `[0, 1]`, `F(t, Y) = e₁ e₁ᵀ` (`L = 0`), `r = 1`,
`ρ = μ = 1`, `θ = 1/16` and `δ = 0` the hypotheses hold. -/
example : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(1 + t) • (e₁ * e₁ᵀ) - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
      Real.exp ((0 + 1 / 1) * (t - 0)) *
        (0 + 0 * (∫ s in (0 : ℝ)..t, ‖(1 + s) • (e₁ * e₁ᵀ) - ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)‖) +
          1 / ((1 - 1 / 16) * 1) * ∫ s in (0 : ℝ)..t,
            Curvature.specNorm ((1 + s) • (e₁ * e₁ᵀ) - ((1 + s) • (e₁ * e₁ᵀ) + N₁₆))) := by
  have hc : ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 + t) ≠ 0 := fun t ht => ne_of_gt (by linarith [ht.1])
  have hXc : ContinuousOn (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) (Set.Icc 0 1) :=
    fun s _ => (hasDerivAt_smul_e₁ 1 s).continuousAt.continuousWithinAt
  have hsol : ODESolution (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ)
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) 0 1 :=
    ⟨fun s _ => (hasDerivAt_smul_e₁_add_N₁₆ s).continuousAt.continuousWithinAt,
      fun s _ => (hasDerivAt_smul_e₁_add_N₁₆ s).hasDerivWithinAt⟩
  have hYd : IsDLRASolution 1 (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ)
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) 0 1 := by
    refine ⟨⟨hXc, fun s hs => ?_⟩, fun t ht => rank_smul_e₁ (hc t ht)⟩
    have h := (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt (s := Ici s)
    convert h using 1
    exact tangentProjAt_smul_e₁_apply (hc s (Ico_subset_Icc_self hs))
  exact hYd.norm_sub_le_integral_of_specNorm_sub_le
    (A := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆)
    (X := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) (X' := fun _ => e₁ * e₁ᵀ) (θ := 1 / 16) one_pos
    le_rfl (fun _ _ _ => by simp) hsol (fun _ _ => norm_e₁_mul_le) hXc
    (fun s _ => (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt) (fun t ht => (hyps_N₁₆ ht.1).1)
    (fun t ht => (hyps_N₁₆ ht.1).2.1) (fun t ht => (hyps_N₁₆ ht.1).2.2.1) (by norm_num)
    (fun t ht => (hyps_N₁₆ ht.1).2.2.2) (by simp)

/-- **Non-vacuity of `dlra_norm_sub_truncation_le_integral_of_specNorm_sub_le` and of
`dlra_norm_sub_truncation_le_integral_of_singularValues_le`** for `2 × 2` matrices, `r = 1`,
`A t = (1 + t) e₁ e₁ᵀ + diag(0, 1/16)` on `[0, 1]` (`Ȧ = e₁ e₁ᵀ`, `μ = ρ = 1`): the truncation
`X t = T₁(A t) = (1 + t) e₁ e₁ᵀ` differs from `A t`, and `‖X t - A t‖₂ = σ₁(A t) ≤ 1/16`. Here
`Ȧ` is tangent at `X t`, so the DLRA solution is `X` itself and the left-hand sides are `0`. -/
example :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(1 + t) • (e₁ * e₁ᵀ) - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
      1 / ((1 - 1 / 16) * 1) * Real.exp (1 / 1 * t) *
        ∫ s in (0 : ℝ)..t,
          Curvature.specNorm ((1 + s) • (e₁ * e₁ᵀ) - ((1 + s) • (e₁ * e₁ᵀ) + N₁₆))) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(1 + t) • (e₁ * e₁ᵀ) - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
      1 / ((1 - 1 / 16) * 1) * Real.exp (1 / 1 * t) *
        ∫ s in (0 : ℝ)..t, (toEuclideanLin ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)).singularValues 1) := by
  have hA : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) ((fun _ : ℝ => e₁ * e₁ᵀ) t) t :=
    fun t _ => hasDerivAt_smul_e₁_add_N₁₆ t
  have hμ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(fun _ : ℝ => e₁ * e₁ᵀ) t‖ ≤ 1 :=
    fun _ _ => norm_e₁_mul_le
  have hXbest : ∀ t ∈ Set.Icc (0 : ℝ) 1, (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) t =
      EckartYoung.truncation ((fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) t) 1 :=
    fun t ht => (truncation_smul_e₁_add ht.1).symm
  have hX : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ))
      ((fun _ : ℝ => e₁ * e₁ᵀ) t) t := fun t _ => hasDerivAt_smul_e₁ 1 t
  have hσ : ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 : ℝ) ≤ (toEuclideanLin
      ((fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) t)).singularValues (1 - 1) :=
    fun t ht => one_le_singularValues_smul_e₁_add ht.1
  have hgap : ∀ t ∈ Set.Icc (0 : ℝ) 1, (toEuclideanLin
      ((fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) t)).singularValues 1 ≤ 1 / 16 * 1 :=
    fun t ht => by
      rw [← EckartYoung.specNorm_sub_truncation]
      simp only []
      rw [truncation_smul_e₁_add ht.1, Curvature.specNorm_sub_comm]
      exact (hyps_N₁₆ ht.1).2.2.2
  have hUV : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((fun _ : ℝ => e₁) t)ᵀ * (fun _ : ℝ => e₁) t = 1 ∧
      ((fun _ : ℝ => e₁) t)ᵀ * (fun _ : ℝ => e₁) t = 1 ∧
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) t =
        (fun _ : ℝ => e₁) t * (fun t : ℝ => (1 + t) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) t *
          ((fun _ : ℝ => e₁) t)ᵀ :=
    fun t _ => ⟨e₁_transpose_mul_self, e₁_transpose_mul_self, smul_e₁_mul _⟩
  have hY : ODESolution (fun t (_ : Matrix (Fin 2) (Fin 2) ℝ) =>
      tangentProj ((fun _ : ℝ => e₁) t) ((fun _ : ℝ => e₁) t) ((fun _ : ℝ => e₁ * e₁ᵀ) t))
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) 0 1 := by
    refine ⟨fun s _ => (hasDerivAt_smul_e₁ 1 s).continuousAt.continuousWithinAt, fun s hs => ?_⟩
    have h := (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt (s := Ici s)
    have hc : (1 + s) ≠ 0 := ne_of_gt (by linarith [hs.1])
    convert h using 1
    rw [← tangentProjAt_smul_e₁ hc]
    exact tangentProjAt_smul_e₁_apply hc
  exact ⟨dlra_norm_sub_truncation_le_integral_of_specNorm_sub_le (θ := 1 / 16) one_pos one_pos hA
      hμ hXbest hX hσ (by norm_num) (fun t ht => (hyps_N₁₆ ht.1).2.2.2) hUV hY rfl,
    dlra_norm_sub_truncation_le_integral_of_singularValues_le (θ := 1 / 16) one_pos one_pos hA hμ
      hXbest hX hσ (by norm_num) hgap hUV hY rfl⟩

end QuasiOptimalitySpectralExamples

end LeanDLRA
