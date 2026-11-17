import LeanDLRA.Research.StiffOldColumnGalerkin

/-!
# Stiff problems with invariant old column spaces: forcing that is constant on the steps

`StiffOldColumnGalerkin` bounds the global error of the rank-adaptive BUG integrator for
`Y' = 𝓛 Y + g(t)`, when the projectors onto the old column spaces commute with the dissipative
operator `𝓛`, by the sum over the steps of

`ωₙ + 2 βₙ (τₙ₊₁ - τₙ) + ϑₙ`, `ωₙ = ‖Pₙ Ŷₙ₊₁ - Y_{L,n}(τₙ₊₁)‖`, `βₙ ≥ ‖g - Pₙ g‖`.

This file treats a forcing that is constant on every step, with value `cₙ` on step `n`, and a
symmetric operator `𝓛` that commutes with the old and the augmented left projectors.

* The numbers `βₙ` are expressed by the data: `β₀ = ‖c₀ - P₀ c₀‖` and
  `βₙ₊₁ = ‖cₙ₊₁ - cₙ‖ + ε + ‖P̂ₙ cₙ - Pₙ₊₁ cₙ‖`, the jump of the forcing, the bound `ε` for the
  normal parts, and the part of the old forcing in the augmented column space of step `n`
  that the column space after the step has lost.
* The numbers `ωₙ` are bounded by the L-step alone: `ωₙ ≤ 2 μₙ (τₙ₊₁ - τₙ)` if
  `‖𝓛 (Y_{L,n}(t) - Yₙ)‖ ≤ μₙ` on the step, that is, if the velocity of the L-step changes by at
  most `μₙ` during the step. The augmented row space does not enter this bound.

## Main results

* `IsRankAdaptiveBUGStep.of_field_eqOn`: the step predicate depends on the field only through
  its values on the step, if the new field is constant in time on the step.
* `IsRankAdaptiveBUGStep.norm_forcing_sub_augLeft_le_of_eqOn`: the bound `‖c - P₁ c‖ ≤ ε`
  for a forcing that equals `c` on the step.
* `IsRankAdaptiveBUGStep.norm_left_galerkin_sub_lstep_le`: `ω ≤ 2 μ (t₁ - t₀)`.
* `stiff_global_error_of_piecewise_const`: the global bound with the numbers `βₙ` above.
* `stiff_global_error_of_piecewise_const_uniform`: for a uniform grid and no loss of forcing
  columns,
  `‖Y_N - A(τ_N)‖ ≤ ‖Y₀ - A(τ₀)‖ + ∑ₙ (ωₙ + ϑₙ) + 2 h (‖c₀ - P₀ c₀‖ + ∑ₙ ‖cₙ₊₁ - cₙ‖) + 2 h N ε`.

## Remarks

* In the last bound `∑ₙ ‖cₙ₊₁ - cₙ‖` is the variation of the forcing and `h N` is the length
  of the time interval. No bound for `∑ₙ ωₙ` in terms of the data is proved; by
  `norm_left_galerkin_sub_lstep_le` it is at most `2 h` times the sum of the changes of the
  velocities of the L-steps.
* The hypothesis on the columns, `P̂ₙ cₙ = Pₙ₊₁ cₙ`, holds if the column space of `Yₙ₊₁` is the
  augmented column space of step `n`. It fails if the Galerkin result has smaller rank than the
  augmented basis, or if the truncation removes a column on which the forcing acts.

## Relation to the literature

The integrator is the one of [CerutiKuschLubich2022]. A lower bound of the form step size
times variation of the forcing for the same class of operators is
`StiffGlobalCycle.variation_mul_le_norm_sub_exactState`.
-/

open Set
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace IsRankAdaptiveBUGStep

variable {F F' : ℝ → E → E} {𝓛 P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {ε ϑ μ : ℝ}
  {YK YL YS : ℝ → E} {Y₀ Y₁ c : E} {t₀ t₁ : ℝ}

/-- A rank-adaptive BUG step for a field `F` is a step for every field `F'` that agrees with
`F` on `[t₀, t₁)` and is constant in time on `[t₀, t₁]`. -/
theorem of_field_eqOn (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hlt : t₀ < t₁) (hF : ∀ t ∈ Ico t₀ t₁, ∀ x, F t x = F' t x)
    (hF' : ∀ t ∈ Icc t₀ t₁, ∀ x, F' t x = F' t₀ x) :
    IsRankAdaptiveBUGStep F' ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁ :=
  have h0 : t₀ ∈ Ico t₀ t₁ := ⟨le_rfl, hlt⟩
  { projP₀ := hs.projP₀
    projQ₀ := hs.projQ₀
    projP₁ := hs.projP₁
    projQ₁ := hs.projQ₁
    comm₁ := hs.comm₁
    kSol := ⟨hs.kSol.cont, fun t ht => by
      have h := hs.kSol.deriv t ht
      rw [hF t ht] at h
      exact h⟩
    kStart := hs.kStart
    kCap := hs.kCap
    kNormal := fun t ht => by
      rw [hF' t ht, ← hF t₀ h0]
      exact hs.kNormal t₀ ⟨le_rfl, hlt.le⟩
    lSol := ⟨hs.lSol.cont, fun t ht => by
      have h := hs.lSol.deriv t ht
      rw [hF t ht] at h
      exact h⟩
    lStart := hs.lStart
    lCap := hs.lCap
    lNormal := fun t ht => by
      rw [hF' t ht, ← hF t₀ h0]
      exact hs.lNormal t₀ ⟨le_rfl, hlt.le⟩
    sSol := ⟨hs.sSol.cont, fun t ht => by
      have h := hs.sSol.deriv t ht
      rw [hF t ht] at h
      exact h⟩
    sStart := hs.sStart
    augP := hs.augP
    augQ := hs.augQ
    trunc := hs.trunc }

/-- **A forcing that is constant on the step lies in the augmented column space up to a normal
part.** If `F(t, x) = 𝓛 x + c` on `[t₀, t₁)` with a symmetric operator `𝓛`, and the augmented
left projector `P₁` commutes with `𝓛` and with the old right projector `Q₀`, then
`‖c - P₁ c‖ ≤ ε`. -/
theorem norm_forcing_sub_augLeft_le_of_eqOn
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hsplit : ∀ t ∈ Ico t₀ t₁, ∀ x, F t x = 𝓛 x + c) (hsym : ∀ x y, ⟪𝓛 x, y⟫ = ⟪x, 𝓛 y⟫)
    (hP𝓛 : ∀ x, P₁ (𝓛 x) = 𝓛 (P₁ x)) (hPQ : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (hlt : t₀ < t₁) :
    ‖c - P₁ c‖ ≤ ε :=
  (hs.of_field_eqOn (F' := fun _ x => 𝓛 x + c) hlt hsplit
    (fun _ _ _ => rfl)).norm_forcing_sub_augLeft_le (fun _ _ => rfl) hsym hP𝓛 hPQ hlt

/-- **The Galerkin result on the old columns against the L-step.** Let `F(t, x) = 𝓛 x + c` on
the step with a dissipative operator `𝓛`, let the old left projector `P₀` commute with `𝓛` and
with the augmented right projector, and let the augmented left projector contain it. If the
velocity of the L-step changes by at most `μ` during the step, `‖𝓛 (Y_L(t) - Y₀)‖ ≤ μ`, then

`‖P₀ Ŷ₁ - Y_L(t₁)‖ ≤ 2 μ (t₁ - t₀)`.

The bound does not contain the augmented row space. -/
theorem norm_left_galerkin_sub_lstep_le
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hsplit : ∀ t ∈ Ico t₀ t₁, ∀ x, F t x = 𝓛 x + c) (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hP𝓛 : ∀ x, P₀ (𝓛 x) = 𝓛 (P₀ x)) (hnest : ∀ x, P₁ (P₀ x) = P₀ x)
    (hPQ : ∀ x, P₀ (Q₁ x) = Q₁ (P₀ x)) (hY₀ : P₀ Y₀ = Y₀) (hlt : t₀ < t₁)
    (hμ : ∀ t ∈ Icc t₀ t₁, ‖𝓛 (YL t - Y₀)‖ ≤ μ) :
    ‖P₀ (YS t₁) - YL t₁‖ ≤ 2 * μ * (t₁ - t₀) := by
  have hP := hs.projP₀
  have hR := hs.galerkinProj
  have hH : 0 < t₁ - t₀ := sub_pos.2 hlt
  have ht₁ : t₁ ∈ Icc t₀ t₁ := ⟨hlt.le, le_rfl⟩
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ t₁ ht₁)
  have hPP : ∀ x, P₀ (P₁ x) = P₁ (P₀ x) := fun x =>
    (hP.comp_eq_of_comp_eq hs.projP₁ hnest x).trans (hnest x).symm
  have hYL : ∀ t ∈ Icc t₀ t₁, P₀ (YL t) = YL t :=
    hs.lSol.galerkin_mem_range hP (by rw [hs.lStart]; exact hY₀)
  have hmem : ∀ t ∈ Icc t₀ t₁, P₁ (Q₁ (YS t)) = YS t := hs.mem_range
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : E, v₀ = 𝓛 Y₀ + P₀ c := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : E, k = (t₁ - t₀)⁻¹ • (YL t₁ - Y₀) := ⟨_, rfl⟩
  -- the L-step against its Euler step
  have hE : ‖(YL t₁ - Y₀) - (t₁ - t₀) • v₀‖ ≤ μ * (t₁ - t₀) := by
    have hc : ContinuousOn (fun t => YL t - (t - t₀) • v₀) (Icc t₀ t₁) :=
      hs.lSol.cont.sub ((continuous_id.sub continuous_const).smul continuous_const).continuousOn
    have hd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => YL t - (t - t₀) • v₀)
        (P₀ (F t (YL t)) - v₀) (Ici t) t := fun t ht => by
      have h1 := ((hasDerivAt_id t).sub_const t₀).smul_const v₀
      rw [one_smul] at h1
      exact (hs.lSol.deriv t ht).sub h1.hasDerivWithinAt
    have hb : ∀ t ∈ Ico t₀ t₁, ‖P₀ (F t (YL t)) - v₀‖ ≤ μ := fun t ht => by
      have e : P₀ (F t (YL t)) - v₀ = 𝓛 (YL t - Y₀) := by
        rw [hsplit t ht, hv₀, map_add, hP𝓛, hYL t (Ico_subset_Icc_self ht), map_sub]
        abel
      rw [e]
      exact hμ t (Ico_subset_Icc_self ht)
    have h := norm_image_sub_le_of_norm_deriv_right_le_segment hc hd hb t₁ ht₁
    have e : (YL t₁ - (t₁ - t₀) • v₀) - (YL t₀ - (t₀ - t₀) • v₀)
        = (YL t₁ - Y₀) - (t₁ - t₀) • v₀ := by
      rw [hs.lStart, sub_self, zero_smul, sub_zero]
      abel
    rw [e] at h
    exact h
  have hkv : ‖v₀ - k‖ ≤ μ := by
    have e : v₀ - k = -((t₁ - t₀)⁻¹ • ((YL t₁ - Y₀) - (t₁ - t₀) • v₀)) := by
      rw [hk]
      simp only [smul_sub, smul_smul, inv_mul_cancel₀ hH.ne', one_smul]
      abel
    rw [e, norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hH.le)]
    calc (t₁ - t₀)⁻¹ * ‖(YL t₁ - Y₀) - (t₁ - t₀) • v₀‖
        ≤ (t₁ - t₀)⁻¹ * (μ * (t₁ - t₀)) := mul_le_mul_of_nonneg_left hE (inv_nonneg.2 hH.le)
      _ = μ := by field_simp
  -- the interpolant of the L-step lies in the Galerkin space
  have hRk : P₁ (Q₁ k) = k := by
    have h1 : P₁ (Q₁ (YL t₁)) = YL t₁ := by
      rw [hs.lCap, ← hYL t₁ ht₁, hnest]
    rw [hk, map_smul, map_smul, map_sub, map_sub, h1, hs.galerkin_fix]
  have hPk : P₀ k = k := by
    rw [hk, map_smul, map_sub, hYL t₁ ht₁, hY₀]
  have hRd : ∀ t ∈ Icc t₀ t₁, P₁ (Q₁ (P₀ (YS t) - (Y₀ + (t - t₀) • k)))
      = P₀ (YS t) - (Y₀ + (t - t₀) • k) := by
    intro t ht
    simp only [map_sub, map_add, map_smul, hRk, hs.galerkin_fix]
    rw [← hPQ, ← hPP, hmem t ht]
  have hcont : ContinuousOn (fun t => P₀ (YS t) - (Y₀ + (t - t₀) • k)) (Icc t₀ t₁) :=
    (P₀.continuous.comp_continuousOn hs.sSol.cont).sub
      (continuous_const.add
        ((continuous_id.sub continuous_const).smul continuous_const)).continuousOn
  have hderiv : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => P₀ (YS t) - (Y₀ + (t - t₀) • k))
      (P₀ (P₁ (Q₁ (F t (YS t)))) - k) (Ici t) t := fun t ht => by
    have h1 := (((hasDerivAt_id t).sub_const t₀).smul_const k).const_add Y₀
    rw [one_smul] at h1
    exact (P₀.hasFDerivAt.comp_hasDerivWithinAt t (hs.sSol.deriv t ht)).sub
      h1.hasDerivWithinAt
  have h := norm_le_add_mul_of_dissipative_forced (T := P₁ * Q₁) (𝓛 := 𝓛) (β := 2 * μ)
    hcont hderiv
    (fun t ht => by
      have hx := hRd t (Ico_subset_Icc_self ht)
      have hsy := hR.symm (𝓛 (P₀ (YS t) - (Y₀ + (t - t₀) • k)))
        (P₀ (YS t) - (Y₀ + (t - t₀) • k))
      change ⟪P₁ (Q₁ (𝓛 (P₀ (YS t) - (Y₀ + (t - t₀) • k)))),
          P₀ (YS t) - (Y₀ + (t - t₀) • k)⟫
        = ⟪𝓛 (P₀ (YS t) - (Y₀ + (t - t₀) • k)),
          P₁ (Q₁ (P₀ (YS t) - (Y₀ + (t - t₀) • k)))⟫ at hsy
      change ⟪P₁ (Q₁ (𝓛 (P₀ (YS t) - (Y₀ + (t - t₀) • k)))),
        P₀ (YS t) - (Y₀ + (t - t₀) • k)⟫ ≤ 0
      rw [hsy, hx]
      exact hdiss _)
    (fun t ht => by
      have e : P₀ (P₁ (Q₁ (F t (YS t)))) - k
          - (P₁ * Q₁) (𝓛 (P₀ (YS t) - (Y₀ + (t - t₀) • k)))
          = (P₁ * Q₁) ((v₀ - k) + (t - t₀) • 𝓛 k) := by
        change P₀ (P₁ (Q₁ (F t (YS t)))) - k
          - P₁ (Q₁ (𝓛 (P₀ (YS t) - (Y₀ + (t - t₀) • k))))
          = P₁ (Q₁ ((v₀ - k) + (t - t₀) • 𝓛 k))
        rw [hPP, hPQ, hsplit t ht, hv₀]
        simp only [map_sub, map_add, map_smul, hP𝓛, hRk]
        abel
      rw [e]
      refine (hR.norm_le _).trans ((norm_add_le _ _).trans ?_)
      have h1 : ‖(t - t₀) • 𝓛 k‖ ≤ μ := by
        have e1 : (t - t₀) • 𝓛 k = ((t - t₀) * (t₁ - t₀)⁻¹) • 𝓛 (YL t₁ - Y₀) := by
          rw [hk, map_smul, smul_smul]
        have hs0 : 0 ≤ (t - t₀) * (t₁ - t₀)⁻¹ :=
          mul_nonneg (sub_nonneg.2 ht.1) (inv_nonneg.2 hH.le)
        have hs1 : (t - t₀) * (t₁ - t₀)⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one hH]
          linarith [ht.2]
        rw [e1, norm_smul, Real.norm_of_nonneg hs0]
        calc (t - t₀) * (t₁ - t₀)⁻¹ * ‖𝓛 (YL t₁ - Y₀)‖
            ≤ 1 * μ := mul_le_mul hs1 (hμ t₁ ht₁) (norm_nonneg _) zero_le_one
          _ = μ := one_mul μ
      linarith)
    t₁ ht₁
  have e1 : P₀ (YS t₁) - (Y₀ + (t₁ - t₀) • k) = P₀ (YS t₁) - YL t₁ := by
    rw [hk, smul_smul, mul_inv_cancel₀ hH.ne', one_smul]
    abel
  have e0 : P₀ (YS t₀) - (Y₀ + (t₀ - t₀) • k) = 0 := by
    rw [hs.start_eq, hY₀, sub_self, zero_smul, add_zero, sub_self]
  rw [e1, e0, norm_zero, zero_add] at h
  exact h

end IsRankAdaptiveBUGStep

section Global

variable {F : ℝ → E → E} {g : ℝ → E} {𝓛 : E →L[ℝ] E} {ε h : ℝ} {ϑ β : ℕ → ℝ} {τ : ℕ → ℝ}
  {N : ℕ} {P Q Pa Qa : ℕ → E →L[ℝ] E} {Y c : ℕ → E} {YK YL YS : ℕ → ℝ → E} {A : ℝ → E}

/-- **Global error for a forcing that is constant on the steps, old column spaces invariant.**
Let `F(t, x) = 𝓛 x + g(t)` with a symmetric dissipative operator `𝓛` and `g = cₙ` on step `n`,
and let the old and the augmented left projectors commute with `𝓛`. If `β₀` bounds the part of
`c₀` outside the first column space and `βₙ₊₁` bounds the sum of the jump `‖cₙ₊₁ - cₙ‖`, of
`ε`, and of the part `‖P̂ₙ cₙ - Pₙ₊₁ cₙ‖` of the old forcing that the column space has lost, then

`‖Y_N - A(τ_N)‖ ≤ ‖Y₀ - A(τ₀)‖ + ∑ₙ (‖Pₙ Ŷₙ₊₁ - Y_{L,n}(τₙ₊₁)‖ + 2 βₙ (τₙ₊₁ - τₙ) + ϑₙ)`. -/
theorem stiff_global_error_of_piecewise_const
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε (ϑ n) (P n) (Q n) (Pa n) (Qa n) (τ n)
      (τ (n + 1)) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hτ : ∀ n < N, τ n < τ (n + 1)) (hsplit : ∀ t x, F t x = 𝓛 x + g t)
    (hconst : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)), g t = c n)
    (hsym : ∀ x y, ⟪𝓛 x, y⟫ = ⟪x, 𝓛 y⟫) (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hP𝓛 : ∀ n < N, ∀ x, P n (𝓛 x) = 𝓛 (P n x))
    (hPa𝓛 : ∀ n < N, ∀ x, Pa n (𝓛 x) = 𝓛 (Pa n x))
    (hnest : ∀ n < N, ∀ x, Pa n (P n x) = P n x)
    (hPQ : ∀ n < N, ∀ x, P n (Qa n x) = Qa n (P n x))
    (hPaQ : ∀ n < N, ∀ x, Pa n (Q n x) = Q n (Pa n x)) (hY : ∀ n < N, P n (Y n) = Y n)
    (hA : ∀ n < N, ODESolution F A (τ n) (τ (n + 1)))
    (hβ0 : ‖c 0 - P 0 (c 0)‖ ≤ β 0)
    (hβ : ∀ n, n + 1 < N →
      ‖c (n + 1) - c n‖ + ε + ‖Pa n (c n) - P (n + 1) (c n)‖ ≤ β (n + 1)) :
    ‖Y N - A (τ N)‖ ≤ ‖Y 0 - A (τ 0)‖
      + ∑ n ∈ Finset.range N, (‖P n (YS n (τ (n + 1))) - YL n (τ (n + 1))‖
        + 2 * β n * (τ (n + 1) - τ n) + ϑ n) := by
  refine stiff_global_error_of_comm_left hstep (fun n hn => (hτ n hn).le) hsplit hdiss hP𝓛
    (fun n hn x => ((hstep n hn).projP₀.comp_eq_of_comp_eq (hstep n hn).projP₁
      (hnest n hn) x).trans (hnest n hn x).symm) hPQ hY hA ?_
  intro n hn t ht
  rw [hconst n hn t ht]
  cases n with
  | zero => exact hβ0
  | succ m =>
    have hm : m < N := (Nat.lt_succ_self m).trans hn
    have hPm := (hstep (m + 1) hn).projP₀
    have h1 : ‖c m - Pa m (c m)‖ ≤ ε :=
      (hstep m hm).norm_forcing_sub_augLeft_le_of_eqOn
        (fun s hs x => by rw [hsplit, hconst m hm s hs]) hsym (hPa𝓛 m hm) (hPaQ m hm) (hτ m hm)
    have h2 : ‖(c (m + 1) - c m) - P (m + 1) (c (m + 1) - c m)‖ ≤ ‖c (m + 1) - c m‖ :=
      hPm.norm_sub_le _
    have e : c (m + 1) - P (m + 1) (c (m + 1))
        = ((c (m + 1) - c m) - P (m + 1) (c (m + 1) - c m)) + (c m - Pa m (c m))
          + (Pa m (c m) - P (m + 1) (c m)) := by
      rw [map_sub]
      abel
    rw [e]
    have h3 := norm_add_le (((c (m + 1) - c m) - P (m + 1) (c (m + 1) - c m))
      + (c m - Pa m (c m))) (Pa m (c m) - P (m + 1) (c m))
    have h4 := norm_add_le ((c (m + 1) - c m) - P (m + 1) (c (m + 1) - c m))
      (c m - Pa m (c m))
    have h5 := hβ m hn
    linarith

/-- **Global error on a uniform grid for a forcing that is constant on the steps**, when no
column on which the forcing acts is lost (`P̂ₙ cₙ = Pₙ₊₁ cₙ`): under the hypotheses of
`stiff_global_error_of_piecewise_const`,

`‖Y_N - A(τ_N)‖ ≤ ‖Y₀ - A(τ₀)‖ + ∑ₙ (ωₙ + ϑₙ) + 2 h (‖c₀ - P₀ c₀‖ + ∑ₙ ‖cₙ₊₁ - cₙ‖) + 2 h N ε`

with `ωₙ = ‖Pₙ Ŷₙ₊₁ - Y_{L,n}(τₙ₊₁)‖`. The third term is the step size times the variation of
the forcing, the last one the length of the time interval times `2 ε`. -/
theorem stiff_global_error_of_piecewise_const_uniform
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε (ϑ n) (P n) (Q n) (Pa n) (Qa n) (τ n)
      (τ (n + 1)) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hh : 0 < h) (hτ : ∀ n < N, τ (n + 1) - τ n = h) (hsplit : ∀ t x, F t x = 𝓛 x + g t)
    (hconst : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)), g t = c n)
    (hsym : ∀ x y, ⟪𝓛 x, y⟫ = ⟪x, 𝓛 y⟫) (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hP𝓛 : ∀ n < N, ∀ x, P n (𝓛 x) = 𝓛 (P n x))
    (hPa𝓛 : ∀ n < N, ∀ x, Pa n (𝓛 x) = 𝓛 (Pa n x))
    (hnest : ∀ n < N, ∀ x, Pa n (P n x) = P n x)
    (hPQ : ∀ n < N, ∀ x, P n (Qa n x) = Qa n (P n x))
    (hPaQ : ∀ n < N, ∀ x, Pa n (Q n x) = Q n (Pa n x)) (hY : ∀ n < N, P n (Y n) = Y n)
    (hA : ∀ n < N, ODESolution F A (τ n) (τ (n + 1)))
    (hcol : ∀ n, n + 1 < N → Pa n (c n) = P (n + 1) (c n)) :
    ‖Y N - A (τ N)‖ ≤ ‖Y 0 - A (τ 0)‖
      + ∑ n ∈ Finset.range N, (‖P n (YS n (τ (n + 1))) - YL n (τ (n + 1))‖ + ϑ n)
      + 2 * h * (‖c 0 - P 0 (c 0)‖ + ∑ n ∈ Finset.range (N - 1), ‖c (n + 1) - c n‖)
      + 2 * h * N * ε := by
  have hlt : ∀ n < N, τ n < τ (n + 1) := fun n hn => by linarith [hτ n hn]
  obtain ⟨β, hβdef⟩ : ∃ β : ℕ → ℝ, β = fun n =>
      if n = 0 then ‖c 0 - P 0 (c 0)‖ else ‖c n - c (n - 1)‖ + ε := ⟨_, rfl⟩
  have hβs : ∀ m, β (m + 1) = ‖c (m + 1) - c m‖ + ε := fun m => by simp [hβdef]
  have hβ0 : β 0 = ‖c 0 - P 0 (c 0)‖ := by simp [hβdef]
  have h1 := stiff_global_error_of_piecewise_const (β := β) hstep hlt hsplit hconst hsym hdiss
    hP𝓛 hPa𝓛 hnest hPQ hPaQ hY hA hβ0.ge
    (fun m hm => by rw [hβs, hcol m hm, sub_self, norm_zero, add_zero])
  have h2 : ∑ n ∈ Finset.range N, (‖P n (YS n (τ (n + 1))) - YL n (τ (n + 1))‖
        + 2 * β n * (τ (n + 1) - τ n) + ϑ n)
      = ∑ n ∈ Finset.range N, (‖P n (YS n (τ (n + 1))) - YL n (τ (n + 1))‖ + ϑ n)
        + 2 * h * ∑ n ∈ Finset.range N, β n := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hτ n (Finset.mem_range.1 hn)]
    ring
  have h3 : ∑ n ∈ Finset.range N, β n
      ≤ ‖c 0 - P 0 (c 0)‖ + ∑ n ∈ Finset.range (N - 1), ‖c (n + 1) - c n‖ + N * ε := by
    cases N with
    | zero => simp
    | succ M =>
      have hε : 0 ≤ ε :=
        (hstep 0 (Nat.succ_pos M)).toIsBUGStep.eps_nonneg (hlt 0 (Nat.succ_pos M)).le
      rw [Finset.sum_range_succ', hβ0, Nat.add_sub_cancel]
      simp only [hβs, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      push_cast
      linarith
  have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 2 * h)
  rw [h2] at h1
  linarith

end Global

namespace StiffCouplingExample

open scoped Matrix LeanDLRA.Frobenius

/-- Non-vacuity of `IsRankAdaptiveBUGStep.norm_left_galerkin_sub_lstep_le` with nonzero data:
for the step `step` of the example the L-step is `Y₀ + t W` with `W N₁ = 0`, so its velocity
does not change (`μ = 0`), for every stiffness `λ ≥ 0`, and the Galerkin result agrees with the
result of the L-step on the old columns. -/
example {lam h : ℝ} (hlam : 0 ≤ lam) (hh : 0 < h) :
    ‖(leftProj U₀ : Matrix (Fin 2) (Fin 3) ℝ →L[ℝ] Matrix (Fin 2) (Fin 3) ℝ)
        (Y₀ + h • W) - (Y₀ + h • W)‖ ≤ 2 * 0 * (h - 0) := by
  refine (step lam h).norm_left_galerkin_sub_lstep_le (c := D - Y₀ * (lam • N₁))
    (𝓛 := stiffOp lam) (fun _ _ _ => rfl) (stiffOp_dissipative hlam) (fun x => ?_)
    (fun x => (isOrthProj_leftProj orthU₀).idem x)
    (fun x => leftProj_rightProj_comm U₀ Va x) U₀_mul_Y₀ hh (fun t _ => ?_)
  · change U₀ * U₀ᵀ * (x * (lam • N₁)) = U₀ * U₀ᵀ * x * (lam • N₁)
    simp only [Matrix.mul_assoc]
  · have e : stiffOp lam ((Y₀ + t • W) - Y₀) = 0 := by
      change ((Y₀ + t • W) - Y₀) * (lam • N₁) = 0
      rw [add_sub_cancel_left, Matrix.smul_mul, Matrix.mul_smul, W_mul_N₁, smul_zero,
        smul_zero]
    rw [e, norm_zero]

/-- The forcing of the example outside the old column space is `D - W`, of norm `4`. -/
private lemma norm_forcing_sub_left (lam : ℝ) :
    ‖(D - Y₀ * (lam • N₁))
      - (leftProj U₀ : Matrix (Fin 2) (Fin 3) ℝ →L[ℝ] Matrix (Fin 2) (Fin 3) ℝ)
        (D - Y₀ * (lam • N₁))‖ = 4 := by
  have e : (D - Y₀ * (lam • N₁))
      - (leftProj U₀ : Matrix (Fin 2) (Fin 3) ℝ →L[ℝ] Matrix (Fin 2) (Fin 3) ℝ)
        (D - Y₀ * (lam • N₁)) = D - W := by
    change (D - Y₀ * (lam • N₁)) - U₀ * U₀ᵀ * (D - Y₀ * (lam • N₁)) = D - W
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, U₀_mul_Y₀, U₀_mul_D]
    abel
  rw [e, norm_D_sub_W]

/-- The Galerkin result of the example agrees with the result of the L-step. -/
private lemma left_galerkin_sub_lstep (h : ℝ) :
    (leftProj U₀ : Matrix (Fin 2) (Fin 3) ℝ →L[ℝ] Matrix (Fin 2) (Fin 3) ℝ) (Y₀ + h • W)
      - (Y₀ + h • W) = 0 := by
  change U₀ * U₀ᵀ * (Y₀ + h • W) - (Y₀ + h • W) = 0
  rw [Matrix.mul_add, Matrix.mul_smul, U₀_mul_Y₀, U₀_mul_W, sub_self]

/-- The old left projector of the example commutes with the stiff operator. -/
private lemma leftProj_stiffOp (lam : ℝ) (x : Matrix (Fin 2) (Fin 3) ℝ) :
    (leftProj U₀ : Matrix (Fin 2) (Fin 3) ℝ →L[ℝ] Matrix (Fin 2) (Fin 3) ℝ) (stiffOp lam x)
      = stiffOp lam (leftProj U₀ x) := by
  change U₀ * U₀ᵀ * (x * (lam • N₁)) = U₀ * U₀ᵀ * x * (lam • N₁)
  simp only [Matrix.mul_assoc]

/-- Non-vacuity of `stiff_global_error_of_piecewise_const` with nonzero data: one step
(`N = 1`) of the example with the constant forcing `D - Y₀ (λ N₁)`, for every stiffness `λ ≥ 0`
and every `h > 0`, with `β₀ = 4`. The bound reads `‖Y₁ - A(h)‖ ≤ 8 h`; by `error_eq` the
left-hand side equals `4 h`. With one step the hypothesis on `βₙ₊₁` is empty. -/
example {lam h : ℝ} (hlam : 0 ≤ lam) (hh : 0 < h) :
    ‖(Y₀ + h • W) - (Y₀ + h • D)‖ ≤ 8 * h := by
  have key := stiff_global_error_of_piecewise_const (N := 1) (F := field lam)
    (g := fun _ => D - Y₀ * (lam • N₁)) (𝓛 := stiffOp lam) (ε := 4) (ϑ := fun _ => 0)
    (β := fun _ => 4) (τ := fun n => (n : ℝ) * h) (P := fun _ => leftProj U₀)
    (Q := fun _ => rightProj V₀) (Pa := fun _ => leftProj U₀) (Qa := fun _ => rightProj Va)
    (Y := fun n => Y₀ + ((n : ℝ) * h) • W) (c := fun _ => D - Y₀ * (lam • N₁))
    (YK := fun _ _ => Y₀) (YL := fun _ t => Y₀ + t • W) (YS := fun _ t => Y₀ + t • W)
    (A := fun t => Y₀ + t • D)
    (fun n hn => by
      obtain rfl : n = 0 := Nat.lt_one_iff.1 hn
      simpa using step lam h)
    (fun n hn => by
      obtain rfl : n = 0 := Nat.lt_one_iff.1 hn
      simpa using hh)
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) (stiffOp_symm lam) (stiffOp_dissipative hlam)
    (fun _ _ x => leftProj_stiffOp lam x) (fun _ _ x => leftProj_stiffOp lam x)
    (fun _ _ x => (isOrthProj_leftProj orthU₀).idem x)
    (fun _ _ x => leftProj_rightProj_comm U₀ Va x)
    (fun _ _ x => leftProj_rightProj_comm U₀ V₀ x)
    (fun n hn => by
      obtain rfl : n = 0 := Nat.lt_one_iff.1 hn
      simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero]
      exact U₀_mul_Y₀)
    (fun n hn => by
      obtain rfl : n = 0 := Nat.lt_one_iff.1 hn
      simpa using exactSol lam h)
    (norm_forcing_sub_left lam).le (fun n hn => absurd hn (by omega))
  simp only [Finset.sum_range_one, Nat.cast_zero, Nat.cast_one, zero_add, zero_mul, one_mul,
    zero_smul, add_zero, sub_zero, sub_self, norm_zero, left_galerkin_sub_lstep] at key
  linarith

/-- Non-vacuity of `stiff_global_error_of_piecewise_const_uniform` with nonzero data: one
step (`N = 1`) of the example, for every stiffness `λ ≥ 0` and every `h > 0`. The forcing
outside the first column space has norm `4` and `ε = 4`, so the bound reads
`‖Y₁ - A(h)‖ ≤ 16 h`. With one step the hypothesis on the columns is empty. -/
example {lam h : ℝ} (hlam : 0 ≤ lam) (hh : 0 < h) :
    ‖(Y₀ + h • W) - (Y₀ + h • D)‖ ≤ 16 * h := by
  have key := stiff_global_error_of_piecewise_const_uniform (N := 1) (F := field lam)
    (g := fun _ => D - Y₀ * (lam • N₁)) (𝓛 := stiffOp lam) (ε := 4) (h := h)
    (ϑ := fun _ => 0) (τ := fun n => (n : ℝ) * h) (P := fun _ => leftProj U₀)
    (Q := fun _ => rightProj V₀) (Pa := fun _ => leftProj U₀) (Qa := fun _ => rightProj Va)
    (Y := fun n => Y₀ + ((n : ℝ) * h) • W) (c := fun _ => D - Y₀ * (lam • N₁))
    (YK := fun _ _ => Y₀) (YL := fun _ t => Y₀ + t • W) (YS := fun _ t => Y₀ + t • W)
    (A := fun t => Y₀ + t • D)
    (fun n hn => by
      obtain rfl : n = 0 := Nat.lt_one_iff.1 hn
      simpa using step lam h)
    hh
    (fun n hn => by
      obtain rfl : n = 0 := Nat.lt_one_iff.1 hn
      simp)
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) (stiffOp_symm lam) (stiffOp_dissipative hlam)
    (fun _ _ x => leftProj_stiffOp lam x) (fun _ _ x => leftProj_stiffOp lam x)
    (fun _ _ x => (isOrthProj_leftProj orthU₀).idem x)
    (fun _ _ x => leftProj_rightProj_comm U₀ Va x)
    (fun _ _ x => leftProj_rightProj_comm U₀ V₀ x)
    (fun n hn => by
      obtain rfl : n = 0 := Nat.lt_one_iff.1 hn
      simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero]
      exact U₀_mul_Y₀)
    (fun n hn => by
      obtain rfl : n = 0 := Nat.lt_one_iff.1 hn
      simpa using exactSol lam h)
    (fun n hn => absurd hn (by omega))
  simp only [Finset.sum_range_one, Finset.range_zero, Finset.sum_empty, Nat.sub_self,
    Nat.cast_zero, Nat.cast_one, zero_add, zero_mul, one_mul, mul_one, zero_smul, add_zero,
    sub_self, norm_zero, left_galerkin_sub_lstep, norm_forcing_sub_left] at key
  linarith

/-- Non-vacuity of `IsRankAdaptiveBUGStep.of_field_eqOn` with nonzero data: the step `step` of
the example, for every stiffness `λ` and every `h > 0`, is also a step for the field that agrees
with `field λ` up to the time `h` and has the additional forcing `(t - h) D` after it. -/
example (lam : ℝ) {h : ℝ} (hh : 0 < h) :
    IsRankAdaptiveBUGStep (fun t x => field lam t x + (max t h - h) • D) 4 0 (leftProj U₀)
      (rightProj V₀) (leftProj U₀) (rightProj Va) 0 h Y₀ (fun _ => Y₀) (fun t => Y₀ + t • W)
      (fun t => Y₀ + t • W) (Y₀ + h • W) :=
  (step lam h).of_field_eqOn hh
    (fun t ht x => by simp only [max_eq_right ht.2.le, sub_self, zero_smul, add_zero])
    (fun t ht x => show field lam t x + (max t h - h) • D = field lam 0 x + (max 0 h - h) • D from
      congrArg₂ (· + ·) rfl (by rw [max_eq_right ht.2, max_eq_right hh.le]))

/-- Non-vacuity of `IsRankAdaptiveBUGStep.norm_forcing_sub_augLeft_le_of_eqOn` with nonzero
data: for the step `step` of the example and every stiffness `λ`, the constant forcing
`D - Y₀ (λ N₁)` lies in the augmented column space up to `ε = 4`. By `norm_forcing_sub_left`
the bound is attained. -/
example (lam : ℝ) {h : ℝ} (hh : 0 < h) :
    ‖(D - Y₀ * (lam • N₁))
      - (leftProj U₀ : Matrix (Fin 2) (Fin 3) ℝ →L[ℝ] Matrix (Fin 2) (Fin 3) ℝ)
        (D - Y₀ * (lam • N₁))‖ ≤ 4 :=
  (step lam h).norm_forcing_sub_augLeft_le_of_eqOn (𝓛 := stiffOp lam) (fun _ _ _ => rfl)
    (stiffOp_symm lam) (leftProj_stiffOp lam) (fun x => leftProj_rightProj_comm U₀ V₀ x) hh

end StiffCouplingExample

end LeanDLRA
