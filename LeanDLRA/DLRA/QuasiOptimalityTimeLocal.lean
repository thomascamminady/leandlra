import LeanDLRA.DLRA.QuasiOptimalitySpectral
import LeanDLRA.LinearAlgebra.SVD.TruncationDeriv
import LeanDLRA.Analysis.GronwallVariableRate

/-!
# Quasi-optimality of matrix DLRA with constants that depend on time

The quasi-optimality bound of `LeanDLRA/DLRA/QuasiOptimalitySpectral.lean` has constants `ρ`, `μ`,
`θ` that hold on the whole interval. This file has the bound with functions `ρ(t) ≤ σ_{r-1}(X t)`
and `μ(t) ≥ ‖F(t, A t)‖` of time: with `τ(s) = ‖X s - A s‖₂ < ρ(s)` and the rate
`k(s) = L + μ(s)/ρ(s)`,

  `‖Y t - X t‖ ≤ e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖X s - A s‖ + μ(s)/(ρ(s) - τ(s)) τ(s)) ds`.

For the truncated SVD `X t = T_r(A t)` under the gap `σ_r(A t) < σ_{r-1}(A t)` (indices start at
`0`) one may take `ρ(t) = σ_{r-1}(A t)`, and `τ(t) = σ_r(A t)`.

## Main results

* `norm_sub_tangentProjAt_le_div_sub_mul_specNorm`: the velocity bound
  `‖X' - P(X t) A'‖ ≤ μ/(ρ - τ) τ` with `ρ`, `μ` at the time `t` only.
* `dlra_norm_sub_le_integral_exp_integral_of_specNorm_sub_lt`,
  `IsDLRASolution.norm_sub_le_integral_exp_integral_of_specNorm_sub_lt`: the bound along a curve
  of critical points.
* `IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_singularValues_lt`: the bound
  against the truncated SVD under the gap; no hypothesis on the curve `T_r(A t)` besides the gap.

## Implementation notes

The proof is that of `dlra_norm_sub_le_integral_of_specNorm_sub_le` with Grönwall's inequality for
a rate that depends on time (`norm_le_exp_integral_mul_add_integral_exp_integral_mul`). The
functions `ρ` and `μ` are continuous on `[a, b]`: this gives the primitives of the rate and of the
source, and a positive lower bound of `ρ`, which the tangency of `X'` uses.

`dlra_norm_sub_le_integral_of_specNorm_sub_le` is restated verbatim as an `example` and follows
with constant `ρ`, `μ`. The bound of [FepponLermusiaux2018, Theorem 32] follows (the last
`example` of the section): there the kernel is `e^{η (t - s)}` with
`η ≥ L + 2 ‖F(t, A t)‖/σ_{r-1}(A t)` and the gap term has the Frobenius norm of the tail.

## References

* [FepponLermusiaux2018]
-/

open Set Finset Matrix Filter
open scoped Topology

namespace LeanDLRA

section TimeLocal

open scoped LeanDLRA.Frobenius
open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Monotonicity of the interval integral for a nonnegative integrand below a continuous one. -/
private theorem intervalIntegral_le_of_nonneg_of_le {f g : ℝ → ℝ} {a t : ℝ} (hat : a ≤ t)
    (hg : ContinuousOn g (Icc a t)) (h0 : ∀ s ∈ Icc a t, 0 ≤ f s)
    (hfg : ∀ s ∈ Icc a t, f s ≤ g s) : ∫ s in a..t, f s ≤ ∫ s in a..t, g s := by
  rw [intervalIntegral.integral_of_le hat, intervalIntegral.integral_of_le hat]
  refine MeasureTheory.integral_mono_of_nonneg ?_
    (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self) ?_
  · exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall fun s hs => h0 s (Ioc_subset_Icc_self hs))
  · exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall fun s hs => hfg s (Ioc_subset_Icc_self hs))

/-- **The velocity of a curve of critical points, constants at one time.** Let `X u` have rank `r`
with `P(X u) (A u - X u) = 0` and `0 < ρ₀ ≤ σ_{r-1}(X u)` on `s`, with derivatives `A'`, `X'` at
`t ∈ s` within `s`. If `‖X t - A t‖₂ < ρ ≤ σ_{r-1}(X t)` and `‖A'‖ ≤ μ` at the time `t`, then
`‖X' - P(X t) A'‖ ≤ μ / (ρ - ‖X t - A t‖₂) ‖X t - A t‖₂`. The lower bound `ρ₀` on `s` is used for
the tangency of `X'` only and does not enter the bound. -/
theorem norm_sub_tangentProjAt_le_div_sub_mul_specNorm {r : ℕ} {A X : ℝ → Matrix m n ℝ}
    {A' X' : Matrix m n ℝ} {s : Set ℝ} {t ρ₀ ρ μ : ℝ} (hA : HasDerivWithinAt A A' s t)
    (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s) (hs : (𝓝[s \ {t}] t).NeBot) (hρ₀ : 0 < ρ₀)
    (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ₀ : ∀ u ∈ s, ρ₀ ≤ (toEuclideanLin (X u)).singularValues (r - 1))
    (hσ : ρ ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ u ∈ s, tangentProjAt (X u) (A u - X u) = 0) (hμ : ‖A'‖ ≤ μ)
    (hd : Curvature.specNorm (X t - A t) < ρ) :
    ‖X' - tangentProjAt (X t) A'‖ ≤
      μ / (ρ - Curvature.specNorm (X t - A t)) * Curvature.specNorm (X t - A t) := by
  have hτ0 := Curvature.specNorm_nonneg (X t - A t)
  have hρ : 0 < ρ := hτ0.trans_lt hd
  have htan : tangentProjAt (X t) X' = X' := tangentProjAt_eq_self_iff.mpr
    (mem_tangentSpaceAt_of_hasDerivWithinAt hX ht hs hρ₀ hrank hσ₀)
  have hdef := norm_tangentProjAt_sub_le_inv_mul_specNorm_of_hasDerivWithinAt hA hX ht hs hρ
    hrank hσ hopt
  rw [Curvature.specNorm_sub_comm] at hdef
  have h1 : ‖tangentProjAt (X t) A'‖ ≤ μ := ((isOrthProj_tangentProjAt _).norm_le _).trans hμ
  have e : X' = tangentProjAt (X t) A' - tangentProjAt (X t) (A' - X') := by
    rw [map_sub, htan]
    abel
  have h3 : ‖X'‖ ≤ ‖tangentProjAt (X t) A'‖ + ‖tangentProjAt (X t) (A' - X')‖ := by
    conv_lhs => rw [e]
    exact norm_sub_le _ _
  have e' : X' - tangentProjAt (X t) A' = -tangentProjAt (X t) (A' - X') := by
    rw [map_sub, htan]
    abel
  rw [e', norm_neg, div_mul_eq_mul_div, le_div_iff₀ (sub_pos.2 hd)]
  have h4 : ‖tangentProjAt (X t) (A' - X')‖ * ρ ≤ ‖X'‖ * Curvature.specNorm (X t - A t) := by
    have h := mul_le_mul_of_nonneg_right hdef hρ.le
    have h5 : ρ⁻¹ * ‖X'‖ * Curvature.specNorm (X t - A t) * ρ =
        ‖X'‖ * Curvature.specNorm (X t - A t) := by
      field_simp
    rwa [h5] at h
  have h6 : ‖X'‖ * Curvature.specNorm (X t - A t) ≤
      (μ + ‖tangentProjAt (X t) (A' - X')‖) * Curvature.specNorm (X t - A t) :=
    mul_le_mul_of_nonneg_right (by linarith) hτ0
  linarith

/-- **Quasi-optimality of matrix DLRA along a curve of critical points, constants that depend on
time.** Let `F` be `L`-Lipschitz, `A` a solution of `Ȧ = F(t, A)` on `[a, b]`, and `X` a
continuous curve of matrices of rank `r` with right derivatives and `P(X t) (A t - X t) = 0`. Let
`ρ` and `μ` be continuous on `[a, b]` with `‖X t - A t‖₂ < ρ t ≤ σ_{r-1}(X t)` and
`‖F(t, A t)‖ ≤ μ t`. If `Y = U S Vᵀ` solves `Ẏ = P(Y) F(t, Y)` and `‖Y a - X a‖ ≤ δ`, then with
`k = L + μ/ρ` and `τ s = ‖X s - A s‖₂`, for `t ∈ [a, b]`

  `‖Y t - X t‖ ≤ e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖X s - A s‖ + μ s / (ρ s - τ s) τ s) ds`. -/
theorem dlra_norm_sub_le_integral_exp_integral_of_specNorm_sub_lt {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ} {ρ μ : ℝ → ℝ}
    {a b L δ : ℝ} (hL : 0 ≤ L) (hF : IsLipschitzField F L) (hA : ODESolution F A a b)
    (hρc : ContinuousOn ρ (Icc a b)) (hμc : ContinuousOn μ (Icc a b))
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ t) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ t ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0)
    (hd : ∀ t ∈ Icc a b, Curvature.specNorm (X t - A t) < ρ t)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t x => tangentProj (U t) (V t) (F t x)) Y a b)
    (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp (∫ u in a..t, (L + μ u / ρ u)) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t, (L + μ u / ρ u)) *
          (L * ‖X s - A s‖ +
            μ s / (ρ s - Curvature.specNorm (X s - A s)) * Curvature.specNorm (X s - A s)) := by
  intro t0 ht0
  rcases eq_or_lt_of_le ht0.1 with h0 | hpos
  · subst h0
    simpa using hδ
  have hab : a < b := hpos.trans_le ht0.2
  have hρpos : ∀ u ∈ Icc a b, 0 < ρ u := fun u hu =>
    (Curvature.specNorm_nonneg _).trans_lt (hd u hu)
  obtain ⟨t₁, ht₁, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab.le) hρc
  have hρ₀ : ∀ u ∈ Icc a b, ρ t₁ ≤ ρ u := fun u hu => isMinOn_iff.1 hmin u hu
  have hIcc : Icc a t0 ⊆ Icc a b := Icc_subset_Icc_right ht0.2
  have hIco : ∀ s ∈ Ico a t0, s ∈ Ico a b := fun s hs => ⟨hs.1, hs.2.trans_le ht0.2⟩
  have hτc : ContinuousOn (fun s => Curvature.specNorm (X s - A s)) (Icc a b) :=
    Curvature.continuous_specNorm.comp_continuousOn (hXc.sub hA.cont)
  have hkOn : ContinuousOn (fun u => L + μ u / ρ u) (Icc a b) :=
    continuousOn_const.add (hμc.div hρc fun u hu => (hρpos u hu).ne')
  have hgOn : ContinuousOn (fun s => L * ‖X s - A s‖ +
      μ s / (ρ s - Curvature.specNorm (X s - A s)) * Curvature.specNorm (X s - A s))
      (Icc a b) :=
    (continuousOn_const.mul (hXc.sub hA.cont).norm).add
      ((hμc.div (hρc.sub hτc) fun u hu => (sub_pos.2 (hd u hu)).ne').mul hτc)
  obtain ⟨kc, hkc, hkeq⟩ : ∃ kc : ℝ → ℝ, Continuous kc ∧
      ∀ s ∈ Icc a b, kc s = L + μ s / ρ s :=
    ⟨fun s => L + μ (projIcc a b hab.le s) / ρ (projIcc a b hab.le s),
      hkOn.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        fun s => (projIcc a b hab.le s).2,
      fun s hs => by simp only [projIcc_of_mem _ hs]⟩
  obtain ⟨gc, hgc, hgeq⟩ : ∃ gc : ℝ → ℝ, Continuous gc ∧ ∀ s ∈ Icc a b, gc s =
      L * ‖X s - A s‖ +
        μ s / (ρ s - Curvature.specNorm (X s - A s)) * Curvature.specNorm (X s - A s) :=
    ⟨fun s => L * ‖X (projIcc a b hab.le s) - A (projIcc a b hab.le s)‖ +
        μ (projIcc a b hab.le s) / (ρ (projIcc a b hab.le s) -
          Curvature.specNorm (X (projIcc a b hab.le s) - A (projIcc a b hab.le s))) *
          Curvature.specNorm (X (projIcc a b hab.le s) - A (projIcc a b hab.le s)),
      hgOn.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        fun s => (projIcc a b hab.le s).2,
      fun s hs => by simp only [projIcc_of_mem _ hs]⟩
  have hP : ∀ s ∈ Icc a b,
      IsOrthProj (tangentProj (U s) (V s) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
    fun s hs => isOrthProj_tangentProj (hUV s hs).1 (hUV s hs).2.1
  have hbound : ∀ s ∈ Ico a t0, ‖tangentProj (U s) (V s) (F s (Y s)) - X' s‖ ≤
      kc s * ‖Y s - X s‖ + gc s := fun s hs => by
    have hsb := hIco s hs
    have hsI := Ico_subset_Icc_self hsb
    obtain ⟨hU, hV, hYs⟩ := hUV s hsI
    have hρs := hρpos s hsI
    have hsub : Icc s b ⊆ Icc a b := Icc_subset_Icc_left hsb.1
    have hne : (𝓝[Icc s b \ {s}] s).NeBot := by
      rw [Icc_sdiff_left]
      exact left_nhdsWithin_Ioc_neBot hsb.2
    have hbest := norm_sub_tangentProjAt_le_div_sub_mul_specNorm
      ((hA.deriv s hsb).mono (Icc_subset_Ici_self : Icc s b ⊆ Ici s))
      ((hX s hsb).mono (Icc_subset_Ici_self : Icc s b ⊆ Ici s)) ⟨le_rfl, hsb.2.le⟩ hne
      (hρpos t₁ ht₁) (fun u hu => hXr u (hsub hu))
      (fun u hu => (hρ₀ u (hsub hu)).trans (hσ u (hsub hu))) (hσ s hsI)
      (fun u hu => hopt u (hsub hu)) (hμ s hsb) (hd s hsI)
    have hsplit : tangentProj (U s) (V s) (F s (Y s)) - X' s =
        tangentProj (U s) (V s) (F s (Y s) - F s (A s)) +
        (tangentProj (U s) (V s) (F s (A s)) - tangentProjAt (X s) (F s (A s))) -
        (X' s - tangentProjAt (X s) (F s (A s))) := by
      rw [map_sub]
      abel
    have e1 : ‖tangentProj (U s) (V s) (F s (Y s) - F s (A s))‖ ≤
        L * ‖Y s - X s‖ + L * ‖X s - A s‖ := by
      refine ((hP s hsI).norm_le _).trans ((hF s _ _).trans ?_)
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hL
      calc ‖Y s - A s‖ = ‖(Y s - X s) + (X s - A s)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖Y s - X s‖ + ‖X s - A s‖ := norm_add_le _ _
    have e2 : ‖tangentProj (U s) (V s) (F s (A s)) - tangentProjAt (X s) (F s (A s))‖ ≤
        μ s / ρ s * ‖Y s - X s‖ := by
      have h := norm_tangentProj_sub_tangentProjAt_le_inv_mul (hXr s hsI) hρs (hσ s hsI) hU hV
        (S s) (F s (A s))
      rw [← hYs] at h
      refine h.trans ?_
      calc (ρ s)⁻¹ * ‖Y s - X s‖ * ‖F s (A s)‖ ≤ (ρ s)⁻¹ * ‖Y s - X s‖ * μ s :=
            mul_le_mul_of_nonneg_left (hμ s hsb)
              (mul_nonneg (inv_nonneg.2 hρs.le) (norm_nonneg _))
        _ = μ s / ρ s * ‖Y s - X s‖ := by rw [div_eq_mul_inv]; ring
    rw [hsplit, hkeq s hsI, hgeq s hsI]
    calc _ ≤ ‖tangentProj (U s) (V s) (F s (Y s) - F s (A s))‖ +
          ‖tangentProj (U s) (V s) (F s (A s)) - tangentProjAt (X s) (F s (A s))‖ +
          ‖X' s - tangentProjAt (X s) (F s (A s))‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ L * ‖Y s - X s‖ + L * ‖X s - A s‖ + μ s / ρ s * ‖Y s - X s‖ +
          μ s / (ρ s - Curvature.specNorm (X s - A s)) * Curvature.specNorm (X s - A s) :=
          add_le_add (add_le_add e1 e2) hbest
      _ = _ := by ring
  have hcmp := norm_le_exp_integral_mul_add_integral_exp_integral_mul (f := fun t => Y t - X t)
    (f' := fun t => tangentProj (U t) (V t) (F t (Y t)) - X' t) (δ := δ) hkc hgc
    ((hY.cont.sub hXc).mono hIcc)
    (fun s hs => (hY.deriv s (hIco s hs)).sub (hX s (hIco s hs))) hδ hbound t0 ⟨ht0.1, le_rfl⟩
  have e1 : ∫ u in a..t0, kc u = ∫ u in a..t0, (L + μ u / ρ u) :=
    intervalIntegral.integral_congr fun u hu => by
      rw [uIcc_of_le ht0.1] at hu
      exact hkeq u (hIcc hu)
  have e2 : ∫ s in a..t0, Real.exp (∫ u in s..t0, kc u) * gc s =
      ∫ s in a..t0, Real.exp (∫ u in s..t0, (L + μ u / ρ u)) *
        (L * ‖X s - A s‖ +
          μ s / (ρ s - Curvature.specNorm (X s - A s)) * Curvature.specNorm (X s - A s)) :=
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le ht0.1] at hs
      have e3 : ∫ u in s..t0, kc u = ∫ u in s..t0, (L + μ u / ρ u) :=
        intervalIntegral.integral_congr fun u hu => by
          rw [uIcc_of_le hs.2] at hu
          exact hkeq u ⟨hs.1.trans hu.1, hu.2.trans ht0.2⟩
      change Real.exp (∫ u in s..t0, kc u) * gc s = _
      rw [e3, hgeq s (hIcc hs)]
  rw [e1, e2] at hcmp
  exact hcmp

/-- **Quasi-optimality for a DLRA solution of rank `r`, constants that depend on time.** The bound
of `dlra_norm_sub_le_integral_exp_integral_of_specNorm_sub_lt` for a DLRA solution `Y` of rank `r`
of `Ẏ = P(Y) F(t, Y)` (`IsDLRASolution`). -/
theorem IsDLRASolution.norm_sub_le_integral_exp_integral_of_specNorm_sub_lt {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ} {ρ μ : ℝ → ℝ}
    {a b L δ : ℝ} (hY : IsDLRASolution r F Y a b) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hA : ODESolution F A a b) (hρc : ContinuousOn ρ (Icc a b))
    (hμc : ContinuousOn μ (Icc a b)) (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ t)
    (hXc : ContinuousOn X (Icc a b)) (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = r)
    (hσ : ∀ t ∈ Icc a b, ρ t ≤ (toEuclideanLin (X t)).singularValues (r - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0)
    (hd : ∀ t ∈ Icc a b, Curvature.specNorm (X t - A t) < ρ t) (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp (∫ u in a..t, (L + μ u / ρ u)) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t, (L + μ u / ρ u)) *
          (L * ‖X s - A s‖ +
            μ s / (ρ s - Curvature.specNorm (X s - A s)) * Curvature.specNorm (X s - A s)) := by
  have hfac : ∀ t ∈ Icc a b, ∃ (U : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ)
      (V : Matrix n (Fin r) ℝ), Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ IsUnit S.det ∧ Y t = U * S * Vᵀ :=
    fun t ht => (SVD.rank_eq_iff_exists_factor (Y t)).1 (hY.2 t ht)
  choose! U S V hU hV hS hYeq using hfac
  have hY' : ODESolution (fun t x => tangentProj (U t) (V t) (F t x)) Y a b :=
    ⟨hY.1.cont, fun t ht => have ht' := Ico_subset_Icc_self ht
      DynamicallyOrthogonal.IsDLRASolution.hasDerivWithinAt_tangentProj hY ht (hU t ht')
        (hV t ht') (hS t ht') (hYeq t ht')⟩
  exact dlra_norm_sub_le_integral_exp_integral_of_specNorm_sub_lt hL hF hA hρc hμc hμ hXc hX hXr
    hσ hopt hd (fun t ht => ⟨hU t ht, hV t ht, hYeq t ht⟩) hY' hδ

/-- The singular value `σ_i` is a continuous function of the matrix. -/
private theorem continuous_singularValues (i : ℕ) :
    Continuous fun Z : Matrix m n ℝ => (toEuclideanLin Z).singularValues i :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun Z Z' => by
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
    exact WeylSingular.abs_singularValues_sub_le_frobenius Z Z' i).continuous

/-- **Quasi-optimality of matrix DLRA against the truncated SVD under a gap, constants that depend
on time.** Let `F` be `L`-Lipschitz, `A` a solution of `Ȧ = F(t, A)` on `[a, b]` with the gap
`σ_r(A t) < σ_{r-1}(A t)`, `μ` continuous with `‖F(t, A t)‖ ≤ μ t`, and `Y` a DLRA solution of
rank `r` with `‖Y a - T_r(A a)‖ ≤ δ`. Then with `k = L + μ/σ_{r-1}(A)`, for `t ∈ [a, b]`

  `‖Y t - T_r(A t)‖ ≤ e^{∫ₐᵗ k} δ +`
  `  ∫ₐᵗ e^{∫ₛᵗ k} (L ‖T_r(A s) - A s‖ + μ s / (σ_{r-1}(A s) - σ_r(A s)) σ_r(A s)) ds`.

No differentiability of the truncated SVD is assumed: it follows from the gap
(`EckartYoung.hasDerivWithinAt_truncation`). -/
theorem IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_singularValues_lt {r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A Y : ℝ → Matrix m n ℝ} {μ : ℝ → ℝ} {a b L δ : ℝ}
    (hY : IsDLRASolution r F Y a b) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hA : ODESolution F A a b) (hμc : ContinuousOn μ (Icc a b))
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ t)
    (hgap : ∀ t ∈ Icc a b, (toEuclideanLin (A t)).singularValues r <
      (toEuclideanLin (A t)).singularValues (r - 1))
    (hδ : ‖Y a - truncation (A a) r‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - truncation (A t) r‖ ≤
      Real.exp (∫ u in a..t, (L + μ u / (toEuclideanLin (A u)).singularValues (r - 1))) * δ +
        ∫ s in a..t,
          Real.exp (∫ u in s..t, (L + μ u / (toEuclideanLin (A u)).singularValues (r - 1))) *
          (L * ‖truncation (A s) r - A s‖ +
            μ s / ((toEuclideanLin (A s)).singularValues (r - 1) -
              (toEuclideanLin (A s)).singularValues r) *
              (toEuclideanLin (A s)).singularValues r) := by
  intro t ht
  have hr : 0 < r := Nat.pos_of_ne_zero fun h0 => by
    subst h0
    exact lt_irrefl _ (hgap a ⟨le_rfl, ht.1.trans ht.2⟩)
  have hσpos : ∀ s ∈ Icc a b, 0 < (toEuclideanLin (A s)).singularValues (r - 1) :=
    fun s hs => ((toEuclideanLin (A s)).singularValues_nonneg r).trans_lt (hgap s hs)
  have he : ∀ s, Curvature.specNorm (truncation (A s) r - A s) =
      (toEuclideanLin (A s)).singularValues r := fun s => by
    rw [Curvature.specNorm_sub_comm, specNorm_sub_truncation]
  have h := hY.norm_sub_le_integral_exp_integral_of_specNorm_sub_lt (A := A)
    (X := fun t => truncation (A t) r)
    (X' := fun t => fderiv ℝ (fun B => truncation B r) (A t) (F t (A t)))
    (ρ := fun t => (toEuclideanLin (A t)).singularValues (r - 1)) (μ := μ) hL hF hA
    ((continuous_singularValues (r - 1)).comp_continuousOn hA.cont) hμc hμ
    (fun s hs => (continuousAt_truncation (hgap s hs)).comp_continuousWithinAt (hA.cont s hs))
    (fun s hs => hasDerivWithinAt_truncation (hA.deriv s hs) (hgap s (Ico_subset_Icc_self hs)))
    (fun s hs => rank_truncation_of_le_singularValues (hσpos s hs) le_rfl)
    (fun s hs => le_singularValues_truncation hr (hσpos s hs) le_rfl)
    (fun s _ => tangentProjAt_truncation_sub_eq_zero _ _)
    (fun s hs => by
      rw [he s]
      exact hgap s hs) hδ t ht
  simp only [he] at h
  exact h

/-! ### The bound with uniform constants and the bound of Feppon and Lermusiaux -/

/-- `dlra_norm_sub_le_integral_of_specNorm_sub_le`, restated verbatim, follows from
`dlra_norm_sub_le_integral_exp_integral_of_specNorm_sub_lt` with constant `ρ` and `μ`: the margin
gives `μ τ / (ρ - τ) ≤ μ / ((1 - θ) ρ) τ`, and `e^{(L + μ/ρ)(t - s)} ≤ e^{(L + μ/ρ)(t - a)}`. -/
example {r : ℕ}
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
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0
    simpa using hδ
  have hab : a < b := hpos.trans_le ht.2
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ a ⟨le_rfl, hab⟩)
  have h1θ : 0 < (1 - θ) * ρ := mul_pos (by linarith) hρ
  have hK : 0 ≤ L + μ / ρ := add_nonneg hL (div_nonneg hμ0 hρ.le)
  have hIcc : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have key := dlra_norm_sub_le_integral_exp_integral_of_specNorm_sub_lt (ρ := fun _ => ρ)
    (μ := fun _ => μ) hL hF hA continuousOn_const continuousOn_const hμ hXc hX hXr hσ hopt
    (fun s hs => (hd s hs).trans_lt (by nlinarith)) hUV hY hδ t ht
  simp only [intervalIntegral.integral_const, smul_eq_mul] at key
  have hc1 : ContinuousOn (fun s => ‖X s - A s‖) (Icc a t) := ((hXc.sub hA.cont).mono hIcc).norm
  have hc2 : ContinuousOn (fun s => Curvature.specNorm (X s - A s)) (Icc a t) :=
    Curvature.continuous_specNorm.comp_continuousOn ((hXc.sub hA.cont).mono hIcc)
  have hle : ∫ s in a..t, Real.exp ((t - s) * (L + μ / ρ)) * (L * ‖X s - A s‖ +
      μ / (ρ - Curvature.specNorm (X s - A s)) * Curvature.specNorm (X s - A s)) ≤
      ∫ s in a..t, Real.exp ((L + μ / ρ) * (t - a)) * (L * ‖X s - A s‖ +
        μ / ((1 - θ) * ρ) * Curvature.specNorm (X s - A s)) := by
    refine intervalIntegral_le_of_nonneg_of_le ht.1
      (continuousOn_const.mul ((continuousOn_const.mul hc1).add (continuousOn_const.mul hc2)))
      (fun s hs => ?_) (fun s hs => ?_)
    · have hτ0 := Curvature.specNorm_nonneg (X s - A s)
      have hgap : 0 < ρ - Curvature.specNorm (X s - A s) := by
        have := hd s (hIcc hs)
        nlinarith
      exact mul_nonneg (Real.exp_pos _).le (add_nonneg (mul_nonneg hL (norm_nonneg _))
        (mul_nonneg (div_nonneg hμ0 hgap.le) hτ0))
    · have hτ0 := Curvature.specNorm_nonneg (X s - A s)
      have hgap : (1 - θ) * ρ ≤ ρ - Curvature.specNorm (X s - A s) := by
        have := hd s (hIcc hs)
        linarith
      have h1 : μ / (ρ - Curvature.specNorm (X s - A s)) ≤ μ / ((1 - θ) * ρ) :=
        div_le_div_of_nonneg_left hμ0 h1θ hgap
      have h2 : Real.exp ((t - s) * (L + μ / ρ)) ≤ Real.exp ((L + μ / ρ) * (t - a)) := by
        rw [Real.exp_le_exp, mul_comm]
        exact mul_le_mul_of_nonneg_left (by linarith [hs.1]) hK
      exact mul_le_mul h2 (add_le_add le_rfl (mul_le_mul_of_nonneg_right h1 hτ0))
        (add_nonneg (mul_nonneg hL (norm_nonneg _))
          (mul_nonneg (div_nonneg hμ0 (h1θ.trans_le hgap).le) hτ0)) (Real.exp_pos _).le
  have hJ : ∫ s in a..t, Real.exp ((L + μ / ρ) * (t - a)) * (L * ‖X s - A s‖ +
      μ / ((1 - θ) * ρ) * Curvature.specNorm (X s - A s)) =
      Real.exp ((L + μ / ρ) * (t - a)) * (L * (∫ s in a..t, ‖X s - A s‖) +
        μ / ((1 - θ) * ρ) * ∫ s in a..t, Curvature.specNorm (X s - A s)) := by
    have hi1 : IntervalIntegrable (fun s => L * ‖X s - A s‖) MeasureTheory.volume a t :=
      (continuousOn_const.mul hc1).intervalIntegrable_of_Icc ht.1
    have hi2 : IntervalIntegrable
        (fun s => μ / ((1 - θ) * ρ) * Curvature.specNorm (X s - A s)) MeasureTheory.volume a t :=
      (continuousOn_const.mul hc2).intervalIntegrable_of_Icc ht.1
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hJ] at hle
  rw [mul_comm (t - a)] at key
  have hsplit : Real.exp ((L + μ / ρ) * (t - a)) *
      (δ + L * (∫ s in a..t, ‖X s - A s‖) +
        μ / ((1 - θ) * ρ) * ∫ s in a..t, Curvature.specNorm (X s - A s)) =
      Real.exp ((L + μ / ρ) * (t - a)) * δ + Real.exp ((L + μ / ρ) * (t - a)) *
        (L * (∫ s in a..t, ‖X s - A s‖) +
          μ / ((1 - θ) * ρ) * ∫ s in a..t, Curvature.specNorm (X s - A s)) := by ring
  rw [hsplit]
  linarith

/-- **The bound of [FepponLermusiaux2018, Theorem 32] follows.** Let `F` be `L`-Lipschitz, `A` a
solution of `Ȧ = F(t, A)` with `t ↦ F(t, A t)` continuous and the gap `σ_r(A t) < σ_{r-1}(A t)`
on `[a, b]`, `Y` a DLRA solution of rank `r` with `Y a = T_r(A a)`, and
`L + 2 ‖F(t, A t)‖ / σ_{r-1}(A t) ≤ η` on `[a, b]`. Then

  `‖Y t - T_r(A t)‖ ≤ ∫ₐᵗ ‖A s - T_r(A s)‖ (L + ‖F(s, A s)‖ / (σ_{r-1}(A s) - σ_r(A s)))`
  `    e^{η (t - s)} ds`.

It follows from `IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_singularValues_lt`
with `μ t = ‖F(t, A t)‖` by `L + μ/σ_{r-1} ≤ η` and `σ_r(A s) ≤ ‖A s - T_r(A s)‖`. -/
example {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A Y : ℝ → Matrix m n ℝ} {a b L η : ℝ}
    (hY : IsDLRASolution r F Y a b) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hA : ODESolution F A a b) (hFc : ContinuousOn (fun t => F t (A t)) (Icc a b))
    (hgap : ∀ t ∈ Icc a b, (toEuclideanLin (A t)).singularValues r <
      (toEuclideanLin (A t)).singularValues (r - 1))
    (hη : ∀ t ∈ Icc a b,
      L + 2 * ‖F t (A t)‖ / (toEuclideanLin (A t)).singularValues (r - 1) ≤ η)
    (hY₀ : Y a = truncation (A a) r) :
    ∀ t ∈ Icc a b, ‖Y t - truncation (A t) r‖ ≤
      ∫ s in a..t, ‖A s - truncation (A s) r‖ *
        (L + ‖F s (A s)‖ / ((toEuclideanLin (A s)).singularValues (r - 1) -
          (toEuclideanLin (A s)).singularValues r)) * Real.exp (η * (t - s)) := by
  intro t ht
  have key := hY.norm_sub_truncation_le_integral_exp_integral_of_singularValues_lt
    (μ := fun t => ‖F t (A t)‖) (δ := 0) hL hF hA hFc.norm (fun _ _ => le_rfl) hgap
    (by rw [hY₀, sub_self, norm_zero]) t ht
  rw [mul_zero, zero_add] at key
  have hIcc : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hσpos : ∀ s ∈ Icc a b, 0 < (toEuclideanLin (A s)).singularValues (r - 1) :=
    fun s hs => ((toEuclideanLin (A s)).singularValues_nonneg r).trans_lt (hgap s hs)
  have hAc : ContinuousOn A (Icc a t) := hA.cont.mono hIcc
  have hTc : ContinuousOn (fun s => truncation (A s) r) (Icc a t) := fun s hs =>
    (continuousAt_truncation (hgap s (hIcc hs))).comp_continuousWithinAt (hAc s hs)
  have hcont : ContinuousOn (fun s => ‖A s - truncation (A s) r‖ *
      (L + ‖F s (A s)‖ / ((toEuclideanLin (A s)).singularValues (r - 1) -
        (toEuclideanLin (A s)).singularValues r)) * Real.exp (η * (t - s))) (Icc a t) :=
    ((hAc.sub hTc).norm.mul (continuousOn_const.add ((hFc.mono hIcc).norm.div
      (((continuous_singularValues (r - 1)).comp_continuousOn hAc).sub
        ((continuous_singularValues r).comp_continuousOn hAc))
      fun s hs => (sub_pos.2 (hgap s (hIcc hs))).ne'))).mul
      (Real.continuous_exp.comp (continuous_const.mul
        (continuous_const.sub continuous_id))).continuousOn
  refine key.trans (intervalIntegral_le_of_nonneg_of_le ht.1 hcont (fun s hs => ?_)
    (fun s hs => ?_))
  · exact mul_nonneg (Real.exp_pos _).le (add_nonneg (mul_nonneg hL (norm_nonneg _))
      (mul_nonneg (div_nonneg (norm_nonneg _) (sub_pos.2 (hgap s (hIcc hs))).le)
        ((toEuclideanLin (A s)).singularValues_nonneg r)))
  · have hsb := hIcc hs
    have hq : 0 ≤ ‖F s (A s)‖ / ((toEuclideanLin (A s)).singularValues (r - 1) -
        (toEuclideanLin (A s)).singularValues r) :=
      div_nonneg (norm_nonneg _) (sub_pos.2 (hgap s hsb)).le
    have hσle : (toEuclideanLin (A s)).singularValues r ≤ ‖A s - truncation (A s) r‖ := by
      rw [← specNorm_sub_truncation]
      exact Curvature.specNorm_le_frob _
    have hrate : ∫ u in s..t, (L + ‖F u (A u)‖ / (toEuclideanLin (A u)).singularValues (r - 1)) ≤
        η * (t - s) := by
      have h := intervalIntegral_le_of_nonneg_of_le (g := fun _ => η) hs.2 continuousOn_const
        (fun u hu => add_nonneg hL (div_nonneg (norm_nonneg (F u (A u)))
          (hσpos u ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩).le))
        (fun u hu => by
          have hub : u ∈ Icc a b := ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩
          have h1 : ‖F u (A u)‖ / (toEuclideanLin (A u)).singularValues (r - 1) ≤
              2 * ‖F u (A u)‖ / (toEuclideanLin (A u)).singularValues (r - 1) :=
            div_le_div_of_nonneg_right (by linarith [norm_nonneg (F u (A u))]) (hσpos u hub).le
          linarith [hη u hub])
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at h
      exact h
    have hsrc : L * ‖truncation (A s) r - A s‖ +
        ‖F s (A s)‖ / ((toEuclideanLin (A s)).singularValues (r - 1) -
          (toEuclideanLin (A s)).singularValues r) * (toEuclideanLin (A s)).singularValues r ≤
        ‖A s - truncation (A s) r‖ *
          (L + ‖F s (A s)‖ / ((toEuclideanLin (A s)).singularValues (r - 1) -
            (toEuclideanLin (A s)).singularValues r)) := by
      rw [norm_sub_rev (truncation (A s) r)]
      have := mul_le_mul_of_nonneg_left hσle hq
      linarith
    rw [mul_comm]
    exact mul_le_mul hsrc (Real.exp_le_exp.2 hrate) (Real.exp_pos _).le
      (mul_nonneg (norm_nonneg _) (add_nonneg hL hq))

end TimeLocal

/-! ### Examples -/

namespace QuasiOptimalityTimeLocalExamples

open scoped LeanDLRA.Frobenius
open QuasiOptimalityExamples

/-- The normal part `diag(0, 1/16)` of the examples. -/
local notation "N₁₆" => (!![0, 0; 0, 1 / 16] : Matrix (Fin 2) (Fin 2) ℝ)

private theorem hasDerivAt_smul_e₁_add_N₁₆ (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) (e₁ * e₁ᵀ) t := by
  simpa using (hasDerivAt_smul_e₁ 1 t).add_const N₁₆

/-- `σ₀(c e₁ e₁ᵀ) ≥ c` for `c > 0`. -/
private theorem le_singularValues_smul_e₁ {c : ℝ} (hc : 0 < c) :
    c ≤ (toEuclideanLin (c • (e₁ * e₁ᵀ))).singularValues (1 - 1) := by
  refine SVD.le_singularValues_of_eq_mul one_pos e₁_transpose_mul_self e₁_transpose_mul_self
    (smul_e₁_mul c) fun w => ?_
  rw [LinearEquiv.map_smul, toLpLin_one]
  change c * ‖w‖ ≤ ‖c • w‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]

/-- `X t = (1 + t) e₁ e₁ᵀ` is a DLRA solution of rank `1` for the field `F = e₁ e₁ᵀ`. -/
private theorem isDLRASolution_smul_e₁ :
    IsDLRASolution 1 (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ)
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) 0 1 := by
  refine ⟨⟨fun s _ => (hasDerivAt_smul_e₁ 1 s).continuousAt.continuousWithinAt,
    fun s hs => ?_⟩, fun t ht => rank_smul_e₁ (ne_of_gt (by linarith [ht.1]))⟩
  have h := (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt (s := Ici s)
  convert h using 1
  exact tangentProjAt_smul_e₁_apply (ne_of_gt (by linarith [hs.1]))

private theorem odeSolution_smul_e₁_add_N₁₆ :
    ODESolution (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => e₁ * e₁ᵀ)
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) 0 1 :=
  ⟨fun s _ => (hasDerivAt_smul_e₁_add_N₁₆ s).continuousAt.continuousWithinAt,
    fun s _ => (hasDerivAt_smul_e₁_add_N₁₆ s).hasDerivWithinAt⟩

/-- **Non-vacuity of `dlra_norm_sub_le_integral_exp_integral_of_specNorm_sub_lt` and of
`IsDLRASolution.norm_sub_le_integral_exp_integral_of_specNorm_sub_lt`**: for
`X t = Y t = (1 + t) e₁ e₁ᵀ` and `A t = X t + diag(0, 1/16) ≠ X t` on `[0, 1]`,
`F(t, Y) = e₁ e₁ᵀ` (`L = 0`), `r = 1`, the function `ρ t = 1 + t ≤ σ₀(X t)`, which is not
constant, `μ = 1` and `δ = 0` the hypotheses hold. -/
example : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(1 + t) • (e₁ * e₁ᵀ) - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
      Real.exp (∫ u in (0 : ℝ)..t, (0 + 1 / (1 + u))) * 0 +
        ∫ s in (0 : ℝ)..t, Real.exp (∫ u in s..t, (0 + 1 / (1 + u))) *
          (0 * ‖(1 + s) • (e₁ * e₁ᵀ) - ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)‖ +
            1 / ((1 + s) -
              Curvature.specNorm ((1 + s) • (e₁ * e₁ᵀ) - ((1 + s) • (e₁ * e₁ᵀ) + N₁₆))) *
              Curvature.specNorm ((1 + s) • (e₁ * e₁ᵀ) - ((1 + s) • (e₁ * e₁ᵀ) + N₁₆))) :=
  isDLRASolution_smul_e₁.norm_sub_le_integral_exp_integral_of_specNorm_sub_lt
    (A := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆)
    (X := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) (X' := fun _ => e₁ * e₁ᵀ)
    (ρ := fun u => 1 + u) (μ := fun _ => 1) le_rfl (fun _ _ _ => by simp)
    odeSolution_smul_e₁_add_N₁₆ (continuous_const.add continuous_id).continuousOn
    continuousOn_const (fun _ _ => norm_e₁_mul_le)
    (fun s _ => (hasDerivAt_smul_e₁ 1 s).continuousAt.continuousWithinAt)
    (fun s _ => (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt)
    (fun t ht => rank_smul_e₁ (ne_of_gt (by linarith [ht.1])))
    (fun t ht => le_singularValues_smul_e₁ (by linarith [ht.1]))
    (fun t ht => by
      have h := tangentProjAt_truncation_sub_eq_zero ((1 + t) • (e₁ * e₁ᵀ) + N₁₆) 1
      rwa [truncation_smul_e₁_add ht.1] at h)
    (fun t ht => ((Curvature.specNorm_le_frob _).trans (norm_smul_e₁_sub_add_le t)).trans_lt
      (by linarith [ht.1]))
    (by simp)

/-- **Non-vacuity of
`IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_singularValues_lt`** for `2 × 2`
matrices, `r = 1`, `A t = (1 + t) e₁ e₁ᵀ + diag(0, 1/16)` on `[0, 1]` and `F = e₁ e₁ᵀ`
(`L = 0`, `μ = 1`): the gap is `σ₁(A t) ≤ 1/16 < 1 ≤ σ₀(A t)`, and `T₁(A t) = (1 + t) e₁ e₁ᵀ`
differs from `A t` and is the DLRA solution `Y`. -/
example : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(1 + t) • (e₁ * e₁ᵀ) - EckartYoung.truncation ((1 + t) • (e₁ * e₁ᵀ) + N₁₆) 1‖ ≤
      Real.exp (∫ u in (0 : ℝ)..t,
        (0 + 1 / (toEuclideanLin ((1 + u) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1))) * 0 +
        ∫ s in (0 : ℝ)..t, Real.exp (∫ u in s..t,
          (0 + 1 / (toEuclideanLin ((1 + u) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1))) *
          (0 * ‖EckartYoung.truncation ((1 + s) • (e₁ * e₁ᵀ) + N₁₆) 1 -
              ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)‖ +
            1 / ((toEuclideanLin ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)).singularValues (1 - 1) -
              (toEuclideanLin ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)).singularValues 1) *
              (toEuclideanLin ((1 + s) • (e₁ * e₁ᵀ) + N₁₆)).singularValues 1) :=
  isDLRASolution_smul_e₁.norm_sub_truncation_le_integral_exp_integral_of_singularValues_lt
    (A := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) (μ := fun _ => 1) le_rfl
    (fun _ _ _ => by simp) odeSolution_smul_e₁_add_N₁₆ continuousOn_const
    (fun _ _ => norm_e₁_mul_le)
    (fun t ht => by
      have h1 : (toEuclideanLin ((1 + t) • (e₁ * e₁ᵀ) + N₁₆)).singularValues 1 ≤ 1 / 16 := by
        rw [← EckartYoung.specNorm_sub_truncation, truncation_smul_e₁_add ht.1,
          Curvature.specNorm_sub_comm]
        exact (Curvature.specNorm_le_frob _).trans (norm_smul_e₁_sub_add_le t)
      have h2 := one_le_singularValues_smul_e₁_add ht.1
      exact h1.trans_lt (lt_of_lt_of_le (by norm_num) h2))
    (by
      rw [truncation_smul_e₁_add le_rfl, sub_self, norm_zero])

end QuasiOptimalityTimeLocalExamples

end LeanDLRA
