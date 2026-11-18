import LeanDLRA.Integrators.Matrix.BUGQuasiOptimalityNormalStep
import LeanDLRA.Integrators.Matrix.BUGQuasiOptimalityTruncation

/-!
# Quasi-optimality of the BUG integrator with the normal velocity as growth rate

`norm_bugRun_sub_truncation_le` bounds the error of the fixed-rank BUG integrator of
[CerutiLubich2022] for given data `A(t)` against the truncated singular value decomposition
`T_r(A(t_n))` with the growth factor `e^{9/2 lam t_n}`, `lam = μ / (ρ - τ)`, in which `μ ≥ ‖Ȧ‖`
is the whole velocity of the data. In this file the growth rate is

  `K = 9/4 (ν + lam τ)/ρ + 5/2 lam (θ + 2 h lam)`,   `ν ≥ ‖(1 - P(T_r(A))) Ȧ‖`,

in which the velocity enters at first order only through its component normal to the manifold of
rank-`r` matrices at `T_r(A)`; the whole velocity is multiplied by the relative tail `τ/ρ`, by
the relative radius `θ ≤ 1/16` of a tube around `T_r(A)` that contains the iterates, or by the
step number `h lam`:

  `‖Y_n - T_r(A(t_n))‖ ≤ e^{K t_n} (‖Y_0 - T_r(A(0))‖ + 5/2 lam t_n τ)`,

as long as the right-hand side at the final time is at most `θ ρ`. Here `σ_r(A) ≤ τ < ρ ≤
σ_{r-1}(A)` (indices start at `0`) and `h lam ≤ 1/16`. All norms are Frobenius norms. This is the
discrete counterpart of
`IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_integral_lt` (growth rate
`ν/ρ + ν/(ρ - ε) + μ ε/ρ²`).

## Main results

* `EckartYoung.norm_sub_truncation_sub_sub_truncation_le_mul_sub`: the increment of the tail
  `A - T_r(A)` along a curve is at most `(ν + μ τ/(ρ - τ)) (b - a)`.
* `Exactness.IsBUGIncrementStep.norm_sub_truncation_le_of_norm_sub_tangentProjAt_le`: one step,
  `‖Y₁ - X₁‖ ≤ (1 + 9/4 (b - a) (ν + lam τ)/ρ + 5/2 η (θ + 2 η)) ‖Y₀ - X₀‖ + 9/4 η σ_r(A b)
      + 4/3 η² (σ_r(A a) + σ_r(A b))` with `η = (b - a) lam`.
* `norm_bugRun_sub_truncation_le_of_norm_sub_tangentProjAt_le`: `N` steps with constants of the
  steps.
* `norm_bugRun_sub_truncation_le_mul_of_norm_sub_tangentProjAt_le`: `N` steps with constants on
  `[0, N h]`.

## Implementation notes

The step is `MatrixBUG.norm_projStep_sub_le_of_trace_of_ginv_mul_norm_le` for the references
`T_r(A(t_k))`. The increment of the tail is the integral of `Ȧ - d/dt T_r(A)`, and
`Ȧ - d/dt T_r(A) = (1 - P(T_r(A))) Ȧ - (d/dt T_r(A) - P(T_r(A)) Ȧ)`: the normal velocity and the
defect of the truncation, which is at most `μ τ / (ρ - τ)`
(`norm_sub_tangentProjAt_le_div_one_sub_mul_specNorm`). The radius `θ` may depend on the step;
the smallness condition is on the bound or on the error itself.

## References

* [CerutiLubich2022]
-/

open Set Finset Matrix Filter
open scoped Topology LeanDLRA.Frobenius

namespace LeanDLRA

/-! ### The increment of the tail -/

section Reference

open EckartYoung Curvature

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- **The increment of the tail of the truncated singular value decomposition along a curve, in
the normal velocity.** Let `A` be continuous on `[a, b]` with right derivative `A'`, `‖A'‖ ≤ μ`,
`‖A' - P(T_r(A t)) A'‖ ≤ ν` for the tangent space projector `P` of the manifold of rank-`r`
matrices, and `σ_r(A t) ≤ τ < ρ ≤ σ_{r-1}(A t)` on `[a, b]` (indices start at `0`). Then the tail
`A - T_r(A)` satisfies
`‖(A b - T_r(A b)) - (A a - T_r(A a))‖ ≤ (ν + μ / (ρ - τ) τ) (b - a)`. -/
theorem EckartYoung.norm_sub_truncation_sub_sub_truncation_le_mul_sub {r : ℕ}
    {A A' : ℝ → Matrix m n ℝ} {a b ρ μ ν τ : ℝ} (hab : a ≤ b)
    (hAc : ContinuousOn A (Icc a b))
    (hA : ∀ t ∈ Ico a b, HasDerivWithinAt A (A' t) (Ici t) t)
    (hμ : ∀ t ∈ Ico a b, ‖A' t‖ ≤ μ)
    (hν : ∀ t ∈ Ico a b, ‖A' t - tangentProjAt (truncation (A t) r) (A' t)‖ ≤ ν)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1))
    (hτ : ∀ t ∈ Icc a b, (toEuclideanLin (A t)).singularValues r ≤ τ) (hτρ : τ < ρ) :
    ‖A b - truncation (A b) r - (A a - truncation (A a) r)‖ ≤
      (ν + μ / (ρ - τ) * τ) * (b - a) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hτ0 : 0 ≤ τ := ((toEuclideanLin (A a)).singularValues_nonneg r).trans (hτ a ha)
  have hρ : 0 < ρ := hτ0.trans_lt hτρ
  have hr : 0 < r := Nat.pos_of_ne_zero fun h0 => by
    subst h0
    have h1 := hσ a ha
    have h2 := hτ a ha
    simp only [Nat.zero_sub] at h1
    linarith
  have hθ : τ / ρ < 1 := (div_lt_one hρ).mpr hτρ
  have hθρ : τ / ρ * ρ = τ := div_mul_cancel₀ τ hρ.ne'
  have hgap : ∀ t ∈ Icc a b, (toEuclideanLin (A t)).singularValues r <
      (toEuclideanLin (A t)).singularValues (r - 1) :=
    fun t ht => (hτ t ht).trans_lt (hτρ.trans_le (hσ t ht))
  have hC : μ / ((1 - τ / ρ) * ρ) = μ / (ρ - τ) := by
    have h1 : (1 - τ / ρ) * ρ = ρ - τ := by rw [sub_mul, one_mul, hθρ]
    rw [h1]
  have hXc : ContinuousOn (fun t => truncation (A t) r) (Icc a b) := fun s hs =>
    (continuousAt_truncation (hgap s hs)).comp_continuousWithinAt (hAc s hs)
  have hX : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => truncation (A t) r)
      (fderiv ℝ (fun B => truncation B r) (A t) (A' t)) (Ici t) t := fun s hs =>
    hasDerivWithinAt_truncation (hA s hs) (hgap s (Ico_subset_Icc_self hs))
  have hb : ∀ t ∈ Ico a b,
      ‖A' t - fderiv ℝ (fun B => truncation B r) (A t) (A' t)‖ ≤ ν + μ / (ρ - τ) * τ := by
    intro t ht
    have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc_left ht.1
    have hts : t ∈ Icc t b := ⟨le_rfl, ht.2.le⟩
    have hs : (𝓝[Icc t b \ {t}] t).NeBot := by
      rw [Icc_sdiff_left]
      exact left_nhdsWithin_Ioc_neBot ht.2
    have hA' := (hA t ht).mono (Icc_subset_Ici_self : Icc t b ⊆ Ici t)
    have hX' := (hX t ht).mono (Icc_subset_Ici_self : Icc t b ⊆ Ici t)
    have hrank : ∀ u ∈ Icc t b, (truncation (A u) r).rank = r := fun u hu =>
      rank_truncation_of_le_singularValues hρ (hσ u (hsub hu))
    have hσ' : ∀ u ∈ Icc t b, ρ ≤ (toEuclideanLin (truncation (A u) r)).singularValues (r - 1) :=
      fun u hu => le_singularValues_truncation hr hρ (hσ u (hsub hu))
    have hopt : ∀ u ∈ Icc t b,
        tangentProjAt (truncation (A u) r) (A u - truncation (A u) r) = 0 :=
      fun u _ => tangentProjAt_truncation_sub_eq_zero _ _
    have hd : specNorm (truncation (A t) r - A t) ≤ τ / ρ * ρ := by
      rw [specNorm_sub_comm, specNorm_sub_truncation, hθρ]
      exact hτ t (hsub hts)
    have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ t ht)
    have b2 := norm_sub_tangentProjAt_le_div_one_sub_mul_specNorm hA' hX' hts hs hρ hrank hσ'
      hopt (hμ t ht) hθ hd
    have hq : 0 ≤ μ / ((1 - τ / ρ) * ρ) :=
      div_nonneg hμ0 (mul_nonneg (sub_pos.mpr hθ).le hρ.le)
    have hsp : specNorm (A t - truncation (A t) r) ≤ τ := by
      rw [specNorm_sub_truncation]
      exact hτ t (hsub hts)
    have b3 : ‖fderiv ℝ (fun B => truncation B r) (A t) (A' t) -
        tangentProjAt (truncation (A t) r) (A' t)‖ ≤ μ / (ρ - τ) * τ := by
      rw [← hC]
      exact b2.trans (mul_le_mul_of_nonneg_left hsp hq)
    have e : A' t - fderiv ℝ (fun B => truncation B r) (A t) (A' t) =
        A' t - tangentProjAt (truncation (A t) r) (A' t) -
          (fderiv ℝ (fun B => truncation B r) (A t) (A' t) -
            tangentProjAt (truncation (A t) r) (A' t)) := by abel
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add (hν t ht) b3)
  exact norm_image_sub_le_of_norm_deriv_right_le_segment
    (f := fun t => A t - truncation (A t) r) (hAc.sub hXc)
    (fun t ht => (hA t ht).sub (hX t ht)) hb b ⟨hab, le_rfl⟩

end Reference

/-! ### One step and the run -/

section Run

open EckartYoung Curvature MatrixBUG

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- **One BUG step for given data against the truncated singular value decomposition, with the
normal velocity in the growth factor.** Let `A` be continuous on `[a, b]`, `a < b`, with right
derivative `A'`, `‖A'‖ ≤ μ`, `‖A' - P(T_r(A t)) A'‖ ≤ ν` and
`σ_r(A t) ≤ τ < ρ ≤ σ_{r-1}(A t)` on `[a, b]` (indices start at `0`), and let
`lam ≥ μ / (ρ - τ)` with `η = (b - a) lam ≤ 1/16`. For a BUG step
`(U₀, S₀, V₀) ↦ (U₁, S₁, V₁)` with exact substeps for `F(t, Y) = Ȧ(t)` from `t = a` to `t = b`,
bases with `r` orthonormal columns and `‖Y₀ - T_r(A a)‖ ≤ θ ρ`, `θ ≤ 1/16`,

  `‖Y₁ - T_r(A b)‖ ≤ (1 + 9/4 (b - a) (ν + lam τ)/ρ + 5/2 η (θ + 2 η)) ‖Y₀ - T_r(A a)‖
      + 9/4 η σ_r(A b) + 4/3 η² (σ_r(A a) + σ_r(A b))`. -/
theorem Exactness.IsBUGIncrementStep.norm_sub_truncation_le_of_norm_sub_tangentProjAt_le
    {r : ℕ} {A A' : ℝ → Matrix m n ℝ} {a b ρ μ ν τ lam θ : ℝ} {U₀ U₁ : Matrix m (Fin r) ℝ}
    {S₀ S₁ : Matrix (Fin r) (Fin r) ℝ} {V₀ V₁ : Matrix n (Fin r) ℝ}
    (hs : Exactness.IsBUGIncrementStep (A a) (A b) U₀ S₀ V₀ U₁ S₁ V₁) (hab : a < b)
    (hAc : ContinuousOn A (Icc a b))
    (hA : ∀ t ∈ Ico a b, HasDerivWithinAt A (A' t) (Ici t) t)
    (hμ : ∀ t ∈ Ico a b, ‖A' t‖ ≤ μ)
    (hν : ∀ t ∈ Ico a b, ‖A' t - tangentProjAt (truncation (A t) r) (A' t)‖ ≤ ν)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1))
    (hτ : ∀ t ∈ Icc a b, (toEuclideanLin (A t)).singularValues r ≤ τ) (hτρ : τ < ρ)
    (hlam : μ ≤ lam * (ρ - τ)) (hstep : (b - a) * lam ≤ 1 / 16)
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1)
    (he : ‖U₀ * S₀ * V₀ᵀ - truncation (A a) r‖ ≤ θ * ρ) (hθ : θ ≤ 1 / 16) :
    ‖U₁ * S₁ * V₁ᵀ - truncation (A b) r‖ ≤
      (1 + 9 / 4 * ((b - a) * ((ν + lam * τ) / ρ)) +
          5 / 2 * ((b - a) * lam) * (θ + 2 * ((b - a) * lam))) *
          ‖U₀ * S₀ * V₀ᵀ - truncation (A a) r‖ +
        9 / 4 * ((b - a) * lam) * (toEuclideanLin (A b)).singularValues r +
        4 / 3 * ((b - a) * lam) ^ 2 * ((toEuclideanLin (A a)).singularValues r +
          (toEuclideanLin (A b)).singularValues r) := by
  classical
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hτ0 : 0 ≤ τ := ((toEuclideanLin (A a)).singularValues_nonneg r).trans (hτ a ha)
  have hρ : 0 < ρ := hτ0.trans_lt hτρ
  have hgap : 0 < ρ - τ := sub_pos.mpr hτρ
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ a ⟨le_rfl, hab⟩)
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab.le
  obtain ⟨G₀, hX₀, hc₀, hr₀, hRG₀, hGR₀, hG₀, htc₀, htr₀⟩ :=
    exists_ginv_truncation (r := r) hρ (hσ a ha)
  obtain ⟨G₁, hX₁, hc₁, hr₁, hRG₁, hGR₁, hG₁, -, -⟩ :=
    exists_ginv_truncation (r := r) hρ (hσ b hb)
  obtain ⟨hinc, -⟩ := norm_truncation_sub_truncation_le_mul_sub hab.le hAc hA hμ hσ hτ hτρ
  have htail := norm_sub_truncation_sub_sub_truncation_le_mul_sub hab.le hAc hA hμ hν hσ hτ hτρ
  have hAinc : ‖A b - A a‖ ≤ μ * (b - a) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment hAc hA hμ b hb
  have hq : μ / (ρ - τ) ≤ lam := (div_le_iff₀ hgap).mpr hlam
  have hinv : ρ⁻¹ * (ρ * (μ / (ρ - τ)) * (b - a)) ≤ (b - a) * lam := by
    have e : ρ⁻¹ * (ρ * (μ / (ρ - τ)) * (b - a)) = (b - a) * (μ / (ρ - τ)) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hq hba
  have hρi : 0 ≤ ρ⁻¹ := (inv_pos.mpr hρ).le
  have hξ : ρ⁻¹ * ‖truncation (A b) r - truncation (A a) r‖ ≤ (b - a) * lam :=
    (mul_le_mul_of_nonneg_left hinc hρi).trans hinv
  have hδ : ρ⁻¹ * specNorm (A b - truncation (A b) r - (A a - truncation (A a) r)) ≤
      (b - a) * ((ν + lam * τ) / ρ) := by
    have h1 : (ν + μ / (ρ - τ) * τ) * (b - a) ≤ (ν + lam * τ) * (b - a) :=
      mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hq hτ0]) hba
    have h2 := mul_le_mul_of_nonneg_left (((specNorm_le_frob _).trans htail).trans h1) hρi
    have e : ρ⁻¹ * ((ν + lam * τ) * (b - a)) = (b - a) * ((ν + lam * τ) / ρ) := by
      field_simp
    rwa [e] at h2
  have hν' : ρ⁻¹ * ‖A b - A a‖ ≤ (b - a) * lam := by
    have h1 : μ ≤ lam * ρ := hlam.trans (by nlinarith)
    have h2 : ρ⁻¹ * (μ * (b - a)) ≤ (b - a) * lam := by
      have e : ρ⁻¹ * (μ * (b - a)) = (b - a) * (μ / ρ) := by field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hρ).mpr h1) hba
    exact (mul_le_mul_of_nonneg_left hAinc hρi).trans h2
  have he' : ρ⁻¹ * ‖U₀ * S₀ * V₀ᵀ - truncation (A a) r‖ ≤ θ := by
    have := mul_le_mul_of_nonneg_left he hρi
    have e : ρ⁻¹ * (θ * ρ) = θ := by field_simp
    linarith
  have htrU : ∀ {W : Matrix m (Fin r) ℝ}, Wᵀ * W = 1 → trace (W * Wᵀ) = (r : ℝ) := fun hW => by
    rw [trace_mul_transpose hW, Fintype.card_fin]
  have htrV : ∀ {W : Matrix n (Fin r) ℝ}, Wᵀ * W = 1 → trace (W * Wᵀ) = (r : ℝ) := fun hW => by
    rw [trace_mul_transpose hW, Fintype.card_fin]
  have h := norm_projStep_sub_le_of_trace_of_ginv_mul_norm_le (isOrthProjMat_mul_transpose hU₁)
    (isOrthProjMat_mul_transpose hV₁) (isOrthProjMat_mul_transpose hU₀)
    (isOrthProjMat_mul_transpose hV₀) (colProj_mul_factor hU₀) (factor_mul_rowProj hV₀)
    (hs.proj_capK hV₀) (hs.proj_capL hU₀) hX₀ hc₀ hr₀ hX₁ hc₁ hr₁ hRG₀ hGR₀ hRG₁ hGR₁
    ((htrU hU₁).trans (htrU hU₀).symm) ((htrV hV₁).trans (htrV hV₀).symm)
    ((htrU hU₀).trans htc₀.symm) ((htrV hV₀).trans htr₀.symm) hG₀ hG₁
    ((mul_le_mul_of_nonneg_left (specNorm_le_frob _) hρi).trans hξ) hδ hξ hν' le_rfl hstep he'
    hθ (specNorm_sub_truncation (A b) r).le
  rw [← hs.eq_proj_mul] at h
  have hΔ : specNorm (A b - truncation (A b) r - (A a - truncation (A a) r)) ≤
      (toEuclideanLin (A a)).singularValues r + (toEuclideanLin (A b)).singularValues r := by
    have e : A b - truncation (A b) r - (A a - truncation (A a) r) =
        A b - truncation (A b) r + (truncation (A a) r - A a) := by abel
    have h1 := WeylSingular.specNorm_add_le (A b - truncation (A b) r) (truncation (A a) r - A a)
    rw [specNorm_sub_comm (truncation (A a) r) (A a), specNorm_sub_truncation,
      specNorm_sub_truncation] at h1
    rw [e]
    linarith
  have hη2 : 0 ≤ 4 / 3 * ((b - a) * lam) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hΔ hη2
  linarith

/-- One step of the recursion: `(1 + a) x + b ≤ e^{s + a} (c + b)` for `x ≤ e^s c`. -/
private theorem one_add_mul_add_le_exp_add_mul {s a c b x : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hc : 0 ≤ c) (hb : 0 ≤ b) (hx : x ≤ Real.exp s * c) :
    (1 + a) * x + b ≤ Real.exp (s + a) * (c + b) := by
  rw [Real.exp_add]
  have h1 : 1 + a ≤ Real.exp a := by linarith [Real.add_one_le_exp a]
  have h3 : (1 + a) * x ≤ (1 + a) * (Real.exp s * c) :=
    mul_le_mul_of_nonneg_left hx (by linarith)
  have h4 : (1 + a) * (Real.exp s * c) ≤ Real.exp a * (Real.exp s * c) :=
    mul_le_mul_of_nonneg_right h1 (mul_nonneg (Real.exp_pos s).le hc)
  have h5 : b ≤ Real.exp s * Real.exp a * b :=
    le_mul_of_one_le_left hb
      (one_le_mul_of_one_le_of_one_le (Real.one_le_exp hs) (Real.one_le_exp ha))
  calc (1 + a) * x + b
      ≤ Real.exp a * (Real.exp s * c) + Real.exp s * Real.exp a * b :=
        add_le_add (h3.trans h4) h5
    _ = Real.exp s * Real.exp a * (c + b) := by ring

omit [DecidableEq m] in
/-- **Quasi-optimality of the BUG integrator for given data with the normal velocity as growth
rate, with constants of the steps.** Let `A` be continuous on `[0, N h]` with right derivative
`A'`. On the `k`-th step `[k h, (k + 1) h]` let `‖A'‖ ≤ μ k`, `‖A' - P(T_r(A t)) A'‖ ≤ ν k` and
`σ_r(A t) ≤ τ k < ρ k ≤ σ_{r-1}(A t)` (indices start at `0`), and let
`lam k ≥ μ k / (ρ k - τ k)` with `h lam k ≤ 1/16` and `θ k ≤ 1/16`. Let `Y k = U k S k (V k)ᵀ`
be `N` steps of the BUG integrator of [CerutiLubich2022] with exact substeps for
`F(t, Y) = Ȧ(t)` and bases with `r` orthonormal columns. Then, with `X k = T_r(A (k h))`,
`s k = σ_r(A (k h))` and the rate

  `K j = 9/4 (ν j + lam j τ j) / ρ j + 5/2 lam j (θ j + 2 h lam j)`,

for `n ≤ N`

  `‖Y n - X n‖ ≤ e^{∑_{j<n} h K j} (‖Y 0 - X 0‖
      + ∑_{k<n} h lam k (9/4 s (k + 1) + 4/3 h lam k (s k + s (k + 1))))`,

provided that for `n < N` this bound or the error `‖Y n - X n‖` itself is at most `θ n ρ n`.
At first order in the step and in the radius `θ` the rate has the normal velocity `ν` and the
velocity times the relative tail only. -/
theorem norm_bugRun_sub_truncation_le_of_norm_sub_tangentProjAt_le {r N : ℕ}
    {A A' : ℝ → Matrix m n ℝ} {U : ℕ → Matrix m (Fin r) ℝ} {S : ℕ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℕ → Matrix n (Fin r) ℝ} {h : ℝ} {ρ μ ν τ lam θ : ℕ → ℝ} (hh : 0 < h)
    (hAc : ContinuousOn A (Icc 0 (N * h)))
    (hA : ∀ t ∈ Ico 0 (N * h), HasDerivWithinAt A (A' t) (Ici t) t)
    (hμ : ∀ k < N, ∀ t ∈ Ico (k * h) ((k + 1 : ℕ) * h), ‖A' t‖ ≤ μ k)
    (hν : ∀ k < N, ∀ t ∈ Ico (k * h) ((k + 1 : ℕ) * h),
      ‖A' t - tangentProjAt (truncation (A t) r) (A' t)‖ ≤ ν k)
    (hσ : ∀ k < N, ∀ t ∈ Icc (k * h) ((k + 1 : ℕ) * h),
      ρ k ≤ (toEuclideanLin (A t)).singularValues (r - 1))
    (hτ : ∀ k < N, ∀ t ∈ Icc (k * h) ((k + 1 : ℕ) * h),
      (toEuclideanLin (A t)).singularValues r ≤ τ k)
    (hτρ : ∀ k < N, τ k < ρ k) (hlam : ∀ k < N, μ k ≤ lam k * (ρ k - τ k))
    (hstep : ∀ k < N, h * lam k ≤ 1 / 16) (hθ : ∀ k < N, θ k ≤ 1 / 16)
    (hU : ∀ k ≤ N, (U k)ᵀ * U k = 1) (hV : ∀ k ≤ N, (V k)ᵀ * V k = 1)
    (hs : ∀ k < N, Exactness.IsBUGIncrementStep (A (k * h)) (A ((k + 1 : ℕ) * h)) (U k) (S k)
      (V k) (U (k + 1)) (S (k + 1)) (V (k + 1)))
    (htube : ∀ n < N, min
      (Real.exp (∑ j ∈ range n, h * (9 / 4 * ((ν j + lam j * τ j) / ρ j) +
          5 / 2 * lam j * (θ j + 2 * (h * lam j)))) *
        (‖U 0 * S 0 * (V 0)ᵀ - truncation (A 0) r‖ +
          ∑ k ∈ range n, h * lam k *
            (9 / 4 * (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r +
              4 / 3 * (h * lam k) * ((toEuclideanLin (A (k * h))).singularValues r +
                (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r))))
      ‖U n * S n * (V n)ᵀ - truncation (A (n * h)) r‖ ≤ θ n * ρ n) :
    ∀ n ≤ N, ‖U n * S n * (V n)ᵀ - truncation (A (n * h)) r‖ ≤
      Real.exp (∑ j ∈ range n, h * (9 / 4 * ((ν j + lam j * τ j) / ρ j) +
          5 / 2 * lam j * (θ j + 2 * (h * lam j)))) *
        (‖U 0 * S 0 * (V 0)ᵀ - truncation (A 0) r‖ +
          ∑ k ∈ range n, h * lam k *
            (9 / 4 * (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r +
              4 / 3 * (h * lam k) * ((toEuclideanLin (A (k * h))).singularValues r +
                (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r))) := by
  have hk0 : ∀ k : ℕ, (k : ℝ) * h < ((k + 1 : ℕ) : ℝ) * h := fun k => by
    push_cast
    linarith
  have hτ0 : ∀ k < N, 0 ≤ τ k := fun k hk =>
    ((toEuclideanLin (A (k * h))).singularValues_nonneg r).trans
      (hτ k hk _ ⟨le_rfl, (hk0 k).le⟩)
  have hρ0 : ∀ k < N, 0 < ρ k := fun k hk => (hτ0 k hk).trans_lt (hτρ k hk)
  have hν0 : ∀ k < N, 0 ≤ ν k := fun k hk =>
    (norm_nonneg _).trans (hν k hk _ ⟨le_rfl, hk0 k⟩)
  have hlam0 : ∀ k < N, 0 ≤ lam k := fun k hk => by
    have hμ0 : 0 ≤ μ k := (norm_nonneg _).trans (hμ k hk _ ⟨le_rfl, hk0 k⟩)
    exact nonneg_of_mul_nonneg_left (hμ0.trans (hlam k hk)) (sub_pos.mpr (hτρ k hk))
  have hterm : ∀ k < N, 0 ≤ h * lam k *
      (9 / 4 * (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r +
        4 / 3 * (h * lam k) * ((toEuclideanLin (A (k * h))).singularValues r +
          (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r)) := fun k hk => by
    have h1 := (toEuclideanLin (A (k * h))).singularValues_nonneg r
    have h2 := (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues_nonneg r
    have h3 := mul_nonneg hh.le (hlam0 k hk)
    positivity
  have hθ0 : ∀ k < N, 0 ≤ θ k := fun k hk => by
    have hB : 0 ≤ Real.exp (∑ j ∈ range k, h * (9 / 4 * ((ν j + lam j * τ j) / ρ j) +
          5 / 2 * lam j * (θ j + 2 * (h * lam j)))) *
        (‖U 0 * S 0 * (V 0)ᵀ - truncation (A 0) r‖ +
          ∑ i ∈ range k, h * lam i *
            (9 / 4 * (toEuclideanLin (A ((i + 1 : ℕ) * h))).singularValues r +
              4 / 3 * (h * lam i) * ((toEuclideanLin (A (i * h))).singularValues r +
                (toEuclideanLin (A ((i + 1 : ℕ) * h))).singularValues r))) :=
      mul_nonneg (Real.exp_pos _).le (add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i hi =>
        hterm i ((Finset.mem_range.mp hi).trans hk)))
    exact nonneg_of_mul_nonneg_left ((le_min hB (norm_nonneg _)).trans (htube k hk))
      (hρ0 k hk)
  have hκ0 : ∀ k < N, 0 ≤ h * (9 / 4 * ((ν k + lam k * τ k) / ρ k) +
      5 / 2 * lam k * (θ k + 2 * (h * lam k))) := fun k hk => by
    have h1 := hν0 k hk
    have h2 := hlam0 k hk
    have h3 := hτ0 k hk
    have h4 := (hρ0 k hk).le
    have h5 := hθ0 k hk
    have h6 := hh.le
    positivity
  intro n
  induction n with
  | zero =>
    intro _
    simp
  | succ n ih =>
    intro hn
    have hnN : n < N := hn
    have ihn := ih hnN.le
    have hen : ‖U n * S n * (V n)ᵀ - truncation (A (n * h)) r‖ ≤ θ n * ρ n :=
      (le_min ihn le_rfl).trans (htube n hnN)
    have hab : (n : ℝ) * h < ((n + 1 : ℕ) : ℝ) * h := hk0 n
    have hba : ((n + 1 : ℕ) : ℝ) * h - n * h = h := by
      push_cast
      ring
    have ha0 : (0 : ℝ) ≤ n * h := mul_nonneg (Nat.cast_nonneg n) hh.le
    have hbN : ((n + 1 : ℕ) : ℝ) * h ≤ N * h :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) hh.le
    have hstepn : (((n + 1 : ℕ) : ℝ) * h - n * h) * lam n ≤ 1 / 16 := by
      rw [hba]
      exact hstep n hnN
    have key := (hs n hnN).norm_sub_truncation_le_of_norm_sub_tangentProjAt_le hab
      (hAc.mono (Icc_subset_Icc ha0 hbN))
      (fun t ht => hA t ⟨ha0.trans ht.1, ht.2.trans_le hbN⟩) (hμ n hnN) (hν n hnN) (hσ n hnN)
      (hτ n hnN) (hτρ n hnN) (hlam n hnN) hstepn (hU n hnN.le) (hV n hnN.le) (hU (n + 1) hn)
      (hV (n + 1) hn) hen (hθ n hnN)
    rw [hba] at key
    have hs0 : 0 ≤ ∑ j ∈ range n, h * (9 / 4 * ((ν j + lam j * τ j) / ρ j) +
        5 / 2 * lam j * (θ j + 2 * (h * lam j))) :=
      Finset.sum_nonneg fun j hj => hκ0 j ((Finset.mem_range.mp hj).trans hnN)
    have hc0 : 0 ≤ ‖U 0 * S 0 * (V 0)ᵀ - truncation (A 0) r‖ +
        ∑ k ∈ range n, h * lam k *
          (9 / 4 * (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r +
            4 / 3 * (h * lam k) * ((toEuclideanLin (A (k * h))).singularValues r +
              (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r)) :=
      add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun k hk =>
        hterm k ((Finset.mem_range.mp hk).trans hnN))
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← add_assoc]
    refine le_trans ?_ (one_add_mul_add_le_exp_add_mul hs0 (hκ0 n hnN) hc0 (hterm n hnN) ihn)
    refine key.trans (le_of_eq ?_)
    ring

/-- The sum of the bound for constants that do not depend on the step and a tail of at most
`τ`: at most `5/2 lam (n h) τ`. -/
private theorem sum_mul_le_five_halves_mul {n : ℕ} {h lam τ : ℝ} {s : ℕ → ℝ} (hh : 0 ≤ h)
    (hlam : 0 ≤ lam) (hstep : h * lam ≤ 1 / 16) (hs0 : ∀ k, 0 ≤ s k)
    (hsτ : ∀ k ≤ n, s k ≤ τ) :
    ∑ k ∈ range n, h * lam * (9 / 4 * s (k + 1) + 4 / 3 * (h * lam) * (s k + s (k + 1))) ≤
      5 / 2 * lam * (n * h) * τ := by
  have hhl : 0 ≤ h * lam := mul_nonneg hh hlam
  have hterm : ∀ k ∈ range n,
      h * lam * (9 / 4 * s (k + 1) + 4 / 3 * (h * lam) * (s k + s (k + 1))) ≤
        h * lam * (5 / 2 * τ) := fun k hk => by
    have hk' := Finset.mem_range.mp hk
    have h1 := hsτ k hk'.le
    have h2 := hsτ (k + 1) hk'
    have h3 : 4 / 3 * (h * lam) * (s k + s (k + 1)) ≤ 4 / 3 * (1 / 16) * (s k + s (k + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (add_nonneg (hs0 k) (hs0 (k + 1)))
    exact mul_le_mul_of_nonneg_left (by linarith [hs0 k, hs0 (k + 1)]) hhl
  refine (Finset.sum_le_sum hterm).trans_eq ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

omit [DecidableEq m] in
/-- **Quasi-optimality of the BUG integrator for given data with the normal velocity as growth
rate.** Let `A` be continuous on `[0, T]`, `T = N h`, with right derivative `A'`, `‖A'‖ ≤ μ`,
`‖A' - P(T_r(A t)) A'‖ ≤ ν` and `σ_r(A t) ≤ τ < ρ ≤ σ_{r-1}(A t)` (indices start at `0`), and
let `lam = μ / (ρ - τ)` with `h lam ≤ 1/16` and `θ ≤ 1/16`. Let `Y k = U k S k (V k)ᵀ` be `N`
steps of the BUG integrator of [CerutiLubich2022] with exact substeps for `F(t, Y) = Ȧ(t)` and
bases with `r` orthonormal columns. With the rate

  `K = 9/4 (ν + lam τ) / ρ + 5/2 lam (θ + 2 h lam)`,

if `e^{K T} (‖Y 0 - T_r(A 0)‖ + 5/2 lam T τ) ≤ θ ρ`, then for `n ≤ N`

  `‖Y n - T_r(A (n h))‖ ≤ e^{K n h} (‖Y 0 - T_r(A 0)‖ + 5/2 lam n h τ)`.

`norm_bugRun_sub_truncation_le_mul_of_forall_le` has the rate `9/2 lam` in place of `K`. -/
theorem norm_bugRun_sub_truncation_le_mul_of_norm_sub_tangentProjAt_le {r N : ℕ}
    {A A' : ℝ → Matrix m n ℝ} {U : ℕ → Matrix m (Fin r) ℝ} {S : ℕ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℕ → Matrix n (Fin r) ℝ} {h ρ μ ν τ θ : ℝ} (hh : 0 < h)
    (hAc : ContinuousOn A (Icc 0 (N * h)))
    (hA : ∀ t ∈ Ico 0 (N * h), HasDerivWithinAt A (A' t) (Ici t) t)
    (hμ : ∀ t ∈ Ico 0 (N * h), ‖A' t‖ ≤ μ)
    (hν : ∀ t ∈ Ico 0 (N * h), ‖A' t - tangentProjAt (truncation (A t) r) (A' t)‖ ≤ ν)
    (hσ : ∀ t ∈ Icc 0 (N * h), ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1))
    (hτ : ∀ t ∈ Icc 0 (N * h), (toEuclideanLin (A t)).singularValues r ≤ τ) (hτρ : τ < ρ)
    (hstep : h * (μ / (ρ - τ)) ≤ 1 / 16) (hθ : θ ≤ 1 / 16)
    (hU : ∀ k ≤ N, (U k)ᵀ * U k = 1) (hV : ∀ k ≤ N, (V k)ᵀ * V k = 1)
    (hs : ∀ k < N, Exactness.IsBUGIncrementStep (A (k * h)) (A ((k + 1 : ℕ) * h)) (U k) (S k)
      (V k) (U (k + 1)) (S (k + 1)) (V (k + 1)))
    (htube : Real.exp ((9 / 4 * ((ν + μ / (ρ - τ) * τ) / ρ) +
        5 / 2 * (μ / (ρ - τ)) * (θ + 2 * (h * (μ / (ρ - τ))))) * (N * h)) *
      (‖U 0 * S 0 * (V 0)ᵀ - truncation (A 0) r‖ + 5 / 2 * (μ / (ρ - τ)) * (N * h) * τ) ≤
        θ * ρ) :
    ∀ n ≤ N, ‖U n * S n * (V n)ᵀ - truncation (A (n * h)) r‖ ≤
      Real.exp ((9 / 4 * ((ν + μ / (ρ - τ) * τ) / ρ) +
          5 / 2 * (μ / (ρ - τ)) * (θ + 2 * (h * (μ / (ρ - τ))))) * (n * h)) *
        (‖U 0 * S 0 * (V 0)ᵀ - truncation (A 0) r‖ + 5 / 2 * (μ / (ρ - τ)) * (n * h) * τ) := by
  intro n hn
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    obtain rfl : n = 0 := Nat.le_zero.mp hn
    simp
  have hgap : 0 < ρ - τ := sub_pos.mpr hτρ
  have hk0 : ∀ k : ℕ, (0 : ℝ) ≤ k * h := fun k => mul_nonneg (Nat.cast_nonneg k) hh.le
  have hkN : ∀ k : ℕ, k ≤ N → (k : ℝ) * h ≤ N * h := fun k hk =>
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hh.le
  have h0mem : (0 : ℝ) ∈ Ico 0 (N * h) := ⟨le_rfl, mul_pos (Nat.cast_pos.mpr hpos) hh⟩
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ 0 h0mem)
  have hν0 : 0 ≤ ν := (norm_nonneg _).trans (hν 0 h0mem)
  have hl : 0 ≤ μ / (ρ - τ) := div_nonneg hμ0 hgap.le
  have hτ0 : 0 ≤ τ := ((toEuclideanLin (A 0)).singularValues_nonneg r).trans
    (hτ 0 ⟨le_rfl, hk0 N⟩)
  have hρ : 0 < ρ := hτ0.trans_lt hτρ
  have hsrc0 : ∀ k : ℕ, 0 ≤ 5 / 2 * (μ / (ρ - τ)) * (k * h) * τ := fun k =>
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hl) (hk0 k)) hτ0
  have hθ0 : 0 ≤ θ :=
    nonneg_of_mul_nonneg_left ((mul_nonneg (Real.exp_pos _).le
      (add_nonneg (norm_nonneg _) (hsrc0 N))).trans htube) hρ
  have hK0 : 0 ≤ 9 / 4 * ((ν + μ / (ρ - τ) * τ) / ρ) +
      5 / 2 * (μ / (ρ - τ)) * (θ + 2 * (h * (μ / (ρ - τ)))) :=
    add_nonneg (mul_nonneg (by norm_num) (div_nonneg (add_nonneg hν0 (mul_nonneg hl hτ0)) hρ.le))
      (mul_nonneg (mul_nonneg (by norm_num) hl)
        (add_nonneg hθ0 (mul_nonneg (by norm_num) (mul_nonneg hh.le hl))))
  have hsτ : ∀ k ≤ N, (toEuclideanLin (A (k * h))).singularValues r ≤ τ := fun k hk =>
    hτ _ ⟨hk0 k, hkN k hk⟩
  have hsum : ∀ j ≤ N, ∑ k ∈ range j, h * (μ / (ρ - τ)) *
      (9 / 4 * (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r +
        4 / 3 * (h * (μ / (ρ - τ))) * ((toEuclideanLin (A (k * h))).singularValues r +
          (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r)) ≤
      5 / 2 * (μ / (ρ - τ)) * (j * h) * τ := fun j hj =>
    sum_mul_le_five_halves_mul (n := j) (s := fun k : ℕ =>
      (toEuclideanLin (A (k * h))).singularValues r) hh.le hl hstep
      (fun k => (toEuclideanLin (A (k * h))).singularValues_nonneg r)
      (fun k hk => hsτ k (hk.trans hj))
  have hsumκ : ∀ j : ℕ, ∑ _i ∈ range j, h * (9 / 4 * ((ν + μ / (ρ - τ) * τ) / ρ) +
      5 / 2 * (μ / (ρ - τ)) * (θ + 2 * (h * (μ / (ρ - τ))))) =
      (9 / 4 * ((ν + μ / (ρ - τ) * τ) / ρ) +
        5 / 2 * (μ / (ρ - τ)) * (θ + 2 * (h * (μ / (ρ - τ))))) * (j * h) := fun j => by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hc0 : ∀ j : ℕ, 0 ≤ ‖U 0 * S 0 * (V 0)ᵀ - truncation (A 0) r‖ +
      ∑ k ∈ range j, h * (μ / (ρ - τ)) *
        (9 / 4 * (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r +
          4 / 3 * (h * (μ / (ρ - τ))) * ((toEuclideanLin (A (k * h))).singularValues r +
            (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r)) := fun j =>
    add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun k _ => by
      have h1 := (toEuclideanLin (A (k * h))).singularValues_nonneg r
      have h2 := (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues_nonneg r
      have h3 := mul_nonneg hh.le hl
      positivity)
  refine ((norm_bugRun_sub_truncation_le_of_norm_sub_tangentProjAt_le (ρ := fun _ => ρ)
    (μ := fun _ => μ) (ν := fun _ => ν) (τ := fun _ => τ) (lam := fun _ => μ / (ρ - τ))
    (θ := fun _ => θ) hh hAc hA
    (fun k hk t ht => hμ t ⟨(hk0 k).trans ht.1, ht.2.trans_le (hkN (k + 1) hk)⟩)
    (fun k hk t ht => hν t ⟨(hk0 k).trans ht.1, ht.2.trans_le (hkN (k + 1) hk)⟩)
    (fun k hk t ht => hσ t ⟨(hk0 k).trans ht.1, ht.2.trans (hkN (k + 1) hk)⟩)
    (fun k hk t ht => hτ t ⟨(hk0 k).trans ht.1, ht.2.trans (hkN (k + 1) hk)⟩)
    (fun _ _ => hτρ) (fun _ _ => (div_mul_cancel₀ μ hgap.ne').ge) (fun _ _ => hstep)
    (fun _ _ => hθ) hU hV hs fun j hj => ?_) n hn).trans ?_
  · refine (min_le_left _ _).trans (le_trans ?_ htube)
    have hmono : 5 / 2 * (μ / (ρ - τ)) * (j * h) * τ ≤ 5 / 2 * (μ / (ρ - τ)) * (N * h) * τ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hkN j hj.le)
        (mul_nonneg (by norm_num) hl)) hτ0
    exact mul_le_mul (Real.exp_le_exp.mpr ((hsumκ j).le.trans
      (mul_le_mul_of_nonneg_left (hkN j hj.le) hK0)))
      (add_le_add le_rfl ((hsum j hj.le).trans hmono)) (hc0 j) (Real.exp_pos _).le
  · exact mul_le_mul (Real.exp_le_exp.mpr (hsumκ n).le) (add_le_add le_rfl (hsum n hn))
      (hc0 n) (Real.exp_pos _).le

end Run

/-! ### Examples -/

namespace BUGQuasiOptimalityNormalTruncationExamples

open scoped LeanDLRA.Frobenius
open QuasiOptimalityExamples EckartYoung BUGQuasiOptimalityTruncationExamples

/-- The tail `diag(0, 1/16)` of the example. -/
local notation "N₁₆" => (!![0, 0; 0, 1 / 16] : Matrix (Fin 2) (Fin 2) ℝ)

private theorem hasDerivAt_smul_e₁_add_N₁₆' (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) (e₁ * e₁ᵀ) t := by
  simpa using (hasDerivAt_smul_e₁ 1 t).add_const N₁₆

/-- **Non-vacuity of `norm_bugRun_sub_truncation_le_mul_of_norm_sub_tangentProjAt_le`** (and of
`norm_bugRun_sub_truncation_le_of_norm_sub_tangentProjAt_le`,
`Exactness.IsBUGIncrementStep.norm_sub_truncation_le_of_norm_sub_tangentProjAt_le`,
`MatrixBUG.norm_projStep_sub_le_of_trace_of_ginv_mul_norm_le` and the lemmas they use): one step
of size `h = 1/32` for the data `A(t) = (1 + t) e₁ e₁ᵀ + diag(0, 1/16)`, `r = 1`, `ρ = μ = 1`,
`τ = θ = 1/16`. The velocity `e₁ e₁ᵀ` is tangent at the reference `T₁(A(t)) = (1 + t) e₁ e₁ᵀ`, so
`ν = 0`, while the reference moves, the tail `diag(0, 1/16)` is not zero, and the iterates
`Y n = (101/100 + n h) e₁ e₁ᵀ` differ from the reference. -/
example : ∀ n : ℕ, n ≤ 1 →
    ‖e₁ * ((101 / 100 + (n : ℝ) * (1 / 32)) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * e₁ᵀ -
        truncation ((1 + (n : ℝ) * (1 / 32)) • (e₁ * e₁ᵀ) + N₁₆) 1‖ ≤
      Real.exp ((9 / 4 * ((0 + 1 / (1 - 1 / 16) * (1 / 16)) / 1) +
          5 / 2 * (1 / (1 - 1 / 16)) * (1 / 16 + 2 * (1 / 32 * (1 / (1 - 1 / 16))))) *
          (n * (1 / 32))) *
        (‖e₁ * ((101 / 100 + ((0 : ℕ) : ℝ) * (1 / 32)) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * e₁ᵀ -
            truncation ((1 + (0 : ℝ)) • (e₁ * e₁ᵀ) + N₁₆) 1‖ +
          5 / 2 * (1 / (1 - 1 / 16)) * (n * (1 / 32)) * (1 / 16)) := by
  have hY : ‖e₁ * ((101 / 100 + ((0 : ℕ) : ℝ) * (1 / 32)) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *
      e₁ᵀ - truncation ((1 + (0 : ℝ)) • (e₁ * e₁ᵀ) + N₁₆) 1‖ ≤ 1 / 100 := by
    have ha : ‖(101 / 100 + ((0 : ℕ) : ℝ) * (1 / 32)) - (1 + 0)‖ = 1 / 100 := by
      rw [Real.norm_eq_abs]
      norm_num
    rw [truncation_smul_e₁_add le_rfl, ← smul_e₁_mul, ← sub_smul, norm_smul, ha]
    nlinarith [norm_e₁_mul_le, norm_nonneg (e₁ * e₁ᵀ)]
  have hexp : Real.exp ((9 / 4 * ((0 + 1 / (1 - 1 / 16) * (1 / 16)) / 1) +
      5 / 2 * (1 / (1 - 1 / 16)) * (1 / 16 + 2 * (1 / 32 * (1 / (1 - 1 / 16))))) *
      (((1 : ℕ) : ℝ) * (1 / 32))) ≤ 2 := by
    have h1 := Real.add_one_le_exp (-((9 / 4 * ((0 + 1 / (1 - 1 / 16) * (1 / 16)) / 1) +
      5 / 2 * (1 / (1 - 1 / 16)) * (1 / 16 + 2 * (1 / 32 * (1 / (1 - 1 / 16))))) *
      (((1 : ℕ) : ℝ) * (1 / 32))))
    have h2 := Real.exp_pos ((9 / 4 * ((0 + 1 / (1 - 1 / 16) * (1 / 16)) / 1) +
      5 / 2 * (1 / (1 - 1 / 16)) * (1 / 16 + 2 * (1 / 32 * (1 / (1 - 1 / 16))))) *
      (((1 : ℕ) : ℝ) * (1 / 32)))
    have h3 : Real.exp ((9 / 4 * ((0 + 1 / (1 - 1 / 16) * (1 / 16)) / 1) +
        5 / 2 * (1 / (1 - 1 / 16)) * (1 / 16 + 2 * (1 / 32 * (1 / (1 - 1 / 16))))) *
        (((1 : ℕ) : ℝ) * (1 / 32))) *
        Real.exp (-((9 / 4 * ((0 + 1 / (1 - 1 / 16) * (1 / 16)) / 1) +
          5 / 2 * (1 / (1 - 1 / 16)) * (1 / 16 + 2 * (1 / 32 * (1 / (1 - 1 / 16))))) *
          (((1 : ℕ) : ℝ) * (1 / 32)))) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h4 : (1 : ℝ) / 2 ≤
        Real.exp (-((9 / 4 * ((0 + 1 / (1 - 1 / 16) * (1 / 16)) / 1) +
          5 / 2 * (1 / (1 - 1 / 16)) * (1 / 16 + 2 * (1 / 32 * (1 / (1 - 1 / 16))))) *
          (((1 : ℕ) : ℝ) * (1 / 32)))) := by
      refine le_trans ?_ h1
      norm_num
    nlinarith
  exact norm_bugRun_sub_truncation_le_mul_of_norm_sub_tangentProjAt_le (N := 1)
    (A := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) (A' := fun _ => e₁ * e₁ᵀ)
    (U := fun _ => e₁) (S := fun k : ℕ => (101 / 100 + (k : ℝ) * (1 / 32)) • 1)
    (V := fun _ => e₁) (h := 1 / 32) (ρ := 1) (μ := 1) (ν := 0) (τ := 1 / 16) (θ := 1 / 16)
    (by norm_num)
    (fun s _ => (hasDerivAt_smul_e₁_add_N₁₆' s).continuousAt.continuousWithinAt)
    (fun s _ => (hasDerivAt_smul_e₁_add_N₁₆' s).hasDerivWithinAt)
    (fun _ _ => norm_e₁_mul_le)
    (fun t ht => by
      have h1 : e₁ * e₁ᵀ - tangentProjAt (truncation ((1 + t) • (e₁ * e₁ᵀ) + N₁₆) 1)
          (e₁ * e₁ᵀ) = 0 := by
        rw [truncation_smul_e₁_add ht.1,
          tangentProjAt_smul_e₁_apply (by linarith [ht.1] : (1 + t) ≠ 0), sub_self]
      exact (congrArg (‖·‖) h1).trans norm_zero |>.le)
    (fun t ht => one_le_singularValues_smul_e₁_add ht.1)
    (fun t ht => by
      have h1 : (toEuclideanLin ((1 + t) • (e₁ * e₁ᵀ) + N₁₆)).singularValues 1 ≤ 1 / 16 := by
        rw [← specNorm_sub_truncation, truncation_smul_e₁_add ht.1,
          Curvature.specNorm_sub_comm]
        exact (Curvature.specNorm_le_frob _).trans (norm_smul_e₁_sub_add_le t)
      exact h1)
    (by norm_num) (by norm_num) (by norm_num) (fun _ _ => e₁_transpose_mul_self)
    (fun _ _ => e₁_transpose_mul_self)
    (fun k _ => by
      have h := isBUGIncrementStep_smul_e₁ (101 / 100 + (k : ℝ) * (1 / 32)) ((k : ℝ) * (1 / 32))
        (((k + 1 : ℕ) : ℝ) * (1 / 32))
      have e : 101 / 100 + (k : ℝ) * (1 / 32) +
          (((k + 1 : ℕ) : ℝ) * (1 / 32) - (k : ℝ) * (1 / 32)) =
          101 / 100 + ((k + 1 : ℕ) : ℝ) * (1 / 32) := by ring
      rw [e] at h
      exact h)
    (by
      calc Real.exp ((9 / 4 * ((0 + (1 : ℝ) / (1 - 1 / 16) * (1 / 16)) / 1) +
              5 / 2 * (1 / (1 - 1 / 16)) * (1 / 16 + 2 * (1 / 32 * (1 / (1 - 1 / 16))))) *
              (((1 : ℕ) : ℝ) * (1 / 32))) *
            (‖e₁ * ((101 / 100 + ((0 : ℕ) : ℝ) * (1 / 32)) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *
                e₁ᵀ - truncation ((1 + (0 : ℝ)) • (e₁ * e₁ᵀ) + N₁₆) 1‖ +
              5 / 2 * (1 / (1 - 1 / 16)) * (((1 : ℕ) : ℝ) * (1 / 32)) * (1 / 16))
          ≤ 2 * (1 / 100 + 5 / 2 * (1 / (1 - 1 / 16)) * (((1 : ℕ) : ℝ) * (1 / 32)) * (1 / 16)) :=
            mul_le_mul hexp (add_le_add hY le_rfl) (by positivity) (by norm_num)
        _ ≤ 1 / 16 * 1 := by norm_num)

end BUGQuasiOptimalityNormalTruncationExamples

end LeanDLRA
