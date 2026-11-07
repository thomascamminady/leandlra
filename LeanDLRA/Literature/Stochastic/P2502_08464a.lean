import Mathlib

/-!
# Results of arXiv 2502.08464: Dynamical variable separation for parametric dynamics

This module formalizes two results of arXiv 2502.08464 (Chen, Chen, Li, Zhou); see `wip/LIT.md`.

* `comparison_lemma` (Lemma A.1, comparison lemma). The paper assumes `α, β` integrable. Here they
  are continuous on `[0, T]`, `u` is continuous on `[0, T]` with derivative `u'` on `(0, T)`, and
  the differential inequality is assumed on `(0, T)` only. The conclusion is the paper's bound
  `u(t) ≤ ∫₀ᵗ α(s) e^{∫_s^t β} ds + e^{∫₀ᵗ β} u(0)` for all `t ∈ [0, T]`. The proof uses the
  integrating factor `u e^{-B}` with `B = ∫₀ᵗ β` and monotonicity of the difference.
* `backward_euler_zeta` (Eq. (4.5)). The backward-Euler discretization of the inner-product form
  (4.4) of the parameter-dependent ODE is the hypothesis `hdisc`. The theorem proves the explicit
  affine update `ζ_{k,n+1} = (c ζ_{k,n} + s)/l` with the paper's coefficients `c`, `s`, `l`. The
  hypothesis `l ≠ 0` is needed for the division and is not stated in the paper. The enrichment index
  `k` is 0-based, so the paper's previous indices `j = 1, …, k-1` are `j ∈ range k` here.

Not formalized: Algorithm 1 (the greedy offline stage). It is a procedure whose steps are
PDE solves, so it has no theorem to state. Proposition A.1 (the a posteriori bound
`‖e‖_V ≤ δ_k`) is also left out. It needs the local logarithmic Lipschitz constant on a
Hilbert space `V` and an energy argument with square roots.

The file uses no definitions from the core library. It works on `ℝ` and on a real inner
product space.
-/

open Set Filter Topology MeasureTheory

namespace LeanDLRA.Literature.P2502_08464

/-- The primitive `t ↦ ∫₀ᵗ f` of a function continuous on `[0, T]` is differentiable on `(0, T)`
with derivative `f t`. -/
theorem primitive_hasDerivAt {T : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 T)) {t : ℝ}
    (ht : t ∈ Ioo 0 T) : HasDerivAt (fun s => ∫ x in (0:ℝ)..s, f x) (f t) t := by
  have hsub : Ioo 0 T ⊆ Icc 0 T := Ioo_subset_Icc_self
  have h0 : (0:ℝ) ∈ Icc 0 T := ⟨le_rfl, by linarith [ht.1, ht.2]⟩
  have ht' : t ∈ Icc 0 T := hsub ht
  have hint : IntervalIntegrable f volume 0 t :=
    (hf.mono (uIcc_subset_Icc h0 ht')).intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter f (𝓝 t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hf.mono hsub) t ht
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas
    ((hf.mono hsub).continuousAt (Ioo_mem_nhds ht.1 ht.2))

/-- The primitive `t ↦ ∫₀ᵗ f` of a function continuous on `[0, T]` is continuous on `[0, T]`. -/
theorem primitive_continuousOn {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 T)) :
    ContinuousOn (fun t => ∫ x in (0:ℝ)..t, f x) (Icc 0 T) := by
  have hf' : IntegrableOn f (uIcc 0 T) volume := by
    rw [uIcc_of_le hT.le]
    exact hf.integrableOn_Icc
  have h := intervalIntegral.continuousOn_primitive_interval (a := 0) hf'
  rwa [uIcc_of_le hT.le] at h

/-- **Lemma A.1 (comparison lemma)** of arXiv 2502.08464, in the form used there.

If `u' ≤ β u + α` on `(0, T)`, then for all `t ∈ [0, T]`,
`u t ≤ ∫₀ᵗ α(s) exp(∫_s^t β) ds + exp(∫₀ᵗ β) u(0)`.

Differences from the paper: `α` and `β` are continuous on `[0, T]` instead of integrable, and the
differential inequality is required only on `(0, T)`; `u` is continuous on `[0, T]`. -/
theorem comparison_lemma {T : ℝ} (hT : 0 < T) {u u' α β : ℝ → ℝ}
    (hu : ContinuousOn u (Icc 0 T)) (hu' : ∀ t ∈ Ioo 0 T, HasDerivAt u (u' t) t)
    (hα : ContinuousOn α (Icc 0 T)) (hβ : ContinuousOn β (Icc 0 T))
    (hineq : ∀ t ∈ Ioo 0 T, u' t ≤ β t * u t + α t) :
    ∀ t ∈ Icc 0 T, u t ≤ (∫ s in (0:ℝ)..t, α s * Real.exp (∫ τ in s..t, β τ))
      + Real.exp (∫ τ in (0:ℝ)..t, β τ) * u 0 := by
  have h0 : (0:ℝ) ∈ Icc 0 T := left_mem_Icc.2 hT.le
  set B : ℝ → ℝ := fun t => ∫ x in (0:ℝ)..t, β x with hB_def
  have hBc : ContinuousOn B (Icc 0 T) := primitive_continuousOn hT hβ
  have hBd : ∀ t ∈ Ioo 0 T, HasDerivAt B (β t) t := fun t ht => primitive_hasDerivAt hβ ht
  set g : ℝ → ℝ := fun s => α s * Real.exp (-B s) with hg_def
  have hgc : ContinuousOn g (Icc 0 T) :=
    hα.mul (Real.continuous_exp.comp_continuousOn hBc.neg)
  have hGc : ContinuousOn (fun t => ∫ x in (0:ℝ)..t, g x) (Icc 0 T) :=
    primitive_continuousOn hT hgc
  have hGd : ∀ t ∈ Ioo 0 T, HasDerivAt (fun t => ∫ x in (0:ℝ)..t, g x) (g t) t :=
    fun t ht => primitive_hasDerivAt hgc ht
  set F : ℝ → ℝ := fun t => u t * Real.exp (-B t) - ∫ x in (0:ℝ)..t, g x with hF_def
  have hFc : ContinuousOn F (Icc 0 T) :=
    (hu.mul (Real.continuous_exp.comp_continuousOn hBc.neg)).sub hGc
  have hFd : ∀ t ∈ Ioo 0 T,
      HasDerivAt F ((u' t - β t * u t) * Real.exp (-B t) - g t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => u t * Real.exp (-B t))
        (u' t * Real.exp (-B t) + u t * (Real.exp (-B t) * (-β t))) t :=
      (hu' t ht).mul (hBd t ht).neg.exp
    exact (h1.sub (hGd t ht)).congr_deriv (by ring)
  have hanti : AntitoneOn F (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hFc
    · rw [interior_Icc]
      intro t ht
      exact (hFd t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hFd t ht).deriv]
      have hexp : 0 ≤ Real.exp (-B t) := (Real.exp_pos _).le
      have hle : u' t - β t * u t - α t ≤ 0 := by linarith [hineq t ht]
      have hrw : (u' t - β t * u t) * Real.exp (-B t) - g t
          = (u' t - β t * u t - α t) * Real.exp (-B t) := by
        simp only [hg_def]
        ring
      rw [hrw]
      exact mul_nonpos_iff.mpr (Or.inr ⟨hle, hexp⟩)
  have hF0 : F 0 = u 0 := by
    simp [hF_def, hB_def]
  intro t ht
  have ht0 : t ∈ Icc 0 T := ht
  have hFt : F t ≤ F 0 := hanti h0 ht0 ht.1
  have hineq' : u t * Real.exp (-B t) - ∫ x in (0:ℝ)..t, g x ≤ u 0 := by
    rw [← hF0]
    exact hFt
  -- exp(B t) * ∫₀ᵗ g = ∫₀ᵗ α(s) exp(∫_s^t β)
  have hkey : Real.exp (B t) * (∫ x in (0:ℝ)..t, g x)
      = ∫ s in (0:ℝ)..t, α s * Real.exp (∫ τ in s..t, β τ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc 0 T := uIcc_subset_Icc h0 ht0 hs
    have hab : IntervalIntegrable β volume 0 t :=
      (hβ.mono (uIcc_subset_Icc h0 ht0)).intervalIntegrable
    have hac : IntervalIntegrable β volume 0 s :=
      (hβ.mono (uIcc_subset_Icc h0 hs')).intervalIntegrable
    have hsplit : ∫ τ in s..t, β τ = B t - B s :=
      (intervalIntegral.integral_interval_sub_left hab hac).symm
    dsimp only [hg_def]
    rw [hsplit, show B t - B s = B t + -B s by ring, Real.exp_add]
    ring
  have hexp_mul : u t = Real.exp (B t) * (u t * Real.exp (-B t)) := by
    have h1 : Real.exp (B t) * Real.exp (-B t) = 1 := by
      rw [← Real.exp_add]
      simp
    linear_combination (-u t) * h1
  have hfin : u t ≤ Real.exp (B t) * (∫ x in (0:ℝ)..t, g x) + Real.exp (B t) * u 0 := by
    calc u t = Real.exp (B t) * (u t * Real.exp (-B t)) := hexp_mul
      _ ≤ Real.exp (B t) * ((∫ x in (0:ℝ)..t, g x) + u 0) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = Real.exp (B t) * (∫ x in (0:ℝ)..t, g x) + Real.exp (B t) * u 0 := by ring
  rw [hkey] at hfin
  exact hfin

/-- **Eq. (4.5)** of arXiv 2502.08464: the explicit backward-Euler update of the parameter-dependent
coefficient `ζ_{k,n+1}`.

Setting: a real inner product space `E`, time step `τ`, `NA` linear parts `A i` with coefficients
`κA i`, `NC` terms `C i` with coefficients `κC i` (the values at a fixed parameter `ξ`), vectors
`gN j = g_{j,n+1}`, `gO j = g_{j,n}`, scalars `zN j = ζ_{j,n+1}`, `zO j = ζ_{j,n}`; the current
enrichment index is `k` and the previous ones are `j ∈ range k`.

The hypothesis `hdisc` is the backward-Euler discretization of the inner-product form (4.4) (with
`(gk)_t ≈ (gk,n+1 - gk,n)/τ` and `(ζk)_t ≈ (ζk,n+1 - ζk,n)/τ`). The conclusion is
`ζ_{k,n+1} = (c ζ_{k,n} + s)/l` with the coefficients `c`, `s`, `l` of (4.5); they are named by the
equations `hc`, `hs`, `hl'`. The hypothesis `hl : l ≠ 0` is needed for the division; the paper
does not state it. -/
theorem backward_euler_zeta {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {NA NC : ℕ} (τ : ℝ) (A : Fin NA → E → E) (κA : Fin NA → ℝ) (C : Fin NC → E)
    (κC : Fin NC → ℝ) (gN gO : ℕ → E) (zN zO : ℕ → ℝ) (k : ℕ)
    (hdisc : inner ℝ (τ⁻¹ • (gN k - gO k)) (gN k) * zN k
        + inner ℝ (gN k) (gN k) * (τ⁻¹ * (zN k - zO k))
        - zN k * ∑ i, κA i * inner ℝ (A i (gN k)) (gN k)
      = ∑ i, ∑ j ∈ Finset.range k, κA i * zN j * inner ℝ (A i (gN j)) (gN k)
        + ∑ i, κC i * inner ℝ (C i) (gN k)
        - ∑ j ∈ Finset.range k, τ⁻¹ * (zN j - zO j) * inner ℝ (gN j) (gN k)
        - ∑ j ∈ Finset.range k, zN j * inner ℝ (τ⁻¹ • (gN j - gO j)) (gN k))
    (c s l : ℝ)
    (hc : c = inner ℝ (gN k) (gN k) * τ⁻¹)
    (hs : s = ∑ i, ∑ j ∈ Finset.range k, κA i * zN j * inner ℝ (A i (gN j)) (gN k)
        + ∑ i, κC i * inner ℝ (C i) (gN k)
        - ∑ j ∈ Finset.range k, τ⁻¹ * (zN j - zO j) * inner ℝ (gN j) (gN k)
        - ∑ j ∈ Finset.range k, zN j * inner ℝ (τ⁻¹ • (gN j - gO j)) (gN k))
    (hl' : l = 2 * c - inner ℝ (gO k) (gN k) * τ⁻¹ - ∑ i, κA i * inner ℝ (A i (gN k)) (gN k))
    (hl : l ≠ 0) :
    zN k = (c * zO k + s) / l := by
  subst hl' hs hc
  rw [eq_div_iff hl]
  simp only [real_inner_smul_left, inner_sub_left] at hdisc ⊢
  linear_combination hdisc

/-- Non-vacuity of `backward_euler_zeta`: one enrichment index in `ℝ`, `τ = 1`, `g = 1` at the new
time level, `g = 0` at the old one, `ζ = 0`; the hypotheses hold and the update gives `0`. -/
example : (0:ℝ) = (1 * 0 + 0) / 2 :=
  backward_euler_zeta (E := ℝ) (NA := 0) (NC := 0) (1:ℝ) (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (fun _ => (1:ℝ)) (fun _ => (0:ℝ)) (fun _ => (0:ℝ)) (fun _ => (0:ℝ)) 0
    (by simp) 1 0 2 (by simp) (by simp) (by simp) (by norm_num)

end LeanDLRA.Literature.P2502_08464
