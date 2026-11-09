import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.EulerBUG
import LeanDLRA.Foundations.OneSided
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.Projectors

/-!
# arXiv 2505.19929: Galerkin alternating projection for kinetic equations in the diffusive limit

This module formalises the GAP integrator of Ceruti, Crouseilles and Einkemmer and its diffusion
limit. Algorithm 2.3 is `IsGAPStep`, which is a BUG step with `P₁ = 1` (`IsGAPStep.isBUGStep`).
Lemma 3.2, Theorem 3.3 and Corollary 3.4 are already in the library (`normal_dist_lipschitz`,
`normal_dist_le_end`, `normal_dist_le_end_paper`, `gap_local_error`, `gap_global_error`) and are
not duplicated; `IsGAPStep.local_error` restates Theorem 3.3 for the bundled step. Theorems 4.1
and 4.2 are about the PDE (4.1), with the unbounded `∂ₓ`, which Mathlib cannot express at this
level; they are proved for the semi-discrete RTE (5.1) with exact substeps, the setting of Section
5, to which the paper says its asymptotic analysis extends: `rte` is (5.1) with an arbitrary
matrix `D` and any angular grid with the moments of `IsAngularQuad`, and `IsRTEGAPStep` is
Algorithm 2.3 for it (well defined by `exists_gapStep`). `rte_diffusion_limit` and `rte_tendsto`
are Theorem 4.1. **Theorem 4.2 is false as stated** in the semi-discrete setting of Section 5, to
which the paper says its asymptotic analysis applies (p. 14) (`theorem_4_2_false`): for the central
difference, three-point Gauss–Legendre, `r = 2` and a rank-two input, GAP converges to a
stationary state for `ε → 0`, not to the solution of the limit equation. (The printed Theorem 4.2
is for the PDE (4.1); the same construction with `X = span {cos x, 1}` applies there, but that
version is not formalized.) What is true, and what
the proof in the paper needs but does not state, is that the density of the L-step output and its
projected gradient are linearly independent; under this hypothesis `gap_ap_step`, `gap_ap_tendsto`
(one step, hypothesis on the limit of the L-step, `gap_indep_eventually`), `gap_step_estimate`
(one step, data depending on `ε`) and `gap_ap_run`, `gap_ap_run_tendsto` (a run) prove Theorem 4.2
with rate `ε`, and `gap_ap_nonvacuous` exhibits an instance. The published proof also uses
`V₁ ∝ 1`, `V₂ ∝ μ` exactly after deriving them up to `O(ε²)`; this is handled here: for `ε > 0`
the basis `V₁` contains `1, μ` only approximately, while the
K-step has the stiff term `ε⁻²`, so an error `δ` in `1 ∈ V₁` damps the density at rate `δ² / ε²`.
The fix is `lstep_capture`: `V₁` contains `1` up to `O(ε²)` and `μ` up to `O(ε)`, which needs the
slow-manifold estimate `IsRelaxSystem.flux_le` to second order in `ε`, and `kstep_estimate` shows
this suffices. The analysis is on an abstract two-scale system (`IsRelaxSystem`): an energy bound
(`IsRelaxSystem.apriori`, which holds for every Galerkin projector), and bounds for the micro
part, the flux and the macro part (`micro_le`, `flux_le`, `macro_le`), with the initial layer
treated explicitly, so no well-prepared data are needed and no CFL condition enters. Other
differences from the paper: the moment `⟨μ³⟩ = 0` used in its proof is not needed; `D` need not be
skew; the initial value of `ρ` is made explicit; the convergence in Theorem 4.1 holds for `t > t₀`
only, unless the input is isotropic; the factor `Δx` in the spatial inner product of Section 5 is
omitted (on a uniform grid it only rescales `X`). In `gap_ap_run` the independence is a hypothesis
at every step; that it propagates from step to step is not proved. Not treated: the PDE itself,
the time discretisation of the substeps in Section 5.2 and Remark 5.1, and the factor forms (5.3),
(5.4), which are equivalent to the projected forms used here by invariance (`relaxField_stay`).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2505_19929

open LeanDLRA

section Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Variation of constants for `y' = -lam y + f` with `‖f t‖ ≤ c e^{-lam (t-a)} + κ` (auxiliary for
Theorem 4.2 of arXiv 2505.19929). -/
theorem norm_le_of_decay {y f : ℝ → E} {a b lam c κ : ℝ} (hlam : 0 < lam) (hκ : 0 ≤ κ)
    (hcont : ContinuousOn y (Icc a b))
    (hy : ∀ t ∈ Ico a b, HasDerivWithinAt y (-lam • y t + f t) (Ici t) t)
    (hf : ∀ t ∈ Ico a b, ‖f t‖ ≤ c * Real.exp (-lam * (t - a)) + κ) :
    ∀ t ∈ Icc a b, ‖y t‖ ≤ Real.exp (-lam * (t - a)) * (‖y a‖ + c * (t - a)) + κ / lam := by
  set φ : ℝ → ℝ := fun t => Real.exp (lam * (t - a)) with hφ
  have hφd : ∀ t, HasDerivAt φ (lam * φ t) t := fun t => by
    have h : HasDerivAt (fun t => lam * (t - a)) lam t := by
      simpa using ((hasDerivAt_id t).sub_const a).const_mul lam
    simpa [hφ, mul_comm] using h.exp
  have hφpos : ∀ t, 0 < φ t := fun t => Real.exp_pos _
  have hφinv : ∀ t, φ t * Real.exp (-lam * (t - a)) = 1 := fun t => by
    simp only [hφ, ← Real.exp_add]; ring_nf; simp
  have hz : ContinuousOn (fun t => φ t • y t) (Icc a b) :=
    (continuous_iff_continuousAt.2 fun t => (hφd t).continuousAt).continuousOn.smul hcont
  have hz' : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => φ t • y t) (φ t • f t) (Ici t) t := by
    intro t ht
    have h := ((hφd t).hasDerivWithinAt (s := Ici t)).smul (hy t ht)
    convert h using 1
    module
  have hB : ∀ t, HasDerivAt (fun t => ‖y a‖ + c * (t - a) + κ / lam * (φ t - 1))
      (c + κ * φ t) t := fun t => by
    have h1 : HasDerivAt (fun t => c * (t - a)) c t := by
      simpa using ((hasDerivAt_id t).sub_const a).const_mul c
    have h2 := ((hφd t).sub_const 1).const_mul (κ / lam)
    have h3 := (h1.const_add ‖y a‖).add h2
    convert h3 using 1
    field_simp
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary hz hz'
    (B := fun t => ‖y a‖ + c * (t - a) + κ / lam * (φ t - 1)) (B' := fun t => c + κ * φ t)
    (by simp [hφ]) hB (fun t ht => by
      rw [norm_smul, Real.norm_of_nonneg (hφpos t).le]
      calc φ t * ‖f t‖ ≤ φ t * (c * Real.exp (-lam * (t - a)) + κ) :=
            mul_le_mul_of_nonneg_left (hf t ht) (hφpos t).le
        _ = c * (φ t * Real.exp (-lam * (t - a))) + κ * φ t := by ring
        _ = c + κ * φ t := by rw [hφinv, mul_one])
  intro t ht
  have h := key ht
  rw [norm_smul, Real.norm_of_nonneg (hφpos t).le] at h
  have hexp : 0 < Real.exp (-lam * (t - a)) := Real.exp_pos _
  have h2 := mul_le_mul_of_nonneg_left h hexp.le
  have h3 : Real.exp (-lam * (t - a)) * (φ t * ‖y t‖) = ‖y t‖ := by
    rw [← mul_assoc, mul_comm (Real.exp _), hφinv, one_mul]
  rw [h3] at h2
  have h4 : Real.exp (-lam * (t - a)) * (‖y a‖ + c * (t - a) + κ / lam * (φ t - 1))
      = Real.exp (-lam * (t - a)) * (‖y a‖ + c * (t - a))
        + κ / lam * (φ t * Real.exp (-lam * (t - a)) - Real.exp (-lam * (t - a))) := by ring
  rw [h4, hφinv] at h2
  have h5 : κ / lam * (1 - Real.exp (-lam * (t - a))) ≤ κ / lam := by
    have : 0 ≤ κ / lam := div_nonneg hκ hlam.le
    nlinarith
  linarith

/-- Grönwall with a layer forcing (auxiliary for Theorem 4.2 of arXiv 2505.19929): if
`e' = 𝓓 e + f`, `‖𝓓 x‖ ≤ β ‖x‖` and `‖f t‖ ≤ c e^{-lam (t-a)} + κ`, then
`‖e t‖ ≤ e^{β (t-a)} (‖e a‖ + c / lam + κ (t - a))`. -/
theorem norm_le_of_forced {e f : ℝ → E} {𝓓 : E →L[ℝ] E} {a b β c lam κ : ℝ} (hβ : 0 ≤ β)
    (h𝓓 : ∀ x, ‖𝓓 x‖ ≤ β * ‖x‖) (hlam : 0 < lam) (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (hcont : ContinuousOn e (Icc a b))
    (he : ∀ t ∈ Ico a b, HasDerivWithinAt e (𝓓 (e t) + f t) (Ici t) t)
    (hf : ∀ t ∈ Ico a b, ‖f t‖ ≤ c * Real.exp (-lam * (t - a)) + κ) :
    ∀ t ∈ Icc a b, ‖e t‖ ≤ Real.exp (β * (t - a)) * (‖e a‖ + c / lam + κ * (t - a)) := by
  intro t ht
  have hta : 0 ≤ t - a := sub_nonneg.2 ht.1
  refine le_of_forall_pos_le_add fun η hη => ?_
  set η' : ℝ := η / (Real.exp (β * (t - a)) * (t - a + 1)) with hη'
  have hexpp : 0 < Real.exp (β * (t - a)) := Real.exp_pos _
  have hη'pos : 0 < η' := by positivity
  set φ : ℝ → ℝ := fun s => Real.exp (β * (s - a)) with hφ
  have hφd : ∀ s, HasDerivAt φ (β * φ s) s := fun s => by
    have h : HasDerivAt (fun s => β * (s - a)) β s := by
      simpa using ((hasDerivAt_id s).sub_const a).const_mul β
    simpa [hφ, mul_comm] using h.exp
  set ψ : ℝ → ℝ := fun s => Real.exp (-lam * (s - a)) with hψ
  have hψd : ∀ s, HasDerivAt ψ (-lam * ψ s) s := fun s => by
    have h : HasDerivAt (fun s => -lam * (s - a)) (-lam) s := by
      simpa using ((hasDerivAt_id s).sub_const a).const_mul (-lam)
    simpa [hψ, mul_comm] using h.exp
  set I : ℝ → ℝ := fun s => ‖e a‖ + c / lam * (1 - ψ s) + (κ + η') * (s - a) with hI
  have hId : ∀ s, HasDerivAt I (c * ψ s + (κ + η')) s := fun s => by
    have h1 : HasDerivAt (fun s => (κ + η') * (s - a)) (κ + η') s := by
      simpa using ((hasDerivAt_id s).sub_const a).const_mul (κ + η')
    have h2 := (((hψd s).const_sub 1).const_mul (c / lam)).const_add ‖e a‖
    have h3 := h2.add h1
    convert h3 using 1
    field_simp
  have hBd : ∀ s, HasDerivAt (fun s => φ s * I s)
      (β * (φ s * I s) + φ s * (c * ψ s + (κ + η'))) s := fun s => by
    have h := (hφd s).mul (hId s)
    convert h using 1
    ring
  have hψpos : ∀ s, 0 < ψ s := fun s => Real.exp_pos _
  have hkey := image_norm_le_of_norm_deriv_right_lt_deriv_boundary' hcont he
    (B := fun s => φ s * I s) (B' := fun s => β * (φ s * I s) + φ s * (c * ψ s + (κ + η')))
    (by simp [hφ, hI, hψ])
    (continuous_iff_continuousAt.2 fun s => (hBd s).continuousAt).continuousOn
    (fun s _ => (hBd s).hasDerivWithinAt) (fun s hs hcontact => by
      have hφ1 : 1 ≤ φ s := Real.one_le_exp (mul_nonneg hβ (sub_nonneg.2 hs.1))
      have h1 : ‖𝓓 (e s) + f s‖ ≤ β * ‖e s‖ + (c * ψ s + κ) :=
        (norm_add_le _ _).trans (add_le_add (h𝓓 _) (hf s hs))
      rw [hcontact] at h1
      have h2 : 0 ≤ c * ψ s := mul_nonneg hc (hψpos s).le
      have h3 : c * ψ s + (κ + η') ≤ φ s * (c * ψ s + (κ + η')) := by
        nlinarith
      linarith)
  have h := hkey ht
  have hψle : 1 - ψ t ≤ 1 := by linarith [hψpos t]
  have hcl : 0 ≤ c / lam := div_nonneg hc hlam.le
  calc ‖e t‖ ≤ φ t * I t := h
    _ ≤ φ t * (‖e a‖ + c / lam + κ * (t - a) + η' * (t - a + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        simp only [hI]
        nlinarith
    _ = Real.exp (β * (t - a)) * (‖e a‖ + c / lam + κ * (t - a)) + η := by
        simp only [hφ]
        rw [mul_add, hη']
        field_simp

/-- The Galerkin-projected two-scale field `z ↦ R (-ε⁻¹ T z + ε⁻² (M z - z))`. -/
noncomputable def relaxField (M R T : E →L[ℝ] E) (ε : ℝ) : ℝ → E → E :=
  fun _ z => R (-(ε⁻¹ • T z) + (ε⁻¹ ^ 2) • (M z - z))

/-- A two-scale system: `M` is the projector onto the macroscopic states, `T` the transport with
`M T M = 0`, and `R` a Galerkin projector whose defects on the macroscopic states and on their
fluxes are measured by `δ` and `ν`. -/
structure IsRelaxSystem (M R T : E →L[ℝ] E) (τ δ ν : ℝ) : Prop where
  projM : IsOrthProj M
  projR : IsOrthProj R
  tau_nonneg : 0 ≤ τ
  delta_nonneg : 0 ≤ δ
  nu_nonneg : 0 ≤ ν
  normT : ∀ x, ‖T x‖ ≤ τ * ‖x‖
  balance : ∀ x, M (T (M x)) = 0
  defectM : ∀ x, ‖M x - R (M x)‖ ≤ δ * ‖x‖
  defectT : ∀ x, ‖T (M x) - R (T (M x))‖ ≤ ν * ‖x‖

section System

variable {M R T : E →L[ℝ] E} {τ δ ν ε a b : ℝ} {x : ℝ → E}

lemma relaxField_eq (t : ℝ) {z : E} (hz : R z = z) :
    relaxField M R T ε t z = -(ε⁻¹ • R (T z)) - (ε⁻¹ ^ 2) • (z - R (M z)) := by
  simp only [relaxField, map_add, map_neg, map_smul, map_sub, hz]
  module

/-- The Galerkin defect is self-adjoint: `‖M (x - R x)‖ ≤ δ ‖x‖`. -/
lemma IsRelaxSystem.defect_adj (hs : IsRelaxSystem M R T τ δ ν) (x : E) :
    ‖M (x - R x)‖ ≤ δ * ‖x‖ := by
  set w := M (x - R x) with hw
  have hMw : M w = w := hs.projM.idem _
  have h1 : ⟪w, w⟫ = ⟪w - R w, x⟫ := by
    calc ⟪w, w⟫ = ⟪w, M (x - R x)⟫ := by rw [hw]
      _ = ⟪M w, x - R x⟫ := (hs.projM.symm _ _).symm
      _ = ⟪w, x - R x⟫ := by rw [hMw]
      _ = ⟪w - R w, x⟫ := by rw [inner_sub_right, inner_sub_left, hs.projR.symm]
  have h2 : ‖w - R w‖ ≤ δ * ‖w‖ := by
    have := hs.defectM w
    rwa [hMw] at this
  have h3 : ‖w‖ ^ 2 ≤ δ * ‖x‖ * ‖w‖ := by
    rw [← real_inner_self_eq_norm_sq, h1]
    calc ⟪w - R w, x⟫ ≤ ‖w - R w‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ δ * ‖w‖ * ‖x‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = δ * ‖x‖ * ‖w‖ := by ring
  rcases (norm_nonneg w).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg hs.delta_nonneg (norm_nonneg _)
  · have : ‖w‖ * ‖w‖ ≤ (δ * ‖x‖) * ‖w‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos

/-- The second-order defect: `‖M (M x - R M x)‖ ≤ δ² ‖x‖`. -/
lemma IsRelaxSystem.defect_sq (hs : IsRelaxSystem M R T τ δ ν) (x : E) :
    ‖M (M x - R (M x))‖ ≤ δ ^ 2 * ‖x‖ := by
  set u := M x - R (M x) with hu
  have hRu : R u = 0 := by simp [hu, hs.projR.idem]
  have h1 := hs.defect_adj u
  rw [hRu, sub_zero] at h1
  calc ‖M u‖ ≤ δ * ‖u‖ := h1
    _ ≤ δ * (δ * ‖x‖) := mul_le_mul_of_nonneg_left (hs.defectM x) hs.delta_nonneg
    _ = δ ^ 2 * ‖x‖ := by ring

/-- The Galerkin space is invariant (arXiv 2505.19929, Lemma 2.1, for both substeps). -/
theorem relaxField_stay (hR : IsOrthProj R)
    (hsol : ODESolution (relaxField M R T ε) x a b) (h0 : R (x a) = x a) :
    ∀ t ∈ Icc a b, R (x t) = x t := by
  have hc : ContinuousOn (fun t => x t - R (x t)) (Icc a b) :=
    hsol.cont.sub (R.continuous.comp_continuousOn hsol.cont)
  have hd : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => x t - R (x t)) 0 (Ici t) t := by
    intro t ht
    have h1 := hsol.deriv t ht
    have h2 : HasDerivWithinAt (fun t => R (x t)) (R (relaxField M R T ε t (x t))) (Ici t) t :=
      R.hasFDerivAt.comp_hasDerivWithinAt t h1
    have h3 := h1.sub h2
    have h4 : relaxField M R T ε t (x t) - R (relaxField M R T ε t (x t)) = 0 := by
      simp [relaxField, hR.idem]
    rwa [h4] at h3
  intro t ht
  have := constant_of_has_deriv_right_zero hc hd t ht
  simp only [h0, sub_self] at this
  exact (sub_eq_zero.1 this).symm

/-- The energy inequality: `⟪F z, z⟫ ≤ 2 τ² ‖z‖²` on the Galerkin space, uniformly in small `ε`. -/
lemma IsRelaxSystem.inner_field_le (hs : IsRelaxSystem M R T τ δ ν) (hε : 0 < ε)
    (hετ : 2 * ε * τ ≤ 1) (t : ℝ) {z : E} (hz : R z = z) :
    ⟪relaxField M R T ε t z, z⟫ ≤ 2 * τ ^ 2 * ‖z‖ ^ 2 := by
  set c := ε⁻¹ with hc
  have hcpos : 0 < c := inv_pos.2 hε
  have hτ := hs.tau_nonneg
  have hεc : ε * c = 1 := mul_inv_cancel₀ hε.ne'
  have hτc : 2 * τ ≤ c := by
    have h : 2 * τ = c * (2 * ε * τ) := by
      calc 2 * τ = (ε * c) * (2 * τ) := by rw [hεc, one_mul]
        _ = _ := by ring
    rw [h]
    nlinarith
  set p := M z with hp
  set g := z - M z with hg
  have hzpg : z = p + g := by simp [hg, hp]
  have hTz : T z = T p + T g := by rw [← map_add, ← hzpg]
  have hpyth : ‖z‖ ^ 2 = ‖p‖ ^ 2 + ‖g‖ ^ 2 := (hs.projM.norm_sq_add z).symm
  have h0 : ⟪T p, p⟫ = 0 := by
    calc ⟪T p, p⟫ = ⟪T p, M z⟫ := rfl
      _ = ⟪M (T p), z⟫ := (hs.projM.symm _ _).symm
      _ = 0 := by rw [hp, hs.balance, inner_zero_left]
  have hgz : ⟪g, z⟫ = ‖g‖ ^ 2 := by
    have h1 : ⟪g, p⟫ = 0 := by
      rw [real_inner_comm]
      exact hs.projM.inner_sub_self z z
    calc ⟪g, z⟫ = ⟪g, p + g⟫ := by rw [← hzpg]
      _ = ‖g‖ ^ 2 := by rw [inner_add_right, h1, zero_add, real_inner_self_eq_norm_sq]
  have hexp : ⟪relaxField M R T ε t z, z⟫ = -(c * ⟪T z, z⟫) - c ^ 2 * ‖g‖ ^ 2 := by
    have h1 : ⟪relaxField M R T ε t z, z⟫ = ⟪-(c • T z) + (c ^ 2) • (M z - z), z⟫ := by
      simp only [relaxField]
      rw [hs.projR.symm, hz]
    have h2 : M z - z = -g := by simp [hg]
    rw [h1, h2, inner_add_left, inner_neg_left, inner_smul_left, inner_smul_left, inner_neg_left,
      hgz]
    simp
    ring
  have hupper : -⟪T z, z⟫ ≤ 2 * τ * ‖p‖ * ‖g‖ + τ * ‖g‖ ^ 2 := by
    have h1 : ⟪T z, z⟫ = ⟪T p, g⟫ + ⟪T g, p⟫ + ⟪T g, g⟫ := by
      have h5 : ⟪T z, z⟫ = ⟪T p + T g, p + g⟫ := by rw [← hTz, ← hzpg]
      rw [h5, inner_add_left, inner_add_right, inner_add_right, h0]
      ring
    have h2 : -⟪T p, g⟫ ≤ τ * ‖p‖ * ‖g‖ := by
      have := abs_real_inner_le_norm (T p) g
      have h3 := neg_abs_le ⟪T p, g⟫
      have h4 := mul_le_mul_of_nonneg_right (hs.normT p) (norm_nonneg g)
      linarith
    have h3 : -⟪T g, p⟫ ≤ τ * ‖p‖ * ‖g‖ := by
      have := abs_real_inner_le_norm (T g) p
      have h3 := neg_abs_le ⟪T g, p⟫
      have h4 := mul_le_mul_of_nonneg_right (hs.normT g) (norm_nonneg p)
      linarith
    have h4 : -⟪T g, g⟫ ≤ τ * ‖g‖ ^ 2 := by
      have := abs_real_inner_le_norm (T g) g
      have h3 := neg_abs_le ⟪T g, g⟫
      have h4 := mul_le_mul_of_nonneg_right (hs.normT g) (norm_nonneg g)
      nlinarith
    rw [h1]
    linarith
  rw [hexp, hpyth]
  have hb : 0 ≤ ‖g‖ ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hupper hcpos.le
  have h2 : c * (τ * ‖g‖ ^ 2) ≤ c ^ 2 * ‖g‖ ^ 2 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hτc (mul_nonneg hcpos.le hb)]
  nlinarith [sq_nonneg (c * ‖g‖ - 2 * τ * ‖p‖)]

/-- A priori bound, uniform in small `ε`: `‖x t‖ ≤ e^{2 τ² (t - a)} ‖x a‖` (auxiliary for
Theorem 4.2 of arXiv 2505.19929). -/
theorem IsRelaxSystem.apriori (hs : IsRelaxSystem M R T τ δ ν) (hε : 0 < ε)
    (hετ : 2 * ε * τ ≤ 1) (hsol : ODESolution (relaxField M R T ε) x a b)
    (h0 : R (x a) = x a) :
    ∀ t ∈ Icc a b, ‖x t‖ ≤ Real.exp (2 * τ ^ 2 * (t - a)) * ‖x a‖ := by
  have hzero : ODESolution (relaxField M R T ε) (fun _ => (0 : E)) a b :=
    ⟨continuousOn_const, fun t _ => by
      simpa [relaxField] using hasDerivWithinAt_const t (Ici t) (0 : E)⟩
  have hstay := relaxField_stay hs.projR hsol h0
  have h := hsol.norm_sub_le_exp_of_inner_le hzero (ℓ := 2 * τ ^ 2) (fun t ht => by
    have h1 := hs.inner_field_le hε hετ t (hstay t ⟨ht.1, ht.2.le⟩)
    have h2 : relaxField M R T ε t (0 : E) = 0 := by simp [relaxField]
    simpa [h2] using h1)
  simpa using h

/-- The micro equation `g' = -ε⁻² g + f`, with `g = z - M z`. -/
lemma micro_identity (hM : IsOrthProj M) (t : ℝ) {z : E} (hz : R z = z) :
    relaxField M R T ε t z - M (relaxField M R T ε t z) =
      -(ε⁻¹ ^ 2) • (z - M z) + (-(ε⁻¹ • (R (T z) - M (R (T z))))
        - (ε⁻¹ ^ 2) • ((M z - R (M z)) - M (M z - R (M z)))) := by
  rw [relaxField_eq t hz]
  simp only [map_sub, map_neg, map_smul, hM.idem]
  module

/-- The macro equation in terms of the micro part. -/
lemma macro_identity (hM : IsOrthProj M) (t : ℝ) {z : E} (hz : R z = z) :
    M (relaxField M R T ε t z) =
      -(ε⁻¹ • M (R (T z))) - (ε⁻¹ ^ 2) • M (M z - R (M z)) := by
  rw [relaxField_eq t hz]
  simp only [map_sub, map_neg, map_smul, hM.idem]

/-- The flux variable `y = g + ε T M z`: `y' = -ε⁻² y + f`. -/
lemma flux_identity (hs : IsRelaxSystem M R T τ δ ν) (hε : ε ≠ 0) (t : ℝ) {z : E}
    (hz : R z = z) :
    relaxField M R T ε t z - M (relaxField M R T ε t z)
        + ε • T (M (relaxField M R T ε t z)) =
      -(ε⁻¹ ^ 2) • (z - M z + ε • T (M z)) +
        (ε⁻¹ • ((T (M z) - R (T (M z))) - M (T (M z) - R (T (M z))))
          - ε⁻¹ • (R (T (z - M z)) - M (R (T (z - M z))))
          - (ε⁻¹ ^ 2) • ((M z - R (M z)) - M (M z - R (M z)))
          - T (M (R (T z))) - ε⁻¹ • T (M (M z - R (M z)))) := by
  have h1 : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε
  have h2 : ε * ε⁻¹ ^ 2 = ε⁻¹ := by rw [sq, ← mul_assoc, h1, one_mul]
  have h3 : ε⁻¹ ^ 2 * ε = ε⁻¹ := by rw [mul_comm, h2]
  have hbal : M (T (M z)) = 0 := hs.balance z
  rw [relaxField_eq t hz]
  simp only [map_sub, map_neg, map_smul, hs.projM.idem, hbal, smul_add, smul_sub, smul_neg,
    smul_smul, neg_mul, h1, h2, h3, one_smul, smul_zero]
  module

/-- The macro equation in closed form: `p' = 𝓓 p + f`. -/
lemma limit_identity (hs : IsRelaxSystem M R T τ δ ν) (hε : ε ≠ 0) (t : ℝ) {z : E}
    (hz : R z = z) :
    M (relaxField M R T ε t z) = M (T (T (M z))) +
      (-(ε⁻¹ • M (T (z - M z + ε • T (M z)))) + ε⁻¹ • M (T z - R (T z))
        - (ε⁻¹ ^ 2) • M (M z - R (M z))) := by
  have h1 : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε
  have hbal : M (T (M z)) = 0 := hs.balance z
  rw [macro_identity hs.projM t hz]
  simp only [map_sub, map_add, map_smul, hbal, smul_sub, smul_add, smul_smul, h1, one_smul,
    sub_zero]
  module

lemma hasDerivWithinAt_clm (L : E →L[ℝ] E) {y : ℝ → E} {v : E} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt y v s t) : HasDerivWithinAt (fun t => L (y t)) (L v) s t :=
  L.hasFDerivAt.comp_hasDerivWithinAt t h

lemma norm_smul_nonneg {c : ℝ} (hc : 0 ≤ c) (v : E) : ‖c • v‖ = c * ‖v‖ := by
  rw [norm_smul, Real.norm_of_nonneg hc]

/-- The micro bound `‖g t‖ ≤ e^{-(t-a)/ε²} ‖g a‖ + (ε τ + δ) C₀` (auxiliary for Theorem 4.2 of
arXiv 2505.19929; it makes `K_i = O(ε)`, `i ≥ 2`, of the proof rigorous). -/
theorem IsRelaxSystem.micro_le (hs : IsRelaxSystem M R T τ δ ν) (hε : 0 < ε)
    (hsol : ODESolution (relaxField M R T ε) x a b) (h0 : R (x a) = x a) {C₀ : ℝ}
    (hC : ∀ t ∈ Icc a b, ‖x t‖ ≤ C₀) :
    ∀ t ∈ Icc a b, ‖x t - M (x t)‖ ≤
      Real.exp (-(ε⁻¹ ^ 2) * (t - a)) * ‖x a - M (x a)‖ + (ε * τ + δ) * C₀ := by
  intro t ht
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans (hC t ht)
  have hstay := relaxField_stay hs.projR hsol h0
  have hc : 0 < ε⁻¹ := inv_pos.2 hε
  have hc2 : 0 < ε⁻¹ ^ 2 := by positivity
  have hτ := hs.tau_nonneg
  have hδ := hs.delta_nonneg
  have key := norm_le_of_decay (y := fun t => x t - M (x t)) (a := a) (b := b)
    (f := fun t => -(ε⁻¹ • (R (T (x t)) - M (R (T (x t)))))
        - (ε⁻¹ ^ 2) • ((M (x t) - R (M (x t))) - M (M (x t) - R (M (x t)))))
    (lam := ε⁻¹ ^ 2) (c := 0) (κ := (ε⁻¹ * τ + ε⁻¹ ^ 2 * δ) * C₀) hc2 (by positivity)
    (hsol.cont.sub (M.continuous.comp_continuousOn hsol.cont))
    (fun s hs' => by
      have h1 := hsol.deriv s hs'
      have h2 := h1.sub (hasDerivWithinAt_clm M h1)
      rwa [micro_identity hs.projM s (hstay s ⟨hs'.1, hs'.2.le⟩)] at h2)
    (fun s hs' => by
      have hs'' : s ∈ Icc a b := ⟨hs'.1, hs'.2.le⟩
      have hz := hC s hs''
      have h1 : ‖R (T (x s)) - M (R (T (x s)))‖ ≤ τ * C₀ :=
        calc _ ≤ ‖R (T (x s))‖ := hs.projM.norm_sub_le _
          _ ≤ ‖T (x s)‖ := hs.projR.norm_le _
          _ ≤ τ * ‖x s‖ := hs.normT _
          _ ≤ τ * C₀ := mul_le_mul_of_nonneg_left hz hτ
      have h2 : ‖(M (x s) - R (M (x s))) - M (M (x s) - R (M (x s)))‖ ≤ δ * C₀ :=
        calc _ ≤ ‖M (x s) - R (M (x s))‖ := hs.projM.norm_sub_le _
          _ ≤ δ * ‖x s‖ := hs.defectM _
          _ ≤ δ * C₀ := mul_le_mul_of_nonneg_left hz hδ
      calc _ ≤ ‖-(ε⁻¹ • (R (T (x s)) - M (R (T (x s)))))‖
            + ‖(ε⁻¹ ^ 2) • ((M (x s) - R (M (x s))) - M (M (x s) - R (M (x s))))‖ :=
            norm_sub_le _ _
        _ = ε⁻¹ * ‖R (T (x s)) - M (R (T (x s)))‖
            + ε⁻¹ ^ 2 * ‖(M (x s) - R (M (x s))) - M (M (x s) - R (M (x s)))‖ := by
            rw [norm_neg, norm_smul_nonneg hc.le, norm_smul_nonneg hc2.le]
        _ ≤ ε⁻¹ * (τ * C₀) + ε⁻¹ ^ 2 * (δ * C₀) := by gcongr
        _ = _ := by ring)
    t ht
  have hval : (ε⁻¹ * τ + ε⁻¹ ^ 2 * δ) * C₀ / ε⁻¹ ^ 2 = (ε * τ + δ) * C₀ := by
    field_simp
  rw [hval, zero_mul, add_zero] at key
  exact key

/-- The flux bound with the raw layer term (auxiliary for Theorem 4.2 of arXiv 2505.19929). -/
theorem IsRelaxSystem.flux_le_raw (hs : IsRelaxSystem M R T τ δ ν) (hε : 0 < ε)
    (hετ : 2 * ε * τ ≤ 1) (hsol : ODESolution (relaxField M R T ε) x a b)
    (h0 : R (x a) = x a) {C₀ : ℝ} (hC : ∀ t ∈ Icc a b, ‖x t‖ ≤ C₀) :
    ∀ t ∈ Icc a b, ‖x t - M (x t) + ε • T (M (x t))‖ ≤
      Real.exp (-(ε⁻¹ ^ 2) * (t - a)) * (‖x a - M (x a) + ε • T (M (x a))‖
        + ε⁻¹ * τ * ‖x a - M (x a)‖ * (t - a))
      + (ε * ν + 2 * τ ^ 2 * ε ^ 2 + 2 * δ) * C₀ := by
  intro t ht
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans (hC t ht)
  have hstay := relaxField_stay hs.projR hsol h0
  have hc : 0 < ε⁻¹ := inv_pos.2 hε
  have hc2 : 0 < ε⁻¹ ^ 2 := by positivity
  have hτ := hs.tau_nonneg
  have hδ := hs.delta_nonneg
  have hν := hs.nu_nonneg
  have hεc : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε.ne'
  have hmicro := hs.micro_le hε hsol h0 hC
  have key := norm_le_of_decay (y := fun t => x t - M (x t) + ε • T (M (x t))) (a := a) (b := b)
    (f := fun t => ε⁻¹ • ((T (M (x t)) - R (T (M (x t)))) - M (T (M (x t)) - R (T (M (x t)))))
          - ε⁻¹ • (R (T (x t - M (x t))) - M (R (T (x t - M (x t)))))
          - (ε⁻¹ ^ 2) • ((M (x t) - R (M (x t))) - M (M (x t) - R (M (x t))))
          - T (M (R (T (x t)))) - ε⁻¹ • T (M (M (x t) - R (M (x t)))))
    (lam := ε⁻¹ ^ 2) (c := ε⁻¹ * τ * ‖x a - M (x a)‖)
    (κ := (ε⁻¹ * ν + 2 * τ ^ 2 + 2 * ε⁻¹ * τ * δ + ε⁻¹ ^ 2 * δ) * C₀) hc2 (by positivity)
    ((hsol.cont.sub (M.continuous.comp_continuousOn hsol.cont)).add
      ((T.continuous.comp (M.continuous)).comp_continuousOn hsol.cont |>.const_smul ε))
    (fun s hs' => by
      have h1 := hsol.deriv s hs'
      have h2 := hasDerivWithinAt_clm M h1
      have h3 := (h1.sub h2).add ((hasDerivWithinAt_clm T h2).const_smul ε)
      rwa [flux_identity hs hε.ne' s (hstay s ⟨hs'.1, hs'.2.le⟩)] at h3)
    (fun s hs' => by
      have hs'' : s ∈ Icc a b := ⟨hs'.1, hs'.2.le⟩
      have hz := hC s hs''
      have hexp : 0 < Real.exp (-(ε⁻¹ ^ 2) * (s - a)) := Real.exp_pos _
      have h1 : ‖(T (M (x s)) - R (T (M (x s)))) - M (T (M (x s)) - R (T (M (x s))))‖
          ≤ ν * C₀ :=
        calc _ ≤ ‖T (M (x s)) - R (T (M (x s)))‖ := hs.projM.norm_sub_le _
          _ ≤ ν * ‖x s‖ := hs.defectT _
          _ ≤ ν * C₀ := mul_le_mul_of_nonneg_left hz hν
      have h2 : ‖R (T (x s - M (x s))) - M (R (T (x s - M (x s))))‖
          ≤ τ * (Real.exp (-(ε⁻¹ ^ 2) * (s - a)) * ‖x a - M (x a)‖ + (ε * τ + δ) * C₀) :=
        calc _ ≤ ‖R (T (x s - M (x s)))‖ := hs.projM.norm_sub_le _
          _ ≤ ‖T (x s - M (x s))‖ := hs.projR.norm_le _
          _ ≤ τ * ‖x s - M (x s)‖ := hs.normT _
          _ ≤ _ := mul_le_mul_of_nonneg_left (hmicro s hs'') hτ
      have h3 : ‖(M (x s) - R (M (x s))) - M (M (x s) - R (M (x s)))‖ ≤ δ * C₀ :=
        calc _ ≤ ‖M (x s) - R (M (x s))‖ := hs.projM.norm_sub_le _
          _ ≤ δ * ‖x s‖ := hs.defectM _
          _ ≤ δ * C₀ := mul_le_mul_of_nonneg_left hz hδ
      have h4 : ‖T (M (R (T (x s))))‖ ≤ τ ^ 2 * C₀ :=
        calc _ ≤ τ * ‖M (R (T (x s)))‖ := hs.normT _
          _ ≤ τ * ‖T (x s)‖ :=
            mul_le_mul_of_nonneg_left ((hs.projM.norm_le _).trans (hs.projR.norm_le _)) hτ
          _ ≤ τ * (τ * C₀) :=
            mul_le_mul_of_nonneg_left ((hs.normT _).trans
              (mul_le_mul_of_nonneg_left hz hτ)) hτ
          _ = τ ^ 2 * C₀ := by ring
      have h5 : ‖T (M (M (x s) - R (M (x s))))‖ ≤ τ * (δ * C₀) :=
        calc _ ≤ τ * ‖M (M (x s) - R (M (x s)))‖ := hs.normT _
          _ ≤ τ * ‖M (x s) - R (M (x s))‖ :=
            mul_le_mul_of_nonneg_left (hs.projM.norm_le _) hτ
          _ ≤ τ * (δ * C₀) := mul_le_mul_of_nonneg_left
            ((hs.defectM _).trans (mul_le_mul_of_nonneg_left hz hδ)) hτ
      have hsum := norm_sub_le
        (ε⁻¹ • ((T (M (x s)) - R (T (M (x s)))) - M (T (M (x s)) - R (T (M (x s)))))
          - ε⁻¹ • (R (T (x s - M (x s))) - M (R (T (x s - M (x s)))))
          - (ε⁻¹ ^ 2) • ((M (x s) - R (M (x s))) - M (M (x s) - R (M (x s))))
          - T (M (R (T (x s)))))
        (ε⁻¹ • T (M (M (x s) - R (M (x s)))))
      have hsum2 := norm_sub_le
        (ε⁻¹ • ((T (M (x s)) - R (T (M (x s)))) - M (T (M (x s)) - R (T (M (x s)))))
          - ε⁻¹ • (R (T (x s - M (x s))) - M (R (T (x s - M (x s)))))
          - (ε⁻¹ ^ 2) • ((M (x s) - R (M (x s))) - M (M (x s) - R (M (x s)))))
        (T (M (R (T (x s)))))
      have hsum3 := norm_sub_le
        (ε⁻¹ • ((T (M (x s)) - R (T (M (x s)))) - M (T (M (x s)) - R (T (M (x s)))))
          - ε⁻¹ • (R (T (x s - M (x s))) - M (R (T (x s - M (x s))))))
        ((ε⁻¹ ^ 2) • ((M (x s) - R (M (x s))) - M (M (x s) - R (M (x s)))))
      have hsum4 := norm_sub_le
        (ε⁻¹ • ((T (M (x s)) - R (T (M (x s)))) - M (T (M (x s)) - R (T (M (x s))))))
        (ε⁻¹ • (R (T (x s - M (x s))) - M (R (T (x s - M (x s))))))
      rw [norm_smul_nonneg hc.le] at hsum hsum4
      rw [norm_smul_nonneg hc.le] at hsum4
      rw [norm_smul_nonneg hc2.le] at hsum3
      have b1 := mul_le_mul_of_nonneg_left h1 hc.le
      have b2 := mul_le_mul_of_nonneg_left h2 hc.le
      have b3 := mul_le_mul_of_nonneg_left h3 hc2.le
      have b5 := mul_le_mul_of_nonneg_left h5 hc.le
      have heq : ε⁻¹ * (τ * (Real.exp (-(ε⁻¹ ^ 2) * (s - a)) * ‖x a - M (x a)‖
          + (ε * τ + δ) * C₀)) = ε⁻¹ * τ * ‖x a - M (x a)‖ * Real.exp (-(ε⁻¹ ^ 2) * (s - a))
            + (τ ^ 2 * (ε⁻¹ * ε) + ε⁻¹ * τ * δ) * C₀ := by ring
      rw [heq, hεc] at b2
      nlinarith)
    t ht
  have hval : (ε⁻¹ * ν + 2 * τ ^ 2 + 2 * ε⁻¹ * τ * δ + ε⁻¹ ^ 2 * δ) * C₀ / ε⁻¹ ^ 2
      ≤ (ε * ν + 2 * τ ^ 2 * ε ^ 2 + 2 * δ) * C₀ := by
    have h : (ε⁻¹ * ν + 2 * τ ^ 2 + 2 * ε⁻¹ * τ * δ + ε⁻¹ ^ 2 * δ) * C₀ / ε⁻¹ ^ 2
        = (ε * ν + 2 * τ ^ 2 * ε ^ 2 + 2 * ε * τ * δ + δ) * C₀ := by
      field_simp
    rw [h]
    refine mul_le_mul_of_nonneg_right ?_ hC0
    nlinarith
  exact key.trans (by simpa using hval)

/-- The slow-manifold bound (auxiliary for Theorem 4.2 of arXiv 2505.19929): the micro part is
`-ε T M x` up to `O(ε²)` and a layer term decaying like `e^{-(t-a)/(2 ε²)}`.  This is the rigorous
form of the expansions of `L` and `K` in the proof. -/
theorem IsRelaxSystem.flux_le (hs : IsRelaxSystem M R T τ δ ν) (hε : 0 < ε)
    (hετ : 2 * ε * τ ≤ 1) (hsol : ODESolution (relaxField M R T ε) x a b)
    (h0 : R (x a) = x a) {C₀ : ℝ} (hC : ∀ t ∈ Icc a b, ‖x t‖ ≤ C₀) :
    ∀ t ∈ Icc a b, ‖x t - M (x t) + ε • T (M (x t))‖ ≤
      3 * C₀ * Real.exp (-(ε⁻¹ ^ 2 / 2) * (t - a))
      + (ε * ν + 2 * τ ^ 2 * ε ^ 2 + 2 * δ) * C₀ := by
  intro t ht
  have hraw := hs.flux_le_raw hε hετ hsol h0 hC t ht
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hna := hC a ha
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hna
  have hτ := hs.tau_nonneg
  set s := t - a with hs'
  have hs0 : 0 ≤ s := sub_nonneg.2 ht.1
  have hc : 0 < ε⁻¹ := inv_pos.2 hε
  have hg : ‖x a - M (x a)‖ ≤ C₀ := (hs.projM.norm_sub_le _).trans hna
  have hp : ‖T (M (x a))‖ ≤ τ * C₀ :=
    (hs.normT _).trans (mul_le_mul_of_nonneg_left ((hs.projM.norm_le _).trans hna) hτ)
  have hy : ‖x a - M (x a) + ε • T (M (x a))‖ ≤ 3 / 2 * C₀ := by
    calc _ ≤ ‖x a - M (x a)‖ + ‖ε • T (M (x a))‖ := norm_add_le _ _
      _ = ‖x a - M (x a)‖ + ε * ‖T (M (x a))‖ := by rw [norm_smul_nonneg hε.le]
      _ ≤ C₀ + ε * (τ * C₀) := by gcongr
      _ ≤ 3 / 2 * C₀ := by nlinarith
  set u := ε⁻¹ ^ 2 / 2 * s with hu
  have hu0 : 0 ≤ u := by positivity
  have hsplit : Real.exp (-(ε⁻¹ ^ 2) * s) = Real.exp (-u) * Real.exp (-u) := by
    rw [← Real.exp_add]; congr 1; rw [hu]; ring
  have he1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have he0 : 0 < Real.exp (-u) := Real.exp_pos _
  have huexp : u * Real.exp (-u) ≤ 1 := by
    have h1 : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
    have h2 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have hsu : ε⁻¹ * τ * ‖x a - M (x a)‖ * s * Real.exp (-u) ≤ C₀ := by
    have h1 : ε⁻¹ * τ * ‖x a - M (x a)‖ * s * Real.exp (-u)
        = (2 * ε * τ) * ‖x a - M (x a)‖ * (u * Real.exp (-u)) := by
      rw [hu]; field_simp
    rw [h1]
    have h2 : 2 * ε * τ * ‖x a - M (x a)‖ ≤ 1 * C₀ :=
      mul_le_mul hετ hg (norm_nonneg _) zero_le_one
    have h3 : 0 ≤ 2 * ε * τ * ‖x a - M (x a)‖ := by positivity
    nlinarith
  have hmain : Real.exp (-(ε⁻¹ ^ 2) * s) * (‖x a - M (x a) + ε • T (M (x a))‖
        + ε⁻¹ * τ * ‖x a - M (x a)‖ * s) ≤ 3 * C₀ * Real.exp (-u) := by
    rw [hsplit]
    have h1 : Real.exp (-u) * ‖x a - M (x a) + ε • T (M (x a))‖ ≤ 3 / 2 * C₀ := by
      nlinarith [norm_nonneg (x a - M (x a) + ε • T (M (x a)))]
    nlinarith
  have hexpeq : -(ε⁻¹ ^ 2 / 2) * s = -u := by rw [hu]; ring
  rw [hexpeq]
  linarith

/-- The macro bound (auxiliary for Theorem 4.2 of arXiv 2505.19929): `M x` follows the limit flow
`v' = M T T M v`, up to the defects of the Galerkin projector. -/
theorem IsRelaxSystem.macro_le (hs : IsRelaxSystem M R T τ δ ν) (hε : 0 < ε)
    (hετ : 2 * ε * τ ≤ 1) (hsol : ODESolution (relaxField M R T ε) x a b)
    (h0 : R (x a) = x a) {C₀ : ℝ} (hC : ∀ t ∈ Icc a b, ‖x t‖ ≤ C₀) {v : ℝ → E}
    (hvc : ContinuousOn v (Icc a b))
    (hv : ∀ t ∈ Ico a b, HasDerivWithinAt v (M (T (T (M (v t))))) (Ici t) t) :
    ∀ t ∈ Icc a b, ‖M (x t) - v t‖ ≤ Real.exp (τ ^ 2 * (t - a)) *
      (‖M (x a) - v a‖ + 6 * C₀ * τ * ε +
        (ε⁻¹ * τ * ((ε * ν + 2 * τ ^ 2 * ε ^ 2 + 2 * δ) * C₀) + ε⁻¹ * δ * τ * C₀
          + ε⁻¹ ^ 2 * δ ^ 2 * C₀) * (t - a)) := by
  intro t ht
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans (hC t ht)
  have hstay := relaxField_stay hs.projR hsol h0
  have hc : 0 < ε⁻¹ := inv_pos.2 hε
  have hc2 : 0 < ε⁻¹ ^ 2 := by positivity
  have hτ := hs.tau_nonneg
  have hδ := hs.delta_nonneg
  have hν := hs.nu_nonneg
  have hflux := hs.flux_le hε hετ hsol h0 hC
  let 𝓓 : E →L[ℝ] E := M ∘L T ∘L T ∘L M
  have h𝓓 : ∀ w, ‖𝓓 w‖ ≤ τ ^ 2 * ‖w‖ := fun w => by
    calc ‖M (T (T (M w)))‖ ≤ ‖T (T (M w))‖ := hs.projM.norm_le _
      _ ≤ τ * ‖T (M w)‖ := hs.normT _
      _ ≤ τ * (τ * ‖M w‖) := mul_le_mul_of_nonneg_left (hs.normT _) hτ
      _ ≤ τ * (τ * ‖w‖) := by gcongr; exact hs.projM.norm_le _
      _ = _ := by ring
  have key := norm_le_of_forced (e := fun t => M (x t) - v t) (𝓓 := 𝓓) (a := a) (b := b)
    (f := fun t => -(ε⁻¹ • M (T (x t - M (x t) + ε • T (M (x t)))))
        + ε⁻¹ • M (T (x t) - R (T (x t))) - (ε⁻¹ ^ 2) • M (M (x t) - R (M (x t))))
    (β := τ ^ 2) (lam := ε⁻¹ ^ 2 / 2) (c := 3 * C₀ * (ε⁻¹ * τ))
    (κ := ε⁻¹ * τ * ((ε * ν + 2 * τ ^ 2 * ε ^ 2 + 2 * δ) * C₀) + ε⁻¹ * δ * τ * C₀
          + ε⁻¹ ^ 2 * δ ^ 2 * C₀)
    (by positivity) h𝓓 (by positivity) (by positivity) (by positivity)
    ((M.continuous.comp_continuousOn hsol.cont).sub hvc)
    (fun s hs' => by
      have h1 := hasDerivWithinAt_clm M (hsol.deriv s hs')
      have h2 := h1.sub (hv s hs')
      rw [limit_identity hs hε.ne' s (hstay s ⟨hs'.1, hs'.2.le⟩)] at h2
      convert h2 using 1
      have hval : 𝓓 (M (x s) - v s) = M (T (T (M (x s)))) - M (T (T (M (v s)))) := by
        simp [𝓓, hs.projM.idem]
      rw [hval]
      abel)
    (fun s hs' => by
      have hs'' : s ∈ Icc a b := ⟨hs'.1, hs'.2.le⟩
      have hz := hC s hs''
      have h1 : ‖M (T (x s - M (x s) + ε • T (M (x s))))‖ ≤
          τ * (3 * C₀ * Real.exp (-(ε⁻¹ ^ 2 / 2) * (s - a))
            + (ε * ν + 2 * τ ^ 2 * ε ^ 2 + 2 * δ) * C₀) :=
        calc _ ≤ ‖T (x s - M (x s) + ε • T (M (x s)))‖ := hs.projM.norm_le _
          _ ≤ τ * ‖x s - M (x s) + ε • T (M (x s))‖ := hs.normT _
          _ ≤ _ := mul_le_mul_of_nonneg_left (hflux s hs'') hτ
      have h2 : ‖M (T (x s) - R (T (x s)))‖ ≤ δ * τ * C₀ :=
        calc _ ≤ δ * ‖T (x s)‖ := hs.defect_adj _
          _ ≤ δ * (τ * C₀) := mul_le_mul_of_nonneg_left
            ((hs.normT _).trans (mul_le_mul_of_nonneg_left hz hτ)) hδ
          _ = _ := by ring
      have h3 : ‖M (M (x s) - R (M (x s)))‖ ≤ δ ^ 2 * C₀ :=
        (hs.defect_sq _).trans (mul_le_mul_of_nonneg_left hz (by positivity))
      have hsum := norm_sub_le
        (-(ε⁻¹ • M (T (x s - M (x s) + ε • T (M (x s)))))
          + ε⁻¹ • M (T (x s) - R (T (x s))))
        ((ε⁻¹ ^ 2) • M (M (x s) - R (M (x s))))
      have hsum2 := norm_add_le
        (-(ε⁻¹ • M (T (x s - M (x s) + ε • T (M (x s))))))
        (ε⁻¹ • M (T (x s) - R (T (x s))))
      rw [norm_neg, norm_smul_nonneg hc.le, norm_smul_nonneg hc.le] at hsum2
      rw [norm_smul_nonneg hc2.le] at hsum
      have b1 := mul_le_mul_of_nonneg_left h1 hc.le
      have b2 := mul_le_mul_of_nonneg_left h2 hc.le
      have b3 := mul_le_mul_of_nonneg_left h3 hc2.le
      nlinarith)
    t ht
  have hval : 3 * C₀ * (ε⁻¹ * τ) / (ε⁻¹ ^ 2 / 2) = 6 * C₀ * τ * ε := by
    field_simp
    ring
  rwa [hval] at key

end System

end Core

section GAP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Algorithm 2.3 of arXiv 2505.19929 (GAP)**, on an inner product space.  `P₀` is the projector
on the old spatial basis `X₀`, `Q₁` the projector on the new angular basis `V₁`.  L-step
`YL' = P₀ F(t, YL)`, `YL t₀ = Y₀`, where `Y₀ = P₀ Y₀` is the low-rank input; `Q₁` captures
`YL t₁`; Galerkin K-step `YK' = Q₁ F(t, YK)`, `YK t₀ = Q₁ Y₀`.  The output is `YK t₁`.  There is
no S-step and no backward step. -/
structure IsGAPStep (F : ℝ → E → E) (P₀ Q₁ : E →L[ℝ] E) (t₀ t₁ : ℝ) (Y₀ : E) (YL YK : ℝ → E) :
    Prop where
  projP₀ : IsOrthProj P₀
  projQ₁ : IsOrthProj Q₁
  start : P₀ Y₀ = Y₀
  lSol : ODESolution (fun t x => P₀ (F t x)) YL t₀ t₁
  lStart : YL t₀ = Y₀
  lCap : Q₁ (YL t₁) = YL t₁
  kSol : ODESolution (fun t x => Q₁ (F t x)) YK t₀ t₁
  kStart : YK t₀ = Q₁ Y₀

/-- **GAP is a BUG step with `P₁ = 1`** (arXiv 2505.19929, Algorithm 2.3 against Algorithm 2.2).
The GAP K-step is the Galerkin S-step of `IsBUGStep` with no new left basis.  The trajectory `YA`
is the K-step of BUG, which GAP does not compute; it enters only to fill the field of
`IsBUGStep`, since with `P₁ = 1` its capture and normal conditions are trivial. -/
theorem IsGAPStep.isBUGStep {F : ℝ → E → E} {P₀ Q₁ Q₀ : E →L[ℝ] E} {t₀ t₁ ε : ℝ} {Y₀ : E}
    {YL YK YA : ℝ → E} (hs : IsGAPStep F P₀ Q₁ t₀ t₁ Y₀ YL YK) (hQ₀ : IsOrthProj Q₀)
    (hA : ODESolution (fun t x => Q₀ (F t x)) YA t₀ t₁) (hA₀ : YA t₀ = Y₀) (hε0 : 0 ≤ ε)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε) :
    IsBUGStep F ε P₀ Q₀ 1 Q₁ t₀ t₁ Y₀ YA YL YK where
  projP₀ := hs.projP₀
  projQ₀ := hQ₀
  projP₁ := IsOrthProj.one
  projQ₁ := hs.projQ₁
  comm₁ _ := rfl
  kSol := hA
  kStart := hA₀
  kCap := rfl
  kNormal t _ := by simpa using hε0
  lSol := hs.lSol
  lStart := hs.lStart
  lCap := hs.lCap
  lNormal := hε
  sSol := hs.kSol
  sStart := hs.kStart

/-- **Theorem 3.3 of arXiv 2505.19929 for `IsGAPStep`**: the library's `gap_local_error`, with the
explicit constants of that library theorem (the paper states only the order
`Δt² + η Δt + δ₀ Δt`). Differences: exact input (`Y₀ = A t₀`, so `δ₀ = 0`), and the model-order
assumption (c) is replaced by `‖(1 - Q₁)(1 - P₀) F(t, YL t₁)‖ ≤ ε`. -/
theorem IsGAPStep.local_error {F : ℝ → E → E} {P₀ Q₁ : E →L[ℝ] E} {t₀ t₁ h L B ε : ℝ} {Y₀ : E}
    {YL YK A : ℝ → E} (hs : IsGAPStep F P₀ Q₁ t₀ t₁ Y₀ YL YK) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε) :
    ‖YK t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + h * (4 * L * B * h + ε))
      + h * (4 * L * B * h + ε) :=
  gap_local_error hF hL hB hs.projP₀ hs.projQ₁ ht₁ hh hA hs.lSol (hs.lStart.trans hA₀.symm)
    hs.lCap hε hs.kSol (by rw [hs.kStart, hA₀])

end GAP

section Concrete

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open scoped LeanDLRA.Frobenius
open LeanDLRA.Frobenius Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The moment conditions on the angular grid: positive weights and the Gauss–Legendre moments
`∑ w = 2`, `∑ w μ = 0`, `∑ w μ² = 2/3` (every Gauss rule with at least two nodes). -/
structure IsAngularQuad (μ w : n → ℝ) : Prop where
  pos : ∀ k, 0 < w k
  mass : ∑ k, w k = 2
  first : ∑ k, w k * μ k = 0
  second : ∑ k, w k * μ k ^ 2 = 2 / 3

/-- The matrix `W_μ = ½ w 𝟙ᵀ` of (5.1). -/
noncomputable def Wmat (w : n → ℝ) : Matrix n n ℝ := Matrix.of fun k _ => w k / 2

/-- The right-hand side of the semi-discrete scaled RTE (5.1):
`F' = -ε⁻¹ D F diag(μ) + ε⁻² (F W_μ - F)`. -/
noncomputable def rte (D : Matrix m m ℝ) (μ w : n → ℝ) (ε : ℝ) (F : Matrix m n ℝ) :
    Matrix m n ℝ :=
  -(ε⁻¹ • (D * F * diagonal μ)) + (ε⁻¹ ^ 2) • (F * Wmat w - F)

/-- The discrete density `ρ = ½ ∑ₖ wₖ F(·, k)`. -/
noncomputable def density (w : n → ℝ) (F : Matrix m n ℝ) : m → ℝ :=
  fun i => ∑ k, w k / 2 * F i k

/-- The isotropic distribution `ρ 𝟙ᵀ`. -/
def iso (r : m → ℝ) : Matrix m n ℝ := Matrix.of fun i _ => r i

/-- The unit vector `b = √(w/2)`, the equilibrium direction in the normalized variables. -/
noncomputable def bCol (w : n → ℝ) : Matrix n Unit ℝ := Matrix.of fun k _ => √(w k / 2)

/-- The scaling `G = F diag(√(w/2))`, which turns the `w`-inner product into the Euclidean one. -/
noncomputable def sDiag (w : n → ℝ) : Matrix n n ℝ := diagonal fun k => √(w k / 2)

/-- The flux direction `c = diag(μ) b`. -/
noncomputable def cCol (μ w : n → ℝ) : Matrix n Unit ℝ := diagonal μ * bCol w

/-- The projector onto isotropic states in the normalized variables. -/
noncomputable def macroP (w : n → ℝ) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ := rightProj (bCol w)

/-- The transport `G ↦ D G diag(μ)`. -/
noncomputable def transport (D : Matrix m m ℝ) (μ : n → ℝ) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  (leftMulCLM D).comp (rightMulCLM (diagonal μ))

/-- The RTE in the normalized variables. -/
noncomputable def rteN (D : Matrix m m ℝ) (μ w : n → ℝ) (ε : ℝ) :
    ℝ → Matrix m n ℝ → Matrix m n ℝ :=
  fun _ G => -(ε⁻¹ • transport D μ G) + (ε⁻¹ ^ 2) • (macroP w G - G)

/-- The basis `V` in the normalized variables: `Ṽ = √2 diag(√(w/2)) V`. -/
noncomputable def angBasis {r : ℕ} (w : n → ℝ) (V : Matrix n (Fin r) ℝ) : Matrix n (Fin r) ℝ :=
  (√2 : ℝ) • (sDiag w * V)

lemma macroP_apply (w : n → ℝ) (G : Matrix m n ℝ) : macroP w G = G * bCol w * (bCol w)ᵀ := by
  simp [macroP]

lemma transport_apply (D : Matrix m m ℝ) (μ : n → ℝ) (G : Matrix m n ℝ) :
    transport D μ G = D * G * diagonal μ := by
  simp [transport, Matrix.mul_assoc]

section Moments

variable {μ w : n → ℝ}

lemma sqrt_sq_half (hq : IsAngularQuad μ w) (k : n) : √(w k / 2) * √(w k / 2) = w k / 2 :=
  Real.mul_self_sqrt (by linarith [hq.pos k])

lemma bCol_orth (hq : IsAngularQuad μ w) : (bCol w)ᵀ * bCol w = 1 := by
  ext i j
  obtain rfl : i = j := Subsingleton.elim _ _
  simp only [Matrix.mul_apply, Matrix.transpose_apply, bCol, Matrix.of_apply, Matrix.one_apply_eq]
  rw [Finset.sum_congr rfl fun k _ => sqrt_sq_half hq k, ← Finset.sum_div, hq.mass]
  norm_num

lemma bCol_cCol (hq : IsAngularQuad μ w) : (bCol w)ᵀ * cCol μ w = 0 := by
  ext i j
  simp only [cCol, Matrix.mul_apply, Matrix.transpose_apply, bCol, Matrix.of_apply,
    Matrix.diagonal_apply, Matrix.zero_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have h : ∀ k, √(w k / 2) * (μ k * √(w k / 2)) = (w k * μ k) / 2 := fun k => by
    have := sqrt_sq_half hq k
    calc _ = μ k * (√(w k / 2) * √(w k / 2)) := by ring
      _ = _ := by rw [this]; ring
  rw [Finset.sum_congr rfl fun k _ => h k, ← Finset.sum_div, hq.first]
  norm_num

lemma cCol_cCol (hq : IsAngularQuad μ w) : (cCol μ w)ᵀ * cCol μ w = (1 / 3 : ℝ) • 1 := by
  ext i j
  obtain rfl : i = j := Subsingleton.elim _ _
  simp only [cCol, Matrix.mul_apply, Matrix.transpose_apply, bCol, Matrix.of_apply,
    Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have h : ∀ k, (μ k * √(w k / 2)) * (μ k * √(w k / 2)) = (w k * μ k ^ 2) / 2 := fun k => by
    have := sqrt_sq_half hq k
    calc _ = μ k ^ 2 * (√(w k / 2) * √(w k / 2)) := by ring
      _ = _ := by rw [this]; ring
  rw [Finset.sum_congr rfl fun k _ => h k, ← Finset.sum_div, hq.second]
  norm_num

lemma cCol_transpose (μ w : n → ℝ) : (cCol μ w)ᵀ = (bCol w)ᵀ * diagonal μ := by
  simp [cCol, Matrix.transpose_mul]

lemma norm_bCol (hq : IsAngularQuad μ w) : ‖bCol w‖ = 1 := by
  have h : ‖bCol w‖ ^ 2 = 1 := by
    rw [norm_sq_eq_sum]
    simp only [bCol, Matrix.of_apply, Fintype.sum_unique]
    have : ∀ k, √(w k / 2) ^ 2 = w k / 2 := fun k => by rw [sq, sqrt_sq_half hq]
    rw [Finset.sum_congr rfl fun k _ => this k, ← Finset.sum_div, hq.mass]
    norm_num
  nlinarith [norm_nonneg (bCol w)]

lemma isOrthProj_macroP (hq : IsAngularQuad μ w) :
    IsOrthProj (macroP w : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
  isOrthProj_rightProj (bCol_orth hq)

lemma macro_balance (hq : IsAngularQuad μ w) (D : Matrix m m ℝ) (G : Matrix m n ℝ) :
    macroP w (transport D μ (macroP w G)) = 0 := by
  have h : (bCol w)ᵀ * (diagonal μ * bCol w) = 0 := bCol_cCol hq
  rw [macroP_apply, transport_apply, macroP_apply]
  calc D * (G * bCol w * (bCol w)ᵀ) * diagonal μ * bCol w * (bCol w)ᵀ
      = D * (G * bCol w) * ((bCol w)ᵀ * (diagonal μ * bCol w)) * (bCol w)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h]; simp

lemma sDiag_transpose (w : n → ℝ) : (sDiag w)ᵀ = sDiag w := by
  simp [sDiag]

lemma sDiag_mul_self (hq : IsAngularQuad μ w) : sDiag w * sDiag w = (1 / 2 : ℝ) • diagonal w := by
  have h : (fun k => √(w k / 2) * √(w k / 2)) = (1 / 2 : ℝ) • w := by
    funext k
    rw [sqrt_sq_half hq, Pi.smul_apply, smul_eq_mul]
    ring
  rw [sDiag, Matrix.diagonal_mul_diagonal, h, Matrix.diagonal_smul]

lemma Wmat_mul_sDiag (hq : IsAngularQuad μ w) :
    Wmat w * sDiag w = sDiag w * bCol w * (bCol w)ᵀ := by
  ext k j
  have h1 : (Wmat w * sDiag w) k j = w k / 2 * √(w j / 2) := by
    simp [sDiag, Wmat, Matrix.mul_diagonal]
  have h2 : (sDiag w * bCol w * (bCol w)ᵀ) k j = √(w k / 2) * √(w k / 2) * √(w j / 2) := by
    simp [sDiag, bCol, Matrix.mul_apply, Matrix.diagonal_apply]
  rw [h1, h2, sqrt_sq_half hq]

lemma rte_mul_sDiag (hq : IsAngularQuad μ w) (D : Matrix m m ℝ) (ε t : ℝ) (F : Matrix m n ℝ) :
    rte D μ w ε F * sDiag w = rteN D μ w ε t (F * sDiag w) := by
  have h1 : D * F * diagonal μ * sDiag w = D * (F * sDiag w) * diagonal μ := by
    have : diagonal μ * sDiag w = sDiag w * diagonal μ := by
      simp [sDiag, Matrix.diagonal_mul_diagonal, mul_comm]
    simp only [Matrix.mul_assoc, this]
  have h2 : F * Wmat w * sDiag w = F * sDiag w * bCol w * (bCol w)ᵀ := by
    rw [Matrix.mul_assoc, Wmat_mul_sDiag hq]
    simp only [Matrix.mul_assoc]
  simp only [rte, rteN, macroP_apply, transport_apply, Matrix.add_mul, Matrix.neg_mul,
    Matrix.smul_mul, Matrix.sub_mul, h1, h2]

lemma angBasis_orth {r : ℕ} (hq : IsAngularQuad μ w) {V : Matrix n (Fin r) ℝ}
    (hV : Vᵀ * diagonal w * V = 1) : (angBasis w V)ᵀ * angBasis w V = 1 := by
  have h2 : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have : (angBasis w V)ᵀ * angBasis w V = ((√2 : ℝ) * √2) • (Vᵀ * (sDiag w * sDiag w) * V) := by
    simp only [angBasis, Matrix.transpose_smul, Matrix.transpose_mul, sDiag_transpose,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [this, h2, sDiag_mul_self hq, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hV]
  norm_num

lemma proj_mul_sDiag {r : ℕ} (hq : IsAngularQuad μ w) (V : Matrix n (Fin r) ℝ)
    (F : Matrix m n ℝ) :
    F * diagonal w * V * Vᵀ * sDiag w
      = (F * sDiag w) * angBasis w V * (angBasis w V)ᵀ := by
  have h2 : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have : (F * sDiag w) * angBasis w V * (angBasis w V)ᵀ
      = ((√2 : ℝ) * √2) • (F * (sDiag w * sDiag w) * V * Vᵀ * sDiag w) := by
    simp only [angBasis, Matrix.transpose_smul, Matrix.transpose_mul, sDiag_transpose,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [this, h2, sDiag_mul_self hq]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  norm_num

end Moments

/-- Scaling a solution by a fixed matrix. -/
lemma odeSolution_mul_right {f g : ℝ → Matrix m n ℝ → Matrix m n ℝ} {y : ℝ → Matrix m n ℝ}
    {a b : ℝ} (N : Matrix n n ℝ) (hy : ODESolution f y a b)
    (h : ∀ t Y, f t Y * N = g t (Y * N)) : ODESolution g (fun t => y t * N) a b where
  cont := by
    simpa [Function.comp_def] using (rightMulCLM N).continuous.comp_continuousOn hy.cont
  deriv t ht := by
    have h1 := hasDerivWithinAt_clm (rightMulCLM N) (hy.deriv t ht)
    simpa [h] using h1

/-- **The fully discrete GAP step for the RTE**: Algorithm 2.3 applied to (5.1), with exact
substeps, and with the projectors of Section 5.  `X` has orthonormal columns; `V` is orthonormal
for `⟨·, ·⟩_w`, so that `𝒫_V[F] = F diag(w) V Vᵀ`.  (On a uniform grid the factor `Δx` in the
spatial inner product only rescales `X`, and is omitted.) -/
structure IsRTEGAPStep {r : ℕ} (D : Matrix m m ℝ) (μ w : n → ℝ) (ε t₀ t₁ : ℝ)
    (X : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (F₀ : Matrix m n ℝ)
    (ℓ k : ℝ → Matrix m n ℝ) : Prop where
  orthoX : Xᵀ * X = 1
  start : X * Xᵀ * F₀ = F₀
  lSol : ODESolution (fun _ Y => X * Xᵀ * rte D μ w ε Y) ℓ t₀ t₁
  lStart : ℓ t₀ = F₀
  orthoV : Vᵀ * diagonal w * V = 1
  capture : ℓ t₁ * diagonal w * V * Vᵀ = ℓ t₁
  kSol : ODESolution (fun _ Y => rte D μ w ε Y * diagonal w * V * Vᵀ) k t₀ t₁
  kStart : k t₀ = F₀ * diagonal w * V * Vᵀ

/-- In the normalized variables `G = F diag(√(w/2))`, `IsRTEGAPStep` is `IsGAPStep` for the field
`rteN`, with orthogonal projectors for the Euclidean inner product (arXiv 2505.19929,
Algorithm 2.3 and (5.1)). -/
theorem IsRTEGAPStep.normalized {r : ℕ} {D : Matrix m m ℝ} {μ w : n → ℝ} {ε t₀ t₁ : ℝ}
    {X : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ} {F₀ : Matrix m n ℝ}
    {ℓ k : ℝ → Matrix m n ℝ} (hq : IsAngularQuad μ w)
    (hs : IsRTEGAPStep D μ w ε t₀ t₁ X V F₀ ℓ k) :
    IsGAPStep (rteN D μ w ε) (leftProj X) (rightProj (angBasis w V)) t₀ t₁ (F₀ * sDiag w)
      (fun t => ℓ t * sDiag w) (fun t => k t * sDiag w) where
  projP₀ := isOrthProj_leftProj hs.orthoX
  projQ₁ := isOrthProj_rightProj (angBasis_orth hq hs.orthoV)
  start := by
    rw [leftProj_apply, ← Matrix.mul_assoc, hs.start]
  lSol := odeSolution_mul_right (sDiag w) hs.lSol fun t Y => by
    rw [leftProj_apply, ← rte_mul_sDiag hq, Matrix.mul_assoc]
  lStart := by simp only [hs.lStart]
  lCap := by
    rw [rightProj_apply, ← proj_mul_sDiag hq, hs.capture]
  kSol := odeSolution_mul_right (sDiag w) hs.kSol fun t Y => by
    rw [proj_mul_sDiag hq, rte_mul_sDiag hq D ε t, rightProj_apply]
  kStart := by
    simp only [hs.kStart]
    rw [rightProj_apply, proj_mul_sDiag hq]

section Systems

variable {μ w : n → ℝ} {r : ℕ}

/-- The transport of the L-step: `G ↦ P D (P G) diag(μ)`, with `P = X Xᵀ`. -/
noncomputable def transportL (X : Matrix m (Fin r) ℝ) (D : Matrix m m ℝ) (μ : n → ℝ) :
    Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  (leftProj X).comp ((transport D μ).comp (leftProj X))

lemma norm_transport_le (D : Matrix m m ℝ) (μ : n → ℝ) (G : Matrix m n ℝ) :
    ‖transport D μ G‖ ≤ (‖D‖ * ‖diagonal μ‖) * ‖G‖ := by
  rw [transport_apply]
  calc ‖D * G * diagonal μ‖ ≤ ‖D * G‖ * ‖diagonal μ‖ := Frobenius.norm_mul_le _ _
    _ ≤ (‖D‖ * ‖G‖) * ‖diagonal μ‖ := by gcongr; exact Frobenius.norm_mul_le _ _
    _ = _ := by ring

/-- The full RTE (5.1) of arXiv 2505.19929 as a two-scale system. -/
theorem relaxSystemFull (hq : IsAngularQuad μ w) (D : Matrix m m ℝ) :
    IsRelaxSystem (macroP w) 1 (transport D μ : Matrix m n ℝ →L[ℝ] _) (‖D‖ * ‖diagonal μ‖) 0 0 where
  projM := isOrthProj_macroP hq
  projR := IsOrthProj.one
  tau_nonneg := by positivity
  delta_nonneg := le_rfl
  nu_nonneg := le_rfl
  normT := norm_transport_le D μ
  balance := macro_balance hq D
  defectM x := by simp
  defectT x := by simp

/-- The L-step of arXiv 2505.19929 as a two-scale system with `R = 1`, for the transport `P T P`. -/
theorem relaxSystemL (hq : IsAngularQuad μ w) {X : Matrix m (Fin r) ℝ} (hX : Xᵀ * X = 1)
    (D : Matrix m m ℝ) :
    IsRelaxSystem (macroP w) 1 (transportL X D μ : Matrix m n ℝ →L[ℝ] _)
      (‖D‖ * ‖diagonal μ‖) 0 0 where
  projM := isOrthProj_macroP hq
  projR := IsOrthProj.one
  tau_nonneg := by positivity
  delta_nonneg := le_rfl
  nu_nonneg := le_rfl
  normT G := by
    have hP := isOrthProj_leftProj (n := n) hX
    calc ‖leftProj X (transport D μ (leftProj X G))‖
        ≤ ‖transport D μ (leftProj X G)‖ := hP.norm_le _
      _ ≤ (‖D‖ * ‖diagonal μ‖) * ‖leftProj X G‖ := norm_transport_le _ _ _
      _ ≤ _ := by gcongr; exact hP.norm_le _
  balance G := by
    have h1 : leftProj X (macroP w G) = macroP w (leftProj X G) :=
      leftProj_rightProj_comm X (bCol w) G
    have h2 : ∀ Z : Matrix m n ℝ, macroP w (leftProj X Z) = leftProj X (macroP w Z) := fun Z =>
      (leftProj_rightProj_comm X (bCol w) Z).symm
    change macroP w (leftProj X (transport D μ (leftProj X (macroP w G)))) = 0
    rw [h1, h2, macro_balance hq, map_zero]
  defectM x := by simp
  defectT x := by simp

lemma mul_transpose_sub {k : Type*} [Fintype k] (Y : Matrix m Unit ℝ) (Z : Matrix n Unit ℝ)
    (U : Matrix n k ℝ) :
    Y * Zᵀ - Y * Zᵀ * U * Uᵀ = Y * (Z - U * Uᵀ * Z)ᵀ := by
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_sub, Matrix.mul_assoc]

/-- The K-step of arXiv 2505.19929 as a two-scale system: the defects of `R = P_V` are the distances
of `b` (the direction `𝟙`) and of `c` (the direction `μ`) to `V`. -/
theorem relaxSystemK (hq : IsAngularQuad μ w) {U : Matrix n (Fin r) ℝ} (hU : Uᵀ * U = 1)
    (D : Matrix m m ℝ) :
    IsRelaxSystem (macroP w) (rightProj U) (transport D μ : Matrix m n ℝ →L[ℝ] _)
      (‖D‖ * ‖diagonal μ‖) ‖bCol w - U * Uᵀ * bCol w‖
      (‖D‖ * ‖cCol μ w - U * Uᵀ * cCol μ w‖) where
  projM := isOrthProj_macroP hq
  projR := isOrthProj_rightProj hU
  tau_nonneg := by positivity
  delta_nonneg := norm_nonneg _
  nu_nonneg := by positivity
  normT := norm_transport_le D μ
  balance := macro_balance hq D
  defectM x := by
    have h : macroP w x - rightProj U (macroP w x)
        = (x * bCol w) * (bCol w - U * Uᵀ * bCol w)ᵀ := by
      rw [macroP_apply, rightProj_apply, mul_transpose_sub]
    rw [h, mul_comm]
    calc _ ≤ ‖x * bCol w‖ * ‖(bCol w - U * Uᵀ * bCol w)ᵀ‖ := Frobenius.norm_mul_le _ _
      _ ≤ ‖x‖ * ‖bCol w - U * Uᵀ * bCol w‖ := by
        rw [Frobenius.norm_transpose]
        gcongr
        exact norm_mul_le_of_orthonormal (bCol_orth hq) x
  defectT x := by
    have h : transport D μ (macroP w x) - rightProj U (transport D μ (macroP w x))
        = (D * (x * bCol w)) * (cCol μ w - U * Uᵀ * cCol μ w)ᵀ := by
      have h0 : transport D μ (macroP w x) = D * (x * bCol w) * (cCol μ w)ᵀ := by
        rw [transport_apply, macroP_apply, cCol_transpose]
        simp only [Matrix.mul_assoc]
      rw [h0, rightProj_apply, mul_transpose_sub]
    rw [h]
    calc _ ≤ ‖D * (x * bCol w)‖ * ‖(cCol μ w - U * Uᵀ * cCol μ w)ᵀ‖ := Frobenius.norm_mul_le _ _
      _ ≤ (‖D‖ * ‖x‖) * ‖cCol μ w - U * Uᵀ * cCol μ w‖ := by
        rw [Frobenius.norm_transpose]
        gcongr
        exact (Frobenius.norm_mul_le _ _).trans (by
          gcongr
          exact norm_mul_le_of_orthonormal (bCol_orth hq) x)
      _ = _ := by ring

lemma relaxField_L {X : Matrix m (Fin r) ℝ} {D : Matrix m m ℝ} {ε : ℝ} (t : ℝ)
    {z : Matrix m n ℝ} (hz : leftProj X z = z) :
    relaxField (macroP w) 1 (transportL X D μ) ε t z = leftProj X (rteN D μ w ε t z) := by
  have h1 : leftProj X (macroP w z) = macroP w z := by
    have := leftProj_rightProj_comm X (bCol w) z
    rw [hz] at this
    exact this
  simp only [relaxField, rteN, transportL, ContinuousLinearMap.comp_apply, hz, map_add, map_neg,
    map_smul, map_sub, one_apply_eq_self, h1]

/-- Invariance of the span of `X` (arXiv 2505.19929, Lemma 2.1) and the L-step in the form of a
two-scale system. -/
theorem lSol_relax {X : Matrix m (Fin r) ℝ} {D : Matrix m m ℝ} {ε t₀ t₁ : ℝ}
    {Q : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} {G₀ : Matrix m n ℝ} {L K : ℝ → Matrix m n ℝ}
    (hs : IsGAPStep (rteN D μ w ε) (leftProj X) Q t₀ t₁ G₀ L K) :
    (∀ t ∈ Icc t₀ t₁, leftProj X (L t) = L t) ∧
      ODESolution (relaxField (macroP w) 1 (transportL X D μ) ε) L t₀ t₁ := by
  have hsol : ODESolution (relaxField (macroP w) (leftProj X) (transport D μ) ε) L t₀ t₁ :=
    hs.lSol
  have stay := relaxField_stay hs.projP₀ hsol (by rw [hs.lStart]; exact hs.start)
  refine ⟨stay, hs.lSol.cont, fun t ht => ?_⟩
  rw [relaxField_L t (stay t ⟨ht.1, ht.2.le⟩)]
  exact hs.lSol.deriv t ht

/-- Uniform linear independence of two vectors. -/
def UniformlyIndep (c₀ : ℝ) (u a : m → ℝ) : Prop :=
  ∀ α β : ℝ, c₀ * (|α| + |β|) ≤ ‖α • u + β • a‖

lemma colwise_bound {u a : m → ℝ} {β γ : Matrix n Unit ℝ} {Z : Matrix m n ℝ} {c₀ e : ℝ}
    (hc₀ : 0 ≤ c₀) (hind : UniformlyIndep c₀ u a)
    (hZ : ∀ i k, Z i k = -(u i * β k ()) + e * (a i * γ k ())) :
    c₀ * ‖β‖ ≤ ‖Z‖ ∧ c₀ * (e * ‖γ‖) ≤ ‖Z‖ := by
  have hcol : ∀ k, (c₀ * (|β k ()| + |e * γ k ()|)) ^ 2 ≤ ∑ i, Z i k ^ 2 := by
    intro k
    have h1 := hind (-β k ()) (e * γ k ())
    rw [abs_neg] at h1
    have h2 : ‖(-β k ()) • u + (e * γ k ()) • a‖ ≤ √(∑ i, Z i k ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      have : ((-β k ()) • u + (e * γ k ()) • a) i = Z i k := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hZ]
        ring
      rw [this, Real.norm_eq_abs]
      exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun i => Z i k ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
    have h3 : 0 ≤ c₀ * (|β k ()| + |e * γ k ()|) := by positivity
    calc _ ≤ (√(∑ i, Z i k ^ 2)) ^ 2 := pow_le_pow_left₀ h3 (h1.trans h2) 2
      _ = _ := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hZnorm : ‖Z‖ ^ 2 = ∑ k, ∑ i, Z i k ^ 2 := by rw [norm_sq_eq_sum, Finset.sum_comm]
  constructor
  · have hβ : (c₀ * ‖β‖) ^ 2 ≤ ‖Z‖ ^ 2 := by
      rw [mul_pow, norm_sq_eq_sum, hZnorm, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => (le_trans ?_ (hcol k))
      simp only [Finset.univ_unique, Finset.sum_singleton]
      have h4 : c₀ * |β k ()| ≤ c₀ * (|β k ()| + |e * γ k ()|) := by
        gcongr
        linarith [abs_nonneg (e * γ k ())]
      have h5 := pow_le_pow_left₀ (mul_nonneg hc₀ (abs_nonneg _)) h4 2
      rw [mul_pow, sq_abs] at h5
      exact h5
    exact abs_le_of_sq_le_sq' hβ (norm_nonneg _) |>.2
  · have hγ : (c₀ * (e * ‖γ‖)) ^ 2 ≤ ‖Z‖ ^ 2 := by
      rw [mul_pow, mul_pow, norm_sq_eq_sum, hZnorm, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => (le_trans ?_ (hcol k))
      simp only [Finset.univ_unique, Finset.sum_singleton]
      have h4 : c₀ * |e * γ k ()| ≤ c₀ * (|β k ()| + |e * γ k ()|) := by
        gcongr
        linarith [abs_nonneg (β k ())]
      have h5 := pow_le_pow_left₀ (mul_nonneg hc₀ (abs_nonneg _)) h4 2
      rw [mul_pow, sq_abs, mul_pow] at h5
      exact h5
    exact abs_le_of_sq_le_sq' hγ (norm_nonneg _) |>.2

lemma exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ x⁻¹ := by
  have h1 : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  rw [Real.exp_neg]
  exact inv_anti₀ hx h1

lemma exp_neg_sq_le {ε h : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hh : 0 < h) :
    Real.exp (-(ε⁻¹ ^ 2) * h) ≤ ε * h⁻¹ := by
  have hx : 0 < ε⁻¹ ^ 2 * h := by positivity
  have h1 := exp_neg_le_inv hx
  have h2 : -(ε⁻¹ ^ 2) * h = -(ε⁻¹ ^ 2 * h) := by ring
  rw [h2]
  refine h1.trans ?_
  have h3 : (ε⁻¹ ^ 2 * h)⁻¹ = ε ^ 2 * h⁻¹ := by
    field_simp
  rw [h3]
  have : ε ^ 2 ≤ ε := by nlinarith
  gcongr

lemma apriori_of_exp {M R T : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} {τ δ ν ε t₀ t₁ h C : ℝ}
    {x : ℝ → Matrix m n ℝ} (hs : IsRelaxSystem M R T τ δ ν) (hε : 0 < ε) (hετ : 2 * ε * τ ≤ 1)
    (hsol : ODESolution (relaxField M R T ε) x t₀ t₁) (h0 : R (x t₀) = x t₀)
    (ht₁ : t₁ = t₀ + h) (hC : Real.exp (2 * τ ^ 2 * h) * ‖x t₀‖ ≤ C) :
    ∀ t ∈ Icc t₀ t₁, ‖x t‖ ≤ C := by
  intro t ht
  refine (hs.apriori hε hετ hsol h0 t ht).trans (le_trans ?_ hC)
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (by positivity))
  linarith [ht.2]

/-- **The L-step produces the moments** (arXiv 2505.19929, the first half of the proof of Theorem
4.2, with the limit taken rigorously). If the density of `L t₁` and its projected gradient are
uniformly independent, then the new basis contains `b` (the direction `𝟙`) up to `O(ε²)` and `c`
(the direction `μ`) up to `O(ε)`. -/
theorem lstep_capture (hq : IsAngularQuad μ w) {X : Matrix m (Fin r) ℝ} (hX : Xᵀ * X = 1)
    {U : Matrix n (Fin r) ℝ} (hU : Uᵀ * U = 1) {D : Matrix m m ℝ} {ε t₀ t₁ h : ℝ}
    {G₀ : Matrix m n ℝ} {L K : ℝ → Matrix m n ℝ}
    (hs : IsGAPStep (rteN D μ w ε) (leftProj X) (rightProj U) t₀ t₁ G₀ L K) (hε : 0 < ε)
    (hετ : 2 * ε * (‖D‖ * ‖diagonal μ‖) ≤ 1) (ht₁ : t₁ = t₀ + h) (hh : 0 < h) {C c₀ : ℝ}
    (hC : Real.exp (2 * (‖D‖ * ‖diagonal μ‖) ^ 2 * h) * ‖G₀‖ ≤ C) (hc₀ : 0 ≤ c₀)
    (hind : UniformlyIndep c₀ (fun i => (L t₁ * bCol w) i ())
      (fun i => (X * Xᵀ * D * (L t₁ * bCol w)) i ())) :
    c₀ * ‖bCol w - U * Uᵀ * bCol w‖ ≤ (6 / h + 2 * (‖D‖ * ‖diagonal μ‖) ^ 2) * C * ε ^ 2 ∧
      c₀ * (ε * ‖cCol μ w - U * Uᵀ * cCol μ w‖) ≤
        (6 / h + 2 * (‖D‖ * ‖diagonal μ‖) ^ 2) * C * ε ^ 2 := by
  set τ := ‖D‖ * ‖diagonal μ‖ with hτdef
  obtain ⟨stay, hsol⟩ := lSol_relax hs
  have sys := relaxSystemL (μ := μ) hq hX D
  have hab : t₀ ≤ t₁ := by linarith
  have hbound : ∀ t ∈ Icc t₀ t₁, ‖L t‖ ≤ C :=
    apriori_of_exp sys hε hετ hsol rfl ht₁ (by rwa [hs.lStart])
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hbound t₀ ⟨le_rfl, hab⟩)
  have hflux := sys.flux_le hε hετ hsol rfl hbound t₁ ⟨hab, le_rfl⟩
  have hτ0 : 0 ≤ τ := by positivity
  set G₁ := L t₁ with hG₁
  set y := G₁ - macroP w G₁ + ε • transportL X D μ (macroP w G₁) with hy
  -- the size of `y`
  have hexp : Real.exp (-(ε⁻¹ ^ 2 / 2) * (t₁ - t₀)) ≤ 2 / h * ε ^ 2 := by
    have hx : 0 < ε⁻¹ ^ 2 / 2 * h := by positivity
    have h1 := exp_neg_le_inv hx
    have h2 : -(ε⁻¹ ^ 2 / 2) * (t₁ - t₀) = -(ε⁻¹ ^ 2 / 2 * h) := by rw [ht₁]; ring
    rw [h2]
    refine h1.trans (le_of_eq ?_)
    field_simp
  have hynorm : ‖y‖ ≤ (6 / h + 2 * τ ^ 2) * C * ε ^ 2 := by
    refine hflux.trans ?_
    have h3 : 3 * C * Real.exp (-(ε⁻¹ ^ 2 / 2) * (t₁ - t₀)) ≤ 3 * C * (2 / h * ε ^ 2) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    have h4 : (6 / h + 2 * τ ^ 2) * C * ε ^ 2
        = 3 * C * (2 / h * ε ^ 2) + (ε * 0 + 2 * τ ^ 2 * ε ^ 2 + 2 * 0) * C := by
      field_simp
      ring
    rw [h4]
    exact add_le_add_left h3 _
  -- the structure of `y`
  have hstay₁ : leftProj X G₁ = G₁ := stay t₁ ⟨hab, le_rfl⟩
  set uM := G₁ * bCol w with huM
  set aM := X * Xᵀ * D * uM with haM
  have hPM : leftProj X (macroP w G₁) = macroP w G₁ := by
    have := leftProj_rightProj_comm X (bCol w) G₁
    rw [hstay₁] at this
    exact this
  have hMG : macroP w G₁ = uM * (bCol w)ᵀ := macroP_apply w G₁
  have hTG : transportL X D μ (macroP w G₁) = aM * (cCol μ w)ᵀ := by
    change leftProj X (transport D μ (leftProj X (macroP w G₁))) = _
    rw [hPM, transport_apply, leftProj_apply, hMG, cCol_transpose]
    simp only [haM, Matrix.mul_assoc]
  have hcap : G₁ * U * Uᵀ = G₁ := by
    have := hs.lCap
    rwa [rightProj_apply] at this
  have hZeq : y - rightProj U y = -(uM * (bCol w - U * Uᵀ * bCol w)ᵀ)
      + ε • (aM * (cCol μ w - U * Uᵀ * cCol μ w)ᵀ) := by
    rw [← mul_transpose_sub, ← mul_transpose_sub, rightProj_apply, hy, hTG, hMG]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, hcap]
    module
  have hZnorm : ‖y - rightProj U y‖ ≤ ‖y‖ := (isOrthProj_rightProj hU).norm_sub_le y
  have hentry : ∀ i k, (y - rightProj U y) i k =
      -((fun i => uM i ()) i * (bCol w - U * Uᵀ * bCol w) k ())
        + ε * ((fun i => aM i ()) i * (cCol μ w - U * Uᵀ * cCol μ w) k ()) := by
    intro i k
    have e : ∀ (Y : Matrix m Unit ℝ) (W : Matrix n Unit ℝ), (Y * Wᵀ) i k = Y i () * W k () := by
      intro Y W
      simp [Matrix.mul_apply]
    rw [hZeq]
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, e, smul_eq_mul]
  obtain ⟨h1, h2⟩ := colwise_bound hc₀ hind hentry
  exact ⟨h1.trans (hZnorm.trans hynorm), h2.trans (hZnorm.trans hynorm)⟩

/-- **The K-step gives the limit equation** (arXiv 2505.19929, the second half of the proof of
Theorem 4.2): if the basis `U` contains `b` up to `d ε²` and `c` up to `d ε`, the macro part of the
K-step follows the limit flow and the micro part is `O(ε)`. -/
theorem kstep_estimate (hq : IsAngularQuad μ w) {U : Matrix n (Fin r) ℝ} (hU : Uᵀ * U = 1)
    {D : Matrix m m ℝ} {ε t₀ t₁ h C d : ℝ} {G₀ : Matrix m n ℝ} {K v : ℝ → Matrix m n ℝ}
    (hK : ODESolution (relaxField (macroP w) (rightProj U) (transport D μ) ε) K t₀ t₁)
    (hK₀ : K t₀ = rightProj U G₀) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hετ : 2 * ε * (‖D‖ * ‖diagonal μ‖) ≤ 1) (ht₁ : t₁ = t₀ + h) (hh : 0 < h)
    (hC : Real.exp (2 * (‖D‖ * ‖diagonal μ‖) ^ 2 * h) * ‖G₀‖ ≤ C) (hd : 0 ≤ d)
    (hβ : ‖bCol w - U * Uᵀ * bCol w‖ ≤ d * ε ^ 2)
    (hγ : ‖cCol μ w - U * Uᵀ * cCol μ w‖ ≤ d * ε)
    (hvc : ContinuousOn v (Icc t₀ t₁))
    (hv : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt v
      (macroP w (transport D μ (transport D μ (macroP w (v t))))) (Ici t) t) :
    ‖macroP w (K t₁) - v t₁‖ ≤ Real.exp ((‖D‖ * ‖diagonal μ‖) ^ 2 * h) *
        (‖macroP w G₀ - v t₀‖ + ε * (d * C + 6 * C * (‖D‖ * ‖diagonal μ‖)
          + ((‖D‖ * ‖diagonal μ‖) * ‖D‖ * d + 2 * (‖D‖ * ‖diagonal μ‖) ^ 3
            + 3 * (‖D‖ * ‖diagonal μ‖) * d + d ^ 2) * C * h)) ∧
      ‖K t₁ - macroP w (K t₁)‖ ≤ ε * ((h⁻¹ + (‖D‖ * ‖diagonal μ‖) + d) * C) := by
  set τ := ‖D‖ * ‖diagonal μ‖ with hτdef
  have hτ0 : 0 ≤ τ := by positivity
  have sys := relaxSystemK (μ := μ) (m := m) hq hU D
  set δ := ‖bCol w - U * Uᵀ * bCol w‖ with hδdef
  set γ := ‖cCol μ w - U * Uᵀ * cCol μ w‖ with hγdef
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hγ0 : 0 ≤ γ := norm_nonneg _
  have hab : t₀ ≤ t₁ := by linarith
  have hR : rightProj U (K t₀) = K t₀ := by rw [hK₀]; exact sys.projR.idem _
  have hG0 : ‖K t₀‖ ≤ ‖G₀‖ := by rw [hK₀]; exact sys.projR.norm_le _
  have hexp1 : 1 ≤ Real.exp (2 * τ ^ 2 * h) := Real.one_le_exp (by positivity)
  have hGC : ‖G₀‖ ≤ C := le_trans (by nlinarith [norm_nonneg G₀]) hC
  have hbound : ∀ t ∈ Icc t₀ t₁, ‖K t‖ ≤ C :=
    apriori_of_exp sys hε hετ hK hR ht₁ (hC.trans' (mul_le_mul_of_nonneg_left hG0 (by positivity)))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hGC
  set c := ε⁻¹ with hc
  have hcpos : 0 < c := inv_pos.2 hε
  have hcε : c * ε = 1 := inv_mul_cancel₀ hε.ne'
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have htt : t₁ - t₀ = h := by rw [ht₁]; ring
  -- `e1 = δ / ε` is `O(ε)`
  set e1 := c * δ with he1
  have he10 : 0 ≤ e1 := by positivity
  have he1le : e1 ≤ d * ε := by
    have : c * δ ≤ c * (d * ε ^ 2) := mul_le_mul_of_nonneg_left hβ hcpos.le
    calc e1 ≤ c * (d * ε ^ 2) := this
      _ = (c * ε) * (d * ε) := by ring
      _ = d * ε := by rw [hcε, one_mul]
  constructor
  · have hmacro := sys.macro_le hε hετ hK hR hbound hvc hv t₁ ⟨hab, le_rfl⟩
    rw [htt] at hmacro
    refine hmacro.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    -- the initial error
    have h1 : ‖macroP w (K t₀) - v t₀‖ ≤ ‖macroP w G₀ - v t₀‖ + ε * (d * C) := by
      have h2 : macroP w (K t₀) - v t₀ = (macroP w G₀ - v t₀) - macroP w (G₀ - rightProj U G₀) := by
        rw [hK₀, map_sub]
        abel
      rw [h2]
      refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
      calc _ ≤ δ * ‖G₀‖ := sys.defect_adj G₀
        _ ≤ (d * ε ^ 2) * C := mul_le_mul hβ hGC (norm_nonneg _) (by positivity)
        _ ≤ (d * ε) * C := by gcongr
        _ = _ := by ring
    -- the forcing
    have h3 : c * τ * ((ε * (‖D‖ * γ) + 2 * τ ^ 2 * ε ^ 2 + 2 * δ) * C) + c * δ * τ * C
        + c ^ 2 * δ ^ 2 * C ≤ ε * ((τ * ‖D‖ * d + 2 * τ ^ 3 + 3 * τ * d + d ^ 2) * C) := by
      have h4 : c * τ * ((ε * (‖D‖ * γ) + 2 * τ ^ 2 * ε ^ 2 + 2 * δ) * C) + c * δ * τ * C
          + c ^ 2 * δ ^ 2 * C = (τ * ‖D‖ * γ * (c * ε) + 2 * τ ^ 3 * ε * (c * ε) + 3 * τ * e1
            + e1 ^ 2) * C := by
        rw [he1]; ring
      rw [h4, hcε, mul_one, mul_one, show ε * ((τ * ‖D‖ * d + 2 * τ ^ 3 + 3 * τ * d + d ^ 2) * C)
        = (ε * (τ * ‖D‖ * d + 2 * τ ^ 3 + 3 * τ * d + d ^ 2)) * C by ring]
      refine mul_le_mul_of_nonneg_right ?_ hC0
      have h5 : τ * ‖D‖ * γ ≤ τ * ‖D‖ * (d * ε) := by gcongr
      have h6 : 3 * τ * e1 ≤ 3 * τ * (d * ε) := by gcongr
      have h7 : e1 ^ 2 ≤ d ^ 2 * ε := by
        have := pow_le_pow_left₀ he10 he1le 2
        have h8 : (d * ε) ^ 2 = d ^ 2 * ε ^ 2 := by ring
        rw [h8] at this
        exact this.trans (by gcongr)
      nlinarith
    have h9 := mul_le_mul_of_nonneg_right h3 hh.le
    calc _ ≤ (‖macroP w G₀ - v t₀‖ + ε * (d * C)) + 6 * C * τ * ε
          + ε * ((τ * ‖D‖ * d + 2 * τ ^ 3 + 3 * τ * d + d ^ 2) * C) * h :=
          add_le_add (add_le_add h1 le_rfl) h9
      _ = _ := by ring
  · have hmicro := sys.micro_le hε hK hR hbound t₁ ⟨hab, le_rfl⟩
    rw [htt] at hmicro
    refine hmicro.trans ?_
    have hgC : ‖K t₀ - macroP w (K t₀)‖ ≤ C :=
      (sys.projM.norm_sub_le _).trans (hbound t₀ ⟨le_rfl, hab⟩)
    have hexp : Real.exp (-(c ^ 2) * h) ≤ ε * h⁻¹ := exp_neg_sq_le hε hε1 hh
    have h1 : Real.exp (-(c ^ 2) * h) * ‖K t₀ - macroP w (K t₀)‖ ≤ (ε * h⁻¹) * C :=
      mul_le_mul hexp hgC (norm_nonneg _) (by positivity)
    have h2 : (ε * τ + δ) * C ≤ (ε * τ + d * ε) * C := by
      refine mul_le_mul_of_nonneg_right ?_ hC0
      nlinarith
    calc _ ≤ (ε * h⁻¹) * C + (ε * τ + d * ε) * C := add_le_add h1 h2
      _ = _ := by ring

end Systems

section Limit

variable {μ w : n → ℝ} {r : ℕ}

/-- A vector as a column matrix. -/
def colV (ρ : m → ℝ) : Matrix m Unit ℝ := Matrix.of fun i _ => ρ i

lemma iso_mul_sDiag (ρ : m → ℝ) :
    (iso ρ : Matrix m n ℝ) * sDiag w = colV ρ * (bCol w)ᵀ := by
  ext i j
  simp [iso, colV, sDiag, bCol, Matrix.mul_apply, Matrix.diagonal_apply]

lemma colV_mulVec (A : Matrix m m ℝ) (ρ : m → ℝ) : colV (A.mulVec ρ) = A * colV ρ := by
  ext i j
  simp [colV, Matrix.mul_apply, Matrix.mulVec, dotProduct]

lemma colV_smul (a : ℝ) (ρ : m → ℝ) : colV (a • ρ) = a • colV ρ := by
  ext i j
  simp [colV]

lemma iso_sub (a b : m → ℝ) : (iso (a - b) : Matrix m n ℝ) = iso a - iso b := by
  ext i j
  simp [iso]

lemma macroP_iso (hq : IsAngularQuad μ w) (ρ : m → ℝ) :
    macroP w ((iso ρ : Matrix m n ℝ) * sDiag w) = (iso ρ : Matrix m n ℝ) * sDiag w := by
  rw [macroP_apply, iso_mul_sDiag, Matrix.mul_assoc (colV ρ), bCol_orth hq, Matrix.mul_one]

/-- The limit operator: `M T T M (ρ 𝟙ᵀ) = ⅓ (A² ρ) 𝟙ᵀ`.  This is `⟨μ²⟩ / 2 = 1/3`. -/
lemma limit_op (hq : IsAngularQuad μ w) (A : Matrix m m ℝ) (ρ : m → ℝ) :
    macroP w (transport A μ (transport A μ (macroP w ((iso ρ : Matrix m n ℝ) * sDiag w)))) =
      (iso ((1 / 3 : ℝ) • (A * A).mulVec ρ) : Matrix m n ℝ) * sDiag w := by
  have hcc : (bCol w)ᵀ * diagonal μ * (diagonal μ * bCol w) = (1 / 3 : ℝ) • 1 := by
    rw [← cCol_transpose]
    exact cCol_cCol hq
  rw [macroP_iso hq, iso_mul_sDiag, iso_mul_sDiag, transport_apply, transport_apply, macroP_apply,
    colV_smul, colV_mulVec]
  calc A * (A * (colV ρ * (bCol w)ᵀ) * diagonal μ) * diagonal μ * bCol w * (bCol w)ᵀ
      = A * A * colV ρ * ((bCol w)ᵀ * diagonal μ * (diagonal μ * bCol w)) * (bCol w)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hcc]; simp [Matrix.mul_smul, Matrix.smul_mul]

lemma density_col (hq : IsAngularQuad μ w) (F : Matrix m n ℝ) :
    F * sDiag w * bCol w = colV (density w F) := by
  ext i j
  have h : ∀ k, F i k * √(w k / 2) * √(w k / 2) = w k / 2 * F i k := fun k => by
    rw [mul_assoc, sqrt_sq_half hq]
    ring
  simp only [Matrix.mul_apply, sDiag, Matrix.diagonal_apply, bCol, colV, density, Matrix.of_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, h]

lemma macroP_mul_sDiag (hq : IsAngularQuad μ w) (F : Matrix m n ℝ) :
    macroP w (F * sDiag w) = (iso (density w F) : Matrix m n ℝ) * sDiag w := by
  rw [macroP_apply, density_col hq, iso_mul_sDiag]

lemma norm_le_iso (hq : IsAngularQuad μ w) (ρ : m → ℝ) :
    ‖ρ‖ ≤ ‖(iso ρ : Matrix m n ℝ) * sDiag w‖ := by
  have h : colV ρ = (iso ρ : Matrix m n ℝ) * sDiag w * bCol w := by
    rw [iso_mul_sDiag, Matrix.mul_assoc, bCol_orth hq, Matrix.mul_one]
  have h1 : ‖colV ρ‖ ≤ ‖(iso ρ : Matrix m n ℝ) * sDiag w‖ := by
    rw [h]
    exact norm_mul_le_of_orthonormal (bCol_orth hq) _
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact (abs_apply_le_norm (colV ρ) i ()).trans h1

/-- The inverse of the scaling. -/
noncomputable def sDiagInv (w : n → ℝ) : Matrix n n ℝ := diagonal fun k => (√(w k / 2))⁻¹

lemma sDiag_mul_inv (hq : IsAngularQuad μ w) : sDiag w * sDiagInv w = 1 := by
  rw [sDiag, sDiagInv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext k
  have : 0 < √(w k / 2) := Real.sqrt_pos.2 (by linarith [hq.pos k])
  exact mul_inv_cancel₀ this.ne'

lemma norm_le_weighted (hq : IsAngularQuad μ w) (F : Matrix m n ℝ) :
    ‖F‖ ≤ ‖F * sDiag w‖ * ‖sDiagInv w‖ := by
  have h : F = F * sDiag w * sDiagInv w := by
    rw [Matrix.mul_assoc, sDiag_mul_inv hq, Matrix.mul_one]
  calc ‖F‖ = ‖F * sDiag w * sDiagInv w‖ := by rw [← h]
    _ ≤ _ := Frobenius.norm_mul_le _ _

/-- `ρ ↦ ρ 𝟙ᵀ diag(√(w/2))` as a continuous linear map. -/
noncomputable def isoCLM (w : n → ℝ) : (m → ℝ) →L[ℝ] Matrix m n ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ρ => (iso ρ : Matrix m n ℝ) * sDiag w
      map_add' := fun a b => by
        have : (iso (a + b) : Matrix m n ℝ) = iso a + iso b := by ext i j; simp [iso]
        rw [this, Matrix.add_mul]
      map_smul' := fun c a => by
        have : (iso (c • a) : Matrix m n ℝ) = c • iso a := by ext i j; simp [iso]
        rw [this, Matrix.smul_mul]
        rfl }

lemma isoCLM_apply (ρ : m → ℝ) : isoCLM w ρ = (iso ρ : Matrix m n ℝ) * sDiag w := rfl

/-- The curve of the limit: it solves `v' = M T T M v`. -/
lemma heat_curve (hq : IsAngularQuad μ w) (A : Matrix m m ℝ) {ρ : ℝ → m → ℝ} {a b : ℝ}
    (hρ : ODESolution (fun _ r => (1 / 3 : ℝ) • (A * A).mulVec r) ρ a b) :
    ContinuousOn (fun t => (iso (ρ t) : Matrix m n ℝ) * sDiag w) (Icc a b) ∧
      ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => (iso (ρ t) : Matrix m n ℝ) * sDiag w)
        (macroP w (transport A μ (transport A μ
          (macroP w ((iso (ρ t) : Matrix m n ℝ) * sDiag w))))) (Ici t) t := by
  constructor
  · exact (isoCLM (m := m) w).continuous.comp_continuousOn hρ.cont
  · intro t ht
    have h := (isoCLM (m := m) w).hasFDerivAt.comp_hasDerivWithinAt t (hρ.deriv t ht)
    rw [limit_op hq]
    exact h

/-- **Theorem 4.1 of arXiv 2505.19929 for the semi-discrete RTE (5.1)** (the discrete setting of
Section 5 of the paper, with `∂ₓ` replaced by `D`).
For arbitrary `D` and arbitrary initial data `F₀` (no well-prepared data), the solution of (5.1)
satisfies, for fixed `t₁ > t₀`, `‖F(t₁) - ρ(t₁) 𝟙ᵀ‖ ≤ C ε`, where `ρ' = ⅓ D² ρ` with
`ρ(t₀) = ½ ∑ₖ wₖ F₀(·, k)`.  Differences from the paper: the discrete setting replaces the PDE,
the initial value of `ρ` is made explicit, `t₁ > t₀` is needed unless `F₀` is isotropic, and the
rate `O(ε)` is added. -/
theorem rte_diffusion_limit (hq : IsAngularQuad μ w) (D : Matrix m m ℝ) {t₀ t₁ : ℝ}
    (h01 : t₀ < t₁) (F₀ : Matrix m n ℝ) {ρ : ℝ → m → ℝ}
    (hρ : ODESolution (fun _ r => (1 / 3 : ℝ) • (D * D).mulVec r) ρ t₀ t₁)
    (hρ₀ : ρ t₀ = density w F₀) :
    ∃ C : ℝ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ F : ℝ → Matrix m n ℝ,
      ODESolution (fun _ Y => rte D μ w ε Y) F t₀ t₁ → F t₀ = F₀ →
        ‖F t₁ - iso (ρ t₁)‖ ≤ C * ε := by
  set τ := ‖D‖ * ‖diagonal μ‖ with hτdef
  have hτ0 : 0 ≤ τ := by positivity
  set h := t₁ - t₀ with hh'
  have hh : 0 < h := sub_pos.2 h01
  have ht₁ : t₁ = t₀ + h := by rw [hh']; ring
  set G₀ := F₀ * sDiag w with hG₀
  set C₀ := Real.exp (2 * τ ^ 2 * h) * ‖G₀‖ with hC₀
  have hC00 : 0 ≤ C₀ := by positivity
  have sys := relaxSystemFull (m := m) hq D
  set K₁ := Real.exp (τ ^ 2 * h) * (6 * C₀ * τ + 2 * τ ^ 3 * C₀ * h) + (h⁻¹ + τ) * C₀ with hK₁
  refine ⟨K₁ * ‖sDiagInv w‖, ?_⟩
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < 1 / (2 * τ + 1) ∧ ε < 1 := by
    have h1 : (0 : ℝ) < 1 / (2 * τ + 1) := by positivity
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h1),
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)] with ε h2 h3 h4
    exact ⟨h2, h3, h4⟩
  filter_upwards [hsmall] with ε hsm F hF hF₀
  obtain ⟨hε, hε1, hε2⟩ := hsm
  have hετ : 2 * ε * τ ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at hε1
    nlinarith
  have hG : ODESolution (relaxField (macroP w) 1 (transport D μ) ε) (fun t => F t * sDiag w)
      t₀ t₁ := odeSolution_mul_right (sDiag w) hF fun t Y => rte_mul_sDiag hq D ε t Y
  have hab : t₀ ≤ t₁ := h01.le
  have hbound : ∀ t ∈ Icc t₀ t₁, ‖F t * sDiag w‖ ≤ C₀ :=
    apriori_of_exp sys hε hετ hG rfl ht₁ (by simp only [hF₀]; exact le_rfl)
  obtain ⟨hvc, hv⟩ := heat_curve (μ := μ) (w := w) hq D hρ
  have hmacro := sys.macro_le hε hετ hG rfl hbound hvc hv t₁ ⟨hab, le_rfl⟩
  have hmicro := sys.micro_le hε hG rfl hbound t₁ ⟨hab, le_rfl⟩
  have htt : t₁ - t₀ = h := rfl
  have h0 : macroP w (F t₀ * sDiag w) - (iso (ρ t₀) : Matrix m n ℝ) * sDiag w = 0 := by
    rw [macroP_mul_sDiag hq, hF₀, hρ₀, sub_self]
  rw [h0, norm_zero, htt] at hmacro
  rw [htt] at hmicro
  set c := ε⁻¹ with hc
  have hcε : c * ε = 1 := inv_mul_cancel₀ hε.ne'
  have hmac2 : ‖macroP w (F t₁ * sDiag w) - (iso (ρ t₁) : Matrix m n ℝ) * sDiag w‖ ≤
      Real.exp (τ ^ 2 * h) * ((6 * C₀ * τ + 2 * τ ^ 3 * C₀ * h) * ε) := by
    refine hmacro.trans (le_of_eq ?_)
    have : c * τ * ((ε * 0 + 2 * τ ^ 2 * ε ^ 2 + 2 * 0) * C₀) + c * 0 * τ * C₀
        + c ^ 2 * 0 ^ 2 * C₀ = 2 * τ ^ 3 * C₀ * ε * (c * ε) := by ring
    rw [this, hcε]
    ring
  have hexp := exp_neg_sq_le hε hε2.le hh
  have hgC : ‖F t₀ * sDiag w - macroP w (F t₀ * sDiag w)‖ ≤ C₀ :=
    (sys.projM.norm_sub_le _).trans (hbound t₀ ⟨le_rfl, hab⟩)
  have hmic2 : ‖F t₁ * sDiag w - macroP w (F t₁ * sDiag w)‖ ≤ ((h⁻¹ + τ) * C₀) * ε := by
    refine hmicro.trans ?_
    have h1 := mul_le_mul hexp hgC (norm_nonneg _) (by positivity)
    calc _ ≤ ε * h⁻¹ * C₀ + (ε * τ + 0) * C₀ := add_le_add h1 le_rfl
      _ = _ := by ring
  have hsum : ‖(F t₁ - iso (ρ t₁)) * sDiag w‖ ≤ K₁ * ε := by
    have h2 : (F t₁ - iso (ρ t₁)) * sDiag w = (F t₁ * sDiag w - macroP w (F t₁ * sDiag w))
        + (macroP w (F t₁ * sDiag w) - (iso (ρ t₁) : Matrix m n ℝ) * sDiag w) := by
      rw [Matrix.sub_mul]
      abel
    rw [h2]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ ((h⁻¹ + τ) * C₀) * ε
          + Real.exp (τ ^ 2 * h) * ((6 * C₀ * τ + 2 * τ ^ 3 * C₀ * h) * ε) :=
          add_le_add hmic2 hmac2
      _ = _ := by rw [hK₁]; ring
  calc _ ≤ ‖(F t₁ - iso (ρ t₁)) * sDiag w‖ * ‖sDiagInv w‖ := norm_le_weighted hq _
    _ ≤ (K₁ * ε) * ‖sDiagInv w‖ := by gcongr
    _ = _ := by ring

/-- **One GAP step on the RTE, with constants uniform in the data.**  Let `n₀` bound the input and
`c₀` the independence of the density of `ℓ t₁` and its projected gradient.  Then for small `ε`
the density error is propagated by the limit flow up to `O(ε)`, and the micro part of the output
is `O(ε)`.  This is the quantitative form of the step of Theorem 4.2 of arXiv 2505.19929.  The
data may depend on `ε`, which is what a run of the scheme needs. -/
theorem gap_step_estimate (hq : IsAngularQuad μ w) (D : Matrix m m ℝ) {h n₀ c₀ : ℝ} (hh : 0 < h)
    (hn₀ : 0 ≤ n₀) (hc₀ : 0 < c₀) :
    ∃ A B ε₀ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∀ (t₀ t₁ : ℝ) (X : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (F₀ : Matrix m n ℝ)
        (ℓ k : ℝ → Matrix m n ℝ) (ρ : ℝ → m → ℝ), t₁ = t₀ + h →
        IsRTEGAPStep D μ w ε t₀ t₁ X V F₀ ℓ k → ‖F₀ * sDiag w‖ ≤ n₀ →
        UniformlyIndep c₀ (density w (ℓ t₁)) ((X * Xᵀ * D).mulVec (density w (ℓ t₁))) →
        ODESolution (fun _ r => (1 / 3 : ℝ) • (D * D).mulVec r) ρ t₀ t₁ →
        ‖(iso (density w (k t₁) - ρ t₁) : Matrix m n ℝ) * sDiag w‖ ≤
            Real.exp ((‖D‖ * ‖diagonal μ‖) ^ 2 * h) *
              (‖(iso (density w F₀ - ρ t₀) : Matrix m n ℝ) * sDiag w‖ + ε * A) ∧
          ‖k t₁ * sDiag w - (iso (density w (k t₁)) : Matrix m n ℝ) * sDiag w‖ ≤ ε * B ∧
          ‖k t₁ * sDiag w‖ ≤ Real.exp (2 * (‖D‖ * ‖diagonal μ‖) ^ 2 * h) * ‖F₀ * sDiag w‖ := by
  set τ := ‖D‖ * ‖diagonal μ‖ with hτdef
  have hτ0 : 0 ≤ τ := by positivity
  set C := Real.exp (2 * τ ^ 2 * h) * n₀ with hCdef
  have hC0 : 0 ≤ C := by positivity
  set d := (6 / h + 2 * τ ^ 2) * C / c₀ with hddef
  have hd0 : 0 ≤ d := by positivity
  refine ⟨d * C + 6 * C * τ + (τ * ‖D‖ * d + 2 * τ ^ 3 + 3 * τ * d + d ^ 2) * C * h,
    (h⁻¹ + τ + d) * C, min 1 (1 / (2 * τ + 1)), by positivity, by positivity, by positivity, ?_⟩
  intro ε hε hε₀ t₀ t₁ X V F₀ ℓ k ρ ht₁ hs hn hind hρ
  have hε1 : ε ≤ 1 := (hε₀.trans_le (min_le_left _ _)).le
  have hετ : 2 * ε * τ ≤ 1 := by
    have h1 := hε₀.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith
  have hN := hs.normalized hq
  have hU := angBasis_orth hq hs.orthoV
  set U := angBasis w V with hUdef
  set G₀ := F₀ * sDiag w with hG₀
  have hC : Real.exp (2 * τ ^ 2 * h) * ‖G₀‖ ≤ C := by
    rw [hCdef]
    gcongr
  have hindN : UniformlyIndep c₀ (fun i => (ℓ t₁ * sDiag w * bCol w) i ())
      (fun i => (X * Xᵀ * D * (ℓ t₁ * sDiag w * bCol w)) i ()) := by
    have h1 : (fun i => (ℓ t₁ * sDiag w * bCol w) i ()) = density w (ℓ t₁) := by
      rw [density_col hq]
      rfl
    have h2 : (fun i => (X * Xᵀ * D * (ℓ t₁ * sDiag w * bCol w)) i ())
        = (X * Xᵀ * D).mulVec (density w (ℓ t₁)) := by
      rw [density_col hq, ← colV_mulVec]
      rfl
    rw [h1, h2]
    exact hind
  obtain ⟨h1, h2⟩ := lstep_capture hq hs.orthoX hU hN hε hετ ht₁ hh hC hc₀.le hindN
  have hβ : ‖bCol w - U * Uᵀ * bCol w‖ ≤ d * ε ^ 2 := by
    rw [hddef, div_mul_eq_mul_div, le_div_iff₀ hc₀]
    linarith
  have hγ : ‖cCol μ w - U * Uᵀ * cCol μ w‖ ≤ d * ε := by
    rw [hddef, div_mul_eq_mul_div, le_div_iff₀ hc₀]
    have h3 : (‖cCol μ w - U * Uᵀ * cCol μ w‖ * c₀) * ε ≤ ((6 / h + 2 * τ ^ 2) * C * ε) * ε := by
      nlinarith
    exact le_of_mul_le_mul_right h3 hε
  have hK : ODESolution (relaxField (macroP w) (rightProj U) (transport D μ) ε)
      (fun t => k t * sDiag w) t₀ t₁ := hN.kSol
  obtain ⟨hvc, hv⟩ := heat_curve (μ := μ) (w := w) hq D hρ
  obtain ⟨h3, h4⟩ := kstep_estimate hq hU hK hN.kStart hε hε1 hετ ht₁ hh hC hd0 hβ hγ hvc hv
  have hsys := relaxSystemK (μ := μ) (m := m) hq hU D
  have hR : rightProj U (k t₀ * sDiag w) = k t₀ * sDiag w := by
    rw [hN.kStart]
    exact hN.projQ₁.idem _
  have htt : t₁ - t₀ = h := by rw [ht₁]; ring
  have hab : t₁ ∈ Icc t₀ t₁ := ⟨by linarith, le_rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [macroP_mul_sDiag hq, macroP_mul_sDiag hq, ← Matrix.sub_mul, ← Matrix.sub_mul, ← iso_sub,
      ← iso_sub] at h3
    exact h3
  · rw [macroP_mul_sDiag hq] at h4
    exact h4
  · have h5 := hsys.apriori hε hετ hK hR t₁ hab
    rw [htt] at h5
    refine h5.trans ?_
    have h6 : ‖k t₀ * sDiag w‖ ≤ ‖G₀‖ := by
      rw [hN.kStart]
      exact hN.projQ₁.norm_le _
    gcongr

end Limit

section Counterexample

/-- The central difference on the periodic grid with four points and `Δx = 1`. -/
noncomputable def cexD : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1 / 2, 0, -1 / 2; -1 / 2, 0, 1 / 2, 0; 0, -1 / 2, 0, 1 / 2; 1 / 2, 0, -1 / 2, 0]

/-- The nodes of the three-point Gauss–Legendre rule. -/
noncomputable def cexμ : Fin 3 → ℝ := ![-√(3 / 5), 0, √(3 / 5)]

/-- The weights of the three-point Gauss–Legendre rule. -/
noncomputable def cexw : Fin 3 → ℝ := ![5 / 9, 8 / 9, 5 / 9]

/-- The density of the counterexample, an eigenvector of `D²`. -/
def cexz : Fin 4 → ℝ := ![1, 1, -1, -1]

/-- The orthonormal spatial basis: the normalized `z` and the constant. -/
noncomputable def cexX : Matrix (Fin 4) (Fin 2) ℝ :=
  !![1 / 2, 1 / 2; 1 / 2, 1 / 2; -1 / 2, 1 / 2; -1 / 2, 1 / 2]

/-- `1 / √2`. -/
noncomputable def cexα : ℝ := (√2)⁻¹

/-- `1 / √40`. -/
noncomputable def cexβ : ℝ := (√40)⁻¹

/-- The basis of `span {1, P₂(μ)}`, orthonormal for the Gauss–Legendre weights; at the nodes
`P₂(μ) ∝ (4, -5, 4)`. -/
noncomputable def cexV : Matrix (Fin 3) (Fin 2) ℝ :=
  !![cexα, 4 * cexβ; cexα, -5 * cexβ; cexα, 4 * cexβ]

/-- The isotropic part `z 𝟙ᵀ`. -/
def cexI : Matrix (Fin 4) (Fin 3) ℝ := !![1, 1, 1; 1, 1, 1; -1, -1, -1; -1, -1, -1]

/-- The anisotropic part: the constant in space times `P₂(μ)`. -/
def cexB : Matrix (Fin 4) (Fin 3) ℝ := !![4, -5, 4; 4, -5, 4; 4, -5, 4; 4, -5, 4]

/-- The exact L- and K-flow of the counterexample: `z 𝟙ᵀ + e^{-t/ε²} 𝟙 P₂ᵀ`. -/
noncomputable def cexF (ε t : ℝ) : Matrix (Fin 4) (Fin 3) ℝ :=
  cexI + Real.exp (-(ε⁻¹ ^ 2) * t) • cexB

/-- The solution `ρ(t) = e^{-t/3} z` of the limit equation. -/
noncomputable def cexρ (t : ℝ) : Fin 4 → ℝ := Real.exp (-(1 / 3) * t) • cexz

/-- The action of `V Vᵀ diag(w)` from the right. -/
noncomputable def cexQ : Matrix (Fin 3) (Fin 3) ℝ := !![1 / 2, 0, 1 / 2; 0, 1, 0; 1 / 2, 0, 1 / 2]

lemma cex_s : √(3 / 5 : ℝ) * √(3 / 5) = 3 / 5 := Real.mul_self_sqrt (by norm_num)

lemma cex_α : cexα * cexα = 1 / 2 := by
  have h : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp only [cexα]
  rw [← mul_inv, h]
  norm_num

lemma cex_β : cexβ * cexβ = 1 / 40 := by
  have h : (√40 : ℝ) * √40 = 40 := Real.mul_self_sqrt (by norm_num)
  simp only [cexβ]
  rw [← mul_inv, h]
  norm_num

/-- The Gauss–Legendre rule with three nodes (arXiv 2505.19929, Section 5) satisfies the moment
conditions. -/
theorem cex_quad : IsAngularQuad cexμ cexw where
  pos k := by fin_cases k <;> norm_num [cexw]
  mass := by norm_num [cexw, Fin.sum_univ_three]
  first := by
    simp only [Fin.sum_univ_three, cexw, cexμ]
    norm_num
  second := by
    have h := cex_s
    rw [Fin.sum_univ_three]
    change (5 / 9 : ℝ) * (-√(3 / 5)) ^ 2 + 8 / 9 * 0 ^ 2 + 5 / 9 * (√(3 / 5)) ^ 2 = 2 / 3
    linear_combination (10 / 9 : ℝ) * h

/-- `cexD` is the periodic central difference. -/
lemma cexD_mulVec (z : Fin 4 → ℝ) :
    cexD.mulVec z = ![(z 1 - z 3) / 2, (z 2 - z 0) / 2, (z 3 - z 1) / 2, (z 0 - z 2) / 2] := by
  ext j
  fin_cases j <;> simp [cexD, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

lemma cexI_eq : (iso cexz : Matrix (Fin 4) (Fin 3) ℝ) = cexI := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [iso, cexz, cexI]

lemma cex_mulVec : (cexD * cexD).mulVec cexz = -cexz := by
  ext i
  fin_cases i <;>
    simp [cexD, cexz, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

lemma cexX_orth : cexXᵀ * cexX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cexX, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

lemma cexV_orth : cexVᵀ * diagonal cexw * cexV = 1 := by
  have h1 := cex_α
  have h2 := cex_β
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cexV, cexw, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]
  · linear_combination 2 * h1
  · ring
  · ring
  · linear_combination 40 * h2

set_option linter.flexible false in
lemma cexV_proj : diagonal cexw * cexV * cexVᵀ = cexQ := by
  have h1 := cex_α
  have h2 := cex_β
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cexV, cexw, cexQ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
  all_goals first
    | linear_combination (5 / 9 : ℝ) * h1 + (80 / 9 : ℝ) * h2
    | linear_combination (8 / 9 : ℝ) * h1 + (200 / 9 : ℝ) * h2
    | linear_combination (5 / 9 : ℝ) * h1 - (100 / 9 : ℝ) * h2
    | linear_combination (8 / 9 : ℝ) * h1 - (160 / 9 : ℝ) * h2

lemma cex_DB : cexD * cexB = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cexD, cexB, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

lemma cexI_W : cexI * Wmat cexw = cexI := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cexI, cexw, Wmat, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

lemma cexB_W : cexB * Wmat cexw = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cexB, cexw, Wmat, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-- The spatial projector `X Xᵀ`. -/
noncomputable def cexP : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1 / 2, 1 / 2, 0, 0; 1 / 2, 1 / 2, 0, 0; 0, 0, 1 / 2, 1 / 2; 0, 0, 1 / 2, 1 / 2]

lemma cexX_proj : cexX * cexXᵀ = cexP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cexX, cexP, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

lemma cex_PI : cexX * cexXᵀ * cexI = cexI := by
  rw [cexX_proj]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cexP, cexI, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

lemma cex_PB : cexX * cexXᵀ * cexB = cexB := by
  rw [cexX_proj]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cexP, cexB, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

lemma cex_PDI : cexX * cexXᵀ * (cexD * cexI) = 0 := by
  rw [cexX_proj]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cexP, cexD, cexI, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

lemma cex_PY : cexX * cexXᵀ * (cexD * cexI * diagonal cexμ) = 0 := by
  rw [← Matrix.mul_assoc, cex_PDI, Matrix.zero_mul]

lemma cex_IQ : cexI * cexQ = cexI := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cexI, cexQ, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

lemma cex_BQ : cexB * cexQ = cexB := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cexB, cexQ, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

lemma cex_YQ : cexD * cexI * diagonal cexμ * cexQ = 0 := by
  have h : diagonal cexμ * cexQ = !![-(√(3 / 5)) / 2, 0, -(√(3 / 5)) / 2; 0, 0, 0;
      √(3 / 5) / 2, 0, √(3 / 5) / 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cexμ, cexQ, Matrix.diagonal_mul] <;> ring
  rw [Matrix.mul_assoc, h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cexD, cexI, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

lemma cex_rte (ε t : ℝ) : rte cexD cexμ cexw ε (cexF ε t) =
    -(ε⁻¹ • (cexD * cexI * diagonal cexμ))
      - (ε⁻¹ ^ 2 * Real.exp (-(ε⁻¹ ^ 2) * t)) • cexB := by
  simp only [rte, cexF, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, cex_DB,
    cexI_W, cexB_W, smul_zero, add_zero]
  module

lemma cex_deriv (ε t : ℝ) : HasDerivAt (cexF ε)
    (-(ε⁻¹ ^ 2 * Real.exp (-(ε⁻¹ ^ 2) * t)) • cexB) t := by
  have h1 : HasDerivAt (fun t => -(ε⁻¹ ^ 2) * t) (-(ε⁻¹ ^ 2)) t := by
    simpa only [mul_one] using (hasDerivAt_id' t).const_mul (-(ε⁻¹ ^ 2))
  have h2 : HasDerivAt (cexF ε) ((Real.exp (-(ε⁻¹ ^ 2) * t) * -(ε⁻¹ ^ 2)) • cexB) t :=
    (h1.exp.smul_const cexB).const_add cexI
  have h3 : -(ε⁻¹ ^ 2 * Real.exp (-(ε⁻¹ ^ 2) * t)) = Real.exp (-(ε⁻¹ ^ 2) * t) * -(ε⁻¹ ^ 2) := by
    ring
  rw [h3]
  exact h2

lemma cex_cont (ε : ℝ) (a b : ℝ) : ContinuousOn (cexF ε) (Icc a b) :=
  fun t _ => (cex_deriv ε t).continuousAt.continuousWithinAt

/-- The flow `cexF` is, for every `ε`, an exact GAP step (arXiv 2505.19929, Algorithm 2.3) from each
of its points, with the same bases: the scheme never leaves `span {z, 𝟙} ⊗ span {1, P₂}`. -/
theorem cex_step (ε t₀ t₁ : ℝ) :
    IsRTEGAPStep cexD cexμ cexw ε t₀ t₁ cexX cexV (cexF ε t₀) (cexF ε) (cexF ε) where
  orthoX := cexX_orth
  start := by
    simp only [cexF, Matrix.mul_add, Matrix.mul_smul, cex_PI, cex_PB]
  lSol := ⟨cex_cont ε _ _, fun t _ => by
    have h : cexX * cexXᵀ * rte cexD cexμ cexw ε (cexF ε t)
        = -(ε⁻¹ ^ 2 * Real.exp (-(ε⁻¹ ^ 2) * t)) • cexB := by
      rw [cex_rte, Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_smul, cex_PY,
        cex_PB]
      simp
    rw [h]
    exact (cex_deriv ε t).hasDerivWithinAt⟩
  lStart := rfl
  orthoV := cexV_orth
  capture := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal cexw), cexV_proj]
    simp only [cexF, Matrix.add_mul, Matrix.smul_mul, cex_IQ, cex_BQ]
  kSol := ⟨cex_cont ε _ _, fun t _ => by
    have h : rte cexD cexμ cexw ε (cexF ε t) * diagonal cexw * cexV * cexVᵀ
        = -(ε⁻¹ ^ 2 * Real.exp (-(ε⁻¹ ^ 2) * t)) • cexB := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal cexw), cexV_proj,
        cex_rte, Matrix.sub_mul, Matrix.neg_mul, Matrix.smul_mul, Matrix.smul_mul, cex_YQ, cex_BQ]
      simp
    rw [h]
    exact (cex_deriv ε t).hasDerivWithinAt⟩
  kStart := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal cexw), cexV_proj]
    simp only [cexF, Matrix.add_mul, Matrix.smul_mul, cex_IQ, cex_BQ]

/-- The density of the counterexample is `z`, for all `ε` and `t`. -/
lemma cex_density (ε t : ℝ) : density cexw (cexF ε t) = cexz := by
  ext i
  fin_cases i <;>
    simp [density, cexF, cexI, cexB, cexw, cexz, Fin.sum_univ_three] <;> ring

lemma cex_heat_of (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.mulVec cexz = -cexz) (a b : ℝ) :
    ODESolution (fun _ r => (1 / 3 : ℝ) • M.mulVec r) cexρ a b := by
  have hd : ∀ t, HasDerivAt cexρ ((1 / 3 : ℝ) • M.mulVec (cexρ t)) t := fun t => by
    have h1 : HasDerivAt (fun t => -(1 / 3 : ℝ) * t) (-(1 / 3)) t := by
      simpa only [mul_one] using (hasDerivAt_id' t).const_mul (-(1 / 3 : ℝ))
    have h2 : HasDerivAt cexρ ((Real.exp (-(1 / 3) * t) * -(1 / 3)) • cexz) t :=
      h1.exp.smul_const cexz
    have h3 : (1 / 3 : ℝ) • M.mulVec (cexρ t)
        = (Real.exp (-(1 / 3) * t) * -(1 / 3)) • cexz := by
      simp only [cexρ, Matrix.mulVec_smul, hM]
      module
    rw [h3]
    exact h2
  exact ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => (hd t).hasDerivWithinAt⟩

/-- `ρ(t) = e^{-t/3} z` solves the limit equation (4.3) of arXiv 2505.19929, `ρ' = ⅓ D² ρ`. -/
theorem cex_heat (a b : ℝ) :
    ODESolution (fun _ r => (1 / 3 : ℝ) • (cexD * cexD).mulVec r) cexρ a b :=
  cex_heat_of _ cex_mulVec a b

lemma cex_ρ_zero : cexρ 0 = cexz := by
  simp [cexρ]

/-- In the counterexample to Theorem 4.2 of arXiv 2505.19929 the projected gradient of the density
vanishes, so the independence hypothesis of `gap_step_estimate` fails for every `c₀ > 0`. -/
theorem cex_not_indep {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ¬ UniformlyIndep c₀ cexz ((cexX * cexXᵀ * cexD).mulVec cexz) := by
  intro h
  have h0 : (cexX * cexXᵀ * cexD).mulVec cexz = 0 := by
    rw [cexX_proj]
    ext i
    fin_cases i <;>
      simp [cexP, cexD, cexz, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_four]
  have := h 0 1
  rw [h0] at this
  simp at this
  linarith

/-- The lower bound behind `theorem_4_2_false` (arXiv 2505.19929, Theorem 4.2). -/
theorem cex_lower_bound (ε t : ℝ) :
    1 - Real.exp (-(1 / 3) * t) ≤ ‖cexF ε t - iso (cexρ t)‖ := by
  set A : Matrix (Fin 4) (Fin 3) ℝ := cexF ε t - iso (cexρ t) with hA
  have h1 := abs_apply_le_norm A 0 0
  have h2 := abs_apply_le_norm A 2 0
  have e1 : A 0 0 = 1 + 4 * Real.exp (-(ε⁻¹ ^ 2) * t) - Real.exp (-(1 / 3) * t) := by
    change cexF ε t 0 0 - cexρ t 0 = _
    simp only [cexρ, cexz, cexF, cexI, cexB]
    simp
    ring
  have e2 : A 2 0 = -1 + 4 * Real.exp (-(ε⁻¹ ^ 2) * t) + Real.exp (-(1 / 3) * t) := by
    change cexF ε t 2 0 - cexρ t 2 = _
    simp only [cexρ, cexz, cexF, cexI, cexB]
    simp
    ring
  rw [e1] at h1
  rw [e2] at h2
  have h3 := abs_le.1 h1
  have h4 := abs_le.1 h2
  linarith [h3.2, h4.1]

lemma cexF_zero (ε : ℝ) : cexF ε 0 = cexI + cexB := by
  simp [cexF]

lemma cex_rank_aux {c : ℝ} (hc0 : c ≠ 0) : 2 ≤ (cexI + c • cexB).rank := by
  let P₁ : Matrix (Fin 2) (Fin 4) ℝ := !![1, 0, 0, 0; 0, 0, 1, 0]
  let P₂ : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; 0, 0]
  have hS : P₁ * (cexI + c • cexB) * P₂ = !![1 + 4 * c, 1 - 5 * c; -1 + 4 * c, -1 - 5 * c] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P₁, P₂, cexI, cexB, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  have hdet : (!![1 + 4 * c, 1 - 5 * c; -1 + 4 * c, -1 - 5 * c] : Matrix (Fin 2) (Fin 2) ℝ).det
      = -18 * c := by
    rw [Matrix.det_fin_two_of]
    ring
  have hu : IsUnit (P₁ * (cexI + c • cexB) * P₂) := by
    rw [hS, Matrix.isUnit_iff_isUnit_det, hdet]
    exact (mul_ne_zero (by norm_num) hc0).isUnit
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 : (P₁ * (cexI + c • cexB) * P₂).rank ≤ (cexI + c • cexB).rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  rw [h1] at h2
  simpa using h2

/-- The flow of the counterexample has rank at least two, so `F₀` lies in `ℳ₂` and `cexV` is an
orthonormal basis of the corange of the L-step, not a completion of a smaller one
(arXiv 2505.19929, (2.3) and Algorithm 2.3). -/
theorem cex_rank (ε t : ℝ) : 2 ≤ (cexF ε t).rank :=
  cex_rank_aux (Real.exp_pos _).ne'

/-- `cexF` does not converge to the solution of the limit equation (arXiv 2505.19929,
Theorem 4.2). -/
theorem cex_not_tendsto {t : ℝ} (ht : 0 < t) :
    ¬ Tendsto (fun ε => cexF ε t) (𝓝[>] 0) (𝓝 (iso (cexρ t))) := by
  intro h
  have h1 : Tendsto (fun ε => ‖cexF ε t - iso (cexρ t)‖) (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero).1 h
    exact this
  have h2 : (0 : ℝ) < 1 - Real.exp (-(1 / 3) * t) := by
    have := Real.exp_lt_exp.2 (show -(1 / 3) * t < 0 by linarith)
    rw [Real.exp_zero] at this
    linarith
  have h3 := ge_of_tendsto' h1 fun ε => cex_lower_bound ε t
  linarith

/-- **Theorem 4.2 of arXiv 2505.19929 is false as stated, in the semi-discrete setting of Section
5** (to which the paper says its asymptotic analysis applies, p. 14). Take the setting of Section 5
of the paper: the periodic central difference on four points (`cexD`, see `cexD_mulVec`), the
three-point Gauss–Legendre rule, `r = 2`, and the input `F₀ = z 𝟙ᵀ + 𝟙 P₂ᵀ` of rank two
(`cex_rank`), with `z = (1, 1, -1, -1)`, `X = span {z, 𝟙}`, `V = span {1, P₂}`. Then `cexF ε t` is
the exact L-step and the exact K-step from each of its points, with the same `X` and `V`, so that
the GAP scheme gives `κ^ε(t) = cexF ε t = z 𝟙ᵀ + e^{-t/ε²} 𝟙 P₂ᵀ` for any number of steps. The
density of `F₀` is `ρ(0)` for the solution `ρ(t) = e^{-t/3} z` of the limit equation `ρ' = ⅓ D² ρ`.
But `κ^ε(t)` does not converge to `ρ(t) 𝟙ᵀ` for any `t > 0`, it converges to the stationary `z 𝟙ᵀ`
(`cex_lower_bound`). The cause is that `P_X ∂ₓ ρ = 0` here, so the L-step produces no `μ`-mode: the
proof reads off the range of `L` from the two vectors `⟨L⟩_μ` and `⟨L⟩_μ ⟨∂ₓXᵀX⟩`, which it tacitly
takes to be linearly independent (`cex_not_indep`). The same formula gives a counterexample for the
PDE (4.1) of the printed theorem, with `X = span {cos x, 1}` and `V = span {1, P₂(μ)}`; that version
is not formalized. -/
theorem theorem_4_2_false {h : ℝ} (hh : 0 < h) :
    IsAngularQuad cexμ cexw ∧
    (∀ ε t₀ t₁, IsRTEGAPStep cexD cexμ cexw ε t₀ t₁ cexX cexV (cexF ε t₀) (cexF ε) (cexF ε)) ∧
    (∀ ε, cexF ε 0 = cexI + cexB) ∧
    ODESolution (fun _ r => (1 / 3 : ℝ) • (cexD * cexD).mulVec r) cexρ 0 h ∧
    cexρ 0 = density cexw (cexI + cexB) ∧
    ¬ Tendsto (fun ε => cexF ε h) (𝓝[>] 0) (𝓝 (iso (cexρ h))) :=
  ⟨cex_quad, cex_step, cexF_zero, cex_heat 0 h,
    by rw [cex_ρ_zero, ← cexF_zero 0, cex_density], cex_not_tendsto hh⟩

end Counterexample


section Theorem42

variable {μ w : n → ℝ} {r : ℕ}

lemma tendsto_of_le_mul {x : ℝ → Matrix m n ℝ} {y : Matrix m n ℝ} {C : ℝ}
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖x ε - y‖ ≤ C * ε) : Tendsto x (𝓝[>] 0) (𝓝 y) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun ε : ℝ => C * ε) (𝓝 0) (𝓝 (C * 0)) := tendsto_id.const_mul C
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) h h1

/-- **Theorem 4.2 of arXiv 2505.19929 for a run of the scheme, repaired.**  Let `Y ε n` be the
iterates of GAP on the semi-discrete RTE (5.1), with exact substeps, step size `h`, for any `D`
(this generality costs nothing) and any input `F₀` (not well prepared).  Suppose that at each step
the density of the L-step output and its projected gradient are uniformly linearly independent
(`hind`); this is the assumption that the proof in the paper makes when it reads off the range of
`L`, and `theorem_4_2_false` shows that it cannot be dropped.  Then the density of `Y ε n` converges
to `ρ(tₙ)` with rate `ε`, and after one step `Y ε n` itself converges to `ρ(tₙ) 𝟙ᵀ`, where
`ρ' = ⅓ D² ρ`, `ρ(t₀) = ½ ∑ₖ wₖ F₀(·, k)`.  Differences from the paper: the discrete setting
(Section 5) replaces the PDE, the hypothesis `hind` is added, and the rate is added. -/
theorem gap_ap_run (hq : IsAngularQuad μ w) (D : Matrix m m ℝ) {h c₀ t₀ : ℝ} (hh : 0 < h)
    (hc₀ : 0 < c₀) {N : ℕ} {F₀ : Matrix m n ℝ} {ρ : ℝ → m → ℝ}
    (hρ : ODESolution (fun _ r => (1 / 3 : ℝ) • (D * D).mulVec r) ρ t₀ (t₀ + N * h))
    (hρ₀ : ρ t₀ = density w F₀) {X : ℝ → ℕ → Matrix m (Fin r) ℝ}
    {V : ℝ → ℕ → Matrix n (Fin r) ℝ} {Y : ℝ → ℕ → Matrix m n ℝ}
    {ℓ k : ℝ → ℕ → ℝ → Matrix m n ℝ} (hY₀ : ∀ ε, Y ε 0 = F₀)
    (hstep : ∀ ε > 0, ∀ j < N, IsRTEGAPStep D μ w ε (t₀ + j * h) (t₀ + (j + 1) * h) (X ε j)
      (V ε j) (Y ε j) (ℓ ε j) (k ε j))
    (hY : ∀ ε > 0, ∀ j < N, Y ε (j + 1) = k ε j (t₀ + (j + 1) * h))
    (hind : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j < N,
      UniformlyIndep c₀ (density w (ℓ ε j (t₀ + (j + 1) * h)))
        ((X ε j * (X ε j)ᵀ * D).mulVec (density w (ℓ ε j (t₀ + (j + 1) * h))))) :
    ∀ j ≤ N, ∃ C : ℝ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖density w (Y ε j) - ρ (t₀ + j * h)‖ ≤ C * ε ∧
      (0 < j → ‖Y ε j - iso (ρ (t₀ + j * h))‖ ≤ C * ε) := by
  set τ := ‖D‖ * ‖diagonal μ‖ with hτdef
  have hτ0 : 0 ≤ τ := by positivity
  set G₀ := F₀ * sDiag w with hG₀
  set n₀ := Real.exp (2 * τ ^ 2 * (N * h)) * ‖G₀‖ with hn₀def
  have hn₀ : 0 ≤ n₀ := by positivity
  obtain ⟨A, B, ε₀, hA, hB, hε₀, key⟩ := gap_step_estimate (r := r) hq D hh hn₀ hc₀
  set q := Real.exp (τ ^ 2 * h) with hq'
  have hq0 : 0 < q := Real.exp_pos _
  let a : ℕ → ℝ := fun j => Nat.rec 0 (fun _ x => q * (x + A)) j
  have ha0 : ∀ j, 0 ≤ a j := by
    intro j
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact mul_nonneg hq0.le (add_nonneg ih hA)
  have hmain : ∀ ε, 0 < ε → ε < ε₀ → (∀ j < N, UniformlyIndep c₀
      (density w (ℓ ε j (t₀ + (j + 1) * h)))
      ((X ε j * (X ε j)ᵀ * D).mulVec (density w (ℓ ε j (t₀ + (j + 1) * h))))) →
      ∀ j ≤ N, ‖Y ε j * sDiag w‖ ≤ Real.exp (2 * τ ^ 2 * (j * h)) * ‖G₀‖ ∧
        ‖(iso (density w (Y ε j) - ρ (t₀ + j * h)) : Matrix m n ℝ) * sDiag w‖ ≤ a j * ε ∧
        (0 < j → ‖Y ε j * sDiag w
          - (iso (density w (Y ε j)) : Matrix m n ℝ) * sDiag w‖ ≤ ε * B) := by
    intro ε hε hεε₀ hindε j
    induction j with
    | zero =>
      intro _
      refine ⟨?_, ?_, fun h0 => absurd h0 (lt_irrefl _)⟩
      · simp [hY₀, hG₀]
      · have : density w (Y ε 0) - ρ (t₀ + ((0 : ℕ) : ℝ) * h) = 0 := by
          simp [hY₀, hρ₀]
        rw [this]
        have h0 : (iso (0 : m → ℝ) : Matrix m n ℝ) = 0 := by
          ext i j
          simp [iso]
        rw [h0]
        simp [a]
    | succ j ih =>
      intro hn
      have hnN : j < N := hn
      obtain ⟨ih1, ih2, -⟩ := ih hnN.le
      have hpos : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hNn : ((j : ℝ) + 1) ≤ N := by exact_mod_cast hn
      have ht : t₀ + ((j : ℝ) + 1) * h = (t₀ + j * h) + h := by ring
      have hbn : ‖Y ε j * sDiag w‖ ≤ n₀ := by
        refine ih1.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
        refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (by positivity))
        exact mul_le_mul_of_nonneg_right (by linarith) hh.le
      have hρs : ODESolution (fun _ r => (1 / 3 : ℝ) • (D * D).mulVec r) ρ (t₀ + j * h)
          (t₀ + (j + 1) * h) := hρ.mono (by nlinarith) (by nlinarith)
      obtain ⟨h1, h2, h3⟩ := key ε hε hεε₀ (t₀ + j * h) (t₀ + (j + 1) * h) (X ε j) (V ε j)
        (Y ε j) (ℓ ε j) (k ε j) ρ ht (hstep ε hε j hnN) hbn (hindε j hnN) hρs
      have hYn := hY ε hε j hnN
      have hcast : t₀ + (((j + 1 : ℕ) : ℝ)) * h = t₀ + (j + 1) * h := by push_cast; ring
      rw [hcast, hYn]
      refine ⟨?_, ?_, fun _ => h2⟩
      · refine h3.trans ?_
        have h4 := mul_le_mul_of_nonneg_left ih1 (Real.exp_pos (2 * τ ^ 2 * h)).le
        refine h4.trans (le_of_eq ?_)
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        push_cast
        ring
      · refine h1.trans ?_
        have h5 : a (j + 1) = q * (a j + A) := rfl
        rw [h5]
        calc q * (_ + ε * A) ≤ q * (a j * ε + ε * A) := by gcongr
          _ = _ := by ring
  intro j hn
  refine ⟨a j + (B + a j) * ‖sDiagInv w‖, ?_⟩
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < ε₀ := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hε₀)]
      with ε h2 h3
    exact ⟨h2, h3⟩
  filter_upwards [hsmall, hind] with ε hsm hindε
  obtain ⟨hε, hεε₀⟩ := hsm
  obtain ⟨-, h2, h3⟩ := hmain ε hε hεε₀ hindε j hn
  have hNinv : 0 ≤ ‖sDiagInv w‖ := norm_nonneg _
  have hb := mul_nonneg (add_nonneg hB (ha0 j)) hNinv
  constructor
  · refine (norm_le_iso hq _).trans (h2.trans ?_)
    have := mul_nonneg hb hε.le
    nlinarith
  · intro hn0
    have h4 : ‖(Y ε j - iso (ρ (t₀ + j * h))) * sDiag w‖ ≤ (B + a j) * ε := by
      have h5 : (Y ε j - iso (ρ (t₀ + j * h))) * sDiag w
          = (Y ε j * sDiag w - (iso (density w (Y ε j)) : Matrix m n ℝ) * sDiag w)
            + (iso (density w (Y ε j) - ρ (t₀ + j * h)) : Matrix m n ℝ) * sDiag w := by
        rw [iso_sub, Matrix.sub_mul, Matrix.sub_mul]
        abel
      rw [h5]
      refine (norm_add_le _ _).trans ?_
      calc _ ≤ ε * B + a j * ε := add_le_add (h3 hn0) h2
        _ = _ := by ring
    calc _ ≤ ‖(Y ε j - iso (ρ (t₀ + j * h))) * sDiag w‖ * ‖sDiagInv w‖ := norm_le_weighted hq _
      _ ≤ ((B + a j) * ε) * ‖sDiagInv w‖ := by gcongr
      _ ≤ _ := by
        have := mul_nonneg (ha0 j) hε.le
        nlinarith

lemma transportL_eq (X : Matrix m (Fin r) ℝ) (D : Matrix m m ℝ) (μ : n → ℝ) :
    transportL X D μ = transport (X * Xᵀ * D * (X * Xᵀ)) μ := by
  ext1 G
  change leftProj X (transport D μ (leftProj X G)) = _
  rw [transport_apply, transport_apply, leftProj_apply, leftProj_apply]
  simp only [Matrix.mul_assoc]

/-- The L-step of arXiv 2505.19929 reaches the limit of the projected system: the density of `ℓ t₁`
is `O(ε)`-close to `ρL(t₁)`, with `ρL' = ⅓ (P D P)² ρL` and `ρL(t₀)` the density of the input. -/
theorem lstep_density_le (hq : IsAngularQuad μ w) {D : Matrix m m ℝ} {ε t₀ t₁ h : ℝ}
    {X : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ} {F₀ : Matrix m n ℝ}
    {ℓ k : ℝ → Matrix m n ℝ} {ρL : ℝ → m → ℝ} (hs : IsRTEGAPStep D μ w ε t₀ t₁ X V F₀ ℓ k)
    (hε : 0 < ε) (hετ : 2 * ε * (‖D‖ * ‖diagonal μ‖) ≤ 1) (ht₁ : t₁ = t₀ + h) (hh : 0 < h)
    (hρL : ODESolution (fun _ r => (1 / 3 : ℝ) •
      ((X * Xᵀ * D * (X * Xᵀ)) * (X * Xᵀ * D * (X * Xᵀ))).mulVec r) ρL t₀ t₁)
    (hρL₀ : ρL t₀ = density w F₀) :
    ‖density w (ℓ t₁) - ρL t₁‖ ≤ Real.exp ((‖D‖ * ‖diagonal μ‖) ^ 2 * h) *
      (6 * (Real.exp (2 * (‖D‖ * ‖diagonal μ‖) ^ 2 * h) * ‖F₀ * sDiag w‖) * (‖D‖ * ‖diagonal μ‖)
        + 2 * (‖D‖ * ‖diagonal μ‖) ^ 3 *
          (Real.exp (2 * (‖D‖ * ‖diagonal μ‖) ^ 2 * h) * ‖F₀ * sDiag w‖) * h) * ε := by
  set τ := ‖D‖ * ‖diagonal μ‖ with hτdef
  set C := Real.exp (2 * τ ^ 2 * h) * ‖F₀ * sDiag w‖ with hC
  have hN := hs.normalized hq
  obtain ⟨-, hsol⟩ := lSol_relax hN
  have sys := relaxSystemL (μ := μ) hq hs.orthoX D
  have hab : t₀ ≤ t₁ := by linarith
  have hbound : ∀ t ∈ Icc t₀ t₁, ‖ℓ t * sDiag w‖ ≤ C :=
    apriori_of_exp sys hε hετ hsol rfl ht₁ (by simp only [hs.lStart]; exact le_rfl)
  obtain ⟨hvc, hv⟩ := heat_curve (μ := μ) (w := w) hq (X * Xᵀ * D * (X * Xᵀ)) hρL
  rw [← transportL_eq] at hv
  have hmacro := sys.macro_le hε hετ hsol rfl hbound hvc hv t₁ ⟨hab, le_rfl⟩
  have htt : t₁ - t₀ = h := by rw [ht₁]; ring
  have h0 : macroP w (ℓ t₀ * sDiag w) - (iso (ρL t₀) : Matrix m n ℝ) * sDiag w = 0 := by
    rw [macroP_mul_sDiag hq, hs.lStart, hρL₀, sub_self]
  rw [h0, norm_zero, htt, macroP_mul_sDiag hq, ← Matrix.sub_mul, ← iso_sub] at hmacro
  refine (norm_le_iso hq _).trans (hmacro.trans (le_of_eq ?_))
  have hcε : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε.ne'
  have : ε⁻¹ * τ * ((ε * 0 + 2 * τ ^ 2 * ε ^ 2 + 2 * 0) * C) + ε⁻¹ * 0 * τ * C
      + ε⁻¹ ^ 2 * 0 ^ 2 * C = 2 * τ ^ 3 * C * ε * (ε⁻¹ * ε) := by ring
  rw [this, hcε]
  ring

/-- Linear independence is stable and quantitative. -/
lemma uniformlyIndep_of_close {u a : m → ℝ} (hLI : LinearIndependent ℝ ![u, a]) :
    ∃ c₀ η : ℝ, 0 < c₀ ∧ 0 < η ∧ ∀ u' a' : m → ℝ, ‖u' - u‖ ≤ η → ‖a' - a‖ ≤ η →
      UniformlyIndep c₀ u' a' := by
  let f : ℝ × ℝ →ₗ[ℝ] (m → ℝ) :=
    { toFun := fun p => p.1 • u + p.2 • a
      map_add' := fun p q => by simp only [Prod.fst_add, Prod.snd_add]; module
      map_smul' := fun c p => by
        simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
        module }
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro p hp
    have := LinearIndependent.pair_iff.1 hLI p.1 p.2 hp
    exact Prod.ext this.1 this.2
  obtain ⟨K, hK, hanti⟩ := f.exists_antilipschitzWith hker
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hbound : ∀ α β : ℝ, max |α| |β| ≤ K * ‖α • u + β • a‖ := fun α β => by
    have h := hanti.le_mul_dist (α, β) 0
    have h0 : f 0 = 0 := map_zero f
    rw [h0, dist_zero_right, dist_zero_right, Prod.norm_def] at h
    simpa [f] using h
  refine ⟨1 / (4 * K), 1 / (4 * K), by positivity, by positivity, ?_⟩
  intro u' a' hu ha α β
  have h1 := hbound α β
  have hsum : |α| + |β| ≤ 2 * (K * ‖α • u + β • a‖) := by
    have h2 := le_max_left |α| |β|
    have h3 := le_max_right |α| |β|
    linarith
  have hdec : α • u + β • a = (α • u' + β • a') - (α • (u' - u) + β • (a' - a)) := by module
  have h4 : ‖α • u + β • a‖ ≤ ‖α • u' + β • a'‖ + (|α| * (1 / (4 * K)) + |β| * (1 / (4 * K))) := by
    rw [hdec]
    refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      gcongr
    · rw [norm_smul, Real.norm_eq_abs]
      gcongr
  have h5 : (|α| + |β|) / (2 * K) ≤ ‖α • u + β • a‖ := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have h6 : 1 / (4 * K) * (|α| + |β|) = (|α| + |β|) / (2 * K)
      - (|α| * (1 / (4 * K)) + |β| * (1 / (4 * K))) := by
    field_simp
    ring
  rw [h6]
  linarith

/-- The independence hypothesis of `gap_step_estimate` and `gap_ap_run` (Theorem 4.2 of
arXiv 2505.19929) follows, for small `ε`, from the independence in the limit of the L-step.  With
`N = 1` this shows that the hypothesis `hind` of `gap_ap_run` can hold. -/
theorem gap_indep_eventually (hq : IsAngularQuad μ w) (D : Matrix m m ℝ) {t₀ h : ℝ} (hh : 0 < h)
    {X : Matrix m (Fin r) ℝ} {F₀ : Matrix m n ℝ} {ρL : ℝ → m → ℝ}
    (hρL : ODESolution (fun _ r => (1 / 3 : ℝ) •
      ((X * Xᵀ * D * (X * Xᵀ)) * (X * Xᵀ * D * (X * Xᵀ))).mulVec r) ρL t₀ (t₀ + h))
    (hρL₀ : ρL t₀ = density w F₀)
    (hLI : LinearIndependent ℝ ![ρL (t₀ + h), (X * Xᵀ * D).mulVec (ρL (t₀ + h))])
    {V : ℝ → Matrix n (Fin r) ℝ} {ℓ k : ℝ → ℝ → Matrix m n ℝ}
    (hstep : ∀ ε > 0, IsRTEGAPStep D μ w ε t₀ (t₀ + h) X (V ε) F₀ (ℓ ε) (k ε)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      UniformlyIndep c₀ (density w (ℓ ε (t₀ + h)))
        ((X * Xᵀ * D).mulVec (density w (ℓ ε (t₀ + h)))) := by
  set τ := ‖D‖ * ‖diagonal μ‖ with hτdef
  have hτ0 : 0 ≤ τ := by positivity
  set t₁ := t₀ + h with ht₁
  set C₀ := Real.exp (2 * τ ^ 2 * h) * ‖F₀ * sDiag w‖ with hC₀
  set C₁ := Real.exp (τ ^ 2 * h) * (6 * C₀ * τ + 2 * τ ^ 3 * C₀ * h) with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  obtain ⟨c₀, η, hc₀, hη, hclose⟩ := uniformlyIndep_of_close hLI
  let Pop : (m → ℝ) →L[ℝ] (m → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin (X * Xᵀ * D))
  have hPop : ∀ z, (X * Xᵀ * D).mulVec z = Pop z := fun _ => rfl
  have hLop : 0 ≤ ‖Pop‖ := norm_nonneg _
  refine ⟨c₀, hc₀, ?_⟩
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < 1 / (2 * τ + 1) ∧
      ε < η / (C₁ + 1) ∧ ε < η / (‖Pop‖ * C₁ + 1) := by
    have h1 : (0 : ℝ) < 1 / (2 * τ + 1) := by positivity
    have h2 : 0 < η / (C₁ + 1) := by positivity
    have h3 : 0 < η / (‖Pop‖ * C₁ + 1) := by positivity
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h1),
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h2),
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h3)] with ε a1 a3 a4 a5
    exact ⟨a1, a3, a4, a5⟩
  filter_upwards [hsmall] with ε hsm
  obtain ⟨hε, hε1, hε2, hε3⟩ := hsm
  have hετ : 2 * ε * τ ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at hε1
    nlinarith
  have hd := lstep_density_le hq (hstep ε hε) hε hετ ht₁ hh hρL hρL₀
  have hd' : ‖density w (ℓ ε t₁) - ρL t₁‖ ≤ C₁ * ε := hd
  have hu : ‖density w (ℓ ε t₁) - ρL t₁‖ ≤ η := by
    refine hd'.trans ?_
    rw [lt_div_iff₀ (by positivity)] at hε2
    nlinarith
  have ha : ‖(X * Xᵀ * D).mulVec (density w (ℓ ε t₁)) - (X * Xᵀ * D).mulVec (ρL t₁)‖ ≤ η := by
    rw [hPop, hPop, ← map_sub]
    refine (Pop.le_opNorm _).trans ?_
    have h1 := mul_le_mul_of_nonneg_left hd' hLop
    rw [lt_div_iff₀ (by positivity)] at hε3
    nlinarith
  exact hclose _ _ hu ha

/-- **Theorem 4.2 of arXiv 2505.19929 for one step with fixed data, repaired.**  Let `ρL` solve the
limit of the L-step `ρL' = ⅓ (P D P)² ρL` from the density of the input, where `P = X Xᵀ`, and
suppose that `ρL(t₁)` and `P D ρL(t₁)` are linearly independent (the limit of the assumption of the
paper that `L` has rank two; it needs `r ≥ 2`, and `theorem_4_2_false` shows that it cannot be
dropped).  Then, for any choice of bases `V ε` capturing the L-step, the output of GAP satisfies
`‖κ^ε(t₁) - ρ(t₁) 𝟙ᵀ‖ ≤ C ε`, where `ρ' = ⅓ D² ρ`, `ρ(t₀) = ½ ∑ₖ wₖ F₀(·, k)`.  The input `F₀` is
not assumed well prepared and `D` is arbitrary.  In the proof the L-step only produces the basis:
`lstep_capture` is the first half of the proof in the paper, carried out for the approximate
inclusion of `1, μ` in `V`, and `kstep_estimate` the second half. -/
theorem gap_ap_step (hq : IsAngularQuad μ w) (D : Matrix m m ℝ) {t₀ h : ℝ} (hh : 0 < h)
    {X : Matrix m (Fin r) ℝ} {F₀ : Matrix m n ℝ} {ρL ρ : ℝ → m → ℝ}
    (hρL : ODESolution (fun _ r => (1 / 3 : ℝ) •
      ((X * Xᵀ * D * (X * Xᵀ)) * (X * Xᵀ * D * (X * Xᵀ))).mulVec r) ρL t₀ (t₀ + h))
    (hρL₀ : ρL t₀ = density w F₀)
    (hLI : LinearIndependent ℝ ![ρL (t₀ + h), (X * Xᵀ * D).mulVec (ρL (t₀ + h))])
    (hρ : ODESolution (fun _ r => (1 / 3 : ℝ) • (D * D).mulVec r) ρ t₀ (t₀ + h))
    (hρ₀ : ρ t₀ = density w F₀) {V : ℝ → Matrix n (Fin r) ℝ} {ℓ k : ℝ → ℝ → Matrix m n ℝ}
    (hstep : ∀ ε > 0, IsRTEGAPStep D μ w ε t₀ (t₀ + h) X (V ε) F₀ (ℓ ε) (k ε)) :
    ∃ C : ℝ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖k ε (t₀ + h) - iso (ρ (t₀ + h))‖ ≤ C * ε := by
  obtain ⟨c₀, hc₀, hind⟩ := gap_indep_eventually hq D hh hρL hρL₀ hLI hstep
  obtain ⟨A, B, ε₀, hA, hB, hε₀, key⟩ :=
    gap_step_estimate (r := r) hq D hh (norm_nonneg (F₀ * sDiag w)) hc₀
  set t₁ := t₀ + h with ht₁
  set q := Real.exp ((‖D‖ * ‖diagonal μ‖) ^ 2 * h) with hq'
  have hq0 : 0 < q := Real.exp_pos _
  refine ⟨(B + q * A) * ‖sDiagInv w‖, ?_⟩
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < ε₀ := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hε₀)]
      with ε a1 a2
    exact ⟨a1, a2⟩
  filter_upwards [hsmall, hind] with ε hsm hindε
  obtain ⟨hε, hεε₀⟩ := hsm
  obtain ⟨h1, h2, -⟩ := key ε hε hεε₀ t₀ t₁ X (V ε) F₀ (ℓ ε) (k ε) ρ ht₁ (hstep ε hε) le_rfl
    hindε hρ
  have h0 : density w F₀ - ρ t₀ = 0 := by rw [hρ₀, sub_self]
  have hiso0 : (iso (0 : m → ℝ) : Matrix m n ℝ) = 0 := by
    ext i j
    simp [iso]
  rw [h0, hiso0, Matrix.zero_mul, norm_zero, zero_add] at h1
  have h4 : ‖(k ε t₁ - iso (ρ t₁)) * sDiag w‖ ≤ (B + q * A) * ε := by
    have h5 : (k ε t₁ - iso (ρ t₁)) * sDiag w
        = (k ε t₁ * sDiag w - (iso (density w (k ε t₁)) : Matrix m n ℝ) * sDiag w)
          + (iso (density w (k ε t₁) - ρ t₁) : Matrix m n ℝ) * sDiag w := by
      rw [iso_sub, Matrix.sub_mul, Matrix.sub_mul]
      abel
    rw [h5]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ ε * B + q * (ε * A) := add_le_add h2 h1
      _ = _ := by ring
  calc _ ≤ ‖(k ε t₁ - iso (ρ t₁)) * sDiag w‖ * ‖sDiagInv w‖ := norm_le_weighted hq _
    _ ≤ ((B + q * A) * ε) * ‖sDiagInv w‖ := by gcongr
    _ = _ := by ring

/-- The limit in the form stated in Theorem 4.2 of arXiv 2505.19929, under the hypotheses of
`gap_ap_step`: `lim_{ε → 0} κ^ε(t₁) = ρ(t₁) 𝟙ᵀ`. -/
theorem gap_ap_tendsto (hq : IsAngularQuad μ w) (D : Matrix m m ℝ) {t₀ h : ℝ} (hh : 0 < h)
    {X : Matrix m (Fin r) ℝ} {F₀ : Matrix m n ℝ} {ρL ρ : ℝ → m → ℝ}
    (hρL : ODESolution (fun _ r => (1 / 3 : ℝ) •
      ((X * Xᵀ * D * (X * Xᵀ)) * (X * Xᵀ * D * (X * Xᵀ))).mulVec r) ρL t₀ (t₀ + h))
    (hρL₀ : ρL t₀ = density w F₀)
    (hLI : LinearIndependent ℝ ![ρL (t₀ + h), (X * Xᵀ * D).mulVec (ρL (t₀ + h))])
    (hρ : ODESolution (fun _ r => (1 / 3 : ℝ) • (D * D).mulVec r) ρ t₀ (t₀ + h))
    (hρ₀ : ρ t₀ = density w F₀) {V : ℝ → Matrix n (Fin r) ℝ} {ℓ k : ℝ → ℝ → Matrix m n ℝ}
    (hstep : ∀ ε > 0, IsRTEGAPStep D μ w ε t₀ (t₀ + h) X (V ε) F₀ (ℓ ε) (k ε)) :
    Tendsto (fun ε => k ε (t₀ + h)) (𝓝[>] 0) (𝓝 (iso (ρ (t₀ + h)))) := by
  obtain ⟨C, hC⟩ := gap_ap_step hq D hh hρL hρL₀ hLI hρ hρ₀ hstep
  exact tendsto_of_le_mul hC

/-- `gap_ap_run` as a limit (Theorem 4.2 of arXiv 2505.19929, repaired): after the first step,
`lim_{ε → 0} Y ε j = ρ(tⱼ) 𝟙ᵀ`. -/
theorem gap_ap_run_tendsto (hq : IsAngularQuad μ w) (D : Matrix m m ℝ) {h c₀ t₀ : ℝ} (hh : 0 < h)
    (hc₀ : 0 < c₀) {N : ℕ} {F₀ : Matrix m n ℝ} {ρ : ℝ → m → ℝ}
    (hρ : ODESolution (fun _ r => (1 / 3 : ℝ) • (D * D).mulVec r) ρ t₀ (t₀ + N * h))
    (hρ₀ : ρ t₀ = density w F₀) {X : ℝ → ℕ → Matrix m (Fin r) ℝ}
    {V : ℝ → ℕ → Matrix n (Fin r) ℝ} {Y : ℝ → ℕ → Matrix m n ℝ}
    {ℓ k : ℝ → ℕ → ℝ → Matrix m n ℝ} (hY₀ : ∀ ε, Y ε 0 = F₀)
    (hstep : ∀ ε > 0, ∀ j < N, IsRTEGAPStep D μ w ε (t₀ + j * h) (t₀ + (j + 1) * h) (X ε j)
      (V ε j) (Y ε j) (ℓ ε j) (k ε j))
    (hY : ∀ ε > 0, ∀ j < N, Y ε (j + 1) = k ε j (t₀ + (j + 1) * h))
    (hind : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j < N,
      UniformlyIndep c₀ (density w (ℓ ε j (t₀ + (j + 1) * h)))
        ((X ε j * (X ε j)ᵀ * D).mulVec (density w (ℓ ε j (t₀ + (j + 1) * h)))))
    {j : ℕ} (hj : j ≤ N) (hj0 : 0 < j) :
    Tendsto (fun ε => Y ε j) (𝓝[>] 0) (𝓝 (iso (ρ (t₀ + j * h)))) := by
  obtain ⟨C, hC⟩ := gap_ap_run hq D hh hc₀ hρ hρ₀ hY₀ hstep hY hind j hj
  exact tendsto_of_le_mul (hC.mono fun _ h => h.2 hj0)

/-- `rte_diffusion_limit` as a limit (Theorem 4.1 of arXiv 2505.19929, semi-discrete):
`lim_{ε → 0} F^ε(t₁) = ρ(t₁) 𝟙ᵀ` for `t₁ > t₀`. -/
theorem rte_tendsto (hq : IsAngularQuad μ w) (D : Matrix m m ℝ) {t₀ t₁ : ℝ}
    (h01 : t₀ < t₁) (F₀ : Matrix m n ℝ) {ρ : ℝ → m → ℝ}
    (hρ : ODESolution (fun _ r => (1 / 3 : ℝ) • (D * D).mulVec r) ρ t₀ t₁)
    (hρ₀ : ρ t₀ = density w F₀) {F : ℝ → ℝ → Matrix m n ℝ}
    (hF : ∀ ε > 0, ODESolution (fun _ Y => rte D μ w ε Y) (F ε) t₀ t₁)
    (hF₀ : ∀ ε, F ε t₀ = F₀) :
    Tendsto (fun ε => F ε t₁) (𝓝[>] 0) (𝓝 (iso (ρ t₁))) := by
  obtain ⟨C, hC⟩ := rte_diffusion_limit hq D h01 F₀ hρ hρ₀
  refine tendsto_of_le_mul (C := C) ?_
  filter_upwards [hC, self_mem_nhdsWithin] with ε h1 h2
  exact h1 (F ε) (hF ε h2) (hF₀ ε)

end Theorem42

section Existence

variable {μ w : n → ℝ} {r : ℕ}

/-- The RTE field as a continuous linear map. -/
noncomputable def rteCLM (D : Matrix m m ℝ) (μ w : n → ℝ) (ε : ℝ) :
    Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  -(ε⁻¹ • (leftMulCLM D).comp (rightMulCLM (diagonal μ)))
    + (ε⁻¹ ^ 2) • (rightMulCLM (Wmat w) - 1)

lemma rteCLM_apply (D : Matrix m m ℝ) (ε : ℝ) (F : Matrix m n ℝ) :
    rteCLM D μ w ε F = rte D μ w ε F := by
  simp [rteCLM, rte, Matrix.mul_assoc]

lemma exists_linear_solution (A : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (a b : ℝ)
    (y₀ : Matrix m n ℝ) :
    ∃ y : ℝ → Matrix m n ℝ, ODESolution (fun _ Y => A Y) y a b ∧ y a = y₀ := by
  have hd : ∀ t, HasDerivAt (fun t : ℝ => NormedSpace.exp ((t - a) • A) y₀)
      (A (NormedSpace.exp ((t - a) • A) y₀)) t := by
    intro t
    have h := ((hasDerivAt_exp_smul_const' A (t - a)).comp_sub_const t a).clm_apply
      (hasDerivAt_const t y₀)
    convert h using 1
    simp
  exact ⟨_, ⟨fun t _ => (hd t).continuousAt.continuousWithinAt,
    fun t _ => (hd t).hasDerivWithinAt⟩, by simp⟩

lemma angBasis_gram (hq : IsAngularQuad μ w) (V : Matrix n (Fin r) ℝ) :
    (angBasis w V)ᵀ * angBasis w V = Vᵀ * diagonal w * V := by
  have h2 : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have : (angBasis w V)ᵀ * angBasis w V = ((√2 : ℝ) * √2) • (Vᵀ * (sDiag w * sDiag w) * V) := by
    simp only [angBasis, Matrix.transpose_smul, Matrix.transpose_mul, sDiag_transpose,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [this, h2, sDiag_mul_self hq, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  norm_num

/-- **Algorithm 2.3 of arXiv 2505.19929 is well defined on the RTE**: from any input
`F₀ = X Xᵀ F₀`, for `r ≤ N_μ`, the substeps have solutions and a basis `V₁` exists.  (Rank
deficiency is allowed: then `V₁` is any orthonormal completion.) -/
theorem exists_gapStep (hq : IsAngularQuad μ w) (D : Matrix m m ℝ) (ε : ℝ) {t₀ t₁ : ℝ}
    (h01 : t₀ ≤ t₁) {X : Matrix m (Fin r) ℝ} (hX : Xᵀ * X = 1) {F₀ : Matrix m n ℝ}
    (hF₀ : X * Xᵀ * F₀ = F₀) (hr : r ≤ Fintype.card n) :
    ∃ (V : Matrix n (Fin r) ℝ) (ℓ k : ℝ → Matrix m n ℝ), IsRTEGAPStep D μ w ε t₀ t₁ X V F₀ ℓ k := by
  obtain ⟨ℓ, hℓ, hℓ₀⟩ := exists_linear_solution ((leftMulCLM (X * Xᵀ)).comp (rteCLM D μ w ε))
    t₀ t₁ F₀
  have hℓ' : ODESolution (fun _ Y => X * Xᵀ * rte D μ w ε Y) ℓ t₀ t₁ :=
    ⟨hℓ.cont, fun t ht => by simpa [rteCLM_apply] using hℓ.deriv t ht⟩
  have hN : ODESolution (relaxField (macroP w) (leftProj X) (transport D μ) ε)
      (fun t => ℓ t * sDiag w) t₀ t₁ := odeSolution_mul_right (sDiag w) hℓ' fun t Y => by
    rw [Matrix.mul_assoc, rte_mul_sDiag hq D ε t]
    rfl
  have hstay := relaxField_stay (isOrthProj_leftProj hX) hN (by
    rw [hℓ₀, leftProj_apply, ← Matrix.mul_assoc, hF₀])
  set L₁ := ℓ t₁ * sDiag w with hL₁
  have hL : leftProj X L₁ = L₁ := hstay t₁ ⟨h01, le_rfl⟩
  have hrank : L₁ᵀ.rank ≤ r := by
    rw [Matrix.rank_transpose, ← hL, leftProj_apply, Matrix.mul_assoc]
    exact (Matrix.rank_mul_le_left _ _).trans (by simpa using X.rank_le_card_width)
  obtain ⟨U, hU, hcap⟩ := exists_orthonormal_capture L₁ᵀ hrank hr
  set V : Matrix n (Fin r) ℝ := (√2 : ℝ)⁻¹ • (sDiagInv w * U) with hVdef
  have hs2 : (√2 : ℝ) ≠ 0 := by positivity
  have hang : angBasis w V = U := by
    simp only [angBasis, hVdef, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hs2, one_smul]
    rw [← Matrix.mul_assoc, sDiag_mul_inv hq, Matrix.one_mul]
  have hV : Vᵀ * diagonal w * V = 1 := by
    rw [← angBasis_gram hq, hang]
    exact hU
  have hcap' : L₁ * U * Uᵀ = L₁ := by
    have := congrArg Matrix.transpose hcap
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  have hcapture : ℓ t₁ * diagonal w * V * Vᵀ = ℓ t₁ := by
    have h1 : (ℓ t₁ * diagonal w * V * Vᵀ) * sDiag w = ℓ t₁ * sDiag w := by
      rw [proj_mul_sDiag hq, hang]
      exact hcap'
    have h2 := congrArg (· * sDiagInv w) h1
    simpa only [Matrix.mul_assoc, sDiag_mul_inv hq, Matrix.mul_one] using h2
  obtain ⟨k, hk, hk₀⟩ := exists_linear_solution
    ((rightMulCLM (diagonal w * V * Vᵀ)).comp (rteCLM D μ w ε)) t₀ t₁ (F₀ * diagonal w * V * Vᵀ)
  refine ⟨V, ℓ, k, hX, hF₀, hℓ', hℓ₀, hV, hcapture, ⟨hk.cont, fun t ht => ?_⟩, hk₀⟩
  have h3 := hk.deriv t ht
  simpa only [ContinuousLinearMap.comp_apply, rightMulCLM_apply, rteCLM_apply,
    Matrix.mul_assoc] using h3

end Existence

section Instance

/-- A spatial basis spanning the `D`-invariant pair `z`, `D z`, for which `theorem_4_2_false` does
not apply. -/
noncomputable def exX : Matrix (Fin 4) (Fin 2) ℝ :=
  !![1 / 2, 1 / 2; 1 / 2, -1 / 2; -1 / 2, -1 / 2; -1 / 2, 1 / 2]

/-- The projector `X Xᵀ` for `exX`. -/
noncomputable def exP : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1 / 2, 0, -1 / 2, 0; 0, 1 / 2, 0, -1 / 2; -1 / 2, 0, 1 / 2, 0; 0, -1 / 2, 0, 1 / 2]

/-- A rank-two input: the isotropic `z 𝟙ᵀ` and an anisotropic `(D z) P₂ᵀ`. -/
def exF : Matrix (Fin 4) (Fin 3) ℝ := !![5, -4, 5; -3, 6, -3; -5, 4, -5; 3, -6, 3]

/-- The gradient `D z`. -/
def exg : Fin 4 → ℝ := ![1, -1, -1, 1]

lemma exX_orth : exXᵀ * exX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exX, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

lemma exX_proj : exX * exXᵀ = exP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exX, exP, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

lemma ex_start : exX * exXᵀ * exF = exF := by
  rw [exX_proj]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exP, exF, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

lemma ex_density : density cexw exF = cexz := by
  ext i
  fin_cases i <;>
    simp [density, exF, cexw, cexz, Fin.sum_univ_three] <;> norm_num

lemma ex_grad : (exX * exXᵀ * cexD).mulVec cexz = exg := by
  rw [exX_proj]
  ext i
  fin_cases i <;>
    simp [exP, cexD, cexz, exg, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_four] <;> norm_num

lemma ex_limit : ((exX * exXᵀ * cexD * (exX * exXᵀ)) * (exX * exXᵀ * cexD * (exX * exXᵀ))).mulVec
    cexz = -cexz := by
  rw [exX_proj]
  ext i
  fin_cases i <;>
    simp [exP, cexD, cexz, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_four] <;> norm_num

set_option linter.flexible false in
lemma ex_indep (t : ℝ) :
    LinearIndependent ℝ ![cexρ t, (exX * exXᵀ * cexD).mulVec (cexρ t)] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  rw [cexρ, Matrix.mulVec_smul, ex_grad] at hab
  have h0 := congrFun hab 0
  have h1 := congrFun hab 1
  simp [cexz, exg] at h0 h1
  have h2 : a * Real.exp (-(1 / 3 * t)) = 0 := by linarith
  have h3 : b * Real.exp (-(1 / 3 * t)) = 0 := by linarith
  have he' : Real.exp (-(1 / 3 * t)) ≠ 0 := (Real.exp_pos _).ne'
  exact ⟨(mul_eq_zero.1 h2).resolve_right he', (mul_eq_zero.1 h3).resolve_right he'⟩

/-- **The hypotheses of `gap_ap_tendsto` can hold** (arXiv 2505.19929, Theorem 4.2).  On the same
grid and quadrature as `theorem_4_2_false`, with `r = 2 < N_μ = 3`, the input
`exF = z 𝟙ᵀ + (D z) P₂ᵀ` and the basis `X = span {z, D z}`, the GAP step exists for every `ε`, and
its output converges to `ρ(h) 𝟙ᵀ`. -/
theorem gap_ap_nonvacuous {h : ℝ} (hh : 0 < h) :
    ∃ (V : ℝ → Matrix (Fin 3) (Fin 2) ℝ) (ℓ k : ℝ → ℝ → Matrix (Fin 4) (Fin 3) ℝ),
      (∀ ε > 0, IsRTEGAPStep cexD cexμ cexw ε 0 (0 + h) exX (V ε) exF (ℓ ε) (k ε)) ∧
        Tendsto (fun ε => k ε (0 + h)) (𝓝[>] 0) (𝓝 (iso (cexρ (0 + h)))) := by
  have hex := fun ε : ℝ => exists_gapStep (D := cexD) cex_quad ε (t₀ := 0) (t₁ := 0 + h)
    (by linarith) exX_orth ex_start (by simp)
  choose V ℓ k hs using hex
  have hρ0 : cexρ 0 = density cexw exF := by rw [cex_ρ_zero, ex_density]
  exact ⟨V, ℓ, k, fun ε _ => hs ε, gap_ap_tendsto cex_quad cexD hh
    (cex_heat_of _ ex_limit _ _) hρ0 (ex_indep _) (cex_heat _ _) hρ0 fun ε _ => hs ε⟩

end Instance

end Concrete

end LeanDLRA.Literature.P2505_19929
