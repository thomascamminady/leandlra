import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2005.06571: Asymptotic-preserving DLRA for multiscale linear transport

This module formalizes L. Einkemmer, J. Hu, Y. Wang, *An asymptotic-preserving dynamical low-rank
method for the multi-scale multi-dimensional linear transport equation* (read in arXiv v2).  The
macro-micro system (3.3), (3.4) is discretized on arbitrary finite nodes: `Model` holds the weights
of `⟨·, ·⟩ₓ` and of the quadrature (3.46), the discrete gradient and divergence, and arbitrary
linear transport operators, so it covers the fully discrete scheme of Sec. 3.5, while the continuum
`L²(Ω)`, `L²(𝕊²)` of Sec. 3 is replaced by finite nodes.  `IsStep` is the scheme (3.15)-(3.20) and
its reorderings of Sec. 3.3, in which a QR factorization may be any factorization with orthonormal
factor; `IsStep2` is the second order scheme of Sec. 3.4.  The paper's limits are formal (`ε = 0`
in the equations).  Here they are true limits as `ε → 0` along any filter, of the scheme itself,
with data that may depend on `ε`: **Prop. 3.1** is `prop_3_1_step` (one step) and `prop_3_1` (all
steps), with the limit of rank at most three in `rank_gLim_le`; **Sec. 3.3** is the same two
theorems for `K-S-L`, `S-K-L`, and `sec_3_3_step`, `sec_3_3` for `L-K-S`, `L-S-K`, `S-L-K`;
**Sec. 3.4** is `sec_3_4` with (3.43), (3.44), and `sec_3_4_recursion` for (3.45); **Sec. 3.5.3** is
`sec_3_5_3`, on the staggered grid, for (3.57) and (3.58), at vertices and cell centers; **Sec. 4**
is `sec_4_mode_ode` for (4.4), `sec_4_band_limited` for (4.5) and `sec_4_rank_le`, for classical
solutions of (4.1) on the circle, with velocities in any Banach space (so the mode system is derived
from the equation, not assumed).  The proof of the limits replaces the paper's factorization of the
limit by one energy estimate (`energy_le`) for the relaxation on the range of a projector, valid for
both signs, including the backward `S`-step, and for the ARS(2,2,2) stages.  At `ε > 0` the
inclusion `ξ, η, γ ∈ span {Vⱼⁿ}` is lost, so the induction carries the defect `vdef`.  Three claims
of the paper are not true as printed.  (a) Prop. 3.1, for all steps, needs the three components of
`∇ₓ ρ / σ^S` to be independent along the limit: footnote 2, which dismisses this as without loss of
generality, is wrong, since (3.25) then fails and the basis may lose `v` for good
(`prop_3_1_false_without_independence`: zero data and a source; the QR factorization (3.18) of
`L¹ = 0` leaves `V¹` free, and then `g = 0` for all `n`, `ε`).  One step is true without it.
(b) The orderings `L-K-S`, `L-S-K`, `S-L-K` need `Xᵀ ∇ₓ ρ` of full column rank, uniformly in `ε`,
which the paper does not state (`sec_3_3_false_without_rank`).  On the other hand they do not need
`ξ, η, γ ∈ span {Vⱼⁿ}`.  (c) The paper calls the limit (3.45) a second-order explicit Runge-Kutta
scheme, but `ρ^{n+1}` depends on `ρ^{n-1/2}`: it is a two-step scheme, and `sec_3_4_sub_midpoint`
gives its exact difference from the explicit midpoint rule.  Informally this difference is
`O(dt³)` along smooth solutions, so the second order claimed should survive; this module proves
neither that estimate nor a convergence theorem for (3.45).  The hypotheses can hold:
`exists_step`, `exists_run`, `exists_step2` (solvability for small `ε`),
`prop_3_1_hypotheses_hold` and `exists_plane_wave`.  Not treated: Remark 3.2 (augmenting the basis
by `ξ, η, γ`), first and second order accuracy in time and space and stability for `ε > 0`, the
remark of Sec. 4 that a nonconstant `σ^S` excites new modes, and the numerical results of Sec. 5.
The library's `Novel/KineticAP.lean` treats a different scheme (the BUG scheme of arXiv 2212.12012).
-/

open Set Filter Topology Finset Asymptotics
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace LeanDLRA.Literature.P2005_06571

open LeanDLRA LeanDLRA.Frobenius

/-! ### The energy estimate of one implicit substep -/

section Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {α : Type*} {l : Filter α}

/-- `f` is bounded along `l`. -/
abbrev Bd (l : Filter α) {F : Type*} [Norm F] (f : α → F) : Prop := f =O[l] fun _ => (1 : ℝ)

/-- The energy estimate for the relaxation equation `τ u = τ P h ± P Σ (u - G)` on the range of an
orthogonal projector `P`: `u` is close to `G` when `G` nearly lies in the range of `P` and `τ` is
small.  Both signs occur: `-` in the `K`- and `L`-steps, `+` in the backward `S`-step. -/
private theorem energy_le {P Sg : E →L[ℝ] E} (hP : IsOrthProj P) {σ₀ σ₁ τ s : ℝ} (hσ₀ : 0 < σ₀)
    (hlow : ∀ x, σ₀ * ‖x‖ ^ 2 ≤ ⟪Sg x, x⟫) (hup : ∀ x, ‖Sg x‖ ≤ σ₁ * ‖x‖)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ σ₀ / 2) (hs : s = 1 ∨ s = -1) {u G h : E} (hu : P u = u)
    (heq : τ • u = τ • P h + s • P (Sg (u - G))) :
    ‖u - G‖ ≤ (1 + 2 * σ₁ / σ₀) * ‖G - P G‖ + 2 / σ₀ * (τ * ‖G‖ + τ * ‖h‖) := by
  set e := u - P G with he
  set f := G - P G with hf
  have hPe : P e = e := by rw [he, map_sub, hu, hP.idem]
  have hue : u - G = e - f := by rw [he, hf]; abel
  have hu2 : u = e + P G := by rw [he]; abel
  have h1 : ⟪τ • u, e⟫ = ⟪τ • P h + s • P (Sg (e - f)), e⟫ := by rw [heq, hue]
  have hPh : ⟪P h, e⟫ = ⟪h, e⟫ := by rw [hP.symm, hPe]
  have hPS : ⟪P (Sg (e - f)), e⟫ = ⟪Sg e, e⟫ - ⟪Sg f, e⟫ := by
    rw [hP.symm, hPe, map_sub, inner_sub_left]
  have hue2 : ⟪u, e⟫ = ‖e‖ ^ 2 + ⟪P G, e⟫ := by
    have h3 : ⟪u, e⟫ = ⟪e + P G, e⟫ := by rw [← hu2]
    rw [h3, inner_add_left, real_inner_self_eq_norm_sq]
  have h2 : τ * (‖e‖ ^ 2 + ⟪P G, e⟫) = τ * ⟪h, e⟫ + s * (⟪Sg e, e⟫ - ⟪Sg f, e⟫) := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, hPh,
      hPS, hue2] at h1
    exact h1
  have hE := hlow e
  have hf1 : ⟪Sg f, e⟫ ≤ σ₁ * ‖f‖ * ‖e‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hup f) (norm_nonneg _))
  have hf2 : -⟪Sg f, e⟫ ≤ σ₁ * ‖f‖ * ‖e‖ := by
    have := abs_real_inner_le_norm (Sg f) e
    have h3 := mul_le_mul_of_nonneg_right (hup f) (norm_nonneg e)
    linarith [neg_abs_le ⟪Sg f, e⟫]
  have hg1 : |⟪P G, e⟫| ≤ ‖G‖ * ‖e‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hP.norm_le G) (norm_nonneg _))
  have hh1 : |⟪h, e⟫| ≤ ‖h‖ * ‖e‖ := abs_real_inner_le_norm _ _
  have hg2 := abs_le.1 hg1
  have hh2 := abs_le.1 hh1
  have hne := norm_nonneg e
  have hmain : σ₀ * ‖e‖ ^ 2 ≤ τ * ‖e‖ ^ 2 + (τ * ‖G‖ + τ * ‖h‖ + σ₁ * ‖f‖) * ‖e‖ := by
    have hτg1 := mul_le_mul_of_nonneg_left hg2.1 hτ0
    have hτg2 := mul_le_mul_of_nonneg_left hg2.2 hτ0
    have hτh1 := mul_le_mul_of_nonneg_left hh2.1 hτ0
    have hτh2 := mul_le_mul_of_nonneg_left hh2.2 hτ0
    have hτe : 0 ≤ τ * ‖e‖ ^ 2 := by positivity
    rcases hs with rfl | rfl
    · nlinarith
    · nlinarith
  have hbd : ‖e‖ ≤ 2 / σ₀ * (τ * ‖G‖ + τ * ‖h‖ + σ₁ * ‖f‖) := by
    rcases eq_or_lt_of_le hne with h0 | hpos
    · rw [← h0]
      have hff : 0 ≤ σ₁ * ‖f‖ := by
        have h3 := hup f
        rcases eq_or_ne f 0 with hf0 | hf0
        · simp [hf0]
        · have hfp : 0 < ‖f‖ := norm_pos_iff.2 hf0
          have h4 : 0 ≤ σ₁ * ‖f‖ := (norm_nonneg _).trans h3
          exact h4
      positivity
    · have h3 : σ₀ / 2 * ‖e‖ ≤ τ * ‖G‖ + τ * ‖h‖ + σ₁ * ‖f‖ := by
        have h4 : (σ₀ - τ) * ‖e‖ ^ 2 ≤ (τ * ‖G‖ + τ * ‖h‖ + σ₁ * ‖f‖) * ‖e‖ := by nlinarith
        have h5 : σ₀ / 2 * ‖e‖ ^ 2 ≤ (σ₀ - τ) * ‖e‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have h6 : (σ₀ / 2 * ‖e‖) * ‖e‖ ≤ (τ * ‖G‖ + τ * ‖h‖ + σ₁ * ‖f‖) * ‖e‖ := by nlinarith
        exact le_of_mul_le_mul_right h6 hpos
      rw [div_mul_eq_mul_div, le_div_iff₀ hσ₀]
      nlinarith
  have htri : ‖u - G‖ ≤ ‖e‖ + ‖f‖ := by rw [hue]; exact norm_sub_le _ _
  have hexp : (1 + 2 * σ₁ / σ₀) * ‖f‖ + 2 / σ₀ * (τ * ‖G‖ + τ * ‖h‖) =
      2 / σ₀ * (τ * ‖G‖ + τ * ‖h‖ + σ₁ * ‖f‖) + ‖f‖ := by
    field_simp
    ring
  rw [hexp]
  linarith

/-- The family `u a` solves a relaxation equation towards `G a` on the range of `P a`, with
stiffness `1 / τ a → ∞`, of either sign, and a data term `h a` with `τ ‖h‖ → 0`. -/
structure Relaxes (l : Filter α) (Sg : E →L[ℝ] E) (P : α → E →L[ℝ] E) (G u : α → E) : Prop where
  ex : ∃ (τ : α → ℝ) (h : α → E) (s : ℝ), (s = 1 ∨ s = -1) ∧ Tendsto τ l (𝓝 0) ∧
    (∀ᶠ a in l, 0 ≤ τ a) ∧ Tendsto (fun a => τ a * ‖h a‖) l (𝓝 0) ∧
    ∀ᶠ a in l, P a (u a) = u a ∧ τ a • u a = τ a • P a (h a) + s • P a (Sg (u a - G a))

private theorem tendsto_mul_of_bd {f g : α → ℝ} (hf : Tendsto f l (𝓝 0)) (hg : Bd l g) :
    Tendsto (fun a => f a * g a) l (𝓝 0) := by
  have h1 : f =o[l] (fun _ => (1 : ℝ)) := (isLittleO_one_iff ℝ).2 hf
  have h2 := h1.mul_isBigO hg
  simpa using (isLittleO_one_iff ℝ).1 (by simpa using h2)

private theorem Bd.norm {F : Type*} [SeminormedAddCommGroup F] {f : α → F} (hf : Bd l f) :
    Bd l (fun a => ‖f a‖) := hf.norm_left

section Relax

variable {Sg : E →L[ℝ] E} {P : α → E →L[ℝ] E} {G u : α → E} {σ₀ σ₁ : ℝ}

/-- The bound `‖u - G‖ ≤ C ‖G - P G‖ + η`, with `η → 0`, from `energy_le`. -/
private theorem Relaxes.exists_bound (hR : Relaxes l Sg P G u) (hσ₀ : 0 < σ₀)
    (hlow : ∀ x, σ₀ * ‖x‖ ^ 2 ≤ ⟪Sg x, x⟫) (hup : ∀ x, ‖Sg x‖ ≤ σ₁ * ‖x‖)
    (hP : ∀ᶠ a in l, IsOrthProj (P a)) (hG : Bd l G) :
    ∃ η : α → ℝ, Tendsto η l (𝓝 0) ∧ ∀ᶠ a in l,
      ‖u a - G a‖ ≤ (1 + 2 * σ₁ / σ₀) * ‖G a - P a (G a)‖ + η a := by
  obtain ⟨τ, h, s, hs, hτ, hτ0, hτh, heq⟩ := hR.ex
  refine ⟨fun a => 2 / σ₀ * (τ a * ‖G a‖ + τ a * ‖h a‖), ?_, ?_⟩
  · have h1 := tendsto_mul_of_bd hτ hG.norm
    simpa using (h1.add hτh).const_mul (2 / σ₀)
  · have hsmall : ∀ᶠ a in l, τ a ≤ σ₀ / 2 := hτ.eventually_le_const (by positivity)
    filter_upwards [heq, hP, hτ0, hsmall] with a h1 h2 h3 h4
    exact energy_le h2 hσ₀ hlow hup h3 h4 hs h1.1 h1.2

private theorem Relaxes.tendsto (hR : Relaxes l Sg P G u) (hσ₀ : 0 < σ₀)
    (hlow : ∀ x, σ₀ * ‖x‖ ^ 2 ≤ ⟪Sg x, x⟫) (hup : ∀ x, ‖Sg x‖ ≤ σ₁ * ‖x‖)
    (hP : ∀ᶠ a in l, IsOrthProj (P a)) (hG : Bd l G)
    (hdef : Tendsto (fun a => ‖G a - P a (G a)‖) l (𝓝 0)) :
    Tendsto (fun a => ‖u a - G a‖) l (𝓝 0) := by
  obtain ⟨η, hη, hb⟩ := hR.exists_bound hσ₀ hlow hup hP hG
  have h1 := (hdef.const_mul (1 + 2 * σ₁ / σ₀)).add hη
  rw [mul_zero, zero_add] at h1
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hb h1

private theorem Relaxes.bd (hR : Relaxes l Sg P G u) (hσ₀ : 0 < σ₀)
    (hlow : ∀ x, σ₀ * ‖x‖ ^ 2 ≤ ⟪Sg x, x⟫) (hup : ∀ x, ‖Sg x‖ ≤ σ₁ * ‖x‖)
    (hP : ∀ᶠ a in l, IsOrthProj (P a)) (hG : Bd l G) : Bd l u := by
  obtain ⟨η, hη, hb⟩ := hR.exists_bound hσ₀ hlow hup hP hG
  have hηb : Bd l η := hη.isBigO_one ℝ
  have hdefb : Bd l (fun a => ‖G a - P a (G a)‖) := by
    refine IsBigO.trans (IsBigO.of_bound 2 ?_) hG
    filter_upwards [hP] with a ha
    rw [norm_norm]
    calc ‖G a - P a (G a)‖ ≤ ‖G a‖ + ‖P a (G a)‖ := norm_sub_le _ _
      _ ≤ ‖G a‖ + ‖G a‖ := by linarith [ha.norm_le (G a)]
      _ = 2 * ‖G a‖ := by ring
  have h1 : Bd l (fun a => (1 + 2 * σ₁ / σ₀) * ‖G a - P a (G a)‖ + η a) :=
    (hdefb.const_mul_left _).add hηb
  have h2 : Bd l (fun a => u a - G a) := by
    refine IsBigO.trans (IsBigO.of_bound 1 ?_) h1
    filter_upwards [hb] with a ha
    rw [one_mul]
    exact ha.trans (le_abs_self _)
  simpa using h2.add hG

/-- The residual of the relaxation equation tends to zero. -/
private theorem Relaxes.tendsto_proj (hR : Relaxes l Sg P G u) (hu : Bd l u)
    (hP : ∀ᶠ a in l, IsOrthProj (P a)) :
    Tendsto (fun a => ‖P a (Sg (u a - G a))‖) l (𝓝 0) := by
  obtain ⟨τ, h, s, hs, hτ, hτ0, hτh, heq⟩ := hR.ex
  have h1 := (tendsto_mul_of_bd hτ hu.norm).add hτh
  rw [add_zero] at h1
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
  filter_upwards [heq, hP, hτ0] with a ha hPa hτa
  have h2 : s • P a (Sg (u a - G a)) = τ a • u a - τ a • P a (h a) := by rw [ha.2]; abel
  have h3 : ‖P a (Sg (u a - G a))‖ = ‖s • P a (Sg (u a - G a))‖ := by
    rw [norm_smul]
    rcases hs with rfl | rfl <;> simp
  rw [h3, h2]
  calc ‖τ a • u a - τ a • P a (h a)‖ ≤ ‖τ a • u a‖ + ‖τ a • P a (h a)‖ := norm_sub_le _ _
    _ = τ a * ‖u a‖ + τ a * ‖P a (h a)‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hτa]
    _ ≤ τ a * ‖u a‖ + τ a * ‖h a‖ := by
      have := mul_le_mul_of_nonneg_left (hPa.norm_le (h a)) hτa
      linarith

end Relax

/-- `(ε² / c) ‖w + ε⁻¹ w'‖ → 0` for bounded `w`, `w'`. -/
private theorem tendsto_tau_norm {ε : α → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) {c : ℝ} {w w' h : α → E}
    (hc : 0 < c) (hw : Bd l w) (hw' : Bd l w') (hh : ∀ᶠ a in l, h a = w a + (ε a)⁻¹ • w' a) :
    Tendsto (fun a => ε a ^ 2 / c * ‖h a‖) l (𝓝 0) := by
  have hε0 : Tendsto ε l (𝓝 0) := tendsto_nhdsWithin_iff.1 hε |>.1
  have hεpos : ∀ᶠ a in l, 0 < ε a := tendsto_nhdsWithin_iff.1 hε |>.2
  have h1 := tendsto_mul_of_bd hε0 hw'.norm
  have hε2 : Tendsto (fun a => ε a ^ 2) l (𝓝 0) := by simpa using hε0.pow 2
  have h2 := tendsto_mul_of_bd hε2 hw.norm
  have h3 := (h1.add h2).div_const c
  simp only [zero_add, zero_div] at h3
  refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ h3
  filter_upwards [hh, hεpos] with a h4 h5
  rw [h4]
  have h6 : ‖w a + (ε a)⁻¹ • w' a‖ ≤ ‖w a‖ + (ε a)⁻¹ * ‖w' a‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have h7 : ε a ^ 2 / c * ‖w a + (ε a)⁻¹ • w' a‖ ≤ ε a ^ 2 / c * (‖w a‖ + (ε a)⁻¹ * ‖w' a‖) :=
    mul_le_mul_of_nonneg_left h6 (by positivity)
  refine h7.trans (le_of_eq ?_)
  field_simp
  ring

/-! ### Implicit substeps, lifted to the full space -/

/-- One forward-backward Euler substep with stiffness `ε⁻²`, lifted to the full space: `P` is the
orthogonal projector onto the current approximation space, `s = 1` for a `K`- or `L`-step and
`s = -1` for the backward `S`-step, `G` is the limit of the micro variable. -/
structure LiftedEuler (T Ab Sg P : E →L[ℝ] E) (s c ε : ℝ) (G u₀ u : E) : Prop where
  h₀ : P u₀ = u₀
  h₁ : P u = u
  eq : u = u₀ + (s * c) • P (-(ε⁻¹ • T u₀ + Ab u₀) - (ε ^ 2)⁻¹ • Sg (u - G))

/-- One ARS(2,2,2) substep, lifted to the full space. -/
structure LiftedARS (T Ab Sg P : E →L[ℝ] E) (s c γ δ ε : ℝ) (G u₀ u₂ u₃ : E) : Prop where
  h₀ : P u₀ = u₀
  h₂ : P u₂ = u₂
  h₃ : P u₃ = u₃
  eq₂ : u₂ = u₀ + (s * (c * γ)) • P (-(ε⁻¹ • T u₀ + Ab u₀) - (ε ^ 2)⁻¹ • Sg (u₂ - G))
  eq₃ : u₃ = u₀ + (s * c) • P (-(ε⁻¹ • (δ • T u₀ + (1 - δ) • T u₂) + δ • Ab u₀ + (1 - δ) • Ab u₂) -
    (ε ^ 2)⁻¹ • ((1 - γ) • Sg (u₂ - G) + γ • Sg (u₃ - G)))

variable {T Ab Sg : E →L[ℝ] E} {P : α → E →L[ℝ] E} {G u₀ u u₂ : α → E} {s c γ δ : ℝ}
  {ε : α → ℝ}

private theorem eventually_pos_of_tendsto {ε : α → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) : ∀ᶠ a in l, 0 <
    ε a :=
  (tendsto_nhdsWithin_iff.1 hε).2

private theorem tendsto_zero_of_tendsto {ε : α → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) : Tendsto ε l (𝓝 0)
    :=
  (tendsto_nhdsWithin_iff.1 hε).1

/-- A bounded family of forward-backward Euler substeps relaxes to `G` as `ε → 0`. -/
private theorem relaxes_of_euler (hε : Tendsto ε l (𝓝[>] 0)) (hc : 0 < c) (hs : s = 1 ∨ s = -1)
    (hu₀ : Bd l u₀)
    (hstep : ∀ᶠ a in l, LiftedEuler T Ab Sg (P a) s c (ε a) (G a) (u₀ a) (u a)) :
    Relaxes l Sg P G u := by
  have hε0 := tendsto_zero_of_tendsto hε
  have hεp := eventually_pos_of_tendsto hε
  have hτ : Tendsto (fun a => ε a ^ 2 / c) l (𝓝 0) := by simpa using (hε0.pow 2).div_const c
  refine ⟨⟨fun a => ε a ^ 2 / c,
    fun a => u₀ a + (s * c) • (-((ε a)⁻¹ • T (u₀ a) + Ab (u₀ a))), -s, ?_, hτ,
    Eventually.of_forall fun a => by positivity, ?_, ?_⟩⟩
  · rcases hs with h | h <;> simp [h]
  · refine tendsto_tau_norm hε (w := fun a => u₀ a - (s * c) • Ab (u₀ a))
      (w' := fun a => -((s * c) • T (u₀ a))) hc ?_ ?_ (Eventually.of_forall fun a => ?_)
    · exact hu₀.sub (((Ab.isBigO_comp u₀ l).trans hu₀).const_smul_left _)
    · exact (((T.isBigO_comp u₀ l).trans hu₀).const_smul_left _).neg_left
    · module
  · filter_upwards [hstep, hεp] with a ha hp
    refine ⟨ha.h₁, ?_⟩
    have hne : ε a ≠ 0 := hp.ne'
    have h1 : ε a ^ 2 / c * (s * c * (ε a ^ 2)⁻¹) = s := by field_simp
    have h2 := congrArg (fun y => (ε a ^ 2 / c) • y) ha.eq
    simp only [map_sub, map_smul, map_add, map_neg, ha.h₀] at h2 ⊢
    rw [h2]
    have h3 : ∀ y : E, (ε a ^ 2 / c * (s * c * (ε a ^ 2)⁻¹)) • y = s • y := fun y => by rw [h1]
    linear_combination (norm := module) -(h3 (P a (Sg (u a))) - h3 (P a (Sg (G a))))

/-- The third stage of a bounded family of ARS(2,2,2) substeps relaxes to `G`. -/
private theorem relaxes_of_ars {u₃ : α → E} (hε : Tendsto ε l (𝓝[>] 0)) (hc : 0 < c) (hγ : 0 < γ)
    (hs : s = 1 ∨ s = -1) (hu₀ : Bd l u₀) (hu₂ : Bd l u₂)
    (hstep : ∀ᶠ a in l, LiftedARS T Ab Sg (P a) s c γ δ (ε a) (G a) (u₀ a) (u₂ a) (u₃ a)) :
    Relaxes l Sg P G u₃ := by
  have hε0 := tendsto_zero_of_tendsto hε
  have hεp := eventually_pos_of_tendsto hε
  have hτ : Tendsto (fun a => ε a ^ 2 / (c * γ)) l (𝓝 0) := by
    simpa using (hε0.pow 2).div_const (c * γ)
  have hcγ : 0 < c * γ := by positivity
  have hTu₀ := (T.isBigO_comp u₀ l).trans hu₀
  have hTu₂ := (T.isBigO_comp u₂ l).trans hu₂
  have hAu₀ := (Ab.isBigO_comp u₀ l).trans hu₀
  have hAu₂ := (Ab.isBigO_comp u₂ l).trans hu₂
  let b : α → E := fun a => (ε a)⁻¹ • T (u₀ a) + Ab (u₀ a)
  let b₃ : α → E := fun a => (ε a)⁻¹ • (δ • T (u₀ a) + (1 - δ) • T (u₂ a)) + δ • Ab (u₀ a) +
    (1 - δ) • Ab (u₂ a)
  refine ⟨⟨fun a => ε a ^ 2 / (c * γ),
    fun a => u₀ a + ((1 - γ) / γ) • (u₂ a - u₀ a) + (s * c) • (-b₃ a + (1 - γ) • b a), -s, ?_, hτ,
    Eventually.of_forall fun a => by positivity, ?_, ?_⟩⟩
  · rcases hs with h | h <;> simp [h]
  · refine tendsto_tau_norm hε (w := fun a => u₀ a + ((1 - γ) / γ) • (u₂ a - u₀ a) +
      (s * c) • (-(δ • Ab (u₀ a) + (1 - δ) • Ab (u₂ a)) + (1 - γ) • Ab (u₀ a)))
      (w' := fun a => (s * c) • (-(δ • T (u₀ a) + (1 - δ) • T (u₂ a)) + (1 - γ) • T (u₀ a)))
      hcγ ?_ ?_ (Eventually.of_forall fun a => ?_)
    · exact (hu₀.add ((hu₂.sub hu₀).const_smul_left _)).add
        ((((hAu₀.const_smul_left _).add (hAu₂.const_smul_left _)).neg_left.add
          (hAu₀.const_smul_left _)).const_smul_left _)
    · exact ((((hTu₀.const_smul_left _).add (hTu₂.const_smul_left _)).neg_left.add
          (hTu₀.const_smul_left _)).const_smul_left _)
    · simp only [b, b₃]
      module
  · filter_upwards [hstep, hεp] with a ha hp
    refine ⟨ha.h₃, ?_⟩
    have hne : ε a ≠ 0 := hp.ne'
    have hγ' : γ ≠ 0 := hγ.ne'
    set e2 := (ε a ^ 2)⁻¹ with he2
    set p₂ := P a (Sg (u₂ a - G a)) with hp₂
    set p₃ := P a (Sg (u₃ a - G a)) with hp₃
    have gen : ∀ (x y z : E) (c1 c2 c3 : ℝ), P a (-x - c1 • (c2 • y + c3 • z)) =
        -P a x - c1 • (c2 • P a y + c3 • P a z) := by
      intro x y z c1 c2 c3
      simp only [map_sub, map_neg, map_smul, map_add]
    have gen2 : ∀ (x y : E) (c1 : ℝ), P a (-x - c1 • y) = -P a x - c1 • P a y := by
      intro x y c1
      simp only [map_sub, map_neg, map_smul]
    have eq2 : u₂ a = u₀ a + (s * (c * γ)) • (-P a (b a) - e2 • p₂) := by
      exact ha.eq₂.trans (by rw [show _ = -P a (b a) - e2 • p₂ from
        gen2 (b a) (Sg (u₂ a - G a)) (ε a ^ 2)⁻¹])
    have eq3 : u₃ a = u₀ a + (s * c) • (-P a (b₃ a) -
        e2 • ((1 - γ) • p₂ + γ • p₃)) := by
      exact ha.eq₃.trans (by rw [show _ = -P a (b₃ a) - e2 • ((1 - γ) • p₂ + γ • p₃) from
        gen (b₃ a) (Sg (u₂ a - G a)) (Sg (u₃ a - G a)) (ε a ^ 2)⁻¹ (1 - γ) γ])
    have hPh : P a (u₀ a + ((1 - γ) / γ) • (u₂ a - u₀ a) + (s * c) • (-b₃ a + (1 - γ) • b a)) =
        u₀ a + ((1 - γ) / γ) • (u₂ a - u₀ a) + (s * c) • (-P a (b₃ a) + (1 - γ) • P a (b a)) := by
      simp only [map_add, map_smul, map_sub, map_neg, ha.h₀, ha.h₂]
    rw [hPh]
    have h1 : ε a ^ 2 / (c * γ) * (s * (c * γ) * e2) = s := by rw [he2]; field_simp
    have h4 : ((1 - γ) / γ * (s * (c * γ))) = (1 - γ) * (s * c) := by field_simp
    have h5 : u₃ a = u₀ a + ((1 - γ) / γ) • (u₂ a - u₀ a) +
        (s * c) • (-P a (b₃ a) + (1 - γ) • P a (b a)) - (s * (c * γ) * e2) • p₃ := by
      have h6 : u₂ a - u₀ a = (s * (c * γ)) • (-P a (b a) - e2 • p₂) := by rw [eq2]; abel
      rw [h6, eq3, smul_smul ((1 - γ) / γ), h4]
      module
    have h7 := congrArg (fun y => (ε a ^ 2 / (c * γ)) • y) h5
    simp only [smul_sub, smul_smul] at h7
    rw [h7, h1]
    module

/-- The forward-backward Euler step `y₁ = y + dt (F y + F' y₁)` of (3.15), (3.17), (3.19). -/
def IsIMEX {Y : Type*} [Add Y] [SMul ℝ Y] (F F' : Y → Y) (dt : ℝ) (y y₁ : Y) : Prop :=
  y₁ = y + dt • (F y + F' y₁)

/-- Choice along a filter. -/
private theorem eventually_choose {β : Type*} [Nonempty β] {Q : α → β → Prop}
    (h : ∀ᶠ a in l, ∃ b, Q a b) : ∃ f : α → β, ∀ᶠ a in l, Q a (f a) := by
  have h1 : ∀ a, ∃ b, (∃ b, Q a b) → Q a b := fun a => by
    by_cases h2 : ∃ b, Q a b
    · exact ⟨h2.choose, fun _ => h2.choose_spec⟩
    · exact ⟨Classical.arbitrary β, fun h3 => (h2 h3).elim⟩
  choose f hf using h1
  exact ⟨f, h.mono fun a ha => hf a ha⟩

/-! ### From factor equations to lifted equations -/

/-- The explicit right-hand side `-(ε⁻¹ T u + ε⁻² Φ + A u)` of the micro equation (3.4), in the
full space. -/
noncomputable def exF (T Ab : E →L[ℝ] E) (Φ : E) (ε : ℝ) (u : E) : E :=
  -(ε⁻¹ • T u + (ε ^ 2)⁻¹ • Φ + Ab u)

/-- The stiff right-hand side `-ε⁻² Σ u` of the micro equation (3.4), in the full space. -/
noncomputable def imF (Sg : E →L[ℝ] E) (ε : ℝ) (u : E) : E := -((ε ^ 2)⁻¹ • Sg u)

/-- The factor substep with right-hand sides `F`, `F'` is the Galerkin projection of the micro
equation onto the range of `P`, in the lift `ℓ`, with sign `s`. -/
structure Sub (l : Filter α) (T Ab Sg : E →L[ℝ] E) (s : ℝ) (ε : α → ℝ) (Φ : α → E)
    (P : α → E →L[ℝ] E) {Y : Type*} [AddCommGroup Y] [Module ℝ Y] (ℓ : α → Y →ₗ[ℝ] E)
    (F F' : α → Y → Y) : Prop where
  range : ∀ᶠ a in l, ∀ y, P a (ℓ a y) = ℓ a y
  exp : ∀ᶠ a in l, ∀ y, ℓ a (F a y) = s • P a (exF T Ab (Φ a) (ε a) (ℓ a y))
  imp : ∀ᶠ a in l, ∀ y, ℓ a (F' a y) = s • P a (imF Sg (ε a) (ℓ a y))

section Gen

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y] {Φ : α → E} {ℓ : α → Y →ₗ[ℝ] E}
  {F F' : α → Y → Y}

private theorem lifted_euler {ℓ : Y →ₗ[ℝ] E} {F F' : Y → Y} {P : E →L[ℝ] E} {ε : ℝ} {Φ G : E}
    (hG : Sg G = -Φ) (hF : ∀ y, ℓ (F y) = s • P (exF T Ab Φ ε (ℓ y)))
    (hF' : ∀ y, ℓ (F' y) = s • P (imF Sg ε (ℓ y))) (hP : ∀ y, P (ℓ y) = ℓ y) {y y₁ : Y}
    (h : IsIMEX F F' c y y₁) : LiftedEuler T Ab Sg P s c ε G (ℓ y) (ℓ y₁) := by
  refine ⟨hP y, hP y₁, ?_⟩
  have h1 := congrArg ℓ h
  rw [map_add, map_smul, map_add, hF, hF'] at h1
  have h2 : -(ε⁻¹ • T (ℓ y) + Ab (ℓ y)) - (ε ^ 2)⁻¹ • Sg (ℓ y₁ - G) =
      exF T Ab Φ ε (ℓ y) + imF Sg ε (ℓ y₁) := by
    rw [map_sub, hG, exF, imF]
    module
  rw [h2, map_add]
  nth_rw 1 [h1]
  module

private theorem lifted_ars {ℓ : Y →ₗ[ℝ] E} {F F' : Y → Y} {P : E →L[ℝ] E} {ε : ℝ} {Φ G : E}
    (hG : Sg G = -Φ) (hF : ∀ y, ℓ (F y) = s • P (exF T Ab Φ ε (ℓ y)))
    (hF' : ∀ y, ℓ (F' y) = s • P (imF Sg ε (ℓ y))) (hP : ∀ y, P (ℓ y) = ℓ y) {y y₂ y₁ : Y}
    (h2 : y₂ = y + c • (γ • F y + γ • F' y₂))
    (h3 : y₁ = y + c • (δ • F y + (1 - δ) • F y₂ + (1 - γ) • F' y₂ + γ • F' y₁)) :
    LiftedARS T Ab Sg P s c γ δ ε G (ℓ y) (ℓ y₂) (ℓ y₁) := by
  refine ⟨hP y, hP y₂, hP y₁, ?_, ?_⟩
  · have h1 := congrArg ℓ h2
    rw [map_add, map_smul, map_add, map_smul, map_smul, hF, hF'] at h1
    have h4 : -(ε⁻¹ • T (ℓ y) + Ab (ℓ y)) - (ε ^ 2)⁻¹ • Sg (ℓ y₂ - G) =
        exF T Ab Φ ε (ℓ y) + imF Sg ε (ℓ y₂) := by
      rw [map_sub, hG, exF, imF]
      module
    rw [h4, map_add]
    nth_rw 1 [h1]
    module
  · have h1 := congrArg ℓ h3
    rw [map_add, map_smul, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
      hF, hF, hF', hF'] at h1
    have h4 : -((ε⁻¹ • (δ • T (ℓ y) + (1 - δ) • T (ℓ y₂)) + δ • Ab (ℓ y) +
        (1 - δ) • Ab (ℓ y₂))) - (ε ^ 2)⁻¹ • ((1 - γ) • Sg (ℓ y₂ - G) + γ • Sg (ℓ y₁ - G)) =
        δ • exF T Ab Φ ε (ℓ y) + (1 - δ) • exF T Ab Φ ε (ℓ y₂) + (1 - γ) • imF Sg ε (ℓ y₂) +
          γ • imF Sg ε (ℓ y₁) := by
      rw [map_sub, map_sub, hG, exF, exF, imF, imF]
      module
    rw [h4, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
    nth_rw 1 [h1]
    module

/-- A bounded family of forward-backward Euler substeps. -/
private theorem Sub.relaxes_euler (hS : Sub l T Ab Sg s ε Φ P ℓ F F') (hε : Tendsto ε l (𝓝[>] 0))
    (hc : 0 < c) (hs : s = 1 ∨ s = -1) (hG : ∀ᶠ a in l, Sg (G a) = -Φ a) {y y₁ : α → Y}
    (hu₀ : Bd l fun a => ℓ a (y a))
    (hstep : ∀ᶠ a in l, IsIMEX (F a) (F' a) c (y a) (y₁ a)) :
    Relaxes l Sg P G fun a => ℓ a (y₁ a) := by
  refine relaxes_of_euler (T := T) (Ab := Ab) hε hc hs hu₀ ?_
  filter_upwards [hS.range, hS.exp, hS.imp, hG, hstep] with a h1 h2 h3 h4 h5
  exact lifted_euler h4 h2 h3 h1 h5

/-- A bounded family of ARS(2,2,2) substeps. -/
private theorem Sub.relaxes_ars (hS : Sub l T Ab Sg s ε Φ P ℓ F F') (hε : Tendsto ε l (𝓝[>] 0))
    (hc : 0 < c) (hγ : 0 < γ) (hs : s = 1 ∨ s = -1) (hG : ∀ᶠ a in l, Sg (G a) = -Φ a)
    {σ₀ σ₁ : ℝ} (hσ₀ : 0 < σ₀) (hlow : ∀ x, σ₀ * ‖x‖ ^ 2 ≤ ⟪Sg x, x⟫)
    (hup : ∀ x, ‖Sg x‖ ≤ σ₁ * ‖x‖) (hP : ∀ᶠ a in l, IsOrthProj (P a)) (hGb : Bd l G)
    {y y₁ : α → Y} (hu₀ : Bd l fun a => ℓ a (y a))
    (hstep : ∀ᶠ a in l, ∃ y₂, y₂ = y a + c • (γ • F a (y a) + γ • F' a y₂) ∧
      y₁ a = y a + c • (δ • F a (y a) + (1 - δ) • F a y₂ + (1 - γ) • F' a y₂ + γ • F' a (y₁ a))) :
    Relaxes l Sg P G fun a => ℓ a (y₁ a) := by
  obtain ⟨y₂, hy₂⟩ := eventually_choose hstep
  have hR₂ : Relaxes l Sg P G fun a => ℓ a (y₂ a) := by
    refine relaxes_of_euler (T := T) (Ab := Ab) hε (mul_pos hc hγ) hs hu₀ ?_
    filter_upwards [hS.range, hS.exp, hS.imp, hG, hy₂] with a h1 h2 h3 h4 h5
    have h6 : IsIMEX (F a) (F' a) (c * γ) (y a) (y₂ a) := by
      rw [IsIMEX]
      nth_rw 1 [h5.1]
      module
    exact lifted_euler h4 h2 h3 h1 h6
  refine relaxes_of_ars (T := T) (Ab := Ab) (δ := δ) hε hc hγ hs hu₀
    (hR₂.bd hσ₀ hlow hup hP hGb) ?_
  filter_upwards [hS.range, hS.exp, hS.imp, hG, hy₂] with a h1 h2 h3 h4 h5
  exact lifted_ars h4 h2 h3 h1 h5.1 h5.2

end Gen

end Core

/-! ### The discrete transport problem and the substeps -/

section Model

/-- The data of the fully discrete transport equation (2.1) in macro-micro form.  `I` are the
spatial nodes of `g`, `J` those of `ρ` (they differ on the staggered grid of Sec. 3.5.2), `W` the
velocity nodes of the quadrature (3.46), `ι` indexes the components of `v`. -/
structure Model (I J W ι : Type*) where
  /-- Weights of the spatial inner product `⟨·, ·⟩ₓ`, e.g. (3.53). -/
  ωx : I → ℝ
  /-- Weights of the velocity quadrature `⟨·⟩ᵥ`, (3.46). -/
  ωv : W → ℝ
  /-- The components `ξ, η, γ` of the velocity, at the velocity nodes. -/
  vel : ι → W → ℝ
  /-- The scattering coefficient at the nodes of `g`. -/
  σS : I → ℝ
  /-- The absorption coefficient at the nodes of `g`. -/
  σA : I → ℝ
  /-- The absorption coefficient at the nodes of `ρ`. -/
  σAρ : J → ℝ
  /-- The source `G` at the nodes of `ρ`. -/
  src : J → ℝ
  /-- The components of the discrete gradient `∇ₓ ρ`, with values at the nodes of `g`. -/
  grad : ι → (J → ℝ) →ₗ[ℝ] (I → ℝ)
  /-- The components of the discrete divergence, with values at the nodes of `ρ`. -/
  dvg : ι → (I → ℝ) →ₗ[ℝ] (J → ℝ)
  /-- The operator `(I - (4π)⁻¹ ⟨·⟩ᵥ) (v · ∇ₓ ·)` used in the `K`-step, e.g. (3.49). -/
  TK : Matrix I W ℝ →ₗ[ℝ] Matrix I W ℝ
  /-- The same operator as discretized in the `L`-step, e.g. (3.54), (3.55). -/
  TL : Matrix I W ℝ →ₗ[ℝ] Matrix I W ℝ
  /-- The same operator as discretized in the `S`-step. -/
  TS : Matrix I W ℝ →ₗ[ℝ] Matrix I W ℝ

variable {I J W ι r : Type*} [Fintype I] [Fintype J] [Fintype W] [Fintype ι] [Fintype r]
  [DecidableEq I] [DecidableEq W] [DecidableEq r] [DecidableEq ι]

/-- The assumptions of the paper that the limit uses: positive weights, `σ^S > 0`, and the moments
`(4π)⁻¹ ⟨v ⊗ v⟩ᵥ = I / 3` of (2.5).  Neither `σ^A ≥ 0` nor any property of the `T`s is needed. -/
structure Model.Admissible (M : Model I J W ι) : Prop where
  ωx_pos : ∀ x, 0 < M.ωx x
  ωv_pos : ∀ w, 0 < M.ωv w
  σS_pos : ∀ x, 0 < M.σS x
  iso : ∀ m n, 1 / (4 * Real.pi) * ∑ w, M.ωv w * M.vel m w * M.vel n w = if m = n then 1 / 3 else 0

namespace Model

variable (M : Model I J W ι)

/-- The matrix of the spatial inner product. -/
def Wx : Matrix I I ℝ := Matrix.diagonal M.ωx

/-- The matrix of the velocity inner product. -/
def Wv : Matrix W W ℝ := Matrix.diagonal M.ωv

/-- The columns of this matrix are the components of `∇ₓ ρ`. -/
def gradMat (ρ : J → ℝ) : Matrix I ι ℝ := Matrix.of fun x m => M.grad m ρ x

/-- The columns of this matrix are `ξ, η, γ`. -/
def velMat : Matrix W ι ℝ := Matrix.of fun w m => M.vel m w

/-- `v · ∇ₓ ρ` at the nodes `(x, v)`. -/
def flux (ρ : J → ℝ) : Matrix I W ℝ := M.gradMat ρ * M.velMatᵀ

/-- The limit `-v · ∇ₓ ρ / σ^S` of the micro part, (2.10), (3.28). -/
noncomputable def gLim (ρ : J → ℝ) : Matrix I W ℝ :=
  -(Matrix.diagonal (fun x => (M.σS x)⁻¹) * M.flux ρ)

/-- The moment `⟨v_m g⟩ᵥ`. -/
def moment (g : Matrix I W ℝ) (m : ι) : I → ℝ := fun x => ∑ w, M.ωv w * M.vel m w * g x w

/-- `∇ₓ · ⟨v g⟩ᵥ`. -/
def divFlux (g : Matrix I W ℝ) : J → ℝ := ∑ m, M.dvg m (M.moment g m)

/-- The right-hand side of the macro equation (3.3): `-(4π)⁻¹ ∇ₓ · ⟨v g⟩ᵥ - σ^A ρ + G`. -/
noncomputable def rhoRHS (g : Matrix I W ℝ) (ρ : J → ℝ) : J → ℝ :=
  fun j => -(1 / (4 * Real.pi)) * M.divFlux g j - M.σAρ j * ρ j + M.src j

/-- The diffusion operator `∇ₓ · (∇ₓ ρ / (3 σ^S))` of (2.6). -/
noncomputable def diffOp (ρ : J → ℝ) : J → ℝ :=
  fun j => 1 / 3 * ∑ m, M.dvg m (fun x => M.grad m ρ x / M.σS x) j

/-- The right-hand side of the limiting diffusion equation (2.6). -/
noncomputable def diffRHS (ρ' ρ : J → ℝ) : J → ℝ :=
  fun j => M.diffOp ρ' j - M.σAρ j * ρ j + M.src j

/-- The forward Euler step (3.31) for the limiting diffusion equation (2.6). -/
noncomputable def eulerStep (dt : ℝ) (ρ : J → ℝ) : J → ℝ := ρ + dt • M.diffRHS ρ ρ

/-- The explicit part of (3.12), written in the scheme (3.15), with `Φ = v · ∇ₓ ρ`. -/
noncomputable def kExp (ε : ℝ) (Φ : Matrix I W ℝ) (V : Matrix W r ℝ) (K : Matrix I r ℝ) :
    Matrix I r ℝ :=
  -(ε⁻¹ • (M.TK (K * V.transpose) * M.Wv * V) + (ε ^ 2)⁻¹ • (Φ * M.Wv * V) +
    Matrix.diagonal M.σA * K)

/-- The implicit part of (3.15), `-σ^S K / ε²`. -/
noncomputable def kImp (ε : ℝ) (K : Matrix I r ℝ) : Matrix I r ℝ :=
  -((ε ^ 2)⁻¹ • (Matrix.diagonal M.σS * K))

/-- The explicit part of (3.13), written in the scheme (3.17). -/
noncomputable def lExp (ε : ℝ) (Φ : Matrix I W ℝ) (X : Matrix I r ℝ) (L : Matrix W r ℝ) :
    Matrix W r ℝ :=
  -(ε⁻¹ • ((M.TL (X * L.transpose)).transpose * M.Wx * X) +
    (ε ^ 2)⁻¹ • (Φ.transpose * M.Wx * X) + L * (X.transpose * M.Wx * Matrix.diagonal M.σA * X))

/-- The implicit part of (3.17), `-⟨X σ^S X⟩ₓ L / ε²`. -/
noncomputable def lImp (ε : ℝ) (X : Matrix I r ℝ) (L : Matrix W r ℝ) : Matrix W r ℝ :=
  -((ε ^ 2)⁻¹ • (L * (X.transpose * M.Wx * Matrix.diagonal M.σS * X)))

/-- The explicit part of (3.14), written in the scheme (3.19).  Note the sign: the `S`-step runs
backward in time. -/
noncomputable def sExp (ε : ℝ) (Φ : Matrix I W ℝ) (X : Matrix I r ℝ) (V : Matrix W r ℝ)
    (S : Matrix r r ℝ) : Matrix r r ℝ :=
  ε⁻¹ • (X.transpose * M.Wx * M.TS (X * S * V.transpose) * M.Wv * V) +
    (ε ^ 2)⁻¹ • (X.transpose * M.Wx * Φ * M.Wv * V) +
    (X.transpose * M.Wx * Matrix.diagonal M.σA * X) * S

/-- The implicit part of (3.19), `⟨X σ^S X⟩ₓ S / ε²`. -/
noncomputable def sImp (ε : ℝ) (X : Matrix I r ℝ) (S : Matrix r r ℝ) : Matrix r r ℝ :=
  (ε ^ 2)⁻¹ • ((X.transpose * M.Wx * Matrix.diagonal M.σS * X) * S)

end Model

/-- The constant `γ` of the ARS(2,2,2) tableau (3.41). -/
noncomputable def arsγ : ℝ := 1 - √2 / 2

/-- The constant `δ` of the ARS(2,2,2) tableau (3.41). -/
noncomputable def arsδ : ℝ := 1 - 1 / (2 * arsγ)

private theorem arsγ_pos : 0 < arsγ := by
  have h : √2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  unfold arsγ
  linarith

/-- One step of the ARS(2,2,2) scheme (3.38) with the double tableau (3.41), from `y` to `y₁`, with
explicit part `F` and implicit part `F'`.  Stage `1` is `y`; stage `3` is `y₁`, since the last row
of both tableaux is the weight vector. -/
def IsARS {Y : Type*} [Add Y] [SMul ℝ Y] (F F' : Y → Y) (dt : ℝ) (y y₁ : Y) : Prop :=
  ∃ y₂, y₂ = y + dt • (arsγ • F y + arsγ • F' y₂) ∧
    y₁ = y + dt • (arsδ • F y + (1 - arsδ) • F y₂ + (1 - arsγ) • F' y₂ + arsγ • F' y₁)

namespace Model

variable (M : Model I J W ι)

/-! ### The change of variables to unit weights -/

/-- Square roots of the spatial weights. -/
noncomputable def sx (x : I) : ℝ := √(M.ωx x)

/-- Square roots of the velocity weights. -/
noncomputable def sv (w : W) : ℝ := √(M.ωv w)

/-- `g ↦ Wx^{1/2} g Wv^{1/2}` turns the weighted inner product into the Frobenius one. -/
noncomputable def hat : Matrix I W ℝ →ₗ[ℝ] Matrix I W ℝ where
  toFun g := Matrix.diagonal M.sx * g * Matrix.diagonal M.sv
  map_add' g g' := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c g := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

/-- The inverse of `hat`. -/
noncomputable def unhat : Matrix I W ℝ →ₗ[ℝ] Matrix I W ℝ where
  toFun g := Matrix.diagonal (fun x => (M.sx x)⁻¹) * g * Matrix.diagonal (fun w => (M.sv w)⁻¹)
  map_add' g g' := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c g := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

/-- The orthonormal basis `Wx^{1/2} X`. -/
noncomputable def Xh (X : Matrix I r ℝ) : Matrix I r ℝ := Matrix.diagonal M.sx * X

/-- The orthonormal basis `Wv^{1/2} V`. -/
noncomputable def Vh (V : Matrix W r ℝ) : Matrix W r ℝ := Matrix.diagonal M.sv * V

/-- The velocities in the unit-weight coordinates. -/
noncomputable def velh : Matrix W ι ℝ := Matrix.diagonal M.sv * M.velMat

/-- The operator `T` in the unit-weight coordinates. -/
noncomputable def tHat (T : Matrix I W ℝ →ₗ[ℝ] Matrix I W ℝ) : Matrix I W ℝ →L[ℝ] Matrix I W ℝ :=
  LinearMap.toContinuousLinearMap (M.hat ∘ₗ T ∘ₗ M.unhat)

/-- Multiplication by `σ^S`. -/
noncomputable def Sg : Matrix I W ℝ →L[ℝ] Matrix I W ℝ := leftMulCLM (Matrix.diagonal M.σS)

/-- Multiplication by `σ^A`. -/
noncomputable def Ab : Matrix I W ℝ →L[ℝ] Matrix I W ℝ := leftMulCLM (Matrix.diagonal M.σA)

/-- The limit of the micro part in the unit-weight coordinates. -/
noncomputable def Gh (ρ : J → ℝ) : Matrix I W ℝ := M.hat (M.gLim ρ)

variable {M}

variable (M) in
/-- The Galerkin projector of the `S`-step, in the hat variables. -/
noncomputable def Gal (X : Matrix I r ℝ) (V : Matrix W r ℝ) : Matrix I W ℝ →L[ℝ] Matrix I W ℝ :=
  leftProj (M.Xh X) * rightProj (M.Vh V)

private theorem Gal_apply (X : Matrix I r ℝ) (V : Matrix W r ℝ) (Y : Matrix I W ℝ) :
    M.Gal X V Y = leftProj (M.Xh X) (rightProj (M.Vh V) Y) := rfl

private theorem hat_apply (g : Matrix I W ℝ) :
    M.hat g = Matrix.diagonal M.sx * g * Matrix.diagonal M.sv := rfl

namespace Admissible

variable (hM : M.Admissible)
include hM

private theorem sx_mul_self (x : I) : M.sx x * M.sx x = M.ωx x :=
  Real.mul_self_sqrt (hM.ωx_pos x).le

private theorem sv_mul_self (w : W) : M.sv w * M.sv w = M.ωv w :=
  Real.mul_self_sqrt (hM.ωv_pos w).le

private theorem sx_ne (x : I) : M.sx x ≠ 0 := (Real.sqrt_pos.2 (hM.ωx_pos x)).ne'

private theorem sv_ne (w : W) : M.sv w ≠ 0 := (Real.sqrt_pos.2 (hM.ωv_pos w)).ne'

private theorem Dx_mul_Dx : (Matrix.diagonal M.sx : Matrix I I ℝ) * Matrix.diagonal M.sx = M.Wx :=
    by
  rw [Matrix.diagonal_mul_diagonal, Model.Wx]
  exact congrArg _ (funext hM.sx_mul_self)

private theorem Dv_mul_Dv : (Matrix.diagonal M.sv : Matrix W W ℝ) * Matrix.diagonal M.sv = M.Wv :=
    by
  rw [Matrix.diagonal_mul_diagonal, Model.Wv]
  exact congrArg _ (funext hM.sv_mul_self)

private theorem hat_unhat (g : Matrix I W ℝ) : M.hat (M.unhat g) = g := by
  change Matrix.diagonal M.sx * (Matrix.diagonal (fun x => (M.sx x)⁻¹) * g *
    Matrix.diagonal (fun w => (M.sv w)⁻¹)) * Matrix.diagonal M.sv = g
  ext x w
  simp only [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have h1 := hM.sx_ne x
  have h2 := hM.sv_ne w
  field_simp

private theorem unhat_hat (g : Matrix I W ℝ) : M.unhat (M.hat g) = g := by
  change Matrix.diagonal (fun x => (M.sx x)⁻¹) * (Matrix.diagonal M.sx * g *
    Matrix.diagonal M.sv) * Matrix.diagonal (fun w => (M.sv w)⁻¹) = g
  ext x w
  simp only [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have h1 := hM.sx_ne x
  have h2 := hM.sv_ne w
  field_simp

private theorem tHat_hat (T : Matrix I W ℝ →ₗ[ℝ] Matrix I W ℝ) (g : Matrix I W ℝ) :
    M.tHat T (M.hat g) = M.hat (T g) := by
  change M.hat (T (M.unhat (M.hat g))) = M.hat (T g)
  rw [hM.unhat_hat]

private theorem Xh_orth {X : Matrix I r ℝ} (hX : X.transpose * M.Wx * X = 1) :
    (M.Xh X).transpose * M.Xh X = 1 := by
  rw [Model.Xh, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ _ X, hM.Dx_mul_Dx, ← Matrix.mul_assoc, hX]

private theorem Vh_orth {V : Matrix W r ℝ} (hV : V.transpose * M.Wv * V = 1) :
    (M.Vh V).transpose * M.Vh V = 1 := by
  rw [Model.Vh, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ _ V, hM.Dv_mul_Dv, ← Matrix.mul_assoc, hV]

/-- Projecting on `range V` with respect to `⟨·, ·⟩ᵥ` is `rightProj (Vh V)` in the hat variables. -/
private theorem hat_right (Y : Matrix I W ℝ) (V : Matrix W r ℝ) :
    M.hat (Y * M.Wv * V * V.transpose) = rightProj (M.Vh V) (M.hat Y) := by
  rw [rightProj_apply, hat_apply, hat_apply, Model.Vh, ← hM.Dv_mul_Dv, Matrix.transpose_mul,
    Matrix.diagonal_transpose]
  simp only [Matrix.mul_assoc]

/-- Projecting on `range X` with respect to `⟨·, ·⟩ₓ` is `leftProj (Xh X)` in the hat variables. -/
private theorem hat_left (Y : Matrix I W ℝ) (X : Matrix I r ℝ) :
    M.hat (X * X.transpose * M.Wx * Y) = leftProj (M.Xh X) (M.hat Y) := by
  rw [leftProj_apply, hat_apply, hat_apply, Model.Xh, ← hM.Dx_mul_Dx, Matrix.transpose_mul,
    Matrix.diagonal_transpose]
  simp only [Matrix.mul_assoc]

private theorem hat_mul_left (d : I → ℝ) (Y : Matrix I W ℝ) :
    M.hat (Matrix.diagonal d * Y) = Matrix.diagonal d * M.hat Y := by
  ext x w
  simp only [hat_apply, Matrix.mul_assoc, Matrix.diagonal_mul]
  ring

/-- `Σ G = -Φ` in the hat variables. -/
private theorem Sg_Gh (ρ : J → ℝ) : M.Sg (M.Gh ρ) = -M.hat (M.flux ρ) := by
  have h : (Matrix.diagonal fun x => M.σS x * (M.σS x)⁻¹) = (1 : Matrix I I ℝ) := by
    rw [← Matrix.diagonal_one]
    exact congrArg _ (funext fun x => mul_inv_cancel₀ (hM.σS_pos x).ne')
  rw [Model.Gh, Model.Sg, leftMulCLM_apply, ← hM.hat_mul_left, Model.gLim, Matrix.mul_neg,
    ← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, h, Matrix.one_mul, map_neg]

end Admissible

/-! ### The lifts of the substeps -/

variable (M) in
/-- The lift `K ↦ K Vᵀ` of the `K`-step, in the hat variables. -/
noncomputable def liftK (V : Matrix W r ℝ) : Matrix I r ℝ →ₗ[ℝ] Matrix I W ℝ where
  toFun K := M.hat (K * V.transpose)
  map_add' K K' := by rw [Matrix.add_mul, map_add]
  map_smul' c K := by rw [Matrix.smul_mul, map_smul, RingHom.id_apply]

variable (M) in
/-- The lift `L ↦ X Lᵀ` of the `L`-step, in the hat variables. -/
noncomputable def liftL (X : Matrix I r ℝ) : Matrix W r ℝ →ₗ[ℝ] Matrix I W ℝ where
  toFun L := M.hat (X * L.transpose)
  map_add' K K' := by rw [Matrix.transpose_add, Matrix.mul_add, map_add]
  map_smul' c K := by rw [Matrix.transpose_smul, Matrix.mul_smul, map_smul, RingHom.id_apply]

variable (M) in
/-- The lift `S ↦ X S Vᵀ` of the `S`-step, in the hat variables. -/
noncomputable def liftS (X : Matrix I r ℝ) (V : Matrix W r ℝ) :
    Matrix r r ℝ →ₗ[ℝ] Matrix I W ℝ where
  toFun S := M.hat (X * S * V.transpose)
  map_add' K K' := by rw [Matrix.mul_add, Matrix.add_mul, map_add]
  map_smul' c K := by rw [Matrix.mul_smul, Matrix.smul_mul, map_smul, RingHom.id_apply]

private theorem liftK_apply (V : Matrix W r ℝ) (K : Matrix I r ℝ) :
    M.liftK V K = M.hat (K * V.transpose) := rfl

private theorem liftL_apply (X : Matrix I r ℝ) (L : Matrix W r ℝ) :
    M.liftL X L = M.hat (X * L.transpose) := rfl

private theorem liftS_apply (X : Matrix I r ℝ) (V : Matrix W r ℝ) (S : Matrix r r ℝ) :
    M.liftS X V S = M.hat (X * S * V.transpose) := rfl

namespace Admissible

variable (hM : M.Admissible) {X : Matrix I r ℝ} {V : Matrix W r ℝ}
include hM

private theorem liftK_range (hV : V.transpose * M.Wv * V = 1) (K : Matrix I r ℝ) :
    rightProj (M.Vh V) (M.liftK V K) = M.liftK V K := by
  rw [liftK_apply, ← hM.hat_right]
  have h : K * V.transpose * M.Wv * V = K := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc V.transpose, hV, Matrix.mul_one]
  rw [h]

private theorem liftL_range (hX : X.transpose * M.Wx * X = 1) (L : Matrix W r ℝ) :
    leftProj (M.Xh X) (M.liftL X L) = M.liftL X L := by
  rw [liftL_apply, ← hM.hat_left]
  have h : X * X.transpose * M.Wx * (X * L.transpose) = X * L.transpose := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc X, Matrix.mul_assoc X, hX, Matrix.mul_one]
  rw [h]

private theorem liftS_range_left (hX : X.transpose * M.Wx * X = 1) (S : Matrix r r ℝ) :
    leftProj (M.Xh X) (M.liftS X V S) = M.liftS X V S := by
  have h : M.liftS X V S = M.liftL X (V * S.transpose) := by
    rw [liftS_apply, liftL_apply, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  rw [h]
  exact hM.liftL_range hX _

private theorem liftS_range_right (hV : V.transpose * M.Wv * V = 1) (S : Matrix r r ℝ) :
    rightProj (M.Vh V) (M.liftS X V S) = M.liftS X V S :=
  hM.liftK_range hV (X * S)

private theorem proj_Ab_right (hV : V.transpose * M.Wv * V = 1) (K : Matrix I r ℝ) :
    rightProj (M.Vh V) (M.Ab (M.liftK V K)) = M.Ab (M.liftK V K) := by
  rw [Model.Ab, leftMulCLM_apply]
  nth_rw 2 [← hM.liftK_range hV K]
  simp only [rightProj_apply, Matrix.mul_assoc]

private theorem liftK_exp (hV : V.transpose * M.Wv * V = 1) (ε : ℝ) (Φ : Matrix I W ℝ)
    (K : Matrix I r ℝ) :
    M.liftK V (M.kExp ε Φ V K) =
      rightProj (M.Vh V) (exF (M.tHat M.TK) M.Ab (M.hat Φ) ε (M.liftK V K)) := by
  simp only [exF, map_neg, map_add, map_smul, hM.proj_Ab_right hV]
  rw [liftK_apply, liftK_apply, Model.kExp, Matrix.neg_mul, Matrix.add_mul, Matrix.add_mul,
    Matrix.smul_mul, Matrix.smul_mul, map_neg, map_add, map_add, map_smul, map_smul,
    hM.hat_right, hM.hat_right, hM.tHat_hat, Matrix.mul_assoc (Matrix.diagonal M.σA),
    hM.hat_mul_left, Model.Ab, leftMulCLM_apply]

private theorem liftK_imp (hV : V.transpose * M.Wv * V = 1) (ε : ℝ) (K : Matrix I r ℝ) :
    M.liftK V (M.kImp ε K) = rightProj (M.Vh V) (imF M.Sg ε (M.liftK V K)) := by
  have h1 : rightProj (M.Vh V) (M.Sg (M.liftK V K)) = M.Sg (M.liftK V K) := by
    rw [Model.Sg, leftMulCLM_apply]
    nth_rw 2 [← hM.liftK_range hV K]
    simp only [rightProj_apply, Matrix.mul_assoc]
  rw [imF, map_neg, map_smul, h1, liftK_apply, liftK_apply, Model.kImp, Matrix.neg_mul,
    Matrix.smul_mul, map_neg, map_smul, Matrix.mul_assoc, hM.hat_mul_left, Model.Sg,
    leftMulCLM_apply]

private theorem transpose_Wx : (M.Wx).transpose = M.Wx := Matrix.diagonal_transpose _

private theorem stiff_symm (d : I → ℝ) (X : Matrix I r ℝ) :
    (X.transpose * M.Wx * Matrix.diagonal d * X).transpose =
      X.transpose * M.Wx * Matrix.diagonal d * X := by
  have h : (M.Wx * Matrix.diagonal d).transpose = M.Wx * Matrix.diagonal d := by
    rw [Matrix.transpose_mul, Matrix.diagonal_transpose, Model.Wx, Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    simp only [mul_comm]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc _ M.Wx.transpose, ← Matrix.transpose_mul, h]
  simp only [Matrix.mul_assoc]

private theorem liftL_exp (ε : ℝ) (Φ : Matrix I W ℝ) (L : Matrix W r ℝ) :
    M.liftL X (M.lExp ε Φ X L) =
      leftProj (M.Xh X) (exF (M.tHat M.TL) M.Ab (M.hat Φ) ε (M.liftL X L)) := by
  simp only [exF, map_neg, map_add, map_smul]
  have h1 : M.hat (X * (L * (X.transpose * M.Wx * Matrix.diagonal M.σA * X)).transpose) =
      leftProj (M.Xh X) (M.Ab (M.liftL X L)) := by
    rw [liftL_apply, Model.Ab, leftMulCLM_apply, ← hM.hat_mul_left, ← hM.hat_left,
      Matrix.transpose_mul, hM.stiff_symm]
    simp only [Matrix.mul_assoc]
  have h2 : ∀ Z : Matrix I W ℝ, M.hat (X * (Z.transpose * M.Wx * X).transpose) =
      leftProj (M.Xh X) (M.hat Z) := fun Z => by
    rw [← hM.hat_left, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hM.transpose_Wx]
    simp only [Matrix.mul_assoc]
  rw [liftL_apply, liftL_apply, Model.lExp, Matrix.transpose_neg, Matrix.transpose_add,
    Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.mul_neg,
    Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, map_neg, map_add, map_add,
    map_smul, map_smul, h2, h2, h1, hM.tHat_hat, liftL_apply]

private theorem liftL_imp (ε : ℝ) (L : Matrix W r ℝ) :
    M.liftL X (M.lImp ε X L) = leftProj (M.Xh X) (imF M.Sg ε (M.liftL X L)) := by
  have h1 : M.hat (X * (L * (X.transpose * M.Wx * Matrix.diagonal M.σS * X)).transpose) =
      leftProj (M.Xh X) (M.Sg (M.liftL X L)) := by
    rw [liftL_apply, Model.Sg, leftMulCLM_apply, ← hM.hat_mul_left, ← hM.hat_left,
      Matrix.transpose_mul, hM.stiff_symm]
    simp only [Matrix.mul_assoc]
  rw [imF, map_neg, map_smul, ← h1, liftL_apply, Model.lImp, Matrix.transpose_neg,
    Matrix.transpose_smul, Matrix.mul_neg, Matrix.mul_smul, map_neg, map_smul]

private theorem hat_both (X : Matrix I r ℝ) (V : Matrix W r ℝ) (Y : Matrix I W ℝ) :
    M.hat (X * (X.transpose * M.Wx * Y * M.Wv * V) * V.transpose) =
      M.Gal X V (M.hat Y) := by
  rw [Gal_apply, ← hM.hat_right, ← hM.hat_left]
  simp only [Matrix.mul_assoc]

private theorem liftS_exp (hV : V.transpose * M.Wv * V = 1) (ε : ℝ) (Φ : Matrix I W ℝ) (S : Matrix
    r r ℝ) :
    M.liftS X V (M.sExp ε Φ X V S) = (-1 : ℝ) • M.Gal X V
      (exF (M.tHat M.TS) M.Ab (M.hat Φ) ε (M.liftS X V S)) := by
  have h1 : M.hat (X * (X.transpose * M.Wx * Matrix.diagonal M.σA * X * S) * V.transpose) =
      M.Gal X V (M.Ab (M.liftS X V S)) := by
    have h2 : rightProj (M.Vh V) (M.Ab (M.liftS X V S)) = M.Ab (M.liftS X V S) :=
      hM.proj_Ab_right hV (X * S)
    rw [Gal_apply, h2, liftS_apply, Model.Ab, leftMulCLM_apply,
      ← hM.hat_mul_left, ← hM.hat_left]
    simp only [Matrix.mul_assoc]
  simp only [exF, map_neg, map_add, map_smul, Gal_apply, neg_one_smul, neg_neg, map_neg]
  simp only [← Gal_apply]
  rw [liftS_apply, liftS_apply, Model.sExp, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, map_add,
    map_add, map_smul, map_smul, hM.hat_both, hM.hat_both, h1, hM.tHat_hat, liftS_apply]

private theorem liftS_imp (hV : V.transpose * M.Wv * V = 1) (ε : ℝ) (S : Matrix r r ℝ) :
    M.liftS X V (M.sImp ε X S) = (-1 : ℝ) • M.Gal X V
      (imF M.Sg ε (M.liftS X V S)) := by
  have h1 : M.hat (X * (X.transpose * M.Wx * Matrix.diagonal M.σS * X * S) * V.transpose) =
      M.Gal X V (M.Sg (M.liftS X V S)) := by
    have h2 : rightProj (M.Vh V) (M.Sg (M.liftS X V S)) = M.Sg (M.liftS X V S) := by
      rw [Model.Sg, leftMulCLM_apply]
      nth_rw 2 [← hM.liftS_range_right hV S]
      simp only [rightProj_apply, Matrix.mul_assoc]
    rw [Gal_apply, h2, liftS_apply, Model.Sg, leftMulCLM_apply,
      ← hM.hat_mul_left, ← hM.hat_left]
    simp only [Matrix.mul_assoc]
  simp only [imF, map_neg, map_smul, Gal_apply, neg_one_smul, neg_neg]
  simp only [← Gal_apply]
  rw [liftS_apply, Model.sImp, Matrix.mul_smul, Matrix.smul_mul, map_smul, h1]

end Admissible

end Model

/-! ### The six orderings of the first order scheme -/

/-- The six orderings of the substeps in Sec. 3.1 and Sec. 3.3. -/
inductive Order
  | KLS | LKS | LSK | SLK | KSL | SKL

namespace Model

variable (M : Model I J W ι)

/-- The three substeps, in the given order, from `(X, S, V)` to `(X₁, S₁, V₁)`, with `Φ = v · ∇ₓ ρⁿ`
frozen.  `K₁ = X₁ S'` and `L₁ = V₁ S''ᵀ` are the factorizations (3.16), (3.18), with any orthonormal
factor: a QR factorization of a rank-deficient matrix has arbitrary further columns. -/
def IsMicro (o : Order) (dt ε : ℝ) (Φ : Matrix I W ℝ) (X : Matrix I r ℝ) (S : Matrix r r ℝ)
    (V : Matrix W r ℝ) (X₁ : Matrix I r ℝ) (S₁ : Matrix r r ℝ) (V₁ : Matrix W r ℝ) : Prop :=
  match o with
  | .KLS => ∃ (K₁ : Matrix I r ℝ) (S' : Matrix r r ℝ) (L₁ : Matrix W r ℝ) (S'' : Matrix r r ℝ),
      IsIMEX (M.kExp ε Φ V) (M.kImp ε) dt (X * S) K₁ ∧ K₁ = X₁ * S' ∧
      IsIMEX (M.lExp ε Φ X₁) (M.lImp ε X₁) dt (V * S'.transpose) L₁ ∧ L₁ = V₁ * S''.transpose ∧
      IsIMEX (M.sExp ε Φ X₁ V₁) (M.sImp ε X₁) dt S'' S₁
  | .LKS => ∃ (L₁ : Matrix W r ℝ) (S' : Matrix r r ℝ) (K₁ : Matrix I r ℝ) (S'' : Matrix r r ℝ),
      IsIMEX (M.lExp ε Φ X) (M.lImp ε X) dt (V * S.transpose) L₁ ∧ L₁ = V₁ * S'.transpose ∧
      IsIMEX (M.kExp ε Φ V₁) (M.kImp ε) dt (X * S') K₁ ∧ K₁ = X₁ * S'' ∧
      IsIMEX (M.sExp ε Φ X₁ V₁) (M.sImp ε X₁) dt S'' S₁
  | .LSK => ∃ (L₁ : Matrix W r ℝ) (S' S'' : Matrix r r ℝ) (K₁ : Matrix I r ℝ),
      IsIMEX (M.lExp ε Φ X) (M.lImp ε X) dt (V * S.transpose) L₁ ∧ L₁ = V₁ * S'.transpose ∧
      IsIMEX (M.sExp ε Φ X V₁) (M.sImp ε X) dt S' S'' ∧
      IsIMEX (M.kExp ε Φ V₁) (M.kImp ε) dt (X * S'') K₁ ∧ K₁ = X₁ * S₁
  | .SLK => ∃ (S' : Matrix r r ℝ) (L₁ : Matrix W r ℝ) (S'' : Matrix r r ℝ) (K₁ : Matrix I r ℝ),
      IsIMEX (M.sExp ε Φ X V) (M.sImp ε X) dt S S' ∧
      IsIMEX (M.lExp ε Φ X) (M.lImp ε X) dt (V * S'.transpose) L₁ ∧ L₁ = V₁ * S''.transpose ∧
      IsIMEX (M.kExp ε Φ V₁) (M.kImp ε) dt (X * S'') K₁ ∧ K₁ = X₁ * S₁
  | .KSL => ∃ (K₁ : Matrix I r ℝ) (S' S'' : Matrix r r ℝ) (L₁ : Matrix W r ℝ),
      IsIMEX (M.kExp ε Φ V) (M.kImp ε) dt (X * S) K₁ ∧ K₁ = X₁ * S' ∧
      IsIMEX (M.sExp ε Φ X₁ V) (M.sImp ε X₁) dt S' S'' ∧
      IsIMEX (M.lExp ε Φ X₁) (M.lImp ε X₁) dt (V * S''.transpose) L₁ ∧ L₁ = V₁ * S₁.transpose
  | .SKL => ∃ (S' : Matrix r r ℝ) (K₁ : Matrix I r ℝ) (S'' : Matrix r r ℝ) (L₁ : Matrix W r ℝ),
      IsIMEX (M.sExp ε Φ X V) (M.sImp ε X) dt S S' ∧
      IsIMEX (M.kExp ε Φ V) (M.kImp ε) dt (X * S') K₁ ∧ K₁ = X₁ * S'' ∧
      IsIMEX (M.lExp ε Φ X₁) (M.lImp ε X₁) dt (V * S''.transpose) L₁ ∧ L₁ = V₁ * S₁.transpose

/-- One step of the first order scheme: the substeps, in the given order, with `ρⁿ` frozen, then
the `ρ`-step (3.20).  For `o = .KLS` this is the `K`-`L`-`S`-`ρ` scheme (3.15)-(3.20). -/
structure IsStep (o : Order) (dt ε : ℝ) (ρ : J → ℝ) (X : Matrix I r ℝ) (S : Matrix r r ℝ)
    (V : Matrix W r ℝ) (ρ₁ : J → ℝ) (X₁ : Matrix I r ℝ) (S₁ : Matrix r r ℝ)
    (V₁ : Matrix W r ℝ) : Prop where
  hX : X.transpose * M.Wx * X = 1
  hV : V.transpose * M.Wv * V = 1
  hX₁ : X₁.transpose * M.Wx * X₁ = 1
  hV₁ : V₁.transpose * M.Wv * V₁ = 1
  micro : M.IsMicro o dt ε (M.flux ρ) X S V X₁ S₁ V₁
  rho : ρ₁ = ρ + dt • M.rhoRHS (X₁ * S₁ * V₁.transpose) ρ

/-- The components of `∇ₓ ρ / σ^S`, as columns. -/
noncomputable def Bh (ρ : J → ℝ) : Matrix I ι ℝ :=
  Matrix.diagonal M.sx * (Matrix.diagonal (fun x => (M.σS x)⁻¹) * M.gradMat ρ)

/-- How far `ξ, η, γ` are from the span of the columns of `V`. -/
noncomputable def vdef (V : Matrix W r ℝ) : ℝ :=
  ‖M.velh.transpose - M.velh.transpose * M.Vh V * (M.Vh V).transpose‖

/-- `ξ, η, γ ∈ span {V_j}`, the hypothesis of Prop. 3.1. -/
def VelInSpan (V : Matrix W r ℝ) : Prop :=
  ∀ m, M.vel m ∈ Submodule.span ℝ (Set.range V.transpose)

/-- The components of `∇ₓ ρ / σ^S` are linearly independent: the assumption of the proof of
Prop. 3.1. -/
def IndepGrad (ρ : J → ℝ) : Prop :=
  LinearIndependent ℝ (fun m x => M.grad m ρ x / M.σS x)

/-- `gradMat` as a linear map. -/
noncomputable def gradL : (J → ℝ) →ₗ[ℝ] Matrix I ι ℝ where
  toFun := M.gradMat
  map_add' ρ ρ' := by
    ext x m
    simp [gradMat]
  map_smul' c ρ := by
    ext x m
    simp [gradMat]

/-- `divFlux` as a linear map. -/
noncomputable def divFluxL : Matrix I W ℝ →ₗ[ℝ] (J → ℝ) where
  toFun := M.divFlux
  map_add' g g' := by
    have h : ∀ m, M.moment (g + g') m = M.moment g m + M.moment g' m := fun m => by
      ext x
      simp [moment, mul_add, Finset.sum_add_distrib]
    simp only [divFlux, h, map_add, Finset.sum_add_distrib]
  map_smul' c g := by
    have h : ∀ m, M.moment (c • g) m = c • M.moment g m := fun m => by
      ext x
      simp only [moment, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring
    simp only [divFlux, h, map_smul, RingHom.id_apply, Finset.smul_sum]

variable {M}

private theorem continuous_gLim : Continuous M.gLim := by
  have h : M.gLim = fun ρ => -(Frobenius.leftMulCLM (Matrix.diagonal fun x => (M.σS x)⁻¹)
      (Frobenius.rightMulCLM M.velMat.transpose (M.gradL ρ))) := rfl
  rw [h]
  exact ((ContinuousLinearMap.continuous _).comp ((ContinuousLinearMap.continuous _).comp
    M.gradL.continuous_of_finiteDimensional)).neg

private theorem continuous_hat : Continuous M.hat := M.hat.continuous_of_finiteDimensional

private theorem continuous_unhat : Continuous M.unhat := M.unhat.continuous_of_finiteDimensional

private theorem continuous_Gh : Continuous M.Gh := continuous_hat.comp continuous_gLim

private theorem continuous_Bh : Continuous M.Bh := by
  have h : M.Bh = fun ρ => Frobenius.leftMulCLM (Matrix.diagonal M.sx)
      (Frobenius.leftMulCLM (Matrix.diagonal fun x => (M.σS x)⁻¹) (M.gradL ρ)) := rfl
  rw [h]
  exact (ContinuousLinearMap.continuous _).comp ((ContinuousLinearMap.continuous _).comp
    M.gradL.continuous_of_finiteDimensional)

private theorem tendsto_rhoRHS {α : Type*} {l : Filter α} {g : α → Matrix I W ℝ} {g₀ : Matrix I W ℝ}
    {ρ : α → J → ℝ} {ρ₀ : J → ℝ} (hg : Tendsto g l (𝓝 g₀)) (hρ : Tendsto ρ l (𝓝 ρ₀)) :
    Tendsto (fun a => M.rhoRHS (g a) (ρ a)) l (𝓝 (M.rhoRHS g₀ ρ₀)) := by
  refine tendsto_pi_nhds.2 fun j => ?_
  have h1 : Tendsto (fun a => M.divFlux (g a) j) l (𝓝 (M.divFlux g₀ j)) :=
    tendsto_pi_nhds.1 ((M.divFluxL.continuous_of_finiteDimensional.tendsto g₀).comp hg) j
  have h2 := tendsto_pi_nhds.1 hρ j
  simp only [Model.rhoRHS]
  exact ((h1.const_mul _).sub (h2.const_mul _)).add_const _

namespace Admissible

variable (hM : M.Admissible)
include hM

private theorem gLim_apply (ρ : J → ℝ) (x : I) (w : W) :
    M.gLim ρ x w = -((M.σS x)⁻¹ * ∑ n, M.grad n ρ x * M.vel n w) := by
  rw [Model.gLim, Matrix.neg_apply, Matrix.diagonal_mul]
  simp only [Model.flux, Matrix.mul_apply, Matrix.transpose_apply, Model.gradMat, Model.velMat,
    Matrix.of_apply]

private theorem moment_gLim (ρ : J → ℝ) (m : ι) :
    M.moment (M.gLim ρ) m = (-(4 * Real.pi / 3)) • fun x => M.grad m ρ x / M.σS x := by
  have hπ : (4 * Real.pi) ≠ 0 := by positivity
  have hiso : ∀ n, ∑ w, M.ωv w * M.vel m w * M.vel n w = 4 * Real.pi * if m = n then 1 / 3 else 0 :=
    fun n => by
      rw [← hM.iso m n]
      field_simp
  ext x
  simp only [Model.moment, hM.gLim_apply, Pi.smul_apply, smul_eq_mul]
  calc ∑ w, M.ωv w * M.vel m w * -((M.σS x)⁻¹ * ∑ n, M.grad n ρ x * M.vel n w)
      = ∑ n, -((M.σS x)⁻¹ * M.grad n ρ x) * ∑ w, M.ωv w * M.vel m w * M.vel n w := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n _ => ?_
        simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun w _ => ?_
        ring
    _ = -(4 * Real.pi / 3) * (M.grad m ρ x / M.σS x) := by
        simp only [hiso]
        rw [Finset.sum_eq_single m]
        · simp only [ite_true]
          ring
        · intro n _ hn
          simp [hn.symm]
        · simp

/-- Substituting the limit `g = -v · ∇ₓ ρ / σ^S` in the macro equation gives the right-hand side of
the diffusion equation (2.6), through `(4π)⁻¹ ⟨v ⊗ v⟩ᵥ = I / 3`. -/
private theorem rhoRHS_gLim (ρ ρ' : J → ℝ) : M.rhoRHS (M.gLim ρ) ρ' = M.diffRHS ρ ρ' := by
  ext j
  have hπ : (4 * Real.pi) ≠ 0 := by positivity
  simp only [Model.rhoRHS, Model.diffRHS, Model.diffOp, Model.divFlux, hM.moment_gLim, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have : -(1 / (4 * Real.pi)) * ∑ m, -(4 * Real.pi / 3) * M.dvg m (fun x => M.grad m ρ x / M.σS x) j
      = 1 / 3 * ∑ m, M.dvg m (fun x => M.grad m ρ x / M.σS x) j := by
    rw [← Finset.mul_sum, ← mul_assoc]
    field_simp
  rw [this]

private theorem Gh_eq (ρ : J → ℝ) : M.Gh ρ = -(M.Bh ρ * M.velh.transpose) := by
  rw [Model.Gh, Model.gLim, map_neg, hat_apply, Model.Bh, Model.flux, Model.velh,
    Matrix.transpose_mul, Matrix.diagonal_transpose]
  simp only [Matrix.mul_assoc]

private theorem defect_eq (ρ : J → ℝ) (V : Matrix W r ℝ) :
    M.Gh ρ - rightProj (M.Vh V) (M.Gh ρ) = -(M.Bh ρ *
      (M.velh.transpose - M.velh.transpose * M.Vh V * (M.Vh V).transpose)) := by
  rw [hM.Gh_eq, rightProj_apply]
  simp only [Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_assoc]
  abel

private theorem defect_le (ρ : J → ℝ) (V : Matrix W r ℝ) :
    ‖M.Gh ρ - rightProj (M.Vh V) (M.Gh ρ)‖ ≤ ‖M.Bh ρ‖ * M.vdef V := by
  rw [hM.defect_eq, norm_neg]
  exact Frobenius.norm_mul_le _ _

private theorem vdef_eq_zero {V : Matrix W r ℝ} (hV : V.transpose * M.Wv * V = 1) (h : M.VelInSpan
    V) :
    M.vdef V = 0 := by
  have h1 : ∀ m, ∃ c : r → ℝ, M.vel m = V.mulVec c := fun m => by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (h m)
    refine ⟨c, ?_⟩
    rw [← hc]
    ext w
    simp [Matrix.mulVec, dotProduct, mul_comm]
  choose c hc using h1
  have h2 : M.velMat = V * Matrix.of fun j m => c m j := by
    ext w m
    simp only [Model.velMat, Matrix.of_apply, hc, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have h3 : M.velh = M.Vh V * Matrix.of fun j m => c m j := by
    rw [Model.velh, h2, Model.Vh, Matrix.mul_assoc]
  have hV' := hM.Vh_orth hV
  rw [vdef, h3, Matrix.transpose_mul]
  have h4 : (Matrix.of fun j m => c m j).transpose * (M.Vh V).transpose * M.Vh V *
      (M.Vh V).transpose = (Matrix.of fun j m => c m j).transpose * (M.Vh V).transpose := by
    rw [Matrix.mul_assoc _ _ (M.Vh V), hV', Matrix.mul_one]
  rw [h4, sub_self, norm_zero]

private theorem bounds : ∃ σ₀ σ₁ : ℝ, 0 < σ₀ ∧ (∀ x : Matrix I W ℝ, σ₀ * ‖x‖ ^ 2 ≤ ⟪M.Sg x, x⟫) ∧
    ∀ x : Matrix I W ℝ, ‖M.Sg x‖ ≤ σ₁ * ‖x‖ := by
  have hc : ∃ σ₀ σ₁ : ℝ, 0 < σ₀ ∧ 0 ≤ σ₁ ∧ (∀ x, σ₀ ≤ M.σS x) ∧ ∀ x, M.σS x ≤ σ₁ := by
    rcases isEmpty_or_nonempty I with h | h
    · exact ⟨1, 1, one_pos, zero_le_one, fun i => h.elim i, fun i => h.elim i⟩
    · obtain ⟨x₀, hx₀⟩ := Finite.exists_min M.σS
      obtain ⟨x₁, hx₁⟩ := Finite.exists_max M.σS
      exact ⟨M.σS x₀, M.σS x₁, hM.σS_pos x₀, (hM.σS_pos x₁).le, hx₀, hx₁⟩
  obtain ⟨σ₀, σ₁, h0, h1, hlo, hhi⟩ := hc
  refine ⟨σ₀, σ₁, h0, fun x => ?_, fun x => ?_⟩
  · rw [Model.Sg, leftMulCLM_apply, inner_def, Frobenius.norm_sq_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Matrix.diagonal_mul]
    have := hlo i
    nlinarith [sq_nonneg (x i j)]
  · have hsq : ‖M.Sg x‖ ^ 2 ≤ (σ₁ * ‖x‖) ^ 2 := by
      rw [mul_pow, Model.Sg, leftMulCLM_apply, Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum,
        Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [Matrix.diagonal_mul, mul_pow]
      have h3 : M.σS i ^ 2 ≤ σ₁ ^ 2 := by
        have h4 := hM.σS_pos i
        have h5 := hhi i
        nlinarith
      exact mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
    exact abs_le_of_sq_le_sq' hsq (by positivity) |>.2

end Admissible

end Model

section Chain

section AbstractChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {α : Type*} {l : Filter α}
  {Sg : E →L[ℝ] E} {P Q : α → E →L[ℝ] E} {G u u' : α → E}

private theorem Relaxes.congr (h : Relaxes l Sg P G u) (he : ∀ᶠ a in l, u a = u' a) :
    Relaxes l Sg P G u' := by
  obtain ⟨τ, g, s, hs, hτ, hτ0, hτh, heq⟩ := h.ex
  refine ⟨⟨τ, g, s, hs, hτ, hτ0, hτh, ?_⟩⟩
  filter_upwards [heq, he] with a h1 h2
  rw [← h2]
  exact h1

/-- A basis capturing `u` captures its limit `G`. -/
private theorem capture_def (hP : ∀ᶠ a in l, IsOrthProj (P a)) (hu : ∀ᶠ a in l, P a (u a) = u a)
    (h : Tendsto (fun a => ‖u a - G a‖) l (𝓝 0)) :
    Tendsto (fun a => ‖G a - P a (G a)‖) l (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h
  filter_upwards [hP, hu] with a h1 h2
  rw [norm_sub_rev (u a)]
  exact h1.norm_sub_le_of_mem_range _ _ h2

private theorem mul_def (hP : ∀ᶠ a in l, IsOrthProj (P a))
    (h1 : Tendsto (fun a => ‖G a - P a (G a)‖) l (𝓝 0))
    (h2 : Tendsto (fun a => ‖G a - Q a (G a)‖) l (𝓝 0)) :
    Tendsto (fun a => ‖G a - (P a * Q a) (G a)‖) l (𝓝 0) := by
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h3
  filter_upwards [hP] with a ha
  have h4 : G a - (P a * Q a) (G a) = (G a - P a (G a)) + P a (G a - Q a (G a)) := by
    rw [map_sub]
    change _ = _ + (_ - P a (Q a (G a)))
    change G a - P a (Q a (G a)) = _
    abel
  rw [h4]
  exact (norm_add_le _ _).trans (by linarith [ha.norm_le (G a - Q a (G a))])

private theorem bd_of_tendsto (h : Tendsto (fun a => ‖u a - G a‖) l (𝓝 0)) (hG : Bd l G) : Bd l u
    := by
  have h1 : Bd l (fun a => u a - G a) := (isBigO_norm_left.1 (h.isBigO_one ℝ))
  simpa using h1.add hG

end AbstractChain

variable {M : Model I J W ι} {α : Type*} {l : Filter α} {ε : α → ℝ} {ρ ρ₁ : α → J → ℝ}

/-- The conclusion of the three substeps: the micro part converges to its limit, and the new basis
`V₁` captures this limit. -/
structure MicroConv (l : Filter α) (M : Model I J W ι) (ρ : α → J → ℝ) (X₁ : α → Matrix I r ℝ)
    (S₁ : α → Matrix r r ℝ) (V₁ : α → Matrix W r ℝ) : Prop where
  conv : Tendsto (fun a => ‖M.liftS (X₁ a) (V₁ a) (S₁ a) - M.Gh (ρ a)‖) l (𝓝 0)
  defect : Tendsto (fun a => ‖M.Gh (ρ a) - rightProj (M.Vh (V₁ a)) (M.Gh (ρ a))‖) l (𝓝 0)

namespace Model

private theorem liftK_eq (X : Matrix I r ℝ) (S : Matrix r r ℝ) (V : Matrix W r ℝ) :
    M.liftK V (X * S) = M.liftS X V S := rfl

private theorem liftL_eq (X : Matrix I r ℝ) (S : Matrix r r ℝ) (V : Matrix W r ℝ) :
    M.liftL X (V * S.transpose) = M.liftS X V S := by
  rw [liftL_apply, liftS_apply, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

namespace Admissible

variable (hM : M.Admissible)
include hM

private theorem subK {V : α → Matrix W r ℝ} (hV : ∀ᶠ a in l, (V a).transpose * M.Wv * V a = 1)
    (Φ : α → Matrix I W ℝ) :
    Sub l (M.tHat M.TK) M.Ab M.Sg 1 ε (fun a => M.hat (Φ a)) (fun a => rightProj (M.Vh (V a)))
      (fun a => M.liftK (V a)) (fun a => M.kExp (ε a) (Φ a) (V a)) (fun a => M.kImp (ε a)) where
  range := by filter_upwards [hV] with a ha y using hM.liftK_range ha y
  exp := by
    filter_upwards [hV] with a ha y
    rw [one_smul]
    exact hM.liftK_exp ha _ _ y
  imp := by
    filter_upwards [hV] with a ha y
    rw [one_smul]
    exact hM.liftK_imp ha _ y

private theorem subL {X : α → Matrix I r ℝ} (hX : ∀ᶠ a in l, (X a).transpose * M.Wx * X a = 1)
    (Φ : α → Matrix I W ℝ) :
    Sub l (M.tHat M.TL) M.Ab M.Sg 1 ε (fun a => M.hat (Φ a)) (fun a => leftProj (M.Xh (X a)))
      (fun a => M.liftL (X a)) (fun a => M.lExp (ε a) (Φ a) (X a))
      (fun a => M.lImp (ε a) (X a)) where
  range := by filter_upwards [hX] with a ha y using hM.liftL_range ha y
  exp := Eventually.of_forall fun _ y => by
    rw [one_smul]
    exact hM.liftL_exp _ _ y
  imp := Eventually.of_forall fun _ y => by
    rw [one_smul]
    exact hM.liftL_imp _ y

private theorem subS {X : α → Matrix I r ℝ} {V : α → Matrix W r ℝ}
    (hX : ∀ᶠ a in l, (X a).transpose * M.Wx * X a = 1)
    (hV : ∀ᶠ a in l, (V a).transpose * M.Wv * V a = 1) (Φ : α → Matrix I W ℝ) :
    Sub l (M.tHat M.TS) M.Ab M.Sg (-1) ε (fun a => M.hat (Φ a)) (fun a => M.Gal (X a) (V a))
      (fun a => M.liftS (X a) (V a)) (fun a => M.sExp (ε a) (Φ a) (X a) (V a))
      (fun a => M.sImp (ε a) (X a)) where
  range := by
    filter_upwards [hX, hV] with a h1 h2 y
    rw [Gal_apply, hM.liftS_range_right h2, hM.liftS_range_left h1]
  exp := by
    filter_upwards [hV] with a ha y
    exact hM.liftS_exp ha _ _ y
  imp := by
    filter_upwards [hV] with a ha y
    exact hM.liftS_imp ha _ y

private theorem orthL {X : α → Matrix I r ℝ} (hX : ∀ᶠ a in l, (X a).transpose * M.Wx * X a = 1) :
    ∀ᶠ a in l, IsOrthProj (leftProj (M.Xh (X a)) : Matrix I W ℝ →L[ℝ] Matrix I W ℝ) :=
  hX.mono fun _ ha => isOrthProj_leftProj (hM.Xh_orth ha)

private theorem orthR {V : α → Matrix W r ℝ} (hV : ∀ᶠ a in l, (V a).transpose * M.Wv * V a = 1) :
    ∀ᶠ a in l, IsOrthProj (rightProj (M.Vh (V a)) : Matrix I W ℝ →L[ℝ] Matrix I W ℝ) :=
  hV.mono fun _ ha => isOrthProj_rightProj (hM.Vh_orth ha)

private theorem orthG {X : α → Matrix I r ℝ} {V : α → Matrix W r ℝ}
    (hX : ∀ᶠ a in l, (X a).transpose * M.Wx * X a = 1)
    (hV : ∀ᶠ a in l, (V a).transpose * M.Wv * V a = 1) :
    ∀ᶠ a in l, IsOrthProj (M.Gal (X a) (V a)) := by
  filter_upwards [hX, hV] with a h1 h2
  exact isOrthProj_leftProj_mul_rightProj (hM.Xh_orth h1) (hM.Vh_orth h2)

variable {c : ℝ} (hε : Tendsto ε l (𝓝[>] 0)) (hc : 0 < c)
include hε hc

/-- The `K`-step, as a relaxation. -/
private theorem relK {X X₁ : α → Matrix I r ℝ} {V : α → Matrix W r ℝ} {S S₁ : α → Matrix r r ℝ}
    {K₁ : α → Matrix I r ℝ} (hV : ∀ᶠ a in l, (V a).transpose * M.Wv * V a = 1)
    (hu : Bd l fun a => M.liftS (X a) (V a) (S a))
    (h : ∀ᶠ a in l, IsIMEX (M.kExp (ε a) (M.flux (ρ a)) (V a)) (M.kImp (ε a)) c (X a * S a) (K₁ a))
    (hK : ∀ᶠ a in l, K₁ a = X₁ a * S₁ a) :
    Relaxes l M.Sg (fun a => rightProj (M.Vh (V a))) (fun a => M.Gh (ρ a))
      (fun a => M.liftS (X₁ a) (V a) (S₁ a)) := by
  refine Relaxes.congr ((hM.subK hV _).relaxes_euler (y := fun a => X a * S a) hε hc (Or.inl rfl)
    (Eventually.of_forall fun _ => hM.Sg_Gh _) hu h) ?_
  filter_upwards [hK] with a ha
  rw [ha, liftK_eq]

/-- The `L`-step, as a relaxation. -/
private theorem relL {X : α → Matrix I r ℝ} {V V₁ : α → Matrix W r ℝ} {S S₁ : α → Matrix r r ℝ}
    {L₁ : α → Matrix W r ℝ} (hX : ∀ᶠ a in l, (X a).transpose * M.Wx * X a = 1)
    (hu : Bd l fun a => M.liftS (X a) (V a) (S a))
    (h : ∀ᶠ a in l, IsIMEX (M.lExp (ε a) (M.flux (ρ a)) (X a)) (M.lImp (ε a) (X a)) c
      (V a * (S a).transpose) (L₁ a))
    (hL : ∀ᶠ a in l, L₁ a = V₁ a * (S₁ a).transpose) :
    Relaxes l M.Sg (fun a => leftProj (M.Xh (X a))) (fun a => M.Gh (ρ a))
      (fun a => M.liftS (X a) (V₁ a) (S₁ a)) := by
  have hu' : Bd l fun a => M.liftL (X a) (V a * (S a).transpose) := by
    simpa only [liftL_eq] using hu
  refine Relaxes.congr ((hM.subL hX _).relaxes_euler (y := fun a => V a * (S a).transpose) hε hc
    (Or.inl rfl) (Eventually.of_forall fun _ => hM.Sg_Gh _) hu' h) ?_
  filter_upwards [hL] with a ha
  rw [ha, liftL_eq]

/-- The `S`-step, as a relaxation. -/
private theorem relS {X : α → Matrix I r ℝ} {V : α → Matrix W r ℝ} {S S₁ : α → Matrix r r ℝ}
    (hX : ∀ᶠ a in l, (X a).transpose * M.Wx * X a = 1)
    (hV : ∀ᶠ a in l, (V a).transpose * M.Wv * V a = 1)
    (hu : Bd l fun a => M.liftS (X a) (V a) (S a))
    (h : ∀ᶠ a in l, IsIMEX (M.sExp (ε a) (M.flux (ρ a)) (X a) (V a)) (M.sImp (ε a) (X a)) c
      (S a) (S₁ a)) :
    Relaxes l M.Sg (fun a => M.Gal (X a) (V a)) (fun a => M.Gh (ρ a))
      (fun a => M.liftS (X a) (V a) (S₁ a)) :=
  (hM.subS hX hV _).relaxes_euler hε hc (Or.inr rfl)
    (Eventually.of_forall fun _ => hM.Sg_Gh _) hu h

variable {X X₁ : α → Matrix I r ℝ} {S S₁ : α → Matrix r r ℝ} {V V₁ : α → Matrix W r ℝ} {dt : ℝ}

omit hc in
/-- The three substeps in an order that starts with `K` or with `S`, `K`: for a family of bases `V`
that nearly contain `ξ, η, γ`, the micro part tends to the limit, and so does the new basis. -/
private theorem micro_kFirst {o : Order} (ho : o = .KLS ∨ o = .KSL ∨ o = .SKL) (hdt : 0 < dt)
    (hGb : Bd l fun a => M.Gh (ρ a))
    (hdef : Tendsto (fun a => ‖M.Gh (ρ a) - rightProj (M.Vh (V a)) (M.Gh (ρ a))‖) l (𝓝 0))
    (hu₀ : Bd l fun a => M.liftS (X a) (V a) (S a))
    (h : ∀ᶠ a in l, M.IsStep o dt (ε a) (ρ a) (X a) (S a) (V a) (ρ₁ a) (X₁ a) (S₁ a) (V₁ a)) :
    MicroConv l M ρ X₁ S₁ V₁ := by
  obtain ⟨σ₀, σ₁, h0, hlow, hup⟩ := hM.bounds
  have hXa := h.mono fun a ha => ha.hX
  have hVa := h.mono fun a ha => ha.hV
  have hX₁a := h.mono fun a ha => ha.hX₁
  have hV₁a := h.mono fun a ha => ha.hV₁
  have hμ := h.mono fun a ha => ha.micro
  rcases ho with rfl | rfl | rfl
  · simp only [Model.IsMicro] at hμ
    obtain ⟨K₁, hμ⟩ := eventually_choose hμ
    obtain ⟨S', hμ⟩ := eventually_choose hμ
    obtain ⟨L₁, hμ⟩ := eventually_choose hμ
    obtain ⟨S'', hμ⟩ := eventually_choose hμ
    have R1 := hM.relK hε hdt hVa hu₀ (hμ.mono fun a ha => ha.1) (hμ.mono fun a ha => ha.2.1)
    have d2 := capture_def (hM.orthL hX₁a) (hX₁a.mono fun a ha => hM.liftS_range_left ha _)
      (R1.tendsto h0 hlow hup (hM.orthR hVa) hGb hdef)
    have R2 := hM.relL hε hdt hX₁a (R1.bd h0 hlow hup (hM.orthR hVa) hGb)
      (hμ.mono fun a ha => ha.2.2.1) (hμ.mono fun a ha => ha.2.2.2.1)
    have d3 := capture_def (hM.orthR hV₁a) (hV₁a.mono fun a ha => hM.liftS_range_right ha _)
      (R2.tendsto h0 hlow hup (hM.orthL hX₁a) hGb d2)
    have R3 := hM.relS hε hdt hX₁a hV₁a (R2.bd h0 hlow hup (hM.orthL hX₁a) hGb)
      (hμ.mono fun a ha => ha.2.2.2.2)
    exact ⟨R3.tendsto h0 hlow hup (hM.orthG hX₁a hV₁a) hGb (mul_def (hM.orthL hX₁a) d2 d3), d3⟩
  · simp only [Model.IsMicro] at hμ
    obtain ⟨K₁, hμ⟩ := eventually_choose hμ
    obtain ⟨S', hμ⟩ := eventually_choose hμ
    obtain ⟨S'', hμ⟩ := eventually_choose hμ
    obtain ⟨L₁, hμ⟩ := eventually_choose hμ
    have R1 := hM.relK hε hdt hVa hu₀ (hμ.mono fun a ha => ha.1) (hμ.mono fun a ha => ha.2.1)
    have d2 := capture_def (hM.orthL hX₁a) (hX₁a.mono fun a ha => hM.liftS_range_left ha _)
      (R1.tendsto h0 hlow hup (hM.orthR hVa) hGb hdef)
    have R2 := hM.relS hε hdt hX₁a hVa (R1.bd h0 hlow hup (hM.orthR hVa) hGb)
      (hμ.mono fun a ha => ha.2.2.1)
    have R3 := hM.relL hε hdt hX₁a (R2.bd h0 hlow hup (hM.orthG hX₁a hVa) hGb)
      (hμ.mono fun a ha => ha.2.2.2.1) (hμ.mono fun a ha => ha.2.2.2.2)
    have t3 := R3.tendsto h0 hlow hup (hM.orthL hX₁a) hGb d2
    exact ⟨t3, capture_def (hM.orthR hV₁a) (hV₁a.mono fun a ha => hM.liftS_range_right ha _) t3⟩
  · simp only [Model.IsMicro] at hμ
    obtain ⟨S', hμ⟩ := eventually_choose hμ
    obtain ⟨K₁, hμ⟩ := eventually_choose hμ
    obtain ⟨S'', hμ⟩ := eventually_choose hμ
    obtain ⟨L₁, hμ⟩ := eventually_choose hμ
    have R1 := hM.relS hε hdt hXa hVa hu₀ (hμ.mono fun a ha => ha.1)
    have R2 := hM.relK hε hdt hVa (R1.bd h0 hlow hup (hM.orthG hXa hVa) hGb)
      (hμ.mono fun a ha => ha.2.1) (hμ.mono fun a ha => ha.2.2.1)
    have d2 := capture_def (hM.orthL hX₁a) (hX₁a.mono fun a ha => hM.liftS_range_left ha _)
      (R2.tendsto h0 hlow hup (hM.orthR hVa) hGb hdef)
    have R3 := hM.relL hε hdt hX₁a (R2.bd h0 hlow hup (hM.orthR hVa) hGb)
      (hμ.mono fun a ha => ha.2.2.2.1) (hμ.mono fun a ha => ha.2.2.2.2)
    have t3 := R3.tendsto h0 hlow hup (hM.orthL hX₁a) hGb d2
    exact ⟨t3, capture_def (hM.orthR hV₁a) (hV₁a.mono fun a ha => hM.liftS_range_right ha _) t3⟩

omit hε hc in
/-- The defect of `V₁` is controlled by the residual of the limit of the `L`-step, when the column
space of `X` sees the gradient. -/
private theorem vdef_le {X : Matrix I r ℝ} {V₁ : Matrix W r ℝ} {u : Matrix I W ℝ} {ρ : J → ℝ}
    {Λ : Matrix ι r ℝ} (hX : X.transpose * M.Wx * X = 1) (hV₁ : V₁.transpose * M.Wv * V₁ = 1)
    (hu : rightProj (M.Vh V₁) u = u) (hΛ : Λ * (X.transpose * M.Wx * M.gradMat ρ) = 1) :
    M.vdef V₁ ≤ ‖Λ‖ * ‖leftProj (M.Xh X) (M.Sg (u - M.Gh ρ))‖ := by
  set Y := M.velh.transpose - M.velh.transpose * M.Vh V₁ * (M.Vh V₁).transpose with hY
  set C := X.transpose * M.Wx * M.gradMat ρ with hC
  set gh := Matrix.diagonal M.sx * M.gradMat ρ with hgh
  have hflux : M.hat (M.flux ρ) = gh * M.velh.transpose := by
    rw [hat_apply, Model.flux, Model.velh, Matrix.transpose_mul, Matrix.diagonal_transpose, hgh]
    simp only [Matrix.mul_assoc]
  have hC' : (M.Xh X).transpose * gh = C := by
    rw [Model.Xh, Matrix.transpose_mul, Matrix.diagonal_transpose, hgh, hC, ← hM.Dx_mul_Dx]
    simp only [Matrix.mul_assoc]
  set r := leftProj (M.Xh X) (M.Sg (u - M.Gh ρ)) with hr
  have hr1 : M.Sg (u - M.Gh ρ) = Matrix.diagonal M.σS * u + gh * M.velh.transpose := by
    rw [map_sub, hM.Sg_Gh, hflux, sub_neg_eq_add, Model.Sg, leftMulCLM_apply]
  have hu' : u * M.Vh V₁ * (M.Vh V₁).transpose = u := by rwa [rightProj_apply] at hu
  have hr2 : r - rightProj (M.Vh V₁) r = M.Xh X * (C * Y) := by
    rw [hr, hr1, leftProj_apply, rightProj_apply, hY, ← hC']
    have h1 : Matrix.diagonal M.σS * u * M.Vh V₁ * (M.Vh V₁).transpose =
        Matrix.diagonal M.σS * u := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc u, hu']
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc] at h1 ⊢
    rw [h1]
    abel
  have hYC : Y = Λ * (C * Y) := by
    rw [← Matrix.mul_assoc, hΛ, Matrix.one_mul]
  have h1 : ‖C * Y‖ = ‖r - rightProj (M.Vh V₁) r‖ := by
    rw [hr2, Frobenius.norm_mul_of_orthonormal (hM.Xh_orth hX)]
  have h2 : ‖r - rightProj (M.Vh V₁) r‖ ≤ ‖r‖ :=
    (isOrthProj_rightProj (hM.Vh_orth hV₁)).norm_sub_le r
  calc M.vdef V₁ = ‖Y‖ := rfl
    _ = ‖Λ * (C * Y)‖ := by rw [← hYC]
    _ ≤ ‖Λ‖ * ‖C * Y‖ := Frobenius.norm_mul_le _ _
    _ ≤ ‖Λ‖ * ‖r‖ := by
      rw [h1]
      exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

omit hε hc in
private theorem tendsto_defect {ρ : α → J → ℝ} {V : α → Matrix W r ℝ} (hB : Bd l fun a => M.Bh (ρ
    a))
    (hv : Tendsto (fun a => M.vdef (V a)) l (𝓝 0)) :
    Tendsto (fun a => ‖M.Gh (ρ a) - rightProj (M.Vh (V a)) (M.Gh (ρ a))‖) l (𝓝 0) := by
  have h1 := tendsto_mul_of_bd hv hB.norm
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
  refine Eventually.of_forall fun a => ?_
  rw [mul_comm]
  exact hM.defect_le _ _

omit hε hc in
/-- Uniform full rank of `Xᵀ ∇ₓ ρ` makes the `L`-step capture `ξ, η, γ`. -/
private theorem tendsto_vdef_of_nondeg {u : α → Matrix I W ℝ}
    (R : Relaxes l M.Sg (fun a => leftProj (M.Xh (X a))) (fun a => M.Gh (ρ a)) u)
    (hub : Bd l u) (hXa : ∀ᶠ a in l, (X a).transpose * M.Wx * X a = 1)
    (hV₁a : ∀ᶠ a in l, (V₁ a).transpose * M.Wv * V₁ a = 1)
    (hu : ∀ᶠ a in l, rightProj (M.Vh (V₁ a)) (u a) = u a)
    (hnd : ∃ C, ∀ᶠ a in l, ∃ Λ : Matrix ι r ℝ,
      Λ * ((X a).transpose * M.Wx * M.gradMat (ρ a)) = 1 ∧ ‖Λ‖ ≤ C) :
    Tendsto (fun a => M.vdef (V₁ a)) l (𝓝 0) := by
  obtain ⟨C, hC⟩ := hnd
  have h1 := (R.tendsto_proj hub (hM.orthL hXa)).const_mul C
  rw [mul_zero] at h1
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
  filter_upwards [hC, hXa, hV₁a, hu] with a ⟨Λ, h2, h3⟩ h4 h5 h6
  exact (hM.vdef_le h4 h5 h6 h2).trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))

omit hc in
/-- The three substeps in an order in which `L` comes before `K`. -/
private theorem micro_lFirst {o : Order} (ho : o = .LKS ∨ o = .LSK ∨ o = .SLK) (hdt : 0 < dt)
    (hGb : Bd l fun a => M.Gh (ρ a)) (hB : Bd l fun a => M.Bh (ρ a))
    (hu₀ : Bd l fun a => M.liftS (X a) (V a) (S a))
    (h : ∀ᶠ a in l, M.IsStep o dt (ε a) (ρ a) (X a) (S a) (V a) (ρ₁ a) (X₁ a) (S₁ a) (V₁ a))
    (hnd : ∃ C, ∀ᶠ a in l, ∃ Λ : Matrix ι r ℝ,
      Λ * ((X a).transpose * M.Wx * M.gradMat (ρ a)) = 1 ∧ ‖Λ‖ ≤ C) :
    MicroConv l M ρ X₁ S₁ V₁ := by
  obtain ⟨σ₀, σ₁, h0, hlow, hup⟩ := hM.bounds
  have hXa := h.mono fun a ha => ha.hX
  have hVa := h.mono fun a ha => ha.hV
  have hX₁a := h.mono fun a ha => ha.hX₁
  have hV₁a := h.mono fun a ha => ha.hV₁
  have hμ := h.mono fun a ha => ha.micro
  rcases ho with rfl | rfl | rfl
  · simp only [Model.IsMicro] at hμ
    obtain ⟨L₁, hμ⟩ := eventually_choose hμ
    obtain ⟨S', hμ⟩ := eventually_choose hμ
    obtain ⟨K₁, hμ⟩ := eventually_choose hμ
    obtain ⟨S'', hμ⟩ := eventually_choose hμ
    have R1 := hM.relL hε hdt hXa hu₀ (hμ.mono fun a ha => ha.1) (hμ.mono fun a ha => ha.2.1)
    have b1 := R1.bd h0 hlow hup (hM.orthL hXa) hGb
    have d1 := hM.tendsto_defect hB (hM.tendsto_vdef_of_nondeg R1 b1 hXa hV₁a
      (hV₁a.mono fun a ha => hM.liftS_range_right ha _) hnd)
    have R2 := hM.relK hε hdt hV₁a b1 (hμ.mono fun a ha => ha.2.2.1)
      (hμ.mono fun a ha => ha.2.2.2.1)
    have d2 := capture_def (hM.orthL hX₁a) (hX₁a.mono fun a ha => hM.liftS_range_left ha _)
      (R2.tendsto h0 hlow hup (hM.orthR hV₁a) hGb d1)
    have R3 := hM.relS hε hdt hX₁a hV₁a (R2.bd h0 hlow hup (hM.orthR hV₁a) hGb)
      (hμ.mono fun a ha => ha.2.2.2.2)
    exact ⟨R3.tendsto h0 hlow hup (hM.orthG hX₁a hV₁a) hGb (mul_def (hM.orthL hX₁a) d2 d1), d1⟩
  · simp only [Model.IsMicro] at hμ
    obtain ⟨L₁, hμ⟩ := eventually_choose hμ
    obtain ⟨S', hμ⟩ := eventually_choose hμ
    obtain ⟨S'', hμ⟩ := eventually_choose hμ
    obtain ⟨K₁, hμ⟩ := eventually_choose hμ
    have R1 := hM.relL hε hdt hXa hu₀ (hμ.mono fun a ha => ha.1) (hμ.mono fun a ha => ha.2.1)
    have b1 := R1.bd h0 hlow hup (hM.orthL hXa) hGb
    have d1 := hM.tendsto_defect hB (hM.tendsto_vdef_of_nondeg R1 b1 hXa hV₁a
      (hV₁a.mono fun a ha => hM.liftS_range_right ha _) hnd)
    have R2 := hM.relS hε hdt hXa hV₁a b1 (hμ.mono fun a ha => ha.2.2.1)
    have R3 := hM.relK hε hdt hV₁a (R2.bd h0 hlow hup (hM.orthG hXa hV₁a) hGb)
      (hμ.mono fun a ha => ha.2.2.2.1) (hμ.mono fun a ha => ha.2.2.2.2)
    exact ⟨R3.tendsto h0 hlow hup (hM.orthR hV₁a) hGb d1, d1⟩
  · simp only [Model.IsMicro] at hμ
    obtain ⟨S', hμ⟩ := eventually_choose hμ
    obtain ⟨L₁, hμ⟩ := eventually_choose hμ
    obtain ⟨S'', hμ⟩ := eventually_choose hμ
    obtain ⟨K₁, hμ⟩ := eventually_choose hμ
    have R1 := hM.relS hε hdt hXa hVa hu₀ (hμ.mono fun a ha => ha.1)
    have R2 := hM.relL hε hdt hXa (R1.bd h0 hlow hup (hM.orthG hXa hVa) hGb)
      (hμ.mono fun a ha => ha.2.1) (hμ.mono fun a ha => ha.2.2.1)
    have b2 := R2.bd h0 hlow hup (hM.orthL hXa) hGb
    have d1 := hM.tendsto_defect hB (hM.tendsto_vdef_of_nondeg R2 b2 hXa hV₁a
      (hV₁a.mono fun a ha => hM.liftS_range_right ha _) hnd)
    have R3 := hM.relK hε hdt hV₁a b2 (hμ.mono fun a ha => ha.2.2.2.1)
      (hμ.mono fun a ha => ha.2.2.2.2)
    exact ⟨R3.tendsto h0 hlow hup (hM.orthR hV₁a) hGb d1, d1⟩

omit hε hc in
/-- From the convergence of the micro part to the macro update. -/
private theorem finish {ρs : J → ℝ} (hρ : Tendsto ρ l (𝓝 ρs))
    (hconv : Tendsto (fun a => ‖M.liftS (X₁ a) (V₁ a) (S₁ a) - M.Gh (ρ a)‖) l (𝓝 0)) :
    Tendsto (fun a => X₁ a * S₁ a * (V₁ a).transpose) l (𝓝 (M.gLim ρs)) := by
  have h1 : Tendsto (fun a => M.Gh (ρ a)) l (𝓝 (M.Gh ρs)) :=
    continuous_Gh.continuousAt.tendsto.comp hρ
  have h2 : Tendsto (fun a => M.liftS (X₁ a) (V₁ a) (S₁ a) - M.Gh (ρ a)) l (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 hconv
  have h3 := h2.add h1
  simp only [sub_add_cancel, zero_add] at h3
  have h4 := (continuous_unhat (M := M)).continuousAt.tendsto.comp h3
  have h5 : M.unhat (M.Gh ρs) = M.gLim ρs := hM.unhat_hat _
  rw [h5] at h4
  refine h4.congr fun a => ?_
  exact hM.unhat_hat (X₁ a * S₁ a * (V₁ a).transpose)

omit hε hc in
private theorem step_finish {ρs : J → ℝ} (hρ : Tendsto ρ l (𝓝 ρs))
    (hconv : Tendsto (fun a => ‖M.liftS (X₁ a) (V₁ a) (S₁ a) - M.Gh (ρ a)‖) l (𝓝 0))
    (hrho : ∀ᶠ a in l, ρ₁ a = ρ a + dt • M.rhoRHS (X₁ a * S₁ a * (V₁ a).transpose) (ρ a)) :
    Tendsto (fun a => X₁ a * S₁ a * (V₁ a).transpose) l (𝓝 (M.gLim ρs)) ∧
      Tendsto ρ₁ l (𝓝 (M.eulerStep dt ρs)) := by
  have h1 : Tendsto (fun a => X₁ a * S₁ a * (V₁ a).transpose) l (𝓝 (M.gLim ρs)) :=
    hM.finish hρ hconv
  refine ⟨h1, ?_⟩
  have h2 := tendsto_rhoRHS (M := M) h1 hρ
  have h3 : Tendsto (fun a => ρ a + dt • M.rhoRHS (X₁ a * S₁ a * (V₁ a).transpose) (ρ a)) l
      (𝓝 (ρs + dt • M.rhoRHS (M.gLim ρs) ρs)) := hρ.add (h2.const_smul dt)
  rw [hM.rhoRHS_gLim] at h3
  exact h3.congr' (hrho.mono fun a ha => ha.symm)

omit hε hc in
private theorem norm_liftS {X : Matrix I r ℝ} {V : Matrix W r ℝ} (hX : X.transpose * M.Wx * X = 1)
    (hV : V.transpose * M.Wv * V = 1) (S : Matrix r r ℝ) : ‖M.liftS X V S‖ = ‖S‖ := by
  have h : M.liftS X V S = M.Xh X * S * (M.Vh V).transpose := by
    rw [liftS_apply, hat_apply, Model.Xh, Model.Vh, Matrix.transpose_mul,
      Matrix.diagonal_transpose]
    simp only [Matrix.mul_assoc]
  rw [h, Frobenius.norm_mul_transpose_of_orthonormal (hM.Vh_orth hV),
    Frobenius.norm_mul_of_orthonormal (hM.Xh_orth hX)]

omit hε hc in
/-- The hypothesis of the proof of Prop. 3.1 gives a left inverse of `∇ₓ ρ / σ^S`. -/
private theorem exists_leftInv {ρ : J → ℝ} (h : M.IndepGrad ρ) : ∃ Λ : Matrix ι I ℝ, Λ * M.Bh ρ = 1
    := by
  let B : Matrix I ι ℝ := Matrix.of fun x m => M.grad m ρ x / M.σS x
  have hB : Function.Injective B.mulVec := by
    rw [Matrix.mulVec_injective_iff]
    exact h
  obtain ⟨g, hg⟩ := B.mulVecLin.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 fun x y hxy => hB (by simpa using hxy))
  have h1 : LinearMap.toMatrix' g * B = 1 := by
    have h2 := congrArg LinearMap.toMatrix' hg
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at h2
    rwa [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at h2
  have h3 : M.Bh ρ = Matrix.diagonal M.sx * B := by
    rw [Model.Bh]
    congr 1
    ext x m
    simp only [Matrix.diagonal_mul, Model.gradMat, Matrix.of_apply, B]
    rw [div_eq_inv_mul]
  refine ⟨LinearMap.toMatrix' g * Matrix.diagonal fun x => (M.sx x)⁻¹, ?_⟩
  have h4 : (Matrix.diagonal fun x => (M.sx x)⁻¹) * (Matrix.diagonal M.sx : Matrix I I ℝ) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg _ (funext fun x => inv_mul_cancel₀ (hM.sx_ne x))
  rw [h3, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Matrix.diagonal M.sx), h4, Matrix.one_mul, h1]

omit hε hc in
/-- If the components of `∇ₓ ρ / σ^S` are independent, then a basis that captures the limit
`-v · ∇ₓ ρ / σ^S` captures `ξ, η, γ`. -/
private theorem tendsto_vdef {ρs : J → ℝ} (hρ : Tendsto ρ l (𝓝 ρs)) (hind : M.IndepGrad ρs)
    (hVa : ∀ᶠ a in l, (V a).transpose * M.Wv * V a = 1)
    (hdef : Tendsto (fun a => ‖M.Gh (ρ a) - rightProj (M.Vh (V a)) (M.Gh (ρ a))‖) l (𝓝 0)) :
    Tendsto (fun a => M.vdef (V a)) l (𝓝 0) := by
  obtain ⟨Λ, hΛ⟩ := hM.exists_leftInv hind
  have h1 : Tendsto (fun a => ‖M.Bh (ρ a) - M.Bh ρs‖) l (𝓝 0) := by
    have h2 : Tendsto (fun a => M.Bh (ρ a) - M.Bh ρs) l (𝓝 0) := by
      have h3 : Tendsto (fun a => M.Bh (ρ a)) l (𝓝 (M.Bh ρs)) :=
        continuous_Bh.continuousAt.tendsto.comp hρ
      simpa using h3.sub_const (M.Bh ρs)
    exact tendsto_zero_iff_norm_tendsto_zero.1 h2
  have h2 := ((h1.mul_const ‖M.velh.transpose‖).add hdef).const_mul ‖Λ‖
  simp only [zero_mul, zero_add, mul_zero] at h2
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h2
  filter_upwards [hVa] with a ha
  set Y := M.velh.transpose - M.velh.transpose * M.Vh (V a) * (M.Vh (V a)).transpose with hY
  have hYb : ‖Y‖ ≤ ‖M.velh.transpose‖ := by
    have h := (isOrthProj_rightProj (hM.Vh_orth ha)).norm_sub_le M.velh.transpose
    rwa [rightProj_apply] at h
  have h3 : Y = Λ * (M.Bh ρs * Y) := by rw [← Matrix.mul_assoc, hΛ, Matrix.one_mul]
  have h4 : M.Gh (ρ a) - rightProj (M.Vh (V a)) (M.Gh (ρ a)) = -(M.Bh (ρ a) * Y) :=
    hM.defect_eq _ _
  have h5 : M.Bh ρs * Y = -((M.Bh (ρ a) - M.Bh ρs) * Y) + M.Bh (ρ a) * Y := by
    rw [Matrix.sub_mul]
    abel
  calc M.vdef (V a) = ‖Λ * (M.Bh ρs * Y)‖ := by rw [← h3]; rfl
    _ ≤ ‖Λ‖ * ‖M.Bh ρs * Y‖ := Frobenius.norm_mul_le _ _
    _ ≤ ‖Λ‖ * (‖M.Bh (ρ a) - M.Bh ρs‖ * ‖M.velh.transpose‖ +
        ‖M.Gh (ρ a) - rightProj (M.Vh (V a)) (M.Gh (ρ a))‖) := by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [h5, h4, norm_neg]
      refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
      rw [norm_neg]
      exact (Frobenius.norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left hYb (norm_nonneg _))

end Admissible

end Model

end Chain

section Main

variable {M : Model I J W ι} {α : Type*} {l : Filter α} {ε : α → ℝ} {dt : ℝ}
  {ρ ρ₁ : α → J → ℝ} {X X₁ : α → Matrix I r ℝ} {S S₁ : α → Matrix r r ℝ}
  {V V₁ : α → Matrix W r ℝ} {ρs : J → ℝ}

/-- `g⁻` and `V⁻` of one step of a `K`-first ordering. -/
private theorem one_step_kFirst (hM : M.Admissible) {o : Order} (ho : o = .KLS ∨ o = .KSL ∨ o =
    .SKL)
    (hε : Tendsto ε l (𝓝[>] 0)) (hdt : 0 < dt) (hρ : Tendsto ρ l (𝓝 ρs))
    (hu₀ : Bd l fun a => M.liftS (X a) (V a) (S a))
    (hv : Tendsto (fun a => M.vdef (V a)) l (𝓝 0))
    (h : ∀ᶠ a in l, M.IsStep o dt (ε a) (ρ a) (X a) (S a) (V a) (ρ₁ a) (X₁ a) (S₁ a) (V₁ a)) :
    Tendsto (fun a => X₁ a * S₁ a * (V₁ a).transpose) l (𝓝 (M.gLim ρs)) ∧
      Tendsto ρ₁ l (𝓝 (M.eulerStep dt ρs)) ∧ Bd l (fun a => M.liftS (X₁ a) (V₁ a) (S₁ a)) ∧
      (M.IndepGrad ρs → Tendsto (fun a => M.vdef (V₁ a)) l (𝓝 0)) := by
  have hGb : Bd l fun a => M.Gh (ρ a) :=
    (Model.continuous_Gh.continuousAt.tendsto.comp hρ).isBigO_one ℝ
  have hB : Bd l fun a => M.Bh (ρ a) :=
    (Model.continuous_Bh.continuousAt.tendsto.comp hρ).isBigO_one ℝ
  have hc := hM.micro_kFirst hε ho hdt hGb (hM.tendsto_defect hB hv) hu₀ h
  obtain ⟨h1, h2⟩ := hM.step_finish hρ hc.conv (h.mono fun a ha => ha.rho)
  exact ⟨h1, h2, bd_of_tendsto hc.conv hGb,
    fun hind => hM.tendsto_vdef hρ hind (h.mono fun a ha => ha.hV₁) hc.defect⟩

/-- **arXiv 2005.06571, Prop. 3.1, one step, and Sec. 3.3 for `K-S-L-ρ`, `S-K-L-ρ`.**

For the orderings `K-L-S`, `K-S-L`, `S-K-L`: if `ρⁿ(ε) → ρ` as `ε → 0`, if `Sⁿ(ε)` stays bounded and
`ξ, η, γ ∈ span {Vⱼⁿ(ε)}`, then for any choice of the factorizations the micro part tends to
`g^{n+1} = -v · ∇ₓ ρ / σ^S` (3.28), and `ρ^{n+1}` to the forward Euler step (3.31) for the diffusion
equation (2.6).

This is a true limit of the scheme (3.15)-(3.20), with `ε` going to zero along any filter, not the
formal substitution `ε = 0` of the paper, and the data may depend on `ε`.  The nodes, the quadrature
and the discretizations of `∇ₓ`, `∇ₓ ·` are arbitrary (`Model`), which covers (3.46), (3.52)-(3.56);
the transport operators are any linear maps, and the spatial variable is discrete: the continuum
`L²(Ω)` of the paper is replaced by a finite set of nodes with weights.  One step needs no
independence of the components of `∇ₓ ρ / σ^S`; `prop_3_1` does. -/
theorem prop_3_1_step (hM : M.Admissible) {o : Order} (ho : o = .KLS ∨ o = .KSL ∨ o = .SKL)
    (hε : Tendsto ε l (𝓝[>] 0)) (hdt : 0 < dt) (hρ : Tendsto ρ l (𝓝 ρs)) (hS : Bd l S)
    (hV : ∀ᶠ a in l, M.VelInSpan (V a))
    (h : ∀ᶠ a in l, M.IsStep o dt (ε a) (ρ a) (X a) (S a) (V a) (ρ₁ a) (X₁ a) (S₁ a) (V₁ a)) :
    Tendsto (fun a => X₁ a * S₁ a * (V₁ a).transpose) l (𝓝 (M.gLim ρs)) ∧
      Tendsto ρ₁ l (𝓝 (M.eulerStep dt ρs)) := by
  have hu₀ : Bd l fun a => M.liftS (X a) (V a) (S a) := by
    refine IsBigO.trans (IsBigO.of_bound 1 ?_) hS
    filter_upwards [h] with a ha
    rw [hM.norm_liftS ha.hX ha.hV, one_mul]
  have hv : Tendsto (fun a => M.vdef (V a)) l (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h, hV] with a h1 h2
    exact (hM.vdef_eq_zero h1.hV h2).symm
  obtain ⟨h1, h2, -, -⟩ := one_step_kFirst hM ho hε hdt hρ hu₀ hv h
  exact ⟨h1, h2⟩

/-- **arXiv 2005.06571, Prop. 3.1** (`o = .KLS`) **and Sec. 3.3** (`o = .KSL`, `.SKL`), all steps.

If `ξ, η, γ ∈ span {Vⱼ⁰}`, `ρ⁰(ε) → ρ₀`, `S⁰(ε)` is bounded and the three components of
`∇ₓ ρ / σ^S` are linearly independent along the limit `(eulerStep dt)^[n] ρ₀`, then for every `n`,
`ρⁿ(ε)` tends to the `n`-th iterate of forward Euler for (2.6), and the micro part `g^{n+1}(ε)` to
`-v · ∇ₓ ρ / σ^S` at the `n`-th iterate.

The linear independence is the "without loss of generality" of the proof of the paper.  It cannot
be dropped, against footnote 2 of the paper: `prop_3_1_false_without_independence`.  At finite `ε`
the inclusion `ξ, η, γ ∈ span {Vⱼⁿ(ε)}` fails in general for `n ≥ 1`, and the proof carries instead
the defect `vdef`, which tends to zero. -/
theorem prop_3_1 (hM : M.Admissible) {o : Order} (ho : o = .KLS ∨ o = .KSL ∨ o = .SKL)
    (hε : Tendsto ε l (𝓝[>] 0)) (hdt : 0 < dt) {ρ : α → ℕ → J → ℝ} {X : α → ℕ → Matrix I r ℝ}
    {S : α → ℕ → Matrix r r ℝ} {V : α → ℕ → Matrix W r ℝ} {ρ₀ : J → ℝ}
    (hrun : ∀ᶠ a in l, ∀ n, M.IsStep o dt (ε a) (ρ a n) (X a n) (S a n) (V a n) (ρ a (n + 1))
      (X a (n + 1)) (S a (n + 1)) (V a (n + 1)))
    (hρ₀ : Tendsto (fun a => ρ a 0) l (𝓝 ρ₀)) (hS₀ : Bd l fun a => S a 0)
    (hV₀ : ∀ᶠ a in l, M.VelInSpan (V a 0))
    (hind : ∀ n, M.IndepGrad ((M.eulerStep dt)^[n] ρ₀)) (n : ℕ) :
    Tendsto (fun a => ρ a n) l (𝓝 ((M.eulerStep dt)^[n] ρ₀)) ∧
      Tendsto (fun a => X a (n + 1) * S a (n + 1) * (V a (n + 1)).transpose) l
        (𝓝 (M.gLim ((M.eulerStep dt)^[n] ρ₀))) := by
  have key : ∀ n, Tendsto (fun a => ρ a n) l (𝓝 ((M.eulerStep dt)^[n] ρ₀)) ∧
      Bd l (fun a => M.liftS (X a n) (V a n) (S a n)) ∧
      Tendsto (fun a => M.vdef (V a n)) l (𝓝 0) := by
    intro n
    induction n with
    | zero =>
      refine ⟨hρ₀, ?_, ?_⟩
      · refine IsBigO.trans (IsBigO.of_bound 1 ?_) hS₀
        filter_upwards [hrun] with a ha
        rw [hM.norm_liftS (ha 0).hX (ha 0).hV, one_mul]
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [hrun, hV₀] with a h1 h2
        exact (hM.vdef_eq_zero (h1 0).hV h2).symm
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      obtain ⟨-, h5, h6, h7⟩ := one_step_kFirst hM ho hε hdt h1 h2 h3
        (hrun.mono fun a ha => ha n)
      refine ⟨?_, h6, h7 (hind n)⟩
      rw [Function.iterate_succ_apply']
      exact h5
  obtain ⟨h1, h2, h3⟩ := key n
  obtain ⟨h4, -, -, -⟩ := one_step_kFirst hM ho hε hdt h1 h2 h3 (hrun.mono fun a ha => ha n)
  exact ⟨h1, h4⟩

/-- **arXiv 2005.06571, Sec. 3.3, the orderings `L-K-S-ρ`, `L-S-K-ρ`, `S-L-K-ρ`, one step**, with a
hypothesis that the paper does not state: `Xᵀ ∇ₓ ρ` must have full column rank, uniformly in `ε`
(it has a left inverse `Λ` with `‖Λ‖ ≤ C`).  This is what makes the claim "the span of the updated
basis `V^{n+1}` will contain `v`" true.  It cannot be dropped: `sec_3_3_false_without_rank`.  In
these orderings, on the other hand, `ξ, η, γ ∈ span {Vⱼⁿ}` is not needed. -/
theorem sec_3_3_step (hM : M.Admissible) {o : Order} (ho : o = .LKS ∨ o = .LSK ∨ o = .SLK)
    (hε : Tendsto ε l (𝓝[>] 0)) (hdt : 0 < dt) (hρ : Tendsto ρ l (𝓝 ρs)) (hS : Bd l S)
    (hnd : ∃ C, ∀ᶠ a in l, ∃ Λ : Matrix ι r ℝ,
      Λ * ((X a).transpose * M.Wx * M.gradMat (ρ a)) = 1 ∧ ‖Λ‖ ≤ C)
    (h : ∀ᶠ a in l, M.IsStep o dt (ε a) (ρ a) (X a) (S a) (V a) (ρ₁ a) (X₁ a) (S₁ a) (V₁ a)) :
    Tendsto (fun a => X₁ a * S₁ a * (V₁ a).transpose) l (𝓝 (M.gLim ρs)) ∧
      Tendsto ρ₁ l (𝓝 (M.eulerStep dt ρs)) := by
  have hGb : Bd l fun a => M.Gh (ρ a) :=
    (Model.continuous_Gh.continuousAt.tendsto.comp hρ).isBigO_one ℝ
  have hB : Bd l fun a => M.Bh (ρ a) :=
    (Model.continuous_Bh.continuousAt.tendsto.comp hρ).isBigO_one ℝ
  have hu₀ : Bd l fun a => M.liftS (X a) (V a) (S a) := by
    refine IsBigO.trans (IsBigO.of_bound 1 ?_) hS
    filter_upwards [h] with a ha
    rw [hM.norm_liftS ha.hX ha.hV, one_mul]
  have hc := hM.micro_lFirst hε ho hdt hGb hB hu₀ h hnd
  exact hM.step_finish hρ hc.conv (h.mono fun a ha => ha.rho)

/-- **arXiv 2005.06571, Sec. 3.3, the orderings `L-K-S-ρ`, `L-S-K-ρ`, `S-L-K-ρ`, all steps**: under
the rank hypothesis of `sec_3_3_step` at every step, the limit is forward Euler for (2.6). -/
theorem sec_3_3 (hM : M.Admissible) {o : Order} (ho : o = .LKS ∨ o = .LSK ∨ o = .SLK)
    (hε : Tendsto ε l (𝓝[>] 0)) (hdt : 0 < dt) {ρ : α → ℕ → J → ℝ} {X : α → ℕ → Matrix I r ℝ}
    {S : α → ℕ → Matrix r r ℝ} {V : α → ℕ → Matrix W r ℝ} {ρ₀ : J → ℝ}
    (hrun : ∀ᶠ a in l, ∀ n, M.IsStep o dt (ε a) (ρ a n) (X a n) (S a n) (V a n) (ρ a (n + 1))
      (X a (n + 1)) (S a (n + 1)) (V a (n + 1)))
    (hρ₀ : Tendsto (fun a => ρ a 0) l (𝓝 ρ₀)) (hS₀ : Bd l fun a => S a 0)
    (hnd : ∀ n, ∃ C, ∀ᶠ a in l, ∃ Λ : Matrix ι r ℝ,
      Λ * ((X a n).transpose * M.Wx * M.gradMat (ρ a n)) = 1 ∧ ‖Λ‖ ≤ C) (n : ℕ) :
    Tendsto (fun a => ρ a n) l (𝓝 ((M.eulerStep dt)^[n] ρ₀)) ∧
      Tendsto (fun a => X a (n + 1) * S a (n + 1) * (V a (n + 1)).transpose) l
        (𝓝 (M.gLim ((M.eulerStep dt)^[n] ρ₀))) := by
  have key : ∀ n, Tendsto (fun a => ρ a n) l (𝓝 ((M.eulerStep dt)^[n] ρ₀)) ∧
      Bd l (fun a => S a n) := by
    intro n
    induction n with
    | zero => exact ⟨hρ₀, hS₀⟩
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      have hstep := hrun.mono fun a ha => ha n
      obtain ⟨h3, h4⟩ := sec_3_3_step hM ho hε hdt h1 h2 (hnd n) hstep
      refine ⟨?_, ?_⟩
      · rw [Function.iterate_succ_apply']
        exact h4
      · have h5 : Bd l fun a => X a (n + 1) * S a (n + 1) * (V a (n + 1)).transpose :=
          h3.isBigO_one ℝ
        have h6 : Bd l fun a => M.liftS (X a (n + 1)) (V a (n + 1)) (S a (n + 1)) :=
          (M.hat.toContinuousLinearMap.isBigO_comp _ _).trans h5
        refine IsBigO.trans (IsBigO.of_bound 1 ?_) h6
        filter_upwards [hrun] with a ha
        rw [hM.norm_liftS (ha (n + 1)).hX (ha (n + 1)).hV, one_mul]
  obtain ⟨h1, h2⟩ := key n
  exact ⟨h1, (sec_3_3_step hM ho hε hdt h1 h2 (hnd n) (hrun.mono fun a ha => ha n)).1⟩

/-- arXiv 2005.06571, Prop. 3.1: the limit micro part has rank at most three, the number of
components of `v`. -/
theorem rank_gLim_le (M : Model I J W ι) (ρ : J → ℝ) : (M.gLim ρ).rank ≤ Fintype.card ι := by
  have h : M.gLim ρ = (-(Matrix.diagonal (fun x => (M.σS x)⁻¹) * M.gradMat ρ)) *
      M.velMat.transpose := by
    rw [Model.gLim, Model.flux, Matrix.neg_mul, Matrix.mul_assoc]
  rw [h]
  refine (Matrix.rank_mul_le_right _ _).trans ?_
  simpa using Matrix.rank_le_card_height M.velMat.transpose

end Main

/-! ### Sec. 3.4: the second order scheme -/

section Second

namespace Model

variable (M : Model I J W ι)

/-- One step of the second order scheme of Sec. 3.4, from `(ρ, X, S, V)` to `(ρ₁, X₁, S₁, V₁)`
through `(ρh, Xh, Sh, Vh)`: step 1 is (3.37); steps 2-7 are half steps of the ARS(2,2,2) scheme for
`K`, `L`, `S`, `S`, `L`, `K` with `ρh` frozen; step 8 is (3.42).  The paper writes out (3.38) for
the `K`-step only and treats the `L`- and `S`-steps "similarly": here the same tableau is used, with
the terms in `ε⁻² ⟨X σ^S X⟩ₓ` implicit, as in (3.17), (3.19). -/
structure IsStep2 (dt ε : ℝ) (ρ : J → ℝ) (X : Matrix I r ℝ) (S : Matrix r r ℝ)
    (V : Matrix W r ℝ) (ρh : J → ℝ) (Xh : Matrix I r ℝ) (Sh : Matrix r r ℝ) (Vh : Matrix W r ℝ)
    (ρ₁ : J → ℝ) (X₁ : Matrix I r ℝ) (S₁ : Matrix r r ℝ) (V₁ : Matrix W r ℝ) : Prop where
  hX : X.transpose * M.Wx * X = 1
  hV : V.transpose * M.Wv * V = 1
  hXh : Xh.transpose * M.Wx * Xh = 1
  hVh : Vh.transpose * M.Wv * Vh = 1
  hX₁ : X₁.transpose * M.Wx * X₁ = 1
  hV₁ : V₁.transpose * M.Wv * V₁ = 1
  rhoHalf : ρh = ρ + (dt / 2) • M.rhoRHS (X * S * V.transpose) ρ
  micro : ∃ (K₁ : Matrix I r ℝ) (S1 : Matrix r r ℝ) (L₁ : Matrix W r ℝ) (S2 S3 : Matrix r r ℝ)
      (L₂ : Matrix W r ℝ) (S4 : Matrix r r ℝ) (K₂ : Matrix I r ℝ),
    IsARS (M.kExp ε (M.flux ρh) V) (M.kImp ε) (dt / 2) (X * S) K₁ ∧ K₁ = Xh * S1 ∧
    IsARS (M.lExp ε (M.flux ρh) Xh) (M.lImp ε Xh) (dt / 2) (V * S1.transpose) L₁ ∧
    L₁ = Vh * S2.transpose ∧
    IsARS (M.sExp ε (M.flux ρh) Xh Vh) (M.sImp ε Xh) (dt / 2) S2 Sh ∧
    IsARS (M.sExp ε (M.flux ρh) Xh Vh) (M.sImp ε Xh) (dt / 2) Sh S3 ∧
    IsARS (M.lExp ε (M.flux ρh) Xh) (M.lImp ε Xh) (dt / 2) (Vh * S3.transpose) L₂ ∧
    L₂ = V₁ * S4.transpose ∧
    IsARS (M.kExp ε (M.flux ρh) V₁) (M.kImp ε) (dt / 2) (Xh * S4) K₂ ∧ K₂ = X₁ * S₁
  rhoFull : ρ₁ = ρ + dt • M.rhoRHS (Xh * Sh * Vh.transpose) ρh

/-- The limit of the half step (3.37), for a macro-micro state `s = (ρⁿ, gⁿ)`. -/
noncomputable def half (dt : ℝ) (s : (J → ℝ) × Matrix I W ℝ) : J → ℝ :=
  s.1 + (dt / 2) • M.rhoRHS s.2 s.1

/-- The limit of one step of the second order scheme on `s = (ρⁿ, gⁿ)`: `g^{n+1}` is (3.44), and
`ρ^{n+1}` is (3.42) with (3.43). -/
noncomputable def next (dt : ℝ) (s : (J → ℝ) × Matrix I W ℝ) : (J → ℝ) × Matrix I W ℝ :=
  (s.1 + dt • M.diffRHS (M.half dt s) (M.half dt s), M.gLim (M.half dt s))

variable {M}

namespace Admissible

variable (hM : M.Admissible) {α : Type*} {l : Filter α} {ε : α → ℝ} {ρ ρh ρ₁ : α → J → ℝ}
  {X Xh X₁ : α → Matrix I r ℝ} {S Sh S₁ : α → Matrix r r ℝ} {V Vh V₁ : α → Matrix W r ℝ}
  {c dt : ℝ}
include hM

/-- The `K`-step of ARS(2,2,2), as a relaxation. -/
private theorem arsK (hε : Tendsto ε l (𝓝[>] 0)) (hc : 0 < c) (hGb : Bd l fun a => M.Gh (ρ a))
    {K₁ : α → Matrix I r ℝ} (hV : ∀ᶠ a in l, (V a).transpose * M.Wv * V a = 1)
    (hu : Bd l fun a => M.liftS (X a) (V a) (S a))
    (h : ∀ᶠ a in l, IsARS (M.kExp (ε a) (M.flux (ρ a)) (V a)) (M.kImp (ε a)) c (X a * S a) (K₁ a))
    (hK : ∀ᶠ a in l, K₁ a = X₁ a * S₁ a) :
    Relaxes l M.Sg (fun a => rightProj (M.Vh (V a))) (fun a => M.Gh (ρ a))
      (fun a => M.liftS (X₁ a) (V a) (S₁ a)) := by
  obtain ⟨σ₀, σ₁, h0, hlow, hup⟩ := hM.bounds
  refine Relaxes.congr ((hM.subK hV _).relaxes_ars (y := fun a => X a * S a) hε hc arsγ_pos
    (Or.inl rfl) (Eventually.of_forall fun _ => hM.Sg_Gh _) h0 hlow hup (hM.orthR hV) hGb hu h) ?_
  filter_upwards [hK] with a ha
  rw [ha, liftK_eq]

/-- The `L`-step of ARS(2,2,2), as a relaxation. -/
private theorem arsL (hε : Tendsto ε l (𝓝[>] 0)) (hc : 0 < c) (hGb : Bd l fun a => M.Gh (ρ a))
    {L₁ : α → Matrix W r ℝ} (hX : ∀ᶠ a in l, (X a).transpose * M.Wx * X a = 1)
    (hu : Bd l fun a => M.liftS (X a) (V a) (S a))
    (h : ∀ᶠ a in l, IsARS (M.lExp (ε a) (M.flux (ρ a)) (X a)) (M.lImp (ε a) (X a)) c
      (V a * (S a).transpose) (L₁ a))
    (hL : ∀ᶠ a in l, L₁ a = V₁ a * (S₁ a).transpose) :
    Relaxes l M.Sg (fun a => leftProj (M.Xh (X a))) (fun a => M.Gh (ρ a))
      (fun a => M.liftS (X a) (V₁ a) (S₁ a)) := by
  obtain ⟨σ₀, σ₁, h0, hlow, hup⟩ := hM.bounds
  have hu' : Bd l fun a => M.liftL (X a) (V a * (S a).transpose) := by
    simpa only [liftL_eq] using hu
  refine Relaxes.congr ((hM.subL hX _).relaxes_ars (y := fun a => V a * (S a).transpose) hε hc
    arsγ_pos (Or.inl rfl) (Eventually.of_forall fun _ => hM.Sg_Gh _) h0 hlow hup (hM.orthL hX) hGb
    hu' h) ?_
  filter_upwards [hL] with a ha
  rw [ha, liftL_eq]

/-- The `S`-step of ARS(2,2,2), as a relaxation. -/
private theorem arsS (hε : Tendsto ε l (𝓝[>] 0)) (hc : 0 < c) (hGb : Bd l fun a => M.Gh (ρ a))
    (hX : ∀ᶠ a in l, (X a).transpose * M.Wx * X a = 1)
    (hV : ∀ᶠ a in l, (V a).transpose * M.Wv * V a = 1)
    (hu : Bd l fun a => M.liftS (X a) (V a) (S a))
    (h : ∀ᶠ a in l, IsARS (M.sExp (ε a) (M.flux (ρ a)) (X a) (V a)) (M.sImp (ε a) (X a)) c
      (S a) (S₁ a)) :
    Relaxes l M.Sg (fun a => M.Gal (X a) (V a)) (fun a => M.Gh (ρ a))
      (fun a => M.liftS (X a) (V a) (S₁ a)) := by
  obtain ⟨σ₀, σ₁, h0, hlow, hup⟩ := hM.bounds
  exact (hM.subS hX hV _).relaxes_ars hε hc arsγ_pos (Or.inr rfl)
    (Eventually.of_forall fun _ => hM.Sg_Gh _) h0 hlow hup (hM.orthG hX hV) hGb hu h

/-- The six substeps of the second order scheme: (3.43) and (3.44), with defects. -/
private theorem micro_two (hε : Tendsto ε l (𝓝[>] 0)) (hdt : 0 < dt)
    (hGb : Bd l fun a => M.Gh (ρh a))
    (hdef : Tendsto (fun a => ‖M.Gh (ρh a) - rightProj (M.Vh (V a)) (M.Gh (ρh a))‖) l (𝓝 0))
    (hu₀ : Bd l fun a => M.liftS (X a) (V a) (S a))
    (h : ∀ᶠ a in l, M.IsStep2 dt (ε a) (ρ a) (X a) (S a) (V a) (ρh a) (Xh a) (Sh a) (Vh a)
      (ρ₁ a) (X₁ a) (S₁ a) (V₁ a)) :
    Tendsto (fun a => ‖M.liftS (Xh a) (Vh a) (Sh a) - M.Gh (ρh a)‖) l (𝓝 0) ∧
      MicroConv l M ρh X₁ S₁ V₁ := by
  obtain ⟨σ₀, σ₁, h0, hlow, hup⟩ := hM.bounds
  have hc : 0 < dt / 2 := by positivity
  have hVa := h.mono fun a ha => ha.hV
  have hXha := h.mono fun a ha => ha.hXh
  have hVha := h.mono fun a ha => ha.hVh
  have hV₁a := h.mono fun a ha => ha.hV₁
  have hμ := h.mono fun a ha => ha.micro
  obtain ⟨K₁, hμ⟩ := eventually_choose hμ
  obtain ⟨S1, hμ⟩ := eventually_choose hμ
  obtain ⟨L₁, hμ⟩ := eventually_choose hμ
  obtain ⟨S2, hμ⟩ := eventually_choose hμ
  obtain ⟨S3, hμ⟩ := eventually_choose hμ
  obtain ⟨L₂, hμ⟩ := eventually_choose hμ
  obtain ⟨S4, hμ⟩ := eventually_choose hμ
  obtain ⟨K₂, hμ⟩ := eventually_choose hμ
  have R1 := hM.arsK hε hc hGb hVa hu₀ (hμ.mono fun a ha => ha.1) (hμ.mono fun a ha => ha.2.1)
  have d1 := capture_def (hM.orthL hXha) (hXha.mono fun a ha => hM.liftS_range_left ha _)
    (R1.tendsto h0 hlow hup (hM.orthR hVa) hGb hdef)
  have R2 := hM.arsL hε hc hGb hXha (R1.bd h0 hlow hup (hM.orthR hVa) hGb)
    (hμ.mono fun a ha => ha.2.2.1) (hμ.mono fun a ha => ha.2.2.2.1)
  have d2 := capture_def (hM.orthR hVha) (hVha.mono fun a ha => hM.liftS_range_right ha _)
    (R2.tendsto h0 hlow hup (hM.orthL hXha) hGb d1)
  have R3 := hM.arsS hε hc hGb hXha hVha (R2.bd h0 hlow hup (hM.orthL hXha) hGb)
    (hμ.mono fun a ha => ha.2.2.2.2.1)
  have d3 := mul_def (hM.orthL hXha) d1 d2
  have t3 := R3.tendsto h0 hlow hup (hM.orthG hXha hVha) hGb d3
  have R4 := hM.arsS hε hc hGb hXha hVha (R3.bd h0 hlow hup (hM.orthG hXha hVha) hGb)
    (hμ.mono fun a ha => ha.2.2.2.2.2.1)
  have R5 := hM.arsL hε hc hGb hXha (R4.bd h0 hlow hup (hM.orthG hXha hVha) hGb)
    (hμ.mono fun a ha => ha.2.2.2.2.2.2.1) (hμ.mono fun a ha => ha.2.2.2.2.2.2.2.1)
  have d5 := capture_def (hM.orthR hV₁a) (hV₁a.mono fun a ha => hM.liftS_range_right ha _)
    (R5.tendsto h0 hlow hup (hM.orthL hXha) hGb d1)
  have R6 := hM.arsK hε hc hGb hV₁a (R5.bd h0 hlow hup (hM.orthL hXha) hGb)
    (hμ.mono fun a ha => ha.2.2.2.2.2.2.2.2.1) (hμ.mono fun a ha => ha.2.2.2.2.2.2.2.2.2)
  exact ⟨t3, R6.tendsto h0 hlow hup (hM.orthR hV₁a) hGb d5, d5⟩

/-- One step of the second order scheme, in the limit. -/
private theorem one_step_two (hε : Tendsto ε l (𝓝[>] 0)) (hdt : 0 < dt)
    {s : (J → ℝ) × Matrix I W ℝ} (hρ : Tendsto ρ l (𝓝 s.1))
    (hg : Tendsto (fun a => X a * S a * (V a).transpose) l (𝓝 s.2))
    (hv : Tendsto (fun a => M.vdef (V a)) l (𝓝 0))
    (h : ∀ᶠ a in l, M.IsStep2 dt (ε a) (ρ a) (X a) (S a) (V a) (ρh a) (Xh a) (Sh a) (Vh a)
      (ρ₁ a) (X₁ a) (S₁ a) (V₁ a)) :
    Tendsto ρh l (𝓝 (M.half dt s)) ∧
      Tendsto (fun a => Xh a * Sh a * (Vh a).transpose) l (𝓝 (M.gLim (M.half dt s))) ∧
      Tendsto ρ₁ l (𝓝 (M.next dt s).1) ∧
      Tendsto (fun a => X₁ a * S₁ a * (V₁ a).transpose) l (𝓝 (M.next dt s).2) ∧
      (M.IndepGrad (M.half dt s) → Tendsto (fun a => M.vdef (V₁ a)) l (𝓝 0)) := by
  have h1 : Tendsto ρh l (𝓝 (M.half dt s)) := by
    have h2 := hρ.add ((tendsto_rhoRHS (M := M) hg hρ).const_smul (dt / 2))
    exact h2.congr' (h.mono fun a ha => ha.rhoHalf.symm)
  have hGb : Bd l fun a => M.Gh (ρh a) :=
    (continuous_Gh.continuousAt.tendsto.comp h1).isBigO_one ℝ
  have hB : Bd l fun a => M.Bh (ρh a) :=
    (continuous_Bh.continuousAt.tendsto.comp h1).isBigO_one ℝ
  have hu₀ : Bd l fun a => M.liftS (X a) (V a) (S a) :=
    (M.hat.toContinuousLinearMap.isBigO_comp _ _).trans (hg.isBigO_one ℝ)
  obtain ⟨t3, hc⟩ := hM.micro_two hε hdt hGb (hM.tendsto_defect hB hv) hu₀ h
  have h2 := hM.finish h1 t3
  have h3 := hM.finish h1 hc.conv
  have h4 : Tendsto ρ₁ l (𝓝 (M.next dt s).1) := by
    have h5 := hρ.add ((tendsto_rhoRHS (M := M) h2 h1).const_smul dt)
    rw [hM.rhoRHS_gLim] at h5
    exact h5.congr' (h.mono fun a ha => ha.rhoFull.symm)
  exact ⟨h1, h2, h4, h3, fun hind => hM.tendsto_vdef h1 hind (h.mono fun a ha => ha.hV₁) hc.defect⟩

end Admissible

end Model

section MainTwo

variable {M : Model I J W ι} {α : Type*} {l : Filter α} {ε : α → ℝ} {dt : ℝ}

/-- **arXiv 2005.06571, Sec. 3.4, (3.43), (3.44).**  For the second order scheme with
`ξ, η, γ ∈ span {Vⱼ⁰}`, as `ε → 0`, the macro variables tend to the limit recursion `M.next`
(see `sec_3_4_recursion` for its form (3.45)), the half step micro part to
`-v · ∇ₓ ρ^{n+1/2} / σ^S` (3.43) and the full step micro part to the same limit (3.44), provided
that the components of `∇ₓ ρ^{n+1/2} / σ^S` are independent along the limit: see `prop_3_1`. -/
theorem sec_3_4 (hM : M.Admissible) (hε : Tendsto ε l (𝓝[>] 0)) (hdt : 0 < dt)
    {ρ ρh : α → ℕ → J → ℝ} {X Xh : α → ℕ → Matrix I r ℝ} {S Sh : α → ℕ → Matrix r r ℝ}
    {V Vh : α → ℕ → Matrix W r ℝ} {s₀ : (J → ℝ) × Matrix I W ℝ}
    (hrun : ∀ᶠ a in l, ∀ n, M.IsStep2 dt (ε a) (ρ a n) (X a n) (S a n) (V a n) (ρh a n) (Xh a n)
      (Sh a n) (Vh a n) (ρ a (n + 1)) (X a (n + 1)) (S a (n + 1)) (V a (n + 1)))
    (hρ₀ : Tendsto (fun a => ρ a 0) l (𝓝 s₀.1))
    (hg₀ : Tendsto (fun a => X a 0 * S a 0 * (V a 0).transpose) l (𝓝 s₀.2))
    (hV₀ : ∀ᶠ a in l, M.VelInSpan (V a 0))
    (hind : ∀ n, M.IndepGrad (M.half dt ((M.next dt)^[n] s₀))) (n : ℕ) :
    Tendsto (fun a => ρ a n) l (𝓝 ((M.next dt)^[n] s₀).1) ∧
      Tendsto (fun a => ρh a n) l (𝓝 (M.half dt ((M.next dt)^[n] s₀))) ∧
      Tendsto (fun a => Xh a n * Sh a n * (Vh a n).transpose) l
        (𝓝 (M.gLim (M.half dt ((M.next dt)^[n] s₀)))) ∧
      Tendsto (fun a => X a (n + 1) * S a (n + 1) * (V a (n + 1)).transpose) l
        (𝓝 (M.gLim (M.half dt ((M.next dt)^[n] s₀)))) := by
  have key : ∀ n, Tendsto (fun a => ρ a n) l (𝓝 ((M.next dt)^[n] s₀).1) ∧
      Tendsto (fun a => X a n * S a n * (V a n).transpose) l (𝓝 ((M.next dt)^[n] s₀).2) ∧
      Tendsto (fun a => M.vdef (V a n)) l (𝓝 0) := by
    intro n
    induction n with
    | zero =>
      refine ⟨hρ₀, hg₀, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [hrun, hV₀] with a h1 h2
      exact (hM.vdef_eq_zero (h1 0).hV h2).symm
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      obtain ⟨-, -, h6, h7, h8⟩ := hM.one_step_two hε hdt h1 h2 h3 (hrun.mono fun a ha => ha n)
      rw [Function.iterate_succ_apply']
      exact ⟨h6, h7, h8 (hind n)⟩
  obtain ⟨h1, h2, h3⟩ := key n
  obtain ⟨h4, h5, -, h7, -⟩ := hM.one_step_two hε hdt h1 h2 h3 (hrun.mono fun a ha => ha n)
  exact ⟨h1, h4, h5, h7⟩

/-- **arXiv 2005.06571, (3.45).**  The limit recursion, after the first step (`n ≥ 1` in the paper),
written with `ρⁿ⁺¹ = ρs (n + 1)`, `ρⁿ⁺¹ᐟ² = ρm n`:
`ρ^{n+1/2} = ρⁿ + (dt/2) (∇ₓ · (∇ₓ ρ^{n-1/2} / (3 σ^S)) - σ^A ρⁿ + G)` and
`ρ^{n+1} = ρⁿ + dt (∇ₓ · (∇ₓ ρ^{n+1/2} / (3 σ^S)) - σ^A ρ^{n+1/2} + G)`. -/
theorem sec_3_4_recursion (hM : M.Admissible) (dt : ℝ) (s₀ : (J → ℝ) × Matrix I W ℝ) (n : ℕ) :
    M.half dt ((M.next dt)^[n + 1] s₀) = ((M.next dt)^[n + 1] s₀).1 +
        (dt / 2) • M.diffRHS (M.half dt ((M.next dt)^[n] s₀)) ((M.next dt)^[n + 1] s₀).1 ∧
      ((M.next dt)^[n + 1] s₀).1 = ((M.next dt)^[n] s₀).1 +
        dt • M.diffRHS (M.half dt ((M.next dt)^[n] s₀)) (M.half dt ((M.next dt)^[n] s₀)) := by
  rw [Function.iterate_succ_apply']
  refine ⟨?_, rfl⟩
  rw [Model.half]
  simp only [Model.next]
  rw [hM.rhoRHS_gLim]

/-- `diffOp` as a linear map. -/
noncomputable def Model.diffOpL (M : Model I J W ι) : (J → ℝ) →ₗ[ℝ] (J → ℝ) where
  toFun := M.diffOp
  map_add' ρ ρ' := by
    have h : ∀ m, (fun x => M.grad m (ρ + ρ') x / M.σS x) =
        (fun x => M.grad m ρ x / M.σS x) + fun x => M.grad m ρ' x / M.σS x := fun m => by
      ext x
      simp only [map_add, Pi.add_apply, add_div]
    ext j
    change 1 / 3 * ∑ m, M.dvg m (fun x => M.grad m (ρ + ρ') x / M.σS x) j =
      1 / 3 * ∑ m, M.dvg m (fun x => M.grad m ρ x / M.σS x) j +
        1 / 3 * ∑ m, M.dvg m (fun x => M.grad m ρ' x / M.σS x) j
    simp_rw [h, map_add, Pi.add_apply]
    rw [Finset.sum_add_distrib, mul_add]
  map_smul' c ρ := by
    have h : ∀ m, (fun x => M.grad m (c • ρ) x / M.σS x) =
        c • fun x => M.grad m ρ x / M.σS x := fun m => by
      ext x
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc]
    ext j
    change 1 / 3 * ∑ m, M.dvg m (fun x => M.grad m (c • ρ) x / M.σS x) j =
      c * (1 / 3 * ∑ m, M.dvg m (fun x => M.grad m ρ x / M.σS x) j)
    simp_rw [h, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    ring

/-- The explicit midpoint rule for (2.6), which is a one-step explicit two-stage Runge-Kutta
scheme. -/
noncomputable def Model.midpointRK (M : Model I J W ι) (dt : ℝ) (ρ : J → ℝ) : J → ℝ :=
  ρ + dt • M.diffRHS (ρ + (dt / 2) • M.diffRHS ρ ρ) (ρ + (dt / 2) • M.diffRHS ρ ρ)

/-- **arXiv 2005.06571, the words after (3.45).**  The paper calls the limit (3.45) "a second-order
explicit RK scheme", but `ρ^{n+1}` depends on `ρ^{n-1/2}`, not only on `ρⁿ`, so it is a two-step
scheme.  With `y = ρⁿ`, `p = ρ^{n-1/2}` and `𝓛 = ∇ₓ · (∇ₓ / (3 σ^S))`, it differs from the
explicit midpoint rule by exactly `(dt² / 2) (𝓛 - σ^A) 𝓛 (p - y)`.  (Informally, since
`p - y = O(dt)` along a smooth solution, this is `O(dt³)`, so second-order consistency should
survive; that estimate is not proved here.) -/
theorem sec_3_4_sub_midpoint (M : Model I J W ι) (dt : ℝ) (y p : J → ℝ) :
    (y + dt • M.diffRHS (y + (dt / 2) • M.diffRHS p y) (y + (dt / 2) • M.diffRHS p y)) -
        M.midpointRK dt y =
      (dt ^ 2 / 2) • fun j => M.diffOp (M.diffOp (p - y)) j - M.σAρ j * M.diffOp (p - y) j := by
  set m := y + (dt / 2) • M.diffRHS p y with hm
  set q := y + (dt / 2) • M.diffRHS y y with hq
  have hdiff : M.diffRHS p y - M.diffRHS y y = M.diffOp (p - y) := by
    have h : M.diffOp (p - y) = M.diffOp p - M.diffOp y := M.diffOpL.map_sub p y
    rw [h]
    ext j
    simp only [Pi.sub_apply, Model.diffRHS]
    ring
  have hmq : m = q + (dt / 2) • M.diffOp (p - y) := by
    rw [hm, hq, ← hdiff, smul_sub]
    abel
  have hL : M.diffOp m = M.diffOp q + (dt / 2) • M.diffOp (M.diffOp (p - y)) := by
    rw [hmq]
    exact (M.diffOpL.map_add _ _).trans (by rw [show M.diffOpL _ = _ from
      M.diffOpL.map_smul (dt / 2) (M.diffOp (p - y))]; rfl)
  ext j
  have h1 := congrFun hL j
  have h2 := congrFun hmq j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  simp only [Model.midpointRK, ← hq, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Model.diffRHS, h1, h2]
  ring

end MainTwo

end Second

end Model

/-! ### Sec. 3.5: the staggered grid -/

section Grid

/-- The periodic index set of cells. -/
abbrev Cell (Nx Ny : ℕ) := ZMod Nx × ZMod Ny

/-- The two staggered families of points of Fig. 1.  As nodes of `g`: `inl (k, l)` is the face
center `(x_{k+1/2}, y_l)` and `inr (k, l)` the face center `(x_k, y_{l+1/2})`.  As nodes of `ρ`:
`inl (k, l)` is the vertex `(x_k, y_l)` and `inr (k, l)` the cell center
`(x_{k+1/2}, y_{l+1/2})`. -/
abbrev Stag (Nx Ny : ℕ) := Cell Nx Ny ⊕ Cell Nx Ny

variable {Nx Ny : ℕ} [NeZero Nx] [NeZero Ny] {W : Type*}

/-- The data of the fully discrete scheme of Sec. 3.5. -/
structure GridData (Nx Ny : ℕ) (W : Type*) where
  /-- Mesh widths. -/
  dx : ℝ
  /-- Mesh widths. -/
  dy : ℝ
  /-- Quadrature weights on `𝕊²`, (3.46). -/
  ωv : W → ℝ
  /-- First component of the velocity. -/
  ξ : W → ℝ
  /-- Second component of the velocity. -/
  η : W → ℝ
  /-- `σ^S` at the nodes of `g`. -/
  σS : Stag Nx Ny → ℝ
  /-- `σ^A` at the nodes of `g`. -/
  σA : Stag Nx Ny → ℝ
  /-- `σ^A` at the nodes of `ρ`. -/
  σAρ : Stag Nx Ny → ℝ
  /-- The source `G` at the nodes of `ρ`. -/
  src : Stag Nx Ny → ℝ
  /-- The upwind transport operator (3.49) of the `K`-step. -/
  TK : Matrix (Stag Nx Ny) W ℝ →ₗ[ℝ] Matrix (Stag Nx Ny) W ℝ
  /-- The transport operator of the `L`-step, (3.54), (3.55). -/
  TL : Matrix (Stag Nx Ny) W ℝ →ₗ[ℝ] Matrix (Stag Nx Ny) W ℝ
  /-- The transport operator of the `S`-step, (3.54), (3.55). -/
  TS : Matrix (Stag Nx Ny) W ℝ →ₗ[ℝ] Matrix (Stag Nx Ny) W ℝ

/-- The positivity and moment assumptions on the scheme of Sec. 3.5, the moments of `ξ, η` being
exact for the Lebedev quadrature. -/
structure GridData.Admissible (D : GridData Nx Ny W) [Fintype W] : Prop where
  dx_pos : 0 < D.dx
  dy_pos : 0 < D.dy
  ωv_pos : ∀ w, 0 < D.ωv w
  σS_pos : ∀ x, 0 < D.σS x
  ξξ : 1 / (4 * Real.pi) * ∑ w, D.ωv w * D.ξ w * D.ξ w = 1 / 3
  ηη : 1 / (4 * Real.pi) * ∑ w, D.ωv w * D.η w * D.η w = 1 / 3
  ξη : 1 / (4 * Real.pi) * ∑ w, D.ωv w * D.ξ w * D.η w = 0

namespace GridData

variable (D : GridData Nx Ny W)

/-- The central difference `D_c^x` of (3.51), (3.54), (3.55), from the nodes of `ρ` to those of
`g`. -/
noncomputable def gradX : (Stag Nx Ny → ℝ) →ₗ[ℝ] (Stag Nx Ny → ℝ) where
  toFun ρ := Sum.elim (fun c => (ρ (.inl (c.1 + 1, c.2)) - ρ (.inl c)) / D.dx)
    (fun c => (ρ (.inr c) - ρ (.inr (c.1 - 1, c.2))) / D.dx)
  map_add' ρ ρ' := by
    ext (c | c) <;> simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr] <;> ring
  map_smul' a ρ := by
    ext (c | c) <;>
      simp only [Pi.smul_apply, Sum.elim_inl, Sum.elim_inr, RingHom.id_apply, smul_eq_mul] <;> ring

/-- The central difference `D_c^y`, from the nodes of `ρ` to those of `g`. -/
noncomputable def gradY : (Stag Nx Ny → ℝ) →ₗ[ℝ] (Stag Nx Ny → ℝ) where
  toFun ρ := Sum.elim (fun c => (ρ (.inr c) - ρ (.inr (c.1, c.2 - 1))) / D.dy)
    (fun c => (ρ (.inl (c.1, c.2 + 1)) - ρ (.inl c)) / D.dy)
  map_add' ρ ρ' := by
    ext (c | c) <;> simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr] <;> ring
  map_smul' a ρ := by
    ext (c | c) <;>
      simp only [Pi.smul_apply, Sum.elim_inl, Sum.elim_inr, RingHom.id_apply, smul_eq_mul] <;> ring

/-- The difference in `x` of (3.56), from the nodes of `g` to those of `ρ`. -/
noncomputable def divX : (Stag Nx Ny → ℝ) →ₗ[ℝ] (Stag Nx Ny → ℝ) where
  toFun f := Sum.elim (fun c => (f (.inl c) - f (.inl (c.1 - 1, c.2))) / D.dx)
    (fun c => (f (.inr (c.1 + 1, c.2)) - f (.inr c)) / D.dx)
  map_add' ρ ρ' := by
    ext (c | c) <;> simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr] <;> ring
  map_smul' a ρ := by
    ext (c | c) <;>
      simp only [Pi.smul_apply, Sum.elim_inl, Sum.elim_inr, RingHom.id_apply, smul_eq_mul] <;> ring

/-- The difference in `y` of (3.56), from the nodes of `g` to those of `ρ`. -/
noncomputable def divY : (Stag Nx Ny → ℝ) →ₗ[ℝ] (Stag Nx Ny → ℝ) where
  toFun f := Sum.elim (fun c => (f (.inr c) - f (.inr (c.1, c.2 - 1))) / D.dy)
    (fun c => (f (.inl (c.1, c.2 + 1)) - f (.inl c)) / D.dy)
  map_add' ρ ρ' := by
    ext (c | c) <;> simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr] <;> ring
  map_smul' a ρ := by
    ext (c | c) <;>
      simp only [Pi.smul_apply, Sum.elim_inl, Sum.elim_inr, RingHom.id_apply, smul_eq_mul] <;> ring

/-- The scheme of Sec. 3.5, as a `Model`: the spatial inner product is (3.53).  The third component
`γ` of the velocity plays no role, since the problem is homogeneous in `z`. -/
noncomputable def model : Model (Stag Nx Ny) (Stag Nx Ny) W (Fin 2) where
  ωx := fun _ => D.dx * D.dy / 2
  ωv := D.ωv
  vel := ![D.ξ, D.η]
  σS := D.σS
  σA := D.σA
  σAρ := D.σAρ
  src := D.src
  grad := ![D.gradX, D.gradY]
  dvg := ![D.divX, D.divY]
  TK := D.TK
  TL := D.TL
  TS := D.TS

variable {D}

private theorem Admissible.model [Fintype W] (hD : D.Admissible) : D.model.Admissible where
  ωx_pos _ := by
    have h1 := hD.dx_pos
    have h2 := hD.dy_pos
    change 0 < D.dx * D.dy / 2
    positivity
  ωv_pos := hD.ωv_pos
  σS_pos := hD.σS_pos
  iso m n := by
    change 1 / (4 * Real.pi) * ∑ w, D.ωv w * (![D.ξ, D.η] m w) * (![D.ξ, D.η] n w) = _
    fin_cases m <;> fin_cases n
    · simpa using hD.ξξ
    · simpa using hD.ξη
    · have h := hD.ξη
      simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta,
        Matrix.cons_val_zero, Fin.isValue, one_ne_zero, ite_false]
      rw [← h]
      congr 1
      exact Finset.sum_congr rfl fun w _ => by ring
    · simpa using hD.ηη

end GridData

section Limit

variable [Fintype W] [DecidableEq W] {D : GridData Nx Ny W}

/-- arXiv 2005.06571, (3.57), at the face centers `(x_{k+1/2}, y_l)`. -/
theorem gLim_inl (hD : D.Admissible) (ρ : Stag Nx Ny → ℝ) (k : ZMod Nx) (l : ZMod Ny) (w : W) :
    D.model.gLim ρ (.inl (k, l)) w = -(1 / D.σS (.inl (k, l)) *
      (D.ξ w * ((ρ (.inl (k + 1, l)) - ρ (.inl (k, l))) / D.dx) +
        D.η w * ((ρ (.inr (k, l)) - ρ (.inr (k, l - 1))) / D.dy))) := by
  rw [hD.model.gLim_apply, Fin.sum_univ_two]
  simp only [GridData.model, Matrix.cons_val_zero, Matrix.cons_val_one, GridData.gradX,
    GridData.gradY, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, one_div]
  ring

/-- arXiv 2005.06571, (3.57), at the face centers `(x_k, y_{l+1/2})`. -/
theorem gLim_inr (hD : D.Admissible) (ρ : Stag Nx Ny → ℝ) (k : ZMod Nx) (l : ZMod Ny) (w : W) :
    D.model.gLim ρ (.inr (k, l)) w = -(1 / D.σS (.inr (k, l)) *
      (D.ξ w * ((ρ (.inr (k, l)) - ρ (.inr (k - 1, l))) / D.dx) +
        D.η w * ((ρ (.inl (k, l + 1)) - ρ (.inl (k, l))) / D.dy))) := by
  rw [hD.model.gLim_apply, Fin.sum_univ_two]
  simp only [GridData.model, Matrix.cons_val_zero, Matrix.cons_val_one, GridData.gradX,
    GridData.gradY, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inr, one_div]
  ring

/-- arXiv 2005.06571, Sec. 3.5.3: the five-point stencil of (3.58), at the vertices. -/
theorem diffOp_inl (ρ : Stag Nx Ny → ℝ) (k : ZMod Nx) (l : ZMod Ny) :
    D.model.diffOp ρ (.inl (k, l)) =
      1 / 3 * (1 / D.dx ^ 2) * ((ρ (.inl (k + 1, l)) - ρ (.inl (k, l))) / D.σS (.inl (k, l)) -
          (ρ (.inl (k, l)) - ρ (.inl (k - 1, l))) / D.σS (.inl (k - 1, l))) +
        1 / 3 * (1 / D.dy ^ 2) * ((ρ (.inl (k, l + 1)) - ρ (.inl (k, l))) / D.σS (.inr (k, l)) -
          (ρ (.inl (k, l)) - ρ (.inl (k, l - 1))) / D.σS (.inr (k, l - 1))) := by
  simp only [Model.diffOp, Fin.sum_univ_two, GridData.model, Matrix.cons_val_zero,
    Matrix.cons_val_one, GridData.gradX, GridData.gradY, GridData.divX, GridData.divY,
    LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr, sub_add_cancel]
  ring

/-- arXiv 2005.06571, Sec. 3.5.3: the five-point stencil, at the cell centers. -/
theorem diffOp_inr (ρ : Stag Nx Ny → ℝ) (k : ZMod Nx) (l : ZMod Ny) :
    D.model.diffOp ρ (.inr (k, l)) =
      1 / 3 * (1 / D.dx ^ 2) * ((ρ (.inr (k + 1, l)) - ρ (.inr (k, l))) / D.σS (.inr (k + 1, l)) -
          (ρ (.inr (k, l)) - ρ (.inr (k - 1, l))) / D.σS (.inr (k, l))) +
        1 / 3 * (1 / D.dy ^ 2) * ((ρ (.inr (k, l + 1)) - ρ (.inr (k, l))) / D.σS (.inl (k, l + 1)) -
          (ρ (.inr (k, l)) - ρ (.inr (k, l - 1))) / D.σS (.inl (k, l))) := by
  simp only [Model.diffOp, Fin.sum_univ_two, GridData.model, Matrix.cons_val_zero,
    Matrix.cons_val_one, GridData.gradX, GridData.gradY, GridData.divX, GridData.divY,
    LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr, add_sub_cancel_right]
  ring

variable {r : Type*} [Fintype r] [DecidableEq r] {α : Type*} {l : Filter α} {ε : α → ℝ} {dt : ℝ}
  {ρ ρ₁ : α → Stag Nx Ny → ℝ} {X X₁ : α → Matrix (Stag Nx Ny) r ℝ} {S S₁ : α → Matrix r r ℝ}
  {V V₁ : α → Matrix W r ℝ} {ρs : Stag Nx Ny → ℝ}

/-- **arXiv 2005.06571, Sec. 3.5.3, (3.57), (3.58).**  The fully discrete first order scheme on the
staggered grid, as `ε → 0`: the micro part tends to the values (3.57), and `ρ^{n+1}` to the explicit
five-point scheme (3.58) for (2.6), at the vertices and, as the paper says "similarly", at the cell
centers.  The transport operators of the `K`-, `L`- and `S`-steps are arbitrary linear maps, which
covers (3.49), (3.52) and (3.54), (3.55). -/
theorem sec_3_5_3 (hD : D.Admissible) (hε : Tendsto ε l (𝓝[>] 0)) (hdt : 0 < dt)
    (hρ : Tendsto ρ l (𝓝 ρs)) (hS : Bd l S) (hV : ∀ᶠ a in l, D.model.VelInSpan (V a))
    (h : ∀ᶠ a in l, D.model.IsStep .KLS dt (ε a) (ρ a) (X a) (S a) (V a) (ρ₁ a) (X₁ a) (S₁ a)
      (V₁ a)) (k : ZMod Nx) (j : ZMod Ny) (w : W) :
    Tendsto (fun a => (X₁ a * S₁ a * (V₁ a).transpose) (.inl (k, j)) w) l
        (𝓝 (-(1 / D.σS (.inl (k, j)) *
          (D.ξ w * ((ρs (.inl (k + 1, j)) - ρs (.inl (k, j))) / D.dx) +
            D.η w * ((ρs (.inr (k, j)) - ρs (.inr (k, j - 1))) / D.dy))))) ∧
      Tendsto (fun a => (X₁ a * S₁ a * (V₁ a).transpose) (.inr (k, j)) w) l
        (𝓝 (-(1 / D.σS (.inr (k, j)) *
          (D.ξ w * ((ρs (.inr (k, j)) - ρs (.inr (k - 1, j))) / D.dx) +
            D.η w * ((ρs (.inl (k, j + 1)) - ρs (.inl (k, j))) / D.dy))))) ∧
      Tendsto (fun a => ρ₁ a (.inl (k, j))) l (𝓝 (ρs (.inl (k, j)) + dt * (
        1 / 3 * (1 / D.dx ^ 2) * ((ρs (.inl (k + 1, j)) - ρs (.inl (k, j))) / D.σS (.inl (k, j)) -
          (ρs (.inl (k, j)) - ρs (.inl (k - 1, j))) / D.σS (.inl (k - 1, j))) +
        1 / 3 * (1 / D.dy ^ 2) * ((ρs (.inl (k, j + 1)) - ρs (.inl (k, j))) / D.σS (.inr (k, j)) -
          (ρs (.inl (k, j)) - ρs (.inl (k, j - 1))) / D.σS (.inr (k, j - 1))) -
        D.σAρ (.inl (k, j)) * ρs (.inl (k, j)) + D.src (.inl (k, j))))) ∧
      Tendsto (fun a => ρ₁ a (.inr (k, j))) l (𝓝 (ρs (.inr (k, j)) + dt * (
        1 / 3 * (1 / D.dx ^ 2) * ((ρs (.inr (k + 1, j)) - ρs (.inr (k, j))) /
            D.σS (.inr (k + 1, j)) -
          (ρs (.inr (k, j)) - ρs (.inr (k - 1, j))) / D.σS (.inr (k, j))) +
        1 / 3 * (1 / D.dy ^ 2) * ((ρs (.inr (k, j + 1)) - ρs (.inr (k, j))) /
            D.σS (.inl (k, j + 1)) -
          (ρs (.inr (k, j)) - ρs (.inr (k, j - 1))) / D.σS (.inl (k, j))) -
        D.σAρ (.inr (k, j)) * ρs (.inr (k, j)) + D.src (.inr (k, j))))) := by
  obtain ⟨h1, h2⟩ := prop_3_1_step hD.model (Or.inl rfl) hε hdt hρ hS hV h
  have hg : ∀ x w, Tendsto (fun a => (X₁ a * S₁ a * (V₁ a).transpose) x w) l
      (𝓝 (D.model.gLim ρs x w)) := fun x w =>
    tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h1 x) w
  have hr := tendsto_pi_nhds.1 h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← gLim_inl hD]
    exact hg _ _
  · rw [← gLim_inr hD]
    exact hg _ _
  · have h3 := hr (.inl (k, j))
    have h4 : D.model.eulerStep dt ρs (.inl (k, j)) = ρs (.inl (k, j)) + dt * (
        D.model.diffOp ρs (.inl (k, j)) - D.σAρ (.inl (k, j)) * ρs (.inl (k, j)) +
          D.src (.inl (k, j))) := rfl
    rwa [h4, diffOp_inl] at h3
  · have h3 := hr (.inr (k, j))
    have h4 : D.model.eulerStep dt ρs (.inr (k, j)) = ρs (.inr (k, j)) + dt * (
        D.model.diffOp ρs (.inr (k, j)) - D.σAρ (.inr (k, j)) * ρs (.inr (k, j)) +
          D.src (.inr (k, j))) := rfl
    rwa [h4, diffOp_inr] at h3

end Limit

end Grid

/-! ### Counterexamples -/

section Zero

variable {I J W ι r : Type*} [Fintype I] [Fintype J] [Fintype W] [Fintype ι] [Fintype r]
  [DecidableEq I] [DecidableEq W] [DecidableEq r] [DecidableEq ι]

namespace Model

variable (M : Model I J W ι) {ε dt : ℝ} {Φ : Matrix I W ℝ}

private theorem imex_k_zero {V : Matrix W r ℝ} (h : Φ * M.Wv * V = 0) :
    IsIMEX (M.kExp ε Φ V) (M.kImp ε) dt (0 : Matrix I r ℝ) 0 := by
  simp [IsIMEX, kExp, kImp, h]

private theorem imex_l_zero {X : Matrix I r ℝ} (h : Φ.transpose * M.Wx * X = 0) :
    IsIMEX (M.lExp ε Φ X) (M.lImp ε X) dt (0 : Matrix W r ℝ) 0 := by
  simp [IsIMEX, lExp, lImp, h]

private theorem imex_s_zero {X : Matrix I r ℝ} {V : Matrix W r ℝ}
    (h : X.transpose * M.Wx * Φ * M.Wv * V = 0) :
    IsIMEX (M.sExp ε Φ X V) (M.sImp ε X) dt (0 : Matrix r r ℝ) 0 := by
  simp [IsIMEX, sExp, sImp, h]

private theorem s_zero_of_k {X : Matrix I r ℝ} {V : Matrix W r ℝ} (h : Φ * M.Wv * V = 0) :
    X.transpose * M.Wx * Φ * M.Wv * V = 0 := by
  have h1 : X.transpose * M.Wx * Φ * M.Wv * V = X.transpose * M.Wx * (Φ * M.Wv * V) := by
    simp only [Matrix.mul_assoc]
  rw [h1, h, Matrix.mul_zero]

private theorem s_zero_of_l {X : Matrix I r ℝ} {V : Matrix W r ℝ} (h : Φ.transpose * M.Wx * X = 0) :
    X.transpose * M.Wx * Φ * M.Wv * V = 0 := by
  have h1 : X.transpose * M.Wx * Φ = (Φ.transpose * M.Wx * X).transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Model.Wx,
      Matrix.diagonal_transpose, Matrix.mul_assoc]
  rw [h1, h, Matrix.transpose_zero, Matrix.zero_mul, Matrix.zero_mul]

private theorem micro_KLS_zero {X X₁ : Matrix I r ℝ} {V V₁ : Matrix W r ℝ} (hK : Φ * M.Wv * V = 0)
    (hL : Φ.transpose * M.Wx * X₁ = 0) :
    M.IsMicro .KLS dt ε Φ X 0 V X₁ 0 V₁ := by
  refine ⟨0, 0, 0, 0, ?_, by simp, ?_, by simp, M.imex_s_zero (M.s_zero_of_l hL)⟩
  · simpa using M.imex_k_zero (dt := dt) (ε := ε) hK
  · simpa using M.imex_l_zero (dt := dt) (ε := ε) hL

private theorem micro_LKS_zero {X X₁ : Matrix I r ℝ} {V V₁ : Matrix W r ℝ} (hK : Φ * M.Wv * V₁ = 0)
    (hL : Φ.transpose * M.Wx * X = 0) :
    M.IsMicro .LKS dt ε Φ X 0 V X₁ 0 V₁ := by
  refine ⟨0, 0, 0, 0, ?_, by simp, ?_, by simp, M.imex_s_zero (M.s_zero_of_k hK)⟩
  · simpa using M.imex_l_zero (dt := dt) (ε := ε) hL
  · simpa using M.imex_k_zero (dt := dt) (ε := ε) hK

private theorem micro_LSK_zero {X X₁ : Matrix I r ℝ} {V V₁ : Matrix W r ℝ} (hK : Φ * M.Wv * V₁ = 0)
    (hL : Φ.transpose * M.Wx * X = 0) :
    M.IsMicro .LSK dt ε Φ X 0 V X₁ 0 V₁ := by
  refine ⟨0, 0, 0, 0, ?_, by simp, M.imex_s_zero (M.s_zero_of_k hK), ?_, by simp⟩
  · simpa using M.imex_l_zero (dt := dt) (ε := ε) hL
  · simpa using M.imex_k_zero (dt := dt) (ε := ε) hK

private theorem micro_SLK_zero {X X₁ : Matrix I r ℝ} {V V₁ : Matrix W r ℝ} (hK : Φ * M.Wv * V₁ = 0)
    (hL : Φ.transpose * M.Wx * X = 0) :
    M.IsMicro .SLK dt ε Φ X 0 V X₁ 0 V₁ := by
  refine ⟨0, 0, 0, 0, M.imex_s_zero (M.s_zero_of_l hL), ?_, by simp, ?_, by simp⟩
  · simpa using M.imex_l_zero (dt := dt) (ε := ε) hL
  · simpa using M.imex_k_zero (dt := dt) (ε := ε) hK

private theorem rhoRHS_zero (ρ : J → ℝ) : M.rhoRHS 0 ρ = fun j => -M.σAρ j * ρ j + M.src j := by
  have h : M.divFlux 0 = 0 := M.divFluxL.map_zero
  ext j
  simp [rhoRHS, h]

end Model

end Zero

section Oct

/-- The nodes `±e₁, ±e₂, ±e₃` of the six-point quadrature on `𝕊²`. -/
abbrev Oct := Fin 3 × Bool

/-- The components of the velocity at the nodes of `Oct`. -/
def octVel (m : Fin 3) (w : Oct) : ℝ := if m = w.1 then (if w.2 then 1 else -1) else 0

/-- The periodic forward difference. -/
def fwd : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun ρ x := ρ (x + 1) - ρ x
  map_add' ρ ρ' := by
    ext x
    simp only [Pi.add_apply]
    ring
  map_smul' a ρ := by
    ext x
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- The periodic backward difference. -/
def bwd : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun ρ x := ρ x - ρ (x - 1)
  map_add' ρ ρ' := by
    ext x
    simp only [Pi.add_apply]
    ring
  map_smul' a ρ := by
    ext x
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- A checkerboard. -/
def chk : Fin 4 → ℝ := ![0, 1, 0, 1]

/-- The model of the counterexamples: a periodic grid of four points in `x`, homogeneous in `y` and
`z`, the six-point quadrature, which is exact for `(4π)⁻¹ ⟨v ⊗ v⟩ᵥ = I / 3`, `σ^S = 1`, `σ^A = 0`,
a checkerboard source, and any transport operators. -/
noncomputable def octModel (TK TL TS : Matrix (Fin 4) Oct ℝ →ₗ[ℝ] Matrix (Fin 4) Oct ℝ) :
    Model (Fin 4) (Fin 4) Oct (Fin 3) where
  ωx := fun _ => 1 / 4
  ωv := fun _ => 2 * Real.pi / 3
  vel := octVel
  σS := fun _ => 1
  σA := fun _ => 0
  σAρ := fun _ => 0
  src := chk
  grad := fun m => if m = 0 then fwd else 0
  dvg := fun m => if m = 0 then bwd else 0
  TK := TK
  TL := TL
  TS := TS

/-- The normalization constant of the velocity basis. -/
noncomputable def octC : ℝ := √(3 / (4 * Real.pi))

private theorem octC_mul : octC * octC * (2 * Real.pi / 3) * 2 = 1 := by
  have h : octC * octC = 3 / (4 * Real.pi) := Real.mul_self_sqrt (by positivity)
  rw [h]
  field_simp
  norm_num

private theorem octC_ne : octC ≠ 0 := by
  intro h
  have := octC_mul
  rw [h] at this
  simp at this

/-- The velocity basis containing `ξ, η, γ`. -/
noncomputable def V0 : Matrix Oct (Fin 3) ℝ := Matrix.of fun w m => octC * octVel m w

/-- A velocity basis orthogonal to `ξ, η, γ`. -/
noncomputable def Vz : Matrix Oct (Fin 3) ℝ := Matrix.of fun w m => if m = w.1 then octC else 0

/-- A spatial basis orthogonal to the gradient of the checkerboard. -/
def Xo : Matrix (Fin 4) (Fin 3) ℝ := !![1, 1, 1; 1, 1, -1; 1, -1, -1; 1, -1, 1]

variable (TK TL TS : Matrix (Fin 4) Oct ℝ →ₗ[ℝ] Matrix (Fin 4) Oct ℝ)

private theorem mul_diag_mul {n k : Type*} [Fintype n] [Fintype k] [DecidableEq n] (A : Matrix n k
    ℝ)
    (d : n → ℝ) (i j : k) :
    (A.transpose * Matrix.diagonal d * A) i j = ∑ x, A x i * d x * A x j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

private theorem sum_oct (f : Oct → ℝ) : ∑ w, f w = ∑ j : Fin 3, (f (j, true) + f (j, false)) := by
  rw [Fintype.sum_prod_type]
  simp

private theorem octModel_admissible : (octModel TK TL TS).Admissible where
  ωx_pos _ := by norm_num [octModel]
  ωv_pos _ := by
    change 0 < 2 * Real.pi / 3
    positivity
  σS_pos _ := by norm_num [octModel]
  iso m n := by
    change 1 / (4 * Real.pi) * ∑ w : Oct, 2 * Real.pi / 3 * octVel m w * octVel n w = _
    rw [sum_oct]
    fin_cases m <;> fin_cases n <;>
      simp [octVel, Fin.sum_univ_three] <;> field_simp <;> norm_num

private theorem V0_orth : V0.transpose * (octModel TK TL TS).Wv * V0 = 1 := by
  have h := octC_mul
  ext i j
  rw [Model.Wv, mul_diag_mul, Matrix.one_apply]
  change ∑ w : Oct, octC * octVel i w * (2 * Real.pi / 3) * (octC * octVel j w) = _
  rw [sum_oct]
  fin_cases i <;> fin_cases j <;> simp [octVel, Fin.sum_univ_three] <;> nlinarith

private theorem Vz_orth : Vz.transpose * (octModel TK TL TS).Wv * Vz = 1 := by
  have h := octC_mul
  ext i j
  rw [Model.Wv, mul_diag_mul, Matrix.one_apply]
  change ∑ w : Oct, (if i = w.1 then octC else 0) * (2 * Real.pi / 3) *
    (if j = w.1 then octC else 0) = _
  rw [sum_oct]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three] <;> nlinarith

private theorem Xo_orth : Xo.transpose * (octModel TK TL TS).Wx * Xo = 1 := by
  ext i j
  rw [Model.Wx, mul_diag_mul]
  change ∑ x : Fin 4, Xo x i * (1 / 4) * Xo x j = _
  fin_cases i <;> fin_cases j <;> simp [Xo, Fin.sum_univ_four] <;> norm_num

private theorem mul_diag_mul' {n k k' : Type*} [Fintype n] [Fintype k] [DecidableEq n]
    (A : Matrix n k ℝ) (B : Matrix n k' ℝ) (d : n → ℝ) (i : k) (j : k') :
    (A.transpose * Matrix.diagonal d * B) i j = ∑ x, A x i * d x * B x j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

private theorem fwd_chk : fwd chk = ![1, -1, 1, -1] := by
  ext x
  fin_cases x <;> simp [fwd, chk]

/-- `(flux chk) ⊥ V`: the columns of `Vz` are orthogonal to `ξ, η, γ`. -/
private theorem flux_Vz (ρ : Fin 4 → ℝ) :
    (octModel TK TL TS).flux ρ * (octModel TK TL TS).Wv * Vz = 0 := by
  have h : (octModel TK TL TS).velMat.transpose * (octModel TK TL TS).Wv * Vz = 0 := by
    ext i j
    rw [Model.Wv, mul_diag_mul', Matrix.zero_apply]
    change ∑ w : Oct, octVel i w * (2 * Real.pi / 3) * (if j = w.1 then octC else 0) = 0
    rw [sum_oct]
    refine Finset.sum_eq_zero fun m _ => ?_
    have key : octVel i (m, true) + octVel i (m, false) = 0 := by
      by_cases h : i = m <;> simp [octVel, h]
    linear_combination (2 * Real.pi / 3 * (if j = m then octC else 0)) * key
  rw [Model.flux, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ Vz, h,
    Matrix.mul_zero]

private theorem flux_smul (M : Model (Fin 4) (Fin 4) Oct (Fin 3)) (t : ℝ) (ρ : Fin 4 → ℝ) :
    M.flux (t • ρ) = t • M.flux ρ := by
  have h : M.gradMat (t • ρ) = t • M.gradMat ρ := M.gradL.map_smul t ρ
  rw [Model.flux, h, Matrix.smul_mul, Model.flux]

/-- The gradient of the checkerboard is orthogonal to the columns of `Xo`. -/
private theorem flux_Xo : ((octModel TK TL TS).flux chk).transpose * (octModel TK TL TS).Wx * Xo =
    0 := by
  have h : ((octModel TK TL TS).gradMat chk).transpose * (octModel TK TL TS).Wx * Xo = 0 := by
    ext m j
    rw [Model.Wx, mul_diag_mul', Matrix.zero_apply]
    change ∑ x : Fin 4, (if m = 0 then fwd else 0 : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) chk x *
      (1 / 4) * Xo x j = 0
    by_cases hm : m = 0
    · rw [ite_eq_left hm, fwd_chk]
      fin_cases j <;> simp [Xo, Fin.sum_univ_four]
    · rw [ite_eq_right hm]
      simp
  rw [Model.flux, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
    Matrix.mul_assoc, ← Matrix.mul_assoc _ _ Xo, h, Matrix.mul_zero]

private theorem V0_span : (octModel TK TL TS).VelInSpan V0 := by
  intro m
  have h : (octModel TK TL TS).vel m = octC⁻¹ • V0.transpose m := by
    ext w
    change octVel m w = octC⁻¹ * (octC * octVel m w)
    rw [← mul_assoc, inv_mul_cancel₀ octC_ne, one_mul]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

/-- The value of the limit of the micro part at one point. -/
private theorem gLim_chk (t : ℝ) : (octModel TK TL TS).gLim (t • chk) 0 (0, true) = -t := by
  rw [(octModel_admissible TK TL TS).gLim_apply, Fin.sum_univ_three]
  change -((1 : ℝ)⁻¹ * ((if (0 : Fin 3) = 0 then fwd else 0 :
      (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) (t • chk) 0 * octVel 0 (0, true) +
    (if (1 : Fin 3) = 0 then fwd else 0 : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) (t • chk) 0 *
      octVel 1 (0, true) +
    (if (2 : Fin 3) = 0 then fwd else 0 : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) (t • chk) 0 *
      octVel 2 (0, true))) = -t
  simp [map_smul, fwd_chk, octVel]

/-- The value of the diffusion operator at one point. -/
private theorem diffOp_chk (t : ℝ) : (octModel TK TL TS).diffOp (t • chk) 0 = 2 * t / 3 := by
  have h1 : ∀ m : Fin 3, m ≠ 0 → (octModel TK TL TS).dvg m = 0 := fun m hm => by
    simp [octModel, hm]
  have h2 : (octModel TK TL TS).dvg 0 = bwd := by simp [octModel]
  have h3 : (octModel TK TL TS).grad 0 = fwd := by simp [octModel]
  have h4 : (octModel TK TL TS).σS = fun _ => 1 := rfl
  have h5 : fwd (t • chk) = t • ![1, -1, 1, -1] := by rw [map_smul, fwd_chk]
  have h6 : bwd (fwd (t • chk)) 0 = 2 * t := by
    have h7 : (0 : Fin 4) - 1 = 3 := by decide
    rw [h5]
    change (t • ![(1 : ℝ), -1, 1, -1]) 0 - (t • ![(1 : ℝ), -1, 1, -1]) (0 - 1) = _
    rw [h7]
    simp
    ring
  simp only [Model.diffOp, Fin.sum_univ_three]
  rw [h1 1 (by decide), h1 2 (by decide), h2, h3, h4]
  simp only [LinearMap.zero_apply, Pi.zero_apply, add_zero, div_one]
  change 1 / 3 * bwd (fwd (t • chk)) 0 = _
  rw [h6]
  ring

private theorem diffOp_zero : (octModel TK TL TS).diffOp 0 = 0 := by
  have h : ∀ m, (fun x => (octModel TK TL TS).grad m 0 x / (octModel TK TL TS).σS x) = 0 := by
    intro m
    ext x
    simp
  have h2 : ∀ m, (octModel TK TL TS).dvg m
      (fun x => (octModel TK TL TS).grad m 0 x / (octModel TK TL TS).σS x) = 0 := fun m => by
    rw [h m, map_zero]
  ext j
  simp only [Model.diffOp, h2, Pi.zero_apply, Finset.sum_const_zero, mul_zero]

/-- **Prop. 3.1 of arXiv 2005.06571 is false without the independence of the components of
`∇ₓ ρ / σ^S`, against footnote 2 of the paper.**  In `octModel`, with `ξ, η, γ ∈ span {Vⱼ⁰}`, take
`ρ⁰ = 0`, `g⁰ = 0` and the source `G = chk`: a run of the scheme (3.15)-(3.20) exists for all `ε`
and all `n`, with `g = 0` at every step, whereas the limit claimed is
`g² = -v · ∇ₓ ρ¹ / σ^S ≠ 0`, and `ρ²` is not the forward Euler step.

The first step is degenerate: `∇ₓ ρ⁰ = 0`, so `L¹ = 0`, its QR factorization (3.18) puts no
constraint on `V¹`, and `V¹ ⊥ ξ, η, γ` is allowed.  So (3.25) fails, and with it the induction: the
source makes `∇ₓ ρ¹ ≠ 0`, but the method has lost `v`.  Such data are natural: zero initial data
with a source.  The transport operators are arbitrary here, so this is the scheme of the paper. -/
theorem prop_3_1_false_without_independence {dt : ℝ} (hdt : 0 < dt) :
    ∃ (ρ : ℕ → Fin 4 → ℝ) (X : ℕ → Matrix (Fin 4) (Fin 3) ℝ) (S : ℕ → Matrix (Fin 3) (Fin 3) ℝ)
      (V : ℕ → Matrix Oct (Fin 3) ℝ), (octModel TK TL TS).VelInSpan (V 0) ∧
      (∀ ε n, (octModel TK TL TS).IsStep .KLS dt ε (ρ n) (X n) (S n) (V n) (ρ (n + 1))
        (X (n + 1)) (S (n + 1)) (V (n + 1))) ∧
      (∀ n, X (n + 1) * S (n + 1) * (V (n + 1)).transpose = 0) ∧
      ρ 1 = (octModel TK TL TS).eulerStep dt (ρ 0) ∧ (octModel TK TL TS).gLim (ρ 1) ≠ 0 ∧
      ρ 2 ≠ (octModel TK TL TS).eulerStep dt (ρ 1) := by
  set M := octModel TK TL TS with hM
  let ρ : ℕ → Fin 4 → ℝ := fun n => ((n : ℝ) * dt) • chk
  let V : ℕ → Matrix Oct (Fin 3) ℝ := fun n => if n = 0 then V0 else Vz
  have hV : ∀ n, (V n).transpose * M.Wv * V n = 1 := fun n => by
    by_cases h : n = 0
    · simp only [V, ite_eq_left h]
      exact V0_orth TK TL TS
    · simp only [V, ite_eq_right h]
      exact Vz_orth TK TL TS
  have hK : ∀ n, M.flux (ρ n) * M.Wv * V n = 0 := fun n => by
    by_cases h : n = 0
    · subst h
      have h0 : M.flux (ρ 0) = 0 := by
        have h1 : ρ 0 = (0 : ℝ) • chk := by simp [ρ]
        rw [h1, flux_smul, zero_smul]
      rw [h0, Matrix.zero_mul, Matrix.zero_mul]
    · simp only [V, ite_eq_right h]
      exact flux_Vz TK TL TS _
  have hL : ∀ n, (M.flux (ρ n)).transpose * M.Wx * Xo = 0 := fun n => by
    simp only [ρ, flux_smul, Matrix.transpose_smul, Matrix.smul_mul]
    rw [flux_Xo, smul_zero]
  have hρ1 : ρ 1 = dt • chk := by simp [ρ]
  have hρ2 : ρ 2 = (2 * dt) • chk := by simp [ρ]
  have hdt' : dt ≠ 0 := hdt.ne'
  refine ⟨ρ, fun _ => Xo, fun _ => 0, V, ?_, fun ε n => ?_, fun n => ?_, ?_, ?_, ?_⟩
  · simpa [V] using V0_span TK TL TS
  · refine ⟨Xo_orth TK TL TS, hV n, Xo_orth TK TL TS, hV (n + 1),
      M.micro_KLS_zero (hK n) (hL n), ?_⟩
    simp only [Matrix.mul_zero, Matrix.zero_mul, M.rhoRHS_zero]
    ext j
    have h : M.σAρ j = 0 := rfl
    have h' : M.src j = chk j := rfl
    simp only [ρ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h, h']
    push_cast
    ring
  · simp
  · rw [hρ1]
    ext j
    have h : M.σAρ j = 0 := rfl
    have h' : M.src j = chk j := rfl
    have h2 : ρ 0 = 0 := by simp [ρ]
    rw [h2, Model.eulerStep]
    simp only [Pi.add_apply, Pi.smul_apply, Model.diffRHS, diffOp_zero, hM, smul_eq_mul]
    change dt * chk j = 0 + dt * (0 - 0 * 0 + chk j)
    ring
  · intro h
    have h1 := congrFun (congrFun h 0) (0, true)
    rw [hρ1, gLim_chk] at h1
    exact hdt' (by simpa using h1)
  · intro h
    have h1 := congrFun h 0
    have hchk : chk 0 = 0 := rfl
    rw [hρ2, hρ1, Model.eulerStep] at h1
    have h2 : M.diffOp (dt • chk) 0 = 2 * dt / 3 := diffOp_chk TK TL TS dt
    have h3 : M.src 0 = 0 := rfl
    simp only [Pi.add_apply, Pi.smul_apply, Model.diffRHS, smul_eq_mul, hchk, mul_zero,
      zero_add, h2, h3] at h1
    have h4 : dt * (2 * dt / 3) = 0 := by linarith
    have h5 : dt * dt = 0 := by nlinarith
    exact hdt' (by simpa using h5)

/-- **The claim of Sec. 3.3 of arXiv 2005.06571 for `L-K-S-ρ`, `L-S-K-ρ`, `S-L-K-ρ` is false as
stated.**  With `ξ, η, γ ∈ span {Vⱼⁿ}`, the hypothesis of Prop. 3.1, and `(Xⁿ)ᵀ ∇ₓ ρⁿ = 0`, the
`L`-step gives `L¹ = 0` for all `ε`, the QR factorization allows `V¹ ⊥ ξ, η, γ`, and then `g¹ = 0`
for all `ε`, not `-v · ∇ₓ ρⁿ / σ^S`.  The claim needs the rank hypothesis of `sec_3_3_step`. -/
theorem sec_3_3_false_without_rank {dt : ℝ} (hdt : 0 < dt) {o : Order}
    (ho : o = .LKS ∨ o = .LSK ∨ o = .SLK) :
    (octModel TK TL TS).VelInSpan V0 ∧
      (∀ ε, (octModel TK TL TS).IsStep o dt ε chk Xo 0 V0 (chk + dt • chk) Xo 0 Vz) ∧
      Xo * (0 : Matrix (Fin 3) (Fin 3) ℝ) * Vz.transpose = 0 ∧
      (octModel TK TL TS).gLim chk ≠ 0 ∧
      chk + dt • chk ≠ (octModel TK TL TS).eulerStep dt chk := by
  set M := octModel TK TL TS with hM
  have hrho : chk + dt • chk =
      chk + dt • M.rhoRHS (Xo * (0 : Matrix (Fin 3) (Fin 3) ℝ) * Vz.transpose) chk := by
    simp only [Matrix.mul_zero, Matrix.zero_mul, M.rhoRHS_zero]
    ext j
    have h : M.σAρ j = 0 := rfl
    have h' : M.src j = chk j := rfl
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h, h']
    ring
  have hK := flux_Vz TK TL TS chk
  have hL := flux_Xo TK TL TS
  refine ⟨V0_span TK TL TS, fun ε => ⟨Xo_orth TK TL TS, V0_orth TK TL TS, Xo_orth TK TL TS,
    Vz_orth TK TL TS, ?_, hrho⟩, by simp, ?_, ?_⟩
  · rcases ho with rfl | rfl | rfl
    · exact M.micro_LKS_zero hK hL
    · exact M.micro_LSK_zero hK hL
    · exact M.micro_SLK_zero hK hL
  · intro h
    have h1 := congrFun (congrFun h 0) (0, true)
    have h2 := gLim_chk TK TL TS 1
    rw [one_smul] at h2
    rw [h1] at h2
    norm_num at h2
  · intro h
    have h1 := congrFun h 0
    have h2 : M.diffOp chk 0 = 2 * 1 / 3 := by
      have h6 := diffOp_chk TK TL TS 1
      rwa [one_smul] at h6
    have hchk : chk 0 = 0 := rfl
    have h3 : M.σAρ 0 = 0 := rfl
    have h4 : M.src 0 = 0 := rfl
    rw [Model.eulerStep] at h1
    simp only [Pi.add_apply, Pi.smul_apply, Model.diffRHS, smul_eq_mul, hchk, h3, h4, h2] at h1
    have h5 : dt * (2 * 1 / 3) = 0 := by linarith
    exact hdt.ne' (by nlinarith)

end Oct

/-! ### Solvability of the scheme -/

section Exists

variable {I J W ι : Type*} [Fintype I] [Fintype J] [Fintype W] [Fintype ι]
  [DecidableEq I] [DecidableEq W] [DecidableEq ι] {k : ℕ}

/-- A QR factorization in a weighted inner product, also for rank-deficient `K`. -/
private theorem exists_qr {n : Type*} [Fintype n] [DecidableEq n] (ω : n → ℝ) (hω : ∀ i, 0 < ω i)
    (hk : k ≤ Fintype.card n) (K : Matrix n (Fin k) ℝ) :
    ∃ (U : Matrix n (Fin k) ℝ) (R : Matrix (Fin k) (Fin k) ℝ),
      U.transpose * Matrix.diagonal ω * U = 1 ∧ K = U * R := by
  let s : n → ℝ := fun i => √(ω i)
  have hs : ∀ i, s i * s i = ω i := fun i => Real.mul_self_sqrt (hω i).le
  have hs0 : ∀ i, s i ≠ 0 := fun i => (Real.sqrt_pos.2 (hω i)).ne'
  obtain ⟨U, hU, hc⟩ := exists_orthonormal_capture_of_le_card (Matrix.diagonal s * K) hk
  refine ⟨Matrix.diagonal (fun i => (s i)⁻¹) * U, U.transpose * (Matrix.diagonal s * K), ?_, ?_⟩
  · have h1 : (Matrix.diagonal fun i => (s i)⁻¹) * Matrix.diagonal ω *
        (Matrix.diagonal fun i => (s i)⁻¹) = (1 : Matrix n n ℝ) := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      refine congrArg _ (funext fun i => ?_)
      rw [← hs i]
      have := hs0 i
      field_simp
    rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
    calc U.transpose * (Matrix.diagonal fun i => (s i)⁻¹) * Matrix.diagonal ω *
          ((Matrix.diagonal fun i => (s i)⁻¹) * U)
        = U.transpose * ((Matrix.diagonal fun i => (s i)⁻¹) * Matrix.diagonal ω *
          (Matrix.diagonal fun i => (s i)⁻¹)) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hU]
  · have h2 : (Matrix.diagonal fun i => (s i)⁻¹) * (Matrix.diagonal s : Matrix n n ℝ) = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      exact congrArg _ (funext fun i => inv_mul_cancel₀ (hs0 i))
    calc K = (Matrix.diagonal fun i => (s i)⁻¹) * (Matrix.diagonal s * K) := by
          rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
      _ = (Matrix.diagonal fun i => (s i)⁻¹) * (U * U.transpose * (Matrix.diagonal s * K)) := by
          rw [hc]
      _ = _ := by simp only [Matrix.mul_assoc]

/-- `1 + c ⟨X σ X⟩ₓ` is invertible for `c ≥ 0`, and for `c σ₀ < -1`, which is the sign of the
`S`-step. -/
private theorem isUnit_one_add_stiff {r : Type*} [Fintype r] [DecidableEq r] {ω σ : I → ℝ}
    (hω : ∀ i, 0 < ω i) {σ₀ c : ℝ} (hσ₀ : 0 < σ₀) (hσ : ∀ i, σ₀ ≤ σ i) {X : Matrix I r ℝ}
    (hX : X.transpose * Matrix.diagonal ω * X = 1) (hc : 0 ≤ c ∨ c * σ₀ < -1) :
    IsUnit (1 + c • (X.transpose * Matrix.diagonal ω * Matrix.diagonal σ * X)) := by
  have hquad : ∀ (d : I → ℝ) (z : r → ℝ), z ⬝ᵥ ((X.transpose * Matrix.diagonal d * X).mulVec z) =
      ∑ i, d i * (X.mulVec z) i ^ 2 := by
    intro d z
    have h : (X.transpose * Matrix.diagonal d * X).mulVec z =
        X.transpose.mulVec ((Matrix.diagonal d).mulVec (X.mulVec z)) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [h, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_diagonal]
    ring
  set S := X.transpose * Matrix.diagonal ω * Matrix.diagonal σ * X with hS
  have hS' : S = X.transpose * Matrix.diagonal (fun i => ω i * σ i) * X := by
    rw [hS, Matrix.mul_assoc X.transpose, Matrix.diagonal_mul_diagonal]
  have key : ∀ z : r → ℝ, (1 + c • S).mulVec z = 0 → z = 0 := by
    intro z hz
    set u := X.mulVec z with hu
    have h1 : z ⬝ᵥ z + c * (z ⬝ᵥ S.mulVec z) = 0 := by
      have h2 := congrArg (fun w => z ⬝ᵥ w) hz
      simpa [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul] using h2
    have h2 : z ⬝ᵥ z = ∑ i, ω i * u i ^ 2 := by
      rw [← hquad ω z, hX, Matrix.one_mulVec]
    have h3 : z ⬝ᵥ S.mulVec z = ∑ i, ω i * σ i * u i ^ 2 := by
      rw [hS', hquad]
    have h4 : σ₀ * (z ⬝ᵥ z) ≤ z ⬝ᵥ S.mulVec z := by
      rw [h2, h3, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h5 := hω i
      have h6 := hσ i
      have h7 : 0 ≤ ω i * u i ^ 2 := by positivity
      nlinarith
    have h5 : 0 ≤ z ⬝ᵥ z := by
      rw [h2]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hω i).le (sq_nonneg _)
    have h6 : z ⬝ᵥ z = 0 := by
      rcases hc with hc | hc
      · have h7 : 0 ≤ c * (z ⬝ᵥ S.mulVec z) :=
          mul_nonneg hc (le_trans (mul_nonneg hσ₀.le h5) h4)
        linarith
      · have hc0 : c < 0 := by
          by_contra hc0
          have : 0 ≤ c * σ₀ := mul_nonneg (not_lt.1 hc0) hσ₀.le
          linarith
        have h7 : c * (z ⬝ᵥ S.mulVec z) ≤ c * (σ₀ * (z ⬝ᵥ z)) :=
          mul_le_mul_of_nonpos_left h4 hc0.le
        nlinarith
    exact dotProduct_self_eq_zero.1 h6
  refine Matrix.mulVec_injective_iff_isUnit.1 fun a b hab => ?_
  refine sub_eq_zero.1 (key (a - b) ?_)
  rw [Matrix.mulVec_sub]
  exact sub_eq_zero.2 hab

section Implicit

variable {r : Type*} [Fintype r] [DecidableEq r] {M : Model I J W ι} {ε c : ℝ}

/-- The implicit part of a `K`-step can be solved. -/
private theorem exists_kImp (hM : M.Admissible) (hc : 0 ≤ c) (b : Matrix I r ℝ) :
    ∃ y, y = b + c • M.kImp ε y := by
  set s := c * (ε ^ 2)⁻¹ with hs
  have hs0 : 0 ≤ s := by positivity
  refine ⟨Matrix.diagonal (fun x => (1 + s * M.σS x)⁻¹) * b, ?_⟩
  ext i j
  have hne : 1 + s * M.σS i ≠ 0 := by
    have := hM.σS_pos i
    positivity
  simp only [Model.kImp, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_neg,
    Matrix.diagonal_mul, smul_eq_mul]
  have h : c * ((ε ^ 2)⁻¹ * (M.σS i * ((1 + s * M.σS i)⁻¹ * b i j))) =
      s * M.σS i * ((1 + s * M.σS i)⁻¹ * b i j) := by
    rw [hs]
    ring
  rw [h]
  field_simp
  ring

/-- The implicit part of an `L`-step can be solved. -/
private theorem exists_lImp (hM : M.Admissible) {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hlo : ∀ x, σ₀ ≤ M.σS x)
    {X : Matrix I r ℝ} (hX : X.transpose * M.Wx * X = 1) (hc : 0 ≤ c) (b : Matrix W r ℝ) :
    ∃ y, y = b + c • M.lImp ε X y := by
  set s := c * (ε ^ 2)⁻¹ with hs
  have hs0 : 0 ≤ s := by positivity
  set A := X.transpose * M.Wx * Matrix.diagonal M.σS * X with hA
  have hu : IsUnit (1 + s • A) := isUnit_one_add_stiff hM.ωx_pos hσ₀ hlo hX (Or.inl hs0)
  refine ⟨b * (1 + s • A)⁻¹, ?_⟩
  have h1 : b * (1 + s • A)⁻¹ * (1 + s • A) = b := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu),
      Matrix.mul_one]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul] at h1
  refine (eq_sub_of_add_eq h1).trans ?_
  rw [Model.lImp, hs]
  module

/-- The implicit part of an `S`-step can be solved, for small `ε`: the step runs backward. -/
private theorem exists_sImp (hM : M.Admissible) {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hlo : ∀ x, σ₀ ≤ M.σS x)
    {X : Matrix I r ℝ} (hX : X.transpose * M.Wx * X = 1) (hc : 1 < c * (ε ^ 2)⁻¹ * σ₀)
    (b : Matrix r r ℝ) : ∃ y, y = b + c • M.sImp ε X y := by
  set s := c * (ε ^ 2)⁻¹ with hs
  set A := X.transpose * M.Wx * Matrix.diagonal M.σS * X with hA
  have hu : IsUnit (1 + (-s) • A) :=
    isUnit_one_add_stiff hM.ωx_pos hσ₀ hlo hX (Or.inr (by linarith))
  refine ⟨(1 + (-s) • A)⁻¹ * b, ?_⟩
  have h1 : (1 + (-s) • A) * ((1 + (-s) • A)⁻¹ * b) = b := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu),
      Matrix.one_mul]
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul] at h1
  refine (eq_sub_of_add_eq h1).trans ?_
  rw [Model.sImp, hs]
  module

end Implicit

/-- A forward-backward Euler step can be solved if its implicit part can. -/
private theorem exists_imex {Y : Type*} [AddCommGroup Y] [Module ℝ Y] {F F' : Y → Y} {dt : ℝ}
    (h : ∀ b, ∃ y, y = b + dt • F' y) (y : Y) : ∃ y₁, IsIMEX F F' dt y y₁ := by
  obtain ⟨y₁, hy⟩ := h (y + dt • F y)
  refine ⟨y₁, ?_⟩
  rw [IsIMEX]
  nth_rw 1 [hy]
  module

/-- An ARS(2,2,2) step can be solved if its implicit part can. -/
private theorem exists_ars {Y : Type*} [AddCommGroup Y] [Module ℝ Y] {F F' : Y → Y} {dt : ℝ}
    (h : ∀ b, ∃ y, y = b + (dt * arsγ) • F' y) (y : Y) : ∃ y₁, IsARS F F' dt y y₁ := by
  obtain ⟨y₂, hy₂⟩ := h (y + (dt * arsγ) • F y)
  obtain ⟨y₁, hy₁⟩ := h (y + dt • (arsδ • F y + (1 - arsδ) • F y₂ + (1 - arsγ) • F' y₂))
  refine ⟨y₁, y₂, ?_, ?_⟩
  · nth_rw 1 [hy₂]
    module
  · nth_rw 1 [hy₁]
    module

private theorem exists_lower (M : Model I J W ι) (hM : M.Admissible) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∀ x, σ₀ ≤ M.σS x := by
  rcases isEmpty_or_nonempty I with h | h
  · exact ⟨1, one_pos, fun i => h.elim i⟩
  · obtain ⟨x₀, hx₀⟩ := Finite.exists_min M.σS
    exact ⟨M.σS x₀, hM.σS_pos x₀, hx₀⟩

/-- arXiv 2005.06571, (3.15)-(3.20) and Sec. 3.3.
**Solvability of one step of the first order scheme, in each of the six orderings**: for small
`ε`, from all data with orthonormal `X`, `V` of rank `k ≤ card I, card W`, there is a step.  The
smallness of `ε` is needed by the `S`-step, which runs backward in time. -/
theorem exists_step (M : Model I J W ι) (hM : M.Admissible) (hI : k ≤ Fintype.card I)
    (hW : k ≤ Fintype.card W) {dt : ℝ} (hdt : 0 < dt) (o : Order) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → ∀ (ρ : J → ℝ) (X : Matrix I (Fin k) ℝ)
      (S : Matrix (Fin k) (Fin k) ℝ) (V : Matrix W (Fin k) ℝ), X.transpose * M.Wx * X = 1 →
      V.transpose * M.Wv * V = 1 → ∃ (X₁ : Matrix I (Fin k) ℝ) (S₁ : Matrix (Fin k) (Fin k) ℝ)
        (V₁ : Matrix W (Fin k) ℝ), M.IsStep o dt ε ρ X S V
          (ρ + dt • M.rhoRHS (X₁ * S₁ * V₁.transpose) ρ) X₁ S₁ V₁ := by
  obtain ⟨σ₀, hσ₀, hlo⟩ := exists_lower M hM
  refine ⟨√(dt * σ₀), by positivity, fun ε hε hε₀ ρ X S V hX hV => ?_⟩
  have hε2 : ε ^ 2 < dt * σ₀ := (Real.lt_sqrt hε.le).1 hε₀
  have hs1 : 1 < dt * (ε ^ 2)⁻¹ * σ₀ := by
    rw [mul_comm dt, mul_assoc, inv_mul_eq_div, one_lt_div (by positivity)]
    exact hε2
  set Φ := M.flux ρ with hΦ
  have iK : ∀ (V' : Matrix W (Fin k) ℝ) (K₀ : Matrix I (Fin k) ℝ),
      ∃ K₁, IsIMEX (M.kExp ε Φ V') (M.kImp ε) dt K₀ K₁ := fun V' K₀ =>
    exists_imex (fun b => exists_kImp hM hdt.le b) K₀
  have iL : ∀ (X' : Matrix I (Fin k) ℝ), X'.transpose * M.Wx * X' = 1 →
      ∀ L₀ : Matrix W (Fin k) ℝ, ∃ L₁, IsIMEX (M.lExp ε Φ X') (M.lImp ε X') dt L₀ L₁ :=
    fun X' hX' L₀ => exists_imex (fun b => exists_lImp hM hσ₀ hlo hX' hdt.le b) L₀
  have iS : ∀ (X' : Matrix I (Fin k) ℝ), X'.transpose * M.Wx * X' = 1 →
      ∀ (V' : Matrix W (Fin k) ℝ) (S₀ : Matrix (Fin k) (Fin k) ℝ),
      ∃ S₁, IsIMEX (M.sExp ε Φ X' V') (M.sImp ε X') dt S₀ S₁ :=
    fun X' hX' _ S₀ => exists_imex (fun b => exists_sImp hM hσ₀ hlo hX' hs1 b) S₀
  have qX : ∀ K : Matrix I (Fin k) ℝ, ∃ (X₁ : Matrix I (Fin k) ℝ) (R : Matrix (Fin k) (Fin k) ℝ),
      X₁.transpose * M.Wx * X₁ = 1 ∧ K = X₁ * R := exists_qr M.ωx hM.ωx_pos hI
  have qV : ∀ L : Matrix W (Fin k) ℝ, ∃ (V₁ : Matrix W (Fin k) ℝ) (R : Matrix (Fin k) (Fin k) ℝ),
      V₁.transpose * M.Wv * V₁ = 1 ∧ L = V₁ * R.transpose := fun L => by
    obtain ⟨V₁, T, h1, h2⟩ := exists_qr M.ωv hM.ωv_pos hW L
    exact ⟨V₁, T.transpose, h1, by rwa [Matrix.transpose_transpose]⟩
  cases o with
  | KLS =>
    obtain ⟨K₁, h1⟩ := iK V (X * S)
    obtain ⟨X₁, S', hX₁, h2⟩ := qX K₁
    obtain ⟨L₁, h3⟩ := iL X₁ hX₁ (V * S'.transpose)
    obtain ⟨V₁, S'', hV₁, h4⟩ := qV L₁
    obtain ⟨S₁, h5⟩ := iS X₁ hX₁ V₁ S''
    exact ⟨X₁, S₁, V₁, hX, hV, hX₁, hV₁, ⟨K₁, S', L₁, S'', h1, h2, h3, h4, h5⟩, rfl⟩
  | LKS =>
    obtain ⟨L₁, h1⟩ := iL X hX (V * S.transpose)
    obtain ⟨V₁, S', hV₁, h2⟩ := qV L₁
    obtain ⟨K₁, h3⟩ := iK V₁ (X * S')
    obtain ⟨X₁, S'', hX₁, h4⟩ := qX K₁
    obtain ⟨S₁, h5⟩ := iS X₁ hX₁ V₁ S''
    exact ⟨X₁, S₁, V₁, hX, hV, hX₁, hV₁, ⟨L₁, S', K₁, S'', h1, h2, h3, h4, h5⟩, rfl⟩
  | LSK =>
    obtain ⟨L₁, h1⟩ := iL X hX (V * S.transpose)
    obtain ⟨V₁, S', hV₁, h2⟩ := qV L₁
    obtain ⟨S'', h3⟩ := iS X hX V₁ S'
    obtain ⟨K₁, h4⟩ := iK V₁ (X * S'')
    obtain ⟨X₁, S₁, hX₁, h5⟩ := qX K₁
    exact ⟨X₁, S₁, V₁, hX, hV, hX₁, hV₁, ⟨L₁, S', S'', K₁, h1, h2, h3, h4, h5⟩, rfl⟩
  | SLK =>
    obtain ⟨S', h1⟩ := iS X hX V S
    obtain ⟨L₁, h2⟩ := iL X hX (V * S'.transpose)
    obtain ⟨V₁, S'', hV₁, h3⟩ := qV L₁
    obtain ⟨K₁, h4⟩ := iK V₁ (X * S'')
    obtain ⟨X₁, S₁, hX₁, h5⟩ := qX K₁
    exact ⟨X₁, S₁, V₁, hX, hV, hX₁, hV₁, ⟨S', L₁, S'', K₁, h1, h2, h3, h4, h5⟩, rfl⟩
  | KSL =>
    obtain ⟨K₁, h1⟩ := iK V (X * S)
    obtain ⟨X₁, S', hX₁, h2⟩ := qX K₁
    obtain ⟨S'', h3⟩ := iS X₁ hX₁ V S'
    obtain ⟨L₁, h4⟩ := iL X₁ hX₁ (V * S''.transpose)
    obtain ⟨V₁, S₁, hV₁, h5⟩ := qV L₁
    exact ⟨X₁, S₁, V₁, hX, hV, hX₁, hV₁, ⟨K₁, S', S'', L₁, h1, h2, h3, h4, h5⟩, rfl⟩
  | SKL =>
    obtain ⟨S', h1⟩ := iS X hX V S
    obtain ⟨K₁, h2⟩ := iK V (X * S')
    obtain ⟨X₁, S'', hX₁, h3⟩ := qX K₁
    obtain ⟨L₁, h4⟩ := iL X₁ hX₁ (V * S''.transpose)
    obtain ⟨V₁, S₁, hV₁, h5⟩ := qV L₁
    exact ⟨X₁, S₁, V₁, hX, hV, hX₁, hV₁, ⟨S', K₁, S'', L₁, h1, h2, h3, h4, h5⟩, rfl⟩

/-- arXiv 2005.06571, Sec. 3.1, Sec. 3.3.  **Solvability of the first order scheme**: for small `ε`,
there is a run from any data, in each of the six orderings. -/
theorem exists_run (M : Model I J W ι) (hM : M.Admissible) (hI : k ≤ Fintype.card I)
    (hW : k ≤ Fintype.card W) {dt : ℝ} (hdt : 0 < dt) (o : Order) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → ∀ (ρ₀ : J → ℝ) (X₀ : Matrix I (Fin k) ℝ)
      (S₀ : Matrix (Fin k) (Fin k) ℝ) (V₀ : Matrix W (Fin k) ℝ), X₀.transpose * M.Wx * X₀ = 1 →
      V₀.transpose * M.Wv * V₀ = 1 → ∃ (ρ : ℕ → J → ℝ) (X : ℕ → Matrix I (Fin k) ℝ)
        (S : ℕ → Matrix (Fin k) (Fin k) ℝ) (V : ℕ → Matrix W (Fin k) ℝ),
        ρ 0 = ρ₀ ∧ X 0 = X₀ ∧ S 0 = S₀ ∧ V 0 = V₀ ∧ ∀ n, M.IsStep o dt ε (ρ n) (X n) (S n) (V n)
          (ρ (n + 1)) (X (n + 1)) (S (n + 1)) (V (n + 1)) := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_step M hM hI hW hdt o
  refine ⟨ε₀, hε₀, fun ε hε hε' ρ₀ X₀ S₀ V₀ hX hV => ?_⟩
  let St := {p : (J → ℝ) × Matrix I (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ × Matrix W (Fin k) ℝ //
    p.2.1.transpose * M.Wx * p.2.1 = 1 ∧ p.2.2.2.transpose * M.Wv * p.2.2.2 = 1}
  have hs : ∀ p : St, ∃ q : St, M.IsStep o dt ε p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 q.1.1 q.1.2.1
      q.1.2.2.1 q.1.2.2.2 := by
    intro p
    obtain ⟨X₁, S₁, V₁, hstep⟩ := h ε hε hε' p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2.1 p.2.2
    exact ⟨⟨(_, X₁, S₁, V₁), hstep.hX₁, hstep.hV₁⟩, hstep⟩
  choose f hf using hs
  let s : ℕ → St := fun n => f^[n] ⟨(ρ₀, X₀, S₀, V₀), hX, hV⟩
  refine ⟨fun n => (s n).1.1, fun n => (s n).1.2.1, fun n => (s n).1.2.2.1,
    fun n => (s n).1.2.2.2, rfl, rfl, rfl, rfl, fun n => ?_⟩
  have h1 : s (n + 1) = f (s n) := Function.iterate_succ_apply' f n _
  simp only [h1]
  exact hf (s n)

/-- arXiv 2005.06571, Sec. 3.4.  **Solvability of one step of the second order scheme**, for small
`ε`. -/
theorem exists_step2 (M : Model I J W ι) (hM : M.Admissible) (hI : k ≤ Fintype.card I)
    (hW : k ≤ Fintype.card W) {dt : ℝ} (hdt : 0 < dt) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → ∀ (ρ : J → ℝ) (X : Matrix I (Fin k) ℝ)
      (S : Matrix (Fin k) (Fin k) ℝ) (V : Matrix W (Fin k) ℝ), X.transpose * M.Wx * X = 1 →
      V.transpose * M.Wv * V = 1 → ∃ (ρh : J → ℝ) (Xh : Matrix I (Fin k) ℝ)
        (Sh : Matrix (Fin k) (Fin k) ℝ) (Vh : Matrix W (Fin k) ℝ) (X₁ : Matrix I (Fin k) ℝ)
        (S₁ : Matrix (Fin k) (Fin k) ℝ) (V₁ : Matrix W (Fin k) ℝ),
        M.IsStep2 dt ε ρ X S V ρh Xh Sh Vh (ρ + dt • M.rhoRHS (Xh * Sh * Vh.transpose) ρh)
          X₁ S₁ V₁ := by
  obtain ⟨σ₀, hσ₀, hlo⟩ := exists_lower M hM
  have hc : 0 < dt / 2 * arsγ := mul_pos (by positivity) arsγ_pos
  refine ⟨√(dt / 2 * arsγ * σ₀), by positivity, fun ε hε hε₀ ρ X S V hX hV => ?_⟩
  have hε2 : ε ^ 2 < dt / 2 * arsγ * σ₀ := (Real.lt_sqrt hε.le).1 hε₀
  have hs1 : 1 < dt / 2 * arsγ * (ε ^ 2)⁻¹ * σ₀ := by
    rw [mul_comm (dt / 2 * arsγ), mul_assoc, inv_mul_eq_div, one_lt_div (by positivity)]
    exact hε2
  set ρh := ρ + (dt / 2) • M.rhoRHS (X * S * V.transpose) ρ with hρh
  set Φ := M.flux ρh with hΦ
  have iK : ∀ (V' : Matrix W (Fin k) ℝ) (K₀ : Matrix I (Fin k) ℝ),
      ∃ K₁, IsARS (M.kExp ε Φ V') (M.kImp ε) (dt / 2) K₀ K₁ := fun V' K₀ =>
    exists_ars (fun b => exists_kImp hM hc.le b) K₀
  have iL : ∀ (X' : Matrix I (Fin k) ℝ), X'.transpose * M.Wx * X' = 1 →
      ∀ L₀ : Matrix W (Fin k) ℝ, ∃ L₁, IsARS (M.lExp ε Φ X') (M.lImp ε X') (dt / 2) L₀ L₁ :=
    fun X' hX' L₀ => exists_ars (fun b => exists_lImp hM hσ₀ hlo hX' hc.le b) L₀
  have iS : ∀ (X' : Matrix I (Fin k) ℝ), X'.transpose * M.Wx * X' = 1 →
      ∀ (V' : Matrix W (Fin k) ℝ) (S₀ : Matrix (Fin k) (Fin k) ℝ),
      ∃ S₁, IsARS (M.sExp ε Φ X' V') (M.sImp ε X') (dt / 2) S₀ S₁ :=
    fun X' hX' _ S₀ => exists_ars (fun b => exists_sImp hM hσ₀ hlo hX' hs1 b) S₀
  have qX : ∀ K : Matrix I (Fin k) ℝ, ∃ (X₁ : Matrix I (Fin k) ℝ) (R : Matrix (Fin k) (Fin k) ℝ),
      X₁.transpose * M.Wx * X₁ = 1 ∧ K = X₁ * R := exists_qr M.ωx hM.ωx_pos hI
  have qV : ∀ L : Matrix W (Fin k) ℝ, ∃ (V₁ : Matrix W (Fin k) ℝ) (R : Matrix (Fin k) (Fin k) ℝ),
      V₁.transpose * M.Wv * V₁ = 1 ∧ L = V₁ * R.transpose := fun L => by
    obtain ⟨V₁, T, h1, h2⟩ := exists_qr M.ωv hM.ωv_pos hW L
    exact ⟨V₁, T.transpose, h1, by rwa [Matrix.transpose_transpose]⟩
  obtain ⟨K₁, h1⟩ := iK V (X * S)
  obtain ⟨Xh, S1, hXh, h2⟩ := qX K₁
  obtain ⟨L₁, h3⟩ := iL Xh hXh (V * S1.transpose)
  obtain ⟨Vh, S2, hVh, h4⟩ := qV L₁
  obtain ⟨Sh, h5⟩ := iS Xh hXh Vh S2
  obtain ⟨S3, h6⟩ := iS Xh hXh Vh Sh
  obtain ⟨L₂, h7⟩ := iL Xh hXh (Vh * S3.transpose)
  obtain ⟨V₁, S4, hV₁, h8⟩ := qV L₂
  obtain ⟨K₂, h9⟩ := iK V₁ (Xh * S4)
  obtain ⟨X₁, S₁, hX₁, h10⟩ := qX K₂
  exact ⟨ρh, Xh, Sh, Vh, X₁, S₁, V₁, hX, hV, hXh, hVh, hX₁, hV₁, rfl,
    ⟨K₁, S1, L₁, S2, S3, L₂, S4, K₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, rfl⟩

end Exists

section Instance

variable (TK TL TS : Matrix (Fin 3) Oct ℝ →ₗ[ℝ] Matrix (Fin 3) Oct ℝ)

/-- The point mass `ρ ↦ ρ m` at `m`, a diagonal gradient. -/
def pt (m : Fin 3) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun ρ x := if x = m then ρ m else 0
  map_add' ρ ρ' := by
    ext x
    by_cases h : x = m <;> simp [h]
  map_smul' c ρ := by
    ext x
    by_cases h : x = m <;> simp [h]

/-- A model in which the three components of the gradient are independent along the limit. -/
noncomputable def diagModel : Model (Fin 3) (Fin 3) Oct (Fin 3) where
  ωx := fun _ => 1
  ωv := fun _ => 2 * Real.pi / 3
  vel := octVel
  σS := fun _ => 1
  σA := fun _ => 0
  σAρ := fun _ => 0
  src := fun _ => 0
  grad := pt
  dvg := fun m => -pt m
  TK := TK
  TL := TL
  TS := TS

private theorem diagModel_admissible : (diagModel TK TL TS).Admissible where
  ωx_pos _ := by norm_num [diagModel]
  ωv_pos _ := by
    change 0 < 2 * Real.pi / 3
    positivity
  σS_pos _ := by norm_num [diagModel]
  iso m n := by
    change 1 / (4 * Real.pi) * ∑ w : Oct, 2 * Real.pi / 3 * octVel m w * octVel n w = _
    rw [sum_oct]
    fin_cases m <;> fin_cases n <;>
      simp [octVel, Fin.sum_univ_three] <;> field_simp <;> norm_num

private theorem diagModel_euler (dt : ℝ) (ρ : Fin 3 → ℝ) :
    (diagModel TK TL TS).eulerStep dt ρ = (1 - dt / 3) • ρ := by
  have h : ∀ j, (diagModel TK TL TS).diffOp ρ j = -(1 / 3) * ρ j := by
    intro j
    simp only [Model.diffOp, diagModel, div_one, LinearMap.neg_apply, Pi.neg_apply]
    rw [Fin.sum_univ_three]
    fin_cases j <;> simp [pt]
  ext j
  simp only [Model.eulerStep, Model.diffRHS, h, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change ρ j + dt * (-(1 / 3) * ρ j - 0 * ρ j + 0) = _
  ring

private theorem diagModel_indep {c : ℝ} (hc : c ≠ 0) :
    (diagModel TK TL TS).IndepGrad (c • fun _ => 1) := by
  rw [Model.IndepGrad, Fintype.linearIndependent_iff]
  intro g hg m
  have h1 := congrFun hg m
  rw [Fin.sum_univ_three] at h1
  fin_cases m <;> simp [diagModel, pt, hc] at h1 ⊢ <;> tauto

/-- The velocity basis `V0` is orthonormal in `diagModel`. -/
private theorem diag_V0_orth : V0.transpose * (diagModel TK TL TS).Wv * V0 = 1 := by
  have h := octC_mul
  ext i j
  rw [Model.Wv, mul_diag_mul, Matrix.one_apply]
  change ∑ w : Oct, octC * octVel i w * (2 * Real.pi / 3) * (octC * octVel j w) = _
  rw [sum_oct]
  fin_cases i <;> fin_cases j <;> simp [octVel, Fin.sum_univ_three] <;> nlinarith

private theorem diag_V0_span : (diagModel TK TL TS).VelInSpan V0 := by
  intro m
  have h : (diagModel TK TL TS).vel m = octC⁻¹ • V0.transpose m := by
    ext w
    change octVel m w = octC⁻¹ * (octC * octVel m w)
    rw [← mul_assoc, inv_mul_cancel₀ octC_ne, one_mul]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

/-- arXiv 2005.06571, Prop. 3.1.  **The hypotheses of `prop_3_1` can all hold**, in a model with
`dt < 3`, whose limit is the
decay `∂ₜ ρ = -ρ / 3`: there is a family of runs for `ε → 0` with `ξ, η, γ ∈ span {Vⱼ⁰}` and
independent components of the gradient along the limit. -/
theorem prop_3_1_hypotheses_hold {dt : ℝ} (hdt : 0 < dt) (hdt3 : dt < 3) :
    ∃ (ρ : ℝ → ℕ → Fin 3 → ℝ) (X : ℝ → ℕ → Matrix (Fin 3) (Fin 3) ℝ)
      (S : ℝ → ℕ → Matrix (Fin 3) (Fin 3) ℝ) (V : ℝ → ℕ → Matrix Oct (Fin 3) ℝ)
      (ρ₀ : Fin 3 → ℝ),
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ n, (diagModel TK TL TS).IsStep .KLS dt ε (ρ ε n) (X ε n) (S ε n)
        (V ε n) (ρ ε (n + 1)) (X ε (n + 1)) (S ε (n + 1)) (V ε (n + 1))) ∧
      Tendsto (fun ε => ρ ε 0) (𝓝[>] 0) (𝓝 ρ₀) ∧ Bd (𝓝[>] (0 : ℝ)) (fun ε => S ε 0) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), (diagModel TK TL TS).VelInSpan (V ε 0)) ∧
      ∀ n, (diagModel TK TL TS).IndepGrad (((diagModel TK TL TS).eulerStep dt)^[n] ρ₀) := by
  set M := diagModel TK TL TS with hMdef
  have hM : M.Admissible := diagModel_admissible TK TL TS
  have hX₀ : (1 : Matrix (Fin 3) (Fin 3) ℝ).transpose * M.Wx * 1 = 1 := by
    have h : M.Wx = 1 := by
      rw [Model.Wx, ← Matrix.diagonal_one]
      rfl
    rw [h]
    simp
  have hV₀ : V0.transpose * M.Wv * V0 = 1 := diag_V0_orth TK TL TS
  obtain ⟨ε₀, hε₀, hrun⟩ := exists_run (k := 3) M hM (by simp) (by simp) hdt .KLS
  have hc : ∀ ε : ℝ, ∃ (ρ : ℕ → Fin 3 → ℝ) (X : ℕ → Matrix (Fin 3) (Fin 3) ℝ)
      (S : ℕ → Matrix (Fin 3) (Fin 3) ℝ) (V : ℕ → Matrix Oct (Fin 3) ℝ), 0 < ε → ε < ε₀ →
      ρ 0 = (fun _ => 1) ∧ S 0 = 0 ∧ V 0 = V0 ∧ ∀ n, M.IsStep .KLS dt ε (ρ n) (X n) (S n) (V n)
        (ρ (n + 1)) (X (n + 1)) (S (n + 1)) (V (n + 1)) := by
    intro ε
    by_cases h : 0 < ε ∧ ε < ε₀
    · obtain ⟨ρ, X, S, V, h0, -, h2, h3, h4⟩ := hrun ε h.1 h.2 (fun _ => 1) 1 0 V0 hX₀ hV₀
      exact ⟨ρ, X, S, V, fun _ _ => ⟨h0, h2, h3, h4⟩⟩
    · exact ⟨fun _ _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
        fun h1 h2 => (h ⟨h1, h2⟩).elim⟩
  choose ρ X S V hall using hc
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 ε₀ := Ioo_mem_nhdsGT hε₀
  have he : ∀ ρ, M.eulerStep dt ρ = (1 - dt / 3) • ρ := diagModel_euler TK TL TS dt
  have hit : ∀ n, (M.eulerStep dt)^[n] (fun _ => 1) = (1 - dt / 3) ^ n • fun _ => (1 : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih, he, smul_smul, pow_succ']
  refine ⟨ρ, X, S, V, fun _ => 1, hev.mono fun ε h => (hall ε h.1 h.2).2.2.2,
    tendsto_const_nhds.congr' (hev.mono fun ε h => (hall ε h.1 h.2).1.symm), ?_,
    hev.mono fun ε h => ?_, fun n => ?_⟩
  · refine IsBigO.of_bound 1 (hev.mono fun ε h => ?_)
    rw [(hall ε h.1 h.2).2.1]
    simp
  · rw [(hall ε h.1 h.2).2.2.1]
    exact diag_V0_span TK TL TS
  · rw [hit]
    refine diagModel_indep TK TL TS (pow_ne_zero n ?_)
    linarith

end Instance

/-! ### Sec. 4: the Fourier analysis for constant `σ^S` -/

section Fourier

/-- The Fourier mode `e^{i k x}`. -/
noncomputable def ee (k : ℤ) (x : ℝ) : ℂ := Complex.exp (Complex.I * k * x)

private theorem hasDerivAt_ee (k : ℤ) (x : ℝ) : HasDerivAt (ee k) (Complex.I * k * ee k x) x := by
  have h1 : HasDerivAt (fun y : ℝ => Complex.I * k * (y : ℂ)) (Complex.I * k * 1) x :=
    (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul _
  have h2 := h1.cexp
  rw [mul_one] at h2
  have h3 : ee k = fun y : ℝ => Complex.exp (Complex.I * k * y) := rfl
  rw [h3, mul_comm (Complex.I * (k : ℂ))]
  exact h2

private theorem continuous_ee (k : ℤ) : Continuous (ee k) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_ee k x).continuousAt

private theorem ee_zero (k : ℤ) : ee k 0 = 1 := by simp [ee]

private theorem ee_two_pi (k : ℤ) : ee k (2 * Real.pi) = 1 := by
  rw [ee, ← Complex.exp_int_mul_two_pi_mul_I k]
  congr 1
  push_cast
  ring

private theorem ee_periodic (k : ℤ) : Function.Periodic (ee k) (2 * Real.pi) := fun x => by
  have h : Complex.I * k * ((x + 2 * Real.pi : ℝ) : ℂ) =
      Complex.I * k * x + k * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [ee, h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, ee]

private theorem ee_mul_ee (j k : ℤ) (x : ℝ) : ee j x * ee k x = ee (j + k) x := by
  rw [ee, ee, ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]

/-- The `k`-th Fourier coefficient `(2π)⁻¹ ∫₀^{2π} e^{-i k x} f(x) dx`. -/
noncomputable def coef (k : ℤ) (f : ℝ → Z) : Z :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ • ∫ x in (0 : ℝ)..(2 * Real.pi), ee (-k) x • f x

private theorem coef_clm {Z' : Type*} [NormedAddCommGroup Z'] [NormedSpace ℂ Z'] [CompleteSpace Z']
    (L : Z →L[ℂ] Z') {f : ℝ → Z} (hf : Continuous f) (k : ℤ) :
    coef k (fun x => L (f x)) = L (coef k f) := by
  have h : IntervalIntegrable (fun x => ee (-k) x • f x) MeasureTheory.volume 0 (2 * Real.pi) :=
    ((continuous_ee (-k)).smul hf).intervalIntegrable _ _
  rw [coef, coef, map_smul, ← ContinuousLinearMap.intervalIntegral_comp_comm L h]
  simp only [map_smul]

private theorem coef_add {f f' : ℝ → Z} (hf : Continuous f) (hf' : Continuous f') (k : ℤ) :
    coef k (fun x => f x + f' x) = coef k f + coef k f' := by
  have h1 : IntervalIntegrable (fun x => ee (-k) x • f x) MeasureTheory.volume 0 (2 * Real.pi) :=
    ((continuous_ee (-k)).smul hf).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x => ee (-k) x • f' x) MeasureTheory.volume 0 (2 * Real.pi) :=
    ((continuous_ee (-k)).smul hf').intervalIntegrable _ _
  simp only [coef, smul_add]
  rw [intervalIntegral.integral_add h1 h2, smul_add]

/-- Fourier coefficients of a derivative: `(∂ₓ f)^_k = i k f^_k`, by periodicity. -/
private theorem coef_deriv {f : ℝ → Z} (hf : ContDiff ℝ 1 f) (hp : Function.Periodic f (2 *
    Real.pi))
    (k : ℤ) : coef k (deriv f) = (Complex.I * k) • coef k f := by
  have hd : ∀ x, HasDerivAt f (deriv f x) x := fun x =>
    (hf.differentiable one_ne_zero x).hasDerivAt
  have hc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hc0 : Continuous f := hf.continuous
  have h1 : ∀ x, HasDerivAt (fun y => ee (-k) y • f y)
      ((Complex.I * (-k : ℤ) * ee (-k) x) • f x + ee (-k) x • deriv f x) x := fun x =>
    ((hasDerivAt_ee (-k) x).smul (hd x)).congr_deriv (add_comm _ _)
  have hi1 : IntervalIntegrable (fun x => (Complex.I * (-k : ℤ) * ee (-k) x) • f x)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (((continuous_const.mul (continuous_ee (-k))).smul hc0)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => ee (-k) x • deriv f x)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    ((continuous_ee (-k)).smul hc).intervalIntegrable _ _
  have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => h1 x) (hi1.add hi2)
  have h3 : f (2 * Real.pi) = f 0 := by simpa using hp 0
  rw [ee_two_pi, ee_zero, h3, sub_self, intervalIntegral.integral_add hi1 hi2] at h2
  have h4 : ∫ x in (0 : ℝ)..(2 * Real.pi), (Complex.I * (-k : ℤ) * ee (-k) x) • f x =
      (Complex.I * (-k : ℤ)) • ∫ x in (0 : ℝ)..(2 * Real.pi), ee (-k) x • f x := by
    rw [← intervalIntegral.integral_smul]
    simp only [smul_smul]
  rw [h4] at h2
  have h5 : ∫ x in (0 : ℝ)..(2 * Real.pi), ee (-k) x • deriv f x =
      (Complex.I * k) • ∫ x in (0 : ℝ)..(2 * Real.pi), ee (-k) x • f x := by
    have h6 := eq_neg_of_add_eq_zero_right h2
    rw [h6, ← neg_smul]
    congr 1
    push_cast
    ring
  rw [coef, h5, coef, smul_comm]

/-- Differentiation in `t` under the integral sign. -/
private theorem hasDerivAt_coef {f : ℝ → ℝ → Z} (hf : ContDiff ℝ 1 fun p : ℝ × ℝ => f p.1 p.2)
    (k : ℤ) (t : ℝ) :
    HasDerivAt (fun s => coef k (f s)) (coef k fun x => deriv (fun s => f s x) t) t := by
  set F : ℝ × ℝ → Z := fun p => f p.1 p.2 with hF
  have hdiff : Differentiable ℝ F := hf.differentiable one_ne_zero
  have hD : Continuous fun p : ℝ × ℝ => fderiv ℝ F p ((1 : ℝ), (0 : ℝ)) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hd : ∀ s x, HasDerivAt (fun s => f s x) (fderiv ℝ F (s, x) ((1 : ℝ), (0 : ℝ))) s := by
    intro s x
    have h1 : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : ℝ)) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
    exact (hdiff (s, x)).hasFDerivAt.comp_hasDerivAt s h1
  have hD' : ∀ s x, deriv (fun s => f s x) s = fderiv ℝ F (s, x) ((1 : ℝ), (0 : ℝ)) :=
    fun s x => (hd s x).deriv
  -- a uniform bound
  have hK : IsCompact (Icc (t - 1) (t + 1) ×ˢ Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (f := fun p : ℝ × ℝ => ee (-k) p.2 • fderiv ℝ F p ((1 : ℝ), (0 : ℝ)))
    (((continuous_ee (-k)).comp continuous_snd).smul hD).continuousOn
  have hcx : ∀ s, Continuous (f s) := fun s =>
    hf.continuous.comp (Continuous.prodMk continuous_const continuous_id)
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => ee (-k) x • f s x)
    (F' := fun s x => ee (-k) x • fderiv ℝ F (s, x) ((1 : ℝ), (0 : ℝ)))
    (μ := MeasureTheory.volume) (a := 0) (b := 2 * Real.pi) (x₀ := t) (bound := fun _ => C)
    (s := Icc (t - 1) (t + 1)) (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s => ((continuous_ee (-k)).smul (hcx s)).aestronglyMeasurable)
    (((continuous_ee (-k)).smul (hcx t)).intervalIntegrable _ _)
    (((continuous_ee (-k)).smul
      (hD.comp (Continuous.prodMk continuous_const continuous_id))).aestronglyMeasurable)
    (Eventually.of_forall fun x hx s hs => hC (s, x) ⟨hs, by
      rw [uIoc_of_le (by positivity)] at hx
      exact ⟨hx.1.le, hx.2⟩⟩)
    (intervalIntegrable_const)
    (Eventually.of_forall fun x _ s _ => (hd s x).const_smul (ee (-k) x))
  have h1 := hmain.2.const_smul (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  have h2 : (fun x => deriv (fun s => f s x) t) =
      fun x => fderiv ℝ F (t, x) ((1 : ℝ), (0 : ℝ)) := funext fun x => hD' t x
  rw [h2]
  exact h1

/-- For a solution of `∂ₜ u = B ∂ₓ u + C u` with `2π`-periodic data the Fourier modes decouple:
`∂ₜ û_k = (i k B + C) û_k`. -/
private theorem mode_ode {B C : Z →L[ℂ] Z} {u : ℝ → ℝ → Z}
    (hu : ContDiff ℝ 1 fun p : ℝ × ℝ => u p.1 p.2)
    (hp : ∀ t, Function.Periodic (u t) (2 * Real.pi))
    (heq : ∀ t, 0 ≤ t → ∀ x, deriv (fun s => u s x) t = B (deriv (u t) x) + C (u t x))
    (k : ℤ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => coef k (u s)) (((Complex.I * k) • B + C) (coef k (u t))) t := by
  have hslice : ∀ t, ContDiff ℝ 1 (u t) := fun t =>
    hu.comp (ContDiff.prodMk contDiff_const contDiff_id)
  have hc : ∀ t, Continuous (u t) := fun t => (hslice t).continuous
  have h1 := hasDerivAt_coef hu k t
  have h2 : (fun x => deriv (fun s => u s x) t) = fun x => B (deriv (u t) x) + C (u t x) :=
    funext (heq t ht)
  have h3 : coef k (fun x => deriv (fun s => u s x) t) =
      ((Complex.I * k) • B + C) (coef k (u t)) := by
    rw [h2, coef_add (f := fun x => B (deriv (u t) x)) (f' := fun x => C (u t x))
      (B.continuous.comp ((hslice t).continuous_deriv le_rfl))
      (C.continuous.comp (hc t)), coef_clm B ((hslice t).continuous_deriv le_rfl),
      coef_clm C (hc t), coef_deriv (hslice t) (hp t), map_smul]
    simp
  rwa [h3] at h1

/-- A mode that vanishes initially vanishes for all `t ≥ 0`. -/
private theorem coef_eq_zero {B C : Z →L[ℂ] Z} {u : ℝ → ℝ → Z}
    (hu : ContDiff ℝ 1 fun p : ℝ × ℝ => u p.1 p.2)
    (hp : ∀ t, Function.Periodic (u t) (2 * Real.pi))
    (heq : ∀ t, 0 ≤ t → ∀ x, deriv (fun s => u s x) t = B (deriv (u t) x) + C (u t x))
    {k : ℤ} (h0 : coef k (u 0) = 0) {t : ℝ} (ht : 0 ≤ t) : coef k (u t) = 0 := by
  set A : Z →L[ℂ] Z := (Complex.I * k) • B + C with hA
  have hode : ∀ t, 0 ≤ t → HasDerivAt (fun s => coef k (u s)) (A (coef k (u t))) t :=
    fun t ht => mode_ode hu hp heq k ht
  have hunique := ODE_solution_unique_of_mem_Icc_right
    (v := fun _ y => A y) (s := fun _ => univ) (K := ‖(A.restrictScalars ℝ)‖₊)
    (f := fun s => coef k (u s)) (g := fun _ => 0) (a := 0) (b := t + 1)
    (fun _ _ => ((A.restrictScalars ℝ).lipschitzWith).lipschitzOnWith)
    (fun s hs => (hode s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hode s hs.1).hasDerivWithinAt) (fun _ _ => mem_univ _)
    continuousOn_const (fun s _ => by simpa using (hasDerivWithinAt_const s (Ici s) (0 : Z)))
    (fun _ _ => mem_univ _) h0
  exact hunique ⟨ht, by linarith⟩

private theorem fourier_eq_ee (k : ℤ) (x : ℝ) :
    (fourier k (x : AddCircle (2 * Real.pi)) : ℂ) = ee k x := by
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  rw [fourier_coe_apply, ee]
  congr 1
  push_cast
  rw [div_eq_iff hπ]
  ring

/-- A continuous periodic function with finitely many Fourier modes is a trigonometric
polynomial. -/
private theorem eq_sum_of_coef_scalar {f : ℝ → ℂ} (hc : Continuous f)
    (hp : Function.Periodic f (2 * Real.pi)) (s : Finset ℤ) (h : ∀ k, k ∉ s → coef k f = 0)
    (x : ℝ) : f x = ∑ k ∈ s, ee k x * coef k f := by
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let F : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨hp.lift, by
      refine (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 ?_
      exact hc⟩
  have hcoef : ∀ k, fourierCoeff F k = coef k f := fun k => by
    rw [fourierCoeff_eq_intervalIntegral F k 0, zero_add, coef]
    have h1 : ∀ y : ℝ, (fourier (-k) (y : AddCircle (2 * Real.pi)) : ℂ) • F (y : AddCircle _) =
        ee (-k) y • f y := fun y => by
      have h2 : F (y : AddCircle (2 * Real.pi)) = f y := rfl
      rw [h2, fourier_eq_ee]
    simp only [h1]
    rw [Complex.real_smul, smul_eq_mul, one_div]
    push_cast
    rfl
  have hs : HasSum (fun k => fourierCoeff F k • fourier k (x : AddCircle (2 * Real.pi)))
      (∑ k ∈ s, fourierCoeff F k • fourier k (x : AddCircle (2 * Real.pi))) :=
    hasSum_sum_of_ne_finset_zero fun k hk => by rw [hcoef, h k hk, zero_smul]
  have hsum : Summable (fourierCoeff F) :=
    summable_of_ne_finset_zero (s := s) fun k hk => by rw [hcoef, h k hk]
  have h2 := has_pointwise_sum_fourier_series_of_summable hsum (x : AddCircle (2 * Real.pi))
  have h3 := h2.unique hs
  have h4 : F (x : AddCircle (2 * Real.pi)) = f x := rfl
  rw [h4] at h3
  rw [h3]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hcoef, fourier_eq_ee, smul_eq_mul, mul_comm]

/-- The same, for functions with values in a Banach space. -/
private theorem eq_sum_of_coef {f : ℝ → Z} (hc : Continuous f) (hp : Function.Periodic f (2 *
    Real.pi))
    (s : Finset ℤ) (h : ∀ k, k ∉ s → coef k f = 0) (x : ℝ) :
    f x = ∑ k ∈ s, ee k x • coef k f := by
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)]
  intro φ
  have h1 := eq_sum_of_coef_scalar (f := fun y => φ (f y)) (φ.continuous.comp hc)
    (fun y => by simp only [hp y]) s (fun k hk => by rw [coef_clm φ hc, h k hk, map_zero]) x
  rw [h1, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coef_clm φ hc, map_smul, smul_eq_mul]

/-- The Fourier coefficients of a trigonometric polynomial. -/
private theorem coef_sum (s : Finset ℤ) (b : ℤ → Z) {j : ℤ} (hj : j ∉ s) :
    coef j (fun x => ∑ k ∈ s, ee k x • b k) = 0 := by
  have h1 : ∀ k ∈ s, ∫ x in (0 : ℝ)..(2 * Real.pi), ee (-j) x • (ee k x • b k) = 0 := by
    intro k hk
    have hne : k - j ≠ 0 := fun h => hj (by rwa [← sub_eq_zero.1 h])
    have hc : Complex.I * ((k - j : ℤ) : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hne)
    simp only [smul_smul, ee_mul_ee]
    rw [intervalIntegral.integral_smul_const]
    have h2 : ∫ x in (0 : ℝ)..(2 * Real.pi), ee (-j + k) x = 0 := by
      have h3 : (fun x : ℝ => ee (-j + k) x) =
          fun x : ℝ => Complex.exp ((Complex.I * ((k - j : ℤ) : ℂ)) * x) := by
        funext x
        rw [ee]
        congr 2
        push_cast
        ring
      rw [h3, integral_exp_mul_complex hc]
      have h4 : Complex.exp ((Complex.I * ((k - j : ℤ) : ℂ)) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
        rw [← Complex.exp_int_mul_two_pi_mul_I (k - j)]
        congr 1
        push_cast
        ring
      rw [h4]
      simp
    rw [h2, zero_smul]
  simp only [coef, Finset.smul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.sum_eq_zero h1, smul_zero]
  · intro k _
    exact ((continuous_ee (-j)).smul
      ((continuous_ee k).smul continuous_const)).intervalIntegrable _ _

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

/-- A classical solution, for `t ≥ 0`, of the slab system (4.1) with constant `σ^S` and
`σ^A = G = 0`, `2π`-periodic in `x`.  The velocity space is a complex Banach space `H`, for instance
`L²(-1, 1)` or a space of nodal values; `M` is multiplication by `v`, `avg` is `⟨·⟩ᵥ` and `e` is the
constant function `1`.  The functions are complex valued, as for the Fourier modes of the paper, and
real solutions are a special case.  They are given on all of `ℝ × ℝ`, which just asks that the
solution is `C¹` up to `t = 0`. -/
structure IsSlabSolution (M : H →L[ℂ] H) (avg : H →L[ℂ] ℂ) (e : H) (ε σ : ℝ)
    (ρ : ℝ → ℝ → ℂ) (g : ℝ → ℝ → H) : Prop where
  ρ_diff : ContDiff ℝ 1 fun p : ℝ × ℝ => ρ p.1 p.2
  g_diff : ContDiff ℝ 1 fun p : ℝ × ℝ => g p.1 p.2
  ρ_per : ∀ t, Function.Periodic (ρ t) (2 * Real.pi)
  g_per : ∀ t, Function.Periodic (g t) (2 * Real.pi)
  eq_ρ : ∀ t, 0 ≤ t → ∀ x, deriv (fun s => ρ s x) t = -(1 / 2) * avg (M (deriv (g t) x))
  eq_g : ∀ t, 0 ≤ t → ∀ x, deriv (fun s => g s x) t =
    -(((ε : ℂ)⁻¹) • (M (deriv (g t) x) - ((1 / 2 : ℂ) * avg (M (deriv (g t) x))) • e)) -
      (((ε : ℂ) ^ 2)⁻¹) • (deriv (ρ t) x • M e) - ((σ : ℂ) / (ε : ℂ) ^ 2) • g t x

/-- The coefficient of `∂ₓ` in (4.1), for `u = (ρ, g)`. -/
noncomputable def slabB (M : H →L[ℂ] H) (avg : H →L[ℂ] ℂ) (e : H) (ε : ℝ) :
    ℂ × H →L[ℂ] ℂ × H :=
  ((-(1 / 2 : ℂ)) • (avg.comp M).comp (ContinuousLinearMap.snd ℂ ℂ H)).prod
    (-(((ε : ℂ)⁻¹) • (M.comp (ContinuousLinearMap.snd ℂ ℂ H) -
        (1 / 2 : ℂ) • ((avg.comp M).comp (ContinuousLinearMap.snd ℂ ℂ H)).smulRight e)) -
      (((ε : ℂ) ^ 2)⁻¹) • (ContinuousLinearMap.fst ℂ ℂ H).smulRight (M e))

/-- The zeroth order coefficient of (4.1), for `u = (ρ, g)`. -/
noncomputable def slabC (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H] (ε σ : ℝ) :
    ℂ × H →L[ℂ] ℂ × H :=
  (0 : ℂ × H →L[ℂ] ℂ).prod (-(((σ : ℂ) / (ε : ℂ) ^ 2) • ContinuousLinearMap.snd ℂ ℂ H))

section Slab

variable {M : H →L[ℂ] H} {avg : H →L[ℂ] ℂ} {e : H} {ε σ : ℝ} {ρ : ℝ → ℝ → ℂ} {g : ℝ → ℝ → H}

private theorem slabB_apply (r : ℂ) (h : H) : slabB M avg e ε (r, h) =
    (-(1 / 2) * avg (M h), -(((ε : ℂ)⁻¹) • (M h - ((1 / 2 : ℂ) * avg (M h)) • e)) -
      (((ε : ℂ) ^ 2)⁻¹) • (r • M e)) := by
  simp [slabB, smul_smul]

private theorem slabC_apply (r : ℂ) (h : H) : slabC H ε σ (r, h) =
    (0, -(((σ : ℂ) / (ε : ℂ) ^ 2) • h)) := by
  simp [slabC]

namespace IsSlabSolution

variable (hs : IsSlabSolution M avg e ε σ ρ g)
include hs

private theorem pair_diff : ContDiff ℝ 1 fun p : ℝ × ℝ => (ρ p.1 p.2, g p.1 p.2) :=
  hs.ρ_diff.prodMk hs.g_diff

private theorem pair_per (t : ℝ) : Function.Periodic (fun x => (ρ t x, g t x)) (2 * Real.pi) := fun
    x => by
  simp only [hs.ρ_per t x, hs.g_per t x]

private theorem ρ_slice (t : ℝ) : ContDiff ℝ 1 (ρ t) :=
  hs.ρ_diff.comp (ContDiff.prodMk contDiff_const contDiff_id)

private theorem g_slice (t : ℝ) : ContDiff ℝ 1 (g t) :=
  hs.g_diff.comp (ContDiff.prodMk contDiff_const contDiff_id)

/-- The system (4.1) in the form `∂ₜ u = B ∂ₓ u + C u`. -/
private theorem pair_eq (t : ℝ) (ht : 0 ≤ t) (x : ℝ) :
    deriv (fun s => (ρ s x, g s x)) t =
      slabB M avg e ε (deriv (fun y => (ρ t y, g t y)) x) + slabC H ε σ (ρ t x, g t x) := by
  have h1 : HasDerivAt (fun s => (ρ s x, g s x))
      (deriv (fun s => ρ s x) t, deriv (fun s => g s x) t) t := by
    have hd1 : DifferentiableAt ℝ (fun s => ρ s x) t :=
      (hs.ρ_diff.comp (ContDiff.prodMk contDiff_id contDiff_const)).differentiable one_ne_zero t
    have hd2 : DifferentiableAt ℝ (fun s => g s x) t :=
      (hs.g_diff.comp (ContDiff.prodMk contDiff_id contDiff_const)).differentiable one_ne_zero t
    exact hd1.hasDerivAt.prodMk hd2.hasDerivAt
  have h2 : HasDerivAt (fun y => (ρ t y, g t y)) (deriv (ρ t) x, deriv (g t) x) x :=
    (((hs.ρ_slice t).differentiable one_ne_zero x).hasDerivAt).prodMk
      (((hs.g_slice t).differentiable one_ne_zero x).hasDerivAt)
  rw [h1.deriv, h2.deriv, slabB_apply, slabC_apply, hs.eq_ρ t ht x, hs.eq_g t ht x]
  simp only [Prod.mk_add_mk, add_zero]
  congr 1
  abel

private theorem coef_fst (t : ℝ) (k : ℤ) :
    (coef k fun x => (ρ t x, g t x)).1 = coef k (ρ t) := by
  have h := coef_clm (ContinuousLinearMap.fst ℂ ℂ H) (hs.pair_diff.comp
    (ContDiff.prodMk contDiff_const contDiff_id)).continuous k (f := fun x => (ρ t x, g t x))
  exact h.symm

private theorem coef_snd (t : ℝ) (k : ℤ) :
    (coef k fun x => (ρ t x, g t x)).2 = coef k (g t) := by
  have h := coef_clm (ContinuousLinearMap.snd ℂ ℂ H) (hs.pair_diff.comp
    (ContDiff.prodMk contDiff_const contDiff_id)).continuous k (f := fun x => (ρ t x, g t x))
  exact h.symm

end IsSlabSolution

/-- **arXiv 2005.06571, (4.4).**  For constant `σ^S` the Fourier modes of a solution of (4.1)
decouple. -/
theorem sec_4_mode_ode (hs : IsSlabSolution M avg e ε σ ρ g) (k : ℤ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => coef k (ρ s))
      (-(1 / 2) * (Complex.I * k) * avg (M (coef k (g t)))) t ∧
    HasDerivAt (fun s => coef k (g s))
      (-(((ε : ℂ)⁻¹) • ((Complex.I * k) • (M (coef k (g t)) -
          ((1 / 2 : ℂ) * avg (M (coef k (g t)))) • e))) -
        (((ε : ℂ) ^ 2)⁻¹) • ((Complex.I * k) • (coef k (ρ t) • M e)) -
        ((σ : ℂ) / (ε : ℂ) ^ 2) • coef k (g t)) t := by
  have h := mode_ode (u := fun t x => (ρ t x, g t x)) hs.pair_diff hs.pair_per hs.pair_eq k ht
  have h1 := (ContinuousLinearMap.fst ℝ ℂ H).hasFDerivAt.comp_hasDerivAt t h
  have h2 := (ContinuousLinearMap.snd ℝ ℂ H).hasFDerivAt.comp_hasDerivAt t h
  have hy : (coef k fun x => (ρ t x, g t x)) = (coef k (ρ t), coef k (g t)) :=
    Prod.ext (hs.coef_fst t k) (hs.coef_snd t k)
  simp only [_root_.add_apply, _root_.smul_apply, hy, slabB_apply, slabC_apply] at h1 h2
  constructor
  · refine (h1.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    · simp only [Prod.smul_mk, Prod.mk_add_mk, ContinuousLinearMap.coe_fst', smul_eq_mul, add_zero]
      ring
    · exact (hs.coef_fst s k).symm
  · refine (h2.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    · simp only [Prod.smul_mk, Prod.mk_add_mk, ContinuousLinearMap.coe_snd', smul_sub, smul_neg,
        smul_comm (Complex.I * (k : ℂ))]
      abel
    · exact (hs.coef_snd s k).symm

/-- **arXiv 2005.06571, Sec. 4, (4.5).**  Band-limited data stay band-limited: if at `t = 0` the
functions `ρ` and `g` are trigonometric polynomials of degree `≤ m₀` in `x`, so are `ρ t` and `g t`
for all `t ≥ 0`, with coefficients the Fourier coefficients of the solution.

The paper argues on the mode system (4.4); here the statement is for a classical solution of (4.1),
and (4.4) is derived (`sec_4_mode_ode`), with values in any Banach space of velocity functions. -/
theorem sec_4_band_limited (hs : IsSlabSolution M avg e ε σ ρ g) {m₀ : ℕ} (a : ℤ → ℂ) (b : ℤ → H)
    (hρ₀ : ∀ x, ρ 0 x = ∑ k ∈ Finset.Icc (-(m₀ : ℤ)) m₀, ee k x • a k)
    (hg₀ : ∀ x, g 0 x = ∑ k ∈ Finset.Icc (-(m₀ : ℤ)) m₀, ee k x • b k) {t : ℝ} (ht : 0 ≤ t)
    (x : ℝ) : ρ t x = ∑ k ∈ Finset.Icc (-(m₀ : ℤ)) m₀, ee k x * coef k (ρ t) ∧
      g t x = ∑ k ∈ Finset.Icc (-(m₀ : ℤ)) m₀, ee k x • coef k (g t) := by
  set s := Finset.Icc (-(m₀ : ℤ)) m₀ with hsdef
  have hzero : ∀ k, k ∉ s → coef k (fun x => (ρ t x, g t x)) = 0 := by
    intro k hk
    refine coef_eq_zero (u := fun t x => (ρ t x, g t x)) hs.pair_diff hs.pair_per hs.pair_eq ?_ ht
    refine Prod.ext ?_ ?_
    · rw [hs.coef_fst 0 k, Prod.fst_zero, funext hρ₀]
      exact coef_sum s a hk
    · rw [hs.coef_snd 0 k, Prod.snd_zero, funext hg₀]
      exact coef_sum s b hk
  have h1 := eq_sum_of_coef_scalar (hs.ρ_slice t).continuous (hs.ρ_per t) s
    (fun k hk => by rw [← hs.coef_fst t k, hzero k hk, Prod.fst_zero]) x
  have h2 := eq_sum_of_coef (hs.g_slice t).continuous (hs.g_per t) s
    (fun k hk => by rw [← hs.coef_snd t k, hzero k hk, Prod.snd_zero]) x
  exact ⟨h1, h2⟩

/-- **arXiv 2005.06571, Sec. 4.**  The solution stays low rank: `g(t, x, ·)` lies, for all `x`, in a
fixed space of velocity functions of dimension at most the number `2 m₀ + 1` of active modes. -/
theorem sec_4_rank_le (hs : IsSlabSolution M avg e ε σ ρ g) {m₀ : ℕ} (a : ℤ → ℂ) (b : ℤ → H)
    (hρ₀ : ∀ x, ρ 0 x = ∑ k ∈ Finset.Icc (-(m₀ : ℤ)) m₀, ee k x • a k)
    (hg₀ : ∀ x, g 0 x = ∑ k ∈ Finset.Icc (-(m₀ : ℤ)) m₀, ee k x • b k) {t : ℝ} (ht : 0 ≤ t) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (g t))) ≤ 2 * m₀ + 1 := by
  classical
  set s := Finset.Icc (-(m₀ : ℤ)) m₀ with hsdef
  set c : Finset H := s.image fun k => coef k (g t) with hc
  have h1 : Submodule.span ℂ (Set.range (g t)) ≤ Submodule.span ℂ (c : Set H) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, rfl⟩
    rw [(sec_4_band_limited hs a b hρ₀ hg₀ ht x).2]
    refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hk)
  have h2 := Submodule.finrank_mono h1
  have h3 : Module.finrank ℂ (Submodule.span ℂ (c : Set H)) ≤ c.card :=
    finrank_span_finset_le_card c
  have h4 : c.card ≤ s.card := Finset.card_image_le
  have h5 : s.card = 2 * m₀ + 1 := by
    rw [hsdef, Int.card_Icc]
    omega
  omega

/-- arXiv 2005.06571, Sec. 4.  **The system (4.1) has solutions**, for all data of plane wave form:
every mode evolves by the exponential of the bounded generator of (4.4).  Sums of such waves are
the band-limited solutions
of `sec_4_band_limited`. -/
theorem exists_plane_wave (M : H →L[ℂ] H) (avg : H →L[ℂ] ℂ) (e : H) (ε σ : ℝ) (k : ℤ) (r₀ : ℂ)
    (h₀ : H) : ∃ (ρ : ℝ → ℝ → ℂ) (g : ℝ → ℝ → H), IsSlabSolution M avg e ε σ ρ g ∧
      (∀ x, ρ 0 x = ee k x * r₀) ∧ ∀ x, g 0 x = ee k x • h₀ := by
  set A : ℂ × H →L[ℂ] ℂ × H := (Complex.I * k) • slabB M avg e ε + slabC H ε σ with hA
  let y : ℝ → ℂ × H := fun t => (NormedSpace.exp ((t : ℂ) • A)) (r₀, h₀)
  have hy : ∀ t, HasDerivAt y (A (y t)) t := by
    intro t
    have h1 := hasDerivAt_exp_smul_const' A (t : ℂ)
    have h2 := (ContinuousLinearMap.apply ℂ (ℂ × H) ((r₀, h₀) : ℂ × H)).hasFDerivAt.comp_hasDerivAt
      _ h1
    have h3 := HasDerivAt.scomp (h := Complex.ofRealCLM) t h2
      (Complex.ofRealCLM.hasDerivAt (x := t))
    refine h3.congr_deriv ?_
    rw [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul]
    rfl
  have hyd : Differentiable ℝ y := fun t => (hy t).differentiableAt
  have hyc : Continuous y := hyd.continuous
  have hyC : ContDiff ℝ 1 y := contDiff_one_iff_deriv.2 ⟨hyd, by
    rw [funext fun t => (hy t).deriv]
    exact A.continuous.comp hyc⟩
  have heC : ContDiff ℝ 1 (ee k) := contDiff_one_iff_deriv.2
    ⟨fun x => (hasDerivAt_ee k x).differentiableAt, by
      rw [funext fun x => (hasDerivAt_ee k x).deriv]
      exact continuous_const.mul (continuous_ee k)⟩
  have hy1 : ∀ t, HasDerivAt (fun s => (y s).1) (A (y t)).1 t := fun t =>
    (ContinuousLinearMap.fst ℝ ℂ H).hasFDerivAt.comp_hasDerivAt t (hy t)
  have hy2 : ∀ t, HasDerivAt (fun s => (y s).2) (A (y t)).2 t := fun t =>
    (ContinuousLinearMap.snd ℝ ℂ H).hasFDerivAt.comp_hasDerivAt t (hy t)
  have hA1 : ∀ z : ℂ × H, (A z).1 = (Complex.I * k) * (-(1 / 2) * avg (M z.2)) := by
    rintro ⟨r, h⟩
    simp [hA, slabB_apply, slabC_apply]
  have hA2 : ∀ z : ℂ × H, (A z).2 = (Complex.I * k) • (-(((ε : ℂ)⁻¹) • (M z.2 -
      ((1 / 2 : ℂ) * avg (M z.2)) • e)) - (((ε : ℂ) ^ 2)⁻¹) • (z.1 • M e)) +
      -(((σ : ℂ) / (ε : ℂ) ^ 2) • z.2) := by
    rintro ⟨r, h⟩
    simp [hA, slabB_apply, slabC_apply]
  have hy0 : y 0 = (r₀, h₀) := by simp [y]
  refine ⟨fun t x => ee k x * (y t).1, fun t x => ee k x • (y t).2,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (heC.comp contDiff_snd).mul ((contDiff_fst.comp hyC).comp contDiff_fst)
  · exact (isBoundedBilinearMap_smul (𝕜 := ℝ) (A := ℂ) (E := H)).contDiff.comp
      ((heC.comp contDiff_snd).prodMk ((contDiff_snd.comp hyC).comp contDiff_fst))
  · intro t x
    simp only [ee_periodic k x]
  · intro t x
    simp only [ee_periodic k x]
  · intro t _ x
    have h1 : deriv (fun s => ee k x * (y s).1) t = ee k x * (A (y t)).1 :=
      ((hy1 t).const_mul (ee k x)).deriv
    have h2 : deriv (fun x => ee k x • (y t).2) x = (Complex.I * k * ee k x) • (y t).2 :=
      ((hasDerivAt_ee k x).smul_const (y t).2).deriv
    rw [h1, h2, hA1, map_smul, map_smul, smul_eq_mul]
    ring
  · intro t _ x
    have h1 : deriv (fun s => ee k x • (y s).2) t = ee k x • (A (y t)).2 :=
      ((hy2 t).const_smul (ee k x)).deriv
    have h2 : deriv (fun x => ee k x • (y t).2) x = (Complex.I * k * ee k x) • (y t).2 :=
      ((hasDerivAt_ee k x).smul_const (y t).2).deriv
    have h3 : deriv (fun x => ee k x * (y t).1) x = (Complex.I * k * ee k x) * (y t).1 :=
      ((hasDerivAt_ee k x).mul_const (y t).1).deriv
    rw [h1, h2, h3, hA2]
    simp only [map_smul, smul_eq_mul]
    module
  · intro x
    change ee k x * (y 0).1 = _
    rw [hy0]
  · intro x
    change ee k x • (y 0).2 = _
    rw [hy0]

end Slab

end Fourier

end LeanDLRA.Literature.P2005_06571
