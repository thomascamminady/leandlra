import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.ProjectorSplitting

/-!
# Hyper-reduced, surrogate and frozen-coupling vector fields

The robust error bounds of the BUG and projector-splitting (KSL) integrators assume that every
substep is driven by the exact vector field `F`.  In practice `F` is replaced by something
cheaper.  This file shows that each such perturbation enters the robust bounds **additively**,
with constants that depend only on `L`, `B`, `T` (and the perturbation constants), never on
singular values.

## (a) Hyper-reduced BUG (OP-RS-03)

All three substeps of a BUG step are driven by a *computed* field `G` (DEIM/EIM/CUR, separable
or Karhunen–Loève approximation of a potential, ...) with `‖G(t, Y) - F(t, Y)‖ ≤ δ` **along the
three substep trajectories only**.  No Lipschitz, continuity or boundedness assumption is made
on `G` (so DEIM index switching is allowed); only the exact field `F` is `L`-Lipschitz and
`B`-bounded.  The normal-component assumption is made for `F`.  Instance: the DLRA-DEIM-FS
scheme of [GhahremaniBabaee2024], eqs. (17a)–(17b), where `G` is the DEIM fibre-sampled `F`.

* `hyper_kstep_capture`: `‖(1 - P₁) A(t₁)‖ ≤ θ`, `θ = h (4 L (B + δ) h + (ε + δ))`;
* `hyper_galerkin_step_error`: `‖YS t₁ - A t₁‖ ≤ (e^{Lh} - 1)(B h + θ') + θ' + h e^{Lh} δ`;
* `IsHyperBUGStep.local_error`, `IsHyperBUGStep.local_error_le`:
  `‖Y₁ - A t₁‖ ≤ h (c₁ (ε + δ) + c₂(B + δ) h + e^{L H} δ)` with the BUG constants
  `c₁ = bugC₁ L H`, `c₂(B) = bugC₂ L B H`;
* `hyper_bug_global_error_le`: `‖Yₙ - A tₙ‖ ≤ c₀ δ₀ + T e^{LT} (c₁ (ε + δ) + c₂(B + δ) h
  + e^{L H} δ)`, i.e. the form `c₀ δ₀ + c₁ ε + c₂ h + c₃ δ` asked for in OP-RS-03 (here `c₂` is
  evaluated at `B + δ`; it is monotone in `δ`, so the constants are uniform for `δ ≤ δ_max`).
  In particular the total error saturates at the DLRA error once `δ ≲ ε + h`.

This is new: [GhahremaniBabaee2024] states (17a)–(17b) without an error analysis of the
hyper-reduced BUG step, and the KSL analogue in this library (`ksl_local_error_inexact`) needs the
substep *solutions* to be close, not just the fields. (Hyper-reduced KSL is covered by composing
`substep_error_of_defect`, which turns a `δ`-accurate field into a substep error `h e^{Lh} δ`, with
`ksl_global_error_inexact`; that route additionally takes the exact `F`-substep flows from the same
starting points as hypotheses and is not packaged as a single theorem here.) The proof needs two new
ingredients: a capture lemma whose K-step trajectory has speed `B + δ` and an extra defect term
`(1 - P₁) Q₀ (F - G)(YK)`, and a Galerkin comparison whose numerical trajectory carries the defect
`δ`. The Lipschitz constant of `G` never enters.
* `hyper_dlra_norm_sub_le` (continuous DLRA `Y' = P(t) G(t, Y)`):
  `‖Y t - A t‖ ≤ gronwallBound δ₀ L (ε + δ) (t - a)`.

What remains of OP-RS-03: the rank-adaptive BUG variant and the a-priori size of
`δ` from DEIM/CUR bounds (the pointwise `δ` is a hypothesis here).  The substep trajectories
are assumed to exist as classical `ODESolution`s (continuous, with right derivative equal to the
projected `G` at every time).  This covers index switching at isolated times (piecewise smooth
trajectories), but not Filippov / sliding-mode solutions of a discontinuous `G`, which would need
an a.e. differential-inclusion version of the Grönwall comparison.

## (b) Surrogate models (OP-OT-07)

If the model `F` is replaced by `F̃` with `‖F(t, A) - F̃(t, A)‖ ≤ η` along the true solution and
`F̃` is `L`-Lipschitz, then

* `surrogate_norm_sub_le`: the exact surrogate solution satisfies
  `‖Ã t - A t‖ ≤ gronwallBound δ₀ L η (t - a)`;
* `surrogate_dlra_norm_sub_le`: continuous DLRA for `F̃` with normal component `ε` satisfies
  `‖Y t - A t‖ ≤ gronwallBound δ₀ L (ε + η) (t - a) ≤ e^{L(t-a)} (δ₀ + (ε + η)(t - a))`;
* `surrogate_bug_global_error_le`, `surrogate_ksl_global_error_le`: the BUG / KSL integrator
  run on `F̃` has global error `c₀ δ₀ + c₁ ε + c₂ h + T e^{LT} η`.

Only `F̃` needs to be Lipschitz; `F` is only assumed to have a solution.  This settles the
abstract part of OP-OT-07 (the papers neither state nor prove it).  Not addressed: decay rates
of the separation error `η_R` (approximation theory) and singular Coulomb potentials.

## (c) Frozen coupling over one step (OP-OT-04)

`F(t, Y) = G(t, Y, E(Y))` with `G` `L_G`-Lipschitz in the coupling argument and `E`
`L_E`-Lipschitz; the frozen field is `F̃(t, Y) = G(t, Y, E(Y₀))`.

* `frozen_local_error`: if `F` is `L`-Lipschitz and `F̃` is `B`-bounded, the frozen and the true
  flows from `Y₀` satisfy `‖Φ̃_h(Y₀) - Φ_h(Y₀)‖ ≤ L_G L_E B h² e^{L h}`.

This proves the `O(h²)` local estimate of OP-OT-04, which underlies the first-order claim of
[UschmajewZeiser2024, Sec. 2.5] (electric field held constant over a Lie-splitting step). The proof
uses the constant defect `L_G L_E B h` instead of the time-dependent defect `L_G L_E B (t - t₀)`.
That avoids an integral Grönwall form and costs only a factor 2 in the constant. The Bogoliubov
scheme of [LeHenaffLubichPickl2026, Sec. 4.2] (keep `χ₄, …, χ₂ₙ` constant over a step, then rebuild
them from `χ₂` by tensorization) is the instance where `E` is the reconstruction map, if that map is
Lipschitz (a hypothesis here; the phase `θ₂ⱼ` of their eq. (10) must be part of a Lipschitz
reconstruction). The reference solution is then the "variational crime" system of their Sec. 2.2, in
which the tensorized functions are substituted continuously; the error of that system against the
exact many-body dynamics is not addressed. With exact integration of the frozen field (`g₀ = 0` in
`frozen_global_error_of_local`), the per-step `O(h²)` estimate gives first-order convergence of the
freeze-and-rebuild scheme to that reference.

## (d) Frozen coupling in robust integrators (OP-HO-04, global part of OP-OT-04)

* `frozen_global_error_of_local`: any integrator whose step `n` has a local error
  `≤ h g₀` with respect to the frozen flow of `F̃ₙ = G(·, ·, E(Yₙ))` has global error
  `≤ e^{LT} (δ₀ + T (g₀ + e^{L H} L_G L_E B h))`;
* `frozen_bug_global_error_le` (BUG) and `frozen_ksl_global_error_le` (KSL):
  `‖Yₙ - A tₙ‖ ≤ C (δ₀ + ε + h)`, with the constants explicit and depending only on
  `L, B, T, H, L_G L_E`.

This proves the claim of OP-HO-04 for the BUG integrator and the K–S–L ordering of the
projector-splitting integrator.  Other orderings follow from `frozen_global_error_of_local` once
their robust local error is certified.  The frozen *boundary data* variant (a time-dependent
source frozen over a step) and the `ε`-uniform stiff BGK version are not covered.
-/

open Set

namespace LeanDLRA.PerturbedField

open LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Auxiliary inequalities -/

section Aux

/-- Splitting of the Grönwall bound with a defect `L c + δ`:
`gronwallBound 0 L (L c + δ) x ≤ (e^{L x} - 1) c + x e^{L x} δ` for `L, δ ≥ 0`. -/
lemma gronwallBound_zero_add_le {L c δ x : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) :
    gronwallBound 0 L (L * c + δ) x ≤ (Real.exp (L * x) - 1) * c + x * Real.exp (L * x) * δ := by
  rcases hL.eq_or_lt with rfl | hL'
  · simp [gronwallBound_K0, mul_comm]
  · rw [gronwallBound_of_K_ne_0 hL'.ne']
    simp only [zero_mul, zero_add]
    have h1 := exp_sub_one_le_mul_exp (L * x)
    have hsplit : (L * c + δ) / L * (Real.exp (L * x) - 1)
        = (Real.exp (L * x) - 1) * c + δ * ((Real.exp (L * x) - 1) / L) := by
      field_simp
    have h2 : (Real.exp (L * x) - 1) / L ≤ x * Real.exp (L * x) := by
      rw [div_le_iff₀ hL']; nlinarith
    rw [hsplit]
    nlinarith

end Aux

/-! ### (a) The hyper-reduced BUG integrator (OP-RS-03) -/

section Hyper

variable {F G : ℝ → E → E} {L B ε δ : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

/-- **Speed lemma for a hyper-reduced substep.**  A trajectory of `y' = P G(t, y)` (`P` an
orthogonal projector) whose driving field is `δ`-close to a `B`-bounded field `F` along the
trajectory moves at most `(B + δ) (t - t₀)`.  No assumption on `G` off the trajectory. -/
lemma hyper_norm_sub_start_le {P : E →L[ℝ] E} (hP : IsOrthProj P) (hB : IsBoundedField F B)
    {y : ℝ → E} (hy : ODESolution (fun t x => P (G t x)) y t₀ t₁)
    (hδ : ∀ t ∈ Ico t₀ t₁, ‖G t (y t) - F t (y t)‖ ≤ δ) :
    ∀ t ∈ Icc t₀ t₁, ‖y t - y t₀‖ ≤ (B + δ) * (t - t₀) := by
  refine hy.norm_sub_le fun t ht => ?_
  have h1 : ‖G t (y t)‖ ≤ ‖F t (y t)‖ + ‖G t (y t) - F t (y t)‖ := by
    have := norm_add_le (F t (y t)) (G t (y t) - F t (y t))
    rwa [add_sub_cancel] at this
  have := hB t (y t)
  calc ‖P (G t (y t))‖ ≤ ‖G t (y t)‖ := hP.norm_le _
    _ ≤ B + δ := by linarith [hδ t ht]

/-- **K-step capture lemma for a hyper-reduced K-step** (new; the defect version of
`kstep_capture` asked for in OP-RS-03).  Let `F` be `L`-Lipschitz and `B`-bounded, `A` the exact
solution of `A' = F(t, A)` on `[t₀, t₁]`, `t₁ = t₀ + h`, and let the K-step be driven by a computed
field `G`: `YK' = Q₀ G(t, YK)`, `YK t₀ = A t₀`, with `‖G(t, YK t) - F(t, YK t)‖ ≤ δ` along `YK`.
If `P₁ (YK t₁) = YK t₁` and `‖(1 - P₁) ((1 - Q₀) F(t, YK t₁))‖ ≤ ε`, then

    ‖(1 - P₁) A(t₁)‖ ≤ h (4 L (B + δ) h + (ε + δ)).

(`g = (1 - P₁)(A - YK)` has `g' = (1 - P₁)(F(A) - Q₀ F(YK)) + (1 - P₁) Q₀ (F(YK) - G(YK))`; the
trajectories have speed `≤ B + δ`.)  `G` need not be Lipschitz or continuous. -/
theorem hyper_kstep_capture {P₁ Q₀ : E →L[ℝ] E} {YK : ℝ → E} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (hδ0 : 0 ≤ δ) (hP₁ : IsOrthProj P₁)
    (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hK : ODESolution (fun t x => Q₀ (G t x)) YK t₀ t₁) (hK₀ : YK t₀ = A t₀)
    (hKcap : P₁ (YK t₁) = YK t₁) (hδ : ∀ t ∈ Ico t₀ t₁, ‖G t (YK t) - F t (YK t)‖ ≤ δ)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε) :
    ‖(1 - P₁) (A t₁)‖ ≤ h * (4 * L * (B + δ) * h + (ε + δ)) := by
  have hle : t₀ ≤ t₁ := by linarith
  have hB0 := hB.nonneg
  set g : ℝ → E := fun t => (1 - P₁) (A t - YK t) with hg
  have hgc : ContinuousOn g (Icc t₀ t₁) :=
    (1 - P₁).continuous.comp_continuousOn (hA.cont.sub hK.cont)
  have hgd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt g ((1 - P₁) (F t (A t) - Q₀ (G t (YK t))))
      (Ici t) t := fun t ht =>
    (1 - P₁).hasFDerivAt.comp_hasDerivWithinAt t ((hA.deriv t ht).sub (hK.deriv t ht))
  have hspK := hyper_norm_sub_start_le hQ₀ hB hK hδ
  have hspA := hA.norm_sub_le_of_bounded hB
  have hbound : ∀ t ∈ Ico t₀ t₁, ‖(1 - P₁) (F t (A t) - Q₀ (G t (YK t)))‖
      ≤ 4 * L * (B + δ) * h + (ε + δ) := by
    intro t ht
    have htI := Ico_subset_Icc_self ht
    have ht₁I : t₁ ∈ Icc t₀ t₁ := ⟨hle, le_rfl⟩
    have hAt := hspA t htI
    have hKt := hspK t htI
    have hKt₁ := hspK t₁ ht₁I
    have hτ : t - t₀ ≤ h := by linarith [ht.2]
    have hτ0 : 0 ≤ t - t₀ := by linarith [ht.1]
    have hAt' : ‖A t - A t₀‖ ≤ B * h := hAt.trans (mul_le_mul_of_nonneg_left hτ hB0)
    have hKt' : ‖YK t - YK t₀‖ ≤ (B + δ) * h :=
      hKt.trans (mul_le_mul_of_nonneg_left hτ (by linarith))
    have hKt₁' : ‖YK t₁ - YK t₀‖ ≤ (B + δ) * h := by
      refine hKt₁.trans (le_of_eq ?_); rw [ht₁]; ring
    have hd1 : ‖A t - YK t‖ ≤ (2 * B + δ) * h := by
      have hdec : A t - YK t = (A t - A t₀) - (YK t - YK t₀) := by rw [hK₀]; abel
      rw [hdec]; refine (norm_sub_le _ _).trans ?_; linarith
    have hd2 : ‖A t - YK t₁‖ ≤ (2 * B + δ) * h := by
      have hdec : A t - YK t₁ = (A t - A t₀) - (YK t₁ - YK t₀) := by rw [hK₀]; abel
      rw [hdec]; refine (norm_sub_le _ _).trans ?_; linarith
    have hmain := norm_compl_sub_le_of_dist hF hL hP₁ hQ₀ t hd1 hd2 (hε t htI)
    have hsplit : (1 - P₁) (F t (A t) - Q₀ (G t (YK t))) =
        (1 - P₁) (F t (A t) - Q₀ (F t (YK t))) + (1 - P₁) (Q₀ (F t (YK t) - G t (YK t))) := by
      rw [← map_add]; congr 1; rw [map_sub]; abel
    have hdef : ‖(1 - P₁) (Q₀ (F t (YK t) - G t (YK t)))‖ ≤ δ :=
      calc _ ≤ ‖Q₀ (F t (YK t) - G t (YK t))‖ := hP₁.compl.norm_le _
        _ ≤ ‖F t (YK t) - G t (YK t)‖ := hQ₀.norm_le _
        _ ≤ δ := by rw [norm_sub_rev]; exact hδ t ht
    rw [hsplit]
    have hLδh : 0 ≤ L * δ * h := by positivity
    calc _ ≤ ‖(1 - P₁) (F t (A t) - Q₀ (F t (YK t)))‖
          + ‖(1 - P₁) (Q₀ (F t (YK t) - G t (YK t)))‖ := norm_add_le _ _
      _ ≤ L * ((2 * B + δ) * h) + L * ((2 * B + δ) * h) + ε + δ := by linarith
      _ ≤ 4 * L * (B + δ) * h + (ε + δ) := by nlinarith
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd hbound t₁ ⟨hle, le_rfl⟩
  have hg₀ : g t₀ = 0 := by simp [hg, hK₀]
  have hg₁ : g t₁ = (1 - P₁) (A t₁) := by
    simp only [hg, map_sub, sub_apply, one_apply_eq_self, hKcap, sub_self, sub_zero]
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [hg₀, hg₁, sub_zero, hlen] at hmvt
  rw [mul_comm h]
  exact hmvt

/-- **Error of a hyper-reduced Galerkin step** (new; defect version of
`galerkin_step_error`).  Let `R` be an orthogonal projector, `F` `L`-Lipschitz and `B`-bounded,
`A` the exact solution on `[t₀, t₁]`, and `YS' = R G(t, YS)`, `YS t₀ = R (A t₀)`, with
`‖G(t, YS t) - F(t, YS t)‖ ≤ δ` along `YS`.  If `‖A t₁ - R (A t₁)‖ ≤ θ`, then

    ‖YS t₁ - A t₁‖ ≤ (e^{L h} - 1) (B h + θ) + θ + h e^{L h} δ.

Only the Lipschitz constant of `F` enters (perturbed Grönwall with defect `δ`). -/
theorem hyper_galerkin_step_error {R : E →L[ℝ] E} (hR : IsOrthProj R)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hδ0 : 0 ≤ δ)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) {YS : ℝ → E}
    (hS : ODESolution (fun t x => R (G t x)) YS t₀ t₁) (hS₀ : YS t₀ = R (A t₀))
    (hδ : ∀ t ∈ Ico t₀ t₁, ‖G t (YS t) - F t (YS t)‖ ≤ δ) {θ : ℝ}
    (hθ : ‖A t₁ - R (A t₁)‖ ≤ θ) :
    ‖YS t₁ - A t₁‖ ≤
      (Real.exp (L * h) - 1) * (B * h + θ) + θ + h * Real.exp (L * h) * δ := by
  have hle : t₀ ≤ t₁ := by linarith
  have hfL : IsLipschitzField (fun t x => R (F t x)) L := hF.comp_contraction R hR.norm_le
  have hZc : ContinuousOn (fun t => R (A t)) (Icc t₀ t₁) :=
    R.continuous.comp_continuousOn hA.cont
  have hZd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => R (A t)) (R (F t (A t))) (Ici t) t :=
    fun t ht => R.hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht)
  have hdef : ∀ t ∈ Ico t₀ t₁, ‖R (F t (A t)) - R (F t (R (A t)))‖ ≤ L * (B * h + θ) := by
    intro t ht
    have hAt : ‖A t - R (A t)‖ ≤ B * h + θ := by
      have h1 := hA.norm_end_sub_le hB ht₁ t (Ico_subset_Icc_self ht)
      have hdec : A t - R (A t) = ((A t - A t₁) - R (A t - A t₁)) + (A t₁ - R (A t₁)) := by
        rw [map_sub]; abel
      rw [hdec]
      calc _ ≤ ‖(A t - A t₁) - R (A t - A t₁)‖ + ‖A t₁ - R (A t₁)‖ := norm_add_le _ _
        _ ≤ ‖A t - A t₁‖ + θ := add_le_add (hR.norm_sub_le _) hθ
        _ ≤ B * h + θ := by rw [norm_sub_rev]; linarith
    calc ‖R (F t (A t)) - R (F t (R (A t)))‖ ≤ L * ‖A t - R (A t)‖ := hfL t _ _
      _ ≤ L * (B * h + θ) := mul_le_mul_of_nonneg_left hAt hL
  have hdefS : ∀ t ∈ Ico t₀ t₁, ‖R (G t (YS t)) - R (F t (YS t))‖ ≤ δ := fun t ht => by
    rw [← map_sub]; exact (hR.norm_le _).trans (hδ t ht)
  have hgr := norm_sub_le_gronwallBound hfL hL (y := YS) (z := fun t => R (A t))
    (u := fun t => R (G t (YS t))) (w := fun t => R (F t (A t))) (ηy := δ)
    (ηz := L * (B * h + θ)) (δ := 0) hS.cont hS.deriv hdefS hZc hZd hdef
    (by simp [hS₀]) t₁ ⟨hle, le_rfl⟩
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [hlen, add_comm δ] at hgr
  have hgr' := hgr.trans (gronwallBound_zero_add_le hL hδ0)
  calc ‖YS t₁ - A t₁‖ ≤ ‖YS t₁ - R (A t₁)‖ + ‖R (A t₁) - A t₁‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
        rw [norm_sub_rev (R (A t₁))]
        linarith

/-- All hypotheses of one step of the **hyper-reduced BUG integrator**: as `IsBUGStep`, but the
K-, L- and S-substeps are driven by a computed field `G`, which is `δ`-close to `F` along the
three substep trajectories.  The normal-component bounds are for the exact field `F`.  No
regularity of `G` is assumed. -/
structure IsHyperBUGStep (F G : ℝ → E → E) (δ ε : ℝ) (P₀ Q₀ P₁ Q₁ : E →L[ℝ] E) (t₀ t₁ : ℝ)
    (Y₀ : E) (YK YL YS : ℝ → E) : Prop where
  projP₀ : IsOrthProj P₀
  projQ₀ : IsOrthProj Q₀
  projP₁ : IsOrthProj P₁
  projQ₁ : IsOrthProj Q₁
  comm₁ : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)
  /-- Hyper-reduced K-step `YK' = Q₀ G(t, YK)`. -/
  kSol : ODESolution (fun t x => Q₀ (G t x)) YK t₀ t₁
  kStart : YK t₀ = Y₀
  kCap : P₁ (YK t₁) = YK t₁
  kNormal : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε
  /-- The computed field is `δ`-accurate along the K-step trajectory. -/
  kDefect : ∀ t ∈ Ico t₀ t₁, ‖G t (YK t) - F t (YK t)‖ ≤ δ
  /-- Hyper-reduced L-step `YL' = P₀ G(t, YL)`. -/
  lSol : ODESolution (fun t x => P₀ (G t x)) YL t₀ t₁
  lStart : YL t₀ = Y₀
  lCap : Q₁ (YL t₁) = YL t₁
  lNormal : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε
  lDefect : ∀ t ∈ Ico t₀ t₁, ‖G t (YL t) - F t (YL t)‖ ≤ δ
  /-- Hyper-reduced Galerkin S-step `YS' = P₁ Q₁ G(t, YS)`. -/
  sSol : ODESolution (fun t x => P₁ (Q₁ (G t x))) YS t₀ t₁
  sStart : YS t₀ = P₁ (Q₁ Y₀)
  sDefect : ∀ t ∈ Ico t₀ t₁, ‖G t (YS t) - F t (YS t)‖ ≤ δ

/-- An exact BUG step is a hyper-reduced BUG step with `G = F`, `δ = 0`. -/
lemma IsBUGStep.isHyperBUGStep {ε : ℝ} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {Y₀ : E}
    {YK YL YS : ℝ → E} (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS) :
    IsHyperBUGStep F F 0 ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS where
  projP₀ := hs.projP₀
  projQ₀ := hs.projQ₀
  projP₁ := hs.projP₁
  projQ₁ := hs.projQ₁
  comm₁ := hs.comm₁
  kSol := hs.kSol
  kStart := hs.kStart
  kCap := hs.kCap
  kNormal := hs.kNormal
  kDefect _ _ := by simp
  lSol := hs.lSol
  lStart := hs.lStart
  lCap := hs.lCap
  lNormal := hs.lNormal
  lDefect _ _ := by simp
  sSol := hs.sSol
  sStart := hs.sStart
  sDefect _ _ := by simp

namespace IsHyperBUGStep

variable {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {Y₀ : E} {YK YL YS : ℝ → E}

/-- **Capture by the new bases of a hyper-reduced BUG step**:
`‖A t₁ - P₁ Q₁ A t₁‖ ≤ 2 h (4 L (B + δ) h + (ε + δ))`. -/
theorem capture (hs : IsHyperBUGStep F G δ ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hδ0 : 0 ≤ δ)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖A t₁ - P₁ (Q₁ (A t₁))‖ ≤ 2 * (h * (4 * L * (B + δ) * h + (ε + δ))) := by
  have h1 := hyper_kstep_capture hF hL hB hδ0 hs.projP₁ hs.projQ₀ ht₁ hh hA hs.kSol
    (hs.kStart.trans hA₀.symm) hs.kCap hs.kDefect hs.kNormal
  have h2 := hyper_kstep_capture hF hL hB hδ0 hs.projQ₁ hs.projP₀ ht₁ hh hA hs.lSol
    (hs.lStart.trans hA₀.symm) hs.lCap hs.lDefect hs.lNormal
  have h3 := norm_sub_apply_apply_le (Q := Q₁) hs.projP₁ (A t₁)
  linarith

/-- **Local error of the hyper-reduced BUG integrator** (new, OP-RS-03).  With
`θ = h (4 L (B + δ) h + (ε + δ))`:

    ‖YS t₁ - A t₁‖ ≤ (e^{L h} - 1) (B h + 2θ) + 2θ + h e^{L h} δ,

i.e. the robust BUG bound with `B ↦ B + δ`, `ε ↦ ε + δ`, plus `O(h δ)`. -/
theorem local_error (hs : IsHyperBUGStep F G δ ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hδ0 : 0 ≤ δ)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + 2 * (h * (4 * L * (B + δ) * h + (ε + δ))))
      + 2 * (h * (4 * L * (B + δ) * h + (ε + δ))) + h * Real.exp (L * h) * δ :=
  hyper_galerkin_step_error (R := P₁ * Q₁) (hs.projP₁.mul hs.projQ₁ hs.comm₁) hF hL hB hδ0 ht₁
    hh hA hs.sSol (by rw [hs.sStart, hA₀]; rfl) hs.sDefect (hs.capture hF hL hB hδ0 ht₁ hh hA hA₀)

/-- **Local error of the hyper-reduced BUG integrator, `O`-form** (new, OP-RS-03).  For
`0 ≤ h ≤ H` and `ε ≥ 0`:

    ‖YS t₁ - A t₁‖ ≤ h (c₁ (ε + δ) + c₂(B + δ) h + e^{L H} δ),

`c₁ = bugC₁ L H`, `c₂(B) = bugC₂ L B H` — no singular values, no Lipschitz constant of `G`. -/
theorem local_error_le (hs : IsHyperBUGStep F G δ ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hδ0 : 0 ≤ δ)
    (hε : 0 ≤ ε) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤
      h * (bugC₁ L H * (ε + δ) + bugC₂ L (B + δ) H * h + Real.exp (L * H) * δ) := by
  have h1 := hs.local_error hF hL hB hδ0 ht₁ hh hA hA₀
  have hB0 := hB.nonneg
  have h2 := bug_bound_le (B := B + δ) (ε := ε + δ) hL (by linarith) (by linarith) hh hhH
  have hexp1 : 0 ≤ Real.exp (L * h) - 1 := by
    have := Real.add_one_le_exp (L * h); nlinarith [mul_nonneg hL hh]
  have h3 : (Real.exp (L * h) - 1) * (B * h + 2 * (h * (4 * L * (B + δ) * h + (ε + δ))))
      ≤ (Real.exp (L * h) - 1) * ((B + δ) * h + 2 * (h * (4 * L * (B + δ) * h + (ε + δ)))) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hexp1
  have h4 : h * Real.exp (L * h) * δ ≤ h * Real.exp (L * H) * δ := by
    have := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hL)
    have := mul_le_mul_of_nonneg_left this hh
    nlinarith
  nlinarith

end IsHyperBUGStep

/-- **Robust global error of the hyper-reduced BUG integrator** (new, OP-RS-03).  Let `F` be
`L`-Lipschitz and `B`-bounded, `A' = F(t, A)` on `[t₀, t₀ + N h]`, `0 ≤ h ≤ H`, and let each
step be a hyper-reduced BUG step (`IsHyperBUGStep`) driven by computed fields `G n` that are
`δ`-accurate along the substep trajectories (no regularity of `G n`).  With exact flows `Φ n` of
`F` from `Y n`, for `n ≤ N`, `n h ≤ T`, `‖Y 0 - A t₀‖ ≤ δ₀`:

    ‖Y n - A tₙ‖ ≤ e^{LT} δ₀ + T e^{LT} (c₁ (ε + δ) + c₂(B + δ) h + e^{L H} δ),

i.e. `c₀ δ₀ + c₁ ε + c₂ h + c₃ δ` with constants depending only on `L, B + δ, T, H`. -/
theorem hyper_bug_global_error_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε : 0 ≤ ε) (hδ0 : 0 ≤ δ) {G : ℕ → ℝ → E → E} {h H : ℝ}
    (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ} (hA : ODESolution F A t₀ (t₀ + N * h))
    {P Q : ℕ → E →L[ℝ] E} {Y : ℕ → E} {YK YL YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsHyperBUGStep F (G n) δ ε (P n) (Q n) (P (n + 1)) (Q (n + 1))
      (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n))
    (hY : ∀ n < N, Y (n + 1) = YS n (t₀ + (n + 1) * h))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {δ₀ T : ℝ} (hδ₀ : ‖Y 0 - A t₀‖ ≤ δ₀) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ₀ + T * Real.exp (L * T) *
        (bugC₁ L H * (ε + δ) + bugC₂ L (B + δ) H * h + Real.exp (L * H) * δ) := by
  intro n hn hT
  have hH : 0 ≤ H := hh.trans hhH
  have hg : 0 ≤ bugC₁ L H * (ε + δ) + bugC₂ L (B + δ) H * h + Real.exp (L * H) * δ := by
    have := bugC₁_nonneg hL hH
    have := bugC₂_nonneg (B := B + δ) hL (by linarith [hB.nonneg]) hH
    positivity
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤
      h * (bugC₁ L H * (ε + δ) + bugC₂ L (B + δ) H * h + Real.exp (L * H) * δ) := by
    intro n hn
    rw [hY n hn]
    exact (hstep n hn).local_error_le hF hL hB hδ0 hε (by ring) hh hhH (hΦ n hn) (hΦ₀ n hn)
  have h1 := lady_windermere_of_le hF hL hh hA hΦ hΦ₀ hg hloc n hn hT
  have h2 := mul_le_mul_of_nonneg_left (show ‖Y 0 - A t₀‖ + T *
    (bugC₁ L H * (ε + δ) + bugC₂ L (B + δ) H * h + Real.exp (L * H) * δ) ≤ δ₀ + T *
    (bugC₁ L H * (ε + δ) + bugC₂ L (B + δ) H * h + Real.exp (L * H) * δ) by linarith)
    (Real.exp_pos (L * T)).le
  calc _ ≤ _ := h1.trans h2
    _ = _ := by ring

/-- The hypotheses of a hyper-reduced BUG step are satisfiable with `G ≠ F`: on `ℝ`, exact field
`F ≡ 1`, computed field `G ≡ 3/2` (`δ = 1/2`), identity projectors, all substep trajectories
`t ↦ 3t/2` on `[0, 1]`, `ε = 0`. -/
example : IsHyperBUGStep (E := ℝ) (fun _ _ => 1) (fun _ _ => 3 / 2) (1 / 2) 0 1 1 1 1 0 1 0
    (fun t => 0 + 3 / 2 * t) (fun t => 0 + 3 / 2 * t) (fun t => 0 + 3 / 2 * t) where
  projP₀ := IsOrthProj.one
  projQ₀ := IsOrthProj.one
  projP₁ := IsOrthProj.one
  projQ₁ := IsOrthProj.one
  comm₁ _ := rfl
  kSol := odeSolution_of_affine (fun _ _ => by simp) (fun _ => rfl) _ _
  kStart := by simp
  kCap := rfl
  kNormal _ _ := by simp
  kDefect _ _ := by norm_num
  lSol := odeSolution_of_affine (fun _ _ => by simp) (fun _ => rfl) _ _
  lStart := by simp
  lCap := rfl
  lNormal _ _ := by simp
  lDefect _ _ := by norm_num
  sSol := odeSolution_of_affine (fun _ _ => by simp) (fun _ => rfl) _ _
  sStart := by simp
  sDefect _ _ := by norm_num

/-- **Continuous DLRA with a hyper-reduced field** (new, continuous variant of OP-RS-03).  Let
`Y' = P(t) G(t, Y)` with orthogonal projectors `P(t)` and a computed field `G` (no regularity)
that is `δ`-accurate along `Y`, `‖G(t, Y t) - F(t, Y t)‖ ≤ δ`.  If `F` is `L`-Lipschitz, its
normal component along `Y` is `‖(1 - P(t)) F(t, Y t)‖ ≤ ε`, and `A' = F(t, A)`, then
`‖Y t - A t‖ ≤ gronwallBound δ₀ L (ε + δ) (t - a)`. -/
theorem hyper_dlra_norm_sub_le {P : ℝ → E →L[ℝ] E} {Y : ℝ → E} {a b δ₀ : ℝ}
    (hP : ∀ t ∈ Ico a b, IsOrthProj (P t)) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hA : ODESolution F A a b) (hY : ODESolution (fun t x => P t (G t x)) Y a b)
    (hε : ∀ t ∈ Ico a b, ‖(1 - P t) (F t (Y t))‖ ≤ ε)
    (hδ : ∀ t ∈ Ico a b, ‖G t (Y t) - F t (Y t)‖ ≤ δ) (hδ₀ : ‖Y a - A a‖ ≤ δ₀) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ gronwallBound δ₀ L (ε + δ) (t - a) := by
  intro t ht
  have h := norm_sub_le_gronwallBound hF hL (y := Y) (z := A) (u := fun t => P t (G t (Y t)))
    (w := fun t => F t (A t)) (ηy := ε + δ) (ηz := 0) hY.cont hY.deriv (fun s hs => ?_)
    hA.cont hA.deriv (fun _ _ => by simp) hδ₀ t ht
  · rwa [add_zero] at h
  have hdec : P s (G s (Y s)) - F s (Y s)
      = P s (G s (Y s) - F s (Y s)) - (1 - P s) (F s (Y s)) := by
    simp only [map_sub, sub_apply, one_apply_eq_self]; abel
  rw [hdec]
  have h1 : ‖P s (G s (Y s) - F s (Y s))‖ ≤ δ := ((hP s hs).norm_le _).trans (hδ s hs)
  have h2 := norm_sub_le (P s (G s (Y s) - F s (Y s))) ((1 - P s) (F s (Y s)))
  linarith [hε s hs]

end Hyper

/-! ### (b) Surrogate models (OP-OT-07) -/

section Surrogate

variable {F Ft : ℝ → E → E} {L η δ₀ : ℝ} {a b : ℝ} {A At : ℝ → E}

/-- **Perturbations of the vector field enter additively** (OP-OT-07, continuous part).  Let `A`
solve the true model `A' = F(t, A)` and `At` the surrogate model `At' = Ft(t, At)` with `Ft`
`L`-Lipschitz (`F` arbitrary), and let the model error be `‖F(t, A t) - Ft(t, A t)‖ ≤ η` along
the true solution.  Then `‖At t - A t‖ ≤ gronwallBound δ₀ L η (t - a)`
`= e^{L(t-a)} δ₀ + η (e^{L(t-a)} - 1)/L`. -/
theorem surrogate_norm_sub_le (hFt : IsLipschitzField Ft L) (hL : 0 ≤ L)
    (hA : ODESolution F A a b) (hAt : ODESolution Ft At a b)
    (hη : ∀ t ∈ Ico a b, ‖F t (A t) - Ft t (A t)‖ ≤ η) (hδ : ‖At a - A a‖ ≤ δ₀) :
    ∀ t ∈ Icc a b, ‖At t - A t‖ ≤ gronwallBound δ₀ L η (t - a) := by
  intro t ht
  have h := norm_sub_le_gronwallBound hFt hL (y := At) (z := A) (u := fun t => Ft t (At t))
    (w := fun t => F t (A t)) (ηy := 0) (ηz := η) hAt.cont hAt.deriv (fun _ _ => by simp)
    hA.cont hA.deriv hη hδ t ht
  rwa [zero_add] at h

/-- **Continuous DLRA of a surrogate model** (OP-OT-07).  Let `Y' = P(t) Ft(t, Y)` be the DLRA
of the surrogate field `Ft` (`L`-Lipschitz) with normal component
`‖(1 - P(t)) Ft(t, Y t)‖ ≤ ε`, and let the true solution satisfy `A' = F(t, A)` with
`‖F(t, A t) - Ft(t, A t)‖ ≤ η`.  Then `‖Y t - A t‖ ≤ gronwallBound δ₀ L (ε + η) (t - a)`: the
model error adds to the normal component inside a single Grönwall estimate. -/
theorem surrogate_dlra_norm_sub_le {P : ℝ → E →L[ℝ] E} {Y : ℝ → E} {ε : ℝ}
    (hFt : IsLipschitzField Ft L) (hL : 0 ≤ L) (hA : ODESolution F A a b)
    (hY : ODESolution (fun t x => P t (Ft t x)) Y a b)
    (hε : ∀ t ∈ Ico a b, ‖(1 - P t) (Ft t (Y t))‖ ≤ ε)
    (hη : ∀ t ∈ Ico a b, ‖F t (A t) - Ft t (A t)‖ ≤ η) (hδ : ‖Y a - A a‖ ≤ δ₀) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ gronwallBound δ₀ L (ε + η) (t - a) := by
  intro t ht
  refine norm_sub_le_gronwallBound hFt hL (y := Y) (z := A) (u := fun t => P t (Ft t (Y t)))
    (w := fun t => F t (A t)) hY.cont hY.deriv (fun s hs => ?_) hA.cont hA.deriv hη hδ t ht
  have h := hε s hs
  rwa [sub_apply, one_apply_eq_self, norm_sub_rev] at h

/-- Explicit form of `surrogate_dlra_norm_sub_le`:
`‖Y t - A t‖ ≤ e^{L(t-a)} (δ₀ + (ε + η)(t - a))`. -/
theorem surrogate_dlra_norm_sub_le_exp {P : ℝ → E →L[ℝ] E} {Y : ℝ → E} {ε : ℝ}
    (hFt : IsLipschitzField Ft L) (hL : 0 ≤ L) (hε0 : 0 ≤ ε) (hη0 : 0 ≤ η)
    (hA : ODESolution F A a b) (hY : ODESolution (fun t x => P t (Ft t x)) Y a b)
    (hε : ∀ t ∈ Ico a b, ‖(1 - P t) (Ft t (Y t))‖ ≤ ε)
    (hη : ∀ t ∈ Ico a b, ‖F t (A t) - Ft t (A t)‖ ≤ η) (hδ : ‖Y a - A a‖ ≤ δ₀) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ Real.exp (L * (t - a)) * (δ₀ + (ε + η) * (t - a)) :=
  fun t ht => (surrogate_dlra_norm_sub_le hFt hL hA hY hε hη hδ t ht).trans
    (gronwallBound_le_exp_mul hL (add_nonneg hε0 hη0))

/-- The surrogate error at the grid point `tₙ = t₀ + n h` is at most `T e^{LT} η` when
`n h ≤ T` and `At t₀ = A t₀`. -/
lemma surrogate_grid_le {t₀ h T : ℝ} {N n : ℕ} (hFt : IsLipschitzField Ft L) (hL : 0 ≤ L)
    (hη0 : 0 ≤ η) (hh : 0 ≤ h) (hA : ODESolution F A t₀ (t₀ + N * h))
    (hAt : ODESolution Ft At t₀ (t₀ + N * h))
    (hη : ∀ t ∈ Ico t₀ (t₀ + N * h), ‖F t (A t) - Ft t (A t)‖ ≤ η) (hAt₀ : At t₀ = A t₀)
    (hn : n ≤ N) (hT : (n : ℝ) * h ≤ T) :
    ‖At (t₀ + n * h) - A (t₀ + n * h)‖ ≤ T * Real.exp (L * T) * η := by
  have hnh : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg n) hh
  have hnN : (n : ℝ) * h ≤ N * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hh
  have h1 := surrogate_norm_sub_le hFt hL hA hAt hη (δ₀ := 0) (by simp [hAt₀])
    (t₀ + n * h) ⟨by linarith, by linarith⟩
  rw [show t₀ + n * h - t₀ = n * h by ring] at h1
  have h2 := gronwallBound_le_exp_mul (δ := 0) (x := (n : ℝ) * h) hL hη0
  have h3 : Real.exp (L * (n * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  have h4 : η * (n * h) ≤ η * T := mul_le_mul_of_nonneg_left hT hη0
  have h5 : Real.exp (L * (n * h)) * (η * (n * h)) ≤ Real.exp (L * T) * (η * T) :=
    mul_le_mul h3 h4 (mul_nonneg hη0 hnh) (Real.exp_pos _).le
  have := h1.trans h2
  rw [zero_add] at this
  linarith

/-- **BUG integrator for a surrogate model** (new, OP-OT-07).  Run the BUG integrator on a
surrogate field `Ft` (`L`-Lipschitz, `B`-bounded, normal component `ε`), with exact surrogate
flows `Φ n` and exact surrogate solution `At`, `At t₀ = A t₀`, where `A` solves the true model
and `‖F(t, A t) - Ft(t, A t)‖ ≤ η`.  Then for `n ≤ N`, `n h ≤ T`:

    ‖Y n - A tₙ‖ ≤ e^{LT} δ₀ + T e^{LT} c₁ ε + T e^{LT} c₂ h + T e^{LT} η. -/
theorem surrogate_bug_global_error_le {B ε : ℝ} (hFt : IsLipschitzField Ft L) (hL : 0 ≤ L)
    (hB : IsBoundedField Ft B) (hε : 0 ≤ ε) (hη0 : 0 ≤ η) {t₀ h H : ℝ} (hh : 0 ≤ h)
    (hhH : h ≤ H) {N : ℕ} (hA : ODESolution F A t₀ (t₀ + N * h))
    (hAt : ODESolution Ft At t₀ (t₀ + N * h))
    (hη : ∀ t ∈ Ico t₀ (t₀ + N * h), ‖F t (A t) - Ft t (A t)‖ ≤ η) (hAt₀ : At t₀ = A t₀)
    {P Q : ℕ → E →L[ℝ] E} {Y : ℕ → E} {YK YL YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsBUGStep Ft ε (P n) (Q n) (P (n + 1)) (Q (n + 1)) (t₀ + n * h)
      (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n))
    (hY : ∀ n < N, Y (n + 1) = YS n (t₀ + (n + 1) * h))
    (hΦ : ∀ n < N, ODESolution Ft (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ₀) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ₀
        + T * Real.exp (L * T) * bugC₁ L H * ε + T * Real.exp (L * T) * bugC₂ L B H * h
        + T * Real.exp (L * T) * η := by
  intro n hn hT
  have h1 := bug_global_error_le hFt hL hB hε hh hhH hAt hstep hY hΦ hΦ₀ (δ := δ₀)
    (by rw [hAt₀]; exact hδ) n hn hT
  have h2 := surrogate_grid_le hFt hL hη0 hh hA hAt hη hAt₀ hn hT
  have h3 := norm_sub_le_norm_sub_add_norm_sub (Y n) (At (t₀ + n * h)) (A (t₀ + n * h))
  linarith

/-- **Projector-splitting (KSL) integrator for a surrogate model** (new, OP-OT-07): as
`surrogate_bug_global_error_le` with the KSL bound,
`‖Y n - A tₙ‖ ≤ e^{LT} δ₀ + T e^{LT} ε + 11 L B T e^{LT} h + T e^{LT} η`. -/
theorem surrogate_ksl_global_error_le {B ε : ℝ} (hFt : IsLipschitzField Ft L) (hL : 0 ≤ L)
    (hB : IsBoundedField Ft B) (hε : 0 ≤ ε) (hη0 : 0 ≤ η) {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ}
    (hA : ODESolution F A t₀ (t₀ + N * h)) (hAt : ODESolution Ft At t₀ (t₀ + N * h))
    (hη : ∀ t ∈ Ico t₀ (t₀ + N * h), ‖F t (A t) - Ft t (A t)‖ ≤ η) (hAt₀ : At t₀ = A t₀)
    {P Q : ℕ → E →L[ℝ] E} {Y : ℕ → E} {YK YS YL Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsKSLStep Ft ε (P n) (Q n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
      (YK n) (YS n) (YL n))
    (hY : ∀ n < N, Y (n + 1) = YL n (t₀ + (n + 1) * h))
    (hΦ : ∀ n < N, ODESolution Ft (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ₀) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * ε
        + 11 * L * B * T * Real.exp (L * T) * h + T * Real.exp (L * T) * η := by
  intro n hn hT
  have h1 := ksl_global_error_le hFt hL hB hε hh hAt hstep hY hΦ hΦ₀ (δ := δ₀)
    (by rw [hAt₀]; exact hδ) n hn hT
  have h2 := surrogate_grid_le hFt hL hη0 hh hA hAt hη hAt₀ hn hT
  have h3 := norm_sub_le_norm_sub_add_norm_sub (Y n) (At (t₀ + n * h)) (A (t₀ + n * h))
  linarith

/-- Non-vacuity of `surrogate_norm_sub_le`: true model `F ≡ 1` with solution `t ↦ t`, surrogate
`Ft ≡ 1/2` with solution `t ↦ t/2` (`L = 0`, `η = 1/2`): the bound `‖t/2 - t‖ ≤ t/2` on `[0, 1]`
is attained. -/
example : ∀ t ∈ Icc (0 : ℝ) 1,
    ‖(0 + 1 / 2 * t) - (0 + 1 * t)‖ ≤ gronwallBound 0 0 (1 / 2) (t - 0) :=
  surrogate_norm_sub_le (E := ℝ) (F := fun _ _ => 1) (Ft := fun _ _ => 1 / 2)
    (fun _ _ _ => by simp) le_rfl
    (odeSolution_of_affine (fun _ _ => rfl) (fun _ => rfl) _ _)
    (odeSolution_of_affine (fun _ _ => rfl) (fun _ => rfl) _ _)
    (fun _ _ => by norm_num) (by simp)

end Surrogate

/-! ### (c) Freezing a coupling term over one step (OP-OT-04) -/

section Frozen

variable {C : Type*} [NormedAddCommGroup C]

/-- The coupled field `F(t, Y) = G(t, Y, E(Y))`. -/
def coupledField (G : ℝ → E → C → E) (Ec : E → C) : ℝ → E → E := fun t Y => G t Y (Ec Y)

/-- The frozen field `F̃(t, Y) = G(t, Y, E(Y₀))`: the coupling term is frozen at the value it
takes at the start `Y₀` of the step. -/
def frozenField (G : ℝ → E → C → E) (Ec : E → C) (Y₀ : E) : ℝ → E → E :=
  fun t Y => G t Y (Ec Y₀)

variable {G : ℝ → E → C → E} {Ec : E → C} {LG LE : ℝ}

omit [InnerProductSpace ℝ E] in
/-- Pointwise defect of the frozen field: `‖F̃(t, Y) - F(t, Y)‖ ≤ L_G L_E ‖Y - Y₀‖`. -/
lemma frozen_defect_le (hG : ∀ t Y c c', ‖G t Y c - G t Y c'‖ ≤ LG * ‖c - c'‖)
    (hE : ∀ Y Y', ‖Ec Y - Ec Y'‖ ≤ LE * ‖Y - Y'‖) (hLG : 0 ≤ LG) (Y₀ : E) (t : ℝ) (Y : E) :
    ‖frozenField G Ec Y₀ t Y - coupledField G Ec t Y‖ ≤ LG * LE * ‖Y - Y₀‖ := by
  unfold frozenField coupledField
  calc _ ≤ LG * ‖Ec Y₀ - Ec Y‖ := hG t Y _ _
    _ ≤ LG * (LE * ‖Y₀ - Y‖) := mul_le_mul_of_nonneg_left (hE _ _) hLG
    _ = LG * LE * ‖Y - Y₀‖ := by rw [norm_sub_rev]; ring

/-- **Freezing the coupling over a step costs `O(h²)`** (new; OP-OT-04, claimed in
[UschmajewZeiser2024, Sec. 2.5]).  Let `F = G(·, ·, E(·))` be `L`-Lipschitz, `G` `L_G`-Lipschitz in
the coupling argument, `E` `L_E`-Lipschitz, and the frozen field `F̃ = G(·, ·, E(Y₀))`
`B`-bounded.  If `Φ` solves `Φ' = F(t, Φ)` and `Φt` solves `Φt' = F̃(t, Φt)` on `[t₀, t₀ + h]`,
both from `Y₀`, then

    ‖Φt t₁ - Φ t₁‖ ≤ L_G L_E B h² e^{L h}.

(Along `Φt` the defect is `≤ L_G L_E ‖Φt t - Y₀‖ ≤ L_G L_E B h`; perturbed Grönwall.) -/
theorem frozen_local_error (hG : ∀ t Y c c', ‖G t Y c - G t Y c'‖ ≤ LG * ‖c - c'‖)
    (hE : ∀ Y Y', ‖Ec Y - Ec Y'‖ ≤ LE * ‖Y - Y'‖) (hLG : 0 ≤ LG) (hLE : 0 ≤ LE) {L B : ℝ}
    (hF : IsLipschitzField (coupledField G Ec) L) (hL : 0 ≤ L) {Y₀ : E}
    (hB : IsBoundedField (frozenField G Ec Y₀) B) {t₀ t₁ h : ℝ} (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) {Φ Φt : ℝ → E} (hΦ : ODESolution (coupledField G Ec) Φ t₀ t₁)
    (hΦ₀ : Φ t₀ = Y₀) (hΦt : ODESolution (frozenField G Ec Y₀) Φt t₀ t₁) (hΦt₀ : Φt t₀ = Y₀) :
    ‖Φt t₁ - Φ t₁‖ ≤ LG * LE * B * h ^ 2 * Real.exp (L * h) := by
  have hB0 := hB.nonneg
  have hη : 0 ≤ LG * LE * B * h := by positivity
  have hdef : ∀ t ∈ Ico t₀ t₁, ‖frozenField G Ec Y₀ t (Φt t) - coupledField G Ec t (Φt t)‖
      ≤ LG * LE * B * h := by
    intro t ht
    have h1 := frozen_defect_le hG hE hLG Y₀ t (Φt t)
    have h2 := hΦt.norm_sub_start_le hB ht₁ t (Ico_subset_Icc_self ht)
    rw [hΦt₀] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hLG hLE)
    nlinarith
  have := substep_error_of_defect hF hL hη ht₁ hh hΦ hΦt.cont hΦt.deriv hdef
    (hΦt₀.trans hΦ₀.symm)
  calc _ ≤ _ := this
    _ = _ := by ring

/-- Non-vacuity and sharpness of `frozen_local_error`: on `ℝ`, `G(t, Y, c) = c`, `E = id`
(so `F(t, Y) = Y`, `L = L_G = L_E = 1`), `Y₀ = 1`; the true flow is `e^t`, the frozen flow
`1 + t` (`B = 1`), and the bound reads `|1 + h - e^h| ≤ h² e^h`. -/
example {h : ℝ} (hh : 0 ≤ h) : ‖(1 + h) - Real.exp h‖ ≤ 1 * 1 * 1 * h ^ 2 * Real.exp (1 * h) := by
  have key := frozen_local_error (E := ℝ) (C := ℝ) (G := fun _ _ c => c) (Ec := fun Y => Y)
    (LG := 1) (LE := 1) (fun _ _ _ _ => by simp) (fun _ _ => by simp) zero_le_one zero_le_one
    (L := 1) (B := 1) (fun _ _ _ => by simp [coupledField]) zero_le_one (Y₀ := 1)
    (fun _ _ => by simp [frozenField]) (t₀ := 0) (t₁ := h) (h := h) (by ring) hh
    (Φ := Real.exp) (Φt := fun t => 1 + 1 * t)
    ⟨Real.continuous_exp.continuousOn, fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt⟩
    (by simp)
    (odeSolution_of_affine (fun _ _ => by simp [frozenField]) (fun _ => rfl) _ _) (by simp)
  simpa using key

end Frozen

/-! ### (d) Frozen coupling inside robust integrators (OP-HO-04) -/

section FrozenGlobal

variable {C : Type*} [NormedAddCommGroup C]
variable {G : ℝ → E → C → E} {Ec : E → C} {LG LE L B : ℝ}

/-- **Global error with frozen coupling, generic form** (new; OP-HO-04 and the global claim of
OP-OT-04).  Let `F = G(·, ·, E(·))` be `L`-Lipschitz, `G` `L_G`-Lipschitz in the coupling
argument and `E` `L_E`-Lipschitz.  Step `n` uses the frozen field
`F̃ₙ = G(·, ·, E(Y n))`, which is `B`-bounded.  Let `Φt n` be its exact flow on `[tₙ, tₙ₊₁]` from
`Y n` and `Φ n` the exact flow of `F`.  If an integrator has local error
`‖Y (n+1) - Φt n tₙ₊₁‖ ≤ h g₀` with respect to the frozen flow (any robust local error bound),
then for `0 ≤ h ≤ H`, `n ≤ N`, `n h ≤ T`:

    ‖Y n - A tₙ‖ ≤ e^{LT} (‖Y 0 - A t₀‖ + T (g₀ + e^{L H} L_G L_E B h)). -/
theorem frozen_global_error_of_local
    (hG : ∀ t Y c c', ‖G t Y c - G t Y c'‖ ≤ LG * ‖c - c'‖)
    (hE : ∀ Y Y', ‖Ec Y - Ec Y'‖ ≤ LE * ‖Y - Y'‖) (hLG : 0 ≤ LG) (hLE : 0 ≤ LE)
    (hF : IsLipschitzField (coupledField G Ec) L) (hL : 0 ≤ L) {t₀ h H : ℝ} (hh : 0 ≤ h)
    (hhH : h ≤ H) {N : ℕ} {A : ℝ → E} (hA : ODESolution (coupledField G Ec) A t₀ (t₀ + N * h))
    {Y : ℕ → E} {Φ Φt : ℕ → ℝ → E}
    (hB : ∀ n < N, IsBoundedField (frozenField G Ec (Y n)) B)
    (hΦ : ∀ n < N, ODESolution (coupledField G Ec) (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    (hΦt : ∀ n < N, ODESolution (frozenField G Ec (Y n)) (Φt n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦt₀ : ∀ n < N, Φt n (t₀ + n * h) = Y n) {g₀ : ℝ} (hg₀ : 0 ≤ g₀) (hB0 : 0 ≤ B)
    (hloc : ∀ n < N, ‖Y (n + 1) - Φt n (t₀ + (n + 1) * h)‖ ≤ h * g₀) {T : ℝ} :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * (g₀ + Real.exp (L * H) * LG * LE * B * h)) := by
  have hg : 0 ≤ g₀ + Real.exp (L * H) * LG * LE * B * h := by positivity
  have hloc' : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤
      h * (g₀ + Real.exp (L * H) * LG * LE * B * h) := by
    intro n hn
    have h1 := frozen_local_error hG hE hLG hLE hF hL (hB n hn) (by ring) hh (hΦ n hn)
      (hΦ₀ n hn) (hΦt n hn) (hΦt₀ n hn)
    have h2 := norm_sub_le_norm_sub_add_norm_sub (Y (n + 1)) (Φt n (t₀ + (n + 1) * h))
      (Φ n (t₀ + (n + 1) * h))
    have h3 : Real.exp (L * h) ≤ Real.exp (L * H) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hL)
    have h4 : LG * LE * B * h ^ 2 * Real.exp (L * h) ≤ LG * LE * B * h ^ 2 * Real.exp (L * H) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 := hloc n hn
    nlinarith
  exact lady_windermere_of_le hF hL hh hA hΦ hΦ₀ hg hloc'

/-- **BUG integrator with frozen coupling** (new; OP-HO-04 for BUG).  Each step `n` is a BUG
step (`IsBUGStep`) for the frozen field `F̃ₙ = G(·, ·, E(Y n))`, which is `L`-Lipschitz and
`B`-bounded with normal component `ε`.  Then for `n ≤ N`, `n h ≤ T`, `‖Y 0 - A t₀‖ ≤ δ₀`:

    ‖Y n - A tₙ‖ ≤ e^{LT} δ₀ + T e^{LT} (c₁ ε + (c₂ + e^{L H} L_G L_E B) h),

with `c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`: first order, constants depending only on
`L, B, T, H, L_G L_E`. -/
theorem frozen_bug_global_error_le
    (hG : ∀ t Y c c', ‖G t Y c - G t Y c'‖ ≤ LG * ‖c - c'‖)
    (hE : ∀ Y Y', ‖Ec Y - Ec Y'‖ ≤ LE * ‖Y - Y'‖) (hLG : 0 ≤ LG) (hLE : 0 ≤ LE)
    (hF : IsLipschitzField (coupledField G Ec) L) (hL : 0 ≤ L) (hB0 : 0 ≤ B) {ε : ℝ}
    (hε : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution (coupledField G Ec) A t₀ (t₀ + N * h))
    {P Q : ℕ → E →L[ℝ] E} {Y : ℕ → E} {YK YL YS Φ Φt : ℕ → ℝ → E}
    (hFt : ∀ n < N, IsLipschitzField (frozenField G Ec (Y n)) L)
    (hB : ∀ n < N, IsBoundedField (frozenField G Ec (Y n)) B)
    (hstep : ∀ n < N, IsBUGStep (frozenField G Ec (Y n)) ε (P n) (Q n) (P (n + 1)) (Q (n + 1))
      (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n))
    (hY : ∀ n < N, Y (n + 1) = YS n (t₀ + (n + 1) * h))
    (hΦ : ∀ n < N, ODESolution (coupledField G Ec) (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    (hΦt : ∀ n < N, ODESolution (frozenField G Ec (Y n)) (Φt n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦt₀ : ∀ n < N, Φt n (t₀ + n * h) = Y n) {δ₀ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ₀) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ₀ + T * Real.exp (L * T) *
        (bugC₁ L H * ε + (bugC₂ L B H + Real.exp (L * H) * LG * LE * B) * h) := by
  intro n hn hT
  have hH : 0 ≤ H := hh.trans hhH
  have hg₀ : 0 ≤ bugC₁ L H * ε + bugC₂ L B H * h :=
    add_nonneg (mul_nonneg (bugC₁_nonneg hL hH) hε) (mul_nonneg (bugC₂_nonneg hL hB0 hH) hh)
  have hloc : ∀ n < N, ‖Y (n + 1) - Φt n (t₀ + (n + 1) * h)‖ ≤
      h * (bugC₁ L H * ε + bugC₂ L B H * h) := by
    intro n hn
    rw [hY n hn]
    exact (hstep n hn).local_error_le (hFt n hn) hL (hB n hn) (by ring) hh hhH (hΦt n hn)
      (hΦt₀ n hn)
  have h1 := frozen_global_error_of_local hG hE hLG hLE hF hL hh hhH hA hB hΦ hΦ₀ hΦt hΦt₀ hg₀
    hB0 hloc n hn hT
  have h2 := mul_le_mul_of_nonneg_left (show ‖Y 0 - A t₀‖ + T * (bugC₁ L H * ε
    + bugC₂ L B H * h + Real.exp (L * H) * LG * LE * B * h) ≤ δ₀ + T * (bugC₁ L H * ε
    + bugC₂ L B H * h + Real.exp (L * H) * LG * LE * B * h) by linarith)
    (Real.exp_pos (L * T)).le
  calc _ ≤ _ := h1.trans h2
    _ = _ := by ring

/-- **Projector-splitting (KSL) integrator with frozen coupling** (new; OP-HO-04 for the
K–S–L ordering).  As `frozen_bug_global_error_le` with `IsKSLStep`:

    ‖Y n - A tₙ‖ ≤ e^{LT} δ₀ + T e^{LT} (ε + (11 L B + e^{L H} L_G L_E B) h). -/
theorem frozen_ksl_global_error_le
    (hG : ∀ t Y c c', ‖G t Y c - G t Y c'‖ ≤ LG * ‖c - c'‖)
    (hE : ∀ Y Y', ‖Ec Y - Ec Y'‖ ≤ LE * ‖Y - Y'‖) (hLG : 0 ≤ LG) (hLE : 0 ≤ LE)
    (hF : IsLipschitzField (coupledField G Ec) L) (hL : 0 ≤ L) (hB0 : 0 ≤ B) {ε : ℝ}
    (hε : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution (coupledField G Ec) A t₀ (t₀ + N * h))
    {P Q : ℕ → E →L[ℝ] E} {Y : ℕ → E} {YK YS YL Φ Φt : ℕ → ℝ → E}
    (hFt : ∀ n < N, IsLipschitzField (frozenField G Ec (Y n)) L)
    (hB : ∀ n < N, IsBoundedField (frozenField G Ec (Y n)) B)
    (hstep : ∀ n < N, IsKSLStep (frozenField G Ec (Y n)) ε (P n) (Q n) (t₀ + n * h)
      (t₀ + (n + 1) * h) (Y n) (YK n) (YS n) (YL n))
    (hY : ∀ n < N, Y (n + 1) = YL n (t₀ + (n + 1) * h))
    (hΦ : ∀ n < N, ODESolution (coupledField G Ec) (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    (hΦt : ∀ n < N, ODESolution (frozenField G Ec (Y n)) (Φt n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦt₀ : ∀ n < N, Φt n (t₀ + n * h) = Y n) {δ₀ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ₀) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ₀ + T * Real.exp (L * T) *
        (ε + (11 * L * B + Real.exp (L * H) * LG * LE * B) * h) := by
  intro n hn hT
  have hg₀ : 0 ≤ 11 * L * B * h + ε := by positivity
  have hloc : ∀ n < N, ‖Y (n + 1) - Φt n (t₀ + (n + 1) * h)‖ ≤ h * (11 * L * B * h + ε) := by
    intro n hn
    rw [hY n hn]
    exact (hstep n hn).local_error (hFt n hn) hL (hB n hn) (by ring) hh (hΦt n hn) (hΦt₀ n hn)
  have h1 := frozen_global_error_of_local hG hE hLG hLE hF hL hh hhH hA hB hΦ hΦ₀ hΦt hΦt₀ hg₀
    hB0 hloc n hn hT
  have h2 := mul_le_mul_of_nonneg_left (show ‖Y 0 - A t₀‖ + T * (11 * L * B * h + ε
    + Real.exp (L * H) * LG * LE * B * h) ≤ δ₀ + T * (11 * L * B * h + ε
    + Real.exp (L * H) * LG * LE * B * h) by linarith)
    (Real.exp_pos (L * T)).le
  calc _ ≤ _ := h1.trans h2
    _ = _ := by ring

end FrozenGlobal

end LeanDLRA.PerturbedField
