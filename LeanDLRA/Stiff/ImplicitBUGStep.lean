import LeanDLRA.Stiff.Defs
import LeanDLRA.Stiff.ImplicitBUG
import LeanDLRA.Integrators.Matrix.BUG
import LeanDLRA.Foundations.Localization
import LeanDLRA.Matrix.LowRankDistance

/-!
# The BUG integrator with backward Euler substeps as a step relation

This file treats one step of the fixed-rank BUG integrator with backward Euler substeps for
matrices (`MatrixImplicitBUG.IsStep`, `MatrixImplicitBUG.stepRel`, defined in
`LeanDLRA/Stiff/Defs.lean`) for a field that is Lipschitz and bounded only on a tube around a
reference solution: the stages stay near the start value, the step depends on the field only
there, its local error is bounded, and a step exists for globally Lipschitz fields when
`h L < 1`. The runs and their error bound are in `LeanDLRA/Stiff/ImplicitBUGRun.lean`.

## Main results

* `MatrixImplicitBUG.IsStep.isMatrixImplicitBUGStep`: a step is a step
  `IsMatrixImplicitBUGStep` of the core with capture tolerance `0` and no truncation, so the
  error analysis of `LeanDLRA/Stiff/ImplicitBUG.lean` applies to it.
* `MatrixImplicitBUG.IsStep.norm_stage_sub_le`: if `‖F(t₁, x)‖ ≤ B` near the start value
  `Y₀ = U₀ S₀ V₀ᵀ`, the K- and L-stages lie within `B h` of `Y₀` and the S-stage within `3 B h`.
* `MatrixImplicitBUG.IsStep.congr_field`, `MatrixImplicitBUG.isStep_tubeExt_iff_of_near`,
  `MatrixImplicitBUG.stepRel_tubeExt_iff_of_near`: a step sees the field only at time `t₁` on the
  ball of radius `3 B h` around `Y₀`; near a reference solution the steps of the tube extension
  `tubeExt F A a b ρ` are the steps of `F`.
* `implicit_kstep_capture_of_le`: the capture lemma of the implicit K-step with a pointwise
  bound of the field along the solution in place of global Lipschitz and time conditions.
* `IsImplicitBUGStep.hasLocalError_of_tube`, `MatrixImplicitBUG.IsStep.hasLocalError_of_tube`:
  the local error `implicitLocalBound` of `IsImplicitBUGStep.local_error` for a field that is
  Lipschitz, bounded and Lipschitz in time only on a tube around a reference solution.
* `MatrixImplicitBUG.IsStep.of_lipschitz`: for a globally Lipschitz field and `h L < 1` the
  conditions on the fixed-point iterations follow from the stage equations.
* `MatrixImplicitBUG.exists_isStep`, `MatrixImplicitBUG.exists_stepRel`: a step exists for a
  globally Lipschitz field with `h L < 1` (Banach's fixed point theorem); no continuity in time
  is needed.

## Implementation notes

The stage equations of a field that is controlled only on a tube can have solutions far from the
tube, where nothing is known about the field. The step selects the stage that the fixed-point
iteration reaches from the start value; every iterate then lies within `B h` (S-stage: `3 B h`)
of the start value, and so does the limit. For this reason the converse locality, from steps of
`F` to steps of the extension, holds as well, and the local error holds for every step.

The time dependence of the field enters through `‖F(t, x) - F(s, x)‖ ≤ Lₜ (t - s)` for `s ≤ t`
and `x` in the tube at both times, as in `LeanDLRA/Integrators/Matrix/EulerBUGRun.lean`. The tube
extension does not satisfy such a condition on the whole space, so the local error is proved
directly on the tube from `implicit_kstep_capture_of_le` and `implicitGalerkin_error_le`, with the
constants of `IsImplicitBUGStep.local_error` (one-sided constant `ℓ = L`).

## References

* [CerutiLubich2022] for the fixed-rank BUG integrator; backward Euler substeps as in the
  BE-BUG integrator of arXiv 2610.18419, Algorithm 3.1.
-/

open Set Filter Topology
open scoped Matrix LeanDLRA.Frobenius RealInnerProductSpace

namespace LeanDLRA

/-! ### Capture and local error on a tube, for orthogonal projectors -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Capture by the implicit K-step, with a pointwise bound of the field.** Let `A` solve
`A' = F(t, A)` on `[t₀, t₁]`, `t₁ = t₀ + h`, let `YK = A t₀ + h Q₀ F(t₁, YK)` be the implicit
K-step, let the new basis capture `YK` up to `τ` and let the doubly normal component at `YK` be
at most `ε`. If `‖F(t, A t) - F(t₁, YK)‖ ≤ M` on `[t₀, t₁)`, then

  `‖(1 - P₁) A(t₁)‖ ≤ M h + h ε + τ`.

With `M = (2 L B + Lₜ) h` for a field that is Lipschitz, Lipschitz in time and bounded on the
whole space this is `implicit_kstep_capture`; the pointwise form serves fields that are
controlled only near `A`. -/
theorem implicit_kstep_capture_of_le {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ h M ε τ : ℝ}
    {P₁ Q₀ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) {YK : E} (hK : YK = A t₀ + h • Q₀ (F t₁ YK))
    (hM : ∀ t ∈ Ico t₀ t₁, ‖F t (A t) - F t₁ YK‖ ≤ M) (hτ : ‖(1 - P₁) YK‖ ≤ τ)
    (hε : ‖(1 - P₁) ((1 - Q₀) (F t₁ YK))‖ ≤ ε) :
    ‖(1 - P₁) (A t₁)‖ ≤ M * h + h * ε + τ := by
  set f := F t₁ YK with hf
  have hD := hA.norm_sub_sub_smul_le ht₁ hh f hM
  have hdec : (1 - P₁) (A t₁) = (1 - P₁) (A t₁ - A t₀ - h • f)
      + h • (1 - P₁) ((1 - Q₀) f) + (1 - P₁) YK := by
    rw [← map_smul, ← map_add, ← map_add]
    congr 1
    have hK' : YK = A t₀ + h • Q₀ f := hK
    rw [sub_apply, one_apply_eq_self, smul_sub, hK']
    abel
  rw [hdec]
  have h1 : ‖(1 - P₁) (A t₁ - A t₀ - h • f)‖ ≤ M * h := (hP₁.compl.norm_le _).trans hD
  have h2 : ‖h • (1 - P₁) ((1 - Q₀) f)‖ ≤ h * ε := by
    rw [norm_smul, Real.norm_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left hε hh
  have h3 := norm_add₃_le (a := (1 - P₁) (A t₁ - A t₀ - h • f))
    (b := h • (1 - P₁) ((1 - Q₀) f)) (c := (1 - P₁) YK)
  linarith

variable {F : ℝ → E → E} {A : ℝ → E} {a b ρ L Lt B t₀ t₁ ε τ ϑ : ℝ}
  {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {Y₀ YK YL xS Y₁ : E}

/-- **Local error of an implicit BUG step near a reference solution.** Let `F` be `L`-Lipschitz
and bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b] ⊇ [t₀, t₁]`, and
Lipschitz in time with constant `Lt` on the tube: `‖F(t, x) - F(s, x)‖ ≤ Lt (t - s)` for `s ≤ t`
and `x` in the tube at both times. Let `(t₁ - t₀) L < 1`, let the stages of the implicit BUG step
(`IsImplicitBUGStep`) satisfy `‖YK - Y₀‖ ≤ B h`, `‖YL - Y₀‖ ≤ B h`, `‖xS - Y₀‖ ≤ 3 B h`
(`h = t₁ - t₀`), and let `‖Y₀ - A t₀‖ + 4 B h < ρ`. Then the step has the local error

  `((L B + Lt) h² + h L η) / (1 - h L) + η + ϑ`, `η = 2 (h ((2 L B + Lt) h + ε) + τ)`,

the bound `implicitLocalBound` of `IsImplicitBUGStep.local_error` with one-sided constant `L`.
Nothing is assumed about `F` outside the tube. -/
theorem IsImplicitBUGStep.hasLocalError_of_tube
    (hs : IsImplicitBUGStep F ε τ ϑ P₀ Q₀ P₁ Q₁ t₁ (t₁ - t₀) Y₀ YK YL xS Y₁)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → (s, x) ∈ tubeSet A a b ρ → (t, x) ∈ tubeSet A a b ρ →
      ‖F t x - F s x‖ ≤ Lt * (t - s))
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hhL : (t₁ - t₀) * L < 1)
    (hA : ODESolution F A t₀ t₁) (hK : ‖YK - Y₀‖ ≤ B * (t₁ - t₀))
    (hYL : ‖YL - Y₀‖ ≤ B * (t₁ - t₀)) (hS : ‖xS - Y₀‖ ≤ 3 * B * (t₁ - t₀))
    (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Y₁ (implicitLocalBound L Lt B L (t₁ - t₀)
      (2 * implicitCaptureBound L Lt B (t₁ - t₀) ε τ) ϑ) := by
  intro Φ hΦ hΦ₀
  set h := t₁ - t₀ with hh_def
  have hh : 0 ≤ h := sub_nonneg.2 h01
  have hBh : 0 ≤ B * h := mul_nonneg hB hh
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (Y₀ - A t₀)]
  have ht₁ : t₁ = t₀ + h := by rw [hh_def]; ring
  have hab : ∀ t ∈ Icc t₀ t₁, t ∈ Icc a b := fun t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩
  have hmem₁ : t₁ ∈ Icc t₀ t₁ := ⟨h01, le_rfl⟩
  -- the reference solution and the exact flow move at speed at most `B`
  have hAt : ∀ t ∈ Icc t₀ t₁, ‖A t - A t₀‖ ≤ B * h := fun t ht =>
    (hA.norm_sub_le (hFB.along hρ ha hb) t ht).trans
      (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB)
  have hnear := ODESolution.near_of_comp_proj (Ψ := fun x => x) hΦ (fun x => le_rfl) hFB hB ha
    hb hA (by rw [hΦ₀]; linarith)
  have hΦt : ∀ t ∈ Icc t₀ t₁, ‖Φ t - Y₀‖ ≤ B * h := fun t ht => by
    have := (hnear t ht).2
    rw [hΦ₀] at this
    exact this.trans (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB)
  -- every point within `R` of `Y₀` with `R + ‖Y₀ - A t₀‖ + B h ≤ ρ` lies in the tube
  have htube : ∀ (x : E) (R : ℝ), ‖x - Y₀‖ ≤ R → R + ‖Y₀ - A t₀‖ + B * h ≤ ρ →
      ∀ t ∈ Icc t₀ t₁, ‖x - A t‖ ≤ ρ := fun x R hx hR t ht => by
    have e : x - A t = (x - Y₀) + (Y₀ - A t₀) - (A t - A t₀) := by abel
    rw [e]
    have h1 := norm_sub_le ((x - Y₀) + (Y₀ - A t₀)) (A t - A t₀)
    have h2 := norm_add_le (x - Y₀) (Y₀ - A t₀)
    linarith [hAt t ht]
  have hYKt : ∀ t ∈ Icc t₀ t₁, ‖YK - A t‖ ≤ ρ := htube YK _ hK (by linarith)
  have hYLt : ∀ t ∈ Icc t₀ t₁, ‖YL - A t‖ ≤ ρ := htube YL _ hYL (by linarith)
  have hxSt : ‖xS - A t₁‖ ≤ ρ := htube xS _ hS (by linarith) t₁ hmem₁
  have hΦ₁t : ∀ t ∈ Icc t₀ t₁, ‖Φ t₁ - A t‖ ≤ ρ := htube (Φ t₁) _ (hΦt t₁ hmem₁) (by linarith)
  have hΦtt : ∀ t ∈ Icc t₀ t₁, ‖Φ t - A t‖ ≤ ρ := fun t ht => (hnear t ht).1.le
  -- the field along the flow, compared with a stage `Z` near `Y₀`
  have hMZ : ∀ Z : E, ‖Z - Y₀‖ ≤ B * h → (∀ t ∈ Icc t₀ t₁, ‖Z - A t‖ ≤ ρ) →
      ∀ t ∈ Ico t₀ t₁, ‖F t (Φ t) - F t₁ Z‖ ≤ (2 * L * B + Lt) * h := by
    intro Z hZ hZt t ht
    have htI : t ∈ Icc t₀ t₁ := Ico_subset_Icc_self ht
    have h1 : ‖F t (Φ t) - F t Z‖ ≤ L * ‖Φ t - Z‖ :=
      hFL t (hab t htI) _ _ (hΦtt t htI) (hZt t htI)
    have h2 : ‖F t₁ Z - F t Z‖ ≤ Lt * (t₁ - t) :=
      hFt t t₁ Z ht.2.le ⟨hab t htI, hZt t htI⟩ ⟨hab t₁ hmem₁, hZt t₁ hmem₁⟩
    have h3 : ‖Φ t - Z‖ ≤ 2 * B * h := by
      have e : Φ t - Z = (Φ t - Y₀) - (Z - Y₀) := by abel
      rw [e]
      linarith [norm_sub_le (Φ t - Y₀) (Z - Y₀), hΦt t htI]
    have e : F t (Φ t) - F t₁ Z = (F t (Φ t) - F t Z) - (F t₁ Z - F t Z) := by abel
    rw [e]
    have h4 := norm_sub_le (F t (Φ t) - F t Z) (F t₁ Z - F t Z)
    have h5 : L * ‖Φ t - Z‖ ≤ L * (2 * B * h) := mul_le_mul_of_nonneg_left h3 hL
    have h6 : Lt * (t₁ - t) ≤ Lt * h := mul_le_mul_of_nonneg_left (by linarith [ht.1]) hLt
    nlinarith
  -- capture of the exact flow by the new bases
  have hcK := implicit_kstep_capture_of_le hs.hP₁ ht₁ hh hΦ
    (by rw [hΦ₀]; exact hs.kstep) (hMZ YK hK hYKt) hs.kcap hs.knormal
  have hcL := implicit_kstep_capture_of_le hs.hQ₁ ht₁ hh hΦ
    (by rw [hΦ₀]; exact hs.lstep) (hMZ YL hYL hYLt) hs.lcap hs.lnormal
  set η := 2 * implicitCaptureBound L Lt B h ε τ with hη_def
  have hcap : ‖Φ t₁ - (P₁ * Q₁) (Φ t₁)‖ ≤ η := by
    have := norm_sub_apply_apply_le hs.hP₁ (Q := Q₁) (Φ t₁)
    change ‖Φ t₁ - P₁ (Q₁ (Φ t₁))‖ ≤ _
    rw [hη_def]
    unfold implicitCaptureBound
    linarith
  -- the implicit Euler defect of the exact flow
  have hdef : ‖Φ t₁ - Φ t₀ - h • F t₁ (Φ t₁)‖ ≤ (L * B + Lt) * h * h := by
    refine hΦ.norm_sub_sub_smul_le ht₁ hh _ fun t ht => ?_
    have htI : t ∈ Icc t₀ t₁ := Ico_subset_Icc_self ht
    have hsub : ‖Φ t₁ - Φ t‖ ≤ B * (t₁ - t) := by
      refine (hΦ.mono ht.1 le_rfl).norm_sub_le (fun s hs => ?_) t₁ ⟨ht.2.le, le_rfl⟩
      have hsI : s ∈ Icc t₀ t₁ := ⟨ht.1.trans hs.1, hs.2.le⟩
      exact hFB s (hab s hsI) _ (hΦtt s hsI)
    have h1 : ‖F t (Φ t) - F t (Φ t₁)‖ ≤ L * ‖Φ t - Φ t₁‖ :=
      hFL t (hab t htI) _ _ (hΦtt t htI) (hΦ₁t t htI)
    have h2 : ‖F t₁ (Φ t₁) - F t (Φ t₁)‖ ≤ Lt * (t₁ - t) :=
      hFt t t₁ _ ht.2.le ⟨hab t htI, hΦ₁t t htI⟩ ⟨hab t₁ hmem₁, hΦ₁t t₁ hmem₁⟩
    have e : F t (Φ t) - F t₁ (Φ t₁) =
        (F t (Φ t) - F t (Φ t₁)) - (F t₁ (Φ t₁) - F t (Φ t₁)) := by abel
    rw [e]
    have h4 := norm_sub_le (F t (Φ t) - F t (Φ t₁)) (F t₁ (Φ t₁) - F t (Φ t₁))
    rw [norm_sub_rev (Φ t)] at h1
    have h5 : L * ‖Φ t₁ - Φ t‖ ≤ L * (B * h) :=
      mul_le_mul_of_nonneg_left (hsub.trans (mul_le_mul_of_nonneg_left (by linarith [ht.1])
        hB)) hL
    have h6 : Lt * (t₁ - t) ≤ Lt * h := mul_le_mul_of_nonneg_left (by linarith [ht.1]) hLt
    nlinarith
  -- the Galerkin step for the tube extension, which agrees with `F` at the points used
  have hρ' : 0 ≤ ρ := hρ
  have hGL : IsLipschitzField (tubeExt F A a b ρ) L := isLipschitzField_tubeExt hFL hL hρ'
  have hG₁ : ∀ x, ‖x - A t₁‖ ≤ ρ → tubeExt F A a b ρ t₁ x = F t₁ x := fun x hx =>
    tubeExt_eq (hab t₁ hmem₁) hx
  have hx : xS = (P₁ * Q₁) (Y₀ + h • tubeExt F A a b ρ t₁ xS) := by
    rw [hG₁ xS hxSt]
    exact hs.sstep
  have hgal := implicitGalerkin_error_le hs.proj hGL hh hx
    (hGL.isOneSidedLipschitzField t₁ xS ((P₁ * Q₁) (Φ t₁)))
  rw [hG₁ _ (hΦ₁t t₁ hmem₁), ← hΦ₀] at hgal
  have hpos : 0 < 1 - h * L := by linarith
  have hη0 : 0 ≤ η := by
    rw [hη_def]
    unfold implicitCaptureBound
    have := (norm_nonneg _).trans hs.kcap
    have := (norm_nonneg _).trans hs.knormal
    positivity
  have hG : ‖xS - (P₁ * Q₁) (Φ t₁)‖ ≤ ((L * B + Lt) * h ^ 2 + h * L * η) / (1 - h * L) := by
    rw [le_div_iff₀ hpos]
    have := mul_le_mul_of_nonneg_left hcap (mul_nonneg hh hL)
    nlinarith
  have hfin : ‖Y₁ - Φ t₁‖ ≤ ‖Y₁ - xS‖ + ‖xS - (P₁ * Q₁) (Φ t₁)‖ +
      ‖(P₁ * Q₁) (Φ t₁) - Φ t₁‖ := by
    have e : Y₁ - Φ t₁ = (Y₁ - xS) + (xS - (P₁ * Q₁) (Φ t₁)) + ((P₁ * Q₁) (Φ t₁) - Φ t₁) := by
      abel
    rw [e]
    exact norm_add₃_le
  rw [norm_sub_rev ((P₁ * Q₁) (Φ t₁))] at hfin
  unfold implicitLocalBound
  linarith [hs.trunc]

end Abstract

/-! ### Iterations that stay in a set -/

section Iterate

/-- Iterates of two maps that agree on an invariant set of one of them agree. -/
private theorem iterate_eq_of_eqOn {α : Type*} {f g : α → α} {s : Set α} (hfg : EqOn f g s)
    (hg : MapsTo g s s) {x : α} (hx : x ∈ s) (j : ℕ) : f^[j] x = g^[j] x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact hfg (hg.iterate j hx)

/-- The limit of an iteration that keeps the closed set `{y | ‖φ y - c‖ ≤ R}` invariant, started
in the set, lies in the set. -/
private theorem norm_sub_le_of_tendsto_iterate {α β : Type*} [TopologicalSpace α]
    [SeminormedAddCommGroup β] {g : α → α} {φ : α → β} (hφ : Continuous φ) {c : β} {R : ℝ}
    {x₀ x : α} (hx₀ : ‖φ x₀ - c‖ ≤ R) (hg : ∀ y, ‖φ y - c‖ ≤ R → ‖φ (g y) - c‖ ≤ R)
    (hlim : Tendsto (fun j => g^[j] x₀) atTop (𝓝 x)) : ‖φ x - c‖ ≤ R := by
  have hmaps : MapsTo g {y | ‖φ y - c‖ ≤ R} {y | ‖φ y - c‖ ≤ R} := fun y hy => hg y hy
  have hclosed : IsClosed {y | ‖φ y - c‖ ≤ R} :=
    isClosed_le (hφ.sub continuous_const).norm continuous_const
  exact hclosed.mem_of_tendsto hlim (Eventually.of_forall fun j => hmaps.iterate j hx₀)

end Iterate

namespace MatrixImplicitBUG

/-! ### The step relation and the core step -/

section Step

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}
  {F G : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ B : ℝ} {U₀ U₁ : Matrix m (Fin r) ℝ}
  {S₀ S₁ : Matrix (Fin r) (Fin r) ℝ} {V₀ V₁ : Matrix n (Fin r) ℝ} {K₁ : Matrix m (Fin r) ℝ}
  {L₁ : Matrix n (Fin r) ℝ}

/-- A step relates the matrices `U₀ S₀ V₀ᵀ` and `U₁ S₁ V₁ᵀ`. -/
theorem IsStep.stepRel (hs : IsStep F t₀ t₁ U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁) :
    stepRel F r t₀ t₁ (U₀ * S₀ * V₀ᵀ) (U₁ * S₁ * V₁ᵀ) :=
  ⟨U₀, S₀, V₀, K₁, L₁, U₁, V₁, S₁, rfl, hs, rfl⟩

/-- The result of a step has rank at most `r`. -/
theorem stepRel.rank_le {Y₀ Y₁ : Matrix m n ℝ} (h : stepRel F r t₀ t₁ Y₀ Y₁) : Y₁.rank ≤ r := by
  obtain ⟨U₀, S₀, V₀, K₁, L₁, U₁, V₁, S₁, -, -, rfl⟩ := h
  exact rank_mul_mul_transpose_le _ _ _

/-- A step can only be started from a matrix of rank at most `r`. -/
theorem stepRel.rank_start_le {Y₀ Y₁ : Matrix m n ℝ} (h : stepRel F r t₀ t₁ Y₀ Y₁) :
    Y₀.rank ≤ r := by
  obtain ⟨U₀, S₀, V₀, K₁, L₁, U₁, V₁, S₁, rfl, -, -⟩ := h
  exact rank_mul_mul_transpose_le _ _ _

/-- The new row basis reproduces the transposed L-stage: `L₁ᵀ V₁ V₁ᵀ = L₁ᵀ`. -/
private theorem IsStep.transpose_mul_lCap (hs : IsStep F t₀ t₁ U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁) :
    L₁ᵀ * (V₁ * V₁ᵀ) = L₁ᵀ := by
  conv_rhs => rw [← hs.lCap]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- **A step is an implicit BUG step of the core.** If the doubly normal components of the field
at the K- and L-stage are at most `ε`, a step is a step `IsMatrixImplicitBUGStep` with step size
`t₁ - t₀`, capture tolerance `0` (the new bases contain the stages) and no truncation. Hence the
error analysis of `LeanDLRA/Stiff/ImplicitBUG.lean` applies, through
`IsMatrixImplicitBUGStep.toAbstract`. -/
theorem IsStep.isMatrixImplicitBUGStep [DecidableEq m] [DecidableEq n] {ε : ℝ}
    (hs : IsStep F t₀ t₁ U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁)
    (hk : ‖(1 - U₁ * U₁ᵀ) * F t₁ (K₁ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hl : ‖(1 - U₀ * U₀ᵀ) * F t₁ (U₀ * L₁ᵀ) * (1 - V₁ * V₁ᵀ)‖ ≤ ε) :
    IsMatrixImplicitBUGStep F ε 0 0 t₁ (t₁ - t₀) U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ (U₁ * S₁ * V₁ᵀ) where
  orthU₀ := hs.orthU₀
  orthV₀ := hs.orthV₀
  kstep := hs.kStep
  lstep := hs.lStep
  orthU₁ := hs.orthU₁
  orthV₁ := hs.orthV₁
  kcap := by
    rw [← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hs.kCap, sub_self, Matrix.zero_mul,
      norm_zero]
  lcap := by
    rw [Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hs.transpose_mul_lCap, sub_self,
      Matrix.mul_zero, norm_zero]
  knormal := hk
  lnormal := hl
  sstep := hs.sStep
  trunc := by simp

/-! ### The stages stay near the start value -/

/-- One step of the K-iteration keeps the K-stage within `B h` of `Y₀`. -/
private theorem norm_kIter_sub_le (hV₀ : V₀ᵀ * V₀ = 1) (h01 : t₀ ≤ t₁) {R : ℝ}
    (hR : B * (t₁ - t₀) ≤ R) (hFB : ∀ x, ‖x - U₀ * S₀ * V₀ᵀ‖ ≤ R → ‖F t₁ x‖ ≤ B)
    (K : Matrix m (Fin r) ℝ) (hK : ‖K * V₀ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ B * (t₁ - t₀)) :
    ‖(U₀ * S₀ + (t₁ - t₀) • (F t₁ (K * V₀ᵀ) * V₀)) * V₀ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤
      B * (t₁ - t₀) := by
  have e : (U₀ * S₀ + (t₁ - t₀) • (F t₁ (K * V₀ᵀ) * V₀)) * V₀ᵀ - U₀ * S₀ * V₀ᵀ =
      (t₁ - t₀) • rightProj V₀ (F t₁ (K * V₀ᵀ)) := by
    rw [rightProj_apply, Matrix.add_mul, Matrix.smul_mul, add_sub_cancel_left]
  rw [e, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 h01), mul_comm]
  exact mul_le_mul_of_nonneg_right
    (((isOrthProj_rightProj hV₀).norm_le _).trans (hFB _ (hK.trans hR))) (sub_nonneg.2 h01)

/-- One step of the L-iteration keeps the L-stage within `B h` of `Y₀`. -/
private theorem norm_lIter_sub_le (hU₀ : U₀ᵀ * U₀ = 1) (h01 : t₀ ≤ t₁) {R : ℝ}
    (hR : B * (t₁ - t₀) ≤ R) (hFB : ∀ x, ‖x - U₀ * S₀ * V₀ᵀ‖ ≤ R → ‖F t₁ x‖ ≤ B)
    (L : Matrix n (Fin r) ℝ) (hL : ‖U₀ * Lᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ B * (t₁ - t₀)) :
    ‖U₀ * (V₀ * S₀ᵀ + (t₁ - t₀) • ((F t₁ (U₀ * Lᵀ))ᵀ * U₀))ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤
      B * (t₁ - t₀) := by
  have e : U₀ * (V₀ * S₀ᵀ + (t₁ - t₀) • ((F t₁ (U₀ * Lᵀ))ᵀ * U₀))ᵀ - U₀ * S₀ * V₀ᵀ =
      (t₁ - t₀) • leftProj U₀ (F t₁ (U₀ * Lᵀ)) := by
    rw [leftProj_apply]
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc]
    exact add_sub_cancel_left _ _
  rw [e, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 h01), mul_comm]
  exact mul_le_mul_of_nonneg_right
    (((isOrthProj_leftProj hU₀).norm_le _).trans (hFB _ (hL.trans hR))) (sub_nonneg.2 h01)

/-- One step of the S-iteration keeps the S-stage within `3 B h` of `Y₀`, if the Galerkin
projection of `Y₀` is within `2 B h` of `Y₀`. -/
private theorem norm_sIter_sub_le (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1) (h01 : t₀ ≤ t₁)
    (hFB : ∀ x, ‖x - U₀ * S₀ * V₀ᵀ‖ ≤ 3 * B * (t₁ - t₀) → ‖F t₁ x‖ ≤ B)
    (hc : ‖leftProj U₁ (rightProj V₁ (U₀ * S₀ * V₀ᵀ)) - U₀ * S₀ * V₀ᵀ‖ ≤ 2 * B * (t₁ - t₀))
    (S : Matrix (Fin r) (Fin r) ℝ) (hS : ‖U₁ * S * V₁ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ 3 * B * (t₁ - t₀)) :
    ‖U₁ * (U₁ᵀ * (U₀ * S₀ * V₀ᵀ + (t₁ - t₀) • F t₁ (U₁ * S * V₁ᵀ)) * V₁) * V₁ᵀ -
      U₀ * S₀ * V₀ᵀ‖ ≤ 3 * B * (t₁ - t₀) := by
  rw [← leftProj_rightProj_apply, map_add, map_smul, map_add, map_smul]
  have e : leftProj U₁ (rightProj V₁ (U₀ * S₀ * V₀ᵀ)) +
      (t₁ - t₀) • leftProj U₁ (rightProj V₁ (F t₁ (U₁ * S * V₁ᵀ))) - U₀ * S₀ * V₀ᵀ =
      (leftProj U₁ (rightProj V₁ (U₀ * S₀ * V₀ᵀ)) - U₀ * S₀ * V₀ᵀ) +
        (t₁ - t₀) • leftProj U₁ (rightProj V₁ (F t₁ (U₁ * S * V₁ᵀ))) := by abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.2 h01)]
  have h1 : ‖leftProj U₁ (rightProj V₁ (F t₁ (U₁ * S * V₁ᵀ)))‖ ≤ B :=
    ((isOrthProj_leftProj hU₁).norm_le _).trans (((isOrthProj_rightProj hV₁).norm_le _).trans
      (hFB _ hS))
  have h2 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 h01)
  linarith

/-- The K-stage localization from the limit of the K-iteration. -/
private theorem IsStep.norm_kStage_sub_le (hs : IsStep F t₀ t₁ U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁)
    (h01 : t₀ ≤ t₁) (hB : 0 ≤ B) {R : ℝ} (hR : B * (t₁ - t₀) ≤ R)
    (hFB : ∀ x, ‖x - U₀ * S₀ * V₀ᵀ‖ ≤ R → ‖F t₁ x‖ ≤ B) :
    ‖K₁ * V₀ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ B * (t₁ - t₀) :=
  norm_sub_le_of_tendsto_iterate (φ := fun K : Matrix m (Fin r) ℝ => K * V₀ᵀ)
    (Frobenius.rightMulCLM (m := m) V₀ᵀ).continuous
    (by simp only [sub_self, norm_zero]; exact mul_nonneg hB (sub_nonneg.2 h01))
    (norm_kIter_sub_le hs.orthV₀ h01 hR hFB) hs.kIter

/-- The L-stage localization from the limit of the L-iteration. -/
private theorem IsStep.norm_lStage_sub_le (hs : IsStep F t₀ t₁ U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁)
    (h01 : t₀ ≤ t₁) (hB : 0 ≤ B) {R : ℝ} (hR : B * (t₁ - t₀) ≤ R)
    (hFB : ∀ x, ‖x - U₀ * S₀ * V₀ᵀ‖ ≤ R → ‖F t₁ x‖ ≤ B) :
    ‖U₀ * L₁ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ B * (t₁ - t₀) :=
  norm_sub_le_of_tendsto_iterate (φ := fun L : Matrix n (Fin r) ℝ => U₀ * Lᵀ)
    ((Frobenius.leftMulCLM (n := n) U₀).comp Frobenius.transposeCLM).continuous
    (by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, sub_self,
        norm_zero]
      exact mul_nonneg hB (sub_nonneg.2 h01))
    (norm_lIter_sub_le hs.orthU₀ h01 hR hFB) hs.lIter

/-- The Galerkin projection `U₁ U₁ᵀ Y₀ V₁ V₁ᵀ` of the start value lies within `2 B h` of `Y₀` if
the K- and L-stage lie within `B h`: the new bases contain the stages. -/
private theorem IsStep.norm_galerkin_sub_le (hs : IsStep F t₀ t₁ U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁)
    (hK : ‖K₁ * V₀ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ B * (t₁ - t₀))
    (hL : ‖U₀ * L₁ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ B * (t₁ - t₀)) :
    ‖leftProj U₁ (rightProj V₁ (U₀ * S₀ * V₀ᵀ)) - U₀ * S₀ * V₀ᵀ‖ ≤ 2 * B * (t₁ - t₀) := by
  have hP₁ := isOrthProj_leftProj (n := n) hs.orthU₁
  have hQ₁ := isOrthProj_rightProj (m := m) hs.orthV₁
  have hcK : ‖(1 - leftProj U₁) (U₀ * S₀ * V₀ᵀ)‖ ≤ B * (t₁ - t₀) := by
    have e : (1 - leftProj U₁) (U₀ * S₀ * V₀ᵀ) =
        (1 - leftProj U₁) (U₀ * S₀ * V₀ᵀ - K₁ * V₀ᵀ) := by
      have hYK : leftProj U₁ (K₁ * V₀ᵀ) = K₁ * V₀ᵀ := by
        rw [leftProj_apply, ← Matrix.mul_assoc, hs.kCap]
      have hz : (1 - leftProj U₁) (K₁ * V₀ᵀ) = 0 := by
        change K₁ * V₀ᵀ - leftProj U₁ (K₁ * V₀ᵀ) = 0
        rw [hYK, sub_self]
      rw [map_sub, hz, sub_zero]
    rw [e, ← norm_neg, ← map_neg, neg_sub]
    exact (hP₁.compl.norm_le _).trans hK
  have hcL : ‖(1 - rightProj V₁) (U₀ * S₀ * V₀ᵀ)‖ ≤ B * (t₁ - t₀) := by
    have e : (1 - rightProj V₁) (U₀ * S₀ * V₀ᵀ) =
        (1 - rightProj V₁) (U₀ * S₀ * V₀ᵀ - U₀ * L₁ᵀ) := by
      have hYL : rightProj V₁ (U₀ * L₁ᵀ) = U₀ * L₁ᵀ := by
        rw [rightProj_apply, Matrix.mul_assoc, Matrix.mul_assoc, hs.transpose_mul_lCap]
      have hz : (1 - rightProj V₁) (U₀ * L₁ᵀ) = 0 := by
        change U₀ * L₁ᵀ - rightProj V₁ (U₀ * L₁ᵀ) = 0
        rw [hYL, sub_self]
      rw [map_sub, hz, sub_zero]
    rw [e, ← norm_neg, ← map_neg, neg_sub]
    exact (hQ₁.compl.norm_le _).trans hL
  rw [norm_sub_rev]
  have := norm_sub_apply_apply_le hP₁ (Q := rightProj V₁) (U₀ * S₀ * V₀ᵀ)
  linarith

/-- The start of the S-iteration is the Galerkin projection of the start value. -/
private theorem mul_galerkinStart_mul_eq :
    U₁ * (U₁ᵀ * U₀ * S₀ * (V₀ᵀ * V₁)) * V₁ᵀ = leftProj U₁ (rightProj V₁ (U₀ * S₀ * V₀ᵀ)) := by
  rw [leftProj_rightProj_apply]
  simp only [Matrix.mul_assoc]

/-- **The stages of a step stay near the start value.** Let `h = t₁ - t₀ ≥ 0`, `B ≥ 0`, and let
`‖F(t₁, x)‖ ≤ B` for all `x` within `3 B h` of `Y₀ = U₀ S₀ V₀ᵀ`. Then the K-stage `K₁ V₀ᵀ` and the
L-stage `U₀ L₁ᵀ` lie within `B h` of `Y₀`, and the S-stage `U₁ S₁ V₁ᵀ` within `3 B h`: every
iterate of the fixed-point iterations does, and so does the limit. -/
theorem IsStep.norm_stage_sub_le (hs : IsStep F t₀ t₁ U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁) (h01 : t₀ ≤ t₁)
    (hB : 0 ≤ B) (hFB : ∀ x, ‖x - U₀ * S₀ * V₀ᵀ‖ ≤ 3 * B * (t₁ - t₀) → ‖F t₁ x‖ ≤ B) :
    ‖K₁ * V₀ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ B * (t₁ - t₀) ∧ ‖U₀ * L₁ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ B * (t₁ - t₀) ∧
      ‖U₁ * S₁ * V₁ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ 3 * B * (t₁ - t₀) := by
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hR : B * (t₁ - t₀) ≤ 3 * B * (t₁ - t₀) := by linarith
  have hK := hs.norm_kStage_sub_le h01 hB hR hFB
  have hL := hs.norm_lStage_sub_le h01 hB hR hFB
  have hc := hs.norm_galerkin_sub_le hK hL
  refine ⟨hK, hL, norm_sub_le_of_tendsto_iterate
    (φ := fun S : Matrix (Fin r) (Fin r) ℝ => U₁ * S * V₁ᵀ)
    (Frobenius.sandwichCLM U₁ V₁ᵀ).continuous ?_
    (norm_sIter_sub_le hs.orthU₁ hs.orthV₁ h01 hFB hc) hs.sIter⟩
  change ‖U₁ * (U₁ᵀ * U₀ * S₀ * (V₀ᵀ * V₁)) * V₁ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ 3 * B * (t₁ - t₀)
  rw [mul_galerkinStart_mul_eq]
  linarith

/-- **A step depends on the field only near the start value.** Let `G` be bounded by `B` at
time `t₁` on the ball of radius `3 B h` around `Y₀ = U₀ S₀ V₀ᵀ` (`h = t₁ - t₀ ≥ 0`), and let `F`
agree with `G` there. Then a step for `G` is a step for `F`: the stages and all iterates of the
fixed-point iterations lie in the ball (`MatrixImplicitBUG.IsStep.norm_stage_sub_le`). -/
theorem IsStep.congr_field (hs : IsStep G t₀ t₁ U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁) (h01 : t₀ ≤ t₁)
    (hB : 0 ≤ B) (hGB : ∀ x, ‖x - U₀ * S₀ * V₀ᵀ‖ ≤ 3 * B * (t₁ - t₀) → ‖G t₁ x‖ ≤ B)
    (hFG : ∀ x, ‖x - U₀ * S₀ * V₀ᵀ‖ ≤ 3 * B * (t₁ - t₀) → F t₁ x = G t₁ x) :
    IsStep F t₀ t₁ U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ := by
  obtain ⟨hK, hL, hS⟩ := hs.norm_stage_sub_le h01 hB hGB
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hR : B * (t₁ - t₀) ≤ 3 * B * (t₁ - t₀) := by linarith
  have hc := hs.norm_galerkin_sub_le hK hL
  -- the three iterations of `F` and `G` coincide
  have hKit : (fun j => (fun K => U₀ * S₀ + (t₁ - t₀) • (F t₁ (K * V₀ᵀ) * V₀))^[j] (U₀ * S₀)) =
      fun j => (fun K => U₀ * S₀ + (t₁ - t₀) • (G t₁ (K * V₀ᵀ) * V₀))^[j] (U₀ * S₀) := by
    funext j
    refine iterate_eq_of_eqOn (s := {K | ‖K * V₀ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ B * (t₁ - t₀)})
      (fun K hK' => ?_) (fun K hK' => norm_kIter_sub_le hs.orthV₀ h01 hR hGB K hK') ?_ j
    · have hK'' : ‖K * V₀ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ B * (t₁ - t₀) := hK'
      rw [hFG _ (hK''.trans hR)]
    · change ‖U₀ * S₀ * V₀ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ B * (t₁ - t₀)
      rw [sub_self, norm_zero]
      exact hBh
  have hLit : (fun j => (fun L => V₀ * S₀ᵀ + (t₁ - t₀) • ((F t₁ (U₀ * Lᵀ))ᵀ * U₀))^[j]
      (V₀ * S₀ᵀ)) = fun j => (fun L => V₀ * S₀ᵀ + (t₁ - t₀) • ((G t₁ (U₀ * Lᵀ))ᵀ * U₀))^[j]
      (V₀ * S₀ᵀ) := by
    funext j
    refine iterate_eq_of_eqOn (s := {L | ‖U₀ * Lᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ B * (t₁ - t₀)})
      (fun L hL' => ?_) (fun L hL' => norm_lIter_sub_le hs.orthU₀ h01 hR hGB L hL') ?_ j
    · have hL'' : ‖U₀ * Lᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ B * (t₁ - t₀) := hL'
      rw [hFG _ (hL''.trans hR)]
    · change ‖U₀ * (V₀ * S₀ᵀ)ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ B * (t₁ - t₀)
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, sub_self,
        norm_zero]
      exact hBh
  have hSit : (fun j => (fun S => U₁ᵀ * (U₀ * S₀ * V₀ᵀ + (t₁ - t₀) • F t₁ (U₁ * S * V₁ᵀ)) *
      V₁)^[j] (U₁ᵀ * U₀ * S₀ * (V₀ᵀ * V₁))) = fun j => (fun S => U₁ᵀ * (U₀ * S₀ * V₀ᵀ +
      (t₁ - t₀) • G t₁ (U₁ * S * V₁ᵀ)) * V₁)^[j] (U₁ᵀ * U₀ * S₀ * (V₀ᵀ * V₁)) := by
    funext j
    refine iterate_eq_of_eqOn (s := {S | ‖U₁ * S * V₁ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ 3 * B * (t₁ - t₀)})
      (fun S hS' => ?_)
      (fun S hS' => norm_sIter_sub_le hs.orthU₁ hs.orthV₁ h01 hGB hc S hS') ?_ j
    · have hS'' : ‖U₁ * S * V₁ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ 3 * B * (t₁ - t₀) := hS'
      rw [hFG _ hS'']
    · change ‖U₁ * (U₁ᵀ * U₀ * S₀ * (V₀ᵀ * V₁)) * V₁ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ 3 * B * (t₁ - t₀)
      rw [mul_galerkinStart_mul_eq]
      linarith
  exact
    { orthU₀ := hs.orthU₀
      orthV₀ := hs.orthV₀
      kStep := by rw [hFG _ (hK.trans hR)]; exact hs.kStep
      kIter := by rw [hKit]; exact hs.kIter
      lStep := by rw [hFG _ (hL.trans hR)]; exact hs.lStep
      lIter := by rw [hLit]; exact hs.lIter
      orthU₁ := hs.orthU₁
      kCap := hs.kCap
      orthV₁ := hs.orthV₁
      lCap := hs.lCap
      sStep := by rw [hFG _ hS]; exact hs.sStep
      sIter := by rw [hSit]; exact hs.sIter }

/-! ### Steps near a reference solution -/

section Tube

variable {A : ℝ → Matrix m n ℝ} {a b ρ : ℝ}

/-- Points within `3 B h` of a start value with `‖Y₀ - A t₀‖ + 4 B h < ρ` lie in the tube at
time `t₁`. -/
private theorem norm_sub_le_of_near (hFB : IsBoundedOnTube F A a b ρ B) (ha : a ≤ t₀)
    (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁) {Y₀ : Matrix m n ℝ}
    (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) (hB : 0 ≤ B) (x : Matrix m n ℝ)
    (hx : ‖x - Y₀‖ ≤ 3 * B * (t₁ - t₀)) : ‖x - A t₁‖ ≤ ρ := by
  have hρ : 0 ≤ ρ := by
    linarith [norm_nonneg (Y₀ - A t₀), mul_nonneg hB (sub_nonneg.2 h01)]
  have hA₁ : ‖A t₁ - A t₀‖ ≤ B * (t₁ - t₀) :=
    hA.norm_sub_le (hFB.along hρ ha hb) t₁ ⟨h01, le_rfl⟩
  have e : x - A t₁ = (x - Y₀) + (Y₀ - A t₀) - (A t₁ - A t₀) := by abel
  rw [e]
  have h1 := norm_sub_le ((x - Y₀) + (Y₀ - A t₀)) (A t₁ - A t₀)
  have h2 := norm_add_le (x - Y₀) (Y₀ - A t₀)
  linarith

/-- **Near a reference solution, the steps of the tube extension are the steps of the field.**
Let `F` be bounded by `B` on the tube of radius `ρ` around a solution `A` over
`[a, b] ⊇ [t₀, t₁]`. If `‖U₀ S₀ V₀ᵀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, a step for
`tubeExt F A a b ρ` is the same as a step for `F`. -/
theorem isStep_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    IsStep (tubeExt F A a b ρ) t₀ t₁ U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ ↔
      IsStep F t₀ t₁ U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ := by
  have hρ : 0 ≤ ρ := by
    linarith [norm_nonneg (U₀ * S₀ * V₀ᵀ - A t₀), mul_nonneg hB (sub_nonneg.2 h01)]
  have hmem : t₁ ∈ Icc a b := ⟨ha.trans h01, hb⟩
  have hin := norm_sub_le_of_near hFB ha hb h01 hA hsmall hB
  have heq : ∀ x, ‖x - U₀ * S₀ * V₀ᵀ‖ ≤ 3 * B * (t₁ - t₀) → tubeExt F A a b ρ t₁ x = F t₁ x :=
    fun x hx => tubeExt_eq hmem (hin x hx)
  constructor
  · intro hs
    exact hs.congr_field h01 hB (fun x _ => isBoundedField_tubeExt hFB hB hρ t₁ x)
      fun x hx => (heq x hx).symm
  · intro hs
    exact hs.congr_field h01 hB (fun x hx => hFB t₁ hmem x (hin x hx)) heq

/-- **Near a reference solution, the step relation of the tube extension is that of the
field**: if `‖Y₀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, then `stepRel (tubeExt F A a b ρ) r t₀ t₁ Y₀ Y₁`
holds if and only if `stepRel F r t₀ t₁ Y₀ Y₁` does. -/
theorem stepRel_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    {Y₀ Y₁ : Matrix m n ℝ} (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    stepRel (tubeExt F A a b ρ) r t₀ t₁ Y₀ Y₁ ↔ stepRel F r t₀ t₁ Y₀ Y₁ := by
  constructor
  · rintro ⟨U₀, S₀, V₀, K₁, L₁, U₁, V₁, S₁, rfl, hs, rfl⟩
    exact ⟨U₀, S₀, V₀, K₁, L₁, U₁, V₁, S₁, rfl,
      (isStep_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 hs, rfl⟩
  · rintro ⟨U₀, S₀, V₀, K₁, L₁, U₁, V₁, S₁, rfl, hs, rfl⟩
    exact ⟨U₀, S₀, V₀, K₁, L₁, U₁, V₁, S₁, rfl,
      (isStep_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).2 hs, rfl⟩

/-- **Local error of a step near a reference solution.** Let `F` be `L`-Lipschitz and bounded
by `B` on the tube of radius `ρ` around a solution `A` over `[a, b] ⊇ [t₀, t₁]`, Lipschitz in
time with constant `Lt` on the tube, and let its normal component at the rank-`r` matrices of the
tube be at most `ε` (`FactoredNormalBoundOn`). If `(t₁ - t₀) L < 1` and
`‖U₀ S₀ V₀ᵀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, the step has the local error
`implicitLocalBound L Lt B L h η 0` with `h = t₁ - t₀`, `η = 2 h ((2 L B + Lt) h + ε)`: the
bound of `IsMatrixImplicitBUGStep.local_error` with one-sided constant `L`, capture tolerance `0`
and no truncation. Nothing is assumed about `F` outside the tube. -/
theorem IsStep.hasLocalError_of_tube [DecidableEq m] [DecidableEq n] {L Lt ε : ℝ}
    (hs : IsStep F t₀ t₁ U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε) (hFL : IsLipschitzOnTube F A a b ρ L)
    (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → (s, x) ∈ tubeSet A a b ρ → (t, x) ∈ tubeSet A a b ρ →
      ‖F t x - F s x‖ ≤ Lt * (t - s))
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hhL : (t₁ - t₀) * L < 1)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ (U₀ * S₀ * V₀ᵀ) (U₁ * S₁ * V₁ᵀ)
      (implicitLocalBound L Lt B L (t₁ - t₀)
        (2 * implicitCaptureBound L Lt B (t₁ - t₀) ε 0) 0) := by
  have hmem : t₁ ∈ Icc a b := ⟨ha.trans h01, hb⟩
  have hin := norm_sub_le_of_near hFB ha hb h01 hA hsmall hB
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  obtain ⟨hK, hYL, hS⟩ := hs.norm_stage_sub_le h01 hB fun x hx => hFB t₁ hmem x (hin x hx)
  have eK : U₁ * (U₁ᵀ * K₁) * V₀ᵀ = K₁ * V₀ᵀ := by rw [← Matrix.mul_assoc, hs.kCap]
  have eL : U₀ * (L₁ᵀ * V₁) * V₁ᵀ = U₀ * L₁ᵀ := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hs.transpose_mul_lCap]
  have hk : ‖(1 - U₁ * U₁ᵀ) * F t₁ (K₁ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε := by
    have := hε t₁ U₁ V₀ (U₁ᵀ * K₁) hs.orthU₁ hs.orthV₀
      (by rw [eK]; exact ⟨hmem, hin _ (hK.trans (by linarith))⟩)
    rwa [eK] at this
  have hl : ‖(1 - U₀ * U₀ᵀ) * F t₁ (U₀ * L₁ᵀ) * (1 - V₁ * V₁ᵀ)‖ ≤ ε := by
    have := hε t₁ U₀ V₁ (L₁ᵀ * V₁) hs.orthU₀ hs.orthV₁
      (by rw [eL]; exact ⟨hmem, hin _ (hYL.trans (by linarith))⟩)
    rwa [eL] at this
  exact (hs.isMatrixImplicitBUGStep hk hl).toAbstract.hasLocalError_of_tube hFL hL hFB hB hLt
    hFt ha hb h01 hhL hA hK hYL hS hsmall

/-- **Local error of a step near a reference solution, simplified for `(t₁ - t₀) L ≤ 1/2`:**
`(t₁ - t₀) ((14 L B + 8 Lt) (t₁ - t₀) + 6 ε)`, the constants of `implicitBUG_global_error_le`.
The hypotheses are those of `MatrixImplicitBUG.IsStep.hasLocalError_of_tube` and `0 ≤ ε`. -/
theorem IsStep.hasLocalError_of_tube_le [DecidableEq m] [DecidableEq n] {L Lt ε : ℝ}
    (hs : IsStep F t₀ t₁ U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε) (hε₀ : 0 ≤ ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → (s, x) ∈ tubeSet A a b ρ → (t, x) ∈ tubeSet A a b ρ →
      ‖F t x - F s x‖ ≤ Lt * (t - s))
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hhL : (t₁ - t₀) * L ≤ 1 / 2)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ (U₀ * S₀ * V₀ᵀ) (U₁ * S₁ * V₁ᵀ)
      ((t₁ - t₀) * ((14 * L * B + 8 * Lt) * (t₁ - t₀) + 6 * ε)) := by
  have hh : 0 ≤ t₁ - t₀ := sub_nonneg.2 h01
  refine (hs.hasLocalError_of_tube hε hFL hL hFB hB hLt hFt ha hb h01 (by linarith) hA
    hsmall).mono ?_
  have hcap : 0 ≤ implicitCaptureBound L Lt B (t₁ - t₀) ε 0 := by
    unfold implicitCaptureBound
    have : 0 ≤ 2 * L * B + Lt := by positivity
    exact add_nonneg (mul_nonneg hh (add_nonneg (mul_nonneg this hh) hε₀)) le_rfl
  refine (implicitLocalBound_le (ϑ := 0) hL hLt hB hh (by linarith) hhL
    (mul_nonneg zero_le_two hcap)).trans (le_of_eq ?_)
  unfold implicitCaptureBound
  ring

end Tube

end Step

/-! ### Existence of a step for globally Lipschitz fields -/

section Exists

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ} {G : ℝ → Matrix m n ℝ → Matrix m n ℝ}
  {t₀ t₁ L : ℝ} {U₀ U₁ : Matrix m (Fin r) ℝ} {S₀ S₁ : Matrix (Fin r) (Fin r) ℝ}
  {V₀ V₁ : Matrix n (Fin r) ℝ} {K₁ : Matrix m (Fin r) ℝ} {L₁ : Matrix n (Fin r) ℝ}

/-- The map of the K-iteration is a contraction with constant `h L`. -/
private theorem contractingWith_kIter (hG : IsLipschitzField G L) (h01 : t₀ ≤ t₁)
    (hhL : (t₁ - t₀) * L < 1) (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (hV₀ : V₀ᵀ * V₀ = 1) :
    ContractingWith (Real.toNNReal ((t₁ - t₀) * L))
      (fun K : Matrix m (Fin r) ℝ => U₀ * S₀ + (t₁ - t₀) • (G t₁ (K * V₀ᵀ) * V₀)) := by
  refine ⟨Real.toNNReal_lt_one.2 hhL, LipschitzWith.of_dist_le_mul fun K K' => ?_⟩
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, ← Matrix.sub_mul,
    norm_smul, Real.norm_of_nonneg (sub_nonneg.2 h01)]
  calc (t₁ - t₀) * ‖(G t₁ (K * V₀ᵀ) - G t₁ (K' * V₀ᵀ)) * V₀‖
      ≤ (t₁ - t₀) * (L * ‖K * V₀ᵀ - K' * V₀ᵀ‖) :=
        mul_le_mul_of_nonneg_left ((norm_mul_le_of_orthonormal hV₀ _).trans (hG t₁ _ _))
          (sub_nonneg.2 h01)
    _ = (t₁ - t₀) * L * ‖K - K'‖ := by
        rw [← Matrix.sub_mul, Frobenius.norm_mul_transpose_of_orthonormal hV₀, mul_assoc]
    _ ≤ Real.toNNReal ((t₁ - t₀) * L) * ‖K - K'‖ :=
        mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _)

/-- The map of the L-iteration is a contraction with constant `h L`. -/
private theorem contractingWith_lIter (hG : IsLipschitzField G L) (h01 : t₀ ≤ t₁)
    (hhL : (t₁ - t₀) * L < 1) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (hU₀ : U₀ᵀ * U₀ = 1) :
    ContractingWith (Real.toNNReal ((t₁ - t₀) * L))
      (fun M : Matrix n (Fin r) ℝ => V₀ * S₀ᵀ + (t₁ - t₀) • ((G t₁ (U₀ * Mᵀ))ᵀ * U₀)) := by
  refine ⟨Real.toNNReal_lt_one.2 hhL, LipschitzWith.of_dist_le_mul fun M M' => ?_⟩
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, ← Matrix.sub_mul,
    ← Matrix.transpose_sub, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 h01)]
  calc (t₁ - t₀) * ‖(G t₁ (U₀ * Mᵀ) - G t₁ (U₀ * M'ᵀ))ᵀ * U₀‖
      ≤ (t₁ - t₀) * (L * ‖U₀ * Mᵀ - U₀ * M'ᵀ‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.2 h01)
        refine (norm_mul_le_of_orthonormal hU₀ _).trans ?_
        rw [Frobenius.norm_transpose]
        exact hG t₁ _ _
    _ = (t₁ - t₀) * L * ‖M - M'‖ := by
        rw [← Matrix.mul_sub, ← Matrix.transpose_sub, Frobenius.norm_mul_of_orthonormal hU₀,
          Frobenius.norm_transpose, mul_assoc]
    _ ≤ Real.toNNReal ((t₁ - t₀) * L) * ‖M - M'‖ :=
        mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _)

/-- The map of the S-iteration is a contraction with constant `h L`. -/
private theorem contractingWith_sIter (hG : IsLipschitzField G L) (h01 : t₀ ≤ t₁)
    (hhL : (t₁ - t₀) * L < 1) (Y₀ : Matrix m n ℝ) (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1) :
    ContractingWith (Real.toNNReal ((t₁ - t₀) * L))
      (fun S : Matrix (Fin r) (Fin r) ℝ => U₁ᵀ * (Y₀ + (t₁ - t₀) • G t₁ (U₁ * S * V₁ᵀ)) * V₁) := by
  refine ⟨Real.toNNReal_lt_one.2 hhL, LipschitzWith.of_dist_le_mul fun S S' => ?_⟩
  have e : U₁ᵀ * (Y₀ + (t₁ - t₀) • G t₁ (U₁ * S * V₁ᵀ)) * V₁ -
      U₁ᵀ * (Y₀ + (t₁ - t₀) • G t₁ (U₁ * S' * V₁ᵀ)) * V₁ =
      (t₁ - t₀) • (U₁ᵀ * (G t₁ (U₁ * S * V₁ᵀ) - G t₁ (U₁ * S' * V₁ᵀ)) * V₁) := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, add_sub_add_left_eq_sub, ← smul_sub,
      Matrix.mul_smul, Matrix.smul_mul]
  rw [dist_eq_norm, dist_eq_norm, e, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 h01)]
  calc (t₁ - t₀) * ‖U₁ᵀ * (G t₁ (U₁ * S * V₁ᵀ) - G t₁ (U₁ * S' * V₁ᵀ)) * V₁‖
      ≤ (t₁ - t₀) * (L * ‖U₁ * S * V₁ᵀ - U₁ * S' * V₁ᵀ‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.2 h01)
        exact (norm_mul_le_of_orthonormal hV₁ _).trans
          ((norm_transpose_mul_le hU₁ _).trans (hG t₁ _ _))
    _ = (t₁ - t₀) * L * ‖S - S'‖ := by
        rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_assoc,
          Frobenius.norm_mul_of_orthonormal hU₁, Frobenius.norm_mul_transpose_of_orthonormal hV₁,
          mul_assoc]
    _ ≤ Real.toNNReal ((t₁ - t₀) * L) * ‖S - S'‖ :=
        mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _)

/-- **For a globally Lipschitz field and `h L < 1`, the stage equations determine a step.** Let
`G` be Lipschitz with constant `L` and `(t₁ - t₀) L < 1`, `t₀ ≤ t₁`. If the factors satisfy the
stage equations, the orthonormality and the capture conditions of `MatrixImplicitBUG.IsStep`,
then they form a step: each stage map is a contraction, so its fixed-point iteration converges
to its only fixed point, which is the given stage. The conditions on the iterations in
`MatrixImplicitBUG.IsStep` therefore ask nothing beyond the equations for such fields. -/
theorem IsStep.of_lipschitz (hG : IsLipschitzField G L) (h01 : t₀ ≤ t₁)
    (hhL : (t₁ - t₀) * L < 1) (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    (hK : K₁ = U₀ * S₀ + (t₁ - t₀) • (G t₁ (K₁ * V₀ᵀ) * V₀))
    (hL : L₁ = V₀ * S₀ᵀ + (t₁ - t₀) • ((G t₁ (U₀ * L₁ᵀ))ᵀ * U₀)) (hU₁ : U₁ᵀ * U₁ = 1)
    (hKcap : U₁ * U₁ᵀ * K₁ = K₁) (hV₁ : V₁ᵀ * V₁ = 1) (hLcap : V₁ * V₁ᵀ * L₁ = L₁)
    (hS : S₁ = U₁ᵀ * (U₀ * S₀ * V₀ᵀ + (t₁ - t₀) • G t₁ (U₁ * S₁ * V₁ᵀ)) * V₁) :
    IsStep G t₀ t₁ U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ := by
  have hcK := contractingWith_kIter hG h01 hhL U₀ S₀ hV₀
  have hcL := contractingWith_lIter hG h01 hhL S₀ V₀ hU₀
  have hcS := contractingWith_sIter hG h01 hhL (U₀ * S₀ * V₀ᵀ) hU₁ hV₁
  have eK : K₁ = ContractingWith.fixedPoint _ hcK := hcK.fixedPoint_unique hK.symm
  have eL : L₁ = ContractingWith.fixedPoint _ hcL := hcL.fixedPoint_unique hL.symm
  have eS : S₁ = ContractingWith.fixedPoint _ hcS := hcS.fixedPoint_unique hS.symm
  exact
    { orthU₀ := hU₀
      orthV₀ := hV₀
      kStep := hK
      kIter := by rw [eK]; exact hcK.tendsto_iterate_fixedPoint (U₀ * S₀)
      lStep := hL
      lIter := by rw [eL]; exact hcL.tendsto_iterate_fixedPoint (V₀ * S₀ᵀ)
      orthU₁ := hU₁
      kCap := hKcap
      orthV₁ := hV₁
      lCap := hLcap
      sStep := hS
      sIter := by rw [eS]; exact hcS.tendsto_iterate_fixedPoint _ }

/-- **A step exists for a globally Lipschitz field and `h L < 1`.** Let `G` be Lipschitz with
constant `L`, `t₀ ≤ t₁`, `(t₁ - t₀) L < 1`, `r ≤ m`, `r ≤ n`, and let `U₀`, `V₀` have orthonormal
columns. Then for every `S₀` there are `K₁`, `L₁`, `U₁`, `V₁`, `S₁` forming a step
(`MatrixImplicitBUG.IsStep`): the stages are the fixed points of contractions (Banach's fixed
point theorem), and the new bases come from QR steps. No continuity in time is needed: the field
is evaluated at `t₁` only. -/
theorem exists_isStep (hG : IsLipschitzField G L) (h01 : t₀ ≤ t₁) (hhL : (t₁ - t₀) * L < 1)
    (hU₀ : U₀ᵀ * U₀ = 1) (S₀ : Matrix (Fin r) (Fin r) ℝ) (hV₀ : V₀ᵀ * V₀ = 1)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) :
    ∃ (K₁ : Matrix m (Fin r) ℝ) (L₁ : Matrix n (Fin r) ℝ) (U₁ : Matrix m (Fin r) ℝ)
      (V₁ : Matrix n (Fin r) ℝ) (S₁ : Matrix (Fin r) (Fin r) ℝ),
      IsStep G t₀ t₁ U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ := by
  have hcK := contractingWith_kIter hG h01 hhL U₀ S₀ hV₀
  have hcL := contractingWith_lIter hG h01 hhL S₀ V₀ hU₀
  obtain ⟨U₁, hU₁, hKcap⟩ := MatrixBUG.exists_qr hrm (ContractingWith.fixedPoint _ hcK)
  obtain ⟨V₁, hV₁, hLcap⟩ := MatrixBUG.exists_qr hrn (ContractingWith.fixedPoint _ hcL)
  have hcS := contractingWith_sIter hG h01 hhL (U₀ * S₀ * V₀ᵀ) hU₁ hV₁
  exact ⟨_, _, U₁, V₁, _, IsStep.of_lipschitz hG h01 hhL hU₀ hV₀
    (ContractingWith.fixedPoint_isFixedPt hcK).symm (ContractingWith.fixedPoint_isFixedPt hcL).symm
    hU₁ hKcap hV₁ hLcap (ContractingWith.fixedPoint_isFixedPt hcS).symm⟩

/-- **A step exists from every start value of rank at most `r`**, for a globally Lipschitz field
with `(t₁ - t₀) L < 1` and `r ≤ m`, `r ≤ n`: factor `Y₀ = U₀ S₀ V₀ᵀ` with orthonormal `U₀`, `V₀`
(`exists_factor_of_rank_le`) and apply `MatrixImplicitBUG.exists_isStep`. -/
theorem exists_stepRel (hG : IsLipschitzField G L) (h01 : t₀ ≤ t₁) (hhL : (t₁ - t₀) * L < 1)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) : ∃ Y₁, stepRel G r t₀ t₁ Y₀ Y₁ := by
  obtain ⟨U₀, S₀, V₀, hU₀, hV₀, rfl⟩ := exists_factor_of_rank_le hY₀ hrm hrn
  obtain ⟨K₁, L₁, U₁, V₁, S₁, hs⟩ := exists_isStep hG h01 hhL hU₀ S₀ hV₀ hrm hrn
  exact ⟨_, hs.stepRel⟩

end Exists

/-! ### Non-vacuity: constant and linear fields -/

section Examples

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}

/-- **Non-vacuity of `implicit_kstep_capture_of_le`**, on `ℝ` as for `implicit_kstep_capture`:
the field `F = 1`, the solution `A t = t`, `Q₀ = 1`, the implicit K-step `YK = 0 + 1 · 1 = 1` and
the zero new basis `P₁ = 0` (`M = 0`, `ε = 0`, `τ = 1`); the bound `‖A 1‖ ≤ 1` is sharp. -/
example : ‖((1 : ℝ →L[ℝ] ℝ) - 0) ((fun t : ℝ => t) 1)‖ ≤ 0 * 1 + 1 * 0 + 1 :=
  implicit_kstep_capture_of_le (E := ℝ) (F := fun _ _ => 1) IsOrthProj.zero
    (t₀ := 0) (t₁ := 1) (h := 1) (by norm_num) zero_le_one
    ⟨continuousOn_id, fun t _ => by simpa using hasDerivWithinAt_id t _⟩
    (YK := 1) (Q₀ := 1) (by norm_num) (fun _ _ => by simp) (by norm_num) (by norm_num)

/-- **Non-vacuity of `MatrixImplicitBUG.exists_isStep`, `MatrixImplicitBUG.IsStep.of_lipschitz`
and `MatrixImplicitBUG.IsStep.stepRel`.** For the linear field `F(t, Y) = M Y + Y Nᵀ + G`
(Lipschitz constant `‖M‖ + ‖N‖`) and `h (‖M‖ + ‖N‖) < 1` a step exists from every factorization
with orthonormal `U₀`, `V₀`; its stage equations alone determine it, and it relates `U₀ S₀ V₀ᵀ` to
its result. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G : Matrix m n ℝ) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    (hhL : (t₁ - t₀) * (‖M‖ + ‖N‖) < 1) {U₀ : Matrix m (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (S₀ : Matrix (Fin r) (Fin r) ℝ) :
    ∃ Y₁, stepRel (fun _ Y => M * Y + Y * Nᵀ + G) r t₀ t₁ (U₀ * S₀ * V₀ᵀ) Y₁ := by
  obtain ⟨K₁, L₁, U₁, V₁, S₁, hs⟩ :=
    exists_isStep (isLipschitzField_linear M N G) h01 hhL hU₀ S₀ hV₀ hrm hrn
  have hs' := IsStep.of_lipschitz (isLipschitzField_linear M N G) h01 hhL hs.orthU₀ hs.orthV₀
    hs.kStep hs.lStep hs.orthU₁ hs.kCap hs.orthV₁ hs.lCap hs.sStep
  exact ⟨_, hs'.stepRel⟩

/-- **Non-vacuity of `MatrixImplicitBUG.exists_stepRel`, `MatrixImplicitBUG.stepRel.rank_le`
and `MatrixImplicitBUG.stepRel.rank_start_le`.** For the linear field `F(t, Y) = M Y + Y Nᵀ + G`
and `h (‖M‖ + ‖N‖) < 1` a step exists from every start value of rank at most `r`, and the start
value and the result of a step have rank at most `r`. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G : Matrix m n ℝ) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    (hhL : (t₁ - t₀) * (‖M‖ + ‖N‖) < 1) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) :
    ∃ Y₁, stepRel (fun _ Y => M * Y + Y * Nᵀ + G) r t₀ t₁ Y₀ Y₁ ∧ Y₀.rank ≤ r ∧ Y₁.rank ≤ r := by
  obtain ⟨Y₁, hY⟩ := exists_stepRel (isLipschitzField_linear M N G) h01 hhL hrm hrn hY₀
  exact ⟨Y₁, hY, hY.rank_start_le, hY.rank_le⟩

/-- **Non-vacuity of `MatrixImplicitBUG.IsStep.norm_stage_sub_le` and
`MatrixImplicitBUG.IsStep.congr_field`.** For the constant field `F(t, Y) = C` (bounded by `‖C‖`,
Lipschitz with constant `0`) a step exists from every factorization with orthonormal `U₀`, `V₀`.
Its result lies within `3 ‖C‖ h` of the start value, and it is a step of every field that equals
`C` at time `t₁` on the ball of radius `3 ‖C‖ h` around the start value. -/
example (C : Matrix m n ℝ) (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁) {U₀ : Matrix m (Fin r) ℝ}
    {V₀ : Matrix n (Fin r) ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (hF : ∀ x, ‖x - U₀ * S₀ * V₀ᵀ‖ ≤ 3 * ‖C‖ * (t₁ - t₀) → F t₁ x = C) :
    ∃ (K₁ : Matrix m (Fin r) ℝ) (L₁ : Matrix n (Fin r) ℝ) (U₁ : Matrix m (Fin r) ℝ)
      (V₁ : Matrix n (Fin r) ℝ) (S₁ : Matrix (Fin r) (Fin r) ℝ),
      IsStep F t₀ t₁ U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ ∧
        ‖U₁ * S₁ * V₁ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ 3 * ‖C‖ * (t₁ - t₀) := by
  have hG : IsLipschitzField (fun (_ : ℝ) (_ : Matrix m n ℝ) => C) 0 := fun _ _ _ => by simp
  obtain ⟨K₁, L₁, U₁, V₁, S₁, hs⟩ := exists_isStep hG h01 (by simp) hU₀ S₀ hV₀ hrm hrn
  have hB : ∀ x, ‖x - U₀ * S₀ * V₀ᵀ‖ ≤ 3 * ‖C‖ * (t₁ - t₀) → ‖C‖ ≤ ‖C‖ := fun _ _ => le_rfl
  exact ⟨K₁, L₁, U₁, V₁, S₁, hs.congr_field h01 (norm_nonneg C) hB hF,
    (hs.norm_stage_sub_le h01 (norm_nonneg C) hB).2.2⟩

/-- **Non-vacuity of `MatrixImplicitBUG.isStep_tubeExt_iff_of_near` and
`MatrixImplicitBUG.stepRel_tubeExt_iff_of_near`.** The linear field `F(t, Y) = M Y + Y Nᵀ + G`
with a stationary point `C` (`M C + C Nᵀ + G = 0`) is bounded by `(‖M‖ + ‖N‖) ρ` on the tube of
radius `ρ` around `A(t) = C`. If `h (‖M‖ + ‖N‖) < 1` and the start value `U₀ S₀ V₀ᵀ` satisfies
`‖U₀ S₀ V₀ᵀ - C‖ + 4 (‖M‖ + ‖N‖) ρ h < ρ`, a step of `F` exists, and it is a step of the tube
extension of `F`. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {t₀ t₁ ρ : ℝ} (hρ : 0 ≤ ρ) (h01 : t₀ ≤ t₁) (hhL : (t₁ - t₀) * (‖M‖ + ‖N‖) < 1)
    {U₀ : Matrix m (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} (hU₀ : U₀ᵀ * U₀ = 1)
    (hV₀ : V₀ᵀ * V₀ = 1) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (hsmall : ‖U₀ * S₀ * V₀ᵀ - C‖ + 4 * ((‖M‖ + ‖N‖) * ρ) * (t₁ - t₀) < ρ) :
    ∃ (K₁ : Matrix m (Fin r) ℝ) (L₁ : Matrix n (Fin r) ℝ) (U₁ : Matrix m (Fin r) ℝ)
      (V₁ : Matrix n (Fin r) ℝ) (S₁ : Matrix (Fin r) (Fin r) ℝ),
      IsStep (tubeExt (fun _ Y => M * Y + Y * Nᵀ + G) (fun _ => C) t₀ t₁ ρ) t₀ t₁ U₀ S₀ V₀
        K₁ L₁ U₁ V₁ S₁ ∧
      stepRel (tubeExt (fun _ Y => M * Y + Y * Nᵀ + G) (fun _ => C) t₀ t₁ ρ) r t₀ t₁
        (U₀ * S₀ * V₀ᵀ) (U₁ * S₁ * V₁ᵀ) := by
  have hP := dlraProblem_linear M N G C hC t₀ t₁ hρ
  obtain ⟨K₁, L₁, U₁, V₁, S₁, hs⟩ :=
    exists_isStep (isLipschitzField_linear M N G) h01 hhL hU₀ S₀ hV₀ hrm hrn
  exact ⟨K₁, L₁, U₁, V₁, S₁,
    (isStep_tubeExt_iff_of_near hP.bounded hP.B_nonneg le_rfl le_rfl h01 hP.sol hsmall).2 hs,
    (stepRel_tubeExt_iff_of_near hP.bounded hP.B_nonneg le_rfl le_rfl h01 hP.sol hsmall).2
      hs.stepRel⟩

variable [DecidableEq m] [DecidableEq n]

/-- **Non-vacuity of `MatrixImplicitBUG.IsStep.isMatrixImplicitBUGStep`,
`IsImplicitBUGStep.hasLocalError_of_tube`, `MatrixImplicitBUG.IsStep.hasLocalError_of_tube` and
`MatrixImplicitBUG.IsStep.hasLocalError_of_tube_le`.** The linear field
`F(t, Y) = M Y + Y Nᵀ + G` with a stationary point `C` is `(‖M‖ + ‖N‖)`-Lipschitz and bounded by
`(‖M‖ + ‖N‖) ρ` on the tube of radius `ρ` around `A(t) = C`, does not depend on time, and its
normal component at the matrices of rank `r` is at most `‖G‖`. If `h (‖M‖ + ‖N‖) ≤ 1/2`, a step
exists from every factorization with orthonormal `U₀`, `V₀`. It is an implicit BUG step of the
core with `ε = ‖G‖`, and if its start value lies near `C`, it has the local error of
`IsImplicitBUGStep.hasLocalError_of_tube` and `h ((14 L B + 8 · 0) h + 6 ‖G‖)` with
`L = ‖M‖ + ‖N‖`, `B = (‖M‖ + ‖N‖) ρ`. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {t₀ t₁ ρ : ℝ} (hρ : 0 ≤ ρ) (h01 : t₀ ≤ t₁) (hhL : (t₁ - t₀) * (‖M‖ + ‖N‖) ≤ 1 / 2)
    {U₀ : Matrix m (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} (hU₀ : U₀ᵀ * U₀ = 1)
    (hV₀ : V₀ᵀ * V₀ = 1) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (hsmall : ‖U₀ * S₀ * V₀ᵀ - C‖ + 4 * ((‖M‖ + ‖N‖) * ρ) * (t₁ - t₀) < ρ) :
    ∃ (K₁ : Matrix m (Fin r) ℝ) (L₁ : Matrix n (Fin r) ℝ) (U₁ : Matrix m (Fin r) ℝ)
      (V₁ : Matrix n (Fin r) ℝ) (S₁ : Matrix (Fin r) (Fin r) ℝ),
      IsMatrixImplicitBUGStep (fun _ Y => M * Y + Y * Nᵀ + G) ‖G‖ 0 0 t₁ (t₁ - t₀) U₀ S₀ V₀
        K₁ L₁ U₁ V₁ S₁ (U₁ * S₁ * V₁ᵀ) ∧
      HasLocalError (fun _ Y => M * Y + Y * Nᵀ + G) t₀ t₁ (U₀ * S₀ * V₀ᵀ) (U₁ * S₁ * V₁ᵀ)
        (implicitLocalBound (‖M‖ + ‖N‖) 0 ((‖M‖ + ‖N‖) * ρ) (‖M‖ + ‖N‖) (t₁ - t₀)
          (2 * implicitCaptureBound (‖M‖ + ‖N‖) 0 ((‖M‖ + ‖N‖) * ρ) (t₁ - t₀) ‖G‖ 0) 0) ∧
      HasLocalError (fun _ Y => M * Y + Y * Nᵀ + G) t₀ t₁ (U₀ * S₀ * V₀ᵀ) (U₁ * S₁ * V₁ᵀ)
        ((t₁ - t₀) * ((14 * (‖M‖ + ‖N‖) * ((‖M‖ + ‖N‖) * ρ) + 8 * 0) * (t₁ - t₀) +
          6 * ‖G‖)) := by
  have hP := dlraProblem_linear M N G C hC t₀ t₁ hρ
  obtain ⟨K₁, L₁, U₁, V₁, S₁, hs⟩ :=
    exists_isStep (isLipschitzField_linear M N G) h01 (by linarith) hU₀ S₀ hV₀ hrm hrn
  have hk : ‖(1 - U₁ * U₁ᵀ) * (M * (K₁ * V₀ᵀ) + K₁ * V₀ᵀ * Nᵀ + G) * (1 - V₀ * V₀ᵀ)‖ ≤ ‖G‖ := by
    have := factoredNormalBoundOn_linear (r := r) M N G univ t₁ U₁ V₀ (U₁ᵀ * K₁) hs.orthU₁
      hs.orthV₀ (mem_univ _)
    rwa [show U₁ * (U₁ᵀ * K₁) * V₀ᵀ = K₁ * V₀ᵀ by rw [← Matrix.mul_assoc, hs.kCap]] at this
  have hl : ‖(1 - U₀ * U₀ᵀ) * (M * (U₀ * L₁ᵀ) + U₀ * L₁ᵀ * Nᵀ + G) * (1 - V₁ * V₁ᵀ)‖ ≤ ‖G‖ := by
    have := factoredNormalBoundOn_linear (r := r) M N G univ t₁ U₀ V₁ (L₁ᵀ * V₁) hs.orthU₀
      hs.orthV₁ (mem_univ _)
    rwa [show U₀ * (L₁ᵀ * V₁) * V₁ᵀ = U₀ * L₁ᵀ by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hs.transpose_mul_lCap]] at this
  have hstep := hs.isMatrixImplicitBUGStep hk hl
  obtain ⟨hK, hYL, hS⟩ := hs.norm_stage_sub_le h01 hP.B_nonneg fun x hx =>
    hP.bounded t₁ ⟨h01, le_rfl⟩ x
      (norm_sub_le_of_near hP.bounded le_rfl le_rfl h01 hP.sol hsmall hP.B_nonneg x hx)
  refine ⟨K₁, L₁, U₁, V₁, S₁, hstep, ?_, ?_⟩
  · exact hstep.toAbstract.hasLocalError_of_tube hP.lipschitz hP.L_nonneg hP.bounded
      hP.B_nonneg le_rfl (fun _ _ _ _ _ _ => by simp) le_rfl le_rfl h01 (by linarith) hP.sol
      hK hYL hS hsmall
  · exact hs.hasLocalError_of_tube_le (factoredNormalBoundOn_linear M N G _) (norm_nonneg G)
      hP.lipschitz hP.L_nonneg hP.bounded hP.B_nonneg le_rfl (fun _ _ _ _ _ _ => by simp)
      le_rfl le_rfl h01 hhL hP.sol hsmall

end Examples

end MatrixImplicitBUG

end LeanDLRA
