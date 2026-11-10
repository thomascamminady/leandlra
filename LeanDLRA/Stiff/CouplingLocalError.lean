import LeanDLRA.Foundations.Existence
import LeanDLRA.Foundations.OneSided
import LeanDLRA.Foundations.Projector
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Matrix.Projectors

/-!
# Stiff problems: a local error bound for the rank-adaptive BUG step with coupling numbers

For a stiff differential equation `Y' = 𝓛 Y + G(t, Y)`, for example a matrix equation with
`𝓛 Y = M Y + Y Nᵀ` and discretised diffusion operators `M`, `N`, the Lipschitz constant of the
right-hand side contains `‖𝓛‖`, which grows without bound under mesh refinement. The local error
bounds of this library for the step of the basis-update and Galerkin (BUG) integrator,
`IsBUGStep.local_error` and `IsRankAdaptiveBUGStep.local_error`, have constants that depend on
the Lipschitz constant of the whole field, so these constants grow with `‖𝓛‖`.

This file proves a local error bound for one rank-adaptive BUG step with exact substeps, a step
in the sense of `IsRankAdaptiveBUGStep`, in which `‖𝓛‖` does not appear. In its place the bound
contains

* the one-sided Lipschitz constant `ℓ` of `F = 𝓛 + G` (for a dissipative `𝓛` this is at most the
  Lipschitz constant `L_G` of the nonstiff part);
* **coupling numbers** of `𝓛` with the subspaces of the step;
* two bounds along the exact solution, `‖A'‖ ≤ B₁` and `‖𝓛 A'‖ ≤ B₂`.

The bound does not contain singular values of the solution either.

## Setting

`E` is a real inner product space and `F(t, x) = 𝓛 x + G(t, x)` with a continuous linear map `𝓛`.
The field `F` is one-sided Lipschitz with constant `ℓ` (`IsOneSidedLipschitzField`) and `G` is
Lipschitz with constant `L_G` (`IsLipschitzField`). As in `IsRankAdaptiveBUGStep`, `P₀`, `Q₀` are
the orthogonal projectors that belong to the old bases and `P₁`, `Q₁` those of the augmented
bases; `A` is the exact solution with `A(t₀) = Y₀`, and `h = t₁ - t₀`.

A number `κ ≥ 0` is a coupling number of `𝓛` with an orthogonal projector `P` if it bounds the
two off-diagonal blocks of `𝓛` with respect to `range P` and its complement:
`‖P 𝓛 (x - P x)‖ ≤ κ ‖x - P x‖` and `‖𝓛 P x - P 𝓛 P x‖ ≤ κ ‖P x‖` for all `x`. Zero is a coupling
number when `𝓛` commutes with `P`, and `‖𝓛‖` is always one. The hypotheses of the theorems are
these two inequalities; there is no definition of a coupling number in the file.

## Main results

* `stiff_galerkin_compare`: a Galerkin trajectory in `range P` stays close to the projected
  exact solution, with rate `ℓ` and defect `(κ + L_G) sup ‖(1 - P) A‖`.
* `stiff_kstep_capture`: the K-step captures the range of the exact solution,
  `‖(1 - P₁) A(t₁)‖ ≤ h (ε + C h)`, where `C = stiffCaptureConst` depends on `ℓ`, `L_G`, `κ`,
  `B₁`, `B₂` only (`stiffCapture_eq`). The same statement with the roles of the two projectors
  exchanged is the capture lemma of the L-step.
* `stiff_galerkin_step_error`: the Galerkin step in a subspace with coupling number `κ̂`.
* `stiff_bug_local_error`: the step before truncation, with every hypothesis listed,
  `‖YS(t₁) - A(t₁)‖ ≤ (κ̂ + L_G) B₁ h² max(1, e^{ℓ h}) + 2 h (ε + C h)`.
* `IsRankAdaptiveBUGStep.stiff_local_error`: the same bound for the step predicate of the
  library, with the truncation: `‖Y₁ - A(t₁)‖` is at most the bound above plus the truncation
  tolerance `ϑ`.

## Remarks on the hypotheses

* The statements are for one step that starts at the exact value, with exact substeps.
* The start value lies in the ranges of the old projectors, `P₀ Y₀ = Y₀` and `Q₀ Y₀ = Y₀` (true
  for `Y₀ = U₀ S₀ V₀ᵀ`). This is a hypothesis of `IsRankAdaptiveBUGStep.stiff_local_error`,
  because the step predicate does not contain it.
* The coupling number `κ` of the old subspaces is a property of the data of the step. The
  coupling number `κ̂` of the augmented subspace `range (P₁ Q₁)` depends on the computed bases;
  it can be evaluated after the step, and no bound for it in terms of the data is proved here.
  The theorem improves on a bound with `‖𝓛‖` only where these numbers are smaller than `‖𝓛‖`.
* `B₂` bounds `𝓛 A'` along the exact solution. This is a smoothness assumption on the exact
  solution, not on the numerical one.
* The first `example` after the theorem is a consistency check of the hypotheses with identity
  projectors, for which the step is the exact flow. The section `StiffCouplingExample` at the
  end of the file instantiates the theorem with nonzero data: a `2 × 3` matrix problem with
  projectors that are not the identity, coupling numbers `12/25 · λ` for a stiff operator of
  norm `λ`, `ε = 4` and a step whose error is exactly `h ε`.

## Relation to the literature

The local error bounds of the BUG integrator [CerutiLubich2022, Lemma 4] and of the
rank-adaptive BUG integrator [CerutiKuschLubich2022, Thm. 2] are stated with the Lipschitz constant
and a bound of the field; in this library they are `IsBUGStep.local_error` and
`IsRankAdaptiveBUGStep.local_error`. The proof in this file has the same three parts (capture by
the K-step, capture by the L-step, Galerkin step), with the one-sided Lipschitz condition and the
coupling numbers in place of the Lipschitz condition. Low-rank integrators for stiff problems
are discussed in [CarrelVandereycken2023, §2.3].
-/

open Set
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Galerkin comparison for a stiff field.** Let `F = 𝓛 + G` be one-sided Lipschitz with
constant `ℓ`, `G` Lipschitz with constant `L_G`, and let `P` be an orthogonal projector with
`‖P 𝓛 (x - P x)‖ ≤ κ ‖x - P x‖`. If `Y' = P F(t, Y)` in the range of `P` and the exact solution
satisfies `‖A - P A‖ ≤ η` on the interval, then
`‖P A(t) - Y(t)‖ ≤ gronwallBound ‖P A(a) - Y(a)‖ ℓ ((κ + L_G) η) (t - a)`.
The norm of `𝓛` does not enter. -/
theorem stiff_galerkin_compare {F G : ℝ → E → E} {𝓛 P : E →L[ℝ] E} {ℓ LG κ η : ℝ}
    {A Y : ℝ → E} {a b : ℝ} (hF : IsOneSidedLipschitzField F ℓ)
    (hsplit : ∀ t x, F t x = 𝓛 x + G t x) (hG : IsLipschitzField G LG) (hP : IsOrthProj P)
    (hκ : ∀ x, ‖P (𝓛 (x - P x))‖ ≤ κ * ‖x - P x‖) (hκ0 : 0 ≤ κ) (hLG : 0 ≤ LG)
    (hA : ODESolution F A a b) (hY : ODESolution (fun t x => P (F t x)) Y a b)
    (hYP : ∀ t ∈ Ico a b, P (Y t) = Y t) (hη : ∀ t ∈ Ico a b, ‖A t - P (A t)‖ ≤ η) :
    ∀ t ∈ Icc a b,
      ‖P (A t) - Y t‖ ≤ gronwallBound ‖P (A a) - Y a‖ ℓ ((κ + LG) * η) (t - a) := by
  have hdef : ∀ t ∈ Ico a b, ‖P (F t (A t)) - P (F t (P (A t)))‖ ≤ (κ + LG) * η := by
    intro t ht
    have e : P (F t (A t)) - P (F t (P (A t)))
        = P (𝓛 (A t - P (A t))) + P (G t (A t) - G t (P (A t))) := by
      rw [hsplit, hsplit]
      simp only [map_sub, map_add]
      abel
    have h1 := hκ (A t)
    have h2 : ‖P (G t (A t) - G t (P (A t)))‖ ≤ LG * ‖A t - P (A t)‖ :=
      (hP.norm_le _).trans (hG t _ _)
    have h3 := hη t ht
    have h4 : (κ + LG) * ‖A t - P (A t)‖ ≤ (κ + LG) * η :=
      mul_le_mul_of_nonneg_left h3 (by linarith)
    rw [e]
    linarith [norm_add_le (P (𝓛 (A t - P (A t)))) (P (G t (A t) - G t (P (A t))))]
  have h := galerkin_norm_sub_le_gronwallBound (F := F) (ℓ := ℓ) (P := P) hF hP
    (y := fun t => P (A t)) (z := Y) (u := fun t => P (F t (A t)))
    (w := fun t => P (F t (Y t))) (a := a) (b := b) (ηy := (κ + LG) * η) (ηz := 0)
    (δ := ‖P (A a) - Y a‖) (fun t _ => hP.idem (A t)) hYP
    (P.continuous.comp_continuousOn hA.cont)
    (fun t ht => P.hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht)) hdef hY.cont hY.deriv
    (fun t _ => by simp) le_rfl
  simpa using h

/-- Bound for the part of `A(t₁) - YK(t₁)` inside the range of the frozen projector:
`(κ + L_G) B₁ h² max(1, e^{ℓ h})`. -/
noncomputable def stiffDrift (ℓ LG κ B₁ h : ℝ) : ℝ :=
  (κ + LG) * (h * B₁) * h * max 1 (Real.exp (ℓ * h))

/-- The capture bound of the stiff K-step lemma `stiff_kstep_capture`. -/
noncomputable def stiffCapture (ℓ LG κ B₁ B₂ ε h : ℝ) : ℝ :=
  stiffDrift ℓ LG κ B₁ h
    + h * (ε + 2 * h * B₂ + (κ + LG) * stiffDrift ℓ LG κ B₁ h + (κ + 2 * LG) * h * B₁)

/-- The constant of the `h²` term of the capture bound. It contains the one-sided Lipschitz
constant `ℓ`, the Lipschitz constant `L_G` of the nonstiff part, the coupling number `κ` and the
bounds `B₁`, `B₂` along the exact solution, and no norm of the stiff operator. -/
noncomputable def stiffCaptureConst (ℓ LG κ B₁ B₂ h : ℝ) : ℝ :=
  (κ + LG) * B₁ * max 1 (Real.exp (ℓ * h)) * (1 + h * (κ + LG)) + 2 * B₂ + (κ + 2 * LG) * B₁

/-- The capture bound has the form `h (ε + C h)`. -/
lemma stiffCapture_eq (ℓ LG κ B₁ B₂ ε h : ℝ) :
    stiffCapture ℓ LG κ B₁ B₂ ε h = h * (ε + stiffCaptureConst ℓ LG κ B₁ B₂ h * h) := by
  unfold stiffCapture stiffCaptureConst stiffDrift
  ring

/-- **K-step capture for a stiff field.** Let `F = 𝓛 + G` be one-sided Lipschitz with constant
`ℓ` and `G` Lipschitz with constant `L_G`. Let `Q₀` be the frozen projector of the K-step, with
coupling number `κ` (`hκ`, `hκ'`), let `YK' = Q₀ F(t, YK)` start at the exact value
`A(t₀) ∈ range Q₀`, and let the new projector `P₁` contain the result, `P₁ YK(t₁) = YK(t₁)`.
If `‖F(t, A(t))‖ ≤ B₁`, `‖𝓛 F(t, A(t))‖ ≤ B₂` along the exact solution and the doubly normal
component of `F` at `YK(t₁)` is at most `ε`, then

`‖(1 - P₁) A(t₁)‖ ≤ stiffCapture ℓ L_G κ B₁ B₂ ε h = h (ε + C h)`.

For `𝓛 Y = M Y` acting from the left and `Q₀ Y = Y V₀ V₀ᵀ` the coupling number is zero; for
`𝓛 Y = M Y + Y Nᵀ` it is `max (‖(1 - V₀ V₀ᵀ) N V₀‖₂, ‖(1 - V₀ V₀ᵀ) Nᵀ V₀‖₂)`. The classical
bound `h (4 L B h + ε)` needs the Lipschitz constant `L ≥ ‖𝓛‖` of `F`. -/
theorem stiff_kstep_capture {F G : ℝ → E → E} {𝓛 P₁ Q₀ : E →L[ℝ] E} {ℓ LG κ B₁ B₂ ε : ℝ}
    {A YK : ℝ → E} {t₀ t₁ h : ℝ} (hF : IsOneSidedLipschitzField F ℓ)
    (hsplit : ∀ t x, F t x = 𝓛 x + G t x) (hG : IsLipschitzField G LG) (hLG : 0 ≤ LG)
    (hκ0 : 0 ≤ κ) (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    (hκ : ∀ x, ‖Q₀ (𝓛 (x - Q₀ x))‖ ≤ κ * ‖x - Q₀ x‖)
    (hκ' : ∀ x, ‖𝓛 (Q₀ x) - Q₀ (𝓛 (Q₀ x))‖ ≤ κ * ‖Q₀ x‖)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hB₁ : ∀ t ∈ Icc t₀ t₁, ‖F t (A t)‖ ≤ B₁) (hB₂ : ∀ t ∈ Icc t₀ t₁, ‖𝓛 (F t (A t))‖ ≤ B₂)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = A t₀)
    (hQA : Q₀ (A t₀) = A t₀) (hKcap : P₁ (YK t₁) = YK t₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε) :
    ‖(1 - P₁) (A t₁)‖ ≤ stiffCapture ℓ LG κ B₁ B₂ ε h := by
  have hle : t₀ ≤ t₁ := by linarith
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ t₀ ⟨le_rfl, hle⟩)
  have key : ∀ (P : E →L[ℝ] E) (x : E), (1 - P) x = x - P x := fun P x => by simp
  have hAs : ∀ {s t : ℝ}, t₀ ≤ s → s ≤ t → t ≤ t₁ → ‖A t - A s‖ ≤ B₁ * (t - s) :=
    fun {s t} hs hst ht => (hA.mono hs ht).norm_sub_le
      (fun x hx => hB₁ x ⟨hs.trans hx.1, (hx.2.trans_le ht).le⟩) t ⟨hst, le_rfl⟩
  have hLs : ∀ {s t : ℝ}, t₀ ≤ s → s ≤ t → t ≤ t₁ → ‖𝓛 (A t) - 𝓛 (A s)‖ ≤ B₂ * (t - s) :=
    fun {s t} hs hst ht => norm_image_sub_le_of_norm_deriv_right_le_segment
      (f := fun t => 𝓛 (A t)) (f' := fun t => 𝓛 (F t (A t))) (a := s) (b := t)
      ((𝓛.continuous.comp_continuousOn hA.cont).mono (Icc_subset_Icc hs ht))
      (fun x hx => 𝓛.hasFDerivAt.comp_hasDerivWithinAt x
        (hA.deriv x ⟨hs.trans hx.1, hx.2.trans_le ht⟩))
      (fun x hx => hB₂ x ⟨hs.trans hx.1, (hx.2.trans_le ht).le⟩) t ⟨hst, le_rfl⟩
  have hKQ : ∀ t ∈ Icc t₀ t₁, Q₀ (YK t) = YK t := hK.galerkin_mem_range hQ₀ (by rw [hK₀, hQA])
  -- the exact solution leaves the range of `Q₀` slowly
  have hn : ∀ t ∈ Icc t₀ t₁, ‖A t - Q₀ (A t)‖ ≤ h * B₁ := by
    intro t ht
    have e : A t - Q₀ (A t) = (A t - A t₀) - Q₀ (A t - A t₀) := by
      rw [map_sub, hQA]; abel
    have h1 := hQ₀.norm_sub_le (A t - A t₀)
    have h2 := hAs le_rfl ht.1 ht.2
    have h3 : B₁ * (t - t₀) ≤ B₁ * h := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB₁0
    rw [e]
    linarith
  -- the part of the difference inside the range of `Q₀`
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = stiffDrift ℓ LG κ B₁ h := ⟨_, rfl⟩
  obtain ⟨m₁, hm₁⟩ : ∃ m, m = Q₀ (A t₁) - YK t₁ := ⟨_, rfl⟩
  obtain ⟨Δ, hΔ⟩ : ∃ d, d = A t₁ - A t₀ := ⟨_, rfl⟩
  have hm : ‖m₁‖ ≤ μ := by
    have h1 := stiff_galerkin_compare hF hsplit hG hQ₀ hκ hκ0 hLG hA hK
      (fun t ht => hKQ t (Ico_subset_Icc_self ht)) (fun t ht => hn t (Ico_subset_Icc_self ht))
      t₁ ⟨hle, le_rfl⟩
    rw [hQA, hK₀, sub_self, norm_zero] at h1
    have hη0 : 0 ≤ (κ + LG) * (h * B₁) := mul_nonneg (by linarith) (mul_nonneg hh hB₁0)
    have h2 := gronwallBound_le_exp_mul_add_max (δ := 0) (K := ℓ) hη0 (sub_nonneg.2 hle)
    have h3 : t₁ - t₀ = h := by linarith
    rw [h3] at h1 h2
    rw [hm₁, hμ, stiffDrift]
    linarith
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans hm
  have hQm : Q₀ m₁ = m₁ := by rw [hm₁, map_sub, hQ₀.idem, hKQ t₁ ⟨hle, le_rfl⟩]
  have hΔn : ‖Δ‖ ≤ h * B₁ := by
    have h1 := hAs le_rfl hle le_rfl
    have h3 : t₁ - t₀ = h := by linarith
    rw [h3, mul_comm] at h1
    rw [hΔ]; exact h1
  have hD : A t₁ - YK t₁ = Q₀ m₁ + (Δ - Q₀ Δ) := by
    rw [hQm, hm₁, hΔ, map_sub, hQA]; abel
  -- the derivative of `(1 - P₁) (1 - Q₀) A`
  obtain ⟨C, hC⟩ : ∃ C, C = ε + 2 * h * B₂ + (κ + LG) * μ + (κ + 2 * LG) * h * B₁ := ⟨_, rfl⟩
  have hgc : ContinuousOn (fun t => (1 - P₁) ((1 - Q₀) (A t))) (Icc t₀ t₁) :=
    (1 - P₁).continuous.comp_continuousOn ((1 - Q₀).continuous.comp_continuousOn hA.cont)
  have hgd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => (1 - P₁) ((1 - Q₀) (A t)))
      ((1 - P₁) ((1 - Q₀) (F t (A t)))) (Ici t) t := fun t ht =>
    (1 - P₁).hasFDerivAt.comp_hasDerivWithinAt t
      ((1 - Q₀).hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht))
  have hgb : ∀ t ∈ Ico t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (A t)))‖ ≤ C := by
    intro t ht
    have htI : t ∈ Icc t₀ t₁ := Ico_subset_Icc_self ht
    have e1 : 𝓛 (A t₁) = 𝓛 (YK t₁) + (𝓛 (Q₀ m₁) + (𝓛 Δ - 𝓛 (Q₀ Δ))) := by
      have h𝓛 : 𝓛 (A t₁) - 𝓛 (YK t₁) = 𝓛 (Q₀ m₁) + (𝓛 Δ - 𝓛 (Q₀ Δ)) := by
        rw [← map_sub 𝓛 (A t₁) (YK t₁), hD, map_add, map_sub]
      rw [← h𝓛]; abel
    have hFd : F t (A t) = F t (YK t₁) + ((𝓛 (A t) - 𝓛 (A t₁)) + 𝓛 (Q₀ m₁)
        + (𝓛 Δ - 𝓛 (Q₀ Δ)) + (G t (A t) - G t (YK t₁))) := by
      rw [hsplit, hsplit, e1]; abel
    have hsplit2 : (1 - P₁) ((1 - Q₀) (F t (A t))) = (1 - P₁) ((1 - Q₀) (F t (YK t₁)))
        + (1 - P₁) ((1 - Q₀) (𝓛 (A t) - 𝓛 (A t₁)) + (1 - Q₀) (𝓛 (Q₀ m₁))
          + ((1 - Q₀) (𝓛 Δ) - (1 - Q₀) (𝓛 (Q₀ Δ))) + (1 - Q₀) (G t (A t) - G t (YK t₁))) := by
      rw [hFd]; simp only [map_add, map_sub]
    have n0 := hε t htI
    have n1 : ‖(1 - Q₀) (𝓛 (A t) - 𝓛 (A t₁))‖ ≤ h * B₂ := by
      have h1 := hLs htI.1 htI.2 le_rfl
      have h2 : B₂ * (t₁ - t) ≤ B₂ * h :=
        mul_le_mul_of_nonneg_left (by linarith [htI.1])
          ((norm_nonneg _).trans (hB₂ t₀ ⟨le_rfl, hle⟩))
      rw [norm_sub_rev] at h1
      linarith [hQ₀.compl.norm_le (𝓛 (A t) - 𝓛 (A t₁))]
    have n2 : ‖(1 - Q₀) (𝓛 (Q₀ m₁))‖ ≤ κ * μ := by
      rw [key]
      have h1 := hκ' m₁
      rw [hQm] at h1 ⊢
      exact h1.trans (mul_le_mul_of_nonneg_left hm hκ0)
    have n3 : ‖(1 - Q₀) (𝓛 Δ)‖ ≤ h * B₂ := by
      have h1 := hLs le_rfl hle le_rfl
      have h3 : t₁ - t₀ = h := by linarith
      rw [h3, ← map_sub, ← hΔ, mul_comm] at h1
      exact (hQ₀.compl.norm_le _).trans h1
    have n4 : ‖(1 - Q₀) (𝓛 (Q₀ Δ))‖ ≤ κ * (h * B₁) := by
      rw [key]
      exact (hκ' Δ).trans (mul_le_mul_of_nonneg_left ((hQ₀.norm_le Δ).trans hΔn) hκ0)
    have n5 : ‖(1 - Q₀) (G t (A t) - G t (YK t₁))‖ ≤ LG * (2 * (h * B₁) + μ) := by
      have h1 : ‖A t - YK t₁‖ ≤ 2 * (h * B₁) + μ := by
        have e : A t - YK t₁ = -(A t₁ - A t) + (Q₀ m₁ + (Δ - Q₀ Δ)) := by rw [← hD]; abel
        have h2 := hAs htI.1 htI.2 le_rfl
        have h3 : B₁ * (t₁ - t) ≤ B₁ * h :=
          mul_le_mul_of_nonneg_left (by linarith [htI.1]) hB₁0
        have h4 := (hQ₀.norm_sub_le Δ).trans hΔn
        rw [e, hQm]
        have h5 := norm_add_le (-(A t₁ - A t)) (m₁ + (Δ - Q₀ Δ))
        have h6 := norm_add_le m₁ (Δ - Q₀ Δ)
        rw [norm_neg] at h5
        linarith
      exact (hQ₀.compl.norm_le _).trans ((hG t _ _).trans (mul_le_mul_of_nonneg_left h1 hLG))
    rw [hsplit2]
    have t1 := norm_add_le ((1 - P₁) ((1 - Q₀) (F t (YK t₁))))
      ((1 - P₁) ((1 - Q₀) (𝓛 (A t) - 𝓛 (A t₁)) + (1 - Q₀) (𝓛 (Q₀ m₁))
          + ((1 - Q₀) (𝓛 Δ) - (1 - Q₀) (𝓛 (Q₀ Δ))) + (1 - Q₀) (G t (A t) - G t (YK t₁))))
    have t2 := hP₁.compl.norm_le ((1 - Q₀) (𝓛 (A t) - 𝓛 (A t₁)) + (1 - Q₀) (𝓛 (Q₀ m₁))
          + ((1 - Q₀) (𝓛 Δ) - (1 - Q₀) (𝓛 (Q₀ Δ))) + (1 - Q₀) (G t (A t) - G t (YK t₁)))
    have t3 := norm_add_le ((1 - Q₀) (𝓛 (A t) - 𝓛 (A t₁)) + (1 - Q₀) (𝓛 (Q₀ m₁))
          + ((1 - Q₀) (𝓛 Δ) - (1 - Q₀) (𝓛 (Q₀ Δ)))) ((1 - Q₀) (G t (A t) - G t (YK t₁)))
    have t4 := norm_add_le ((1 - Q₀) (𝓛 (A t) - 𝓛 (A t₁)) + (1 - Q₀) (𝓛 (Q₀ m₁)))
          ((1 - Q₀) (𝓛 Δ) - (1 - Q₀) (𝓛 (Q₀ Δ)))
    have t5 := norm_add_le ((1 - Q₀) (𝓛 (A t) - 𝓛 (A t₁))) ((1 - Q₀) (𝓛 (Q₀ m₁)))
    have t6 := norm_sub_le ((1 - Q₀) (𝓛 Δ)) ((1 - Q₀) (𝓛 (Q₀ Δ)))
    rw [hC]
    linarith
  have hg := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd hgb t₁ ⟨hle, le_rfl⟩
  have hg0 : (1 - Q₀) (A t₀) = 0 := by rw [key, hQA, sub_self]
  have h3 : t₁ - t₀ = h := by linarith
  simp only [hg0, map_zero, sub_zero, h3] at hg
  have e : (1 - P₁) (A t₁) = (1 - P₁) m₁ + (1 - P₁) ((1 - Q₀) (A t₁)) := by
    have e0 : A t₁ = m₁ + YK t₁ + (1 - Q₀) (A t₁) := by rw [hm₁, key]; abel
    have e1 : (1 - P₁) (YK t₁) = 0 := by rw [key, hKcap, sub_self]
    conv_lhs => rw [e0]
    rw [map_add, map_add, e1, add_zero]
  rw [e, stiffCapture, ← hμ]
  have h4 := norm_add_le ((1 - P₁) m₁) ((1 - P₁) ((1 - Q₀) (A t₁)))
  have h5 := hP₁.compl.norm_le m₁
  rw [hC] at hg
  linarith

/-- **Galerkin step for a stiff field.** Let `F = 𝓛 + G` be one-sided Lipschitz with constant
`ℓ`, `G` Lipschitz with constant `L_G`, and let `R` be an orthogonal projector with
`‖R 𝓛 (x - R x)‖ ≤ κ ‖x - R x‖`. If the Galerkin solution `YS' = R F(t, YS)` starts at
`R A(t₀)`, the exact solution stays within `η` of the range of `R` on the step and within `θ`
at its end, then

`‖YS(t₁) - A(t₁)‖ ≤ (κ + L_G) η h max(1, e^{ℓ h}) + θ`.

The classical bound `(e^{L h} - 1)(B h + θ) + θ` needs the Lipschitz constant `L ≥ ‖𝓛‖`. -/
theorem stiff_galerkin_step_error {F G : ℝ → E → E} {𝓛 R : E →L[ℝ] E} {ℓ LG κ η θ : ℝ}
    {A YS : ℝ → E} {t₀ t₁ h : ℝ} (hF : IsOneSidedLipschitzField F ℓ)
    (hsplit : ∀ t x, F t x = 𝓛 x + G t x) (hG : IsLipschitzField G LG) (hLG : 0 ≤ LG)
    (hκ0 : 0 ≤ κ) (hR : IsOrthProj R) (hκ : ∀ x, ‖R (𝓛 (x - R x))‖ ≤ κ * ‖x - R x‖)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hS : ODESolution (fun t x => R (F t x)) YS t₀ t₁) (hS₀ : YS t₀ = R (A t₀))
    (hη : ∀ t ∈ Icc t₀ t₁, ‖A t - R (A t)‖ ≤ η) (hθ : ‖A t₁ - R (A t₁)‖ ≤ θ) :
    ‖YS t₁ - A t₁‖ ≤ (κ + LG) * η * h * max 1 (Real.exp (ℓ * h)) + θ := by
  have hle : t₀ ≤ t₁ := by linarith
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hη t₀ ⟨le_rfl, hle⟩)
  have hSR : ∀ t ∈ Icc t₀ t₁, R (YS t) = YS t := hS.galerkin_mem_range hR (by rw [hS₀, hR.idem])
  have h1 := stiff_galerkin_compare hF hsplit hG hR hκ hκ0 hLG hA hS
    (fun t ht => hSR t (Ico_subset_Icc_self ht)) (fun t ht => hη t (Ico_subset_Icc_self ht))
    t₁ ⟨hle, le_rfl⟩
  rw [hS₀, sub_self, norm_zero] at h1
  have hc0 : 0 ≤ (κ + LG) * η := mul_nonneg (by linarith) hη0
  have h2 := gronwallBound_le_exp_mul_add_max (δ := 0) (K := ℓ) hc0 (sub_nonneg.2 hle)
  have h3 : t₁ - t₀ = h := by linarith
  rw [h3] at h1 h2
  have e : YS t₁ - A t₁ = -(R (A t₁) - YS t₁) - (A t₁ - R (A t₁)) := by abel
  rw [e]
  have h4 := norm_sub_le (-(R (A t₁) - YS t₁)) (A t₁ - R (A t₁))
  rw [norm_neg] at h4
  linarith

/-- **Local error of one augmented BUG step for a stiff field.** Let `F = 𝓛 + G` be one-sided
Lipschitz with constant `ℓ` and `G` Lipschitz with constant `L_G`. The step starts from the
exact value `A(t₀)`, which lies in the ranges of the old projectors `P₀`, `Q₀` and of the new
commuting projectors `P₁`, `Q₁` (augmented bases contain the old ones). The K-step and the
L-step are solved exactly and captured by `P₁` and `Q₁`; the S-step is the Galerkin equation
for `P₁ Q₁`. Let `κ` be a coupling number of `𝓛` with `P₀` and with `Q₀`, and `κ̂` one of `𝓛`
with `P₁ Q₁`. If `‖F(t, A(t))‖ ≤ B₁` and `‖𝓛 F(t, A(t))‖ ≤ B₂` along the exact solution, then

`‖YS(t₁) - A(t₁)‖ ≤ (κ̂ + L_G) B₁ h² max(1, e^{ℓ h}) + 2 h (ε + C h)`,

with `C = stiffCaptureConst ℓ L_G κ B₁ B₂ h`. Neither the norm of `𝓛` nor a singular value
of the solution enters. For `𝓛 = 0` the constants reduce to multiples of `L_G B₁`, as in the
classical bound `(e^{L h} - 1)(B h + 2 h (4 L B h + ε)) + 2 h (4 L B h + ε)`. -/
theorem stiff_bug_local_error {F G : ℝ → E → E} {𝓛 P₀ Q₀ P₁ Q₁ : E →L[ℝ] E}
    {ℓ LG κ κh B₁ B₂ ε : ℝ} {A YK YL YS : ℝ → E} {t₀ t₁ h : ℝ}
    (hF : IsOneSidedLipschitzField F ℓ) (hsplit : ∀ t x, F t x = 𝓛 x + G t x)
    (hG : IsLipschitzField G LG) (hLG : 0 ≤ LG) (hκ0 : 0 ≤ κ) (hκh0 : 0 ≤ κh)
    (hP₀ : IsOrthProj P₀) (hQ₀ : IsOrthProj Q₀) (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁)
    (hc : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x))
    (hκQ : ∀ x, ‖Q₀ (𝓛 (x - Q₀ x))‖ ≤ κ * ‖x - Q₀ x‖)
    (hκQ' : ∀ x, ‖𝓛 (Q₀ x) - Q₀ (𝓛 (Q₀ x))‖ ≤ κ * ‖Q₀ x‖)
    (hκP : ∀ x, ‖P₀ (𝓛 (x - P₀ x))‖ ≤ κ * ‖x - P₀ x‖)
    (hκP' : ∀ x, ‖𝓛 (P₀ x) - P₀ (𝓛 (P₀ x))‖ ≤ κ * ‖P₀ x‖)
    (hκh : ∀ x, ‖(P₁ * Q₁) (𝓛 (x - (P₁ * Q₁) x))‖ ≤ κh * ‖x - (P₁ * Q₁) x‖)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hB₁ : ∀ t ∈ Icc t₀ t₁, ‖F t (A t)‖ ≤ B₁) (hB₂ : ∀ t ∈ Icc t₀ t₁, ‖𝓛 (F t (A t))‖ ≤ B₂)
    (hP₀A : P₀ (A t₀) = A t₀) (hQ₀A : Q₀ (A t₀) = A t₀)
    (hP₁A : P₁ (A t₀) = A t₀) (hQ₁A : Q₁ (A t₀) = A t₀)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = A t₀)
    (hKcap : P₁ (YK t₁) = YK t₁)
    (hL : ODESolution (fun t x => P₀ (F t x)) YL t₀ t₁) (hL₀ : YL t₀ = A t₀)
    (hLcap : Q₁ (YL t₁) = YL t₁)
    (hεK : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε)
    (hεL : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε)
    (hS : ODESolution (fun t x => (P₁ * Q₁) (F t x)) YS t₀ t₁) (hS₀ : YS t₀ = A t₀) :
    ‖YS t₁ - A t₁‖ ≤ (κh + LG) * (h * B₁) * h * max 1 (Real.exp (ℓ * h))
      + 2 * stiffCapture ℓ LG κ B₁ B₂ ε h := by
  have hle : t₀ ≤ t₁ := by linarith
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ t₀ ⟨le_rfl, hle⟩)
  have key : ∀ (P : E →L[ℝ] E) (x : E), (1 - P) x = x - P x := fun P x => by simp
  have hR : IsOrthProj (P₁ * Q₁) := hP₁.mul hQ₁ hc
  have hRA : (P₁ * Q₁) (A t₀) = A t₀ := by
    change P₁ (Q₁ (A t₀)) = A t₀
    rw [hQ₁A, hP₁A]
  have hη : ∀ t ∈ Icc t₀ t₁, ‖A t - (P₁ * Q₁) (A t)‖ ≤ h * B₁ := by
    intro t ht
    have e : A t - (P₁ * Q₁) (A t) = (A t - A t₀) - (P₁ * Q₁) (A t - A t₀) := by
      rw [map_sub, hRA]; abel
    have h1 := hR.norm_sub_le (A t - A t₀)
    have h2 := hA.norm_sub_le (fun x hx => hB₁ x (Ico_subset_Icc_self hx)) t ht
    have h3 : B₁ * (t - t₀) ≤ B₁ * h := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB₁0
    rw [e]
    linarith
  have hcK := stiff_kstep_capture hF hsplit hG hLG hκ0 hP₁ hQ₀ hκQ hκQ' ht₁ hh hA hB₁ hB₂
    hK hK₀ hQ₀A hKcap hεK
  have hcL := stiff_kstep_capture hF hsplit hG hLG hκ0 hQ₁ hP₀ hκP hκP' ht₁ hh hA hB₁ hB₂
    hL hL₀ hP₀A hLcap hεL
  rw [key] at hcK hcL
  have hθ : ‖A t₁ - (P₁ * Q₁) (A t₁)‖ ≤ 2 * stiffCapture ℓ LG κ B₁ B₂ ε h := by
    have e : A t₁ - (P₁ * Q₁) (A t₁) = (A t₁ - P₁ (A t₁)) + P₁ (A t₁ - Q₁ (A t₁)) := by
      change A t₁ - P₁ (Q₁ (A t₁)) = _
      rw [map_sub]; abel
    rw [e]
    have h1 := norm_add_le (A t₁ - P₁ (A t₁)) (P₁ (A t₁ - Q₁ (A t₁)))
    have h2 := hP₁.norm_le (A t₁ - Q₁ (A t₁))
    linarith
  exact stiff_galerkin_step_error (R := P₁ * Q₁) hF hsplit hG hLG hκh0 hR hκh ht₁ hh hA
    hS (by rw [hS₀, hRA]) hη hθ

/-- **Local error of the rank-adaptive BUG step for a stiff field**: `stiff_bug_local_error` for
the step predicate `IsRankAdaptiveBUGStep` of the library, with the truncation. Let
`F = 𝓛 + G` be one-sided Lipschitz with constant `ℓ` and `G` Lipschitz with constant `L_G`, let
`κ` be a coupling number of `𝓛` with the old projectors `P₀` and `Q₀` and `κ̂` one of `𝓛` with
the Galerkin projector `P₁ Q₁`, and let `‖F(t, A(t))‖ ≤ B₁` and `‖𝓛 F(t, A(t))‖ ≤ B₂` along the
exact solution `A`, which starts at `Y₀`, a point in the ranges of `P₀` and `Q₀`. Then the
result `Y₁` of the step satisfies

`‖Y₁ - A(t₁)‖ ≤ (κ̂ + L_G) B₁ h² max(1, e^{ℓ h}) + 2 h (ε + C h) + ϑ`,

with `C = stiffCaptureConst ℓ L_G κ B₁ B₂ h`, the normal-component bound `ε` and the truncation
tolerance `ϑ` of the step. -/
theorem IsRankAdaptiveBUGStep.stiff_local_error {F G : ℝ → E → E} {𝓛 P₀ Q₀ P₁ Q₁ : E →L[ℝ] E}
    {ℓ LG κ κh B₁ B₂ ε ϑ : ℝ} {A YK YL YS : ℝ → E} {Y₀ Y₁ : E} {t₀ t₁ h : ℝ}
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hF : IsOneSidedLipschitzField F ℓ) (hsplit : ∀ t x, F t x = 𝓛 x + G t x)
    (hG : IsLipschitzField G LG) (hLG : 0 ≤ LG) (hκ0 : 0 ≤ κ) (hκh0 : 0 ≤ κh)
    (hκQ : ∀ x, ‖Q₀ (𝓛 (x - Q₀ x))‖ ≤ κ * ‖x - Q₀ x‖)
    (hκQ' : ∀ x, ‖𝓛 (Q₀ x) - Q₀ (𝓛 (Q₀ x))‖ ≤ κ * ‖Q₀ x‖)
    (hκP : ∀ x, ‖P₀ (𝓛 (x - P₀ x))‖ ≤ κ * ‖x - P₀ x‖)
    (hκP' : ∀ x, ‖𝓛 (P₀ x) - P₀ (𝓛 (P₀ x))‖ ≤ κ * ‖P₀ x‖)
    (hκh : ∀ x, ‖(P₁ * Q₁) (𝓛 (x - (P₁ * Q₁) x))‖ ≤ κh * ‖x - (P₁ * Q₁) x‖)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hB₁ : ∀ t ∈ Icc t₀ t₁, ‖F t (A t)‖ ≤ B₁) (hB₂ : ∀ t ∈ Icc t₀ t₁, ‖𝓛 (F t (A t))‖ ≤ B₂)
    (hP₀Y : P₀ Y₀ = Y₀) (hQ₀Y : Q₀ Y₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ (κh + LG) * (h * B₁) * h * max 1 (Real.exp (ℓ * h))
      + 2 * stiffCapture ℓ LG κ B₁ B₂ ε h + ϑ := by
  subst hA₀
  have h1 := stiff_bug_local_error hF hsplit hG hLG hκ0 hκh0 hs.projP₀ hs.projQ₀ hs.projP₁
    hs.projQ₁ hs.comm₁ hκQ hκQ' hκP hκP' hκh ht₁ hh hA hB₁ hB₂ hP₀Y hQ₀Y hs.augP hs.augQ
    hs.kSol hs.kStart hs.kCap hs.lSol hs.lStart hs.lCap hs.kNormal hs.lNormal hs.sSol'
    hs.start_eq
  have h2 := norm_sub_le_norm_sub_add_norm_sub Y₁ (YS t₁) (A t₁)
  have h3 := hs.trunc
  linarith

/-- The hypotheses of `IsRankAdaptiveBUGStep.stiff_local_error` can be met with a nonzero stiff
operator: for any dissipative `𝓛` and any point `a`, the field `F(t, x) = 𝓛 x - 𝓛 a` has the
stationary solution `a`; with all four projectors the identity, the constant trajectories form a
step in the sense of `IsRankAdaptiveBUGStep`, and every hypothesis holds with all constants zero
except the step size. (A consistency check only: with identity projectors the integrator is the
exact flow.) -/
example (𝓛 : E →L[ℝ] E) (h𝓛 : ∀ x, ⟪𝓛 x, x⟫ ≤ 0) (a : E) :
    ‖a - a‖ ≤ (0 + 0) * (1 * 0) * 1 * max 1 (Real.exp (0 * 1))
      + 2 * stiffCapture 0 0 0 0 0 0 1 + 0 := by
  have hF : IsOneSidedLipschitzField (fun (_ : ℝ) x => 𝓛 x + -𝓛 a) 0 := by
    intro t x y
    have e : 𝓛 x + -𝓛 a - (𝓛 y + -𝓛 a) = 𝓛 (x - y) := by rw [map_sub]; abel
    change ⟪𝓛 x + -𝓛 a - (𝓛 y + -𝓛 a), x - y⟫ ≤ 0 * ‖x - y‖ ^ 2
    rw [e, zero_mul]
    exact h𝓛 _
  have hsol : ∀ P : E →L[ℝ] E, P = 1 →
      ODESolution (fun (_ : ℝ) x => P (𝓛 x + -𝓛 a)) (fun _ => a) 0 1 := by
    rintro P rfl
    exact ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) a⟩
  have hsol0 : ODESolution (fun (_ : ℝ) x => 𝓛 x + -𝓛 a) (fun _ => a) 0 1 :=
    ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) a⟩
  have hsol2 : ODESolution
      (fun (_ : ℝ) x => (1 : E →L[ℝ] E) ((1 : E →L[ℝ] E) (𝓛 x + -𝓛 a))) (fun _ => a) 0 1 :=
    ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) a⟩
  have hstep : IsRankAdaptiveBUGStep (fun (_ : ℝ) x => 𝓛 x + -𝓛 a) 0 0 1 1 1 1 0 1 a
      (fun _ => a) (fun _ => a) (fun _ => a) a :=
    { projP₀ := IsOrthProj.one
      projQ₀ := IsOrthProj.one
      projP₁ := IsOrthProj.one
      projQ₁ := IsOrthProj.one
      comm₁ := fun _ => rfl
      kSol := hsol 1 rfl
      kStart := rfl
      kCap := rfl
      kNormal := fun _ _ => by simp
      lSol := hsol 1 rfl
      lStart := rfl
      lCap := rfl
      lNormal := fun _ _ => by simp
      sSol := hsol2
      sStart := rfl
      augP := rfl
      augQ := rfl
      trunc := by simp }
  exact hstep.stiff_local_error (G := fun _ _ => -𝓛 a) (𝓛 := 𝓛) (A := fun _ => a) hF
    (fun _ _ => rfl) (fun _ _ _ => by simp) le_rfl le_rfl le_rfl (fun _ => by simp)
    (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) (by norm_num)
    zero_le_one hsol0 rfl (fun _ _ => by simp) (fun _ _ => by simp) rfl rfl

/-! ### A step with nonzero coupling, projectors that are not the identity and `ε > 0`

A `2 × 3` matrix problem with the Frobenius inner product. The stiff operator is the right
multiplication `Y ↦ Y (λ N₁)` with `N₁ = -e₂ e₂ᵀ`, the rest of the field is constant, and the
start value `Y₀ = U₀ V₀ᵀ` has rank one, with `U₀ = e₁` and `V₀ = (3/5, 4/5, 0)ᵀ`. The row space of
`Y₀` is not invariant under `N₁`, so the stiff operator does not commute with the projector of the
K-step. -/

namespace StiffCouplingExample

open scoped Matrix LeanDLRA.Frobenius

/-- The old left basis `e₁`. -/
def U₀ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The old right basis `(3/5, 4/5, 0)ᵀ`. -/
noncomputable def V₀ : Matrix (Fin 3) (Fin 1) ℝ := !![3 / 5; 4 / 5; 0]

/-- The augmented right basis `[V₀, e₃]`. -/
noncomputable def Va : Matrix (Fin 3) (Fin 2) ℝ := !![3 / 5, 0; 4 / 5, 0; 0, 1]

/-- The stiff direction `N₁ = -e₂ e₂ᵀ`; the stiff operator is `Y ↦ Y (λ N₁)`. -/
def N₁ : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, -1, 0; 0, 0, 0]

/-- The start value `U₀ V₀ᵀ`. -/
noncomputable def Y₀ : Matrix (Fin 2) (Fin 3) ℝ := !![3 / 5, 4 / 5, 0; 0, 0, 0]

/-- The value of the field along the exact solution. -/
def D : Matrix (Fin 2) (Fin 3) ℝ := !![0, 0, 3; 0, 0, 4]

/-- The part of `D` in the old column space, `U₀ U₀ᵀ D`. -/
def W : Matrix (Fin 2) (Fin 3) ℝ := !![0, 0, 3; 0, 0, 0]

/-- The off-diagonal block `(1 - V₀ V₀ᵀ) N₁ V₀ V₀ᵀ` of `N₁`. -/
noncomputable def M₁ : Matrix (Fin 3) (Fin 3) ℝ :=
  !![144 / 625, 192 / 625, 0; -(108 / 625), -(144 / 625), 0; 0, 0, 0]

/-- The off-diagonal block `V₀ V₀ᵀ N₁ (1 - V₀ V₀ᵀ)` of `N₁`. -/
noncomputable def M₂ : Matrix (Fin 3) (Fin 3) ℝ :=
  !![144 / 625, -(108 / 625), 0; 192 / 625, -(144 / 625), 0; 0, 0, 0]

local macro "entries" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Fin.sum_univ_three, U₀, V₀, Va, N₁, Y₀, D, W, M₁, M₂] <;> try norm_num))

lemma orthU₀ : U₀ᵀ * U₀ = 1 := by entries

lemma orthV₀ : V₀ᵀ * V₀ = 1 := by entries

lemma orthVa : Vaᵀ * Va = 1 := by entries

lemma blockV : (1 - V₀ * V₀ᵀ) * N₁ * (V₀ * V₀ᵀ) = M₁ := by entries

lemma blockV' : V₀ * V₀ᵀ * N₁ * (1 - V₀ * V₀ᵀ) = M₂ := by entries

lemma blockVa : (1 - Va * Vaᵀ) * N₁ * (Va * Vaᵀ) = M₁ := by entries

lemma D_mul_N₁ : D * N₁ = 0 := by entries

lemma W_mul_N₁ : W * N₁ = 0 := by entries

lemma D_mul_V₀ : D * (V₀ * V₀ᵀ) = 0 := by entries

lemma D_mul_Va : D * (Va * Vaᵀ) = D := by entries

lemma W_mul_Va : W * (Va * Vaᵀ) = W := by entries

lemma U₀_mul_D : U₀ * U₀ᵀ * D = W := by entries

lemma U₀_mul_W : U₀ * U₀ᵀ * W = W := by entries

lemma U₀_mul_Y₀ : U₀ * U₀ᵀ * Y₀ = Y₀ := by entries

lemma Y₀_mul_V₀ : Y₀ * (V₀ * V₀ᵀ) = Y₀ := by entries

lemma Y₀_mul_Va : Y₀ * (Va * Vaᵀ) = Y₀ := by entries

lemma D_sub_W_mul_Va : (D - W) * (Va * Vaᵀ) = D - W := by
  rw [Matrix.sub_mul, D_mul_Va, W_mul_Va]

lemma idemU : U₀ * U₀ᵀ * (U₀ * U₀ᵀ) = U₀ * U₀ᵀ := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc U₀ᵀ, orthU₀, Matrix.one_mul]

lemma idemV : V₀ * V₀ᵀ * (V₀ * V₀ᵀ) = V₀ * V₀ᵀ := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc V₀ᵀ, orthV₀, Matrix.one_mul]

lemma idemVa : Va * Vaᵀ * (Va * Vaᵀ) = Va * Vaᵀ := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vaᵀ, orthVa, Matrix.one_mul]

lemma norm_M₁ : ‖M₁‖ = 12 / 25 := by
  have h1 : ‖M₁‖ ^ 2 = (12 / 25) ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    norm_num [M₁, Fin.sum_univ_three]
  rw [← Real.sqrt_sq (norm_nonneg M₁), h1]
  exact Real.sqrt_sq (by norm_num)

lemma norm_M₂ : ‖M₂‖ = 12 / 25 := by
  have h1 : ‖M₂‖ ^ 2 = (12 / 25) ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    norm_num [M₂, Fin.sum_univ_three]
  rw [← Real.sqrt_sq (norm_nonneg M₂), h1]
  exact Real.sqrt_sq (by norm_num)

/-- The Frobenius norm of the stiff direction is one, so `‖λ N₁‖ = λ`. -/
theorem norm_N₁ : ‖N₁‖ = 1 := by
  have h1 : ‖N₁‖ ^ 2 = 1 ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    norm_num [N₁, Fin.sum_univ_three]
  rw [← Real.sqrt_sq (norm_nonneg N₁), h1]
  exact Real.sqrt_sq (by norm_num)

/-- `‖D‖ = 5`: the bound `B₁` of the derivative of the exact solution. -/
theorem norm_D : ‖D‖ = 5 := by
  have h1 : ‖D‖ ^ 2 = 5 ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    norm_num [D, Fin.sum_univ_two, Fin.sum_univ_three]
  rw [← Real.sqrt_sq (norm_nonneg D), h1]
  exact Real.sqrt_sq (by norm_num)

/-- `‖D - W‖ = 4`: the normal component `ε` of the field. -/
theorem norm_D_sub_W : ‖D - W‖ = 4 := by
  have h1 : ‖D - W‖ ^ 2 = 4 ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    norm_num [D, W, Fin.sum_univ_two, Fin.sum_univ_three]
  rw [← Real.sqrt_sq (norm_nonneg (D - W)), h1]
  exact Real.sqrt_sq (by norm_num)

lemma norm_smul_M₁ {lam : ℝ} (hlam : 0 ≤ lam) : ‖lam • M₁‖ = 12 / 25 * lam := by
  rw [norm_smul, Real.norm_of_nonneg hlam, norm_M₁, mul_comm]

lemma norm_smul_M₂ {lam : ℝ} (hlam : 0 ≤ lam) : ‖lam • M₂‖ = 12 / 25 * lam := by
  rw [norm_smul, Real.norm_of_nonneg hlam, norm_M₂, mul_comm]

lemma blockV_smul (lam : ℝ) : (1 - V₀ * V₀ᵀ) * (lam • N₁) * (V₀ * V₀ᵀ) = lam • M₁ := by
  rw [Matrix.mul_smul, Matrix.smul_mul, blockV]

lemma blockV'_smul (lam : ℝ) : V₀ * V₀ᵀ * (lam • N₁) * (1 - V₀ * V₀ᵀ) = lam • M₂ := by
  rw [Matrix.mul_smul, Matrix.smul_mul, blockV']

lemma blockVa_smul (lam : ℝ) : (1 - Va * Vaᵀ) * (lam • N₁) * (Va * Vaᵀ) = lam • M₁ := by
  rw [Matrix.mul_smul, Matrix.smul_mul, blockVa]

/-- If `z Q = 0`, then `z N Q` sees only the off-diagonal block `(1 - Q) N Q` of `N`. -/
private lemma block_right {m n : Type*} [Fintype n] [DecidableEq n] {z : Matrix m n ℝ}
    {Q : Matrix n n ℝ} (N : Matrix n n ℝ) (hz : z * Q = 0) :
    z * N * Q = z * ((1 - Q) * N * Q) := by
  have h1 : z * (Q * N * Q) = 0 := by
    rw [Matrix.mul_assoc Q N Q, ← Matrix.mul_assoc z Q (N * Q), hz, Matrix.zero_mul]
  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, h1, sub_zero,
    Matrix.mul_assoc]

/-- If `y Q = y`, then `y N - y N Q` sees only the off-diagonal block `Q N (1 - Q)` of `N`. -/
private lemma block_left {m n : Type*} [Fintype n] [DecidableEq n] {y : Matrix m n ℝ}
    {Q : Matrix n n ℝ} (N : Matrix n n ℝ) (hy : y * Q = y) :
    y * N - y * N * Q = y * (Q * N * (1 - Q)) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hy, Matrix.mul_sub, Matrix.mul_one]

/-- The stiff operator `Y ↦ Y (λ N₁)`. Its norm grows with `λ` (`norm_N₁`). -/
noncomputable def stiffOp (lam : ℝ) : Matrix (Fin 2) (Fin 3) ℝ →L[ℝ] Matrix (Fin 2) (Fin 3) ℝ :=
  Frobenius.rightMulCLM (lam • N₁)

/-- The field `F(t, Y) = Y (λ N₁) + (D - Y₀ (λ N₁))`: the stiff operator and a constant. -/
noncomputable def field (lam : ℝ) (_ : ℝ) (x : Matrix (Fin 2) (Fin 3) ℝ) :
    Matrix (Fin 2) (Fin 3) ℝ :=
  stiffOp lam x + (D - Y₀ * (lam • N₁))

/-- **The coupling number of the K-step projector is `(12/25) λ`,** first inequality: the block
`(1 - V₀ V₀ᵀ) (λ N₁) V₀ V₀ᵀ` has Frobenius norm `(12/25) λ`, less than half of `‖λ N₁‖ = λ`. -/
theorem coupling_Q₀ {lam : ℝ} (hlam : 0 ≤ lam) (x : Matrix (Fin 2) (Fin 3) ℝ) :
    ‖rightProj V₀ (stiffOp lam (x - rightProj V₀ x))‖
      ≤ 12 / 25 * lam * ‖x - rightProj V₀ x‖ := by
  have hz : (x - x * (V₀ * V₀ᵀ)) * (V₀ * V₀ᵀ) = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc x, idemV, sub_self]
  change ‖(x - x * (V₀ * V₀ᵀ)) * (lam • N₁) * (V₀ * V₀ᵀ)‖
    ≤ 12 / 25 * lam * ‖x - x * (V₀ * V₀ᵀ)‖
  rw [block_right (lam • N₁) hz, blockV_smul]
  have h1 := Frobenius.norm_mul_le (x - x * (V₀ * V₀ᵀ)) (lam • M₁)
  rw [norm_smul_M₁ hlam] at h1
  linarith

/-- The coupling number of the K-step projector, second inequality. -/
theorem coupling_Q₀' {lam : ℝ} (hlam : 0 ≤ lam) (x : Matrix (Fin 2) (Fin 3) ℝ) :
    ‖stiffOp lam (rightProj V₀ x) - rightProj V₀ (stiffOp lam (rightProj V₀ x))‖
      ≤ 12 / 25 * lam * ‖rightProj V₀ x‖ := by
  have hy : x * (V₀ * V₀ᵀ) * (V₀ * V₀ᵀ) = x * (V₀ * V₀ᵀ) := by
    rw [Matrix.mul_assoc x, idemV]
  change ‖x * (V₀ * V₀ᵀ) * (lam • N₁) - x * (V₀ * V₀ᵀ) * (lam • N₁) * (V₀ * V₀ᵀ)‖
    ≤ 12 / 25 * lam * ‖x * (V₀ * V₀ᵀ)‖
  rw [block_left (lam • N₁) hy, blockV'_smul]
  have h1 := Frobenius.norm_mul_le (x * (V₀ * V₀ᵀ)) (lam • M₂)
  rw [norm_smul_M₂ hlam] at h1
  linarith

/-- The stiff operator acts from the right, so it commutes with the L-step projector. -/
theorem coupling_P₀ (lam : ℝ) (x : Matrix (Fin 2) (Fin 3) ℝ) :
    leftProj U₀ (stiffOp lam (x - leftProj U₀ x)) = 0 := by
  change U₀ * U₀ᵀ * ((x - U₀ * U₀ᵀ * x) * (lam • N₁)) = 0
  rw [← Matrix.mul_assoc (U₀ * U₀ᵀ) (x - U₀ * U₀ᵀ * x), Matrix.mul_sub,
    ← Matrix.mul_assoc (U₀ * U₀ᵀ) (U₀ * U₀ᵀ) x, idemU, sub_self, Matrix.zero_mul]

/-- The second identity for the L-step projector. -/
theorem coupling_P₀' (lam : ℝ) (x : Matrix (Fin 2) (Fin 3) ℝ) :
    stiffOp lam (leftProj U₀ x) - leftProj U₀ (stiffOp lam (leftProj U₀ x)) = 0 := by
  change U₀ * U₀ᵀ * x * (lam • N₁) - U₀ * U₀ᵀ * (U₀ * U₀ᵀ * x * (lam • N₁)) = 0
  rw [← Matrix.mul_assoc (U₀ * U₀ᵀ) (U₀ * U₀ᵀ * x), ← Matrix.mul_assoc (U₀ * U₀ᵀ) (U₀ * U₀ᵀ) x,
    idemU, sub_self]

/-- The space of the example. -/
local notation "𝕄" => Matrix (Fin 2) (Fin 3) ℝ

/-- The coupling number of the Galerkin projector `P₁ Q₁` is `(12/25) λ` as well. -/
theorem coupling_aug {lam : ℝ} (hlam : 0 ≤ lam) (x : Matrix (Fin 2) (Fin 3) ℝ) :
    ‖(leftProj U₀ * rightProj Va : 𝕄 →L[ℝ] 𝕄)
        (stiffOp lam (x - (leftProj U₀ * rightProj Va : 𝕄 →L[ℝ] 𝕄) x))‖
      ≤ 12 / 25 * lam * ‖x - (leftProj U₀ * rightProj Va : 𝕄 →L[ℝ] 𝕄) x‖ := by
  change ‖U₀ * U₀ᵀ * ((x - U₀ * U₀ᵀ * (x * (Va * Vaᵀ))) * (lam • N₁) * (Va * Vaᵀ))‖
    ≤ 12 / 25 * lam * ‖x - U₀ * U₀ᵀ * (x * (Va * Vaᵀ))‖
  obtain ⟨z, hz⟩ : ∃ z, z = x - U₀ * U₀ᵀ * (x * (Va * Vaᵀ)) := ⟨_, rfl⟩
  have hz0 : U₀ * U₀ᵀ * z * (Va * Vaᵀ) = 0 := by
    rw [hz, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc (U₀ * U₀ᵀ) (U₀ * U₀ᵀ), idemU,
      Matrix.mul_assoc (U₀ * U₀ᵀ) (x * (Va * Vaᵀ)), Matrix.mul_assoc x, idemVa,
      ← Matrix.mul_assoc (U₀ * U₀ᵀ) x (Va * Vaᵀ), sub_self]
  have hn : ‖U₀ * U₀ᵀ * z‖ ≤ ‖z‖ := (isOrthProj_leftProj orthU₀).norm_le z
  rw [← hz, ← Matrix.mul_assoc (U₀ * U₀ᵀ) (z * (lam • N₁)), ← Matrix.mul_assoc (U₀ * U₀ᵀ) z,
    block_right (lam • N₁) hz0, blockVa_smul]
  have h1 := Frobenius.norm_mul_le (U₀ * U₀ᵀ * z) (lam • M₁)
  rw [norm_smul_M₁ hlam] at h1
  have h2 := mul_le_mul_of_nonneg_left hn (by linarith : (0 : ℝ) ≤ 12 / 25 * lam)
  linarith

local macro "sums" : tactic =>
  `(tactic| (simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, N₁] <;> try ring1))

lemma inner_mul_N₁ (z : Matrix (Fin 2) (Fin 3) ℝ) :
    ⟪z * N₁, z⟫ = -(z 0 1 * z 0 1 + z 1 1 * z 1 1) := by
  rw [Frobenius.inner_def]
  sums

/-- The field is one-sided Lipschitz with constant `0` for every `λ ≥ 0`, although its Lipschitz
constant grows with `λ`. -/
theorem oneSided {lam : ℝ} (hlam : 0 ≤ lam) : IsOneSidedLipschitzField (field lam) 0 := by
  intro t x y
  have e : field lam t x - field lam t y = lam • ((x - y) * N₁) := by
    change x * (lam • N₁) + (D - Y₀ * (lam • N₁)) - (y * (lam • N₁) + (D - Y₀ * (lam • N₁)))
      = lam • ((x - y) * N₁)
    rw [← Matrix.mul_smul, Matrix.sub_mul]
    abel
  rw [e, real_inner_smul_left, inner_mul_N₁, zero_mul]
  nlinarith [mul_nonneg hlam (mul_self_nonneg ((x - y) 0 1)),
    mul_nonneg hlam (mul_self_nonneg ((x - y) 1 1))]

lemma field_start (lam t : ℝ) : field lam t Y₀ = D := by
  change Y₀ * (lam • N₁) + (D - Y₀ * (lam • N₁)) = D
  abel

/-- Along `Y₀ + s C` with `C N₁ = 0` the field has the constant value `D`. -/
lemma field_affine (lam t s : ℝ) {C : Matrix (Fin 2) (Fin 3) ℝ} (hC : C * N₁ = 0) :
    field lam t (Y₀ + s • C) = D := by
  change (Y₀ + s • C) * (lam • N₁) + (D - Y₀ * (lam • N₁)) = D
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul C, hC, smul_zero, smul_zero]
  abel

lemma stiffOp_field (lam t : ℝ) : stiffOp lam (field lam t (Y₀ + t • D)) = 0 := by
  rw [field_affine lam t t D_mul_N₁]
  change D * (lam • N₁) = 0
  rw [Matrix.mul_smul, D_mul_N₁, smul_zero]

private lemma odeSolution_affine
    {f : ℝ → Matrix (Fin 2) (Fin 3) ℝ → Matrix (Fin 2) (Fin 3) ℝ}
    {C : Matrix (Fin 2) (Fin 3) ℝ} (hf : ∀ t, f t (Y₀ + t • C) = C) (a b : ℝ) :
    ODESolution f (fun t => Y₀ + t • C) a b := by
  refine ODESolution.of_hasDerivAt (fun t => ?_) a b
  have h : HasDerivAt (fun s : ℝ => Y₀ + s • C) ((1 : ℝ) • C) t :=
    ((hasDerivAt_id t).smul_const C).const_add Y₀
  have h' : HasDerivAt (fun s : ℝ => Y₀ + s • C) (f t (Y₀ + t • C)) t := by
    rw [hf t]
    rwa [one_smul] at h
  exact h'

/-- The exact solution `A(t) = Y₀ + t D`. -/
theorem exactSol (lam h : ℝ) : ODESolution (field lam) (fun t => Y₀ + t • D) 0 h :=
  odeSolution_affine (fun t => field_affine lam t t D_mul_N₁) 0 h

/-- The K-step is stationary: `D V₀ = 0`. -/
theorem kSol (lam h : ℝ) :
    ODESolution (fun t x => rightProj V₀ (field lam t x)) (fun _ => Y₀) 0 h := by
  refine ⟨continuousOn_const, fun t _ => ?_⟩
  have e : rightProj V₀ (field lam t Y₀) = 0 := by
    rw [field_start]
    exact D_mul_V₀
  change HasDerivWithinAt (fun _ : ℝ => Y₀) (rightProj V₀ (field lam t Y₀)) (Ici t) t
  rw [e]
  exact hasDerivWithinAt_const t (Ici t) Y₀

/-- The L-step: `Y₀ + t W` with `W = U₀ U₀ᵀ D`. -/
theorem lSol (lam h : ℝ) :
    ODESolution (fun t x => leftProj U₀ (field lam t x)) (fun t => Y₀ + t • W) 0 h :=
  odeSolution_affine (fun t => by
    rw [field_affine lam t t W_mul_N₁]
    exact U₀_mul_D) 0 h

/-- The Galerkin step: `Y₀ + t W` again. -/
theorem sSol (lam h : ℝ) :
    ODESolution (fun t x => leftProj U₀ (rightProj Va (field lam t x)))
      (fun t => Y₀ + t • W) 0 h :=
  odeSolution_affine (fun t => by
    rw [field_affine lam t t W_mul_N₁]
    change U₀ * U₀ᵀ * (D * (Va * Vaᵀ)) = W
    rw [D_mul_Va, U₀_mul_D]) 0 h

/-- A rank-adaptive BUG step of the example over `[0, h]`: the old bases are `U₀` and `V₀`, the
augmented right basis is `Va`, the normal components are bounded by `ε = 4`, and nothing is
truncated (`ϑ = 0`). None of the four projectors is the identity. -/
theorem step (lam h : ℝ) :
    IsRankAdaptiveBUGStep (field lam) 4 0 (leftProj U₀) (rightProj V₀) (leftProj U₀)
      (rightProj Va) 0 h Y₀ (fun _ => Y₀) (fun t => Y₀ + t • W) (fun t => Y₀ + t • W)
      (Y₀ + h • W) :=
  { projP₀ := isOrthProj_leftProj orthU₀
    projQ₀ := isOrthProj_rightProj orthV₀
    projP₁ := isOrthProj_leftProj orthU₀
    projQ₁ := isOrthProj_rightProj orthVa
    comm₁ := fun x => leftProj_rightProj_comm U₀ Va x
    kSol := kSol lam h
    kStart := rfl
    kCap := U₀_mul_Y₀
    kNormal := fun t _ => by
      have e : (1 - leftProj U₀) ((1 - rightProj V₀) (field lam t Y₀)) = D - W := by
        rw [field_start]
        change (D - D * (V₀ * V₀ᵀ)) - U₀ * U₀ᵀ * (D - D * (V₀ * V₀ᵀ)) = D - W
        rw [D_mul_V₀, sub_zero, U₀_mul_D]
      exact le_of_eq ((congrArg norm e).trans norm_D_sub_W)
    lSol := lSol lam h
    lStart := by
      rw [zero_smul, add_zero]
    lCap := by
      change (Y₀ + h • W) * (Va * Vaᵀ) = Y₀ + h • W
      rw [Matrix.add_mul, Matrix.smul_mul, Y₀_mul_Va, W_mul_Va]
    lNormal := fun t _ => by
      have e : (1 - rightProj Va) ((1 - leftProj U₀) (field lam t (Y₀ + h • W))) = 0 := by
        rw [field_affine lam t h W_mul_N₁]
        change (D - U₀ * U₀ᵀ * D) - (D - U₀ * U₀ᵀ * D) * (Va * Vaᵀ) = 0
        rw [U₀_mul_D, D_sub_W_mul_Va, sub_self]
      exact (congrArg norm e).trans_le (by rw [norm_zero]; norm_num)
    sSol := sSol lam h
    sStart := by
      change Y₀ + (0 : ℝ) • W = U₀ * U₀ᵀ * (Y₀ * (Va * Vaᵀ))
      rw [zero_smul, add_zero, Y₀_mul_Va, U₀_mul_Y₀]
    augP := U₀_mul_Y₀
    augQ := Y₀_mul_Va
    trunc := le_of_eq (by rw [sub_self, norm_zero]) }

/-- Non-vacuity of `IsRankAdaptiveBUGStep.stiff_local_error` with nonzero data: for every
`λ ≥ 0` and `h ≥ 0` all hypotheses hold for the step `step` with the one-sided Lipschitz constant
`ℓ = 0`, the coupling numbers `κ = κ̂ = 12/25 · λ`, `L_G = 0`, `B₁ = 5`, `B₂ = 0`, `ε = 4` and
`ϑ = 0`. For `λ > 0` the coupling numbers are smaller than the norm `λ` of the stiff operator. The
projectors are not the identity. -/
example {lam h : ℝ} (hlam : 0 ≤ lam) (hh : 0 ≤ h) :
    ‖(Y₀ + h • W) - (Y₀ + h • D)‖
      ≤ (12 / 25 * lam + 0) * (h * 5) * h * max 1 (Real.exp (0 * h))
        + 2 * stiffCapture 0 0 (12 / 25 * lam) 5 0 4 h + 0 := by
  have hκ : (0 : ℝ) ≤ 12 / 25 * lam := mul_nonneg (by norm_num) hlam
  exact (step lam h).stiff_local_error (G := fun _ _ => D - Y₀ * (lam • N₁))
    (𝓛 := stiffOp lam) (A := fun t => Y₀ + t • D) (oneSided hlam) (fun _ _ => rfl)
    (fun _ _ _ => by simp) le_rfl hκ hκ (coupling_Q₀ hlam) (coupling_Q₀' hlam)
    (fun _ => by rw [coupling_P₀, norm_zero]; exact mul_nonneg hκ (norm_nonneg _))
    (fun _ => by rw [coupling_P₀', norm_zero]; exact mul_nonneg hκ (norm_nonneg _))
    (coupling_aug hlam) (zero_add h).symm hh (exactSol lam h)
    (by rw [zero_smul, add_zero])
    (fun t _ => le_of_eq ((congrArg norm (field_affine lam t t D_mul_N₁)).trans norm_D))
    (fun t _ => le_of_eq ((congrArg norm (stiffOp_field lam t)).trans norm_zero))
    U₀_mul_Y₀ Y₀_mul_V₀

/-- The error of the step of the example is exactly `4 h = h ε`. The bound of
`IsRankAdaptiveBUGStep.stiff_local_error` is `2 h ε` plus terms of order `h²` and higher. -/
theorem error_eq {h : ℝ} (hh : 0 ≤ h) : ‖(Y₀ + h • W) - (Y₀ + h • D)‖ = 4 * h := by
  have e : (Y₀ + h • W) - (Y₀ + h • D) = -(h • (D - W)) := by
    rw [smul_sub]
    abel
  rw [e, norm_neg, norm_smul, Real.norm_of_nonneg hh, norm_D_sub_W, mul_comm]

/-- A matrix orthogonal to the range of `Q₀`, of norm `1`. -/
noncomputable def X₁ : Matrix (Fin 2) (Fin 3) ℝ := !![4 / 5, -(3 / 5), 0; 0, 0, 0]

/-- The image `Q₀ (X₁ N₁)`, of norm `12/25`. -/
noncomputable def X₂ : Matrix (Fin 2) (Fin 3) ℝ := !![36 / 125, 48 / 125, 0; 0, 0, 0]

local macro "entries'" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Fin.sum_univ_three, V₀, N₁, X₁, X₂] <;> try norm_num))

lemma X₁_mul_V₀ : X₁ * (V₀ * V₀ᵀ) = 0 := by entries'

lemma X₁_mul_N₁_mul_V₀ : X₁ * N₁ * (V₀ * V₀ᵀ) = X₂ := by entries'

lemma norm_X₁ : ‖X₁‖ = 1 := by
  have h1 : ‖X₁‖ ^ 2 = 1 ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    norm_num [X₁, Fin.sum_univ_two, Fin.sum_univ_three]
  rw [← Real.sqrt_sq (norm_nonneg X₁), h1]
  exact Real.sqrt_sq (by norm_num)

lemma norm_X₂ : ‖X₂‖ = 12 / 25 := by
  have h1 : ‖X₂‖ ^ 2 = (12 / 25) ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    norm_num [X₂, Fin.sum_univ_two, Fin.sum_univ_three]
  rw [← Real.sqrt_sq (norm_nonneg X₂), h1]
  exact Real.sqrt_sq (by norm_num)

/-- The coupling number `12/25 · λ` of `coupling_Q₀` is attained at `X₁`: for `λ > 0` the
coupling of the stiff operator with the projector `Q₀` is not zero. -/
theorem coupling_Q₀_attained {lam : ℝ} (hlam : 0 ≤ lam) :
    ‖rightProj V₀ (stiffOp lam (X₁ - rightProj V₀ X₁))‖
      = 12 / 25 * lam * ‖X₁ - rightProj V₀ X₁‖ := by
  have e1 : X₁ - rightProj V₀ X₁ = X₁ := by
    change X₁ - X₁ * (V₀ * V₀ᵀ) = X₁
    rw [X₁_mul_V₀, sub_zero]
  have e2 : rightProj V₀ (stiffOp lam X₁) = lam • X₂ := by
    change X₁ * (lam • N₁) * (V₀ * V₀ᵀ) = lam • X₂
    rw [Matrix.mul_smul, Matrix.smul_mul, X₁_mul_N₁_mul_V₀]
  rw [e1, e2, norm_smul, Real.norm_of_nonneg hlam, norm_X₁, norm_X₂]
  ring

end StiffCouplingExample

end LeanDLRA
