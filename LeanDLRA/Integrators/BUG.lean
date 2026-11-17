import LeanDLRA.Integrators.Defs
import LeanDLRA.Integrators.KStep

/-!
# Robust error bound of the basis-update & Galerkin (BUG) integrator

This file formalises the central result of Ceruti–Lubich, *An unconventional robust integrator
for dynamical low-rank approximation* (BIT 2022, [CerutiLubich2022]): the BUG ("unconventional")
integrator has local error `O(h (h + ε))` and global error `O(δ + ε + h)` with constants that are
**independent of the singular values** of the exact and the approximate solution
([CerutiLubich2022], Lemmas 2–4 and Theorem 4).

## The integrator as full-space trajectories

As in the rest of the library, the integrator is written abstractly on a real inner product
space `E` with orthogonal projectors.  One step from `Y₀ = U₀ S₀ V₀ᵀ` at `t₀` to `t₁ = t₀ + h`
consists of (with `P₀ X = U₀ U₀ᵀ X`, `Q₀ X = X V₀ V₀ᵀ` and the new projectors
`P₁ X = U₁ U₁ᵀ X`, `Q₁ X = X V₁ V₁ᵀ`):

* **K-step** `K' = F(t, K V₀ᵀ) V₀`: the trajectory `YK = K V₀ᵀ` solves `YK' = Q₀ F(t, YK)`,
  `YK t₀ = Y₀`; the new basis `U₁` spans the range of `K(t₁)`: `P₁ (YK t₁) = YK t₁`;
* **L-step** `L' = F(t, U₀ Lᵀ)ᵀ U₀`: the trajectory `YL = U₀ Lᵀ` solves `YL' = P₀ F(t, YL)`,
  `YL t₀ = Y₀`, and `Q₁ (YL t₁) = YL t₁`;
* **S-step (Galerkin)** `S' = U₁ᵀ F(t, U₁ S V₁ᵀ) V₁`, `S(t₀) = U₁ᵀ Y₀ V₁`: the trajectory
  `YS = U₁ S V₁ᵀ` solves `YS' = P₁ Q₁ F(t, YS)`, `YS t₀ = P₁ Q₁ Y₀`, and `Y₁ = YS t₁`.

`P₁` and `Q₁` commute (left and right multiplication).  The normal-component assumption
(assumption 2 of Theorem 2 of [CerutiLubich2022]) is only used at the points `YK t₁` and `YL t₁`,
in the form `‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε` and
`‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε`.  All hypotheses of one step are bundled in the
predicate `IsBUGStep`.

## Main results

With `F` `L`-Lipschitz and bounded by `B`, and `ϑ = h (4 L B h + ε)`:

* `galerkin_step_error`: a Galerkin step with an orthogonal projector `R` whose range captures the
  exact solution at `t₁` up to `θ` has error `≤ (e^{L h} - 1) (B h + θ) + θ`;
* `bug_capture` (Lemma 3 of [CerutiLubich2022]): `‖A t₁ - P₁ Q₁ A t₁‖ ≤ 2 ϑ`;
* `bug_local_error` (Lemma 4): `‖Y₁ - A t₁‖ ≤ (e^{L h} - 1) (B h + 2ϑ) + 2ϑ`;
* `bug_local_error_le` (Lemma 4, `O`-form): for `0 ≤ h ≤ H`,
  `‖Y₁ - A t₁‖ ≤ h (c₁ ε + c₂ h)` with `c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`;
* `bug_global_error` (Theorem 4): for a sequence of BUG steps on the grid `tₙ = t₀ + n h`,
  `‖Yₙ - A tₙ‖ ≤ e^{L n h} (‖Y₀ - A t₀‖ + n h (c₁ ε + c₂ h))`;
* `bug_global_error_le` (Theorem 4, final form): for `n h ≤ T` and `‖Y₀ - A t₀‖ ≤ δ`,
  `‖Yₙ - A tₙ‖ ≤ c₀ δ + c₁' ε + c₂' h` with `c₀ = e^{L T}`, `c₁' = T e^{L T} c₁`,
  `c₂' = T e^{L T} c₂`, constants depending only on `L`, `B`, `T`, `H`.

## Deviations from the paper

* The paper proves Lemma 2 by quoting the local error analysis of the projector-splitting
  integrator.  We instead use the direct K-step capture lemma `kstep_capture`, which
  gives the explicit `ϑ = h (4 L B h + ε)` (for exact initial data, `δ = 0` in the paper's (5)).
* The comparison in Lemma 4 is done in the full space with `Z = P₁ Q₁ A` instead of the small
  matrix `S̃ = U₁ᵀ A V₁`, and the remainder is estimated by `‖(1 - P₁ Q₁) A(t)‖ ≤ B h + 2ϑ`
  (instead of the paper's `2 B h + 2ϑ`), which gives the explicit constants above.
* Everything is stated for an arbitrary real inner product space, so the result covers matrices
  (Frobenius norm), and any other setting with two commuting orthogonal "row/column" projectors.
* The exact flows `Φ n` from the numerical values (needed for Lady Windermere's fan) are
  hypotheses; their existence for globally Lipschitz, time-continuous `F` is proved in
  `Foundations/Existence.lean`.
-/

open Set

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Auxiliary inequalities -/

section Aux

/-- `gronwallBound 0 L (L c) x = (e^{L x} - 1) c`. -/
lemma gronwallBound_zero_mul (L c x : ℝ) :
    gronwallBound 0 L (L * c) x = (Real.exp (L * x) - 1) * c := by
  rcases eq_or_ne L 0 with rfl | hL
  · simp [gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 hL]
    simp only
    rw [mul_div_cancel_left₀ c hL]
    ring

/-- `e^x - 1 ≤ x e^x`. -/
lemma exp_sub_one_le_mul_exp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := Real.add_one_le_exp (-x)
  have hpos := Real.exp_pos x
  have hmul : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  nlinarith

lemma bugC₁_nonneg {L H : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H) : 0 ≤ bugC₁ L H := by
  unfold bugC₁; positivity

lemma bugC₂_nonneg {L B H : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hH : 0 ≤ H) : 0 ≤ bugC₂ L B H := by
  unfold bugC₂; positivity

/-- The explicit local bound `(e^{L h} - 1) (B h + 2ϑ) + 2ϑ`, `ϑ = h (4 L B h + ε)`, is bounded by
`h (c₁ ε + c₂ h)` for `0 ≤ h ≤ H`. -/
lemma bug_bound_le {L B ε h H : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hε : 0 ≤ ε) (hh : 0 ≤ h)
    (hhH : h ≤ H) :
    (Real.exp (L * h) - 1) * (B * h + 2 * (h * (4 * L * B * h + ε)))
        + 2 * (h * (4 * L * B * h + ε))
      ≤ h * (bugC₁ L H * ε + bugC₂ L B H * h) := by
  set e := Real.exp (L * H) with he
  have hLh : 0 ≤ L * h := mul_nonneg hL hh
  have hexp : Real.exp (L * h) ≤ e := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hL)
  have h1 : Real.exp (L * h) - 1 ≤ L * h * e :=
    (exp_sub_one_le_mul_exp (L * h)).trans (mul_le_mul_of_nonneg_left hexp hLh)
  have hX : 0 ≤ B * h + 2 * (h * (4 * L * B * h + ε)) := by positivity
  have h2 : (Real.exp (L * h) - 1) * (B * h + 2 * (h * (4 * L * B * h + ε)))
      ≤ L * h * e * (B * h + 2 * (h * (4 * L * B * h + ε))) :=
    mul_le_mul_of_nonneg_right h1 hX
  have hgap : 0 ≤ 2 * L * e * h * ε * (H - h) + 8 * L ^ 2 * B * e * h ^ 2 * (H - h) := by
    have hHh : 0 ≤ H - h := by linarith
    have he0 : 0 ≤ e := (Real.exp_pos _).le
    positivity
  have hid : h * (bugC₁ L H * ε + bugC₂ L B H * h)
      = L * h * e * (B * h + 2 * (h * (4 * L * B * h + ε))) + 2 * (h * (4 * L * B * h + ε))
        + (2 * L * e * h * ε * (H - h) + 8 * L ^ 2 * B * e * h ^ 2 * (H - h)) := by
    unfold bugC₁ bugC₂; rw [← he]; ring
  rw [hid]
  linarith

end Aux

/-! ### The Galerkin step and the local error -/

section Local

variable {F : ℝ → E → E} {L B ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

/-- **Error of a Galerkin step** (core of Lemma 4 of [CerutiLubich2022]).  Let `R` be an orthogonal
projector, `F` `L`-Lipschitz (`L ≥ 0`) and bounded by `B`, `A` a solution of `A' = F(t, A)` on
`[t₀, t₁]`, `t₁ = t₀ + h`, `h ≥ 0`, and `YS` the Galerkin trajectory `YS' = R F(t, YS)` with
`YS t₀ = R (A t₀)`.  If the range of `R` captures the exact solution at the end of the step,
`‖A t₁ - R (A t₁)‖ ≤ θ`, then

    ‖YS t₁ - A t₁‖ ≤ (e^{L h} - 1) (B h + θ) + θ.

(Proof: compare `YS` with `Z = R A` by Grönwall; the defect of `Z` is
`‖R F(t, A) - R F(t, Z)‖ ≤ L ‖(1 - R) A t‖ ≤ L (B h + θ)`.) -/
theorem galerkin_step_error {R : E →L[ℝ] E} (hR : IsOrthProj R) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) {YS : ℝ → E} (hS : ODESolution (fun t x => R (F t x)) YS t₀ t₁)
    (hS₀ : YS t₀ = R (A t₀)) {θ : ℝ} (hθ : ‖A t₁ - R (A t₁)‖ ≤ θ) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + θ) + θ := by
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
  have hgr := norm_sub_le_gronwallBound hfL hL (y := YS) (z := fun t => R (A t))
    (u := fun t => R (F t (YS t))) (w := fun t => R (F t (A t))) (ηy := 0)
    (ηz := L * (B * h + θ)) (δ := 0) hS.cont hS.deriv (fun _ _ => by simp) hZc hZd hdef
    (by simp [hS₀]) t₁ ⟨hle, le_rfl⟩
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [zero_add, hlen, gronwallBound_zero_mul] at hgr
  calc ‖YS t₁ - A t₁‖ ≤ ‖YS t₁ - R (A t₁)‖ + ‖R (A t₁) - A t₁‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (Real.exp (L * h) - 1) * (B * h + θ) + θ := by
        rw [norm_sub_rev (R (A t₁))]
        exact add_le_add hgr hθ

/-- Capture by a product of projectors: `‖x - P (Q x)‖ ≤ ‖(1 - P) x‖ + ‖(1 - Q) x‖` for an
orthogonal projector `P` (no assumption on `Q`). -/
lemma norm_sub_apply_apply_le {P Q : E →L[ℝ] E} (hP : IsOrthProj P) (x : E) :
    ‖x - P (Q x)‖ ≤ ‖(1 - P) x‖ + ‖(1 - Q) x‖ := by
  have hdec : x - P (Q x) = (x - P x) + P (x - Q x) := by rw [map_sub]; abel
  rw [hdec]
  calc _ ≤ ‖x - P x‖ + ‖P (x - Q x)‖ := norm_add_le _ _
    _ ≤ ‖x - P x‖ + ‖x - Q x‖ := add_le_add le_rfl (hP.norm_le _)
    _ = ‖(1 - P) x‖ + ‖(1 - Q) x‖ := by simp

/-- **Lemma 3 of [CerutiLubich2022] (abstract form).**  If the K-step and the L-step capture
conditions hold (see `kstep_capture`), the new left and right bases together capture the exact
solution: `‖A t₁ - P₁ Q₁ A t₁‖ ≤ 2 ϑ`, `ϑ = h (4 L B h + ε)`. -/
theorem bug_capture {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {YK YL : ℝ → E} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (hP₀ : IsOrthProj P₀) (hQ₀ : IsOrthProj Q₀)
    (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = A t₀)
    (hKcap : P₁ (YK t₁) = YK t₁)
    (hεK : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε)
    (hLs : ODESolution (fun t x => P₀ (F t x)) YL t₀ t₁) (hL₀ : YL t₀ = A t₀)
    (hLcap : Q₁ (YL t₁) = YL t₁)
    (hεL : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε) :
    ‖A t₁ - P₁ (Q₁ (A t₁))‖ ≤ 2 * (h * (4 * L * B * h + ε)) := by
  have h1 := kstep_capture hF hL hB hP₁ hQ₀ ht₁ hh hA hK hK₀ hKcap hεK
  have h2 := kstep_capture hF hL hB hQ₁ hP₀ ht₁ hh hA hLs hL₀ hLcap hεL
  have h3 := norm_sub_apply_apply_le (Q := Q₁) hP₁ (A t₁)
  linarith

/-- **Robust local error of the BUG integrator** (Ceruti–Lubich, [CerutiLubich2022, Lemma 4],
with explicit constants).  Let `F` be `L`-Lipschitz (`L ≥ 0`) and bounded by `B`, `A` the exact
solution on `[t₀, t₁]`, `t₁ = t₀ + h`, `h ≥ 0`, with `A t₀ = Y₀`.  Assume

* K-step: `YK' = Q₀ F(t, YK)`, `YK t₀ = Y₀`, `P₁ (YK t₁) = YK t₁`,
  `‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε` on `[t₀, t₁]`;
* L-step: `YL' = P₀ F(t, YL)`, `YL t₀ = Y₀`, `Q₁ (YL t₁) = YL t₁`,
  `‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε` on `[t₀, t₁]`;
* S-step: `YS' = P₁ Q₁ F(t, YS)`, `YS t₀ = P₁ Q₁ Y₀`,

where `P₀, Q₀, P₁, Q₁` are orthogonal projectors and `P₁`, `Q₁` commute.  Then, with
`ϑ = h (4 L B h + ε)`,

    ‖YS t₁ - A t₁‖ ≤ (e^{L h} - 1) (B h + 2ϑ) + 2ϑ  ( = O(h (h + ε)) ).

The bound does not involve singular values: no rank or invertibility assumption is made. -/
theorem bug_local_error {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {Y₀ : E} {YK YL YS : ℝ → E}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hP₀ : IsOrthProj P₀)
    (hQ₀ : IsOrthProj Q₀) (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁)
    (hc : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = Y₀)
    (hKcap : P₁ (YK t₁) = YK t₁)
    (hεK : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε)
    (hLs : ODESolution (fun t x => P₀ (F t x)) YL t₀ t₁) (hL₀ : YL t₀ = Y₀)
    (hLcap : Q₁ (YL t₁) = YL t₁)
    (hεL : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε)
    (hS : ODESolution (fun t x => P₁ (Q₁ (F t x))) YS t₀ t₁) (hS₀ : YS t₀ = P₁ (Q₁ Y₀)) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + 2 * (h * (4 * L * B * h + ε)))
      + 2 * (h * (4 * L * B * h + ε)) := by
  have hcap := bug_capture hF hL hB hP₀ hQ₀ hP₁ hQ₁ ht₁ hh hA hK (hK₀.trans hA₀.symm) hKcap hεK
    hLs (hL₀.trans hA₀.symm) hLcap hεL
  exact galerkin_step_error (R := P₁ * Q₁) (hP₁.mul hQ₁ hc) hF hL hB ht₁ hh hA hS
    (by rw [hS₀, hA₀]; rfl) hcap

/-- All hypotheses of one step of the BUG integrator from `(t₀, Y₀)` to `t₁` with initial
projectors `P₀, Q₀` (bases `U₀`, `V₀`), new projectors `P₁, Q₁` (bases `U₁`, `V₁`), K-, L- and
S-step trajectories `YK`, `YL`, `YS` (the new approximation is `YS t₁`), and normal-component
bound `ε` at the points `YK t₁`, `YL t₁`. -/
structure IsBUGStep (F : ℝ → E → E) (ε : ℝ) (P₀ Q₀ P₁ Q₁ : E →L[ℝ] E) (t₀ t₁ : ℝ) (Y₀ : E)
    (YK YL YS : ℝ → E) : Prop where
  projP₀ : IsOrthProj P₀
  projQ₀ : IsOrthProj Q₀
  projP₁ : IsOrthProj P₁
  projQ₁ : IsOrthProj Q₁
  /-- The new left and right projectors commute. -/
  comm₁ : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)
  /-- K-step: `YK' = Q₀ F(t, YK)` (the matrix K-step for `K = YK V₀`). -/
  kSol : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁
  kStart : YK t₀ = Y₀
  /-- The new left basis captures `K(t₁)`. -/
  kCap : P₁ (YK t₁) = YK t₁
  kNormal : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε
  /-- L-step: `YL' = P₀ F(t, YL)` (the matrix L-step for `Lᵀ = U₀ᵀ YL`). -/
  lSol : ODESolution (fun t x => P₀ (F t x)) YL t₀ t₁
  lStart : YL t₀ = Y₀
  /-- The new right basis captures `L(t₁)`. -/
  lCap : Q₁ (YL t₁) = YL t₁
  lNormal : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε
  /-- Galerkin S-step: `YS' = P₁ Q₁ F(t, YS)` (the matrix S-step for `S = U₁ᵀ YS V₁`). -/
  sSol : ODESolution (fun t x => P₁ (Q₁ (F t x))) YS t₀ t₁
  sStart : YS t₀ = P₁ (Q₁ Y₀)

namespace IsBUGStep

variable {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {Y₀ : E} {YK YL YS : ℝ → E}

/-- The normal-component bound forces `ε ≥ 0` on a nonempty step. -/
lemma eps_nonneg (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS) (h01 : t₀ ≤ t₁) : 0 ≤ ε :=
  (norm_nonneg _).trans (hs.kNormal t₀ ⟨le_rfl, h01⟩)

/-- **Robust local error of the BUG integrator** ([CerutiLubich2022, Lemma 4]), bundled form of
`bug_local_error`. -/
theorem local_error (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + 2 * (h * (4 * L * B * h + ε)))
      + 2 * (h * (4 * L * B * h + ε)) :=
  bug_local_error hF hL hB hs.projP₀ hs.projQ₀ hs.projP₁ hs.projQ₁ hs.comm₁ ht₁ hh hA hA₀
    hs.kSol hs.kStart hs.kCap hs.kNormal hs.lSol hs.lStart hs.lCap hs.lNormal hs.sSol hs.sStart

/-- **Robust local error of the BUG integrator, `O`-form** ([CerutiLubich2022, Lemma 4]).  For
step sizes `0 ≤ h ≤ H`: `‖YS t₁ - A t₁‖ ≤ h (c₁ ε + c₂ h)` with `c₁ = bugC₁ L H`,
`c₂ = bugC₂ L B H` depending only on `L`, `B` and the step-size bound `H` — in particular not on
singular values. -/
theorem local_error_le (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤ h * (bugC₁ L H * ε + bugC₂ L B H * h) :=
  (hs.local_error hF hL hB ht₁ hh hA hA₀).trans
    (bug_bound_le hL hB.nonneg (hs.eps_nonneg (by linarith)) hh hhH)

end IsBUGStep

/-- **Robust local error of the BUG integrator, `O`-form**, unbundled ([CerutiLubich2022],
Lemma 4): under the hypotheses of `bug_local_error` and `0 ≤ h ≤ H`,
`‖YS t₁ - A t₁‖ ≤ h (c₁ ε + c₂ h)` with `c₁ = 2 + 2 L H e^{L H}` and
`c₂ = L B (8 + e^{L H} (1 + 8 L H))`. -/
theorem bug_local_error_le {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {Y₀ : E} {YK YL YS : ℝ → E}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hP₀ : IsOrthProj P₀)
    (hQ₀ : IsOrthProj Q₀) (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁)
    (hc : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = Y₀)
    (hKcap : P₁ (YK t₁) = YK t₁)
    (hεK : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε)
    (hLs : ODESolution (fun t x => P₀ (F t x)) YL t₀ t₁) (hL₀ : YL t₀ = Y₀)
    (hLcap : Q₁ (YL t₁) = YL t₁)
    (hεL : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε)
    (hS : ODESolution (fun t x => P₁ (Q₁ (F t x))) YS t₀ t₁) (hS₀ : YS t₀ = P₁ (Q₁ Y₀)) :
    ‖YS t₁ - A t₁‖ ≤ h * (bugC₁ L H * ε + bugC₂ L B H * h) :=
  IsBUGStep.local_error_le ⟨hP₀, hQ₀, hP₁, hQ₁, hc, hK, hK₀, hKcap, hεK, hLs, hL₀, hLcap, hεL,
    hS, hS₀⟩ hF hL hB ht₁ hh hhH hA hA₀

end Local

/-! ### Global error -/

section Global

variable {F : ℝ → E → E} {L B ε : ℝ}

/-- **Robust global error bound of the BUG integrator** (Ceruti–Lubich, [CerutiLubich2022],
Theorem 4, with explicit constants).  Let `F` be `L`-Lipschitz (`L ≥ 0`) and bounded by `B`, let
`tₙ = t₀ + n h` with `0 ≤ h ≤ H`, and let `A` solve `A' = F(t, A)` on `[t₀, t₀ + N h]`.  For
`n < N` let step `n` of the BUG integrator go from `(tₙ, Y n)` to `Y (n+1) = YS n tₙ₊₁` with
projectors `P n, Q n` (old bases) and `P (n+1), Q (n+1)` (new bases), as described by
`IsBUGStep`, and let `Φ n` be the exact flow on `[tₙ, tₙ₊₁]` started at `Y n`.  Then for `n ≤ N`

    ‖Y n - A tₙ‖ ≤ e^{L n h} (‖Y 0 - A t₀‖ + n h (c₁ ε + c₂ h)),

with `c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H` independent of singular values.  (Proof: local error
`bug_local_error_le` and Lady Windermere's fan `lady_windermere`.) -/
theorem bug_global_error (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YK YL YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsBUGStep F ε (P n) (Q n) (P (n + 1)) (Q (n + 1)) (t₀ + n * h)
      (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n))
    (hY : ∀ n < N, Y (n + 1) = YS n (t₀ + (n + 1) * h))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (L * (n * h)) * (‖Y 0 - A t₀‖ + n * h * (bugC₁ L H * ε + bugC₂ L B H * h)) := by
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤
      h * (bugC₁ L H * ε + bugC₂ L B H * h) := by
    intro n hn
    rw [hY n hn]
    exact (hstep n hn).local_error_le hF hL hB (by ring) hh hhH (hΦ n hn) (hΦ₀ n hn)
  intro n hn
  calc _ ≤ _ := lady_windermere hF hL hh hA hΦ hΦ₀ hloc n hn
    _ = _ := by ring

/-- **Robust global error bound of the BUG integrator, final form** (Ceruti–Lubich,
[CerutiLubich2022, Thm. 4] / Theorem 2): under the hypotheses of `bug_global_error`, with an
initial error `‖Y 0 - A t₀‖ ≤ δ`, `ε ≥ 0`, and `n h ≤ T`,

    ‖Y n - A tₙ‖ ≤ c₀ δ + c₁' ε + c₂' h,

with `c₀ = e^{L T}`, `c₁' = T e^{L T} c₁`, `c₂' = T e^{L T} c₂` depending only on `L`, `B`, `T`
and the step-size bound `H` — in particular not on singular values. -/
theorem bug_global_error_le (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hε : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YK YL YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsBUGStep F ε (P n) (Q n) (P (n + 1)) (Q (n + 1)) (t₀ + n * h)
      (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n))
    (hY : ∀ n < N, Y (n + 1) = YS n (t₀ + (n + 1) * h))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * bugC₁ L H * ε + T * Real.exp (L * T) * bugC₂ L B H * h := by
  intro n hn hT
  have hH : 0 ≤ H := hh.trans hhH
  have hg : 0 ≤ bugC₁ L H * ε + bugC₂ L B H * h :=
    add_nonneg (mul_nonneg (bugC₁_nonneg hL hH) hε)
      (mul_nonneg (bugC₂_nonneg hL hB.nonneg hH) hh)
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤
      h * (bugC₁ L H * ε + bugC₂ L B H * h) := by
    intro n hn
    rw [hY n hn]
    exact (hstep n hn).local_error_le hF hL hB (by ring) hh hhH (hΦ n hn) (hΦ₀ n hn)
  have h1 := lady_windermere_of_le hF hL hh hA hΦ hΦ₀ hg hloc n hn hT
  have h2 : Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * (bugC₁ L H * ε + bugC₂ L B H * h))
      ≤ Real.exp (L * T) * (δ + T * (bugC₁ L H * ε + bugC₂ L B H * h)) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  calc _ ≤ _ := h1.trans h2
    _ = _ := by ring

end Global

/-! ### Satisfiability of the hypotheses -/

/-- Auxiliary for the examples: `t ↦ t` solves `y' = F(t, y)` whenever `F ≡ 1`. -/
lemma odeSolution_id_of_eq_one {F : ℝ → ℝ → ℝ} (hF : ∀ t x, F t x = 1) (a b : ℝ) :
    ODESolution F (fun t => t) a b :=
  ⟨continuousOn_id, fun t _ => by rw [hF]; exact hasDerivWithinAt_id t _⟩

/-- The hypotheses of one BUG step are jointly satisfiable with a nonzero vector field: on `ℝ`,
`F(t, y) = 1`, all projectors the identity, all trajectories `t ↦ t` on `[0, 1]`, `ε = 0`. -/
example : IsBUGStep (E := ℝ) (fun _ _ => 1) 0 1 1 1 1 0 1 0 (fun t => t) (fun t => t)
    (fun t => t) where
  projP₀ := IsOrthProj.one
  projQ₀ := IsOrthProj.one
  projP₁ := IsOrthProj.one
  projQ₁ := IsOrthProj.one
  comm₁ _ := rfl
  kSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
  kStart := rfl
  kCap := rfl
  kNormal _ _ := by simp
  lSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
  lStart := rfl
  lCap := rfl
  lNormal _ _ := by simp
  sSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
  sStart := rfl

/-- The hypotheses of `bug_global_error` are jointly satisfiable: on `ℝ` with `F(t, y) = 1`
(`L = 0`, `B = 1`), step size `h = 1`, five steps, exact solution `A t = t`, numerical values
`Y n = n`, all projectors the identity, and all substep trajectories and exact flows `t ↦ t`.
The conclusion is the (here exact) bound `‖Y n - A n‖ ≤ ...`. -/
example : ∀ n ≤ 5, ‖((n : ℕ) : ℝ) - (0 + n * 1)‖ ≤ Real.exp (0 * (n * 1)) *
    (‖((0 : ℕ) : ℝ) - 0‖ + n * 1 * (bugC₁ 0 1 * 0 + bugC₂ 0 1 1 * 1)) :=
  bug_global_error (E := ℝ) (F := fun _ _ => 1) (L := 0) (B := 1) (ε := 0)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => by simp) (t₀ := 0) (h := 1) (H := 1) zero_le_one
    le_rfl (N := 5) (A := fun t => t)
    (odeSolution_id_of_eq_one (fun _ _ => rfl) _ _) (P := fun _ => 1) (Q := fun _ => 1)
    (Y := fun n => (n : ℝ))
    (YK := fun _ t => t) (YL := fun _ t => t) (YS := fun _ t => t) (Φ := fun _ t => t)
    (fun n _ => {
      projP₀ := IsOrthProj.one
      projQ₀ := IsOrthProj.one
      projP₁ := IsOrthProj.one
      projQ₁ := IsOrthProj.one
      comm₁ := fun _ => rfl
      kSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
      kStart := by simp
      kCap := rfl
      kNormal := fun _ _ => by simp
      lSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
      lStart := by simp
      lCap := rfl
      lNormal := fun _ _ => by simp
      sSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
      sStart := by simp })
    (fun n _ => by simp)
    (fun _ _ => odeSolution_id_of_eq_one (fun _ _ => by simp) _ _)
    (fun n _ => by simp)

end LeanDLRA
