import LeanDLRA.Foundations.Projector
import LeanDLRA.Analysis.Defs

/-!
# ODE toolkit for dynamical low-rank error analysis

All error analysis of dynamical low-rank integrators reduces to two analytic tools:

* the **mean value inequality**: a trajectory whose velocity is bounded by `B` moves at most
  `B * (t - a)` (used to show that all substeps stay `O(h)`-close to the starting value);
* the **Grönwall inequality** for perturbed ODEs with Lipschitz right-hand side
  (used for Galerkin substeps and for stability of the exact flow).

We fix the conventions used throughout the library:

* `ODESolution f y a b` : `y` solves `y' = f t y` on `[a, b]` in the sense used by Mathlib's
  Grönwall/uniqueness theorems (continuity on `Icc a b` and right derivatives on `Ico a b`);
* `IsLipschitzField f L` : `‖f t x - f t y‖ ≤ L * ‖x - y‖` for all `t, x, y`;
* `IsBoundedField f B` : `‖f t x‖ ≤ B` for all `t, x`.

These predicates are defined in `LeanDLRA/Analysis/Defs.lean`.
-/

open Set

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace IsLipschitzField

variable {f : ℝ → E → E} {L : ℝ}

omit [NormedSpace ℝ E] in
lemma nonneg_of_exists_ne (hf : IsLipschitzField f L) (h : ∃ x y : E, x ≠ y) : 0 ≤ L := by
  obtain ⟨x, y, hxy⟩ := h
  have h1 := hf 0 x y
  have h2 : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  nlinarith [norm_nonneg (f 0 x - f 0 y)]

omit [NormedSpace ℝ E] in
/-- Conversion to Mathlib's `LipschitzWith`. -/
lemma lipschitzWith (hf : IsLipschitzField f L) (hL : 0 ≤ L) (t : ℝ) :
    LipschitzWith ⟨L, hL⟩ (f t) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm]; exact hf t x y

/-- Composing a Lipschitz field with a contraction (e.g. an orthogonal projector) keeps it
Lipschitz with the same constant. -/
lemma comp_contraction (hf : IsLipschitzField f L) (P : E →L[ℝ] E) (hP : ∀ x, ‖P x‖ ≤ ‖x‖) :
    IsLipschitzField (fun t x => P (f t x)) L := fun t x y => by
  simpa [map_sub] using (hP (f t x - f t y)).trans (hf t x y)

end IsLipschitzField

lemma IsBoundedField.comp_contraction {f : ℝ → E → E} {B : ℝ} (hf : IsBoundedField f B)
    (P : E →L[ℝ] E) (hP : ∀ x, ‖P x‖ ≤ ‖x‖) : IsBoundedField (fun t x => P (f t x)) B :=
  fun t x => (hP _).trans (hf t x)

namespace ODESolution

variable {f : ℝ → E → E} {y : ℝ → E} {a b : ℝ}

/-- Restriction of a solution to a subinterval. -/
lemma mono (hy : ODESolution f y a b) {a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    ODESolution f y a' b' where
  cont := hy.cont.mono (Icc_subset_Icc ha hb)
  deriv t ht := hy.deriv t ⟨ha.trans ht.1, ht.2.trans_le hb⟩

/-- **Speed bound.** A solution whose velocity is bounded by `B` moves at most `B * (t - a)`. -/
lemma norm_sub_le (hy : ODESolution f y a b) {B : ℝ} (hB : ∀ t ∈ Ico a b, ‖f t (y t)‖ ≤ B) :
    ∀ t ∈ Icc a b, ‖y t - y a‖ ≤ B * (t - a) :=
  norm_image_sub_le_of_norm_deriv_right_le_segment hy.cont hy.deriv hB

/-- Speed bound for a bounded vector field. -/
lemma norm_sub_le_of_bounded (hy : ODESolution f y a b) {B : ℝ} (hB : IsBoundedField f B) :
    ∀ t ∈ Icc a b, ‖y t - y a‖ ≤ B * (t - a) :=
  hy.norm_sub_le fun t _ => hB t (y t)

/-- Uniqueness of solutions for Lipschitz vector fields. -/
lemma eqOn (hy : ODESolution f y a b) {z : ℝ → E} (hz : ODESolution f z a b) {L : ℝ}
    (hf : IsLipschitzField f L) (hL : 0 ≤ L) (h0 : y a = z a) : EqOn y z (Icc a b) :=
  ODE_solution_unique (hf.lipschitzWith hL) hy.cont hy.deriv hz.cont hz.deriv h0

end ODESolution

/-- **Grönwall comparison for perturbed ODEs.**  If `y' = u`, `z' = w` with
`‖u t - f t (y t)‖ ≤ ηy` and `‖w t - f t (z t)‖ ≤ ηz`, and `f` is `L`-Lipschitz, then
`‖y t - z t‖ ≤ gronwallBound δ L (ηy + ηz) (t - a)`. -/
lemma norm_sub_le_gronwallBound {f : ℝ → E → E} {L : ℝ} (hf : IsLipschitzField f L)
    (hL : 0 ≤ L) {y z u w : ℝ → E} {a b ηy ηz δ : ℝ}
    (hyc : ContinuousOn y (Icc a b)) (hy : ∀ t ∈ Ico a b, HasDerivWithinAt y (u t) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, ‖u t - f t (y t)‖ ≤ ηy)
    (hzc : ContinuousOn z (Icc a b)) (hz : ∀ t ∈ Ico a b, HasDerivWithinAt z (w t) (Ici t) t)
    (hzd : ∀ t ∈ Ico a b, ‖w t - f t (z t)‖ ≤ ηz) (h0 : ‖y a - z a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖y t - z t‖ ≤ gronwallBound δ L (ηy + ηz) (t - a) := by
  intro t ht
  have := dist_le_of_approx_trajectories_ODE (v := f) (K := ⟨L, hL⟩) (hf.lipschitzWith hL)
    hyc hy (fun t ht => by simpa [dist_eq_norm] using hyd t ht)
    hzc hz (fun t ht => by simpa [dist_eq_norm] using hzd t ht)
    (by simpa [dist_eq_norm] using h0) t ht
  rw [dist_eq_norm] at this
  exact this

/-- Explicit form of the Grönwall bound: `gronwallBound δ L η x ≤ exp (L x) * (δ + η x)`. -/
lemma gronwallBound_le_exp_mul {δ L η x : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η) :
    gronwallBound δ L η x ≤ Real.exp (L * x) * (δ + η * x) := by
  rcases hL.eq_or_lt with rfl | hL'
  · simp [gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 hL'.ne']
    simp only
    have hexp : Real.exp (L * x) - 1 ≤ L * x * Real.exp (L * x) := by
      have h := Real.add_one_le_exp (-(L * x))
      have hpos := Real.exp_pos (L * x)
      have hmul : Real.exp (-(L * x)) * Real.exp (L * x) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith
    have h1 : η / L * (Real.exp (L * x) - 1) ≤ η * x * Real.exp (L * x) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hL']
      nlinarith [mul_le_mul_of_nonneg_left hexp hη]
    nlinarith [Real.exp_pos (L * x)]

/-- `gronwallBound` is monotone in its first and third arguments when `L ≥ 0`, `x ≥ 0`. -/
lemma gronwallBound_mono {δ δ' L η η' x : ℝ} (hL : 0 ≤ L) (hx : 0 ≤ x) (hδ : δ ≤ δ')
    (hη : η ≤ η') : gronwallBound δ L η x ≤ gronwallBound δ' L η' x := by
  rcases hL.eq_or_lt with rfl | hL'
  · simp only [gronwallBound_K0]; nlinarith
  · simp only [gronwallBound_of_K_ne_0 hL'.ne']
    have h1 : 0 ≤ Real.exp (L * x) - 1 := by
      have := Real.add_one_le_exp (L * x); nlinarith [mul_nonneg hL hx]
    have h2 : η / L ≤ η' / L := div_le_div_of_nonneg_right hη hL'.le
    nlinarith [Real.exp_pos (L * x), mul_le_mul_of_nonneg_right h2 h1]

end LeanDLRA
