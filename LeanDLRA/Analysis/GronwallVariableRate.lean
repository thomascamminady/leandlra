import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Grönwall's inequality with a time-dependent rate

Mathlib's `gronwallBound` and `LeanDLRA.gronwallIntegralBound` solve the scalar comparison equation
`u' = K u + η` with a constant rate `K`. This file has the comparison with the solution of
`u' = k(t) u + g(t)`, `u(a) = δ`, for continuous `k` and `g`:

  `‖f x‖ ≤ e^{∫ₐˣ k} δ + ∫ₐˣ e^{∫ₛˣ k} g(s) ds`

if `f` has right derivatives with `‖f'‖ ≤ k ‖f‖ + g`. No sign condition on `k`, `g` or `δ`.

## Main results

* `LeanDLRA.norm_le_exp_integral_mul_add_integral_exp_integral_mul`: the inequality.

## Implementation notes

The comparison function is `B_ε(x) = e^{K(x)} (δ + ∫ₐˣ e^{-K(s)} g(s) ds + ε (x - a))` with
`K(x) = ∫ₐˣ k`; it satisfies `B_ε' = k B_ε + g + ε e^{K} > k B_ε + g`, so
`image_le_of_liminf_slope_right_lt_deriv_boundary` applies, and `ε → 0`. The continuity of `k` and
`g` is used for the derivatives of the two primitives.
-/

open Set Filter
open scoped Topology

namespace LeanDLRA

/-- The comparison step: `K` and `G` are primitives of `k` and of `e^{-K} g` that vanish at
`a`. -/
private theorem norm_le_exp_mul_add_of_hasDerivAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f f' : ℝ → E} {δ a b : ℝ} {k g K G : ℝ → ℝ}
    (hK : ∀ x, HasDerivAt K (k x) x) (hG : ∀ x, HasDerivAt G (Real.exp (-K x) * g x) x)
    (hKa : K a = 0) (hGa : G a = 0) (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) (ha : ‖f a‖ ≤ δ)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ k x * ‖f x‖ + g x) {x : ℝ} (hx : x ∈ Icc a b) {ε : ℝ}
    (hε : 0 < ε) : ‖f x‖ ≤ Real.exp (K x) * (δ + G x + ε * (x - a)) := by
  have hB : ∀ t, HasDerivAt (fun t => Real.exp (K t) * (δ + G t + ε * (t - a)))
      (k t * (Real.exp (K t) * (δ + G t + ε * (t - a))) + g t + ε * Real.exp (K t)) t := by
    intro t
    have h2 : HasDerivAt (fun t => δ + G t + ε * (t - a)) (Real.exp (-K t) * g t + ε * 1) t :=
      ((hG t).const_add δ).add (((hasDerivAt_id t).sub_const a).const_mul ε)
    have he : Real.exp (K t) * Real.exp (-K t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h3 : HasDerivAt (fun t => Real.exp (K t) * (δ + G t + ε * (t - a)))
        (Real.exp (K t) * k t * (δ + G t + ε * (t - a)) +
          Real.exp (K t) * (Real.exp (-K t) * g t + ε * 1)) t := (hK t).exp.mul h2
    refine h3.congr_deriv ?_
    linear_combination (g t) * he
  have hBa : ‖f a‖ ≤ Real.exp (K a) * (δ + G a + ε * (a - a)) := by
    rw [hKa, hGa, Real.exp_zero, sub_self, mul_zero, add_zero, add_zero, one_mul]
    exact ha
  exact image_le_of_liminf_slope_right_lt_deriv_boundary (f := fun t => ‖f t‖)
    (f' := fun t => k t * ‖f t‖ + g t) (continuous_norm.comp_continuousOn hf)
    (fun t ht r hr => (hf' t ht).liminf_right_slope_norm_le ((bound t ht).trans_lt hr))
    (B := fun t => Real.exp (K t) * (δ + G t + ε * (t - a))) hBa hB
    (fun t _ (heq : ‖f t‖ = Real.exp (K t) * (δ + G t + ε * (t - a))) => by
      rw [heq]
      linarith [mul_pos hε (Real.exp_pos (K t))]) hx

/-- **Grönwall's inequality with a time-dependent rate.** If `f` is continuous on `[a, b]` with
right derivatives `f'` on `[a, b)`, `‖f' x‖ ≤ k x ‖f x‖ + g x` for continuous `k` and `g`, and
`‖f a‖ ≤ δ`, then `‖f x‖ ≤ e^{∫ₐˣ k} δ + ∫ₐˣ e^{∫ₛˣ k} g(s) ds` on `[a, b]`. -/
theorem norm_le_exp_integral_mul_add_integral_exp_integral_mul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f f' : ℝ → E} {δ a b : ℝ} {k g : ℝ → ℝ}
    (hk : Continuous k) (hg : Continuous g) (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) (ha : ‖f a‖ ≤ δ)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ k x * ‖f x‖ + g x) :
    ∀ x ∈ Icc a b, ‖f x‖ ≤ Real.exp (∫ u in a..x, k u) * δ +
      ∫ s in a..x, Real.exp (∫ u in s..x, k u) * g s := by
  obtain ⟨K, hK, hKdef⟩ : ∃ K : ℝ → ℝ, (∀ x, HasDerivAt K (k x) x) ∧
      ∀ x, K x = ∫ u in a..x, k u :=
    ⟨fun x => ∫ u in a..x, k u, fun x => (hk.integral_hasStrictDerivAt a x).hasDerivAt,
      fun _ => rfl⟩
  have hKc : Continuous K := continuous_iff_continuousAt.2 fun x => (hK x).continuousAt
  have hc : Continuous fun s => Real.exp (-K s) * g s :=
    (Real.continuous_exp.comp hKc.neg).mul hg
  obtain ⟨G, hG, hGdef⟩ : ∃ G : ℝ → ℝ, (∀ x, HasDerivAt G (Real.exp (-K x) * g x) x) ∧
      ∀ x, G x = ∫ s in a..x, Real.exp (-K s) * g s :=
    ⟨fun x => ∫ s in a..x, Real.exp (-K s) * g s,
      fun x => (hc.integral_hasStrictDerivAt a x).hasDerivAt, fun _ => rfl⟩
  have hKa : K a = 0 := by rw [hKdef, intervalIntegral.integral_same]
  have hGa : G a = 0 := by rw [hGdef, intervalIntegral.integral_same]
  intro x hx
  have hmain : ‖f x‖ ≤ Real.exp (K x) * (δ + G x) := by
    refine le_of_forall_pos_le_add fun η hη => ?_
    have hc0 : 0 ≤ Real.exp (K x) * (x - a) :=
      mul_nonneg (Real.exp_pos _).le (sub_nonneg.2 hx.1)
    have hpos : 0 < Real.exp (K x) * (x - a) + 1 := by linarith
    have h := norm_le_exp_mul_add_of_hasDerivAt hK hG hKa hGa hf hf' ha bound hx
      (div_pos hη hpos)
    have h2 : η / (Real.exp (K x) * (x - a) + 1) * (Real.exp (K x) * (x - a)) ≤ η := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith
    linarith
  have hs : ∀ s, Real.exp (K x) * (Real.exp (-K s) * g s) =
      Real.exp (∫ u in s..x, k u) * g s := fun s => by
    rw [← mul_assoc, ← Real.exp_add, ← sub_eq_add_neg, hKdef x, hKdef s,
      intervalIntegral.integral_interval_sub_left (hk.intervalIntegrable _ _)
        (hk.intervalIntegrable _ _)]
  have hI : Real.exp (K x) * G x = ∫ s in a..x, Real.exp (∫ u in s..x, k u) * g s := by
    rw [hGdef, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun s _ => hs s
  rw [← hI, ← hKdef x, ← mul_add]
  exact hmain

/-- **Non-vacuity of `norm_le_exp_integral_mul_add_integral_exp_integral_mul`**: `f x = x` on
`[0, 1]` with the rate `k x = x`, the source `g = 1` and `δ = 0`; then `‖f'‖ = 1 ≤ x · x + 1`. -/
example : ∀ x ∈ Icc (0 : ℝ) 1, ‖x‖ ≤ Real.exp (∫ u in (0 : ℝ)..x, u) * 0 +
    ∫ s in (0 : ℝ)..x, Real.exp (∫ u in s..x, u) * 1 :=
  norm_le_exp_integral_mul_add_integral_exp_integral_mul (f := fun x : ℝ => x)
    (f' := fun _ => (1 : ℝ)) (k := fun x => x) (g := fun _ => 1) continuous_id continuous_const
    continuous_id.continuousOn (fun x _ => (hasDerivAt_id x).hasDerivWithinAt) (by simp)
    (fun x hx => by
      have := mul_nonneg hx.1 (norm_nonneg x)
      simp only [norm_one]
      linarith)

end LeanDLRA
