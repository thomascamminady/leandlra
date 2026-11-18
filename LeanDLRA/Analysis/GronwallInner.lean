import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Grönwall's inequality from a bound on the inner product with the derivative

`LeanDLRA.norm_le_exp_integral_mul_add_integral_exp_integral_mul` compares `‖f‖` with the solution
of `u' = k(t) u + g(t)` under the bound `‖f'‖ ≤ k ‖f‖ + g` on the norm of the derivative. In an
inner product space only the component of `f'` along `f` changes `‖f‖`: this file has the same
conclusion,

  `‖f x‖ ≤ e^{∫ₐˣ k} δ + ∫ₐˣ e^{∫ₛˣ k} g(s) ds`,

under the one-sided bound `⟪f, f'⟫ ≤ (k ‖f‖ + g) ‖f‖` with `g ≥ 0` on `[a, b)`. No sign condition
on `k`, and no bound on the part of `f'` orthogonal to `f`.

## Main results

* `LeanDLRA.norm_le_exp_integral_mul_add_integral_exp_integral_mul_of_inner_le`: the inequality.

## Implementation notes

The function `‖f‖²` has the right derivative `2 ⟪f, f'⟫`, also where `f` vanishes. It is compared
with the square of `B_ε(x) = e^{K(x)} (δ + ε + ∫ₐˣ e^{-K(s)} g(s) ds + ε (x - a))`, `K(x) = ∫ₐˣ k`,
which is positive on `[a, b]` because `g ≥ 0` there, and satisfies
`B_ε' = k B_ε + g + ε e^{K} > k B_ε + g`. The sign condition on `g` cannot be dropped: `f = 0`
satisfies the hypothesis for every `g`.
-/

open Set Filter
open scoped Topology RealInnerProductSpace

namespace LeanDLRA

/-- The comparison step: `K` and `G` are primitives of `k` and of `e^{-K} g`, with `K a = 0`,
`G a = 0` and `G ≥ 0` on `[a, b]`. -/
private theorem norm_le_exp_mul_add_of_inner_le_of_hasDerivAt {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f f' : ℝ → E} {δ a b : ℝ}
    {k g K G : ℝ → ℝ} (hK : ∀ x, HasDerivAt K (k x) x)
    (hG : ∀ x, HasDerivAt G (Real.exp (-K x) * g x) x) (hKa : K a = 0) (hGa : G a = 0)
    (hG0 : ∀ x ∈ Icc a b, 0 ≤ G x) (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) (ha : ‖f a‖ ≤ δ)
    (bound : ∀ x ∈ Ico a b, ⟪f x, f' x⟫ ≤ (k x * ‖f x‖ + g x) * ‖f x‖) {x : ℝ}
    (hx : x ∈ Icc a b) {ε : ℝ} (hε : 0 < ε) :
    ‖f x‖ ≤ Real.exp (K x) * (δ + ε + G x + ε * (x - a)) := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans ha
  have hBpos : ∀ t ∈ Icc a b, 0 < Real.exp (K t) * (δ + ε + G t + ε * (t - a)) := fun t ht =>
    mul_pos (Real.exp_pos _)
      (by nlinarith [hG0 t ht, mul_nonneg hε.le (sub_nonneg.2 ht.1)])
  have hB : ∀ t, HasDerivAt (fun t => Real.exp (K t) * (δ + ε + G t + ε * (t - a)))
      (k t * (Real.exp (K t) * (δ + ε + G t + ε * (t - a))) + g t + ε * Real.exp (K t)) t := by
    intro t
    have h2 : HasDerivAt (fun t => δ + ε + G t + ε * (t - a))
        (Real.exp (-K t) * g t + ε * 1) t :=
      ((hG t).const_add (δ + ε)).add (((hasDerivAt_id t).sub_const a).const_mul ε)
    have he : Real.exp (K t) * Real.exp (-K t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h3 : HasDerivAt (fun t => Real.exp (K t) * (δ + ε + G t + ε * (t - a)))
        (Real.exp (K t) * k t * (δ + ε + G t + ε * (t - a)) +
          Real.exp (K t) * (Real.exp (-K t) * g t + ε * 1)) t := (hK t).exp.mul h2
    refine h3.congr_deriv ?_
    linear_combination (g t) * he
  have hB2 : ∀ t, HasDerivAt (fun t => (Real.exp (K t) * (δ + ε + G t + ε * (t - a))) ^ 2)
      (2 * (Real.exp (K t) * (δ + ε + G t + ε * (t - a))) *
        (k t * (Real.exp (K t) * (δ + ε + G t + ε * (t - a))) + g t + ε * Real.exp (K t))) t :=
    fun t => by
      have h := (hB t).pow 2
      refine h.congr_deriv ?_
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  have hBa : ‖f a‖ ^ 2 ≤ (Real.exp (K a) * (δ + ε + G a + ε * (a - a))) ^ 2 := by
    rw [hKa, hGa, Real.exp_zero, sub_self, mul_zero, add_zero, add_zero, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
  have hsq := image_le_of_deriv_right_lt_deriv_boundary (f := fun t => ‖f t‖ ^ 2)
    (f' := fun t => 2 * ⟪f t, f' t⟫)
    ((continuous_norm.comp_continuousOn hf).pow 2)
    (fun t ht => (hf' t ht).norm_sq)
    (B := fun t => (Real.exp (K t) * (δ + ε + G t + ε * (t - a))) ^ 2) hBa hB2
    (fun t ht (heq : ‖f t‖ ^ 2 = (Real.exp (K t) * (δ + ε + G t + ε * (t - a))) ^ 2) => by
      have hpos := hBpos t (Ico_subset_Icc_self ht)
      have hfB : ‖f t‖ = Real.exp (K t) * (δ + ε + G t + ε * (t - a)) :=
        (pow_left_inj₀ (norm_nonneg _) hpos.le two_ne_zero).1 heq
      have hb := bound t ht
      rw [hfB] at hb
      have hε' := mul_pos (mul_pos hε (Real.exp_pos (K t))) hpos
      nlinarith) hx
  exact (abs_le_of_sq_le_sq' hsq (hBpos x hx).le).2

/-- **Grönwall's inequality from the inner product with the derivative, time-dependent rate.** Let
`f` be continuous on `[a, b]` with right derivatives `f'` on `[a, b)` in a real inner product
space. If `⟪f x, f' x⟫ ≤ (k x ‖f x‖ + g x) ‖f x‖` for continuous `k` and `g` with `g ≥ 0` on
`[a, b)`, and `‖f a‖ ≤ δ`, then `‖f x‖ ≤ e^{∫ₐˣ k} δ + ∫ₐˣ e^{∫ₛˣ k} g(s) ds` on `[a, b]`. -/
theorem norm_le_exp_integral_mul_add_integral_exp_integral_mul_of_inner_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f f' : ℝ → E} {δ a b : ℝ} {k g : ℝ → ℝ}
    (hk : Continuous k) (hg : Continuous g) (hg0 : ∀ x ∈ Ico a b, 0 ≤ g x)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) (ha : ‖f a‖ ≤ δ)
    (bound : ∀ x ∈ Ico a b, ⟪f x, f' x⟫ ≤ (k x * ‖f x‖ + g x) * ‖f x‖) :
    ∀ x ∈ Icc a b, ‖f x‖ ≤ Real.exp (∫ u in a..x, k u) * δ +
      ∫ s in a..x, Real.exp (∫ u in s..x, k u) * g s := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hax | hax
  · subst hax
    simpa using ha
  have hab : a < b := hax.trans_le hx.2
  replace hg0 : ∀ x ∈ Icc a b, 0 ≤ g x := by
    have h : closure (Ico a b) ⊆ {x | 0 ≤ g x} :=
      closure_minimal (fun x hx => hg0 x hx) (isClosed_le continuous_const hg)
    rwa [closure_Ico hab.ne] at h
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
  have hG0 : ∀ x ∈ Icc a b, 0 ≤ G x := fun x hx => by
    rw [hGdef]
    exact intervalIntegral.integral_nonneg hx.1 fun s hs =>
      mul_nonneg (Real.exp_pos _).le (hg0 s ⟨hs.1, hs.2.trans hx.2⟩)
  have hmain : ‖f x‖ ≤ Real.exp (K x) * (δ + G x) := by
    refine le_of_forall_pos_le_add fun η hη => ?_
    have hc0 : 0 ≤ Real.exp (K x) * (x - a) :=
      mul_nonneg (Real.exp_pos _).le (sub_nonneg.2 hx.1)
    have hpos : 0 < Real.exp (K x) * (1 + (x - a)) := by
      have := Real.exp_pos (K x)
      nlinarith
    have h := norm_le_exp_mul_add_of_inner_le_of_hasDerivAt hK hG hKa hGa hG0 hf hf' ha bound
      hx (div_pos hη hpos)
    have h2 : η / (Real.exp (K x) * (1 + (x - a))) * (Real.exp (K x) * (1 + (x - a))) = η :=
      div_mul_cancel₀ _ hpos.ne'
    have h3 : Real.exp (K x) * (δ + η / (Real.exp (K x) * (1 + (x - a))) + G x +
        η / (Real.exp (K x) * (1 + (x - a))) * (x - a)) = Real.exp (K x) * (δ + G x) +
        η / (Real.exp (K x) * (1 + (x - a))) * (Real.exp (K x) * (1 + (x - a))) := by
      ring
    rw [h3, h2] at h
    exact h
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

/-- **Non-vacuity of `norm_le_exp_integral_mul_add_integral_exp_integral_mul_of_inner_le`, with a
derivative that the bound on norms does not cover**: `f x = e^{-x}` has `⟪f, f'⟫ = -‖f‖² ≤ 0`, so
the hypothesis holds with `k = 0` and `g = 0`, while `‖f'‖ = ‖f‖` is not below `0 ‖f‖ + 0`. The
conclusion is `‖f x‖ ≤ 1`. -/
example : ∀ x ∈ Icc (0 : ℝ) 1, ‖Real.exp (-x)‖ ≤
    Real.exp (∫ _ in (0 : ℝ)..x, (0 : ℝ)) * 1 +
      ∫ s in (0 : ℝ)..x, Real.exp (∫ _ in s..x, (0 : ℝ)) * 0 :=
  norm_le_exp_integral_mul_add_integral_exp_integral_mul_of_inner_le
    (f := fun x : ℝ => Real.exp (-x)) (f' := fun x : ℝ => -Real.exp (-x)) (k := fun _ => 0)
    (g := fun _ => 0) continuous_const continuous_const (fun _ _ => le_rfl)
    (Real.continuous_exp.comp continuous_neg).continuousOn
    (fun x _ => by
      have h : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-x) * -1) x :=
        (hasDerivAt_neg x).exp
      exact (h.congr_deriv (by ring)).hasDerivWithinAt)
    (by simp)
    (fun x _ => by
      rw [inner_neg_right, real_inner_self_eq_norm_sq]
      have := sq_nonneg ‖Real.exp (-x)‖
      linarith)

end LeanDLRA
