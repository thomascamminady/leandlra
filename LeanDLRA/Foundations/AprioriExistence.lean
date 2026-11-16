import LeanDLRA.Foundations.Existence

/-!
# Existence of solutions from an a priori bound

`LeanDLRA/Foundations/Existence.lean` gives solutions of `y' = f(t, y)` on a whole interval for
fields that are Lipschitz and bounded on the whole space. Many fields are Lipschitz and bounded
only on a region, for example the factor equations of dynamical low-rank approximation, which
contain the inverse of the core matrix. This file treats such fields without a continuation
argument: the field is multiplied by a Lipschitz cutoff `χ` with values in `[0, 1]` that vanishes
outside the region. The damped field `χ(y) f(t, y)` is Lipschitz and bounded on the whole space,
so it has a solution on the whole interval, and an a priori bound that keeps the solutions of
damped equations in the part of the region where `χ = 1` shows that this solution solves the
original equation.

## Main results

* `LeanDLRA.isLipschitzField_cutoff_smul`, `LeanDLRA.isBoundedField_cutoff_smul`: the damped field
  `χ(x) f(t, x)` is Lipschitz with constant `L + Lχ M` and bounded by `M` on the whole space if
  `f` is `L`-Lipschitz and bounded by `M` on a set `K` and `χ` is `Lχ`-Lipschitz with values in
  `[0, 1]` and zero outside `K`.
* `LeanDLRA.exists_ODESolution_of_apriori_sublevel`: let `g` be a Lipschitz function of the
  state and `δ₁ < δ₂`. If `f` is Lipschitz and bounded on `{g ≤ δ₂}` and every solution of
  every damped equation `y' = c(y) f(t, y)` (`0 ≤ c ≤ 1`, `c = 0` on `{g > δ₂}`) with initial
  value `y₀` satisfies `g(y(t)) ≤ δ₁` on `[a, b]`, then `y' = f(t, y)`, `y(a) = y₀` has a
  solution on `[a, b]`, and it satisfies `g(y(t)) ≤ δ₁`.
* `LeanDLRA.exists_ODESolution_of_closedBall`: a field that is Lipschitz and bounded by `M` on the
  closed ball of radius `δ` around `y₀` has a solution with `y(a) = y₀` on `[a, b]` if
  `M (b - a) < δ` (local Picard–Lindelöf theorem), and `‖y(t) - y₀‖ ≤ M (t - a)`.

## Implementation notes

The region conditions are `IsLipschitzFieldOn` and `IsBoundedFieldOn` on `univ ×ˢ K`. The a priori
bound is asked for all damped equations and not only for the one with the cutoff of the proof, so
that the statement does not mention a particular cutoff; in applications the bound comes from an
estimate of the velocity that holds for every factor `c` with values in `[0, 1]`.
-/

open Set Metric

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Damped fields -/

section Cutoff

variable {f : ℝ → E → E} {K : Set E} {χ : E → ℝ} {L Lχ M : ℝ}

/-- **A damped field is Lipschitz on the whole space.** Let `f` be `L`-Lipschitz and bounded by
`M` on the set `K` (at every time), and let `χ` be `Lχ`-Lipschitz with values in `[0, 1]` and zero
outside `K`. Then `χ(x) f(t, x)` is Lipschitz in `x` on the whole space with constant
`L + Lχ M`. -/
theorem isLipschitzField_cutoff_smul (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (hχL : ∀ x y, |χ x - χ y| ≤ Lχ * ‖x - y‖) (hχK : ∀ x, x ∉ K → χ x = 0)
    (hL : IsLipschitzFieldOn f (univ ×ˢ K) L) (hL0 : 0 ≤ L)
    (hM : IsBoundedFieldOn f (univ ×ˢ K) M) (hM0 : 0 ≤ M) :
    IsLipschitzField (fun t x => χ x • f t x) (L + Lχ * M) := by
  intro t x y
  have hχxy := hχL x y
  have hLχ : 0 ≤ Lχ * ‖x - y‖ := (abs_nonneg _).trans hχxy
  have hLxy : 0 ≤ L * ‖x - y‖ := mul_nonneg hL0 (norm_nonneg _)
  have hmem : ∀ {z}, z ∈ K → (t, z) ∈ (univ : Set ℝ) ×ˢ K := fun hz => ⟨mem_univ t, hz⟩
  change ‖χ x • f t x - χ y • f t y‖ ≤ (L + Lχ * M) * ‖x - y‖
  by_cases hx : x ∈ K
  · by_cases hy : y ∈ K
    · have h1 := hL (hmem hx) (hmem hy)
      have h2 := hM (hmem hy)
      calc ‖χ x • f t x - χ y • f t y‖
          = ‖χ x • (f t x - f t y) + (χ x - χ y) • f t y‖ := by
            congr 1
            rw [smul_sub, sub_smul]
            abel
        _ ≤ χ x * ‖f t x - f t y‖ + |χ x - χ y| * ‖f t y‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hχ0 x)]
        _ ≤ 1 * (L * ‖x - y‖) + Lχ * ‖x - y‖ * M :=
            add_le_add (mul_le_mul (hχ1 x) h1 (norm_nonneg _) zero_le_one)
              (mul_le_mul hχxy h2 (norm_nonneg _) hLχ)
        _ = (L + Lχ * M) * ‖x - y‖ := by ring
    · have h2 := hM (hmem hx)
      calc ‖χ x • f t x - χ y • f t y‖ = |χ x - χ y| * ‖f t x‖ := by
            rw [hχK y hy, zero_smul, sub_zero, sub_zero, norm_smul, Real.norm_eq_abs]
        _ ≤ Lχ * ‖x - y‖ * M := mul_le_mul hχxy h2 (norm_nonneg _) hLχ
        _ ≤ (L + Lχ * M) * ‖x - y‖ := by nlinarith
  · by_cases hy : y ∈ K
    · have h2 := hM (hmem hy)
      calc ‖χ x • f t x - χ y • f t y‖ = |χ x - χ y| * ‖f t y‖ := by
            rw [hχK x hx, zero_smul, zero_sub, zero_sub, norm_neg, abs_neg, norm_smul,
              Real.norm_eq_abs]
        _ ≤ Lχ * ‖x - y‖ * M := mul_le_mul hχxy h2 (norm_nonneg _) hLχ
        _ ≤ (L + Lχ * M) * ‖x - y‖ := by nlinarith
    · rw [hχK x hx, hχK y hy, zero_smul, zero_smul, sub_zero, norm_zero]
      nlinarith [mul_nonneg hLχ hM0]

/-- **A damped field is bounded on the whole space**: if `f` is bounded by `M ≥ 0` on `K` and `χ`
has values in `[0, 1]` and is zero outside `K`, then `χ(x) f(t, x)` is bounded by `M`. -/
theorem isBoundedField_cutoff_smul (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (hχK : ∀ x, x ∉ K → χ x = 0) (hM : IsBoundedFieldOn f (univ ×ˢ K) M) (hM0 : 0 ≤ M) :
    IsBoundedField (fun t x => χ x • f t x) M := by
  intro t x
  change ‖χ x • f t x‖ ≤ M
  by_cases hx : x ∈ K
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ0 x)]
    have h := hM (t := t) (x := x) ⟨mem_univ t, hx⟩
    calc χ x * ‖f t x‖ ≤ 1 * M := mul_le_mul (hχ1 x) h (norm_nonneg _) zero_le_one
      _ = M := one_mul M
  · rw [hχK x hx, zero_smul, norm_zero]
    exact hM0

end Cutoff

/-! ### Existence from an a priori bound -/

section Apriori

variable [CompleteSpace E] {f : ℝ → E → E}

/-- **Existence from an a priori bound.** Let `g` be a Lipschitz function of the state and
`δ₁ < δ₂`. Let `f` be Lipschitz and bounded on the region `{g ≤ δ₂}` and continuous in time
there. Assume the a priori bound: every solution `y` with `y(a) = y₀` of a damped equation
`y' = c(y) f(t, y)`, where `c` has values in `[0, 1]` and vanishes on `{g > δ₂}`, satisfies
`g(y(t)) ≤ δ₁` on `[a, b]`. Then the equation `y' = f(t, y)`, `y(a) = y₀` has a solution on
`[a, b]`, and `g(y(t)) ≤ δ₁` along it. No continuation argument is needed: the equation damped by
a Lipschitz cutoff has a solution on the whole interval, and by the a priori bound the cutoff
equals one along it.

`exists_ODESolution_of_apriori` (`LeanDLRA/Foundations/Localization.lean`) is the statement of
this kind for the tube `‖x - A t‖ ≤ ρ` around a curve, with the field extended by the retraction
onto the ball. Here the region is a sublevel set of an arbitrary Lipschitz function, which need
not be a ball (for the factor equations of dynamical low-rank approximation it bounds the three
factors by different amounts), the field is damped instead of extended, and continuity in time
is asked for each state separately. -/
theorem exists_ODESolution_of_apriori_sublevel {g : E → ℝ} {Lg δ₁ δ₂ L M a b : ℝ} {y₀ : E}
    (hg : ∀ x y, |g x - g y| ≤ Lg * ‖x - y‖) (hδ : δ₁ < δ₂)
    (hL : IsLipschitzFieldOn f (univ ×ˢ {x | g x ≤ δ₂}) L)
    (hM : IsBoundedFieldOn f (univ ×ˢ {x | g x ≤ δ₂}) M)
    (hc : ∀ x, g x ≤ δ₂ → Continuous fun t => f t x) (hab : a ≤ b)
    (hpri : ∀ (c : E → ℝ) (y : ℝ → E), (∀ x, 0 ≤ c x) → (∀ x, c x ≤ 1) →
      (∀ x, δ₂ < g x → c x = 0) → y a = y₀ → ODESolution (fun t x => c x • f t x) y a b →
      ∀ t ∈ Icc a b, g (y t) ≤ δ₁) :
    ∃ y : ℝ → E, ODESolution f y a b ∧ y a = y₀ ∧ ∀ t ∈ Icc a b, g (y t) ≤ δ₁ := by
  have hd : 0 < δ₂ - δ₁ := sub_pos.2 hδ
  set χ : E → ℝ := fun x => max 0 (min 1 ((δ₂ - g x) / (δ₂ - δ₁))) with hχ
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => le_max_left _ _
  have hχ1 : ∀ x, χ x ≤ 1 := fun x => max_le zero_le_one (min_le_left _ _)
  have hχout : ∀ x, δ₂ < g x → χ x = 0 := fun x hx =>
    max_eq_left ((min_le_right 1 ((δ₂ - g x) / (δ₂ - δ₁))).trans
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hx.le) hd.le))
  have hχK : ∀ x, x ∉ {x | g x ≤ δ₂} → χ x = 0 := fun x hx => hχout x (not_le.1 hx)
  have hχin : ∀ x, g x ≤ δ₁ → χ x = 1 := fun x hx => by
    have h1 : 1 ≤ (δ₂ - g x) / (δ₂ - δ₁) := by
      rw [le_div_iff₀ hd]
      linarith
    simp only [hχ, min_eq_left h1]
    exact max_eq_right zero_le_one
  have hχL : ∀ x y, |χ x - χ y| ≤ Lg / (δ₂ - δ₁) * ‖x - y‖ := fun x y => by
    have h1 : |χ x - χ y| ≤ |(δ₂ - g x) / (δ₂ - δ₁) - (δ₂ - g y) / (δ₂ - δ₁)| := by
      refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp) ?_)
      exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) le_rfl)
    have h2 : (δ₂ - g x) / (δ₂ - δ₁) - (δ₂ - g y) / (δ₂ - δ₁) = (g y - g x) / (δ₂ - δ₁) := by
      ring
    rw [h2, abs_div, abs_of_pos hd, abs_sub_comm (g y) (g x)] at h1
    calc |χ x - χ y| ≤ |g x - g y| / (δ₂ - δ₁) := h1
      _ ≤ Lg * ‖x - y‖ / (δ₂ - δ₁) := div_le_div_of_nonneg_right (hg x y) hd.le
      _ = Lg / (δ₂ - δ₁) * ‖x - y‖ := by ring
  have hL' : IsLipschitzFieldOn f (univ ×ˢ {x | g x ≤ δ₂}) (max L 0) := fun _ _ _ hx hy =>
    (hL hx hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hM' : IsBoundedFieldOn f (univ ×ˢ {x | g x ≤ δ₂}) (max M 0) := fun _ _ hx =>
    (hM hx).trans (le_max_left _ _)
  have hLip := isLipschitzField_cutoff_smul hχ0 hχ1 hχL hχK hL' (le_max_right _ _) hM'
    (le_max_right _ _)
  have hBdd := isBoundedField_cutoff_smul hχ0 hχ1 hχK hM' (le_max_right _ _)
  have hcont : ∀ x, Continuous fun t => χ x • f t x := fun x => by
    by_cases hx : g x ≤ δ₂
    · exact (hc x hx).const_smul _
    · simp only [hχK x hx, zero_smul]
      exact continuous_const
  obtain ⟨y, hy, hya⟩ := exists_ODESolution hLip hBdd hcont hab y₀
  have hgy := hpri χ y hχ0 hχ1 hχout hya hy
  refine ⟨y, ⟨hy.cont, fun t ht => ?_⟩, hya, hgy⟩
  have h := hy.deriv t ht
  simp only [hχin (y t) (hgy t (Ico_subset_Icc_self ht)), one_smul] at h
  exact h

/-- **Local existence on a ball** (Picard–Lindelöf) for a field that is Lipschitz and bounded on
a ball only. If `f` is `L`-Lipschitz and bounded by `M` on the closed ball of radius `δ` around
`y₀` and continuous in time there, and `M (b - a) < δ`, then `y' = f(t, y)`, `y(a) = y₀` has a
solution on `[a, b]`, and `‖y(t) - y₀‖ ≤ M (t - a)`. -/
theorem exists_ODESolution_of_closedBall {y₀ : E} {δ L M a b : ℝ}
    (hL : IsLipschitzFieldOn f (univ ×ˢ closedBall y₀ δ) L)
    (hM : IsBoundedFieldOn f (univ ×ˢ closedBall y₀ δ) M) (hM0 : 0 ≤ M)
    (hc : ∀ x ∈ closedBall y₀ δ, Continuous fun t => f t x) (hab : a ≤ b)
    (hδ : M * (b - a) < δ) :
    ∃ y : ℝ → E, ODESolution f y a b ∧ y a = y₀ ∧ ∀ t ∈ Icc a b, ‖y t - y₀‖ ≤ M * (t - a) := by
  have hball : ∀ x, ‖x - y₀‖ ≤ δ → x ∈ closedBall y₀ δ := fun _ hx =>
    mem_closedBall_iff_norm.2 hx
  obtain ⟨y, hy, hya, hyb⟩ := exists_ODESolution_of_apriori_sublevel (f := f)
    (g := fun x => ‖x - y₀‖)
    (Lg := 1) (δ₁ := M * (b - a)) (δ₂ := δ) (L := L) (M := M) (a := a) (b := b) (y₀ := y₀)
    (fun x y => by
      rw [one_mul]
      have h := abs_norm_sub_norm_le (x - y₀) (y - y₀)
      rwa [sub_sub_sub_cancel_right] at h)
    hδ (fun t x y hx hy => hL ⟨mem_univ t, hball x hx.2⟩ ⟨mem_univ t, hball y hy.2⟩)
    (fun t x hx => hM ⟨mem_univ t, hball x hx.2⟩) (fun x hx => hc x (hball x hx)) hab
    (fun c y hc0 hc1 hcout hya hy t ht => by
      have hbd : ∀ s ∈ Ico a b, ‖c (y s) • f s (y s)‖ ≤ M := fun s _ => by
        by_cases hs : ‖y s - y₀‖ ≤ δ
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hc0 _)]
          have h := hM (t := s) (x := y s) ⟨mem_univ s, hball _ hs⟩
          calc c (y s) * ‖f s (y s)‖ ≤ 1 * M := mul_le_mul (hc1 _) h (norm_nonneg _) zero_le_one
            _ = M := one_mul M
        · rw [hcout _ (not_le.1 hs), zero_smul, norm_zero]
          exact hM0
      have h := hy.norm_sub_le hbd t ht
      rw [hya] at h
      exact h.trans (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hM0))
  refine ⟨y, hy, hya, fun t ht => ?_⟩
  have hbd : ∀ s ∈ Ico a b, ‖f s (y s)‖ ≤ M := fun s hs =>
    hM ⟨mem_univ s, hball _ ((hyb s (Ico_subset_Icc_self hs)).trans hδ.le)⟩
  have h := hy.norm_sub_le hbd t ht
  rwa [hya] at h

end Apriori

/-- **Non-vacuity.** The field `f(t, y) = y²` on `ℝ` is neither bounded nor Lipschitz on the
whole line, but on the ball `|y - 1| ≤ 1` it is `4`-Lipschitz and bounded by `4`, so the initial
value problem `y' = y²`, `y(0) = 1` has a solution on `[0, 1/5]`. -/
example : ∃ y : ℝ → ℝ, ODESolution (fun _ x => x ^ 2) y 0 (1 / 5) ∧ y 0 = 1 ∧
    ∀ t ∈ Icc (0 : ℝ) (1 / 5), ‖y t - 1‖ ≤ 4 * (t - 0) := by
  have hmem : ∀ {x : ℝ}, x ∈ closedBall (1 : ℝ) 1 → 0 ≤ x ∧ x ≤ 2 := by
    intro x hx
    rw [mem_closedBall_iff_norm, Real.norm_eq_abs, abs_le] at hx
    constructor <;> linarith [hx.1, hx.2]
  refine exists_ODESolution_of_closedBall (L := 4) (M := 4) (δ := 1) ?_ ?_ (by norm_num)
    (fun _ _ => continuous_const) (by norm_num) (by norm_num)
  · intro t x y hx hy
    obtain ⟨hx0, hx2⟩ := hmem hx.2
    obtain ⟨hy0, hy2⟩ := hmem hy.2
    change ‖x ^ 2 - y ^ 2‖ ≤ 4 * ‖x - y‖
    have h : x ^ 2 - y ^ 2 = (x + y) * (x - y) := by ring
    rw [h, norm_mul, Real.norm_eq_abs (x + y), abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  · intro t x hx
    obtain ⟨hx0, hx2⟩ := hmem hx.2
    change ‖x ^ 2‖ ≤ 4
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith

end LeanDLRA
