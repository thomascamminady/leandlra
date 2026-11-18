import LeanDLRA.Research.ImplicitBUGStiffRows

/-!
# Runs of the implicit BUG integrator on the stiff-rows family are uniform in the stiffness

For the family of `2 × 2` steps of `LeanDLRA.StiffRowsExample`,

  `M = diag(0, -1)`,  `N = diag(0, -lam)`,  `X(t) = (3/5, 4/5 e^{-t})ᵀ (1, 0)`,
  `Y₀ = (3/5, 4/5)ᵀ (c, s)`,  `c² + s² = 1`,

no one-step bound `‖Y₁ - X(h)‖ ≤ C₁ ‖Y₀ - X(0)‖ + C₂ h²` holds uniformly in `lam`
(`StiffRowsExample.not_exists_forall_norm_sub_le`). This file shows that whole runs are
nevertheless uniform in `lam`: after `n` steps of size `h ≤ 1` from a start value with `c ≥ 1/2`,

  `‖Yₙ - X(n h)‖ ≤ 4 ‖Y₀ - X(0)‖ + 18 (1 + n h) h`     for every `lam ≥ 0`.

The loss of a step is of size `h a/(1 + a)`, where `a = h lam sₙ²` is the stiff energy of the
numerical row basis `(cₙ, sₙ)`. The L-step is a full resolvent step for the rough component of
the row basis: with `tₙ = sₙ/cₙ`,

  `tₙ₊₁² + h lam tₙ₊₁² ≤ tₙ²`,

so the squared tangent of the row angle decreases and its decrease pays the stiff energy of all
later row bases: `∑_{k ≥ 1} h lam tₖ² ≤ t₀²`. Only the first step can lose `≈ h`.

## Main results

* `StiffRowsExample.norm_run_sub_le`: the bound for runs of any length.
* `StiffRowsExample.sq_div_add_le_sq_div`: the decrease of the squared tangent in one step.

## Implementation notes

The state of the run is described by three numbers that do not depend on the signs of the bases:
the entry `p = (Yₙ)₀₀`, the ratio `ρ = (Uₙ)₁/(Uₙ)₀` and `t = (Vₙ)₁/(Vₙ)₀`; then
`Yₙ = p (1, ρ)ᵀ (1, t)`. One step gives `ρ' (1 + a + h) = ρ (1 + a)` (the K-step is a backward
Euler step of size `h/(1 + a)` for the direction of the columns) and
`p' = p (1 + ρ ρ')(1 + t t') / ((1 + t'²)(1 + ρ'² (1 + h)) + h lam t'² (1 + ρ'²))`.

## References

* [CerutiLubich2022] for the BUG integrator; backward Euler substeps as in arXiv 2610.18419.
-/

open Set
open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA

namespace StiffRowsExample

/-- The matrix `diag(0, -1)` acting on the columns. -/
local notation "Mᵣ" => (!![0, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ)

/-- The stiff matrix `diag(0, -lam)` acting on the rows. -/
local notation "Nᵣ" lam => (!![0, 0; 0, -lam] : Matrix (Fin 2) (Fin 2) ℝ)

/-- The start column `(3/5, 4/5)ᵀ`. -/
local notation "uᵣ" => (!![3 / 5; 4 / 5] : Matrix (Fin 2) (Fin 1) ℝ)

private theorem ratio_step {c s σ c' s' L₀ L₁ d₀ d₁ : ℝ} (hc : c ≠ 0) (hσ : σ ≠ 0)
    (l0 : L₀ * d₀ = c * σ) (l1 : L₁ * d₁ = s * σ)
    (cl0 : c' * (c' * L₀ + s' * L₁) = L₀) (cl1 : s' * (c' * L₀ + s' * L₁) = L₁) :
    c' ≠ 0 ∧ s' / c' * d₁ = s / c * d₀ := by
  have hL₀ : L₀ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at l0
    exact mul_ne_zero hc hσ l0.symm
  have hc' : c' ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at cl0
    exact hL₀ cl0.symm
  refine ⟨hc', ?_⟩
  have hx : s' * L₀ = c' * L₁ := by linear_combination c' * cl1 - s' * cl0
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff hc' hc]
  have key : (s' * d₁ * c - s * d₀ * c') * (σ * L₀) = 0 := by
    linear_combination c * σ * d₁ * hx + c' * c * σ * l1 - s * c' * σ * l0
  have h0 := (mul_eq_zero.1 key).resolve_right (mul_ne_zero hσ hL₀)
  linarith

private theorem tan_energy {t t' D h lam : ℝ} (hh : 0 < h) (hlam : 0 ≤ lam) (hD1 : 1 ≤ D)
    (hD2 : D ≤ 2) (r : t' * (D + h * lam) = t * D) : t' ^ 2 + h * lam * t' ^ 2 ≤ t ^ 2 := by
  have hsq : t ^ 2 * D ^ 2 = t' ^ 2 * (D + h * lam) ^ 2 := by
    rw [← mul_pow, ← mul_pow, r]
  have hDpos : 0 < D ^ 2 := by positivity
  have hl : 0 ≤ h * lam := by positivity
  have h3 : 0 ≤ D * (2 - D) + h * lam := by nlinarith
  have h5 := mul_nonneg (sq_nonneg t') (mul_nonneg hl h3)
  have h4 : (t' ^ 2 + h * lam * t' ^ 2) * D ^ 2 ≤ t ^ 2 * D ^ 2 := by
    rw [hsq]
    linarith
  exact le_of_mul_le_mul_right h4 hDpos

private theorem mag_identity {h lam α σ c α' σ' c' ρ ρ' t t' : ℝ}
    (hA : α' ^ 2 * (1 + ρ' ^ 2) = 1) (hC : c' ^ 2 * (1 + t' ^ 2) = 1)
    (hS : σ' * (1 + h * (ρ' * α') ^ 2 + h * lam * (t' * c') ^ 2) =
      (α * α' + ρ * α * (ρ' * α')) * σ * (c * c' + t * c * (t' * c'))) :
    α' * σ' * c' * ((1 + t' ^ 2) * (1 + ρ' ^ 2 * (1 + h)) + h * lam * t' ^ 2 * (1 + ρ' ^ 2)) =
      α * σ * c * ((1 + ρ * ρ') * (1 + t * t')) := by
  linear_combination (α' * c' * (1 + t' ^ 2) * (1 + ρ' ^ 2)) * hS +
    (α * σ * c * ((1 + ρ * ρ') * (1 + t * t')) * (c' ^ 2 * (1 + t' ^ 2)) -
      α' * c' * σ' * h * ρ' ^ 2 * (1 + t' ^ 2)) * hA +
    (α * σ * c * ((1 + ρ * ρ') * (1 + t * t')) -
      α' * c' * σ' * h * lam * t' ^ 2 * (1 + ρ' ^ 2)) * hC

private theorem num_den_bounds {ρ ρ' t t' a b D h lam : ℝ} (hh : 0 < h) (hlam : 0 ≤ lam)
    (ha : 0 ≤ a) (hb : b * (1 + a) = a) (hD1 : 1 ≤ D) (hDh : D ≤ 1 + h)
    (hD : (D - 1) * (1 + ρ ^ 2) = h * ρ ^ 2)
    (r1 : ρ' * (1 + a + h) = ρ * (1 + a)) (r2 : t' * (D + h * lam) = t * D) :
    0 < (1 + ρ * ρ') * (1 + t * t') ∧
    (1 + ρ * ρ') * (1 + t * t') ≤
      (1 + t' ^ 2) * (1 + ρ' ^ 2 * (1 + h)) + h * lam * t' ^ 2 * (1 + ρ' ^ 2) ∧
    ((1 + t' ^ 2) * (1 + ρ' ^ 2 * (1 + h)) + h * lam * t' ^ 2 * (1 + ρ' ^ 2)) *
      (1 - (ρ' ^ 2 * h * b + h * (h * lam * t' ^ 2))) ≤ (1 + ρ * ρ') * (1 + t * t') := by
  have ha1 : 0 < 1 + a := by linarith
  have hDpos : 0 < D := by linarith
  have hb0 : 0 ≤ b := by
    have hb' : b = a / (1 + a) := by rw [eq_div_iff ha1.ne']; exact hb
    rw [hb']; positivity
  have e1 : ρ * ρ' * (1 + a) = ρ' ^ 2 * (1 + a + h) := by linear_combination -ρ' * r1
  have e2 : t * t' * D = t' ^ 2 * (D + h * lam) := by linear_combination -t' * r2
  have hρρ : 0 ≤ ρ * ρ' := by
    have h0 : ρ * ρ' = ρ' ^ 2 * (1 + a + h) / (1 + a) := by rw [eq_div_iff ha1.ne']; exact e1
    rw [h0]; positivity
  have htt : 0 ≤ t * t' := by
    have h0 : t * t' = t' ^ 2 * (D + h * lam) / D := by rw [eq_div_iff hDpos.ne']; exact e2
    rw [h0]; positivity
  have hR : ρ' ^ 2 ≤ ρ ^ 2 := by
    have hsq : ρ' ^ 2 * (1 + a + h) ^ 2 = ρ ^ 2 * (1 + a) ^ 2 := by
      rw [← mul_pow, ← mul_pow, r1]
    have h2 : (1 + a) ^ 2 ≤ (1 + a + h) ^ 2 := pow_le_pow_left₀ ha1.le (by linarith) 2
    have h3 : ρ' ^ 2 * (1 + a) ^ 2 ≤ ρ ^ 2 * (1 + a) ^ 2 := by
      rw [← hsq]
      exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    exact le_of_mul_le_mul_right h3 (by positivity)
  have hD1' : h * ρ' ^ 2 ≤ (D - 1) * (1 + ρ' ^ 2) := by
    have h0 : (D - 1) * (1 + ρ' ^ 2) * (1 + ρ ^ 2) = h * ρ ^ 2 * (1 + ρ' ^ 2) := by
      linear_combination (1 + ρ' ^ 2) * hD
    have h2 := mul_nonneg hh.le (sub_nonneg.2 hR)
    have h3 : h * ρ' ^ 2 * (1 + ρ ^ 2) ≤ (D - 1) * (1 + ρ' ^ 2) * (1 + ρ ^ 2) := by
      rw [h0]
      linarith
    exact le_of_mul_le_mul_right h3 (by positivity)
  have hl : 0 ≤ h * lam := by positivity
  obtain ⟨den, hden⟩ : ∃ den : ℝ, den =
      (1 + t' ^ 2) * (1 + ρ' ^ 2 * (1 + h)) + h * lam * t' ^ 2 * (1 + ρ' ^ 2) := ⟨_, rfl⟩
  obtain ⟨num, hnum⟩ : ∃ num : ℝ, num = (1 + ρ * ρ') * (1 + t * t') := ⟨_, rfl⟩
  rw [← hden, ← hnum]
  have key : (den - num) * ((1 + a) * D) = (1 + t' ^ 2) * ρ' ^ 2 * h * a * D +
      t' ^ 2 * (h * lam) * ((D - 1) * (1 + ρ' ^ 2) * (1 + a) - ρ' ^ 2 * h) := by
    rw [hden, hnum]
    linear_combination (-(D + t * t' * D)) * e1 - ((1 + a) + ρ' ^ 2 * (1 + a + h)) * e2
  have hpos : 0 < (1 + a) * D := by positivity
  have hden1 : 1 + t' ^ 2 ≤ den := by
    have h0 : 0 ≤ (1 + t' ^ 2) * (ρ' ^ 2 * (1 + h)) + h * lam * t' ^ 2 * (1 + ρ' ^ 2) := by
      positivity
    have h2 : den = 1 + t' ^ 2 +
        ((1 + t' ^ 2) * (ρ' ^ 2 * (1 + h)) + h * lam * t' ^ 2 * (1 + ρ' ^ 2)) := by
      rw [hden]; ring
    linarith
  have hden2 : 1 + ρ' ^ 2 ≤ den := by
    have h0 : 0 ≤ ρ' ^ 2 * h + t' ^ 2 * (1 + ρ' ^ 2 * (1 + h)) +
        h * lam * t' ^ 2 * (1 + ρ' ^ 2) := by positivity
    have h2 : den = 1 + ρ' ^ 2 + (ρ' ^ 2 * h + t' ^ 2 * (1 + ρ' ^ 2 * (1 + h)) +
        h * lam * t' ^ 2 * (1 + ρ' ^ 2)) := by
      rw [hden]; ring
    linarith
  have hbr : 0 ≤ (D - 1) * (1 + ρ' ^ 2) * (1 + a) - ρ' ^ 2 * h := by
    have m1 := mul_le_mul_of_nonneg_right hD1' ha1.le
    have m2 : 0 ≤ h * ρ' ^ 2 * a := by positivity
    linarith
  have hnumpos : 0 < num := by rw [hnum]; positivity
  refine ⟨hnumpos, ?_, ?_⟩
  · have h5 : 0 ≤ (den - num) * ((1 + a) * D) := by
      rw [key]
      have h6 := mul_nonneg (mul_nonneg (sq_nonneg t') hl) hbr
      have h7 : 0 ≤ (1 + t' ^ 2) * ρ' ^ 2 * h * a * D := by positivity
      linarith
    have h8 := nonneg_of_mul_nonneg_left h5 hpos
    linarith
  · have h7 : 0 ≤ ρ' ^ 2 * h * b := by positivity
    have t1 : (1 + t' ^ 2) * ρ' ^ 2 * h * a * D ≤ ρ' ^ 2 * h * b * den * ((1 + a) * D) := by
      have h6 : (1 + t' ^ 2) * ρ' ^ 2 * h * a * D =
          ρ' ^ 2 * h * b * (1 + t' ^ 2) * ((1 + a) * D) := by
        linear_combination (-((1 + t' ^ 2) * ρ' ^ 2 * h * D)) * hb
      rw [h6]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hden1 h7) hpos.le
    have h8 : (D - 1) * (1 + ρ' ^ 2) * (1 + a) - ρ' ^ 2 * h ≤ h * den * ((1 + a) * D) := by
      have h9 : (D - 1) * (1 + ρ' ^ 2) * (1 + a) ≤ h * (1 + ρ' ^ 2) * (1 + a) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) ha1.le
      have h11 : (1 + ρ' ^ 2) * 1 ≤ den * D :=
        mul_le_mul hden2 hD1 zero_le_one (by linarith [sq_nonneg ρ'])
      have h10 := mul_le_mul_of_nonneg_left h11 (mul_nonneg hh.le ha1.le)
      have h12 : 0 ≤ ρ' ^ 2 * h := by positivity
      linarith
    have h12 : 0 ≤ t' ^ 2 * (h * lam) := by positivity
    have t2 := mul_le_mul_of_nonneg_left h8 h12
    have h13 : (den - num) * ((1 + a) * D) ≤
        (ρ' ^ 2 * h * b + h * (h * lam * t' ^ 2)) * den * ((1 + a) * D) := by
      rw [key]; linarith
    have h14 := le_of_mul_le_mul_right h13 hpos
    linarith

private theorem mul_bounds {p p' num den x : ℝ} (hp : 0 < p) (hnum : 0 < num)
    (e : p' * den = p * num) (hU : num ≤ den) (hL : den * (1 - x) ≤ num) :
    0 < p' ∧ p' ≤ p ∧ p * (1 - x) ≤ p' := by
  have hden : 0 < den := lt_of_lt_of_le hnum hU
  have hp' : p' = p * num / den := by rw [eq_div_iff hden.ne']; exact e
  refine ⟨by rw [hp']; positivity, ?_, ?_⟩
  · rw [hp', div_le_iff₀ hden]
    exact mul_le_mul_of_nonneg_left hU hp.le
  · rw [hp', le_div_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_left hL hp.le]


private theorem step_real {h lam α β σ c s α' β' σ' c' s' K₀ K₁ L₀ L₁ ρ ρ' t t' : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hlam : 0 ≤ lam)
    (hβ : β = ρ * α) (hβ' : β' = ρ' * α') (hs : s = t * c) (hs' : s' = t' * c')
    (hα' : α' ≠ 0) (hc' : c' ≠ 0)
    (hU : α ^ 2 + β ^ 2 = 1) (hU' : α' ^ 2 + β' ^ 2 = 1) (hV' : c' ^ 2 + s' ^ 2 = 1)
    (k0 : K₀ * (1 + h * lam * s ^ 2) = α * σ) (k1 : K₁ * (1 + h * lam * s ^ 2 + h) = β * σ)
    (l0 : L₀ * (1 + h * β ^ 2) = c * σ) (l1 : L₁ * (1 + h * β ^ 2 + h * lam) = s * σ)
    (ck0 : α' * (α' * K₀ + β' * K₁) = K₀) (ck1 : β' * (α' * K₀ + β' * K₁) = K₁)
    (cl0 : c' * (c' * L₀ + s' * L₁) = L₀) (cl1 : s' * (c' * L₀ + s' * L₁) = L₁)
    (hS : σ' * (1 + h * β' ^ 2 + h * lam * s' ^ 2) =
      (α * α' + β * β') * σ * (c * c' + s * s'))
    (hp : 0 < α * σ * c) :
    0 < α' * σ' * c' ∧ α' * σ' * c' ≤ α * σ * c ∧
      α * σ * c * (1 - (ρ' ^ 2 * h * (h * lam * s ^ 2 / (1 + h * lam * s ^ 2)) +
        h * (h * lam * t' ^ 2))) ≤ α' * σ' * c' ∧
      t' ^ 2 + h * lam * t' ^ 2 ≤ t ^ 2 ∧
      ρ' * (1 + h * lam * s ^ 2 + h) = ρ * (1 + h * lam * s ^ 2) := by
  subst hβ hβ' hs hs'
  have hα : α ≠ 0 := by rintro rfl; simp at hp
  have hσ : σ ≠ 0 := by rintro rfl; simp at hp
  have hc : c ≠ 0 := by rintro rfl; simp at hp
  have ha : 0 ≤ h * lam * (t * c) ^ 2 := by positivity
  have ha1 : (1 + h * lam * (t * c) ^ 2) ≠ 0 := by positivity
  have hβ1 : (ρ * α) ^ 2 ≤ 1 := by linarith [sq_nonneg α]
  have hD1 : (1 : ℝ) ≤ 1 + h * (ρ * α) ^ 2 := by
    have h0 := mul_nonneg hh.le (sq_nonneg (ρ * α))
    linarith
  have hDh : 1 + h * (ρ * α) ^ 2 ≤ 1 + h := by
    have h0 := mul_le_mul_of_nonneg_left hβ1 hh.le
    linarith
  obtain ⟨-, r2⟩ := ratio_step hc hσ l0 l1 cl0 cl1
  obtain ⟨-, r1⟩ := ratio_step hα hσ k0 k1 ck0 ck1
  rw [mul_div_cancel_right₀ _ hc', mul_div_cancel_right₀ _ hc] at r2
  rw [mul_div_cancel_right₀ _ hα', mul_div_cancel_right₀ _ hα] at r1
  have hA : α' ^ 2 * (1 + ρ' ^ 2) = 1 := by linear_combination hU'
  have hAα : α ^ 2 * (1 + ρ ^ 2) = 1 := by linear_combination hU
  have hC : c' ^ 2 * (1 + t' ^ 2) = 1 := by linear_combination hV'
  have hD : (1 + h * (ρ * α) ^ 2 - 1) * (1 + ρ ^ 2) = h * ρ ^ 2 := by
    linear_combination (h * ρ ^ 2) * hAα
  have e := mag_identity hA hC hS
  obtain ⟨hnum, hUb, hLb⟩ :=
    num_den_bounds hh hlam ha (div_mul_cancel₀ _ ha1) hD1 hDh hD r1 r2
  obtain ⟨h1, h2, h3⟩ := mul_bounds hp hnum e hUb hLb
  exact ⟨h1, h2, h3, tan_energy hh hlam hD1 (by linarith) r2, r1⟩

private theorem seq_bounds {h lam : ℝ} (hh : 0 < h) (hlam : 0 ≤ lam) {n : ℕ}
    {p ρ t a : ℕ → ℝ} (hp0 : 0 < p 0) (hρ0 : ρ 0 = 4 / 3) (ha0 : ∀ k, 0 ≤ a k)
    (ha : ∀ k ≤ n, 0 < p k → a k ≤ h * lam * t k ^ 2)
    (hstep : ∀ k < n, 0 < p k → 0 < p (k + 1) ∧ p (k + 1) ≤ p k ∧
      p k * (1 - (ρ (k + 1) ^ 2 * h * (a k / (1 + a k)) + h * (h * lam * t (k + 1) ^ 2))) ≤
        p (k + 1) ∧
      t (k + 1) ^ 2 + h * lam * t (k + 1) ^ 2 ≤ t k ^ 2 ∧
      ρ (k + 1) * (1 + a k + h) = ρ k * (1 + a k)) :
    ∀ k ≤ n, 0 < p k ∧ p k ≤ p 0 ∧
      p 0 * (1 - 16 / 9 * h - 25 / 9 * h * (t 0 ^ 2 - t k ^ 2) +
        16 / 9 * h * (a k / (1 + a k))) ≤ p k ∧
      t k ^ 2 ≤ t 0 ^ 2 ∧ 4 / 3 * Real.exp (-(k * h)) ≤ ρ k ∧ ρ k ≤ 4 / 3 ∧
      ρ k - 4 / 3 * Real.exp (-(k * h)) ≤
        4 / 3 * (h * (1 - a k / (1 + a k)) + h * (t 0 ^ 2 - t k ^ 2) + k * h ^ 2) := by
  have hbnn : ∀ k, 0 ≤ a k / (1 + a k) := fun k =>
    div_nonneg (ha0 k) (by linarith [ha0 k])
  have hb1 : ∀ k, a k / (1 + a k) ≤ 1 := fun k => by
    rw [div_le_one (by linarith [ha0 k])]; linarith
  intro k
  induction k with
  | zero =>
    intro _
    have h1 := mul_nonneg hh.le (sub_nonneg.2 (hb1 0))
    refine ⟨hp0, le_rfl, ?_, le_rfl, ?_, hρ0.le, ?_⟩
    · have h2 : 1 - 16 / 9 * h - 25 / 9 * h * (t 0 ^ 2 - t 0 ^ 2) +
          16 / 9 * h * (a 0 / (1 + a 0)) ≤ 1 := by linarith
      calc p 0 * _ ≤ p 0 * 1 := mul_le_mul_of_nonneg_left h2 hp0.le
        _ = p 0 := mul_one _
    · simp only [Nat.cast_zero, zero_mul, neg_zero, Real.exp_zero, mul_one]
      linarith
    · simp only [Nat.cast_zero, zero_mul, neg_zero, Real.exp_zero, mul_one]
      linarith
  | succ k ih =>
    intro hk
    obtain ⟨hpk, hpk0, hJ, htk, hρl, hρu, hδ⟩ := ih (Nat.le_of_succ_le hk)
    obtain ⟨hp', hpp, hlow, hen, hr⟩ := hstep k (Nat.lt_of_succ_le hk) hpk
    have hak := ha0 k
    have hak' := ha0 (k + 1)
    have hb := hbnn k
    have hb' : a (k + 1) / (1 + a (k + 1)) ≤ a (k + 1) := div_le_self hak' (by linarith)
    have ha' := ha (k + 1) hk hp'
    have he' : 0 ≤ h * lam * t (k + 1) ^ 2 := by positivity
    have hdiff : a (k + 1) / (1 + a (k + 1)) ≤ t k ^ 2 - t (k + 1) ^ 2 := by linarith
    have hE0 : 0 < Real.exp (-(k * h)) := Real.exp_pos _
    have hρk0 : 0 ≤ ρ k := by linarith
    have hden : 0 < 1 + a k + h := by linarith
    have hρ'0 : 0 ≤ ρ (k + 1) := by
      have h0 : 0 ≤ ρ (k + 1) * (1 + a k + h) := by
        rw [hr]; exact mul_nonneg hρk0 (by linarith)
      exact nonneg_of_mul_nonneg_left h0 hden
    have hρ'le : ρ (k + 1) ≤ ρ k := by
      have h0 : ρ (k + 1) * (1 + a k + h) ≤ ρ k * (1 + a k + h) := by
        rw [hr]; exact mul_le_mul_of_nonneg_left (by linarith) hρk0
      exact le_of_mul_le_mul_right h0 hden
    have hρ'sq : ρ (k + 1) ^ 2 ≤ 16 / 9 := by
      have h0 := pow_le_pow_left₀ hρ'0 (hρ'le.trans hρu) 2
      norm_num at h0
      exact h0
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have hw0 : 0 < Real.exp (-h) := Real.exp_pos _
    have hw1 : Real.exp (-h) * (1 + h) ≤ 1 := by
      have h1 := Real.add_one_le_exp h
      have h2 : Real.exp (-h) * Real.exp h = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      nlinarith
    have hw2 : 1 - h ≤ Real.exp (-h) := by
      have h1 := Real.add_one_le_exp (-h)
      linarith
    have hE : Real.exp (-(((k + 1 : ℕ) : ℝ) * h)) = Real.exp (-(k * h)) * Real.exp (-h) := by
      rw [← Real.exp_add, hcast]
      congr 1
      ring
    have hbeq : a k / (1 + a k) * (1 + a k) = a k := div_mul_cancel₀ _ (by linarith)
    refine ⟨hp', hpp.trans hpk0, ?_, by linarith, ?_, hρ'le.trans hρu, ?_⟩
    · have hx0 : 0 ≤ ρ (k + 1) ^ 2 * h * (a k / (1 + a k)) + h * (h * lam * t (k + 1) ^ 2) := by
        positivity
      have hhb : 0 ≤ h * (a k / (1 + a k)) := mul_nonneg hh.le hb
      have hxX : ρ (k + 1) ^ 2 * h * (a k / (1 + a k)) + h * (h * lam * t (k + 1) ^ 2) ≤
          16 / 9 * h * (a k / (1 + a k)) + h * (h * lam * t (k + 1) ^ 2) := by
        have h0 := mul_le_mul_of_nonneg_right hρ'sq hhb
        linarith
      have h3 := mul_le_mul hpk0 hxX hx0 hp0.le
      have key : 0 ≤ p 0 * (h * (25 / 9 * (t k ^ 2 - t (k + 1) ^ 2) -
          h * lam * t (k + 1) ^ 2 - 16 / 9 * (a (k + 1) / (1 + a (k + 1))))) :=
        mul_nonneg hp0.le (mul_nonneg hh.le (by linarith))
      linarith
    · rw [hE]
      have h1 : Real.exp (-h) * (1 + a k + h) ≤ 1 + a k := by
        have h2 := mul_le_mul_of_nonneg_right hw1 (by linarith : (0 : ℝ) ≤ 1 + a k)
        have h3 := mul_nonneg hw0.le (mul_nonneg hak hh.le)
        linarith
      have s1 : ρ k * Real.exp (-h) ≤ ρ (k + 1) := by
        have h2 : ρ k * Real.exp (-h) * (1 + a k + h) ≤ ρ (k + 1) * (1 + a k + h) := by
          rw [hr]
          have h3 := mul_le_mul_of_nonneg_left h1 hρk0
          linarith
        exact le_of_mul_le_mul_right h2 hden
      have h4 := mul_le_mul_of_nonneg_right hρl hw0.le
      linarith
    · rw [hE, hcast]
      have c1 : (1 - a k / (1 + a k) - h) * (1 + a k + h) ≤ 1 := by
        have h0 : (1 - a k / (1 + a k) - h) * (1 + a k + h) =
            1 - a k / (1 + a k) * h - a k * h - h ^ 2 := by
          linear_combination (-1 : ℝ) * hbeq
        rw [h0]
        nlinarith [mul_nonneg hb hh.le, mul_nonneg hak hh.le, sq_nonneg h]
      have u1 : ρ (k + 1) ≤ ρ k - ρ k * h * (1 - a k / (1 + a k) - h) := by
        have h2 : ρ (k + 1) * (1 + a k + h) ≤
            (ρ k - ρ k * h * (1 - a k / (1 + a k) - h)) * (1 + a k + h) := by
          rw [hr]
          have h3 := mul_le_mul_of_nonneg_left c1 (mul_nonneg hρk0 hh.le)
          linarith
        exact le_of_mul_le_mul_right h2 hden
      have g1 := mul_nonneg hh.le (sub_nonneg.2 hρl)
      have g2 := mul_nonneg (sub_nonneg.2 hρu) (mul_nonneg hh.le (add_nonneg hb hh.le))
      have g3 := mul_nonneg hE0.le (sub_nonneg.2 hw2)
      have g4 := mul_nonneg hh.le (sub_nonneg.2 hdiff)
      linarith

private theorem sq_sum_le {X1 X2 X3 a1 a2 a3 B : ℝ} (h1 : X1 ≤ a1 ^ 2) (h2 : X2 ≤ a2 ^ 2)
    (h3 : X3 ≤ a3 ^ 2) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (hB : a1 + a2 + a3 ≤ B) :
    X1 + X2 + X3 ≤ B ^ 2 := by
  have h4 := pow_le_pow_left₀ (by positivity) hB 2
  have h5 := mul_nonneg ha1 ha2
  have h6 := mul_nonneg ha1 ha3
  have h7 := mul_nonneg ha2 ha3
  have h8 : (a1 + a2 + a3) ^ 2 =
      a1 ^ 2 + a2 ^ 2 + a3 ^ 2 + 2 * (a1 * a2) + 2 * (a1 * a3) + 2 * (a2 * a3) := by ring
  linarith

private theorem start_bounds {c s e₀ : ℝ} (hc : 1 / 2 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1)
    (he₀ : 0 ≤ e₀) (he : 2 - 2 * c ≤ e₀ ^ 2) :
    c ≤ 1 ∧ (s / c) ^ 2 ≤ 3 ∧ (s / c) ^ 2 ≤ 4 * e₀ ^ 2 ∧ 1 - c ≤ e₀ / 2 := by
  have hc1 : c ≤ 1 := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [sq_nonneg s]
  have hc2 : 1 / 4 ≤ c ^ 2 := by nlinarith
  have hs2 : s ^ 2 ≤ e₀ ^ 2 := by nlinarith [sq_nonneg (1 - c)]
  have hT : (s / c) ^ 2 ≤ 4 * s ^ 2 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    have h0 := mul_nonneg (sq_nonneg s) (sub_nonneg.2 hc2)
    linarith
  refine ⟨hc1, by linarith, by linarith, ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have h0 := mul_self_lt_mul_self (by positivity : (0 : ℝ) ≤ e₀ / 2) hcon
  have h1 : (1 - c) * (1 - c) ≤ (1 - c) * (1 / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

private theorem err_bound {h c e₀ p ρ t E x T : ℝ} (hh : 0 < h) (hx : 0 ≤ x)
    (hc1 : c ≤ 1) (he₀ : 0 ≤ e₀) (hT0 : 0 ≤ T) (hT3 : T ≤ 3)
    (hT4 : T ≤ 4 * e₀ ^ 2) (h1c : 1 - c ≤ e₀ / 2)
    (hE0 : 0 ≤ E) (hp : 0 < p) (hp0 : p ≤ 3 / 5 * c)
    (hpl : 3 / 5 * c * (1 - 16 / 9 * h - 25 / 9 * h * T) ≤ p)
    (ht : t ^ 2 ≤ T) (hρl : 4 / 3 * E ≤ ρ) (hρu : ρ ≤ 4 / 3)
    (hρd : ρ - 4 / 3 * E ≤ 4 / 3 * (h + h * T + x * h)) :
    (p - 3 / 5) ^ 2 + (t * p) ^ 2 + ((ρ * p - 4 / 5 * E) ^ 2 + (ρ * t * p) ^ 2) ≤
      (4 * e₀ + 18 * (1 + x) * h) ^ 2 := by
  have hρ0 : 0 ≤ ρ := by linarith
  have hA0 : 0 ≤ 3 / 5 - p := by linarith
  have hA : 3 / 5 - p ≤ 3 / 10 * e₀ + 91 / 15 * h := by
    have h1 : c * (h * (16 / 9 + 25 / 9 * T)) ≤ 1 * (h * (16 / 9 + 25 / 9 * 3)) :=
      mul_le_mul hc1 (mul_le_mul_of_nonneg_left (by linarith) hh.le) (by positivity)
        zero_le_one
    linarith
  have hxh : 0 ≤ x * h := mul_nonneg hx hh.le
  have hB1 : ρ * p - 4 / 5 * E ≤ 4 / 5 * (4 * h + x * h) := by
    have h1 := mul_nonneg hρ0 hA0
    have h2 := mul_le_mul_of_nonneg_left hT3 hh.le
    linarith
  have hB2 : -(4 / 3 * (3 / 5 - p)) ≤ ρ * p - 4 / 5 * E := by
    have h1 := mul_nonneg (sub_nonneg.2 hρu) hA0
    linarith
  have hC : (t * p) ^ 2 + (ρ * t * p) ^ 2 ≤ (2 * e₀) ^ 2 := by
    have hp2 : p ^ 2 ≤ (3 / 5) ^ 2 := pow_le_pow_left₀ hp.le (by linarith) 2
    have hρ2 : ρ ^ 2 ≤ (4 / 3) ^ 2 := pow_le_pow_left₀ hρ0 hρu 2
    have h1 : (t * p) ^ 2 + (ρ * t * p) ^ 2 = t ^ 2 * (p ^ 2 * (1 + ρ ^ 2)) := by ring
    have h2 : p ^ 2 * (1 + ρ ^ 2) ≤ (3 / 5) ^ 2 * (1 + (4 / 3) ^ 2) :=
      mul_le_mul hp2 (by linarith) (by positivity) (by norm_num)
    have h3 : t ^ 2 * (p ^ 2 * (1 + ρ ^ 2)) ≤ T * 1 :=
      mul_le_mul ht (by norm_num at h2; linarith) (by positivity) hT0
    rw [h1]
    linarith
  have ha1 : 0 ≤ 3 / 10 * e₀ + 91 / 15 * h := by positivity
  have ha2 : 0 ≤ 4 / 3 * (3 / 10 * e₀ + 91 / 15 * h) + 4 / 5 * (4 * h + x * h) := by positivity
  have s1 : (p - 3 / 5) ^ 2 ≤ (3 / 10 * e₀ + 91 / 15 * h) ^ 2 := by
    have h0 := pow_le_pow_left₀ hA0 hA 2
    have h1 : (p - 3 / 5) ^ 2 = (3 / 5 - p) ^ 2 := by ring
    rw [h1]
    exact h0
  have s2 : (ρ * p - 4 / 5 * E) ^ 2 ≤
      (4 / 3 * (3 / 10 * e₀ + 91 / 15 * h) + 4 / 5 * (4 * h + x * h)) ^ 2 :=
    sq_le_sq' (by linarith) (by linarith)
  have hsum : 3 / 10 * e₀ + 91 / 15 * h +
      (4 / 3 * (3 / 10 * e₀ + 91 / 15 * h) + 4 / 5 * (4 * h + x * h)) + 2 * e₀ ≤
      4 * e₀ + 18 * (1 + x) * h := by
    linarith
  have h9 := sq_sum_le s1 s2 hC ha1 ha2 (by positivity) hsum
  linarith

/-- The entries of a product of rank-one factors. -/
private theorem factor_apply (U V : Matrix (Fin 2) (Fin 1) ℝ) (S : Matrix (Fin 1) (Fin 1) ℝ)
    (i j : Fin 2) : (U * S * Vᵀ) i j = U i 0 * S 0 0 * V j 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.mul_apply, Fin.sum_univ_one,
    Matrix.transpose_apply]

/-- An orthonormal column in `ℝ²` has entries with squares summing to one. -/
private theorem sq_add_sq_of_orth {W : Matrix (Fin 2) (Fin 1) ℝ} (hW : Wᵀ * W = 1) :
    W 0 0 ^ 2 + W 1 0 ^ 2 = 1 := by
  have e := congrFun (congrFun hW 0) 0
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.transpose_apply,
    Matrix.one_apply_eq] at e
  linear_combination e

/-- The scalar relations of one step of the matrix implicit BUG integrator of rank one for
`F(Z) = diag(0, -1) Z + Z diag(0, -lam)` with exact capture. -/
private theorem step_entries {h lam ε t₁ : ℝ} {S₀ S₁ : Matrix (Fin 1) (Fin 1) ℝ}
    {U₀ V₀ K₁ L₁ U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ} {Y₁ : Matrix (Fin 2) (Fin 2) ℝ}
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
      Mᵣ * Z + Z * Nᵣ lam) ε 0 0 t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) :
    (K₁ 0 0 * (1 + h * lam * V₀ 1 0 ^ 2) = U₀ 0 0 * S₀ 0 0 ∧
      K₁ 1 0 * (1 + h * lam * V₀ 1 0 ^ 2 + h) = U₀ 1 0 * S₀ 0 0) ∧
    (L₁ 0 0 * (1 + h * U₀ 1 0 ^ 2) = V₀ 0 0 * S₀ 0 0 ∧
      L₁ 1 0 * (1 + h * U₀ 1 0 ^ 2 + h * lam) = V₀ 1 0 * S₀ 0 0) ∧
    (U₁ 0 0 * (U₁ 0 0 * K₁ 0 0 + U₁ 1 0 * K₁ 1 0) = K₁ 0 0 ∧
      U₁ 1 0 * (U₁ 0 0 * K₁ 0 0 + U₁ 1 0 * K₁ 1 0) = K₁ 1 0) ∧
    (V₁ 0 0 * (V₁ 0 0 * L₁ 0 0 + V₁ 1 0 * L₁ 1 0) = L₁ 0 0 ∧
      V₁ 1 0 * (V₁ 0 0 * L₁ 0 0 + V₁ 1 0 * L₁ 1 0) = L₁ 1 0) ∧
    S₁ 0 0 * (1 + h * U₁ 1 0 ^ 2 + h * lam * V₁ 1 0 ^ 2) =
      (U₀ 0 0 * U₁ 0 0 + U₀ 1 0 * U₁ 1 0) * S₀ 0 0 * (V₀ 0 0 * V₁ 0 0 + V₀ 1 0 * V₁ 1 0) := by
  have hU := sq_add_sq_of_orth hs.orthU₀
  have hV := sq_add_sq_of_orth hs.orthV₀
  have hU' := sq_add_sq_of_orth hs.orthU₁
  have hV' := sq_add_sq_of_orth hs.orthV₁
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · have e := congrFun (congrFun hs.kstep 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at e
    linear_combination e
  · have e := congrFun (congrFun hs.kstep 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at e
    linear_combination e - h * K₁ 1 0 * hV
  · have e := congrFun (congrFun hs.lstep 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, Function.swap] at e
    linear_combination e
  · have e := congrFun (congrFun hs.lstep 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, Function.swap] at e
    linear_combination e - h * lam * L₁ 1 0 * hU
  · have hcap0 : (1 - U₁ * U₁ᵀ) * (K₁ * V₀ᵀ) = 0 := norm_le_zero_iff.1 hs.kcap
    have hcap : U₁ * (U₁ᵀ * K₁) = K₁ := by
      have e := congrArg (fun Z => Z * V₀) hcap0
      simp only [Matrix.zero_mul, Matrix.mul_assoc, hs.orthV₀, Matrix.mul_one] at e
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at e
      rw [← Matrix.mul_assoc]
      exact e.symm
    have c0 := congrFun (congrFun hcap 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transpose_apply, Matrix.transpose_apply] at c0
    exact c0
  · have hcap0 : (1 - U₁ * U₁ᵀ) * (K₁ * V₀ᵀ) = 0 := norm_le_zero_iff.1 hs.kcap
    have hcap : U₁ * (U₁ᵀ * K₁) = K₁ := by
      have e := congrArg (fun Z => Z * V₀) hcap0
      simp only [Matrix.zero_mul, Matrix.mul_assoc, hs.orthV₀, Matrix.mul_one] at e
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at e
      rw [← Matrix.mul_assoc]
      exact e.symm
    have c1 := congrFun (congrFun hcap 1) 0
    rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transpose_apply, Matrix.transpose_apply] at c1
    exact c1
  · have hl0 : U₀ * L₁ᵀ * (1 - V₁ * V₁ᵀ) = 0 := norm_le_zero_iff.1 hs.lcap
    have e := congrArg (fun Z => U₀ᵀ * Z) hl0
    simp only [Matrix.mul_zero, ← Matrix.mul_assoc, hs.orthU₀, Matrix.one_mul] at e
    have d := congrFun (congrFun e 0) 0
    simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two] at d
    linear_combination -d
  · have hl0 : U₀ * L₁ᵀ * (1 - V₁ * V₁ᵀ) = 0 := norm_le_zero_iff.1 hs.lcap
    have e := congrArg (fun Z => U₀ᵀ * Z) hl0
    simp only [Matrix.mul_zero, ← Matrix.mul_assoc, hs.orthU₀, Matrix.one_mul] at e
    have d := congrFun (congrFun e 0) 1
    simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two] at d
    linear_combination -d
  · have e := congrFun (congrFun hs.sstep 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at e
    linear_combination e - h * U₁ 1 0 ^ 2 * S₁ 0 0 * hV' - h * lam * V₁ 1 0 ^ 2 * S₁ 0 0 * hU'

/-- The scalar form of one step: the entry `(0, 0)` of the numerical solution, the tangent of
the row angle and the ratio of the entries of the column basis. -/
private theorem step_facts {h lam ε t₁ : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hlam : 0 ≤ lam)
    {S₀ S₁ : Matrix (Fin 1) (Fin 1) ℝ} {U₀ V₀ K₁ L₁ U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ}
    {Y₁ : Matrix (Fin 2) (Fin 2) ℝ}
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
      Mᵣ * Z + Z * Nᵣ lam) ε 0 0 t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁)
    (hp : 0 < U₀ 0 0 * S₀ 0 0 * V₀ 0 0) :
    0 < U₁ 0 0 * S₁ 0 0 * V₁ 0 0 ∧ U₁ 0 0 * S₁ 0 0 * V₁ 0 0 ≤ U₀ 0 0 * S₀ 0 0 * V₀ 0 0 ∧
      U₀ 0 0 * S₀ 0 0 * V₀ 0 0 * (1 - ((U₁ 1 0 / U₁ 0 0) ^ 2 * h *
        (h * lam * V₀ 1 0 ^ 2 / (1 + h * lam * V₀ 1 0 ^ 2)) +
        h * (h * lam * (V₁ 1 0 / V₁ 0 0) ^ 2))) ≤ U₁ 0 0 * S₁ 0 0 * V₁ 0 0 ∧
      (V₁ 1 0 / V₁ 0 0) ^ 2 + h * lam * (V₁ 1 0 / V₁ 0 0) ^ 2 ≤ (V₀ 1 0 / V₀ 0 0) ^ 2 ∧
      U₁ 1 0 / U₁ 0 0 * (1 + h * lam * V₀ 1 0 ^ 2 + h) =
        U₀ 1 0 / U₀ 0 0 * (1 + h * lam * V₀ 1 0 ^ 2) := by
  obtain ⟨⟨k0, k1⟩, ⟨l0, l1⟩, ⟨ck0, ck1⟩, ⟨cl0, cl1⟩, hS⟩ := step_entries hs
  have hα : U₀ 0 0 ≠ 0 := by
    intro h0
    rw [h0] at hp
    simp at hp
  have hσ : S₀ 0 0 ≠ 0 := by
    intro h0
    rw [h0] at hp
    simp at hp
  have hc : V₀ 0 0 ≠ 0 := by
    intro h0
    rw [h0] at hp
    simp at hp
  obtain ⟨hc', -⟩ := ratio_step hc hσ l0 l1 cl0 cl1
  obtain ⟨hα', -⟩ := ratio_step hα hσ k0 k1 ck0 ck1
  exact step_real hh hh1 hlam (div_mul_cancel₀ _ hα).symm (div_mul_cancel₀ _ hα').symm
    (div_mul_cancel₀ _ hc).symm (div_mul_cancel₀ _ hc').symm hα' hc'
    (sq_add_sq_of_orth hs.orthU₀) (sq_add_sq_of_orth hs.orthU₁) (sq_add_sq_of_orth hs.orthV₁)
    k0 k1 l0 l1 ck0 ck1 cl0 cl1 hS hp

/-- **The squared tangent of the row angle pays the stiff energy.** In one step of the matrix
implicit BUG integrator (rank `1`, exact capture) for
`F(Z) = diag(0, -1) Z + Z diag(0, -lam)` with step size `0 < h ≤ 1`, started from factors with
`(U₀)₀ S₀ (V₀)₀ > 0`, the tangents `t₀ = (V₀)₁/(V₀)₀` and `t₁ = (V₁)₁/(V₁)₀` of the angle of
the row basis against the kernel of the stiff matrix satisfy `t₁² + h lam t₁² ≤ t₀²`. -/
theorem sq_div_add_le_sq_div {h lam ε t₁ : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hlam : 0 ≤ lam)
    {S₀ S₁ : Matrix (Fin 1) (Fin 1) ℝ} {U₀ V₀ K₁ L₁ U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ}
    {Y₁ : Matrix (Fin 2) (Fin 2) ℝ}
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
      Mᵣ * Z + Z * Nᵣ lam) ε 0 0 t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁)
    (hp : 0 < U₀ 0 0 * S₀ 0 0 * V₀ 0 0) :
    (V₁ 1 0 / V₁ 0 0) ^ 2 + h * lam * (V₁ 1 0 / V₁ 0 0) ^ 2 ≤ (V₀ 1 0 / V₀ 0 0) ^ 2 :=
  (step_facts hh hh1 hlam hs hp).2.2.2.1

/-- **Runs on the stiff-rows family are uniform in the stiffness.** Let `0 < h ≤ 1`, `lam ≥ 0`
and `c ≥ 1/2`, `c² + s² = 1`. For every run of `n` steps of the matrix implicit BUG integrator
(rank `1`, exact capture, no truncation) for `F(Z) = diag(0, -1) Z + Z diag(0, -lam)` from
`Y₀ = (3/5, 4/5)ᵀ (c, s)`, the result `Yₙ = Uₙ Sₙ Vₙᵀ` satisfies

  `‖Yₙ - X(n h)‖ ≤ 4 ‖Y₀ - X(0)‖ + 18 (1 + n h) h`,   `X(t) = (3/5, 4/5 e^{-t})ᵀ (1, 0)`,

with constants that do not depend on `lam`, although no bound
`‖Y₁ - X(h)‖ ≤ C₁ ‖Y₀ - X(0)‖ + C₂ h²` for one step holds uniformly in `lam`
(`not_exists_forall_norm_sub_le`). -/
theorem norm_run_sub_le {h lam c s : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hlam : 0 ≤ lam)
    (hc : 1 / 2 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1) {n : ℕ} {ε t : ℕ → ℝ}
    {U K L V : ℕ → Matrix (Fin 2) (Fin 1) ℝ} {S : ℕ → Matrix (Fin 1) (Fin 1) ℝ}
    {Y : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (hstep : ∀ k < n, IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
      Mᵣ * Z + Z * Nᵣ lam) (ε k) 0 0 (t k) h (U k) (S k) (V k) (K k) (L k) (U (k + 1))
      (V (k + 1)) (S (k + 1)) (Y k))
    (hK₀ : U 0 * S 0 = uᵣ) (hV₀ : V 0 = !![c; s]) :
    ‖U n * S n * (V n)ᵀ - !![3 / 5, 0; 4 / 5 * Real.exp (-(n * h)), 0]‖ ≤
      4 * ‖uᵣ * !![c; s]ᵀ - !![3 / 5, 0; 4 / 5, 0]‖ + 18 * (1 + n * h) * h := by
  have h00 : U 0 0 0 * S 0 0 0 = 3 / 5 := by
    have e := congrFun (congrFun hK₀ 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_one] at e
    simpa using e
  have h10 : U 0 1 0 * S 0 0 0 = 4 / 5 := by
    have e := congrFun (congrFun hK₀ 1) 0
    rw [Matrix.mul_apply, Fin.sum_univ_one] at e
    simpa using e
  have hc0 : V 0 0 0 = c := by simp [hV₀]
  have hs0 : V 0 1 0 = s := by simp [hV₀]
  have hS0 : S 0 0 0 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h00
    norm_num at h00
  have hU00 : U 0 0 0 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h00
    norm_num at h00
  have hρ0 : U 0 1 0 / U 0 0 0 = 4 / 3 := by
    rw [div_eq_iff hU00]
    have h1 : (U 0 1 0 - 4 / 3 * U 0 0 0) * S 0 0 0 = 0 := by
      linear_combination h10 - 4 / 3 * h00
    have h2 := (mul_eq_zero.1 h1).resolve_right hS0
    linarith
  have hp0 : U 0 0 0 * S 0 0 0 * V 0 0 0 = 3 / 5 * c := by rw [h00, hc0]
  have ht0 : V 0 1 0 / V 0 0 0 = s / c := by rw [hc0, hs0]
  have hVorth : ∀ k ≤ n, V k 0 0 ^ 2 + V k 1 0 ^ 2 = 1 := by
    intro k hk
    cases k with
    | zero =>
      rw [hc0, hs0]
      exact hcs
    | succ j => exact sq_add_sq_of_orth (hstep j (Nat.lt_of_succ_le hk)).orthV₁
  have inv := seq_bounds hh hlam (n := n) (p := fun k => U k 0 0 * S k 0 0 * V k 0 0)
    (ρ := fun k => U k 1 0 / U k 0 0) (t := fun k => V k 1 0 / V k 0 0)
    (a := fun k => h * lam * V k 1 0 ^ 2)
    (by
      show 0 < U 0 0 0 * S 0 0 0 * V 0 0 0
      rw [hp0]
      linarith)
    hρ0
    (fun k => by
      show 0 ≤ h * lam * V k 1 0 ^ 2
      positivity)
    (fun k hk hpk => by
      show h * lam * V k 1 0 ^ 2 ≤ h * lam * (V k 1 0 / V k 0 0) ^ 2
      have hpk' : 0 < U k 0 0 * S k 0 0 * V k 0 0 := hpk
      have hck : V k 0 0 ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hpk'
        exact lt_irrefl _ hpk'
      have ho := hVorth k hk
      have h1 : V k 1 0 ^ 2 ≤ (V k 1 0 / V k 0 0) ^ 2 := by
        rw [div_pow, le_div_iff₀ (by positivity)]
        have h2 : V k 1 0 ^ 2 * V k 0 0 ^ 2 = V k 1 0 ^ 2 - V k 1 0 ^ 2 * V k 1 0 ^ 2 := by
          linear_combination V k 1 0 ^ 2 * ho
        have h3 := mul_nonneg (sq_nonneg (V k 1 0)) (sq_nonneg (V k 1 0))
        linarith
      exact mul_le_mul_of_nonneg_left h1 (by positivity))
    (fun k hk hpk => step_facts hh hh1 hlam (hstep k hk) hpk)
    n le_rfl
  obtain ⟨hpn, hpn0, hJ, htn, hρl, hρu, hδ⟩ := inv
  rw [hp0] at hpn0 hJ
  rw [ht0] at hJ htn hδ
  have he : 2 - 2 * c ≤ ‖uᵣ * !![c; s]ᵀ - !![3 / 5, 0; 4 / 5, 0]‖ ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecHead, Function.swap]
    nlinarith [hcs]
  obtain ⟨hc1, hT3, hT4, h1c⟩ := start_bounds hc hcs (norm_nonneg _) he
  have hb0 : 0 ≤ h * lam * V n 1 0 ^ 2 / (1 + h * lam * V n 1 0 ^ 2) := by positivity
  have g1 := mul_nonneg hh.le (sq_nonneg (V n 1 0 / V n 0 0))
  have g2 := mul_nonneg hh.le hb0
  have hpl : 3 / 5 * c * (1 - 16 / 9 * h - 25 / 9 * h * (s / c) ^ 2) ≤
      U n 0 0 * S n 0 0 * V n 0 0 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) hJ
    linarith
  have hρd : U n 1 0 / U n 0 0 - 4 / 3 * Real.exp (-(n * h)) ≤
      4 / 3 * (h + h * (s / c) ^ 2 + n * h * h) := by
    have h3 : (n : ℝ) * h ^ 2 = n * h * h := by ring
    linarith
  have key := err_bound hh (mul_nonneg (Nat.cast_nonneg n) hh.le) hc1 (norm_nonneg _)
    (sq_nonneg (s / c)) hT3 hT4 h1c (Real.exp_pos _).le hpn hpn0 hpl htn hρl hρu hρd
  have hα : U n 0 0 ≠ 0 := by
    intro h0
    rw [h0] at hpn
    simp at hpn
  have hcn : V n 0 0 ≠ 0 := by
    intro h0
    rw [h0] at hpn
    simp at hpn
  have e1 : U n 1 0 = U n 1 0 / U n 0 0 * U n 0 0 := (div_mul_cancel₀ _ hα).symm
  have e2 : V n 1 0 = V n 1 0 / V n 0 0 * V n 0 0 := (div_mul_cancel₀ _ hcn).symm
  have f1 : U n 0 0 * S n 0 0 * V n 1 0 =
      V n 1 0 / V n 0 0 * (U n 0 0 * S n 0 0 * V n 0 0) := by
    calc U n 0 0 * S n 0 0 * V n 1 0
        = U n 0 0 * S n 0 0 * (V n 1 0 / V n 0 0 * V n 0 0) := by rw [← e2]
      _ = V n 1 0 / V n 0 0 * (U n 0 0 * S n 0 0 * V n 0 0) := by ring
  have f2 : U n 1 0 * S n 0 0 * V n 0 0 =
      U n 1 0 / U n 0 0 * (U n 0 0 * S n 0 0 * V n 0 0) := by
    calc U n 1 0 * S n 0 0 * V n 0 0
        = U n 1 0 / U n 0 0 * U n 0 0 * S n 0 0 * V n 0 0 := by rw [← e1]
      _ = U n 1 0 / U n 0 0 * (U n 0 0 * S n 0 0 * V n 0 0) := by ring
  have f3 : U n 1 0 * S n 0 0 * V n 1 0 =
      U n 1 0 / U n 0 0 * (V n 1 0 / V n 0 0) * (U n 0 0 * S n 0 0 * V n 0 0) := by
    calc U n 1 0 * S n 0 0 * V n 1 0
        = U n 1 0 / U n 0 0 * U n 0 0 * S n 0 0 * (V n 1 0 / V n 0 0 * V n 0 0) := by
          rw [← e1, ← e2]
      _ = U n 1 0 / U n 0 0 * (V n 1 0 / V n 0 0) * (U n 0 0 * S n 0 0 * V n 0 0) := by ring
  have l00 : (!![3 / 5, 0; 4 / 5 * Real.exp (-(n * h)), 0] : Matrix (Fin 2) (Fin 2) ℝ) 0 0 =
      3 / 5 := rfl
  have l01 : (!![3 / 5, 0; 4 / 5 * Real.exp (-(n * h)), 0] : Matrix (Fin 2) (Fin 2) ℝ) 0 1 =
      0 := rfl
  have l10 : (!![3 / 5, 0; 4 / 5 * Real.exp (-(n * h)), 0] : Matrix (Fin 2) (Fin 2) ℝ) 1 0 =
      4 / 5 * Real.exp (-(n * h)) := rfl
  have l11 : (!![3 / 5, 0; 4 / 5 * Real.exp (-(n * h)), 0] : Matrix (Fin 2) (Fin 2) ℝ) 1 1 =
      0 := rfl
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [Frobenius.norm_sq_eq_sum, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Matrix.sub_apply, factor_apply, l00, l01, l10, l11, sub_zero]
  rw [f1, f2, f3]
  exact key

/-- The hypotheses of `norm_run_sub_le` hold for runs of one step: a step exists for every
`h`, `lam` and start value, and its result is within `4 ‖Y₀ - X(0)‖ + 18 (1 + h) h` of the
solution, for every `lam`. -/
example {h lam c s : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hlam : 0 ≤ lam) (hc : 1 / 2 ≤ c)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ Y₁ : Matrix (Fin 2) (Fin 2) ℝ,
      ‖Y₁ - !![3 / 5, 0; 4 / 5 * Real.exp (-h), 0]‖ ≤
        4 * ‖uᵣ * !![c; s]ᵀ - !![3 / 5, 0; 4 / 5, 0]‖ + 18 * (1 + h) * h := by
  obtain ⟨K₁, L₁, U₁, V₁, S₁, Y₁, ε, hs⟩ := exists_isMatrixImplicitBUGStep hh.le hlam hcs 0
  have key := norm_run_sub_le hh hh1 hlam hc hcs (n := 1) (ε := fun _ => ε) (t := fun _ => 0)
    (U := fun k => if k = 0 then uᵣ else U₁) (K := fun _ => K₁) (L := fun _ => L₁)
    (V := fun k => if k = 0 then !![c; s] else V₁) (S := fun k => if k = 0 then 1 else S₁)
    (Y := fun _ => Y₁)
    (by
      intro k hk
      obtain rfl : k = 0 := by omega
      simpa using hs)
    (by simp) (by simp)
  refine ⟨U₁ * S₁ * V₁ᵀ, ?_⟩
  simpa using key

end StiffRowsExample

end LeanDLRA
