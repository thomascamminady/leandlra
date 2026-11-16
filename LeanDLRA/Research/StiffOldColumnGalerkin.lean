import LeanDLRA.Research.StiffEnergyGalerkin
import LeanDLRA.Foundations.OneSided

/-!
# Stiff problems: the Galerkin step when the old column space is invariant

For a stiff linear equation with forcing, `Y' = 𝓛 Y + g(t)`, with a dissipative operator `𝓛`,
this file bounds the error of one step of the rank-adaptive BUG integrator, and of a sequence
of steps, when the projector `P₀` onto the old column space commutes with `𝓛`. This is the case
for `𝓛 Y = Y N` with a symmetric negative semidefinite matrix `N` and every `P₀ Y = U₀ U₀ᵀ Y`.
The bound contains neither the norm of `𝓛` nor a coupling number, and no quantity of the exact
solution. It consists of two numbers of the step and one number of the forcing:

* `‖P₀ Ŷ₁ - Y_L(t₁)‖`, the difference on the old columns between the result of the Galerkin
  step and the result of the L-step;
* `‖Ŷ₁ - P₀ Ŷ₁‖`, the part of the Galerkin result on the columns added in the step;
* `β`, a bound for the part `g - P₀ g` of the forcing outside the old column space.

The reason is that the equation splits along `P₀`: the L-step is the exact flow of the part
`P₀ A` of a solution, and the part `A - P₀ A` is driven by `g - P₀ g` alone.

## Main results

* `IsRankAdaptiveBUGStep.norm_sub_left_galerkin_le`: the Galerkin result has at most the
  norm `β (t₁ - t₀)` outside the old column space.
* `IsRankAdaptiveBUGStep.stiff_error_of_comm_left`: for one step,
  `‖Y₁ - A(t₁)‖ ≤ ‖Y₀ - A(t₀)‖ + ‖P₀ Ŷ₁ - Y_L(t₁)‖ + ‖Ŷ₁ - P₀ Ŷ₁‖ + β (t₁ - t₀) + ϑ`.
* `IsRankAdaptiveBUGStep.stiff_error_of_comm_left_le`: the same with `2 β (t₁ - t₀)` in place
  of the third and fourth term.
* `IsRankAdaptiveBUGStep.augLeft_apply_right_forcing`,
  `IsRankAdaptiveBUGStep.norm_forcing_sub_augLeft_le`: if the forcing is constant on the step
  and `P₁` commutes with a symmetric `𝓛` and with `Q₀`, then `P₁ Q₀ g = Q₀ g` and
  `‖g - P₁ g‖ ≤ ε`.
* `stiff_global_error_of_comm_left`: for `N` steps on an arbitrary grid,
  `‖Y_N - A(τ_N)‖ ≤ ‖Y₀ - A(τ₀)‖ + ∑ₙ (ωₙ + 2 βₙ (τₙ₊₁ - τₙ) + ϑₙ)` with
  `ωₙ = ‖Pₙ Ŷₙ₊₁ - Y_{L,n}(τₙ₊₁)‖`.

## Remarks on the hypotheses

* The forcing is an arbitrary function of time. If it is constant on the steps and the column
  space after a step contains the columns added in it, then `βₙ` is at most the jump of the
  forcing at `τₙ` plus the part of the old forcing outside the augmented column space, so that
  `∑ₙ βₙ (τₙ₊₁ - τₙ)` is bounded by the step size times the variation of the forcing plus the
  usual normal parts. Of this, `IsRankAdaptiveBUGStep.norm_forcing_sub_augLeft_le` proves the
  bound for the old forcing outside the augmented column space; the sum is not formed here.
* No bound for the numbers `ωₙ` in terms of the data is proved here. In particular the file
  does not show that the global error is small for a forcing of bounded variation; it reduces
  that question, for operators that commute with the old column projectors, to a bound for
  `∑ₙ ωₙ`.
* The operator `𝓛` need not be symmetric. The projector `P₀` has to commute with `𝓛` and
  with the two augmented projectors, and the starting value has to lie in its range; `P₁` and
  `Q₁` need not commute with `𝓛`.
* For the step of `StiffCouplingExample` the bound is attained for every stiffness `λ` (the
  `example` at the end of the file).

## Relation to the literature

The integrator is the one of [CerutiKuschLubich2022]. For the energy bound with the exact
solution outside the Galerkin space see `IsRankAdaptiveBUGStep.stiff_energy_error`.
-/

open Set
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Growth of a forced dissipative equation.** If `x' = T (𝓛 x) + d(t)` with `‖d(t)‖ ≤ β`
and `⟪T (𝓛 x), x⟫ ≤ 0` along the trajectory, then `‖x(t)‖ ≤ ‖x(a)‖ + β (t - a)`. -/
lemma norm_le_add_mul_of_dissipative_forced {T 𝓛 : E →L[ℝ] E} {x u : ℝ → E} {a b β : ℝ}
    (hxc : ContinuousOn x (Icc a b)) (hx : ∀ t ∈ Ico a b, HasDerivWithinAt x (u t) (Ici t) t)
    (hdiss : ∀ t ∈ Ico a b, ⟪T (𝓛 (x t)), x t⟫ ≤ 0)
    (hd : ∀ t ∈ Ico a b, ‖u t - T (𝓛 (x t))‖ ≤ β) :
    ∀ t ∈ Icc a b, ‖x t‖ ≤ ‖x a‖ + β * (t - a) := by
  intro t ht
  have h := norm_sub_le_gronwallBound_of_inner_le (F := fun _ y => T (𝓛 y)) (ℓ := 0)
    (y := x) (z := fun _ => 0) (u := u) (w := fun _ => 0) (ηy := β) (ηz := 0)
    (δ := ‖x a‖) (a := a) (b := b)
    (fun s hs => by simpa using hdiss s hs) hxc hx hd continuousOn_const
    (fun s _ => hasDerivWithinAt_const s (Ici s) (0 : E)) (fun s _ => by simp) (by simp) t ht
  simpa [gronwallBound_K0] using h

namespace IsRankAdaptiveBUGStep

variable {F : ℝ → E → E} {g : ℝ → E} {𝓛 P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {ε ϑ β : ℝ}
  {A YK YL YS : ℝ → E} {Y₀ Y₁ : E} {t₀ t₁ : ℝ}

/-- **The Galerkin result outside the old column space.** Let `F(t, x) = 𝓛 x + g(t)` with a
dissipative operator `𝓛`, and let the old left projector `P₀` commute with `𝓛` and with the
augmented projectors. If the starting value lies in the range of `P₀` and the part of the
forcing outside this range is at most `β` on the step, then the Galerkin step moves at most
`β (t₁ - t₀)` out of the range of `P₀`. -/
theorem norm_sub_left_galerkin_le
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hsplit : ∀ t x, F t x = 𝓛 x + g t) (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hP𝓛 : ∀ x, P₀ (𝓛 x) = 𝓛 (P₀ x)) (hPP : ∀ x, P₀ (P₁ x) = P₁ (P₀ x))
    (hPQ : ∀ x, P₀ (Q₁ x) = Q₁ (P₀ x)) (hY₀ : P₀ Y₀ = Y₀) (hle : t₀ ≤ t₁)
    (hβ : ∀ t ∈ Ico t₀ t₁, ‖g t - P₀ (g t)‖ ≤ β) :
    ‖YS t₁ - P₀ (YS t₁)‖ ≤ β * (t₁ - t₀) := by
  have hR := hs.galerkinProj
  have hmem : ∀ t ∈ Icc t₀ t₁, P₁ (Q₁ (YS t)) = YS t := hs.mem_range
  have hRx : ∀ t ∈ Icc t₀ t₁, P₁ (Q₁ (YS t - P₀ (YS t))) = YS t - P₀ (YS t) := by
    intro t ht
    rw [map_sub, map_sub, ← hPQ, ← hPP, hmem t ht]
  have hcont : ContinuousOn (fun t => YS t - P₀ (YS t)) (Icc t₀ t₁) :=
    hs.sSol.cont.sub (P₀.continuous.comp_continuousOn hs.sSol.cont)
  have hderiv : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => YS t - P₀ (YS t))
      (P₁ (Q₁ (F t (YS t))) - P₀ (P₁ (Q₁ (F t (YS t))))) (Ici t) t := fun t ht =>
    (hs.sSol.deriv t ht).sub (P₀.hasFDerivAt.comp_hasDerivWithinAt t (hs.sSol.deriv t ht))
  have h := norm_le_add_mul_of_dissipative_forced (T := P₁ * Q₁) (𝓛 := 𝓛) (β := β) hcont hderiv
    (fun t ht => by
      have hx := hRx t (Ico_subset_Icc_self ht)
      change ⟪P₁ (Q₁ (𝓛 (YS t - P₀ (YS t)))), YS t - P₀ (YS t)⟫ ≤ 0
      have e : ⟪P₁ (Q₁ (𝓛 (YS t - P₀ (YS t)))), YS t - P₀ (YS t)⟫
          = ⟪𝓛 (YS t - P₀ (YS t)), YS t - P₀ (YS t)⟫ := by
        have := hR.symm (𝓛 (YS t - P₀ (YS t))) (YS t - P₀ (YS t))
        change ⟪P₁ (Q₁ (𝓛 (YS t - P₀ (YS t)))), YS t - P₀ (YS t)⟫
          = ⟪𝓛 (YS t - P₀ (YS t)), P₁ (Q₁ (YS t - P₀ (YS t)))⟫ at this
        rw [this, hx]
      rw [e]
      exact hdiss _)
    (fun t ht => by
      have e : P₁ (Q₁ (F t (YS t))) - P₀ (P₁ (Q₁ (F t (YS t))))
          - (P₁ * Q₁) (𝓛 (YS t - P₀ (YS t))) = (P₁ * Q₁) (g t - P₀ (g t)) := by
        change P₁ (Q₁ (F t (YS t))) - P₀ (P₁ (Q₁ (F t (YS t))))
          - P₁ (Q₁ (𝓛 (YS t - P₀ (YS t)))) = P₁ (Q₁ (g t - P₀ (g t)))
        rw [hPP, hPQ, hsplit]
        simp only [map_sub, map_add, hP𝓛]
        abel
      rw [e]
      exact (hR.norm_le _).trans (hβ t ht))
    t₁ ⟨hle, le_rfl⟩
  have h0 : YS t₀ - P₀ (YS t₀) = 0 := by rw [hs.start_eq, hY₀, sub_self]
  rw [h0, norm_zero, zero_add] at h
  exact h

/-- **Error of one rank-adaptive BUG step when the old column space is invariant.** Let
`F(t, x) = 𝓛 x + g(t)` with a dissipative operator `𝓛`, let the old left projector `P₀` commute
with `𝓛` and with the augmented projectors, and let the starting value lie in the range of
`P₀`. If `A` is an exact solution on the step, not necessarily with `A(t₀) = Y₀`, and the part
of the forcing outside the range of `P₀` is at most `β` on the step, then

`‖Y₁ - A(t₁)‖ ≤ ‖Y₀ - A(t₀)‖ + ‖P₀ Ŷ₁ - Y_L(t₁)‖ + ‖Ŷ₁ - P₀ Ŷ₁‖ + β (t₁ - t₀) + ϑ`

with the Galerkin result `Ŷ₁ = YS t₁`, the result `Y_L(t₁)` of the L-step and the truncation
tolerance `ϑ`. The error at the start enters with the factor one. -/
theorem stiff_error_of_comm_left
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hsplit : ∀ t x, F t x = 𝓛 x + g t) (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hP𝓛 : ∀ x, P₀ (𝓛 x) = 𝓛 (P₀ x)) (hY₀ : P₀ Y₀ = Y₀) (hle : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁) (hβ : ∀ t ∈ Ico t₀ t₁, ‖g t - P₀ (g t)‖ ≤ β) :
    ‖Y₁ - A t₁‖ ≤ ‖Y₀ - A t₀‖ + ‖P₀ (YS t₁) - YL t₁‖ + ‖YS t₁ - P₀ (YS t₁)‖
      + β * (t₁ - t₀) + ϑ := by
  have hP := hs.projP₀
  have ht₁ : t₁ ∈ Icc t₀ t₁ := ⟨hle, le_rfl⟩
  have hYL : ∀ t ∈ Icc t₀ t₁, P₀ (YL t) = YL t :=
    hs.lSol.galerkin_mem_range hP (by rw [hs.lStart]; exact hY₀)
  -- the L-step against the part of the exact solution in the old column space
  have h1 : ‖YL t₁ - P₀ (A t₁)‖ ≤ ‖P₀ (Y₀ - A t₀)‖ := by
    have h := norm_le_add_mul_of_dissipative_forced (T := 1) (𝓛 := 𝓛) (β := 0)
      (x := fun t => YL t - P₀ (A t))
      (u := fun t => P₀ (F t (YL t)) - P₀ (F t (A t)))
      (hs.lSol.cont.sub (P₀.continuous.comp_continuousOn hA.cont))
      (fun t ht => (hs.lSol.deriv t ht).sub
        (P₀.hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht)))
      (fun t _ => hdiss _)
      (fun t ht => by
        have e : P₀ (F t (YL t)) - P₀ (F t (A t))
            - (1 : E →L[ℝ] E) (𝓛 (YL t - P₀ (A t))) = 0 := by
          change P₀ (F t (YL t)) - P₀ (F t (A t)) - 𝓛 (YL t - P₀ (A t)) = 0
          rw [hsplit, hsplit]
          simp only [map_sub, map_add, hP𝓛, hYL t (Ico_subset_Icc_self ht)]
          abel
        rw [e, norm_zero])
      t₁ ht₁
    have e0 : YL t₀ - P₀ (A t₀) = P₀ (Y₀ - A t₀) := by rw [hs.lStart, map_sub, hY₀]
    simpa [e0] using h
  -- the part of the exact solution outside the old column space
  have h2 : ‖A t₁ - P₀ (A t₁)‖ ≤ ‖(Y₀ - A t₀) - P₀ (Y₀ - A t₀)‖ + β * (t₁ - t₀) := by
    have h := norm_le_add_mul_of_dissipative_forced (T := 1) (𝓛 := 𝓛) (β := β)
      (x := fun t => A t - P₀ (A t))
      (u := fun t => F t (A t) - P₀ (F t (A t)))
      (hA.cont.sub (P₀.continuous.comp_continuousOn hA.cont))
      (fun t ht => (hA.deriv t ht).sub
        (P₀.hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht)))
      (fun t _ => hdiss _)
      (fun t ht => by
        have e : F t (A t) - P₀ (F t (A t)) - (1 : E →L[ℝ] E) (𝓛 (A t - P₀ (A t)))
            = g t - P₀ (g t) := by
          change F t (A t) - P₀ (F t (A t)) - 𝓛 (A t - P₀ (A t)) = g t - P₀ (g t)
          rw [hsplit]
          simp only [map_sub, map_add, hP𝓛]
          abel
        rw [e]
        exact hβ t ht)
      t₁ ht₁
    have e0 : (Y₀ - A t₀) - P₀ (Y₀ - A t₀) = -(A t₀ - P₀ (A t₀)) := by
      rw [map_sub, hY₀]
      abel
    rw [e0, norm_neg]
    exact h
  -- the two parts of the error of the Galerkin result
  have h3 : ‖P₀ (YS t₁ - A t₁)‖ ≤ ‖P₀ (YS t₁) - YL t₁‖ + ‖P₀ (Y₀ - A t₀)‖ := by
    have e : P₀ (YS t₁ - A t₁) = (P₀ (YS t₁) - YL t₁) + (YL t₁ - P₀ (A t₁)) := by
      rw [map_sub]
      abel
    rw [e]
    exact (norm_add_le _ _).trans (by linarith)
  have h4 : ‖(YS t₁ - A t₁) - P₀ (YS t₁ - A t₁)‖
      ≤ ‖YS t₁ - P₀ (YS t₁)‖ + β * (t₁ - t₀) + ‖(Y₀ - A t₀) - P₀ (Y₀ - A t₀)‖ := by
    have e : (YS t₁ - A t₁) - P₀ (YS t₁ - A t₁)
        = (YS t₁ - P₀ (YS t₁)) - (A t₁ - P₀ (A t₁)) := by
      rw [map_sub]
      abel
    rw [e]
    exact (_root_.norm_sub_le _ _).trans (by linarith)
  have hβh : 0 ≤ β * (t₁ - t₀) := by
    rcases hle.eq_or_lt with h | h
    · rw [h, sub_self, mul_zero]
    · exact mul_nonneg ((norm_nonneg _).trans (hβ t₀ ⟨le_rfl, h⟩)) (sub_nonneg.2 hle)
  have hsq1 := hP.norm_sq_add (YS t₁ - A t₁)
  have hsq0 := hP.norm_sq_add (Y₀ - A t₀)
  have hp := norm_nonneg (P₀ (Y₀ - A t₀))
  have hq := norm_nonneg ((Y₀ - A t₀) - P₀ (Y₀ - A t₀))
  have hn := norm_nonneg (Y₀ - A t₀)
  have hω := norm_nonneg (P₀ (YS t₁) - YL t₁)
  have hν := norm_nonneg (YS t₁ - P₀ (YS t₁))
  have hpn : ‖P₀ (Y₀ - A t₀)‖ ≤ ‖Y₀ - A t₀‖ := hP.norm_le _
  have hqn : ‖(Y₀ - A t₀) - P₀ (Y₀ - A t₀)‖ ≤ ‖Y₀ - A t₀‖ := hP.norm_sub_le _
  have h5 : ‖YS t₁ - A t₁‖ ≤ ‖Y₀ - A t₀‖ + ‖P₀ (YS t₁) - YL t₁‖ + ‖YS t₁ - P₀ (YS t₁)‖
      + β * (t₁ - t₀) := by
    have hc : 0 ≤ ‖YS t₁ - P₀ (YS t₁)‖ + β * (t₁ - t₀) := by linarith
    refine abs_le_of_sq_le_sq' ?_ (by linarith) |>.2
    have ha := norm_nonneg (P₀ (YS t₁ - A t₁))
    have hb := norm_nonneg ((YS t₁ - A t₁) - P₀ (YS t₁ - A t₁))
    have ha2 : ‖P₀ (YS t₁ - A t₁)‖ ^ 2
        ≤ (‖P₀ (YS t₁) - YL t₁‖ + ‖P₀ (Y₀ - A t₀)‖) ^ 2 :=
      pow_le_pow_left₀ ha h3 2
    have hb2 : ‖(YS t₁ - A t₁) - P₀ (YS t₁ - A t₁)‖ ^ 2
        ≤ (‖YS t₁ - P₀ (YS t₁)‖ + β * (t₁ - t₀) + ‖(Y₀ - A t₀) - P₀ (Y₀ - A t₀)‖) ^ 2 :=
      pow_le_pow_left₀ hb h4 2
    nlinarith [mul_nonneg hω (sub_nonneg.2 hpn), mul_nonneg hc (sub_nonneg.2 hqn),
      mul_nonneg hω hc, mul_nonneg hω hn, mul_nonneg hc hn]
  have e : Y₁ - A t₁ = (Y₁ - YS t₁) + (YS t₁ - A t₁) := by abel
  rw [e]
  have h6 := norm_add_le (Y₁ - YS t₁) (YS t₁ - A t₁)
  have h7 := hs.trunc
  linarith

/-- **Error of one rank-adaptive BUG step when the old column space is invariant**, with the
part of the Galerkin result on the added columns bounded by the forcing: under the hypotheses of
`stiff_error_of_comm_left` and if `P₀` commutes with the augmented projectors,

`‖Y₁ - A(t₁)‖ ≤ ‖Y₀ - A(t₀)‖ + ‖P₀ Ŷ₁ - Y_L(t₁)‖ + 2 β (t₁ - t₀) + ϑ`. -/
theorem stiff_error_of_comm_left_le
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hsplit : ∀ t x, F t x = 𝓛 x + g t) (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hP𝓛 : ∀ x, P₀ (𝓛 x) = 𝓛 (P₀ x)) (hPP : ∀ x, P₀ (P₁ x) = P₁ (P₀ x))
    (hPQ : ∀ x, P₀ (Q₁ x) = Q₁ (P₀ x)) (hY₀ : P₀ Y₀ = Y₀) (hle : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁) (hβ : ∀ t ∈ Ico t₀ t₁, ‖g t - P₀ (g t)‖ ≤ β) :
    ‖Y₁ - A t₁‖ ≤ ‖Y₀ - A t₀‖ + ‖P₀ (YS t₁) - YL t₁‖ + 2 * β * (t₁ - t₀) + ϑ := by
  have h1 := hs.stiff_error_of_comm_left hsplit hdiss hP𝓛 hY₀ hle hA hβ
  have h2 := hs.norm_sub_left_galerkin_le hsplit hdiss hP𝓛 hPP hPQ hY₀ hle hβ
  linarith

/-- **The K-step captures a constant forcing in the old row space.** Let `F(t, x) = 𝓛 x + c`
with a symmetric operator `𝓛` and a forcing `c` that is constant on the step, and let the
augmented left projector `P₁` commute with `𝓛` and with the old right projector `Q₀`. Then the
part `Q₀ c` of the forcing lies in the range of `P₁`. No bound for `𝓛` and no sign condition
is needed. -/
theorem augLeft_apply_right_forcing {c : E}
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hsplit : ∀ t x, F t x = 𝓛 x + c) (hsym : ∀ x y, ⟪𝓛 x, y⟫ = ⟪x, 𝓛 y⟫)
    (hP𝓛 : ∀ x, P₁ (𝓛 x) = 𝓛 (P₁ x)) (hPQ : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (hlt : t₀ < t₁) :
    P₁ (Q₀ c) = Q₀ c := by
  have hQ := hs.projQ₀
  obtain ⟨x, hx⟩ : ∃ x : ℝ → E, x = fun t => YK t - P₁ (YK t) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : E, d = Q₀ c - P₁ (Q₀ c) := ⟨_, rfl⟩
  have hxc : ContinuousOn x (Icc t₀ t₁) := by
    rw [hx]
    exact hs.kSol.cont.sub (P₁.continuous.comp_continuousOn hs.kSol.cont)
  have hv : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt x (Q₀ (𝓛 (x t)) + d) (Ici t) t := by
    intro t ht
    have h := (hs.kSol.deriv t ht).sub
      (P₁.hasFDerivAt.comp_hasDerivWithinAt t (hs.kSol.deriv t ht))
    have e : Q₀ (F t (YK t)) - P₁ (Q₀ (F t (YK t))) = Q₀ (𝓛 (x t)) + d := by
      rw [hsplit, hx, hd]
      simp only [map_sub, map_add, hPQ, hP𝓛]
      abel
    rw [← e, hx]
    exact h
  have hQd : Q₀ d = d := by
    rw [hd, map_sub, hQ.idem, ← hPQ, hQ.idem]
  have hQv : ∀ t, Q₀ (Q₀ (𝓛 (x t)) + d) = Q₀ (𝓛 (x t)) + d := fun t => by
    rw [map_add, hQ.idem, hQd]
  have hf : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt
      (fun s => -(1 / 2 : ℝ) * ⟪𝓛 (x s), x s⟫ - ⟪d, x s⟫)
      (-‖Q₀ (𝓛 (x t)) + d‖ ^ 2) (Ici t) t := by
    intro t ht
    have h1 := hv t ht
    have h2 : HasDerivWithinAt (fun s => 𝓛 (x s)) (𝓛 (Q₀ (𝓛 (x t)) + d)) (Ici t) t :=
      𝓛.hasFDerivAt.comp_hasDerivWithinAt t h1
    have h3 := h2.inner ℝ h1
    have h4 := (hasDerivWithinAt_const t (Ici t) d).inner ℝ h1
    refine ((h3.const_mul (-(1 / 2 : ℝ))).sub h4).congr_deriv ?_
    have e1 : ⟪𝓛 (Q₀ (𝓛 (x t)) + d), x t⟫ = ⟪𝓛 (x t), Q₀ (𝓛 (x t)) + d⟫ := by
      rw [hsym, real_inner_comm]
    have e2 : ‖Q₀ (𝓛 (x t)) + d‖ ^ 2
        = ⟪𝓛 (x t), Q₀ (𝓛 (x t)) + d⟫ + ⟪d, Q₀ (𝓛 (x t)) + d⟫ := by
      rw [← real_inner_self_eq_norm_sq]
      nth_rewrite 1 [inner_add_left]
      rw [hQ.symm, hQv]
    rw [e1, inner_zero_left, e2]
    ring
  have hfc : ContinuousOn (fun s => -(1 / 2 : ℝ) * ⟪𝓛 (x s), x s⟫ - ⟪d, x s⟫)
      (Icc t₀ t₁) :=
    (continuousOn_const.mul ((𝓛.continuous.comp_continuousOn hxc).inner hxc)).sub
      (continuousOn_const.inner hxc)
  have hx0 : x t₀ = 0 := by rw [hx]; simp only; rw [hs.kStart, hs.augP, sub_self]
  have hx1 : x t₁ = 0 := by rw [hx]; simp only; rw [hs.kCap, sub_self]
  have hzero : ∀ t ∈ Icc t₀ t₁, -(1 / 2 : ℝ) * ⟪𝓛 (x t), x t⟫ - ⟪d, x t⟫ = 0 := by
    intro t ht
    have hup := image_le_of_deriv_right_le_deriv_boundary hfc hf
      (B := fun _ => (0 : ℝ)) (B' := fun _ => 0) (by simp [hx0]) continuousOn_const
      (fun s _ => hasDerivWithinAt_const s (Ici s) (0 : ℝ))
      (fun s _ => neg_nonpos.2 (sq_nonneg _)) ht
    have hlow := image_le_of_deriv_right_le_deriv_boundary
      (hfc.mono (Icc_subset_Icc_left ht.1))
      (fun s hs' => hf s ⟨ht.1.trans hs'.1, hs'.2⟩)
      (B := fun _ => -(1 / 2 : ℝ) * ⟪𝓛 (x t), x t⟫ - ⟪d, x t⟫) (B' := fun _ => 0) le_rfl
      continuousOn_const (fun s _ => hasDerivWithinAt_const s (Ici s) _)
      (fun s _ => neg_nonpos.2 (sq_nonneg _)) (show t₁ ∈ Icc t t₁ from ⟨ht.2, le_rfl⟩)
    simp only [hx1, map_zero, inner_zero_right, mul_zero, sub_zero] at hlow
    exact le_antisymm hup hlow
  have hmem : t₀ ∈ Icc t₀ t₁ := ⟨le_rfl, hlt.le⟩
  have hd0 : HasDerivWithinAt (fun s => -(1 / 2 : ℝ) * ⟪𝓛 (x s), x s⟫ - ⟪d, x s⟫) 0
      (Icc t₀ t₁) t₀ :=
    (hasDerivWithinAt_const t₀ (Icc t₀ t₁) (0 : ℝ)).congr hzero (hzero t₀ hmem)
  have hd1 := (hf t₀ ⟨le_rfl, hlt⟩).mono (Icc_subset_Ici_self : Icc t₀ t₁ ⊆ Ici t₀)
  have h0 := (uniqueDiffOn_Icc hlt t₀ hmem).eq_deriv _ hd1 hd0
  rw [hx0, map_zero, map_zero, zero_add] at h0
  have hd' : d = 0 := by
    have : ‖d‖ ^ 2 = 0 := by linarith
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 this)
  rw [hd] at hd'
  exact (sub_eq_zero.1 hd').symm

/-- **A constant forcing outside the augmented column space is a normal part.** Under the
hypotheses of `augLeft_apply_right_forcing`, the part of the forcing outside the range of the
augmented left projector is at most the bound `ε` for the normal part at the result of the
K-step. -/
theorem norm_forcing_sub_augLeft_le {c : E}
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hsplit : ∀ t x, F t x = 𝓛 x + c) (hsym : ∀ x y, ⟪𝓛 x, y⟫ = ⟪x, 𝓛 y⟫)
    (hP𝓛 : ∀ x, P₁ (𝓛 x) = 𝓛 (P₁ x)) (hPQ : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (hlt : t₀ < t₁) :
    ‖c - P₁ c‖ ≤ ε := by
  have h1 : Q₀ (P₁ c) = Q₀ c :=
    (hPQ c).symm.trans (hs.augLeft_apply_right_forcing hsplit hsym hP𝓛 hPQ hlt)
  have h2 := hs.kNormal t₀ ⟨le_rfl, hlt.le⟩
  have e : (1 - P₁) ((1 - Q₀) (F t₀ (YK t₁))) = c - P₁ c := by
    rw [hsplit]
    simp only [sub_apply, one_apply_eq_self, map_sub, map_add, hPQ, hP𝓛, hs.kCap, h1]
    abel
  rw [e] at h2
  exact h2

end IsRankAdaptiveBUGStep

/-- **Global error of the rank-adaptive BUG integrator when the old column spaces are
invariant.** Let `F(t, x) = 𝓛 x + g(t)` with a dissipative operator `𝓛` and let `A` be an exact
solution on every step of a grid `τ₀ ≤ τ₁ ≤ … ≤ τ_N`. If in every step the old left projector
`Pₙ` commutes with `𝓛` and with the augmented projectors, `Yₙ` lies in its range, and the part
of the forcing outside this range is at most `βₙ`, then

`‖Y_N - A(τ_N)‖ ≤ ‖Y₀ - A(τ₀)‖ + ∑ₙ (‖Pₙ Ŷₙ₊₁ - Y_{L,n}(τₙ₊₁)‖ + 2 βₙ (τₙ₊₁ - τₙ) + ϑₙ)`.

The right-hand side contains neither the norm of `𝓛` nor the exact solution after `τ₀`. -/
theorem stiff_global_error_of_comm_left {F : ℝ → E → E} {g : ℝ → E} {𝓛 : E →L[ℝ] E} {ε : ℝ}
    {ϑ β : ℕ → ℝ} {τ : ℕ → ℝ} {N : ℕ} {P Q Pa Qa : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YK YL YS : ℕ → ℝ → E} {A : ℝ → E}
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε (ϑ n) (P n) (Q n) (Pa n) (Qa n) (τ n)
      (τ (n + 1)) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hτ : ∀ n < N, τ n ≤ τ (n + 1)) (hsplit : ∀ t x, F t x = 𝓛 x + g t)
    (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0) (hP𝓛 : ∀ n < N, ∀ x, P n (𝓛 x) = 𝓛 (P n x))
    (hPP : ∀ n < N, ∀ x, P n (Pa n x) = Pa n (P n x))
    (hPQ : ∀ n < N, ∀ x, P n (Qa n x) = Qa n (P n x)) (hY : ∀ n < N, P n (Y n) = Y n)
    (hA : ∀ n < N, ODESolution F A (τ n) (τ (n + 1)))
    (hβ : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)), ‖g t - P n (g t)‖ ≤ β n) :
    ‖Y N - A (τ N)‖ ≤ ‖Y 0 - A (τ 0)‖
      + ∑ n ∈ Finset.range N, (‖P n (YS n (τ (n + 1))) - YL n (τ (n + 1))‖
        + 2 * β n * (τ (n + 1) - τ n) + ϑ n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN : N < N + 1 := Nat.lt_succ_self N
    have h1 := ih (fun n hn => hstep n (hn.trans hN)) (fun n hn => hτ n (hn.trans hN))
      (fun n hn => hP𝓛 n (hn.trans hN)) (fun n hn => hPP n (hn.trans hN))
      (fun n hn => hPQ n (hn.trans hN)) (fun n hn => hY n (hn.trans hN))
      (fun n hn => hA n (hn.trans hN)) (fun n hn => hβ n (hn.trans hN))
    have h2 := (hstep N hN).stiff_error_of_comm_left_le hsplit hdiss (hP𝓛 N hN) (hPP N hN)
      (hPQ N hN) (hY N hN) (hτ N hN) (hA N hN) (hβ N hN)
    rw [Finset.sum_range_succ]
    linarith

namespace StiffCouplingExample

open scoped Matrix LeanDLRA.Frobenius

/-- Non-vacuity of `IsRankAdaptiveBUGStep.stiff_error_of_comm_left_le` with nonzero data: for
the step `step` of the example, every stiffness `λ ≥ 0` and every `h ≥ 0`, the hypotheses hold
with `β = 4` (the forcing outside the old column space is `D - W`). The Galerkin result and
the result of the L-step agree, so the bound reads `‖Y₁ - A(h)‖ ≤ 8 h`, for every `λ`; by
`error_eq` the left-hand side equals `4 h`. -/
example {lam h : ℝ} (hlam : 0 ≤ lam) (hh : 0 ≤ h) :
    ‖(Y₀ + h • W) - (Y₀ + h • D)‖
      ≤ ‖Y₀ - (Y₀ + (0 : ℝ) • D)‖
        + ‖(leftProj U₀ : Matrix (Fin 2) (Fin 3) ℝ →L[ℝ] Matrix (Fin 2) (Fin 3) ℝ)
            (Y₀ + h • W) - (Y₀ + h • W)‖ + 2 * 4 * (h - 0) + 0 := by
  refine (step lam h).stiff_error_of_comm_left_le (g := fun _ => D - Y₀ * (lam • N₁))
    (𝓛 := stiffOp lam) (A := fun t => Y₀ + t • D) (fun _ _ => rfl)
    (stiffOp_dissipative hlam) (fun x => ?_) (fun _ => rfl)
    (fun x => leftProj_rightProj_comm U₀ Va x) U₀_mul_Y₀ hh (exactSol lam h) (fun t _ => ?_)
  · change U₀ * U₀ᵀ * (x * (lam • N₁)) = U₀ * U₀ᵀ * x * (lam • N₁)
    simp only [Matrix.mul_assoc]
  · have e : (D - Y₀ * (lam • N₁))
        - (leftProj U₀ : Matrix (Fin 2) (Fin 3) ℝ →L[ℝ] Matrix (Fin 2) (Fin 3) ℝ)
          (D - Y₀ * (lam • N₁)) = D - W := by
      change (D - Y₀ * (lam • N₁)) - U₀ * U₀ᵀ * (D - Y₀ * (lam • N₁)) = D - W
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, U₀_mul_Y₀, U₀_mul_D]
      abel
    rw [e, norm_D_sub_W]

/-- Non-vacuity of `IsRankAdaptiveBUGStep.norm_forcing_sub_augLeft_le`: for the step `step` of
the example and every stiffness `λ` the forcing outside the augmented column space is `D - W`,
of norm `4`, and the step has `ε = 4`. -/
example {lam h : ℝ} (hh : 0 < h) :
    ‖(D - Y₀ * (lam • N₁))
      - (leftProj U₀ : Matrix (Fin 2) (Fin 3) ℝ →L[ℝ] Matrix (Fin 2) (Fin 3) ℝ)
        (D - Y₀ * (lam • N₁))‖ ≤ 4 :=
  (step lam h).norm_forcing_sub_augLeft_le (c := D - Y₀ * (lam • N₁)) (𝓛 := stiffOp lam)
    (fun _ _ => rfl) (stiffOp_symm lam)
    (fun x => by
      change U₀ * U₀ᵀ * (x * (lam • N₁)) = U₀ * U₀ᵀ * x * (lam • N₁)
      simp only [Matrix.mul_assoc])
    (fun x => leftProj_rightProj_comm U₀ V₀ x) hh

end StiffCouplingExample

end LeanDLRA
