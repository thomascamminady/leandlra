import Mathlib
import LeanDLRA.Literature.Kinetic.P1807_02338a

/-!
# Local and global mass conservation are incompatible (arXiv 1807.02338, Sec. 4)

Einkemmer, Lubich, *A quasi-conservative dynamical low-rank algorithm for the Vlasov equation*,
Section 4; Sections 3 and 5 are in `LeanDLRA.Literature.Kinetic.P1807_02338a`, whose Vlasov operator
`vlasovF`, moments, right-hand sides `rhsL` and solution notions we use.  This module proves the
counterexample of Sec. 4 for the actual objects and not for a model: on `Ω_x = [0, 2π]`, `Ω_v = ℝ`
with the rank-2 functions `X₁¹ = 2/√(3π) cos²x`, `X₂¹ = sin(2x)/√π`, `V₁⁰ = e^{-v²}/(π/2)^{1/4}`,
`V₂⁰ = 2v e^{-v²}/(π/2)^{1/4}`, we compute all the integrals of the paper, show that the local mass
constraint of Step 3 forces `λ₁₁ = 0`, and determine exactly when it is compatible with the global
mass constraint.  This holds for every field `E`, in the static form of the linear systems for `λ`
and for solutions of the corrected L-step, and we give an exact solution that loses mass.

## Main results

* The data: `integral_cos_sq_mul_cos_two` (the integral `π/2`), `isOrthonormalL2_X₀`,
  `isOrthonormalL2_V₀`, `alpha_eq`, `beta_eq`, `kappa_eq`, `inner_X₁_dX₂_eq_integral`,
  `inner_X₁_dX₂`.
* The general mechanism, for any `d`, `r` and bases: `exists_local_global_iff`, and the global
  equations of Step 3 as the time derivative of total mass and momentum, `lStep_global_hasDerivAt`.
* The counterexample: `local_forces_lam`, `sec4_counterexample`, and the sharp version
  `exists_local_global_mass_iff`, `exists_local_global_mass_iff_S`.  Each system alone is solvable:
  `localConstraint_zero`, `globalConstraint_solvable`.
* For solutions: `lStep_mass_drift`, `lStep_not_continuity_and_mass`, and the instance
  `rotL_mass_not_conserved`.
* Momentum, which the paper only mentions: `exists_local_global_momentum_iff`,
  `exists_local_global_momentum_iff_S`, `local_forces_zero`.

## Claims of the paper that fail as printed

* **The display `⟨X₁¹, F(f)⟩ₓᵥ = ⟨X₁¹, ∇X₂¹⟩ · β₂` is false.**  The example never fixes `f`, and the
  right side does not depend on it.  For `f = ∑ X_i S_ij V_j` the correct value is
  `-⟨X₁¹, ∇X₂¹⟩ S₂₂ β₂` (`innerF_X₁_eq_integral`), so the display holds exactly when `S₂₂ = -1`
  (`printed_identity_iff`).
* **Consequently the example needs `S₂₂ ≠ 0`, which the paper does not state.**  With `S₂₂ = 0` the
  two systems are compatible, also for invertible `S` (`compatible_of_S₂₂_eq_zero`).  The conclusion
  "it is not possible to both satisfy the continuity equation and obtain global conservation of
  mass" is correct for general `f`: it holds for all `S` with `S₂₂ ≠ 0` (`sec4_counterexample`), for
  instance for `S = 1`.

## Modelling choices

* `d = 1`, so `x, v ∈ PS 1 = ℝ¹`.  `Ωx` is Lebesgue measure on `{x | x 0 ∈ (0, 2π]}`, the set of
  full measure in `[0, 2π]`.  The spatial functions are `2π`-periodic on all of `ℝ¹`.
* `Ω_v = ℝ`, so the integration by parts in `v` behind `b_i = 0` needs decay of `L_k`, which is
  `IsVelocityProfile` from the companion module.
* `E` is an arbitrary field with `E(·) ∈ L¹(Ω_x)`.  The Poisson equation is never used, so
  `E = E(f)` is included.  The statements are at a fixed time, as the paper's are, and `f` is either
  `∑ X_k L_k` with arbitrary `L_k`, or the value `∑ X_i S_ij V_j` at the start of Step 3.
* Existence of solutions of the corrected L-step for general `E`, `λ` is not addressed, as in the
  paper: `lStep_mass_drift` assumes a solution, and `rotL` is one for `E = 0`, `λ = 0`.
* The local momentum constraint uses `rhsL`, with the correct sign of `Eρ`; see the companion module
  for the sign error in the printed `d_i`.  For mass `rhsL` is the printed `b_i`.

## What is not formalized

The global equations of Steps 1 and 2, the size of the combined system, and the weighted
least-squares option with its cost are descriptions of the numerical method rather than results.
-/

open Set Filter Topology Finset MeasureTheory
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P1807_02338

/-! ### Trigonometric integrals over one period -/

section Trig

open Real

/-- Mean value over `[0, 2π]` of a trigonometric polynomial with frequencies `0, 2, 4`. -/
lemma integral_trig (A B C D G : ℝ) :
    ∫ x in (0 : ℝ)..(2 * π), (A + B * cos (2 * x) + C * sin (2 * x) + D * cos (4 * x) +
      G * sin (4 * x)) = 2 * π * A := by
  have hd : ∀ x ∈ uIcc (0 : ℝ) (2 * π), HasDerivAt
      (fun x => A * x + B * (sin (2 * x) / 2) - C * (cos (2 * x) / 2) + D * (sin (4 * x) / 4) -
        G * (cos (4 * x) / 4))
      (A + B * cos (2 * x) + C * sin (2 * x) + D * cos (4 * x) + G * sin (4 * x)) x := by
    intro x _
    have h2 : HasDerivAt (fun x : ℝ => 2 * x) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    have h4 : HasDerivAt (fun x : ℝ => 4 * x) 4 x := by
      simpa using (hasDerivAt_id x).const_mul (4 : ℝ)
    have e := ((((((hasDerivAt_id x).const_mul A).add
      (((h2.sin).div_const 2).const_mul B)).sub (((h2.cos).div_const 2).const_mul C)).add
      (((h4.sin).div_const 4).const_mul D)).sub (((h4.cos).div_const 4).const_mul G))
    exact e.congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have s2 : sin (2 * (2 * π)) = 0 := by
    have := sin_nat_mul_pi 4
    norm_num at this
    rw [show 2 * (2 * π) = 4 * π by ring]; exact this
  have s4 : sin (4 * (2 * π)) = 0 := by
    have := sin_nat_mul_pi 8
    norm_num at this
    rw [show 4 * (2 * π) = 8 * π by ring]; exact this
  have c2 : cos (2 * (2 * π)) = 1 := by
    have := cos_nat_mul_two_pi 2
    norm_num at this
    exact this
  have c4 : cos (4 * (2 * π)) = 1 := by
    have := cos_nat_mul_two_pi 4
    norm_num at this
    exact this
  simp only [s2, s4, c2, c4]
  simp
  ring

private lemma c2_eq (x : ℝ) : cos (2 * x) = 2 * cos x ^ 2 - 1 := cos_two_mul x
private lemma s2_eq (x : ℝ) : sin (2 * x) = 2 * sin x * cos x := sin_two_mul x
private lemma c4_eq (x : ℝ) : cos (4 * x) = 2 * (2 * cos x ^ 2 - 1) ^ 2 - 1 := by
  rw [show 4 * x = 2 * (2 * x) by ring, cos_two_mul, cos_two_mul]
private lemma s4_eq (x : ℝ) : sin (4 * x) = 2 * (2 * sin x * cos x) * (2 * cos x ^ 2 - 1) := by
  rw [show 4 * x = 2 * (2 * x) by ring, sin_two_mul, sin_two_mul, cos_two_mul]

/-- `∫₀^{2π} cos²x dx = π`. -/
lemma integral_cos_sq' : ∫ x in (0 : ℝ)..(2 * π), cos x ^ 2 = π := by
  have h := integral_trig (1 / 2) (1 / 2) 0 0 0
  have e : (fun x : ℝ => (1 / 2 : ℝ) + 1 / 2 * cos (2 * x) + 0 * sin (2 * x) + 0 * cos (4 * x) +
      0 * sin (4 * x)) = fun x => cos x ^ 2 := by
    funext x
    rw [c2_eq]; ring
  rw [e] at h
  rw [h]; ring

/-- `∫₀^{2π} sin 2x dx = 0`. -/
lemma integral_sin_two : ∫ x in (0 : ℝ)..(2 * π), sin (2 * x) = 0 := by
  have h := integral_trig 0 0 1 0 0
  have e : (fun x : ℝ => (0 : ℝ) + 0 * cos (2 * x) + 1 * sin (2 * x) + 0 * cos (4 * x) +
      0 * sin (4 * x)) = fun x => sin (2 * x) := by
    funext x; ring
  rw [e] at h
  rw [h]; ring

/-- `∫₀^{2π} cos⁴x dx = 3π/4`. -/
lemma integral_cos_four : ∫ x in (0 : ℝ)..(2 * π), (cos x ^ 2) * (cos x ^ 2) = 3 * π / 4 := by
  have h := integral_trig (3 / 8) (1 / 2) 0 (1 / 8) 0
  have e : (fun x : ℝ => (3 / 8 : ℝ) + 1 / 2 * cos (2 * x) + 0 * sin (2 * x) + 1 / 8 * cos (4 * x) +
      0 * sin (4 * x)) = fun x => (cos x ^ 2) * (cos x ^ 2) := by
    funext x
    rw [c2_eq, c4_eq]; ring
  rw [e] at h
  rw [h]; ring

/-- `∫₀^{2π} sin²2x dx = π`. -/
lemma integral_sin_two_sq : ∫ x in (0 : ℝ)..(2 * π), sin (2 * x) * sin (2 * x) = π := by
  have h := integral_trig (1 / 2) 0 0 (-1 / 2) 0
  have e : (fun x : ℝ => (1 / 2 : ℝ) + 0 * cos (2 * x) + 0 * sin (2 * x) + -1 / 2 * cos (4 * x) +
      0 * sin (4 * x)) = fun x => sin (2 * x) * sin (2 * x) := by
    funext x
    rw [s2_eq, c4_eq]
    linear_combination (-4 * cos x ^ 2) * sin_sq_add_cos_sq x
  rw [e] at h
  rw [h]; ring

/-- `∫₀^{2π} cos²x sin 2x dx = 0`. -/
lemma integral_cos_sq_mul_sin_two : ∫ x in (0 : ℝ)..(2 * π), cos x ^ 2 * sin (2 * x) = 0 := by
  have h := integral_trig 0 0 (1 / 2) 0 (1 / 4)
  have e : (fun x : ℝ => (0 : ℝ) + 0 * cos (2 * x) + 1 / 2 * sin (2 * x) + 0 * cos (4 * x) +
      1 / 4 * sin (4 * x)) = fun x => cos x ^ 2 * sin (2 * x) := by
    funext x
    rw [s2_eq, s4_eq]; ring
  rw [e] at h
  rw [h]; ring

/-- **The integral of Sec. 4** (arXiv 1807.02338): `∫₀^{2π} cos²x cos 2x dx = π/2`. -/
theorem integral_cos_sq_mul_cos_two : ∫ x in (0 : ℝ)..(2 * π), cos x ^ 2 * cos (2 * x) = π / 2 := by
  have h := integral_trig (1 / 4) (1 / 2) 0 (1 / 4) 0
  have e : (fun x : ℝ => (1 / 4 : ℝ) + 1 / 2 * cos (2 * x) + 0 * sin (2 * x) + 1 / 4 * cos (4 * x) +
      0 * sin (4 * x)) = fun x => cos x ^ 2 * cos (2 * x) := by
    funext x
    rw [c2_eq, c4_eq]; ring
  rw [e] at h
  rw [h]; ring

/-- `∫₀^{2π} sin 2x cos 2x dx = 0`. -/
lemma integral_sin_two_mul_cos_two : ∫ x in (0 : ℝ)..(2 * π), sin (2 * x) * cos (2 * x) = 0 := by
  have h := integral_trig 0 0 0 0 (1 / 2)
  have e : (fun x : ℝ => (0 : ℝ) + 0 * cos (2 * x) + 0 * sin (2 * x) + 0 * cos (4 * x) +
      1 / 2 * sin (4 * x)) = fun x => sin (2 * x) * cos (2 * x) := by
    funext x
    rw [s2_eq, s4_eq, c2_eq]; ring
  rw [e] at h
  rw [h]; ring

end Trig

/-! ### Gaussian moments -/

section Gauss

open Real

lemma integrable_pow_mul_gauss (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun y : ℝ => y ^ n * exp (-b * y ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq hb (s := (n : ℝ))
    (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  simpa [Real.rpow_natCast] using h

lemma integrable_gauss {b : ℝ} (hb : 0 < b) : Integrable (fun y : ℝ => exp (-b * y ^ 2)) := by
  simpa using integrable_pow_mul_gauss 0 hb

/-- Odd Gaussian moments vanish. -/
lemma integral_odd_gauss (g : ℝ → ℝ) (hg : ∀ y, g (-y) = -g y) :
    ∫ y, g y = 0 := by
  have h := integral_neg_eq_self g (volume : Measure ℝ)
  simp_rw [hg] at h
  rw [integral_neg] at h
  linarith

lemma integral_gauss_one (b : ℝ) : ∫ y : ℝ, y * exp (-b * y ^ 2) = 0 :=
  integral_odd_gauss _ fun y => by simp

lemma integral_gauss_two {b : ℝ} (hb : 0 < b) :
    ∫ y : ℝ, y ^ 2 * exp (-b * y ^ 2) = √(π / b) / (2 * b) := by
  have hv : ∀ x : ℝ, HasDerivAt (fun y => exp (-b * y ^ 2)) (-b * (2 * x) * exp (-b * x ^ 2)) x :=
    fun x => by
      have h1 : HasDerivAt (fun y : ℝ => -b * y ^ 2) (-b * (2 * x)) x := by
        simpa using (hasDerivAt_pow 2 x).const_mul (-b)
      simpa [mul_comm] using h1.exp
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun y : ℝ => y) (u' := fun _ => 1)
    (v := fun y => exp (-b * y ^ 2)) (v' := fun x => -b * (2 * x) * exp (-b * x ^ 2))
    (fun x _ => hasDerivAt_id x) (fun x _ => hv x)
    (by
      have := (integrable_pow_mul_gauss 2 hb).const_mul (-2 * b)
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only [Pi.mul_apply]
      ring)
    (by simpa [Pi.mul_def] using integrable_gauss hb)
    (by simpa [Pi.mul_def] using integrable_pow_mul_gauss 1 hb)
  have e1 : (fun x : ℝ => x * (-b * (2 * x) * exp (-b * x ^ 2))) =
      fun x => (-2 * b) * (x ^ 2 * exp (-b * x ^ 2)) := by
    funext x; ring
  simp only [one_mul] at h
  rw [e1, integral_const_mul, integral_gaussian b] at h
  have hb' : (0 : ℝ) < 2 * b := by positivity
  rw [eq_div_iff hb'.ne']
  linear_combination -h

lemma integral_exp_one : ∫ y : ℝ, exp (-y ^ 2) = √π := by
  have h := integral_gaussian 1
  simpa using h

lemma integral_sq_exp_one : ∫ y : ℝ, y ^ 2 * exp (-y ^ 2) = √π / 2 := by
  have h := integral_gauss_two (b := 1) one_pos
  simpa using h

lemma integral_exp_two : ∫ y : ℝ, exp (-(2 * y ^ 2)) = √(π / 2) := by
  have h := integral_gaussian 2
  simpa using h

lemma integral_sq_exp_two : ∫ y : ℝ, y ^ 2 * exp (-(2 * y ^ 2)) = √(π / 2) / 4 := by
  have h := integral_gauss_two (b := 2) two_pos
  have e : (2 : ℝ) * 2 = 4 := by norm_num
  simpa [e] using h

/-- Polynomial times Gaussian. -/
lemma integrable_poly_gauss (a b c d e : ℝ) : Integrable (fun y : ℝ =>
    (a + b * y + c * y ^ 2 + d * y ^ 3 + e * y ^ 4) * exp (-y ^ 2)) := by
  have h : ∀ n : ℕ, Integrable (fun y : ℝ => y ^ n * exp (-y ^ 2)) := fun n => by
    simpa using integrable_pow_mul_gauss n (b := 1) one_pos
  have := (((((h 0).const_mul a).add ((h 1).const_mul b)).add ((h 2).const_mul c)).add
    ((h 3).const_mul d)).add ((h 4).const_mul e)
  refine this.congr (ae_of_all _ fun y => ?_)
  simp only [Pi.add_apply]
  ring

end Gauss

/-! ### The coordinate of `ℝ¹` -/

section Coord

open Real

/-- The coordinate `v ↦ v 0` as a measurable equivalence between `ℝ¹ = PS 1` and `ℝ`. -/
noncomputable def coordEquiv : PS 1 ≃ᵐ ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

lemma measurePreserving_coord :
    MeasurePreserving coordEquiv (volume : Measure (PS 1)) (volume : Measure ℝ) :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1)).trans
    (volume_preserving_funUnique (Fin 1) ℝ)

lemma integral_coord (g : ℝ → ℝ) : ∫ v : PS 1, g (v 0) = ∫ y, g y :=
  measurePreserving_coord.integral_comp' g

lemma integrable_coord {g : ℝ → ℝ} (hg : Integrable g) : Integrable (fun v : PS 1 => g (v 0)) :=
  (measurePreserving_coord.integrable_comp_emb coordEquiv.measurableEmbedding).2 hg

/-- The spatial domain `Ω_x = [0, 2π]` of Sec. 4 with Lebesgue measure, as a measure on `ℝ¹`. -/
noncomputable def Ωx : Measure (PS 1) := volume.restrict {x | x 0 ∈ Ioc 0 (2 * π)}

lemma measurePreserving_Ωx :
    MeasurePreserving coordEquiv Ωx ((volume : Measure ℝ).restrict (Ioc 0 (2 * π))) :=
  measurePreserving_coord.restrict_preimage measurableSet_Ioc

instance : IsFiniteMeasure Ωx := ⟨by
  have h := measurePreserving_Ωx.measure_preimage MeasurableSet.univ.nullMeasurableSet
  rw [preimage_univ] at h
  rw [h, Measure.restrict_apply_univ, Real.volume_Ioc]
  exact ENNReal.ofReal_lt_top⟩

lemma integral_Ωx (g : ℝ → ℝ) : ∫ x, g (x 0) ∂Ωx = ∫ y in (0 : ℝ)..(2 * π), g y := by
  rw [intervalIntegral.integral_of_le (by positivity)]
  exact measurePreserving_Ωx.integral_comp' g

lemma integrable_Ωx {g : ℝ → ℝ} (hg : Continuous g) : Integrable (fun x : PS 1 => g (x 0)) Ωx :=
  (measurePreserving_Ωx.integrable_comp_emb coordEquiv.measurableEmbedding).2 hg.integrableOn_Ioc

lemma norm_coord (v : PS 1) : ‖v‖ = |v 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _), Real.norm_eq_abs]

lemma hasFDerivAt_coord {h : ℝ → ℝ} {h' : ℝ} {x : PS 1} (hh : HasDerivAt h h' (x 0)) :
    HasFDerivAt (fun y : PS 1 => h (y 0))
      (h' • (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1) : PS 1 →L[ℝ] ℝ)) x :=
  hh.comp_hasFDerivAt x (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1) : PS 1 →L[ℝ] ℝ).hasFDerivAt

/-- On `ℝ¹` the partial derivative of a function of the coordinate is its derivative. -/
lemma pd_coord {h : ℝ → ℝ} {h' : ℝ} {x : PS 1} (hh : HasDerivAt h h' (x 0)) :
    pd 0 (fun y : PS 1 => h (y 0)) x = h' := by
  simp [pd, (hasFDerivAt_coord hh).fderiv]

/-- A sufficient condition for a function of the coordinate to be a velocity profile. -/
lemma isVelocityProfile_coord {g g' : ℝ → ℝ} (hg : ∀ y, HasDerivAt g (g' y) y)
    (hg' : Continuous g') (h1 : Integrable fun y => (1 + y ^ 2) * g y)
    (h2 : Integrable fun y => (1 + y ^ 2) * g' y) :
    IsVelocityProfile (volume : Measure (PS 1)) (fun v => g (v 0)) where
  differentiable v := (hasFDerivAt_coord (hg (v 0))).differentiableAt
  integrable := by
    refine (integrable_coord h1).congr (ae_of_all _ fun v => ?_)
    simp [norm_coord]
  integrable_pd b := by
    have hb : b = 0 := Subsingleton.elim _ _
    subst hb
    have e : ∀ v : PS 1, pd 0 (fun v : PS 1 => g (v 0)) v = g' (v 0) := fun v =>
      pd_coord (hg (v 0))
    simp only [e, norm_coord]
    refine ((integrable_coord h2).const_mul 2).mono
      (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun v => ?_)
    have hy : 1 + |v 0| ≤ 2 * (1 + v 0 ^ 2) := by
      nlinarith [sq_abs (v 0), sq_nonneg (|v 0| - 1), abs_nonneg (v 0)]
    have hp : (0 : ℝ) ≤ 1 + |v 0| := by positivity
    have hq : (0 : ℝ) ≤ 1 + v 0 ^ 2 := by positivity
    rw [norm_mul, norm_mul, norm_mul, Real.norm_of_nonneg hp, Real.norm_of_nonneg hq,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc (1 + |v 0|) * ‖g' (v 0)‖ ≤ (2 * (1 + v 0 ^ 2)) * ‖g' (v 0)‖ :=
          mul_le_mul_of_nonneg_right hy (norm_nonneg _)
      _ = 2 * ((1 + v 0 ^ 2) * ‖g' (v 0)‖) := by ring

end Coord

/-! ### The functions of the counterexample -/

section Factors

open Real

/-- The functions `X₁¹(x) = 2/√(3π) cos²x` and `X₂¹(x) = sin(2x)/√π` of Sec. 4 as functions of the
real variable. -/
noncomputable def xf : Fin 2 → ℝ → ℝ :=
  ![fun y => 2 / √(3 * π) * cos y ^ 2, fun y => 1 / √π * sin (2 * y)]

/-- The derivatives of `xf`. -/
noncomputable def xd : Fin 2 → ℝ → ℝ :=
  ![fun y => -(2 / √(3 * π)) * sin (2 * y), fun y => 2 / √π * cos (2 * y)]

/-- The functions `V₁⁰(v) = e^{-v²}/(π/2)^{1/4}` and `V₂⁰(v) = 2v e^{-v²}/(π/2)^{1/4}` of Sec. 4 as
functions of the real variable. -/
noncomputable def vf : Fin 2 → ℝ → ℝ :=
  ![fun y => exp (-y ^ 2) / (π / 2) ^ (1 / 4 : ℝ),
    fun y => 2 * y * exp (-y ^ 2) / (π / 2) ^ (1 / 4 : ℝ)]

/-- The derivatives of `vf`. -/
noncomputable def vd : Fin 2 → ℝ → ℝ :=
  ![fun y => -(2 * y) * exp (-y ^ 2) / (π / 2) ^ (1 / 4 : ℝ),
    fun y => (2 - 4 * y ^ 2) * exp (-y ^ 2) / (π / 2) ^ (1 / 4 : ℝ)]

/-- The spatial basis `X₁¹, X₂¹` of Sec. 4 on `Ω_x ⊂ ℝ¹`. -/
noncomputable def X₀ (i : Fin 2) (x : PS 1) : ℝ := xf i (x 0)

/-- The velocity basis `V₁⁰, V₂⁰` of Sec. 4 on `Ω_v = ℝ¹`. -/
noncomputable def V₀ (j : Fin 2) (v : PS 1) : ℝ := vf j (v 0)

/-- `⁴√(2π)`, the value of `α₁` and of `β₂`. -/
noncomputable def a₀ : ℝ := (2 * π) ^ (1 / 4 : ℝ)

/-- The normalising constant `(π/2)^{1/4}`. -/
private noncomputable def c₀ : ℝ := (π / 2) ^ (1 / 4 : ℝ)

private lemma c₀_pos : 0 < c₀ := rpow_pos_of_pos (by positivity) _

lemma a₀_pos : 0 < a₀ := rpow_pos_of_pos (by positivity) _

private lemma c₀_mul_self : c₀ * c₀ = √(π / 2) := by
  rw [c₀, ← rpow_add (by positivity), sqrt_eq_rpow]
  norm_num

private lemma a₀_mul_c₀ : a₀ * c₀ = √π := by
  rw [a₀, c₀, ← mul_rpow (by positivity) (by positivity),
    show 2 * π * (π / 2) = π ^ (2 : ℝ) by rw [rpow_two]; ring, ← rpow_mul pi_pos.le, sqrt_eq_rpow]
  norm_num

private lemma a₀_eq : a₀ = √π / c₀ := by
  rw [eq_div_iff c₀_pos.ne', a₀_mul_c₀]

private lemma vf_zero (y : ℝ) : vf 0 y = exp (-y ^ 2) / c₀ := rfl
private lemma vf_one (y : ℝ) : vf 1 y = 2 * y * exp (-y ^ 2) / c₀ := rfl
private lemma vd_zero (y : ℝ) : vd 0 y = -(2 * y) * exp (-y ^ 2) / c₀ := rfl
private lemma vd_one (y : ℝ) : vd 1 y = (2 - 4 * y ^ 2) * exp (-y ^ 2) / c₀ := rfl
private lemma xf_zero (y : ℝ) : xf 0 y = 2 / √(3 * π) * cos y ^ 2 := rfl
private lemma xf_one (y : ℝ) : xf 1 y = 1 / √π * sin (2 * y) := rfl
private lemma xd_zero (y : ℝ) : xd 0 y = -(2 / √(3 * π)) * sin (2 * y) := rfl
private lemma xd_one (y : ℝ) : xd 1 y = 2 / √π * cos (2 * y) := rfl

lemma continuous_xf (i : Fin 2) : Continuous (xf i) := by
  fin_cases i
  · exact (by fun_prop : Continuous fun y : ℝ => 2 / √(3 * π) * cos y ^ 2)
  · exact (by fun_prop : Continuous fun y : ℝ => 1 / √π * sin (2 * y))

lemma continuous_xd (i : Fin 2) : Continuous (xd i) := by
  fin_cases i
  · exact (by fun_prop : Continuous fun y : ℝ => -(2 / √(3 * π)) * sin (2 * y))
  · exact (by fun_prop : Continuous fun y : ℝ => 2 / √π * cos (2 * y))

lemma continuous_vf (i : Fin 2) : Continuous (vf i) := by
  fin_cases i
  · exact (by fun_prop : Continuous fun y : ℝ => exp (-y ^ 2) / (π / 2) ^ (1 / 4 : ℝ))
  · exact (by fun_prop : Continuous fun y : ℝ => 2 * y * exp (-y ^ 2) / (π / 2) ^ (1 / 4 : ℝ))

lemma continuous_vd (i : Fin 2) : Continuous (vd i) := by
  fin_cases i
  · exact (by fun_prop : Continuous fun y : ℝ => -(2 * y) * exp (-y ^ 2) / (π / 2) ^ (1 / 4 : ℝ))
  · exact (by fun_prop :
      Continuous fun y : ℝ => (2 - 4 * y ^ 2) * exp (-y ^ 2) / (π / 2) ^ (1 / 4 : ℝ))

lemma hasDerivAt_xf : ∀ (i : Fin 2) (y : ℝ), HasDerivAt (xf i) (xd i y) y := by
  refine Fin.forall_fin_two.2 ⟨fun y => ?_, fun y => ?_⟩
  · have h := ((hasDerivAt_cos y).pow 2).const_mul (2 / √(3 * π))
    refine h.congr_deriv ?_
    have e : (2 : ℕ) - 1 = 1 := rfl
    rw [xd_zero, sin_two_mul, e, pow_one]
    push_cast
    ring
  · have h2 : HasDerivAt (fun x : ℝ => 2 * x) 2 y := by
      simpa using (hasDerivAt_id y).const_mul (2 : ℝ)
    have h := (h2.sin).const_mul (1 / √π)
    refine h.congr_deriv ?_
    rw [xd_one]
    ring

lemma hasDerivAt_vf : ∀ (i : Fin 2) (y : ℝ), HasDerivAt (vf i) (vd i y) y := by
  have he : ∀ y : ℝ, HasDerivAt (fun y : ℝ => exp (-y ^ 2)) (exp (-y ^ 2) * (-(2 * y))) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => -y ^ 2) (-(2 * y)) y := by
      simpa using (hasDerivAt_pow 2 y).const_mul (-1 : ℝ)
    exact h1.exp
  refine Fin.forall_fin_two.2 ⟨fun y => ?_, fun y => ?_⟩
  · have h := (he y).div_const c₀
    refine h.congr_deriv ?_
    rw [vd_zero]
    ring
  · have h1 : HasDerivAt (fun y : ℝ => 2 * y) 2 y := by
      simpa using (hasDerivAt_id y).const_mul (2 : ℝ)
    have h := (h1.mul (he y)).div_const c₀
    refine h.congr_deriv ?_
    rw [vd_one]
    ring

lemma differentiable_X₀ (k : Fin 2) : Differentiable ℝ (X₀ k) := fun x =>
  (hasFDerivAt_coord (hasDerivAt_xf k (x 0))).differentiableAt

lemma pd_X₀ (k : Fin 2) (x : PS 1) : pd 0 (X₀ k) x = xd k (x 0) :=
  pd_coord (hasDerivAt_xf k (x 0))

/-- The velocity basis functions are velocity profiles. -/
lemma isVelocityProfile_V₀ (j : Fin 2) : IsVelocityProfile (volume : Measure (PS 1)) (V₀ j) := by
  refine isVelocityProfile_coord (hasDerivAt_vf j) (continuous_vd j) ?_ ?_
  · revert j
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · refine ((integrable_poly_gauss 1 0 1 0 0).div_const c₀).congr (ae_of_all _ fun y => ?_)
      simp only [vf_zero]
      ring
    · refine ((integrable_poly_gauss 0 2 0 2 0).div_const c₀).congr (ae_of_all _ fun y => ?_)
      simp only [vf_one]
      ring
  · revert j
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · refine ((integrable_poly_gauss 0 (-2) 0 (-2) 0).div_const c₀).congr (ae_of_all _ fun y => ?_)
      simp only [vd_zero]
      ring
    · refine ((integrable_poly_gauss 2 0 (-2) 0 (-4)).div_const c₀).congr (ae_of_all _ fun y => ?_)
      simp only [vd_one]
      ring

end Factors

/-! ### Local and global constraints in Step 3 -/

section General

variable {d r : ℕ} {μ ν : Measure (PS d)} {X V : Fin r → PS d → ℝ}

/-- `κ_i = ∫ X_i dx`. -/
noncomputable def kappa (μ : Measure (PS d)) (X : Fin r → PS d → ℝ) (i : Fin r) : ℝ :=
  ∫ x, X i x ∂μ

/-- `⟨w_m X_i, F(f)⟩ₓᵥ`, with weight `w_m = 1` (mass) or `w_m = v_a` (momentum), as an iterated
integral with `x` inside, as in the right-hand side `rhsL`. -/
noncomputable def innerF (μ ν : Measure (PS d)) (X : Fin r → PS d → ℝ) (E₀ : PS d → PS d)
    (f : PS d → PS d → ℝ) (m : Option (Fin d)) (i : Fin r) : ℝ :=
  ∫ v, wt m v * ∫ x, X i x * vlasovF E₀ f x v ∂μ ∂ν

/-- The local constraints of Step 3, (3.13) and (3.14), in the form (3.8) with Step 3's
right-hand sides: `∑_l λ_il α_l = b_i` for `m = none` and
`∑_l λ_il β_{a,l} = (d_i)_a` for `m = some a`.  The right-hand side is `rhsL`, which has the correct
sign of `Eρ`; for mass it is the printed `b_i`. -/
def LocalConstraint (μ ν : Measure (PS d)) (X V : Fin r → PS d → ℝ) (E₀ : PS d → PS d)
    (f : PS d → PS d → ℝ) (m : Option (Fin d)) (lam : Matrix (Fin r) (Fin r) ℝ) : Prop :=
  ∀ i, ∑ l, lam i l * momentMatrix ν V m l = rhsL μ ν X E₀ f m i

/-- The global constraints of Step 3 in Sec. 4:
`0 = ∑_ij κ_i λ_ij α_j + ∑_i κ_i ⟨X_i, F(f)⟩ₓᵥ` for `m = none` and
`0 = ∑_ij κ_i λ_ij β_j + ∑_i κ_i ⟨v X_i, F(f)⟩ₓᵥ` for `m = some a`.
By `lStep_global_hasDerivAt` this says that the time derivative of the total mass, respectively
momentum, of the corrected L-step vanishes. -/
def GlobalConstraint (μ ν : Measure (PS d)) (X V : Fin r → PS d → ℝ) (E₀ : PS d → PS d)
    (f : PS d → PS d → ℝ) (m : Option (Fin d)) (lam : Matrix (Fin r) (Fin r) ℝ) : Prop :=
  ∑ i, ∑ j, kappa μ X i * lam i j * momentMatrix ν V m j +
    ∑ i, kappa μ X i * innerF μ ν X E₀ f m i = 0

variable {E₀ : PS d → PS d} {f : PS d → PS d → ℝ} {m : Option (Fin d)}

/-- When `rhsL` vanishes the local constraints make the `λ`-part of the global constraint vanish. -/
lemma sum_kappa_lam_eq_zero {lam : Matrix (Fin r) (Fin r) ℝ}
    (hrhs : ∀ i, rhsL μ ν X E₀ f m i = 0) (hloc : LocalConstraint μ ν X V E₀ f m lam) :
    ∑ i, ∑ j, kappa μ X i * lam i j * momentMatrix ν V m j = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  have h := hloc i
  rw [hrhs i] at h
  calc ∑ j, kappa μ X i * lam i j * momentMatrix ν V m j
      = kappa μ X i * ∑ j, lam i j * momentMatrix ν V m j := by
        rw [mul_sum]
        exact sum_congr rfl fun j _ => by ring
    _ = 0 := by rw [h, mul_zero]

/-- **Sec. 4, why the systems can be incompatible** (arXiv 1807.02338).  In Step 3 the right-hand
side of the local system vanishes, so a `λ` that solves it does not enter the global constraint.
Local and global constraints then have a common solution exactly when
`∑_i κ_i ⟨w_m X_i, F(f)⟩ₓᵥ = 0`, a condition on `f` that `λ` cannot influence.  General version,
for any bases and any `d`, `r`; the hypothesis is `rhsL_lowRank_eq_zero`. -/
theorem exists_local_global_iff (hrhs : ∀ i, rhsL μ ν X E₀ f m i = 0) :
    (∃ lam, LocalConstraint μ ν X V E₀ f m lam ∧ GlobalConstraint μ ν X V E₀ f m lam) ↔
      ∑ i, kappa μ X i * innerF μ ν X E₀ f m i = 0 := by
  constructor
  · rintro ⟨lam, hloc, hglob⟩
    have h := sum_kappa_lam_eq_zero hrhs hloc
    rw [GlobalConstraint, h, zero_add] at hglob
    exact hglob
  · intro h
    refine ⟨0, fun i => ?_, ?_⟩
    · simp [hrhs i]
    · simp [GlobalConstraint, h]

/-- **Sec. 4, the term `⟨X_i, F(f)⟩ₓᵥ`** (arXiv 1807.02338).  It equals `-⟨X_i, ∇·(ρu)⟩ₓ`, written
out for `f = ∑ X_k L_k`: minus `∑_a ∑_k ⟨X_i, ∂_a X_k⟩ ∫ v_a L_k dv`, for any field.  This is the
correct version of the identity that Sec. 4 uses, see `printed_identity_iff`. -/
theorem innerF_none_lowRank [ν.IsAddHaarMeasure] {L : Fin r → PS d → ℝ}
    (hL : ∀ k, IsVelocityProfile ν (L k)) (hXd : ∀ k, Differentiable ℝ (X k)) (i : Fin r)
    (hc : ∀ a k, Integrable (fun x => X i x * pd a (X k) x) μ)
    (he : ∀ b k, Integrable (fun x => X i x * (X k x * E₀ x b)) μ) :
    innerF μ ν X E₀ (lowRank X L) none i =
      -∑ a, ∑ k, (∫ x, X i x * pd a (X k) x ∂μ) * ∫ v, v a * L k v ∂ν := by
  have h := rhsL_lowRank_eq_zero (μ := μ) (E₀ := E₀) hL hXd i hc he none
  have e : ∫ x, X i x * flux ν E₀ (lowRank X L) none x ∂μ =
      ∑ a, ∑ k, (∫ x, X i x * pd a (X k) x ∂μ) * ∫ v, v a * L k v ∂ν := by
    simp only [flux]
    simp_rw [X_mul_divMomentum hL hXd i]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun k _ => (hc a k).mul_const _]
    simp_rw [integral_finsetSum _ fun k _ => (hc _ k).mul_const _, integral_mul_const]
  rw [rhsL, e] at h
  rw [innerF]
  linarith

/-- **Sec. 4, the term `⟨v X_i, F(f)⟩ₓᵥ`** (arXiv 1807.02338).  It equals
`-⟨X_i, (∇·(ρu ⊗ u))_c + E_c ρ⟩ₓ`, written out for `f = ∑ X_k L_k`. -/
theorem innerF_some_lowRank [ν.IsAddHaarMeasure] {L : Fin r → PS d → ℝ}
    (hL : ∀ k, IsVelocityProfile ν (L k)) (hXd : ∀ k, Differentiable ℝ (X k)) (i : Fin r)
    (hc : ∀ a k, Integrable (fun x => X i x * pd a (X k) x) μ)
    (he : ∀ b k, Integrable (fun x => X i x * (X k x * E₀ x b)) μ) (c : Fin d) :
    innerF μ ν X E₀ (lowRank X L) (some c) i =
      -(∑ b, ∑ k, (∫ x, X i x * pd b (X k) x ∂μ) * ∫ v, v c * v b * L k v ∂ν) -
        ∫ x, X i x * (E₀ x c * rho ν (lowRank X L) x) ∂μ := by
  have h := rhsL_lowRank_eq_zero (μ := μ) (E₀ := E₀) hL hXd i hc he (some c)
  have e : ∫ x, X i x * divStress ν (lowRank X L) c x ∂μ =
      ∑ b, ∑ k, (∫ x, X i x * pd b (X k) x ∂μ) * ∫ v, v c * v b * L k v ∂ν := by
    simp_rw [X_mul_divStress hL hXd i c]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun k _ => (hc a k).mul_const _]
    simp_rw [integral_finsetSum _ fun k _ => (hc _ k).mul_const _, integral_mul_const]
  simp only [rhsL, flux, mul_add] at h
  rw [integral_add (integrable_X_divStress hL hXd i c hc) (integrable_X_E_rho hL i c he), e] at h
  rw [innerF]
  linarith

variable {E : ℝ → PS d → PS d} {t : ℝ} {L : ℝ → Fin r → PS d → ℝ}
  {lam : ℝ → Matrix (Fin r) (Fin r) ℝ}

/-- **Sec. 4, Step 3, the global equations** (arXiv 1807.02338).  Along a solution of the corrected
L-step (3.12) `∂ₜL_i = ⟨X_i, F(f)⟩ₓ + ∑_l λ_il V_l`, the total mass (`m = none`) and the total
momentum (`m = some a`) have the time derivative
`∑_ij κ_i λ_ij α_j + ∑_i κ_i ⟨X_i, F(f)⟩ₓᵥ`, respectively with `β_j` and `⟨v X_i, F(f)⟩ₓᵥ`.
So `GlobalConstraint` is exactly the condition that the derivative vanishes. -/
theorem lStep_global_hasDerivAt [IsFiniteMeasure μ] (hX : IsOrthonormalL2 μ X)
    (hV : ∀ m j, Integrable (fun v => wt m v * V j v) ν)
    (hL : ∀ k, IsDominatedCurve ν (fun s => L s k)
      (fun s v => (∫ x, X k x * vlasovF (E s) (lowRank X (L s)) x v ∂μ) + ∑ l, lam s k l * V l v) t)
    (m : Option (Fin d)) :
    HasDerivAt (fun s => ∫ x, moment ν m (lowRank X (L s)) x ∂μ)
      (∑ i, ∑ j, kappa μ X i * lam t i j * momentMatrix ν V m j +
        ∑ i, kappa μ X i * innerF μ ν X (E t) (lowRank X (L t)) m i) t := by
  set A := momentMatrix ν V with hA
  set I : Fin r → PS d → ℝ := fun k v => ∫ x, X k x * vlasovF (E t) (lowRank X (L t)) x v ∂μ with hI
  have hsplit : ∀ k, ∫ v, wt m v * (I k v + ∑ l, lam t k l * V l v) ∂ν =
      innerF μ ν X (E t) (lowRank X (L t)) m k + ∑ l, lam t k l * A m l := fun k => by
    have hVsum : Integrable (fun v => ∑ l, lam t k l * (wt m v * V l v)) ν :=
      integrable_finsetSum _ fun l _ => (hV m l).const_mul _
    have htot := ((hL k).hasDerivAt_moment m).1
    have e : ∀ v, wt m v * (I k v + ∑ l, lam t k l * V l v) =
        wt m v * I k v + ∑ l, lam t k l * (wt m v * V l v) := fun v => by
      rw [mul_add, mul_sum]
      congr 1
      exact sum_congr rfl fun l _ => by ring
    have hIint : Integrable (fun v => wt m v * I k v) ν := by
      have e' : (fun v => wt m v * I k v) = fun v =>
          wt m v * (I k v + ∑ l, lam t k l * V l v) - ∑ l, lam t k l * (wt m v * V l v) := by
        funext v
        rw [e]
        ring
      rw [e']
      exact htot.sub hVsum
    simp_rw [e]
    rw [integral_add hIint hVsum, integral_finsetSum _ fun l _ => (hV m l).const_mul _]
    simp_rw [integral_const_mul]
    rfl
  have hint : ∀ k, Integrable (X k) μ := fun k => (hX.memLp k).integrable one_le_two
  have h1 : HasDerivAt (fun s => ∑ k, kappa μ X k * ∫ v, wt m v * L s k v ∂ν)
      (∑ k, kappa μ X k *
        (innerF μ ν X (E t) (lowRank X (L t)) m k + ∑ l, lam t k l * A m l)) t := by
    refine HasDerivAt.fun_sum fun k _ => ?_
    rw [← hsplit k]
    exact ((hL k).hasDerivAt_moment m).2.const_mul _
  have h2 : (fun s => ∫ x, moment ν m (lowRank X (L s)) x ∂μ) =ᶠ[𝓝 t]
      fun s => ∑ k, kappa μ X k * ∫ v, wt m v * L s k v ∂ν := by
    filter_upwards [eventually_all.2 fun k => (hL k).integrable] with s hs
    have e : ∀ x, moment ν m (lowRank X (L s)) x = ∑ k, X k x * ∫ v, wt m v * L s k v ∂ν :=
      fun x => moment_lowRank (fun k => integrable_wt_of_weighted (hs k) m) x
    simp_rw [e]
    rw [integral_finsetSum _ fun k _ => (hint k).mul_const _]
    simp_rw [integral_mul_const]
    rfl
  have h3 := h1.congr_of_eventuallyEq h2
  convert h3 using 1
  simp only [mul_add, sum_add_distrib, mul_sum]
  rw [add_comm]
  congr 1
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

/-- **Step 3, projected continuity equation ⟺ local mass constraint** (arXiv 1807.02338).  Along a
solution of the corrected L-step, `P_X̄ (∂ₜρ + ∇·(ρu)) = 0` holds exactly when `∑_l λ_il α_l = 0`
for all `i`. -/
theorem lStep_projectedContinuity_iff [ν.IsAddHaarMeasure] (hX : IsOrthonormalL2 μ X)
    (hV : ∀ m j, Integrable (fun v => wt m v * V j v) ν) (hXd : ∀ k, Differentiable ℝ (X k))
    (hc : ∀ i a k, Integrable (fun x => X i x * pd a (X k) x) μ)
    (he : ∀ i b k, Integrable (fun x => X i x * (X k x * E t x b)) μ)
    (hprof : ∀ k, IsVelocityProfile ν (L t k))
    (hL : ∀ k, IsDominatedCurve ν (fun s => L s k)
      (fun s v => (∫ x, X k x * vlasovF (E s) (lowRank X (L s)) x v ∂μ) +
        ∑ l, lam s k l * V l v) t) :
    proj μ X (fun x => deriv (fun s => rho ν (lowRank X (L s)) x) t +
        divMomentum ν (lowRank X (L t)) x) = 0 ↔
      ∀ i, ∑ l, lam t i l * momentMatrix ν V none l = 0 := by
  have hΦ : ∀ i m, Integrable (fun x => X i x * flux ν (E t) (lowRank X (L t)) m x) μ :=
    fun i m => integrable_X_flux hprof hXd i m (hc i) (he i)
  rw [proj_eq_zero_iff hX]
  refine forall_congr' fun i => ?_
  have h := lStep_residual hX hV hL hΦ none i
  rw [rhsL_lowRank_eq_zero hprof hXd i (hc i) (he i) none, sub_zero] at h
  simp only [moment_none, flux] at h
  rw [h]
  simp only [Matrix.mulVec, dotProduct]
  have e : ∑ l, momentMatrix ν V none l * lam t i l = ∑ l, lam t i l * momentMatrix ν V none l :=
    sum_congr rfl fun l _ => mul_comm _ _
  rw [e]

end General

/-! ### The data of the counterexample -/

section Data

open Real

private lemma sp_pos : 0 < √π := Real.sqrt_pos.2 pi_pos
private lemma s3_pos : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
private lemma sp_mul : √π * √π = π := Real.mul_self_sqrt pi_pos.le
private lemma s3_mul : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
private lemma s3p : √(3 * π) = √3 * √π := Real.sqrt_mul (by norm_num) π
private lemma s3p_mul : √(3 * π) * √(3 * π) = 3 * π := Real.mul_self_sqrt (by positivity)

/-- `2/√3`, the value of `⟨X₁¹, ∂ₓX₂¹⟩`. -/
noncomputable def c₁ : ℝ := 2 / √3

lemma c₁_pos : 0 < c₁ := div_pos two_pos s3_pos

private lemma inner_xf_00 : ∫ y in (0 : ℝ)..(2 * π), xf 0 y * xf 0 y = 1 := by
  have e : (fun y => xf 0 y * xf 0 y) = fun y =>
      (2 / √(3 * π) * (2 / √(3 * π))) * (cos y ^ 2 * cos y ^ 2) := by
    funext y
    rw [xf_zero]
    ring
  rw [e, intervalIntegral.integral_const_mul, integral_cos_four, div_mul_div_comm, s3p_mul]
  have := pi_pos
  field_simp
  norm_num

private lemma inner_xf_01 : ∫ y in (0 : ℝ)..(2 * π), xf 0 y * xf 1 y = 0 := by
  have e : (fun y => xf 0 y * xf 1 y) = fun y =>
      (2 / √(3 * π) * (1 / √π)) * (cos y ^ 2 * sin (2 * y)) := by
    funext y
    rw [xf_zero, xf_one]
    ring
  rw [e, intervalIntegral.integral_const_mul, integral_cos_sq_mul_sin_two, mul_zero]

private lemma inner_xf_10 : ∫ y in (0 : ℝ)..(2 * π), xf 1 y * xf 0 y = 0 := by
  simp_rw [mul_comm (xf 1 _)]
  exact inner_xf_01

private lemma inner_xf_11 : ∫ y in (0 : ℝ)..(2 * π), xf 1 y * xf 1 y = 1 := by
  have e : (fun y => xf 1 y * xf 1 y) = fun y =>
      (1 / √π * (1 / √π)) * (sin (2 * y) * sin (2 * y)) := by
    funext y
    rw [xf_one]
    ring
  rw [e, intervalIntegral.integral_const_mul, integral_sin_two_sq, div_mul_div_comm, sp_mul]
  have := pi_pos
  field_simp

lemma continuous_coord₀ : Continuous fun x : PS 1 => x 0 := by fun_prop

lemma continuous_X₀ (i : Fin 2) : Continuous (X₀ i) := (continuous_xf i).comp continuous_coord₀

lemma continuous_V₀ (i : Fin 2) : Continuous (V₀ i) := (continuous_vf i).comp continuous_coord₀

/-- **Sec. 4** (arXiv 1807.02338): the functions `X₁¹, X₂¹` are orthonormal in `L²(0, 2π)`. -/
theorem isOrthonormalL2_X₀ : IsOrthonormalL2 Ωx X₀ where
  memLp i := (memLp_two_iff_integrable_sq (continuous_X₀ i).aestronglyMeasurable).2
    (integrable_Ωx (g := fun y => xf i y ^ 2) ((continuous_xf i).pow 2))
  inner_eq i k := by
    have h : ∫ x, X₀ i x * X₀ k x ∂Ωx = ∫ y in (0 : ℝ)..(2 * π), xf i y * xf k y :=
      integral_Ωx fun y => xf i y * xf k y
    have key : ∀ i k : Fin 2, ∫ y in (0 : ℝ)..(2 * π), xf i y * xf k y =
        if i = k then 1 else 0 := by
      refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · rw [inner_xf_00]; simp
      · rw [inner_xf_01]; simp
      · rw [inner_xf_10]; simp
      · rw [inner_xf_11]; simp
    rw [h, key]

private lemma exp_mul_self (y : ℝ) : exp (-y ^ 2) * exp (-y ^ 2) = exp (-(2 * y ^ 2)) := by
  rw [← exp_add]
  ring_nf

private lemma integrable_exp_two : ∀ n : ℕ, Integrable fun y : ℝ => y ^ n * exp (-(2 * y ^ 2)) :=
  fun n => by simpa using integrable_pow_mul_gauss n (b := 2) two_pos

private lemma vf_mul_00 (y : ℝ) :
    vf 0 y * vf 0 y = 1 / (c₀ * c₀) * exp (-(2 * y ^ 2)) := by
  rw [vf_zero, ← exp_mul_self]
  ring

private lemma vf_mul_01 (y : ℝ) :
    vf 0 y * vf 1 y = 2 / (c₀ * c₀) * (y * exp (-(2 * y ^ 2))) := by
  rw [vf_zero, vf_one, ← exp_mul_self]
  ring

private lemma vf_mul_11 (y : ℝ) :
    vf 1 y * vf 1 y = 4 / (c₀ * c₀) * (y ^ 2 * exp (-(2 * y ^ 2))) := by
  rw [vf_one, ← exp_mul_self]
  ring

private lemma inner_vf_00 : ∫ y, vf 0 y * vf 0 y = 1 := by
  simp_rw [vf_mul_00]
  rw [integral_const_mul, integral_exp_two, c₀_mul_self]
  have : 0 < √(π / 2) := Real.sqrt_pos.2 (by positivity)
  field_simp

private lemma inner_vf_01 : ∫ y, vf 0 y * vf 1 y = 0 := by
  simp_rw [vf_mul_01]
  rw [integral_const_mul, integral_odd_gauss _ fun y => by simp, mul_zero]

private lemma inner_vf_10 : ∫ y, vf 1 y * vf 0 y = 0 := by
  simp_rw [mul_comm (vf 1 _)]
  exact inner_vf_01

private lemma inner_vf_11 : ∫ y, vf 1 y * vf 1 y = 1 := by
  simp_rw [vf_mul_11]
  rw [integral_const_mul, integral_sq_exp_two, c₀_mul_self]
  have : 0 < √(π / 2) := Real.sqrt_pos.2 (by positivity)
  field_simp

private lemma integrable_vf_sq : ∀ j : Fin 2, Integrable fun y => vf j y ^ 2 := by
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · refine ((integrable_exp_two 0).const_mul (1 / (c₀ * c₀))).congr (ae_of_all _ fun y => ?_)
    simp only [pow_zero, one_mul]
    rw [sq (vf 0 y), vf_mul_00]
  · refine ((integrable_exp_two 2).const_mul (4 / (c₀ * c₀))).congr (ae_of_all _ fun y => ?_)
    simp only
    rw [sq (vf 1 y), vf_mul_11]

/-- **Sec. 4** (arXiv 1807.02338): the functions `V₁⁰, V₂⁰` are orthonormal in `L²(ℝ)`. -/
theorem isOrthonormalL2_V₀ : IsOrthonormalL2 (volume : Measure (PS 1)) V₀ where
  memLp i := (memLp_two_iff_integrable_sq (continuous_V₀ i).aestronglyMeasurable).2
    (integrable_coord (integrable_vf_sq i))
  inner_eq i k := by
    have h : ∫ v, V₀ i v * V₀ k v = ∫ y, vf i y * vf k y :=
      integral_coord fun y => vf i y * vf k y
    have key : ∀ i k : Fin 2, ∫ y, vf i y * vf k y = if i = k then 1 else 0 := by
      refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · rw [inner_vf_00]; simp
      · rw [inner_vf_01]; simp
      · rw [inner_vf_10]; simp
      · rw [inner_vf_11]; simp
    rw [h, key]

lemma momentMatrix_none (j : Fin 2) :
    momentMatrix (volume : Measure (PS 1)) V₀ none j = ∫ y, vf j y := by
  simp only [momentMatrix, Matrix.of_apply, wt_none, one_mul]
  exact integral_coord (vf j)

lemma momentMatrix_some (j : Fin 2) :
    momentMatrix (volume : Measure (PS 1)) V₀ (some 0) j = ∫ y, y * vf j y := by
  simp only [momentMatrix, Matrix.of_apply, wt_some]
  exact integral_coord fun y => y * vf j y

private lemma int_vf_0 : ∫ y, vf 0 y = a₀ := by
  simp_rw [vf_zero]
  rw [integral_div, integral_exp_one, a₀_eq]

private lemma int_vf_1 : ∫ y, vf 1 y = 0 :=
  integral_odd_gauss _ fun y => by
    rw [vf_one, vf_one, neg_sq]
    ring

private lemma int_y_vf_0 : ∫ y, y * vf 0 y = 0 :=
  integral_odd_gauss _ fun y => by
    rw [vf_zero, vf_zero, neg_sq]
    ring

private lemma int_y_vf_1 : ∫ y, y * vf 1 y = a₀ := by
  have e : (fun y => y * vf 1 y) = fun y => 2 / c₀ * (y ^ 2 * exp (-y ^ 2)) := by
    funext y
    rw [vf_one]
    ring
  rw [e, integral_const_mul, integral_sq_exp_one, a₀_eq]
  field_simp

private lemma int_yy_vf_0 : ∫ y, y * y * vf 0 y = a₀ / 2 := by
  have e : (fun y => y * y * vf 0 y) = fun y => 1 / c₀ * (y ^ 2 * exp (-y ^ 2)) := by
    funext y
    rw [vf_zero]
    ring
  rw [e, integral_const_mul, integral_sq_exp_one, a₀_eq]
  field_simp

private lemma int_yy_vf_1 : ∫ y, y * y * vf 1 y = 0 :=
  integral_odd_gauss _ fun y => by
    rw [vf_one, vf_one, neg_sq]
    ring

/-- **Sec. 4** (arXiv 1807.02338): `α = (⁴√(2π), 0)`, where `α_j = ∫ V_j⁰ dv`. -/
theorem alpha_eq : momentMatrix (volume : Measure (PS 1)) V₀ none = ![a₀, 0] := by
  funext j
  rw [momentMatrix_none]
  revert j
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · simpa using int_vf_0
  · simpa using int_vf_1

/-- **Sec. 4** (arXiv 1807.02338): `β = (0, ⁴√(2π))`, where `β_j = ∫ v V_j⁰ dv`.  The paper states
only `β₁ = 0`. -/
theorem beta_eq : momentMatrix (volume : Measure (PS 1)) V₀ (some 0) = ![0, a₀] := by
  funext j
  rw [momentMatrix_some]
  revert j
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · simpa using int_y_vf_0
  · simpa using int_y_vf_1

/-- **Sec. 4** (arXiv 1807.02338): `κ = (2√(π/3), 0)`, where `κ_i = ∫ X_i¹ dx`. -/
theorem kappa_eq : kappa Ωx X₀ = ![2 * √(π / 3), 0] := by
  have h : ∀ i, kappa Ωx X₀ i = ∫ y in (0 : ℝ)..(2 * π), xf i y := fun i => integral_Ωx (xf i)
  have h0 : ∫ y in (0 : ℝ)..(2 * π), xf 0 y = 2 * √(π / 3) := by
    have e : xf 0 = fun y => 2 / √(3 * π) * cos y ^ 2 := rfl
    rw [e, intervalIntegral.integral_const_mul, integral_cos_sq']
    have h3 : √(3 * π) * √(π / 3) = π := by
      rw [← Real.sqrt_mul (by positivity), show 3 * π * (π / 3) = π ^ 2 by ring]
      exact Real.sqrt_sq pi_pos.le
    have h4 : 0 < √(3 * π) := Real.sqrt_pos.2 (by positivity)
    rw [div_mul_eq_mul_div, div_eq_iff h4.ne']
    calc 2 * π = 2 * (√(3 * π) * √(π / 3)) := by rw [h3]
      _ = 2 * √(π / 3) * √(3 * π) := by ring
  have h1 : ∫ y in (0 : ℝ)..(2 * π), xf 1 y = 0 := by
    have e : xf 1 = fun y => 1 / √π * sin (2 * y) := rfl
    rw [e, intervalIntegral.integral_const_mul, integral_sin_two, mul_zero]
  funext i
  rw [h]
  revert i
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · simpa using h0
  · simpa using h1

private lemma inner_pd (i k : Fin 2) :
    ∫ x, X₀ i x * pd 0 (X₀ k) x ∂Ωx = ∫ y in (0 : ℝ)..(2 * π), xf i y * xd k y := by
  simp_rw [pd_X₀]
  exact integral_Ωx fun y => xf i y * xd k y

private lemma sqrt_prod : √(3 * π) * √π = √3 * π := by
  rw [s3p, mul_assoc, sp_mul]

/-- **Sec. 4** (arXiv 1807.02338, implicit in the paper): `⟨X₁¹, ∂ₓX₁¹⟩ = 0`. -/
theorem inner_X₁_dX₁ : ∫ x, X₀ 0 x * pd 0 (X₀ 0) x ∂Ωx = 0 := by
  rw [inner_pd]
  have e : (fun y => xf 0 y * xd 0 y) = fun y =>
      (-(2 / √(3 * π) * (2 / √(3 * π)))) * (cos y ^ 2 * sin (2 * y)) := by
    funext y
    rw [xf_zero, xd_zero]
    ring
  rw [e, intervalIntegral.integral_const_mul, integral_cos_sq_mul_sin_two, mul_zero]

/-- **Sec. 4** (arXiv 1807.02338): `⟨X₁¹, ∂ₓX₂¹⟩` is the multiple `4/(√3 π)` of
`∫₀^{2π} cos²x cos 2x dx`. -/
theorem inner_X₁_dX₂_eq_integral : ∫ x, X₀ 0 x * pd 0 (X₀ 1) x ∂Ωx =
    4 / (√3 * π) * ∫ y in (0 : ℝ)..(2 * π), cos y ^ 2 * cos (2 * y) := by
  rw [inner_pd]
  have e : (fun y => xf 0 y * xd 1 y) = fun y =>
      (2 / √(3 * π) * (2 / √π)) * (cos y ^ 2 * cos (2 * y)) := by
    funext y
    rw [xf_zero, xd_one]
    ring
  rw [e, intervalIntegral.integral_const_mul, div_mul_div_comm, sqrt_prod]
  norm_num

/-- **Sec. 4** (arXiv 1807.02338): `⟨X₁¹, ∂ₓX₂¹⟩ = 2/√3 ≠ 0`. -/
theorem inner_X₁_dX₂ : ∫ x, X₀ 0 x * pd 0 (X₀ 1) x ∂Ωx = c₁ := by
  rw [inner_X₁_dX₂_eq_integral, integral_cos_sq_mul_cos_two, c₁]
  have := pi_pos
  have := s3_pos
  field_simp
  norm_num

/-- **Sec. 4** (arXiv 1807.02338, not in the paper): `⟨X₂¹, ∂ₓX₁¹⟩ = -2/√3`. -/
theorem inner_X₂_dX₁ : ∫ x, X₀ 1 x * pd 0 (X₀ 0) x ∂Ωx = -c₁ := by
  rw [inner_pd]
  have e : (fun y => xf 1 y * xd 0 y) = fun y =>
      (-(1 / √π * (2 / √(3 * π)))) * (sin (2 * y) * sin (2 * y)) := by
    funext y
    rw [xf_one, xd_zero]
    ring
  rw [e, intervalIntegral.integral_const_mul, integral_sin_two_sq, div_mul_div_comm,
    mul_comm √π, sqrt_prod, c₁]
  have := pi_pos
  have := s3_pos
  field_simp

/-- **Sec. 4** (arXiv 1807.02338, not in the paper): `⟨X₂¹, ∂ₓX₂¹⟩ = 0`. -/
theorem inner_X₂_dX₂ : ∫ x, X₀ 1 x * pd 0 (X₀ 1) x ∂Ωx = 0 := by
  rw [inner_pd]
  have e : (fun y => xf 1 y * xd 1 y) = fun y =>
      (1 / √π * (2 / √π)) * (sin (2 * y) * cos (2 * y)) := by
    funext y
    rw [xf_one, xd_one]
    ring
  rw [e, intervalIntegral.integral_const_mul, integral_sin_two_mul_cos_two, mul_zero]

/-- The bound `|X_i| ≤ 2/√(3π) + 1/√π`. -/
private lemma abs_X₀_le : ∀ (i : Fin 2) (x : PS 1), ‖X₀ i x‖ ≤ 2 / √(3 * π) + 1 / √π := by
  have h1 : 0 ≤ 2 / √(3 * π) := by positivity
  have h2 : 0 ≤ 1 / √π := by positivity
  refine Fin.forall_fin_two.2 ⟨fun x => ?_, fun x => ?_⟩
  · have e : X₀ 0 x = 2 / √(3 * π) * cos (x 0) ^ 2 := rfl
    rw [e, norm_mul, Real.norm_of_nonneg h1, Real.norm_of_nonneg (sq_nonneg _)]
    have hc : cos (x 0) ^ 2 ≤ 1 := cos_sq_le_one _
    nlinarith
  · have e : X₀ 1 x = 1 / √π * sin (2 * x 0) := rfl
    rw [e, norm_mul, Real.norm_of_nonneg h2, Real.norm_eq_abs]
    have hc : |sin (2 * x 0)| ≤ 1 := abs_sin_le_one _
    nlinarith

lemma integrable_X_pd (i : Fin 2) (a : Fin 1) (k : Fin 2) :
    Integrable (fun x => X₀ i x * pd a (X₀ k) x) Ωx := by
  have ha : a = 0 := Subsingleton.elim _ _
  subst ha
  simp_rw [pd_X₀]
  exact integrable_Ωx (g := fun y => xf i y * xd k y) ((continuous_xf i).mul (continuous_xd k))

lemma integrable_X_E {E₀ : PS 1 → PS 1} (hE : Integrable (fun x => E₀ x 0) Ωx) (i : Fin 2)
    (b : Fin 1) (k : Fin 2) : Integrable (fun x => X₀ i x * (X₀ k x * E₀ x b)) Ωx := by
  have hb : b = 0 := Subsingleton.elim _ _
  subst hb
  set C : ℝ := 2 / √(3 * π) + 1 / √π with hC
  refine (hE.norm.const_mul (C * C)).mono'
    ((continuous_X₀ i).aestronglyMeasurable.mul
      ((continuous_X₀ k).aestronglyMeasurable.mul hE.aestronglyMeasurable))
    (ae_of_all _ fun x => ?_)
  have h1 := abs_X₀_le i x
  have h2 := abs_X₀_le k x
  have h3 : 0 ≤ C := by positivity
  rw [norm_mul, norm_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) h3) (norm_nonneg _)

end Data

/-! ### The counterexample in Step 3 -/

section Counterexample

open Real

local notation "Ωv" => (volume : Measure (PS 1))

/-- Linear combinations of velocity profiles are velocity profiles. -/
lemma IsVelocityProfile.comb {d : ℕ} {ν : Measure (PS d)} {g h : PS d → ℝ}
    (hg : IsVelocityProfile ν g) (hh : IsVelocityProfile ν h) (a c : ℝ) :
    IsVelocityProfile ν (fun v => a * g v + c * h v) where
  differentiable := (hg.differentiable.const_mul a).add (hh.differentiable.const_mul c)
  integrable := by
    refine ((hg.integrable.const_mul a).add (hh.integrable.const_mul c)).congr
      (ae_of_all _ fun v => ?_)
    simp only [Pi.add_apply]
    ring
  integrable_pd b := by
    have e : ∀ v, pd b (fun v => a * g v + c * h v) v = a * pd b g v + c * pd b h v := fun v => by
      have h1 : HasFDerivAt (fun v => a * g v + c * h v)
          (a • fderiv ℝ g v + c • fderiv ℝ h v) v :=
        ((hg.differentiable v).hasFDerivAt.const_mul a).add
          ((hh.differentiable v).hasFDerivAt.const_mul c)
      rw [pd, h1.fderiv]
      simp [pd]
    simp only [e]
    refine (((hg.integrable_pd b).const_mul a).add ((hh.integrable_pd b).const_mul c)).congr
      (ae_of_all _ fun v => ?_)
    simp only [Pi.add_apply]
    ring

/-- `L_k = ∑_l S_kl V_l⁰`: at the start of Step 3 of the splitting the low-rank function is
`f = ∑ X_k L_k = ∑ X_k S_kl V_l⁰`. -/
noncomputable def coreL (S : Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2) (v : PS 1) : ℝ :=
  ∑ l, S k l * V₀ l v

lemma lowRank_coreK (S : Matrix (Fin 2) (Fin 2) ℝ) :
    lowRank (coreK X₀ S) V₀ = lowRank X₀ (coreL S) := by
  funext x v
  simp only [lowRank, coreK, coreL, Fin.sum_univ_two]
  ring

lemma isVelocityProfile_coreL (S : Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2) :
    IsVelocityProfile Ωv (coreL S k) := by
  have h := (isVelocityProfile_V₀ 0).comb (isVelocityProfile_V₀ 1) (S k 0) (S k 1)
  have e : coreL S k = fun v => S k 0 * V₀ 0 v + S k 1 * V₀ 1 v := by
    funext v
    simp [coreL, Fin.sum_univ_two]
  rw [e]
  exact h

private lemma integrable_pow_vf (n : ℕ) : ∀ j : Fin 2, Integrable fun y => y ^ n * vf j y := by
  have h : ∀ n : ℕ, Integrable (fun y : ℝ => y ^ n * exp (-y ^ 2)) := fun n => by
    simpa using integrable_pow_mul_gauss n (b := 1) one_pos
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · refine ((h n).const_mul (1 / c₀)).congr (ae_of_all _ fun y => ?_)
    simp only [vf_zero]
    ring
  · refine ((h (n + 1)).const_mul (2 / c₀)).congr (ae_of_all _ fun y => ?_)
    simp only [vf_one]
    ring

private lemma integral_weight_coreL {w : ℝ → ℝ} (hw : ∀ j, Integrable fun y => w y * vf j y)
    (S : Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2) :
    ∫ v : PS 1, w (v 0) * coreL S k v =
      S k 0 * (∫ y, w y * vf 0 y) + S k 1 * ∫ y, w y * vf 1 y := by
  have e : (fun v : PS 1 => w (v 0) * coreL S k v) =
      fun v => (fun y => S k 0 * (w y * vf 0 y) + S k 1 * (w y * vf 1 y)) (v 0) := by
    funext v
    simp only [coreL, V₀, Fin.sum_univ_two]
    ring
  rw [e]
  refine (integral_coord fun y => S k 0 * (w y * vf 0 y) + S k 1 * (w y * vf 1 y)).trans ?_
  rw [integral_add ((hw 0).const_mul _) ((hw 1).const_mul _), integral_const_mul,
    integral_const_mul]

/-- `∫ v L₂ dv = S₂₂ ⁴√(2π)` for `L₂ = S₂₁ V₁⁰ + S₂₂ V₂⁰`. -/
lemma integral_v_coreL (S : Matrix (Fin 2) (Fin 2) ℝ) :
    ∫ v : PS 1, v 0 * coreL S 1 v = S 1 1 * a₀ := by
  have h := integral_weight_coreL (w := fun y => y)
    (fun j => by simpa using integrable_pow_vf 1 j) S 1
  simp only at h
  rw [h, int_y_vf_0, int_y_vf_1]
  ring

/-- `∫ v² L₂ dv = S₂₁ ⁴√(2π)/2` for `L₂ = S₂₁ V₁⁰ + S₂₂ V₂⁰`. -/
lemma integral_vv_coreL (S : Matrix (Fin 2) (Fin 2) ℝ) :
    ∫ v : PS 1, v 0 * v 0 * coreL S 1 v = S 1 0 * (a₀ / 2) := by
  have h := integral_weight_coreL (w := fun y => y * y)
    (fun j => by simpa [sq] using integrable_pow_vf 2 j) S 1
  simp only at h
  rw [h, int_yy_vf_0, int_yy_vf_1]
  ring

variable {E₀ : PS 1 → PS 1}

lemma rhsL_eq_zero (hE : Integrable (fun x => E₀ x 0) Ωx) {L : Fin 2 → PS 1 → ℝ}
    (hL : ∀ k, IsVelocityProfile Ωv (L k)) (m : Option (Fin 1)) (i : Fin 2) :
    rhsL Ωx Ωv X₀ E₀ (lowRank X₀ L) m i = 0 :=
  rhsL_lowRank_eq_zero hL differentiable_X₀ i (integrable_X_pd i) (integrable_X_E hE i) m

/-- **Sec. 4** (arXiv 1807.02338): `⟨X₁¹, F(f)⟩ₓᵥ = -(2/√3) ∫ v L₂ dv` for `f = X₁¹ L₁ + X₂¹ L₂` and
any field `E`.  This is the correct form of the identity in Sec. 4, see `printed_identity_iff`.  The
field drops out by integration by parts in `v`. -/
theorem innerF_X₁ (hE : Integrable (fun x => E₀ x 0) Ωx) {L : Fin 2 → PS 1 → ℝ}
    (hL : ∀ k, IsVelocityProfile Ωv (L k)) :
    innerF Ωx Ωv X₀ E₀ (lowRank X₀ L) none 0 = -(c₁ * ∫ v, v 0 * L 1 v) := by
  rw [innerF_none_lowRank hL differentiable_X₀ 0 (integrable_X_pd 0) (integrable_X_E hE 0)]
  simp only [Fin.sum_univ_one, Fin.sum_univ_two, inner_X₁_dX₁, inner_X₁_dX₂, zero_mul, zero_add]

/-- **Sec. 4, "Thus, `λ₁₁ = 0`"** (arXiv 1807.02338).  The local mass constraint forces
`λ_i1 = 0` for both `i`, since `α₂ = 0` and `b_i = 0`.  Here `f = ∑ X_k L_k`, with `L_k` arbitrary
velocity profiles, and `E` is any field. -/
theorem local_forces_lam (hE : Integrable (fun x => E₀ x 0) Ωx) {L : Fin 2 → PS 1 → ℝ}
    (hL : ∀ k, IsVelocityProfile Ωv (L k)) {lam : Matrix (Fin 2) (Fin 2) ℝ}
    (h : LocalConstraint Ωx Ωv X₀ V₀ E₀ (lowRank X₀ L) none lam) (i : Fin 2) : lam i 0 = 0 := by
  have h1 := h i
  rw [rhsL_eq_zero hE hL, Fin.sum_univ_two, alpha_eq] at h1
  simpa [a₀_pos.ne'] using h1

/-- **Sec. 4, option "local"** (arXiv 1807.02338): the zero correction solves the local constraints,
of mass and of momentum, in Step 3. -/
theorem localConstraint_zero (hE : Integrable (fun x => E₀ x 0) Ωx) {L : Fin 2 → PS 1 → ℝ}
    (hL : ∀ k, IsVelocityProfile Ωv (L k)) (m : Option (Fin 1)) :
    LocalConstraint Ωx Ωv X₀ V₀ E₀ (lowRank X₀ L) m 0 := fun i => by
  rw [rhsL_eq_zero hE hL]
  simp

/-- **Sec. 4, option "global"** (arXiv 1807.02338): the global mass constraint alone is solvable for
every `f`, by a correction `λ₁₁` alone.  Only the combination of the two systems is inconsistent.
The paper does not state solvability. -/
theorem globalConstraint_solvable (E₀ : PS 1 → PS 1) (f : PS 1 → PS 1 → ℝ) :
    ∃ lam, GlobalConstraint Ωx Ωv X₀ V₀ E₀ f none lam := by
  refine ⟨!![-innerF Ωx Ωv X₀ E₀ f none 0 / a₀, 0; 0, 0], ?_⟩
  simp only [GlobalConstraint, Fin.sum_univ_two, kappa_eq, alpha_eq]
  simp
  field_simp [a₀_pos.ne']
  ring

/-- **Sec. 4, local and global mass conservation** (arXiv 1807.02338).  For the functions of Sec. 4
and `f = X₁¹ L₁ + X₂¹ L₂` with arbitrary velocity profiles `L_k` and any field `E`, a correction
that satisfies both the local constraints and the global constraint exists exactly when
`∫ v L₂ dv = 0`. -/
theorem exists_local_global_mass_iff (hE : Integrable (fun x => E₀ x 0) Ωx)
    {L : Fin 2 → PS 1 → ℝ} (hL : ∀ k, IsVelocityProfile Ωv (L k)) :
    (∃ lam, LocalConstraint Ωx Ωv X₀ V₀ E₀ (lowRank X₀ L) none lam ∧
      GlobalConstraint Ωx Ωv X₀ V₀ E₀ (lowRank X₀ L) none lam) ↔ ∫ v, v 0 * L 1 v = 0 := by
  rw [exists_local_global_iff (rhsL_eq_zero hE hL none), Fin.sum_univ_two, innerF_X₁ hE hL,
    kappa_eq]
  have hk : 0 < √(π / 3) := Real.sqrt_pos.2 (by positivity)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, add_zero]
  constructor
  · intro h
    have h1 := (mul_eq_zero.1 h).resolve_left (mul_pos two_pos hk).ne'
    exact (mul_eq_zero.1 (neg_eq_zero.1 h1)).resolve_left c₁_pos.ne'
  · intro h
    rw [h]
    ring

/-- **Sec. 4, local and global mass conservation for `f = ∑ X_i S_ij V_j`** (arXiv 1807.02338).
With `f = ∑ X_i¹ S_ij V_j⁰` for the functions of Sec. 4 and any field `E`, there is a correction
satisfying the local constraints and the global constraint if and only if `S₂₂ = 0`. -/
theorem exists_local_global_mass_iff_S (hE : Integrable (fun x => E₀ x 0) Ωx)
    (S : Matrix (Fin 2) (Fin 2) ℝ) :
    (∃ lam, LocalConstraint Ωx Ωv X₀ V₀ E₀ (lowRank (coreK X₀ S) V₀) none lam ∧
      GlobalConstraint Ωx Ωv X₀ V₀ E₀ (lowRank (coreK X₀ S) V₀) none lam) ↔ S 1 1 = 0 := by
  rw [lowRank_coreK, exists_local_global_mass_iff hE (isVelocityProfile_coreL S),
    integral_v_coreL]
  simp [a₀_pos.ne']

/-- **Sec. 4, the counterexample** (arXiv 1807.02338): "it is not possible to both satisfy the
continuity equation and obtain global conservation of mass".  Take `Ω_x = [0, 2π]`, `Ω_v = ℝ`, the
rank-2 functions `X₁¹, X₂¹, V₁⁰, V₂⁰` of Sec. 4, any field `E`, and `f = ∑ X_i¹ S_ij V_j⁰`.  If a
correction `λ` satisfies the local mass constraint, then `λ₁₁ = 0`, and it violates the global
mass constraint.

Difference from the paper: we need the hypothesis `S₂₂ ≠ 0`, which the paper does not state.  It
cannot be dropped, see `exists_local_global_mass_iff_S` and `compatible_of_S₂₂_eq_zero`. -/
theorem sec4_counterexample (hE : Integrable (fun x => E₀ x 0) Ωx)
    (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : S 1 1 ≠ 0) {lam : Matrix (Fin 2) (Fin 2) ℝ}
    (hloc : LocalConstraint Ωx Ωv X₀ V₀ E₀ (lowRank (coreK X₀ S) V₀) none lam) :
    lam 0 0 = 0 ∧ ¬ GlobalConstraint Ωx Ωv X₀ V₀ E₀ (lowRank (coreK X₀ S) V₀) none lam := by
  refine ⟨?_, fun hglob => hS ((exists_local_global_mass_iff_S hE S).1 ⟨lam, hloc, hglob⟩)⟩
  rw [lowRank_coreK] at hloc
  exact local_forces_lam hE (isVelocityProfile_coreL S) hloc 0

/-- The hypotheses of `sec4_counterexample` hold: `S = 1`, `E = 0` and `λ = 0`. -/
example : ¬ GlobalConstraint Ωx Ωv X₀ V₀ 0 (lowRank (coreK X₀ 1) V₀) none 0 :=
  (sec4_counterexample (by simp) 1 (by simp) (by
    rw [lowRank_coreK]
    exact localConstraint_zero (by simp) (isVelocityProfile_coreL 1) none)).2

/-- **Sec. 4, the term `⟨X₁¹, F(f)⟩ₓᵥ` in terms of the integral** (arXiv 1807.02338).  For
`f = ∑ X_i¹ S_ij V_j⁰` and any field,
`⟨X₁¹, F(f)⟩ₓᵥ = -(4/(√3 π)) (∫₀^{2π} cos²x cos 2x dx) S₂₂ ⁴√(2π)`.  This is the proportionality
in Sec. 4 with its constant, which contains the factor `S₂₂` that the paper omits. -/
theorem innerF_X₁_eq_integral (hE : Integrable (fun x => E₀ x 0) Ωx)
    (S : Matrix (Fin 2) (Fin 2) ℝ) :
    innerF Ωx Ωv X₀ E₀ (lowRank (coreK X₀ S) V₀) none 0 =
      -(4 / (√3 * π) * (∫ y in (0 : ℝ)..(2 * π), cos y ^ 2 * cos (2 * y)) * S 1 1 * a₀) := by
  have h := inner_X₁_dX₂
  rw [inner_X₁_dX₂_eq_integral] at h
  rw [h, lowRank_coreK, innerF_X₁ hE (isVelocityProfile_coreL S), integral_v_coreL]
  ring

/-- **The formula in Sec. 4 is wrong as printed** (arXiv 1807.02338).  The paper writes
`⟨X₁¹, F(f)⟩ₓᵥ = ⟨X₁¹, ∇X₂¹⟩ · β₂`.  The correct value is `-⟨X₁¹, ∇X₂¹⟩ S₂₂ β₂`
(`innerF_X₁`, `integral_v_coreL`), so the printed formula holds exactly when `S₂₂ = -1`. -/
theorem printed_identity_iff (hE : Integrable (fun x => E₀ x 0) Ωx)
    (S : Matrix (Fin 2) (Fin 2) ℝ) :
    innerF Ωx Ωv X₀ E₀ (lowRank (coreK X₀ S) V₀) none 0 =
        (∫ x, X₀ 0 x * pd 0 (X₀ 1) x ∂Ωx) * momentMatrix Ωv V₀ (some 0) 1 ↔ S 1 1 = -1 := by
  rw [lowRank_coreK, innerF_X₁ hE (isVelocityProfile_coreL S), integral_v_coreL, inner_X₁_dX₂,
    beta_eq]
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have h : c₁ * a₀ ≠ 0 := (mul_pos c₁_pos a₀_pos).ne'
  constructor
  · intro e
    have : (c₁ * a₀) * (S 1 1 + 1) = 0 := by linear_combination -e
    have := (mul_eq_zero.1 this).resolve_left h
    linarith
  · intro e
    rw [e]
    ring

/-- **The hypothesis `S₂₂ ≠ 0` cannot be dropped** (arXiv 1807.02338).  For the invertible matrix
`S = [0 1; 1 0]`, so for a genuinely rank-2 function `f` built from the functions of Sec. 4, the
local and the global mass constraints do have a common solution, namely `λ = 0`. -/
theorem compatible_of_S₂₂_eq_zero (hE : Integrable (fun x => E₀ x 0) Ωx) :
    ∃ S : Matrix (Fin 2) (Fin 2) ℝ, S.det ≠ 0 ∧
      ∃ lam, LocalConstraint Ωx Ωv X₀ V₀ E₀ (lowRank (coreK X₀ S) V₀) none lam ∧
        GlobalConstraint Ωx Ωv X₀ V₀ E₀ (lowRank (coreK X₀ S) V₀) none lam :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two],
    (exists_local_global_mass_iff_S hE _).2 (by simp)⟩

/-- **Sec. 4, momentum** (arXiv 1807.02338, not in the paper):
`⟨v X₁¹, F(f)⟩ₓᵥ = -(2/√3) ∫ v² L₂ dv - ⟨X₁¹, E ρ⟩ₓ` for `f = X₁¹ L₁ + X₂¹ L₂`. -/
theorem innerF_vX₁ (hE : Integrable (fun x => E₀ x 0) Ωx) {L : Fin 2 → PS 1 → ℝ}
    (hL : ∀ k, IsVelocityProfile Ωv (L k)) :
    innerF Ωx Ωv X₀ E₀ (lowRank X₀ L) (some 0) 0 =
      -(c₁ * ∫ v, v 0 * v 0 * L 1 v) - ∫ x, X₀ 0 x * (E₀ x 0 * rho Ωv (lowRank X₀ L) x) ∂Ωx := by
  rw [innerF_some_lowRank hL differentiable_X₀ 0 (integrable_X_pd 0) (integrable_X_E hE 0) 0]
  simp only [Fin.sum_univ_one, Fin.sum_univ_two, inner_X₁_dX₁, inner_X₁_dX₂, zero_mul, zero_add]

/-- **Sec. 4, the momentum analogue** (arXiv 1807.02338; the paper only remarks that momentum
behaves in the same way).  For the functions of Sec. 4, a correction satisfying the local and the
global momentum constraint exists exactly when
`(2/√3) ∫ v² L₂ dv + ⟨X₁¹, E ρ⟩ₓ = 0`.  The local system uses the correct sign of `Eρ`. -/
theorem exists_local_global_momentum_iff (hE : Integrable (fun x => E₀ x 0) Ωx)
    {L : Fin 2 → PS 1 → ℝ} (hL : ∀ k, IsVelocityProfile Ωv (L k)) :
    (∃ lam, LocalConstraint Ωx Ωv X₀ V₀ E₀ (lowRank X₀ L) (some 0) lam ∧
      GlobalConstraint Ωx Ωv X₀ V₀ E₀ (lowRank X₀ L) (some 0) lam) ↔
      c₁ * (∫ v, v 0 * v 0 * L 1 v) +
        ∫ x, X₀ 0 x * (E₀ x 0 * rho Ωv (lowRank X₀ L) x) ∂Ωx = 0 := by
  rw [exists_local_global_iff (rhsL_eq_zero hE hL (some 0)), Fin.sum_univ_two, innerF_vX₁ hE hL,
    kappa_eq]
  have hk : 0 < √(π / 3) := Real.sqrt_pos.2 (by positivity)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, add_zero]
  constructor
  · intro h
    have := (mul_eq_zero.1 h).resolve_left (mul_pos two_pos hk).ne'
    linarith
  · intro h
    have : -(c₁ * ∫ v, v 0 * v 0 * L 1 v) -
        ∫ x, X₀ 0 x * (E₀ x 0 * rho Ωv (lowRank X₀ L) x) ∂Ωx = 0 := by linarith
    rw [this, mul_zero]

/-- **Sec. 4, momentum, with a concrete condition** (arXiv 1807.02338, not in the paper).  For
`f = ∑ X_i¹ S_ij V_j⁰` and `E = 0` the local and global momentum constraints have a common solution
exactly when `S₂₁ = 0`. -/
theorem exists_local_global_momentum_iff_S (S : Matrix (Fin 2) (Fin 2) ℝ) :
    (∃ lam, LocalConstraint Ωx Ωv X₀ V₀ 0 (lowRank (coreK X₀ S) V₀) (some 0) lam ∧
      GlobalConstraint Ωx Ωv X₀ V₀ 0 (lowRank (coreK X₀ S) V₀) (some 0) lam) ↔ S 1 0 = 0 := by
  have hE : Integrable (fun x => (0 : PS 1 → PS 1) x 0) Ωx := by simp
  rw [lowRank_coreK, exists_local_global_momentum_iff hE (isVelocityProfile_coreL S),
    integral_vv_coreL]
  simp [a₀_pos.ne', c₁_pos.ne']

/-- **Sec. 4, Step 3** (arXiv 1807.02338, not in the paper).  For the functions of Sec. 4 the two
local systems together have the only solution `λ = 0`, since `[α; β]` is `⁴√(2π)` times the
identity.  So in Step 3, with the correct sign of `Eρ`, there is no room for any correction once
both local laws are imposed. -/
theorem local_forces_zero (hE : Integrable (fun x => E₀ x 0) Ωx) {L : Fin 2 → PS 1 → ℝ}
    (hL : ∀ k, IsVelocityProfile Ωv (L k)) {lam : Matrix (Fin 2) (Fin 2) ℝ}
    (h₁ : LocalConstraint Ωx Ωv X₀ V₀ E₀ (lowRank X₀ L) none lam)
    (h₂ : LocalConstraint Ωx Ωv X₀ V₀ E₀ (lowRank X₀ L) (some 0) lam) : lam = 0 := by
  have h0 := local_forces_lam hE hL h₁
  have h1 : ∀ i, lam i 1 = 0 := fun i => by
    have h3 := h₂ i
    rw [rhsL_eq_zero hE hL, Fin.sum_univ_two, beta_eq] at h3
    simpa [a₀_pos.ne'] using h3
  ext i j
  revert j
  exact Fin.forall_fin_two.2 ⟨h0 i, h1 i⟩

end Counterexample

/-! ### The counterexample for solutions of the corrected L-step -/

section Dynamic

open Real

local notation "Ωv" => (volume : Measure (PS 1))

variable {E : ℝ → PS 1 → PS 1} {t : ℝ} {L : ℝ → Fin 2 → PS 1 → ℝ}
  {lam : ℝ → Matrix (Fin 2) (Fin 2) ℝ}

lemma integrable_wt_V₀ (m : Option (Fin 1)) (j : Fin 2) :
    Integrable (fun v => wt m v * V₀ j v) Ωv :=
  (isVelocityProfile_V₀ j).integrable_wt m

private lemma kappa_mul_c₁ : 2 * √(π / 3) * c₁ = 4 * √π / 3 := by
  rw [Real.sqrt_div pi_pos.le, c₁]
  calc 2 * (√π / √3) * (2 / √3) = 4 * √π / (√3 * √3) := by ring
    _ = 4 * √π / 3 := by rw [s3_mul]

/-- **Sec. 4, the counterexample as a statement on solutions** (arXiv 1807.02338).  Let `L` solve
the corrected L-step `∂ₜL_i = ⟨X_i, F(f)⟩ₓ + ∑_l λ_il V_l` at time `t`, for the functions of Sec. 4,
any field `E(t)` and any correction `λ(t)`, and assume that the projected continuity equation
`P_X̄ (∂ₜρ + ∇·(ρu)) = 0` holds at time `t`.  Then the total mass changes at the exact rate
`d/dt ∫∫ f dv dx = -(4√π/3) ∫ v L₂ dv`, whatever `λ` is. -/
theorem lStep_mass_drift (hE : Integrable (fun x => E t x 0) Ωx)
    (hprof : ∀ k, IsVelocityProfile Ωv (L t k))
    (hL : ∀ k, IsDominatedCurve Ωv (fun s => L s k) (fun s v =>
      (∫ x, X₀ k x * vlasovF (E s) (lowRank X₀ (L s)) x v ∂Ωx) + ∑ l, lam s k l * V₀ l v) t)
    (hloc : proj Ωx X₀ (fun x => deriv (fun s => rho Ωv (lowRank X₀ (L s)) x) t +
      divMomentum Ωv (lowRank X₀ (L t)) x) = 0) :
    HasDerivAt (fun s => ∫ x, rho Ωv (lowRank X₀ (L s)) x ∂Ωx)
      (-(4 * √π / 3 * ∫ v, v 0 * L t 1 v)) t := by
  have hlam := (lStep_projectedContinuity_iff isOrthonormalL2_X₀ integrable_wt_V₀
    differentiable_X₀ integrable_X_pd (fun i => integrable_X_E hE i) hprof hL).1 hloc
  have hrhs := rhsL_eq_zero hE hprof none
  have hlocal : LocalConstraint Ωx Ωv X₀ V₀ (E t) (lowRank X₀ (L t)) none (lam t) := fun i => by
    rw [hlam i, hrhs i]
  have h := lStep_global_hasDerivAt isOrthonormalL2_X₀ integrable_wt_V₀ hL none
  simp only [moment_none] at h
  rw [sum_kappa_lam_eq_zero hrhs hlocal, zero_add, Fin.sum_univ_two, innerF_X₁ hE hprof,
    kappa_eq] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul,
    add_zero] at h
  convert h using 1
  rw [← kappa_mul_c₁]
  ring

/-- **Sec. 4, "it is not possible to both satisfy the continuity equation and obtain global
conservation of mass"** (arXiv 1807.02338), for solutions.  If `L` solves the corrected L-step at
time `t` and `∫ v L₂ dv ≠ 0`, then no correction `λ` gives both the projected continuity equation
and a vanishing time derivative of the total mass.  The hypotheses hold for the exact solution
`rotL`, see `rotL_mass_not_conserved`. -/
theorem lStep_not_continuity_and_mass (hE : Integrable (fun x => E t x 0) Ωx)
    (hprof : ∀ k, IsVelocityProfile Ωv (L t k))
    (hL : ∀ k, IsDominatedCurve Ωv (fun s => L s k) (fun s v =>
      (∫ x, X₀ k x * vlasovF (E s) (lowRank X₀ (L s)) x v ∂Ωx) + ∑ l, lam s k l * V₀ l v) t)
    (hj : ∫ v, v 0 * L t 1 v ≠ 0) :
    ¬ (proj Ωx X₀ (fun x => deriv (fun s => rho Ωv (lowRank X₀ (L s)) x) t +
        divMomentum Ωv (lowRank X₀ (L t)) x) = 0 ∧
      HasDerivAt (fun s => ∫ x, rho Ωv (lowRank X₀ (L s)) x ∂Ωx) 0 t) := by
  rintro ⟨hloc, h0⟩
  have h := (lStep_mass_drift hE hprof hL hloc).unique h0
  have hp : (0 : ℝ) < 4 * √π / 3 := by
    have := sp_pos
    positivity
  exact hj ((mul_eq_zero.1 (neg_eq_zero.1 h)).resolve_left hp.ne')

/-! #### An exact solution -/

/-- An exact solution of the L-step for the functions of Sec. 4 with `E = 0`, `λ = 0`, starting
from `f = X₁¹ V₁⁰ + X₂¹ V₂⁰`, that is `S = 1`.  Since `⟨X₁, ∂ₓX₂⟩ = 2/√3 = -⟨X₂, ∂ₓX₁⟩`, the L-step
`∂ₜL₁ = -(2/√3) v L₂`, `∂ₜL₂ = (2/√3) v L₁` rotates `(L₁, L₂)` by the angle `(2/√3) v t`. -/
noncomputable def rotL (s : ℝ) : Fin 2 → PS 1 → ℝ :=
  ![fun v => cos (c₁ * v 0 * s) * V₀ 0 v - sin (c₁ * v 0 * s) * V₀ 1 v,
    fun v => sin (c₁ * v 0 * s) * V₀ 0 v + cos (c₁ * v 0 * s) * V₀ 1 v]

/-- The right-hand side of the L-step along `rotL`. -/
noncomputable def rotD (s : ℝ) (k : Fin 2) (v : PS 1) : ℝ :=
  ![-(c₁ * v 0 * rotL s 1 v), c₁ * v 0 * rotL s 0 v] k

private lemma rotL_zero (s : ℝ) (v : PS 1) :
    rotL s 0 v = cos (c₁ * v 0 * s) * V₀ 0 v - sin (c₁ * v 0 * s) * V₀ 1 v := rfl

private lemma rotL_one (s : ℝ) (v : PS 1) :
    rotL s 1 v = sin (c₁ * v 0 * s) * V₀ 0 v + cos (c₁ * v 0 * s) * V₀ 1 v := rfl

private lemma rotD_zero (s : ℝ) (v : PS 1) : rotD s 0 v = -(c₁ * v 0 * rotL s 1 v) := rfl

private lemma rotD_one (s : ℝ) (v : PS 1) : rotD s 1 v = c₁ * v 0 * rotL s 0 v := rfl

lemma rotL_at_zero : ∀ (k : Fin 2) (v : PS 1), rotL 0 k v = V₀ k v := by
  refine Fin.forall_fin_two.2 ⟨fun v => ?_, fun v => ?_⟩
  · simp [rotL_zero]
  · simp [rotL_one]

lemma differentiable_V₀ (j : Fin 2) : Differentiable ℝ (V₀ j) := fun v =>
  (hasFDerivAt_coord (hasDerivAt_vf j (v 0))).differentiableAt

private lemma differentiable_angle (s : ℝ) : Differentiable ℝ fun v : PS 1 => c₁ * v 0 * s :=
  (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1) : PS 1 →L[ℝ] ℝ).differentiable).const_mul
    c₁).mul_const s

lemma differentiable_rotL (s : ℝ) : ∀ k, Differentiable ℝ (rotL s k) := by
  have hc := differentiable_angle s
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · exact (hc.cos.mul (differentiable_V₀ 0)).sub (hc.sin.mul (differentiable_V₀ 1))
  · exact (hc.sin.mul (differentiable_V₀ 0)).add (hc.cos.mul (differentiable_V₀ 1))

lemma continuous_rotL (s : ℝ) (k : Fin 2) : Continuous (rotL s k) :=
  (differentiable_rotL s k).continuous

/-- `⟨X_k, F(f)⟩ₓ` along `rotL`. -/
lemma integral_X_vlasovF_rot (s : ℝ) (k : Fin 2) (v : PS 1) :
    ∫ x, X₀ k x * vlasovF 0 (lowRank X₀ (rotL s)) x v ∂Ωx = rotD s k v := by
  have he : ∀ i b k, Integrable (fun x : PS 1 => X₀ i x * (X₀ k x * (0 : PS 1 → PS 1) x b)) Ωx :=
    fun i b k => by simp
  rw [integral_X_vlasovF differentiable_X₀ (differentiable_rotL s) k (integrable_X_pd k) (he k) v]
  revert k
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · simp only [Fin.sum_univ_one, Fin.sum_univ_two, inner_X₁_dX₁, inner_X₁_dX₂, rotD_zero]
    simp
    ring
  · simp only [Fin.sum_univ_one, Fin.sum_univ_two, inner_X₂_dX₁, inner_X₂_dX₂, rotD_one]
    simp
    ring

/-- The Gaussian majorant. -/
private noncomputable def bd (y : ℝ) : ℝ := 4 * (1 + y ^ 2) ^ 2 * exp (-y ^ 2) / c₀

private lemma integrable_bd : Integrable bd := by
  refine ((integrable_poly_gauss 4 0 8 0 4).div_const c₀).congr (ae_of_all _ fun y => ?_)
  simp only [bd]
  ring

private lemma abs_vf_add_le (y : ℝ) :
    |vf 0 y| + |vf 1 y| ≤ 2 * (1 + y ^ 2) * exp (-y ^ 2) / c₀ := by
  have he : 0 < exp (-y ^ 2) / c₀ := div_pos (exp_pos _) c₀_pos
  have h0 : vf 0 y = exp (-y ^ 2) / c₀ := rfl
  have h1 : vf 1 y = 2 * y * (exp (-y ^ 2) / c₀) := by
    rw [vf_one]
    ring
  have e : 2 * (1 + y ^ 2) * exp (-y ^ 2) / c₀ = 2 * (1 + y ^ 2) * (exp (-y ^ 2) / c₀) := by ring
  rw [h0, h1, e, abs_mul, abs_of_pos he, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2)]
  have hy : 2 * |y| ≤ 1 + y ^ 2 := by
    nlinarith [sq_abs y, sq_nonneg (|y| - 1)]
  nlinarith [sq_nonneg y]

private lemma abs_comb_le (C S a b : ℝ) (hC : |C| ≤ 1) (hS : |S| ≤ 1) :
    |C * a + S * b| ≤ |a| + |b| := by
  calc |C * a + S * b| ≤ |C * a| + |S * b| := abs_add_le _ _
    _ = |C| * |a| + |S| * |b| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * |a| + 1 * |b| := by gcongr
    _ = |a| + |b| := by ring

private lemma abs_rotL_le (s : ℝ) : ∀ (k : Fin 2) (v : PS 1),
    |rotL s k v| ≤ 2 * (1 + v 0 ^ 2) * exp (-v 0 ^ 2) / c₀ := by
  refine Fin.forall_fin_two.2 ⟨fun v => ?_, fun v => ?_⟩
  · have h := abs_comb_le (cos (c₁ * v 0 * s)) (-sin (c₁ * v 0 * s)) (V₀ 0 v) (V₀ 1 v)
      (abs_cos_le_one _) (by rw [abs_neg]; exact abs_sin_le_one _)
    have e : rotL s 0 v = cos (c₁ * v 0 * s) * V₀ 0 v + -sin (c₁ * v 0 * s) * V₀ 1 v := by
      rw [rotL_zero]
      ring
    rw [e]
    exact h.trans (abs_vf_add_le (v 0))
  · have h := abs_comb_le (sin (c₁ * v 0 * s)) (cos (c₁ * v 0 * s)) (V₀ 0 v) (V₀ 1 v)
      (abs_sin_le_one _) (abs_cos_le_one _)
    exact h.trans (abs_vf_add_le (v 0))

private lemma one_add_abs_le (y : ℝ) : 1 + |y| ≤ 2 * (1 + y ^ 2) := by
  nlinarith [sq_abs y, sq_nonneg (|y| - 1), abs_nonneg y]

private lemma mul_abs_le_bd {y R : ℝ} (hR : |R| ≤ 2 * (1 + y ^ 2) * exp (-y ^ 2) / c₀) :
    (1 + |y|) * |R| ≤ bd y := by
  have hp : (0 : ℝ) ≤ 2 * (1 + y ^ 2) := by positivity
  calc (1 + |y|) * |R| ≤ (2 * (1 + y ^ 2)) * (2 * (1 + y ^ 2) * exp (-y ^ 2) / c₀) :=
        mul_le_mul (one_add_abs_le y) hR (abs_nonneg _) hp
    _ = bd y := by
      simp only [bd]
      ring

private lemma mul_abs_D_le {y R : ℝ} (hR : |R| ≤ 2 * (1 + y ^ 2) * exp (-y ^ 2) / c₀) :
    (1 + |y|) * |c₁ * y * R| ≤ c₁ * bd y := by
  have hp : (0 : ℝ) ≤ 2 * (1 + y ^ 2) := by positivity
  have hy : (1 + |y|) * |y| ≤ 2 * (1 + y ^ 2) := by
    nlinarith [sq_abs y, sq_nonneg (|y| - 1), abs_nonneg y]
  have hc : |c₁| = c₁ := abs_of_pos c₁_pos
  rw [abs_mul, abs_mul, hc]
  calc (1 + |y|) * (c₁ * |y| * |R|) = c₁ * (((1 + |y|) * |y|) * |R|) := by ring
    _ ≤ c₁ * ((2 * (1 + y ^ 2)) * (2 * (1 + y ^ 2) * exp (-y ^ 2) / c₀)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hy hR (abs_nonneg _) hp) c₁_pos.le
    _ = c₁ * bd y := by
      simp only [bd]
      ring

private lemma hasDerivAt_rotL : ∀ (k : Fin 2) (v : PS 1) (s : ℝ),
    HasDerivAt (fun τ => rotL τ k v) (rotD s k v) s := by
  have ha : ∀ (v : PS 1) (s : ℝ), HasDerivAt (fun τ : ℝ => c₁ * v 0 * τ) (c₁ * v 0) s :=
    fun v s => by simpa using (hasDerivAt_id s).const_mul (c₁ * v 0)
  refine Fin.forall_fin_two.2 ⟨fun v s => ?_, fun v s => ?_⟩
  · have h := ((ha v s).cos.mul_const (V₀ 0 v)).sub ((ha v s).sin.mul_const (V₀ 1 v))
    refine h.congr_deriv ?_
    rw [rotD_zero, rotL_one]
    ring
  · have h := ((ha v s).sin.mul_const (V₀ 0 v)).add ((ha v s).cos.mul_const (V₀ 1 v))
    refine h.congr_deriv ?_
    rw [rotD_one, rotL_zero]
    ring

private lemma abs_rotD_le (s : ℝ) : ∀ (k : Fin 2) (v : PS 1),
    (1 + ‖v‖) * |rotD s k v| ≤ c₁ * bd (v 0) := by
  refine Fin.forall_fin_two.2 ⟨fun v => ?_, fun v => ?_⟩
  · rw [rotD_zero, abs_neg, norm_coord]
    exact mul_abs_D_le (abs_rotL_le s 1 v)
  · rw [rotD_one, norm_coord]
    exact mul_abs_D_le (abs_rotL_le s 0 v)

lemma isDominatedCurve_rotD (k : Fin 2) (t : ℝ) :
    IsDominatedCurve Ωv (fun s => rotL s k) (fun s v => rotD s k v) t := by
  refine ⟨Eventually.of_forall fun s => ?_, ?_, 1, one_pos, fun v => c₁ * bd (v 0),
    (integrable_coord integrable_bd).const_mul _, ae_of_all _ fun v s _ =>
      ⟨hasDerivAt_rotL k v s, abs_rotD_le s k v⟩⟩
  · refine (integrable_coord integrable_bd).mono'
      (Continuous.aestronglyMeasurable ((by fun_prop : Continuous fun v : PS 1 => 1 + ‖v‖).mul
        (continuous_rotL s k))) (ae_of_all _ fun v => ?_)
    rw [norm_mul, Real.norm_eq_abs (rotL s k v), Real.norm_of_nonneg (by positivity), norm_coord]
    exact mul_abs_le_bd (abs_rotL_le s k v)
  · have hc : Continuous fun v : PS 1 => rotD t k v := by
      revert k
      refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
      · exact (by
          have := continuous_rotL t 1
          fun_prop : Continuous fun v : PS 1 => -(c₁ * v 0 * rotL t 1 v))
      · exact (by
          have := continuous_rotL t 0
          fun_prop : Continuous fun v : PS 1 => c₁ * v 0 * rotL t 0 v)
    exact hc.aestronglyMeasurable

/-- `rotL` solves the L-step (2.7), which is (3.12) with `λ = 0`, for `E = 0`. -/
lemma isDominatedCurve_rotL (k : Fin 2) (t : ℝ) :
    IsDominatedCurve Ωv (fun s => rotL s k) (fun s v =>
      (∫ x, X₀ k x * vlasovF ((fun _ => (0 : PS 1 → PS 1)) s) (lowRank X₀ (rotL s)) x v ∂Ωx) +
        ∑ l, ((fun _ => (0 : Matrix (Fin 2) (Fin 2) ℝ)) s) k l * V₀ l v) t := by
  have e : (fun (s : ℝ) (v : PS 1) =>
      (∫ x, X₀ k x * vlasovF ((fun _ => (0 : PS 1 → PS 1)) s) (lowRank X₀ (rotL s)) x v ∂Ωx) +
        ∑ l, ((fun _ => (0 : Matrix (Fin 2) (Fin 2) ℝ)) s) k l * V₀ l v) =
      fun s v => rotD s k v := by
    funext s v
    simp only [integral_X_vlasovF_rot]
    simp
  rw [e]
  exact isDominatedCurve_rotD k t

/-- **Sec. 4, an instance of the failure of global mass conservation** (arXiv 1807.02338).  The
exact solution `rotL` of the L-step with `E = 0`, `λ = 0`, starting at `f = X₁¹ V₁⁰ + X₂¹ V₂⁰`,
satisfies the projected continuity equation at time `0`, and yet its total mass has the nonzero
derivative `-(4√π/3) ⁴√(2π)` there.  This shows that the hypotheses of `lStep_mass_drift` and
`lStep_not_continuity_and_mass` hold for an actual solution. -/
theorem rotL_mass_not_conserved :
    (∀ k v, rotL 0 k v = V₀ k v) ∧
      proj Ωx X₀ (fun x => deriv (fun s => rho Ωv (lowRank X₀ (rotL s)) x) 0 +
        divMomentum Ωv (lowRank X₀ (rotL 0)) x) = 0 ∧
      HasDerivAt (fun s => ∫ x, rho Ωv (lowRank X₀ (rotL s)) x ∂Ωx) (-(4 * √π / 3 * a₀)) 0 := by
  have hr : ∀ k, rotL 0 k = V₀ k := fun k => funext (rotL_at_zero k)
  have hprof : ∀ k, IsVelocityProfile Ωv (rotL 0 k) := fun k => by
    rw [hr]
    exact isVelocityProfile_V₀ k
  have hE : Integrable (fun x => ((fun _ => (0 : PS 1 → PS 1)) (0 : ℝ)) x 0) Ωx := by simp
  have hL : ∀ k, _ := fun k => isDominatedCurve_rotL k 0
  have hloc := (lStep_projectedContinuity_iff isOrthonormalL2_X₀ integrable_wt_V₀
    differentiable_X₀ integrable_X_pd (fun i => integrable_X_E hE i) hprof hL).2 (fun i => by simp)
  refine ⟨rotL_at_zero, hloc, ?_⟩
  have h := lStep_mass_drift hE hprof hL hloc
  have hj : ∫ v : PS 1, v 0 * rotL 0 1 v = a₀ := by
    rw [hr]
    have := congrFun beta_eq 1
    simpa [momentMatrix] using this
  rwa [hj] at h

end Dynamic

end LeanDLRA.Literature.P1807_02338
