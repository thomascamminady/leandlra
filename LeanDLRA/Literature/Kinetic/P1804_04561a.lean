import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Integrators.Matrix.ProjectorSplitting
import LeanDLRA.Foundations.Galerkin
import LeanDLRA.Foundations.OneSided
import LeanDLRA.Kinetic.Defs
import LeanDLRA.LinearAlgebra.LowRank.SepRank

/-!
# Low-rank BGK for weakly compressible flow (arXiv 1804.04561)

Einkemmer, *A low-rank algorithm for weakly compressible flow*.  This module proves the expansion
(8) of the Maxwellian with its rank, writes the projector-splitting scheme (17)-(25) for BGK on a
grid with its substep equations, and replaces the formal limit `ε → 0` of Section 4 by theorems: the
K- and L-steps relax to the constraint of the paper with an explicit rate and converge to the
solution of a closed moment system, while the backward S-step repels its constraint.

## Section 2

Everything here is on `ℝ^d` with Lebesgue measure, without discretization.

* `eq8_remainder`: Eq. (8), with remainder `|ρ| (2π)^{-d/2} ‖u‖³ / 2`, uniform in `v`, `x`, `d`.
* `eq8_rank_le`, `eq8_rank_le_two`, `eq8_rank_le_three`: separation rank at most
  `C(d + 2, 2)`, so `6` and `10`, for arbitrary `ρ (x)`, `u (x)`.
* `eq8_rank_sharp`, `eq8_rank_sharp_two`, `eq8_rank_sharp_three`: these ranks are attained, already
  on an arbitrarily small ball of velocities `u`.  The paper does not prove this.
* `maxwellian_not_low_rank`: the exact Maxwellian has no finite separation rank.
* `integral_maxwellian`, `integral_smul_maxwellian`: its mass and momentum are `ρ` and `ρ u`.

## Section 3

The scheme is written on a grid: `f i j = f (x_i, v_j)`, `D a` discretizes `∂_{x_a}`, `ξ j` is the
node `v_j`, and the inner products are Frobenius (unit quadrature weights in `L²`, which a diagonal
scaling reaches).  `bgkField` is `-v · ∇ₓ f + ε⁻¹ (M f - f)`, and one step of the scheme is
`MatrixKSL.IsStep (bgkField D ξ M ε)`.

* `eq17`, `eq18`: the projector and the three-term splitting; that it is the orthogonal projector
  onto the tangent space is `isOrthProj_tangentProj`, `mem_range_tangentProj`.
* `eq19`, `eq20`, `eq21`: the substep trajectories solve these equations.
* `eq23`, `eq24`, `eq25`: the factor equations, with `cOne`, `dOne`.
* `discreteMaxwellian_mul`: `M (f) V = ρ c³` for the Maxwellian `discreteMaxwellian` on the grid.

## Section 4

For an equilibrium that depends on `f` through its moments, `M f = ℳ (mom f)`, with `mom` linear and
`mom ∘ ℳ = id`, the stiff part of a substep conserves the moments.  This is the structure that
replaces the formal argument.  `mom f = f Φ` on the grid, `IsClosure` collects the regularity of
`ℳ`, and `IsRelaxSol` describes a solution of `∂ₜ f = σ P (A f + ε⁻¹ (M f - f))`.

* `IsRelaxSol.lyapunov_le`, `IsRelaxSol.defect_le`: `‖P M f - f‖ ≤ e^{-t/ε} ‖P M f₀ - f₀‖ + ε B`,
  with `B` independent of `ε`, nothing being assumed about the size of the solution.
* `IsRelaxSol.moment_limit`, `IsRelaxSol.singular_limit`, `tendsto_singular_limit`: the moments
  stay `O(ε)` close to the closed system `μ' = mom P A P ℳ μ`, and `f` converges to `P ℳ (μ)`.
* `kStep_singular_limit`, `kStep_tendsto`, `kStep_limit_constraint`, and
  `lStep_singular_limit`, `reduced_mem_range_left`, `lStep_limit_constraint`: the same for the
  K- and L-steps of the scheme; the limits satisfy the constraints `K = ∫ V M dv`, `L = ∫ X M dx`.
* `kStep_formal_constraint`, `lStep_formal_constraint`, `sStep_formal_constraint`,
  `formal_constraint`: the paper's own step, for all three substeps, under the assumption
  `ε ∂ₜ y_ε → 0` that the formal argument hides; `kConstraint_maxwellian`,
  `lConstraint_maxwellian`, `sConstraint_maxwellian`: the formulas of Section 4.
* `equilibrium_iff`, `eq_maxwellian_of_exact`, `kStep_reproduces_maxwellian`,
  `lStep_reproduces_maxwellian`, `step_reproduces_maxwellian`: if the bases represent the
  Maxwellian, the scheme yields a Maxwellian, up to `O(e^{-t/ε} + ε)`, and exactly without
  transport.

## Misprints in the paper

Each is checked against the printed PDF (pp. 11, 12, 17) and refuted by a Lean counterexample.

* Eq. (23) has the wrong sign of the collision term, and contradicts the paper's Eq. (26):
  `eq23_printed_iff`, `eq23_printed_false`.
* The second equality of Eq. (25) has the wrong overall sign: its right-hand side is `+L̇_i`, not
  `-L̇_i` (`eq25_printed_iff`, `eq25_printed_false`).  The first equality, `-L̇_i = (X¹_j, …)`, is
  right except for the index, `X¹_j` for `X¹_i`.
* The formulas for `L_i` and `S_{ij}` in Section 4 lack the factor `(2π)^{-d/2}`, which the formula
  for `K_j` has: `lConstraint_printed_false`, `sConstraint_printed_false`, with instances in the
  last section where the constraint holds with nonzero `L₀`, `S₀`.

## How far the formal argument of Section 4 goes

The paper takes `ε → 0` formally in each substep.  The theorems here say when that step is valid.

* For the S-step ("we obtain a very similar result") the formal step is valid only for families
  that converge with `ε Ṡ_ε → 0` (`sStep_formal_constraint`).  The S-step runs backward, so its
  constraint repels: `IsRelaxSol.defect_ge`, `pure_relaxation` (`σ = -1`).  By `sStep_diverges`,
  solutions off the constraint leave every ball on `[0, τ]` as `ε → 0`.  Starting from the K-step
  does not change this: `sStep_undoes_kStep`, `sStep_constraint_fails` give an S-step whose defect
  is the initial defect of the K-step, for every `ε`.  The L-step then relaxes again.
* For the K-step the paper's proviso, that `V` represent the Maxwellian accurately, is needed:
  `kStep_reproduces_maxwellian` confirms the exact case, and if `V` holds neither the moments nor
  the Maxwellian the constraint can repel, `kStep_repels`.  So the hypothesis of moment
  conservation in `kStep_singular_limit` cannot be dropped.  The L-step needs no such hypothesis
  (`lStep_isRelaxSol`).

## Differences from the paper, and what is left

* Section 2 is continuous.  Sections 3 and 4 are an abstract core: on matrices, and for the
  singular limit on an inner product space.  `L²(Ω)`, `∇ₓ` and the PDE are not modelled.
* The singular limit needs the moments to be exact, `ℳ (μ) Φ = μ`.  This holds for the Maxwellian
  on `ℝ^d` (`integral_maxwellian`, `integral_smul_maxwellian`), but not for its point values
  `discreteMaxwellian` under a general quadrature, so that map is an instance of the formal
  statements and not of `IsClosure`.  `ℳ` is therefore a parameter, with `isClosure_linear`,
  `kStep_nonvacuous`, `lStep_nonvacuous`, `sStep_nonvacuous` as instances.  Stating the limit for
  the true Maxwellian would need a weighted `L²` space in `v`.
* `U` carries the positivity of the density, and the moments along a solution are assumed to stay in
  `U`.  For `U = univ` this is void.
* The limit `ε → 0` of a whole step with transport is left open: the K- and L-steps are controlled,
  but the S-step between them has no uniform bound (`sStep_diverges`).  This is a property of exact
  substeps at fixed `τ ≫ ε`.  `lStep_reproduces_maxwellian` holds for the output of any S-step, with
  a constant that depends on it.
* Not formalized: the Chapman–Enskog derivation (9)-(10) of the Navier–Stokes equations, the moment
  computation `∫ v_i v_j f^eq dv`, the Strang variant, the discretizations and costs of Sections
  3.1-3.3, and the numerics of Section 5.

## Core vocabulary

The discrete density `ρ (f)_i = ∑_j w_j f_{ij}` is the core `Kinetic.density` of
`LeanDLRA/Kinetic/Defs.lean`. The discrete momentum `momentum` is vector valued and stays a
definition of this file; `momentum_eq_quadMoment` writes each of its components as a core
quadrature moment `Kinetic.quadMoment`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace LeanDLRA.Literature.P1804_04561

open LeanDLRA.Kinetic (density)

/-! ### Section 2: the Maxwellian and its expansion -/

section Maxwellian

/-- Velocity space `ℝ^d`. -/
abbrev Vel (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The normalization `(2π)^{-d/2}` of Eq. (7). -/
noncomputable def gaussConst (d : ℕ) : ℝ := ((2 * Real.pi) ^ ((d : ℝ) / 2))⁻¹

lemma gaussConst_pos (d : ℕ) : 0 < gaussConst d := by
  unfold gaussConst
  have := Real.pi_pos
  positivity

/-- The Maxwellian of Eq. (7) with `θ = 1`:
`f^eq = ρ (2π)^{-d/2} exp (-(v - u)² / 2)`. -/
noncomputable def maxwellian {d : ℕ} (ρ : ℝ) (u v : Vel d) : ℝ :=
  ρ * gaussConst d * Real.exp (-‖v - u‖ ^ 2 / 2)

/-- The truncated Maxwellian of Eq. (8):
`ρ (2π)^{-d/2} exp (-v² / 2) (1 + v · u + (v · u)² / 2 - u² / 2)`. -/
noncomputable def maxwellianTrunc {d : ℕ} (ρ : ℝ) (u v : Vel d) : ℝ :=
  ρ * gaussConst d * Real.exp (-‖v‖ ^ 2 / 2) * (1 + ⟪v, u⟫ + ⟪v, u⟫ ^ 2 / 2 - ‖u‖ ^ 2 / 2)

/-- `|y³ - 3 y| e^{-y²/2} ≤ 3`: the third derivative of the Gaussian is bounded. -/
private lemma abs_cubic_mul_exp_le (y : ℝ) :
    |y ^ 3 - 3 * y| * Real.exp (-y ^ 2 / 2) ≤ 3 := by
  have hp : 0 ≤ |y| := abs_nonneg y
  have h1 : |y ^ 3 - 3 * y| ≤ |y| ^ 3 + 3 * |y| := by
    calc |y ^ 3 - 3 * y| ≤ |y ^ 3| + |3 * y| := abs_sub _ _
      _ = |y| ^ 3 + 3 * |y| := by rw [abs_pow, abs_mul]; norm_num
  have h2 : 1 + y ^ 2 / 2 + (y ^ 2 / 2) ^ 2 / 2 ≤ Real.exp (y ^ 2 / 2) :=
    Real.quadratic_le_exp_of_nonneg (by positivity)
  have h3 : Real.exp (-y ^ 2 / 2) = (Real.exp (y ^ 2 / 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [h3, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  have h5 : 1 + |y| ^ 2 / 2 + (|y| ^ 2 / 2) ^ 2 / 2 = 1 + y ^ 2 / 2 + (y ^ 2 / 2) ^ 2 / 2 := by
    rw [sq_abs]
  have h4 : |y| ^ 3 + 3 * |y| ≤ 3 * (1 + |y| ^ 2 / 2 + (|y| ^ 2 / 2) ^ 2 / 2) := by
    nlinarith [sq_nonneg (|y| ^ 2 - 2), sq_nonneg (|y| - 1), sq_nonneg (|y| - 2),
      mul_nonneg hp (sq_nonneg (|y| - 2)), sq_nonneg (|y| ^ 2 - |y|)]
  rw [h5] at h4
  linarith

private lemma abs_le_of_abs_deriv_le {g g' c c' : ℝ → ℝ}
    (hg : ∀ s, HasDerivAt g (g' s) s) (hc : ∀ s, HasDerivAt c (c' s) s)
    (h0 : |g 0| ≤ c 0) (hle : ∀ s, 0 ≤ s → |g' s| ≤ c' s) {s : ℝ} (hs : 0 ≤ s) : |g s| ≤ c s := by
  have hcont : ContinuousOn g (Icc 0 s) := fun x _ => (hg x).continuousAt.continuousWithinAt
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := s) (f := g) (f' := g')
    (B := c) (B' := c') hcont (fun x _ => (hg x).hasDerivWithinAt) (by simpa using h0) hc
    (fun x hx => by simpa using hle x hx.1) (right_mem_Icc.2 hs)
  simpa using this

private lemma gauss_taylor_nonneg (t b : ℝ) (hb : 0 ≤ b) :
    |Real.exp (-(t - b) ^ 2 / 2) -
      Real.exp (-t ^ 2 / 2) * (1 + t * b + (t ^ 2 - 1) * b ^ 2 / 2)| ≤ b ^ 3 / 2 := by
  set e : ℝ → ℝ := fun s => Real.exp (-(t - s) ^ 2 / 2) with he
  have hsub : ∀ s, HasDerivAt (fun s => t - s) (-1) s := fun s => by
    simpa using (hasDerivAt_id' s).const_sub t
  have he' : ∀ s, HasDerivAt e ((t - s) * e s) s := fun s => by
    have h0 : HasDerivAt (fun s => -(t - s) ^ 2 / 2) (t - s) s := by
      have h1 := ((hsub s).fun_pow 2).fun_neg.div_const 2
      have h2 : -(((2 : ℕ) : ℝ) * (t - s) ^ (2 - 1) * -1) / 2 = t - s := by
        norm_num
      rwa [h2] at h1
    have h := h0.exp
    rw [mul_comm] at h
    exact h
  have d1 : ∀ s, HasDerivAt (fun s => (t - s) * e s) (((t - s) ^ 2 - 1) * e s) s := fun s => by
    have h := (hsub s).fun_mul (he' s)
    have h2 : -1 * e s + (t - s) * ((t - s) * e s) = ((t - s) ^ 2 - 1) * e s := by ring
    rwa [h2] at h
  have d2 : ∀ s, HasDerivAt (fun s => ((t - s) ^ 2 - 1) * e s)
      (((t - s) ^ 3 - 3 * (t - s)) * e s) s := fun s => by
    have h0 : HasDerivAt (fun s => (t - s) ^ 2 - 1) (-(2 * (t - s))) s := by
      have h1 := ((hsub s).fun_pow 2).sub_const 1
      have h2 : ((2 : ℕ) : ℝ) * (t - s) ^ (2 - 1) * -1 = -(2 * (t - s)) := by norm_num
      rwa [h2] at h1
    have h := h0.fun_mul (he' s)
    have h2 : -(2 * (t - s)) * e s + ((t - s) ^ 2 - 1) * ((t - s) * e s) =
        ((t - s) ^ 3 - 3 * (t - s)) * e s := by ring
    rwa [h2] at h
  have hb3 : ∀ s, |((t - s) ^ 3 - 3 * (t - s)) * e s| ≤ 3 := fun s => by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact abs_cubic_mul_exp_le (t - s)
  have dsq : ∀ s : ℝ, HasDerivAt (fun s : ℝ => 3 * s ^ 2 / 2) (3 * s) s := fun s => by
    have h := (((hasDerivAt_id' s).fun_pow 2).const_mul (3 : ℝ)).div_const 2
    have h2 : (3 : ℝ) * (((2 : ℕ) : ℝ) * s ^ (2 - 1) * 1) / 2 = 3 * s := by
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
      ring
    rwa [h2] at h
  have dcu : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s ^ 3 / 2) (3 * s ^ 2 / 2) s := fun s => by
    have h := ((hasDerivAt_id' s).fun_pow 3).div_const 2
    have h2 : (((3 : ℕ) : ℝ) * s ^ (3 - 1) * 1) / 2 = 3 * s ^ 2 / 2 := by
      norm_num
    rwa [h2] at h
  -- first integration
  have r2 : ∀ s, 0 ≤ s → |((t - s) ^ 2 - 1) * e s - ((t - 0) ^ 2 - 1) * e 0| ≤ 3 * s :=
    fun s hs => by
      refine abs_le_of_abs_deriv_le
        (g := fun s => ((t - s) ^ 2 - 1) * e s - ((t - 0) ^ 2 - 1) * e 0)
        (g' := fun s => ((t - s) ^ 3 - 3 * (t - s)) * e s)
        (c := fun s => 3 * s) (c' := fun _ => 3) (fun s => (d2 s).sub_const _)
        (fun s => by simpa using (hasDerivAt_id' s).const_mul (3 : ℝ)) (by simp)
        (fun s _ => hb3 s) hs
  -- second integration
  have r1 : ∀ s, 0 ≤ s → |(t - s) * e s - (t - 0) * e 0 - ((t - 0) ^ 2 - 1) * e 0 * s| ≤
      3 * s ^ 2 / 2 := fun s hs => by
    refine abs_le_of_abs_deriv_le
      (g := fun s => (t - s) * e s - (t - 0) * e 0 - ((t - 0) ^ 2 - 1) * e 0 * s)
      (g' := fun s => ((t - s) ^ 2 - 1) * e s - ((t - 0) ^ 2 - 1) * e 0)
      (c := fun s => 3 * s ^ 2 / 2) (c' := fun s => 3 * s) (fun s => ?_) dsq (by simp)
      r2 hs
    have h := ((d1 s).sub_const ((t - 0) * e 0)).fun_sub
      ((hasDerivAt_id' s).const_mul (((t - 0) ^ 2 - 1) * e 0))
    rwa [mul_one] at h
  -- third integration
  have r0 : |e b - e 0 - (t - 0) * e 0 * b - ((t - 0) ^ 2 - 1) * e 0 * (b ^ 2 / 2)| ≤
      b ^ 3 / 2 := by
    refine abs_le_of_abs_deriv_le
      (g := fun s => e s - e 0 - (t - 0) * e 0 * s - ((t - 0) ^ 2 - 1) * e 0 * (s ^ 2 / 2))
      (g' := fun s => (t - s) * e s - (t - 0) * e 0 - ((t - 0) ^ 2 - 1) * e 0 * s)
      (c := fun s => s ^ 3 / 2) (c' := fun s => 3 * s ^ 2 / 2) (fun s => ?_) dcu (by simp)
      r1 hb
    have h1 := ((he' s).sub_const (e 0)).fun_sub ((hasDerivAt_id' s).const_mul ((t - 0) * e 0))
    have h2 := (((hasDerivAt_id' s).fun_pow 2).div_const 2).const_mul (((t - 0) ^ 2 - 1) * e 0)
    have h3 := h1.fun_sub h2
    have h4 : (t - s) * e s - (t - 0) * e 0 * 1 -
        ((t - 0) ^ 2 - 1) * e 0 * (((2 : ℕ) : ℝ) * s ^ (2 - 1) * 1 / 2) =
        (t - s) * e s - (t - 0) * e 0 - ((t - 0) ^ 2 - 1) * e 0 * s := by
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
      ring
    rwa [h4] at h3
  have hrw : Real.exp (-t ^ 2 / 2) = e 0 := by simp [he]
  have hrw2 : Real.exp (-(t - b) ^ 2 / 2) = e b := rfl
  have hfin : e b - e 0 - (t - 0) * e 0 * b - ((t - 0) ^ 2 - 1) * e 0 * (b ^ 2 / 2) =
      e b - e 0 * (1 + t * b + (t ^ 2 - 1) * b ^ 2 / 2) := by
    simp only [sub_zero]
    ring
  rw [hrw, hrw2, ← hfin]
  exact r0

/-- Taylor expansion of `s ↦ e^{-(t-s)²/2}` at `s = 0`, with remainder uniform in `t`. -/
private lemma gauss_taylor (t b : ℝ) :
    |Real.exp (-(t - b) ^ 2 / 2) -
      Real.exp (-t ^ 2 / 2) * (1 + t * b + (t ^ 2 - 1) * b ^ 2 / 2)| ≤ |b| ^ 3 / 2 := by
  rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg hb]
    exact gauss_taylor_nonneg t b hb
  · have h := gauss_taylor_nonneg (-t) (-b) (by linarith)
    rw [abs_of_nonpos hb]
    have e1 : (-t - -b) ^ 2 = (t - b) ^ 2 := by ring
    have e2 : (-t) ^ 2 = t ^ 2 := by ring
    have e3 : -t * -b = t * b := by ring
    have e4 : (-b) ^ 2 = b ^ 2 := by ring
    rwa [e1, e2, e3, e4] at h

/-- **Eq. (8), the expansion** (arXiv 1804.04561, Eq. (8)).  For all `ρ`, `u`, `v` and every
dimension `d`,
`|f^eq - ρ (2π)^{-d/2} e^{-v²/2} (1 + v · u + (v · u)² / 2 - u² / 2)| ≤ |ρ| (2π)^{-d/2} ‖u‖³ / 2`.
The paper writes `𝒪(u³)`; this is that remainder, with an explicit constant, uniform in `v`
(and in `x`, when `ρ` and `u` depend on `x`). -/
theorem eq8_remainder {d : ℕ} (ρ : ℝ) (u v : Vel d) :
    |maxwellian ρ u v - maxwellianTrunc ρ u v| ≤ |ρ| * gaussConst d * (‖u‖ ^ 3 / 2) := by
  have hc := gaussConst_pos d
  by_cases hu : u = 0
  · subst hu
    simp [maxwellian, maxwellianTrunc]
  have hb : 0 < ‖u‖ := norm_pos_iff.2 hu
  set b := ‖u‖ with hbdef
  set t := ⟪v, u⟫ / b with htdef
  have hinner : ⟪v, u⟫ = t * b := by rw [htdef]; field_simp
  have hCS : t ^ 2 ≤ ‖v‖ ^ 2 := by
    have h := abs_real_inner_le_norm v u
    rw [hinner, abs_mul, abs_of_pos hb] at h
    have h' : |t| ≤ ‖v‖ := le_of_mul_le_mul_right h hb
    calc t ^ 2 = |t| ^ 2 := (sq_abs t).symm
      _ ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg t) h' 2
  have e1 : ‖v - u‖ ^ 2 = (‖v‖ ^ 2 - t ^ 2) + (t - b) ^ 2 := by
    rw [norm_sub_sq_real, hinner]; ring
  have e2 : ‖v‖ ^ 2 = (‖v‖ ^ 2 - t ^ 2) + t ^ 2 := by ring
  set w := ‖v‖ ^ 2 - t ^ 2 with hw
  have hw0 : 0 ≤ w := by rw [hw]; linarith
  have ex1 : Real.exp (-‖v - u‖ ^ 2 / 2) = Real.exp (-w / 2) * Real.exp (-(t - b) ^ 2 / 2) := by
    rw [← Real.exp_add, e1]; congr 1; ring
  have ex2 : Real.exp (-‖v‖ ^ 2 / 2) = Real.exp (-w / 2) * Real.exp (-t ^ 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    linarith
  have ex3 : Real.exp (-w / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have key : maxwellian ρ u v - maxwellianTrunc ρ u v = ρ * gaussConst d * Real.exp (-w / 2) *
      (Real.exp (-(t - b) ^ 2 / 2) -
        Real.exp (-t ^ 2 / 2) * (1 + t * b + (t ^ 2 - 1) * b ^ 2 / 2)) := by
    simp only [maxwellian, maxwellianTrunc, ex1, ex2, hinner]
    ring
  rw [key, abs_mul, abs_mul, abs_mul, abs_of_pos hc, abs_of_pos (Real.exp_pos _)]
  have h := gauss_taylor t b
  rw [abs_of_pos hb] at h
  have hmul : 0 ≤ |ρ| * gaussConst d := by positivity
  calc |ρ| * gaussConst d * Real.exp (-w / 2) * _
      ≤ |ρ| * gaussConst d * 1 * (b ^ 3 / 2) := by gcongr
    _ = _ := by ring

/-! #### Moments -/

private lemma integral_gauss (d : ℕ) :
    ∫ w : Vel d, Real.exp (-‖w‖ ^ 2 / 2) = (gaussConst d)⁻¹ := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Vel d) (b := 1 / 2) (by norm_num)
  have e : ∀ w : Vel d, Real.exp (-(1 / 2) * ‖w‖ ^ 2) = Real.exp (-‖w‖ ^ 2 / 2) := fun w => by
    congr 1; ring
  simp only [e, finrank_euclideanSpace_fin] at h
  rw [h, gaussConst, inv_inv]
  congr 1
  ring

private lemma integrable_gauss (d : ℕ) :
    MeasureTheory.Integrable fun w : Vel d => Real.exp (-‖w‖ ^ 2 / 2) :=
  .of_integral_ne_zero (by rw [integral_gauss]; exact (inv_pos.2 (gaussConst_pos d)).ne')

private lemma integrable_smul_gauss (d : ℕ) :
    MeasureTheory.Integrable fun w : Vel d => Real.exp (-‖w‖ ^ 2 / 2) • w := by
  have hint : MeasureTheory.Integrable fun w : Vel d => 2 * Real.exp (-‖w‖ ^ 2 / 4) := by
    have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Vel d) (b := 1 / 4) (by norm_num)
    have e : ∀ w : Vel d, Real.exp (-(1 / 4) * ‖w‖ ^ 2) = Real.exp (-‖w‖ ^ 2 / 4) := fun w => by
      congr 1; ring
    simp only [e] at h
    refine MeasureTheory.Integrable.const_mul (.of_integral_ne_zero ?_) 2
    rw [h]
    exact (Real.rpow_pos_of_pos (by have := Real.pi_pos; positivity) _).ne'
  refine hint.mono' (by fun_prop) (.of_forall fun w => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h1 : ‖w‖ ^ 2 / 4 + 1 ≤ Real.exp (‖w‖ ^ 2 / 4) := Real.add_one_le_exp _
  have h2 : ‖w‖ ≤ 2 * Real.exp (‖w‖ ^ 2 / 4) := by nlinarith [sq_nonneg (‖w‖ - 2)]
  have h3 : Real.exp (-‖w‖ ^ 2 / 2) = Real.exp (-‖w‖ ^ 2 / 4) * Real.exp (-‖w‖ ^ 2 / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (-‖w‖ ^ 2 / 4) * Real.exp (‖w‖ ^ 2 / 4) = 1 := by
    rw [← Real.exp_add]; simp [neg_div]
  have hp := Real.exp_pos (-‖w‖ ^ 2 / 4)
  calc Real.exp (-‖w‖ ^ 2 / 2) * ‖w‖
      ≤ Real.exp (-‖w‖ ^ 2 / 2) * (2 * Real.exp (‖w‖ ^ 2 / 4)) := by gcongr
    _ = 2 * Real.exp (-‖w‖ ^ 2 / 4) * (Real.exp (-‖w‖ ^ 2 / 4) * Real.exp (‖w‖ ^ 2 / 4)) := by
        rw [h3]; ring
    _ = _ := by rw [h4, mul_one]

/-- **Eq. (6), density** (arXiv 1804.04561, Eq. (6) and the line after it): the Maxwellian has
mass `ρ`, `∫ f^eq dv = ρ`, for the Lebesgue measure on `ℝ^d`. -/
theorem integral_maxwellian {d : ℕ} (ρ : ℝ) (u : Vel d) : ∫ v, maxwellian ρ u v = ρ := by
  have h : ∫ v : Vel d, Real.exp (-‖v - u‖ ^ 2 / 2) = (gaussConst d)⁻¹ := by
    rw [MeasureTheory.integral_sub_right_eq_self (fun w : Vel d => Real.exp (-‖w‖ ^ 2 / 2)) u]
    exact integral_gauss d
  simp only [maxwellian]
  rw [MeasureTheory.integral_const_mul, h]
  have := (gaussConst_pos d).ne'
  field_simp

/-- **Eq. (6), momentum** (arXiv 1804.04561, Eq. (6) and the line after it): the Maxwellian has
momentum `ρ u`, `∫ v f^eq dv = ρ u`. -/
theorem integral_smul_maxwellian {d : ℕ} (ρ : ℝ) (u : Vel d) :
    ∫ v, maxwellian ρ u v • v = ρ • u := by
  have hodd : ∫ w : Vel d, Real.exp (-‖w‖ ^ 2 / 2) • w = 0 := by
    have h := MeasureTheory.integral_neg_eq_self (fun w : Vel d => Real.exp (-‖w‖ ^ 2 / 2) • w)
      MeasureTheory.volume
    simp only [norm_neg, smul_neg, MeasureTheory.integral_neg] at h
    have h2 : (2 : ℝ) • (∫ w : Vel d, Real.exp (-‖w‖ ^ 2 / 2) • w) = 0 := by
      rw [two_smul]
      nth_rw 1 [← h]
      simp
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  have hsplit : ∫ v : Vel d, Real.exp (-‖v - u‖ ^ 2 / 2) • v = (gaussConst d)⁻¹ • u := by
    have h1 : ∫ v : Vel d, Real.exp (-‖v - u‖ ^ 2 / 2) • v =
        ∫ w : Vel d, Real.exp (-‖w‖ ^ 2 / 2) • (w + u) := by
      rw [← MeasureTheory.integral_sub_right_eq_self
        (fun w : Vel d => Real.exp (-‖w‖ ^ 2 / 2) • (w + u)) u]
      simp
    have h2 : ∀ w : Vel d, Real.exp (-‖w‖ ^ 2 / 2) • (w + u) =
        Real.exp (-‖w‖ ^ 2 / 2) • w + Real.exp (-‖w‖ ^ 2 / 2) • u := fun w => smul_add _ _ _
    rw [h1]
    simp only [h2]
    rw [MeasureTheory.integral_add (integrable_smul_gauss d)
      ((integrable_gauss d).smul_const u), hodd, zero_add,
      integral_smul_const, integral_gauss]
  simp only [maxwellian, mul_smul]
  rw [MeasureTheory.integral_smul, MeasureTheory.integral_smul, hsplit, smul_smul, smul_smul]
  have := (gaussConst_pos d).ne'
  rw [mul_assoc]
  congr 1
  field_simp

/-! #### Separation rank

`f (x, v)` has separation rank at most `r` if `f (x, v) = ∑_{k < r} a_k (x) b_k (v)`: the sense
of "low rank" in Eq. (12) of arXiv 1804.04561. This is the core `HasSepRankLE ℝ f r`. -/

/-- If all slices `f x` lie in the span of `r` functions, the separation rank is at most `r`
(arXiv 1804.04561, Eq. (8), the rank). -/
theorem HasSepRankLE.of_mem_span {X Y ι : Type*} [Fintype ι] {f : X → Y → ℝ} (b : ι → Y → ℝ)
    (h : ∀ x, f x ∈ Submodule.span ℝ (Set.range b)) : HasSepRankLE ℝ f (Fintype.card ι) := by
  classical
  choose c hc using fun x => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (h x)
  let e := Fintype.equivFin ι
  refine ⟨fun k x => c x (e.symm k), fun k => b (e.symm k), fun x y => ?_⟩
  have h1 := congrFun (hc x) y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
  rw [← h1]
  exact (Equiv.sum_comp e.symm fun i => c x i * b i y).symm

/-- Linearly independent functions in the span of the slices bound the separation rank from
below (arXiv 1804.04561, Eq. (8), the rank). -/
theorem HasSepRankLE.card_le {X Y ι : Type*} [Fintype ι] {f : X → Y → ℝ} {r : ℕ}
    (hf : HasSepRankLE ℝ f r) {g : ι → Y → ℝ} (hg : LinearIndependent ℝ g)
    (hs : ∀ i, g i ∈ Submodule.span ℝ (Set.range f)) : Fintype.card ι ≤ r := by
  obtain ⟨a, b, hab⟩ := hf
  let W := Submodule.span ℝ (Set.range b)
  have hfW : Set.range f ⊆ W := by
    rintro _ ⟨x, rfl⟩
    have : f x = ∑ k, a k x • b k := by
      funext y
      simp [hab]
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hgW : ∀ i, g i ∈ W := fun i => Submodule.span_le.2 hfW (hs i)
  have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range b)
  have hLI : LinearIndependent ℝ (fun i => (⟨g i, hgW i⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hg
  calc Fintype.card ι ≤ Module.finrank ℝ W := hLI.fintype_card_le_finrank
    _ ≤ Fintype.card (Fin r) := finrank_range_le_card b
    _ = r := Fintype.card_fin r

/-- The homogeneous coordinates `(1, v₁, …, v_d)` of `v`. -/
def hatV {d : ℕ} (v : Vel d) : Option (Fin d) → ℝ
  | none => 1
  | some i => v i

/-- The product `w_a w_b` of two coordinates, as a function of the unordered pair `{a, b}`. -/
def mon2 {ι : Type*} (w : ι → ℝ) : Sym2 ι → ℝ :=
  Sym2.lift ⟨fun a b => w a * w b, fun _ _ => mul_comm _ _⟩

@[simp] lemma mon2_mk {ι : Type*} (w : ι → ℝ) (a b : ι) : mon2 w s(a, b) = w a * w b := rfl

/-- The functions `e^{-v²/2} v^α`, `|α| ≤ 2`, indexed by unordered pairs in `{0, 1, …, d}`. -/
noncomputable def quadMon {d : ℕ} (s : Sym2 (Option (Fin d))) (v : Vel d) : ℝ :=
  Real.exp (-‖v‖ ^ 2 / 2) * mon2 (hatV v) s

section Independence

variable {ι : Type*}

private noncomputable def monPoly : Sym2 ι → MvPolynomial ι ℝ :=
  Sym2.lift ⟨fun a b => MvPolynomial.X a * MvPolynomial.X b, fun _ _ => mul_comm _ _⟩

private lemma eval_monPoly (w : ι → ℝ) (s : Sym2 ι) :
    MvPolynomial.eval w (monPoly s) = mon2 w s := by
  induction s with
  | h a b => simp [monPoly]

private noncomputable def monExp [DecidableEq ι] : Sym2 ι → (ι →₀ ℕ) :=
  Sym2.lift ⟨fun a b => Finsupp.single a 1 + Finsupp.single b 1, fun _ _ => add_comm _ _⟩

private lemma monExp_injective [DecidableEq ι] : Function.Injective (monExp (ι := ι)) := by
  intro s s'
  induction s with
  | h a b =>
    induction s' with
    | h c e =>
      intro h
      simp only [monExp, Sym2.lift_mk] at h
      have hinj : ∀ x y : ι, (Finsupp.single x 1 : ι →₀ ℕ) = Finsupp.single y 1 → x = y := by
        intro x y hxy
        by_contra hne
        have hx := DFunLike.congr_fun hxy x
        simp [Ne.symm hne] at hx
      by_cases hca : c = a
      · subst hca
        rw [hinj _ _ (add_left_cancel h)]
      · have ha := DFunLike.congr_fun h a
        simp only [Finsupp.add_apply, Finsupp.single_apply] at ha
        have hea : e = a := by
          by_contra hne
          simp [hca, hne] at ha
        subst hea
        rw [hinj _ _ (add_left_cancel (h.trans (add_comm _ _)))]
        exact Sym2.eq_swap

private lemma linearIndependent_monPoly : LinearIndependent ℝ (monPoly (ι := ι)) := by
  classical
  have h := (MvPolynomial.basisMonomials ι ℝ).linearIndependent.comp _
    (monExp_injective (ι := ι))
  convert h using 1
  funext s
  induction s with
  | h a b =>
    simp only [Function.comp_apply, monExp, monPoly, Sym2.lift_mk,
      MvPolynomial.coe_basisMonomials]
    rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul_monomial, mul_one]

end Independence

private lemma mon2_smul {ι : Type*} (c : ℝ) (w : ι → ℝ) (s : Sym2 ι) :
    mon2 (c • w) s = c ^ 2 * mon2 w s := by
  induction s with
  | h a b => simp only [mon2_mk, Pi.smul_apply, smul_eq_mul]; ring

/-- The functions `e^{-v²/2} v^α`, `|α| ≤ 2`, are linearly independent.
(arXiv 1804.04561, Eq. (8), the rank.) -/
theorem linearIndependent_quadMon (d : ℕ) :
    LinearIndependent ℝ (quadMon (d := d)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set P : MvPolynomial (Option (Fin d)) ℝ := ∑ s, g s • monPoly s with hP
  have heval : ∀ w, MvPolynomial.eval w P = ∑ s, g s * mon2 w s := fun w => by
    simp [hP, map_sum, eval_monPoly]
  have hv : ∀ v : Vel d, MvPolynomial.eval (hatV v) P = 0 := fun v => by
    have h := congrFun hg v
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, quadMon] at h
    have h' : Real.exp (-‖v‖ ^ 2 / 2) * ∑ s, g s * mon2 (hatV v) s = 0 := by
      rw [Finset.mul_sum, ← h]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [heval]
    exact (mul_eq_zero.1 h').resolve_left (Real.exp_pos _).ne'
  have hscale : ∀ w : Option (Fin d) → ℝ, MvPolynomial.eval w
      (MvPolynomial.X none * P) = 0 := fun w => by
    rw [map_mul, MvPolynomial.eval_X]
    by_cases h0 : w none = 0
    · rw [h0, zero_mul]
    · set v : Vel d := WithLp.toLp 2 fun i => w (some i) / w none with hvdef
      have hw : w = w none • hatV v := by
        funext a
        cases a with
        | none => simp [hatV]
        | some i =>
          simp only [Pi.smul_apply, hatV, smul_eq_mul, hvdef]
          field_simp
      have h2 : MvPolynomial.eval w P = (w none) ^ 2 * MvPolynomial.eval (hatV v) P := by
        rw [heval, heval, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        conv_lhs => rw [hw, mon2_smul]
        ring
      rw [h2, hv, mul_zero, mul_zero]
  have hzero : MvPolynomial.X none * P = 0 :=
    MvPolynomial.funext fun w => by rw [hscale, map_zero]
  have hPzero : P = 0 :=
    (mul_eq_zero.1 hzero).resolve_left (MvPolynomial.X_ne_zero _)
  exact Fintype.linearIndependent_iff.1 linearIndependent_monPoly g hPzero

private lemma inner_eq_sum {d : ℕ} (v u : Vel d) : ⟪v, u⟫ = ∑ i, u i * v i := by
  simp [PiLp.inner_apply]

/-- **Eq. (8), the rank** (arXiv 1804.04561, the sentence after Eq. (8)), in every dimension: for
arbitrary `ρ (x)`, `u (x)` on an arbitrary set `X`, the truncated Maxwellian has separation rank at
most `(d + 1) (d + 2) / 2 = C(d + 2, 2)`, the dimension of `span {e^{-v²/2} v^α : |α| ≤ 2}`. -/
theorem eq8_rank_le {d : ℕ} {X : Type*} (ρ : X → ℝ) (u : X → Vel d) :
    HasSepRankLE ℝ (fun x v => maxwellianTrunc (ρ x) (u x) v) (Nat.choose (d + 2) 2) := by
  classical
  have hcard : Fintype.card (Sym2 (Option (Fin d))) = Nat.choose (d + 2) 2 := by
    rw [Sym2.card, Fintype.card_option, Fintype.card_fin]
  rw [← hcard]
  refine HasSepRankLE.of_mem_span (quadMon (d := d)) fun x => ?_
  set S := Submodule.span ℝ (Set.range (quadMon (d := d))) with hS
  have hm : ∀ s, quadMon s ∈ S := fun s => Submodule.subset_span ⟨s, rfl⟩
  have hexp : (fun v => maxwellianTrunc (ρ x) (u x) v) =
      (ρ x * gaussConst d * (1 - ‖u x‖ ^ 2 / 2)) • quadMon s(none, none) +
      ∑ i, (ρ x * gaussConst d * u x i) • quadMon s(none, some i) +
      ∑ i, ∑ j, (ρ x * gaussConst d * (u x i * u x j / 2)) • quadMon s(some i, some j) := by
    funext v
    have h2 : ⟪v, u x⟫ ^ 2 = ∑ i, ∑ j, (u x i * u x j) * (v i * v j) := by
      rw [inner_eq_sum, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    simp only [maxwellianTrunc, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
      quadMon, mon2_mk, hatV, one_mul, mul_one]
    rw [h2, inner_eq_sum]
    set c := ρ x * gaussConst d
    set G := Real.exp (-‖v‖ ^ 2 / 2)
    have e1 : ∑ i, c * u x i * (G * v i) = c * G * ∑ i, u x i * v i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, ∑ j, c * (u x i * u x j / 2) * (G * (v i * v j)) =
        c * G * ((∑ i, ∑ j, u x i * u x j * (v i * v j)) / 2) := by
      rw [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, e2]
    ring
  change (fun v => maxwellianTrunc (ρ x) (u x) v) ∈ S
  rw [hexp]
  refine S.add_mem (S.add_mem (S.smul_mem _ (hm _)) ?_) ?_
  · exact S.sum_mem fun i _ => S.smul_mem _ (hm _)
  · exact S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem _ (hm _)

/-- **Eq. (8), rank 6 in two dimensions** (arXiv 1804.04561). -/
theorem eq8_rank_le_two {X : Type*} (ρ : X → ℝ) (u : X → Vel 2) :
    HasSepRankLE ℝ (fun x v => maxwellianTrunc (ρ x) (u x) v) 6 :=
  eq8_rank_le ρ u

/-- **Eq. (8), rank 10 in three dimensions** (arXiv 1804.04561). -/
theorem eq8_rank_le_three {X : Type*} (ρ : X → ℝ) (u : X → Vel 3) :
    HasSepRankLE ℝ (fun x v => maxwellianTrunc (ρ x) (u x) v) 10 :=
  eq8_rank_le ρ u

private lemma inner_smul_single {d : ℕ} (v : Vel d) (t : ℝ) (i : Fin d) :
    ⟪v, t • EuclideanSpace.single i (1 : ℝ)⟫ = t * v i := by
  rw [real_inner_smul_right, EuclideanSpace.inner_single_right]
  simp

private lemma norm_single_one {d : ℕ} (i : Fin d) : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by
  simp

/-- The rank in `eq8_rank_le` is attained: the slices `v ↦ T_u (v)` for `u` in an arbitrarily small
ball span all of `e^{-v²/2} v^α`, `|α| ≤ 2`, by finite differences in `u`. -/
private lemma quadMon_mem_span {d : ℕ} {ρ₀ δ : ℝ} (hρ : ρ₀ ≠ 0) (hδ : 0 < δ)
    (s : Sym2 (Option (Fin d))) :
    quadMon s ∈ Submodule.span ℝ (Set.range fun (x : Metric.ball (0 : Vel d) δ) v =>
      maxwellianTrunc ρ₀ (x : Vel d) v) := by
  classical
  set S := Submodule.span ℝ (Set.range fun (x : Metric.ball (0 : Vel d) δ) v =>
      maxwellianTrunc ρ₀ (x : Vel d) v) with hS
  set T : Vel d → Vel d → ℝ := fun u v => maxwellianTrunc ρ₀ u v with hT
  have Tmem : ∀ u : Vel d, ‖u‖ < δ → T u ∈ S := fun u hu =>
    Submodule.subset_span ⟨⟨u, mem_ball_zero_iff.2 hu⟩, rfl⟩
  set t := δ / 3 with ht
  have htpos : 0 < t := by positivity
  have hc : ρ₀ * gaussConst d ≠ 0 := mul_ne_zero hρ (gaussConst_pos d).ne'
  set c := ρ₀ * gaussConst d with hcdef
  set e : Fin d → Vel d := fun i => EuclideanSpace.single i (1 : ℝ) with he
  have hen : ∀ i, ‖e i‖ = 1 := fun i => norm_single_one i
  have T0 : T 0 = c • quadMon s(none, none) := by
    funext v
    simp [hT, maxwellianTrunc, quadMon, hatV, hcdef]
  have T1 : ∀ (a : ℝ) (i : Fin d) (v : Vel d), T (a • e i) v =
      c * (Real.exp (-‖v‖ ^ 2 / 2) * (1 + a * v i + (a * v i) ^ 2 / 2 - a ^ 2 / 2)) :=
    fun a i v => by
    have hn : ‖a • e i‖ ^ 2 = a ^ 2 := by rw [norm_smul, hen, mul_one, Real.norm_eq_abs, sq_abs]
    have hin : ⟪v, a • e i⟫ = a * v i := inner_smul_single v a i
    simp only [hT, maxwellianTrunc]
    rw [hin, hn]
    ring
  have m0 : T 0 ∈ S := Tmem 0 (by simpa using hδ)
  have mp : ∀ i, T (t • e i) ∈ S := fun i => Tmem _ (by
    rw [norm_smul, hen, Real.norm_eq_abs, abs_of_pos htpos, mul_one, ht]; linarith)
  have mn : ∀ i, T ((-t) • e i) ∈ S := fun i => Tmem _ (by
    rw [norm_smul, hen, Real.norm_eq_abs, abs_neg, abs_of_pos htpos, mul_one, ht]; linarith)
  have hnone : ∀ i, quadMon s(none, some i) ∈ S := fun i => by
    have : quadMon s(none, some i) = (2 * t * c)⁻¹ • (T (t • e i) - T ((-t) • e i)) := by
      funext v
      simp only [quadMon, mon2_mk, hatV, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, T1]
      field_simp
      ring
    rw [this]
    exact S.smul_mem _ (S.sub_mem (mp i) (mn i))
  have hdiag : ∀ i, quadMon s(some i, some i) ∈ S := fun i => by
    have : quadMon s(some i, some i) =
        (t ^ 2 * c)⁻¹ • (T (t • e i) + T ((-t) • e i) - (2 : ℝ) • T 0) + c⁻¹ • T 0 := by
      funext v
      have h0 : T 0 v = c * Real.exp (-‖v‖ ^ 2 / 2) := by
        rw [T0]; simp [quadMon, hatV]
      simp only [quadMon, mon2_mk, hatV, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul,
        T1, h0]
      field_simp
      ring
    rw [this]
    exact S.add_mem (S.smul_mem _ (S.sub_mem (S.add_mem (mp i) (mn i)) (S.smul_mem _ m0)))
      (S.smul_mem _ m0)
  have hoff : ∀ i j, i ≠ j → quadMon s(some i, some j) ∈ S := fun i j hij => by
    have hin : ⟪e i, e j⟫ = 0 := by
      simp only [he]
      rw [EuclideanSpace.inner_single_right]
      simp [hij.symm]
    have hnorm : ‖t • (e i + e j)‖ < δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      have := norm_add_le (e i) (e j)
      rw [hen, hen] at this
      nlinarith
    have hT2 : ∀ v : Vel d, T (t • (e i + e j)) v = c * (Real.exp (-‖v‖ ^ 2 / 2) *
        (1 + t * (v i + v j) + (t * (v i + v j)) ^ 2 / 2 - t ^ 2)) := fun v => by
      have hn : ‖t • (e i + e j)‖ ^ 2 = 2 * t ^ 2 := by
        rw [norm_smul, mul_pow, norm_add_sq_real, hen, hen, hin, Real.norm_eq_abs, sq_abs]
        ring
      have hinner : ⟪v, t • (e i + e j)⟫ = t * (v i + v j) := by
        rw [smul_add, inner_add_right]
        simp only [he]
        rw [inner_smul_single, inner_smul_single]
        ring
      simp only [hT, maxwellianTrunc]
      rw [hinner, hn]
      ring
    have : quadMon s(some i, some j) = (t ^ 2 * c)⁻¹ •
        (T (t • (e i + e j)) - T (t • e i) - T (t • e j) + T 0) := by
      funext v
      have h0 : T 0 v = c * Real.exp (-‖v‖ ^ 2 / 2) := by
        rw [T0]; simp [quadMon, hatV]
      simp only [quadMon, mon2_mk, hatV, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul,
        T1, hT2, h0]
      field_simp
      ring
    rw [this]
    exact S.smul_mem _ (S.add_mem (S.sub_mem (S.sub_mem (Tmem _ hnorm) (mp i)) (mp j)) m0)
  induction s with
  | h a b =>
    cases a with
    | none =>
      cases b with
      | none =>
        have : quadMon s((none : Option (Fin d)), none) = c⁻¹ • T 0 := by
          rw [T0, smul_smul, inv_mul_cancel₀ hc, one_smul]
        rw [this]
        exact S.smul_mem _ m0
      | some i => exact hnone i
    | some i =>
      cases b with
      | none =>
        rw [Sym2.eq_swap]
        exact hnone i
      | some j =>
        by_cases hij : i = j
        · subst hij
          exact hdiag i
        · exact hoff i j hij

/-- **Eq. (8), sharpness of the rank** (arXiv 1804.04561, "rank 6 and 10"; the paper does not
prove this): already for constant `ρ₀ ≠ 0` and `u (x) = x` on an arbitrarily small ball, the
separation rank of the truncated Maxwellian is not smaller than `C(d + 2, 2)`. -/
theorem eq8_rank_sharp {d : ℕ} {ρ₀ δ : ℝ} (hρ : ρ₀ ≠ 0) (hδ : 0 < δ) {r : ℕ}
    (h : HasSepRankLE ℝ
      (fun (x : Metric.ball (0 : Vel d) δ) v => maxwellianTrunc ρ₀ (x : Vel d) v) r) :
    Nat.choose (d + 2) 2 ≤ r := by
  classical
  have hcard : Fintype.card (Sym2 (Option (Fin d))) = Nat.choose (d + 2) 2 := by
    rw [Sym2.card, Fintype.card_option, Fintype.card_fin]
  rw [← hcard]
  exact HasSepRankLE.card_le h (linearIndependent_quadMon d) (quadMon_mem_span hρ hδ)

/-- The rank of the truncated Maxwellian in two dimensions is exactly `6` in general.
(arXiv 1804.04561, Eq. (8).) -/
theorem eq8_rank_sharp_two {ρ₀ δ : ℝ} (hρ : ρ₀ ≠ 0) (hδ : 0 < δ) :
    ¬ HasSepRankLE ℝ
      (fun (x : Metric.ball (0 : Vel 2) δ) v => maxwellianTrunc ρ₀ (x : Vel 2) v) 5 :=
  fun h => absurd (eq8_rank_sharp hρ hδ h) (by decide)

/-- The rank of the truncated Maxwellian in three dimensions is exactly `10` in general.
(arXiv 1804.04561, Eq. (8).) -/
theorem eq8_rank_sharp_three {ρ₀ δ : ℝ} (hρ : ρ₀ ≠ 0) (hδ : 0 < δ) :
    ¬ HasSepRankLE ℝ
      (fun (x : Metric.ball (0 : Vel 3) δ) v => maxwellianTrunc ρ₀ (x : Vel 3) v) 9 :=
  fun h => absurd (eq8_rank_sharp hρ hδ h) (by decide)

/-- **The Maxwellian is not low rank** (arXiv 1804.04561, Section 2, before Eq. (8): "this is not a
low-rank representation due to the presence of both velocity and position dependent functions in
the exponential").  For `d ≥ 1`, `ρ₀ ≠ 0` and `u (x) = x` on an arbitrarily small ball, the exact
Maxwellian has no finite separation rank: this is why the truncation (8) is needed. -/
theorem maxwellian_not_low_rank {d : ℕ} (hd : 0 < d) {ρ₀ δ : ℝ} (hρ : ρ₀ ≠ 0) (hδ : 0 < δ)
    (r : ℕ) :
    ¬ HasSepRankLE ℝ
      (fun (x : Metric.ball (0 : Vel d) δ) v => maxwellian ρ₀ (x : Vel d) v) r := by
  classical
  intro h
  set e : Vel d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) with he
  have hen : ‖e‖ = 1 := norm_single_one _
  set a : Fin (r + 1) → ℝ := fun k => δ / 2 * ((k : ℝ) / (r + 1)) with ha
  have ha_lt : ∀ k, ‖a k • e‖ < δ := fun k => by
    rw [norm_smul, hen, mul_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hk : (k : ℝ) / (r + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have := k.2
      exact_mod_cast this.le
    simp only [ha]
    nlinarith
  have ha_inj : Function.Injective a := fun k l hkl => by
    have h2 : δ / 2 ≠ 0 := by positivity
    have h3 : ((r : ℝ) + 1) ≠ 0 := by positivity
    have := mul_left_cancel₀ h2 hkl
    have h4 := (div_left_inj' h3).1 this
    exact Fin.ext (by exact_mod_cast h4)
  set g : Fin (r + 1) → Vel d → ℝ := fun k v => maxwellian ρ₀ (a k • e) v with hg
  have hmem : ∀ k, g k ∈ Submodule.span ℝ (Set.range fun (x : Metric.ball (0 : Vel d) δ) v =>
      maxwellian ρ₀ (x : Vel d) v) := fun k =>
    Submodule.subset_span ⟨⟨a k • e, mem_ball_zero_iff.2 (ha_lt k)⟩, rfl⟩
  have hLI : LinearIndependent ℝ g := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hval : ∀ (k : Fin (r + 1)) (l : ℕ), g k ((l : ℝ) • e) =
        ρ₀ * gaussConst d * Real.exp (-(l : ℝ) ^ 2 / 2) * Real.exp (-(a k) ^ 2 / 2) *
          Real.exp (a k) ^ l := fun k l => by
      have hn : ‖(l : ℝ) • e - a k • e‖ ^ 2 = ((l : ℝ) - a k) ^ 2 := by
        rw [← sub_smul, norm_smul, hen, mul_one, Real.norm_eq_abs, sq_abs]
      simp only [hg, maxwellian, hn]
      have e : Real.exp (-((l : ℝ) - a k) ^ 2 / 2) =
          Real.exp (-(l : ℝ) ^ 2 / 2) * Real.exp (-(a k) ^ 2 / 2) * Real.exp (a k) ^ l := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [e]
      ring
    set c' : Fin (r + 1) → ℝ := fun k => c k * Real.exp (-(a k) ^ 2 / 2) with hc'
    have hzero : c' = 0 := by
      refine Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
        (f := fun k => Real.exp (a k)) (fun k l hkl => ha_inj (Real.exp_injective hkl)) fun l => ?_
      have h1 := congrFun hc ((l : ℕ) • (1 : ℝ) • e)
      have h2 : ((l : ℕ) • (1 : ℝ) • e) = ((l : ℕ) : ℝ) • e := by
        rw [one_smul, Nat.cast_smul_eq_nsmul]
      rw [h2] at h1
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hval, Pi.zero_apply] at h1
      have hne : ρ₀ * gaussConst d * Real.exp (-((l : ℕ) : ℝ) ^ 2 / 2) ≠ 0 :=
        mul_ne_zero (mul_ne_zero hρ (gaussConst_pos d).ne') (Real.exp_pos _).ne'
      have h3 : (ρ₀ * gaussConst d * Real.exp (-((l : ℕ) : ℝ) ^ 2 / 2)) *
          ∑ k, c' k * Real.exp (a k) ^ (l : ℕ) = 0 := by
        rw [Finset.mul_sum, ← h1]
        exact Finset.sum_congr rfl fun k _ => by simp only [hc']; ring
      exact (mul_eq_zero.1 h3).resolve_left hne
    intro k
    have := congrFun hzero k
    simp only [hc', Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_right (Real.exp_pos _).ne'
  have hc := HasSepRankLE.card_le h hLI hmem
  simp at hc

end Maxwellian

/-! ### Scalar and vector comparison lemmas -/

section Comparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `R' = b - R / ε`, `‖b‖ ≤ B` gives
`‖R t‖ ≤ e^{-t/ε} ‖R 0‖ + ε B (1 - e^{-t/ε})`. -/
private lemma relax_decay {R b : ℝ → E} {ε B τ : ℝ} (hε : 0 < ε) (hc : ContinuousOn R (Icc 0 τ))
    (hR : ∀ t ∈ Ico 0 τ, HasDerivWithinAt R (b t - ε⁻¹ • R t) (Ici t) t)
    (hb : ∀ t ∈ Ico 0 τ, ‖b t‖ ≤ B) {t : ℝ} (ht : t ∈ Icc 0 τ) :
    ‖R t‖ ≤ Real.exp (-t / ε) * ‖R 0‖ + ε * B * (1 - Real.exp (-t / ε)) := by
  set w : ℝ → ℝ := fun s => Real.exp (s / ε) with hw
  have hw' : ∀ s, HasDerivAt w (ε⁻¹ * w s) s := fun s => by
    have h1 : HasDerivAt (fun s : ℝ => s / ε) ε⁻¹ s := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id' s).div_const ε
    have h2 := h1.exp
    rw [mul_comm] at h2
    exact h2
  have hy : ∀ s ∈ Ico 0 τ, HasDerivWithinAt (fun s => w s • R s) (w s • b s) (Ici s) s :=
    fun s hs => by
    have h := (hw' s).hasDerivWithinAt.smul (hR s hs)
    have e : w s • (b s - ε⁻¹ • R s) + (ε⁻¹ * w s) • R s = w s • b s := by
      rw [smul_sub, smul_smul, mul_comm (w s)]
      abel
    rw [e] at h
    exact h
  have hB : ∀ s, HasDerivAt (fun s => ‖R 0‖ + ε * B * (w s - 1)) (B * w s) s := fun s => by
    have h := (((hw' s).sub_const 1).const_mul (ε * B)).const_add ‖R 0‖
    have e : ε * B * (ε⁻¹ * w s) = B * w s := by field_simp
    rwa [e] at h
  have h0 : w 0 = 1 := by simp [hw]
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := τ)
    (f := fun s => w s • R s) (f' := fun s => w s • b s) (B := fun s => ‖R 0‖ + ε * B * (w s - 1))
    (B' := fun s => B * w s)
    (ContinuousOn.smul (fun s _ => (hw' s).continuousAt.continuousWithinAt) hc) hy
    (by simp [h0]) hB
    (fun s hs => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hb s hs) (Real.exp_pos _).le) ht
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hmain
  have hinv : Real.exp (-t / ε) * w t = 1 := by
    simp only [hw]
    rw [← Real.exp_add]
    simp [neg_div]
  have hpos : 0 ≤ Real.exp (-t / ε) := (Real.exp_pos _).le
  have := mul_le_mul_of_nonneg_left hmain hpos
  have e1 : Real.exp (-t / ε) * (w t * ‖R t‖) = ‖R t‖ := by
    rw [← mul_assoc, hinv, one_mul]
  have e2 : Real.exp (-t / ε) * (‖R 0‖ + ε * B * (w t - 1)) =
      Real.exp (-t / ε) * ‖R 0‖ + ε * B * (1 - Real.exp (-t / ε)) := by
    have : Real.exp (-t / ε) * (ε * B * (w t - 1)) =
        ε * B * (Real.exp (-t / ε) * w t - Real.exp (-t / ε)) := by ring
    rw [mul_add, this, hinv]
  rwa [e1, e2] at this

/-- `R' = b + R / ε`, `‖b‖ ≤ B`, `B ≥ 0` gives `e^{t/ε} (‖R 0‖ - ε B) ≤ ‖R t‖`. -/
private lemma relax_growth {R b : ℝ → E} {ε B τ : ℝ} (hε : 0 < ε) (hB0 : 0 ≤ B)
    (hc : ContinuousOn R (Icc 0 τ))
    (hR : ∀ t ∈ Ico 0 τ, HasDerivWithinAt R (b t + ε⁻¹ • R t) (Ici t) t)
    (hb : ∀ t ∈ Ico 0 τ, ‖b t‖ ≤ B) {t : ℝ} (ht : t ∈ Icc 0 τ) :
    Real.exp (t / ε) * (‖R 0‖ - ε * B) ≤ ‖R t‖ := by
  set w : ℝ → ℝ := fun s => Real.exp (-s / ε) with hw
  have hw' : ∀ s, HasDerivAt w (-ε⁻¹ * w s) s := fun s => by
    have h1 : HasDerivAt (fun s : ℝ => -s / ε) (-ε⁻¹) s := by
      have h := ((hasDerivAt_id' s).fun_neg).div_const ε
      have e : (-1 : ℝ) / ε = -ε⁻¹ := by rw [neg_div, one_div]
      rwa [e] at h
    have h2 := h1.exp
    rw [mul_comm] at h2
    exact h2
  have hy : ∀ s ∈ Ico 0 τ,
      HasDerivWithinAt (fun s => w s • R s - w 0 • R 0) (w s • b s) (Ici s) s :=
    fun s hs => by
      have h := ((hw' s).hasDerivWithinAt.smul (hR s hs)).sub_const (w 0 • R 0)
      have e : w s • (b s + ε⁻¹ • R s) + (-ε⁻¹ * w s) • R s = w s • b s := by
        rw [smul_add, smul_smul, mul_comm (w s), neg_mul, neg_smul]
        abel
      rw [e] at h
      exact h
  have hBd : ∀ s, HasDerivAt (fun s => ε * B * (1 - w s)) (B * w s) s := fun s => by
    have h := ((hw' s).const_sub 1).const_mul (ε * B)
    have e : ε * B * -(-ε⁻¹ * w s) = B * w s := by field_simp
    rwa [e] at h
  have h0 : w 0 = 1 := by simp [hw]
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := τ)
    (f := fun s => w s • R s - w 0 • R 0) (f' := fun s => w s • b s)
    (B := fun s => ε * B * (1 - w s)) (B' := fun s => B * w s)
    ((ContinuousOn.smul (fun s _ => (hw' s).continuousAt.continuousWithinAt) hc).sub
      continuousOn_const) hy
    (by simp [h0]) hBd
    (fun s hs => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hb s hs) (Real.exp_pos _).le) ht
  simp only [h0, one_smul] at hmain
  have hrev := norm_sub_norm_le (R 0) (w t • R t)
  rw [norm_sub_rev (R 0)] at hrev
  have hle : ‖R 0‖ - ε * B ≤ ‖w t • R t‖ := by
    have hwpos : 0 < w t := Real.exp_pos _
    have h2 : ε * B * (1 - w t) ≤ ε * B := by nlinarith [mul_nonneg hε.le hB0]
    linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hle
  have hinv : Real.exp (t / ε) * w t = 1 := by
    simp only [hw]
    rw [← Real.exp_add]
    simp [neg_div]
  have hpos : 0 ≤ Real.exp (t / ε) := (Real.exp_pos _).le
  calc Real.exp (t / ε) * (‖R 0‖ - ε * B) ≤ Real.exp (t / ε) * (w t * ‖R t‖) :=
        mul_le_mul_of_nonneg_left hle hpos
    _ = ‖R t‖ := by rw [← mul_assoc, hinv, one_mul]

private lemma scalar_gronwall {Z Z' : ℝ → ℝ} {κ τ : ℝ} (hc : ContinuousOn Z (Icc 0 τ))
    (hd : ∀ t ∈ Ico 0 τ, HasDerivWithinAt Z (Z' t) (Ici t) t)
    (hle : ∀ t ∈ Ico 0 τ, Z' t ≤ κ * Z t) {t : ℝ} (ht : t ∈ Icc 0 τ) :
    Z t ≤ Z 0 * Real.exp (κ * t) := by
  set w : ℝ → ℝ := fun s => Real.exp (-κ * s) with hw
  have hw' : ∀ s, HasDerivAt w (-κ * w s) s := fun s => by
    have h1 : HasDerivAt (fun s : ℝ => -κ * s) (-κ) s := by
      simpa using (hasDerivAt_id' s).const_mul (-κ)
    have h2 := h1.exp
    rw [mul_comm] at h2
    exact h2
  have hmain := image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := τ)
    (f := fun s => w s * Z s) (f' := fun s => -κ * w s * Z s + w s * Z' s)
    (B := fun _ => Z 0) (B' := fun _ => 0)
    (ContinuousOn.mul (fun s _ => (hw' s).continuousAt.continuousWithinAt) hc)
    (fun s hs => (hw' s).hasDerivWithinAt.mul (hd s hs))
    (by simp [hw]) continuousOn_const (fun s _ => hasDerivWithinAt_const _ _ _)
    (fun s hs => by
      have := mul_le_mul_of_nonneg_left (hle s hs) (Real.exp_pos (-κ * s)).le
      simp only [hw]
      nlinarith) ht
  have hinv : w t * Real.exp (κ * t) = 1 := by
    simp only [hw]
    rw [← Real.exp_add]
    simp
  have hpos : 0 ≤ Real.exp (κ * t) := (Real.exp_pos _).le
  calc Z t = (w t * Real.exp (κ * t)) * Z t := by rw [hinv, one_mul]
    _ = (w t * Z t) * Real.exp (κ * t) := by ring
    _ ≤ Z 0 * Real.exp (κ * t) := mul_le_mul_of_nonneg_right hmain hpos

private lemma poly_bound {r s c₀ L : ℝ} (hc₀ : 0 ≤ c₀) (hL : 0 ≤ L) :
    (r + s) * (c₀ + L * s + r) ≤ 2 * (c₀ + L + 1) * (r ^ 2 + s ^ 2 + 1) := by
  have h1 : r + s ≤ 2 * (r ^ 2 + s ^ 2 + 1) := by nlinarith [sq_nonneg (r - 1), sq_nonneg (s - 1)]
  have h2 : r * s + s ^ 2 ≤ 2 * (r ^ 2 + s ^ 2 + 1) := by nlinarith [sq_nonneg (r - s)]
  have h3 : r ^ 2 + r * s ≤ 2 * (r ^ 2 + s ^ 2 + 1) := by nlinarith [sq_nonneg (r - s)]
  have h4 := mul_le_mul_of_nonneg_left h1 hc₀
  have h5 := mul_le_mul_of_nonneg_left h2 hL
  nlinarith

end Comparison

/-! ### Abstract relaxation -/

section Relaxation

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The projected BGK field `σ P (A f + ε⁻¹ (ℳ (mom f) - f))`.  With `A = -v · ∇ₓ` and `ℳ ∘ mom`
the Maxwellian of `f`, this is the right-hand side of Eq. (19) (`P = P_V`, `σ = 1`), of Eq. (21)
(`P = P_X`, `σ = 1`) and of Eq. (20) (`P = P_X P_V`, `σ = -1`). -/
noncomputable def relaxField (σ : ℝ) (P A : E →L[ℝ] E) (mom : E →L[ℝ] F) (cl : F → E) (ε : ℝ)
    (_t : ℝ) (f : E) : E :=
  σ • P (A f + ε⁻¹ • (cl (mom f) - f))

/-- The defect `P M(f) - f` of the constraint `f = P M(f)` of Section 4. -/
noncomputable def defect (P : E →L[ℝ] E) (mom : E →L[ℝ] F) (cl : F → E) (f : E) : E :=
  P (cl (mom f)) - f

/-- The closed moment system `μ' = mom (P (A (P (ℳ μ))))`: the fluid limit of a relaxing substep. -/
noncomputable def reducedField (P A : E →L[ℝ] E) (mom : E →L[ℝ] F) (cl : F → E) (_t : ℝ)
    (μ : F) : F :=
  mom (P (A (P (cl μ))))

/-- `ℳ` is `C¹` on the convex set `U` of admissible moments, with derivative bounded by `L` and
linear growth.  On a set of moments with density bounded below, the Maxwellian has these
properties; `U` is the place where the positivity of the density goes. -/
structure IsClosure (cl : F → E) (cl' : F → F →L[ℝ] E) (U : Set F) (L c₀ : ℝ) : Prop where
  convex : Convex ℝ U
  hasFDerivAt : ∀ μ ∈ U, HasFDerivAt cl (cl' μ) μ
  deriv_le : ∀ μ ∈ U, ‖cl' μ‖ ≤ L
  growth : ∀ μ ∈ U, ‖cl μ‖ ≤ c₀ + L * ‖μ‖
  L_nonneg : 0 ≤ L
  c₀_nonneg : 0 ≤ c₀

lemma IsClosure.lipschitz {cl : F → E} {cl' : F → F →L[ℝ] E} {U : Set F} {L c₀ : ℝ}
    (hc : IsClosure cl cl' U L c₀) {μ ν : F} (hμ : μ ∈ U) (hν : ν ∈ U) :
    ‖cl μ - cl ν‖ ≤ L * ‖μ - ν‖ :=
  hc.convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x hx => (hc.hasFDerivAt x hx).hasFDerivWithinAt) hc.deriv_le hν hμ

/-- A solution of the projected BGK equation on `[0, τ]`, with values in `range P`, whose moments
are admissible (`mem`) and for which the projected Maxwellian has the moments of `f` (`cons`).
For the K-step `cons` holds if the moment test functions lie in the range of `V`, or if `V`
represents the Maxwellian exactly (`kStep_isRelaxSol`, `cons_of_moments_mem`, `cons_of_exact`); for
the L-step it always holds (`lStep_isRelaxSol`). -/
structure IsRelaxSol (σ : ℝ) (P A : E →L[ℝ] E) (mom : E →L[ℝ] F) (cl : F → E) (U : Set F)
    (ε τ : ℝ) (f : ℝ → E) : Prop where
  ode : ODESolution (relaxField σ P A mom cl ε) f 0 τ
  start : P (f 0) = f 0
  mem : ∀ t ∈ Icc 0 τ, mom (f t) ∈ U
  cons : ∀ t ∈ Icc 0 τ, mom (P (cl (mom (f t)))) = mom (f t)

/-- The forcing `σ (P ℳ'(mom f) mom P A f - P A f)` of the defect equation. -/
noncomputable def forcing (σ : ℝ) (P A : E →L[ℝ] E) (mom : E →L[ℝ] F) (cl' : F → F →L[ℝ] E)
    (f : E) : E :=
  σ • (P (cl' (mom f) (mom (P (A f)))) - P (A f))

namespace IsRelaxSol

variable {σ : ℝ} {P A : E →L[ℝ] E} {mom : E →L[ℝ] F} {cl : F → E} {cl' : F → F →L[ℝ] E}
  {U : Set F} {ε τ L c₀ : ℝ} {f : ℝ → E}

/-- A substep stays in the range of `P`: in Eqs. (19)-(21) of arXiv 1804.04561, `V`, resp. `X`,
stays constant. -/
theorem mem_range (h : IsRelaxSol σ P A mom cl U ε τ f) (hP : IsOrthProj P) :
    ∀ t ∈ Icc (0 : ℝ) τ, P (f t) = f t := by
  refine range_invariant_of_deriv_mem_range hP h.ode.cont
    (G := fun t => σ • (A (f t) + ε⁻¹ • (cl (mom (f t)) - f t))) (fun t ht => ?_) h.start
  have := h.ode.deriv t ht
  simp only [relaxField] at this
  rw [map_smul]
  exact this

/-- The projected field along a solution, in terms of the defect (arXiv 1804.04561, Section 4).
-/
theorem field_eq (h : IsRelaxSol σ P A mom cl U ε τ f) (hP : IsOrthProj P) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) τ) :
    relaxField σ P A mom cl ε t (f t) = σ • (P (A (f t)) + ε⁻¹ • defect P mom cl (f t)) := by
  simp only [relaxField, defect, map_add, map_smul, map_sub, h.mem_range hP t ht]

/-- The stiff part conserves the moments.
(arXiv 1804.04561, Section 4.) -/
theorem mom_deriv (h : IsRelaxSol σ P A mom cl U ε τ f) (hP : IsOrthProj P) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) τ) :
    HasDerivWithinAt (fun s => mom (f s)) (σ • mom (P (A (f t)))) (Ici t) t := by
  have ht' := Ico_subset_Icc_self ht
  have h1 := mom.hasFDerivAt.comp_hasDerivWithinAt t (h.ode.deriv t ht)
  have h2 : mom (relaxField σ P A mom cl ε t (f t)) = σ • mom (P (A (f t))) := by
    rw [h.field_eq hP ht']
    simp only [map_smul, map_add, defect, map_sub, h.cons t ht', sub_self, smul_zero, add_zero]
  rw [h2] at h1
  exact h1

/-- The defect equation `R' = b - σ ε⁻¹ R` (arXiv 1804.04561, Section 4). -/
theorem defect_deriv (h : IsRelaxSol σ P A mom cl U ε τ f) (hP : IsOrthProj P)
    (hc : IsClosure cl cl' U L c₀) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) τ) :
    HasDerivWithinAt (fun s => defect P mom cl (f s))
      (forcing σ P A mom cl' (f t) - (σ * ε⁻¹) • defect P mom cl (f t)) (Ici t) t := by
  have ht' := Ico_subset_Icc_self ht
  have hcl := hc.hasFDerivAt _ (h.mem t ht')
  have h1 := (P.hasFDerivAt.comp _ hcl).comp_hasDerivWithinAt t (h.mom_deriv hP ht)
  have h2 := h1.sub (h.ode.deriv t ht)
  have e : forcing σ P A mom cl' (f t) - (σ * ε⁻¹) • defect P mom cl (f t) =
      (P.comp (cl' (mom (f t)))) (σ • mom (P (A (f t)))) -
        relaxField σ P A mom cl ε t (f t) := by
    rw [h.field_eq hP ht']
    simp only [forcing, ContinuousLinearMap.comp_apply, map_smul, smul_add, smul_sub, smul_smul]
    abel
  rw [e]
  exact h2

/-- Continuity of the defect (arXiv 1804.04561, Section 4). -/
theorem defect_continuousOn (h : IsRelaxSol σ P A mom cl U ε τ f)
    (hc : IsClosure cl cl' U L c₀) :
    ContinuousOn (fun s => defect P mom cl (f s)) (Icc 0 τ) := by
  have hm : ContinuousOn (fun s => mom (f s)) (Icc 0 τ) :=
    mom.continuous.comp_continuousOn h.ode.cont
  have hcl : ContinuousOn (fun s => cl (mom (f s))) (Icc 0 τ) := fun t ht =>
    ContinuousAt.comp_continuousWithinAt (g := cl) (f := fun s => mom (f s))
      (hc.hasFDerivAt _ (h.mem t ht)).continuousAt (hm t ht)
  exact (P.continuous.comp_continuousOn hcl).sub h.ode.cont

/-- The solution is controlled by its moments and its defect (arXiv 1804.04561, Section 4). -/
theorem norm_le (h : IsRelaxSol σ P A mom cl U ε τ f) (hP : IsOrthProj P)
    (hc : IsClosure cl cl' U L c₀) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) τ) :
    ‖f t‖ ≤ c₀ + L * ‖mom (f t)‖ + ‖defect P mom cl (f t)‖ := by
  have e : f t = P (cl (mom (f t))) - defect P mom cl (f t) := by simp [defect]
  have e' : ‖f t‖ = ‖P (cl (mom (f t))) - defect P mom cl (f t)‖ := congrArg norm e
  rw [e']
  have h1 := norm_sub_le (P (cl (mom (f t)))) (defect P mom cl (f t))
  have h2 := hP.norm_le (cl (mom (f t)))
  have h3 := hc.growth _ (h.mem t ht)
  linarith

end IsRelaxSol

lemma forcing_le {σ : ℝ} {P A : E →L[ℝ] E} {mom : E →L[ℝ] F} {cl : F → E}
    {cl' : F → F →L[ℝ] E} {U : Set F} {L c₀ : ℝ} (hP : IsOrthProj P)
    (hc : IsClosure cl cl' U L c₀) (hσ : |σ| ≤ 1) {x : E} (hx : mom x ∈ U) :
    ‖forcing σ P A mom cl' x‖ ≤ (L * ‖mom‖ + 1) * ‖A‖ * ‖x‖ := by
  have hA : ‖A x‖ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x
  have hPA : ‖P (A x)‖ ≤ ‖A‖ * ‖x‖ := (hP.norm_le _).trans hA
  have hm : ‖mom (P (A x))‖ ≤ ‖mom‖ * (‖A‖ * ‖x‖) :=
    (mom.le_opNorm _).trans (mul_le_mul_of_nonneg_left hPA (norm_nonneg _))
  have hcl : ‖cl' (mom x) (mom (P (A x)))‖ ≤ L * (‖mom‖ * (‖A‖ * ‖x‖)) :=
    ((cl' (mom x)).le_opNorm _).trans
      (mul_le_mul (hc.deriv_le _ hx) hm (norm_nonneg _) hc.L_nonneg)
  have hPcl := (hP.norm_le _).trans hcl
  have hsub := norm_sub_le (P (cl' (mom x) (mom (P (A x))))) (P (A x))
  have hnn : 0 ≤ (L * ‖mom‖ + 1) * ‖A‖ * ‖x‖ := by
    have := hc.L_nonneg
    positivity
  rw [forcing, norm_smul, Real.norm_eq_abs]
  calc |σ| * ‖P (cl' (mom x) (mom (P (A x)))) - P (A x)‖
      ≤ 1 * ((L * ‖mom‖ + 1) * ‖A‖ * ‖x‖) :=
        mul_le_mul hσ (by nlinarith) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- The growth rate of the Lyapunov function of `lyapunov_le`. -/
noncomputable def relaxRate (a cm L c₀ : ℝ) : ℝ :=
  4 * ((L * cm + 1) * a + cm * a) * (c₀ + L + 1)

/-- A uniform bound for the defect and the moments of a relaxing substep. -/
noncomputable def relaxZ (a cm L c₀ τ z : ℝ) : ℝ :=
  z * Real.exp (relaxRate a cm L c₀ * τ)

/-- A uniform bound for the forcing of the defect equation of a relaxing substep. -/
noncomputable def relaxB (a cm L c₀ τ z : ℝ) : ℝ :=
  (L * cm + 1) * a * (c₀ + (L + 1) * relaxZ a cm L c₀ τ z)

/-- The constant of the moment estimate `moment_limit`. -/
noncomputable def limitC (a cm L c₀ τ z : ℝ) : ℝ :=
  let j := cm * a
  let Zb := relaxZ a cm L c₀ τ z
  Real.exp (j * L * τ) * (j * Zb + (j * L * (j * Zb) + j * relaxB a cm L c₀ τ z) * τ) + j * Zb

namespace IsRelaxSol

variable {P A : E →L[ℝ] E} {mom : E →L[ℝ] F} {cl : F → E} {cl' : F → F →L[ℝ] E}
  {U : Set F} {ε τ L c₀ : ℝ} {f : ℝ → E}

/-- The energy estimate, uniform in `ε`: nothing is assumed about the size of `f`.
(arXiv 1804.04561, Section 4.) -/
theorem lyapunov_le (h : IsRelaxSol 1 P A mom cl U ε τ f) (hP : IsOrthProj P)
    (hc : IsClosure cl cl' U L c₀) (hε : 0 < ε) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) τ) :
    ‖defect P mom cl (f t)‖ ^ 2 + ‖mom (f t)‖ ^ 2 + 1 ≤
      (‖defect P mom cl (f 0)‖ ^ 2 + ‖mom (f 0)‖ ^ 2 + 1) *
        Real.exp (relaxRate ‖A‖ ‖mom‖ L c₀ * t) := by
  have hR := fun s (hs : s ∈ Ico (0 : ℝ) τ) => h.defect_deriv hP hc hs
  have hm := fun s (hs : s ∈ Ico (0 : ℝ) τ) => h.mom_deriv hP hs
  have hL := hc.L_nonneg
  have hc₀ := hc.c₀_nonneg
  refine scalar_gronwall (Z := fun s => ‖defect P mom cl (f s)‖ ^ 2 + ‖mom (f s)‖ ^ 2 + 1)
    (Z' := fun s => 2 * ⟪defect P mom cl (f s),
        forcing 1 P A mom cl' (f s) - ((1 : ℝ) * ε⁻¹) • defect P mom cl (f s)⟫ +
      2 * ⟪mom (f s), (1 : ℝ) • mom (P (A (f s)))⟫)
    (κ := relaxRate ‖A‖ ‖mom‖ L c₀) ?_ ?_ ?_ ht
  · have h1 := h.defect_continuousOn hc
    have h2 : ContinuousOn (fun s => mom (f s)) (Icc 0 τ) :=
      mom.continuous.comp_continuousOn h.ode.cont
    exact ((h1.norm.pow 2).add (h2.norm.pow 2)).add continuousOn_const
  · intro s hs
    exact ((hR s hs).norm_sq.add (hm s hs).norm_sq).add_const 1
  · intro s hs
    have hs' := Ico_subset_Icc_self hs
    set r := ‖defect P mom cl (f s)‖
    set q := ‖mom (f s)‖
    have hr0 : 0 ≤ r := norm_nonneg _
    have hq0 : 0 ≤ q := norm_nonneg _
    have hf := h.norm_le hP hc hs'
    have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
    have hm0 : 0 ≤ ‖mom‖ := norm_nonneg _
    set C₁ := (L * ‖mom‖ + 1) * ‖A‖ with hC₁
    set C₂ := ‖mom‖ * ‖A‖ with hC₂
    have hC₁0 : 0 ≤ C₁ := by positivity
    have hC₂0 : 0 ≤ C₂ := by positivity
    have hb : ‖forcing 1 P A mom cl' (f s)‖ ≤ C₁ * (c₀ + L * q + r) :=
      (forcing_le hP hc (by simp) (h.mem s hs')).trans
        (mul_le_mul_of_nonneg_left hf hC₁0)
    have hmd : ‖mom (P (A (f s)))‖ ≤ C₂ * (c₀ + L * q + r) := by
      have h1 : ‖P (A (f s))‖ ≤ ‖A‖ * ‖f s‖ := (hP.norm_le _).trans (A.le_opNorm _)
      have h2 : ‖mom (P (A (f s)))‖ ≤ ‖mom‖ * (‖A‖ * ‖f s‖) :=
        (mom.le_opNorm _).trans (mul_le_mul_of_nonneg_left h1 hm0)
      calc _ ≤ ‖mom‖ * (‖A‖ * ‖f s‖) := h2
        _ = C₂ * ‖f s‖ := by rw [hC₂]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hf hC₂0
    have i1 : ⟪defect P mom cl (f s),
        forcing 1 P A mom cl' (f s) - ((1 : ℝ) * ε⁻¹) • defect P mom cl (f s)⟫ ≤
        r * ‖forcing 1 P A mom cl' (f s)‖ := by
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
      have h1 := real_inner_le_norm (defect P mom cl (f s)) (forcing 1 P A mom cl' (f s))
      have h2 : 0 ≤ (1 : ℝ) * ε⁻¹ * r ^ 2 := by positivity
      linarith
    have i2 : ⟪mom (f s), (1 : ℝ) • mom (P (A (f s)))⟫ ≤ q * ‖mom (P (A (f s)))‖ := by
      rw [one_smul]
      exact real_inner_le_norm _ _
    have hS : 0 ≤ c₀ + L * q + r := by positivity
    have i3 : r * ‖forcing 1 P A mom cl' (f s)‖ + q * ‖mom (P (A (f s)))‖ ≤
        (C₁ + C₂) * ((r + q) * (c₀ + L * q + r)) := by
      have h1 := mul_le_mul_of_nonneg_left hb hr0
      have h2 := mul_le_mul_of_nonneg_left hmd hq0
      have h3 : 0 ≤ C₂ * r * (c₀ + L * q + r) := by positivity
      have h4 : 0 ≤ C₁ * q * (c₀ + L * q + r) := by positivity
      nlinarith
    have i4 := mul_le_mul_of_nonneg_left (poly_bound (r := r) (s := q) hc₀ hL)
      (add_nonneg hC₁0 hC₂0)
    have e : relaxRate ‖A‖ ‖mom‖ L c₀ * (r ^ 2 + q ^ 2 + 1) =
        2 * ((C₁ + C₂) * (2 * (c₀ + L + 1) * (r ^ 2 + q ^ 2 + 1))) := by
      rw [relaxRate, hC₁, hC₂]
      ring
    rw [e]
    linarith

/-- Uniform bounds on `[0, τ]`.
(arXiv 1804.04561, Section 4.) -/
theorem bounds (h : IsRelaxSol 1 P A mom cl U ε τ f) (hP : IsOrthProj P)
    (hc : IsClosure cl cl' U L c₀) (hε : 0 < ε) {z : ℝ}
    (hz : ‖defect P mom cl (f 0)‖ ^ 2 + ‖mom (f 0)‖ ^ 2 + 1 ≤ z) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) τ) :
    ‖defect P mom cl (f t)‖ ≤ relaxZ ‖A‖ ‖mom‖ L c₀ τ z ∧
      ‖mom (f t)‖ ≤ relaxZ ‖A‖ ‖mom‖ L c₀ τ z ∧
      ‖forcing 1 P A mom cl' (f t)‖ ≤ relaxB ‖A‖ ‖mom‖ L c₀ τ z := by
  have hL := hc.L_nonneg
  have hc₀ := hc.c₀_nonneg
  have hly := h.lyapunov_le hP hc hε ht
  have hκ : 0 ≤ relaxRate ‖A‖ ‖mom‖ L c₀ := by
    rw [relaxRate]
    positivity
  have hexp : Real.exp (relaxRate ‖A‖ ‖mom‖ L c₀ * t) ≤
      Real.exp (relaxRate ‖A‖ ‖mom‖ L c₀ * τ) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hκ)
  have hz0 : 0 ≤ z := le_trans (by positivity) hz
  have hZ : ‖defect P mom cl (f t)‖ ^ 2 + ‖mom (f t)‖ ^ 2 + 1 ≤ relaxZ ‖A‖ ‖mom‖ L c₀ τ z := by
    refine hly.trans ?_
    rw [relaxZ]
    exact mul_le_mul hz hexp (Real.exp_pos _).le hz0
  set r := ‖defect P mom cl (f t)‖
  set q := ‖mom (f t)‖
  have h1 : r ≤ relaxZ ‖A‖ ‖mom‖ L c₀ τ z := by nlinarith [sq_nonneg (r - 1), sq_nonneg q]
  have h2 : q ≤ relaxZ ‖A‖ ‖mom‖ L c₀ τ z := by nlinarith [sq_nonneg (q - 1), sq_nonneg r]
  refine ⟨h1, h2, ?_⟩
  have hf := h.norm_le hP hc ht
  have hC : 0 ≤ (L * ‖mom‖ + 1) * ‖A‖ := by positivity
  have hb := forcing_le (A := A) (cl' := cl') (σ := 1) hP hc (by simp) (h.mem t ht)
  refine hb.trans ?_
  rw [relaxB]
  refine mul_le_mul_of_nonneg_left (hf.trans ?_) hC
  have : L * q ≤ L * relaxZ ‖A‖ ‖mom‖ L c₀ τ z := mul_le_mul_of_nonneg_left h2 hL
  nlinarith

/-- **Relaxation of a substep.**  Along every solution of a relaxing substep the defect of the
constraint `f = P M(f)` satisfies
`‖P M(f t) - f t‖ ≤ e^{-t/ε} ‖P M(f 0) - f 0‖ + ε B`, where `B` does not depend on `ε`.
(arXiv 1804.04561, Section 4.) -/
theorem defect_le (h : IsRelaxSol 1 P A mom cl U ε τ f) (hP : IsOrthProj P)
    (hc : IsClosure cl cl' U L c₀) (hε : 0 < ε) {z : ℝ}
    (hz : ‖defect P mom cl (f 0)‖ ^ 2 + ‖mom (f 0)‖ ^ 2 + 1 ≤ z) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) τ) :
    ‖defect P mom cl (f t)‖ ≤
      Real.exp (-t / ε) * ‖defect P mom cl (f 0)‖ + ε * relaxB ‖A‖ ‖mom‖ L c₀ τ z := by
  have hdec := relax_decay (R := fun s => defect P mom cl (f s))
    (b := fun s => forcing 1 P A mom cl' (f s)) (B := relaxB ‖A‖ ‖mom‖ L c₀ τ z) hε
    (h.defect_continuousOn hc)
    (fun s hs => by simpa using h.defect_deriv hP hc hs)
    (fun s hs => (h.bounds hP hc hε hz (Ico_subset_Icc_self hs)).2.2) ht
  have hB0 : 0 ≤ relaxB ‖A‖ ‖mom‖ L c₀ τ z :=
    (norm_nonneg _).trans (h.bounds hP hc hε hz ht).2.2
  have hexp : 0 ≤ Real.exp (-t / ε) := (Real.exp_pos _).le
  have : ε * relaxB ‖A‖ ‖mom‖ L c₀ τ z * (1 - Real.exp (-t / ε)) ≤
      ε * relaxB ‖A‖ ‖mom‖ L c₀ τ z := by
    have h3 : 0 ≤ ε * relaxB ‖A‖ ‖mom‖ L c₀ τ z := by positivity
    nlinarith
  linarith

end IsRelaxSol

namespace IsRelaxSol

variable {P A : E →L[ℝ] E} {mom : E →L[ℝ] F} {cl : F → E} {cl' : F → F →L[ℝ] E}
  {U : Set F} {ε τ L c₀ : ℝ} {f : ℝ → E}

/-- **The fluid limit of the moments.**  The moments of a relaxing substep stay within `O(ε)` of the
solution `m₀` of the closed moment system `μ' = mom (P (A (P (ℳ μ))))`.
(arXiv 1804.04561, Section 4.) -/
theorem moment_limit (h : IsRelaxSol 1 P A mom cl U ε τ f) (hP : IsOrthProj P)
    (hc : IsClosure cl cl' U L c₀) (hε : 0 < ε) {z : ℝ}
    (hz : ‖defect P mom cl (f 0)‖ ^ 2 + ‖mom (f 0)‖ ^ 2 + 1 ≤ z) {m₀ : ℝ → F}
    (hm₀ : ODESolution (reducedField P A mom cl) m₀ 0 τ) (h0 : m₀ 0 = mom (f 0))
    (hU : ∀ t ∈ Icc (0 : ℝ) τ, m₀ t ∈ U) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) τ) :
    ‖mom (f t) - m₀ t‖ ≤ ε * limitC ‖A‖ ‖mom‖ L c₀ τ z := by
  set J : E →L[ℝ] F := mom.comp (P.comp A) with hJ
  set j := ‖mom‖ * ‖A‖ with hjdef
  have hj0 : 0 ≤ j := by positivity
  have hL := hc.L_nonneg
  have hJle : ∀ x, ‖J x‖ ≤ j * ‖x‖ := fun x => by
    have h1 : ‖P (A x)‖ ≤ ‖A‖ * ‖x‖ := (hP.norm_le _).trans (A.le_opNorm _)
    calc ‖J x‖ = ‖mom (P (A x))‖ := rfl
      _ ≤ ‖mom‖ * ‖P (A x)‖ := mom.le_opNorm _
      _ ≤ ‖mom‖ * (‖A‖ * ‖x‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = _ := by rw [hjdef]; ring
  set Zb := relaxZ ‖A‖ ‖mom‖ L c₀ τ z with hZb
  set B := relaxB ‖A‖ ‖mom‖ L c₀ τ z with hB
  have hbd := fun s (hs : s ∈ Icc (0 : ℝ) τ) => h.bounds hP hc hε hz hs
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hbd t ht).2.2
  have hZb0 : 0 ≤ Zb := (norm_nonneg _).trans (hbd t ht).1
  set η := j * L * (j * Zb) + j * B with hη
  have hη0 : 0 ≤ η := by positivity
  set R : ℝ → E := fun s => defect P mom cl (f s) with hR
  set ψ : ℝ → F := fun s => mom (f s) - m₀ s - ε • J (R s) with hψ
  have hψc : ContinuousOn ψ (Icc 0 τ) := by
    have h1 : ContinuousOn (fun s => mom (f s)) (Icc 0 τ) :=
      mom.continuous.comp_continuousOn h.ode.cont
    have h2 : ContinuousOn (fun s => J (R s)) (Icc 0 τ) :=
      J.continuous.comp_continuousOn (h.defect_continuousOn hc)
    exact (h1.sub hm₀.cont).sub (continuousOn_const.smul h2)
  have hψd : ∀ s ∈ Ico (0 : ℝ) τ, HasDerivWithinAt ψ
      (((1 : ℝ) • mom (P (A (f s))) - reducedField P A mom cl s (m₀ s)) -
        ε • J (forcing 1 P A mom cl' (f s) - ((1 : ℝ) * ε⁻¹) • R s)) (Ici s) s := fun s hs =>
    ((h.mom_deriv hP hs).sub (hm₀.deriv s hs)).sub
      ((J.hasFDerivAt.comp_hasDerivWithinAt s (h.defect_deriv hP hc hs)).const_smul ε)
  have hψ0 : ‖ψ 0‖ ≤ ε * (j * Zb) := by
    have e : ψ 0 = -(ε • J (R 0)) := by
      simp only [hψ, h0, sub_self, zero_sub]
    rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    refine mul_le_mul_of_nonneg_left ?_ hε.le
    exact (hJle _).trans (mul_le_mul_of_nonneg_left (hbd 0 ⟨le_rfl, ht.1.trans ht.2⟩).1 hj0)
  have hsplit : ∀ s, mom (f s) - m₀ s = ψ s + ε • J (R s) := fun s => by
    simp only [hψ]
    abel
  have hstep : ∀ s ∈ Icc (0 : ℝ) τ, ‖mom (f s) - m₀ s‖ ≤ ‖ψ s‖ + ε * (j * Zb) := fun s hs => by
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    exact mul_le_mul_of_nonneg_left
      ((hJle _).trans (mul_le_mul_of_nonneg_left (hbd s hs).1 hj0)) hε.le
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (δ := ε * (j * Zb)) (K := j * L)
    (ε := ε * η) hψc hψd hψ0 (fun s hs => by
      have hs' := Ico_subset_Icc_self hs
      have e : ((1 : ℝ) • mom (P (A (f s))) - reducedField P A mom cl s (m₀ s)) -
          ε • J (forcing 1 P A mom cl' (f s) - ((1 : ℝ) * ε⁻¹) • R s) =
          J (P (cl (mom (f s)) - cl (m₀ s))) - ε • J (forcing 1 P A mom cl' (f s)) := by
        have e1 : ε • ((1 : ℝ) * ε⁻¹) • J (R s) = J (R s) := by
          rw [smul_smul, one_mul, mul_inv_cancel₀ hε.ne', one_smul]
        have e2 : f s = P (cl (mom (f s))) - R s := by simp [hR, defect]
        have e3 : mom (P (A (f s))) = J (P (cl (mom (f s)))) - J (R s) := by
          conv_lhs => rw [e2]
          simp only [map_sub, hJ, ContinuousLinearMap.comp_apply]
        have e4 : reducedField P A mom cl s (m₀ s) = J (P (cl (m₀ s))) := rfl
        rw [one_smul, e3, e4, map_sub J, smul_sub, map_smul J, e1, map_sub P, map_sub J]
        abel
      rw [e]
      have h1 : ‖J (P (cl (mom (f s)) - cl (m₀ s)))‖ ≤ j * (L * ‖mom (f s) - m₀ s‖) :=
        (hJle _).trans (mul_le_mul_of_nonneg_left
          ((hP.norm_le _).trans (hc.lipschitz (h.mem s hs') (hU s hs'))) hj0)
      have h2 : ‖ε • J (forcing 1 P A mom cl' (f s))‖ ≤ ε * (j * B) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
        exact mul_le_mul_of_nonneg_left
          ((hJle _).trans (mul_le_mul_of_nonneg_left (hbd s hs').2.2 hj0)) hε.le
      have h3 := hstep s hs'
      have h4 : j * (L * ‖mom (f s) - m₀ s‖) ≤ j * L * ‖ψ s‖ + ε * (j * L * (j * Zb)) := by
        have := mul_le_mul_of_nonneg_left h3 (mul_nonneg hj0 hL)
        nlinarith
      calc _ ≤ ‖J (P (cl (mom (f s)) - cl (m₀ s)))‖ + ‖ε • J (forcing 1 P A mom cl' (f s))‖ :=
            norm_sub_le _ _
        _ ≤ j * L * ‖ψ s‖ + ε * η := by rw [hη]; nlinarith) t ht
  rw [sub_zero] at hgr
  have hexp : Real.exp (j * L * t) ≤ Real.exp (j * L * τ) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 (by positivity))
  have hexp1 : 1 ≤ Real.exp (j * L * t) :=
    Real.one_le_exp (mul_nonneg (mul_nonneg hj0 hL) ht.1)
  have hg2 := gronwallBound_le_exp_mul_add_max (δ := ε * (j * Zb)) (K := j * L)
    (η := ε * η) (x := t) (mul_nonneg hε.le hη0) ht.1
  rw [max_eq_right hexp1] at hg2
  have hψt : ‖ψ t‖ ≤ ε * (Real.exp (j * L * τ) * (j * Zb + η * τ)) := by
    refine hgr.trans (hg2.trans ?_)
    have hexp0 := (Real.exp_pos (j * L * t)).le
    have h1 : Real.exp (j * L * t) * (ε * (j * Zb)) ≤ Real.exp (j * L * τ) * (ε * (j * Zb)) :=
      mul_le_mul_of_nonneg_right hexp (by positivity)
    have h2 : ε * η * t * Real.exp (j * L * t) ≤ ε * η * τ * Real.exp (j * L * τ) := by
      have h3 : ε * η * t ≤ ε * η * τ := mul_le_mul_of_nonneg_left ht.2 (by positivity)
      exact mul_le_mul h3 hexp hexp0 (by have := ht.1.trans ht.2; positivity)
    calc _ ≤ Real.exp (j * L * τ) * (ε * (j * Zb)) + ε * η * τ * Real.exp (j * L * τ) :=
          add_le_add h1 h2
      _ = _ := by ring
  have hC : limitC ‖A‖ ‖mom‖ L c₀ τ z =
      Real.exp (j * L * τ) * (j * Zb + η * τ) + j * Zb := rfl
  rw [hC]
  have := hstep t ht
  nlinarith

/-- **The singular limit of a relaxing substep** (arXiv 1804.04561, Section 4, made rigorous).  If
`m₀` solves the closed moment system, then
`‖f t - P ℳ(m₀ t)‖ ≤ e^{-t/ε} ‖P M(f 0) - f 0‖ + O(ε)`, uniformly on `[0, τ]`. -/
theorem singular_limit (h : IsRelaxSol 1 P A mom cl U ε τ f) (hP : IsOrthProj P)
    (hc : IsClosure cl cl' U L c₀) (hε : 0 < ε) {z : ℝ}
    (hz : ‖defect P mom cl (f 0)‖ ^ 2 + ‖mom (f 0)‖ ^ 2 + 1 ≤ z) {m₀ : ℝ → F}
    (hm₀ : ODESolution (reducedField P A mom cl) m₀ 0 τ) (h0 : m₀ 0 = mom (f 0))
    (hU : ∀ t ∈ Icc (0 : ℝ) τ, m₀ t ∈ U) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) τ) :
    ‖f t - P (cl (m₀ t))‖ ≤ Real.exp (-t / ε) * ‖defect P mom cl (f 0)‖ +
      ε * (relaxB ‖A‖ ‖mom‖ L c₀ τ z + L * limitC ‖A‖ ‖mom‖ L c₀ τ z) := by
  have h1 := h.defect_le hP hc hε hz ht
  have h2 := h.moment_limit hP hc hε hz hm₀ h0 hU ht
  have h3 : ‖P (cl (mom (f t)) - cl (m₀ t))‖ ≤ L * ‖mom (f t) - m₀ t‖ :=
    (hP.norm_le _).trans (hc.lipschitz (h.mem t ht) (hU t ht))
  have e : f t - P (cl (m₀ t)) = P (cl (mom (f t)) - cl (m₀ t)) - defect P mom cl (f t) := by
    simp only [defect, map_sub]
    abel
  have h4 : L * ‖mom (f t) - m₀ t‖ ≤ L * (ε * limitC ‖A‖ ‖mom‖ L c₀ τ z) :=
    mul_le_mul_of_nonneg_left h2 hc.L_nonneg
  rw [e]
  calc _ ≤ ‖P (cl (mom (f t)) - cl (m₀ t))‖ + ‖defect P mom cl (f t)‖ := norm_sub_le _ _
    _ ≤ _ := by nlinarith

end IsRelaxSol

/-- **Rigorous form of Section 4 for a relaxing substep** (arXiv 1804.04561, Section 4: "if we take
`ε → 0` we obtain the constraint"; the paper argues formally).  Fix the data `f₀`, and let `f ε` be
any family of solutions of the projected BGK equation with `f ε 0 = f₀`.  Then for every `t > 0`,
`f ε t → P ℳ(m₀ t)` as `ε → 0⁺`, where `m₀` solves the closed moment system.  The limit satisfies
the constraint `f = P M(f)` of the paper, by `reduced_constraint`. -/
theorem tendsto_singular_limit {P A : E →L[ℝ] E} {mom : E →L[ℝ] F} {cl : F → E}
    {cl' : F → F →L[ℝ] E} {U : Set F} {τ L c₀ : ℝ} (hP : IsOrthProj P)
    (hc : IsClosure cl cl' U L c₀) {f₀ : E} {f : ℝ → ℝ → E}
    (hf : ∀ ε > 0, IsRelaxSol 1 P A mom cl U ε τ (f ε)) (hf0 : ∀ ε > 0, f ε 0 = f₀)
    {m₀ : ℝ → F} (hm₀ : ODESolution (reducedField P A mom cl) m₀ 0 τ) (h0 : m₀ 0 = mom f₀)
    (hU : ∀ t ∈ Icc (0 : ℝ) τ, m₀ t ∈ U) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) τ) :
    Tendsto (fun ε => f ε t) (𝓝[>] 0) (𝓝 (P (cl (m₀ t)))) := by
  set z := ‖defect P mom cl f₀‖ ^ 2 + ‖mom f₀‖ ^ 2 + 1 with hz
  set C := relaxB ‖A‖ ‖mom‖ L c₀ τ z + L * limitC ‖A‖ ‖mom‖ L c₀ τ z with hC
  have ht0 : 0 < t := ht.1
  have h1 : Tendsto (fun ε : ℝ => t * ε⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop ht0
  have h2 : Tendsto (fun ε : ℝ => Real.exp (-t / ε)) (𝓝[>] 0) (𝓝 0) := by
    have h3 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    refine h3.congr fun ε => ?_
    simp only [Function.comp_apply]
    congr 1
    ring
  have h4 : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have h5 : Tendsto (fun ε : ℝ => Real.exp (-t / ε) * ‖defect P mom cl f₀‖ + ε * C)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (h2.mul_const ‖defect P mom cl f₀‖).add (h4.mul_const C)
  refine tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h5)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  have hsol := hf ε hε'
  have hfε := hf0 ε hε'
  have := hsol.singular_limit hP hc hε' (z := z) (by rw [hfε]) hm₀ (by rw [hfε, h0]) hU
    (Ioc_subset_Icc_self ht)
  rwa [hfε] at this

/-- The limit of `tendsto_singular_limit` satisfies the constraint: `g = P ℳ(μ)` with
`mom g = μ` is a fixed point, `P M(g) = g`.  In the K-step this is
`K_j = ∫ V_j M(K) dv` of Section 4 of arXiv 1804.04561. -/
theorem reduced_constraint {P : E →L[ℝ] E} {mom : E →L[ℝ] F} {cl : F → E} {μ : F}
    (h : mom (P (cl μ)) = μ) : P (cl (mom (P (cl μ)))) = P (cl μ) := by
  rw [h]

/-- **The equilibria of the stiff part** (arXiv 1804.04561, Section 4).  For `f ∈ range P`,
`P (M f - f) = 0` holds if and only if `f = P M(f)`.  If moreover `P` represents the Maxwellian
exactly, `P M(f) = M(f)`, then `f = M(f)`: this is the last sentence of Section 4, "the dynamical
low-rank splitting would yield exactly the correct form of the distribution function". -/
theorem equilibrium_iff {P : E →L[ℝ] E} {M : E → E} {f : E} (hf : P f = f) :
    P (M f - f) = 0 ↔ f = P (M f) := by
  rw [map_sub, hf, sub_eq_zero, eq_comm]

/-- If the constraint `f = P M(f)` holds and `P` represents the Maxwellian, then `f` is Maxwellian
(arXiv 1804.04561, Section 4, last sentence). -/
theorem eq_maxwellian_of_exact {P : E →L[ℝ] E} {M : E → E} {f : E} (hc : f = P (M f))
    (hex : P (M f) = M f) : f = M f := hc.trans hex

/-- **The formal limit of Section 4 of arXiv 1804.04561, as a theorem**, for all three substeps
(`σ = 1` for K and L, `σ = -1` for S).  If `y_ε → y₀`, `y_ε' = A (y_ε) + σ ε⁻¹ (G (y_ε) - y_ε)`
with `G`, `A` continuous at `y₀`, and if `ε y_ε' → 0` (the derivative is not of order `1/ε`, which
is what the paper's formal step tacitly assumes), then `y₀ = G y₀`. -/
theorem formal_constraint {ι : Type*} {l : Filter ι} [l.NeBot] {ε : ι → ℝ}
    (hε : Tendsto ε l (𝓝 0)) (hne : ∀ᶠ i in l, ε i ≠ 0) {y ydot : ι → E} {y₀ : E}
    (hy : Tendsto y l (𝓝 y₀)) {G A : E → E} (hG : ContinuousAt G y₀) (hA : ContinuousAt A y₀)
    {σ : ℝ} (hσ : σ ≠ 0)
    (hydot : ∀ i, ydot i = A (y i) + (σ * (ε i)⁻¹) • (G (y i) - y i))
    (hb : Tendsto (fun i => ε i • ydot i) l (𝓝 0)) : y₀ = G y₀ := by
  have h1 : Tendsto (fun i => ε i • A (y i)) l (𝓝 ((0 : ℝ) • A y₀)) :=
    hε.smul (hA.tendsto.comp hy)
  have h2 : Tendsto (fun i => σ • (G (y i) - y i)) l (𝓝 (σ • (G y₀ - y₀))) :=
    ((hG.tendsto.comp hy).sub hy).const_smul σ
  have h3 := h1.add h2
  have h4 : Tendsto (fun i => ε i • ydot i) l (𝓝 ((0 : ℝ) • A y₀ + σ • (G y₀ - y₀))) := by
    refine h3.congr' ?_
    filter_upwards [hne] with i hi
    have e : ε i * (σ * (ε i)⁻¹) = σ := by field_simp
    change ε i • A (y i) + σ • (G (y i) - y i) = ε i • ydot i
    rw [hydot, smul_add, smul_smul, e]
  have h5 := tendsto_nhds_unique h4 hb
  rw [zero_smul, zero_add] at h5
  have h6 := (smul_eq_zero.1 h5).resolve_left hσ
  exact (sub_eq_zero.1 h6).symm

/-- **Pure relaxation is explicit** (`A = 0`, any sign `σ`): the moments are constant and the
defect is exactly `e^{-σ t / ε}` times its initial value.  For `σ = -1` (the S-step, Eq. (20)) the
defect grows like `e^{t/ε}`.
(arXiv 1804.04561, Section 4, on Eqs. (23)-(25).) -/
theorem pure_relaxation {σ : ℝ} {P : E →L[ℝ] E} {mom : E →L[ℝ] F} {cl : F → E} {U : Set F}
    {ε τ : ℝ} {f : ℝ → E} (h : IsRelaxSol σ P 0 mom cl U ε τ f) (hP : IsOrthProj P)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) τ) :
    mom (f t) = mom (f 0) ∧
      defect P mom cl (f t) = Real.exp (-σ * t / ε) • defect P mom cl (f 0) := by
  have hmc : ∀ s ∈ Icc (0 : ℝ) τ, mom (f s) = mom (f 0) :=
    constant_of_has_deriv_right_zero (mom.continuous.comp_continuousOn h.ode.cont)
      fun s hs => by simpa using h.mom_deriv hP hs
  refine ⟨hmc t ht, ?_⟩
  set g := P (cl (mom (f 0))) with hg
  have hdef : ∀ s ∈ Icc (0 : ℝ) τ, defect P mom cl (f s) = g - f s := fun s hs => by
    simp only [defect, hmc s hs, hg]
  set w : ℝ → ℝ := fun s => Real.exp (σ * s / ε) with hw
  have hw' : ∀ s, HasDerivAt w (σ * ε⁻¹ * w s) s := fun s => by
    have h1 : HasDerivAt (fun s : ℝ => σ * s / ε) (σ * ε⁻¹) s := by
      have := ((hasDerivAt_id' s).const_mul σ).div_const ε
      simpa [div_eq_mul_inv] using this
    have h2 := h1.exp
    rw [mul_comm] at h2
    exact h2
  have hy : ∀ s ∈ Icc (0 : ℝ) τ, w s • (g - f s) = g - f 0 := by
    have hconst := constant_of_has_deriv_right_zero (a := 0) (b := τ)
      (f := fun s => w s • (g - f s))
      (ContinuousOn.smul (fun s _ => (hw' s).continuousAt.continuousWithinAt)
        (continuousOn_const.sub h.ode.cont))
      (fun s hs => by
        have hs' := Ico_subset_Icc_self hs
        have h1 := (h.ode.deriv s hs).const_sub g
        have h2 := (hw' s).hasDerivWithinAt.smul h1
        have e : w s • (-relaxField σ P 0 mom cl ε s (f s)) + (σ * ε⁻¹ * w s) • (g - f s) = 0 := by
          rw [h.field_eq hP hs', hdef s hs']
          simp only [zero_apply, map_zero, zero_add, smul_neg, smul_smul]
          have e2 : w s * (σ * ε⁻¹) = σ * ε⁻¹ * w s := by ring
          rw [e2]
          abel
        rw [e] at h2
        exact h2)
    intro s hs
    have := hconst s hs
    simpa [hw] using this
  have hinv : Real.exp (-σ * t / ε) * w t = 1 := by
    simp only [hw]
    rw [← Real.exp_add]
    have : -σ * t / ε + σ * t / ε = 0 := by ring
    rw [this, Real.exp_zero]
  have h0 : defect P mom cl (f 0) = g - f 0 := hdef 0 ⟨le_rfl, ht.1.trans ht.2⟩
  rw [hdef t ht, h0, ← hy t ht, smul_smul, hinv, one_smul]

/-- **The S-step repels the constraint.**  With transport, along an S-step solution bounded by `Φ`,
`e^{t/ε} (‖R 0‖ - ε B) ≤ ‖R t‖` for the defect `R = P M(f) - f`, `B = (L ‖mom‖ + 1) ‖A‖ Φ`.
(arXiv 1804.04561, Section 4, on Eq. (24).) -/
theorem IsRelaxSol.defect_ge {P A : E →L[ℝ] E} {mom : E →L[ℝ] F} {cl : F → E}
    {cl' : F → F →L[ℝ] E} {U : Set F} {ε τ L c₀ Φ : ℝ} {f : ℝ → E}
    (h : IsRelaxSol (-1) P A mom cl U ε τ f) (hP : IsOrthProj P)
    (hc : IsClosure cl cl' U L c₀) (hε : 0 < ε) (hΦ : 0 ≤ Φ)
    (hbd : ∀ t ∈ Icc (0 : ℝ) τ, ‖f t‖ ≤ Φ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) τ) :
    Real.exp (t / ε) * (‖defect P mom cl (f 0)‖ - ε * ((L * ‖mom‖ + 1) * ‖A‖ * Φ)) ≤
      ‖defect P mom cl (f t)‖ := by
  have hL := hc.L_nonneg
  refine relax_growth (R := fun s => defect P mom cl (f s))
    (b := fun s => forcing (-1) P A mom cl' (f s)) hε (by positivity)
    (h.defect_continuousOn hc) (fun s hs => ?_) (fun s hs => ?_) ht
  · have := h.defect_deriv hP hc hs
    simpa [sub_eq_add_neg] using this
  · have hs' := Ico_subset_Icc_self hs
    refine (forcing_le hP hc (by simp) (h.mem s hs')).trans ?_
    exact mul_le_mul_of_nonneg_left (hbd s hs') (by positivity)

/-- **The S-step does not enforce its constraint** (compare arXiv 1804.04561, Section 4, on
Eq. (24); the paper only sets `1/ε`-terms to zero).  Fix `f₀` with `P M(f₀) ≠ f₀`, `τ > 0` and any
bound `Φ`.  For all sufficiently small `ε`, every solution of the S-step (20) on `[0, τ]` from `f₀`
exceeds `Φ` somewhere: as `ε → 0` the S-step does not converge to the constraint, it diverges. -/
theorem sStep_unbounded {P A : E →L[ℝ] E} {mom : E →L[ℝ] F} {cl : F → E}
    {cl' : F → F →L[ℝ] E} {U : Set F} {τ L c₀ : ℝ} (hP : IsOrthProj P)
    (hc : IsClosure cl cl' U L c₀) {f₀ : E} (hf₀ : defect P mom cl f₀ ≠ 0) (hτ : 0 < τ) (Φ : ℝ) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ f : ℝ → E, IsRelaxSol (-1) P A mom cl U ε τ f →
      f 0 = f₀ → ∃ s ∈ Icc (0 : ℝ) τ, Φ < ‖f s‖ := by
  have hL := hc.L_nonneg
  have hc₀ := hc.c₀_nonneg
  set ρ₀ := ‖defect P mom cl f₀‖ with hρ₀
  have hρ : 0 < ρ₀ := norm_pos_iff.2 hf₀
  set Ψ := |Φ| with hΨ
  have hΨ0 : 0 ≤ Ψ := abs_nonneg Φ
  set B := (L * ‖mom‖ + 1) * ‖A‖ * Ψ with hB
  have hB0 : 0 ≤ B := by positivity
  set Q := c₀ + L * (‖mom‖ * Ψ) + Ψ with hQ
  have hQ0 : 0 ≤ Q := by positivity
  refine ⟨min (ρ₀ / (2 * (B + 1))) (τ * ρ₀ / (2 * (Q + 1))), by positivity, ?_⟩
  rintro ε ⟨hε, hεlt⟩ f hf hf0
  by_contra hcon
  push Not at hcon
  have hbd : ∀ s ∈ Icc (0 : ℝ) τ, ‖f s‖ ≤ Ψ := fun s hs => (hcon s hs).trans (le_abs_self Φ)
  have ht : τ ∈ Icc (0 : ℝ) τ := ⟨hτ.le, le_rfl⟩
  have hge := hf.defect_ge hP hc hε hΨ0 hbd ht
  rw [hf0] at hge
  have h1 : ε < ρ₀ / (2 * (B + 1)) := hεlt.trans_le (min_le_left _ _)
  have h2 : ε < τ * ρ₀ / (2 * (Q + 1)) := hεlt.trans_le (min_le_right _ _)
  have h1' : ε * (2 * (B + 1)) < ρ₀ := (lt_div_iff₀ (by positivity)).1 h1
  have h2' : ε * (2 * (Q + 1)) < τ * ρ₀ := (lt_div_iff₀ (by positivity)).1 h2
  have h3 : ρ₀ / 2 ≤ ρ₀ - ε * B := by nlinarith
  have hup : ‖defect P mom cl (f τ)‖ ≤ Q := by
    have hm : ‖mom (f τ)‖ ≤ ‖mom‖ * Ψ :=
      (mom.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hbd τ ht) (norm_nonneg _))
    have h4 : ‖P (cl (mom (f τ)))‖ ≤ c₀ + L * ‖mom (f τ)‖ :=
      (hP.norm_le _).trans (hc.growth _ (hf.mem τ ht))
    have h5 := norm_sub_le (P (cl (mom (f τ)))) (f τ)
    have h6 : L * ‖mom (f τ)‖ ≤ L * (‖mom‖ * Ψ) := mul_le_mul_of_nonneg_left hm hL
    have h7 := hbd τ ht
    simp only [defect]
    linarith
  have hexp : τ / ε + 1 ≤ Real.exp (τ / ε) := Real.add_one_le_exp _
  have hratio : (Q + 1) ≤ (τ / ε) * (ρ₀ / 2) := by
    rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
    nlinarith
  have hfin : (τ / ε) * (ρ₀ / 2) ≤ Real.exp (τ / ε) * (ρ₀ - ε * B) := by
    have h8 : τ / ε ≤ Real.exp (τ / ε) := by linarith
    exact mul_le_mul h8 h3 (by positivity) (Real.exp_pos _).le
  linarith

end Relaxation

/-! ### Section 3: the scheme, discrete in `x` and `v` -/

section Scheme

variable {d : ℕ} {m n r q : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype q]
  [DecidableEq n] [DecidableEq r]

/-- The discrete transport term `f ↦ v · ∇ₓ f` on `f ∈ ℝ^{m × n}`, `f i j = f (x_i, v_j)`: the
matrix `D a` discretizes `∂_{x_a}` (no property of it is used) and `ξ j` is the velocity node `v_j`:
`(v · ∇ₓ f) = ∑ₐ Dₐ f diag (ξ · a)`. -/
noncomputable def transport (D : Fin d → Matrix m m ℝ) (ξ : n → Vel d) :
    Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  ∑ a, (Frobenius.leftMulCLM (D a)).comp (Frobenius.rightMulCLM (Matrix.diagonal fun j => ξ j a))

lemma transport_apply (D : Fin d → Matrix m m ℝ) (ξ : n → Vel d) (f : Matrix m n ℝ) :
    transport D ξ f = ∑ a, D a * f * Matrix.diagonal fun j => ξ j a := by
  simp [transport, Matrix.mul_assoc]

/-- The right-hand side `-v · ∇ₓ f + ε⁻¹ (M f - f)` of Eqs. (4), (11) on the grid, with the
equilibrium map `M` as a parameter (the BGK collision operator `C (f) = M f - f`). -/
noncomputable def bgkField (D : Fin d → Matrix m m ℝ) (ξ : n → Vel d)
    (M : Matrix m n ℝ → Matrix m n ℝ) (ε : ℝ) (_t : ℝ) (f : Matrix m n ℝ) : Matrix m n ℝ :=
  -transport D ξ f + ε⁻¹ • (M f - f)

/-- The sign convention of Eq. (17): `g = v · ∇ₓ f - ε⁻¹ C (f)`, `∂ₜ f = -g`. -/
lemma bgkField_eq (D : Fin d → Matrix m m ℝ) (ξ : n → Vel d) (M : Matrix m n ℝ → Matrix m n ℝ)
    (ε t : ℝ) (f : Matrix m n ℝ) :
    bgkField D ξ M ε t f = -(transport D ξ f - ε⁻¹ • (M f - f)) := by
  simp only [bgkField]
  abel

/-- The coefficient `c¹_{jl} = ∫ v_a V_j V_l dv` of Eq. (23), component `a`. -/
noncomputable def cOne (ξ : n → Vel d) (V : Matrix n r ℝ) (a : Fin d) : Matrix r r ℝ :=
  Vᵀ * (Matrix.diagonal fun j => ξ j a) * V

/-- The coefficient `d¹_{il} = ∫ X_i ∂_{x_a} X_l dx` of Eq. (24), component `a`. -/
noncomputable def dOne (D : Fin d → Matrix m m ℝ) (X : Matrix m r ℝ) (a : Fin d) : Matrix r r ℝ :=
  Xᵀ * D a * X

omit [DecidableEq n] [DecidableEq r] in
/-- **Eq. (18)** (arXiv 1804.04561): `P (f) g = P_V g - P_V P_X g + P_X g`, on the grid.  That
`tangentProj X V` is the orthogonal projector onto the tangent space at `X S Vᵀ` is
`isOrthProj_tangentProj` and `mem_range_tangentProj`. -/
theorem eq18 (X : Matrix m r ℝ) (V : Matrix n r ℝ) (g : Matrix m n ℝ) :
    tangentProj X V g = rightProj V g - rightProj V (leftProj X g) + leftProj X g := by
  simp only [tangentProj_apply, rightProj_apply, leftProj_apply]
  abel

/-- **Eq. (17) and its three-term splitting** (arXiv 1804.04561), on the grid: with
`g = v · ∇ₓ f - ε⁻¹ C (f)`, the projected field is `-P (f) g = -P_V g + P_V P_X g - P_X g`.  The
three terms are the right-hand sides of Eqs. (19), (20), (21). -/
theorem eq17 (D : Fin d → Matrix m m ℝ) (ξ : n → Vel d) (M : Matrix m n ℝ → Matrix m n ℝ)
    (ε t : ℝ) (X : Matrix m r ℝ) (V : Matrix n r ℝ) (f : Matrix m n ℝ) :
    tangentProj X V (bgkField D ξ M ε t f) =
      -rightProj V (transport D ξ f - ε⁻¹ • (M f - f)) +
        rightProj V (leftProj X (transport D ξ f - ε⁻¹ • (M f - f))) -
        leftProj X (transport D ξ f - ε⁻¹ • (M f - f)) := by
  rw [bgkField_eq, map_neg, eq18]
  abel

variable {D : Fin d → Matrix m m ℝ} {ξ : n → Vel d} {M : Matrix m n ℝ → Matrix m n ℝ} {ε : ℝ}
  {V : Matrix n r ℝ} {X : Matrix m r ℝ}

/-- **Eq. (19)** (arXiv 1804.04561), on the grid: the K-step gives
`∂ₜ f = -P_V (v · ∇ₓ f - ε⁻¹ C (f))` for `f = K Vᵀ`, with `V` constant. -/
theorem eq19 {K : ℝ → Matrix m r ℝ} {t₀ t₁ : ℝ}
    (hK : ODESolution (MatrixKSL.kField V (bgkField D ξ M ε)) K t₀ t₁) :
    ODESolution (fun _ f => -rightProj V (transport D ξ f - ε⁻¹ • (M f - f)))
      (fun t => K t * Vᵀ) t₀ t₁ := by
  have h := MatrixKSL.odeSolution_kField hK
  have e : (fun t x => rightProj V (bgkField D ξ M ε t x)) =
      fun _ f => -rightProj V (transport D ξ f - ε⁻¹ • (M f - f)) := by
    funext t x
    rw [bgkField_eq, map_neg]
  rwa [e] at h

/-- **Eq. (20)** (arXiv 1804.04561), on the grid: the S-step gives
`∂ₜ f = P_V P_X (v · ∇ₓ f - ε⁻¹ C (f))` for `f = X S Vᵀ`, with `X`, `V` constant. -/
theorem eq20 {S : ℝ → Matrix r r ℝ} {t₀ t₁ : ℝ}
    (hS : ODESolution (MatrixKSL.sField X V (bgkField D ξ M ε)) S t₀ t₁) :
    ODESolution (fun _ f => leftProj X (rightProj V (transport D ξ f - ε⁻¹ • (M f - f))))
      (fun t => X * S t * Vᵀ) t₀ t₁ := by
  have h := MatrixKSL.odeSolution_sField hS
  have e : (fun t x => -leftProj X (rightProj V (bgkField D ξ M ε t x))) =
      fun _ f => leftProj X (rightProj V (transport D ξ f - ε⁻¹ • (M f - f))) := by
    funext t x
    rw [bgkField_eq, map_neg, map_neg, neg_neg]
  rwa [e] at h

/-- **Eq. (21)** (arXiv 1804.04561), on the grid: the L-step gives
`∂ₜ f = -P_X (v · ∇ₓ f - ε⁻¹ C (f))` for `f = X Lᵀ`, with `X` constant. -/
theorem eq21 {Lf : ℝ → Matrix n r ℝ} {t₀ t₁ : ℝ}
    (hL : ODESolution (MatrixKSL.lField X (bgkField D ξ M ε)) Lf t₀ t₁) :
    ODESolution (fun _ f => -leftProj X (transport D ξ f - ε⁻¹ • (M f - f)))
      (fun t => X * (Lf t)ᵀ) t₀ t₁ := by
  have h := MatrixKSL.odeSolution_lField hL
  have e : (fun t x => leftProj X (bgkField D ξ M ε t x)) =
      fun _ f => -leftProj X (transport D ξ f - ε⁻¹ • (M f - f)) := by
    funext t x
    rw [bgkField_eq, map_neg]
  rwa [e] at h

/-- **Eq. (23), corrected, and Eq. (26)** (arXiv 1804.04561), on the grid:
`K̇ = -∑ₐ Dₐ K c¹ₐ + ε⁻¹ (M (K Vᵀ) V - K)`.  In the paper's notation
`∂ₜ K_j = -∑_l c¹_{jl} · ∇ₓ K_l - ε⁻¹ (K_j - c³_j (K) ρ (K))`, which is Eq. (26).  Eq. (23) is
printed with the opposite sign of the collision term, see `eq23_printed_iff`. -/
theorem eq23 (hV : Vᵀ * V = 1) (t : ℝ) (K : Matrix m r ℝ) :
    MatrixKSL.kField V (bgkField D ξ M ε) t K =
      -∑ a, D a * K * cOne ξ V a + ε⁻¹ • (M (K * Vᵀ) * V - K) := by
  have e1 : K * Vᵀ * V = K := by rw [Matrix.mul_assoc, hV, Matrix.mul_one]
  have e2 : ∀ a, D a * (K * Vᵀ) * (Matrix.diagonal fun j => ξ j a) * V = D a * K * cOne ξ V a :=
    fun a => by simp only [cOne, Matrix.mul_assoc]
  simp only [MatrixKSL.kField, bgkField, transport_apply, Matrix.add_mul, Matrix.neg_mul,
    Matrix.sum_mul, Matrix.smul_mul, Matrix.sub_mul, e1, e2]

/-- **Eq. (24)** (arXiv 1804.04561), on the grid (`sField` contains the minus sign of the backward
step): `Ṡ = ∑ₐ d¹ₐ S c¹ₐ + ε⁻¹ (S - Xᵀ M (X S Vᵀ) V)`.  This is the equation as printed, with
`e_{ij} (S) = (Xᵀ M (X S Vᵀ) V)_{ij}`. -/
theorem eq24 (hX : Xᵀ * X = 1) (hV : Vᵀ * V = 1) (t : ℝ) (S : Matrix r r ℝ) :
    MatrixKSL.sField X V (bgkField D ξ M ε) t S =
      ∑ a, dOne D X a * S * cOne ξ V a + ε⁻¹ • (S - Xᵀ * M (X * S * Vᵀ) * V) := by
  have e1 : Xᵀ * (X * S * Vᵀ) * V = S := by
    calc Xᵀ * (X * S * Vᵀ) * V = (Xᵀ * X) * S * (Vᵀ * V) := by simp only [Matrix.mul_assoc]
      _ = S := by rw [hX, hV, Matrix.one_mul, Matrix.mul_one]
  have e2 : ∀ a, Xᵀ * (D a * (X * S * Vᵀ) * Matrix.diagonal fun j => ξ j a) * V =
      dOne D X a * S * cOne ξ V a := fun a => by
    simp only [dOne, cOne, Matrix.mul_assoc]
  simp only [MatrixKSL.sField, bgkField, transport_apply, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, e1, e2]
  rw [neg_add, neg_neg, ← smul_neg, neg_sub]

/-- **Eq. (25), corrected** (arXiv 1804.04561), on the grid:
`L̇ = -∑ₐ diag (ξ · a) L (d¹ₐ)ᵀ + ε⁻¹ (M (X Lᵀ)ᵀ X - L)`, that is
`∂ₜ L_i = -∑_l (d¹_{il} · v) L_l - ε⁻¹ (L_i - d³_i (L))`.  The paper prints this right-hand side
for `-∂ₜ L_i`, see `eq25_printed_iff`. -/
theorem eq25 (hX : Xᵀ * X = 1) (t : ℝ) (Lf : Matrix n r ℝ) :
    MatrixKSL.lField X (bgkField D ξ M ε) t Lf =
      -∑ a, (Matrix.diagonal fun j => ξ j a) * Lf * (dOne D X a)ᵀ +
        ε⁻¹ • ((M (X * Lfᵀ))ᵀ * X - Lf) := by
  have e1 : (X * Lfᵀ)ᵀ * X = Lf := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, hX, Matrix.mul_one]
  have e2 : ∀ a, (D a * (X * Lfᵀ) * Matrix.diagonal fun j => ξ j a)ᵀ * X =
      (Matrix.diagonal fun j => ξ j a) * Lf * (dOne D X a)ᵀ := fun a => by
    simp only [dOne, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
      Matrix.mul_assoc]
  simp only [MatrixKSL.lField, bgkField, transport_apply, Matrix.transpose_add,
    Matrix.transpose_neg, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.transpose_sub,
    Matrix.add_mul, Matrix.neg_mul, Matrix.sum_mul, Matrix.smul_mul, Matrix.sub_mul, e1, e2]

private lemma eq_zero_of_add_eq_sub {W : Type*} [AddCommGroup W] [Module ℝ W] {S x : W}
    (h : S + x = S - x) : x = 0 := by
  have h1 : x + x = 0 := by
    have h2 := sub_eq_zero.2 h
    have h3 : S + x - (S - x) = x + x := by abel
    rwa [h3] at h2
  have h2 : (2 : ℝ) • x = 0 := by rwa [two_smul]
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/-- **Eq. (23) as printed is wrong** (arXiv 1804.04561, Eq. (23)).  The paper prints
`-K̇_j = ∑_l c¹_{jl} · ∇ₓ K_l - ε⁻¹ (K_j - c³_j ρ)`, which has the opposite sign of the collision
term compared with `eq23` and with the paper's own Eq. (26).  It holds if and only if `K` already
satisfies the constraint `K = M (K Vᵀ) V`. -/
theorem eq23_printed_iff (hV : Vᵀ * V = 1) (hε : ε ≠ 0) (t : ℝ) (K : Matrix m r ℝ) :
    -MatrixKSL.kField V (bgkField D ξ M ε) t K =
        ∑ a, D a * K * cOne ξ V a - ε⁻¹ • (K - M (K * Vᵀ) * V) ↔ K = M (K * Vᵀ) * V := by
  rw [eq23 hV, neg_add, neg_neg, ← smul_neg, neg_sub]
  constructor
  · intro h
    have h2 := eq_zero_of_add_eq_sub h
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left (inv_ne_zero hε))
  · intro h
    rw [← h]
    simp

/-- **Eq. (25) as printed is wrong** (arXiv 1804.04561, Eq. (25)).  The paper prints
`-L̇_i = -∑_l (d¹_{il} · v) L_l - ε⁻¹ (L_i - d³_i)`.  The right-hand side is `+L̇_i` (`eq25`), so
the printed equation holds if and only if `L̇ = 0`. -/
theorem eq25_printed_iff (hX : Xᵀ * X = 1) (t : ℝ) (Lf : Matrix n r ℝ) :
    -MatrixKSL.lField X (bgkField D ξ M ε) t Lf =
        -∑ a, (Matrix.diagonal fun j => ξ j a) * Lf * (dOne D X a)ᵀ -
          ε⁻¹ • (Lf - (M (X * Lfᵀ))ᵀ * X) ↔
      MatrixKSL.lField X (bgkField D ξ M ε) t Lf = 0 := by
  have e : -∑ a, (Matrix.diagonal fun j => ξ j a) * Lf * (dOne D X a)ᵀ -
      ε⁻¹ • (Lf - (M (X * Lfᵀ))ᵀ * X) = MatrixKSL.lField X (bgkField D ξ M ε) t Lf := by
    rw [eq25 hX, sub_eq_add_neg, ← smul_neg, neg_sub]
  rw [e]
  constructor
  · intro h
    have h1 : (2 : ℝ) • MatrixKSL.lField X (bgkField D ξ M ε) t Lf = 0 := by
      rw [two_smul]
      nth_rw 1 [← h]
      simp
    exact (smul_eq_zero.1 h1).resolve_left two_ne_zero
  · intro h
    rw [h]
    simp

/-- The Lipschitz constant of the BGK field for fixed `ε`, of size `1/ε`.  The robust analysis of
`LeanDLRA.Integrators.ProjectorSplitting` also asks for a global bound of the field, so it applies
to `bgkField` only after a truncation outside a ball, and its constant `e^{L T}` is then of size
`e^{T/ε}`: it says nothing uniform as `ε → 0`.
(arXiv 1804.04561, Eqs. (17)-(25).) -/
theorem bgkField_isLipschitzField {LM : ℝ} (hM : ∀ f g, ‖M f - M g‖ ≤ LM * ‖f - g‖) (hε : 0 < ε) :
    IsLipschitzField (bgkField D ξ M ε) (‖transport D ξ‖ + ε⁻¹ * (LM + 1)) := fun t f g => by
  have e : bgkField D ξ M ε t f - bgkField D ξ M ε t g =
      -transport D ξ (f - g) + ε⁻¹ • ((M f - M g) - (f - g)) := by
    simp only [bgkField, map_sub, smul_sub]
    abel
  rw [e]
  have h1 : ‖transport D ξ (f - g)‖ ≤ ‖transport D ξ‖ * ‖f - g‖ := (transport D ξ).le_opNorm _
  have h2 : ‖ε⁻¹ • ((M f - M g) - (f - g))‖ ≤ ε⁻¹ * ((LM + 1) * ‖f - g‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hε).le
    have := norm_sub_le (M f - M g) (f - g)
    have := hM f g
    linarith
  calc _ ≤ ‖-transport D ξ (f - g)‖ + ‖ε⁻¹ • ((M f - M g) - (f - g))‖ := norm_add_le _ _
    _ ≤ _ := by rw [norm_neg]; nlinarith

/-! #### The discrete Maxwellian

The discrete density `ρ (f)_i = ∑_j w_j f_{ij}`, the velocity quadrature with weights `w`, is
the core `Kinetic.density w f`. -/

/-- The discrete momentum `(ρ u) (f) = ∑_j w_j f_{ij} ξ_j`. -/
noncomputable def momentum (w : n → ℝ) (ξ : n → Vel d) (f : Matrix m n ℝ) (i : m) : Vel d :=
  ∑ j, (w j * f i j) • ξ j

/-- The bulk velocity `u (f) = (ρ u) (f) / ρ (f)`. -/
noncomputable def bulk (w : n → ℝ) (ξ : n → Vel d) (f : Matrix m n ℝ) (i : m) : Vel d :=
  (density w f i)⁻¹ • momentum w ξ f i

/-- `h^eq (f)`, with `f^eq = ρ h^eq`: `h^eq_{ij} = (2π)^{-d/2} exp (-(ξ_j - u_i)² / 2)`. -/
noncomputable def heq (w : n → ℝ) (ξ : n → Vel d) (f : Matrix m n ℝ) : Matrix m n ℝ :=
  Matrix.of fun i j => gaussConst d * Real.exp (-‖ξ j - bulk w ξ f i‖ ^ 2 / 2)

/-- The Maxwellian `f^eq (f)` of Section 3 at the grid points. -/
noncomputable def discreteMaxwellian (w : n → ℝ) (ξ : n → Vel d) (f : Matrix m n ℝ) :
    Matrix m n ℝ :=
  Matrix.of fun i j => maxwellian (density w f i) (bulk w ξ f i) (ξ j)

/-- `M (f) V = ρ (f) c³`, with `c³_j (f) = ∑_l h^eq_l V_{lj}`: the collision term of Eq. (23).
(arXiv 1804.04561, Eq. (23).) -/
theorem discreteMaxwellian_mul (w : n → ℝ) (ξ : n → Vel d) (f : Matrix m n ℝ) (V : Matrix n r ℝ)
    (i : m) (j : r) :
    (discreteMaxwellian w ξ f * V) i j = density w f i * (heq w ξ f * V) i j := by
  simp only [Matrix.mul_apply, discreteMaxwellian, heq, Matrix.of_apply, maxwellian,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

omit [DecidableEq n] in
/-- Continuity of the discrete Maxwellian wherever the density does not vanish.
(arXiv 1804.04561, Section 4.) -/
theorem continuousAt_discreteMaxwellian (w : n → ℝ) (ξ : n → Vel d)
    {f : Matrix m n ℝ} (hρ : ∀ i, density w f i ≠ 0) :
    ContinuousAt (discreteMaxwellian w ξ) f := by
  have hco : ∀ i j, Continuous fun g : Matrix m n ℝ => g i j := fun i j =>
    (continuous_apply j).comp (continuous_apply i)
  have hden : ∀ i, Continuous fun g : Matrix m n ℝ => density w g i := fun i => by
    simp only [Kinetic.density_apply]
    exact continuous_finsetSum _ fun j _ => continuous_const.mul (hco i j)
  have hmom : ∀ i, Continuous fun g : Matrix m n ℝ => momentum w ξ g i := fun i =>
    continuous_finsetSum _ fun j _ => (continuous_const.mul (hco i j)).smul continuous_const
  have hbulk : ∀ i, ContinuousAt (fun g : Matrix m n ℝ => bulk w ξ g i) f := fun i =>
    ((hden i).continuousAt.inv₀ (hρ i)).smul (hmom i).continuousAt
  refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ?_
  simp only [discreteMaxwellian, Matrix.of_apply, maxwellian]
  refine ((hden i).continuousAt.mul continuousAt_const).mul
    (Real.continuous_exp.continuousAt.comp ?_)
  exact (((continuousAt_const.sub (hbulk i)).norm.pow 2).neg).div_const 2

/-! #### Section 4 on the grid: the moment structure -/

variable {Φ : Matrix n q ℝ} {cl : Matrix m q ℝ → Matrix m n ℝ}
  {cl' : Matrix m q ℝ → Matrix m q ℝ →L[ℝ] Matrix m n ℝ} {U : Set (Matrix m q ℝ)} {τ L c₀ : ℝ}

/-- The K-step conserves moments if the moment test functions lie in the range of `V`. -/
lemma cons_of_moments_mem (hΦ : V * Vᵀ * Φ = Φ) (hcl : ∀ μ ∈ U, cl μ * Φ = μ) :
    ∀ μ ∈ U, cl μ * V * Vᵀ * Φ = μ := fun μ hμ => by
  have e : cl μ * V * Vᵀ * Φ = cl μ * (V * Vᵀ * Φ) := by simp only [Matrix.mul_assoc]
  rw [e, hΦ, hcl μ hμ]

/-- The K-step conserves moments if `V` represents the Maxwellian exactly. -/
lemma cons_of_exact (hex : ∀ μ ∈ U, cl μ * V * Vᵀ = cl μ) (hcl : ∀ μ ∈ U, cl μ * Φ = μ) :
    ∀ μ ∈ U, cl μ * V * Vᵀ * Φ = μ := fun μ hμ => by
  rw [hex μ hμ, hcl μ hμ]

private lemma relaxField_right (t : ℝ) (f : Matrix m n ℝ) :
    rightProj V (bgkField D ξ (fun f => cl (f * Φ)) ε t f) =
      relaxField 1 (rightProj V) (-transport D ξ) (Frobenius.rightMulCLM Φ) cl ε t f := by
  simp [relaxField, bgkField]

private lemma relaxField_left (t : ℝ) (f : Matrix m n ℝ) :
    leftProj X (bgkField D ξ (fun f => cl (f * Φ)) ε t f) =
      relaxField 1 (leftProj X) (-transport D ξ) (Frobenius.rightMulCLM Φ) cl ε t f := by
  simp [relaxField, bgkField]

/-- The K-step is a relaxing substep.
(arXiv 1804.04561, Eqs. (19), (23).) -/
theorem kStep_isRelaxSol (hV : Vᵀ * V = 1) (hcl : ∀ μ ∈ U, cl μ * V * Vᵀ * Φ = μ)
    {K : ℝ → Matrix m r ℝ}
    (hK : ODESolution (MatrixKSL.kField V (bgkField D ξ (fun f => cl (f * Φ)) ε)) K 0 τ)
    (hU : ∀ t ∈ Icc (0 : ℝ) τ, K t * Vᵀ * Φ ∈ U) :
    IsRelaxSol 1 (rightProj V) (-transport D ξ) (Frobenius.rightMulCLM Φ) cl U ε τ
      (fun t => K t * Vᵀ) where
  ode := by
    have h := MatrixKSL.odeSolution_kField hK
    have e : (fun t x => rightProj V (bgkField D ξ (fun f => cl (f * Φ)) ε t x)) =
        relaxField 1 (rightProj V) (-transport D ξ) (Frobenius.rightMulCLM Φ) cl ε := by
      funext t x
      exact relaxField_right t x
    rwa [e] at h
  start := rightProj_mul_transpose hV _
  mem := hU
  cons t ht := by
    simpa [Matrix.mul_assoc] using hcl _ (hU t ht)

/-- The L-step is a relaxing substep, for every `X`: the moments of `f = X Lᵀ` lie in the range of
`X`, so `P_X` does not change the moments of the Maxwellian.
(arXiv 1804.04561, Eqs. (21), (25).) -/
theorem lStep_isRelaxSol (hX : Xᵀ * X = 1) (hcl : ∀ μ ∈ U, cl μ * Φ = μ)
    {Lf : ℝ → Matrix n r ℝ}
    (hL : ODESolution (MatrixKSL.lField X (bgkField D ξ (fun f => cl (f * Φ)) ε)) Lf 0 τ)
    (hU : ∀ t ∈ Icc (0 : ℝ) τ, X * (Lf t)ᵀ * Φ ∈ U) :
    IsRelaxSol 1 (leftProj X) (-transport D ξ) (Frobenius.rightMulCLM Φ) cl U ε τ
      (fun t => X * (Lf t)ᵀ) where
  ode := by
    have h := MatrixKSL.odeSolution_lField hL
    have e : (fun t x => leftProj X (bgkField D ξ (fun f => cl (f * Φ)) ε t x)) =
        relaxField 1 (leftProj X) (-transport D ξ) (Frobenius.rightMulCLM Φ) cl ε := by
      funext t x
      exact relaxField_left t x
    rwa [e] at h
  start := leftProj_mul_left hX _
  mem := hU
  cons t ht := by
    have h1 := hcl _ (hU t ht)
    simp only [Frobenius.rightMulCLM_apply, leftProj_apply]
    rw [Matrix.mul_assoc (X * Xᵀ), h1]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Xᵀ X, hX, Matrix.one_mul]

/-- The S-step is a relaxing substep with the wrong sign, `σ = -1`.
(arXiv 1804.04561, Eqs. (20), (24).) -/
theorem sStep_isRelaxSol (hX : Xᵀ * X = 1) (hV : Vᵀ * V = 1)
    (hcl : ∀ μ ∈ U, cl μ * V * Vᵀ * Φ = μ) {S : ℝ → Matrix r r ℝ}
    (hS : ODESolution (MatrixKSL.sField X V (bgkField D ξ (fun f => cl (f * Φ)) ε)) S 0 τ)
    (hU : ∀ t ∈ Icc (0 : ℝ) τ, X * S t * Vᵀ * Φ ∈ U) :
    IsRelaxSol (-1) (leftProj X * rightProj V) (-transport D ξ) (Frobenius.rightMulCLM Φ) cl U ε τ
      (fun t => X * S t * Vᵀ) where
  ode := by
    have h := MatrixKSL.odeSolution_sField hS
    have e : (fun t x => -leftProj X (rightProj V (bgkField D ξ (fun f => cl (f * Φ)) ε t x))) =
        relaxField (-1) (leftProj X * rightProj V) (-transport D ξ) (Frobenius.rightMulCLM Φ)
          cl ε := by
      funext t x
      simp [relaxField, bgkField]
    rwa [e] at h
  start := by
    simp only [mul_apply_eq_comp]
    rw [rightProj_mul_transpose hV, Matrix.mul_assoc, leftProj_mul_left hX]
  mem := hU
  cons t ht := by
    have h1 := hcl _ (hU t ht)
    simp only [Frobenius.rightMulCLM_apply, mul_apply_eq_comp, leftProj_apply,
      rightProj_apply]
    calc X * Xᵀ * (cl (X * S t * Vᵀ * Φ) * V * Vᵀ) * Φ
        = X * Xᵀ * (cl (X * S t * Vᵀ * Φ) * V * Vᵀ * Φ) := by simp only [Matrix.mul_assoc]
      _ = X * Xᵀ * (X * S t * Vᵀ * Φ) := by rw [h1]
      _ = X * S t * Vᵀ * Φ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Xᵀ X, hX, Matrix.one_mul]

private lemma relaxB_nonneg {a cm L c₀ τ z : ℝ} (ha : 0 ≤ a) (hcm : 0 ≤ cm) (hL : 0 ≤ L)
    (hc₀ : 0 ≤ c₀) (hz : 0 ≤ z) : 0 ≤ relaxB a cm L c₀ τ z := by
  have : 0 ≤ relaxZ a cm L c₀ τ z := mul_nonneg hz (Real.exp_pos _).le
  rw [relaxB]
  positivity

private lemma limitC_nonneg {a cm L c₀ τ z : ℝ} (ha : 0 ≤ a) (hcm : 0 ≤ cm) (hL : 0 ≤ L)
    (hc₀ : 0 ≤ c₀) (hz : 0 ≤ z) (hτ : 0 ≤ τ) : 0 ≤ limitC a cm L c₀ τ z := by
  have h1 : 0 ≤ relaxZ a cm L c₀ τ z := mul_nonneg hz (Real.exp_pos _).le
  have h2 := relaxB_nonneg (τ := τ) (z := z) ha hcm hL hc₀ hz
  simp only [limitC]
  positivity

/-- The constant of `kStep_singular_limit` and `lStep_singular_limit`. -/
noncomputable def stepC (a cm L c₀ τ z : ℝ) : ℝ :=
  relaxB a cm L c₀ τ z + L * limitC a cm L c₀ τ z + limitC a cm L c₀ τ z

/-- **Section 4, the K-step** (arXiv 1804.04561, Section 4: taking `ε → 0` in Eq. (23) gives "the
projection of the Maxwell–Boltzmann distribution onto the space spanned by the `V_j`"; the paper
argues formally).
On the grid, for a moment-based equilibrium `M f = ℳ (f Φ)` and a K-step that conserves the moments
(`hcl`, see `cons_of_moments_mem`, `cons_of_exact`; without this the statement is false,
`kStep_repels`), the constraint defect relaxes:
`‖M (K Vᵀ) V - K‖ ≤ e^{-t/ε} ‖M (K₀ Vᵀ) V - K₀‖ + C ε`, and `K` converges to
`K̄ = ℳ (m₀) V`, where `m₀` solves the closed moment system.  `C` does not depend on `ε`. -/
theorem kStep_singular_limit (hc : IsClosure cl cl' U L c₀) (hV : Vᵀ * V = 1)
    (hcl : ∀ μ ∈ U, cl μ * V * Vᵀ * Φ = μ) (K₀ : Matrix m r ℝ) {m₀ : ℝ → Matrix m q ℝ}
    (hm₀ : ODESolution (reducedField (rightProj V) (-transport D ξ) (Frobenius.rightMulCLM Φ) cl)
      m₀ 0 τ) (h0 : m₀ 0 = K₀ * Vᵀ * Φ) (hU₀ : ∀ t ∈ Icc (0 : ℝ) τ, m₀ t ∈ U) :
    ∃ C : ℝ, ∀ ε > 0, ∀ K : ℝ → Matrix m r ℝ,
      ODESolution (MatrixKSL.kField V (bgkField D ξ (fun f => cl (f * Φ)) ε)) K 0 τ →
      K 0 = K₀ → (∀ t ∈ Icc (0 : ℝ) τ, K t * Vᵀ * Φ ∈ U) → ∀ t ∈ Icc (0 : ℝ) τ,
        ‖cl (K t * Vᵀ * Φ) * V - K t‖ ≤
            Real.exp (-t / ε) * ‖cl (K₀ * Vᵀ * Φ) * V - K₀‖ + ε * C ∧
          ‖K t * Vᵀ * Φ - m₀ t‖ ≤ ε * C ∧
          ‖K t - cl (m₀ t) * V‖ ≤
            Real.exp (-t / ε) * ‖cl (K₀ * Vᵀ * Φ) * V - K₀‖ + ε * C := by
  have hP := isOrthProj_rightProj (m := m) hV
  have hdef : ∀ Y : Matrix m r ℝ, ‖defect (rightProj V) (Frobenius.rightMulCLM Φ) cl (Y * Vᵀ)‖ =
      ‖cl (Y * Vᵀ * Φ) * V - Y‖ := fun Y => by
    have e : defect (rightProj V) (Frobenius.rightMulCLM Φ) cl (Y * Vᵀ) =
        (cl (Y * Vᵀ * Φ) * V - Y) * Vᵀ := by
      simp only [defect, Frobenius.rightMulCLM_apply, rightProj_apply, Matrix.sub_mul]
    rw [e, Frobenius.norm_mul_transpose_of_orthonormal hV]
  set z := ‖cl (K₀ * Vᵀ * Φ) * V - K₀‖ ^ 2 + ‖K₀ * Vᵀ * Φ‖ ^ 2 + 1 with hz
  set a := ‖-transport D ξ‖ with ha
  set cm := ‖(Frobenius.rightMulCLM Φ : Matrix m n ℝ →L[ℝ] Matrix m q ℝ)‖ with hcm
  refine ⟨stepC a cm L c₀ τ z, fun ε hε K hK hK0 hU t ht => ?_⟩
  have hsol := kStep_isRelaxSol (D := D) (ξ := ξ) (ε := ε) hV hcl hK hU
  have hzz : ‖defect (rightProj V) (Frobenius.rightMulCLM Φ) cl (K 0 * Vᵀ)‖ ^ 2 +
      ‖Frobenius.rightMulCLM Φ (K 0 * Vᵀ)‖ ^ 2 + 1 ≤ z := by
    rw [hdef, hK0, Frobenius.rightMulCLM_apply]
  have hτ : 0 ≤ τ := ht.1.trans ht.2
  have hB0 : 0 ≤ relaxB a cm L c₀ τ z := relaxB_nonneg (norm_nonneg _) (norm_nonneg _)
    hc.L_nonneg hc.c₀_nonneg (by positivity)
  have hC0 : 0 ≤ limitC a cm L c₀ τ z := limitC_nonneg (norm_nonneg _) (norm_nonneg _)
    hc.L_nonneg hc.c₀_nonneg (by positivity) hτ
  have hL0 := hc.L_nonneg
  have hS1 : relaxB a cm L c₀ τ z ≤ stepC a cm L c₀ τ z := by
    rw [stepC]; nlinarith [mul_nonneg hL0 hC0]
  have hS2 : limitC a cm L c₀ τ z ≤ stepC a cm L c₀ τ z := by
    rw [stepC]; nlinarith [mul_nonneg hL0 hC0]
  have hS3 : relaxB a cm L c₀ τ z + L * limitC a cm L c₀ τ z ≤ stepC a cm L c₀ τ z := by
    rw [stepC]; linarith
  have h1 : ‖defect (rightProj V) (Frobenius.rightMulCLM Φ) cl (K t * Vᵀ)‖ ≤
      Real.exp (-t / ε) * ‖defect (rightProj V) (Frobenius.rightMulCLM Φ) cl (K 0 * Vᵀ)‖ +
        ε * relaxB a cm L c₀ τ z := hsol.defect_le hP hc hε hzz ht
  have h0' : m₀ 0 = Frobenius.rightMulCLM Φ (K 0 * Vᵀ) := by
    rw [Frobenius.rightMulCLM_apply, hK0, h0]
  have h2 : ‖Frobenius.rightMulCLM Φ (K t * Vᵀ) - m₀ t‖ ≤ ε * limitC a cm L c₀ τ z :=
    hsol.moment_limit hP hc hε hzz hm₀ h0' hU₀ ht
  have h3 : ‖K t * Vᵀ - rightProj V (cl (m₀ t))‖ ≤
      Real.exp (-t / ε) * ‖defect (rightProj V) (Frobenius.rightMulCLM Φ) cl (K 0 * Vᵀ)‖ +
        ε * (relaxB a cm L c₀ τ z + L * limitC a cm L c₀ τ z) :=
    hsol.singular_limit hP hc hε hzz hm₀ h0' hU₀ ht
  have e3 : K t * Vᵀ - rightProj V (cl (m₀ t)) = (K t - cl (m₀ t) * V) * Vᵀ := by
    simp only [rightProj_apply, Matrix.sub_mul]
  rw [e3, Frobenius.norm_mul_transpose_of_orthonormal hV, hdef, hK0] at h3
  rw [hdef, hdef, hK0] at h1
  rw [Frobenius.rightMulCLM_apply] at h2
  refine ⟨h1.trans ?_, h2.trans (mul_le_mul_of_nonneg_left hS2 hε.le), h3.trans ?_⟩
  · exact add_le_add_right (mul_le_mul_of_nonneg_left hS1 hε.le) _
  · exact add_le_add_right (mul_le_mul_of_nonneg_left hS3 hε.le) _

/-- The limit of the K-step satisfies the constraint of Section 4 of arXiv 1804.04561:
`K̄ = M (K̄ Vᵀ) V`, that is `K̄_j = ∫ V_j M (K̄) dv`, the projection of the Maxwellian onto the
span of the `V_j`. -/
theorem kStep_limit_constraint (hcl : ∀ μ ∈ U, cl μ * V * Vᵀ * Φ = μ) {μ : Matrix m q ℝ}
    (hμ : μ ∈ U) : cl (cl μ * V * Vᵀ * Φ) * V = cl μ * V := by
  rw [hcl μ hμ]

/-- **Section 4, the K-step, as a limit** (arXiv 1804.04561, Section 4).  For fixed data and every
`t > 0`, the K-step converges as `ε → 0⁺` to `K̄ (t) = ℳ (m₀ t) V`, which satisfies the constraint
by `kStep_limit_constraint`. -/
theorem kStep_tendsto (hc : IsClosure cl cl' U L c₀) (hV : Vᵀ * V = 1)
    (hcl : ∀ μ ∈ U, cl μ * V * Vᵀ * Φ = μ) {K₀ : Matrix m r ℝ} {K : ℝ → ℝ → Matrix m r ℝ}
    (hK : ∀ ε > 0, ODESolution (MatrixKSL.kField V (bgkField D ξ (fun f => cl (f * Φ)) ε))
      (K ε) 0 τ)
    (hK0 : ∀ ε > 0, K ε 0 = K₀) (hU : ∀ ε > 0, ∀ t ∈ Icc (0 : ℝ) τ, K ε t * Vᵀ * Φ ∈ U)
    {m₀ : ℝ → Matrix m q ℝ}
    (hm₀ : ODESolution (reducedField (rightProj V) (-transport D ξ) (Frobenius.rightMulCLM Φ) cl)
      m₀ 0 τ) (h0 : m₀ 0 = K₀ * Vᵀ * Φ) (hU₀ : ∀ t ∈ Icc (0 : ℝ) τ, m₀ t ∈ U) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) τ) :
    Tendsto (fun ε => K ε t) (𝓝[>] 0) (𝓝 (cl (m₀ t) * V)) := by
  have hP := isOrthProj_rightProj (m := m) hV
  have h := tendsto_singular_limit (f₀ := K₀ * Vᵀ) (f := fun ε t => K ε t * Vᵀ) hP hc
    (fun ε hε => kStep_isRelaxSol hV hcl (hK ε hε) (hU ε hε))
    (fun ε hε => by simp only [hK0 ε hε]) hm₀ (by rw [Frobenius.rightMulCLM_apply, h0]) hU₀ ht
  have h2 := (Frobenius.rightMulCLM V : Matrix m n ℝ →L[ℝ] Matrix m r ℝ).continuous.tendsto _
    |>.comp h
  have e1 : ∀ ε, (Frobenius.rightMulCLM V : Matrix m n ℝ →L[ℝ] Matrix m r ℝ) (K ε t * Vᵀ) =
      K ε t := fun ε => by
    rw [Frobenius.rightMulCLM_apply, Matrix.mul_assoc, hV, Matrix.mul_one]
  have e2 : (Frobenius.rightMulCLM V : Matrix m n ℝ →L[ℝ] Matrix m r ℝ)
      (rightProj V (cl (m₀ t))) = cl (m₀ t) * V := by
    rw [Frobenius.rightMulCLM_apply, rightProj_apply]
    simp only [Matrix.mul_assoc]
    rw [hV, Matrix.mul_one]
  rw [e2] at h2
  exact h2.congr fun ε => e1 ε

/-- **Section 4, the L-step** (arXiv 1804.04561, Section 4: "this takes the Maxwell–Boltzmann
distribution and projects it onto the space spanned by the `X_i`"; the paper argues formally).  On
the grid, for a moment-based equilibrium and every `X` (no assumption on the basis is needed here),
`‖M (X Lᵀ)ᵀ X - L‖ ≤ e^{-t/ε} ‖M (X L₀ᵀ)ᵀ X - L₀‖ + C ε`, and `L` converges to
`L̄ = ℳ (m₀)ᵀ X`.  `C` does not depend on `ε`. -/
theorem lStep_singular_limit (hc : IsClosure cl cl' U L c₀) (hX : Xᵀ * X = 1)
    (hcl : ∀ μ ∈ U, cl μ * Φ = μ) (L₀ : Matrix n r ℝ) {m₀ : ℝ → Matrix m q ℝ}
    (hm₀ : ODESolution (reducedField (leftProj X) (-transport D ξ) (Frobenius.rightMulCLM Φ) cl)
      m₀ 0 τ) (h0 : m₀ 0 = X * L₀ᵀ * Φ) (hU₀ : ∀ t ∈ Icc (0 : ℝ) τ, m₀ t ∈ U) :
    ∃ C : ℝ, ∀ ε > 0, ∀ Lf : ℝ → Matrix n r ℝ,
      ODESolution (MatrixKSL.lField X (bgkField D ξ (fun f => cl (f * Φ)) ε)) Lf 0 τ →
      Lf 0 = L₀ → (∀ t ∈ Icc (0 : ℝ) τ, X * (Lf t)ᵀ * Φ ∈ U) → ∀ t ∈ Icc (0 : ℝ) τ,
        ‖(cl (X * (Lf t)ᵀ * Φ))ᵀ * X - Lf t‖ ≤
            Real.exp (-t / ε) * ‖(cl (X * L₀ᵀ * Φ))ᵀ * X - L₀‖ + ε * C ∧
          ‖X * (Lf t)ᵀ * Φ - m₀ t‖ ≤ ε * C ∧
          ‖Lf t - (cl (m₀ t))ᵀ * X‖ ≤
            Real.exp (-t / ε) * ‖(cl (X * L₀ᵀ * Φ))ᵀ * X - L₀‖ + ε * C := by
  have hP := isOrthProj_leftProj (n := n) hX
  have hiso : ∀ A : Matrix n r ℝ, ‖X * Aᵀ‖ = ‖A‖ := fun A => by
    rw [Frobenius.norm_mul_of_orthonormal hX, Frobenius.norm_transpose]
  have hdef : ∀ Y : Matrix n r ℝ, ‖defect (leftProj X) (Frobenius.rightMulCLM Φ) cl (X * Yᵀ)‖ =
      ‖(cl (X * Yᵀ * Φ))ᵀ * X - Y‖ := fun Y => by
    have e : defect (leftProj X) (Frobenius.rightMulCLM Φ) cl (X * Yᵀ) =
        X * ((cl (X * Yᵀ * Φ))ᵀ * X - Y)ᵀ := by
      simp only [defect, Frobenius.rightMulCLM_apply, leftProj_apply, Matrix.transpose_sub,
        Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_sub, Matrix.mul_assoc]
    rw [e, hiso]
  set z := ‖(cl (X * L₀ᵀ * Φ))ᵀ * X - L₀‖ ^ 2 + ‖X * L₀ᵀ * Φ‖ ^ 2 + 1 with hz
  set a := ‖-transport D ξ‖ with ha
  set cm := ‖(Frobenius.rightMulCLM Φ : Matrix m n ℝ →L[ℝ] Matrix m q ℝ)‖ with hcm
  refine ⟨stepC a cm L c₀ τ z, fun ε hε Lf hL hL0 hU t ht => ?_⟩
  have hsol := lStep_isRelaxSol (D := D) (ξ := ξ) (ε := ε) hX hcl hL hU
  have hzz : ‖defect (leftProj X) (Frobenius.rightMulCLM Φ) cl (X * (Lf 0)ᵀ)‖ ^ 2 +
      ‖Frobenius.rightMulCLM Φ (X * (Lf 0)ᵀ)‖ ^ 2 + 1 ≤ z := by
    rw [hdef, hL0, Frobenius.rightMulCLM_apply]
  have hτ : 0 ≤ τ := ht.1.trans ht.2
  have hB0 : 0 ≤ relaxB a cm L c₀ τ z := relaxB_nonneg (norm_nonneg _) (norm_nonneg _)
    hc.L_nonneg hc.c₀_nonneg (by positivity)
  have hC0 : 0 ≤ limitC a cm L c₀ τ z := limitC_nonneg (norm_nonneg _) (norm_nonneg _)
    hc.L_nonneg hc.c₀_nonneg (by positivity) hτ
  have hL0' := hc.L_nonneg
  have hS1 : relaxB a cm L c₀ τ z ≤ stepC a cm L c₀ τ z := by
    rw [stepC]; nlinarith [mul_nonneg hL0' hC0]
  have hS2 : limitC a cm L c₀ τ z ≤ stepC a cm L c₀ τ z := by
    rw [stepC]; nlinarith [mul_nonneg hL0' hC0]
  have hS3 : relaxB a cm L c₀ τ z + L * limitC a cm L c₀ τ z ≤ stepC a cm L c₀ τ z := by
    rw [stepC]; linarith
  have h1 : ‖defect (leftProj X) (Frobenius.rightMulCLM Φ) cl (X * (Lf t)ᵀ)‖ ≤
      Real.exp (-t / ε) * ‖defect (leftProj X) (Frobenius.rightMulCLM Φ) cl (X * (Lf 0)ᵀ)‖ +
        ε * relaxB a cm L c₀ τ z := hsol.defect_le hP hc hε hzz ht
  have h0' : m₀ 0 = Frobenius.rightMulCLM Φ (X * (Lf 0)ᵀ) := by
    rw [Frobenius.rightMulCLM_apply, hL0, h0]
  have h2 : ‖Frobenius.rightMulCLM Φ (X * (Lf t)ᵀ) - m₀ t‖ ≤ ε * limitC a cm L c₀ τ z :=
    hsol.moment_limit hP hc hε hzz hm₀ h0' hU₀ ht
  have h3 : ‖X * (Lf t)ᵀ - leftProj X (cl (m₀ t))‖ ≤
      Real.exp (-t / ε) * ‖defect (leftProj X) (Frobenius.rightMulCLM Φ) cl (X * (Lf 0)ᵀ)‖ +
        ε * (relaxB a cm L c₀ τ z + L * limitC a cm L c₀ τ z) :=
    hsol.singular_limit hP hc hε hzz hm₀ h0' hU₀ ht
  have e3 : X * (Lf t)ᵀ - leftProj X (cl (m₀ t)) = X * (Lf t - (cl (m₀ t))ᵀ * X)ᵀ := by
    simp only [leftProj_apply, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_sub, Matrix.mul_assoc]
  rw [e3, hiso, hdef, hL0] at h3
  rw [hdef, hdef, hL0] at h1
  rw [Frobenius.rightMulCLM_apply] at h2
  refine ⟨h1.trans ?_, h2.trans (mul_le_mul_of_nonneg_left hS2 hε.le), h3.trans ?_⟩
  · exact add_le_add_right (mul_le_mul_of_nonneg_left hS1 hε.le) _
  · exact add_le_add_right (mul_le_mul_of_nonneg_left hS3 hε.le) _

/-- The closed moment system of the L-step keeps the moments in the range of `X`.  Hence
`mom (X Xᵀ ℳ(m₀)) = m₀` if `ℳ` preserves moments, and the limit `L̄ = ℳ (m₀)ᵀ X` satisfies the
constraint `L̄ = M (X L̄ᵀ)ᵀ X` (`lStep_limit_constraint`).
(arXiv 1804.04561, Section 4.) -/
theorem reduced_mem_range_left (hX : Xᵀ * X = 1) {m₀ : ℝ → Matrix m q ℝ}
    (hm₀ : ODESolution (reducedField (leftProj X) (-transport D ξ) (Frobenius.rightMulCLM Φ) cl)
      m₀ 0 τ) (h0 : leftProj X (m₀ 0) = m₀ 0) : ∀ t ∈ Icc (0 : ℝ) τ, leftProj X (m₀ t) = m₀ t := by
  refine range_invariant_of_deriv_mem_range (isOrthProj_leftProj hX) hm₀.cont
    (G := fun t => -transport D ξ (leftProj X (cl (m₀ t))) * Φ) (fun t ht => ?_) h0
  have h := hm₀.deriv t ht
  have e : reducedField (leftProj X) (-transport D ξ) (Frobenius.rightMulCLM Φ) cl t (m₀ t) =
      leftProj X (-transport D ξ (leftProj X (cl (m₀ t))) * Φ) := by
    simp only [reducedField, Frobenius.rightMulCLM_apply, leftProj_apply,
      neg_apply, Matrix.mul_assoc]
  rwa [e] at h

/-- The limit of the L-step satisfies the constraint of Section 4 of arXiv 1804.04561: for
`L̄ = ℳ (μ)ᵀ X` with `μ` in the range of `X` (`reduced_mem_range_left`),
`L̄ = M (X L̄ᵀ)ᵀ X`, that is `L̄_i = ∫ X_i M (L̄) dx`. -/
theorem lStep_limit_constraint (hcl : ∀ μ ∈ U, cl μ * Φ = μ)
    {μ : Matrix m q ℝ} (hμ : μ ∈ U) (hμX : leftProj X μ = μ) :
    (cl (X * ((cl μ)ᵀ * X)ᵀ * Φ))ᵀ * X = (cl μ)ᵀ * X := by
  have e : X * ((cl μ)ᵀ * X)ᵀ * Φ = leftProj X (cl μ * Φ) := by
    simp only [leftProj_apply, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e, hcl μ hμ, hμX]

/-- **The S-step does not enforce the constraint**, in the notation of Eq. (24) (compare
arXiv 1804.04561, Section 4: "we obtain a very similar result for the evolution equations for
`S_{ij}`").  Fix a moment-based equilibrium, orthonormal `X`, `V`, an `S₀` with
`S₀ ≠ Xᵀ M (X S₀ Vᵀ) V`, and any bound `B`.  For all sufficiently small `ε` every solution of the
S-step from `S₀` on `[0, τ]` exceeds `B`.  Only the formal statement `sStep_formal_constraint`
holds: the constraint is a repelling set of the S-step, because that step runs backward. -/
theorem sStep_diverges (hc : IsClosure cl cl' U L c₀) (hX : Xᵀ * X = 1) (hV : Vᵀ * V = 1)
    (hcl : ∀ μ ∈ U, cl μ * V * Vᵀ * Φ = μ) {S₀ : Matrix r r ℝ}
    (hS₀ : S₀ ≠ Xᵀ * cl (X * S₀ * Vᵀ * Φ) * V) (hτ : 0 < τ) (B : ℝ) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ S : ℝ → Matrix r r ℝ,
      ODESolution (MatrixKSL.sField X V (bgkField D ξ (fun f => cl (f * Φ)) ε)) S 0 τ →
      S 0 = S₀ → (∀ t ∈ Icc (0 : ℝ) τ, X * S t * Vᵀ * Φ ∈ U) →
      ∃ s ∈ Icc (0 : ℝ) τ, B < ‖S s‖ := by
  have hP := isOrthProj_leftProj_mul_rightProj (m := m) (n := n) hX hV
  have hiso : ∀ A : Matrix r r ℝ, ‖X * A * Vᵀ‖ = ‖A‖ := fun A => by
    rw [Frobenius.norm_mul_transpose_of_orthonormal hV, Frobenius.norm_mul_of_orthonormal hX]
  have hdef : defect (leftProj X * rightProj V) (Frobenius.rightMulCLM Φ) cl (X * S₀ * Vᵀ) ≠
      0 := by
    intro h0
    have e : defect (leftProj X * rightProj V) (Frobenius.rightMulCLM Φ) cl (X * S₀ * Vᵀ) =
        X * (Xᵀ * cl (X * S₀ * Vᵀ * Φ) * V - S₀) * Vᵀ := by
      simp only [defect, Frobenius.rightMulCLM_apply, mul_apply_eq_comp,
        leftProj_apply, rightProj_apply, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [e] at h0
    have h1 : ‖Xᵀ * cl (X * S₀ * Vᵀ * Φ) * V - S₀‖ = 0 := by rw [← hiso, h0, norm_zero]
    exact hS₀ (sub_eq_zero.1 (norm_eq_zero.1 h1)).symm
  obtain ⟨ε₀, hε₀, H⟩ := sStep_unbounded (A := -transport D ξ) hP hc hdef hτ B
  refine ⟨ε₀, hε₀, fun ε hε S hS hS0 hU => ?_⟩
  obtain ⟨s, hs, hlt⟩ := H ε hε _ (sStep_isRelaxSol hX hV hcl hS hU) (by simp only [hS0])
  exact ⟨s, hs, by rwa [hiso] at hlt⟩

/-- **The S-step undoes the relaxation of the K-step.**  Without transport (`T = 0`), for every
`ε > 0` and every step of the scheme, the constraint defect of the S-step at its final time is
`Xᵀ` times the defect of the *initial* data of the K-step:
`X¹ᵀ M (f) V⁰ - S (τ) = X¹ᵀ (M (f⁰) V⁰ - K⁰)`.  It does not tend to `0` with `ε`, although the
K-step has reduced its defect by `e^{-τ/ε}` (`pure_relaxation`).
(arXiv 1804.04561, Section 4, on Eq. (24).) -/
theorem sStep_undoes_kStep (hT : transport D ξ = 0) {U₀ U₁ : Matrix m r ℝ}
    {S₀ Ŝ₁ : Matrix r r ℝ} {V₀ : Matrix n r ℝ} {K : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ}
    {Lf : ℝ → Matrix n r ℝ}
    (hs : MatrixKSL.IsStep (bgkField D ξ (fun f => cl (f * Φ)) ε) 0 τ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf)
    (hτ : 0 ≤ τ) (hcl : ∀ μ ∈ U, cl μ * V₀ * V₀ᵀ * Φ = μ)
    (hUK : ∀ t ∈ Icc (0 : ℝ) τ, K t * V₀ᵀ * Φ ∈ U)
    (hUS : ∀ t ∈ Icc (0 : ℝ) τ, U₁ * S t * V₀ᵀ * Φ ∈ U) :
    U₁ᵀ * cl (U₁ * S τ * V₀ᵀ * Φ) * V₀ - S τ =
      U₁ᵀ * (cl (U₀ * S₀ * V₀ᵀ * Φ) * V₀ - U₀ * S₀) := by
  have hA : -transport D ξ = 0 := by rw [hT, neg_zero]
  have hV₀ := hs.orthV₀
  have hU₁ := hs.orthU₁
  have hK := kStep_isRelaxSol (D := D) (ξ := ξ) (ε := ε) hV₀ hcl hs.kSol hUK
  have hS := sStep_isRelaxSol (D := D) (ξ := ξ) (ε := ε) hU₁ hV₀ hcl hs.sSol hUS
  rw [hA] at hK hS
  have hτm : τ ∈ Icc (0 : ℝ) τ := ⟨hτ, le_rfl⟩
  obtain ⟨pK1, pK2⟩ := pure_relaxation hK (isOrthProj_rightProj hV₀) hτm
  obtain ⟨pS1, pS2⟩ := pure_relaxation hS (isOrthProj_leftProj_mul_rightProj hU₁ hV₀) hτm
  have hS0 : U₁ * S 0 * V₀ᵀ = K τ * V₀ᵀ := by rw [hs.sStart, hs.kQR]
  simp only [Frobenius.rightMulCLM_apply] at pK1 pS1
  set mm := U₀ * S₀ * V₀ᵀ * Φ with hmm
  have pK1' : K τ * V₀ᵀ * Φ = mm := by rw [pK1, hs.kStart]
  have pS1' : U₁ * S τ * V₀ᵀ * Φ = mm := by rw [pS1, hS0, pK1']
  have dK0 : defect (rightProj V₀) (Frobenius.rightMulCLM Φ) cl (K 0 * V₀ᵀ) =
      (cl mm * V₀ - U₀ * S₀) * V₀ᵀ := by
    simp only [defect, Frobenius.rightMulCLM_apply, rightProj_apply, Matrix.sub_mul, hs.kStart,
      hmm]
  have dKt : defect (rightProj V₀) (Frobenius.rightMulCLM Φ) cl (K τ * V₀ᵀ) =
      (cl mm * V₀ - K τ) * V₀ᵀ := by
    simp only [defect, Frobenius.rightMulCLM_apply, rightProj_apply, Matrix.sub_mul, pK1']
  have hfix : U₁ * U₁ᵀ * (K τ * V₀ᵀ) = K τ * V₀ᵀ := by
    rw [hs.kQR]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U₁ᵀ U₁, hU₁, Matrix.one_mul]
  have dS0 : defect (leftProj U₁ * rightProj V₀) (Frobenius.rightMulCLM Φ) cl (U₁ * S 0 * V₀ᵀ) =
      U₁ * U₁ᵀ * ((cl mm * V₀ - K τ) * V₀ᵀ) := by
    rw [hS0]
    simp only [defect, Frobenius.rightMulCLM_apply, mul_apply_eq_comp, leftProj_apply,
      rightProj_apply, pK1']
    rw [Matrix.sub_mul, Matrix.mul_sub, hfix]
  have dSt : defect (leftProj U₁ * rightProj V₀) (Frobenius.rightMulCLM Φ) cl (U₁ * S τ * V₀ᵀ) =
      U₁ * (U₁ᵀ * cl mm * V₀ - S τ) * V₀ᵀ := by
    have e : (Frobenius.rightMulCLM Φ) (U₁ * S τ * V₀ᵀ) = mm := by
      rw [Frobenius.rightMulCLM_apply, pS1']
    simp only [defect, e, mul_apply_eq_comp, leftProj_apply, rightProj_apply]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [dKt, dK0] at pK2
  rw [dSt, dS0, pK2, Matrix.mul_smul, smul_smul] at pS2
  have hexp : Real.exp (-(-1) * τ / ε) * Real.exp (-1 * τ / ε) = 1 := by
    rw [← Real.exp_add]
    have e0 : -(-1) * τ / ε + -1 * τ / ε = 0 := by ring
    rw [e0, Real.exp_zero]
  rw [hexp, one_smul] at pS2
  have hcancel : ∀ A : Matrix r r ℝ, U₁ᵀ * (U₁ * A * V₀ᵀ) * V₀ = A := fun A => by
    calc U₁ᵀ * (U₁ * A * V₀ᵀ) * V₀ = (U₁ᵀ * U₁) * A * (V₀ᵀ * V₀) := by
          simp only [Matrix.mul_assoc]
      _ = A := by rw [hU₁, hV₀, Matrix.one_mul, Matrix.mul_one]
  have h1 := congrArg (fun Z => U₁ᵀ * Z * V₀) pS2
  beta_reduce at h1
  rw [hcancel] at h1
  rw [pS1', h1]
  have e2 : U₁ * U₁ᵀ * ((cl mm * V₀ - U₀ * S₀) * V₀ᵀ) =
      U₁ * (U₁ᵀ * (cl mm * V₀ - U₀ * S₀)) * V₀ᵀ := by
    simp only [Matrix.mul_assoc]
  rw [e2, hcancel]

/-- **The last sentence of Section 4, the K-step** (arXiv 1804.04561: "if we can assume that our
low-rank approximation is able to exactly represent the Maxwell–Boltzmann distribution, then the
dynamical low-rank splitting would yield exactly the correct form of the distribution function").
If `V` represents the Maxwellian, then `f = K Vᵀ` is Maxwellian up to the initial layer and `O(ε)`:
`‖M (f) - f‖ ≤ e^{-t/ε} ‖M (f₀) - f₀‖ + C ε`, with `C` independent of `ε`. -/
theorem kStep_reproduces_maxwellian (hc : IsClosure cl cl' U L c₀) (hV : Vᵀ * V = 1)
    (hex : ∀ μ ∈ U, cl μ * V * Vᵀ = cl μ) (hcl : ∀ μ ∈ U, cl μ * Φ = μ) (K₀ : Matrix m r ℝ) :
    ∃ C : ℝ, ∀ ε > 0, ∀ K : ℝ → Matrix m r ℝ,
      ODESolution (MatrixKSL.kField V (bgkField D ξ (fun f => cl (f * Φ)) ε)) K 0 τ →
      K 0 = K₀ → (∀ t ∈ Icc (0 : ℝ) τ, K t * Vᵀ * Φ ∈ U) → ∀ t ∈ Icc (0 : ℝ) τ,
        ‖cl (K t * Vᵀ * Φ) - K t * Vᵀ‖ ≤
          Real.exp (-t / ε) * ‖cl (K₀ * Vᵀ * Φ) * V - K₀‖ + ε * C := by
  have hP := isOrthProj_rightProj (m := m) hV
  have hdef : ∀ Y : Matrix m r ℝ, ‖defect (rightProj V) (Frobenius.rightMulCLM Φ) cl (Y * Vᵀ)‖ =
      ‖cl (Y * Vᵀ * Φ) * V - Y‖ := fun Y => by
    have e : defect (rightProj V) (Frobenius.rightMulCLM Φ) cl (Y * Vᵀ) =
        (cl (Y * Vᵀ * Φ) * V - Y) * Vᵀ := by
      simp only [defect, Frobenius.rightMulCLM_apply, rightProj_apply, Matrix.sub_mul]
    rw [e, Frobenius.norm_mul_transpose_of_orthonormal hV]
  set z := ‖cl (K₀ * Vᵀ * Φ) * V - K₀‖ ^ 2 + ‖K₀ * Vᵀ * Φ‖ ^ 2 + 1 with hz
  refine ⟨relaxB ‖-transport D ξ‖ ‖(Frobenius.rightMulCLM Φ : Matrix m n ℝ →L[ℝ] Matrix m q ℝ)‖
    L c₀ τ z, fun ε hε K hK hK0 hU t ht => ?_⟩
  have hsol := kStep_isRelaxSol (D := D) (ξ := ξ) (ε := ε) hV (cons_of_exact hex hcl) hK hU
  have hzz : ‖defect (rightProj V) (Frobenius.rightMulCLM Φ) cl (K 0 * Vᵀ)‖ ^ 2 +
      ‖Frobenius.rightMulCLM Φ (K 0 * Vᵀ)‖ ^ 2 + 1 ≤ z := by
    rw [hdef, hK0, Frobenius.rightMulCLM_apply]
  have h1 := hsol.defect_le hP hc hε hzz ht
  have e : defect (rightProj V) (Frobenius.rightMulCLM Φ) cl (K t * Vᵀ) =
      cl (K t * Vᵀ * Φ) - K t * Vᵀ := by
    simp only [defect, Frobenius.rightMulCLM_apply, rightProj_apply, hex _ (hU t ht)]
  beta_reduce at h1
  rwa [e, hdef, hK0] at h1

/-- **The last sentence of Section 4, the L-step, which ends each step of the scheme**
(arXiv 1804.04561).  If `X` represents the Maxwellian, then `f = X Lᵀ` is Maxwellian up to the
initial layer and `O(ε)`.  The constant depends on `X` and `L₀` only through the initial defect and
moments (`IsRelaxSol.defect_le`).  In the scheme `L₀` comes from the S-step, which has no uniform
bound in general (`sStep_diverges`), so this is a statement about the last substep. -/
theorem lStep_reproduces_maxwellian (hc : IsClosure cl cl' U L c₀) (hX : Xᵀ * X = 1)
    (hex : ∀ μ ∈ U, X * Xᵀ * cl μ = cl μ) (hcl : ∀ μ ∈ U, cl μ * Φ = μ) (L₀ : Matrix n r ℝ) :
    ∃ C : ℝ, ∀ ε > 0, ∀ Lf : ℝ → Matrix n r ℝ,
      ODESolution (MatrixKSL.lField X (bgkField D ξ (fun f => cl (f * Φ)) ε)) Lf 0 τ →
      Lf 0 = L₀ → (∀ t ∈ Icc (0 : ℝ) τ, X * (Lf t)ᵀ * Φ ∈ U) → ∀ t ∈ Icc (0 : ℝ) τ,
        ‖cl (X * (Lf t)ᵀ * Φ) - X * (Lf t)ᵀ‖ ≤
          Real.exp (-t / ε) * ‖(cl (X * L₀ᵀ * Φ))ᵀ * X - L₀‖ + ε * C := by
  have hP := isOrthProj_leftProj (n := n) hX
  have hdef : ∀ Y : Matrix n r ℝ, ‖defect (leftProj X) (Frobenius.rightMulCLM Φ) cl (X * Yᵀ)‖ =
      ‖(cl (X * Yᵀ * Φ))ᵀ * X - Y‖ := fun Y => by
    have e : defect (leftProj X) (Frobenius.rightMulCLM Φ) cl (X * Yᵀ) =
        X * ((cl (X * Yᵀ * Φ))ᵀ * X - Y)ᵀ := by
      simp only [defect, Frobenius.rightMulCLM_apply, leftProj_apply, Matrix.transpose_sub,
        Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_sub, Matrix.mul_assoc]
    rw [e, Frobenius.norm_mul_of_orthonormal hX, Frobenius.norm_transpose]
  set z := ‖(cl (X * L₀ᵀ * Φ))ᵀ * X - L₀‖ ^ 2 + ‖X * L₀ᵀ * Φ‖ ^ 2 + 1 with hz
  refine ⟨relaxB ‖-transport D ξ‖ ‖(Frobenius.rightMulCLM Φ : Matrix m n ℝ →L[ℝ] Matrix m q ℝ)‖
    L c₀ τ z, fun ε hε Lf hL hL0 hU t ht => ?_⟩
  have hsol := lStep_isRelaxSol (D := D) (ξ := ξ) (ε := ε) hX hcl hL hU
  have hzz : ‖defect (leftProj X) (Frobenius.rightMulCLM Φ) cl (X * (Lf 0)ᵀ)‖ ^ 2 +
      ‖Frobenius.rightMulCLM Φ (X * (Lf 0)ᵀ)‖ ^ 2 + 1 ≤ z := by
    rw [hdef, hL0, Frobenius.rightMulCLM_apply]
  have h1 := hsol.defect_le hP hc hε hzz ht
  have e : defect (leftProj X) (Frobenius.rightMulCLM Φ) cl (X * (Lf t)ᵀ) =
      cl (X * (Lf t)ᵀ * Φ) - X * (Lf t)ᵀ := by
    simp only [defect, Frobenius.rightMulCLM_apply, leftProj_apply, hex _ (hU t ht)]
  beta_reduce at h1
  rwa [e, hdef, hL0] at h1

/-! #### The formal limits of Section 4 -/

omit [Fintype q] in
private lemma continuous_sum_mul {ι : Type*} [Fintype ι] {p p' l : Type*} [Fintype p]
    [Fintype p'] [Fintype l] (A : ι → Matrix p p' ℝ) (B : ι → Matrix l r ℝ) :
    Continuous fun K : Matrix p' l ℝ => ∑ a, A a * K * B a :=
  continuous_finsetSum _ fun a _ =>
    ((Frobenius.rightMulCLM (B a)).comp (Frobenius.leftMulCLM (A a)) :
      Matrix p' l ℝ →L[ℝ] Matrix p r ℝ).continuous

/-- **Section 4, the constraint of the K-step** (arXiv 1804.04561, Section 4), as a theorem about
the formal limit: if `K_ε → K₀` along `ε → 0`, with `ε K̇_ε → 0` (the assumption hidden in "taking
`ε → 0`") and `M` continuous at `K₀ Vᵀ`, then `K₀ = M (K₀ Vᵀ) V`. -/
theorem kStep_formal_constraint {ι : Type*} {l : Filter ι} [l.NeBot] {e : ι → ℝ}
    (he : Tendsto e l (𝓝 0)) (hne : ∀ᶠ i in l, e i ≠ 0) (hV : Vᵀ * V = 1)
    {K Kdot : ι → Matrix m r ℝ} {K₀ : Matrix m r ℝ} (hK : Tendsto K l (𝓝 K₀))
    (hM : ContinuousAt M (K₀ * Vᵀ))
    (hdot : ∀ i, Kdot i = MatrixKSL.kField V (bgkField D ξ M (e i)) 0 (K i))
    (hb : Tendsto (fun i => e i • Kdot i) l (𝓝 0)) : K₀ = M (K₀ * Vᵀ) * V := by
  have hG : ContinuousAt (fun K : Matrix m r ℝ => M (K * Vᵀ) * V) K₀ := by
    have h1 : ContinuousAt (fun K : Matrix m r ℝ => K * Vᵀ) K₀ :=
      (Frobenius.rightMulCLM Vᵀ : Matrix m r ℝ →L[ℝ] Matrix m n ℝ).continuous.continuousAt
    have h2 : ContinuousAt (fun K : Matrix m r ℝ => M (K * Vᵀ)) K₀ :=
      ContinuousAt.comp (f := fun K : Matrix m r ℝ => K * Vᵀ) (g := M) hM h1
    exact (Frobenius.rightMulCLM V :
      Matrix m n ℝ →L[ℝ] Matrix m r ℝ).continuous.continuousAt.comp h2
  have hA : ContinuousAt (fun K : Matrix m r ℝ => -∑ a, D a * K * cOne ξ V a) K₀ :=
    (continuous_sum_mul D (cOne ξ V)).neg.continuousAt
  refine formal_constraint he hne hK hG hA one_ne_zero (fun i => ?_) hb
  rw [hdot, eq23 hV, one_mul]

/-- **Section 4, the constraint of the L-step** (arXiv 1804.04561, Section 4), as a theorem about
the formal limit: `L₀ = M (X L₀ᵀ)ᵀ X`. -/
theorem lStep_formal_constraint {ι : Type*} {l : Filter ι} [l.NeBot] {e : ι → ℝ}
    (he : Tendsto e l (𝓝 0)) (hne : ∀ᶠ i in l, e i ≠ 0) (hX : Xᵀ * X = 1)
    {Lf Ldot : ι → Matrix n r ℝ} {L₀ : Matrix n r ℝ} (hL : Tendsto Lf l (𝓝 L₀))
    (hM : ContinuousAt M (X * L₀ᵀ))
    (hdot : ∀ i, Ldot i = MatrixKSL.lField X (bgkField D ξ M (e i)) 0 (Lf i))
    (hb : Tendsto (fun i => e i • Ldot i) l (𝓝 0)) : L₀ = (M (X * L₀ᵀ))ᵀ * X := by
  have hG : ContinuousAt (fun L : Matrix n r ℝ => (M (X * Lᵀ))ᵀ * X) L₀ := by
    have h1 : ContinuousAt (fun L : Matrix n r ℝ => X * Lᵀ) L₀ :=
      ((Frobenius.leftMulCLM X).comp Frobenius.transposeCLM :
        Matrix n r ℝ →L[ℝ] Matrix m n ℝ).continuous.continuousAt
    have h2 : ContinuousAt (fun L : Matrix n r ℝ => M (X * Lᵀ)) L₀ :=
      ContinuousAt.comp (f := fun L : Matrix n r ℝ => X * Lᵀ) (g := M) hM h1
    exact ((Frobenius.rightMulCLM X).comp Frobenius.transposeCLM :
      Matrix m n ℝ →L[ℝ] Matrix n r ℝ).continuous.continuousAt.comp h2
  have hA : ContinuousAt
      (fun L : Matrix n r ℝ => -∑ a, (Matrix.diagonal fun j => ξ j a) * L * (dOne D X a)ᵀ) L₀ :=
    (continuous_sum_mul (fun a => Matrix.diagonal fun j => ξ j a)
      (fun a => (dOne D X a)ᵀ)).neg.continuousAt
  refine formal_constraint he hne hL hG hA one_ne_zero (fun i => ?_) hb
  rw [hdot, eq25 hX, one_mul]

/-- **Section 4, the constraint of the S-step** (arXiv 1804.04561, Section 4), as a theorem about
the formal limit: `S₀ = Xᵀ M (X S₀ Vᵀ) V`.  This concerns a family that converges with
`ε Ṡ_ε → 0`; by `sStep_diverges`, solutions that start off the constraint leave every ball on
`[0, τ]` as `ε → 0`. -/
theorem sStep_formal_constraint {ι : Type*} {l : Filter ι} [l.NeBot] {e : ι → ℝ}
    (he : Tendsto e l (𝓝 0)) (hne : ∀ᶠ i in l, e i ≠ 0) (hX : Xᵀ * X = 1) (hV : Vᵀ * V = 1)
    {S Sdot : ι → Matrix r r ℝ} {S₀ : Matrix r r ℝ} (hS : Tendsto S l (𝓝 S₀))
    (hM : ContinuousAt M (X * S₀ * Vᵀ))
    (hdot : ∀ i, Sdot i = MatrixKSL.sField X V (bgkField D ξ M (e i)) 0 (S i))
    (hb : Tendsto (fun i => e i • Sdot i) l (𝓝 0)) : S₀ = Xᵀ * M (X * S₀ * Vᵀ) * V := by
  have hG : ContinuousAt (fun S : Matrix r r ℝ => Xᵀ * M (X * S * Vᵀ) * V) S₀ := by
    have h1 : ContinuousAt (fun S : Matrix r r ℝ => X * S * Vᵀ) S₀ :=
      ((Frobenius.rightMulCLM Vᵀ).comp (Frobenius.leftMulCLM X) :
        Matrix r r ℝ →L[ℝ] Matrix m n ℝ).continuous.continuousAt
    have h2 : ContinuousAt (fun S : Matrix r r ℝ => M (X * S * Vᵀ)) S₀ :=
      ContinuousAt.comp (f := fun S : Matrix r r ℝ => X * S * Vᵀ) (g := M) hM h1
    exact ((Frobenius.rightMulCLM V).comp (Frobenius.leftMulCLM Xᵀ) :
      Matrix m n ℝ →L[ℝ] Matrix r r ℝ).continuous.continuousAt.comp h2
  have hA : ContinuousAt (fun S : Matrix r r ℝ => ∑ a, dOne D X a * S * cOne ξ V a) S₀ :=
    (continuous_sum_mul (dOne D X) (cOne ξ V)).continuousAt
  refine formal_constraint he hne hS hG hA (neg_ne_zero.2 one_ne_zero) (fun i => ?_) hb
  rw [hdot, eq24 hX hV]
  congr 1
  rw [neg_one_mul, neg_smul, ← smul_neg, neg_sub]

/-- **The formula for `K_j` in Section 4** (arXiv 1804.04561):
`K_j = ρ (K) (2π)^{-d/2} ∫ V_j (v) exp (-(v - u (K))² / 2) dv`, here with the discrete Maxwellian
and the sum over the grid in place of the integral. -/
theorem kConstraint_maxwellian (w : n → ℝ) {K₀ : Matrix m r ℝ}
    (h : K₀ = discreteMaxwellian w ξ (K₀ * Vᵀ) * V) (i : m) (j : r) :
    K₀ i j = density w (K₀ * Vᵀ) i * gaussConst d *
      ∑ l, V l j * Real.exp (-‖ξ l - bulk w ξ (K₀ * Vᵀ) i‖ ^ 2 / 2) := by
  conv_lhs => rw [h]
  simp only [Matrix.mul_apply, discreteMaxwellian, Matrix.of_apply, maxwellian, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- **The formula for `L_i` in Section 4** (arXiv 1804.04561), with the sum over the grid in place
of the integral.  The paper omits the factor `(2π)^{-d/2}` here. -/
theorem lConstraint_maxwellian (w : n → ℝ) {L₀ : Matrix n r ℝ}
    (h : L₀ = (discreteMaxwellian w ξ (X * L₀ᵀ))ᵀ * X) (j : n) (i : r) :
    L₀ j i = gaussConst d * ∑ k, X k i * density w (X * L₀ᵀ) k *
      Real.exp (-‖ξ j - bulk w ξ (X * L₀ᵀ) k‖ ^ 2 / 2) := by
  conv_lhs => rw [h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, discreteMaxwellian, Matrix.of_apply,
    maxwellian, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **The formula for `S_{ij}` in Section 4** (arXiv 1804.04561), with the sum over the grid in
place of the integral.  The paper omits the factor `(2π)^{-d/2}` here. -/
theorem sConstraint_maxwellian (w : n → ℝ) {S₀ : Matrix r r ℝ}
    (h : S₀ = Xᵀ * discreteMaxwellian w ξ (X * S₀ * Vᵀ) * V) (i j : r) :
    S₀ i j = gaussConst d * ∑ k, ∑ l, X k i * V l j * density w (X * S₀ * Vᵀ) k *
      Real.exp (-‖ξ l - bulk w ξ (X * S₀ * Vᵀ) k‖ ^ 2 / 2) := by
  conv_lhs => rw [h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, discreteMaxwellian, Matrix.of_apply,
    maxwellian, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

private lemma gaussConst_ne_one (hd : 0 < d) : gaussConst d ≠ 1 := by
  have h1 : (1 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h2 : (1 : ℝ) < (2 * Real.pi) ^ ((d : ℝ) / 2) :=
    Real.one_lt_rpow h1 (by have : (0 : ℝ) < d := by exact_mod_cast hd
                            positivity)
  exact (inv_lt_one_of_one_lt₀ h2).ne

/-- **The formula for `L_i` as printed in Section 4 is false** (arXiv 1804.04561): it lacks the
factor `(2π)^{-d/2}` of `lConstraint_maxwellian`, so it fails wherever `L₀` does not vanish. -/
theorem lConstraint_printed_false (hd : 0 < d) (w : n → ℝ) {L₀ : Matrix n r ℝ}
    (h : L₀ = (discreteMaxwellian w ξ (X * L₀ᵀ))ᵀ * X) {j : n} {i : r} (hne : L₀ j i ≠ 0) :
    L₀ j i ≠ ∑ k, X k i * density w (X * L₀ᵀ) k *
      Real.exp (-‖ξ j - bulk w ξ (X * L₀ᵀ) k‖ ^ 2 / 2) := by
  intro hp
  have h1 := lConstraint_maxwellian w h j i
  rw [← hp] at h1
  have h2 : (1 - gaussConst d) * L₀ j i = 0 := by linarith
  have h3 := (mul_eq_zero.1 h2).resolve_right hne
  exact gaussConst_ne_one hd (sub_eq_zero.1 h3).symm

/-- **The formula for `S_{ij}` as printed in Section 4 is false** (arXiv 1804.04561): it lacks the
factor `(2π)^{-d/2}` of `sConstraint_maxwellian`, so it fails wherever `S₀` does not vanish. -/
theorem sConstraint_printed_false (hd : 0 < d) (w : n → ℝ) {S₀ : Matrix r r ℝ}
    (h : S₀ = Xᵀ * discreteMaxwellian w ξ (X * S₀ * Vᵀ) * V) {i j : r} (hne : S₀ i j ≠ 0) :
    S₀ i j ≠ ∑ k, ∑ l, X k i * V l j * density w (X * S₀ * Vᵀ) k *
      Real.exp (-‖ξ l - bulk w ξ (X * S₀ * Vᵀ) k‖ ^ 2 / 2) := by
  intro hp
  have h1 := sConstraint_maxwellian w h i j
  rw [← hp] at h1
  have h2 : (1 - gaussConst d) * S₀ i j = 0 := by linarith
  have h3 := (mul_eq_zero.1 h2).resolve_right hne
  exact gaussConst_ne_one hd (sub_eq_zero.1 h3).symm

/-- **The scheme reproduces a Maxwellian exactly**, for every `ε` (arXiv 1804.04561, end of
Section 4), without transport, where a Maxwellian is stationary: if `M (Y₀) = Y₀` for
`Y₀ = U₀ S₀ V₀ᵀ`, one step of the scheme returns `Y₀`.  With transport a Maxwellian is not
stationary, and `kStep_reproduces_maxwellian`, `lStep_reproduces_maxwellian` are the statements. -/
theorem step_reproduces_maxwellian (hT : transport D ξ = 0) {U₀ U₁ : Matrix m r ℝ}
    {S₀ Ŝ₁ : Matrix r r ℝ} {V₀ : Matrix n r ℝ} {K : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ}
    {Lf : ℝ → Matrix n r ℝ}
    (hs : MatrixKSL.IsStep (bgkField D ξ (fun f => cl (f * Φ)) ε) 0 τ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf)
    (hτ : 0 ≤ τ) (hcl₁ : ∀ μ ∈ U, cl μ * V₀ * V₀ᵀ * Φ = μ) (hcl₂ : ∀ μ ∈ U, cl μ * Φ = μ)
    (hUK : ∀ t ∈ Icc (0 : ℝ) τ, K t * V₀ᵀ * Φ ∈ U)
    (hUS : ∀ t ∈ Icc (0 : ℝ) τ, U₁ * S t * V₀ᵀ * Φ ∈ U)
    (hUL : ∀ t ∈ Icc (0 : ℝ) τ, U₁ * (Lf t)ᵀ * Φ ∈ U)
    (hY : cl (U₀ * S₀ * V₀ᵀ * Φ) = U₀ * S₀ * V₀ᵀ) :
    U₁ * (Lf τ)ᵀ = U₀ * S₀ * V₀ᵀ := by
  have hA : -transport D ξ = 0 := by rw [hT, neg_zero]
  have hV₀ := hs.orthV₀
  have hU₁ := hs.orthU₁
  have hK := kStep_isRelaxSol (D := D) (ξ := ξ) (ε := ε) hV₀ hcl₁ hs.kSol hUK
  have hS := sStep_isRelaxSol (D := D) (ξ := ξ) (ε := ε) hU₁ hV₀ hcl₁ hs.sSol hUS
  have hL := lStep_isRelaxSol (D := D) (ξ := ξ) (ε := ε) hU₁ hcl₂ hs.lSol hUL
  rw [hA] at hK hS hL
  have hτm : τ ∈ Icc (0 : ℝ) τ := ⟨hτ, le_rfl⟩
  obtain ⟨pK1, pK2⟩ := pure_relaxation hK (isOrthProj_rightProj hV₀) hτm
  obtain ⟨pS1, pS2⟩ := pure_relaxation hS (isOrthProj_leftProj_mul_rightProj hU₁ hV₀) hτm
  obtain ⟨pL1, pL2⟩ := pure_relaxation hL (isOrthProj_leftProj hU₁) hτm
  simp only [Frobenius.rightMulCLM_apply] at pK1 pS1 pL1
  set Y₀ := U₀ * S₀ * V₀ᵀ with hY₀
  have hK0 : K 0 * V₀ᵀ = Y₀ := by rw [hs.kStart]
  have hPV : rightProj V₀ Y₀ = Y₀ := by
    rw [hY₀]
    exact rightProj_mul_transpose hV₀ (U₀ * S₀)
  -- the K-step does not move `Y₀`
  have hKτ : K τ * V₀ᵀ = Y₀ := by
    rw [hK0] at pK1 pK2
    have d0 : defect (rightProj V₀) (Frobenius.rightMulCLM Φ) cl Y₀ = 0 := by
      simp only [defect, Frobenius.rightMulCLM_apply, hY, hPV, sub_self]
    rw [d0, smul_zero] at pK2
    have e := sub_eq_zero.1 pK2
    rw [Frobenius.rightMulCLM_apply, pK1, hY, hPV] at e
    exact e.symm
  have hfix : leftProj U₁ Y₀ = Y₀ := by
    rw [← hKτ, hs.kQR, Matrix.mul_assoc]
    exact leftProj_mul_left hU₁ _
  -- the S-step does not move `Y₀`
  have hS0 : U₁ * S 0 * V₀ᵀ = Y₀ := by rw [hs.sStart, ← hs.kQR, hKτ]
  have hSτ : U₁ * S τ * V₀ᵀ = Y₀ := by
    rw [hS0] at pS1 pS2
    have d0 : defect (leftProj U₁ * rightProj V₀) (Frobenius.rightMulCLM Φ) cl Y₀ = 0 := by
      simp only [defect, Frobenius.rightMulCLM_apply, mul_apply_eq_comp, hY, hPV, hfix, sub_self]
    rw [d0, smul_zero] at pS2
    have e := sub_eq_zero.1 pS2
    rw [Frobenius.rightMulCLM_apply, pS1, mul_apply_eq_comp, hY, hPV, hfix] at e
    exact e.symm
  -- the L-step does not move `Y₀`
  have hL0 : U₁ * (Lf 0)ᵀ = Y₀ := by
    rw [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, hSτ]
  rw [hL0] at pL1 pL2
  have d0 : defect (leftProj U₁) (Frobenius.rightMulCLM Φ) cl Y₀ = 0 := by
    simp only [defect, Frobenius.rightMulCLM_apply, hY, hfix, sub_self]
  rw [d0, smul_zero] at pL2
  have e := sub_eq_zero.1 pL2
  rw [Frobenius.rightMulCLM_apply, pL1, hY, hfix] at e
  exact e.symm

end Scheme

/-! ### Counterexamples and instances -/

section Examples

/-- Solutions from a derivative on all of `ℝ`. -/
private lemma odeSolution_of_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E → E} {y : ℝ → E} {a b : ℝ} (h : ∀ t, HasDerivAt y (f t (y t)) t) :
    ODESolution f y a b where
  cont t _ := (h t).continuousAt.continuousWithinAt
  deriv t _ := (h t).hasDerivWithinAt

/-- The curve `t ↦ G + e^{c t + b} w`. -/
private lemma hasDerivAt_exp_curve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G w : E) (c b t : ℝ) :
    HasDerivAt (fun t => G + Real.exp (c * t + b) • w)
      ((c * Real.exp (c * t + b)) • w) t := by
  have h1 : HasDerivAt (fun t : ℝ => c * t + b) c t := by
    simpa using ((hasDerivAt_id' t).const_mul c).add_const b
  have h2 := h1.exp
  rw [mul_comm] at h2
  exact (h2.smul_const w).const_add G

variable {d : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- **The S-step undoes the K-step: an explicit step** (compare arXiv 1804.04561, Section 4).  Take
the linear BGK model `M f = f Q` with `Q² = Q`, no transport, and full bases `X = V = 1`.  For every
`ε > 0`, `τ` and every `Y₀` there is a step of the scheme (`IsStep`) in which the K-step has defect
`K (τ) - M (K (τ)) = e^{-τ/ε} (Y₀ - Y₀ Q)`, and the S-step has defect
`S (τ) - M (S (τ)) = Y₀ - Y₀ Q`, for every `ε`: the constraint of the S-step is not reached as
`ε → 0`. -/
theorem sStep_constraint_fails (ξ : n → Vel d) {Q : Matrix n n ℝ} (hQ : Q * Q = Q)
    (Y₀ : Matrix n n ℝ) (ε τ : ℝ) :
    ∃ (Ŝ₁ : Matrix n n ℝ) (K S : ℝ → Matrix n n ℝ) (Lf : ℝ → Matrix n n ℝ),
      MatrixKSL.IsStep (bgkField (fun _ => 0) ξ (fun f => f * Q) ε) 0 τ 1 Y₀ 1 1 Ŝ₁ K S Lf ∧
      K τ - K τ * Q = Real.exp (-τ / ε) • (Y₀ - Y₀ * Q) ∧
      S τ - S τ * Q = Y₀ - Y₀ * Q := by
  set G := Y₀ * Q with hG
  set w := Y₀ - G with hw
  have hGQ : G * Q = G := by rw [hG, Matrix.mul_assoc, hQ]
  have hwQ : w * Q = 0 := by rw [hw, Matrix.sub_mul, hGQ, hG, sub_self]
  have hGw : G + w = Y₀ := by rw [hw]; abel
  have hT : transport (fun _ : Fin d => (0 : Matrix n n ℝ)) ξ = 0 := by
    ext f
    simp [transport_apply]
  have hF : ∀ (t c : ℝ), bgkField (fun _ => 0) ξ (fun f => f * Q) ε t (G + c • w) =
      (-(ε⁻¹ * c)) • w := fun t c => by
    have e : (G + c • w) * Q = G := by rw [Matrix.add_mul, Matrix.smul_mul, hwQ, smul_zero, hGQ,
      add_zero]
    simp only [bgkField, hT, e, zero_apply, neg_zero, zero_add]
    rw [sub_add_eq_sub_sub, sub_self, zero_sub, smul_neg, smul_smul, neg_smul]
  set F := bgkField (fun _ : Fin d => (0 : Matrix n n ℝ)) ξ (fun f => f * Q) ε with hFdef
  have hk : ∀ t Y, MatrixKSL.kField 1 F t Y = F t Y := fun t Y => by simp [MatrixKSL.kField]
  have hs : ∀ t Y, MatrixKSL.sField 1 1 F t Y = -F t Y := fun t Y => by simp [MatrixKSL.sField]
  have hl : ∀ t Y, MatrixKSL.lField 1 F t Y = (F t Yᵀ)ᵀ := fun t Y => by simp [MatrixKSL.lField]
  set K : ℝ → Matrix n n ℝ := fun t => G + Real.exp (-ε⁻¹ * t + 0) • w with hK
  set S : ℝ → Matrix n n ℝ := fun t => G + Real.exp (ε⁻¹ * t + -ε⁻¹ * τ) • w with hS
  have hKd : ∀ t, HasDerivAt K (F t (K t)) t := fun t => by
    have h := hasDerivAt_exp_curve G w (-ε⁻¹) 0 t
    simp only [hK]
    rw [hF, ← neg_mul]
    exact h
  have hSd : ∀ t, HasDerivAt S (-F t (S t)) t := fun t => by
    have h := hasDerivAt_exp_curve G w ε⁻¹ (-ε⁻¹ * τ) t
    simp only [hS]
    rw [hF, neg_smul, neg_neg]
    exact h
  have hK0 : K 0 = Y₀ := by simp [hK, hGw]
  have hSτ : S τ = Y₀ := by
    simp [hS, hGw]
  have hKτ : K τ * Q = G := by
    simp only [hK]
    rw [Matrix.add_mul, Matrix.smul_mul, hwQ, smul_zero, hGQ, add_zero]
  refine ⟨K τ, K, S, fun t => (K t)ᵀ, ?_, ?_, ?_⟩
  · exact
      { orthV₀ := by simp
        kSol := odeSolution_of_hasDerivAt fun t => by rw [hk]; exact hKd t
        kStart := by rw [hK0, Matrix.one_mul]
        orthU₁ := by simp
        kQR := by rw [Matrix.one_mul]
        sSol := odeSolution_of_hasDerivAt fun t => by rw [hs]; exact hSd t
        sStart := by
          simp only [hS, hK]
          congr 3
          ring
        lSol := odeSolution_of_hasDerivAt fun t => by
          rw [hl, Matrix.transpose_transpose]
          exact Frobenius.hasDerivAt_transpose (hKd t)
        lStart := by rw [hK0, hSτ, Matrix.one_mul] }
  · rw [hKτ]
    have e : -ε⁻¹ * τ + 0 = -τ / ε := by ring
    simp only [hK, e]
    rw [add_sub_cancel_left]
  · rw [hSτ]

/-- The velocity basis of `kStep_repels`: a unit vector that contains neither the moment `(1, 1)`
nor the equilibrium `(9/10, 1/10)`. -/
noncomputable def repV : Matrix (Fin 2) (Fin 1) ℝ := !![4 / 5; 3 / 5]

/-- The moment `(1, 1)` of `kStep_repels`. -/
noncomputable def repΦ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 1]

/-- The positive equilibrium profile `(9/10, 1/10)` of `kStep_repels`, with unit mass. -/
noncomputable def repΨ : Matrix (Fin 1) (Fin 2) ℝ := !![9 / 10, 1 / 10]

lemma repV_orth : repVᵀ * repV = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [repV, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

/-- The equilibrium of `kStep_repels` conserves the mass. -/
lemma repΨ_mul_repΦ : repΨ * repΦ = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [repΨ, repΦ, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

private lemma rep_lambda : repVᵀ * (repΦ * repΨ) * repV = (273 / 250 : ℝ) • 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [repV, repΦ, repΨ, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

/-- **Without moment conservation the K-step repels its constraint**, so the hypothesis `hcl` of
`kStep_singular_limit` cannot be dropped.  Two velocities, one spatial cell, no transport, rank
one: the equilibrium `M f = ρ (f) (9/10, 1/10)` is positive and conserves the mass `ρ = f₁ + f₂`,
but `V = (4/5, 3/5)` contains neither the moment `(1, 1)` nor the profile `(9/10, 1/10)`.  Then
`K̇ = (23 / (250 ε)) K`: the only solution of the constraint `K = M (K Vᵀ) V` is `K = 0`, and the
K-step starting from `K = 1` has defect `(23/250) e^{23 t / (250 ε)}`, which blows up as `ε → 0`.
(arXiv 1804.04561, Section 4, on Eq. (23).) -/
theorem kStep_repels {d : ℕ} (ξ : Fin 2 → Vel d) (ε τ : ℝ) :
    ∃ K : ℝ → Matrix (Fin 1) (Fin 1) ℝ,
      ODESolution (MatrixKSL.kField repV (bgkField (fun _ : Fin d => 0) ξ
        (fun f => f * repΦ * repΨ) ε)) K 0 τ ∧ K 0 = 1 ∧
      ∀ t, K t * repVᵀ * repΦ * repΨ * repV - K t =
        ((23 / 250) * Real.exp (23 / 250 * ε⁻¹ * t)) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have hG : ∀ Y : Matrix (Fin 1) (Fin 1) ℝ,
      Y * repVᵀ * repΦ * repΨ * repV = (273 / 250 : ℝ) • Y := fun Y => by
      calc Y * repVᵀ * repΦ * repΨ * repV = Y * (repVᵀ * (repΦ * repΨ) * repV) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [rep_lambda, Matrix.mul_smul, Matrix.mul_one]
  have hfield : ∀ t (Y : Matrix (Fin 1) (Fin 1) ℝ),
      MatrixKSL.kField repV (bgkField (fun _ : Fin d => 0) ξ (fun f => f * repΦ * repΨ) ε) t Y =
        (23 / 250 * ε⁻¹) • Y := fun t Y => by
    rw [eq23 repV_orth]
    simp only [Matrix.zero_mul, Finset.sum_const_zero, neg_zero, zero_add]
    rw [hG]
    module
  set c : ℝ := 23 / 250 * ε⁻¹ with hc
  refine ⟨fun t => Real.exp (c * t) • 1, odeSolution_of_hasDerivAt fun t => ?_, by simp,
    fun t => ?_⟩
  · have h := hasDerivAt_exp_curve (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 c 0 t
    simp only [zero_add, add_zero] at h
    rw [hfield, smul_smul]
    exact h
  · beta_reduce
    rw [hG]
    module

private lemma gaussConst_one_ne : gaussConst 1 ≠ 1 := by
  have h1 : (1 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h2 : (1 : ℝ) < (2 * Real.pi) ^ (((1 : ℕ) : ℝ) / 2) := Real.one_lt_rpow h1 (by norm_num)
  exact (inv_lt_one_of_one_lt₀ h2).ne

/-- The Maxwellian of a one-cell, one-velocity model with `w = 1`, `ξ = 0`. -/
private noncomputable abbrev exM : Matrix (Fin 1) (Fin 1) ℝ → Matrix (Fin 1) (Fin 1) ℝ :=
  discreteMaxwellian (d := 1) (fun _ => 1) (fun _ => 0)

private lemma exM_one : exM 1 = gaussConst 1 • 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [exM, discreteMaxwellian, Kinetic.density_apply, momentum, bulk, maxwellian]

/-- **Eq. (23) as printed is false** (arXiv 1804.04561), already for the true discrete Maxwellian
on one cell and one velocity: see `eq23_printed_iff`. -/
theorem eq23_printed_false :
    ∃ K : Matrix (Fin 1) (Fin 1) ℝ,
      -MatrixKSL.kField (1 : Matrix (Fin 1) (Fin 1) ℝ)
          (bgkField (fun _ : Fin 1 => 0) (fun _ => 0) exM 1) 0 K ≠
        ∑ a, (0 : Matrix (Fin 1) (Fin 1) ℝ) * K *
            cOne (d := 1) (fun _ : Fin 1 => 0) (1 : Matrix (Fin 1) (Fin 1) ℝ) a -
          (1 : ℝ)⁻¹ • (K - exM (K * 1ᵀ) * 1) := by
  refine ⟨1, fun h => ?_⟩
  have hV : (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1 = 1 := by simp
  have h1 := (eq23_printed_iff (D := fun _ : Fin 1 => 0) (ξ := fun _ => 0) (M := exM) (ε := 1)
    hV one_ne_zero 0 1).1 h
  simp only [Matrix.transpose_one, Matrix.mul_one, exM_one] at h1
  have h2 := congrFun (congrFun h1 0) 0
  have h3 : (1 : ℝ) = gaussConst 1 := by simpa using h2
  exact gaussConst_one_ne h3.symm

/-- **Eq. (25) as printed is false** (arXiv 1804.04561), already for the true discrete Maxwellian
on one cell and one velocity: see `eq25_printed_iff`. -/
theorem eq25_printed_false :
    ∃ Lf : Matrix (Fin 1) (Fin 1) ℝ,
      -MatrixKSL.lField (1 : Matrix (Fin 1) (Fin 1) ℝ)
          (bgkField (fun _ : Fin 1 => 0) (fun _ => 0) exM 1) 0 Lf ≠
        -∑ a : Fin 1, (Matrix.diagonal fun j => (fun _ : Fin 1 => (0 : Vel 1)) j a) * Lf *
            (dOne (fun _ : Fin 1 => (0 : Matrix (Fin 1) (Fin 1) ℝ))
              (1 : Matrix (Fin 1) (Fin 1) ℝ) a)ᵀ -
          (1 : ℝ)⁻¹ • (Lf - (exM (1 * Lfᵀ))ᵀ * 1) := by
  refine ⟨1, fun h => ?_⟩
  have hX : (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1 = 1 := by simp
  have h1 := (eq25_printed_iff (D := fun _ : Fin 1 => 0) (ξ := fun _ => 0) (M := exM) (ε := 1)
    hX 0 1).1 h
  rw [eq25 hX] at h1
  simp only [Matrix.transpose_one, Matrix.mul_one, exM_one] at h1
  have h2 := congrFun (congrFun h1 0) 0
  have h3 : gaussConst 1 - 1 = 0 := by simpa [dOne] using h2
  exact gaussConst_one_ne (sub_eq_zero.1 h3)

/-- One cell, one velocity `ξ = 0`, and the quadrature weight `w = (2π)^{1/2}`, which integrates
the Gaussian exactly: then every `f` is its own discrete Maxwellian. -/
private lemma discreteMaxwellian_exact (f : Matrix (Fin 1) (Fin 1) ℝ) :
    discreteMaxwellian (d := 1) (fun _ => (gaussConst 1)⁻¹) (fun _ => 0) f = f := by
  have hc := (gaussConst_pos 1).ne'
  ext i j
  fin_cases i
  fin_cases j
  simp [discreteMaxwellian, Kinetic.density_apply, momentum, bulk, maxwellian]
  field_simp

/-- **The formula for `L_i` printed in Section 4 fails** (arXiv 1804.04561), unconditionally: with
the data of `discreteMaxwellian_exact` and `X = 1`, `L₀ = 1` satisfies the constraint of the
L-step, and `lConstraint_printed_false` applies. -/
example : ∃ (w : Fin 1 → ℝ) (L₀ : Matrix (Fin 1) (Fin 1) ℝ),
    L₀ = (discreteMaxwellian (d := 1) w (fun _ => 0) (1 * L₀ᵀ))ᵀ * 1 ∧
    L₀ 0 0 ≠ ∑ k, (1 : Matrix (Fin 1) (Fin 1) ℝ) k 0 * density w (1 * L₀ᵀ) k *
      Real.exp (-‖(0 : Vel 1) - bulk w (fun _ => 0) (1 * L₀ᵀ) k‖ ^ 2 / 2) := by
  have h : (1 : Matrix (Fin 1) (Fin 1) ℝ) =
      (discreteMaxwellian (d := 1) (fun _ => (gaussConst 1)⁻¹) (fun _ => 0) (1 * 1ᵀ))ᵀ * 1 := by
    rw [discreteMaxwellian_exact]
    simp
  exact ⟨_, 1, h, lConstraint_printed_false one_pos _ h (by simp)⟩

/-- **The formula for `S_{ij}` printed in Section 4 fails** (arXiv 1804.04561), unconditionally:
with the data of `discreteMaxwellian_exact` and `X = V = 1`, `S₀ = 1` satisfies the constraint of
the S-step, and `sConstraint_printed_false` applies. -/
example : ∃ (w : Fin 1 → ℝ) (S₀ : Matrix (Fin 1) (Fin 1) ℝ),
    S₀ = 1ᵀ * discreteMaxwellian (d := 1) w (fun _ => 0) (1 * S₀ * 1ᵀ) * 1 ∧
    S₀ 0 0 ≠ ∑ k, ∑ l, (1 : Matrix (Fin 1) (Fin 1) ℝ) k 0 * (1 : Matrix (Fin 1) (Fin 1) ℝ) l 0 *
      density w (1 * S₀ * 1ᵀ) k *
        Real.exp (-‖(0 : Vel 1) - bulk w (fun _ => 0) (1 * S₀ * 1ᵀ) k‖ ^ 2 / 2) := by
  have h : (1 : Matrix (Fin 1) (Fin 1) ℝ) =
      1ᵀ * discreteMaxwellian (d := 1) (fun _ => (gaussConst 1)⁻¹) (fun _ => 0) (1 * 1 * 1ᵀ) *
        1 := by
    rw [discreteMaxwellian_exact]
    simp
  exact ⟨_, 1, h, sConstraint_printed_false one_pos _ h (by simp)⟩

/-! #### The hypotheses of the singular limit can hold -/

/-- Linear ODEs have solutions. -/
private lemma exists_linear_solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (B : E →L[ℝ] E) (y₀ : E) (a b : ℝ) :
    ∃ y : ℝ → E, ODESolution (fun _ x => B x) y a b ∧ y a = y₀ := by
  refine ⟨fun t => NormedSpace.exp ((t - a) • B) y₀, odeSolution_of_hasDerivAt fun t => ?_,
    by simp⟩
  have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • B)) (B * NormedSpace.exp ((t - a) • B))
      (t - a) := hasDerivAt_exp_smul_const' B (t - a)
  have h2 : HasDerivAt (fun t : ℝ => t - a) 1 t := (hasDerivAt_id' t).sub_const a
  have h3 := h1.scomp t h2
  simp only [one_smul] at h3
  exact h3.clm_apply (hasDerivAt_const t y₀) |>.congr_deriv (by simp)

variable {m r q : Type*} [Fintype m] [Fintype r] [Fintype q] [DecidableEq r] [DecidableEq q]

/-- A linear closure `ℳ μ = μ Ψ`, for instance the first-order truncation of Eq. (8) in `(ρ, ρ u)`
on a lattice, is a closure on all moments.
(arXiv 1804.04561, Section 4, an instance.) -/
theorem isClosure_linear (Ψ : Matrix q n ℝ) :
    IsClosure (fun μ : Matrix m q ℝ => μ * Ψ) (fun _ => Frobenius.rightMulCLM Ψ) univ
      ‖(Frobenius.rightMulCLM Ψ : Matrix m q ℝ →L[ℝ] Matrix m n ℝ)‖ 0 where
  convex := convex_univ
  hasFDerivAt _ _ := (Frobenius.rightMulCLM Ψ).hasFDerivAt
  deriv_le _ _ := le_rfl
  growth μ _ := by simpa using (Frobenius.rightMulCLM Ψ).le_opNorm μ
  L_nonneg := norm_nonneg _
  c₀_nonneg := le_rfl

/-- **Non-vacuity of `kStep_singular_limit`**: for a linear closure with `Ψ Φ = 1` and a basis
containing the moments, all hypotheses hold and all solutions exist.
(arXiv 1804.04561, Section 4, an instance.) -/
theorem kStep_nonvacuous (D : Fin d → Matrix m m ℝ) (ξ : n → Vel d) {V : Matrix n r ℝ}
    {Φ : Matrix n q ℝ} {Ψ : Matrix q n ℝ} (hΦ : V * Vᵀ * Φ = Φ) (hΨ : Ψ * Φ = 1)
    (K₀ : Matrix m r ℝ) (τ : ℝ) :
    (∀ μ : Matrix m q ℝ, μ * Ψ * V * Vᵀ * Φ = μ) ∧
    (∃ m₀ : ℝ → Matrix m q ℝ, ODESolution (reducedField (rightProj V) (-transport D ξ)
      (Frobenius.rightMulCLM Φ) (fun μ => μ * Ψ)) m₀ 0 τ ∧ m₀ 0 = K₀ * Vᵀ * Φ) ∧
    ∀ ε : ℝ, ∃ K : ℝ → Matrix m r ℝ,
      ODESolution (MatrixKSL.kField V (bgkField D ξ (fun f => f * Φ * Ψ) ε)) K 0 τ ∧ K 0 = K₀ := by
  have : CompleteSpace (Matrix m q ℝ) := FiniteDimensional.complete ℝ _
  have : CompleteSpace (Matrix m r ℝ) := FiniteDimensional.complete ℝ _
  refine ⟨fun μ => ?_, ?_, fun ε => ?_⟩
  · have e : μ * Ψ * V * Vᵀ * Φ = μ * Ψ * (V * Vᵀ * Φ) := by simp only [Matrix.mul_assoc]
    rw [e, hΦ, Matrix.mul_assoc, hΨ, Matrix.mul_one]
  · set B : Matrix m q ℝ →L[ℝ] Matrix m q ℝ := (Frobenius.rightMulCLM Φ).comp ((rightProj V).comp
      ((-transport D ξ).comp ((rightProj V).comp (Frobenius.rightMulCLM Ψ)))) with hB
    obtain ⟨y, hy, hy0⟩ := exists_linear_solution B (K₀ * Vᵀ * Φ) 0 τ
    exact ⟨y, hy, hy0⟩
  · set Fc : Matrix m n ℝ →L[ℝ] Matrix m n ℝ := -transport D ξ +
      ε⁻¹ • (Frobenius.rightMulCLM (Φ * Ψ) - 1) with hFc
    set B : Matrix m r ℝ →L[ℝ] Matrix m r ℝ := (Frobenius.rightMulCLM V).comp
      (Fc.comp (Frobenius.rightMulCLM Vᵀ)) with hB
    obtain ⟨y, hy, hy0⟩ := exists_linear_solution B K₀ 0 τ
    refine ⟨y, ?_, hy0⟩
    have e : MatrixKSL.kField V (bgkField D ξ (fun f => f * Φ * Ψ) ε) = fun _ x => B x := by
      funext t x
      simp [MatrixKSL.kField, bgkField, hB, hFc, Matrix.mul_assoc, Matrix.add_mul, Matrix.smul_mul,
        Matrix.sub_mul]
    rw [e]
    exact hy

/-- **Non-vacuity of `lStep_singular_limit`**: for a linear closure with `Ψ Φ = 1`, all hypotheses
hold and all solutions exist.
(arXiv 1804.04561, Section 4, an instance.) -/
theorem lStep_nonvacuous (D : Fin d → Matrix m m ℝ) (ξ : n → Vel d) {X : Matrix m r ℝ}
    {Φ : Matrix n q ℝ} {Ψ : Matrix q n ℝ} (hΨ : Ψ * Φ = 1) (L₀ : Matrix n r ℝ) (τ : ℝ) :
    (∀ μ : Matrix m q ℝ, μ * Ψ * Φ = μ) ∧
    (∃ m₀ : ℝ → Matrix m q ℝ, ODESolution (reducedField (leftProj X) (-transport D ξ)
      (Frobenius.rightMulCLM Φ) (fun μ => μ * Ψ)) m₀ 0 τ ∧ m₀ 0 = X * L₀ᵀ * Φ) ∧
    ∀ ε : ℝ, ∃ Lf : ℝ → Matrix n r ℝ,
      ODESolution (MatrixKSL.lField X (bgkField D ξ (fun f => f * Φ * Ψ) ε)) Lf 0 τ ∧
        Lf 0 = L₀ := by
  have : CompleteSpace (Matrix m q ℝ) := FiniteDimensional.complete ℝ _
  have : CompleteSpace (Matrix n r ℝ) := FiniteDimensional.complete ℝ _
  refine ⟨fun μ => by rw [Matrix.mul_assoc, hΨ, Matrix.mul_one], ?_, fun ε => ?_⟩
  · set B : Matrix m q ℝ →L[ℝ] Matrix m q ℝ := (Frobenius.rightMulCLM Φ).comp ((leftProj X).comp
      ((-transport D ξ).comp ((leftProj X).comp (Frobenius.rightMulCLM Ψ)))) with hB
    obtain ⟨y, hy, hy0⟩ := exists_linear_solution B (X * L₀ᵀ * Φ) 0 τ
    exact ⟨y, hy, hy0⟩
  · set Fc : Matrix m n ℝ →L[ℝ] Matrix m n ℝ := -transport D ξ +
      ε⁻¹ • (Frobenius.rightMulCLM (Φ * Ψ) - 1) with hFc
    set B : Matrix n r ℝ →L[ℝ] Matrix n r ℝ := (Frobenius.rightMulCLM X).comp
      (Frobenius.transposeCLM.comp (Fc.comp ((Frobenius.leftMulCLM X).comp
        Frobenius.transposeCLM))) with hB
    obtain ⟨y, hy, hy0⟩ := exists_linear_solution B L₀ 0 τ
    refine ⟨y, ?_, hy0⟩
    have e : MatrixKSL.lField X (bgkField D ξ (fun f => f * Φ * Ψ) ε) = fun _ x => B x := by
      funext t x
      simp [MatrixKSL.lField, bgkField, hB, hFc, Matrix.mul_assoc, Matrix.add_mul, Matrix.smul_mul,
        Matrix.sub_mul]
    rw [e]
    exact hy

/-- **Non-vacuity of `sStep_diverges`**: for a linear closure the S-step has solutions from every
`S₀`, for every `ε`.
(arXiv 1804.04561, Section 4, an instance.) -/
theorem sStep_nonvacuous (D : Fin d → Matrix m m ℝ) (ξ : n → Vel d) (X : Matrix m r ℝ)
    (V : Matrix n r ℝ) (Φ : Matrix n q ℝ) (Ψ : Matrix q n ℝ) (S₀ : Matrix r r ℝ) (ε τ : ℝ) :
    ∃ S : ℝ → Matrix r r ℝ,
      ODESolution (MatrixKSL.sField X V (bgkField D ξ (fun f => f * Φ * Ψ) ε)) S 0 τ ∧
        S 0 = S₀ := by
  have : CompleteSpace (Matrix r r ℝ) := FiniteDimensional.complete ℝ _
  set Fc : Matrix m n ℝ →L[ℝ] Matrix m n ℝ := -transport D ξ +
    ε⁻¹ • (Frobenius.rightMulCLM (Φ * Ψ) - 1) with hFc
  set B : Matrix r r ℝ →L[ℝ] Matrix r r ℝ := -((Frobenius.rightMulCLM V).comp
    ((Frobenius.leftMulCLM Xᵀ).comp (Fc.comp ((Frobenius.rightMulCLM Vᵀ).comp
      (Frobenius.leftMulCLM X))))) with hB
  obtain ⟨y, hy, hy0⟩ := exists_linear_solution B S₀ 0 τ
  refine ⟨y, ?_, hy0⟩
  have e : MatrixKSL.sField X V (bgkField D ξ (fun f => f * Φ * Ψ) ε) = fun _ x => B x := by
    funext t x
    simp [MatrixKSL.sField, bgkField, hB, hFc, Matrix.mul_assoc, Matrix.add_mul, Matrix.smul_mul,
      Matrix.sub_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sub]
  rw [e]
  exact hy

/-- A nondegenerate instance of the data of `kStep_nonvacuous`: three velocities, rank two, one
moment, with an equilibrium that is not in the range of `V`. -/
example :
    let V : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; 0, 0]
    let Φ : Matrix (Fin 3) (Fin 1) ℝ := !![1; 0; 0]
    let Ψ : Matrix (Fin 1) (Fin 3) ℝ := !![1, 1, 1]
    Vᵀ * V = 1 ∧ V * Vᵀ * Φ = Φ ∧ Ψ * Φ = 1 := by
  intro V Φ Ψ
  have hV : Vᵀ * V = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [V, Matrix.mul_apply, Fin.sum_univ_succ]
  have hVΦ : Vᵀ * Φ = !![1; 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [V, Φ, Matrix.mul_apply, Fin.sum_univ_succ]
  refine ⟨hV, ?_, ?_⟩
  · rw [Matrix.mul_assoc, hVΦ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [V, Φ, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i
    fin_cases j
    simp [Φ, Ψ, Matrix.mul_apply, Fin.sum_univ_succ]

end Examples

/-! ### The moments in the core kinetic vocabulary -/

section KineticCore

variable {d : ℕ} {m n : Type*} [Fintype n]

/-- **The discrete momentum through the core moments**: the component `a` of the discrete momentum
`(ρ u) (f)_i = ∑_j w_j f_{ij} ξ_j` is the core quadrature moment `Kinetic.quadMoment` of `f` with
the weights `w` and the function `j ↦ (ξ_j)_a`. -/
theorem momentum_eq_quadMoment (w : n → ℝ) (ξ : n → Vel d) (f : Matrix m n ℝ) (i : m)
    (a : Fin d) :
    momentum w ξ f i a = Kinetic.quadMoment w (fun j => ξ j a) f i := by
  rw [Kinetic.quadMoment_apply, momentum, WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- One velocity `ξ = 3` with weight `2` and `f = 1`: the momentum is `6`. -/
example :
    momentum (d := 1) (fun _ : Fin 1 => (2 : ℝ)) (fun _ => EuclideanSpace.single 0 3)
      (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = 6 := by
  rw [momentum_eq_quadMoment]
  simp [Kinetic.quadMoment_apply]
  norm_num

/-- **Eq. (8) on a grid**: by the core lemma `HasSepRankLE.rank_le`, the samples of the truncated
Maxwellian in two dimensions on every grid of positions and velocities form a matrix of rank at
most `6`. -/
example {X p q : Type*} [Finite p] [Fintype q] (ρ : X → ℝ) (u : X → Vel 2) (xs : p → X)
    (vs : q → Vel 2) :
    (Matrix.of fun i j => maxwellianTrunc (ρ (xs i)) (u (xs i)) (vs j)).rank ≤ 6 :=
  (eq8_rank_le_two ρ u).rank_le xs vs

end KineticCore

/-- The local `density` of this file, replaced by the core `Kinetic.density` (the same definition:
`ρ (f)_i = ∑_j w_j f_{ij}`). -/
@[deprecated (since := "2026-11-10")] alias density := LeanDLRA.Kinetic.density

end LeanDLRA.Literature.P1804_04561
