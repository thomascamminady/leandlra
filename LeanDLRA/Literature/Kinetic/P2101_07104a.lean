import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.Matrix.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Novel.KineticAP

/-!
# Results of arXiv 2101.07104: Efficient DLR for Boltzmann–BGK near compressible Navier–Stokes

The paper (Einkemmer, Hu, Ying) has no numbered theorems: its results are the derivations and the
algorithm of Secs. 3, 4 and the formal analysis of Sec. 6. This module proves them for genuine
functions of `x, v ∈ ℝ^d`, integrals and derivatives, for `T = 1`, and for the fully discrete step
on matrices as in Sec. 6: the Maxwellian moments (1.3) and (4.14), (4.15) as Mathlib convolutions
(`integral_maxwellian`, `integral_coord_mul_maxwellian`, `integral_coord_mul_coord_mul_maxwellian`,
`moment_first_eq_convolution`, `moment_second_eq_convolution`, `integrable_moment_first`,
`integrable_moment_second`, `integral_lowRank`, `collision_invariants`); the equations (3.6), (4.4),
(4.5), (4.6), (4.7) (`bgk_iff_source`, `bgk_iff_source_isothermal`, `hasDerivAt_velocity`,
`transportM_eq`, `transportM_eq_calM`); the K-, L- and S-equations (4.8)–(4.13) (`kEquation`,
`lEquation`, `sEquation`, for any measures on `x`- and `v`-space, non-vacuous by
`isVelocityBasis_const`, `isSpaceBasis_const`); the explicit K-step (4.20) (`imex_iff_closedForm`,
`kStep_closedForm`, `closedForm_sub_mean`) and resolvent commutation (`imex_iff_resolvent`,
`imex_eq_resolvent`); the IMEX KSL step (`IsIMEXKSLStep`, equal to IMEX Euler for the three terms of
(3.7) by `kStep_iff_imex`, `sStep_iff_imex`, `lStep_iff_imex`, solvable by
`exists_isIMEXKSLStep`); and the low rank of the expansion (`rank_firstOrder_le`).

The main new statement is `IsIMEXKSLStep.ap_step_le`: `g = 1 + O(ε)`, which Sec. 6 takes for
granted, is proved at fixed time step, for every input and every rank, with an explicit constant,
provided `⟨V⟩ ≠ 0`.

Points where the printed paper is wrong, misprinted or silent (each checked in the PDF):
* Remark 4.2: for `T = 1` the Chapman–Enskog stress (formally, from (2.3) and (2.6)) is
  `∇u + (∇u)ᵀ`, not `σ(u)` of (2.10)
  (`chapmanEnskog_stress`, `transportM_euler`, `remark_4_2_false`); (2.9), and with it (2.12) and
  (4.22), rely on the energy equation, which the isothermal model does not have. The two stresses
  differ by `(2 / d) (∇ · u) I`, and the momentum equations by `(2 / d) ε ∇ (∇ · u)`.
* (4.19) is misprinted: it lacks a factor `Δt` (`printed_update_iff`). With it, (4.18)–(4.19)
  give `ρ¹ u¹ = ρ u + Δt I₂ + (Δt² I₁ / ρ) (I₂ - I₁ u)` (`forwardEuler_momentum`), so (6.1) holds
  for this update only up to an `O(Δt)` defect in the momentum. The scheme of Sec. 5.2 updates
  `(ρ, ρ u)` directly and has no such defect.
* The paper does not discuss solvability of the S-step: it can be singular for
  `ρ_min ≤ ε / Δt ≤ ρ_max`, and then no step exists
  (`isUnit_one_sub_stiffness`, `not_exists_imexKSLStep`).
* The step "`g = 1 + O(ε)` (the first equality implies so)" below (6.3) fails for `⟨V⟩ = 0`
  (`not_ap_of_mean_zero`); `ap_step_le` proves it for `⟨V⟩ ≠ 0`.

Not about the paper: `resolvent_sign` records that an internal planning note for this slice had
the wrong sign for the relaxation; the paper's signs agree with `imex_iff_resolvent`.

Not formalized: the cost claims and FFT interpolation; the derivation of (4.2), (4.3) by
differentiating under the integral (only `collision_invariants`); the Chapman–Enskog expansion as
a limit theorem; `T ≠ 1`; the identification of the `O(ε)` term in (6.2)–(6.4), where the paper
ignores the low-rank projection error; the spatial discretizations of Sec. 5; and the KSL step with
QR in `L²`, which is why the AP theorem is on matrices. The time derivatives in
`chapmanEnskog_stress` are the Euler equations in non-conservative form.
-/

open Set Filter Topology Finset MeasureTheory
open scoped RealInnerProductSpace Matrix Convolution

namespace LeanDLRA.Literature.P2101_07104

section Maxwellian

/-- Position and velocity space `ℝ^d` (with `d = d_x = d_v`, as `v · ∇ₓ` requires). -/
abbrev Vel (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-- The kernel `v ↦ exp (-v² / 2)` of the convolutions in Sec. 4.1 of the paper. -/
noncomputable def gaussKernel (v : Vel d) : ℝ := Real.exp (-‖v‖ ^ 2 / 2)

/-- The isothermal Maxwellian (4.1) (`T = 1`), for given density and bulk velocity. -/
noncomputable def maxwellian (ρ : ℝ) (u v : Vel d) : ℝ :=
  ρ / (2 * Real.pi) ^ ((d : ℝ) / 2) * Real.exp (-‖v - u‖ ^ 2 / 2)

/-- `w, a ↦ a • w`: the bilinear map convolving an `F`-valued function with a scalar kernel. -/
noncomputable def scalarKernel (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    F →L[ℝ] ℝ →L[ℝ] F :=
  (ContinuousLinearMap.lsmul ℝ ℝ).flip

lemma maxwellian_eq (ρ : ℝ) (u v : Vel d) :
    maxwellian ρ u v = ρ / (2 * Real.pi) ^ ((d : ℝ) / 2) * gaussKernel (u - v) := by
  rw [maxwellian, gaussKernel, norm_sub_rev]

lemma pi_pow_pos : 0 < (2 * Real.pi) ^ ((d : ℝ) / 2) := by
  have := Real.pi_pos
  positivity

lemma gaussKernel_pos (v : Vel d) : 0 < gaussKernel v := Real.exp_pos _

lemma maxwellian_pos {ρ : ℝ} (hρ : 0 < ρ) (u v : Vel d) : 0 < maxwellian ρ u v := by
  have := pi_pow_pos (d := d)
  rw [maxwellian]
  have := Real.exp_pos (-‖v - u‖ ^ 2 / 2)
  positivity

/-- **Moments are Gaussian convolutions** (arXiv 2101.07104, Sec. 4.1), for any `F`-valued weight
`ψ`: `⟨ψ M⟩ᵥ = ρ (2π)^{-d/2} (ψ ∗ exp(-v²/2))(u)`, with Mathlib's convolution. -/
theorem integral_maxwellian_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ℝ) (u : Vel d) (ψ : Vel d → F) :
    ∫ v, maxwellian ρ u v • ψ v =
      (ρ / (2 * Real.pi) ^ ((d : ℝ) / 2)) • (ψ ⋆[scalarKernel F, volume] gaussKernel) u := by
  rw [convolution_def, ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [scalarKernel, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply]
  rw [maxwellian_eq, smul_smul]

/-- **(4.14) of arXiv 2101.07104**: `⟨v V M⟩ᵥ = ρ (2π)^{-d/2} g¹(u)`, with
`g¹ = (v ↦ v V) ∗ (v ↦ exp (-v² / 2))`, for `T = 1`, at a point `x` with `ρ = ρ(x)`, `u = u(x)`. No
hypothesis on `V`; the integrals exist for `V ∈ L²` by `integrable_moment_first`. The FFT and the
cost claim are not formalized. -/
theorem moment_first_eq_convolution (ρ : ℝ) (u : Vel d) (V : Vel d → ℝ) :
    ∫ v, V v • maxwellian ρ u v • v =
      (ρ / (2 * Real.pi) ^ ((d : ℝ) / 2)) •
        ((fun v => V v • v) ⋆[scalarKernel (Vel d), volume] gaussKernel) u := by
  rw [← integral_maxwellian_smul]
  exact integral_congr_ae (Eventually.of_forall fun v => smul_comm _ _ _)

/-- The tensor `v ⊗ v`. -/
def tensorSq (v : Vel d) : Fin d → Fin d → ℝ := fun a b => v a * v b

/-- **(4.15) of arXiv 2101.07104**: `⟨v ⊗ v V M⟩ᵥ = ρ (2π)^{-d/2} g²(u)`, with
`g² = (v ↦ (v ⊗ v) V) ∗ (v ↦ exp (-v² / 2))`, for `T = 1`. The tensor `v ⊗ v` has values in
`Fin d → Fin d → ℝ`. -/
theorem moment_second_eq_convolution (ρ : ℝ) (u : Vel d) (V : Vel d → ℝ) :
    ∫ v, V v • maxwellian ρ u v • tensorSq v =
      (ρ / (2 * Real.pi) ^ ((d : ℝ) / 2)) •
        ((fun v => V v • tensorSq v) ⋆[scalarKernel (Fin d → Fin d → ℝ), volume]
          gaussKernel) u := by
  rw [← integral_maxwellian_smul]
  exact integral_congr_ae (Eventually.of_forall fun v => smul_comm _ _ _)

lemma integral_gaussKernel : ∫ v : Vel d, gaussKernel v = (2 * Real.pi) ^ ((d : ℝ) / 2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Vel d) (b := 1 / 2) (by norm_num)
  have h2 : Real.pi / (1 / 2) = 2 * Real.pi := by ring
  rw [h2, finrank_euclideanSpace_fin] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [gaussKernel]
  congr 1
  ring

lemma integrable_exp_neg_mul_sq_norm {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : Vel d => Real.exp (-b * ‖v‖ ^ 2)) := by
  have h : 0 < ∫ v : Vel d, Real.exp (-b * ‖v‖ ^ 2) := by
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
    have := Real.pi_pos
    positivity
  exact Integrable.of_integral_ne_zero h.ne'


lemma continuous_gaussKernel : Continuous (gaussKernel : Vel d → ℝ) := by
  unfold gaussKernel
  fun_prop

lemma integrable_gaussKernel : Integrable (gaussKernel : Vel d → ℝ) := by
  have h := integrable_exp_neg_mul_sq_norm (d := d) (b := 1 / 2) (by norm_num)
  refine h.congr (Eventually.of_forall fun v => ?_)
  simp only [gaussKernel]
  congr 1
  ring

lemma sq_mul_gaussKernel_le (v : Vel d) :
    ‖v‖ ^ 2 * gaussKernel v ≤ 4 * Real.exp (-(1 / 4) * ‖v‖ ^ 2) := by
  have h1 : ‖v‖ ^ 2 / 4 + 1 ≤ Real.exp (‖v‖ ^ 2 / 4) := Real.add_one_le_exp _
  have h2 : gaussKernel v = (Real.exp (‖v‖ ^ 2 / 4))⁻¹ * Real.exp (-(1 / 4) * ‖v‖ ^ 2) := by
    rw [gaussKernel, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have h3 : ‖v‖ ^ 2 ≤ 4 * Real.exp (‖v‖ ^ 2 / 4) := by nlinarith [sq_nonneg ‖v‖]
  have h4 := Real.exp_pos (‖v‖ ^ 2 / 4)
  have h5 := Real.exp_pos (-(1 / 4) * ‖v‖ ^ 2)
  rw [h2, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ h5.le
  rw [← div_eq_mul_inv, div_le_iff₀ h4]
  exact h3

lemma integrable_sq_mul_gaussKernel : Integrable (fun v : Vel d => ‖v‖ ^ 2 * gaussKernel v) := by
  have h := (integrable_exp_neg_mul_sq_norm (d := d) (b := 1 / 4) (by norm_num)).const_mul 4
  refine h.mono' (by have := continuous_gaussKernel (d := d); fun_prop) ?_
  refine Eventually.of_forall fun v => ?_
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (gaussKernel_pos v).le)]
  exact sq_mul_gaussKernel_le v

lemma abs_coord_le_norm (v : Vel d) (a : Fin d) : |v a| ≤ ‖v‖ := by
  simpa using PiLp.norm_apply_le v a

lemma continuous_apply' (a : Fin d) : Continuous (fun v : Vel d => v a) := by fun_prop

lemma integrable_coord_mul_gaussKernel (a : Fin d) :
    Integrable (fun v : Vel d => v a * gaussKernel v) := by
  have h := (integrable_sq_mul_gaussKernel (d := d)).add integrable_gaussKernel
  refine h.mono' (by have := continuous_gaussKernel (d := d); fun_prop) ?_
  refine Eventually.of_forall fun v => ?_
  have h1 := abs_coord_le_norm v a
  have h2 := gaussKernel_pos v
  have h3 : |v a| ≤ ‖v‖ ^ 2 + 1 := by nlinarith [sq_nonneg (‖v‖ - 1), norm_nonneg v]
  simp only [Pi.add_apply]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg h2.le]
  nlinarith

lemma integrable_coord_mul_coord_mul_gaussKernel (a b : Fin d) :
    Integrable (fun v : Vel d => v a * v b * gaussKernel v) := by
  refine (integrable_sq_mul_gaussKernel (d := d)).mono'
    (by have := continuous_gaussKernel (d := d); fun_prop) ?_
  refine Eventually.of_forall fun v => ?_
  have h1 := abs_coord_le_norm v a
  have h2 := abs_coord_le_norm v b
  have h3 := gaussKernel_pos v
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_of_nonneg h3.le]
  refine mul_le_mul_of_nonneg_right ?_ h3.le
  rw [sq]
  exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)

lemma gaussKernel_neg (v : Vel d) : gaussKernel (-v) = gaussKernel v := by
  simp [gaussKernel]

lemma integral_coord_mul_gaussKernel (a : Fin d) :
    ∫ v : Vel d, v a * gaussKernel v = 0 := by
  have h := integral_neg_eq_self (fun v : Vel d => v a * gaussKernel v) volume
  have h2 : ∫ v : Vel d, (-v) a * gaussKernel (-v) = -∫ v : Vel d, v a * gaussKernel v := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp [gaussKernel_neg]
  rw [h2] at h
  linarith

lemma hasFDerivAt_gaussKernel (x : Vel d) :
    HasFDerivAt gaussKernel (gaussKernel x • (-(innerSL ℝ x))) x := by
  have h1 := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h2 := (h1.const_mul (-(1 / 2) : ℝ)).exp
  refine (h2.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
  · ext w
    have h3 : -(1 / 2 : ℝ) * ‖x‖ ^ 2 = -‖x‖ ^ 2 / 2 := by ring
    simp only [gaussKernel, h3]
    simp
  · simp only [gaussKernel]
    congr 1
    ring

lemma integral_coord_mul_coord_mul_gaussKernel (a b : Fin d) :
    ∫ v : Vel d, v a * v b * gaussKernel v =
      if a = b then (2 * Real.pi) ^ ((d : ℝ) / 2) else 0 := by
  set w : Vel d := EuclideanSpace.single a 1 with hw
  have hG : ∀ x : Vel d, fderiv ℝ gaussKernel x w = -(x a * gaussKernel x) := fun x => by
    rw [(hasFDerivAt_gaussKernel x).fderiv]
    simp [hw, EuclideanSpace.inner_single_right, mul_comm]
  have hf : ∀ x : Vel d, fderiv ℝ (fun v : Vel d => v b) x w = if a = b then 1 else 0 := fun x => by
    have h := (EuclideanSpace.proj b : Vel d →L[ℝ] ℝ).hasFDerivAt (x := x)
    have h2 : fderiv ℝ (fun v : Vel d => v b) x = (EuclideanSpace.proj b : Vel d →L[ℝ] ℝ) :=
      h.fderiv
    rw [h2]
    simp [hw, PiLp.single_apply, eq_comm]
  have hdiff : ∀ x : Vel d, DifferentiableAt ℝ (fun v : Vel d => v b) x := fun x =>
    (EuclideanSpace.proj b : Vel d →L[ℝ] ℝ).differentiableAt
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Vel d)))
    (f := fun v : Vel d => v b) (g := gaussKernel) (v := w) (by
      simp only [hf]
      split_ifs
      · simpa using integrable_gaussKernel
      · simp) (by
      simp only [hG]
      have := (integrable_coord_mul_coord_mul_gaussKernel (d := d) a b).neg
      refine this.congr (Eventually.of_forall fun v => ?_)
      simp only [Pi.neg_apply]
      ring) (integrable_coord_mul_gaussKernel b) (fun x _ => hdiff x)
      (fun x _ => (hasFDerivAt_gaussKernel x).differentiableAt)
  simp only [hf, hG] at h
  have h3 : ∫ v : Vel d, v a * v b * gaussKernel v =
      -∫ v : Vel d, v b * -(v a * gaussKernel v) := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only
    ring
  rw [h3, h, neg_neg]
  split_ifs
  · simpa using integral_gaussKernel
  · simp

/-- Change of variables `v = w + u` in a Maxwellian-weighted integral. -/
lemma integral_mul_maxwellian (φ : Vel d → ℝ) (ρ : ℝ) (u : Vel d) :
    ∫ v, φ v * maxwellian ρ u v =
      ρ / (2 * Real.pi) ^ ((d : ℝ) / 2) * ∫ w, φ (w + u) * gaussKernel w := by
  rw [← integral_sub_right_eq_self (fun w => φ (w + u) * gaussKernel w) u, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [sub_add_cancel, maxwellian, gaussKernel]
  ring

/-- `⟨M⟩ᵥ = ρ`: (1.3) of arXiv 2101.07104 for the Maxwellian (4.1). -/
theorem integral_maxwellian (ρ : ℝ) (u : Vel d) : ∫ v, maxwellian ρ u v = ρ := by
  have h := integral_mul_maxwellian (fun _ => (1 : ℝ)) ρ u
  simp only [one_mul] at h
  rw [h, integral_gaussKernel]
  have := pi_pow_pos (d := d)
  field_simp

/-- `⟨v M⟩ᵥ = ρ u`: (1.3) of arXiv 2101.07104 for the Maxwellian (4.1). -/
theorem integral_coord_mul_maxwellian (ρ : ℝ) (u : Vel d) (a : Fin d) :
    ∫ v, v a * maxwellian ρ u v = ρ * u a := by
  rw [integral_mul_maxwellian]
  have h : ∫ w : Vel d, (w + u) a * gaussKernel w =
      (2 * Real.pi) ^ ((d : ℝ) / 2) * u a := by
    have h1 : ∀ w : Vel d, (w + u) a * gaussKernel w =
        w a * gaussKernel w + u a * gaussKernel w := fun w => by
      simp only [PiLp.add_apply]
      ring
    simp only [h1]
    rw [integral_add (integrable_coord_mul_gaussKernel a) (integrable_gaussKernel.const_mul _),
      integral_coord_mul_gaussKernel, integral_const_mul, integral_gaussKernel]
    ring
  rw [h]
  have := pi_pow_pos (d := d)
  field_simp

/-- `⟨v ⊗ v M⟩ᵥ = ρ (u ⊗ u + I)`: for `g = 1` the fluxes (4.2), (4.3) of arXiv 2101.07104 are the
isothermal Euler fluxes, the left-hand side of (4.22). -/
theorem integral_coord_mul_coord_mul_maxwellian (ρ : ℝ) (u : Vel d) (a b : Fin d) :
    ∫ v, v a * v b * maxwellian ρ u v = ρ * (u a * u b + if a = b then 1 else 0) := by
  rw [integral_mul_maxwellian]
  have hZ := pi_pow_pos (d := d)
  have h : ∫ w : Vel d, (w + u) a * (w + u) b * gaussKernel w =
      (2 * Real.pi) ^ ((d : ℝ) / 2) * (u a * u b + if a = b then 1 else 0) := by
    have h1 : ∀ w : Vel d, (w + u) a * (w + u) b * gaussKernel w =
        w a * w b * gaussKernel w + (u b * (w a * gaussKernel w) + u a * (w b * gaussKernel w)) +
          u a * u b * gaussKernel w := fun w => by
      simp only [PiLp.add_apply]
      ring
    simp only [h1]
    have I2 := (integrable_coord_mul_gaussKernel (d := d) a).const_mul (u b)
    have I3 := (integrable_coord_mul_gaussKernel (d := d) b).const_mul (u a)
    have I1 := integrable_coord_mul_coord_mul_gaussKernel (d := d) a b
    have I4 := (integrable_gaussKernel (d := d)).const_mul (u a * u b)
    rw [integral_add (I1.fun_add (I2.fun_add I3)) I4, integral_add I1 (I2.fun_add I3),
      integral_add I2 I3, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_coord_mul_gaussKernel, integral_coord_mul_gaussKernel,
      integral_coord_mul_coord_mul_gaussKernel, integral_gaussKernel]
    split_ifs <;> ring
  rw [h]
  field_simp

lemma sq_le_exp (t : ℝ) : t ^ 2 ≤ 4 * Real.exp (t ^ 2 / 4) := by
  have h1 : t ^ 2 / 4 + 1 ≤ Real.exp (t ^ 2 / 4) := Real.add_one_le_exp _
  nlinarith [sq_nonneg t]

/-- The envelope `exp (-|v - u|² / 4)` of all the weights of (4.14), (4.15). -/
lemma memLp_envelope (u : Vel d) :
    MemLp (fun v : Vel d => Real.exp (-‖v - u‖ ^ 2 / 4)) 2 volume := by
  have hc : Continuous (fun v : Vel d => Real.exp (-‖v - u‖ ^ 2 / 4)) := by fun_prop
  refine (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).2 ?_
  refine ((integrable_gaussKernel (d := d)).comp_sub_right u).congr
    (Eventually.of_forall fun v => ?_)
  simp only [gaussKernel]
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma integrable_envelope (u : Vel d) :
    Integrable (fun v : Vel d => Real.exp (-‖v - u‖ ^ 2 / 4)) := by
  have h := (integrable_exp_neg_mul_sq_norm (d := d) (b := 1 / 4) (by norm_num)).comp_sub_right u
  refine h.congr (Eventually.of_forall fun v => ?_)
  simp only
  congr 1
  ring

/-- `|v_a v_b| e^{-|v-u|²/2} ≤ (8 + 2 |u|²) e^{-|v-u|²/4}`. -/
lemma second_weight_le (u v : Vel d) (a b : Fin d) :
    |v a * v b| * Real.exp (-‖v - u‖ ^ 2 / 2) ≤
      (8 + 2 * ‖u‖ ^ 2) * Real.exp (-‖v - u‖ ^ 2 / 4) := by
  have h1 : |v a * v b| ≤ ‖v‖ ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul (abs_coord_le_norm v a) (abs_coord_le_norm v b) (abs_nonneg _) (norm_nonneg _)
  have h2 : ‖v‖ ≤ ‖v - u‖ + ‖u‖ := by
    have := norm_add_le (v - u) u
    rwa [sub_add_cancel] at this
  have h3 : ‖v‖ ^ 2 ≤ 2 * ‖v - u‖ ^ 2 + 2 * ‖u‖ ^ 2 := by
    have h4 := norm_nonneg v
    have h5 := norm_nonneg (v - u)
    have h6 := norm_nonneg u
    nlinarith [sq_nonneg (‖v - u‖ - ‖u‖)]
  have h4 := sq_le_exp ‖v - u‖
  have h5 : 1 ≤ Real.exp (‖v - u‖ ^ 2 / 4) := Real.one_le_exp (by positivity)
  have h6 : |v a * v b| ≤ (8 + 2 * ‖u‖ ^ 2) * Real.exp (‖v - u‖ ^ 2 / 4) := by
    nlinarith [sq_nonneg ‖u‖]
  have h7 : Real.exp (-‖v - u‖ ^ 2 / 2) =
      (Real.exp (‖v - u‖ ^ 2 / 4))⁻¹ * Real.exp (-‖v - u‖ ^ 2 / 4) := by
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have h8 := Real.exp_pos (‖v - u‖ ^ 2 / 4)
  rw [h7, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  rw [← div_eq_mul_inv, div_le_iff₀ h8]
  exact h6

lemma first_weight_le (u v : Vel d) (a : Fin d) :
    |v a| * Real.exp (-‖v - u‖ ^ 2 / 2) ≤
      (9 + 2 * ‖u‖ ^ 2) * Real.exp (-‖v - u‖ ^ 2 / 4) := by
  have h1 : ‖v‖ ≤ ‖v - u‖ + ‖u‖ := by
    have := norm_add_le (v - u) u
    rwa [sub_add_cancel] at this
  have h3 : |v a| ≤ 1 + 2 * ‖v - u‖ ^ 2 + 2 * ‖u‖ ^ 2 := by
    have h4 := abs_coord_le_norm v a
    have h5 := norm_nonneg (v - u)
    have h6 := norm_nonneg u
    have h7 := norm_nonneg v
    nlinarith [sq_nonneg (‖v - u‖ - ‖u‖), sq_nonneg (‖v‖ - 1)]
  have h4 := sq_le_exp ‖v - u‖
  have h5 : 1 ≤ Real.exp (‖v - u‖ ^ 2 / 4) := Real.one_le_exp (by positivity)
  have h6 : |v a| ≤ (9 + 2 * ‖u‖ ^ 2) * Real.exp (‖v - u‖ ^ 2 / 4) := by
    nlinarith [sq_nonneg ‖u‖]
  have h7 : Real.exp (-‖v - u‖ ^ 2 / 2) =
      (Real.exp (‖v - u‖ ^ 2 / 4))⁻¹ * Real.exp (-‖v - u‖ ^ 2 / 4) := by
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have h8 := Real.exp_pos (‖v - u‖ ^ 2 / 4)
  rw [h7, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  rw [← div_eq_mul_inv, div_le_iff₀ h8]
  exact h6

lemma exp_le_envelope (u v : Vel d) :
    Real.exp (-‖v - u‖ ^ 2 / 2) ≤ Real.exp (-‖v - u‖ ^ 2 / 4) :=
  Real.exp_le_exp.2 (by nlinarith [sq_nonneg ‖v - u‖])

/-- An `L²` function times a weight with Gaussian envelope is integrable. -/
lemma integrable_mul_of_envelope {V w : Vel d → ℝ} (hV : MemLp V 2 volume) (hw : Continuous w)
    {u : Vel d} {C : ℝ} (hC : ∀ v, |w v| ≤ C * Real.exp (-‖v - u‖ ^ 2 / 4)) :
    Integrable (fun v => V v * w v) := by
  have h1 : MemLp w 2 volume := by
    have h2 := (memLp_envelope u).const_mul C
    refine h2.of_le_mul (c := 1) hw.aestronglyMeasurable (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, one_mul]
    exact (hC v).trans (le_abs_self _ |>.trans (by simp [norm_mul]))
  exact hV.integrable_mul h1

lemma continuous_maxwellian (ρ : ℝ) (u : Vel d) : Continuous (maxwellian ρ u) := by
  unfold maxwellian
  fun_prop

lemma abs_first_moment_le (ρ : ℝ) (u v : Vel d) (a : Fin d) :
    |v a * maxwellian ρ u v| ≤ |ρ / (2 * Real.pi) ^ ((d : ℝ) / 2)| * (9 + 2 * ‖u‖ ^ 2) *
      Real.exp (-‖v - u‖ ^ 2 / 4) := by
  rw [maxwellian, abs_mul, abs_mul (_ / _), Real.abs_exp]
  have := mul_le_mul_of_nonneg_left (first_weight_le u v a)
    (abs_nonneg (ρ / (2 * Real.pi) ^ ((d : ℝ) / 2)))
  calc _ = |ρ / (2 * Real.pi) ^ ((d : ℝ) / 2)| * (|v a| * Real.exp (-‖v - u‖ ^ 2 / 2)) := by ring
    _ ≤ _ := this
    _ = _ := by ring

lemma abs_second_moment_le (ρ : ℝ) (u v : Vel d) (a b : Fin d) :
    |v a * v b * maxwellian ρ u v| ≤ |ρ / (2 * Real.pi) ^ ((d : ℝ) / 2)| * (8 + 2 * ‖u‖ ^ 2) *
      Real.exp (-‖v - u‖ ^ 2 / 4) := by
  rw [maxwellian, abs_mul, abs_mul (_ / _), Real.abs_exp]
  have := mul_le_mul_of_nonneg_left (second_weight_le u v a b)
    (abs_nonneg (ρ / (2 * Real.pi) ^ ((d : ℝ) / 2)))
  calc _ = |ρ / (2 * Real.pi) ^ ((d : ℝ) / 2)| * (|v a * v b| * Real.exp (-‖v - u‖ ^ 2 / 2)) := by
        ring
    _ ≤ _ := this
    _ = _ := by ring

/-- `⟨v_a V M⟩ᵥ` exists for `V ∈ L²`: the integrals (4.14) of arXiv 2101.07104 are not junk. -/
theorem integrable_moment_first {V : Vel d → ℝ} (hV : MemLp V 2 volume) (ρ : ℝ) (u : Vel d)
    (a : Fin d) : Integrable (fun v => V v * (v a * maxwellian ρ u v)) :=
  integrable_mul_of_envelope hV (u := u)
    (by have := continuous_maxwellian ρ u; fun_prop) (abs_first_moment_le ρ u · a)

/-- `⟨v_a v_b V M⟩ᵥ` exists for `V ∈ L²`: the integrals (4.15) of arXiv 2101.07104 are not junk. -/
theorem integrable_moment_second {V : Vel d → ℝ} (hV : MemLp V 2 volume) (ρ : ℝ) (u : Vel d)
    (a b : Fin d) : Integrable (fun v => V v * (v a * v b * maxwellian ρ u v)) :=
  integrable_mul_of_envelope hV (u := u)
    (by have := continuous_maxwellian ρ u; fun_prop) (abs_second_moment_le ρ u · a b)

/-- **The fluxes of (4.2), (4.3), (4.16), (4.17) of arXiv 2101.07104 for a low-rank `g`.** For
`g = ∑ᵢⱼ Xᵢ Sᵢⱼ Vⱼ` at a point `x`, a Maxwellian-weighted moment with weight `w` is the sum
`∑ᵢⱼ Xᵢ Sᵢⱼ ⟨w Vⱼ⟩ᵥ`; `w` is `v_a M` or `v_a v_b M`, for which integrability is
`integrable_moment_first`, `integrable_moment_second`. -/
theorem integral_lowRank {r : ℕ} {V : Fin r → Vel d → ℝ} {w : Vel d → ℝ}
    (hw : ∀ j, Integrable (fun v => V j v * w v)) (X : Fin r → ℝ) (S : Fin r → Fin r → ℝ) :
    ∫ v, (∑ i, ∑ j, X i * S i j * V j v) * w v = ∑ i, ∑ j, X i * S i j * ∫ v, V j v * w v := by
  have h1 : ∀ i ∈ (Finset.univ : Finset (Fin r)), ∀ j ∈ (Finset.univ : Finset (Fin r)),
      Integrable (fun v => X i * S i j * (V j v * w v)) := fun i _ j _ =>
    (hw j).const_mul _
  have h2 : ∀ i ∈ (Finset.univ : Finset (Fin r)),
      Integrable (fun v => ∑ j, X i * S i j * (V j v * w v)) := fun i hi =>
    integrable_finsetSum _ (h1 i hi)
  have h3 : ∀ v, (∑ i, ∑ j, X i * S i j * V j v) * w v =
      ∑ i, ∑ j, X i * S i j * (V j v * w v) := fun v => by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [h3]
  rw [integral_finsetSum _ h2]
  simp only [integral_finsetSum _ (h1 _ (Finset.mem_univ _)), integral_const_mul]

/-- **Collision invariants** behind the moment equations (2.4), (3.5) of arXiv 2101.07104: if `f`
has density `ρ` and momentum `ρ u`, then `⟨M - f⟩ᵥ = 0` and `⟨v_a (M - f)⟩ᵥ = 0`. This is the only
property of the BGK collision term used to derive (4.2), (4.3); the derivation
itself (differentiating under the integral) is not formalized. -/
theorem collision_invariants {f : Vel d → ℝ} {ρ : ℝ} {u : Vel d} (hf : Integrable f)
    (hf' : ∀ a, Integrable (fun v => v a * f v)) (hρ : ∫ v, f v = ρ)
    (hm : ∀ a, ∫ v, v a * f v = ρ * u a) :
    ∫ v, (maxwellian ρ u v - f v) = 0 ∧ ∀ a, ∫ v, v a * (maxwellian ρ u v - f v) = 0 := by
  have hM : Integrable (fun v => maxwellian ρ u v) := by
    refine (((integrable_gaussKernel (d := d)).comp_sub_right u).const_mul
      (ρ / (2 * Real.pi) ^ ((d : ℝ) / 2))).congr (Eventually.of_forall fun v => ?_)
    simp only [maxwellian, gaussKernel]
  have hMa : ∀ a, Integrable (fun v => v a * maxwellian ρ u v) := fun a => by
    refine ((integrable_envelope u).const_mul
      (|ρ / (2 * Real.pi) ^ ((d : ℝ) / 2)| * (9 + 2 * ‖u‖ ^ 2))).mono'
      (by have := continuous_maxwellian ρ u; fun_prop) (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs]
    exact abs_first_moment_le ρ u v a
  refine ⟨?_, fun a => ?_⟩
  · rw [integral_sub hM hf, integral_maxwellian, hρ, sub_self]
  · simp only [mul_sub]
    rw [integral_sub (hMa a) (hf' a), integral_coord_mul_maxwellian, hm, sub_self]

end Maxwellian

variable {d : ℕ}

section Transport

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Chain rule for the Maxwellian along differentiable moments. -/
lemma hasFDerivAt_maxwellian {r : Z → ℝ} {w : Z → Vel d} {r' : Z →L[ℝ] ℝ} {w' : Z →L[ℝ] Vel d}
    {z : Z} (hr : HasFDerivAt r r' z) (hw : HasFDerivAt w w' z) (hr0 : r z ≠ 0) (v : Vel d) :
    HasFDerivAt (fun y => maxwellian (r y) (w y) v)
      (maxwellian (r z) (w z) v • ((r z)⁻¹ • r' + (innerSL ℝ (v - w z)).comp w')) z := by
  have h1 : HasFDerivAt (fun y => v - w y) (-w') z := hw.const_sub v
  have h2 := (h1.norm_sq.const_mul (-(1 / 2) : ℝ)).exp
  have h3 := (hr.mul_const ((2 * Real.pi) ^ ((d : ℝ) / 2))⁻¹).mul h2
  refine (h3.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · ext q
    have hZ := pi_pow_pos (d := d)
    have h4 : -(1 / 2 : ℝ) * ‖v - w z‖ ^ 2 = -‖v - w z‖ ^ 2 / 2 := by ring
    simp only [maxwellian, h4, add_apply, smul_apply, smul_eq_mul,
      ContinuousLinearMap.comp_apply, neg_apply, innerSL_apply_apply, inner_neg_right]
    simp only [nsmul_eq_mul]
    field_simp
    push_cast
    ring
  · simp only [maxwellian]
    have h4 : -‖v - w y‖ ^ 2 / 2 = -(1 / 2 : ℝ) * ‖v - w y‖ ^ 2 := by ring
    rw [h4, div_eq_mul_inv]
    rfl

end Transport

section Equations

/-- The operator `𝓜 = (∂ₜ M + v · ∇ₓ M) / M` of (3.6), (4.6), for the Maxwellian (4.1) of the
moments `ρ`, `u`. -/
noncomputable def transportM (ρ : ℝ → Vel d → ℝ) (u : ℝ → Vel d → Vel d) (t : ℝ) (x v : Vel d) :
    ℝ :=
  (deriv (fun s => maxwellian (ρ s x) (u s x) v) t +
      fderiv ℝ (fun y => maxwellian (ρ t y) (u t y) v) x v) / maxwellian (ρ t x) (u t x) v

/-- **First line of (4.6) of arXiv 2101.07104.** -/
theorem transportM_eq {ρ : ℝ → Vel d → ℝ} {u : ℝ → Vel d → Vel d} {t : ℝ} {x : Vel d} {ρt : ℝ}
    {ut : Vel d} {ρx : Vel d →L[ℝ] ℝ} {ux : Vel d →L[ℝ] Vel d} (hρ : 0 < ρ t x)
    (hρt : HasDerivAt (fun s => ρ s x) ρt t) (hut : HasDerivAt (fun s => u s x) ut t)
    (hρx : HasFDerivAt (ρ t) ρx x) (hux : HasFDerivAt (u t) ux x) (v : Vel d) :
    transportM ρ u t x v = (ρt + ρx v) / ρ t x + ⟪v - u t x, ut + ux v⟫ := by
  have h1 := (hasFDerivAt_maxwellian hρt.hasFDerivAt hut.hasFDerivAt hρ.ne' v).hasDerivAt
  have h2 := hasFDerivAt_maxwellian hρx hux hρ.ne' v
  have hM := maxwellian_pos hρ (u t x) v
  rw [transportM, h1.deriv, h2.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul, inner_add_right]
  field_simp
  ring

/-- **(4.4) of arXiv 2101.07104**: `∂ₜ u = (I₂ - I₁ u) / ρ`, from `∂ₜ ρ = I₁`, `∂ₜ (ρ u) = I₂`.
Differentiability of `u` is derived. -/
theorem hasDerivAt_velocity {ρ : ℝ → Vel d → ℝ} {u : ℝ → Vel d → Vel d} {t : ℝ} {x : Vel d}
    {I₁ : ℝ} {I₂ : Vel d} (hρ : ρ t x ≠ 0) (h₁ : HasDerivAt (fun s => ρ s x) I₁ t)
    (h₂ : HasDerivAt (fun s => ρ s x • u s x) I₂ t) :
    HasDerivAt (fun s => u s x) ((ρ t x)⁻¹ • (I₂ - I₁ • u t x)) t := by
  have h3 := (h₁.fun_inv hρ).fun_smul h₂
  have hev : ∀ᶠ s in 𝓝 t, ρ s x ≠ 0 := h₁.continuousAt.eventually_ne hρ
  refine (h3.congr_deriv ?_).congr_of_eventuallyEq (hev.mono fun s hs => ?_)
  · have h4 : -I₁ / ρ t x ^ 2 * ρ t x = -((ρ t x)⁻¹ * I₁) := by field_simp
    rw [smul_sub, smul_smul, smul_smul, h4, neg_smul, sub_eq_add_neg]
  · simp only [smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- The operator `𝓜 = M₁ + v · M₂ + (v ⊗ v) : M₃` in the form (4.6). -/
noncomputable def calM (m₁ : ℝ) (m₂ : Vel d) (m₃ : Fin d → Fin d → ℝ) (v : Vel d) : ℝ :=
  m₁ + ⟪v, m₂⟫ + ∑ a, ∑ b, v a * v b * m₃ a b

/-- `M₁` of (4.7). -/
noncomputable def coefM₁ (ρ I₁ : ℝ) (I₂ u : Vel d) : ℝ := (I₁ - ⟪u, I₂ - I₁ • u⟫) / ρ

/-- `M₂` of (4.7), with `∇ₓ ρ = gρ`, `∇ₓ (u²) = gu`. -/
noncomputable def coefM₂ (ρ I₁ : ℝ) (I₂ u gρ gu : Vel d) : Vel d :=
  ρ⁻¹ • (gρ + I₂ - I₁ • u) - (1 / 2 : ℝ) • gu

/-- `M₃ = ∇ₓ u` of (4.7), with `(∇ₓ u)_{ab} = ∂_{x_b} u_a` as in the paper (Sec. 2). -/
noncomputable def coefM₃ (ux : Vel d →L[ℝ] Vel d) (a b : Fin d) : ℝ :=
  ux (EuclideanSpace.single b 1) a

lemma sum_coefM₃ (ux : Vel d →L[ℝ] Vel d) (v : Vel d) :
    ∑ a, ∑ b, v a * v b * coefM₃ ux a b = ⟪v, ux v⟫ := by
  have h1 : ux v = ∑ b, v b • ux (EuclideanSpace.single b 1) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
    simp [map_sum]
  rw [h1, inner_sum]
  simp only [inner_smul_right, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, coefM₃,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

/-- **(4.6)–(4.7) of arXiv 2101.07104**: under the moment equations `∂ₜ ρ = I₁`, `∂ₜ (ρ u) = I₂`,
`𝓜 = (∂ₜ M + v · ∇ₓ M) / M` for the Maxwellian (4.1) is the quadratic polynomial
`M₁ + v · M₂ + (v ⊗ v) : M₃` in `v`, with the coefficients of (4.7). All time derivatives of `u`
are derived, not assumed. -/
theorem transportM_eq_calM {ρ : ℝ → Vel d → ℝ} {u : ℝ → Vel d → Vel d} {t : ℝ} {x : Vel d}
    {I₁ : ℝ} {I₂ : Vel d} (hρ : 0 < ρ t x) (h₁ : HasDerivAt (fun s => ρ s x) I₁ t)
    (h₂ : HasDerivAt (fun s => ρ s x • u s x) I₂ t) (hρx : DifferentiableAt ℝ (ρ t) x)
    (hux : DifferentiableAt ℝ (u t) x) (v : Vel d) :
    transportM ρ u t x v =
      calM (coefM₁ (ρ t x) I₁ I₂ (u t x))
        (coefM₂ (ρ t x) I₁ I₂ (u t x) (gradient (ρ t) x) (gradient (fun y => ‖u t y‖ ^ 2) x))
        (coefM₃ (fderiv ℝ (u t) x)) v := by
  have hut := hasDerivAt_velocity hρ.ne' h₁ h₂
  rw [transportM_eq hρ h₁ hut hρx.hasFDerivAt hux.hasFDerivAt v, calM, sum_coefM₃, coefM₁, coefM₂]
  have key1 : ⟪v, gradient (ρ t) x⟫ = fderiv ℝ (ρ t) x v := by
    rw [real_inner_comm]
    exact inner_gradient_left
  have key2 : ⟪v, gradient (fun y => ‖u t y‖ ^ 2) x⟫ = 2 * ⟪u t x, fderiv ℝ (u t) x v⟫ := by
    rw [real_inner_comm, inner_gradient_left, hux.hasFDerivAt.norm_sq.fderiv]
    simp
  simp only [inner_sub_left, inner_add_right, inner_sub_right, inner_smul_right, key1, key2]
  have hρ' := hρ.ne'
  field_simp
  ring

/-- **(3.6) of arXiv 2101.07104** (derivation): with `f = M g` and `M ≠ 0` at the point, the BGK
equation (1.1) at `(t, x, v)` is equivalent to `∂ₜ g = -v · ∇ₓ g - (∂ₜ M + v · ∇ₓ M) / M g +
(ν / ε) (1 - g)`.  Here `v` is frozen and `f`, `M`, `g` are functions of `(t, x)`. -/
theorem bgk_iff_source {f M g : ℝ → Vel d → ℝ} {t : ℝ} {x v : Vel d} {ν ε : ℝ}
    (hf : ∀ s y, f s y = M s y * g s y)
    (hMt : DifferentiableAt ℝ (fun s => M s x) t) (hMx : DifferentiableAt ℝ (M t) x)
    (hgt : DifferentiableAt ℝ (fun s => g s x) t) (hgx : DifferentiableAt ℝ (g t) x)
    (hM : M t x ≠ 0) :
    deriv (fun s => f s x) t + fderiv ℝ (f t) x v = ν / ε * (M t x - f t x) ↔
      deriv (fun s => g s x) t = -fderiv ℝ (g t) x v -
        (deriv (fun s => M s x) t + fderiv ℝ (M t) x v) / M t x * g t x +
          ν / ε * (1 - g t x) := by
  have h1 : (fun s => f s x) = fun s => M s x * g s x := funext fun s => hf s x
  have h2 : f t = fun y => M t y * g t y := funext fun y => hf t y
  have h3 : deriv (fun s => f s x) t = deriv (fun s => M s x) t * g t x +
      M t x * deriv (fun s => g s x) t := by
    rw [h1]
    exact (hMt.hasDerivAt.mul hgt.hasDerivAt).deriv
  have h4 : fderiv ℝ (f t) x v = M t x * fderiv ℝ (g t) x v + g t x * fderiv ℝ (M t) x v := by
    rw [h2]
    have := (hMx.hasFDerivAt.mul hgx.hasFDerivAt).fderiv
    change fderiv ℝ (M t * g t) x v = _
    rw [this]
    simp
  rw [h3, h4, hf t x]
  constructor
  · intro h
    apply mul_left_cancel₀ hM
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp
    ring

/-- **(4.5) of arXiv 2101.07104**: the equation for `g = f / M` in the isothermal case `T = 1`,
`ν = ρ`, under the moment equations `∂ₜ ρ = I₁`, `∂ₜ (ρ u) = I₂`: the BGK equation (1.1) for
`f = M g` is equivalent to `∂ₜ g = -v · ∇ₓ g - 𝓜 g + (ρ / ε) (1 - g)` with `𝓜` as in (4.6). -/
theorem bgk_iff_source_isothermal {ρ : ℝ → Vel d → ℝ} {u : ℝ → Vel d → Vel d}
    {f g : ℝ → Vel d → ℝ} {t : ℝ} {x v : Vel d} {I₁ ε : ℝ} {I₂ : Vel d} (hρ : 0 < ρ t x)
    (h₁ : HasDerivAt (fun s => ρ s x) I₁ t) (h₂ : HasDerivAt (fun s => ρ s x • u s x) I₂ t)
    (hρx : DifferentiableAt ℝ (ρ t) x) (hux : DifferentiableAt ℝ (u t) x)
    (hf : ∀ s y, f s y = maxwellian (ρ s y) (u s y) v * g s y)
    (hgt : DifferentiableAt ℝ (fun s => g s x) t) (hgx : DifferentiableAt ℝ (g t) x) :
    deriv (fun s => f s x) t + fderiv ℝ (f t) x v =
        ρ t x / ε * (maxwellian (ρ t x) (u t x) v - f t x) ↔
      deriv (fun s => g s x) t = -fderiv ℝ (g t) x v -
        calM (coefM₁ (ρ t x) I₁ I₂ (u t x))
          (coefM₂ (ρ t x) I₁ I₂ (u t x) (gradient (ρ t) x) (gradient (fun y => ‖u t y‖ ^ 2) x))
          (coefM₃ (fderiv ℝ (u t) x)) v * g t x + ρ t x / ε * (1 - g t x) := by
  have hut := hasDerivAt_velocity hρ.ne' h₁ h₂
  have hMt := (hasFDerivAt_maxwellian h₁.hasFDerivAt hut.hasFDerivAt hρ.ne' v).hasDerivAt
  have hMx := hasFDerivAt_maxwellian hρx.hasFDerivAt hux.hasFDerivAt hρ.ne' v
  rw [← transportM_eq_calM hρ h₁ h₂ hρx hux v]
  exact bgk_iff_source (M := fun s y => maxwellian (ρ s y) (u s y) v) hf
    hMt.differentiableAt hMx.differentiableAt hgt hgx (maxwellian_pos hρ _ _).ne'

end Equations

section ChapmanEnskog

lemma sq_sq_mul_gaussKernel_le (v : Vel d) :
    ‖v‖ ^ 4 * gaussKernel v ≤ 64 * Real.exp (-(1 / 4) * ‖v‖ ^ 2) := by
  have h1 : ‖v‖ ^ 2 / 8 + 1 ≤ Real.exp (‖v‖ ^ 2 / 8) := Real.add_one_le_exp _
  have h2 : ‖v‖ ^ 2 ≤ 8 * Real.exp (‖v‖ ^ 2 / 8) := by nlinarith [sq_nonneg ‖v‖]
  have h3 : ‖v‖ ^ 4 ≤ 64 * Real.exp (‖v‖ ^ 2 / 4) := by
    have h4 : Real.exp (‖v‖ ^ 2 / 4) = Real.exp (‖v‖ ^ 2 / 8) * Real.exp (‖v‖ ^ 2 / 8) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h5 : ‖v‖ ^ 4 = ‖v‖ ^ 2 * ‖v‖ ^ 2 := by ring
    rw [h4, h5]
    nlinarith [sq_nonneg ‖v‖, Real.exp_pos (‖v‖ ^ 2 / 8)]
  have h6 : gaussKernel v = (Real.exp (‖v‖ ^ 2 / 4))⁻¹ * Real.exp (-(1 / 4) * ‖v‖ ^ 2) := by
    rw [gaussKernel, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have h7 := Real.exp_pos (‖v‖ ^ 2 / 4)
  rw [h6, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  rw [← div_eq_mul_inv, div_le_iff₀ h7]
  exact h3

lemma integrable_sq_sq_mul_gaussKernel :
    Integrable (fun v : Vel d => ‖v‖ ^ 4 * gaussKernel v) := by
  have h := (integrable_exp_neg_mul_sq_norm (d := d) (b := 1 / 4) (by norm_num)).const_mul 64
  refine h.mono' (by have := continuous_gaussKernel (d := d); fun_prop) ?_
  refine Eventually.of_forall fun v => ?_
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (gaussKernel_pos v).le)]
  exact sq_sq_mul_gaussKernel_le v

lemma integrable_third_moment (j a b : Fin d) :
    Integrable (fun v : Vel d => v j * v a * v b * gaussKernel v) := by
  have h := (integrable_sq_mul_gaussKernel (d := d)).add integrable_sq_sq_mul_gaussKernel
  refine h.mono' (by have := continuous_gaussKernel (d := d); fun_prop) ?_
  refine Eventually.of_forall fun v => ?_
  have h1 := abs_coord_le_norm v j
  have h2 := abs_coord_le_norm v a
  have h3 := abs_coord_le_norm v b
  have h4 := gaussKernel_pos v
  have h5 : |v j| * |v a| * |v b| ≤ ‖v‖ ^ 2 + ‖v‖ ^ 4 := by
    have h6 : |v j| * |v a| ≤ ‖v‖ * ‖v‖ := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    have h7 : |v j| * |v a| * |v b| ≤ ‖v‖ * ‖v‖ * ‖v‖ :=
      mul_le_mul h6 h3 (abs_nonneg _) (by positivity)
    have h8 := norm_nonneg v
    nlinarith [sq_nonneg (‖v‖ ^ 2 - ‖v‖), sq_nonneg ‖v‖, mul_nonneg h8 h8]
  simp only [Pi.add_apply]
  rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_of_nonneg h4.le, ← add_mul]
  exact mul_le_mul_of_nonneg_right h5 h4.le

lemma integrable_fourth_moment (i j a b : Fin d) :
    Integrable (fun v : Vel d => v i * v j * v a * v b * gaussKernel v) := by
  refine (integrable_sq_sq_mul_gaussKernel (d := d)).mono'
    (by have := continuous_gaussKernel (d := d); fun_prop) ?_
  refine Eventually.of_forall fun v => ?_
  have h1 := abs_coord_le_norm v i
  have h2 := abs_coord_le_norm v j
  have h3 := abs_coord_le_norm v a
  have h4 := abs_coord_le_norm v b
  have h5 := gaussKernel_pos v
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_eq_abs, Real.norm_of_nonneg h5.le]
  refine mul_le_mul_of_nonneg_right ?_ h5.le
  have h6 : |v i| * |v j| ≤ ‖v‖ * ‖v‖ := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
  have h7 : |v i| * |v j| * |v a| ≤ ‖v‖ * ‖v‖ * ‖v‖ :=
    mul_le_mul h6 h3 (abs_nonneg _) (by positivity)
  calc |v i| * |v j| * |v a| * |v b| ≤ ‖v‖ * ‖v‖ * ‖v‖ * ‖v‖ :=
        mul_le_mul h7 h4 (abs_nonneg _) (by positivity)
    _ = ‖v‖ ^ 4 := by ring

lemma integral_second_moment (a b : Fin d) :
    ∫ v : Vel d, v a * v b * gaussKernel v =
      (if a = b then 1 else 0) * (2 * Real.pi) ^ ((d : ℝ) / 2) := by
  rw [integral_coord_mul_coord_mul_gaussKernel]
  split_ifs <;> simp

/-- Isserlis' formula for the fourth moments of the Gaussian, for `chapmanEnskog_stress`; the
"direct integration" of (2.12) of arXiv 2101.07104. -/
theorem integral_fourth_moment (i j a b : Fin d) :
    ∫ v : Vel d, v i * v j * v a * v b * gaussKernel v =
      (2 * Real.pi) ^ ((d : ℝ) / 2) * ((if i = j then 1 else 0) * (if a = b then 1 else 0) +
        (if i = a then 1 else 0) * (if j = b then 1 else 0) +
        (if i = b then 1 else 0) * (if j = a then 1 else 0)) := by
  set w : Vel d := EuclideanSpace.single i 1 with hw
  have hG : ∀ x : Vel d, fderiv ℝ gaussKernel x w = -(x i * gaussKernel x) := fun x => by
    rw [(hasFDerivAt_gaussKernel x).fderiv]
    simp [hw, EuclideanSpace.inner_single_right, mul_comm]
  have hp : ∀ (c : Fin d) (x : Vel d),
      HasFDerivAt (fun v : Vel d => v c) (EuclideanSpace.proj c : Vel d →L[ℝ] ℝ) x := fun c x =>
    (EuclideanSpace.proj c : Vel d →L[ℝ] ℝ).hasFDerivAt
  have hf3 : ∀ x : Vel d, HasFDerivAt (fun v : Vel d => v j * v a * v b)
      ((x j * x a) • (EuclideanSpace.proj b : Vel d →L[ℝ] ℝ) +
        x b • (x j • (EuclideanSpace.proj a : Vel d →L[ℝ] ℝ) +
          x a • (EuclideanSpace.proj j : Vel d →L[ℝ] ℝ))) x := fun x =>
    ((hp j x).mul (hp a x)).mul (hp b x)
  have hf : ∀ x : Vel d, fderiv ℝ (fun v : Vel d => v j * v a * v b) x w =
      (if i = j then 1 else 0) * (x a * x b) + (if i = a then 1 else 0) * (x j * x b) +
        (if i = b then 1 else 0) * (x j * x a) := fun x => by
    have hs : ∀ c, (EuclideanSpace.proj c : Vel d →L[ℝ] ℝ) w = if i = c then 1 else 0 := fun c => by
      simp [hw, PiLp.single_apply, eq_comm]
    rw [(hf3 x).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, hs]
    ring
  have hI : ∀ (c e : Fin d) (t : ℝ), Integrable fun x : Vel d => t * (x c * x e * gaussKernel x) :=
    fun c e t => (integrable_coord_mul_coord_mul_gaussKernel c e).const_mul t
  have hrw : ∀ x : Vel d, fderiv ℝ (fun v : Vel d => v j * v a * v b) x w * gaussKernel x =
      (if i = j then 1 else 0) * (x a * x b * gaussKernel x) +
        (if i = a then 1 else 0) * (x j * x b * gaussKernel x) +
        (if i = b then 1 else 0) * (x j * x a * gaussKernel x) := fun x => by
    rw [hf]
    ring
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Vel d)))
    (f := fun v : Vel d => v j * v a * v b) (g := gaussKernel) (v := w) (by
      simp only [hrw]
      exact ((hI a b _).fun_add (hI j b _)).fun_add (hI j a _)) (by
      simp only [hG]
      refine (integrable_fourth_moment i j a b).neg.congr (Eventually.of_forall fun v => ?_)
      simp only [Pi.neg_apply]
      ring) (integrable_third_moment j a b) (fun x _ => (hf3 x).differentiableAt)
      (fun x _ => (hasFDerivAt_gaussKernel x).differentiableAt)
  simp only [hrw, hG] at h
  have h3 : ∫ v : Vel d, v i * v j * v a * v b * gaussKernel v =
      -∫ v : Vel d, v j * v a * v b * -(v i * gaussKernel v) := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only
    ring
  rw [h3, h, neg_neg, integral_add ((hI a b _).fun_add (hI j b _)) (hI j a _),
    integral_add (hI a b _) (hI j b _), integral_const_mul, integral_const_mul, integral_const_mul,
    integral_second_moment, integral_second_moment, integral_second_moment]
  ring

lemma sum_delta (A : Fin d → Fin d → ℝ) (i j : Fin d) :
    ∑ a, ∑ b, A a b * ((if i = a then 1 else 0) * (if j = b then 1 else 0) +
      (if i = b then 1 else 0) * (if j = a then 1 else 0)) = A i j + A j i := by
  simp [mul_add, Finset.sum_add_distrib, mul_ite, Finset.sum_ite_eq]

/-- The Gaussian integral behind the Chapman–Enskog stress (arXiv 2101.07104, (2.12) for `T = 1`):
`⟨c_i c_j ((c ⊗ c - I) : A)⟩ = (2 π)^{d/2} (A_{ij} + A_{ji})`. -/
theorem integral_stress_gaussKernel (A : Fin d → Fin d → ℝ) (i j : Fin d) :
    ∫ c : Vel d, c i * c j * (∑ a, ∑ b, (c a * c b - if a = b then 1 else 0) * A a b) *
        gaussKernel c = (2 * Real.pi) ^ ((d : ℝ) / 2) * (A i j + A j i) := by
  have hb : ∀ a ∈ (Finset.univ : Finset (Fin d)), ∀ b ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun c : Vel d => A a b * (c i * c j * c a * c b * gaussKernel c -
        (if a = b then 1 else 0) * (c i * c j * gaussKernel c))) := fun a _ b _ =>
    ((integrable_fourth_moment i j a b).sub'
      ((integrable_coord_mul_coord_mul_gaussKernel i j).const_mul _)).const_mul _
  have ha : ∀ a ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun c : Vel d => ∑ b, A a b * (c i * c j * c a * c b * gaussKernel c -
        (if a = b then 1 else 0) * (c i * c j * gaussKernel c))) := fun a _ =>
    integrable_finsetSum _ fun b _ => hb a (Finset.mem_univ _) b (Finset.mem_univ _)
  have heq : ∀ c : Vel d, c i * c j * (∑ a, ∑ b, (c a * c b - if a = b then 1 else 0) * A a b) *
      gaussKernel c = ∑ a, ∑ b, A a b * (c i * c j * c a * c b * gaussKernel c -
        (if a = b then 1 else 0) * (c i * c j * gaussKernel c)) := fun c => by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  simp only [heq]
  rw [integral_finsetSum _ ha]
  simp only [integral_finsetSum _ (hb _ (Finset.mem_univ _)), integral_const_mul]
  have hin : ∀ a b : Fin d, ∫ c : Vel d, (c i * c j * c a * c b * gaussKernel c -
      (if a = b then 1 else 0) * (c i * c j * gaussKernel c)) =
      (2 * Real.pi) ^ ((d : ℝ) / 2) *
        ((if i = a then 1 else 0) * (if j = b then 1 else 0) +
          (if i = b then 1 else 0) * (if j = a then 1 else 0)) := fun a b => by
    rw [integral_sub (integrable_fourth_moment i j a b)
      ((integrable_coord_mul_coord_mul_gaussKernel i j).const_mul _), integral_const_mul,
      integral_fourth_moment, integral_second_moment]
    ring
  simp only [hin, mul_left_comm (A _ _) ((2 * Real.pi) ^ ((d : ℝ) / 2)), ← Finset.mul_sum]
  rw [sum_delta]

/-- `(∂ₜ M + v · ∇ₓ M) / M` on the isothermal Euler manifold: `𝓜 = ((v - u) ⊗ (v - u) - I) : ∇ₓ u`.
This replaces (2.9) of arXiv 2101.07104 in the case `T = 1`: the term `|v - u|² / d` of (2.9) comes
from the Euler energy equation, which the isothermal model does not have. The hypotheses `hρt`,
`hut` are the isothermal Euler equations (4.22), `ε = 0`, in non-conservative form, as used in
Sec. 2 of the paper to replace time derivatives by spatial ones. -/
theorem transportM_euler {ρ : ℝ → Vel d → ℝ} {u : ℝ → Vel d → Vel d} {t : ℝ} {x : Vel d}
    (hρ : 0 < ρ t x) (hρx : DifferentiableAt ℝ (ρ t) x) (hux : DifferentiableAt ℝ (u t) x)
    (hρt : HasDerivAt (fun s => ρ s x)
      (-fderiv ℝ (ρ t) x (u t x) - ρ t x * ∑ a, coefM₃ (fderiv ℝ (u t) x) a a) t)
    (hut : HasDerivAt (fun s => u s x)
      (-fderiv ℝ (u t) x (u t x) - (ρ t x)⁻¹ • gradient (ρ t) x) t) (v : Vel d) :
    transportM ρ u t x v = ∑ a, ∑ b,
      ((v - u t x) a * (v - u t x) b - if a = b then 1 else 0) * coefM₃ (fderiv ℝ (u t) x) a b := by
  rw [transportM_eq hρ hρt hut hρx.hasFDerivAt hux.hasFDerivAt v]
  set c := v - u t x with hc
  set ux := fderiv ℝ (u t) x with hu
  set ρx := fderiv ℝ (ρ t) x with hr
  have h1 : ∑ a, ∑ b, (c a * c b - if a = b then 1 else 0) * coefM₃ ux a b =
      ⟪c, ux c⟫ - ∑ a, coefM₃ ux a a := by
    rw [← sum_coefM₃, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  have h2 : ⟪c, gradient (ρ t) x⟫ = ρx c := by
    rw [real_inner_comm]
    exact inner_gradient_left
  have h3 : ρx v = ρx c + ρx (u t x) := by
    rw [hc, map_sub]
    ring
  have h4 : ux v = ux c + ux (u t x) := by
    rw [hc, map_sub]
    abel
  rw [h1, h3, h4]
  have h5 : -ux (u t x) - (ρ t x)⁻¹ • gradient (ρ t) x + (ux c + ux (u t x)) =
      ux c - (ρ t x)⁻¹ • gradient (ρ t) x := by abel
  rw [h5, inner_sub_right, inner_smul_right, h2]
  have := hρ.ne'
  field_simp
  ring

/-- **The Chapman–Enskog stress of the isothermal model, (2.6) with (2.3)**: with
`f₁ = -(∂ₜ M + v · ∇ₓ M) / ρ` on the isothermal Euler manifold,
`P₁ = -⟨(v - u) ⊗ (v - u) f₁⟩ᵥ = ∇ₓ u + (∇ₓ u)ᵀ`.

This contradicts Remark 4.2 of arXiv 2101.07104, see `remark_4_2_false`. -/
theorem chapmanEnskog_stress {ρ : ℝ → Vel d → ℝ} {u : ℝ → Vel d → Vel d} {t : ℝ} {x : Vel d}
    (hρ : 0 < ρ t x) (hρx : DifferentiableAt ℝ (ρ t) x) (hux : DifferentiableAt ℝ (u t) x)
    (hρt : HasDerivAt (fun s => ρ s x)
      (-fderiv ℝ (ρ t) x (u t x) - ρ t x * ∑ a, coefM₃ (fderiv ℝ (u t) x) a a) t)
    (hut : HasDerivAt (fun s => u s x)
      (-fderiv ℝ (u t) x (u t x) - (ρ t x)⁻¹ • gradient (ρ t) x) t) (i j : Fin d) :
    -∫ v, (v - u t x) i * (v - u t x) j *
        (-(transportM ρ u t x v * maxwellian (ρ t x) (u t x) v / ρ t x)) =
      coefM₃ (fderiv ℝ (u t) x) i j + coefM₃ (fderiv ℝ (u t) x) j i := by
  set A := coefM₃ (fderiv ℝ (u t) x) with hA
  have hZ := pi_pow_pos (d := d)
  have h1 : ∀ v, (v - u t x) i * (v - u t x) j *
      (-(transportM ρ u t x v * maxwellian (ρ t x) (u t x) v / ρ t x)) =
      -(1 / ρ t x) * ((v - u t x) i * (v - u t x) j *
        (∑ a, ∑ b, ((v - u t x) a * (v - u t x) b - if a = b then 1 else 0) * A a b) *
          maxwellian (ρ t x) (u t x) v) := fun v => by
    rw [transportM_euler hρ hρx hux hρt hut v]
    ring
  simp only [h1]
  rw [integral_const_mul, integral_mul_maxwellian]
  simp only [add_sub_cancel_right]
  rw [integral_stress_gaussKernel]
  have := hρ.ne'
  field_simp

/-- The stress `σ(u) = ∇u + (∇u)ᵀ - (2 / d) (∇ · u) I` of (2.10), for `∇u = A`. -/
noncomputable def sigmaStress (A : Fin d → Fin d → ℝ) (a b : Fin d) : ℝ :=
  A a b + A b a - 2 / d * (∑ c, A c c) * if a = b then 1 else 0

/-- `∇u + (∇u)ᵀ = σ(u)`, with `σ` from (2.10) of arXiv 2101.07104, if and only if `∇ · u = 0`. -/
theorem forall_eq_sigmaStress_iff (hd : 0 < d) (A : Fin d → Fin d → ℝ) :
    (∀ a b, A a b + A b a = sigmaStress A a b) ↔ ∑ c, A c c = 0 := by
  have hd' : (d : ℝ) ≠ 0 := by positivity
  constructor
  · intro h
    have h1 := h ⟨0, hd⟩ ⟨0, hd⟩
    simp only [sigmaStress, ↓reduceIte, mul_one] at h1
    have h2 : 2 / (d : ℝ) * ∑ c, A c c = 0 := by linarith
    have h3 : (2 : ℝ) / d ≠ 0 := by positivity
    exact (mul_eq_zero.1 h2).resolve_left h3
  · intro h a b
    simp [sigmaStress, h]

/-- **Remark 4.2 of arXiv 2101.07104 is false.** It states that for `T = 1` the fluid limit is
(4.22), with viscous stress `σ(u) = ∇u + (∇u)ᵀ - (2 / d) (∇ · u) I` of (2.10), so that
`P₁ = σ(u)` in (2.7). For the isothermal model (4.1), with `𝓜` as in (4.6), `P₁ = ∇u + (∇u)ᵀ`
(`chapmanEnskog_stress`), which differs from `σ(u)` by `(2 / d) (∇ · u) I`, a bulk viscosity
(`d = 1`: `σ(u) = 0`, whereas `P₁ = 2 ∂ₓ u`). The two agree only if `∇ · u = 0`.

The witness is the exact solution `ρ = (1 + s)^{-d}`, `u = y / (1 + s)` of isothermal Euler, at
`s = 0`, with `P₁ = 2 I`, `σ(u) = 0`. (A witness for the difference of the divergences, the terms
in the momentum equation, would be any flow with `∇ (∇ · u) ≠ 0`.) -/
theorem remark_4_2_false (hd : 0 < d) (x : Vel d) :
    ∃ (ρ : ℝ → Vel d → ℝ) (u : ℝ → Vel d → Vel d),
      0 < ρ 0 x ∧ DifferentiableAt ℝ (ρ 0) x ∧ DifferentiableAt ℝ (u 0) x ∧
      HasDerivAt (fun s => ρ s x)
        (-fderiv ℝ (ρ 0) x (u 0 x) - ρ 0 x * ∑ a, coefM₃ (fderiv ℝ (u 0) x) a a) 0 ∧
      HasDerivAt (fun s => u s x)
        (-fderiv ℝ (u 0) x (u 0 x) - (ρ 0 x)⁻¹ • gradient (ρ 0) x) 0 ∧
      ∃ i j, coefM₃ (fderiv ℝ (u 0) x) i j + coefM₃ (fderiv ℝ (u 0) x) j i ≠
        sigmaStress (coefM₃ (fderiv ℝ (u 0) x)) i j := by
  have hd' : (d : ℝ) ≠ 0 := by positivity
  set ρ : ℝ → Vel d → ℝ := fun s _ => ((1 + s) ^ d)⁻¹ with hρ
  set u : ℝ → Vel d → Vel d := fun s y => (1 + s)⁻¹ • y with hu
  have e1 : ρ 0 = fun _ => 1 := by
    funext y
    simp [hρ]
  have e2 : u 0 = id := by
    funext y
    simp [hu]
  have hx1 : ρ 0 x = 1 := congrFun e1 x
  have hx2 : u 0 x = x := congrFun e2 x
  have hA : coefM₃ (fderiv ℝ (u 0) x) = fun a b => if a = b then 1 else 0 := by
    rw [e2]
    funext a b
    simp only [coefM₃]
    rw [fderiv_id]
    simp [PiLp.single_apply]
  have hf1 : fderiv ℝ (ρ 0) x = 0 := by
    rw [e1]
    simp
  have hg1 : gradient (ρ 0) x = 0 := by
    rw [e1]
    simp [gradient]
  have hT : ∑ a, coefM₃ (fderiv ℝ (u 0) x) a a = d := by
    rw [hA]
    simp
  have hf2 : fderiv ℝ (u 0) x = ContinuousLinearMap.id ℝ (Vel d) := by
    rw [e2]
    exact fderiv_id
  refine ⟨ρ, u, by rw [hx1]; norm_num, by rw [e1]; exact differentiableAt_const _,
    by rw [e2]; exact differentiableAt_id, ?_, ?_, ⟨0, hd⟩, ⟨0, hd⟩, ?_⟩
  · rw [hf1, hT, hx1]
    have h1 : HasDerivAt (fun s : ℝ => (1 + s) ^ d) (d : ℝ) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).const_add 1).fun_pow d
      simpa using this
    have h2 := h1.fun_inv (by simp)
    convert h2 using 1
    simp
  · rw [hg1, hf2, hx2]
    have h1 : HasDerivAt (fun s : ℝ => (1 + s)⁻¹) (-1) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).const_add 1).fun_inv (by simp)
      simpa using this
    have h2 := h1.smul_const x
    convert h2 using 1
    simp
  · rw [hA]
    have h3 : sigmaStress (d := d) (fun a b => if a = b then 1 else 0) ⟨0, hd⟩ ⟨0, hd⟩ = 0 := by
      simp only [sigmaStress, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      field_simp
      ring
    rw [h3]
    simp only [↓reduceIte]
    norm_num

end ChapmanEnskog

section Substeps

variable {r : ℕ} {μ ν : Measure (Vel d)}

lemma inner_eq_sum (y v : Vel d) : ⟪y, v⟫ = ∑ a, y a * v a := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- The coefficient `c¹_{jl} = ⟨v V_j V_l⟩ᵥ` of the K-step. -/
noncomputable def c1 (μ : Measure (Vel d)) (V : Fin r → Vel d → ℝ) (j l : Fin r) : Vel d :=
  WithLp.toLp 2 fun a => ∫ v, v a * V j v * V l v ∂μ

/-- The coefficient `c*_{jl} = ⟨v ⊗ v V_j V_l⟩ᵥ` of the K-step. -/
noncomputable def cStar (μ : Measure (Vel d)) (V : Fin r → Vel d → ℝ) (j l : Fin r)
    (a b : Fin d) : ℝ :=
  ∫ v, v a * v b * V j v * V l v ∂μ

/-- `V̄_j = ⟨V_j⟩ᵥ`. -/
noncomputable def vBar (μ : Measure (Vel d)) (V : Fin r → Vel d → ℝ) (j : Fin r) : ℝ :=
  ∫ v, V j v ∂μ

/-- `c²_{jl} = δ_{jl} m₁ + c¹_{jl} · m₂ + c*_{jl} : m₃`. With `(m₁, m₂, m₃) = (M₁, M₂, M₃)(x)` this
is `c²_{jl}` of the K-step, and with `(m₁, m₂, m₃) = (d*_{ik}, d**_{ik}, d***_{ik})` it is
`d²_{ik;jl}` of the S-step. -/
noncomputable def c2 (μ : Measure (Vel d)) (V : Fin r → Vel d → ℝ) (m₁ : ℝ) (m₂ : Vel d)
    (m₃ : Fin d → Fin d → ℝ) (j l : Fin r) : ℝ :=
  (if j = l then m₁ else 0) + ⟪c1 μ V j l, m₂⟫ + ∑ a, ∑ b, cStar μ V j l a b * m₃ a b

/-- The right-hand side `h = -v · ∇ₓ g - 𝓜 g + (ρ / ε) (1 - g)` of (4.5), for a function `g` of
`(x, v)` and coefficient functions `ρ, m₁, m₂, m₃` of `x`. -/
noncomputable def source (ρ : Vel d → ℝ) (ε : ℝ) (m₁ : Vel d → ℝ) (m₂ : Vel d → Vel d)
    (m₃ : Vel d → Fin d → Fin d → ℝ) (g : Vel d → Vel d → ℝ) (x v : Vel d) : ℝ :=
  -fderiv ℝ (fun y => g y v) x v - calM (m₁ x) (m₂ x) (m₃ x) v * g x v + ρ x / ε * (1 - g x v)

/-- The velocity basis: orthonormal in `L²(μ)`, with the integrals of the K-step finite. -/
structure IsVelocityBasis (μ : Measure (Vel d)) (V : Fin r → Vel d → ℝ) : Prop where
  integrable : ∀ j, Integrable (V j) μ
  integrable_mul : ∀ j l, Integrable (fun v => V j v * V l v) μ
  integrable_first : ∀ j l a, Integrable (fun v => v a * V j v * V l v) μ
  integrable_second : ∀ j l a b, Integrable (fun v => v a * v b * V j v * V l v) μ
  orthonormal : ∀ j l, ∫ v, V j v * V l v ∂μ = if j = l then 1 else 0

namespace IsVelocityBasis

variable {V : Fin r → Vel d → ℝ}

lemma integrable_inner (hV : IsVelocityBasis μ V) (y : Vel d) (j l : Fin r) :
    Integrable (fun v => ⟪y, v⟫ * (V j v * V l v)) μ := by
  simp only [inner_eq_sum, Finset.sum_mul]
  refine integrable_finsetSum _ fun a _ => ?_
  refine ((hV.integrable_first j l a).const_mul (y a)).congr (Eventually.of_forall fun v => ?_)
  simp only
  ring

lemma integral_inner (hV : IsVelocityBasis μ V) (y : Vel d) (j l : Fin r) :
    ∫ v, ⟪y, v⟫ * (V j v * V l v) ∂μ = ⟪y, c1 μ V j l⟫ := by
  have hint : ∀ a ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun v => y a * v a * (V j v * V l v)) μ := fun a _ => by
    refine ((hV.integrable_first j l a).const_mul (y a)).congr (Eventually.of_forall fun v => ?_)
    simp only
    ring
  simp only [inner_eq_sum, Finset.sum_mul]
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : ∀ v, y a * v a * (V j v * V l v) = y a * (v a * V j v * V l v) := fun v => by ring
  simp only [h]
  rw [integral_const_mul]
  rfl

lemma integrable_calM (hV : IsVelocityBasis μ V) (m₁ : ℝ) (m₂ : Vel d) (m₃ : Fin d → Fin d → ℝ)
    (j l : Fin r) : Integrable (fun v => calM m₁ m₂ m₃ v * (V j v * V l v)) μ := by
  have h1 := (hV.integrable_mul j l).const_mul m₁
  have h2 := (hV.integrable_inner m₂ j l)
  have h3 : Integrable (fun v => ∑ a, ∑ b, m₃ a b * (v a * v b * V j v * V l v)) μ :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      (hV.integrable_second j l a b).const_mul _
  refine (h1.add (h2.add h3)).congr (Eventually.of_forall fun v => ?_)
  simp only [Pi.add_apply, calM, real_inner_comm m₂ v]
  simp only [add_mul, Finset.sum_mul, add_assoc, add_right_inj]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **(4.9) of arXiv 2101.07104**: `⟨V_j V_l 𝓜⟩ᵥ = δ_{jl} M₁ + c¹_{jl} · M₂ + c*_{jl} : M₃`. -/
theorem integral_calM (hV : IsVelocityBasis μ V) (m₁ : ℝ) (m₂ : Vel d) (m₃ : Fin d → Fin d → ℝ)
    (j l : Fin r) :
    ∫ v, calM m₁ m₂ m₃ v * (V j v * V l v) ∂μ = c2 μ V m₁ m₂ m₃ j l := by
  have h1 := (hV.integrable_mul j l).const_mul m₁
  have h2 := (hV.integrable_inner m₂ j l)
  have hb : ∀ a ∈ (Finset.univ : Finset (Fin d)), ∀ b ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun v => m₃ a b * (v a * v b * V j v * V l v)) μ := fun a _ b _ =>
    (hV.integrable_second j l a b).const_mul _
  have ha : ∀ a ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun v => ∑ b, m₃ a b * (v a * v b * V j v * V l v)) μ := fun a _ =>
    integrable_finsetSum _ fun b _ => hb a (Finset.mem_univ _) b (Finset.mem_univ _)
  have h3 : Integrable (fun v => ∑ a, ∑ b, m₃ a b * (v a * v b * V j v * V l v)) μ :=
    integrable_finsetSum _ fun a _ => ha a (Finset.mem_univ _)
  have heq : ∀ v, calM m₁ m₂ m₃ v * (V j v * V l v) =
      m₁ * (V j v * V l v) + (⟪m₂, v⟫ * (V j v * V l v) +
        ∑ a, ∑ b, m₃ a b * (v a * v b * V j v * V l v)) := fun v => by
    simp only [calM, add_mul, Finset.sum_mul, add_assoc, real_inner_comm m₂ v, add_right_inj]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  simp only [heq]
  rw [integral_add h1 (h2.fun_add h3), integral_add h2 h3, integral_const_mul,
    hV.integral_inner, integral_finsetSum _ ha, hV.orthonormal, c2, add_assoc]
  simp only [integral_finsetSum _ (hb _ (Finset.mem_univ _)), integral_const_mul]
  congr 1
  · split_ifs <;> simp
  · rw [real_inner_comm]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [cStar, mul_comm]

end IsVelocityBasis

lemma integral_neg_sub_add {α : Type*} [MeasurableSpace α] {m : Measure α} {f g h : α → ℝ}
    (hf : Integrable f m) (hg : Integrable g m) (hh : Integrable h m) (c : ℝ) :
    ∫ a, -f a - g a + c * h a ∂m = -∫ a, f a ∂m - ∫ a, g a ∂m + c * ∫ a, h a ∂m := by
  rw [integral_add (hf.fun_neg.sub' hg) (hh.const_mul c), integral_sub hf.fun_neg hg, integral_neg,
    integral_const_mul]

lemma fderiv_sum_mul {K : Fin r → Vel d → ℝ} {x : Vel d} (hK : ∀ l, DifferentiableAt ℝ (K l) x)
    (c : Fin r → ℝ) (v : Vel d) :
    fderiv ℝ (fun y => ∑ l, K l y * c l) x v = ∑ l, ⟪gradient (K l) x, v⟫ * c l := by
  have h1 : HasFDerivAt (fun y => ∑ l, K l y * c l) (∑ l, c l • fderiv ℝ (K l) x) x :=
    HasFDerivAt.fun_sum fun l _ => (hK l).hasFDerivAt.mul_const (c l)
  rw [h1.fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul, inner_gradient_left]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- **(4.8) of arXiv 2101.07104 with (3.8)**: the right-hand side `⟨V_j, h⟩ᵥ` of the K-equation for
`g = ∑ₗ K_l V_l`, at a point `x`, in the generality of any measure `μ` on velocity space (the
paper's `ℝ^d`, or its truncation). -/
theorem kEquation {V : Fin r → Vel d → ℝ} (hV : IsVelocityBasis μ V) (ρ : Vel d → ℝ) (ε : ℝ)
    (m₁ : Vel d → ℝ) (m₂ : Vel d → Vel d) (m₃ : Vel d → Fin d → Fin d → ℝ)
    {K : Fin r → Vel d → ℝ} {x : Vel d} (hK : ∀ l, DifferentiableAt ℝ (K l) x) (j : Fin r) :
    ∫ v, V j v * source ρ ε m₁ m₂ m₃ (fun y v => ∑ l, K l y * V l v) x v ∂μ =
      -∑ l, ⟪gradient (K l) x, c1 μ V j l⟫ - ∑ l, K l x * c2 μ V (m₁ x) (m₂ x) (m₃ x) j l +
        ρ x / ε * (vBar μ V j - K j x) := by
  have hd : ∀ v : Vel d, fderiv ℝ (fun y => ∑ l, K l y * V l v) x v =
      ∑ l, ⟪gradient (K l) x, v⟫ * V l v := fun v => fderiv_sum_mul hK _ v
  have hc1 : ∀ l ∈ (Finset.univ : Finset (Fin r)),
      Integrable (fun v => ⟪gradient (K l) x, v⟫ * (V j v * V l v)) μ := fun l _ =>
    hV.integrable_inner _ j l
  have hc2 : ∀ l ∈ (Finset.univ : Finset (Fin r)),
      Integrable (fun v => K l x * (calM (m₁ x) (m₂ x) (m₃ x) v * (V j v * V l v))) μ := fun l _ =>
    (hV.integrable_calM _ _ _ j l).const_mul _
  have hc3 : ∀ l ∈ (Finset.univ : Finset (Fin r)),
      Integrable (fun v => K l x * (V j v * V l v)) μ := fun l _ =>
    (hV.integrable_mul j l).const_mul _
  have heq : ∀ v, V j v * source ρ ε m₁ m₂ m₃ (fun y v => ∑ l, K l y * V l v) x v =
      -∑ l, ⟪gradient (K l) x, v⟫ * (V j v * V l v) -
        ∑ l, K l x * (calM (m₁ x) (m₂ x) (m₃ x) v * (V j v * V l v)) +
        ρ x / ε * (V j v - ∑ l, K l x * (V j v * V l v)) := fun v => by
    have e1 : ∑ l, ⟪gradient (K l) x, v⟫ * (V j v * V l v) =
        V j v * ∑ l, ⟪gradient (K l) x, v⟫ * V l v := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    have e2 : ∑ l, K l x * (calM (m₁ x) (m₂ x) (m₃ x) v * (V j v * V l v)) =
        calM (m₁ x) (m₂ x) (m₃ x) v * V j v * ∑ l, K l x * V l v := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    have e3 : ∑ l, K l x * (V j v * V l v) = V j v * ∑ l, K l x * V l v := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    simp only [source, hd]
    rw [e1, e2, e3]
    ring
  simp only [heq]
  have I1 : Integrable (fun v => ∑ l, ⟪gradient (K l) x, v⟫ * (V j v * V l v)) μ :=
    integrable_finsetSum _ hc1
  have I2 : Integrable (fun v => ∑ l, K l x * (calM (m₁ x) (m₂ x) (m₃ x) v * (V j v * V l v))) μ :=
    integrable_finsetSum _ hc2
  have I3 : Integrable (fun v => ∑ l, K l x * (V j v * V l v)) μ :=
    integrable_finsetSum _ hc3
  rw [integral_neg_sub_add I1 I2 ((hV.integrable j).sub' I3),
    integral_sub (hV.integrable j) I3, integral_finsetSum _ hc1, integral_finsetSum _ hc2,
    integral_finsetSum _ hc3]
  simp only [integral_const_mul, hV.integral_inner, hV.integral_calM, hV.orthonormal]
  simp [vBar]

/-- `d¹_{ik} = ⟨X_i ∇ₓ X_k⟩ₓ` of (4.21). -/
noncomputable def d1 (ν : Measure (Vel d)) (X : Fin r → Vel d → ℝ) (i k : Fin r) : Vel d :=
  WithLp.toLp 2 fun a => ∫ x, X i x * gradient (X k) x a ∂ν

/-- `d*_{ik} = ⟨X_i X_k M₁⟩ₓ` of (4.21). -/
noncomputable def dS (ν : Measure (Vel d)) (X : Fin r → Vel d → ℝ) (m₁ : Vel d → ℝ)
    (i k : Fin r) : ℝ :=
  ∫ x, X i x * X k x * m₁ x ∂ν

/-- `d**_{ik} = ⟨X_i X_k M₂⟩ₓ` of (4.21). -/
noncomputable def dSS (ν : Measure (Vel d)) (X : Fin r → Vel d → ℝ) (m₂ : Vel d → Vel d)
    (i k : Fin r) : Vel d :=
  WithLp.toLp 2 fun a => ∫ x, X i x * X k x * m₂ x a ∂ν

/-- `d***_{ik} = ⟨X_i X_k M₃⟩ₓ` of (4.21). -/
noncomputable def dSSS (ν : Measure (Vel d)) (X : Fin r → Vel d → ℝ)
    (m₃ : Vel d → Fin d → Fin d → ℝ) (i k : Fin r) (a b : Fin d) : ℝ :=
  ∫ x, X i x * X k x * m₃ x a b ∂ν

/-- `X̄_i = ⟨ρ X_i⟩ₓ` of (4.21). -/
noncomputable def xBar (ν : Measure (Vel d)) (X : Fin r → Vel d → ℝ) (ρ : Vel d → ℝ) (i : Fin r) :
    ℝ :=
  ∫ x, ρ x * X i x ∂ν

/-- `R_{ik} = ⟨ρ X_i X_k⟩ₓ` of (4.21). -/
noncomputable def gram (ν : Measure (Vel d)) (X : Fin r → Vel d → ℝ) (ρ : Vel d → ℝ)
    (i k : Fin r) : ℝ :=
  ∫ x, ρ x * X i x * X k x ∂ν

/-- The space basis: differentiable, with all the integrals of (4.21) finite. -/
structure IsSpaceBasis (ν : Measure (Vel d)) (X : Fin r → Vel d → ℝ) (ρ : Vel d → ℝ)
    (m₁ : Vel d → ℝ) (m₂ : Vel d → Vel d) (m₃ : Vel d → Fin d → Fin d → ℝ) : Prop where
  differentiable : ∀ k, Differentiable ℝ (X k)
  integrable_grad : ∀ i k a, Integrable (fun x => X i x * gradient (X k) x a) ν
  integrable_m₁ : ∀ i k, Integrable (fun x => X i x * X k x * m₁ x) ν
  integrable_m₂ : ∀ i k a, Integrable (fun x => X i x * X k x * m₂ x a) ν
  integrable_m₃ : ∀ i k a b, Integrable (fun x => X i x * X k x * m₃ x a b) ν
  integrable_ρ : ∀ i, Integrable (fun x => ρ x * X i x) ν
  integrable_ρ₂ : ∀ i k, Integrable (fun x => ρ x * X i x * X k x) ν

lemma calM_expand (c m₁ : ℝ) (m₂ : Vel d) (m₃ : Fin d → Fin d → ℝ) (v : Vel d) :
    c * m₁ + (∑ a, v a * (c * m₂ a) + ∑ a, ∑ b, v a * v b * (c * m₃ a b)) =
      c * calM m₁ m₂ m₃ v := by
  have e1 : ∑ a, v a * (c * m₂ a) = c * ⟪v, m₂⟫ := by
    rw [real_inner_comm, inner_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  have e2 : ∑ a, ∑ b, v a * v b * (c * m₃ a b) = c * ∑ a, ∑ b, v a * v b * m₃ a b := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [calM, e1, e2]
  ring

namespace IsSpaceBasis

variable {X : Fin r → Vel d → ℝ} {ρ : Vel d → ℝ} {m₁ : Vel d → ℝ} {m₂ : Vel d → Vel d}
  {m₃ : Vel d → Fin d → Fin d → ℝ}

lemma integrable_inner_grad (hX : IsSpaceBasis ν X ρ m₁ m₂ m₃) (i k : Fin r) (v : Vel d) :
    Integrable (fun x => X i x * ⟪gradient (X k) x, v⟫) ν := by
  simp only [inner_eq_sum, Finset.mul_sum]
  refine integrable_finsetSum _ fun a _ => ?_
  refine ((hX.integrable_grad i k a).const_mul (v a)).congr (Eventually.of_forall fun x => ?_)
  simp only
  ring

lemma integral_inner_grad (hX : IsSpaceBasis ν X ρ m₁ m₂ m₃) (i k : Fin r) (v : Vel d) :
    ∫ x, X i x * ⟪gradient (X k) x, v⟫ ∂ν = ⟪d1 ν X i k, v⟫ := by
  have hint : ∀ a ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun x => v a * (X i x * gradient (X k) x a)) ν := fun a _ =>
    (hX.integrable_grad i k a).const_mul _
  have h : ∀ x, X i x * ⟪gradient (X k) x, v⟫ =
      ∑ a, v a * (X i x * gradient (X k) x a) := fun x => by
    rw [inner_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  simp only [h]
  rw [integral_finsetSum _ hint, inner_eq_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_const_mul, mul_comm]
  rfl

lemma integrable_calM (hX : IsSpaceBasis ν X ρ m₁ m₂ m₃) (i k : Fin r) (v : Vel d) :
    Integrable (fun x => X i x * X k x * calM (m₁ x) (m₂ x) (m₃ x) v) ν := by
  have h1 := hX.integrable_m₁ i k
  have h2 : Integrable (fun x => ∑ a, v a * (X i x * X k x * m₂ x a)) ν :=
    integrable_finsetSum _ fun a _ => (hX.integrable_m₂ i k a).const_mul _
  have h3 : Integrable (fun x => ∑ a, ∑ b, v a * v b * (X i x * X k x * m₃ x a b)) ν :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      (hX.integrable_m₃ i k a b).const_mul _
  refine (h1.add (h2.add h3)).congr (Eventually.of_forall fun x => ?_)
  exact calM_expand _ _ _ _ _

/-- **(4.13) of arXiv 2101.07104**:
`⟨X_i X_k 𝓜⟩ₓ = d*_{ik} + v · d**_{ik} + (v ⊗ v) : d***_{ik}`. -/
theorem integral_calM (hX : IsSpaceBasis ν X ρ m₁ m₂ m₃) (i k : Fin r) (v : Vel d) :
    ∫ x, X i x * X k x * calM (m₁ x) (m₂ x) (m₃ x) v ∂ν =
      calM (dS ν X m₁ i k) (dSS ν X m₂ i k) (dSSS ν X m₃ i k) v := by
  have h1 := hX.integrable_m₁ i k
  have hb : ∀ a ∈ (Finset.univ : Finset (Fin d)), ∀ b ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun x => v a * v b * (X i x * X k x * m₃ x a b)) ν := fun a _ b _ =>
    (hX.integrable_m₃ i k a b).const_mul _
  have ha : ∀ a ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun x => ∑ b, v a * v b * (X i x * X k x * m₃ x a b)) ν := fun a _ =>
    integrable_finsetSum _ fun b _ => hb a (Finset.mem_univ _) b (Finset.mem_univ _)
  have ha2 : ∀ a ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun x => v a * (X i x * X k x * m₂ x a)) ν := fun a _ =>
    (hX.integrable_m₂ i k a).const_mul _
  have h2 : Integrable (fun x => ∑ a, v a * (X i x * X k x * m₂ x a)) ν :=
    integrable_finsetSum _ ha2
  have h3 : Integrable (fun x => ∑ a, ∑ b, v a * v b * (X i x * X k x * m₃ x a b)) ν :=
    integrable_finsetSum _ ha
  have heq : ∀ x, X i x * X k x * calM (m₁ x) (m₂ x) (m₃ x) v =
      X i x * X k x * m₁ x + (∑ a, v a * (X i x * X k x * m₂ x a) +
        ∑ a, ∑ b, v a * v b * (X i x * X k x * m₃ x a b)) := fun x =>
    (calM_expand _ _ _ _ _).symm
  simp only [heq]
  rw [integral_add h1 (h2.fun_add h3), integral_add h2 h3, integral_finsetSum _ ha2,
    integral_finsetSum _ ha, calM, inner_eq_sum, add_assoc]
  simp only [integral_finsetSum _ (hb _ (Finset.mem_univ _)), integral_const_mul]
  rfl

end IsSpaceBasis

/-- **(4.12) of arXiv 2101.07104 with (3.10)**: the right-hand side `⟨X_i, h⟩ₓ` of the L-equation
for `g = ∑ₖ X_k L_k`, at a velocity `v`, in the generality of any measure `ν` on position space. -/
theorem lEquation {X : Fin r → Vel d → ℝ} {ρ : Vel d → ℝ} {ε : ℝ} {m₁ : Vel d → ℝ}
    {m₂ : Vel d → Vel d} {m₃ : Vel d → Fin d → Fin d → ℝ} (hX : IsSpaceBasis ν X ρ m₁ m₂ m₃)
    (L : Fin r → Vel d → ℝ) (i : Fin r) (v : Vel d) :
    ∫ x, X i x * source ρ ε m₁ m₂ m₃ (fun y v => ∑ k, X k y * L k v) x v ∂ν =
      -∑ k, ⟪d1 ν X i k, v⟫ * L k v -
        ∑ k, calM (dS ν X m₁ i k) (dSS ν X m₂ i k) (dSSS ν X m₃ i k) v * L k v +
        1 / ε * (xBar ν X ρ i - ∑ k, gram ν X ρ i k * L k v) := by
  have hc1 : ∀ k ∈ (Finset.univ : Finset (Fin r)),
      Integrable (fun x => X i x * ⟪gradient (X k) x, v⟫ * L k v) ν := fun k _ =>
    (hX.integrable_inner_grad i k v).mul_const _
  have hc2 : ∀ k ∈ (Finset.univ : Finset (Fin r)),
      Integrable (fun x => X i x * X k x * calM (m₁ x) (m₂ x) (m₃ x) v * L k v) ν := fun k _ =>
    (hX.integrable_calM i k v).mul_const _
  have hc3 : ∀ k ∈ (Finset.univ : Finset (Fin r)),
      Integrable (fun x => ρ x * X i x * X k x * L k v) ν := fun k _ =>
    (hX.integrable_ρ₂ i k).mul_const _
  have I1 : Integrable (fun x => ∑ k, X i x * ⟪gradient (X k) x, v⟫ * L k v) ν :=
    integrable_finsetSum _ hc1
  have I2 : Integrable (fun x => ∑ k, X i x * X k x * calM (m₁ x) (m₂ x) (m₃ x) v * L k v) ν :=
    integrable_finsetSum _ hc2
  have I3 : Integrable (fun x => ∑ k, ρ x * X i x * X k x * L k v) ν :=
    integrable_finsetSum _ hc3
  have heq : ∀ x, X i x * source ρ ε m₁ m₂ m₃ (fun y v => ∑ k, X k y * L k v) x v =
      -∑ k, X i x * ⟪gradient (X k) x, v⟫ * L k v -
        ∑ k, X i x * X k x * calM (m₁ x) (m₂ x) (m₃ x) v * L k v +
        1 / ε * (ρ x * X i x - ∑ k, ρ x * X i x * X k x * L k v) := fun x => by
    have e1 : ∑ k, X i x * ⟪gradient (X k) x, v⟫ * L k v =
        X i x * ∑ k, ⟪gradient (X k) x, v⟫ * L k v := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : ∑ k, X i x * X k x * calM (m₁ x) (m₂ x) (m₃ x) v * L k v =
        calM (m₁ x) (m₂ x) (m₃ x) v * X i x * ∑ k, X k x * L k v := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e3 : ∑ k, ρ x * X i x * X k x * L k v = ρ x * X i x * ∑ k, X k x * L k v := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [source, fderiv_sum_mul (fun k => (hX.differentiable k).differentiableAt)]
    rw [e1, e2, e3]
    ring
  simp only [heq]
  rw [integral_neg_sub_add I1 I2 ((hX.integrable_ρ i).sub' I3), integral_sub (hX.integrable_ρ i) I3,
    integral_finsetSum _ hc1, integral_finsetSum _ hc2, integral_finsetSum _ hc3]
  simp only [integral_mul_const, hX.integral_inner_grad, hX.integral_calM]
  rfl

/-- **(4.10)–(4.11) of arXiv 2101.07104 with (3.9)**: the right-hand side `-⟨X_i V_j, h⟩_{x,v}` of
the S-equation for `g = ∑_{k,l} X_k S_{kl} V_l`. The double integral is taken as the iterated
integral, `x` first, which is what Fubini gives for integrable `h`. Here
`d²_{ik;jl} = c2 μ V (dS ..) (dSS ..) (dSSS ..) j l`. -/
theorem sEquation {X : Fin r → Vel d → ℝ} {ρ : Vel d → ℝ} {ε : ℝ} {m₁ : Vel d → ℝ}
    {m₂ : Vel d → Vel d} {m₃ : Vel d → Fin d → Fin d → ℝ} (hX : IsSpaceBasis ν X ρ m₁ m₂ m₃)
    {V : Fin r → Vel d → ℝ} (hV : IsVelocityBasis μ V) (S : Fin r → Fin r → ℝ) (i j : Fin r) :
    -∫ v, V j v * ∫ x, X i x * source ρ ε m₁ m₂ m₃
        (fun y v => ∑ k, ∑ l, X k y * S k l * V l v) x v ∂ν ∂μ =
      ∑ k, ∑ l, ⟪d1 ν X i k, c1 μ V j l⟫ * S k l +
        ∑ k, ∑ l, S k l * c2 μ V (dS ν X m₁ i k) (dSS ν X m₂ i k) (dSSS ν X m₃ i k) j l -
        1 / ε * (xBar ν X ρ i * vBar μ V j - ∑ k, gram ν X ρ i k * S k j) := by
  have hg : (fun (y v : Vel d) => ∑ k, ∑ l, X k y * S k l * V l v) =
      fun y v => ∑ k, X k y * ∑ l, S k l * V l v := by
    funext y v
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hg]
  simp only [lEquation hX]
  have hc1 : ∀ k ∈ (Finset.univ : Finset (Fin r)), ∀ l ∈ (Finset.univ : Finset (Fin r)),
      Integrable (fun v => S k l * (⟪d1 ν X i k, v⟫ * (V j v * V l v))) μ := fun k _ l _ =>
    (hV.integrable_inner _ j l).const_mul _
  have hc2 : ∀ k ∈ (Finset.univ : Finset (Fin r)), ∀ l ∈ (Finset.univ : Finset (Fin r)),
      Integrable (fun v => S k l *
        (calM (dS ν X m₁ i k) (dSS ν X m₂ i k) (dSSS ν X m₃ i k) v * (V j v * V l v))) μ :=
    fun k _ l _ => (hV.integrable_calM _ _ _ j l).const_mul _
  have hc3 : ∀ k ∈ (Finset.univ : Finset (Fin r)), ∀ l ∈ (Finset.univ : Finset (Fin r)),
      Integrable (fun v => gram ν X ρ i k * S k l * (V j v * V l v)) μ := fun k _ l _ =>
    (hV.integrable_mul j l).const_mul _
  have hd1 : ∀ k ∈ (Finset.univ : Finset (Fin r)),
      Integrable (fun v => ∑ l, S k l * (⟪d1 ν X i k, v⟫ * (V j v * V l v))) μ := fun k hk =>
    integrable_finsetSum _ (hc1 k hk)
  have hd2 : ∀ k ∈ (Finset.univ : Finset (Fin r)), Integrable (fun v => ∑ l, S k l *
      (calM (dS ν X m₁ i k) (dSS ν X m₂ i k) (dSSS ν X m₃ i k) v * (V j v * V l v))) μ :=
    fun k hk => integrable_finsetSum _ (hc2 k hk)
  have hd3 : ∀ k ∈ (Finset.univ : Finset (Fin r)),
      Integrable (fun v => ∑ l, gram ν X ρ i k * S k l * (V j v * V l v)) μ := fun k hk =>
    integrable_finsetSum _ (hc3 k hk)
  have I1 := integrable_finsetSum _ hd1
  have I2 := integrable_finsetSum _ hd2
  have I3 := integrable_finsetSum _ hd3
  have I0 := (hV.integrable j).const_mul (xBar ν X ρ i)
  have heq : ∀ v, V j v * (-∑ k, ⟪d1 ν X i k, v⟫ * ∑ l, S k l * V l v -
        ∑ k, calM (dS ν X m₁ i k) (dSS ν X m₂ i k) (dSSS ν X m₃ i k) v * ∑ l, S k l * V l v +
        1 / ε * (xBar ν X ρ i - ∑ k, gram ν X ρ i k * ∑ l, S k l * V l v)) =
      -∑ k, ∑ l, S k l * (⟪d1 ν X i k, v⟫ * (V j v * V l v)) -
        ∑ k, ∑ l, S k l *
          (calM (dS ν X m₁ i k) (dSS ν X m₂ i k) (dSSS ν X m₃ i k) v * (V j v * V l v)) +
        1 / ε * (xBar ν X ρ i * V j v - ∑ k, ∑ l, gram ν X ρ i k * S k l * (V j v * V l v)) :=
      fun v => by
    have e : ∀ c : Fin r → ℝ, ∑ k, ∑ l, c k * S k l * (V j v * V l v) =
        V j v * ∑ k, c k * ∑ l, S k l * V l v := fun c => by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    have e1 := e fun k => ⟪d1 ν X i k, v⟫
    have e2 := e fun k => calM (dS ν X m₁ i k) (dSS ν X m₂ i k) (dSSS ν X m₃ i k) v
    have e3 := e fun k => gram ν X ρ i k
    have f1 : ∑ k, ∑ l, S k l * (⟪d1 ν X i k, v⟫ * (V j v * V l v)) =
        ∑ k, ∑ l, ⟪d1 ν X i k, v⟫ * S k l * (V j v * V l v) :=
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    have f2 : ∑ k, ∑ l, S k l *
          (calM (dS ν X m₁ i k) (dSS ν X m₂ i k) (dSSS ν X m₃ i k) v * (V j v * V l v)) =
        ∑ k, ∑ l, calM (dS ν X m₁ i k) (dSS ν X m₂ i k) (dSSS ν X m₃ i k) v * S k l *
          (V j v * V l v) :=
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    rw [f1, f2, e1, e2, e3]
    ring
  simp only [heq]
  rw [integral_neg_sub_add I1 I2 (I0.sub' I3), integral_sub I0 I3, integral_finsetSum _ hd1,
    integral_finsetSum _ hd2, integral_finsetSum _ hd3, integral_const_mul]
  simp only [integral_finsetSum _ (hc1 _ (Finset.mem_univ _)),
    integral_finsetSum _ (hc2 _ (Finset.mem_univ _)),
    integral_finsetSum _ (hc3 _ (Finset.mem_univ _)), integral_const_mul, hV.integral_inner,
    hV.integral_calM, hV.orthonormal, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  have e : ∑ k, ∑ l, S k l * ⟪d1 ν X i k, c1 μ V j l⟫ =
      ∑ k, ∑ l, ⟪d1 ν X i k, c1 μ V j l⟫ * S k l :=
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [e, vBar]
  ring

/-- **(4.20) of arXiv 2101.07104, scalar form**: the first-order IMEX step for
`K' = -E + (ρ / ε) (V̄ - K)`, implicit in the relaxation, is the explicit formula (4.20). It exists
and is unique for all `ρ ≥ 0`, `ε > 0`, `Δt ≥ 0`. -/
theorem imex_iff_closedForm {Kn E Vb ρ ε Δt K : ℝ} (hρ : 0 ≤ ρ) (hε : 0 < ε) (hΔt : 0 ≤ Δt) :
    K = Kn + Δt * (-E + ρ / ε * (Vb - K)) ↔
      K = 1 / (1 + Δt * ρ / ε) * Kn - Δt / (1 + Δt * ρ / ε) * E +
        Δt * ρ / (ε + Δt * ρ) * Vb := by
  have h1 : 0 < 1 + Δt * ρ / ε := by positivity
  have h2 : 0 < ε + Δt * ρ := by positivity
  have h3 : 1 + Δt * ρ / ε = (ε + Δt * ρ) / ε := by field_simp
  have key : K = Kn + Δt * (-E + ρ / ε * (Vb - K)) ↔
      (ε + Δt * ρ) * K = ε * Kn - ε * Δt * E + Δt * ρ * Vb := by
    constructor
    · intro h
      have h4 : ε * K = ε * (Kn + Δt * (-E + ρ / ε * (Vb - K))) := by rw [← h]
      field_simp at h4
      linarith
    · intro h
      apply mul_left_cancel₀ hε.ne'
      field_simp
      linarith
  rw [key, h3]
  constructor
  · intro h
    apply mul_left_cancel₀ h2.ne'
    rw [h]
    field_simp
  · intro h
    rw [h]
    field_simp

/-- **(4.20) of arXiv 2101.07104.** `Kp` is the IMEX Euler step for the K-equation (3.8), with
the relaxation term of `⟨V_j, h⟩ᵥ` taken at the new time (this is the term `ρ / ε (Kn_j - Kp)`),
if and only if `Kp` is given by the explicit formula (4.20), pointwise in `x`. The bracket is
`∑ₗ c¹_{jl} · ∇ₓ Kₗⁿ + ∑ₗ c²_{jl} Kₗⁿ`, with `c²` from (4.9) at the coefficients of `𝓜` at `x`. -/
theorem kStep_closedForm {V : Fin r → Vel d → ℝ} (hV : IsVelocityBasis μ V) (ρ : Vel d → ℝ) {ε : ℝ}
    (m₁ : Vel d → ℝ) (m₂ : Vel d → Vel d) (m₃ : Vel d → Fin d → Fin d → ℝ)
    {Kn : Fin r → Vel d → ℝ} {x : Vel d} (hKn : ∀ l, DifferentiableAt ℝ (Kn l) x)
    (hρ : 0 ≤ ρ x) (hε : 0 < ε) {Δt : ℝ} (hΔt : 0 ≤ Δt) (j : Fin r) {Kp : ℝ} :
    Kp = Kn j x + Δt * (∫ v, V j v * source ρ ε m₁ m₂ m₃ (fun y v => ∑ l, Kn l y * V l v) x v ∂μ +
        ρ x / ε * (Kn j x - Kp)) ↔
      Kp = 1 / (1 + Δt * ρ x / ε) * Kn j x -
        Δt / (1 + Δt * ρ x / ε) * (∑ l, ⟪gradient (Kn l) x, c1 μ V j l⟫ +
          ∑ l, Kn l x * c2 μ V (m₁ x) (m₂ x) (m₃ x) j l) +
        Δt * ρ x / (ε + Δt * ρ x) * vBar μ V j := by
  rw [kEquation hV ρ ε m₁ m₂ m₃ hKn j, ← imex_iff_closedForm hρ hε hΔt]
  exact ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩

/-- The K-step tends to the mean as `ε → 0`, at rate `ε / (ε + Δt ρ)`: from (4.20) of
arXiv 2101.07104,
`Kⁿ⁺¹ - V̄ = ε / (ε + Δt ρ) (Kⁿ - Δt E - V̄)`, pointwise in `x`. -/
theorem closedForm_sub_mean {Kn E Vb ρ ε Δt : ℝ} (hρ : 0 ≤ ρ) (hε : 0 < ε) (hΔt : 0 ≤ Δt) :
    1 / (1 + Δt * ρ / ε) * Kn - Δt / (1 + Δt * ρ / ε) * E + Δt * ρ / (ε + Δt * ρ) * Vb - Vb =
      ε / (ε + Δt * ρ) * (Kn - Δt * E - Vb) := by
  have h1 : 0 < 1 + Δt * ρ / ε := by positivity
  have h2 : 0 < ε + Δt * ρ := by positivity
  have h3 : 1 + Δt * ρ / ε = (ε + Δt * ρ) / ε := by field_simp
  rw [h3]
  field_simp
  ring

/-- **(4.19) of arXiv 2101.07104 is misprinted.** As printed it has no factor `Δt`; with
`w = I₂ - I₁ u` it agrees with the forward Euler step for (4.4) only if `Δt = 1` or `w = 0`. -/
theorem printed_update_iff {ρ Δt : ℝ} (hρ : ρ ≠ 0) (u w : Vel d) :
    u + ρ⁻¹ • w = u + (Δt / ρ) • w ↔ Δt = 1 ∨ w = 0 := by
  constructor
  · intro h
    have h1 : (Δt / ρ - ρ⁻¹) • w = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact (add_left_cancel h).symm
    rcases smul_eq_zero.1 h1 with h2 | h2
    · left
      field_simp at h2
      linarith
    · exact Or.inr h2
  · rintro (rfl | rfl)
    · rw [one_div]
    · simp

/-- **The forward Euler step (4.18)–(4.19) of arXiv 2101.07104, with `Δt` restored, is not the
momentum update `ρ u + Δt I₂`**: with `w = I₂ - I₁ u`, `ρ¹ u¹ = ρ u + Δt I₂ + (Δt² I₁ / ρ) w`, and
the last term is nonzero whenever `I₁ ≠ 0` and `w ≠ 0`. So (6.1) has a defect of order `Δt` in the
momentum for this time discretization. (That the extra term is in general not a divergence, so
that total momentum is not conserved, is not proved here.) The scheme of Sec. 5.2 updates
`(ρ, ρ u)` and does not have it. -/
theorem forwardEuler_momentum {ρ I₁ Δt : ℝ} (hρ : ρ ≠ 0) (u I₂ : Vel d) :
    (ρ + Δt * I₁) • (u + (Δt / ρ) • (I₂ - I₁ • u)) =
      ρ • u + Δt • I₂ + (Δt ^ 2 * I₁ / ρ) • (I₂ - I₁ • u) := by
  have hΔ : Δt = ρ * (Δt / ρ) := by field_simp
  have h2 : Δt ^ 2 * I₁ / ρ = ρ * (Δt / ρ) * I₁ * (Δt / ρ) := by field_simp
  rw [h2]
  generalize Δt / ρ = c at hΔ
  subst hΔ
  module

section Instances

/-- Non-vacuity of `IsVelocityBasis` (arXiv 2101.07104, (3.4)): the constant is a rank-one velocity
basis on a compact domain of positive measure, with non-zero mean. -/
theorem isVelocityBasis_const {Ω : Set (Vel d)} (hΩ : IsCompact Ω) (h0 : 0 < volume.real Ω) :
    IsVelocityBasis (volume.restrict Ω) (fun (_ : Fin 1) (_ : Vel d) => (√(volume.real Ω))⁻¹) ∧
      vBar (volume.restrict Ω) (fun (_ : Fin 1) (_ : Vel d) => (√(volume.real Ω))⁻¹) 0 ≠ 0 := by
  have hc : ∀ {f : Vel d → ℝ}, Continuous f → Integrable f (volume.restrict Ω) := fun hf =>
    hf.continuousOn.integrableOn_compact hΩ
  have hsq : (√(volume.real Ω))⁻¹ * (√(volume.real Ω))⁻¹ * volume.real Ω = 1 := by
    have h1 := Real.mul_self_sqrt h0.le
    have h2 : √(volume.real Ω) ≠ 0 := (Real.sqrt_pos.2 h0).ne'
    field_simp
    exact Real.sq_sqrt h0.le |>.symm
  refine ⟨⟨fun _ => hc (by fun_prop), fun _ _ => hc (by fun_prop),
    fun _ _ a => hc (by fun_prop), fun _ _ a b => hc (by fun_prop), fun j l => ?_⟩, ?_⟩
  · have hjl : j = l := Subsingleton.elim _ _
    simp only [hjl, ↓reduceIte]
    rw [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
    linarith
  · rw [vBar, integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
    exact mul_ne_zero h0.ne' (inv_ne_zero (Real.sqrt_pos.2 h0).ne')

/-- Non-vacuity of `IsSpaceBasis` (arXiv 2101.07104, (3.4)): on a compact domain, a constant `X`
works for all continuous coefficient functions. -/
theorem isSpaceBasis_const {Ω : Set (Vel d)} (hΩ : IsCompact Ω) (c : ℝ) {ρ m₁ : Vel d → ℝ}
    {m₂ : Vel d → Vel d} {m₃ : Vel d → Fin d → Fin d → ℝ} (hρ : Continuous ρ)
    (hm₁ : Continuous m₁) (hm₂ : Continuous m₂) (hm₃ : ∀ a b, Continuous fun x => m₃ x a b) :
    IsSpaceBasis (volume.restrict Ω) (fun (_ : Fin 1) (_ : Vel d) => c) ρ m₁ m₂ m₃ := by
  have hc : ∀ {f : Vel d → ℝ}, Continuous f → Integrable f (volume.restrict Ω) := fun hf =>
    hf.continuousOn.integrableOn_compact hΩ
  have hg : ∀ x : Vel d, gradient (fun _ : Vel d => c) x = 0 := fun x => by
    simp [gradient]
  refine ⟨fun _ => differentiable_const _, fun _ _ a => ?_, fun _ _ => hc (by fun_prop),
    fun _ _ a => hc (by fun_prop), fun _ _ a b => hc ((hm₃ a b).const_mul _),
    fun _ => hc (by fun_prop), fun _ _ => hc (by fun_prop)⟩
  simp [hg]

end Instances

end Substeps

section Resolvent

/-- **Resolvent commutation** (Secs. 3–4.1 of arXiv 2101.07104, the reason why the implicit K-step
is explicit): if the relaxation `S` commutes with the Galerkin projector `Q` and `I + h S` is
injective, then for `Y₀ ∈ range Q` the implicit-explicit Euler step for `Y' = Q (N(Y) - S Y)` is
`(I + h S) Y₁ = Y₀ + h Q N(Y₀)`: no projected operator has to be inverted. Note the sign of `S`,
which is the sign of a relaxation; see `resolvent_sign`. -/
theorem imex_iff_resolvent {H : Type*} [AddCommGroup H] [Module ℝ H] {Q S : H →ₗ[ℝ] H}
    (hQ : ∀ y, Q (Q y) = Q y) (hcomm : ∀ y, Q (S y) = S (Q y)) {h : ℝ}
    (hinj : ∀ y, y + h • S y = 0 → y = 0) (N : H → H) {Y₀ Y₁ : H} (hY₀ : Q Y₀ = Y₀) :
    Y₁ = Y₀ + h • Q (N Y₀ - S Y₁) ↔ Y₁ + h • S Y₁ = Y₀ + h • Q (N Y₀) := by
  have hb : Q (Y₀ + h • Q (N Y₀)) = Y₀ + h • Q (N Y₀) := by
    rw [map_add, map_smul, hQ, hY₀]
  constructor
  · intro hY
    have h1 : Q Y₁ = Y₁ := by
      conv_lhs => rw [hY]
      rw [map_add, map_smul, hQ, hY₀, ← hY]
    have h2 : Q (S Y₁) = S Y₁ := by rw [hcomm, h1]
    have h3 := hY
    rw [map_sub, h2] at h3
    linear_combination (norm := module) h3
  · intro hY
    have h1 : Y₁ - Q Y₁ = 0 := by
      refine hinj _ ?_
      have h2 := congrArg Q hY
      rw [map_add, map_smul, hcomm, hb, ← hY] at h2
      rw [map_sub, smul_sub]
      linear_combination (norm := module) -h2
    have h3 : Q Y₁ = Y₁ := (sub_eq_zero.1 h1).symm
    rw [map_sub, hcomm, h3, smul_sub]
    linear_combination (norm := module) hY

/-- Resolvent commutation (arXiv 2101.07104, Secs. 3–4.1), in explicit form:
`Y₁ = (I + h S)⁻¹ (Y₀ + h Q N(Y₀))`, for a bounded `S` with `I + h S` invertible. -/
theorem imex_eq_resolvent {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {Q S : H →L[ℝ] H} (hQ : ∀ y, Q (Q y) = Q y) (hcomm : ∀ y, Q (S y) = S (Q y)) {h : ℝ}
    (hu : IsUnit (1 + h • S)) (N : H → H) {Y₀ Y₁ : H} (hY₀ : Q Y₀ = Y₀) :
    Y₁ = Y₀ + h • Q (N Y₀ - S Y₁) ↔
      Y₁ = (Ring.inverse ((1 : H →L[ℝ] H) + h • S) : H →L[ℝ] H) (Y₀ + h • Q (N Y₀)) := by
  set A : H →L[ℝ] H := 1 + h • S with hA
  set B : H →L[ℝ] H := Ring.inverse A with hB
  have hl : ∀ y, B (A y) = y := fun y => DFunLike.congr_fun (Ring.inverse_mul_cancel A hu) y
  have hr : ∀ y, A (B y) = y := fun y => DFunLike.congr_fun (Ring.mul_inverse_cancel A hu) y
  have hAy : ∀ y, A y = y + h • S y := fun y => by simp [hA]
  have hinj : ∀ y, y + h • S y = 0 → y = 0 := fun y hy => by
    rw [← hAy] at hy
    rw [← hl y, hy, map_zero]
  have key := imex_iff_resolvent (Q := (Q : H →ₗ[ℝ] H)) (S := (S : H →ₗ[ℝ] H)) hQ hcomm hinj N hY₀
    (Y₁ := Y₁)
  simp only [ContinuousLinearMap.coe_coe] at key
  rw [key, ← hAy]
  exact ⟨fun h1 => by rw [← h1, hl], fun h1 => by rw [h1, hr]⟩

/-- Not a statement about the paper: the internal planning note for this slice (not arXiv
2101.07104, whose signs agree with `imex_iff_resolvent`), read literally, has the wrong sign:
implicit Euler for
`Y' = Q (N + S Y)` with `Q = S = 1`, `N = 0`, `h = 1/2`, `Y₀ = 1` gives `Y₁ = 2`, not
`(1 + h)⁻¹ Y₀ = 2/3`. The correct statement, for `Y' = Q (N - S Y)`, is `imex_iff_resolvent`. -/
theorem resolvent_sign :
    (2 : ℝ) = 1 + (1 / 2) * (0 + 2) ∧ (2 : ℝ) ≠ (1 + 1 / 2)⁻¹ * (1 + (1 / 2) * 0) := by
  norm_num

end Resolvent

section KSL

open scoped LeanDLRA.Frobenius
open LeanDLRA.Frobenius LeanDLRA.Novel.KineticAP

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq r]

/-- One step of the IMEX projector-splitting integrator of Sec. 4.1 of arXiv 2101.07104, fully
discrete: `g = K₀ Vᵀ` on the grid, with the relaxation `(ρ / ε) (1 - g)` implicit and all other
terms `F` explicit. -/
structure IsIMEXKSLStep (ρ : m → ℝ) (e : Matrix m Unit ℝ) (b : Matrix n Unit ℝ)
    (F : Matrix m n ℝ → Matrix m n ℝ) (h ε : ℝ) (K₀ : Matrix m r ℝ) (V : Matrix n r ℝ)
    (K₁ X₁ : Matrix m r ℝ) (S₁ S₂ : Matrix r r ℝ) (L₁ : Matrix r n ℝ) : Prop where
  /-- The K-step (4.20). -/
  kStep : K₁ + (h / ε) • (Matrix.diagonal ρ * K₁) =
    K₀ + h • (F (K₀ * Vᵀ) * V) + (h / ε) • (Matrix.diagonal ρ * (e * (Vᵀ * b)ᵀ))
  /-- The orthonormal factor of the QR decomposition. -/
  orthonormal : X₁ᵀ * X₁ = 1
  /-- The QR decomposition of `K₁`, possibly rank-deficient. -/
  qr : K₁ = X₁ * S₁
  /-- The S-step of Sec. 4.1, integrated backward as in (3.9). -/
  sStep : S₂ - (h / ε) • (stiffness ρ X₁ * S₂) =
    S₁ - h • (X₁ᵀ * F (X₁ * S₁ * Vᵀ) * V) - (h / ε) • (X₁ᵀ * (Matrix.diagonal ρ * e) * (Vᵀ * b)ᵀ)
  /-- The L-step of Sec. 4.1. -/
  lStep : L₁ + (h / ε) • (stiffness ρ X₁ * L₁) =
    S₂ * Vᵀ + h • (X₁ᵀ * F (X₁ * (S₂ * Vᵀ))) + (h / ε) • (X₁ᵀ * (Matrix.diagonal ρ * e) * bᵀ)

omit [DecidableEq m] in
lemma norm_mul_le_of_orthonormal {W : Matrix n r ℝ} (hW : Wᵀ * W = 1) (Z : Matrix m n ℝ) :
    ‖Z * W‖ ≤ ‖Z‖ := by
  rw [← norm_mul_transpose_of_orthonormal hW (Z * W)]
  simpa using (isOrthProj_rightProj (m := m) hW).norm_le Z

omit [DecidableEq m] in
lemma norm_transpose_mul_le {W : Matrix m r ℝ} (hW : Wᵀ * W = 1) (Z : Matrix m n ℝ) :
    ‖Wᵀ * Z‖ ≤ ‖Z‖ := by
  rw [← norm_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  exact (norm_mul_le_of_orthonormal hW Zᵀ).trans (norm_transpose Z).le

omit [DecidableEq m] [DecidableEq r] in
lemma norm_mul_transpose_unit (a : Matrix m Unit ℝ) (c : Matrix r Unit ℝ) :
    ‖a * cᵀ‖ = ‖a‖ * ‖c‖ := by
  have h : ‖a * cᵀ‖ ^ 2 = (‖a‖ * ‖c‖) ^ 2 := by
    rw [mul_pow, norm_sq_eq_sum, norm_sq_eq_sum, norm_sq_eq_sum, Finset.sum_mul_sum]
    simp [Matrix.mul_apply, mul_pow]
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

lemma le_norm_of_coercive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {c : ℝ}
    {y z : E} (h : c * ‖y‖ ^ 2 ≤ ⟪z, y⟫) : c * ‖y‖ ≤ ‖z‖ := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
    have h2 := real_inner_le_norm z y
    have h3 : c * ‖y‖ * ‖y‖ ≤ ‖z‖ * ‖y‖ := by nlinarith
    exact le_of_mul_le_mul_right h3 hy'

section Bounds

variable {ρ : m → ℝ} {ρ₀ ρ₁ : ℝ} {e : Matrix m Unit ℝ} {b : Matrix n Unit ℝ}
  {F : Matrix m n ℝ → Matrix m n ℝ} {h ε Λ : ℝ} {K₀ : Matrix m r ℝ} {V : Matrix n r ℝ}
  {K₁ X₁ : Matrix m r ℝ} {S₁ S₂ : Matrix r r ℝ} {L₁ : Matrix r n ℝ}

/-- The component of `e` orthogonal to `range X₁`. -/
def perp (X₁ : Matrix m r ℝ) (e : Matrix m Unit ℝ) : Matrix m Unit ℝ := e - X₁ * (X₁ᵀ * e)

namespace IsIMEXKSLStep

/-- K-step limit: `K₁ → e V̄ᵀ` at rate `ε / h`. -/
lemma kStep_le (hs : IsIMEXKSLStep ρ e b F h ε K₀ V K₁ X₁ S₁ S₂ L₁)
    (hρ : IsCrossSection ρ ρ₀ ρ₁) (hV : Vᵀ * V = 1) (hF : ∀ Z, ‖F Z‖ ≤ Λ * ‖Z‖) (hh : 0 < h)
    (hε : 0 < ε) :
    (ρ₀ + ε / h) * ‖K₁ - e * (Vᵀ * b)ᵀ‖ ≤
      ε / h * ((1 + h * Λ) * ‖K₀‖ + ‖e‖ * ‖Vᵀ * b‖) := by
  set τ := ε / h with hτ
  have hτ0 : 0 < τ := div_pos hε hh
  have h1 : τ * (h / ε) = 1 := by
    rw [hτ]
    field_simp
  set Y := K₁ - e * (Vᵀ * b)ᵀ with hY
  have key := congrArg (fun Z => τ • Z) hs.kStep
  simp only [smul_add, smul_smul, h1, one_smul] at key
  have heq : Matrix.diagonal ρ * Y + τ • Y =
      τ • (K₀ + h • (F (K₀ * Vᵀ) * V) - e * (Vᵀ * b)ᵀ) := by
    rw [hY, Matrix.mul_sub]
    linear_combination (norm := module) key
  have hc : (ρ₀ + τ) * ‖Y‖ ≤ ‖Matrix.diagonal ρ * Y + τ • Y‖ := by
    refine le_norm_of_coercive ?_
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have := hρ.lower_inner Y
    nlinarith
  refine hc.trans ?_
  rw [heq, norm_smul, Real.norm_of_nonneg hτ0.le]
  refine mul_le_mul_of_nonneg_left ?_ hτ0.le
  have h2 : ‖F (K₀ * Vᵀ) * V‖ ≤ Λ * ‖K₀‖ := by
    refine (norm_mul_le_of_orthonormal hV _).trans ?_
    have := hF (K₀ * Vᵀ)
    rwa [norm_mul_transpose_of_orthonormal hV] at this
  have h3 : ‖K₀ + h • (F (K₀ * Vᵀ) * V) - e * (Vᵀ * b)ᵀ‖ ≤
      ‖K₀‖ + h * ‖F (K₀ * Vᵀ) * V‖ + ‖e‖ * ‖Vᵀ * b‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul_transpose_unit]
    refine add_le_add ((norm_add_le _ _).trans ?_) le_rfl
    rw [norm_smul, Real.norm_of_nonneg hh.le]
  have h4 := mul_le_mul_of_nonneg_left h2 hh.le
  nlinarith

/-- `e` is captured by the new basis up to the K-step error. -/
lemma perp_le (hs : IsIMEXKSLStep ρ e b F h ε K₀ V K₁ X₁ S₁ S₂ L₁) :
    ‖perp X₁ e‖ * ‖Vᵀ * b‖ ≤ ‖K₁ - e * (Vᵀ * b)ᵀ‖ := by
  have h1 := (isOrthProj_leftProj (n := r) hs.orthonormal).norm_sub_le (K₁ - e * (Vᵀ * b)ᵀ)
  have h2 : K₁ - e * (Vᵀ * b)ᵀ - leftProj X₁ (K₁ - e * (Vᵀ * b)ᵀ) =
      -(perp X₁ e * (Vᵀ * b)ᵀ) := by
    have h3 : X₁ * X₁ᵀ * K₁ = K₁ := by
      rw [hs.qr, Matrix.mul_assoc, ← Matrix.mul_assoc X₁ᵀ, hs.orthonormal, Matrix.one_mul]
    rw [leftProj_apply, Matrix.mul_sub, h3, perp, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
    abel
  rw [h2, norm_neg, norm_mul_transpose_unit] at h1
  exact h1

/-- S-step limit: `S₂ → (X₁ᵀ e) V̄ᵀ`. The factor `ρ₀ - ε / h` is the distance of `ε / h` to the
spectrum of `⟨ρ X X⟩` when `ε / h < ρ₀`. -/
lemma sStep_le (hs : IsIMEXKSLStep ρ e b F h ε K₀ V K₁ X₁ S₁ S₂ L₁)
    (hρ : IsCrossSection ρ ρ₀ ρ₁) (hV : Vᵀ * V = 1) (hF : ∀ Z, ‖F Z‖ ≤ Λ * ‖Z‖) (hh : 0 < h)
    (hε : 0 < ε) :
    (ρ₀ - ε / h) * ‖S₂ - (X₁ᵀ * e) * (Vᵀ * b)ᵀ‖ ≤
      ε / h * (‖e‖ * ‖Vᵀ * b‖ + (1 + h * Λ) * ‖K₁‖) + ρ₁ * (‖perp X₁ e‖ * ‖Vᵀ * b‖) := by
  set τ := ε / h with hτ
  have hτ0 : 0 < τ := div_pos hε hh
  have h1 : τ * (h / ε) = 1 := by
    rw [hτ]
    field_simp
  have hX := hs.orthonormal
  set c := X₁ᵀ * e with hc
  set bb := (Vᵀ * b)ᵀ with hbb
  set R := stiffness ρ X₁ with hR
  set D := Matrix.diagonal ρ with hD
  have key := congrArg (fun Z => τ • Z) hs.sStep
  simp only [smul_sub, smul_smul, h1, one_smul] at key
  have hXbar : X₁ᵀ * (D * e) = R * c + X₁ᵀ * (D * perp X₁ e) := by
    simp only [hR, stiffness, perp, Matrix.mul_sub, Matrix.mul_assoc, hc]
    abel
  have heq : R * (S₂ - c * bb) - τ • (S₂ - c * bb) =
      τ • (c * bb - S₁ + h • (X₁ᵀ * F (X₁ * S₁ * Vᵀ) * V)) + X₁ᵀ * (D * (perp X₁ e * bb)) := by
    rw [hXbar, Matrix.add_mul] at key
    have e1 : R * (S₂ - c * bb) = R * S₂ - R * c * bb := by
      rw [Matrix.mul_sub, Matrix.mul_assoc R c]
    have e2 : X₁ᵀ * (D * (perp X₁ e * bb)) = X₁ᵀ * (D * perp X₁ e) * bb := by
      simp only [Matrix.mul_assoc]
    rw [e1, e2]
    linear_combination (norm := module) -key
  have hcoer : (ρ₀ - τ) * ‖S₂ - c * bb‖ ≤ ‖R * (S₂ - c * bb) - τ • (S₂ - c * bb)‖ := by
    refine le_norm_of_coercive ?_
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have := hρ.lower_stiffness hX (S₂ - c * bb)
    nlinarith
  refine hcoer.trans ?_
  rw [heq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_of_nonneg hτ0.le]
  have hρ₁ : 0 ≤ ρ₁ := hρ.pos.le.trans hρ.le
  have h2 : ‖X₁ᵀ * (D * (perp X₁ e * bb))‖ ≤ ρ₁ * (‖perp X₁ e‖ * ‖Vᵀ * b‖) := by
    refine (norm_transpose_mul_le hX _).trans ?_
    have := hρ.norm_diagonal_mul_le (perp X₁ e * bb)
    rwa [hbb, norm_mul_transpose_unit] at this
  have h3 : ‖S₁‖ = ‖K₁‖ := by rw [hs.qr, norm_mul_of_orthonormal hX]
  have h4 : ‖X₁ᵀ * F (X₁ * S₁ * Vᵀ) * V‖ ≤ Λ * ‖S₁‖ := by
    refine (norm_mul_le_of_orthonormal hV _).trans ((norm_transpose_mul_le hX _).trans ?_)
    have := hF (X₁ * S₁ * Vᵀ)
    rwa [norm_mul_transpose_of_orthonormal hV, norm_mul_of_orthonormal hX] at this
  have h5 : ‖c * bb‖ ≤ ‖e‖ * ‖Vᵀ * b‖ := by
    rw [hbb, norm_mul_transpose_unit]
    exact mul_le_mul_of_nonneg_right (norm_transpose_mul_le hX e) (norm_nonneg _)
  have h6 : ‖c * bb - S₁ + h • (X₁ᵀ * F (X₁ * S₁ * Vᵀ) * V)‖ ≤
      ‖e‖ * ‖Vᵀ * b‖ + (1 + h * Λ) * ‖K₁‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hh.le, ← h3]
    have h7 := norm_sub_le (c * bb) S₁
    have h8 := mul_le_mul_of_nonneg_left h4 hh.le
    nlinarith
  have := mul_le_mul_of_nonneg_left h6 hτ0.le
  linarith

/-- L-step limit: `L₁ → (X₁ᵀ e) bᵀ`. -/
lemma lStep_le (hs : IsIMEXKSLStep ρ e b F h ε K₀ V K₁ X₁ S₁ S₂ L₁)
    (hρ : IsCrossSection ρ ρ₀ ρ₁) (hV : Vᵀ * V = 1) (hF : ∀ Z, ‖F Z‖ ≤ Λ * ‖Z‖) (hh : 0 < h)
    (hε : 0 < ε) :
    (ρ₀ + ε / h) * ‖L₁ - (X₁ᵀ * e) * bᵀ‖ ≤
      ε / h * ((1 + h * Λ) * ‖S₂‖ + ‖e‖ * ‖b‖) + ρ₁ * (‖perp X₁ e‖ * ‖b‖) := by
  set τ := ε / h with hτ
  have hτ0 : 0 < τ := div_pos hε hh
  have h1 : τ * (h / ε) = 1 := by
    rw [hτ]
    field_simp
  have hX := hs.orthonormal
  set c := X₁ᵀ * e with hc
  set R := stiffness ρ X₁ with hR
  set D := Matrix.diagonal ρ with hD
  have key := congrArg (fun Z => τ • Z) hs.lStep
  simp only [smul_add, smul_smul, h1, one_smul] at key
  have hXbar : X₁ᵀ * (D * e) = R * c + X₁ᵀ * (D * perp X₁ e) := by
    simp only [hR, stiffness, perp, Matrix.mul_sub, Matrix.mul_assoc, hc]
    abel
  have heq : R * (L₁ - c * bᵀ) + τ • (L₁ - c * bᵀ) =
      τ • (S₂ * Vᵀ + h • (X₁ᵀ * F (X₁ * (S₂ * Vᵀ))) - c * bᵀ) +
        X₁ᵀ * (D * (perp X₁ e * bᵀ)) := by
    rw [hXbar, Matrix.add_mul] at key
    have e1 : R * (L₁ - c * bᵀ) = R * L₁ - R * c * bᵀ := by
      rw [Matrix.mul_sub, Matrix.mul_assoc R c]
    have e2 : X₁ᵀ * (D * (perp X₁ e * bᵀ)) = X₁ᵀ * (D * perp X₁ e) * bᵀ := by
      simp only [Matrix.mul_assoc]
    rw [e1, e2]
    linear_combination (norm := module) key
  have hcoer : (ρ₀ + τ) * ‖L₁ - c * bᵀ‖ ≤ ‖R * (L₁ - c * bᵀ) + τ • (L₁ - c * bᵀ)‖ := by
    refine le_norm_of_coercive ?_
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have := hρ.lower_stiffness hX (L₁ - c * bᵀ)
    nlinarith
  refine hcoer.trans ?_
  rw [heq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_of_nonneg hτ0.le]
  have h2 : ‖X₁ᵀ * (D * (perp X₁ e * bᵀ))‖ ≤ ρ₁ * (‖perp X₁ e‖ * ‖b‖) := by
    refine (norm_transpose_mul_le hX _).trans ?_
    have := hρ.norm_diagonal_mul_le (perp X₁ e * bᵀ)
    rwa [norm_mul_transpose_unit] at this
  have h3 : ‖S₂ * Vᵀ‖ = ‖S₂‖ := norm_mul_transpose_of_orthonormal hV S₂
  have h4 : ‖X₁ᵀ * F (X₁ * (S₂ * Vᵀ))‖ ≤ Λ * ‖S₂‖ := by
    refine (norm_transpose_mul_le hX _).trans ?_
    have := hF (X₁ * (S₂ * Vᵀ))
    rwa [norm_mul_of_orthonormal hX, h3] at this
  have h5 : ‖c * bᵀ‖ ≤ ‖e‖ * ‖b‖ := by
    rw [norm_mul_transpose_unit]
    exact mul_le_mul_of_nonneg_right (norm_transpose_mul_le hX e) (norm_nonneg _)
  have h6 : ‖S₂ * Vᵀ + h • (X₁ᵀ * F (X₁ * (S₂ * Vᵀ))) - c * bᵀ‖ ≤
      (1 + h * Λ) * ‖S₂‖ + ‖e‖ * ‖b‖ := by
    refine (norm_sub_le _ _).trans ?_
    have h7 := norm_add_le (S₂ * Vᵀ) (h • (X₁ᵀ * F (X₁ * (S₂ * Vᵀ))))
    rw [norm_smul, Real.norm_of_nonneg hh.le, h3] at h7
    have h8 := mul_le_mul_of_nonneg_left h4 hh.le
    nlinarith
  have := mul_le_mul_of_nonneg_left h6 hτ0.le
  linarith

omit [Fintype n] [DecidableEq m] [DecidableEq r] in
lemma sub_eq (X₁ : Matrix m r ℝ) (L₁ : Matrix r n ℝ) (e : Matrix m Unit ℝ) (b : Matrix n Unit ℝ) :
    X₁ * L₁ - e * bᵀ = X₁ * (L₁ - (X₁ᵀ * e) * bᵀ) - perp X₁ e * bᵀ := by
  rw [perp, Matrix.sub_mul, Matrix.mul_sub]
  simp only [Matrix.mul_assoc]
  abel

end IsIMEXKSLStep

/-- The constant of `IsIMEXKSLStep.ap_step_le`, with `E = ‖e‖`, `B = ‖b‖`, `q = ‖V̄‖`,
`N = ‖K₀‖`. -/
noncomputable def apConst (ρ₀ ρ₁ Λ h E B q N : ℝ) : ℝ :=
  let G := 1 + h * Λ
  let p := E * q
  let δ := (G * N + p) / ρ₀
  let s := p + ρ₀ * δ / 2
  let σ := 2 / ρ₀ * (p + G * s + ρ₁ * δ)
  let l := p + ρ₀ * σ / 2
  (((G * l + E * B + ρ₁ * δ * B / q) / ρ₀) + δ * B / q) / h

omit [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq r] in
/-- The real arithmetic of `IsIMEXKSLStep.ap_step_le`. -/
private lemma ap_arith {ρ₀ ρ₁ G τ E B q N p δ s σ l lam a pn ks w s2 y : ℝ} (hρ₀ : 0 < ρ₀)
    (hρ₁ : 0 ≤ ρ₁) (hτ0 : 0 < τ) (hτ1 : τ ≤ ρ₀ / 2) (hG : 0 ≤ G) (hq : 0 < q) (hE : 0 ≤ E)
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hp : p = E * q) (hδ : δ = (G * N + p) / ρ₀)
    (hs : s = p + ρ₀ * δ / 2) (hσ : σ = 2 / ρ₀ * (p + G * s + ρ₁ * δ))
    (hl : l = p + ρ₀ * σ / 2) (hlam : lam = (G * l + E * B + ρ₁ * δ * B / q) / ρ₀)
    (ha0 : 0 ≤ a) (hw0 : 0 ≤ w) (hy0 : 0 ≤ y)
    (h1 : (ρ₀ + τ) * a ≤ τ * (G * N + p)) (h2 : pn * q ≤ a) (h3 : ks ≤ a + p)
    (h4 : (ρ₀ - τ) * w ≤ τ * (p + G * ks) + ρ₁ * (pn * q)) (h5 : s2 ≤ w + p)
    (h6 : (ρ₀ + τ) * y ≤ τ * (G * s2 + E * B) + ρ₁ * (pn * B)) :
    y + pn * B ≤ τ * (lam + δ * B / q) := by
  have hp0 : 0 ≤ p := by
    rw [hp]
    positivity
  have hδ' : ρ₀ * δ = G * N + p := by
    rw [hδ]
    field_simp
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    positivity
  have ha1 : a ≤ τ * δ := by
    have h7 : ρ₀ * a ≤ ρ₀ * (τ * δ) :=
      calc ρ₀ * a ≤ (ρ₀ + τ) * a := mul_le_mul_of_nonneg_right (by linarith) ha0
        _ ≤ τ * (G * N + p) := h1
        _ = ρ₀ * (τ * δ) := by
          rw [← hδ']
          ring
    exact le_of_mul_le_mul_left h7 hρ₀
  have hks : ks ≤ s := by
    have h7 : τ * δ ≤ ρ₀ / 2 * δ := mul_le_mul_of_nonneg_right hτ1 hδ0
    rw [hs]
    linarith
  have hs0 : 0 ≤ s := by
    rw [hs]
    positivity
  have hσ' : ρ₀ / 2 * σ = p + G * s + ρ₁ * δ := by
    rw [hσ]
    field_simp
  have hσ0 : 0 ≤ σ := by
    rw [hσ]
    positivity
  have hw1 : w ≤ τ * σ := by
    have h7 : ρ₀ / 2 * w ≤ ρ₀ / 2 * (τ * σ) :=
      calc ρ₀ / 2 * w ≤ (ρ₀ - τ) * w := mul_le_mul_of_nonneg_right (by linarith) hw0
        _ ≤ τ * (p + G * ks) + ρ₁ * (pn * q) := h4
        _ ≤ τ * (p + G * s) + ρ₁ * (τ * δ) :=
          add_le_add (mul_le_mul_of_nonneg_left
            (add_le_add_right (mul_le_mul_of_nonneg_left hks hG) p) hτ0.le)
            (mul_le_mul_of_nonneg_left (h2.trans ha1) hρ₁)
        _ = ρ₀ / 2 * (τ * σ) := by
          rw [show ρ₀ / 2 * (τ * σ) = τ * (ρ₀ / 2 * σ) by ring, hσ']
          ring
    exact le_of_mul_le_mul_left h7 (by positivity)
  have hS2 : s2 ≤ l := by
    have h7 : τ * σ ≤ ρ₀ / 2 * σ := mul_le_mul_of_nonneg_right hτ1 hσ0
    rw [hl]
    linarith
  have hpn : pn * B ≤ τ * (δ * B / q) := by
    have h7 : pn ≤ τ * δ / q := by
      rw [le_div_iff₀ hq]
      exact h2.trans ha1
    calc pn * B ≤ τ * δ / q * B := mul_le_mul_of_nonneg_right h7 hB
      _ = τ * (δ * B / q) := by ring
  have hlam' : ρ₀ * lam = G * l + E * B + ρ₁ * δ * B / q := by
    rw [hlam]
    field_simp
  have hy : y ≤ τ * lam := by
    have h7 : ρ₀ * y ≤ ρ₀ * (τ * lam) :=
      calc ρ₀ * y ≤ (ρ₀ + τ) * y := mul_le_mul_of_nonneg_right (by linarith) hy0
        _ ≤ τ * (G * s2 + E * B) + ρ₁ * (pn * B) := h6
        _ ≤ τ * (G * l + E * B) + ρ₁ * (τ * (δ * B / q)) :=
          add_le_add (mul_le_mul_of_nonneg_left
            (add_le_add_left (mul_le_mul_of_nonneg_left hS2 hG) _) hτ0.le)
            (mul_le_mul_of_nonneg_left hpn hρ₁)
        _ = ρ₀ * (τ * lam) := by
          rw [show ρ₀ * (τ * lam) = τ * (ρ₀ * lam) by ring, hlam']
          ring
    exact le_of_mul_le_mul_left h7 hρ₀
  rw [mul_add]
  exact add_le_add hy hpn

/-- **Asymptotic preservation of one IMEX KSL step (Sec. 6 of arXiv 2101.07104, Remark 4.4), at
fixed time step.**  If `V̄ = Vᵀ b ≠ 0`, every step of the scheme satisfies `‖g¹ - 1‖ ≤ C ε`, with
`C` independent of `ε`, for `ε ≤ h ρ₀ / 2`, at every rank, in particular `r = 1` as stated in
Remark 4.4.

This is the fact `g = 1 + O(ε)` that the formal analysis (6.2)–(6.3) of the paper relies on. Here
nothing about `g` is assumed: the input `K₀` is arbitrary and the bases need not contain the
constants. The hypothesis on `V̄` cannot be dropped, see `not_ap_of_mean_zero`. `F` is the transport
and `𝓜` term; only `‖F Z‖ ≤ Λ ‖Z‖` is used. This is not (6.3): the `O(ε)` term is bounded, not
identified. -/
theorem IsIMEXKSLStep.ap_step_le (hs : IsIMEXKSLStep ρ e b F h ε K₀ V K₁ X₁ S₁ S₂ L₁)
    (hρ : IsCrossSection ρ ρ₀ ρ₁) (hV : Vᵀ * V = 1) (hΛ : 0 ≤ Λ) (hF : ∀ Z, ‖F Z‖ ≤ Λ * ‖Z‖)
    (hh : 0 < h) (hε : 0 < ε) (hε' : ε ≤ h * ρ₀ / 2) (hb : Vᵀ * b ≠ 0) :
    ‖X₁ * L₁ - e * bᵀ‖ ≤ apConst ρ₀ ρ₁ Λ h ‖e‖ ‖b‖ ‖Vᵀ * b‖ ‖K₀‖ * ε := by
  have hτ1 : ε / h ≤ ρ₀ / 2 := by
    rw [div_le_iff₀ hh]
    linarith
  have h3 : ‖K₁‖ ≤ ‖K₁ - e * (Vᵀ * b)ᵀ‖ + ‖e‖ * ‖Vᵀ * b‖ := by
    have h5 := norm_add_le (K₁ - e * (Vᵀ * b)ᵀ) (e * (Vᵀ * b)ᵀ)
    rwa [sub_add_cancel, norm_mul_transpose_unit] at h5
  have h5 : ‖S₂‖ ≤ ‖S₂ - (X₁ᵀ * e) * (Vᵀ * b)ᵀ‖ + ‖e‖ * ‖Vᵀ * b‖ := by
    have h6 := norm_add_le (S₂ - (X₁ᵀ * e) * (Vᵀ * b)ᵀ) ((X₁ᵀ * e) * (Vᵀ * b)ᵀ)
    rw [sub_add_cancel, norm_mul_transpose_unit] at h6
    have h7 : ‖X₁ᵀ * e‖ * ‖Vᵀ * b‖ ≤ ‖e‖ * ‖Vᵀ * b‖ :=
      mul_le_mul_of_nonneg_right (norm_transpose_mul_le hs.orthonormal e) (norm_nonneg _)
    linarith
  have hmain := ap_arith (ρ₁ := ρ₁) (G := 1 + h * Λ) (τ := ε / h) (E := ‖e‖) (B := ‖b‖)
    (q := ‖Vᵀ * b‖) (N := ‖K₀‖) (a := ‖K₁ - e * (Vᵀ * b)ᵀ‖)
    (w := ‖S₂ - (X₁ᵀ * e) * (Vᵀ * b)ᵀ‖) (y := ‖L₁ - (X₁ᵀ * e) * bᵀ‖) (ks := ‖K₁‖) (s2 := ‖S₂‖)
    (pn := ‖perp X₁ e‖) hρ.pos (hρ.pos.le.trans hρ.le) (div_pos hε hh) hτ1 (by positivity)
    (norm_pos_iff.2 hb) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) rfl rfl rfl rfl rfl rfl
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hs.kStep_le hρ hV hF hh hε) hs.perp_le h3
    (hs.sStep_le hρ hV hF hh hε) h5 (hs.lStep_le hρ hV hF hh hε)
  rw [IsIMEXKSLStep.sub_eq]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul_of_orthonormal hs.orthonormal, norm_mul_transpose_unit]
  refine hmain.trans (le_of_eq ?_)
  simp only [apConst]
  ring

end Bounds

section WellPosed

variable {ρ : m → ℝ} {ρ₀ ρ₁ : ℝ}

lemma upper_stiffness {p : Type*} [Fintype p] (hρ : IsCrossSection ρ ρ₀ ρ₁)
    {Y : Matrix m r ℝ} (hY : Yᵀ * Y = 1) (Z : Matrix r p ℝ) :
    ⟪stiffness ρ Y * Z, Z⟫ ≤ ρ₁ * ‖Z‖ ^ 2 := by
  have h : ⟪stiffness ρ Y * Z, Z⟫ = ⟪Matrix.diagonal ρ * (Y * Z), Y * Z⟫ := by
    rw [stiffness, Matrix.mul_assoc, Matrix.mul_assoc, inner_mul_left, Matrix.transpose_transpose,
      inner_mul_right']
  rw [h, ← norm_mul_of_orthonormal hY Z]
  exact hρ.upper_inner _

omit [DecidableEq m] [Fintype m] in
lemma isUnit_of_coercive' {A : Matrix r r ℝ} {c : ℝ} (hc : 0 < c)
    (hA : ∀ Z : Matrix r Unit ℝ, c * ‖Z‖ ^ 2 ≤ ⟪A * Z, Z⟫) : IsUnit A := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  set Z : Matrix r Unit ℝ := Matrix.of (fun i (_ : Unit) => x i - y i) with hZ
  have hz : A * Z = 0 := by
    ext i j
    have h := congrFun hxy i
    rw [Matrix.zero_apply, Matrix.mul_apply]
    simp only [hZ, Matrix.of_apply, Matrix.mulVec, dotProduct] at h ⊢
    simp only [mul_sub, Finset.sum_sub_distrib, h, sub_self]
  have h := le_norm_of_coercive (hA Z)
  rw [hz, norm_zero] at h
  have hz0 : Z = 0 := by
    have h2 : ‖Z‖ ≤ 0 := by
      by_contra hne
      have hne' := not_le.1 hne
      nlinarith
    exact norm_le_zero_iff.1 h2
  ext i
  have := congrFun (congrFun hz0 i) ()
  simpa [hZ, sub_eq_zero] using this

/-- **Solvability of the S-step of Sec. 4.1 of arXiv 2101.07104**: the matrix `I - (Δt / ε) R` is
invertible if `Δt ρ_min > ε` or `Δt ρ_max < ε`. In the range `ρ_min ≤ ε / Δt ≤ ρ_max` it can be
singular, see `not_exists_imexKSLStep`; the paper does not comment on this. -/
theorem isUnit_one_sub_stiffness (hρ : IsCrossSection ρ ρ₀ ρ₁) {Y : Matrix m r ℝ}
    (hY : Yᵀ * Y = 1) {s : ℝ} (hs : 1 < s * ρ₀ ∨ s * ρ₁ < 1 ∧ 0 ≤ s) :
    IsUnit (1 - s • stiffness ρ Y) := by
  rcases hs with hs | ⟨hs, hs0⟩
  · have h0 := hρ.pos
    have hs0 : 0 < s := by
      by_contra hne
      have hne' := not_lt.1 hne
      nlinarith
    have h1 : IsUnit (s • stiffness ρ Y - 1) := by
      refine isUnit_of_coercive' (c := s * ρ₀ - 1) (by linarith) fun Z => ?_
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, inner_sub_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      have := mul_le_mul_of_nonneg_left (hρ.lower_stiffness hY Z) hs0.le
      nlinarith
    have h2 : 1 - s • stiffness ρ Y = -(s • stiffness ρ Y - 1) := by abel
    rw [h2]
    exact h1.neg
  · refine isUnit_of_coercive' (c := 1 - s * ρ₁) (by linarith) fun Z => ?_
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    have := mul_le_mul_of_nonneg_left (upper_stiffness hρ hY Z) hs0
    nlinarith

/-- **Well-posedness of the scheme of arXiv 2101.07104, Sec. 4.1, at small `ε`**: for `ε < h ρ₀` and
`r ≤ m`, every input has an
IMEX KSL step, so `IsIMEXKSLStep.ap_step_le` is not vacuous. -/
theorem exists_isIMEXKSLStep {k : ℕ} (hk : k ≤ Fintype.card m) {n' : Type*} [Fintype n']
    (hρ : IsCrossSection ρ ρ₀ ρ₁) (e : Matrix m Unit ℝ) (b : Matrix n' Unit ℝ)
    (F : Matrix m n' ℝ → Matrix m n' ℝ) {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (hτ : ε < h * ρ₀)
    (K₀ : Matrix m (Fin k) ℝ) (V : Matrix n' (Fin k) ℝ) :
    ∃ K₁ X₁ S₁ S₂ L₁, IsIMEXKSLStep ρ e b F h ε K₀ V K₁ X₁ S₁ S₂ L₁ := by
  set s := h / ε with hs
  have hs0 : 0 < s := div_pos hh hε
  set rk := K₀ + h • (F (K₀ * Vᵀ) * V) + s • (Matrix.diagonal ρ * (e * (Vᵀ * b)ᵀ)) with hrk
  have hd : ∀ i, 1 + s * ρ i ≠ 0 := fun i => by
    have := hρ.pos.trans_le (hρ.lower i)
    positivity
  set K₁ := Matrix.diagonal (fun i => (1 + s * ρ i)⁻¹) * rk with hK₁
  have hKeq : K₁ + s • (Matrix.diagonal ρ * K₁) = rk := by
    have h1 : K₁ + s • (Matrix.diagonal ρ * K₁) =
        Matrix.diagonal (fun i => 1 + s * ρ i) * K₁ := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_mul, smul_eq_mul]
      ring
    rw [h1, hK₁, ← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    simp only [mul_inv_cancel₀ (hd _), Matrix.diagonal_one, Matrix.one_mul]
  obtain ⟨X₁, hX, hcap⟩ := LeanDLRA.MatrixBUG.exists_qr hk K₁
  have hqr : K₁ = X₁ * (X₁ᵀ * K₁) := by rw [← Matrix.mul_assoc, hcap]
  have hsρ : 1 < s * ρ₀ := by
    rw [hs, div_mul_eq_mul_div, lt_div_iff₀ hε]
    linarith
  set R := stiffness ρ X₁ with hR
  have hu₁ := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_one_sub_stiffness hρ hX (Or.inl hsρ))
  have hu₂ := (Matrix.isUnit_iff_isUnit_det _).1 (hρ.isUnit_one_add_stiffness hX hs0.le)
  set rS := X₁ᵀ * K₁ - h • (X₁ᵀ * F (X₁ * (X₁ᵀ * K₁) * Vᵀ) * V) -
    s • (X₁ᵀ * (Matrix.diagonal ρ * e) * (Vᵀ * b)ᵀ) with hrS
  set S₂ := (1 - s • R)⁻¹ * rS with hS₂
  have hS : S₂ - s • (R * S₂) = rS := by
    have h1 : S₂ - s • (R * S₂) = (1 - s • R) * S₂ := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [h1, hS₂, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu₁, Matrix.one_mul]
  set rL := S₂ * Vᵀ + h • (X₁ᵀ * F (X₁ * (S₂ * Vᵀ))) +
    s • (X₁ᵀ * (Matrix.diagonal ρ * e) * bᵀ) with hrL
  set L₁ := (1 + s • R)⁻¹ * rL with hL₁
  have hL : L₁ + s • (R * L₁) = rL := by
    have h1 : L₁ + s • (R * L₁) = (1 + s • R) * L₁ := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [h1, hL₁, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu₂, Matrix.one_mul]
  exact ⟨K₁, X₁, X₁ᵀ * K₁, S₂, L₁, hKeq, hX, hqr, hS, hL⟩

end WellPosed

section Rank

variable {d : ℕ}

omit [Fintype m] [DecidableEq m] [DecidableEq r] in
/-- **The low-rank structure of Sec. 3 of arXiv 2101.07104, (3.3), for `T = 1`**: on a grid, the
first-order expansion `1 - (ε / ρ) 𝓜`, with `𝓜 = M₁ + v · M₂ + (v ⊗ v) : M₃` as in (4.6), has rank
at most `2 + d + d²`, for all coefficients `M₁, M₂, M₃`, as the paper argues (a sum of products of
functions of `x` and of `v`). -/
theorem rank_firstOrder_le (ρ : m → ℝ) (ε : ℝ) (c₁ : m → ℝ) (c₂ : m → Vel d)
    (c₃ : m → Fin d → Fin d → ℝ) (v : n → Vel d) :
    (Matrix.of fun i j => 1 - ε / ρ i * calM (c₁ i) (c₂ i) (c₃ i) (v j)).rank ≤ 2 + d + d * d := by
  classical
  set A : Matrix m (Unit ⊕ (Unit ⊕ (Fin d ⊕ (Fin d × Fin d)))) ℝ := Matrix.of fun i k =>
    match k with
    | Sum.inl _ => 1
    | Sum.inr (Sum.inl _) => -(ε / ρ i * c₁ i)
    | Sum.inr (Sum.inr (Sum.inl a)) => -(ε / ρ i * c₂ i a)
    | Sum.inr (Sum.inr (Sum.inr p)) => -(ε / ρ i * c₃ i p.1 p.2) with hA
  set B : Matrix (Unit ⊕ (Unit ⊕ (Fin d ⊕ (Fin d × Fin d)))) n ℝ := Matrix.of fun k j =>
    match k with
    | Sum.inl _ => 1
    | Sum.inr (Sum.inl _) => 1
    | Sum.inr (Sum.inr (Sum.inl a)) => v j a
    | Sum.inr (Sum.inr (Sum.inr p)) => v j p.1 * v j p.2 with hB
  have h : (Matrix.of fun i j => 1 - ε / ρ i * calM (c₁ i) (c₂ i) (c₃ i) (v j)) = A * B := by
    ext i j
    have e1 : ∑ a, -(ε / ρ i * c₂ i a) * v j a = -(ε / ρ i * ∑ a, v j a * c₂ i a) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    have e2 : ∑ a, ∑ b, -(ε / ρ i * c₃ i a b) * (v j a * v j b) =
        -(ε / ρ i * ∑ a, ∑ b, v j a * v j b * c₃ i a b) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    have e3 : ⟪v j, c₂ i⟫ = ∑ a, v j a * c₂ i a := inner_eq_sum _ _
    simp only [Matrix.of_apply, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, hA,
      hB, calM, e3, Finset.univ_unique, Finset.sum_singleton]
    rw [e1, e2]
    ring
  rw [h]
  refine (Matrix.rank_mul_le_left A B).trans ((Matrix.rank_le_card_width A).trans (le_of_eq ?_))
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_prod, Fintype.card_fin]
  ring

end Rank

section Galerkin

variable {ρ : m → ℝ} {ρ₀ ρ₁ : ℝ} {e : Matrix m Unit ℝ} {b : Matrix n Unit ℝ}
  {F : Matrix m n ℝ → Matrix m n ℝ} {h ε : ℝ} {K₀ K₁ X₁ : Matrix m r ℝ} {V : Matrix n r ℝ}
  {S₁ S₂ : Matrix r r ℝ} {L₀ L₁ : Matrix r n ℝ}

omit [Fintype m] [DecidableEq m] in
private lemma mul_transpose_inj {p : Type*} (hV : Vᵀ * V = 1)
    {Z W : Matrix p r ℝ} (h : Z * Vᵀ = W * Vᵀ) : Z = W := by
  have := congrArg (fun Y : Matrix p n ℝ => Y * V) h
  simpa only [Matrix.mul_assoc, hV, Matrix.mul_one] using this

/-- **The K-step of `IsIMEXKSLStep` is the implicit-explicit Euler step of the first term of
(3.7) of arXiv 2101.07104**, `g¹ = g⁰ + h Q (F g⁰ + (1/ε) ρ (1 - g¹))` with `Q = V Vᵀ`, by the
resolvent commutation `imex_iff_resolvent`: `Q` acts in velocity and the relaxation in position. -/
theorem kStep_iff_imex (hρ : IsCrossSection ρ ρ₀ ρ₁) (hV : Vᵀ * V = 1) (hh : 0 ≤ h) (hε : 0 < ε) :
    K₁ + (h / ε) • (Matrix.diagonal ρ * K₁) =
        K₀ + h • (F (K₀ * Vᵀ) * V) + (h / ε) • (Matrix.diagonal ρ * (e * (Vᵀ * b)ᵀ)) ↔
      K₁ * Vᵀ = K₀ * Vᵀ + h • rightProj V (F (K₀ * Vᵀ) + (1 / ε) • (Matrix.diagonal ρ * (e * bᵀ)) -
        (1 / ε) • (Matrix.diagonal ρ * (K₁ * Vᵀ))) := by
  set D := Matrix.diagonal ρ with hD
  set S : Matrix m n ℝ →L[ℝ] Matrix m n ℝ := (1 / ε) • leftMulCLM D with hS
  have hSa : ∀ y, S y = (1 / ε) • (D * y) := fun y => rfl
  have hQ : ∀ y, rightProj (m := m) V (rightProj V y) = rightProj V y :=
    (isOrthProj_rightProj (m := m) hV).idem
  have hcomm : ∀ y, rightProj (m := m) V (S y) = S (rightProj V y) := fun y => by
    simp only [hSa, rightProj_apply, Matrix.smul_mul, Matrix.mul_assoc]
  have hinj : ∀ y, y + h • S y = 0 → y = 0 := fun y hy => by
    have h1 : (1 : ℝ) * ‖y‖ ^ 2 ≤ ⟪y + h • S y, y⟫ := by
      rw [inner_add_left, real_inner_self_eq_norm_sq, real_inner_smul_left, hSa,
        real_inner_smul_left]
      have h2 := hρ.lower_inner y
      have h3 := hρ.pos
      have h4 : 0 ≤ ⟪D * y, y⟫ := le_trans (by positivity) h2
      have h5 : 0 ≤ h * (1 / ε * ⟪D * y, y⟫) := by positivity
      linarith
    have h2 := le_norm_of_coercive h1
    rw [hy, norm_zero, one_mul] at h2
    exact norm_le_zero_iff.1 h2
  have hY₀ : rightProj (m := m) V (K₀ * Vᵀ) = K₀ * Vᵀ := by
    rw [rightProj_apply, Matrix.mul_assoc K₀, hV, Matrix.mul_one]
  have key := imex_iff_resolvent (Q := (rightProj (m := m) V : _ →L[ℝ] _).toLinearMap)
    (S := S.toLinearMap) hQ hcomm hinj (fun Y => F Y + (1 / ε) • (D * (e * bᵀ))) hY₀
    (Y₁ := K₁ * Vᵀ)
  simp only [ContinuousLinearMap.coe_coe, hSa] at key
  rw [key]
  have hid : ((K₁ + (h / ε) • (D * K₁)) * Vᵀ =
      (K₀ + h • (F (K₀ * Vᵀ) * V) + (h / ε) • (D * (e * (Vᵀ * b)ᵀ))) * Vᵀ) ↔
      K₁ * Vᵀ + h • (1 / ε) • (D * (K₁ * Vᵀ)) =
        K₀ * Vᵀ + h • rightProj (m := m) V (F (K₀ * Vᵀ) + (1 / ε) • (D * (e * bᵀ))) := by
    have h1 : (h / ε) = h * (1 / ε) := by ring
    rw [rightProj_apply]
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.transpose_mul,
      Matrix.transpose_transpose, h1, smul_add, smul_smul, add_assoc]
  rw [← hid]
  exact ⟨fun h1 => by rw [h1], fun h1 => mul_transpose_inj hV h1⟩

/-- **The S-step of `IsIMEXKSLStep` is the backward implicit-explicit Euler step of the second term
of (3.7) of arXiv 2101.07104**, for the Galerkin operator `P = X₁ X₁ᵀ ⊗ V Vᵀ`. -/
theorem sStep_iff_imex (hX : X₁ᵀ * X₁ = 1) (hV : Vᵀ * V = 1) :
    S₂ - (h / ε) • (stiffness ρ X₁ * S₂) =
        S₁ - h • (X₁ᵀ * F (X₁ * S₁ * Vᵀ) * V) -
          (h / ε) • (X₁ᵀ * (Matrix.diagonal ρ * e) * (Vᵀ * b)ᵀ) ↔
      X₁ * S₂ * Vᵀ = X₁ * S₁ * Vᵀ - h • leftProj X₁ (rightProj V (F (X₁ * S₁ * Vᵀ) +
        (1 / ε) • (Matrix.diagonal ρ * (e * bᵀ - X₁ * S₂ * Vᵀ)))) := by
  have h1 : (h / ε) = h * (1 / ε) := by ring
  have h2 : Matrix.diagonal ρ * (X₁ * S₂ * Vᵀ) * V * Vᵀ = Matrix.diagonal ρ * (X₁ * S₂ * Vᵀ) := by
    simp only [Matrix.mul_assoc, hV, Matrix.mul_one]
  have key : X₁ * (S₂ - (h / ε) • (stiffness ρ X₁ * S₂)) * Vᵀ -
        X₁ * (S₁ - h • (X₁ᵀ * F (X₁ * S₁ * Vᵀ) * V) -
          (h / ε) • (X₁ᵀ * (Matrix.diagonal ρ * e) * (Vᵀ * b)ᵀ)) * Vᵀ =
      X₁ * S₂ * Vᵀ - (X₁ * S₁ * Vᵀ - h • leftProj X₁ (rightProj V (F (X₁ * S₁ * Vᵀ) +
        (1 / ε) • (Matrix.diagonal ρ * (e * bᵀ - X₁ * S₂ * Vᵀ))))) := by
    rw [rightProj_apply, leftProj_apply]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_assoc, stiffness, Matrix.transpose_mul,
      Matrix.transpose_transpose, h1, smul_add, smul_sub, smul_smul, hV, Matrix.mul_one]
    abel
  constructor
  · intro h3
    rw [h3, sub_self] at key
    exact (sub_eq_zero.1 key.symm)
  · intro h3
    have h4 := sub_eq_zero.2 h3
    rw [← key, sub_eq_zero] at h4
    have h5 := mul_transpose_inj hV h4
    have h6 := congrArg (fun Z : Matrix m r ℝ => X₁ᵀ * Z) h5
    simpa only [← Matrix.mul_assoc, hX, Matrix.one_mul] using h6

/-- **The L-step of `IsIMEXKSLStep` is the implicit-explicit Euler step of the third term of
(3.7) of arXiv 2101.07104**, for the Galerkin operator `X₁ X₁ᵀ`. Here `X₁ᵀ ρ X₁` cannot be avoided:
unlike in the K-step, the projector does not commute with the relaxation. -/
theorem lStep_iff_imex (hX : X₁ᵀ * X₁ = 1) :
    L₁ + (h / ε) • (stiffness ρ X₁ * L₁) =
        L₀ + h • (X₁ᵀ * F (X₁ * L₀)) + (h / ε) • (X₁ᵀ * (Matrix.diagonal ρ * e) * bᵀ) ↔
      X₁ * L₁ = X₁ * L₀ + h • leftProj X₁ (F (X₁ * L₀) +
        (1 / ε) • (Matrix.diagonal ρ * (e * bᵀ - X₁ * L₁))) := by
  have h1 : (h / ε) = h * (1 / ε) := by ring
  have key : X₁ * (L₁ + (h / ε) • (stiffness ρ X₁ * L₁)) -
        X₁ * (L₀ + h • (X₁ᵀ * F (X₁ * L₀)) + (h / ε) • (X₁ᵀ * (Matrix.diagonal ρ * e) * bᵀ)) =
      X₁ * L₁ - (X₁ * L₀ + h • leftProj X₁ (F (X₁ * L₀) +
        (1 / ε) • (Matrix.diagonal ρ * (e * bᵀ - X₁ * L₁)))) := by
    rw [leftProj_apply]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_assoc, stiffness, h1,
      smul_add, smul_sub, smul_smul]
    abel
  constructor
  · intro h3
    rw [h3, sub_self] at key
    exact (sub_eq_zero.1 key.symm)
  · intro h3
    have h4 := sub_eq_zero.2 h3
    rw [← key, sub_eq_zero] at h4
    have h6 := congrArg (fun Z : Matrix m n ℝ => X₁ᵀ * Z) h4
    simpa only [← Matrix.mul_assoc, hX, Matrix.one_mul] using h6

end Galerkin

section Counterexamples

/-- The grid function `1` on two grid points. -/
def ones : Matrix (Fin 2) Unit ℝ := Matrix.of fun _ _ => 1

/-- The velocity basis of mean zero, `(1, -1) / √2`. -/
noncomputable def meanZero : Matrix (Fin 2) (Fin 1) ℝ :=
  Matrix.of fun i _ => (if i = 0 then 1 else -1) / √2

/-- The input `K₀ = (1, 0)ᵀ`. -/
def firstCell : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun i _ => if i = 0 then 1 else 0

lemma meanZero_orthonormal : meanZeroᵀ * meanZero = 1 := by
  have h2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : √(2 : ℝ) ≠ 0 := by positivity
  ext i j
  fin_cases i
  fin_cases j
  simp only [meanZero, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Fin.sum_univ_two,
    Matrix.one_apply]
  simp
  field_simp
  rw [h2]
  norm_num

lemma meanZero_mean : meanZeroᵀ * ones = 0 := by
  ext i j
  simp only [meanZero, ones, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Fin.sum_univ_two, Matrix.zero_apply, Fin.isValue, ite_true, one_ne_zero, ite_false, mul_one]
  ring

/-- **Asymptotic preservation fails without `V̄ ≠ 0`** (the hypothesis of
`IsIMEXKSLStep.ap_step_le`, not stated in arXiv 2101.07104, Sec. 6): for constant density, zero
explicit term and a velocity basis of mean zero, every step of the scheme has
`‖g¹ - 1‖ ≥ 1`, for all `h`, `ε`. The K-step loses the constant direction, and `X₁` keeps the
direction of `K₀`, which does not contain the constant `1` of the position grid. So the expansion
`g = 1 + O(ε)` used for (6.3) is false in general, and steps exist (`exists_isIMEXKSLStep`) for all
`ε < h`. -/
theorem not_ap_of_mean_zero {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    {K₁ X₁ : Matrix (Fin 2) (Fin 1) ℝ} {S₁ S₂ : Matrix (Fin 1) (Fin 1) ℝ}
    {L₁ : Matrix (Fin 1) (Fin 2) ℝ}
    (hs : IsIMEXKSLStep (fun _ => (1 : ℝ)) ones ones (fun _ => 0) h ε firstCell meanZero K₁ X₁ S₁ S₂
      L₁) :
    1 ≤ ‖X₁ * L₁ - ones * onesᵀ‖ := by
  have hk := hs.kStep
  rw [meanZero_mean] at hk
  have hs0 : 0 < h / ε := div_pos hh hε
  have h1 : ∀ i j, (1 + h / ε) * K₁ i j = firstCell i j := fun i j => by
    have := congrFun (congrFun hk i) j
    simp [Matrix.diagonal_one] at this
    linarith
  have h2 : K₁ 1 0 = 0 := by
    have h3 := h1 1 0
    have h4 : firstCell 1 0 = 0 := by simp [firstCell]
    rw [h4] at h3
    exact (mul_eq_zero.1 h3).resolve_left (by positivity)
  have h3 : K₁ 0 0 ≠ 0 := fun h4 => by
    have := h1 0 0
    simp [firstCell, h4] at this
  have hqr : ∀ i, K₁ i 0 = X₁ i 0 * S₁ 0 0 := fun i => by
    have := congrFun (congrFun hs.qr i) 0
    simpa [Matrix.mul_apply] using this
  have hS₁ : S₁ 0 0 ≠ 0 := fun h4 => h3 (by rw [hqr, h4, mul_zero])
  have hX : X₁ 1 0 = 0 := by
    have := hqr 1
    rw [h2] at this
    exact (mul_eq_zero.1 this.symm).resolve_right hS₁
  have h4 := abs_apply_le_norm (X₁ * L₁ - ones * onesᵀ) 1 0
  have h5 : (X₁ * L₁ - ones * onesᵀ) 1 0 = -1 := by
    simp [Matrix.mul_apply, hX, ones]
  rw [h5] at h4
  simpa using h4

/-- Non-vacuity of `not_ap_of_mean_zero`: for `ε < h` these steps exist. -/
example {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (hτ : ε < h) :
    ∃ K₁ X₁ S₁ S₂ L₁, IsIMEXKSLStep (fun _ : Fin 2 => (1 : ℝ)) ones ones (fun _ => 0) h ε firstCell
      meanZero K₁ X₁ S₁ S₂ L₁ :=
  exists_isIMEXKSLStep (ρ₀ := 1) (ρ₁ := 1) (by simp)
    ⟨one_pos, le_rfl, fun _ => le_rfl, fun _ => le_rfl⟩ ones ones _ hh hε (by simpa using hτ)
    firstCell meanZero

/-- The grid function `1` on one grid point. -/
def one₁ : Matrix (Fin 1) Unit ℝ := Matrix.of fun _ _ => 1

/-- **The S-step of Sec. 4.1 of arXiv 2101.07104 can have no solution**: with `ρ = 1` and
`Δt = ε`, the matrix `I - (Δt / ε) R` vanishes, and the scheme has no step at all for the input
`g = 0`. See `isUnit_one_sub_stiffness` for the range in which the S-step is solvable. -/
theorem not_exists_imexKSLStep {h : ℝ} (hh : 0 < h) :
    ¬ ∃ (K₁ X₁ : Matrix (Fin 1) (Fin 1) ℝ) (S₁ S₂ : Matrix (Fin 1) (Fin 1) ℝ)
      (L₁ : Matrix (Fin 1) (Fin 1) ℝ),
      IsIMEXKSLStep (fun _ => (1 : ℝ)) one₁ one₁ (fun _ => 0) h h 0 1 K₁ X₁ S₁ S₂ L₁ := by
  rintro ⟨K₁, X₁, S₁, S₂, L₁, hs⟩
  have hdiv : h / h = 1 := div_self hh.ne'
  have hk := congrFun (congrFun hs.kStep 0) 0
  have hX := congrFun (congrFun hs.orthonormal 0) 0
  have hq := congrFun (congrFun hs.qr 0) 0
  have hS := congrFun (congrFun hs.sStep 0) 0
  replace hk : K₁ 0 0 + K₁ 0 0 = 1 := by
    simpa [hdiv, one₁, Matrix.mul_apply, Matrix.diagonal_one] using hk
  replace hX : X₁ 0 0 * X₁ 0 0 = 1 := by simpa [Matrix.mul_apply] using hX
  replace hq : K₁ 0 0 = X₁ 0 0 * S₁ 0 0 := by simpa [Matrix.mul_apply] using hq
  replace hS : S₂ 0 0 - X₁ 0 0 * X₁ 0 0 * S₂ 0 0 = S₁ 0 0 - X₁ 0 0 := by
    simpa [hdiv, one₁, Matrix.mul_apply, stiffness, Matrix.diagonal_one] using hS
  rw [hX, one_mul, sub_self] at hS
  have h1 : S₁ 0 0 = X₁ 0 0 := by linarith
  rw [h1, hX] at hq
  linarith

/-- Non-vacuity of `IsIMEXKSLStep.ap_step_le`: a basis with non-zero mean. -/
example : ∃ (V : Matrix (Fin 1) (Fin 1) ℝ) (b : Matrix (Fin 1) Unit ℝ),
    Vᵀ * V = 1 ∧ Vᵀ * b ≠ 0 :=
  ⟨1, one₁, by simp, fun h => by simpa [one₁] using congrFun (congrFun h 0) ()⟩

end Counterexamples

end KSL

end LeanDLRA.Literature.P2101_07104
