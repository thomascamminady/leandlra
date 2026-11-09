import Mathlib
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2411.06844: Stable multiplicative DLRA for linear Boltzmann-BGK

This module formalises the fully discrete schemes of Baumann, Einkemmer, Klingenberg and Kusch for
`f = M g` on the periodic grid `ZMod N`, with the concrete stencils `Dx`, `Dxx`, `Dp`, velocity
nodes `v` and weights `ω`, as operators whose entries agree with the paper's matrices for `N ≥ 3`;
`Δx > 0` is arbitrary instead of `1 / N_x`. It proves Lemma 1 (`sum_mul_Dx`, `sum_mul_Dx_self`,
`sum_mul_Dxx`, `sum_mul_Dxx_self`), Lemma 2 (`normalized_step`, `lemma2_normalized`), Lemma 3
(`lemma3_cfl`, through the upwind form in place of the Fourier transform), Theorem 1
(`naive_step_eq9`, `theorem1_naive_unstable`, `centered_mode_growth`), and Theorem 2
(`theorem2_step`, `theorem2_trajectory`, with solvability and positivity of the scheme in
`isConservativeStep_gNext`, `positive_step`, `consIter_spec`). Two claims of the paper are
corrected. First, the proofs of Lemma 2 and Theorem 2 use `QuadNormalized`, `(1/√(2π)) Σ_k ω_k
e^{v_k²/2} = 1`, which the paper does not list and which fails for the Gauss-Hermite weights of
`e^{-v²}` named in Sec. 3.1 (`gaussHermite_one_point`, `lemma2_fails_gaussHermite`,
`gaussHermite_three_point_not_quadNormalized`); for `σ > 0` it is necessary
(`quadNormalized_of_normalized`, `conservative_needs_quadNormalized`), as is the initial
normalization (`conservative_needs_normalized`), and it holds when `ω_k e^{v_k²/2} / √(2π)` are
the weights of a Gauss-Hermite rule for `e^{-v²/2}`. Second, **Theorem 3 is false**. It fails
for weights satisfying `QuadNormalized` (`theorem3_false`): one step of (15), without truncation,
under the CFL condition, increases the `ℋ`-norm from `g ≡ 1`, with the three-point Gauss-Hermite
rule of `e^{-v²/2}`, for which Lemma 2 and Theorem 2 hold. It also fails for the printed weights,
the three-point Gauss-Hermite rule of `e^{-v²}` (`gaussHermite_three_point`):
`theorem3_false_gaussHermite`, one step of (15) with `σ = 0`, `Δx = 1/N_x`, a positive rank-one
state satisfying (11), and spatial spaces of the full dimensions `2r`, `4r`. The equalities that
the proof deduces from the augmentations (15c), (15e) fail (`ce_displayed_equality_fails`),
because the S-step output lies in `𝒳̂̂`, not in `X̂`. What remains true is formalised on the
scheme in projector form `IsDLRAStep`: the mass relation (`IsDLRAStep.normalized`), the energy
estimate given those equalities (`dlra_stable_of_equalities`), stability when the augmented spaces
are invariant under the weights (`dlra_stable_of_invariant`, `dlra_stable_of_scalar_weights`), and
stability of an `ℋ`-orthogonal Galerkin step (`hGalerkin_stable`). For `ϑ > 0` the Euclidean
truncation is only used through `IsMassTruncation`, and its `ℋ`-norm behaviour is a hypothesis.
Not treated: the two-dimensional setting, and the simplified rank-`2r` scheme of Section 6.1, for
which the paper claims no theorem.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2411_06844

/-! ### Periodic stencils and Lemma 1 -/

section Stencils

variable {N : ℕ} [NeZero N]

/-- The central difference `(D^x z)_j = Σ_i D^x_{ji} z_i = (z_{j+1} - z_{j-1}) / (2 Δx)`. -/
noncomputable def Dx (dx : ℝ) (z : ZMod N → ℝ) (j : ZMod N) : ℝ :=
  (z (j + 1) - z (j - 1)) / (2 * dx)

/-- The stabilisation `(D^{xx} z)_j = (z_{j+1} - 2 z_j + z_{j-1}) / Δx²`. -/
noncomputable def Dxx (dx : ℝ) (z : ZMod N → ℝ) (j : ZMod N) : ℝ :=
  (z (j + 1) - 2 * z j + z (j - 1)) / dx ^ 2

/-- The forward difference `(D^+ z)_j = (z_{j+1} - z_j) / Δx`. -/
noncomputable def Dp (dx : ℝ) (z : ZMod N → ℝ) (j : ZMod N) : ℝ :=
  (z (j + 1) - z j) / dx

private lemma sum_shift_succ (h : ZMod N → ℝ) : ∑ j, h (j + 1) = ∑ j, h j :=
  Equiv.sum_comp (Equiv.addRight 1) h

private lemma sum_shift_pred (h : ZMod N → ℝ) : ∑ j, h (j - 1) = ∑ j, h j :=
  Equiv.sum_comp (Equiv.subRight 1) h

private lemma sum_mul_pred (y z : ZMod N → ℝ) :
    ∑ j, y j * z (j - 1) = ∑ j, y (j + 1) * z j := by
  rw [← sum_shift_succ (fun j => y j * z (j - 1))]
  simp

/-- arXiv 2411.06844, Lemma 1, first identity: `D^x` is skew,
`Σ y_j D^x_{ji} z_i = - Σ z_j D^x_{ji} y_i`.  The grid is periodic and any `N ≥ 1` is allowed. -/
theorem sum_mul_Dx (dx : ℝ) (y z : ZMod N → ℝ) :
    ∑ j, y j * Dx dx z j = -∑ j, z j * Dx dx y j := by
  have h1 := sum_mul_pred y z
  have h2 := sum_mul_pred z y
  have e : ∀ (a b : ZMod N → ℝ), ∑ j, a j * Dx dx b j
      = (∑ j, a j * b (j + 1) - ∑ j, a j * b (j - 1)) / (2 * dx) := by
    intro a b
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Dx]
    ring
  rw [e, e, h1, h2]
  have h3 : ∑ j, z j * y (j + 1) = ∑ j, y (j + 1) * z j :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  have h4 : ∑ j, y j * z (j + 1) = ∑ j, z (j + 1) * y j :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [h3, h4]
  ring

/-- arXiv 2411.06844, Lemma 1, second identity: `Σ z_j D^x_{ji} z_i = 0`. -/
theorem sum_mul_Dx_self (dx : ℝ) (z : ZMod N → ℝ) : ∑ j, z j * Dx dx z j = 0 := by
  have := sum_mul_Dx dx z z
  linarith

/-- arXiv 2411.06844, Lemma 1, third identity: `D^{xx}` is symmetric. -/
theorem sum_mul_Dxx (dx : ℝ) (y z : ZMod N → ℝ) :
    ∑ j, y j * Dxx dx z j = ∑ j, z j * Dxx dx y j := by
  have h1 := sum_mul_pred y z
  have h2 := sum_mul_pred z y
  have e : ∀ (a b : ZMod N → ℝ), ∑ j, a j * Dxx dx b j
      = (∑ j, a j * b (j + 1) - 2 * ∑ j, a j * b j + ∑ j, a j * b (j - 1)) / dx ^ 2 := by
    intro a b
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Dxx]
    ring
  rw [e, e, h1, h2]
  have h3 : ∑ j, z j * y (j + 1) = ∑ j, y (j + 1) * z j :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  have h4 : ∑ j, y j * z (j + 1) = ∑ j, z (j + 1) * y j :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  have h5 : ∑ j, z j * y j = ∑ j, y j * z j :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [h3, h4, h5]
  ring

/-- arXiv 2411.06844, Lemma 1, last identity:
`Σ z_j D^{xx}_{ji} z_i = - Σ_j (Σ_i D^+_{ji} z_i)²`. -/
theorem sum_mul_Dxx_self (dx : ℝ) (z : ZMod N → ℝ) :
    ∑ j, z j * Dxx dx z j = -∑ j, Dp dx z j ^ 2 := by
  have h1 := sum_mul_pred z z
  have h2 : ∑ j, z (j + 1) ^ 2 = ∑ j, z j ^ 2 := sum_shift_succ fun j => z j ^ 2
  have e1 : ∑ j, z j * Dxx dx z j
      = (2 * ∑ j, z j * z (j + 1) - 2 * ∑ j, z j ^ 2) / dx ^ 2 := by
    have : ∑ j, z j * Dxx dx z j
        = (∑ j, z j * z (j + 1) - 2 * ∑ j, z j ^ 2 + ∑ j, z j * z (j - 1)) / dx ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Dxx]
      ring
    rw [this, h1]
    have h3 : ∑ j, z (j + 1) * z j = ∑ j, z j * z (j + 1) :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [h3]
    ring
  have e2 : ∑ j, Dp dx z j ^ 2
      = (∑ j, z (j + 1) ^ 2 - 2 * ∑ j, z j * z (j + 1) + ∑ j, z j ^ 2) / dx ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Dp]
    ring
  rw [e1, e2, h2]
  ring

/-- The combination `(D^x z) a - (Δx/2) (D^{xx} z) |a|` appearing in Lemma 3 and in the scheme: the
transport term of (8) is `-upw`. -/
noncomputable def upw (dx a : ℝ) (z : ZMod N → ℝ) (j : ZMod N) : ℝ :=
  Dx dx z j * a - dx / 2 * Dxx dx z j * |a|

omit [NeZero N] in
/-- The Fourier-free replacement for the diagonalisation in the proof of Lemma 3: `upw` is the
upwind difference, for `a ≥ 0` the backward one. -/
lemma upw_of_nonneg {dx a : ℝ} (hdx : dx ≠ 0) (ha : 0 ≤ a) (z : ZMod N → ℝ) (j : ZMod N) :
    upw dx a z j = a * Dp dx z (j - 1) := by
  simp only [upw, Dx, Dxx, Dp, abs_of_nonneg ha, sub_add_cancel]
  field_simp
  ring

omit [NeZero N] in
/-- For `a ≤ 0`, `upw` is the forward difference. -/
lemma upw_of_nonpos {dx a : ℝ} (hdx : dx ≠ 0) (ha : a ≤ 0) (z : ZMod N → ℝ) (j : ZMod N) :
    upw dx a z j = a * Dp dx z j := by
  simp only [upw, Dx, Dxx, Dp, abs_of_nonpos ha]
  field_simp
  ring

/-- The exact identity behind Lemma 3: `‖upw‖² = a² ‖D^+ z‖²`, using `‖D^- z‖ = ‖D^+ z‖`.
arXiv 2411.06844, Lemma 3, the identity replacing the Fourier analysis. -/
theorem sum_upw_sq {dx : ℝ} (hdx : dx ≠ 0) (a : ℝ) (z : ZMod N → ℝ) :
    ∑ j, upw dx a z j ^ 2 = a ^ 2 * ∑ j, Dp dx z j ^ 2 := by
  rcases le_total 0 a with ha | ha
  · rw [Finset.mul_sum, ← sum_shift_pred (fun j => a ^ 2 * Dp dx z j ^ 2)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [upw_of_nonneg hdx ha]
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [upw_of_nonpos hdx ha]
    ring

/-- `⟨z, upw z⟩ = (Δx/2) |a| ‖D^+ z‖²`, from Lemma 1.
arXiv 2411.06844, Lemma 1 applied to the transport term in the proof of Theorem 2. -/
theorem sum_mul_upw (dx a : ℝ) (z : ZMod N → ℝ) :
    ∑ j, z j * upw dx a z j = dx / 2 * |a| * ∑ j, Dp dx z j ^ 2 := by
  have h1 := sum_mul_Dx_self dx z
  have h2 := sum_mul_Dxx_self dx z
  have : ∑ j, z j * upw dx a z j
      = a * ∑ j, z j * Dx dx z j - dx / 2 * |a| * ∑ j, z j * Dxx dx z j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [upw]
    ring
  rw [this, h1, h2]
  ring

omit [NeZero N] in
/-- Under `|a| Δt ≤ Δx` the explicit upwind step keeps positivity (the scheme is monotone). -/
lemma upw_step_pos {dx dt a : ℝ} (hdx : 0 < dx) (hdt : 0 ≤ dt) (hcfl : |a| * dt ≤ dx)
    {z : ZMod N → ℝ} (hz : ∀ j, 0 < z j) (j : ZMod N) : 0 < z j - dt * upw dx a z j := by
  have hdx' := hdx.ne'
  have hl0 : 0 ≤ |a| * dt / dx := by positivity
  have hl1 : |a| * dt / dx ≤ 1 := (div_le_one hdx).2 hcfl
  rcases le_total 0 a with ha | ha
  · have e : z j - dt * upw dx a z j
        = (1 - |a| * dt / dx) * z j + |a| * dt / dx * z (j - 1) := by
      rw [upw_of_nonneg hdx' ha, abs_of_nonneg ha]
      simp only [Dp, sub_add_cancel]
      field_simp
      ring
    rw [e]
    rcases eq_or_lt_of_le hl1 with h | h
    · rw [h]
      have := hz (j - 1)
      linarith
    · have h1 : 0 < (1 - |a| * dt / dx) * z j := mul_pos (by linarith) (hz j)
      have h2 : 0 ≤ |a| * dt / dx * z (j - 1) := mul_nonneg hl0 (hz _).le
      linarith
  · have e : z j - dt * upw dx a z j
        = (1 - |a| * dt / dx) * z j + |a| * dt / dx * z (j + 1) := by
      rw [upw_of_nonpos hdx' ha, abs_of_nonpos ha]
      simp only [Dp]
      field_simp
      ring
    rw [e]
    rcases eq_or_lt_of_le hl1 with h | h
    · rw [h]
      have := hz (j + 1)
      linarith
    · have h1 : 0 < (1 - |a| * dt / dx) * z j := mul_pos (by linarith) (hz j)
      have h2 : 0 ≤ |a| * dt / dx * z (j + 1) := mul_nonneg hl0 (hz _).le
      linarith

omit [NeZero N] in
/-- The stencils are linear: scaling. -/
lemma upw_const_mul (dx a c : ℝ) (z : ZMod N → ℝ) (j : ZMod N) :
    upw dx a (fun i => c * z i) j = c * upw dx a z j := by
  simp only [upw, Dx, Dxx]
  ring

end Stencils

/-! ### Quadrature, `ℋ`-norm, the two fully discrete schemes -/

section Scheme

variable {N : ℕ} [NeZero N] {K : Type*} [Fintype K]

/-- The quadrature weights `Z_k = (1/√(2π)) ω_k e^{v_k²/2}` of Section 5.2. -/
noncomputable def quadZ (v ω : K → ℝ) (k : K) : ℝ :=
  1 / Real.sqrt (2 * Real.pi) * ω k * Real.exp (v k ^ 2 / 2)

/-- `‖F‖²_ℋ = √(2π) Σ_{j,k} F_{jk}² ω_k e^{3 v_k²/2}` (Definition 2). -/
noncomputable def hNormSq (v ω : K → ℝ) (F : ZMod N → K → ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi) * ∑ j, ∑ k, F j k ^ 2 * ω k * Real.exp (3 * v k ^ 2 / 2)

/-- `f_{jk} = (1/√(2π)) ρ_j g_{jk} e^{-v_k²/2}` (Definition 1). -/
noncomputable def fOf (v : K → ℝ) (ρ : ZMod N → ℝ) (g : ZMod N → K → ℝ) (j : ZMod N) (k : K) : ℝ :=
  1 / Real.sqrt (2 * Real.pi) * ρ j * g j k * Real.exp (-(v k ^ 2) / 2)

/-- The relation (11): `1 = (1/√(2π)) Σ_k g_{jk} ω_k e^{v_k²/2}` for every `j`. -/
def IsNormalized (v ω : K → ℝ) (g : ZMod N → K → ℝ) : Prop :=
  ∀ j, ∑ k, g j k * quadZ v ω k = 1

/-- The identity `(1/√(2π)) Σ_k ω_k e^{v_k²/2} = 1`, which the paper uses in the proof of Lemma 2
without listing it. See `gaussHermite_one_point`: Gauss-Hermite weights do not satisfy it. -/
def QuadNormalized (v ω : K → ℝ) : Prop := ∑ k, quadZ v ω k = 1

/-- The density update (7b) = (8b). -/
noncomputable def densityNext (dt dx : ℝ) (v ω : K → ℝ) (ρ : ZMod N → ℝ) (g : ZMod N → K → ℝ)
    (j : ZMod N) : ℝ :=
  ρ j - dt * (1 / Real.sqrt (2 * Real.pi)) *
      ∑ k, Dx dx (fun i => ρ i * g i k) j * v k * ω k * Real.exp (v k ^ 2 / 2)
    + dt * (dx / (2 * Real.sqrt (2 * Real.pi))) *
      ∑ k, Dxx dx (fun i => ρ i * g i k) j * |v k| * ω k * Real.exp (v k ^ 2 / 2)

/-- The conservative scheme (8a), (8b). -/
structure IsConservativeStep (σ dt dx : ℝ) (v ω : K → ℝ) (ρ : ZMod N → ℝ) (g : ZMod N → K → ℝ)
    (ρ' : ZMod N → ℝ) (g' : ZMod N → K → ℝ) : Prop where
  density : ∀ j, ρ' j = densityNext dt dx v ω ρ g j
  update : ∀ j k, g' j k = g j k
    - dt * (1 / ρ j) * Dx dx (fun i => ρ i * g i k) j * v k
    + dt * (dx / 2) * (1 / ρ j) * Dxx dx (fun i => ρ i * g i k) j * |v k|
    + σ * dt * (ρ' j / ρ j) * (1 - g' j k)
    - g' j k / ρ j * (ρ' j - ρ j)

/-- The naive advection-form scheme (7a), (7b). -/
structure IsNaiveStep (σ dt dx : ℝ) (v ω : K → ℝ) (ρ : ZMod N → ℝ) (g : ZMod N → K → ℝ)
    (ρ' : ZMod N → ℝ) (g' : ZMod N → K → ℝ) : Prop where
  density : ∀ j, ρ' j = densityNext dt dx v ω ρ g j
  update : ∀ j k, g' j k = g j k
    - dt * Dx dx (fun i => g i k) j * v k
    + dt * (dx / 2) * Dxx dx (fun i => g i k) j * |v k|
    + σ * dt * (1 - g' j k)
    - g' j k / ρ j * (ρ' j - ρ j)
    - dt * (g j k / ρ j) * Dx dx ρ j * v k

/-- `Σ_{j,k} u_{jk}² Z_k`: the `ℋ`-norm in the variables `u = ρ g`, see `hNormSq_fOf`. -/
noncomputable def zE (Z : K → ℝ) (u : ZMod N → K → ℝ) : ℝ := ∑ j, ∑ k, u j k ^ 2 * Z k

/-- The bilinear form of `zE`. -/
noncomputable def zI (Z : K → ℝ) (a b : ZMod N → K → ℝ) : ℝ := ∑ j, ∑ k, a j k * b j k * Z k

private lemma sqrt_two_pi_ne : Real.sqrt (2 * Real.pi) ≠ 0 :=
  (Real.sqrt_pos.2 (by positivity)).ne'

/-- `‖f‖²_ℋ = Σ_{j,k} (ρ_j g_{jk})² Z_k`: the Maxwellian factors cancel.
arXiv 2411.06844, Definitions 1 and 2. -/
theorem hNormSq_fOf (v ω : K → ℝ) (ρ : ZMod N → ℝ) (g : ZMod N → K → ℝ) :
    hNormSq v ω (fOf v ρ g) = zE (quadZ v ω) (fun j k => ρ j * g j k) := by
  simp only [hNormSq, zE, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have hs := sqrt_two_pi_ne
  have he : Real.exp (-(v k ^ 2) / 2) ^ 2 * Real.exp (3 * v k ^ 2 / 2)
      = Real.exp (v k ^ 2 / 2) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp only [fOf, quadZ]
  calc Real.sqrt (2 * Real.pi) * ((1 / Real.sqrt (2 * Real.pi) * ρ j * g j k *
          Real.exp (-(v k ^ 2) / 2)) ^ 2 * ω k * Real.exp (3 * v k ^ 2 / 2))
      = Real.sqrt (2 * Real.pi) * (1 / Real.sqrt (2 * Real.pi)) ^ 2 * (ρ j * g j k) ^ 2 * ω k *
          (Real.exp (-(v k ^ 2) / 2) ^ 2 * Real.exp (3 * v k ^ 2 / 2)) := by ring
    _ = (ρ j * g j k) ^ 2 * (1 / Real.sqrt (2 * Real.pi) * ω k * Real.exp (v k ^ 2 / 2)) := by
        rw [he]
        field_simp

/-- The Lemma 3 inequality for arbitrary nonnegative velocity weights.
arXiv 2411.06844, Lemma 3 with general weights. -/
theorem weighted_cfl {dt dx : ℝ} (hdx : 0 < dx) {v W : K → ℝ} (hW : ∀ k, 0 ≤ W k)
    (hcfl : ∀ k, |v k| * dt ≤ dx) (u : ZMod N → K → ℝ) :
    dt * ∑ k, W k * ∑ j, upw dx (v k) (fun i => u i k) j ^ 2
      ≤ dx * ∑ k, W k * |v k| * ∑ j, Dp dx (fun i => u i k) j ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [sum_upw_sq hdx.ne', ← sq_abs (v k)]
  have hP : 0 ≤ W k * ∑ j, Dp dx (fun i => u i k) j ^ 2 :=
    mul_nonneg (hW k) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have : |v k| * (|v k| * dt) * (W k * ∑ j, Dp dx (fun i => u i k) j ^ 2)
      ≤ |v k| * dx * (W k * ∑ j, Dp dx (fun i => u i k) j ^ 2) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcfl k) (abs_nonneg _)) hP
  nlinarith [this]

/-- **Lemma 3** (arXiv 2411.06844).  Under `max_k |v_k| Δt ≤ Δx`,
`Δt ‖D^x f diag(v) - (Δx/2) D^{xx} f diag(|v|)‖²_ℋ - Δx ‖D^+ f diag(|v|^{1/2})‖²_ℋ ≤ 0`.
The paper diagonalises the stencils by a discrete Fourier transform; here the upwind form
(`upw_of_nonneg`, `upw_of_nonpos`) and `‖D^- z‖ = ‖D^+ z‖` replace it. The weights only have to be
nonnegative and `Δx > 0`, and the CFL condition is stated as `∀ k, |v_k| Δt ≤ Δx`. -/
theorem lemma3_cfl {dt dx : ℝ} (hdx : 0 < dx) {v ω : K → ℝ} (hω : ∀ k, 0 ≤ ω k)
    (hcfl : ∀ k, |v k| * dt ≤ dx) (f : ZMod N → K → ℝ) :
    dt * hNormSq v ω (fun j k => Dx dx (fun i => f i k) j * v k
          - dx / 2 * Dxx dx (fun i => f i k) j * |v k|)
      - dx * hNormSq v ω (fun j k => Dp dx (fun i => f i k) j * Real.sqrt |v k|) ≤ 0 := by
  have hs : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  set W : K → ℝ := fun k => Real.sqrt (2 * Real.pi) * (ω k * Real.exp (3 * v k ^ 2 / 2)) with hWdef
  have hW : ∀ k, 0 ≤ W k := fun k =>
    mul_nonneg hs (mul_nonneg (hω k) (Real.exp_pos _).le)
  have h := weighted_cfl hdx hW hcfl f
  have e1 : hNormSq v ω (fun j k => Dx dx (fun i => f i k) j * v k
        - dx / 2 * Dxx dx (fun i => f i k) j * |v k|)
      = ∑ k, W k * ∑ j, upw dx (v k) (fun i => f i k) j ^ 2 := by
    rw [hNormSq, Finset.sum_comm]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [upw, hWdef]
    ring
  have e2 : hNormSq v ω (fun j k => Dp dx (fun i => f i k) j * Real.sqrt |v k|)
      = ∑ k, W k * |v k| * ∑ j, Dp dx (fun i => f i k) j ^ 2 := by
    rw [hNormSq, Finset.sum_comm]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
    simp only [hWdef]
    ring
  rw [e1, e2]
  linarith

/-- The energy argument of Theorem 2, in the variables `u = ρ g`: everything the proof needs is the
equation *tested with the new state* and the sign of the collision term.  This is why it also
applies to the Galerkin step of Theorem 3 whenever the test function is admissible.
arXiv 2411.06844, proof of Theorem 2. -/
theorem energy_core {σ dt dx : ℝ} (hσ : 0 ≤ σ) (hdt : 0 ≤ dt) (hdx : 0 < dx) {v Z : K → ℝ}
    (hZ : ∀ k, 0 ≤ Z k) (hcfl : ∀ k, |v k| * dt ≤ dx) {u u' m' : ZMod N → K → ℝ}
    (hweak : (1 + σ * dt) * zE Z u' = zI Z u' u
      - dt * zI Z u' (fun j k => upw dx (v k) (fun i => u i k) j) + σ * dt * zI Z u' m')
    (hcoll : zI Z u' m' ≤ zE Z u') : zE Z u' ≤ zE Z u := by
  set T : ZMod N → K → ℝ := fun j k => upw dx (v k) (fun i => u i k) j with hT
  have hexp : zE Z (fun j k => u' j k - u j k + dt * T j k)
      = zE Z u' + zE Z u + dt ^ 2 * zE Z T - 2 * zI Z u' u + 2 * dt * zI Z u' T
        - 2 * dt * zI Z u T := by
    simp only [zE, zI, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hnn : 0 ≤ zE Z (fun j k => u' j k - u j k + dt * T j k) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (sq_nonneg _) (hZ k)
  have hT2 : zE Z T = ∑ k, Z k * ∑ j, upw dx (v k) (fun i => u i k) j ^ 2 := by
    rw [zE, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hI : 2 * zI Z u T = dx * ∑ k, Z k * |v k| * ∑ j, Dp dx (fun i => u i k) j ^ 2 := by
    rw [zI, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := sum_mul_upw dx (v k) (fun i => u i k)
    calc 2 * ∑ j, u j k * T j k * Z k
        = 2 * Z k * ∑ j, u j k * upw dx (v k) (fun i => u i k) j := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [hT]; ring
      _ = dx * (Z k * |v k| * ∑ j, Dp dx (fun i => u i k) j ^ 2) := by rw [this]; ring
  have hcf : dt * zE Z T ≤ 2 * zI Z u T := by
    rw [hT2, hI]
    exact weighted_cfl hdx hZ hcfl u
  have h1 : dt * (dt * zE Z T) ≤ dt * (2 * zI Z u T) := mul_le_mul_of_nonneg_left hcf hdt
  have h2 : σ * dt * (zI Z u' m' - zE Z u') ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hσ hdt) (by linarith)
  nlinarith [h1, h2, hnn, hexp, hweak]

omit [NeZero N] in
/-- The density update in upwind form. -/
lemma densityNext_eq (dt dx : ℝ) (v ω : K → ℝ) (ρ : ZMod N → ℝ) (g : ZMod N → K → ℝ) (j : ZMod N) :
    densityNext dt dx v ω ρ g j
      = ρ j - dt * ∑ k, upw dx (v k) (fun i => ρ i * g i k) j * quadZ v ω k := by
  have : ∑ k, upw dx (v k) (fun i => ρ i * g i k) j * quadZ v ω k
      = (1 / Real.sqrt (2 * Real.pi)) *
          ∑ k, Dx dx (fun i => ρ i * g i k) j * v k * ω k * Real.exp (v k ^ 2 / 2)
        - (dx / (2 * Real.sqrt (2 * Real.pi))) *
          ∑ k, Dxx dx (fun i => ρ i * g i k) j * |v k| * ω k * Real.exp (v k ^ 2 / 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [upw, quadZ]
    ring
  rw [this, densityNext]
  ring

omit [NeZero N] in
/-- Equation (14a) in the form `(1 + σΔt) ρ' g' = ρ g - Δt upw(ρ g) + σΔt ρ'`, the first display of
the proofs of Lemma 2 and Theorem 2. -/
lemma IsConservativeStep.mul_form {σ dt dx : ℝ} {v ω : K → ℝ} {ρ ρ' : ZMod N → ℝ}
    {g g' : ZMod N → K → ℝ} (h : IsConservativeStep σ dt dx v ω ρ g ρ' g') (hρ : ∀ j, ρ j ≠ 0)
    (j : ZMod N) (k : K) :
    (1 + σ * dt) * (ρ' j * g' j k) = ρ j * g j k
      - dt * upw dx (v k) (fun i => ρ i * g i k) j + σ * dt * ρ' j := by
  have h1 := h.update j k
  have h2 := hρ j
  field_simp at h1
  simp only [upw]
  linear_combination (1 / 2 : ℝ) * h1

end Scheme

/-! ### Lemma 2 and Theorem 2 -/

section Stability

variable {N : ℕ} [NeZero N] {K : Type*} [Fintype K]
variable {σ dt dx : ℝ} {v ω : K → ℝ}

omit [NeZero N] in
/-- One step of **Lemma 2** (arXiv 2411.06844).  The relation (11) passes from `g` to `g'`.  The
identity `QuadNormalized` is used in the paper's proof without being assumed, and it fails for
Gauss-Hermite weights, see `lemma2_fails_gaussHermite`.  `1 + σΔt > 0` is needed to cancel. -/
theorem normalized_step (hm : QuadNormalized v ω) (hσ : 0 ≤ σ) (hdt : 0 ≤ dt)
    {ρ ρ' : ZMod N → ℝ} {g g' : ZMod N → K → ℝ} (hρ : ∀ j, ρ j ≠ 0) (hρ' : ∀ j, ρ' j ≠ 0)
    (h : IsConservativeStep σ dt dx v ω ρ g ρ' g') (hg : IsNormalized v ω g) :
    IsNormalized v ω g' := by
  intro j
  have hs : 1 + σ * dt ≠ 0 := by positivity
  have hd := h.density j
  rw [densityNext_eq] at hd
  have key : (1 + σ * dt) * ρ' j * ∑ k, g' j k * quadZ v ω k = (1 + σ * dt) * ρ' j := by
    calc (1 + σ * dt) * ρ' j * ∑ k, g' j k * quadZ v ω k
        = ∑ k, ((1 + σ * dt) * (ρ' j * g' j k)) * quadZ v ω k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ k, (ρ j * g j k - dt * upw dx (v k) (fun i => ρ i * g i k) j
            + σ * dt * ρ' j) * quadZ v ω k :=
          Finset.sum_congr rfl fun k _ => by rw [h.mul_form hρ]
      _ = ρ j * ∑ k, g j k * quadZ v ω k
            - dt * ∑ k, upw dx (v k) (fun i => ρ i * g i k) j * quadZ v ω k
            + σ * dt * ρ' j * ∑ k, quadZ v ω k := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
            ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = (1 + σ * dt) * ρ' j := by
          rw [hg j, hm]
          linarith
  exact mul_left_cancel₀ (mul_ne_zero hs (hρ' j)) (by rw [key, mul_one])

omit [NeZero N] in
/-- **Lemma 2** (arXiv 2411.06844).  If `g⁰` satisfies (11), so does every `gⁿ`.  Difference from
the paper: the hypothesis `QuadNormalized`, used silently there, is stated; positive densities are
part of the setting of the paper. -/
theorem lemma2_normalized (hm : QuadNormalized v ω) (hσ : 0 ≤ σ) (hdt : 0 ≤ dt)
    {ρ : ℕ → ZMod N → ℝ} {g : ℕ → ZMod N → K → ℝ} (hρ : ∀ n j, 0 < ρ n j)
    (h : ∀ n, IsConservativeStep σ dt dx v ω (ρ n) (g n) (ρ (n + 1)) (g (n + 1)))
    (h0 : IsNormalized v ω (g 0)) (n : ℕ) : IsNormalized v ω (g n) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    exact normalized_step hm hσ hdt (fun j => (hρ n j).ne') (fun j => (hρ (n + 1) j).ne') (h n) ih

/-- The collision term has a sign for a normalized state: `⟨u', ρ'⟩ ≤ ‖u'‖²`, i.e.
`Σ f^{n+1} (M^{n+1} - f^{n+1}) ω e^{3v²/2} ≤ 0`, because the Maxwellian part vanishes by (10).
arXiv 2411.06844, proof of Theorem 2, relation (10). -/
theorem collision_sign (hm : QuadNormalized v ω) (hZ : ∀ k, 0 ≤ quadZ v ω k) (ρ' : ZMod N → ℝ)
    {g' : ZMod N → K → ℝ} (hg : IsNormalized v ω g') :
    zI (quadZ v ω) (fun j k => ρ' j * g' j k) (fun j _ => ρ' j)
      ≤ zE (quadZ v ω) (fun j k => ρ' j * g' j k) := by
  set Z := quadZ v ω with hZdef
  have h1 : zI Z (fun j k => ρ' j * g' j k) (fun j _ => ρ' j) = ∑ j, ρ' j ^ 2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    calc ∑ k, ρ' j * g' j k * ρ' j * Z k = ρ' j ^ 2 * ∑ k, g' j k * Z k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = ρ' j ^ 2 := by rw [hg j, mul_one]
  have h2 : zE Z (fun j (_ : K) => ρ' j) = ∑ j, ρ' j ^ 2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, hm, mul_one]
  have hnn : 0 ≤ zE Z (fun j k => ρ' j * g' j k - ρ' j) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (hZ k)
  have hexp : zE Z (fun j k => ρ' j * g' j k - ρ' j)
      = zE Z (fun j k => ρ' j * g' j k)
        - 2 * zI Z (fun j k => ρ' j * g' j k) (fun j _ => ρ' j) + zE Z (fun j (_ : K) => ρ' j) := by
    simp only [zE, zI, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hexp, h1, h2] at hnn
  rw [h1]
  linarith

omit [Fintype K] in
private lemma quadZ_nonneg (hω : ∀ k, 0 ≤ ω k) (k : K) : 0 ≤ quadZ v ω k :=
  mul_nonneg (mul_nonneg (by positivity) (hω k)) (Real.exp_pos _).le

/-- **Theorem 2** (arXiv 2411.06844), one step.  Under `max_k |v_k| Δt ≤ Δx` the conservative
scheme (8) satisfies `‖f^{n+1}‖²_ℋ ≤ ‖f^n‖²_ℋ`.  Differences from the paper: the two facts its proof
takes from Lemma 2 are stated, namely (11) at the new time level and `QuadNormalized`.  Both are
necessary: `conservative_needs_normalized`, `conservative_needs_quadNormalized`.  For a whole
trajectory (11) is derived, see `theorem2_trajectory`. -/
theorem theorem2_step (hσ : 0 ≤ σ) (hdt : 0 ≤ dt) (hdx : 0 < dx) (hω : ∀ k, 0 ≤ ω k)
    (hm : QuadNormalized v ω) (hcfl : ∀ k, |v k| * dt ≤ dx)
    {ρ ρ' : ZMod N → ℝ} {g g' : ZMod N → K → ℝ} (hρ : ∀ j, ρ j ≠ 0)
    (h : IsConservativeStep σ dt dx v ω ρ g ρ' g') (hg' : IsNormalized v ω g') :
    hNormSq v ω (fOf v ρ' g') ≤ hNormSq v ω (fOf v ρ g) := by
  rw [hNormSq_fOf, hNormSq_fOf]
  have hZ := quadZ_nonneg (v := v) hω
  refine energy_core hσ hdt hdx hZ hcfl (m' := fun j _ => ρ' j) ?_ (collision_sign hm hZ ρ' hg')
  simp only [zE, zI, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have := h.mul_form hρ j k
  linear_combination (ρ' j * g' j k * quadZ v ω k) * this

/-- The explicit solution of (8a), i.e. (14a) divided by `1 + σΔt`. -/
noncomputable def gNext (σ dt dx : ℝ) (v : K → ℝ) (ρ ρ' : ZMod N → ℝ) (g : ZMod N → K → ℝ)
    (j : ZMod N) (k : K) : ℝ :=
  (ρ j * g j k - dt * upw dx (v k) (fun i => ρ i * g i k) j + σ * dt * ρ' j)
    / ((1 + σ * dt) * ρ' j)

omit [NeZero N] in
/-- The implicit step (8a) is solvable: for `ρ, ρ' ≠ 0`, `gNext` is a solution.
arXiv 2411.06844, scheme (8); not stated in the paper. -/
theorem isConservativeStep_gNext (hσ : 0 ≤ σ) (hdt : 0 ≤ dt) {ρ ρ' : ZMod N → ℝ}
    {g : ZMod N → K → ℝ} (hρ : ∀ j, ρ j ≠ 0) (hρ' : ∀ j, ρ' j ≠ 0)
    (hd : ∀ j, ρ' j = densityNext dt dx v ω ρ g j) :
    IsConservativeStep σ dt dx v ω ρ g ρ' (gNext σ dt dx v ρ ρ' g) := by
  refine ⟨hd, fun j k => ?_⟩
  have hs : 1 + σ * dt ≠ 0 := by positivity
  have h1 := hρ j
  have h2 := hρ' j
  have hy : (1 + σ * dt) * (ρ' j * gNext σ dt dx v ρ ρ' g j k) = ρ j * g j k
      - dt * upw dx (v k) (fun i => ρ i * g i k) j + σ * dt * ρ' j := by
    simp only [gNext]
    field_simp
  simp only [upw] at hy
  generalize gNext σ dt dx v ρ ρ' g j k = y at hy ⊢
  field_simp
  linear_combination (2 : ℝ) * hy

omit [NeZero N] in
/-- A positive normalized state stays positive under the CFL condition: the density update is a
convex combination of neighbouring values and `gNext` is positive.
arXiv 2411.06844, scheme (8); not stated in the paper. -/
theorem positive_step (hσ : 0 ≤ σ) (hdt : 0 ≤ dt) (hdx : 0 < dx) (hω : ∀ k, 0 < ω k)
    [Nonempty K] (hcfl : ∀ k, |v k| * dt ≤ dx)
    {ρ : ZMod N → ℝ} {g : ZMod N → K → ℝ} (hρ : ∀ j, 0 < ρ j) (hg : ∀ j k, 0 < g j k)
    (hn : IsNormalized v ω g) :
    (∀ j, 0 < densityNext dt dx v ω ρ g j) ∧
      ∀ j k, 0 < gNext σ dt dx v ρ (densityNext dt dx v ω ρ g) g j k := by
  have hZ : ∀ k, 0 < quadZ v ω k := fun k =>
    mul_pos (mul_pos (by positivity) (hω k)) (Real.exp_pos _)
  have hu : ∀ j k, 0 < ρ j * g j k - dt * upw dx (v k) (fun i => ρ i * g i k) j := fun j k =>
    upw_step_pos hdx hdt (hcfl k) (fun i => mul_pos (hρ i) (hg i k)) j
  have hd : ∀ j, 0 < densityNext dt dx v ω ρ g j := by
    intro j
    have e : densityNext dt dx v ω ρ g j
        = ∑ k, (ρ j * g j k - dt * upw dx (v k) (fun i => ρ i * g i k) j) * quadZ v ω k := by
      rw [densityNext_eq]
      have h1 : ρ j = ∑ k, ρ j * g j k * quadZ v ω k := by
        have := hn j
        calc ρ j = ρ j * ∑ k, g j k * quadZ v ω k := by rw [this, mul_one]
          _ = ∑ k, ρ j * g j k * quadZ v ω k := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by ring
      rw [Finset.mul_sum]
      conv_lhs => rw [h1]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    exact Finset.sum_pos (fun k _ => mul_pos (hu j k) (hZ k)) Finset.univ_nonempty
  refine ⟨hd, fun j k => ?_⟩
  have h1 := hu j k
  have h2 := hd j
  have h3 : 0 ≤ σ * dt := mul_nonneg hσ hdt
  exact div_pos (by nlinarith [mul_nonneg h3 h2.le]) (by positivity)

/-- The state after `n` steps of (8), built with `densityNext` and `gNext`. -/
noncomputable def consIter (σ dt dx : ℝ) (v ω : K → ℝ) (ρ₀ : ZMod N → ℝ) (g₀ : ZMod N → K → ℝ) :
    ℕ → (ZMod N → ℝ) × (ZMod N → K → ℝ)
  | 0 => (ρ₀, g₀)
  | n + 1 =>
    let s := consIter σ dt dx v ω ρ₀ g₀ n
    (densityNext dt dx v ω s.1 s.2, gNext σ dt dx v s.1 (densityNext dt dx v ω s.1 s.2) s.2)

/-- **Theorem 2** (arXiv 2411.06844) for trajectories, with nothing assumed about later time
levels: for positive initial data satisfying (11), under `max_k |v_k| Δt ≤ Δx`, every sequence
solving (8) has positive densities, satisfies (11), and has nonincreasing `ℋ`-norm.
The paper assumes `ρ > 0`; positivity of `g⁰` is the extra assumption that lets it be derived.
Differences: `QuadNormalized` is stated (see `theorem2_step`). -/
theorem theorem2_trajectory (hσ : 0 ≤ σ) (hdt : 0 ≤ dt) (hdx : 0 < dx) (hω : ∀ k, 0 < ω k)
    (hm : QuadNormalized v ω) (hcfl : ∀ k, |v k| * dt ≤ dx)
    {ρ : ℕ → ZMod N → ℝ} {g : ℕ → ZMod N → K → ℝ}
    (h : ∀ n, IsConservativeStep σ dt dx v ω (ρ n) (g n) (ρ (n + 1)) (g (n + 1)))
    (hρ0 : ∀ j, 0 < ρ 0 j) (hg0 : ∀ j k, 0 < g 0 j k) (hn0 : IsNormalized v ω (g 0)) (n : ℕ) :
    (∀ j, 0 < ρ n j) ∧ (∀ j k, 0 < g n j k) ∧ IsNormalized v ω (g n) ∧
      hNormSq v ω (fOf v (ρ (n + 1)) (g (n + 1))) ≤ hNormSq v ω (fOf v (ρ n) (g n)) := by
  have hne : Nonempty K := by
    by_contra hK
    rw [not_nonempty_iff] at hK
    have : QuadNormalized v ω := hm
    simp [QuadNormalized] at this
  have hs : 0 < 1 + σ * dt := by positivity
  have ht : 0 ≤ σ * dt := mul_nonneg hσ hdt
  have step : ∀ n, (∀ j, 0 < ρ n j) → (∀ j k, 0 < g n j k) → IsNormalized v ω (g n) →
      (∀ j, 0 < ρ (n + 1) j) ∧ (∀ j k, 0 < g (n + 1) j k) ∧ IsNormalized v ω (g (n + 1)) := by
    intro n h1 h2 h3
    have hp := positive_step (σ := σ) hσ hdt hdx hω hcfl h1 h2 h3
    have hr : ρ (n + 1) = densityNext dt dx v ω (ρ n) (g n) := funext (h n).density
    have hr' : ∀ j, 0 < ρ (n + 1) j := fun j => by rw [hr]; exact hp.1 j
    refine ⟨hr', fun j k => ?_, normalized_step hm hσ hdt (fun j => (h1 j).ne')
      (fun j => (hr' j).ne') (h n) h3⟩
    have hm' := (h n).mul_form (fun j => (h1 j).ne') j k
    have hu : 0 < ρ n j * g n j k - dt * upw dx (v k) (fun i => ρ n i * g n i k) j :=
      upw_step_pos hdx hdt (hcfl k) (fun i => mul_pos (h1 i) (h2 i k)) j
    have hpos : 0 < (1 + σ * dt) * (ρ (n + 1) j * g (n + 1) j k) := by
      rw [hm']
      nlinarith [mul_nonneg ht (hr' j).le]
    exact (mul_pos_iff_of_pos_left (hr' j)).1 ((mul_pos_iff_of_pos_left hs).1 hpos)
  have all : ∀ n, (∀ j, 0 < ρ n j) ∧ (∀ j k, 0 < g n j k) ∧ IsNormalized v ω (g n) := by
    intro n
    induction n with
    | zero => exact ⟨hρ0, hg0, hn0⟩
    | succ n ih => exact step n ih.1 ih.2.1 ih.2.2
  refine ⟨(all n).1, (all n).2.1, (all n).2.2, ?_⟩
  exact theorem2_step hσ hdt hdx (fun k => (hω k).le) hm hcfl (fun j => ((all n).1 j).ne') (h n)
    (all (n + 1)).2.2

omit [NeZero N] in
/-- The hypotheses of `theorem2_trajectory` are satisfiable: `consIter` solves (8) from any positive
initial data satisfying (11), under the CFL condition.
arXiv 2411.06844, scheme (8); not stated in the paper. -/
theorem consIter_spec (hσ : 0 ≤ σ) (hdt : 0 ≤ dt) (hdx : 0 < dx) (hω : ∀ k, 0 < ω k)
    (hm : QuadNormalized v ω) (hcfl : ∀ k, |v k| * dt ≤ dx)
    {ρ₀ : ZMod N → ℝ} {g₀ : ZMod N → K → ℝ} (hρ0 : ∀ j, 0 < ρ₀ j) (hg0 : ∀ j k, 0 < g₀ j k)
    (hn0 : IsNormalized v ω g₀) (n : ℕ) :
    IsConservativeStep σ dt dx v ω (consIter σ dt dx v ω ρ₀ g₀ n).1 (consIter σ dt dx v ω ρ₀ g₀ n).2
      (consIter σ dt dx v ω ρ₀ g₀ (n + 1)).1 (consIter σ dt dx v ω ρ₀ g₀ (n + 1)).2 := by
  have hne : Nonempty K := by
    by_contra hK
    rw [not_nonempty_iff] at hK
    have : QuadNormalized v ω := hm
    simp [QuadNormalized] at this
  have inv : ∀ n, (∀ j, 0 < (consIter σ dt dx v ω ρ₀ g₀ n).1 j) ∧
      (∀ j k, 0 < (consIter σ dt dx v ω ρ₀ g₀ n).2 j k) ∧
      IsNormalized v ω (consIter σ dt dx v ω ρ₀ g₀ n).2 := by
    intro n
    induction n with
    | zero => exact ⟨hρ0, hg0, hn0⟩
    | succ n ih =>
      have hp := positive_step (σ := σ) hσ hdt hdx hω hcfl ih.1 ih.2.1 ih.2.2
      refine ⟨hp.1, hp.2, ?_⟩
      exact normalized_step hm hσ hdt (fun j => (ih.1 j).ne') (fun j => (hp.1 j).ne')
        (isConservativeStep_gNext hσ hdt (fun j => (ih.1 j).ne') (fun j => (hp.1 j).ne')
          fun _ => rfl) ih.2.2
  exact isConservativeStep_gNext hσ hdt (fun j => ((inv n).1 j).ne')
    (fun j => ((inv (n + 1)).1 j).ne') fun _ => rfl

omit [NeZero N] in
/-- The identity `QuadNormalized` cannot be dropped from Lemma 2: if `σ, Δt > 0` and (11) holds at
two consecutive time levels at one grid point, then `QuadNormalized`.
arXiv 2411.06844, Lemma 2, necessity of the unlisted hypothesis. -/
theorem quadNormalized_of_normalized (hσ : 0 < σ) (hdt : 0 < dt) {ρ ρ' : ZMod N → ℝ}
    {g g' : ZMod N → K → ℝ} (hρ : ∀ j, ρ j ≠ 0) (hρ' : ∀ j, ρ' j ≠ 0)
    (h : IsConservativeStep σ dt dx v ω ρ g ρ' g') (hg : IsNormalized v ω g)
    (hg' : IsNormalized v ω g') (j : ZMod N) : QuadNormalized v ω := by
  have hd := h.density j
  rw [densityNext_eq] at hd
  have key : (1 + σ * dt) * ρ' j
      = ρ' j + σ * dt * ρ' j * ∑ k, quadZ v ω k := by
    calc (1 + σ * dt) * ρ' j = (1 + σ * dt) * ρ' j * ∑ k, g' j k * quadZ v ω k := by
          rw [hg' j, mul_one]
      _ = ∑ k, ((1 + σ * dt) * (ρ' j * g' j k)) * quadZ v ω k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ k, (ρ j * g j k - dt * upw dx (v k) (fun i => ρ i * g i k) j
            + σ * dt * ρ' j) * quadZ v ω k :=
          Finset.sum_congr rfl fun k _ => by rw [h.mul_form hρ]
      _ = ρ j * ∑ k, g j k * quadZ v ω k
            - dt * ∑ k, upw dx (v k) (fun i => ρ i * g i k) j * quadZ v ω k
            + σ * dt * ρ' j * ∑ k, quadZ v ω k := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
            ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = ρ' j + σ * dt * ρ' j * ∑ k, quadZ v ω k := by
          rw [hg j, mul_one, hd]
  have hne : σ * dt * ρ' j ≠ 0 := mul_ne_zero (mul_pos hσ hdt).ne' (hρ' j)
  have : σ * dt * ρ' j * ∑ k, quadZ v ω k = σ * dt * ρ' j * 1 := by linarith
  exact mul_left_cancel₀ hne this

/-- The one-point Gauss-Hermite rule for `e^{-v²}` is node `0`, weight `√π`, and it violates
`QuadNormalized`.  So the identity used in the proof of Lemma 2 is an extra requirement on the
weights and not a property of the quadrature named in the paper.
arXiv 2411.06844, Lemma 2, the unlisted hypothesis. -/
theorem gaussHermite_one_point :
    ¬ QuadNormalized (fun _ : Unit => (0 : ℝ)) (fun _ => Real.sqrt Real.pi) := by
  simp only [QuadNormalized, quadZ, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_div, Real.exp_zero, mul_one, Finset.univ_unique, Finset.sum_singleton]
  rw [Real.sqrt_mul (by norm_num), div_mul_eq_mul_div, one_mul, div_eq_one_iff_eq
    (mul_ne_zero (by positivity) (by positivity))]
  have h1 : 0 < Real.sqrt Real.pi := by positivity
  have h2 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  nlinarith

omit [Fintype K] [NeZero N] in
private lemma upw_const (dx a c : ℝ) (j : ZMod N) : upw dx a (fun _ => c) j = 0 := by
  have h : c - 2 * c + c = 0 := by ring
  simp [upw, Dx, Dxx, h]

/-- The initial normalization cannot be dropped from `theorem2_step`: from `g = 0`, which violates
(11), the implicit collision raises the `ℋ`-norm, on one grid point with one node and CFL.
arXiv 2411.06844, Theorem 2, necessity of the hypothesis of Lemma 2. -/
theorem conservative_needs_normalized :
    ∃ (σ dt dx : ℝ) (v ω : Unit → ℝ) (ρ ρ' : ZMod 1 → ℝ) (g g' : ZMod 1 → Unit → ℝ),
      0 < σ ∧ 0 < dt ∧ 0 < dx ∧ (∀ k, 0 < ω k) ∧ QuadNormalized v ω ∧ (∀ k, |v k| * dt ≤ dx) ∧
      (∀ j, 0 < ρ j) ∧ (∀ j, 0 < ρ' j) ∧ IsConservativeStep σ dt dx v ω ρ g ρ' g' ∧
      hNormSq v ω (fOf v ρ g) < hNormSq v ω (fOf v ρ' g') := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hZ : ∀ k, quadZ (fun _ : Unit => (0 : ℝ)) (fun _ => Real.sqrt (2 * Real.pi)) k = 1 := by
    intro k
    simp only [quadZ]
    field_simp
    simp
  refine ⟨1, 1, 1, fun _ => 0, fun _ => Real.sqrt (2 * Real.pi), fun _ => 1, fun _ => 1,
    fun _ _ => 0, fun _ _ => 1 / 2, one_pos, one_pos, one_pos, fun _ => hs, ?_, ?_,
    fun _ => one_pos, fun _ => one_pos, ⟨fun j => ?_, fun j k => ?_⟩, ?_⟩
  · simp only [QuadNormalized, hZ, Finset.univ_unique, Finset.sum_singleton]
  · simp
  · rw [densityNext_eq]
    simp only [upw_const, zero_mul, Finset.sum_const_zero, mul_zero, sub_zero]
  · simp [Dx, Dxx]
    norm_num
  · rw [hNormSq_fOf, hNormSq_fOf]
    simp only [zE, hZ]
    simp

/-- `QuadNormalized` cannot be dropped from `theorem2_step`: with `Z = 2` and the normalized state
`g = 1/2` the implicit collision raises the `ℋ`-norm.
arXiv 2411.06844, Theorem 2, necessity of the unlisted hypothesis. -/
theorem conservative_needs_quadNormalized :
    ∃ (σ dt dx : ℝ) (v ω : Unit → ℝ) (ρ ρ' : ZMod 1 → ℝ) (g g' : ZMod 1 → Unit → ℝ),
      0 < σ ∧ 0 < dt ∧ 0 < dx ∧ (∀ k, 0 < ω k) ∧ (∀ k, |v k| * dt ≤ dx) ∧
      (∀ j, 0 < ρ j) ∧ (∀ j, 0 < ρ' j) ∧ IsNormalized v ω g ∧
      IsConservativeStep σ dt dx v ω ρ g ρ' g' ∧
      hNormSq v ω (fOf v ρ g) < hNormSq v ω (fOf v ρ' g') := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hZ : ∀ k, quadZ (fun _ : Unit => (0 : ℝ)) (fun _ => 2 * Real.sqrt (2 * Real.pi)) k = 2 := by
    intro k
    simp only [quadZ]
    field_simp
    simp
  refine ⟨1, 1, 1, fun _ => 0, fun _ => 2 * Real.sqrt (2 * Real.pi), fun _ => 1, fun _ => 1,
    fun _ _ => 1 / 2, fun _ _ => 3 / 4, one_pos, one_pos, one_pos, fun _ => by positivity, ?_,
    fun _ => one_pos, fun _ => one_pos, ?_, ⟨fun j => ?_, fun j k => ?_⟩, ?_⟩
  · simp
  · intro j
    simp only [hZ, Finset.univ_unique, Finset.sum_singleton]
    norm_num
  · rw [densityNext_eq]
    simp only [upw_const, zero_mul, Finset.sum_const_zero, mul_zero, sub_zero]
  · simp [Dx, Dxx]
    norm_num
  · rw [hNormSq_fOf, hNormSq_fOf]
    simp only [zE, hZ]
    simp
    norm_num

omit [NeZero N] in
/-- **Lemma 2 fails for Gauss-Hermite weights.**  With the one-point rule, for all `σ, Δt > 0`, the
relation (11) is not preserved by (8), on every normalized state.  The hypothesis of Lemma 2 is
satisfiable for this rule, e.g. by `g⁰ ≡ √2`.
arXiv 2411.06844, Lemma 2. -/
theorem lemma2_fails_gaussHermite {σ dt dx : ℝ} (hσ : 0 < σ) (hdt : 0 < dt)
    {ρ ρ' : ZMod N → ℝ} {g g' : ZMod N → Unit → ℝ} (hρ : ∀ j, ρ j ≠ 0) (hρ' : ∀ j, ρ' j ≠ 0)
    (h : IsConservativeStep σ dt dx (fun _ : Unit => (0 : ℝ)) (fun _ => Real.sqrt Real.pi)
      ρ g ρ' g')
    (hg : IsNormalized (fun _ : Unit => (0 : ℝ)) (fun _ => Real.sqrt Real.pi) g) :
    ¬ IsNormalized (fun _ : Unit => (0 : ℝ)) (fun _ => Real.sqrt Real.pi) g' := fun hg' =>
  gaussHermite_one_point (quadNormalized_of_normalized hσ hdt hρ hρ' h hg hg' 0)

omit [NeZero N] in
/-- `g ≡ √2` is normalized for the one-point Gauss-Hermite rule.
arXiv 2411.06844, Lemma 2. -/
theorem gaussHermite_one_point_normalized :
    IsNormalized (N := N) (fun _ : Unit => (0 : ℝ)) (fun _ => Real.sqrt Real.pi)
      (fun _ _ => Real.sqrt 2) := by
  intro j
  have h1 : Real.sqrt 2 ≠ 0 := by positivity
  have h2 : Real.sqrt Real.pi ≠ 0 := by positivity
  simp only [quadZ, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    Real.exp_zero, mul_one, Finset.univ_unique, Finset.sum_singleton]
  rw [Real.sqrt_mul (by norm_num)]
  field_simp

end Stability

/-! ### Theorem 1: the naive scheme -/

section Naive

variable {N : ℕ} [NeZero N] {K : Type*} [Fintype K]

/-- The explicit Euler step with central differences for `∂_t z + a/Δt ∂_x z = 0`, i.e. equation
(9) for one velocity, with `a = Δt v_k`. -/
noncomputable def centered (dx a : ℝ) (z : ZMod N → ℝ) (j : ZMod N) : ℝ :=
  z j - a * Dx dx z j

/-- The energy identity for skew `D^x`: `‖z - a D^x z‖² = ‖z‖² + a² ‖D^x z‖²`.
arXiv 2411.06844, Theorem 1; compare `norm_eulerStep_sq`. -/
theorem sum_centered_sq (dx a : ℝ) (z : ZMod N → ℝ) :
    ∑ j, centered dx a z j ^ 2 = ∑ j, z j ^ 2 + a ^ 2 * ∑ j, Dx dx z j ^ 2 := by
  have h := sum_mul_Dx_self dx z
  have e : ∑ j, centered dx a z j ^ 2
      = ∑ j, z j ^ 2 - 2 * a * ∑ j, z j * Dx dx z j + a ^ 2 * ∑ j, Dx dx z j ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [centered]
    ring
  rw [e, h]
  ring

/-- If `(D^x)² z = -w² z`, iterates of `centered` grow exactly by `1 + a² w²` per step in the
squared norm.
arXiv 2411.06844, Theorem 1. -/
theorem sum_centered_iterate_sq {dx a w : ℝ} {z : ZMod N → ℝ}
    (hz : ∀ j, Dx dx (Dx dx z) j = -(w ^ 2) * z j) (n : ℕ) :
    ∑ j, (centered dx a)^[n] z j ^ 2 = (1 + a ^ 2 * w ^ 2) ^ n * ∑ j, z j ^ 2 := by
  have step : ∀ y : ZMod N → ℝ, (∀ j, Dx dx (Dx dx y) j = -(w ^ 2) * y j) →
      (∀ j, Dx dx (Dx dx (centered dx a y)) j = -(w ^ 2) * centered dx a y j) ∧
      ∑ j, centered dx a y j ^ 2 = (1 + a ^ 2 * w ^ 2) * ∑ j, y j ^ 2 := by
    intro y hy
    constructor
    · have e : Dx dx (centered dx a y) = fun i => Dx dx y i + a * w ^ 2 * y i := by
        funext i
        have := hy i
        rw [Dx] at this
        simp only [centered, Dx] at this ⊢
        linear_combination (-a) * this
      intro j
      rw [e]
      have := hy j
      simp only [Dx, centered] at this ⊢
      linear_combination this
    · have h1 : ∑ j, Dx dx y j ^ 2 = w ^ 2 * ∑ j, y j ^ 2 := by
        have h2 := sum_mul_Dx dx (Dx dx y) y
        have h3 : ∑ j, y j * Dx dx (Dx dx y) j = -(w ^ 2) * ∑ j, y j ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [hy j]; ring
        have h4 : ∑ j, Dx dx y j * Dx dx y j = ∑ j, Dx dx y j ^ 2 :=
          Finset.sum_congr rfl fun j _ => by ring
        rw [h4, h3] at h2
        linarith
      rw [sum_centered_sq, h1]
      ring
  have inv : ∀ n, (∀ j, Dx dx (Dx dx ((centered dx a)^[n] z)) j
        = -(w ^ 2) * (centered dx a)^[n] z j) ∧
      ∑ j, (centered dx a)^[n] z j ^ 2 = (1 + a ^ 2 * w ^ 2) ^ n * ∑ j, z j ^ 2 := by
    intro n
    induction n with
    | zero => exact ⟨hz, by simp⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨h1, h2⟩ := step _ ih.1
      refine ⟨h1, ?_⟩
      rw [h2, ih.2]
      ring
  exact (inv n).2

/-- The real part of the Fourier mode `j ↦ e^{2π i j / N}`. -/
noncomputable def modeRe (j : ZMod N) : ℝ := ((ZMod.toCircle j : Circle) : ℂ).re

/-- The imaginary part of the Fourier mode `j ↦ e^{2π i j / N}`. -/
noncomputable def modeIm (j : ZMod N) : ℝ := ((ZMod.toCircle j : Circle) : ℂ).im

private lemma mode_sq (j : ZMod N) : modeRe j ^ 2 + modeIm j ^ 2 = 1 := by
  have h := Circle.norm_coe (ZMod.toCircle j)
  have h2 := Complex.sq_norm ((ZMod.toCircle j : Circle) : ℂ)
  rw [h, Complex.normSq_apply] at h2
  simp only [modeRe, modeIm]
  linarith

private lemma mode_add (i j : ZMod N) :
    ((ZMod.toCircle (i + j) : Circle) : ℂ)
      = (ZMod.toCircle i : Circle) * (ZMod.toCircle j : Circle) := by
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

private lemma modeRe_succ (j : ZMod N) :
    modeRe (j + 1) = modeRe j * modeRe (N := N) 1 - modeIm j * modeIm (N := N) 1 := by
  simp only [modeRe, modeIm, mode_add, Complex.mul_re]

private lemma modeIm_succ (j : ZMod N) :
    modeIm (j + 1) = modeRe j * modeIm (N := N) 1 + modeIm j * modeRe (N := N) 1 := by
  simp only [modeRe, modeIm, mode_add, Complex.mul_im]

private lemma modeRe_pred (j : ZMod N) :
    modeRe (j - 1) = modeRe j * modeRe (N := N) 1 + modeIm j * modeIm (N := N) 1 := by
  have h1 := modeRe_succ (j - 1)
  have h2 := modeIm_succ (j - 1)
  rw [sub_add_cancel] at h1 h2
  rw [h1, h2]
  linear_combination (-modeRe (j - 1)) * mode_sq (N := N) 1

private lemma modeIm_pred (j : ZMod N) :
    modeIm (j - 1) = modeIm j * modeRe (N := N) 1 - modeRe j * modeIm (N := N) 1 := by
  have h1 := modeRe_succ (j - 1)
  have h2 := modeIm_succ (j - 1)
  rw [sub_add_cancel] at h1 h2
  rw [h1, h2]
  linear_combination (-modeIm (j - 1)) * mode_sq (N := N) 1

private lemma Dx_modeRe {dx : ℝ} (hdx : dx ≠ 0) (j : ZMod N) :
    Dx dx modeRe j = -(modeIm (N := N) 1 / dx) * modeIm j := by
  simp only [Dx, modeRe_succ, modeRe_pred]
  field_simp
  ring

private lemma Dx_modeIm {dx : ℝ} (hdx : dx ≠ 0) (j : ZMod N) :
    Dx dx modeIm j = modeIm (N := N) 1 / dx * modeRe j := by
  simp only [Dx, modeIm_succ, modeIm_pred]
  field_simp
  ring

omit [NeZero N] in
private lemma Dx_const_mul (dx c : ℝ) (z : ZMod N → ℝ) (j : ZMod N) :
    Dx dx (fun i => c * z i) j = c * Dx dx z j := by
  simp only [Dx]
  ring

private lemma Dx_Dx_modeRe {dx : ℝ} (hdx : dx ≠ 0) (j : ZMod N) :
    Dx dx (Dx dx modeRe) j = -((modeIm (N := N) 1 / dx) ^ 2) * modeRe j := by
  have e : Dx dx (modeRe (N := N)) = fun i => -(modeIm (N := N) 1 / dx) * modeIm i :=
    funext (Dx_modeRe hdx)
  rw [e, Dx_const_mul, Dx_modeIm hdx]
  ring

private lemma modeIm_one : modeIm (N := N) 1 = Real.sin (2 * Real.pi / N) := by
  have h : ((ZMod.toCircle (1 : ZMod N) : Circle) : ℂ)
      = Complex.exp ((2 * Real.pi / N : ℝ) * Complex.I) := by
    have := ZMod.toCircle_natCast (N := N) 1
    rw [Nat.cast_one] at this
    rw [this]
    congr 1
    push_cast
    ring
  rw [modeIm, h, Complex.exp_ofReal_mul_I_im]

private lemma modeRe_zero : modeRe (0 : ZMod N) = 1 := by
  simp [modeRe]

omit [NeZero N] in
private lemma sin_two_pi_div_ne (hN : 3 ≤ N) : Real.sin (2 * Real.pi / N) ≠ 0 := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : 0 < 2 * Real.pi / N := by positivity
  have h2 : 2 * Real.pi / N < Real.pi := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  exact (Real.sin_pos_of_pos_of_lt_pi h1 h2).ne'

/-- **Theorem 1, von Neumann part** (arXiv 2411.06844).  The discretisation (9), explicit Euler with
central differences, has a Fourier mode with squared amplification factor
`1 + (a sin(2π/N) / Δx)² > 1` for every `a = Δt v_k ≠ 0` and `N ≥ 3`, at every time step, so every
time step is unstable in the sense of von Neumann.  (For `N ≤ 2` the stencil `D^x` vanishes.) -/
theorem centered_mode_growth (hN : 3 ≤ N) {dx a : ℝ} (hdx : 0 < dx) (ha : a ≠ 0) :
    1 < 1 + (a * Real.sin (2 * Real.pi / N) / dx) ^ 2 ∧ 0 < ∑ j, modeRe (N := N) j ^ 2 ∧
      ∀ n, ∑ j, (centered dx a)^[n] (modeRe (N := N)) j ^ 2
        = (1 + (a * Real.sin (2 * Real.pi / N) / dx) ^ 2) ^ n * ∑ j, modeRe (N := N) j ^ 2 := by
  have hs := sin_two_pi_div_ne (N := N) hN
  refine ⟨?_, ?_, fun n => ?_⟩
  · have : 0 < (a * Real.sin (2 * Real.pi / N) / dx) ^ 2 := by positivity
    linarith
  · refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun j _ => sq_nonneg (modeRe (N := N) j))
      (Finset.mem_univ 0))
    rw [modeRe_zero]
    norm_num
  · have h := sum_centered_iterate_sq (dx := dx) (a := a) (w := modeIm (N := N) 1 / dx)
      (z := modeRe (N := N)) (Dx_Dx_modeRe hdx.ne') n
    rw [h, modeIm_one]
    congr 2
    ring

private lemma hNormSq_pos {v ω : K → ℝ} (hω : ∀ k, 0 < ω k) {F : ZMod N → K → ℝ}
    (j : ZMod N) (k : K) (hF : F j k ≠ 0) : 0 < hNormSq v ω F := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have ht : ∀ j k, 0 ≤ F j k ^ 2 * ω k * Real.exp (3 * v k ^ 2 / 2) := fun j k =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (hω k).le) (Real.exp_pos _).le
  have h0 : 0 < F j k ^ 2 * ω k * Real.exp (3 * v k ^ 2 / 2) :=
    mul_pos (mul_pos (by positivity) (hω k)) (Real.exp_pos _)
  have h1 := Finset.single_le_sum (s := Finset.univ) (f := fun k => F j k ^ 2 * ω k *
    Real.exp (3 * v k ^ 2 / 2)) (fun k _ => ht j k) (Finset.mem_univ k)
  have h2 := Finset.single_le_sum (s := Finset.univ) (f := fun j => ∑ k, F j k ^ 2 * ω k *
    Real.exp (3 * v k ^ 2 / 2)) (fun j _ => Finset.sum_nonneg fun k _ => ht j k)
    (Finset.mem_univ j)
  exact mul_pos hs (lt_of_lt_of_le h0 (h1.trans h2))

private lemma hNormSq_swap (v ω : K → ℝ) (F : ZMod N → K → ℝ) :
    hNormSq v ω F = ∑ k, (Real.sqrt (2 * Real.pi) * ω k * Real.exp (3 * v k ^ 2 / 2)) *
      ∑ j, F j k ^ 2 := by
  rw [hNormSq, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The `ℋ`-norm of one explicit central step:
`‖f - Δt D^x f diag(v)‖²_ℋ = ‖f‖²_ℋ + Δt² ‖D^x f diag(v)‖²_ℋ`.
arXiv 2411.06844, Theorem 1, equation (9). -/
theorem hNormSq_centered (v ω : K → ℝ) (dt dx : ℝ) (f : ZMod N → K → ℝ) :
    hNormSq v ω (fun j k => f j k - dt * Dx dx (fun i => f i k) j * v k)
      = hNormSq v ω f + dt ^ 2 * hNormSq v ω (fun j k => Dx dx (fun i => f i k) j * v k) := by
  rw [hNormSq_swap, hNormSq_swap, hNormSq_swap, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := sum_centered_sq dx (dt * v k) (fun i => f i k)
  have e1 : ∑ j, (f j k - dt * Dx dx (fun i => f i k) j * v k) ^ 2
      = ∑ j, centered dx (dt * v k) (fun i => f i k) j ^ 2 :=
    Finset.sum_congr rfl fun j _ => by simp only [centered]; ring
  have e2 : ∑ j, (Dx dx (fun i => f i k) j * v k) ^ 2
      = v k ^ 2 * ∑ j, Dx dx (fun i => f i k) j ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, h]
  ring

omit [NeZero N] in
/-- Equation (9) of arXiv 2411.06844: one step of the naive scheme (7) with `σ = 0` from `g ≡ 1`,
which the paper's proof of Theorem 1 uses, is `f' = f - Δt D^x f diag(v)`. -/
theorem naive_step_eq9 {dt dx : ℝ} {v ω : K → ℝ} {ρ ρ' : ZMod N → ℝ} {g g' : ZMod N → K → ℝ}
    (h : IsNaiveStep 0 dt dx v ω ρ g ρ' g') (hg : ∀ j k, g j k = 1) (hρ : ∀ j, ρ j ≠ 0)
    (j : ZMod N) (k : K) :
    fOf v ρ' g' j k = fOf v ρ g j k - dt * Dx dx (fun i => fOf v ρ g i k) j * v k := by
  have h1 := h.update j k
  have hc : (fun i => g i k) = fun _ => 1 := funext fun i => hg i k
  have h2 : ρ' j * g' j k = ρ j - dt * Dx dx ρ j * v k := by
    have h3 := hρ j
    rw [hc, hg] at h1
    simp only [Dx, Dxx, sub_self, zero_div, mul_zero, zero_mul, sub_zero, add_zero] at h1
    have hs : (1 : ℝ) - 2 * 1 + 1 = 0 := by norm_num
    rw [hs] at h1
    simp only [zero_div, mul_zero, zero_mul, add_zero] at h1
    field_simp at h1
    simp only [Dx]
    field_simp
    linear_combination h1
  have e : (fun i => fOf v ρ g i k)
      = fun i => (1 / Real.sqrt (2 * Real.pi) * Real.exp (-(v k ^ 2) / 2)) * ρ i := by
    funext i
    simp only [fOf, hg]
    ring
  rw [e, Dx_const_mul]
  simp only [fOf, hg]
  linear_combination (1 / Real.sqrt (2 * Real.pi) * Real.exp (-(v k ^ 2) / 2)) * h2

/-- **Theorem 1** (arXiv 2411.06844).  For `N ≥ 3`, any positive weights, a nonzero node and *every*
`Δt > 0` (in particular under the CFL condition of Theorem 2), the naive scheme (7) with `σ = 0` has
a state `gⁿ ≡ 1`, `ρⁿ > 0` and a solution with `ρ^{n+1} > 0` of the step such that the `ℋ`-norm
strictly grows, in contrast to Theorem 2.  `ρⁿ` is a constant plus a Fourier mode.  The statement
"not von Neumann stable" of the paper refers to the linear scheme (9), which is
`centered_mode_growth`.  `naive_step_eq9` is the connection between (7) and (9); it concerns one
step, because `g^{n+1} ≢ 1` afterwards. -/
theorem theorem1_naive_unstable (hN : 3 ≤ N) {dt dx : ℝ} (hdt : 0 < dt) (hdx : 0 < dx)
    {v ω : K → ℝ} (hω : ∀ k, 0 < ω k) {k₀ : K} (hk₀ : v k₀ ≠ 0) :
    ∃ (ρ ρ' : ZMod N → ℝ) (g g' : ZMod N → K → ℝ), (∀ j, 0 < ρ j) ∧ (∀ j, 0 < ρ' j) ∧
      (∀ j k, g j k = 1) ∧ IsNaiveStep 0 dt dx v ω ρ g ρ' g' ∧
      hNormSq v ω (fOf v ρ g) < hNormSq v ω (fOf v ρ' g') := by
  classical
  set c : ZMod N → ℝ := modeRe with hc
  set r : ZMod N → ℝ := fun j => c j - dt * ∑ k, upw dx (v k) c j * quadZ v ω k with hr
  set C : ℝ := 1 + ∑ j, |c j| + ∑ j, |r j| with hC
  have hcle : ∀ j, |c j| ≤ ∑ j, |c j| := fun j =>
    Finset.single_le_sum (f := fun j => |c j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have hrle : ∀ j, |r j| ≤ ∑ j, |r j| := fun j =>
    Finset.single_le_sum (f := fun j => |r j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have hc0 : 0 ≤ ∑ j, |c j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hr0 : 0 ≤ ∑ j, |r j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set ρ : ZMod N → ℝ := fun j => C + c j with hρdef
  have hρ : ∀ j, 0 < ρ j := fun j => by
    have := neg_abs_le (c j)
    have := hcle j
    simp only [hρdef, hC]
    linarith
  set g : ZMod N → K → ℝ := fun _ _ => 1 with hgdef
  have hdens : ∀ j, densityNext dt dx v ω ρ g j = C + r j := by
    intro j
    rw [densityNext_eq]
    have e : ∀ k, upw dx (v k) (fun i => ρ i * g i k) j = upw dx (v k) c j := by
      intro k
      simp only [hρdef, hgdef, upw, Dx, Dxx, mul_one]
      ring
    have e2 : ∑ k, upw dx (v k) (fun i => ρ i * g i k) j * quadZ v ω k
        = ∑ k, upw dx (v k) c j * quadZ v ω k :=
      Finset.sum_congr rfl fun k _ => by rw [e k]
    rw [e2]
    change C + c j - _ = C + (c j - _)
    ring
  set ρ' : ZMod N → ℝ := fun j => C + r j with hρ'def
  have hρ' : ∀ j, 0 < ρ' j := fun j => by
    have := neg_abs_le (r j)
    have := hrle j
    simp only [hρ'def, hC]
    linarith
  set g' : ZMod N → K → ℝ := fun j k => (ρ j - dt * Dx dx ρ j * v k) / ρ' j with hg'def
  have hstep : IsNaiveStep 0 dt dx v ω ρ g ρ' g' := by
    refine ⟨fun j => (hdens j).symm, fun j k => ?_⟩
    have h1 := (hρ j).ne'
    have h2 := (hρ' j).ne'
    simp only [hgdef, Dx, Dxx, sub_self, zero_div, mul_zero, zero_mul, sub_zero, add_zero]
    have hs : (1 : ℝ) - 2 * 1 + 1 = 0 := by norm_num
    simp only [hs, zero_div, mul_zero, zero_mul, add_zero, hg'def, Dx]
    field_simp
    ring
  have hf : hNormSq v ω (fOf v ρ' g') = hNormSq v ω (fOf v ρ g)
      + dt ^ 2 * hNormSq v ω (fun j k => Dx dx (fun i => fOf v ρ g i k) j * v k) := by
    rw [← hNormSq_centered]
    congr 1
    funext j k
    exact naive_step_eq9 hstep (fun _ _ => rfl) (fun j => (hρ j).ne') j k
  have hne : Dx dx (fun i => fOf v ρ g i k₀) 1 * v k₀ ≠ 0 := by
    have e : (fun i => fOf v ρ g i k₀)
        = fun i => (1 / Real.sqrt (2 * Real.pi) * Real.exp (-(v k₀ ^ 2) / 2)) * (C + c i) := by
      funext i
      simp only [fOf, hgdef, hρdef]
      ring
    rw [e, Dx_const_mul]
    have e2 : Dx dx (fun i => C + c i) 1 = Dx dx c 1 := by
      simp only [Dx]
      ring
    rw [e2, hc, Dx_modeRe hdx.ne', modeIm_one]
    have hs := sin_two_pi_div_ne (N := N) hN
    have h2 : Real.sqrt (2 * Real.pi) ≠ 0 := sqrt_two_pi_ne
    have h3 := Real.exp_pos (-(v k₀ ^ 2) / 2)
    have h4 := hdx.ne'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (div_ne_zero one_ne_zero h2) h3.ne')
      (mul_ne_zero (neg_ne_zero.2 (div_ne_zero hs h4)) hs)) hk₀
  refine ⟨ρ, ρ', g, g', hρ, hρ', fun _ _ => rfl, hstep, ?_⟩
  have h5 := hNormSq_pos (v := v) (F := fun j k => Dx dx (fun i => fOf v ρ g i k) j * v k) hω 1 k₀
    hne
  rw [hf]
  have h6 : 0 < dt ^ 2 := by positivity
  nlinarith [mul_pos h6 h5]

end Naive

/-! ### The DLRA scheme (15) and Theorem 3 -/

section DLRA

variable {N : ℕ} [NeZero N] {K r : Type*} [Fintype K] [DecidableEq K] [Fintype r]

/-- The column space of a matrix. -/
def colSpace {m n : Type*} [Fintype n] (A : Matrix m n ℝ) : Submodule ℝ (m → ℝ) :=
  LinearMap.range A.mulVecLin

/-- `Q` is the matrix of the orthogonal projector onto `W`. -/
structure IsOrthProjOnto {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℝ)
    (W : Submodule ℝ (ι → ℝ)) : Prop where
  symm : Qᵀ = Q
  mem : ∀ x, Q *ᵥ x ∈ W
  fix : ∀ x ∈ W, Q *ᵥ x = x

/-- The hyperplane `u^⊥`. -/
def hyperplane {ι : Type*} [Fintype ι] (u : ι → ℝ) : Submodule ℝ (ι → ℝ) where
  carrier := {x | u ⬝ᵥ x = 0}
  add_mem' := by
    intro a b (ha : u ⬝ᵥ a = 0) (hb : u ⬝ᵥ b = 0)
    change u ⬝ᵥ (a + b) = 0
    rw [dotProduct_add, ha, hb, add_zero]
  zero_mem' := dotProduct_zero u
  smul_mem' := by
    intro c x (hx : u ⬝ᵥ x = 0)
    change u ⬝ᵥ (c • x) = 0
    rw [dotProduct_smul, hx, smul_zero]

omit [Fintype K] [DecidableEq K] [Fintype r] in
lemma mem_hyperplane {ι : Type*} [Fintype ι] {u x : ι → ℝ} :
    x ∈ hyperplane u ↔ u ⬝ᵥ x = 0 := Iff.rfl

/-- The orthogonal projector onto `u^⊥`, `I - u uᵀ / ‖u‖²`. -/
noncomputable def hyperProj {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → ℝ) : Matrix ι ι ℝ :=
  1 - (u ⬝ᵥ u)⁻¹ • Matrix.vecMulVec u u

omit [Fintype K] [DecidableEq K] [Fintype r] in
lemma hyperProj_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (u x : ι → ℝ) :
    hyperProj u *ᵥ x = x - ((u ⬝ᵥ u)⁻¹ * (u ⬝ᵥ x)) • u := by
  ext i
  simp only [hyperProj, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring

omit [Fintype K] [DecidableEq K] [Fintype r] in
/-- `hyperProj u` is the orthogonal projector onto `u^⊥`, used for the projector of the
counterexample to Theorem 3 of arXiv 2411.06844. -/
theorem isOrthProjOnto_hyperProj {ι : Type*} [Fintype ι] [DecidableEq ι] {u : ι → ℝ}
    (hu : u ≠ 0) : IsOrthProjOnto (hyperProj u) (hyperplane u) := by
  have hne : u ⬝ᵥ u ≠ 0 := fun h => hu (dotProduct_self_eq_zero.1 h)
  refine ⟨?_, fun x => ?_, fun x hx => ?_⟩
  · simp only [hyperProj, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
      Matrix.transpose_vecMulVec]
  · rw [mem_hyperplane, hyperProj_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    field_simp
    ring
  · rw [mem_hyperplane] at hx
    rw [hyperProj_mulVec, hx]
    simp

/-- The right-hand side of (14a): the conservative scheme reads `(1 + σΔt) g^{n+1} = G`, and `G` is
the operator that enters the `K`-, `L`- and `S`-steps. -/
noncomputable def rhsG (σ dt dx : ℝ) (v : K → ℝ) (ρ ρ' : ZMod N → ℝ) (g : Matrix (ZMod N) K ℝ) :
    Matrix (ZMod N) K ℝ :=
  Matrix.of fun j k => ρ j / ρ' j * g j k
    - dt * (1 / ρ' j) * Dx dx (fun i => ρ i * g i k) j * v k
    + dt * (dx / 2) * (1 / ρ' j) * Dxx dx (fun i => ρ i * g i k) j * |v k|
    + σ * dt

/-- The twice augmented space of (15b), (15c) and of (15d), (15e): with `𝒲 = range [A, B]`, this is
`𝒲 + diag(w) 𝒲`, the range of `qr [qr [A, B], diag(w) qr [A, B]]`. -/
noncomputable def augment {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    (A B : Matrix ι r ℝ) : Submodule ℝ (ι → ℝ) :=
  (colSpace A ⊔ colSpace B) ⊔ (colSpace A ⊔ colSpace B).map (Matrix.diagonal w).mulVecLin

/-- The projector `X̂ X̂ᵀ` of an orthonormal basis is `IsOrthProjOnto` its range, so the projectors
in `IsDLRAStep` are the `P^X`, `P^V` of the paper for any choice of the `qr` factors.
arXiv 2411.06844, Section 5.1. -/
theorem isOrthProjOnto_of_orthonormal {ι c : Type*} [Fintype ι] [Fintype c] [DecidableEq c]
    {B : Matrix ι c ℝ} (hB : Bᵀ * B = 1) : IsOrthProjOnto (B * Bᵀ) (colSpace B) := by
  refine ⟨by simp [Matrix.transpose_mul], fun x => ⟨Bᵀ *ᵥ x, ?_⟩, ?_⟩
  · simp [Matrix.mulVec_mulVec]
  · rintro _ ⟨y, rfl⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
    rw [Matrix.mul_assoc, hB, Matrix.mul_one]

/-- The mass part `H₁ = ĝ z zᵀ`, `z = Z / ‖Z‖`, of the truncation in Section 5.2. -/
noncomputable def massPart (Z : K → ℝ) (ghat : Matrix (ZMod N) K ℝ) : Matrix (ZMod N) K ℝ :=
  (Z ⬝ᵥ Z)⁻¹ • (ghat * Matrix.vecMulVec Z Z)

/-- The mass-preserving truncation of Section 5.2: `g' = H₁ + T`, where `T` replaces
`H₂ = ĝ (I - z zᵀ)`, `T Z = 0`, and `‖H₂ - T‖_F ≤ ϑ`.  The truncated SVD of the paper has these
properties, and for `ϑ = 0` they force `g' = ĝ` (`IsMassTruncation.eq_of_zero`), whichever SVD is
used. -/
def IsMassTruncation (Z : K → ℝ) (ϑ : ℝ) (ghat g' : Matrix (ZMod N) K ℝ) : Prop :=
  ∃ T : Matrix (ZMod N) K ℝ, g' = massPart Z ghat + T ∧ T *ᵥ Z = 0 ∧
    ∑ j, ∑ k, ((ghat - massPart Z ghat - T) j k) ^ 2 ≤ ϑ ^ 2

/-- One step of the DLRA scheme (15) of arXiv 2411.06844 from `ρ`, `g = X S Vᵀ`, in projector form:
`ρ'` is (15a); `PX`, `PV` are the orthogonal projectors onto the twice augmented spaces (15b)-(15e),
with `K^{n+1} = G V` and `L^{n+1} = Xᵀ G`; `ghat = (1 + σΔt)⁻¹ PX G PV` is `X̂̂ Ŝ̂ V̂̂ᵀ` for (15f),
because `g̃ = PX g PV = g` (`IsDLRAStep.proj_fix`); `g'` is the truncation.  (15d) is printed in
the paper with `D^x_{ij}` where the projection of (14a) gives `D^x_{ji}`; the projection is used
here. -/
structure IsDLRAStep [DecidableEq r] (σ dt dx ϑ : ℝ) (v ω : K → ℝ) (ρ : ZMod N → ℝ)
    (X : Matrix (ZMod N) r ℝ) (S : Matrix r r ℝ) (V : Matrix K r ℝ) (ρ' : ZMod N → ℝ)
    (PX : Matrix (ZMod N) (ZMod N) ℝ) (PV : Matrix K K ℝ) (ghat g' : Matrix (ZMod N) K ℝ) :
    Prop where
  orthX : Xᵀ * X = 1
  orthV : Vᵀ * V = 1
  density : ∀ j, ρ' j = densityNext dt dx v ω ρ (X * S * Vᵀ) j
  projX : IsOrthProjOnto PX
    (augment (fun j => ρ' j ^ 2) (rhsG σ dt dx v ρ ρ' (X * S * Vᵀ) * V) X)
  projV : IsOrthProjOnto PV
    (augment (fun k => ω k * Real.exp (v k ^ 2 / 2)) ((rhsG σ dt dx v ρ ρ' (X * S * Vᵀ))ᵀ * X) V)
  sStep : ghat = (1 + σ * dt)⁻¹ • (PX * rhsG σ dt dx v ρ ρ' (X * S * Vᵀ) * PV)
  trunc : IsMassTruncation (quadZ v ω) ϑ ghat g'

omit [DecidableEq K] in
/-- With `ϑ = 0` the truncation does nothing.
arXiv 2411.06844, Section 5.2. -/
theorem IsMassTruncation.eq_of_zero {Z : K → ℝ} {ghat g' : Matrix (ZMod N) K ℝ}
    (h : IsMassTruncation Z 0 ghat g') : g' = ghat := by
  obtain ⟨T, h1, -, h3⟩ := h
  have hz : ∀ j k, (ghat - massPart Z ghat - T) j k = 0 := by
    have h0 : ∑ j, ∑ k, ((ghat - massPart Z ghat - T) j k) ^ 2 = 0 :=
      le_antisymm (by simpa using h3)
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    intro j k
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).1 h0 j (Finset.mem_univ j)
    have h5 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => sq_nonneg _)).1 h4 k (Finset.mem_univ k)
    exact pow_eq_zero_iff (two_ne_zero) |>.1 h5
  rw [h1]
  ext j k
  have := hz j k
  simp only [Matrix.sub_apply, Matrix.add_apply] at this ⊢
  linarith

omit [NeZero N] [DecidableEq K] in
/-- `massPart` carries the whole mass: `H₁ Z = ĝ Z`.
arXiv 2411.06844, Section 5.2. -/
theorem massPart_mulVec {Z : K → ℝ} (hZ : Z ≠ 0) (ghat : Matrix (ZMod N) K ℝ) :
    massPart Z ghat *ᵥ Z = ghat *ᵥ Z := by
  have hne : Z ⬝ᵥ Z ≠ 0 := fun h => hZ (dotProduct_self_eq_zero.1 h)
  have e : Matrix.vecMulVec Z Z *ᵥ Z = (Z ⬝ᵥ Z) • Z := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [massPart, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_smul, smul_smul,
    inv_mul_cancel₀ hne, one_smul]

omit [DecidableEq K] in
/-- The truncation keeps the relation (11), which is the purpose of the construction in the paper:
`g' Z = ĝ Z`.
arXiv 2411.06844, Section 5.2. -/
theorem IsMassTruncation.mulVec {Z : K → ℝ} (hZ : Z ≠ 0) {ϑ : ℝ}
    {ghat g' : Matrix (ZMod N) K ℝ} (h : IsMassTruncation Z ϑ ghat g') :
    g' *ᵥ Z = ghat *ᵥ Z := by
  obtain ⟨T, h1, h2, -⟩ := h
  rw [h1, Matrix.add_mulVec, h2, add_zero, massPart_mulVec hZ]

omit [NeZero N] [Fintype K] [DecidableEq K] in
/-- `G` in upwind form. -/
lemma rhsG_apply (σ dt dx : ℝ) (v : K → ℝ) (ρ : ZMod N → ℝ) {ρ' : ZMod N → ℝ}
    (hρ' : ∀ j, ρ' j ≠ 0) (g : Matrix (ZMod N) K ℝ) (j : ZMod N) (k : K) :
    rhsG σ dt dx v ρ ρ' g j k
      = (ρ j * g j k - dt * upw dx (v k) (fun i => ρ i * g i k) j) / ρ' j + σ * dt := by
  have := hρ' j
  simp only [rhsG, Matrix.of_apply, upw]
  field_simp
  ring

omit [NeZero N] [DecidableEq K] in
/-- `G Z = (1 + σΔt) 𝟙`: the mass balance behind `1 = ĝ Z`, from (15a), (11), `QuadNormalized`. -/
lemma rhsG_mulVec {σ dt dx : ℝ} {v ω : K → ℝ} {ρ ρ' : ZMod N → ℝ} {g : Matrix (ZMod N) K ℝ}
    (hρ' : ∀ j, ρ' j ≠ 0) (hd : ∀ j, ρ' j = densityNext dt dx v ω ρ g j)
    (hg : IsNormalized v ω g) (hm : QuadNormalized v ω) :
    rhsG σ dt dx v ρ ρ' g *ᵥ quadZ v ω = fun _ => 1 + σ * dt := by
  funext j
  simp only [Matrix.mulVec, dotProduct]
  have h1 := (hd j).trans (densityNext_eq dt dx v ω ρ g j)
  have h2 := hρ' j
  calc ∑ k, rhsG σ dt dx v ρ ρ' g j k * quadZ v ω k
      = (ρ j * ∑ k, g j k * quadZ v ω k
          - dt * ∑ k, upw dx (v k) (fun i => ρ i * g i k) j * quadZ v ω k) / ρ' j
        + σ * dt * ∑ k, quadZ v ω k := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          Finset.sum_div, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [rhsG_apply _ _ _ _ _ hρ']
        field_simp
    _ = 1 + σ * dt := by
        rw [hg j, mul_one, ← h1, div_self h2, hm, mul_one]

omit [Fintype K] [DecidableEq K] [Fintype r] in
private lemma col_mem_colSpace {m c : Type*} [Fintype c] (A : Matrix m c ℝ) (b : c) :
    (fun i => A i b) ∈ colSpace A := by
  classical
  refine ⟨Pi.single b 1, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  rfl

omit [DecidableEq K] in
private lemma colSpace_le_augment_right {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    (A B : Matrix ι r ℝ) : colSpace B ≤ augment w A B :=
  le_sup_right.trans le_sup_left

omit [DecidableEq K] in
private lemma sup_le_augment {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    (A B : Matrix ι r ℝ) : colSpace A ⊔ colSpace B ≤ augment w A B := le_sup_left

omit [DecidableEq K] in
private lemma colSpace_le_augment_left {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    (A B : Matrix ι r ℝ) : colSpace A ≤ augment w A B :=
  le_sup_left.trans le_sup_left

omit [DecidableEq K] in
private lemma mem_augment_diag {ι : Type*} [Fintype ι] [DecidableEq ι] {w : ι → ℝ}
    {A B : Matrix ι r ℝ} {x : ι → ℝ} (hx : x ∈ colSpace A ⊔ colSpace B) :
    (fun i => w i * x i) ∈ augment w A B := by
  refine Submodule.mem_sup_right ⟨x, hx, ?_⟩
  funext i
  simp [Matrix.mulVec_diagonal]

omit [NeZero N] in
/-- If `𝟙 ∈ 𝒱̂`, then `Z ∈ 𝒱̂̂` by the second augmentation (15e).
arXiv 2411.06844, augmentation (15e). -/
theorem quadZ_mem_of_one_mem {v ω : K → ℝ} (A B : Matrix K r ℝ)
    (h : (fun _ : K => (1 : ℝ)) ∈ colSpace A ⊔ colSpace B) :
    quadZ v ω ∈ augment (fun k => ω k * Real.exp (v k ^ 2 / 2)) A B := by
  have e : quadZ v ω = (1 / Real.sqrt (2 * Real.pi)) •
      fun k => (ω k * Real.exp (v k ^ 2 / 2)) * (fun _ : K => (1 : ℝ)) k := by
    funext k
    simp only [quadZ, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  exact Submodule.smul_mem _ _ (mem_augment_diag h)

variable [DecidableEq r]

/-- `X S Vᵀ` lies in the augmented spaces, so `g̃ = g` in (15f).
arXiv 2411.06844, S-step (15f). -/
theorem IsDLRAStep.proj_fix {σ dt dx ϑ : ℝ} {v ω : K → ℝ} {ρ ρ' : ZMod N → ℝ}
    {X : Matrix (ZMod N) r ℝ} {S : Matrix r r ℝ} {V : Matrix K r ℝ}
    {PX : Matrix (ZMod N) (ZMod N) ℝ} {PV : Matrix K K ℝ} {ghat g' : Matrix (ZMod N) K ℝ}
    (h : IsDLRAStep σ dt dx ϑ v ω ρ X S V ρ' PX PV ghat g') :
    PX * (X * S * Vᵀ) * PV = X * S * Vᵀ := by
  have hX : PX * X = X := by
    apply Matrix.ext
    intro j c
    exact congrFun (h.projX.fix (fun i => X i c)
      (colSpace_le_augment_right _ _ _ (col_mem_colSpace X c))) j
  have hV : PV * V = V := by
    apply Matrix.ext
    intro j c
    exact congrFun (h.projV.fix (fun i => V i c)
      (colSpace_le_augment_right _ _ _ (col_mem_colSpace V c))) j
  have hV' : Vᵀ * PV = Vᵀ := by
    have := congrArg Matrix.transpose hV
    rwa [Matrix.transpose_mul, h.projV.symm] at this
  calc PX * (X * S * Vᵀ) * PV = (PX * X) * S * (Vᵀ * PV) := by
        simp only [Matrix.mul_assoc]
    _ = X * S * Vᵀ := by rw [hX, hV']

/-- The Frobenius pairing and symmetric projectors: `⟨P G Q, W⟩ = ⟨G, P W Q⟩`. -/
private lemma fro_proj {m n : Type*} [Fintype m] [Fintype n]
    {P : Matrix m m ℝ} {Q : Matrix n n ℝ} (hP : Pᵀ = P) (hQ : Qᵀ = Q) (G W : Matrix m n ℝ) :
    ∑ j, ∑ k, (P * G * Q) j k * W j k = ∑ j, ∑ k, G j k * (P * W * Q) j k := by
  have e : ∀ A B : Matrix m n ℝ, ∑ j, ∑ k, A j k * B j k = (Aᵀ * B).trace := by
    intro A B
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_comm
  rw [e, e, Matrix.transpose_mul, Matrix.transpose_mul, hP, hQ]
  calc (Q * (Gᵀ * P) * W).trace = (Q * ((Gᵀ * P) * W)).trace := by rw [Matrix.mul_assoc]
    _ = (((Gᵀ * P) * W) * Q).trace := Matrix.trace_mul_comm _ _
    _ = (Gᵀ * (P * W * Q)).trace := by simp only [Matrix.mul_assoc]

variable {σ dt dx ϑ : ℝ} {v ω : K → ℝ} {ρ ρ' : ZMod N → ℝ}
  {X : Matrix (ZMod N) r ℝ} {S : Matrix r r ℝ} {V : Matrix K r ℝ}
  {PX : Matrix (ZMod N) (ZMod N) ℝ} {PV : Matrix K K ℝ} {ghat g' : Matrix (ZMod N) K ℝ}

/-- The claim `1 = ĝ Z` of Section 5.2 of arXiv 2411.06844.  The paper states it without proof.
`𝟙 ∈ range X` follows from `1 = g Z`, whereas `Z ∈ 𝒱̂̂` has to be assumed.  It holds from the
second step on because the truncation puts `z` into `V^{n+1}`, and at the first step if
`𝟙 ∈ range V`, as for `g⁰ ≡ 1` (`quadZ_mem_of_one_mem`). -/
theorem IsDLRAStep.normalized (h : IsDLRAStep σ dt dx ϑ v ω ρ X S V ρ' PX PV ghat g')
    (hσ : 0 ≤ σ) (hdt : 0 ≤ dt) (hρ' : ∀ j, ρ' j ≠ 0) (hm : QuadNormalized v ω)
    (hg : IsNormalized v ω (X * S * Vᵀ))
    (hZ : quadZ v ω ∈ augment (fun k => ω k * Real.exp (v k ^ 2 / 2))
      ((rhsG σ dt dx v ρ ρ' (X * S * Vᵀ))ᵀ * X) V) :
    IsNormalized v ω ghat := by
  have hs : 1 + σ * dt ≠ 0 := by positivity
  have hone : (fun _ : ZMod N => (1 : ℝ)) = (X * S * Vᵀ) *ᵥ quadZ v ω :=
    funext fun j => (hg j).symm
  have hmem : (fun _ : ZMod N => (1 : ℝ)) ∈ colSpace X := by
    refine ⟨(S * Vᵀ) *ᵥ quadZ v ω, ?_⟩
    rw [hone, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hfix := h.projX.fix _ (colSpace_le_augment_right _ _ _ hmem)
  have hG := rhsG_mulVec (σ := σ) hρ' h.density hg hm
  have key : ghat *ᵥ quadZ v ω = fun _ => 1 := by
    rw [h.sStep, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      h.projV.fix _ hZ, hG]
    have e : (fun _ : ZMod N => 1 + σ * dt) = (1 + σ * dt) • fun _ : ZMod N => (1 : ℝ) := by
      funext j
      simp
    rw [e, Matrix.mulVec_smul, hfix, smul_smul, inv_mul_cancel₀ hs, one_smul]
  exact fun j => congrFun key j

omit [Fintype K] [Fintype r] in
/-- An orthogonal projector is idempotent. -/
private lemma IsOrthProjOnto.idem {ι : Type*} [Fintype ι] {Q : Matrix ι ι ℝ}
    {W : Submodule ℝ (ι → ℝ)} (h : IsOrthProjOnto Q W) : Q * Q = Q := by
  classical
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec, h.fix _ (h.mem x)]

omit [Fintype K] [Fintype r] in
/-- If the range of `P` is invariant under `diag(d)`, then `diag(d)` preserves `P`-fixed
matrices. -/
private lemma proj_diag_fix {ι c : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℝ}
    {W : Submodule ℝ (ι → ℝ)} (hP : IsOrthProjOnto P W) {d : ι → ℝ}
    (hinv : ∀ x ∈ W, (fun i => d i * x i) ∈ W) {A : Matrix ι c ℝ} (hA : P * A = A) :
    P * (Matrix.diagonal d * A) = Matrix.diagonal d * A := by
  ext i b
  have hcol : (fun i => A i b) ∈ W := by
    have e : (fun i => A i b) = P *ᵥ fun i => A i b := by
      funext i
      exact (congrFun (congrFun hA i) b).symm
    rw [e]
    exact hP.mem _
  have h := congrFun (hP.fix _ (hinv _ hcol)) i
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_mul]
  exact h

/-- **Theorem 3, the proof of the paper with its unproved step made explicit.**  Assume the two
equalities displayed in the proof of Theorem 3 of arXiv 2411.06844,
`Σ_α P^X_{αj} g_{αβ} (ρ_α)² = g_{jβ} (ρ_j)²` and `Σ_β P^V_{kβ} g_{jβ} ω_β e^{v_β²/2} = g_{jk} ω_k
e^{v_k²/2}` (with `quadZ` for the second, which differs by the factor `√(2π)`), and `1 = ĝ Z`.  Then
the S-step output satisfies the bound of Theorem 3.  These equalities do not follow from (15c),
(15e) and fail in `ce_displayed_equality_fails`. -/
theorem dlra_stable_of_equalities (h : IsDLRAStep σ dt dx ϑ v ω ρ X S V ρ' PX PV ghat g')
    (hσ : 0 ≤ σ) (hdt : 0 ≤ dt) (hdx : 0 < dx) (hω : ∀ k, 0 ≤ ω k) (hm : QuadNormalized v ω)
    (hcfl : ∀ k, |v k| * dt ≤ dx) (hρ' : ∀ j, ρ' j ≠ 0) (hnorm : IsNormalized v ω ghat)
    (hX : PX * (Matrix.diagonal (fun j => ρ' j ^ 2) * ghat)
      = Matrix.diagonal (fun j => ρ' j ^ 2) * ghat)
    (hV : ghat * Matrix.diagonal (quadZ v ω) * PV = ghat * Matrix.diagonal (quadZ v ω)) :
    hNormSq v ω (fOf v ρ' ghat) ≤ hNormSq v ω (fOf v ρ (X * S * Vᵀ)) := by
  rw [hNormSq_fOf v ω ρ' ghat, hNormSq_fOf v ω ρ (X * S * Vᵀ)]
  have hZ : ∀ k, 0 ≤ quadZ v ω k := fun k =>
    mul_nonneg (mul_nonneg (by positivity) (hω k)) (Real.exp_pos _).le
  set Z := quadZ v ω with hZdef
  set G := rhsG σ dt dx v ρ ρ' (X * S * Vᵀ) with hGdef
  set W : Matrix (ZMod N) K ℝ :=
    Matrix.diagonal (fun j => ρ' j ^ 2) * ghat * Matrix.diagonal Z with hWdef
  have hW : PX * W * PV = W := by
    calc PX * W * PV
        = PX * (Matrix.diagonal (fun j => ρ' j ^ 2) * (ghat * Matrix.diagonal Z * PV)) := by
          simp only [hWdef, Matrix.mul_assoc]
      _ = PX * (Matrix.diagonal (fun j => ρ' j ^ 2) * ghat) * Matrix.diagonal Z := by
          rw [hV]
          simp only [Matrix.mul_assoc]
      _ = W := by rw [hX]
  have hfro := fro_proj h.projX.symm h.projV.symm G W
  rw [hW] at hfro
  have hs : 1 + σ * dt ≠ 0 := by positivity
  have hM : PX * G * PV = (1 + σ * dt) • ghat := by
    rw [h.sStep, smul_smul, mul_inv_cancel₀ hs, one_smul]
  have hWa : ∀ j k, W j k = ρ' j ^ 2 * ghat j k * Z k := by
    intro j k
    simp only [hWdef, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine energy_core hσ hdt hdx hZ hcfl (m' := fun j _ => ρ' j) ?_
    (collision_sign hm hZ ρ' hnorm)
  have e1 : (1 + σ * dt) * zE Z (fun j k => ρ' j * ghat j k)
      = ∑ j, ∑ k, (PX * G * PV) j k * W j k := by
    simp only [zE, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hM, hWa, Matrix.smul_apply, smul_eq_mul]
    ring
  have e2 : ∑ j, ∑ k, G j k * W j k
      = zI Z (fun j k => ρ' j * ghat j k) (fun j k => ρ j * (X * S * Vᵀ) j k)
        - dt * zI Z (fun j k => ρ' j * ghat j k)
          (fun j k => upw dx (v k) (fun i => ρ i * (X * S * Vᵀ) i k) j)
        + σ * dt * zI Z (fun j k => ρ' j * ghat j k) (fun j _ => ρ' j) := by
    simp only [zI, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hWa, hGdef, rhsG_apply _ _ _ _ _ hρ']
    have := hρ' j
    field_simp
  rw [e1, hfro, e2]

/-- **Theorem 3, corrected.**  If the projected spaces are *invariant* under `diag(ρ'²)` and
`diag(ω e^{v²/2})`, i.e. the augmentations (15c), (15e) are iterated until nothing changes instead
of being applied once, then the conclusion of Theorem 3 of arXiv 2411.06844 holds for every
truncation that does not increase the `ℋ`-norm, in particular for `ϑ = 0`
(`IsMassTruncation.eq_of_zero`).  The Euclidean truncation with `ϑ > 0` is not `ℋ`-orthogonal, so
it has to be assumed non-expansive. `Z ∈ 𝒱̂̂` is discussed at `IsDLRAStep.normalized`. -/
theorem dlra_stable_of_invariant (h : IsDLRAStep σ dt dx ϑ v ω ρ X S V ρ' PX PV ghat g')
    (hσ : 0 ≤ σ) (hdt : 0 ≤ dt) (hdx : 0 < dx) (hω : ∀ k, 0 ≤ ω k) (hm : QuadNormalized v ω)
    (hcfl : ∀ k, |v k| * dt ≤ dx) (hρ' : ∀ j, ρ' j ≠ 0) (hg : IsNormalized v ω (X * S * Vᵀ))
    (hZ : quadZ v ω ∈ augment (fun k => ω k * Real.exp (v k ^ 2 / 2))
      ((rhsG σ dt dx v ρ ρ' (X * S * Vᵀ))ᵀ * X) V)
    (hinvX : ∀ x ∈ augment (fun j => ρ' j ^ 2) (rhsG σ dt dx v ρ ρ' (X * S * Vᵀ) * V) X,
      (fun j => ρ' j ^ 2 * x j) ∈
        augment (fun j => ρ' j ^ 2) (rhsG σ dt dx v ρ ρ' (X * S * Vᵀ) * V) X)
    (hinvV : ∀ x ∈ augment (fun k => ω k * Real.exp (v k ^ 2 / 2))
        ((rhsG σ dt dx v ρ ρ' (X * S * Vᵀ))ᵀ * X) V,
      (fun k => (ω k * Real.exp (v k ^ 2 / 2)) * x k) ∈
        augment (fun k => ω k * Real.exp (v k ^ 2 / 2))
          ((rhsG σ dt dx v ρ ρ' (X * S * Vᵀ))ᵀ * X) V)
    (htrunc : hNormSq v ω (fOf v ρ' g') ≤ hNormSq v ω (fOf v ρ' ghat)) :
    hNormSq v ω (fOf v ρ' g') ≤ hNormSq v ω (fOf v ρ (X * S * Vᵀ)) := by
  have hnorm := h.normalized hσ hdt hρ' hm hg hZ
  have hX1 : PX * ghat = ghat := by
    rw [h.sStep, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.projX.idem]
  have hV1 : ghat * PV = ghat := by
    rw [h.sStep, Matrix.smul_mul, Matrix.mul_assoc, h.projV.idem]
  have hV2 : PV * ghatᵀ = ghatᵀ := by
    have := congrArg Matrix.transpose hV1
    rwa [Matrix.transpose_mul, h.projV.symm] at this
  have hinvZ : ∀ x ∈ augment (fun k => ω k * Real.exp (v k ^ 2 / 2))
      ((rhsG σ dt dx v ρ ρ' (X * S * Vᵀ))ᵀ * X) V, (fun k => quadZ v ω k * x k) ∈
        augment (fun k => ω k * Real.exp (v k ^ 2 / 2))
          ((rhsG σ dt dx v ρ ρ' (X * S * Vᵀ))ᵀ * X) V := by
    intro x hx
    have e : (fun k => quadZ v ω k * x k) = (1 / Real.sqrt (2 * Real.pi)) •
        fun k => (ω k * Real.exp (v k ^ 2 / 2)) * x k := by
      funext k
      simp only [quadZ, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (hinvV x hx)
  have hX := proj_diag_fix h.projX hinvX hX1
  have hV3 := proj_diag_fix h.projV hinvZ hV2
  have hV : ghat * Matrix.diagonal (quadZ v ω) * PV = ghat * Matrix.diagonal (quadZ v ω) := by
    have := congrArg Matrix.transpose hV3
    simpa only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.transpose_transpose,
      h.projV.symm] using this
  exact htrunc.trans (dlra_stable_of_equalities h hσ hdt hdx hω hm hcfl hρ' hnorm hX hV)

/-- The invariance hypotheses of `dlra_stable_of_invariant` hold for arbitrary bases when `ρ'` and
`ω e^{v²/2}` are constant, since then the augmentations (15c), (15e) add nothing.
arXiv 2411.06844, Theorem 3, corrected. -/
theorem dlra_stable_of_scalar_weights (h : IsDLRAStep σ dt dx ϑ v ω ρ X S V ρ' PX PV ghat g')
    (hσ : 0 ≤ σ) (hdt : 0 ≤ dt) (hdx : 0 < dx) (hω : ∀ k, 0 ≤ ω k) (hm : QuadNormalized v ω)
    (hcfl : ∀ k, |v k| * dt ≤ dx) (hρ' : ∀ j, ρ' j ≠ 0) (hg : IsNormalized v ω (X * S * Vᵀ))
    (hZ : quadZ v ω ∈ augment (fun k => ω k * Real.exp (v k ^ 2 / 2))
      ((rhsG σ dt dx v ρ ρ' (X * S * Vᵀ))ᵀ * X) V)
    {c d : ℝ} (hc : ∀ j, ρ' j = c) (hd : ∀ k, ω k * Real.exp (v k ^ 2 / 2) = d)
    (htrunc : hNormSq v ω (fOf v ρ' g') ≤ hNormSq v ω (fOf v ρ' ghat)) :
    hNormSq v ω (fOf v ρ' g') ≤ hNormSq v ω (fOf v ρ (X * S * Vᵀ)) := by
  refine dlra_stable_of_invariant h hσ hdt hdx hω hm hcfl hρ' hg hZ (fun x hx => ?_)
    (fun x hx => ?_) htrunc
  · have e : (fun j => ρ' j ^ 2 * x j) = c ^ 2 • x := by
      funext j
      simp only [hc, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact Submodule.smul_mem _ _ hx
  · have e : (fun k => (ω k * Real.exp (v k ^ 2 / 2)) * x k) = d • x := by
      funext k
      simp only [hd, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact Submodule.smul_mem _ _ hx

omit [DecidableEq K] in
/-- With `ℋ`-orthogonal projection in place of (15f) no augmentation is needed: if `gapp` is the
`ℋ`-orthogonal projection of the full conservative step `gfull` onto any set (only the
orthogonality relation is used), then `‖fapp‖_ℋ ≤ ‖f‖_ℋ`.  This is not in the paper; it is the other
way to repair Theorem 3, and the weighted form of `augmentedBug_euler_norm_le`.
arXiv 2411.06844, Theorem 3, a repair that is not in the paper. -/
theorem hGalerkin_stable (hσ : 0 ≤ σ) (hdt : 0 ≤ dt) (hdx : 0 < dx) (hω : ∀ k, 0 ≤ ω k)
    (hm : QuadNormalized v ω) (hcfl : ∀ k, |v k| * dt ≤ dx) {g gfull gapp : ZMod N → K → ℝ}
    (hρ : ∀ j, ρ j ≠ 0) (hfull : IsConservativeStep σ dt dx v ω ρ g ρ' gfull)
    (hn : IsNormalized v ω gfull)
    (horth : zI (quadZ v ω) (fun j k => ρ' j * (gfull j k - gapp j k))
      (fun j k => ρ' j * gapp j k) = 0) :
    hNormSq v ω (fOf v ρ' gapp) ≤ hNormSq v ω (fOf v ρ g) := by
  refine le_trans ?_ (theorem2_step hσ hdt hdx hω hm hcfl hρ hfull hn)
  rw [hNormSq_fOf, hNormSq_fOf]
  have hZ : ∀ k, 0 ≤ quadZ v ω k := fun k =>
    mul_nonneg (mul_nonneg (by positivity) (hω k)) (Real.exp_pos _).le
  have hnn : 0 ≤ zE (quadZ v ω) (fun j k => ρ' j * (gfull j k - gapp j k)) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (hZ k)
  have hexp : zE (quadZ v ω) (fun j k => ρ' j * gfull j k)
      = zE (quadZ v ω) (fun j k => ρ' j * gapp j k)
        + zE (quadZ v ω) (fun j k => ρ' j * (gfull j k - gapp j k))
        + 2 * zI (quadZ v ω) (fun j k => ρ' j * (gfull j k - gapp j k))
          (fun j k => ρ' j * gapp j k) := by
    simp only [zE, zI, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hexp, horth]
  linarith

end DLRA

/-! ### Theorem 3 is false as stated -/

section Counterexample

/-- A function on `ZMod 5`, given by its five values. -/
def v5 (a b c d e : ℝ) (j : ZMod 5) : ℝ :=
  if j = 0 then a else if j = 1 then b else if j = 2 then c else if j = 3 then d else e

private lemma v5_0 (a b c d e : ℝ) : v5 a b c d e 0 = a := by
  rw [v5, ite_eq_left rfl]

private lemma v5_1 (a b c d e : ℝ) : v5 a b c d e 1 = b := by
  rw [v5, ite_eq_right (show (1 : ZMod 5) ≠ 0 by decide), ite_eq_left rfl]

private lemma v5_2 (a b c d e : ℝ) : v5 a b c d e 2 = c := by
  rw [v5, ite_eq_right (show (2 : ZMod 5) ≠ 0 by decide),
    ite_eq_right (show (2 : ZMod 5) ≠ 1 by decide), ite_eq_left rfl]

private lemma v5_3 (a b c d e : ℝ) : v5 a b c d e 3 = d := by
  rw [v5, ite_eq_right (show (3 : ZMod 5) ≠ 0 by decide),
    ite_eq_right (show (3 : ZMod 5) ≠ 1 by decide),
    ite_eq_right (show (3 : ZMod 5) ≠ 2 by decide), ite_eq_left rfl]

private lemma v5_4 (a b c d e : ℝ) : v5 a b c d e 4 = e := by
  rw [v5, ite_eq_right (show (4 : ZMod 5) ≠ 0 by decide),
    ite_eq_right (show (4 : ZMod 5) ≠ 1 by decide),
    ite_eq_right (show (4 : ZMod 5) ≠ 2 by decide), ite_eq_right (show (4 : ZMod 5) ≠ 3 by decide)]

private lemma sum_z5 (f : ZMod 5 → ℝ) : ∑ j, f j = f 0 + f 1 + f 2 + f 3 + f 4 :=
  Fin.sum_univ_five f

private lemma forall_z5 {P : ZMod 5 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3)
    (h4 : P 4) (j : ZMod 5) : P j := by
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
    revert j
    decide
  rcases this with rfl | rfl | rfl | rfl | rfl <;> assumption

private lemma forall_f3 {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (k : Fin 3) : P k := by
  have : k = 0 ∨ k = 1 ∨ k = 2 := by
    revert k
    decide
  rcases this with rfl | rfl | rfl <;> assumption

private lemma s0 : (0 : ZMod 5) + 1 = 1 := by decide
private lemma s1 : (1 : ZMod 5) + 1 = 2 := by decide
private lemma s2 : (2 : ZMod 5) + 1 = 3 := by decide
private lemma s3 : (3 : ZMod 5) + 1 = 4 := by decide
private lemma s4 : (4 : ZMod 5) + 1 = 0 := by decide
private lemma p0 : (0 : ZMod 5) - 1 = 4 := by decide
private lemma p1 : (1 : ZMod 5) - 1 = 0 := by decide
private lemma p2 : (2 : ZMod 5) - 1 = 1 := by decide
private lemma p3 : (3 : ZMod 5) - 1 = 2 := by decide
private lemma p4 : (4 : ZMod 5) - 1 = 3 := by decide

/-- The nodes `0, ±√3` of the three-point Gauss-Hermite rule for the weight `e^{-v²/2}`. -/
noncomputable def ceV : Fin 3 → ℝ := ![-Real.sqrt 3, 0, Real.sqrt 3]

/-- The weights `1/6, 2/3, 1/6` of that rule: `Z_k = ω_k e^{v_k²/2} / √(2π)`. -/
noncomputable def ceZ : Fin 3 → ℝ := ![1 / 6, 2 / 3, 1 / 6]

/-- The weights `ω_k`, chosen so that `quadZ ceV ceω = ceZ`. -/
noncomputable def ceω (k : Fin 3) : ℝ :=
  Real.sqrt (2 * Real.pi) * ceZ k * Real.exp (-(ceV k ^ 2) / 2)

/-- `Δt = 0.9 Δx / max |v|`. -/
noncomputable def ceDt : ℝ := 9 / (50 * Real.sqrt 3)

/-- `σ = 5√3 / 9`, so that `σ Δt = 1/10`. -/
noncomputable def ceSigma : ℝ := 5 * Real.sqrt 3 / 9

/-- The density at time `tₙ`. -/
noncomputable def ceρ : ZMod 5 → ℝ := v5 1 2 9 10 11

/-- The density at time `t_{n+1}`. -/
noncomputable def ceρ' : ZMod 5 → ℝ := v5 (53 / 20) (29 / 10) (81 / 10) 10 (187 / 20)

/-- Row `j` of the first column of the explicit upwind step of `ρ`, for `v = -√3`. -/
noncomputable def ceU0 : ZMod 5 → ℝ := v5 (19 / 10) (83 / 10) (99 / 10) (109 / 10) 2

/-- The same for `v = √3`. -/
noncomputable def ceU2 : ZMod 5 → ℝ := v5 10 (11 / 10) (27 / 10) (91 / 10) (101 / 10)

/-- The explicit upwind step of `ρ`, by velocity. -/
noncomputable def ceU : Fin 3 → ZMod 5 → ℝ := ![ceU0, ceρ, ceU2]

/-- The spatial basis `X = 𝟙/√5` of rank one. -/
noncomputable def ceX : Matrix (ZMod 5) Unit ℝ := Matrix.of fun _ _ => 1 / Real.sqrt 5

/-- The velocity basis `V = 𝟙/√3` of rank one. -/
noncomputable def ceB : Matrix (Fin 3) Unit ℝ := Matrix.of fun _ _ => 1 / Real.sqrt 3

/-- The coefficient `S = √15`, so that `X S Vᵀ ≡ 1`. -/
noncomputable def ceS : Matrix Unit Unit ℝ := Matrix.of fun _ _ => Real.sqrt 5 * Real.sqrt 3

/-- The operator `G` of (14a) for this state. -/
noncomputable def ceG : Matrix (ZMod 5) (Fin 3) ℝ :=
  Matrix.of fun j k => ceU k j / ceρ' j + 1 / 10

/-- `Σ_k G_{jk}`, proportional to `K^{n+1} = G V`. -/
noncomputable def ceKt : ZMod 5 → ℝ := v5 (2739 / 530) (1227 / 290) (89 / 30) (33 / 10) (471 / 170)

/-- `Σ_j G_{jk}`, proportional to `L^{n+1} = Xᵀ G`. -/
noncomputable def ceLt : Fin 3 → ℝ :=
  ![(1708607789 / 258677100), (2283223 / 470322), (601548637 / 86225700)]

/-- The normal vector of the four-dimensional space `𝒳̂̂`. -/
noncomputable def ceN : ZMod 5 → ℝ := v5 (-310087577) 556014274 (-779418774) 159011300 374480777

/-- `n · G_k / n · n`, the coefficient removed from column `k` by the projection. -/
noncomputable def ceκ : Fin 3 → ℝ :=
  ![(669826467 / 1178320249435354810), 0, (-(669826467 / 1178320249435354810))]

/-- The result `ĝ` of the S-step. -/
noncomputable def ceGhat : Matrix (ZMod 5) (Fin 3) ℝ :=
  Matrix.of fun j k => 10 / 11 * (ceG j k - ceκ k * ceN j)

private lemma sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)

private lemma sqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)

private lemma ceDt_mul : ceDt * Real.sqrt 3 = 9 / 10 * (1 / 5) := by
  have h := sqrt3_pos.ne'
  calc ceDt * Real.sqrt 3 = 9 / 50 * (Real.sqrt 3 / Real.sqrt 3) := by
        rw [ceDt]
        ring
    _ = 9 / 10 * (1 / 5) := by
        rw [div_self h]
        norm_num

private lemma ceDt_pos : 0 < ceDt := by
  have := sqrt3_pos
  rw [ceDt]
  positivity

private lemma ceSigma_mul : ceSigma * ceDt = 1 / 10 := by
  have h := sqrt3_pos.ne'
  calc ceSigma * ceDt = 1 / 10 * (Real.sqrt 3 / Real.sqrt 3) := by
        rw [ceSigma, ceDt]
        ring
    _ = 1 / 10 := by rw [div_self h, mul_one]

private lemma ceZ_pos : ∀ k, 0 < ceZ k := by
  refine forall_f3 ?_ ?_ ?_
  · change (0 : ℝ) < 1 / 6
    norm_num
  · change (0 : ℝ) < 2 / 3
    norm_num
  · change (0 : ℝ) < 1 / 6
    norm_num

private lemma ceρ_pos : ∀ j, 0 < ceρ j := by
  refine forall_z5 ?_ ?_ ?_ ?_ ?_ <;>
    simp only [ceρ, v5_0, v5_1, v5_2, v5_3, v5_4] <;> norm_num

private lemma ceρ'_pos : ∀ j, 0 < ceρ' j := by
  refine forall_z5 ?_ ?_ ?_ ?_ ?_ <;>
    simp only [ceρ', v5_0, v5_1, v5_2, v5_3, v5_4] <;> norm_num

private lemma ceω_pos (k : Fin 3) : 0 < ceω k :=
  mul_pos (mul_pos (Real.sqrt_pos.2 (by positivity)) (ceZ_pos k)) (Real.exp_pos _)

private lemma ce_quadZ : quadZ ceV ceω = ceZ := by
  funext k
  have hs := sqrt_two_pi_ne
  have he : Real.exp (-(ceV k ^ 2) / 2) * Real.exp (ceV k ^ 2 / 2) = 1 := by
    rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
  simp only [quadZ, ceω]
  calc 1 / Real.sqrt (2 * Real.pi) * (Real.sqrt (2 * Real.pi) * ceZ k *
        Real.exp (-(ceV k ^ 2) / 2)) * Real.exp (ceV k ^ 2 / 2)
      = (1 / Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi)) * ceZ k *
          (Real.exp (-(ceV k ^ 2) / 2) * Real.exp (ceV k ^ 2 / 2)) := by ring
    _ = ceZ k := by
        rw [he, one_div, inv_mul_cancel₀ hs]
        ring

private lemma ce_quad : QuadNormalized ceV ceω := by
  have z0 : ceZ 0 = 1 / 6 := rfl
  have z1 : ceZ 1 = 2 / 3 := rfl
  have z2 : ceZ 2 = 1 / 6 := rfl
  rw [QuadNormalized, ce_quadZ, Fin.sum_univ_three, z0, z1, z2]
  norm_num

private lemma ce_cfl : ∀ k, |ceV k| * ceDt < 1 / 5 := by
  have h3 := sqrt3_pos
  have h := ceDt_mul
  refine forall_f3 ?_ ?_ ?_
  · have e : ceV 0 = -Real.sqrt 3 := rfl
    rw [e, abs_neg, abs_of_pos h3, mul_comm, h]
    norm_num
  · have e : ceV 1 = 0 := rfl
    rw [e]
    simp
  · have e : ceV 2 = Real.sqrt 3 := rfl
    rw [e, abs_of_pos h3, mul_comm, h]
    norm_num

/-- `g = X S Vᵀ ≡ 1`.
arXiv 2411.06844, counterexample to Theorem 3. -/
theorem ce_g (j : ZMod 5) (k : Fin 3) : (ceX * ceS * ceBᵀ) j k = 1 := by
  have h3 := sqrt3_pos.ne'
  have h5 := sqrt5_pos.ne'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, ceX, ceS, ceB, Matrix.of_apply,
    Finset.univ_unique, Finset.sum_singleton]
  field_simp

private lemma upw_step_left {dx dt a l : ℝ} (hdx : dx ≠ 0) (ha : a ≤ 0) (hl : dt * -a = l * dx)
    (z : ZMod 5 → ℝ) (j : ZMod 5) :
    z j - dt * upw dx a z j = (1 - l) * z j + l * z (j + 1) := by
  rw [upw_of_nonpos hdx ha]
  simp only [Dp]
  field_simp
  linear_combination (z (j + 1) - z j) * hl

private lemma upw_step_right {dx dt a l : ℝ} (hdx : dx ≠ 0) (ha : 0 ≤ a) (hl : dt * a = l * dx)
    (z : ZMod 5 → ℝ) (j : ZMod 5) :
    z j - dt * upw dx a z j = (1 - l) * z j + l * z (j - 1) := by
  rw [upw_of_nonneg hdx ha]
  simp only [Dp, sub_add_cancel]
  field_simp
  linear_combination (z (j - 1) - z j) * hl

private lemma ce_U : ∀ (k : Fin 3) (j : ZMod 5),
    ceρ j - ceDt * upw (1 / 5) (ceV k) ceρ j = ceU k j := by
  have h5 : (1 / 5 : ℝ) ≠ 0 := by norm_num
  have h3 := sqrt3_pos
  refine forall_f3 ?_ ?_ ?_
  · intro j
    have h := upw_step_left (dx := 1 / 5) (dt := ceDt) (a := -Real.sqrt 3) (l := 9 / 10) h5
      (by linarith) (by rw [neg_neg]; exact ceDt_mul) ceρ j
    have e : ceV 0 = -Real.sqrt 3 := rfl
    have e2 : ceU 0 = ceU0 := rfl
    rw [e, h, e2]
    clear h
    revert j
    refine forall_z5 ?_ ?_ ?_ ?_ ?_ <;>
      simp only [ceρ, ceU0, s0, s1, s2, s3, s4, v5_0, v5_1, v5_2, v5_3, v5_4] <;> norm_num
  · intro j
    have e : ceV 1 = 0 := rfl
    have e2 : ceU 1 = ceρ := rfl
    rw [e, e2]
    simp [upw]
  · intro j
    have h := upw_step_right (dx := 1 / 5) (dt := ceDt) (a := Real.sqrt 3) (l := 9 / 10) h5
      h3.le ceDt_mul ceρ j
    have e : ceV 2 = Real.sqrt 3 := rfl
    have e2 : ceU 2 = ceU2 := rfl
    rw [e, h, e2]
    clear h
    revert j
    refine forall_z5 ?_ ?_ ?_ ?_ ?_ <;>
      simp only [ceρ, ceU2, p0, p1, p2, p3, p4, v5_0, v5_1, v5_2, v5_3, v5_4] <;> norm_num

private lemma ce_u (k : Fin 3) : (fun i => ceρ i * (ceX * ceS * ceBᵀ) i k) = ceρ := by
  funext i
  rw [ce_g, mul_one]

private lemma ce_mean : ∀ j, ceρ' j = 1 / 6 * ceU 0 j + 2 / 3 * ceU 1 j + 1 / 6 * ceU 2 j := by
  have e0 : ceU 0 = ceU0 := rfl
  have e1 : ceU 1 = ceρ := rfl
  have e2 : ceU 2 = ceU2 := rfl
  rw [e0, e1, e2]
  refine forall_z5 ?_ ?_ ?_ ?_ ?_ <;>
    simp only [ceρ, ceρ', ceU0, ceU2, v5_0, v5_1, v5_2, v5_3, v5_4] <;> norm_num

private lemma ce_density (j : ZMod 5) :
    ceρ' j = densityNext ceDt (1 / 5) ceV ceω ceρ (ceX * ceS * ceBᵀ) j := by
  have h0 := ce_U 0 j
  have h1 := ce_U 1 j
  have h2 := ce_U 2 j
  rw [densityNext_eq ceDt (1 / 5) ceV ceω ceρ (ceX * ceS * ceBᵀ) j, ce_quadZ]
  simp only [ce_u, Fin.sum_univ_three]
  rw [ce_mean, ← h0, ← h1, ← h2]
  have z0 : ceZ 0 = 1 / 6 := rfl
  have z1 : ceZ 1 = 2 / 3 := rfl
  have z2 : ceZ 2 = 1 / 6 := rfl
  rw [z0, z1, z2]
  ring

private lemma ce_rhsG : rhsG ceSigma ceDt (1 / 5) ceV ceρ ceρ' (ceX * ceS * ceBᵀ) = ceG := by
  ext j k
  rw [rhsG_apply _ _ _ _ _ fun j => (ceρ'_pos j).ne', ce_u, ce_g, mul_one, ce_U, ceSigma_mul]
  rfl

private lemma ce_Gsum (j : ZMod 5) : ∑ k, ceG j k = ceKt j := by
  rw [Fin.sum_univ_three]
  have e0 : ceU 0 = ceU0 := rfl
  have e1 : ceU 1 = ceρ := rfl
  have e2 : ceU 2 = ceU2 := rfl
  simp only [ceG, Matrix.of_apply, e0, e1, e2]
  revert j
  refine forall_z5 ?_ ?_ ?_ ?_ ?_ <;>
    simp only [ceρ, ceρ', ceU0, ceU2, ceKt, v5_0, v5_1, v5_2, v5_3, v5_4] <;> norm_num

private lemma ce_Lsum : ∀ k, ∑ j, ceG j k = ceLt k := by
  have e0 : ceU 0 = ceU0 := rfl
  have e1 : ceU 1 = ceρ := rfl
  have e2 : ceU 2 = ceU2 := rfl
  have l0 : ceLt 0 = (1708607789 / 258677100) := rfl
  have l1 : ceLt 1 = (2283223 / 470322) := rfl
  have l2 : ceLt 2 = (601548637 / 86225700) := rfl
  refine forall_f3 ?_ ?_ ?_ <;> rw [sum_z5] <;>
    simp only [ceG, Matrix.of_apply, e0, e1, e2, l0, l1, l2, ceρ, ceρ', ceU0, ceU2, v5_0, v5_1,
      v5_2, v5_3, v5_4] <;> norm_num

private lemma ce_colK : (fun j => (ceG * ceB) j ()) = (1 / Real.sqrt 3) • ceKt := by
  funext j
  simp only [Matrix.mul_apply, ceB, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_mul,
    ce_Gsum]
  ring

private lemma ce_colL : (fun k => (ceGᵀ * ceX) k ()) = (1 / Real.sqrt 5) • ceLt := by
  funext k
  simp only [Matrix.mul_apply, ceX, Matrix.of_apply, Matrix.transpose_apply, Pi.smul_apply,
    smul_eq_mul, ← Finset.sum_mul, ce_Lsum]
  ring

private lemma colSpace_unit_le {ι : Type*} {W : Submodule ℝ (ι → ℝ)} (A : Matrix ι Unit ℝ)
    (h : (fun i => A i ()) ∈ W) : colSpace A ≤ W := by
  rintro _ ⟨x, rfl⟩
  have e : A.mulVecLin x = x () • fun i => A i () := by
    funext i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  rw [e]
  exact W.smul_mem _ h

private lemma augment_le_of_cols {ι : Type*} [Fintype ι] [DecidableEq ι] {w : ι → ℝ}
    {A B : Matrix ι Unit ℝ} {W : Submodule ℝ (ι → ℝ)} (ha : (fun i => A i ()) ∈ W)
    (hb : (fun i => B i ()) ∈ W) (hwa : (fun i => w i * A i ()) ∈ W)
    (hwb : (fun i => w i * B i ()) ∈ W) : augment w A B ≤ W := by
  refine sup_le (sup_le (colSpace_unit_le A ha) (colSpace_unit_le B hb)) ?_
  rw [Submodule.map_le_iff_le_comap]
  have e : ∀ C : Matrix ι Unit ℝ, (Matrix.diagonal w).mulVecLin (fun i => C i ())
      = fun i => w i * C i () := by
    intro C
    funext i
    simp [Matrix.mulVec_diagonal]
  refine sup_le (colSpace_unit_le A ?_) (colSpace_unit_le B ?_)
  · rw [Submodule.mem_comap, e]
    exact hwa
  · rw [Submodule.mem_comap, e]
    exact hwb

private lemma ce_mem_hyper {x : ZMod 5 → ℝ}
    (h : ceN 0 * x 0 + ceN 1 * x 1 + ceN 2 * x 2 + ceN 3 * x 3 + ceN 4 * x 4 = 0) :
    x ∈ hyperplane ceN := by
  rw [mem_hyperplane, dotProduct, sum_z5]
  exact h

private lemma ce_N_ne : ceN ≠ 0 := fun h => by
  have := congrFun h 0
  simp only [ceN, v5_0, Pi.zero_apply] at this
  norm_num at this

/-- The twice augmented spatial space of the counterexample is the hyperplane `ceN^⊥`, of
dimension `4 = 4 r`.
arXiv 2411.06844, counterexample to Theorem 3. -/
theorem ce_augX : augment (fun j => ceρ' j ^ 2) (ceG * ceB) ceX = hyperplane ceN := by
  have h3 := sqrt3_pos.ne'
  have h5 := sqrt5_pos.ne'
  have colX : (fun i => ceX i ()) = (1 / Real.sqrt 5) • fun _ : ZMod 5 => (1 : ℝ) := by
    funext i
    simp [ceX]
  apply le_antisymm
  · refine augment_le_of_cols ?_ ?_ ?_ ?_
    · rw [ce_colK]
      refine Submodule.smul_mem _ _ (ce_mem_hyper ?_)
      simp only [ceN, ceKt, v5_0, v5_1, v5_2, v5_3, v5_4]
      norm_num
    · rw [colX]
      refine Submodule.smul_mem _ _ (ce_mem_hyper ?_)
      simp only [ceN, v5_0, v5_1, v5_2, v5_3, v5_4]
      norm_num
    · have e : (fun i => ceρ' i ^ 2 * (ceG * ceB) i ())
          = (1 / Real.sqrt 3) • fun i => ceρ' i ^ 2 * ceKt i := by
        funext i
        have := congrFun ce_colK i
        simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
        rw [this]
        ring
      rw [e]
      refine Submodule.smul_mem _ _ (ce_mem_hyper ?_)
      simp only [ceN, ceKt, ceρ', v5_0, v5_1, v5_2, v5_3, v5_4]
      norm_num
    · have e : (fun i => ceρ' i ^ 2 * ceX i ())
          = (1 / Real.sqrt 5) • fun i => ceρ' i ^ 2 := by
        funext i
        simp only [ceX, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      refine Submodule.smul_mem _ _ (ce_mem_hyper ?_)
      simp only [ceN, ceρ', v5_0, v5_1, v5_2, v5_3, v5_4]
      norm_num
  · intro x hx
    rw [mem_hyperplane, dotProduct, sum_z5] at hx
    simp only [ceN, v5_0, v5_1, v5_2, v5_3, v5_4] at hx
    set W := augment (fun j => ceρ' j ^ 2) (ceG * ceB) ceX with hW
    have hX1 : (fun _ : ZMod 5 => (1 : ℝ)) ∈ colSpace (ceG * ceB) ⊔ colSpace ceX := by
      have e : (fun _ : ZMod 5 => (1 : ℝ)) = Real.sqrt 5 • fun i => ceX i () := by
        rw [colX, smul_smul, mul_one_div_cancel h5, one_smul]
      rw [e]
      exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (col_mem_colSpace _ _))
    have hK1 : ceKt ∈ colSpace (ceG * ceB) ⊔ colSpace ceX := by
      have e : ceKt = Real.sqrt 3 • fun i => (ceG * ceB) i () := by
        rw [ce_colK, smul_smul, mul_one_div_cancel h3, one_smul]
      rw [e]
      exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (col_mem_colSpace _ _))
    have m1 : (fun _ : ZMod 5 => (1 : ℝ)) ∈ W := sup_le_augment _ _ _ hX1
    have m2 : ceKt ∈ W := sup_le_augment _ _ _ hK1
    have m3 : (fun j => ceρ' j ^ 2 * (fun _ : ZMod 5 => (1 : ℝ)) j) ∈ W := mem_augment_diag hX1
    have m4 : (fun j => ceρ' j ^ 2 * ceKt j) ∈ W := mem_augment_diag hK1
    have e : x = ((-(2879598226 / 550707025)) * x 0 + (4414206551 / 660848430) * x 1 +
      (-(410170644 / 550707025)) * x 2 + (194364523 / 660848430) * x 3) • (fun _ : ZMod 5 => (1 :
      ℝ))
        + ((141115044 / 110141405) * x 0 + (-(30858349 / 22028281)) * x 1 + (29399736 /
          110141405) * x 2 + (-(3244607 / 22028281)) * x 3) • ceKt
        + ((8352376 / 66084843) * x 0 + (-(13068763 / 66084843)) * x 1 + (3434139 / 22028281) * x
          2 + (-(1862010 / 22028281)) * x 3) • (fun j => ceρ' j ^ 2 * (fun _ : ZMod 5 => (1 : ℝ))
          j)
        + ((-(6991760 / 198254529)) * x 0 + (967730 / 18023139) * x 1 + (-(95430 / 2002571)) * x
          2 + (5794300 / 198254529) * x 3) • (fun j => ceρ' j ^ 2 * ceKt j) := by
      funext j
      revert j
      refine forall_z5 ?_ ?_ ?_ ?_ ?_ <;>
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ceKt, ceρ', v5_0, v5_1, v5_2, v5_3,
          v5_4]
      · ring
      · ring
      · ring
      · ring
      · linear_combination (1 / 374480777 : ℝ) * hx
    rw [e]
    exact W.add_mem (W.add_mem (W.add_mem (W.smul_mem _ m1) (W.smul_mem _ m2))
      (W.smul_mem _ m3)) (W.smul_mem _ m4)

private lemma ce_quadZ_mem : ceZ ∈ augment (fun k => ceω k * Real.exp (ceV k ^ 2 / 2))
    (ceGᵀ * ceX) ceB := by
  have h3 := sqrt3_pos.ne'
  have colB : (fun _ : Fin 3 => (1 : ℝ)) = Real.sqrt 3 • fun i => ceB i () := by
    funext i
    simp only [ceB, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
  have := quadZ_mem_of_one_mem (r := Unit) (v := ceV) (ω := ceω) (ceGᵀ * ceX) ceB (by
    rw [colB]
    exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (col_mem_colSpace _ _)))
  rwa [ce_quadZ] at this

/-- The twice augmented velocity space of the counterexample is all of `ℝ³`, so that the velocity
projection plays no role at all.  (`4 r = 4` exceeds the number `3` of nodes.)
arXiv 2411.06844, counterexample to Theorem 3. -/
theorem ce_augV : augment (fun k => ceω k * Real.exp (ceV k ^ 2 / 2)) (ceGᵀ * ceX) ceB = ⊤ := by
  have h3 := sqrt3_pos.ne'
  have h5 := sqrt5_pos.ne'
  rw [eq_top_iff]
  intro x _
  set W := augment (fun k => ceω k * Real.exp (ceV k ^ 2 / 2)) (ceGᵀ * ceX) ceB with hW
  have m1 : (fun _ : Fin 3 => (1 : ℝ)) ∈ W := by
    have e : (fun _ : Fin 3 => (1 : ℝ)) = Real.sqrt 3 • fun i => ceB i () := by
      funext i
      simp only [ceB, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    rw [e]
    exact W.smul_mem _ (colSpace_le_augment_right _ _ _ (col_mem_colSpace _ _))
  have m2 : ceLt ∈ W := by
    have e : ceLt = Real.sqrt 5 • fun k => (ceGᵀ * ceX) k () := by
      rw [ce_colL, smul_smul, mul_one_div_cancel h5, one_smul]
    rw [e]
    exact W.smul_mem _ (colSpace_le_augment_left _ _ _ (col_mem_colSpace _ _))
  have m3 : ceZ ∈ W := ce_quadZ_mem
  have l0 : ceLt 0 = (1708607789 / 258677100) := rfl
  have l1 : ceLt 1 = (2283223 / 470322) := rfl
  have l2 : ceLt 2 = (601548637 / 86225700) := rfl
  have z0 : ceZ 0 = 1 / 6 := rfl
  have z1 : ceZ 1 = 2 / 3 := rfl
  have z2 : ceZ 2 = 1 / 6 := rfl
  have e : x = ((2981405497 / 144057183) * x 0 + (-(1 / 3)) * x 1 + (-(2789329253 / 144057183)) *
    x 2) • (fun _ : Fin 3 => (1 : ℝ))
      + ((-(129338550 / 48019061)) * x 0 + 0 * x 1 + (129338550 / 48019061) * x 2) • ceLt +
        ((-(548873261 / 48019061)) * x 0 + 2 * x 1 + (452835139 / 48019061) * x 2) • ceZ := by
    funext k
    revert k
    refine forall_f3 ?_ ?_ ?_ <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, l0, l1, l2, z0, z1, z2] <;> ring
  rw [e]
  exact W.add_mem (W.add_mem (W.smul_mem _ m1) (W.smul_mem _ m2)) (W.smul_mem _ m3)

private lemma ce_kappa : ∀ k, (ceN ⬝ᵥ ceN)⁻¹ * (ceN ⬝ᵥ fun j => ceG j k) = ceκ k := by
  have e0 : ceU 0 = ceU0 := rfl
  have e1 : ceU 1 = ceρ := rfl
  have e2 : ceU 2 = ceU2 := rfl
  have k0 : ceκ 0 = (669826467 / 1178320249435354810) := rfl
  have k1 : ceκ 1 = 0 := rfl
  have k2 : ceκ 2 = (-(669826467 / 1178320249435354810)) := rfl
  refine forall_f3 ?_ ?_ ?_ <;> rw [dotProduct, dotProduct, sum_z5, sum_z5] <;>
    simp only [ceN, ceG, Matrix.of_apply, e0, e1, e2, k0, k1, k2, ceρ, ceρ', ceU0, ceU2, v5_0,
      v5_1, v5_2, v5_3, v5_4] <;> norm_num

private lemma ce_ghat_eq :
    (1 + ceSigma * ceDt)⁻¹ • (hyperProj ceN * ceG * (1 : Matrix (Fin 3) (Fin 3) ℝ)) = ceGhat := by
  ext j k
  rw [Matrix.mul_one, Matrix.smul_apply, ceSigma_mul]
  have h : (hyperProj ceN * ceG) j k = (hyperProj ceN *ᵥ fun i => ceG i k) j := rfl
  rw [h, hyperProj_mulVec, ce_kappa]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ceGhat, Matrix.of_apply]
  norm_num

/-- For `ϑ = 0`, keeping everything is an admissible truncation. -/
private lemma isMassTruncation_self {K : Type*} [Fintype K] {Z : K → ℝ} (hZ : Z ≠ 0)
    (ghat : Matrix (ZMod 5) K ℝ) : IsMassTruncation Z 0 ghat ghat := by
  refine ⟨ghat - massPart Z ghat, by abel, ?_, ?_⟩
  · rw [Matrix.sub_mulVec, massPart_mulVec hZ, sub_self]
  · simp

private lemma ceZ_ne : ceZ ≠ 0 := fun h => (ceZ_pos 0).ne' (congrFun h 0)

/-- One exact step of the DLRA scheme (15), with no truncation at all.
arXiv 2411.06844, counterexample to Theorem 3. -/
theorem ce_step : IsDLRAStep ceSigma ceDt (1 / 5) 0 ceV ceω ceρ ceX ceS ceB ceρ'
    (hyperProj ceN) 1 ceGhat ceGhat := by
  have hX : ceXᵀ * ceX = 1 := by
    ext a b
    have hab : a = b := Subsingleton.elim a b
    subst hab
    have hs : 1 / Real.sqrt 5 * (1 / Real.sqrt 5) = 1 / 5 := by
      rw [one_div_mul_one_div, Real.mul_self_sqrt (by norm_num)]
    rw [Matrix.one_apply_eq, Matrix.mul_apply, sum_z5]
    simp only [Matrix.transpose_apply, ceX, Matrix.of_apply, hs]
    norm_num
  have hV : ceBᵀ * ceB = 1 := by
    ext a b
    have hab : a = b := Subsingleton.elim a b
    subst hab
    have hs : 1 / Real.sqrt 3 * (1 / Real.sqrt 3) = 1 / 3 := by
      rw [one_div_mul_one_div, Real.mul_self_sqrt (by norm_num)]
    rw [Matrix.one_apply_eq, Matrix.mul_apply, Fin.sum_univ_three]
    simp only [Matrix.transpose_apply, ceB, Matrix.of_apply, hs]
    norm_num
  refine ⟨hX, hV, ce_density, ?_, ?_, ?_, ?_⟩
  · rw [ce_rhsG, ce_augX]
    exact isOrthProjOnto_hyperProj ce_N_ne
  · rw [ce_rhsG, ce_augV]
    exact ⟨Matrix.transpose_one, fun _ => Submodule.mem_top, fun _ _ => Matrix.one_mulVec _⟩
  · rw [ce_rhsG, ce_ghat_eq]
  · rw [ce_quadZ]
    exact isMassTruncation_self ceZ_ne _

private lemma ce_normalized_g : IsNormalized ceV ceω (ceX * ceS * ceBᵀ) := by
  intro j
  rw [ce_quadZ]
  simp only [ce_g, one_mul]
  have := ce_quad
  rwa [QuadNormalized, ce_quadZ] at this

private lemma ce_normalized_ghat : IsNormalized ceV ceω ceGhat := by
  refine ce_step.normalized ?_ ceDt_pos.le (fun j => (ceρ'_pos j).ne') ce_quad ce_normalized_g ?_
  · have := sqrt3_pos
    rw [ceSigma]
    positivity
  · rw [ce_rhsG, ce_quadZ]
    exact ce_quadZ_mem

private lemma ce_old : hNormSq ceV ceω (fOf ceV ceρ (ceX * ceS * ceBᵀ)) = 307 := by
  rw [hNormSq_fOf ceV ceω ceρ (ceX * ceS * ceBᵀ), ce_quadZ]
  simp only [zE, ce_g, mul_one, sum_z5, Fin.sum_univ_three]
  have z0 : ceZ 0 = 1 / 6 := rfl
  have z1 : ceZ 1 = 2 / 3 := rfl
  have z2 : ceZ 2 = 1 / 6 := rfl
  simp only [z0, z1, z2, ceρ, v5_0, v5_1, v5_2, v5_3, v5_4]
  norm_num

private lemma ce_new : 307 < hNormSq ceV ceω (fOf ceV ceρ' ceGhat) := by
  rw [hNormSq_fOf ceV ceω ceρ' ceGhat, ce_quadZ]
  have e0 : ceU 0 = ceU0 := rfl
  have e1 : ceU 1 = ceρ := rfl
  have e2 : ceU 2 = ceU2 := rfl
  have k0 : ceκ 0 = (669826467 / 1178320249435354810) := rfl
  have k1 : ceκ 1 = 0 := rfl
  have k2 : ceκ 2 = (-(669826467 / 1178320249435354810)) := rfl
  have z0 : ceZ 0 = 1 / 6 := rfl
  have z1 : ceZ 1 = 2 / 3 := rfl
  have z2 : ceZ 2 = 1 / 6 := rfl
  simp only [zE, sum_z5, Fin.sum_univ_three, ceGhat, ceG, Matrix.of_apply, e0, e1, e2, k0, k1, k2,
    z0, z1, z2, ceN, ceρ, ceρ', ceU0, ceU2, v5_0, v5_1, v5_2, v5_3, v5_4]
  norm_num

/-- **Theorem 3 of arXiv 2411.06844 fails for weights satisfying `QuadNormalized`.**  It claims
that under `max_k |v_k| Δt ≤ Δx` the DLRA scheme (15) satisfies `‖f^{n+1}‖²_ℋ ≤ ‖f^n‖²_ℋ`.
Here is one step of (15), in exact arithmetic and without truncation (`ϑ = 0`), with
`‖f^{n+1}‖²_ℋ > ‖f^n‖²_ℋ = 307`.  It has `N_x = 5` points, `Δx = 1/5`, CFL number `0.9`, collisions
`σ > 0`, the rank-one state `g ≡ 1` that the paper itself starts from in Section 6.1, and nodes
`0, ±√3` with `ω_k e^{v_k²/2} / √(2π) = 2/3, 1/6, 1/6`, the three-point Gauss-Hermite rule of the
weight `e^{-v²/2}`, so that `QuadNormalized` and (11) hold exactly.  Difference from the printed
setting: Sec. 3.1 names the Gauss-Hermite rule of `e^{-v²}`, whose weights violate `QuadNormalized`
(`gaussHermite_one_point`, `gaussHermite_three_point_not_quadNormalized`), so that for `σ > 0`
already Lemma 2 fails for them; the counterexample with those weights is
`theorem3_false_gaussHermite`.  The weights here are the ones under which the paper's Lemma 2 and
Theorem 2 hold.  The ranks are the full ones:
`[K, X]` has rank 2, `𝒳̂̂` has dimension `4` (`ce_augX`), and the velocity projection is the
identity (`ce_augV`), so the failure is entirely that of the Euclidean spatial Galerkin projection
in the `ρ'`-weighted norm.  The relation (11) stays exact for `g'`.

The gap in the proof of the paper: it deduces from (15c), (15e) that
`Σ_α P^X_{αj} g_{αβ} (ρ_α)² = g_{jβ} (ρ_j)²`.  But `g^{n+1}` lies in `𝒳̂̂ ⊗ 𝒱̂̂`, while (15c) adds
`ρ² X̂` and not `ρ² X̂̂`, which would contain `ρ⁴ X̂`.  See `ce_displayed_equality_fails`, and
`dlra_stable_of_invariant` for a corrected statement.  The growth factor is about `1.0096`, which a
floating point run of (15a)-(15f) with QR factorisations reproduces. -/
theorem theorem3_false :
    ∃ (σ dt dx : ℝ) (v ω : Fin 3 → ℝ) (ρ ρ' : ZMod 5 → ℝ) (X : Matrix (ZMod 5) Unit ℝ)
      (S : Matrix Unit Unit ℝ) (V : Matrix (Fin 3) Unit ℝ) (PX : Matrix (ZMod 5) (ZMod 5) ℝ)
      (PV : Matrix (Fin 3) (Fin 3) ℝ) (ghat g' : Matrix (ZMod 5) (Fin 3) ℝ),
      0 < σ ∧ 0 < dt ∧ dx = 1 / 5 ∧ (∀ k, 0 < ω k) ∧ QuadNormalized v ω ∧
      (∀ k, |v k| * dt < dx) ∧ (∀ j, 0 < ρ j) ∧ (∀ j, 0 < ρ' j) ∧
      (∀ j k, (X * S * Vᵀ) j k = 1) ∧ IsNormalized v ω (X * S * Vᵀ) ∧
      IsDLRAStep σ dt dx 0 v ω ρ X S V ρ' PX PV ghat g' ∧ IsNormalized v ω g' ∧
      hNormSq v ω (fOf v ρ (X * S * Vᵀ)) < hNormSq v ω (fOf v ρ' g') := by
  refine ⟨ceSigma, ceDt, 1 / 5, ceV, ceω, ceρ, ceρ', ceX, ceS, ceB, hyperProj ceN, 1, ceGhat,
    ceGhat, ?_, ceDt_pos, rfl, ceω_pos, ce_quad, ce_cfl, ceρ_pos, ceρ'_pos, ce_g, ce_normalized_g,
    ce_step, ce_normalized_ghat, ?_⟩
  · have := sqrt3_pos
    rw [ceSigma]
    positivity
  · rw [ce_old]
    exact ce_new

/-- The first equality displayed in the proof of Theorem 3 of arXiv 2411.06844 fails in the
counterexample: `P^X (ρ'² g^{n+1}) ≠ ρ'² g^{n+1}`, although (15c) was applied. -/
theorem ce_displayed_equality_fails :
    hyperProj ceN * (Matrix.diagonal (fun j => ceρ' j ^ 2) * ceGhat)
      ≠ Matrix.diagonal (fun j => ceρ' j ^ 2) * ceGhat := by
  intro hX
  have hσ : 0 ≤ ceSigma := by
    have := sqrt3_pos
    rw [ceSigma]
    positivity
  have h := dlra_stable_of_equalities ce_step hσ ceDt_pos.le (by norm_num)
    (fun k => (ceω_pos k).le) ce_quad (fun k => (ce_cfl k).le) (fun j => (ceρ'_pos j).ne')
    ce_normalized_ghat hX (Matrix.mul_one _)
  have h1 := ce_new
  rw [ce_old] at h
  linarith

end Counterexample

/-! ### Theorem 3 with the printed Gauss-Hermite weights -/

section CounterexamplePrinted

/-- The nodes `∓√6/2 = ∓√(3/2)` and `0` of the three-point Gauss-Hermite rule for the weight
`e^{-v²}` named in Section 3.1 of arXiv 2411.06844: the roots of `H₃(v) = 8v³ - 12v`. -/
noncomputable def ghV : Fin 3 → ℝ := ![-(Real.sqrt 6 / 2), 0, Real.sqrt 6 / 2]

/-- The weights `√π/6, 2√π/3, √π/6` of that rule, see `gaussHermite_three_point`. -/
noncomputable def ghω : Fin 3 → ℝ :=
  ![Real.sqrt Real.pi / 6, 2 * Real.sqrt Real.pi / 3, Real.sqrt Real.pi / 6]

private lemma ghV_0 : ghV 0 = -(Real.sqrt 6 / 2) := rfl
private lemma ghV_1 : ghV 1 = 0 := rfl
private lemma ghV_2 : ghV 2 = Real.sqrt 6 / 2 := rfl
private lemma ghω_0 : ghω 0 = Real.sqrt Real.pi / 6 := rfl
private lemma ghω_1 : ghω 1 = 2 * Real.sqrt Real.pi / 3 := rfl
private lemma ghω_2 : ghω 2 = Real.sqrt Real.pi / 6 := rfl

private lemma sqrt6_sq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)

private lemma sqrt6_pos : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)

private lemma ghV0_sq : ghV 0 ^ 2 = 3 / 2 := by
  rw [ghV_0, neg_sq, div_pow, sqrt6_sq]
  norm_num

private lemma ghV2_sq : ghV 2 ^ 2 = 3 / 2 := by
  rw [ghV_2, div_pow, sqrt6_sq]
  norm_num

/-- `ghV`, `ghω` is the three-point Gauss-Hermite rule for `e^{-v²}`: the nodes are the roots of
`H₃(v) = 8v³ - 12v`, the weights sum to `∫ e^{-v²} dv = √π`, and the rule reproduces the moments
`∫ v^m e^{-v²} dv` for `m ≤ 5`: `√π/2` for `m = 2`, `3√π/4` for `m = 4`, `0` for odd `m`.
arXiv 2411.06844, Section 3.1. -/
theorem gaussHermite_three_point :
    (∀ k, 8 * ghV k ^ 3 - 12 * ghV k = 0) ∧ ∑ k, ghω k = ∫ v : ℝ, Real.exp (-v ^ 2) ∧
      ∑ k, ghω k * ghV k ^ 2 = Real.sqrt Real.pi / 2 ∧
      ∑ k, ghω k * ghV k ^ 4 = 3 * Real.sqrt Real.pi / 4 ∧
      ∀ m, Odd m → ∑ k, ghω k * ghV k ^ m = 0 := by
  have hs := sqrt6_sq
  have h4 : ∀ k, ghV k ^ 4 = (ghV k ^ 2) ^ 2 := fun k => by ring
  refine ⟨forall_f3 ?_ ?_ ?_, ?_, ?_, ?_, fun m hm => ?_⟩
  · rw [ghV_0]
    linear_combination (-Real.sqrt 6) * hs
  · rw [ghV_1]
    ring
  · rw [ghV_2]
    linear_combination Real.sqrt 6 * hs
  · have h := integral_gaussian 1
    simp only [neg_mul, one_mul, div_one] at h
    rw [h, Fin.sum_univ_three, ghω_0, ghω_1, ghω_2]
    ring
  · rw [Fin.sum_univ_three, ghω_0, ghω_1, ghω_2, ghV0_sq, ghV_1, ghV2_sq]
    ring
  · rw [Fin.sum_univ_three, h4, h4, h4, ghω_0, ghω_1, ghω_2, ghV0_sq, ghV_1, ghV2_sq]
    ring
  · rw [Fin.sum_univ_three, ghV_0, ghV_1, ghV_2, hm.neg_pow, zero_pow hm.pos.ne', ghω_0, ghω_2]
    ring

private lemma ghω_pos : ∀ k, 0 < ghω k := by
  refine forall_f3 ?_ ?_ ?_
  · rw [ghω_0]
    positivity
  · rw [ghω_1]
    positivity
  · rw [ghω_2]
    positivity

private lemma gh_quadZ_pos (k : Fin 3) : 0 < quadZ ghV ghω k :=
  mul_pos (mul_pos (by positivity) (ghω_pos k)) (Real.exp_pos _)

private lemma gh_quadZ_symm : quadZ ghV ghω 2 = quadZ ghV ghω 0 := by
  simp only [quadZ, ghV0_sq, ghV2_sq, ghω_0, ghω_2]

/-- `Z_± = e^{3/4} Z_0 / 4` for the printed rule. -/
private lemma gh_quadZ_ratio : 4 * quadZ ghV ghω 0 = Real.exp (3 / 4) * quadZ ghV ghω 1 := by
  simp only [quadZ, ghV0_sq, ghV_1, ghω_0, ghω_1]
  have e1 : (3 : ℝ) / 2 / 2 = 3 / 4 := by norm_num
  have e2 : (0 : ℝ) ^ 2 / 2 = 0 := by norm_num
  rw [e1, e2, Real.exp_zero]
  ring

private lemma two_lt_exp : 2 < Real.exp (3 / 4) := by
  have h := Real.quadratic_le_exp_of_nonneg (x := 3 / 4) (by norm_num)
  norm_num at h
  linarith

private lemma exp_lt_four : Real.exp (3 / 4) < 4 := by
  have h1 : Real.exp (3 / 4) < Real.exp 1 := Real.exp_lt_exp.2 (by norm_num)
  have h2 := Real.exp_one_lt_d9
  have h3 : (2.7182818286 : ℝ) < 4 := by norm_num
  linarith

/-- The printed weights violate `QuadNormalized`: `Σ_k Z_k = (2 + e^{3/4}) / (3√2) ≈ 0.970`.  So
`theorem3_false` does not cover them, and the proof of Lemma 2 does not apply to them for `σ > 0`.
arXiv 2411.06844, Section 3.1 and Lemma 2. -/
theorem gaussHermite_three_point_not_quadNormalized : ¬ QuadNormalized ghV ghω := by
  intro h
  have hr := gh_quadZ_ratio
  have h2 : (11 / 8 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have he : Real.exp (3 / 4) ≤ 17 / 8 := by
    have h := Real.exp_bound' (x := 3 / 4) (by norm_num) (by norm_num) (n := 3) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hz1 : quadZ ghV ghω 1 * Real.sqrt 2 = 2 / 3 := by
    simp only [quadZ, ghV_1, ghω_1]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hp : 0 < Real.sqrt Real.pi := by positivity
    have hq : 0 < Real.sqrt 2 := by positivity
    have e2 : (0 : ℝ) ^ 2 / 2 = 0 := by norm_num
    rw [e2, Real.exp_zero]
    field_simp
  rw [QuadNormalized, Fin.sum_univ_three, gh_quadZ_symm] at h
  have h1 : (Real.exp (3 / 4) / 2 + 1) * quadZ ghV ghω 1 = 1 := by linarith
  have key : (Real.exp (3 / 4) / 2 + 1) * (2 / 3) = Real.sqrt 2 := by
    calc (Real.exp (3 / 4) / 2 + 1) * (2 / 3)
        = (Real.exp (3 / 4) / 2 + 1) * (quadZ ghV ghω 1 * Real.sqrt 2) := by rw [hz1]
      _ = Real.sqrt 2 := by rw [← mul_assoc, h1, one_mul]
  linarith

/-- `Δt = 0.9 Δx / max_k |v_k|` for the printed nodes and `Δx = 1/5`. -/
noncomputable def ghDt : ℝ := 3 * Real.sqrt 6 / 50

/-- The velocity profile `h_k = c_k / Z_k` with `c = (1/6, 2/3, 1/6)`, so that `g = 𝟙 hᵀ` satisfies
(11) for the printed weights. -/
noncomputable def ghH (k : Fin 3) : ℝ := ceZ k / quadZ ghV ghω k

/-- `‖h‖`. -/
noncomputable def ghHn : ℝ := Real.sqrt (∑ k, ghH k ^ 2)

/-- The velocity basis `V = h / ‖h‖` of rank one. -/
noncomputable def ghB : Matrix (Fin 3) Unit ℝ := Matrix.of fun k _ => ghH k / ghHn

/-- The coefficient `S = √5 ‖h‖`, so that `X S Vᵀ = 𝟙 hᵀ` with `X = 𝟙/√5`. -/
noncomputable def ghS : Matrix Unit Unit ℝ := Matrix.of fun _ _ => Real.sqrt 5 * ghHn

/-- The operator `G` of (14a) for this state and `σ = 0`. -/
noncomputable def ghG : Matrix (ZMod 5) (Fin 3) ℝ :=
  Matrix.of fun j k => ghH k * (ceU k j / ceρ' j)

/-- The result `ĝ` of the S-step. -/
noncomputable def ghGhat : Matrix (ZMod 5) (Fin 3) ℝ :=
  Matrix.of fun j k => ghH k * (ceU k j / ceρ' j - ceκ k * ceN j)

private lemma ghH_pos (k : Fin 3) : 0 < ghH k := div_pos (ceZ_pos k) (gh_quadZ_pos k)

private lemma gh_c (k : Fin 3) : quadZ ghV ghω k * ghH k = ceZ k := by
  have := (gh_quadZ_pos k).ne'
  simp only [ghH]
  field_simp

private lemma ghH_symm : ghH 2 = ghH 0 := by
  simp only [ghH, gh_quadZ_symm]
  rfl

private lemma ghH_lt : 2 * ghH 0 < ghH 1 ∧ ghH 1 < 4 * ghH 0 := by
  have h0 := gh_quadZ_pos 0
  have h1 := gh_quadZ_pos 1
  have hr := gh_quadZ_ratio
  have z0 : ceZ 0 = 1 / 6 := rfl
  have z1 : ceZ 1 = 2 / 3 := rfl
  have a := mul_lt_mul_of_pos_right two_lt_exp h1
  have b := mul_lt_mul_of_pos_right exp_lt_four h1
  simp only [ghH, z0, z1]
  constructor
  · rw [show 2 * (1 / 6 / quadZ ghV ghω 0) = 1 / 3 / quadZ ghV ghω 0 by ring,
      div_lt_div_iff₀ h0 h1]
    linarith
  · rw [show 4 * (1 / 6 / quadZ ghV ghω 0) = 2 / 3 / quadZ ghV ghω 0 by ring,
      div_lt_div_iff₀ h1 h0]
    linarith

private lemma ghHn_sq : ghHn ^ 2 = ∑ k, ghH k ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private lemma ghHn_pos : 0 < ghHn := by
  refine Real.sqrt_pos.2 ?_
  rw [Fin.sum_univ_three]
  have := ghH_pos 0
  nlinarith [sq_nonneg (ghH 1), sq_nonneg (ghH 2)]

private lemma ghDt_mul : ghDt * (Real.sqrt 6 / 2) = 9 / 10 * (1 / 5) := by
  rw [ghDt]
  linear_combination (3 / 100 : ℝ) * sqrt6_sq

private lemma ghDt_pos : 0 < ghDt := by
  have := sqrt6_pos
  rw [ghDt]
  positivity

private lemma gh_cfl : ∀ k, |ghV k| * ghDt < 1 / 5 := by
  have h6 := sqrt6_pos
  refine forall_f3 ?_ ?_ ?_
  · rw [ghV_0, abs_neg, abs_of_pos (by positivity), mul_comm, ghDt_mul]
    norm_num
  · rw [ghV_1]
    simp
  · rw [ghV_2, abs_of_pos (by positivity), mul_comm, ghDt_mul]
    norm_num

/-- `g = X S Vᵀ = 𝟙 hᵀ`.
arXiv 2411.06844, counterexample to Theorem 3 with the printed weights. -/
theorem gh_g (j : ZMod 5) (k : Fin 3) : (ceX * ghS * ghBᵀ) j k = ghH k := by
  have h5 := sqrt5_pos.ne'
  have hn := ghHn_pos.ne'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, ceX, ghS, ghB, Matrix.of_apply,
    Finset.univ_unique, Finset.sum_singleton]
  field_simp

private lemma gh_U : ∀ (k : Fin 3) (j : ZMod 5),
    ceρ j - ghDt * upw (1 / 5) (ghV k) ceρ j = ceU k j := by
  have h5 : (1 / 5 : ℝ) ≠ 0 := by norm_num
  have h6 := sqrt6_pos
  refine forall_f3 ?_ ?_ ?_
  · intro j
    have h := upw_step_left (dx := 1 / 5) (dt := ghDt) (a := -(Real.sqrt 6 / 2)) (l := 9 / 10) h5
      (by linarith) (by rw [neg_neg]; exact ghDt_mul) ceρ j
    have e2 : ceU 0 = ceU0 := rfl
    rw [ghV_0, h, e2]
    clear h
    revert j
    refine forall_z5 ?_ ?_ ?_ ?_ ?_ <;>
      simp only [ceρ, ceU0, s0, s1, s2, s3, s4, v5_0, v5_1, v5_2, v5_3, v5_4] <;> norm_num
  · intro j
    have e2 : ceU 1 = ceρ := rfl
    rw [ghV_1, e2]
    simp [upw]
  · intro j
    have h := upw_step_right (dx := 1 / 5) (dt := ghDt) (a := Real.sqrt 6 / 2) (l := 9 / 10) h5
      (by positivity) ghDt_mul ceρ j
    have e2 : ceU 2 = ceU2 := rfl
    rw [ghV_2, h, e2]
    clear h
    revert j
    refine forall_z5 ?_ ?_ ?_ ?_ ?_ <;>
      simp only [ceρ, ceU2, p0, p1, p2, p3, p4, v5_0, v5_1, v5_2, v5_3, v5_4] <;> norm_num

private lemma gh_u (k : Fin 3) :
    (fun i => ceρ i * (ceX * ghS * ghBᵀ) i k) = fun i => ghH k * ceρ i := by
  funext i
  rw [gh_g, mul_comm]

private lemma gh_density (j : ZMod 5) :
    ceρ' j = densityNext ghDt (1 / 5) ghV ghω ceρ (ceX * ghS * ghBᵀ) j := by
  rw [densityNext_eq ghDt (1 / 5) ghV ghω ceρ (ceX * ghS * ghBᵀ) j]
  simp only [gh_u, upw_const_mul, Fin.sum_univ_three]
  have c0 := gh_c 0
  have c1 := gh_c 1
  have c2 := gh_c 2
  have z0 : ceZ 0 = 1 / 6 := rfl
  have z1 : ceZ 1 = 2 / 3 := rfl
  have z2 : ceZ 2 = 1 / 6 := rfl
  rw [z0] at c0
  rw [z1] at c1
  rw [z2] at c2
  linear_combination ce_mean j - 1 / 6 * gh_U 0 j - 2 / 3 * gh_U 1 j - 1 / 6 * gh_U 2 j
    + (ghDt * upw (1 / 5) (ghV 0) ceρ j) * c0 + (ghDt * upw (1 / 5) (ghV 1) ceρ j) * c1
    + (ghDt * upw (1 / 5) (ghV 2) ceρ j) * c2

private lemma gh_rhsG : rhsG 0 ghDt (1 / 5) ghV ceρ ceρ' (ceX * ghS * ghBᵀ) = ghG := by
  ext j k
  rw [rhsG_apply _ _ _ _ _ fun j => (ceρ'_pos j).ne', gh_u, gh_g, upw_const_mul]
  simp only [ghG, Matrix.of_apply]
  rw [← gh_U k j]
  ring

private lemma gh_colK : (fun j => (ghG * ghB) j ()) = fun j =>
    ghHn⁻¹ * (6 * ghH 0 ^ 2 + (ghH 1 ^ 2 - 4 * ghH 0 ^ 2) * (ceρ j / ceρ' j)) := by
  funext j
  have hm := ce_mean j
  have e1 : ceU 1 = ceρ := rfl
  rw [e1] at hm
  have hU2 : ceU 2 j = 6 * ceρ' j - 4 * ceρ j - ceU 0 j := by linarith
  have hρ' := (ceρ'_pos j).ne'
  have hn := ghHn_pos.ne'
  simp only [Matrix.mul_apply, ghG, ghB, Matrix.of_apply, Fin.sum_univ_three, ghH_symm, e1, hU2]
  field_simp
  ring

private lemma gh_Kt : ∀ j, ceKt j = 63 / 10 - 3 * (ceρ j / ceρ' j) := by
  refine forall_z5 ?_ ?_ ?_ ?_ ?_ <;>
    simp only [ceKt, ceρ, ceρ', v5_0, v5_1, v5_2, v5_3, v5_4] <;> norm_num

private lemma gh_sup :
    colSpace (ghG * ghB) ⊔ colSpace ceX = colSpace (ceG * ceB) ⊔ colSpace ceX := by
  have h3 := sqrt3_pos.ne'
  have h5 := sqrt5_pos.ne'
  have hn := ghHn_pos.ne'
  have hb : ghH 1 ^ 2 - 4 * ghH 0 ^ 2 ≠ 0 := by
    have h1 := ghH_lt.1
    have := ghH_pos 0
    nlinarith
  have one_eq : (fun _ : ZMod 5 => (1 : ℝ)) = Real.sqrt 5 • fun i => ceX i () := by
    funext i
    simp only [ceX, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
  have kt_eq : ceKt = Real.sqrt 3 • fun j => (ceG * ceB) j () := by
    rw [ce_colK, smul_smul, mul_one_div_cancel h3, one_smul]
  apply le_antisymm
  · refine sup_le (colSpace_unit_le _ ?_) le_sup_right
    have e : (fun j => (ghG * ghB) j ()) =
        (ghHn⁻¹ * (6 * ghH 0 ^ 2 + 21 / 10 * (ghH 1 ^ 2 - 4 * ghH 0 ^ 2))) •
          (fun _ : ZMod 5 => (1 : ℝ)) + (-(ghHn⁻¹ * (ghH 1 ^ 2 - 4 * ghH 0 ^ 2) / 3)) • ceKt := by
      rw [gh_colK]
      funext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, gh_Kt j]
      ring
    rw [e, one_eq, kt_eq]
    exact add_mem
      (Submodule.smul_mem _ _ (Submodule.mem_sup_right
        (Submodule.smul_mem _ _ (col_mem_colSpace _ _))))
      (Submodule.smul_mem _ _ (Submodule.mem_sup_left
        (Submodule.smul_mem _ _ (col_mem_colSpace _ _))))
  · refine sup_le (colSpace_unit_le _ ?_) le_sup_right
    have e : (fun j => (ceG * ceB) j ()) =
        (1 / Real.sqrt 3 * (63 / 10 + 18 * ghH 0 ^ 2 / (ghH 1 ^ 2 - 4 * ghH 0 ^ 2))) •
          (fun _ : ZMod 5 => (1 : ℝ)) +
        (-(1 / Real.sqrt 3 * (3 * ghHn / (ghH 1 ^ 2 - 4 * ghH 0 ^ 2)))) •
          fun j => (ghG * ghB) j () := by
      rw [ce_colK, gh_colK]
      funext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, gh_Kt j]
      generalize ghH 1 ^ 2 - 4 * ghH 0 ^ 2 = B at hb ⊢
      field_simp
      ring
    rw [e, one_eq]
    exact add_mem
      (Submodule.smul_mem _ _ (Submodule.mem_sup_right
        (Submodule.smul_mem _ _ (col_mem_colSpace _ _))))
      (Submodule.smul_mem _ _ (Submodule.mem_sup_left (col_mem_colSpace _ _)))

/-- The twice augmented spatial space is the same hyperplane `ceN^⊥` as in `theorem3_false`, of
dimension `4 = 4 r`; `[K, X]` has rank `2 = 2 r`.
arXiv 2411.06844, counterexample to Theorem 3 with the printed weights. -/
theorem gh_augX : augment (fun j => ceρ' j ^ 2) (ghG * ghB) ceX = hyperplane ceN := by
  rw [← ce_augX]
  unfold augment
  rw [gh_sup]

private lemma gh_Ssum : ∀ k, ∑ j, ceU k j / ceρ' j = ceLt k - 1 / 2 := by
  have e0 : ceU 0 = ceU0 := rfl
  have e1 : ceU 1 = ceρ := rfl
  have e2 : ceU 2 = ceU2 := rfl
  have l0 : ceLt 0 = (1708607789 / 258677100) := rfl
  have l1 : ceLt 1 = (2283223 / 470322) := rfl
  have l2 : ceLt 2 = (601548637 / 86225700) := rfl
  refine forall_f3 ?_ ?_ ?_ <;> rw [sum_z5] <;>
    simp only [e0, e1, e2, l0, l1, l2, ceρ, ceρ', ceU0, ceU2, v5_0, v5_1, v5_2, v5_3, v5_4] <;>
    norm_num

private lemma gh_w (k : Fin 3) :
    ghω k * Real.exp (ghV k ^ 2 / 2) = Real.sqrt (2 * Real.pi) * quadZ ghV ghω k := by
  have := sqrt_two_pi_ne
  simp only [quadZ]
  field_simp

/-- The twice augmented velocity space is all of `ℝ³` (`4 r = 4` exceeds the `3` nodes).
arXiv 2411.06844, counterexample to Theorem 3 with the printed weights. -/
theorem gh_augV :
    augment (fun k => ghω k * Real.exp (ghV k ^ 2 / 2)) (ghGᵀ * ceX) ghB = ⊤ := by
  have h5 := sqrt5_pos.ne'
  have hs := sqrt_two_pi_ne
  have hn := ghHn_pos.ne'
  have hm : 4 * ghH 0 - ghH 1 ≠ 0 := by
    have := ghH_lt.2
    linarith
  have hH2 := ghH_symm
  rw [eq_top_iff]
  intro x _
  set W := augment (fun k => ghω k * Real.exp (ghV k ^ 2 / 2)) (ghGᵀ * ceX) ghB with hW
  have mB : (fun k => ghB k ()) ∈ colSpace (ghGᵀ * ceX) ⊔ colSpace ghB :=
    Submodule.mem_sup_right (col_mem_colSpace _ _)
  have mL : (fun k => (ghGᵀ * ceX) k ()) ∈ colSpace (ghGᵀ * ceX) ⊔ colSpace ghB :=
    Submodule.mem_sup_left (col_mem_colSpace _ _)
  have mh : ghH ∈ W := by
    have e : ghH = ghHn • fun k => ghB k () := by
      funext k
      simp only [ghB, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    rw [e]
    exact W.smul_mem _ (sup_le_augment _ _ _ mB)
  have mc : ceZ ∈ W := by
    have e : ceZ = (ghHn / Real.sqrt (2 * Real.pi)) •
        fun k => (ghω k * Real.exp (ghV k ^ 2 / 2)) * ghB k () := by
      funext k
      simp only [Pi.smul_apply, smul_eq_mul, gh_w, ghB, Matrix.of_apply]
      rw [← gh_c k]
      field_simp
    rw [e]
    exact W.smul_mem _ (mem_augment_diag mB)
  have colL : ∀ k, (ghGᵀ * ceX) k () = ghH k * (ceLt k - 1 / 2) / Real.sqrt 5 := by
    intro k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, ghG, ceX, Matrix.of_apply]
    rw [← gh_Ssum k, Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  have mq : (fun k => ceZ k * (ceLt k - 1 / 2)) ∈ W := by
    have e : (fun k => ceZ k * (ceLt k - 1 / 2)) = (Real.sqrt 5 / Real.sqrt (2 * Real.pi)) •
        fun k => (ghω k * Real.exp (ghV k ^ 2 / 2)) * (ghGᵀ * ceX) k () := by
      funext k
      simp only [Pi.smul_apply, smul_eq_mul, gh_w, colL]
      rw [← gh_c k]
      field_simp
    rw [e]
    exact W.smul_mem _ (mem_augment_diag mL)
  have z0 : ceZ 0 = 1 / 6 := rfl
  have z1 : ceZ 1 = 2 / 3 := rfl
  have z2 : ceZ 2 = 1 / 6 := rfl
  have l0 : ceLt 0 = (1708607789 / 258677100) := rfl
  have l1 : ceLt 1 = (2283223 / 470322) := rfl
  have l2 : ceLt 2 = (601548637 / 86225700) := rfl
  have hdq : ceZ 0 * (ceLt 0 - 1 / 2) - ceZ 2 * (ceLt 2 - 1 / 2) ≠ 0 := by
    rw [z0, z2, l0, l2]
    norm_num
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ * (ceZ 0 * (ceLt 0 - 1 / 2) - ceZ 2 * (ceLt 2 - 1 / 2))
      = x 0 - x 2 :=
    ⟨(x 0 - x 2) / (ceZ 0 * (ceLt 0 - 1 / 2) - ceZ 2 * (ceLt 2 - 1 / 2)), div_mul_cancel₀ _ hdq⟩
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α * (4 * ghH 0 - ghH 1)
      = 4 * (x 0 - γ * (ceZ 0 * (ceLt 0 - 1 / 2))) - (x 1 - γ * (ceZ 1 * (ceLt 1 - 1 / 2))) :=
    ⟨(4 * (x 0 - γ * (ceZ 0 * (ceLt 0 - 1 / 2))) - (x 1 - γ * (ceZ 1 * (ceLt 1 - 1 / 2))))
      / (4 * ghH 0 - ghH 1), div_mul_cancel₀ _ hm⟩
  have e : x = α • ghH + (6 * (x 0 - γ * (ceZ 0 * (ceLt 0 - 1 / 2)) - α * ghH 0)) • ceZ
      + γ • fun k => ceZ k * (ceLt k - 1 / 2) := by
    simp only [z0, z1, z2, l0, l1, l2] at hγ hα
    funext k
    revert k
    refine forall_f3 ?_ ?_ ?_ <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, z0, z1, z2, l0, l1, l2, hH2]
    · ring
    · linear_combination hα
    · linear_combination hγ
  rw [e]
  exact W.add_mem (W.add_mem (W.smul_mem _ mh) (W.smul_mem _ mc)) (W.smul_mem _ mq)

private lemma gh_kappa :
    ∀ k, (ceN ⬝ᵥ ceN)⁻¹ * (ceN ⬝ᵥ fun j => ghG j k) = ghH k * ceκ k := by
  intro k
  have hsum : (ceN ⬝ᵥ fun _ : ZMod 5 => (1 : ℝ)) = 0 := by
    rw [dotProduct, sum_z5]
    simp only [ceN, v5_0, v5_1, v5_2, v5_3, v5_4]
    norm_num
  have e : (fun j => ghG j k) =
      ghH k • ((fun j => ceG j k) - (1 / 10 : ℝ) • fun _ : ZMod 5 => (1 : ℝ)) := by
    funext j
    simp only [ghG, ceG, Matrix.of_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [e, dotProduct_smul, dotProduct_sub, dotProduct_smul, hsum, ← ce_kappa k]
  simp only [smul_eq_mul]
  ring

private lemma gh_ghat_eq :
    (1 + 0 * ghDt)⁻¹ • (hyperProj ceN * ghG * (1 : Matrix (Fin 3) (Fin 3) ℝ)) = ghGhat := by
  ext j k
  rw [Matrix.mul_one, zero_mul, add_zero, inv_one, one_smul]
  have h : (hyperProj ceN * ghG) j k = (hyperProj ceN *ᵥ fun i => ghG i k) j := rfl
  rw [h, hyperProj_mulVec, gh_kappa]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ghGhat, ghG, Matrix.of_apply]
  ring

/-- One exact step of the DLRA scheme (15) with the printed quadrature, `σ = 0` and no truncation.
arXiv 2411.06844, counterexample to Theorem 3 with the printed weights. -/
theorem gh_step : IsDLRAStep 0 ghDt (1 / 5) 0 ghV ghω ceρ ceX ghS ghB ceρ' (hyperProj ceN) 1
    ghGhat ghGhat := by
  have hX : ceXᵀ * ceX = 1 := by
    ext a b
    have hab : a = b := Subsingleton.elim a b
    subst hab
    have hs : 1 / Real.sqrt 5 * (1 / Real.sqrt 5) = 1 / 5 := by
      rw [one_div_mul_one_div, Real.mul_self_sqrt (by norm_num)]
    rw [Matrix.one_apply_eq, Matrix.mul_apply, sum_z5]
    simp only [Matrix.transpose_apply, ceX, Matrix.of_apply, hs]
    norm_num
  have hV : ghBᵀ * ghB = 1 := by
    ext a b
    have hab : a = b := Subsingleton.elim a b
    subst hab
    have hn := ghHn_pos.ne'
    rw [Matrix.one_apply_eq, Matrix.mul_apply]
    simp only [Matrix.transpose_apply, ghB, Matrix.of_apply]
    calc ∑ k, ghH k / ghHn * (ghH k / ghHn) = (∑ k, ghH k ^ 2) / ghHn ^ 2 := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = 1 := by rw [← ghHn_sq, div_self (pow_ne_zero 2 hn)]
  refine ⟨hX, hV, gh_density, ?_, ?_, ?_, ?_⟩
  · rw [gh_rhsG, gh_augX]
    exact isOrthProjOnto_hyperProj ce_N_ne
  · rw [gh_rhsG, gh_augV]
    exact ⟨Matrix.transpose_one, fun _ => Submodule.mem_top, fun _ _ => Matrix.one_mulVec _⟩
  · rw [gh_rhsG, gh_ghat_eq]
  · exact isMassTruncation_self (fun h => (gh_quadZ_pos 0).ne' (congrFun h 0)) _

private lemma gh_normalized_g : IsNormalized ghV ghω (ceX * ghS * ghBᵀ) := by
  intro j
  have z0 : ceZ 0 = 1 / 6 := rfl
  have z1 : ceZ 1 = 2 / 3 := rfl
  have z2 : ceZ 2 = 1 / 6 := rfl
  simp only [gh_g, Fin.sum_univ_three]
  rw [mul_comm (ghH 0), gh_c, mul_comm (ghH 1), gh_c, mul_comm (ghH 2), gh_c, z0, z1, z2]
  norm_num

private lemma gh_normalized_ghat : IsNormalized ghV ghω ghGhat := by
  intro j
  have hρ' := (ceρ'_pos j).ne'
  have hm := ce_mean j
  have hc : ∀ k (a : ℝ), ghH k * a * quadZ ghV ghω k = ceZ k * a := fun k a => by
    rw [← gh_c k]
    ring
  have z0 : ceZ 0 = 1 / 6 := rfl
  have z1 : ceZ 1 = 2 / 3 := rfl
  have z2 : ceZ 2 = 1 / 6 := rfl
  have k1 : ceκ 1 = 0 := rfl
  have k2 : ceκ 2 = -ceκ 0 := by
    simp only [ceκ]
    norm_num
  simp only [ghGhat, Matrix.of_apply, Fin.sum_univ_three, hc, z0, z1, z2, k1, k2]
  calc 1 / 6 * (ceU 0 j / ceρ' j - ceκ 0 * ceN j) + 2 / 3 * (ceU 1 j / ceρ' j - 0 * ceN j)
        + 1 / 6 * (ceU 2 j / ceρ' j - -ceκ 0 * ceN j)
      = (1 / 6 * ceU 0 j + 2 / 3 * ceU 1 j + 1 / 6 * ceU 2 j) / ceρ' j := by ring
    _ = 1 := by rw [← hm, div_self hρ']

/-- `‖f‖²_ℋ` of a state `ρ_j h_k a_{jk}`: `Σ_k c_k h_k Σ_j (ρ_j a_{jk})²`. -/
private lemma gh_zE (ρ'' : ZMod 5 → ℝ) (a : ZMod 5 → Fin 3 → ℝ) :
    zE (quadZ ghV ghω) (fun j k => ρ'' j * (ghH k * a j k))
      = ∑ k, ceZ k * ghH k * ∑ j, (ρ'' j * a j k) ^ 2 := by
  simp only [zE]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, ← gh_c k]
  exact Finset.sum_congr rfl fun j _ => by ring

private lemma gh_grow : hNormSq ghV ghω (fOf ghV ceρ (ceX * ghS * ghBᵀ))
    < hNormSq ghV ghω (fOf ghV ceρ' ghGhat) := by
  rw [hNormSq_fOf ghV ghω ceρ (ceX * ghS * ghBᵀ), hNormSq_fOf ghV ghω ceρ' ghGhat]
  have eo : (fun j k => ceρ j * (ceX * ghS * ghBᵀ) j k)
      = fun j k => ceρ j * (ghH k * (fun _ _ => (1 : ℝ)) j k) := by
    funext j k
    rw [gh_g, mul_one]
  have en : (fun j k => ceρ' j * ghGhat j k)
      = fun j k => ceρ' j * (ghH k * (fun j k => ceU k j / ceρ' j - ceκ k * ceN j) j k) := rfl
  rw [eo, en, gh_zE, gh_zE, Fin.sum_univ_three, Fin.sum_univ_three, ghH_symm]
  have z0 : ceZ 0 = 1 / 6 := rfl
  have z1 : ceZ 1 = 2 / 3 := rfl
  have z2 : ceZ 2 = 1 / 6 := rfl
  have e0 : ceU 0 = ceU0 := rfl
  have e1 : ceU 1 = ceρ := rfl
  have e2 : ceU 2 = ceU2 := rfl
  have k0 : ceκ 0 = (669826467 / 1178320249435354810) := rfl
  have k1 : ceκ 1 = 0 := rfl
  have k2 : ceκ 2 = (-(669826467 / 1178320249435354810)) := rfl
  have r : ∀ k : Fin 3, ∑ j, (ceρ j * (fun _ _ => (1 : ℝ)) j k) ^ 2 = 307 := by
    intro k
    rw [sum_z5]
    simp only [ceρ, v5_0, v5_1, v5_2, v5_3, v5_4]
    norm_num
  have t1 : ∑ j, (ceρ' j * (ceU 1 j / ceρ' j - ceκ 1 * ceN j)) ^ 2 = 307 := by
    rw [sum_z5]
    simp only [e1, k1, ceρ, ceρ', v5_0, v5_1, v5_2, v5_3, v5_4]
    norm_num
  have t02 : 614 < ∑ j, (ceρ' j * (ceU 0 j / ceρ' j - ceκ 0 * ceN j)) ^ 2
      + ∑ j, (ceρ' j * (ceU 2 j / ceρ' j - ceκ 2 * ceN j)) ^ 2 := by
    rw [sum_z5, sum_z5]
    simp only [e0, e2, k0, k2, ceN, ceρ', ceU0, ceU2, v5_0, v5_1, v5_2, v5_3, v5_4]
    norm_num
  rw [r 0]
  rw [t1, z0, z1, z2]
  have h0 := ghH_pos 0
  linarith [mul_lt_mul_of_pos_left t02 h0]

/-- **Theorem 3 of arXiv 2411.06844 fails for the printed Gauss-Hermite weights.**  Section 3.1
(p. 4) names the Gauss-Hermite rule of `e^{-v²}`; here it is the three-point rule, nodes `0`,
`±√(3/2)`, weights `2√π/3, √π/6` (`gaussHermite_three_point`), which violates `QuadNormalized`
(`gaussHermite_three_point_not_quadNormalized`), so that `theorem3_false` does not apply to it.
One exact step of (15), without truncation (`ϑ = 0`), under the CFL condition with CFL number `0.9`,
on `N_x = 5` points with `Δx = 1/N_x` as printed, from the positive rank-one state `g = 𝟙 hᵀ`,
`h_k = c_k / Z_k`, `c = (1/6, 2/3, 1/6)`, which satisfies (11), increases the `ℋ`-norm.  The
relation (11) also holds after the step.  The collision coefficient is `σ = 0`, which Theorem 3
does not exclude and for which neither the proof of Lemma 2 nor that of Theorem 2 uses
`QuadNormalized`; the failure comes from the projection alone, as in `theorem3_false`: the S-step
output lies in `𝒳̂̂ = ceN^⊥` (`gh_augX`, the same space as there), and `ρ'² 𝒳̂̂ ⊄ 𝒳̂̂`.  The spatial
spaces have full dimension, `[K, X]` rank `2 = 2r` and `𝒳̂̂` dimension `4 = 4r`; the velocity
projection is the identity (`gh_augV`).  A floating-point run gives the growth factor `≈ 1.022`
for (15), and `≈ 0.991` for the full scheme (8) from the same data. -/
theorem theorem3_false_gaussHermite :
    ∃ (dt : ℝ) (ρ ρ' : ZMod 5 → ℝ) (X : Matrix (ZMod 5) Unit ℝ) (S : Matrix Unit Unit ℝ)
      (V : Matrix (Fin 3) Unit ℝ) (PX : Matrix (ZMod 5) (ZMod 5) ℝ)
      (PV : Matrix (Fin 3) (Fin 3) ℝ) (ghat g' : Matrix (ZMod 5) (Fin 3) ℝ),
      0 < dt ∧ (∀ k, |ghV k| * dt < 1 / 5) ∧ (∀ j, 0 < ρ j) ∧ (∀ j, 0 < ρ' j) ∧
      (∀ j k, 0 < (X * S * Vᵀ) j k) ∧ IsNormalized ghV ghω (X * S * Vᵀ) ∧
      IsDLRAStep 0 dt (1 / 5) 0 ghV ghω ρ X S V ρ' PX PV ghat g' ∧ IsNormalized ghV ghω g' ∧
      hNormSq ghV ghω (fOf ghV ρ (X * S * Vᵀ)) < hNormSq ghV ghω (fOf ghV ρ' g') :=
  ⟨ghDt, ceρ, ceρ', ceX, ghS, ghB, hyperProj ceN, 1, ghGhat, ghGhat, ghDt_pos, gh_cfl, ceρ_pos,
    ceρ'_pos, fun j k => by rw [gh_g]; exact ghH_pos k, gh_normalized_g, gh_step,
    gh_normalized_ghat, gh_grow⟩

end CounterexamplePrinted

end LeanDLRA.Literature.P2411_06844
