import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Results of arXiv 2206.14404: Sweep-based low-rank method for S_N transport

Formalized: Sec. 4.1 of the paper, the upwind backward-Euler K-step for one octant with `μ ≥ 0`
(the paper's "+" octant), reduced to the matrix setting. The paper's diagonal blocks are
`P_i = R̄ + (σ_t(i) + 1/h) I_r` with `R̄ = Vᵀ diag(μ) V / Δx` (r × r). The file proves:

* `galerkinR_posSemidef`, `rBar_posSemidef`: `R̄` is positive semidefinite when `μ ≥ 0`
  (the "one sign" condition of the octant).
* `diagBlock_posDef`: each diagonal block is positive definite and hence invertible when `σ_t ≥ 0`
  and `h > 0`. The paper does not state this; it is the positivity needed for the marching solve.
* `upwind_marching`: for cells `1..n`, the paper's discrete equation (30) in vector form, with
  vacuum boundary `K_0 = 0`, has exactly one solution, given by the marching recursion (32).
  The marched sequence also satisfies (30) for every cell.

Differences from the paper. Eq. (30) is stated as one vector equation per cell, with the `r`
components of `K_{i}` as a vector; the paper's index sum `Σ_ℓ K_ℓ r_{ℓj}` is `R̄ *ᵥ K` because
`R̄` is symmetric. The nonnegativity `σ_t ≥ 0` and `h > 0` are not written in the paper, but
`σ_t` is a total cross-section and `h` a step size, so they are assumed here. The source `s_i`
is an arbitrary vector (it contains the scattering and `K^{0}/h` terms of the paper).

Not formalized. Sec. 3 (the octant-wise BUG integrator, Eqs. (21)-(23)) is a derivation of the
equations, not a stated theorem. Its convergence would need the octant block projectors on the
product space, which this file does not build; the paper states no convergence result (its
"convergence" refers to the source iteration). Eqs. (25)-(26) (implicit Runge-Kutta) are not
formalized.

The core library is not used: this file is a finite-dimensional linear-algebra statement, and
`LeanDLRA` has no marching or upwind-block definitions to reuse.
-/

open Matrix

namespace LeanDLRA.Literature.P2206_14404

variable {N r : ℕ}

/-- Paper: `R^+ = V^T μ V`, the `r × r` Galerkin compression of the transport term
for one octant. -/
noncomputable def galerkinR (V : Matrix (Fin N) (Fin r) ℝ) (μ : Fin N → ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  Vᵀ * diagonal μ * V

/-- Paper: `R̄^+ = R^+ / Δx`. -/
noncomputable def rBar (Δx : ℝ) (V : Matrix (Fin N) (Fin r) ℝ) (μ : Fin N → ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  Δx⁻¹ • galerkinR V μ

/-- Paper: the diagonal block `L_i^+ = R̄^+ + (σ_t(i) + 1/h) I_r`, with `c = σ_t(i) + 1/h`. -/
noncomputable def diagBlock (R : Matrix (Fin r) (Fin r) ℝ) (c : ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  R + c • (1 : Matrix (Fin r) (Fin r) ℝ)

/-- Paper Eq. (32), the marching scheme `K_i = P_i⁻¹ (R̄ K_{i-1} + s_i)`, with vacuum `K_0 = 0`. -/
noncomputable def march (R : Matrix (Fin r) (Fin r) ℝ) (c : ℕ → ℝ) (s : ℕ → Fin r → ℝ) :
    ℕ → Fin r → ℝ
  | 0 => 0
  | i + 1 => (diagBlock R (c (i + 1)))⁻¹ *ᵥ (R *ᵥ march R c s i + s (i + 1))

lemma galerkinR_posSemidef (V : Matrix (Fin N) (Fin r) ℝ) {μ : Fin N → ℝ} (hμ : ∀ j, 0 ≤ μ j) :
    (galerkinR V μ).PosSemidef := by
  have hD : (diagonal μ).PosSemidef := posSemidef_diagonal_iff.mpr hμ
  have h := hD.conjTranspose_mul_mul_same V
  simpa [galerkinR, conjTranspose_eq_transpose_of_trivial] using h

lemma rBar_posSemidef (Δx : ℝ) (hΔx : 0 < Δx) (V : Matrix (Fin N) (Fin r) ℝ)
    {μ : Fin N → ℝ} (hμ : ∀ j, 0 ≤ μ j) : (rBar Δx V μ).PosSemidef :=
  (galerkinR_posSemidef V hμ).smul (inv_nonneg.mpr hΔx.le)

lemma diagBlock_posDef {R : Matrix (Fin r) (Fin r) ℝ} (hR : R.PosSemidef) {c : ℝ} (hc : 0 < c) :
    (diagBlock R c).PosDef := by
  unfold diagBlock
  have h1 : (c • (1 : Matrix (Fin r) (Fin r) ℝ)).PosDef :=
    (Matrix.PosDef.one).smul hc
  rw [add_comm]
  exact h1.add_posSemidef hR

lemma diagBlock_isUnit_det {R : Matrix (Fin r) (Fin r) ℝ} (hR : R.PosSemidef) {c : ℝ}
    (hc : 0 < c) : IsUnit (diagBlock R c).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (diagBlock_posDef hR hc).isUnit

lemma diagBlock_mulVec (R : Matrix (Fin r) (Fin r) ℝ) (c : ℝ) (x : Fin r → ℝ) :
    diagBlock R c *ᵥ x = R *ᵥ x + c • x := by
  simp [diagBlock, add_mulVec, smul_mulVec, one_mulVec]

/-- Paper Eqs. (30)-(32) for one octant with `μ ≥ 0`, the "+" octant. Cells `1..n` of the
unknown `u` satisfy the backward-Euler equation (30) in vector form,
`(1/h) u_{i} = -R̄ (u_{i} - u_{i-1}) - σ_t(i) u_{i} + s_i`, with vacuum `u_0 = 0`. Then
`u` agrees with the marching solution (32) on `0..n`. The marched sequence also satisfies (30)
for every cell. Here `σ_t ≥ 0` and `h > 0` are assumed (see the module docstring). -/
theorem upwind_marching (Δx h : ℝ) (hΔx : 0 < Δx) (hh : 0 < h)
    (V : Matrix (Fin N) (Fin r) ℝ) (μ : Fin N → ℝ) (hμ : ∀ j, 0 ≤ μ j)
    (σ : ℕ → ℝ) (hσ : ∀ i, 0 ≤ σ i) (s : ℕ → Fin r → ℝ)
    (u : ℕ → Fin r → ℝ) (hu0 : u 0 = 0) (n : ℕ)
    (hu : ∀ i < n, (1 / h) • u (i + 1) =
      -(rBar Δx V μ *ᵥ (u (i + 1) - u i)) - σ (i + 1) • u (i + 1) + s (i + 1)) :
    (∀ i ≤ n, u i = march (rBar Δx V μ) (fun i => σ i + 1 / h) s i) ∧
    (∀ i, (1 / h) • march (rBar Δx V μ) (fun i => σ i + 1 / h) s (i + 1) =
      -(rBar Δx V μ *ᵥ (march (rBar Δx V μ) (fun i => σ i + 1 / h) s (i + 1)
          - march (rBar Δx V μ) (fun i => σ i + 1 / h) s i))
        - σ (i + 1) • march (rBar Δx V μ) (fun i => σ i + 1 / h) s (i + 1) + s (i + 1)) := by
  set R := rBar Δx V μ with hRdef
  set c : ℕ → ℝ := fun i => σ i + 1 / h with hcdef
  have hR : R.PosSemidef := rBar_posSemidef Δx hΔx V hμ
  have hc : ∀ i, 0 < c i := fun i => by
    simp only [hcdef]
    have : 0 < 1 / h := by positivity
    linarith [hσ i]
  have hdet : ∀ i, IsUnit (diagBlock R (c i)).det := fun i => diagBlock_isUnit_det hR (hc i)
  -- The equation (30) written as `P_i u_i = R̄ u_{i-1} + s_i`.
  have step : ∀ i < n, diagBlock R (c (i + 1)) *ᵥ u (i + 1) = R *ᵥ u i + s (i + 1) := by
    intro i hi
    have hu' := hu i hi
    simp only [Matrix.mulVec_sub] at hu'
    rw [diagBlock_mulVec]
    simp only [hcdef]
    linear_combination (norm := module) hu'
  have key : ∀ i ≤ n, u i = march R c s i := by
    intro i
    induction i with
    | zero => intro _; simp [march, hu0]
    | succ k ih =>
      intro hk
      have hstep := step k (by omega)
      have hu_eq : u (k + 1) = (diagBlock R (c (k + 1)))⁻¹ *ᵥ (R *ᵥ u k + s (k + 1)) := by
        rw [← hstep, mulVec_mulVec, Matrix.nonsing_inv_mul _ (hdet (k + 1)), one_mulVec]
      rw [hu_eq, ih (by omega)]
      simp only [march]
  refine ⟨key, fun i => ?_⟩
  set m := march R c s with hm
  have hP : diagBlock R (c (i + 1)) *ᵥ m (i + 1) = R *ᵥ m i + s (i + 1) := by
    have hm1 : m (i + 1) = (diagBlock R (c (i + 1)))⁻¹ *ᵥ (R *ᵥ m i + s (i + 1)) := by
      simp only [hm, march]
    rw [hm1, mulVec_mulVec, Matrix.mul_nonsing_inv _ (hdet (i + 1)), one_mulVec]
  rw [diagBlock_mulVec] at hP
  simp only [Matrix.mulVec_sub, hcdef] at hP ⊢
  linear_combination (norm := module) hP

end LeanDLRA.Literature.P2206_14404
