import LeanDLRA.Foundations.ODE
import LeanDLRA.Matrix.Frobenius

/-!
# Results of arXiv 2508.04484: High-order deterministic DLRA for proton transport

This module formalizes the material-mixture structure of the collision term in arXiv 2508.04484
(Sec. 2.1, eq. (6); Sec. 3.3.2, eq. (25); Sec. 3.3.3, eq. (26b)). The paper writes the
cross sections of a mixture of base materials as weighted sums, `Σ_s = Σ_i w_i Σ_{s;i}`, and the
discretized collision term as `G(t,u) = Σ_i w_i S⁻¹ u (Σ_{t;i} I + G_i) + Σ_i w_i ψᵘ T_M G_i`.
Matrices are real, with the Frobenius norm (`open scoped LeanDLRA.Frobenius`), and the
Lipschitz notion is `IsLipschitzField` from `LeanDLRA/Foundations/ODE.lean`. Everything is stated
for an arbitrary finite family of materials `ι` with time-dependent coefficients `D t i`, `C t i`,
so the paper's `D_i = w_i S⁻¹` and `C_i = Σ_{t;i} I + G_i` are special cases. Each result:

* `material_mixture_isLipschitz` (Sec. 2.1 / 3.3.2, eqs. (6), (25)): the collision field
  `u ↦ Σ_i D_i u C_i + B(t)` is Lipschitz in `u` with constant `Σ_i ‖D_i‖ ‖C_i‖`. The constant is
  derived here, the paper states no bound. Only the counting of operations is omitted (see below).
* `material_mixture_factorized` (Sec. 3.3.2, low-rank evaluation): for `u = U S Vᵀ`, the field is
  evaluated on the factors as `(D_i U) S ((C_iᵀ V))ᵀ`, so it is never formed as a full `n × m`
  product in the proof. The paper does not write this identity; its cost claim `O(r²(n+m))`
  (Sec. 5, quoted from its ref. [27]) is not formalized.
* `collided_L_step_galerkin` (Sec. 3.3.3, eq. (26b), step 1): the collided L-step with fixed
  basis `U` equals the Galerkin projection `Uᵀ F(t, U L)` of the collision field onto range(U),
  with `L ∈ ℝ^{r×m}` as in the paper.
* `collided_L_step_isLipschitz`: the right-hand side of that L-step is Lipschitz in `L` with
  constant `Σ_i ‖Uᵀ D_i U‖ ‖C_i‖`.

## Core definitions used and deviations

Core definitions used: `IsLipschitzField` (`LeanDLRA.Foundations.ODE`) and the Frobenius norm and
submultiplicativity `LeanDLRA.Frobenius.norm_mul_le`. No new definitions are introduced.

The results are stated for arbitrary coefficient matrices `C_i`, so they do not depend on the
sign convention of the total-cross-section term.

## Left out

* The cost bound `O(r²(n+m))` of the factorized evaluation (only the identity is proved).
* The augmented BUG streaming step (eqs. (15a)-(15c) and (26a)), its RK4 substeps, and the Lie
  splitting error. The paper states no error estimate for them. The library's global BUG error
  (`bug_global_error`) needs a bounded field, while the streaming field is linear in `u` and not
  bounded, so it does not apply directly.
* The claim that the hybrid L-step is exact when `G` preserves range(`P_U`): the paper does not
  state it.
-/

open scoped LeanDLRA.Frobenius Matrix

namespace LeanDLRA.Literature.P2508_04484

variable {ι ρ κ r : Type*} [Fintype ι] [Fintype ρ] [Fintype κ] [Fintype r]

/-- Frobenius submultiplicativity for a triple product. -/
lemma norm_mul_mul_le {ρ' κ' : Type*} [Fintype ρ'] [Fintype κ']
    (A : Matrix ρ' ρ' ℝ) (X : Matrix ρ' κ' ℝ) (B : Matrix κ' κ' ℝ) :
    ‖A * X * B‖ ≤ ‖A‖ * ‖X‖ * ‖B‖ :=
  (LeanDLRA.Frobenius.norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (LeanDLRA.Frobenius.norm_mul_le _ _) (norm_nonneg _))

/-- arXiv 2508.04484, Sec. 2.1 eq. (6) and Sec. 3.3.2 eq. (25): the collision field of a
mixture of materials, `u ↦ Σ_i D_i u C_i + B(t)`, with `D_i = w_i S⁻¹` and
`C_i = Σ_{t;i} I + G_i` in the paper, is Lipschitz in `u` with constant `L` whenever
`Σ_i ‖D_i‖ ‖C_i‖ ≤ L` for every `t`. The constant is derived here, the paper states none. -/
theorem material_mixture_isLipschitz (D : ℝ → ι → Matrix ρ ρ ℝ) (C : ℝ → ι → Matrix κ κ ℝ)
    (B : ℝ → Matrix ρ κ ℝ) {L : ℝ} (hL : ∀ t, ∑ i, ‖D t i‖ * ‖C t i‖ ≤ L) :
    IsLipschitzField (fun t u => (∑ i, D t i * u * C t i) + B t) L := by
  intro t x y
  dsimp only
  have hdiff : (∑ i, D t i * x * C t i) + B t - ((∑ i, D t i * y * C t i) + B t)
      = ∑ i, D t i * (x - y) * C t i := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]
    abel
  rw [hdiff]
  calc ‖∑ i, D t i * (x - y) * C t i‖
      ≤ ∑ i, ‖D t i * (x - y) * C t i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖D t i‖ * ‖x - y‖ * ‖C t i‖ :=
        Finset.sum_le_sum fun i _ => norm_mul_mul_le _ _ _
    _ = (∑ i, ‖D t i‖ * ‖C t i‖) * ‖x - y‖ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ L * ‖x - y‖ := mul_le_mul_of_nonneg_right (hL t) (norm_nonneg _)

/-- Non-vacuity: with one material, the hypothesis holds with `L = ‖D‖ ‖C‖`. -/
example (D : Matrix ρ ρ ℝ) (C : Matrix κ κ ℝ) (B : Matrix ρ κ ℝ) :
    IsLipschitzField (fun _ u => (∑ _i : Unit, D * u * C) + B) (‖D‖ * ‖C‖) :=
  material_mixture_isLipschitz (fun _ _ => D) (fun _ _ => C) (fun _ => B)
    (fun _ => by simp)

/-- arXiv 2508.04484, Sec. 3.3.2 eq. (25) (low-rank evaluation): for `u = U S Vᵀ`, the mixture
field satisfies `Σ_i D_i u C_i = Σ_i (D_i U) S ((C_iᵀ V))ᵀ`, the factorized evaluation. The paper
does not write this identity; its operation-count claim (Sec. 5) is not formalized. -/
theorem material_mixture_factorized (D : ι → Matrix ρ ρ ℝ) (C : ι → Matrix κ κ ℝ)
    (U : Matrix ρ r ℝ) (S : Matrix r r ℝ) (V : Matrix κ r ℝ) :
    ∑ i, D i * (U * S * Vᵀ) * C i = ∑ i, (D i * U) * S * ((C i)ᵀ * V)ᵀ := by
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- arXiv 2508.04484, Sec. 3.3.3 eq. (26b), step 1 (collided L-step): with the basis `U` held
fixed and `L ∈ ℝ^{r×m}`, the collided self-scattering right-hand side `Σ_i D_i (U L) C_i` is
Galerkin-projected onto range(U) as `Uᵀ · (Σ_i D_i (U L) C_i) = Σ_i (Uᵀ D_i U) L C_i`. The
paper writes this sum with `C_i = Σ_{t;i} I + G_i` up to the sign discussed in the module
docstring. -/
theorem collided_L_step_galerkin (D : ι → Matrix ρ ρ ℝ) (C : ι → Matrix κ κ ℝ)
    (U : Matrix ρ r ℝ) (L : Matrix r κ ℝ) :
    Uᵀ * (∑ i, D i * (U * L) * C i) = ∑ i, (Uᵀ * D i * U) * L * C i := by
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mul_assoc]

/-- arXiv 2508.04484, Sec. 3.3.3 eq. (26b), step 1: the right-hand side of the collided L-step,
`L ↦ Σ_i (Uᵀ D_i U) L C_i`, is Lipschitz in `L` with constant `L'` whenever
`Σ_i ‖Uᵀ D_i U‖ ‖C_i‖ ≤ L'` for every `t`. -/
theorem collided_L_step_isLipschitz (D : ℝ → ι → Matrix ρ ρ ℝ) (C : ℝ → ι → Matrix κ κ ℝ)
    (U : Matrix ρ r ℝ) {L' : ℝ} (hL : ∀ t, ∑ i, ‖Uᵀ * D t i * U‖ * ‖C t i‖ ≤ L') :
    IsLipschitzField (fun t (L : Matrix r κ ℝ) => ∑ i, (Uᵀ * D t i * U) * L * C t i) L' := by
  have h := material_mixture_isLipschitz (fun t i => Uᵀ * D t i * U) C
    (fun _ => (0 : Matrix r κ ℝ)) hL
  simpa using h

end LeanDLRA.Literature.P2508_04484
