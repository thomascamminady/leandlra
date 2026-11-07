import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Frobenius
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Results of arXiv 2105.04358: DLRA for Burgers' equation with uncertainty

This module formalizes the following results of Kusch, Ceruti, Einkemmer, Frank (arXiv 2105.04358,
May 2021), read verbatim from the paper:

* **Theorem 1 (hyperbolicity of the K-step), `kstep_jacobian_symm`, `kstep_jacobian_spectral`.**
  The paper states that for a scalar flux, the K-step equation has flux Jacobian
  `J_nj = E[f'(u_I) W_j W_n]`, which is symmetric, hence diagonalizable with real eigenvalues.
  We prove the abstract core: for any measure `μ` on the random space, any real `f'`, and any
  functions `W_j` (orthonormality is not needed), the matrix `J` is symmetric, and it has a
  real orthogonal spectral decomposition. The paper's hypothesis that the scalar equation is
  hyperbolic and its `C¹` regularity are not used, and the spatial derivative is absent: the
  statement is about the matrix `J` itself, with `E[·] = ∫ · dμ`.
* **Sec. 3.1, closed K-step flux for Burgers, `burgers_flux_coeff`.** For `f(u) = u²/2` the
  paper writes `E[f(u_I) W_m] = ½ Σ_{i,j} K_i K_j a_{ijm}` with `a_{ijm} = E[W_i W_j W_m]`.
  We prove this identity pointwise in `x`, under the integrability of the triple products
  (needed for `E` to be defined). The paper's gPC quadrature is not modeled.
* **Sec. 3.4, filter factor, `filterFactor_pos_le_one`, `filter_rank_le`, `filter_norm_le`.** The
  filtered coefficients are `L̃_{iℓ} = g_λ(i) L̂_{iℓ}` with `g_λ(i) = 1/(1 + λ i² (i+1)²)`. We
  use the 0-indexed convention of the paper's Eq. (6) (`i = 0, …, N`), because Sec. 3.4 writes
  `(i-1)²`, which is inconsistent with that convention. We prove `0 < g_λ(i) ≤ 1` for `λ ≥ 0`,
  that the filter does not increase the rank, and that it does not increase the Frobenius norm.

Not formalized: Sec. 2.1 (the optimization problem (5) for the filter), Sec. 3.2 to 3.3 beyond
the Burgers identity above (the S- and L-step formulas, and the quadrature costs), Sec. 3.5 to
3.6 (nodal and multi-dimensional discretizations), Sec. 4 (boundary ansatz (29)-(30), which is a
construction without a theorem statement and whose exactness is a prescribed boundary
condition on `K`), and Sec. 5 (DG0 discretization and the Lax-Friedrichs flux, with no
theorem statement; the paper does not claim the coincidence with matrix PSI).

Core definitions reused from the library: `Matrix.diagonal`, the Frobenius norm
(`LeanDLRA.Frobenius`). The local definitions are `kstepJac`, `filterFactor`.
-/

open Set Filter Topology Finset MeasureTheory
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2105_04358

variable {Θ : Type*} [MeasurableSpace Θ]

/-! ### Theorem 1: the K-step flux Jacobian -/

/-- The K-step flux Jacobian `J_nj = ∫ g W_j W_n dμ`, i.e. the paper's `E[f'(u_I) W_j W_n]` with
`g = f'(u_I)`. -/
noncomputable def kstepJac {r : ℕ} (μ : Measure Θ) (W : Fin r → Θ → ℝ) (g : Θ → ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun n j => ∫ ξ, g ξ * W j ξ * W n ξ ∂μ

/-- The K-step flux Jacobian is symmetric for every `g`. -/
theorem kstepJac_transpose {r : ℕ} (μ : Measure Θ) (W : Fin r → Θ → ℝ) (g : Θ → ℝ) :
    (kstepJac μ W g)ᵀ = kstepJac μ W g := by
  ext n j
  simp only [kstepJac, Matrix.transpose_apply, Matrix.of_apply]
  congr 1
  funext ξ
  ring

/-- **Theorem 1 of arXiv 2105.04358, symmetry.** For any real function `f'` and
`u_I = ∑_j K_j W_j`, the K-step flux Jacobian `J_nj = E[f'(u_I) W_j W_n]` is symmetric. -/
theorem kstep_jacobian_symm {r : ℕ} (μ : Measure Θ) (W : Fin r → Θ → ℝ) (f' : ℝ → ℝ)
    (K : Fin r → ℝ) :
    (kstepJac μ W (fun ξ => f' (∑ j, K j * W j ξ)))ᵀ =
      kstepJac μ W (fun ξ => f' (∑ j, K j * W j ξ)) :=
  kstepJac_transpose μ W _

/-- **Theorem 1 of arXiv 2105.04358, diagonalization.** The K-step flux Jacobian has real
eigenvalues `lam` and an orthogonal eigenbasis: `J = U diag(lam) Uᵀ` with `Uᵀ U = 1`. -/
theorem kstep_jacobian_spectral {r : ℕ} (μ : Measure Θ) (W : Fin r → Θ → ℝ) (g : Θ → ℝ) :
    ∃ (U : Matrix (Fin r) (Fin r) ℝ) (lam : Fin r → ℝ),
      Uᵀ * U = 1 ∧ kstepJac μ W g = U * Matrix.diagonal lam * Uᵀ := by
  have hM : (kstepJac μ W g).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact kstepJac_transpose μ W g
  refine ⟨(hM.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ), fun i => hM.eigenvalues i, ?_, ?_⟩
  · have h := Matrix.UnitaryGroup.star_mul_self hM.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  · have key := hM.spectral_theorem
    conv_lhs => rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      ]

/-! ### Section 3.1: the closed K-step flux for Burgers' equation -/

/-- **Sec. 3.1 of arXiv 2105.04358, closed flux.** For `f(u) = u²/2` and `u_I = ∑_i K_i W_i`,
`E[f(u_I) W_m] = ½ ∑_{i,j} K_i K_j a_{ijm}` with `a_{ijm} = E[W_i W_j W_m]`. The integrability of
the triple products is needed for `E` to be defined. -/
theorem burgers_flux_coeff {r : ℕ} (μ : Measure Θ) (W : Fin r → Θ → ℝ) (K : Fin r → ℝ)
    (m : Fin r) (hint : ∀ i j k, Integrable (fun ξ => W i ξ * W j ξ * W k ξ) μ) :
    ∫ ξ, (∑ i, K i * W i ξ) ^ 2 / 2 * W m ξ ∂μ =
      1 / 2 * ∑ i, ∑ j, K i * K j * ∫ ξ, W i ξ * W j ξ * W m ξ ∂μ := by
  have hpt : ∀ ξ, (∑ i, K i * W i ξ) ^ 2 / 2 * W m ξ =
      ∑ i, ∑ j, (1 / 2 * (K i * K j)) * (W i ξ * W j ξ * W m ξ) := by
    intro ξ
    rw [sq, Finset.sum_mul_sum]
    simp only [Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint' : ∀ i j, Integrable (fun ξ => 1 / 2 * (K i * K j) * (W i ξ * W j ξ * W m ξ)) μ :=
    fun i j => (hint i j m).const_mul _
  have hsum : ∀ i, Integrable (fun ξ => ∑ j, 1 / 2 * (K i * K j) * (W i ξ * W j ξ * W m ξ)) μ :=
    fun i => integrable_finsetSum Finset.univ (fun j _ => hint' i j)
  calc ∫ ξ, (∑ i, K i * W i ξ) ^ 2 / 2 * W m ξ ∂μ
      = ∫ ξ, ∑ i, ∑ j, 1 / 2 * (K i * K j) * (W i ξ * W j ξ * W m ξ) ∂μ :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = ∑ i, ∫ ξ, ∑ j, 1 / 2 * (K i * K j) * (W i ξ * W j ξ * W m ξ) ∂μ :=
        integral_finsetSum Finset.univ (fun i _ => hsum i)
    _ = ∑ i, ∑ j, ∫ ξ, 1 / 2 * (K i * K j) * (W i ξ * W j ξ * W m ξ) ∂μ :=
        Finset.sum_congr rfl fun i _ => integral_finsetSum Finset.univ (fun j _ => hint' i j)
    _ = 1 / 2 * ∑ i, ∑ j, K i * K j * ∫ ξ, W i ξ * W j ξ * W m ξ ∂μ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul]
        ring

/-! ### Section 3.4: the filter -/

/-- The filter factor `g_λ(i) = 1 / (1 + λ i² (i+1)²)` of arXiv 2105.04358 (Sec. 2.1 and Sec. 3.4),
with the 0-indexed convention `i = 0, …, N` of Eq. (6). -/
noncomputable def filterFactor (lam : ℝ) (i : ℕ) : ℝ :=
  1 / (1 + lam * (i : ℝ) ^ 2 * ((i : ℝ) + 1) ^ 2)

/-- For `λ ≥ 0` the filter factor lies in `(0, 1]`. -/
theorem filterFactor_pos_le_one {lam : ℝ} (hlam : 0 ≤ lam) (i : ℕ) :
    0 < filterFactor lam i ∧ filterFactor lam i ≤ 1 := by
  have h : 0 ≤ lam * (i : ℝ) ^ 2 * ((i : ℝ) + 1) ^ 2 := by positivity
  have hpos : 0 < 1 + lam * (i : ℝ) ^ 2 * ((i : ℝ) + 1) ^ 2 := by linarith
  unfold filterFactor
  exact ⟨one_div_pos.mpr hpos, (div_le_one hpos).mpr (by linarith)⟩

/-- Filtering the coefficients `L̃ = diag(g_λ) L` does not increase the rank. -/
theorem filter_rank_le {N r : ℕ} (lam : ℝ) (L : Matrix (Fin N) (Fin r) ℝ) :
    (Matrix.diagonal (fun i : Fin N => filterFactor lam i) * L).rank ≤ L.rank :=
  Matrix.rank_mul_le_right _ _

/-- Filtering the coefficients `L̃ = diag(g_λ) L` does not increase the Frobenius norm
(for `λ ≥ 0`). -/
theorem filter_norm_le {N r : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) (L : Matrix (Fin N) (Fin r) ℝ) :
    ‖Matrix.diagonal (fun i : Fin N => filterFactor lam i) * L‖ ≤ ‖L‖ := by
  rw [Frobenius.norm_def, Frobenius.norm_def]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.diagonal_mul, mul_pow]
  have h1 : filterFactor lam i.val ^ 2 ≤ 1 := by
    obtain ⟨h0, h2⟩ := filterFactor_pos_le_one hlam i.val
    nlinarith
  calc filterFactor lam i.val ^ 2 * L i j ^ 2 ≤ 1 * L i j ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = L i j ^ 2 := one_mul _

/-! ### Non-vacuity -/

/-- The Burgers flux Jacobian of Theorem 1 applies to a Dirac measure with `f'(u) = u`. -/
example :
    (kstepJac (r := 2) (Measure.dirac (0 : ℝ)) (fun _ _ => (1 : ℝ)) (fun ξ => ξ))ᵀ =
      kstepJac (r := 2) (Measure.dirac (0 : ℝ)) (fun _ _ => (1 : ℝ)) (fun ξ => ξ) :=
  kstepJac_transpose _ _ _

/-- The filter factor for `λ = 1` and `i = 1` is `1/5`. -/
example : filterFactor 1 1 = 1 / 5 := by
  norm_num [filterFactor]

end LeanDLRA.Literature.P2105_04358
