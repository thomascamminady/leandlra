import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2610.18419: Sylvester solvers for implicit DLRA of reaction-diffusion

This module formalizes the mass-lumped matrix ODE of Section 2 (eqs. (2.16), (2.19), (2.21),
(2.22)) of Saha, Yang and Yin, arXiv 2610.18419, in the abstract matrix setting: diagonal positive
mass matrices `M_x = diagonal dx`, `M_y = diagonal dy`, and stiffness matrices `A_x`, `A_y`
(`A_y` symmetric, both positive semidefinite as quadratic forms, the property the paper proves in
Lemma 4.2(i), stated there for periodic boundary conditions). It proves
that the operator `𝓛(W) = L_x W + W L_yᵀ + α W` with `L_x = -M_x⁻¹ A_x`, `L_y = -M_y⁻¹ A_y` is
dissipative for `α ≤ 0` in the weighted inner product `(Z, W)_M = (M_x Z M_y, W)_F`, that is,
`(𝓛(W), W)_M ≤ 0` (`massLumped_dissipative`). This is not a numbered statement of the paper: by
Lemma 2.1 it is the matrix form of `-(∇w_h, ∇w_h)_h + α (w_h, w_h)_h ≤ 0`, the inequality behind
the stability estimates (2.25) and Theorem 3.6 (ii). The proof is direct from the matrix form; the
identity (2.18) of Lemma 2.1 from [26] is not used.

Core definitions used: none (the file works on `Matrix` from Mathlib). Local definitions added:
`massIP` (eq. (2.16)) and `massLumpedOp` (eq. (2.22) with (2.19)).

Not formalized, and left out on purpose:
* Lemma 3.4 (implicit BUG equals implicit Galerkin on subspaces), Prop. 3.2 (equivalences in the
  M-inner product), Theorem 3.6 (well-posedness of the implicit BUG-MLFEM). They need the finite
  element spaces `V_h`, the GQR decomposition and the tangent-space projectors, none of which are in
  the library in this weighted form. The existing `galerkin_implicitEuler_stability` in
  `Foundations/OneSided.lean` covers the abstract Galerkin step only.
* Algorithm 4.1 (sparse-by-small Sylvester solver) is already in the library as
  `sylvester_iff_shifted_columns` and `shifted_existsUnique` in `Stiff/ImplicitSolvability.lean`,
  and is not duplicated here. The banded cost analysis is not formalized.
* The nonsingularity of the shifted systems `A + λ_j I` from `λ_j > 0` (paper, Section 4, proof
  of Lemma 4.3 (i)) is not formalized here. `shifted_existsUnique` there assumes `xᵀ A x ≥ 0`
  for all `x`, which the paper's `A = Δt M_x⁻¹ A_x` need not satisfy (it is only similar to the
  positive semidefinite `Δt M_x^{-1/2} A_x M_x^{-1/2}`); the companion module `P2610_18419b`
  proves invertibility of `Δt M⁻¹ S + λ I` directly (`shift_mul_inv_isUnit`).
* Lemma 2.1 (identity (2.18)) and the FEM assembly of `M_x`, `A_x` from Gauss–Lobatto quadrature
  are cited in the paper and not re-derived here.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2610_18419

/-- The mass-lumped inner product `(Z, W)_M = (M_x Z M_y, W)_F` of arXiv 2610.18419, eq. (2.16),
with the diagonal positive mass matrices `M_x = diagonal dx` and `M_y = diagonal dy`. -/
noncomputable def massIP {m n : ℕ} (dx : Fin m → ℝ) (dy : Fin n → ℝ)
    (Z W : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (Matrix.diagonal dx * Z * Matrix.diagonal dy) i j * W i j

/-- The matrix reaction-diffusion operator `𝓛(W) = L_x W + W L_yᵀ + α W` of arXiv 2610.18419,
eq. (2.22), with `L_x = -M_x⁻¹ A_x` and `L_y = -M_y⁻¹ A_y` as in eq. (2.19). -/
noncomputable def massLumpedOp {m n : ℕ} (dx : Fin m → ℝ) (dy : Fin n → ℝ)
    (Ax : Matrix (Fin m) (Fin m) ℝ) (Ay : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (W : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  (-(Matrix.diagonal fun i => (dx i)⁻¹) * Ax) * W
    + W * (-(Matrix.diagonal fun j => (dy j)⁻¹) * Ay)ᵀ + α • W

/-- `diagonal d⁻¹ * diagonal d = 1` when all entries of `d` are nonzero. -/
private lemma diag_inv_mul_diag {n : ℕ} (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) :
    Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d = 1 := by
  have hfun : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : ℝ) :=
    funext fun i => inv_mul_cancel₀ (hd i)
  rw [Matrix.diagonal_mul_diagonal, hfun]
  exact Matrix.diagonal_one

/-- `M_x L_x = -A_x` for the mass-lumped `L_x = -M_x⁻¹ A_x` (eq. (2.19)). -/
private lemma mass_mul_Lx {m : ℕ} (dx : Fin m → ℝ) (hdx : ∀ i, dx i ≠ 0)
    (Ax : Matrix (Fin m) (Fin m) ℝ) :
    Matrix.diagonal dx * (-(Matrix.diagonal fun i => (dx i)⁻¹) * Ax) = -Ax := by
  have h1 : Matrix.diagonal dx * Matrix.diagonal (fun i => (dx i)⁻¹) = 1 := by
    have hfun : (fun i => dx i * (dx i)⁻¹) = fun _ => (1 : ℝ) :=
      funext fun i => mul_inv_cancel₀ (hdx i)
    rw [Matrix.diagonal_mul_diagonal, hfun]
    exact Matrix.diagonal_one
  rw [neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, h1, Matrix.one_mul]

/-- `L_yᵀ M_y = -A_y` for symmetric `A_y` (eq. (2.19)). -/
private lemma Ly_transpose_mul_mass {n : ℕ} (dy : Fin n → ℝ) (hdy : ∀ j, dy j ≠ 0)
    (Ay : Matrix (Fin n) (Fin n) ℝ) (hAy : Ayᵀ = Ay) :
    (-(Matrix.diagonal fun j => (dy j)⁻¹) * Ay)ᵀ * Matrix.diagonal dy = -Ay := by
  rw [Matrix.transpose_mul, Matrix.transpose_neg, Matrix.diagonal_transpose, hAy,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, diag_inv_mul_diag dy hdy, Matrix.mul_one]

/-- **Dissipativity of the mass-lumped matrix ODE (arXiv 2610.18419, eqs. (2.21)–(2.22)).**
Let `M_x = diagonal dx`, `M_y = diagonal dy` be positive diagonal mass matrices, let `A_y` be
symmetric and `A_x`, `A_y` be positive semidefinite as quadratic forms (the stiffness property of
the paper's Lemma 4.2(i); symmetry of `A_x` is not needed). If `α ≤ 0`, then for every `W`,
`(𝓛(W), W)_M ≤ 0`, where `𝓛(W) = L_x W + W L_yᵀ + α W`, `L_x = -M_x⁻¹ A_x`, `L_y = -M_y⁻¹ A_y`,
and `(·,·)_M` is `massIP`. This is the one-sided estimate used for the stability of the
mass-lumped semi-discretization. -/
theorem massLumped_dissipative {m n : ℕ} (dx : Fin m → ℝ) (dy : Fin n → ℝ)
    (hdx : ∀ i, 0 < dx i) (hdy : ∀ j, 0 < dy j)
    (Ax : Matrix (Fin m) (Fin m) ℝ) (Ay : Matrix (Fin n) (Fin n) ℝ) (hAy : Ayᵀ = Ay)
    (hAxPSD : ∀ v : Fin m → ℝ, 0 ≤ v ⬝ᵥ (Ax *ᵥ v))
    (hAyPSD : ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (Ay *ᵥ v))
    {α : ℝ} (hα : α ≤ 0) (W : Matrix (Fin m) (Fin n) ℝ) :
    massIP dx dy (massLumpedOp dx dy Ax Ay α W) W ≤ 0 := by
  have hdx' : ∀ i, dx i ≠ 0 := fun i => (hdx i).ne'
  have hdy' : ∀ j, dy j ≠ 0 := fun j => (hdy j).ne'
  have h1 := mass_mul_Lx dx hdx' Ax
  have h2 := Ly_transpose_mul_mass dy hdy' Ay hAy
  have hS : Matrix.diagonal dx * massLumpedOp dx dy Ax Ay α W * Matrix.diagonal dy
      = -(Ax * W * Matrix.diagonal dy) - (Matrix.diagonal dx * W * Ay)
        + α • (Matrix.diagonal dx * W * Matrix.diagonal dy) := by
    unfold massLumpedOp
    calc Matrix.diagonal dx * ((-(Matrix.diagonal fun i => (dx i)⁻¹) * Ax) * W
            + W * (-(Matrix.diagonal fun j => (dy j)⁻¹) * Ay)ᵀ + α • W) * Matrix.diagonal dy
        = (Matrix.diagonal dx * (-(Matrix.diagonal fun i => (dx i)⁻¹) * Ax)) * W
            * Matrix.diagonal dy
          + Matrix.diagonal dx * W
            * ((-(Matrix.diagonal fun j => (dy j)⁻¹) * Ay)ᵀ * Matrix.diagonal dy)
          + α • (Matrix.diagonal dx * W * Matrix.diagonal dy) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_assoc]
      _ = -(Ax * W * Matrix.diagonal dy) - (Matrix.diagonal dx * W * Ay)
            + α • (Matrix.diagonal dx * W * Matrix.diagonal dy) := by
          rw [h1, h2]
          simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, sub_eq_add_neg]
  have hT1 : 0 ≤ ∑ i, ∑ j, (Ax * W * Matrix.diagonal dy) i j * W i j := by
    have hcol : ∀ j, ∑ i, (Ax * W * Matrix.diagonal dy) i j * W i j
        = dy j * ((fun k => W k j) ⬝ᵥ (Ax *ᵥ fun k => W k j)) := by
      intro j
      have e : ∀ i, (Ax * W * Matrix.diagonal dy) i j * W i j
          = dy j * ((Ax *ᵥ fun k => W k j) i * W i j) := by
        intro i
        rw [Matrix.mul_diagonal, Matrix.mul_apply]
        simp only [Matrix.mulVec, dotProduct]
        ring
      rw [Finset.sum_congr rfl fun i _ => e i, ← Finset.mul_sum]
      congr 1
      exact dotProduct_comm _ _
    rw [Finset.sum_comm]
    exact Finset.sum_nonneg fun j _ => by
      rw [hcol j]
      exact mul_nonneg (hdy j).le (hAxPSD _)
  have hT2 : 0 ≤ ∑ i, ∑ j, (Matrix.diagonal dx * W * Ay) i j * W i j := by
    have hrow : ∀ i, ∑ j, (Matrix.diagonal dx * W * Ay) i j * W i j
        = dx i * ((fun k => W i k) ⬝ᵥ (Ay *ᵥ fun k => W i k)) := by
      intro i
      have e : ∀ j, (Matrix.diagonal dx * W * Ay) i j * W i j
          = dx i * ((∑ k, W i k * Ay k j) * W i j) := by
        intro j
        rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_apply]
        ring
      rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum]
      congr 1
      simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl fun i _ => hrow i]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hdx i).le (hAyPSD _)
  have hT3 : 0 ≤ ∑ i, ∑ j, (Matrix.diagonal dx * W * Matrix.diagonal dy) i j * W i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
      have e : dx i * W i j * dy j * W i j = (dx i * dy j) * (W i j * W i j) := by ring
      rw [e]
      exact mul_nonneg (mul_nonneg (hdx i).le (hdy j).le) (mul_self_nonneg _)
  have hexp : massIP dx dy (massLumpedOp dx dy Ax Ay α W) W
      = -(∑ i, ∑ j, (Ax * W * Matrix.diagonal dy) i j * W i j)
        - (∑ i, ∑ j, (Matrix.diagonal dx * W * Ay) i j * W i j)
        + α * (∑ i, ∑ j, (Matrix.diagonal dx * W * Matrix.diagonal dy) i j * W i j) := by
    unfold massIP
    simp only [hS, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
      smul_eq_mul, sub_mul, add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib, ← Finset.mul_sum, mul_assoc]
  have hmul : α * (∑ i, ∑ j, (Matrix.diagonal dx * W * Matrix.diagonal dy) i j * W i j) ≤ 0 :=
    mul_nonpos_iff.mpr (Or.inr ⟨hα, hT3⟩)
  rw [hexp]
  linarith

end LeanDLRA.Literature.P2610_18419
