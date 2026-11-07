import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Results of arXiv 2002.02356: Existence of DLR approximations for random semilinear PDEs

Kazashi–Nobile, *Existence of dynamical low rank approximations for random semi-linear
evolutionary equations on the maximal interval* (arXiv 2002.02356v2). Only pages 1–9 of the PDF
were read verbatim (Sections 1–2.2, up to the statement of Lemma 2.10). Nothing from later pages
is formalized.

**Proved here.** The matrix core of **Lemma 2.8** (uniqueness of the orthogonal change of
representation), as `lemma_2_8_matrix_core`. The paper works with `U_j ∈ H` and `Y_j ∈ L²(Ω)`;
here `H` and `L²(Ω)` are replaced by `ℝ^α` and `ℝ^β` with the Euclidean inner product, and
`u_S = Σ_j U_j Y_j` by the matrix product `Vᵀ W` with `V : Matrix ι α ℝ` and `W : Matrix ι β ℝ`
(`ι` the index set of size `S`). Differences from the paper:

* Linear independence of `Vt` in `H` becomes invertibility of the Gram matrix `Vt Vtᵀ`. This is
  the same condition on the rows of `Vt`, and it is the Gram matrix the paper's proof inverts.
* Orthonormality in `L²(Ω)` becomes `W Wᵀ = 1` and `Wt Wtᵀ = 1`.
* The paper's linear independence of `V` is not used by the proof, so it is omitted.
* Uniqueness is proved among all `Θ'` with `Θ'ᵀ W = Wt`, not only among orthogonal `Θ'`.
  This is stronger than the paper's uniqueness in `O(S)`.

**Not proved.** Lemma 2.6 (singular value decomposition in `M_S` and the bounds (2.8)),
Proposition 2.7 (absolutely continuous factorization), Lemma 2.10 and Proposition 2.11
(existence of a Dual DO solution equivalent to the original problem), Lemmas 3.3–3.4 (projector
perturbation), Lemma 4.5 (a priori bound), Theorems 4.6 and 4.8 (maximal interval). These are
statements about `L²(Ω; H)` with Bochner integrals, absolutely continuous curves in `H`, and
unbounded operators `Λ`. Mathlib does not provide that setting in a form usable here, and no
proof was attempted.

**Library definitions used.** None. The statement is elementary matrix algebra on Mathlib's
`Matrix`, `Matrix.transpose` and `Matrix.nonsing_inv`. The projector and factor definitions of
`LeanDLRA/Matrix/` are not needed. The result is not a duplicate of
`LeanDLRA/Matrix/GaugeODE.lean` (`mul_transpose_eq_of_factorization`), which compares the
projectors `U Uᵀ` and not the representation pair `(Vt, Wt)`.
-/

open Matrix

namespace LeanDLRA.Literature.P2002_02356

variable {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]

/-- **Lemma 2.8 (matrix core), arXiv 2002.02356, Lemma 2.8.** Let `V, Vt : Matrix ι α ℝ` and
`W, Wt : Matrix ι β ℝ` with orthonormal rows `W Wᵀ = 1`, `Wt Wtᵀ = 1`, the Gram matrix
`Vt Vtᵀ` invertible, and `Vᵀ W = Vtᵀ Wt`. Then there is an orthogonal `Θ` (`Θᵀ Θ = 1`)
with `(Vt, Wt) = (Θᵀ V, Θᵀ W)`, and `Θ` is unique: every `Θ'` with `Θ'ᵀ W = Wt` equals `Θ`. -/
theorem lemma_2_8_matrix_core (V : Matrix ι α ℝ) (W : Matrix ι β ℝ)
    (Vt : Matrix ι α ℝ) (Wt : Matrix ι β ℝ)
    (hW : W * Wᵀ = 1) (hWt : Wt * Wtᵀ = 1) (hM : IsUnit (Vt * Vtᵀ).det)
    (h : Vᵀ * W = Vtᵀ * Wt) :
    ∃ Θ : Matrix ι ι ℝ, Θᵀ * Θ = 1 ∧ Vt = Θᵀ * V ∧ Wt = Θᵀ * W ∧
      ∀ Θ' : Matrix ι ι ℝ, Θ'ᵀ * W = Wt → Θ' = Θ := by
  set G : Matrix ι ι ℝ := (Vt * Vtᵀ)⁻¹ * Vt * Vᵀ with hGdef
  -- `Wt = G W`
  have hWeq : Wt = G * W := by
    have h1 : (Vt * Vtᵀ)⁻¹ * (Vt * Vtᵀ) = 1 := Matrix.nonsing_inv_mul _ hM
    have h2 : Vt * Vtᵀ * Wt = Vt * Vᵀ * W := by
      rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc]
    calc Wt = (Vt * Vtᵀ)⁻¹ * (Vt * Vtᵀ) * Wt := by rw [h1, Matrix.one_mul]
      _ = (Vt * Vtᵀ)⁻¹ * (Vt * Vᵀ * W) := by rw [Matrix.mul_assoc, h2]
      _ = G * W := by rw [hGdef]; simp only [Matrix.mul_assoc]
  -- `G Gᵀ = 1`
  have hGG : G * Gᵀ = 1 := by
    have h3 : Wt * Wtᵀ = G * (W * Wᵀ) * Gᵀ := by
      rw [hWeq, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [hW, Matrix.mul_one] at h3
    rw [← h3, hWt]
  -- `Vtᵀ G = Vᵀ`, using `W Wᵀ = 1` to cancel `W`
  have hVG : Vtᵀ * G = Vᵀ := by
    have h4 : Vtᵀ * G * W = Vᵀ * W := by
      rw [Matrix.mul_assoc, ← hWeq, h]
    have h5 : (Vtᵀ * G * W) * Wᵀ = (Vᵀ * W) * Wᵀ := by rw [h4]
    simp only [Matrix.mul_assoc, hW, Matrix.mul_one] at h5
    exact h5
  -- `Vt = G V`
  have hVt : Vt = G * V := by
    have h6 : Gᵀ * Vt = V := by
      have := congrArg Matrix.transpose hVG
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.transpose_transpose] at this
    calc Vt = (G * Gᵀ) * Vt := by rw [hGG, Matrix.one_mul]
      _ = G * (Gᵀ * Vt) := by rw [Matrix.mul_assoc]
      _ = G * V := by rw [h6]
  refine ⟨Gᵀ, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_transpose]
    exact hGG
  · rw [Matrix.transpose_transpose, hVt]
  · rw [Matrix.transpose_transpose, hWeq]
  · intro Θ' hΘ'
    have h7 : Θ'ᵀ * W * Wᵀ = G * W * Wᵀ := by rw [hΘ', hWeq]
    simp only [Matrix.mul_assoc, hW, Matrix.mul_one] at h7
    have := congrArg Matrix.transpose h7
    rwa [Matrix.transpose_transpose] at this

end LeanDLRA.Literature.P2002_02356
