import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2603.13990: Rank-adaptive tensor BUG for Schrödinger

This module proves the unitarity of the implicit midpoint rule for Hermitian Hamiltonians
(Sec. 3 of arXiv 2603.13990), as the matrix statement
`1 + (i h/2) H` and `1 - (i h/2) H` give a unitary one-step map `U` for every Hermitian `H` on
`ℂⁿ`. The implicit midpoint step for `y' = -i H y` is `y₁ = y₀ - (i h/2) H (y₀ + y₁)`. We show that
it is well defined (the solution is unique), that the solution map is unitary, and hence that the
step conserves the Euclidean norm. Both are stated on `Matrix n n ℂ` and `n → ℂ` with Mathlib's
`dotProduct`/`mulVec`, which is the abstract core of the paper's statement.

Not formalized here, and why:
* Lemma 1 (orthonormality of MPS state vectors) and Algorithm 1 / Sec. 5 (MPS-BUG sweeps): they need
  tensor-train infrastructure that the library does not have. The matrix and Tucker versions of
  the rank-adaptive step already exist (`TuckerBUG.lean`, `RankAdaptiveBUG.lean`), so nothing is
  duplicated.
* Eq. (4.19) (the TDVP tangent projector as a telescoping sum of nested projectors): not done here.
* Appendix A (truncated SVD, Eckart–Young): already proved in `LeanDLRA/Classical/EckartYoung.lean`
  (`sq_norm_sub_truncation`, `norm_sub_truncation`, `specNorm_sub_truncation`); not duplicated.
* TDVP norm and energy conservation: the Galerkin norm conservation is in `LeanDLRA/Foundations`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2603_13990

variable {n : Type*} [Fintype n]

/-- The sum of squared moduli is the (complex) Hermitian square `⟪v, v⟫`. -/
private lemma sum_norm_sq_eq_star_dotProduct (v : n → ℂ) :
    ∑ i, ((‖v i‖ ^ 2 : ℝ) : ℂ) = star v ⬝ᵥ v := by
  simp [dotProduct, Complex.conj_mul']

/-- The kernel of `1 + c • H` is trivial when `star c = -c` (i.e. `c` is purely imaginary) and `H`
is Hermitian: `⟨x, x⟩ + c ⟨x, H x⟩ = 0` and its conjugate force `⟨x, x⟩ = 0`. -/
private lemma imagCoef_mulVec_injective [DecidableEq n] (H : Matrix n n ℂ)
    (hH : H.IsHermitian) (c : ℂ)
    (hc : star c = -c) (x : n → ℂ) (hx : (1 + c • H) *ᵥ x = 0) : x = 0 := by
  have e1 : star x ⬝ᵥ x + c * (star x ⬝ᵥ (H *ᵥ x)) = 0 := by
    have h' := congrArg (fun v => star x ⬝ᵥ v) hx
    simpa [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
      using h'
  have hs' : star (star x ⬝ᵥ x) = star x ⬝ᵥ x := by
    simp [dotProduct, star_sum, mul_comm]
  have e2 := congrArg star e1
  rw [star_add, star_mul, star_zero, hc, hs', hH.star_dotProduct_mulVec_comm x x] at e2
  have hs : star x ⬝ᵥ x = 0 := by linear_combination (e1 + e2) / 2
  have hr : ∑ i, ‖x i‖ ^ 2 = 0 := by
    have hc0 : ∑ i, ((‖x i‖ ^ 2 : ℝ) : ℂ) = 0 := by rw [sum_norm_sq_eq_star_dotProduct, hs]
    exact_mod_cast hc0
  have hi : ∀ i ∈ (univ : Finset n), ‖x i‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp hr
  funext i
  have := hi i (mem_univ i)
  simpa using this

/-- **Implicit midpoint is unitary (arXiv 2603.13990, Sec. 3).** For a Hermitian `H` and a step
`h`, the implicit midpoint rule for `y' = -i H y`, `y₁ = y₀ - (i h/2) H (y₀ + y₁)`, has a unique
solution `y₁`, and the map `y₀ ↦ y₁` is given by a unitary matrix `U` (`Uᴴ U = 1 = U Uᴴ`).

The paper states unitarity of the Cayley transform `(1 - i h H/2)(1 + i h H/2)⁻¹` for the implicit
midpoint rule; here `U = (1 + c H)⁻¹ (1 - c H)` with `c = i h/2`, written for the solution. -/
theorem implicitMidpoint_unitary [DecidableEq n] (H : Matrix n n ℂ) (hH : H.IsHermitian) (h : ℝ) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      ∀ y0 y1 : n → ℂ, y1 = y0 - (Complex.I * ((h / 2 : ℝ) : ℂ)) • (H *ᵥ (y0 + y1)) →
        y1 = U *ᵥ y0 := by
  set c : ℂ := Complex.I * ((h / 2 : ℝ) : ℂ) with hc_def
  have hc : star c = -c := by simp [hc_def]
  set N : Matrix n n ℂ := 1 + c • H with hN_def
  set M : Matrix n n ℂ := 1 - c • H with hM_def
  have hstar : Nᴴ = M := by
    rw [hN_def, hM_def, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, hH.eq, hc, sub_eq_add_neg, neg_smul]
  have hMH : Mᴴ = N := by rw [← hstar, Matrix.conjTranspose_conjTranspose]
  have hNM : N * M = M * N := by
    have h1 : Commute (1 : Matrix n n ℂ) (1 - c • H) := Commute.one_left _
    have h2 : Commute (c • H) (1 - c • H) :=
      Commute.sub_right (Commute.one_right _) (Commute.refl _)
    exact (Commute.add_left h1 h2).eq
  have hinj : Function.Injective (fun v => N *ᵥ v) := by
    intro a b hab
    have hab' : N *ᵥ a = N *ᵥ b := hab
    have h0 : N *ᵥ (a - b) = 0 := by
      rw [Matrix.mulVec_sub, hab', sub_self]
    exact sub_eq_zero.mp (imagCoef_mulVec_injective H hH c hc (a - b) h0)
  have hNu : IsUnit N := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hdet : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).mp hNu
  set a : Matrix n n ℂ := N⁻¹ with ha_def
  have hNa : N * a = 1 := Matrix.mul_nonsing_inv N hdet
  have haN : a * N = 1 := Matrix.nonsing_inv_mul N hdet
  have haM : a * M = M * a := by
    calc a * M = a * M * (N * a) := by rw [hNa, mul_one]
      _ = a * (M * N) * a := by simp only [mul_assoc]
      _ = a * (N * M) * a := by rw [hNM]
      _ = (a * N) * (M * a) := by simp only [mul_assoc]
      _ = M * a := by rw [haN, one_mul]
  have haH : aᴴ * M = 1 := by
    rw [← hstar, ← Matrix.conjTranspose_mul, hNa, Matrix.conjTranspose_one]
  have hMa : M * aᴴ = 1 := mul_eq_one_comm.mp haH
  have hZM : aᴴ * a * M = a := by rw [mul_assoc, haM, ← mul_assoc, haH, one_mul]
  have hUU : (a * M)ᴴ * (a * M) = 1 := by
    calc (a * M)ᴴ * (a * M) = N * (aᴴ * a) * M := by
          rw [Matrix.conjTranspose_mul, hMH]; simp only [mul_assoc]
      _ = N * (aᴴ * a * M) := by simp only [mul_assoc]
      _ = N * a := by rw [hZM]
      _ = 1 := hNa
  refine ⟨a * M, hUU, mul_eq_one_comm.mp hUU, ?_⟩
  intro y0 y1 hy
  have h2 : H *ᵥ (y0 + y1) = H *ᵥ y0 + H *ᵥ y1 := Matrix.mulVec_add _ _ _
  have hy' : y1 + c • (H *ᵥ y1) = y0 - c • (H *ᵥ y0) := by
    rw [h2, smul_add] at hy
    linear_combination (norm := module) hy
  have hNy : N *ᵥ y1 = M *ᵥ y0 := by
    rw [hN_def, hM_def, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
    exact hy'
  rw [← Matrix.mulVec_mulVec, ← hNy, Matrix.mulVec_mulVec, haN, Matrix.one_mulVec]

/-- **Norm conservation of the implicit midpoint rule (arXiv 2603.13990, Sec. 3).** For a Hermitian
`H`, every solution `y₁` of `y₁ = y₀ - (i h/2) H (y₀ + y₁)` satisfies `‖y₁‖₂ = ‖y₀‖₂`, in the form
`∑ |y₁ᵢ|² = ∑ |y₀ᵢ|²`. This is the consequence of `implicitMidpoint_unitary`. -/
theorem implicitMidpoint_norm_conserved (H : Matrix n n ℂ) (hH : H.IsHermitian) (h : ℝ)
    (y0 y1 : n → ℂ) (hy : y1 = y0 - (Complex.I * ((h / 2 : ℝ) : ℂ)) • (H *ᵥ (y0 + y1))) :
    ∑ i, ‖y1 i‖ ^ 2 = ∑ i, ‖y0 i‖ ^ 2 := by
  classical
  obtain ⟨U, hU, _, hsol⟩ := implicitMidpoint_unitary H hH h
  have hy1 := hsol y0 y1 hy
  have hnorm : star (U *ᵥ y0) ⬝ᵥ (U *ᵥ y0) = star y0 ⬝ᵥ y0 := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  have hc : ∑ i, ((‖y1 i‖ ^ 2 : ℝ) : ℂ) = ∑ i, ((‖y0 i‖ ^ 2 : ℝ) : ℂ) := by
    rw [sum_norm_sq_eq_star_dotProduct, sum_norm_sq_eq_star_dotProduct, hy1, hnorm]
  exact_mod_cast hc

/-- Non-vacuity: the implicit midpoint hypothesis holds, e.g. for `H = 0` and `y₁ = y₀`. -/
example (y0 : Fin 2 → ℂ) :
    y0 = y0 - (Complex.I * ((1 / 2 : ℝ) : ℂ)) •
      ((0 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ (y0 + y0)) := by
  simp

end LeanDLRA.Literature.P2603_13990
