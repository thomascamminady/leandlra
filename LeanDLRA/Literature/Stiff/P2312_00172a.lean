import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Foundations.OneSided
import LeanDLRA.Matrix.Frobenius

/-!
# Results of arXiv 2312.00172: Projected exponential methods for stiff DLRA (Carrel-Vandereycken)

This module formalizes two results of arXiv 2312.00172 for real matrices with the Frobenius norm
`‖·‖` (the paper's default norm). Core definitions used: `EckartYoung.truncation` (the paper's
truncation `T_r`, the best rank-`r` approximation), `EckartYoung.norm_sub_truncation_le`,
`ODESolution`, `IsOneSidedLipschitzField`, `isOneSidedLipschitzField_linear_iff`,
`ODESolution.norm_sub_le_exp_of_oneSided` and `norm_sub_le_gronwallBound_of_oneSided`.
The local definition added is `phi1`, the scalar `φ₁` of the paper's eq. (4).

* **Lemma 8 (truncation inequality)**, `truncation_add_sub_le`:
  `‖T_r(A + E) - A‖ ≤ ‖T_r(A) - A‖ + 2‖E‖`, stated exactly as in the paper. Its immediate
  corollary `truncation_add_sub_le_of_rank_le`, `‖T_r(A + E) - A‖ ≤ 2‖E‖` when `rank A ≤ r`, is
  not printed in the paper.
* **Lemma 3 (bounds of the φ-functions), for k = 0 and k = 1**, `norm_exp_le` and `norm_phi1_le`:
  `‖φ₀(hL) X‖ ≤ φ₀(hℓ) ‖X‖` and `‖φ₁(hL) X‖ ≤ φ₁(hℓ) ‖X‖`, with `ℓ` the one-sided Lipschitz
  constant of `L` (Definition 1), any real `ℓ` satisfying `⟪L X, X⟫ ≤ ℓ ‖X‖²` for all `X`.
  Here `φ₀(hL) X = y(h)` for the solution `y' = L y`, `y(0) = X` (the exponential), and
  `φ₁(hL) X = h⁻¹ z(h)` for the solution `z' = L z + X`, `z(0) = 0`. These are the IVP
  characterizations of Lemma 2 of the paper, which we take as the definition of `φ₀` and `φ₁`
  and do not reprove. The scalars are `φ₀(z) = e^z` and `φ₁(z) = (e^z - 1)/z`, `φ₁(0) = 1`.

Differences from the paper and what is left out:

* Lemma 3 is proved only for `k = 0, 1` and only for the Frobenius norm (the paper also allows the
  spectral norm). The general `k ≥ 2` needs a calculus of `φ_k` that the library does not have.
  For `k = 1` the step size is `h > 0` instead of `h ≥ 0`, since `φ₁(hL) X = h⁻¹ z(h)` needs
  `h ≠ 0`; at `h = 0` the claim `‖X‖ ≤ φ₁(0) ‖X‖` is trivial.
* `ℓ` is any constant satisfying the one-sided inequality, not necessarily the smallest one. The
  statement is therefore at least as strong as the paper's.
* The matrix `L` is a continuous linear map on `Matrix m n ℝ`, which is the paper's situation since
  the paper's `L` is linear on a finite-dimensional space.
* Lemma 9 (stable expansion of the projected flow), Theorem 10 (projected exponential Euler) and
  Theorem 11 (projected exponential Runge) are not formalized. They need the Taylor and defect
  expansions of Sections 2.1 and 3.1 of the paper, the DLRA accuracy theorem (Theorem 7) with the
  projected-flow estimates, and the stage-wise recursion of Sections 3.2 and 3.3. The library
  does not yet contain these, so they are omitted here.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2312_00172

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The scalar `φ₁` of the paper's eq. (4), `φ₁(z) = (e^z - p₀(z))/z` with `p₀ = 1`, and
`φ₁(0) = 1` by continuity. -/
noncomputable def phi1 (z : ℝ) : ℝ := if z = 0 then 1 else (Real.exp z - 1) / z

/-- **arXiv 2312.00172, Lemma 8 (truncation inequality).** For the truncation `T_r` to rank `r`
(the Frobenius best rank-`r` approximation, `EckartYoung.truncation`) and any matrices `A, E`,
`‖T_r(A + E) - A‖ ≤ ‖T_r(A) - A‖ + 2‖E‖`. -/
theorem truncation_add_sub_le [DecidableEq n] (A E : Matrix m n ℝ) (r : ℕ) :
    ‖EckartYoung.truncation (A + E) r - A‖ ≤ ‖EckartYoung.truncation A r - A‖ + 2 * ‖E‖ := by
  have h1 : ‖(A + E) - EckartYoung.truncation (A + E) r‖ ≤
      ‖(A + E) - EckartYoung.truncation A r‖ :=
    EckartYoung.norm_sub_truncation_le (A + E) (EckartYoung.rank_truncation_le A r)
  have h2 : ‖(A + E) - EckartYoung.truncation A r‖ ≤ ‖A - EckartYoung.truncation A r‖ + ‖E‖ := by
    rw [show (A + E) - EckartYoung.truncation A r = (A - EckartYoung.truncation A r) + E by abel]
    exact norm_add_le _ _
  have h3 : ‖EckartYoung.truncation (A + E) r - A‖ ≤
      ‖(A + E) - EckartYoung.truncation (A + E) r‖ + ‖E‖ := by
    rw [show EckartYoung.truncation (A + E) r - A =
      -((A + E) - EckartYoung.truncation (A + E) r) + E by abel]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
  have h4 : ‖EckartYoung.truncation A r - A‖ = ‖A - EckartYoung.truncation A r‖ := norm_sub_rev _ _
  linarith

/-- **Corollary of arXiv 2312.00172, Lemma 8** (not printed in the paper): if `rank A ≤ r` then
`‖T_r(A + E) - A‖ ≤ 2‖E‖`, since then `T_r(A) = A`. -/
theorem truncation_add_sub_le_of_rank_le [DecidableEq n] {A : Matrix m n ℝ} {r : ℕ}
    (hA : A.rank ≤ r) (E : Matrix m n ℝ) :
    ‖EckartYoung.truncation (A + E) r - A‖ ≤ 2 * ‖E‖ := by
  have h := truncation_add_sub_le A E r
  have h0 : ‖A - EckartYoung.truncation A r‖ ≤ 0 := by
    simpa using EckartYoung.norm_sub_truncation_le A hA
  have h1 : ‖EckartYoung.truncation A r - A‖ = 0 := by
    rw [norm_sub_rev]
    exact le_antisymm h0 (norm_nonneg _)
  linarith

/-- The Grönwall bound with zero initial value and defect `η` is `η x φ₁(ℓ x)`. -/
private lemma gronwallBound_zero_eq (ℓ η x : ℝ) (hx : 0 ≤ x) :
    gronwallBound 0 ℓ η x = η * x * phi1 (ℓ * x) := by
  rcases eq_or_lt_of_le hx with rfl | hx'
  · simp [gronwallBound_x0]
  · by_cases hℓ : ℓ = 0
    · subst hℓ
      simp [gronwallBound_K0, phi1]
    · have hne : ℓ * x ≠ 0 := mul_ne_zero hℓ hx'.ne'
      simp only [gronwallBound_of_K_ne_0 hℓ, phi1, hne, ↓reduceIte]
      field_simp
      ring

/-- **arXiv 2312.00172, Lemma 3 with `k = 0`.** Let `L` be a linear operator on matrices with
one-sided Lipschitz constant `ℓ`, i.e. `⟪L X, X⟫ ≤ ℓ ‖X‖²` (Definition 1, which is the
logarithmic norm condition for linear operators). If `y' = L y` on `[0, h]` with `y(0) = X`, then
`‖φ₀(hL) X‖ = ‖y(h)‖ ≤ φ₀(hℓ) ‖X‖ = e^{hℓ} ‖X‖` for `h ≥ 0`. -/
theorem norm_exp_le {L : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} {ℓ : ℝ}
    (hL : ∀ X : Matrix m n ℝ, ⟪L X, X⟫ ≤ ℓ * ‖X‖ ^ 2)
    {X : Matrix m n ℝ} {h : ℝ} (hh : 0 ≤ h) {y : ℝ → Matrix m n ℝ}
    (hy : ODESolution (fun _ Z => L Z) y 0 h) (hy0 : y 0 = X) :
    ‖y h‖ ≤ Real.exp (h * ℓ) * ‖X‖ := by
  have hF : IsOneSidedLipschitzField (fun _ Z => L Z) ℓ :=
    (isOneSidedLipschitzField_linear_iff (fun _ => L) ℓ).2 fun _ => hL
  have hz : ODESolution (fun _ Z => L Z) (fun _ => (0 : Matrix m n ℝ)) 0 h :=
    ⟨continuousOn_const, fun t _ => by
      simp only [map_zero]
      exact hasDerivWithinAt_const _ _ _⟩
  have key := hy.norm_sub_le_exp_of_oneSided hz hF h ⟨hh, le_rfl⟩
  simp only [sub_zero, hy0] at key
  rw [mul_comm ℓ h] at key
  exact key

/-- **arXiv 2312.00172, Lemma 3 with `k = 1`.** Let `L` have one-sided Lipschitz constant `ℓ`
(as in `norm_exp_le`). If `z' = L z + X` on `[0, h]` with `z(0) = 0`, `h > 0`, then Lemma 2 of the
paper gives `z(h) = h φ₁(hL) X`, and the bound is `‖φ₁(hL) X‖ = ‖h⁻¹ z(h)‖ ≤ φ₁(hℓ) ‖X‖`. -/
theorem norm_phi1_le {L : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} {ℓ : ℝ}
    (hL : ∀ X : Matrix m n ℝ, ⟪L X, X⟫ ≤ ℓ * ‖X‖ ^ 2)
    {X : Matrix m n ℝ} {h : ℝ} (hh : 0 < h) {z : ℝ → Matrix m n ℝ}
    (hz : ODESolution (fun _ Y => L Y + X) z 0 h) (hz0 : z 0 = 0) :
    ‖h⁻¹ • z h‖ ≤ phi1 (h * ℓ) * ‖X‖ := by
  have hF : IsOneSidedLipschitzField (fun _ Y => L Y) ℓ :=
    (isOneSidedLipschitzField_linear_iff (fun _ => L) ℓ).2 fun _ => hL
  have key := norm_sub_le_gronwallBound_of_oneSided (F := fun _ Y => L Y) (ℓ := ℓ) hF
    (y := z) (z := fun _ => (0 : Matrix m n ℝ)) (u := fun t => L (z t) + X)
    (w := fun _ => (0 : Matrix m n ℝ)) (a := 0) (b := h) (ηy := ‖X‖) (ηz := 0) (δ := 0)
    hz.cont (fun t ht => hz.deriv t ht) (fun t _ => by simp) continuousOn_const
    (fun t _ => hasDerivWithinAt_const _ _ _) (fun t _ => by simp) (by simp [hz0])
    h ⟨hh.le, le_rfl⟩
  simp only [sub_zero, add_zero] at key
  rw [gronwallBound_zero_eq ℓ ‖X‖ h hh.le] at key
  have hinv : 0 < h⁻¹ := inv_pos.2 hh
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hinv]
  calc h⁻¹ * ‖z h‖ ≤ h⁻¹ * (‖X‖ * h * phi1 (ℓ * h)) := mul_le_mul_of_nonneg_left key hinv.le
    _ = phi1 (h * ℓ) * ‖X‖ := by
      rw [mul_comm ℓ h]
      have hh1 : h⁻¹ * h = 1 := inv_mul_cancel₀ hh.ne'
      linear_combination (‖X‖ * phi1 (h * ℓ)) * hh1

/-- Non-vacuity of the hypothesis of `norm_exp_le`: `L = -id` on matrices has one-sided constant
`ℓ = -1`, since `⟪-X, X⟫ = -‖X‖²`. -/
example : ∀ X : Matrix (Fin 2) (Fin 2) ℝ,
    ⟪(-(ContinuousLinearMap.id ℝ (Matrix (Fin 2) (Fin 2) ℝ))) X, X⟫ ≤ (-1) * ‖X‖ ^ 2 := by
  intro X
  simp [inner_neg_left]

end LeanDLRA.Literature.P2312_00172
