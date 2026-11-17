import LeanDLRA.OpenProblems.RankAdaptivity.MainDefs
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Integrators.ParallelBUG
import LeanDLRA.Integrators.Matrix.BUG
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Classical.WeylSingular
import LeanDLRA.Classical.BestApproximation
import LeanDLRA.Stability.Conservation
import LeanDLRA.Training.Descent
import LeanDLRA.Foundations.OneSided
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Classical.EckartYoung

/-!
# Open problems OP-RA-18, OP-RA-19, OP-RA-20, OP-RA-26
-/

open Set Finset Matrix
open scoped RealInnerProductSpace

namespace LeanDLRA.OpenProblems.RankAdaptivity

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Abstract

section Counting

end Counting

section Matrices

open scoped LeanDLRA.Frobenius
open EckartYoung WeylSingular Curvature MatrixBUG

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Right multiplication by a matrix with orthonormal columns does not increase the Frobenius
norm. -/
private theorem frob_mul_isometry_right {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq c] (A : Matrix a b ℝ) {V : Matrix b c ℝ} (hV : Vᵀ * V = 1) :
    ‖A * V‖ ≤ ‖A‖ :=
  (frob_mul_le' A V).trans
    (mul_le_of_le_one_right (norm_nonneg A) (specNorm_le_one_of_orthonormal hV))

/-- **OP-RA-18: the step-rejection indicator is a certified lower bound.**  For orthonormal
`Ũ ⊥ U₀` and `Ṽ ⊥ V₀`, `η = ‖Ũᵀ X Ṽ‖ ≤ ‖(I - U₀U₀ᵀ) X (I - V₀V₀ᵀ)‖` (with `X = F(Y₀)` the right side
is bounded by `ε`); equality fails for doubly-normal parts outside `span Ũ ⊗ span Ṽ`
(`doublyNormal_invisible`). -/
theorem norm_eta_le_norm_normal [DecidableEq m] [DecidableEq n] {k k' p q : Type*}
    [Fintype k] [Fintype k'] [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    {U₀ : Matrix m k ℝ} {V₀ : Matrix n k' ℝ} {Ut : Matrix m p ℝ} {Vt : Matrix n q ℝ}
    (hUt : Utᵀ * Ut = 1) (hVt : Vtᵀ * Vt = 1) (hU : Utᵀ * U₀ = 0) (hV : Vtᵀ * V₀ = 0)
    (X : Matrix m n ℝ) :
    ‖Utᵀ * X * Vt‖ ≤ ‖(1 - U₀ * U₀ᵀ) * X * (1 - V₀ * V₀ᵀ)‖ := by
  have hL : Utᵀ * (1 - U₀ * U₀ᵀ) = Utᵀ := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hU, Matrix.zero_mul, sub_zero]
  have hV' : V₀ᵀ * Vt = 0 := by
    have h := congrArg Matrix.transpose hV
    simpa [Matrix.transpose_mul] using h
  have hR : (1 - V₀ * V₀ᵀ) * Vt = Vt := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV', Matrix.mul_zero, sub_zero]
  have e : Utᵀ * ((1 - U₀ * U₀ᵀ) * X * (1 - V₀ * V₀ᵀ)) * Vt = Utᵀ * X * Vt := by
    rw [show Utᵀ * ((1 - U₀ * U₀ᵀ) * X * (1 - V₀ * V₀ᵀ)) * Vt =
        (Utᵀ * (1 - U₀ * U₀ᵀ)) * X * ((1 - V₀ * V₀ᵀ) * Vt) by simp only [Matrix.mul_assoc],
      hL, hR]
  rw [← e]
  refine (frob_mul_isometry_right _ hVt).trans ?_
  have hT : ‖Utᵀ * ((1 - U₀ * U₀ᵀ) * X * (1 - V₀ * V₀ᵀ))‖ =
      ‖((1 - U₀ * U₀ᵀ) * X * (1 - V₀ * V₀ᵀ))ᵀ * Ut‖ := by
    rw [← frobenius_norm_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hT]
  exact (frob_mul_isometry_right _ hUt).trans (le_of_eq (frobenius_norm_transpose _))

/-- **OP-RA-19 (b): right truncation does not increase left-weighted energies.**  For an
orthogonal projector `Q` (`Qᵀ = Q = Q²`, e.g. `V Vᵀ`) and any left weight `D`,
`‖D v Q‖ ≤ ‖D v‖`; this is the missing step of the energy-stable multiplicative scheme. -/
theorem norm_weighted_rightTrunc_le {p : Type*} [Fintype p] (D : Matrix p m ℝ)
    (v : Matrix m n ℝ) (Q : Matrix n n ℝ) (hQs : Qᵀ = Q) (hQi : Q * Q = Q) :
    ‖D * v * Q‖ ≤ ‖D * v‖ :=
  (IsOrthProjMat.mk hQs hQi).norm_mul_le' (D * v)

/-- The rank-one truncation of `diag(2, 1)`: its right singular vector for the top singular
value `2` is `± e₁` (the eigenvalue `1` is excluded because `σ₀ ≥ ‖A e₁‖ = 2`), so
`truncation A 1 = diag(2, 0)`. -/
private theorem truncation_diag_two_one (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A = !![2, 0; 0, 1]) : truncation A 1 = !![2, 0; 0, 0] := by
  have hAA : Aᵀ * A = !![4, 0; 0, 1] := by
    rw [hA]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have hs : toEuclideanLin A (EuclideanSpace.single 0 1) = EuclideanSpace.single 0 2 := by
    rw [hA]
    ext i
    fin_cases i <;> simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  have hσ : 2 ≤ (toEuclideanLin A).singularValues 0 := by
    rw [← specNorm_eq_singularValues_zero]
    have h := norm_toEuclideanLin_le A (EuclideanSpace.single 0 1)
    rw [hs] at h
    simpa using h
  let i0 : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) := ⟨0, by simp⟩
  let j0 : {i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) // (i : ℕ) < 1} :=
    ⟨i0, Nat.zero_lt_one⟩
  have hP : topRightSingularVectors A 1 * (topRightSingularVectors A 1)ᵀ =
      Matrix.of fun a b => rightSingularVectors A i0 a * rightSingularVectors A i0 b := by
    ext a b
    rw [Matrix.mul_apply, Fintype.sum_eq_single j0]
    · rfl
    · intro x hx
      exact absurd (Subtype.ext (Fin.ext (by have := x.2; change (x.1 : ℕ) = 0; omega))) hx
  have hE := transpose_mul_self_mulVec_rightSingularVectors A i0
  rw [hAA] at hE
  have hn : rightSingularVectors A i0 0 ^ 2 + rightSingularVectors A i0 1 ^ 2 = 1 := by
    have h1 := (rightSingularVectors A).orthonormal.1 i0
    have h2 : ‖rightSingularVectors A i0‖ ^ 2 =
        rightSingularVectors A i0 0 ^ 2 + rightSingularVectors A i0 1 ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp [Real.norm_eq_abs, sq_abs]
    rw [h1] at h2
    linarith
  have h1 := congrFun hE 1
  simp only [mulVec, dotProduct, Fin.isValue, of_apply, cons_val', cons_val_fin_one,
    cons_val_one, Fin.sum_univ_two, cons_val_zero, zero_mul, one_mul, zero_add, Pi.smul_apply,
    smul_eq_mul] at h1
  have hσ' : 2 ≤ (toEuclideanLin A).singularValues ↑i0 := hσ
  have hs2 : 4 ≤ (toEuclideanLin A).singularValues ↑i0 ^ 2 := by nlinarith
  have hx1 : rightSingularVectors A i0 1 = 0 := by
    have hm : ((toEuclideanLin A).singularValues ↑i0 ^ 2 - 1) *
        rightSingularVectors A i0 1 = 0 := by
      linear_combination (-1 : ℝ) * h1
    rcases mul_eq_zero.1 hm with h | h
    · linarith
    · exact h
  have hx00 : rightSingularVectors A i0 0 * rightSingularVectors A i0 0 = 1 := by
    rw [hx1] at hn
    nlinarith
  unfold truncation
  rw [Matrix.mul_assoc, hP]
  generalize rightSingularVectors A i0 = e at hx1 hx00 ⊢
  subst hA
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx1, hx00]

/-- **OP-RA-19 (c): two-sided mixed terms are not contracted by truncation.**  For
`Z = diag(2, 1)`, `C = [[1, 1], [0, 0]]`, `D = [[1, 0], [-2, 0]]`: `‖C Z D‖ = 0` but
`‖C T₁(Z) D‖ = 2`. -/
theorem mixed_term_counterexample :
    ‖(!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![2, 0; 0, 1] * !![1, 0; -2, 0]‖ = 0 ∧
      ‖(!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
        truncation (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) 1 * !![1, 0; -2, 0]‖ = 2 := by
  have hT := truncation_diag_two_one (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) rfl
  rw [hT]
  refine ⟨?_, ?_⟩
  · rw [norm_eq_zero]
    ext i j
    fin_cases i
    all_goals fin_cases j
    all_goals norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · have hp : (!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![2, 0; 0, 0] *
        !![1, 0; -2, 0] = !![2, 0; 0, 0] := by
      ext i j
      fin_cases i
      all_goals fin_cases j
      all_goals norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hp]
    have h : ‖(!![2, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)‖ ^ 2 = 4 := by
      rw [frob_sq]
      norm_num [Fin.sum_univ_two]
    nlinarith [norm_nonneg (!![2, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)]

/-- **OP-RA-19 (c), positive surrogate.**  If `‖Z v‖ ≥ ρ ‖v‖` (`σ_min(Z) ≥ ρ > 0`), then
`‖C Z D‖_F ≤ (‖C Z‖_F² + ‖Z D‖_F²) / (2 ρ)`. -/
theorem norm_mixed_le_of_sigmaMin [DecidableEq m] {p q : Type*} [Fintype p] [Fintype q]
    (C : Matrix p m ℝ) (Z : Matrix m m ℝ) (D : Matrix m q ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hZ : ∀ v : EuclideanSpace ℝ m, ρ * ‖v‖ ≤ ‖toEuclideanLin Z v‖) :
    ‖C * Z * D‖ ≤ (‖C * Z‖ ^ 2 + ‖Z * D‖ ^ 2) / (2 * ρ) := by
  classical
  have hunit : IsUnit Z.det := isUnit_det_of_bounded_below hρ hZ
  have hZinv : Z * Z⁻¹ = 1 := Matrix.mul_nonsing_inv Z hunit
  have hZinv' : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z hunit
  have hcomp : ∀ x : EuclideanSpace ℝ m, toEuclideanLin Z (toEuclideanLin Z⁻¹ x) = x := fun x => by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, hZinv]
    simp
  have hinv : specNorm Z⁻¹ ≤ ρ⁻¹ := by
    refine specNorm_le_of (inv_nonneg.2 hρ.le) fun x => ?_
    have h := hZ (toEuclideanLin Z⁻¹ x)
    rw [hcomp x] at h
    calc ‖toEuclideanLin Z⁻¹ x‖ = ρ⁻¹ * (ρ * ‖toEuclideanLin Z⁻¹ x‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ hρ.ne', one_mul]
      _ ≤ ρ⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hρ.le)
  have hCZD : C * Z * D = C * Z * Z⁻¹ * (Z * D) := by
    rw [Matrix.mul_assoc (C * Z) Z⁻¹ (Z * D), ← Matrix.mul_assoc Z⁻¹ Z D, hZinv', Matrix.one_mul]
  have h1 : ‖C * Z * D‖ ≤ ‖C * Z * Z⁻¹‖ * ‖Z * D‖ := by
    rw [hCZD]
    exact (frob_mul_le' _ _).trans (mul_le_mul_of_nonneg_left (specNorm_le_frob _) (norm_nonneg _))
  have h2 : ‖C * Z * Z⁻¹‖ ≤ ‖C * Z‖ * ρ⁻¹ :=
    (frob_mul_le' _ _).trans (mul_le_mul_of_nonneg_left hinv (norm_nonneg _))
  have h3 : ‖C * Z * D‖ ≤ ‖C * Z‖ * ρ⁻¹ * ‖Z * D‖ :=
    h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
  have hρi : ρ⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ.ne'
  have key : ‖C * Z‖ * ρ⁻¹ * ‖Z * D‖ * (2 * ρ) = 2 * ‖C * Z‖ * ‖Z * D‖ := by
    linear_combination (2 * ‖C * Z‖ * ‖Z * D‖) * hρi
  have hfin : ‖C * Z‖ * ρ⁻¹ * ‖Z * D‖ ≤ (‖C * Z‖ ^ 2 + ‖Z * D‖ ^ 2) / (2 * ρ) := by
    rw [le_div_iff₀ (mul_pos two_pos hρ)]
    nlinarith [sq_nonneg (‖C * Z‖ - ‖Z * D‖)]
  exact h3.trans hfin

/-- **OP-RA-20 (iv): diffusive scaling forces numerical rank one.**  If the kinetic remainder
satisfies `g_ε = -w bᵀ + O(ε)`, i.e. `‖g_ε + w bᵀ‖ ≤ C ε`, then the tolerance rule at `C ε`
selects rank `≤ 1`.  (The asymptotic-preserving analysis of the integrator itself needs the
kinetic PDE and is not stated.) -/
theorem epsRank_le_one_of_near_rankOne {w : Matrix m (Fin 1) ℝ} {b : Matrix n (Fin 1) ℝ} {C : ℝ}
    (hC : 0 ≤ C) {g : ℝ → Matrix m n ℝ} (hg : ∀ ε > 0, ‖g ε + w * bᵀ‖ ≤ C * ε) :
    ∀ ε > 0, epsRank (C * ε) (g ε) ≤ 1 := by
  have _ := hC
  intro ε hε
  apply epsRank_le_of_distLR_le
  have hrank : (-(w * bᵀ)).rank ≤ 1 := by
    rw [← Matrix.neg_mul]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))
  refine (distLR_le_norm_sub hrank).trans ?_
  rw [sub_neg_eq_add]
  exact hg ε hε

/-- **OP-RA-26 (refuted): augmented Galerkin spaces need not beat the tangent projector.**  The
claim `‖(1 - P̂Q̂) Z‖ ≤ ‖(1 - P(Y)) Z‖` for `range Û ⊇ range U`, `range V̂ ⊇ range V` is false:
for `U = V = Û = V̂ = e₁` and `Z = e₁ e₂ᵀ`, `P(Y) Z = Z` but `P̂ Q̂ Z = 0`.  The correct monotone
quantity is the doubly-normal part (`norm_normal_le_of_le`). -/
theorem augmentedGalerkin_not_le_tangent :
    ∃ (U V Ua Va : Matrix (Fin 2) (Fin 1) ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ Uaᵀ * Ua = 1 ∧ Vaᵀ * Va = 1 ∧ Ua * Uaᵀ * U = U ∧
        Va * Vaᵀ * V = V ∧ ¬ ‖Z - Ua * Uaᵀ * Z * (Va * Vaᵀ)‖ ≤ ‖Z - tangentProj U V Z‖ := by
  have hU1 : (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) =
      1 := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  have hA : (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, 1] := by
    ext i j
    fin_cases i
    fin_cases j
    all_goals norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  have hB : (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) * (!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ) =
      !![0, 1; 0, 0] := by
    ext i j
    fin_cases i
    all_goals fin_cases j
    all_goals norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  have hZV : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) =
      0 := by
    ext i j
    fin_cases i
    all_goals fin_cases j
    all_goals norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  have hPZ : (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) * (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ *
      (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 0, 0] := by
    rw [Matrix.mul_assoc, hA, hB]
  refine ⟨!![1; 0], !![1; 0], !![1; 0], !![1; 0], !![0, 1; 0, 0], hU1, hU1, hU1, hU1, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, hU1, Matrix.mul_one]
  · rw [Matrix.mul_assoc, hU1, Matrix.mul_one]
  · rw [tangentProj_apply, hPZ, hZV]
    simp only [Matrix.zero_mul, add_zero, sub_zero]
    rw [← Matrix.mul_assoc, hZV, Matrix.zero_mul, sub_zero, sub_self, norm_zero]
    intro h
    have h0 : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) = 0 := norm_le_zero_iff.mp h
    have := congrFun (congrFun h0 0) 1
    simp at this

end Matrices

end LeanDLRA.OpenProblems.RankAdaptivity
