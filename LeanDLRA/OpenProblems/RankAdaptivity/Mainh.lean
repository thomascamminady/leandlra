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
import LeanDLRA.Randomized.RandomizedBUG
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Foundations.Projector
import LeanDLRA.Foundations.Galerkin

/-!
# Open problems OP-RA-27, OP-RA-28, OP-RA-29, OP-RA-32, OP-RA-37
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

/-- **OP-RA-27: enrichment by the top singular vector of `E` itself can gain nothing.**  There
are `U`, `E` and a top left singular vector `w` of `E` (`‖Eᵀ w‖ = ‖E‖₂`) that already lies in
`span U` while `(I - U Uᵀ) E ≠ 0`: enriching by `w` leaves `‖(I - P_U) E‖` unchanged, in contrast
to the top singular vector of the residual (`exists_enrich_top_singular`). -/
theorem enrich_top_singular_of_E_no_gain :
    ∃ (U w : Matrix (Fin 2) (Fin 1) ℝ) (Em : Matrix (Fin 2) (Fin 2) ℝ),
      Uᵀ * U = 1 ∧ wᵀ * w = 1 ∧ ‖Emᵀ * w‖ = specNorm Em ∧ U * Uᵀ * w = w ∧
        (1 - U * Uᵀ) * Em ≠ 0 := by
  have hspec : specNorm (diagonal ![2, 1] : Matrix (Fin 2) (Fin 2) ℝ) = 2 := by
    rw [specNorm_eq_l2, l2_opNorm_diagonal]
    norm_num [Pi.norm_def, Finset.sup, Fin.univ_succ]
  refine ⟨(!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ), (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ),
    diagonal ![2, 1], ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · rw [hspec]
    have h2 : (diagonal ![2, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)
        = (!![2; 0] : Matrix (Fin 2) (Fin 1) ℝ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
    rw [h2]
    have hsq : ‖(!![2; 0] : Matrix (Fin 2) (Fin 1) ℝ)‖ ^ 2 = 2 ^ 2 := by
      rw [LeanDLRA.Frobenius.norm_sq_eq_sum]
      simp [Fin.sum_univ_succ]
    exact (pow_left_inj₀ (norm_nonneg _) (by norm_num) two_ne_zero).1 hsq
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ,
          Function.swap, Matrix.vecHead, Matrix.vecTail]
  · intro h
    have := congrFun (congrFun h 1) 1
    simp [Matrix.mul_apply, Matrix.one_apply,
      Matrix.diagonal] at this

/-- **OP-RA-28 (b): the domain-decomposition identity holds up to the projection error.**  For
orthonormal `U₀`, `‖U₀S₀V₀ᵀ - U₀S₀V₀ᵀ V̂V̂ᵀ‖ = ‖(I - V̂V̂ᵀ) V₀ S₀ᵀ‖`, so `Û Ŝ V̂ᵀ = U₀S₀V₀ᵀ` holds
exactly iff `range(V₀ S₀ᵀ) ⊆ range V̂`, and otherwise only up to the truncation tolerance. -/
theorem norm_sub_rightProj_eq [DecidableEq n] {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] {U₀ : Matrix m k ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (S₀ : Matrix k k ℝ)
    (V₀ : Matrix n k ℝ) (Va : Matrix n l ℝ) :
    ‖U₀ * S₀ * V₀ᵀ - U₀ * S₀ * V₀ᵀ * (Va * Vaᵀ)‖ = ‖(1 - Va * Vaᵀ) * (V₀ * S₀ᵀ)‖ := by
  have hP : (Va * Vaᵀ)ᵀ = Va * Vaᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hL : U₀ * S₀ * V₀ᵀ - U₀ * S₀ * V₀ᵀ * (Va * Vaᵀ)
      = U₀ * (S₀ * V₀ᵀ * (1 - Va * Vaᵀ)) := by
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  have hR : (S₀ * V₀ᵀ * (1 - Va * Vaᵀ)) = ((1 - Va * Vaᵀ) * (V₀ * S₀ᵀ))ᵀ := by
    simp [Matrix.transpose_mul, Matrix.transpose_sub, hP]
  rw [hL, LeanDLRA.Frobenius.norm_mul_of_orthonormal hU₀, hR, LeanDLRA.Frobenius.norm_transpose]

/-- **OP-RA-29 (iii), hard thresholding: exact on rank-`r` data above the threshold.**  If
`rank A ≤ r` and `σ_{r-1}(A) > α ≥ 0` (0-based), the hard-thresholding rule keeps exactly `r`
singular values and reproduces `A`. -/
theorem hardThreshold_exact [DecidableEq n] {r : ℕ} (hr : 0 < r) (A : Matrix m n ℝ)
    (hA : A.rank ≤ r) {α : ℝ} (hα : 0 ≤ α)
    (hσ : α < (toEuclideanLin A).singularValues (r - 1)) :
    ((range (Fintype.card n)).filter fun i => α < (toEuclideanLin A).singularValues i).card = r ∧
      truncation A r = A := by
  set T := toEuclideanLin A with hTdef
  have hzero : ∀ i, A.rank ≤ i → T.singularValues i = 0 := fun i hi =>
    (T.singularValues_eq_zero_iff_le_finrank_range).2 (by
      rw [hTdef, ← rank_eq_finrank_range A]; exact hi)
  have hpos : r - 1 < A.rank := by
    by_contra hcon
    have h0 := hzero (r - 1) (by omega)
    linarith
  have hrk : A.rank ≤ Fintype.card n := Matrix.rank_le_card_width A
  have hcard : r ≤ Fintype.card n := by omega
  refine ⟨?_, (LeanDLRA.RandomizedBUG.truncation_eq_self_iff A r).2 hA⟩
  have hfilt : ((range (Fintype.card n)).filter fun i => α < T.singularValues i) = range r := by
    ext i
    simp only [mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, hi⟩
      by_contra hir
      have h0 := hzero i (by omega)
      linarith
    · intro hi
      exact ⟨by omega, lt_of_lt_of_le hσ (T.singularValues_antitone (by omega))⟩
  rw [hfilt, Finset.card_range]

/-- **OP-RA-29 (iii), soft thresholding: bias `α √r`.**  Shrinking all `r` retained singular
values of `U diag(σ) Vᵀ` by `α` changes the matrix by exactly `α √r` in the Frobenius norm,
whatever the data. -/
theorem softThreshold_bias {k : Type*} [Fintype k] [DecidableEq k] {U : Matrix m k ℝ}
    {V : Matrix n k ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (σ : k → ℝ) {α : ℝ} (hα : 0 ≤ α) :
    ‖U * diagonal σ * Vᵀ - U * diagonal (fun i => σ i - α) * Vᵀ‖ = α * √(Fintype.card k) := by
  have hdiag : ∀ j, ∑ i, V i j ^ 2 = 1 := fun j => by
    have h := congrFun (congrFun hV j) j
    simpa [Matrix.mul_apply, sq] using h
  have hVn : ‖V‖ ^ 2 = (Fintype.card k : ℝ) := by
    rw [LeanDLRA.Frobenius.norm_sq_eq_sum, Finset.sum_comm]
    simp [hdiag]
  have hD : diagonal σ - diagonal (fun i => σ i - α) = α • (1 : Matrix k k ℝ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have hsub : U * diagonal σ * Vᵀ - U * diagonal (fun i => σ i - α) * Vᵀ = α • (U * Vᵀ) := by
    calc U * diagonal σ * Vᵀ - U * diagonal (fun i => σ i - α) * Vᵀ
        = U * (diagonal σ - diagonal (fun i => σ i - α)) * Vᵀ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul]
      _ = α • (U * Vᵀ) := by rw [hD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [hsub, norm_smul, Real.norm_of_nonneg hα, LeanDLRA.Frobenius.norm_mul_of_orthonormal hU,
    LeanDLRA.Frobenius.norm_transpose, ← hVn, Real.sqrt_sq (norm_nonneg _)]

set_option linter.unusedDecidableInType false in
/-- **OP-RA-32: SVD truncation makes the rank-adaptive step `L²`-stable.**  For a dissipative
field (`⟪F(t, Y), Y⟫ ≤ 0`), the matrix rank-adaptive BUG step with SVD truncation
`Y₁ = T_{r₁}(Û Ŝ(t₁) V̂ᵀ)` satisfies `‖Y₁‖ ≤ ‖Y₀‖`: the augmented S-step starts at `Y₀`
(`start_eq`) and does not increase the norm, and `truncation` is nonexpansive.  This discharges
the truncation hypothesis of `augmentedBug_norm_le_of_dissipative` for SVD truncation. -/
theorem rankAdaptive_svd_norm_le [DecidableEq m] [DecidableEq n] {r : ℕ} {k k' : Type*}
    [Fintype k] [Fintype k'] [DecidableEq k] [DecidableEq k']
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {ϑ t₀ t₁ : ℝ} {U₀ : Matrix m (Fin r) ℝ}
    {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {Ua : Matrix m k ℝ}
    {Va : Matrix n k' ℝ} {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ}
    {Sa : ℝ → Matrix k k' ℝ} {Y₁ : Matrix m n ℝ}
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁) {r₁ : ℕ}
    (hY₁ : Y₁ = truncation (Ua * Sa t₁ * Vaᵀ) r₁) (hdiss : ∀ t Y, ⟪F t Y, Y⟫ ≤ 0)
    (h01 : t₀ ≤ t₁) :
    ‖Y₁‖ ≤ ‖U₀ * S₀ * V₀ᵀ‖ := by
  have hP : IsOrthProj (leftProj Ua * rightProj Va : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
    (isOrthProj_leftProj hs.orthUa).mul (isOrthProj_rightProj hs.orthVa)
      (leftProj_rightProj_comm Ua Va)
  have hYS := odeSolution_sField hs.sSol
  have h0 : (leftProj Ua * rightProj Va : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (Ua * Sa t₀ * Vaᵀ)
      = Ua * Sa t₀ * Vaᵀ := by
    rw [hs.start_eq]
    change leftProj Ua (rightProj Va (U₀ * S₀ * V₀ᵀ)) = U₀ * S₀ * V₀ᵀ
    rw [hs.aug_right, hs.aug_left]
  have hF : ∀ t x, (leftProj Ua * rightProj Va : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) x = x →
      ⟪F t x, x⟫ ≤ 0 :=
    fun t x _ => hdiss t x
  have hgal := hYS.galerkin_norm_le' hP h0 hF t₁ ⟨h01, le_rfl⟩
  rw [hs.start_eq] at hgal
  have htr : ‖truncation (Ua * Sa t₁ * Vaᵀ) r₁‖ ≤ ‖Ua * Sa t₁ * Vaᵀ‖ := by
    have hT : truncation (Ua * Sa t₁ * Vaᵀ) r₁
        = rightProj (topRightSingularVectors (Ua * Sa t₁ * Vaᵀ) r₁) (Ua * Sa t₁ * Vaᵀ) := by
      rw [rightProj_apply]; rfl
    rw [hT]
    exact (isOrthProj_rightProj (transpose_mul_topRightSingularVectors _ r₁)).norm_le _
  rw [hY₁]
  exact htr.trans hgal

omit [Fintype m] in
/-- The rank of a finite sum is at most the sum of the ranks. -/
private theorem rank_sum_le_aux {ι : Type*} (s : Finset ι) (Z : ι → Matrix m n ℝ) :
    (∑ i ∈ s, Z i).rank ≤ ∑ i ∈ s, (Z i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (LeanDLRA.EckartYoung.rank_add_le _ _).trans (add_le_add_right ih _)

/-- **OP-RA-37 (iv): `ε`-ranks of superpositions are subadditive.**  For matrices `Xᵢ` (e.g. proton
beams) with tolerances `εᵢ ≥ 0`, `rank_{∑ εᵢ}(∑ Xᵢ) ≤ ∑ rank_{εᵢ}(Xᵢ)`: simulating the beams
jointly never needs more rank than separately.  (Rank counts without truncation, (ii)–(iii), are
`Matrix.rank_add_le`.) -/
theorem epsRank_sum_le {ι : Type*} (s : Finset ι) (X : ι → Matrix m n ℝ) (ε : ι → ℝ)
    (hε : ∀ i ∈ s, 0 ≤ ε i) :
    epsRank (∑ i ∈ s, ε i) (∑ i ∈ s, X i) ≤ ∑ i ∈ s, epsRank (ε i) (X i) := by
  have key : ∀ i ∈ s, ∃ Z : Matrix m n ℝ, Z.rank ≤ epsRank (ε i) (X i) ∧ ‖X i - Z‖ ≤ ε i :=
    fun i hi => exists_epsRank_approx (hε i hi)
  choose! Z hZr hZn using key
  have hrank : (∑ i ∈ s, Z i).rank ≤ ∑ i ∈ s, epsRank (ε i) (X i) :=
    (rank_sum_le_aux s Z).trans (Finset.sum_le_sum hZr)
  refine epsRank_le_of_norm_sub_le hrank ?_
  rw [← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum hZn)

end Matrices

end LeanDLRA.OpenProblems.RankAdaptivity
