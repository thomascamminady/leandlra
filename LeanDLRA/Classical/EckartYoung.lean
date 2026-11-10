import LeanDLRA.Matrix.Interpolation
import LeanDLRA.LinearAlgebra.SVD.Defs

/-!
# The Eckart–Young–Mirsky theorem for real matrices

For a real matrix `A ∈ ℝ^{m × n}` let `σ_i(A) := (Matrix.toEuclideanLin A).singularValues i`
(Mathlib's `LinearMap.singularValues`: the square roots of the eigenvalues of `Aᵀ A`, sorted
decreasingly, zero-indexed, and `0` for `i ≥ n`).  The theorem of Schmidt (1907),
Eckart–Young (1936) and Mirsky (1960) says that truncating the singular value decomposition is
a best rank-`r` approximation in both the Frobenius and the spectral norm:

* **(F)** every `B` with `rank B ≤ r` satisfies `‖A - B‖_F² ≥ ∑_{r ≤ i < n} σ_i(A)²`, with
  equality for `B⋆ = A V_r V_rᵀ`, where the columns of `V_r` are the top `r` eigenvectors of
  `Aᵀ A`; hence `dist_F(A, {rank ≤ r}) = (∑_{i ≥ r} σ_i(A)²)^{1/2}`;
* **(S)** every `B` with `rank B ≤ r` satisfies `σ_r(A) ≤ ‖A - B‖₂`, with equality at `B⋆`.

The case `r = 0` gives `‖A‖_F² = ∑_i σ_i(A)²` and `‖A‖₂ = σ_0(A)`.

## Proof strategy (no SVD needed)

We never construct a singular value decomposition: only the spectral theorem for the symmetric
operator `T† T`, `T = toEuclideanLin A`, enters, through its sorted orthonormal eigenbasis
`e_i` (`rightSingularVectors A`) with `T† T e_i = σ_i² e_i`.  The two basic identities are
`‖T y‖² = ∑_i σ_i² ⟪e_i, y⟫²` and `‖M‖_F² = ∑_k ‖M b_k‖²` for every orthonormal basis `b`
(with `≤` for an orthonormal family, by Bessel's inequality).

* (F), lower bound: `K = ker B` has dimension `≥ n - r`.  For an orthonormal basis `q_j` of `K`,
  `‖A - B‖_F² ≥ ∑_j ‖(A - B) q_j‖² = ∑_j ‖A q_j‖² = ∑_i σ_i² c_i` with the weights
  `c_i = ∑_j ⟪e_i, q_j⟫² ∈ [0, 1]` (Bessel) and `∑_i c_i = dim K ≥ n - r` (Parseval).  An
  elementary rearrangement inequality (`sum_Ico_le_sum_mul`, the core of Ky Fan's maximum
  principle) gives `∑_i σ_i² c_i ≥ ∑_{i ≥ r} σ_i²`.
* (S), lower bound: `ker B` and `span {e_0, …, e_r}` have dimensions adding up to more than `n`,
  so they share a unit vector `x`, and `‖(A - B) x‖² = ‖A x‖² ≥ σ_r² ‖x‖²`
  (Courant–Fischer).
* Attainment: `A - B⋆` acts as `T` on `span {e_i : i ≥ r}` and as `0` on its orthogonal
  complement.

## Main results

* `rightSingularVectors`, `topRightSingularVectors`, `truncation` (`B⋆ = A V_r V_rᵀ`),
  `rank_truncation_le`, `transpose_mul_topRightSingularVectors` (`V_rᵀ V_r = 1`);
* bridge to `Aᵀ A`: `toEuclideanLin_transpose_mul_self`,
  `transpose_mul_self_mulVec_rightSingularVectors`, `sq_singularValues_eq_eigenvalues₀`
  (`σ_i(A)² = λ_i(Aᵀ A)`);
* Frobenius norm (`open scoped LeanDLRA.Frobenius`): `sq_norm_eq_sum_sq_singularValues`,
  `sum_sq_singularValues_le_sq_norm_sub` (lower bound), `sq_norm_sub_truncation` (attainment),
  `norm_sub_truncation_le`, `infDist_setOf_rank_le` (distance to the rank-`≤ r` matrices);
* spectral norm (`LeanDLRA.Curvature.specNorm`): `singularValues_le_specNorm_sub` (lower bound),
  `specNorm_sub_truncation` (`= σ_r(A)`), `specNorm_eq_singularValues_zero`.

## Connection to dynamical low-rank approximation

* `norm_projEulerDEIM_truncation_sub_le`: the truncated SVD is a quasi-best (`κ = 1`)
  approximation, as assumed in `LeanDLRA.norm_projEulerDEIM_sub_le` (Lemma 11 of
  arXiv 2510.19518, which cites Eckart–Young for exactly this).
* `sqrt_tail_le_norm_sub`, `rank_le_of_tolerance`: the rank selected by the rank-adaptive BUG
  integrator (Ceruti–Kusch–Lubich, arXiv 2104.05247, eq. (6): the smallest `r` with
  `(∑_{i ≥ r} σ_i²)^{1/2} ≤ ϑ`) is the smallest rank of *any* matrix within `ϑ` of `Ŷ₁`, and
  `norm_sub_truncation_le_of_tail` provides the truncation hypothesis `‖Y₁ - Ŷ₁‖ ≤ ϑ`
  (`IsRankAdaptiveBUGStep.trunc`).
* `sum_tail_le_sq_norm_normal`, `sum_tail_le_sq_norm_sub_tangentProj`: the normal component
  `(I - U Uᵀ) Z (I - V Vᵀ)` of any `Z` at any point `Y = U S Vᵀ` of rank `r` is at least the
  singular-value tail `(∑_{i ≥ 2r} σ_i(Z)²)^{1/2}`; so the modelling error `ε` of the robust
  DLRA error bounds can never beat the `2r`-tail of `F(Y)`.
* `lt_rank_of_specNorm_sub_lt`: every `Y` with `‖Y - X‖₂ < σ_k(X)` has rank `> k`.  With
  `k = r - 1`, the curvature radius `ρ = σ_{r-1}(X)` of `LeanDLRA.Curvature` (the smallest
  nonzero singular value of a rank-`r` matrix `X`) is the spectral distance from `X` to the
  matrices of rank `< r`.

## References

* E. Schmidt, *Zur Theorie der linearen und nichtlinearen Integralgleichungen I*,
  Math. Ann. 63 (1907), 433–476.
* C. Eckart, G. Young, *The approximation of one matrix by another of lower rank*,
  Psychometrika 1 (1936), 211–218.
* L. Mirsky, *Symmetric gauge functions and unitarily invariant norms*,
  Quart. J. Math. 11 (1960), 50–59.
* K. Fan, *Maximum properties and inequalities for the eigenvalues of completely continuous
  operators*, Proc. Natl. Acad. Sci. USA 37 (1951), 760–766.
* G. H. Golub, C. F. Van Loan, *Matrix Computations*, 4th ed., Thm. 2.4.8.
* G. Ceruti, J. Kusch, C. Lubich, *A rank-adaptive robust integrator for dynamical low-rank
  approximation*, BIT 62 (2022), arXiv 2104.05247.

## Implementation notes

Only real matrices are treated.  We work with `Fin (finrank ℝ (EuclideanSpace ℝ n))`-indexed
eigenbases (as produced by `LinearMap.IsSymmetric.eigenvectorBasis` with `hn := rfl`, which is
also how `LinearMap.singularValues` is defined), and state the final results with
`Fintype.card n`.  The Frobenius norm is the scoped instance of `LeanDLRA.Frobenius`, the
spectral norm is `LeanDLRA.Curvature.specNorm`, so both can be used in one file.

`rightSingularVectors`, `topRightSingularVectors` and `truncation` are defined in
`LeanDLRA/LinearAlgebra/SVD/Defs.lean`.
-/

open Matrix WithLp Module Finset
open scoped RealInnerProductSpace

namespace LeanDLRA.EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-! ### Preliminaries -/

/-- Squared singular values are antitone. -/
lemma sq_singularValues_antitone {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) {i j : ℕ} (h : i ≤ j) :
    T.singularValues j ^ 2 ≤ T.singularValues i ^ 2 :=
  pow_le_pow_left₀ (T.singularValues_nonneg j) (T.singularValues_antitone h) 2

/-- Summing over the indices `i ∈ [r, d)` written as a sum over `Fin d`. -/
lemma sum_fin_ite_eq_sum_Ico (d r : ℕ) (f : ℕ → ℝ) :
    ∑ i : Fin d, (if (i : ℕ) < r then 0 else f i) = ∑ i ∈ Ico r d, f i := by
  have h := Fin.sum_univ_eq_sum_range (fun i ↦ if i < r then (0 : ℝ) else f i) d
  rw [h, Finset.sum_ite, Finset.sum_const_zero, zero_add]
  exact Finset.sum_congr (by ext i; simp; omega) fun _ _ ↦ rfl

/-- **A rearrangement inequality** (the combinatorial core of Ky Fan's maximum principle).
If `μ` is antitone and nonnegative and the weights `c_i ∈ [0, 1]`, `i < d`, have total mass at
least `d - r`, then `∑_i μ_i c_i` is at least the tail `∑_{r ≤ i < d} μ_i`. -/
theorem sum_Ico_le_sum_mul {d r : ℕ} {μ : ℕ → ℝ} (hμ : Antitone μ) (hμ0 : ∀ i, 0 ≤ μ i)
    {c : Fin d → ℝ} (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) (hc : (d : ℝ) ≤ ∑ i, c i + r) :
    ∑ i ∈ Ico r d, μ i ≤ ∑ i : Fin d, μ i * c i := by
  rcases le_or_gt d r with hdr | hrd
  · rw [Finset.Ico_eq_empty_of_le hdr, Finset.sum_empty]
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hμ0 _) (hc0 _)
  have hcard : ∑ i : Fin d, (if (i : ℕ) < r then (0 : ℝ) else 1) = d - r := by
    rw [sum_fin_ite_eq_sum_Ico d r fun _ ↦ 1]
    simp [Nat.cast_sub hrd.le]
  rw [← sum_fin_ite_eq_sum_Ico]
  have h1 : ∀ i : Fin d, μ r * (c i - if (i : ℕ) < r then 0 else 1) ≤
      μ i * c i - if (i : ℕ) < r then 0 else μ i := by
    intro i
    split_ifs with h
    · have := hμ h.le
      nlinarith [hc0 i]
    · have := hμ (not_lt.mp h)
      nlinarith [mul_nonneg (sub_nonneg.2 this) (sub_nonneg.2 (hc1 i))]
  have h2 := Finset.sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin d))) ↦ h1 i
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, hcard, Finset.sum_sub_distrib] at h2
  nlinarith [mul_nonneg (hμ0 r) (show (0 : ℝ) ≤ ∑ i, c i - (d - r) by linarith)]

omit [Fintype m] in
/-- The rank of a matrix is the dimension of the range of `toEuclideanLin`. -/
lemma rank_eq_finrank_range [Finite m] (B : Matrix m n ℝ) :
    B.rank = finrank ℝ (LinearMap.range (toEuclideanLin B)) := by
  cases nonempty_fintype m
  exact B.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun m ℝ).toBasis
    (EuclideanSpace.basisFun n ℝ).toBasis

omit [Fintype m] in
/-- Rank–nullity for `toEuclideanLin`. -/
lemma finrank_ker_add_rank [Finite m] (B : Matrix m n ℝ) :
    finrank ℝ (LinearMap.ker (toEuclideanLin B)) + B.rank = Fintype.card n := by
  rw [rank_eq_finrank_range, add_comm, LinearMap.finrank_range_add_finrank_ker,
    finrank_euclideanSpace]

omit [Fintype m] [DecidableEq n] in
/-- Subadditivity of the rank. -/
lemma rank_add_le (B C : Matrix m n ℝ) : (B + C).rank ≤ B.rank + C.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

omit [Fintype m] in
/-- The entries of `A x` are inner products with the rows of `A`. -/
lemma toEuclideanLin_apply_eq_inner (M : Matrix m n ℝ) (x : EuclideanSpace ℝ n) (i : m) :
    toEuclideanLin M x i = ⟪x, toLp 2 (M i)⟫ := by
  simp [Matrix.toLpLin_apply, mulVec, dotProduct, PiLp.inner_apply]

/-- `‖A x‖² = ∑_i ⟪x, aᵢ⟫²` over the rows `aᵢ` of `A`. -/
lemma sq_norm_toEuclideanLin (M : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    ‖toEuclideanLin M x‖ ^ 2 = ∑ i, ⟪x, toLp 2 (M i)⟫ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [toEuclideanLin_apply_eq_inner]

/-! ### The Frobenius norm as a Hilbert–Schmidt sum -/

section Frobenius

open scoped LeanDLRA.Frobenius

omit [Fintype m] [DecidableEq n] in
/-- The squared norm of a row. -/
lemma sq_norm_row (M : Matrix m n ℝ) (i : m) :
    ‖(toLp 2 (M i) : EuclideanSpace ℝ n)‖ ^ 2 = ∑ j, M i j ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp

/-- For an orthonormal family `q_k`, `∑_k ‖M q_k‖² ≤ ‖M‖_F²` (Bessel's inequality, row by
row). -/
theorem sum_sq_norm_toEuclideanLin_le (M : Matrix m n ℝ) {ι : Type*} [Fintype ι]
    {q : ι → EuclideanSpace ℝ n} (hq : Orthonormal ℝ q) :
    ∑ k, ‖toEuclideanLin M (q k)‖ ^ 2 ≤ ‖M‖ ^ 2 := by
  simp_rw [sq_norm_toEuclideanLin]
  rw [Finset.sum_comm, Frobenius.norm_sq_eq_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have h := hq.sum_inner_products_le (toLp 2 (M i)) (s := univ)
  simp only [Real.norm_eq_abs, sq_abs] at h
  rwa [sq_norm_row] at h

/-- For an orthonormal basis `b`, `‖M‖_F² = ∑_k ‖M b_k‖²`. -/
theorem sq_norm_eq_sum_sq_norm_toEuclideanLin (M : Matrix m n ℝ) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ n)) :
    ‖M‖ ^ 2 = ∑ k, ‖toEuclideanLin M (b k)‖ ^ 2 := by
  simp_rw [sq_norm_toEuclideanLin]
  rw [Finset.sum_comm, Frobenius.norm_sq_eq_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [b.sum_sq_inner_right, sq_norm_row]

end Frobenius

/-! ### Right singular vectors -/

/- `rightSingularVectors` is defined in `LeanDLRA/LinearAlgebra/SVD/Defs.lean`. -/

/-- `T† T e_i = σ_i² e_i`. -/
theorem adjoint_toEuclideanLin_rightSingularVectors (A : Matrix m n ℝ)
    (i : Fin (finrank ℝ (EuclideanSpace ℝ n))) :
    LinearMap.adjoint (toEuclideanLin A) (toEuclideanLin A (rightSingularVectors A i)) =
      (toEuclideanLin A).singularValues i ^ 2 • rightSingularVectors A i := by
  have h := (toEuclideanLin A).isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i
  rw [LinearMap.comp_apply] at h
  rw [LinearMap.sq_singularValues_fin _ rfl i, rightSingularVectors, h]
  rfl

/-- `‖A y‖² = ⟪Aᵀ A y, y⟫`. -/
lemma sq_norm_toEuclideanLin_eq_inner (A : Matrix m n ℝ) (y : EuclideanSpace ℝ n) :
    ‖toEuclideanLin A y‖ ^ 2 = ⟪LinearMap.adjoint (toEuclideanLin A) (toEuclideanLin A y), y⟫ := by
  rw [LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]

/-- **Spectral form of `‖A y‖²`**: `‖A y‖² = ∑_i σ_i(A)² ⟪e_i, y⟫²`. -/
theorem sq_norm_toEuclideanLin_apply (A : Matrix m n ℝ) (y : EuclideanSpace ℝ n) :
    ‖toEuclideanLin A y‖ ^ 2 = ∑ i : Fin (finrank ℝ (EuclideanSpace ℝ n)),
      (toEuclideanLin A).singularValues i ^ 2 * ⟪rightSingularVectors A i, y⟫ ^ 2 := by
  set T := toEuclideanLin A
  set e := rightSingularVectors A
  rw [sq_norm_toEuclideanLin_eq_inner, ← e.sum_inner_mul_inner (LinearMap.adjoint T (T y)) y]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hsymm : ⟪LinearMap.adjoint T (T y), e i⟫ = ⟪y, LinearMap.adjoint T (T (e i))⟫ := by
    rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
  rw [hsymm, adjoint_toEuclideanLin_rightSingularVectors, real_inner_smul_right,
    real_inner_comm y]
  ring

/-- `‖A e_i‖² = σ_i(A)²`. -/
theorem sq_norm_toEuclideanLin_rightSingularVectors (A : Matrix m n ℝ)
    (i : Fin (finrank ℝ (EuclideanSpace ℝ n))) :
    ‖toEuclideanLin A (rightSingularVectors A i)‖ ^ 2 =
      (toEuclideanLin A).singularValues i ^ 2 := by
  rw [sq_norm_toEuclideanLin_eq_inner, adjoint_toEuclideanLin_rightSingularVectors,
    real_inner_smul_left, real_inner_self_eq_norm_sq, (rightSingularVectors A).orthonormal.1 i]
  ring

/-! ### The bridge to the eigenvalues of `Aᵀ A` -/

section Bridge

/-- `Aᵀ A` acts as `T† T` for `T = toEuclideanLin A`. -/
theorem toEuclideanLin_transpose_mul_self (A : Matrix m n ℝ) :
    toEuclideanLin (Aᵀ * A) = LinearMap.adjoint (toEuclideanLin A) ∘ₗ toEuclideanLin A := by
  classical
  rw [toLpLin_mul_same, ← conjTranspose_eq_transpose_of_trivial,
    toEuclideanLin_conjTranspose_eq_adjoint]

/-- The right singular vectors are eigenvectors of the matrix `Aᵀ A`:
`(Aᵀ A) v_i = σ_i(A)² v_i`. -/
theorem transpose_mul_self_mulVec_rightSingularVectors (A : Matrix m n ℝ)
    (i : Fin (finrank ℝ (EuclideanSpace ℝ n))) :
    (Aᵀ * A) *ᵥ ofLp (rightSingularVectors A i) =
      (toEuclideanLin A).singularValues i ^ 2 • ofLp (rightSingularVectors A i) := by
  have h := congrArg ofLp (adjoint_toEuclideanLin_rightSingularVectors A i)
  rw [← LinearMap.comp_apply, ← toEuclideanLin_transpose_mul_self, Matrix.toLpLin_apply] at h
  simpa using h

/-- Eigenvalues of equal symmetric operators agree at equal positions. -/
lemma eigenvalues_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {S₁ S₂ : E →ₗ[ℝ] E} (h : S₁ = S₂) (h₁ : S₁.IsSymmetric)
    (h₂ : S₂.IsSymmetric) {d₁ d₂ : ℕ} (hn₁ : finrank ℝ E = d₁) (hn₂ : finrank ℝ E = d₂)
    (i : Fin d₁) (j : Fin d₂) (hij : (i : ℕ) = j) :
    h₁.eigenvalues hn₁ i = h₂.eigenvalues hn₂ j := by
  subst h hn₁ hn₂
  rw [Fin.ext hij]

/-- **Bridge lemma**: `σ_i(A)² = λ_i(Aᵀ A)`, the `i`-th largest eigenvalue of the symmetric
matrix `Aᵀ A` (Mathlib's `Matrix.IsHermitian.eigenvalues₀`). -/
theorem sq_singularValues_eq_eigenvalues₀ (A : Matrix m n ℝ) (hA : (Aᵀ * A).IsHermitian)
    (i : Fin (Fintype.card n)) :
    (toEuclideanLin A).singularValues i ^ 2 = hA.eigenvalues₀ i := by
  have hi : (i : ℕ) < finrank ℝ (EuclideanSpace ℝ n) := by
    rw [finrank_euclideanSpace]; exact i.isLt
  rw [LinearMap.sq_singularValues_of_lt _ rfl hi, IsHermitian.eigenvalues₀]
  exact eigenvalues_congr (toEuclideanLin_transpose_mul_self A).symm _ _ _ _ _ _ rfl

end Bridge

/-! ### The truncation `B⋆ = A V_r V_rᵀ` -/

/- `topRightSingularVectors` and `truncation` are defined in
`LeanDLRA/LinearAlgebra/SVD/Defs.lean`. -/

/-- `V_r` has orthonormal columns. -/
theorem transpose_mul_topRightSingularVectors (A : Matrix m n ℝ) (r : ℕ) :
    (topRightSingularVectors A r)ᵀ * topRightSingularVectors A r = 1 := by
  ext i i'
  have h := orthonormal_iff_ite.mp (rightSingularVectors A).orthonormal i i'
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h
  simp only [Matrix.mul_apply, transpose_apply, topRightSingularVectors, Matrix.one_apply,
    Subtype.ext_iff]
  rw [← h]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

/-- The truncation has rank at most `r`. -/
theorem rank_truncation_le (A : Matrix m n ℝ) (r : ℕ) : (truncation A r).rank ≤ r := by
  refine (rank_mul_le_right _ _).trans ((rank_le_card_height _).trans ?_)
  refine (Fintype.card_le_of_injective (fun i ↦ (⟨i.1, i.2⟩ : Fin r)) fun a b h ↦ ?_).trans
    (Fintype.card_fin r).le
  exact Subtype.ext (Fin.ext (by simpa using congrArg Fin.val h))

/-- `B⋆ x = A (∑_{i < r} ⟪e_i, x⟫ e_i)`. -/
theorem toEuclideanLin_truncation_apply (A : Matrix m n ℝ) (r : ℕ) (x : EuclideanSpace ℝ n) :
    toEuclideanLin (truncation A r) x = toEuclideanLin A
      (∑ i ∈ univ.filter fun i : Fin (finrank ℝ (EuclideanSpace ℝ n)) ↦ (i : ℕ) < r,
        ⟪rightSingularVectors A i, x⟫ • rightSingularVectors A i) := by
  rw [truncation, Matrix.mul_assoc, toLpLin_mul_same, LinearMap.comp_apply]
  congr 1
  ext j
  rw [Matrix.toLpLin_apply]
  simp only [ofLp_sum, ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mulVec, dotProduct, Matrix.mul_apply, transpose_apply, topRightSingularVectors,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Finset.sum_filter]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_filter,
    Finset.sum_subtype (p := fun i : Fin (finrank ℝ (EuclideanSpace ℝ n)) ↦ (i : ℕ) < r)
    (univ.filter fun i : Fin (finrank ℝ (EuclideanSpace ℝ n)) ↦ (i : ℕ) < r) (fun i ↦ by simp)]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring

/-- The coefficients of the projected vector. -/
lemma inner_rightSingularVectors_sum (A : Matrix m n ℝ) (r : ℕ) (x : EuclideanSpace ℝ n)
    (k : Fin (finrank ℝ (EuclideanSpace ℝ n))) :
    ⟪rightSingularVectors A k,
        ∑ i ∈ univ.filter fun i : Fin (finrank ℝ (EuclideanSpace ℝ n)) ↦ (i : ℕ) < r,
          ⟪rightSingularVectors A i, x⟫ • rightSingularVectors A i⟫ =
      if (k : ℕ) < r then ⟪rightSingularVectors A k, x⟫ else 0 := by
  simp_rw [inner_sum, real_inner_smul_right,
    orthonormal_iff_ite.mp (rightSingularVectors A).orthonormal k, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/-- `‖(A - B⋆) x‖² = ∑_{i ≥ r} σ_i(A)² ⟪e_i, x⟫²`. -/
theorem sq_norm_toEuclideanLin_sub_truncation_apply (A : Matrix m n ℝ) (r : ℕ)
    (x : EuclideanSpace ℝ n) :
    ‖toEuclideanLin (A - truncation A r) x‖ ^ 2 = ∑ k : Fin (finrank ℝ (EuclideanSpace ℝ n)),
      if (k : ℕ) < r then 0 else
        (toEuclideanLin A).singularValues k ^ 2 * ⟪rightSingularVectors A k, x⟫ ^ 2 := by
  rw [map_sub, LinearMap.sub_apply, toEuclideanLin_truncation_apply, ← map_sub,
    sq_norm_toEuclideanLin_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [inner_sub_right, inner_rightSingularVectors_sum]
  split_ifs <;> simp

/-- `(A - B⋆) e_j = 0` for `j < r` and `= A e_j` otherwise. -/
lemma toEuclideanLin_sub_truncation_rightSingularVectors (A : Matrix m n ℝ) (r : ℕ)
    (j : Fin (finrank ℝ (EuclideanSpace ℝ n))) :
    toEuclideanLin (A - truncation A r) (rightSingularVectors A j) =
      if (j : ℕ) < r then 0 else toEuclideanLin A (rightSingularVectors A j) := by
  rw [map_sub, LinearMap.sub_apply, toEuclideanLin_truncation_apply]
  have hP : (∑ i ∈ univ.filter fun i : Fin (finrank ℝ (EuclideanSpace ℝ n)) ↦ (i : ℕ) < r,
      ⟪rightSingularVectors A i, rightSingularVectors A j⟫ • rightSingularVectors A i) =
        if (j : ℕ) < r then rightSingularVectors A j else 0 := by
    simp_rw [orthonormal_iff_ite.mp (rightSingularVectors A).orthonormal, ite_smul, one_smul,
      zero_smul]
    rw [Finset.sum_ite_eq']
    simp
  rw [hP]
  split_ifs <;> simp

/-- The truncation of order `0` is the zero matrix. -/
theorem truncation_zero (A : Matrix m n ℝ) : truncation A 0 = 0 := by
  apply (toEuclideanLin (m := m) (n := n) (𝕜 := ℝ)).injective
  ext1 x
  rw [toEuclideanLin_truncation_apply]
  simp

/-! ### Eckart–Young–Mirsky in the Frobenius norm -/

section Frobenius

open scoped LeanDLRA.Frobenius

/-- **`‖A‖_F² = ∑_i σ_i(A)²`**. -/
theorem sq_norm_eq_sum_sq_singularValues (A : Matrix m n ℝ) :
    ‖A‖ ^ 2 = ∑ i ∈ range (Fintype.card n), (toEuclideanLin A).singularValues i ^ 2 := by
  rw [sq_norm_eq_sum_sq_norm_toEuclideanLin A (rightSingularVectors A)]
  simp_rw [sq_norm_toEuclideanLin_rightSingularVectors]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ (toEuclideanLin A).singularValues i ^ 2),
    finrank_euclideanSpace]

/-- **Eckart–Young–Mirsky, Frobenius norm, lower bound**: every `B` of rank `≤ r` satisfies
`∑_{r ≤ i < n} σ_i(A)² ≤ ‖A - B‖_F²`. -/
theorem sum_sq_singularValues_le_sq_norm_sub (A B : Matrix m n ℝ) {r : ℕ} (hB : B.rank ≤ r) :
    ∑ i ∈ Ico r (Fintype.card n), (toEuclideanLin A).singularValues i ^ 2 ≤ ‖A - B‖ ^ 2 := by
  set K := LinearMap.ker (toEuclideanLin B)
  let q := stdOrthonormalBasis ℝ K
  have hq : Orthonormal ℝ fun j ↦ (q j : EuclideanSpace ℝ n) :=
    Orthonormal.comp_linearIsometry q.orthonormal K.subtypeₗᵢ
  have hq1 : ∀ j, ‖(q j : EuclideanSpace ℝ n)‖ = 1 := fun j ↦ hq.1 j
  have hTq : ∀ j, toEuclideanLin (A - B) (q j) = toEuclideanLin A (q j) := fun j ↦ by
    rw [map_sub, LinearMap.sub_apply, LinearMap.mem_ker.mp (q j).2, sub_zero]
  have h1 : ∑ j, ‖toEuclideanLin A (q j)‖ ^ 2 ≤ ‖A - B‖ ^ 2 :=
    (Finset.sum_congr rfl fun j _ ↦ by rw [hTq]).trans_le
      (sum_sq_norm_toEuclideanLin_le (A - B) hq)
  simp_rw [sq_norm_toEuclideanLin_apply] at h1
  rw [Finset.sum_comm] at h1
  simp_rw [← Finset.mul_sum] at h1
  refine le_trans ?_ h1
  rw [← finrank_euclideanSpace (𝕜 := ℝ) (ι := n)]
  refine sum_Ico_le_sum_mul (μ := fun i ↦ (toEuclideanLin A).singularValues i ^ 2)
    (fun i j h ↦ sq_singularValues_antitone _ h) (fun i ↦ sq_nonneg _)
    (fun i ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _) (fun i ↦ ?_) ?_
  · have h := hq.sum_inner_products_le (rightSingularVectors A i) (s := univ)
    simp only [Real.norm_eq_abs, sq_abs, (rightSingularVectors A).orthonormal.1 i, one_pow] at h
    exact le_of_eq_of_le (Finset.sum_congr rfl fun j _ ↦ by rw [real_inner_comm]) h
  · have hsum : ∑ i, ∑ j, ⟪rightSingularVectors A i, (q j : EuclideanSpace ℝ n)⟫ ^ 2 =
        finrank ℝ K := by
      rw [Finset.sum_comm]
      simp_rw [(rightSingularVectors A).sum_sq_inner_right, hq1, one_pow]
      simp
    rw [hsum]
    have hK : finrank ℝ K + B.rank = finrank ℝ (EuclideanSpace ℝ n) := by
      rw [finrank_euclideanSpace]; exact finrank_ker_add_rank B
    have : finrank ℝ (EuclideanSpace ℝ n) ≤ finrank ℝ K + r := by omega
    exact_mod_cast this

/-- **Eckart–Young–Mirsky, Frobenius norm, attainment**:
`‖A - A V_r V_rᵀ‖_F² = ∑_{r ≤ i < n} σ_i(A)²`. -/
theorem sq_norm_sub_truncation (A : Matrix m n ℝ) (r : ℕ) :
    ‖A - truncation A r‖ ^ 2 =
      ∑ i ∈ Ico r (Fintype.card n), (toEuclideanLin A).singularValues i ^ 2 := by
  rw [sq_norm_eq_sum_sq_norm_toEuclideanLin _ (rightSingularVectors A), ← finrank_euclideanSpace
    (𝕜 := ℝ) (ι := n), ← sum_fin_ite_eq_sum_Ico]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [toEuclideanLin_sub_truncation_rightSingularVectors]
  split_ifs
  · simp
  · exact sq_norm_toEuclideanLin_rightSingularVectors A j

/-- **Eckart–Young–Mirsky (Frobenius norm)**: the truncated SVD is a best approximation of rank
`≤ r`. -/
theorem norm_sub_truncation_le (A : Matrix m n ℝ) {r : ℕ} {B : Matrix m n ℝ} (hB : B.rank ≤ r) :
    ‖A - truncation A r‖ ≤ ‖A - B‖ := by
  have h := sum_sq_singularValues_le_sq_norm_sub A B hB
  rw [← sq_norm_sub_truncation] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- `‖A - B⋆‖_F = (∑_{r ≤ i < n} σ_i(A)²)^{1/2}`. -/
theorem norm_sub_truncation (A : Matrix m n ℝ) (r : ℕ) :
    ‖A - truncation A r‖ =
      √(∑ i ∈ Ico r (Fintype.card n), (toEuclideanLin A).singularValues i ^ 2) := by
  rw [← sq_norm_sub_truncation, Real.sqrt_sq (norm_nonneg _)]

/-- `(∑_{r ≤ i < n} σ_i(A)²)^{1/2} ≤ ‖A - B‖_F` for `rank B ≤ r`. -/
theorem sqrt_sum_sq_singularValues_le_norm_sub (A B : Matrix m n ℝ) {r : ℕ} (hB : B.rank ≤ r) :
    √(∑ i ∈ Ico r (Fintype.card n), (toEuclideanLin A).singularValues i ^ 2) ≤ ‖A - B‖ := by
  rw [← norm_sub_truncation]
  exact norm_sub_truncation_le A hB

/-- **Eckart–Young–Mirsky, distance form**: in the Frobenius metric, the distance from `A` to the
set of matrices of rank `≤ r` is `(∑_{r ≤ i < n} σ_i(A)²)^{1/2}`. -/
theorem infDist_setOf_rank_le (A : Matrix m n ℝ) (r : ℕ) :
    Metric.infDist A {B : Matrix m n ℝ | B.rank ≤ r} =
      √(∑ i ∈ Ico r (Fintype.card n), (toEuclideanLin A).singularValues i ^ 2) := by
  refine le_antisymm ?_ ?_
  · rw [← norm_sub_truncation, ← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem (rank_truncation_le A r)
  · refine (Metric.le_infDist ⟨0, by simp [Matrix.rank_zero]⟩).2 fun B hB ↦ ?_
    rw [dist_eq_norm]
    exact sqrt_sum_sq_singularValues_le_norm_sub A B hB

end Frobenius

/-! ### Eckart–Young–Mirsky in the spectral norm -/

section Spectral

open Curvature

/-- **Eckart–Young–Mirsky, spectral norm, lower bound**: every `B` of rank `≤ r` satisfies
`σ_r(A) ≤ ‖A - B‖₂`. -/
theorem singularValues_le_specNorm_sub (A B : Matrix m n ℝ) {r : ℕ} (hB : B.rank ≤ r) :
    (toEuclideanLin A).singularValues r ≤ specNorm (A - B) := by
  set T := toEuclideanLin A
  set e := rightSingularVectors A
  rcases le_or_gt (finrank ℝ (EuclideanSpace ℝ n)) r with hdr | hrd
  · rw [LinearMap.singularValues_of_finrank_le _ hdr]
    exact specNorm_nonneg _
  set K := LinearMap.ker (toEuclideanLin B)
  set W := Submodule.span ℝ (Set.range (e ∘ Fin.castLE hrd))
  have hW : finrank ℝ W = r + 1 := by
    rw [finrank_span_eq_card (e.orthonormal.linearIndependent.comp _ (Fin.castLE_injective _)),
      Fintype.card_fin]
  have hK : finrank ℝ K + B.rank = Fintype.card n := finrank_ker_add_rank B
  have hKW : finrank ℝ ↥(K ⊓ W) ≠ 0 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq K W
    have h2 := Submodule.finrank_le (K ⊔ W)
    rw [finrank_euclideanSpace] at h2
    omega
  obtain ⟨x, hx, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (p := K ⊓ W) fun h ↦ hKW (by rw [h, finrank_bot])
  obtain ⟨hxK, hxW⟩ := Submodule.mem_inf.mp hx
  have hcoef : ∀ k : Fin (finrank ℝ (EuclideanSpace ℝ n)), r < (k : ℕ) → ⟪e k, x⟫ = 0 := by
    intro k hk
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hxW
    rw [inner_sum]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [real_inner_smul_right, Function.comp_apply, e.orthonormal.inner_eq_zero, mul_zero]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castLE] at this
    omega
  have hlow : T.singularValues r ^ 2 * ‖x‖ ^ 2 ≤ ‖T x‖ ^ 2 := by
    rw [sq_norm_toEuclideanLin_apply, ← e.sum_sq_inner_right x, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ ↦ ?_
    rcases le_or_gt (k : ℕ) r with hk | hk
    · exact mul_le_mul_of_nonneg_right (sq_singularValues_antitone T hk) (sq_nonneg _)
    · rw [hcoef k hk]
      simp
  have hTx : toEuclideanLin (A - B) x = T x := by
    rw [map_sub, LinearMap.sub_apply, LinearMap.mem_ker.mp hxK, sub_zero]
  have hup := norm_toEuclideanLin_le (A - B) x
  rw [hTx] at hup
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hsq : (T.singularValues r * ‖x‖) ^ 2 ≤ (specNorm (A - B) * ‖x‖) ^ 2 := by
    rw [mul_pow]
    exact hlow.trans (pow_le_pow_left₀ (norm_nonneg _) hup 2)
  have := (pow_le_pow_iff_left₀ (mul_nonneg (T.singularValues_nonneg r) hxpos.le)
    (mul_nonneg (specNorm_nonneg _) hxpos.le) two_ne_zero).mp hsq
  exact le_of_mul_le_mul_right this hxpos

/-- **Eckart–Young–Mirsky, spectral norm, attainment (upper bound)**:
`‖A - A V_r V_rᵀ‖₂ ≤ σ_r(A)`. -/
theorem specNorm_sub_truncation_le (A : Matrix m n ℝ) (r : ℕ) :
    specNorm (A - truncation A r) ≤ (toEuclideanLin A).singularValues r := by
  refine specNorm_le_of ((toEuclideanLin A).singularValues_nonneg r) fun x ↦ ?_
  have h : ‖toEuclideanLin (A - truncation A r) x‖ ^ 2 ≤
      ((toEuclideanLin A).singularValues r * ‖x‖) ^ 2 := by
    rw [sq_norm_toEuclideanLin_sub_truncation_apply, mul_pow,
      ← (rightSingularVectors A).sum_sq_inner_right x, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ ↦ ?_
    split_ifs with hk
    · positivity
    · exact mul_le_mul_of_nonneg_right
        (sq_singularValues_antitone (toEuclideanLin A) (not_lt.mp hk)) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg ((toEuclideanLin A).singularValues_nonneg r) (norm_nonneg _)) two_ne_zero).mp h

/-- **Eckart–Young–Mirsky (spectral norm)**: `‖A - A V_r V_rᵀ‖₂ = σ_r(A)`. -/
theorem specNorm_sub_truncation (A : Matrix m n ℝ) (r : ℕ) :
    specNorm (A - truncation A r) = (toEuclideanLin A).singularValues r :=
  le_antisymm (specNorm_sub_truncation_le A r)
    (singularValues_le_specNorm_sub A _ (rank_truncation_le A r))

/-- The truncated SVD is a best approximation of rank `≤ r` in the spectral norm. -/
theorem specNorm_sub_truncation_le_specNorm_sub (A : Matrix m n ℝ) {r : ℕ} {B : Matrix m n ℝ}
    (hB : B.rank ≤ r) : specNorm (A - truncation A r) ≤ specNorm (A - B) := by
  rw [specNorm_sub_truncation]
  exact singularValues_le_specNorm_sub A B hB

/-- **`‖A‖₂ = σ_0(A)`**. -/
theorem specNorm_eq_singularValues_zero (A : Matrix m n ℝ) :
    specNorm A = (toEuclideanLin A).singularValues 0 := by
  simpa [truncation_zero] using specNorm_sub_truncation A 0

end Spectral

/-! ### Connection to dynamical low-rank approximation -/

section DLRA

open scoped LeanDLRA.Frobenius

/-- **Quasi-optimality of the truncated SVD in projected Euler-DEIM.**  Lemma 11 of
arXiv 2510.19518 (`LeanDLRA.norm_projEulerDEIM_sub_le`) assumes a retraction `T` with
`‖T x - x‖ ≤ κ ‖z - x‖` for all `z ∈ ℳ`; by Eckart–Young–Mirsky the truncated SVD satisfies this
with `κ = 1` on `ℳ = {rank ≤ r}`, so the local error of one projected Euler-DEIM step with SVD
truncation is at most `d + 2 (e + h C ε)`. -/
theorem norm_projEulerDEIM_truncation_sub_le {r : ℕ}
    {Pob P : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hP : IsObliqueProj Pob P) (hP0 : P ≠ 0)
    {C ε h e d : ℝ} (hC : ‖Pob‖ ≤ C) (hh : 0 ≤ h) {Y V W Z : Matrix m n ℝ}
    (hv : ‖V - P V‖ ≤ ε) (hE : ‖W - (Y + h • V)‖ ≤ e) (hZ : Z.rank ≤ r) (hd : ‖Z - W‖ ≤ d) :
    ‖truncation (Y + h • Pob V) r - W‖ ≤ d + 2 * (e + h * (C * ε)) := by
  have hT : ∀ (X : Matrix m n ℝ), ∀ Z ∈ {Z : Matrix m n ℝ | Z.rank ≤ r},
      ‖truncation X r - X‖ ≤ 1 * ‖Z - X‖ := fun X Z hZ ↦ by
    rw [one_mul, norm_sub_rev, norm_sub_rev Z]
    exact norm_sub_truncation_le X hZ
  have := norm_projEulerDEIM_sub_le (T := fun X ↦ truncation X r) hT zero_le_one hP hP0 hC hh hv
    hE (show Z ∈ {Z : Matrix m n ℝ | Z.rank ≤ r} from hZ) hd
  linarith

/-- **Truncation to a tolerance** (rank-adaptive BUG, Ceruti–Kusch–Lubich eq. (6)): if the
singular-value tail beyond `r` is at most `ϑ`, the truncation `Y₁ = A V_r V_rᵀ` satisfies the
truncation hypothesis `‖Y₁ - Ŷ₁‖ ≤ ϑ` of `IsRankAdaptiveBUGStep` (with `Ŷ₁ = A`). -/
theorem norm_sub_truncation_le_of_tail (A : Matrix m n ℝ) {r : ℕ} {ϑ : ℝ}
    (h : √(∑ i ∈ Ico r (Fintype.card n), (toEuclideanLin A).singularValues i ^ 2) ≤ ϑ) :
    ‖truncation A r - A‖ ≤ ϑ := by
  rwa [norm_sub_rev, norm_sub_truncation]

/-- The singular-value tail of `A` beyond the rank of `B` is a lower bound for `‖A - B‖_F`. -/
theorem sqrt_tail_le_norm_sub (A B : Matrix m n ℝ) :
    √(∑ i ∈ Ico B.rank (Fintype.card n), (toEuclideanLin A).singularValues i ^ 2) ≤ ‖A - B‖ :=
  sqrt_sum_sq_singularValues_le_norm_sub A B le_rfl

/-- **Optimality of the rank-adaptive truncation rank.**  If `r` is the rank selected by the
tolerance criterion, i.e. every `s < r` has tail `> ϑ`, then every matrix within Frobenius
distance `ϑ` of `A` has rank at least `r`: no approximation of lower rank meets the tolerance. -/
theorem rank_le_of_tolerance (A : Matrix m n ℝ) {r : ℕ} {ϑ : ℝ}
    (hr : ∀ s < r, ϑ < √(∑ i ∈ Ico s (Fintype.card n), (toEuclideanLin A).singularValues i ^ 2))
    {B : Matrix m n ℝ} (hB : ‖A - B‖ ≤ ϑ) : r ≤ B.rank := by
  by_contra hlt
  have := hr B.rank (not_le.mp hlt)
  linarith [sqrt_tail_le_norm_sub A B]

/-- **The normal component is bounded below by a singular-value tail.**  For arbitrary `U`
(`k` columns) and `V` (`l` columns), the normal component `(I - U Uᵀ) Z (I - V Vᵀ)` satisfies
`‖(I - U Uᵀ) Z (I - V Vᵀ)‖_F² ≥ ∑_{i ≥ k + l} σ_i(Z)²`, because `Z` minus its normal component
has rank `≤ k + l`.  In DLRA (`k = l = r`, `Z = F(Y)` at `Y = U S Vᵀ`) this says that the
modelling error `ε ≥ ‖(I - U Uᵀ) F(Y) (I - V Vᵀ)‖_F` of the robust error bounds is at least the
`2r`-tail of the singular values of `F(Y)`. -/
theorem sum_tail_le_sq_norm_normal [DecidableEq m] {k l : Type*} [Fintype k] [Fintype l]
    (Z : Matrix m n ℝ) (U : Matrix m k ℝ) (V : Matrix n l ℝ) :
    ∑ i ∈ Ico (Fintype.card k + Fintype.card l) (Fintype.card n),
        (toEuclideanLin Z).singularValues i ^ 2 ≤ ‖(1 - U * Uᵀ) * Z * (1 - V * Vᵀ)‖ ^ 2 := by
  set B := U * (Uᵀ * Z) + (1 - U * Uᵀ) * Z * V * Vᵀ
  have hB : B.rank ≤ Fintype.card k + Fintype.card l :=
    (rank_add_le _ _).trans (add_le_add ((rank_mul_le_left _ _).trans (rank_le_card_width _))
      ((rank_mul_le_right _ _).trans (rank_le_card_height _)))
  have hZB : (1 - U * Uᵀ) * Z * (1 - V * Vᵀ) = Z - B := by
    simp only [B, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc]
    abel
  rw [hZB]
  exact sum_sq_singularValues_le_sq_norm_sub Z B hB

/-- The tangent-space form of `sum_tail_le_sq_norm_normal`: `‖Z - P(Y) Z‖_F² ≥ ∑_{i ≥ k + l}
σ_i(Z)²` for the tangent-space projector `P(Y) = tangentProj U V`. -/
theorem sum_tail_le_sq_norm_sub_tangentProj {k l : Type*} [Fintype k]
    [Fintype l] (Z : Matrix m n ℝ) (U : Matrix m k ℝ) (V : Matrix n l ℝ) :
    ∑ i ∈ Ico (Fintype.card k + Fintype.card l) (Fintype.card n),
        (toEuclideanLin Z).singularValues i ^ 2 ≤ ‖Z - tangentProj U V Z‖ ^ 2 := by
  classical
  have h := tangentProj_add_normal U V Z
  rw [← eq_sub_iff_add_eq'] at h
  rw [← h]
  exact sum_tail_le_sq_norm_normal Z U V

end DLRA

/-- **Rank cannot drop within the spectral ball of radius `σ_k`.**  If `‖Y - X‖₂ < σ_k(X)` then
`rank Y > k`.  With `k = r - 1` and `X` of rank `r`, this identifies the curvature radius
`ρ = σ_{r-1}(X)` of `LeanDLRA.Curvature` (the smallest nonzero singular value) with the spectral
distance from `X` to the matrices of rank `< r`, which is why Koch–Lubich's smallness condition
`‖Y - X‖ ≤ ρ/8` keeps `Y` of full rank `r`. -/
theorem lt_rank_of_specNorm_sub_lt (X Y : Matrix m n ℝ) {k : ℕ}
    (h : Curvature.specNorm (X - Y) < (toEuclideanLin X).singularValues k) : k < Y.rank := by
  by_contra hle
  exact (not_le.mpr h) (singularValues_le_specNorm_sub X Y (not_lt.mp hle))

end LeanDLRA.EckartYoung
