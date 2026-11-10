import LeanDLRA.Classical.CourantFischer
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.LinearAlgebra.SVD.Defs

/-!
# The thin singular value decomposition

Let `T : E →ₗ[𝕜] F` be a linear map between finite-dimensional inner product spaces over
`𝕜 = ℝ` or `ℂ`, with singular values `σ₀ ≥ σ₁ ≥ ⋯` (Mathlib's `LinearMap.singularValues`: the square
roots of the eigenvalues of `T† T`, sorted decreasingly, `0`-indexed, `σᵢ > 0` exactly for
`i < r := dim range T`).  This file constructs the singular vectors and proves the existence of the
**thin (compact) singular value decomposition**

    T x = ∑_{i < r} σᵢ ⟪vᵢ, x⟫ uᵢ,        (vᵢ)_{i<r}, (uᵢ)_{i<r} orthonormal,

and, for real matrices `A ∈ ℝ^{m × n}` of rank `r`,

    A = U diag(σ) Vᵀ,   Uᵀ U = 1,  Vᵀ V = 1,  σ₀ ≥ ⋯ ≥ σ_{r-1} > 0,
    σᵢ = (toEuclideanLin A).singularValues i.

It also identifies the smallest singular value as the best lower bound of `T`, the quantity that
appears as `σ_min(S) ≥ ρ` in LeanDLRA's curvature estimates.  Mathlib has the singular values but
no singular vectors and no SVD (as of this toolchain).

The singular vectors are defined in `LeanDLRA/LinearAlgebra/SVD/Defs.lean`:
`LinearMap.rightSingularBasis` (an orthonormal eigenbasis `e₀, …, e_{d-1}` of `T† T` with
`T† T eᵢ = σᵢ² eᵢ`, `d = dim E`; it is the eigenbasis Mathlib uses to define
`LinearMap.singularValues`), `LinearMap.rightSingularVectors` (`vᵢ = eᵢ` for `i < r`) and
`LinearMap.leftSingularVectors` (`uᵢ = σᵢ⁻¹ T vᵢ` for `i < r`).

## Main results

* `LinearMap.orthonormal_rightSingularVectors`, `LinearMap.orthonormal_leftSingularVectors`,
  `LinearMap.apply_rightSingularVectors` (`T vᵢ = σᵢ uᵢ`),
  `LinearMap.adjoint_apply_leftSingularVectors` (`T† uᵢ = σᵢ vᵢ`),
  `LinearMap.apply_eq_sum` (**thin SVD of a linear map**: `T x = ∑_{i<r} σᵢ ⟪vᵢ, x⟫ uᵢ`);
* `LinearMap.singularValues_mul_norm_le`: `σ_{d-1}(T) ‖x‖ ≤ ‖T x‖`;
  `LinearMap.forall_mul_norm_le_iff`: for `d > 0`, `(∀ x, ρ ‖x‖ ≤ ‖T x‖) ↔ ρ ≤ σ_{d-1}(T)`;
* `LinearMap.singularValues_mul_norm_le_of_mem_orthogonal`: on `(ker T)ᗮ`,
  `σ_{r-1}(T) ‖y‖ ≤ ‖T y‖`;
* `LeanDLRA.SVD.exists_svd` (**thin SVD of a real matrix**), with the matrix action
  `LeanDLRA.SVD.toEuclideanLin_ofCols_mul_diagonal_mul_transpose`;
* `LeanDLRA.SVD.forall_mul_norm_le_iff`, `LeanDLRA.SVD.forall_mul_norm_le_iff_fin`: for a square
  `S ∈ ℝ^{k × k}`, `k > 0`: `(∀ v, ρ ‖v‖ ≤ ‖S v‖) ↔ ρ ≤ σ_{k-1}(S)` (false for `k = 0`, see the
  example at the end of that section);
* `LeanDLRA.SVD.singularValues_mul_norm_le_of_eq_mul`: for **every** orthonormal factorisation
  `X = U S Vᵀ` of a rank-`r` matrix with `r` columns, `σ_{r-1}(X) ‖w‖ ≤ ‖S w‖`.

## Connection to dynamical low-rank approximation

`LeanDLRA.Curvature` proves the curvature estimates of Koch–Lubich for `X = U S Vᵀ` *under the
hypothesis* `σ_min(S) ≥ ρ > 0` (`koch_lubich_normal`, `koch_lubich_tangent`), or for a given
SVD `X = U diag(σ) Vᵀ` with `σᵢ ≥ ρ` (`koch_lubich_normal_svd`, `koch_lubich_tangent_svd`).  This
file discharges these hypotheses for every matrix of rank exactly `r`, with the optimal
`ρ = σ_{r-1}(X)` (`σ_r(X)` in the paper's `1`-based indexing):

* `LeanDLRA.SVD.exists_svd_bounded_below`: every `X ∈ ℳ_r` has an SVD satisfying the hypotheses of
  `koch_lubich_normal_svd` / `koch_lubich_tangent_svd` with `ρ = σ_{r-1}(X)`, and
  `LeanDLRA.SVD.singularValues_pred_rank_pos` gives `ρ > 0`;
* `LeanDLRA.SVD.koch_lubich_normal_of_rank`, `LeanDLRA.SVD.koch_lubich_tangent_of_rank`:
  the curvature bounds as unconditional statements about every `X ∈ ℳ_r` (the tangent bound for
  *any* orthonormal factorisation `X = U S Vᵀ`);
* `LeanDLRA.SVD.rank_eq_iff_exists_factor`: `ℳ_r = {U S Vᵀ : Uᵀ U = 1, Vᵀ V = 1, S invertible}`,
  the representation of the rank-`r` manifold used by all DLRA integrators (KL07, §2);
* `LeanDLRA.SVD.exists_ginv`: every `X ∈ ℳ_r` has a reflexive generalized inverse `G = V S⁻¹ Uᵀ`
  with `‖G‖₂ ≤ σ_{r-1}(X)⁻¹`, the operator through which the curvature enters the error analysis.

## Implementation notes

The right singular vectors are the eigenvectors produced by
`LinearMap.IsSymmetric.eigenvectorBasis` for `T† T` with `hn := rfl`, which is exactly how
`LinearMap.singularValues` is defined, so `T† T eᵢ = σᵢ² eᵢ` holds by `sq_singularValues_fin`
without any reindexing.  The lower bounds use the eigen-span bounds of
`LeanDLRA.Classical.CourantFischer` (`le_re_inner_of_repr_eq_zero`).  Matrices are built from
column families with `LeanDLRA.ofCols` (`Matrix/Orthonormal.lean`).  The matrix results are stated
for real matrices only; the operator results hold over any `RCLike` field.

## References

* E. Schmidt, *Zur Theorie der linearen und nichtlinearen Integralgleichungen I*,
  Math. Ann. 63 (1907), 433–476.
* G. H. Golub, C. F. Van Loan, *Matrix Computations*, 4th ed., JHU Press 2013, Thm. 2.4.1.
* S. Axler, *Linear Algebra Done Right*, 4th ed., Springer 2024, §7.E (7.70, 7.75).
* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., CUP 2013, Thm. 7.3.2.
* O. Koch, C. Lubich, *Dynamical low-rank approximation*, SIAM J. Matrix Anal. Appl. 29 (2007),
  434–454, §2 and Lemma 4.2.

## Tags

singular value decomposition, SVD, singular vectors, smallest singular value, low-rank manifold
-/

open Module Submodule
open scoped InnerProductSpace ComplexConjugate

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

/-- `T† T eᵢ = σᵢ² eᵢ`. -/
theorem adjoint_apply_rightSingularBasis (i : Fin (finrank 𝕜 E)) :
    adjoint T (T (T.rightSingularBasis i)) =
      ((T.singularValues i ^ 2 : ℝ) : 𝕜) • T.rightSingularBasis i := by
  have h := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i
  rw [LinearMap.comp_apply] at h
  rw [T.sq_singularValues_fin rfl i, rightSingularBasis, h]

/-- The images `T eᵢ` are orthogonal: `⟪T eᵢ, T eⱼ⟫ = δᵢⱼ σᵢ²`. -/
theorem inner_apply_rightSingularBasis (i j : Fin (finrank 𝕜 E)) :
    ⟪T (T.rightSingularBasis i), T (T.rightSingularBasis j)⟫_𝕜 =
      if i = j then ((T.singularValues i ^ 2 : ℝ) : 𝕜) else 0 := by
  rw [← adjoint_inner_left, adjoint_apply_rightSingularBasis, inner_smul_left,
    orthonormal_iff_ite.mp (T.rightSingularBasis).orthonormal, RCLike.conj_ofReal]
  split_ifs <;> simp

/-- `‖T eᵢ‖ = σᵢ`. -/
theorem norm_apply_rightSingularBasis (i : Fin (finrank 𝕜 E)) :
    ‖T (T.rightSingularBasis i)‖ = T.singularValues i := by
  have h := T.inner_apply_rightSingularBasis i i
  simp only [↓reduceIte, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖T (T.rightSingularBasis i)‖ ^ 2 = T.singularValues i ^ 2 := by
    exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (T.singularValues_nonneg _) two_ne_zero).mp h2

/-- `T eᵢ = 0` for `i ≥ dim range T`. -/
theorem apply_rightSingularBasis_eq_zero {i : Fin (finrank 𝕜 E)}
    (hi : finrank 𝕜 (range T) ≤ i) : T (T.rightSingularBasis i) = 0 := by
  rw [← norm_eq_zero, norm_apply_rightSingularBasis,
    T.singularValues_eq_zero_iff_le_finrank_range]
  exact hi

/-- The first `r = dim range T` singular values are positive. -/
theorem singularValues_pos (i : Fin (finrank 𝕜 (range T))) : 0 < T.singularValues i :=
  T.singularValues_pos_iff_lt_finrank_range.mpr i.isLt

/-- The right singular vectors are orthonormal. -/
theorem orthonormal_rightSingularVectors : Orthonormal 𝕜 T.rightSingularVectors :=
  (T.rightSingularBasis).orthonormal.comp _ (Fin.castLE_injective _)

/-- `T vᵢ = σᵢ uᵢ`. -/
theorem apply_rightSingularVectors (i : Fin (finrank 𝕜 (range T))) :
    T (T.rightSingularVectors i) = ((T.singularValues i : ℝ) : 𝕜) • T.leftSingularVectors i := by
  have h : ((T.singularValues i : ℝ) : 𝕜) ≠ 0 := by
    exact_mod_cast (T.singularValues_pos i).ne'
  rw [leftSingularVectors, smul_smul, mul_inv_cancel₀ h, one_smul]

/-- `T† uᵢ = σᵢ vᵢ`: the left singular vectors are the eigenvectors of `T T†`. -/
theorem adjoint_apply_leftSingularVectors (i : Fin (finrank 𝕜 (range T))) :
    adjoint T (T.leftSingularVectors i) =
      ((T.singularValues i : ℝ) : 𝕜) • T.rightSingularVectors i := by
  have h : ((T.singularValues i : ℝ) : 𝕜) ≠ 0 := by
    exact_mod_cast (T.singularValues_pos i).ne'
  rw [leftSingularVectors, map_smul, rightSingularVectors, adjoint_apply_rightSingularBasis,
    smul_smul, Fin.val_castLE]
  congr 1
  push_cast
  field_simp

/-- The left singular vectors are orthonormal. -/
theorem orthonormal_leftSingularVectors : Orthonormal 𝕜 T.leftSingularVectors := by
  rw [orthonormal_iff_ite]
  intro i j
  have hi : ((T.singularValues i : ℝ) : 𝕜) ≠ 0 := by exact_mod_cast (T.singularValues_pos i).ne'
  simp only [leftSingularVectors, inner_smul_left, inner_smul_right, rightSingularVectors,
    inner_apply_rightSingularBasis, Fin.castLE_inj, RCLike.conj_ofReal, map_inv₀]
  split_ifs with h
  · subst h
    simp only [Fin.val_castLE]
    push_cast
    field_simp
  · simp

/-- **Thin singular value decomposition of a linear map**:
`T x = ∑_{i < r} σᵢ ⟪vᵢ, x⟫ uᵢ`, `r = dim range T`. -/
theorem apply_eq_sum (x : E) :
    T x = ∑ i : Fin (finrank 𝕜 (range T)), ((T.singularValues i : ℝ) : 𝕜) •
      ⟪T.rightSingularVectors i, x⟫_𝕜 • T.leftSingularVectors i := by
  have h1 : ∀ i : Fin (finrank 𝕜 (range T)), ((T.singularValues i : ℝ) : 𝕜) •
      ⟪T.rightSingularVectors i, x⟫_𝕜 • T.leftSingularVectors i =
      ⟪T.rightSingularVectors i, x⟫_𝕜 • T (T.rightSingularVectors i) := by
    intro i
    rw [apply_rightSingularVectors, smul_comm]
  simp_rw [h1]
  set e := T.rightSingularBasis
  let emb : Fin (finrank 𝕜 (range T)) ↪ Fin (finrank 𝕜 E) :=
    ⟨Fin.castLE T.finrank_range_le_finrank, Fin.castLE_injective _⟩
  calc T x = ∑ k, ⟪e k, x⟫_𝕜 • T (e k) := by
        conv_lhs => rw [← e.sum_repr' x]
        simp [map_sum, map_smul]
    _ = ∑ k ∈ Finset.univ.map emb, ⟪e k, x⟫_𝕜 • T (e k) := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_).symm
        have hk' : finrank 𝕜 (range T) ≤ k := by
          by_contra h
          exact hk (Finset.mem_map.mpr ⟨⟨k, not_le.mp h⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        rw [apply_rightSingularBasis_eq_zero T hk', smul_zero]
    _ = _ := Finset.sum_map _ _ _

/-- `‖T x‖² = re ⟪T† T x, x⟫`. -/
theorem sq_norm_apply (x : E) : ‖T x‖ ^ 2 = RCLike.re ⟪(adjoint T ∘ₗ T) x, x⟫_𝕜 := by
  rw [comp_apply, adjoint_inner_left, inner_self_eq_norm_sq]

/-- The smallest singular value bounds `T` from below: `σ_{d-1}(T) ‖x‖ ≤ ‖T x‖`, `d = dim E`.
(For `d = 0` both sides vanish.) -/
theorem singularValues_mul_norm_le (x : E) :
    T.singularValues (finrank 𝕜 E - 1) * ‖x‖ ≤ ‖T x‖ := by
  rcases Nat.eq_zero_or_pos (finrank 𝕜 E) with hd | hd
  · rw [T.singularValues_of_finrank_le (by omega), zero_mul]
    exact norm_nonneg _
  set k : Fin (finrank 𝕜 E) := ⟨finrank 𝕜 E - 1, by omega⟩
  have h := T.isSymmetric_adjoint_comp_self.le_re_inner_of_repr_eq_zero rfl k (x := x)
    fun i hi => absurd hi (not_lt.mpr (Fin.le_def.mpr (by simp only [k]; omega)))
  rw [← T.sq_singularValues_fin rfl k, ← sq_norm_apply] at h
  have h' : (T.singularValues (finrank 𝕜 E - 1) * ‖x‖) ^ 2 ≤ ‖T x‖ ^ 2 := by
    rw [mul_pow]; exact h
  exact (pow_le_pow_iff_left₀ (mul_nonneg (T.singularValues_nonneg _) (norm_nonneg _))
    (norm_nonneg _) two_ne_zero).mp h'

/-- On the orthogonal complement of the kernel, `σ_{r-1}(T) ‖y‖ ≤ ‖T y‖` with
`r = dim range T`. -/
theorem singularValues_mul_norm_le_of_mem_orthogonal {y : E} (hy : y ∈ (ker T)ᗮ) :
    T.singularValues (finrank 𝕜 (range T) - 1) * ‖y‖ ≤ ‖T y‖ := by
  rcases Nat.eq_zero_or_pos (finrank 𝕜 (range T)) with hr | hr
  · rw [hr, Nat.zero_sub, ← hr, T.singularValues_finrank_range_self, zero_mul]
    exact norm_nonneg _
  have hrd := T.finrank_range_le_finrank
  set k : Fin (finrank 𝕜 E) := ⟨finrank 𝕜 (range T) - 1, by omega⟩
  have h := T.isSymmetric_adjoint_comp_self.le_re_inner_of_repr_eq_zero rfl k (x := y) ?_
  · rw [← T.sq_singularValues_fin rfl k, ← sq_norm_apply] at h
    have h' : (T.singularValues (finrank 𝕜 (range T) - 1) * ‖y‖) ^ 2 ≤ ‖T y‖ ^ 2 := by
      rw [mul_pow]; exact h
    exact (pow_le_pow_iff_left₀ (mul_nonneg (T.singularValues_nonneg _) (norm_nonneg _))
      (norm_nonneg _) two_ne_zero).mp h'
  · intro i hi
    have hi' : finrank 𝕜 (range T) ≤ i := by
      have := Fin.lt_def.mp hi
      simp only [k] at this
      omega
    rw [OrthonormalBasis.repr_apply_apply]
    exact Submodule.inner_right_of_mem_orthogonal
      (mem_ker.mpr (T.apply_rightSingularBasis_eq_zero hi')) hy

/-- **Smallest singular value as the best lower bound.**  If `dim E > 0`, then
`ρ ‖x‖ ≤ ‖T x‖` for all `x` iff `ρ ≤ σ_{dim E - 1}(T)`. -/
theorem forall_mul_norm_le_iff (hd : 0 < finrank 𝕜 E) {ρ : ℝ} :
    (∀ x, ρ * ‖x‖ ≤ ‖T x‖) ↔ ρ ≤ T.singularValues (finrank 𝕜 E - 1) := by
  constructor
  · intro h
    set k : Fin (finrank 𝕜 E) := ⟨finrank 𝕜 E - 1, by omega⟩
    have := h (T.rightSingularBasis k)
    rwa [(T.rightSingularBasis).orthonormal.1 k, mul_one, norm_apply_rightSingularBasis] at this
  · intro h x
    exact (mul_le_mul_of_nonneg_right h (norm_nonneg x)).trans (T.singularValues_mul_norm_le x)

end LinearMap

namespace LeanDLRA.SVD

open Matrix WithLp

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

omit [Fintype m] in
/-- The rank of a matrix is the dimension of the range of `toEuclideanLin`. -/
lemma rank_eq_finrank_range [Finite m] (A : Matrix m n ℝ) :
    A.rank = finrank ℝ (LinearMap.range (toEuclideanLin A)) := by
  have := Fintype.ofFinite m
  exact A.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun m ℝ).toBasis
    (EuclideanSpace.basisFun n ℝ).toBasis

omit [Fintype m] in
/-- The matrix `U diag(σ) Vᵀ` built from columns `uᵢ`, `vᵢ` acts as `x ↦ ∑ᵢ σᵢ ⟪vᵢ, x⟫ uᵢ`. -/
lemma toEuclideanLin_ofCols_mul_diagonal_mul_transpose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → EuclideanSpace ℝ m) (σ : ι → ℝ) (v : ι → EuclideanSpace ℝ n)
    (x : EuclideanSpace ℝ n) :
    toEuclideanLin (ofCols u * diagonal σ * (ofCols v)ᵀ) x = ∑ i, σ i • ⟪v i, x⟫_ℝ • u i := by
  ext j
  simp only [toLpLin_mul_same, LinearMap.coe_comp, Function.comp_apply, toLpLin_apply,
    mulVec_mulVec, mulVec, dotProduct, Matrix.mul_apply, ofCols_apply, diagonal_apply,
    transpose_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    Finset.sum_mul, PiLp.inner_apply, RCLike.inner_apply, Real.ringHom_apply, ofLp_sum, ofLp_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

/-- **Thin singular value decomposition of a real matrix.**  If `rank A = r`, then
`A = U diag(σ) Vᵀ` with `Uᵀ U = 1`, `Vᵀ V = 1` (`r` orthonormal columns each), and
`σ₀ ≥ ⋯ ≥ σ_{r-1} > 0` the nonzero singular values of `A` (Mathlib's
`(toEuclideanLin A).singularValues`). -/
theorem exists_svd (A : Matrix m n ℝ) {r : ℕ} (hr : A.rank = r) :
    ∃ (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (σ : Fin r → ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ Antitone σ ∧ (∀ i, 0 < σ i) ∧
      (∀ i, σ i = (toEuclideanLin A).singularValues i) ∧ A = U * diagonal σ * Vᵀ := by
  have hr' : finrank ℝ (LinearMap.range (toEuclideanLin A)) = r := by
    rw [← hr, rank_eq_finrank_range]
  subst hr'
  refine ⟨ofCols (toEuclideanLin A).leftSingularVectors,
    ofCols (toEuclideanLin A).rightSingularVectors, fun i => (toEuclideanLin A).singularValues i,
    transpose_ofCols_mul_ofCols (toEuclideanLin A).orthonormal_leftSingularVectors,
    transpose_ofCols_mul_ofCols (toEuclideanLin A).orthonormal_rightSingularVectors,
    fun i j h => (toEuclideanLin A).singularValues_antitone h,
    (toEuclideanLin A).singularValues_pos, fun _ => rfl, ?_⟩
  apply toEuclideanLin.injective
  ext1 x
  rw [toEuclideanLin_ofCols_mul_diagonal_mul_transpose, (toEuclideanLin A).apply_eq_sum]
  simp

/-- **The smallest singular value as the best lower bound** (matrix version): for
`S ∈ ℝ^{m × n}` with `n` nonempty, `ρ ‖v‖ ≤ ‖S v‖` for all `v` iff `ρ ≤ σ_{n-1}(S)`. -/
theorem forall_mul_norm_le_iff [Nonempty n] (S : Matrix m n ℝ) {ρ : ℝ} :
    (∀ v, ρ * ‖v‖ ≤ ‖toEuclideanLin S v‖) ↔
      ρ ≤ (toEuclideanLin S).singularValues (Fintype.card n - 1) := by
  have := (toEuclideanLin S).forall_mul_norm_le_iff
    (by rw [finrank_euclideanSpace]; exact Fintype.card_pos) (ρ := ρ)
  rwa [finrank_euclideanSpace] at this

/-- **The smallest singular value as the best lower bound** for a square matrix
`S ∈ ℝ^{k × k}`, `k > 0`: `(∀ v, ρ ‖v‖ ≤ ‖S v‖) ↔ ρ ≤ σ_{k-1}(S)`.  This is the hypothesis
`σ_min(S) ≥ ρ` of `LeanDLRA.Curvature.koch_lubich_normal` and its relatives. -/
theorem forall_mul_norm_le_iff_fin {k : ℕ} (hk : 0 < k) (S : Matrix (Fin k) (Fin k) ℝ)
    {ρ : ℝ} : (∀ v, ρ * ‖v‖ ≤ ‖toEuclideanLin S v‖) ↔
      ρ ≤ (toEuclideanLin S).singularValues (k - 1) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  rw [forall_mul_norm_le_iff, Fintype.card_fin]

/-- The hypothesis `0 < k` of `forall_mul_norm_le_iff_fin` cannot be dropped: on the zero space
every `ρ` is a lower bound, while `σ_{0-1} = σ₀ = 0`. -/
example :
    (∀ v : EuclideanSpace ℝ (Fin 0),
      1 * ‖v‖ ≤ ‖toEuclideanLin (0 : Matrix (Fin 0) (Fin 0) ℝ) v‖) ∧
    ¬ (1 : ℝ) ≤ (toEuclideanLin (0 : Matrix (Fin 0) (Fin 0) ℝ)).singularValues (0 - 1) := by
  refine ⟨fun v => ?_, ?_⟩
  · rw [Subsingleton.elim v 0]
    simp
  · rw [LinearMap.singularValues_of_finrank_le _ (by simp)]
    norm_num

section Factor

/-- `Aᵀ A` acts as `T† T` for `T = toEuclideanLin A`. -/
lemma toEuclideanLin_transpose_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix m ι ℝ) :
    toEuclideanLin (Aᵀ * A) = LinearMap.adjoint (toEuclideanLin A) ∘ₗ toEuclideanLin A := by
  classical
  rw [toLpLin_mul_same, ← conjTranspose_eq_transpose_of_trivial,
    toEuclideanLin_conjTranspose_eq_adjoint]

/-- A matrix with orthonormal columns is an isometry: `Uᵀ U = 1 → ‖U x‖ = ‖x‖`. -/
lemma norm_toEuclideanLin_of_transpose_mul_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Matrix m ι ℝ} (hU : Uᵀ * U = 1) (x : EuclideanSpace ℝ ι) :
    ‖toEuclideanLin U x‖ = ‖x‖ := by
  have h := (toEuclideanLin U).sq_norm_apply x
  rw [← toEuclideanLin_transpose_mul_self, hU, toLpLin_one, LinearMap.id_apply,
    inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

omit [Fintype m] [DecidableEq n] in
/-- If `X = U S Vᵀ` has rank `r` (the number of columns of `U`, `V`), then `S` is injective. -/
theorem injective_of_eq_mul {r : ℕ} {X : Matrix m n ℝ} {U : Matrix m (Fin r) ℝ}
    {S : Matrix (Fin r) (Fin r) ℝ} {V : Matrix n (Fin r) ℝ} (hX : X = U * S * Vᵀ)
    (hr : X.rank = r) : Function.Injective (toEuclideanLin S) := by
  have hS : S.rank = r := by
    refine le_antisymm (by simpa using S.rank_le_card_width) ?_
    calc r = X.rank := hr.symm
      _ ≤ (U * S).rank := hX ▸ rank_mul_le_left _ _
      _ ≤ S.rank := rank_mul_le_right _ _
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  have h1 := (toEuclideanLin S).finrank_range_add_finrank_ker
  rw [← rank_eq_finrank_range, hS, finrank_euclideanSpace, Fintype.card_fin] at h1
  omega

/-- **Lower bound of the core factor of any orthonormal factorisation.**  If `X = U S Vᵀ` has
rank `r`, with `r` orthonormal columns in `U` and `V`, then `σ_{r-1}(X) ‖w‖ ≤ ‖S w‖`.  (In fact
`S` has the same singular values as `X`; only the lower bound is needed.)  Proof: `V w` lies in
`(ker X)ᗮ` (as `S` is invertible), where `X` is bounded below by `σ_{r-1}(X)`, and
`‖X V w‖ = ‖U S w‖ = ‖S w‖`. -/
theorem singularValues_mul_norm_le_of_eq_mul {r : ℕ} {X : Matrix m n ℝ}
    {U : Matrix m (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hX : X = U * S * Vᵀ) (hr : X.rank = r)
    (w : EuclideanSpace ℝ (Fin r)) :
    (toEuclideanLin X).singularValues (r - 1) * ‖w‖ ≤ ‖toEuclideanLin S w‖ := by
  classical
  have hinj := injective_of_eq_mul hX hr
  have hrX : finrank ℝ (LinearMap.range (toEuclideanLin X)) = r := by
    rw [← hr, rank_eq_finrank_range]
  have hy : toEuclideanLin V w ∈ (LinearMap.ker (toEuclideanLin X))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    have hz' : toEuclideanLin S (toEuclideanLin Vᵀ z) = 0 := by
      have h := congrArg (toEuclideanLin Uᵀ) (LinearMap.mem_ker.mp hz)
      rw [map_zero] at h
      rw [← h, hX, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← toLpLin_mul_same,
        ← toLpLin_mul_same, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul]
    have hVz : toEuclideanLin Vᵀ z = 0 := hinj (hz'.trans (map_zero _).symm)
    rw [← LinearMap.adjoint_inner_left, ← toEuclideanLin_conjTranspose_eq_adjoint,
      conjTranspose_eq_transpose_of_trivial, hVz, inner_zero_left]
  have h := (toEuclideanLin X).singularValues_mul_norm_le_of_mem_orthogonal hy
  rw [hrX, norm_toEuclideanLin_of_transpose_mul_eq_one hV] at h
  have hXV : toEuclideanLin X (toEuclideanLin V w) = toEuclideanLin U (toEuclideanLin S w) := by
    rw [hX, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← toLpLin_mul_same,
      ← toLpLin_mul_same, Matrix.mul_assoc (U * S), hV, Matrix.mul_one]
  rwa [hXV, norm_toEuclideanLin_of_transpose_mul_eq_one hU] at h

end Factor

/-! ### Connection to dynamical low-rank approximation -/

section DLRA

/-- The smallest nonzero singular value `σ_{r-1}(X)` of a rank-`r` matrix, `r > 0`, is
positive. -/
theorem singularValues_pred_rank_pos {r : ℕ} {X : Matrix m n ℝ} (hX : X.rank = r) (hr : 0 < r) :
    0 < (toEuclideanLin X).singularValues (r - 1) := by
  rw [LinearMap.singularValues_pos_iff_lt_finrank_range, ← rank_eq_finrank_range, hX]
  omega

/-- **Every rank-`r` matrix satisfies the hypotheses of `LeanDLRA.Curvature.koch_lubich_normal_svd`
and `LeanDLRA.Curvature.koch_lubich_tangent_svd` with `ρ = σ_{r-1}(X)`**: it has a thin SVD
`X = U diag(σ) Vᵀ` with `σᵢ ≥ σ_{r-1}(X)` for all `i`. -/
theorem exists_svd_bounded_below {r : ℕ} {X : Matrix m n ℝ} (hX : X.rank = r) :
    ∃ (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (σ : Fin r → ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ X = U * diagonal σ * Vᵀ ∧
      ∀ i, (toEuclideanLin X).singularValues (r - 1) ≤ σ i := by
  obtain ⟨U, V, σ, hU, hV, -, -, hσ, hXeq⟩ := exists_svd X hX
  refine ⟨U, V, σ, hU, hV, hXeq, fun i => ?_⟩
  rw [hσ i]
  exact (toEuclideanLin X).singularValues_antitone (by omega)

omit [DecidableEq n] in
/-- **The manifold `ℳ_r` of rank-`r` matrices** is the set of products `U S Vᵀ` with `r`
orthonormal columns in `U` and `V` and invertible `S` (Koch–Lubich 2007, §2). -/
theorem rank_eq_iff_exists_factor {r : ℕ} (X : Matrix m n ℝ) :
    X.rank = r ↔ ∃ (U : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ)
      (V : Matrix n (Fin r) ℝ), Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ IsUnit S.det ∧ X = U * S * Vᵀ := by
  classical
  constructor
  · intro hX
    obtain ⟨U, V, σ, hU, hV, -, hσ, -, hXeq⟩ := exists_svd X hX
    refine ⟨U, diagonal σ, V, hU, hV, ?_, hXeq⟩
    rw [det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (hσ i).ne'
  · rintro ⟨U, S, V, hU, hV, hS, rfl⟩
    refine le_antisymm (rank_mul_mul_transpose_le U S V) ?_
    have hS' : S = Uᵀ * (U * S * Vᵀ) * V := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc, hV,
        Matrix.mul_one]
    calc r = S.rank := by
          rw [rank_of_isUnit S ((isUnit_iff_isUnit_det S).mpr hS), Fintype.card_fin]
      _ = (Uᵀ * (U * S * Vᵀ) * V).rank := by rw [← hS']
      _ ≤ (Uᵀ * (U * S * Vᵀ)).rank := rank_mul_le_left _ _
      _ ≤ (U * S * Vᵀ).rank := rank_mul_le_right _ _

variable [DecidableEq m]

open Curvature in
/-- **Generalized inverse with spectral bound.**  Every `X` of rank `r > 0` has a reflexive
generalized inverse `G` (`X G X = X`, `G X G = G`; namely `G = V diag(σ)⁻¹ Uᵀ`, the
Moore–Penrose inverse) with `‖G‖₂ ≤ σ_{r-1}(X)⁻¹`.  The curvature bounds of
`LeanDLRA.Curvature` are proved through such a `G` (`norm_normal_sub_le`). -/
theorem exists_ginv {r : ℕ} {X : Matrix m n ℝ} (hX : X.rank = r) (hr : 0 < r) :
    ∃ G : Matrix n m ℝ, X * G * X = X ∧ G * X * G = G ∧
      specNorm G ≤ ((toEuclideanLin X).singularValues (r - 1))⁻¹ := by
  obtain ⟨U, V, σ, hU, hV, hXeq, hσ⟩ := exists_svd_bounded_below hX
  have hρ := singularValues_pred_rank_pos hX hr
  have hS := diagonal_bounded_below hρ.le hσ
  have hdet := isUnit_det_of_bounded_below hρ hS
  refine ⟨V * (diagonal σ)⁻¹ * Uᵀ, ?_, ?_, specNorm_ginv_le hρ hU hV hS⟩
  · rw [hXeq]; exact factor_ginv_factor hU hV hdet
  · rw [hXeq]; exact ginv_factor_ginv hU hV hdet

section Frobenius

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

open Curvature

/-- **Koch–Lubich curvature bound for the normal component, unconditional form.**  For every
`X` of rank `r > 0` and every `Y = U' S' V'ᵀ` with `r` orthonormal columns in `U'`, `V'`:
`‖(I - U' U'ᵀ)(Y - X)(I - V' V'ᵀ)‖_F ≤ σ_{r-1}(X)⁻¹ ‖Y - X‖_F²`. -/
theorem koch_lubich_normal_of_rank {r : ℕ} {X : Matrix m n ℝ} (hX : X.rank = r) (hr : 0 < r)
    {U' : Matrix m (Fin r) ℝ} {V' : Matrix n (Fin r) ℝ} (S' : Matrix (Fin r) (Fin r) ℝ)
    (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1) :
    ‖(1 - U' * U'ᵀ) * (U' * S' * V'ᵀ - X) * (1 - V' * V'ᵀ)‖ ≤
      ((toEuclideanLin X).singularValues (r - 1))⁻¹ * ‖U' * S' * V'ᵀ - X‖ ^ 2 := by
  obtain ⟨U, V, σ, hU, hV, hXeq, hσ⟩ := exists_svd_bounded_below hX
  have h := koch_lubich_normal_svd (S' := S') (singularValues_pred_rank_pos hX hr) hσ hU hV hU'
    hV'
  rwa [← hXeq] at h

omit [DecidableEq m] in
/-- **Koch–Lubich Lipschitz bound for the tangent projector, unconditional form.**  For every
orthonormal factorisation `X = U S Vᵀ` of a rank-`r` matrix (`r > 0`), every `Y = U' S' V'ᵀ` as in
`koch_lubich_normal_of_rank`, and every `B`:
`‖P(Y) B - P(X) B‖_F ≤ 2 √2 σ_{r-1}(X)⁻¹ ‖Y - X‖_F ‖B‖₂`. -/
theorem koch_lubich_tangent_of_rank {r : ℕ} {X : Matrix m n ℝ} (hX : X.rank = r) (hr : 0 < r)
    {U U' : Matrix m (Fin r) ℝ} {V V' : Matrix n (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ}
    (S' : Matrix (Fin r) (Fin r) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hXeq : X = U * S * Vᵀ) (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1) (B : Matrix m n ℝ) :
    ‖tangentProjMat (U' * U'ᵀ) (V' * V'ᵀ) B - tangentProjMat (U * Uᵀ) (V * Vᵀ) B‖ ≤
      2 * √2 * ((toEuclideanLin X).singularValues (r - 1))⁻¹ * ‖U' * S' * V'ᵀ - X‖ *
        specNorm B := by
  classical
  have h := koch_lubich_tangent (S' := S') (singularValues_pred_rank_pos hX hr) hU hV hU' hV'
    (singularValues_mul_norm_le_of_eq_mul hU hV hXeq hX) B
  rwa [← hXeq] at h

end Frobenius

end DLRA

end LeanDLRA.SVD
