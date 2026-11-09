import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Classical.WeylSingular
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.LowRankDistance

/-!
# Results of arXiv 2602.14854: Domain-decomposition DLRA for radiative transfer

The paper states no theorem.  This module proves properties of the two linear-algebra ingredients
of its rank-adaptive domain-decomposition DLRA scheme (Algorithms 4 and 5), stated on real matrices
with the Frobenius norm.

* `epsRank` and `alg5_tolerance_truncation`: **Algorithm 5**.  The core `ε`-rank `epsRank tol A`
  is the smallest `r'` with `(∑_{j ≥ r'} σ_j(A)²)^{1/2} ≤ tol` (`epsRank_eq_sInf_tailNorm`);
  truncating the (augmented) factorisation `U₀ S₀ V₀ᵀ` to
  this rank gives a factorisation `U₁ S₁ V₁ᵀ` of rank `≤ r'` with Frobenius error `≤ tol`, and no
  smaller rank meets the tolerance.
* `alg4_augmentation`: **Algorithm 4**.  The leading `r_t` left singular vectors `V̂` of
  `L₀ = [V₀S₀ᵀ, V_L S_Lᵀ, V_R S_Rᵀ]` are orthonormal and `‖(I − V̂V̂ᵀ)L₀‖_F² = ∑_{j ≥ r_t} σ_j²`;
  with `r_t = epsRank tol L₀ᵀ` this is `≤ tol²` and each neighbour block is captured to within
  `tol`.
  Differences from Algorithm 4: the extra requirement `r_t ≥ r` of step 3 is not imposed in
  `alg4_augmentation_tol` (`alg4_augmentation` holds for every `r_t`), and steps 5–6 (extension of
  `U⁰` by a random basis, QR, new core) are not formalised.

Section 3 / Algorithm 6 (the domain-decomposition scheme itself) is a description of an algorithm,
not a statement with a conclusion, and is not formalised.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2602_14854

open LeanDLRA.WeylSingular LeanDLRA.EckartYoung LeanDLRA.Frobenius

section Alg5

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  [DecidableEq n] [DecidableEq p] [DecidableEq q]

/-! The rank selected by the tolerance criterion of Algorithm 5, the smallest `r'` with
`(∑_{j ≥ r'} σ_j(A)²)^{1/2} ≤ tol`, is the core `ε`-rank `epsRank tol A` (the smallest `r'` with
`distLR r' A ≤ tol`), since the singular-value tail is the distance to the matrices of rank `≤ r'`
(`tailNorm_eq_infDist`). The local `tolRank A tol` of an earlier version of this file was this
number (unification batch C3; `epsRank_eq_sInf_tailNorm`). -/

/-- **Bridge.** The `ε`-rank is the smallest rank whose singular-value tail is at most the
tolerance: `epsRank tol A = min {r' : τ_{r'}(A) ≤ tol}`. -/
theorem epsRank_eq_sInf_tailNorm (A : Matrix m n ℝ) (tol : ℝ) :
    epsRank tol A = sInf {r : ℕ | tailNorm A r ≤ tol} := by
  simp only [epsRank, distLR, lowRankSet, tailNorm_eq_infDist]

theorem tailNorm_card (A : Matrix m n ℝ) : tailNorm A (Fintype.card n) = 0 := by
  simp [tailNorm]

/-- The tolerance rank meets the tolerance: `τ_{epsRank tol A}(A) ≤ tol`. -/
theorem tolRank_spec (A : Matrix m n ℝ) {tol : ℝ} (htol : 0 ≤ tol) :
    tailNorm A (epsRank tol A) ≤ tol := by
  rw [epsRank_eq_sInf_tailNorm]
  exact Nat.sInf_mem (s := {r : ℕ | tailNorm A r ≤ tol})
    ⟨Fintype.card n, by simpa [tailNorm_card] using htol⟩

omit [DecidableEq n] in
/-- The tolerance rank is at most the number of columns. -/
theorem tolRank_le_card (A : Matrix m n ℝ) {tol : ℝ} (htol : 0 ≤ tol) :
    epsRank tol A ≤ Fintype.card n := by
  classical
  rw [epsRank_eq_sInf_tailNorm]
  exact Nat.sInf_le (by simpa [tailNorm_card] using htol)

theorem lt_tailNorm_of_lt_tolRank (A : Matrix m n ℝ) {tol : ℝ} {s : ℕ} (hs : s < epsRank tol A) :
    tol < tailNorm A s := by
  rw [epsRank_eq_sInf_tailNorm] at hs
  by_contra h
  exact absurd (Nat.sInf_le (not_lt.mp h)) (not_le.mpr hs)

/-- **Algorithm 5 (tolerance truncation), plain form.**  arXiv 2602.14854, Algorithm 5.
Keeping the smallest `r'` with `(∑_{j ≥ r'} σ_j²)^{1/2} ≤ tol` (`r' = epsRank tol A`, `tol ≥ 0`),
the truncated SVD `A V_{r'} V_{r'}ᵀ` has rank `≤ r'`, satisfies `‖A − A V_{r'} V_{r'}ᵀ‖_F ≤ tol`,
and `r'` is minimal: every `B` with `‖A − B‖_F ≤ tol` has rank `≥ r'`. -/
theorem alg5_tolerance_truncation_plain (A : Matrix m n ℝ) {tol : ℝ} (htol : 0 ≤ tol) :
    (truncation A (epsRank tol A)).rank ≤ epsRank tol A ∧
      ‖A - truncation A (epsRank tol A)‖ ≤ tol ∧
      (∀ B : Matrix m n ℝ, ‖A - B‖ ≤ tol → epsRank tol A ≤ B.rank) := by
  refine ⟨rank_truncation_le _ _, ?_, fun B hB => ?_⟩
  · rw [← tailNorm_eq_norm_sub_truncation]; exact tolRank_spec A htol
  · by_contra h
    have h1 := lt_tailNorm_of_lt_tolRank A (not_le.mp h)
    have h2 := tailNorm_le_norm_sub A B (le_refl B.rank)
    linarith

omit [DecidableEq n] in
/-- **Algorithm 5 (tolerance truncation), factored form.**  arXiv 2602.14854, Algorithm 5.
Let `Ŷ = U₀ S₀ V₀ᵀ` with `U₀ᵀU₀ = 1`, `V₀ᵀV₀ = 1` and an arbitrary core `S₀`.  Choose the smallest
`r'` with `(∑_{j ≥ r'} σ_j(S₀)²)^{1/2} ≤ tol` (`tol ≥ 0`) and truncate the core's SVD,
`S₁ = S₀ V_{r'} V_{r'}ᵀ = P_{r'} Σ_{r'} Qᵀ`, giving
`Y₁ = U₀ S₁ V₀ᵀ = (U₀P_{r'}) Σ_{r'} (V₀Q_{r'})ᵀ`.
Then `‖Ŷ − Y₁‖_F ≤ tol` (indeed `= τ_{r'}(S₀)`), `rank Y₁ ≤ r'`, and every smaller rank `s < r'`
misses the tolerance, `tol < τ_s(S₀)`.  Written with the truncated core rather than the
factors `U₁, S₁, V₁` of its SVD; `S₁ = P Σ Qᵀ` is just that SVD. -/
theorem alg5_tolerance_truncation
    {U₀ : Matrix m p ℝ} {V₀ : Matrix n q ℝ} (hU : U₀ᵀ * U₀ = 1) (hV : V₀ᵀ * V₀ = 1)
    (S₀ : Matrix p q ℝ) {tol : ℝ} (htol : 0 ≤ tol) :
    ‖U₀ * S₀ * V₀ᵀ - U₀ * truncation S₀ (epsRank tol S₀) * V₀ᵀ‖ ≤ tol ∧
      (U₀ * truncation S₀ (epsRank tol S₀) * V₀ᵀ).rank ≤ epsRank tol S₀ ∧
      (∀ s < epsRank tol S₀, tol < tailNorm S₀ s) := by
  refine ⟨?_, ?_, fun s hs => lt_tailNorm_of_lt_tolRank S₀ hs⟩
  · have : U₀ * S₀ * V₀ᵀ - U₀ * truncation S₀ (epsRank tol S₀) * V₀ᵀ
        = U₀ * (S₀ - truncation S₀ (epsRank tol S₀)) * V₀ᵀ := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
    rw [this, norm_mul_transpose_of_orthonormal hV, norm_mul_of_orthonormal hU,
      ← tailNorm_eq_norm_sub_truncation]
    exact tolRank_spec S₀ htol
  · exact (Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_mul_le_right _ _).trans (rank_truncation_le _ _))

end Alg5

section Alg4

/-- `σ_i(Aᵀ) ≤ σ_i(A)`, via Eckart–Young–Mirsky (spectral norm). -/
private theorem sv_transpose_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n ℝ) (i : ℕ) :
    (Matrix.toEuclideanLin Aᵀ).singularValues i ≤ (Matrix.toEuclideanLin A).singularValues i := by
  have h := singularValues_le_specNorm_sub (r := i) Aᵀ (truncation A i)ᵀ
    (by rw [Matrix.rank_transpose]; exact rank_truncation_le A i)
  rwa [← Matrix.transpose_sub, Curvature.specNorm_transpose, specNorm_sub_truncation] at h

/-- `σ_i(Aᵀ) = σ_i(A)`. -/
private theorem sv_transpose {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n ℝ) (i : ℕ) :
    (Matrix.toEuclideanLin Aᵀ).singularValues i = (Matrix.toEuclideanLin A).singularValues i :=
  le_antisymm (sv_transpose_le A i) (by simpa using sv_transpose_le Aᵀ i)

variable {n a b c : Type*} [Fintype n] [Fintype a] [Fintype b] [Fintype c] [DecidableEq n]

/-- The Frobenius norm of a column block is at most that of the whole matrix. -/
theorem norm_fromCols_left_le {m : Type*} [Fintype m] (X : Matrix m a ℝ) (Y : Matrix m b ℝ) :
    ‖X‖ ≤ ‖Matrix.fromCols X Y‖ := by
  have h : ‖X‖ ^ 2 ≤ ‖Matrix.fromCols X Y‖ ^ 2 := by
    rw [norm_sq_eq_sum, norm_sq_eq_sum]
    simp only [Fintype.sum_sum_type, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
      Finset.sum_add_distrib]
    have : 0 ≤ ∑ i, ∑ j, Y i j ^ 2 := by positivity
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

theorem norm_fromCols_right_le {m : Type*} [Fintype m] (X : Matrix m a ℝ) (Y : Matrix m b ℝ) :
    ‖Y‖ ≤ ‖Matrix.fromCols X Y‖ := by
  have h : ‖Y‖ ^ 2 ≤ ‖Matrix.fromCols X Y‖ ^ 2 := by
    rw [norm_sq_eq_sum, norm_sq_eq_sum]
    simp only [Fintype.sum_sum_type, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
      Finset.sum_add_distrib]
    have : 0 ≤ ∑ i, ∑ j, X i j ^ 2 := by positivity
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- **Algorithm 4 (augmentation with neighbour bases).**  arXiv 2602.14854, Algorithm 4.
Let `L₀ = [K₀, K_L, K_R]` (in the paper `K₀ = V₀S₀ᵀ`, `K_L = V_L S_Lᵀ`, `K_R = V_R S_Rᵀ`; the three
blocks may be arbitrary `n × _` matrices, no orthonormality is needed) and let `V̂` consist of the
leading `r_t` left singular vectors of `L₀`, i.e. the first `r_t` right singular vectors of `L₀ᵀ`
(`topRightSingularVectors L₀ᵀ r_t`).  Then `V̂ᵀV̂ = 1` and
`‖(I − V̂V̂ᵀ)L₀‖_F² = ∑_{j ≥ r_t} σ_j(L₀)²` (the sum over `r_t ≤ j < n` is complete: `L₀` has
`n` rows so `σ_j(L₀) = 0` for `j ≥ n`).  Here `r_t = r` is a free parameter; for the
tolerance-selected `r_t` see `alg4_augmentation_tol`. -/
theorem alg4_augmentation [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (K₀ : Matrix n a ℝ) (K_L : Matrix n b ℝ) (K_R : Matrix n c ℝ) (r : ℕ) :
    let L₀ : Matrix n (a ⊕ b ⊕ c) ℝ := Matrix.fromCols K₀ (Matrix.fromCols K_L K_R)
    let Vh := topRightSingularVectors L₀ᵀ r
    Vhᵀ * Vh = 1 ∧
      ‖(1 - Vh * Vhᵀ) * L₀‖ ^ 2 =
        ∑ j ∈ Ico r (Fintype.card n), (Matrix.toEuclideanLin L₀).singularValues j ^ 2 := by
  intro L₀ Vh
  refine ⟨transpose_mul_topRightSingularVectors L₀ᵀ r, ?_⟩
  have h1 : (1 - Vh * Vhᵀ) * L₀ = (L₀ᵀ - truncation L₀ᵀ r)ᵀ := by
    simp only [truncation, Vh, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_assoc]
  rw [h1, norm_transpose, sq_norm_sub_truncation]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sv_transpose]

/-- **Algorithm 4, tolerance form.**  arXiv 2602.14854, Algorithm 4.  With `L₀ = [K₀, K_L, K_R]` as
in `alg4_augmentation` and `r_t = epsRank tol L₀ᵀ` (the smallest `r_t` with
`(∑_{j ≥ r_t} σ_j(L₀)²)^{1/2} ≤ tol`, `tol ≥ 0`), the truncated basis `V̂` satisfies
`‖(I − V̂V̂ᵀ)L₀‖_F² ≤ tol²`, and each of the three blocks (in particular the neighbour blocks
`V_L S_Lᵀ` and `V_R S_Rᵀ`) is captured to within `tol`: `‖(I − V̂V̂ᵀ)K‖_F ≤ tol`.
Difference from the paper: step 3 of Algorithm 4 also imposes `r_t ≥ r`; here `r_t` is the
tolerance rank itself. -/
theorem alg4_augmentation_tol (K₀ : Matrix n a ℝ) (K_L : Matrix n b ℝ) (K_R : Matrix n c ℝ)
    {tol : ℝ} (htol : 0 ≤ tol) :
    let L₀ : Matrix n (a ⊕ b ⊕ c) ℝ := Matrix.fromCols K₀ (Matrix.fromCols K_L K_R)
    let Vh := topRightSingularVectors L₀ᵀ (epsRank tol L₀ᵀ)
    ‖(1 - Vh * Vhᵀ) * L₀‖ ^ 2 ≤ tol ^ 2 ∧
      ‖(1 - Vh * Vhᵀ) * K₀‖ ≤ tol ∧ ‖(1 - Vh * Vhᵀ) * K_L‖ ≤ tol ∧
        ‖(1 - Vh * Vhᵀ) * K_R‖ ≤ tol := by
  intro L₀ Vh
  have hmain : ‖(1 - Vh * Vhᵀ) * L₀‖ ≤ tol := by
    have h1 : (1 - Vh * Vhᵀ) * L₀ = (L₀ᵀ - truncation L₀ᵀ (epsRank tol L₀ᵀ))ᵀ := by
      simp only [truncation, Vh, Matrix.transpose_sub, Matrix.transpose_mul,
        Matrix.transpose_transpose, Matrix.sub_mul, Matrix.one_mul,
        Matrix.mul_assoc]
    rw [h1, norm_transpose, ← tailNorm_eq_norm_sub_truncation]
    exact tolRank_spec _ htol
  have hsplit : (1 - Vh * Vhᵀ) * L₀ = Matrix.fromCols ((1 - Vh * Vhᵀ) * K₀)
      (Matrix.fromCols ((1 - Vh * Vhᵀ) * K_L) ((1 - Vh * Vhᵀ) * K_R)) := by
    simp only [L₀, Matrix.mul_fromCols]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact pow_le_pow_left₀ (norm_nonneg _) hmain 2
  · have h2 := norm_fromCols_left_le ((1 - Vh * Vhᵀ) * K₀)
      (Matrix.fromCols ((1 - Vh * Vhᵀ) * K_L) ((1 - Vh * Vhᵀ) * K_R))
    rw [← hsplit] at h2
    exact h2.trans hmain
  · have h1 : ‖(1 - Vh * Vhᵀ) * K_L‖ ≤ ‖Matrix.fromCols ((1 - Vh * Vhᵀ) * K_L)
        ((1 - Vh * Vhᵀ) * K_R)‖ := norm_fromCols_left_le _ _
    have h2 := norm_fromCols_right_le ((1 - Vh * Vhᵀ) * K₀)
      (Matrix.fromCols ((1 - Vh * Vhᵀ) * K_L) ((1 - Vh * Vhᵀ) * K_R))
    rw [← hsplit] at h2
    exact h1.trans (h2.trans hmain)
  · have h1 : ‖(1 - Vh * Vhᵀ) * K_R‖ ≤ ‖Matrix.fromCols ((1 - Vh * Vhᵀ) * K_L)
        ((1 - Vh * Vhᵀ) * K_R)‖ := norm_fromCols_right_le _ _
    have h2 := norm_fromCols_right_le ((1 - Vh * Vhᵀ) * K₀)
      (Matrix.fromCols ((1 - Vh * Vhᵀ) * K_L) ((1 - Vh * Vhᵀ) * K_R))
    rw [← hsplit] at h2
    exact h1.trans (h2.trans hmain)

end Alg4

end LeanDLRA.Literature.P2602_14854
