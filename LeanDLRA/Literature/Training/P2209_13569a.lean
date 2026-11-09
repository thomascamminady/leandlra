import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Classical.KyFan
import LeanDLRA.Classical.SVD
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Training.FactorizedDynamics

/-!
# Results of arXiv 2209.13569: Exploring low-rank training of deep neural networks

This module formalizes the three mathematical statements of Kamalakara, Locatelli, Venkitesh, Ba,
Gal and Gomez on real matrices `W = U Vᵀ`, with the Frobenius norm of `LeanDLRA.Frobenius`.
**Sec. 3, eq. (1)**: the expansion of one factor GD step is the library's
`LeanDLRA.FactorizedDynamics.factorGD_product` and is not repeated; `factorGD_eq_gradStep_iff`
and `exists_factorGD_ne_gradStep` prove the accompanying claim that this is not the full GD step,
and `factorGD_paper_formula_false` shows that the quadratic term as printed in the paper,
`α² ∇W W ∇Wᵀ`, is wrong even for square matrices (the correct term is `α² ∇W Wᵀ ∇W`).
The paper's conclusion that the first-order term does not simplify is
`exists_firstOrderTerm_eq_zero`.
**Sec. 3.2, eq. (3)**: `spectral_initialization` shows, for every SVD `IsSVD A Û σ V̂`, that
`U = Û_{:r} √Σ_r`, `V = V̂_{:r} √Σ_r` are balanced (via the library's
`LeanDLRA.FactorizedDynamics.spectralInit_balanced`) and that `U Vᵀ` is a best rank-`r`
approximation in the Frobenius and the spectral norm; this uses `IsSVD.singularValues_eq`, which
identifies the diagonal of every SVD with Mathlib's singular values, and
`exists_isSVD_of_le` and `exists_spectral_initialization` show that such SVDs and factors exist for
every `r ≤ min(m, n)`.  The paper's own remark that `U Uᵀ` and `V Vᵀ` cannot equal `Σ_r` is a shape
mismatch if read literally; its content is `mul_transpose_ne_diagonal`.
**Sec. 3.3**: the paper only cites Srebro–Shraibman.  `isLeast_nuclearNorm` is the identity
`‖W‖_* = min_{W = U Vᵀ} (‖U‖_F² + ‖V‖_F²) / 2` for factors with any `k ≥ rank W` columns, where
`nuclearNorm` is the sum of the singular values, `spectralFactor_attains_nuclearNorm` shows that the
spectral factors attain the minimum, and `sInf_factorObjective_eq` and
`isMinimizer_factorObjective_iff` give the paper's reading, that the penalty
`(λ/2)(‖U‖_F² + ‖V‖_F²)` acts as nuclear-norm regularization of `W`: for any loss, the two
regularized problems have the same infimum and corresponding minimizers.  No nuclear-norm duality is
needed: the lower bound is `∑_i σ_i = ⟪Uᵀ Û, Vᵀ V̂⟫ ≤ ‖U‖_F ‖V‖_F`.  The paper's deep-network
setting, its experiments, and its Frobenius-decay discussion are not formalized.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2209_13569

open Matrix LeanDLRA.Curvature LeanDLRA.EckartYoung LeanDLRA.FactorizedDynamics

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

/-! ### Sec. 3, eq. (1): factorized gradient descent -/

section FactorGD

/-- **The factorized step is a full GD step only in a degenerate case** (arXiv 2209.13569, Sec. 3,
eq. (1)).  The expansion of `U⁺ V⁺ᵀ` is the library's
`LeanDLRA.FactorizedDynamics.factorGD_product`.  This theorem proves the claim attached to it, that
the result is not `W - α ∇W`: the factor step of `W = U Vᵀ` agrees with the full step for all
gradients `G` and all step sizes `α` exactly when `W = 0` and `G ↦ G V Vᵀ + U Uᵀ G` is the
identity.  The paper only makes the remark and has no such characterization. -/
theorem factorGD_eq_gradStep_iff (U : Matrix m k ℝ) (V : Matrix n k ℝ) :
    (∀ (α : ℝ) (G : Matrix m n ℝ),
        (U - α • (G * V)) * (V - α • (Gᵀ * U))ᵀ = U * Vᵀ - α • G) ↔
      U * Vᵀ = 0 ∧ ∀ G : Matrix m n ℝ, G * V * Vᵀ + U * Uᵀ * G = G := by
  constructor
  · intro h
    have hsplit : ∀ G : Matrix m n ℝ,
        G * (U * Vᵀ)ᵀ * G = 0 ∧ G * V * Vᵀ + U * Uᵀ * G = G := by
      intro G
      have h1 := h 1 G
      have h2 := h (-1) G
      rw [factorGD_product] at h1 h2
      constructor
      · have h3 : (2 : ℝ) • (G * (U * Vᵀ)ᵀ * G) = 0 := by
          linear_combination (norm := module) h1 + h2
        simpa using h3
      · have h3 : (2 : ℝ) • (G * V * Vᵀ + U * Uᵀ * G) = (2 : ℝ) • G := by
          linear_combination (norm := module) h2 - h1
        exact smul_right_injective _ (two_ne_zero) h3
    refine ⟨?_, fun G => (hsplit G).2⟩
    have h0 := (hsplit (U * Vᵀ)).1
    have h1 : ((U * Vᵀ)ᵀ * (U * Vᵀ))ᴴ * ((U * Vᵀ)ᵀ * (U * Vᵀ)) = 0 := by
      rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, transpose_transpose,
        Matrix.mul_assoc, ← Matrix.mul_assoc (U * Vᵀ), h0, Matrix.mul_zero]
    have h2 := conjTranspose_mul_self_eq_zero.mp h1
    rw [← conjTranspose_eq_transpose_of_trivial] at h2
    exact conjTranspose_mul_self_eq_zero.mp h2
  · rintro ⟨h0, h1⟩ α G
    rw [factorGD_product, h0, h1]
    simp

/-- The exceptional case of `factorGD_eq_gradStep_iff` occurs: for `U = 1`, `V = 0` the factor step
is the full GD step. -/
example (α : ℝ) (G : Matrix (Fin 1) (Fin 1) ℝ) :
    ((1 : Matrix (Fin 1) (Fin 1) ℝ) - α • (G * 0)) * (0 - α • (Gᵀ * 1))ᵀ =
      1 * (0 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ - α • G := by
  simp

/-- A matrix with more columns than rows has a nontrivial kernel. -/
private theorem exists_ne_zero_mulVec_eq_zero (hk : Fintype.card k < Fintype.card m)
    (A : Matrix k m ℝ) : ∃ x : m → ℝ, x ≠ 0 ∧ A *ᵥ x = 0 := by
  have h := LinearMap.ker_ne_bot_of_finrank_lt (f := A.mulVecLin) (by simpa using hk)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  exact ⟨x, hx0, by simpa using hx⟩

/-- For `k < m` and `k < n` there is a nonzero `G` with `G V = 0` and `Gᵀ U = 0`, namely `G = x yᵀ`
with `x ⟂ range U` and `y ⟂ range V`. -/
private theorem exists_normal_gradient (hm : Fintype.card k < Fintype.card m)
    (hn : Fintype.card k < Fintype.card n) (U : Matrix m k ℝ) (V : Matrix n k ℝ) :
    ∃ G : Matrix m n ℝ, G ≠ 0 ∧ G * V = 0 ∧ Gᵀ * U = 0 := by
  obtain ⟨x, hx, hUx⟩ := exists_ne_zero_mulVec_eq_zero hm Uᵀ
  obtain ⟨y, hy, hVy⟩ := exists_ne_zero_mulVec_eq_zero hn Vᵀ
  refine ⟨vecMulVec x y, ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := Function.ne_iff.mp hx
    obtain ⟨b, hb⟩ := Function.ne_iff.mp hy
    intro h
    have h3 : x a * y b = 0 := by simpa [vecMulVec_apply] using congrFun (congrFun h a) b
    exact (mul_eq_zero.mp h3).elim ha hb
  · rw [vecMulVec_mul, ← mulVec_transpose, hVy]
    ext a b
    simp [vecMulVec_apply]
  · rw [transpose_vecMulVec, vecMulVec_mul, ← mulVec_transpose, hUx]
    ext a b
    simp [vecMulVec_apply]

/-- **In the low-rank regime no factorization reproduces full GD** (arXiv 2209.13569, Sec. 3,
eq. (1)).  If `k < m` and `k < n`, then for every `U ∈ ℝ^{m×k}`, `V ∈ ℝ^{n×k}` there is a nonzero
gradient `G` (normal to the rank-`k` manifold at `W = U Vᵀ`) for which the factor step does not
change `W` at all, while `W - α G ≠ W` for each `α ≠ 0`.  This sharpens the paper's remark that the
factorized update does not align with the vanilla gradient descent update. -/
theorem exists_factorGD_ne_gradStep (hm : Fintype.card k < Fintype.card m)
    (hn : Fintype.card k < Fintype.card n) (U : Matrix m k ℝ) (V : Matrix n k ℝ) :
    ∃ G : Matrix m n ℝ, G ≠ 0 ∧ ∀ α : ℝ,
      (U - α • (G * V)) * (V - α • (Gᵀ * U))ᵀ = U * Vᵀ ∧
        (α ≠ 0 → (U - α • (G * V)) * (V - α • (Gᵀ * U))ᵀ ≠ U * Vᵀ - α • G) := by
  obtain ⟨G, hG0, hGV, hGU⟩ := exists_normal_gradient hm hn U V
  have hstep : ∀ α : ℝ, (U - α • (G * V)) * (V - α • (Gᵀ * U))ᵀ = U * Vᵀ := by
    intro α
    rw [hGV, hGU]
    simp
  refine ⟨G, hG0, fun α => ⟨hstep α, fun hα h => ?_⟩⟩
  rw [hstep α] at h
  exact smul_ne_zero hα hG0 (sub_eq_self.mp h.symm)

/-- **The first-order term of eq. (1) does not simplify** (arXiv 2209.13569, Sec. 3.2).  The paper
concludes that `∇W V Vᵀ + U Uᵀ ∇W` cannot be simplified under spectral initialization.  In the
low-rank regime `k < m`, `k < n` this holds for all factors, spectral or not: the map
`G ↦ G V Vᵀ + U Uᵀ G` has a nonzero kernel, so it is no nonzero multiple of the identity. -/
theorem exists_firstOrderTerm_eq_zero (hm : Fintype.card k < Fintype.card m)
    (hn : Fintype.card k < Fintype.card n) (U : Matrix m k ℝ) (V : Matrix n k ℝ) :
    ∃ G : Matrix m n ℝ, G ≠ 0 ∧ G * V * Vᵀ + U * Uᵀ * G = 0 := by
  obtain ⟨G, hG0, hGV, hGU⟩ := exists_normal_gradient hm hn U V
  refine ⟨G, hG0, ?_⟩
  have hUG : Uᵀ * G = 0 := by
    simpa [transpose_mul] using congrArg Matrix.transpose hGU
  rw [hGV, Matrix.mul_assoc U, hUG]
  simp

/-- **`U Uᵀ` cannot be a nonsingular diagonal matrix** (arXiv 2209.13569, Sec. 3.2).  The paper
disputes the claim `U₀ U₀ᵀ = V₀ V₀ᵀ = Σ_r` that it attributes to Khodak et al. (2021), because
`U Uᵀ` and `V Vᵀ` "cannot be equal to `Σ_r`".  Read literally, this is a shape mismatch (`m × m`
against `r × r`).  The meaningful content is this theorem: for fewer columns than rows, `U Uᵀ` has
rank `≤ k < m`, so it equals no `m × m` diagonal matrix with nonzero diagonal.  The theorem holds
for all `U`, in particular for the spectral factor `spectralFactor`.  The product that does equal
`Σ_r` is `Uᵀ U`, see `spectral_initialization`. -/
theorem mul_transpose_ne_diagonal [DecidableEq m] (hm : Fintype.card k < Fintype.card m)
    (U : Matrix m k ℝ) {d : m → ℝ} (hd : ∀ a, d a ≠ 0) : U * Uᵀ ≠ Matrix.diagonal d := by
  intro h
  have h1 : (U * Uᵀ).rank ≤ Fintype.card k := (rank_mul_le_left _ _).trans U.rank_le_card_width
  rw [h, rank_diagonal, Fintype.card_congr (Equiv.subtypeUnivEquiv hd)] at h1
  omega

/-- **The `α²` term as printed in the paper is wrong** (arXiv 2209.13569, Sec. 3, eq. (1)).  The
paper writes the quadratic term as `α² ∇W W ∇Wᵀ`.  For non-square `W` this does not typecheck, and
this theorem shows that it also fails for square matrices: already for `2 × 2` matrices the factor
step differs from the printed formula.  The correct term `α² ∇W Wᵀ ∇W` is in
`LeanDLRA.FactorizedDynamics.factorGD_product`. -/
theorem factorGD_paper_formula_false :
    ∃ (U V G : Matrix (Fin 2) (Fin 2) ℝ) (α : ℝ),
      (U - α • (G * V)) * (V - α • (Gᵀ * U))ᵀ ≠
        U * Vᵀ - α • (G * V * Vᵀ + U * Uᵀ * G) + α ^ 2 • (G * (U * Vᵀ) * Gᵀ) := by
  refine ⟨!![0, 0; 0, 1], 1, !![0, 1; 0, 0], 1, fun h => ?_⟩
  rw [factorGD_product] at h
  have h2 := add_left_cancel h
  simp only [one_smul, one_pow, transpose_one, Matrix.mul_one] at h2
  have h1 := congrFun (congrFun h2 0) 0
  simp [vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply] at h1

end FactorGD

/-! ### Sec. 3.2, eq. (3): spectral initialization -/

section Spectral

variable {p r : ℕ}

/-- `A = Û diag(σ) V̂ᵀ` is a singular value decomposition of `A` with `p` columns: `Û`, `V̂` have
orthonormal columns and `σ₀ ≥ σ₁ ≥ ⋯ ≥ 0`.  This covers the thin SVD (`p = rank A`) and the reduced
SVD (`p = min(m, n)`) used in arXiv 2209.13569, see `exists_isSVD_of_le`. -/
structure IsSVD (A : Matrix m n ℝ) (Uh : Matrix m (Fin p) ℝ) (σ : Fin p → ℝ)
    (Vh : Matrix n (Fin p) ℝ) : Prop where
  left_orth : Uhᵀ * Uh = 1
  right_orth : Vhᵀ * Vh = 1
  antitone : Antitone σ
  nonneg : ∀ i, 0 ≤ σ i
  eq_mul : A = Uh * Matrix.diagonal σ * Vhᵀ

/-- The leading `r` columns `X_{:r}` of a matrix with `p ≥ r` columns. -/
def leadCols {ι : Type*} (hr : r ≤ p) (X : Matrix ι (Fin p) ℝ) : Matrix ι (Fin r) ℝ :=
  X.submatrix id (Fin.castLE hr)

/-- The leading `r` values `σ_{:r}`, that is, the diagonal of `Σ_r`. -/
def leadVals (hr : r ≤ p) (σ : Fin p → ℝ) : Fin r → ℝ := σ ∘ Fin.castLE hr

/-- The truncated SVD `SVD_r(W) = Û_{:r} Σ_r V̂_{:r}ᵀ` of arXiv 2209.13569, eq. (3). -/
def svdTrunc (hr : r ≤ p) (Uh : Matrix m (Fin p) ℝ) (σ : Fin p → ℝ)
    (Vh : Matrix n (Fin p) ℝ) : Matrix m n ℝ :=
  leadCols hr Uh * Matrix.diagonal (leadVals hr σ) * (leadCols hr Vh)ᵀ

/-- The matrix `√Σ_r` of arXiv 2209.13569, eq. (3). -/
noncomputable def sqrtSigma (hr : r ≤ p) (σ : Fin p → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.diagonal fun i => √(leadVals hr σ i)

/-- The factor `U = Û_{:r} √Σ_r` of arXiv 2209.13569, eq. (3). -/
noncomputable def spectralFactor {ι : Type*} (hr : r ≤ p) (X : Matrix ι (Fin p) ℝ)
    (σ : Fin p → ℝ) : Matrix ι (Fin r) ℝ :=
  leadCols hr X * sqrtSigma hr σ

/-- The leading columns of a matrix with orthonormal columns are orthonormal. -/
private theorem transpose_leadCols_mul_self {ι : Type*} [Fintype ι] {X : Matrix ι (Fin p) ℝ}
    (hX : Xᵀ * X = 1) (hr : r ≤ p) : (leadCols hr X)ᵀ * leadCols hr X = 1 := by
  have h := congrArg (fun M => M.submatrix (Fin.castLE hr) (Fin.castLE hr)) hX
  simp only [submatrix_one _ (Fin.castLE_injective hr)] at h
  rw [submatrix_mul _ _ _ id _ Function.bijective_id] at h
  exact h

omit [Fintype m] [Fintype n] in
/-- `Û_{:r} Σ_r V̂_{:r}ᵀ` is `Û diag(σ₀, …, σ_{r-1}, 0, …, 0) V̂ᵀ`. -/
private theorem svdTrunc_eq (hr : r ≤ p) (Uh : Matrix m (Fin p) ℝ) (σ : Fin p → ℝ)
    (Vh : Matrix n (Fin p) ℝ) :
    svdTrunc hr Uh σ Vh =
      Uh * Matrix.diagonal (fun i : Fin p => if (i : ℕ) < r then σ i else 0) * Vhᵀ := by
  ext a b
  rw [svdTrunc, Matrix.mul_apply, Matrix.mul_apply]
  simp only [leadCols, leadVals, Matrix.mul_diagonal, Matrix.transpose_apply,
    Matrix.submatrix_apply, id, Function.comp]
  rw [KyFan.sum_castLE_eq_sum_filter hr (fun i => Uh a i * σ i * Vh b i), Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- `‖Û diag(d) V̂ᵀ‖_F² = ∑_i d_i²` for orthonormal columns. -/
private theorem sq_norm_mul_diagonal_mul {Uh : Matrix m (Fin p) ℝ} {Vh : Matrix n (Fin p) ℝ}
    (hU : Uhᵀ * Uh = 1) (hV : Vhᵀ * Vh = 1) (d : Fin p → ℝ) :
    ‖Uh * Matrix.diagonal d * Vhᵀ‖ ^ 2 = ∑ i, d i ^ 2 := by
  rw [Frobenius.norm_mul_transpose_of_orthonormal hV, Frobenius.norm_mul_of_orthonormal hU,
    Frobenius.norm_sq_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Matrix.diagonal_apply_ne _ hj.symm])
    (fun h => absurd (Finset.mem_univ i) h), diagonal_apply_eq]

/-- The spectral norm of a diagonal matrix is at most any bound on the entries. -/
private theorem specNorm_diagonal_le [DecidableEq n] (d : n → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ i, |d i| ≤ C) : specNorm (Matrix.diagonal d) ≤ C := by
  have h : specNorm (Matrix.diagonal d) = ‖d‖ := l2_opNorm_diagonal (𝕜 := ℝ) d
  rw [h]
  exact (pi_norm_le_iff_of_nonneg hC).mpr fun i => by simpa using hd i

/-- `‖Û diag(d) V̂ᵀ‖₂ ≤ C` if `|d_i| ≤ C` for all `i`. -/
private theorem specNorm_mul_diagonal_mul_le [DecidableEq n] {Uh : Matrix m (Fin p) ℝ}
    {Vh : Matrix n (Fin p) ℝ} (hU : Uhᵀ * Uh = 1) (hV : Vhᵀ * Vh = 1) (d : Fin p → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hd : ∀ i, |d i| ≤ C) : specNorm (Uh * Matrix.diagonal d * Vhᵀ) ≤ C := by
  classical
  have h1 := specNorm_le_one_of_orthonormal hU
  have h2 : specNorm Vhᵀ ≤ 1 := by
    rw [specNorm_transpose]
    exact specNorm_le_one_of_orthonormal hV
  have h3 := specNorm_diagonal_le d hC hd
  calc specNorm (Uh * Matrix.diagonal d * Vhᵀ)
      ≤ specNorm (Uh * Matrix.diagonal d) * specNorm Vhᵀ := specNorm_mul_le _ _
    _ ≤ (specNorm Uh * specNorm (Matrix.diagonal d)) * specNorm Vhᵀ := by
        gcongr
        · exact specNorm_nonneg _
        · exact specNorm_mul_le _ _
    _ ≤ (1 * C) * 1 := by
        gcongr
        · exact specNorm_nonneg _
        · exact specNorm_nonneg _
    _ = C := by ring

namespace IsSVD

variable {A : Matrix m n ℝ} {Uh : Matrix m (Fin p) ℝ} {σ : Fin p → ℝ} {Vh : Matrix n (Fin p) ℝ}

/-- An SVD has at most `n` columns. -/
theorem le_card_width (hs : IsSVD A Uh σ Vh) : p ≤ Fintype.card n := by
  have h1 := rank_eq_card_of_transpose_mul_eq_one hs.right_orth
  have h2 := Vh.rank_le_card_height
  rw [h1, Fintype.card_fin] at h2
  exact h2

/-- A matrix with an SVD with `p` columns has rank `≤ p`. -/
theorem rank_le (hs : IsSVD A Uh σ Vh) : A.rank ≤ p := by
  rw [hs.eq_mul]
  exact rank_mul_mul_transpose_le _ _ _

omit [Fintype m] in
/-- The truncated SVD has rank `≤ r`. -/
theorem rank_svdTrunc_le (hr : r ≤ p) : (svdTrunc hr Uh σ Vh).rank ≤ r :=
  rank_mul_mul_transpose_le _ _ _

/-- The truncation error `A - Û_{:r} Σ_r V̂_{:r}ᵀ` is `Û diag(0, …, 0, σ_r, σ_{r+1}, …) V̂ᵀ`. -/
theorem sub_svdTrunc (hs : IsSVD A Uh σ Vh) (hr : r ≤ p) :
    A - svdTrunc hr Uh σ Vh =
      Uh * Matrix.diagonal (fun i : Fin p => if (i : ℕ) < r then 0 else σ i) * Vhᵀ := by
  conv_lhs => rw [hs.eq_mul]
  rw [svdTrunc_eq, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  congr 3
  ext i
  split_ifs <;> simp

/-- Every singular value of `A` is at most the corresponding `σ i`, by Eckart–Young–Mirsky. -/
private theorem singularValues_le [DecidableEq n] (hs : IsSVD A Uh σ Vh) (i : Fin p) :
    (toEuclideanLin A).singularValues i ≤ σ i := by
  classical
  have hr : (i : ℕ) ≤ p := i.2.le
  refine (singularValues_le_specNorm_sub A (svdTrunc hr Uh σ Vh)
    (rank_svdTrunc_le hr)).trans ?_
  rw [hs.sub_svdTrunc hr]
  refine specNorm_mul_diagonal_mul_le hs.left_orth hs.right_orth _ (hs.nonneg i) fun j => ?_
  split_ifs with hj
  · simpa using hs.nonneg i
  · rw [abs_of_nonneg (hs.nonneg j)]
    exact hs.antitone (not_lt.mp hj)

/-- The singular values of `A` with index `≥ p` vanish. -/
theorem singularValues_eq_zero [DecidableEq n] (hs : IsSVD A Uh σ Vh) {i : ℕ} (hi : p ≤ i) :
    (toEuclideanLin A).singularValues i = 0 := by
  classical
  have h1 := singularValues_le_specNorm_sub A A (hs.rank_le.trans hi)
  rw [sub_self] at h1
  have h2 : specNorm (0 : Matrix m n ℝ) ≤ 0 := specNorm_le_of le_rfl fun x => by simp
  exact le_antisymm (h1.trans h2) ((toEuclideanLin A).singularValues_nonneg i)

/-- **Uniqueness of the singular values**: the diagonal of every SVD consists of the singular
values `σ_i(A)` of `A` (Mathlib's `LinearMap.singularValues`). -/
theorem singularValues_eq [DecidableEq n] (hs : IsSVD A Uh σ Vh) (i : Fin p) :
    (toEuclideanLin A).singularValues i = σ i := by
  have hsum : ∑ i : Fin p, (toEuclideanLin A).singularValues i ^ 2 = ∑ i, σ i ^ 2 := by
    rw [← sq_norm_mul_diagonal_mul hs.left_orth hs.right_orth σ, ← hs.eq_mul,
      sq_norm_eq_sum_sq_singularValues,
      Fin.sum_univ_eq_sum_range (fun i => (toEuclideanLin A).singularValues i ^ 2)]
    refine Finset.sum_subset (Finset.range_subset_range.mpr hs.le_card_width) fun j _ hj => ?_
    rw [hs.singularValues_eq_zero (by simpa using hj)]
    simp
  have hle : ∀ i ∈ (univ : Finset (Fin p)), (toEuclideanLin A).singularValues i ^ 2 ≤ σ i ^ 2 :=
    fun i _ => pow_le_pow_left₀ ((toEuclideanLin A).singularValues_nonneg _)
      (hs.singularValues_le i) 2
  have h := (Finset.sum_eq_sum_iff_of_le hle).mp hsum i (Finset.mem_univ i)
  exact (pow_left_inj₀ ((toEuclideanLin A).singularValues_nonneg _) (hs.nonneg i)
    two_ne_zero).mp h

/-- `‖A - Û_{:r} Σ_r V̂_{:r}ᵀ‖_F² = ∑_{i ≥ r} σ_i(A)²`. -/
theorem sq_norm_sub_svdTrunc [DecidableEq n] (hs : IsSVD A Uh σ Vh) (hr : r ≤ p) :
    ‖A - svdTrunc hr Uh σ Vh‖ ^ 2 =
      ∑ i ∈ Finset.Ico r (Fintype.card n), (toEuclideanLin A).singularValues i ^ 2 := by
  have hsub : Finset.Ico r p ⊆ Finset.Ico r (Fintype.card n) :=
    Finset.Ico_subset_Ico_right hs.le_card_width
  rw [hs.sub_svdTrunc hr, sq_norm_mul_diagonal_mul hs.left_orth hs.right_orth,
    ← Finset.sum_subset hsub fun j hj hj' => ?_, ← sum_fin_ite_eq_sum_Ico]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs.singularValues_eq i]
    split_ifs <;> simp
  · have hj1 : p ≤ j := by
      simp only [Finset.mem_Ico, not_and, not_lt] at hj hj'
      exact hj' hj.1
    rw [hs.singularValues_eq_zero hj1]
    simp

/-- The truncated SVD is a best rank-`r` approximation in the Frobenius norm. -/
theorem norm_sub_svdTrunc_le (hs : IsSVD A Uh σ Vh) (hr : r ≤ p) {B : Matrix m n ℝ}
    (hB : B.rank ≤ r) : ‖A - svdTrunc hr Uh σ Vh‖ ≤ ‖A - B‖ := by
  classical
  have h := sum_sq_singularValues_le_sq_norm_sub A B hB
  rw [← hs.sq_norm_sub_svdTrunc hr] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- The truncated SVD is a best rank-`r` approximation in the spectral norm. -/
theorem specNorm_sub_svdTrunc_le [DecidableEq n] (hs : IsSVD A Uh σ Vh) (hr : r ≤ p)
    {B : Matrix m n ℝ} (hB : B.rank ≤ r) :
    specNorm (A - svdTrunc hr Uh σ Vh) ≤ specNorm (A - B) := by
  rw [hs.sub_svdTrunc hr]
  rcases hr.lt_or_eq with hrp | rfl
  · refine (specNorm_mul_diagonal_mul_le hs.left_orth hs.right_orth _ (hs.nonneg ⟨r, hrp⟩)
      fun j => ?_).trans ?_
    · split_ifs with hj
      · simpa using hs.nonneg ⟨r, hrp⟩
      · rw [abs_of_nonneg (hs.nonneg j)]
        exact hs.antitone (not_lt.mp hj)
    · have h := singularValues_le_specNorm_sub A B hB
      rwa [show (toEuclideanLin A).singularValues r = σ ⟨r, hrp⟩ from
        hs.singularValues_eq ⟨r, hrp⟩] at h
  · refine (specNorm_mul_diagonal_mul_le hs.left_orth hs.right_orth _ (specNorm_nonneg (A - B))
      fun j => ?_)
    simpa using specNorm_nonneg (A - B)

end IsSVD

/-- **Spectral initialization** (arXiv 2209.13569, Sec. 3.2, eq. (3)).  Let `A = Û Σ V̂ᵀ` be any SVD
with `p ≥ r` columns and `U = Û_{:r} √Σ_r`, `V = V̂_{:r} √Σ_r`.  Then the factors are balanced and
column-wise orthogonal, `UᵀU = VᵀV = Σ_r`; their product is the truncated SVD
`Û_{:r} Σ_r V̂_{:r}ᵀ`, has rank `≤ r` and Frobenius error `(∑_{i ≥ r} σ_i(A)²)^{1/2}`; and it is a
best approximation of `A` among all matrices of rank `≤ r`, in both the Frobenius and the spectral
norm (Eckart–Young–Mirsky).  Balancedness comes from
`LeanDLRA.FactorizedDynamics.spectralInit_balanced`.  The statement holds for every SVD, also when
`σ_{r-1} = σ_r` and the truncated SVD is not unique.  In the paper eq. (3) is a definition, followed
by the remark that `U`, `V` are column-wise orthogonal.  Balancedness and optimality are the
standard properties of this choice and are not stated there as a theorem. -/
theorem spectral_initialization [DecidableEq n] {A : Matrix m n ℝ} {Uh : Matrix m (Fin p) ℝ}
    {σ : Fin p → ℝ} {Vh : Matrix n (Fin p) ℝ} (hs : IsSVD A Uh σ Vh) (hr : r ≤ p) :
    (spectralFactor hr Uh σ)ᵀ * spectralFactor hr Uh σ = Matrix.diagonal (leadVals hr σ) ∧
    (spectralFactor hr Vh σ)ᵀ * spectralFactor hr Vh σ = Matrix.diagonal (leadVals hr σ) ∧
    spectralFactor hr Uh σ * (spectralFactor hr Vh σ)ᵀ = svdTrunc hr Uh σ Vh ∧
    (spectralFactor hr Uh σ * (spectralFactor hr Vh σ)ᵀ).rank ≤ r ∧
    ‖A - spectralFactor hr Uh σ * (spectralFactor hr Vh σ)ᵀ‖ ^ 2 =
      ∑ i ∈ Finset.Ico r (Fintype.card n), (toEuclideanLin A).singularValues i ^ 2 ∧
    (∀ B : Matrix m n ℝ, B.rank ≤ r →
      ‖A - spectralFactor hr Uh σ * (spectralFactor hr Vh σ)ᵀ‖ ≤ ‖A - B‖) ∧
    (∀ B : Matrix m n ℝ, B.rank ≤ r →
      specNorm (A - spectralFactor hr Uh σ * (spectralFactor hr Vh σ)ᵀ) ≤ specNorm (A - B)) := by
  have hRR : sqrtSigma hr σ * sqrtSigma hr σ = Matrix.diagonal (leadVals hr σ) := by
    rw [sqrtSigma, diagonal_mul_diagonal]
    congr 1
    ext i
    exact Real.mul_self_sqrt (hs.nonneg _)
  obtain ⟨h1, h2, h3⟩ := spectralInit_balanced
    (transpose_leadCols_mul_self hs.left_orth hr) (transpose_leadCols_mul_self hs.right_orth hr)
    (R := sqrtSigma hr σ) (diagonal_transpose _)
  rw [hRR] at h1 h2 h3
  have hprod : spectralFactor hr Uh σ * (spectralFactor hr Vh σ)ᵀ = svdTrunc hr Uh σ Vh := h3
  rw [hprod]
  exact ⟨h1, h2, rfl, IsSVD.rank_svdTrunc_le hr, hs.sq_norm_sub_svdTrunc hr,
    fun _ hB => hs.norm_sub_svdTrunc_le hr hB, fun _ hB => hs.specNorm_sub_svdTrunc_le hr hB⟩

/-- Every matrix has an SVD with `rank A` columns (`LeanDLRA.SVD.exists_svd`). -/
theorem exists_isSVD (A : Matrix m n ℝ) :
    ∃ (Uh : Matrix m (Fin A.rank) ℝ) (σ : Fin A.rank → ℝ) (Vh : Matrix n (Fin A.rank) ℝ),
      IsSVD A Uh σ Vh := by
  classical
  obtain ⟨U, V, σ, hU, hV, hσ, hpos, -, hA⟩ := SVD.exists_svd A rfl
  exact ⟨U, σ, V, ⟨hU, hV, hσ, fun i => (hpos i).le, hA⟩⟩

/-- Orthonormal columns extend to `s + t` orthonormal columns if `s + t ≤ card m`. -/
private theorem exists_extend_orthonormal {s t : ℕ} (U₀ : Matrix m (Fin s) ℝ)
    (hU₀ : U₀ᵀ * U₀ = 1) (h : s + t ≤ Fintype.card m) :
    ∃ U : Matrix m (Fin (s + t)) ℝ, Uᵀ * U = 1 ∧ leadCols (Nat.le_add_right s t) U = U₀ := by
  classical
  obtain ⟨U₁, h1, h2, h3⟩ := exists_orthonormal_capture_compl U₀ hU₀ (0 : Matrix m (Fin t) ℝ)
    (s := t) (by simp) (by simpa using h)
  have hc := (fromCols_orthonormal_capture hU₀ h1 h2 h3).1
  refine ⟨(fromCols U₀ U₁).submatrix id finSumFinEquiv.symm, ?_, ?_⟩
  · rw [transpose_submatrix, ← submatrix_mul _ _ _ id _ Function.bijective_id, hc,
      submatrix_one_equiv]
  · ext a i
    have : finSumFinEquiv.symm (Fin.castLE (Nat.le_add_right s t) i) = Sum.inl i := by
      rw [Equiv.symm_apply_eq]
      rfl
    simp [leadCols, this]

/-- **Existence of the reduced SVD**: every `A` has an SVD with `p` columns for each
`rank A ≤ p ≤ min(m, n)`, by padding with zero singular values.  With `p = min(m, n)` this is the
`Û`, `Σ`, `V̂` of arXiv 2209.13569, Sec. 3.2. -/
theorem exists_isSVD_of_le (A : Matrix m n ℝ) {p : ℕ} (hp : A.rank ≤ p)
    (hm : p ≤ Fintype.card m) (hn : p ≤ Fintype.card n) :
    ∃ (Uh : Matrix m (Fin p) ℝ) (σ : Fin p → ℝ) (Vh : Matrix n (Fin p) ℝ), IsSVD A Uh σ Vh := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hp
  obtain ⟨U₀, σ₀, V₀, hs⟩ := exists_isSVD A
  obtain ⟨Uh, hU, hU0⟩ := exists_extend_orthonormal (t := t) U₀ hs.left_orth hm
  obtain ⟨Vh, hV, hV0⟩ := exists_extend_orthonormal (t := t) V₀ hs.right_orth hn
  have hle : A.rank ≤ A.rank + t := Nat.le_add_right _ _
  let σ : Fin (A.rank + t) → ℝ := fun i => if h : (i : ℕ) < A.rank then σ₀ ⟨i, h⟩ else 0
  have hσ0 : ∀ i, 0 ≤ σ i := fun i => by
    simp only [σ]
    split_ifs
    · exact hs.nonneg _
    · exact le_rfl
  have hlead : leadVals hle σ = σ₀ := by
    ext i
    simp [leadVals, σ]
  refine ⟨Uh, σ, Vh, hU, hV, fun i j hij => ?_, hσ0, ?_⟩
  · by_cases hj : (j : ℕ) < A.rank
    · have hi : (i : ℕ) < A.rank := lt_of_le_of_lt hij hj
      have ei : σ i = σ₀ ⟨i, hi⟩ := by simp [σ, hi]
      have ej : σ j = σ₀ ⟨j, hj⟩ := by simp [σ, hj]
      rw [ei, ej]
      exact hs.antitone hij
    · have ej : σ j = 0 := by simp [σ, hj]
      rw [ej]
      exact hσ0 i
  · have h1 : A = svdTrunc hle Uh σ Vh := by
      rw [svdTrunc, hU0, hV0, hlead]
      exact hs.eq_mul
    refine h1.trans ?_
    rw [svdTrunc_eq]
    congr 3
    ext i
    split_ifs with hi
    · rfl
    · simp [σ, hi]

/-- **Spectral initialization exists for every `r ≤ min(m, n)`** (arXiv 2209.13569, Sec. 3.2,
eq. (3)): there are balanced `U ∈ ℝ^{m×r}`, `V ∈ ℝ^{n×r}` with `U Vᵀ` a best approximation of `A`
of rank `≤ r` in the Frobenius norm.  The proof takes the spectral factors of a reduced SVD
(`exists_isSVD_of_le`, `spectral_initialization`); the statement itself records only balancedness,
rank and optimality, not that `U`, `V` come from an SVD. -/
theorem exists_spectral_initialization (A : Matrix m n ℝ) {r : ℕ}
    (hm : r ≤ Fintype.card m) (hn : r ≤ Fintype.card n) :
    ∃ (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ), Uᵀ * U = Vᵀ * V ∧
      (U * Vᵀ).rank ≤ r ∧ ∀ B : Matrix m n ℝ, B.rank ≤ r → ‖A - U * Vᵀ‖ ≤ ‖A - B‖ := by
  classical
  obtain ⟨p, hrp, hp, hpm, hpn⟩ : ∃ p, r ≤ p ∧ A.rank ≤ p ∧ p ≤ Fintype.card m ∧
      p ≤ Fintype.card n :=
    ⟨min (Fintype.card m) (Fintype.card n), le_min hm hn,
      le_min A.rank_le_card_height A.rank_le_card_width, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨Uh, σ, Vh, hs⟩ := exists_isSVD_of_le A hp hpm hpn
  obtain ⟨h1, h2, -, h4, -, h6, -⟩ := spectral_initialization hs hrp
  exact ⟨_, _, h1.trans h2.symm, h4, h6⟩

end Spectral

/-! ### Sec. 3.3: Srebro–Shraibman, the factor penalty is the nuclear norm -/

section Nuclear

/-- The **nuclear norm** `‖A‖_* = ∑_i σ_i(A)`. -/
noncomputable def nuclearNorm [DecidableEq n] (A : Matrix m n ℝ) : ℝ :=
  ∑ i ∈ Finset.range (Fintype.card n), (toEuclideanLin A).singularValues i

variable {p : ℕ} {A : Matrix m n ℝ} {Uh : Matrix m (Fin p) ℝ} {σ : Fin p → ℝ}
  {Vh : Matrix n (Fin p) ℝ}

/-- The nuclear norm is the sum of the diagonal of any SVD. -/
theorem IsSVD.nuclearNorm_eq [DecidableEq n] (hs : IsSVD A Uh σ Vh) :
    nuclearNorm A = ∑ i, σ i := by
  rw [nuclearNorm, ← Finset.sum_subset (Finset.range_subset_range.mpr hs.le_card_width)
    fun j _ hj => hs.singularValues_eq_zero (by simpa using hj),
    ← Fin.sum_univ_eq_sum_range (fun i => (toEuclideanLin A).singularValues i)]
  exact Finset.sum_congr rfl fun i _ => hs.singularValues_eq i

/-- For `A = U Vᵀ`: `∑_i σ_i = tr(Ûᵀ U Vᵀ V̂) = ⟪Uᵀ Û, Vᵀ V̂⟫`. -/
private theorem IsSVD.sum_eq_inner (hs : IsSVD A Uh σ Vh) {U : Matrix m k ℝ} {V : Matrix n k ℝ}
    (hA : A = U * Vᵀ) : ∑ i, σ i = ⟪Uᵀ * Uh, Vᵀ * Vh⟫ := by
  have h1 : Uhᵀ * A * Vh = Matrix.diagonal σ := by
    calc Uhᵀ * A * Vh
        = (Uhᵀ * Uh) * Matrix.diagonal σ * (Vhᵀ * Vh) := by
          rw [hs.eq_mul]
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal σ := by
          rw [hs.left_orth, hs.right_orth, Matrix.one_mul, Matrix.mul_one]
  rw [Frobenius.inner_eq_trace, transpose_mul, transpose_transpose,
    show Uhᵀ * U * (Vᵀ * Vh) = Uhᵀ * A * Vh by rw [hA]; simp only [Matrix.mul_assoc], h1,
    trace_diagonal]

/-- `‖Xᵀ Y‖_F ≤ ‖X‖_F` if `Y` has orthonormal columns. -/
private theorem norm_transpose_mul_le {l : Type*} [Fintype l] {q : ℕ} (X : Matrix l k ℝ)
    {Y : Matrix l (Fin q) ℝ} (hY : Yᵀ * Y = 1) : ‖Xᵀ * Y‖ ≤ ‖X‖ := by
  classical
  calc ‖Xᵀ * Y‖ ≤ ‖Xᵀ‖ * specNorm Y := frob_mul_le' _ _
    _ ≤ ‖Xᵀ‖ * 1 := by
        gcongr
        exact specNorm_le_one_of_orthonormal hY
    _ = ‖X‖ := by rw [mul_one, Frobenius.norm_transpose]

/-- **Lower bound of Srebro–Shraibman, product form**: `‖U Vᵀ‖_* ≤ ‖U‖_F ‖V‖_F`. -/
theorem nuclearNorm_mul_transpose_le_mul [DecidableEq n] (U : Matrix m k ℝ) (V : Matrix n k ℝ) :
    nuclearNorm (U * Vᵀ) ≤ ‖U‖ * ‖V‖ := by
  classical
  obtain ⟨Uh, σ, Vh, hs⟩ := exists_isSVD (U * Vᵀ)
  rw [hs.nuclearNorm_eq, hs.sum_eq_inner rfl]
  exact (real_inner_le_norm _ _).trans (mul_le_mul (norm_transpose_mul_le U hs.left_orth)
    (norm_transpose_mul_le V hs.right_orth) (norm_nonneg _) (norm_nonneg _))

/-- **Lower bound of Srebro–Shraibman**: `‖U Vᵀ‖_* ≤ (‖U‖_F² + ‖V‖_F²) / 2` for all factors. -/
theorem nuclearNorm_mul_transpose_le [DecidableEq n] (U : Matrix m k ℝ) (V : Matrix n k ℝ) :
    nuclearNorm (U * Vᵀ) ≤ (‖U‖ ^ 2 + ‖V‖ ^ 2) / 2 := by
  have h := nuclearNorm_mul_transpose_le_mul U V
  nlinarith [sq_nonneg (‖U‖ - ‖V‖)]

omit [Fintype k] in
/-- `(X D Eᵀ)ᵀ (X D Eᵀ) = E D (Xᵀ X) D Eᵀ`. -/
private theorem transpose_factor_mul_self {l : Type*} [Fintype l] (X : Matrix l (Fin p) ℝ)
    (d : Fin p → ℝ) (E : Matrix k (Fin p) ℝ) :
    (X * Matrix.diagonal d * Eᵀ)ᵀ * (X * Matrix.diagonal d * Eᵀ) =
      E * (Matrix.diagonal d * ((Xᵀ * X) * Matrix.diagonal d)) * Eᵀ := by
  simp only [transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]

/-- Balanced factors with `k ≥ p` columns from an SVD with `p` columns. -/
private theorem IsSVD.exists_factor [DecidableEq n] (hs : IsSVD A Uh σ Vh)
    (hk : p ≤ Fintype.card k) :
    ∃ (U : Matrix m k ℝ) (V : Matrix n k ℝ), A = U * Vᵀ ∧ ‖U‖ ^ 2 = nuclearNorm A ∧
      ‖V‖ ^ 2 = nuclearNorm A ∧ Uᵀ * U = Vᵀ * V := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin p) (β := k) (by simpa using hk)
  let E : Matrix k (Fin p) ℝ := (1 : Matrix k k ℝ).submatrix id e
  have hE : Eᵀ * E = 1 := by
    simp only [E, transpose_submatrix, transpose_one]
    rw [← submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.one_mul,
      submatrix_one _ e.injective]
  let d : Fin p → ℝ := fun i => √(σ i)
  have hdd : Matrix.diagonal d * Matrix.diagonal d = Matrix.diagonal σ := by
    rw [diagonal_mul_diagonal]
    congr 1
    ext i
    exact Real.mul_self_sqrt (hs.nonneg i)
  have hsum : ∑ i, d i ^ 2 = nuclearNorm A := by
    rw [hs.nuclearNorm_eq]
    exact Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hs.nonneg i)
  refine ⟨Uh * Matrix.diagonal d * Eᵀ, Vh * Matrix.diagonal d * Eᵀ, ?_,
    (sq_norm_mul_diagonal_mul hs.left_orth hE d).trans hsum,
    (sq_norm_mul_diagonal_mul hs.right_orth hE d).trans hsum, ?_⟩
  · have hexp : Uh * Matrix.diagonal d * Eᵀ * (Vh * Matrix.diagonal d * Eᵀ)ᵀ =
        Uh * (Matrix.diagonal d * ((Eᵀ * E) * Matrix.diagonal d)) * Vhᵀ := by
      simp only [transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
    rw [hexp, hE, Matrix.one_mul, hdd]
    exact hs.eq_mul
  · rw [transpose_factor_mul_self, transpose_factor_mul_self, hs.left_orth, hs.right_orth]

/-- **Attainment in Srebro–Shraibman**: every `A` of rank `≤ k` factors as `A = U Vᵀ` with
`‖U‖_F² = ‖V‖_F² = ‖A‖_*` and `UᵀU = VᵀV`.  The factors are the spectral factors `Û √Σ`, `V̂ √Σ`,
padded with zero columns. -/
theorem exists_factor_of_rank_le [DecidableEq n] (A : Matrix m n ℝ)
    (hk : A.rank ≤ Fintype.card k) :
    ∃ (U : Matrix m k ℝ) (V : Matrix n k ℝ), A = U * Vᵀ ∧ ‖U‖ ^ 2 = nuclearNorm A ∧
      ‖V‖ ^ 2 = nuclearNorm A ∧ Uᵀ * U = Vᵀ * V := by
  obtain ⟨Uh, σ, Vh, hs⟩ := exists_isSVD A
  exact hs.exists_factor hk

/-- **Srebro–Shraibman (2005)**, as used in arXiv 2209.13569, Sec. 3.3:
`‖W‖_* = min_{W = U Vᵀ} (‖U‖_F² + ‖V‖_F²) / 2`, the minimum over `U ∈ ℝ^{m×k}`, `V ∈ ℝ^{n×k}` for
every `k ≥ rank W`.  The paper only cites this fact.  Here `‖W‖_*` is `nuclearNorm`, the sum of the
singular values, and the minimum is attained (`IsLeast`).  For `k < rank W` the constraint set is
empty, so `k ≥ rank W` is necessary. -/
theorem isLeast_nuclearNorm [DecidableEq n] (W : Matrix m n ℝ) (hk : W.rank ≤ Fintype.card k) :
    IsLeast {c : ℝ | ∃ (U : Matrix m k ℝ) (V : Matrix n k ℝ),
      W = U * Vᵀ ∧ c = (‖U‖ ^ 2 + ‖V‖ ^ 2) / 2} (nuclearNorm W) := by
  constructor
  · obtain ⟨U, V, hW, hU, hV, -⟩ := exists_factor_of_rank_le (k := k) W hk
    exact ⟨U, V, hW, by rw [hU, hV]; ring⟩
  · rintro c ⟨U, V, hW, rfl⟩
    rw [hW]
    exact nuclearNorm_mul_transpose_le U V

/-- `‖X‖_F² = tr(Xᵀ X)`, for `Xᵀ X` diagonal. -/
private theorem sq_norm_eq_sum_of_transpose_mul_self {l : Type*} [Fintype l] {r : ℕ}
    {X : Matrix l (Fin r) ℝ} {d : Fin r → ℝ} (hX : Xᵀ * X = Matrix.diagonal d) :
    ‖X‖ ^ 2 = ∑ i, d i := by
  rw [← real_inner_self_eq_norm_sq, Frobenius.inner_eq_trace, hX, trace_diagonal]

/-- **The spectral factors attain the Srebro–Shraibman minimum** (arXiv 2209.13569, Sec. 3.2 and
3.3): `U = Û_{:r} √Σ_r`, `V = V̂_{:r} √Σ_r` satisfy `‖U‖_F² = ‖V‖_F² = ‖U Vᵀ‖_* = ∑_{i<r} σ_i`.
So the initialization of eq. (3) is a minimum-penalty factorization of `SVD_r(W)`. -/
theorem spectralFactor_attains_nuclearNorm [DecidableEq n] (hs : IsSVD A Uh σ Vh) {r : ℕ}
    (hr : r ≤ p) :
    ‖spectralFactor hr Uh σ‖ ^ 2 =
        nuclearNorm (spectralFactor hr Uh σ * (spectralFactor hr Vh σ)ᵀ) ∧
      ‖spectralFactor hr Vh σ‖ ^ 2 =
        nuclearNorm (spectralFactor hr Uh σ * (spectralFactor hr Vh σ)ᵀ) := by
  obtain ⟨h1, h2, h3, -⟩ := spectral_initialization hs hr
  have hs' : IsSVD (svdTrunc hr Uh σ Vh) (leadCols hr Uh) (leadVals hr σ) (leadCols hr Vh) :=
    ⟨transpose_leadCols_mul_self hs.left_orth hr, transpose_leadCols_mul_self hs.right_orth hr,
      fun i j hij => hs.antitone (show Fin.castLE hr i ≤ Fin.castLE hr j from hij),
      fun _ => hs.nonneg _, rfl⟩
  rw [h3, hs'.nuclearNorm_eq]
  exact ⟨sq_norm_eq_sum_of_transpose_mul_self h1, sq_norm_eq_sum_of_transpose_mul_self h2⟩

/-- The factored objective `L(U Vᵀ) + (λ/2) (‖U‖_F² + ‖V‖_F²)` of arXiv 2209.13569, Sec. 3.3. -/
noncomputable def factorObjective (L : Matrix m n ℝ → ℝ) (lam : ℝ) (U : Matrix m k ℝ)
    (V : Matrix n k ℝ) : ℝ :=
  L (U * Vᵀ) + lam / 2 * (‖U‖ ^ 2 + ‖V‖ ^ 2)

/-- The nuclear-norm regularized objective `L(W) + λ ‖W‖_*`. -/
noncomputable def nuclearObjective [DecidableEq n] (L : Matrix m n ℝ → ℝ) (lam : ℝ)
    (W : Matrix m n ℝ) : ℝ :=
  L W + lam * nuclearNorm W

omit [Fintype m] in
/-- `rank (U Vᵀ) ≤ k` for `k` columns. -/
private theorem rank_mul_transpose_le (U : Matrix m k ℝ) (V : Matrix n k ℝ) :
    (U * Vᵀ).rank ≤ Fintype.card k :=
  (rank_mul_le_left _ _).trans U.rank_le_card_width

/-- The factored objective dominates the nuclear-norm objective for `λ ≥ 0`. -/
private theorem nuclearObjective_le_factorObjective [DecidableEq n] (L : Matrix m n ℝ → ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) (U : Matrix m k ℝ) (V : Matrix n k ℝ) :
    nuclearObjective L lam (U * Vᵀ) ≤ factorObjective L lam U V := by
  have h := mul_le_mul_of_nonneg_left (nuclearNorm_mul_transpose_le U V) hlam
  simp only [nuclearObjective, factorObjective]
  linarith

/-- The two objectives agree at a penalty-minimal factorization. -/
private theorem exists_factorObjective_eq [DecidableEq n] (L : Matrix m n ℝ → ℝ) (lam : ℝ)
    {W : Matrix m n ℝ} (hW : W.rank ≤ Fintype.card k) :
    ∃ (U : Matrix m k ℝ) (V : Matrix n k ℝ), W = U * Vᵀ ∧
      factorObjective L lam U V = nuclearObjective L lam W := by
  obtain ⟨U, V, hUV, hU, hV, -⟩ := exists_factor_of_rank_le (k := k) W hW
  refine ⟨U, V, hUV, ?_⟩
  rw [factorObjective, nuclearObjective, ← hUV, hU, hV]
  ring

/-- **The factor penalty acts as nuclear-norm regularization: values** (arXiv 2209.13569, Sec. 3.3).
For every loss `L` and `λ ≥ 0`, `inf_{U,V} L(U Vᵀ) + (λ/2)(‖U‖_F² + ‖V‖_F²)` equals
`inf_{rank W ≤ k} L(W) + λ ‖W‖_*`.  The infima are `sInf` in `ℝ`, and no bound on `L` is assumed.
The paper states this informally, as a consequence of Srebro–Shraibman; the rank constraint
`rank W ≤ k` is implicit there. -/
theorem sInf_factorObjective_eq [DecidableEq n] (L : Matrix m n ℝ → ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    sInf (Set.range fun q : Matrix m k ℝ × Matrix n k ℝ => factorObjective L lam q.1 q.2) =
      sInf (nuclearObjective L lam '' {W : Matrix m n ℝ | W.rank ≤ Fintype.card k}) := by
  set S := Set.range fun q : Matrix m k ℝ × Matrix n k ℝ => factorObjective L lam q.1 q.2
  set T := nuclearObjective L lam '' {W : Matrix m n ℝ | W.rank ≤ Fintype.card k}
  have hlb : lowerBounds S = lowerBounds T := by
    ext c
    constructor
    · rintro hc _ ⟨W, hW, rfl⟩
      obtain ⟨U, V, -, h⟩ := exists_factorObjective_eq L lam (k := k) hW
      exact h ▸ hc ⟨(U, V), rfl⟩
    · rintro hc _ ⟨q, rfl⟩
      exact (hc ⟨_, rank_mul_transpose_le q.1 q.2, rfl⟩).trans
        (nuclearObjective_le_factorObjective L hlam q.1 q.2)
  have hS : S.Nonempty := Set.range_nonempty _
  have hT : T.Nonempty := ⟨_, 0, by simp, rfl⟩
  by_cases hbdd : BddBelow S
  · have hbdd' : BddBelow T := by
      obtain ⟨c, hc⟩ := hbdd
      exact ⟨c, hlb ▸ hc⟩
    have h1 : sInf S ∈ lowerBounds T := hlb ▸ fun _ hx => csInf_le hbdd hx
    have h2 : sInf T ∈ lowerBounds S := hlb.symm ▸ fun _ hx => csInf_le hbdd' hx
    exact le_antisymm (le_csInf hT h1) (le_csInf hS h2)
  · have hbdd' : ¬ BddBelow T := fun ⟨c, hc⟩ => hbdd ⟨c, hlb ▸ hc⟩
    rw [Real.sInf_of_not_bddBelow hbdd, Real.sInf_of_not_bddBelow hbdd']

/-- **The factor penalty acts as nuclear-norm regularization: minimizers** (arXiv 2209.13569,
Sec. 3.3).  For `λ ≥ 0`, `(U₀, V₀)` minimizes `L(U Vᵀ) + (λ/2)(‖U‖_F² + ‖V‖_F²)` over all
`U ∈ ℝ^{m×k}`, `V ∈ ℝ^{n×k}` iff `W₀ = U₀ V₀ᵀ` minimizes `L(W) + λ ‖W‖_*` over `rank W ≤ k` and the
two objectives agree at `(U₀, V₀)`, that is, the factorization of `W₀` is penalty-minimal. -/
theorem isMinimizer_factorObjective_iff [DecidableEq n] (L : Matrix m n ℝ → ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) (U₀ : Matrix m k ℝ) (V₀ : Matrix n k ℝ) :
    (∀ (U : Matrix m k ℝ) (V : Matrix n k ℝ),
        factorObjective L lam U₀ V₀ ≤ factorObjective L lam U V) ↔
      (∀ W : Matrix m n ℝ, W.rank ≤ Fintype.card k →
        nuclearObjective L lam (U₀ * V₀ᵀ) ≤ nuclearObjective L lam W) ∧
      factorObjective L lam U₀ V₀ = nuclearObjective L lam (U₀ * V₀ᵀ) := by
  constructor
  · intro h
    refine ⟨fun W hW => ?_, le_antisymm ?_ (nuclearObjective_le_factorObjective L hlam U₀ V₀)⟩
    · obtain ⟨U, V, -, hUV⟩ := exists_factorObjective_eq L lam (k := k) hW
      exact (nuclearObjective_le_factorObjective L hlam U₀ V₀).trans (hUV ▸ h U V)
    · obtain ⟨U, V, -, hUV⟩ := exists_factorObjective_eq L lam (k := k)
        (rank_mul_transpose_le U₀ V₀)
      exact hUV ▸ h U V
  · rintro ⟨h1, h2⟩ U V
    rw [h2]
    exact (h1 _ (rank_mul_transpose_le U V)).trans
      (nuclearObjective_le_factorObjective L hlam U V)

end Nuclear

end LeanDLRA.Literature.P2209_13569
