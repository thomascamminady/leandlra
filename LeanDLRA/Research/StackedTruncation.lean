import LeanDLRA.Research.LoewnerRank

/-!
# Ranks of a rectangular low-rank backward Euler scheme with stacked-factor truncation

The Sylvester problem `A' = -PA - AQ + G Hᵀ` (`P ⪰ 0`, `Q ⪰ 0`) is the off-diagonal block of the
Lyapunov problem with `diag(P, Q)` and the forcing `[G; H][G; H]ᵀ`. A low-rank scheme for the
`m × n` unknown that stores a factor pair `(L, R)`, `Y = L Rᵀ`, carries the positive semidefinite
matrix `W Wᵀ` of the stacked factor `W = [L; R]` along: its off-diagonal block is `Y`
(`toBlocks₁₂_mul_transpose`), a backward Euler step of the Lyapunov problem for `W Wᵀ` is a
backward Euler step of the Sylvester problem for `Y` (`toBlocks₁₂_add_smul_lyapunov`), the rank
of the block is at most the rank of the whole (`rank_toBlocks₁₂_le`), and the Frobenius norm of
the block of a symmetric matrix is at most `1/√2` times the norm of the whole
(`two_mul_norm_toBlocks₁₂_sq_le`).

*Stacked-factor truncation* replaces the step `Ŵ = [L̂; R̂]` by `W = Ŵ Z` with `Z Zᵀ ⪯ 1` (for
instance the orthogonal projector onto leading eigenvectors of the small Gram matrix
`ŴᵀŴ = L̂ᵀL̂ + R̂ᵀR̂`, `posSemidef_one_sub_mul_transpose`); the truncated singular value
decomposition of `L̂ R̂ᵀ` is in general not of this form. It only removes a positive semidefinite
part of `Ŵ Ŵᵀ` (`posSemidef_mul_transpose_sub_mul_transpose`). Therefore the computed iterates
stay below the untruncated lifted run `𝒳_j` in the Loewner order, and

  `rank (L_j R_jᵀ) ≤ rank_θ(𝒳_j)`

for every step size and every tolerance (`rank_le_epsRank_of_stacked_sylvester_run`), with the
error bound `√2 ‖X_j - L_j R_jᵀ‖ ≤ E_j` for the off-diagonal block `X_j` of `𝒳_j`, which is the
untruncated backward Euler run of the Sylvester problem (`norm_sub_le_of_stacked_sylvester_run`).
The proofs apply `LoewnerRank.rank_le_epsRank_of_truncated_lyapunov_run` and
`LoewnerRank.norm_sub_le_of_truncated_lyapunov_run` to the lifted run.

The truncated singular value decomposition of the iterate itself does not obey such a bound
with a fixed fraction of the tolerance: for every `c > 0` there is a scalar problem with a
sign change in which the truncated run has rank one at a step where the untruncated run is below
`c θ` (`exists_plain_rank_gt_epsRank`).
-/

open scoped Matrix LeanDLRA.Frobenius
open Matrix

namespace LeanDLRA.StackedTruncation

variable {m n k f : Type*}

/-! ### The off-diagonal block of a matrix on a sum type -/

/-- The rank of the off-diagonal block is at most the rank of the whole matrix. -/
theorem rank_toBlocks₁₂_le [Fintype m] [Fintype n] (M : Matrix (m ⊕ n) (m ⊕ n) ℝ) :
    M.toBlocks₁₂.rank ≤ M.rank := by
  classical
  have key : M.toBlocks₁₂ = fromCols (1 : Matrix m m ℝ) (0 : Matrix m n ℝ) *
      (M * fromRows (0 : Matrix m n ℝ) (1 : Matrix n n ℝ)) := by
    conv_rhs => rw [← Matrix.fromBlocks_toBlocks M, Matrix.fromBlocks_mul_fromRows,
      Matrix.fromCols_mul_fromRows]
    simp
  rw [key]
  exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_mul_le_left _ _)

/-- For a symmetric matrix, twice the squared Frobenius norm of the off-diagonal block is at
most the squared Frobenius norm of the whole matrix. -/
theorem two_mul_norm_toBlocks₁₂_sq_le [Fintype m] [Fintype n]
    {M : Matrix (m ⊕ n) (m ⊕ n) ℝ} (hM : Mᵀ = M) :
    2 * ‖M.toBlocks₁₂‖ ^ 2 ≤ ‖M‖ ^ 2 := by
  have hs : ∀ (i : m) (j : n), M (Sum.inr j) (Sum.inl i) = M (Sum.inl i) (Sum.inr j) := by
    intro i j
    have h := congrFun (congrFun hM (Sum.inl i)) (Sum.inr j)
    simpa [Matrix.transpose_apply] using h
  have e : ∑ j : n, ∑ i : m, M (Sum.inr j) (Sum.inl i) ^ 2
      = ∑ i : m, ∑ j : n, M (Sum.inl i) (Sum.inr j) ^ 2 := by
    rw [Finset.sum_comm]
    simp [hs]
  have h11 : 0 ≤ ∑ i : m, ∑ j : m, M (Sum.inl i) (Sum.inl j) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h22 : 0 ≤ ∑ i : n, ∑ j : n, M (Sum.inr i) (Sum.inr j) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum]
  simp only [Fintype.sum_sum_type, Finset.sum_add_distrib, Matrix.toBlocks₁₂, Matrix.of_apply]
  rw [e]
  linarith

/-- `√2 ‖M₁₂‖ ≤ ‖M‖` for a symmetric matrix `M` on a sum type. -/
theorem sqrt_two_mul_norm_toBlocks₁₂_le [Fintype m] [Fintype n]
    {M : Matrix (m ⊕ n) (m ⊕ n) ℝ} (hM : Mᵀ = M) :
    Real.sqrt 2 * ‖M.toBlocks₁₂‖ ≤ ‖M‖ := by
  have h := two_mul_norm_toBlocks₁₂_sq_le hM
  have h2 : (Real.sqrt 2 * ‖M.toBlocks₁₂‖) ^ 2 ≤ ‖M‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact h
  exact (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg _)) (norm_nonneg _)).mp h2

/-- The off-diagonal block of `W Wᵀ` for a stacked factor `W = [L; R]` is `L Rᵀ`. -/
theorem toBlocks₁₂_mul_transpose [Fintype k] (W : Matrix (m ⊕ n) k ℝ) :
    (W * Wᵀ).toBlocks₁₂ = W.toRows₁ * W.toRows₂ᵀ := by
  ext i j
  simp [Matrix.toBlocks₁₂, Matrix.toRows₁, Matrix.toRows₂, Matrix.mul_apply]

/-- The off-diagonal block of a backward Euler step of the Lyapunov equation with `diag(P, Q)`
is a backward Euler step of the Sylvester equation with `P` and `Q`. -/
theorem toBlocks₁₂_add_smul_lyapunov [Fintype m] [Fintype n] {P : Matrix m m ℝ} {Q : Matrix n n ℝ}
    {M G : Matrix (m ⊕ n) (m ⊕ n) ℝ} {h : ℝ}
    (hM : M + h • (fromBlocks P 0 0 Q * M + M * fromBlocks P 0 0 Q) = G) :
    M.toBlocks₁₂ + h • (P * M.toBlocks₁₂ + M.toBlocks₁₂ * Q) = G.toBlocks₁₂ := by
  rw [← hM]
  ext i j
  simp [Matrix.toBlocks₁₂, Matrix.mul_apply, Fintype.sum_sum_type]

/-- The Sylvester operator does not see a shift `σ` that is added to `P` and removed from `Q`
(used to balance the smallest eigenvalues of the two diagonal blocks of the lift). -/
theorem shift_mul_add_mul_shift [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (P : Matrix m m ℝ) (Q : Matrix n n ℝ) (B : Matrix m n ℝ) (σ : ℝ) :
    (P + σ • (1 : Matrix m m ℝ)) * B + B * (Q - σ • (1 : Matrix n n ℝ)) = P * B + B * Q := by
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]
  abel

/-- A block diagonal matrix with positive semidefinite blocks is positive semidefinite. -/
theorem posSemidef_fromBlocks_diag [Finite m] [Finite n] {P : Matrix m m ℝ} {Q : Matrix n n ℝ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : (fromBlocks P 0 0 Q).PosSemidef := by
  cases nonempty_fintype m
  cases nonempty_fintype n
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.IsHermitian.fromBlocks hP.isHermitian (by simp) hQ.isHermitian) fun x => ?_
  have h1 : 0 ≤ (x ∘ Sum.inl) ⬝ᵥ (P *ᵥ (x ∘ Sum.inl)) := by
    simpa using (Matrix.posSemidef_iff_dotProduct_mulVec.mp hP).2 (x ∘ Sum.inl)
  have h2 : 0 ≤ (x ∘ Sum.inr) ⬝ᵥ (Q *ᵥ (x ∘ Sum.inr)) := by
    simpa using (Matrix.posSemidef_iff_dotProduct_mulVec.mp hQ).2 (x ∘ Sum.inr)
  have e : star x ⬝ᵥ (fromBlocks P 0 0 Q *ᵥ x)
      = (x ∘ Sum.inl) ⬝ᵥ (P *ᵥ (x ∘ Sum.inl)) + (x ∘ Sum.inr) ⬝ᵥ (Q *ᵥ (x ∘ Sum.inr)) := by
    simp [Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]
  rw [e]
  exact add_nonneg h1 h2

/-! ### Stacked-factor truncation -/

section Truncation

variable {ι : Type*} [Fintype k]

/-- An orthogonal projector `Z Zᵀ` (`Z` with orthonormal columns) satisfies `Z Zᵀ ⪯ 1`. -/
theorem posSemidef_one_sub_mul_transpose [DecidableEq k] {r : Type*} [Fintype r]
    [DecidableEq r] {Z : Matrix k r ℝ} (hZ : Zᵀ * Z = 1) : (1 - Z * Zᵀ).PosSemidef := by
  have hidem : Z * Zᵀ * (Z * Zᵀ) = Z * Zᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Zᵀ, hZ, Matrix.one_mul]
  have e : (1 - Z * Zᵀ) = (1 - Z * Zᵀ)ᴴ * (1 - Z * Zᵀ) := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
      Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hidem]
    abel
  rw [e]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Stacked-factor truncation `W = Ŵ Z` with `Z Zᵀ ⪯ 1` removes a positive semidefinite part of
`Ŵ Ŵᵀ`. -/
theorem posSemidef_mul_transpose_sub_mul_transpose [DecidableEq k] (W : Matrix ι k ℝ)
    {Z : Matrix k k ℝ} (hZ : (1 - Z * Zᵀ).PosSemidef) : (W * Wᵀ - W * Z * (W * Z)ᵀ).PosSemidef := by
  have h := hZ.mul_mul_conjTranspose_same W
  have e : W * (1 - Z * Zᵀ) * Wᴴ = W * Wᵀ - W * Z * (W * Z)ᵀ := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rwa [e] at h

/-- The rank of `(Ŵ Z)(Ŵ Z)ᵀ` is at most the rank of `Z`. -/
theorem rank_mul_mul_transpose_le [Fintype ι] (W : Matrix ι k ℝ) (Z : Matrix k k ℝ) :
    (W * Z * (W * Z)ᵀ).rank ≤ Z.rank :=
  (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end Truncation

/-! ### The run -/

section Run

variable [Fintype m] [Fintype n] [Fintype k] [Fintype f] [DecidableEq k] {P : Matrix m m ℝ}
  {Q : Matrix n n ℝ} {Wf : Matrix (m ⊕ n) f ℝ}
  {h θ : ℝ} {N : ℕ} {X : ℕ → Matrix (m ⊕ n) (m ⊕ n) ℝ} {W Wh : ℕ → Matrix (m ⊕ n) k ℝ}
  {Z : ℕ → Matrix k k ℝ}

/-- **Ranks of a low-rank backward Euler run of a Sylvester equation with stacked-factor
truncation.** Let `P ⪰ 0`, `Q ⪰ 0`, let `Wf = [G; H]` be a stacked factor of the forcing `G Hᵀ`,
let `X` be the backward Euler run of the lifted Lyapunov problem, and let the scheme store
stacked factors `W_j = [L_j; R_j]`: `Ŵ_{j+1}` is a stacked factor of the lifted step from
`W_j W_jᵀ`, and `W_{j+1} = Ŵ_{j+1} Z_j` with `Z_j Z_jᵀ ⪯ 1` and
`rank Z_j ≤ rank_θ(Ŵ_{j+1} Ŵ_{j+1}ᵀ)`. Then the off-diagonal block of `X` is the backward Euler
run of `A' = -PA - AQ + G Hᵀ`, and the computed iterates `L_j R_jᵀ` have
`rank (L_j R_jᵀ) ≤ rank_θ(X_j)`, for every step size and every tolerance. -/
theorem rank_le_epsRank_of_stacked_sylvester_run (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (hh : 0 ≤ h) (hθ : 0 ≤ θ)
    (hX : ∀ j < N, X (j + 1) + h • (fromBlocks P 0 0 Q * X (j + 1)
      + X (j + 1) * fromBlocks P 0 0 Q) = X j + h • (Wf * Wfᵀ))
    (hWh : ∀ j < N, Wh (j + 1) * (Wh (j + 1))ᵀ + h • (fromBlocks P 0 0 Q
      * (Wh (j + 1) * (Wh (j + 1))ᵀ) + Wh (j + 1) * (Wh (j + 1))ᵀ * fromBlocks P 0 0 Q)
      = W j * (W j)ᵀ + h • (Wf * Wfᵀ))
    (hX0 : (X 0 - W 0 * (W 0)ᵀ).PosSemidef)
    (hW : ∀ j < N, W (j + 1) = Wh (j + 1) * Z j)
    (hZ : ∀ j < N, (1 - Z j * (Z j)ᵀ).PosSemidef)
    (hZrank : ∀ j < N, (Z j).rank ≤ epsRank θ (Wh (j + 1) * (Wh (j + 1))ᵀ)) :
    ∀ j < N, (X (j + 1)).toBlocks₁₂ + h • (P * (X (j + 1)).toBlocks₁₂
        + (X (j + 1)).toBlocks₁₂ * Q) = (X j).toBlocks₁₂ + h • (Wf.toRows₁ * Wf.toRows₂ᵀ) ∧
      ((W (j + 1)).toRows₁ * (W (j + 1)).toRows₂ᵀ).rank ≤ epsRank θ (X (j + 1)) ∧
      (X (j + 1) - W (j + 1) * (W (j + 1))ᵀ).PosSemidef := by
  have hpsd : ∀ V : Matrix (m ⊕ n) k ℝ, (V * Vᵀ).PosSemidef := fun V => by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose V
  have hF : (Wf * Wfᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose Wf
  have hrun := LoewnerRank.rank_le_epsRank_of_truncated_lyapunov_run
    (posSemidef_fromBlocks_diag hP hQ) hF hh hθ (X := X) (Y := fun j => W j * (W j)ᵀ)
    (Yh := fun j => Wh j * (Wh j)ᵀ) hX hWh (hpsd _) hX0 (fun j _ => hpsd _)
    (fun j hj => by
      rw [hW j hj]
      exact posSemidef_mul_transpose_sub_mul_transpose _ (hZ j hj))
    (fun j hj => by
      rw [hW j hj]
      exact (rank_mul_mul_transpose_le _ _).trans (hZrank j hj))
  intro j hj
  obtain ⟨-, -, hle, hr⟩ := hrun j hj
  refine ⟨?_, ?_, hle⟩
  · have h1 := toBlocks₁₂_add_smul_lyapunov (hX j hj)
    rw [h1, ← toBlocks₁₂_mul_transpose]
    rfl
  · rw [← toBlocks₁₂_mul_transpose]
    exact (rank_toBlocks₁₂_le _).trans hr

/-- **Error of a low-rank backward Euler run of a Sylvester equation with stacked-factor
truncation.** In the setting of `rank_le_epsRank_of_stacked_sylvester_run`, if `P ⪰ c`,
`Q ⪰ c ≥ 0` and every truncation changes `Ŵ Ŵᵀ` by at most `θ`, then the computed iterates
`L_j R_jᵀ` satisfy `√2 ‖X_j - L_j R_jᵀ‖ ≤ E_j` for the off-diagonal block `X_j` of the lifted
run and every sequence with `E₀ ≥ ‖X₀ - W₀ W₀ᵀ‖`, `E_{j+1} ≥ E_j / (1 + 2hc) + θ`. -/
theorem norm_sub_le_of_stacked_sylvester_run [DecidableEq m] [DecidableEq n] {c : ℝ}
    {E : ℕ → ℝ} (hP : (P - c • (1 : Matrix m m ℝ)).PosSemidef)
    (hQ : (Q - c • (1 : Matrix n n ℝ)).PosSemidef) (hh : 0 ≤ h) (hc : 0 ≤ c) (hθ : 0 ≤ θ)
    (hX : ∀ j < N, X (j + 1) + h • (fromBlocks P 0 0 Q * X (j + 1)
      + X (j + 1) * fromBlocks P 0 0 Q) = X j + h • (Wf * Wfᵀ))
    (hWh : ∀ j < N, Wh (j + 1) * (Wh (j + 1))ᵀ + h • (fromBlocks P 0 0 Q
      * (Wh (j + 1) * (Wh (j + 1))ᵀ) + Wh (j + 1) * (Wh (j + 1))ᵀ * fromBlocks P 0 0 Q)
      = W j * (W j)ᵀ + h • (Wf * Wfᵀ))
    (hX0 : (X 0 - W 0 * (W 0)ᵀ).PosSemidef)
    (hW : ∀ j < N, W (j + 1) = Wh (j + 1) * Z j)
    (hZ : ∀ j < N, (1 - Z j * (Z j)ᵀ).PosSemidef)
    (hZrank : ∀ j < N, (Z j).rank ≤ epsRank θ (Wh (j + 1) * (Wh (j + 1))ᵀ))
    (hT : ∀ j < N, ‖Wh (j + 1) * (Wh (j + 1))ᵀ - W (j + 1) * (W (j + 1))ᵀ‖ ≤ θ)
    (hE0 : ‖X 0 - W 0 * (W 0)ᵀ‖ ≤ E 0)
    (hE : ∀ j < N, E j / (1 + 2 * h * c) + θ ≤ E (j + 1)) :
    ∀ j ≤ N, Real.sqrt 2 * ‖(X j).toBlocks₁₂ - (W j).toRows₁ * (W j).toRows₂ᵀ‖ ≤ E j := by
  have hone : (c • (1 : Matrix m m ℝ)).PosSemidef := Matrix.PosSemidef.one.smul hc
  have hone' : (c • (1 : Matrix n n ℝ)).PosSemidef := Matrix.PosSemidef.one.smul hc
  have hP0 : P.PosSemidef := by simpa using hP.add hone
  have hQ0 : Q.PosSemidef := by simpa using hQ.add hone'
  have hPc : (fromBlocks P 0 0 Q - c • (1 : Matrix (m ⊕ n) (m ⊕ n) ℝ)).PosSemidef := by
    have h1 := posSemidef_fromBlocks_diag hP hQ
    have e : fromBlocks P 0 0 Q - c • (1 : Matrix (m ⊕ n) (m ⊕ n) ℝ)
        = fromBlocks (P - c • (1 : Matrix m m ℝ)) 0 0 (Q - c • (1 : Matrix n n ℝ)) := by
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, sub_eq_add_neg, Matrix.fromBlocks_neg,
        Matrix.fromBlocks_add]
      simp [sub_eq_add_neg]
    rwa [e]
  have hnorm := LoewnerRank.norm_sub_le_of_truncated_lyapunov_run hPc hh hc (X := X)
    (Y := fun j => W j * (W j)ᵀ) (Yh := fun j => Wh j * (Wh j)ᵀ) hX hWh hT hE0 hE
  have hord := rank_le_epsRank_of_stacked_sylvester_run hP0 hQ0 hh hθ hX hWh hX0 hW hZ hZrank
  have hsymm : ∀ j ≤ N, (X j - W j * (W j)ᵀ)ᵀ = X j - W j * (W j)ᵀ := by
    intro j hj
    have hp : (X j - W j * (W j)ᵀ).PosSemidef := by
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · exact hX0
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        exact (hord i hj).2.2
    have := hp.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  intro j hj
  have h1 := sqrt_two_mul_norm_toBlocks₁₂_le (hsymm j hj)
  have e : (X j - W j * (W j)ᵀ).toBlocks₁₂
      = (X j).toBlocks₁₂ - (W j).toRows₁ * (W j).toRows₂ᵀ := by
    rw [← toBlocks₁₂_mul_transpose]
    rfl
  rw [e] at h1
  exact h1.trans (hnorm j hj)

end Run

/-! ### Non-vacuity and a counterexample for the truncated singular value decomposition -/

/-- The hypotheses of `rank_le_epsRank_of_stacked_sylvester_run` and of
`norm_sub_le_of_stacked_sylvester_run` can hold with a truncation that changes the iterate:
`P = Q = 1` on `1 × 1` matrices, `G = H = 1`, `h = 4`, `c = 1`, `θ = 1`, start at zero; the
lifted step `(4/9) [1; 1][1; 1]ᵀ` is truncated to zero. -/
example : ∃ (X : ℕ → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)
    (W Wh : ℕ → Matrix (Fin 1 ⊕ Fin 1) (Fin 1) ℝ) (Wf : Matrix (Fin 1 ⊕ Fin 1) (Fin 1) ℝ)
    (Z : ℕ → Matrix (Fin 1) (Fin 1) ℝ) (E : ℕ → ℝ),
    ((1 : Matrix (Fin 1) (Fin 1) ℝ) - (1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosSemidef ∧
    (∀ j < 1, X (j + 1) + (4 : ℝ) • (fromBlocks 1 0 0 1 * X (j + 1)
      + X (j + 1) * fromBlocks 1 0 0 1) = X j + (4 : ℝ) • (Wf * Wfᵀ)) ∧
    (∀ j < 1, Wh (j + 1) * (Wh (j + 1))ᵀ + (4 : ℝ) • (fromBlocks 1 0 0 1
      * (Wh (j + 1) * (Wh (j + 1))ᵀ) + Wh (j + 1) * (Wh (j + 1))ᵀ * fromBlocks 1 0 0 1)
      = W j * (W j)ᵀ + (4 : ℝ) • (Wf * Wfᵀ)) ∧
    (X 0 - W 0 * (W 0)ᵀ).PosSemidef ∧ (∀ j < 1, W (j + 1) = Wh (j + 1) * Z j) ∧
    (∀ j < 1, (1 - Z j * (Z j)ᵀ).PosSemidef) ∧
    (∀ j < 1, (Z j).rank ≤ epsRank 1 (Wh (j + 1) * (Wh (j + 1))ᵀ)) ∧
    (∀ j < 1, ‖Wh (j + 1) * (Wh (j + 1))ᵀ - W (j + 1) * (W (j + 1))ᵀ‖ ≤ 1) ∧
    ‖X 0 - W 0 * (W 0)ᵀ‖ ≤ E 0 ∧ (∀ j < 1, E j / (1 + 2 * 4 * 1) + 1 ≤ E (j + 1)) ∧
    (X 1).toBlocks₁₂ ≠ (W 1).toRows₁ * (W 1).toRows₂ᵀ := by
  obtain ⟨w, hw⟩ : ∃ w : Matrix (Fin 1 ⊕ Fin 1) (Fin 1) ℝ, w = Matrix.of fun _ _ => 1 :=
    ⟨_, rfl⟩
  have hww : w * wᵀ = Matrix.of fun _ _ => 1 := by
    subst hw
    ext i j
    simp [Matrix.mul_apply]
  have hnorm : ‖w * wᵀ‖ ≤ 2 := by
    have h4 : ‖w * wᵀ‖ ^ 2 = 4 := by
      rw [hww, Frobenius.norm_sq_eq_sum]
      norm_num [Fintype.sum_sum_type]
    nlinarith [norm_nonneg (w * wᵀ)]
  refine ⟨fun j => ((j : ℝ) * (4 / 9)) • (w * wᵀ), fun _ => 0, fun j => ((j : ℝ) * (2 / 3)) • w,
    w, fun _ => 0, fun j => (j : ℝ), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using Matrix.PosSemidef.zero
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp only [Nat.cast_zero, zero_mul, zero_smul, zero_add, Nat.cast_one, one_mul,
      Matrix.fromBlocks_one, Matrix.mul_one]
    module
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp only [zero_add, Nat.cast_one, one_mul, Matrix.fromBlocks_one, Matrix.mul_one,
      Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.zero_mul]
    module
  · simpa using Matrix.PosSemidef.zero
  · intro j _; simp
  · intro j _; simpa using Matrix.PosSemidef.one
  · intro j _; simp
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp only [zero_add, Nat.cast_one, one_mul, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Matrix.zero_mul, sub_zero]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    nlinarith [norm_nonneg (w * wᵀ)]
  · simp
  · intro j hj
    obtain rfl : j = 0 := by omega
    norm_num
  · intro h0
    have h1 := congrFun (congrFun h0 0) 0
    rw [hww] at h1
    norm_num [Matrix.toBlocks₁₂, Matrix.toRows₁, Matrix.toRows₂, Matrix.mul_apply] at h1

/-- **The truncated singular value decomposition does not obey a rank bound with a fixed
fraction of the tolerance.** For every `c > 0` there is a scalar problem
`A' = -A/2 - A/2 + F` (`1 × 1` matrices, `P = Q = 1/2`) with a step size `h`, a tolerance `θ`
and a start with `|A₀| > θ` of the opposite sign to `F`, such that the backward Euler run `Y`
with truncation at `θ` (the step `Ŷ` is replaced by zero if `‖Ŷ‖ ≤ θ`) has rank one at the
second step, while the untruncated run satisfies `‖X₂‖ ≤ c θ`, that is `rank_{cθ}(X₂) = 0`:
the first step lands on `-θ` and is truncated, so the truncated run is ahead of the
untruncated one by `θ / (1 + h)` when both become positive. -/
theorem exists_plain_rank_gt_epsRank {c : ℝ} (hc : 0 < c) :
    ∃ (h θ : ℝ) (F : Matrix (Fin 1) (Fin 1) ℝ) (X Y Yh : ℕ → Matrix (Fin 1) (Fin 1) ℝ),
      0 < h ∧ 0 < θ ∧ X 0 = Y 0 ∧
      (∀ j < 2, X (j + 1) + h • (((1 / 2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * X (j + 1)
        + X (j + 1) * ((1 / 2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))) = X j + h • F) ∧
      (∀ j < 2, Yh (j + 1) + h • (((1 / 2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * Yh (j + 1)
        + Yh (j + 1) * ((1 / 2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))) = Y j + h • F) ∧
      (∀ j < 2, Y (j + 1) = if ‖Yh (j + 1)‖ ≤ θ then 0 else Yh (j + 1)) ∧
      epsRank (c * θ) (X 2) = 0 ∧ (Y 2).rank = 1 := by
  have hone : ‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖ = 1 := by
    have h : ‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖ ^ 2 = 1 := by
      rw [Frobenius.norm_sq_eq_sum]; simp
    nlinarith [norm_nonneg (1 : Matrix (Fin 1) (Fin 1) ℝ)]
  have hn : ∀ r : ℝ, ‖r • (1 : Matrix (Fin 1) (Fin 1) ℝ)‖ = |r| := fun r => by
    rw [norm_smul, hone, mul_one, Real.norm_eq_abs]
  have hF : (c / 4) • (((1 + c / 2) * (1 + c / 4) / (c / 4)) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      = ((1 + c / 2) * (1 + c / 4)) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    rw [smul_smul]
    congr 1
    field_simp
  obtain ⟨x, hx0, hx1, hx2⟩ : ∃ x : ℕ → ℝ, x 0 = -(1 + c / 4) ^ 2 - (1 + c / 2) * (1 + c / 4) ∧
      x 1 = -(1 + c / 4) ∧ x 2 = c / 2 :=
    ⟨fun j => if j = 0 then -(1 + c / 4) ^ 2 - (1 + c / 2) * (1 + c / 4)
      else if j = 1 then -(1 + c / 4) else c / 2, by simp, by simp, by simp⟩
  obtain ⟨y, hy0, hy1, hy2⟩ : ∃ y : ℕ → ℝ, y 0 = -(1 + c / 4) ^ 2 - (1 + c / 2) * (1 + c / 4) ∧
      y 1 = 0 ∧ y 2 = 1 + c / 2 :=
    ⟨fun j => if j = 0 then -(1 + c / 4) ^ 2 - (1 + c / 2) * (1 + c / 4)
      else if j = 1 then 0 else 1 + c / 2, by simp, by simp, by simp⟩
  obtain ⟨z, hz1, hz2⟩ : ∃ z : ℕ → ℝ, z 1 = -(1 + c / 4) ∧ z 2 = 1 + c / 2 :=
    ⟨fun j => if j = 1 then -(1 + c / 4) else 1 + c / 2, by simp, by simp⟩
  refine ⟨c / 4, 1 + c / 4, ((1 + c / 2) * (1 + c / 4) / (c / 4)) • 1, fun j => x j • 1,
    fun j => y j • 1, fun j => z j • 1, by positivity, by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hx0, hy0]
  · intro j hj
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · simp only [zero_add, hx0, hx1, hF, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]
      module
    · simp only [Nat.reduceAdd, hx1, hx2, hF, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]
      module
  · intro j hj
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · simp only [zero_add, hy0, hz1, hF, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]
      module
    · simp only [Nat.reduceAdd, hy1, hz2, hF, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]
      module
  · intro j hj
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · have hle : ‖(-(1 + c / 4)) • (1 : Matrix (Fin 1) (Fin 1) ℝ)‖ ≤ 1 + c / 4 := by
        rw [hn, abs_neg, abs_of_pos (by positivity)]
      simp only [zero_add, hy1, hz1, hle, ↓reduceIte, zero_smul]
    · have hlt : ¬ ‖(1 + c / 2) • (1 : Matrix (Fin 1) (Fin 1) ℝ)‖ ≤ 1 + c / 4 := by
        rw [hn, abs_of_pos (by positivity), not_le]
        linarith
      simp only [Nat.reduceAdd, hy2, hz2, hlt, ↓reduceIte]
  · simp only [hx2]
    refine Nat.le_zero.mp (epsRank_le_of_norm_sub_le (Y := 0) Matrix.rank_zero.le ?_)
    rw [sub_zero, hn, abs_of_pos (by positivity)]
    nlinarith [mul_pos hc hc]
  · simp only [hy2]
    have hu : IsUnit ((1 + c / 2) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
      rw [Matrix.isUnit_iff_isUnit_det]
      have hpos : (0 : ℝ) < 1 + c / 2 := by positivity
      simp [hpos.ne']
    rw [Matrix.rank_of_isUnit _ hu]
    simp

end LeanDLRA.StackedTruncation
