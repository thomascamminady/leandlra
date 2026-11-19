import LeanDLRA.Matrix.LowRankDistance

/-!
# Ranks of truncated backward Euler runs through the Loewner order

For symmetric positive semidefinite matrices the `ε`-rank is monotone in the Loewner order:
if `0 ⪯ Y ⪯ X`, then `distLR r Y ≤ distLR r X` for every `r`
(`distLR_le_distLR_of_posSemidef`) and `rank_ε(Y) ≤ rank_ε(X)`
(`epsRank_le_epsRank_of_posSemidef`). The proof needs no eigenvalues: for a best approximation
`Z₀` of `X` of rank `≤ r` with row space spanned by `V`, and a Gram factorisation `Y = MᵀM`, the
generalised Schur complement `S = NᵀN`, `N = M - U Uᵀ M` with `U` an orthonormal basis of the
range of `M V`, satisfies `0 ⪯ S ⪯ Y`, `rank (Y - S) ≤ r`, `S V = 0`, and therefore
`‖S‖² ≤ ⟪S, X - Z₀⟫` (`exists_posSemidef_rank_le_norm_sub_le`). The same construction gives a
positive semidefinite best approximation below `Y` (`exists_posSemidef_truncation`).

The backward Euler step of the differential Lyapunov equation `A' = -PA - AP + F` with `P ⪰ 0`,
`X₁ + h (P X₁ + X₁ P) = X₀ + h F`, is monotone in the Loewner order
(`posSemidef_of_add_smul_lyapunov`) and a contraction with factor `1 / (1 + 2hc)` if `P ⪰ c`
(`mul_norm_le_of_add_smul_lyapunov`). A truncation `Y_{j+1}` of the step `Ŷ_{j+1}` from `Y_j`
with `0 ⪯ Y_{j+1} ⪯ Ŷ_{j+1}` and `rank Y_{j+1} ≤ rank_θ(Ŷ_{j+1})` (the truncated eigenvalue
decomposition at the tolerance rank) therefore stays below the untruncated run `X_j`, and

  `rank Y_j ≤ rank_θ(X_j)`

for every step size and every tolerance (`rank_le_epsRank_of_truncated_lyapunov_run`); the error
obeys `‖X_j - Y_j‖ ≤ E_j` for every solution of `E_{j+1} ≥ E_j / (1 + 2hc) + θ`
(`norm_sub_le_of_truncated_lyapunov_run`). In contrast to the recompression lemma of Bachmayr
and Dahmen (arXiv 1304.7796, `epsRank_sandwich`), the tolerance need not exceed the accumulated
error. The Sylvester problem `A' = -PA - AQ + G Hᵀ` is the off-diagonal block of the Lyapunov
problem with `diag(P, Q)` and the forcing `[G; H][G; H]ᵀ`.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius
open Matrix

namespace LeanDLRA.LoewnerRank

variable {n : Type*} [Fintype n]

/-! ### The Frobenius inner product of positive semidefinite matrices -/

/-- The Frobenius inner product of a Gram matrix `NᵀN` and a positive semidefinite matrix is
nonnegative. -/
theorem inner_transpose_mul_self_nonneg {k : Type*} [Fintype k] (N : Matrix k n ℝ)
    {B : Matrix n n ℝ} (hB : B.PosSemidef) : 0 ≤ ⟪Nᵀ * N, B⟫ := by
  have h := (hB.mul_mul_conjTranspose_same N).trace_nonneg
  rw [Frobenius.inner_mul_left, Matrix.transpose_transpose, Frobenius.inner_eq_trace,
    Matrix.trace_mul_comm]
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-- `⟪B Z, Z⟫ ≥ 0` for positive semidefinite `B`. -/
theorem inner_mul_self_nonneg_of_posSemidef {k : Type*} [Fintype k] {B : Matrix n n ℝ}
    (hB : B.PosSemidef) (Z : Matrix n k ℝ) : 0 ≤ ⟪B * Z, Z⟫ := by
  have h := inner_transpose_mul_self_nonneg Zᵀ hB
  rw [Matrix.transpose_transpose, real_inner_comm] at h
  rwa [Frobenius.inner_mul_right]

/-- `⟪Z B, Z⟫ ≥ 0` for positive semidefinite `B`. -/
theorem inner_self_mul_nonneg_of_posSemidef {k : Type*} [Fintype k] {B : Matrix n n ℝ}
    (hB : B.PosSemidef) (Z : Matrix k n ℝ) : 0 ≤ ⟪Z * B, Z⟫ := by
  have h := inner_transpose_mul_self_nonneg Z hB
  rw [real_inner_comm] at h
  rwa [Frobenius.inner_mul_left]

/-! ### Monotonicity of the low-rank distance in the Loewner order -/

/-- **Positive semidefinite approximation below a dominated matrix.** If `0 ⪯ Y ⪯ X`, there is
a positive semidefinite `Z ⪯ Y` of rank `≤ r` with `‖Y - Z‖ ≤ distLR r X`. -/
theorem exists_posSemidef_rank_le_norm_sub_le {X Y : Matrix n n ℝ} (hY : Y.PosSemidef)
    (hXY : (X - Y).PosSemidef) (r : ℕ) :
    ∃ Z : Matrix n n ℝ, Z.PosSemidef ∧ (Y - Z).PosSemidef ∧ Z.rank ≤ r ∧
      ‖Y - Z‖ ≤ distLR r X := by
  classical
  rcases le_or_gt Y.rank r with hr | hr
  · refine ⟨Y, hY, ?_, hr, ?_⟩
    · rw [sub_self]; exact Matrix.PosSemidef.zero
    · rw [sub_self, norm_zero]; exact distLR_nonneg
  obtain ⟨k, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hY
  obtain ⟨M, hYM⟩ : ∃ M : Matrix (Fin k) n ℝ, Y = Mᵀ * M := by
    refine ⟨Matrix.of fun i a => v i a, ?_⟩
    rw [hv]
    ext a b
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.sum_apply]
  have hrn : r ≤ Fintype.card n := hr.le.trans Y.rank_le_card_width
  have hrk : r ≤ Fintype.card (Fin k) := by
    refine hr.le.trans ?_
    rw [hYM]
    exact (Matrix.rank_mul_le_right _ _).trans M.rank_le_card_height
  obtain ⟨Z₀, hZ₀r, hZ₀⟩ := exists_best_approx r X
  obtain ⟨V, -, hVZ⟩ := exists_orthonormal_capture Z₀ᵀ (by rwa [Matrix.rank_transpose]) hrn
  have hZV : Z₀ * V * Vᵀ = Z₀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hVZ
  obtain ⟨U, hU, hUM⟩ := exists_orthonormal_capture (M * V)
    ((Matrix.rank_mul_le_right _ _).trans (by simpa using V.rank_le_card_width)) hrk
  have hAt : (Uᵀ * M)ᵀ = Mᵀ * U := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hNt : (M - U * (Uᵀ * M))ᵀ = Mᵀ - (Uᵀ * M)ᵀ * Uᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_mul]
  have hNN : (M - U * (Uᵀ * M))ᵀ * (M - U * (Uᵀ * M)) = Y - (Uᵀ * M)ᵀ * (Uᵀ * M) := by
    have e1 : Mᵀ * (U * (Uᵀ * M)) = (Uᵀ * M)ᵀ * (Uᵀ * M) := by
      rw [← Matrix.mul_assoc, hAt]
    have e2 : (Uᵀ * M)ᵀ * Uᵀ * M = (Uᵀ * M)ᵀ * (Uᵀ * M) := by rw [Matrix.mul_assoc]
    have e3 : (Uᵀ * M)ᵀ * Uᵀ * (U * (Uᵀ * M)) = (Uᵀ * M)ᵀ * (Uᵀ * M) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul]
    rw [hNt, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, e1, e2, e3, hYM]
    abel
  have hNV : (M - U * (Uᵀ * M)) * V = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc U, hUM, sub_self]
  have hZpsd : ((Uᵀ * M)ᵀ * (Uᵀ * M)).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self (Uᵀ * M)
  have hSpsd : ((M - U * (Uᵀ * M))ᵀ * (M - U * (Uᵀ * M))).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self (M - U * (Uᵀ * M))
  refine ⟨(Uᵀ * M)ᵀ * (Uᵀ * M), hZpsd, by rw [← hNN]; exact hSpsd,
    (Matrix.rank_mul_le_right _ _).trans
      ((Uᵀ * M).rank_le_card_height.trans (by simp)), ?_⟩
  rw [← hNN, ← hZ₀]
  have hSZ : ⟪(M - U * (Uᵀ * M))ᵀ * (M - U * (Uᵀ * M)), Z₀⟫ = 0 := by
    rw [← hZV, Frobenius.inner_mul_right', Matrix.transpose_transpose, Matrix.mul_assoc _ _ V,
      hNV, Matrix.mul_zero, inner_zero_left]
  have hdiff : X - Z₀ - (M - U * (Uᵀ * M))ᵀ * (M - U * (Uᵀ * M))
      = (X - Y) + (Uᵀ * M)ᵀ * (Uᵀ * M) - Z₀ := by
    rw [hNN]; abel
  have h1 : ‖(M - U * (Uᵀ * M))ᵀ * (M - U * (Uᵀ * M))‖ ^ 2
      ≤ ‖(M - U * (Uᵀ * M))ᵀ * (M - U * (Uᵀ * M))‖ * ‖X - Z₀‖ := by
    rw [← real_inner_self_eq_norm_sq]
    refine le_trans ?_ (real_inner_le_norm _ _)
    rw [← sub_nonneg, ← inner_sub_right, hdiff, inner_sub_right, inner_add_right, hSZ, sub_zero]
    exact add_nonneg (inner_transpose_mul_self_nonneg _ hXY)
      (inner_transpose_mul_self_nonneg _ hZpsd)
  by_contra hc
  rw [not_le] at hc
  have hpos : 0 < ‖(M - U * (Uᵀ * M))ᵀ * (M - U * (Uᵀ * M))‖ :=
    lt_of_le_of_lt (norm_nonneg _) hc
  have h2 := mul_lt_mul_of_pos_left hc hpos
  rw [sq] at h1
  linarith

/-- **The low-rank distance is monotone in the Loewner order**: `0 ⪯ Y ⪯ X` implies
`distLR r Y ≤ distLR r X` for every `r`. -/
theorem distLR_le_distLR_of_posSemidef {X Y : Matrix n n ℝ} (hY : Y.PosSemidef)
    (hXY : (X - Y).PosSemidef) (r : ℕ) : distLR r Y ≤ distLR r X := by
  obtain ⟨Z, -, -, hZr, hZ⟩ := exists_posSemidef_rank_le_norm_sub_le hY hXY r
  exact (distLR_le_norm_sub hZr).trans hZ

/-- **The `ε`-rank is monotone in the Loewner order**: `0 ⪯ Y ⪯ X` implies
`rank_ε(Y) ≤ rank_ε(X)`. -/
theorem epsRank_le_epsRank_of_posSemidef {X Y : Matrix n n ℝ} (hY : Y.PosSemidef)
    (hXY : (X - Y).PosSemidef) {ε : ℝ} (hε : 0 ≤ ε) : epsRank ε Y ≤ epsRank ε X :=
  epsRank_le_of_distLR_le ((distLR_le_distLR_of_posSemidef hY hXY _).trans (distLR_epsRank_le hε))

/-- Perturbed form: if `0 ⪯ Y ⪯ X + G` with `‖G‖ ≤ e ≤ ε`, then
`rank_ε(Y) ≤ rank_{ε - e}(X)`. -/
theorem epsRank_le_epsRank_sub_of_posSemidef {X Y G : Matrix n n ℝ} (hY : Y.PosSemidef)
    (hXY : (X + G - Y).PosSemidef) {ε e : ℝ} (hG : ‖G‖ ≤ e) (he : e ≤ ε) :
    epsRank ε Y ≤ epsRank (ε - e) X :=
  (epsRank_le_epsRank_of_posSemidef hY hXY ((norm_nonneg G).trans (hG.trans he))).trans
    (epsRank_le_sub he (by simpa using hG))

/-- **Positive semidefinite truncation.** A positive semidefinite `Y` has a positive
semidefinite approximation `Z ⪯ Y` of rank at most the `θ`-rank within the tolerance `θ`. -/
theorem exists_posSemidef_truncation {Y : Matrix n n ℝ} (hY : Y.PosSemidef) {θ : ℝ}
    (hθ : 0 ≤ θ) :
    ∃ Z : Matrix n n ℝ, Z.PosSemidef ∧ (Y - Z).PosSemidef ∧ Z.rank ≤ epsRank θ Y ∧
      ‖Y - Z‖ ≤ θ := by
  obtain ⟨Z, h1, h2, h3, h4⟩ := exists_posSemidef_rank_le_norm_sub_le hY
    (by rw [sub_self]; exact Matrix.PosSemidef.zero) (epsRank θ Y)
  exact ⟨Z, h1, h2, h3, h4.trans (distLR_epsRank_le hθ)⟩

/-! ### The backward Euler step of a Lyapunov equation -/

/-- **Contraction of the Lyapunov resolvent.** If `P ⪰ c` and
`X + h (P X + X P) = G`, `h ≥ 0`, then `(1 + 2hc) ‖X‖ ≤ ‖G‖`. -/
theorem mul_norm_le_of_add_smul_lyapunov [DecidableEq n] {P X G : Matrix n n ℝ} {h c : ℝ}
    (hP : (P - c • (1 : Matrix n n ℝ)).PosSemidef) (hh : 0 ≤ h)
    (hX : X + h • (P * X + X * P) = G) : (1 + 2 * h * c) * ‖X‖ ≤ ‖G‖ := by
  have h1 : 0 ≤ ⟪P * X, X⟫ - c * ‖X‖ ^ 2 := by
    have := inner_mul_self_nonneg_of_posSemidef hP X
    rwa [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq] at this
  have h2 : 0 ≤ ⟪X * P, X⟫ - c * ‖X‖ ^ 2 := by
    have := inner_self_mul_nonneg_of_posSemidef hP X
    rwa [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq] at this
  have h3 : ⟪G, X⟫ = ‖X‖ ^ 2 + h * (⟪P * X, X⟫ + ⟪X * P, X⟫) := by
    rw [← hX, inner_add_left, real_inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq]
  have h4 : ⟪G, X⟫ ≤ ‖G‖ * ‖X‖ := real_inner_le_norm _ _
  have h5 : (1 + 2 * h * c) * ‖X‖ ^ 2 ≤ ‖G‖ * ‖X‖ := by
    nlinarith [mul_nonneg hh h1, mul_nonneg hh h2]
  by_contra hcon
  rw [not_le] at hcon
  have hXpos : 0 < ‖X‖ := by
    by_contra h0
    have h0' : ‖X‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
    rw [h0', mul_zero] at hcon
    exact absurd hcon (not_lt.mpr (norm_nonneg _))
  have h6 := mul_lt_mul_of_pos_right hcon hXpos
  nlinarith

/-- **The Lyapunov resolvent is positive.** If `P ⪰ 0`, `G ⪰ 0`, `h ≥ 0` and
`X + h (P X + X P) = G`, then `X ⪰ 0`. -/
theorem posSemidef_of_add_smul_lyapunov {P X G : Matrix n n ℝ} {h : ℝ} (hP : P.PosSemidef)
    (hG : G.PosSemidef) (hh : 0 ≤ h) (hX : X + h • (P * X + X * P) = G) : X.PosSemidef := by
  classical
  have hPt : Pᵀ = P := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hP.isHermitian.eq
  have hGt : Gᵀ = G := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hG.isHermitian.eq
  have hXt : Xᵀ = X := by
    have hT : Xᵀ + h • (P * Xᵀ + Xᵀ * P) = G := by
      have := congrArg Matrix.transpose hX
      rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_add,
        Matrix.transpose_mul, Matrix.transpose_mul, hPt, hGt] at this
      rw [← this]; abel_nf
    have hD : (Xᵀ - X) + h • (P * (Xᵀ - X) + (Xᵀ - X) * P) = 0 := by
      have e : (0 : Matrix n n ℝ)
          = (Xᵀ + h • (P * Xᵀ + Xᵀ * P)) - (X + h • (P * X + X * P)) := by
        rw [hT, hX, sub_self]
      rw [e, Matrix.mul_sub, Matrix.sub_mul]
      module
    have hP0 : (P - (0 : ℝ) • (1 : Matrix n n ℝ)).PosSemidef := by simpa using hP
    have := mul_norm_le_of_add_smul_lyapunov hP0 hh hD
    rw [norm_zero] at this
    have h0 : ‖Xᵀ - X‖ = 0 := le_antisymm (by nlinarith) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  have hXh : X.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hXt]
  rw [hXh.posSemidef_iff_eigenvalues_nonneg]
  intro i
  have hv := hXh.mulVec_eigenvectorBasis i
  have hlam := hXh.eigenvalues_eq i
  have hq := hP.dotProduct_mulVec_nonneg ⇑(hXh.eigenvectorBasis i)
  have hg := hG.dotProduct_mulVec_nonneg ⇑(hXh.eigenvectorBasis i)
  simp only [star_trivial, RCLike.re_to_real] at hlam hq hg
  have e1 : (P * X) *ᵥ ⇑(hXh.eigenvectorBasis i)
      = hXh.eigenvalues i • (P *ᵥ ⇑(hXh.eigenvectorBasis i)) := by
    rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have e2 : ⇑(hXh.eigenvectorBasis i) ᵥ* X
      = hXh.eigenvalues i • ⇑(hXh.eigenvectorBasis i) := by
    rw [← Matrix.mulVec_transpose, hXt, hv]
  have e3 : ⇑(hXh.eigenvectorBasis i) ⬝ᵥ (X * P) *ᵥ ⇑(hXh.eigenvectorBasis i)
      = hXh.eigenvalues i
        * (⇑(hXh.eigenvectorBasis i) ⬝ᵥ P *ᵥ ⇑(hXh.eigenvectorBasis i)) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, e2, smul_dotProduct, smul_eq_mul]
  rw [← hX, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
    Matrix.add_mulVec, dotProduct_add, e1, dotProduct_smul, e3, ← hlam, smul_eq_mul,
    smul_eq_mul] at hg
  change 0 ≤ hXh.eigenvalues i
  by_contra hneg
  rw [not_le] at hneg
  nlinarith [mul_nonneg hh hq, mul_nonneg (mul_nonneg hh hq) (neg_nonneg.mpr hneg.le)]

/-! ### Truncated backward Euler runs -/

/-- **Ranks of a truncated backward Euler run of a Lyapunov equation.** Let `P ⪰ 0`, `F ⪰ 0`,
let `X` be the backward Euler run of `A' = -PA - AP + F` and let `Y` be a run in which the step
`Ŷ_{j+1}` from `Y_j` is replaced by a positive semidefinite `Y_{j+1} ⪯ Ŷ_{j+1}` of rank at most
`rank_θ(Ŷ_{j+1})`. If `0 ⪯ Y₀ ⪯ X₀`, then `0 ⪯ Y_j ⪯ Ŷ_j ⪯ X_j` and
`rank Y_j ≤ rank_θ(X_j)` for all steps, for every step size and tolerance. -/
theorem rank_le_epsRank_of_truncated_lyapunov_run {P F : Matrix n n ℝ} {h θ : ℝ}
    (hP : P.PosSemidef) (hF : F.PosSemidef) (hh : 0 ≤ h) (hθ : 0 ≤ θ) {N : ℕ}
    {X Y Yh : ℕ → Matrix n n ℝ}
    (hX : ∀ j < N, X (j + 1) + h • (P * X (j + 1) + X (j + 1) * P) = X j + h • F)
    (hYh : ∀ j < N, Yh (j + 1) + h • (P * Yh (j + 1) + Yh (j + 1) * P) = Y j + h • F)
    (hY0 : (Y 0).PosSemidef) (hXY0 : (X 0 - Y 0).PosSemidef)
    (hYpos : ∀ j < N, (Y (j + 1)).PosSemidef)
    (hYle : ∀ j < N, (Yh (j + 1) - Y (j + 1)).PosSemidef)
    (hYrank : ∀ j < N, (Y (j + 1)).rank ≤ epsRank θ (Yh (j + 1))) :
    ∀ j < N, (Yh (j + 1)).PosSemidef ∧ (X (j + 1) - Yh (j + 1)).PosSemidef ∧
      (X (j + 1) - Y (j + 1)).PosSemidef ∧ (Y (j + 1)).rank ≤ epsRank θ (X (j + 1)) := by
  classical
  have hYp : ∀ j ≤ N, (Y j).PosSemidef := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · exact hY0
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      exact hYpos i hj
  have hstep : ∀ j < N, (X j - Y j).PosSemidef →
      (X (j + 1) - Yh (j + 1)).PosSemidef := by
    intro j hj hle
    refine posSemidef_of_add_smul_lyapunov hP hle hh ?_
    have e : X j - Y j = (X (j + 1) + h • (P * X (j + 1) + X (j + 1) * P))
        - (Yh (j + 1) + h • (P * Yh (j + 1) + Yh (j + 1) * P)) := by
      rw [hX j hj, hYh j hj]; abel
    rw [e, Matrix.mul_sub, Matrix.sub_mul]
    module
  have hord : ∀ j ≤ N, (X j - Y j).PosSemidef := by
    intro j
    induction j with
    | zero => intro _; exact hXY0
    | succ j ih =>
      intro hj
      have h1 := hstep j hj (ih (Nat.le_of_succ_le hj))
      have h2 := h1.add (hYle j hj)
      rwa [sub_add_sub_cancel] at h2
  intro j hj
  have hYhp : (Yh (j + 1)).PosSemidef :=
    posSemidef_of_add_smul_lyapunov hP ((hYp j hj.le).add (hF.smul hh)) hh (hYh j hj)
  have h1 := hstep j hj (hord j hj.le)
  exact ⟨hYhp, h1, hord (j + 1) hj,
    (hYrank j hj).trans (epsRank_le_epsRank_of_posSemidef hYhp h1 hθ)⟩

/-- **Error of a truncated backward Euler run of a Lyapunov equation.** If `P ⪰ c ≥ 0` and
every truncation is within `θ`, then `‖X_j - Y_j‖ ≤ E_j` for every sequence with
`E₀ ≥ ‖X₀ - Y₀‖` and `E_{j+1} ≥ E_j / (1 + 2hc) + θ` (for instance the constant
`θ (1 + 2hc) / (2hc)` when `Y₀ = X₀`). -/
theorem norm_sub_le_of_truncated_lyapunov_run [DecidableEq n] {P F : Matrix n n ℝ} {h c θ : ℝ}
    (hP : (P - c • (1 : Matrix n n ℝ)).PosSemidef) (hh : 0 ≤ h) (hc : 0 ≤ c) {N : ℕ}
    {X Y Yh : ℕ → Matrix n n ℝ} {E : ℕ → ℝ}
    (hX : ∀ j < N, X (j + 1) + h • (P * X (j + 1) + X (j + 1) * P) = X j + h • F)
    (hYh : ∀ j < N, Yh (j + 1) + h • (P * Yh (j + 1) + Yh (j + 1) * P) = Y j + h • F)
    (hT : ∀ j < N, ‖Yh (j + 1) - Y (j + 1)‖ ≤ θ) (hE0 : ‖X 0 - Y 0‖ ≤ E 0)
    (hE : ∀ j < N, E j / (1 + 2 * h * c) + θ ≤ E (j + 1)) :
    ∀ j ≤ N, ‖X j - Y j‖ ≤ E j := by
  have hpos : 0 < 1 + 2 * h * c := by nlinarith [mul_nonneg hh hc]
  intro j
  induction j with
  | zero => intro _; exact hE0
  | succ j ih =>
    intro hj
    have hlt : j < N := hj
    have hD : (X (j + 1) - Yh (j + 1))
        + h • (P * (X (j + 1) - Yh (j + 1)) + (X (j + 1) - Yh (j + 1)) * P) = X j - Y j := by
      have e : X j - Y j = (X (j + 1) + h • (P * X (j + 1) + X (j + 1) * P))
          - (Yh (j + 1) + h • (P * Yh (j + 1) + Yh (j + 1) * P)) := by
        rw [hX j hlt, hYh j hlt]; abel
      rw [e, Matrix.mul_sub, Matrix.sub_mul]
      module
    have h1 := mul_norm_le_of_add_smul_lyapunov hP hh hD
    have h2 : ‖X (j + 1) - Yh (j + 1)‖ ≤ E j / (1 + 2 * h * c) := by
      rw [le_div_iff₀ hpos, mul_comm]
      exact h1.trans (ih hlt.le)
    calc ‖X (j + 1) - Y (j + 1)‖
        = ‖(X (j + 1) - Yh (j + 1)) + (Yh (j + 1) - Y (j + 1))‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ ‖X (j + 1) - Yh (j + 1)‖ + ‖Yh (j + 1) - Y (j + 1)‖ := norm_add_le _ _
      _ ≤ E j / (1 + 2 * h * c) + θ := add_le_add h2 (hT j hlt)
      _ ≤ E (j + 1) := hE j hlt

/-- The hypotheses of `rank_le_epsRank_of_truncated_lyapunov_run` and of
`norm_sub_le_of_truncated_lyapunov_run` can hold with a truncation that changes the iterate:
`P = F = 1` on `1 × 1` matrices, `h = c = 1`, `θ = 1/2`, start at zero; the step `1/3` is
truncated to zero, and the error bound `E₁ = 1/2` is not zero. -/
example : ∃ (X Y Yh : ℕ → Matrix (Fin 1) (Fin 1) ℝ) (E : ℕ → ℝ),
    ((1 : Matrix (Fin 1) (Fin 1) ℝ) - (1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosSemidef ∧
    (∀ j < 1, X (j + 1) + (1 : ℝ) • (1 * X (j + 1) + X (j + 1) * 1) = X j + (1 : ℝ) • 1) ∧
    (∀ j < 1, Yh (j + 1) + (1 : ℝ) • (1 * Yh (j + 1) + Yh (j + 1) * 1) = Y j + (1 : ℝ) • 1) ∧
    (Y 0).PosSemidef ∧ (X 0 - Y 0).PosSemidef ∧ (∀ j < 1, (Y (j + 1)).PosSemidef) ∧
    (∀ j < 1, (Yh (j + 1) - Y (j + 1)).PosSemidef) ∧
    (∀ j < 1, (Y (j + 1)).rank ≤ epsRank (1 / 2) (Yh (j + 1))) ∧
    (∀ j < 1, ‖Yh (j + 1) - Y (j + 1)‖ ≤ 1 / 2) ∧ ‖X 0 - Y 0‖ ≤ E 0 ∧
    (∀ j < 1, E j / (1 + 2 * 1 * 1) + 1 / 2 ≤ E (j + 1)) ∧ X 1 ≠ Y 1 := by
  have hone : ‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖ = 1 := by
    have h : ‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖ ^ 2 = 1 := by
      rw [Frobenius.norm_sq_eq_sum]; simp
    nlinarith [norm_nonneg (1 : Matrix (Fin 1) (Fin 1) ℝ)]
  have hthird : ((1 / 3 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by norm_num)
  refine ⟨fun j => ((j : ℝ) / 3) • 1, fun _ => 0, fun j => ((j : ℝ) / 3) • 1,
    fun j => (j : ℝ) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using Matrix.PosSemidef.zero
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp only [Nat.cast_zero, zero_div, zero_smul, zero_add, Nat.cast_one, Matrix.one_mul,
      Matrix.mul_one, one_smul]
    module
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp only [zero_add, Nat.cast_one, Matrix.one_mul, Matrix.mul_one, one_smul]
    module
  · exact Matrix.PosSemidef.zero
  · simpa using Matrix.PosSemidef.zero
  · intro j _; exact Matrix.PosSemidef.zero
  · intro j hj
    obtain rfl : j = 0 := by omega
    simpa using hthird
  · intro j _; simp
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp only [zero_add, Nat.cast_one, sub_zero]
    rw [norm_smul, hone]; norm_num
  · simp
  · intro j hj
    obtain rfl : j = 0 := by omega
    norm_num
  · simp only [Nat.cast_one]
    intro h0
    have := congrArg norm h0
    rw [norm_smul, hone, norm_zero] at this
    norm_num at this

end LeanDLRA.LoewnerRank
