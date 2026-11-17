import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Orthonormal

/-!
# Results of arXiv 2609.21039: Stiefel-AdamW for linear factorization blocks

Zangrando, Sutti, Tudisco, *Stiefel-AdamW: Geometry-Aware AdamW for Linear Factorization Blocks*.
A weight `W = B A`, `B ∈ ℝ^{m×r}`, `A ∈ ℝ^{r×n}`, is trained with `A Aᵀ = I`.  This module proves
the gauge reduction from `GL(r)` to `O(r)` and `‖B‖ = ‖W‖` in the Frobenius and spectral norms
(`gauge_reduction`, `exists_GL_gauge`, `gauge_orthogonal_iff`, `stiefelFiber_eq_orbit`,
`isCompact_stiefelFiber`, `specNorm_mul_eq_of_rowOrthonormal`; the Frobenius case is the library's
`Frobenius.norm_mul_transpose_of_orthonormal`), the tangent geometry of App. A.1 (`stiefelProj`,
`rowProj`, `isOrthProj_stiefelProj`, `isOrthProj_rowProj`, `tangent_iff_exists_skew`), the Cayley
retraction and its fixed-point iteration of App. A.2 (`cayleyRetr`, `cayleyMap_contraction` = Lemma
A.1, `cayleyIter_sub_le` = Theorem A.2, `cayleyIter_first_order` = Lemma A.3), Algorithm 1 as
`StiefelAdamWRun`, the corrected regret bound and Proposition 4.3, and the example of §4.2
(`recovery_aligned`, `sigma_recursion`, `recovery_gd_diverges`, `constrained_bounded`).

**Theorem 4.2 is false** (`theorem_4_2_false`, and `theorem_4_2_false_factorized` for losses of
`W`): a constrained critical point which is not the minimizer never moves, (H6) holds there with
equality, and the regret is linear.  The proof in App. B needs `Γ_t⁻¹ D_t = M_t`, which fails unless
`M_t` is tangent, and `⟨E_t, A_t - A*⟩_{Γ⁻¹} ≤ 0`, which does not follow from (H6).  The corrected
statements are `regret_le_add_normalDefect`, which needs no (H6) and has the extra term
`∑ ν_t`, and `regret_bound_of_normal_alignment`, which replaces (H6) by `ν_t ≤ 0`.  They give
`R(T) ≤ C₁ + C₂ √T` with explicit constants, for any second-order retraction: the paper's
`L¹L²` terms depend on `T`, and `ε > 0` makes them unnecessary.

**Proposition 4.3, first claim, is false** (`proposition_4_3_first_claim_false`): at a critical
point of `L` on the rank-`r` matrices with `∇L(W) ≠ 0`, the gradient of `L ∘ Φ` vanishes on the
whole fiber.  `not_bddAbove_grad_fiber_iff` is the sharp form.  The second claim holds for every `W`
(`proposition_4_3_second_claim`), with an explicit bound; the paper's proof treats the fiber as one
`O(r)`-orbit, which requires `rank W = r`.

Conventions: (H5) is `V_t = max(β₂ V_{t-1} + (1 - β₂) G_t^{∘2}, V_{t-1})`, as in the paper.  Since
Algorithm 1 has `D_t` of shape `r × n`, line 10 is read with `D_tᵀ`.  Regret is against a comparator
`(B*, A*)` as in App. B, with loss `L_t(B, A)`.  Not formalized: the QR and polar retractions, and
the remark on an inexact retraction (this proof technique gives a term `∑ δ / η_t`, not `C₆ δ`).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2609_21039

open LeanDLRA.Curvature

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

section Gauge

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

/-- A square real matrix of full rank is invertible. -/
private theorem isUnit_of_rank_eq {M : Matrix r r ℝ} (h : M.rank = Fintype.card r) : IsUnit M := by
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  have h' : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank] using h
  exact LinearMap.range_eq_top.mp h'

/-- A matrix of full column rank has a left inverse. -/
private theorem exists_leftInverse {B : Matrix m r ℝ} (hB : B.rank = Fintype.card r) :
    ∃ L : Matrix r m ℝ, L * B = 1 := by
  have h : IsUnit (Bᵀ * B) := isUnit_of_rank_eq (by rw [Matrix.rank_transpose_mul_self, hB])
  refine ⟨(Bᵀ * B)⁻¹ * Bᵀ, ?_⟩
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 h)]

/-- A matrix of full row rank has a right inverse. -/
private theorem exists_rightInverse {A : Matrix r n ℝ} (hA : A.rank = Fintype.card r) :
    ∃ R : Matrix n r ℝ, A * R = 1 := by
  obtain ⟨L, hL⟩ := exists_leftInverse (B := Aᵀ) (by rw [Matrix.rank_transpose, hA])
  refine ⟨Lᵀ, ?_⟩
  have := congrArg Matrix.transpose hL
  simpa [Matrix.transpose_mul] using this

/-- Membership in `O(r)` in terms of the transpose. -/
private theorem mem_orthogonal_iff {Q : Matrix r r ℝ} :
    Q ∈ Matrix.orthogonalGroup r ℝ ↔ Qᵀ * Q = 1 := by
  rw [Matrix.mem_orthogonalGroup_iff']

/-- arXiv 2609.21039, gauge reduction (§3.1), Frobenius norm: if `A Aᵀ = I` then `‖B A‖_F = ‖B‖_F`,
so the factor `B` has the size of `W = B A`.  This restates
`Frobenius.norm_mul_transpose_of_orthonormal` for `V = Aᵀ`. -/
theorem norm_mul_eq_of_rowOrthonormal {A : Matrix r n ℝ} (hA : A * Aᵀ = 1) (B : Matrix m r ℝ) :
    ‖B * A‖ = ‖B‖ := by
  have h := Frobenius.norm_mul_transpose_of_orthonormal (V := Aᵀ) (by simpa using hA) B
  simpa using h

/-- arXiv 2609.21039, gauge reduction (§3.1), spectral norm: if `A Aᵀ = I` then `‖B A‖₂ = ‖B‖₂`. -/
theorem specNorm_mul_eq_of_rowOrthonormal [DecidableEq n] {A : Matrix r n ℝ}
    (hA : A * Aᵀ = 1) (B : Matrix m r ℝ) : specNorm (B * A) = specNorm B := by
  classical
  have hAt : specNorm Aᵀ ≤ 1 :=
    specNorm_le_one_of_orthonormal (U := Aᵀ) (by simpa using hA)
  have hA1 : specNorm A ≤ 1 := by rwa [specNorm_transpose] at hAt
  apply le_antisymm
  · calc specNorm (B * A) ≤ specNorm B * specNorm A := specNorm_mul_le _ _
      _ ≤ specNorm B * 1 := by gcongr; exact specNorm_nonneg _
      _ = specNorm B := mul_one _
  · have hB : B = B * A * Aᵀ := by rw [Matrix.mul_assoc, hA, Matrix.mul_one]
    calc specNorm B = specNorm (B * A * Aᵀ) := by rw [← hB]
      _ ≤ specNorm (B * A) * specNorm Aᵀ := specNorm_mul_le _ _
      _ ≤ specNorm (B * A) * 1 := by gcongr; exact specNorm_nonneg _
      _ = specNorm (B * A) := mul_one _

/-- arXiv 2609.21039, §3.1: on the constrained fiber, `B` is determined by `W` and `A`: `B = W Aᵀ`.
-/
theorem eq_mul_transpose_of_rowOrthonormal {A : Matrix r n ℝ} (hA : A * Aᵀ = 1)
    {B : Matrix m r ℝ} {W : Matrix m n ℝ} (hW : B * A = W) : B = W * Aᵀ := by
  rw [← hW, Matrix.mul_assoc, hA, Matrix.mul_one]

/-- arXiv 2609.21039, §3.1: the full gauge symmetry `Φ(B M, M⁻¹ A) = Φ(B, A)`, `M ∈ GL(r)`. -/
theorem gauge_mul {M : Matrix r r ℝ} (hM : IsUnit M) (B : Matrix m r ℝ) (A : Matrix r n ℝ) :
    (B * M) * (M⁻¹ * A) = B * A := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc M, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).1 hM), Matrix.one_mul]

/-- arXiv 2609.21039, §3.1: at a full-rank factorization the gauge group of `Φ` is all of `GL(r)`:
two factorizations of the same matrix differ by some `M ∈ GL(r)`. The paper states this without
proof; full rank of `B` and `A` is needed. -/
theorem exists_GL_gauge {B B' : Matrix m r ℝ} {A A' : Matrix r n ℝ}
    (hB : B.rank = Fintype.card r) (hA : A.rank = Fintype.card r) (h : B * A = B' * A') :
    ∃ M : Matrix r r ℝ, IsUnit M ∧ B' = B * M ∧ A' = M⁻¹ * A := by
  obtain ⟨L, hL⟩ := exists_leftInverse hB
  have hA' : A'.rank = Fintype.card r := by
    apply le_antisymm (by simpa using A'.rank_le_card_height)
    calc Fintype.card r = A.rank := hA.symm
      _ = (L * (B * A)).rank := by rw [← Matrix.mul_assoc, hL, Matrix.one_mul]
      _ ≤ (B * A).rank := Matrix.rank_mul_le_right _ _
      _ = (B' * A').rank := by rw [h]
      _ ≤ A'.rank := Matrix.rank_mul_le_right _ _
  obtain ⟨R', hR'⟩ := exists_rightInverse hA'
  obtain ⟨R, hR⟩ := exists_rightInverse hA
  have hB' : B' = B * (A * R') := by
    rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, hR', Matrix.mul_one]
  have hMA : A * R' * A' = A := by
    have h1 : B * (A * R' * A') = B * A := by rw [← Matrix.mul_assoc, ← hB', h]
    have h2 := congrArg (L * ·) h1
    simpa only [← Matrix.mul_assoc, hL, Matrix.one_mul] using h2
  have hMu : (A * R') * (A' * R) = 1 := by rw [← Matrix.mul_assoc, hMA, hR]
  have hdet : IsUnit (A * R').det := Matrix.isUnit_det_of_right_inverse hMu
  refine ⟨A * R', (Matrix.isUnit_iff_isUnit_det _).2 hdet, hB', ?_⟩
  calc A' = (A * R')⁻¹ * ((A * R') * A') := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
    _ = (A * R')⁻¹ * A := by rw [hMA]

/-- arXiv 2609.21039, gauge reduction (§3.1): for row-orthonormal `A` and `M ∈ GL(r)`, the gauged
factor `M⁻¹ A` is row-orthonormal if and only if `M ∈ O(r)`. -/
theorem gauge_orthogonal_iff {A : Matrix r n ℝ} (hA : A * Aᵀ = 1) {M : Matrix r r ℝ}
    (hM : IsUnit M) :
    (M⁻¹ * A) * (M⁻¹ * A)ᵀ = 1 ↔ M ∈ Matrix.orthogonalGroup r ℝ := by
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).1 hM
  have hdet' : IsUnit Mᵀ.det := by simpa using hdet
  have key : (M⁻¹ * A) * (M⁻¹ * A)ᵀ = M⁻¹ * (M⁻¹)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc A, hA, Matrix.one_mul]
  rw [key, mem_orthogonal_iff]
  constructor
  · intro h
    have h2 : M⁻¹ * (M⁻¹)ᵀ * (Mᵀ * M) = 1 := by
      rw [Matrix.transpose_nonsing_inv]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Mᵀ⁻¹), Matrix.nonsing_inv_mul _ hdet',
        Matrix.one_mul, Matrix.nonsing_inv_mul _ hdet]
    rw [h, Matrix.one_mul] at h2
    exact h2
  · intro h
    have h3 : (M⁻¹)ᵀ = M := by
      have h4 : M⁻¹ = Mᵀ := Matrix.inv_eq_left_inv h
      rw [h4, Matrix.transpose_transpose]
    rw [h3, Matrix.nonsing_inv_mul _ hdet]

/-- arXiv 2609.21039, gauge reduction (§3.1): if `B A = B' A'` with `A`, `A'` row-orthonormal and
`B` of full column rank, then `B' = B Q` and `A' = Qᵀ A` for some `Q ∈ O(r)`.  Full rank of `B` is
necessary: for `W = 0` every row-orthonormal `A` occurs with `B = 0`. -/
theorem gauge_reduction {B B' : Matrix m r ℝ} {A A' : Matrix r n ℝ}
    (hA : A * Aᵀ = 1) (hA' : A' * A'ᵀ = 1) (hB : B.rank = Fintype.card r)
    (h : B * A = B' * A') :
    ∃ Q ∈ Matrix.orthogonalGroup r ℝ, B' = B * Q ∧ A' = Qᵀ * A := by
  obtain ⟨L, hL⟩ := exists_leftInverse hB
  have hB1 : B' = B * (A * A'ᵀ) := by
    rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, hA', Matrix.mul_one]
  have hB2 : B = B' * (A * A'ᵀ)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, ← h,
      Matrix.mul_assoc, hA, Matrix.mul_one]
  have hOO : (A * A'ᵀ) * (A * A'ᵀ)ᵀ = 1 := by
    have h1 : B * ((A * A'ᵀ) * (A * A'ᵀ)ᵀ) = B := by
      rw [← Matrix.mul_assoc, ← hB1, ← hB2]
    have h2 := congrArg (L * ·) h1
    simpa only [← Matrix.mul_assoc, hL, Matrix.one_mul] using h2
  have hOO' : (A * A'ᵀ)ᵀ * (A * A'ᵀ) = 1 := mul_eq_one_comm.mp hOO
  have hAeq : (A * A'ᵀ) * A' = A := by
    have h1 : B * ((A * A'ᵀ) * A') = B * A := by rw [← Matrix.mul_assoc, ← hB1, h]
    have h2 := congrArg (L * ·) h1
    simpa only [← Matrix.mul_assoc, hL, Matrix.one_mul] using h2
  refine ⟨A * A'ᵀ, mem_orthogonal_iff.2 hOO', hB1, ?_⟩
  calc A' = (A * A'ᵀ)ᵀ * ((A * A'ᵀ) * A') := by rw [← Matrix.mul_assoc, hOO', Matrix.one_mul]
    _ = (A * A'ᵀ)ᵀ * A := by rw [hAeq]

/-- The fiber `Φ⁻¹(W)` of the factorization map on `ℝ^{m×r} × ℝ^{r×n}`. -/
def fiber (r : Type*) [Fintype r] (W : Matrix m n ℝ) : Set (Matrix m r ℝ × Matrix r n ℝ) :=
  {p | p.1 * p.2 = W}

/-- The fiber of the restriction of `Φ` to `ℝ^{m×r} × {A : A Aᵀ = I}`. -/
def stiefelFiber (r : Type*) [Fintype r] [DecidableEq r] (W : Matrix m n ℝ) :
    Set (Matrix m r ℝ × Matrix r n ℝ) :=
  {p | p.1 * p.2 = W ∧ p.2 * p.2ᵀ = 1}

/-- arXiv 2609.21039, §3.1: if `B` has full column rank, the constrained fiber through `(B, A)` is
the single orbit `{(B Q, Qᵀ A) : Q ∈ O(r)}`.  For rank-deficient `W` it is in general larger, a case
which the paper's proof of Proposition 4.3 overlooks. -/
theorem stiefelFiber_eq_orbit {W : Matrix m n ℝ} {B : Matrix m r ℝ} {A : Matrix r n ℝ}
    (hp : (B, A) ∈ stiefelFiber r W) (hB : B.rank = Fintype.card r) :
    stiefelFiber r W =
      (fun Q : Matrix r r ℝ => (B * Q, Qᵀ * A)) '' Matrix.orthogonalGroup r ℝ := by
  obtain ⟨hW, hA⟩ := hp
  ext ⟨B', A'⟩
  constructor
  · rintro ⟨hW', hA'⟩
    obtain ⟨Q, hQ, h1, h2⟩ := gauge_reduction hA hA' hB (hW.trans hW'.symm)
    exact ⟨Q, hQ, Prod.ext h1.symm h2.symm⟩
  · rintro ⟨Q, hQ, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    have hQ2 : Qᵀ * Q = 1 := mem_orthogonal_iff.1 hQ
    have hQ1 : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ2
    constructor
    · simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q, hQ1, Matrix.one_mul]
      exact hW
    · rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
        ← Matrix.mul_assoc A, hA, Matrix.one_mul]
      exact hQ2

/-- A row-orthonormal matrix has `‖A‖_F² = r`. -/
theorem norm_sq_of_rowOrthonormal {A : Matrix r n ℝ} (hA : A * Aᵀ = 1) :
    ‖A‖ ^ 2 = Fintype.card r := by
  have h : ⟪Aᵀ, Aᵀ⟫ = Matrix.trace (A * Aᵀ) := by
    rw [Frobenius.inner_eq_trace, Matrix.transpose_transpose]
  rw [hA, Matrix.trace_one, real_inner_self_eq_norm_sq, Frobenius.norm_transpose] at h
  exact_mod_cast h

/-- The row-orthonormal matrices form a compact set. -/
theorem isCompact_rowStiefel : IsCompact {A : Matrix r n ℝ | A * Aᵀ = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (by fun_prop) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Matrix r n ℝ))
      (r := √(Fintype.card r))).subset fun A hA => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    apply Real.le_sqrt_of_sq_le
    exact (norm_sq_of_rowOrthonormal hA).le

/-- arXiv 2609.21039, §3.1: the fibers of the constrained map are compact, for every `W`. -/
theorem isCompact_stiefelFiber (W : Matrix m n ℝ) : IsCompact (stiefelFiber r W) := by
  have hc : IsCompact {A : Matrix r n ℝ | A * Aᵀ = 1 ∧ W * Aᵀ * A = W} := by
    have : {A : Matrix r n ℝ | A * Aᵀ = 1 ∧ W * Aᵀ * A = W} =
        {A : Matrix r n ℝ | A * Aᵀ = 1} ∩ {A : Matrix r n ℝ | W * Aᵀ * A = W} := rfl
    rw [this]
    exact isCompact_rowStiefel.inter_right (isClosed_eq (by fun_prop) continuous_const)
  have himg := hc.image (f := fun A : Matrix r n ℝ => (W * Aᵀ, A)) (by fun_prop)
  convert himg using 1
  ext ⟨B, A⟩
  constructor
  · rintro ⟨h1, h2⟩
    have hB := eq_mul_transpose_of_rowOrthonormal h2 h1
    refine ⟨A, ⟨h2, ?_⟩, ?_⟩
    · rw [← hB]; exact h1
    · exact Prod.ext hB.symm rfl
  · rintro ⟨A', ⟨h1, h2⟩, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact ⟨h2, h1⟩

/-- Non-vacuity, arXiv 2609.21039, §3.1: for `rank W ≤ k ≤ n` the constrained fiber is nonempty. -/
theorem stiefelFiber_nonempty {k : ℕ} {W : Matrix m n ℝ} (h₁ : W.rank ≤ k)
    (h₂ : k ≤ Fintype.card n) : (stiefelFiber (Fin k) W).Nonempty := by
  obtain ⟨U, hU, hcap⟩ := exists_orthonormal_capture Wᵀ (by rwa [Matrix.rank_transpose]) h₂
  refine ⟨(W * U, Uᵀ), ?_, by simpa using hU⟩
  have h := congrArg Matrix.transpose hcap
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h
  change W * U * Uᵀ = W
  rw [Matrix.mul_assoc]
  exact h

/-- arXiv 2609.21039, §3.1, the factor blow-up that the constraint rules out: without the constraint
the gauge moves `B` arbitrarily far while `W = B A` stays fixed.  Compare
`norm_mul_eq_of_rowOrthonormal`. -/
theorem factor_blowup {B : Matrix m r ℝ} (hB : B ≠ 0) (A : Matrix r n ℝ) (C : ℝ) :
    ∃ t : ℝ, t ≠ 0 ∧ (t • B) * (t⁻¹ • A) = B * A ∧ C < ‖t • B‖ := by
  have hn : 0 < ‖B‖ := norm_pos_iff.2 hB
  have ht : (|C| + 1) / ‖B‖ ≠ 0 := by positivity
  refine ⟨(|C| + 1) / ‖B‖, ht, ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ht, one_smul]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_cancel₀ _ hn.ne']
    linarith [le_abs_self C]

end Gauge

section Stiefel

variable {n r : Type*} [Fintype n] [Fintype r] [DecidableEq r]

/-- `sym(M) = (M + Mᵀ) / 2` (arXiv 2609.21039, App. A.1). -/
noncomputable def symPart (M : Matrix r r ℝ) : Matrix r r ℝ := (1 / 2 : ℝ) • (M + Mᵀ)

/-- `skew(M) = (M - Mᵀ) / 2` (arXiv 2609.21039, App. A.1). -/
noncomputable def skewPart (M : Matrix r r ℝ) : Matrix r r ℝ := (1 / 2 : ℝ) • (M - Mᵀ)

/-- The symmetric part is symmetric. -/
@[simp] lemma transpose_symPart (M : Matrix r r ℝ) : (symPart M)ᵀ = symPart M := by
  simp [symPart, add_comm]

/-- The skew part is skew. -/
lemma transpose_skewPart (M : Matrix r r ℝ) : (skewPart M)ᵀ = -skewPart M := by
  simp only [skewPart, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_transpose]
  rw [← smul_neg, neg_sub]

/-- `sym` is self-adjoint for the Frobenius inner product. -/
lemma inner_symPart (S T : Matrix r r ℝ) : ⟪symPart S, T⟫ = ⟪S, symPart T⟫ := by
  have h : ⟪Sᵀ, T⟫ = ⟪S, Tᵀ⟫ := by
    rw [← Frobenius.inner_transpose Sᵀ T, Matrix.transpose_transpose]
  simp only [symPart, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right, h]
  simp

/-- The tangent projection `P_X(Z) = Z - X sym(Xᵀ Z)` on `ℝ^{n×r}` (arXiv 2609.21039, App. A.1), as
a continuous linear map. -/
noncomputable def stiefelProj (X : Matrix n r ℝ) : Matrix n r ℝ →L[ℝ] Matrix n r ℝ :=
  1 - (1 / 2 : ℝ) • (Frobenius.leftMulCLM (X * Xᵀ) +
    (Frobenius.leftMulCLM X).comp ((Frobenius.rightMulCLM X).comp Frobenius.transposeCLM))

/-- The formula `P_X(Z) = Z - X sym(Xᵀ Z)`. -/
lemma stiefelProj_apply (X Z : Matrix n r ℝ) :
    stiefelProj X Z = Z - X * symPart (Xᵀ * Z) := by
  have h : Frobenius.leftMulCLM (X * Xᵀ) Z = X * (Xᵀ * Z) := by
    simp [Frobenius.leftMulCLM, Matrix.mul_assoc]
  have h2 : (Frobenius.leftMulCLM X).comp ((Frobenius.rightMulCLM X).comp
      Frobenius.transposeCLM) Z = X * (Zᵀ * X) := by
    simp [Frobenius.leftMulCLM, Frobenius.rightMulCLM, Frobenius.transposeCLM]
  have h3 : stiefelProj X Z = Z - (1 / 2 : ℝ) • (X * (Xᵀ * Z) + X * (Zᵀ * X)) := by
    simp [stiefelProj, h, h2]
  rw [h3, symPart, Matrix.mul_smul, Matrix.mul_add, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- arXiv 2609.21039, eq. (A.1): `P_X(Z) = X skew(Xᵀ Z) + (I - X Xᵀ) Z`. -/
theorem stiefelProj_eq_skew [DecidableEq n] (X Z : Matrix n r ℝ) :
    stiefelProj X Z = X * skewPart (Xᵀ * Z) + (1 - X * Xᵀ) * Z := by
  rw [stiefelProj_apply, symPart, skewPart]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.mul_add,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  module

/-- `sym(Xᵀ P_X(Z)) = 0` on the Stiefel manifold. -/
theorem symPart_transpose_mul_stiefelProj {X : Matrix n r ℝ} (hX : Xᵀ * X = 1)
    (Z : Matrix n r ℝ) : symPart (Xᵀ * stiefelProj X Z) = 0 := by
  have h : Xᵀ * stiefelProj X Z = Xᵀ * Z - symPart (Xᵀ * Z) := by
    rw [stiefelProj_apply, Matrix.mul_sub, ← Matrix.mul_assoc, hX, Matrix.one_mul]
  rw [h, symPart, Matrix.transpose_sub, transpose_symPart, symPart]
  module

/-- arXiv 2609.21039, App. A.1 ("orthogonal projection onto the tangent space"): `P_X` is an
orthogonal projector for the Frobenius inner product when `Xᵀ X = I`. -/
theorem isOrthProj_stiefelProj {X : Matrix n r ℝ} (hX : Xᵀ * X = 1) :
    IsOrthProj (stiefelProj X) where
  idem Z := by
    rw [stiefelProj_apply (Z := stiefelProj X Z), symPart_transpose_mul_stiefelProj hX]
    simp
  symm Z Y := by
    have key : ⟪X * symPart (Xᵀ * Z), Y⟫ = ⟪Z, X * symPart (Xᵀ * Y)⟫ := by
      rw [Frobenius.inner_mul_left, inner_symPart, Frobenius.inner_mul_left,
        Matrix.transpose_transpose]
    rw [stiefelProj_apply, stiefelProj_apply, inner_sub_left, inner_sub_right, key]

/-- arXiv 2609.21039, App. A.1: the range of `P_X` is the tangent space `T_X St(n, r) = {ξ : Xᵀ ξ +
ξᵀ X = 0}`. -/
theorem stiefelProj_eq_self_iff {X ξ : Matrix n r ℝ} (hX : Xᵀ * X = 1) :
    stiefelProj X ξ = ξ ↔ Xᵀ * ξ + ξᵀ * X = 0 := by
  rw [stiefelProj_apply, sub_eq_self]
  have hsym : symPart (Xᵀ * ξ) = (1 / 2 : ℝ) • (Xᵀ * ξ + ξᵀ * X) := by
    rw [symPart, Matrix.transpose_mul, Matrix.transpose_transpose]
  constructor
  · intro h
    have h1 : symPart (Xᵀ * ξ) = 0 := by
      have := congrArg (Xᵀ * ·) h
      simpa only [← Matrix.mul_assoc, hX, Matrix.one_mul, Matrix.mul_zero] using this
    rw [hsym] at h1
    exact (smul_eq_zero.1 h1).resolve_left (by norm_num)
  · intro h
    rw [hsym, h]
    simp

/-- `P_X(Z)` is tangent at `X`. -/
theorem stiefelProj_tangent {X : Matrix n r ℝ} (hX : Xᵀ * X = 1) (Z : Matrix n r ℝ) :
    Xᵀ * stiefelProj X Z + (stiefelProj X Z)ᵀ * X = 0 :=
  (stiefelProj_eq_self_iff hX).1 ((isOrthProj_stiefelProj hX).idem Z)

/-- arXiv 2609.21039, App. A.1: tangent vectors are `ξ = X Ω + X_⊥ K` with `Ω` skew.  Here `X_⊥ K`
is written `(I - X Xᵀ) K`, which needs no orthonormal completion. -/
theorem tangent_iff_exists_skew [DecidableEq n] {X ξ : Matrix n r ℝ} (hX : Xᵀ * X = 1) :
    Xᵀ * ξ + ξᵀ * X = 0 ↔
      ∃ (Ω : Matrix r r ℝ) (K : Matrix n r ℝ), Ωᵀ = -Ω ∧ ξ = X * Ω + (1 - X * Xᵀ) * K := by
  constructor
  · intro h
    refine ⟨skewPart (Xᵀ * ξ), ξ, transpose_skewPart _, ?_⟩
    rw [← stiefelProj_eq_skew, (stiefelProj_eq_self_iff hX).2 h]
  · rintro ⟨Ω, K, hΩ, rfl⟩
    have h1 : Xᵀ * (1 - X * Xᵀ) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hX, Matrix.one_mul, sub_self]
    have h2 : Xᵀ * (X * Ω + (1 - X * Xᵀ) * K) = Ω := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc, hX, Matrix.one_mul, ← Matrix.mul_assoc, h1,
        Matrix.zero_mul, add_zero]
    have h3 : (X * Ω + (1 - X * Xᵀ) * K)ᵀ * X = Ωᵀ := by
      have := congrArg Matrix.transpose h2
      simpa [Matrix.transpose_mul] using this
    rw [h2, h3, hΩ, add_neg_cancel]

/-- The kernel of `P_X` is the normal space `{X S : Sᵀ = S}`. -/
theorem stiefelProj_eq_zero_iff {X Z : Matrix n r ℝ} (hX : Xᵀ * X = 1) :
    stiefelProj X Z = 0 ↔ ∃ S : Matrix r r ℝ, Sᵀ = S ∧ Z = X * S := by
  constructor
  · intro h
    rw [stiefelProj_apply, sub_eq_zero] at h
    exact ⟨_, transpose_symPart _, h⟩
  · rintro ⟨S, hS, rfl⟩
    rw [stiefelProj_apply, ← Matrix.mul_assoc, hX, Matrix.one_mul, symPart, hS]
    simp only [← two_smul ℝ S, smul_smul]
    norm_num

/-- The tangent projection in the row convention, `Z ↦ (P_{Aᵀ}(Zᵀ))ᵀ`, used for `A = Xᵀ`. -/
noncomputable def rowProj (A : Matrix r n ℝ) : Matrix r n ℝ →L[ℝ] Matrix r n ℝ :=
  (Frobenius.transposeCLM (m := n) (n := r)).comp
    ((stiefelProj Aᵀ).comp (Frobenius.transposeCLM (m := r) (n := n)))

/-- Definition of `rowProj`. -/
lemma rowProj_eq (A Z : Matrix r n ℝ) : rowProj A Z = (stiefelProj Aᵀ Zᵀ)ᵀ := rfl

/-- `sym(Mᵀ) = sym(M)`. -/
lemma symPart_transpose (M : Matrix r r ℝ) : symPart Mᵀ = symPart M := by
  simp [symPart, add_comm]

/-- arXiv 2609.21039, §3.2 in row form: `Z ↦ Z - sym(Z Aᵀ) A`. -/
lemma rowProj_apply (A Z : Matrix r n ℝ) : rowProj A Z = Z - symPart (Z * Aᵀ) * A := by
  rw [rowProj_eq, stiefelProj_apply, Matrix.transpose_sub, Matrix.transpose_mul,
    transpose_symPart, Matrix.transpose_transpose, Matrix.transpose_transpose,
    ← symPart_transpose (Z * Aᵀ), Matrix.transpose_mul, Matrix.transpose_transpose]

/-- arXiv 2609.21039, §3.2: the row form of the tangent projection is an orthogonal projector on
`ℝ^{r×n}` when `A Aᵀ = I`. -/
theorem isOrthProj_rowProj {A : Matrix r n ℝ} (hA : A * Aᵀ = 1) : IsOrthProj (rowProj A) := by
  have hX : Aᵀᵀ * Aᵀ = 1 := by simpa using hA
  have hP := isOrthProj_stiefelProj hX
  refine ⟨fun Z => ?_, fun Z Y => ?_⟩
  · simp only [rowProj_eq, Matrix.transpose_transpose, hP.idem]
  · simp only [rowProj_eq]
    calc ⟪(stiefelProj Aᵀ Zᵀ)ᵀ, Y⟫ = ⟪(stiefelProj Aᵀ Zᵀ)ᵀᵀ, Yᵀ⟫ :=
          (Frobenius.inner_transpose _ _).symm
      _ = ⟪stiefelProj Aᵀ Zᵀ, Yᵀ⟫ := by rw [Matrix.transpose_transpose]
      _ = ⟪Zᵀ, stiefelProj Aᵀ Yᵀ⟫ := hP.symm _ _
      _ = ⟪Zᵀᵀ, (stiefelProj Aᵀ Yᵀ)ᵀ⟫ := (Frobenius.inner_transpose _ _).symm
      _ = ⟪Z, (stiefelProj Aᵀ Yᵀ)ᵀ⟫ := by rw [Matrix.transpose_transpose]

/-- The range of the row form is `{ξ : A ξᵀ + ξ Aᵀ = 0}`. -/
theorem rowProj_eq_self_iff {A ξ : Matrix r n ℝ} (hA : A * Aᵀ = 1) :
    rowProj A ξ = ξ ↔ A * ξᵀ + ξ * Aᵀ = 0 := by
  have hX : Aᵀᵀ * Aᵀ = 1 := by simpa using hA
  rw [rowProj_eq]
  constructor
  · intro h
    have h' : stiefelProj Aᵀ ξᵀ = ξᵀ := by
      rw [← Matrix.transpose_transpose (stiefelProj Aᵀ ξᵀ), h]
    simpa using (stiefelProj_eq_self_iff hX).1 h'
  · intro h
    have h' : stiefelProj Aᵀ ξᵀ = ξᵀ := (stiefelProj_eq_self_iff hX).2 (by simpa using h)
    rw [h', Matrix.transpose_transpose]

end Stiefel

section Cayley

variable {n r : Type*} [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]

/-- For skew `Ω` the matrix `I - s Ω` is invertible, so (A.2) is well defined for every step size.
-/
theorem isUnit_one_sub_smul_skew {Ω : Matrix n n ℝ} (hΩ : Ωᵀ = -Ω) (s : ℝ) :
    IsUnit (1 - s • Ω) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  have hkey : ∀ v : n → ℝ, v ⬝ᵥ (Ω *ᵥ v) = 0 := fun v => by
    have h1 : v ⬝ᵥ (Ω *ᵥ v) = v ⬝ᵥ (Ωᵀ *ᵥ v) := by
      rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, dotProduct_comm]
    rw [hΩ, Matrix.neg_mulVec, dotProduct_neg] at h1
    linarith
  have hinj : ∀ v : n → ℝ, (1 - s • Ω) *ᵥ v = 0 → v = 0 := fun v hv => by
    have h2 : v = s • (Ω *ᵥ v) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, sub_eq_zero] at hv
      exact hv
    have h3 : v ⬝ᵥ v = 0 := by
      calc v ⬝ᵥ v = v ⬝ᵥ (s • (Ω *ᵥ v)) := by rw [← h2]
        _ = s * (v ⬝ᵥ (Ω *ᵥ v)) := by rw [dotProduct_smul, smul_eq_mul]
        _ = 0 := by rw [hkey, mul_zero]
    exact dotProduct_self_eq_zero.1 h3
  intro a b hab
  have := hinj (a - b) (by rw [Matrix.mulVec_sub, hab, sub_self])
  exact sub_eq_zero.1 this

/-- arXiv 2609.21039, eq. (A.2): `Y(α) = (I - α/2 Ω)⁻¹ (I + α/2 Ω) X`. -/
noncomputable def cayley (Ω : Matrix n n ℝ) (α : ℝ) (X : Matrix n r ℝ) : Matrix n r ℝ :=
  (1 - (α / 2) • Ω)⁻¹ * ((1 + (α / 2) • Ω) * X)

/-- arXiv 2609.21039, eq. (A.3): `Y(α) = X + α/2 Ω (X + Y(α))`. -/
theorem cayley_fixedPoint {Ω : Matrix n n ℝ} (hΩ : Ωᵀ = -Ω) (α : ℝ) (X : Matrix n r ℝ) :
    cayley Ω α X = X + (α / 2) • (Ω * (X + cayley Ω α X)) := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_one_sub_smul_skew hΩ (α / 2))
  have h : (1 - (α / 2) • Ω) * cayley Ω α X = (1 + (α / 2) • Ω) * X := by
    rw [cayley, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  rw [Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.one_mul, Matrix.smul_mul,
    Matrix.smul_mul] at h
  rw [Matrix.mul_add, smul_add]
  exact (sub_eq_iff_eq_add.1 h).trans (add_assoc _ _ _)

/-- Every solution of the implicit equation (A.3) preserves `Xᵀ X`. -/
theorem gram_eq_of_fixedPoint {Ω : Matrix n n ℝ} (hΩ : Ωᵀ = -Ω) {s : ℝ} {X Y : Matrix n r ℝ}
    (h : Y = X + s • (Ω * (X + Y))) : Yᵀ * Y = Xᵀ * X := by
  have hD : Y - X = s • (Ω * (X + Y)) := sub_eq_iff_eq_add'.2 h
  have h0 : (X + Y)ᵀ * (Y - X) + (Y - X)ᵀ * (X + Y) = 0 := by
    rw [hD, Matrix.transpose_smul, Matrix.transpose_mul, hΩ, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, smul_neg, add_neg_cancel]
  have h1 : (X + Y)ᵀ * (Y - X) + (Y - X)ᵀ * (X + Y) = (2 : ℝ) • (Yᵀ * Y - Xᵀ * X) := by
    simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub]
    module
  rw [h1] at h0
  have h2 := (smul_eq_zero.1 h0).resolve_left (by norm_num)
  exact sub_eq_zero.1 h2

/-- arXiv 2609.21039, App. A.2: the Cayley curve stays on the Stiefel manifold. -/
theorem cayley_stiefel {Ω : Matrix n n ℝ} (hΩ : Ωᵀ = -Ω) (α : ℝ) (X : Matrix n r ℝ) :
    (cayley Ω α X)ᵀ * cayley Ω α X = Xᵀ * X :=
  gram_eq_of_fixedPoint hΩ (cayley_fixedPoint hΩ α X)

/-- arXiv 2609.21039, App. A.2: `Y(0) = X`. -/
theorem cayley_zero (Ω : Matrix n n ℝ) (X : Matrix n r ℝ) : cayley Ω 0 X = X := by
  simp [cayley]

/-- The fixed-point map `F(Y) = X + α/2 Ω (X + Y)` of arXiv 2609.21039, App. A.2.2. -/
noncomputable def cayleyMap (Ω : Matrix n n ℝ) (α : ℝ) (X Y : Matrix n r ℝ) : Matrix n r ℝ :=
  X + (α / 2) • (Ω * (X + Y))

/-- The iterates (A.4) with `Y₀ = (I + α Ω) X`. -/
noncomputable def cayleyIter (Ω : Matrix n n ℝ) (α : ℝ) (X : Matrix n r ℝ) : ℕ → Matrix n r ℝ
  | 0 => (1 + α • Ω) * X
  | i + 1 => cayleyMap Ω α X (cayleyIter Ω α X i)

/-- The factor `ρ = |α|/2 ‖Ω‖₂` of Lemma A.1. -/
noncomputable def cayleyRho (Ω : Matrix n n ℝ) (α : ℝ) : ℝ := |α| / 2 * specNorm Ω

/-- `ρ ≥ 0`. -/
lemma cayleyRho_nonneg (Ω : Matrix n n ℝ) (α : ℝ) : 0 ≤ cayleyRho Ω α := by
  have := specNorm_nonneg Ω
  unfold cayleyRho
  positivity

/-- arXiv 2609.21039, Lemma A.1: `F` is Lipschitz with constant `ρ`, in the Frobenius norm. The
paper has `α ≥ 0` and assumes `ρ < 1`; neither is needed for the inequality. -/
theorem cayleyMap_contraction (Ω : Matrix n n ℝ) (α : ℝ) (X Y₁ Y₂ : Matrix n r ℝ) :
    ‖cayleyMap Ω α X Y₁ - cayleyMap Ω α X Y₂‖ ≤ cayleyRho Ω α * ‖Y₁ - Y₂‖ := by
  have h : cayleyMap Ω α X Y₁ - cayleyMap Ω α X Y₂ = (α / 2) • (Ω * (Y₁ - Y₂)) := by
    simp only [cayleyMap, Matrix.mul_add, Matrix.mul_sub, smul_add, smul_sub]
    abel
  rw [h, norm_smul, Real.norm_eq_abs, abs_div, abs_two]
  calc |α| / 2 * ‖Ω * (Y₁ - Y₂)‖ ≤ |α| / 2 * (specNorm Ω * ‖Y₁ - Y₂‖) := by
        gcongr; exact frob_mul_le _ _
    _ = cayleyRho Ω α * ‖Y₁ - Y₂‖ := by unfold cayleyRho; ring

/-- arXiv 2609.21039, Theorem A.2: `‖Y_i - Y*‖ ≤ ρⁱ ‖Y₀ - Y*‖`, eq. (A.5). -/
theorem cayleyIter_sub_le {Ω : Matrix n n ℝ} (hΩ : Ωᵀ = -Ω) (α : ℝ) (X : Matrix n r ℝ) (i : ℕ) :
    ‖cayleyIter Ω α X i - cayley Ω α X‖ ≤
      cayleyRho Ω α ^ i * ‖cayleyIter Ω α X 0 - cayley Ω α X‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hfix : cayleyMap Ω α X (cayley Ω α X) = cayley Ω α X :=
      (cayley_fixedPoint hΩ α X).symm
    calc ‖cayleyIter Ω α X (i + 1) - cayley Ω α X‖
        = ‖cayleyMap Ω α X (cayleyIter Ω α X i) - cayleyMap Ω α X (cayley Ω α X)‖ := by
          rw [hfix]; rfl
      _ ≤ cayleyRho Ω α * ‖cayleyIter Ω α X i - cayley Ω α X‖ := cayleyMap_contraction _ _ _ _ _
      _ ≤ cayleyRho Ω α * (cayleyRho Ω α ^ i * ‖cayleyIter Ω α X 0 - cayley Ω α X‖) := by
          gcongr; exact cayleyRho_nonneg _ _
      _ = _ := by ring

/-- arXiv 2609.21039, proof of Theorem A.2: for `ρ < 1` the exact Cayley point is the only fixed
point of `F`. -/
theorem cayley_unique_fixedPoint {Ω : Matrix n n ℝ} (hΩ : Ωᵀ = -Ω) {α : ℝ}
    (hρ : cayleyRho Ω α < 1) {X Y : Matrix n r ℝ} (hY : cayleyMap Ω α X Y = Y) :
    Y = cayley Ω α X := by
  have hfix : cayleyMap Ω α X (cayley Ω α X) = cayley Ω α X :=
    (cayley_fixedPoint hΩ α X).symm
  have h := cayleyMap_contraction Ω α X Y (cayley Ω α X)
  rw [hY, hfix] at h
  have h0 : ‖Y - cayley Ω α X‖ = 0 := by
    have := norm_nonneg (Y - cayley Ω α X)
    nlinarith
  exact sub_eq_zero.1 (norm_eq_zero.1 h0)

/-- `‖X‖_F = √r` on the Stiefel manifold. -/
theorem norm_of_stiefel {X : Matrix n r ℝ} (hX : Xᵀ * X = 1) : ‖X‖ = √(Fintype.card r) := by
  have h : Xᵀ * Xᵀᵀ = 1 := by simpa using hX
  rw [← Frobenius.norm_transpose X, ← norm_sq_of_rowOrthonormal h,
    Real.sqrt_sq (norm_nonneg _)]

/-- arXiv 2609.21039, eq. (A.7) with an explicit constant: `‖Y₀ - Y*‖ ≤ α²/2 ‖Ω‖₂² √r`.  With
`cayleyIter_sub_le` this gives the claim of §3.3 in the form `‖Y_k - Y*‖ = O(α^{2+k})`. -/
theorem cayleyIter_zero_sub_le {Ω : Matrix n n ℝ} (hΩ : Ωᵀ = -Ω) (α : ℝ) {X : Matrix n r ℝ}
    (hX : Xᵀ * X = 1) :
    ‖cayleyIter Ω α X 0 - cayley Ω α X‖ ≤
      α ^ 2 / 2 * specNorm Ω ^ 2 * √(Fintype.card r) := by
  have hgram : (cayley Ω α X)ᵀ * cayley Ω α X = 1 := (cayley_stiefel hΩ α X).trans hX
  have hnY := norm_of_stiefel hgram
  have hfp := cayley_fixedPoint hΩ α X
  generalize cayley Ω α X = Y at hfp hnY ⊢
  have hY0 : cayleyIter Ω α X 0 = X + α • (Ω * X) := by
    simp [cayleyIter, Matrix.add_mul, Matrix.smul_mul]
  have h0 : X + Y = (2 : ℝ) • X + (α / 2) • (Ω * (X + Y)) := by
    conv_lhs => rw [hfp]
    rw [two_smul, add_assoc]
  have h1 : Ω * (X + Y) = (2 : ℝ) • (Ω * X) + (α / 2) • (Ω * (Ω * (X + Y))) := by
    conv_lhs => rw [h0]
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  have h2 : Y = X + α • (Ω * X) + (α / 2) ^ 2 • (Ω * (Ω * (X + Y))) := by
    calc Y = X + (α / 2) • (Ω * (X + Y)) := hfp
      _ = X + (α / 2) • ((2 : ℝ) • (Ω * X) + (α / 2) • (Ω * (Ω * (X + Y)))) := by rw [← h1]
      _ = _ := by module
  have hdiff : cayleyIter Ω α X 0 - Y = (-(α / 2) ^ 2) • (Ω * (Ω * (X + Y))) := by
    rw [hY0, eq_sub_of_add_eq h2.symm]
    module
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
  have hZ : ‖X + Y‖ ≤ 2 * √(Fintype.card r) := by
    have := norm_add_le X Y
    rw [hnY, norm_of_stiefel hX] at this
    linarith
  have hnorm : ‖Ω * (Ω * (X + Y))‖ ≤ specNorm Ω ^ 2 * (2 * √(Fintype.card r)) := by
    have hs := specNorm_nonneg Ω
    calc ‖Ω * (Ω * (X + Y))‖ ≤ specNorm Ω * ‖Ω * (X + Y)‖ := frob_mul_le _ _
      _ ≤ specNorm Ω * (specNorm Ω * ‖X + Y‖) := by gcongr; exact frob_mul_le _ _
      _ ≤ specNorm Ω * (specNorm Ω * (2 * √(Fintype.card r))) := by gcongr
      _ = _ := by ring
  calc (α / 2) ^ 2 * ‖Ω * (Ω * (X + Y))‖
      ≤ (α / 2) ^ 2 * (specNorm Ω ^ 2 * (2 * √(Fintype.card r))) := by gcongr
    _ = _ := by ring

/-- arXiv 2609.21039, eq. (A.6): `Y(α) = X + α Ω X + O(α²)`, with an explicit constant. -/
theorem cayley_sub_first_order_le {Ω : Matrix n n ℝ} (hΩ : Ωᵀ = -Ω) (α : ℝ) {X : Matrix n r ℝ}
    (hX : Xᵀ * X = 1) :
    ‖cayley Ω α X - (X + α • (Ω * X))‖ ≤ α ^ 2 / 2 * specNorm Ω ^ 2 * √(Fintype.card r) := by
  have h := cayleyIter_zero_sub_le hΩ α hX
  have hY0 : cayleyIter Ω α X 0 = X + α • (Ω * X) := by
    simp [cayleyIter, Matrix.add_mul, Matrix.smul_mul]
  rwa [hY0, norm_sub_rev] at h

/-- arXiv 2609.21039, App. A.2: `Y'(0) = Ω X`. -/
theorem hasDerivAt_cayley {Ω : Matrix n n ℝ} (hΩ : Ωᵀ = -Ω) {X : Matrix n r ℝ}
    (hX : Xᵀ * X = 1) : HasDerivAt (fun α : ℝ => cayley Ω α X) (Ω * X) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun h : ℝ => cayley Ω (0 + h) X - cayley Ω 0 X - h • (Ω * X)) =O[𝓝 0]
      fun h : ℝ => h ^ 2 := by
    apply Asymptotics.IsBigO.of_bound (1 / 2 * specNorm Ω ^ 2 * √(Fintype.card r))
    refine Filter.Eventually.of_forall fun h => ?_
    have h1 := cayley_sub_first_order_le hΩ h hX
    rw [zero_add, cayley_zero, sub_sub, Real.norm_eq_abs, abs_pow, sq_abs]
    calc _ ≤ h ^ 2 / 2 * specNorm Ω ^ 2 * √(Fintype.card r) := h1
      _ = _ := by ring
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

/-- arXiv 2609.21039, Lemma A.3, in stronger form: for every number `s` of iterations, `‖Y_s - (X +
α Ω X)‖ ≤ (1 + ρˢ) α²/2 ‖Ω‖₂² √r`.  The paper has the weaker `O(α²) + O(ρˢ)`. -/
theorem cayleyIter_first_order {Ω : Matrix n n ℝ} (hΩ : Ωᵀ = -Ω) (α : ℝ) {X : Matrix n r ℝ}
    (hX : Xᵀ * X = 1) (s : ℕ) :
    ‖cayleyIter Ω α X s - (X + α • (Ω * X))‖ ≤
      (1 + cayleyRho Ω α ^ s) * (α ^ 2 / 2 * specNorm Ω ^ 2 * √(Fintype.card r)) := by
  have h1 := cayleyIter_sub_le hΩ α X s
  have h2 := cayleyIter_zero_sub_le hΩ α hX
  have h3 := cayley_sub_first_order_le hΩ α hX
  have hρ : 0 ≤ cayleyRho Ω α ^ s := pow_nonneg (cayleyRho_nonneg _ _) _
  have h4 : ‖cayleyIter Ω α X s - cayley Ω α X‖ ≤
      cayleyRho Ω α ^ s * (α ^ 2 / 2 * specNorm Ω ^ 2 * √(Fintype.card r)) :=
    h1.trans (by gcongr)
  calc ‖cayleyIter Ω α X s - (X + α • (Ω * X))‖
      = ‖(cayleyIter Ω α X s - cayley Ω α X) + (cayley Ω α X - (X + α • (Ω * X)))‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add h4 h3
    _ = _ := by ring

/-- arXiv 2609.21039, Lemma A.3, second part: for `ρ < 1` the iterates converge to the exact Cayley
point as `s → ∞`. -/
theorem tendsto_cayleyIter {Ω : Matrix n n ℝ} (hΩ : Ωᵀ = -Ω) {α : ℝ} (hρ : cayleyRho Ω α < 1)
    (X : Matrix n r ℝ) : Tendsto (cayleyIter Ω α X) atTop (𝓝 (cayley Ω α X)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h : Tendsto (fun i : ℕ => cayleyRho Ω α ^ i * ‖cayleyIter Ω α X 0 - cayley Ω α X‖) atTop
      (𝓝 (0 * ‖cayleyIter Ω α X 0 - cayley Ω α X‖)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (cayleyRho_nonneg _ _) hρ).mul_const _
  rw [zero_mul] at h
  exact squeeze_zero (fun _ => norm_nonneg _) (cayleyIter_sub_le hΩ α X) h

/-- The skew generator of arXiv 2609.21039, App. A.2.1: `Ω̂ = ξ Xᵀ - ½ X (Xᵀ ξ Xᵀ)`, `Ω = Ω̂ - Ω̂ᵀ`.
-/
noncomputable def cayleyOmega (X ξ : Matrix n r ℝ) : Matrix n n ℝ :=
  (ξ * Xᵀ - (1 / 2 : ℝ) • (X * (Xᵀ * ξ * Xᵀ))) - (ξ * Xᵀ - (1 / 2 : ℝ) • (X * (Xᵀ * ξ * Xᵀ)))ᵀ

/-- The generator is skew. -/
lemma cayleyOmega_transpose (X ξ : Matrix n r ℝ) : (cayleyOmega X ξ)ᵀ = -cayleyOmega X ξ := by
  rw [cayleyOmega, Matrix.transpose_sub, Matrix.transpose_transpose, neg_sub]

/-- The generator is homogeneous in `ξ`. -/
lemma cayleyOmega_smul (X ξ : Matrix n r ℝ) (α : ℝ) :
    cayleyOmega X (α • ξ) = α • cayleyOmega X ξ := by
  simp only [cayleyOmega, Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_sub,
    Matrix.transpose_smul]
  module

/-- arXiv 2609.21039, App. A.2.2 (`Y₀ = X + α ξ`): `Ω X = ξ` for tangent `ξ`. -/
theorem cayleyOmega_mul {X ξ : Matrix n r ℝ} (hX : Xᵀ * X = 1) (hξ : Xᵀ * ξ + ξᵀ * X = 0) :
    cayleyOmega X ξ * X = ξ := by
  have h1 : ξ * Xᵀ * X = ξ := by rw [Matrix.mul_assoc, hX, Matrix.mul_one]
  have h2 : X * (Xᵀ * ξ * Xᵀ) * X = X * (Xᵀ * ξ) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc (Xᵀ * ξ), hX, Matrix.mul_one]
  have h3 : (ξ * Xᵀ)ᵀ * X = X * (ξᵀ * X) := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have h4 : (X * (Xᵀ * ξ * Xᵀ))ᵀ * X = X * (ξᵀ * X) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, hX,
      Matrix.mul_one]
  have h5 : ξᵀ * X = -(Xᵀ * ξ) := eq_neg_of_add_eq_zero_right hξ
  simp only [cayleyOmega, Matrix.sub_mul, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.smul_mul, h1, h2, h3, h4, h5, Matrix.mul_neg]
  module

/-- The Cayley retraction `Retr_X(ξ) = (I - ½ Ω)⁻¹ (I + ½ Ω) X` of arXiv 2609.21039, App. A.2.1,
with `Ω = cayleyOmega X ξ`. -/
noncomputable def cayleyRetr (X ξ : Matrix n r ℝ) : Matrix n r ℝ :=
  cayley (cayleyOmega X ξ) 1 X

/-- `Retr_X(α ξ)` is the curve (A.2) of the generator of `ξ`. -/
theorem cayleyRetr_smul (X ξ : Matrix n r ℝ) (α : ℝ) :
    cayleyRetr X (α • ξ) = cayley (cayleyOmega X ξ) α X := by
  simp only [cayleyRetr, cayley, cayleyOmega_smul, smul_smul]
  congr 3 <;> ring_nf

/-- arXiv 2609.21039, App. A.2.1: `Retr_X(0) = X`. -/
theorem cayleyRetr_zero (X : Matrix n r ℝ) : cayleyRetr X 0 = X := by
  have h := cayleyRetr_smul X 0 0
  rw [zero_smul, cayley_zero] at h
  exact h

/-- arXiv 2609.21039, App. A.2: the Cayley retraction maps into the Stiefel manifold. -/
theorem cayleyRetr_stiefel {X : Matrix n r ℝ} (hX : Xᵀ * X = 1) (ξ : Matrix n r ℝ) :
    (cayleyRetr X ξ)ᵀ * cayleyRetr X ξ = 1 :=
  (cayley_stiefel (cayleyOmega_transpose X ξ) 1 X).trans hX

/-- arXiv 2609.21039, App. A.2.1: `D Retr_X(0) = Id` on the tangent space. -/
theorem hasDerivAt_cayleyRetr {X ξ : Matrix n r ℝ} (hX : Xᵀ * X = 1)
    (hξ : Xᵀ * ξ + ξᵀ * X = 0) : HasDerivAt (fun α : ℝ => cayleyRetr X (α • ξ)) ξ 0 := by
  have h := hasDerivAt_cayley (cayleyOmega_transpose X ξ) hX
  rw [cayleyOmega_mul hX hξ] at h
  simpa only [cayleyRetr_smul] using h

/-- `‖Ω‖_F ≤ 3 ‖ξ‖_F` on the Stiefel manifold. -/
theorem norm_cayleyOmega_le {X : Matrix n r ℝ} (hX : Xᵀ * X = 1) (ξ : Matrix n r ℝ) :
    ‖cayleyOmega X ξ‖ ≤ 3 * ‖ξ‖ := by
  have h1 : ‖ξ * Xᵀ‖ = ‖ξ‖ := Frobenius.norm_mul_transpose_of_orthonormal hX ξ
  have h2 : ‖X * (Xᵀ * ξ * Xᵀ)‖ ≤ ‖ξ‖ := by
    rw [Frobenius.norm_mul_of_orthonormal hX, Frobenius.norm_mul_transpose_of_orthonormal hX]
    exact norm_transpose_mul_le hX ξ
  have h3 : ‖ξ * Xᵀ - (1 / 2 : ℝ) • (X * (Xᵀ * ξ * Xᵀ))‖ ≤ 3 / 2 * ‖ξ‖ := by
    calc _ ≤ ‖ξ * Xᵀ‖ + ‖(1 / 2 : ℝ) • (X * (Xᵀ * ξ * Xᵀ))‖ := norm_sub_le _ _
      _ = ‖ξ‖ + 1 / 2 * ‖X * (Xᵀ * ξ * Xᵀ)‖ := by rw [h1, norm_smul]; norm_num
      _ ≤ _ := by linarith
  calc ‖cayleyOmega X ξ‖ ≤ _ := norm_sub_le _ _
    _ ≤ 3 * ‖ξ‖ := by rw [Frobenius.norm_transpose]; linarith

/-- The second-order bound used in arXiv 2609.21039, App. B ("Lagrange remainder"), with an explicit
constant: `‖Retr_X(ξ) - X - ξ‖_F ≤ 9/2 √r ‖ξ‖_F²` for tangent `ξ`. -/
theorem norm_cayleyRetr_sub_le {X ξ : Matrix n r ℝ} (hX : Xᵀ * X = 1)
    (hξ : Xᵀ * ξ + ξᵀ * X = 0) :
    ‖cayleyRetr X ξ - X - ξ‖ ≤ 9 / 2 * √(Fintype.card r) * ‖ξ‖ ^ 2 := by
  have h := cayley_sub_first_order_le (cayleyOmega_transpose X ξ) 1 hX
  rw [cayleyOmega_mul hX hξ, one_smul] at h
  have hs : specNorm (cayleyOmega X ξ) ≤ 3 * ‖ξ‖ :=
    (specNorm_le_frob _).trans (norm_cayleyOmega_le hX ξ)
  have hs0 := specNorm_nonneg (cayleyOmega X ξ)
  have hsq : specNorm (cayleyOmega X ξ) ^ 2 ≤ (3 * ‖ξ‖) ^ 2 := by gcongr
  have hr : 0 ≤ √(Fintype.card r : ℝ) := Real.sqrt_nonneg _
  calc ‖cayleyRetr X ξ - X - ξ‖ = ‖cayley (cayleyOmega X ξ) 1 X - (X + ξ)‖ := by
        rw [sub_sub]; rfl
    _ ≤ _ := h
    _ ≤ 1 ^ 2 / 2 * (3 * ‖ξ‖) ^ 2 * √(Fintype.card r) := by gcongr
    _ = _ := by ring

end Cayley

section Gradient

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

/-- The Hilbert space `ℝ^{m×r} × ℝ^{r×n}`, with the Frobenius structure on each factor. -/
abbrev FactorSpace (m n r : Type*) [Fintype m] [Fintype n] [Fintype r] :=
  WithLp 2 (Matrix m r ℝ × Matrix r n ℝ)

/-- The factorization map `Φ(B, A) = B A`. -/
noncomputable def factorMap (p : FactorSpace m n r) : Matrix m n ℝ := p.fst * p.snd

/-- The vector `(G Aᵀ, Bᵀ G)`: the Euclidean gradient of `L ∘ Φ` at `(B, A)` when `G = ∇L(B A)`. -/
noncomputable def factorGrad (G : Matrix m n ℝ) (p : FactorSpace m n r) : FactorSpace m n r :=
  WithLp.toLp 2 (G * p.sndᵀ, p.fstᵀ * G)

/-- arXiv 2609.21039, Algorithm 1 lines 1-2 and App. C: the chain rule `∇(L ∘ Φ)(B, A) = (∇L(W) Aᵀ,
Bᵀ ∇L(W))`. -/
theorem hasGradientAt_comp_factorMap {ℓ : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ}
    {p : FactorSpace m n r} (h : HasGradientAt ℓ G (factorMap p)) :
    HasGradientAt (fun q : FactorSpace m n r => ℓ (factorMap q)) (factorGrad G p) p := by
  have hfst : HasFDerivAt (fun q : FactorSpace m n r => q.fst)
      (WithLp.fstL 2 ℝ (Matrix m r ℝ) (Matrix r n ℝ)) p :=
    (WithLp.fstL 2 ℝ (Matrix m r ℝ) (Matrix r n ℝ)).hasFDerivAt
  have hsnd : HasFDerivAt (fun q : FactorSpace m n r => q.snd)
      (WithLp.sndL 2 ℝ (Matrix m r ℝ) (Matrix r n ℝ)) p :=
    (WithLp.sndL 2 ℝ (Matrix m r ℝ) (Matrix r n ℝ)).hasFDerivAt
  have hΦ := (Frobenius.mulCLM (m := m) (l := r) (n := n)).hasFDerivAt_of_bilinear hfst hsnd
  have hcomp := HasFDerivAt.comp (g := ℓ) (f := factorMap) p h.hasFDerivAt hΦ
  rw [hasGradientAt_iff_hasFDerivAt]
  refine hcomp.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
  change ⟪G, p.fst * q.snd + q.fst * p.snd⟫ = ⟪G * p.sndᵀ, q.fst⟫ + ⟪p.fstᵀ * G, q.snd⟫
  rw [inner_add_right, Frobenius.inner_mul_left', Frobenius.inner_mul_right', add_comm]

/-- `‖∇(L ∘ Φ)‖² = ‖G Aᵀ‖² + ‖Bᵀ G‖²`, the first line of arXiv 2609.21039, App. C. -/
theorem norm_factorGrad_sq (G : Matrix m n ℝ) (p : FactorSpace m n r) :
    ‖factorGrad G p‖ ^ 2 = ‖G * p.sndᵀ‖ ^ 2 + ‖p.fstᵀ * G‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rfl

/-- The Riemannian gradient of `L ∘ Φ` on `ℝ^{m×r} × St`: the `A` part of `factorGrad` is projected
onto the tangent space. -/
noncomputable def stiefelGrad (G : Matrix m n ℝ) (p : FactorSpace m n r) : FactorSpace m n r :=
  WithLp.toLp 2 (G * p.sndᵀ, rowProj p.snd (p.fstᵀ * G))

/-- `stiefelGrad` is tangent and represents the differential on tangent directions, which
characterizes the Riemannian gradient. -/
theorem stiefelGrad_spec {G : Matrix m n ℝ} {p q : FactorSpace m n r}
    (hA : p.snd * p.sndᵀ = 1) (hq : p.snd * q.sndᵀ + q.snd * p.sndᵀ = 0) :
    rowProj p.snd (stiefelGrad G p).snd = (stiefelGrad G p).snd ∧
      ⟪stiefelGrad G p, q⟫ = ⟪factorGrad G p, q⟫ := by
  have hP := isOrthProj_rowProj hA
  refine ⟨hP.idem _, ?_⟩
  have hq' : rowProj p.snd q.snd = q.snd := (rowProj_eq_self_iff hA).2 hq
  change ⟪G * p.sndᵀ, q.fst⟫ + ⟪rowProj p.snd (p.fstᵀ * G), q.snd⟫ =
    ⟪G * p.sndᵀ, q.fst⟫ + ⟪p.fstᵀ * G, q.snd⟫
  rw [hP.symm, hq']

/-- The Riemannian gradient is no longer than the Euclidean one. -/
theorem norm_stiefelGrad_le {G : Matrix m n ℝ} {p : FactorSpace m n r}
    (hA : p.snd * p.sndᵀ = 1) : ‖stiefelGrad G p‖ ≤ ‖factorGrad G p‖ := by
  have hP := isOrthProj_rowProj hA
  have h : ‖stiefelGrad G p‖ ^ 2 ≤ ‖factorGrad G p‖ ^ 2 := by
    rw [norm_factorGrad_sq, WithLp.prod_norm_sq_eq_of_L2]
    have := hP.norm_le (p.fstᵀ * G)
    change ‖G * p.sndᵀ‖ ^ 2 + ‖rowProj p.snd (p.fstᵀ * G)‖ ^ 2 ≤ _
    gcongr
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- arXiv 2609.21039, Proposition 4.3, second claim, with an explicit bound: `‖∇(L ∘ Φ)‖ ≤ ‖G‖ √(1 +
‖W‖²)` on the constrained fiber.  Unlike the paper's proof this does not use that the fiber is one
`O(r)`-orbit, which fails for `rank W < r`. -/
theorem norm_factorGrad_le_of_mem_stiefelFiber {G W : Matrix m n ℝ}
    {p : Matrix m r ℝ × Matrix r n ℝ} (hp : p ∈ stiefelFiber r W) :
    ‖factorGrad G (WithLp.toLp 2 p)‖ ≤ ‖G‖ * √(1 + ‖W‖ ^ 2) := by
  obtain ⟨B, A⟩ := p
  obtain ⟨hW, hA⟩ := hp
  have hAt : Aᵀᵀ * Aᵀ = 1 := by simpa using hA
  have h1 : ‖G * Aᵀ‖ ≤ ‖G‖ := norm_mul_le_of_orthonormal hAt G
  have hB : ‖B‖ = ‖W‖ := by rw [← hW, norm_mul_eq_of_rowOrthonormal hA]
  have h2 : ‖Bᵀ * G‖ ≤ ‖W‖ * ‖G‖ := by
    calc ‖Bᵀ * G‖ ≤ ‖Bᵀ‖ * ‖G‖ := Frobenius.norm_mul_le _ _
      _ = ‖W‖ * ‖G‖ := by rw [Frobenius.norm_transpose, hB]
  have hsq : ‖factorGrad G (WithLp.toLp 2 (B, A))‖ ^ 2 ≤ (‖G‖ * √(1 + ‖W‖ ^ 2)) ^ 2 := by
    rw [norm_factorGrad_sq, mul_pow, Real.sq_sqrt (by positivity)]
    change ‖G * Aᵀ‖ ^ 2 + ‖Bᵀ * G‖ ^ 2 ≤ _
    have h3 : ‖G * Aᵀ‖ ^ 2 ≤ ‖G‖ ^ 2 := by gcongr
    have h4 : ‖Bᵀ * G‖ ^ 2 ≤ (‖W‖ * ‖G‖) ^ 2 := by gcongr
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq

/-- **arXiv 2609.21039, Proposition 4.3, second claim**: on the fiber of the constrained map the
gradient of `L ∘ Φ` is bounded, both the Euclidean gradient and the Riemannian one.  Holds for every
`W`, without the hypotheses `rank W ≤ r` and `∇L(W) ≠ 0`. -/
theorem proposition_4_3_second_claim (G W : Matrix m n ℝ) :
    BddAbove ((fun p : Matrix m r ℝ × Matrix r n ℝ => ‖factorGrad G (WithLp.toLp 2 p)‖) ''
      stiefelFiber r W) ∧
    BddAbove ((fun p : Matrix m r ℝ × Matrix r n ℝ => ‖stiefelGrad G (WithLp.toLp 2 p)‖) ''
      stiefelFiber r W) := by
  constructor
  · refine ⟨‖G‖ * √(1 + ‖W‖ ^ 2), ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact norm_factorGrad_le_of_mem_stiefelFiber hp
  · refine ⟨‖G‖ * √(1 + ‖W‖ ^ 2), ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact (norm_stiefelGrad_le hp.2).trans (norm_factorGrad_le_of_mem_stiefelFiber hp)

/-- The chain rule as an equation for `gradient`. -/
theorem gradient_comp_factorMap {ℓ : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ}
    {p : FactorSpace m n r} (h : HasGradientAt ℓ G (factorMap p)) :
    gradient (fun q : FactorSpace m n r => ℓ (factorMap q)) p = factorGrad G p :=
  (hasGradientAt_comp_factorMap h).gradient

/-- arXiv 2609.21039, App. C: along `(t B, t⁻¹ A)` the gradient of `L ∘ Φ` is unbounded as soon as
it does not vanish at `(B, A)`.  This hypothesis is missing in the paper. -/
theorem not_bddAbove_of_ne_zero {G : Matrix m n ℝ} {B : Matrix m r ℝ} {A : Matrix r n ℝ}
    (h : G * Aᵀ ≠ 0 ∨ Bᵀ * G ≠ 0) :
    ¬ BddAbove ((fun p : Matrix m r ℝ × Matrix r n ℝ => ‖factorGrad G (WithLp.toLp 2 p)‖) ''
      fiber r (B * A)) := by
  rintro ⟨C, hC⟩
  have hmem : ∀ t : ℝ, t ≠ 0 → (t • B, t⁻¹ • A) ∈ fiber r (B * A) := fun t ht => by
    change t • B * t⁻¹ • A = B * A
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ht, one_smul]
  have hbd : ∀ t : ℝ, t ≠ 0 →
      ‖t⁻¹ • (G * Aᵀ)‖ ≤ C ∧ ‖t • (Bᵀ * G)‖ ≤ C := fun t ht => by
    have h1 : ‖factorGrad G (WithLp.toLp 2 (t • B, t⁻¹ • A))‖ ≤ C :=
      hC ⟨_, hmem t ht, rfl⟩
    have h2 := norm_factorGrad_sq G (WithLp.toLp 2 (t • B, t⁻¹ • A) : FactorSpace m n r)
    have h3 : G * (t⁻¹ • A)ᵀ = t⁻¹ • (G * Aᵀ) := by
      rw [Matrix.transpose_smul, Matrix.mul_smul]
    have h4 : (t • B)ᵀ * G = t • (Bᵀ * G) := by
      rw [Matrix.transpose_smul, Matrix.smul_mul]
    change _ = ‖G * (t⁻¹ • A)ᵀ‖ ^ 2 + ‖(t • B)ᵀ * G‖ ^ 2 at h2
    rw [h3, h4] at h2
    have hn := norm_nonneg (factorGrad G (WithLp.toLp 2 (t • B, t⁻¹ • A)))
    have hC0 : 0 ≤ C := hn.trans h1
    constructor
    · refine (sq_le_sq₀ (norm_nonneg _) hC0).1 ?_
      nlinarith [sq_nonneg ‖t • (Bᵀ * G)‖]
    · refine (sq_le_sq₀ (norm_nonneg _) hC0).1 ?_
      nlinarith [sq_nonneg ‖t⁻¹ • (G * Aᵀ)‖]
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hbd 1 one_ne_zero).1
  rcases h with h | h
  · have ha : 0 < ‖G * Aᵀ‖ := norm_pos_iff.2 h
    have ht : ‖G * Aᵀ‖ / (C + 1) ≠ 0 := by positivity
    have := (hbd _ ht).1
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity), inv_div,
      div_mul_cancel₀ _ ha.ne'] at this
    linarith
  · have ha : 0 < ‖Bᵀ * G‖ := norm_pos_iff.2 h
    have ht : (C + 1) / ‖Bᵀ * G‖ ≠ 0 := by positivity
    have := (hbd _ ht).2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
      div_mul_cancel₀ _ ha.ne'] at this
    linarith

/-- A factorization of `W` with `card r` factors whose last rows are prescribed. -/
private theorem exists_factorization_aux {W : Matrix m n ℝ} {k : ℕ}
    (hk : W.rank + k = Fintype.card r) (A₂ : Matrix (Fin k) n ℝ) :
    ∃ (B : Matrix m r ℝ) (A : Matrix r n ℝ) (e : Fin W.rank ⊕ Fin k ≃ r),
      B * A = W ∧ ∀ i, A (e (Sum.inr i)) = A₂ i := by
  obtain ⟨U, -, hcap⟩ := exists_orthonormal_capture W (le_refl W.rank) W.rank_le_card_height
  let e : Fin W.rank ⊕ Fin k ≃ r := Fintype.equivOfCardEq (by simp [hk])
  refine ⟨(Matrix.fromCols U 0).submatrix id e.symm,
    (Matrix.fromRows (Uᵀ * W) A₂).submatrix e.symm id, e, ?_, fun i => ?_⟩
  · rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, Matrix.zero_mul, add_zero,
      ← Matrix.mul_assoc, hcap]
    simp
  · ext j
    simp

/-- Every `W` with `rank W ≤ r` factorizes as `B A`. -/
theorem exists_factorization {W : Matrix m n ℝ} (h : W.rank ≤ Fintype.card r) :
    ∃ (B : Matrix m r ℝ) (A : Matrix r n ℝ), B * A = W := by
  obtain ⟨B, A, -, hBA, -⟩ := exists_factorization_aux (r := r) (W := W)
    (Nat.add_sub_cancel' h) 0
  exact ⟨B, A, hBA⟩

/-- At full rank, `G Wᵀ = 0` and `Wᵀ G = 0` force `G Aᵀ = 0` and `Bᵀ G = 0`. -/
private theorem factor_grad_eq_zero {G W : Matrix m n ℝ} {B : Matrix m r ℝ} {A : Matrix r n ℝ}
    (hrB : B.rank = Fintype.card r) (hrA : A.rank = Fintype.card r) (hW : B * A = W)
    (h2 : G * Wᵀ = 0) (h3 : Wᵀ * G = 0) : G * Aᵀ = 0 ∧ Bᵀ * G = 0 := by
  obtain ⟨L, hL⟩ := exists_leftInverse hrB
  obtain ⟨R, hR⟩ := exists_rightInverse hrA
  have hLt : Bᵀ * Lᵀ = 1 := by
    have := congrArg Matrix.transpose hL
    simpa [Matrix.transpose_mul] using this
  have hRt : Rᵀ * Aᵀ = 1 := by
    have := congrArg Matrix.transpose hR
    simpa [Matrix.transpose_mul] using this
  constructor
  · have h5 : G * Aᵀ * Bᵀ = 0 := by
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hW, h2]
    have := congrArg (· * Lᵀ) h5
    simpa only [Matrix.mul_assoc, hLt, Matrix.mul_one, Matrix.zero_mul] using this
  · have h7 : Aᵀ * (Bᵀ * G) = 0 := by
      rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, hW, h3]
    have := congrArg (Rᵀ * ·) h7
    simpa only [← Matrix.mul_assoc, hRt, Matrix.one_mul, Matrix.mul_zero] using this

/-- **arXiv 2609.21039, Proposition 4.3, first claim, corrected and sharp.**  Let `rank W ≤ r` and
`G = ∇L(W) ≠ 0`.  Then `‖∇(L ∘ Φ)‖_{L^∞(F)} = +∞` if and only if `rank W < r` or `G Wᵀ ≠ 0` or `Wᵀ G
≠ 0`.  The paper claims `+∞` unconditionally, which is false, see
`proposition_4_3_first_claim_false`.  The excluded case is exactly a critical point of `L` on the
rank-`r` matrices. -/
theorem not_bddAbove_grad_fiber_iff {G W : Matrix m n ℝ} (hrank : W.rank ≤ Fintype.card r)
    (hG : G ≠ 0) :
    ¬ BddAbove ((fun p : Matrix m r ℝ × Matrix r n ℝ => ‖factorGrad G (WithLp.toLp 2 p)‖) ''
      fiber r W) ↔ W.rank < Fintype.card r ∨ G * Wᵀ ≠ 0 ∨ Wᵀ * G ≠ 0 := by
  classical
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    have hre : W.rank = Fintype.card r := le_antisymm hrank h1
    apply h
    refine ⟨0, ?_⟩
    rintro _ ⟨⟨B, A⟩, hp, rfl⟩
    have hW : B * A = W := hp
    have hrB : B.rank = Fintype.card r := by
      apply le_antisymm (by simpa using B.rank_le_card_width)
      calc Fintype.card r = W.rank := hre.symm
        _ = (B * A).rank := by rw [hW]
        _ ≤ B.rank := Matrix.rank_mul_le_left _ _
    have hrA : A.rank = Fintype.card r := by
      apply le_antisymm (by simpa using A.rank_le_card_height)
      calc Fintype.card r = W.rank := hre.symm
        _ = (B * A).rank := by rw [hW]
        _ ≤ A.rank := Matrix.rank_mul_le_right _ _
    obtain ⟨h4, h6⟩ := factor_grad_eq_zero hrB hrA hW h2 h3
    have h8 := norm_factorGrad_sq G (WithLp.toLp 2 (B, A) : FactorSpace m n r)
    change _ = ‖G * Aᵀ‖ ^ 2 + ‖Bᵀ * G‖ ^ 2 at h8
    rw [h4, h6] at h8
    simp only [norm_zero] at h8
    have h9 : ‖factorGrad G (WithLp.toLp 2 (B, A))‖ ^ 2 = 0 := by rw [h8]; norm_num
    exact (pow_eq_zero_iff (by norm_num)).1 h9 |>.le
  · rintro (h | h | h)
    · obtain ⟨i, j, hij⟩ : ∃ i j, G i j ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hG (Matrix.ext hcon)
      obtain ⟨k, hk⟩ : ∃ k, W.rank + (k + 1) = Fintype.card r :=
        ⟨Fintype.card r - W.rank - 1, by omega⟩
      obtain ⟨B, A, e, hBA, hA⟩ := exists_factorization_aux (r := r) (W := W) hk
        (Matrix.of fun _ c => if c = j then 1 else 0)
      rw [← hBA]
      apply not_bddAbove_of_ne_zero
      left
      intro h0
      have h1 := congrFun (congrFun h0 i) (e (Sum.inr 0))
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hA, Matrix.zero_apply] at h1
      simp [hij] at h1
    · obtain ⟨B, A, hBA⟩ := exists_factorization (r := r) hrank
      rw [← hBA] at h ⊢
      apply not_bddAbove_of_ne_zero
      left
      intro h0
      apply h
      rw [Matrix.transpose_mul, ← Matrix.mul_assoc, h0, Matrix.zero_mul]
    · obtain ⟨B, A, hBA⟩ := exists_factorization (r := r) hrank
      rw [← hBA] at h ⊢
      apply not_bddAbove_of_ne_zero
      right
      intro h0
      apply h
      rw [Matrix.transpose_mul, Matrix.mul_assoc, h0, Matrix.mul_zero]

/-- The gradient of `y ↦ ½ ‖y - c‖²`. -/
theorem hasGradientAt_half_norm_sq_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (c x : E) :
    HasGradientAt (fun y : E => (1 / 2 : ℝ) * ‖y - c‖ ^ 2) (x - c) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (((hasFDerivAt_id x).sub_const c).norm_sq).const_mul (1 / 2 : ℝ)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
  simp [InnerProductSpace.toDual_apply_apply]

/-- **arXiv 2609.21039, Proposition 4.3, first claim, is false.**  Take `m = n = 2`, `r = 1`, the
paper's own loss `L(X) = ½ ‖X - I‖²` of §4.2, and its best rank-one approximation `W = diag(1, 0)`.
Then `rank W ≤ r` and `∇L(W) = diag(0, -1) ≠ 0`, but `∇(L ∘ Φ)` vanishes on the whole fiber, so its
supremum is `0` and not `+∞`.  The paper's proof takes `t → 0` without checking that `∇L(W) Aᵀ` or
`Bᵀ ∇L(W)` is nonzero. -/
theorem proposition_4_3_first_claim_false :
    ∃ (ℓ : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (W G : Matrix (Fin 2) (Fin 2) ℝ),
      HasGradientAt ℓ G W ∧ W.rank ≤ Fintype.card (Fin 1) ∧ G ≠ 0 ∧
      (∀ p : Matrix (Fin 2) (Fin 1) ℝ × Matrix (Fin 1) (Fin 2) ℝ, p ∈ fiber (Fin 1) W →
        gradient (fun q : FactorSpace (Fin 2) (Fin 2) (Fin 1) => ℓ (factorMap q))
          (WithLp.toLp 2 p) = 0) ∧
      BddAbove ((fun p : Matrix (Fin 2) (Fin 1) ℝ × Matrix (Fin 1) (Fin 2) ℝ =>
        ‖factorGrad G (WithLp.toLp 2 p)‖) '' fiber (Fin 1) W) := by
  let W : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
  let G : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, -1]
  let B₀ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]
  let A₀ : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]
  have hG : G ≠ 0 := by
    intro h
    have := congrFun (congrFun h 1) 1
    simp [G] at this
  have hW : B₀ * A₀ = W := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [B₀, A₀, W, Matrix.mul_apply]
  have hrank1 : W.rank ≤ Fintype.card (Fin 1) := by
    rw [← hW]
    exact Matrix.rank_mul_le_left _ _ |>.trans (by simpa using B₀.rank_le_card_width)
  have hrank2 : Fintype.card (Fin 1) ≤ W.rank := by
    have h1 : B₀ᵀ * W * A₀ᵀ = 1 := by
      ext i j; fin_cases i; fin_cases j
      simp [B₀, A₀, W, Matrix.mul_apply, Fin.sum_univ_two]
    calc Fintype.card (Fin 1) = (1 : Matrix (Fin 1) (Fin 1) ℝ).rank := Matrix.rank_one.symm
      _ = (B₀ᵀ * W * A₀ᵀ).rank := by rw [h1]
      _ ≤ (B₀ᵀ * W).rank := Matrix.rank_mul_le_left _ _
      _ ≤ W.rank := Matrix.rank_mul_le_right _ _
  have h1 : G * Wᵀ = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [G, W, Matrix.mul_apply, Fin.sum_univ_two]
  have h2 : Wᵀ * G = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [G, W, Matrix.mul_apply, Fin.sum_univ_two]
  have hre : W.rank = Fintype.card (Fin 1) := le_antisymm hrank1 hrank2
  have hzero : ∀ p : Matrix (Fin 2) (Fin 1) ℝ × Matrix (Fin 1) (Fin 2) ℝ, p ∈ fiber (Fin 1) W →
      factorGrad G (WithLp.toLp 2 p) = 0 := by
    rintro ⟨B, A⟩ hp
    have hBA : B * A = W := hp
    have hrB : B.rank = Fintype.card (Fin 1) := by
      apply le_antisymm (by simpa using B.rank_le_card_width)
      calc Fintype.card (Fin 1) = W.rank := hre.symm
        _ = (B * A).rank := by rw [hBA]
        _ ≤ B.rank := Matrix.rank_mul_le_left _ _
    have hrA : A.rank = Fintype.card (Fin 1) := by
      apply le_antisymm (by simpa using A.rank_le_card_height)
      calc Fintype.card (Fin 1) = W.rank := hre.symm
        _ = (B * A).rank := by rw [hBA]
        _ ≤ A.rank := Matrix.rank_mul_le_right _ _
    obtain ⟨h3, h4⟩ := factor_grad_eq_zero hrB hrA hBA h1 h2
    change WithLp.toLp 2 (G * Aᵀ, Bᵀ * G) = 0
    rw [h3, h4]
    rfl
  have hgrad : HasGradientAt (fun X : Matrix (Fin 2) (Fin 2) ℝ => (1 / 2 : ℝ) * ‖X - 1‖ ^ 2)
      G W := by
    have hGW : W - 1 = G := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [W, G]
    rw [← hGW]
    exact hasGradientAt_half_norm_sq_sub 1 W
  refine ⟨fun X => (1 / 2 : ℝ) * ‖X - 1‖ ^ 2, W, G, hgrad, hrank1, hG, fun p hp => ?_, 0, ?_⟩
  · have h3 : factorMap (WithLp.toLp 2 p : FactorSpace (Fin 2) (Fin 2) (Fin 1)) = W := hp
    have h4 := gradient_comp_factorMap (ℓ := fun X => (1 / 2 : ℝ) * ‖X - 1‖ ^ 2) (G := G)
      (p := (WithLp.toLp 2 p : FactorSpace (Fin 2) (Fin 2) (Fin 1)))
      (by rw [h3]; exact hgrad)
    exact h4.trans (hzero p hp)
  · rintro _ ⟨p, hp, rfl⟩
    simp only [hzero p hp, norm_zero, le_refl]

end Gradient

section AlgorithmDefs

variable {p q : Type*}

/-- The elementwise direction `M / √(V + ε)` (arXiv 2609.21039, Algorithm 1 lines 7 and 9). -/
noncomputable def precond (ε : ℝ) (M V : Matrix p q ℝ) : Matrix p q ℝ :=
  Matrix.of fun i j => M i j / √(V i j + ε)

/-- First moment, Algorithm 1 lines 3-4. -/
def firstMoment (β : ℝ) (M G : Matrix p q ℝ) : Matrix p q ℝ := β • M + (1 - β) • G

/-- Second moment, Algorithm 1 lines 5-6. -/
def secondMoment (β₂ : ℝ) (V G : Matrix p q ℝ) : Matrix p q ℝ :=
  β₂ • V + (1 - β₂) • (G ⊙ G)

/-- The entrywise maximum (H5) of arXiv 2609.21039: `V ↦ max(β₂ V + (1 - β₂) G^{∘2}, V)`. -/
noncomputable def amsMoment (β₂ : ℝ) (V G : Matrix p q ℝ) : Matrix p q ℝ :=
  Matrix.of fun i j => max (secondMoment β₂ V G i j) (V i j)

/-- The diagonal metric `S = √(V + ε)`. -/
noncomputable def sqrtWeight (ε : ℝ) (V : Matrix p q ℝ) : Matrix p q ℝ :=
  Matrix.of fun i j => √(V i j + ε)

variable [Fintype p] [Fintype q]

/-- The weighted square `∑ S_{ij} X_{ij}²`. -/
def wnorm (S X : Matrix p q ℝ) : ℝ := ∑ i, ∑ j, S i j * X i j ^ 2

/-- The weighted inner product `∑ S_{ij} X_{ij} Y_{ij}`. -/
def winner (S X Y : Matrix p q ℝ) : ℝ := ∑ i, ∑ j, S i j * (X i j * Y i j)

/-- Expansion of the weighted square. -/
lemma wnorm_add (S X Y : Matrix p q ℝ) :
    wnorm S (X + Y) = wnorm S X + 2 * winner S X Y + wnorm S Y := by
  simp only [wnorm, winner, Finset.mul_sum, ← Finset.sum_add_distrib, Matrix.add_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Homogeneity of the weighted square. -/
lemma wnorm_smul (S X : Matrix p q ℝ) (c : ℝ) : wnorm S (c • X) = c ^ 2 * wnorm S X := by
  simp only [wnorm, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Additivity of the weighted inner product. -/
lemma winner_add_right (S X Y Z : Matrix p q ℝ) :
    winner S X (Y + Z) = winner S X Y + winner S X Z := by
  simp only [winner, ← Finset.sum_add_distrib, Matrix.add_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Homogeneity of the weighted inner product. -/
lemma winner_smul_right (S X Y : Matrix p q ℝ) (c : ℝ) :
    winner S X (c • Y) = c * winner S X Y := by
  simp only [winner, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Additivity of the weighted inner product, for differences. -/
lemma winner_sub_right (S X Y Z : Matrix p q ℝ) :
    winner S X (Y - Z) = winner S X Y - winner S X Z := by
  simp only [winner, ← Finset.sum_sub_distrib, Matrix.sub_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `⟨X, M / S⟩_S = ⟨X, M⟩`. -/
lemma winner_precond {ε : ℝ} (hε : 0 < ε) {V : Matrix p q ℝ} (hV : ∀ i j, 0 ≤ V i j)
    (X M : Matrix p q ℝ) : winner (sqrtWeight ε V) X (precond ε M V) = ⟪X, M⟫ := by
  rw [Frobenius.inner_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : √(V i j + ε) ≠ 0 := (Real.sqrt_pos.2 (by linarith [hV i j])).ne'
  simp only [sqrtWeight, precond, Matrix.of_apply]
  field_simp

/-- Upper bound of the weighted square by the Frobenius norm. -/
lemma wnorm_le {S : Matrix p q ℝ} {c : ℝ} (hS : ∀ i j, S i j ≤ c) (X : Matrix p q ℝ) :
    wnorm S X ≤ c * ‖X‖ ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hS i j) (sq_nonneg _)

/-- Cauchy-Schwarz for the weighted inner product. -/
lemma winner_le {S : Matrix p q ℝ} {c : ℝ} (hc : 0 ≤ c) (hS0 : ∀ i j, 0 ≤ S i j)
    (hS : ∀ i j, S i j ≤ c) (X Y : Matrix p q ℝ) : winner S X Y ≤ c * (‖X‖ * ‖Y‖) := by
  have h1 : winner S X Y = ⟪Matrix.of fun i j => S i j * X i j, Y⟫ := by
    rw [Frobenius.inner_def]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [mul_assoc]
  have h2 : ‖(Matrix.of fun i j => S i j * X i j : Matrix p q ℝ)‖ ≤ c * ‖X‖ := by
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
    rw [mul_pow, Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [Matrix.of_apply, mul_pow]
    have : S i j ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (hS0 i j) (hS i j) 2
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  rw [h1]
  calc _ ≤ ‖(Matrix.of fun i j => S i j * X i j : Matrix p q ℝ)‖ * ‖Y‖ := real_inner_le_norm _ _
    _ ≤ c * ‖X‖ * ‖Y‖ := by gcongr
    _ = _ := by ring

end AlgorithmDefs

section AdamSeq

variable {p q : Type*} [Fintype p] [Fintype q]

/-- The moment recursions of one factor under (H4) and (H5), with `M₀ = V₀ = 0`. -/
structure AdamSeq (β : ℕ → ℝ) (β₂ ε G : ℝ) (g M V : ℕ → Matrix p q ℝ) : Prop where
  M0 : M 0 = 0
  V0 : V 0 = 0
  Msucc : ∀ t, M (t + 1) = firstMoment (β (t + 1)) (M t) (g (t + 1))
  Vsucc : ∀ t, V (t + 1) = amsMoment β₂ (V t) (g (t + 1))
  β0 : ∀ t, 0 ≤ β t
  β1 : ∀ t, β t ≤ 1
  β₂0 : 0 ≤ β₂
  β₂1 : β₂ ≤ 1
  ε0 : 0 < ε
  G0 : 0 ≤ G
  g_le : ∀ t, 1 ≤ t → ∀ i j, |g t i j| ≤ G

namespace AdamSeq

variable {β : ℕ → ℝ} {β₂ ε G : ℝ} {g M V : ℕ → Matrix p q ℝ}

/-- `|M_t| ≤ G∞`, the bound `‖M_t‖ ≤ G∞` of arXiv 2609.21039, App. B. -/
lemma abs_M_le (h : AdamSeq β β₂ ε G g M V) (t : ℕ) (i : p) (j : q) : |M t i j| ≤ G := by
  induction t with
  | zero => simpa [h.M0] using h.G0
  | succ t ih =>
    have h1 := h.g_le (t + 1) (by omega) i j
    have hb0 := h.β0 (t + 1)
    have hb1 := h.β1 (t + 1)
    rw [h.Msucc]
    simp only [firstMoment, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    calc |β (t + 1) * M t i j + (1 - β (t + 1)) * g (t + 1) i j|
        ≤ |β (t + 1) * M t i j| + |(1 - β (t + 1)) * g (t + 1) i j| := abs_add_le _ _
      _ = β (t + 1) * |M t i j| + (1 - β (t + 1)) * |g (t + 1) i j| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hb0, abs_of_nonneg (sub_nonneg.2 hb1)]
      _ ≤ β (t + 1) * G + (1 - β (t + 1)) * G := by
          have : 0 ≤ 1 - β (t + 1) := by linarith
          gcongr
      _ = G := by ring

/-- The second moment is nonnegative. -/
lemma V_nonneg (h : AdamSeq β β₂ ε G g M V) (t : ℕ) (i : p) (j : q) : 0 ≤ V t i j := by
  induction t with
  | zero => simp [h.V0]
  | succ t ih =>
    rw [h.Vsucc]
    exact ih.trans (le_max_right _ _)

/-- (H5) makes the second moment nondecreasing. -/
lemma V_mono (h : AdamSeq β β₂ ε G g M V) (t : ℕ) (i : p) (j : q) : V t i j ≤ V (t + 1) i j := by
  rw [h.Vsucc]
  exact le_max_right _ _

/-- The second moment is bounded by `G∞²`. -/
lemma V_le (h : AdamSeq β β₂ ε G g M V) (t : ℕ) (i : p) (j : q) : V t i j ≤ G ^ 2 := by
  induction t with
  | zero => simpa [h.V0] using sq_nonneg G
  | succ t ih =>
    rw [h.Vsucc, amsMoment, Matrix.of_apply]
    refine max_le ?_ ih
    have h1 := h.g_le (t + 1) (by omega) i j
    have h2 : g (t + 1) i j ^ 2 ≤ G ^ 2 := sq_le_sq' (by linarith [abs_le.1 h1]) (abs_le.1 h1).2
    have h3 := h.β₂0
    have h4 := h.β₂1
    simp only [secondMoment, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.hadamard_apply]
    nlinarith [mul_le_mul_of_nonneg_left ih h3,
      mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 h4)]

/-- `√ε ≤ S_t`. -/
lemma sqrt_lower (h : AdamSeq β β₂ ε G g M V) (t : ℕ) (i : p) (j : q) :
    √ε ≤ sqrtWeight ε (V t) i j :=
  Real.sqrt_le_sqrt (by linarith [h.V_nonneg t i j])

/-- `S_t ≤ √(G∞² + ε)`. -/
lemma sqrt_upper (h : AdamSeq β β₂ ε G g M V) (t : ℕ) (i : p) (j : q) :
    sqrtWeight ε (V t) i j ≤ √(G ^ 2 + ε) :=
  Real.sqrt_le_sqrt (by linarith [h.V_le t i j])

/-- `S_t` is nondecreasing. -/
lemma sqrt_mono (h : AdamSeq β β₂ ε G g M V) (t : ℕ) (i : p) (j : q) :
    sqrtWeight ε (V t) i j ≤ sqrtWeight ε (V (t + 1)) i j :=
  Real.sqrt_le_sqrt (by linarith [h.V_mono t i j])

/-- `S_t > 0`. -/
lemma sqrt_pos (h : AdamSeq β β₂ ε G g M V) (t : ℕ) (i : p) (j : q) :
    0 < sqrtWeight ε (V t) i j :=
  (Real.sqrt_pos.2 h.ε0).trans_le (h.sqrt_lower t i j)

/-- `‖M_t / S_t‖²_{S_t} ≤ N G∞² / √ε`. -/
lemma wnorm_precond_le (h : AdamSeq β β₂ ε G g M V) (t : ℕ) :
    wnorm (sqrtWeight ε (V t)) (precond ε (M t) (V t)) ≤
      Fintype.card p * Fintype.card q * (G ^ 2 / √ε) := by
  have hentry : ∀ i j, sqrtWeight ε (V t) i j * precond ε (M t) (V t) i j ^ 2 ≤ G ^ 2 / √ε := by
    intro i j
    have hS := h.sqrt_pos t i j
    have hS' := h.sqrt_lower t i j
    have hε : 0 < √ε := Real.sqrt_pos.2 h.ε0
    have hM : M t i j ^ 2 ≤ G ^ 2 := sq_le_sq' (by linarith [abs_le.1 (h.abs_M_le t i j)])
      (abs_le.1 (h.abs_M_le t i j)).2
    have heq : sqrtWeight ε (V t) i j * precond ε (M t) (V t) i j ^ 2 =
        M t i j ^ 2 / sqrtWeight ε (V t) i j := by
      simp only [precond, sqrtWeight, Matrix.of_apply] at hS ⊢
      field_simp
    rw [heq]
    exact div_le_div₀ (sq_nonneg _) hM hε hS'
  calc wnorm (sqrtWeight ε (V t)) (precond ε (M t) (V t))
      ≤ ∑ _i : p, ∑ _j : q, G ^ 2 / √ε :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = _ := by simp; ring

/-- `‖M_t / S_t‖_F ≤ G∞ √(N / ε)`. -/
lemma norm_precond_le (h : AdamSeq β β₂ ε G g M V) (t : ℕ) :
    ‖precond ε (M t) (V t)‖ ≤ G * √(Fintype.card p * Fintype.card q / ε) := by
  have hN : (0 : ℝ) ≤ Fintype.card p * Fintype.card q / ε := by
    have := h.ε0
    positivity
  have hsq : ‖precond ε (M t) (V t)‖ ^ 2 ≤ (G * √(Fintype.card p * Fintype.card q / ε)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hN, Frobenius.norm_sq_eq_sum]
    have hentry : ∀ i j, precond ε (M t) (V t) i j ^ 2 ≤ G ^ 2 / ε := by
      intro i j
      have hS := h.sqrt_lower t i j
      have hε : 0 < ε := h.ε0
      have hS2 : ε ≤ sqrtWeight ε (V t) i j ^ 2 := by
        have := Real.sq_sqrt hε.le
        nlinarith [Real.sqrt_nonneg ε]
      have hM : M t i j ^ 2 ≤ G ^ 2 := sq_le_sq' (by linarith [abs_le.1 (h.abs_M_le t i j)])
        (abs_le.1 (h.abs_M_le t i j)).2
      have heq : precond ε (M t) (V t) i j ^ 2 = M t i j ^ 2 / sqrtWeight ε (V t) i j ^ 2 := by
        simp only [precond, sqrtWeight, Matrix.of_apply, div_pow]
      rw [heq]
      exact div_le_div₀ (sq_nonneg _) hM hε hS2
    calc ∑ i, ∑ j, precond ε (M t) (V t) i j ^ 2 ≤ ∑ _i : p, ∑ _j : q, G ^ 2 / ε :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
      _ = _ := by simp; ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg h.G0 (Real.sqrt_nonneg _))).1 hsq

end AdamSeq

/-- Weighted telescoping, with the last term kept. -/
private theorem telescope_aux {S d : ℕ → ℝ} {D : ℝ} (hS0 : ∀ t, 1 ≤ t → 0 ≤ S t)
    (hmono : ∀ t, 1 ≤ t → S t ≤ S (t + 1)) (hd : ∀ t, 1 ≤ t → d t ^ 2 ≤ D ^ 2) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 (T + 1), S t * (d t ^ 2 - d (t + 1) ^ 2) * √(t : ℝ) +
        S (T + 1) * d (T + 1 + 1) ^ 2 * √((T + 1 : ℕ) : ℝ) ≤
      D ^ 2 * S (T + 1) * √((T + 1 : ℕ) : ℝ) := by
  induction T with
  | zero =>
    simp only [zero_add, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, Real.sqrt_one,
      mul_one]
    nlinarith [hS0 1 le_rfl, hd 1 le_rfl, mul_le_mul_of_nonneg_left (hd 1 le_rfl) (hS0 1 le_rfl)]
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 : 0 ≤ S (T + 1) := hS0 _ (by omega)
    have h2 : S (T + 1) ≤ S (T + 1 + 1) := hmono _ (by omega)
    have h3 : d (T + 1 + 1) ^ 2 ≤ D ^ 2 := hd _ (by omega)
    have h4 : √((T + 1 : ℕ) : ℝ) ≤ √((T + 1 + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by push_cast; linarith)
    have h5 : 0 ≤ √((T + 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
    have h6 : S (T + 1) * √((T + 1 : ℕ) : ℝ) ≤ S (T + 1 + 1) * √((T + 1 + 1 : ℕ) : ℝ) :=
      mul_le_mul h2 h4 h5 (h1.trans h2)
    have h7 := mul_le_mul_of_nonneg_left h6 (sub_nonneg.2 h3)
    nlinarith

/-- The telescoping step of AMSGrad for one coordinate, under monotone weights. -/
private theorem telescope {S d : ℕ → ℝ} {D Smax : ℝ} (hS0 : ∀ t, 1 ≤ t → 0 ≤ S t)
    (hmono : ∀ t, 1 ≤ t → S t ≤ S (t + 1)) (hmax : ∀ t, 1 ≤ t → S t ≤ Smax)
    (hd : ∀ t, 1 ≤ t → d t ^ 2 ≤ D ^ 2) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, S t * (d t ^ 2 - d (t + 1) ^ 2) * √(t : ℝ) ≤ D ^ 2 * Smax * √(T : ℝ) := by
  cases T with
  | zero => simp
  | succ T =>
    have h := telescope_aux hS0 hmono hd T
    have h1 : 0 ≤ S (T + 1) * d (T + 1 + 1) ^ 2 * √((T + 1 : ℕ) : ℝ) :=
      mul_nonneg (mul_nonneg (hS0 _ (by omega)) (sq_nonneg _)) (Real.sqrt_nonneg _)
    have h2 : D ^ 2 * S (T + 1) * √((T + 1 : ℕ) : ℝ) ≤ D ^ 2 * Smax * √((T + 1 : ℕ) : ℝ) := by
      have := hmax (T + 1) (by omega)
      have : 0 ≤ D ^ 2 := sq_nonneg D
      gcongr
    linarith

/-- `∑_{t ≤ T} 1/√t ≤ 2 √T`. -/
theorem sum_inv_sqrt_le (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, (1 / √(t : ℝ)) ≤ 2 * √(T : ℝ) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 : 0 ≤ √(T : ℝ) := Real.sqrt_nonneg _
    have h2 : 0 < √((T + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have h3 : √((T + 1 : ℕ) : ℝ) ^ 2 = √(T : ℝ) ^ 2 + 1 := by
      rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      push_cast; ring
    have h4 : 1 / √((T + 1 : ℕ) : ℝ) ≤ 2 * √((T + 1 : ℕ) : ℝ) - 2 * √(T : ℝ) := by
      rw [div_le_iff₀ h2]
      nlinarith
    linarith

/-- `∑_{t ≥ 1} bᵗ ≤ b / (1 - b)`, the summability used for (H2). -/
theorem sum_pow_le {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, b ^ t ≤ b / (1 - b) := by
  have h : ∑ t ∈ Finset.Icc 1 T, b ^ t = (b - b ^ (T + 1)) / (1 - b) := by
    have hne : 1 - b ≠ 0 := by linarith
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      field_simp
      ring
  rw [h]
  apply div_le_div_of_nonneg_right _ (by linarith)
  have := pow_nonneg hb0 (T + 1)
  linarith

/-- The regret recursion of one factor (arXiv 2609.21039, App. B, eqs. (B.3)-(B.8)), in the form
that also covers the projected and retracted factor.  From a one-step inequality with defect `ν_t`
and remainder `κ_t`, it bounds `∑ ⟨x_t - x*, g_t⟩`.  The momentum is treated through `g_t - M_t =
β_t (g_t - M_{t-1})`, with `∑ β_t < ∞`, instead of the paper's Young inequality. -/
theorem adam_core {β : ℕ → ℝ} {β₂ ε G : ℝ} {g M V x : ℕ → Matrix p q ℝ}
    (h : AdamSeq β β₂ ε G g M V) {xs : Matrix p q ℝ} {η₀ D : ℝ} (hη₀ : 0 < η₀)
    (hD : 0 ≤ D) (hx : ∀ t, 1 ≤ t → ∀ i j, |x t i j - xs i j| ≤ D) (ν κ : ℕ → ℝ)
    (hstep : ∀ t, 1 ≤ t → wnorm (sqrtWeight ε (V t)) (x (t + 1) - xs) ≤
      wnorm (sqrtWeight ε (V t)) (x t - xs) - 2 * (η₀ / √(t : ℝ)) * ⟪x t - xs, M t⟫ +
        2 * (η₀ / √(t : ℝ)) * ν t + κ t) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, ⟪x t - xs, g t⟫ ≤
      2 * (Fintype.card p * Fintype.card q) * D * G * ∑ t ∈ Finset.Icc 1 T, β t +
      Fintype.card p * Fintype.card q * (D ^ 2 * √(G ^ 2 + ε)) * √(T : ℝ) / (2 * η₀) +
      ∑ t ∈ Finset.Icc 1 T, ν t + ∑ t ∈ Finset.Icc 1 T, κ t * √(t : ℝ) / (2 * η₀) := by
  set N : ℝ := Fintype.card p * Fintype.card q with hN
  -- entrywise bounds
  have hdiff : ∀ t, 1 ≤ t → ⟪x t - xs, g t - M (t - 1)⟫ ≤ N * (D * (2 * G)) := by
    intro t ht
    rw [Frobenius.inner_def]
    calc _ ≤ ∑ _i : p, ∑ _j : q, D * (2 * G) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          simp only [Matrix.sub_apply]
          have h1 := hx t ht i j
          have h2 : |g t i j - M (t - 1) i j| ≤ 2 * G := by
            have h3 := h.g_le t ht i j
            have h4 := h.abs_M_le (t - 1) i j
            calc _ ≤ |g t i j| + |M (t - 1) i j| := abs_sub _ _
              _ ≤ _ := by linarith
          calc _ ≤ |x t i j - xs i j| * |g t i j - M (t - 1) i j| := by
                rw [← abs_mul]; exact le_abs_self _
            _ ≤ _ := by gcongr
      _ = _ := by simp [hN]; ring
  have hgM : ∀ t, 1 ≤ t → ⟪x t - xs, g t⟫ ≤ ⟪x t - xs, M t⟫ + β t * (N * (D * (2 * G))) := by
    intro t ht
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have h1 := hdiff (s + 1) ht
    have hM : M (s + 1) = g (s + 1) - β (s + 1) • (g (s + 1) - M s) := by
      rw [h.Msucc, firstMoment]
      module
    have h2 : ⟪x (s + 1) - xs, M (s + 1)⟫ = ⟪x (s + 1) - xs, g (s + 1)⟫ -
        β (s + 1) * ⟪x (s + 1) - xs, g (s + 1) - M s⟫ := by
      rw [hM, inner_sub_right, inner_smul_right]
    simp only [Nat.add_sub_cancel] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 (h.β0 (s + 1))
    linarith
  -- one step
  have hMbound : ∀ t, 1 ≤ t → ⟪x t - xs, M t⟫ ≤
      (wnorm (sqrtWeight ε (V t)) (x t - xs) - wnorm (sqrtWeight ε (V t)) (x (t + 1) - xs)) *
          √(t : ℝ) / (2 * η₀) + ν t + κ t * √(t : ℝ) / (2 * η₀) := by
    intro t ht
    have hs : 0 < √(t : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast ht)
    have h1 := hstep t ht
    have hc : 0 < √(t : ℝ) / (2 * η₀) := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 hc.le
    have h3 : √(t : ℝ) / (2 * η₀) * (2 * (η₀ / √(t : ℝ))) = 1 := by field_simp
    have h4 : √(t : ℝ) / (2 * η₀) * (wnorm (sqrtWeight ε (V t)) (x t - xs) -
          2 * (η₀ / √(t : ℝ)) * ⟪x t - xs, M t⟫ + 2 * (η₀ / √(t : ℝ)) * ν t + κ t) =
        (wnorm (sqrtWeight ε (V t)) (x t - xs)) * √(t : ℝ) / (2 * η₀) -
          (√(t : ℝ) / (2 * η₀) * (2 * (η₀ / √(t : ℝ)))) * ⟪x t - xs, M t⟫ +
          (√(t : ℝ) / (2 * η₀) * (2 * (η₀ / √(t : ℝ)))) * ν t + κ t * √(t : ℝ) / (2 * η₀) := by
      ring
    rw [h4, h3] at h2
    have h5 : √(t : ℝ) / (2 * η₀) * wnorm (sqrtWeight ε (V t)) (x (t + 1) - xs) =
        wnorm (sqrtWeight ε (V t)) (x (t + 1) - xs) * √(t : ℝ) / (2 * η₀) := by ring
    rw [h5] at h2
    have h6 : (wnorm (sqrtWeight ε (V t)) (x t - xs) -
          wnorm (sqrtWeight ε (V t)) (x (t + 1) - xs)) * √(t : ℝ) / (2 * η₀) =
        wnorm (sqrtWeight ε (V t)) (x t - xs) * √(t : ℝ) / (2 * η₀) -
          wnorm (sqrtWeight ε (V t)) (x (t + 1) - xs) * √(t : ℝ) / (2 * η₀) := by ring
    rw [h6]
    linarith
  -- telescoping
  have htel : ∑ t ∈ Finset.Icc 1 T,
      (wnorm (sqrtWeight ε (V t)) (x t - xs) - wnorm (sqrtWeight ε (V t)) (x (t + 1) - xs)) *
        √(t : ℝ) ≤ N * (D ^ 2 * √(G ^ 2 + ε)) * √(T : ℝ) := by
    have hexp : ∀ t, (wnorm (sqrtWeight ε (V t)) (x t - xs) -
        wnorm (sqrtWeight ε (V t)) (x (t + 1) - xs)) * √(t : ℝ) =
        ∑ i, ∑ j, sqrtWeight ε (V t) i j *
          ((x t i j - xs i j) ^ 2 - (x (t + 1) i j - xs i j) ^ 2) * √(t : ℝ) := by
      intro t
      simp only [wnorm, Matrix.sub_apply, ← Finset.sum_sub_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [hexp]
    rw [Finset.sum_comm]
    calc ∑ i, ∑ t ∈ Finset.Icc 1 T, ∑ j, sqrtWeight ε (V t) i j *
          ((x t i j - xs i j) ^ 2 - (x (t + 1) i j - xs i j) ^ 2) * √(t : ℝ)
        ≤ ∑ _i : p, ∑ _j : q, D ^ 2 * √(G ^ 2 + ε) * √(T : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_le_sum fun j _ => ?_
          refine telescope (S := fun t => sqrtWeight ε (V t) i j)
            (d := fun t => x t i j - xs i j) (fun t _ => (h.sqrt_pos t i j).le)
            (fun t _ => h.sqrt_mono t i j) (fun t _ => h.sqrt_upper t i j) (fun t ht => ?_) T
          have := abs_le.1 (hx t ht i j)
          exact sq_le_sq' (by linarith) this.2
      _ = _ := by simp [hN]; ring
  have hsum : ∑ t ∈ Finset.Icc 1 T, ⟪x t - xs, g t⟫ ≤
      ∑ t ∈ Finset.Icc 1 T, (β t * (N * (D * (2 * G))) +
        (wnorm (sqrtWeight ε (V t)) (x t - xs) - wnorm (sqrtWeight ε (V t)) (x (t + 1) - xs)) *
          √(t : ℝ) / (2 * η₀) + ν t + κ t * √(t : ℝ) / (2 * η₀)) := by
    refine Finset.sum_le_sum fun t ht => ?_
    have ht1 : 1 ≤ t := (Finset.mem_Icc.1 ht).1
    linarith [hgM t ht1, hMbound t ht1]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.sum_div] at hsum
  have hη2 : 0 < 2 * η₀ := by positivity
  have hdiv := div_le_div_of_nonneg_right htel hη2.le
  have heq : 2 * N * D * G * ∑ t ∈ Finset.Icc 1 T, β t =
      (∑ t ∈ Finset.Icc 1 T, β t) * (N * (D * (2 * G))) := by ring
  rw [heq]
  linarith

end AdamSeq

section Algorithm

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

/-- `ξ = -η P_X(Dᵀ)` with `X = Aᵀ`: line 10 of Algorithm 1 of arXiv 2609.21039.  The paper writes
`D` for a matrix of shape `r × n` and projects it at `X ∈ ℝ^{n×r}`; the transpose makes the shapes
agree. -/
noncomputable def stiefelDirection (η : ℝ) (A D : Matrix r n ℝ) : Matrix n r ℝ :=
  -η • stiefelProj Aᵀ Dᵀ

/-- **arXiv 2609.21039, Algorithm 1 (Stiefel-AdamW)**: ambient moments for both factors, AdamW step
on `B`, projected direction and retraction on `A`.  The gradients `GB`, `GA` are parameters, `wd` is
the weight decay `λ`, and `ams` selects the update (H5).  Iterates start at `t = 1` and `M₀ = V₀ =
0`. -/
structure StiefelAdamWRun (Retr : Matrix n r ℝ → Matrix n r ℝ → Matrix n r ℝ)
    (η β₁ : ℕ → ℝ) (β₂ ε wd : ℝ) (ams : Bool)
    (GB : ℕ → Matrix m r ℝ) (GA : ℕ → Matrix r n ℝ)
    (B MB VB : ℕ → Matrix m r ℝ) (A MA VA : ℕ → Matrix r n ℝ) : Prop where
  init : A 1 * (A 1)ᵀ = 1
  MB_zero : MB 0 = 0
  MA_zero : MA 0 = 0
  VB_zero : VB 0 = 0
  VA_zero : VA 0 = 0
  MB_succ : ∀ t, MB (t + 1) = firstMoment (β₁ (t + 1)) (MB t) (GB (t + 1))
  MA_succ : ∀ t, MA (t + 1) = firstMoment (β₁ (t + 1)) (MA t) (GA (t + 1))
  VB_succ : ∀ t, VB (t + 1) =
    if ams then amsMoment β₂ (VB t) (GB (t + 1)) else secondMoment β₂ (VB t) (GB (t + 1))
  VA_succ : ∀ t, VA (t + 1) =
    if ams then amsMoment β₂ (VA t) (GA (t + 1)) else secondMoment β₂ (VA t) (GA (t + 1))
  B_step : ∀ t, 1 ≤ t → B (t + 1) = B t - η t • (precond ε (MB t) (VB t) + wd • B t)
  A_step : ∀ t, 1 ≤ t → A (t + 1) =
    (Retr (A t)ᵀ (stiefelDirection (η t) (A t) (precond ε (MA t) (VA t))))ᵀ

/-- A retraction onto the Stiefel manifold with a second-order remainder on the tangent space, the
only properties of `Retr` used in the regret analysis.  The Cayley retraction is an instance; QR and
polar retractions are not treated in this module. -/
structure IsSecondOrderRetraction (Retr : Matrix n r ℝ → Matrix n r ℝ → Matrix n r ℝ) (c : ℝ) :
    Prop where
  stiefel : ∀ X, Xᵀ * X = 1 → ∀ ξ, (Retr X ξ)ᵀ * Retr X ξ = 1
  second_order : ∀ X ξ, Xᵀ * X = 1 → Xᵀ * ξ + ξᵀ * X = 0 → ‖Retr X ξ - X - ξ‖ ≤ c * ‖ξ‖ ^ 2

/-- arXiv 2609.21039, App. A.2: the Cayley retraction has these properties. -/
theorem isSecondOrderRetraction_cayleyRetr [DecidableEq n] :
    IsSecondOrderRetraction (n := n) (r := r) cayleyRetr (9 / 2 * √(Fintype.card r)) where
  stiefel _ hX ξ := cayleyRetr_stiefel hX ξ
  second_order _ _ hX hξ := norm_cayleyRetr_sub_le hX hξ

section Run

variable {Retr : Matrix n r ℝ → Matrix n r ℝ → Matrix n r ℝ} {η β₁ : ℕ → ℝ} {β₂ ε wd : ℝ}
  {ams : Bool} {GB : ℕ → Matrix m r ℝ} {GA : ℕ → Matrix r n ℝ}
  {B MB VB : ℕ → Matrix m r ℝ} {A MA VA : ℕ → Matrix r n ℝ}

/-- arXiv 2609.21039, §3.1: Algorithm 1 keeps `A_t A_tᵀ = I`. -/
theorem StiefelAdamWRun.rowOrthonormal
    (hrun : StiefelAdamWRun Retr η β₁ β₂ ε wd ams GB GA B MB VB A MA VA)
    (hRetr : ∀ X, Xᵀ * X = 1 → ∀ ξ, (Retr X ξ)ᵀ * Retr X ξ = 1) (t : ℕ) (ht : 1 ≤ t) :
    A t * (A t)ᵀ = 1 := by
  induction t, ht using Nat.le_induction with
  | base => exact hrun.init
  | succ t ht ih =>
    rw [hrun.A_step t ht, Matrix.transpose_transpose]
    exact hRetr _ (by simpa using ih) _

/-- arXiv 2609.21039, Algorithm 1 line 10: `ξ_t` is tangent. -/
theorem stiefelDirection_tangent {A₀ : Matrix r n ℝ} (hA : A₀ * A₀ᵀ = 1) (a : ℝ)
    (D : Matrix r n ℝ) :
    A₀ᵀᵀ * stiefelDirection a A₀ D + (stiefelDirection a A₀ D)ᵀ * A₀ᵀ = 0 := by
  have hX : A₀ᵀᵀ * A₀ᵀ = 1 := by simpa using hA
  have h := stiefelProj_tangent hX Dᵀ
  simp only [stiefelDirection, Matrix.mul_smul, Matrix.transpose_smul, Matrix.smul_mul,
    ← smul_add, h, smul_zero]

/-- arXiv 2609.21039, §3.1: no factor blow-up along the run, `‖B_t A_t‖_F = ‖B_t‖_F` and `‖A_t‖_F =
√r`. -/
theorem StiefelAdamWRun.norm_factors
    (hrun : StiefelAdamWRun Retr η β₁ β₂ ε wd ams GB GA B MB VB A MA VA)
    (hRetr : ∀ X, Xᵀ * X = 1 → ∀ ξ, (Retr X ξ)ᵀ * Retr X ξ = 1) (t : ℕ) (ht : 1 ≤ t) :
    ‖B t * A t‖ = ‖B t‖ ∧ ‖A t‖ = √(Fintype.card r) := by
  have h := hrun.rowOrthonormal hRetr t ht
  refine ⟨norm_mul_eq_of_rowOrthonormal h _, ?_⟩
  rw [← Real.sqrt_sq (norm_nonneg (A t)), norm_sq_of_rowOrthonormal h]

end Run

/-- Entries of a row-orthonormal matrix are at most one in absolute value. -/
lemma abs_entry_le_one {A : Matrix r n ℝ} (hA : A * Aᵀ = 1) (i : r) (j : n) : |A i j| ≤ 1 := by
  have h1 : ∑ l, A i l ^ 2 = 1 := by
    have := congrFun (congrFun hA i) i
    simpa [Matrix.mul_apply, sq] using this
  have h2 : A i j ^ 2 ≤ 1 := by
    rw [← h1]
    exact Finset.single_le_sum (f := fun l => A i l ^ 2) (fun l _ => sq_nonneg _)
      (Finset.mem_univ j)
  exact abs_le_of_sq_le_sq' (by simpa using h2) zero_le_one |> abs_le.2

/-- First-order inequality for a differentiable convex function. -/
private theorem convex_first_order {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} (hf : ConvexOn ℝ univ f) {x y g : E}
    (hg : HasGradientAt f g x) : f x - f y ≤ ⟪g, x - y⟫ := by
  set v := y - x with hv
  have hline : HasDerivAt (fun s : ℝ => f (x + s • v)) ⟪g, v⟫ 0 := by
    have h1 : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    have h2 : HasFDerivAt f (InnerProductSpace.toDual ℝ E g) (x + (0 : ℝ) • v) := by
      simpa using hg.hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have hs : Tendsto (fun s : ℝ => s⁻¹ • (f (x + s • v) - f x)) (𝓝[>] 0) (𝓝 ⟪g, v⟫) := by
    simpa using hline.tendsto_slope_zero_right
  have hbound : ∀ᶠ s in 𝓝[>] (0 : ℝ), s⁻¹ • (f (x + s • v) - f x) ≤ f y - f x := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs
    have hs0 := hs.1
    have hs1 := hs.2
    have h := hf.2 (mem_univ x) (mem_univ y) (sub_nonneg.2 hs1.le) hs0.le (by ring)
    have hx : (1 - s) • x + s • y = x + s • v := by
      rw [hv]; module
    rw [hx] at h
    simp only [smul_eq_mul] at h ⊢
    rw [inv_mul_le_iff₀ hs0]
    linarith
  have h := le_of_tendsto hs hbound
  have h2 : x - y = -v := by rw [hv]; abel
  rw [h2, inner_neg_right]
  linarith

/-- The defect `ν_t = ⟨A_t - A*, D_t - P_t D_t⟩_{S_t}`: how much the normal part of the direction
`D_t = M_t / S_t` points away from the comparator, in the metric `S_t`.  It is the term which the
proof of Theorem 4.2 of arXiv 2609.21039 misses. -/
noncomputable def normalDefect (ε : ℝ) (A As M V : Matrix r n ℝ) : ℝ :=
  winner (sqrtWeight ε V) (A - As) (precond ε M V - rowProj A (precond ε M V))

/-- The constant term of the corrected regret bound. -/
noncomputable def regretC₁ (NB NA Dinf Ginf β₀ b : ℝ) : ℝ :=
  (2 * NB * (2 * Dinf) * Ginf + 2 * NA * 2 * Ginf) * (β₀ * (b / (1 - b)))

/-- The bound `G∞ √(N / ε)` of `‖D_t‖_F`. -/
noncomputable def dirBound (NA Ginf ε : ℝ) : ℝ := Ginf * √(NA / ε)

/-- The coefficient of `√T` in the corrected regret bound. -/
noncomputable def regretC₂ (NB NA R c η₀ Dinf Ginf ε : ℝ) : ℝ :=
  (NB * ((2 * Dinf) ^ 2 * √(Ginf ^ 2 + ε)) + NA * (2 ^ 2 * √(Ginf ^ 2 + ε))) / (2 * η₀) +
    NB * (η₀ * (Ginf ^ 2 / √ε)) +
    2 * η₀ * (√(Ginf ^ 2 + ε) * dirBound NA Ginf ε ^ 2 *
      (4 * R * c + (1 + c * η₀ * dirBound NA Ginf ε) ^ 2) / 2)

/-- Summing a bound of the form `K / √t`. -/
private theorem sum_le_of_le_inv_sqrt {f : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ t, 1 ≤ t → f t ≤ K * (1 / √(t : ℝ))) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, f t ≤ 2 * K * √(T : ℝ) := by
  calc ∑ t ∈ Finset.Icc 1 T, f t ≤ ∑ t ∈ Finset.Icc 1 T, K * (1 / √(t : ℝ)) :=
        Finset.sum_le_sum fun t ht => h t (Finset.mem_Icc.1 ht).1
    _ = K * ∑ t ∈ Finset.Icc 1 T, (1 / √(t : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ K * (2 * √(T : ℝ)) := by gcongr; exact sum_inv_sqrt_le T
    _ = _ := by ring

/-- The regret `R(T) = ∑_{t ≤ T} (L_t(B_t, A_t) - L_t(B*, A*))` of arXiv 2609.21039, App. B. -/
noncomputable def regret (L : ℕ → FactorSpace m n r → ℝ) (B : ℕ → Matrix m r ℝ)
    (A : ℕ → Matrix r n ℝ) (Bs : Matrix m r ℝ) (As : Matrix r n ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, (L t (WithLp.toLp 2 (B t, A t)) - L t (WithLp.toLp 2 (Bs, As)))

/-- The arithmetic of the retraction remainder. -/
private theorem kappa_scalar {a η₀ S D R c : ℝ} (ha0 : 0 < a) (ha : a ≤ η₀) (hS : 0 ≤ S)
    (hD : 0 ≤ D) (hc : 0 ≤ c) :
    2 * (S * ((2 * R) * (c * (a * D) ^ 2))) + S * (a * D + c * (a * D) ^ 2) ^ 2 ≤
      2 * (S * D ^ 2 * (4 * R * c + (1 + c * η₀ * D) ^ 2) / 2) * a ^ 2 := by
  have h7 : (1 + c * a * D) ^ 2 ≤ (1 + c * η₀ * D) ^ 2 := by gcongr
  have h9 : 0 ≤ S * (a * D) ^ 2 := by positivity
  have h10 := mul_le_mul_of_nonneg_left h7 h9
  have e1 : S * (a * D + c * (a * D) ^ 2) ^ 2 = S * (a * D) ^ 2 * (1 + c * a * D) ^ 2 := by ring
  have e2 : 2 * (S * D ^ 2 * (4 * R * c + (1 + c * η₀ * D) ^ 2) / 2) * a ^ 2 =
      2 * (S * ((2 * R) * (c * (a * D) ^ 2))) + S * (a * D) ^ 2 * (1 + c * η₀ * D) ^ 2 := by ring
  rw [e1, e2]
  linarith

/-- One retraction step: the remainder `κ` of the regret recursion is `O(a²)`. -/
private theorem kappa_le {Retr : Matrix n r ℝ → Matrix n r ℝ → Matrix n r ℝ} {c : ℝ}
    (hRetr : IsSecondOrderRetraction Retr c) (hc : 0 ≤ c) {A₀ A₁ As D S : Matrix r n ℝ}
    {a η₀ Smax Dbar : ℝ} (ha0 : 0 < a) (haη : a ≤ η₀) (hSmax : 0 ≤ Smax) (hDbar : 0 ≤ Dbar)
    (hS0 : ∀ i j, 0 ≤ S i j) (hS1 : ∀ i j, S i j ≤ Smax) (hA₀ : A₀ * A₀ᵀ = 1)
    (hAs : As * Asᵀ = 1) (hnext : A₁ = (Retr A₀ᵀ (stiefelDirection a A₀ D))ᵀ)
    (hDn : ‖D‖ ≤ Dbar) :
    2 * winner S (A₀ - As) (A₁ - A₀ + a • rowProj A₀ D) + wnorm S (A₁ - A₀) ≤
      2 * (Smax * Dbar ^ 2 * (4 * √(Fintype.card r) * c + (1 + c * η₀ * Dbar) ^ 2) / 2) *
        a ^ 2 := by
  have hX : A₀ᵀᵀ * A₀ᵀ = 1 := by simpa using hA₀
  have hξt := stiefelDirection_tangent hA₀ a D
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = stiefelDirection a A₀ D := ⟨_, rfl⟩
  rw [← hξ] at hξt hnext
  have hE' := hRetr.second_order _ ξ hX hξt
  have hPn : ‖ξ‖ ≤ a * Dbar := by
    rw [hξ, stiefelDirection, norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos ha0]
    have h1 := (isOrthProj_stiefelProj hX).norm_le Dᵀ
    rw [Frobenius.norm_transpose] at h1
    gcongr
    exact h1.trans hDn
  have hξ2 : ‖ξ‖ ^ 2 ≤ (a * Dbar) ^ 2 := by gcongr
  obtain ⟨E, hEdef⟩ : ∃ E, E = Retr A₀ᵀ ξ - A₀ᵀ - ξ := ⟨_, rfl⟩
  rw [← hEdef] at hE'
  have hEn : ‖E‖ ≤ c * (a * Dbar) ^ 2 := hE'.trans (by gcongr)
  have hrow : a • rowProj A₀ D = -ξᵀ := by
    rw [hξ, stiefelDirection, rowProj_eq, Matrix.transpose_smul, neg_smul, neg_neg]
  have hu1 : A₁ - A₀ + a • rowProj A₀ D = Eᵀ := by
    rw [hrow, hnext, hEdef]
    simp only [Matrix.transpose_sub, Matrix.transpose_transpose]
    abel
  have hu2 : A₁ - A₀ = ξᵀ + Eᵀ := by
    rw [hnext, hEdef]
    simp only [Matrix.transpose_sub, Matrix.transpose_transpose]
    abel
  have hwn : ‖A₁ - A₀‖ ≤ a * Dbar + c * (a * Dbar) ^ 2 := by
    rw [hu2]
    refine (norm_add_le _ _).trans ?_
    rw [Frobenius.norm_transpose, Frobenius.norm_transpose]
    exact add_le_add hPn hEn
  obtain ⟨R, hR⟩ : ∃ R, R = √(Fintype.card r : ℝ) := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; exact Real.sqrt_nonneg _
  have hun : ‖A₀ - As‖ ≤ 2 * R := by
    have h1 : ‖A₀‖ = R := by
      rw [hR, ← norm_sq_of_rowOrthonormal hA₀, Real.sqrt_sq (norm_nonneg _)]
    have h2 : ‖As‖ = R := by
      rw [hR, ← norm_sq_of_rowOrthonormal hAs, Real.sqrt_sq (norm_nonneg _)]
    have := norm_sub_le A₀ As
    linarith
  rw [hu1, ← hR]
  have h1 := winner_le hSmax hS0 hS1 (A₀ - As) Eᵀ
  have h2 := wnorm_le hS1 (A₁ - A₀)
  rw [Frobenius.norm_transpose] at h1
  have h3 : ‖A₀ - As‖ * ‖E‖ ≤ (2 * R) * (c * (a * Dbar) ^ 2) :=
    mul_le_mul hun hEn (norm_nonneg _) (by positivity)
  have h4 : ‖A₁ - A₀‖ ^ 2 ≤ (a * Dbar + c * (a * Dbar) ^ 2) ^ 2 := by gcongr
  have h5 := mul_le_mul_of_nonneg_left h3 hSmax
  have h6 := mul_le_mul_of_nonneg_left h4 hSmax
  have h7 := kappa_scalar (R := R) ha0 haη hSmax hDbar hc
  linarith

/-- The regret of the unconstrained factor `B`. -/
private theorem factor_B_bound {β₁ : ℕ → ℝ} {η₀ β₂ ε Dinf Ginf : ℝ}
    {GB B MB VB : ℕ → Matrix m r ℝ} (hη₀ : 0 < η₀) (hD : 0 ≤ Dinf)
    (hseq : AdamSeq β₁ β₂ ε Ginf GB MB VB) {Bs : Matrix m r ℝ}
    (hstep : ∀ t : ℕ, 1 ≤ t → B (t + 1) = B t - (η₀ / √(t : ℝ)) • precond ε (MB t) (VB t))
    (hx : ∀ t : ℕ, 1 ≤ t → ∀ i j, |B t i j - Bs i j| ≤ 2 * Dinf) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, ⟪B t - Bs, GB t⟫ ≤
      2 * (Fintype.card m * Fintype.card r) * (2 * Dinf) * Ginf * ∑ t ∈ Finset.Icc 1 T, β₁ t +
      Fintype.card m * Fintype.card r * ((2 * Dinf) ^ 2 * √(Ginf ^ 2 + ε)) * √(T : ℝ) / (2 * η₀) +
      2 * (η₀ / 2 * (Fintype.card m * Fintype.card r * (Ginf ^ 2 / √ε))) * √(T : ℝ) := by
  have hε := hseq.ε0
  have hstepB : ∀ t : ℕ, 1 ≤ t → wnorm (sqrtWeight ε (VB t)) (B (t + 1) - Bs) ≤
      wnorm (sqrtWeight ε (VB t)) (B t - Bs) - 2 * (η₀ / √(t : ℝ)) * ⟪B t - Bs, MB t⟫ +
        2 * (η₀ / √(t : ℝ)) * 0 +
        (η₀ / √(t : ℝ)) ^ 2 * wnorm (sqrtWeight ε (VB t)) (precond ε (MB t) (VB t)) := by
    intro t ht
    have h1 : B (t + 1) - Bs = (B t - Bs) + (-(η₀ / √(t : ℝ))) • precond ε (MB t) (VB t) := by
      rw [hstep t ht]
      module
    rw [h1, wnorm_add, winner_smul_right, winner_precond hε (hseq.V_nonneg t), wnorm_smul]
    apply le_of_eq
    ring
  have hB := adam_core hseq hη₀ (by positivity) hx (fun _ => 0)
    (fun t => (η₀ / √(t : ℝ)) ^ 2 * wnorm (sqrtWeight ε (VB t)) (precond ε (MB t) (VB t)))
    hstepB T
  have hκB : ∀ t : ℕ, 1 ≤ t → (η₀ / √(t : ℝ)) ^ 2 * wnorm (sqrtWeight ε (VB t))
      (precond ε (MB t) (VB t)) * √(t : ℝ) / (2 * η₀) ≤
      (η₀ / 2 * (Fintype.card m * Fintype.card r * (Ginf ^ 2 / √ε))) * (1 / √(t : ℝ)) := by
    intro t ht
    have hs : 0 < √(t : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast ht)
    have h1 := hseq.wnorm_precond_le t
    have h2 : (η₀ / √(t : ℝ)) ^ 2 * wnorm (sqrtWeight ε (VB t)) (precond ε (MB t) (VB t)) *
        √(t : ℝ) / (2 * η₀) = (η₀ / 2 * (1 / √(t : ℝ))) *
          wnorm (sqrtWeight ε (VB t)) (precond ε (MB t) (VB t)) := by
      field_simp
    rw [h2]
    calc _ ≤ (η₀ / 2 * (1 / √(t : ℝ))) * (Fintype.card m * Fintype.card r * (Ginf ^ 2 / √ε)) := by
          gcongr
      _ = _ := by ring
  have hκBsum := sum_le_of_le_inv_sqrt (by positivity) hκB T
  simp only [Finset.sum_const_zero, add_zero] at hB
  linarith

/-- The regret of the Stiefel factor `A`, up to the normal defect. -/
private theorem factor_A_bound {Retr : Matrix n r ℝ → Matrix n r ℝ → Matrix n r ℝ} {c : ℝ}
    (hRetr : IsSecondOrderRetraction Retr c) (hc : 0 ≤ c) {β₁ : ℕ → ℝ} {η₀ β₂ ε Ginf : ℝ}
    {GA A MA VA : ℕ → Matrix r n ℝ} (hη₀ : 0 < η₀) (hseq : AdamSeq β₁ β₂ ε Ginf GA MA VA)
    {As : Matrix r n ℝ} (hAorth : ∀ t, 1 ≤ t → A t * (A t)ᵀ = 1) (hAs : As * Asᵀ = 1)
    (hnext : ∀ t : ℕ, 1 ≤ t → A (t + 1) =
      (Retr (A t)ᵀ (stiefelDirection (η₀ / √(t : ℝ)) (A t) (precond ε (MA t) (VA t))))ᵀ)
    (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, ⟪A t - As, GA t⟫ ≤
      2 * (Fintype.card r * Fintype.card n) * 2 * Ginf * ∑ t ∈ Finset.Icc 1 T, β₁ t +
      Fintype.card r * Fintype.card n * (2 ^ 2 * √(Ginf ^ 2 + ε)) * √(T : ℝ) / (2 * η₀) +
      ∑ t ∈ Finset.Icc 1 T, normalDefect ε (A t) As (MA t) (VA t) +
      2 * ((√(Ginf ^ 2 + ε) * dirBound (Fintype.card r * Fintype.card n) Ginf ε ^ 2 *
        (4 * √(Fintype.card r) * c +
          (1 + c * η₀ * dirBound (Fintype.card r * Fintype.card n) Ginf ε) ^ 2) / 2) * η₀) *
        √(T : ℝ) := by
  have hε := hseq.ε0
  have hG := hseq.G0
  have hxA : ∀ t, 1 ≤ t → ∀ i j, |A t i j - As i j| ≤ 2 := fun t ht i j => by
    have := abs_sub (A t i j) (As i j)
    linarith [abs_entry_le_one (hAorth t ht) i j, abs_entry_le_one hAs i j]
  let κ : ℕ → ℝ := fun t =>
    2 * winner (sqrtWeight ε (VA t)) (A t - As)
        (A (t + 1) - A t + (η₀ / √(t : ℝ)) • rowProj (A t) (precond ε (MA t) (VA t))) +
      wnorm (sqrtWeight ε (VA t)) (A (t + 1) - A t)
  have hstepA : ∀ t : ℕ, 1 ≤ t → wnorm (sqrtWeight ε (VA t)) (A (t + 1) - As) ≤
      wnorm (sqrtWeight ε (VA t)) (A t - As) - 2 * (η₀ / √(t : ℝ)) * ⟪A t - As, MA t⟫ +
        2 * (η₀ / √(t : ℝ)) * normalDefect ε (A t) As (MA t) (VA t) + κ t := by
    intro t ht
    have h1 : A (t + 1) - As = (A t - As) + (A (t + 1) - A t) := by abel
    have h2 : winner (sqrtWeight ε (VA t)) (A t - As) (A (t + 1) - A t) =
        -(η₀ / √(t : ℝ)) * winner (sqrtWeight ε (VA t)) (A t - As)
          (rowProj (A t) (precond ε (MA t) (VA t))) +
        winner (sqrtWeight ε (VA t)) (A t - As)
          (A (t + 1) - A t + (η₀ / √(t : ℝ)) • rowProj (A t) (precond ε (MA t) (VA t))) := by
      rw [winner_add_right, winner_smul_right]
      ring
    have h3 : winner (sqrtWeight ε (VA t)) (A t - As) (rowProj (A t) (precond ε (MA t) (VA t))) =
        ⟪A t - As, MA t⟫ - normalDefect ε (A t) As (MA t) (VA t) := by
      rw [normalDefect, winner_sub_right, winner_precond hε (hseq.V_nonneg t)]
      ring
    rw [h1, wnorm_add, h2, h3]
    apply le_of_eq
    simp only [κ]
    ring
  have hA := adam_core hseq hη₀ zero_le_two hxA
    (fun t => normalDefect ε (A t) As (MA t) (VA t)) κ hstepA T
  obtain ⟨Smax, hSmax⟩ : ∃ S, S = √(Ginf ^ 2 + ε) := ⟨_, rfl⟩
  obtain ⟨Dbar, hDbar⟩ : ∃ D, D = dirBound (Fintype.card r * Fintype.card n) Ginf ε := ⟨_, rfl⟩
  rw [← hSmax] at hA
  rw [← hSmax, ← hDbar]
  have hSmax0 : 0 ≤ Smax := by rw [hSmax]; exact Real.sqrt_nonneg _
  have hDbar0 : 0 ≤ Dbar := by rw [hDbar]; exact mul_nonneg hG (Real.sqrt_nonneg _)
  have hR0 : (0 : ℝ) ≤ √(Fintype.card r) := Real.sqrt_nonneg _
  obtain ⟨K, hK⟩ : ∃ K, K = Smax * Dbar ^ 2 *
      (4 * √(Fintype.card r) * c + (1 + c * η₀ * Dbar) ^ 2) / 2 := ⟨_, rfl⟩
  rw [← hK]
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hκA : ∀ t : ℕ, 1 ≤ t → κ t * √(t : ℝ) / (2 * η₀) ≤ (K * η₀) * (1 / √(t : ℝ)) := by
    intro t ht
    have hs1 : 1 ≤ √(t : ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast ht)
    have hs : 0 < √(t : ℝ) := by linarith
    have ha0 : 0 < η₀ / √(t : ℝ) := by positivity
    have haη : η₀ / √(t : ℝ) ≤ η₀ := div_le_self hη₀.le hs1
    have hDn : ‖precond ε (MA t) (VA t)‖ ≤ Dbar := by
      rw [hDbar]
      exact hseq.norm_precond_le t
    have hκ2 : κ t ≤ 2 * K * (η₀ / √(t : ℝ)) ^ 2 := by
      rw [hK]
      exact kappa_le hRetr hc ha0 haη hSmax0 hDbar0 (fun i j => (hseq.sqrt_pos t i j).le)
        (fun i j => hSmax.symm ▸ hseq.sqrt_upper t i j) (hAorth t ht) hAs (hnext t ht) hDn
    calc κ t * √(t : ℝ) / (2 * η₀) ≤ (2 * K * (η₀ / √(t : ℝ)) ^ 2) * √(t : ℝ) / (2 * η₀) := by
          gcongr
      _ = _ := by field_simp
  have hκAsum := sum_le_of_le_inv_sqrt (mul_nonneg hK0 hη₀.le) hκA T
  linarith

/-- **arXiv 2609.21039, Theorem 4.2, corrected: the bound without (H6).**  For the iterates of
Algorithm 1 with (H5), no weight decay and `η_t = η₀/√t`, any retraction with second-order
remainder, convex `L_t`, (H2) in the form `β_{1,t} = β₀ bᵗ`, (H3), (H4) and every comparator `(B*,
A*)` with `A* A*ᵀ = I` and `‖B*‖_max ≤ D∞`, `R(T) ≤ C₁ + C₂ √T + ∑_{t ≤ T} ν_t`, where `ν_t =
normalDefect ...`.  `C₁`, `C₂` are explicit and independent of `T`.  (H6) is not used, strict
convexity and `β₀ < √β₂` are not needed.  The defect cannot be dropped, see `theorem_4_2_false`.
The term comes from the identity `Γ_t⁻¹ D_t = M_t` of the paper's App. B, which fails unless `M_t`
is tangent. -/
theorem regret_le_add_normalDefect
    {Retr : Matrix n r ℝ → Matrix n r ℝ → Matrix n r ℝ} {c : ℝ}
    (hRetr : IsSecondOrderRetraction Retr c) (hc : 0 ≤ c)
    {η β₁ : ℕ → ℝ} {η₀ β₀ b β₂ ε Dinf Ginf : ℝ}
    (hη₀ : 0 < η₀) (hη : ∀ t, η t = η₀ / √(t : ℝ))
    (hβ₀ : 0 ≤ β₀) (hβ₀1 : β₀ ≤ 1) (hb0 : 0 < b) (hb1 : b < 1) (hβ : ∀ t, β₁ t = β₀ * b ^ t)
    (hβ₂0 : 0 ≤ β₂) (hβ₂1 : β₂ ≤ 1) (hε : 0 < ε) (hD : 0 ≤ Dinf) (hG : 0 ≤ Ginf)
    {GB B MB VB : ℕ → Matrix m r ℝ} {GA A MA VA : ℕ → Matrix r n ℝ}
    (hrun : StiefelAdamWRun Retr η β₁ β₂ ε 0 true GB GA B MB VB A MA VA)
    {L : ℕ → FactorSpace m n r → ℝ} (hconv : ∀ t, ConvexOn ℝ univ (L t))
    (hgrad : ∀ t, 1 ≤ t →
      HasGradientAt (L t) (WithLp.toLp 2 (GB t, GA t)) (WithLp.toLp 2 (B t, A t)))
    (H3 : ∀ t, 1 ≤ t → ∀ i j, |B t i j| ≤ Dinf)
    (H4B : ∀ t, 1 ≤ t → ∀ i j, |GB t i j| ≤ Ginf)
    (H4A : ∀ t, 1 ≤ t → ∀ i j, |GA t i j| ≤ Ginf)
    {Bs : Matrix m r ℝ} {As : Matrix r n ℝ} (hBs : ∀ i j, |Bs i j| ≤ Dinf)
    (hAs : As * Asᵀ = 1) (T : ℕ) :
    regret L B A Bs As T ≤
      regretC₁ (Fintype.card m * Fintype.card r) (Fintype.card r * Fintype.card n) Dinf Ginf β₀ b +
      regretC₂ (Fintype.card m * Fintype.card r) (Fintype.card r * Fintype.card n)
        (√(Fintype.card r)) c η₀ Dinf Ginf ε * √(T : ℝ) +
      ∑ t ∈ Finset.Icc 1 T, normalDefect ε (A t) As (MA t) (VA t) := by
  have hβ0 : ∀ t, 0 ≤ β₁ t := fun t => by rw [hβ]; positivity
  have hβ1 : ∀ t, β₁ t ≤ 1 := fun t => by
    rw [hβ]
    calc β₀ * b ^ t ≤ 1 * 1 := by
          gcongr
          exact pow_le_one₀ hb0.le hb1.le
      _ = 1 := one_mul 1
  have hseqB : AdamSeq β₁ β₂ ε Ginf GB MB VB :=
    ⟨hrun.MB_zero, hrun.VB_zero, hrun.MB_succ, by simpa using hrun.VB_succ, hβ0, hβ1, hβ₂0, hβ₂1,
      hε, hG, H4B⟩
  have hseqA : AdamSeq β₁ β₂ ε Ginf GA MA VA :=
    ⟨hrun.MA_zero, hrun.VA_zero, hrun.MA_succ, by simpa using hrun.VA_succ, hβ0, hβ1, hβ₂0, hβ₂1,
      hε, hG, H4A⟩
  have hAorth := hrun.rowOrthonormal hRetr.stiefel
  have hconvex : regret L B A Bs As T ≤
      ∑ t ∈ Finset.Icc 1 T, ⟪B t - Bs, GB t⟫ + ∑ t ∈ Finset.Icc 1 T, ⟪A t - As, GA t⟫ := by
    rw [regret, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun t ht => ?_
    have h := convex_first_order (hconv t) (y := WithLp.toLp 2 (Bs, As))
      (hgrad t (Finset.mem_Icc.1 ht).1)
    refine h.trans (le_of_eq ?_)
    change ⟪GB t, B t - Bs⟫ + ⟪GA t, A t - As⟫ = _
    rw [real_inner_comm, real_inner_comm (A t - As)]
  have hxB : ∀ t : ℕ, 1 ≤ t → ∀ i j, |B t i j - Bs i j| ≤ 2 * Dinf := fun t ht i j => by
    have := abs_sub (B t i j) (Bs i j)
    linarith [H3 t ht i j, hBs i j]
  have hB := factor_B_bound hη₀ hD hseqB (B := B) (fun t ht => by
    rw [hrun.B_step t ht, hη t, zero_smul, add_zero]) hxB T
  have hA := factor_A_bound hRetr hc hη₀ hseqA hAorth hAs (fun t ht => by
    rw [hrun.A_step t ht, hη t]) T
  have hβsum : ∑ t ∈ Finset.Icc 1 T, β₁ t ≤ β₀ * (b / (1 - b)) := by
    simp only [hβ, ← Finset.mul_sum]
    gcongr
    exact sum_pow_le hb0.le hb1 T
  have h1 : 2 * ((Fintype.card m : ℝ) * Fintype.card r) * (2 * Dinf) * Ginf *
      ∑ t ∈ Finset.Icc 1 T, β₁ t ≤
      2 * (Fintype.card m * Fintype.card r) * (2 * Dinf) * Ginf * (β₀ * (b / (1 - b))) := by
    gcongr
  have h2 : 2 * ((Fintype.card r : ℝ) * Fintype.card n) * 2 * Ginf *
      ∑ t ∈ Finset.Icc 1 T, β₁ t ≤
      2 * (Fintype.card r * Fintype.card n) * 2 * Ginf * (β₀ * (b / (1 - b))) := by
    gcongr
  have e : regretC₁ (Fintype.card m * Fintype.card r) (Fintype.card r * Fintype.card n)
        Dinf Ginf β₀ b +
      regretC₂ (Fintype.card m * Fintype.card r) (Fintype.card r * Fintype.card n)
        (√(Fintype.card r)) c η₀ Dinf Ginf ε * √(T : ℝ) +
      ∑ t ∈ Finset.Icc 1 T, normalDefect ε (A t) As (MA t) (VA t) =
      2 * (Fintype.card m * Fintype.card r) * (2 * Dinf) * Ginf * (β₀ * (b / (1 - b))) +
      Fintype.card m * Fintype.card r * ((2 * Dinf) ^ 2 * √(Ginf ^ 2 + ε)) * √(T : ℝ) / (2 * η₀) +
      2 * (η₀ / 2 * (Fintype.card m * Fintype.card r * (Ginf ^ 2 / √ε))) * √(T : ℝ) +
      (2 * (Fintype.card r * Fintype.card n) * 2 * Ginf * (β₀ * (b / (1 - b))) +
      Fintype.card r * Fintype.card n * (2 ^ 2 * √(Ginf ^ 2 + ε)) * √(T : ℝ) / (2 * η₀) +
      ∑ t ∈ Finset.Icc 1 T, normalDefect ε (A t) As (MA t) (VA t) +
      2 * ((√(Ginf ^ 2 + ε) * dirBound (Fintype.card r * Fintype.card n) Ginf ε ^ 2 *
        (4 * √(Fintype.card r) * c +
          (1 + c * η₀ * dirBound (Fintype.card r * Fintype.card n) Ginf ε) ^ 2) / 2) * η₀) *
        √(T : ℝ)) := by
    simp only [regretC₁, regretC₂]
    ring
  rw [e]
  linarith

end Algorithm

section RegretCorollary

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

/-- `(C₁ + C₂ √T) / T → 0`. -/
private theorem tendsto_bound (C₁ C₂ : ℝ) :
    Tendsto (fun T : ℕ => (C₁ + C₂ * √(T : ℝ)) / T) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T : ℕ => C₁ / (T : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C₁
  have h2 : Tendsto (fun T : ℕ => C₂ / √(T : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop C₂
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  obtain ⟨s, hs⟩ : ∃ s, s = √(T : ℝ) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.2 hT'
  have hTs : (T : ℝ) = s ^ 2 := by rw [hs, Real.sq_sqrt hT'.le]
  rw [← hs, hTs]
  field_simp

/-- **arXiv 2609.21039, Theorem 4.2, corrected.**  Under the hypotheses of
`regret_le_add_normalDefect`, with (H6) replaced by the normal alignment `ν_t ≤ 0`, `R(T) ≤ C₁ + C₂
√T` for all `T`.  This is (4.1) with `C₃ = C₄ = C₅ = 0`.  Since regret can be negative, the
conclusion on `R(T)/T` is `limsup ≤ 0`, and `lim = 0` when `R ≥ 0`, for instance when the comparator
minimizes every `L_t` on the manifold. -/
theorem regret_bound_of_normal_alignment
    {Retr : Matrix n r ℝ → Matrix n r ℝ → Matrix n r ℝ} {c : ℝ}
    (hRetr : IsSecondOrderRetraction Retr c) (hc : 0 ≤ c)
    {η β₁ : ℕ → ℝ} {η₀ β₀ b β₂ ε Dinf Ginf : ℝ}
    (hη₀ : 0 < η₀) (hη : ∀ t, η t = η₀ / √(t : ℝ))
    (hβ₀ : 0 ≤ β₀) (hβ₀1 : β₀ ≤ 1) (hb0 : 0 < b) (hb1 : b < 1) (hβ : ∀ t, β₁ t = β₀ * b ^ t)
    (hβ₂0 : 0 ≤ β₂) (hβ₂1 : β₂ ≤ 1) (hε : 0 < ε) (hD : 0 ≤ Dinf) (hG : 0 ≤ Ginf)
    {GB B MB VB : ℕ → Matrix m r ℝ} {GA A MA VA : ℕ → Matrix r n ℝ}
    (hrun : StiefelAdamWRun Retr η β₁ β₂ ε 0 true GB GA B MB VB A MA VA)
    {L : ℕ → FactorSpace m n r → ℝ} (hconv : ∀ t, ConvexOn ℝ univ (L t))
    (hgrad : ∀ t, 1 ≤ t →
      HasGradientAt (L t) (WithLp.toLp 2 (GB t, GA t)) (WithLp.toLp 2 (B t, A t)))
    (H3 : ∀ t, 1 ≤ t → ∀ i j, |B t i j| ≤ Dinf)
    (H4B : ∀ t, 1 ≤ t → ∀ i j, |GB t i j| ≤ Ginf)
    (H4A : ∀ t, 1 ≤ t → ∀ i j, |GA t i j| ≤ Ginf)
    {Bs : Matrix m r ℝ} {As : Matrix r n ℝ} (hBs : ∀ i j, |Bs i j| ≤ Dinf)
    (hAs : As * Asᵀ = 1)
    (H6' : ∀ t, 1 ≤ t → normalDefect ε (A t) As (MA t) (VA t) ≤ 0) :
    (∀ T : ℕ, regret L B A Bs As T ≤
      regretC₁ (Fintype.card m * Fintype.card r) (Fintype.card r * Fintype.card n) Dinf Ginf β₀ b +
      regretC₂ (Fintype.card m * Fintype.card r) (Fintype.card r * Fintype.card n)
        (√(Fintype.card r)) c η₀ Dinf Ginf ε * √(T : ℝ)) ∧
    (∀ δ > 0, ∀ᶠ T : ℕ in atTop, regret L B A Bs As T / T ≤ δ) ∧
    ((∀ T, 0 ≤ regret L B A Bs As T) →
      Tendsto (fun T : ℕ => regret L B A Bs As T / T) atTop (𝓝 0)) := by
  have hbound : ∀ T : ℕ, regret L B A Bs As T ≤
      regretC₁ (Fintype.card m * Fintype.card r) (Fintype.card r * Fintype.card n) Dinf Ginf β₀ b +
      regretC₂ (Fintype.card m * Fintype.card r) (Fintype.card r * Fintype.card n)
        (√(Fintype.card r)) c η₀ Dinf Ginf ε * √(T : ℝ) := fun T => by
    have h := regret_le_add_normalDefect hRetr hc hη₀ hη hβ₀ hβ₀1 hb0 hb1 hβ hβ₂0 hβ₂1 hε hD hG
      hrun hconv hgrad H3 H4B H4A hBs hAs T
    have h2 : ∑ t ∈ Finset.Icc 1 T, normalDefect ε (A t) As (MA t) (VA t) ≤ 0 :=
      Finset.sum_nonpos fun t ht => H6' t (Finset.mem_Icc.1 ht).1
    linarith
  have hratio : ∀ T : ℕ, regret L B A Bs As T / T ≤
      (regretC₁ (Fintype.card m * Fintype.card r) (Fintype.card r * Fintype.card n)
        Dinf Ginf β₀ b + regretC₂ (Fintype.card m * Fintype.card r)
        (Fintype.card r * Fintype.card n) (√(Fintype.card r)) c η₀ Dinf Ginf ε * √(T : ℝ)) / T :=
    fun T => div_le_div_of_nonneg_right (hbound T) (Nat.cast_nonneg T)
  have hlim := tendsto_bound (regretC₁ (Fintype.card m * Fintype.card r)
    (Fintype.card r * Fintype.card n) Dinf Ginf β₀ b) (regretC₂ (Fintype.card m * Fintype.card r)
    (Fintype.card r * Fintype.card n) (√(Fintype.card r)) c η₀ Dinf Ginf ε)
  refine ⟨hbound, fun δ hδ => ?_, fun hnn => ?_⟩
  · filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with T hT
    exact (hratio T).trans hT.le
  · exact squeeze_zero (fun T => div_nonneg (hnn T) (Nat.cast_nonneg T)) hratio hlim

end RegretCorollary

section Counterexample

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

/-- **arXiv 2609.21039, Assumptions 4.1**, for the run of Algorithm 1 with no weight decay: (H1)
strictly convex `L_t` with minimizer `(B*, A*)` over `ℝ^{m×r} × St(n, r)`, (H2), (H3), (H4), (H5)
through `ams = true` in `run`, and (H6) `⟨ξ_t, A* - A_t⟩ ≥ 0`, where `ξ_t` is transposed to match
`A_t`. -/
structure Assumptions41 (Retr : Matrix n r ℝ → Matrix n r ℝ → Matrix n r ℝ) (η β₁ : ℕ → ℝ)
    (β₀ b β₂ ε Dinf Ginf : ℝ) (L : ℕ → FactorSpace m n r → ℝ) (Bs : Matrix m r ℝ)
    (As : Matrix r n ℝ) (GB : ℕ → Matrix m r ℝ) (GA : ℕ → Matrix r n ℝ)
    (B MB VB : ℕ → Matrix m r ℝ) (A MA VA : ℕ → Matrix r n ℝ) : Prop where
  run : StiefelAdamWRun Retr η β₁ β₂ ε 0 true GB GA B MB VB A MA VA
  H1 : ∀ t, StrictConvexOn ℝ univ (L t)
  grad : ∀ t, 1 ≤ t →
    HasGradientAt (L t) (WithLp.toLp 2 (GB t, GA t)) (WithLp.toLp 2 (B t, A t))
  As_mem : As * Asᵀ = 1
  minimizer : ∀ (T : ℕ) (B' : Matrix m r ℝ) (A' : Matrix r n ℝ), A' * A'ᵀ = 1 →
    ∑ t ∈ Finset.Icc 1 T, L t (WithLp.toLp 2 (Bs, As)) ≤
      ∑ t ∈ Finset.Icc 1 T, L t (WithLp.toLp 2 (B', A'))
  H2 : 0 < b ∧ b < 1 ∧ 0 ≤ β₀ ∧ β₀ < √β₂ ∧ ∀ t, β₁ t = β₀ * b ^ t
  H3 : ∀ t, 1 ≤ t → ∀ i j, |B t i j| ≤ Dinf
  H4 : ∀ t, 1 ≤ t → (∀ i j, |GB t i j| ≤ Ginf) ∧ ∀ i j, |GA t i j| ≤ Ginf
  H6 : ∀ t, 1 ≤ t →
    0 ≤ ⟪(stiefelDirection (η t) (A t) (precond ε (MA t) (VA t)))ᵀ, As - A t⟫

/-- On the circle, a direction parallel to a coordinate point has zero tangent projection. -/
lemma stiefelProj_stuck {A D : Matrix (Fin 1) (Fin 2) ℝ} (hA : A * Aᵀ = 1) (hA01 : A 0 1 = 0)
    (hD : D 0 1 = 0) : stiefelProj Aᵀ Dᵀ = 0 := by
  have hX : Aᵀᵀ * Aᵀ = 1 := by simpa using hA
  have h00 : A 0 0 ^ 2 = 1 := by
    have := congrFun (congrFun hA 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hA01, sq] using this
  rw [stiefelProj_eq_zero_iff hX]
  refine ⟨Matrix.of fun _ _ => D 0 0 * A 0 0, ?_, ?_⟩
  · ext i j
    fin_cases i
    fin_cases j
    rfl
  · ext i j
    fin_cases j
    fin_cases i
    · simp only [Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_one, Matrix.of_apply]
      change D 0 0 = A 0 0 * (D 0 0 * A 0 0)
      linear_combination (-D 0 0) * h00
    · simp [Matrix.mul_apply, hA01, hD]

/-- A run of Algorithm 1 that does not move: at `A₀ = (±1, 0)` the projection kills every direction
of the form `(d, 0)`, and such directions are all the moments can produce from a gradient `(g, 0)`.
-/
theorem exists_stuck_run {m : Type*} [Fintype m]
    {Retr : Matrix (Fin 2) (Fin 1) ℝ → Matrix (Fin 2) (Fin 1) ℝ → Matrix (Fin 2) (Fin 1) ℝ}
    (hRetr : ∀ X, Retr X 0 = X) (η β₁ : ℕ → ℝ) (β₂ ε : ℝ)
    {A₀ G₀ : Matrix (Fin 1) (Fin 2) ℝ} (hA : A₀ * A₀ᵀ = 1) (hA01 : A₀ 0 1 = 0)
    (hG : G₀ 0 1 = 0) (B₀ : Matrix m (Fin 1) ℝ) :
    ∃ (MB VB : ℕ → Matrix m (Fin 1) ℝ) (MA VA : ℕ → Matrix (Fin 1) (Fin 2) ℝ),
      StiefelAdamWRun Retr η β₁ β₂ ε 0 true (fun _ => 0) (fun _ => G₀) (fun _ => B₀) MB VB
        (fun _ => A₀) MA VA ∧
      ∀ t, stiefelDirection (η t) A₀ (precond ε (MA t) (VA t)) = 0 := by
  let MA : ℕ → Matrix (Fin 1) (Fin 2) ℝ :=
    fun t => Nat.rec 0 (fun k M => firstMoment (β₁ (k + 1)) M G₀) t
  let VA : ℕ → Matrix (Fin 1) (Fin 2) ℝ := fun t => Nat.rec 0 (fun _ V => amsMoment β₂ V G₀) t
  have hMA : ∀ t, MA t 0 1 = 0 := by
    intro t
    induction t with
    | zero => rfl
    | succ k ih =>
      change firstMoment (β₁ (k + 1)) (MA k) G₀ 0 1 = 0
      simp [firstMoment, ih, hG]
  have hVA : ∀ t, VA t 0 1 = 0 := by
    intro t
    induction t with
    | zero => rfl
    | succ k ih =>
      change amsMoment β₂ (VA k) G₀ 0 1 = 0
      simp [amsMoment, secondMoment, ih, hG]
  have hdir : ∀ t, stiefelDirection (η t) A₀ (precond ε (MA t) (VA t)) = 0 := by
    intro t
    rw [stiefelDirection, stiefelProj_stuck hA hA01 (by simp [precond, hMA]), smul_zero]
  have hzero : precond ε (0 : Matrix m (Fin 1) ℝ) 0 = 0 := by
    ext i j
    simp [precond]
  refine ⟨fun _ => 0, fun _ => 0, MA, VA, ⟨hA, rfl, rfl, rfl, rfl, fun t => ?_, fun t => rfl,
    fun t => ?_, fun t => rfl, fun t _ => ?_, fun t _ => ?_⟩, hdir⟩
  · simp [firstMoment]
  · ext i j
    simp [amsMoment, secondMoment]
  · simp [hzero]
  · have h := hdir t
    change A₀ = (Retr A₀ᵀ (stiefelDirection (η t) A₀ (precond ε (MA t) (VA t))))ᵀ
    rw [h, hRetr, Matrix.transpose_transpose]

/-- `y ↦ ½ ‖y - c‖²` is strictly convex. -/
theorem strictConvexOn_half_norm_sq_sub {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (c : E) :
    StrictConvexOn ℝ univ (fun y : E => (1 / 2 : ℝ) * ‖y - c‖ ^ 2) := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have hb' : b = 1 - a := by linarith
  have h1 : a • x + b • y - c = a • (x - c) + b • (y - c) := by
    rw [hb']; module
  have h2 : 0 < ‖x - y‖ ^ 2 := by
    have : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    positivity
  have h3 : x - y = (x - c) - (y - c) := by abel
  rw [h3, norm_sub_sq_real] at h2
  simp only [smul_eq_mul]
  rw [h1, norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb]
  simp only [conj_trivial]
  have h4 : 0 < a * b := mul_pos ha hb
  have h5 := mul_pos h4 h2
  rw [hb'] at h5 ⊢
  nlinarith

/-- Linear growth is incompatible with the shape of (4.1). -/
private theorem not_bound_of_linear {R : ℕ → ℝ} (hR : ∀ T, R T = 2 * T) :
    ¬ ∃ C₁ C₂ C₃ C₄ C₅ : ℝ, ∀ T : ℕ, 1 ≤ T → R T ≤
      C₁ + C₂ * √(T : ℝ) + C₃ * √(1 + Real.log T) + C₄ * Real.log T +
        C₅ * (T : ℝ) ^ (-(1 / 2) : ℝ) := by
  rintro ⟨C₁, C₂, C₃, C₄, C₅, h⟩
  obtain ⟨K₁, hK₁⟩ : ∃ K, K = |C₁| + |C₃| + |C₅| := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K, K = |C₂| + 2 * |C₃| + 2 * |C₄| := ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  have hbound : ∀ T : ℕ, 1 ≤ T → 2 * (T : ℝ) ≤ K₁ + K₂ * √(T : ℝ) := by
    intro T hT
    have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have hs0 : 0 ≤ √(T : ℝ) := Real.sqrt_nonneg _
    have hs1 : 1 ≤ √(T : ℝ) := Real.one_le_sqrt.2 hT1
    have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
    have hlog : Real.log T ≤ 2 * √(T : ℝ) := by
      have h1 := Real.log_le_sub_one_of_pos (show 0 < √(T : ℝ) by linarith)
      rw [Real.log_sqrt (by linarith)] at h1
      linarith
    have hsq : √(1 + Real.log T) ≤ 1 + 2 * √(T : ℝ) := by
      calc √(1 + Real.log T) ≤ 1 + Real.log T :=
            Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
        _ ≤ _ := by linarith
    have hpow : (T : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hT1 (by norm_num)
    have hpow0 : 0 ≤ (T : ℝ) ^ (-(1 / 2) : ℝ) := by positivity
    have h1 := h T hT
    rw [hR T] at h1
    have e1 : C₂ * √(T : ℝ) ≤ |C₂| * √(T : ℝ) := by gcongr; exact le_abs_self _
    have e2 : C₃ * √(1 + Real.log T) ≤ |C₃| * (1 + 2 * √(T : ℝ)) :=
      mul_le_mul (le_abs_self _) hsq (Real.sqrt_nonneg _) (abs_nonneg _)
    have e3 : C₄ * Real.log T ≤ |C₄| * (2 * √(T : ℝ)) :=
      mul_le_mul (le_abs_self _) hlog hlog0 (abs_nonneg _)
    have e4 : C₅ * (T : ℝ) ^ (-(1 / 2) : ℝ) ≤ |C₅| * 1 :=
      mul_le_mul (le_abs_self _) hpow hpow0 (abs_nonneg _)
    have e5 := le_abs_self C₁
    rw [hK₁, hK₂]
    nlinarith
  obtain ⟨T, hT⟩ := exists_nat_ge ((K₁ + K₂ + 1) ^ 2)
  have hT1 : 1 ≤ T + 1 := by omega
  have h1 := hbound (T + 1) hT1
  have hcast : ((T + 1 : ℕ) : ℝ) = T + 1 := by push_cast; ring
  have hs : K₁ + K₂ + 1 ≤ √((T + 1 : ℕ) : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    rw [hcast]
    linarith
  have hsq : √((T + 1 : ℕ) : ℝ) ^ 2 = ((T + 1 : ℕ) : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  nlinarith [Real.sqrt_nonneg ((T + 1 : ℕ) : ℝ)]

/-- **arXiv 2609.21039, Theorem 4.2 is false.**  For every choice of retraction with `Retr_X(0) = X`
and all parameters allowed by (H2), take `m = r = 1`, `n = 2`, `L_t(B, A) = ½ ‖B‖² + ½ ‖A - e‖²`
with `e = (1, 0)`, and start at `B₁ = 0`, `A₁ = -e`.  All of Assumptions 4.1 hold, `(0, e)` is the
minimizer over the manifold and over the whole Euclidean space, but `-e` is a critical point on the
circle: the projection annihilates the direction, so `ξ_t = 0`, (H6) holds with equality and the
iterates never move.  Hence `R(T) = 2 T`, `R(T)/T` does not tend to `0`, and no constants `C₁, …,
C₅` satisfy (4.1). -/
theorem theorem_4_2_false
    (Retr : Matrix (Fin 2) (Fin 1) ℝ → Matrix (Fin 2) (Fin 1) ℝ → Matrix (Fin 2) (Fin 1) ℝ)
    (hRetr : ∀ X, Retr X 0 = X) {η₀ β₀ b β₂ ε : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < √β₂) :
    ∃ (L : ℕ → FactorSpace (Fin 1) (Fin 2) (Fin 1) → ℝ) (Bs : Matrix (Fin 1) (Fin 1) ℝ)
      (As : Matrix (Fin 1) (Fin 2) ℝ) (GB B MB VB : ℕ → Matrix (Fin 1) (Fin 1) ℝ)
      (GA A MA VA : ℕ → Matrix (Fin 1) (Fin 2) ℝ) (Dinf Ginf : ℝ),
      Assumptions41 Retr (fun t => η₀ / √(t : ℝ)) (fun t => β₀ * b ^ t) β₀ b β₂ ε Dinf Ginf
        L Bs As GB GA B MB VB A MA VA ∧
      (∀ t p, L t (WithLp.toLp 2 (Bs, As)) ≤ L t p) ∧
      (∀ T : ℕ, regret L B A Bs As T = 2 * T) ∧
      ¬ Tendsto (fun T : ℕ => regret L B A Bs As T / T) atTop (𝓝 0) ∧
      ¬ ∃ C₁ C₂ C₃ C₄ C₅ : ℝ, ∀ T : ℕ, 1 ≤ T → regret L B A Bs As T ≤
        C₁ + C₂ * √(T : ℝ) + C₃ * √(1 + Real.log T) + C₄ * Real.log T +
          C₅ * (T : ℝ) ^ (-(1 / 2) : ℝ) := by
  let e : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]
  let A₀ : Matrix (Fin 1) (Fin 2) ℝ := !![-1, 0]
  let G₀ : Matrix (Fin 1) (Fin 2) ℝ := A₀ - e
  let c : FactorSpace (Fin 1) (Fin 2) (Fin 1) := WithLp.toLp 2 (0, e)
  let p₀ : FactorSpace (Fin 1) (Fin 2) (Fin 1) := WithLp.toLp 2 (0, A₀)
  let L : ℕ → FactorSpace (Fin 1) (Fin 2) (Fin 1) → ℝ := fun _ p => (1 / 2 : ℝ) * ‖p - c‖ ^ 2
  have he : e * eᵀ = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [e, Matrix.mul_apply, Fin.sum_univ_two]
  have hA₀ : A₀ * A₀ᵀ = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [A₀, Matrix.mul_apply, Fin.sum_univ_two]
  have hA01 : A₀ 0 1 = 0 := by simp [A₀]
  have hG01 : G₀ 0 1 = 0 := by simp [G₀, A₀, e]
  obtain ⟨MB, VB, MA, VA, hrun, hdir⟩ := exists_stuck_run (m := Fin 1) hRetr
    (fun t => η₀ / √(t : ℝ)) (fun t => β₀ * b ^ t) β₂ ε hA₀ hA01 hG01 0
  have hsub : p₀ - c = WithLp.toLp 2 (0, G₀) := by
    apply (WithLp.ofLp_injective 2)
    refine Prod.ext ?_ ?_
    · simp [p₀, c]
    · simp [p₀, c, G₀]
  have hG2 : ‖G₀‖ ^ 2 = 4 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [G₀, A₀, e, Fin.sum_univ_two]
    norm_num
  have hLp : (1 / 2 : ℝ) * ‖p₀ - c‖ ^ 2 = 2 := by
    rw [hsub, WithLp.prod_norm_sq_eq_of_L2]
    change (1 / 2 : ℝ) * (‖(0 : Matrix (Fin 1) (Fin 1) ℝ)‖ ^ 2 + ‖G₀‖ ^ 2) = 2
    rw [hG2, norm_zero]
    norm_num
  have hreg : ∀ T : ℕ, regret L (fun _ => 0) (fun _ => A₀) 0 e T = 2 * T := by
    intro T
    have hstep : ∀ t, L t (WithLp.toLp 2 (0, A₀)) - L t (WithLp.toLp 2 (0, e)) = 2 := by
      intro t
      change (1 / 2 : ℝ) * ‖p₀ - c‖ ^ 2 - (1 / 2 : ℝ) * ‖c - c‖ ^ 2 = 2
      rw [hLp, sub_self, norm_zero]
      norm_num
    simp [regret, hstep]
    ring
  have hmin : ∀ t p, L t (WithLp.toLp 2 (0, e)) ≤ L t p := fun t p => by
    change (1 / 2 : ℝ) * ‖c - c‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖p - c‖ ^ 2
    rw [sub_self, norm_zero]
    nlinarith [sq_nonneg ‖p - c‖]
  refine ⟨L, 0, e, fun _ => 0, fun _ => 0, MB, VB, fun _ => G₀, fun _ => A₀, MA, VA, 0, 2,
    ⟨hrun, fun _ => strictConvexOn_half_norm_sq_sub c, fun t _ => ?_, he, fun T B' A' _ => ?_,
      ⟨hb0, hb1, hβ₀, hβ, fun _ => rfl⟩, fun t _ i j => by simp,
      fun t _ => ⟨fun i j => by simp, fun i j => ?_⟩, fun t _ => ?_⟩, hmin, hreg, ?_, ?_⟩
  · have h := hasGradientAt_half_norm_sq_sub c p₀
    rw [hsub] at h
    exact h
  · exact Finset.sum_le_sum fun t _ => hmin t _
  · fin_cases i
    fin_cases j <;> norm_num [G₀, A₀, e]
  · have h := hdir t
    simp only [h, Matrix.transpose_zero, inner_zero_left, le_refl]
  · intro hlim
    have hconst : Tendsto (fun T : ℕ => regret L (fun _ => 0) (fun _ => A₀) 0 e T / T) atTop
        (𝓝 2) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with T hT
      have hT' : (T : ℝ) ≠ 0 := by
        have : 1 ≤ T := hT
        positivity
      rw [hreg T]
      field_simp
    have := tendsto_nhds_unique hlim hconst
    norm_num at this
  · exact not_bound_of_linear hreg

end Counterexample

section RankRecovery

variable {n r : Type*} [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]

/-- Plain gradient descent on `L(B, A) = ½ ‖B A - α I‖²` (arXiv 2609.21039, §4.2). -/
structure IsRecoveryGD (η α : ℝ) (B : ℕ → Matrix n r ℝ) (A : ℕ → Matrix r n ℝ) : Prop where
  B_step : ∀ k, B (k + 1) = B k - η • ((B k * A k - α • 1) * (A k)ᵀ)
  A_step : ∀ k, A (k + 1) = A k - η • ((B k)ᵀ * (B k * A k - α • 1))

/-- arXiv 2609.21039, §4.2: the gradient used in `IsRecoveryGD` is the true gradient. -/
theorem hasGradientAt_recovery (α : ℝ) (p : FactorSpace n n r) :
    HasGradientAt (fun q : FactorSpace n n r =>
        (1 / 2 : ℝ) * ‖factorMap q - α • (1 : Matrix n n ℝ)‖ ^ 2)
      (WithLp.toLp 2 ((p.fst * p.snd - α • 1) * p.sndᵀ, p.fstᵀ * (p.fst * p.snd - α • 1))) p :=
  hasGradientAt_comp_factorMap (ℓ := fun X => (1 / 2 : ℝ) * ‖X - α • (1 : Matrix n n ℝ)‖ ^ 2)
    (G := p.fst * p.snd - α • 1) (hasGradientAt_half_norm_sq_sub _ _)

/-- arXiv 2609.21039, §4.2: from `B₀ = 0`, the first step is `B₁ = η α A₀ᵀ`, `A₁ = A₀`. -/
theorem recovery_first_step {η α : ℝ} {B : ℕ → Matrix n r ℝ} {A : ℕ → Matrix r n ℝ}
    (h : IsRecoveryGD η α B A) (hB : B 0 = 0) : B 1 = (η * α) • (A 0)ᵀ ∧ A 1 = A 0 := by
  constructor
  · have := h.B_step 0
    rw [hB] at this
    simp only [zero_add, Matrix.zero_mul, zero_sub, Matrix.neg_mul, Matrix.smul_mul,
      Matrix.one_mul] at this
    rw [this]
    simp [smul_smul]
  · have := h.A_step 0
    rw [hB] at this
    simpa using this

/-- arXiv 2609.21039, §4.2: for `α = 1/η` and `B₀ = 0`, one has `B_k = A_kᵀ` for `k ≥ 1`, and `X_k =
B_k` follows `X_{k+1} = (2 I - η X_k X_kᵀ) X_k`. -/
theorem recovery_aligned {η : ℝ} (hη : η ≠ 0) {B : ℕ → Matrix n r ℝ} {A : ℕ → Matrix r n ℝ}
    (h : IsRecoveryGD η (1 / η) B A) (hB : B 0 = 0) :
    (∀ k, 1 ≤ k → B k = (A k)ᵀ) ∧
      ∀ k, 1 ≤ k → B (k + 1) = ((2 : ℝ) • 1 - η • (B k * (B k)ᵀ)) * B k := by
  have hstep : ∀ k, B k = (A k)ᵀ → B (k + 1) = ((2 : ℝ) • 1 - η • (B k * (B k)ᵀ)) * B k := by
    intro k hk
    have h1 := h.B_step k
    have hA : A k = (B k)ᵀ := by rw [hk, Matrix.transpose_transpose]
    rw [hA, Matrix.transpose_transpose] at h1
    have h2 : (B k * (B k)ᵀ - (1 / η) • 1) * B k = B k * (B k)ᵀ * B k - (1 / η) • B k := by
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
    have h3 : ((2 : ℝ) • 1 - η • (B k * (B k)ᵀ)) * B k =
        (2 : ℝ) • B k - η • (B k * (B k)ᵀ * B k) := by
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [h1, h2, h3, smul_sub, smul_smul, mul_one_div_cancel hη, one_smul, two_smul]
    abel
  have halign : ∀ k, 1 ≤ k → B k = (A k)ᵀ := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      obtain ⟨h1, h2⟩ := recovery_first_step h hB
      rw [h1, h2, mul_one_div_cancel hη, one_smul]
    | succ k _ ih =>
      have hA : A k = (B k)ᵀ := by rw [ih, Matrix.transpose_transpose]
      rw [h.B_step k, h.A_step k, hA]
      simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
        Matrix.transpose_transpose, Matrix.transpose_one]
  exact ⟨halign, fun k hk => hstep k (halign k hk)⟩

variable {q : Type*} [Fintype q]

/-- arXiv 2609.21039, §4.2: the recursion decouples across singular values.  If `V` is a right
singular vector, or block, of `X` with `s = σ²`, it is one of `(2 I - η X Xᵀ) X` with `s (2 - η
s)²`, i.e. `σ ↦ σ |2 - η σ²|`. -/
theorem sigma_recursion {η s : ℝ} {X : Matrix n r ℝ} {V : Matrix r q ℝ}
    (hV : Xᵀ * X * V = s • V) :
    (((2 : ℝ) • 1 - η • (X * Xᵀ)) * X)ᵀ * (((2 : ℝ) • 1 - η • (X * Xᵀ)) * X) * V =
      (s * (2 - η * s) ^ 2) • V := by
  set M : Matrix r r ℝ := (2 : ℝ) • 1 - η • (Xᵀ * X) with hM
  have h1 : ((2 : ℝ) • 1 - η • (X * Xᵀ)) * X = X * M := by
    rw [hM, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  have hMt : Mᵀ = M := by
    simp [hM, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul]
  have h2 : M * V = (2 - η * s) • V := by
    rw [hM, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, hV, smul_smul]
    module
  rw [h1, Matrix.transpose_mul, hMt]
  calc M * Xᵀ * (X * M) * V = M * ((Xᵀ * X) * (M * V)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [h2, Matrix.mul_smul, hV, Matrix.mul_smul, Matrix.mul_smul, h2, smul_smul, smul_smul]
        congr 1
        ring

/-- Squared singular values are bounded by `‖X‖_F²`. -/
theorem eigen_le_norm_sq {s : ℝ} {X : Matrix n r ℝ} {V : Matrix r q ℝ} (hV0 : V ≠ 0)
    (hV : Xᵀ * X * V = s • V) : s ≤ ‖X‖ ^ 2 := by
  have h1 : ‖X * V‖ ^ 2 = s * ‖V‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, Frobenius.inner_mul_left, ← Matrix.mul_assoc, hV,
      inner_smul_right, real_inner_self_eq_norm_sq]
  have h2 : ‖X * V‖ ^ 2 ≤ (‖X‖ * ‖V‖) ^ 2 := by
    gcongr
    exact Frobenius.norm_mul_le _ _
  have h3 : 0 < ‖V‖ ^ 2 := by
    have := norm_pos_iff.2 hV0
    positivity
  rw [h1, mul_pow] at h2
  exact le_of_mul_le_mul_right h2 h3

/-- arXiv 2609.21039, §4.2: if `X₀` has a singular value with `σ² > 3/η`, the recursion `X_{k+1} =
(2 I - η X_k X_kᵀ) X_k` diverges. -/
theorem recovery_diverges {η s₀ : ℝ} (hη : 0 < η) (hs : 3 / η < s₀) {X : ℕ → Matrix n r ℝ}
    {V : Matrix r q ℝ} (hV0 : V ≠ 0) (hV : (X 0)ᵀ * X 0 * V = s₀ • V)
    (hX : ∀ k, X (k + 1) = ((2 : ℝ) • 1 - η • (X k * (X k)ᵀ)) * X k) :
    Tendsto (fun k => ‖X k‖) atTop atTop := by
  have hs1 : 3 < η * s₀ := by
    rw [div_lt_iff₀ hη] at hs
    linarith
  obtain ⟨c, hc⟩ : ∃ c, c = (η * s₀ - 2) ^ 2 := ⟨_, rfl⟩
  have hc1 : 1 < c := by
    rw [hc]
    nlinarith
  have hs0 : 0 < s₀ := by
    have : 0 < 3 / η := by positivity
    linarith
  obtain ⟨S, hS0, hSsucc⟩ : ∃ S : ℕ → ℝ, S 0 = s₀ ∧ ∀ k, S (k + 1) = S k * (2 - η * S k) ^ 2 :=
    ⟨fun k => Nat.rec s₀ (fun _ x => x * (2 - η * x) ^ 2) k, rfl, fun _ => rfl⟩
  have hSV : ∀ k, (X k)ᵀ * X k * V = S k • V := by
    intro k
    induction k with
    | zero => rw [hS0]; exact hV
    | succ k ih =>
      rw [hSsucc, hX]
      exact sigma_recursion ih
  have hSlow : ∀ k, s₀ * c ^ k ≤ S k := by
    intro k
    induction k with
    | zero => simp [hS0]
    | succ k ih =>
      have h1 : s₀ ≤ S k := by
        have : 1 ≤ c ^ k := one_le_pow₀ hc1.le
        nlinarith
      have h2 : c ≤ (2 - η * S k) ^ 2 := by
        rw [hc]
        have h3 : η * s₀ ≤ η * S k := by gcongr
        nlinarith
      rw [hSsucc, pow_succ, ← mul_assoc]
      exact mul_le_mul ih h2 (by linarith) (by linarith [mul_pos hs0 (pow_pos (by linarith) k)])
  have hnorm : ∀ k, s₀ * c ^ k ≤ ‖X k‖ ^ 2 := fun k =>
    (hSlow k).trans (eigen_le_norm_sq hV0 (hSV k))
  have hlim : Tendsto (fun k => s₀ * c ^ k) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hc1).const_mul_atTop hs0
  have hsq : Tendsto (fun k => ‖X k‖ ^ 2) atTop atTop := tendsto_atTop_mono hnorm hlim
  have hsqrt := Real.tendsto_sqrt_atTop.comp hsq
  refine hsqrt.congr fun k => ?_
  simp [Real.sqrt_sq (norm_nonneg (X k))]

/-- arXiv 2609.21039, §4.2: with `A Aᵀ = I` the update on `B` is affine, `B_{k+1} = (1 - η) B_k + η
α Aᵀ`. -/
theorem constrained_affine {η α : ℝ} {B : Matrix n r ℝ} {A : Matrix r n ℝ} (hA : A * Aᵀ = 1) :
    B - η • ((B * A - α • 1) * Aᵀ) = (1 - η) • B + (η * α) • Aᵀ := by
  rw [Matrix.sub_mul, Matrix.mul_assoc, hA, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
  module

/-- arXiv 2609.21039, §4.2: for `0 < η < 2` the constrained iterates are bounded, for every sequence
of row-orthonormal `A_k` and whatever the size of `α` and `B₀`.  The paper gives no bound; the one
here is in the Frobenius norm, whence the factor `√r`. -/
theorem constrained_bounded {η α : ℝ} (hη0 : 0 < η) (hη2 : η < 2) {B : ℕ → Matrix n r ℝ}
    {A : ℕ → Matrix r n ℝ} (hA : ∀ k, A k * (A k)ᵀ = 1)
    (hB : ∀ k, B (k + 1) = B k - η • ((B k * A k - α • 1) * (A k)ᵀ)) (k : ℕ) :
    ‖B k‖ ≤ max ‖B 0‖ (η * |α| * √(Fintype.card r) / (1 - |1 - η|)) := by
  have hq : |1 - η| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hq' : 0 < 1 - |1 - η| := by linarith
  obtain ⟨M, hM⟩ : ∃ M, M = max ‖B 0‖ (η * |α| * √(Fintype.card r) / (1 - |1 - η|)) := ⟨_, rfl⟩
  rw [← hM]
  have hM1 : ‖B 0‖ ≤ M := by rw [hM]; exact le_max_left _ _
  have hM2 : η * |α| * √(Fintype.card r) ≤ (1 - |1 - η|) * M := by
    have : η * |α| * √(Fintype.card r) / (1 - |1 - η|) ≤ M := by rw [hM]; exact le_max_right _ _
    rw [div_le_iff₀ hq'] at this
    linarith
  induction k with
  | zero => exact hM1
  | succ k ih =>
    rw [hB, constrained_affine (hA k)]
    have h1 : ‖(A k)ᵀ‖ = √(Fintype.card r) := by
      rw [Frobenius.norm_transpose, ← norm_sq_of_rowOrthonormal (hA k),
        Real.sqrt_sq (norm_nonneg _)]
    calc ‖(1 - η) • B k + (η * α) • (A k)ᵀ‖ ≤ ‖(1 - η) • B k‖ + ‖(η * α) • (A k)ᵀ‖ :=
          norm_add_le _ _
      _ = |1 - η| * ‖B k‖ + η * |α| * √(Fintype.card r) := by
          rw [norm_smul, norm_smul, h1, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
            abs_of_pos hη0]
      _ ≤ |1 - η| * M + (1 - |1 - η|) * M := by
          gcongr
      _ = M := by ring

/-- arXiv 2609.21039, §4.2: unconstrained gradient descent from `B₀ = 0` with `α = 1/η` diverges as
soon as an iterate has a singular value with `σ² > 3/η`.  Compare `constrained_bounded`. -/
theorem recovery_gd_diverges {η s₀ : ℝ} (hη : 0 < η) (hs : 3 / η < s₀) {B : ℕ → Matrix n r ℝ}
    {A : ℕ → Matrix r n ℝ} (h : IsRecoveryGD η (1 / η) B A) (hB : B 0 = 0) {k : ℕ} (hk : 1 ≤ k)
    {V : Matrix r q ℝ} (hV0 : V ≠ 0) (hV : (B k)ᵀ * B k * V = s₀ • V) :
    Tendsto (fun j => ‖B (k + j)‖) atTop atTop :=
  recovery_diverges (X := fun j => B (k + j)) hη hs hV0 hV
    fun j => (recovery_aligned hη.ne' h hB).2 (k + j) (by omega)

end RankRecovery

section Factorized

/-- Four linear forms in `(B, a₁, a₂)`, for the extension `recoveryExtension`. -/
noncomputable def recoveryCoords :
    FactorSpace (Fin 1) (Fin 2) (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4) where
  toFun p := WithLp.toLp 2 ![p.fst 0 0 - p.snd 0 1, p.snd 0 1, p.snd 0 0, p.snd 0 0]
  map_add' p q := by
    ext i
    fin_cases i
    · simp; ring
    all_goals simp
  map_smul' c p := by
    ext i
    fin_cases i
    · simp; ring
    all_goals simp

/-- The four forms determine the point. -/
lemma recoveryCoords_injective : Function.Injective recoveryCoords := by
  intro p q h
  have h0 : p.fst 0 0 - p.snd 0 1 = q.fst 0 0 - q.snd 0 1 :=
    congrFun (congrArg WithLp.ofLp h) 0
  have h1 : p.snd 0 1 = q.snd 0 1 := congrFun (congrArg WithLp.ofLp h) 1
  have h2 : p.snd 0 0 = q.snd 0 0 := congrFun (congrArg WithLp.ofLp h) 2
  apply WithLp.ofLp_injective 2
  refine Prod.ext ?_ ?_
  · ext i j
    fin_cases i
    fin_cases j
    change p.fst 0 0 = q.fst 0 0
    linarith
  · ext i j
    fin_cases i
    fin_cases j
    · exact h2
    · exact h1

/-- The function `½ ((B - a₂)² + a₂² + a₁² + a₁²) - ½` on `ℝ × ℝ²`. -/
noncomputable def recoveryExtension (p : FactorSpace (Fin 1) (Fin 2) (Fin 1)) : ℝ :=
  (1 / 2 : ℝ) * ‖recoveryCoords p‖ ^ 2 - 1 / 2

/-- `recoveryExtension` is strictly convex, so `(B, A) ↦ ½ ‖B A - e‖²` on `ℝ × St(2, 1)` satisfies
(H1) of arXiv 2609.21039.  That formula itself is not convex on `ℝ × ℝ²`, which is why (H1) only
asks for an extension from the manifold. -/
theorem strictConvexOn_recoveryExtension : StrictConvexOn ℝ univ recoveryExtension := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have h := (strictConvexOn_half_norm_sq_sub (0 : EuclideanSpace ℝ (Fin 4))).2
    (mem_univ (recoveryCoords x)) (mem_univ (recoveryCoords y))
    (recoveryCoords_injective.ne hxy) ha hb hab
  simp only [sub_zero, ← map_smul, ← map_add, smul_eq_mul] at h
  simp only [recoveryExtension, smul_eq_mul]
  linarith

/-- On `ℝ × St(2, 1)` the extension equals `½ ‖B A - e‖²`, with `e = (0, 1)`. -/
theorem recoveryExtension_eq {p : FactorSpace (Fin 1) (Fin 2) (Fin 1)}
    (hA : p.snd * p.sndᵀ = 1) :
    recoveryExtension p = (1 / 2 : ℝ) * ‖factorMap p - !![0, 1]‖ ^ 2 := by
  have h1 : p.snd 0 0 ^ 2 + p.snd 0 1 ^ 2 = 1 := by
    have := congrFun (congrFun hA 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, sq] using this
  have h2 : ‖recoveryCoords p‖ ^ 2 = (p.fst 0 0 - p.snd 0 1) ^ 2 + p.snd 0 1 ^ 2 +
      p.snd 0 0 ^ 2 + p.snd 0 0 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [recoveryCoords, Fin.sum_univ_four]
  have h3 : ‖factorMap p - !![0, 1]‖ ^ 2 =
      (p.fst 0 0 * p.snd 0 0) ^ 2 + (p.fst 0 0 * p.snd 0 1 - 1) ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [factorMap, Matrix.mul_apply, Fin.sum_univ_two]
  rw [recoveryExtension, h2, h3]
  have h4 : (p.fst 0 0 * p.snd 0 0) ^ 2 + (p.fst 0 0 * p.snd 0 1 - 1) ^ 2 =
      p.fst 0 0 ^ 2 * (p.snd 0 0 ^ 2 + p.snd 0 1 ^ 2) - 2 * p.fst 0 0 * p.snd 0 1 + 1 := by ring
  rw [h4, h1]
  nlinarith

/-- **arXiv 2609.21039, Theorem 4.2 also fails for losses of `W = B A`.**  Take `ℓ(W) = ½ ‖W - e‖²`,
`e = (0, 1)`, which satisfies (H1) by `strictConvexOn_recoveryExtension` and `recoveryExtension_eq`.
Algorithm 1 with the gradients of its lines 1-2 from `B = 0`, `A = (1, 0)` sits at a saddle point:
`G^B = G^A = 0`, `ξ_t = 0`, so (H3), (H4), (H6) are trivial, and the regret against `min_W ℓ` is `T
/ 2`. -/
theorem theorem_4_2_false_factorized
    (Retr : Matrix (Fin 2) (Fin 1) ℝ → Matrix (Fin 2) (Fin 1) ℝ → Matrix (Fin 2) (Fin 1) ℝ)
    (hRetr : ∀ X, Retr X 0 = X) (η β₁ : ℕ → ℝ) (β₂ ε : ℝ) :
    ∃ (ℓ : Matrix (Fin 1) (Fin 2) ℝ → ℝ) (Bs : Matrix (Fin 1) (Fin 1) ℝ)
      (As : Matrix (Fin 1) (Fin 2) ℝ) (GW : ℕ → Matrix (Fin 1) (Fin 2) ℝ)
      (GB B MB VB : ℕ → Matrix (Fin 1) (Fin 1) ℝ) (GA A MA VA : ℕ → Matrix (Fin 1) (Fin 2) ℝ),
      StiefelAdamWRun Retr η β₁ β₂ ε 0 true GB GA B MB VB A MA VA ∧
      (∀ t, HasGradientAt ℓ (GW t) (B t * A t) ∧ GB t = GW t * (A t)ᵀ ∧ GA t = (B t)ᵀ * GW t) ∧
      (∀ p : FactorSpace (Fin 1) (Fin 2) (Fin 1), p.snd * p.sndᵀ = 1 →
        recoveryExtension p = ℓ (factorMap p)) ∧
      (∀ t, B t = 0 ∧ GB t = 0 ∧ GA t = 0) ∧
      (∀ t, stiefelDirection (η t) (A t) (precond ε (MA t) (VA t)) = 0) ∧
      As * Asᵀ = 1 ∧ (∀ W, ℓ (Bs * As) ≤ ℓ W) ∧
      ∀ T : ℕ, ∑ t ∈ Finset.Icc 1 T, (ℓ (B t * A t) - ℓ (Bs * As)) = T / 2 := by
  let e : Matrix (Fin 1) (Fin 2) ℝ := !![0, 1]
  let A₀ : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]
  have he : e * eᵀ = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [e, Matrix.mul_apply, Fin.sum_univ_two]
  have hA₀ : A₀ * A₀ᵀ = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [A₀, Matrix.mul_apply, Fin.sum_univ_two]
  have hA01 : A₀ 0 1 = 0 := by simp [A₀]
  obtain ⟨MB, VB, MA, VA, hrun, hdir⟩ := exists_stuck_run (m := Fin 1) hRetr η β₁ β₂ ε hA₀ hA01
    (G₀ := 0) rfl (0 : Matrix (Fin 1) (Fin 1) ℝ)
  have hmul : (1 : Matrix (Fin 1) (Fin 1) ℝ) * e = e := Matrix.one_mul e
  have hzero : (0 : Matrix (Fin 1) (Fin 1) ℝ) * A₀ = 0 := Matrix.zero_mul _
  have hGW : (0 - e) * A₀ᵀ = (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [e, A₀, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨fun W => (1 / 2 : ℝ) * ‖W - e‖ ^ 2, 1, e, fun _ => 0 - e, fun _ => 0, fun _ => 0, MB, VB,
    fun _ => 0, fun _ => A₀, MA, VA, hrun, fun t => ⟨?_, hGW.symm, ?_⟩,
    fun p hp => recoveryExtension_eq hp, fun _ => ⟨rfl, rfl, rfl⟩, hdir, he, fun W => ?_,
    fun T => ?_⟩
  · have h := hasGradientAt_half_norm_sq_sub e (0 : Matrix (Fin 1) (Fin 2) ℝ)
    simpa only [hzero] using h
  · simp
  · change (1 / 2 : ℝ) * ‖(1 : Matrix (Fin 1) (Fin 1) ℝ) * e - e‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖W - e‖ ^ 2
    rw [hmul, sub_self, norm_zero]
    nlinarith [sq_nonneg ‖W - e‖]
  · have hn : ‖e‖ ^ 2 = 1 := by
      rw [Frobenius.norm_sq_eq_sum]
      simp [e, Fin.sum_univ_two]
    have hval : (1 / 2 : ℝ) * ‖(0 : Matrix (Fin 1) (Fin 1) ℝ) * A₀ - e‖ ^ 2 -
        (1 / 2 : ℝ) * ‖(1 : Matrix (Fin 1) (Fin 1) ℝ) * e - e‖ ^ 2 = 1 / 2 := by
      rw [hmul, hzero, sub_self, norm_zero, zero_sub, norm_neg, hn]
      norm_num
    change ∑ _t ∈ Finset.Icc 1 T, ((1 / 2 : ℝ) * ‖(0 : Matrix (Fin 1) (Fin 1) ℝ) * A₀ - e‖ ^ 2 -
        (1 / 2 : ℝ) * ‖(1 : Matrix (Fin 1) (Fin 1) ℝ) * e - e‖ ^ 2) = T / 2
    rw [hval]
    simp
    ring

/-- Non-vacuity of `regret_bound_of_normal_alignment`: the hypotheses hold for a run of Algorithm 1
with the Cayley retraction and nonzero gradients, here at the minimizer `(0, e)` of `½ ‖B‖² + ½ ‖A -
2 e‖²` over the manifold. -/
theorem normal_alignment_nonvacuous {η₀ β₀ b β₂ ε : ℝ} :
    ∃ (L : ℕ → FactorSpace (Fin 1) (Fin 2) (Fin 1) → ℝ)
      (As : Matrix (Fin 1) (Fin 2) ℝ) (GB B MB VB : ℕ → Matrix (Fin 1) (Fin 1) ℝ)
      (GA A MA VA : ℕ → Matrix (Fin 1) (Fin 2) ℝ),
      StiefelAdamWRun cayleyRetr (fun t : ℕ => η₀ / √(t : ℝ)) (fun t => β₀ * b ^ t) β₂ ε 0 true
        GB GA B MB VB A MA VA ∧
      (∀ t, ConvexOn ℝ univ (L t)) ∧
      (∀ t, HasGradientAt (L t) (WithLp.toLp 2 (GB t, GA t)) (WithLp.toLp 2 (B t, A t))) ∧
      (∀ t, GA t ≠ 0) ∧ As * Asᵀ = 1 ∧
      (∀ t, normalDefect ε (A t) As (MA t) (VA t) ≤ 0) := by
  let e : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]
  let G₀ : Matrix (Fin 1) (Fin 2) ℝ := e - (2 : ℝ) • e
  let c : FactorSpace (Fin 1) (Fin 2) (Fin 1) := WithLp.toLp 2 (0, (2 : ℝ) • e)
  let p₀ : FactorSpace (Fin 1) (Fin 2) (Fin 1) := WithLp.toLp 2 (0, e)
  have he : e * eᵀ = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [e, Matrix.mul_apply, Fin.sum_univ_two]
  have hG01 : G₀ 0 1 = 0 := by simp [G₀, e]
  obtain ⟨MB, VB, MA, VA, hrun, -⟩ := exists_stuck_run (m := Fin 1) (cayleyRetr_zero (n := Fin 2)
    (r := Fin 1)) (fun t : ℕ => η₀ / √(t : ℝ)) (fun t => β₀ * b ^ t) β₂ ε he (by simp [e]) hG01 0
  have hsub : p₀ - c = WithLp.toLp 2 (0, G₀) := by
    apply WithLp.ofLp_injective 2
    refine Prod.ext ?_ ?_
    · simp [p₀, c]
    · simp [p₀, c, G₀]
  refine ⟨fun _ p => (1 / 2 : ℝ) * ‖p - c‖ ^ 2, e, fun _ => 0, fun _ => 0, MB, VB, fun _ => G₀,
    fun _ => e, MA, VA, hrun, fun _ => (strictConvexOn_half_norm_sq_sub c).convexOn, fun t => ?_,
    fun t h => ?_, he, fun t => ?_⟩
  · have h := hasGradientAt_half_norm_sq_sub c p₀
    rw [hsub] at h
    exact h
  · have := congrFun (congrFun h 0) 0
    simp [G₀, e] at this
    norm_num at this
  · simp [normalDefect, winner]

end Factorized

end LeanDLRA.Literature.P2609_21039
