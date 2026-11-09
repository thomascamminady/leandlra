import LeanDLRA.Matrix.Curvature

/-!
# Results of arXiv 2308.16720: DLR tensor approximations to parabolic problems

Bachmayr, Eisenmann and Uschmajew, *Dynamical low-rank tensor approximations to
high-dimensional parabolic problems: existence and convergence of spatial discretizations*.

**Prop. 4.2 (tangent projector of a constrained Tucker manifold)** is proved in the core, for
finite tensors: `LeanDLRA.Tensor.tuckerTangentProj_eq_starProjection` in
`LeanDLRA/Tensor/Tucker/Tangent.lean` shows that `P_X = P_X⁰ + ∑ₖ P_Xᵏ` of (4.7)–(4.9) is the
orthogonal projection onto the span of the tangent vectors (4.5) (Thm 4.1(iii) taken as the
description of `T_X ℳ`), with corollaries `isOrthProj_tuckerTangentProj`,
`tuckerTangentProj_eq_self_iff` and `mem_tuckerTangentSpace_iff`. Differences from the paper are
listed there: finite dimensions instead of `ℓ²(ℕ^d)`, an arbitrary orthogonal projector `P_C` in
place of the tangent projector of the core manifold `ℳ_c`, and the co-range bases `W_k` given by
two hypotheses that say that `W_k W_kᵀ` is the projector onto `Vᵏ`.

**Lemma 4.8** is proved here for finite `n` (the paper: `U, V ∈ [ℓ²(ℕ)]^r`): for `U, V` with
orthonormal columns and `Uᵀ V` symmetric positive semidefinite,
(i) `‖U - V‖₂ ≤ √2 ‖U Uᵀ - V Vᵀ‖₂` (`specNorm_sub_le_sqrt_two_mul`, spectral norms) and
(ii) `‖x - y‖ ≤ √2 ‖U x - V y‖` (`norm_sub_le_sqrt_two_mul`, for blocks of columns with the
Frobenius norm; one column is the paper's vector statement). The proof avoids the paper's
diagonalization of `Uᵀ V`: (ii) uses `4 ⟪x, Σ y⟫ ≤ ⟪x + y, Σ (x + y)⟫ ≤ ‖x + y‖²` for
`Σ = Uᵀ V`, and (i) uses `‖Σ w‖² ≤ ⟪w, Σ w⟫` (`norm_sq_mul_le_inner`, Cauchy–Schwarz for the
semi-inner product of `Σ`).

Not formalized (left out, not weakened):
* Thm 2.2, Thm 2.5 and Thm 3.2 (existence, stability and convergence of spatial
  discretizations): Gelfand triples, Bochner spaces and weak compactness, outside the library.
* Thm 4.1 (i)–(ii) (manifold structure in Hilbert space), Lemma 4.4 and Props. 4.5–4.6 (weak
  closure, distance to the boundary of `ℳ`).
* Props. 4.7 and 4.9 (curvature bounds for constrained Tucker manifolds): they combine Prop. 4.2,
  Lemma 4.8, the singular-subspace perturbation bound (4.13) for every matricization, the
  polar-decomposition gauge and Prop. 4.6; the matrix case `d = 2` is in
  `LeanDLRA/Matrix/Curvature.lean` (`koch_lubich_tangent_specNorm`, `koch_lubich_normal`).
* Props. 4.10 and 4.11 (tensor-train curvature bounds; proof in the appendix).
* Sec. 5 (the model problem: Lemmas 5.2–5.6, Prop. 5.4, Thms 5.8–5.10).

Core definitions used: `Curvature.specNorm`, the Frobenius inner product on matrices
(`LeanDLRA.Frobenius`), `Matrix.PosSemidef`; no local definitions.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2308_16720

open LeanDLRA.Curvature

section Lemma48

variable {n r m : Type*} [Fintype n] [Fintype r] [Fintype m] [DecidableEq r]

omit [DecidableEq r] in
/-- The form `z ↦ ⟪z, S z⟫` of a positive semidefinite matrix is nonnegative. -/
lemma inner_mul_nonneg {S : Matrix r r ℝ} (hS : S.PosSemidef) (z : Matrix r m ℝ) :
    0 ≤ ⟪z, S * z⟫ := by
  rw [Frobenius.inner_eq_trace, ← Matrix.mul_assoc]
  have := (hS.conjTranspose_mul_mul_same z).trace_nonneg
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

omit [DecidableEq r] in
/-- A symmetric matrix moves to the other side of the Frobenius inner product. -/
lemma inner_mul_comm {S : Matrix r r ℝ} (hS : S.PosSemidef) (x y : Matrix r m ℝ) :
    ⟪x, S * y⟫ = ⟪y, S * x⟫ := by
  have hT : Sᵀ = S := by
    have := hS.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  rw [Frobenius.inner_mul_left', hT, real_inner_comm]

variable {U V : Matrix n r ℝ}

omit [DecidableEq r] in
/-- `⟪U x, V y⟫ = ⟪x, Uᵀ V y⟫`. -/
lemma inner_mul_mul_eq (x y : Matrix r m ℝ) : ⟪U * x, V * y⟫ = ⟪x, (Uᵀ * V) * y⟫ := by
  rw [Frobenius.inner_mul_left, Matrix.mul_assoc]

/-- `⟪z, Uᵀ V z⟫ ≤ ‖z‖²` for orthonormal `U, V`. -/
lemma inner_transpose_mul_le (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (z : Matrix r m ℝ) :
    ⟪z, (Uᵀ * V) * z⟫ ≤ ‖z‖ ^ 2 := by
  rw [← inner_mul_mul_eq]
  calc ⟪U * z, V * z⟫ ≤ ‖U * z‖ * ‖V * z‖ := real_inner_le_norm _ _
    _ = ‖z‖ ^ 2 := by
      rw [Frobenius.norm_mul_of_orthonormal hU, Frobenius.norm_mul_of_orthonormal hV, sq]

/-- `‖U x - V y‖² = ‖x‖² - 2 ⟪x, Uᵀ V y⟫ + ‖y‖²` for orthonormal `U, V`. -/
lemma norm_mul_sub_mul_sq (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (x y : Matrix r m ℝ) :
    ‖U * x - V * y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, (Uᵀ * V) * y⟫ + ‖y‖ ^ 2 := by
  have e1 : ⟪U * x, U * x⟫ = ‖x‖ ^ 2 := by
    rw [inner_mul_mul_eq, hU, Matrix.one_mul, real_inner_self_eq_norm_sq]
  have e2 : ⟪V * y, V * y⟫ = ‖y‖ ^ 2 := by
    rw [inner_mul_mul_eq, hV, Matrix.one_mul, real_inner_self_eq_norm_sq]
  have e3 : ⟪U * x, V * y⟫ = ⟪x, (Uᵀ * V) * y⟫ := inner_mul_mul_eq x y
  have e4 : ⟪V * y, U * x⟫ = ⟪x, (Uᵀ * V) * y⟫ := by rw [real_inner_comm, e3]
  rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right, e1, e2, e3,
    e4]
  ring

/-- **Lemma 4.8 (ii)** (Bachmayr–Eisenmann–Uschmajew, arXiv 2308.16720): for `U, V` with
orthonormal columns such that `Uᵀ V` is symmetric positive semidefinite,
`‖x - y‖ ≤ √2 ‖U x - V y‖`. Stated for blocks of columns `x, y` with the Frobenius norm and for
finite `n` (the paper: vectors `x, y ∈ ℝ^r` and `U, V ∈ [ℓ²(ℕ)]^r`; `m = Unit` is the vector
case). -/
theorem norm_sub_le_sqrt_two_mul (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hS : (Uᵀ * V).PosSemidef) (x y : Matrix r m ℝ) : ‖x - y‖ ≤ √2 * ‖U * x - V * y‖ := by
  have h1 : 0 ≤ ⟪x - y, (Uᵀ * V) * (x - y)⟫ := inner_mul_nonneg hS _
  have h2 := inner_transpose_mul_le hU hV (x + y)
  have hsym := inner_mul_comm hS y x
  simp only [Matrix.mul_sub, Matrix.mul_add, inner_sub_left, inner_sub_right, inner_add_left,
    inner_add_right] at h1 h2
  have hn := norm_mul_sub_mul_sq hU hV x y
  have hsq : ‖x - y‖ ^ 2 ≤ (√2 * ‖U * x - V * y‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hn, norm_sub_sq_real]
    rw [norm_add_sq_real] at h2
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- `‖S w‖² ≤ ⟪w, S w⟫` for `S = Uᵀ V` positive semidefinite with orthonormal `U, V` (so
`0 ≤ S ≤ 1`). -/
lemma norm_sq_mul_le_inner (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : (Uᵀ * V).PosSemidef)
    (w : Matrix r m ℝ) : ‖(Uᵀ * V) * w‖ ^ 2 ≤ ⟪w, (Uᵀ * V) * w⟫ := by
  set S := Uᵀ * V with hSdef
  set v := S * w with hv
  have hA : 0 ≤ ⟪w, S * w⟫ := inner_mul_nonneg hS w
  have hB : ⟪w, S * v⟫ = ‖v‖ ^ 2 := by
    rw [inner_mul_comm hS, ← real_inner_self_eq_norm_sq]
  have hC : ⟪v, S * v⟫ ≤ ‖v‖ ^ 2 := inner_transpose_mul_le hU hV v
  have hCS : ⟪w, S * v⟫ ^ 2 ≤ ⟪w, S * w⟫ * ⟪v, S * v⟫ := by
    have hq : ∀ t : ℝ, 0 ≤ ⟪v, S * v⟫ * (t * t) + (-2 * ⟪w, S * v⟫) * t + ⟪w, S * w⟫ :=
      fun t => by
        have h := inner_mul_nonneg hS (w - t • v)
        simp only [Matrix.mul_sub, Matrix.mul_smul, inner_sub_left, inner_sub_right,
          real_inner_smul_left, real_inner_smul_right] at h
        rw [inner_mul_comm hS v w] at h
        nlinarith [h]
    have hd := discrim_le_zero hq
    rw [discrim] at hd
    nlinarith [hd]
  rw [hB] at hCS
  rcases eq_or_lt_of_le (sq_nonneg ‖v‖) with h0 | hpos
  · rw [← h0]; exact hA
  · have := mul_le_mul_of_nonneg_left hC hA
    nlinarith [hCS, this, hpos]

/-- **Lemma 4.8 (i)** (arXiv 2308.16720): for `U, V` with orthonormal columns such that `Uᵀ V`
is symmetric positive semidefinite, the spectral norms satisfy
`‖U - V‖₂ ≤ √2 ‖U Uᵀ - V Vᵀ‖₂`. Finite `n` (the paper: `U, V ∈ [ℓ²(ℕ)]^r`). -/
theorem specNorm_sub_le_sqrt_two_mul [DecidableEq n] (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hS : (Uᵀ * V).PosSemidef) : specNorm (U - V) ≤ √2 * specNorm (U * Uᵀ - V * Vᵀ) := by
  refine specNorm_le_of_col (mul_nonneg (Real.sqrt_nonneg 2) (specNorm_nonneg _)) fun w => ?_
  set S := Uᵀ * V with hSdef
  have hT : Vᵀ * U = S := by
    have := hS.1
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
      Matrix.transpose_transpose] at this
    exact this
  have hP : (U * Uᵀ - V * Vᵀ) * (U * w) = U * w - V * (S * w) := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul,
      Matrix.mul_assoc V, ← Matrix.mul_assoc Vᵀ, hT]
  have hPn : ‖U * w - V * (S * w)‖ ≤ specNorm (U * Uᵀ - V * Vᵀ) * ‖w‖ := by
    rw [← hP, ← Frobenius.norm_mul_of_orthonormal hU w]
    exact frob_mul_le _ _
  have h1 : ‖(U - V) * w‖ ^ 2 = 2 * ‖w‖ ^ 2 - 2 * ⟪w, S * w⟫ := by
    rw [Matrix.sub_mul, norm_mul_sub_mul_sq hU hV]
    ring
  have h2 : ‖U * w - V * (S * w)‖ ^ 2 = ‖w‖ ^ 2 - ‖S * w‖ ^ 2 := by
    rw [norm_mul_sub_mul_sq hU hV, inner_mul_comm hS, real_inner_self_eq_norm_sq]
    ring
  have h3 := norm_sq_mul_le_inner hU hV hS w
  have hsq : ‖(U - V) * w‖ ^ 2 ≤ (√2 * specNorm (U * Uᵀ - V * Vᵀ) * ‖w‖) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have h4 := pow_le_pow_left₀ (norm_nonneg _) hPn 2
    rw [mul_pow] at h4
    nlinarith [h1, h2, h3, h4]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2)
    (specNorm_nonneg _)) (norm_nonneg _)) two_ne_zero).1 hsq

end Lemma48

end LeanDLRA.Literature.P2308_16720
