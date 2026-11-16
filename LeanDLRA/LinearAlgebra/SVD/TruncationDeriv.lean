import LeanDLRA.Classical.SVD
import LeanDLRA.Classical.WeylSingular
import LeanDLRA.LinearAlgebra.SVD.MinMax

/-!
# Differentiability of the truncated singular value decomposition under a gap

Let `σ_i(A)` be the singular values of a real matrix `A` (zero-indexed, decreasing), and let
`T_r(A) = truncation A r = A V_r V_rᵀ` be the truncated singular value decomposition, where the
columns of `V_r` are the top `r` right singular vectors (`topRightSingularVectors`). The matrix
`Q(A) = V_r V_rᵀ` is the orthogonal projector onto the span of the eigenvectors of `Aᵀ A` for its
`r` largest eigenvalues. If `σ_r(A) < σ_{r-1}(A)` (a gap after the `r`-th singular value), this
projector does not depend on the choice of the eigenvectors, and `B ↦ T_r(B)` is Fréchet
differentiable at `A`. All norms are Frobenius norms.

## Main results

* `Frobenius.sq_sub_sq_mul_norm_le_norm_sylvester`: coercivity of the Sylvester operator,
  `(α² - β²) ‖Z‖ ≤ ‖B₁ᵀ B₁ Z - Z B₂ᵀ B₂‖` if `α ‖Z‖ ≤ ‖B₁ Z‖`, `‖B₂ Zᵀ‖ ≤ β ‖Z‖`, `0 ≤ β ≤ α`.
* `EckartYoung.singularValues_mul_norm_le_norm_mul`, `EckartYoung.norm_mul_le_singularValues_mul`:
  `σ_{r-1}(A) ‖Z‖ ≤ ‖A Z‖` on the range of `Q(A)` and `‖A Z‖ ≤ σ_r(A) ‖Z‖` on its kernel.
* `norm_sub_le_of_isOrthProjMat`: a Davis–Kahan bound for the difference of two spectral
  projectors of `Aᵀ A` and `Bᵀ B`.
* `EckartYoung.topRightSingularVectors_mul_transpose_eq`,
  `EckartYoung.truncation_eq_mul_of_isOrthProjMat`: under a gap, `Q(A)` is the only orthogonal
  projector with these properties, so `T_r(A) = A P` for every such projector `P`.
* `EckartYoung.hasFDerivAt_truncation`: under the gap, `B ↦ T_r(B)` has a Fréchet derivative `L`
  at `A` with `‖L H‖ ≤ (1 + 4 ‖A‖² / (σ_{r-1}(A)² - σ_r(A)²)) ‖H‖`;
  `EckartYoung.differentiableAt_truncation`, `EckartYoung.continuousAt_truncation`,
  `EckartYoung.norm_fderiv_truncation_apply_le`.
* `EckartYoung.hasDerivWithinAt_truncation`: for a curve `A(t)` with a derivative `A'` within a
  set and a gap at `A(t)`, the curve `T_r(A(t))` has a derivative within the same set (for
  example a right derivative) of norm at most `(1 + 4 ‖A‖² / (σ_{r-1}² - σ_r²)) ‖A'‖`.

## Implementation notes

With `M = Aᵀ A`, `M̃ = Bᵀ B`, `E = M̃ - M`, `P = Q(A)`, `P̃ = Q(B)`, the off-diagonal blocks
`(1 - P) P̃` and `(1 - P̃) P` solve Sylvester equations with right-hand sides `(1 - P) E P̃` and
`(1 - P̃) E P`; coercivity gives the Davis–Kahan bound `‖P̃ - P‖ = O(‖E‖)`. The block
`X = P P̃ (1 - P)` solves `M X - X M = P E (1 - P) + O(‖E‖ ‖P̃ - P‖)` exactly, the diagonal blocks
of `P̃ - P` are `O(‖P̃ - P‖²)`, and the solution `X₀(E)` of `M X₀ - X₀ M = P E (1 - P)` (the
Sylvester operator is invertible on the block `P · (1 - P)` by coercivity) is linear in `E`.
Hence `P̃ - P = X₀(E) + X₀(E)ᵀ + O(‖E‖²)`, and `T_r(B) = B P̃`. No resolvent and no implicit
function theorem is used. The constant `4 ‖A‖²` is that of this proof, not the sharp one.

## References

* [KochLubich2007]
-/

open Matrix Filter Asymptotics
open scoped Topology RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA

open EckartYoung Curvature

/-! ### Coercivity of the Sylvester operator -/

/-- **Coercivity of the Sylvester operator.** If the columns of `Z` lie where `‖B₁ x‖ ≥ α ‖x‖`
(`α ‖Z‖ ≤ ‖B₁ Z‖`) and its rows where `‖B₂ y‖ ≤ β ‖y‖` (`‖B₂ Zᵀ‖ ≤ β ‖Z‖`), with `0 ≤ β ≤ α`,
then `(α² - β²) ‖Z‖ ≤ ‖B₁ᵀ B₁ Z - Z B₂ᵀ B₂‖`. -/
theorem Frobenius.sq_sub_sq_mul_norm_le_norm_sylvester {n k p q : Type*} [Fintype n]
    [Fintype k] [Fintype p] [Fintype q] {B₁ : Matrix p n ℝ} {B₂ : Matrix q k ℝ}
    {Z : Matrix n k ℝ} {α β : ℝ} (hβ : 0 ≤ β) (hβα : β ≤ α) (h₁ : α * ‖Z‖ ≤ ‖B₁ * Z‖)
    (h₂ : ‖B₂ * Zᵀ‖ ≤ β * ‖Z‖) :
    (α ^ 2 - β ^ 2) * ‖Z‖ ≤ ‖B₁ᵀ * B₁ * Z - Z * (B₂ᵀ * B₂)‖ := by
  have hin : ⟪B₁ᵀ * B₁ * Z - Z * (B₂ᵀ * B₂), Z⟫ = ‖B₁ * Z‖ ^ 2 - ‖B₂ * Zᵀ‖ ^ 2 := by
    rw [inner_sub_left, Matrix.mul_assoc, Frobenius.inner_mul_left, transpose_transpose,
      real_inner_self_eq_norm_sq, ← Matrix.mul_assoc, Frobenius.inner_mul_right,
      real_inner_self_eq_norm_sq, ← Frobenius.norm_transpose (Z * B₂ᵀ), transpose_mul,
      transpose_transpose]
  have hZ := norm_nonneg Z
  have hα : 0 ≤ α := hβ.trans hβα
  have h1 : α ^ 2 * ‖Z‖ ^ 2 ≤ ‖B₁ * Z‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hα hZ) h₁ 2
  have h2 : ‖B₂ * Zᵀ‖ ^ 2 ≤ β ^ 2 * ‖Z‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h₂ 2
  have h3 := real_inner_le_norm (B₁ᵀ * B₁ * Z - Z * (B₂ᵀ * B₂)) Z
  rw [hin] at h3
  rcases hZ.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  · refine le_of_mul_le_mul_right ?_ hpos
    nlinarith

/-! ### The projector onto the top right singular vectors -/

section Projector

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- `V_r V_rᵀ` is an orthogonal projector. -/
theorem EckartYoung.isOrthProjMat_topRightSingularVectors (A : Matrix m n ℝ) (r : ℕ) :
    IsOrthProjMat (topRightSingularVectors A r * (topRightSingularVectors A r)ᵀ) :=
  isOrthProjMat_mul_transpose (transpose_mul_topRightSingularVectors A r)

/-- `T_r(A) = A (V_r V_rᵀ)`. -/
theorem EckartYoung.truncation_eq_mul_topRightSingularVectors (A : Matrix m n ℝ) (r : ℕ) :
    truncation A r = A * (topRightSingularVectors A r * (topRightSingularVectors A r)ᵀ) :=
  Matrix.mul_assoc _ _ _

/-- The top right singular vectors are eigenvectors of `Aᵀ A`:
`Aᵀ A V_r = V_r diag(σ_i(A)², i < r)`. -/
theorem EckartYoung.transpose_mul_self_mul_topRightSingularVectors (A : Matrix m n ℝ) (r : ℕ) :
    Aᵀ * A * topRightSingularVectors A r = topRightSingularVectors A r *
      diagonal fun i : {i : Fin (Module.finrank ℝ (EuclideanSpace ℝ n)) // (i : ℕ) < r} =>
        (toEuclideanLin A).singularValues i.1 ^ 2 := by
  ext a j
  have h := congrFun (transpose_mul_self_mulVec_rightSingularVectors A j.1) a
  have h' : (Aᵀ * A * topRightSingularVectors A r) a j =
      ((Aᵀ * A) *ᵥ WithLp.ofLp (rightSingularVectors A j.1)) a := rfl
  rw [h', h, Matrix.mul_diagonal]
  simp [topRightSingularVectors, mul_comm]

/-- `V_r V_rᵀ` commutes with `Aᵀ A`. -/
theorem EckartYoung.transpose_mul_self_mul_comm (A : Matrix m n ℝ) (r : ℕ) :
    Aᵀ * A * (topRightSingularVectors A r * (topRightSingularVectors A r)ᵀ) =
      topRightSingularVectors A r * (topRightSingularVectors A r)ᵀ * (Aᵀ * A) := by
  have e := transpose_mul_self_mul_topRightSingularVectors A r
  have hs : (Aᵀ * A * (topRightSingularVectors A r * (topRightSingularVectors A r)ᵀ))ᵀ =
      Aᵀ * A * (topRightSingularVectors A r * (topRightSingularVectors A r)ᵀ) := by
    rw [← Matrix.mul_assoc, e]
    simp [transpose_mul, Matrix.mul_assoc]
  rw [← hs]
  simp [transpose_mul, Matrix.mul_assoc]

/-- **Lower bound on the range of `V_r V_rᵀ`.** If `V_r V_rᵀ Z = Z`, then
`σ_{r-1}(A) ‖Z‖ ≤ ‖A Z‖`. -/
theorem EckartYoung.singularValues_mul_norm_le_norm_mul {k : Type*} [Fintype k]
    {A : Matrix m n ℝ} {r : ℕ} {Z : Matrix n k ℝ}
    (hZ : topRightSingularVectors A r * (topRightSingularVectors A r)ᵀ * Z = Z) :
    (toEuclideanLin A).singularValues (r - 1) * ‖Z‖ ≤ ‖A * Z‖ := by
  have hV := transpose_mul_topRightSingularVectors A r
  have hZW : Z = topRightSingularVectors A r * ((topRightSingularVectors A r)ᵀ * Z) := by
    rw [← Matrix.mul_assoc, hZ]
  have hW : ‖Z‖ = ‖(topRightSingularVectors A r)ᵀ * Z‖ := by
    conv_lhs => rw [hZW]
    exact Frobenius.norm_mul_of_orthonormal hV _
  have hσ0 := (toEuclideanLin A).singularValues_nonneg (r - 1)
  obtain ⟨W, hWdef⟩ :
      ∃ W : Matrix {i : Fin (Module.finrank ℝ (EuclideanSpace ℝ n)) // (i : ℕ) < r} k ℝ,
        W = (topRightSingularVectors A r)ᵀ * Z := ⟨_, rfl⟩
  rw [← hWdef] at hW hZW
  have hsq : (toEuclideanLin A).singularValues (r - 1) ^ 2 * ‖W‖ ^ 2 ≤ ‖A * Z‖ ^ 2 := by
    have e : ‖A * Z‖ ^ 2 = ∑ i, ∑ c, W i c *
        ((toEuclideanLin A).singularValues i.1 ^ 2 * W i c) := by
      calc ‖A * Z‖ ^ 2 = ⟪Z, Aᵀ * A * Z⟫ := by
            rw [← real_inner_self_eq_norm_sq, Frobenius.inner_mul_left, Matrix.mul_assoc]
        _ = ⟪topRightSingularVectors A r * W,
            Aᵀ * A * topRightSingularVectors A r * W⟫ := by
            rw [Matrix.mul_assoc (Aᵀ * A), ← hZW]
        _ = ⟪topRightSingularVectors A r * W, topRightSingularVectors A r *
            ((diagonal fun i : {i : Fin (Module.finrank ℝ (EuclideanSpace ℝ n)) // (i : ℕ) < r} =>
              (toEuclideanLin A).singularValues i.1 ^ 2) * W)⟫ := by
            rw [transpose_mul_self_mul_topRightSingularVectors, Matrix.mul_assoc]
        _ = _ := by
            rw [Frobenius.inner_mul_mul_of_orthonormal hV, Frobenius.inner_def]
            simp [Matrix.diagonal_mul]
    rw [e, Curvature.frob_sq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have hi : (toEuclideanLin A).singularValues (r - 1) ^ 2 ≤
        (toEuclideanLin A).singularValues i.1 ^ 2 :=
      sq_singularValues_antitone _ (by have := i.2; omega)
    nlinarith [sq_nonneg (W i c)]
  rw [hW]
  exact (pow_le_pow_iff_left₀ (mul_nonneg hσ0 (norm_nonneg _)) (norm_nonneg _)
    two_ne_zero).mp (by rw [mul_pow]; exact hsq)

/-- **Upper bound on the kernel of `V_r V_rᵀ`.** If `V_r V_rᵀ Z = 0`, then
`‖A Z‖ ≤ σ_r(A) ‖Z‖`. -/
theorem EckartYoung.norm_mul_le_singularValues_mul {k : Type*} [Fintype k]
    {A : Matrix m n ℝ} {r : ℕ} {Z : Matrix n k ℝ}
    (hZ : topRightSingularVectors A r * (topRightSingularVectors A r)ᵀ * Z = 0) :
    ‖A * Z‖ ≤ (toEuclideanLin A).singularValues r * ‖Z‖ := by
  have hT : truncation A r * Z = 0 := by
    rw [truncation_eq_mul_topRightSingularVectors, Matrix.mul_assoc, hZ, Matrix.mul_zero]
  have e : A * Z = (A - truncation A r) * Z := by rw [Matrix.sub_mul, hT, sub_zero]
  rw [e]
  exact (frob_mul_le _ _).trans (mul_le_mul_of_nonneg_right (specNorm_sub_truncation_le A r)
    (norm_nonneg _))

end Projector

/-! ### Davis–Kahan bound and uniqueness of the spectral projector -/

section DavisKahan

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- `M (1 - P) = (1 - P) M` if `M P = P M`. -/
private theorem mul_compl_comm {M P : Matrix n n ℝ} (h : M * P = P * M) :
    M * (1 - P) = (1 - P) * M := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, h]

/-- One off-diagonal block of the Davis–Kahan bound:
`(α'² - β²) ‖(1 - P) P'‖ ≤ ‖Bᵀ B - Aᵀ A‖`. -/
private theorem sq_sub_sq_mul_norm_compl_mul_le {A B : Matrix m n ℝ} {P P' : Matrix n n ℝ}
    {β α' : ℝ} (hP : IsOrthProjMat P) (hP' : IsOrthProjMat P')
    (hPc : Aᵀ * A * P = P * (Aᵀ * A)) (hP'c : Bᵀ * B * P' = P' * (Bᵀ * B))
    (hβ : ∀ Z : Matrix n n ℝ, P * Z = 0 → ‖A * Z‖ ≤ β * ‖Z‖)
    (hα' : ∀ Z : Matrix n n ℝ, P' * Z = Z → α' * ‖Z‖ ≤ ‖B * Z‖) (hβ0 : 0 ≤ β)
    (hβα' : β ≤ α') :
    (α' ^ 2 - β ^ 2) * ‖(1 - P) * P'‖ ≤ ‖Bᵀ * B - Aᵀ * A‖ := by
  have hYt : ((1 - P) * P')ᵀ = P' * (1 - P) := by
    rw [transpose_mul, hP'.symm, hP.compl.symm]
  have h1 : α' * ‖((1 - P) * P')ᵀ‖ ≤ ‖B * ((1 - P) * P')ᵀ‖ :=
    hα' _ (by rw [hYt, ← Matrix.mul_assoc, hP'.idem])
  have h2 : ‖A * ((1 - P) * P')ᵀᵀ‖ ≤ β * ‖((1 - P) * P')ᵀ‖ := by
    rw [transpose_transpose, Frobenius.norm_transpose]
    exact hβ _ (by rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hP.idem, sub_self,
      Matrix.zero_mul])
  have h := Frobenius.sq_sub_sq_mul_norm_le_norm_sylvester hβ0 hβα' h1 h2
  have hc := mul_compl_comm hPc
  have heq : Bᵀ * B * ((1 - P) * P')ᵀ - ((1 - P) * P')ᵀ * (Aᵀ * A) =
      P' * ((Bᵀ * B - Aᵀ * A) * (1 - P)) := by
    rw [hYt, ← Matrix.mul_assoc, hP'c, Matrix.mul_assoc P' (1 - P), ← hc]
    noncomm_ring
  rw [heq, Frobenius.norm_transpose] at h
  refine h.trans ((hP'.norm_mul_le _).trans ?_)
  exact hP.compl.norm_mul_le' _

omit [DecidableEq n] in
/-- **Davis–Kahan bound** for spectral projectors of `Aᵀ A` and `Bᵀ B`. Let `P`, `P'` be
orthogonal projectors that commute with `Aᵀ A` and `Bᵀ B`, with `α ‖Z‖ ≤ ‖A Z‖` on the range and
`‖A Z‖ ≤ β ‖Z‖` on the kernel of `P`, and `α' ‖Z‖ ≤ ‖B Z‖`, `‖B Z‖ ≤ β' ‖Z‖` for `P'`. If
`0 ≤ β < α'` and `0 ≤ β' < α`, then
`‖P' - P‖ ≤ ‖Bᵀ B - Aᵀ A‖ (1 / (α'² - β²) + 1 / (α² - β'²))`. -/
theorem norm_sub_le_of_isOrthProjMat {A B : Matrix m n ℝ} {P P' : Matrix n n ℝ}
    {α β α' β' : ℝ} (hP : IsOrthProjMat P) (hP' : IsOrthProjMat P')
    (hPc : Aᵀ * A * P = P * (Aᵀ * A)) (hP'c : Bᵀ * B * P' = P' * (Bᵀ * B))
    (hα : ∀ Z : Matrix n n ℝ, P * Z = Z → α * ‖Z‖ ≤ ‖A * Z‖)
    (hβ : ∀ Z : Matrix n n ℝ, P * Z = 0 → ‖A * Z‖ ≤ β * ‖Z‖)
    (hα' : ∀ Z : Matrix n n ℝ, P' * Z = Z → α' * ‖Z‖ ≤ ‖B * Z‖)
    (hβ' : ∀ Z : Matrix n n ℝ, P' * Z = 0 → ‖B * Z‖ ≤ β' * ‖Z‖) (hβ0 : 0 ≤ β) (hβ'0 : 0 ≤ β')
    (hβα' : β < α') (hβ'α : β' < α) :
    ‖P' - P‖ ≤ ‖Bᵀ * B - Aᵀ * A‖ * (1 / (α' ^ 2 - β ^ 2) + 1 / (α ^ 2 - β' ^ 2)) := by
  classical
  have h1 := sq_sub_sq_mul_norm_compl_mul_le hP hP' hPc hP'c hβ hα' hβ0 hβα'.le
  have h2 := sq_sub_sq_mul_norm_compl_mul_le hP' hP hP'c hPc hβ' hα hβ'0 hβ'α.le
  rw [norm_sub_rev] at h2
  have g1 : 0 < α' ^ 2 - β ^ 2 := by nlinarith
  have g2 : 0 < α ^ 2 - β' ^ 2 := by nlinarith
  have hsplit : P' - P = (1 - P) * P' - ((1 - P') * P)ᵀ := by
    rw [transpose_mul, hP.symm, hP'.compl.symm]
    noncomm_ring
  have e1 : ‖(1 - P) * P'‖ ≤ ‖Bᵀ * B - Aᵀ * A‖ * (1 / (α' ^ 2 - β ^ 2)) := by
    rw [mul_one_div, le_div_iff₀ g1]
    linarith
  have e2 : ‖(1 - P') * P‖ ≤ ‖Bᵀ * B - Aᵀ * A‖ * (1 / (α ^ 2 - β' ^ 2)) := by
    rw [mul_one_div, le_div_iff₀ g2]
    linarith
  rw [hsplit, mul_add]
  refine (norm_sub_le _ _).trans ?_
  rw [Frobenius.norm_transpose]
  exact add_le_add e1 e2

/-- **The spectral projector is unique under a gap.** Let `P` be an orthogonal projector that
commutes with `Aᵀ A`, with `α ‖Z‖ ≤ ‖A Z‖` on its range and `‖A Z‖ ≤ β ‖Z‖` on its kernel,
where `0 ≤ β < σ_{r-1}(A)` and `σ_r(A) < α`. Then `P = V_r V_rᵀ`: the projector of the
truncated SVD does not depend on the choice of the singular vectors. -/
theorem EckartYoung.topRightSingularVectors_mul_transpose_eq {A : Matrix m n ℝ} {r : ℕ}
    {P : Matrix n n ℝ} {α β : ℝ} (hP : IsOrthProjMat P) (hPc : Aᵀ * A * P = P * (Aᵀ * A))
    (hα : ∀ Z : Matrix n n ℝ, P * Z = Z → α * ‖Z‖ ≤ ‖A * Z‖)
    (hβ : ∀ Z : Matrix n n ℝ, P * Z = 0 → ‖A * Z‖ ≤ β * ‖Z‖) (hβ0 : 0 ≤ β)
    (hβσ : β < (toEuclideanLin A).singularValues (r - 1))
    (hσα : (toEuclideanLin A).singularValues r < α) :
    topRightSingularVectors A r * (topRightSingularVectors A r)ᵀ = P := by
  have h := norm_sub_le_of_isOrthProjMat hP (isOrthProjMat_topRightSingularVectors A r) hPc
    (transpose_mul_self_mul_comm A r) hα hβ (fun Z hZ => singularValues_mul_norm_le_norm_mul hZ)
    (fun Z hZ => norm_mul_le_singularValues_mul hZ) hβ0
    ((toEuclideanLin A).singularValues_nonneg r) hβσ hσα
  rw [sub_self, norm_zero, zero_mul] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

/-- **The truncated SVD under a gap**: for every orthogonal projector `P` as in
`EckartYoung.topRightSingularVectors_mul_transpose_eq`, `T_r(A) = A P`. -/
theorem EckartYoung.truncation_eq_mul_of_isOrthProjMat {A : Matrix m n ℝ} {r : ℕ}
    {P : Matrix n n ℝ} {α β : ℝ} (hP : IsOrthProjMat P) (hPc : Aᵀ * A * P = P * (Aᵀ * A))
    (hα : ∀ Z : Matrix n n ℝ, P * Z = Z → α * ‖Z‖ ≤ ‖A * Z‖)
    (hβ : ∀ Z : Matrix n n ℝ, P * Z = 0 → ‖A * Z‖ ≤ β * ‖Z‖) (hβ0 : 0 ≤ β)
    (hβσ : β < (toEuclideanLin A).singularValues (r - 1))
    (hσα : (toEuclideanLin A).singularValues r < α) :
    truncation A r = A * P := by
  rw [truncation_eq_mul_topRightSingularVectors,
    topRightSingularVectors_mul_transpose_eq hP hPc hα hβ hβ0 hβσ hσα]

end DavisKahan

/-! ### The Sylvester equation on the block `P · (1 - P)` -/

section Sylvester

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- `P (P X (1 - P)) (1 - P) = P X (1 - P)` for an orthogonal projector `P`. -/
private theorem block_block {P : Matrix n n ℝ} (hP : IsOrthProjMat P) (X : Matrix n n ℝ) :
    P * (P * X * (1 - P)) * (1 - P) = P * X * (1 - P) := by
  rw [show P * (P * X * (1 - P)) * (1 - P) = P * P * X * ((1 - P) * (1 - P)) by noncomm_ring,
    hP.idem, hP.compl.idem]

/-- Coercivity of the Sylvester operator `Z ↦ Aᵀ A Z - Z Aᵀ A` on the block `P · (1 - P)`. -/
private theorem sq_sub_sq_mul_norm_le_of_block {A : Matrix m n ℝ} {P Z : Matrix n n ℝ}
    {α β : ℝ} (hP : IsOrthProjMat P) (hα : ∀ Z : Matrix n n ℝ, P * Z = Z → α * ‖Z‖ ≤ ‖A * Z‖)
    (hβ : ∀ Z : Matrix n n ℝ, P * Z = 0 → ‖A * Z‖ ≤ β * ‖Z‖) (hβ0 : 0 ≤ β) (hβα : β ≤ α)
    (hZ : P * Z * (1 - P) = Z) :
    (α ^ 2 - β ^ 2) * ‖Z‖ ≤ ‖Aᵀ * A * Z - Z * (Aᵀ * A)‖ := by
  have h1 : P * Z = Z := by
    calc P * Z = P * (P * Z * (1 - P)) := by rw [hZ]
      _ = P * P * Z * (1 - P) := by noncomm_ring
      _ = Z := by rw [hP.idem, hZ]
  have hZP : Z * P = 0 := by
    calc Z * P = P * Z * (1 - P) * P := by rw [hZ]
      _ = P * Z * (P - P * P) := by noncomm_ring
      _ = 0 := by rw [hP.idem, sub_self, Matrix.mul_zero]
  have h2 : P * Zᵀ = 0 := by
    rw [← hP.symm, ← transpose_mul, hZP, transpose_zero]
  exact Frobenius.sq_sub_sq_mul_norm_le_norm_sylvester hβ0 hβα (hα Z h1)
    ((hβ Zᵀ h2).trans_eq (by rw [Frobenius.norm_transpose]))

/-- **Solvability of the Sylvester equation.** Under a gap `β < α`, there is a linear map
`E ↦ X₀(E)` with `X₀(E) = P X₀(E) (1 - P)` and `Aᵀ A X₀(E) - X₀(E) Aᵀ A = P E (1 - P)`. -/
private theorem exists_linearMap_sylvester {A : Matrix m n ℝ} {P : Matrix n n ℝ} {α β : ℝ}
    (hP : IsOrthProjMat P) (hPc : Aᵀ * A * P = P * (Aᵀ * A))
    (hα : ∀ Z : Matrix n n ℝ, P * Z = Z → α * ‖Z‖ ≤ ‖A * Z‖)
    (hβ : ∀ Z : Matrix n n ℝ, P * Z = 0 → ‖A * Z‖ ≤ β * ‖Z‖) (hβ0 : 0 ≤ β) (hβα : β < α) :
    ∃ X₀ : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ, ∀ E : Matrix n n ℝ,
      P * X₀ E * (1 - P) = X₀ E ∧ Aᵀ * A * X₀ E - X₀ E * (Aᵀ * A) = P * E * (1 - P) := by
  have hc := mul_compl_comm hPc
  have hcomm : ∀ Z : Matrix n n ℝ, P * Z * (1 - P) = Z →
      P * (Aᵀ * A * Z - Z * (Aᵀ * A)) * (1 - P) = Aᵀ * A * Z - Z * (Aᵀ * A) := by
    intro Z hZ
    calc P * (Aᵀ * A * Z - Z * (Aᵀ * A)) * (1 - P) =
        P * (Aᵀ * A) * Z * (1 - P) - P * Z * (Aᵀ * A * (1 - P)) := by noncomm_ring
      _ = Aᵀ * A * (P * Z * (1 - P)) - P * Z * (1 - P) * (Aᵀ * A) := by
        rw [← hPc, hc]
        noncomm_ring
      _ = _ := by rw [hZ]
  let S : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ :=
    (LinearMap.mulLeft ℝ P ∘ₗ LinearMap.mulRight ℝ (1 - P)) ∘ₗ
        (LinearMap.mulLeft ℝ (Aᵀ * A) - LinearMap.mulRight ℝ (Aᵀ * A)) +
      (LinearMap.id - LinearMap.mulLeft ℝ P ∘ₗ LinearMap.mulRight ℝ (1 - P))
  have hS : ∀ Z, S Z = P * (Aᵀ * A * Z - Z * (Aᵀ * A)) * (1 - P) + (Z - P * Z * (1 - P)) := by
    intro Z
    simp [S, Matrix.mul_assoc]
  have hPS : ∀ Z, P * S Z * (1 - P) = P * (Aᵀ * A * Z - Z * (Aᵀ * A)) * (1 - P) := by
    intro Z
    rw [hS, show P * (P * (Aᵀ * A * Z - Z * (Aᵀ * A)) * (1 - P) + (Z - P * Z * (1 - P))) *
        (1 - P) = P * (P * (Aᵀ * A * Z - Z * (Aᵀ * A)) * (1 - P)) * (1 - P) +
          (P * Z * (1 - P) - P * (P * Z * (1 - P)) * (1 - P)) by noncomm_ring,
      block_block hP, block_block hP, sub_self, add_zero]
  have hrest : ∀ Z, S Z - P * S Z * (1 - P) = Z - P * Z * (1 - P) := by
    intro Z
    rw [hPS, hS]
    abel
  have hinj : Function.Injective S := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Z hZ0
    have h2 : Z - P * Z * (1 - P) = 0 := by
      rw [← hrest, hZ0]
      simp
    have hblk : P * Z * (1 - P) = Z := (sub_eq_zero.1 h2).symm
    have h1 : Aᵀ * A * Z - Z * (Aᵀ * A) = 0 := by
      rw [← hcomm Z hblk, ← hPS, hZ0]
      simp
    have h := sq_sub_sq_mul_norm_le_of_block hP hα hβ hβ0 hβα.le hblk
    rw [h1, norm_zero] at h
    have hg : 0 < α ^ 2 - β ^ 2 := by nlinarith
    exact norm_le_zero_iff.1 (by nlinarith [norm_nonneg Z])
  let e := LinearEquiv.ofInjectiveEndo S hinj
  refine ⟨e.symm.toLinearMap ∘ₗ (LinearMap.mulLeft ℝ P ∘ₗ LinearMap.mulRight ℝ (1 - P)),
    fun E => ?_⟩
  have hval : (e.symm.toLinearMap ∘ₗ (LinearMap.mulLeft ℝ P ∘ₗ LinearMap.mulRight ℝ (1 - P))) E =
      e.symm (P * E * (1 - P)) := by
    simp [Matrix.mul_assoc]
  rw [hval]
  have hSX : S (e.symm (P * E * (1 - P))) = P * E * (1 - P) := e.apply_symm_apply _
  have hblk : P * e.symm (P * E * (1 - P)) * (1 - P) = e.symm (P * E * (1 - P)) := by
    have h := hrest (e.symm (P * E * (1 - P)))
    rw [hSX, block_block hP, sub_self] at h
    exact (sub_eq_zero.1 h.symm).symm
  refine ⟨hblk, ?_⟩
  rw [← hcomm _ hblk, ← hPS, hSX, block_block hP]

omit [DecidableEq n] in
/-- The diagonal block of the difference of two orthogonal projectors is of second order:
`‖P (Q - P) P‖ ≤ ‖Q - P‖²`. -/
private theorem norm_mul_sub_mul_le {P Q : Matrix n n ℝ} (hP : IsOrthProjMat P)
    (hQ : IsOrthProjMat Q) : ‖P * (Q - P) * P‖ ≤ ‖Q - P‖ ^ 2 := by
  classical
  have key : ∀ P Q : Matrix n n ℝ, P * (Q - P) * P + P * ((Q - P) * (Q - P)) * P =
      P * (Q * Q - Q) * P - P * Q * (P * P - P) - (P * P - P) * Q * P + (P * P - P) * P +
        (P * P - P) * (P * P - P) := by
    intros
    noncomm_ring
  have h := key P Q
  simp only [hQ.idem, hP.idem, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero] at h
  rw [eq_neg_of_add_eq_zero_left h, norm_neg, sq]
  exact (hP.norm_mul_le' _).trans ((hP.norm_mul_le _).trans (frobenius_norm_mul _ _))

/-- **Second-order expansion of the spectral projector.** If `X₀ = P X₀ (1 - P)` solves
`Aᵀ A X₀ - X₀ Aᵀ A = P (Bᵀ B - Aᵀ A) (1 - P)`, then
`‖P' - P - (X₀ + X₀ᵀ)‖ ≤ 2 ‖P' - P‖² + 4 ‖P' - P‖ ‖Bᵀ B - Aᵀ A‖ / (α² - β²)`. -/
private theorem norm_sub_sub_add_transpose_le {A B : Matrix m n ℝ} {P P' X₀ : Matrix n n ℝ}
    {α β : ℝ} (hP : IsOrthProjMat P) (hP' : IsOrthProjMat P')
    (hPc : Aᵀ * A * P = P * (Aᵀ * A)) (hP'c : Bᵀ * B * P' = P' * (Bᵀ * B))
    (hα : ∀ Z : Matrix n n ℝ, P * Z = Z → α * ‖Z‖ ≤ ‖A * Z‖)
    (hβ : ∀ Z : Matrix n n ℝ, P * Z = 0 → ‖A * Z‖ ≤ β * ‖Z‖) (hβ0 : 0 ≤ β) (hβα : β < α)
    (hX₀ : P * X₀ * (1 - P) = X₀)
    (hX₀M : Aᵀ * A * X₀ - X₀ * (Aᵀ * A) = P * (Bᵀ * B - Aᵀ * A) * (1 - P)) :
    ‖P' - P - (X₀ + X₀ᵀ)‖ ≤
      2 * ‖P' - P‖ ^ 2 + 4 * ‖P' - P‖ * ‖Bᵀ * B - Aᵀ * A‖ / (α ^ 2 - β ^ 2) := by
  have hg : 0 < α ^ 2 - β ^ 2 := by nlinarith
  have hid : ∀ P Q M E : Matrix n n ℝ, M * (P * Q * (1 - P)) - P * Q * (1 - P) * M -
      (P * E * (1 - P) + P * (Q - P) * E * (1 - P) - P * E * (Q - P) * (1 - P)) =
      P * ((M + E) * Q - Q * (M + E)) * (1 - P) + (M * P - P * M) * Q * (1 - P) -
        P * Q * (M * P - P * M) + (P * P - P) * E * (1 - P) + P * E * (P * P - P) := by
    intros
    noncomm_ring
  have h := hid P P' (Aᵀ * A) (Bᵀ * B - Aᵀ * A)
  simp only [add_sub_cancel, hP'c, hPc, hP.idem, sub_self, Matrix.mul_zero, Matrix.zero_mul,
    add_zero] at h
  have h' := sub_eq_zero.1 h
  have hZb : P * (P * P' * (1 - P) - X₀) * (1 - P) = P * P' * (1 - P) - X₀ := by
    rw [show P * (P * P' * (1 - P) - X₀) * (1 - P) =
        P * (P * P' * (1 - P)) * (1 - P) - P * X₀ * (1 - P) by noncomm_ring, block_block hP, hX₀]
  have hZM : Aᵀ * A * (P * P' * (1 - P) - X₀) - (P * P' * (1 - P) - X₀) * (Aᵀ * A) =
      P * (P' - P) * (Bᵀ * B - Aᵀ * A) * (1 - P) -
        P * (Bᵀ * B - Aᵀ * A) * (P' - P) * (1 - P) := by
    calc _ = (Aᵀ * A * (P * P' * (1 - P)) - P * P' * (1 - P) * (Aᵀ * A)) -
          (Aᵀ * A * X₀ - X₀ * (Aᵀ * A)) := by noncomm_ring
      _ = _ := by
        rw [h', hX₀M]
        abel
  have hZ := sq_sub_sq_mul_norm_le_of_block hP hα hβ hβ0 hβα.le hZb
  rw [hZM] at hZ
  set D := P' - P with hD
  set E := Bᵀ * B - Aᵀ * A with hE
  set Z := P * P' * (1 - P) - X₀ with hZdef
  have hDE : ‖P * D * E * (1 - P) - P * E * D * (1 - P)‖ ≤ 2 * ‖D‖ * ‖E‖ := by
    refine (norm_sub_le _ _).trans ?_
    have e1 : ‖P * D * E * (1 - P)‖ ≤ ‖D‖ * ‖E‖ :=
      (hP.compl.norm_mul_le' _).trans ((frobenius_norm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (hP.norm_mul_le _) (norm_nonneg _)))
    have e2 : ‖P * E * D * (1 - P)‖ ≤ ‖D‖ * ‖E‖ := by
      refine (hP.compl.norm_mul_le' _).trans ((frobenius_norm_mul _ _).trans ?_)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hP.norm_mul_le _) (norm_nonneg _)
    linarith
  have hZn : ‖Z‖ ≤ 2 * ‖D‖ * ‖E‖ / (α ^ 2 - β ^ 2) := by
    rw [le_div_iff₀ hg]
    linarith
  have hZt : Zᵀ = (1 - P) * P' * P - X₀ᵀ := by
    rw [hZdef, transpose_sub, transpose_mul, transpose_mul, hP.symm, hP'.symm, hP.compl.symm,
      Matrix.mul_assoc]
  have hdec : P' - P - (X₀ + X₀ᵀ) = P * D * P + (1 - P) * D * (1 - P) + Z + Zᵀ := by
    rw [hZt, hD, hZdef]
    have key : ∀ P Q X Y : Matrix n n ℝ, Q - P - (X + Y) = P * (Q - P) * P +
        (1 - P) * (Q - P) * (1 - P) + (P * Q * (1 - P) - X) + ((1 - P) * Q * P - Y) +
          (P * P - P) * P + (P * P - P) * P := by
      intros
      noncomm_ring
    rw [key P P' X₀ X₀ᵀ, hP.idem, sub_self, Matrix.zero_mul, add_zero, add_zero]
  have hd1 : ‖P * D * P‖ ≤ ‖D‖ ^ 2 := norm_mul_sub_mul_le hP hP'
  have hd2 : ‖(1 - P) * D * (1 - P)‖ ≤ ‖D‖ ^ 2 := by
    have e : (1 - P) * D * (1 - P) = -((1 - P) * ((1 - P') - (1 - P)) * (1 - P)) := by
      rw [hD]
      noncomm_ring
    rw [e, norm_neg]
    refine (norm_mul_sub_mul_le hP.compl hP'.compl).trans_eq ?_
    rw [show (1 - P') - (1 - P) = -(P' - P) by noncomm_ring, norm_neg]
  rw [hdec]
  calc ‖P * D * P + (1 - P) * D * (1 - P) + Z + Zᵀ‖ ≤
      ‖P * D * P‖ + ‖(1 - P) * D * (1 - P)‖ + ‖Z‖ + ‖Zᵀ‖ :=
        (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ ‖D‖ ^ 2 + ‖D‖ ^ 2 + 2 * ‖D‖ * ‖E‖ / (α ^ 2 - β ^ 2) +
        2 * ‖D‖ * ‖E‖ / (α ^ 2 - β ^ 2) := by
      rw [Frobenius.norm_transpose]
      gcongr
    _ = _ := by ring

end Sylvester

/-! ### The Fréchet derivative of the truncated SVD -/

section Derivative

/-- The gaps of a perturbation: if `|α' - α| ≤ h` and `|β' - β| ≤ h` with
`h ≤ (α² - β²) / (4 (α + β + 1))`, then `α'² - β²` and `α² - β'²` are at least `(α² - β²) / 2`. -/
private theorem half_le_sq_sub_sq {α β α' β' h : ℝ} (hβ0 : 0 ≤ β) (hβα : β < α)
    (hβ' : 0 ≤ β') (hh0 : 0 ≤ h) (hh : h ≤ (α ^ 2 - β ^ 2) / (4 * (α + β + 1)))
    (h1 : |α' - α| ≤ h) (h2 : |β' - β| ≤ h) :
    (α ^ 2 - β ^ 2) / 2 ≤ α' ^ 2 - β ^ 2 ∧ (α ^ 2 - β ^ 2) / 2 ≤ α ^ 2 - β' ^ 2 := by
  have hpos : 0 < 4 * (α + β + 1) := by linarith
  have hh' : h * (4 * (α + β + 1)) ≤ α ^ 2 - β ^ 2 := (le_div_iff₀ hpos).1 hh
  have hα'l : α - h ≤ α' := by linarith [(abs_le.1 h1).1]
  have hβ'u : β' ≤ β + h := by linarith [(abs_le.1 h2).2]
  have hhα : h ≤ α := by
    by_contra hlt
    have := mul_lt_mul_of_pos_right (not_le.1 hlt) hpos
    nlinarith
  constructor
  · have : (α - h) ^ 2 ≤ α' ^ 2 := pow_le_pow_left₀ (by linarith) hα'l 2
    nlinarith [mul_nonneg hh0 hβ0]
  · have : β' ^ 2 ≤ (β + h) ^ 2 := pow_le_pow_left₀ hβ' hβ'u 2
    nlinarith [mul_le_mul_of_nonneg_left hhα hh0, mul_nonneg hh0 hβ0]

/-- The quadratic remainder bound of `EckartYoung.hasFDerivAt_truncation`. -/
private theorem quadratic_remainder_le {a c d e h g : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hh : 0 ≤ h) (hg : 0 < g) (hde : d ≤ 4 * e / g)
    (heh : e ≤ c * h) :
    a * (2 * d ^ 2 + 4 * d * e / g + 2 * h ^ 2 / g) + h * d ≤
      (a * (2 * (4 * c / g) ^ 2 + 4 * (4 * c / g) * c / g + 2 / g) + 4 * c / g) * h ^ 2 := by
  have hD0 : 0 ≤ 4 * c / g := div_nonneg (by linarith) hg.le
  have hd' : d ≤ 4 * c / g * h := by
    refine hde.trans ?_
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hg]
    nlinarith
  have h1 : d ^ 2 ≤ (4 * c / g * h) ^ 2 := pow_le_pow_left₀ hd hd' 2
  have h2 : d * e ≤ 4 * c / g * h * (c * h) := mul_le_mul hd' heh he (mul_nonneg hD0 hh)
  have h3 : 4 * d * e / g ≤ 4 * (4 * c / g * h) * (c * h) / g := by
    rw [div_le_div_iff_of_pos_right hg]
    nlinarith
  have h4 : h * d ≤ h * (4 * c / g * h) := mul_le_mul_of_nonneg_left hd' hh
  calc a * (2 * d ^ 2 + 4 * d * e / g + 2 * h ^ 2 / g) + h * d ≤
      a * (2 * (4 * c / g * h) ^ 2 + 4 * (4 * c / g * h) * (c * h) / g + 2 * h ^ 2 / g) +
        h * (4 * c / g * h) :=
        add_le_add (mul_le_mul_of_nonneg_left (by linarith) ha) h4
    _ = _ := by ring

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Fréchet derivative of the truncated SVD under a gap.** If `σ_r(A) < σ_{r-1}(A)`, the map
`B ↦ T_r(B) = truncation B r` has a Fréchet derivative `L` at `A` with
`‖L H‖ ≤ (1 + 4 ‖A‖² / (σ_{r-1}(A)² - σ_r(A)²)) ‖H‖`. Explicitly,
`L H = H Q + A (X₀ + X₀ᵀ)`, where `Q = V_r V_rᵀ` and `X₀ = Q X₀ (1 - Q)` solves the Sylvester
equation `Aᵀ A X₀ - X₀ Aᵀ A = Q (Hᵀ A + Aᵀ H) (1 - Q)`. -/
theorem EckartYoung.hasFDerivAt_truncation {A : Matrix m n ℝ} {r : ℕ}
    (hgap : (toEuclideanLin A).singularValues r < (toEuclideanLin A).singularValues (r - 1)) :
    ∃ L : Matrix m n ℝ →L[ℝ] Matrix m n ℝ, HasFDerivAt (fun B => truncation B r) L A ∧
      ∀ H, ‖L H‖ ≤ (1 + 4 * ‖A‖ ^ 2 / ((toEuclideanLin A).singularValues (r - 1) ^ 2 -
        (toEuclideanLin A).singularValues r ^ 2)) * ‖H‖ := by
  set α := (toEuclideanLin A).singularValues (r - 1) with hαdef
  set β := (toEuclideanLin A).singularValues r with hβdef
  set P := topRightSingularVectors A r * (topRightSingularVectors A r)ᵀ with hPdef
  have hβ0 : 0 ≤ β := (toEuclideanLin A).singularValues_nonneg r
  have hg : 0 < α ^ 2 - β ^ 2 := by nlinarith
  have hP : IsOrthProjMat P := isOrthProjMat_topRightSingularVectors A r
  have hPc : Aᵀ * A * P = P * (Aᵀ * A) := transpose_mul_self_mul_comm A r
  have hα : ∀ Z : Matrix n n ℝ, P * Z = Z → α * ‖Z‖ ≤ ‖A * Z‖ :=
    fun Z hZ => singularValues_mul_norm_le_norm_mul hZ
  have hβ : ∀ Z : Matrix n n ℝ, P * Z = 0 → ‖A * Z‖ ≤ β * ‖Z‖ :=
    fun Z hZ => norm_mul_le_singularValues_mul hZ
  obtain ⟨X₀, hX₀⟩ := exists_linearMap_sylvester hP hPc hα hβ hβ0 hgap
  have hX₀n : ∀ F, (α ^ 2 - β ^ 2) * ‖X₀ F‖ ≤ ‖F‖ := fun F => by
    have h := sq_sub_sq_mul_norm_le_of_block hP hα hβ hβ0 hgap.le (hX₀ F).1
    rw [(hX₀ F).2] at h
    exact h.trans ((hP.compl.norm_mul_le' _).trans (hP.norm_mul_le _))
  let L₀ : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ :=
    { toFun := fun H => H * P + A * (X₀ (Hᵀ * A + Aᵀ * H) + (X₀ (Hᵀ * A + Aᵀ * H))ᵀ)
      map_add' := fun H H' => by
        simp only [transpose_add, Matrix.add_mul, Matrix.mul_add, map_add]
        abel
      map_smul' := fun c H => by
        simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, map_smul,
          RingHom.id_apply] }
  have hL₀ : ∀ H, L₀ H = H * P + A * (X₀ (Hᵀ * A + Aᵀ * H) + (X₀ (Hᵀ * A + Aᵀ * H))ᵀ) :=
    fun H => rfl
  refine ⟨LinearMap.toContinuousLinearMap L₀, ?_, fun H => ?_⟩
  · rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    refine IsBigO.trans_isLittleO ?_ (isLittleO_norm_pow_id one_lt_two)
    set c := 2 * ‖A‖ + 1 with hcdef
    set δ := min 1 ((α ^ 2 - β ^ 2) / (4 * (α + β + 1))) with hδdef
    have hδ : 0 < δ := lt_min one_pos (div_pos hg (by linarith))
    refine IsBigO.of_bound ((‖A‖ * (2 * (4 * c / ((α ^ 2 - β ^ 2) / 2 * 2)) ^ 2 +
      4 * (4 * c / ((α ^ 2 - β ^ 2) / 2 * 2)) * c / (α ^ 2 - β ^ 2) + 2 / (α ^ 2 - β ^ 2)) +
      4 * c / ((α ^ 2 - β ^ 2) / 2 * 2))) ?_
    filter_upwards [Metric.ball_mem_nhds (0 : Matrix m n ℝ) hδ] with H hH
    rw [mem_ball_zero_iff] at hH
    simp only [norm_pow, norm_norm]
    have hh1 : ‖H‖ ≤ 1 := hH.le.trans (min_le_left _ _)
    have hh2 : ‖H‖ ≤ (α ^ 2 - β ^ 2) / (4 * (α + β + 1)) := hH.le.trans (min_le_right _ _)
    -- the perturbed matrix
    have hW1 := WeylSingular.abs_singularValues_sub_le_frobenius (A + H) A (r - 1)
    have hW2 := WeylSingular.abs_singularValues_sub_le_frobenius (A + H) A r
    rw [add_sub_cancel_left] at hW1 hW2
    obtain ⟨g1, g2⟩ := half_le_sq_sub_sq hβ0 hgap
      ((toEuclideanLin (A + H)).singularValues_nonneg _) (norm_nonneg H) hh2 hW1 hW2
    set P' := topRightSingularVectors (A + H) r * (topRightSingularVectors (A + H) r)ᵀ
      with hP'def
    have hP' : IsOrthProjMat P' := isOrthProjMat_topRightSingularVectors (A + H) r
    have hP'c : (A + H)ᵀ * (A + H) * P' = P' * ((A + H)ᵀ * (A + H)) :=
      transpose_mul_self_mul_comm (A + H) r
    have hg2 : 0 < (α ^ 2 - β ^ 2) / 2 := by linarith
    have hlt1 : β < (toEuclideanLin (A + H)).singularValues (r - 1) := by
      by_contra hle
      have := pow_le_pow_left₀ ((toEuclideanLin (A + H)).singularValues_nonneg _)
        (not_lt.1 hle) 2
      linarith
    have hlt2 : (toEuclideanLin (A + H)).singularValues r < α := by
      by_contra hle
      have := pow_le_pow_left₀ (hβ0.trans hgap.le) (not_lt.1 hle) 2
      linarith
    have hDK := norm_sub_le_of_isOrthProjMat hP hP' hPc hP'c hα hβ
      (fun Z hZ => singularValues_mul_norm_le_norm_mul hZ)
      (fun Z hZ => norm_mul_le_singularValues_mul hZ) hβ0
      ((toEuclideanLin (A + H)).singularValues_nonneg r) hlt1 hlt2
    set E := (A + H)ᵀ * (A + H) - Aᵀ * A with hEdef
    have hEexp : E = (Hᵀ * A + Aᵀ * H) + Hᵀ * H := by
      rw [hEdef, transpose_add]
      simp only [Matrix.add_mul, Matrix.mul_add]
      abel
    have hEn : ‖E‖ ≤ c * ‖H‖ := by
      rw [hEexp]
      have h1 := frobenius_norm_mul Hᵀ A
      have h2 := frobenius_norm_mul Aᵀ H
      have h3 := frobenius_norm_mul Hᵀ H
      rw [Frobenius.norm_transpose] at h1 h2 h3
      have h4 : ‖H‖ * ‖H‖ ≤ ‖H‖ := by nlinarith [norm_nonneg H]
      calc ‖Hᵀ * A + Aᵀ * H + Hᵀ * H‖ ≤ ‖Hᵀ * A‖ + ‖Aᵀ * H‖ + ‖Hᵀ * H‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ c * ‖H‖ := by rw [hcdef]; nlinarith [norm_nonneg A, norm_nonneg H]
    have hDn : ‖P' - P‖ ≤ 4 * ‖E‖ / ((α ^ 2 - β ^ 2) / 2 * 2) := by
      refine hDK.trans ?_
      have i1 : 1 / ((toEuclideanLin (A + H)).singularValues (r - 1) ^ 2 - β ^ 2) ≤
          1 / ((α ^ 2 - β ^ 2) / 2) := one_div_le_one_div_of_le hg2 g1
      have i2 : 1 / (α ^ 2 - (toEuclideanLin (A + H)).singularValues r ^ 2) ≤
          1 / ((α ^ 2 - β ^ 2) / 2) := one_div_le_one_div_of_le hg2 g2
      calc ‖E‖ * (1 / ((toEuclideanLin (A + H)).singularValues (r - 1) ^ 2 - β ^ 2) +
            1 / (α ^ 2 - (toEuclideanLin (A + H)).singularValues r ^ 2)) ≤
            ‖E‖ * (1 / ((α ^ 2 - β ^ 2) / 2) + 1 / ((α ^ 2 - β ^ 2) / 2)) :=
          mul_le_mul_of_nonneg_left (add_le_add i1 i2) (norm_nonneg _)
        _ = _ := by field_simp; ring
    have hexp := norm_sub_sub_add_transpose_le hP hP' hPc hP'c hα hβ hβ0 hgap (hX₀ E).1
      (hX₀ E).2
    have hlin : X₀ E = X₀ (Hᵀ * A + Aᵀ * H) + X₀ (Hᵀ * H) := by rw [hEexp, map_add]
    have hHH : ‖X₀ (Hᵀ * H)‖ ≤ ‖H‖ ^ 2 / (α ^ 2 - β ^ 2) := by
      rw [le_div_iff₀ hg, mul_comm]
      refine (hX₀n _).trans ?_
      have := frobenius_norm_mul Hᵀ H
      rw [Frobenius.norm_transpose] at this
      nlinarith
    have hrem : truncation (A + H) r - truncation A r -
        LinearMap.toContinuousLinearMap L₀ H =
        A * ((P' - P - (X₀ E + (X₀ E)ᵀ)) + (X₀ (Hᵀ * H) + (X₀ (Hᵀ * H))ᵀ)) + H * (P' - P) := by
      rw [LinearMap.coe_toContinuousLinearMap', hL₀, truncation_eq_mul_topRightSingularVectors,
        truncation_eq_mul_topRightSingularVectors, ← hP'def, ← hPdef, hlin, transpose_add]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub]
      abel
    change ‖truncation (A + H) r - truncation A r - LinearMap.toContinuousLinearMap L₀ H‖ ≤ _
    rw [hrem]
    have hfin : ‖A * ((P' - P - (X₀ E + (X₀ E)ᵀ)) + (X₀ (Hᵀ * H) + (X₀ (Hᵀ * H))ᵀ)) +
        H * (P' - P)‖ ≤ ‖A‖ * (2 * ‖P' - P‖ ^ 2 + 4 * ‖P' - P‖ * ‖E‖ / (α ^ 2 - β ^ 2) +
          2 * ‖H‖ ^ 2 / (α ^ 2 - β ^ 2)) + ‖H‖ * ‖P' - P‖ := by
      refine (norm_add_le _ _).trans (add_le_add ((frobenius_norm_mul _ _).trans ?_)
        (frobenius_norm_mul _ _))
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (norm_add_le _ _).trans ?_
      have : ‖X₀ (Hᵀ * H) + (X₀ (Hᵀ * H))ᵀ‖ ≤ 2 * ‖H‖ ^ 2 / (α ^ 2 - β ^ 2) := by
        refine (norm_add_le _ _).trans ?_
        rw [Frobenius.norm_transpose, show 2 * ‖H‖ ^ 2 / (α ^ 2 - β ^ 2) =
          ‖H‖ ^ 2 / (α ^ 2 - β ^ 2) + ‖H‖ ^ 2 / (α ^ 2 - β ^ 2) by ring]
        exact add_le_add hHH hHH
      rw [← hEdef] at hexp
      exact add_le_add hexp this
    refine hfin.trans ?_
    have hg' : (α ^ 2 - β ^ 2) / 2 * 2 = α ^ 2 - β ^ 2 := by ring
    rw [hg'] at hDn ⊢
    exact quadratic_remainder_le (norm_nonneg A) (by positivity) (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg H) hg hDn hEn
  · rw [LinearMap.coe_toContinuousLinearMap', hL₀]
    have hE₁ : ‖Hᵀ * A + Aᵀ * H‖ ≤ 2 * ‖A‖ * ‖H‖ := by
      refine (norm_add_le _ _).trans ?_
      have h1 := frobenius_norm_mul Hᵀ A
      have h2 := frobenius_norm_mul Aᵀ H
      rw [Frobenius.norm_transpose] at h1 h2
      linarith
    have hXle : ‖X₀ (Hᵀ * A + Aᵀ * H)‖ ≤ 2 * ‖A‖ * ‖H‖ / (α ^ 2 - β ^ 2) := by
      rw [le_div_iff₀ hg, mul_comm]
      exact (hX₀n _).trans hE₁
    calc ‖H * P + A * (X₀ (Hᵀ * A + Aᵀ * H) + (X₀ (Hᵀ * A + Aᵀ * H))ᵀ)‖ ≤
        ‖H‖ + ‖A‖ * (2 * (2 * ‖A‖ * ‖H‖ / (α ^ 2 - β ^ 2))) := by
          refine (norm_add_le _ _).trans (add_le_add (hP.norm_mul_le' H)
            ((frobenius_norm_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))))
          refine (norm_add_le _ _).trans ?_
          rw [Frobenius.norm_transpose]
          linarith
      _ = _ := by
          field_simp
          ring

/-- Under a gap `σ_r(A) < σ_{r-1}(A)`, the truncated SVD `B ↦ T_r(B)` is differentiable at
`A`. -/
theorem EckartYoung.differentiableAt_truncation {A : Matrix m n ℝ} {r : ℕ}
    (hgap : (toEuclideanLin A).singularValues r < (toEuclideanLin A).singularValues (r - 1)) :
    DifferentiableAt ℝ (fun B => truncation B r) A :=
  let ⟨_, hL, _⟩ := hasFDerivAt_truncation hgap
  hL.differentiableAt

/-- Under a gap `σ_r(A) < σ_{r-1}(A)`, the truncated SVD `B ↦ T_r(B)` is continuous at `A`. -/
theorem EckartYoung.continuousAt_truncation {A : Matrix m n ℝ} {r : ℕ}
    (hgap : (toEuclideanLin A).singularValues r < (toEuclideanLin A).singularValues (r - 1)) :
    ContinuousAt (fun B => truncation B r) A :=
  (differentiableAt_truncation hgap).continuousAt

/-- **Bound on the derivative of the truncated SVD.** Under a gap `σ_r(A) < σ_{r-1}(A)`,
`‖D T_r(A) H‖ ≤ (1 + 4 ‖A‖² / (σ_{r-1}(A)² - σ_r(A)²)) ‖H‖`. -/
theorem EckartYoung.norm_fderiv_truncation_apply_le {A : Matrix m n ℝ} {r : ℕ}
    (hgap : (toEuclideanLin A).singularValues r < (toEuclideanLin A).singularValues (r - 1))
    (H : Matrix m n ℝ) :
    ‖fderiv ℝ (fun B => truncation B r) A H‖ ≤
      (1 + 4 * ‖A‖ ^ 2 / ((toEuclideanLin A).singularValues (r - 1) ^ 2 -
        (toEuclideanLin A).singularValues r ^ 2)) * ‖H‖ := by
  obtain ⟨L, hL, hb⟩ := hasFDerivAt_truncation hgap
  rw [hL.fderiv]
  exact hb H

/-- **Derivative of the truncated SVD along a curve.** If `A` has the derivative `A'` at `t`
within `s` (for example a right derivative, `s = Ici t`) and `σ_r(A t) < σ_{r-1}(A t)`, then
`u ↦ T_r(A u)` has the derivative `D T_r(A t) A'` at `t` within `s`; its norm is at most
`(1 + 4 ‖A t‖² / (σ_{r-1}(A t)² - σ_r(A t)²)) ‖A'‖`
(`EckartYoung.norm_fderiv_truncation_apply_le`). -/
theorem EckartYoung.hasDerivWithinAt_truncation {A : ℝ → Matrix m n ℝ} {A' : Matrix m n ℝ}
    {s : Set ℝ} {t : ℝ} {r : ℕ} (hA : HasDerivWithinAt A A' s t)
    (hgap : (toEuclideanLin (A t)).singularValues r <
      (toEuclideanLin (A t)).singularValues (r - 1)) :
    HasDerivWithinAt (fun u => truncation (A u) r)
      (fderiv ℝ (fun B => truncation B r) (A t) A') s t :=
  (differentiableAt_truncation hgap).hasFDerivAt.comp_hasDerivWithinAt t hA

end Derivative

/-! ### Examples -/

section Examples

/-- `Frobenius.sq_sub_sq_mul_norm_le_norm_sylvester` with `B₁ = 1`, `B₂ = 0`, `α = 1`, `β = 0`. -/
example (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    ((1 : ℝ) ^ 2 - 0 ^ 2) * ‖Z‖ ≤ ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1 * Z -
      Z * ((0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 0)‖ :=
  Frobenius.sq_sub_sq_mul_norm_le_norm_sylvester le_rfl zero_le_one (by simp) (by simp)

/-- The bounds on the range and on the kernel of `Q = V_r V_rᵀ`, for `Z = Q` and `Z = 1 - Q`. -/
example (A : Matrix (Fin 2) (Fin 3) ℝ) (r : ℕ) :
    (toEuclideanLin A).singularValues (r - 1) *
        ‖topRightSingularVectors A r * (topRightSingularVectors A r)ᵀ‖ ≤
      ‖A * (topRightSingularVectors A r * (topRightSingularVectors A r)ᵀ)‖ ∧
    ‖A * (1 - topRightSingularVectors A r * (topRightSingularVectors A r)ᵀ)‖ ≤
      (toEuclideanLin A).singularValues r *
        ‖1 - topRightSingularVectors A r * (topRightSingularVectors A r)ᵀ‖ :=
  ⟨singularValues_mul_norm_le_norm_mul (isOrthProjMat_topRightSingularVectors A r).idem,
    norm_mul_le_singularValues_mul (by
      rw [Matrix.mul_sub, Matrix.mul_one, (isOrthProjMat_topRightSingularVectors A r).idem,
        sub_self])⟩

/-- The first unit column of `ℝ²`. -/
local notation "e₁" => (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)

private theorem e₁_transpose_mul_self : e₁ᵀ * e₁ = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem smul_e₁_mul (c : ℝ) :
    c • (e₁ * e₁ᵀ) = e₁ * (c • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * e₁ᵀ := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- `c e₁ e₁ᵀ` has the gap `σ₁ = 0 < 1 ≤ σ₀` for `c ≥ 1`. -/
private theorem gap_smul_e₁ {c : ℝ} (hc : 1 ≤ c) :
    (toEuclideanLin (c • (e₁ * e₁ᵀ))).singularValues 1 ≤ 0 ∧
      (1 : ℝ) ≤ (toEuclideanLin (c • (e₁ * e₁ᵀ))).singularValues (1 - 1) := by
  constructor
  · have hr : (c • (e₁ * e₁ᵀ)).rank ≤ 1 := by
      rw [smul_e₁_mul]
      exact (rank_mul_le_right _ _).trans (by simpa using rank_le_card_height e₁ᵀ)
    have h := EckartYoung.singularValues_le_specNorm_sub (c • (e₁ * e₁ᵀ)) (c • (e₁ * e₁ᵀ)) hr
    rw [sub_self] at h
    exact h.trans ((specNorm_le_frob 0).trans_eq norm_zero)
  · refine SVD.le_singularValues_of_eq_mul one_pos e₁_transpose_mul_self e₁_transpose_mul_self
      (smul_e₁_mul c) fun w => ?_
    rw [LinearEquiv.map_smul, toLpLin_one]
    change 1 * ‖w‖ ≤ ‖c • w‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    nlinarith [norm_nonneg w]

private theorem lt_smul_e₁ {c : ℝ} (hc : 1 ≤ c) :
    (toEuclideanLin (c • (e₁ * e₁ᵀ))).singularValues 1 <
      (toEuclideanLin (c • (e₁ * e₁ᵀ))).singularValues (1 - 1) := by
  have h := gap_smul_e₁ hc
  linarith [h.1, h.2]

/-- Under the gap, the truncation of `e₁ e₁ᵀ` to rank `1` is `e₁ e₁ᵀ P` for the projector
`P = e₁ e₁ᵀ`, obtained from `EckartYoung.truncation_eq_mul_of_isOrthProjMat` with `α = 1`,
`β = 0`, without computing singular vectors. -/
example : truncation ((1 : ℝ) • (e₁ * e₁ᵀ)) 1 = (1 : ℝ) • (e₁ * e₁ᵀ) * (e₁ * e₁ᵀ) := by
  have hP : IsOrthProjMat (e₁ * e₁ᵀ) := isOrthProjMat_mul_transpose e₁_transpose_mul_self
  have hA : ((1 : ℝ) • (e₁ * e₁ᵀ))ᵀ * ((1 : ℝ) • (e₁ * e₁ᵀ)) = e₁ * e₁ᵀ := by
    rw [one_smul, transpose_mul, transpose_transpose, hP.idem]
  have h := gap_smul_e₁ (le_refl (1 : ℝ))
  refine EckartYoung.truncation_eq_mul_of_isOrthProjMat (α := 1) (β := 0) hP
    (by rw [hA]) (fun Z hZ => ?_) (fun Z hZ => ?_) le_rfl (by linarith [h.2])
    (by linarith [h.1])
  · rw [one_smul, hZ, one_mul]
  · rw [one_smul, hZ, norm_zero, zero_mul]

private theorem hasDerivAt_smul_e₁ (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) (e₁ * e₁ᵀ) t := by
  simpa using ((hasDerivAt_id t).const_add 1).smul_const (e₁ * e₁ᵀ)

/-- The truncation to rank `1` is differentiable at `e₁ e₁ᵀ` (gap `σ₁ = 0 < σ₀`), and the curve
`t ↦ T₁((1 + t) e₁ e₁ᵀ)` has a right derivative at `0` of norm at most
`(1 + 4 ‖e₁ e₁ᵀ‖² / (σ₀² - σ₁²)) ‖e₁ e₁ᵀ‖`. -/
example : DifferentiableAt ℝ (fun B => truncation B 1) ((1 : ℝ) • (e₁ * e₁ᵀ)) ∧
    HasDerivWithinAt (fun t : ℝ => truncation ((1 + t) • (e₁ * e₁ᵀ)) 1)
      (fderiv ℝ (fun B => truncation B 1) ((1 + 0 : ℝ) • (e₁ * e₁ᵀ)) (e₁ * e₁ᵀ))
      (Set.Ici 0) 0 ∧
    ‖fderiv ℝ (fun B => truncation B 1) ((1 + 0 : ℝ) • (e₁ * e₁ᵀ)) (e₁ * e₁ᵀ)‖ ≤
      (1 + 4 * ‖(1 + 0 : ℝ) • (e₁ * e₁ᵀ)‖ ^ 2 /
        ((toEuclideanLin ((1 + 0 : ℝ) • (e₁ * e₁ᵀ))).singularValues (1 - 1) ^ 2 -
          (toEuclideanLin ((1 + 0 : ℝ) • (e₁ * e₁ᵀ))).singularValues 1 ^ 2)) * ‖e₁ * e₁ᵀ‖ := by
  have hgap0 := lt_smul_e₁ (le_refl (1 : ℝ))
  have hgap := lt_smul_e₁ (by norm_num : (1 : ℝ) ≤ 1 + 0)
  exact ⟨EckartYoung.differentiableAt_truncation hgap0,
    EckartYoung.hasDerivWithinAt_truncation (hasDerivAt_smul_e₁ 0).hasDerivWithinAt hgap,
    EckartYoung.norm_fderiv_truncation_apply_le hgap _⟩

end Examples

end LeanDLRA
