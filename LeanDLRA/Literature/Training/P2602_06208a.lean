import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Classical.WeylSingular
import LeanDLRA.Classical.SVD
import LeanDLRA.OpenProblems.Curated.Classicala

/-!
# Results of arXiv 2602.06208: Emergent low-rank training dynamics in MLPs

Xu, Yaras, Asato, Qu, Balzano.  For the two-layer network `f(X) = W₂ φ(W₁ X)` with fixed second
layer, whitened data, squared loss and gradient descent from `W₁(0)ᵀ W₁(0) = ε² I`, this module
proves the paper's main result, **Theorem D.11** (`Net.theorem_D_11`) with its simplified form
**Theorem 3.5** (`Net.theorem_3_5`): there are fixed orthogonal `U`, `V` such that the blocks 2, 3,
4 of `Uᵀ W₁(t) V` move by at most `η ρ(t)` per iteration, in normalised Frobenius norm, with
`ρ(0) ≤ r(ε)` and `ρ(t) ≤ C₂ q^t (1 - q^t)` for `t ≥ 1`.  The network, the loss and the gradient
are concrete: `Net.hasGradientAt_loss` is eq. (12), and `Net.Run` is gradient descent under
Assumption 3.4.  All the supporting results are proved: Lemmas D.1–D.10 (`lemma_D_1`, …,
`Net.lemma_D_10`), including the principal-angle form of Lemma D.3 and Wedin's theorem (Lemma D.5,
only cited in the paper) with left and right subspaces and without the `√2` of the library's
`LeanDLRA.SinTheta.wedin_frobenius`.
The block structure itself (`exists_block_decomposition`) holds for arbitrary gradient-like
sequences.  `exists_isSVD` shows that the SVDs of `Net.Run` always exist, and
`hypotheses_satisfiable` exhibits a run (with `φ = id`) that satisfies all hypotheses.

Differences from the paper, explained in the docstrings: `(1 - Θ(η))^{Θ(t)}` is written `q^t`
(`rpow_decay_eq_pow`, `decay_factor_mem`) and `Θ(1)` is explicit; `0 < φ'(0)` and `0 < ε`, used
silently in the paper, are hypotheses; the paper states that the denominator of `δ(t)` is positive
by Assumption 3.4 and `r(ε) < φ'(0) σ_K / 2`; this step is not derived here from those alone:
`Net.lemma_D_9` and `Net.lemma_D_10` are **conditional on** the positivity of the denominator
(hypothesis `hden`), and Theorems D.11 and 3.5 instead **add** the hypothesis `1 - φ'(0)/2 ≤ G₃`,
from which the positivity is proved (`Net.Run.deltaDen_pos`); no counterexample for smaller `G₃`
is formalized; `η ≤ 1/γ_L` and the full row rank of `W₂` are not needed and are dropped; the bound
at `t = 0` is sharper; in Theorem 3.5 the constant `C₂` depends on `η` through `1 / (1 - q)`; and
the proof of Lemma D.10 uses `dim 𝒮 = p`, where the formal proof only needs and uses
`dim 𝒮 ≥ p`.

Not formalized: Proposition B.1/E.1 (non-smooth activations; a random matrix argument, outside the
list of this slice) and the empirical parts of the paper.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2602_06208

open Matrix Module LeanDLRA.Curvature LeanDLRA.EckartYoung

noncomputable section

/-! ### Norms and singular values -/

section Norms

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- The singular value `σ_{i+1}(A)` of the paper: Mathlib's `LinearMap.singularValues`, sorted
decreasingly and **zero-based**, so that the paper's `σ₁`, `σ_K`, `σ_{K+1}` are `sv A 0`,
`sv A (K - 1)`, `sv A K`. -/
abbrev sv [DecidableEq β] (A : Matrix α β ℝ) (i : ℕ) : ℝ :=
  (toEuclideanLin A).singularValues i

lemma sv_nonneg [DecidableEq β] (A : Matrix α β ℝ) (i : ℕ) : 0 ≤ sv A i :=
  (toEuclideanLin A).singularValues_nonneg i

lemma sv_antitone [DecidableEq β] (A : Matrix α β ℝ) {i j : ℕ} (h : i ≤ j) : sv A j ≤ sv A i :=
  (toEuclideanLin A).singularValues_antitone h

/-- `‖A‖_max`, the largest magnitude of an entry (Mathlib's entrywise sup norm). -/
def maxNorm (A : Matrix α β ℝ) : ℝ :=
  ((Finset.univ.sup fun i => Finset.univ.sup fun j => ‖A i j‖₊ : NNReal) : ℝ)

lemma abs_le_maxNorm (A : Matrix α β ℝ) (i : α) (j : β) : |A i j| ≤ maxNorm A := by
  have h1 : ‖A i j‖₊ ≤ Finset.univ.sup fun j => ‖A i j‖₊ :=
    Finset.le_sup (f := fun j => ‖A i j‖₊) (Finset.mem_univ j)
  have h2 : (Finset.univ.sup fun j => ‖A i j‖₊) ≤
      Finset.univ.sup fun i => Finset.univ.sup fun j => ‖A i j‖₊ :=
    Finset.le_sup (f := fun i => Finset.univ.sup fun j => ‖A i j‖₊) (Finset.mem_univ i)
  exact_mod_cast NNReal.coe_le_coe.mpr (h1.trans h2)

lemma maxNorm_nonneg (A : Matrix α β ℝ) : 0 ≤ maxNorm A := NNReal.coe_nonneg _

lemma maxNorm_le {A : Matrix α β ℝ} {r : ℝ} (hr : 0 ≤ r) (h : ∀ i j, |A i j| ≤ r) :
    maxNorm A ≤ r := by
  lift r to NNReal using hr
  rw [maxNorm, NNReal.coe_le_coe]
  refine Finset.sup_le fun i _ => Finset.sup_le fun j _ => ?_
  rw [← NNReal.coe_le_coe]
  simpa using h i j

/-- `‖A‖_∞`, the largest absolute row sum (the value of Mathlib's `Matrix.linftyOpNorm`, see
`Matrix.linfty_opNorm_def`). -/
def infNorm (A : Matrix α β ℝ) : ℝ := ((Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ : NNReal) : ℝ)

/-- `‖A‖₁`, the largest absolute column sum. -/
def oneNorm (A : Matrix α β ℝ) : ℝ := infNorm Aᵀ

lemma infNorm_nonneg (A : Matrix α β ℝ) : 0 ≤ infNorm A := NNReal.coe_nonneg _

lemma sum_abs_le_infNorm (A : Matrix α β ℝ) (i : α) : ∑ j, |A i j| ≤ infNorm A := by
  have h2 : ∑ j, ‖A i j‖₊ ≤ (Finset.univ : Finset α).sup fun i => ∑ j, ‖A i j‖₊ :=
    Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i)
  have h3 := NNReal.coe_le_coe.mpr h2
  simpa [infNorm] using h3

lemma infNorm_le {A : Matrix α β ℝ} {r : ℝ} (hr : 0 ≤ r) (h : ∀ i, ∑ j, |A i j| ≤ r) :
    infNorm A ≤ r := by
  lift r to NNReal using hr
  rw [infNorm, NNReal.coe_le_coe]
  refine Finset.sup_le fun i _ => ?_
  rw [← NNReal.coe_le_coe]
  simpa using h i

lemma oneNorm_nonneg (A : Matrix α β ℝ) : 0 ≤ oneNorm A := infNorm_nonneg _

lemma sum_abs_le_oneNorm (A : Matrix α β ℝ) (j : β) : ∑ i, |A i j| ≤ oneNorm A :=
  sum_abs_le_infNorm Aᵀ j

lemma oneNorm_le {A : Matrix α β ℝ} {r : ℝ} (hr : 0 ≤ r) (h : ∀ j, ∑ i, |A i j| ≤ r) :
    oneNorm A ≤ r :=
  infNorm_le hr h

variable [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] [Fintype α] in
lemma toEuclideanLin_coord (A : Matrix α β ℝ) (x : EuclideanSpace ℝ β) (i : α) :
    toEuclideanLin A x i = ∑ j, A i j * x j := by
  simp [Matrix.toLpLin_apply, mulVec, dotProduct]

omit [DecidableEq α] in
lemma specNorm_le_of_sq {A : Matrix α β ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : EuclideanSpace ℝ β, ‖toEuclideanLin A x‖ ^ 2 ≤ C ^ 2 * ‖x‖ ^ 2) :
    specNorm A ≤ C := by
  refine specNorm_le_of hC fun x => ?_
  have h1 := h x
  rw [← mul_pow] at h1
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1

omit [DecidableEq α] in
/-- Entrywise domination implies domination of the spectral norm (the fact behind Lemma D.1 and
the Horn–Johnson Theorem 8.1.18 citation in the proof of Lemma D.8). -/
lemma specNorm_le_of_abs_le {A B : Matrix α β ℝ} (h : ∀ i j, |A i j| ≤ B i j) :
    specNorm A ≤ specNorm B := by
  refine specNorm_le_of (specNorm_nonneg _) fun x => ?_
  let y : EuclideanSpace ℝ β := WithLp.toLp 2 fun j => |x j|
  have hy : ‖y‖ = ‖x‖ := by simp [y, EuclideanSpace.norm_eq]
  have key : ‖toEuclideanLin A x‖ ≤ ‖toEuclideanLin B y‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, toEuclideanLin_coord,
      toEuclideanLin_coord]
    refine sq_le_sq.mpr ?_
    have hB : 0 ≤ ∑ j, B i j * y j := Finset.sum_nonneg fun j _ =>
      mul_nonneg ((abs_nonneg _).trans (h i j)) (abs_nonneg _)
    rw [abs_of_nonneg hB]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (h i j) (abs_nonneg _)
  calc _ ≤ ‖toEuclideanLin B y‖ := key
    _ ≤ specNorm B * ‖y‖ := norm_toEuclideanLin_le B y
    _ = _ := by rw [hy]

omit [DecidableEq α] in
/-- The Schur test: `‖A‖₂ ≤ √(‖A‖_∞ ‖A‖₁)` (with `c₁`, `c₂` bounding the row and column sums). -/
lemma specNorm_le_sqrt_of_schur {A : Matrix α β ℝ} {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hrow : ∀ i, ∑ j, |A i j| ≤ c₁) (hcol : ∀ j, ∑ i, |A i j| ≤ c₂) :
    specNorm A ≤ √(c₁ * c₂) := by
  refine specNorm_le_of_sq (Real.sqrt_nonneg _) fun x => ?_
  rw [Real.sq_sqrt (mul_nonneg hc₁ hc₂), EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  have hi : ∀ i, ‖toEuclideanLin A x i‖ ^ 2 ≤ c₁ * ∑ j, |A i j| * x j ^ 2 := fun i => by
    rw [Real.norm_eq_abs, sq_abs, toEuclideanLin_coord]
    have h1 : (∑ j, A i j * x j) ^ 2 ≤ (∑ j, |A i j| * |x j|) ^ 2 := by
      refine sq_le_sq.mpr ?_
      have hnn : 0 ≤ ∑ j, |A i j| * |x j| :=
        Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
      rw [abs_of_nonneg hnn]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun j _ => abs_mul _ _
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => √|A i j|)
      (fun j => √|A i j| * |x j|)
    have e1 : ∀ j, √|A i j| * (√|A i j| * |x j|) = |A i j| * |x j| := fun j => by
      rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg _)]
    have e2 : ∀ j, √|A i j| ^ 2 = |A i j| := fun j => Real.sq_sqrt (abs_nonneg _)
    have e3 : ∀ j, (√|A i j| * |x j|) ^ 2 = |A i j| * x j ^ 2 := fun j => by
      rw [mul_pow, e2, sq_abs]
    simp only [e1, e2, e3] at h2
    refine h1.trans (h2.trans ?_)
    exact mul_le_mul_of_nonneg_right (hrow i)
      (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
  calc ∑ i, ‖toEuclideanLin A x i‖ ^ 2
      ≤ ∑ i, c₁ * ∑ j, |A i j| * x j ^ 2 := Finset.sum_le_sum fun i _ => hi i
    _ = c₁ * ∑ j, (∑ i, |A i j|) * x j ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ ≤ c₁ * ∑ j, c₂ * x j ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hc₁
        exact mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
    _ = c₁ * c₂ * ∑ j, ‖x j‖ ^ 2 := by
        simp only [Real.norm_eq_abs, sq_abs, Finset.mul_sum, mul_assoc]

omit [DecidableEq α] in
/-- A column of `A` has Euclidean norm at most `‖A‖₂`. -/
lemma sum_sq_col_le (A : Matrix α β ℝ) (j : β) : ∑ i, A i j ^ 2 ≤ specNorm A ^ 2 := by
  have h := norm_toEuclideanLin_le A (EuclideanSpace.single j 1)
  have h1 : ‖toEuclideanLin A (EuclideanSpace.single j 1)‖ ^ 2 = ∑ i, A i j ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs, toEuclideanLin_coord]
    simp
  rw [← h1]
  simpa using pow_le_pow_left₀ (norm_nonneg _) h 2

omit [DecidableEq α] in
/-- A row of `A` has Euclidean norm at most `‖A‖₂`. -/
lemma sum_sq_row_le (A : Matrix α β ℝ) (i : α) : ∑ j, A i j ^ 2 ≤ specNorm A ^ 2 := by
  classical
  have h := sum_sq_col_le Aᵀ i
  rwa [specNorm_transpose] at h

end Norms

/-! ### Singular value decompositions -/

section SVD

variable {m d : ℕ} {γ : Type*} [Fintype γ]

/-- The rectangular diagonal matrix `Σ` of the singular values of `A`. -/
def singularDiag (A : Matrix (Fin m) (Fin d) ℝ) : Matrix (Fin m) (Fin d) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = j then sv A i else 0

/-- `A = L Σ Rᵀ` is a (full) singular value decomposition: `L`, `R` are orthogonal and `Σ` carries
the singular values of `A`, sorted decreasingly. -/
structure IsSVD (A : Matrix (Fin m) (Fin d) ℝ) (L : Matrix (Fin m) (Fin m) ℝ)
    (R : Matrix (Fin d) (Fin d) ℝ) : Prop where
  left : Lᵀ * L = 1
  right : Rᵀ * R = 1
  eq : A = L * singularDiag A * Rᵀ

/-- The first `K` columns of `U`; for a factor of an SVD these are the top-`K` singular vectors
(the paper's `L₁,₁(t)`, `R₁,₁(t)`). -/
def topCols {α : Type*} {n K : ℕ} (hK : K ≤ n) (U : Matrix α (Fin n) ℝ) : Matrix α (Fin K) ℝ :=
  U.submatrix id (Fin.castLE hK)

lemma topCols_transpose_mul_self {α : Type*} [Fintype α] {n K : ℕ} (hK : K ≤ n)
    {U : Matrix α (Fin n) ℝ} (hU : Uᵀ * U = 1) : (topCols hK U)ᵀ * topCols hK U = 1 := by
  have h : (topCols hK U)ᵀ * topCols hK U = (Uᵀ * U).submatrix (Fin.castLE hK) (Fin.castLE hK) := by
    ext i j
    simp [topCols, Matrix.mul_apply]
  rw [h, hU]
  exact Matrix.submatrix_one _ (Fin.castLE_injective hK)

lemma singularDiag_transpose (A : Matrix (Fin m) (Fin d) ℝ) :
    singularDiag Aᵀ = (singularDiag A)ᵀ := by
  ext i j
  simp only [singularDiag, of_apply, transpose_apply]
  by_cases h : (i : ℕ) = j
  · rw [h]
    simp [LeanDLRA.SVD.singularValues_transpose]
  · have h' : ¬ (j : ℕ) = i := fun e => h e.symm
    simp [h, h']

variable {A : Matrix (Fin m) (Fin d) ℝ} {L : Matrix (Fin m) (Fin m) ℝ}
  {R : Matrix (Fin d) (Fin d) ℝ}

/-- `Aᵀ = R Σᵀ Lᵀ`. -/
lemma IsSVD.transpose (h : IsSVD A L R) : IsSVD Aᵀ R L where
  left := h.right
  right := h.left
  eq := by
    conv_lhs => rw [h.eq]
    rw [singularDiag_transpose]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]

lemma IsSVD.mul_transpose_right (h : IsSVD A L R) : R * Rᵀ = 1 := mul_eq_one_comm.mp h.right

lemma IsSVD.mul_right (h : IsSVD A L R) : A * R = L * singularDiag A := by
  conv_lhs => rw [h.eq]
  rw [Matrix.mul_assoc, h.right, Matrix.mul_one]

omit [Fintype γ] in
lemma singularDiag_mul_apply (A : Matrix (Fin m) (Fin d) ℝ) (Z : Matrix (Fin d) γ ℝ) (i : Fin m)
    (c : γ) :
    (singularDiag A * Z) i c = if h : (i : ℕ) < d then sv A i * Z ⟨i, h⟩ c else 0 := by
  rw [Matrix.mul_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i, h⟩]
    · simp [singularDiag]
    · intro j _ hj
      have hne : (i : ℕ) ≠ j := fun e => hj (Fin.ext e.symm)
      simp [singularDiag, hne]
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    have hne : (i : ℕ) ≠ j := fun e => h (e ▸ j.2)
    simp [singularDiag, hne]

lemma norm_singularDiag_mul_sq_le (A : Matrix (Fin m) (Fin d) ℝ) (Z : Matrix (Fin d) γ ℝ) :
    ‖singularDiag A * Z‖ ^ 2 ≤ ∑ j : Fin d, sv A j ^ 2 * ∑ c, Z j c ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  let e : ℕ → ℝ := fun k => if h : k < d then sv A k ^ 2 * ∑ c, Z ⟨k, h⟩ c ^ 2 else 0
  have he : ∀ k, 0 ≤ e k := fun k => by
    simp only [e]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    · exact le_rfl
  have h1 : ∀ i : Fin m, ∑ c, (singularDiag A * Z) i c ^ 2 = e i := fun i => by
    simp only [singularDiag_mul_apply, e]
    split_ifs with h
    · simp [mul_pow, Finset.mul_sum]
    · simp
  have h2 : ∑ j : Fin d, sv A j ^ 2 * ∑ c, Z j c ^ 2 = ∑ j : Fin d, e j :=
    Finset.sum_congr rfl fun j _ => by simp [e, j.2]
  rw [h2]
  simp_rw [h1]
  rw [Fin.sum_univ_eq_sum_range e m, Fin.sum_univ_eq_sum_range e d]
  calc ∑ k ∈ Finset.range m, e k = ∑ k ∈ (Finset.range m).filter (· < d), e k := by
        refine (Finset.sum_filter_of_ne fun k _ hk => ?_).symm
        by_contra hkd
        exact hk (by simp [e, hkd])
    _ ≤ ∑ k ∈ Finset.range d, e k := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => he k
        intro k hk
        simpa using (Finset.mem_filter.mp hk).2

lemma sum_castLE {n K : ℕ} (hK : K ≤ n) (f : Fin n → ℝ) :
    ∑ j : Fin K, f (Fin.castLE hK j) = ∑ j : Fin n, if (j : ℕ) < K then f j else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun j _ => Fin.castLE hK j) ?_ ?_ ?_ ?_
  · intro j _
    simp
  · intro i _ j _ h
    exact Fin.castLE_injective hK h
  · intro j hj
    refine ⟨⟨j, by simpa using hj⟩, Finset.mem_univ _, ?_⟩
    ext
    simp
  · intro j _
    rfl

/-- The estimate `‖A B‖_F² ≤ σ₁² ‖R₁ᵀ B‖_F² + σ_{K+1}² ‖B‖_F²`, the paper's split of `G₁(t) V` into
the top-`K` and the bottom components (proof of Lemma D.10). -/
lemma IsSVD.norm_mul_sq_le (h : IsSVD A L R) {K : ℕ} (hK : K ≤ d) (B : Matrix (Fin d) γ ℝ) :
    ‖A * B‖ ^ 2 ≤ sv A 0 ^ 2 * ‖(topCols hK R)ᵀ * B‖ ^ 2 + sv A K ^ 2 * ‖B‖ ^ 2 := by
  set Z := Rᵀ * B with hZ
  have e1 : A * B = L * (singularDiag A * Z) := by
    conv_lhs => rw [h.eq]
    simp only [hZ, Matrix.mul_assoc]
  have e2 : ‖A * B‖ = ‖singularDiag A * Z‖ := by
    rw [e1, Frobenius.norm_mul_of_orthonormal h.left]
  have hBZ : ‖Z‖ = ‖B‖ := by
    rw [hZ]
    refine Frobenius.norm_mul_of_orthonormal ?_ B
    rw [transpose_transpose]
    exact h.mul_transpose_right
  let ρ : Fin d → ℝ := fun j => ∑ c, Z j c ^ 2
  have hρ : ∀ j, 0 ≤ ρ j := fun j => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hZsq : ‖B‖ ^ 2 = ∑ j, ρ j := by rw [← hBZ, Frobenius.norm_sq_eq_sum]
  have hTop : ‖(topCols hK R)ᵀ * B‖ ^ 2 = ∑ j : Fin d, if (j : ℕ) < K then ρ j else 0 := by
    rw [← sum_castLE hK ρ, Frobenius.norm_sq_eq_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
    simp [hZ, topCols, Matrix.mul_apply]
  rw [e2, hTop, hZsq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine (norm_singularDiag_mul_sq_le A Z).trans (Finset.sum_le_sum fun j _ => ?_)
  have hanti := (toEuclideanLin A).singularValues_antitone
  have hnn := (toEuclideanLin A).singularValues_nonneg
  split_ifs with hj
  · have h1 : sv A j ≤ sv A 0 := hanti (Nat.zero_le _)
    have h2 : sv A j ^ 2 ≤ sv A 0 ^ 2 := pow_le_pow_left₀ (hnn _) h1 2
    have h3 := mul_le_mul_of_nonneg_right h2 (hρ j)
    have h4 : 0 ≤ sv A K ^ 2 * ρ j := mul_nonneg (sq_nonneg _) (hρ j)
    linarith
  · have h1 : sv A j ≤ sv A K := hanti (not_lt.mp hj)
    have h2 : sv A j ^ 2 ≤ sv A K ^ 2 := pow_le_pow_left₀ (hnn _) h1 2
    have h3 := mul_le_mul_of_nonneg_right h2 (hρ j)
    simpa using h3

/-- `A R₁ = L₁ D` with `D = diag(σ₁, …, σ_K)`. -/
lemma IsSVD.mul_topCols (h : IsSVD A L R) {K : ℕ} (hKm : K ≤ m) (hKd : K ≤ d) :
    A * topCols hKd R = topCols hKm L * diagonal fun i : Fin K => sv A i := by
  ext i j
  have h1 : (A * R) i (Fin.castLE hKd j) = (L * singularDiag A) i (Fin.castLE hKd j) := by
    rw [h.mul_right]
  have h2 : (A * topCols hKd R) i j = (A * R) i (Fin.castLE hKd j) := by
    simp [topCols, Matrix.mul_apply]
  rw [h2, h1, Matrix.mul_apply, Matrix.mul_diagonal, Finset.sum_eq_single (Fin.castLE hKm j)]
  · simp [singularDiag, topCols]
  · intro k _ hk
    have hne : (k : ℕ) ≠ j := fun e => hk (Fin.ext (by simpa using e))
    simp [singularDiag, hne]
  · simp

/-- `Aᵀ L₁ = R₁ D` with `D = diag(σ₁, …, σ_K)`. -/
lemma IsSVD.transpose_mul_topCols (h : IsSVD A L R) {K : ℕ} (hKm : K ≤ m) (hKd : K ≤ d) :
    Aᵀ * topCols hKm L = topCols hKd R * diagonal fun i : Fin K => sv A i := by
  have h1 := h.transpose.mul_topCols hKd hKm
  simpa only [sv, LeanDLRA.SVD.singularValues_transpose] using h1

/-- The projectors on the top-`K` left and right singular spaces intertwine `A`. -/
lemma IsSVD.compl_mul (h : IsSVD A L R) {K : ℕ} (hKm : K ≤ m) (hKd : K ≤ d) :
    (1 - topCols hKm L * (topCols hKm L)ᵀ) * A = A * (1 - topCols hKd R * (topCols hKd R)ᵀ) := by
  have h1 := h.mul_topCols hKm hKd
  have h2 := congrArg Matrix.transpose (h.transpose_mul_topCols hKm hKd)
  rw [Matrix.transpose_mul, Matrix.transpose_mul, transpose_transpose, diagonal_transpose] at h2
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, h2,
    ← Matrix.mul_assoc A, h1, Matrix.mul_assoc]

lemma mul_norm_le_norm_mul_diagonal {α : Type*} [Fintype α] {K : ℕ} (Y : Matrix α (Fin K) ℝ)
    (D : Fin K → ℝ) {s : ℝ} (hs : 0 ≤ s) (hD : ∀ i, s ≤ D i) : s * ‖Y‖ ≤ ‖Y * diagonal D‖ := by
  have h : (s * ‖Y‖) ^ 2 ≤ ‖Y * diagonal D‖ ^ 2 := by
    rw [mul_pow, Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Matrix.mul_diagonal, mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs (hD j) 2) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h

/-- One half of Wedin's coupled inequalities. -/
lemma wedin_half {A B : Matrix (Fin m) (Fin d) ℝ} {L L' : Matrix (Fin m) (Fin m) ℝ}
    {R R' : Matrix (Fin d) (Fin d) ℝ} (hA : IsSVD A L R) (hB : IsSVD B L' R') {K : ℕ}
    (hK : 0 < K) (hKm : K ≤ m) (hKd : K ≤ d) :
    sv B (K - 1) * ‖(1 - topCols hKm L * (topCols hKm L)ᵀ) * topCols hKm L'‖ ≤
      sv A K * ‖(1 - topCols hKd R * (topCols hKd R)ᵀ) * topCols hKd R'‖ + ‖B - A‖ := by
  set L₁ := topCols hKm L
  set R₁ := topCols hKd R
  set L₁' := topCols hKm L'
  set R₁' := topCols hKd R'
  have hL₁ : L₁ᵀ * L₁ = 1 := topCols_transpose_mul_self hKm hA.left
  have hR₁ : R₁ᵀ * R₁ = 1 := topCols_transpose_mul_self hKd hA.right
  have hR₁' : R₁'ᵀ * R₁' = 1 := topCols_transpose_mul_self hKd hB.right
  have hQL : IsOrthProjMat (1 - L₁ * L₁ᵀ) := (isOrthProjMat_mul_transpose hL₁).compl
  have hs : ∀ i : Fin K, sv B (K - 1) ≤ sv B i := fun i =>
    (toEuclideanLin B).singularValues_antitone (by omega)
  have h1 := mul_norm_le_norm_mul_diagonal ((1 - L₁ * L₁ᵀ) * L₁') (fun i : Fin K => sv B i)
    ((toEuclideanLin B).singularValues_nonneg _) hs
  have h2 : (1 - L₁ * L₁ᵀ) * L₁' * diagonal (fun i : Fin K => sv B i) =
      A * ((1 - R₁ * R₁ᵀ) * R₁') + (1 - L₁ * L₁ᵀ) * (B - A) * R₁' := by
    have hB' : L₁' * diagonal (fun i : Fin K => sv B i) = B * R₁' :=
      (hB.mul_topCols hKm hKd).symm
    have hc : (1 - L₁ * L₁ᵀ) * A = A * (1 - R₁ * R₁ᵀ) := hA.compl_mul hKm hKd
    calc (1 - L₁ * L₁ᵀ) * L₁' * diagonal (fun i : Fin K => sv B i)
        = (1 - L₁ * L₁ᵀ) * (B * R₁') := by rw [Matrix.mul_assoc, hB']
      _ = (1 - L₁ * L₁ᵀ) * A * R₁' + (1 - L₁ * L₁ᵀ) * (B - A) * R₁' := by
          rw [← Matrix.add_mul, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_assoc]
      _ = _ := by rw [hc, Matrix.mul_assoc]
  have h3 : ‖A * ((1 - R₁ * R₁ᵀ) * R₁')‖ ≤ sv A K * ‖(1 - R₁ * R₁ᵀ) * R₁'‖ := by
    have h4 := hA.norm_mul_sq_le hKd ((1 - R₁ * R₁ᵀ) * R₁')
    have h5 : (topCols hKd R)ᵀ * ((1 - R₁ * R₁ᵀ) * R₁') = 0 := by
      rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hR₁,
        Matrix.one_mul, sub_self, Matrix.zero_mul]
    rw [h5, norm_zero] at h4
    have h6 : ‖A * ((1 - R₁ * R₁ᵀ) * R₁')‖ ^ 2 ≤ (sv A K * ‖(1 - R₁ * R₁ᵀ) * R₁'‖) ^ 2 := by
      rw [mul_pow]
      simpa using h4
    exact (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg ((toEuclideanLin A).singularValues_nonneg _) (norm_nonneg _)) two_ne_zero).mp h6
  have h7 : ‖(1 - L₁ * L₁ᵀ) * (B - A) * R₁'‖ ≤ ‖B - A‖ := by
    refine (norm_mul_le_of_orthonormal hR₁' _).trans ?_
    exact hQL.norm_mul_le _
  rw [h2] at h1
  exact h1.trans ((norm_add_le _ _).trans (add_le_add h3 h7))

end SVD

/-! ### Principal angles: Lemmas D.3, D.4 and D.5 -/

section Angles

variable {α : Type*} [Fintype α] {k : ℕ}

/-- Definition 3.1: `‖sin Θ(U₁, U₂)‖₂ = (∑ᵢ sin² θᵢ)^{1/2}`, where the principal angles are
`θᵢ = arccos σᵢ(U₁ᵀ U₂)`. -/
def sinTheta (U₁ U₂ : Matrix α (Fin k) ℝ) : ℝ :=
  √(∑ i : Fin k, Real.sin (Real.arccos (sv (U₁ᵀ * U₂) i)) ^ 2)

lemma sv_transpose_mul_le_one {U₁ U₂ : Matrix α (Fin k) ℝ} (hU₁ : U₁ᵀ * U₁ = 1)
    (hU₂ : U₂ᵀ * U₂ = 1) (i : ℕ) : sv (U₁ᵀ * U₂) i ≤ 1 := by
  classical
  have h0 : sv (U₁ᵀ * U₂) i ≤ specNorm (U₁ᵀ * U₂) := by
    rw [specNorm_eq_singularValues_zero]
    exact (toEuclideanLin (U₁ᵀ * U₂)).singularValues_antitone (Nat.zero_le i)
  have h1 := specNorm_mul_le U₁ᵀ U₂
  rw [specNorm_transpose] at h1
  have h2 := specNorm_le_one_of_orthonormal hU₁
  have h3 := specNorm_le_one_of_orthonormal hU₂
  have h4 := specNorm_nonneg U₁
  have h5 := specNorm_nonneg U₂
  nlinarith

/-- `‖sin Θ(U₁, U₂)‖₂² = k - ‖U₁ᵀ U₂‖_F²`. -/
lemma sq_sinTheta {U₁ U₂ : Matrix α (Fin k) ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (hU₂ : U₂ᵀ * U₂ = 1) :
    sinTheta U₁ U₂ ^ 2 = k - ‖U₁ᵀ * U₂‖ ^ 2 := by
  classical
  have hsv : ∀ i : Fin k, Real.sin (Real.arccos (sv (U₁ᵀ * U₂) i)) ^ 2 =
      1 - sv (U₁ᵀ * U₂) i ^ 2 := fun i => by
    have h1 := sv_transpose_mul_le_one hU₁ hU₂ i
    have h0 := (toEuclideanLin (U₁ᵀ * U₂)).singularValues_nonneg i
    rw [Real.sin_arccos, Real.sq_sqrt]
    nlinarith
  have hsum : 0 ≤ ∑ i : Fin k, Real.sin (Real.arccos (sv (U₁ᵀ * U₂) i)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [sinTheta, Real.sq_sqrt hsum, Finset.sum_congr rfl fun i _ => hsv i,
    sq_norm_eq_sum_sq_singularValues, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, sv]
  rw [Fin.sum_univ_eq_sum_range (fun i => (toEuclideanLin (U₁ᵀ * U₂)).singularValues i ^ 2) k]

/-- `‖(1 - U₁ U₁ᵀ) U₂‖_F² = k - ‖U₁ᵀ U₂‖_F²`. -/
lemma sq_norm_compl_mul [DecidableEq α] {U₁ U₂ : Matrix α (Fin k) ℝ} (hU₁ : U₁ᵀ * U₁ = 1)
    (hU₂ : U₂ᵀ * U₂ = 1) : ‖(1 - U₁ * U₁ᵀ) * U₂‖ ^ 2 = k - ‖U₁ᵀ * U₂‖ ^ 2 := by
  classical
  have hQ := (isOrthProjMat_mul_transpose hU₁).compl
  rw [frob_sq_eq_trace, frob_sq_eq_trace, Matrix.transpose_mul, hQ.symm, Matrix.mul_assoc,
    ← Matrix.mul_assoc (1 - U₁ * U₁ᵀ), hQ.idem, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    trace_sub, hU₂, trace_one, Fintype.card_fin, Matrix.transpose_mul, transpose_transpose]
  simp only [Matrix.mul_assoc]

/-- The formula `‖sin Θ(U₁, U₂)‖₂ = ‖(1 - U₁ U₁ᵀ) U₂‖_F` behind Lemma D.3. -/
lemma sinTheta_eq_norm_compl_mul [DecidableEq α] {U₁ U₂ : Matrix α (Fin k) ℝ} (hU₁ : U₁ᵀ * U₁ = 1)
    (hU₂ : U₂ᵀ * U₂ = 1) : sinTheta U₁ U₂ = ‖(1 - U₁ * U₁ᵀ) * U₂‖ := by
  have h : sinTheta U₁ U₂ ^ 2 = ‖(1 - U₁ * U₁ᵀ) * U₂‖ ^ 2 := by
    rw [sq_sinTheta hU₁ hU₂, sq_norm_compl_mul hU₁ hU₂]
  exact (pow_left_inj₀ (Real.sqrt_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- The sine of the principal angles is symmetric. -/
lemma sinTheta_comm {U₁ U₂ : Matrix α (Fin k) ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (hU₂ : U₂ᵀ * U₂ = 1) :
    sinTheta U₁ U₂ = sinTheta U₂ U₁ := by
  have h : sinTheta U₁ U₂ ^ 2 = sinTheta U₂ U₁ ^ 2 := by
    rw [sq_sinTheta hU₁ hU₂, sq_sinTheta hU₂ hU₁, ← Frobenius.norm_transpose (U₁ᵀ * U₂),
      Matrix.transpose_mul, transpose_transpose]
  exact (pow_left_inj₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) two_ne_zero).mp h

omit [Fintype α] in
/-- Orthonormal columns that fill the space form an orthogonal matrix. -/
lemma add_mul_transpose_eq_one [Fintype α] [DecidableEq α] {K e : ℕ}
    (hn : Fintype.card α = K + e) {U₁ : Matrix α (Fin K) ℝ} {U₂ : Matrix α (Fin e) ℝ}
    (hU₁ : U₁ᵀ * U₁ = 1) (hU₂ : U₂ᵀ * U₂ = 1) (h0 : U₁ᵀ * U₂ = 0) :
    U₁ * U₁ᵀ + U₂ * U₂ᵀ = 1 := by
  have h0' : U₂ᵀ * U₁ = 0 := by
    have h := congrArg Matrix.transpose h0
    rwa [Matrix.transpose_mul, transpose_transpose, transpose_zero] at h
  have h1 : (fromCols U₁ U₂)ᵀ * fromCols U₁ U₂ = 1 := by
    rw [transpose_fromCols, fromRows_mul_fromCols, hU₁, hU₂, h0, h0', fromBlocks_one]
  have hc : Fintype.card (Fin K ⊕ Fin e) = Fintype.card α := by simp [hn]
  have h2 := (mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hc)).mp h1
  rwa [transpose_fromCols, fromCols_mul_fromRows] at h2

/-- **Lemma D.3** (arXiv 2602.06208).  For `U₁, U₂ ∈ ℝ^{n×K}` with orthonormal columns and
`U₁⊥ ∈ ℝ^{n×(n-K)}` with orthonormal columns, `U₁ᵀ U₁⊥ = 0`:
`‖U₁U₁ᵀ - U₂U₂ᵀ‖_F = √2 ‖sin Θ(U₁, U₂)‖₂ = √2 ‖U₁⊥ᵀ U₂‖_F`, with `sinTheta` the principal-angle
definition (Definition 3.1).  The library's `Curvature.norm_sub_sq_eq_of_trace` supplies the
projector half; the principal-angle form is new.  No difference from the paper. -/
theorem lemma_D_3 {K e : ℕ} (hn : Fintype.card α = K + e)
    {U₁ U₂ : Matrix α (Fin K) ℝ} {U₁p : Matrix α (Fin e) ℝ} (hU₁ : U₁ᵀ * U₁ = 1)
    (hU₂ : U₂ᵀ * U₂ = 1) (hp : U₁pᵀ * U₁p = 1) (h0 : U₁ᵀ * U₁p = 0) :
    ‖U₁ * U₁ᵀ - U₂ * U₂ᵀ‖ = √2 * sinTheta U₁ U₂ ∧ sinTheta U₁ U₂ = ‖U₁pᵀ * U₂‖ := by
  classical
  have hP := isOrthProjMat_mul_transpose hU₁
  have hQ := isOrthProjMat_mul_transpose hU₂
  have htr : trace (U₂ * U₂ᵀ) = trace (U₁ * U₁ᵀ) := by
    rw [trace_mul_comm, hU₂, trace_mul_comm, hU₁]
  have h1 := norm_sub_sq_eq_of_trace hQ hP htr
  rw [← Matrix.mul_assoc, Frobenius.norm_mul_transpose_of_orthonormal hU₂, norm_sub_rev,
    ← sinTheta_eq_norm_compl_mul hU₁ hU₂] at h1
  constructor
  · have h2 : (√2 * sinTheta U₁ U₂) ^ 2 = ‖U₁ * U₁ᵀ - U₂ * U₂ᵀ‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num), h1]
    exact ((pow_left_inj₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (norm_nonneg _)
      two_ne_zero).mp h2).symm
  · rw [sinTheta_eq_norm_compl_mul hU₁ hU₂, norm_transpose_mul_eq hp, leftProj_apply,
      ← add_mul_transpose_eq_one hn hU₁ hp h0, add_sub_cancel_left]

/-- **Lemma D.4** (arXiv 2602.06208).  Let `Q ∈ ℝ^{m×d}`, `U₁ ∈ ℝ^{m×K}` have orthonormal columns,
let `U₁⊥ ∈ ℝ^{m×(m-K)}` have orthonormal columns with `U₁ᵀ U₁⊥ = 0`, and let `Ũ ∈ ℝ^{d×f}` have
orthonormal columns orthogonal to the range of `Qᵀ U₁`.  Then `‖U₂ᵀ Q Ũ‖_F ≤ ‖U₂ᵀ U₁⊥‖_F`.
Difference from the paper: `Ũ` only needs orthonormal columns in `ℛ⊥(Qᵀ U₁)`, it need not be a basis
(the paper's `f = d - K`), and `U₂` is arbitrary. -/
theorem lemma_D_4 {m d K e f : ℕ} (hm : m = K + e) {Q : Matrix (Fin m) (Fin d) ℝ}
    {U₁ U₂ : Matrix (Fin m) (Fin K) ℝ} {U₁p : Matrix (Fin m) (Fin e) ℝ}
    {Ũ : Matrix (Fin d) (Fin f) ℝ} (hQ : Qᵀ * Q = 1) (hU₁ : U₁ᵀ * U₁ = 1)
    (hp : U₁pᵀ * U₁p = 1) (h0 : U₁ᵀ * U₁p = 0) (hŨ : Ũᵀ * Ũ = 1) (hŨ0 : (Qᵀ * U₁)ᵀ * Ũ = 0) :
    ‖U₂ᵀ * Q * Ũ‖ ≤ ‖U₂ᵀ * U₁p‖ := by
  have hc := add_mul_transpose_eq_one (by simpa using hm) hU₁ hp h0
  have h1 : U₁ᵀ * Q * Ũ = 0 := by
    rw [Matrix.transpose_mul, transpose_transpose] at hŨ0
    exact hŨ0
  have h2 : U₂ᵀ * Q * Ũ = U₂ᵀ * U₁p * (U₁pᵀ * Q * Ũ) := by
    calc U₂ᵀ * Q * Ũ = U₂ᵀ * (U₁ * U₁ᵀ + U₁p * U₁pᵀ) * Q * Ũ := by rw [hc, Matrix.mul_one]
      _ = U₂ᵀ * U₁ * (U₁ᵀ * Q * Ũ) + U₂ᵀ * U₁p * (U₁pᵀ * Q * Ũ) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_zero, zero_add]
  have h3 : specNorm (U₁pᵀ * Q * Ũ) ≤ 1 := by
    have e1 := specNorm_mul_le (U₁pᵀ * Q) Ũ
    have e2 := specNorm_mul_le U₁pᵀ Q
    rw [specNorm_transpose] at e2
    have a1 := specNorm_le_one_of_orthonormal hp
    have a2 := specNorm_le_one_of_orthonormal hQ
    have a3 := specNorm_le_one_of_orthonormal hŨ
    have b1 := specNorm_nonneg U₁p
    have b2 := specNorm_nonneg Q
    have b3 := specNorm_nonneg Ũ
    have c2 : specNorm (U₁pᵀ * Q) ≤ 1 := e2.trans (by nlinarith)
    have c3 := specNorm_nonneg (U₁pᵀ * Q)
    exact e1.trans (by nlinarith)
  rw [h2]
  refine (frob_mul_le' _ _).trans ?_
  have := norm_nonneg (U₂ᵀ * U₁p)
  nlinarith

/-- **Lemma D.5** (Wedin's sin-Θ theorem, arXiv 2602.06208, without the `√2` of the library's
`LeanDLRA.SinTheta.wedin_frobenius`, and for left and right subspaces).  If `A = L Σ Rᵀ` and
`Ã = L' Σ' R'ᵀ` are SVDs and `σ_{K+1}(A) < σ_K(Ã)`, then
`max {‖sin Θ(L₁(Ã), L₁(A))‖₂, ‖sin Θ(R₁(Ã), R₁(A))‖₂} ≤ ‖Ã - A‖_F / (σ_K(Ã) - σ_{K+1}(A))`.
Wedin's theorem is only cited in the paper; here it is proved. -/
theorem lemma_D_5 {m d K : ℕ} {A B : Matrix (Fin m) (Fin d) ℝ} {L L' : Matrix (Fin m) (Fin m) ℝ}
    {R R' : Matrix (Fin d) (Fin d) ℝ} (hA : IsSVD A L R) (hB : IsSVD B L' R') (hK : 0 < K)
    (hKm : K ≤ m) (hKd : K ≤ d) (hgap : sv A K < sv B (K - 1)) :
    max (sinTheta (topCols hKm L') (topCols hKm L)) (sinTheta (topCols hKd R') (topCols hKd R)) ≤
      ‖B - A‖ / (sv B (K - 1) - sv A K) := by
  have hLo := topCols_transpose_mul_self hKm hA.left
  have hLo' := topCols_transpose_mul_self hKm hB.left
  have hRo := topCols_transpose_mul_self hKd hA.right
  have hRo' := topCols_transpose_mul_self hKd hB.right
  have h1 := wedin_half hA hB hK hKm hKd
  have h2 := wedin_half hA.transpose hB.transpose hK hKd hKm
  simp only [sv, LeanDLRA.SVD.singularValues_transpose] at h2
  rw [← transpose_sub, Frobenius.norm_transpose] at h2
  rw [sinTheta_comm hLo' hLo, sinTheta_comm hRo' hRo, sinTheta_eq_norm_compl_mul hLo hLo',
    sinTheta_eq_norm_compl_mul hRo hRo']
  set x := ‖(1 - topCols hKm L * (topCols hKm L)ᵀ) * topCols hKm L'‖
  set y := ‖(1 - topCols hKd R * (topCols hKd R)ᵀ) * topCols hKd R'‖
  have hα := (toEuclideanLin A).singularValues_nonneg K
  have hδ : 0 < sv B (K - 1) - sv A K := sub_pos.mpr hgap
  have hx0 : 0 ≤ x := norm_nonneg _
  have hy0 : 0 ≤ y := norm_nonneg _
  simp only [sv] at hδ ⊢
  rw [le_div_iff₀ hδ]
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy]
    nlinarith
  · rw [max_eq_left hxy]
    nlinarith

end Angles

/-! ### Lemmas D.1 and D.2 -/

section EntrywiseLemmas

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Lemma D.1** (arXiv 2602.06208): `σ₁(A) ≤ σ₁(|A|)` for the entrywise absolute value `|A|`.
No difference from the paper. -/
theorem lemma_D_1 [DecidableEq β] (A : Matrix α β ℝ) : sv A 0 ≤ sv (A.map abs) 0 := by
  classical
  rw [sv, sv, ← specNorm_eq_singularValues_zero, ← specNorm_eq_singularValues_zero]
  exact specNorm_le_of_abs_le fun i j => le_rfl

/-- `σ₁(W) ≤ |ε|` for an `ε`-scaled semi-orthogonal `W`. -/
lemma specNorm_sq_le_of_scaled [DecidableEq β] {W : Matrix α β ℝ} {ε : ℝ}
    (hW : Wᵀ * W = ε ^ 2 • (1 : Matrix β β ℝ)) : specNorm W ^ 2 ≤ ε ^ 2 := by
  classical
  have h := specNorm_transpose_mul_self W
  rw [hW] at h
  have h1 : specNorm (ε ^ 2 • (1 : Matrix β β ℝ)) ≤ ε ^ 2 := by
    refine specNorm_le_of (sq_nonneg ε) fun x => ?_
    have : toEuclideanLin (ε ^ 2 • (1 : Matrix β β ℝ)) x = ε ^ 2 • x := by
      ext i
      simp
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ε)]
  nlinarith

/-- The spectral norm of `W X` for `ε`-scaled semi-orthogonal `W` and whitened `X`. -/
lemma specNorm_mul_sq_le {N : Type*} [Fintype N] [DecidableEq β] [DecidableEq N] {W : Matrix α β ℝ}
    {X : Matrix β N ℝ} {ε : ℝ} (hW : Wᵀ * W = ε ^ 2 • (1 : Matrix β β ℝ)) (hX : X * Xᵀ = 1) :
    specNorm (W * X) ^ 2 ≤ ε ^ 2 := by
  classical
  have h1 := specNorm_mul_le W X
  have h2 : specNorm X ≤ 1 := by
    have h3 : specNorm Xᵀ ≤ 1 :=
      specNorm_le_one_of_orthonormal (by rw [transpose_transpose]; exact hX)
    rwa [specNorm_transpose] at h3
  have h3 := specNorm_nonneg W
  have h4 := specNorm_nonneg (W * X)
  have h5 : specNorm (W * X) ≤ specNorm W := by nlinarith
  exact (pow_le_pow_left₀ h4 h5 2).trans (specNorm_sq_le_of_scaled hW)

/-- Row sums of `Z ⊙ Z` for `Z = W X`. -/
lemma sum_sq_row_mul_le {N : Type*} [Fintype N] [DecidableEq β] {W : Matrix α β ℝ}
    {X : Matrix β N ℝ} {ε : ℝ} (hW : Wᵀ * W = ε ^ 2 • (1 : Matrix β β ℝ)) (hX : X * Xᵀ = 1)
    (i : α) : ∑ j, (W * X) i j ^ 2 ≤ ε ^ 2 := by
  classical
  exact (sum_sq_row_le (W * X) i).trans (specNorm_mul_sq_le hW hX)

/-- Column sums of `Z ⊙ Z` for `Z = W X`. -/
lemma sum_sq_col_mul_le {N : Type*} [Fintype N] [DecidableEq β] {W : Matrix α β ℝ}
    {X : Matrix β N ℝ} {ε : ℝ} (hW : Wᵀ * W = ε ^ 2 • (1 : Matrix β β ℝ)) (hX : X * Xᵀ = 1)
    (j : N) : ∑ i, (W * X) i j ^ 2 ≤ ε ^ 2 := by
  classical
  exact (sum_sq_col_le (W * X) j).trans (specNorm_mul_sq_le hW hX)

/-- **Lemma D.2** (arXiv 2602.06208): if `Wᵀ W = ε² I` and `X Xᵀ = I`, then
`‖W X ⊙ W X‖_∞ ≤ ε²` and `‖W X ⊙ W X‖₁ ≤ ε²`.  No difference from the paper. -/
theorem lemma_D_2 {N : Type*} [Fintype N] [DecidableEq β] {W : Matrix α β ℝ} {X : Matrix β N ℝ}
    {ε : ℝ} (hW : Wᵀ * W = ε ^ 2 • (1 : Matrix β β ℝ)) (hX : X * Xᵀ = 1) :
    infNorm ((W * X) ⊙ (W * X)) ≤ ε ^ 2 ∧ oneNorm ((W * X) ⊙ (W * X)) ≤ ε ^ 2 := by
  refine ⟨infNorm_le (sq_nonneg ε) fun i => ?_, oneNorm_le (sq_nonneg ε) fun j => ?_⟩
  · simpa [Matrix.hadamard_apply, abs_mul_abs_self, sq] using sum_sq_row_mul_le hW hX i
  · simpa [Matrix.hadamard_apply, abs_mul_abs_self, sq] using sum_sq_col_mul_le hW hX j

end EntrywiseLemmas

/-! ### Scaling of singular values -/

section Scaling

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

lemma specNorm_smul_le (c : ℝ) (A : Matrix α β ℝ) : specNorm (c • A) ≤ |c| * specNorm A := by
  refine specNorm_le_of (mul_nonneg (abs_nonneg _) (specNorm_nonneg _)) fun x => ?_
  have e : toEuclideanLin (c • A) x = c • toEuclideanLin A x := by
    rw [map_smul, LinearMap.smul_apply]
  rw [e, norm_smul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_toEuclideanLin_le A x) (abs_nonneg c)

lemma specNorm_zero' : specNorm (0 : Matrix α β ℝ) = 0 :=
  le_antisymm (specNorm_le_of le_rfl fun x => by simp) (specNorm_nonneg _)

/-- `σ_i(A) = 0` as soon as `rank A ≤ i`. -/
lemma sv_eq_zero_of_rank_le {A : Matrix α β ℝ} {i : ℕ} (h : A.rank ≤ i) : sv A i = 0 := by
  classical
  have h1 := singularValues_le_specNorm_sub A A h
  rw [sub_self, specNorm_zero'] at h1
  exact le_antisymm h1 ((toEuclideanLin A).singularValues_nonneg i)

lemma sv_smul_le (c : ℝ) (A : Matrix α β ℝ) (i : ℕ) : sv (c • A) i ≤ |c| * sv A i := by
  classical
  have hr : (c • truncation A i).rank ≤ i := by
    have e : c • truncation A i = (c • (1 : Matrix α α ℝ)) * truncation A i := by
      rw [Matrix.smul_mul, Matrix.one_mul]
    rw [e]
    exact (Matrix.rank_mul_le_right _ _).trans (rank_truncation_le A i)
  have h1 := singularValues_le_specNorm_sub (c • A) (c • truncation A i) hr
  rw [← smul_sub] at h1
  refine h1.trans ((specNorm_smul_le c _).trans (le_of_eq ?_))
  rw [specNorm_sub_truncation]

/-- `σ_i(c A) = |c| σ_i(A)`. -/
lemma sv_smul (c : ℝ) (A : Matrix α β ℝ) (i : ℕ) : sv (c • A) i = |c| * sv A i := by
  refine le_antisymm (sv_smul_le c A i) ?_
  rcases eq_or_ne c 0 with rfl | hc
  · rw [abs_zero, zero_mul]
    exact (toEuclideanLin ((0 : ℝ) • A)).singularValues_nonneg i
  · have h1 := sv_smul_le c⁻¹ (c • A) i
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul, abs_inv] at h1
    have hc' : 0 < |c| := abs_pos.mpr hc
    calc |c| * sv A i ≤ |c| * (|c|⁻¹ * sv (c • A) i) := mul_le_mul_of_nonneg_left h1 hc'.le
      _ = _ := by field_simp

end Scaling

/-! ### The small-update subspace: the linear algebra of Lemma D.10 and Theorem D.11 -/

section Blocks

variable {m d : ℕ}

/-- A matrix with `r` rows and `n ≥ r + p` columns has `p` orthonormal kernel vectors. -/
lemma exists_orthonormal_ker {ρ : Type*} [Fintype ρ] {n p : ℕ} (hr : Fintype.card ρ + p ≤ n)
    (T : Matrix ρ (Fin n) ℝ) : ∃ V : Matrix (Fin n) (Fin p) ℝ, Vᵀ * V = 1 ∧ T * V = 0 := by
  classical
  have hS : p ≤ finrank ℝ (LinearMap.ker (toEuclideanLin T)) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (toEuclideanLin T)
    have h2 : finrank ℝ (LinearMap.range (toEuclideanLin T)) ≤
        finrank ℝ (EuclideanSpace ℝ ρ) := Submodule.finrank_le _
    simp only [finrank_euclideanSpace, Fintype.card_fin] at h1 h2
    omega
  obtain ⟨u, hu, hmem, -⟩ := exists_orthonormal_of_le (W := ⊥)
    (V := LinearMap.ker (toEuclideanLin T)) bot_le (by simp) hS
  refine ⟨ofCols u, transpose_ofCols_mul_ofCols hu, ?_⟩
  ext i j
  have h3 : toEuclideanLin T (u j) = 0 := hmem j
  have h4 := toEuclideanLin_coord T (u j) i
  rw [h3] at h4
  simpa [Matrix.mul_apply] using h4.symm

/-- The bases `V₂`, `U₂ = W₁(0) V₂ / ε` of Lemma D.10: `V₂` has `p` orthonormal columns in
`ℛ(R₁,₂(0)) ∩ ℛ⊥(W₁(0)ᵀ L₁,₁(0))`.  (The paper's proof uses `dim 𝒮 = p`; only `dim 𝒮 ≥ p`, which
holds for two subspaces of dimension `d - K`, is used here.) -/
lemma exists_small_update_basis {K p : ℕ} (hd : 2 * K + p ≤ d) {W₀ : Matrix (Fin m) (Fin d) ℝ}
    {ε : ℝ} (hε : 0 < ε) (hW₀ : W₀ᵀ * W₀ = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ))
    (L₁ : Matrix (Fin m) (Fin K) ℝ) (R₁ : Matrix (Fin d) (Fin K) ℝ) :
    ∃ (U₂ : Matrix (Fin m) (Fin p) ℝ) (V₂ : Matrix (Fin d) (Fin p) ℝ),
      U₂ᵀ * U₂ = 1 ∧ V₂ᵀ * V₂ = 1 ∧ W₀ * V₂ = ε • U₂ ∧ W₀ᵀ * U₂ = ε • V₂ ∧
        R₁ᵀ * V₂ = 0 ∧ L₁ᵀ * U₂ = 0 := by
  have hcard : Fintype.card (Fin K ⊕ Fin K) + p ≤ d := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨V₂, hV, hT⟩ := exists_orthonormal_ker hcard (fromRows R₁ᵀ (L₁ᵀ * W₀))
  rw [fromRows_mul, ← fromRows_zero] at hT
  obtain ⟨h1, h2⟩ := fromRows_inj hT
  have hε' : ε ≠ 0 := hε.ne'
  refine ⟨ε⁻¹ • (W₀ * V₂), V₂, ?_, hV, ?_, ?_, h1, ?_⟩
  · rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.transpose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc W₀ᵀ, hW₀, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, hV, smul_smul]
    have e : ε⁻¹ * ε⁻¹ * ε ^ 2 = 1 := by field_simp
    rw [e, one_smul]
  · rw [smul_smul, mul_inv_cancel₀ hε', one_smul]
  · rw [Matrix.mul_smul, ← Matrix.mul_assoc, hW₀, Matrix.smul_mul, Matrix.one_mul, smul_smul]
    congr 1
    field_simp
  · rw [Matrix.mul_smul, ← Matrix.mul_assoc, h2, smul_zero]

/-- A family with orthonormal columns can be completed by `q` further orthonormal columns. -/
lemma exists_orthonormal_compl {n q p : ℕ} (hn : p + q ≤ n) (U₂ : Matrix (Fin n) (Fin p) ℝ) :
    ∃ U₁ : Matrix (Fin n) (Fin q) ℝ, U₁ᵀ * U₁ = 1 ∧ U₁ᵀ * U₂ = 0 := by
  obtain ⟨U₁, h1, h2⟩ := exists_orthonormal_ker (p := q) (by simpa using hn) U₂ᵀ
  refine ⟨U₁, h1, ?_⟩
  have h3 := congrArg Matrix.transpose h2
  rwa [Matrix.transpose_mul, transpose_transpose, transpose_zero] at h3

/-- `‖Uᵀ B‖_F ≤ ‖sin Θ(U, U₀)‖₂` when `B` has orthonormal columns orthogonal to `U₀`. -/
lemma norm_transpose_mul_le_sinTheta {α : Type*} [Fintype α] {k p : ℕ}
    {U U₀ : Matrix α (Fin k) ℝ} (hU : Uᵀ * U = 1) (hU₀ : U₀ᵀ * U₀ = 1)
    {B : Matrix α (Fin p) ℝ} (hB : Bᵀ * B = 1) (h0 : U₀ᵀ * B = 0) :
    ‖Uᵀ * B‖ ≤ sinTheta U U₀ := by
  classical
  rw [sinTheta_comm hU hU₀, sinTheta_eq_norm_compl_mul hU₀ hU]
  have hQ := (isOrthProjMat_mul_transpose hU₀).compl
  have e : Uᵀ * B = ((1 - U₀ * U₀ᵀ) * U)ᵀ * B := by
    rw [Matrix.transpose_mul, hQ.symm, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_assoc, h0, Matrix.mul_zero, sub_zero]
  rw [e]
  refine (frob_mul_le' _ _).trans ?_
  rw [Frobenius.norm_transpose]
  have h1 := specNorm_le_one_of_orthonormal hB
  have h2 := norm_nonneg ((1 - U₀ * U₀ᵀ) * U)
  nlinarith

/-- `‖B‖_F² = p` for `B` with `p` orthonormal columns. -/
lemma sq_norm_of_orthonormal {α : Type*} [Fintype α] {p : ℕ} {B : Matrix α (Fin p) ℝ}
    (hB : Bᵀ * B = 1) : ‖B‖ ^ 2 = p := by
  rw [frob_sq_eq_trace, hB, trace_one, Fintype.card_fin]

/-- The alignment `A(t) = max {‖sin Θ(L₁,₁(t), L₁,₁(0))‖₂, ‖sin Θ(R₁,₁(t), R₁,₁(0))‖₂}` of
Theorem 3.5. -/
def alignment {K : ℕ} (hKm : K ≤ m) (hKd : K ≤ d) (L : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (R : ℕ → Matrix (Fin d) (Fin d) ℝ) (t : ℕ) : ℝ :=
  max (sinTheta (topCols hKm (L t)) (topCols hKm (L 0)))
    (sinTheta (topCols hKd (R t)) (topCols hKd (R 0)))

/-- The rate `ρ(t) = (σ₁²(G₁(t)) A²(t) / p + σ²_{K+1}(G₁(t)))^{1/2}` of Theorem 3.5. -/
def rho {K : ℕ} (hKm : K ≤ m) (hKd : K ≤ d) (L : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (R : ℕ → Matrix (Fin d) (Fin d) ℝ) (G : ℕ → Matrix (Fin m) (Fin d) ℝ) (p t : ℕ) : ℝ :=
  √(sv (G t) 0 ^ 2 * alignment hKm hKd L R t ^ 2 / p + sv (G t) K ^ 2)

/-- The estimate `‖G₁(t) V‖_F ≤ ρ(t) √p`, `‖G₁ᵀ(t) U‖_F ≤ ρ(t) √p` of Lemma D.10.  The bound holds
for arbitrary matrices `G t` with SVDs `L t`, `R t`, and arbitrary `V₂`, `U₂` as produced by
`exists_small_update_basis`. -/
lemma norm_mul_le_rho {K p : ℕ} (hp : 0 < p) (hKm : K ≤ m) (hKd : K ≤ d)
    {L : ℕ → Matrix (Fin m) (Fin m) ℝ} {R : ℕ → Matrix (Fin d) (Fin d) ℝ}
    {G : ℕ → Matrix (Fin m) (Fin d) ℝ} (hsvd : ∀ t, IsSVD (G t) (L t) (R t))
    {U₂ : Matrix (Fin m) (Fin p) ℝ} {V₂ : Matrix (Fin d) (Fin p) ℝ} (hU₂ : U₂ᵀ * U₂ = 1)
    (hV₂ : V₂ᵀ * V₂ = 1) (hR : (topCols hKd (R 0))ᵀ * V₂ = 0)
    (hL : (topCols hKm (L 0))ᵀ * U₂ = 0) (t : ℕ) :
    ‖G t * V₂‖ ≤ rho hKm hKd L R G p t * √p ∧ ‖(G t)ᵀ * U₂‖ ≤ rho hKm hKd L R G p t * √p := by
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  set a := alignment hKm hKd L R t with ha
  have hrho : (rho hKm hKd L R G p t * √p) ^ 2 =
      sv (G t) 0 ^ 2 * a ^ 2 + sv (G t) K ^ 2 * p := by
    have hnn : 0 ≤ sv (G t) 0 ^ 2 * a ^ 2 / p + sv (G t) K ^ 2 := by positivity
    rw [mul_pow, rho, Real.sq_sqrt hnn, Real.sq_sqrt hp'.le]
    field_simp
  have hbound : ∀ (x s : ℝ), 0 ≤ x → 0 ≤ s → s ≤ a →
      x ^ 2 ≤ sv (G t) 0 ^ 2 * s ^ 2 + sv (G t) K ^ 2 * p →
      x ≤ rho hKm hKd L R G p t * √p := fun x s hx hs hsa hxs => by
    have h1 : s ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hs hsa 2
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (sv (G t) 0))
    have h3 : x ^ 2 ≤ (rho hKm hKd L R G p t * √p) ^ 2 := by
      rw [hrho]
      linarith
    exact (pow_le_pow_iff_left₀ hx (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      two_ne_zero).mp h3
  constructor
  · have h1 := (hsvd t).norm_mul_sq_le hKd V₂
    have h2 := norm_transpose_mul_le_sinTheta (topCols_transpose_mul_self hKd (hsvd t).right)
      (topCols_transpose_mul_self hKd (hsvd 0).right) hV₂ hR
    rw [sq_norm_of_orthonormal hV₂] at h1
    refine hbound _ _ (norm_nonneg _) (norm_nonneg ((topCols hKd (R t))ᵀ * V₂))
      (h2.trans (le_max_right _ _)) h1
  · have h1 := (hsvd t).transpose.norm_mul_sq_le hKm U₂
    have h2 := norm_transpose_mul_le_sinTheta (topCols_transpose_mul_self hKm (hsvd t).left)
      (topCols_transpose_mul_self hKm (hsvd 0).left) hU₂ hL
    rw [sq_norm_of_orthonormal hU₂] at h1
    simp only [sv, LeanDLRA.SVD.singularValues_transpose] at h1
    refine hbound _ _ (norm_nonneg _) (norm_nonneg ((topCols hKm (L t))ᵀ * U₂))
      (h2.trans (le_max_left _ _)) h1

/-- The rotated weight `W̃₁ = Uᵀ W₁ V` of Theorem 3.5. -/
def tilde {α β : Type*} [Fintype α] [Fintype β] {m d : ℕ}
    (U : Matrix (Fin m) α ℝ) (V : Matrix (Fin d) β ℝ) (W : Matrix (Fin m) (Fin d) ℝ) :
    Matrix α β ℝ :=
  Uᵀ * W * V

lemma tilde_fromCols {α₁ α₂ β₁ β₂ : Type*} [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
    (U₁ : Matrix (Fin m) α₁ ℝ) (U₂ : Matrix (Fin m) α₂ ℝ) (V₁ : Matrix (Fin d) β₁ ℝ)
    (V₂ : Matrix (Fin d) β₂ ℝ) (W : Matrix (Fin m) (Fin d) ℝ) :
    tilde (fromCols U₁ U₂) (fromCols V₁ V₂) W =
      fromBlocks (U₁ᵀ * W * V₁) (U₁ᵀ * W * V₂) (U₂ᵀ * W * V₁) (U₂ᵀ * W * V₂) := by
  rw [tilde, transpose_fromCols, fromRows_mul, fromRows_mul_fromCols]

/-- One GD step `W' = W - η G`, seen through `A · B`. -/
lemma norm_mul_step {α β : Type*} [Fintype α] [Fintype β] {W W' G : Matrix (Fin m) (Fin d) ℝ}
    {η : ℝ} (hη : 0 ≤ η) (h : W' = W - η • G) (A : Matrix α (Fin m) ℝ)
    (B : Matrix (Fin d) β ℝ) : ‖A * W' * B - A * W * B‖ = η * ‖A * G * B‖ := by
  have e : A * W' * B - A * W * B = (-η) • (A * G * B) := by
    rw [h, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, neg_smul]
    abel
  rw [e, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hη]

lemma fromCols_orthogonal {α : Type*} [Fintype α] [DecidableEq α] {q p : ℕ}
    (hc : q + p = Fintype.card α) {U₁ : Matrix α (Fin q) ℝ} {U₂ : Matrix α (Fin p) ℝ}
    (hU₁ : U₁ᵀ * U₁ = 1) (hU₂ : U₂ᵀ * U₂ = 1) (h0 : U₁ᵀ * U₂ = 0) :
    (fromCols U₁ U₂)ᵀ * fromCols U₁ U₂ = 1 ∧ fromCols U₁ U₂ * (fromCols U₁ U₂)ᵀ = 1 := by
  have h0' : U₂ᵀ * U₁ = 0 := by
    have h := congrArg Matrix.transpose h0
    rwa [Matrix.transpose_mul, transpose_transpose, transpose_zero] at h
  have h1 : (fromCols U₁ U₂)ᵀ * fromCols U₁ U₂ = 1 := by
    rw [transpose_fromCols, fromRows_mul_fromCols, hU₁, hU₂, h0, h0', fromBlocks_one]
  have hc' : Fintype.card (Fin q ⊕ Fin p) = Fintype.card α := by simpa using hc
  exact ⟨h1, (mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hc')).mp h1⟩

/-- **The block decomposition behind Theorem D.11 of arXiv 2602.06208, for arbitrary gradient-like
sequences.**  For `W₀ᵀ W₀ = ε² I` and arbitrary `L₀`, `R₀` there are orthogonal `U = [U₁ U₂]`,
`V = [V₁ V₂]` (with `U₁ ∈ ℝ^{m×(m-p)}`, `V₁ ∈ ℝ^{d×2K}`, `U₂ ∈ ℝ^{m×p}`, `V₂ ∈ ℝ^{d×p}`), built
from `W₀`, `L₀`, `R₀` only, such that the off-diagonal blocks of `W̃(0) = Uᵀ W₀ V` vanish,
`‖W̃₄(0)‖_F / √p = ε`, and for **every** sequence `W(t + 1) = W(t) - η G(t)`, `W(0) = W₀`, with
SVDs `G(t) = L(t) Σ(t) R(t)ᵀ`, `L(0) = L₀`, `R(0) = R₀`, the increments of blocks 2, 3, 4 are at
most `η ρ(t) √p`.  This part of the theorem uses nothing about neural networks. -/
theorem exists_block_decomposition {K p : ℕ} (hd : 2 * K + p = d) (hmd : d ≤ m) (hp : 0 < p)
    (hKm : K ≤ m) (hKd : K ≤ d) {W₀ : Matrix (Fin m) (Fin d) ℝ} {ε : ℝ} (hε : 0 < ε)
    (hW₀ : W₀ᵀ * W₀ = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) (L₀ : Matrix (Fin m) (Fin m) ℝ)
    (R₀ : Matrix (Fin d) (Fin d) ℝ) :
    ∃ (U : Matrix (Fin m) (Fin (m - p) ⊕ Fin p) ℝ) (V : Matrix (Fin d) (Fin (2 * K) ⊕ Fin p) ℝ),
      Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ Vᵀ * V = 1 ∧ V * Vᵀ = 1 ∧
      (tilde U V W₀).toBlocks₁₂ = 0 ∧ (tilde U V W₀).toBlocks₂₁ = 0 ∧
      ‖(tilde U V W₀).toBlocks₂₂‖ / √p = ε ∧
      ∀ (η : ℝ) (W G : ℕ → Matrix (Fin m) (Fin d) ℝ) (L : ℕ → Matrix (Fin m) (Fin m) ℝ)
        (R : ℕ → Matrix (Fin d) (Fin d) ℝ), 0 ≤ η → W 0 = W₀ → L 0 = L₀ → R 0 = R₀ →
        (∀ t, W (t + 1) = W t - η • G t) → (∀ t, IsSVD (G t) (L t) (R t)) → ∀ t,
          W t = U * fromBlocks (tilde U V (W t)).toBlocks₁₁ (tilde U V (W t)).toBlocks₁₂
            (tilde U V (W t)).toBlocks₂₁ (tilde U V (W t)).toBlocks₂₂ * Vᵀ ∧
          ‖(tilde U V (W (t + 1))).toBlocks₁₂ - (tilde U V (W t)).toBlocks₁₂‖ / √p ≤
            η * rho hKm hKd L R G p t ∧
          ‖(tilde U V (W (t + 1))).toBlocks₂₁ - (tilde U V (W t)).toBlocks₂₁‖ / √p ≤
            η * rho hKm hKd L R G p t ∧
          ‖(tilde U V (W (t + 1))).toBlocks₂₂ - (tilde U V (W t)).toBlocks₂₂‖ / √p ≤
            η * rho hKm hKd L R G p t := by
  obtain ⟨U₂, V₂, hU₂, hV₂, h1, h2, hR, hL⟩ := exists_small_update_basis (p := p) (by omega) hε hW₀
    (topCols hKm L₀) (topCols hKd R₀)
  obtain ⟨U₁, hU₁, hU₁₂⟩ := exists_orthonormal_compl (q := m - p) (by omega) U₂
  obtain ⟨V₁, hV₁, hV₁₂⟩ := exists_orthonormal_compl (q := 2 * K) (by omega) V₂
  obtain ⟨hUU, hUU'⟩ := fromCols_orthogonal (by simp; omega) hU₁ hU₂ hU₁₂
  obtain ⟨hVV, hVV'⟩ := fromCols_orthogonal (by simp; omega) hV₁ hV₂ hV₁₂
  have hV₂₁ : V₂ᵀ * V₁ = 0 := by
    have h := congrArg Matrix.transpose hV₁₂
    rwa [Matrix.transpose_mul, transpose_transpose, transpose_zero] at h
  have hsqp : 0 < √(p : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp)
  have h13 : U₂ᵀ * W₀ = ε • V₂ᵀ := by
    have h := congrArg Matrix.transpose h2
    rwa [Matrix.transpose_mul, transpose_transpose, transpose_smul] at h
  refine ⟨fromCols U₁ U₂, fromCols V₁ V₂, hUU, hUU', hVV, hVV', ?_, ?_, ?_, ?_⟩
  · rw [tilde_fromCols, toBlocks_fromBlocks₁₂, Matrix.mul_assoc, h1, Matrix.mul_smul, hU₁₂,
      smul_zero]
  · rw [tilde_fromCols, toBlocks_fromBlocks₂₁, h13, Matrix.smul_mul, hV₂₁, smul_zero]
  · rw [tilde_fromCols, toBlocks_fromBlocks₂₂, h13, Matrix.smul_mul, hV₂, norm_smul,
      Real.norm_eq_abs, abs_of_pos hε]
    have h3 : ‖(1 : Matrix (Fin p) (Fin p) ℝ)‖ = √p := by
      have h4 := sq_norm_of_orthonormal (B := (1 : Matrix (Fin p) (Fin p) ℝ)) (by simp)
      rw [← h4, Real.sqrt_sq (norm_nonneg _)]
    rw [h3]
    field_simp
  · intro η W G L R hη hW0 hL0 hR0 hGD hsvd t
    rw [← hL0] at hL
    rw [← hR0] at hR
    obtain ⟨hGV, hGU⟩ := norm_mul_le_rho hp hKm hKd hsvd hU₂ hV₂ hR hL t
    set ρ := rho hKm hKd L R G p t
    have hρ := mul_le_mul_of_nonneg_left hGV hη
    have hρ' := mul_le_mul_of_nonneg_left hGU hη
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [fromBlocks_toBlocks, tilde, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ _
        (fromCols V₁ V₂)ᵀ, Matrix.mul_assoc _ (fromCols V₁ V₂), hVV', Matrix.mul_one,
        ← Matrix.mul_assoc, hUU', Matrix.one_mul]
    · rw [tilde_fromCols, tilde_fromCols, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₁₂,
        div_le_iff₀ hsqp, norm_mul_step hη (hGD t), Matrix.mul_assoc, mul_assoc]
      exact (mul_le_mul_of_nonneg_left (norm_transpose_mul_le hU₁ _) hη).trans hρ
    · rw [tilde_fromCols, tilde_fromCols, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₁,
        div_le_iff₀ hsqp, norm_mul_step hη (hGD t), mul_assoc]
      refine le_trans (mul_le_mul_of_nonneg_left ?_ hη) hρ'
      have e : U₂ᵀ * G t * V₁ = ((G t)ᵀ * U₂)ᵀ * V₁ := by
        rw [Matrix.transpose_mul, transpose_transpose]
      rw [e]
      refine (norm_mul_le_of_orthonormal hV₁ _).trans (le_of_eq ?_)
      exact Frobenius.norm_transpose _
    · rw [tilde_fromCols, tilde_fromCols, toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₂₂,
        div_le_iff₀ hsqp, norm_mul_step hη (hGD t), Matrix.mul_assoc, mul_assoc]
      exact (mul_le_mul_of_nonneg_left (norm_transpose_mul_le hU₂ _) hη).trans hρ

/-- Orthonormal columns extend to an orthogonal matrix having them as its first columns. -/
lemma exists_orthogonal_extension {n r : ℕ} (hr : r ≤ n) {U : Matrix (Fin n) (Fin r) ℝ}
    (hU : Uᵀ * U = 1) : ∃ Q : Matrix (Fin n) (Fin n) ℝ, Qᵀ * Q = 1 ∧ topCols hr Q = U := by
  obtain ⟨U₁, h1, h2⟩ := exists_orthonormal_compl (n := n) (q := n - r) (p := r) (by omega) U
  have h3 : Uᵀ * U₁ = 0 := by
    have h := congrArg Matrix.transpose h2
    rwa [Matrix.transpose_mul, transpose_transpose, transpose_zero] at h
  obtain ⟨hT, -⟩ := fromCols_orthogonal (by simp; omega) hU h1 h3
  have hn : n = r + (n - r) := by omega
  let e : Fin n ≃ Fin r ⊕ Fin (n - r) := (finCongr hn).trans finSumFinEquiv.symm
  refine ⟨(fromCols U U₁).submatrix id e, ?_, ?_⟩
  · rw [transpose_submatrix, ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, hT,
      Matrix.submatrix_one_equiv]
  · ext i j
    have h5 : finCongr hn (Fin.castLE hr j) = Fin.castAdd (n - r) j := by
      ext
      simp
    have he : e (Fin.castLE hr j) = Sum.inl j := by
      simp only [e, Equiv.trans_apply]
      rw [h5, finSumFinEquiv_symm_apply_castAdd]
    simp [topCols, he]

/-- **Every real matrix has an SVD** in the sense of `IsSVD` (the paper's `G₁(t) = L₁ Σ₁ R₁ᵀ`, arXiv
2602.06208, Appendix D.3.3), so the field `svd` of `Net.Run` only fixes a choice.  The library has
the thin SVD; this is its completion. -/
theorem exists_isSVD (A : Matrix (Fin m) (Fin d) ℝ) : ∃ L R, IsSVD A L R := by
  obtain ⟨U, V, σ, hU, hV, -, -, hσ, hA⟩ := LeanDLRA.SVD.exists_svd A rfl
  have hrm : A.rank ≤ m := by simpa using Matrix.rank_le_card_height A
  have hrd : A.rank ≤ d := by simpa using Matrix.rank_le_card_width A
  obtain ⟨L, hL, hLt⟩ := exists_orthogonal_extension hrm hU
  obtain ⟨R, hR, hRt⟩ := exists_orthogonal_extension hrd hV
  refine ⟨L, R, hL, hR, ?_⟩
  have hS : singularDiag A =
      topCols hrm (1 : Matrix (Fin m) (Fin m) ℝ) * diagonal σ *
        (topCols hrd (1 : Matrix (Fin d) (Fin d) ℝ))ᵀ := by
    ext i j
    have key : ∀ a : Fin A.rank, (topCols hrm (1 : Matrix (Fin m) (Fin m) ℝ) * diagonal σ) i a *
        (topCols hrd (1 : Matrix (Fin d) (Fin d) ℝ))ᵀ a j =
        if (i : ℕ) = a ∧ (j : ℕ) = a then σ a else 0 := fun a => by
      rw [Matrix.mul_diagonal, transpose_apply]
      simp only [topCols, submatrix_apply, id, Matrix.one_apply, Fin.ext_iff, Fin.val_castLE]
      by_cases h1 : (i : ℕ) = a <;> by_cases h2 : (j : ℕ) = a <;> simp [h1, h2]
    rw [Matrix.mul_apply, Finset.sum_congr rfl fun a _ => key a]
    simp only [singularDiag, Matrix.of_apply]
    by_cases hij : (i : ℕ) = j
    · simp only [hij, ↓reduceIte]
      by_cases hjr : (j : ℕ) < A.rank
      · rw [Finset.sum_eq_single (⟨j, hjr⟩ : Fin A.rank)]
        · simp [hσ]
        · intro b _ hb
          have hne : (j : ℕ) ≠ b := fun h => hb (Fin.ext h.symm)
          simp [hne]
        · simp
      · have h0 : sv A j = 0 := sv_eq_zero_of_rank_le (not_lt.mp hjr)
        rw [h0]
        refine (Finset.sum_eq_zero fun a _ => ?_).symm
        have hne : (j : ℕ) ≠ a := fun h => hjr (h ▸ a.2)
        simp [hne]
    · simp only [hij, ↓reduceIte]
      refine (Finset.sum_eq_zero fun a _ => ?_).symm
      have hne : ¬ ((i : ℕ) = a ∧ (j : ℕ) = a) := fun h => hij (h.1.trans h.2.symm)
      simp [hne]
  have h1 : L * topCols hrm (1 : Matrix (Fin m) (Fin m) ℝ) = U := by
    rw [← hLt]
    ext i j
    simp [topCols, Matrix.mul_apply, Matrix.one_apply]
  have h2 : R * topCols hrd (1 : Matrix (Fin d) (Fin d) ℝ) = V := by
    rw [← hRt]
    ext i j
    simp [topCols, Matrix.mul_apply, Matrix.one_apply]
  rw [hS]
  calc A = U * diagonal σ * Vᵀ := hA
    _ = _ := by
      rw [← h1, ← h2, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]

end Blocks

/-! ### One-dimensional facts about the activation -/

section Activation

lemma abs_sub_le_of_abs_deriv_le {f : ℝ → ℝ} {C : ℝ} (hf : Differentiable ℝ f)
    (h : ∀ x, |deriv f x| ≤ C) (x y : ℝ) : |f x - f y| ≤ C * |x - y| := by
  have h1 := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Set.univ) (C := C)
    (fun z _ => hf z) (fun z _ => by simpa using h z) convex_univ (Set.mem_univ y)
    (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using h1

/-- Taylor's theorem with remainder for a function with `f 0 = 0`:
`|f z - f'(0) z| ≤ (μ/2) z²` when `|f''| ≤ μ`. -/
lemma abs_sub_deriv_mul_le {f : ℝ → ℝ} {μ : ℝ} (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f)) (h0 : f 0 = 0) (hμ : ∀ x, |deriv (deriv f) x| ≤ μ)
    (z : ℝ) : |f z - deriv f 0 * z| ≤ μ / 2 * z ^ 2 := by
  have hμ0 : 0 ≤ μ := (abs_nonneg _).trans (hμ 0)
  have hL := abs_sub_le_of_abs_deriv_le hf' hμ
  let g : ℝ → ℝ := fun s => f (s * z) - deriv f 0 * (s * z)
  let g' : ℝ → ℝ := fun s => (deriv f (s * z) - deriv f 0) * z
  have hg : ∀ s, HasDerivAt g (g' s) s := fun s => by
    have h1 : HasDerivAt (fun s : ℝ => s * z) z s := by
      simpa using (hasDerivAt_id s).mul_const z
    have h2 : HasDerivAt (fun s : ℝ => f (s * z)) (deriv f (s * z) * z) s :=
      HasDerivAt.comp (h₂ := f) (h := fun s : ℝ => s * z) s (hf (s * z)).hasDerivAt h1
    have h3 := h2.sub (h1.const_mul (deriv f 0))
    convert h3 using 1
    simp only [g']
    ring
  let B : ℝ → ℝ := fun s => μ / 2 * (s ^ 2 * z ^ 2)
  let B' : ℝ → ℝ := fun s => μ * s * z ^ 2
  have hB : ∀ s, HasDerivAt B (B' s) s := fun s => by
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := by
      simpa using hasDerivAt_pow 2 s
    have h2 := (h1.mul_const (z ^ 2)).const_mul (μ / 2)
    convert h2 using 1
    simp only [B']
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := g) (f' := g') (a := 0)
    (b := 1) (B := B) (B' := B')
    (fun s _ => (hg s).continuousAt.continuousWithinAt)
    (fun s _ => (hg s).hasDerivWithinAt) (by simp [g, B, h0]) hB
    (fun s hs => by
      have h1 := hL (s * z) 0
      have hs0 : 0 ≤ s := hs.1
      rw [sub_zero, abs_mul, abs_of_nonneg hs0] at h1
      simp only [g', B', Real.norm_eq_abs, abs_mul]
      calc |deriv f (s * z) - deriv f 0| * |z| ≤ μ * (s * |z|) * |z| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = μ * s * z ^ 2 := by rw [← sq_abs z]; ring)
    (Set.right_mem_Icc.mpr zero_le_one)
  simpa [g, B, Real.norm_eq_abs] using key

/-- The paper's `(1 - Θ(η))^{Θ(t)}`, that is `(1 - c₁ η)^{c₂ t}`, is the `t`-th power of
`q = (1 - c₁ η)^{c₂}`. -/
lemma rpow_decay_eq_pow {a : ℝ} (ha : 0 ≤ a) (c₂ : ℝ) (t : ℕ) :
    a ^ (c₂ * t) = (a ^ c₂) ^ t := by
  rw [Real.rpow_mul ha, Real.rpow_natCast]

/-- The decay factor `q = (1 - c₁ η)^{c₂}` lies in `[0, 1)`. -/
lemma decay_factor_mem {c₁ c₂ η : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hη : 0 < η)
    (h1 : c₁ * η < 1) : 0 ≤ (1 - c₁ * η) ^ c₂ ∧ (1 - c₁ * η) ^ c₂ < 1 :=
  ⟨Real.rpow_nonneg (by linarith) _,
    Real.rpow_lt_one (by linarith) (by linarith [mul_pos hc₁ hη]) hc₂⟩

end Activation

/-! ### Frobenius estimates for Hadamard products -/

section Hadamard

variable {α β : Type*} [Fintype α] [Fintype β]

lemma norm_hadamard_le {A B : Matrix α β ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, |B i j| ≤ c) :
    ‖A ⊙ B‖ ≤ c * ‖A‖ := by
  have hsq : ‖A ⊙ B‖ ^ 2 ≤ (c * ‖A‖) ^ 2 := by
    rw [mul_pow, Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Matrix.hadamard_apply, mul_pow, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs (B i j)]
    exact pow_le_pow_left₀ (abs_nonneg _) (h i j) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

lemma norm_of_abs_le_mul {A B : Matrix α β ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, |A i j| ≤ c * |B i j|) : ‖A‖ ≤ c * ‖B‖ := by
  have hsq : ‖A‖ ^ 2 ≤ (c * ‖B‖) ^ 2 := by
    rw [mul_pow, Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 := pow_le_pow_left₀ (abs_nonneg _) (h i j) 2
    rwa [sq_abs, mul_pow, sq_abs] at h1
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

end Hadamard

/-! ### The two-layer network -/

section Network

variable {m d N K : ℕ}

/-- Data of the two-layer network `f(X) = W₂ φ(W₁ X)` with fixed second layer (Assumption 3.3):
activation `φ`, second layer `W₂ ∈ ℝ^{K×m}`, inputs `X ∈ ℝ^{d×N}`, labels `Y ∈ ℝ^{K×N}`. -/
structure Net (m d N K : ℕ) where
  /-- The activation function. -/
  φ : ℝ → ℝ
  /-- The fixed second layer. -/
  W₂ : Matrix (Fin K) (Fin m) ℝ
  /-- The input data. -/
  X : Matrix (Fin d) (Fin N) ℝ
  /-- The labels. -/
  Y : Matrix (Fin K) (Fin N) ℝ

namespace Net

variable (net : Net m d N K)

/-- The residual `Δ₂(W₁) = W₂ φ(W₁ X) - Y`, with `φ` applied entrywise. -/
def residual (W₁ : Matrix (Fin m) (Fin d) ℝ) : Matrix (Fin K) (Fin N) ℝ :=
  net.W₂ * (W₁ * net.X).map net.φ - net.Y

/-- The squared error loss `ℒ(W₁) = ½ ‖W₂ φ(W₁ X) - Y‖_F²`, eq. (4). -/
def loss (W₁ : Matrix (Fin m) (Fin d) ℝ) : ℝ := 1 / 2 * ‖net.residual W₁‖ ^ 2

/-- The gradient `G₁(W₁) = ((W₂ᵀ Δ₂) ⊙ φ'(W₁ X)) Xᵀ`, eq. (12); see `Net.hasGradientAt_loss`. -/
def grad (W₁ : Matrix (Fin m) (Fin d) ℝ) : Matrix (Fin m) (Fin d) ℝ :=
  ((net.W₂ᵀ * net.residual W₁) ⊙ (W₁ * net.X).map (deriv net.φ)) * net.Xᵀ

/-- The matrix `W₂ᵀ Y Xᵀ`, of rank at most `K`, that governs the small-initialisation gradient. -/
def target : Matrix (Fin m) (Fin d) ℝ := net.W₂ᵀ * net.Y * net.Xᵀ

/-- The local Lipschitz constant `γ_L = μ M ‖W₂‖₁ + β² σ₁²(W₂)` of Lemma D.7. -/
def gammaL (β μ M : ℝ) : ℝ := μ * M * oneNorm net.W₂ + β ^ 2 * sv net.W₂ 0 ^ 2

/-- The radius `r(ε)` of Lemma D.8. -/
def rEps (β μ ε : ℝ) (W₀ : Matrix (Fin m) (Fin d) ℝ) : ℝ :=
  ε * deriv net.φ 0 * sv net.W₂ 0 ^ 2 * (deriv net.φ 0 + μ / 2 * ε) +
    μ * maxNorm (W₀ * net.X) * sv net.W₂ 0 * (β * sv net.W₂ 0 * √d * ε + ‖net.Y‖)

/-- Assumptions 3.2 and 3.3 on the data and the activation: `X` is whitened, `φ(0) = 0`,
`|φ'| ≤ β`, `|φ''| ≤ μ`.  The dimension conditions `K < d/2`, `m ≥ d` are separate hypotheses of the
theorems.  The assumption that `W₂` has full row rank is not needed anywhere. -/
structure Assumptions (β μ : ℝ) : Prop where
  whitened : net.X * net.Xᵀ = 1
  φ_zero : net.φ 0 = 0
  φ_diff : Differentiable ℝ net.φ
  φ'_diff : Differentiable ℝ (deriv net.φ)
  φ'_bound : ∀ x, |deriv net.φ x| ≤ β
  φ''_bound : ∀ x, |deriv (deriv net.φ) x| ≤ μ

variable {net}

lemma Assumptions.β_nonneg {β μ : ℝ} (h : net.Assumptions β μ) : 0 ≤ β :=
  (abs_nonneg _).trans (h.φ'_bound 0)

lemma Assumptions.μ_nonneg {β μ : ℝ} (h : net.Assumptions β μ) : 0 ≤ μ :=
  (abs_nonneg _).trans (h.φ''_bound 0)

lemma Assumptions.specNorm_X {β μ : ℝ} (h : net.Assumptions β μ) : specNorm net.X ≤ 1 := by
  have h3 : specNorm net.Xᵀ ≤ 1 :=
    specNorm_le_one_of_orthonormal (by rw [transpose_transpose]; exact h.whitened)
  rwa [specNorm_transpose] at h3

lemma Assumptions.norm_mul_X {β μ : ℝ} (h : net.Assumptions β μ) (A : Matrix (Fin m) (Fin d) ℝ) :
    ‖A * net.X‖ = ‖A‖ := by
  have h1 := Frobenius.norm_mul_transpose_of_orthonormal (V := net.Xᵀ)
    (by rw [transpose_transpose]; exact h.whitened) A
  rwa [transpose_transpose] at h1

lemma Assumptions.norm_mul_Xt {β μ : ℝ} (h : net.Assumptions β μ) (A : Matrix (Fin m) (Fin N) ℝ) :
    ‖A * net.Xᵀ‖ ≤ ‖A‖ := by
  have h1 := frob_mul_le' A net.Xᵀ
  rw [specNorm_transpose] at h1
  have h2 := norm_nonneg A
  have h3 := h.specNorm_X
  nlinarith

variable (net)

/-- The entrywise formula for the loss. -/
lemma loss_eq (W₁ : Matrix (Fin m) (Fin d) ℝ) :
    net.loss W₁ = 1 / 2 * ∑ k, ∑ n, net.residual W₁ k n ^ 2 := by
  rw [loss, Frobenius.norm_sq_eq_sum]

/-- The entries of the residual. -/
lemma residual_apply (W₁ : Matrix (Fin m) (Fin d) ℝ) (k : Fin K) (n : Fin N) :
    net.residual W₁ k n = ∑ i, net.W₂ k i * net.φ ((W₁ * net.X) i n) - net.Y k n := by
  simp [residual, Matrix.mul_apply]

/-- The evaluation of a matrix at a position, as a continuous linear map for the Frobenius norm. -/
def evalCLM {α β : Type*} [Fintype α] [Fintype β] (i : α) (j : β) : Matrix α β ℝ →L[ℝ] ℝ :=
  LinearMap.mkContinuous (Matrix.entryLinearMap ℝ ℝ i j) 1 fun A => by
    simpa using Frobenius.abs_apply_le_norm A i j

/-- **Eqs. (11)–(12)** (arXiv 2602.06208, Appendix D.2): `G₁` is the gradient of the loss with
respect to the Frobenius inner product.  No difference from the paper. -/
theorem hasGradientAt_loss (hφ : Differentiable ℝ net.φ) (W : Matrix (Fin m) (Fin d) ℝ) :
    HasGradientAt net.loss (net.grad W) W := by
  let ℓ : Fin m → Fin N → Matrix (Fin m) (Fin d) ℝ →L[ℝ] ℝ := fun i n =>
    (evalCLM i n).comp (Frobenius.rightMulCLM net.X)
  have hℓ : ∀ i n (W' : Matrix (Fin m) (Fin d) ℝ), ℓ i n W' = (W' * net.X) i n := fun _ _ _ => rfl
  have h1 : ∀ i n, HasFDerivAt (fun W' => net.φ (ℓ i n W'))
      (deriv net.φ (ℓ i n W) • ℓ i n) W := fun i n =>
    HasDerivAt.comp_hasFDerivAt W (hφ _).hasDerivAt (ℓ i n).hasFDerivAt
  have h2 : ∀ k n, HasFDerivAt (fun W' => net.residual W' k n)
      (∑ i, net.W₂ k i • deriv net.φ (ℓ i n W) • ℓ i n) W := fun k n => by
    have h3 := (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (h1 i n).const_mul (net.W₂ k i)).sub_const (net.Y k n)
    refine h3.congr_of_eventuallyEq (Eventually.of_forall fun W' => ?_)
    simp only [residual_apply, hℓ]
  have h5 := (HasFDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) fun n _ => (h2 k n).pow 2).const_mul (1 / 2 : ℝ)
  have h6 : net.loss = fun y => 1 / 2 * ∑ k, ∑ n, net.residual y k n ^ 2 := funext net.loss_eq
  rw [h6, hasGradientAt_iff_hasFDerivAt]
  refine h5.congr_fderiv ?_
  ext H
  rw [InnerProductSpace.toDual_apply_apply, grad, Frobenius.inner_mul_right, transpose_transpose,
    Frobenius.inner_def]
  simp only [_root_.smul_apply, FunLike.coe_sum, Finset.sum_apply, smul_eq_mul,
    Matrix.hadamard_apply, map_apply, hℓ, Matrix.mul_apply (M := net.W₂ᵀ), transpose_apply]
  let T : Fin K → Fin N → Fin m → ℝ := fun k n i =>
    net.residual W k n * (net.W₂ k i * (deriv net.φ ((W * net.X) i n) * (H * net.X) i n))
  have e : ∀ x : ℝ, (2 : ℕ) • x ^ (2 - 1) = 2 * x := fun x => by norm_num
  calc _ = ∑ k, ∑ n, ∑ i, T k n i := by
        simp only [Finset.mul_sum, e]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun n _ =>
          Finset.sum_congr rfl fun i _ => ?_
        simp only [T]
        ring
    _ = ∑ i, ∑ n, ∑ k, T k n i := by
        rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm, Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
        simp only [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun n _ =>
          Finset.sum_congr rfl fun k _ => ?_
        simp only [T]
        ring

/-- `√(2 ℓ) = ‖Δ₂‖_F`. -/
lemma sqrt_two_mul_loss (W₁ : Matrix (Fin m) (Fin d) ℝ) :
    √(2 * net.loss W₁) = ‖net.residual W₁‖ := by
  rw [loss, ← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul,
    Real.sqrt_sq (norm_nonneg _)]

lemma specNorm_W₂ : specNorm net.W₂ = sv net.W₂ 0 := specNorm_eq_singularValues_zero _

lemma specNorm_W₂t : specNorm net.W₂ᵀ = sv net.W₂ 0 := by
  rw [specNorm_transpose, specNorm_W₂]

variable {net}

/-- **Lemma D.6** (arXiv 2602.06208): `‖G₁(W₁)‖_F ≤ β σ₁(W₂) √(2 ℒ(W₁))`, stated for every `W₁` (the
paper's `W₁(t)`).  No difference from the paper. -/
theorem lemma_D_6 {β μ : ℝ} (h : net.Assumptions β μ) (W₁ : Matrix (Fin m) (Fin d) ℝ) :
    ‖net.grad W₁‖ ≤ β * sv net.W₂ 0 * √(2 * net.loss W₁) := by
  rw [sqrt_two_mul_loss, grad]
  refine (h.norm_mul_Xt _).trans ?_
  refine (norm_hadamard_le h.β_nonneg fun i j => h.φ'_bound _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ h.β_nonneg
  rw [← specNorm_W₂t]
  exact frob_mul_le _ _

/-- The entries of `W₂ᵀ Δ₂` are bounded by `‖W₂‖₁ ‖Δ₂‖_max`. -/
lemma abs_transpose_mul_le (W₂ : Matrix (Fin K) (Fin m) ℝ) (D : Matrix (Fin K) (Fin N) ℝ)
    (i : Fin m) (n : Fin N) : |(W₂ᵀ * D) i n| ≤ oneNorm W₂ * maxNorm D := by
  rw [Matrix.mul_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k, |W₂ᵀ i k * D k n| ≤ ∑ k, |W₂ k i| * maxNorm D := Finset.sum_le_sum fun k _ => by
        rw [abs_mul, transpose_apply]
        exact mul_le_mul_of_nonneg_left (abs_le_maxNorm D k n) (abs_nonneg _)
    _ = (∑ k, |W₂ k i|) * maxNorm D := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_abs_le_oneNorm W₂ i) (maxNorm_nonneg D)

/-- **Lemma D.7** (arXiv 2602.06208): the gradient is Lipschitz with constant `γ_L` on
`ℳ = {W₁ : ‖Δ₂(W₁)‖_max ≤ M}`.  Difference from the paper: only `W₁` has to lie in `ℳ` (and the
scaled semi-orthogonal `W₁(0)` of the paper's statement plays no role in its proof). -/
theorem lemma_D_7 {β μ M : ℝ} (h : net.Assumptions β μ) {W W' : Matrix (Fin m) (Fin d) ℝ}
    (hM : maxNorm (net.residual W) ≤ M) :
    ‖net.grad W - net.grad W'‖ ≤ net.gammaL β μ M * ‖W - W'‖ := by
  have hβ := h.β_nonneg
  have hμ := h.μ_nonneg
  have hM0 : 0 ≤ M := (maxNorm_nonneg _).trans hM
  have hσ : 0 ≤ sv net.W₂ 0 := (toEuclideanLin net.W₂).singularValues_nonneg 0
  have hone := oneNorm_nonneg net.W₂
  set Z := W * net.X with hZ
  set Z' := W' * net.X with hZ'
  set A := net.W₂ᵀ * net.residual W with hA
  set A' := net.W₂ᵀ * net.residual W' with hA'
  have hZZ : ‖Z - Z'‖ = ‖W - W'‖ := by rw [hZ, hZ', ← Matrix.sub_mul, h.norm_mul_X]
  have e : net.grad W - net.grad W' =
      (A ⊙ (Z.map (deriv net.φ) - Z'.map (deriv net.φ)) + (A - A') ⊙ Z'.map (deriv net.φ)) *
        net.Xᵀ := by
    simp only [grad]
    rw [← hZ, ← hZ', ← hA, ← hA', ← Matrix.sub_mul]
    congr 1
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.hadamard_apply, map_apply]
    ring
  have ht1 : ‖A ⊙ (Z.map (deriv net.φ) - Z'.map (deriv net.φ))‖ ≤
      (μ * M * oneNorm net.W₂) * ‖Z - Z'‖ := by
    refine norm_of_abs_le_mul (by positivity) fun i j => ?_
    simp only [Matrix.hadamard_apply, Matrix.sub_apply, map_apply, abs_mul]
    have h1 := abs_sub_le_of_abs_deriv_le h.φ'_diff h.φ''_bound (Z i j) (Z' i j)
    have h2 : |A i j| ≤ oneNorm net.W₂ * M :=
      (abs_transpose_mul_le _ _ i j).trans (mul_le_mul_of_nonneg_left hM hone)
    calc |A i j| * |deriv net.φ (Z i j) - deriv net.φ (Z' i j)|
        ≤ (oneNorm net.W₂ * M) * (μ * |Z i j - Z' i j|) :=
          mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hdiff : A - A' = net.W₂ᵀ * net.W₂ * (Z.map net.φ - Z'.map net.φ) := by
    simp only [hA, hA', residual]
    rw [← Matrix.mul_sub, sub_sub_sub_cancel_right, ← Matrix.mul_sub, Matrix.mul_assoc]
  have ht2 : ‖(A - A') ⊙ Z'.map (deriv net.φ)‖ ≤ (β ^ 2 * sv net.W₂ 0 ^ 2) * ‖Z - Z'‖ := by
    have h1 := norm_hadamard_le (A := A - A') (B := Z'.map (deriv net.φ)) hβ
      fun i j => h.φ'_bound _
    have h2 : ‖Z.map net.φ - Z'.map net.φ‖ ≤ β * ‖Z - Z'‖ := by
      refine norm_of_abs_le_mul hβ fun i j => ?_
      simpa using abs_sub_le_of_abs_deriv_le h.φ_diff h.φ'_bound (Z i j) (Z' i j)
    have h3 : ‖A - A'‖ ≤ sv net.W₂ 0 * sv net.W₂ 0 * ‖Z.map net.φ - Z'.map net.φ‖ := by
      rw [hdiff]
      refine (frob_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      refine (specNorm_mul_le _ _).trans ?_
      rw [specNorm_W₂t, specNorm_W₂]
    calc _ ≤ β * ‖A - A'‖ := h1
      _ ≤ β * (sv net.W₂ 0 * sv net.W₂ 0 * (β * ‖Z - Z'‖)) := by
          refine mul_le_mul_of_nonneg_left (h3.trans ?_) hβ
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  rw [e, gammaL, add_mul, ← hZZ]
  exact (h.norm_mul_Xt _).trans ((norm_add_le _ _).trans (add_le_add ht1 ht2))

/-- `‖W₀‖_F = ε √d` for an `ε`-scaled semi-orthogonal matrix. -/
lemma norm_of_scaled {ε : ℝ} (hε : 0 ≤ ε) {W₀ : Matrix (Fin m) (Fin d) ℝ}
    (hW₀ : W₀ᵀ * W₀ = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) : ‖W₀‖ = ε * √d := by
  have h1 : ‖W₀‖ ^ 2 = (ε * √d) ^ 2 := by
    rw [frob_sq_eq_trace, hW₀, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1

lemma specNorm_Z_le {β μ ε : ℝ} (h : net.Assumptions β μ) (hε : 0 ≤ ε)
    {W₀ : Matrix (Fin m) (Fin d) ℝ}
    (hW₀ : W₀ᵀ * W₀ = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) : specNorm (W₀ * net.X) ≤ ε :=
  (pow_le_pow_iff_left₀ (specNorm_nonneg _) hε two_ne_zero).mp
    (specNorm_mul_sq_le hW₀ h.whitened)

/-- The Taylor expansion in the proof of Lemma D.8: `σ₁(φ(W₁(0) X)) ≤ φ'(0) ε + (μ/2) ε²`. -/
lemma specNorm_map_le {β μ ε : ℝ} (h : net.Assumptions β μ) (hc : 0 ≤ deriv net.φ 0)
    (hε : 0 ≤ ε) {W₀ : Matrix (Fin m) (Fin d) ℝ}
    (hW₀ : W₀ᵀ * W₀ = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    specNorm ((W₀ * net.X).map net.φ) ≤ deriv net.φ 0 * ε + μ / 2 * ε ^ 2 := by
  set Z := W₀ * net.X with hZ
  set c := deriv net.φ 0 with hcdef
  have hμ := h.μ_nonneg
  have hb : 0 ≤ μ / 2 * ε ^ 2 := by positivity
  have hentry : ∀ i j, |(Z.map net.φ - c • Z) i j| ≤ μ / 2 * Z i j ^ 2 := fun i j => by
    simpa [Matrix.sub_apply] using
      abs_sub_deriv_mul_le h.φ_diff h.φ'_diff h.φ_zero h.φ''_bound (Z i j)
  have hR : specNorm (Z.map net.φ - c • Z) ≤ μ / 2 * ε ^ 2 := by
    have h1 := specNorm_le_sqrt_of_schur (A := Z.map net.φ - c • Z) hb hb
      (fun i => (Finset.sum_le_sum fun j _ => hentry i j).trans ?_)
      (fun j => (Finset.sum_le_sum fun i _ => hentry i j).trans ?_)
    · rwa [Real.sqrt_mul_self hb] at h1
    · rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_sq_row_mul_le hW₀ h.whitened i) (by positivity)
    · rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_sq_col_mul_le hW₀ h.whitened j) (by positivity)
  have e : Z.map net.φ = c • Z + (Z.map net.φ - c • Z) := (add_sub_cancel _ _).symm
  rw [e]
  refine (WeylSingular.specNorm_add_le _ _).trans (add_le_add ?_ hR)
  refine (specNorm_smul_le _ _).trans ?_
  rw [abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (specNorm_Z_le h hε hW₀) hc

lemma norm_residual_le {β μ ε : ℝ} (h : net.Assumptions β μ) (hε : 0 ≤ ε)
    {W₀ : Matrix (Fin m) (Fin d) ℝ}
    (hW₀ : W₀ᵀ * W₀ = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    ‖net.residual W₀‖ ≤ sv net.W₂ 0 * (β * (ε * √d)) + ‖net.Y‖ := by
  have hσ : 0 ≤ sv net.W₂ 0 := (toEuclideanLin net.W₂).singularValues_nonneg 0
  have h1 : ‖(W₀ * net.X).map net.φ‖ ≤ β * ‖W₀ * net.X‖ := by
    refine norm_of_abs_le_mul h.β_nonneg fun i j => ?_
    have h2 := abs_sub_le_of_abs_deriv_le h.φ_diff h.φ'_bound ((W₀ * net.X) i j) 0
    simpa [h.φ_zero] using h2
  rw [h.norm_mul_X, norm_of_scaled hε hW₀] at h1
  refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
  refine (frob_mul_le _ _).trans ?_
  rw [specNorm_W₂]
  exact mul_le_mul_of_nonneg_left h1 hσ

/-- The rank bound `rank (W₂ᵀ Y Xᵀ) ≤ K`. -/
lemma rank_target_le (net : Net m d N K) : net.target.rank ≤ K := by
  have h1 : net.target = net.W₂ᵀ * (net.Y * net.Xᵀ) := Matrix.mul_assoc _ _ _
  rw [h1]
  refine (Matrix.rank_mul_le_left _ _).trans ?_
  simpa using Matrix.rank_le_card_width net.W₂ᵀ

/-- The perturbation estimate at the heart of Lemma D.8: `G₁(0) = -φ'(0) W₂ᵀ Y Xᵀ + E` with
`‖E‖₂ ≤ r(ε)`. -/
lemma exists_grad_eq_add {β μ ε : ℝ} (h : net.Assumptions β μ) (hc : 0 ≤ deriv net.φ 0)
    (hε : 0 ≤ ε) {W₀ : Matrix (Fin m) (Fin d) ℝ}
    (hW₀ : W₀ᵀ * W₀ = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    ∃ E, net.grad W₀ = (-deriv net.φ 0) • net.target + E ∧ specNorm E ≤ net.rEps β μ ε W₀ := by
  have hμ := h.μ_nonneg
  have hβ := h.β_nonneg
  have hσ : 0 ≤ sv net.W₂ 0 := (toEuclideanLin net.W₂).singularValues_nonneg 0
  set Z := W₀ * net.X with hZ
  set c := deriv net.φ 0 with hcdef
  set A := net.W₂ᵀ * net.residual W₀ with hA
  set Q := net.W₂ᵀ * net.W₂ * Z.map net.φ * net.Xᵀ with hQ
  set P := A ⊙ Z.map (fun z => deriv net.φ z - c) with hP
  have hmax := maxNorm_nonneg Z
  refine ⟨c • Q + P * net.Xᵀ, ?_, ?_⟩
  · have e2 : A ⊙ Z.map (deriv net.φ) = c • A + P := by
      ext i j
      simp only [hP, Matrix.hadamard_apply, Matrix.add_apply, Matrix.smul_apply, map_apply,
        smul_eq_mul]
      ring
    have e3 : A * net.Xᵀ = Q - net.target := by
      simp only [hA, hQ, residual, target, hZ, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [grad, ← hZ, ← hA, e2, Matrix.add_mul, Matrix.smul_mul, e3, smul_sub, neg_smul]
    abel
  · have hQb : specNorm Q ≤ sv net.W₂ 0 * sv net.W₂ 0 * (c * ε + μ / 2 * ε ^ 2) := by
      have h1 : specNorm Q ≤ specNorm (net.W₂ᵀ * net.W₂ * Z.map net.φ) := by
        have h2 := specNorm_mul_le (net.W₂ᵀ * net.W₂ * Z.map net.φ) net.Xᵀ
        rw [specNorm_transpose] at h2
        have h3 := h.specNorm_X
        have h4 := specNorm_nonneg (net.W₂ᵀ * net.W₂ * Z.map net.φ)
        nlinarith
      refine h1.trans ((specNorm_mul_le _ _).trans ?_)
      have h2 : specNorm (net.W₂ᵀ * net.W₂) ≤ sv net.W₂ 0 * sv net.W₂ 0 := by
        refine (specNorm_mul_le _ _).trans ?_
        rw [specNorm_W₂t, specNorm_W₂]
      exact mul_le_mul h2 (specNorm_map_le h hc hε hW₀) (specNorm_nonneg _) (by positivity)
    have hPb : ‖P‖ ≤ (μ * maxNorm Z) * ‖A‖ := by
      refine norm_hadamard_le (by positivity) fun i j => ?_
      have h1 := abs_sub_le_of_abs_deriv_le h.φ'_diff h.φ''_bound (Z i j) 0
      rw [sub_zero] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (abs_le_maxNorm Z i j) hμ)
    have hAb : ‖A‖ ≤ sv net.W₂ 0 * ‖net.residual W₀‖ := by
      rw [← specNorm_W₂t]
      exact frob_mul_le _ _
    have hDb := norm_residual_le h hε hW₀
    have hPX : specNorm (P * net.Xᵀ) ≤ (μ * maxNorm Z) *
        (sv net.W₂ 0 * (sv net.W₂ 0 * (β * (ε * √d)) + ‖net.Y‖)) := by
      refine (specNorm_le_frob _).trans ((h.norm_mul_Xt _).trans (hPb.trans ?_))
      refine mul_le_mul_of_nonneg_left (hAb.trans ?_) (by positivity)
      exact mul_le_mul_of_nonneg_left hDb hσ
    have hcQ : specNorm (c • Q) ≤ c * (sv net.W₂ 0 * sv net.W₂ 0 * (c * ε + μ / 2 * ε ^ 2)) := by
      refine (specNorm_smul_le _ _).trans ?_
      rw [abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left hQb hc
    refine (WeylSingular.specNorm_add_le _ _).trans ((add_le_add hcQ hPX).trans (le_of_eq ?_))
    simp only [rEps, ← hZ, ← hcdef]
    ring

/-- **Lemma D.8** (arXiv 2602.06208): for `W₁(0)ᵀ W₁(0) = ε² I` the gradient at initialisation is
approximately of rank `K`: `|σ_i(G₁(0)) - φ'(0) σ_i(W₂ᵀ Y Xᵀ)| ≤ r(ε)` for `i ≤ K` and
`σ_i(G₁(0)) ≤ r(ε)` for `i > K`.
Differences from the paper: indices are zero-based (`i < K`, `K ≤ i`); the hypothesis
`0 ≤ φ'(0)` is made explicit (the paper uses it silently, for instance in the bound
`σ₁(φ(W₁(0) X)) ≤ φ'(0) σ₁(Z₁(0)) + σ₁(R(Z₁(0)))` and for `r(ε) ≥ 0`); the paper's smallness
condition `r(ε) < φ'(0) σ_K(W₂ᵀ Y Xᵀ) / 2` only serves to separate `σ_K` from `σ_{K+1}` and is not
needed for these inclusions; see `sv_grad_gap` for the separation. -/
theorem lemma_D_8 {β μ ε : ℝ} (h : net.Assumptions β μ) (hc : 0 ≤ deriv net.φ 0) (hε : 0 ≤ ε)
    {W₀ : Matrix (Fin m) (Fin d) ℝ}
    (hW₀ : W₀ᵀ * W₀ = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    (∀ i, i < K → |sv (net.grad W₀) i - deriv net.φ 0 * sv net.target i| ≤ net.rEps β μ ε W₀) ∧
      ∀ i, K ≤ i → sv (net.grad W₀) i ≤ net.rEps β μ ε W₀ := by
  obtain ⟨E, hE, hEb⟩ := exists_grad_eq_add h hc hε hW₀
  have hw : ∀ i, |sv (net.grad W₀) i - deriv net.φ 0 * sv net.target i| ≤
      net.rEps β μ ε W₀ := fun i => by
    have h1 : |sv ((-deriv net.φ 0) • net.target + E) i - sv ((-deriv net.φ 0) • net.target) i| ≤
        specNorm E := WeylSingular.abs_singularValues_add_sub_le _ _ _
    rw [← hE, sv_smul, abs_neg, abs_of_nonneg hc] at h1
    exact h1.trans hEb
  refine ⟨fun i _ => hw i, fun i hi => ?_⟩
  have h1 := hw i
  rw [sv_eq_zero_of_rank_le ((rank_target_le net).trans hi), mul_zero, sub_zero] at h1
  exact (le_abs_self _).trans h1

/-- Gap at initialisation (the end of the proof of Lemma D.8): if
`r(ε) < φ'(0) σ_K(W₂ᵀ Y Xᵀ) / 2`, then `σ_{K+1}(G₁(0)) < σ_K(G₁(0))`. -/
lemma sv_grad_gap {β μ ε : ℝ} (h : net.Assumptions β μ) (hc : 0 ≤ deriv net.φ 0) (hε : 0 ≤ ε)
    (hK : 0 < K) {W₀ : Matrix (Fin m) (Fin d) ℝ}
    (hW₀ : W₀ᵀ * W₀ = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hr : net.rEps β μ ε W₀ < deriv net.φ 0 * sv net.target (K - 1) / 2) :
    sv (net.grad W₀) K < sv (net.grad W₀) (K - 1) := by
  obtain ⟨h1, h2⟩ := lemma_D_8 h hc hε hW₀
  have h3 := abs_le.mp (h1 (K - 1) (by omega))
  have h4 := h2 K le_rfl
  linarith [h3.1]

/-- `r(ε) ≥ 0`. -/
lemma rEps_nonneg {β μ ε : ℝ} (h : net.Assumptions β μ) (hc : 0 ≤ deriv net.φ 0) (hε : 0 ≤ ε)
    {W₀ : Matrix (Fin m) (Fin d) ℝ}
    (hW₀ : W₀ᵀ * W₀ = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) : 0 ≤ net.rEps β μ ε W₀ :=
  (sv_nonneg _ K).trans ((lemma_D_8 h hc hε hW₀).2 K le_rfl)

variable (net) in
/-- The numerator constant of `δ(t)`: `γ_L β σ₁(W₂) √(2 ℓ(0)) Θ(1)`, where the paper's `Θ(1)` is
`G₁ η / (1 - q)`. -/
def deltaNum (β μ M G₁ q η : ℝ) (W₀ : Matrix (Fin m) (Fin d) ℝ) : ℝ :=
  net.gammaL β μ M * β * sv net.W₂ 0 * √(2 * net.loss W₀) * (G₁ * η / (1 - q))

variable (net) in
/-- The denominator `φ'(0) σ_K(W₂ᵀ Y Xᵀ) - r(ε) - σ_{K+1}(G₁(t))` of `δ(t)`. -/
def deltaDen (β μ ε : ℝ) (W₀ W : Matrix (Fin m) (Fin d) ℝ) : ℝ :=
  deriv net.φ 0 * sv net.target (K - 1) - net.rEps β μ ε W₀ - sv (net.grad W) K

variable (net) in
/-- A full-batch gradient descent run `W₁(t + 1) = W₁(t) - η G₁(t)` on the squared loss with the
fixed second layer, satisfying **Assumption 3.4**, and with a choice of SVD
`G₁(t) = L(t) Σ(t) R(t)ᵀ` at every iteration (for repeated singular values the SVD is not unique;
all statements hold for every choice).

`q ∈ [0, 1)` stands for the paper's `(1 - Θ(η))^{Θ(1)}`, so that `q ^ t` is the paper's
`(1 - Θ(η))^{Θ(t)}`; see `rpow_decay_eq_pow`.  The quotients of Assumption 3.4 are the paper's;
their denominators are positive under the hypotheses of the theorems. -/
structure Run (η M G₁ G₂ G₃ q : ℝ) (W : ℕ → Matrix (Fin m) (Fin d) ℝ)
    (L : ℕ → Matrix (Fin m) (Fin m) ℝ) (R : ℕ → Matrix (Fin d) (Fin d) ℝ) : Prop where
  η_pos : 0 < η
  q_nonneg : 0 ≤ q
  q_lt_one : q < 1
  gd : ∀ t, W (t + 1) = W t - η • net.grad (W t)
  svd : ∀ t, IsSVD (net.grad (W t)) (L t) (R t)
  residual_bound : ∀ t, maxNorm (net.residual (W t)) ≤ M
  grad_decay : ∀ t, ‖net.grad (W t)‖ / ‖net.grad (W 0)‖ ≤ G₁ * q ^ t
  sv_decay : ∀ t, ∀ i < K, sv (net.grad (W t)) i / sv (net.grad (W 0)) i ≤
    G₂ * (‖net.grad (W t)‖ / ‖net.grad (W 0)‖)
  tail_gap : ∀ t, G₃ * sv net.target (K - 1) ≤ sv net.target (K - 1) - sv (net.grad (W t)) K

variable {η M G₁ G₂ G₃ q β μ ε : ℝ} {W : ℕ → Matrix (Fin m) (Fin d) ℝ}
  {L : ℕ → Matrix (Fin m) (Fin m) ℝ} {R : ℕ → Matrix (Fin d) (Fin d) ℝ}

/-- `σ_K(G₁(0)) > 0`. -/
lemma sv_grad_pos (h : net.Assumptions β μ) (hc : 0 ≤ deriv net.φ 0) (hε : 0 ≤ ε) (hK : 0 < K)
    {W₀ : Matrix (Fin m) (Fin d) ℝ} (hW₀ : W₀ᵀ * W₀ = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hr : net.rEps β μ ε W₀ < deriv net.φ 0 * sv net.target (K - 1) / 2) :
    0 < sv (net.grad W₀) (K - 1) :=
  lt_of_le_of_lt (sv_nonneg _ K) (sv_grad_gap h hc hε hK hW₀ hr)

lemma sv_le_norm {α β' : Type*} [Fintype α] [Fintype β'] [DecidableEq β'] (A : Matrix α β' ℝ)
    (i : ℕ) : sv A i ≤ ‖A‖ := by
  classical
  have h1 : sv A i ≤ specNorm A := by
    rw [specNorm_eq_singularValues_zero]
    exact (toEuclideanLin A).singularValues_antitone (Nat.zero_le i)
  exact h1.trans (specNorm_le_frob A)

lemma norm_grad_pos (h : net.Assumptions β μ) (hc : 0 ≤ deriv net.φ 0) (hε : 0 ≤ ε) (hK : 0 < K)
    {W₀ : Matrix (Fin m) (Fin d) ℝ} (hW₀ : W₀ᵀ * W₀ = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hr : net.rEps β μ ε W₀ < deriv net.φ 0 * sv net.target (K - 1) / 2) :
    0 < ‖net.grad W₀‖ :=
  (sv_grad_pos h hc hε hK hW₀ hr).trans_le (sv_le_norm _ _)

/-- Accumulated movement of a run: `‖W₁(t) - W₁(0)‖_F ≤ η G₁ (1 - q^t) / (1 - q) ‖G₁(0)‖_F`. -/
lemma Run.norm_sub_init_le (hrun : net.Run η M G₁ G₂ G₃ q W L R)
    (hpos : 0 < ‖net.grad (W 0)‖) (t : ℕ) :
    ‖W t - W 0‖ ≤ G₁ * η / (1 - q) * (1 - q ^ t) * ‖net.grad (W 0)‖ := by
  have hq : 0 < 1 - q := sub_pos.mpr hrun.q_lt_one
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 : W (t + 1) - W 0 = (W t - W 0) - η • net.grad (W t) := by
      rw [hrun.gd t]
      abel
    have h2 : ‖net.grad (W t)‖ ≤ G₁ * q ^ t * ‖net.grad (W 0)‖ :=
      (div_le_iff₀ hpos).mp (hrun.grad_decay t)
    have hη := hrun.η_pos
    rw [h1]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    have h3 := mul_le_mul_of_nonneg_left h2 hη.le
    have e : G₁ * η / (1 - q) * (1 - q ^ (t + 1)) * ‖net.grad (W 0)‖ =
        G₁ * η / (1 - q) * (1 - q ^ t) * ‖net.grad (W 0)‖ +
          η * (G₁ * q ^ t * ‖net.grad (W 0)‖) := by
      field_simp
      ring
    rw [e]
    exact add_le_add ih h3

lemma Run.one_le_G₁ (hrun : net.Run η M G₁ G₂ G₃ q W L R) (hpos : 0 < ‖net.grad (W 0)‖) :
    1 ≤ G₁ := by
  have h1 := hrun.grad_decay 0
  rwa [div_self hpos.ne', pow_zero, mul_one] at h1

lemma Run.one_le_G₂ (hrun : net.Run η M G₁ G₂ G₃ q W L R) (hK : 0 < K)
    (hpos : 0 < ‖net.grad (W 0)‖) (hσ : 0 < sv (net.grad (W 0)) 0) : 1 ≤ G₂ := by
  have h1 := hrun.sv_decay 0 0 hK
  rwa [div_self hσ.ne', div_self hpos.ne', mul_one] at h1

lemma Run.M_nonneg (hrun : net.Run η M G₁ G₂ G₃ q W L R) : 0 ≤ M :=
  (maxNorm_nonneg _).trans (hrun.residual_bound 0)

lemma Run.one_sub_pow_nonneg (hrun : net.Run η M G₁ G₂ G₃ q W L R) (t : ℕ) : 0 ≤ 1 - q ^ t :=
  sub_nonneg.mpr (pow_le_one₀ hrun.q_nonneg hrun.q_lt_one.le)

lemma gammaL_nonneg (h : net.Assumptions β μ) (hM : 0 ≤ M) : 0 ≤ net.gammaL β μ M := by
  have hμ := h.μ_nonneg
  have hone := oneNorm_nonneg net.W₂
  rw [gammaL]
  positivity

lemma Run.deltaNum_nonneg (h : net.Assumptions β μ) (hrun : net.Run η M G₁ G₂ G₃ q W L R)
    (hpos : 0 < ‖net.grad (W 0)‖) : 0 ≤ net.deltaNum β μ M G₁ q η (W 0) := by
  have h1 := gammaL_nonneg h hrun.M_nonneg
  have h2 := h.β_nonneg
  have h3 : 0 ≤ sv net.W₂ 0 := (toEuclideanLin net.W₂).singularValues_nonneg 0
  have h4 : 0 ≤ G₁ := zero_le_one.trans (hrun.one_le_G₁ hpos)
  have h5 := hrun.η_pos
  have h6 : 0 < 1 - q := sub_pos.mpr hrun.q_lt_one
  rw [deltaNum]
  positivity

/-- The first half of the proof of Lemma D.9:
`‖G₁(t) - G₁(0)‖_F ≤ γ_L β σ₁(W₂) √(2 ℓ(0)) Θ(1) (1 - q^t)`. -/
lemma Run.norm_grad_sub_le (h : net.Assumptions β μ) (hrun : net.Run η M G₁ G₂ G₃ q W L R)
    (hpos : 0 < ‖net.grad (W 0)‖) (t : ℕ) :
    ‖net.grad (W t) - net.grad (W 0)‖ ≤ net.deltaNum β μ M G₁ q η (W 0) * (1 - q ^ t) := by
  have h7 := lemma_D_7 h (hrun.residual_bound t) (W' := W 0)
  have h1 := hrun.norm_sub_init_le hpos t
  have h6 := lemma_D_6 h (W 0)
  have hγ := gammaL_nonneg h hrun.M_nonneg (net := net) (β := β) (μ := μ)
  have hG₁ : 0 ≤ G₁ := zero_le_one.trans (hrun.one_le_G₁ hpos)
  have hη := hrun.η_pos
  have hq : 0 < 1 - q := sub_pos.mpr hrun.q_lt_one
  have hκ : 0 ≤ G₁ * η / (1 - q) * (1 - q ^ t) :=
    mul_nonneg (by positivity) (hrun.one_sub_pow_nonneg t)
  calc ‖net.grad (W t) - net.grad (W 0)‖ ≤ net.gammaL β μ M * ‖W t - W 0‖ := h7
    _ ≤ net.gammaL β μ M * (G₁ * η / (1 - q) * (1 - q ^ t) * ‖net.grad (W 0)‖) :=
        mul_le_mul_of_nonneg_left h1 hγ
    _ ≤ net.gammaL β μ M * (G₁ * η / (1 - q) * (1 - q ^ t) *
          (β * sv net.W₂ 0 * √(2 * net.loss (W 0)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h6 hκ) hγ
    _ = _ := by
        simp only [deltaNum]
        ring

variable (net) in
/-- The quantity `δ(t)` of Lemmas D.9–D.10 and Theorem D.11. -/
def delta (β μ ε M G₁ q η : ℝ) (W₀ W : Matrix (Fin m) (Fin d) ℝ) (t : ℕ) : ℝ :=
  net.deltaNum β μ M G₁ q η W₀ * (1 - q ^ t) / net.deltaDen β μ ε W₀ W

/-- **Lemma D.9** (arXiv 2602.06208): the top-`K` singular subspaces of `G₁(t)` stay close to those
of `G₁(0)`: `‖sin Θ(L₁,₁(t), L₁,₁(0))‖₂ ≤ δ(t)`, `‖sin Θ(R₁,₁(t), R₁,₁(0))‖₂ ≤ δ(t)`.  By Lemma D.3
these are the paper's `‖L₁,₁ᵀ(t) L₁,₂(0)‖_F` and `‖R₁,₁ᵀ(t) R₁,₂(0)‖_F`.  Differences from the
paper: `q^t` stands for `(1 - Θ(η))^{Θ(t)}` and the `Θ(1)` is explicit (`G₁ η / (1 - q)`, see
`deltaNum`); `η ≤ 1/γ_L` is not needed.  **Conditional on** `hden`, the positivity of the
denominators, which the paper derives from Assumption 3.4 and the condition on `r(ε)`; here it is
proved from Assumption 3.4 under the added hypothesis `G₃ ≥ 1 - φ'(0)/2`, see `Run.deltaDen_pos`. -/
theorem lemma_D_9 (h : net.Assumptions β μ) (hc : 0 ≤ deriv net.φ 0) (hε : 0 ≤ ε) (hK : 0 < K)
    (hKm : K ≤ m) (hKd : K ≤ d)
    (hW₀ : (W 0)ᵀ * W 0 = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hr : net.rEps β μ ε (W 0) < deriv net.φ 0 * sv net.target (K - 1) / 2)
    (hrun : net.Run η M G₁ G₂ G₃ q W L R) (hden : ∀ t, 0 < net.deltaDen β μ ε (W 0) (W t))
    (t : ℕ) :
    sinTheta (topCols hKm (L t)) (topCols hKm (L 0)) ≤ net.delta β μ ε M G₁ q η (W 0) (W t) t ∧
      sinTheta (topCols hKd (R t)) (topCols hKd (R 0)) ≤
        net.delta β μ ε M G₁ q η (W 0) (W t) t := by
  have hpos := norm_grad_pos h hc hε hK hW₀ hr
  obtain ⟨h1, -⟩ := lemma_D_8 h hc hε hW₀
  have h2 := (abs_le.mp (h1 (K - 1) (by omega))).1
  have hden' := hden t
  have hlow : net.deltaDen β μ ε (W 0) (W t) ≤
      sv (net.grad (W 0)) (K - 1) - sv (net.grad (W t)) K := by
    simp only [deltaDen]
    linarith
  have hgap : sv (net.grad (W t)) K < sv (net.grad (W 0)) (K - 1) := by linarith
  have hW := lemma_D_5 (hrun.svd t) (hrun.svd 0) hK hKm hKd hgap
  have hb : ‖net.grad (W 0) - net.grad (W t)‖ /
      (sv (net.grad (W 0)) (K - 1) - sv (net.grad (W t)) K) ≤
      net.delta β μ ε M G₁ q η (W 0) (W t) t := by
    rw [norm_sub_rev, delta]
    exact div_le_div₀ (mul_nonneg (hrun.deltaNum_nonneg h hpos) (hrun.one_sub_pow_nonneg t))
      (hrun.norm_grad_sub_le h hpos t) hden' hlow
  have hLo := topCols_transpose_mul_self hKm (hrun.svd t).left
  have hLo' := topCols_transpose_mul_self hKm (hrun.svd 0).left
  have hRo := topCols_transpose_mul_self hKd (hrun.svd t).right
  have hRo' := topCols_transpose_mul_self hKd (hrun.svd 0).right
  rw [sinTheta_comm hLo hLo', sinTheta_comm hRo hRo']
  exact ⟨(le_max_left _ _).trans (hW.trans hb), (le_max_right _ _).trans (hW.trans hb)⟩

/-- The positivity of the denominators of `δ(t)`, with a uniform lower bound.  The paper asserts
positivity from Assumption 3.4 and `r(ε) < φ'(0) σ_K / 2`; this proof uses, in addition,
`G₃ ≥ 1 - φ'(0) / 2`. -/
lemma Run.deltaDen_pos (h : net.Assumptions β μ) (hc : 0 ≤ deriv net.φ 0) (hε : 0 ≤ ε)
    (hrun : net.Run η M G₁ G₂ G₃ q W L R)
    (hW₀ : (W 0)ᵀ * W 0 = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hr : net.rEps β μ ε (W 0) < deriv net.φ 0 * sv net.target (K - 1) / 2)
    (hG₃ : 1 - deriv net.φ 0 / 2 ≤ G₃) (t : ℕ) :
    0 < (deriv net.φ 0 - 1 + G₃) * sv net.target (K - 1) - net.rEps β μ ε (W 0) ∧
      (deriv net.φ 0 - 1 + G₃) * sv net.target (K - 1) - net.rEps β μ ε (W 0) ≤
        net.deltaDen β μ ε (W 0) (W t) := by
  have h0 := rEps_nonneg h hc hε hW₀
  have hσ : 0 ≤ sv net.target (K - 1) := (toEuclideanLin net.target).singularValues_nonneg _
  have h1 := hrun.tail_gap t
  have h2 : deriv net.φ 0 / 2 * sv net.target (K - 1) ≤
      (deriv net.φ 0 - 1 + G₃) * sv net.target (K - 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hσ
  refine ⟨by linarith, ?_⟩
  simp only [deltaDen]
  nlinarith

lemma sinTheta_self {α : Type*} [Fintype α] {k : ℕ} {U : Matrix α (Fin k) ℝ}
    (hU : Uᵀ * U = 1) : sinTheta U U = 0 := by
  classical
  rw [sinTheta_eq_norm_compl_mul hU hU, Matrix.sub_mul, Matrix.mul_assoc, hU, Matrix.mul_one,
    Matrix.one_mul, sub_self, norm_zero]

/-- The value at `t = 0`: `ρ(0) = σ_{K+1}(G₁(0)) ≤ r(ε)`.  (The paper states the weaker
`ρ(0) ≤ r(ε) √p`, which follows; its proof gives this.) -/
lemma rho_zero_le (h : net.Assumptions β μ) (hc : 0 ≤ deriv net.φ 0) (hε : 0 ≤ ε)
    (hKm : K ≤ m) (hKd : K ≤ d) {p : ℕ}
    (hW₀ : (W 0)ᵀ * W 0 = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hrun : net.Run η M G₁ G₂ G₃ q W L R) :
    rho hKm hKd L R (fun t => net.grad (W t)) p 0 ≤ net.rEps β μ ε (W 0) := by
  have hLo := topCols_transpose_mul_self hKm (hrun.svd 0).left
  have hRo := topCols_transpose_mul_self hKd (hrun.svd 0).right
  have h1 : alignment hKm hKd L R 0 = 0 := by
    rw [alignment, sinTheta_self hLo, sinTheta_self hRo, max_self]
  have h2 := (lemma_D_8 h hc hε hW₀).2 K le_rfl
  have h3 : 0 ≤ sv (net.grad (W 0)) K := sv_nonneg _ _
  simp only [rho, h1]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    zero_add]
  rwa [Real.sqrt_sq h3]

/-- The value at `t ≥ 1` in Lemma D.10 and Theorem D.11:
`ρ(t) ≤ (Ḡ² q^{2t} δ²(t) / p (φ'(0) σ₁(W₂ᵀ Y Xᵀ) + r(ε))² + σ²_{K+1}(G₁(t)))^{1/2}`, `Ḡ = G₁ G₂`.
It holds for `t = 0` as well. -/
lemma rho_le (h : net.Assumptions β μ) (hc : 0 ≤ deriv net.φ 0) (hε : 0 ≤ ε) (hK : 0 < K)
    (hKm : K ≤ m) (hKd : K ≤ d) {p : ℕ}
    (hW₀ : (W 0)ᵀ * W 0 = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hr : net.rEps β μ ε (W 0) < deriv net.φ 0 * sv net.target (K - 1) / 2)
    (hrun : net.Run η M G₁ G₂ G₃ q W L R) (hden : ∀ t, 0 < net.deltaDen β μ ε (W 0) (W t))
    (t : ℕ) :
    rho hKm hKd L R (fun t => net.grad (W t)) p t ≤
      √((G₁ * G₂) ^ 2 * q ^ (2 * t) * net.delta β μ ε M G₁ q η (W 0) (W t) t ^ 2 / p *
          (deriv net.φ 0 * sv net.target 0 + net.rEps β μ ε (W 0)) ^ 2 +
        sv (net.grad (W t)) K ^ 2) := by
  have hpos := norm_grad_pos h hc hε hK hW₀ hr
  have hσK := sv_grad_pos h hc hε hK hW₀ hr
  have hσ0 : 0 < sv (net.grad (W 0)) 0 :=
    hσK.trans_le (sv_antitone _ (Nat.zero_le _))
  have hG₁ := hrun.one_le_G₁ hpos
  have hG₂ := hrun.one_le_G₂ hK hpos hσ0
  have hqt : 0 ≤ q ^ t := pow_nonneg hrun.q_nonneg t
  obtain ⟨hD, -⟩ := lemma_D_8 h hc hε hW₀
  have hσ0T : sv (net.grad (W 0)) 0 ≤
      deriv net.φ 0 * sv net.target 0 + net.rEps β μ ε (W 0) := by
    have := (abs_le.mp (hD 0 hK)).2
    linarith
  set e := deriv net.φ 0 * sv net.target 0 + net.rEps β μ ε (W 0) with he
  have hdec : sv (net.grad (W t)) 0 ≤ G₁ * G₂ * q ^ t * e := by
    have h1 := hrun.sv_decay t 0 hK
    have h2 := hrun.grad_decay t
    have h3 : sv (net.grad (W t)) 0 / sv (net.grad (W 0)) 0 ≤ G₂ * (G₁ * q ^ t) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
    have h4 := (div_le_iff₀ hσ0).mp h3
    have h5 : 0 ≤ G₁ * G₂ * q ^ t := by positivity
    calc _ ≤ G₂ * (G₁ * q ^ t) * sv (net.grad (W 0)) 0 := h4
      _ = G₁ * G₂ * q ^ t * sv (net.grad (W 0)) 0 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hσ0T h5
  obtain ⟨hL, hR⟩ := lemma_D_9 h hc hε hK hKm hKd hW₀ hr hrun hden t
  set δ := net.delta β μ ε M G₁ q η (W 0) (W t) t with hδ
  have hA : alignment hKm hKd L R t ≤ δ := max_le hL hR
  have hA0 : 0 ≤ alignment hKm hKd L R t := le_max_of_le_left (Real.sqrt_nonneg _)
  have hs0 : 0 ≤ sv (net.grad (W t)) 0 := sv_nonneg _ _
  have h1 : sv (net.grad (W t)) 0 ^ 2 * alignment hKm hKd L R t ^ 2 ≤
      (G₁ * G₂ * q ^ t * e) ^ 2 * δ ^ 2 :=
    mul_le_mul (pow_le_pow_left₀ hs0 hdec 2) (pow_le_pow_left₀ hA0 hA 2) (by positivity)
      (by positivity)
  refine Real.sqrt_le_sqrt ?_
  have h2 : (G₁ * G₂ * q ^ t * e) ^ 2 * δ ^ 2 =
      (G₁ * G₂) ^ 2 * q ^ (2 * t) * δ ^ 2 * e ^ 2 := by
    rw [mul_comm 2 t, pow_mul]
    ring
  have hdiv := div_le_div_of_nonneg_right h1 (Nat.cast_nonneg p)
  rw [h2] at hdiv
  have e3 : (G₁ * G₂) ^ 2 * q ^ (2 * t) * δ ^ 2 / p * e ^ 2 =
      (G₁ * G₂) ^ 2 * q ^ (2 * t) * δ ^ 2 * e ^ 2 / p := by ring
  rw [e3]
  exact add_le_add hdiv le_rfl

/-- **Lemma D.10** (arXiv 2602.06208).  Under the hypotheses of Lemma D.9 there are `V ∈ ℝ^{d×p}`,
`U ∈ ℝ^{m×p}` with orthonormal columns, built from `W₁(0)`, `L₀`, `R₀` only, such that
`W₁(0) V = ε U`, `W₁(0)ᵀ U = ε V`, and along every run
`max {‖W₁(t+1) V - W₁(t) V‖_F, ‖W₁ᵀ(t+1) U - W₁ᵀ(t) U‖_F} / √p ≤ η ρ(t)`, with the bounds on `ρ(t)`.
Differences from the paper: the bound at `t = 0` is the sharper `ρ(0) ≤ r(ε)`; `0 < φ'(0)` and
`0 < ε` are explicit (the paper divides by `ε` and uses the sign of `φ'(0)` without comment);
`η ≤ 1/γ_L` is not needed.  **Conditional on** `hden` (positivity of the denominators of `δ(t)`),
as `lemma_D_9`. -/
theorem lemma_D_10 (h : net.Assumptions β μ) (hc : 0 < deriv net.φ 0) (hε : 0 < ε) (hK : 0 < K)
    (hKm : K ≤ m) (hKd : K ≤ d) {p : ℕ} (hd : 2 * K + p = d) (hp : 0 < p)
    {W₀ : Matrix (Fin m) (Fin d) ℝ}
    (hW₀ : W₀ᵀ * W₀ = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hr : net.rEps β μ ε W₀ < deriv net.φ 0 * sv net.target (K - 1) / 2)
    (L₀ : Matrix (Fin m) (Fin m) ℝ) (R₀ : Matrix (Fin d) (Fin d) ℝ) :
    ∃ (U : Matrix (Fin m) (Fin p) ℝ) (V : Matrix (Fin d) (Fin p) ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ W₀ * V = ε • U ∧ W₀ᵀ * U = ε • V ∧
      ∀ {η M G₁ G₂ G₃ q : ℝ} {W : ℕ → Matrix (Fin m) (Fin d) ℝ}
        {L : ℕ → Matrix (Fin m) (Fin m) ℝ} {R : ℕ → Matrix (Fin d) (Fin d) ℝ},
        net.Run η M G₁ G₂ G₃ q W L R → W 0 = W₀ → L 0 = L₀ → R 0 = R₀ →
        (∀ t, 0 < net.deltaDen β μ ε W₀ (W t)) → ∀ t,
          max (‖W (t + 1) * V - W t * V‖ / √p) (‖(W (t + 1))ᵀ * U - (W t)ᵀ * U‖ / √p) ≤
            η * rho hKm hKd L R (fun t => net.grad (W t)) p t ∧
          rho hKm hKd L R (fun t => net.grad (W t)) p 0 ≤ net.rEps β μ ε W₀ ∧
          rho hKm hKd L R (fun t => net.grad (W t)) p t ≤
            √((G₁ * G₂) ^ 2 * q ^ (2 * t) * net.delta β μ ε M G₁ q η W₀ (W t) t ^ 2 / p *
                (deriv net.φ 0 * sv net.target 0 + net.rEps β μ ε W₀) ^ 2 +
              sv (net.grad (W t)) K ^ 2) := by
  obtain ⟨U, V, hU, hV, h1, h2, hR, hL⟩ := exists_small_update_basis (p := p) (by omega) hε hW₀
    (topCols hKm L₀) (topCols hKd R₀)
  refine ⟨U, V, hU, hV, h1, h2, ?_⟩
  intro η M G₁ G₂ G₃ q W L R hrun hW0 hL0 hR0 hden t
  subst hW0
  rw [← hL0] at hL
  rw [← hR0] at hR
  have hsqp : 0 < √(p : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp)
  have hη := hrun.η_pos
  obtain ⟨hGV, hGU⟩ := norm_mul_le_rho (G := fun t => net.grad (W t)) hp hKm hKd hrun.svd hU hV
    hR hL t
  refine ⟨?_, rho_zero_le h hc.le hε.le hKm hKd hW₀ hrun,
    rho_le h hc.le hε.le hK hKm hKd hW₀ hr hrun hden t⟩
  refine max_le ?_ ?_
  · rw [div_le_iff₀ hsqp, hrun.gd t, Matrix.sub_mul, Matrix.smul_mul, sub_sub_cancel_left,
      norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hη, mul_assoc]
    exact mul_le_mul_of_nonneg_left hGV hη.le
  · rw [div_le_iff₀ hsqp, hrun.gd t, transpose_sub, transpose_smul, Matrix.sub_mul,
      Matrix.smul_mul, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hη,
      mul_assoc]
    exact mul_le_mul_of_nonneg_left hGU hη.le

/-- **Theorem D.11** (formal version of Theorem 3.5, arXiv 2602.06208).  Let `X` be whitened,
`2 K + p = d`, `d ≤ m`, `W₁(0)ᵀ W₁(0) = ε² I`, `r(ε) < φ'(0) σ_K(W₂ᵀ Y Xᵀ) / 2`.  Then there are
orthogonal `U ∈ ℝ^{m×m}`, `V ∈ ℝ^{d×d}`, with columns grouped as `(m - p) + p` and `2 K + p`, such
that `W̃₁ = Uᵀ W₁ V` has `W̃₁,₂(0) = 0`, `W̃₁,₃(0) = 0`, `‖W̃₁,₄(0)‖_F / √p = ε`, and for every run
(GD with Assumption 3.4) started at `W₁(0)`, for all `t`: `W₁(t) = U W̃₁(t) Vᵀ`,
`‖W̃₁,ᵢ(t + 1) - W̃₁,ᵢ(t)‖_F / √p ≤ η ρ(t)` for `i ∈ {2, 3, 4}`, with
`ρ(t) = (σ₁²(G₁(t)) A²(t) / p + σ²_{K+1}(G₁(t)))^{1/2}`, `ρ(0) ≤ r(ε)`, and
`ρ(t) ≤ (Ḡ² q^{2t} δ²(t) / p (φ'(0) σ₁(W₂ᵀ Y Xᵀ) + r(ε))² + σ²_{K+1}(G₁(t)))^{1/2}`.

`U`, `V` are chosen before the run: they depend on `W₁(0)` and on the SVD factors `L₀`, `R₀` of
`G₁(0)` only.  In Lean, `W̃₁,₂`, `W̃₁,₃`, `W̃₁,₄` are `toBlocks₁₂`, `toBlocks₂₁`, `toBlocks₂₂`.

Differences from the paper.  `q^t` stands for `(1 - Θ(η))^{Θ(t)}` (`Net.Run`, `rpow_decay_eq_pow`),
and the exponent `Θ(t)` in the bound on `ρ` is written `2 t`.  `Θ(1)` in `δ(t)` is explicit.
`0 < φ'(0)` and `0 < ε` are explicit hypotheses, used silently in the paper.
`1 - φ'(0)/2 ≤ G₃` is **added**: the paper says that the denominator of `δ(t)` is positive by
Assumption 3.4 and `r(ε) < φ'(0) σ_K / 2`; the proof here derives the positivity from Assumption 3.4
with this added hypothesis, which bounds `σ_{K+1}(G₁(t)) ≤ (1 - G₃) σ_K ≤ φ'(0) σ_K / 2`.  No
counterexample for smaller `G₃` is formalized.
The sharper `ρ(0) ≤ r(ε)` replaces the paper's `ρ(0) ≤ r(ε) √p`.  `η ≤ 1/γ_L` and the full row rank
of `W₂` are not needed. -/
theorem theorem_D_11 (h : net.Assumptions β μ) (hc : 0 < deriv net.φ 0) (hε : 0 < ε) (hK : 0 < K)
    (hKm : K ≤ m) (hKd : K ≤ d) (hmd : d ≤ m) {p : ℕ} (hd : 2 * K + p = d) (hp : 0 < p)
    {W₀ : Matrix (Fin m) (Fin d) ℝ}
    (hW₀ : W₀ᵀ * W₀ = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hr : net.rEps β μ ε W₀ < deriv net.φ 0 * sv net.target (K - 1) / 2)
    (L₀ : Matrix (Fin m) (Fin m) ℝ) (R₀ : Matrix (Fin d) (Fin d) ℝ) :
    ∃ (U : Matrix (Fin m) (Fin (m - p) ⊕ Fin p) ℝ) (V : Matrix (Fin d) (Fin (2 * K) ⊕ Fin p) ℝ),
      Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ Vᵀ * V = 1 ∧ V * Vᵀ = 1 ∧
      (tilde U V W₀).toBlocks₁₂ = 0 ∧ (tilde U V W₀).toBlocks₂₁ = 0 ∧
      ‖(tilde U V W₀).toBlocks₂₂‖ / √p = ε ∧
      ∀ {η M G₁ G₂ G₃ q : ℝ} {W : ℕ → Matrix (Fin m) (Fin d) ℝ}
        {L : ℕ → Matrix (Fin m) (Fin m) ℝ} {R : ℕ → Matrix (Fin d) (Fin d) ℝ},
        net.Run η M G₁ G₂ G₃ q W L R → W 0 = W₀ → L 0 = L₀ → R 0 = R₀ →
        1 - deriv net.φ 0 / 2 ≤ G₃ → ∀ t,
          W t = U * fromBlocks (tilde U V (W t)).toBlocks₁₁ (tilde U V (W t)).toBlocks₁₂
            (tilde U V (W t)).toBlocks₂₁ (tilde U V (W t)).toBlocks₂₂ * Vᵀ ∧
          ‖(tilde U V (W (t + 1))).toBlocks₁₂ - (tilde U V (W t)).toBlocks₁₂‖ / √p ≤
            η * rho hKm hKd L R (fun t => net.grad (W t)) p t ∧
          ‖(tilde U V (W (t + 1))).toBlocks₂₁ - (tilde U V (W t)).toBlocks₂₁‖ / √p ≤
            η * rho hKm hKd L R (fun t => net.grad (W t)) p t ∧
          ‖(tilde U V (W (t + 1))).toBlocks₂₂ - (tilde U V (W t)).toBlocks₂₂‖ / √p ≤
            η * rho hKm hKd L R (fun t => net.grad (W t)) p t ∧
          rho hKm hKd L R (fun t => net.grad (W t)) p 0 ≤ net.rEps β μ ε W₀ ∧
          rho hKm hKd L R (fun t => net.grad (W t)) p t ≤
            √((G₁ * G₂) ^ 2 * q ^ (2 * t) * net.delta β μ ε M G₁ q η W₀ (W t) t ^ 2 / p *
                (deriv net.φ 0 * sv net.target 0 + net.rEps β μ ε W₀) ^ 2 +
              sv (net.grad (W t)) K ^ 2) := by
  obtain ⟨U, V, hU, hU', hV, hV', h12, h21, h22, hrest⟩ :=
    exists_block_decomposition hd hmd hp hKm hKd hε hW₀ L₀ R₀
  refine ⟨U, V, hU, hU', hV, hV', h12, h21, h22, ?_⟩
  intro η M G₁ G₂ G₃ q W L R hrun hW0 hL0 hR0 hG₃ t
  subst hW0
  have hden : ∀ t, 0 < net.deltaDen β μ ε (W 0) (W t) := fun t => by
    obtain ⟨h1, h2⟩ := hrun.deltaDen_pos h hc.le hε.le hW₀ hr hG₃ t
    exact h1.trans_le h2
  obtain ⟨a, b, c, e⟩ := hrest η W (fun t => net.grad (W t)) L R hrun.η_pos.le rfl hL0 hR0 hrun.gd
    hrun.svd t
  exact ⟨a, b, c, e, rho_zero_le h hc.le hε.le hKm hKd hW₀ hrun,
    rho_le h hc.le hε.le hK hKm hKd hW₀ hr hrun hden t⟩

variable (net) in
/-- The constant `C₁` of Theorem 3.5, valid for all `ε ≤ ε₀`. -/
def C₁ (β μ ε₀ : ℝ) : ℝ :=
  deriv net.φ 0 * sv net.W₂ 0 ^ 2 * (deriv net.φ 0 + μ / 2 * ε₀) +
    μ * sv net.W₂ 0 * (β * sv net.W₂ 0 * √d * ε₀ + ‖net.Y‖)

variable (net) in
/-- The constant `C₂` of Theorem 3.5: independent of `t`, of order `1 / (1 - q) = Θ(1 / η)` through
its second term (see the discussion in `theorem_3_5`). -/
def C₂ (β μ ε M G₁ G₂ G₃ q η : ℝ) (W₀ : Matrix (Fin m) (Fin d) ℝ) (p : ℕ) : ℝ :=
  √((G₁ * G₂ * (net.deltaNum β μ M G₁ q η W₀ /
        ((deriv net.φ 0 - 1 + G₃) * sv net.target (K - 1) - net.rEps β μ ε W₀)) *
        (deriv net.φ 0 * sv net.target 0 + net.rEps β μ ε W₀)) ^ 2 / p +
      (G₁ * ‖net.grad W₀‖ / (1 - q)) ^ 2)

lemma maxNorm_mul_X_le (h : net.Assumptions β μ) (hε : 0 ≤ ε) {W₀ : Matrix (Fin m) (Fin d) ℝ}
    (hW₀ : W₀ᵀ * W₀ = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    maxNorm (W₀ * net.X) ≤ ε := by
  refine maxNorm_le hε fun i j => ?_
  have h1 : (W₀ * net.X) i j ^ 2 ≤ ε ^ 2 :=
    (Finset.single_le_sum (f := fun j => (W₀ * net.X) i j ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)).trans (sum_sq_row_mul_le hW₀ h.whitened i)
  exact abs_le_of_sq_le_sq h1 hε

/-- `r(ε) ≤ C₁ ε` for `ε ≤ ε₀`: the paper's `ρ(0) ≲ C₁ ε`. -/
lemma rEps_le_C₁ (h : net.Assumptions β μ) (hc : 0 ≤ deriv net.φ 0) (hε : 0 ≤ ε) {ε₀ : ℝ}
    (hε₀ : ε ≤ ε₀) {W₀ : Matrix (Fin m) (Fin d) ℝ}
    (hW₀ : W₀ᵀ * W₀ = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    net.rEps β μ ε W₀ ≤ net.C₁ β μ ε₀ * ε := by
  have hμ := h.μ_nonneg
  have hβ := h.β_nonneg
  have hσ : 0 ≤ sv net.W₂ 0 := sv_nonneg _ _
  have hmax := maxNorm_mul_X_le h hε hW₀
  have hmax0 := maxNorm_nonneg (W₀ * net.X)
  have hY := norm_nonneg net.Y
  have hsd : 0 ≤ √(d : ℝ) := Real.sqrt_nonneg _
  have h1 : ε * deriv net.φ 0 * sv net.W₂ 0 ^ 2 * (deriv net.φ 0 + μ / 2 * ε) ≤
      ε * deriv net.φ 0 * sv net.W₂ 0 ^ 2 * (deriv net.φ 0 + μ / 2 * ε₀) :=
    mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hε₀ (by positivity))) (by positivity)
  have h2 : β * sv net.W₂ 0 * √d * ε + ‖net.Y‖ ≤ β * sv net.W₂ 0 * √d * ε₀ + ‖net.Y‖ :=
    add_le_add (mul_le_mul_of_nonneg_left hε₀ (by positivity)) le_rfl
  have h3 : μ * maxNorm (W₀ * net.X) * sv net.W₂ 0 * (β * sv net.W₂ 0 * √d * ε + ‖net.Y‖) ≤
      μ * ε * sv net.W₂ 0 * (β * sv net.W₂ 0 * √d * ε₀ + ‖net.Y‖) :=
    mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hμ) hσ) h2 (by positivity)
      (by positivity)
  calc _ ≤ _ := add_le_add h1 h3
    _ = _ := by
      simp only [C₁]
      ring

/-- The decay `ρ(t) ≤ C₂ q^t (1 - q^t)` for `t ≥ 1`. -/
lemma rho_le_C₂ (h : net.Assumptions β μ) (hc : 0 ≤ deriv net.φ 0) (hε : 0 ≤ ε) (hK : 0 < K)
    (hKm : K ≤ m) (hKd : K ≤ d) {p : ℕ}
    (hW₀ : (W 0)ᵀ * W 0 = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hr : net.rEps β μ ε (W 0) < deriv net.φ 0 * sv net.target (K - 1) / 2)
    (hrun : net.Run η M G₁ G₂ G₃ q W L R) (hG₃ : 1 - deriv net.φ 0 / 2 ≤ G₃) {t : ℕ} (ht : t ≠ 0) :
    rho hKm hKd L R (fun t => net.grad (W t)) p t ≤
      net.C₂ β μ ε M G₁ G₂ G₃ q η (W 0) p * (q ^ t * (1 - q ^ t)) := by
  have hden0 := hrun.deltaDen_pos h hc hε hW₀ hr hG₃
  have hden : ∀ t, 0 < net.deltaDen β μ ε (W 0) (W t) := fun t => (hden0 t).1.trans_le (hden0 t).2
  have hrho := rho_le (p := p) h hc hε hK hKm hKd hW₀ hr hrun hden t
  have hpos := norm_grad_pos h hc hε hK hW₀ hr
  have hq0 := hrun.q_nonneg
  have hq1 := hrun.q_lt_one
  have hq : 0 < 1 - q := sub_pos.mpr hq1
  have hG₁ := hrun.one_le_G₁ hpos
  have hN := hrun.deltaNum_nonneg h hpos
  set N := net.deltaNum β μ M G₁ q η (W 0) with hNdef
  set D₀ := (deriv net.φ 0 - 1 + G₃) * sv net.target (K - 1) - net.rEps β μ ε (W 0) with hD₀
  set e := deriv net.φ 0 * sv net.target 0 + net.rEps β μ ε (W 0) with he
  set f := G₁ * ‖net.grad (W 0)‖ / (1 - q) with hf
  have hD0 : 0 < D₀ := (hden0 0).1
  have hqt0 : 0 ≤ q ^ t := pow_nonneg hq0 t
  have hqt1 : 0 ≤ 1 - q ^ t := hrun.one_sub_pow_nonneg t
  set a := q ^ t * (1 - q ^ t) with ha
  have ha0 : 0 ≤ a := mul_nonneg hqt0 hqt1
  have hf0 : 0 ≤ f := by positivity
  set δ := net.delta β μ ε M G₁ q η (W 0) (W t) t with hδ
  have hδ0 : 0 ≤ δ := div_nonneg (mul_nonneg hN hqt1) (hden t).le
  have hδ1 : δ ≤ N / D₀ * (1 - q ^ t) := by
    have e1 : N / D₀ * (1 - q ^ t) = N * (1 - q ^ t) / D₀ := by ring
    rw [e1]
    exact div_le_div_of_nonneg_left (mul_nonneg hN hqt1) hD0 (hden0 t).2
  have hs0 : 0 ≤ sv (net.grad (W t)) K := sv_nonneg _ _
  have hs1 : sv (net.grad (W t)) K ≤ f * a := by
    have h1 := (sv_le_norm (net.grad (W t)) K).trans ((div_le_iff₀ hpos).mp (hrun.grad_decay t))
    have h2 : q ^ t ≤ q := pow_le_of_le_one hq0 hq1.le ht
    have h3 : G₁ * q ^ t * ‖net.grad (W 0)‖ = f * (q ^ t * (1 - q)) := by
      simp only [hf]
      field_simp
    rw [h3] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hf0)
    exact mul_le_mul_of_nonneg_left (by linarith) hqt0
  refine hrho.trans ?_
  have hb : (G₁ * G₂) ^ 2 * q ^ (2 * t) * δ ^ 2 / p * e ^ 2 + sv (net.grad (W t)) K ^ 2 ≤
      ((G₁ * G₂ * (N / D₀) * e) ^ 2 / p + f ^ 2) * a ^ 2 := by
    have e1 : q ^ (2 * t) = (q ^ t) ^ 2 := by rw [mul_comm 2 t, pow_mul]
    have h1 : δ ^ 2 ≤ (N / D₀ * (1 - q ^ t)) ^ 2 := pow_le_pow_left₀ hδ0 hδ1 2
    have h2 : sv (net.grad (W t)) K ^ 2 ≤ (f * a) ^ 2 := pow_le_pow_left₀ hs0 hs1 2
    have h3 : (G₁ * G₂) ^ 2 * q ^ (2 * t) * δ ^ 2 / p * e ^ 2 ≤
        (G₁ * G₂) ^ 2 * q ^ (2 * t) * (N / D₀ * (1 - q ^ t)) ^ 2 / p * e ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg p)
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    calc _ ≤ _ := add_le_add h3 h2
      _ = _ := by
        rw [e1, ha]
        ring
  refine (Real.sqrt_le_sqrt hb).trans (le_of_eq ?_)
  have hW : 0 ≤ (G₁ * G₂ * (N / D₀) * e) ^ 2 / p + f ^ 2 := by positivity
  rw [Real.sqrt_mul hW, Real.sqrt_sq ha0, C₂]

/-- **Theorem 3.5** (simplified version, arXiv 2602.06208).  Let `ε ≤ ε₀`, with `ε` small in the
sense `C₁ ε < φ'(0) σ_K(W₂ᵀ Y Xᵀ) / 2` (the paper's `ε ≲ 𝒪(σ_K(W₂ᵀ Y Xᵀ))`).  Then the conclusion of
Theorem D.11 holds, with `ρ(0) ≤ C₁ ε` and `ρ(t) ≤ C₂ q^t (1 - q^t)` for `t ≥ 1`, where `C₁` does
not depend on `ε ≤ ε₀`, and `C₂` not on `t`.

Differences from the paper: those of `theorem_D_11`, and: `C₁`, `C₂` are explicit.  The paper does
not say on what its constants depend.  In this proof `C₂` depends on `η`, through `1 / (1 - q)`,
because Assumption 3.4 controls `σ_{K+1}(G₁(t))` only by the factor `q^t` of `‖G₁(t)‖_F`, not by
`1 - q^t`.  Therefore the bound on `η ρ(t)` is not of order `η`.  The paper's step size condition
`η ≲ min(1, Ω(1 / (‖W₂‖₁ + σ₁²(W₂))))` is not needed. -/
theorem theorem_3_5 (h : net.Assumptions β μ) (hc : 0 < deriv net.φ 0) (hε : 0 < ε) {ε₀ : ℝ}
    (hε₀ : ε ≤ ε₀) (hK : 0 < K) (hKm : K ≤ m) (hKd : K ≤ d) (hmd : d ≤ m) {p : ℕ}
    (hd : 2 * K + p = d) (hp : 0 < p) {W₀ : Matrix (Fin m) (Fin d) ℝ}
    (hW₀ : W₀ᵀ * W₀ = ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hsmall : net.C₁ β μ ε₀ * ε < deriv net.φ 0 * sv net.target (K - 1) / 2)
    (L₀ : Matrix (Fin m) (Fin m) ℝ) (R₀ : Matrix (Fin d) (Fin d) ℝ) :
    ∃ (U : Matrix (Fin m) (Fin (m - p) ⊕ Fin p) ℝ) (V : Matrix (Fin d) (Fin (2 * K) ⊕ Fin p) ℝ),
      Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ Vᵀ * V = 1 ∧ V * Vᵀ = 1 ∧
      (tilde U V W₀).toBlocks₁₂ = 0 ∧ (tilde U V W₀).toBlocks₂₁ = 0 ∧
      ‖(tilde U V W₀).toBlocks₂₂‖ / √p = ε ∧
      ∀ {η M G₁ G₂ G₃ q : ℝ} {W : ℕ → Matrix (Fin m) (Fin d) ℝ}
        {L : ℕ → Matrix (Fin m) (Fin m) ℝ} {R : ℕ → Matrix (Fin d) (Fin d) ℝ},
        net.Run η M G₁ G₂ G₃ q W L R → W 0 = W₀ → L 0 = L₀ → R 0 = R₀ →
        1 - deriv net.φ 0 / 2 ≤ G₃ →
        (∀ t,
          W t = U * fromBlocks (tilde U V (W t)).toBlocks₁₁ (tilde U V (W t)).toBlocks₁₂
            (tilde U V (W t)).toBlocks₂₁ (tilde U V (W t)).toBlocks₂₂ * Vᵀ ∧
          ‖(tilde U V (W (t + 1))).toBlocks₁₂ - (tilde U V (W t)).toBlocks₁₂‖ / √p ≤
            η * rho hKm hKd L R (fun t => net.grad (W t)) p t ∧
          ‖(tilde U V (W (t + 1))).toBlocks₂₁ - (tilde U V (W t)).toBlocks₂₁‖ / √p ≤
            η * rho hKm hKd L R (fun t => net.grad (W t)) p t ∧
          ‖(tilde U V (W (t + 1))).toBlocks₂₂ - (tilde U V (W t)).toBlocks₂₂‖ / √p ≤
            η * rho hKm hKd L R (fun t => net.grad (W t)) p t) ∧
        rho hKm hKd L R (fun t => net.grad (W t)) p 0 ≤ net.C₁ β μ ε₀ * ε ∧
        ∀ t, t ≠ 0 → rho hKm hKd L R (fun t => net.grad (W t)) p t ≤
          net.C₂ β μ ε M G₁ G₂ G₃ q η W₀ p * (q ^ t * (1 - q ^ t)) := by
  have hrC := rEps_le_C₁ h hc.le hε.le hε₀ hW₀
  have hr : net.rEps β μ ε W₀ < deriv net.φ 0 * sv net.target (K - 1) / 2 := hrC.trans_lt hsmall
  obtain ⟨U, V, hU, hU', hV, hV', h12, h21, h22, hrest⟩ :=
    theorem_D_11 h hc hε hK hKm hKd hmd hd hp hW₀ hr L₀ R₀
  refine ⟨U, V, hU, hU', hV, hV', h12, h21, h22, ?_⟩
  intro η M G₁ G₂ G₃ q W L R hrun hW0 hL0 hR0 hG₃
  refine ⟨fun t => ?_, ?_, ?_⟩
  · obtain ⟨a, b, c, e, -, -⟩ := hrest hrun hW0 hL0 hR0 hG₃ t
    exact ⟨a, b, c, e⟩
  · obtain ⟨-, -, -, -, e, -⟩ := hrest hrun hW0 hL0 hR0 hG₃ 0
    exact e.trans hrC
  · intro t ht
    subst hW0
    exact rho_le_C₂ h hc.le hε.le hK hKm hKd hW₀ hr hrun hG₃ ht

end Net

end Network

/-! ### Non-vacuity: an explicit run -/

section Instance

/-- The second layer `W₂ = (1, 0, 0)` of the example. -/
def exW₂ : Matrix (Fin 1) (Fin 3) ℝ := Matrix.of fun _ j => if j = 0 then 1 else 0

/-- The example: `φ = id`, `d = m = N = 3`, `K = 1`, `p = 1`, `X = I`, `Y = -W₂`. -/
def exNet : Net 3 3 3 1 where
  φ := fun x => x
  W₂ := exW₂
  X := 1
  Y := -exW₂

/-- The residual size `g(t) = (5/4) 2^{-t}` of the example. -/
def exg (t : ℕ) : ℝ := 5 / 4 * (1 / 2) ^ t

/-- The iterates of the example, starting at `W₁(0) = (1/4) I`. -/
def exW (t : ℕ) : Matrix (Fin 3) (Fin 3) ℝ := diagonal ![exg t - 1, 1 / 4, 1 / 4]

/-- The gradients of the example. -/
def exG (t : ℕ) : Matrix (Fin 3) (Fin 3) ℝ := diagonal ![exg t, 0, 0]

lemma exg_pos (t : ℕ) : 0 < exg t := by
  rw [exg]
  positivity

lemma exg_le (t : ℕ) : exg t ≤ 5 / 4 := by
  have h : (1 / 2 : ℝ) ^ t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [exg]
  linarith

lemma exNet_deriv : deriv exNet.φ = fun _ => 1 := deriv_id''

lemma exNet_residual (t : ℕ) :
    exNet.residual (exW t) = Matrix.of fun _ n => if n = 0 then exg t else 0 := by
  ext k n
  rw [Net.residual_apply]
  fin_cases k
  fin_cases n <;> simp [exNet, exW, exW₂]

lemma exNet_grad (t : ℕ) : exNet.grad (exW t) = exG t := by
  ext i j
  rw [Net.grad, exNet_residual, exNet_deriv]
  fin_cases i <;> fin_cases j <;>
    simp [exNet, exW₂, exG, Matrix.mul_apply, Matrix.hadamard_apply]

lemma norm_exG (t : ℕ) : ‖exG t‖ = exg t := by
  have h : ‖exG t‖ ^ 2 = exg t ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [exG, Fin.sum_univ_three, Matrix.diagonal_apply]
  exact (pow_left_inj₀ (norm_nonneg _) (exg_pos t).le two_ne_zero).mp h

lemma sv_zero_eq_norm {α : Type*} [Fintype α] {n : ℕ} (hn : 0 < n) {A : Matrix α (Fin n) ℝ}
    (h : A.rank ≤ 1) : sv A 0 = ‖A‖ := by
  have h1 := sq_norm_eq_sum_sq_singularValues A
  rw [Fintype.card_fin, Finset.sum_eq_single 0] at h1
  · exact (pow_left_inj₀ (sv_nonneg _ _) (norm_nonneg _) two_ne_zero).mp h1.symm
  · intro b _ hb
    have h2 : sv A b = 0 := sv_eq_zero_of_rank_le (h.trans (Nat.one_le_iff_ne_zero.mpr hb))
    simp only [sv] at h2
    rw [h2, zero_pow two_ne_zero]
  · intro h0
    exact absurd (Finset.mem_range.mpr hn) h0

lemma rank_exG (t : ℕ) : (exG t).rank ≤ 1 := by
  have e : exG t = (Matrix.of fun i (_ : Fin 1) => if i = 0 then exg t else 0 :
      Matrix (Fin 3) (Fin 1) ℝ) * exW₂ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [exG, exW₂, Matrix.mul_apply]
  rw [e]
  exact (Matrix.rank_mul_le_right _ _).trans (by simpa using Matrix.rank_le_card_height exW₂)

lemma sv_exG_zero (t : ℕ) : sv (exG t) 0 = exg t := by
  rw [sv_zero_eq_norm (by norm_num) (rank_exG t), norm_exG]

lemma sv_exG_of_pos (t : ℕ) {i : ℕ} (hi : 1 ≤ i) : sv (exG t) i = 0 :=
  sv_eq_zero_of_rank_le ((rank_exG t).trans hi)

lemma exSVD (t : ℕ) :
    IsSVD (exG t) (1 : Matrix (Fin 3) (Fin 3) ℝ) (1 : Matrix (Fin 3) (Fin 3) ℝ) where
  left := by simp
  right := by simp
  eq := by
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    have h0 := sv_exG_zero t
    have h1 := sv_exG_of_pos t (i := 1) le_rfl
    have h2 := sv_exG_of_pos t (i := 2) (by norm_num)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [singularDiag, h0, h1, h2] <;> simp [exG]

lemma exNet_target : exNet.target = diagonal ![-1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Net.target, exNet, exW₂, Matrix.mul_apply]

lemma sv_exNet_target : sv exNet.target 0 = 1 := by
  rw [sv_zero_eq_norm (by norm_num) (Net.rank_target_le exNet), exNet_target]
  have h : ‖(diagonal ![-1, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ)‖ ^ 2 = 1 ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [Fin.sum_univ_three, Matrix.diagonal_apply]
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp h

lemma sv_exW₂ : sv exNet.W₂ 0 = 1 := by
  have hr : exNet.W₂.rank ≤ 1 := by simpa using Matrix.rank_le_card_height exNet.W₂
  rw [sv_zero_eq_norm (by norm_num) hr]
  have h : ‖exNet.W₂‖ ^ 2 = 1 ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [exNet, exW₂]
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp h

lemma exRun : exNet.Run (1 / 2) (5 / 4) 1 1 1 (1 / 2) exW (fun _ => 1) (fun _ => 1) where
  η_pos := by norm_num
  q_nonneg := by norm_num
  q_lt_one := by norm_num
  gd t := by
    rw [exNet_grad]
    have e : exg (t + 1) = exg t / 2 := by
      simp only [exg, pow_succ]
      ring
    ext i j
    fin_cases i <;> fin_cases j <;> simp [exW, exG, e]
    ring
  svd t := by
    rw [exNet_grad]
    exact exSVD t
  residual_bound t := by
    rw [exNet_residual]
    refine maxNorm_le (by norm_num) fun k n => ?_
    simp only [Matrix.of_apply]
    split_ifs
    · rw [abs_of_pos (exg_pos t)]
      exact exg_le t
    · norm_num
  grad_decay t := by
    rw [exNet_grad, exNet_grad, norm_exG, norm_exG, one_mul]
    simp only [exg]
    field_simp
    simp
  sv_decay t i hi := by
    obtain rfl : i = 0 := by omega
    rw [exNet_grad, exNet_grad, norm_exG, norm_exG, sv_exG_zero, sv_exG_zero, one_mul]
  tail_gap t := by
    rw [exNet_grad, sv_exG_of_pos t le_rfl]
    simp

/-- **Non-vacuity of the hypotheses of Theorems D.11 and 3.5 of arXiv 2602.06208**: they hold
simultaneously for
`d = m = N = 3`, `K = 1`, `p = 1`, `φ = id`, `X = I`, `W₂ = (1, 0, 0)`, `Y = -W₂`,
`W₁(0) = (1/4) I`, `η = 1/2`, `q = 1/2`.  The activation is linear here; for this explicit run
`G₁(t) = diag((5/4) 2^{-t}, 0, 0)`. -/
theorem hypotheses_satisfiable :
    ∃ (net : Net 3 3 3 1) (W : ℕ → Matrix (Fin 3) (Fin 3) ℝ)
      (L R : ℕ → Matrix (Fin 3) (Fin 3) ℝ),
      net.Assumptions 1 0 ∧ 0 < deriv net.φ 0 ∧
      (W 0)ᵀ * W 0 = (1 / 4 : ℝ) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) ∧
      net.rEps 1 0 (1 / 4) (W 0) < deriv net.φ 0 * sv net.target (1 - 1) / 2 ∧
      net.Run (1 / 2) (5 / 4) 1 1 1 (1 / 2) W L R ∧ 1 - deriv net.φ 0 / 2 ≤ 1 := by
  have hc : deriv exNet.φ 0 = 1 := by rw [exNet_deriv]
  refine ⟨exNet, exW, fun _ => 1, fun _ => 1, ?_, ?_, ?_, ?_, exRun, ?_⟩
  · refine ⟨by simp [exNet], rfl, differentiable_id, ?_, fun x => ?_, fun x => ?_⟩
    · rw [exNet_deriv]
      exact differentiable_const _
    · rw [exNet_deriv]
      simp
    · rw [exNet_deriv]
      simp
  · rw [hc]
    exact one_pos
  · have e : exg 0 = 5 / 4 := by simp [exg]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [exW, e] <;> norm_num
  · rw [hc, Nat.sub_self, sv_exNet_target]
    simp only [Net.rEps, hc, sv_exW₂]
    norm_num
  · rw [hc]
    norm_num

end Instance

end

end LeanDLRA.Literature.P2602_06208
