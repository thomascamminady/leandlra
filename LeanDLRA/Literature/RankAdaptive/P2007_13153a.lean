import LeanDLRA.Matrix.Frobenius

/-!
# Results of arXiv 2007.13153: Rank-adaptive symplectic DLR model reduction of Hamiltonian systems

Matrix-level results of the structure-preserving reduced-basis method of arXiv 2007.13153, with
`J = [[0, I], [-I, 0]]` (`sJ`), `S(Z) = Z Zᵀ + Jᵀ Z Zᵀ J` (`Smat`), orthosymplectic bases `𝒰_τ`
(`Uτ`), `𝒵_τ` (`Zτ`), the horizontal space `H_U` (`Hspace`) and the basis velocity field `F` of
eq. (4.1) (`velF`):

* Lemma 5.1: `S` is symmetric PSD and skew-Hamiltonian, `S⁻¹` is skew-Hamiltonian, and
  `ker S = ker Zᵀ ∩ ker (Zᵀ J)` has even dimension;
* Lemma 5.2: `F(U, Z) ∈ H_U` for `U ∈ 𝒰_τ`, `Z ∈ 𝒵_τ` (the "if" direction; the "only if" half
  of the paper's equivalence is shown to be false for fixed `Y`);
* Sec. 6.3 / Remark 6.1: the rank update leaves the state `U Z = R` unchanged and makes
  `rank S(Z) ≤ 2n - 2`, so `Z ∉ 𝒵_τ`;
* Sec. 5 regularization (PVL factorization assumed): `S_ε` is SPD, skew-Hamiltonian,
  `‖S - S_ε‖_F ≤ √m_ε ε` with `m_ε` counting both diagonal blocks of `D` (with the printed count,
  entries of the `n × n` block only, the bound fails: `regularization_bound_block_count_fails`),
  `F_ε ∈ H_U`, and the symmetrization identity `‖F - F_*‖² = ¼ ‖F J - J F‖²` for the second
  definition `F_{ε,*} = [W | J_{2N}ᵀ W]` of the paper.

Not formalized: Lemma 4.1 (order conditions of partitioned Runge-Kutta methods up to order 3,
which require B-series theory), the Paige-Van Loan decomposition itself (Lemma 5.3, cited), the
bound on `‖F_ε S - L‖` of Sec. 5, and the first definition `F_{ε,*} = [F | J_{2N}ᵀ F]`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2007_13153

variable {m l p : Type*} [Fintype m] [DecidableEq m] [Fintype l] [DecidableEq l] [Fintype p]

/-- The standard symplectic unit `J = [[0, I], [-I, 0]]` (eq. (2.2)). -/
def sJ (l : Type*) [Fintype l] [DecidableEq l] : Matrix (l ⊕ l) (l ⊕ l) ℝ :=
  Matrix.fromBlocks 0 1 (-1) 0

lemma sJ_transpose : (sJ l)ᵀ = -sJ l := by
  simp [sJ, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]

lemma sJ_mul_sJ : sJ l * sJ l = -1 := by
  simp [sJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]

lemma sJ_transpose_mul : (sJ l)ᵀ * sJ l = 1 := by
  rw [sJ_transpose, neg_mul, sJ_mul_sJ, neg_neg]

lemma sJ_mul_transpose : sJ l * (sJ l)ᵀ = 1 := by
  rw [sJ_transpose, mul_neg, sJ_mul_sJ, neg_neg]


/-- The matrix `S(Z) = Z Zᵀ + Jᵀ Z Zᵀ J` of Section 5 (here `Z : ℝ^{2n × p}`, `J = J_{2n}`). -/
noncomputable def Smat (Z : Matrix (l ⊕ l) p ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ :=
  Z * Zᵀ + (sJ l)ᵀ * (Z * Zᵀ) * sJ l

lemma Smat_transpose (Z : Matrix (l ⊕ l) p ℝ) : (Smat Z)ᵀ = Smat Z := by
  simp [Smat, Matrix.transpose_mul, Matrix.mul_assoc]

/-- A real-linear map `f` on a finite-dimensional space with `f ∘ f = -id` forces even dimension. -/
lemma even_finrank_of_comp_eq_neg_id {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (f : V →ₗ[ℝ] V) (hf : f ∘ₗ f = -LinearMap.id) :
    Even (Module.finrank ℝ V) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have h := congrArg LinearMap.det hf
  rw [LinearMap.det_comp] at h
  have h2 : LinearMap.det (-LinearMap.id : V →ₗ[ℝ] V) = (-1) ^ Module.finrank ℝ V := by
    have : (-LinearMap.id : V →ₗ[ℝ] V) = (-1 : ℝ) • LinearMap.id := by simp
    rw [this, LinearMap.det_smul]; simp
  rw [h2, hodd.neg_one_pow] at h
  nlinarith [mul_self_nonneg (LinearMap.det f)]


/-- **arXiv 2007.13153, Lemma 5.1 (first part).**  For every `Z ∈ ℝ^{2n × p}`, the matrix
`S = Z Zᵀ + Jᵀ Z Zᵀ J` is symmetric positive semi-definite and skew-Hamiltonian, `S J = J Sᵀ`.
Difference from the paper: the assumption `p ≥ 2n` is not needed and is dropped. -/
theorem lemma_5_1_posSemidef (Z : Matrix (l ⊕ l) p ℝ) :
    (Smat Z).PosSemidef ∧ (Smat Z) * sJ l = sJ l * (Smat Z)ᵀ := by
  refine ⟨?_, ?_⟩
  · have h1 : (Z * Zᵀ).PosSemidef := by
      simpa using Matrix.posSemidef_self_mul_conjTranspose Z
    have h2 := h1.conjTranspose_mul_mul_same (sJ l)
    simpa [Smat, Matrix.conjTranspose_eq_transpose_of_trivial] using h1.add h2
  · rw [Smat_transpose]
    unfold Smat
    generalize Z * Zᵀ = A
    have h1 : (sJ l)ᵀ * A * sJ l * sJ l = -((sJ l)ᵀ * A) := by
      rw [Matrix.mul_assoc _ _ (sJ l), sJ_mul_sJ]; simp
    have h2 : sJ l * ((sJ l)ᵀ * A * sJ l) = A * sJ l := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, sJ_mul_transpose, Matrix.one_mul]
    rw [Matrix.add_mul, Matrix.mul_add, h1, h2, sJ_transpose]
    simp only [Matrix.neg_mul, neg_neg]
    abel

/-- **arXiv 2007.13153, Lemma 5.1 (inverse).**  If `S` is invertible (full rank `2n`, i.e.
`Z ∈ 𝒵_τ`), then `S⁻¹` is skew-Hamiltonian: `S⁻¹ J = J (S⁻¹)ᵀ`.  Here invertibility is phrased as
`IsUnit S.det`; `lemma_5_1_isUnit_of_rank` converts from the rank hypothesis. -/
theorem lemma_5_1_inv (Z : Matrix (l ⊕ l) p ℝ) (h : IsUnit (Smat Z).det) :
    (Smat Z)⁻¹ * sJ l = sJ l * ((Smat Z)⁻¹)ᵀ := by
  have hsk := (lemma_5_1_posSemidef Z).2
  rw [Smat_transpose] at hsk
  rw [Matrix.transpose_nonsing_inv, Smat_transpose]
  calc (Smat Z)⁻¹ * sJ l = (Smat Z)⁻¹ * (sJ l * (Smat Z) * (Smat Z)⁻¹) := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h, Matrix.mul_one]
    _ = ((Smat Z)⁻¹ * (Smat Z)) * sJ l * (Smat Z)⁻¹ := by
        rw [← hsk]; simp only [Matrix.mul_assoc]
    _ = sJ l * (Smat Z)⁻¹ := by
        rw [Matrix.nonsing_inv_mul _ h, Matrix.one_mul]

/-- **arXiv 2007.13153, Lemma 5.1 (rank hypothesis).**  `rank S = 2n` is the same as `S`
being invertible (used to translate the paper's "if `S` has rank `2n`"). -/
theorem lemma_5_1_isUnit_of_rank (Z : Matrix (l ⊕ l) p ℝ)
    (h : (Smat Z).rank = Fintype.card (l ⊕ l)) : IsUnit (Smat Z).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hSv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hrn := LinearMap.finrank_range_add_finrank_ker (Smat Z).mulVecLin
  have hk : 0 < Module.finrank ℝ (LinearMap.ker (Smat Z).mulVecLin) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact ⟨⟨v, by simpa using hSv⟩, by simpa using hv⟩
  have : Module.finrank ℝ (LinearMap.range (Smat Z).mulVecLin) = Fintype.card (l ⊕ l) := h
  rw [this, Module.finrank_fintype_fun_eq_card] at hrn
  omega

/-- **arXiv 2007.13153, Lemma 5.1 (null space).**  `ker S = ker Zᵀ ∩ ker (Zᵀ J)` and this
null space has even dimension.  (For the paper's pairs `(v, Jv)`: if `v` and `Jv` lie in
`ker Zᵀ`, then `v ∈ ker Zᵀ ∩ ker(Zᵀ J) = ker S`.) -/
theorem lemma_5_1_ker (Z : Matrix (l ⊕ l) p ℝ) :
    LinearMap.ker (Smat Z).mulVecLin =
        LinearMap.ker Zᵀ.mulVecLin ⊓ LinearMap.ker (Zᵀ * sJ l).mulVecLin ∧
      Even (Module.finrank ℝ (LinearMap.ker (Smat Z).mulVecLin)) := by
  have nn : ∀ {ι : Type _} [Fintype ι] (w : ι → ℝ), 0 ≤ w ⬝ᵥ w := fun w =>
    Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have e1 : ∀ w : l ⊕ l → ℝ, w ⬝ᵥ ((Z * Zᵀ) *ᵥ w) = (Zᵀ *ᵥ w) ⬝ᵥ (Zᵀ *ᵥ w) := by
    intro w
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have hq : ∀ v : l ⊕ l → ℝ, v ⬝ᵥ (Smat Z *ᵥ v) =
      (Zᵀ *ᵥ v) ⬝ᵥ (Zᵀ *ᵥ v) + (Zᵀ *ᵥ (sJ l *ᵥ v)) ⬝ᵥ (Zᵀ *ᵥ (sJ l *ᵥ v)) := by
    intro v
    have e2 : v ⬝ᵥ (((sJ l)ᵀ * (Z * Zᵀ) * sJ l) *ᵥ v) =
        (Zᵀ *ᵥ (sJ l *ᵥ v)) ⬝ᵥ (Zᵀ *ᵥ (sJ l *ᵥ v)) := by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, e1]
    unfold Smat
    rw [Matrix.add_mulVec, dotProduct_add, e1, e2]
  have hker : LinearMap.ker (Smat Z).mulVecLin =
      LinearMap.ker Zᵀ.mulVecLin ⊓ LinearMap.ker (Zᵀ * sJ l).mulVecLin := by
    ext v
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Submodule.mem_inf]
    rw [← Matrix.mulVec_mulVec]
    constructor
    · intro h
      have := hq v
      rw [h, dotProduct_zero] at this
      have h1 : (Zᵀ *ᵥ v) ⬝ᵥ (Zᵀ *ᵥ v) = 0 := by
        linarith [nn (Zᵀ *ᵥ v), nn (Zᵀ *ᵥ (sJ l *ᵥ v))]
      have h2 : (Zᵀ *ᵥ (sJ l *ᵥ v)) ⬝ᵥ (Zᵀ *ᵥ (sJ l *ᵥ v)) = 0 := by
        linarith [nn (Zᵀ *ᵥ v), nn (Zᵀ *ᵥ (sJ l *ᵥ v))]
      exact ⟨dotProduct_self_eq_zero.mp h1, dotProduct_self_eq_zero.mp h2⟩
    · rintro ⟨h1, h2⟩
      unfold Smat
      rw [Matrix.add_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, h2]
      simp
  refine ⟨hker, ?_⟩
  have hinv : ∀ v ∈ LinearMap.ker (Smat Z).mulVecLin,
      (sJ l).mulVecLin v ∈ LinearMap.ker (Smat Z).mulVecLin := by
    intro v hv
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    have hsk := (lemma_5_1_posSemidef Z).2
    rw [Smat_transpose] at hsk
    rw [Matrix.mulVec_mulVec, hsk, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  refine even_finrank_of_comp_eq_neg_id ((sJ l).mulVecLin.restrict hinv) ?_
  apply LinearMap.ext
  rintro ⟨v, hv⟩
  apply Subtype.ext
  change (sJ l).mulVecLin ((sJ l).mulVecLin v) = -v
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, sJ_mul_sJ, Matrix.neg_mulVec,
    Matrix.one_mulVec]


/-! ### Orthosymplectic bases, the velocity field `F`, and the horizontal space -/

variable (m l) in
/-- The set `𝒰_τ` of orthosymplectic `2N × 2n` matrices, eq. (3.3):
`Uᵀ U = I`, `Uᵀ J_{2N} U = J_{2n}`. -/
def Uτ (U : Matrix (m ⊕ m) (l ⊕ l) ℝ) : Prop :=
  Uᵀ * U = 1 ∧ Uᵀ * sJ m * U = sJ l

/-- The set `𝒵_τ`, eq. (3.3): `Z ∈ ℝ^{2n × p}` with `rank (Z Zᵀ + Jᵀ Z Zᵀ J) = 2n`. -/
def Zτ (Z : Matrix (l ⊕ l) p ℝ) : Prop := (Smat Z).rank = Fintype.card (l ⊕ l)

/-- The horizontal space `H_U = {X : Xᵀ U = 0, X J_{2n} = J_{2N} X}`, eq. (4.2). -/
def Hspace (U : Matrix (m ⊕ m) (l ⊕ l) ℝ) : Set (Matrix (m ⊕ m) (l ⊕ l) ℝ) :=
  {X | Xᵀ * U = 0 ∧ X * sJ l = sJ m * X}

/-- The velocity field of the reduced basis, eq. (4.1), with the matrix `S` replaced by an
arbitrary `S'` (for the paper's `F` take `S' = S(Z)`, for the regularized `F_ε` take `S' = S_ε`):
`(I - U Uᵀ)(J_{2N} Y Zᵀ - Y Zᵀ J_{2n}ᵀ) S'⁻¹`. -/
noncomputable def velF' (S' : Matrix (l ⊕ l) (l ⊕ l) ℝ) (U : Matrix (m ⊕ m) (l ⊕ l) ℝ)
    (Z : Matrix (l ⊕ l) p ℝ) (Y : Matrix (m ⊕ m) p ℝ) : Matrix (m ⊕ m) (l ⊕ l) ℝ :=
  (1 - U * Uᵀ) * (sJ m * Y * Zᵀ - Y * Zᵀ * (sJ l)ᵀ) * S'⁻¹

/-- The velocity field `F(U, Z; η_h)` of eq. (4.1) (with `Y = ∇H(UZ)` an arbitrary `2N × p`
matrix): `(I - U Uᵀ)(J_{2N} Y Zᵀ - Y Zᵀ J_{2n}ᵀ) S(Z)⁻¹`. -/
noncomputable def velF (U : Matrix (m ⊕ m) (l ⊕ l) ℝ) (Z : Matrix (l ⊕ l) p ℝ)
    (Y : Matrix (m ⊕ m) p ℝ) : Matrix (m ⊕ m) (l ⊕ l) ℝ :=
  velF' (Smat Z) U Z Y

/-- Orthosymplectic matrices intertwine the symplectic units: `J_{2N} U = U J_{2n}`. -/
lemma Uτ.J_mul {U : Matrix (m ⊕ m) (l ⊕ l) ℝ} (hU : Uτ m l U) : sJ m * U = U * sJ l := by
  obtain ⟨h1, h2⟩ := hU
  have hat : (sJ m)ᵀ * sJ m = 1 := sJ_transpose_mul
  have hbt : (sJ l)ᵀ * sJ l = 1 := sJ_transpose_mul
  have h2t : Uᵀ * (sJ m)ᵀ * U = (sJ l)ᵀ := by
    have := congrArg Matrix.transpose h2
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  have hD : (sJ m * U - U * sJ l)ᵀ * (sJ m * U - U * sJ l) = 0 := by
    have t1 : Uᵀ * (sJ m)ᵀ * (sJ m * U) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (sJ m)ᵀ, hat, Matrix.one_mul, h1]
    have t2 : Uᵀ * (sJ m)ᵀ * (U * sJ l) = 1 := by
      rw [← Matrix.mul_assoc, h2t, hbt]
    have t3 : (sJ l)ᵀ * Uᵀ * (sJ m * U) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, h2, hbt]
    have t4 : (sJ l)ᵀ * Uᵀ * (U * sJ l) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, h1, Matrix.one_mul, hbt]
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_sub, t1, t2, t3, t4]
    simp
  have : sJ m * U - U * sJ l = 0 := by
    rw [← Matrix.conjTranspose_mul_self_eq_zero]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hD
  exact sub_eq_zero.mp this

/-- The orthogonal projector `U Uᵀ` commutes with `J_{2N}`. -/
lemma Uτ.proj_comm {U : Matrix (m ⊕ m) (l ⊕ l) ℝ} (hU : Uτ m l U) :
    sJ m * (U * Uᵀ) = (U * Uᵀ) * sJ m := by
  have h := hU.J_mul
  have h' : Uᵀ * sJ m = sJ l * Uᵀ := by
    have := congrArg Matrix.transpose h
    simp only [Matrix.transpose_mul, sJ_transpose, Matrix.neg_mul,
      Matrix.mul_neg, neg_inj] at this
    simpa using this
  rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, Matrix.mul_assoc, h']


/-- The matrix `A = J_{2N} Y Zᵀ - Y Zᵀ J_{2n}ᵀ` satisfies `A J_{2n} = J_{2N} A`. -/
lemma A_comm (Z : Matrix (l ⊕ l) p ℝ) (Y : Matrix (m ⊕ m) p ℝ) :
    (sJ m * Y * Zᵀ - Y * Zᵀ * (sJ l)ᵀ) * sJ l = sJ m * (sJ m * Y * Zᵀ - Y * Zᵀ * (sJ l)ᵀ) := by
  have h1 : sJ m * (sJ m * Y * Zᵀ) = -(Y * Zᵀ) := by
    simp only [← Matrix.mul_assoc, sJ_mul_sJ, Matrix.neg_mul, Matrix.one_mul]
  have h2 : Y * Zᵀ * (sJ l)ᵀ * sJ l = Y * Zᵀ := by
    rw [Matrix.mul_assoc _ _ (sJ l), sJ_transpose_mul, Matrix.mul_one]
  rw [Matrix.sub_mul, Matrix.mul_sub, h1, h2, sJ_transpose]
  simp only [Matrix.mul_neg, Matrix.mul_assoc]
  abel

/-- The field `(I - U Uᵀ) (…) S'⁻¹` is always orthogonal to `U`: `F'ᵀ U = 0` (for any `S'`,
invertible or not, whenever `Uᵀ U = I`). -/
lemma velF'_transpose_mul {U : Matrix (m ⊕ m) (l ⊕ l) ℝ} (hU : Uᵀ * U = 1)
    (S' : Matrix (l ⊕ l) (l ⊕ l) ℝ) (Z : Matrix (l ⊕ l) p ℝ) (Y : Matrix (m ⊕ m) p ℝ) :
    (velF' S' U Z Y)ᵀ * U = 0 := by
  have hP : (1 - U * Uᵀ)ᵀ * U = 0 := by
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_one, Matrix.sub_mul, Matrix.mul_assoc, hU, Matrix.one_mul,
      Matrix.mul_one, sub_self]
  simp only [velF', Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hP, Matrix.mul_zero, Matrix.mul_zero]

/-- **Core of arXiv 2007.13153, Lemma 5.2.**  For an orthosymplectic `U` and *any* invertible
`S'` commuting with `J_{2n}` (in particular `S(Z)` and every skew-Hamiltonian regularization
`S_ε`), the field `(I - U Uᵀ)(J Y Zᵀ - Y Zᵀ Jᵀ) S'⁻¹` lies in the horizontal space `H_U`. -/
theorem velF'_mem_Hspace {U : Matrix (m ⊕ m) (l ⊕ l) ℝ} (hU : Uτ m l U)
    {S' : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hdet : IsUnit S'.det) (hJ : S' * sJ l = sJ l * S')
    (Z : Matrix (l ⊕ l) p ℝ) (Y : Matrix (m ⊕ m) p ℝ) :
    velF' S' U Z Y ∈ Hspace U := by
  refine ⟨?_, ?_⟩
  · exact velF'_transpose_mul hU.1 S' Z Y
  · have hinv : S'⁻¹ * sJ l = sJ l * S'⁻¹ := by
      calc S'⁻¹ * sJ l = S'⁻¹ * (sJ l * S' * S'⁻¹) := by
            rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
        _ = (S'⁻¹ * S') * sJ l * S'⁻¹ := by rw [← hJ]; simp only [Matrix.mul_assoc]
        _ = sJ l * S'⁻¹ := by rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
    have hP : (1 - U * Uᵀ) * sJ m = sJ m * (1 - U * Uᵀ) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hU.proj_comm]
    have h1 : (1 - U * Uᵀ) * (sJ m * Y * Zᵀ - Y * Zᵀ * (sJ l)ᵀ) * S'⁻¹ * sJ l =
        (1 - U * Uᵀ) * ((sJ m * Y * Zᵀ - Y * Zᵀ * (sJ l)ᵀ) * sJ l) * S'⁻¹ := by
      simp only [Matrix.mul_assoc, hinv]
    rw [velF', h1, A_comm, ← Matrix.mul_assoc (1 - U * Uᵀ), hP]
    simp only [Matrix.mul_assoc]

/-- **arXiv 2007.13153, Lemma 5.2 (direction "if").**  For `U ∈ 𝒰_τ` and `Z ∈ 𝒵_τ` (and any
`Y ∈ ℝ^{2N × p}`, in the paper `Y = ∇H(UZ)`), the velocity field `F(U, Z) = (I - U Uᵀ)
(J_{2N} Y Zᵀ - Y Zᵀ J_{2n}ᵀ) S⁻¹` lies in the horizontal space `H_U`.  Difference from the paper:
only the "if" direction is stated (the one the paper uses); see `lemma_5_2_converse_fails` for why
the "only if" direction cannot hold for a fixed `Y`. -/
theorem lemma_5_2 {U : Matrix (m ⊕ m) (l ⊕ l) ℝ} {Z : Matrix (l ⊕ l) p ℝ}
    (hU : Uτ m l U) (hZ : Zτ Z) (Y : Matrix (m ⊕ m) p ℝ) : velF U Z Y ∈ Hspace U := by
  refine velF'_mem_Hspace hU (lemma_5_1_isUnit_of_rank Z hZ) ?_ Z Y
  have := (lemma_5_1_posSemidef Z).2
  rwa [Smat_transpose] at this


/-- **arXiv 2007.13153, Lemma 5.2 (the "only if" half is false as stated).**  The paper states
`F(U, Z) ∈ H_U` as an "if and only if" `U ∈ 𝒰_τ`, `Z ∈ 𝒵_τ`.  For a fixed `Y` the converse
fails: with `Y = 0` and `U = 0` (which is not orthosymplectic) one has `F = 0 ∈ H_U`, while
`Z = 1 ∈ 𝒵_τ`.  This is also a counterexample in the paper's setting `Y = ∇H(U Z)`, for any
Hamiltonian with `∇H(0) = 0` (e.g. `H = 0`).  Only the "if" direction (`lemma_5_2`) is true in
general, and it is the one the paper uses. -/
theorem lemma_5_2_converse_fails [Nonempty l] :
    ∃ (U : Matrix (m ⊕ m) (l ⊕ l) ℝ) (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ)
      (Y : Matrix (m ⊕ m) (l ⊕ l) ℝ), Zτ Z ∧ ¬ Uτ m l U ∧ velF U Z Y ∈ Hspace U := by
  refine ⟨0, 1, 0, ?_, ?_, ?_⟩
  · have h : Smat (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) = (2 : ℝ) • 1 := by
      simp [Smat, sJ_transpose_mul, two_smul]
    unfold Zτ
    apply Matrix.rank_of_det_ne_zero
    rw [h, Matrix.det_smul]
    simp
  · rintro ⟨h, -⟩
    simp only [Matrix.transpose_zero, Matrix.mul_zero] at h
    have := congrFun (congrFun h (Sum.inl (Classical.arbitrary l)))
      (Sum.inl (Classical.arbitrary l))
    simp at this
  · simp [velF, velF', Hspace]


/-- Non-vacuity: the identity is an orthosymplectic basis (the case `n = N`). -/
example : Uτ m m (1 : Matrix (m ⊕ m) (m ⊕ m) ℝ) := by simp [Uτ]

/-- Orthosymplectic matrices also satisfy `Uᵀ J_{2N} = J_{2n} Uᵀ`. -/
lemma Uτ.transpose_mul_J {U : Matrix (m ⊕ m) (l ⊕ l) ℝ} (hU : Uτ m l U) :
    Uᵀ * sJ m = sJ l * Uᵀ := by
  have := congrArg Matrix.transpose hU.J_mul
  simp only [Matrix.transpose_mul, sJ_transpose, Matrix.neg_mul, Matrix.mul_neg, neg_inj] at this
  simpa using this

/-- Transport of `S` along a map `B` that intertwines the symplectic units. -/
lemma Smat_map {l₀ : Type*} [Fintype l₀] [DecidableEq l₀] (B : Matrix (l ⊕ l) (l₀ ⊕ l₀) ℝ)
    (hT : (sJ l)ᵀ * B = B * (sJ l₀)ᵀ) (hT2 : Bᵀ * sJ l = sJ l₀ * Bᵀ)
    (Z₀ : Matrix (l₀ ⊕ l₀) p ℝ) : Smat (B * Z₀) = B * Smat Z₀ * Bᵀ := by
  have e : (B * Z₀) * (B * Z₀)ᵀ = B * (Z₀ * Z₀ᵀ) * Bᵀ := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have e2 : (sJ l)ᵀ * (B * (Z₀ * Z₀ᵀ) * Bᵀ) * sJ l =
      B * ((sJ l₀)ᵀ * (Z₀ * Z₀ᵀ) * sJ l₀) * Bᵀ := by
    calc (sJ l)ᵀ * (B * (Z₀ * Z₀ᵀ) * Bᵀ) * sJ l
        = ((sJ l)ᵀ * B) * (Z₀ * Z₀ᵀ) * (Bᵀ * sJ l) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hT, hT2]; simp only [Matrix.mul_assoc]
  unfold Smat
  rw [e, e2, Matrix.mul_add, Matrix.add_mul]

/-- **arXiv 2007.13153, Sec. 6.3 and Remark 6.1 (rank update).**  Let `U₀ ∈ 𝒰_{τ-1}` (with
`2n-2` columns), `Z₀` arbitrary, and `R = U₀ Z₀` the current reduced state.  Let `U ∈ 𝒰_τ` be an
orthosymplectic basis with two more columns whose span contains the columns of `U₀`
(`U₀ = U C`; this is what the construction `[U₀ | e | J₂Nᵀ e]` followed by symplectic
Gram-Schmidt delivers).  Put `Z = Uᵀ R`.  Then (i) the state is unchanged, `U Z = R` (so every
invariant of the Hamiltonian system is conserved by the rank update), (ii)
`rank S(Z) ≤ min {rank (Uᵀ U₀), rank S(Z₀)}`, hence `≤ 2n-2`, and (iii) `Z ∉ 𝒵_τ`, so the
velocity field `F` of (4.1) is not defined and the regularization of Section 5 is needed.
Differences from the paper: the construction of `U` from the error vector `e` is not formalized;
`U` is any orthosymplectic basis extending `U₀` by one symplectic pair of columns
(`card l = card l₀ + 1`). -/
theorem rank_update {l₀ : Type*} [Fintype l₀] [DecidableEq l₀]
    {U₀ : Matrix (m ⊕ m) (l₀ ⊕ l₀) ℝ} {U : Matrix (m ⊕ m) (l ⊕ l) ℝ}
    (hU₀ : Uτ m l₀ U₀) (hU : Uτ m l U) (hext : ∃ C : Matrix (l ⊕ l) (l₀ ⊕ l₀) ℝ, U₀ = U * C)
    (hcard : Fintype.card l = Fintype.card l₀ + 1) (Z₀ : Matrix (l₀ ⊕ l₀) p ℝ) :
    U * (Uᵀ * (U₀ * Z₀)) = U₀ * Z₀ ∧
    (Smat (Uᵀ * (U₀ * Z₀))).rank ≤ min (Uᵀ * U₀).rank (Smat Z₀).rank ∧
    ¬ Zτ (Uᵀ * (U₀ * Z₀)) := by
  obtain ⟨C, hC⟩ := hext
  have hproj : U * (Uᵀ * U₀) = U₀ := by
    rw [hC, ← Matrix.mul_assoc Uᵀ U C, hU.1, Matrix.one_mul]
  have hBJ : (Uᵀ * U₀) * sJ l₀ = sJ l * (Uᵀ * U₀) := by
    rw [Matrix.mul_assoc, ← hU₀.J_mul, ← Matrix.mul_assoc, hU.transpose_mul_J, Matrix.mul_assoc]
  have hBJT : (sJ l)ᵀ * (Uᵀ * U₀) = (Uᵀ * U₀) * (sJ l₀)ᵀ := by
    calc (sJ l)ᵀ * (Uᵀ * U₀) = (sJ l)ᵀ * (Uᵀ * U₀) * (sJ l₀ * (sJ l₀)ᵀ) := by
          rw [sJ_mul_transpose, Matrix.mul_one]
      _ = (sJ l)ᵀ * ((Uᵀ * U₀) * sJ l₀) * (sJ l₀)ᵀ := by simp only [Matrix.mul_assoc]
      _ = ((sJ l)ᵀ * sJ l) * (Uᵀ * U₀) * (sJ l₀)ᵀ := by rw [hBJ]; simp only [Matrix.mul_assoc]
      _ = (Uᵀ * U₀) * (sJ l₀)ᵀ := by rw [sJ_transpose_mul, Matrix.one_mul]
  have hBJ2 : (Uᵀ * U₀)ᵀ * sJ l = sJ l₀ * (Uᵀ * U₀)ᵀ := by
    have := congrArg Matrix.transpose hBJT
    simpa [Matrix.transpose_mul] using this
  have hS : Smat (Uᵀ * (U₀ * Z₀)) = (Uᵀ * U₀) * Smat Z₀ * (Uᵀ * U₀)ᵀ := by
    rw [← Matrix.mul_assoc]
    exact Smat_map _ hBJT hBJ2 Z₀
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc Uᵀ U₀ Z₀, ← Matrix.mul_assoc, hproj]
  · rw [hS]
    refine le_min ?_ ?_
    · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _)
    · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · intro hZ
    unfold Zτ at hZ
    rw [hS] at hZ
    have h1 : (Uᵀ * U₀ * Smat Z₀ * (Uᵀ * U₀)ᵀ).rank ≤ Fintype.card (l₀ ⊕ l₀) :=
      ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans
        (Matrix.rank_le_card_width _)
    have h2 : Fintype.card (l ⊕ l) = Fintype.card (l₀ ⊕ l₀) + 2 := by
      simp only [Fintype.card_sum]; omega
    omega

/-- Non-vacuity of `rank_update`: the smallest instance, `U₀` empty (rank `0`), `U = 1` on one
symplectic pair, `N = 1`. -/
example (Z₀ : Matrix (Empty ⊕ Empty) p ℝ) :
    ¬ Zτ ((1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ)ᵀ *
      ((0 : Matrix (Unit ⊕ Unit) (Empty ⊕ Empty) ℝ) * Z₀)) := by
  refine (rank_update (m := Unit) (l := Unit) (l₀ := Empty) (U₀ := 0) (U := 1) ?_ ?_ ?_ ?_ Z₀).2.2
  · constructor <;> exact Subsingleton.elim _ _
  · simp [Uτ]
  · exact ⟨0, by simp⟩
  · simp

/-! ### The `ε`-regularization of Section 5 (PVL form) -/

/-- The block-doubled diagonal matrix `D = diag (d, d)`, the diagonal factor in the PVL form
`S = Q D Qᵀ` of a symmetric skew-Hamiltonian matrix (Section 5, below Lemma 5.3). -/
noncomputable def dblDiag (d : l → ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ :=
  Matrix.diagonal (Sum.elim d d)

/-- The `ε`-regularization `S_ε = Q D_ε Qᵀ` of `S = Q D Qᵀ`: every diagonal entry of `D` below
`ε` is replaced by `ε` (so `(D_ε)_i = max (D_i) ε`). -/
noncomputable def Sreg (Q : Matrix (l ⊕ l) (l ⊕ l) ℝ) (d : l → ℝ) (ε : ℝ) :
    Matrix (l ⊕ l) (l ⊕ l) ℝ :=
  Q * dblDiag (fun i => max (d i) ε) * Qᵀ

lemma dblDiag_comm_sJ (d : l → ℝ) : dblDiag d * sJ l = sJ l * dblDiag d := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> by_cases h : i = j <;>
    simp [dblDiag, sJ, Matrix.fromBlocks, Matrix.diagonal_apply, Matrix.mul_apply,
      h]

lemma orth_mul_transpose {Q : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hQ : Qᵀ * Q = 1) : Q * Qᵀ = 1 :=
  mul_eq_one_comm.mp hQ

lemma Sreg_transpose (Q : Matrix (l ⊕ l) (l ⊕ l) ℝ) (d : l → ℝ) (ε : ℝ) :
    (Sreg Q d ε)ᵀ = Sreg Q d ε := by
  simp [Sreg, dblDiag, Matrix.transpose_mul, Matrix.mul_assoc]

/-- **arXiv 2007.13153, Sec. 5 (`ε`-regularization), matrix part.**  Let `Z ∈ ℝ^{2n × p}` and
suppose `S(Z) = Q D Qᵀ` with `Q` orthogonal and symplectic (`Q ∈ 𝒰` on `2n × 2n`) and
`D = diag (d, d)` (the PVL form of Lemma 5.3, which is *assumed* here, as it is cited, not
proved, in the paper).  For `ε > 0` the matrix `S_ε = Q D_ε Qᵀ`, `(D_ε)_i = max (D_i) ε`, is
symmetric positive definite and skew-Hamiltonian, and
`‖S − S_ε‖_F ≤ √m_ε · ε`, where `m_ε` is the number of diagonal entries of `D` (that is, of
`Sum.elim d d`, so counted in both blocks) that are smaller than `ε`.
Difference from the paper: `m_ε` counts entries of the full `2n × 2n` diagonal `D`, i.e. twice
the paper's count of entries of the `n × n` block `D_{n_τ}` (p. 8).  With the paper's count the
bound fails (`regularization_bound_block_count_fails`); since the count here is twice the paper's,
this theorem gives the paper's bound with an extra factor `√2`. -/
theorem regularization_bound (Z : Matrix (l ⊕ l) p ℝ) {Q : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hQ : Uτ l l Q) {d : l → ℝ} (hfac : Smat Z = Q * dblDiag d * Qᵀ) {ε : ℝ} (hε : 0 < ε) :
    (Sreg Q d ε).PosDef ∧ Sreg Q d ε * sJ l = sJ l * (Sreg Q d ε)ᵀ ∧
      ‖Smat Z - Sreg Q d ε‖ ≤
        Real.sqrt ((Finset.univ.filter (fun i : l ⊕ l => Sum.elim d d i < ε)).card) * ε := by
  have hQQ := orth_mul_transpose hQ.1
  have hunit : IsUnit Q := ⟨⟨Q, Qᵀ, hQQ, hQ.1⟩, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · have hD : (dblDiag (fun i => max (d i) ε)).PosDef := by
      unfold dblDiag
      rw [Matrix.posDef_diagonal_iff]
      rintro (i | i) <;> simp [lt_max_of_lt_right hε]
    have := (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := dblDiag (fun i => max (d i) ε))
      hunit).mpr hD
    simpa [Sreg, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using this
  · rw [Sreg_transpose]
    unfold Sreg
    calc Q * dblDiag (fun i => max (d i) ε) * Qᵀ * sJ l
        = Q * dblDiag (fun i => max (d i) ε) * (Qᵀ * sJ l) := by rw [Matrix.mul_assoc]
      _ = (Q * sJ l) * dblDiag (fun i => max (d i) ε) * Qᵀ := by
          rw [hQ.transpose_mul_J, ← Matrix.mul_assoc, Matrix.mul_assoc Q, dblDiag_comm_sJ,
            ← Matrix.mul_assoc, Matrix.mul_assoc _ _ (dblDiag _)]
      _ = sJ l * (Q * dblDiag (fun i => max (d i) ε) * Qᵀ) := by
          rw [← hQ.J_mul]; simp only [Matrix.mul_assoc]
  · -- nonnegativity of the diagonal, from `S ⪰ 0`
    have hnn : ∀ i : l ⊕ l, 0 ≤ Sum.elim d d i := by
      have hS := (lemma_5_1_posSemidef Z).1
      have h2 := hS.conjTranspose_mul_mul_same Q
      rw [hfac] at h2
      have e : Qᴴ * (Q * dblDiag d * Qᵀ) * Q = dblDiag d := by
        rw [Matrix.conjTranspose_eq_transpose_of_trivial]
        calc Qᵀ * (Q * dblDiag d * Qᵀ) * Q = (Qᵀ * Q) * dblDiag d * (Qᵀ * Q) := by
              simp only [Matrix.mul_assoc]
          _ = dblDiag d := by rw [hQ.1]; simp
      rw [e] at h2
      intro i
      have := h2.diag_nonneg (i := i)
      rcases i with i | i <;> simpa [dblDiag] using this
    have hdiff : Smat Z - Sreg Q d ε =
        Q * Matrix.diagonal (fun i : l ⊕ l => Sum.elim d d i - max (Sum.elim d d i) ε) * Qᵀ := by
      have hD : dblDiag d - dblDiag (fun i => max (d i) ε) =
          Matrix.diagonal (fun i : l ⊕ l => Sum.elim d d i - max (Sum.elim d d i) ε) := by
        unfold dblDiag
        ext i j
        rcases i with i | i <;> rcases j with j | j <;> by_cases h : i = j <;>
          simp [h]
      rw [hfac, Sreg, ← Matrix.sub_mul, ← Matrix.mul_sub, hD]
    rw [hdiff, Frobenius.norm_mul_transpose_of_orthonormal hQ.1,
      Frobenius.norm_mul_of_orthonormal hQ.1]
    have hsq : ‖Matrix.diagonal (fun i : l ⊕ l => Sum.elim d d i - max (Sum.elim d d i) ε)‖ ^ 2 ≤
        (Finset.univ.filter (fun i : l ⊕ l => Sum.elim d d i < ε)).card * ε ^ 2 := by
      rw [Frobenius.norm_sq_eq_sum]
      have h1 : ∀ i : l ⊕ l, ∑ j : l ⊕ l,
          (Matrix.diagonal (fun i : l ⊕ l => Sum.elim d d i - max (Sum.elim d d i) ε) i j) ^ 2 =
          (Sum.elim d d i - max (Sum.elim d d i) ε) ^ 2 := by
        intro i
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj; simp [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
        · simp
      simp_rw [h1]
      calc ∑ i : l ⊕ l, (Sum.elim d d i - max (Sum.elim d d i) ε) ^ 2
          ≤ ∑ i : l ⊕ l, (if Sum.elim d d i < ε then ε ^ 2 else 0) := by
            apply Finset.sum_le_sum
            intro i _
            by_cases hi : Sum.elim d d i < ε
            · simp only [hi, ↓reduceIte]; rw [max_eq_right hi.le]
              nlinarith [hnn i]
            · simp only [hi, ↓reduceIte]; rw [max_eq_left (not_lt.mp hi)]
              simp
        _ = _ := by
            rw [← Finset.sum_filter]; simp
    calc _ = Real.sqrt (‖Matrix.diagonal (fun i : l ⊕ l => Sum.elim d d i
              - max (Sum.elim d d i) ε)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (_ * ε ^ 2) := Real.sqrt_le_sqrt hsq
      _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hε.le]

/-- **arXiv 2007.13153, Sec. 5 (p. 8): `‖S - S_ε‖_F ≤ √m_ε ε` fails with the printed count.**
If `m_ε` is the number of entries of the `n × n` block `D_{n_τ}` that are smaller than `ε`, as
printed, the bound can fail: for `n = 1`, `Z = 0`, `Q = I`, `D = 0` and `ε = 1` one has `m_ε = 1`
but `‖S - S_ε‖_F = ‖I₂‖_F = √2 > 1`.  With both diagonal blocks counted the bound holds
(`regularization_bound`). -/
theorem regularization_bound_block_count_fails :
    ∃ (Z : Matrix (Unit ⊕ Unit) Unit ℝ) (Q : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ)
      (d : Unit → ℝ) (ε : ℝ), Uτ Unit Unit Q ∧ Smat Z = Q * dblDiag d * Qᵀ ∧ 0 < ε ∧
        Real.sqrt ((Finset.univ.filter (fun i : Unit => d i < ε)).card) * ε <
          ‖Smat Z - Sreg Q d ε‖ := by
  refine ⟨0, 1, 0, 1, by simp [Uτ], ?_, one_pos, ?_⟩
  · ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Smat, dblDiag]
  · have hS : Smat (0 : Matrix (Unit ⊕ Unit) Unit ℝ) - Sreg 1 0 1 = -1 := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [Smat, Sreg, dblDiag]
    have hn : ‖(-1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ)‖ ^ 2 = 2 := by
      rw [Frobenius.norm_sq_eq_sum]
      simp [Fintype.sum_sum_type]
      norm_num
    have hc : (Finset.univ.filter (fun i : Unit => (0 : Unit → ℝ) i < 1)).card = 1 := by simp
    rw [hS, hc, Nat.cast_one, Real.sqrt_one, one_mul]
    nlinarith [norm_nonneg (-1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ)]

/-- The averaged field `F_* = ½ (F - J_{2N} F J_{2n})`, the nearest point (in Frobenius norm) to
`F` in the space `{X : X J_{2n} = J_{2N} X}`.  Writing `F = [F₁ | F₂]` in column blocks of width
`n`, one gets `F_* = [W | J_{2N}ᵀ W]` with `W = ½ (F₁ + J_{2N} F₂)`, which is the paper's
`F_{ε,*} = [W | J_{2N}ᵀ W]` with `2X := F₁ + G₂`, `2Y := G₁ - F₂` (Section 5). -/
noncomputable def symmetrize (X : Matrix (m ⊕ m) (l ⊕ l) ℝ) : Matrix (m ⊕ m) (l ⊕ l) ℝ :=
  (1 / 2 : ℝ) • (X - sJ m * X * sJ l)

/-- **arXiv 2007.13153, Sec. 5, symmetrized field `F_{ε,*} ∈ H_U`.**  If `U ∈ 𝒰_τ` and
`Xᵀ U = 0` (as is the case for every `F_ε = (I - U Uᵀ)(…) S†`, see `velF'_transpose_mul`), then the
symmetrization `X_* = ½ (X - J X J)` lies in `H_U`, for *any* matrix `S†` in place of `S⁻¹`. -/
theorem symmetrize_mem_Hspace {U : Matrix (m ⊕ m) (l ⊕ l) ℝ} (hU : Uτ m l U)
    {X : Matrix (m ⊕ m) (l ⊕ l) ℝ} (hX : Xᵀ * U = 0) : symmetrize X ∈ Hspace U := by
  have hUX : Uᵀ * X = 0 := by
    have := congrArg Matrix.transpose hX
    simpa [Matrix.transpose_mul] using this
  refine ⟨?_, ?_⟩
  · have : Uᵀ * symmetrize X = 0 := by
      unfold symmetrize
      rw [Matrix.mul_smul, Matrix.mul_sub, hUX, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        hU.transpose_mul_J, Matrix.mul_assoc (sJ l), hUX]
      simp
    have h2 := congrArg Matrix.transpose this
    simpa [Matrix.transpose_mul] using h2
  · unfold symmetrize
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub]
    congr 1
    have h1 : sJ m * X * sJ l * sJ l = -(sJ m * X) := by
      rw [Matrix.mul_assoc _ _ (sJ l), sJ_mul_sJ]; simp
    have h2 : sJ m * (sJ m * X * sJ l) = -(X * sJ l) := by
      simp only [← Matrix.mul_assoc, sJ_mul_sJ, Matrix.neg_mul, Matrix.one_mul]
    rw [h1, h2]
    abel

/-- **arXiv 2007.13153, Sec. 5, error of the symmetrization.**  For every
`X ∈ ℝ^{2N × 2n}`: `‖X - X_*‖_F² = ¼ ‖X J_{2n} - J_{2N} X‖_F²` (the paper's
`‖F_ε - F_{ε,*}‖² = ¼ ‖F_ε J_{2n} - J_{2N} F_ε‖²`), with `X_* = symmetrize X`. -/
theorem symmetrize_error (X : Matrix (m ⊕ m) (l ⊕ l) ℝ) :
    ‖X - symmetrize X‖ ^ 2 = (1 / 4) * ‖X * sJ l - sJ m * X‖ ^ 2 := by
  have key : (X + sJ m * X * sJ l) = (X * sJ l - sJ m * X) * (sJ l)ᵀ := by
    rw [Matrix.sub_mul, sJ_transpose, Matrix.mul_neg, Matrix.mul_neg, Matrix.mul_assoc X,
      sJ_mul_sJ]
    simp [Matrix.mul_assoc]
  have hx : X - symmetrize X = (1 / 2 : ℝ) • (X + sJ m * X * sJ l) := by
    unfold symmetrize
    ext i j
    simp
    ring
  rw [hx, norm_smul, key, Frobenius.norm_mul_transpose_of_orthonormal sJ_transpose_mul]
  rw [mul_pow, Real.norm_eq_abs, sq_abs]
  norm_num

/-- **arXiv 2007.13153, Sec. 5: the regularized velocity field.**  Under the hypotheses of
`regularization_bound` (the assumed PVL factorization `S(Z) = Q D Qᵀ`), for `U ∈ 𝒰_τ`:
the field `F_ε = (I - U Uᵀ)(J Y Zᵀ - Y Zᵀ Jᵀ) S_ε⁻¹` lies in `H_U` (the paper's "belongs to the
tangent space of the orthosymplectic manifold by construction"; its symmetrization is then `F_ε`
itself, `symmetrize_error` gives zero error). -/
theorem regularized_velocity_mem_Hspace (Z : Matrix (l ⊕ l) p ℝ)
    {Q : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hQ : Uτ l l Q) {d : l → ℝ}
    (hfac : Smat Z = Q * dblDiag d * Qᵀ) {ε : ℝ} (hε : 0 < ε)
    {U : Matrix (m ⊕ m) (l ⊕ l) ℝ} (hU : Uτ m l U) (Y : Matrix (m ⊕ m) p ℝ) :
    velF' (Sreg Q d ε) U Z Y ∈ Hspace U := by
  obtain ⟨hpd, hsk, -⟩ := regularization_bound Z hQ hfac hε
  rw [Sreg_transpose] at hsk
  exact velF'_mem_Hspace hU ((Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit) hsk Z Y

/-- Non-vacuity of `regularization_bound`: for `Z = 1` one has `S = 2 I = Q D Qᵀ` with `Q = 1`
and `D = diag (2, 2)`, so the factorization hypothesis is satisfiable. -/
example : Smat (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) = (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) *
    dblDiag (fun _ : l => (2 : ℝ)) * (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ)ᵀ := by
  have : dblDiag (fun _ : l => (2 : ℝ)) = (2 : ℝ) • 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> by_cases h : i = j <;>
      simp [dblDiag, h]
  rw [this]
  simp [Smat, sJ_transpose_mul, two_smul]

end LeanDLRA.Literature.P2007_13153
