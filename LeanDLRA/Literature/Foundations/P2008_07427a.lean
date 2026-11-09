import LeanDLRA.Foundations.Projector
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.GaugeODE
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2008.07427: dynamical reduced basis (symplectic DLRA) for Hamiltonian systems

Orthosymplectic matrices `U ∈ ℝ^{2N × 2n}` (`Uᵀ U = I`, `Uᵀ J_{2N} U = J_{2n}`) are matrices over
the index types `ι ⊕ ι` and `κ ⊕ κ`, with `J = symplJ ι = [[0, I], [-I, 0]]`.  Proved:

* **Lemma 3.3** `lemma_3_3` (as printed: for symplectic `M₊` with symplectic inverse `M`,
  `M₊ M₊ᵀ = I` iff `M = M₊ᵀ`) and `isOrthosymplectic_iff` (the characterization derived in its
  proof: `U` is orthosymplectic iff `U = [A | Jᵀ A]` with `Aᵀ A = I`, `Aᵀ J A = 0`);
* **Prop. 5.7 / Cor. 5.8** `cayleyRetraction_lipschitz` (constant `3`; in fact `2`,
  `cayleyRetraction_lipschitz_two`) and `cayleyRetraction_error_isBigO` for the Cayley retraction
  `R_Q(V) = cay(Υ_Q(V)) Q` on horizontal vectors, via `‖(I - Ω)⁻¹ X‖_F ≤ ‖X‖_F` for skew `Ω` and
  `‖M (Q + Y)‖_F ≤ 2‖M‖_F`;
* **Prop. 4.3 / Remark 4.4** `tangentPi`: `Π(w) = (I - U Uᵀ)(wZ + J w Z Jᵀ) S⁻¹ Zᵀ + U Uᵀ w` is
  an `IsOrthProj` (`isOrthProj_tangentPi`) onto `tangentSpace U Z`, commutes with `J`
  (`tangentPi_symplJ_mul`), and `⟨w - Π w, J y⟩ = 0` on the tangent space;
* **Prop. 4.5, conditional** `isOrthosymplectic_of_horizontal`: orthosymplecticity is preserved
  when `U̇ ∈ H_U` along the curve (the first step of the paper's proof); `isHorizontal_rhs` shows
  that the right-hand side of (4.10) lies in `H_U` at orthosymplectic `U` (the second step).  Not
  proved: Prop. 4.5 itself, that a solution of (4.10) started on the manifold stays on it (this
  needs an invariance argument, since `isHorizontal_rhs` applies only at points already known to
  be orthosymplectic);
* **Sec. 4.2** `hamiltonian_conserved` (abstract, state-dependent orthogonal projector commuting
  with a skew `J`) and `hamiltonian_conserved_matrix` (with the projector of Prop. 4.3).

`example`s at the end exhibit orthosymplectic `Q`, nonzero horizontal `V`, and invertible `S`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2008_07427

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The canonical symplectic unit `J_{2N} = [[0, I], [-I, 0]]` on `ι ⊕ ι`. -/
def symplJ (ι : Type*) [Fintype ι] [DecidableEq ι] : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks 0 1 (-1) 0

lemma symplJ_mul_self : symplJ ι * symplJ ι = -1 := by
  ext i j; rcases i with i | i <;> rcases j with j | j <;>
    simp [symplJ, Matrix.fromBlocks_multiply, Matrix.one_apply]

lemma symplJ_transpose : (symplJ ι)ᵀ = -symplJ ι := by
  simp [symplJ, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]

lemma symplJ_transpose_mul : (symplJ ι)ᵀ * symplJ ι = 1 := by
  rw [symplJ_transpose, Matrix.neg_mul, symplJ_mul_self, neg_neg]

lemma symplJ_mul_transpose : symplJ ι * (symplJ ι)ᵀ = 1 := by
  rw [symplJ_transpose, Matrix.mul_neg, symplJ_mul_self, neg_neg]

/-- `U ∈ ℝ^{2N × 2n}` is orthosymplectic: `Uᵀ U = I_{2n}` and `Uᵀ J_{2N} U = J_{2n}`
(arXiv 2008.07427, Def. 3.2 / (4.4)). -/
def IsOrthosymplectic (U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ) : Prop :=
  Uᵀ * U = 1 ∧ Uᵀ * symplJ ι * U = symplJ κ


/-- An orthosymplectic matrix commutes with the symplectic units: `J_{2N} U = U J_{2n}`. -/
lemma IsOrthosymplectic.comm {U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} (h : IsOrthosymplectic U) :
    symplJ ι * U = U * symplJ κ := by
  obtain ⟨h1, h2⟩ := h
  have f1 : Uᵀ * (symplJ ι * U) = symplJ κ := by rw [← Matrix.mul_assoc]; exact h2
  have f1' : ∀ X : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ,
      Uᵀ * (symplJ ι * (U * X)) = symplJ κ * X := by
    intro X; rw [← Matrix.mul_assoc (symplJ ι), ← Matrix.mul_assoc Uᵀ, f1]
  have f2' : ∀ X : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ,
      Uᵀ * ((symplJ ι)ᵀ * (U * X)) = (symplJ κ)ᵀ * X := by
    intro X
    have := congrArg Matrix.transpose h2
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at this
    rw [← Matrix.mul_assoc (symplJ ι)ᵀ, ← Matrix.mul_assoc Uᵀ, ← this]
  have f3 : ∀ X : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ, Uᵀ * (U * X) = X := by
    intro X; rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have g4 : ∀ X : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ,
      (symplJ ι)ᵀ * (symplJ ι * X) = X := by
    intro X; rw [← Matrix.mul_assoc, symplJ_transpose_mul, Matrix.one_mul]
  have f2 : Uᵀ * ((symplJ ι)ᵀ * U) = (symplJ κ)ᵀ := by
    have := f2' 1
    rwa [Matrix.mul_one, Matrix.mul_one] at this
  have hW : (symplJ ι * U - U * symplJ κ)ᵀ * (symplJ ι * U - U * symplJ κ) = 0 := by
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_assoc, f1, f2', f3, g4, h1, symplJ_transpose_mul]
    abel
  have := (Matrix.conjTranspose_mul_self_eq_zero (A := symplJ ι * U - U * symplJ κ)).1
    (by rwa [Matrix.conjTranspose_eq_transpose_of_trivial])
  exact sub_eq_zero.1 this

/-- **Characterization of orthosymplectic matrices, from the proof of Lemma 3.3**
(arXiv 2008.07427).  A matrix `U ∈ ℝ^{2N × 2n}` is orthosymplectic (`Uᵀ U = I`,
`Uᵀ J_{2N} U = J_{2n}`, canonical `J`) iff `U = [A | J_{2N}ᵀ A]` with `Aᵀ A = I_n` and
`Aᵀ J_{2N} A = 0`.  Here `2N = ι ⊕ ι` and `2n = κ ⊕ κ` are index types, `[· | ·]` is
`Matrix.fromCols`.  No condition `n ≤ N` is needed.  The printed statement of Lemma 3.3 is
`lemma_3_3`; the "only if" direction here is derived in its proof, and the paper uses the form
`U = [A | J_{2N}ᵀ A]` later (Lemma 4.8). -/
theorem isOrthosymplectic_iff (U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ) :
    IsOrthosymplectic U ↔ ∃ A : Matrix (ι ⊕ ι) κ ℝ, Aᵀ * A = 1 ∧ Aᵀ * symplJ ι * A = 0 ∧
      U = Matrix.fromCols A ((symplJ ι)ᵀ * A) := by
  constructor
  · intro h
    have hc := h.comm
    obtain ⟨h1, h2⟩ := h
    set A := U.toCols₁ with hA
    set B := U.toCols₂ with hB
    have hU : U = Matrix.fromCols A B := (Matrix.fromCols_toCols U).symm
    have hJ : symplJ ι * Matrix.fromCols A B = Matrix.fromCols A B * symplJ κ := by
      rw [← hU]; exact hc
    rw [Matrix.mul_fromCols] at hJ
    conv at hJ => rhs; rw [symplJ, Matrix.fromCols_mul_fromBlocks]
    simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg] at hJ
    replace hJ := Matrix.fromCols_inj hJ
    have hB' : B = (symplJ ι)ᵀ * A := by
      rw [symplJ_transpose, Matrix.neg_mul, hJ.1, neg_neg]
    rw [hU, Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols] at h1
    rw [hU, Matrix.transpose_fromCols, Matrix.mul_assoc, Matrix.mul_fromCols,
      Matrix.fromRows_mul_fromCols] at h2
    rw [← Matrix.fromBlocks_one] at h1
    replace h1 := Matrix.fromBlocks_inj.1 h1
    have hκ : symplJ κ = Matrix.fromBlocks 0 1 (-1) 0 := rfl
    rw [hκ] at h2
    replace h2 := Matrix.fromBlocks_inj.1 h2
    refine ⟨A, h1.1, ?_, ?_⟩
    · rw [Matrix.mul_assoc]; exact h2.1
    · rw [hU, hB']
  · rintro ⟨A, hA1, hA2, rfl⟩
    have hA2' : Aᵀ * (symplJ ι * A) = 0 := by rw [← Matrix.mul_assoc]; exact hA2
    have e1 : Aᵀ * ((symplJ ι)ᵀ * A) = 0 := by
      have := congrArg Matrix.transpose hA2
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
    have e2 : (Aᵀ * (symplJ ι * ((symplJ ι)ᵀ * A))) = 1 := by
      rw [← Matrix.mul_assoc (symplJ ι), symplJ_mul_transpose, Matrix.one_mul, hA1]
    have e3 : Aᵀ * (symplJ ι * (symplJ ι * A)) = -1 := by
      rw [← Matrix.mul_assoc (symplJ ι), symplJ_mul_self, Matrix.neg_mul, Matrix.one_mul,
        Matrix.mul_neg, hA1]
    refine ⟨?_, ?_⟩
    · rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one]
      refine Matrix.fromBlocks_inj.2 ⟨hA1, e1, ?_, ?_⟩
      · simpa [Matrix.transpose_mul, Matrix.mul_assoc] using hA2'
      · simpa [Matrix.transpose_mul, Matrix.mul_assoc] using e2
    · rw [Matrix.transpose_fromCols, Matrix.mul_assoc, Matrix.mul_fromCols,
        Matrix.fromRows_mul_fromCols]
      have hκ : symplJ κ = Matrix.fromBlocks 0 1 (-1) 0 := rfl
      rw [hκ]
      refine Matrix.fromBlocks_inj.2 ⟨hA2', ?_, ?_, ?_⟩
      · exact e2
      · simpa [Matrix.transpose_mul, Matrix.mul_assoc] using e3
      · have e4 : ∀ X : Matrix (ι ⊕ ι) κ ℝ, symplJ ι * ((symplJ ι)ᵀ * X) = X := by
          intro X; rw [← Matrix.mul_assoc, symplJ_mul_transpose, Matrix.one_mul]
        simpa [Matrix.transpose_mul, Matrix.mul_assoc, e4] using hA2'

/-- **Lemma 3.3** (arXiv 2008.07427), as printed.  Let `M₊ ∈ ℝ^{2n × 2N}` be symplectic,
`M₊ J_{2N} M₊ᵀ = J_{2n}`, and let `M = J_{2N}ᵀ M₊ᵀ J_{2n}` be its symplectic (right) inverse.
Then `M₊ M₊ᵀ = I_{2n}` iff `M = M₊ᵀ`.  No condition `n ≤ N` is needed. -/
theorem lemma_3_3 (Mp : Matrix (κ ⊕ κ) (ι ⊕ ι) ℝ) (hMp : Mp * symplJ ι * Mpᵀ = symplJ κ) :
    Mp * Mpᵀ = 1 ↔ (symplJ ι)ᵀ * Mpᵀ * symplJ κ = Mpᵀ := by
  constructor
  · intro h
    have hU : IsOrthosymplectic Mpᵀ :=
      ⟨by rwa [Matrix.transpose_transpose], by rwa [Matrix.transpose_transpose]⟩
    rw [Matrix.mul_assoc, ← hU.comm, ← Matrix.mul_assoc, symplJ_transpose_mul, Matrix.one_mul]
  · intro h
    have ht : Mp * (symplJ ι)ᵀ * Mpᵀ = (symplJ κ)ᵀ := by
      have := congrArg Matrix.transpose hMp
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
    calc Mp * Mpᵀ = Mp * ((symplJ ι)ᵀ * Mpᵀ * symplJ κ) := by rw [h]
      _ = Mp * (symplJ ι)ᵀ * Mpᵀ * symplJ κ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ht, symplJ_transpose_mul]

/-- Non-vacuity of `lemma_3_3`: the identity on `ℝ^{2N}` is symplectic. -/
example : (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) * symplJ ι * (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)ᵀ =
    symplJ ι := by simp

/-! ### The Cayley retraction (Section 5) -/

section Cayley

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]

lemma norm_le_norm_one_sub_mul {Ω : Matrix m m ℝ} (hΩ : Ωᵀ = -Ω) (Z : Matrix m n ℝ) :
    ‖Z‖ ≤ ‖(1 - Ω) * Z‖ := by
  have h0 : ⟪Z, Ω * Z⟫ = 0 := by
    have h := Frobenius.inner_mul_left Ω Z Z
    rw [hΩ, Matrix.neg_mul, inner_neg_right] at h
    have := real_inner_comm Z (Ω * Z)
    linarith
  have h2 : ‖(1 - Ω) * Z‖ ^ 2 = ‖Z‖ ^ 2 + ‖Ω * Z‖ ^ 2 := by
    rw [Matrix.sub_mul, Matrix.one_mul, norm_sub_sq_real, h0]; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (by rw [h2]; nlinarith [sq_nonneg ‖Ω * Z‖])

lemma isUnit_one_sub {Ω : Matrix m m ℝ} (hΩ : Ωᵀ = -Ω) : IsUnit (1 - Ω) := by
  refine Matrix.mulVec_injective_iff_isUnit.1 fun x y hxy => ?_
  have hz : (1 - Ω) *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  have hZ : (1 - Ω) * (Matrix.of fun i (_ : Unit) => (x - y) i) = 0 := by
    ext i u
    exact congrFun hz i
  have h := norm_le_norm_one_sub_mul hΩ (Matrix.of fun i (_ : Unit) => (x - y) i)
  rw [hZ, norm_zero] at h
  have h0 := norm_le_zero_iff.1 h
  funext i
  have := congrFun (congrFun h0 i) ()
  simpa [sub_eq_zero] using this

/-- The Cayley transform `cay(Ω) = (I - Ω/2)⁻¹ (I + Ω/2)` (arXiv 2008.07427, (5.3)). -/
noncomputable def cay (Ω : Matrix m m ℝ) : Matrix m m ℝ :=
  (1 - (1 / 2 : ℝ) • Ω)⁻¹ * (1 + (1 / 2 : ℝ) • Ω)

lemma cay_transpose_mul_cay {Ω : Matrix m m ℝ} (hΩ : Ωᵀ = -Ω) :
    (cay Ω)ᵀ * cay Ω = 1 := by
  set Ω' : Matrix m m ℝ := (1 / 2 : ℝ) • Ω with hΩ'def
  have hΩ' : Ω'ᵀ = -Ω' := by rw [hΩ'def, Matrix.transpose_smul, hΩ, smul_neg]
  have hAu : IsUnit (1 - Ω') := isUnit_one_sub hΩ'
  have hBu : IsUnit (1 + Ω') := by
    have := isUnit_one_sub (Ω := -Ω') (by rw [Matrix.transpose_neg, hΩ'])
    rwa [sub_neg_eq_add] at this
  have hA := (Matrix.isUnit_iff_isUnit_det _).1 hAu
  have hB := (Matrix.isUnit_iff_isUnit_det _).1 hBu
  have hAt : (1 - Ω')ᵀ = 1 + Ω' := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hΩ', sub_neg_eq_add]
  have hBt : (1 + Ω')ᵀ = 1 - Ω' := by
    rw [Matrix.transpose_add, Matrix.transpose_one, hΩ', sub_eq_add_neg]
  have hcomm : (1 - Ω') * (1 + Ω') = (1 + Ω') * (1 - Ω') := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_one]
    abel
  have hc : (1 - Ω')⁻¹ * (1 + Ω') = (1 + Ω') * (1 - Ω')⁻¹ := by
    calc (1 - Ω')⁻¹ * (1 + Ω') = (1 - Ω')⁻¹ * (1 + Ω') * ((1 - Ω') * (1 - Ω')⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]
      _ = (1 - Ω')⁻¹ * ((1 + Ω') * (1 - Ω')) * (1 - Ω')⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (1 + Ω') * (1 - Ω')⁻¹ := by
          rw [← hcomm]
          simp only [← Matrix.mul_assoc]
          rw [Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
  unfold cay
  rw [← hΩ'def]
  have e1 : ((1 - Ω')⁻¹ * (1 + Ω'))ᵀ = (1 - Ω') * (1 + Ω')⁻¹ := by
    rw [Matrix.transpose_mul, hBt, Matrix.transpose_nonsing_inv, hAt]
  rw [e1, hc]
  calc (1 - Ω') * (1 + Ω')⁻¹ * ((1 + Ω') * (1 - Ω')⁻¹)
      = (1 - Ω') * ((1 + Ω')⁻¹ * (1 + Ω')) * (1 - Ω')⁻¹ := by simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv _ hA]

lemma cay_skew_identity {k : Type*} {Ω : Matrix m m ℝ} (hΩ : Ωᵀ = -Ω) (Q : Matrix m k ℝ) :
    (1 - (1 / 2 : ℝ) • Ω) * (cay Ω * Q) = (1 + (1 / 2 : ℝ) • Ω) * Q := by
  have hu : IsUnit (1 - (1 / 2 : ℝ) • Ω) := isUnit_one_sub (by
    rw [Matrix.transpose_smul, hΩ, smul_neg])
  have hA := (Matrix.isUnit_iff_isUnit_det _).1 hu
  unfold cay
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.one_mul]

/-- `Θ_S^Q(V) = V + Q (S - Qᵀ V / 2)` (arXiv 2008.07427, Prop. 5.6). -/
noncomputable def theta (Q : Matrix m n ℝ) (S : Matrix n n ℝ) (V : Matrix m n ℝ) : Matrix m n ℝ :=
  V + Q * (S - (1 / 2 : ℝ) • (Qᵀ * V))

/-- `Υ_Q(V) = Θ Qᵀ - Q Θᵀ` with `Θ = Θ_S^Q(V)` (arXiv 2008.07427, (5.17)). -/
noncomputable def upsilon (Q : Matrix m n ℝ) (S : Matrix n n ℝ) (V : Matrix m n ℝ) : Matrix m m ℝ :=
  theta Q S V * Qᵀ - Q * (theta Q S V)ᵀ

/-- The Cayley retraction `R_Q(V) = cay(Υ_Q(V)) Q` (arXiv 2008.07427, (5.18)). -/
noncomputable def cayleyRetraction (Q : Matrix m n ℝ) (S : Matrix n n ℝ) (V : Matrix m n ℝ) :
    Matrix m n ℝ :=
  cay (upsilon Q S V) * Q

omit [DecidableEq m] in
lemma upsilon_transpose (Q : Matrix m n ℝ) (S : Matrix n n ℝ) (V : Matrix m n ℝ) :
    (upsilon Q S V)ᵀ = -upsilon Q S V := by
  simp [upsilon, Matrix.transpose_mul, Matrix.transpose_sub]

omit [DecidableEq m] in
lemma upsilon_sub_of_horizontal {Q : Matrix m n ℝ} (S : Matrix n n ℝ) {V W : Matrix m n ℝ}
    (hV : Qᵀ * V = 0) (hW : Qᵀ * W = 0) :
    upsilon Q S V - upsilon Q S W = (V - W) * Qᵀ - Q * (V - W)ᵀ := by
  simp only [upsilon, theta, hV, hW, smul_zero, sub_zero, Matrix.add_mul,
    Matrix.transpose_add, Matrix.mul_add, Matrix.sub_mul, Matrix.transpose_sub, Matrix.mul_sub]
  abel

omit [DecidableEq m] in
lemma norm_mul_le_of_orthonormal {k : Type*} [Fintype k] [DecidableEq k]
    {Q : Matrix n k ℝ} (hQ : Qᵀ * Q = 1) (M : Matrix m n ℝ) : ‖M * Q‖ ≤ ‖M‖ := by
  have h := (isOrthProj_rightProj (m := m) hQ).norm_le M
  rw [rightProj_apply, Frobenius.norm_mul_transpose_of_orthonormal hQ (M * Q)] at h
  exact h

/-- The horizontal space `H_Q = {V : Qᵀ V = 0, V J_{2n} = J_{2N} V}` (arXiv 2008.07427, (4.7)). -/
def IsHorizontal (Q V : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ) : Prop :=
  Qᵀ * V = 0 ∧ V * symplJ κ = symplJ ι * V

/-- The retraction `R_Q` is `2`-Lipschitz on horizontal vectors (a sharper form of
Prop. 5.7, which is the corollary with constant `3`); see `cayleyRetraction_lipschitz`. -/
theorem cayleyRetraction_lipschitz_two {Q : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} (hQ : IsOrthosymplectic Q)
    (S : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) {V W : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ}
    (hV : IsHorizontal Q V) (hW : IsHorizontal Q W) :
    ‖cayleyRetraction Q S V - cayleyRetraction Q S W‖ ≤ 2 * ‖V - W‖ := by
  have hQ1 := hQ.1
  set ΩV : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ := (1 / 2 : ℝ) • upsilon Q S V with hΩV
  set ΩW : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ := (1 / 2 : ℝ) • upsilon Q S W with hΩW
  set U := cayleyRetraction Q S V with hU
  set Y := cayleyRetraction Q S W with hY
  have eV := cay_skew_identity (upsilon_transpose Q S V) Q
  have eW := cay_skew_identity (upsilon_transpose Q S W) Q
  have hYo : Yᵀ * Y = 1 := by
    rw [hY, cayleyRetraction, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (cay _),
      cay_transpose_mul_cay (upsilon_transpose Q S W), Matrix.one_mul, hQ1]
  have key : (1 - ΩV) * (U - Y) = (ΩV - ΩW) * (Q + Y) := by
    have eV' : (1 - ΩV) * U = (1 + ΩV) * Q := eV
    have eW' : (1 - ΩW) * Y = (1 + ΩW) * Q := eW
    simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.one_mul]
      at eV' eW' ⊢
    linear_combination (norm := abel) eV' - eW'
  have hskew : ΩVᵀ = -ΩV := by
    rw [hΩV, Matrix.transpose_smul, upsilon_transpose, smul_neg]
  have hM : ΩV - ΩW = (1 / 2 : ℝ) • ((V - W) * Qᵀ - Q * (V - W)ᵀ) := by
    rw [hΩV, hΩW, ← smul_sub, upsilon_sub_of_horizontal S (hV.1) (hW.1)]
  have hMn : ‖ΩV - ΩW‖ ≤ ‖V - W‖ := by
    rw [hM, norm_smul, Real.norm_of_nonneg (by norm_num)]
    have h1 : ‖(V - W) * Qᵀ‖ = ‖V - W‖ := Frobenius.norm_mul_transpose_of_orthonormal hQ1 _
    have h2 : ‖Q * (V - W)ᵀ‖ = ‖V - W‖ := by
      rw [Frobenius.norm_mul_of_orthonormal hQ1, Frobenius.norm_transpose]
    have := norm_sub_le ((V - W) * Qᵀ) (Q * (V - W)ᵀ)
    linarith
  have hQY : ‖(ΩV - ΩW) * (Q + Y)‖ ≤ 2 * ‖ΩV - ΩW‖ := by
    rw [Matrix.mul_add]
    have a1 := norm_mul_le_of_orthonormal hQ1 (ΩV - ΩW)
    have a2 := norm_mul_le_of_orthonormal hYo (ΩV - ΩW)
    have := norm_add_le ((ΩV - ΩW) * Q) ((ΩV - ΩW) * Y)
    linarith
  calc ‖U - Y‖ ≤ ‖(1 - ΩV) * (U - Y)‖ := norm_le_norm_one_sub_mul hskew _
    _ = ‖(ΩV - ΩW) * (Q + Y)‖ := by rw [key]
    _ ≤ 2 * ‖V - W‖ := by linarith

/-- **Prop. 5.7** (arXiv 2008.07427).  The Cayley retraction `R_Q(V) = cay(Υ_Q(V)) Q`, (5.18),
is Lipschitz in the Frobenius norm on the horizontal space `H_Q` of an orthosymplectic `Q`:
`‖R_Q(V) - R_Q(W)‖_F ≤ 3 ‖V - W‖_F` for `V, W ∈ H_Q = {Qᵀ V = 0, V J_{2n} = J_{2N} V}`.  `S` is an
arbitrary `2n × 2n` matrix here (the paper takes `S` symmetric with `S J + J Sᵀ = 0`, a special
case).  The statement is proved with the sharper constant `2` in
`cayleyRetraction_lipschitz_two`.  The paper's `3` comes from a three-term bound of
`‖Υ_Q(V) - Υ_Q(W)‖` whose third term, `Q (V - W)ᵀ Q Qᵀ`, vanishes on `H_Q`. -/
theorem cayleyRetraction_lipschitz {Q : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} (hQ : IsOrthosymplectic Q)
    (S : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) {V W : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ}
    (hV : IsHorizontal Q V) (hW : IsHorizontal Q W) :
    ‖cayleyRetraction Q S V - cayleyRetraction Q S W‖ ≤ 3 * ‖V - W‖ :=
  (cayleyRetraction_lipschitz_two hQ S hV hW).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))

/-- **Cor. 5.8** (arXiv 2008.07427).  If the tangent-space solution `V(t_m)` is approximated by
`V_m` with error `O(Δt^k)`, then `‖R_Q(V(t_m)) - R_Q(V_m)‖ = O(Δt^k)`.  Stated for any filter `l`
on the step sizes (e.g. `𝓝[>] 0`): `V`, `Vh : ι' → H_Q` stand for the exact solution and the
numerical solution of the tangent-space equation (both horizontal, as in the paper where all
Runge-Kutta stages are horizontal), indexed by the step size; the hypothesis is the paper's
"the numerical method on the tangent space is of order `k`" in the form
`Vh dt - V dt = O(dt^k)`.  (The proof, via Prop. 5.7, gives `3` times the constant of the
hypothesis.)  The Runge-Kutta error analysis itself is not part of this statement. -/
theorem cayleyRetraction_error_isBigO {Q : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} (hQ : IsOrthosymplectic Q)
    (S : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) {l : Filter ℝ} {K : ℕ}
    {V Vh : ℝ → Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} (hV : ∀ dt, IsHorizontal Q (V dt))
    (hVh : ∀ dt, IsHorizontal Q (Vh dt))
    (h : (fun dt => Vh dt - V dt) =O[l] fun dt => dt ^ K) :
    (fun dt => cayleyRetraction Q S (Vh dt) - cayleyRetraction Q S (V dt)) =O[l]
      fun dt => dt ^ K := by
  refine Asymptotics.IsBigO.trans ?_ h
  refine Asymptotics.IsBigO.of_bound 3 (Filter.Eventually.of_forall fun dt => ?_)
  exact cayleyRetraction_lipschitz hQ S (hVh dt) (hV dt)

end Cayley

/-! ### Orthosymplecticity is preserved (Prop. 4.5) -/

/-- **Prop. 4.5, conditional on `U̇(t) ∈ H_{U(t)}`** (arXiv 2008.07427; the first step of the
paper's proof, its claim about `W`).  If `U(t₀)` is orthosymplectic and `U̇(t) ∈ H_{U(t)}`, i.e.
`U̇ᵀ U = 0` and `U̇ J_{2n} = J_{2N} U̇`, for all `t`, then `U(t)` is orthosymplectic for all `t`.
Stated for a differentiable curve on a convex set `s` of times (an interval).  For solutions of
(4.10) the paper verifies `U̇ ∈ H_U` using that `U` is orthosymplectic (`isHorizontal_rhs` below);
Prop. 4.5 itself, without the hypothesis `U̇ ∈ H_U` along the solution, is not proved here. -/
theorem isOrthosymplectic_of_horizontal {U U' : ℝ → Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} {s : Set ℝ}
    (hs : Convex ℝ s) (hU : ∀ t ∈ s, HasDerivWithinAt U (U' t) s t)
    (hH : ∀ t ∈ s, IsHorizontal (U t) (U' t)) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (h₀ : IsOrthosymplectic (U t₀)) {t : ℝ} (ht : t ∈ s) : IsOrthosymplectic (U t) := by
  have hg : ∀ x ∈ s, (U x)ᵀ * U' x = 0 := fun x hx => (hH x hx).1
  refine ⟨transpose_mul_self_eq_one_of_gauge hs hU hg ht₀ h₀.1 ht, ?_⟩
  have hd : ∀ x ∈ s, HasDerivWithinAt (fun t => (U t)ᵀ * (symplJ ι * U t)) 0 s x := by
    intro x hx
    have h := Frobenius.hasDerivWithinAt_mul (Frobenius.hasDerivWithinAt_transpose (hU x hx))
      (Frobenius.hasDerivWithinAt_const_mul (symplJ ι) (hU x hx))
    have hJ := (hH x hx).2
    have e1 : (U' x)ᵀ * (symplJ ι * U x) = 0 := by
      have : (U' x)ᵀ * symplJ ι = symplJ κ * (U' x)ᵀ := by
        have := congrArg Matrix.transpose hJ
        rw [Matrix.transpose_mul, Matrix.transpose_mul, symplJ_transpose, symplJ_transpose] at this
        simpa using this.symm
      rw [← Matrix.mul_assoc, this, Matrix.mul_assoc]
      have h0 : (U' x)ᵀ * U x = 0 := by
        have := congrArg Matrix.transpose (hg x hx)
        simpa [Matrix.transpose_mul] using this
      rw [h0, Matrix.mul_zero]
    have e2 : (U x)ᵀ * (symplJ ι * U' x) = 0 := by
      rw [← hJ, ← Matrix.mul_assoc, hg x hx, Matrix.zero_mul]
    rw [e1, e2, add_zero] at h
    exact h
  have h := hs.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hd (fun x _ => by simp) ht₀ ht
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc]
  exact h₀.2


/-! ### The tangent-space projection (Prop. 4.3, Remark 4.4) -/

section Tangent

variable {p : Type*} [Fintype p]

/-- `S = Zᵀ Z + J_{2n} Zᵀ Z J_{2n}ᵀ` (arXiv 2008.07427, Prop. 4.3). -/
def Smat (Z : Matrix p (κ ⊕ κ) ℝ) : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ :=
  Zᵀ * Z + symplJ κ * (Zᵀ * Z) * (symplJ κ)ᵀ

/-- `F_w = w Z + J_{2N} w Z J_{2n}ᵀ` (arXiv 2008.07427, Prop. 4.3). -/
def Fmat (Z : Matrix p (κ ⊕ κ) ℝ) (w : Matrix (ι ⊕ ι) p ℝ) : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ :=
  w * Z + symplJ ι * w * Z * (symplJ κ)ᵀ

/-- The projection `Π(w) = (I - U Uᵀ)(w Z + J_{2N} w Z J_{2n}ᵀ) S⁻¹ Zᵀ + U Uᵀ w` of
arXiv 2008.07427, Prop. 4.3, with `S = Zᵀ Z + J_{2n} Zᵀ Z J_{2n}ᵀ` and `S⁻¹` the matrix inverse. -/
noncomputable def tangentPi (U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ) (Z : Matrix p (κ ⊕ κ) ℝ)
    (w : Matrix (ι ⊕ ι) p ℝ) : Matrix (ι ⊕ ι) p ℝ :=
  (1 - U * Uᵀ) * Fmat Z w * (Smat Z)⁻¹ * Zᵀ + U * Uᵀ * w

/-- The tangent space `T_R M^spl = {X_U Zᵀ + U X_Zᵀ : X_U ∈ H_U, X_Z ∈ ℝ^{p × 2n}}` at
`R = U Zᵀ`, in the form the paper derives from Prop. 4.1 (display after Remark 4.2); it is taken
here as the definition (Prop. 4.1 itself, the equality with (4.6), is not formalized). -/
def tangentSpace (U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ) (Z : Matrix p (κ ⊕ κ) ℝ) :
    Set (Matrix (ι ⊕ ι) p ℝ) :=
  {X | ∃ (XU : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ) (XZ : Matrix p (κ ⊕ κ) ℝ),
    IsHorizontal U XU ∧ X = XU * Zᵀ + U * XZᵀ}

lemma Smat_comm (Z : Matrix p (κ ⊕ κ) ℝ) : Smat Z * symplJ κ = symplJ κ * Smat Z := by
  have h2 : symplJ κ * symplJ κ = -1 := symplJ_mul_self
  have h3 : (symplJ κ)ᵀ = -symplJ κ := symplJ_transpose
  simp only [Smat, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_one, h3,
    Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc (symplJ κ) (symplJ κ), h2, Matrix.neg_mul,
    Matrix.one_mul]
  abel

lemma Smat_transpose (Z : Matrix p (κ ⊕ κ) ℝ) : (Smat Z)ᵀ = Smat Z := by
  simp [Smat, Matrix.transpose_mul, Matrix.mul_assoc]

lemma Sinv_comm {Z : Matrix p (κ ⊕ κ) ℝ} (hS : IsUnit (Smat Z).det) :
    (Smat Z)⁻¹ * symplJ κ = symplJ κ * (Smat Z)⁻¹ := by
  calc (Smat Z)⁻¹ * symplJ κ = (Smat Z)⁻¹ * symplJ κ * (Smat Z * (Smat Z)⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ hS, Matrix.mul_one]
    _ = (Smat Z)⁻¹ * (symplJ κ * Smat Z) * (Smat Z)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (Smat Z)⁻¹ * (Smat Z * symplJ κ) * (Smat Z)⁻¹ := by rw [← Smat_comm]
    _ = symplJ κ * (Smat Z)⁻¹ := by
        simp only [← Matrix.mul_assoc]
        rw [Matrix.nonsing_inv_mul _ hS, Matrix.one_mul]

lemma Fmat_comm (Z : Matrix p (κ ⊕ κ) ℝ) (w : Matrix (ι ⊕ ι) p ℝ) :
    Fmat Z w * symplJ κ = symplJ ι * Fmat Z w := by
  have h2 : symplJ ι * symplJ ι = -1 := symplJ_mul_self
  have h3 : (symplJ κ)ᵀ = -symplJ κ := symplJ_transpose
  have h4 : (symplJ κ) * symplJ κ = -1 := symplJ_mul_self
  simp only [Fmat, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, h3, Matrix.mul_neg,
    Matrix.neg_mul, h4, Matrix.mul_one, ← Matrix.mul_assoc (symplJ ι) (symplJ ι), h2,
    Matrix.neg_mul, Matrix.one_mul, neg_neg]
  abel

lemma proj_comm {U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} (hU : IsOrthosymplectic U) :
    symplJ ι * (U * Uᵀ) = (U * Uᵀ) * symplJ ι := by
  have hc := hU.comm
  have ht : Uᵀ * symplJ ι = symplJ κ * Uᵀ := by
    have := congrArg Matrix.transpose hc
    rw [Matrix.transpose_mul, Matrix.transpose_mul, symplJ_transpose, symplJ_transpose] at this
    simpa using this
  rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, ← ht, Matrix.mul_assoc]

lemma one_sub_proj_comm {U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} (hU : IsOrthosymplectic U) :
    symplJ ι * (1 - U * Uᵀ) = (1 - U * Uᵀ) * symplJ ι := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, proj_comm hU]

lemma one_sub_proj_mul_self {U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} (hU : IsOrthosymplectic U) :
    (1 - U * Uᵀ) * U = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU.1, Matrix.mul_one, sub_self]

omit [DecidableEq κ] in
lemma one_sub_proj_mul_horizontal {U XU : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} (hX : Uᵀ * XU = 0) :
    (1 - U * Uᵀ) * XU = XU := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hX, Matrix.mul_zero, sub_zero]

/-- The right-hand side of the basis equation (4.10),
`U̇ = (I - U Uᵀ)(J_{2N} Y Z - Y Z J_{2n}ᵀ) S⁻¹` (that is `(I - U Uᵀ) F_{J Y} S⁻¹`, since
`F_{J Y} = J Y Z - Y Z J_{2n}ᵀ`), lies in the horizontal
space `H_U` whenever `U` is orthosymplectic. -/
lemma isHorizontal_rhs {U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} (hU : IsOrthosymplectic U)
    {Z : Matrix p (κ ⊕ κ) ℝ} (hS : IsUnit (Smat Z).det) (w : Matrix (ι ⊕ ι) p ℝ) :
    IsHorizontal U ((1 - U * Uᵀ) * Fmat Z w * (Smat Z)⁻¹) := by
  refine ⟨?_, ?_⟩
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one,
      ← Matrix.mul_assoc, hU.1, Matrix.one_mul, sub_self, Matrix.zero_mul, Matrix.zero_mul]
  · calc (1 - U * Uᵀ) * Fmat Z w * (Smat Z)⁻¹ * symplJ κ
        = (1 - U * Uᵀ) * (Fmat Z w * ((Smat Z)⁻¹ * symplJ κ)) := by simp only [Matrix.mul_assoc]
      _ = (1 - U * Uᵀ) * (Fmat Z w * (symplJ κ * (Smat Z)⁻¹)) := by rw [Sinv_comm hS]
      _ = ((1 - U * Uᵀ) * (Fmat Z w * symplJ κ)) * (Smat Z)⁻¹ := by simp only [Matrix.mul_assoc]
      _ = symplJ ι * ((1 - U * Uᵀ) * Fmat Z w * (Smat Z)⁻¹) := by
          rw [Fmat_comm, ← Matrix.mul_assoc (1 - U * Uᵀ), ← one_sub_proj_comm hU]
          simp only [Matrix.mul_assoc]

lemma tangentPi_mem {U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} (hU : IsOrthosymplectic U)
    {Z : Matrix p (κ ⊕ κ) ℝ} (hS : IsUnit (Smat Z).det) (w : Matrix (ι ⊕ ι) p ℝ) :
    tangentPi U Z w ∈ tangentSpace U Z :=
  ⟨_, wᵀ * U, isHorizontal_rhs hU hS w, by simp [tangentPi, Matrix.transpose_mul, Matrix.mul_assoc]⟩

lemma tangentPi_of_mem {U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} (hU : IsOrthosymplectic U)
    {Z : Matrix p (κ ⊕ κ) ℝ} (hS : IsUnit (Smat Z).det) {x : Matrix (ι ⊕ ι) p ℝ}
    (hx : x ∈ tangentSpace U Z) : tangentPi U Z x = x := by
  obtain ⟨XU, XZ, ⟨h1, h2⟩, hxe⟩ := hx
  have e0 : (1 - U * Uᵀ) * x = XU * Zᵀ := by
    rw [hxe, Matrix.mul_add, ← Matrix.mul_assoc, one_sub_proj_mul_horizontal h1,
      ← Matrix.mul_assoc, one_sub_proj_mul_self hU, Matrix.zero_mul, add_zero]
  have hJx : (1 - U * Uᵀ) * (symplJ ι * x) = XU * symplJ κ * Zᵀ := by
    rw [← Matrix.mul_assoc, ← one_sub_proj_comm hU, Matrix.mul_assoc, e0, ← Matrix.mul_assoc,
      h2]
  have e1 : (1 - U * Uᵀ) * Fmat Z x = XU * Smat Z := by
    unfold Fmat Smat
    have e2 : (1 - U * Uᵀ) * (symplJ ι * x * Z * (symplJ κ)ᵀ)
        = XU * symplJ κ * Zᵀ * Z * (symplJ κ)ᵀ := by
      rw [show (1 - U * Uᵀ) * (symplJ ι * x * Z * (symplJ κ)ᵀ)
        = ((1 - U * Uᵀ) * (symplJ ι * x)) * Z * (symplJ κ)ᵀ by simp only [Matrix.mul_assoc], hJx]
    rw [Matrix.mul_add, ← Matrix.mul_assoc (1 - U * Uᵀ) x Z, e0, e2]
    simp only [Matrix.mul_add, Matrix.mul_assoc]
  unfold tangentPi
  rw [e1, Matrix.mul_assoc XU, Matrix.mul_nonsing_inv _ hS, Matrix.mul_one, hxe,
    Matrix.mul_add, ← Matrix.mul_assoc (U * Uᵀ) U, Matrix.mul_assoc U Uᵀ U, hU.1, Matrix.mul_one,
    ← Matrix.mul_assoc (U * Uᵀ) XU, Matrix.mul_assoc U Uᵀ XU, h1, Matrix.mul_zero,
    Matrix.zero_mul, zero_add]

lemma Sinv_transpose (Z : Matrix p (κ ⊕ κ) ℝ) : ((Smat Z)⁻¹)ᵀ = (Smat Z)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, Smat_transpose]

omit [Fintype ι] [DecidableEq κ] in
lemma one_sub_proj_transpose (U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ) : (1 - U * Uᵀ)ᵀ = 1 - U * Uᵀ := by
  simp [Matrix.transpose_mul]

lemma symplJ_transpose_mul_mul (X : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ) :
    (symplJ ι)ᵀ * X * symplJ κ = symplJ ι * X * (symplJ κ)ᵀ := by
  rw [symplJ_transpose (ι := ι), symplJ_transpose (ι := κ)]
  simp [Matrix.neg_mul, Matrix.mul_neg]

lemma inner_tangentPi_aux {U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} (hU : IsOrthosymplectic U)
    {Z : Matrix p (κ ⊕ κ) ℝ} (hS : IsUnit (Smat Z).det) (w v : Matrix (ι ⊕ ι) p ℝ) :
    ⟪(1 - U * Uᵀ) * Fmat Z w * (Smat Z)⁻¹ * Zᵀ, v⟫
      = ⟪w * Z, (1 - U * Uᵀ) * Fmat Z v * (Smat Z)⁻¹⟫ := by
  rw [Frobenius.inner_mul_right, Matrix.transpose_transpose, Frobenius.inner_mul_right,
    Sinv_transpose, Frobenius.inner_mul_left, one_sub_proj_transpose]
  unfold Fmat
  rw [inner_add_left]
  have h2 : ⟪symplJ ι * w * Z * (symplJ κ)ᵀ, (1 - U * Uᵀ) * (v * Z * (Smat Z)⁻¹)⟫
      = ⟪w * Z, (symplJ ι)ᵀ * ((1 - U * Uᵀ) * (v * Z * (Smat Z)⁻¹) * symplJ κ)⟫ := by
    rw [Frobenius.inner_mul_right, Matrix.transpose_transpose, Matrix.mul_assoc (symplJ ι),
      Frobenius.inner_mul_left]
  have h3 : (symplJ ι)ᵀ * ((1 - U * Uᵀ) * (v * Z * (Smat Z)⁻¹) * symplJ κ)
      = (1 - U * Uᵀ) * (symplJ ι * v * Z * (symplJ κ)ᵀ) * (Smat Z)⁻¹ := by
    have hc : (symplJ ι)ᵀ * (1 - U * Uᵀ) = (1 - U * Uᵀ) * (symplJ ι)ᵀ := by
      rw [symplJ_transpose, Matrix.neg_mul, Matrix.mul_neg, one_sub_proj_comm hU]
    calc (symplJ ι)ᵀ * ((1 - U * Uᵀ) * (v * Z * (Smat Z)⁻¹) * symplJ κ)
        = ((symplJ ι)ᵀ * (1 - U * Uᵀ)) * (v * Z * ((Smat Z)⁻¹ * symplJ κ)) := by
          simp only [Matrix.mul_assoc]
      _ = (1 - U * Uᵀ) * ((symplJ ι)ᵀ * (v * Z) * symplJ κ) * (Smat Z)⁻¹ := by
          rw [hc, Sinv_comm hS]; simp only [Matrix.mul_assoc]
      _ = (1 - U * Uᵀ) * (symplJ ι * (v * Z) * (symplJ κ)ᵀ) * (Smat Z)⁻¹ := by
          rw [symplJ_transpose_mul_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h2, h3, ← inner_add_right]
  congr 1
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

lemma inner_tangentPi_symm {U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} (hU : IsOrthosymplectic U)
    {Z : Matrix p (κ ⊕ κ) ℝ} (hS : IsUnit (Smat Z).det) (w v : Matrix (ι ⊕ ι) p ℝ) :
    ⟪tangentPi U Z w, v⟫ = ⟪w, tangentPi U Z v⟫ := by
  unfold tangentPi
  rw [inner_add_left, inner_add_right, inner_tangentPi_aux hU hS,
    Frobenius.inner_mul_right w Z, ← leftProj_apply, ← leftProj_apply, leftProj_symm]

/-- `w ↦ Π(w)` of Prop. 4.3 as a continuous linear map on `ℝ^{2N × p}`. -/
noncomputable def tangentPiCLM (U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ) (Z : Matrix p (κ ⊕ κ) ℝ) :
    Matrix (ι ⊕ ι) p ℝ →L[ℝ] Matrix (ι ⊕ ι) p ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := tangentPi U Z
      map_add' := fun x y => by
        simp only [tangentPi, Fmat, Matrix.mul_add, Matrix.add_mul]; abel
      map_smul' := fun c x => by
        simp only [tangentPi, Fmat, Matrix.mul_smul, Matrix.smul_mul, ← smul_add,
          RingHom.id_apply] }

@[simp] lemma tangentPiCLM_apply (U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ) (Z : Matrix p (κ ⊕ κ) ℝ)
    (w : Matrix (ι ⊕ ι) p ℝ) : tangentPiCLM U Z w = tangentPi U Z w := rfl

/-- **Prop. 4.3 and Remark 4.4** (arXiv 2008.07427), first part.  For orthosymplectic `U` and
`Z` with `S = Zᵀ Z + J_{2n} Zᵀ Z J_{2n}ᵀ` invertible (the full-rank condition (4.5)), the map
`Π(w) = (I - U Uᵀ)(w Z + J_{2N} w Z J_{2n}ᵀ) S⁻¹ Zᵀ + U Uᵀ w` is an orthogonal projector for the
Frobenius inner product (`IsOrthProj`, Remark 4.4), and its range is the tangent space
`tangentSpace U Z` of Prop. 4.1: `Π w ∈ T` and `Π x = x` for `x ∈ T`
(`tangentPi_mem`, `tangentPi_of_mem`). -/
theorem isOrthProj_tangentPi {U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} (hU : IsOrthosymplectic U)
    {Z : Matrix p (κ ⊕ κ) ℝ} (hS : IsUnit (Smat Z).det) :
    IsOrthProj (tangentPiCLM U Z) where
  idem w := tangentPi_of_mem hU hS (tangentPi_mem hU hS w)
  symm w v := inner_tangentPi_symm hU hS w v

/-- `Π` of Prop. 4.3 commutes with the symplectic unit, `Π (J_{2N} w) = J_{2N} Π(w)`.  Auxiliary:
not stated in the paper; used for the conservation argument of Section 4.2. -/
theorem tangentPi_symplJ_mul {U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} (hU : IsOrthosymplectic U)
    (Z : Matrix p (κ ⊕ κ) ℝ) (w : Matrix (ι ⊕ ι) p ℝ) :
    tangentPi U Z (symplJ ι * w) = symplJ ι * tangentPi U Z w := by
  have hF : Fmat Z (symplJ ι * w) = symplJ ι * Fmat Z w := by
    simp only [Fmat, Matrix.mul_add, Matrix.mul_assoc]
  unfold tangentPi
  rw [hF, Matrix.mul_add]
  congr 1
  · rw [← Matrix.mul_assoc (1 - U * Uᵀ) (symplJ ι), ← one_sub_proj_comm hU]
    simp only [Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← proj_comm hU]

omit [Fintype p] in
/-- The tangent space is invariant under `J_{2N}`. -/
lemma symplJ_mul_mem_tangentSpace {U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} (hU : IsOrthosymplectic U)
    {Z : Matrix p (κ ⊕ κ) ℝ} {y : Matrix (ι ⊕ ι) p ℝ} (hy : y ∈ tangentSpace U Z) :
    symplJ ι * y ∈ tangentSpace U Z := by
  obtain ⟨XU, XZ, ⟨h1, h2⟩, rfl⟩ := hy
  have hc := hU.comm
  have ht : Uᵀ * symplJ ι = symplJ κ * Uᵀ := by
    have := congrArg Matrix.transpose hc
    rw [Matrix.transpose_mul, Matrix.transpose_mul, symplJ_transpose, symplJ_transpose] at this
    simpa using this
  refine ⟨symplJ ι * XU, XZ * (symplJ κ)ᵀ, ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.mul_assoc, ht, Matrix.mul_assoc, h1, Matrix.mul_zero]
  · rw [Matrix.mul_assoc, h2]
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add,
      ← Matrix.mul_assoc, hc]

/-- **Remark 4.4** (arXiv 2008.07427): the symplectic projection property of Prop. 4.3 in the form
`⟨w - Π w, J_{2N} y⟩_F = 0` for all `y ∈ T_R M^spl`.  Here `⟨a, J b⟩_F = tr(aᵀ J_{2N} b)` equals
`∑_j ω_j(a, b)` with `ω_j(a, b) = a_jᵀ J_{2N} b_j` (see `inner_symplJ_mul_eq_sum`), so this is
the identity `∑_j ω_j(w - Π w, y) = 0` of Prop. 4.3. -/
theorem inner_sub_tangentPi_symplJ_mul {U : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} (hU : IsOrthosymplectic U)
    {Z : Matrix p (κ ⊕ κ) ℝ} (hS : IsUnit (Smat Z).det) (w : Matrix (ι ⊕ ι) p ℝ)
    {y : Matrix (ι ⊕ ι) p ℝ} (hy : y ∈ tangentSpace U Z) :
    ⟪w - tangentPi U Z w, symplJ ι * y⟫ = 0 := by
  have hJy := symplJ_mul_mem_tangentSpace hU hy
  rw [inner_sub_left, inner_tangentPi_symm hU hS, tangentPi_of_mem hU hS hJy, sub_self]

lemma inner_symplJ_mul_eq_sum (a b : Matrix (ι ⊕ ι) p ℝ) :
    ⟪a, symplJ ι * b⟫ = ∑ j, (fun i => a i j) ⬝ᵥ (symplJ ι *ᵥ fun i => b i j) := by
  simp only [Frobenius.inner_def, Matrix.mul_apply, dotProduct, Matrix.mulVec]
  rw [Finset.sum_comm]

end Tangent

/-! ### Hamiltonian conservation (Section 4.2) -/

section Conservation

/-- **Section 4.2, abstract form** (arXiv 2008.07427).  Let `H` have gradient `g`, let `J` be
skew (`⟨J z, z⟩ = 0`) and let `Π(t)` be orthogonal projectors commuting with `J`.  Along any curve
with `R' = Π(t) J ∇H(R)` the Hamiltonian is constant: `dH/dt = ⟨∇H, Π J ∇H⟩ = ⟨Π∇H, J Π∇H⟩ = 0`.
The projector may depend on time (hence on the state `R(t)`), which is the case of the paper
(`Π = Π_{T_R M^spl}`); this is stronger than the fixed-projector statement
`ODESolution.galerkin_energy_eq_of_skew` of the library.  Stated on a real inner product space
for a curve differentiable on a convex set of times; the paper's `E = ℝ^{2N × p}` with the
Frobenius inner product and `J = J_{2N}·` is `hamiltonian_conserved_matrix`.  Smoothness of `H`
is the existence of the gradient `g`. -/
theorem hamiltonian_conserved {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : E → ℝ} {g : E → E} (hH : ∀ x, HasFDerivAt H (innerSL ℝ (g x)) x)
    {J : E →L[ℝ] E} (hJ : ∀ z, ⟪J z, z⟫ = 0) {Pi : ℝ → E →L[ℝ] E}
    (hPi : ∀ t, IsOrthProj (Pi t)) (hJP : ∀ t z, J (Pi t z) = Pi t (J z))
    {R R' : ℝ → E} {s : Set ℝ} (hs : Convex ℝ s) (hR : ∀ t ∈ s, HasDerivWithinAt R (R' t) s t)
    (hR' : ∀ t ∈ s, R' t = Pi t (J (g (R t)))) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    H (R t) = H (R t₀) := by
  have hd : ∀ x ∈ s, HasDerivWithinAt (fun t => H (R t)) 0 s x := by
    intro x hx
    have h := (hH (R x)).comp_hasDerivWithinAt x (hR x hx)
    have h0 : (innerSL ℝ (g (R x))) (R' x) = 0 := by
      rw [innerSL_apply_apply, hR' x hx, ← (hPi x).symm, ← (hPi x).inner_comp, ← hJP,
        real_inner_comm, hJ]
    rw [h0] at h
    exact h
  have h := hs.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hd (fun x _ => by simp) ht₀ ht
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  exact h

omit [DecidableEq κ] in
lemma inner_symplJ_mul_self {p : Type*} [Fintype p] (z : Matrix (ι ⊕ ι) p ℝ) :
    ⟪symplJ ι * z, z⟫ = 0 := by
  have h := Frobenius.inner_mul_left (symplJ ι) z z
  rw [symplJ_transpose, Matrix.neg_mul, inner_neg_right] at h
  have := real_inner_comm z (symplJ ι * z)
  linarith

/-- **Section 4.2** (arXiv 2008.07427), matrix form.  On `ℝ^{2N × p}` with the Frobenius inner
product let `H` have Frobenius gradient `g` and let `R(t) = U(t) Z(t)ᵀ` evolve by
`R' = Π_{T_R M^spl}(X_H(R))`, `X_H = J_{2N} ∇H`, where for every `t` the basis `U(t)` is
orthosymplectic and `S(t)` invertible (so `Π(t) = tangentPi (U t) (Z t)` is the projector of
Prop. 4.3).  Then `H(R(t)) = H(R(t₀))`.  The reduced system (4.10) itself and the manifold
condition `R(t) = U(t) Z(t)ᵀ` are not needed for this step; only `R' = Π(t) X_H(R)`. -/
theorem hamiltonian_conserved_matrix {p : Type*} [Fintype p]
    {H : Matrix (ι ⊕ ι) p ℝ → ℝ} {g : Matrix (ι ⊕ ι) p ℝ → Matrix (ι ⊕ ι) p ℝ}
    (hH : ∀ x, HasFDerivAt H (innerSL ℝ (g x)) x)
    {U : ℝ → Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} {Z : ℝ → Matrix p (κ ⊕ κ) ℝ}
    (hU : ∀ t, IsOrthosymplectic (U t)) (hS : ∀ t, IsUnit (Smat (Z t)).det)
    {R R' : ℝ → Matrix (ι ⊕ ι) p ℝ} {s : Set ℝ} (hs : Convex ℝ s)
    (hR : ∀ t ∈ s, HasDerivWithinAt R (R' t) s t)
    (hR' : ∀ t ∈ s, R' t = tangentPi (U t) (Z t) (symplJ ι * g (R t))) {t₀ t : ℝ}
    (ht₀ : t₀ ∈ s) (ht : t ∈ s) : H (R t) = H (R t₀) :=
  hamiltonian_conserved (J := Frobenius.leftMulCLM (symplJ ι))
    (Pi := fun t => tangentPiCLM (U t) (Z t)) hH (fun z => inner_symplJ_mul_self z)
    (fun t => isOrthProj_tangentPi (hU t) (hS t))
    (fun t z => (tangentPi_symplJ_mul (hU t) (Z t) z).symm) hs hR hR' ht₀ ht

end Conservation

/-! ### The hypotheses are satisfiable -/

section Examples

/-- A nontrivial instance (`N = 2`, `n = 1`): the orthosymplectic `Q = [e₁ | Jᵀ e₁]` and the
nonzero horizontal vector `V = [e₂ | Jᵀ e₂]`, with `e₁, e₂` the unit vectors of the `q`-block. -/
def exQ : Matrix (Fin 2 ⊕ Fin 2) (Fin 1 ⊕ Fin 1) ℝ :=
  Matrix.of fun i j => if (i = Sum.inl 0 ∧ j = Sum.inl 0) ∨ (i = Sum.inr 0 ∧ j = Sum.inr 0)
    then 1 else 0

/-- The horizontal vector of the nontrivial instance. -/
def exV : Matrix (Fin 2 ⊕ Fin 2) (Fin 1 ⊕ Fin 1) ℝ :=
  Matrix.of fun i j => if (i = Sum.inl 1 ∧ j = Sum.inl 0) ∨ (i = Sum.inr 1 ∧ j = Sum.inr 0)
    then 1 else 0

example : IsOrthosymplectic exQ ∧ IsHorizontal exQ exV ∧ exV ≠ 0 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [exQ, Matrix.mul_apply]
  · ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [exQ, symplJ, Matrix.mul_apply]
  · ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [exQ, exV, Matrix.mul_apply]
  · ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [exV, symplJ, Matrix.mul_apply]
  · intro h
    have := congrFun (congrFun h (Sum.inl 1)) (Sum.inl 0)
    simp [exV] at this

/-- The identity is orthosymplectic, and `S = 2 I` is invertible for `Z = I`, so the hypotheses
of the projection and conservation theorems are met (here `p = 2n`). -/
example : IsOrthosymplectic (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) ∧
    IsUnit (Smat (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)).det := by
  refine ⟨⟨by simp, by simp⟩, ?_⟩
  have : Smat (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) = (2 : ℝ) • 1 := by
    simp [Smat, symplJ_mul_transpose, two_smul]
  rw [this, Matrix.det_smul, Matrix.det_one, mul_one]
  exact (pow_ne_zero _ two_ne_zero).isUnit

end Examples

end LeanDLRA.Literature.P2008_07427
