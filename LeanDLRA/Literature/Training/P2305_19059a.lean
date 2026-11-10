import LeanDLRA.Foundations.Existence
import LeanDLRA.Foundations.Galerkin
import LeanDLRA.Foundations.OneSided
import LeanDLRA.LinearAlgebra.Factorization.Defs
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Training.Descent

/-!
# Results of arXiv 2305.19059: Geometry-aware training of Tucker-factorized layers (TDLRT)

This module proves the theorems of Zangrando, Schotthöfer, Ceruti, Kusch and Tudisco on genuine
tensors rather than on an abstract inner product space.  It builds real tensors `Tensor n` with
the entrywise inner product, the multilinear product `tucker U C = C ×ⱼ Uⱼ`, the matricizations
`mat i` (a linear isometry onto matrices with the Frobenius norm, whose inverse is `Tenᵢ`), the
Tucker tangent space `tangentSpace` of eq. (1) and its orthogonal projector `tangentProj`.  The
main results are `thm_2_1` (with `thm_2_1_frozen`, `hasDerivAt_K`, `K_eq_iff`), `cor_2_2`, `thm_3_1`
(with `thm_3_1_uniform`, `thm_3_1_tangent`), `lemma_G_2`, `thm_3_2` (with
`thm_3_2_of_inner_bound`), `lemma_G_3` and `lemma_G_3_counterexample`.  Along the way eq. (3) and
eq. (4) are shown to be equivalent (`core_eq_of_flow`, `factor_eq_of_flow`, `flow_of_factor_eq`),
`tangentProj_eq` gives the closed form of `P(W)`, and `norm_tangentProj_le` compares the augmented
core gradient with the Riemannian gradient.  Hypotheses are shown to be satisfiable by
`thm_2_1_hypotheses`, `isCoreQR_unitCore`, `exists_core_flow` and `thm_3_2_instance`.

Where the paper needs repair.  The `Kᵢ` equation of Thm 2.1 holds exactly when `Qᵢᵀ Q̇ᵢ = 0`; the
printed statement omits this and its proof freezes `Vᵢ`, so `thm_2_1` is Thm 2.1 under the extra
hypothesis `Qᵢᵀ Q̇ᵢ = 0`.  No flow whose QR factors violate it is formalized, so the printed
statement is not refuted here.  In Thm 3.1 the constants of the proof
depend on `λ`, and `α > 0` fails at stationary points; the correct uniform statement holds for
small `λ` away from such points.  In Thm 3.2 the proof applies Lemma G.3 to bases that depend on
the batch, where it is false; we assume that the batch of the core step is drawn after the bases
are fixed.  Whether the printed Thm 3.2 holds without this is left open.  Each theorem's docstring
lists its differences from the paper.

Thm 3.3 and Lemma F.1 are not repeated here: their abstract versions are
`LeanDLRA.aug_tucker_global_error` and `LeanDLRA.norm_sub_modeProd_apply_le`, and `hasDerivAt_kStep`
with `isOrthProj_coProj` identifies the concrete `K`-step with the abstract one.
-/

open Set Filter Topology Finset MeasureTheory
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2305_19059

open LeanDLRA

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### Kronecker products of a family of matrices -/

section Kron

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {l m p : κ → Type*} [∀ j, Fintype (l j)] [∀ j, Fintype (m j)] [∀ j, Fintype (p j)]

/-- The Kronecker product `⊗ⱼ Aⱼ` of a family of matrices, with multi-indices as row and column
indices: its entries are `(⊗ⱼ Aⱼ) a b = ∏ⱼ Aⱼ (a j) (b j)`. -/
def kron (A : ∀ j, Matrix (l j) (m j) ℝ) : Matrix (∀ j, l j) (∀ j, m j) ℝ :=
  Matrix.of fun a b => ∏ j, A j (a j) (b j)

/-- The entries of `⊗ⱼ Aⱼ`. -/
@[simp] lemma kron_apply (A : ∀ j, Matrix (l j) (m j) ℝ) (a : ∀ j, l j) (b : ∀ j, m j) :
    kron A a b = ∏ j, A j (a j) (b j) := rfl

/-- Mixed product rule: `(⊗ⱼ Aⱼ) (⊗ⱼ Bⱼ) = ⊗ⱼ (Aⱼ Bⱼ)`. -/
theorem kron_mul (A : ∀ j, Matrix (l j) (m j) ℝ) (B : ∀ j, Matrix (m j) (p j) ℝ) :
    kron A * kron B = kron fun j => A j * B j := by
  ext a c
  simp only [Matrix.mul_apply, kron_apply, ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- `(⊗ⱼ Aⱼ)ᵀ = ⊗ⱼ Aⱼᵀ`. -/
theorem kron_transpose (A : ∀ j, Matrix (l j) (m j) ℝ) :
    (kron A)ᵀ = kron fun j => (A j)ᵀ := by
  ext a b
  simp

/-- The Kronecker product of identities is the identity. -/
theorem kron_one [∀ j, DecidableEq (l j)] : kron (fun j => (1 : Matrix (l j) (l j) ℝ)) = 1 := by
  ext a b
  rw [kron_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.1 h
    simp only [h, ite_false]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

/-- A Kronecker product with a zero factor vanishes. -/
theorem kron_eq_zero {A : ∀ j, Matrix (l j) (m j) ℝ} {k : κ} (h : A k = 0) : kron A = 0 := by
  ext a b
  rw [kron_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [h])

end Kron

/-! ### Tensors, the multilinear product and the matricizations -/

section Tensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n m r : ι → Type*} [∀ i, Fintype (n i)] [∀ i, Fintype (m i)] [∀ i, Fintype (r i)]

/-- Real tensors with mode index types `n i`, with the Euclidean (entrywise) inner product. -/
abbrev Tensor (n : ι → Type*) [∀ i, Fintype (n i)] : Type _ := EuclideanSpace ℝ (∀ i, n i)

/-- The multilinear product `C ×ⱼ Uⱼ`, entrywise
`(C ×ⱼ Uⱼ) a = ∑_b (∏ⱼ Uⱼ (a j) (b j)) C b`. -/
noncomputable def tucker (U : ∀ i, Matrix (n i) (r i) ℝ) : Tensor r →L[ℝ] Tensor n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun C => WithLp.toLp 2 fun a => ∑ b, kron U a b * C b
      map_add' := fun C D => by
        ext a
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c C => by
        ext a
        simp [Finset.mul_sum, mul_left_comm] }

/-- The entries of `C ×ⱼ Uⱼ`. -/
lemma tucker_apply (U : ∀ i, Matrix (n i) (r i) ℝ) (C : Tensor r) (a : ∀ i, n i) :
    tucker U C a = ∑ b, kron U a b * C b := rfl

/-- Composition of multilinear products: `(C ×ⱼ Bⱼ) ×ⱼ Aⱼ = C ×ⱼ (Aⱼ Bⱼ)`. -/
theorem tucker_tucker (A : ∀ i, Matrix (m i) (n i) ℝ) (B : ∀ i, Matrix (n i) (r i) ℝ)
    (C : Tensor r) : tucker A (tucker B C) = tucker (fun i => A i * B i) C := by
  ext a
  simp only [tucker_apply, ← kron_mul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [mul_assoc]

/-- The multilinear product with identities is the identity. -/
theorem tucker_one [∀ i, DecidableEq (n i)] (C : Tensor n) :
    tucker (fun i => (1 : Matrix (n i) (n i) ℝ)) C = C := by
  ext a
  rw [tucker_apply, kron_one]
  simp [Matrix.one_apply]

/-- A multilinear product with a zero factor vanishes. -/
theorem tucker_eq_zero {U : ∀ i, Matrix (n i) (r i) ℝ} {k : ι} (h : U k = 0) (C : Tensor r) :
    tucker U C = 0 := by
  ext a
  rw [tucker_apply, kron_eq_zero h]
  simp

/-- The adjoint of `· ×ⱼ Uⱼ` is `· ×ⱼ Uⱼᵀ`. -/
theorem inner_tucker (U : ∀ i, Matrix (n i) (r i) ℝ) (C : Tensor r) (D : Tensor n) :
    ⟪tucker U C, D⟫ = ⟪C, tucker (fun i => (U i)ᵀ) D⟫ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, tucker_apply, Finset.sum_mul,
    Finset.mul_sum, ← kron_transpose, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

/-- All modes but `i`. -/
abbrev Rest (n : ι → Type*) (i : ι) : Type _ := ∀ j : {j // j ≠ i}, n j

/-- `⊗_{j ≠ i} Uⱼ`. -/
def kronRest (U : ∀ i, Matrix (n i) (r i) ℝ) (i : ι) : Matrix (Rest n i) (Rest r i) ℝ :=
  kron fun j : {j // j ≠ i} => U j

/-- The entries of the mode-`i` unfolding. -/
private def glue (i : ι) (a : n i) (b : Rest n i) : ∀ j, n j :=
  (Equiv.piSplitAt i n).symm (a, b)

@[simp] private lemma glue_self (i : ι) (a : n i) (b : Rest n i) : glue i a b i = a := by
  simp [glue, Equiv.piSplitAt]

@[simp] private lemma glue_ne (i : ι) (a : n i) (b : Rest n i) (j : {j // j ≠ i}) :
    glue i a b j = b j := by
  simp [glue, Equiv.piSplitAt, j.2]

private lemma sum_glue {M : Type*} [AddCommMonoid M] (i : ι) (f : (∀ j, n j) → M) :
    ∑ x, f x = ∑ a : n i, ∑ b : Rest n i, f (glue i a b) := by
  rw [← (Equiv.piSplitAt i n).symm.sum_comp, Fintype.sum_prod_type]
  rfl

private lemma prod_glue {i : ι} (f : ι → ℝ) : ∏ j, f j = f i * ∏ j : {j // j ≠ i}, f j :=
  Fintype.prod_eq_mul_prod_subtype_ne f i

/-- The mode-`i` matricization `Matᵢ`, a linear isometry from tensors to matrices with the
Frobenius norm; `(mat i).symm` is the tensorization `Tenᵢ` along mode `i`. -/
noncomputable def mat (i : ι) : Tensor n ≃ₗᵢ[ℝ] Matrix (n i) (Rest n i) ℝ :=
  LinearIsometryEquiv.mk
    { toFun := fun T => Matrix.of fun a b => T (glue i a b)
      invFun := fun X => WithLp.toLp 2 fun x => X (x i) fun j => x j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun T => by
        ext x
        have : glue i (x i) (fun j : {j // j ≠ i} => x j) = x :=
          (Equiv.piSplitAt i n).symm_apply_apply x
        simp [this]
      right_inv := fun X => by
        ext a b
        simp only [Matrix.of_apply, glue_self]
        congr 1
        funext j
        exact glue_ne i a b j }
    fun T => by
      have h : ‖(Matrix.of fun a b => T (glue i a b) : Matrix (n i) (Rest n i) ℝ)‖ ^ 2 =
          ‖T‖ ^ 2 := by
        rw [Frobenius.norm_sq_eq_sum, EuclideanSpace.norm_sq_eq]
        simp only [Matrix.of_apply, Real.norm_eq_abs, sq_abs]
        rw [sum_glue i]
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- The entries of the mode-`i` matricization. -/
@[simp] lemma mat_apply (i : ι) (T : Tensor n) (a : n i) (b : Rest n i) :
    mat i T a b = T (glue i a b) := rfl

/-- `Matᵢ(C ×ⱼ Uⱼ) = Uᵢ Matᵢ(C) (⊗_{j ≠ i} Uⱼ)ᵀ`. -/
theorem mat_tucker (U : ∀ i, Matrix (n i) (r i) ℝ) (C : Tensor r) (i : ι) :
    mat i (tucker U C) = U i * mat i C * (kronRest U i)ᵀ := by
  ext a b
  simp only [mat_apply, tucker_apply, Matrix.mul_apply, Matrix.transpose_apply, kronRest,
    kron_apply]
  rw [sum_glue i]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [prod_glue (i := i)]
  simp only [glue_self, glue_ne]
  ring

/-! ### Calculus -/

/-- A matrix curve is differentiable as soon as its entries are. -/
private lemma hasDerivAt_matrix {a' b' : Type*} [Fintype a'] [Fintype b']
    {f : ℝ → Matrix a' b' ℝ} {f' : Matrix a' b' ℝ} {t : ℝ}
    (h : ∀ a b, HasDerivAt (fun s => f s a b) (f' a b) t) : HasDerivAt f f' t := by
  classical
  have e : f = fun s => ∑ a, ∑ b, f s a b • Matrix.single a b (1 : ℝ) := by
    funext s
    conv_lhs => rw [Matrix.matrix_eq_sum_single (f s)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have e' : f' = ∑ a, ∑ b, f' a b • Matrix.single a b (1 : ℝ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single f']
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e, e']
  exact HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ => (h a b).smul_const _

/-- The entries of a differentiable matrix curve are differentiable. -/
private lemma hasDerivAt_entry {a' b' : Type*} [Fintype a'] [Fintype b']
    {f : ℝ → Matrix a' b' ℝ} {f' : Matrix a' b' ℝ} {t : ℝ} (h : HasDerivAt f f' t) (a : a')
    (b : b') : HasDerivAt (fun s => f s a b) (f' a b) t := by
  classical
  exact (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℝ ℝ a b)).hasFDerivAt.comp_hasDerivAt t h

/-- The entries of a differentiable tensor curve are differentiable. -/
private lemma hasDerivAt_tensor_entry {T : ℝ → Tensor n} {T' : Tensor n} {t : ℝ}
    (h : HasDerivAt T T' t) (a : ∀ i, n i) : HasDerivAt (fun s => T s a) (T' a) t :=
  (EuclideanSpace.proj a : Tensor n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t h

/-- A tensor curve is differentiable as soon as its entries are. -/
private lemma hasDerivAt_tensor {T : ℝ → Tensor n} {T' : Tensor n} {t : ℝ}
    (h : ∀ a, HasDerivAt (fun s => T s a) (T' a) t) : HasDerivAt T T' t := by
  have h1 : HasDerivAt (fun s => (T s).ofLp) T'.ofLp t := hasDerivAt_pi.2 h
  exact ((PiLp.continuousLinearEquiv 2 ℝ fun _ : (∀ i, n i) => ℝ).symm
    : (∀ _ : (∀ i, n i), ℝ) →L[ℝ] Tensor n).hasFDerivAt.comp_hasDerivAt t h1

/-- Product rule for `⊗ⱼ Aⱼ(t)`:
`(⊗ⱼ Aⱼ)˙ = ∑ₖ (Ȧₖ ⊗ ⊗_{j ≠ k} Aⱼ)`. -/
theorem hasDerivAt_kron {κ : Type*} [Fintype κ] [DecidableEq κ] {l m : κ → Type*}
    [∀ j, Fintype (l j)] [∀ j, Fintype (m j)] {A : ℝ → ∀ j, Matrix (l j) (m j) ℝ}
    {A' : ∀ j, Matrix (l j) (m j) ℝ} {t : ℝ} (hA : ∀ j, HasDerivAt (fun s => A s j) (A' j) t) :
    HasDerivAt (fun s => kron (A s)) (∑ k, kron (Function.update (A t) k (A' k))) t := by
  refine hasDerivAt_matrix fun a b => ?_
  simp only [kron_apply, Matrix.sum_apply]
  refine (HasDerivAt.fun_finsetProd fun j _ => hasDerivAt_entry (hA j) (a j) (b j)).congr_deriv ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), Function.update_self, smul_eq_mul,
    mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- The tangent vector `δC ×ⱼ Uⱼ + ∑ₖ C ×ₖ δUₖ ×_{j ≠ k} Uⱼ`. -/
noncomputable def tuckerDot (U δU : ∀ i, Matrix (n i) (r i) ℝ) (C δC : Tensor r) : Tensor n :=
  tucker U δC + ∑ k, tucker (Function.update U k (δU k)) C

/-- Leibniz rule for `t ↦ C(t) ×ⱼ Uⱼ(t)`. -/
theorem hasDerivAt_tucker {U : ℝ → ∀ i, Matrix (n i) (r i) ℝ} {U' : ∀ i, Matrix (n i) (r i) ℝ}
    {C : ℝ → Tensor r} {C' : Tensor r} {t : ℝ} (hU : ∀ j, HasDerivAt (fun s => U s j) (U' j) t)
    (hC : HasDerivAt C C' t) :
    HasDerivAt (fun s => tucker (U s) (C s)) (tuckerDot (U t) U' (C t) C') t := by
  refine hasDerivAt_tensor fun a => ?_
  simp only [tucker_apply]
  have h : ∀ b, HasDerivAt (fun s => kron (U s) a b * C s b)
      ((∑ k, kron (Function.update (U t) k (U' k))) a b * C t b + kron (U t) a b * C' b) t :=
    fun b => (hasDerivAt_entry (hasDerivAt_kron hU) a b).mul (hasDerivAt_tensor_entry hC b)
  refine (HasDerivAt.fun_sum fun b _ => h b).congr_deriv ?_
  simp only [tuckerDot, PiLp.add_apply, tucker_apply, WithLp.ofLp_sum, Finset.sum_apply,
    Matrix.sum_apply, Finset.sum_add_distrib, Finset.sum_mul]
  rw [add_comm, Finset.sum_comm]

/-! ### The tangent space of the Tucker manifold -/

/-- `(⊗_{j ≠ i} Aⱼ)ᵀ (⊗_{j ≠ i} Bⱼ) = ⊗_{j ≠ i} (Aⱼᵀ Bⱼ)`. -/
theorem kronRest_transpose_mul {m' : ι → Type*} [∀ i, Fintype (m' i)]
    (A : ∀ i, Matrix (n i) (r i) ℝ) (B : ∀ i, Matrix (n i) (m' i) ℝ) (i : ι) :
    (kronRest A i)ᵀ * kronRest B i = kronRest (fun j => (A j)ᵀ * B j) i := by
  unfold kronRest
  rw [kron_transpose, kron_mul]

/-- `⊗_{j ≠ i} Uⱼ` does not depend on `Uᵢ`. -/
theorem kronRest_update_self (U : ∀ i, Matrix (n i) (r i) ℝ) (i : ι)
    (δ : Matrix (n i) (r i) ℝ) : kronRest (Function.update U i δ) i = kronRest U i := by
  unfold kronRest
  congr 1
  funext j
  rw [Function.update_of_ne j.2]

/-- `⊗_{j ≠ i} Aⱼ` vanishes if `Aₖ = 0` for some `k ≠ i`. -/
theorem kronRest_eq_zero {A : ∀ i, Matrix (n i) (r i) ℝ} {i k : ι} (hk : k ≠ i) (h : A k = 0) :
    kronRest A i = 0 :=
  kron_eq_zero (k := (⟨k, hk⟩ : {j // j ≠ i})) h

/-- The tangent space `T_U 𝒮` of the Stiefel manifold at `U`. -/
def stiefelTangent {m' k' : Type*} [Fintype m'] [Fintype k'] (U : Matrix m' k' ℝ) :
    Submodule ℝ (Matrix m' k' ℝ) where
  carrier := {δ | Uᵀ * δ + δᵀ * U = 0}
  add_mem' := fun {a b} ha hb => by
    have ha' : Uᵀ * a + aᵀ * U = 0 := ha
    have hb' : Uᵀ * b + bᵀ * U = 0 := hb
    change Uᵀ * (a + b) + (a + b)ᵀ * U = 0
    rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, add_add_add_comm, ha', hb', add_zero]
  zero_mem' := by simp
  smul_mem' := fun c a ha => by
    have ha' : Uᵀ * a + aᵀ * U = 0 := ha
    change Uᵀ * (c • a) + (c • a)ᵀ * U = 0
    rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, ha', smul_zero]

/-- The tangent space (1) of arXiv 2305.19059 at `W = C ×ⱼ Uⱼ`: the vectors
`δC ×ⱼ Uⱼ + ∑ₖ C ×ₖ δUₖ ×_{j ≠ k} Uⱼ` with `δUₖ ∈ T_{Uₖ} 𝒮ₖ`.  (These vectors already form a
subspace, `mem_tangentSpace_iff`; the span merely packages them as a `Submodule`.) -/
noncomputable def tangentSpace (U : ∀ i, Matrix (n i) (r i) ℝ) (C : Tensor r) :
    Submodule ℝ (Tensor n) :=
  Submodule.span ℝ {X | ∃ (δC : Tensor r) (δU : ∀ i, Matrix (n i) (r i) ℝ),
    (∀ j, δU j ∈ stiefelTangent (U j)) ∧ X = tuckerDot U δU C δC}

/-- The orthogonal projector `P(W)` onto the tangent space at `W = C ×ⱼ Uⱼ`. -/
noncomputable def tangentProj (U : ∀ i, Matrix (n i) (r i) ℝ) (C : Tensor r) :
    Tensor n →L[ℝ] Tensor n :=
  (tangentSpace U C).starProjection

/-- Core variations `D ×ⱼ Uⱼ` are tangent. -/
theorem tucker_mem_tangentSpace (U : ∀ i, Matrix (n i) (r i) ℝ) (C D : Tensor r) :
    tucker U D ∈ tangentSpace U C := by
  refine Submodule.subset_span ⟨D, 0, fun j => zero_mem _, ?_⟩
  unfold tuckerDot
  rw [Finset.sum_eq_zero fun k _ => tucker_eq_zero (k := k) (by simp) C, add_zero]

/-- Basis variations `C ×ₖ δ ×_{j ≠ k} Uⱼ` with `δ ∈ T_{Uₖ} 𝒮ₖ` are tangent. -/
theorem tucker_update_mem_tangentSpace (U : ∀ i, Matrix (n i) (r i) ℝ) (C : Tensor r) {k : ι}
    {δ : Matrix (n k) (r k) ℝ} (hδ : δ ∈ stiefelTangent (U k)) :
    tucker (Function.update U k δ) C ∈ tangentSpace U C := by
  refine Submodule.subset_span ⟨0, Function.update 0 k δ, fun j => ?_, ?_⟩
  · by_cases h : j = k
    · subst h
      simpa using hδ
    · simp [Function.update_of_ne h, zero_mem]
  · unfold tuckerDot
    rw [map_zero, zero_add, Finset.sum_eq_single k]
    · rw [Function.update_self]
    · intro j _ hj
      exact tucker_eq_zero (k := j) (by simp [Function.update_of_ne hj]) C
    · simp

section QR

variable [∀ i, DecidableEq (r i)]

/-- `⊗_{j ≠ i} Uⱼ` has orthonormal columns if the `Uⱼ` have. -/
theorem kronRest_orth {U : ∀ i, Matrix (n i) (r i) ℝ} (hU : ∀ j, (U j)ᵀ * U j = 1) (i : ι) :
    (kronRest U i)ᵀ * kronRest U i = 1 := by
  rw [kronRest_transpose_mul]
  simp only [hU]
  exact kron_one

/-- `(δC ×ⱼ Uⱼ + ∑ₖ C ×ₖ δUₖ ×_{j ≠ k} Uⱼ) ×ⱼ Uⱼᵀ = δC` under the gauge `Uⱼᵀ δUⱼ = 0`. -/
theorem tucker_tuckerDot {U δU : ∀ i, Matrix (n i) (r i) ℝ} (hU : ∀ j, (U j)ᵀ * U j = 1)
    (hg : ∀ j, (U j)ᵀ * δU j = 0) (C δC : Tensor r) :
    tucker (fun j => (U j)ᵀ) (tuckerDot U δU C δC) = δC := by
  unfold tuckerDot
  rw [map_add, map_sum, tucker_tucker]
  have h1 : (fun j => (U j)ᵀ * U j) = fun j => 1 := funext hU
  rw [h1, tucker_one, Finset.sum_eq_zero, add_zero]
  intro k _
  rw [tucker_tucker]
  exact tucker_eq_zero (k := k) (by simp [hg k]) C

/-- `Matᵢ(δC ×ⱼ Uⱼ + ∑ₖ C ×ₖ δUₖ ×_{j ≠ k} Uⱼ) (⊗_{j ≠ i} Uⱼ) = Uᵢ Matᵢ(δC) + δUᵢ Matᵢ(C)` under
the gauge `Uⱼᵀ δUⱼ = 0`. -/
theorem mat_tuckerDot_mul {U δU : ∀ i, Matrix (n i) (r i) ℝ} (hU : ∀ j, (U j)ᵀ * U j = 1)
    (hg : ∀ j, (U j)ᵀ * δU j = 0) (C δC : Tensor r) (i : ι) :
    mat i (tuckerDot U δU C δC) * kronRest U i = U i * mat i δC + δU i * mat i C := by
  have hE := kronRest_orth hU i
  unfold tuckerDot
  rw [map_add, map_sum, Matrix.add_mul, Matrix.sum_mul, mat_tucker,
    Matrix.mul_assoc (U i * mat i δC), hE, Matrix.mul_one]
  congr 1
  rw [Finset.sum_eq_single i]
  · rw [mat_tucker, Function.update_self, kronRest_update_self, Matrix.mul_assoc (δU i * mat i C),
      hE, Matrix.mul_one]
  · intro k _ hk
    rw [mat_tucker, Matrix.mul_assoc, kronRest_transpose_mul, kronRest_eq_zero hk, Matrix.mul_zero]
    have : ((U k)ᵀ * δU k)ᵀ = (δU k)ᵀ * U k := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [Function.update_self, ← this, hg k, Matrix.transpose_zero]
  · simp

/-- `Matᵢ(C)ᵀ = Q Sᵀ` with `Qᵀ Q = 1` and `S` invertible: the QR decomposition of the unfolded
core used in arXiv 2305.19059.  Triangularity of `S` plays no role and is not required. -/
structure IsCoreQR (i : ι) (C : Tensor r) (Q : Matrix (Rest r i) (r i) ℝ)
    (S : Matrix (r i) (r i) ℝ) : Prop where
  orth : Qᵀ * Q = 1
  fact : (mat i C)ᵀ = Q * Sᵀ
  unit : IsUnit S

/-- `Matᵢ(C) = S Qᵀ`. -/
lemma IsCoreQR.mat_eq {i : ι} {C : Tensor r} {Q : Matrix (Rest r i) (r i) ℝ}
    {S : Matrix (r i) (r i) ℝ} (h : IsCoreQR i C Q S) : mat i C = S * Qᵀ := by
  have := congrArg Matrix.transpose h.fact
  simpa [Matrix.transpose_mul] using this

/-- `Sᵢ = Matᵢ(C) Qᵢ`, as in the proof of Thm 2.1 of arXiv 2305.19059. -/
lemma IsCoreQR.mat_mul {i : ι} {C : Tensor r} {Q : Matrix (Rest r i) (r i) ℝ}
    {S : Matrix (r i) (r i) ℝ} (h : IsCoreQR i C Q S) : mat i C * Q = S := by
  rw [h.mat_eq, Matrix.mul_assoc, h.orth, Matrix.mul_one]

/-- **Bridge to the core frames.** `IsCoreQR i C Q S` says exactly that `Q` is an orthonormal basis
of the column space of `Matᵢ(C)ᵀ` (the core `Matrix.IsOrthBasisOf`) and `S = Matᵢ(C) Q`. The
invertibility of `S` asked for by `IsCoreQR` is then automatic, because `Q` has as many columns as
`Matᵢ(C)ᵀ`. -/
theorem isCoreQR_iff {i : ι} {C : Tensor r} {Q : Matrix (Rest r i) (r i) ℝ}
    {S : Matrix (r i) (r i) ℝ} :
    IsCoreQR i C Q S ↔ Matrix.IsOrthBasisOf Q (mat i C)ᵀ ∧ S = mat i C * Q := by
  constructor
  · intro h
    have hS : IsUnit Sᵀ.det := by
      rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det S).1 h.unit
    refine ⟨⟨h.orth, ?_, Sᵀ⁻¹, ?_⟩, h.mat_mul.symm⟩
    · rw [h.fact, ← Matrix.mul_assoc, Matrix.mul_assoc Q, h.orth, Matrix.mul_one]
    · rw [h.fact, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hS, Matrix.mul_one]
  · rintro ⟨hb, rfl⟩
    obtain ⟨C₀, hC₀⟩ := hb.span
    have hQt : Qᵀ = C₀ᵀ * mat i C := by
      rw [hC₀, Matrix.transpose_mul, Matrix.transpose_transpose]
    have h1 : C₀ᵀ * (mat i C * Q) = 1 := by rw [← Matrix.mul_assoc, ← hQt, hb.orth]
    refine ⟨hb.orth, ?_, (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse h1)⟩
    rw [Matrix.transpose_mul, ← Matrix.mul_assoc, hb.capture]

/-- The orthonormal factor of the QR decomposition of `Matᵢ(C)ᵀ` is an orthonormal basis of its
column space (`Matrix.IsOrthBasisOf`), hence captures it (`Matrix.IsOrthCapture`). -/
theorem IsCoreQR.isOrthBasisOf {i : ι} {C : Tensor r} {Q : Matrix (Rest r i) (r i) ℝ}
    {S : Matrix (r i) (r i) ℝ} (h : IsCoreQR i C Q S) : Matrix.IsOrthBasisOf Q (mat i C)ᵀ :=
  (isCoreQR_iff.1 h).1

/-- The matrix `Vᵢ = (⊗_{j ≠ i} Uⱼ) Qᵢ` of arXiv 2305.19059; `Matᵢ(W) = Uᵢ Sᵢ Vᵢᵀ`. -/
def coFrame (U : ∀ i, Matrix (n i) (r i) ℝ) (i : ι) (Q : Matrix (Rest r i) (r i) ℝ) :
    Matrix (Rest n i) (r i) ℝ :=
  kronRest U i * Q

/-- `Matᵢ(W) = Uᵢ Sᵢ Vᵢᵀ`. -/
theorem mat_tucker_eq {U : ∀ i, Matrix (n i) (r i) ℝ} {C : Tensor r} {i : ι}
    {Q : Matrix (Rest r i) (r i) ℝ} {S : Matrix (r i) (r i) ℝ} (hQR : IsCoreQR i C Q S) :
    mat i (tucker U C) = U i * S * (coFrame U i Q)ᵀ := by
  rw [mat_tucker, hQR.mat_eq, coFrame, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- Every `Tenᵢ(A Vᵢᵀ)` is tangent at `W = C ×ⱼ Uⱼ`.  The part of `A` in the range of `Uᵢ` is a core
variation; the part orthogonal to it is a variation `δUᵢ = (1 - Uᵢ Uᵢᵀ) A Sᵢ⁻¹` of the basis, and
this is where invertibility of `Sᵢ` (that is, `W ∈ ℳ_ρ`) enters. -/
theorem ten_mem_tangentSpace {U : ∀ i, Matrix (n i) (r i) ℝ} {C : Tensor r} {i : ι}
    (hUi : (U i)ᵀ * U i = 1) {Q : Matrix (Rest r i) (r i) ℝ} {S : Matrix (r i) (r i) ℝ}
    (hQR : IsCoreQR i C Q S) (A : Matrix (n i) (r i) ℝ) :
    (mat i).symm (A * (coFrame U i Q)ᵀ) ∈ tangentSpace U C := by
  have hS : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hQR.unit
  set A₁ := (U i)ᵀ * A with hA₁
  set δ := (A - U i * A₁) * S⁻¹ with hδ
  have hδS : δ * S = A - U i * A₁ := by
    rw [hδ, Matrix.mul_assoc, Matrix.nonsing_inv_mul S hS, Matrix.mul_one]
  have hUδ : (U i)ᵀ * δ = 0 := by
    rw [hδ, ← Matrix.mul_assoc, Matrix.mul_sub, ← Matrix.mul_assoc, hUi, Matrix.one_mul, hA₁,
      sub_self, Matrix.zero_mul]
  have hδm : δ ∈ stiefelTangent (U i) := by
    change (U i)ᵀ * δ + δᵀ * U i = 0
    have : ((U i)ᵀ * δ)ᵀ = δᵀ * U i := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [← this, hUδ, Matrix.transpose_zero, add_zero]
  have key : (mat i).symm (A * (coFrame U i Q)ᵀ) =
      tucker U ((mat i).symm (A₁ * Qᵀ)) + tucker (Function.update U i δ) C := by
    apply (mat i).injective
    rw [LinearIsometryEquiv.apply_symm_apply, map_add, mat_tucker, mat_tucker,
      LinearIsometryEquiv.apply_symm_apply, Function.update_self, kronRest_update_self, hQR.mat_eq,
      coFrame, Matrix.transpose_mul]
    calc A * (Qᵀ * (kronRest U i)ᵀ)
        = (U i * A₁ + (A - U i * A₁)) * (Qᵀ * (kronRest U i)ᵀ) := by rw [add_sub_cancel]
      _ = U i * (A₁ * Qᵀ) * (kronRest U i)ᵀ + δ * (S * Qᵀ) * (kronRest U i)ᵀ := by
          rw [← hδS]
          simp only [Matrix.add_mul, Matrix.mul_assoc]
  rw [key]
  exact add_mem (tucker_mem_tangentSpace U C _) (tucker_update_mem_tangentSpace U C hδm)

/-- `Matᵢ(P(W) X) Vᵢ = Matᵢ(X) Vᵢ`: the projector `P(W)` is invisible to the `Kᵢ` equation. -/
theorem mat_tangentProj_mul {U : ∀ i, Matrix (n i) (r i) ℝ} {C : Tensor r} {i : ι}
    (hUi : (U i)ᵀ * U i = 1) {Q : Matrix (Rest r i) (r i) ℝ} {S : Matrix (r i) (r i) ℝ}
    (hQR : IsCoreQR i C Q S) (X : Tensor n) :
    mat i (tangentProj U C X) * coFrame U i Q = mat i X * coFrame U i Q := by
  refine ext_inner_right ℝ fun A => ?_
  have h := ten_mem_tangentSpace hUi hQR A
  rw [Frobenius.inner_mul_right, Frobenius.inner_mul_right,
    ← (mat i).apply_symm_apply (A * (coFrame U i Q)ᵀ), LinearIsometryEquiv.inner_map_map,
    LinearIsometryEquiv.inner_map_map, tangentProj, Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.2 h]

end QR

/-- `P(W) X ×ⱼ Uⱼᵀ = X ×ⱼ Uⱼᵀ`: the projector `P(W)` is invisible to the core equation. -/
theorem tucker_tangentProj (U : ∀ i, Matrix (n i) (r i) ℝ) (C : Tensor r) (X : Tensor n) :
    tucker (fun j => (U j)ᵀ) (tangentProj U C X) = tucker (fun j => (U j)ᵀ) X := by
  refine ext_inner_right ℝ fun D => ?_
  rw [real_inner_comm, ← inner_tucker, real_inner_comm D, ← inner_tucker, tangentProj,
    ← Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.2 (tucker_mem_tangentSpace U C D)]

/-! ### Gradients of the reduced losses -/

/-- Chain rule for gradients: `∇(f ∘ T) = T† ∘ ∇f ∘ T`. -/
private lemma hasFDerivAt_comp_clm {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [InnerProductSpace ℝ E₁] [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] {f : E₂ → ℝ}
    {f' : E₂ → E₂} (hf : ∀ x, HasFDerivAt f (innerSL ℝ (f' x)) x) (T : E₁ →L[ℝ] E₂)
    (Ta : E₂ → E₁) (hT : ∀ a b, ⟪T a, b⟫ = ⟪a, Ta b⟫) (x : E₁) :
    HasFDerivAt (fun y => f (T y)) (innerSL ℝ (Ta (f' (T x)))) x := by
  have h := (hf (T x)).comp x T.hasFDerivAt
  have e : (innerSL ℝ (f' (T x))).comp T = innerSL ℝ (Ta (f' (T x))) := by
    ext y
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    rw [real_inner_comm, hT, real_inner_comm]
  rw [e] at h
  exact h

/-- The gradient of `D ↦ ℒ(D ×ⱼ Uⱼ)` at `D` is `∇ℒ(D ×ⱼ Uⱼ) ×ⱼ Uⱼᵀ`. -/
theorem hasFDerivAt_loss_tucker {ℒ : Tensor n → ℝ} {g : Tensor n → Tensor n}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (U : ∀ i, Matrix (n i) (r i) ℝ) (D : Tensor r) :
    HasFDerivAt (fun D' => ℒ (tucker U D'))
      (innerSL ℝ (tucker (fun j => (U j)ᵀ) (g (tucker U D)))) D :=
  hasFDerivAt_comp_clm hℒ (tucker U) _ (inner_tucker U) D

/-- `⟪Tenᵢ(K Yᵀ), T⟫ = ⟪K, Matᵢ(T) Y⟫`. -/
theorem inner_ten {k' : Type*} [Fintype k'] (i : ι) (Y : Matrix (Rest n i) k' ℝ)
    (K : Matrix (n i) k' ℝ) (T : Tensor n) :
    ⟪(mat i).symm (K * Yᵀ), T⟫ = ⟪K, mat i T * Y⟫ := by
  rw [← (mat i).inner_map_map, LinearIsometryEquiv.apply_symm_apply, Frobenius.inner_mul_right,
    Matrix.transpose_transpose]

/-- The linear map `K ↦ Tenᵢ(K Yᵀ)`. -/
noncomputable def tenRight {k' : Type*} [Fintype k'] (i : ι) (Y : Matrix (Rest n i) k' ℝ) :
    Matrix (n i) k' ℝ →L[ℝ] Tensor n :=
  (mat i).symm.toLinearIsometry.toContinuousLinearMap.comp (Frobenius.rightMulCLM Yᵀ)

/-- `tenRight i Y K = Tenᵢ(K Yᵀ)`. -/
lemma tenRight_apply {k' : Type*} [Fintype k'] (i : ι) (Y : Matrix (Rest n i) k' ℝ)
    (K : Matrix (n i) k' ℝ) : tenRight i Y K = (mat i).symm (K * Yᵀ) := rfl

/-- The gradient of `K ↦ ℒ(Tenᵢ(K Yᵀ))` at `K` is `Matᵢ(∇ℒ(Tenᵢ(K Yᵀ))) Y`. -/
theorem hasFDerivAt_loss_ten {k' : Type*} [Fintype k'] {ℒ : Tensor n → ℝ}
    {g : Tensor n → Tensor n} (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (i : ι)
    (Y : Matrix (Rest n i) k' ℝ) (K : Matrix (n i) k' ℝ) :
    HasFDerivAt (fun K' => ℒ ((mat i).symm (K' * Yᵀ)))
      (innerSL ℝ (mat i (g ((mat i).symm (K * Yᵀ))) * Y)) K :=
  hasFDerivAt_comp_clm hℒ (tenRight i Y) (fun T => mat i T * Y) (fun a b => inner_ten i Y a b) K

/-- `C ×ₖ δ ×_{j ≠ k} Uⱼ = Tenₖ(δ Matₖ(C) (⊗_{j ≠ k} Uⱼ)ᵀ)`, which is linear in `δ`. -/
theorem tucker_update_eq (U : ∀ i, Matrix (n i) (r i) ℝ) (C : Tensor r) (k : ι)
    (δ : Matrix (n k) (r k) ℝ) :
    tucker (Function.update U k δ) C = (mat k).symm (δ * (kronRest U k * (mat k C)ᵀ)ᵀ) := by
  apply (mat k).injective
  rw [LinearIsometryEquiv.apply_symm_apply, mat_tucker, Function.update_self, kronRest_update_self,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- `Tenᵢ(Qᵢᵀ) ×_{j ≠ i} Uⱼ ×ᵢ K = Tenᵢ(K Vᵢᵀ)`, the tensorization formula in the proof of Thm 2.1
of arXiv 2305.19059. -/
theorem tucker_update_ten (U : ∀ i, Matrix (n i) (r i) ℝ) (i : ι) (Q : Matrix (Rest r i) (r i) ℝ)
    (K : Matrix (n i) (r i) ℝ) :
    tucker (Function.update U i K) ((mat i).symm Qᵀ) = (mat i).symm (K * (coFrame U i Q)ᵀ) := by
  apply (mat i).injective
  rw [LinearIsometryEquiv.apply_symm_apply, mat_tucker,
    Function.update_self, kronRest_update_self, LinearIsometryEquiv.apply_symm_apply, coFrame,
    Matrix.transpose_mul, Matrix.mul_assoc]

/-! ### Theorem 2.1: the robust equations for `Kᵢ` and `C` -/

section Thm21

variable [∀ i, DecidableEq (r i)]

/-- Equation (3), read at the level of the factors: under the gauge `Uⱼᵀ U̇ⱼ = 0`,
`Uᵢ Matᵢ(Ċ) Qᵢ + U̇ᵢ Sᵢ = -Matᵢ(X) Vᵢ` whenever `Ẇ = -P(W) X`. -/
theorem factor_key {U U' : ∀ i, Matrix (n i) (r i) ℝ} {C C' : Tensor r} {X : Tensor n}
    (horth : ∀ j, (U j)ᵀ * U j = 1) (hgauge : ∀ j, (U j)ᵀ * U' j = 0)
    (hdot : tuckerDot U U' C C' = -tangentProj U C X) {i : ι} {Q : Matrix (Rest r i) (r i) ℝ}
    {S : Matrix (r i) (r i) ℝ} (hQR : IsCoreQR i C Q S) :
    U i * (mat i C' * Q) + U' i * S = -(mat i X * coFrame U i Q) := by
  have h : mat i (tuckerDot U U' C C') * coFrame U i Q =
      (U i * mat i C' + U' i * mat i C) * Q := by
    rw [coFrame, ← Matrix.mul_assoc, mat_tuckerDot_mul horth hgauge]
  rw [hdot, map_neg, Matrix.neg_mul, mat_tangentProj_mul (horth i) hQR] at h
  rw [h, Matrix.add_mul, ← hQR.mat_mul]
  simp only [Matrix.mul_assoc]

/-- The core equation of (4) follows from (3): under the gauge `Uⱼᵀ U̇ⱼ = 0`, `Ẇ = -P(W) X` gives
`Ċ = -X ×ⱼ Uⱼᵀ`. -/
theorem core_eq_of_flow {U U' : ∀ i, Matrix (n i) (r i) ℝ} {C C' : Tensor r} {X : Tensor n}
    (horth : ∀ j, (U j)ᵀ * U j = 1) (hgauge : ∀ j, (U j)ᵀ * U' j = 0)
    (hdot : tuckerDot U U' C C' = -tangentProj U C X) :
    C' = -tucker (fun j => (U j)ᵀ) X := by
  have h := congrArg (tucker fun j => (U j)ᵀ) hdot
  rwa [tucker_tuckerDot horth hgauge, map_neg, tucker_tangentProj] at h

/-- The basis equation of (4) follows from (3), without any pseudo-inverse:
`U̇ᵢ Sᵢ = -(1 - Uᵢ Uᵢᵀ) Matᵢ(X) Vᵢ`.  Since `Matᵢ(C)† = Qᵢ Sᵢ⁻¹`, this is the first line of (4). -/
theorem factor_eq_of_flow [∀ i, DecidableEq (n i)] {U U' : ∀ i, Matrix (n i) (r i) ℝ}
    {C C' : Tensor r} {X : Tensor n}
    (horth : ∀ j, (U j)ᵀ * U j = 1) (hgauge : ∀ j, (U j)ᵀ * U' j = 0)
    (hdot : tuckerDot U U' C C' = -tangentProj U C X) {i : ι} {Q : Matrix (Rest r i) (r i) ℝ}
    {S : Matrix (r i) (r i) ℝ} (hQR : IsCoreQR i C Q S) :
    U' i * S = -((1 - U i * (U i)ᵀ) * (mat i X * coFrame U i Q)) := by
  have h := factor_key horth hgauge hdot hQR
  have h1 : (1 - U i * (U i)ᵀ) * (U i * (mat i C' * Q)) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (U i)ᵀ, horth i,
      Matrix.one_mul, sub_self]
  have h2 : (1 - U i * (U i)ᵀ) * (U' i * S) = U' i * S := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (U i)ᵀ, hgauge i,
      Matrix.zero_mul, Matrix.mul_zero, sub_zero]
  rw [← h2, ← Matrix.mul_neg, ← h, Matrix.mul_add, h1, zero_add]

/-- **The exact evolution of `Kᵢ`** along the projected flow `Ẇ = -P(W) X`, for *any* differentiable
curve `Qᵢ(t)` of QR factors: with `Kᵢ = Uᵢ Sᵢ`, `Sᵢ = Matᵢ(C) Qᵢ`,
`K̇ᵢ = -Matᵢ(X) Vᵢ + Kᵢ Qᵢᵀ Q̇ᵢ`. -/
theorem hasDerivAt_K {U : ℝ → ∀ i, Matrix (n i) (r i) ℝ} {U' : ∀ i, Matrix (n i) (r i) ℝ}
    {C : ℝ → Tensor r} {C' : Tensor r} {t : ℝ} {X : Tensor n}
    (hU : ∀ j, HasDerivAt (fun s => U s j) (U' j) t) (hC : HasDerivAt C C' t)
    (horth : ∀ j, (U t j)ᵀ * U t j = 1) (hgauge : ∀ j, (U t j)ᵀ * U' j = 0)
    (hflow : HasDerivAt (fun s => tucker (U s) (C s)) (-tangentProj (U t) (C t) X) t)
    {i : ι} {Q : ℝ → Matrix (Rest r i) (r i) ℝ} {Q' : Matrix (Rest r i) (r i) ℝ}
    {S : Matrix (r i) (r i) ℝ} (hQ : HasDerivAt Q Q' t) (hQR : IsCoreQR i (C t) (Q t) S) :
    HasDerivAt (fun s => U s i * (mat i (C s) * Q s))
      (-(mat i X * coFrame (U t) i (Q t)) + U t i * S * ((Q t)ᵀ * Q')) t := by
  have hdot : tuckerDot (U t) U' (C t) C' = -tangentProj (U t) (C t) X :=
    (hasDerivAt_tucker hU hC).unique hflow
  have hmat : HasDerivAt (fun s => mat i (C s)) (mat i C') t := by
    have h0 := (mat i).toLinearIsometry.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hC
    exact h0
  have h := Frobenius.hasDerivAt_mul (hU i) (Frobenius.hasDerivAt_mul hmat hQ)
  refine h.congr_deriv ?_
  have h3 : mat i (C t) * Q' = S * ((Q t)ᵀ * Q') := by rw [hQR.mat_eq, Matrix.mul_assoc]
  rw [← factor_key horth hgauge hdot hQR, h3, hQR.mat_mul]
  simp only [Matrix.mul_add, Matrix.mul_assoc]
  abel

/-- The paper's `K`-equation holds **if and only if** `Qᵢᵀ Q̇ᵢ = 0`.  So it needs a gauge for `Qᵢ`
(which the proof of Thm 2.1 obtains by freezing `Vᵢ`), and fails for every curve of QR factors
with `Qᵢᵀ Q̇ᵢ ≠ 0`. -/
theorem K_eq_iff {U : ∀ i, Matrix (n i) (r i) ℝ} {X : Tensor n} (horth : ∀ j, (U j)ᵀ * U j = 1)
    {i : ι} {V : Matrix (Rest n i) (r i) ℝ} {Q Q' : Matrix (Rest r i) (r i) ℝ}
    {S : Matrix (r i) (r i) ℝ} (hS : IsUnit S) :
    -(mat i X * V) + U i * S * (Qᵀ * Q') = -(mat i X * V) ↔ Qᵀ * Q' = 0 := by
  have hS' : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hS
  constructor
  · intro h
    have h0 : U i * S * (Qᵀ * Q') = 0 := by simpa using h
    have h1 := congrArg (fun M => S⁻¹ * ((U i)ᵀ * M)) h0
    simpa only [Matrix.mul_zero, ← Matrix.mul_assoc, horth i, Matrix.one_mul,
      Matrix.nonsing_inv_mul S hS'] using h1
  · intro h
    rw [h, Matrix.mul_zero, add_zero]

/-- With `Vᵢ` frozen, `Qᵢ` is frozen as well: under the gauge `Uⱼᵀ U̇ⱼ = 0`,
`V̇ᵢ = 0` forces `Q̇ᵢ = 0`.  (Differentiate `Vᵢ = (⊗_{j ≠ i} Uⱼ) Qᵢ` and multiply by
`(⊗_{j ≠ i} Uⱼ)ᵀ`.) -/
theorem Q_deriv_eq_zero_of_frozen {U : ℝ → ∀ i, Matrix (n i) (r i) ℝ}
    {U' : ∀ i, Matrix (n i) (r i) ℝ} {t : ℝ} (hU : ∀ j, HasDerivAt (fun s => U s j) (U' j) t)
    (horth : ∀ j, (U t j)ᵀ * U t j = 1) (hgauge : ∀ j, (U t j)ᵀ * U' j = 0) {i : ι}
    {Q : ℝ → Matrix (Rest r i) (r i) ℝ} {Q' : Matrix (Rest r i) (r i) ℝ}
    (hQ : HasDerivAt Q Q' t) (hV : HasDerivAt (fun s => coFrame (U s) i (Q s)) 0 t) : Q' = 0 := by
  have hE := hasDerivAt_kron (A := fun s (j : {j // j ≠ i}) => U s j)
    (A' := fun j => U' j) fun j => hU j
  have h := (Frobenius.hasDerivAt_mul hE hQ).unique hV
  have h0 : (kronRest (U t) i)ᵀ *
      ∑ k, kron (Function.update (fun j : {j // j ≠ i} => U t j) k (U' k)) = 0 := by
    rw [Matrix.mul_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    unfold kronRest
    rw [kron_transpose, kron_mul]
    exact kron_eq_zero (k := k) (by simp [hgauge])
  have h1 := congrArg (fun M => (kronRest (U t) i)ᵀ * M) h
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_zero] at h1
  rw [h0, Matrix.zero_mul, zero_add] at h1
  have h2 : (kronRest (U t) i)ᵀ * kron (fun j : {j // j ≠ i} => U t j) = 1 := kronRest_orth horth i
  rwa [h2, Matrix.one_mul] at h1

/-- **Theorem 2.1 of arXiv 2305.19059** (robust reparametrization), for genuine Tucker tensors.

Let `W(t) = C(t) ×ⱼ Uⱼ(t)` with `Uⱼᵀ Uⱼ = 1`, in the gauge `Uⱼᵀ U̇ⱼ = 0`, satisfy eq. (3)
`Ẇ = -P(W) ∇ℒ(W)` at `t`, where `P(W)` is the orthogonal projector onto the tangent space (1); let
`Matᵢ(C)ᵀ = Qᵢ Sᵢᵀ` with `Qᵢ` orthonormal and `Sᵢ` invertible (`W ∈ ℳ_ρ`), and `Kᵢ = Uᵢ Sᵢ`,
`Vᵢ = (⊗_{j ≠ i} Uⱼ) Qᵢ`.  If `Qᵢᵀ Q̇ᵢ = 0`, then

* `K̇ᵢ = -Matᵢ(∇ℒ(W)) Vᵢ`;
* `Matᵢ(∇ℒ(W)) Vᵢ` is the gradient at `Kᵢ` of `K ↦ ℒ(Tenᵢ(Qᵢᵀ) ×_{j ≠ i} Uⱼ ×ᵢ K)`, so
  `K̇ᵢ = -∇_{Kᵢ} ℒ(Tenᵢ(Qᵢᵀ) ×_{j ≠ i} Uⱼ ×ᵢ Kᵢ)`;
* `Ċ = -∇ℒ(W) ×ⱼ Uⱼᵀ`, which is the gradient at `C` of `D ↦ ℒ(D ×ⱼ Uⱼ)`, so
  `Ċ = -∇_C ℒ(C ×ⱼ Uⱼ)`.

Differences from the paper.  The printed statement has no condition on `Qᵢ`, so this is Thm 2.1
under the extra hypothesis `Qᵢᵀ Q̇ᵢ = 0`: `hasDerivAt_K` gives the extra term `Kᵢ Qᵢᵀ Q̇ᵢ` and
`K_eq_iff` shows that the formula holds exactly when `Qᵢᵀ Q̇ᵢ = 0`.  No flow whose QR factors have
`Qᵢᵀ Q̇ᵢ ≠ 0` is constructed, so the printed statement is not refuted.  The paper's proof assumes
`V̇ᵢ = 0`, which is a special case (`thm_2_1_frozen`); `Qᵢᵀ Q̇ᵢ = 0` is all it needs, and then `Vᵢ`
may move with the `Uⱼ`, so the result holds along the whole flow and not only for a frozen
substep.  The proof in the paper uses
`Ẇ = -∇ℒ(W)` at one point and quotes (4); here (3) is the only assumption, and (4) is derived
(`core_eq_of_flow`, `factor_eq_of_flow`).  The gauge `Uⱼᵀ U̇ⱼ = 0` is implicit in (4). -/
theorem thm_2_1 {ℒ : Tensor n → ℝ} {g : Tensor n → Tensor n}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    {U : ℝ → ∀ i, Matrix (n i) (r i) ℝ} {U' : ∀ i, Matrix (n i) (r i) ℝ}
    {C : ℝ → Tensor r} {C' : Tensor r} {t : ℝ}
    (hU : ∀ j, HasDerivAt (fun s => U s j) (U' j) t) (hC : HasDerivAt C C' t)
    (horth : ∀ j, (U t j)ᵀ * U t j = 1) (hgauge : ∀ j, (U t j)ᵀ * U' j = 0)
    (hflow : HasDerivAt (fun s => tucker (U s) (C s))
      (-tangentProj (U t) (C t) (g (tucker (U t) (C t)))) t)
    {i : ι} {Q : ℝ → Matrix (Rest r i) (r i) ℝ} {Q' : Matrix (Rest r i) (r i) ℝ}
    {S : Matrix (r i) (r i) ℝ} (hQ : HasDerivAt Q Q' t) (hQg : (Q t)ᵀ * Q' = 0)
    (hQR : IsCoreQR i (C t) (Q t) S) :
    HasDerivAt (fun s => U s i * (mat i (C s) * Q s))
      (-(mat i (g (tucker (U t) (C t))) * coFrame (U t) i (Q t))) t ∧
    HasFDerivAt (fun K => ℒ (tucker (Function.update (U t) i K) ((mat i).symm (Q t)ᵀ)))
      (innerSL ℝ (mat i (g (tucker (U t) (C t))) * coFrame (U t) i (Q t))) (U t i * S) ∧
    C' = -tucker (fun j => (U t j)ᵀ) (g (tucker (U t) (C t))) ∧
    HasFDerivAt (fun D => ℒ (tucker (U t) D))
      (innerSL ℝ (tucker (fun j => (U t j)ᵀ) (g (tucker (U t) (C t))))) (C t) := by
  have hdot : tuckerDot (U t) U' (C t) C' = -tangentProj (U t) (C t) (g (tucker (U t) (C t))) :=
    (hasDerivAt_tucker hU hC).unique hflow
  have hsymm : (mat i).symm (U t i * S * (coFrame (U t) i (Q t))ᵀ) = tucker (U t) (C t) := by
    rw [← mat_tucker_eq hQR, LinearIsometryEquiv.symm_apply_apply]
  refine ⟨?_, ?_, core_eq_of_flow horth hgauge hdot, hasFDerivAt_loss_tucker hℒ (U t) (C t)⟩
  · have h := hasDerivAt_K hU hC horth hgauge hflow hQ hQR
    rwa [hQg, Matrix.mul_zero, add_zero] at h
  · have h := hasFDerivAt_loss_ten hℒ i (coFrame (U t) i (Q t)) (U t i * S)
    rw [hsymm] at h
    simpa only [tucker_update_ten] using h

/-- **Theorem 2.1 of arXiv 2305.19059 with `Vᵢ` frozen**, the assumption `V̇ᵢ = 0` made at the start
of the paper's proof.  This is `thm_2_1`: by `Q_deriv_eq_zero_of_frozen`, `V̇ᵢ = 0` forces
`Q̇ᵢ = 0`.  See `thm_2_1` for the differences from the paper. -/
theorem thm_2_1_frozen {ℒ : Tensor n → ℝ} {g : Tensor n → Tensor n}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    {U : ℝ → ∀ i, Matrix (n i) (r i) ℝ} {U' : ∀ i, Matrix (n i) (r i) ℝ}
    {C : ℝ → Tensor r} {C' : Tensor r} {t : ℝ}
    (hU : ∀ j, HasDerivAt (fun s => U s j) (U' j) t) (hC : HasDerivAt C C' t)
    (horth : ∀ j, (U t j)ᵀ * U t j = 1) (hgauge : ∀ j, (U t j)ᵀ * U' j = 0)
    (hflow : HasDerivAt (fun s => tucker (U s) (C s))
      (-tangentProj (U t) (C t) (g (tucker (U t) (C t)))) t)
    {i : ι} {Q : ℝ → Matrix (Rest r i) (r i) ℝ} {Q' : Matrix (Rest r i) (r i) ℝ}
    {S : Matrix (r i) (r i) ℝ} (hQ : HasDerivAt Q Q' t)
    (hV : HasDerivAt (fun s => coFrame (U s) i (Q s)) 0 t) (hQR : IsCoreQR i (C t) (Q t) S) :
    HasDerivAt (fun s => U s i * (mat i (C s) * Q s))
      (-(mat i (g (tucker (U t) (C t))) * coFrame (U t) i (Q t))) t := by
  have hQ0 := Q_deriv_eq_zero_of_frozen hU horth hgauge hQ hV
  exact (thm_2_1 hℒ hU hC horth hgauge hflow hQ (by rw [hQ0, Matrix.mul_zero]) hQR).1

end Thm21

/-! ### The `K`-step on tensors -/

section KStep

/-- The projector `X ↦ Tenᵢ(Matᵢ(X) V Vᵀ)` onto the tensors with mode-`i` co-range in that of `V`:
the operator `Q₀ i` of `Integrators/TuckerBUG.lean`. -/
noncomputable def coProj {k' : Type*} [Fintype k'] (i : ι) (V : Matrix (Rest n i) k' ℝ) :
    Tensor n →L[ℝ] Tensor n :=
  (tenRight i V).comp ((Frobenius.rightMulCLM V).comp
    (mat i).toLinearIsometry.toContinuousLinearMap)

/-- `coProj i V X = Tenᵢ(Matᵢ(X) V Vᵀ)`. -/
lemma coProj_apply {k' : Type*} [Fintype k'] (i : ι) (V : Matrix (Rest n i) k' ℝ) (X : Tensor n) :
    coProj i V X = (mat i).symm (mat i X * V * Vᵀ) := rfl

/-- `coProj i V` is an orthogonal projector if `V` has orthonormal columns. -/
theorem isOrthProj_coProj {k' : Type*} [Fintype k'] [DecidableEq k'] {i : ι}
    {V : Matrix (Rest n i) k' ℝ} (hV : Vᵀ * V = 1) : IsOrthProj (coProj i V) where
  idem x := by
    simp only [coProj_apply, LinearIsometryEquiv.apply_symm_apply]
    congr 1
    rw [Matrix.mul_assoc (mat i x * V), hV, Matrix.mul_one]
  symm x y := by
    have h : ⟪(mat i).symm (mat i x * V * Vᵀ), y⟫ = ⟪mat i x * V * Vᵀ, mat i y⟫ := by
      rw [← (mat i).inner_map_map, LinearIsometryEquiv.apply_symm_apply]
    have h' : ⟪x, (mat i).symm (mat i y * V * Vᵀ)⟫ = ⟪mat i x, mat i y * V * Vᵀ⟫ := by
      rw [← (mat i).inner_map_map, LinearIsometryEquiv.apply_symm_apply]
    have e₁ : ⟪mat i x * V * Vᵀ, mat i y⟫ = ⟪mat i x * V, mat i y * V⟫ := by
      rw [Frobenius.inner_mul_right, Matrix.transpose_transpose]
    have e₂ : ⟪mat i x, mat i y * V * Vᵀ⟫ = ⟪mat i x * V, mat i y * V⟫ := by
      rw [Frobenius.inner_mul_right', Matrix.transpose_transpose]
    rw [coProj_apply, coProj_apply, h, h', e₁, e₂]

/-- **The `K`-step on tensors** (the frozen-`Vᵢ` reading of Thm 2.1 of arXiv 2305.19059): if
`K̇ = -Matᵢ(∇ℒ(Tenᵢ(K Vᵀ))) V` with `V` frozen, which by `hasFDerivAt_loss_ten` is the gradient flow
of `K ↦ ℒ(Tenᵢ(K Vᵀ))`, then `Y = Tenᵢ(K Vᵀ)` solves `Ẏ = -Π ∇ℒ(Y)` with the orthogonal projector
`Π = coProj i V` (`isOrthProj_coProj`).  This is the `K`-step `YK' = Q₀ i F(YK)` of
`Integrators/TuckerBUG.lean`. -/
theorem hasDerivAt_kStep {k' : Type*} [Fintype k'] {g : Tensor n → Tensor n} {i : ι}
    {V : Matrix (Rest n i) k' ℝ} {K : ℝ → Matrix (n i) k' ℝ} {t : ℝ}
    (hK : HasDerivAt K (-(mat i (g ((mat i).symm (K t * Vᵀ))) * V)) t) :
    HasDerivAt (fun s => (mat i).symm (K s * Vᵀ))
      (-coProj i V (g ((mat i).symm (K t * Vᵀ)))) t := by
  have h := (tenRight i V).hasFDerivAt.comp_hasDerivAt t hK
  rw [tenRight_apply, Matrix.neg_mul, map_neg] at h
  exact h

end KStep

/-! ### Isometries and projectors from orthonormal bases -/

private lemma le_of_sq_le_mul {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ a * b) : a ≤ b := by
  by_contra hc
  push Not at hc
  nlinarith

/-- `· ×ⱼ Uⱼ` is an isometry for orthonormal `Uⱼ`. -/
theorem norm_tucker [∀ i, DecidableEq (r i)] {U : ∀ i, Matrix (n i) (r i) ℝ}
    (hU : ∀ j, (U j)ᵀ * U j = 1) (D : Tensor r) : ‖tucker U D‖ = ‖D‖ := by
  have h : ‖tucker U D‖ ^ 2 = ‖D‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_tucker, tucker_tucker,
      show (fun j => (U j)ᵀ * U j) = fun j => 1 from funext hU, tucker_one,
      real_inner_self_eq_norm_sq]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- `· ×ⱼ Uⱼᵀ` is a contraction for orthonormal `Uⱼ`. -/
theorem norm_tucker_transpose_le [∀ i, DecidableEq (r i)] {U : ∀ i, Matrix (n i) (r i) ℝ}
    (hU : ∀ j, (U j)ᵀ * U j = 1) (X : Tensor n) : ‖tucker (fun j => (U j)ᵀ) X‖ ≤ ‖X‖ := by
  set Y := tucker (fun j => (U j)ᵀ) X with hY
  refine le_of_sq_le_mul (norm_nonneg _) ?_
  calc ‖Y‖ ^ 2 = ⟪Y, tucker (fun j => (U j)ᵀ) X⟫ := (real_inner_self_eq_norm_sq Y).symm
    _ = ⟪tucker U Y, X⟫ := (inner_tucker U Y X).symm
    _ ≤ ‖tucker U Y‖ * ‖X‖ := real_inner_le_norm _ _
    _ = ‖Y‖ * ‖X‖ := by rw [norm_tucker hU]

/-- The mode product of orthogonal projector matrices, `X ↦ X ×ⱼ Pⱼ`, is an orthogonal projector. -/
theorem isOrthProj_tucker {P : ∀ i, Matrix (n i) (n i) ℝ}
    (hP : ∀ j, Curvature.IsOrthProjMat (P j)) :
    IsOrthProj (tucker P) where
  idem x := by
    rw [tucker_tucker]
    simp only [(hP _).idem]
  symm x y := by
    rw [inner_tucker]
    simp only [(hP _).symm]

/-! ### Corollary 2.2 -/

section Cor22

/-- The column space of a matrix. -/
def colSpan {a' b' : Type*} [Fintype b'] (A : Matrix a' b' ℝ) : Submodule ℝ (a' → ℝ) :=
  LinearMap.range A.mulVecLin

private lemma colSpan_fromCols_mul_le {a' b₁ b₂ b₃ : Type*} [Fintype b₁] [Fintype b₂] [Fintype b₃]
    (A : Matrix a' b₁ ℝ) (B : Matrix a' b₂ ℝ) (T : Matrix b₂ b₃ ℝ) :
    colSpan (Matrix.fromCols A (B * T)) ≤ colSpan (Matrix.fromCols A B) := by
  rintro _ ⟨v, rfl⟩
  refine ⟨Sum.elim (v ∘ Sum.inl) (T *ᵥ (v ∘ Sum.inr)), ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.fromCols_mulVec_sumElim,
    Matrix.fromCols_mulVec, Matrix.mulVec_mulVec]

private lemma eq_of_innerSL_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {a b : E}
    (h : innerSL ℝ a = innerSL ℝ b) : a = b :=
  ext_inner_right ℝ fun y => by simpa only [innerSL_apply_apply] using DFunLike.congr_fun h y

variable [∀ i, DecidableEq (r i)]

/-- **Corollary 2.2 of arXiv 2305.19059**: if `K̇ᵢ` is the right-hand side of the `Kᵢ` equation (5)
at `Kᵢ = Uᵢ Sᵢ`, that is `K̇ᵢ = -∇_{Kᵢ} ℒ(Tenᵢ(Qᵢᵀ) ×_{j ≠ i} Uⱼ ×ᵢ Kᵢ)`, and
`∇_{Uᵢ} ℒ(W)` is the gradient of `A ↦ ℒ(C ×ᵢ A ×_{j ≠ i} Uⱼ)` at `Uᵢ`, then
`∇_{Uᵢ} ℒ(W) = -K̇ᵢ Sᵢᵀ` and `span [Uᵢ, K̇ᵢ] = span [Uᵢ, ∇_{Uᵢ} ℒ(W)]`.

Both gradients are computed by the chain rule on genuine Tucker tensors; only invertibility of `Sᵢ`
is used (the paper's "full-rankness of `Sᵢ`"; its condition (6) serves to provide it), and
orthonormality of the `Uⱼ` is not needed.  The abstract projector version is
`LeanDLRA.FactorizedDynamics.capture_kStep_iff`. -/
theorem cor_2_2 {ℒ : Tensor n → ℝ} {g : Tensor n → Tensor n}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (U : ∀ i, Matrix (n i) (r i) ℝ) (C : Tensor r)
    {i : ι} {Q : Matrix (Rest r i) (r i) ℝ} {S : Matrix (r i) (r i) ℝ} (hQR : IsCoreQR i C Q S)
    {Kdot GU : Matrix (n i) (r i) ℝ}
    (hK : HasFDerivAt (fun K => ℒ (tucker (Function.update U i K) ((mat i).symm Qᵀ)))
      (innerSL ℝ (-Kdot)) (U i * S))
    (hGU : HasFDerivAt (fun A => ℒ (tucker (Function.update U i A) C)) (innerSL ℝ GU) (U i)) :
    GU = -(Kdot * Sᵀ) ∧
      colSpan (Matrix.fromCols (U i) Kdot) = colSpan (Matrix.fromCols (U i) GU) := by
  have hG1 : -Kdot = mat i (g (tucker U C)) * coFrame U i Q := by
    have h := hasFDerivAt_loss_ten hℒ i (coFrame U i Q) (U i * S)
    rw [← mat_tucker_eq hQR, LinearIsometryEquiv.symm_apply_apply] at h
    simp only [← tucker_update_ten U i Q] at h
    exact eq_of_innerSL_eq (hK.unique h)
  have hG2 : GU = mat i (g (tucker U C)) * (coFrame U i Q * Sᵀ) := by
    have h := hasFDerivAt_loss_ten hℒ i (kronRest U i * (mat i C)ᵀ) (U i)
    simp only [← tucker_update_eq U C i, Function.update_eq_self] at h
    rw [eq_of_innerSL_eq (hGU.unique h), hQR.fact, coFrame, Matrix.mul_assoc (kronRest U i)]
  have hGK : GU = -(Kdot * Sᵀ) := by
    rw [hG2, ← Matrix.mul_assoc, ← hG1, Matrix.neg_mul]
  refine ⟨hGK, ?_⟩
  have hS : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hQR.unit
  have e₁ : GU = Kdot * (-Sᵀ) := by rw [hGK, Matrix.mul_neg]
  have e₂ : Kdot = GU * (-(S⁻¹)ᵀ) := by
    rw [hGK, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul S hS, Matrix.transpose_one, Matrix.mul_one]
  refine le_antisymm ?_ ?_
  · conv_lhs => rw [e₂]
    exact colSpan_fromCols_mul_le _ _ _
  · conv_lhs => rw [e₁]
    exact colSpan_fromCols_mul_le _ _ _

end Cor22

/-! ### The closed form of `P(W)`: equations (3) and (4) are equivalent -/

section Projection

/-- `tuckerDot` is additive in the variations. -/
theorem tuckerDot_add (U δ₁ δ₂ : ∀ i, Matrix (n i) (r i) ℝ) (C D₁ D₂ : Tensor r) :
    tuckerDot U (δ₁ + δ₂) C (D₁ + D₂) = tuckerDot U δ₁ C D₁ + tuckerDot U δ₂ C D₂ := by
  unfold tuckerDot
  simp only [tucker_update_eq, Pi.add_apply, Matrix.add_mul, map_add, Finset.sum_add_distrib]
  abel

/-- `tuckerDot` is homogeneous in the variations. -/
theorem tuckerDot_smul (c : ℝ) (U δ : ∀ i, Matrix (n i) (r i) ℝ) (C D : Tensor r) :
    tuckerDot U (c • δ) C (c • D) = c • tuckerDot U δ C D := by
  unfold tuckerDot
  simp only [tucker_update_eq, Pi.smul_apply, Matrix.smul_mul, map_smul, smul_add, Finset.smul_sum]

/-- The vectors `δC ×ⱼ Uⱼ + ∑ₖ C ×ₖ δUₖ ×_{j ≠ k} Uⱼ` of (1) form a subspace: `tangentSpace` is
exactly this set. -/
theorem mem_tangentSpace_iff {U : ∀ i, Matrix (n i) (r i) ℝ} {C : Tensor r} {X : Tensor n} :
    X ∈ tangentSpace U C ↔ ∃ (δC : Tensor r) (δU : ∀ i, Matrix (n i) (r i) ℝ),
      (∀ j, δU j ∈ stiefelTangent (U j)) ∧ X = tuckerDot U δU C δC := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x h => exact h
  | zero =>
    refine ⟨0, 0, fun j => zero_mem _, ?_⟩
    have := tuckerDot_smul 0 U 0 C 0
    simpa using this.symm
  | add x y _ _ hx hy =>
    obtain ⟨D₁, δ₁, h₁, rfl⟩ := hx
    obtain ⟨D₂, δ₂, h₂, rfl⟩ := hy
    exact ⟨D₁ + D₂, δ₁ + δ₂, fun j => add_mem (h₁ j) (h₂ j), (tuckerDot_add ..).symm⟩
  | smul c x _ hx =>
    obtain ⟨D, δ, h, rfl⟩ := hx
    exact ⟨c • D, c • δ, fun j => Submodule.smul_mem _ c (h j), (tuckerDot_smul ..).symm⟩

variable [∀ i, DecidableEq (n i)] [∀ i, DecidableEq (r i)]

/-- The horizontal basis directions `δUᵢ = (1 - Uᵢ Uᵢᵀ) Matᵢ(X) Vᵢ Sᵢ⁻¹` of `P(W) X`. -/
noncomputable def horizontal (U : ∀ i, Matrix (n i) (r i) ℝ)
    (Q : ∀ i, Matrix (Rest r i) (r i) ℝ) (S : ∀ i, Matrix (r i) (r i) ℝ) (X : Tensor n) :
    ∀ i, Matrix (n i) (r i) ℝ :=
  fun i => (1 - U i * (U i)ᵀ) * (mat i X * coFrame U i (Q i)) * (S i)⁻¹

/-- **Closed form of the tangent projector**: for `W = C ×ⱼ Uⱼ` with orthonormal `Uⱼ` and
invertible `Sⱼ` in every mode (that is, `W ∈ ℳ_ρ`),
`P(W) X = (X ×ⱼ Uⱼᵀ) ×ⱼ Uⱼ + ∑ₖ C ×ₖ δUₖ ×_{j ≠ k} Uⱼ` with `δUₖ = (1 - Uₖ Uₖᵀ) Matₖ(X) Vₖ Sₖ⁻¹`. -/
theorem tangentProj_eq {U : ∀ i, Matrix (n i) (r i) ℝ} {C : Tensor r}
    (horth : ∀ j, (U j)ᵀ * U j = 1) {Q : ∀ i, Matrix (Rest r i) (r i) ℝ}
    {S : ∀ i, Matrix (r i) (r i) ℝ} (hQR : ∀ i, IsCoreQR i C (Q i) (S i)) (X : Tensor n) :
    tangentProj U C X =
      tuckerDot U (horizontal U Q S X) C (tucker (fun j => (U j)ᵀ) X) := by
  set δ := horizontal U Q S X with hδdef
  set Z := tuckerDot U δ C (tucker (fun j => (U j)ᵀ) X) with hZ
  have hδS : ∀ i, δ i * S i = (1 - U i * (U i)ᵀ) * (mat i X * coFrame U i (Q i)) := fun i => by
    have hS : IsUnit (S i).det := (Matrix.isUnit_iff_isUnit_det _).1 (hQR i).unit
    rw [hδdef, horizontal, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hS, Matrix.mul_one]
  have hg : ∀ j, (U j)ᵀ * δ j = 0 := fun j => by
    have : (U j)ᵀ * (1 - U j * (U j)ᵀ) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, horth j, Matrix.one_mul, sub_self]
    rw [hδdef, horizontal, Matrix.mul_assoc (1 - U j * (U j)ᵀ), ← Matrix.mul_assoc (U j)ᵀ, this,
      Matrix.zero_mul]
  have hcore : tucker (fun j => (U j)ᵀ) Z = tucker (fun j => (U j)ᵀ) X :=
    tucker_tuckerDot horth hg C _
  have hmat : ∀ i, mat i Z * coFrame U i (Q i) = mat i X * coFrame U i (Q i) := fun i => by
    have hE : (kronRest (fun j => (U j)ᵀ) i)ᵀ = kronRest U i := by
      unfold kronRest
      rw [kron_transpose]
      simp only [Matrix.transpose_transpose]
    have h1 : mat i (tucker (fun j => (U j)ᵀ) X) = (U i)ᵀ * mat i X * kronRest U i := by
      rw [mat_tucker, hE]
    rw [coFrame, ← Matrix.mul_assoc, mat_tuckerDot_mul horth hg, ← coFrame, Matrix.add_mul,
      Matrix.mul_assoc (δ i), (hQR i).mat_mul, hδS, h1, coFrame, Matrix.sub_mul, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    abel
  have hmem : Z ∈ tangentSpace U C := by
    refine Submodule.subset_span ⟨_, δ, fun j => ?_, rfl⟩
    change (U j)ᵀ * δ j + (δ j)ᵀ * U j = 0
    have : ((U j)ᵀ * δ j)ᵀ = (δ j)ᵀ * U j := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [← this, hg j, Matrix.transpose_zero, add_zero]
  refine Submodule.eq_starProjection_of_mem_orthogonal hmem ?_
  rw [Submodule.mem_orthogonal]
  intro Y hY
  obtain ⟨D, δU, -, rfl⟩ := mem_tangentSpace_iff.1 hY
  unfold tuckerDot
  rw [inner_add_left, sum_inner, inner_tucker, map_sub, hcore, sub_self, inner_zero_right, zero_add]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hY : (kronRest U k * (mat k C)ᵀ) = coFrame U k (Q k) * (S k)ᵀ := by
    rw [(hQR k).fact, coFrame, Matrix.mul_assoc]
  rw [tucker_update_eq, inner_ten, hY, ← Matrix.mul_assoc, map_sub, Matrix.sub_mul, Matrix.sub_mul,
    hmat, sub_self, inner_zero_right]

/-- **(4) implies (3)**: if the factors satisfy the (pseudo-inverse) equations (4), then
`Ẇ = -P(W) X`.  With `core_eq_of_flow` and `factor_eq_of_flow`, the two systems are equivalent. -/
theorem flow_of_factor_eq {U U' : ∀ i, Matrix (n i) (r i) ℝ} {C C' : Tensor r}
    (horth : ∀ j, (U j)ᵀ * U j = 1) {Q : ∀ i, Matrix (Rest r i) (r i) ℝ}
    {S : ∀ i, Matrix (r i) (r i) ℝ} (hQR : ∀ i, IsCoreQR i C (Q i) (S i)) {X : Tensor n}
    (hU' : U' = -horizontal U Q S X) (hC' : C' = -tucker (fun j => (U j)ᵀ) X) :
    tuckerDot U U' C C' = -tangentProj U C X := by
  have h := tuckerDot_smul (-1) U (horizontal U Q S X) C (tucker (fun j => (U j)ᵀ) X)
  simp only [neg_smul, one_smul] at h
  rw [tangentProj_eq horth hQR, hU', hC', h]

/-- **Stationarity of the augmented core controls Riemannian stationarity**: if the orthonormal
augmented bases `Ûⱼ` contain `Uⱼ` and the basis gradients `∇_{Uⱼ} ℒ(W) = Matⱼ(X) Vⱼ Sⱼᵀ`, as in
lines 1–3 of Algorithm 1 of arXiv 2305.19059, then `‖P(W) X‖ ≤ ‖X ×ⱼ Ûⱼᵀ‖`. -/
theorem norm_tangentProj_le {R : ι → Type*} [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)]
    {U : ∀ i, Matrix (n i) (r i) ℝ} {C : Tensor r} (horth : ∀ j, (U j)ᵀ * U j = 1)
    {Q : ∀ i, Matrix (Rest r i) (r i) ℝ} {S : ∀ i, Matrix (r i) (r i) ℝ}
    (hQR : ∀ i, IsCoreQR i C (Q i) (S i)) {Uh : ∀ i, Matrix (n i) (R i) ℝ}
    (hUh : ∀ j, (Uh j)ᵀ * Uh j = 1) (hcap : ∀ j, Uh j * (Uh j)ᵀ * U j = U j) {X : Tensor n}
    (hgrad : ∀ j, Uh j * (Uh j)ᵀ * (mat j X * coFrame U j (Q j) * (S j)ᵀ) =
      mat j X * coFrame U j (Q j) * (S j)ᵀ) :
    ‖tangentProj U C X‖ ≤ ‖tucker (fun j => (Uh j)ᵀ) X‖ := by
  set δ := horizontal U Q S X with hδdef
  have hδ : ∀ k, Uh k * (Uh k)ᵀ * δ k = δ k := fun k => by
    have hS : IsUnit (S k).det := (Matrix.isUnit_iff_isUnit_det _).1 (hQR k).unit
    have hSt : (S k)ᵀ * ((S k)⁻¹)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hS, Matrix.transpose_one]
    set M := mat k X * coFrame U k (Q k) with hM
    have h1 : Uh k * (Uh k)ᵀ * M = M := by
      have := congrArg (fun A => A * ((S k)⁻¹)ᵀ) (hgrad k)
      simpa only [Matrix.mul_assoc, hSt, Matrix.mul_one] using this
    have h2 : Uh k * (Uh k)ᵀ * ((1 - U k * (U k)ᵀ) * M) = (1 - U k * (U k)ᵀ) * M := by
      have h3 : Uh k * (Uh k)ᵀ * (U k * (U k)ᵀ) = U k * (U k)ᵀ := by
        rw [← Matrix.mul_assoc, hcap k]
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, h1, ← Matrix.mul_assoc (Uh k * (Uh k)ᵀ),
        h3]
    rw [hδdef, horizontal, ← hM, ← Matrix.mul_assoc, h2]
  have hPi : tucker (fun j => Uh j * (Uh j)ᵀ) (tangentProj U C X) = tangentProj U C X := by
    rw [tangentProj_eq horth hQR, ← hδdef]
    unfold tuckerDot
    rw [map_add, map_sum, tucker_tucker]
    congr 1
    · simp only [hcap]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [tucker_tucker]
      have e : (fun j => Uh j * (Uh j)ᵀ * Function.update U k (δ k) j) =
          Function.update U k (δ k) := by
        funext j
        by_cases h : j = k
        · subst h
          rw [Function.update_self, hδ]
        · rw [Function.update_of_ne h, hcap]
      rw [e]
  set Y := tangentProj U C X with hY
  have hinner : ⟪Y, Y⟫ = ⟪Y, X⟫ := by
    have hid : (tangentSpace U C).starProjection Y = Y :=
      Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ _)
    have h : ⟪(tangentSpace U C).starProjection Y, X⟫ =
        ⟪Y, (tangentSpace U C).starProjection X⟫ := by
      rw [Submodule.inner_starProjection_left_eq_right]
    rw [hid] at h
    exact h.symm
  refine le_of_sq_le_mul (norm_nonneg _) ?_
  have e : tucker (fun j => Uh j * (Uh j)ᵀ) Y = tucker Uh (tucker (fun j => (Uh j)ᵀ) Y) :=
    (tucker_tucker _ _ _).symm
  calc ‖Y‖ ^ 2 = ⟪tucker Uh (tucker (fun j => (Uh j)ᵀ) Y), X⟫ := by
        rw [← e, hPi, ← hinner, real_inner_self_eq_norm_sq]
    _ = ⟪tucker (fun j => (Uh j)ᵀ) Y, tucker (fun j => (Uh j)ᵀ) X⟫ := inner_tucker _ _ _
    _ ≤ ‖tucker (fun j => (Uh j)ᵀ) Y‖ * ‖tucker (fun j => (Uh j)ᵀ) X‖ := real_inner_le_norm _ _
    _ ≤ ‖Y‖ * ‖tucker (fun j => (Uh j)ᵀ) X‖ :=
        mul_le_mul_of_nonneg_right (norm_tucker_transpose_le hUh Y) (norm_nonneg _)

end Projection

/-! ### Theorem 3.1: descent of one TDLRT step -/

section Thm31

variable {R r' : ι → Type*} [∀ i, Fintype (R i)] [∀ i, Fintype (r' i)] [∀ i, DecidableEq (R i)]

/-- The state after the core flow is `C ×ⱼ Ûⱼ`; along the flow, the loss decreases at rate
`‖∇ℒ ×ⱼ Ûⱼᵀ‖²`. -/
private lemma loss_core_flow_le {ℒ : Tensor n → ℝ} {g : Tensor n → Tensor n}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) {Uh : ∀ j, Matrix (n j) (R j) ℝ}
    {Ch : ℝ → Tensor R} {lam α : ℝ} (hlam : 0 ≤ lam)
    (hCh : ODESolution (fun _ c => -tucker (fun j => (Uh j)ᵀ) (g (tucker Uh c))) Ch 0 lam)
    (hα : ∀ t ∈ Icc 0 lam, α ≤ ‖tucker (fun j => (Uh j)ᵀ) (g (tucker Uh (Ch t)))‖ ^ 2) :
    ℒ (tucker Uh (Ch lam)) ≤ ℒ (tucker Uh (Ch 0)) - α * lam := by
  set y : ℝ → Tensor n := fun t => tucker Uh (Ch t) with hy
  set A : ℝ → Tensor R := fun t => tucker (fun j => (Uh j)ᵀ) (g (y t)) with hA
  have hyc : ContinuousOn y (Icc 0 lam) := (tucker Uh).continuous.comp_continuousOn hCh.cont
  have hc : ContinuousOn (ℒ ∘ y) (Icc 0 lam) :=
    (continuous_of_hasFDerivAt_innerSL hℒ).comp_continuousOn hyc
  have hd : ∀ t ∈ Ico 0 lam, HasDerivWithinAt (ℒ ∘ y) (-‖A t‖ ^ 2) (Ici t) t := fun t ht => by
    have h1 : HasDerivWithinAt y (tucker Uh (-A t)) (Ici t) t :=
      (tucker Uh).hasFDerivAt.comp_hasDerivWithinAt t (hCh.deriv t ht)
    refine (hasDerivWithinAt_energy_comp hℒ h1).congr_deriv ?_
    rw [real_inner_comm, inner_tucker, inner_neg_left, real_inner_self_eq_norm_sq]
  have hB : ∀ t, HasDerivWithinAt (fun s => ℒ (y 0) - α * s) (-α) (Ici t) t := fun t => by
    simpa using ((hasDerivWithinAt_id t (Ici t)).const_mul α).const_sub (ℒ (y 0))
  have h := image_le_of_deriv_right_le_deriv_boundary hc hd
    (B := fun s => ℒ (y 0) - α * s) (by simp)
    (Continuous.continuousOn (by fun_prop)) (fun t _ => hB t)
    fun t ht => neg_le_neg (hα t (Ico_subset_Icc_self ht))
  exact h (right_mem_Icc.2 hlam)

/-- **Theorem 3.1 of arXiv 2305.19059** (descent of one step of Algorithm 1, exact integration).

The previous weight is `W(0) = C₀ ×ⱼ Uⱼ`.  The bases `Ûⱼ` are orthonormal and contain the `Uⱼ`
(lines 2–3); the core starts at `Ĉ(0) = C₀ ×ⱼ Ûⱼᵀ Uⱼ` (line 4) and solves
`Ĉ' = -∇_C ℒ(Ĉ ×ⱼ Ûⱼ) = -∇ℒ(Ĉ ×ⱼ Ûⱼ) ×ⱼ Ûⱼᵀ` exactly on `[0, λ]` (line 5, compare
`hasFDerivAt_loss_tucker`); `C' ×ⱼ U'ⱼ` approximates `Ĉ(λ)` up to `τ` (line 6), and the new weight
is `W(λ) = C' ×ⱼ Ûⱼ U'ⱼ` (line 7).  Then `ℒ(W(λ)) ≤ ℒ(W(0)) - α λ + β τ` for every `α` with
`α ≤ ‖∇ℒ(Ŵ(t)) ×ⱼ Ûⱼᵀ‖²` on `[0, λ]` and every `β` bounding `‖∇ℒ‖` on the segment from `Ŵ(λ)` to
`W(λ)`, in particular for the minimum and maximum used in the paper's proof.

The facts `Ŵ(0) = W(0)` and `‖W(λ) - Ŵ(λ)‖ ≤ τ` are derived.  Differences from the paper: `τ` is an
absolute tolerance, as in the paper's proof (the tolerance of (6) is relative, take
`τ ‖Ĉ(λ)‖`).  The paper asserts `α, β > 0` independent of `λ`, `τ`; these `α`, `β` are not, and
`α > 0` fails at stationary points.  See `thm_3_1_uniform` and `thm_3_1_tangent` for the correct
form of that claim. -/
theorem thm_3_1 {ℒ : Tensor n → ℝ} {g : Tensor n → Tensor n}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) {Uo : ∀ j, Matrix (n j) (r j) ℝ} {Co : Tensor r}
    {Uh : ∀ j, Matrix (n j) (R j) ℝ} (hUh : ∀ j, (Uh j)ᵀ * Uh j = 1)
    (hcap : ∀ j, Uh j * (Uh j)ᵀ * Uo j = Uo j) {Ch : ℝ → Tensor R} {lam : ℝ} (hlam : 0 ≤ lam)
    (h0 : Ch 0 = tucker (fun j => (Uh j)ᵀ * Uo j) Co)
    (hCh : ODESolution (fun _ c => -tucker (fun j => (Uh j)ᵀ) (g (tucker Uh c))) Ch 0 lam)
    {U' : ∀ j, Matrix (R j) (r' j) ℝ} {C' : Tensor r'} {τ : ℝ}
    (hτ : ‖tucker U' C' - Ch lam‖ ≤ τ) {α β : ℝ}
    (hα : ∀ t ∈ Icc 0 lam, α ≤ ‖tucker (fun j => (Uh j)ᵀ) (g (tucker Uh (Ch t)))‖ ^ 2)
    (hβ : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖g (s • tucker (fun j => Uh j * U' j) C' + (1 - s) • tucker Uh (Ch lam))‖ ≤ β) :
    ℒ (tucker (fun j => Uh j * U' j) C') ≤ ℒ (tucker Uo Co) - α * lam + β * τ := by
  have hstart : tucker Uh (Ch 0) = tucker Uo Co := by
    rw [h0, tucker_tucker]
    simp only [← Matrix.mul_assoc, hcap]
  have h1 := loss_core_flow_le hℒ hlam hCh hα
  rw [hstart] at h1
  have hW : tucker (fun j => Uh j * U' j) C' = tucker Uh (tucker U' C') :=
    (tucker_tucker _ _ _).symm
  have hdist : ‖tucker (fun j => Uh j * U' j) C' - tucker Uh (Ch lam)‖ ≤ τ := by
    rw [hW, ← map_sub, norm_tucker hUh]
    exact hτ
  have hβ' : ∀ w ∈ segment ℝ (tucker Uh (Ch lam)) (tucker (fun j => Uh j * U' j) C'),
      ‖g w‖ ≤ β := by
    rintro _ ⟨a, b, ha, hb, hab, rfl⟩
    have h := hβ b ⟨hb, by linarith⟩
    rwa [show 1 - b = a by linarith, add_comm] at h
  have h2 := abs_energy_sub_le hℒ hβ'
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ 0 (by simp))
  have h3 := mul_le_mul_of_nonneg_left hdist hβ0
  have h4 := (abs_le.1 h2).2
  linarith

/-- **Theorem 3.1 of arXiv 2305.19059 with constants independent of `λ` and `τ`.**  Let
`‖∇ℒ‖ ≤ L₁` and `∇ℒ` be `L₂`-Lipschitz on a set `K` containing the trajectory `Ŵ` and the
truncation segment (the paper's "locally bounded and Lipschitz around `W`"), and
`a = ‖∇ℒ(W(0)) ×ⱼ Ûⱼᵀ‖`.  For
`L₁ L₂ λ ≤ a / 2`, one step satisfies `ℒ(W(λ)) ≤ ℒ(W(0)) - (a² / 4) λ + L₁ τ`.  So `α = a² / 4` and
`β = L₁` do not depend on `λ` or `τ`; this is the "small enough learning rate" of the paper's
appendix, which the statement in its Section 3 omits. -/
theorem thm_3_1_uniform {ℒ : Tensor n → ℝ} {g : Tensor n → Tensor n}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) {Uo : ∀ j, Matrix (n j) (r j) ℝ} {Co : Tensor r}
    {Uh : ∀ j, Matrix (n j) (R j) ℝ} (hUh : ∀ j, (Uh j)ᵀ * Uh j = 1)
    (hcap : ∀ j, Uh j * (Uh j)ᵀ * Uo j = Uo j) {Ch : ℝ → Tensor R} {lam : ℝ} (hlam : 0 ≤ lam)
    (h0 : Ch 0 = tucker (fun j => (Uh j)ᵀ * Uo j) Co)
    (hCh : ODESolution (fun _ c => -tucker (fun j => (Uh j)ᵀ) (g (tucker Uh c))) Ch 0 lam)
    {U' : ∀ j, Matrix (R j) (r' j) ℝ} {C' : Tensor r'} {τ : ℝ}
    (hτ : ‖tucker U' C' - Ch lam‖ ≤ τ) {K : Set (Tensor n)} {L₁ L₂ : ℝ} (hL₂ : 0 ≤ L₂)
    (hbd : ∀ x ∈ K, ‖g x‖ ≤ L₁) (hLip : ∀ x ∈ K, ∀ y ∈ K, ‖g x - g y‖ ≤ L₂ * ‖x - y‖)
    (hK : ∀ t ∈ Icc 0 lam, tucker Uh (Ch t) ∈ K)
    (hK' : ∀ s ∈ Icc (0 : ℝ) 1,
      s • tucker (fun j => Uh j * U' j) C' + (1 - s) • tucker Uh (Ch lam) ∈ K)
    (hsmall : L₁ * L₂ * lam ≤ ‖tucker (fun j => (Uh j)ᵀ) (g (tucker Uo Co))‖ / 2) :
    ℒ (tucker (fun j => Uh j * U' j) C') ≤
      ℒ (tucker Uo Co) - ‖tucker (fun j => (Uh j)ᵀ) (g (tucker Uo Co))‖ ^ 2 / 4 * lam + L₁ * τ := by
  set a := ‖tucker (fun j => (Uh j)ᵀ) (g (tucker Uo Co))‖ with ha
  have hstart : tucker Uh (Ch 0) = tucker Uo Co := by
    rw [h0, tucker_tucker]
    simp only [← Matrix.mul_assoc, hcap]
  have hspeed : ∀ t ∈ Ico 0 lam,
      ‖-tucker (fun j => (Uh j)ᵀ) (g (tucker Uh (Ch t)))‖ ≤ L₁ := fun t ht => by
    rw [norm_neg]
    exact (norm_tucker_transpose_le hUh _).trans (hbd _ (hK t (Ico_subset_Icc_self ht)))
  have hmove := hCh.norm_sub_le hspeed
  refine thm_3_1 hℒ hUh hcap hlam h0 hCh hτ (fun t ht => ?_) fun s hs => hbd _ (hK' s hs)
  have ht0 : (0 : ℝ) ∈ Icc 0 lam := left_mem_Icc.2 hlam
  have hL₁ : 0 ≤ L₁ := (norm_nonneg _).trans (hbd _ (hK 0 ht0))
  have hdist : ‖tucker Uh (Ch t) - tucker Uo Co‖ ≤ L₁ * lam := by
    rw [← hstart, ← map_sub, norm_tucker hUh]
    calc ‖Ch t - Ch 0‖ ≤ L₁ * (t - 0) := hmove t ht
      _ ≤ L₁ * lam := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hL₁
  have hgrad : ‖g (tucker Uh (Ch t)) - g (tucker Uo Co)‖ ≤ a / 2 := by
    have := hLip _ (hK t ht) _ (hstart ▸ hK 0 ht0)
    calc _ ≤ L₂ * ‖tucker Uh (Ch t) - tucker Uo Co‖ := this
      _ ≤ L₂ * (L₁ * lam) := mul_le_mul_of_nonneg_left hdist hL₂
      _ = L₁ * L₂ * lam := by ring
      _ ≤ a / 2 := hsmall
  have hdiff : ‖tucker (fun j => (Uh j)ᵀ) (g (tucker Uh (Ch t))) -
      tucker (fun j => (Uh j)ᵀ) (g (tucker Uo Co))‖ ≤ a / 2 := by
    rw [← map_sub]
    exact (norm_tucker_transpose_le hUh _).trans hgrad
  have hlow : a / 2 ≤ ‖tucker (fun j => (Uh j)ᵀ) (g (tucker Uh (Ch t)))‖ := by
    have := norm_sub_norm_le (tucker (fun j => (Uh j)ᵀ) (g (tucker Uo Co)))
      (tucker (fun j => (Uh j)ᵀ) (g (tucker Uh (Ch t))))
    rw [norm_sub_rev] at this
    linarith
  have ha0 : 0 ≤ a := norm_nonneg _
  nlinarith

/-- **Theorem 3.1 of arXiv 2305.19059 for Algorithm 1, with its Riemannian descent rate.**  If
`W(0)` lies on the Tucker manifold (invertible `Sⱼ` in every mode, orthonormal `Uⱼ`) and the bases
`Ûⱼ` contain `Uⱼ` and `∇_{Uⱼ} ℒ(W(0))` as in lines 1–3, then with `p = ‖P(W(0)) ∇ℒ(W(0))‖`, for
`L₁ L₂ λ ≤ p / 2`: `ℒ(W(λ)) ≤ ℒ(W(0)) - (p² / 4) λ + L₁ τ`.  Thus the paper's `α > 0` holds exactly
away from stationary points of `ℒ` on `ℳ_ρ`, with `α` depending neither on `λ` nor on `τ` nor on
the augmented bases. -/
theorem thm_3_1_tangent [∀ i, DecidableEq (n i)] [∀ i, DecidableEq (r i)]
    {ℒ : Tensor n → ℝ} {g : Tensor n → Tensor n}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) {Uo : ∀ j, Matrix (n j) (r j) ℝ} {Co : Tensor r}
    (hUo : ∀ j, (Uo j)ᵀ * Uo j = 1) {Q : ∀ i, Matrix (Rest r i) (r i) ℝ}
    {S : ∀ i, Matrix (r i) (r i) ℝ} (hQR : ∀ i, IsCoreQR i Co (Q i) (S i))
    {Uh : ∀ j, Matrix (n j) (R j) ℝ} (hUh : ∀ j, (Uh j)ᵀ * Uh j = 1)
    (hcap : ∀ j, Uh j * (Uh j)ᵀ * Uo j = Uo j)
    (hgrad : ∀ j, Uh j * (Uh j)ᵀ * (mat j (g (tucker Uo Co)) * coFrame Uo j (Q j) * (S j)ᵀ) =
      mat j (g (tucker Uo Co)) * coFrame Uo j (Q j) * (S j)ᵀ)
    {Ch : ℝ → Tensor R} {lam : ℝ} (hlam : 0 ≤ lam)
    (h0 : Ch 0 = tucker (fun j => (Uh j)ᵀ * Uo j) Co)
    (hCh : ODESolution (fun _ c => -tucker (fun j => (Uh j)ᵀ) (g (tucker Uh c))) Ch 0 lam)
    {U' : ∀ j, Matrix (R j) (r' j) ℝ} {C' : Tensor r'} {τ : ℝ}
    (hτ : ‖tucker U' C' - Ch lam‖ ≤ τ) {K : Set (Tensor n)} {L₁ L₂ : ℝ} (hL₂ : 0 ≤ L₂)
    (hbd : ∀ x ∈ K, ‖g x‖ ≤ L₁) (hLip : ∀ x ∈ K, ∀ y ∈ K, ‖g x - g y‖ ≤ L₂ * ‖x - y‖)
    (hK : ∀ t ∈ Icc 0 lam, tucker Uh (Ch t) ∈ K)
    (hK' : ∀ s ∈ Icc (0 : ℝ) 1,
      s • tucker (fun j => Uh j * U' j) C' + (1 - s) • tucker Uh (Ch lam) ∈ K)
    (hsmall : L₁ * L₂ * lam ≤ ‖tangentProj Uo Co (g (tucker Uo Co))‖ / 2) :
    ℒ (tucker (fun j => Uh j * U' j) C') ≤
      ℒ (tucker Uo Co) - ‖tangentProj Uo Co (g (tucker Uo Co))‖ ^ 2 / 4 * lam + L₁ * τ := by
  have hle := norm_tangentProj_le hUo hQR hUh hcap hgrad
  have h := thm_3_1_uniform hℒ hUh hcap hlam h0 hCh hτ hL₂ hbd hLip hK hK'
    (hsmall.trans (by linarith))
  have hsq : ‖tangentProj Uo Co (g (tucker Uo Co))‖ ^ 2 ≤
      ‖tucker (fun j => (Uh j)ᵀ) (g (tucker Uo Co))‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  have := mul_le_mul_of_nonneg_right hsq hlam
  linarith

end Thm31

/-! ### Lemma G.2 and the deterministic Robbins–Monro argument -/

section Sequences

/-- **Lemma G.2 of arXiv 2305.19059** (descent lemma for a one-sided Lipschitz gradient):
`ℒ x ≤ ℒ y + ⟪∇ℒ(y), x - y⟫ + L₂/2 ‖x - y‖²` when
`⟪∇ℒ(x) - ∇ℒ(y), x - y⟫ ≤ L₂ ‖x - y‖²`.  This extends `LeanDLRA.descent_lemma`, which assumes a
Lipschitz gradient.  The paper's proof integrates, which needs a continuous gradient; here `∇ℒ` is
only assumed to exist everywhere. -/
theorem lemma_G_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ℒ : E → ℝ}
    {g : E → E} {K : ℝ} (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : IsOneSidedLipschitzField (fun _ => g) K) (x y : E) :
    ℒ x ≤ ℒ y + ⟪g y, x - y⟫ + K / 2 * ‖x - y‖ ^ 2 := by
  set d := x - y with hd
  have hB : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ℒ y + s * ⟪g y, d⟫ + K / 2 * s ^ 2 * ‖d‖ ^ 2)
      (⟪g y, d⟫ + K * t * ‖d‖ ^ 2) t := by
    intro t
    have h := (((hasDerivAt_id' t).mul_const ⟪g y, d⟫).const_add (ℒ y)).add
      (((hasDerivAt_pow 2 t).const_mul (K / 2)).mul_const (‖d‖ ^ 2))
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1, ⟪g (y + s • d), d⟫ ≤ ⟪g y, d⟫ + K * s * ‖d‖ ^ 2 := by
    intro s hs
    rcases hs.1.eq_or_lt with rfl | h0
    · simp
    · have h1 := hg 0 (y + s • d) y
      simp only [add_sub_cancel_left, inner_smul_right, norm_smul, Real.norm_of_nonneg h0.le] at h1
      have h2 : ⟪g (y + s • d) - g y, d⟫ ≤ K * s * ‖d‖ ^ 2 := by
        refine le_of_mul_le_mul_left ?_ h0
        calc s * ⟪g (y + s • d) - g y, d⟫ ≤ K * (s * ‖d‖) ^ 2 := h1
          _ = s * (K * s * ‖d‖ ^ 2) := by ring
      rw [inner_sub_left] at h2
      linarith
  have key := image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := 1)
    (f := fun s : ℝ => ℒ (y + s • d)) (f' := fun s => ⟪g (y + s • d), d⟫)
    (fun s _ => (hasDerivAt_loss_line hℒ y d s).continuousAt.continuousWithinAt)
    (fun s _ => (hasDerivAt_loss_line hℒ y d s).hasDerivWithinAt)
    (B := fun s => ℒ y + s * ⟪g y, d⟫ + K / 2 * s ^ 2 * ‖d‖ ^ 2)
    (B' := fun s => ⟪g y, d⟫ + K * s * ‖d‖ ^ 2) (by simp)
    (fun s _ => (hB s).continuousAt.continuousWithinAt)
    (fun s _ => (hB s).hasDerivWithinAt) hbound (right_mem_Icc.2 zero_le_one)
  have key' : ℒ (y + (1 : ℝ) • d) ≤ ℒ y + 1 * ⟪g y, d⟫ + K / 2 * 1 ^ 2 * ‖d‖ ^ 2 := key
  have hyd : y + (1 : ℝ) • d = x := by rw [one_smul, hd, add_sub_cancel]
  rw [hyd] at key'
  linarith

/-- The summation argument at the end of the proof of Thm 3.2 of arXiv 2305.19059.  The learning
rates tend to zero, so `1 - K v λ_t / 2 ≥ 1 / 2` eventually: the paper needs `K v λ_t ≤ 1` here and
assumes `K v λ_t ≤ 2`, under which its inequality has the wrong direction. -/
private theorem rm_core {u A e lam : ℕ → ℝ} {K m v C ℓ : ℝ} (hK : 0 ≤ K) (hm : 0 ≤ m)
    (hC : 0 ≤ C) (hA : ∀ t, 0 ≤ A t) (he : ∀ t, 0 ≤ e t) (hlam : ∀ t, 0 < lam t)
    (hlow : ∀ t, ℓ ≤ u t) (hdiv : ¬ Summable lam) (hsq : Summable fun t => lam t ^ 2)
    (hes : Summable e)
    (hstep : ∀ t, u (t + 1) ≤ u t - lam t * A t + K / 2 * lam t ^ 2 * (m + v * A t) + C * e t)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) : ∃ t, N ≤ t ∧ A t < ε := by
  have hlam0 : Tendsto lam atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hsq.tendsto_atTop_zero
    have e1 : (Real.sqrt ∘ fun t => lam t ^ 2) = lam :=
      funext fun t => Real.sqrt_sq (hlam t).le
    rwa [e1, Real.sqrt_zero] at h
  have hev : ∀ᶠ t in atTop, K * v * lam t < 1 := by
    have h := hlam0.const_mul (K * v)
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds one_pos)
  obtain ⟨T, hT⟩ := eventually_atTop.1 hev
  have hsq' : Summable fun k => lam (k + T) ^ 2 := (summable_nat_add_iff T).2 hsq
  have hes' : Summable fun k => e (k + T) := (summable_nat_add_iff T).2 hes
  set w : ℕ → ℝ := fun k => lam (k + T) / 2 with hw
  set a : ℕ → ℝ := fun k => A (k + T) with ha
  have hone : ∀ k, w k * a k ≤ u (k + T) - u (k + 1 + T) +
      (K / 2 * m * lam (k + T) ^ 2 + C * e (k + T)) := fun k => by
    have h1 := hstep (k + T)
    have h2 : K * v * lam (k + T) * (lam (k + T) * A (k + T)) ≤ lam (k + T) * A (k + T) :=
      mul_le_of_le_one_left (mul_nonneg (hlam _).le (hA _)) (hT _ (Nat.le_add_left _ _)).le
    rw [show k + T + 1 = k + 1 + T by ring] at h1
    simp only [hw, ha]
    nlinarith
  have hsum : ∀ n, ∑ k ∈ Finset.range n, w k * a k ≤
      u T - ℓ + (K / 2 * m * ∑' k, lam (k + T) ^ 2 + C * ∑' k, e (k + T)) := fun n => by
    have h1 : ∑ k ∈ Finset.range n, (u (k + T) - u (k + 1 + T)) = u T - u (n + T) := by
      have := Finset.sum_range_sub' (fun k => u (k + T)) n
      simpa using this
    have h2 : ∑ k ∈ Finset.range n, lam (k + T) ^ 2 ≤ ∑' k, lam (k + T) ^ 2 :=
      hsq'.sum_le_tsum _ fun k _ => sq_nonneg _
    have h3 : ∑ k ∈ Finset.range n, e (k + T) ≤ ∑' k, e (k + T) :=
      hes'.sum_le_tsum _ fun k _ => he _
    have h4 := Finset.sum_le_sum fun k (_ : k ∈ Finset.range n) => hone k
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, ← Finset.mul_sum, ← Finset.mul_sum]
      at h4
    have h5 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ K / 2 * m)
    have h6 := mul_le_mul_of_nonneg_left h3 hC
    linarith [hlow (n + T)]
  have hwdiv : ¬ Summable w := fun hs => hdiv <| (summable_nat_add_iff T).1 <| by
    have := hs.mul_left 2
    simpa [hw, mul_div_cancel₀] using this
  obtain ⟨k, hk, hlt⟩ := exists_lt_of_sum_mul_le (fun k => (div_pos (hlam _) two_pos).le)
    (fun k => hA _) hwdiv hsum hε N
  exact ⟨k + T, hk.trans (Nat.le_add_right _ _), hlt⟩

private lemma liminf_eq_zero {a : ℕ → ℝ} (h0 : ∀ t, 0 ≤ a t)
    (h : ∀ ε > 0, ∀ N, ∃ t, N ≤ t ∧ a t < ε) : liminf a atTop = 0 := by
  have hfreq : ∀ ε > 0, ∃ᶠ t in atTop, a t ≤ ε := fun ε hε => frequently_atTop.2 fun N => by
    obtain ⟨t, ht, hlt⟩ := h ε hε N
    exact ⟨t, ht, hlt.le⟩
  have hbb : IsBoundedUnder (· ≥ ·) atTop a := isBoundedUnder_of ⟨0, h0⟩
  have hcb : IsCoboundedUnder (· ≥ ·) atTop a :=
    IsCoboundedUnder.of_frequently_le (hfreq 1 one_pos)
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
    (le_liminf_of_le hcb (Eventually.of_forall h0))
  simpa using liminf_le_of_frequently_le (hfreq ε hε) hbb

end Sequences

/-! ### Theorem 3.2: convergence of the stochastic scheme -/

section Thm32

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The real inner product as a continuous bilinear map. -/
private noncomputable def innerB (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ (innerₗ E) 1 fun x y => by
    simpa using norm_inner_le_norm (𝕜 := ℝ) x y

/-- Tower property for `⟪Y, Z⟫` with `Y` measurable for `m`. -/
private lemma integral_inner_eq_of_condExp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [IsFiniteMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {Y Z Zb : Ω → E} (hY : StronglyMeasurable[m] Y) (hZ : Integrable Z μ)
    (hYZ : Integrable (fun ω => ⟪Y ω, Z ω⟫) μ) (hc : μ[Z | m] =ᵐ[μ] Zb) :
    ∫ ω, ⟪Y ω, Z ω⟫ ∂μ = ∫ ω, ⟪Y ω, Zb ω⟫ ∂μ := by
  have h := condExp_bilin_of_stronglyMeasurable_left (innerB E) hY hYZ hZ
  rw [← integral_condExp hm]
  refine integral_congr_ae (h.trans ?_)
  filter_upwards [hc] with ω hω
  simp only [hω]
  rfl

/-- **Lemma G.3 of arXiv 2305.19059, in its valid form.**  If the projector `P` is known before the
batch is drawn (`Y = P g` measurable for `m`) and `E[B | m] = g`, then
`E ⟪g, B ×ⱼ Pⱼ⟫ = E ‖g ×ⱼ Pⱼ‖² ≥ 0`.  For a batch-dependent projector, the case the paper's proof
of Thm 3.2 needs, the inequality fails: `lemma_G_3_counterexample`. -/
theorem lemma_G_3 [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {P : Ω → ∀ j, Matrix (n j) (n j) ℝ} (hP : ∀ ω j, Curvature.IsOrthProjMat (P ω j))
    {B g : Ω → Tensor n} (hY : StronglyMeasurable[m] fun ω => tucker (P ω) (g ω))
    (hB : Integrable B μ) (hc : μ[B | m] =ᵐ[μ] g)
    (hI : Integrable (fun ω => ⟪g ω, tucker (P ω) (B ω)⟫) μ) :
    ∫ ω, ⟪g ω, tucker (P ω) (B ω)⟫ ∂μ = ∫ ω, ‖tucker (P ω) (g ω)‖ ^ 2 ∂μ := by
  have e : ∀ ω, ⟪g ω, tucker (P ω) (B ω)⟫ = ⟪tucker (P ω) (g ω), B ω⟫ := fun ω =>
    ((isOrthProj_tucker (hP ω)).symm _ _).symm
  simp only [e] at hI ⊢
  rw [integral_inner_eq_of_condExp hm hY hB hI hc]
  exact integral_congr_ae (ae_of_all _ fun ω => (isOrthProj_tucker (hP ω)).inner_self_apply _)

/-- **Theorem 3.2 of arXiv 2305.19059, general form**, with the mixed-term estimate that the paper
derives from its Lemma G.3 as the hypothesis `hinner`, and with the drift in expectation.  See
`thm_3_2` for the statement with conditional expectations. -/
theorem thm_3_2_of_inner_bound [IsProbabilityMeasure μ] {ℒ : Tensor n → ℝ} {g : Tensor n → Tensor n}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) {K : ℝ} (hK : 0 ≤ K)
    (hg : IsOneSidedLipschitzField (fun _ => g) K) {ℓ : ℝ} (hℓ : ∀ x, ℓ ≤ ℒ x)
    {W Wt B : ℕ → Ω → Tensor n} {Pr Pa : ℕ → Ω → ∀ j, Matrix (n j) (n j) ℝ} {lam : ℕ → ℝ}
    (hcap : ∀ t ω j, Pa t ω j * Pr t ω j = Pr t ω j)
    (hW : ∀ t ω, tucker (Pr t ω) (W t ω) = W t ω)
    (hstep : ∀ t ω, Wt (t + 1) ω = tucker (Pa t ω) (W t ω - lam t • B t ω))
    {C : ℝ} (hC : ∀ t ω, ∀ w ∈ segment ℝ (Wt (t + 1) ω) (W (t + 1) ω), ‖g w‖ ≤ C)
    (hlam : ∀ t, 0 < lam t) (hdiv : ¬ Summable lam) (hsq : Summable fun t => lam t ^ 2)
    (htr : Summable fun t => ∫ ω, ‖W (t + 1) ω - Wt (t + 1) ω‖ ∂μ)
    {m v : ℝ} (hm : 0 ≤ m)
    (hdrift : ∀ t, ∫ ω, ‖tucker (Pa t ω) (B t ω)‖ ^ 2 ∂μ ≤
      m + v * ∫ ω, ‖tucker (Pr t ω) (g (W t ω))‖ ^ 2 ∂μ)
    (hinner : ∀ t, ∫ ω, ‖tucker (Pr t ω) (g (W t ω))‖ ^ 2 ∂μ ≤
      ∫ ω, ⟪g (W t ω), tucker (Pa t ω) (B t ω)⟫ ∂μ)
    (hIℓ : ∀ t, Integrable (fun ω => ℒ (W t ω)) μ)
    (hIb : ∀ t, Integrable (fun ω => ⟪g (W t ω), tucker (Pa t ω) (B t ω)⟫) μ)
    (hIc : ∀ t, Integrable (fun ω => ‖tucker (Pa t ω) (B t ω)‖ ^ 2) μ)
    (hIe : ∀ t, Integrable (fun ω => ‖W (t + 1) ω - Wt (t + 1) ω‖) μ) :
    liminf (fun t => ∫ ω, ‖tucker (Pr t ω) (g (W t ω))‖ ^ 2 ∂μ) atTop = 0 := by
  obtain ⟨ω₀⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ω₀ _ (left_mem_segment ℝ _ _))
  have hpoint : ∀ t ω, ℒ (W (t + 1) ω) ≤ ℒ (W t ω) - lam t * ⟪g (W t ω), tucker (Pa t ω) (B t ω)⟫ +
      K / 2 * lam t ^ 2 * ‖tucker (Pa t ω) (B t ω)‖ ^ 2 + C * ‖W (t + 1) ω - Wt (t + 1) ω‖ := by
    intro t ω
    have hfix : tucker (Pa t ω) (W t ω) = W t ω := by
      conv_lhs => rw [← hW t ω]
      rw [tucker_tucker]
      simp only [hcap]
      exact hW t ω
    have hd : Wt (t + 1) ω - W t ω = -(lam t • tucker (Pa t ω) (B t ω)) := by
      rw [hstep, map_sub, hfix, map_smul]
      abel
    have h1 := lemma_G_2 hℒ hg (Wt (t + 1) ω) (W t ω)
    rw [hd, norm_neg, norm_smul, Real.norm_of_nonneg (hlam t).le, inner_neg_right,
      inner_smul_right] at h1
    have h2 := (abs_le.1 (abs_energy_sub_le hℒ (hC t ω))).2
    have h3 := mul_le_mul_of_nonneg_left
      (le_refl ‖W (t + 1) ω - Wt (t + 1) ω‖) hC0
    nlinarith
  set u : ℕ → ℝ := fun t => ∫ ω, ℒ (W t ω) ∂μ with hu
  set A : ℕ → ℝ := fun t => ∫ ω, ‖tucker (Pr t ω) (g (W t ω))‖ ^ 2 ∂μ with hA
  set e : ℕ → ℝ := fun t => ∫ ω, ‖W (t + 1) ω - Wt (t + 1) ω‖ ∂μ with he
  have hA0 : ∀ t, 0 ≤ A t := fun t => integral_nonneg fun ω => sq_nonneg _
  have he0 : ∀ t, 0 ≤ e t := fun t => integral_nonneg fun ω => norm_nonneg _
  have hlow : ∀ t, ℓ ≤ u t := fun t => by
    have h := integral_mono (integrable_const ℓ) (hIℓ t) fun ω => hℓ (W t ω)
    simpa using h
  have hdescent : ∀ t, u (t + 1) ≤ u t - lam t * A t +
      K / 2 * lam t ^ 2 * (m + v * A t) + C * e t := fun t => by
    have hi₁ : Integrable
        (fun ω => ℒ (W t ω) - lam t * ⟪g (W t ω), tucker (Pa t ω) (B t ω)⟫) μ :=
      (hIℓ t).sub ((hIb t).const_mul _)
    have hi₂ : Integrable (fun ω => ℒ (W t ω) - lam t * ⟪g (W t ω), tucker (Pa t ω) (B t ω)⟫ +
        K / 2 * lam t ^ 2 * ‖tucker (Pa t ω) (B t ω)‖ ^ 2) μ :=
      hi₁.add ((hIc t).const_mul _)
    have hi₃ : Integrable (fun ω => ℒ (W t ω) - lam t * ⟪g (W t ω), tucker (Pa t ω) (B t ω)⟫ +
        K / 2 * lam t ^ 2 * ‖tucker (Pa t ω) (B t ω)‖ ^ 2 +
        C * ‖W (t + 1) ω - Wt (t + 1) ω‖) μ :=
      hi₂.add ((hIe t).const_mul _)
    have h := integral_mono (hIℓ (t + 1)) hi₃ (hpoint t)
    rw [integral_add hi₂ ((hIe t).const_mul _), integral_add hi₁ ((hIc t).const_mul _),
      integral_sub (hIℓ t) ((hIb t).const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul] at h
    have h1 := mul_le_mul_of_nonneg_left (hinner t) (hlam t).le
    have h2 := mul_le_mul_of_nonneg_left (hdrift t)
      (by positivity : 0 ≤ K / 2 * lam t ^ 2)
    simp only [hu, hA, he]
    linarith
  exact liminf_eq_zero hA0 fun ε hε N =>
    rm_core hK hm hC0 hA0 he0 hlam hlow hdiv hsq htr hdescent hε N

/-- **Theorem 3.2 of arXiv 2305.19059** (convergence in expectation), on a probability space.

Notation: `W t` is `W(t)`, `Wt (t + 1)` is the weight `W̃(t + 1)` before truncation, `B t` is the
batch gradient `∇ℒ_B(W(t))`, `Pr t ω j` is `P_{Uⱼ(t)}` and `Pa t ω j` is `P_{Ũⱼ(t + 1)}`.  These are
projector matrices, so that ranks may depend on `t` and `ω`.  Assume `Ũⱼ(t + 1) ⊇ Uⱼ(t)`, that
`W(t)` has Tucker form in the `Uⱼ(t)`, the update
`W̃(t + 1) = (W(t) - λ_t ∇ℒ_B(W(t))) ×ⱼ P_{Ũⱼ(t + 1)}`, the Robbins–Monro conditions,
`∑ₜ E ‖W̃(t) - W(t)‖ < ∞` (15), the drift bound (16), and a bound `‖∇ℒ‖ ≤ C` on the truncation
segments.  Then `liminf_t E ‖∇ℒ(W(t)) ×ⱼ P_{Uⱼ(t)}‖² = 0`.

Differences from the paper.

* **Fresh batch**: we assume a σ-algebra `G t` for which `∇ℒ(W(t)) ×ⱼ P_{Ũⱼ(t + 1)}` is measurable
  and `E[∇ℒ_B(W(t)) | G t] = ∇ℒ(W(t))`: the batch of the core step is drawn after the augmented
  bases are fixed.  The paper instead invokes its Lemma G.3 for bases computed from the same batch,
  and `lemma_G_3_counterexample` shows that this step is false.  Whether the printed statement
  survives without this assumption is not settled here; `thm_3_2_of_inner_bound` records what the
  argument needs.
* The drift (16) is stated for the batch gradient: the proof uses this form and the text calls it
  the "projected stochastic gradient", while the display prints `∇ℒ`.
* The paper assumes `λ_t ≤ 2 / (L₂ ν)` and then bounds `-λ_t (1 - λ_t L₂ ν / 2)` by `-λ_t`, which
  is the wrong direction.  No restriction is needed, because `λ_t → 0`; see `rm_core`.
* `∇ℒ` is only one-sided Lipschitz (Lemma G.2) and `ℒ` is bounded below, which is weaker than the
  paper's assumptions.  The conditioning `F t` is any sub-σ-algebra, for instance the one generated
  by `W(t)` and the `Uⱼ(t)`.  All expectations occurring in the proof are assumed finite. -/
theorem thm_3_2 [IsProbabilityMeasure μ] {ℒ : Tensor n → ℝ} {g : Tensor n → Tensor n}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) {K : ℝ} (hK : 0 ≤ K)
    (hg : IsOneSidedLipschitzField (fun _ => g) K) {ℓ : ℝ} (hℓ : ∀ x, ℓ ≤ ℒ x)
    {W Wt B : ℕ → Ω → Tensor n} {Pr Pa : ℕ → Ω → ∀ j, Matrix (n j) (n j) ℝ} {lam : ℕ → ℝ}
    (hPr : ∀ t ω j, Curvature.IsOrthProjMat (Pr t ω j))
    (hPa : ∀ t ω j, Curvature.IsOrthProjMat (Pa t ω j))
    (hcap : ∀ t ω j, Pa t ω j * Pr t ω j = Pr t ω j)
    (hW : ∀ t ω, tucker (Pr t ω) (W t ω) = W t ω)
    (hstep : ∀ t ω, Wt (t + 1) ω = tucker (Pa t ω) (W t ω - lam t • B t ω))
    {C : ℝ} (hC : ∀ t ω, ∀ w ∈ segment ℝ (Wt (t + 1) ω) (W (t + 1) ω), ‖g w‖ ≤ C)
    (hlam : ∀ t, 0 < lam t) (hdiv : ¬ Summable lam) (hsq : Summable fun t => lam t ^ 2)
    (htr : Summable fun t => ∫ ω, ‖W (t + 1) ω - Wt (t + 1) ω‖ ∂μ)
    {m v : ℝ} (hm : 0 ≤ m) {F G : ℕ → MeasurableSpace Ω} (hF : ∀ t, F t ≤ mΩ)
    (hG : ∀ t, G t ≤ mΩ)
    (hdrift : ∀ t, μ[fun ω => ‖tucker (Pa t ω) (B t ω)‖ ^ 2 | F t] ≤ᵐ[μ]
      fun ω => m + v * ‖tucker (Pr t ω) (g (W t ω))‖ ^ 2)
    (hmeas : ∀ t, StronglyMeasurable[G t] fun ω => tucker (Pa t ω) (g (W t ω)))
    (hunb : ∀ t, μ[B t | G t] =ᵐ[μ] fun ω => g (W t ω))
    (hIB : ∀ t, Integrable (B t) μ)
    (hIℓ : ∀ t, Integrable (fun ω => ℒ (W t ω)) μ)
    (hIa : ∀ t, Integrable (fun ω => ‖tucker (Pr t ω) (g (W t ω))‖ ^ 2) μ)
    (hIa' : ∀ t, Integrable (fun ω => ‖tucker (Pa t ω) (g (W t ω))‖ ^ 2) μ)
    (hIb : ∀ t, Integrable (fun ω => ⟪g (W t ω), tucker (Pa t ω) (B t ω)⟫) μ)
    (hIc : ∀ t, Integrable (fun ω => ‖tucker (Pa t ω) (B t ω)‖ ^ 2) μ)
    (hIe : ∀ t, Integrable (fun ω => ‖W (t + 1) ω - Wt (t + 1) ω‖) μ) :
    liminf (fun t => ∫ ω, ‖tucker (Pr t ω) (g (W t ω))‖ ^ 2 ∂μ) atTop = 0 := by
  have hdrift' : ∀ t, ∫ ω, ‖tucker (Pa t ω) (B t ω)‖ ^ 2 ∂μ ≤
      m + v * ∫ ω, ‖tucker (Pr t ω) (g (W t ω))‖ ^ 2 ∂μ := fun t => by
    have h := integral_mono_ae integrable_condExp
      ((integrable_const m).add ((hIa t).const_mul v)) (hdrift t)
    have e : ∫ ω, (μ[fun ω => ‖tucker (Pa t ω) (B t ω)‖ ^ 2 | F t]) ω ∂μ =
        ∫ ω, ‖tucker (Pa t ω) (B t ω)‖ ^ 2 ∂μ := integral_condExp (hF t)
    have e' : ∫ ω, (m + v * ‖tucker (Pr t ω) (g (W t ω))‖ ^ 2) ∂μ =
        m + v * ∫ ω, ‖tucker (Pr t ω) (g (W t ω))‖ ^ 2 ∂μ := by
      rw [integral_add (integrable_const m) ((hIa t).const_mul v), integral_const_mul]
      simp
    calc _ = _ := e.symm
      _ ≤ _ := h
      _ = _ := e'
  have hinner : ∀ t, ∫ ω, ‖tucker (Pr t ω) (g (W t ω))‖ ^ 2 ∂μ ≤
      ∫ ω, ⟪g (W t ω), tucker (Pa t ω) (B t ω)⟫ ∂μ := fun t => by
    rw [lemma_G_3 (hG t) (hPa t) (hmeas t) (hIB t) (hunb t) (hIb t)]
    refine integral_mono (hIa t) (hIa' t) fun ω => ?_
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    have h : ∀ j, Pr t ω j * Pa t ω j = Pr t ω j := fun j => by
      have := congrArg Matrix.transpose (hcap t ω j)
      simpa only [Matrix.transpose_mul, (hPr t ω j).symm, (hPa t ω j).symm] using this
    have e : tucker (Pr t ω) (g (W t ω)) =
        tucker (Pr t ω) (tucker (Pa t ω) (g (W t ω))) := by
      rw [tucker_tucker]
      simp only [h]
    rw [e]
    exact (isOrthProj_tucker (hPr t ω)).norm_le _
  exact thm_3_2_of_inner_bound hℒ hK hg hℓ hcap hW hstep hC hlam hdiv hsq htr hm hdrift' hinner
    hIℓ hIb hIc hIe

end Thm32

/-! ### Lemma G.3 fails for batch-dependent bases -/

section Counterexample

/-- The direction `e₁` or `e₂` that batch `B` contributes in mode `0`. -/
noncomputable def cexDir (B : Bool) : Fin 3 → ℝ := if B then ![0, 1, 0] else ![0, 0, 1]

/-- The second mode-`0` profile of the batch gradient of batch `B`. -/
noncomputable def cexSide (B : Bool) : Fin 3 → ℝ := if B then ![0, -1, 3] else ![0, 3, -1]

/-- The diagonal of the core `C = diag(1, 1, 0)` in modes `1`, `2`, and of `P_{U₁} = P_{U₂}`. -/
noncomputable def cexDiag : Fin 3 → ℝ := ![1, 1, 0]

/-- The diagonal of a matrix orthogonal to the core. -/
noncomputable def cexAnti : Fin 3 → ℝ := ![1, -1, 0]

/-- The batch gradient `∇ℒ_B = a_B ⊗ diag(1, 1, 0) + b_B ⊗ diag(1, -1, 0)` for `3 × 3 × 3`
tensors. -/
noncomputable def cexGrad (B : Bool) : Tensor (fun _ : Fin 3 => Fin 3) :=
  WithLp.toLp 2 fun x =>
    if x 1 = x 2 then cexDir B (x 0) * cexDiag (x 1) + cexSide B (x 0) * cexAnti (x 1) else 0

/-- The full gradient `∇ℒ`, the mean of the two batch gradients. -/
noncomputable def cexMean : Tensor (fun _ : Fin 3 => Fin 3) :=
  (1 / 2 : ℝ) • (cexGrad true + cexGrad false)

/-- The diagonals of the mode projectors `P_{U_{0,1}} = cexDir B`, `P_{U₁} = P_{U₂} = cexDiag`. -/
noncomputable def cexWeight (B : Bool) (i : Fin 3) : Fin 3 → ℝ :=
  if i = 0 then cexDir B else cexDiag

/-- The multilinear product with diagonal matrices is a pointwise weight. -/
theorem tucker_diagonal {n : ι → Type*} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (d : ∀ i, n i → ℝ) (X : Tensor n) (a : ∀ i, n i) :
    tucker (fun i => Matrix.diagonal (d i)) X a = (∏ i, d i (a i)) * X a := by
  rw [tucker_apply, Finset.sum_eq_single a]
  · simp [Matrix.diagonal_apply_eq]
  · intro b _ hb
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hb
    rw [kron_apply, Finset.prod_eq_zero (Finset.mem_univ j), zero_mul]
    exact Matrix.diagonal_apply_ne _ (Ne.symm hj)
  · simp

private lemma inner_eq_sum {n : ι → Type*} [∀ i, Fintype (n i)] (X Y : Tensor n) :
    ⟪X, Y⟫ = ∑ a, X a * Y a := by
  simp [PiLp.inner_apply, mul_comm]

private lemma sum_three (f : (Fin 3 → Fin 3) → ℝ) :
    ∑ x, f x = ∑ a, ∑ b, ∑ d, f ![a, b, d] := by
  let e : Fin 3 × Fin 3 × Fin 3 ≃ (Fin 3 → Fin 3) :=
    { toFun := fun p => ![p.1, p.2.1, p.2.2]
      invFun := fun x => (x 0, x 1, x 2)
      left_inv := fun _ => rfl
      right_inv := fun x => by
        funext i
        fin_cases i <;> rfl }
  rw [← e.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  rfl

/-- **Lemma G.3 of arXiv 2305.19059 is false for batch-dependent bases**, the only case in which the
paper's proof of Thm 3.2 needs more than the trivial identity `lemma_G_3`.

Tucker data of a `3 × 3 × 3` tensor: `U₀ = e₀`, `U₁ = U₂ = [e₀, e₁]`, core `C = diag(1, 1)` of size
`1 × 2 × 2`.  There are two equally likely batches with gradients `cexGrad B`.  By the first part,
the basis gradient `∇_{U₀} ℒ_B = Mat₀(∇ℒ_B) (U₁ ⊗ U₂) Mat₀(C)ᵀ` of batch `B` is `2 cexDir B`, which
is orthogonal to `U₀`.  So Algorithm 1 augments mode `0` by `U_{0,1} = cexDir B` (and the modes `1`,
`2` not at all), which depends on the batch.  By the second part, for the mean gradient `∇ℒ`,
`E ⟪∇ℒ, ∇ℒ_B ×_{j ≠ 0} P_{U_j} ×₀ P_{U_{0,1}}⟫ < 0`.  For matrices with invertible core, `Q` is
square and the mixed term is linear in the batch gradient, so such an example needs order `3`.

The error in the printed proof: it bounds `E[φ(U_{0,1})]` from below by `inf_Û E[φ(Û)]`, whereas
only `E[inf_Û φ(Û)] ≤ E[φ(U_{0,1})]` is available, and `E[inf] ≤ inf E`. -/
theorem lemma_G_3_counterexample :
    (∀ (B : Bool) (a : Fin 3),
      ∑ b, ∑ d, cexGrad B ![a, b, d] * (if b = d then cexDiag b else 0) = 2 * cexDir B a) ∧
    1 / 2 * ⟪cexMean, tucker (fun i => Matrix.diagonal (cexWeight true i)) (cexGrad true)⟫ +
      1 / 2 * ⟪cexMean, tucker (fun i => Matrix.diagonal (cexWeight false i)) (cexGrad false)⟫ <
        0 := by
  constructor
  · intro B a
    cases B <;> fin_cases a <;>
      simp [cexGrad, cexDir, cexSide, cexDiag, cexAnti, Fin.sum_univ_three] <;> norm_num
  · have key : ∀ B,
        ⟪cexMean, tucker (fun i => Matrix.diagonal (cexWeight B i)) (cexGrad B)⟫ = -1 := by
      intro B
      rw [inner_eq_sum]
      simp only [tucker_diagonal]
      rw [sum_three]
      cases B <;>
        simp [cexMean, cexGrad, cexDir, cexSide, cexDiag, cexAnti, cexWeight, Fin.sum_univ_three,
          Fin.prod_univ_three] <;> norm_num
    rw [key, key]
    norm_num

end Counterexample

/-! ### The hypotheses can hold -/

section Instances

/-- The core of a rank-one tensor: `r i = Unit` for all `i`. -/
noncomputable def unitCore : Tensor (fun _ : ι => Unit) := WithLp.toLp 2 fun _ => 1

/-- The factor `Q` of the rank-one core. -/
def unitQ (i : ι) : Matrix (Rest (fun _ : ι => Unit) i) Unit ℝ := Matrix.of fun _ _ => 1

/-- The rank-one core has a QR decomposition, with `S = 1`. -/
theorem isCoreQR_unitCore (i : ι) : IsCoreQR i (unitCore (ι := ι)) (unitQ i) 1 where
  orth := by
    ext a b
    simp [Matrix.mul_apply, unitQ]
  fact := by
    ext a b
    simp [unitCore, unitQ]
  unit := isUnit_one

/-- `∇(‖X‖² / 2) = X`. -/
theorem hasFDerivAt_half_norm_sq (x : Tensor n) :
    HasFDerivAt (fun y : Tensor n => ‖y‖ ^ 2 / 2) (innerSL ℝ x) x := by
  have h := ((hasFDerivAt_id x).norm_sq).const_mul (1 / 2 : ℝ)
  have e : (fun y : Tensor n => ‖y‖ ^ 2 / 2) = fun y => (1 / 2 : ℝ) * ‖id y‖ ^ 2 := by
    funext y
    simp only [id]
    ring
  rw [e]
  convert h using 1
  ext y
  simp only [innerSL_apply_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, id, nsmul_eq_mul]
  push_cast
  ring

/-- The hypotheses of `thm_2_1` hold on a genuine flow.  For `ℒ(X) = ‖X‖² / 2`, any orthonormal `Uⱼ`
and any `C₀` with `Matᵢ(C₀)ᵀ = Q Sᵀ`, the curve `W(s) = e⁻ˢ C₀ ×ⱼ Uⱼ` with constant bases satisfies
eq. (3) with `∇ℒ(W) = W ≠ 0` in general, and `e⁻ᵗ S` is the QR factor at `t`.  Such data exist for
every order: `isCoreQR_unitCore`, with `Uⱼ` any unit vectors. -/
theorem thm_2_1_hypotheses [∀ i, DecidableEq (r i)] {U : ∀ i, Matrix (n i) (r i) ℝ} {C₀ : Tensor r}
    {i : ι} {Q : Matrix (Rest r i) (r i) ℝ} {S : Matrix (r i) (r i) ℝ} (hQR : IsCoreQR i C₀ Q S)
    (t : ℝ) :
    (∀ x : Tensor n, HasFDerivAt (fun y : Tensor n => ‖y‖ ^ 2 / 2) (innerSL ℝ x) x) ∧
    HasDerivAt (fun s => tucker U (Real.exp (-s) • C₀))
      (-tangentProj U (Real.exp (-t) • C₀) (tucker U (Real.exp (-t) • C₀))) t ∧
    IsCoreQR i (Real.exp (-t) • C₀) Q (Real.exp (-t) • S) := by
  refine ⟨fun x => ?_, ?_, ?_⟩
  · exact hasFDerivAt_half_norm_sq x
  · have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_neg t).exp
    have h := (tucker U).hasFDerivAt.comp_hasDerivAt t (hexp.smul_const C₀)
    have hP : tangentProj U (Real.exp (-t) • C₀) (tucker U (Real.exp (-t) • C₀)) =
        tucker U (Real.exp (-t) • C₀) :=
      Submodule.starProjection_eq_self_iff.2 (tucker_mem_tangentSpace U _ _)
    rw [hP, map_smul, ← neg_smul]
    rw [map_smul] at h
    exact h
  · have hE : Real.exp (-t) ≠ 0 := (Real.exp_pos _).ne'
    refine ⟨hQR.orth, ?_, ?_⟩
    · rw [map_smul, Matrix.transpose_smul, hQR.fact, Matrix.transpose_smul, Matrix.mul_smul]
    · exact IsUnit.smul (Units.mk0 _ hE) hQR.unit

/-- The exact integration assumed in `thm_3_1` is available: for a bounded Lipschitz gradient, the
core flow of line 5 of Algorithm 1 has a solution on `[0, λ]` from every starting value. -/
theorem exists_core_flow {R : ι → Type*} [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)]
    {g : Tensor n → Tensor n} {L₁ L₂ : ℝ} (hbd : ∀ x, ‖g x‖ ≤ L₁)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ L₂ * ‖x - y‖) {Uh : ∀ j, Matrix (n j) (R j) ℝ}
    (hUh : ∀ j, (Uh j)ᵀ * Uh j = 1) {lam : ℝ} (hlam : 0 ≤ lam) (c₀ : Tensor R) :
    ∃ Ch : ℝ → Tensor R,
      ODESolution (fun _ c => -tucker (fun j => (Uh j)ᵀ) (g (tucker Uh c))) Ch 0 lam ∧
        Ch 0 = c₀ := by
  set T : Tensor n →L[ℝ] Tensor R := tucker fun j => (Uh j)ᵀ with hT
  have hL : IsLipschitzField (fun (_ : ℝ) (c : Tensor R) => -T (g (tucker Uh c))) L₂ := fun _ x y =>
    calc ‖-T (g (tucker Uh x)) - -T (g (tucker Uh y))‖
        = ‖T (g (tucker Uh x) - g (tucker Uh y))‖ := by
          rw [map_sub, neg_sub_neg, norm_sub_rev]
      _ ≤ ‖g (tucker Uh x) - g (tucker Uh y)‖ := norm_tucker_transpose_le hUh _
      _ ≤ L₂ * ‖tucker Uh x - tucker Uh y‖ := hLip _ _
      _ = L₂ * ‖x - y‖ := by rw [← map_sub, norm_tucker hUh]
  have hB : IsBoundedField (fun (_ : ℝ) (c : Tensor R) => -T (g (tucker Uh c))) L₁ := fun _ x => by
    rw [norm_neg]
    exact (norm_tucker_transpose_le hUh _).trans (hbd _)
  exact exists_ODESolution hL hB (fun _ => continuous_const) hlam c₀

/-- The hypotheses of `thm_3_2` hold on a genuine run: exact gradient descent for
`ℒ(X) = ‖X‖² / 2` with `λ_t = 1 / (t + 1)`, full bases and no truncation, seen as a process on a
one-point probability space. -/
theorem thm_3_2_instance [∀ i, DecidableEq (n i)] (W₀ : Tensor n) :
    let lam : ℕ → ℝ := fun t => 1 / ((t : ℝ) + 1)
    let W : ℕ → Unit → Tensor n := fun t _ => (∏ k ∈ Finset.range t, (1 - lam k)) • W₀
    liminf (fun t => ∫ ω, ‖tucker (fun j => (1 : Matrix (n j) (n j) ℝ)) (W t ω)‖ ^ 2
      ∂(Measure.dirac ())) atTop = 0 := by
  intro lam W
  have hlam : ∀ t, 0 < lam t := fun t => by positivity
  have hlam1 : ∀ t, lam t ≤ 1 := fun t => by
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    simp only [lam]
    rw [div_le_one (by positivity)]
    linarith
  have hsucc : ∀ t ω, W (t + 1) ω = W t ω - lam t • W t ω := fun t ω => by
    simp only [W]
    rw [Finset.prod_range_succ, mul_comm, mul_smul, sub_smul, one_smul]
  have hbd : ∀ t ω, ‖W t ω‖ ≤ ‖W₀‖ := fun t ω => by
    simp only [W]
    have h0 : 0 ≤ ∏ k ∈ Finset.range t, (1 - lam k) :=
      Finset.prod_nonneg fun k _ => by linarith [hlam1 k]
    have h1 : ∏ k ∈ Finset.range t, (1 - lam k) ≤ 1 :=
      Finset.prod_le_one₀ (fun k _ => by linarith [hlam1 k]) fun k _ => by linarith [hlam k]
    rw [norm_smul, Real.norm_of_nonneg h0]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  have hone : ∀ x : Tensor n, tucker (fun j => (1 : Matrix (n j) (n j) ℝ)) x = x := tucker_one
  have hdiv : ¬ Summable lam := fun h => Real.not_summable_one_div_natCast <|
    (summable_nat_add_iff 1).1 <| h.congr fun t => by simp [lam]
  have hsq : Summable fun t => lam t ^ 2 :=
    ((summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)).congr fun t => by
      simp [lam]
  refine thm_3_2 (ℒ := fun y => ‖y‖ ^ 2 / 2) (g := id) (K := 1) (ℓ := 0) (m := 0) (v := 1)
    (Wt := W) (B := W) (lam := lam) (Pr := fun _ _ _ => 1) (Pa := fun _ _ _ => 1)
    (F := fun _ => inferInstance) (G := fun _ => inferInstance) (C := ‖W₀‖)
    hasFDerivAt_half_norm_sq zero_le_one ?_ (fun _ => by positivity)
    (fun _ _ _ => ⟨Matrix.transpose_one, Matrix.one_mul 1⟩)
    (fun _ _ _ => ⟨Matrix.transpose_one, Matrix.one_mul 1⟩)
    (fun _ _ _ => Matrix.one_mul _) (fun _ _ => hone _)
    (fun t ω => by rw [hone]; exact hsucc t ω) ?_ hlam hdiv hsq ?_ le_rfl (fun _ => le_rfl)
    (fun _ => le_rfl) ?_ (fun _ => StronglyMeasurable.of_discrete) ?_
    (fun _ => .of_finite) (fun _ => .of_finite) (fun _ => .of_finite) (fun _ => .of_finite)
    (fun _ => .of_finite) (fun _ => .of_finite) (fun _ => .of_finite)
  · intro _ x y
    simp only [id, one_mul]
    exact (real_inner_self_eq_norm_sq _).le
  · intro t ω w hw
    rw [segment_same, Set.mem_singleton_iff] at hw
    rw [hw]
    exact hbd (t + 1) ω
  · have e : (fun t => ∫ ω, ‖W (t + 1) ω - W (t + 1) ω‖ ∂(Measure.dirac ())) = fun _ => 0 := by
      funext t
      simp
    rw [e]
    exact summable_zero
  · intro t
    rw [condExp_of_stronglyMeasurable le_rfl .of_discrete .of_finite]
    refine Eventually.of_forall fun ω => ?_
    simp only [hone, id, zero_add, one_mul]
    exact le_rfl
  · intro t
    rw [condExp_of_stronglyMeasurable le_rfl .of_discrete .of_finite]
    rfl

end Instances

end Tensor

end LeanDLRA.Literature.P2305_19059
