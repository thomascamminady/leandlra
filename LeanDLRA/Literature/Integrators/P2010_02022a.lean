import LeanDLRA.Integrators.BUG
import LeanDLRA.LinearAlgebra.Factorization.Defs
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2010.02022: Tucker exactness of the unconventional robust BUG integrator

This module is about Theorem 6 of Ceruti–Lubich, on actual tensors `ℝ^{n₁ × ⋯ × n_d}`: it defines
the multilinear product, the matricizations `Matᵢ`/`Tenᵢ`, the Kronecker products, one step of the
Tucker BUG integrator of §5.1 with genuine QR factorizations and ODE substeps (`IsTuckerStep`), and
multilinear rank as the tuple of ranks of the matricizations.  **Theorem 6 is false as printed**
(`Counterexample.theorem6_false`): it assumes that `Uᵢ(t₁)ᵀ Uᵢ(t₀)` is invertible, but its proof
applies Lemma 1 to `Matᵢ(A(t)) = Uᵢ(t) Sᵢ(t) Vᵢ(t)ᵀ`, which needs `Vᵢ(t₁)ᵀ Vᵢ(t₀)` invertible, and
for `d ≥ 3` this does not follow (`modeV_overlap`).  On `A(t) = u ⊗ ((1 - t) I + t J)`, of
multilinear rank `(1, 2, 2)` with constant `Uᵢ`, one gets `K₀(1) = 0`; the QR factor of the zero
column is an arbitrary unit vector and the step can return `0 ≠ A(1)`.  The corrected statement is
proved: `IsTuckerStep.exact_of_overlap` assumes the invertibility of `Vᵢ(t₁)ᵀ Vᵢ(t₀)`, and
`IsTuckerStep.exact_of_hypotheses` keeps the printed hypotheses and adds that every `Kᵢ(t₁)` has
full rank; moreover `IsTuckerStep.eq_proj` gives `Y₁ = A(t₁) X U¹ᵢ U¹ᵢᵀ` and
`IsTuckerStep.exact_iff` characterizes exactness without any assumption.  The abstract Galerkin
core of the theorem, with mode projectors in place of tensors, is
`LeanDLRA.Exactness.tucker_exact_abstract`; it is not proved again here.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2010_02022

open Matrix (IsQR)

variable {d : ℕ} {m n p r : Fin d → ℕ}

/-- The space `ℝ^{n₁ × ⋯ × n_d}` of tensors of order `d`, with the product topology.  (Only the
topology matters for the exactness results; it is the topology of the Euclidean norm of the
paper.) -/
abbrev Tensor (n : Fin d → ℕ) : Type := (∀ i, Fin (n i)) → ℝ

/-- A family of mode matrices `Uᵢ ∈ ℝ^{mᵢ × nᵢ}`. -/
abbrev ModeMatrices (m n : Fin d → ℕ) : Type := ∀ i, Matrix (Fin (m i)) (Fin (n i)) ℝ

/-- Multi-indices on all modes except `i`: the column index of the mode-`i` matricization. -/
abbrev OffMode (n : Fin d → ℕ) (i : Fin d) : Type := ∀ j : {j // j ≠ i}, Fin (n j)

/-- The multilinear product `C X_{i=1}^d Uᵢ` of a core `C ∈ ℝ^{n₁ × ⋯ × n_d}` with matrices
`Uᵢ ∈ ℝ^{mᵢ × nᵢ}`. -/
noncomputable def tuckerMul (U : ModeMatrices m n) (C : Tensor n) : Tensor m :=
  fun x => ∑ y, C y * ∏ i, U i (x i) (y i)

/-- The mode-`i` matricization `Matᵢ(A) ∈ ℝ^{nᵢ × n_¬ᵢ}`.  Its columns are indexed by the
multi-indices on the other modes (no ordering of these is needed). -/
def Mat (i : Fin d) (A : Tensor n) : Matrix (Fin (n i)) (OffMode n i) ℝ :=
  Matrix.of fun a b => A ((Equiv.piSplitAt i fun j => Fin (n j)).symm (a, b))

/-- The tensorization `Tenᵢ`, the inverse of `Matᵢ`. -/
def Ten (i : Fin d) (M : Matrix (Fin (n i)) (OffMode n i) ℝ) : Tensor n :=
  fun x => M (x i) fun j => x j

/-- The Kronecker product `⊗_{j ≠ i} Uⱼ`. -/
noncomputable def kron (U : ModeMatrices m n) (i : Fin d) : Matrix (OffMode m i) (OffMode n i) ℝ :=
  Matrix.of fun x y => ∏ j : {j // j ≠ i}, U j (x j) (y j)

private lemma split_symm_self (i : Fin d) (a : Fin (n i)) (b : OffMode n i) :
    (Equiv.piSplitAt i fun j => Fin (n j)).symm (a, b) i = a :=
  congrArg Prod.fst ((Equiv.piSplitAt i fun j => Fin (n j)).apply_symm_apply (a, b))

private lemma split_symm_ne (i : Fin d) (a : Fin (n i)) (b : OffMode n i) (j : {j // j ≠ i}) :
    (Equiv.piSplitAt i fun j => Fin (n j)).symm (a, b) j = b j :=
  congrFun (congrArg Prod.snd ((Equiv.piSplitAt i fun j => Fin (n j)).apply_symm_apply (a, b))) j

@[simp] lemma Mat_apply (i : Fin d) (A : Tensor n) (a : Fin (n i)) (b : OffMode n i) :
    Mat i A a b = A ((Equiv.piSplitAt i fun j => Fin (n j)).symm (a, b)) := rfl

@[simp] lemma Mat_Ten (i : Fin d) (M : Matrix (Fin (n i)) (OffMode n i) ℝ) :
    Mat i (Ten i M) = M := by
  ext a b
  have h := (Equiv.piSplitAt i fun j => Fin (n j)).apply_symm_apply (a, b)
  simp only [Mat_apply, Ten]
  exact congrArg (fun q : Fin (n i) × OffMode n i => M q.1 q.2) h

@[simp] lemma Ten_Mat (i : Fin d) (A : Tensor n) : Ten i (Mat i A) = A := by
  funext x
  have h := (Equiv.piSplitAt i fun j => Fin (n j)).symm_apply_apply x
  simp only [Ten, Mat_apply]
  exact congrArg A h

lemma Mat_injective (i : Fin d) : Function.Injective (Mat i : Tensor n → _) :=
  Function.LeftInverse.injective (Ten_Mat i)

lemma Mat_add (i : Fin d) (A B : Tensor n) : Mat i (A + B) = Mat i A + Mat i B := rfl

lemma Mat_sub (i : Fin d) (A B : Tensor n) : Mat i (A - B) = Mat i A - Mat i B := rfl

lemma Mat_smul (i : Fin d) (c : ℝ) (A : Tensor n) : Mat i (c • A) = c • Mat i A := rfl

lemma tuckerMul_add (U : ModeMatrices m n) (A B : Tensor n) :
    tuckerMul U (A + B) = tuckerMul U A + tuckerMul U B := by
  funext x
  simp [tuckerMul, add_mul, Finset.sum_add_distrib]

lemma tuckerMul_smul (U : ModeMatrices m n) (c : ℝ) (A : Tensor n) :
    tuckerMul U (c • A) = c • tuckerMul U A := by
  funext x
  simp [tuckerMul, Finset.mul_sum, mul_assoc]

lemma tuckerMul_sub (U : ModeMatrices m n) (A B : Tensor n) :
    tuckerMul U (A - B) = tuckerMul U A - tuckerMul U B := by
  funext x
  simp [tuckerMul, sub_mul, Finset.sum_sub_distrib]

/-- `(C X Wᵢ) X Uᵢ = C X (Uᵢ Wᵢ)` (arXiv 2010.02022, §5, used in the proof of Theorem 6). -/
theorem tuckerMul_tuckerMul (U : ModeMatrices m n) (W : ModeMatrices n p) (C : Tensor p) :
    tuckerMul U (tuckerMul W C) = tuckerMul (fun i => U i * W i) C := by
  funext x
  simp only [tuckerMul, Matrix.mul_apply, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

/-- `C X I = C` (arXiv 2010.02022, §5). -/
@[simp] theorem tuckerMul_one (C : Tensor n) :
    tuckerMul (fun i => (1 : Matrix (Fin (n i)) (Fin (n i)) ℝ)) C = C := by
  funext x
  simp only [tuckerMul]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Ne.symm hi]), mul_zero]
  · simp

/-- `(⊗ⱼ Uⱼ)ᵀ (⊗ⱼ Wⱼ) = ⊗ⱼ (Uⱼᵀ Wⱼ)`, for the Kronecker products of arXiv 2010.02022, §5.1. -/
theorem kron_transpose_mul (U : ModeMatrices m n) (W : ModeMatrices m p) (i : Fin d) :
    (kron U i)ᵀ * kron W i = kron (fun j => (U j)ᵀ * W j) i := by
  ext y z
  simp only [Matrix.mul_apply, kron, Matrix.transpose_apply, Matrix.of_apply,
    ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- `⊗ⱼ I = I`, for the Kronecker products of arXiv 2010.02022, §5.1. -/
theorem kron_one (i : Fin d) :
    kron (fun j => (1 : Matrix (Fin (n j)) (Fin (n j)) ℝ)) i = 1 := by
  ext x y
  by_cases h : x = y
  · subst h; simp [kron]
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    rw [Matrix.one_apply_ne h]
    simp only [kron, Matrix.of_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

/-- The Kronecker product of matrices with orthonormal columns has orthonormal columns
(arXiv 2010.02022, §5.1: this is why `Vᵢ⁰` has orthonormal columns). -/
theorem kron_orth {U : ModeMatrices m n} (hU : ∀ i, (U i)ᵀ * U i = 1) (i : Fin d) :
    (kron U i)ᵀ * kron U i = 1 := by
  rw [kron_transpose_mul]
  simp only [hU, kron_one]

/-- **Matricization of a Tucker tensor** (arXiv 2010.02022, §5):
`Matᵢ(C X Uⱼ) = Uᵢ Matᵢ(C) (⊗_{j ≠ i} Uⱼ)ᵀ`. -/
theorem Mat_tuckerMul (U : ModeMatrices m n) (C : Tensor n) (i : Fin d) :
    Mat i (tuckerMul U C) = U i * Mat i C * (kron U i)ᵀ := by
  ext a b
  let e := (Equiv.piSplitAt i fun j => Fin (n j)).symm
  let x := (Equiv.piSplitAt i fun j => Fin (m j)).symm (a, b)
  have h : ∀ a' b', ∏ j, U j (x j) (e (a', b') j)
      = U i a a' * ∏ j : {j // j ≠ i}, U j (b j) (b' j) := fun a' b' => by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    simp only [x, e, split_symm_self, split_symm_ne]
  calc Mat i (tuckerMul U C) a b
      = ∑ y, C y * ∏ j, U j (x j) (y j) := rfl
    _ = ∑ q, C (e q) * ∏ j, U j (x j) (e q j) := (e.sum_comp _).symm
    _ = ∑ a', ∑ b', C (e (a', b')) * ∏ j, U j (x j) (e (a', b') j) :=
        Fintype.sum_prod_type _
    _ = ∑ b', ∑ a', C (e (a', b')) * ∏ j, U j (x j) (e (a', b') j) := Finset.sum_comm
    _ = (U i * Mat i C * (kron U i)ᵀ) a b := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply, kron, Matrix.of_apply, Mat_apply,
          Finset.sum_mul, h]
        refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun a' _ => ?_
        simp only [e]
        ring

/-- Mode-wise invariance (arXiv 2010.02022, proof of Theorem 6, the tensorization step): if
`P Matᵢ(A) = Matᵢ(A)`, then `A ×ᵢ P = A`. -/
theorem tuckerMul_update_eq (i : Fin d) (P : Matrix (Fin (n i)) (Fin (n i)) ℝ) (A : Tensor n)
    (h : P * Mat i A = Mat i A) :
    tuckerMul (Function.update (fun j => (1 : Matrix (Fin (n j)) (Fin (n j)) ℝ)) i P) A = A := by
  refine Mat_injective i ?_
  have hk : kron (Function.update (fun j => (1 : Matrix (Fin (n j)) (Fin (n j)) ℝ)) i P) i = 1 := by
    rw [← kron_one i]
    ext x y
    simp only [kron, Matrix.of_apply]
    exact Finset.prod_congr rfl fun j _ => by rw [Function.update_of_ne j.2]
  rw [Mat_tuckerMul, hk, Function.update_self, Matrix.transpose_one, Matrix.mul_one, h]

/-- **From the mode-wise to the full invariance** (arXiv 2010.02022, last step of the proof of
Theorem 6): `A ×ᵢ Pᵢ = A` for all `i` gives `A X_{i} Pᵢ = A`. -/
theorem tuckerMul_eq_self_of_mode (P : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℝ) (A : Tensor n)
    (h : ∀ i, P i * Mat i A = Mat i A) : tuckerMul P A = A := by
  classical
  have key : ∀ s : Finset (Fin d), tuckerMul (fun j => if j ∈ s then P j else 1) A = A := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      have hfun : (fun j => if j ∈ insert i s then P j else 1) =
          fun j => Function.update (fun j => (1 : Matrix (Fin (n j)) (Fin (n j)) ℝ)) i (P i) j *
            (if j ∈ s then P j else 1) := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj]
      rw [hfun, ← tuckerMul_tuckerMul, ih, tuckerMul_update_eq i _ A (h i)]
  simpa using key Finset.univ

/-! ### The integrator -/

/-! A QR factorization `K = Q R` (`Q` with orthonormal columns, `R` upper triangular) is the core
`Matrix.IsQR K Q R`; the local `IsQR` of an earlier version of this file was the same structure
(unification batch C4). If `K` has rank `< k`, the factor `Q` is not determined by `K`. -/

/-- A QR factorization with invertible `R` has full column rank. -/
lemma IsQR.rank_eq {κ : Type*} [Fintype κ] {k : ℕ} {K Q : Matrix κ (Fin k) ℝ}
    {R : Matrix (Fin k) (Fin k) ℝ} (h : IsQR K Q R) (hR : IsUnit R) : K.rank = k := by
  have hRk : R.rank = k := by simpa using Matrix.rank_of_isUnit R hR
  have h1 : R = Qᵀ * K := by rw [h.eq, ← Matrix.mul_assoc, h.orth, Matrix.one_mul]
  apply le_antisymm
  · rw [h.eq]
    exact (Matrix.rank_mul_le_right _ _).trans hRk.le
  · calc k = R.rank := hRk.symm
      _ = (Qᵀ * K).rank := by rw [← h1]
      _ ≤ K.rank := Matrix.rank_mul_le_right _ _

/-- The matrix `Vᵢ = (⊗_{j ≠ i} Uⱼ) Qᵢ` of the K-step (paper: `Vᵢ⁰ᵀ = Qᵢᵀ ⊗_{j ≠ i} Uⱼ⁰ᵀ`). -/
noncomputable def modeV (U : ModeMatrices n r) (Q : ∀ i, Matrix (OffMode r i) (Fin (r i)) ℝ)
    (i : Fin d) : Matrix (OffMode n i) (Fin (r i)) ℝ :=
  kron U i * Q i

/-- **One step of the Tucker BUG integrator** (arXiv 2010.02022, §5.1) from
`Y₀ = C₀ X U⁰ᵢ` at `t₀` to `Y₁ = C(t₁) X U¹ᵢ` at `t₁`:

* `U⁰ᵢ` has orthonormal columns and `Matᵢ(C₀)ᵀ = Qᵢ Sᵢᵀ` is a QR factorization;
* with `Vᵢ = (⊗_{j ≠ i} U⁰ⱼ) Qᵢ` and `Fᵢ = Matᵢ ∘ F(t, ·) ∘ Tenᵢ`, the matrix `Kᵢ` solves
  `K̇ᵢ = Fᵢ(t, Kᵢ Vᵢᵀ) Vᵢ`, `Kᵢ(t₀) = U⁰ᵢ Sᵢ`;
* `Kᵢ(t₁) = U¹ᵢ Rᵢ` is a QR factorization;
* the core solves `Ċ = F(t, C X U¹ᵢ) X U¹ᵢᵀ`, `C(t₀) = C₀ X U¹ᵢᵀ U⁰ᵢ`. -/
structure IsTuckerStep (F : ℝ → Tensor n → Tensor n) (t₀ t₁ : ℝ) (U₀ : ModeMatrices n r)
    (C₀ : Tensor r) (Q : ∀ i, Matrix (OffMode r i) (Fin (r i)) ℝ)
    (S : ∀ i, Matrix (Fin (r i)) (Fin (r i)) ℝ) (K : ∀ i, ℝ → Matrix (Fin (n i)) (Fin (r i)) ℝ)
    (U₁ : ModeMatrices n r) (R : ∀ i, Matrix (Fin (r i)) (Fin (r i)) ℝ) (C : ℝ → Tensor r) :
    Prop where
  orth₀ : ∀ i, (U₀ i)ᵀ * U₀ i = 1
  qr₀ : ∀ i, IsQR (Mat i C₀)ᵀ (Q i) (S i)ᵀ
  kODE : ∀ i, ODESolution
    (fun t Kᵢ => Mat i (F t (Ten i (Kᵢ * (modeV U₀ Q i)ᵀ))) * modeV U₀ Q i) (K i) t₀ t₁
  kInit : ∀ i, K i t₀ = U₀ i * S i
  qr₁ : ∀ i, IsQR (K i t₁) (U₁ i) (R i)
  cODE : ODESolution (fun t c => tuckerMul (fun i => (U₁ i)ᵀ) (F t (tuckerMul U₁ c))) C t₀ t₁
  cInit : C t₀ = tuckerMul (fun i => (U₁ i)ᵀ * U₀ i) C₀

/-- The continuous linear map `X ↦ Matᵢ(X) N`. -/
noncomputable def matCLM (i : Fin d) {q : Type*} [Fintype q] (N : Matrix (OffMode n i) q ℝ) :
    Tensor n →L[ℝ] Matrix (Fin (n i)) q ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => Mat i X * N
      map_add' := fun X Y => by rw [Mat_add, Matrix.add_mul]
      map_smul' := fun c X => by simp [Mat_smul, Matrix.smul_mul] }

/-- The continuous linear map `X ↦ X X Uᵢ`. -/
noncomputable def tuckerCLM (U : ModeMatrices m n) : Tensor n →L[ℝ] Tensor m :=
  LinearMap.toContinuousLinearMap
    { toFun := tuckerMul U
      map_add' := tuckerMul_add U
      map_smul' := tuckerMul_smul U }

section Step

variable {F : ℝ → Tensor n → Tensor n} {A : ℝ → Tensor n} {t₀ t₁ : ℝ} {U₀ U₁ : ModeMatrices n r}
  {C₀ : Tensor r} {Q : ∀ i, Matrix (OffMode r i) (Fin (r i)) ℝ}
  {S R : ∀ i, Matrix (Fin (r i)) (Fin (r i)) ℝ} {K : ∀ i, ℝ → Matrix (Fin (n i)) (Fin (r i)) ℝ}
  {C : ℝ → Tensor r}

/-- `Vᵢ` has orthonormal columns. -/
lemma modeV_orth {U : ModeMatrices n r} {Q : ∀ i, Matrix (OffMode r i) (Fin (r i)) ℝ}
    (hU : ∀ i, (U i)ᵀ * U i = 1) (hQ : ∀ i, (Q i)ᵀ * Q i = 1) (i : Fin d) :
    (modeV U Q i)ᵀ * modeV U Q i = 1 := by
  rw [modeV, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (kron U i),
    kron_orth hU, Matrix.one_mul, hQ]

/-- **`Matᵢ(Y) = Uᵢ Sᵢ Vᵢᵀ`** for `Y = C X Uⱼ` and `Matᵢ(C)ᵀ = Qᵢ Sᵢᵀ` (paper, §5.1). -/
lemma Mat_eq_of_fac {U : ModeMatrices n r} {C : Tensor r}
    {Q : ∀ i, Matrix (OffMode r i) (Fin (r i)) ℝ} {S : ∀ i, Matrix (Fin (r i)) (Fin (r i)) ℝ}
    {i : Fin d} (h : (Mat i C)ᵀ = Q i * (S i)ᵀ) :
    Mat i (tuckerMul U C) = U i * S i * (modeV U Q i)ᵀ := by
  have h' : Mat i C = S i * (Q i)ᵀ := by
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul] using this
  rw [Mat_tuckerMul, h', modeV, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- **The explicit K-step** (arXiv 2010.02022, proof of Lemma 1 applied to `Matᵢ`): for
`F(t, Y) = Ȧ(t)` and `Y₀ = A(t₀)`, one has `Kᵢ(t₁) = Matᵢ(A(t₁)) Vᵢ`. -/
theorem IsTuckerStep.k_eq (hs : IsTuckerStep F t₀ t₁ U₀ C₀ Q S K U₁ R C) (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) (h0 : tuckerMul U₀ C₀ = A t₀) (i : Fin d) :
    K i t₁ = Mat i (A t₁) * modeV U₀ Q i := by
  have hV := modeV_orth hs.orth₀ (fun i => (hs.qr₀ i).orth) i
  have hY : U₀ i * S i * (modeV U₀ Q i)ᵀ = Mat i (A t₀) := by
    rw [← h0, Mat_eq_of_fac (hs.qr₀ i).eq]
  have h := (hs.kODE i).eq_add_map_sub (matCLM i (modeV U₀ Q i))
    (A' := fun t => F t (Ten i (K i t * (modeV U₀ Q i)ᵀ))) hA.cont
    (fun t ht => hA.deriv t ht _) (fun t _ => rfl) t₁ (right_mem_Icc.mpr ht)
  rw [h, hs.kInit]
  change U₀ i * S i + Mat i (A t₁ - A t₀) * modeV U₀ Q i = _
  rw [Mat_sub, Exactness.kStep_eq hV hY]

/-- **The explicit result of a step** (arXiv 2010.02022, the display in the proof of Theorem 6):
for `F(t, Y) = Ȧ(t)` and `Y₀ = A(t₀)`, without any rank assumption,
`Y₁ = A(t₁) X U¹ᵢ U¹ᵢᵀ`. -/
theorem IsTuckerStep.eq_proj (hs : IsTuckerStep F t₀ t₁ U₀ C₀ Q S K U₁ R C) (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) (h0 : tuckerMul U₀ C₀ = A t₀) :
    tuckerMul U₁ (C t₁) = tuckerMul (fun i => U₁ i * (U₁ i)ᵀ) (A t₁) := by
  have h := hs.cODE.eq_add_map_sub (tuckerCLM fun i => (U₁ i)ᵀ)
    (A' := fun t => F t (tuckerMul U₁ (C t))) hA.cont
    (fun t ht => hA.deriv t ht _) (fun t _ => rfl) t₁ (right_mem_Icc.mpr ht)
  have h2 : C t₁ = tuckerMul (fun i => (U₁ i)ᵀ) (A t₁) := by
    rw [h, hs.cInit]
    change tuckerMul (fun i => (U₁ i)ᵀ * U₀ i) C₀ + tuckerMul (fun i => (U₁ i)ᵀ) (A t₁ - A t₀) = _
    rw [← tuckerMul_tuckerMul, h0, tuckerMul_sub]
    abel
  rw [h2, tuckerMul_tuckerMul]

/-- **Exactness criterion** (arXiv 2010.02022, proof of Theorem 6, sharpened to an equivalence):
for `F(t, Y) = Ȧ(t)` and `Y₀ = A(t₀)`, a step is exact if and only if the new bases capture every
matricization of `A(t₁)`.  There is no rank or overlap assumption. -/
theorem IsTuckerStep.exact_iff (hs : IsTuckerStep F t₀ t₁ U₀ C₀ Q S K U₁ R C) (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) (h0 : tuckerMul U₀ C₀ = A t₀) :
    tuckerMul U₁ (C t₁) = A t₁ ↔ ∀ i, U₁ i * (U₁ i)ᵀ * Mat i (A t₁) = Mat i (A t₁) := by
  rw [hs.eq_proj ht hA h0]
  refine ⟨fun h i => ?_, tuckerMul_eq_self_of_mode _ _⟩
  have horth := (hs.qr₁ i).orth
  have h1 := congrArg (Mat i) h
  rw [Mat_tuckerMul] at h1
  rw [← h1]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc (U₁ i) (U₁ i)ᵀ (U₁ i), horth, Matrix.mul_one]

/-- A rank-`r` Tucker form `A = C X Uᵢ` with orthonormal `Uᵢ` and `Matᵢ(C)ᵀ = Qᵢ Sᵢᵀ`, `Qᵢ` with
orthonormal columns and `Sᵢ` invertible; so `Matᵢ(A) = Uᵢ Sᵢ Vᵢᵀ` with `Vᵢ = (⊗_{j ≠ i} Uⱼ) Qᵢ`
is the factorization (3) of the paper for each matricization, and `A` has multilinear rank
exactly `r` (`IsTuckerForm.rank_Mat`). -/
structure IsTuckerForm (A : Tensor n) (U : ModeMatrices n r) (C : Tensor r)
    (Q : ∀ i, Matrix (OffMode r i) (Fin (r i)) ℝ) (S : ∀ i, Matrix (Fin (r i)) (Fin (r i)) ℝ) :
    Prop where
  eq : A = tuckerMul U C
  orthU : ∀ i, (U i)ᵀ * U i = 1
  orthQ : ∀ i, (Q i)ᵀ * Q i = 1
  fac : ∀ i, (Mat i C)ᵀ = Q i * (S i)ᵀ
  unit : ∀ i, IsUnit (S i)

lemma IsTuckerForm.mat_eq {A : Tensor n} {U : ModeMatrices n r} {C' : Tensor r}
    {Q : ∀ i, Matrix (OffMode r i) (Fin (r i)) ℝ} {S : ∀ i, Matrix (Fin (r i)) (Fin (r i)) ℝ}
    (h : IsTuckerForm A U C' Q S) (i : Fin d) : Mat i A = U i * S i * (modeV U Q i)ᵀ := by
  rw [h.eq, Mat_eq_of_fac (h.fac i)]

/-- A tensor in rank-`r` Tucker form (arXiv 2010.02022, §5, factorization of each `Matᵢ`) has
multilinear rank exactly `r`. -/
theorem IsTuckerForm.rank_Mat {A : Tensor n} {U : ModeMatrices n r} {C' : Tensor r}
    {Q : ∀ i, Matrix (OffMode r i) (Fin (r i)) ℝ} {S : ∀ i, Matrix (Fin (r i)) (Fin (r i)) ℝ}
    (h : IsTuckerForm A U C' Q S) (i : Fin d) : (Mat i A).rank = r i := by
  have hM := h.mat_eq i
  have hV := modeV_orth h.orthU h.orthQ i
  have h1 : (U i)ᵀ * Mat i A * modeV U Q i = S i := by
    rw [hM]
    calc (U i)ᵀ * (U i * S i * (modeV U Q i)ᵀ) * modeV U Q i
        = ((U i)ᵀ * U i) * S i * ((modeV U Q i)ᵀ * modeV U Q i) := by
          simp only [Matrix.mul_assoc]
      _ = S i := by rw [h.orthU, hV, Matrix.one_mul, Matrix.mul_one]
  have hS : (S i).rank = r i := by
    simpa using Matrix.rank_of_isUnit (S i) (h.unit i)
  apply le_antisymm
  · rw [hM]
    calc (U i * S i * (modeV U Q i)ᵀ).rank ≤ (U i * S i).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (S i).rank := Matrix.rank_mul_le_right _ _
      _ = r i := hS
  · calc r i = (S i).rank := hS.symm
      _ = ((U i)ᵀ * Mat i A * modeV U Q i).rank := by rw [h1]
      _ ≤ ((U i)ᵀ * Mat i A).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (Mat i A).rank := Matrix.rank_mul_le_right _ _

/-- The gap in the proof of Theorem 6 of arXiv 2010.02022: the overlap of the `V` factors in terms
of the `U` overlaps is `Vᵢᵀ V'ᵢ = Qᵢᵀ (⊗_{j ≠ i} Uⱼᵀ U'ⱼ) Q'ᵢ`.  For `d ≥ 3` the middle factor,
of size `∏_{j ≠ i} rⱼ`, is compressed to `rᵢ × rᵢ`, and the compression of an invertible matrix can
be singular (`Counterexample.overlap_zero`).  For `d = 2` the factors `Qᵢ` are square and the
hypothesis of the paper suffices (Theorem 3, `LeanDLRA.Exactness.bug_exact_ode_of_factors`). -/
theorem modeV_overlap (U U' : ModeMatrices n r) (Q Q' : ∀ i, Matrix (OffMode r i) (Fin (r i)) ℝ)
    (i : Fin d) :
    (modeV U Q i)ᵀ * modeV U' Q' i =
      (Q i)ᵀ * kron (fun j => (U j)ᵀ * U' j) i * Q' i := by
  rw [modeV, modeV, Matrix.transpose_mul, ← kron_transpose_mul]
  simp only [Matrix.mul_assoc]

/-- **Tucker exactness, Lemma 1 form** (arXiv 2010.02022, Theorem 6, corrected).  If
`Matᵢ(A(t₁)) = Uᵢ Sᵢ Vᵢᵀ` with `rᵢ` columns (`Sᵢ` may be singular, `Uᵢ`, `Vᵢ` need not be
orthonormal) and `Vᵢᵀ V⁰ᵢ` is invertible for each `i`, where `V⁰ᵢ` is the K-step matrix of the
integrator, then the step for `F(t, Y) = Ȧ(t)` from `Y₀ = A(t₀)` is exact.  This is the hypothesis
that the paper's proof uses through Lemma 1; the printed hypothesis on the `U` factors is not
sufficient (`Counterexample.theorem6_false`).  No upper triangularity of the QR factors is used. -/
theorem IsTuckerStep.exact (hs : IsTuckerStep F t₀ t₁ U₀ C₀ Q S K U₁ R C) (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) (h0 : tuckerMul U₀ C₀ = A t₀)
    {Ua : ModeMatrices n r} {Sa : ∀ i, Matrix (Fin (r i)) (Fin (r i)) ℝ}
    {Va : ∀ i, Matrix (OffMode n i) (Fin (r i)) ℝ}
    (hfac : ∀ i, Mat i (A t₁) = Ua i * Sa i * (Va i)ᵀ)
    (hV : ∀ i, IsUnit ((Va i)ᵀ * modeV U₀ Q i)) : tuckerMul U₁ (C t₁) = A t₁ := by
  refine (hs.exact_iff ht hA h0).mpr fun i => ?_
  have hcap := (Exactness.capture_of_qr (hs.qr₁ i).orth (hs.qr₁ i).eq.symm).1
  exact Exactness.mul_eq_self_of_capture (hs.k_eq ht hA h0 i) hcap
    (Exactness.exists_eq_mul_mul_of_isUnit (hfac i) (hV i))

/-- **Tucker exactness, corrected form of the paper** (arXiv 2010.02022, Theorem 6).  Let `A(t₀)`
and `A(t₁)` be in rank-`r` Tucker form, `Matᵢ(A(tₖ)) = Uᵢ(tₖ) Sᵢ(tₖ) Vᵢ(tₖ)ᵀ`.  If each
`Vᵢ(t₁)ᵀ Vᵢ(t₀)` is invertible, the step for `F(t, Y) = Ȧ(t)` from any Tucker form of
`Y₀ = A(t₀)` satisfies `Y₁ = A(t₁)`.  Difference from the paper: the overlap of the factors `Vᵢ`
replaces the overlap of the factors `Uᵢ`, which does not suffice for `d ≥ 3`
(`Counterexample.theorem6_false`); only the endpoints `t₀`, `t₁` enter.  Non-vacuous by
`Counterexample.exact_of_overlap_applies`. -/
theorem IsTuckerStep.exact_of_overlap (hs : IsTuckerStep F t₀ t₁ U₀ C₀ Q S K U₁ R C)
    (ht : t₀ ≤ t₁) (hA : IsDerivRHS F A t₀ t₁) (h0 : tuckerMul U₀ C₀ = A t₀)
    {Ue₀ Ue₁ : ModeMatrices n r} {Ce₀ Ce₁ : Tensor r}
    {Qe₀ Qe₁ : ∀ i, Matrix (OffMode r i) (Fin (r i)) ℝ}
    {Se₀ Se₁ : ∀ i, Matrix (Fin (r i)) (Fin (r i)) ℝ}
    (hf₀ : IsTuckerForm (A t₀) Ue₀ Ce₀ Qe₀ Se₀) (hf₁ : IsTuckerForm (A t₁) Ue₁ Ce₁ Qe₁ Se₁)
    (hV : ∀ i, IsUnit ((modeV Ue₁ Qe₁ i)ᵀ * modeV Ue₀ Qe₀ i)) :
    tuckerMul U₁ (C t₁) = A t₁ := by
  refine hs.exact ht hA h0 hf₁.mat_eq fun i => ?_
  have hY : U₀ i * S i * (modeV U₀ Q i)ᵀ = Ue₀ i * Se₀ i * (modeV Ue₀ Qe₀ i)ᵀ := by
    rw [← hf₀.mat_eq i, ← h0, Mat_eq_of_fac (hs.qr₀ i).eq]
  exact Exactness.isUnit_transpose_mul_of_eq hY (hf₀.orthU i) (hf₀.unit i) (hV i)

/-- **Tucker exactness from full rank K-steps** (arXiv 2010.02022, Theorem 6, corrected).  If
`A(t₁)` has multilinear rank at most `r` and every `Kᵢ(t₁)` has full column rank `rᵢ`, so that the
range of `U¹ᵢ` is determined by `Kᵢ(t₁)`, then the step for `F(t, Y) = Ȧ(t)` from `Y₀ = A(t₀)` is
exact.  No overlap assumption is needed; rank deficiency of some `Kᵢ(t₁)` is the only way to lose
exactness, and it does happen (`Counterexample.theorem6_fails_for_every_qr_factor`). -/
theorem IsTuckerStep.exact_of_rank (hs : IsTuckerStep F t₀ t₁ U₀ C₀ Q S K U₁ R C) (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) (h0 : tuckerMul U₀ C₀ = A t₀)
    (hrank : ∀ i, (Mat i (A t₁)).rank ≤ r i) (hK : ∀ i, (K i t₁).rank = r i) :
    tuckerMul U₁ (C t₁) = A t₁ := by
  refine (hs.exact_iff ht hA h0).mpr fun i => ?_
  have hk := hs.k_eq ht hA h0 i
  have hq := hs.qr₁ i
  have hle : LinearMap.range (K i t₁).mulVecLin ≤ LinearMap.range (Mat i (A t₁)).mulVecLin := by
    rw [hk, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have heq : LinearMap.range (K i t₁).mulVecLin = LinearMap.range (Mat i (A t₁)).mulVecLin :=
    Submodule.eq_of_le_of_finrank_le hle (by
      change (Mat i (A t₁)).rank ≤ (K i t₁).rank
      rw [hK]
      exact hrank i)
  apply Matrix.mulVec_injective
  funext v
  have hv : (Mat i (A t₁)).mulVec v ∈ LinearMap.range (K i t₁).mulVecLin := by
    rw [heq]
    exact ⟨v, rfl⟩
  obtain ⟨x, hx⟩ := hv
  rw [Matrix.mulVecLin_apply] at hx
  rw [← Matrix.mulVec_mulVec, ← hx, hq.eq, Matrix.mulVec_mulVec]
  congr 1
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (U₁ i)ᵀ, hq.orth, Matrix.one_mul]

/-- The hypotheses of Theorem 6 of arXiv 2010.02022, as printed: `F(t, Y) = Ȧ(t)`, the path
`A(t) = C(t) X Uᵢ(t)` has multilinear rank `r` on `[t₀, t₁]` with orthonormal `Uᵢ(t)`, and each
`rᵢ × rᵢ` matrix `Uᵢ(t₁)ᵀ Uᵢ(t₀)` is invertible. -/
structure Theorem6Hypotheses (F : ℝ → Tensor n → Tensor n) (A : ℝ → Tensor n)
    (Ue : ℝ → ModeMatrices n r) (Ce : ℝ → Tensor r) (t₀ t₁ : ℝ) : Prop where
  rhs : IsDerivRHS F A t₀ t₁
  tucker : ∀ t ∈ Icc t₀ t₁, A t = tuckerMul (Ue t) (Ce t)
  rank : ∀ t ∈ Icc t₀ t₁, ∀ i, (Mat i (A t)).rank = r i
  orth : ∀ t ∈ Icc t₀ t₁, ∀ i, (Ue t i)ᵀ * Ue t i = 1
  overlap : ∀ i, IsUnit ((Ue t₁ i)ᵀ * Ue t₀ i)

/-- **Theorem 6 of arXiv 2010.02022 with one added hypothesis**: under the printed hypotheses
(`Theorem6Hypotheses`), the step is exact provided that every `Kᵢ(t₁)` has full rank `rᵢ`.  The
added hypothesis cannot be dropped (`Counterexample.theorem6_false`); the printed overlap assumption
is not used.  Non-vacuous by `Counterexample.exact_of_hypotheses_applies`. -/
theorem IsTuckerStep.exact_of_hypotheses (hs : IsTuckerStep F t₀ t₁ U₀ C₀ Q S K U₁ R C)
    (ht : t₀ ≤ t₁) {Ue : ℝ → ModeMatrices n r} {Ce : ℝ → Tensor r}
    (hyp : Theorem6Hypotheses F A Ue Ce t₀ t₁) (h0 : tuckerMul U₀ C₀ = A t₀)
    (hK : ∀ i, (K i t₁).rank = r i) : tuckerMul U₁ (C t₁) = A t₁ :=
  hs.exact_of_rank ht hyp.rhs h0 (fun i => (hyp.rank t₁ (right_mem_Icc.mpr ht) i).le) hK

end Step

/-! ### The counterexample -/

namespace Counterexample

/-- All modes have size `2`. -/
abbrev nn : Fin 3 → ℕ := fun _ => 2

/-- The multilinear rank `(1, 2, 2)`. -/
def rr : Fin 3 → ℕ := ![1, 2, 2]

/-- The matrix path `B(t) = (1 - t) I + t J`, `J` the rotation by `π / 2`. -/
noncomputable def B (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 - t, -t; t, 1 - t]

/-- `√((1 - t)² + t²)`: all singular values of `B(t)` are equal to this. -/
noncomputable def sv (t : ℝ) : ℝ := √((1 - t) ^ 2 + t ^ 2)

lemma sv_pos (t : ℝ) : 0 < sv t := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg (1 - t), sq_nonneg t])

lemma sv_sq (t : ℝ) : sv t * sv t = (1 - t) ^ 2 + t ^ 2 :=
  Real.mul_self_sqrt (by positivity)

lemma B_transpose_mul (t : ℝ) : (B t)ᵀ * B t = (sv t * sv t) • 1 := by
  rw [sv_sq]
  ext a c
  fin_cases a <;> fin_cases c <;> simp [B, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma B_mul_transpose (t : ℝ) : B t * (B t)ᵀ = (sv t * sv t) • 1 := by
  rw [sv_sq]
  ext a c
  fin_cases a <;> fin_cases c <;> simp [B, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma sum_B_mul (t t' : ℝ) :
    ∑ a, ∑ c, B t a c * B t' a c = 2 * ((1 - t) * (1 - t') + t * t') := by
  simp [B, Fin.sum_univ_two]
  ring

/-- Mode `1` as a mode different from `0`. -/
def p01 : {j : Fin 3 // j ≠ 0} := ⟨1, by decide⟩
/-- Mode `2` as a mode different from `0`. -/
def p02 : {j : Fin 3 // j ≠ 0} := ⟨2, by decide⟩
/-- Mode `2` as a mode different from `1`. -/
def p12 : {j : Fin 3 // j ≠ 1} := ⟨2, by decide⟩
/-- Mode `1` as a mode different from `2`. -/
def p21 : {j : Fin 3 // j ≠ 2} := ⟨1, by decide⟩

/-- Multi-indices off mode `0`. -/
def eqv0 : OffMode rr 0 ≃ Fin 2 × Fin 2 where
  toFun b := (b p01, b p02)
  invFun q j := match j with
    | ⟨0, h⟩ => absurd rfl h
    | ⟨1, _⟩ => q.1
    | ⟨2, _⟩ => q.2
  left_inv b := by
    funext ⟨j, hj⟩
    fin_cases j
    · exact absurd rfl hj
    · rfl
    · rfl
  right_inv _ := rfl

/-- Multi-indices off mode `1`. -/
def eqv1 : OffMode rr 1 ≃ Fin 2 where
  toFun b := b p12
  invFun c j := match j with
    | ⟨0, _⟩ => (0 : Fin 1)
    | ⟨1, h⟩ => absurd rfl h
    | ⟨2, _⟩ => c
  left_inv b := by
    funext ⟨j, hj⟩
    fin_cases j
    · exact Subsingleton.elim (α := Fin 1) _ _
    · exact absurd rfl hj
    · rfl
  right_inv _ := rfl

/-- Multi-indices off mode `2`. -/
def eqv2 : OffMode rr 2 ≃ Fin 2 where
  toFun b := b p21
  invFun c j := match j with
    | ⟨0, _⟩ => (0 : Fin 1)
    | ⟨1, _⟩ => c
    | ⟨2, h⟩ => absurd rfl h
  left_inv b := by
    funext ⟨j, hj⟩
    fin_cases j
    · exact Subsingleton.elim (α := Fin 1) _ _
    · rfl
    · exact absurd rfl hj
  right_inv _ := rfl

lemma sum_off0 (f : Fin 2 → Fin 2 → ℝ) :
    ∑ b : OffMode rr 0, f (b p01) (b p02) = ∑ a, ∑ c, f a c := by
  rw [← Fintype.sum_prod_type' f]
  exact eqv0.sum_comp fun q => f q.1 q.2

lemma sum_off1 (f : Fin 2 → ℝ) : ∑ b : OffMode rr 1, f (b p12) = ∑ c, f c :=
  eqv1.sum_comp f

lemma sum_off2 (f : Fin 2 → ℝ) : ∑ b : OffMode rr 2, f (b p21) = ∑ c, f c :=
  eqv2.sum_comp f

/-- The core `C(t) ∈ ℝ^{1 × 2 × 2}`, the matrix `B(t)` seen as a tensor. -/
noncomputable def core (t : ℝ) : Tensor rr := fun y => B t (y 1) (y 2)

lemma B_eq (t : ℝ) : B t = B 0 + t • (B 1 - B 0) := by
  ext a c
  fin_cases a <;> fin_cases c <;> simp [B] <;> ring

lemma core_eq (t : ℝ) : core t = core 0 + t • (core 1 - core 0) := by
  funext y
  change B t (y 1) (y 2) = B 0 (y 1) (y 2) + t • (B 1 (y 1) (y 2) - B 0 (y 1) (y 2))
  rw [B_eq t]
  rfl

lemma Mat_core0 (t : ℝ) (a : Fin (rr 0)) (b : OffMode rr 0) :
    Mat 0 (core t) a b = B t (b p01) (b p02) := by
  change B t ((Equiv.piSplitAt 0 fun j => Fin (rr j)).symm (a, b) (p01 : Fin 3))
    ((Equiv.piSplitAt 0 fun j => Fin (rr j)).symm (a, b) (p02 : Fin 3)) = _
  rw [split_symm_ne, split_symm_ne]

lemma Mat_core1 (t : ℝ) (a : Fin (rr 1)) (b : OffMode rr 1) :
    Mat 1 (core t) a b = B t a (b p12) := by
  change B t ((Equiv.piSplitAt 1 fun j => Fin (rr j)).symm (a, b) 1)
    ((Equiv.piSplitAt 1 fun j => Fin (rr j)).symm (a, b) (p12 : Fin 3)) = _
  rw [split_symm_ne, split_symm_self]

lemma Mat_core2 (t : ℝ) (a : Fin (rr 2)) (b : OffMode rr 2) :
    Mat 2 (core t) a b = B t (b p21) a := by
  change B t ((Equiv.piSplitAt 2 fun j => Fin (rr j)).symm (a, b) (p21 : Fin 3))
    ((Equiv.piSplitAt 2 fun j => Fin (rr j)).symm (a, b) 2) = _
  rw [split_symm_ne, split_symm_self]

/-- The constant bases `U₁ = u`, `U₂ = U₃ = I`. -/
noncomputable def U0 (u : Fin 2 → ℝ) : ModeMatrices nn rr
  | 0 => Matrix.of fun a _ => u a
  | 1 => (1 : Matrix (Fin 2) (Fin 2) ℝ)
  | 2 => (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- The factors `Qᵢ(t)` of `Matᵢ(C(t))ᵀ = Qᵢ(t) Sᵢ(t)ᵀ`. -/
noncomputable def QQ (t : ℝ) : ∀ i, Matrix (OffMode rr i) (Fin (rr i)) ℝ
  | 0 => Matrix.of fun b _ => (√2 * sv t)⁻¹ * B t (b p01) (b p02)
  | 1 => Matrix.of fun b c => (1 : Matrix (Fin 2) (Fin 2) ℝ) (b p12) c
  | 2 => Matrix.of fun b c => (1 : Matrix (Fin 2) (Fin 2) ℝ) (b p21) c

/-- The factors `Sᵢ(t)` of `Matᵢ(C(t))ᵀ = Qᵢ(t) Sᵢ(t)ᵀ`. -/
noncomputable def SS (t : ℝ) : ∀ i, Matrix (Fin (rr i)) (Fin (rr i)) ℝ
  | 0 => Matrix.of fun _ _ => √2 * sv t
  | 1 => B t
  | 2 => (B t)ᵀ

lemma sqrt2_mul_self : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)

lemma sqrt2_ne : √2 ≠ 0 := by positivity

lemma sv_zero : sv 0 = 1 := by simp [sv]

lemma sv_one : sv 1 = 1 := by simp [sv]

/-- The overlap of the mode-`0` factors. -/
lemma QQ_overlap0 (t t' : ℝ) :
    (QQ t 0)ᵀ * QQ t' 0 = Matrix.of fun _ _ => ((1 - t) * (1 - t') + t * t') / (sv t * sv t') := by
  ext a c
  change ∑ b : OffMode rr 0, ((√2 * sv t)⁻¹ * B t (b p01) (b p02)) *
    ((√2 * sv t')⁻¹ * B t' (b p01) (b p02)) = _
  rw [sum_off0 fun x y => ((√2 * sv t)⁻¹ * B t x y) * ((√2 * sv t')⁻¹ * B t' x y)]
  have h : ∀ x y, ((√2 * sv t)⁻¹ * B t x y) * ((√2 * sv t')⁻¹ * B t' x y) =
      ((√2 * sv t)⁻¹ * (√2 * sv t')⁻¹) * (B t x y * B t' x y) := fun x y => by ring
  simp only [h, ← Finset.mul_sum, sum_B_mul]
  have h2 := sqrt2_mul_self
  have h3 := sqrt2_ne
  have h4 := (sv_pos t).ne'
  have h5 := (sv_pos t').ne'
  simp only [Matrix.of_apply]
  field_simp
  rw [show √2 ^ 2 = 2 by rw [sq, h2]]

lemma sum_mul_one (f : Fin 2 → ℝ) (c : Fin 2) :
    ∑ x, f x * (1 : Matrix (Fin 2) (Fin 2) ℝ) x c = f c := by
  simp [Matrix.one_apply]

lemma sum_one_mul (f : Fin 2 → ℝ) (c : Fin 2) :
    ∑ x, (1 : Matrix (Fin 2) (Fin 2) ℝ) c x * f x = f c := by
  simp [Matrix.one_apply]

lemma sum_one_mul_one (c c' : Fin 2) :
    ∑ x, (1 : Matrix (Fin 2) (Fin 2) ℝ) x c * (1 : Matrix (Fin 2) (Fin 2) ℝ) x c' =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) c c' := by
  simp [Matrix.one_apply, eq_comm]

lemma fin3_cases {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (i : Fin 3) : P i := by
  fin_cases i
  exacts [h0, h1, h2]

lemma QQ_orth (t : ℝ) : ∀ i : Fin 3, (QQ t i)ᵀ * QQ t i = 1 := by
  refine fin3_cases ?_ ?_ ?_
  · rw [QQ_overlap0]
    ext a c
    have ha : a = c := Subsingleton.elim (α := Fin 1) a c
    subst ha
    have h4 := (sv_pos t).ne'
    have h5 := sv_sq t
    simp only [Matrix.of_apply, Matrix.one_apply_eq]
    rw [div_eq_one_iff_eq (mul_ne_zero h4 h4), h5]
    ring
  · ext c c'
    change ∑ b : OffMode rr 1, (1 : Matrix (Fin 2) (Fin 2) ℝ) (b p12) c *
      (1 : Matrix (Fin 2) (Fin 2) ℝ) (b p12) c' = _
    rw [sum_off1 fun x => (1 : Matrix (Fin 2) (Fin 2) ℝ) x c * (1 : Matrix (Fin 2) (Fin 2) ℝ) x c']
    exact sum_one_mul_one c c'
  · ext c c'
    change ∑ b : OffMode rr 2, (1 : Matrix (Fin 2) (Fin 2) ℝ) (b p21) c *
      (1 : Matrix (Fin 2) (Fin 2) ℝ) (b p21) c' = _
    rw [sum_off2 fun x => (1 : Matrix (Fin 2) (Fin 2) ℝ) x c * (1 : Matrix (Fin 2) (Fin 2) ℝ) x c']
    exact sum_one_mul_one c c'

/-- The factorization of the core. -/
lemma core_fac (t : ℝ) : ∀ i : Fin 3, (Mat i (core t))ᵀ = QQ t i * (SS t i)ᵀ := by
  refine fin3_cases ?_ ?_ ?_
  · ext b a
    have h4 := (sv_pos t).ne'
    change Mat 0 (core t) a b = ∑ c : Fin 1, ((√2 * sv t)⁻¹ * B t (b p01) (b p02)) * (√2 * sv t)
    rw [Mat_core0, Fin.sum_univ_one]
    field_simp
  · ext b a
    change Mat 1 (core t) a b = ∑ c : Fin 2, (1 : Matrix (Fin 2) (Fin 2) ℝ) (b p12) c * B t a c
    rw [Mat_core1]
    exact (sum_one_mul (B t a) (b p12)).symm
  · ext b a
    change Mat 2 (core t) a b = ∑ c : Fin 2, (1 : Matrix (Fin 2) (Fin 2) ℝ) (b p21) c * B t c a
    rw [Mat_core2]
    exact (sum_one_mul (fun c => B t c a) (b p21)).symm

lemma B_isUnit (t : ℝ) : IsUnit (B t) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two, isUnit_iff_ne_zero]
  simp only [B, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  nlinarith [sv_pos t, sv_sq t, mul_pos (sv_pos t) (sv_pos t)]

lemma SS_isUnit (t : ℝ) : ∀ i : Fin 3, IsUnit (SS t i) := by
  refine fin3_cases ?_ ?_ ?_
  · change IsUnit (Matrix.of fun _ _ => √2 * sv t : Matrix (Fin 1) (Fin 1) ℝ)
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_one, isUnit_iff_ne_zero]
    exact mul_ne_zero sqrt2_ne (sv_pos t).ne'
  · exact B_isUnit t
  · exact (Matrix.isUnit_transpose _).mpr (B_isUnit t)

lemma U0_orth {u : Fin 2 → ℝ} (hu : ∑ a, u a ^ 2 = 1) : ∀ i : Fin 3, (U0 u i)ᵀ * U0 u i = 1 := by
  refine fin3_cases ?_ ?_ ?_
  · ext a c
    have ha : a = c := Subsingleton.elim (α := Fin 1) a c
    subst ha
    rw [Matrix.one_apply_eq]
    change ∑ b, u b * u b = (1 : ℝ)
    simpa [sq] using hu
  · change ((1 : Matrix (Fin 2) (Fin 2) ℝ))ᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ)
    simp
  · change ((1 : Matrix (Fin 2) (Fin 2) ℝ))ᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ)
    simp

/-- The exact solution `A(t) = u ⊗ B(t)`. -/
noncomputable def Apath (u : Fin 2 → ℝ) (t : ℝ) : Tensor nn := tuckerMul (U0 u) (core t)

/-- The constant right-hand side `Ȧ(t)`. -/
noncomputable def cc (u : Fin 2 → ℝ) : Tensor nn := Apath u 1 - Apath u 0

lemma Apath_eq (u : Fin 2 → ℝ) (t : ℝ) : Apath u t = Apath u 0 + t • cc u := by
  rw [Apath, core_eq t, tuckerMul_add, tuckerMul_smul, tuckerMul_sub]
  rfl

/-- `A(t)` is in rank-`(1, 2, 2)` Tucker form, for every `t`. -/
lemma Apath_form {u : Fin 2 → ℝ} (hu : ∑ a, u a ^ 2 = 1) (t : ℝ) :
    IsTuckerForm (Apath u t) (U0 u) (core t) (QQ t) (SS t) where
  eq := rfl
  orthU := U0_orth hu
  orthQ := QQ_orth t
  fac := core_fac t
  unit := SS_isUnit t

lemma isDerivRHS_Apath (u : Fin 2 → ℝ) (t₁ : ℝ) :
    IsDerivRHS (fun _ _ => cc u) (Apath u) 0 t₁ := by
  have h := Exactness.isDerivRHS_add_smul (Apath u 0) (cc u) 0 t₁
  rwa [show (fun t => Apath u 0 + t • cc u) = Apath u from funext fun t => (Apath_eq u t).symm] at h

/-- The new bases: an arbitrary `U¹₁ = w` in mode `0`, the normalized `K`-factors otherwise. -/
noncomputable def U1 (w : Fin 2 → ℝ) (t : ℝ) : ModeMatrices nn rr
  | 0 => Matrix.of fun a _ => w a
  | 1 => ((sv t)⁻¹ • B t : Matrix (Fin 2) (Fin 2) ℝ)
  | 2 => ((sv t)⁻¹ • (B t)ᵀ : Matrix (Fin 2) (Fin 2) ℝ)

/-- The triangular QR factors at `t₁`. -/
noncomputable def R1 (ρ t : ℝ) : ∀ i, Matrix (Fin (rr i)) (Fin (rr i)) ℝ
  | 0 => Matrix.of fun _ _ => ρ
  | 1 => (sv t • 1 : Matrix (Fin 2) (Fin 2) ℝ)
  | 2 => (sv t • 1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- The K-step solutions. -/
noncomputable def KK (u : Fin 2 → ℝ) (i : Fin 3) (t : ℝ) : Matrix (Fin (nn i)) (Fin (rr i)) ℝ :=
  Mat i (Apath u t) * modeV (U0 u) (QQ 0) i

/-- The core-step solution. -/
noncomputable def CC (u w : Fin 2 → ℝ) (t₁ t : ℝ) : Tensor rr :=
  tuckerMul (fun i => (U1 w t₁ i)ᵀ * U0 u i) (core 0) +
    t • tuckerMul (fun i => (U1 w t₁ i)ᵀ) (cc u)

lemma KK_eq {u : Fin 2 → ℝ} (hu : ∑ a, u a ^ 2 = 1) (i : Fin 3) (t : ℝ) :
    KK u i t = U0 u i * (Mat i (core t) * QQ 0 i) := by
  rw [KK, Apath, Mat_tuckerMul, modeV]
  calc U0 u i * Mat i (core t) * (kron (U0 u) i)ᵀ * (kron (U0 u) i * QQ 0 i)
      = U0 u i * Mat i (core t) * ((kron (U0 u) i)ᵀ * kron (U0 u) i) * QQ 0 i := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [kron_orth (U0_orth hu), Matrix.mul_one, Matrix.mul_assoc]

lemma G0 (t : ℝ) : Mat 0 (core t) * QQ 0 0 = Matrix.of fun _ _ => √2 * (1 - t) := by
  ext a c
  change ∑ b : OffMode rr 0, Mat 0 (core t) a b * ((√2 * sv 0)⁻¹ * B 0 (b p01) (b p02)) = _
  simp only [Mat_core0]
  rw [sum_off0 fun x y => B t x y * ((√2 * sv 0)⁻¹ * B 0 x y), sv_zero]
  have h : ∀ x y, B t x y * ((√2 * 1)⁻¹ * B 0 x y) = (√2)⁻¹ * (B t x y * B 0 x y) :=
    fun x y => by rw [mul_one]; ring
  simp only [h, ← Finset.mul_sum, sum_B_mul, Matrix.of_apply]
  have h2 := sqrt2_mul_self
  have h3 := sqrt2_ne
  field_simp
  rw [show √2 ^ 2 = 2 by rw [sq, h2]]
  ring

lemma G1 (t : ℝ) (a c : Fin 2) : (Mat 1 (core t) * QQ 0 1) a c = B t a c :=
  calc (Mat 1 (core t) * QQ 0 1) a c
      = ∑ b : OffMode rr 1, Mat 1 (core t) a b * (1 : Matrix (Fin 2) (Fin 2) ℝ) (b p12) c := rfl
    _ = ∑ b : OffMode rr 1, B t a (b p12) * (1 : Matrix (Fin 2) (Fin 2) ℝ) (b p12) c :=
        Finset.sum_congr rfl fun b _ =>
          congrArg (· * (1 : Matrix (Fin 2) (Fin 2) ℝ) (b p12) c) (Mat_core1 t a b)
    _ = ∑ x, B t a x * (1 : Matrix (Fin 2) (Fin 2) ℝ) x c :=
        sum_off1 fun x => B t a x * (1 : Matrix (Fin 2) (Fin 2) ℝ) x c
    _ = B t a c := sum_mul_one _ c

lemma G2 (t : ℝ) (a c : Fin 2) : (Mat 2 (core t) * QQ 0 2) a c = B t c a :=
  calc (Mat 2 (core t) * QQ 0 2) a c
      = ∑ b : OffMode rr 2, Mat 2 (core t) a b * (1 : Matrix (Fin 2) (Fin 2) ℝ) (b p21) c := rfl
    _ = ∑ b : OffMode rr 2, B t (b p21) a * (1 : Matrix (Fin 2) (Fin 2) ℝ) (b p21) c :=
        Finset.sum_congr rfl fun b _ =>
          congrArg (· * (1 : Matrix (Fin 2) (Fin 2) ℝ) (b p21) c) (Mat_core2 t a b)
    _ = ∑ x, B t x a * (1 : Matrix (Fin 2) (Fin 2) ℝ) x c :=
        sum_off2 fun x => B t x a * (1 : Matrix (Fin 2) (Fin 2) ℝ) x c
    _ = B t c a := sum_mul_one (fun x => B t x a) c

/-- The value of the K-step solution in mode `0`: `K₀(t) = √2 (1 - t) u`. -/
lemma KK0 {u : Fin 2 → ℝ} (hu : ∑ a, u a ^ 2 = 1) (t : ℝ) (a : Fin 2) (c : Fin (rr 0)) :
    KK u 0 t a c = u a * (√2 * (1 - t)) := by
  rw [KK_eq hu, G0]
  change ∑ b : Fin 1, u a * (√2 * (1 - t)) = _
  simp

/-- The value of the K-step solution in mode `1`: `K₁(t) = B(t)`. -/
lemma KK1 {u : Fin 2 → ℝ} (hu : ∑ a, u a ^ 2 = 1) (t : ℝ) (a c : Fin 2) :
    KK u 1 t a c = B t a c := by
  rw [KK_eq hu]
  change ∑ x : Fin 2, (1 : Matrix (Fin 2) (Fin 2) ℝ) a x * (Mat 1 (core t) * QQ 0 1) x c = _
  rw [sum_one_mul (fun x => (Mat 1 (core t) * QQ 0 1) x c) a, G1]

/-- The value of the K-step solution in mode `2`: `K₂(t) = B(t)ᵀ`. -/
lemma KK2 {u : Fin 2 → ℝ} (hu : ∑ a, u a ^ 2 = 1) (t : ℝ) (a c : Fin 2) :
    KK u 2 t a c = B t c a := by
  rw [KK_eq hu]
  change ∑ x : Fin 2, (1 : Matrix (Fin 2) (Fin 2) ℝ) a x * (Mat 2 (core t) * QQ 0 2) x c = _
  rw [sum_one_mul (fun x => (Mat 2 (core t) * QQ 0 2) x c) a, G2]

lemma upper_fin_one (M : Matrix (Fin (rr 0)) (Fin (rr 0)) ℝ) : M.BlockTriangular id :=
  fun a b h => absurd h (by
    have : a = b := Subsingleton.elim (α := Fin 1) a b
    subst this
    exact lt_irrefl _)

lemma upper_smul_one (s : ℝ) : (s • 1 : Matrix (Fin 2) (Fin 2) ℝ).BlockTriangular id := by
  intro a c (h : c < a)
  rw [Matrix.smul_apply, Matrix.one_apply_ne (ne_of_lt h).symm, smul_zero]

/-- `IsQR` of the initial core. -/
lemma qr_core0 : ∀ i : Fin 3, IsQR (Mat i (core 0))ᵀ (QQ 0 i) (SS 0 i)ᵀ := by
  refine fin3_cases ⟨core_fac 0 0, QQ_orth 0 0, upper_fin_one _⟩ ⟨core_fac 0 1, QQ_orth 0 1, ?_⟩
    ⟨core_fac 0 2, QQ_orth 0 2, ?_⟩
  · have h : (B 0)ᵀ = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext a c
      fin_cases a <;> fin_cases c <;> simp [B]
    change Matrix.BlockTriangular ((B 0)ᵀ : Matrix (Fin 2) (Fin 2) ℝ) id
    rw [h]
    exact Matrix.blockTriangular_one
  · have h : B 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext a c
      fin_cases a <;> fin_cases c <;> simp [B]
    change Matrix.BlockTriangular (((B 0)ᵀ)ᵀ : Matrix (Fin 2) (Fin 2) ℝ) id
    rw [Matrix.transpose_transpose, h]
    exact Matrix.blockTriangular_one

/-- `IsQR` of the K-steps at `t₁`, when `K₀(t₁) = √2 (1 - t₁) u = ρ w`. -/
lemma qr_K {u w : Fin 2 → ℝ} (hu : ∑ a, u a ^ 2 = 1) (hw : ∑ a, w a ^ 2 = 1) {ρ t₁ : ℝ}
    (hρ : ∀ a, u a * (√2 * (1 - t₁)) = w a * ρ) :
    ∀ i : Fin 3, IsQR (KK u i t₁) (U1 w t₁ i) (R1 ρ t₁ i) := by
  have hs := (sv_pos t₁).ne'
  have hs2 : (sv t₁)⁻¹ * sv t₁ = 1 := inv_mul_cancel₀ hs
  refine fin3_cases ⟨?_, ?_, upper_fin_one _⟩ ⟨?_, ?_, ?_⟩ ⟨?_, ?_, ?_⟩
  · ext a c
    rw [KK0 hu]
    change _ = ∑ b : Fin 1, w a * ρ
    simpa using hρ a
  · ext a c
    have ha : a = c := Subsingleton.elim (α := Fin 1) a c
    subst ha
    rw [Matrix.one_apply_eq]
    change ∑ b, w b * w b = (1 : ℝ)
    simpa [sq] using hw
  · ext a c
    refine (KK1 hu t₁ a c).trans ?_
    change B t₁ a c = (((sv t₁)⁻¹ • B t₁ : Matrix (Fin 2) (Fin 2) ℝ) *
      (sv t₁ • 1 : Matrix (Fin 2) (Fin 2) ℝ)) a c
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hs2, one_smul]
  · change ((sv t₁)⁻¹ • B t₁ : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *
      ((sv t₁)⁻¹ • B t₁ : Matrix (Fin 2) (Fin 2) ℝ) = (1 : Matrix (Fin 2) (Fin 2) ℝ)
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, B_transpose_mul, smul_smul,
      smul_smul]
    have : (sv t₁)⁻¹ * (sv t₁)⁻¹ * (sv t₁ * sv t₁) = 1 := by field_simp
    rw [this, one_smul]
  · exact upper_smul_one _
  · ext a c
    refine (KK2 hu t₁ a c).trans ?_
    change (B t₁)ᵀ a c = (((sv t₁)⁻¹ • (B t₁)ᵀ : Matrix (Fin 2) (Fin 2) ℝ) *
      (sv t₁ • 1 : Matrix (Fin 2) (Fin 2) ℝ)) a c
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hs2, one_smul]
  · change ((sv t₁)⁻¹ • (B t₁)ᵀ : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *
      ((sv t₁)⁻¹ • (B t₁)ᵀ : Matrix (Fin 2) (Fin 2) ℝ) = (1 : Matrix (Fin 2) (Fin 2) ℝ)
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_transpose,
      B_mul_transpose, smul_smul, smul_smul]
    have : (sv t₁)⁻¹ * (sv t₁)⁻¹ * (sv t₁ * sv t₁) = 1 := by field_simp
    rw [this, one_smul]
  · exact upper_smul_one _

/-- Example for arXiv 2010.02022, Theorem 6: the construction is a genuine step of the Tucker BUG
integrator from `t₀ = 0` to `t₁`, for `Ȧ` constant, as soon as `K₀(t₁) = √2 (1 - t₁) u = ρ w`. -/
theorem isTuckerStep {u w : Fin 2 → ℝ} (hu : ∑ a, u a ^ 2 = 1) (hw : ∑ a, w a ^ 2 = 1) {ρ t₁ : ℝ}
    (hρ : ∀ a, u a * (√2 * (1 - t₁)) = w a * ρ) :
    IsTuckerStep (fun _ _ => cc u) 0 t₁ (U0 u) (core 0) (QQ 0) (SS 0) (KK u) (U1 w t₁) (R1 ρ t₁)
      (CC u w t₁) where
  orth₀ := U0_orth hu
  qr₀ := qr_core0
  kODE i := by
    have h : KK u i = fun t => KK u i 0 + t • (Mat i (cc u) * modeV (U0 u) (QQ 0) i) := by
      funext t
      simp only [KK]
      rw [Apath_eq u t, Mat_add, Mat_smul, Matrix.add_mul, Matrix.smul_mul]
    rw [h]
    exact Exactness.odeSolution_add_smul_of_const (fun _ _ => rfl) _ _ _
  kInit i := by
    have hV := modeV_orth (U0_orth hu) (QQ_orth 0) i
    have hM : Mat i (Apath u 0) = U0 u i * SS 0 i * (modeV (U0 u) (QQ 0) i)ᵀ :=
      (Apath_form hu 0).mat_eq i
    rw [KK, hM, Matrix.mul_assoc, hV, Matrix.mul_one]
  qr₁ := qr_K hu hw hρ
  cODE := Exactness.odeSolution_add_smul_of_const (fun _ _ => rfl) _ _ _
  cInit := by simp [CC]

/-- Counterexample to arXiv 2010.02022, Theorem 6: if the new mode-`0` basis `U¹₀ = w` is orthogonal
to `u`, the step returns `Y₁ = 0`. -/
theorem step_eq_zero {u w : Fin 2 → ℝ} (hu : ∑ a, u a ^ 2 = 1) (hw : ∑ a, w a ^ 2 = 1)
    (huw : ∑ a, u a * w a = 0) : tuckerMul (U1 w 1) (CC u w 1 1) = 0 := by
  have hs := isTuckerStep (ρ := 0) (t₁ := 1) hu hw (fun a => by simp)
  rw [hs.eq_proj zero_le_one (isDerivRHS_Apath u 1) rfl, Apath, tuckerMul_tuckerMul]
  have hz : (U1 w 1 0)ᵀ * U0 u 0 = 0 := by
    ext a c
    change ∑ b, w b * u b = (0 : ℝ)
    simpa [mul_comm] using huw
  have hz' : U1 w 1 0 * (U1 w 1 0)ᵀ * U0 u 0 = 0 := by
    rw [Matrix.mul_assoc, hz, Matrix.mul_zero]
  funext x
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Finset.prod_eq_zero (Finset.mem_univ 0) (by simp only [hz']; rfl), mul_zero]

lemma Apath_ne_zero {u : Fin 2 → ℝ} (hu : ∑ a, u a ^ 2 = 1) (t : ℝ) : Apath u t ≠ 0 := by
  intro h
  have h1 := (Apath_form hu t).rank_Mat 1
  rw [h, show Mat 1 (0 : Tensor nn) = 0 from rfl, Matrix.rank_zero] at h1
  exact absurd h1 (by decide)

/-- `Uᵢ` are constant, so the overlaps of the `V` factors are those of the `Q` factors. -/
lemma overlap_eq {u : Fin 2 → ℝ} (hu : ∑ a, u a ^ 2 = 1) (t : ℝ) (i : Fin 3) :
    (modeV (U0 u) (QQ t) i)ᵀ * modeV (U0 u) (QQ 0) i = (QQ t i)ᵀ * QQ 0 i := by
  rw [modeV_overlap]
  simp only [U0_orth hu]
  rw [kron_one, Matrix.mul_one]

/-- For `t ≠ 1` all the overlaps `Vᵢ(t)ᵀ Vᵢ(0)` are invertible. -/
lemma overlap_isUnit {u : Fin 2 → ℝ} (hu : ∑ a, u a ^ 2 = 1) {t : ℝ} (ht : t ≠ 1) :
    ∀ i : Fin 3, IsUnit ((modeV (U0 u) (QQ t) i)ᵀ * modeV (U0 u) (QQ 0) i) := by
  refine fin3_cases ?_ ?_ ?_
  · rw [overlap_eq hu, QQ_overlap0]
    change IsUnit (Matrix.of fun _ _ => ((1 - t) * (1 - 0) + t * 0) / (sv t * sv 0) :
      Matrix (Fin 1) (Fin 1) ℝ)
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_one, isUnit_iff_ne_zero]
    have h1 : 1 - t ≠ 0 := sub_ne_zero.mpr ht.symm
    have h2 := (sv_pos t).ne'
    have h3 := (sv_pos 0).ne'
    simp only [Matrix.of_apply]
    rw [sub_zero, mul_one, mul_zero, add_zero]
    exact div_ne_zero h1 (mul_ne_zero h2 h3)
  · rw [overlap_eq hu]
    exact (QQ_orth 0 1).symm ▸ isUnit_one
  · rw [overlap_eq hu]
    exact (QQ_orth 0 2).symm ▸ isUnit_one

/-- Counterexample to arXiv 2010.02022, Theorem 6: at `t = 1` the mode-`0` overlap
`V₀(1)ᵀ V₀(0)` needed by Lemma 1 vanishes, although all the overlaps `Uᵢ(1)ᵀ Uᵢ(0) = I` of the
printed hypothesis are invertible. -/
theorem overlap_zero {u : Fin 2 → ℝ} (hu : ∑ a, u a ^ 2 = 1) :
    (modeV (U0 u) (QQ 1) 0)ᵀ * modeV (U0 u) (QQ 0) 0 = 0 := by
  rw [overlap_eq hu, QQ_overlap0]
  ext a c
  simp

/-- The printed hypotheses of arXiv 2010.02022, Theorem 6, hold for `A(t) = u ⊗ B(t)` on every
interval, for every unit vector `u`, with constant `Uᵢ` and affine `C(t)`. -/
theorem hypotheses {u : Fin 2 → ℝ} (hu : ∑ a, u a ^ 2 = 1) (t₁ : ℝ) :
    Theorem6Hypotheses (fun _ _ => cc u) (Apath u) (fun _ => U0 u) core 0 t₁ where
  rhs := isDerivRHS_Apath u t₁
  tucker _ _ := rfl
  rank t _ i := (Apath_form hu t).rank_Mat i
  orth _ _ := U0_orth hu
  overlap i := by rw [U0_orth hu i]; exact isUnit_one

/-- The K-step in mode `0` ends at `K₀(1) = 0`. -/
lemma KK0_one {u : Fin 2 → ℝ} (hu : ∑ a, u a ^ 2 = 1) : KK u 0 1 = 0 := by
  ext a c
  rw [KK0 hu]
  simp

/-- **arXiv 2010.02022, Theorem 6, fails for every choice of the QR factor of a zero column.**
Whatever unit vector `w` a QR routine returns for the zero column, take the orthogonal unit vector
`u` and `A(t) = u ⊗ ((1 - t) I + t J) ∈ ℝ^{2 × 2 × 2}`, `J` the rotation by `π / 2`.  The printed
hypotheses hold on `[0, 1]`, with multilinear rank `(1, 2, 2)` and `Uᵢ(1)ᵀ Uᵢ(0) = I`.  The K-step
in mode `0` gives `K₀(1) = 0`, so `K₀(1) = w · 0` is a QR factorization, and this is a genuine step
from `Y₀ = A(0)`.  It returns `Y₁ = 0`, while `A(1) ≠ 0`. -/
theorem theorem6_fails_for_every_qr_factor {w : Fin 2 → ℝ} (hw : ∑ a, w a ^ 2 = 1) :
    let u : Fin 2 → ℝ := ![-w 1, w 0]
    Theorem6Hypotheses (fun _ _ => cc u) (Apath u) (fun _ => U0 u) core 0 1 ∧
      IsTuckerStep (fun _ _ => cc u) 0 1 (U0 u) (core 0) (QQ 0) (SS 0) (KK u) (U1 w 1) (R1 0 1)
        (CC u w 1) ∧
      tuckerMul (U0 u) (core 0) = Apath u 0 ∧
      KK u 0 1 = 0 ∧
      tuckerMul (U1 w 1) (CC u w 1 1) = 0 ∧
      Apath u 1 ≠ 0 := by
  intro u
  have hu : ∑ a, u a ^ 2 = 1 := by
    rw [← hw]
    simp [u, Fin.sum_univ_two, add_comm]
  have huw : ∑ a, u a * w a = 0 := by
    simp [u, Fin.sum_univ_two]
    ring
  exact ⟨hypotheses hu 1, isTuckerStep hu hw fun a => by simp, rfl, KK0_one hu,
    step_eq_zero hu hw huw, Apath_ne_zero hu 1⟩

/-- **arXiv 2010.02022, Theorem 6, is false as printed**: its hypotheses, for `d = 3`, do not imply
`Y₁ = A(t₁)` for an arbitrary QR factorization of `Kᵢ(t₁)`.  The conclusion holds under the
invertibility of `Vᵢ(t₁)ᵀ Vᵢ(t₀)` (`IsTuckerStep.exact_of_overlap`), or if all `Kᵢ(t₁)` have full
rank (`IsTuckerStep.exact_of_hypotheses`).  When `Kᵢ(t₁)` has full rank the QR step is determined
and this failure cannot occur, so the failure sits on the degenerate set of rank-deficient
`Kᵢ(t₁)`. -/
theorem theorem6_false :
    ¬ ∀ (n r : Fin 3 → ℕ) (F : ℝ → Tensor n → Tensor n) (A : ℝ → Tensor n)
        (Ue : ℝ → ModeMatrices n r) (Ce : ℝ → Tensor r) (U₀ U₁ : ModeMatrices n r) (C₀ : Tensor r)
        (Q : ∀ i, Matrix (OffMode r i) (Fin (r i)) ℝ) (S R : ∀ i, Matrix (Fin (r i)) (Fin (r i)) ℝ)
        (K : ∀ i, ℝ → Matrix (Fin (n i)) (Fin (r i)) ℝ) (C : ℝ → Tensor r),
        Theorem6Hypotheses F A Ue Ce 0 1 → IsTuckerStep F 0 1 U₀ C₀ Q S K U₁ R C →
          tuckerMul U₀ C₀ = A 0 → tuckerMul U₁ (C 1) = A 1 := by
  intro h
  have hw : ∑ a, (![0, 1] : Fin 2 → ℝ) a ^ 2 = 1 := by simp [Fin.sum_univ_two]
  obtain ⟨h1, h2, h3, -, h5, h6⟩ := theorem6_fails_for_every_qr_factor hw
  exact h6 ((h _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3).symm.trans h5)

/-- A tensor index with `y 1 = 0`, `y 2 = 1`. -/
def yy : ∀ i, Fin (rr i)
  | 0 => (0 : Fin 1)
  | 1 => (0 : Fin 2)
  | 2 => (1 : Fin 2)

lemma Apath_ne_Apath_zero {u : Fin 2 → ℝ} (hu : ∑ a, u a ^ 2 = 1) {t : ℝ} (ht : t ≠ 0) :
    Apath u t ≠ Apath u 0 := by
  intro h
  have hinv : ∀ s, tuckerMul (fun i => (U0 u i)ᵀ) (Apath u s) = core s := fun s => by
    rw [Apath, tuckerMul_tuckerMul]
    simp only [U0_orth hu]
    exact tuckerMul_one _
  have h1 : core t = core 0 := by rw [← hinv t, h, hinv]
  have h2 : B t 0 1 = B 0 0 1 := congrFun h1 yy
  apply ht
  simpa [B] using h2

/-- **Non-vacuity** of the corrected arXiv 2010.02022, Theorem 6
(`IsTuckerStep.exact_of_overlap`): on the path above all its hypotheses hold for `0 < t₁ ≠ 1`, the
step is exact, and `A(t₁) ≠ A(0)`. -/
theorem exact_of_overlap_applies {u : Fin 2 → ℝ} (hu : ∑ a, u a ^ 2 = 1) {t₁ : ℝ} (h0 : 0 < t₁)
    (h1 : t₁ ≠ 1) :
    (∀ i, IsUnit ((modeV (U0 u) (QQ t₁) i)ᵀ * modeV (U0 u) (QQ 0) i)) ∧
      tuckerMul (U1 u t₁) (CC u u t₁ t₁) = Apath u t₁ ∧ Apath u t₁ ≠ Apath u 0 :=
  ⟨overlap_isUnit hu h1,
    (isTuckerStep hu hu (ρ := √2 * (1 - t₁)) fun _ => rfl).exact_of_overlap h0.le
      (isDerivRHS_Apath u t₁) rfl (Apath_form hu 0) (Apath_form hu t₁) (overlap_isUnit hu h1),
    Apath_ne_Apath_zero hu h0.ne'⟩

lemma R1_isUnit {ρ : ℝ} (hρ : ρ ≠ 0) (t : ℝ) : ∀ i : Fin 3, IsUnit (R1 ρ t i) := by
  have hs : IsUnit (sv t • 1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one, mul_one, isUnit_iff_ne_zero]
    exact pow_ne_zero _ (sv_pos t).ne'
  refine fin3_cases ?_ hs hs
  change IsUnit (Matrix.of fun _ _ => ρ : Matrix (Fin 1) (Fin 1) ℝ)
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_one, isUnit_iff_ne_zero]
  exact hρ

/-- **Non-vacuity** of `IsTuckerStep.exact_of_hypotheses` (arXiv 2010.02022, Theorem 6 with full
rank K-steps): on the path above, the printed hypotheses and the full rank of all `Kᵢ(t₁)` hold for
`0 < t₁ ≠ 1`, and the step is exact. -/
theorem exact_of_hypotheses_applies {u : Fin 2 → ℝ} (hu : ∑ a, u a ^ 2 = 1) {t₁ : ℝ} (h0 : 0 < t₁)
    (h1 : t₁ ≠ 1) :
    Theorem6Hypotheses (fun _ _ => cc u) (Apath u) (fun _ => U0 u) core 0 t₁ ∧
      (∀ i, (KK u i t₁).rank = rr i) ∧
      tuckerMul (U1 u t₁) (CC u u t₁ t₁) = Apath u t₁ := by
  have hρ : √2 * (1 - t₁) ≠ 0 := mul_ne_zero sqrt2_ne (sub_ne_zero.mpr h1.symm)
  have hs := isTuckerStep (u := u) hu hu (ρ := √2 * (1 - t₁)) (t₁ := t₁) fun _ => rfl
  have hK : ∀ i, (KK u i t₁).rank = rr i := fun i =>
    IsQR.rank_eq (hs.qr₁ i) (R1_isUnit hρ t₁ i)
  exact ⟨hypotheses hu t₁, hK, hs.exact_of_hypotheses h0.le (hypotheses hu t₁) rfl hK⟩

end Counterexample

/-- The local QR predicate of this file, replaced by the core `Matrix.IsQR` (same fields). -/
@[deprecated (since := "2026-11-09")] alias IsQR := Matrix.IsQR

end LeanDLRA.Literature.P2010_02022
