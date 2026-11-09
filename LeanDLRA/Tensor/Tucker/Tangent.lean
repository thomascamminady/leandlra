import LeanDLRA.Tensor.Tucker.Basic

/-!
# The tangent space of constrained Tucker manifolds and its orthogonal projector

Bachmayr–Eisenmann–Uschmajew (arXiv 2308.16720, Sec. 4.1) consider manifolds of tensors
`X = C ×₁ U₁ ⋯ ×_d U_d` whose core `C` lies in a submanifold `ℳ_c` of the full-rank cores that
is invariant under changes of basis: the Tucker manifold (`ℳ_c` open), and tensor train or
hierarchical Tucker manifolds for other choices of `ℳ_c`. By their Thm 4.1(iii) the tangent space
at `X` is spanned by `Ċ ×ₖ Uₖ + ∑ₖ C ×ₖ U̇ₖ ×_{j ≠ k} Uⱼ` with `Ċ ∈ T_C ℳ_c` and `Uₖᵀ U̇ₖ = 0`
(4.5), and their Prop. 4.2 gives its orthogonal projector `P_X = P_X⁰ + ∑ₖ P_Xᵏ`. This file
proves Prop. 4.2 for finite tensors (`Tensor ι`, `ι : Fin d → Type*`) in the core vocabulary:
mode projectors `modeProj`, co-range projectors `actOn (· ≠ k) (W Wᵀ)` and unfoldings `unfold`.

Differences from the paper: finite dimensions instead of `ℓ²(ℕ^d)`; the manifold structure
(Thm 4.1(i)–(ii)) is not formalized, and `T_X ℳ` is the span of (4.5), which is Thm 4.1(iii); the
tangent projector of `ℳ_c` is replaced by an arbitrary orthogonal projector `P_C` (only its
range enters); the orthonormal basis of the co-range `Vᵏ` of `Mat_k(X)` is a matrix `W_k` whose
columns lie in `Vᵏ` (`W_k = Mat_{≠k}(X) B_k`) and for which `W_k W_kᵀ` fixes `Mat_k(X)`.
Remark 4.3 (non-orthonormal `Uₖ`) and the curvature bounds (Props. 4.7–4.11) are not formalized.

## Main definitions

* `tuckerCLM U`: the multilinear product `C ↦ C ×ₖ Uₖ` as a continuous linear map.
* `compEquiv μ`, `coRangeCoeff`: the column index of the co-range unfolding `unfold (· ≠ μ)` and
  the coefficient matrix of a co-range map.
* `tuckerTangentGen U C PC`, `tuckerTangentSpace U C PC`: the tangent vectors (4.5) and their
  span `T_X ℳ`.
* `tuckerTangentProj U PC W`: the projector (4.7)–(4.9).

## Main results

* `tucker_tucker`, `tucker_one`, `tucker_eq_zero_of`, `inner_tucker_left` (the adjoint of
  `C ↦ C ×ₖ Uₖ` is `Z ↦ Z ×ₖ Uₖᵀ`), `modeAct_tucker`, `modeAct_sub`: algebra of multilinear
  products.
* `actOn_unfold_mul`: a co-range map `actOn (· ≠ μ) (Mat_{≠μ}(X) M)` maps into `X ×_μ A`.
* `tuckerTangentProj_eq_starProjection` (**Prop. 4.2**): `P_X` is the orthogonal projection onto
  `T_X ℳ`; `isOrthProj_tuckerTangentProj`, `tuckerTangentProj_eq_self_iff`, and
  `mem_tuckerTangentSpace_iff` (the vectors (4.5) already form the subspace).
-/

open scoped Matrix RealInnerProductSpace

namespace LeanDLRA.Tensor

section TuckerAlgebra

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {ι ρ σ : κ → Type*} [∀ k, Fintype (ι k)]
  [∀ k, Fintype (ρ k)] [∀ k, Fintype (σ k)]

omit [∀ k, Fintype (ι k)] in
/-- Multilinear products compose: `(C ×ₖ Aₖ) ×ₖ Bₖ = C ×ₖ (Bₖ Aₖ)`. -/
theorem tucker_tucker (C : Tensor ρ) (A : ∀ k, Matrix (σ k) (ρ k) ℝ)
    (B : ∀ k, Matrix (ι k) (σ k) ℝ) :
    tucker (tucker C A) B = tucker C (fun k => B k * A k) := by
  ext x
  simp only [tucker_apply, Matrix.mul_apply, Fintype.prod_sum, Finset.prod_mul_distrib,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => by ring

omit [∀ k, Fintype (ρ k)] in
/-- The multilinear product with identity matrices is the identity. -/
theorem tucker_one [∀ k, DecidableEq (ι k)] (C : Tensor ι) :
    tucker C (fun k => (1 : Matrix (ι k) (ι k) ℝ)) = C := by
  ext x
  rw [tucker_apply, Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hy
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [Ne.symm hk]),
      zero_mul]
  · simp

omit [∀ k, Fintype (ι k)] in
/-- A multilinear product with a zero factor vanishes. -/
theorem tucker_eq_zero_of {U : ∀ k, Matrix (ι k) (ρ k) ℝ} {k : κ} (h : U k = 0) (C : Tensor ρ) :
    tucker C U = 0 := by
  ext x
  simp only [tucker_apply, PiLp.zero_apply]
  exact Finset.sum_eq_zero fun y _ => by
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [h]), zero_mul]

/-- The adjoint of `C ↦ C ×ₖ Uₖ` is `Z ↦ Z ×ₖ Uₖᵀ`. -/
theorem inner_tucker_left (C : Tensor ρ) (U : ∀ k, Matrix (ι k) (ρ k) ℝ) (Z : Tensor ι) :
    ⟪tucker C U, Z⟫ = ⟪C, tucker Z (fun k => (U k)ᵀ)⟫ := by
  rw [inner_eq_sum, inner_eq_sum]
  simp only [tucker_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring

/-- A mode action on a Tucker tensor acts on its basis:
`(C ×ⱼ Uⱼ) ×ₖ A = C ×ₖ (A Uₖ) ×_{j ≠ k} Uⱼ`. -/
theorem modeAct_tucker (k : κ) (A : Matrix (ι k) (ι k) ℝ) (U : ∀ k, Matrix (ι k) (ρ k) ℝ)
    (C : Tensor ρ) : modeAct k A (tucker C U) = tucker C (Function.update U k (A * U k)) := by
  have hsplit : ∀ (V : ∀ j, Matrix (ι j) (ρ j) ℝ) (x : ∀ j, ι j) (y : ∀ j, ρ j),
      ∏ j, V j (x j) (y j) = V k (x k) (y k) * ∏ j ∈ Finset.univ.erase k, V j (x j) (y j) :=
    fun V x y => (Finset.mul_prod_erase _ _ (Finset.mem_univ k)).symm
  have hupd : ∀ (x : ∀ j, ι j) (c : ι k) (y : ∀ j, ρ j),
      ∏ j ∈ Finset.univ.erase k, U j (Function.update x k c j) (y j) =
        ∏ j ∈ Finset.univ.erase k, U j (x j) (y j) := fun x c y =>
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hupdU : ∀ (x : ∀ j, ι j) (y : ∀ j, ρ j),
      ∏ j ∈ Finset.univ.erase k, Function.update U k (A * U k) j (x j) (y j) =
        ∏ j ∈ Finset.univ.erase k, U j (x j) (y j) := fun x y =>
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  ext x
  simp only [modeAct_apply, tucker_apply, hsplit _ (Function.update x k _), hsplit
    (Function.update U k (A * U k)), Function.update_self, hupd, hupdU, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun c _ => by ring

end TuckerAlgebra

section CoRange

variable {d : ℕ} {ι : Fin d → Type*} [∀ k, Fintype (ι k)]

/-- `X ×ₖ (A - B) = X ×ₖ A - X ×ₖ B`. -/
theorem modeAct_sub (k : Fin d) (A B : Matrix (ι k) (ι k) ℝ) :
    modeAct k (A - B) = modeAct (ι := ι) k A - modeAct k B := by
  ext1 X; ext x
  simp [modeAct_apply, sub_mul, Finset.sum_sub_distrib]

/-- The multi-indices of the complement of the complement of mode `μ` are the indices of mode
`μ` (the column index set of the co-range unfolding `unfold (· ≠ μ)`). -/
def compEquiv (μ : Fin d) : (∀ j : {j : Fin d // ¬ j ≠ μ}, ι j) ≃ ι μ where
  toFun z := z ⟨μ, not_not.2 rfl⟩
  invFun c j := cast (congrArg ι (not_not.1 j.2).symm) c
  left_inv z := by
    funext ⟨j, hj⟩
    obtain rfl := not_not.1 hj
    rfl
  right_inv _ := rfl

omit [∀ k, Fintype (ι k)] in
/-- The part of `x` on the complement of the modes `≠ μ` is `x μ`. -/
lemma restrict_not_ne (μ : Fin d) (x : ∀ j, ι j) :
    Subtype.restrict (fun j => ¬ j ≠ μ) x = (compEquiv μ).symm (x μ) := by
  funext ⟨j, hj⟩
  obtain rfl := not_not.1 hj
  rfl

omit [∀ k, Fintype (ι k)] in
/-- Merging the part of `x` on the modes `≠ μ` with a mode-`μ` index `c` updates `x` at `μ`. -/
lemma merge_compEquiv_symm (μ : Fin d) (x : ∀ j, ι j) (c : ι μ) :
    merge (· ≠ μ) (Subtype.restrict (· ≠ μ) x) ((compEquiv μ).symm c) =
      Function.update x μ c := by
  funext j
  by_cases h : j = μ
  · subst h
    simp [merge, compEquiv]
  · simp [merge, h, Subtype.restrict]

/-- **Co-range maps built from the unfolding act on the mode `μ` of `X`**: a matrix of the form
`Mat_{≠μ}(X) M` acting on the modes `≠ μ` maps every `Z` to `X ×_μ A` for a matrix `A`
(depending on `M` and `Z`). This is why the co-range projector of the `μ`-th matricization of
`X` maps into the mode-`μ` variations of `X`. -/
theorem actOn_unfold_mul (μ : Fin d) (X Z : Tensor ι)
    (M : Matrix (∀ j : {j : Fin d // ¬ j ≠ μ}, ι j) (∀ j : {j : Fin d // j ≠ μ}, ι j) ℝ) :
    actOn (· ≠ μ) (unfold (· ≠ μ) X * M) Z = modeAct μ (Matrix.of fun a c =>
      ∑ z, M ((compEquiv μ).symm c) z * Z (merge (· ≠ μ) z ((compEquiv μ).symm a))) X := by
  ext x
  rw [actOn_apply, modeAct_apply]
  simp only [unfold_apply, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Fintype.sum_equiv (compEquiv μ) _ _ fun b => ?_
  rw [Equiv.symm_apply_apply, ← merge_compEquiv_symm, Equiv.symm_apply_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [override_eq_merge, restrict_not_ne]
  ring

end CoRange

/-! ### The tangent space of a constrained Tucker manifold -/

section Tangent

variable {d : ℕ} {ι r : Fin d → Type*} [∀ k, Fintype (ι k)] [∀ k, Fintype (r k)]

/-- The multilinear product `C ↦ C ×ₖ Uₖ` as a continuous linear map. -/
noncomputable def tuckerCLM (U : ∀ k, Matrix (ι k) (r k) ℝ) : Tensor r →L[ℝ] Tensor ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun C => tucker C U
      map_add' := fun C D => by
        ext x; simp [tucker_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c C => by
        ext x; simp [tucker_apply, Finset.mul_sum, mul_left_comm] }

/-- `tuckerCLM U C = C ×ₖ Uₖ`. -/
@[simp] lemma tuckerCLM_apply (U : ∀ k, Matrix (ι k) (r k) ℝ) (C : Tensor r) :
    tuckerCLM U C = tucker C U := rfl

variable (U : ∀ k, Matrix (ι k) (r k) ℝ) (C : Tensor r) (PC : Tensor r →L[ℝ] Tensor r)

/-- The tangent vectors (4.5) of Bachmayr–Eisenmann–Uschmajew (arXiv 2308.16720, Thm 4.1(iii))
at `X = C ×ₖ Uₖ`: `Ċ ×ₖ Uₖ + ∑ₖ C ×ₖ U̇ₖ ×_{j ≠ k} Uⱼ` with `Ċ` in the tangent space
`{Ċ | P_C Ċ = Ċ}` of the core manifold and `Uₖᵀ U̇ₖ = 0`. -/
def tuckerTangentGen : Set (Tensor ι) :=
  {ξ | ∃ Cdot : Tensor r, PC Cdot = Cdot ∧ ∃ Udot : ∀ k, Matrix (ι k) (r k) ℝ,
    (∀ k, (U k)ᵀ * Udot k = 0) ∧
      ξ = tucker Cdot U + ∑ k, tucker C (Function.update U k (Udot k))}

/-- The **tangent space** `T_X ℳ` at `X = C ×ₖ Uₖ` of a constrained Tucker manifold whose core
manifold has the tangent projector `P_C` (arXiv 2308.16720, Thm 4.1(iii)): the span of the
tangent vectors (4.5) (`tuckerTangentGen`; they already form a subspace when `P_C` is
linear). -/
noncomputable def tuckerTangentSpace : Submodule ℝ (Tensor ι) :=
  Submodule.span ℝ (tuckerTangentGen U C PC)

/-- The **tangent projector** (4.7)–(4.9) of arXiv 2308.16720, Prop. 4.2:
`P_X = P_X⁰ + ∑ₖ P_Xᵏ` with `P_X⁰ Z = P_C(Z ×ₖ Uₖᵀ) ×ₖ Uₖ` and
`P_Xᵏ = (I - P_{Uₖ}) ∘ Q_k`, where `Q_k = actOn {j ≠ k} (W_k W_kᵀ)` is the co-range projector of
the `k`-th matricization (`W_k` an orthonormal basis of the space `Vᵏ` spanned by the rows of
`Mat_k(X)`); in matricized form `Mat_k(P_Xᵏ Z) = (I - P_{Uᵏ}) Mat_k(Z) P_{Vᵏ}` (4.8). -/
noncomputable def tuckerTangentProj {s : Fin d → Type*} [∀ k, Fintype (s k)]
    (W : ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s k) ℝ) : Tensor ι →L[ℝ] Tensor ι :=
  (tuckerCLM U).comp (PC.comp (tuckerCLM fun k => (U k)ᵀ)) +
    ∑ k, (1 - modeProj k (U k)) * actOn (· ≠ k) (W k * (W k)ᵀ)

variable {U C PC}

variable [∀ k, DecidableEq (r k)]

/-- The mode-`k` variations of `X = C ×ⱼ Uⱼ` are mode-`k` actions on `X`:
`C ×ₖ U̇ ×_{j ≠ k} Uⱼ = X ×ₖ (U̇ Uₖᵀ)` for orthonormal `Uₖ`. -/
theorem tucker_update_eq_modeAct {k : Fin d} (hU : (U k)ᵀ * U k = 1)
    (Udot : Matrix (ι k) (r k) ℝ) :
    tucker C (Function.update U k Udot) = modeAct k (Udot * (U k)ᵀ) (tucker C U) := by
  rw [modeAct_tucker, Matrix.mul_assoc, hU, Matrix.mul_one]

omit [∀ k, DecidableEq (r k)] in
/-- The mode-`k` projector annihilates the mode-`k` variations with `Uₖᵀ U̇ = 0`. -/
theorem modeProj_tucker_update_eq_zero {k : Fin d} {Udot : Matrix (ι k) (r k) ℝ}
    (hUd : (U k)ᵀ * Udot = 0) :
    modeProj k (U k) (tucker C (Function.update U k Udot)) = 0 := by
  rw [modeProj, modeAct_tucker, Function.update_self, Function.update_idem, Matrix.mul_assoc, hUd,
    Matrix.mul_zero]
  exact tucker_eq_zero_of (k := k) (by simp) C

/-- The mode-`j` projector of an orthonormal `Uⱼ` fixes the mode-`k` variations, `j ≠ k`. -/
theorem modeProj_tucker_update_of_ne {j k : Fin d} (hjk : j ≠ k) (hU : (U j)ᵀ * U j = 1)
    (Udot : Matrix (ι k) (r k) ℝ) :
    modeProj j (U j) (tucker C (Function.update U k Udot)) =
      tucker C (Function.update U k Udot) := by
  have h := modeProj_tucker (U := Function.update U k Udot) j
    (by rw [Function.update_of_ne hjk]; exact hU) C
  rwa [Function.update_of_ne hjk] at h

omit [∀ k, DecidableEq (r k)] in
/-- The core part `(·) ×ⱼ Uⱼᵀ` of a mode-`k` variation with `Uₖᵀ U̇ = 0` vanishes. -/
theorem tucker_transpose_tucker_update {k : Fin d} {Udot : Matrix (ι k) (r k) ℝ}
    (hUd : (U k)ᵀ * Udot = 0) :
    tucker (tucker C (Function.update U k Udot)) (fun j => (U j)ᵀ) = 0 := by
  rw [tucker_tucker]
  exact tucker_eq_zero_of (k := k) (by simp [hUd]) C

/-- The coefficient matrix of a co-range map `actOn (· ≠ μ) (Mat_{≠μ}(X) M)` applied to `Z`
(`actOn_unfold_mul`). -/
def coRangeCoeff (μ : Fin d) (M : Matrix (∀ j : {j : Fin d // ¬ j ≠ μ}, ι j)
    (∀ j : {j : Fin d // j ≠ μ}, ι j) ℝ) (Z : Tensor ι) : Matrix (ι μ) (ι μ) ℝ :=
  Matrix.of fun a c => ∑ z, M ((compEquiv μ).symm c) z * Z (merge (· ≠ μ) z ((compEquiv μ).symm a))

omit [∀ k, DecidableEq (r k)] in
/-- **The mode terms of the tangent projector are mode-`k` variations**: if the columns of
`W` lie in the co-range `Vᵏ` of `Mat_k(X)` (`W = Mat_{≠k}(X) B`), then
`(I - P_{Uₖ}) Q_k Z = C ×ₖ U̇ ×_{j ≠ k} Uⱼ` with `U̇ = A Uₖ - Uₖ Uₖᵀ A Uₖ`, so `Uₖᵀ U̇ = 0`
for orthonormal `Uₖ`. -/
theorem one_sub_modeProj_coRange_eq {k : Fin d} {s : Type*} [Fintype s]
    {W : Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) s ℝ} {B : Matrix _ s ℝ}
    (hB : W = unfold (· ≠ k) (tucker C U) * B) (Z : Tensor ι) :
    (1 - modeProj k (U k)) (actOn (· ≠ k) (W * Wᵀ) Z) = tucker C (Function.update U k
      (coRangeCoeff k (B * Wᵀ) Z * U k - U k * (U k)ᵀ * coRangeCoeff k (B * Wᵀ) Z * U k)) := by
  have hWW : W * Wᵀ = unfold (· ≠ k) (tucker C U) * (B * Wᵀ) := by
    nth_rw 1 [hB]
    rw [Matrix.mul_assoc]
  rw [hWW, actOn_unfold_mul, ← coRangeCoeff, sub_apply, one_apply_eq_self, modeProj,
    modeAct_modeAct, ← sub_apply, ← modeAct_sub, modeAct_tucker, Matrix.sub_mul]

variable (hU : ∀ k, (U k)ᵀ * U k = 1)
include hU

/-- `Uₖᵀ (A Uₖ - Uₖ Uₖᵀ A Uₖ) = 0` for orthonormal `Uₖ`. -/
lemma transpose_mul_sub_mul {k : Fin d} (A : Matrix (ι k) (ι k) ℝ) :
    (U k)ᵀ * (A * U k - U k * (U k)ᵀ * A * U k) = 0 := by
  simp only [Matrix.mul_sub, ← Matrix.mul_assoc, hU k, Matrix.one_mul, sub_self]

/-- The value of the tangent projector at `Z` is a tangent vector (4.5). -/
theorem tuckerTangentProj_mem_gen (hPC : IsOrthProj PC) {s : Fin d → Type*}
    [∀ k, Fintype (s k)] {W : ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s k) ℝ}
    (hWB : ∀ k, ∃ B : Matrix _ (s k) ℝ, W k = unfold (· ≠ k) (tucker C U) * B) (Z : Tensor ι) :
    tuckerTangentProj U PC W Z ∈ tuckerTangentGen U C PC := by
  choose B hB using hWB
  refine ⟨PC (tucker Z fun k => (U k)ᵀ), hPC.idem _,
    fun k => coRangeCoeff k (B k * (W k)ᵀ) Z * U k -
      U k * (U k)ᵀ * coRangeCoeff k (B k * (W k)ᵀ) Z * U k,
    fun k => transpose_mul_sub_mul hU _, ?_⟩
  simp only [tuckerTangentProj, add_apply, sum_apply,
    ContinuousLinearMap.comp_apply, mul_apply_eq_comp, tuckerCLM_apply]
  exact congrArg _ (Finset.sum_congr rfl fun k _ => one_sub_modeProj_coRange_eq (hB k) Z)

/-- The residual `Z - P_X Z` is orthogonal to the core variations `Ċ ×ₖ Uₖ`, `P_C Ċ = Ċ`. -/
theorem inner_sub_tuckerTangentProj_core (hPC : IsOrthProj PC) {s : Fin d → Type*}
    [∀ k, Fintype (s k)] (W : ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s k) ℝ)
    (Z : Tensor ι) {Cdot : Tensor r} (hCd : PC Cdot = Cdot) :
    ⟪Z - tuckerTangentProj U PC W Z, tucker Cdot U⟫ = 0 := by
  have h0 : ⟪tucker (PC (tucker Z fun k => (U k)ᵀ)) U, tucker Cdot U⟫ = ⟪Z, tucker Cdot U⟫ := by
    rw [inner_tucker hU, hPC.symm, hCd, real_inner_comm, ← inner_tucker_left, real_inner_comm]
  have hk : ∀ k, ⟪(1 - modeProj k (U k)) (actOn (· ≠ k) (W k * (W k)ᵀ) Z), tucker Cdot U⟫ = 0 :=
    fun k => by
      rw [(isOrthProj_modeProj k (hU k)).compl.symm, sub_apply,
        one_apply_eq_self, modeProj_tucker k (hU k), sub_self, inner_zero_right]
  simp only [tuckerTangentProj, add_apply, sum_apply,
    ContinuousLinearMap.comp_apply, mul_apply_eq_comp, tuckerCLM_apply,
    inner_sub_left, inner_add_left, sum_inner, h0, hk, Finset.sum_const_zero, add_zero, sub_self]

/-- The residual `Z - P_X Z` is orthogonal to the mode-`m` variations `C ×ₘ U̇ ×_{j ≠ m} Uⱼ`,
`Uₘᵀ U̇ = 0`. -/
theorem inner_sub_tuckerTangentProj_update {s : Fin d → Type*} [∀ k, Fintype (s k)]
    {W : ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s k) ℝ}
    (hWX : ∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U) (Z : Tensor ι)
    {m : Fin d} {Udot : Matrix (ι m) (r m) ℝ} (hUd : (U m)ᵀ * Udot = 0) :
    ⟪Z - tuckerTangentProj U PC W Z, tucker C (Function.update U m Udot)⟫ = 0 := by
  set ξ := tucker C (Function.update U m Udot) with hξ
  have hsymm : ∀ k (Y : Tensor ι), ⟪actOn (· ≠ k) (W k * (W k)ᵀ) Z, Y⟫ =
      ⟪Z, actOn (· ≠ k) (W k * (W k)ᵀ) Y⟫ := fun k Y => by
    rw [inner_actOn, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hQ : actOn (· ≠ m) (W m * (W m)ᵀ) ξ = ξ := by
    rw [hξ, tucker_update_eq_modeAct (hU m), modeAct,
      actOn_comm_of_disjoint _ (fun k hk hk' => hk hk'), ← modeAct, hWX m]
  have h0 : ⟪tucker (PC (tucker Z fun k => (U k)ᵀ)) U, ξ⟫ = 0 := by
    rw [inner_tucker_left, hξ, tucker_transpose_tucker_update hUd, inner_zero_right]
  have hk : ∀ k, ⟪(1 - modeProj k (U k)) (actOn (· ≠ k) (W k * (W k)ᵀ) Z), ξ⟫ =
      if k = m then ⟪Z, ξ⟫ else 0 := fun k => by
    rw [(isOrthProj_modeProj k (hU k)).compl.symm, sub_apply,
      one_apply_eq_self]
    split_ifs with hkm
    · subst hkm
      rw [hξ, modeProj_tucker_update_eq_zero hUd, sub_zero, ← hξ, hsymm, hQ]
    · rw [hξ, modeProj_tucker_update_of_ne hkm (hU k), sub_self, inner_zero_right]
  simp only [tuckerTangentProj, add_apply, sum_apply,
    ContinuousLinearMap.comp_apply, mul_apply_eq_comp, tuckerCLM_apply,
    inner_sub_left, inner_add_left, sum_inner, h0, hk, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, zero_add, sub_self]

/-- **Tangent projector of a constrained Tucker manifold** (Bachmayr–Eisenmann–Uschmajew,
arXiv 2308.16720, Prop. 4.2, finite-dimensional): at `X = C ×ₖ Uₖ` with orthonormal `Uₖ`, an
orthogonal projector `P_C` onto the tangent space of the core manifold, and matrices `W_k`
whose columns span the co-range `Vᵏ` of `Mat_k(X)` (`W_k = Mat_{≠k}(X) B_k`) with
`W_k W_kᵀ` fixing `Mat_k(X)` (for instance an orthonormal basis of `Vᵏ`), the operator
`P_X = P_X⁰ + ∑ₖ P_Xᵏ` of (4.7)–(4.9) is the orthogonal projection onto the tangent space
`T_X ℳ` spanned by (4.5). -/
theorem tuckerTangentProj_eq_starProjection (hPC : IsOrthProj PC) {s : Fin d → Type*}
    [∀ k, Fintype (s k)] {W : ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s k) ℝ}
    (hWX : ∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U)
    (hWB : ∀ k, ∃ B : Matrix _ (s k) ℝ, W k = unfold (· ≠ k) (tucker C U) * B) :
    tuckerTangentProj U PC W = (tuckerTangentSpace U C PC).starProjection := by
  ext1 Z
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (Submodule.subset_span (tuckerTangentProj_mem_gen hU hPC hWB Z)) fun w hw => ?_
  induction hw using Submodule.span_induction with
  | mem ξ hξ =>
    obtain ⟨Cdot, hCd, Udot, hUd, rfl⟩ := hξ
    rw [inner_add_right, inner_sum, inner_sub_tuckerTangentProj_core hU hPC W Z hCd,
      Finset.sum_eq_zero fun k _ => inner_sub_tuckerTangentProj_update hU hWX Z (hUd k),
      add_zero]
  | zero => exact inner_zero_right _
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [real_inner_smul_right, hx, mul_zero]

/-- **Prop. 4.2, projector form**: `P_X` is an orthogonal projector. -/
theorem isOrthProj_tuckerTangentProj (hPC : IsOrthProj PC) {s : Fin d → Type*}
    [∀ k, Fintype (s k)] {W : ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s k) ℝ}
    (hWX : ∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U)
    (hWB : ∀ k, ∃ B : Matrix _ (s k) ℝ, W k = unfold (· ≠ k) (tucker C U) * B) :
    IsOrthProj (tuckerTangentProj U PC W) := by
  rw [tuckerTangentProj_eq_starProjection hU hPC hWX hWB]
  exact ⟨fun x => Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ x),
    fun x y => Submodule.inner_starProjection_left_eq_right _ x y⟩

/-- **Prop. 4.2, range form**: `P_X ξ = ξ` exactly for the tangent vectors. -/
theorem tuckerTangentProj_eq_self_iff (hPC : IsOrthProj PC) {s : Fin d → Type*}
    [∀ k, Fintype (s k)] {W : ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s k) ℝ}
    (hWX : ∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U)
    (hWB : ∀ k, ∃ B : Matrix _ (s k) ℝ, W k = unfold (· ≠ k) (tucker C U) * B) (ξ : Tensor ι) :
    tuckerTangentProj U PC W ξ = ξ ↔ ξ ∈ tuckerTangentSpace U C PC := by
  rw [tuckerTangentProj_eq_starProjection hU hPC hWX hWB]
  exact Submodule.starProjection_eq_self_iff

/-- The tangent vectors (4.5) already form the tangent space: every element of the span is of
the form `Ċ ×ₖ Uₖ + ∑ₖ C ×ₖ U̇ₖ ×_{j ≠ k} Uⱼ` (Thm 4.1(iii) describes `T_X ℳ` as the span). -/
theorem mem_tuckerTangentSpace_iff (hPC : IsOrthProj PC) {s : Fin d → Type*}
    [∀ k, Fintype (s k)] {W : ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s k) ℝ}
    (hWX : ∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U)
    (hWB : ∀ k, ∃ B : Matrix _ (s k) ℝ, W k = unfold (· ≠ k) (tucker C U) * B) (ξ : Tensor ι) :
    ξ ∈ tuckerTangentSpace U C PC ↔ ξ ∈ tuckerTangentGen U C PC := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  rw [← (tuckerTangentProj_eq_self_iff hU hPC hWX hWB ξ).2 h]
  exact tuckerTangentProj_mem_gen hU hPC hWB ξ

end Tangent

/-! ### Example -/

/-- Non-vacuity of `tuckerTangentProj_eq_starProjection`: one mode with a `1 × 1` basis, the
unconstrained Tucker case `P_C = 1`, and `W = 1`. -/
example : tuckerTangentProj (ι := fun _ : Fin 1 => Fin 1) (r := fun _ => Fin 1) (fun _ => 1) 1
      (fun _ => Matrix.of fun _ (_ : Fin 1) => (1 : ℝ)) =
    (tuckerTangentSpace (ι := fun _ : Fin 1 => Fin 1) (r := fun _ => Fin 1) (fun _ => 1)
      (WithLp.toLp 2 fun _ => 1) 1).starProjection := by
  have hX : tucker (ι := fun _ : Fin 1 => Fin 1) (WithLp.toLp 2 fun _ => (1 : ℝ))
      (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) = WithLp.toLp 2 fun _ => 1 := tucker_one _
  refine tuckerTangentProj_eq_starProjection (fun _ => by simp) IsOrthProj.one (fun k => ?_)
    fun k => ⟨Matrix.of fun _ _ => 1, ?_⟩
  · rw [hX]
    ext x
    simp [actOn_apply, Matrix.mul_apply]
  · rw [hX]
    have h : (Matrix.of fun _ _ => (1 : ℝ) : Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ) =
        unfold (ι := fun _ : Fin 1 => Fin 1) (· ≠ k) (WithLp.toLp 2 fun _ => 1) *
          (Matrix.of fun _ _ => 1 : Matrix ({j : Fin 1 // ¬ j ≠ k} → Fin 1) (Fin 1) ℝ) := by
      ext z i
      rw [Matrix.mul_apply]
      simp
    exact h

end LeanDLRA.Tensor
