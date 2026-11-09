import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.GaugeODE

/-!
# Results of arXiv 2107.09207: escape of spurious critical points on the low-rank manifold

Riemannian gradient descent for `f(Z) = ½‖Z − X‖²` on the manifold of rank-`r` matrices, in the
language of `LeanDLRA.tangentProj`.

* `IsRGDFixedPoint`, `tangentProj_sub_eq_zero_iff`, `lemma_2_4` (Lemma 2.4 / Def. 2.5): the
  fixed points of Riemannian GD on `cl(M_r)` are `Y = P X = X Q`, and for `X` of rank `r` with
  distinct singular values they are exactly the `2^r` partial sums of its SVD (`X` and `2^r − 1`
  spurious points).  For repeated singular values the partial sums of one fixed SVD do not
  exhaust the fixed points (`fixedPoint_not_partialSVD`).
* `IsRGDStep`, `example_1_1` (Example 1.1): for `X = diag(2,1,0)`, `r = 2`, `Z₀ = diag(2,0,1)`,
  the iterates are `diag(2,0,(1−α)^k) → diag(2,0,0)`, a spurious rank-one limit.
* `lemma_2_6`, `lemma_2_6_gradient` (Lemma 2.6): the factor equations for a flow `Ż = M`,
  a corollary of the Koch–Lubich equivalence already in `LeanDLRA.Matrix.GaugeODE`.

* `lemma_2_7_lower_bound`, `lemma_2_7_isUnit_det` (Lemma 2.7, a priori half only): for any solution
  of `Ṡ = −S + Uᵀ X U` with `X` positive semidefinite, `vᵀ S(t) v ≥ e^{−t} c ‖v‖²` whenever
  `vᵀ S(0) v ≥ c ‖v‖²`, so the core stays invertible.  The existence of the coupled flow
  `U̇ = P_U⊥ X U S⁻¹`, `Ṡ = −S + UᵀXU` for all `t ≥ 0` is **not** formalized.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2107_09207

section Fixed

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **Fixed points of Riemannian gradient descent on the closure of the rank-`r` manifold**
(arXiv 2107.09207, Def. 2.5, for `f(Z) = ½‖Z − X‖²`).  A matrix `Y` of rank `s ≤ r` is a fixed
point if, for an orthonormal factorization `Y = U S Vᵀ` (`Uᵀ U = 1`, `Vᵀ V = 1`, `S` invertible,
`U : m × k`, `V : n × k`, `#k = s ≤ r`), the Riemannian gradient vanishes,
`P(Y) (Y − X) = 0`, where `P(Y) = tangentProj U V` is the orthogonal projector onto the tangent
space of the manifold of rank-`s` matrices at `Y` (it depends only on `Y`, see
`tangentProj_eq_of_factorization`).  The rank-deficient case `s < r` is the case in which the
iteration sits on a lower stratum of `cl(M_r)`; `s = 0` (`Y = 0`) is allowed. -/
def IsRGDFixedPoint (r : ℕ) (X Y : Matrix m n ℝ) : Prop :=
  ∃ (k : Type) (_ : Fintype k) (_ : DecidableEq k) (U : Matrix m k ℝ) (S : Matrix k k ℝ)
    (V : Matrix n k ℝ), Fintype.card k ≤ r ∧ Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ IsUnit S.det ∧
      Y = U * S * Vᵀ ∧ tangentProj U V (Y - X) = 0

/-- **Projector form of the fixed-point equation** (arXiv 2107.09207, Lemma 2.4 / Def. 2.5: the
`P(Y)(Y − X) = 0 ⇔ Y = P X = X Q` step).  For `Y = U S Vᵀ` with `Uᵀ U = 1`, `Vᵀ V = 1`:
`P(Y) (Y − X) = 0` iff `U Uᵀ X = Y` and `X V Vᵀ = Y`, i.e. `Y = P X = X Q` for the orthogonal
projectors `P = U Uᵀ`, `Q = V Vᵀ` onto the column and row space of `Y`.  (`S` need not be
invertible for this equivalence.) -/
theorem tangentProj_sub_eq_zero_iff {k : Type*} [Fintype k] [DecidableEq k] {U : Matrix m k ℝ}
    {V : Matrix n k ℝ} {S : Matrix k k ℝ} {X : Matrix m n ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) :
    tangentProj U V (U * S * Vᵀ - X) = 0 ↔ U * Uᵀ * X = U * S * Vᵀ ∧ X * V * Vᵀ = U * S * Vᵀ := by
  have hPP : U * Uᵀ * (U * Uᵀ) = U * Uᵀ := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc U Uᵀ U, hU, Matrix.mul_one]
  have hQQ : V * Vᵀ * (V * Vᵀ) = V * Vᵀ := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc V Vᵀ V, hV, Matrix.mul_one]
  have hUU : U * Uᵀ * U = U := by rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  have hPY : U * Uᵀ * (U * S * Vᵀ) = U * S * Vᵀ := by
    calc U * Uᵀ * (U * S * Vᵀ) = (U * Uᵀ * U) * S * Vᵀ := by simp only [Matrix.mul_assoc]
      _ = U * S * Vᵀ := by rw [hUU]
  have hYQ : U * S * Vᵀ * (V * Vᵀ) = U * S * Vᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V Vᵀ, hV, Matrix.one_mul]
  rw [map_sub, tangentProj_mul_mul_transpose hU, sub_eq_zero, tangentProj_apply]
  set Y := U * S * Vᵀ with hY
  set P := U * Uᵀ with hP
  set Q := V * Vᵀ with hQ
  have e1 : U * Uᵀ * X = P * X := rfl
  have e2 : X * V * Vᵀ = X * Q := by rw [hQ, Matrix.mul_assoc]
  have e3 : U * Uᵀ * X * V * Vᵀ = P * X * Q := by rw [hP, hQ]; simp only [Matrix.mul_assoc]
  rw [e1, e2, e3]
  constructor
  · intro h
    have h1 : P * Y = P * X := by
      rw [h]
      simp only [Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc, hPP]
      abel
    have h2 : Y * Q = X * Q := by
      rw [h]
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, hQQ]
      abel
    exact ⟨by rw [← h1, hPY], by rw [← h2, hYQ]⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2, hYQ]
    abel


variable {r : ℕ}

/-- The matrix `∑_{i ∈ J} σ_i u_i v_iᵀ = U₀ diag(1_J σ) V₀ᵀ`: the part of the SVD
`U₀ diag(σ) V₀ᵀ` that keeps the singular triplets with index in `J`. -/
def partialSVD (U₀ : Matrix m (Fin r) ℝ) (σ : Fin r → ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (J : Finset (Fin r)) : Matrix m n ℝ :=
  U₀ * Matrix.diagonal (fun i => if i ∈ J then σ i else 0) * V₀ᵀ

omit [Fintype m] [Fintype n] in
lemma submatrix_mul_diag_mul_transpose (A : Matrix m (Fin r) ℝ) (B : Matrix n (Fin r) ℝ)
    (w : Fin r → ℝ) (J : Finset (Fin r)) :
    A.submatrix id (Subtype.val : J → Fin r) * Matrix.diagonal (fun j : J => w j) *
        (B.submatrix id (Subtype.val : J → Fin r))ᵀ =
      A * Matrix.diagonal (fun i => if i ∈ J then w i else 0) * Bᵀ := by
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.submatrix_apply, id]
  have h : ∀ i, A a i * (if i ∈ J then w i else 0) * B b i =
      if i ∈ J then A a i * w i * B b i else 0 := fun i => by split_ifs <;> simp
  simp_rw [h]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_coe_sort J (fun i => A a i * w i * B b i)]

lemma diag_ind_mul_diag (σ : Fin r → ℝ) (J : Finset (Fin r)) :
    Matrix.diagonal (fun i => if i ∈ J then (1 : ℝ) else 0) * Matrix.diagonal σ =
      Matrix.diagonal (fun i => if i ∈ J then σ i else 0) := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

lemma diag_mul_diag_ind (σ : Fin r → ℝ) (J : Finset (Fin r)) :
    Matrix.diagonal σ * Matrix.diagonal (fun i => if i ∈ J then (1 : ℝ) else 0) =
      Matrix.diagonal (fun i => if i ∈ J then σ i else 0) := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

/-- Every partial sum `∑_{i ∈ J} σ_i u_i v_iᵀ` of an SVD `X = U₀ diag(σ) V₀ᵀ` (any `J`, any
nonzero `σ`, no distinctness needed) is a fixed point of Riemannian GD for `f(Z) = ½‖Z − X‖²`
on `cl(M_r)` (arXiv 2107.09207, Lemma 2.4, "if" direction). -/
theorem isRGDFixedPoint_partialSVD {U₀ : Matrix m (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
    {σ : Fin r → ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hσ : ∀ i, σ i ≠ 0)
    (J : Finset (Fin r)) :
    IsRGDFixedPoint r (U₀ * Matrix.diagonal σ * V₀ᵀ) (partialSVD U₀ σ V₀ J) := by
  have hsub : (U₀.submatrix id (Subtype.val : J → Fin r))ᵀ *
      U₀.submatrix id (Subtype.val : J → Fin r) = 1 := by
    ext a b
    have := congrFun (congrFun hU₀ a.1) b.1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id,
      Matrix.one_apply, Subtype.ext_iff] at this ⊢
    exact this
  have hsubV : (V₀.submatrix id (Subtype.val : J → Fin r))ᵀ *
      V₀.submatrix id (Subtype.val : J → Fin r) = 1 := by
    ext a b
    have := congrFun (congrFun hV₀ a.1) b.1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id,
      Matrix.one_apply, Subtype.ext_iff] at this ⊢
    exact this
  have hY : partialSVD U₀ σ V₀ J = U₀.submatrix id (Subtype.val : J → Fin r) *
      Matrix.diagonal (fun j : J => σ j) * (V₀.submatrix id (Subtype.val : J → Fin r))ᵀ :=
    (submatrix_mul_diag_mul_transpose U₀ V₀ σ J).symm
  have hPU : U₀.submatrix id (Subtype.val : J → Fin r) *
      (U₀.submatrix id (Subtype.val : J → Fin r))ᵀ =
      U₀ * Matrix.diagonal (fun i => if i ∈ J then (1 : ℝ) else 0) * U₀ᵀ := by
    have := submatrix_mul_diag_mul_transpose U₀ U₀ (fun _ => 1) J
    simpa using this
  have hPV : V₀.submatrix id (Subtype.val : J → Fin r) *
      (V₀.submatrix id (Subtype.val : J → Fin r))ᵀ =
      V₀ * Matrix.diagonal (fun i => if i ∈ J then (1 : ℝ) else 0) * V₀ᵀ := by
    have := submatrix_mul_diag_mul_transpose V₀ V₀ (fun _ => 1) J
    simpa using this
  refine ⟨J, inferInstance, inferInstance, U₀.submatrix id (Subtype.val : J → Fin r),
    Matrix.diagonal (fun j : J => σ j), V₀.submatrix id (Subtype.val : J → Fin r), ?_,
    hsub, hsubV, ?_, hY, ?_⟩
  · simpa using Finset.card_le_univ J
  · rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun j _ => hσ j
  · rw [hY]
    refine (tangentProj_sub_eq_zero_iff hsub hsubV).2 ⟨?_, ?_⟩
    · rw [hPU, ← hY]
      unfold partialSVD
      calc _ = U₀ * Matrix.diagonal (fun i => if i ∈ J then (1 : ℝ) else 0) *
            (U₀ᵀ * U₀) * Matrix.diagonal σ * V₀ᵀ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU₀, Matrix.mul_one, Matrix.mul_assoc U₀, diag_ind_mul_diag]
    · rw [Matrix.mul_assoc, hPV, ← hY]
      unfold partialSVD
      calc _ = U₀ * Matrix.diagonal σ * (V₀ᵀ * V₀) *
            Matrix.diagonal (fun i => if i ∈ J then (1 : ℝ) else 0) * V₀ᵀ := by
              simp only [Matrix.mul_assoc]
        _ = _ := by rw [hV₀, Matrix.mul_one, Matrix.mul_assoc U₀, diag_mul_diag_ind]

omit [Fintype m] [Fintype n] in
lemma partialSVD_univ (U₀ : Matrix m (Fin r) ℝ) (σ : Fin r → ℝ) (V₀ : Matrix n (Fin r) ℝ) :
    partialSVD U₀ σ V₀ Finset.univ = U₀ * Matrix.diagonal σ * V₀ᵀ := by
  simp [partialSVD]

lemma partialSVD_inj_aux {U₀ : Matrix m (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
    {σ : Fin r → ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (J : Finset (Fin r)) :
    U₀ᵀ * partialSVD U₀ σ V₀ J * V₀ =
      Matrix.diagonal (fun i => if i ∈ J then σ i else 0) := by
  unfold partialSVD
  calc _ = (U₀ᵀ * U₀) * Matrix.diagonal (fun i => if i ∈ J then σ i else 0) * (V₀ᵀ * V₀) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU₀, hV₀, Matrix.one_mul, Matrix.mul_one]

/-- Distinct index sets give distinct partial sums, for a positive spectrum (part of the count
in arXiv 2107.09207, Lemma 2.4). -/
theorem partialSVD_injective {U₀ : Matrix m (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
    {σ : Fin r → ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hσ : ∀ i, 0 < σ i) :
    Function.Injective (partialSVD U₀ σ V₀) := by
  intro J J' h
  have := partialSVD_inj_aux (σ := σ) hU₀ hV₀ J
  rw [h, partialSVD_inj_aux hU₀ hV₀ J'] at this
  have h2 := Matrix.diagonal_injective this
  ext i
  have := congrFun h2 i
  have hi := hσ i
  by_cases hJ : i ∈ J <;> by_cases hJ' : i ∈ J' <;> simp_all

/-- **Classification of fixed points** (arXiv 2107.09207, Lemma 2.4, "only if" direction).
Let `X = U₀ diag(σ) V₀ᵀ` with orthonormal `U₀`, `V₀` and **pairwise distinct** positive `σ`.
Every fixed point `Y` of Riemannian GD on `cl(M_r)` is a partial sum
`∑_{i ∈ J} σ_i u_i v_iᵀ` of the SVD of `X`.  The distinctness of the singular values is needed
(`fixedPoint_not_partialSVD`: for `X = I₂` a non-diagonal rank-one projector is a fixed point);
the paper assumes it for part 2) of Lemma 2.4 (the count), not for part 1). -/
theorem exists_partialSVD_of_isRGDFixedPoint {U₀ : Matrix m (Fin r) ℝ}
    {V₀ : Matrix n (Fin r) ℝ} {σ : Fin r → ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    (hσ : ∀ i, 0 < σ i) (hinj : Function.Injective σ) {Y : Matrix m n ℝ}
    (h : IsRGDFixedPoint r (U₀ * Matrix.diagonal σ * V₀ᵀ) Y) :
    ∃ J : Finset (Fin r), Y = partialSVD U₀ σ V₀ J := by
  obtain ⟨k, _, _, U, S, V, -, hU, hV, -, rfl, hP⟩ := h
  rw [tangentProj_sub_eq_zero_iff hU hV] at hP
  obtain ⟨h1, h2⟩ := hP
  have hPt : (U * Uᵀ)ᵀ = U * Uᵀ := by simp [Matrix.transpose_mul]
  have hQt : (V * Vᵀ)ᵀ = V * Vᵀ := by simp [Matrix.transpose_mul]
  have hPP : U * Uᵀ * (U * Uᵀ) = U * Uᵀ := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc U Uᵀ U, hU, Matrix.mul_one]
  rw [Matrix.mul_assoc] at h2
  generalize hX : U₀ * Matrix.diagonal σ * V₀ᵀ = X at h1 h2
  generalize U * Uᵀ = P at hPt hPP h1
  generalize V * Vᵀ = Q at hQt h2
  have hPXQ : P * X = X * Q := h1.trans h2.symm
  have hXtP : Xᵀ * P = Q * Xᵀ := by
    have := congrArg Matrix.transpose hPXQ
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, hPt, hQt] at this
  have hcomm : P * (X * Xᵀ) = (X * Xᵀ) * P := by
    calc P * (X * Xᵀ) = (P * X) * Xᵀ := by rw [Matrix.mul_assoc]
      _ = X * (Q * Xᵀ) := by rw [hPXQ, Matrix.mul_assoc]
      _ = X * (Xᵀ * P) := by rw [hXtP]
      _ = _ := by rw [Matrix.mul_assoc]
  set D := Matrix.diagonal σ with hD
  set D2 := Matrix.diagonal (fun i => σ i * σ i) with hD2
  have hDD : D * D = D2 := by rw [hD, hD2, Matrix.diagonal_mul_diagonal]
  have hXX : X * Xᵀ = U₀ * D2 * U₀ᵀ := by
    calc X * Xᵀ = U₀ * D * (V₀ᵀ * V₀) * D * U₀ᵀ := by
          rw [← hX]; simp [Matrix.transpose_mul, hD, Matrix.mul_assoc]
      _ = U₀ * (D * D) * U₀ᵀ := by rw [hV₀, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hDD]
  have hXXU : X * Xᵀ * U₀ = U₀ * D2 := by
    rw [hXX, Matrix.mul_assoc, Matrix.mul_assoc, hU₀, Matrix.mul_one]
  set M := U₀ᵀ * P * U₀ with hM
  have hPUD : P * U₀ * D2 = U₀ * D2 * M := by
    calc P * U₀ * D2 = P * (X * Xᵀ * U₀) := by rw [hXXU, Matrix.mul_assoc]
      _ = (X * Xᵀ) * P * U₀ := by rw [← Matrix.mul_assoc P (X * Xᵀ) U₀, hcomm]
      _ = _ := by rw [hXX]; simp only [hM, Matrix.mul_assoc]
  have hMD : M * D2 = D2 * M := by
    calc M * D2 = U₀ᵀ * (P * U₀ * D2) := by rw [hM]; simp only [Matrix.mul_assoc]
      _ = U₀ᵀ * U₀ * (D2 * M) := by rw [hPUD]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU₀, Matrix.one_mul]
  have hMoff : ∀ l j, l ≠ j → M l j = 0 := by
    intro l j hlj
    have h0 := congrFun (congrFun hMD l) j
    rw [hD2, Matrix.mul_diagonal, Matrix.diagonal_mul] at h0
    have hne : σ j * σ j - σ l * σ l ≠ 0 := by
      intro h3
      have h4 : σ j = σ l := (mul_self_inj (hσ j).le (hσ l).le).1 (by linarith)
      exact hlj (hinj h4).symm
    have h5 : M l j * (σ j * σ j - σ l * σ l) = 0 := by linarith
    exact (mul_eq_zero.1 h5).resolve_right hne
  set μ : Fin r → ℝ := fun i => M i i with hμ
  have hMdiag : M = Matrix.diagonal μ := by
    ext l j
    by_cases hlj : l = j
    · subst hlj; simp [hμ]
    · simp [Matrix.diagonal_apply_ne _ hlj, hMoff l j hlj]
  have hDinv : D2 * Matrix.diagonal (fun i => (σ i * σ i)⁻¹) = 1 := by
    rw [hD2, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (mul_self_ne_zero.2 (hσ i).ne')
  have hPU₀ : P * U₀ = U₀ * Matrix.diagonal μ := by
    have h3 : P * U₀ * D2 = U₀ * Matrix.diagonal μ * D2 := by
      rw [hPUD, hMdiag, Matrix.mul_assoc, Matrix.mul_assoc, hD2, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_mul_diagonal]
      congr 2
      funext i
      ring
    calc P * U₀ = P * U₀ * D2 * Matrix.diagonal (fun i => (σ i * σ i)⁻¹) := by
          rw [Matrix.mul_assoc _ D2, hDinv, Matrix.mul_one]
      _ = U₀ * Matrix.diagonal μ * D2 * Matrix.diagonal (fun i => (σ i * σ i)⁻¹) := by rw [h3]
      _ = U₀ * Matrix.diagonal μ := by rw [Matrix.mul_assoc _ D2, hDinv, Matrix.mul_one]
  have hid : Matrix.diagonal μ * Matrix.diagonal μ = Matrix.diagonal μ := by
    have h3 : P * (P * U₀) = P * U₀ := by rw [← Matrix.mul_assoc, hPP]
    rw [hPU₀, ← Matrix.mul_assoc P U₀, hPU₀, Matrix.mul_assoc] at h3
    have h4 := congrArg (fun A => U₀ᵀ * A) h3
    simp only [← Matrix.mul_assoc, hU₀, Matrix.one_mul] at h4
    exact h4
  have hμ01 : ∀ i, μ i = 0 ∨ μ i = 1 := by
    intro i
    rw [Matrix.diagonal_mul_diagonal] at hid
    have h5 := congrFun (Matrix.diagonal_injective hid) i
    have : μ i * (μ i - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  refine ⟨Finset.univ.filter (fun i => μ i = 1), ?_⟩
  have hdiagμ : Matrix.diagonal μ =
      Matrix.diagonal
        (fun i => if i ∈ Finset.univ.filter (fun i => μ i = 1) then (1 : ℝ) else 0) := by
    congr 1
    funext i
    rcases hμ01 i with h | h <;> simp [h]
  rw [← h1, ← hX, partialSVD, ← diag_ind_mul_diag, ← hdiagμ]
  calc P * (U₀ * D * V₀ᵀ) = P * U₀ * D * V₀ᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hPU₀]; simp only [Matrix.mul_assoc, hD]

/-- **Lemma 2.4 / Def. 2.5** (arXiv 2107.09207).  Let `f(Z) = ½‖Z − X‖²` with
`X = U₀ diag(σ) V₀ᵀ` of rank `r` (orthonormal `U₀ : m × r`, `V₀ : n × r`, `σ_i > 0`) with
pairwise distinct singular values.  Then
* the fixed points of Riemannian GD on `cl(M_r)` (`IsRGDFixedPoint`) are exactly the
  `2^r` partial sums `∑_{i∈J} σ_i u_i v_iᵀ`, `J ⊆ {1..r}` (`J = univ` gives `X`);
* the map `J ↦ ∑_{i∈J} σ_i u_i v_iᵀ` is injective;
* hence there are exactly `2^r − 1` fixed points different from `X` (the spurious ones, which
  keep a proper subset of the singular triplets).

Differences from the paper: real matrices only; part 1) (the classification) is proved under the
distinctness of the singular values that the paper assumes only for part 2) (the count), and for
one fixed SVD it fails without it (`fixedPoint_not_partialSVD`); "fixed point of Riemannian GD" is
formalised as vanishing of the Riemannian gradient `P(Y)(Y − X)` at `Y`, the projector being
taken on the stratum of rank `s = rank Y` (see `IsRGDFixedPoint`).  The projector form
`P(Y)(Y − X) = 0 ⇔ Y = P X = X Q` is `tangentProj_sub_eq_zero_iff`. -/
theorem lemma_2_4 {U₀ : Matrix m (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {σ : Fin r → ℝ}
    {X : Matrix m n ℝ} (hX : X = U₀ * Matrix.diagonal σ * V₀ᵀ) (hU₀ : U₀ᵀ * U₀ = 1)
    (hV₀ : V₀ᵀ * V₀ = 1) (hσ : ∀ i, 0 < σ i) (hinj : Function.Injective σ) :
    (∀ Y, IsRGDFixedPoint r X Y ↔ ∃ J : Finset (Fin r), Y = partialSVD U₀ σ V₀ J) ∧
      Function.Injective (partialSVD U₀ σ V₀) ∧ partialSVD U₀ σ V₀ Finset.univ = X ∧
      {Y | IsRGDFixedPoint r X Y ∧ Y ≠ X}.ncard = 2 ^ r - 1 := by
  subst hX
  have hchar : ∀ Y, IsRGDFixedPoint r (U₀ * Matrix.diagonal σ * V₀ᵀ) Y ↔
      ∃ J : Finset (Fin r), Y = partialSVD U₀ σ V₀ J := fun Y =>
    ⟨exists_partialSVD_of_isRGDFixedPoint hU₀ hV₀ hσ hinj, by
      rintro ⟨J, rfl⟩
      exact isRGDFixedPoint_partialSVD hU₀ hV₀ (fun i => (hσ i).ne') J⟩
  have hinjJ := partialSVD_injective hU₀ hV₀ hσ
  refine ⟨hchar, hinjJ, partialSVD_univ _ _ _, ?_⟩
  have hset : {Y | IsRGDFixedPoint r (U₀ * Matrix.diagonal σ * V₀ᵀ) Y ∧
      Y ≠ U₀ * Matrix.diagonal σ * V₀ᵀ} =
      partialSVD U₀ σ V₀ '' {J : Finset (Fin r) | J ≠ Finset.univ} := by
    ext Y
    simp only [Set.mem_ofPred_eq, Set.mem_image, hchar]
    constructor
    · rintro ⟨⟨J, rfl⟩, hne⟩
      exact ⟨J, fun h => hne (by rw [h, partialSVD_univ]), rfl⟩
    · rintro ⟨J, hJ, rfl⟩
      refine ⟨⟨J, rfl⟩, fun h => hJ ?_⟩
      exact hinjJ (h.trans (partialSVD_univ _ _ _).symm)
  rw [hset, Set.ncard_image_of_injective _ hinjJ]
  have : {J : Finset (Fin r) | J ≠ Finset.univ} = Set.univ \ {Finset.univ} := by
    ext J; simp
  rw [this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin]

/-- The unit vector `u = (3/5, 4/5)` as a `2 × 1` matrix. -/
noncomputable def u35 : Matrix (Fin 2) (Fin 1) ℝ := !![3 / 5; 4 / 5]

lemma u35_orth : u35ᵀ * u35 = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [u35, Matrix.mul_apply]
  norm_num

/-- **The distinctness hypothesis of Lemma 2.4 cannot be dropped** (arXiv 2107.09207).  For
`X = I₂ = 1 · diag(1, 1) · 1ᵀ` and `r = 2`, the rank-one projector `Y = u uᵀ`, `u = (3/5, 4/5)`,
is a fixed point of Riemannian GD on `cl(M₂)`, but it is not a partial sum of this SVD of `X`
(those are diagonal).  So part 1) of Lemma 2.4, read for one fixed SVD, needs distinct singular
values. -/
theorem fixedPoint_not_partialSVD :
    IsRGDFixedPoint 2 (1 : Matrix (Fin 2) (Fin 2) ℝ) (u35 * u35ᵀ) ∧
      ∀ J : Finset (Fin 2), u35 * u35ᵀ ≠ partialSVD 1 (fun _ => (1 : ℝ)) 1 J := by
  refine ⟨⟨Fin 1, inferInstance, inferInstance, u35, 1, u35, by simp, u35_orth, u35_orth,
    by simp, by rw [Matrix.mul_one], ?_⟩, fun J h => ?_⟩
  · have h := (tangentProj_sub_eq_zero_iff (S := 1) (X := 1) u35_orth u35_orth).2
      ⟨by simp, by simp⟩
    simpa using h
  · have h01 := congrFun (congrFun h 0) 1
    simp [partialSVD, u35, Matrix.mul_apply] at h01

end Fixed

section Example

variable {m n : Type*} [Fintype m] [Fintype n]

/-- One step of Riemannian gradient descent with step size `α` for `f(Z) = ½‖Z − X‖²` on the
manifold of rank-`r` matrices: `Z = U S Vᵀ` (orthonormal `U`, `V`, invertible `S`) is moved along
the Riemannian gradient `P(Z)(Z − X)` (`P(Z) = tangentProj U V`) and mapped back to the
manifold by the truncated SVD, i.e. `Z'` is a best rank-`≤ r` approximation (Frobenius norm) of
`Z − α P(Z)(Z − X)`.  Any best approximation is allowed (no tie-breaking). -/
def IsRGDStep (r : ℕ) (X : Matrix m n ℝ) (α : ℝ) (Z Z' : Matrix m n ℝ) : Prop :=
  ∃ (U : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (V : Matrix n (Fin r) ℝ),
    Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ IsUnit S.det ∧ Z = U * S * Vᵀ ∧
    Z'.rank ≤ r ∧ ∀ Y : Matrix m n ℝ, Y.rank ≤ r →
      ‖Z - α • tangentProj U V (Z - X) - Z'‖ ≤ ‖Z - α • tangentProj U V (Z - X) - Y‖

end Example

/-- The matrix `X = diag(2,1,0)` of Example 1.1. -/
def X₀ : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![2, 1, 0]

/-- The iterates `diag(2, 0, t)`. -/
def Zt (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![2, 0, t]

/-- Orthonormal frame `[e₁ e₃]`. -/
def F13 : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 0; 0, 1]

lemma F13_orth : F13ᵀ * F13 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply] <;> simp [F13, Fin.sum_univ_succ]

lemma Zt_factor (t : ℝ) : Zt t = F13 * Matrix.diagonal ![2, t] * F13ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply] <;>
    simp [Zt, F13, Fin.sum_univ_succ, Matrix.diagonal_apply]

lemma tangent_Zt {t : ℝ} (α : ℝ) :
    Zt t - α • tangentProj F13 F13 (Zt t - X₀) = Zt ((1 - α) * t) := by
  rw [tangentProj_apply]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  all_goals simp [Zt, X₀, F13, Fin.sum_univ_succ, Matrix.diagonal_apply]
  ring

lemma rank_Zt_le (t : ℝ) : (Zt t).rank ≤ 2 := by
  rw [Zt_factor]
  refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans ?_)
  exact (Matrix.rank_le_width _).trans (by simp)

/-- Orthonormal frame `[e₁ e₂]`. -/
def F12 : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; 0, 0]

lemma F12_orth : F12ᵀ * F12 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply] <;> simp [F12, Fin.sum_univ_succ]

lemma X₀_eq : X₀ = F12 * Matrix.diagonal (![2, 1] : Fin 2 → ℝ) * F12ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply] <;>
    simp [X₀, F12, Fin.sum_univ_succ, Matrix.diagonal_apply]

lemma Zt_zero_eq : Zt 0 = partialSVD F12 (![2, 1] : Fin 2 → ℝ) F12 {0} := by
  unfold partialSVD
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply] <;>
    simp [Zt, F12, Matrix.diagonal_apply]

/-- `diag(2,0,0)` is a (spurious) fixed point for `X = diag(2,1,0)`, `r = 2`. -/
lemma X₀_spurious : IsRGDFixedPoint 2 X₀ (Zt 0) := by
  rw [Zt_zero_eq, X₀_eq]
  exact isRGDFixedPoint_partialSVD F12_orth F12_orth (by intro i; fin_cases i <;> simp) {0}

/-- Non-vacuity of Lemma 2.4: its hypotheses hold for `X = diag(2,1,0)`, `r = 2`, so that
`X` has exactly `3` spurious fixed points. -/
example : {Y | IsRGDFixedPoint 2 X₀ Y ∧ Y ≠ X₀}.ncard = 2 ^ 2 - 1 :=
  (lemma_2_4 X₀_eq F12_orth F12_orth (by intro i; fin_cases i <;> simp)
    (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all)).2.2.2

lemma isUnit_det_diag {t : ℝ} (ht : 0 < t) :
    IsUnit (Matrix.diagonal ![2, t] : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
  simp [Fin.prod_univ_two, ht.ne']

lemma continuous_Zt : Continuous Zt := by
  unfold Zt
  refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
  fin_cases i
  · exact continuous_const
  · exact continuous_const
  · exact continuous_id

lemma isRGDStep_Zt {t : ℝ} (ht : 0 < t) (α : ℝ) :
    IsRGDStep 2 X₀ α (Zt t) (Zt ((1 - α) * t)) := by
  refine ⟨F13, Matrix.diagonal ![2, t], F13, F13_orth, F13_orth, isUnit_det_diag ht,
    Zt_factor t, rank_Zt_le _, fun Y _ => ?_⟩
  rw [tangent_Zt, sub_self, norm_zero]
  exact norm_nonneg _

lemma eq_of_isRGDStep_Zt {t : ℝ} (ht : 0 < t) {α : ℝ} {Z' : Matrix (Fin 3) (Fin 3) ℝ}
    (h : IsRGDStep 2 X₀ α (Zt t) Z') : Z' = Zt ((1 - α) * t) := by
  obtain ⟨U, S, V, hU, hV, hS, hZ, hr, hmin⟩ := h
  have hP : tangentProj U V = tangentProj F13 F13 :=
    tangentProj_eq_of_factorization hU hV hS F13_orth F13_orth (isUnit_det_diag ht)
      (hZ.symm.trans (Zt_factor t))
  have := hmin _ (rank_Zt_le ((1 - α) * t))
  rw [hP, tangent_Zt, sub_self, norm_zero] at this
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 this)).symm

/-- **Example 1.1** (arXiv 2107.09207).  `X = diag(2,1,0)`, `r = 2`, `Z₀ = diag(2,0,1)`,
step size `α ∈ (0,1)` (so that all iterates keep rank `2`).
* The sequence `Z_k = diag(2, 0, (1−α)^k)` is an orbit of Riemannian GD with truncated-SVD
  retraction (first conjunct), and it is the only one starting at `Z₀` (`z k = Zt ((1-α)^k)`).
* It converges to `diag(2,0,0)`, which has rank `1`, differs from `X`, and is a fixed point of
  Riemannian GD on `cl(M₂)` (a spurious limit in the sense of Lemma 2.4).

The retraction is the one of Def. 2.3 (a best approximation in `cl(M₂)`, any minimizer
allowed); here the gradient step `Z_k − α P(Z_k)(Z_k − X)` already has rank `2`, so every
retraction that fixes `M₂` gives the same iterates.  The step size range `α ∈ (0,1)` is the
paper's; it is where `(1−α)^k > 0`. -/
theorem example_1_1 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ k : ℕ, IsRGDStep 2 X₀ α (Zt ((1 - α) ^ k)) (Zt ((1 - α) ^ (k + 1)))) ∧
    ∀ z : ℕ → Matrix (Fin 3) (Fin 3) ℝ, z 0 = Zt 1 →
      (∀ k, IsRGDStep 2 X₀ α (z k) (z (k + 1))) →
      (∀ k, z k = Zt ((1 - α) ^ k)) ∧ Tendsto z atTop (𝓝 (Zt 0)) ∧
        (Zt 0).rank = 1 ∧ Zt 0 ≠ X₀ ∧ IsRGDFixedPoint 2 X₀ (Zt 0) := by
  have hpos : ∀ k : ℕ, 0 < (1 - α) ^ k := fun k => pow_pos (by linarith) k
  refine ⟨fun k => ?_, fun z hz0 hz => ?_⟩
  · have := isRGDStep_Zt (hpos k) α
    rwa [← pow_succ'] at this
  · have hzk : ∀ k, z k = Zt ((1 - α) ^ k) := by
      intro k
      induction k with
      | zero => simpa using hz0
      | succ k ih =>
        have := eq_of_isRGDStep_Zt (hpos k) (ih ▸ hz k)
        rw [this, pow_succ']
    refine ⟨hzk, ?_, ?_, ?_, X₀_spurious⟩
    · have h1 : Tendsto (fun k : ℕ => (1 - α) ^ k) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
      have := (continuous_Zt.tendsto 0).comp h1
      rw [show z = fun k => Zt ((1 - α) ^ k) from funext hzk]
      exact this
    · rw [Zt, Matrix.rank_diagonal, Fintype.card_subtype, Finset.card_eq_one]
      exact ⟨0, by ext i; fin_cases i <;> simp⟩
    · intro h
      have := congrFun (congrFun h 1) 1
      simp [Zt, X₀] at this


section Gauge

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n]
  [DecidableEq r]

/-- **Lemma 2.6** (arXiv 2107.09207; Koch–Lubich, Prop. 2.1), pointwise form for a *tangent*
velocity.  Let `Z(t) = U(t) S(t) V(t)ᵀ` with `U`, `S`, `V` differentiable at `t`, orthonormal
`U(t)`, `V(t)`, invertible `S(t)` and the gauge conditions `U(t)ᵀ U̇ = 0`, `V(t)ᵀ V̇ = 0`
(equivalently `U̇ᵀ U = V̇ᵀ V = 0`).  If `M` is tangent to the rank-`r` manifold at `Z(t)`
(`P(Z) M = M`, which is automatic for the Riemannian gradient `−P(Z)(Z − X)`), then
`Ż = M` iff `U̇ = (1 − U Uᵀ) M V S⁻¹`, `V̇ = (1 − V Vᵀ) Mᵀ U S⁻ᵀ`, `Ṡ = Uᵀ M V`.

This is a corollary of the library's `hasDerivAt_factorProduct_tangentProj_iff_factorODE`
(the general form with `Ż = P(Z) M` for arbitrary `M`); tangency of `M` is needed because the
right-hand sides of the factor equations only see `P(Z) M`.  As in the paper's source
(Koch–Lubich), existence/uniqueness and smoothness of the factor path along a given flow are
not part of the statement. -/
theorem lemma_2_6 {U : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix n r ℝ}
    {U' : Matrix m r ℝ} {S' : Matrix r r ℝ} {V' : Matrix n r ℝ} {M : Matrix m n ℝ} {t : ℝ}
    (hU : HasDerivAt U U' t) (hS : HasDerivAt S S' t) (hV : HasDerivAt V V' t)
    (hUo : (U t)ᵀ * U t = 1) (hVo : (V t)ᵀ * V t = 1) (hdet : IsUnit (S t).det)
    (hgU : (U t)ᵀ * U' = 0) (hgV : (V t)ᵀ * V' = 0) (hM : tangentProj (U t) (V t) M = M) :
    HasDerivAt (fun t => U t * S t * (V t)ᵀ) M t ↔
      U' = (1 - U t * (U t)ᵀ) * M * V t * (S t)⁻¹ ∧ S' = (U t)ᵀ * M * V t ∧
        V' = (1 - V t * (V t)ᵀ) * Mᵀ * U t * ((S t)⁻¹)ᵀ := by
  have := hasDerivAt_factorProduct_tangentProj_iff_factorODE (Ad := M) hU hS hV hUo hVo hdet
    hgU hgV
  rwa [hM] at this

/-- **Lemma 2.6, gradient-flow form** (arXiv 2107.09207): for `Z = U S Vᵀ` as in `lemma_2_6`,
the Riemannian gradient flow `Ż = −P(Z)(Z − X)` of `f(Z) = ½‖Z − X‖²` is equivalent to
`U̇ = (1 − U Uᵀ)(X − Z) V S⁻¹`, `V̇ = (1 − V Vᵀ)(X − Z)ᵀ U S⁻ᵀ`, `Ṡ = Uᵀ (X − Z) V`
(`Z = U S Vᵀ`).  No tangency hypothesis is needed since `−P(Z)(Z−X) = P(Z)(X − Z)`. -/
theorem lemma_2_6_gradient {U : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix n r ℝ}
    {U' : Matrix m r ℝ} {S' : Matrix r r ℝ} {V' : Matrix n r ℝ} {X : Matrix m n ℝ} {t : ℝ}
    (hU : HasDerivAt U U' t) (hS : HasDerivAt S S' t) (hV : HasDerivAt V V' t)
    (hUo : (U t)ᵀ * U t = 1) (hVo : (V t)ᵀ * V t = 1) (hdet : IsUnit (S t).det)
    (hgU : (U t)ᵀ * U' = 0) (hgV : (V t)ᵀ * V' = 0) :
    HasDerivAt (fun t => U t * S t * (V t)ᵀ)
        (-(tangentProj (U t) (V t) (U t * S t * (V t)ᵀ - X))) t ↔
      U' = (1 - U t * (U t)ᵀ) * (X - U t * S t * (V t)ᵀ) * V t * (S t)⁻¹ ∧
        S' = (U t)ᵀ * (X - U t * S t * (V t)ᵀ) * V t ∧
        V' = (1 - V t * (V t)ᵀ) * (X - U t * S t * (V t)ᵀ)ᵀ * U t * ((S t)⁻¹)ᵀ := by
  have := hasDerivAt_factorProduct_tangentProj_iff_factorODE
    (Ad := X - U t * S t * (V t)ᵀ) hU hS hV hUo hVo hdet hgU hgV
  have h : tangentProj (U t) (V t) (X - U t * S t * (V t)ᵀ) =
      -(tangentProj (U t) (V t) (U t * S t * (V t)ᵀ - X)) := by
    rw [← map_neg, neg_sub]
  rwa [h] at this

end Gauge

section Lemma27

variable {n r : Type*} [Fintype n] [Fintype r]

/-- The quadratic form `M ↦ vᵀ M v` as a continuous linear functional. -/
noncomputable def quadForm (v : r → ℝ) : Matrix r r ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => v ⬝ᵥ (M *ᵥ v)
      map_add' := fun M N => by simp [Matrix.add_mulVec, dotProduct_add]
      map_smul' := fun a M => by simp [Matrix.smul_mulVec, dotProduct_smul] }

lemma quadForm_apply (v : r → ℝ) (M : Matrix r r ℝ) : quadForm v M = v ⬝ᵥ (M *ᵥ v) := rfl

/-- **Lemma 2.7, lower bound on the core (arXiv 2107.09207).**  Let `X` be symmetric positive
semidefinite (the SPSD setting of the paper; its proof uses `X ⪰ 0`) and let
`U : ℝ → ℝ^{n × r}`, `S : ℝ → ℝ^{r × r}` be such that on `[0, T]` the core satisfies
`Ṡ = −S + Uᵀ X U` (right derivatives on `[0, T)`, continuity on `[0, T]`).  If
`vᵀ S(0) v ≥ c ‖v‖²` for all `v` (i.e. `c ≤ λ_min(S(0))` for symmetric `S(0)`), then for all
`t ∈ [0, T]` and all `v`,
`vᵀ S(t) v ≥ e^{−t} c ‖v‖²`, i.e. `λ_min(S(t)) ≥ e^{−t} λ_min(S(0))` for symmetric `S`.
(Variation of constants: `e^t S(t) − S(0) = ∫₀ᵗ e^s Uᵀ X U ds ⪰ 0`.)

**This is only the a priori half of Lemma 2.7.**  It holds for every solution of the core
equation, whatever the path `U(t)` is (no orthonormality or `U̇` equation is used).  The other half
of the lemma, existence of the solution of the coupled system `U̇ = P_U⊥ X U S⁻¹`,
`Ṡ = −S + UᵀXU` for **all** `t ≥ 0` (a continuation argument for a field that is not globally
Lipschitz), is *not* formalized here. -/
theorem lemma_2_7_lower_bound {X : Matrix n n ℝ} (hX : X.PosSemidef)
    {U : ℝ → Matrix n r ℝ} {S : ℝ → Matrix r r ℝ} {T c : ℝ}
    (hSc : ContinuousOn S (Icc 0 T))
    (hS : ∀ t ∈ Ico 0 T, HasDerivWithinAt S (-S t + (U t)ᵀ * X * U t) (Ici t) t)
    (hc : ∀ v : r → ℝ, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S 0 *ᵥ v)) :
    ∀ t ∈ Icc 0 T, ∀ v : r → ℝ, Real.exp (-t) * c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S t *ᵥ v) := by
  intro t ht v
  have hq : ∀ s ∈ Ico 0 T, 0 ≤ quadForm v ((U s)ᵀ * X * U s) := by
    intro s _
    have h := hX.dotProduct_mulVec_nonneg (U s *ᵥ v)
    rw [star_trivial] at h
    rw [quadForm_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
    exact h
  have hd : ∀ s ∈ Ico 0 T, HasDerivWithinAt (fun s => Real.exp s * quadForm v (S s))
      (Real.exp s * quadForm v ((U s)ᵀ * X * U s)) (Ici s) s := by
    intro s hs
    have h1 := (Real.hasDerivAt_exp s).hasDerivWithinAt (s := Ici s)
    have h2 := (quadForm v).hasFDerivAt.comp_hasDerivWithinAt s (hS s hs)
    refine (h1.mul h2).congr_deriv ?_
    simp only [Function.comp_apply, map_add, map_neg]
    ring
  have hB := image_le_of_deriv_right_le_deriv_boundary
    (f := fun s => -(Real.exp s * quadForm v (S s)))
    (f' := fun s => -(Real.exp s * quadForm v ((U s)ᵀ * X * U s))) (a := 0) (b := T)
    (B := fun _ => -(quadForm v (S 0))) (B' := fun _ => 0)
    ((Real.continuous_exp.continuousOn.mul ((quadForm v).continuous.comp_continuousOn hSc)).neg)
    (fun s hs => (hd s hs).neg)
    (by simp) continuousOn_const (fun s _ => hasDerivWithinAt_const _ _ _)
    (fun s hs => by
      have := mul_nonneg (Real.exp_pos s).le (hq s hs)
      linarith)
  have := hB ht
  have h3 : quadForm v (S 0) ≤ Real.exp t * quadForm v (S t) := by linarith
  have h4 : c * (v ⬝ᵥ v) ≤ quadForm v (S 0) := hc v
  have he : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (-t)
  calc Real.exp (-t) * c * (v ⬝ᵥ v) = Real.exp (-t) * (c * (v ⬝ᵥ v)) := by ring
    _ ≤ Real.exp (-t) * quadForm v (S 0) := mul_le_mul_of_nonneg_left h4 hpos.le
    _ ≤ Real.exp (-t) * (Real.exp t * quadForm v (S t)) := mul_le_mul_of_nonneg_left h3 hpos.le
    _ = quadForm v (S t) := by rw [← mul_assoc, he, one_mul]

/-- **Lemma 2.7, the rank never drops in finite time (arXiv 2107.09207).**  Under the hypotheses of
`lemma_2_7_lower_bound` with `c > 0` (e.g. `S(0)` symmetric positive definite and `c = λ_min`),
`S(t)` is invertible for every `t ∈ [0, T]`.  As for `lemma_2_7_lower_bound`, this is the a priori
half of Lemma 2.7 only; global existence of the coupled flow is not formalized. -/
theorem lemma_2_7_isUnit_det [DecidableEq r] {X : Matrix n n ℝ} (hX : X.PosSemidef)
    {U : ℝ → Matrix n r ℝ} {S : ℝ → Matrix r r ℝ} {T c : ℝ} (hc0 : 0 < c)
    (hSc : ContinuousOn S (Icc 0 T))
    (hS : ∀ t ∈ Ico 0 T, HasDerivWithinAt S (-S t + (U t)ᵀ * X * U t) (Ici t) t)
    (hc : ∀ v : r → ℝ, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S 0 *ᵥ v)) :
    ∀ t ∈ Icc 0 T, IsUnit (S t).det := by
  intro t ht
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro a b hab
  have h0 : S t *ᵥ (a - b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
  have h1 := lemma_2_7_lower_bound hX hSc hS hc t ht (a - b)
  rw [h0, dotProduct_zero] at h1
  have hpos : 0 < Real.exp (-t) * c := mul_pos (Real.exp_pos _) hc0
  have h2 : (a - b) ⬝ᵥ (a - b) ≤ 0 := by
    by_contra hcon
    linarith [mul_pos hpos (not_le.1 hcon)]
  have h3 : 0 ≤ (a - b) ⬝ᵥ (a - b) := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 (le_antisymm h2 h3))

end Lemma27

end LeanDLRA.Literature.P2107_09207
