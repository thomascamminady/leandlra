import Mathlib
import LeanDLRA.LinearAlgebra.LowRank.Defs

/-!
# Orthonormal bases capturing a column space ("QR / orth" step)

Every integrator for dynamical low-rank approximation (projector-splitting / KSL, the basis-update
& Galerkin (BUG) integrator, its rank-adaptive and parallel variants) contains a step of the form
"compute an orthonormal basis `U₁` of the range of `K₁`", in practice by a QR decomposition:
`K₁ = U₁ R₁` (Lubich–Oseledets, arXiv 1301.1058, §3.2; Ceruti–Lubich, arXiv 2010.02022, §3.1;
Ceruti–Kusch–Lubich, arXiv 2104.05247, §2.1, and arXiv 2304.05660, §2.1 and §3.1).  The error
analysis never uses the triangular factor: it only uses that the new basis is orthonormal,
`U₁ᵀ U₁ = 1`, and that it *captures* the range, `U₁ U₁ᵀ K₁ = K₁`.  This file proves the existence
of such bases, together with the elementary rank and projector facts used alongside them.

## Main results

* `LeanDLRA.exists_orthonormal_of_le`: in a finite-dimensional real inner product space, if
  `W ≤ V` and `dim W ≤ r ≤ dim V`, there are `r` orthonormal vectors in `V` whose span contains
  `W`.
* `LeanDLRA.exists_orthonormal_capture`: for every `K : Matrix m k ℝ` with `rank K ≤ r ≤ card m`
  there is `U : Matrix m (Fin r) ℝ` with `Uᵀ U = 1` and `U Uᵀ K = K`.  In particular this holds for
  every `K : Matrix m (Fin r) ℝ` with `r ≤ card m` (`exists_orthonormal_capture_of_le_card`), which
  is the QR step of all the integrators above (with the rank-deficient case covered as well).
* `LeanDLRA.exists_augmented_basis`: the `m × 2r` augmented basis `Û` of the rank-adaptive BUG
  integrator, capturing both `K(t₁)` and `U₀` (more generally `exists_orthonormal_capture_fromCols`
  for a block matrix `[K, U₀]`).
* `LeanDLRA.mul_transpose_eq_of_capture`: uniqueness of the orthogonal projector `U Uᵀ` onto a
  given range.
* `LeanDLRA.mul_transpose_eq_one_of_transpose_mul_eq_one`, `rank_eq_card_of_transpose_mul_eq_one`,
  `rank_mul_mul_transpose_le` (`rank (U S Vᵀ) ≤ r`), `rank_mul_add_mul_transpose_le`
  (`rank (U B + C Vᵀ) ≤ 2 r`).
* `LeanDLRA.exists_orthonormal_capture_compl` and `exists_parallel_augmented_basis`: the basis
  `Ũ₁ ⊥ U₀` capturing `(1 - U₀ U₀ᵀ) K(t₁)` and the augmented basis `Û = (U₀, Ũ₁)` of the parallel
  BUG integrator.

## Deviations from the papers

* The papers take `Û` "an orthonormal basis of the range" and, in the rank-deficient case, either
  allow fewer columns (arXiv 2304.05660, §2.1: `r̂ ≤ 2 r`) or fill `Ũ₁` with zero columns
  (arXiv 2304.05660, §3.1).  Here the basis always has exactly the prescribed number of
  orthonormal columns; it then spans a superspace of the range.  This needs `r ≤ card m`
  (resp. `2 r ≤ card m`), the regime in which the integrators are used.  The error analysis only
  uses `Ûᵀ Û = 1` and the capture identities, which hold for both choices.

## Implementation notes

Columns of a matrix are viewed as vectors of `EuclideanSpace ℝ m`; `colSpan A` is the span of the
columns of `A` there, and `ofCols u` is the matrix with columns `u j` (both defined in
`LeanDLRA/LinearAlgebra/LowRank/Defs.lean`).  The existence proof extends
an orthonormal basis of the column space to an orthonormal basis of the ambient space
(`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`) and keeps the first `r` vectors.
-/

open Module Submodule
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA

/-! ### An abstract extension lemma -/

/-- In a finite-dimensional real inner product space, if `W ≤ V` and `dim W ≤ r ≤ dim V`, then
there are `r` orthonormal vectors lying in `V` whose span contains `W`. -/
theorem exists_orthonormal_of_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {W V : Submodule ℝ E} (hWV : W ≤ V) {r : ℕ}
    (hW : finrank ℝ W ≤ r) (hV : r ≤ finrank ℝ V) :
    ∃ u : Fin r → E, Orthonormal ℝ u ∧ (∀ j, u j ∈ V) ∧ W ≤ span ℝ (Set.range u) := by
  set d := finrank ℝ W with hd
  set n := finrank ℝ V with hn
  let bW : OrthonormalBasis (Fin d) ℝ W := stdOrthonormalBasis ℝ W
  let v : Fin n → V := fun i =>
    if h : (i : ℕ) < d then ⟨(bW ⟨i, h⟩ : E), hWV (bW ⟨i, h⟩).2⟩ else 0
  let s : Set (Fin n) := {i | (i : ℕ) < d}
  have hvi : ∀ (i : Fin n) (h : (i : ℕ) < d), ((v i : V) : E) = (bW ⟨i, h⟩ : E) := by
    intro i h
    simp [v, h]
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.domRestrict_apply, Submodule.coe_inner]
    rw [hvi i hi, hvi j hj, ← Submodule.coe_inner, orthonormal_iff_ite.mp bW.orthonormal]
    simp [Fin.ext_iff]
  obtain ⟨B, hB⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (ι := Fin n) (by simp [n])
  refine ⟨fun j => (B (Fin.castLE hV j) : E), ?_, fun j => (B _).2, ?_⟩
  · exact (B.orthonormal.comp_linearIsometry V.subtypeₗᵢ).comp _ (Fin.castLE_injective hV)
  · intro w hw
    have hrep : w = ∑ i, bW.repr ⟨w, hw⟩ i • (bW i : E) := by
      conv_lhs => rw [show w = ((⟨w, hw⟩ : W) : E) from rfl, ← bW.sum_repr ⟨w, hw⟩]
      simp
    rw [hrep]
    refine Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (subset_span ⟨⟨i, by omega⟩, ?_⟩)
    have hi : (Fin.castLE hV ⟨i, by omega⟩ : Fin n) ∈ s := by simp [s]
    simp only
    rw [hB _ hi, hvi _ (by simp)]
    rfl

/-! ### Columns as Euclidean vectors -/

variable {m n ι : Type*}

lemma colSpan_eq_map (A : Matrix m n ℝ) :
    colSpan A = (span ℝ (Set.range A.col)).map
      (WithLp.linearEquiv 2 ℝ (m → ℝ)).symm.toLinearMap := by
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

/-- The dimension of the column space is the rank. -/
lemma finrank_colSpan [Fintype n] (A : Matrix m n ℝ) :
    finrank ℝ (colSpan A) = A.rank := by
  rw [colSpan_eq_map, LinearEquiv.finrank_map_eq, Matrix.rank_eq_finrank_span_cols]

lemma toLp_col_mem_colSpan (A : Matrix m n ℝ) (j : n) :
    WithLp.toLp 2 (A.col j) ∈ colSpan A :=
  subset_span ⟨j, rfl⟩

lemma toLp_col_ofCols (u : ι → EuclideanSpace ℝ m) (j : ι) :
    WithLp.toLp 2 ((ofCols u).col j) = u j := rfl

/-- The entries of `(ofCols u)ᵀ A` are inner products of the `u j` with the columns of `A`. -/
lemma transpose_ofCols_mul_apply [Fintype m] (u : ι → EuclideanSpace ℝ m)
    (A : Matrix m n ℝ) (j : ι) (l : n) :
    ((ofCols u)ᵀ * A) j l = ⟪u j, WithLp.toLp 2 (A.col l)⟫ := by
  simp [Matrix.mul_apply, PiLp.inner_apply, mul_comm]

/-- Orthonormal columns give a matrix with `Uᵀ U = 1`. -/
lemma transpose_ofCols_mul_ofCols [Fintype m] [DecidableEq ι]
    {u : ι → EuclideanSpace ℝ m} (hu : Orthonormal ℝ u) : (ofCols u)ᵀ * ofCols u = 1 := by
  ext j l
  rw [transpose_ofCols_mul_apply, toLp_col_ofCols, orthonormal_iff_ite.mp hu, Matrix.one_apply]

/-- If every column of `X` lies in the span of the `u i`, then `X = ofCols u * C` for some `C`. -/
lemma exists_eq_mul_of_col_mem_span [Fintype ι] {u : ι → EuclideanSpace ℝ m}
    {X : Matrix m n ℝ} (h : ∀ j, WithLp.toLp 2 (X.col j) ∈ span ℝ (Set.range u)) :
    ∃ C : Matrix ι n ℝ, X = ofCols u * C := by
  have h' := fun j => (Submodule.mem_span_range_iff_exists_fun ℝ).mp (h j)
  choose c hc using h'
  refine ⟨Matrix.of fun i j => c j i, ?_⟩
  ext a j
  have := congrArg (fun x : EuclideanSpace ℝ m => x a) (hc j)
  simp only [Matrix.col_apply] at this
  rw [← this]
  simp [Matrix.mul_apply, mul_comm]

/-- If `Uᵀ U = 1` and `X = U C`, then `U Uᵀ X = X`. -/
lemma mul_transpose_mul_eq_of_eq_mul [Fintype m] [Fintype ι] [DecidableEq ι]
    {U : Matrix m ι ℝ} (hU : Uᵀ * U = 1) {X : Matrix m n ℝ} {C : Matrix ι n ℝ}
    (hX : X = U * C) : U * Uᵀ * X = X := by
  rw [hX, Matrix.mul_assoc U, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul]

/-- The orthonormal family produced by `exists_orthonormal_of_le` captures every matrix whose
column space lies in its span. -/
lemma ofCols_capture [Fintype m] [Fintype ι] {u : ι → EuclideanSpace ℝ m}
    (hu : Orthonormal ℝ u) {X : Matrix m n ℝ} (hX : colSpan X ≤ span ℝ (Set.range u)) :
    ofCols u * (ofCols u)ᵀ * X = X := by
  classical
  obtain ⟨C, hC⟩ := exists_eq_mul_of_col_mem_span fun j => hX (toLp_col_mem_colSpan X j)
  exact mul_transpose_mul_eq_of_eq_mul (transpose_ofCols_mul_ofCols hu) hC

/-! ### Existence of a capturing orthonormal basis -/

/-- **Existence of the "QR" basis.**  For every real matrix `K` with `rank K ≤ r ≤ card m` there is
a matrix `U` with `r` orthonormal columns (`Uᵀ U = 1`) whose range contains the range of `K`
(`U Uᵀ K = K`).  This is the orthonormalisation step `K₁ = U₁ R₁` of the KSL and BUG
integrators (arXiv 1301.1058 §3, arXiv 2010.02022 Alg. 1); the statement also covers
rank-deficient `K`, where a QR factorisation is not unique. -/
theorem exists_orthonormal_capture [Fintype m] {k : Type*} [Fintype k] (K : Matrix m k ℝ) {r : ℕ}
    (hK : K.rank ≤ r) (hr : r ≤ Fintype.card m) :
    ∃ U : Matrix m (Fin r) ℝ, Uᵀ * U = 1 ∧ U * Uᵀ * K = K := by
  obtain ⟨u, hu, -, hW⟩ := exists_orthonormal_of_le (W := colSpan K) (V := ⊤) (r := r) le_top
    (by rw [finrank_colSpan]; exact hK) (by rw [finrank_top, finrank_euclideanSpace]; exact hr)
  exact ⟨ofCols u, transpose_ofCols_mul_ofCols hu, ofCols_capture hu hW⟩

/-- The QR step for an `m × r` matrix: if `r ≤ card m`, every `K : Matrix m (Fin r) ℝ` admits
`U : Matrix m (Fin r) ℝ` with `Uᵀ U = 1` and `U Uᵀ K = K`. -/
theorem exists_orthonormal_capture_of_le_card [Fintype m] {r : ℕ} (K : Matrix m (Fin r) ℝ)
    (hr : r ≤ Fintype.card m) : ∃ U : Matrix m (Fin r) ℝ, Uᵀ * U = 1 ∧ U * Uᵀ * K = K :=
  exists_orthonormal_capture K (by simpa using K.rank_le_card_width) hr

/-! ### Augmented bases (rank-adaptive BUG) -/

/-- **Augmented basis for a block matrix.**  If `rank [K, U₀] ≤ r ≤ card m`, there is
`Û : Matrix m (Fin r) ℝ` with orthonormal columns whose range contains the ranges of both `K` and
`U₀`. -/
theorem exists_orthonormal_capture_fromCols [Fintype m] {k₁ k₂ : Type*} [Fintype k₁]
    [Fintype k₂] (K : Matrix m k₁ ℝ) (U₀ : Matrix m k₂ ℝ) {r : ℕ}
    (hK : (Matrix.fromCols K U₀).rank ≤ r) (hr : r ≤ Fintype.card m) :
    ∃ U : Matrix m (Fin r) ℝ, Uᵀ * U = 1 ∧ U * Uᵀ * K = K ∧ U * Uᵀ * U₀ = U₀ := by
  obtain ⟨U, hU, hcap⟩ := exists_orthonormal_capture _ hK hr
  rw [Matrix.mul_fromCols] at hcap
  exact ⟨U, hU, Matrix.fromCols_inj.eq_iff.mp hcap⟩

/-- **Augmented basis of the rank-adaptive BUG integrator** (Ceruti–Kusch–Lubich,
arXiv 2104.05247, Alg. 1, K-step; arXiv 2304.05660, §2.1): for `K(t₁), U₀ : Matrix m (Fin r) ℝ`
and `2 r ≤ card m` there is `Û : Matrix m (Fin (2 r)) ℝ` with `Ûᵀ Û = 1`, `Û Ûᵀ K = K` and
`Û Ûᵀ U₀ = U₀`.  The paper's `Û` is an orthonormal basis of the range of `(K(t₁), U₀)`; here the
rank-deficient case is covered by completing to `2 r` orthonormal columns. -/
theorem exists_augmented_basis [Fintype m] {r : ℕ} (K U₀ : Matrix m (Fin r) ℝ)
    (hr : 2 * r ≤ Fintype.card m) :
    ∃ U : Matrix m (Fin (2 * r)) ℝ, Uᵀ * U = 1 ∧ U * Uᵀ * K = K ∧ U * Uᵀ * U₀ = U₀ := by
  refine exists_orthonormal_capture_fromCols K U₀ ?_ hr
  have h := (Matrix.fromCols K U₀).rank_le_card_width
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

/-! ### Uniqueness of the orthogonal projector -/

/-- If two matrices with orthonormal columns have the same range, the orthogonal projectors
`U Uᵀ` and `U' U'ᵀ` coincide.  Ranges are compared through the capture identities. -/
theorem mul_transpose_eq_of_capture_of_capture [Fintype m] {ι' : Type*} [Fintype ι]
    [Fintype ι'] {U : Matrix m ι ℝ} {U' : Matrix m ι' ℝ}
    (h : U' * U'ᵀ * U = U) (h' : U * Uᵀ * U' = U') : U * Uᵀ = U' * U'ᵀ := by
  have h1 : U' * U'ᵀ * (U * Uᵀ) = U * Uᵀ := by rw [← Matrix.mul_assoc, h]
  have h2 : U * Uᵀ * (U' * U'ᵀ) = U' * U'ᵀ := by rw [← Matrix.mul_assoc, h']
  have h3 : U * Uᵀ * (U' * U'ᵀ) = U * Uᵀ := by
    have := congrArg Matrix.transpose h1
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  rw [← h2, h3]

/-- **Uniqueness of the projector.**  If `U` has orthonormal columns, `U'` has the same number of
columns (more generally: index types of equal cardinality) and the range of `U` is contained in
the range of `U'` in the sense `U' U'ᵀ U = U`, then `U Uᵀ = U' U'ᵀ`.  In particular the projector
`P₁ = U₁ U₁ᵀ` of an integrator step does not depend on the choice of orthonormal basis
(cf. arXiv 2104.05247, remark after (8)).  The orthonormality `U'ᵀ U' = 1` of the second matrix is
not needed as a hypothesis; the proof writes `U = U' M` with `M = U'ᵀ U`, observes `Mᵀ M = 1`,
hence `M Mᵀ = 1` for the square matrix `M`. -/
theorem mul_transpose_eq_of_capture [Fintype m] {ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] {U : Matrix m ι ℝ} {U' : Matrix m ι' ℝ}
    (hcard : Fintype.card ι = Fintype.card ι') (hU : Uᵀ * U = 1)
    (h : U' * U'ᵀ * U = U) : U * Uᵀ = U' * U'ᵀ := by
  classical
  set M := U'ᵀ * U with hM
  have hUM : U = U' * M := by rw [hM, ← Matrix.mul_assoc]; exact h.symm
  have hMM : Mᵀ * M = 1 := by
    calc Mᵀ * M = Uᵀ * (U' * U'ᵀ * U) := by
          simp [M, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h, hU]
  have hMM' : M * Mᵀ = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (A := Mᵀ) (B := M) (eq := hcard)).mp hMM
  calc U * Uᵀ = U' * M * (U' * M)ᵀ := by rw [← hUM]
    _ = U' * (M * Mᵀ) * U'ᵀ := by simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = U' * U'ᵀ := by rw [hMM', Matrix.mul_one]

/-- `mul_transpose_eq_of_capture` for two `m × r` matrices: if `Uᵀ U = 1` and
`U' U'ᵀ U = U` then `U Uᵀ = U' U'ᵀ` (no orthonormality of `U'` is needed). -/
theorem mul_transpose_eq_of_capture_fin [Fintype m] {r : ℕ} {U U' : Matrix m (Fin r) ℝ}
    (hU : Uᵀ * U = 1) (h : U' * U'ᵀ * U = U) : U * Uᵀ = U' * U'ᵀ :=
  mul_transpose_eq_of_capture rfl hU h

/-! ### Square orthonormal matrices and rank bounds -/

/-- A square matrix with orthonormal columns is orthogonal: `Qᵀ Q = 1 → Q Qᵀ = 1`. -/
theorem mul_transpose_eq_one_of_transpose_mul_eq_one [Fintype ι] [DecidableEq ι]
    {Q : Matrix ι ι ℝ} (h : Qᵀ * Q = 1) : Q * Qᵀ = 1 :=
  mul_eq_one_comm.mp h

/-- A matrix with orthonormal columns has full column rank. -/
theorem rank_eq_card_of_transpose_mul_eq_one [Fintype m] [Fintype ι] [DecidableEq ι]
    {U : Matrix m ι ℝ} (h : Uᵀ * U = 1) : U.rank = Fintype.card ι := by
  apply le_antisymm U.rank_le_card_width
  calc Fintype.card ι = (1 : Matrix ι ι ℝ).rank := Matrix.rank_one.symm
    _ = (Uᵀ * U).rank := by rw [h]
    _ ≤ U.rank := Matrix.rank_mul_le_right _ _

/-- A factored matrix `U S Vᵀ` with `r` columns in `U` has rank at most `r`. -/
theorem rank_mul_mul_transpose_le {n : Type*} [Fintype n] {r : ℕ}
    (U : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) :
    (U * S * Vᵀ).rank ≤ r := by
  calc (U * S * Vᵀ).rank ≤ (U * S).rank := Matrix.rank_mul_le_left _ _
    _ ≤ U.rank := Matrix.rank_mul_le_left _ _
    _ ≤ r := by simpa using U.rank_le_card_width

/-- Tangent vectors `U B + C Vᵀ` at a rank-`r` point have rank at most `2 r`. -/
theorem rank_mul_add_mul_transpose_le {n : Type*} [Fintype n] {r : ℕ}
    (U : Matrix m (Fin r) ℝ) (B : Matrix (Fin r) n ℝ) (C : Matrix m (Fin r) ℝ)
    (V : Matrix n (Fin r) ℝ) : (U * B + C * Vᵀ).rank ≤ 2 * r := by
  rw [← Matrix.fromCols_mul_fromRows]
  calc _ ≤ (Matrix.fromCols U C).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin r ⊕ Fin r) := Matrix.rank_le_card_width _
    _ = 2 * r := by simp only [Fintype.card_sum, Fintype.card_fin]; ring

/-! ### Capture in the orthogonal complement (parallel BUG) -/

/-- Inner products of columns are the entries of `Aᵀ B`. -/
lemma inner_toLp_col_col [Fintype m] {n' : Type*} (A : Matrix m n ℝ) (B : Matrix m n' ℝ)
    (j : n) (l : n') :
    ⟪WithLp.toLp 2 (A.col j), WithLp.toLp 2 (B.col l)⟫ = (Aᵀ * B) j l := by
  simp [Matrix.mul_apply, PiLp.inner_apply, mul_comm]

/-- **Orthogonal-complement capture.**  Let `U₀` have orthonormal columns and let
`X = (1 - U₀ U₀ᵀ) K`.  If `rank X ≤ s` and `card ι + s ≤ card m`, there is
`Ũ : Matrix m (Fin s) ℝ` with `Ũᵀ Ũ = 1`, `Ũᵀ U₀ = 0` and `Ũ Ũᵀ X = X`. -/
theorem exists_orthonormal_capture_compl [Fintype m] [DecidableEq m] [Fintype ι]
    [DecidableEq ι] {k : Type*} [Fintype k] (U₀ : Matrix m ι ℝ) (hU₀ : U₀ᵀ * U₀ = 1)
    (K : Matrix m k ℝ) {s : ℕ} (hK : ((1 - U₀ * U₀ᵀ) * K).rank ≤ s)
    (hs : Fintype.card ι + s ≤ Fintype.card m) :
    ∃ U : Matrix m (Fin s) ℝ, Uᵀ * U = 1 ∧ Uᵀ * U₀ = 0 ∧
      U * Uᵀ * ((1 - U₀ * U₀ᵀ) * K) = (1 - U₀ * U₀ᵀ) * K := by
  set X := (1 - U₀ * U₀ᵀ) * K with hX
  have hXU : Xᵀ * U₀ = 0 := by
    rw [hX, Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.sub_mul,
      Matrix.one_mul, Matrix.mul_assoc, hU₀, Matrix.mul_one, sub_self, Matrix.mul_zero]
  have hWV : colSpan X ≤ (colSpan U₀)ᗮ := by
    rw [← Submodule.isOrtho_iff_le, colSpan, colSpan, Submodule.isOrtho_span]
    rintro _ ⟨j, rfl⟩ _ ⟨l, rfl⟩
    rw [inner_toLp_col_col, hXU, Matrix.zero_apply]
  have hdim := (colSpan U₀).finrank_add_finrank_orthogonal
  rw [finrank_euclideanSpace, finrank_colSpan] at hdim
  have hU₀r := U₀.rank_le_card_width
  obtain ⟨u, hu, hV, hW⟩ := exists_orthonormal_of_le (r := s) hWV
    (by rw [finrank_colSpan]; exact hK) (by omega)
  refine ⟨ofCols u, transpose_ofCols_mul_ofCols hu, ?_, ofCols_capture hu hW⟩
  ext j l
  rw [transpose_ofCols_mul_apply, Matrix.zero_apply]
  exact Submodule.inner_left_of_mem_orthogonal (toLp_col_mem_colSpan U₀ l) (hV j)

/-- **Augmented basis of the parallel BUG integrator** (Ceruti–Kusch–Lubich, arXiv 2304.05660,
§3.1, K-step).  Let `U₀ : Matrix m (Fin r) ℝ` have orthonormal columns, `K : Matrix m (Fin r) ℝ`
and `r + r ≤ card m`.  Then there is `Ũ₁ : Matrix m (Fin r) ℝ` with orthonormal columns,
orthogonal to `U₀` (`Ũ₁ᵀ U₀ = 0`), whose range contains the range of `(1 - U₀ U₀ᵀ) K`.  In the
paper, `Ũ₁` is filled with zero columns in the rank-deficient case; here it is completed to `r`
orthonormal columns instead. -/
theorem exists_orthonormal_capture_compl_fin [Fintype m] [DecidableEq m] {r : ℕ}
    (U₀ : Matrix m (Fin r) ℝ) (hU₀ : U₀ᵀ * U₀ = 1) (K : Matrix m (Fin r) ℝ)
    (hr : r + r ≤ Fintype.card m) :
    ∃ U : Matrix m (Fin r) ℝ, Uᵀ * U = 1 ∧ Uᵀ * U₀ = 0 ∧
      U * Uᵀ * ((1 - U₀ * U₀ᵀ) * K) = (1 - U₀ * U₀ᵀ) * K :=
  exists_orthonormal_capture_compl U₀ hU₀ K
    (by have h := ((1 - U₀ * U₀ᵀ) * K).rank_le_card_width; rwa [Fintype.card_fin] at h)
    (by rw [Fintype.card_fin]; exact hr)

/-- The augmented basis `Û = (U₀, Ũ₁)` of the parallel BUG integrator: if `U₀` and `Ũ₁` have
orthonormal columns, `Ũ₁ᵀ U₀ = 0` and `Ũ₁` captures `(1 - U₀ U₀ᵀ) K`, then `Û` has orthonormal
columns and captures both `U₀` and `K` (arXiv 2304.05660, §3.1). -/
theorem fromCols_orthonormal_capture [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι]
    {ι' k : Type*} [Fintype ι'] [DecidableEq ι'] {U₀ : Matrix m ι ℝ} {U₁ : Matrix m ι' ℝ}
    {K : Matrix m k ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hU₁ : U₁ᵀ * U₁ = 1) (h₁₀ : U₁ᵀ * U₀ = 0)
    (hcap : U₁ * U₁ᵀ * ((1 - U₀ * U₀ᵀ) * K) = (1 - U₀ * U₀ᵀ) * K) :
    (Matrix.fromCols U₀ U₁)ᵀ * Matrix.fromCols U₀ U₁ = 1 ∧
      Matrix.fromCols U₀ U₁ * (Matrix.fromCols U₀ U₁)ᵀ * K = K ∧
      Matrix.fromCols U₀ U₁ * (Matrix.fromCols U₀ U₁)ᵀ * U₀ = U₀ := by
  have h₀₁ : U₀ᵀ * U₁ = 0 := by
    have := congrArg Matrix.transpose h₁₀
    simpa [Matrix.transpose_mul] using this
  have hP : Matrix.fromCols U₀ U₁ * (Matrix.fromCols U₀ U₁)ᵀ = U₀ * U₀ᵀ + U₁ * U₁ᵀ := by
    rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, hU₀, hU₁, h₀₁, h₁₀,
      Matrix.fromBlocks_one]
  · have e : U₁ * U₁ᵀ * ((1 - U₀ * U₀ᵀ) * K) = U₁ * U₁ᵀ * K := by
      simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub]
      rw [show U₁ * U₁ᵀ * (U₀ * U₀ᵀ * K) = U₁ * (U₁ᵀ * U₀) * U₀ᵀ * K by
        simp only [Matrix.mul_assoc], h₁₀]
      simp
    have hK : U₁ * U₁ᵀ * K = (1 - U₀ * U₀ᵀ) * K := by rw [← e]; exact hcap
    rw [hP, Matrix.add_mul, hK, Matrix.sub_mul, Matrix.one_mul]
    abel
  · rw [hP, Matrix.add_mul, Matrix.mul_assoc U₀, hU₀, Matrix.mul_one, Matrix.mul_assoc U₁, h₁₀,
      Matrix.mul_zero, add_zero]

/-- **Augmented basis of the parallel BUG integrator** (Ceruti–Kusch–Lubich, arXiv 2304.05660,
§3.1, K-step).  If `U₀ : Matrix m (Fin r) ℝ` has orthonormal columns, `K : Matrix m (Fin r) ℝ`
and `r + r ≤ card m`, there is `Ũ₁ : Matrix m (Fin r) ℝ` with `Ũ₁ᵀ U₀ = 0` such that
`Û = (U₀, Ũ₁)` has orthonormal columns and captures both `K` and `U₀`. -/
theorem exists_parallel_augmented_basis [Fintype m] {r : ℕ}
    (U₀ : Matrix m (Fin r) ℝ) (hU₀ : U₀ᵀ * U₀ = 1) (K : Matrix m (Fin r) ℝ)
    (hr : r + r ≤ Fintype.card m) :
    ∃ U₁ : Matrix m (Fin r) ℝ, U₁ᵀ * U₁ = 1 ∧ U₁ᵀ * U₀ = 0 ∧
      (Matrix.fromCols U₀ U₁)ᵀ * Matrix.fromCols U₀ U₁ = 1 ∧
      Matrix.fromCols U₀ U₁ * (Matrix.fromCols U₀ U₁)ᵀ * K = K ∧
      Matrix.fromCols U₀ U₁ * (Matrix.fromCols U₀ U₁)ᵀ * U₀ = U₀ := by
  classical
  obtain ⟨U₁, hU₁, h₁₀, hcap⟩ := exists_orthonormal_capture_compl_fin U₀ hU₀ K hr
  exact ⟨U₁, hU₁, h₁₀, fromCols_orthonormal_capture hU₀ hU₁ h₁₀ hcap⟩

end LeanDLRA
