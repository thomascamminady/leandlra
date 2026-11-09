import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Interpolation
import LeanDLRA.Matrix.GaugeODE

/-!
# Results of arXiv 2607.03402: Sketched DLRA, orthogonal vs oblique projections

Carrel–Grigori, *Sketch low-rank dynamics: orthogonal vs. oblique projections*.  This module
formalizes the subspace-embedding preliminaries of §2.1, the coupled factor equations of the
orthogonal sketch DLRA (§3.2) and the Loewner bounds for sketch-orthonormal bases (§5.2), all
in finite dimensions over `ℝ`, with the Frobenius inner product on matrices
(`open scoped LeanDLRA.Frobenius`).

## Main definitions

* `IsEmbeddingOn T V ε`: the linear map `T` is an `ε`-embedding of the subspace `V`,
  `(1 - ε)‖x‖² ≤ ‖T x‖² ≤ (1 + ε)‖x‖²` on `V` (the event of Definition 2.1 for one draw).  A
  sketch `Θ ∈ ℝ^{ℓ×m}` embeds `V ⊆ ℝ^m` when `IsEmbeddingOn (Matrix.toEuclideanLin Θ) V ε`.
  Column and row spaces are the core `LeanDLRA.colSpan` (of `Z` and of `Zᵀ`).
* `IsOSE μ Θ d ε δ` (**Definition 2.1**): a random sketch `Θ : α → ℝ^{ℓ×m}` on a measure space
  fails to `ε`-embed any fixed `d`-dimensional subspace with probability at most `δ`.
* `colsIn V k`: the matrices in `ℝ^{m×k}` whose columns lie in `V` (helper; `mem_colsIn_iff`
  identifies it with `colSpan U ≤ V`).

## Main results

* `isEmbeddingOn_iff` (the "Equivalently" of **Definition 2.1**): the norm form of an
  `ε`-embedding is equivalent to `|⟪T x, T y⟫ - ⟪x, y⟫| ≤ ε ‖x‖ ‖y‖` on `V`.
* `abs_inner_sketch_sub_le` (**Proposition 2.2**, deterministic form) and
  `abs_norm_sq_sketch_sub_le_of_orthonormal` (its orthonormal special case);
  `abs_inner_sketch_sub_le_prob` (the probability statement).
* `abs_inner_twoSidedSketch_sub_le`, `norm_sq_twoSidedSketch_ge` (**Corollary 2.3**,
  deterministic form); `twoSidedSketch_prob` (with probability `≥ 1 - 2δ`).
* `norm_sketchTangentProj_sub_le_of_isEmbeddingOn` (**§4.2**, chain of Corollary 2.3 with the
  core `norm_sketchTangentProj_sub_le`): if the realized sketches embed the column and row
  spaces of the perpendicular residual `N = Z - P_Y Z` and of `δ = P^{Θ,Ω}_Y Z - P_Y Z`, then
  `‖P^{Θ,Ω}_Y Z - P_Y Z‖_F ≤ (2ε + ε²)/(1 - ε)² ‖Z - P_Y Z‖_F`.
* `orthSketchDLRA_factorODE_within` and `orthSketchDLRA_factorODE` (**Proposition 3.1**:
  coupled equations (9) of the orthogonal sketch DLRA under the Euclidean gauge), with the
  algebraic core `gramFactorODE_of_sum_eq`; `obliqueTangentProj_self_mul_right` (eq. (7) is the
  orthogonal tangent projector (3), so (8) is the classical DLRA).
* `sketch_embed_loewner` (**§5.2**: `(1+ε)⁻¹ I ⪯ PᵀP ⪯ (1-ε)⁻¹ I` for sketch-orthonormal `P`),
  `sketch_embed_loewner_of_isEmbeddingOn`, and `sketch_embed_loewner_prob` (probability
  `≥ 1 - δ` for bases spanning a fixed range).

Non-vacuity: `isEmbeddingOn_one`, a genuine compression (`Θ = (1 0)` embeds `colSpan e₁`),
`isOSE_one`, and examples for `sketch_embed_loewner` and `orthSketchDLRA_factorODE` (moving
core `S(t) = eᵗ`, non-orthonormal sketch-orthogonal `P = 2`).

## Deviations from the paper

* **Probability.**  The deterministic theorems take the embedding of the relevant fixed
  subspaces by the realized sketch as hypothesis; this is exactly the event the paper's proofs
  use.  The probability statements follow by inclusion of events (and a union bound for
  Corollary 2.3, which needs no independence of `Θ` and `Ω`).  `IsOSE` bounds the failure
  probability `μ {¬ embedding} ≤ δ`; for a probability measure this gives "the embedding holds
  with probability `≥ 1 - δ`" (`ofReal_one_sub_le_measure`), and is equivalent to it when the
  event is measurable.  Embedding a subspace of dimension `≤ d` via an OSE of exact dimension
  `d` needs `d ≤ m` (`exists_le_finrank_eq`), implicit in the paper's `r ≪ m`.
* **Range of `ε`.**  Proposition 2.2 holds for every `ε`.  Corollary 2.3 needs `0 ≤ ε`, and its
  lower bound `‖ΘZΩᵀ‖² ≥ (1-ε)²‖Z‖²` needs `ε ≤ 1` (for `ε > 2`, `Θ = I`, `Ω = I` is a
  counterexample); the paper's OSE parameter is implicitly in `(0, 1)`.  That lower bound is
  not a special case of the first bound of the corollary (which gives `1 - 2ε - ε²`); it
  follows from the norm form of the embedding on each side.
* **Proposition 3.1** is stated for a given differentiable factorization (as in the paper, "let
  `Y = P S Wᵀ` be a solution"), with derivatives within a set on which derivatives are unique
  (so one-sided derivatives at interval endpoints are covered), and `S(t)` invertible (the
  parametrization of `M_r^{Θ,Ω}` has `S ∈ GL(r)`; the paper uses `S⁻¹`).  The pointwise version
  assumes full column rank (invertible Gram matrices) as the paper does; the trajectory version
  `orthSketchDLRA_factorODE` instead derives it: the gauge keeps `PᵀP`, `WᵀW` constant
  (core `transpose_mul_self_eq_of_skew`), and sketch-orthogonal initial factors have invertible
  Gram matrices (`isUnit_det_gram_of_sketch`).  The proof is direct algebra on eq. (7), not
  via the map `φ` and matrix square roots; `φ` itself is not formalized.
* **§5.2** is stated for any `P` with `(ΘP)ᵀ(ΘP) = I`, the property of the RGS output that the
  claim uses.

## Not formalized here

Lemma 4.1 (oblique coupled equations) is not formalized.  Lemma 4.2 and Proposition 4.4 are in
`LeanDLRA/Matrix/Interpolation.lean` (`obliqueTangentProj_sketch_eq`,
`isObliqueProj_sketchTangentProj`, `sketchTangentProj_eq_iff`), together with a quantitative
consequence of eq. (15), `norm_sketchTangentProj_sub_le`, whose two hypotheses are discharged
here by Corollary 2.3 (`norm_sketchTangentProj_sub_le_of_isEmbeddingOn`).

## Core definitions used

`colSpan`, `Frobenius.leftMulCLM`, `obliqueProj`, `obliqueTangentProj`, `tangentProj`;
core lemmas `exists_orthonormal_of_le`, `finrank_colSpan`,
`GaugeODE.hasDerivWithinAt_factorProduct`, `transpose_mul_self_eq_of_skew`,
`obliqueProj_self_mul_right`.  The local definitions
`IsEmbeddingOn`, `IsOSE` and `colsIn` have no core counterpart (the core states embedding
hypotheses inline, e.g. `norm_sq_bounds_of_sketch`, `norm_sketchTangentProj_sub_le`).
-/

open Set Filter Topology Finset Module MeasureTheory
open scoped RealInnerProductSpace Matrix MatrixOrder LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2607_03402

/-- Quadratic form of `PᵀP`: `xᵀ (PᵀP) x = ‖P x‖²`. -/
private lemma quad_transpose_mul_self {m k : Type*} [Fintype m] [Fintype k] (P : Matrix m k ℝ)
    (x : k → ℝ) : x ⬝ᵥ ((Pᵀ * P) *ᵥ x) = (P *ᵥ x) ⬝ᵥ (P *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-! ### Subspace embeddings (§2.1) -/

section Embedding

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

/-- **`ε`-embedding of a subspace** (the event in Definition 2.1 of arXiv 2607.03402, for one
realization of the sketch): the linear map `T` satisfies
`(1 - ε)‖x‖² ≤ ‖T x‖² ≤ (1 + ε)‖x‖²` for every `x ∈ V`.  For a sketch `Θ ∈ ℝ^{ℓ×m}` take
`T = Matrix.toEuclideanLin Θ`. -/
def IsEmbeddingOn (T : E →ₗ[ℝ] F) (V : Submodule ℝ E) (ε : ℝ) : Prop :=
  ∀ x ∈ V, (1 - ε) * ‖x‖ ^ 2 ≤ ‖T x‖ ^ 2 ∧ ‖T x‖ ^ 2 ≤ (1 + ε) * ‖x‖ ^ 2

variable {T : E →ₗ[ℝ] F} {V W : Submodule ℝ E} {ε : ℝ}

/-- An `ε`-embedding of `V` is an `ε`-embedding of every subspace of `V`. -/
theorem IsEmbeddingOn.mono (h : IsEmbeddingOn T V ε) (hWV : W ≤ V) : IsEmbeddingOn T W ε :=
  fun x hx => h x (hWV hx)

/-- Polarization step: `|⟪T x, T y⟫ - ⟪x, y⟫| ≤ ε (‖x‖² + ‖y‖²) / 2` on an `ε`-embedded
subspace. -/
private lemma IsEmbeddingOn.abs_inner_sub_le_half (h : IsEmbeddingOn T V ε) {x y : E}
    (hx : x ∈ V) (hy : y ∈ V) :
    |⟪T x, T y⟫ - ⟪x, y⟫| ≤ ε * (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  obtain ⟨h1, h2⟩ := h (x + y) (V.add_mem hx hy)
  obtain ⟨h3, h4⟩ := h (x - y) (V.sub_mem hx hy)
  simp only [map_add, map_sub, norm_add_sq_real, norm_sub_sq_real] at h1 h2 h3 h4
  rw [abs_le]
  constructor <;> linarith

/-- **Inner-product form of an embedding** (Definition 2.1 of arXiv 2607.03402, "Equivalently",
direction norm form ⇒ inner-product form): if `T` is an `ε`-embedding of `V`, then
`|⟪T x, T y⟫ - ⟪x, y⟫| ≤ ε ‖x‖ ‖y‖` for all `x, y ∈ V`. -/
theorem IsEmbeddingOn.abs_inner_sub_le (h : IsEmbeddingOn T V ε) {x y : E} (hx : x ∈ V)
    (hy : y ∈ V) : |⟪T x, T y⟫ - ⟪x, y⟫| ≤ ε * ‖x‖ * ‖y‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  have key := h.abs_inner_sub_le_half (V.smul_mem ‖y‖ hx) (V.smul_mem ‖x‖ hy)
  have hpos : 0 < ‖x‖ * ‖y‖ := mul_pos (norm_pos_iff.2 hx0) (norm_pos_iff.2 hy0)
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right, norm_smul, norm_norm] at key
  have e : ‖x‖ * (‖y‖ * ⟪T x, T y⟫) - ‖x‖ * (‖y‖ * ⟪x, y⟫) =
      (‖x‖ * ‖y‖) * (⟪T x, T y⟫ - ⟪x, y⟫) := by ring
  have e2 : ε * ((‖y‖ * ‖x‖) ^ 2 + (‖x‖ * ‖y‖) ^ 2) / 2 = (‖x‖ * ‖y‖) * (ε * ‖x‖ * ‖y‖) := by
    ring
  rw [e, abs_mul, abs_of_pos hpos, e2] at key
  exact le_of_mul_le_mul_left key hpos

/-- **Definition 2.1 of arXiv 2607.03402, "Equivalently"**: `T` is an `ε`-embedding of `V`
(norm form) iff `|⟪T x, T y⟫ - ⟪x, y⟫| ≤ ε ‖x‖ ‖y‖` for all `x, y ∈ V`. -/
theorem isEmbeddingOn_iff :
    IsEmbeddingOn T V ε ↔ ∀ x ∈ V, ∀ y ∈ V, |⟪T x, T y⟫ - ⟪x, y⟫| ≤ ε * ‖x‖ * ‖y‖ := by
  refine ⟨fun h x hx y hy => h.abs_inner_sub_le hx hy, fun h x hx => ?_⟩
  have h' := h x hx x hx
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, abs_le] at h'
  constructor <;> nlinarith [h'.1, h'.2]

end Embedding

/-! ### Tall matrices and two-sided sketches (Proposition 2.2, Corollary 2.3) -/

section Matrices

variable {p q m n k : Type*}

/-- The matrices `U ∈ ℝ^{m×k}` whose columns lie in the subspace `V ⊆ ℝ^m`
(`mem_colsIn_iff`: equivalently `colSpan U ≤ V`). -/
def colsIn (V : Submodule ℝ (EuclideanSpace ℝ m)) (k : Type*) : Submodule ℝ (Matrix m k ℝ) where
  carrier := {U | ∀ j, WithLp.toLp 2 (U.col j) ∈ V}
  add_mem' {_ _} hU hW j := V.add_mem (hU j) (hW j)
  zero_mem' _ := V.zero_mem
  smul_mem' c _ hU j := V.smul_mem c (hU j)

/-- A matrix has its columns in `V` iff its column space (core `colSpan`) is contained in
`V`. -/
theorem mem_colsIn_iff {V : Submodule ℝ (EuclideanSpace ℝ m)} {U : Matrix m k ℝ} :
    U ∈ colsIn V k ↔ colSpan U ≤ V := by
  rw [colSpan, Submodule.span_le, Set.range_subset_iff]
  rfl

/-- The column space of `Z M` is contained in that of `Z`. -/
theorem colSpan_mul_le [Fintype n] (Z : Matrix m n ℝ) (M : Matrix n q ℝ) :
    colSpan (Z * M) ≤ colSpan Z := by
  rw [colSpan, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  change WithLp.toLp 2 ((Z * M).col j) ∈ colSpan Z
  have e : WithLp.toLp 2 ((Z * M).col j) = ∑ i, M i j • WithLp.toLp 2 (Z.col i) := by
    ext l
    simp [Matrix.mul_apply, Matrix.col, mul_comm]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (toLp_col_mem_colSpan Z i)

variable [Fintype p] [Fintype q] [Fintype m] [Fintype n] [Fintype k]

omit [Fintype p] [Fintype q] [Fintype n] in
/-- The squared Frobenius norm is the sum of the squared Euclidean norms of the columns. -/
theorem norm_sq_eq_sum_norm_sq_col (U : Matrix m k ℝ) :
    ‖U‖ ^ 2 = ∑ j, ‖WithLp.toLp 2 (U.col j)‖ ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum, Finset.sum_comm]
  simp [EuclideanSpace.real_norm_sq_eq, Matrix.col]

omit [Fintype p] [Fintype q] [Fintype n] in
/-- A matrix with orthonormal columns has squared Frobenius norm equal to the number of
columns. -/
theorem norm_sq_eq_card_of_orthonormal [DecidableEq k] {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) :
    ‖U‖ ^ 2 = Fintype.card k := by
  rw [← real_inner_self_eq_norm_sq, Frobenius.inner_eq_trace, hU, Matrix.trace_one]

variable [DecidableEq m] [DecidableEq n]

omit [Fintype p] [Fintype q] [Fintype n] [Fintype k] [DecidableEq n] in
/-- The sketch of the `j`-th column of `U` is the `j`-th column of `Θ U`. -/
theorem toEuclideanLin_toLp_col (Θ : Matrix p m ℝ) (U : Matrix m k ℝ) (j : k) :
    Matrix.toEuclideanLin Θ (WithLp.toLp 2 (U.col j)) = WithLp.toLp 2 ((Θ * U).col j) := rfl

omit [Fintype q] [Fintype n] [DecidableEq n] in
/-- If `Θ` `ε`-embeds `V ⊆ ℝ^m`, then `U ↦ Θ U` `ε`-embeds (in the Frobenius norm) the matrices
with columns in `V`: sum the column-wise bounds. -/
theorem IsEmbeddingOn.leftMul {Θ : Matrix p m ℝ} {V : Submodule ℝ (EuclideanSpace ℝ m)} {ε : ℝ}
    (h : IsEmbeddingOn (Matrix.toEuclideanLin Θ) V ε) :
    IsEmbeddingOn (Frobenius.leftMulCLM Θ : Matrix m k ℝ →L[ℝ] Matrix p k ℝ).toLinearMap
      (colsIn V k) ε := by
  intro U hU
  simp only [ContinuousLinearMap.coe_coe, Frobenius.leftMulCLM_apply]
  rw [norm_sq_eq_sum_norm_sq_col, norm_sq_eq_sum_norm_sq_col, Finset.mul_sum, Finset.mul_sum]
  constructor
  · refine Finset.sum_le_sum fun j _ => ?_
    have := (h _ (hU j)).1
    rwa [toEuclideanLin_toLp_col] at this
  · refine Finset.sum_le_sum fun j _ => ?_
    have := (h _ (hU j)).2
    rwa [toEuclideanLin_toLp_col] at this

omit [Fintype p] [Fintype q] [Fintype n] [Fintype k] [DecidableEq n] in
/-- Non-vacuity of `IsEmbeddingOn`: the identity sketch `ε`-embeds every subspace, for every
`ε ≥ 0`. -/
theorem isEmbeddingOn_one (V : Submodule ℝ (EuclideanSpace ℝ m)) {ε : ℝ} (hε : 0 ≤ ε) :
    IsEmbeddingOn (Matrix.toEuclideanLin (1 : Matrix m m ℝ)) V ε := by
  intro x _
  have e : Matrix.toEuclideanLin (1 : Matrix m m ℝ) x = x := by simp
  rw [e]
  constructor <;> nlinarith [sq_nonneg ‖x‖]

/-- Non-vacuity with a genuine compression (`ℓ = 1 < m = 2`): the sketch `Θ = (1 0)` is a
`0`-embedding of the column space of `U = e₁`, so Proposition 2.2 and Corollary 2.3 apply to
sketches that are not injective on `ℝ^m`. -/
example : IsEmbeddingOn (Matrix.toEuclideanLin !![(1 : ℝ), 0])
    (colSpan (!![(1 : ℝ); 0] : Matrix (Fin 2) (Fin 1) ℝ)) 0 := by
  intro x hx
  rw [colSpan, Set.range_unique, Submodule.mem_span_singleton] at hx
  obtain ⟨c, rfl⟩ := hx
  have e1 : ‖c • WithLp.toLp 2 ((!![(1 : ℝ); 0] : Matrix (Fin 2) (Fin 1) ℝ).col default)‖ ^ 2 =
      c ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]; simp [Fin.sum_univ_two, Matrix.col]
  have e2 : ‖Matrix.toEuclideanLin !![(1 : ℝ), 0]
      (c • WithLp.toLp 2 ((!![(1 : ℝ); 0] : Matrix (Fin 2) (Fin 1) ℝ).col default))‖ ^ 2 =
      c ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, Fin.sum_univ_two, Matrix.col]
  rw [e1, e2]
  constructor <;> linarith

omit [Fintype q] [Fintype n] [DecidableEq n] in
/-- Frobenius-norm form of an embedding: if `Θ` `ε`-embeds `V` and `colSpan U ≤ V`, then
`(1 - ε)‖U‖² ≤ ‖Θ U‖² ≤ (1 + ε)‖U‖²`. -/
theorem IsEmbeddingOn.norm_sq_mul_bounds {Θ : Matrix p m ℝ}
    {V : Submodule ℝ (EuclideanSpace ℝ m)} {ε : ℝ}
    (h : IsEmbeddingOn (Matrix.toEuclideanLin Θ) V ε) {U : Matrix m k ℝ} (hU : colSpan U ≤ V) :
    (1 - ε) * ‖U‖ ^ 2 ≤ ‖Θ * U‖ ^ 2 ∧ ‖Θ * U‖ ^ 2 ≤ (1 + ε) * ‖U‖ ^ 2 :=
  h.leftMul U (mem_colsIn_iff.2 hU)

omit [Fintype q] [Fintype n] [DecidableEq n] in
/-- Frobenius inner-product form of an embedding: if `Θ` `ε`-embeds `V` and the columns of `U`
and `U'` lie in `V`, then `|⟪Θ U, Θ U'⟫ - ⟪U, U'⟫| ≤ ε ‖U‖ ‖U'‖`. -/
theorem IsEmbeddingOn.abs_inner_mul_sub_le {Θ : Matrix p m ℝ}
    {V : Submodule ℝ (EuclideanSpace ℝ m)} {ε : ℝ}
    (h : IsEmbeddingOn (Matrix.toEuclideanLin Θ) V ε) {U U' : Matrix m k ℝ}
    (hU : colSpan U ≤ V) (hU' : colSpan U' ≤ V) :
    |⟪Θ * U, Θ * U'⟫ - ⟪U, U'⟫| ≤ ε * ‖U‖ * ‖U'‖ :=
  h.leftMul.abs_inner_sub_le (mem_colsIn_iff.2 hU) (mem_colsIn_iff.2 hU')

omit [Fintype q] [Fintype n] [DecidableEq n] in
/-- **Proposition 2.2 of arXiv 2607.03402** (tall matrix embedding; deterministic form).  Let
`U, V ∈ ℝ^{m×k}` and let the sketch `Ω ∈ ℝ^{ℓ×m}` `ε`-embed `Range([U V]) = colSpan U ⊔ colSpan V`
(the event of probability `≥ 1 - δ` for an `OSE(2r, ε, δ)` and fixed `U, V`, used in the
paper's proof; the probability form is `abs_inner_sketch_sub_le_prob`).  Then
`|⟪ΩU, ΩV⟫ - ⟪U, V⟫| ≤ ε ‖U‖_F ‖V‖_F` and, equivalently,
`|⟪UᵀΩᵀ, VᵀΩᵀ⟫ - ⟪Uᵀ, Vᵀ⟫| ≤ ε ‖U‖_F ‖V‖_F`.  No sign condition on `ε` is needed. -/
theorem abs_inner_sketch_sub_le {Ω : Matrix p m ℝ} {ε : ℝ} {U V : Matrix m k ℝ}
    (hΩ : IsEmbeddingOn (Matrix.toEuclideanLin Ω) (colSpan U ⊔ colSpan V) ε) :
    |⟪Ω * U, Ω * V⟫ - ⟪U, V⟫| ≤ ε * ‖U‖ * ‖V‖ ∧
      |⟪Uᵀ * Ωᵀ, Vᵀ * Ωᵀ⟫ - ⟪Uᵀ, Vᵀ⟫| ≤ ε * ‖U‖ * ‖V‖ := by
  have h := hΩ.abs_inner_mul_sub_le le_sup_left le_sup_right
  refine ⟨h, ?_⟩
  rwa [← Matrix.transpose_mul, ← Matrix.transpose_mul, Frobenius.inner_transpose,
    Frobenius.inner_transpose]

omit [Fintype q] [Fintype n] [DecidableEq n] in
/-- **Proposition 2.2 of arXiv 2607.03402, "in particular"** (deterministic form): if `U` has
orthonormal columns (`r = card k` of them) and `Ω` `ε`-embeds `colSpan U`, then
`|‖ΩU‖_F² - ‖U‖_F²| ≤ ε r` and `|‖UᵀΩᵀ‖_F² - ‖U‖_F²| ≤ ε r`.  (The paper states the second
bound for its second matrix `V`; it is the same statement.) -/
theorem abs_norm_sq_sketch_sub_le_of_orthonormal [DecidableEq k] {Ω : Matrix p m ℝ} {ε : ℝ}
    {U : Matrix m k ℝ} (hU : Uᵀ * U = 1)
    (hΩ : IsEmbeddingOn (Matrix.toEuclideanLin Ω) (colSpan U) ε) :
    |‖Ω * U‖ ^ 2 - ‖U‖ ^ 2| ≤ ε * Fintype.card k ∧
      |‖Uᵀ * Ωᵀ‖ ^ 2 - ‖U‖ ^ 2| ≤ ε * Fintype.card k := by
  have h := abs_inner_sketch_sub_le (V := U) (hΩ.mono (sup_le le_rfl le_rfl))
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, Frobenius.norm_transpose, mul_assoc, ← sq,
    norm_sq_eq_card_of_orthonormal hU] at h
  rw [norm_sq_eq_card_of_orthonormal hU]
  exact h

/-- **Corollary 2.3 of arXiv 2607.03402** (two-sided embedding; deterministic form).  Let
`Z, Z' ∈ ℝ^{m×n}`, let `Θ ∈ ℝ^{ℓ×m}` `ε`-embed their combined column space and
`Ω ∈ ℝ^{ℓ'×n}` `ε`-embed their combined row space (`colSpan` of the transposes), with
`0 ≤ ε`.  Then `|⟪ΘZΩᵀ, ΘZ'Ωᵀ⟫ - ⟪Z, Z'⟫| ≤ (2ε + ε²) ‖Z‖_F ‖Z'‖_F`.  The proof is the
paper's: Proposition 2.2 on each side, and `‖ZΩᵀ‖_F² ≤ (1 + ε)‖Z‖_F²` for the cross term.
Probability form: `twoSidedSketch_prob`. -/
theorem abs_inner_twoSidedSketch_sub_le {Θ : Matrix p m ℝ} {Ω : Matrix q n ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) {Z Z' : Matrix m n ℝ}
    (hΘ : IsEmbeddingOn (Matrix.toEuclideanLin Θ) (colSpan Z ⊔ colSpan Z') ε)
    (hΩ : IsEmbeddingOn (Matrix.toEuclideanLin Ω) (colSpan Zᵀ ⊔ colSpan Z'ᵀ) ε) :
    |⟪Θ * Z * Ωᵀ, Θ * Z' * Ωᵀ⟫ - ⟪Z, Z'⟫| ≤ (2 * ε + ε ^ 2) * ‖Z‖ * ‖Z'‖ := by
  have h1 := hΘ.abs_inner_mul_sub_le (U := Z * Ωᵀ) (U' := Z' * Ωᵀ)
    ((colSpan_mul_le _ _).trans le_sup_left) ((colSpan_mul_le _ _).trans le_sup_right)
  have h2 := hΩ.abs_inner_mul_sub_le (U := Zᵀ) (U' := Z'ᵀ) le_sup_left le_sup_right
  have eX : ∀ A : Matrix m n ℝ, Ω * Aᵀ = (A * Ωᵀ)ᵀ := fun A => by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [eX, eX, Frobenius.inner_transpose, Frobenius.inner_transpose, Frobenius.norm_transpose,
    Frobenius.norm_transpose] at h2
  have n1 := (hΩ.norm_sq_mul_bounds (U := Zᵀ) le_sup_left).2
  have n2 := (hΩ.norm_sq_mul_bounds (U := Z'ᵀ) le_sup_right).2
  rw [eX, Frobenius.norm_transpose, Frobenius.norm_transpose] at n1 n2
  have hprod : ‖Z * Ωᵀ‖ * ‖Z' * Ωᵀ‖ ≤ (1 + ε) * ‖Z‖ * ‖Z'‖ := by
    have hsq : (‖Z * Ωᵀ‖ * ‖Z' * Ωᵀ‖) ^ 2 ≤ ((1 + ε) * ‖Z‖ * ‖Z'‖) ^ 2 := by
      have := mul_le_mul n1 n2 (sq_nonneg _) (by positivity)
      nlinarith [this]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  calc |⟪Θ * (Z * Ωᵀ), Θ * (Z' * Ωᵀ)⟫ - ⟪Z, Z'⟫|
      ≤ |⟪Θ * (Z * Ωᵀ), Θ * (Z' * Ωᵀ)⟫ - ⟪Z * Ωᵀ, Z' * Ωᵀ⟫| +
          |⟪Z * Ωᵀ, Z' * Ωᵀ⟫ - ⟪Z, Z'⟫| := abs_sub_le _ _ _
    _ ≤ ε * ‖Z * Ωᵀ‖ * ‖Z' * Ωᵀ‖ + ε * ‖Z‖ * ‖Z'‖ := add_le_add h1 h2
    _ ≤ ε * ((1 + ε) * ‖Z‖ * ‖Z'‖) + ε * ‖Z‖ * ‖Z'‖ := by
        rw [mul_assoc ε]; gcongr
    _ = (2 * ε + ε ^ 2) * ‖Z‖ * ‖Z'‖ := by ring

/-- **Corollary 2.3 of arXiv 2607.03402, "in particular"** (deterministic form): if `Θ`
`ε`-embeds the column space of `Z` and `Ω` its row space, with `ε ≤ 1`, then
`‖ΘZΩᵀ‖_F² ≥ (1 - ε)² ‖Z‖_F²`.  (This is not a consequence of the first bound of the corollary,
which only gives `1 - 2ε - ε²`; it follows from the norm form of the embedding on each side.
For `ε > 2` it fails: `Θ = I`, `Ω = I` embed everything.) -/
theorem norm_sq_twoSidedSketch_ge {Θ : Matrix p m ℝ} {Ω : Matrix q n ℝ} {ε : ℝ} (hε : ε ≤ 1)
    {Z : Matrix m n ℝ} (hΘ : IsEmbeddingOn (Matrix.toEuclideanLin Θ) (colSpan Z) ε)
    (hΩ : IsEmbeddingOn (Matrix.toEuclideanLin Ω) (colSpan Zᵀ) ε) :
    (1 - ε) ^ 2 * ‖Z‖ ^ 2 ≤ ‖Θ * Z * Ωᵀ‖ ^ 2 := by
  have n1 := (hΘ.norm_sq_mul_bounds (U := Z * Ωᵀ) (colSpan_mul_le _ _)).1
  have n2 := (hΩ.norm_sq_mul_bounds (U := Zᵀ) le_rfl).1
  rw [← Matrix.transpose_transpose (Ω * Zᵀ), Frobenius.norm_transpose, Matrix.transpose_mul,
    Matrix.transpose_transpose, Frobenius.norm_transpose] at n2
  rw [Matrix.mul_assoc]
  have h1e : 0 ≤ 1 - ε := by linarith
  nlinarith [mul_le_mul_of_nonneg_left n2 h1e]

/-- **Oblique residual bound of §4.2 of arXiv 2607.03402** (deterministic; a chain of
Corollary 2.3 with the core quantitative form of eq. (15), `norm_sketchTangentProj_sub_le`).
Setting of Lemma 4.2 / Proposition 4.4: `U`, `V` orthonormal, `P = U R`, `W = V R'`
sketch-orthonormal.  Let `N = Z - P_Y Z` (for `Z = F(Y)`, the perpendicular residual
`P_Y^⊥ F(Y)`) and `δ = P^{Θ,Ω}_Y Z - P_Y Z` (the `Z` of Proposition 4.4).  If the realized
`Θ` `ε`-embeds the combined column space of `N` and `δ`, and `Ω` their combined row space,
with `0 ≤ ε < 1`, then `‖P^{Θ,Ω}_Y Z - P_Y Z‖_F ≤ (2ε + ε²) / (1 - ε)² ‖Z - P_Y Z‖_F`.  The
paper derives the two ingredients in §4.2 (the bound `(2ε + ε²)‖P_Y^⊥ F‖ ‖δY‖` on the oblique
residual, from `⟪N, δY⟫ = 0` and Corollary 2.3, and `‖ΘZΩᵀ‖² ≥ (1 - ε)²‖Z‖²` in the proof of
Proposition 4.4) but does not state the combined inequality; as in Proposition 4.4 the
embedding is a hypothesis on the realized sketch (cf. Remark 4.5). -/
theorem norm_sketchTangentProj_sub_le_of_isEmbeddingOn [DecidableEq k] {l : Type*} [Fintype l]
    [DecidableEq l] {U : Matrix m k ℝ} {V : Matrix n l ℝ} {Θ : Matrix p m ℝ}
    {Ω : Matrix q n ℝ} {R : Matrix k k ℝ} {R' : Matrix l l ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hP : (Θ * (U * R))ᵀ * (Θ * (U * R)) = 1)
    (hW : (Ω * (V * R'))ᵀ * (Ω * (V * R')) = 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (Z : Matrix m n ℝ)
    (hΘ : IsEmbeddingOn (Matrix.toEuclideanLin Θ) (colSpan (Z - tangentProj U V Z) ⊔
      colSpan (sketchTangentProj Θ Ω (U * R) (V * R') Z - tangentProj U V Z)) ε)
    (hΩ : IsEmbeddingOn (Matrix.toEuclideanLin Ω) (colSpan (Z - tangentProj U V Z)ᵀ ⊔
      colSpan (sketchTangentProj Θ Ω (U * R) (V * R') Z - tangentProj U V Z)ᵀ) ε) :
    ‖sketchTangentProj Θ Ω (U * R) (V * R') Z - tangentProj U V Z‖ ≤
      (2 * ε + ε ^ 2) / (1 - ε) ^ 2 * ‖Z - tangentProj U V Z‖ := by
  set δ := sketchTangentProj Θ Ω (U * R) (V * R') Z - tangentProj U V Z with hδ
  have hob := isObliqueProj_sketchTangentProj hU hV hP hW
  have horth := isOrthProj_tangentProj (m := m) (n := n) hU hV
  -- `δ` is tangent and `N = Z - P_Y Z` is normal, so `⟪N, δ⟫ = 0`
  have hδt : tangentProj U V δ = δ := by
    rw [hδ, map_sub, hob.range, horth.idem]
  have hNδ : ⟪Z - tangentProj U V Z, δ⟫ = 0 := by
    rw [real_inner_comm, ← hδt]
    exact horth.inner_sub_self δ Z
  have hip := abs_inner_twoSidedSketch_sub_le hε0 hΘ hΩ
  rw [hNδ, sub_zero] at hip
  have hlow2 := norm_sq_twoSidedSketch_ge hε1.le (hΘ.mono le_sup_right) (hΩ.mono le_sup_right)
  have hlow : (1 - ε) * ‖δ‖ ≤ ‖Θ * δ * Ωᵀ‖ := by
    have h1e : 0 ≤ 1 - ε := by linarith
    rw [← pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero, mul_pow]
    exact hlow2
  exact norm_sketchTangentProj_sub_le hU hV hP hW hε1 (by positivity) Z hlow hip

end Matrices

/-! ### Oblivious subspace embeddings: the probability statements -/

section Probability

variable {α : Type*} [MeasurableSpace α] {p q m n k : Type*} [Fintype p] [Fintype q]
  [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n]

/-- **Definition 2.1 of arXiv 2607.03402** (oblivious subspace embedding `OSE(d, ε, δ)`), for a
random sketch `Θ : α → ℝ^{ℓ×m}` on a measure space `(α, μ)`: for every `d`-dimensional
subspace `V ⊆ ℝ^m`, the event that `Θ` fails to `ε`-embed `V` has measure at most `δ`.  For a
probability measure this gives "with probability at least `1 - δ`"
(`ofReal_one_sub_le_measure`), and is equivalent to it when the event is measurable.  The
paper's distribution over sketches is the law of `Θ`. -/
def IsOSE (μ : Measure α) (Θ : α → Matrix p m ℝ) (d : ℕ) (ε δ : ℝ) : Prop :=
  ∀ V : Submodule ℝ (EuclideanSpace ℝ m), finrank ℝ V = d →
    μ {ω | ¬ IsEmbeddingOn (Matrix.toEuclideanLin (Θ ω)) V ε} ≤ ENNReal.ofReal δ

omit [DecidableEq m] in
/-- Every subspace of `ℝ^m` of dimension at most `d ≤ m` lies in a subspace of dimension
exactly `d` (via the core `exists_orthonormal_of_le`). -/
theorem exists_le_finrank_eq (W : Submodule ℝ (EuclideanSpace ℝ m)) {d : ℕ}
    (hW : finrank ℝ W ≤ d) (hd : d ≤ Fintype.card m) :
    ∃ V : Submodule ℝ (EuclideanSpace ℝ m), W ≤ V ∧ finrank ℝ V = d := by
  obtain ⟨u, hu, -, hWu⟩ := exists_orthonormal_of_le (le_top : W ≤ ⊤) hW
    (by rwa [finrank_top, finrank_euclideanSpace])
  exact ⟨Submodule.span ℝ (Set.range u), hWu, by
    rw [finrank_span_eq_card hu.linearIndependent, Fintype.card_fin]⟩

omit [Fintype q] [Fintype n] [Fintype k] [DecidableEq n] in
/-- An `OSE(d, ε, δ)` fails to `ε`-embed a fixed subspace of dimension at most `d ≤ m` with
probability at most `δ`. -/
theorem IsOSE.measure_not_embedding_le {μ : Measure α} {Θ : α → Matrix p m ℝ} {d : ℕ}
    {ε δ : ℝ} (h : IsOSE μ Θ d ε δ) {W : Submodule ℝ (EuclideanSpace ℝ m)}
    (hW : finrank ℝ W ≤ d) (hd : d ≤ Fintype.card m) :
    μ {ω | ¬ IsEmbeddingOn (Matrix.toEuclideanLin (Θ ω)) W ε} ≤ ENNReal.ofReal δ := by
  obtain ⟨V, hWV, hV⟩ := exists_le_finrank_eq W hW hd
  refine (measure_mono ?_).trans (h V hV)
  intro ω hω
  exact fun h' => hω (h'.mono hWV)

omit [MeasurableSpace α] in
/-- For a probability measure, an event whose complement has measure at most `δ ≥ 0` has
measure at least `1 - δ` (no measurability needed). -/
theorem ofReal_one_sub_le_measure {_ : MeasurableSpace α} {μ : Measure α}
    [IsProbabilityMeasure μ] {s : Set α} {δ : ℝ} (hδ : 0 ≤ δ) (h : μ sᶜ ≤ ENNReal.ofReal δ) :
    ENNReal.ofReal (1 - δ) ≤ μ s := by
  have h1 : (1 : ENNReal) ≤ μ s + μ sᶜ := by
    rw [← measure_univ (μ := μ), ← Set.union_compl_self s]
    exact measure_union_le _ _
  rw [ENNReal.ofReal_sub _ hδ, ENNReal.ofReal_one, tsub_le_iff_right]
  exact h1.trans (by gcongr)

omit [Fintype p] [Fintype q] [Fintype n] [Fintype k] [DecidableEq n] in
/-- Non-vacuity of `IsOSE`: the constant identity sketch is an `OSE(d, ε, 0)` for every
`ε ≥ 0` and every measure. -/
theorem isOSE_one (μ : Measure α) (d : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    IsOSE μ (fun _ => (1 : Matrix m m ℝ)) d ε 0 := by
  intro V _
  have h : {ω : α | ¬ IsEmbeddingOn (Matrix.toEuclideanLin (1 : Matrix m m ℝ)) V ε} = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun _ hω => hω (isEmbeddingOn_one V hε)
  rw [h, measure_empty]
  exact zero_le

omit [Fintype q] [Fintype n] [DecidableEq n] in
/-- **Proposition 2.2 of arXiv 2607.03402** (probability form).  Let `Ω` be an
`OSE(2r, ε, δ)` with `r = card k` and `2r ≤ m`, and let `U, V ∈ ℝ^{m×r}` be fixed.  Then with
probability at least `1 - δ`, `|⟪ΩU, ΩV⟫ - ⟪U, V⟫| ≤ ε ‖U‖_F ‖V‖_F` and
`|⟪UᵀΩᵀ, VᵀΩᵀ⟫ - ⟪Uᵀ, Vᵀ⟫| ≤ ε ‖U‖_F ‖V‖_F`. -/
theorem abs_inner_sketch_sub_le_prob {μ : Measure α} [IsProbabilityMeasure μ]
    {Ω : α → Matrix p m ℝ} {ε δ : ℝ} (hδ : 0 ≤ δ) (hΩ : IsOSE μ Ω (2 * Fintype.card k) ε δ)
    (hk : 2 * Fintype.card k ≤ Fintype.card m) (U V : Matrix m k ℝ) :
    ENNReal.ofReal (1 - δ) ≤ μ {ω | |⟪Ω ω * U, Ω ω * V⟫ - ⟪U, V⟫| ≤ ε * ‖U‖ * ‖V‖ ∧
      |⟪Uᵀ * (Ω ω)ᵀ, Vᵀ * (Ω ω)ᵀ⟫ - ⟪Uᵀ, Vᵀ⟫| ≤ ε * ‖U‖ * ‖V‖} := by
  refine ofReal_one_sub_le_measure hδ ?_
  have hdim : finrank ℝ ↥(colSpan U ⊔ colSpan V) ≤ 2 * Fintype.card k := by
    calc finrank ℝ ↥(colSpan U ⊔ colSpan V)
        ≤ finrank ℝ (colSpan U) + finrank ℝ (colSpan V) :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ 2 * Fintype.card k := by
          rw [finrank_colSpan, finrank_colSpan, two_mul]
          exact add_le_add (Matrix.rank_le_card_width U) (Matrix.rank_le_card_width V)
  refine (measure_mono ?_).trans (hΩ.measure_not_embedding_le hdim hk)
  intro ω hω
  exact fun h' => hω (abs_inner_sketch_sub_le h')

/-- **Corollary 2.3 of arXiv 2607.03402** (probability form).  Let `Θ : α → ℝ^{ℓ×m}` and
`Ω : α → ℝ^{ℓ'×n}` be `OSE(d, ε, δ)` on the same probability space (no independence is
needed), with `0 ≤ ε ≤ 1` and `d ≤ m, n`, and let `Z, Z' ∈ ℝ^{m×n}` be fixed with combined
column space and combined row space of dimension at most `d`.  Then with probability at least
`1 - 2δ`, `|⟪ΘZΩᵀ, ΘZ'Ωᵀ⟫ - ⟪Z, Z'⟫| ≤ (2ε + ε²) ‖Z‖_F ‖Z'‖_F` and
`‖ΘZΩᵀ‖_F² ≥ (1 - ε)² ‖Z‖_F²`. -/
theorem twoSidedSketch_prob {μ : Measure α} [IsProbabilityMeasure μ] {Θ : α → Matrix p m ℝ}
    {Ω : α → Matrix q n ℝ} {d : ℕ} {ε δ : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ)
    (hΘ : IsOSE μ Θ d ε δ) (hΩ : IsOSE μ Ω d ε δ) (hdm : d ≤ Fintype.card m)
    (hdn : d ≤ Fintype.card n) {Z Z' : Matrix m n ℝ}
    (hcol : finrank ℝ ↥(colSpan Z ⊔ colSpan Z') ≤ d)
    (hrow : finrank ℝ ↥(colSpan Zᵀ ⊔ colSpan Z'ᵀ) ≤ d) :
    ENNReal.ofReal (1 - 2 * δ) ≤ μ {ω |
      |⟪Θ ω * Z * (Ω ω)ᵀ, Θ ω * Z' * (Ω ω)ᵀ⟫ - ⟪Z, Z'⟫| ≤ (2 * ε + ε ^ 2) * ‖Z‖ * ‖Z'‖ ∧
        (1 - ε) ^ 2 * ‖Z‖ ^ 2 ≤ ‖Θ ω * Z * (Ω ω)ᵀ‖ ^ 2} := by
  refine ofReal_one_sub_le_measure (by linarith) ?_
  calc μ {ω | |⟪Θ ω * Z * (Ω ω)ᵀ, Θ ω * Z' * (Ω ω)ᵀ⟫ - ⟪Z, Z'⟫| ≤
          (2 * ε + ε ^ 2) * ‖Z‖ * ‖Z'‖ ∧ (1 - ε) ^ 2 * ‖Z‖ ^ 2 ≤ ‖Θ ω * Z * (Ω ω)ᵀ‖ ^ 2}ᶜ
      ≤ μ ({ω | ¬ IsEmbeddingOn (Matrix.toEuclideanLin (Θ ω)) (colSpan Z ⊔ colSpan Z') ε} ∪
          {ω | ¬ IsEmbeddingOn (Matrix.toEuclideanLin (Ω ω)) (colSpan Zᵀ ⊔ colSpan Z'ᵀ) ε}) := by
        refine measure_mono fun ω hω => ?_
        by_contra hc
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
        exact hω ⟨abs_inner_twoSidedSketch_sub_le hε0 hc.1 hc.2,
          norm_sq_twoSidedSketch_ge hε1 (hc.1.mono le_sup_left) (hc.2.mono le_sup_left)⟩
    _ ≤ μ {ω | ¬ IsEmbeddingOn (Matrix.toEuclideanLin (Θ ω)) (colSpan Z ⊔ colSpan Z') ε} +
          μ {ω | ¬ IsEmbeddingOn (Matrix.toEuclideanLin (Ω ω)) (colSpan Zᵀ ⊔ colSpan Z'ᵀ) ε} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal δ + ENNReal.ofReal δ :=
        add_le_add (hΘ.measure_not_embedding_le hcol hdm) (hΩ.measure_not_embedding_le hrow hdn)
    _ = ENNReal.ofReal (2 * δ) := by rw [← ENNReal.ofReal_add hδ hδ, two_mul]

end Probability

/-! ### Orthogonal sketch DLRA: coupled factor equations (Proposition 3.1) -/

section OrthSketch

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

/-- A sketch-orthogonal basis (`P ∈ St_Θ(m, r)`, `(ΘP)ᵀ(ΘP) = I`, Definition 2.5 of
arXiv 2607.03402) has full column rank: its Gram matrix `PᵀP` is invertible. -/
theorem isUnit_det_gram_of_sketch {p : Type*} [Fintype p] {Θ : Matrix p m ℝ}
    {P : Matrix m r ℝ} (h : (Θ * P)ᵀ * (Θ * P) = 1) : IsUnit (Pᵀ * P).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have hz : (Pᵀ * P) *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  have hPz : P *ᵥ (x - y) = 0 := by
    have e := quad_transpose_mul_self P (x - y)
    rw [hz, dotProduct_zero] at e
    exact dotProduct_self_eq_zero.1 e.symm
  have e := congrArg (((Θ * P)ᵀ * Θ) *ᵥ ·) hPz
  simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at e
  rw [Matrix.mul_assoc, h, Matrix.one_mulVec] at e
  exact sub_eq_zero.1 e

/-- **Eq. (7) of arXiv 2607.03402 is the orthogonal tangent projector (3)**: for bases
`P = U R`, `W = V R'` of the ranges of orthonormal `U`, `V` (`R`, `R'` invertible; e.g. the
sketch-orthogonal factors with `U = P(PᵀP)^{-1/2}`, `R = (PᵀP)^{1/2}` as in the map `φ`), the
projector
`Z ↦ P(PᵀP)⁻¹PᵀZ + ZW(WᵀW)⁻¹Wᵀ - P(PᵀP)⁻¹PᵀZW(WᵀW)⁻¹Wᵀ`, which is
`obliqueTangentProj P P W W`, equals the core `tangentProj U V`.  So the orthogonal sketch
DLRA (8) is the classical DLRA (5). -/
theorem obliqueTangentProj_self_mul_right {k k' : Type*} [Fintype k] [DecidableEq k]
    [Fintype k'] [DecidableEq k'] {U : Matrix m k ℝ} {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {R : Matrix k k ℝ} {R' : Matrix k' k' ℝ} (hR : IsUnit R.det)
    (hR' : IsUnit R'.det) :
    obliqueTangentProj (U * R) (U * R) (V * R') (V * R') = tangentProj U V := by
  ext1 Z
  rw [obliqueTangentProj_apply, obliqueProj_self_mul_right hU hR,
    obliqueProj_self_mul_right hV hR', tangentProj_apply]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

variable [DecidableEq m] [DecidableEq n]

/-- Algebraic core of **Proposition 3.1 of arXiv 2607.03402**.  Let `P ∈ ℝ^{m×r}`,
`W ∈ ℝ^{n×r}` have invertible Gram matrices, `S` be invertible, and let the velocities
`P', S', W'` satisfy the Euclidean gauge `PᵀP' = 0`, `WᵀW' = 0`.  If
`P' S Wᵀ + P S' Wᵀ + P S W'ᵀ = P_Y X` with `P_Y` the projector (7) written in the factors
(`obliqueTangentProj P P W W`), then the coupled equations (9) hold:
`P' = (I - P(PᵀP)⁻¹Pᵀ) X W (WᵀW)⁻¹ S⁻¹`, `S' = (PᵀP)⁻¹ Pᵀ X W (WᵀW)⁻¹`,
`W' = (I - W(WᵀW)⁻¹Wᵀ) Xᵀ P (PᵀP)⁻¹ S⁻ᵀ`. -/
theorem gramFactorODE_of_sum_eq {P P' : Matrix m r ℝ} {S S' : Matrix r r ℝ}
    {W W' : Matrix n r ℝ} {X : Matrix m n ℝ} (hPr : IsUnit (Pᵀ * P).det)
    (hWr : IsUnit (Wᵀ * W).det) (hS : IsUnit S.det) (hgP : Pᵀ * P' = 0) (hgW : Wᵀ * W' = 0)
    (h : P' * S * Wᵀ + P * S' * Wᵀ + P * S * W'ᵀ = obliqueTangentProj P P W W X) :
    P' = (1 - P * (Pᵀ * P)⁻¹ * Pᵀ) * X * W * (Wᵀ * W)⁻¹ * S⁻¹ ∧
      S' = (Pᵀ * P)⁻¹ * Pᵀ * X * W * (Wᵀ * W)⁻¹ ∧
      W' = (1 - W * (Wᵀ * W)⁻¹ * Wᵀ) * Xᵀ * P * (Pᵀ * P)⁻¹ * (S⁻¹)ᵀ := by
  have hW'W : W'ᵀ * W = 0 := by
    rw [← Matrix.transpose_transpose (W'ᵀ * W), Matrix.transpose_mul, Matrix.transpose_transpose,
      hgW, Matrix.transpose_zero]
  have hPt : Pᵀ * obliqueProj P P = Pᵀ := transpose_mul_obliqueProj hPr
  have hWW : (obliqueProj W W)ᵀ * W = W := obliqueProj_transpose_mul hWr
  rw [obliqueTangentProj_apply] at h
  -- right multiplication by `W`
  have hR : (P' * S + P * S') * (Wᵀ * W) = X * W := by
    have := congrArg (· * W) h
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, hW'W, hWW, Matrix.mul_zero,
      add_zero] at this
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, this]
    abel
  -- left multiplication by `Pᵀ`
  have hL : (Pᵀ * P) * (S' * Wᵀ + S * W'ᵀ) = Pᵀ * X := by
    have := congrArg (Pᵀ * ·) h
    simp only [Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc, hgP, hPt, Matrix.zero_mul,
      zero_add] at this
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, this]
    abel
  have hR' : P' * S + P * S' = X * W * (Wᵀ * W)⁻¹ := by
    rw [← hR, Matrix.mul_nonsing_inv_cancel_right _ _ hWr]
  have hL' : S' * Wᵀ + S * W'ᵀ = (Pᵀ * P)⁻¹ * (Pᵀ * X) := by
    rw [← hL, Matrix.nonsing_inv_mul_cancel_left _ _ hPr]
  have hS' : S' = (Pᵀ * P)⁻¹ * Pᵀ * X * W * (Wᵀ * W)⁻¹ := by
    have := congrArg (fun A => (Pᵀ * P)⁻¹ * (Pᵀ * A)) hR'
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, hgP, Matrix.zero_mul, zero_add] at this
    rw [Matrix.mul_assoc ((Pᵀ * P)⁻¹) Pᵀ P, Matrix.nonsing_inv_mul _ hPr, Matrix.one_mul] at this
    rw [this]
  refine ⟨?_, hS', ?_⟩
  · have h1 : P' * S = (1 - P * (Pᵀ * P)⁻¹ * Pᵀ) * X * W * (Wᵀ * W)⁻¹ := by
      rw [eq_sub_of_add_eq hR', hS']
      simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    rw [← h1, Matrix.mul_nonsing_inv_cancel_right _ _ hS]
  · have h2 : S * W'ᵀ = (Pᵀ * P)⁻¹ * Pᵀ * X * (1 - W * (Wᵀ * W)⁻¹ * Wᵀ) := by
      rw [eq_sub_of_add_eq' hL', hS']
      simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    have hsymm : ((Pᵀ * P)⁻¹)ᵀ = (Pᵀ * P)⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
    have hsymmW : ((Wᵀ * W)⁻¹)ᵀ = (Wᵀ * W)⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
    have h3 : W' * Sᵀ = (1 - W * (Wᵀ * W)⁻¹ * Wᵀ) * Xᵀ * P * (Pᵀ * P)⁻¹ := by
      have := congrArg Matrix.transpose h2
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_sub,
        Matrix.transpose_one, hsymm, hsymmW, Matrix.mul_assoc] at this
      simpa only [Matrix.mul_assoc] using this
    have hST : IsUnit Sᵀ.det := by rwa [Matrix.det_transpose]
    rw [Matrix.transpose_nonsing_inv, ← h3, Matrix.mul_nonsing_inv_cancel_right _ _ hST]

/-- **Proposition 3.1 of arXiv 2607.03402** (orthogonal sketch DLRA coupled equations;
pointwise form, at a time `t`, derivatives within a set `s` on which they are unique).  Let
`Y(t) = P(t) S(t) W(t)ᵀ` solve the orthogonal sketch DLRA (8), `Ẏ = P_Y F(Y)` with `P_Y` the
projector (7) in the factors (`obliqueTangentProj P P W W`), where `P(t)`, `W(t)` have full
column rank (invertible Gram matrices), `S(t)` is invertible, and the Euclidean gauge
`PᵀṖ = 0`, `WᵀẆ = 0` holds.  Then the factors satisfy (9):
`Ṗ = (I - P(PᵀP)⁻¹Pᵀ) F(PSWᵀ) W (WᵀW)⁻¹ S⁻¹`, `Ṡ = (PᵀP)⁻¹ Pᵀ F(PSWᵀ) W (WᵀW)⁻¹`,
`Ẇ = (I - W(WᵀW)⁻¹Wᵀ) F(PSWᵀ)ᵀ P (PᵀP)⁻¹ S⁻ᵀ`.  The sketch-orthogonality of the initial
factors is not needed here; see `orthSketchDLRA_factorODE` for the trajectory form, where it
replaces the full-rank hypothesis. -/
theorem orthSketchDLRA_factorODE_within {P : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ}
    {W : ℝ → Matrix n r ℝ} {P' : Matrix m r ℝ} {S' : Matrix r r ℝ} {W' : Matrix n r ℝ}
    {F : Matrix m n ℝ → Matrix m n ℝ} {s : Set ℝ} {t : ℝ} (hs : UniqueDiffWithinAt ℝ s t)
    (hP : HasDerivWithinAt P P' s t) (hS : HasDerivWithinAt S S' s t)
    (hW : HasDerivWithinAt W W' s t) (hPr : IsUnit ((P t)ᵀ * P t).det)
    (hWr : IsUnit ((W t)ᵀ * W t).det) (hSr : IsUnit (S t).det) (hgP : (P t)ᵀ * P' = 0)
    (hgW : (W t)ᵀ * W' = 0)
    (hY : HasDerivWithinAt (fun t => P t * S t * (W t)ᵀ)
      (obliqueTangentProj (P t) (P t) (W t) (W t) (F (P t * S t * (W t)ᵀ))) s t) :
    P' = (1 - P t * ((P t)ᵀ * P t)⁻¹ * (P t)ᵀ) * F (P t * S t * (W t)ᵀ) * W t *
        ((W t)ᵀ * W t)⁻¹ * (S t)⁻¹ ∧
      S' = ((P t)ᵀ * P t)⁻¹ * (P t)ᵀ * F (P t * S t * (W t)ᵀ) * W t * ((W t)ᵀ * W t)⁻¹ ∧
      W' = (1 - W t * ((W t)ᵀ * W t)⁻¹ * (W t)ᵀ) * (F (P t * S t * (W t)ᵀ))ᵀ * P t *
        ((P t)ᵀ * P t)⁻¹ * ((S t)⁻¹)ᵀ :=
  gramFactorODE_of_sum_eq hPr hWr hSr hgP hgW
    (hs.eq_deriv _ (GaugeODE.hasDerivWithinAt_factorProduct hP hS hW) hY)

/-- **Proposition 3.1 of arXiv 2607.03402** (trajectory form).  On a convex set `s` with unique
derivatives (e.g. an interval `[a, b]`, `a < b`), let `P, S, W` have derivatives `Ṗ, Ṡ, Ẇ`,
with the Euclidean gauge `PᵀṖ = 0`, `WᵀẆ = 0`, `S(t)` invertible, sketch-orthogonal initial
factors `P(a) ∈ St_Θ(m, r)`, `W(a) ∈ St_Ω(n, r)`, and let `Y = P S Wᵀ` solve the orthogonal
sketch DLRA (8) on `s`.  Then for every `t ∈ s`, `P(t)ᵀP(t) = P(a)ᵀP(a)` and
`W(t)ᵀW(t) = W(a)ᵀW(a)` (so the factors keep full column rank, which the paper assumes and
which is derived here), and the coupled equations (9) hold at `t`. -/
theorem orthSketchDLRA_factorODE {p q : Type*} [Fintype p] [Fintype q]
    {Θ : Matrix p m ℝ} {Ω : Matrix q n ℝ} {P P' : ℝ → Matrix m r ℝ} {S S' : ℝ → Matrix r r ℝ}
    {W W' : ℝ → Matrix n r ℝ} {F : Matrix m n ℝ → Matrix m n ℝ} {s : Set ℝ} (hs : Convex ℝ s)
    (hsu : UniqueDiffOn ℝ s) {a : ℝ} (ha : a ∈ s)
    (hP : ∀ t ∈ s, HasDerivWithinAt P (P' t) s t) (hS : ∀ t ∈ s, HasDerivWithinAt S (S' t) s t)
    (hW : ∀ t ∈ s, HasDerivWithinAt W (W' t) s t)
    (hP₀ : (Θ * P a)ᵀ * (Θ * P a) = 1) (hW₀ : (Ω * W a)ᵀ * (Ω * W a) = 1)
    (hSr : ∀ t ∈ s, IsUnit (S t).det)
    (hgP : ∀ t ∈ s, (P t)ᵀ * P' t = 0) (hgW : ∀ t ∈ s, (W t)ᵀ * W' t = 0)
    (hY : ∀ t ∈ s, HasDerivWithinAt (fun t => P t * S t * (W t)ᵀ)
      (obliqueTangentProj (P t) (P t) (W t) (W t) (F (P t * S t * (W t)ᵀ))) s t)
    {t : ℝ} (ht : t ∈ s) :
    (P t)ᵀ * P t = (P a)ᵀ * P a ∧ (W t)ᵀ * W t = (W a)ᵀ * W a ∧
      P' t = (1 - P t * ((P t)ᵀ * P t)⁻¹ * (P t)ᵀ) * F (P t * S t * (W t)ᵀ) * W t *
        ((W t)ᵀ * W t)⁻¹ * (S t)⁻¹ ∧
      S' t = ((P t)ᵀ * P t)⁻¹ * (P t)ᵀ * F (P t * S t * (W t)ᵀ) * W t * ((W t)ᵀ * W t)⁻¹ ∧
      W' t = (1 - W t * ((W t)ᵀ * W t)⁻¹ * (W t)ᵀ) * (F (P t * S t * (W t)ᵀ))ᵀ * P t *
        ((P t)ᵀ * P t)⁻¹ * ((S t)⁻¹)ᵀ := by
  have hPc : (P t)ᵀ * P t = (P a)ᵀ * P a := transpose_mul_self_eq_of_skew hs hP
    (fun x hx => by rw [hgP x hx, Matrix.transpose_zero, add_zero]) ha ht
  have hWc : (W t)ᵀ * W t = (W a)ᵀ * W a := transpose_mul_self_eq_of_skew hs hW
    (fun x hx => by rw [hgW x hx, Matrix.transpose_zero, add_zero]) ha ht
  have hPr : IsUnit ((P t)ᵀ * P t).det := by rw [hPc]; exact isUnit_det_gram_of_sketch hP₀
  have hWr : IsUnit ((W t)ᵀ * W t).det := by rw [hWc]; exact isUnit_det_gram_of_sketch hW₀
  exact ⟨hPc, hWc, orthSketchDLRA_factorODE_within (hsu t ht) (hP t ht) (hS t ht) (hW t ht) hPr
    hWr (hSr t ht) (hgP t ht) (hgW t ht) (hY t ht)⟩

end OrthSketch

section ExampleOrth

/-- The orthogonal sketch DLRA of the example: `Y(t) = 2 eᵗ`. -/
private lemma ex_hY (t : ℝ) :
    HasDerivWithinAt (fun t => !![(2 : ℝ)] * (Real.exp t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *
        (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ)
      (obliqueTangentProj !![(2 : ℝ)] !![(2 : ℝ)] (1 : Matrix (Fin 1) (Fin 1) ℝ) 1
        (id (!![(2 : ℝ)] * (Real.exp t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *
          (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ))) Set.univ t := by
  have h1 : (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1 = 1 := by simp
  have hP : obliqueTangentProj !![(2 : ℝ)] !![(2 : ℝ)] (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 =
      tangentProj (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    have := obliqueTangentProj_self_mul_right (m := Fin 1) (n := Fin 1) h1 h1
      (R := !![(2 : ℝ)]) (R' := 1) (by simp) (by simp)
    simpa using this
  have hf : (fun t => !![(2 : ℝ)] * (Real.exp t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *
      (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ) = fun t => Real.exp t • !![(2 : ℝ)] := by
    funext t; simp
  rw [hP, tangentProj_apply, hf]
  simp only [id, Matrix.transpose_one, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    add_sub_cancel_right]
  exact ((Real.hasDerivAt_exp t).smul_const !![(2 : ℝ)]).hasDerivWithinAt

/-- Non-vacuity of `orthSketchDLRA_factorODE` with a moving core: `m = n = r = 1`,
`P = 2` (not orthonormal, but sketch-orthonormal for `Θ = 1/2`), `W = 1`, `S(t) = eᵗ`,
`F = id`, so `Y(t) = 2eᵗ` solves (8); (9) then gives `Ṡ = (PᵀP)⁻¹ Pᵀ Y W (WᵀW)⁻¹`. -/
example (t : ℝ) :
    Real.exp t • (1 : Matrix (Fin 1) (Fin 1) ℝ) =
      (!![(2 : ℝ)]ᵀ * !![(2 : ℝ)])⁻¹ * !![(2 : ℝ)]ᵀ *
        (!![(2 : ℝ)] * (Real.exp t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * (1 : Matrix _ _ ℝ)ᵀ) *
        1 * ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1)⁻¹ :=
  (orthSketchDLRA_factorODE (Θ := !![(1 / 2 : ℝ)]) (Ω := (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (P := fun _ => !![(2 : ℝ)]) (P' := fun _ => 0)
    (S := fun t => Real.exp t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (S' := fun t => Real.exp t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (W := fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) (W' := fun _ => 0) (F := id)
    convex_univ uniqueDiffOn_univ (Set.mem_univ 0)
    (fun _ _ => hasDerivWithinAt_const _ _ _)
    (fun t _ => ((Real.hasDerivAt_exp t).smul_const _).hasDerivWithinAt)
    (fun _ _ => hasDerivWithinAt_const _ _ _)
    (by ext i j; fin_cases i; fin_cases j; norm_num [Matrix.mul_apply])
    (by simp) (fun t _ => by simp [Real.exp_ne_zero]) (fun _ _ => by simp)
    (fun _ _ => by simp) (fun t _ => ex_hY t) (Set.mem_univ t)).2.2.2.1

end ExampleOrth

/-! ### Loewner bounds for sketch-orthonormal bases (§5.2) -/

section Loewner

variable {m k p : Type*} [Fintype m] [Fintype k] [Fintype p]

/-- **Sec. 5.2 of arXiv 2607.03402** (Loewner form of the near-orthonormality of sketched bases;
deterministic form).  Let `P : ℝ^{m×k}` and let `Θ : ℝ^{p×m}` ε-embed the range of `P`, in the
sense that `(1-ε)‖Pc‖² ≤ ‖ΘPc‖² ≤ (1+ε)‖Pc‖²` for every coefficient vector `c` (so `Pc` ranges
over `range P`), with `0 ≤ ε < 1`.  If `ΘP` has orthonormal columns, `(ΘP)ᵀ(ΘP) = I`, then
`(1+ε)⁻¹ I ⪯ PᵀP ⪯ (1-ε)⁻¹ I` in the Loewner order.  The paper states this for the RGS output
with an `(r, ε, δ)`-OSE, with probability at least `1 - δ`: see `sketch_embed_loewner_prob`;
`sketch_embed_loewner_of_isEmbeddingOn` takes the embedding hypothesis as `IsEmbeddingOn`. -/
theorem sketch_embed_loewner [DecidableEq k]
    (P : Matrix m k ℝ) (Θ : Matrix p m ℝ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hemb : ∀ c : k → ℝ,
      (1 - ε) * ((P *ᵥ c) ⬝ᵥ (P *ᵥ c)) ≤ (Θ *ᵥ (P *ᵥ c)) ⬝ᵥ (Θ *ᵥ (P *ᵥ c)) ∧
        (Θ *ᵥ (P *ᵥ c)) ⬝ᵥ (Θ *ᵥ (P *ᵥ c)) ≤ (1 + ε) * ((P *ᵥ c) ⬝ᵥ (P *ᵥ c)))
    (hP : (Θ * P)ᵀ * (Θ * P) = 1) :
    ((1 + ε)⁻¹ : ℝ) • (1 : Matrix k k ℝ) ≤ Pᵀ * P ∧
      Pᵀ * P ≤ ((1 - ε)⁻¹ : ℝ) • (1 : Matrix k k ℝ) := by
  have hnorm : ∀ c : k → ℝ, c ⬝ᵥ c = (Θ *ᵥ (P *ᵥ c)) ⬝ᵥ (Θ *ᵥ (P *ᵥ c)) := by
    intro c
    have h := quad_transpose_mul_self (Θ * P) c
    rw [hP, Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at h
    exact h
  have hpos1 : (0 : ℝ) < 1 + ε := by linarith
  have hpos2 : (0 : ℝ) < 1 - ε := by linarith
  have hlow : ∀ c : k → ℝ, (1 + ε)⁻¹ * (c ⬝ᵥ c) ≤ (P *ᵥ c) ⬝ᵥ (P *ᵥ c) := by
    intro c
    have h := (hemb c).2
    rw [← hnorm c] at h
    rw [inv_mul_le_iff₀ hpos1]
    linarith
  have hup : ∀ c : k → ℝ, (P *ᵥ c) ⬝ᵥ (P *ᵥ c) ≤ (1 - ε)⁻¹ * (c ⬝ᵥ c) := by
    intro c
    have h := (hemb c).1
    rw [← hnorm c] at h
    rw [le_inv_mul_iff₀ hpos2]
    linarith
  have hH : (Pᵀ * P).IsHermitian := by
    simpa using Matrix.isHermitian_conjTranspose_mul_self P
  have hI : ∀ a : ℝ, (a • (1 : Matrix k k ℝ)).IsHermitian := fun a => by
    simp [Matrix.IsHermitian]
  constructor
  · rw [Matrix.le_iff]
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hH.sub (hI _))
    intro x
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, quad_transpose_mul_self, smul_eq_mul]
    linarith [hlow x]
  · rw [Matrix.le_iff]
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ((hI _).sub hH)
    intro x
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, quad_transpose_mul_self, smul_eq_mul]
    linarith [hup x]

/-- Non-vacuity: `P = e₁ ∈ ℝ²` and `Θ = I` satisfy the hypotheses of `sketch_embed_loewner`
with `ε = 1/2`, so the conclusion is not vacuous. -/
example :
    ((1 + (1 / 2 : ℝ))⁻¹ : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) ≤
        (!![(1 : ℝ); 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * !![(1 : ℝ); 0] ∧
      (!![(1 : ℝ); 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * !![(1 : ℝ); 0] ≤
        ((1 - (1 / 2 : ℝ))⁻¹ : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  apply sketch_embed_loewner (!![(1 : ℝ); 0] : Matrix (Fin 2) (Fin 1) ℝ)
    (1 : Matrix (Fin 2) (Fin 2) ℝ) (by norm_num) (by norm_num)
  · intro c
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    constructor
    · nlinarith [sq_nonneg (c 0)]
    · nlinarith [sq_nonneg (c 0)]
  · ext i j
    fin_cases i
    all_goals fin_cases j
    all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]

variable [DecidableEq m] [DecidableEq k]

omit [Fintype k] in
/-- **Sec. 5.2 of arXiv 2607.03402** (deterministic form, with `IsEmbeddingOn`): if `Θ`
`ε`-embeds the column space of `P` (`0 ≤ ε < 1`) and `(ΘP)ᵀ(ΘP) = I`, then
`(1+ε)⁻¹ I ⪯ PᵀP ⪯ (1-ε)⁻¹ I`. -/
theorem sketch_embed_loewner_of_isEmbeddingOn [Finite k] {P : Matrix m k ℝ} {Θ : Matrix p m ℝ}
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hΘ : IsEmbeddingOn (Matrix.toEuclideanLin Θ) (colSpan P) ε)
    (hP : (Θ * P)ᵀ * (Θ * P) = 1) :
    ((1 + ε)⁻¹ : ℝ) • (1 : Matrix k k ℝ) ≤ Pᵀ * P ∧
      Pᵀ * P ≤ ((1 - ε)⁻¹ : ℝ) • (1 : Matrix k k ℝ) := by
  have := Fintype.ofFinite k
  refine sketch_embed_loewner P Θ hε0 hε1 (fun c => ?_) hP
  have hmem : WithLp.toLp 2 (P *ᵥ c) ∈ colSpan P := by
    have e : WithLp.toLp 2 (P *ᵥ c) = ∑ j, c j • WithLp.toLp 2 (P.col j) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Matrix.col, mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (toLp_col_mem_colSpan P j)
  have hsq : ∀ v : m → ℝ, ‖WithLp.toLp 2 v‖ ^ 2 = v ⬝ᵥ v := fun v => by
    rw [EuclideanSpace.real_norm_sq_eq]; simp [dotProduct, sq]
  have hsq' : ∀ v : p → ℝ, ‖WithLp.toLp 2 v‖ ^ 2 = v ⬝ᵥ v := fun v => by
    rw [EuclideanSpace.real_norm_sq_eq]; simp [dotProduct, sq]
  have h := hΘ _ hmem
  rw [Matrix.toLpLin_toLp, hsq, hsq', Matrix.toLin'_apply] at h
  exact h

variable {α : Type*} [MeasurableSpace α]

/-- **Sec. 5.2 of arXiv 2607.03402** (probability form).  Let `Θ` be an `OSE(r, ε, δ)` with
`r = card k ≤ m`, `0 ≤ ε < 1`, and let `K ∈ ℝ^{m×r}` be fixed.  If for every draw the basis
`P(ω)` (e.g. produced from `K` by randomized Gram–Schmidt) spans a subspace of `range K` and is
sketch-orthonormal, `(Θ P)ᵀ(Θ P) = I`, then with probability at least `1 - δ`,
`(1+ε)⁻¹ I ⪯ PᵀP ⪯ (1-ε)⁻¹ I`.  (The paper's joint statement for `P` and `W`, with
probability `1 - 2δ`, follows by the union bound as in `twoSidedSketch_prob`.) -/
theorem sketch_embed_loewner_prob {μ : Measure α} [IsProbabilityMeasure μ]
    {Θ : α → Matrix p m ℝ} {ε δ : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hδ : 0 ≤ δ)
    (hΘ : IsOSE μ Θ (Fintype.card k) ε δ) (hk : Fintype.card k ≤ Fintype.card m)
    (K : Matrix m k ℝ) {P : α → Matrix m k ℝ} (hPK : ∀ ω, colSpan (P ω) ≤ colSpan K)
    (hP : ∀ ω, (Θ ω * P ω)ᵀ * (Θ ω * P ω) = 1) :
    ENNReal.ofReal (1 - δ) ≤ μ {ω | ((1 + ε)⁻¹ : ℝ) • (1 : Matrix k k ℝ) ≤ (P ω)ᵀ * P ω ∧
      (P ω)ᵀ * P ω ≤ ((1 - ε)⁻¹ : ℝ) • (1 : Matrix k k ℝ)} := by
  refine ofReal_one_sub_le_measure hδ ?_
  have hdim : finrank ℝ (colSpan K) ≤ Fintype.card k := by
    rw [finrank_colSpan]; exact Matrix.rank_le_card_width K
  refine (measure_mono ?_).trans (hΘ.measure_not_embedding_le hdim hk)
  intro ω hω
  exact fun h' => hω (sketch_embed_loewner_of_isEmbeddingOn hε0 hε1 (h'.mono (hPK ω)) (hP ω))

end Loewner

end LeanDLRA.Literature.P2607_03402
