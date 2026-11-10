import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Topology.UniformSpace.Matrix

/-!
# Definitions: the Frobenius structure on real matrices

The vocabulary of layer 1 (`LinearAlgebra/`) for matrices. Dynamical low-rank approximation works
on `ℝ^{m × n}` with the Frobenius inner product `⟪A, B⟫ = ∑ᵢ ∑ⱼ Aᵢⱼ Bᵢⱼ = tr (Aᵀ B)`.
Mathlib provides the Frobenius norm only as non-instance definitions
(`Matrix.frobeniusNormedAddCommGroup`, `Matrix.frobeniusNormedSpace`), because several matrix norms
are natural. This file registers them as *scoped* instances, activated by
`open scoped LeanDLRA.Frobenius`, builds the inner product space on top of them, and packages the
matrix operations used everywhere in the library as continuous linear maps.

The theorems about these objects (adjoint identities, trace formula, isometries, product rules)
are in `LeanDLRA/Matrix/Frobenius.lean`.

## Main definitions

* `LeanDLRA.Frobenius.innerProductSpace`: the scoped Frobenius inner product space structure on
  `Matrix m n ℝ`, whose norm is definitionally Mathlib's Frobenius norm.
* `LeanDLRA.Frobenius.leftMulCLM`, `rightMulCLM`, `mulCLM`, `transposeCLM`, `transposeLIE`:
  `X ↦ M X`, `X ↦ X M`, `(A, B) ↦ A B` and `X ↦ Xᵀ` as continuous (bi)linear maps.
* `LeanDLRA.Frobenius.sandwichCLM`, `sandwichTransposeCLM`: `X ↦ M X N` and `X ↦ M Xᵀ N`.
* `LeanDLRA.Frobenius.weightedInner`: the weighted (quadrature) inner product
  `∑ᵢ ∑ⱼ wxᵢ wvⱼ Xᵢⱼ Yᵢⱼ` of kinetic discretizations.
* `LeanDLRA.Curvature.specNorm`: the spectral norm `‖A‖₂`, the operator norm of `x ↦ A x` on
  Euclidean spaces.

## Main results

* `LeanDLRA.Frobenius.inner_def`, `norm_sq_eq_sum`, `norm_def`: the inner product and the norm
  entrywise.
* `LeanDLRA.Frobenius.weightedInner_eq_inner`: for nonnegative weights, the weighted inner product
  is the Frobenius inner product after scaling by `diag(√wx)` and `diag(√wv)`.

## Implementation notes

The instances are scoped, never global, so that other matrix norms remain available. The
topology and uniformity of the Frobenius norm are given high priority inside the scope; they are
definitionally Mathlib's product topology and uniformity (`frobeniusTopologicalSpace_eq`,
`frobeniusUniformSpace_eq`), and the `example`s below check that there is no instance diamond.

The deprecated aliases at the end record the duplicate definitions this file replaced:
`Exactness.sandwichCLM`, `Exactness.sandwichTransposeCLM` (renamed), `GaugeODE.mulBilin` and
`GaugeODE.transposeCLM` (equal to `mulCLM` and `transposeCLM`). `RandomizedBUG.mulTransposeCLM Q`
was `sandwichTransposeCLM Q 1`.

## References

* [KochLubich2007, §2]
-/

open scoped Matrix RealInnerProductSpace

namespace LeanDLRA.Frobenius

attribute [scoped instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {k l m n : Type*} [Fintype k] [Fintype l] [Fintype m] [Fintype n]

/-! ### Topology and completeness -/

/-- The uniform structure of the Frobenius norm. Mathlib also has a global product uniformity
`Matrix.instUniformSpace`; the two are definitionally equal, but only after unfolding
definitions, so the Frobenius one gets high priority inside the scope. This makes all statements
about matrices elaborate with the instances that the abstract (normed-space) API expects. -/
noncomputable scoped instance (priority := high) frobeniusUniformSpace :
    UniformSpace (Matrix m n ℝ) :=
  PseudoMetricSpace.toUniformSpace

/-- The topology of the Frobenius norm (definitionally the product topology, see
`frobeniusTopologicalSpace_eq`), preferred inside the scope for the same reason as
`frobeniusUniformSpace`. -/
noncomputable scoped instance (priority := high) frobeniusTopologicalSpace :
    TopologicalSpace (Matrix m n ℝ) :=
  UniformSpace.toTopologicalSpace

/-- The Frobenius topology is Mathlib's (product) topology on matrices. -/
theorem frobeniusTopologicalSpace_eq :
    (frobeniusTopologicalSpace : TopologicalSpace (Matrix m n ℝ)) =
      (inferInstanceAs (TopologicalSpace (m → n → ℝ))) := rfl

/-- The Frobenius uniformity is Mathlib's (product) uniformity on matrices. -/
theorem frobeniusUniformSpace_eq :
    (frobeniusUniformSpace : UniformSpace (Matrix m n ℝ)) = Matrix.instUniformSpace m n ℝ := rfl

/-- No instance diamond with the abstract API: the scoped topology is the one induced by the
scoped Frobenius normed group, even at instance transparency. -/
example : (frobeniusTopologicalSpace : TopologicalSpace (Matrix m n ℝ)) =
    (Matrix.frobeniusNormedAddCommGroup :
      NormedAddCommGroup (Matrix m n ℝ)).toUniformSpace.toTopologicalSpace := by
  with_reducible_and_instances rfl

/-- `Matrix m n ℝ` is complete for the Frobenius norm. -/
scoped instance completeSpace : CompleteSpace (Matrix m n ℝ) :=
  FiniteDimensional.complete ℝ _

/-! ### The Frobenius norm and inner product -/

/-- The squared Frobenius norm is the sum of the squared entries. -/
theorem norm_sq_eq_sum (A : Matrix m n ℝ) : ‖A‖ ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  change ‖WithLp.toLp 2 fun i => WithLp.toLp 2 fun j => A i j‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  congr 1; ext i
  rw [PiLp.norm_sq_eq_of_L2]
  simp

/-- The Frobenius norm `‖A‖ = √(∑ᵢ ∑ⱼ Aᵢⱼ²)`. -/
theorem norm_def (A : Matrix m n ℝ) : ‖A‖ = √(∑ i, ∑ j, A i j ^ 2) := by
  rw [← norm_sq_eq_sum, Real.sqrt_sq (norm_nonneg A)]

/-- The Frobenius inner product `⟪A, B⟫ = ∑ᵢ ∑ⱼ Aᵢⱼ Bᵢⱼ` on real `m × n` matrices. Its
underlying normed space is Mathlib's `Matrix.frobeniusNormedSpace`, so the norm induced by the
inner product is (definitionally) the Frobenius norm. -/
noncomputable scoped instance innerProductSpace : InnerProductSpace ℝ (Matrix m n ℝ) where
  toNormedSpace := Matrix.frobeniusNormedSpace
  inner A B := ∑ i, ∑ j, A i j * B i j
  norm_sq_eq_re_inner A := by
    rw [norm_sq_eq_sum, RCLike.re_to_real]
    simp only [sq]
  conj_inner_symm A B := by
    simp only [conj_trivial]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  add_left A B C := by
    simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  smul_left A B r := by
    simp only [Matrix.smul_apply, smul_eq_mul, conj_trivial, Finset.mul_sum, mul_assoc]

/-- The Frobenius inner product is the sum of the entrywise products. -/
theorem inner_def (A B : Matrix m n ℝ) : ⟪A, B⟫ = ∑ i, ∑ j, A i j * B i j := rfl

/-- No instance diamond: the normed space structure underlying the inner product space is
Mathlib's Frobenius normed space, even at instance transparency. -/
example : (innerProductSpace.toNormedSpace : NormedSpace ℝ (Matrix m n ℝ)) =
    Matrix.frobeniusNormedSpace := by
  with_reducible_and_instances rfl

/-- No instance diamond: the norm induced by the inner product is the Frobenius norm. -/
example (A : Matrix m n ℝ) : ‖A‖ = √(∑ i, ∑ j, A i j ^ 2) ∧ ‖A‖ ^ 2 = ⟪A, A⟫ :=
  ⟨norm_def A, (real_inner_self_eq_norm_sq A).symm⟩

/-- The module structure of the Frobenius normed space is the usual one on matrices. -/
example : (Matrix.frobeniusNormedSpace : NormedSpace ℝ (Matrix m n ℝ)).toModule =
    Matrix.module := by
  with_reducible_and_instances rfl

/-- Transposition preserves the Frobenius norm. -/
theorem norm_transpose (A : Matrix m n ℝ) : ‖Aᵀ‖ = ‖A‖ :=
  Matrix.frobenius_norm_transpose A

/-- Submultiplicativity of the Frobenius norm for rectangular matrices. -/
theorem norm_mul_le (A : Matrix m l ℝ) (B : Matrix l n ℝ) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ :=
  Matrix.frobenius_norm_mul A B

end LeanDLRA.Frobenius

/-! ### The spectral norm -/

namespace LeanDLRA.Curvature

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The spectral norm `‖A‖₂` of a real matrix: the operator norm of `x ↦ A x` on Euclidean
spaces. It agrees with Mathlib's `Matrix.instL2OpNormedAddCommGroup` (`specNorm_eq_l2` in
`LeanDLRA/Matrix/Curvature.lean`), but is given a separate name so that it can be used alongside
the Frobenius norm. -/
noncomputable def specNorm (A : Matrix m n ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖

end LeanDLRA.Curvature

namespace LeanDLRA.Frobenius

variable {k l m n : Type*} [Fintype k] [Fintype l] [Fintype m] [Fintype n]

/-! ### Matrix operations as continuous linear maps -/

/-- Transposition as a linear isometric equivalence for the Frobenius norm. -/
noncomputable def transposeLIE : Matrix m n ℝ ≃ₗᵢ[ℝ] Matrix n m ℝ :=
  { Matrix.transposeLinearEquiv m n ℝ ℝ with norm_map' := norm_transpose }

/-- `transposeLIE A = Aᵀ`. -/
@[simp] theorem transposeLIE_apply (A : Matrix m n ℝ) : transposeLIE A = Aᵀ := rfl

/-- The inverse of `transposeLIE` is again transposition. -/
@[simp] theorem transposeLIE_symm_apply (A : Matrix n m ℝ) :
    (transposeLIE : Matrix m n ℝ ≃ₗᵢ[ℝ] Matrix n m ℝ).symm A = Aᵀ := rfl

/-- Left multiplication `X ↦ M X` as a continuous linear map (operator norm `≤ ‖M‖`). -/
noncomputable def leftMulCLM (M : Matrix m l ℝ) : Matrix l n ℝ →L[ℝ] Matrix m n ℝ :=
  LinearMap.mkContinuous
    { toFun := fun X => M * X
      map_add' := Matrix.mul_add M
      map_smul' := fun c X => Matrix.mul_smul M c X }
    ‖M‖ fun X => norm_mul_le M X

/-- `leftMulCLM M X = M X`. -/
@[simp] theorem leftMulCLM_apply (M : Matrix m l ℝ) (X : Matrix l n ℝ) :
    leftMulCLM M X = M * X := rfl

/-- Left multiplication by `M` has operator norm at most the Frobenius norm `‖M‖`. -/
theorem norm_leftMulCLM_le (M : Matrix m l ℝ) :
    ‖(leftMulCLM M : Matrix l n ℝ →L[ℝ] Matrix m n ℝ)‖ ≤ ‖M‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg M) _

/-- Right multiplication `X ↦ X M` as a continuous linear map (operator norm `≤ ‖M‖`). -/
noncomputable def rightMulCLM (M : Matrix l n ℝ) : Matrix m l ℝ →L[ℝ] Matrix m n ℝ :=
  LinearMap.mkContinuous
    { toFun := fun X => X * M
      map_add' := fun X Y => Matrix.add_mul X Y M
      map_smul' := fun c X => Matrix.smul_mul c X M }
    ‖M‖ fun X => by rw [mul_comm]; exact norm_mul_le X M

/-- `rightMulCLM M X = X M`. -/
@[simp] theorem rightMulCLM_apply (M : Matrix l n ℝ) (X : Matrix m l ℝ) :
    rightMulCLM M X = X * M := rfl

/-- Right multiplication by `M` has operator norm at most the Frobenius norm `‖M‖`. -/
theorem norm_rightMulCLM_le (M : Matrix l n ℝ) :
    ‖(rightMulCLM M : Matrix m l ℝ →L[ℝ] Matrix m n ℝ)‖ ≤ ‖M‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg M) _

/-- Matrix multiplication `(A, B) ↦ A B` as a continuous bilinear map. -/
noncomputable def mulCLM : Matrix m l ℝ →L[ℝ] Matrix l n ℝ →L[ℝ] Matrix m n ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun A B => A * B) Matrix.add_mul (fun c A B => Matrix.smul_mul c A B)
      Matrix.mul_add (fun c A B => Matrix.mul_smul A c B))
    1 fun A B => by rw [one_mul]; exact norm_mul_le A B

/-- `mulCLM A B = A B`. -/
@[simp] theorem mulCLM_apply (A : Matrix m l ℝ) (B : Matrix l n ℝ) : mulCLM A B = A * B := rfl

/-- Transposition as a continuous linear map. -/
noncomputable def transposeCLM : Matrix m n ℝ →L[ℝ] Matrix n m ℝ :=
  LinearMap.mkContinuous (Matrix.transposeLinearEquiv m n ℝ ℝ).toLinearMap 1
    fun A => by rw [one_mul]; exact (norm_transpose A).le

/-- `transposeCLM A = Aᵀ`. -/
@[simp] theorem transposeCLM_apply (A : Matrix m n ℝ) : transposeCLM A = Aᵀ := rfl

/-- The two-sided multiplication `X ↦ M X N` as a continuous linear map. -/
noncomputable def sandwichCLM {p q : Type*} [Fintype p] [Fintype q] (M : Matrix p m ℝ)
    (N : Matrix n q ℝ) : Matrix m n ℝ →L[ℝ] Matrix p q ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => M * X * N
      map_add' := fun X Y => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }

/-- `sandwichCLM M N X = M X N`. -/
@[simp] theorem sandwichCLM_apply {p q : Type*} [Fintype p] [Fintype q] (M : Matrix p m ℝ)
    (N : Matrix n q ℝ) (X : Matrix m n ℝ) : sandwichCLM M N X = M * X * N := rfl

/-- The two-sided multiplication of the transpose, `X ↦ M Xᵀ N`, as a continuous linear map. -/
noncomputable def sandwichTransposeCLM {p q : Type*} [Fintype p] [Fintype q] (M : Matrix p n ℝ)
    (N : Matrix m q ℝ) : Matrix m n ℝ →L[ℝ] Matrix p q ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => M * Xᵀ * N
      map_add' := fun X Y => by rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]; rfl }

/-- `sandwichTransposeCLM M N X = M Xᵀ N`. -/
@[simp] theorem sandwichTransposeCLM_apply {p q : Type*} [Fintype p] [Fintype q]
    (M : Matrix p n ℝ) (N : Matrix m q ℝ) (X : Matrix m n ℝ) :
    sandwichTransposeCLM M N X = M * Xᵀ * N := rfl

/-- The sandwich map is the composition of a right and a left multiplication. -/
theorem sandwichCLM_eq_comp {p q : Type*} [Fintype p] [Fintype q] (M : Matrix p m ℝ)
    (N : Matrix n q ℝ) : sandwichCLM M N = (rightMulCLM N).comp (leftMulCLM M) :=
  ContinuousLinearMap.ext fun _ => rfl

/-- The transposed sandwich map is the sandwich map composed with transposition. -/
theorem sandwichTransposeCLM_eq_comp {p q : Type*} [Fintype p] [Fintype q] (M : Matrix p n ℝ)
    (N : Matrix m q ℝ) : sandwichTransposeCLM M N = (sandwichCLM M N).comp transposeCLM :=
  ContinuousLinearMap.ext fun _ => rfl

/-! ### The weighted (quadrature) inner product -/

/-- The weighted inner product `∑ᵢ ∑ⱼ wxᵢ wvⱼ Xᵢⱼ Yᵢⱼ` of two matrices, with row weights `wx` and
column weights `wv`: the discrete `L²` inner product of phase-space functions `f(xᵢ, vⱼ)` for a
quadrature with weights `wx` in space and `wv` in velocity. It is a genuine inner product for
positive weights; `weightedInner_eq_inner` reduces it to the Frobenius inner product. -/
def weightedInner (wx : m → ℝ) (wv : n → ℝ) (X Y : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, wx i * wv j * X i j * Y i j

/-- The weighted inner product is symmetric. -/
theorem weightedInner_comm (wx : m → ℝ) (wv : n → ℝ) (X Y : Matrix m n ℝ) :
    weightedInner wx wv X Y = weightedInner wx wv Y X := by
  simp only [weightedInner]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- With unit weights the weighted inner product is the Frobenius inner product. -/
theorem weightedInner_one (X Y : Matrix m n ℝ) :
    weightedInner (fun _ => 1) (fun _ => 1) X Y = ⟪X, Y⟫ := by
  simp only [weightedInner, inner_def, one_mul]

/-- **Isometry to the Frobenius space.** For nonnegative weights, the weighted inner product is
the Frobenius inner product of the scaled matrices `diag(√wx) X diag(√wv)`. -/
theorem weightedInner_eq_inner [DecidableEq m] [DecidableEq n] {wx : m → ℝ} {wv : n → ℝ}
    (hwx : ∀ i, 0 ≤ wx i) (hwv : ∀ j, 0 ≤ wv j) (X Y : Matrix m n ℝ) :
    weightedInner wx wv X Y =
      ⟪Matrix.diagonal (fun i => √(wx i)) * X * Matrix.diagonal (fun j => √(wv j)),
        Matrix.diagonal (fun i => √(wx i)) * Y * Matrix.diagonal (fun j => √(wv j))⟫ := by
  simp only [weightedInner, inner_def, Matrix.diagonal_mul, Matrix.mul_diagonal]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  linear_combination (-(wv j * X i j * Y i j)) * Real.mul_self_sqrt (hwx i) +
    (-(√(wx i) * √(wx i) * X i j * Y i j)) * Real.mul_self_sqrt (hwv j)

end LeanDLRA.Frobenius

/-! ### Deprecated names -/

namespace LeanDLRA

@[deprecated (since := "2026-11-09")] alias Exactness.sandwichCLM := Frobenius.sandwichCLM
@[deprecated (since := "2026-11-09")] alias Exactness.sandwichTransposeCLM :=
  Frobenius.sandwichTransposeCLM
@[deprecated (since := "2026-11-09")] alias GaugeODE.mulBilin := Frobenius.mulCLM
@[deprecated (since := "2026-11-09")] alias GaugeODE.mulBilin_apply := Frobenius.mulCLM_apply
@[deprecated (since := "2026-11-09")] alias GaugeODE.transposeCLM := Frobenius.transposeCLM
@[deprecated (since := "2026-11-09")] alias GaugeODE.transposeCLM_apply :=
  Frobenius.transposeCLM_apply

end LeanDLRA

/-! ### The weighted matrix space (decision Q5) -/

namespace LeanDLRA

open Matrix

variable {m n : Type*}

/-- **The weighted matrix space**: `Matrix m n ℝ` with the weighted (quadrature) inner product
`Frobenius.weightedInner wx wv`, `⟪X, Y⟫ = ∑ᵢ ∑ⱼ wxᵢ wvⱼ Xᵢⱼ Yᵢⱼ`, as a type synonym. For positive
weights (instances `Fact (∀ i, 0 < wx i)` and `Fact (∀ j, 0 < wv j)`) it is a real inner product
space whose norm is the discrete weighted `L²` norm of kinetic discretizations, so every abstract
inner-product theorem of the library applies to weighted norms directly.
`WeightedMatrix.toFrobenius` is the isometry `X ↦ diag(√wx) X diag(√wv)` onto the Frobenius space.
Matrices are converted with `WeightedMatrix.toWeighted` and `WeightedMatrix.ofWeighted` (both the
identity). -/
def WeightedMatrix (_wx : m → ℝ) (_wv : n → ℝ) : Type _ := Matrix m n ℝ

namespace WeightedMatrix

variable {wx : m → ℝ} {wv : n → ℝ}

instance : AddCommGroup (WeightedMatrix wx wv) := inferInstanceAs (AddCommGroup (Matrix m n ℝ))

instance : Module ℝ (WeightedMatrix wx wv) := inferInstanceAs (Module ℝ (Matrix m n ℝ))

/-- A matrix as an element of the weighted space (the identity map). -/
def toWeighted : Matrix m n ℝ ≃ₗ[ℝ] WeightedMatrix wx wv := LinearEquiv.refl ℝ _

/-- The matrix underlying an element of the weighted space (the identity map). -/
def ofWeighted : WeightedMatrix wx wv ≃ₗ[ℝ] Matrix m n ℝ := LinearEquiv.refl ℝ _

@[simp]
theorem ofWeighted_toWeighted (X : Matrix m n ℝ) :
    ofWeighted (toWeighted (wx := wx) (wv := wv) X) = X := rfl

@[simp]
theorem toWeighted_ofWeighted (X : WeightedMatrix wx wv) : toWeighted (ofWeighted X) = X := rfl

variable [Fintype m] [Fintype n]

/-- The weighted inner product `⟪X, Y⟫ = ∑ᵢ ∑ⱼ wxᵢ wvⱼ Xᵢⱼ Yᵢⱼ` (defined for all weights; an inner
product for positive ones). -/
noncomputable instance : Inner ℝ (WeightedMatrix wx wv) :=
  ⟨fun X Y => Frobenius.weightedInner wx wv (ofWeighted X) (ofWeighted Y)⟩

/-- The inner product of the weighted space is `Frobenius.weightedInner`. -/
theorem inner_def (X Y : WeightedMatrix wx wv) :
    ⟪X, Y⟫ = Frobenius.weightedInner wx wv (ofWeighted X) (ofWeighted Y) := rfl

variable [hx : Fact (∀ i, 0 < wx i)] [hv : Fact (∀ j, 0 < wv j)]

omit [Fintype m] [Fintype n] in
private theorem weight_mul_self_nonneg (X : WeightedMatrix wx wv) (i : m) (j : n) :
    0 ≤ wx i * wv j * ofWeighted X i j * ofWeighted X i j := by
  have h1 := (hx.out i).le
  have h2 := (hv.out j).le
  have e : wx i * wv j * ofWeighted X i j * ofWeighted X i j =
      wx i * wv j * (ofWeighted X i j * ofWeighted X i j) := by ring
  rw [e]
  exact mul_nonneg (mul_nonneg h1 h2) (mul_self_nonneg _)

/-- For positive weights the weighted space is a normed group, with the norm of the weighted inner
product. -/
noncomputable instance : NormedAddCommGroup (WeightedMatrix wx wv) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (WeightedMatrix wx wv) _ _ _
    { toInner := inferInstance
      conj_inner_symm := fun X Y => by
        simp only [conj_trivial, inner_def]
        exact Frobenius.weightedInner_comm wx wv _ _
      re_inner_nonneg := fun X => by
        simp only [RCLike.re_to_real, inner_def, Frobenius.weightedInner]
        exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          weight_mul_self_nonneg X i j
      definite := fun X h => by
        change Frobenius.weightedInner wx wv (ofWeighted X) (ofWeighted X) = 0 at h
        have h0 : ∀ i j, wx i * wv j * ofWeighted X i j * ofWeighted X i j = 0 := by
          intro i j
          have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
            weight_mul_self_nonneg X i j).1 h i (Finset.mem_univ i)
          exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
            weight_mul_self_nonneg X i j).1 hi j (Finset.mem_univ j)
        apply ofWeighted.injective
        ext i j
        have hw : wx i * wv j ≠ 0 := mul_ne_zero (hx.out i).ne' (hv.out j).ne'
        have e : wx i * wv j * (ofWeighted X i j * ofWeighted X i j) = 0 := by
          rw [← h0 i j]; ring
        simpa using (mul_eq_zero.1 e).resolve_left hw
      add_left := fun X Y Z => by
        simp only [inner_def, Frobenius.weightedInner, map_add, Matrix.add_apply, mul_add,
          add_mul, Finset.sum_add_distrib]
      smul_left := fun X Y r => by
        simp only [inner_def, Frobenius.weightedInner, map_smul, Matrix.smul_apply, smul_eq_mul,
          conj_trivial, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring }

/-- For positive weights the weighted space is a real inner product space. -/
noncomputable instance : InnerProductSpace ℝ (WeightedMatrix wx wv) :=
  InnerProductSpace.ofCore _

/-- The squared norm of the weighted space is the weighted sum of squares. -/
theorem norm_sq_eq (X : WeightedMatrix wx wv) :
    ‖X‖ ^ 2 = ∑ i, ∑ j, wx i * wv j * ofWeighted X i j ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_def, Frobenius.weightedInner]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable [DecidableEq m] [DecidableEq n]

open scoped Frobenius in
/-- **Isometry to the Frobenius space** (decision Q5): for positive weights,
`X ↦ diag(√wx) X diag(√wv)` is a linear isometric equivalence of the weighted space onto
`Matrix m n ℝ` with the Frobenius inner product (`Frobenius.weightedInner_eq_inner`). -/
noncomputable def toFrobenius : WeightedMatrix wx wv ≃ₗᵢ[ℝ] Matrix m n ℝ :=
  LinearEquiv.isometryOfInner
    { toFun := fun X => diagonal (fun i => √(wx i)) * ofWeighted X * diagonal (fun j => √(wv j))
      map_add' := fun X Y => by
        simp only [map_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r X => by
        simp only [map_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
      invFun := fun Y => toWeighted
        (diagonal (fun i => (√(wx i))⁻¹) * Y * diagonal (fun j => (√(wv j))⁻¹))
      left_inv := fun X => by
        have h1 : diagonal (fun i => (√(wx i))⁻¹) * diagonal (fun i => √(wx i)) = 1 := by
          rw [diagonal_mul_diagonal, ← diagonal_one]
          congr 1; funext i
          exact inv_mul_cancel₀ (Real.sqrt_pos.2 (hx.out i)).ne'
        have h2 : diagonal (fun j => √(wv j)) * diagonal (fun j => (√(wv j))⁻¹) = 1 := by
          rw [diagonal_mul_diagonal, ← diagonal_one]
          congr 1; funext j
          exact mul_inv_cancel₀ (Real.sqrt_pos.2 (hv.out j)).ne'
        change toWeighted (diagonal (fun i => (√(wx i))⁻¹) *
          (diagonal (fun i => √(wx i)) * ofWeighted X * diagonal (fun j => √(wv j))) *
            diagonal (fun j => (√(wv j))⁻¹)) = X
        calc _ = toWeighted (diagonal (fun i => (√(wx i))⁻¹) * diagonal (fun i => √(wx i)) *
              ofWeighted X * (diagonal (fun j => √(wv j)) * diagonal (fun j => (√(wv j))⁻¹))) := by
              simp only [Matrix.mul_assoc]
          _ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one, toWeighted_ofWeighted]
      right_inv := fun Y => by
        have h1 : diagonal (fun i => √(wx i)) * diagonal (fun i => (√(wx i))⁻¹) = 1 := by
          rw [diagonal_mul_diagonal, ← diagonal_one]
          congr 1; funext i
          exact mul_inv_cancel₀ (Real.sqrt_pos.2 (hx.out i)).ne'
        have h2 : diagonal (fun j => (√(wv j))⁻¹) * diagonal (fun j => √(wv j)) = 1 := by
          rw [diagonal_mul_diagonal, ← diagonal_one]
          congr 1; funext j
          exact inv_mul_cancel₀ (Real.sqrt_pos.2 (hv.out j)).ne'
        change diagonal (fun i => √(wx i)) * ofWeighted (toWeighted (diagonal
          (fun i => (√(wx i))⁻¹) * Y * diagonal (fun j => (√(wv j))⁻¹))) *
            diagonal (fun j => √(wv j)) = Y
        rw [ofWeighted_toWeighted]
        calc _ = diagonal (fun i => √(wx i)) * diagonal (fun i => (√(wx i))⁻¹) * Y *
              (diagonal (fun j => (√(wv j))⁻¹) * diagonal (fun j => √(wv j))) := by
              simp only [Matrix.mul_assoc]
          _ = Y := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one] }
    fun X Y => (Frobenius.weightedInner_eq_inner (fun i => (hx.out i).le)
      (fun j => (hv.out j).le) (ofWeighted X) (ofWeighted Y)).symm

open scoped Frobenius in
/-- `toFrobenius X = diag(√wx) X diag(√wv)`. -/
theorem toFrobenius_apply (X : WeightedMatrix wx wv) :
    toFrobenius X = diagonal (fun i => √(wx i)) * ofWeighted X * diagonal (fun j => √(wv j)) :=
  rfl

open scoped Frobenius in
/-- The weighted inner product is the Frobenius inner product of the scaled matrices. -/
theorem inner_toFrobenius (X Y : WeightedMatrix wx wv) :
    ⟪toFrobenius X, toFrobenius Y⟫ = ⟪X, Y⟫ :=
  toFrobenius.inner_map_map X Y

open scoped Frobenius in
/-- The weighted norm is the Frobenius norm of the scaled matrix. -/
theorem norm_toFrobenius (X : WeightedMatrix wx wv) : ‖toFrobenius X‖ = ‖X‖ :=
  toFrobenius.norm_map X

end WeightedMatrix

section Example

private theorem fact_two_pos : Fact (∀ _ : Fin 1, (0 : ℝ) < 2) := ⟨fun _ => two_pos⟩

private theorem fact_one_pos : Fact (∀ _ : Fin 1, (0 : ℝ) < 1) := ⟨fun _ => one_pos⟩

attribute [local instance] fact_two_pos fact_one_pos

/-- Non-vacuity: with weights `wx = 2`, `wv = 1` on `1 × 1` matrices, `‖1‖² = 2`. -/
example : ‖(WeightedMatrix.toWeighted 1 :
    WeightedMatrix (fun _ : Fin 1 => (2 : ℝ)) fun _ : Fin 1 => (1 : ℝ))‖ ^ 2 = 2 := by
  rw [WeightedMatrix.norm_sq_eq]
  simp

end Example

end LeanDLRA
