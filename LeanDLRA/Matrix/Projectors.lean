import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Foundations.Projector
import LeanDLRA.LinearAlgebra.Projection.Defs
import LeanDLRA.FixedRank.Defs

/-!
# Left, right and tangent-space projectors on matrices

For a matrix `U ∈ ℝ^{m × k}` with orthonormal columns (`Uᵀ U = 1`) and `V ∈ ℝ^{n × k'}` with
orthonormal columns, the maps

* `leftProj U  : X ↦ U Uᵀ X` (orthogonal projection onto matrices with column space in
  `range U`), and
* `rightProj V : X ↦ X V Vᵀ` (orthogonal projection onto matrices with row space in `range V`)

are commuting orthogonal projectors on `ℝ^{m × n}` with the Frobenius inner product.  They are the
building blocks of all DLRA integrators: the orthogonal projector onto the tangent space of the
rank-`r` manifold at `Y = U S Vᵀ` is (Koch–Lubich 2007, Lemma 4.1; Lubich–Oseledets,
arXiv 1301.1058, eq. (2.6))

  `P(Y) Z = U Uᵀ Z - U Uᵀ Z V Vᵀ + Z V Vᵀ`,

which is `LeanDLRA.tangent (leftProj U) (rightProj V)` in the abstract calculus of
`LeanDLRA.Foundations.Projector`, and its normal part is `(I - U Uᵀ) Z (I - V Vᵀ)`, the quantity
bounded by `ε` in the robust error analyses (Kieri–Lubich–Walach 2016; Ceruti–Lubich,
arXiv 2010.02022, §2.3, assumption (2.3)).

Main results:

* `isOrthProj_leftProj`, `isOrthProj_rightProj`, `leftProj_rightProj_comm`;
* `tangentProj U V := tangent (leftProj U) (rightProj V)`, its explicit formula, the normal-part
  formula `normal_leftProj_rightProj_apply`, and `isOrthProj_tangentProj`;
* `tangentProj` fixes `U S Vᵀ`, `U B` and `C Vᵀ`, and its range consists exactly of the matrices
  `U B + C Vᵀ` (`mem_range_tangentProj`), the tangent space of Koch–Lubich (2007, §2.1);
* range monotonicity (`U₁ U₁ᵀ U = U`): `leftProj U₁` fixes the range of `leftProj U` and
  `‖(1 - leftProj U₁) X‖ ≤ ‖(1 - leftProj U) X‖` (used for augmented bases in the rank-adaptive
  BUG integrator, Ceruti–Kusch–Lubich, arXiv 2104.05247, §3);
* transposition swaps left and right projectors (used for symmetry preservation,
  Ceruti–Lubich, arXiv 2010.02022, Thm 5).

The column index types of `U` and `V` are allowed to differ, so the same API covers augmented
bases (`[K₁, U₀]` with `2r` columns) and the original bases.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA

variable {k k' m n : Type*} [Fintype k] [Fintype k'] [Fintype m] [Fintype n]

/-! ### Left and right projectors

`leftProj`, `rightProj` and their `_apply` lemmas are defined in
`LeanDLRA/LinearAlgebra/Projection/Defs.lean`. -/

/-- The complementary left projector: `(1 - leftProj U) X = (1 - U Uᵀ) X`. -/
lemma one_sub_leftProj_apply [DecidableEq m] (U : Matrix m k ℝ) (X : Matrix m n ℝ) :
    (1 - leftProj U) X = (1 - U * Uᵀ) * X := by
  simp [Matrix.sub_mul]

/-- The complementary right projector: `(1 - rightProj V) X = X (1 - V Vᵀ)`. -/
lemma one_sub_rightProj_apply [DecidableEq n] (V : Matrix n k ℝ) (X : Matrix m n ℝ) :
    (1 - rightProj V) X = X * (1 - V * Vᵀ) := by
  simp [Matrix.mul_sub, Matrix.mul_assoc]

/-- `leftProj U` is symmetric for every `U`. -/
lemma leftProj_symm (U : Matrix m k ℝ) (X Y : Matrix m n ℝ) :
    ⟪leftProj U X, Y⟫ = ⟪X, leftProj U Y⟫ := by
  simp only [leftProj_apply]
  rw [Frobenius.inner_mul_left, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- `rightProj V` is symmetric for every `V`. -/
lemma rightProj_symm (V : Matrix n k ℝ) (X Y : Matrix m n ℝ) :
    ⟪rightProj V X, Y⟫ = ⟪X, rightProj V Y⟫ := by
  rw [rightProj_apply', rightProj_apply', Frobenius.inner_mul_right, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- `leftProj U` fixes every matrix whose columns lie in the range of `U`. -/
lemma leftProj_mul_left [DecidableEq k] {U : Matrix m k ℝ} (hU : Uᵀ * U = 1)
    (B : Matrix k n ℝ) : leftProj U (U * B) = U * B := by
  rw [leftProj_apply, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul]

/-- `rightProj V` fixes every matrix whose rows lie in the range of `V`. -/
lemma rightProj_mul_transpose [DecidableEq k] {V : Matrix n k ℝ} (hV : Vᵀ * V = 1)
    (C : Matrix m k ℝ) : rightProj V (C * Vᵀ) = C * Vᵀ := by
  rw [rightProj_apply, Matrix.mul_assoc C, Matrix.mul_assoc C, hV, Matrix.one_mul]

/-- `leftProj U` is an orthogonal projector when `U` has orthonormal columns. -/
theorem isOrthProj_leftProj [DecidableEq k] {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) :
    IsOrthProj (leftProj U : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) where
  idem X := by
    simp only [leftProj_apply, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
  symm := leftProj_symm U

/-- `rightProj V` is an orthogonal projector when `V` has orthonormal columns. -/
theorem isOrthProj_rightProj [DecidableEq k] {V : Matrix n k ℝ} (hV : Vᵀ * V = 1) :
    IsOrthProj (rightProj V : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) where
  idem X := by
    simp only [rightProj_apply, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᵀ V, hV, Matrix.one_mul]
  symm := rightProj_symm V

/-- Left and right projectors always commute. -/
theorem leftProj_rightProj_comm (U : Matrix m k ℝ) (V : Matrix n k' ℝ) (X : Matrix m n ℝ) :
    leftProj U (rightProj V X) = rightProj V (leftProj U X) := by
  simp [Matrix.mul_assoc]

/-- The Galerkin (S-step) projection: `U Uᵀ X V Vᵀ = U (Uᵀ X V) Vᵀ`. -/
lemma leftProj_rightProj_apply (U : Matrix m k ℝ) (V : Matrix n k' ℝ) (X : Matrix m n ℝ) :
    leftProj U (rightProj V X) = U * (Uᵀ * X * V) * Vᵀ := by
  simp [Matrix.mul_assoc]

/-- The product `leftProj U * rightProj V` is an orthogonal projector (the Galerkin projector
onto `{U S Vᵀ}`). -/
theorem isOrthProj_leftProj_mul_rightProj [DecidableEq k] [DecidableEq k'] {U : Matrix m k ℝ}
    {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    IsOrthProj (leftProj U * rightProj V : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
  (isOrthProj_leftProj hU).mul (isOrthProj_rightProj hV) (leftProj_rightProj_comm U V)

/-- `leftProj U X = X` iff the columns of `X` lie in the range of `U`. -/
theorem leftProj_eq_self_iff [DecidableEq k] {U : Matrix m k ℝ} (hU : Uᵀ * U = 1)
    (X : Matrix m n ℝ) : leftProj U X = X ↔ ∃ B : Matrix k n ℝ, X = U * B := by
  constructor
  · intro h
    exact ⟨Uᵀ * X, by rw [← Matrix.mul_assoc, ← leftProj_apply, h]⟩
  · rintro ⟨B, rfl⟩
    exact leftProj_mul_left hU B

/-- `rightProj V X = X` iff the rows of `X` lie in the range of `V`. -/
theorem rightProj_eq_self_iff [DecidableEq k] {V : Matrix n k ℝ} (hV : Vᵀ * V = 1)
    (X : Matrix m n ℝ) : rightProj V X = X ↔ ∃ C : Matrix m k ℝ, X = C * Vᵀ := by
  constructor
  · intro h
    exact ⟨X * V, by rw [← rightProj_apply, h]⟩
  · rintro ⟨C, rfl⟩
    exact rightProj_mul_transpose hV C

/-- The coefficient matrix `Uᵀ X` has the norm of the projection `U Uᵀ X`. -/
lemma norm_transpose_mul_eq [DecidableEq k] {U : Matrix m k ℝ} (hU : Uᵀ * U = 1)
    (X : Matrix m n ℝ) : ‖Uᵀ * X‖ = ‖leftProj U X‖ := by
  rw [leftProj_apply, Matrix.mul_assoc, Frobenius.norm_mul_of_orthonormal hU]

/-- Multiplication by `Uᵀ` (with `Uᵀ U = 1`) does not increase the Frobenius norm. -/
lemma norm_transpose_mul_le [DecidableEq k] {U : Matrix m k ℝ} (hU : Uᵀ * U = 1)
    (X : Matrix m n ℝ) : ‖Uᵀ * X‖ ≤ ‖X‖ := by
  rw [norm_transpose_mul_eq hU]
  exact (isOrthProj_leftProj hU).norm_le X

/-- Multiplication by `V` (with `Vᵀ V = 1`) from the right does not increase the norm. -/
lemma norm_mul_le_of_orthonormal [DecidableEq k] {V : Matrix n k ℝ} (hV : Vᵀ * V = 1)
    (X : Matrix m n ℝ) : ‖X * V‖ ≤ ‖X‖ := by
  calc ‖X * V‖ = ‖Vᵀ * Xᵀ‖ := by rw [← Frobenius.norm_transpose (X * V), Matrix.transpose_mul]
    _ ≤ ‖Xᵀ‖ := norm_transpose_mul_le hV Xᵀ
    _ = ‖X‖ := Frobenius.norm_transpose X

/-! ### Transposition swaps left and right -/

/-- `(U Uᵀ X)ᵀ = Xᵀ U Uᵀ`. -/
theorem transpose_leftProj (U : Matrix m k ℝ) (X : Matrix m n ℝ) :
    (leftProj U X)ᵀ = rightProj U Xᵀ := by
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

/-- `(X V Vᵀ)ᵀ = V Vᵀ Xᵀ`. -/
theorem transpose_rightProj (V : Matrix n k ℝ) (X : Matrix m n ℝ) :
    (rightProj V X)ᵀ = leftProj V Xᵀ := by
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

/-! ### The tangent-space projector -/

/- `tangentProj` and `tangentProj_apply` are defined in `LeanDLRA/FixedRank/Defs.lean`. -/

/-- The normal part of the tangent-space splitting: `(I - U Uᵀ) Z (I - V Vᵀ)`. -/
theorem normal_leftProj_rightProj_apply [DecidableEq m] [DecidableEq n] (U : Matrix m k ℝ)
    (V : Matrix n k' ℝ) (Z : Matrix m n ℝ) :
    normal (leftProj U) (rightProj V) Z = (1 - U * Uᵀ) * Z * (1 - V * Vᵀ) := by
  simp only [normal_apply, leftProj_apply, rightProj_apply, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

/-- `Z = P(Y) Z + (I - U Uᵀ) Z (I - V Vᵀ)`. -/
theorem tangentProj_add_normal [DecidableEq m] [DecidableEq n] (U : Matrix m k ℝ)
    (V : Matrix n k' ℝ) (Z : Matrix m n ℝ) :
    tangentProj U V Z + (1 - U * Uᵀ) * Z * (1 - V * Vᵀ) = Z := by
  rw [← normal_leftProj_rightProj_apply, tangentProj, tangent_apply_add_normal_apply]

/-- The normal part written with complementary projectors, in the form used by the abstract
integrator layer: `(1 - P) ((1 - Q) Z) = (I - U Uᵀ) Z (I - V Vᵀ)`. -/
theorem one_sub_leftProj_one_sub_rightProj_apply [DecidableEq m] [DecidableEq n]
    (U : Matrix m k ℝ) (V : Matrix n k' ℝ) (Z : Matrix m n ℝ) :
    (1 - leftProj U) ((1 - rightProj V) Z) = (1 - U * Uᵀ) * Z * (1 - V * Vᵀ) := by
  rw [one_sub_leftProj_apply, one_sub_rightProj_apply, Matrix.mul_assoc]

/-- The tangent-space projector is an orthogonal projector. -/
theorem isOrthProj_tangentProj [DecidableEq k] [DecidableEq k'] {U : Matrix m k ℝ}
    {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    IsOrthProj (tangentProj U V : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
  (isOrthProj_leftProj hU).tangent (isOrthProj_rightProj hV) (leftProj_rightProj_comm U V)

/-- The normal projector `Z ↦ (I - U Uᵀ) Z (I - V Vᵀ)` is an orthogonal projector. -/
theorem isOrthProj_normal_leftProj_rightProj [DecidableEq k] [DecidableEq k']
    {U : Matrix m k ℝ} {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    IsOrthProj (normal (leftProj U) (rightProj V) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
  (isOrthProj_leftProj hU).normal (isOrthProj_rightProj hV) (leftProj_rightProj_comm U V)

/-- Pythagoras for the tangent/normal splitting at `Y = U S Vᵀ`. -/
theorem norm_sq_tangentProj_add_normal [DecidableEq m] [DecidableEq n] [DecidableEq k]
    [DecidableEq k'] {U : Matrix m k ℝ} {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (Z : Matrix m n ℝ) :
    ‖tangentProj U V Z‖ ^ 2 + ‖(1 - U * Uᵀ) * Z * (1 - V * Vᵀ)‖ ^ 2 = ‖Z‖ ^ 2 := by
  rw [← normal_leftProj_rightProj_apply]
  exact (isOrthProj_leftProj hU).norm_sq_tangent_add_normal (isOrthProj_rightProj hV)
    (leftProj_rightProj_comm U V) Z

/-- The tangent-space projector fixes `U B` (only `Uᵀ U = 1` is needed). -/
theorem tangentProj_mul_left [DecidableEq k] {U : Matrix m k ℝ} (hU : Uᵀ * U = 1)
    (V : Matrix n k' ℝ) (B : Matrix k n ℝ) : tangentProj U V (U * B) = U * B := by
  rw [tangentProj, tangent_apply, leftProj_rightProj_comm, leftProj_mul_left hU]
  abel

/-- The tangent-space projector fixes `C Vᵀ` (only `Vᵀ V = 1` is needed). -/
theorem tangentProj_mul_transpose [DecidableEq k'] (U : Matrix m k ℝ) {V : Matrix n k' ℝ}
    (hV : Vᵀ * V = 1) (C : Matrix m k' ℝ) : tangentProj U V (C * Vᵀ) = C * Vᵀ := by
  rw [tangentProj, tangent_apply, rightProj_mul_transpose hV]
  abel

/-- The tangent-space projector at `Y = U S Vᵀ` fixes `Y` itself. -/
theorem tangentProj_mul_mul_transpose [DecidableEq k] {U : Matrix m k ℝ} (hU : Uᵀ * U = 1)
    (V : Matrix n k' ℝ) (S : Matrix k k' ℝ) : tangentProj U V (U * S * Vᵀ) = U * S * Vᵀ := by
  rw [Matrix.mul_assoc]
  exact tangentProj_mul_left hU V _

/-- Fixed points of the tangent-space projector are exactly the matrices `U B + C Vᵀ`. -/
theorem tangentProj_eq_self_iff [DecidableEq k] [DecidableEq k'] {U : Matrix m k ℝ}
    {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (Z : Matrix m n ℝ) :
    tangentProj U V Z = Z ↔ ∃ (B : Matrix k n ℝ) (C : Matrix m k' ℝ), Z = U * B + C * Vᵀ := by
  constructor
  · intro h
    refine ⟨Uᵀ * Z, Z * V - U * Uᵀ * Z * V, ?_⟩
    conv_lhs => rw [← h]
    rw [tangentProj_apply]
    simp only [Matrix.sub_mul, Matrix.mul_assoc]
    abel
  · rintro ⟨B, C, rfl⟩
    rw [map_add, tangentProj_mul_left hU, tangentProj_mul_transpose U hV]

/-- **Tangent space at `Y = U S Vᵀ`.** The range of the tangent-space projector consists exactly of
the matrices `U B + C Vᵀ` (Koch–Lubich 2007, §2.1). -/
theorem mem_range_tangentProj [DecidableEq k] [DecidableEq k'] {U : Matrix m k ℝ}
    {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (Z : Matrix m n ℝ) :
    Z ∈ LinearMap.range (tangentProj U V : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ) ↔
      ∃ (B : Matrix k n ℝ) (C : Matrix m k' ℝ), Z = U * B + C * Vᵀ := by
  rw [LinearMap.mem_range, ← tangentProj_eq_self_iff hU hV]
  simp only [ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨X, rfl⟩
    exact (isOrthProj_tangentProj hU hV).idem X
  · intro h
    exact ⟨Z, h⟩

/-- Transposition maps the tangent projector at `U S Vᵀ` to the one at `V Sᵀ Uᵀ`. -/
theorem transpose_tangentProj (U : Matrix m k ℝ) (V : Matrix n k' ℝ) (Z : Matrix m n ℝ) :
    (tangentProj U V Z)ᵀ = tangentProj V U Zᵀ := by
  simp only [tangentProj_apply, Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]
  abel

/-! ### Range monotonicity (augmented bases) -/

/-- If the range of `U₁` contains the range of `U` (`U₁ U₁ᵀ U = U`), then `leftProj U₁` fixes the
range of `leftProj U`. -/
theorem leftProj_leftProj_of_mul {k₂ : Type*} [Fintype k₂] {U : Matrix m k ℝ}
    {U₁ : Matrix m k₂ ℝ} (h : U₁ * U₁ᵀ * U = U) (X : Matrix m n ℝ) :
    leftProj U₁ (leftProj U X) = leftProj U X := by
  simp only [leftProj_apply]
  rw [show U₁ * U₁ᵀ * (U * Uᵀ * X) = U₁ * U₁ᵀ * U * Uᵀ * X by simp only [Matrix.mul_assoc], h]

/-- If the range of `U₁` contains the range of `U`, then `leftProj U ∘ leftProj U₁ = leftProj U`. -/
theorem leftProj_leftProj_of_mul' {k₂ : Type*} [Fintype k₂] {U : Matrix m k ℝ}
    {U₁ : Matrix m k₂ ℝ} (h : U₁ * U₁ᵀ * U = U) (X : Matrix m n ℝ) :
    leftProj U (leftProj U₁ X) = leftProj U X := by
  have h' : Uᵀ * U₁ * U₁ᵀ = Uᵀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose h
  simp only [leftProj_apply]
  rw [show U * Uᵀ * (U₁ * U₁ᵀ * X) = U * (Uᵀ * U₁ * U₁ᵀ) * X by simp only [Matrix.mul_assoc], h',
    Matrix.mul_assoc]

/-- If the range of `V₁` contains the range of `V` (`V₁ V₁ᵀ V = V`), then `rightProj V₁` fixes the
range of `rightProj V`. -/
theorem rightProj_rightProj_of_mul {k₂ : Type*} [Fintype k₂] {V : Matrix n k ℝ}
    {V₁ : Matrix n k₂ ℝ} (h : V₁ * V₁ᵀ * V = V) (X : Matrix m n ℝ) :
    rightProj V₁ (rightProj V X) = rightProj V X := by
  have h' : Vᵀ * V₁ * V₁ᵀ = Vᵀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose h
  simp only [rightProj_apply]
  rw [show X * V * Vᵀ * V₁ * V₁ᵀ = X * V * (Vᵀ * V₁ * V₁ᵀ) by simp only [Matrix.mul_assoc], h']

/-- If the range of `V₁` contains the range of `V`, then `rightProj V ∘ rightProj V₁ = rightProj V`.
-/
theorem rightProj_rightProj_of_mul' {k₂ : Type*} [Fintype k₂] {V : Matrix n k ℝ}
    {V₁ : Matrix n k₂ ℝ} (h : V₁ * V₁ᵀ * V = V) (X : Matrix m n ℝ) :
    rightProj V (rightProj V₁ X) = rightProj V X := by
  simp only [rightProj_apply]
  rw [show X * V₁ * V₁ᵀ * V * Vᵀ = X * (V₁ * V₁ᵀ * V) * Vᵀ by simp only [Matrix.mul_assoc], h,
    Matrix.mul_assoc X]

/-- **Range monotonicity.** Projecting onto a larger column space `range U₁ ⊇ range U` leaves a
smaller remainder: `‖(1 - leftProj U₁) X‖ ≤ ‖(1 - leftProj U) X‖`. -/
theorem norm_one_sub_leftProj_le {k₂ : Type*} [Fintype k₂] [DecidableEq k₂]
    {U : Matrix m k ℝ} {U₁ : Matrix m k₂ ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (h : U₁ * U₁ᵀ * U = U)
    (X : Matrix m n ℝ) : ‖(1 - leftProj U₁) X‖ ≤ ‖(1 - leftProj U) X‖ := by
  change ‖X - leftProj U₁ X‖ ≤ ‖X - leftProj U X‖
  exact (isOrthProj_leftProj hU₁).norm_sub_le_of_mem_range X _ (leftProj_leftProj_of_mul h X)

/-- **Range monotonicity** for right projectors: `range V₁ ⊇ range V` implies
`‖(1 - rightProj V₁) X‖ ≤ ‖(1 - rightProj V) X‖`. -/
theorem norm_one_sub_rightProj_le {k₂ : Type*} [Fintype k₂] [DecidableEq k₂]
    {V : Matrix n k ℝ} {V₁ : Matrix n k₂ ℝ} (hV₁ : V₁ᵀ * V₁ = 1) (h : V₁ * V₁ᵀ * V = V)
    (X : Matrix m n ℝ) : ‖(1 - rightProj V₁) X‖ ≤ ‖(1 - rightProj V) X‖ := by
  change ‖X - rightProj V₁ X‖ ≤ ‖X - rightProj V X‖
  exact (isOrthProj_rightProj hV₁).norm_sub_le_of_mem_range X _ (rightProj_rightProj_of_mul h X)

/-- Jointly satisfiable hypotheses: the identity basis is orthonormal and contains every range. -/
example [DecidableEq m] (U : Matrix m k ℝ) :
    (1 : Matrix m m ℝ)ᵀ * 1 = 1 ∧ (1 : Matrix m m ℝ) * (1 : Matrix m m ℝ)ᵀ * U = U := by
  simp

end LeanDLRA
