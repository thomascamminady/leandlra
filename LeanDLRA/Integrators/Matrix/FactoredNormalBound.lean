import LeanDLRA.Integrators.Matrix.Defs
import LeanDLRA.Matrix.Projectors

/-!
# Mixed components of a field under the factored normal bound

The factored normal bound `LeanDLRA.FactoredNormalBoundOn F r D ε` controls the doubly normal
component `(1 - U Uᵀ) F(t, U S Vᵀ) (1 - V Vᵀ)` at every factored point, rank-deficient ones
included. Together with a Lipschitz bound it also controls the *mixed* components (one factor
inside the column space, the other outside the row space, or the other way round) in the
directions in which `S` is small:

* `LeanDLRA.norm_col_transpose_mul_field_mul_normal_le`: for a unit column `a`,
  `‖(U a)ᵀ F(t, U S Vᵀ) (1 - V Vᵀ)‖ ≤ ε + L ‖aᵀ S‖`;
* `LeanDLRA.norm_normal_mul_field_mul_col_le`: the transposed form, for a unit column `b`,
  `‖(1 - U Uᵀ) F(t, U S Vᵀ) (V b)‖ ≤ ε + L ‖S b‖`;
* `LeanDLRA.norm_normal_mul_field_mul_le` and
  `LeanDLRA.norm_transpose_mul_field_mul_normal_le`: the homogeneous forms for every column `c`,
  `‖(1 - U Uᵀ) F(t, U S Vᵀ) (V c)‖ ≤ ε ‖c‖ + L ‖S c‖` and
  `‖(U c)ᵀ F(t, U S Vᵀ) (1 - V Vᵀ)‖ ≤ ε ‖c‖ + L ‖cᵀ S‖`; their forms with the suffix
  `_of_closedBall` hold on a region that contains the closed ball of radius `‖S‖` around
  `U S Vᵀ`, because a deflated point is `‖S b‖` or `‖aᵀ S‖` away from it
  (`LeanDLRA.norm_deflate_right_sub`, `LeanDLRA.norm_deflate_left_sub`).

The proof of the column bound deflates the direction `a`: the point `U (1 - a aᵀ) S Vᵀ` is a
factored point for the basis `U (1 - a aᵀ) + u' aᵀ`, in which the column `U a` is replaced by a
unit column `u'` orthogonal to the range of `U`. The normal bound at that point bounds the
component along `U a`, and the two points are `‖aᵀ S‖` apart. The transposed form follows by
transposing the field (`LeanDLRA.FactoredNormalBoundOn.transpose`,
`LeanDLRA.IsLipschitzFieldOn.transpose`).
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

variable {m n : Type*} [Fintype m] [Fintype n]

/-! ### Auxiliary identities -/

/-- The complementary projector `1 - B Bᵀ` is symmetric. -/
private theorem one_sub_mul_transpose_self_transpose {k l : Type*} [Fintype l] [DecidableEq k]
    (B : Matrix k l ℝ) : (1 - B * Bᵀ)ᵀ = 1 - B * Bᵀ := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- A row block `xᵀ` that annihilates `B` passes through the projector `1 - B Bᵀ`. -/
private theorem transpose_mul_normal_of_mul_eq_zero {k l : Type*} [Fintype l]
    [DecidableEq m] {x : Matrix m k ℝ} {B : Matrix m l ℝ} (h : xᵀ * B = 0) (X : Matrix m n ℝ)
    (Q : Matrix n n ℝ) : xᵀ * ((1 - B * Bᵀ) * X * Q) = xᵀ * X * Q := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one,
    ← Matrix.mul_assoc xᵀ B, h, Matrix.zero_mul, sub_zero]

/-- Transposition swaps the two complementary projectors of a doubly normal component. -/
private theorem transpose_normal_mul_mul_normal {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq m] [DecidableEq n] (U : Matrix m k ℝ) (V : Matrix n l ℝ) (X : Matrix m n ℝ) :
    ((1 - U * Uᵀ) * X * (1 - V * Vᵀ))ᵀ = (1 - V * Vᵀ) * Xᵀ * (1 - U * Uᵀ) := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, one_sub_mul_transpose_self_transpose,
    one_sub_mul_transpose_self_transpose, Matrix.mul_assoc]

/-- Multiplication by `1 - V Vᵀ` from the right does not increase the Frobenius norm. -/
private theorem norm_mul_one_sub_le {k l : Type*} [Fintype k] [Fintype l] [DecidableEq l]
    [DecidableEq n] {V : Matrix n l ℝ} (hV : Vᵀ * V = 1) (X : Matrix k n ℝ) :
    ‖X * (1 - V * Vᵀ)‖ ≤ ‖X‖ := by
  rw [← one_sub_rightProj_apply]
  exact (isOrthProj_rightProj hV).compl.norm_le X

/-! ### Deflation of one direction -/

section Deflation

variable {r : ℕ} {a : Matrix (Fin r) (Fin 1) ℝ}

private theorem deflate_mul_col (ha : aᵀ * a = 1) : (1 - a * aᵀ) * a = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, ha, Matrix.mul_one, sub_self]

private theorem col_transpose_mul_deflate (ha : aᵀ * a = 1) : aᵀ * (1 - a * aᵀ) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ha, Matrix.one_mul, sub_self]

private theorem deflate_mul_deflate (ha : aᵀ * a = 1) :
    (1 - a * aᵀ) * (1 - a * aᵀ) = 1 - a * aᵀ := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, deflate_mul_col ha, Matrix.zero_mul,
    sub_zero]

variable {U : Matrix m (Fin r) ℝ} {u' : Matrix m (Fin 1) ℝ}

/-- The basis `U (1 - a aᵀ) + u' aᵀ`, in which the column `U a` is replaced by `u'`, has
orthonormal columns. -/
private theorem swapped_basis_orthonormal (hU : Uᵀ * U = 1) (ha : aᵀ * a = 1)
    (hu' : u'ᵀ * u' = 1) (hUu' : Uᵀ * u' = 0) :
    (U * (1 - a * aᵀ) + u' * aᵀ)ᵀ * (U * (1 - a * aᵀ) + u' * aᵀ) = 1 := by
  have hu'U : u'ᵀ * U = 0 := by
    rw [← Matrix.transpose_transpose U, ← Matrix.transpose_mul, hUu', Matrix.transpose_zero]
  have h₁ : ((1 : Matrix (Fin r) (Fin r) ℝ) - a * aᵀ) * Uᵀ * (U * (1 - a * aᵀ)) =
      1 - a * aᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul, deflate_mul_deflate ha]
  have h₂ : ((1 : Matrix (Fin r) (Fin r) ℝ) - a * aᵀ) * Uᵀ * (u' * aᵀ) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hUu', Matrix.zero_mul, Matrix.mul_zero]
  have h₃ : a * u'ᵀ * (U * (1 - a * aᵀ)) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc u'ᵀ, hu'U, Matrix.zero_mul, Matrix.mul_zero]
  have h₄ : a * u'ᵀ * (u' * aᵀ) = a * aᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc u'ᵀ, hu', Matrix.one_mul]
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, one_sub_mul_transpose_self_transpose, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_add, h₁, h₂, h₃, h₄, add_zero, zero_add, sub_add_cancel]

omit [Fintype m] in
/-- The swapped basis and `U` agree on the deflated core `(1 - a aᵀ) S`. -/
private theorem swapped_basis_mul_deflate (ha : aᵀ * a = 1) (S : Matrix (Fin r) (Fin r) ℝ) :
    (U * (1 - a * aᵀ) + u' * aᵀ) * ((1 - a * aᵀ) * S) = U * ((1 - a * aᵀ) * S) := by
  rw [Matrix.add_mul, Matrix.mul_assoc u', ← Matrix.mul_assoc aᵀ, col_transpose_mul_deflate ha,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, Matrix.mul_assoc U,
    ← Matrix.mul_assoc (1 - a * aᵀ) (1 - a * aᵀ) S, deflate_mul_deflate ha]

/-- The column `U a` is orthogonal to the swapped basis. -/
private theorem col_transpose_mul_swapped_basis (hU : Uᵀ * U = 1) (ha : aᵀ * a = 1)
    (hUu' : Uᵀ * u' = 0) : (U * a)ᵀ * (U * (1 - a * aᵀ) + u' * aᵀ) = 0 := by
  rw [Matrix.transpose_mul, Matrix.mul_add, Matrix.mul_assoc aᵀ, ← Matrix.mul_assoc Uᵀ U, hU,
    Matrix.one_mul, col_transpose_mul_deflate ha, Matrix.mul_assoc aᵀ, ← Matrix.mul_assoc Uᵀ u',
    hUu', Matrix.zero_mul, Matrix.mul_zero, add_zero]

/-- **Deflation of one direction.** If a unit column `u'` is orthogonal to the range of `U`,
there is a basis with orthonormal columns that agrees with `U` on the deflated core
`(1 - a aᵀ) S` and is orthogonal to the column `U a`. -/
private theorem exists_swapped_basis (hU : Uᵀ * U = 1) (ha : aᵀ * a = 1)
    (hu' : u'ᵀ * u' = 1) (hUu' : Uᵀ * u' = 0) (S : Matrix (Fin r) (Fin r) ℝ) :
    ∃ U₁ : Matrix m (Fin r) ℝ, U₁ᵀ * U₁ = 1 ∧
      U₁ * ((1 - a * aᵀ) * S) = U * ((1 - a * aᵀ) * S) ∧ (U * a)ᵀ * U₁ = 0 :=
  ⟨_, swapped_basis_orthonormal hU ha hu' hUu', swapped_basis_mul_deflate ha S,
    col_transpose_mul_swapped_basis hU ha hUu'⟩

end Deflation

/-! ### Transposition of the field -/

section Transpose

variable [DecidableEq m] [DecidableEq n] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {r : ℕ}
  {D : Set (ℝ × Matrix m n ℝ)} {ε L : ℝ}

/-- The factored normal bound is invariant under transposition of the field and of the region:
the roles of the two bases are exchanged. -/
theorem FactoredNormalBoundOn.transpose (h : FactoredNormalBoundOn F r D ε) :
    FactoredNormalBoundOn (fun t (X : Matrix n m ℝ) => (F t Xᵀ)ᵀ) r
      {p : ℝ × Matrix n m ℝ | (p.1, p.2ᵀ) ∈ D} ε := by
  intro t V U S hV hU hmem
  have hpt : (V * S * Uᵀ)ᵀ = U * Sᵀ * Vᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      ← Matrix.mul_assoc]
  have hmem' : (t, U * Sᵀ * Vᵀ) ∈ D := by
    rw [← hpt]
    exact hmem
  change ‖(1 - V * Vᵀ) * (F t (V * S * Uᵀ)ᵀ)ᵀ * (1 - U * Uᵀ)‖ ≤ ε
  rw [hpt, ← transpose_normal_mul_mul_normal, Frobenius.norm_transpose]
  exact h t U V Sᵀ hU hV hmem'

omit [DecidableEq m] [DecidableEq n] in
/-- A Lipschitz bound in the state is invariant under transposition of the field and of the
region. -/
theorem IsLipschitzFieldOn.transpose (h : IsLipschitzFieldOn F D L) :
    IsLipschitzFieldOn (fun t (X : Matrix n m ℝ) => (F t Xᵀ)ᵀ)
      {p : ℝ × Matrix n m ℝ | (p.1, p.2ᵀ) ∈ D} L := by
  intro t X Y hX hY
  have hX' : (t, Xᵀ) ∈ D := hX
  have hY' : (t, Yᵀ) ∈ D := hY
  change ‖(F t Xᵀ)ᵀ - (F t Yᵀ)ᵀ‖ ≤ L * ‖X - Y‖
  rw [← Matrix.transpose_sub, Frobenius.norm_transpose, ← Frobenius.norm_transpose (X - Y),
    Matrix.transpose_sub]
  exact h hX' hY'

end Transpose

/-! ### The mixed components at a factored point -/

section Mixed

variable [DecidableEq m] [DecidableEq n] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {r : ℕ}
  {D : Set (ℝ × Matrix m n ℝ)} {ε L : ℝ} {t : ℝ} {U : Matrix m (Fin r) ℝ}
  {V : Matrix n (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ}

omit [DecidableEq m] [DecidableEq n] in
/-- Deflating a unit direction `a` on the left moves the factored point `U S Vᵀ` by exactly
`‖aᵀ S‖`. -/
theorem norm_deflate_left_sub (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {a : Matrix (Fin r) (Fin 1) ℝ} (ha : aᵀ * a = 1) :
    ‖U * ((1 - a * aᵀ) * S) * Vᵀ - U * S * Vᵀ‖ = ‖aᵀ * S‖ := by
  have h : U * S * Vᵀ - U * ((1 - a * aᵀ) * S) * Vᵀ = U * (a * (aᵀ * S)) * Vᵀ := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.sub_mul 1, Matrix.one_mul, sub_sub_cancel,
      Matrix.mul_assoc a]
  rw [norm_sub_rev, h, Frobenius.norm_mul_transpose_of_orthonormal hV,
    Frobenius.norm_mul_of_orthonormal hU, Frobenius.norm_mul_of_orthonormal ha]

/-- **Mixed component along a column direction.** Let `F` satisfy the factored normal bound
with defect `ε` and a Lipschitz bound with constant `L` on a region `D`. At a factored point
`U S Vᵀ` and for a unit column `a`, the component of the field with column factor `U a` and row
factor outside the range of `V` satisfies
`‖(U a)ᵀ F(t, U S Vᵀ) (1 - V Vᵀ)‖ ≤ ε + L ‖aᵀ S‖`.
The bound needs a unit column `u'` orthogonal to the range of `U` (such a column exists exactly
when `r` is smaller than the number of rows) and the deflated point `U (1 - a aᵀ) S Vᵀ` in the
region. No sign condition on `L` is used. -/
theorem norm_col_transpose_mul_field_mul_normal_le
    (hN : FactoredNormalBoundOn F r D ε) (hL : IsLipschitzFieldOn F D L)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {a : Matrix (Fin r) (Fin 1) ℝ} (ha : aᵀ * a = 1)
    {u' : Matrix m (Fin 1) ℝ} (hu' : u'ᵀ * u' = 1) (hUu' : Uᵀ * u' = 0)
    (hW : (t, U * S * Vᵀ) ∈ D) (hW₀ : (t, U * ((1 - a * aᵀ) * S) * Vᵀ) ∈ D) :
    ‖(U * a)ᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε + L * ‖aᵀ * S‖ := by
  have hx : (U * a)ᵀ * (U * a) = 1 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul, ha]
  obtain ⟨U₁, hU₁, hfac, hxU₁⟩ := exists_swapped_basis hU ha hu' hUu' S
  -- the deflated point is a factored point for the swapped basis
  have h₁ : ‖(U * a)ᵀ * F t (U * ((1 - a * aᵀ) * S) * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε := by
    have hN' := hN t U₁ V ((1 - a * aᵀ) * S) hU₁ hV (by rw [hfac]; exact hW₀)
    rw [hfac] at hN'
    rw [← transpose_mul_normal_of_mul_eq_zero hxU₁ (F t (U * ((1 - a * aᵀ) * S) * Vᵀ))
      (1 - V * Vᵀ)]
    exact (norm_transpose_mul_le hx _).trans hN'
  -- the two points are `‖aᵀ S‖` apart
  have hnorm : ‖U * S * Vᵀ - U * ((1 - a * aᵀ) * S) * Vᵀ‖ = ‖aᵀ * S‖ := by
    rw [norm_sub_rev]
    exact norm_deflate_left_sub hU hV ha
  have h₂ : ‖(U * a)ᵀ * (F t (U * S * Vᵀ) - F t (U * ((1 - a * aᵀ) * S) * Vᵀ)) *
      (1 - V * Vᵀ)‖ ≤ L * ‖aᵀ * S‖ :=
    calc ‖(U * a)ᵀ * (F t (U * S * Vᵀ) - F t (U * ((1 - a * aᵀ) * S) * Vᵀ)) * (1 - V * Vᵀ)‖
        ≤ ‖(U * a)ᵀ * (F t (U * S * Vᵀ) - F t (U * ((1 - a * aᵀ) * S) * Vᵀ))‖ :=
          norm_mul_one_sub_le hV _
      _ ≤ ‖F t (U * S * Vᵀ) - F t (U * ((1 - a * aᵀ) * S) * Vᵀ)‖ := norm_transpose_mul_le hx _
      _ ≤ L * ‖U * S * Vᵀ - U * ((1 - a * aᵀ) * S) * Vᵀ‖ := hL hW hW₀
      _ = L * ‖aᵀ * S‖ := by rw [hnorm]
  calc ‖(U * a)ᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖
      = ‖(U * a)ᵀ * F t (U * ((1 - a * aᵀ) * S) * Vᵀ) * (1 - V * Vᵀ) +
          (U * a)ᵀ * (F t (U * S * Vᵀ) - F t (U * ((1 - a * aᵀ) * S) * Vᵀ)) *
            (1 - V * Vᵀ)‖ := by
        rw [← Matrix.add_mul, ← Matrix.mul_add, add_sub_cancel]
    _ ≤ ε + L * ‖aᵀ * S‖ := (norm_add_le _ _).trans (add_le_add h₁ h₂)

/-- **Mixed component along a row direction**, the transposed form of
`norm_col_transpose_mul_field_mul_normal_le`: for a unit column `b`,
`‖(1 - U Uᵀ) F(t, U S Vᵀ) (V b)‖ ≤ ε + L ‖S b‖`,
given a unit column `v'` orthogonal to the range of `V` and the deflated point
`U S (1 - b bᵀ) Vᵀ` in the region. It is obtained from the column form by transposing the field
(`FactoredNormalBoundOn.transpose`, `IsLipschitzFieldOn.transpose`). -/
theorem norm_normal_mul_field_mul_col_le
    (hN : FactoredNormalBoundOn F r D ε) (hL : IsLipschitzFieldOn F D L)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {b : Matrix (Fin r) (Fin 1) ℝ} (hb : bᵀ * b = 1)
    {v' : Matrix n (Fin 1) ℝ} (hv' : v'ᵀ * v' = 1) (hVv' : Vᵀ * v' = 0)
    (hW : (t, U * S * Vᵀ) ∈ D) (hW₀ : (t, U * (S * (1 - b * bᵀ)) * Vᵀ) ∈ D) :
    ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (V * b)‖ ≤ ε + L * ‖S * b‖ := by
  have hpt : ∀ T : Matrix (Fin r) (Fin r) ℝ, (V * Tᵀ * Uᵀ)ᵀ = U * T * Vᵀ := fun T => by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose, ← Matrix.mul_assoc]
  have hW' : (t, V * Sᵀ * Uᵀ) ∈ {p : ℝ × Matrix n m ℝ | (p.1, p.2ᵀ) ∈ D} := by
    change (t, (V * Sᵀ * Uᵀ)ᵀ) ∈ D
    rw [hpt]
    exact hW
  have hT : (1 - b * bᵀ) * Sᵀ = (S * (1 - b * bᵀ))ᵀ := by
    rw [Matrix.transpose_mul, one_sub_mul_transpose_self_transpose]
  have hW₀' : (t, V * ((1 - b * bᵀ) * Sᵀ) * Uᵀ) ∈
      {p : ℝ × Matrix n m ℝ | (p.1, p.2ᵀ) ∈ D} := by
    change (t, (V * ((1 - b * bᵀ) * Sᵀ) * Uᵀ)ᵀ) ∈ D
    rw [hT, hpt]
    exact hW₀
  have key : ‖(V * b)ᵀ * (F t (V * Sᵀ * Uᵀ)ᵀ)ᵀ * (1 - U * Uᵀ)‖ ≤ ε + L * ‖bᵀ * Sᵀ‖ :=
    norm_col_transpose_mul_field_mul_normal_le hN.transpose hL.transpose hV hU hb hv' hVv'
      hW' hW₀'
  have hlhs : (V * b)ᵀ * (F t (U * S * Vᵀ))ᵀ * (1 - U * Uᵀ) =
      ((1 - U * Uᵀ) * F t (U * S * Vᵀ) * (V * b))ᵀ := by
    rw [Matrix.transpose_mul ((1 - U * Uᵀ) * F t (U * S * Vᵀ)) (V * b),
      Matrix.transpose_mul (1 - U * Uᵀ) (F t (U * S * Vᵀ)),
      one_sub_mul_transpose_self_transpose, Matrix.mul_assoc (V * b)ᵀ]
  have hrhs : bᵀ * Sᵀ = (S * b)ᵀ := (Matrix.transpose_mul S b).symm
  rw [hpt, hlhs, Frobenius.norm_transpose, hrhs, Frobenius.norm_transpose] at key
  exact key

omit [DecidableEq m] [DecidableEq n] in
/-- Deflating a unit direction `b` moves the factored point `U S Vᵀ` by exactly `‖S b‖`. -/
theorem norm_deflate_right_sub (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {b : Matrix (Fin r) (Fin 1) ℝ} (hb : bᵀ * b = 1) :
    ‖U * (S * (1 - b * bᵀ)) * Vᵀ - U * S * Vᵀ‖ = ‖S * b‖ := by
  have h : U * (S * (1 - b * bᵀ)) * Vᵀ - U * S * Vᵀ = -(U * (S * (b * bᵀ)) * Vᵀ) := by
    rw [Matrix.mul_sub S, Matrix.mul_one, Matrix.mul_sub U, Matrix.sub_mul,
      sub_sub_cancel_left]
  rw [h, norm_neg, Frobenius.norm_mul_transpose_of_orthonormal hV,
    Frobenius.norm_mul_of_orthonormal hU, ← Matrix.mul_assoc,
    Frobenius.norm_mul_transpose_of_orthonormal hb]

/-- For a column `c`, the `1 × 1` matrix `cᵀ c` is `‖c‖²`. -/
private theorem col_transpose_mul_self (c : Matrix (Fin r) (Fin 1) ℝ) :
    cᵀ * c = (‖c‖ ^ 2) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  rw [Frobenius.norm_sq_eq_sum]
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim i 0
  obtain rfl : j = 0 := Subsingleton.elim j 0
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, Fin.sum_univ_one, pow_two]

/-- A nonzero column is its norm times a unit column. -/
private theorem exists_unit_col_smul_eq {c : Matrix (Fin r) (Fin 1) ℝ} (hc : c ≠ 0) :
    ∃ b : Matrix (Fin r) (Fin 1) ℝ, bᵀ * b = 1 ∧ ‖c‖ • b = c := by
  have hc' : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  refine ⟨‖c‖⁻¹ • c, ?_, ?_⟩
  · have h : ‖c‖⁻¹ * ‖c‖⁻¹ * ‖c‖ ^ 2 = 1 := by
      rw [pow_two, mul_mul_mul_comm, inv_mul_cancel₀ hc', mul_one]
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      col_transpose_mul_self, smul_smul, h, one_smul]
  · rw [smul_smul, mul_inv_cancel₀ hc', one_smul]

/-- **Mixed component, homogeneous form.** For every column `c`, of any norm,
`‖(1 - U Uᵀ) F(t, U S Vᵀ) (V c)‖ ≤ ε ‖c‖ + L ‖S c‖`,
provided the deflated point `U S (1 - b bᵀ) Vᵀ` lies in the region for every unit column `b`.
For the full region this hypothesis is trivial; for a region that contains the closed ball of
radius `‖S‖` around `U S Vᵀ` see `norm_normal_mul_field_mul_le_of_closedBall`. Applied to the
columns of the identity it bounds `(1 - U Uᵀ) F(t, U S Vᵀ) V` column by column in terms of the
columns of `S`, with no inverse of `S`. -/
theorem norm_normal_mul_field_mul_le
    (hN : FactoredNormalBoundOn F r D ε) (hL : IsLipschitzFieldOn F D L)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {v' : Matrix n (Fin 1) ℝ} (hv' : v'ᵀ * v' = 1) (hVv' : Vᵀ * v' = 0)
    (hW : (t, U * S * Vᵀ) ∈ D)
    (hW₀ : ∀ b : Matrix (Fin r) (Fin 1) ℝ, bᵀ * b = 1 →
      (t, U * (S * (1 - b * bᵀ)) * Vᵀ) ∈ D)
    (c : Matrix (Fin r) (Fin 1) ℝ) :
    ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (V * c)‖ ≤ ε * ‖c‖ + L * ‖S * c‖ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · obtain ⟨b, hb, hcb⟩ := exists_unit_col_smul_eq hc
    have key := norm_normal_mul_field_mul_col_le hN hL hU hV hb hv' hVv' hW (hW₀ b hb)
    have h₁ : (1 - U * Uᵀ) * F t (U * S * Vᵀ) * (V * c) =
        ‖c‖ • ((1 - U * Uᵀ) * F t (U * S * Vᵀ) * (V * b)) := by
      rw [← Matrix.mul_smul, ← Matrix.mul_smul, hcb]
    have h₂ : S * c = ‖c‖ • (S * b) := by
      rw [← Matrix.mul_smul, hcb]
    rw [h₁, h₂, norm_smul, norm_smul, norm_norm]
    calc ‖c‖ * ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (V * b)‖
        ≤ ‖c‖ * (ε + L * ‖S * b‖) := mul_le_mul_of_nonneg_left key (norm_nonneg c)
      _ = ε * ‖c‖ + L * (‖c‖ * ‖S * b‖) := by ring

/-- The homogeneous form on a region that contains the closed ball of radius `‖S‖` around the
factored point `U S Vᵀ`: every deflated point lies in that ball
(`norm_deflate_right_sub`). -/
theorem norm_normal_mul_field_mul_le_of_closedBall
    (hN : FactoredNormalBoundOn F r D ε) (hL : IsLipschitzFieldOn F D L)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {v' : Matrix n (Fin 1) ℝ} (hv' : v'ᵀ * v' = 1) (hVv' : Vᵀ * v' = 0)
    (hD : ∀ X : Matrix m n ℝ, ‖X - U * S * Vᵀ‖ ≤ ‖S‖ → (t, X) ∈ D)
    (c : Matrix (Fin r) (Fin 1) ℝ) :
    ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (V * c)‖ ≤ ε * ‖c‖ + L * ‖S * c‖ := by
  refine norm_normal_mul_field_mul_le hN hL hU hV hv' hVv' (hD _ ?_) (fun b hb => hD _ ?_) c
  · rw [sub_self, norm_zero]
    exact norm_nonneg S
  · rw [norm_deflate_right_sub hU hV hb]
    exact norm_mul_le_of_orthonormal hb S

/-- **Mixed component, homogeneous form on the left.** For every column `c`, of any norm,
`‖(U c)ᵀ F(t, U S Vᵀ) (1 - V Vᵀ)‖ ≤ ε ‖c‖ + L ‖cᵀ S‖`,
provided the deflated point `U (1 - a aᵀ) S Vᵀ` lies in the region for every unit column `a`.
Applied to the columns of the identity it bounds `Uᵀ F(t, U S Vᵀ) (1 - V Vᵀ)` row by row in
terms of the rows of `S`. -/
theorem norm_transpose_mul_field_mul_normal_le
    (hN : FactoredNormalBoundOn F r D ε) (hL : IsLipschitzFieldOn F D L)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {u' : Matrix m (Fin 1) ℝ} (hu' : u'ᵀ * u' = 1) (hUu' : Uᵀ * u' = 0)
    (hW : (t, U * S * Vᵀ) ∈ D)
    (hW₀ : ∀ a : Matrix (Fin r) (Fin 1) ℝ, aᵀ * a = 1 →
      (t, U * ((1 - a * aᵀ) * S) * Vᵀ) ∈ D)
    (c : Matrix (Fin r) (Fin 1) ℝ) :
    ‖(U * c)ᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε * ‖c‖ + L * ‖cᵀ * S‖ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · obtain ⟨a, ha, hca⟩ := exists_unit_col_smul_eq hc
    have key := norm_col_transpose_mul_field_mul_normal_le hN hL hU hV ha hu' hUu' hW
      (hW₀ a ha)
    have h₁ : (U * c)ᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ) =
        ‖c‖ • ((U * a)ᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ)) := by
      rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, ← Matrix.mul_smul, hca]
    have h₂ : cᵀ * S = ‖c‖ • (aᵀ * S) := by
      rw [← Matrix.smul_mul, ← Matrix.transpose_smul, hca]
    rw [h₁, h₂, norm_smul, norm_smul, norm_norm]
    calc ‖c‖ * ‖(U * a)ᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖
        ≤ ‖c‖ * (ε + L * ‖aᵀ * S‖) := mul_le_mul_of_nonneg_left key (norm_nonneg c)
      _ = ε * ‖c‖ + L * (‖c‖ * ‖aᵀ * S‖) := by ring

/-- The homogeneous form on the left on a region that contains the closed ball of radius `‖S‖`
around the factored point `U S Vᵀ` (`norm_deflate_left_sub`). -/
theorem norm_transpose_mul_field_mul_normal_le_of_closedBall
    (hN : FactoredNormalBoundOn F r D ε) (hL : IsLipschitzFieldOn F D L)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {u' : Matrix m (Fin 1) ℝ} (hu' : u'ᵀ * u' = 1) (hUu' : Uᵀ * u' = 0)
    (hD : ∀ X : Matrix m n ℝ, ‖X - U * S * Vᵀ‖ ≤ ‖S‖ → (t, X) ∈ D)
    (c : Matrix (Fin r) (Fin 1) ℝ) :
    ‖(U * c)ᵀ * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε * ‖c‖ + L * ‖cᵀ * S‖ := by
  refine norm_transpose_mul_field_mul_normal_le hN hL hU hV hu' hUu' (hD _ ?_)
    (fun a ha => hD _ ?_) c
  · rw [sub_self, norm_zero]
    exact norm_nonneg S
  · rw [norm_deflate_left_sub hU hV ha]
    exact norm_transpose_mul_le ha S

end Mixed

/-! ### Non-vacuity -/

namespace FactoredNormalBoundExamples

/-- The identity matrix of size one. -/
local notation "I₁" => (1 : Matrix (Fin 1) (Fin 1) ℝ)

/-- The matrix `E₂₁`; its transpose `E₁₂` multiplies from the right in `shiftField`. -/
private def shiftMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- The linear field `Y ↦ Y E₁₂` on `2 × 2` matrices, in the form `M Y + Y Nᵀ + G` of
`factoredNormalBoundOn_linear` with `M = 0`, `N = E₂₁`, `G = 0`. -/
private def shiftField : ℝ → Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
  fun _ Y => 0 * Y + Y * shiftMatrixᵀ + 0

/-- The unit column `(1, 0)` of `ℝ²`. -/
private def e₁ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The unit column `(0, 1)` of `ℝ²`. -/
private def e₂ : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]

/-- The constant field `(0 1)` on `1 × 2` matrices. -/
private def constRowField : ℝ → Matrix (Fin 1) (Fin 2) ℝ → Matrix (Fin 1) (Fin 2) ℝ :=
  fun _ _ => !![0, 1]

/-- A matrix whose squared entries sum to one has Frobenius norm one. -/
private theorem norm_eq_one {k l : Type*} [Fintype k] [Fintype l] {A : Matrix k l ℝ}
    (h : ∑ i, ∑ j, A i j ^ 2 = 1) : ‖A‖ = 1 := by
  rw [← Frobenius.norm_sq_eq_sum] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg A) two_ne_zero).1 h

private theorem norm_shiftMatrix : ‖shiftMatrix‖ = 1 :=
  norm_eq_one (by simp [shiftMatrix, Fin.sum_univ_two])

private theorem norm_one_one : ‖I₁‖ = 1 :=
  norm_eq_one (by simp)

private theorem e₁_orth : e₁ᵀ * e₁ = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [e₁, Matrix.mul_apply, Fin.sum_univ_two]

private theorem e₂_orth : e₂ᵀ * e₂ = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [e₂, Matrix.mul_apply, Fin.sum_univ_two]

private theorem e₁_e₂ : e₁ᵀ * e₂ = 0 := by
  ext i j
  fin_cases i; fin_cases j
  simp [e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]

private theorem one_orth : I₁ᵀ * I₁ = 1 := by
  rw [Matrix.transpose_one, Matrix.mul_one]

private theorem factoredNormalBoundOn_shiftField :
    FactoredNormalBoundOn shiftField 1 univ 0 := by
  have h := factoredNormalBoundOn_linear (r := 1) (0 : Matrix (Fin 2) (Fin 2) ℝ) shiftMatrix 0
    univ
  rw [norm_zero] at h
  exact h

private theorem isLipschitzFieldOn_shiftField : IsLipschitzFieldOn shiftField univ 1 := by
  intro t X Y _ _
  have h := norm_linear_sub_le (0 : Matrix (Fin 2) (Fin 2) ℝ) shiftMatrix 0 X Y
  rw [norm_zero, zero_add, norm_shiftMatrix] at h
  exact h

/-- The mixed component of `shiftField` at the point `e₁ e₁ᵀ` in the direction `a = 1`. -/
private theorem shiftField_mixed :
    (e₁ * I₁)ᵀ * shiftField 0 (e₁ * I₁ * e₁ᵀ) * (1 - e₁ * e₁ᵀ) =
      !![0, 1] := by
  ext i j
  simp only [shiftField, Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.zero_apply, Matrix.one_apply, Fin.sum_univ_two, Fin.sum_univ_one]
  fin_cases i
  fin_cases j <;> simp [shiftMatrix, e₁]

/-- Non-vacuity of `norm_col_transpose_mul_field_mul_normal_le` with nonzero data: the field
`Y ↦ Y E₁₂` (defect `0`, Lipschitz constant `1`), rank one, the point `e₁ e₁ᵀ`, `a = 1` and
`u' = e₂`. -/
example :
    ‖(e₁ * I₁)ᵀ * shiftField 0 (e₁ * I₁ * e₁ᵀ) * (1 - e₁ * e₁ᵀ)‖ ≤
      0 + 1 * ‖I₁ᵀ * I₁‖ :=
  norm_col_transpose_mul_field_mul_normal_le factoredNormalBoundOn_shiftField
    isLipschitzFieldOn_shiftField e₁_orth e₁_orth one_orth e₂_orth e₁_e₂ (mem_univ _)
    (mem_univ _)

/-- In the preceding example the bound holds with equality, and the term `L ‖aᵀ S‖` equals one:
the bound does not hold with the Lipschitz constant replaced by zero. -/
example :
    ‖(e₁ * I₁)ᵀ * shiftField 0 (e₁ * I₁ * e₁ᵀ) * (1 - e₁ * e₁ᵀ)‖ =
        0 + 1 * ‖I₁ᵀ * I₁‖ ∧
      (1 : ℝ) * ‖I₁ᵀ * I₁‖ = 1 := by
  have h : ‖(!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ)‖ = 1 :=
    norm_eq_one (by simp [Fin.sum_univ_two])
  rw [shiftField_mixed, h, one_orth, norm_one_one]
  norm_num

/-- Non-vacuity of `norm_normal_mul_field_mul_col_le` with the same field and point, `b = 1`
and `v' = e₂`. -/
example :
    ‖(1 - e₁ * e₁ᵀ) * shiftField 0 (e₁ * I₁ * e₁ᵀ) * (e₁ * I₁)‖ ≤ 0 + 1 * ‖I₁ * I₁‖ :=
  norm_normal_mul_field_mul_col_le factoredNormalBoundOn_shiftField
    isLipschitzFieldOn_shiftField e₁_orth e₁_orth one_orth e₂_orth e₁_e₂ (mem_univ _)
    (mem_univ _)

/-- Non-vacuity of `norm_normal_mul_field_mul_le`: on the full region the hypothesis on the
deflated points is trivial. -/
example (c : Matrix (Fin 1) (Fin 1) ℝ) :
    ‖(1 - e₁ * e₁ᵀ) * shiftField 0 (e₁ * I₁ * e₁ᵀ) * (e₁ * c)‖ ≤ 0 * ‖c‖ + 1 * ‖I₁ * c‖ :=
  norm_normal_mul_field_mul_le factoredNormalBoundOn_shiftField isLipschitzFieldOn_shiftField
    e₁_orth e₁_orth e₂_orth e₁_e₂ (mem_univ _) (fun _ _ => mem_univ _) c

/-- Non-vacuity of `norm_normal_mul_field_mul_le_of_closedBall`. -/
example (c : Matrix (Fin 1) (Fin 1) ℝ) :
    ‖(1 - e₁ * e₁ᵀ) * shiftField 0 (e₁ * I₁ * e₁ᵀ) * (e₁ * c)‖ ≤ 0 * ‖c‖ + 1 * ‖I₁ * c‖ :=
  norm_normal_mul_field_mul_le_of_closedBall factoredNormalBoundOn_shiftField
    isLipschitzFieldOn_shiftField e₁_orth e₁_orth e₂_orth e₁_e₂ (fun _ _ => mem_univ _) c

/-- Non-vacuity of `FactoredNormalBoundOn.transpose` and `IsLipschitzFieldOn.transpose`. -/
example :
    FactoredNormalBoundOn (fun t (X : Matrix (Fin 2) (Fin 2) ℝ) => (shiftField t Xᵀ)ᵀ) 1
        {p : ℝ × Matrix (Fin 2) (Fin 2) ℝ | (p.1, p.2ᵀ) ∈ (univ : Set (ℝ × _))} 0 ∧
      IsLipschitzFieldOn (fun t (X : Matrix (Fin 2) (Fin 2) ℝ) => (shiftField t Xᵀ)ᵀ)
        {p : ℝ × Matrix (Fin 2) (Fin 2) ℝ | (p.1, p.2ᵀ) ∈ (univ : Set (ℝ × _))} 1 :=
  ⟨factoredNormalBoundOn_shiftField.transpose, isLipschitzFieldOn_shiftField.transpose⟩

/-- Non-vacuity of `norm_deflate_right_sub`: deflating the only direction of `e₁ e₁ᵀ`. -/
example : ‖e₁ * (I₁ * (1 - I₁ * I₁ᵀ)) * e₁ᵀ - e₁ * I₁ * e₁ᵀ‖ = ‖I₁ * I₁‖ :=
  norm_deflate_right_sub e₁_orth e₁_orth one_orth

/-- Non-vacuity of `norm_transpose_mul_field_mul_normal_le` and of its closed-ball form. -/
example (c : Matrix (Fin 1) (Fin 1) ℝ) :
    ‖(e₁ * c)ᵀ * shiftField 0 (e₁ * I₁ * e₁ᵀ) * (1 - e₁ * e₁ᵀ)‖ ≤ 0 * ‖c‖ + 1 * ‖cᵀ * I₁‖ :=
  norm_transpose_mul_field_mul_normal_le factoredNormalBoundOn_shiftField
    isLipschitzFieldOn_shiftField e₁_orth e₁_orth e₂_orth e₁_e₂ (mem_univ _)
    (fun _ _ => mem_univ _) c

example (c : Matrix (Fin 1) (Fin 1) ℝ) :
    ‖(e₁ * c)ᵀ * shiftField 0 (e₁ * I₁ * e₁ᵀ) * (1 - e₁ * e₁ᵀ)‖ ≤ 0 * ‖c‖ + 1 * ‖cᵀ * I₁‖ :=
  norm_transpose_mul_field_mul_normal_le_of_closedBall factoredNormalBoundOn_shiftField
    isLipschitzFieldOn_shiftField e₁_orth e₁_orth e₂_orth e₁_e₂ (fun _ _ => mem_univ _) c

/-- Non-vacuity of `norm_deflate_left_sub`. -/
example : ‖e₁ * ((1 - I₁ * I₁ᵀ) * I₁) * e₁ᵀ - e₁ * I₁ * e₁ᵀ‖ = ‖I₁ᵀ * I₁‖ :=
  norm_deflate_left_sub e₁_orth e₁_orth one_orth

/-- The unit column `u'` orthogonal to the range of `U` cannot be dropped from
`norm_col_transpose_mul_field_mul_normal_le`. For `1 × 2` matrices and rank one the basis `U`
is square, so no such column exists. The constant field `(0 1)` satisfies the factored normal
bound with defect `0` and is Lipschitz with constant `0`, the remaining hypotheses hold for
`U = S = a = 1` and `V = e₁`, and the left side of the bound is `1`. -/
example :
    FactoredNormalBoundOn constRowField 1 univ 0 ∧ IsLipschitzFieldOn constRowField univ 0 ∧
      I₁ᵀ * I₁ = 1 ∧ e₁ᵀ * e₁ = 1 ∧
      ¬ ‖(I₁ * I₁)ᵀ * constRowField 0 (I₁ * I₁ * e₁ᵀ) * (1 - e₁ * e₁ᵀ)‖ ≤
        0 + 0 * ‖I₁ᵀ * I₁‖ := by
  refine ⟨?_, ?_, one_orth, e₁_orth, ?_⟩
  · intro t U V S hU _ _
    have hU' : U * Uᵀ = 1 := by
      rw [← hU]
      ext i j
      obtain rfl : i = 0 := Subsingleton.elim i 0
      obtain rfl : j = 0 := Subsingleton.elim j 0
      rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_one, Fin.sum_univ_one,
        Matrix.transpose_apply]
    have h0 : I₁ - U * Uᵀ = 0 := by rw [hU', sub_self]
    rw [h0, Matrix.zero_mul, Matrix.zero_mul]
    exact norm_zero.le
  · intro t X Y _ _
    simp [constRowField]
  · have hmat : (I₁ * I₁)ᵀ * constRowField 0 (I₁ * I₁ * e₁ᵀ) * (1 - e₁ * e₁ᵀ) = !![0, 1] := by
      ext i j
      simp only [constRowField, Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply,
        Matrix.one_apply, Fin.sum_univ_two, Fin.sum_univ_one]
      fin_cases i
      fin_cases j <;> simp [e₁]
    have h : ‖(!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ)‖ = 1 :=
      norm_eq_one (by simp [Fin.sum_univ_two])
    rw [hmat, h]
    norm_num

end FactoredNormalBoundExamples

end LeanDLRA
