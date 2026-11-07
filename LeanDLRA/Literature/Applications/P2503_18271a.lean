import LeanDLRA.Matrix.Projectors
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Results of arXiv 2503.18271: On-the-fly ROM of the filter density function (TDB/DO)

Matrix-level core of the time-dependent-basis (TDB / dynamically orthogonal) reduction of the
composition matrix `Φ ∈ ℝ^{n × nc}` in arXiv 2503.18271, Sec. 2-3.  The rank-`r` ansatz is
`Φ̂ = U Σ Yᵀ` with `Uᵀ U = I` and `Yᵀ Y = I`, the right-hand side is `M(Φ̂) = -L(Φ̂) + S(Φ̂)` with
`L(Φ̂) = D Φ̂` linear, and the factor equations are the projected ones (Eqs. (22a)-(22c)).

* `linear_mixing_annihilated` (Sec. 3, "left-linear mixing does not move the composition basis"):
  for `L(Φ̂) = D Φ̂` one has `(I - Y Yᵀ) L(Φ̂)ᵀ U Σ⁻ᵀ = 0`, so only the source term moves `Y`.
  `Y_equation_source_only` gives the consequence for `M = -L + S`.  The proof uses only `Yᵀ Y = I`
  and needs no invertibility of `Σ`.
* `tdb_velocity_gauge_free`: for the factor velocities written with arbitrary `r × r` gauge matrices
  `A` (in `U̇ = ... + U A`) and `B` (in `Ẏ = ... + Y B`), the velocity of `Φ̂ = U Σ Yᵀ` equals the
  tangent-space projection `P_{Φ̂}(M)` of Eq. (11), and the gauge terms cancel.
  `tdb_velocity_gauge_invariant` states the consequence of the paper's remark that any skew gauge
  gives equivalent approximations: two gauge choices give the same `Φ̂̇`.

Core definitions used: `Matrix.tangentProj` (= `LeanDLRA.tangentProj`, the tangent projector of
`LeanDLRA/Matrix/Projectors.lean`, with the explicit formula `tangentProj_apply`), matrix
transposition and `Matrix` inverse from Mathlib.  No new definitions are introduced.

Differences from the paper and what is not formalized:
* The gauge statement is proved for the velocity `Φ̂̇` only.  The paper's claim that different skew
  gauges give the same trajectory `Φ̂(t)` needs uniqueness for the projected ODE on the rank-`r`
  manifold (a locally Lipschitz tangent projector) and is cited to Ref. [20] in the paper; it is
  left out.
* The velocity identities need the Y-gauge `B` to be skew (`Bᵀ = -B`, which cancels the terms
  `U Σ B Yᵀ`), but hold for every `A`: the U-gauge `A` cancels without any symmetry.  Skewness
  of `A` and `B` is what keeps `Uᵀ U = I` and `Yᵀ Y = I` along the flow; that is the separate
  result `GaugeODE.transpose_mul_self_eq_of_skew`, not reproved here.
* The paper's Σ-equation (22c) is written for the DO gauge `A = B = 0`; the general-gauge form
  `Σ̇ = Uᵀ M Y + Σ B - A Σ` is the one forced by `Φ̂̇ = P_{Φ̂}(M)`, as stated in the hypotheses.
* The PDE/SGS model, the Langevin equation and the Vreman closure of the paper are not formalized.
-/

open scoped Matrix

namespace LeanDLRA.Literature.P2503_18271

variable {n nc r : Type*} [Fintype n] [Fintype nc] [Fintype r]

/-- **Sec. 3, left-linear mixing does not move the composition basis** (arXiv 2503.18271,
Sec. 3).  For the linear mixing term `L(Φ̂) = D Φ̂` evaluated at `Φ̂ = U Σ Yᵀ`, the identity
`(I - Y Yᵀ) L(Φ̂)ᵀ U Σ⁻ᵀ = 0` holds, given orthonormal columns `Yᵀ Y = I`.
The paper's `Σ⁻ᵀ` is `(Σ⁻¹)ᵀ` in Lean; no invertibility of `Σ` is needed. -/
theorem linear_mixing_annihilated [DecidableEq nc] [DecidableEq r]
    (D : Matrix n n ℝ) (U : Matrix n r ℝ) (Sg : Matrix r r ℝ) (Y : Matrix nc r ℝ)
    (hY : Yᵀ * Y = 1) :
    (1 - Y * Yᵀ) * ((D * (U * Sg * Yᵀ))ᵀ * U * (Sg⁻¹)ᵀ) = 0 := by
  have hYY : (1 - Y * Yᵀ) * Y = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hY, Matrix.mul_one, sub_self]
  have hX : (U * Sg * Yᵀ)ᵀ = Y * (Sgᵀ * Uᵀ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  have key : (1 - Y * Yᵀ) * (D * (U * Sg * Yᵀ))ᵀ = 0 := by
    rw [Matrix.transpose_mul, hX, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - Y * Yᵀ) Y, hYY,
      Matrix.zero_mul]
  rw [show (1 - Y * Yᵀ) * ((D * (U * Sg * Yᵀ))ᵀ * U * (Sg⁻¹)ᵀ)
      = ((1 - Y * Yᵀ) * (D * (U * Sg * Yᵀ))ᵀ) * U * (Sg⁻¹)ᵀ by simp only [Matrix.mul_assoc],
    key, Matrix.zero_mul, Matrix.zero_mul]

/-- Non-vacuity of `linear_mixing_annihilated`: the orthonormality hypothesis `Yᵀ Y = I` holds
for the unit vector `Y = e₁ ∈ ℝ^{2 × 1}`. -/
example : (!![(1 : ℝ); 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * !![(1 : ℝ); 0] = 1 := by
  ext i j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  fin_cases i
  simp [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two]

/-- **Sec. 3, the source term alone drives `Y`** (arXiv 2503.18271, Eq. (19)/(22b) with
`M(Φ̂) = -L(Φ̂) + S(Φ̂)`): the `Y`-part of the projected right-hand side is
`(I - Y Yᵀ) M(Φ̂)ᵀ U Σ⁻ᵀ = (I - Y Yᵀ) S(Φ̂)ᵀ U Σ⁻ᵀ` for the linear term `L(Φ̂) = D Φ̂`. -/
theorem Y_equation_source_only [DecidableEq nc] [DecidableEq r]
    (D : Matrix n n ℝ) (U : Matrix n r ℝ) (Sg : Matrix r r ℝ) (Y : Matrix nc r ℝ)
    (Srce : Matrix n nc ℝ) (hY : Yᵀ * Y = 1) :
    (1 - Y * Yᵀ) * ((-(D * (U * Sg * Yᵀ)) + Srce)ᵀ * U * (Sg⁻¹)ᵀ)
      = (1 - Y * Yᵀ) * (Srceᵀ * U * (Sg⁻¹)ᵀ) := by
  have h := linear_mixing_annihilated D U Sg Y hY
  have e : (-(D * (U * Sg * Yᵀ)) + Srce)ᵀ * U * (Sg⁻¹)ᵀ
      = -((D * (U * Sg * Yᵀ))ᵀ * U * (Sg⁻¹)ᵀ) + Srceᵀ * U * (Sg⁻¹)ᵀ := by
    simp only [Matrix.transpose_add, Matrix.transpose_neg, Matrix.add_mul, Matrix.neg_mul]
  rw [e, Matrix.mul_add, Matrix.mul_neg, h, neg_zero, zero_add]

/-- **Gauge-free velocity of the factorized composition matrix** (arXiv 2503.18271, Eqs. (11)-(22)).
Let `Φ̂ = U Σ Yᵀ` with `Σ` invertible, and let the factor velocities be
`U̇ = (I - U Uᵀ) M Y Σ⁻¹ + U A`, `Ẏ = (I - Y Yᵀ) Mᵀ U Σ⁻ᵀ + Y B`, `Σ̇ = Uᵀ M Y + Σ B - A Σ`,
with `A` arbitrary and `B` skew (`Bᵀ = -B`) of size `r × r`.  Then
`U̇ Σ Yᵀ + U Σ̇ Yᵀ + U Σ Ẏᵀ = P_{Φ̂}(M)`, the tangent-space projection `tangentProj U Y M`.
The gauge terms cancel, so the velocity does not depend on the gauge; `A = B = 0` is the DO choice
of the paper. -/
theorem tdb_velocity_gauge_free [DecidableEq n] [DecidableEq nc] [DecidableEq r]
    (U : Matrix n r ℝ) (Sg : Matrix r r ℝ) (Y : Matrix nc r ℝ) (M : Matrix n nc ℝ)
    (hSg : Sg.det ≠ 0)
    (U' : Matrix n r ℝ) (Sg' : Matrix r r ℝ) (Y' : Matrix nc r ℝ) (A B : Matrix r r ℝ)
    (hU' : U' = (1 - U * Uᵀ) * (M * Y * Sg⁻¹) + U * A)
    (hY' : Y' = (1 - Y * Yᵀ) * (Mᵀ * U * (Sg⁻¹)ᵀ) + Y * B)
    (hSg' : Sg' = Uᵀ * M * Y + Sg * B - A * Sg) (hB : Bᵀ = -B) :
    U' * Sg * Yᵀ + U * Sg' * Yᵀ + U * Sg * Y'ᵀ = tangentProj U Y M := by
  have hUnit : IsUnit Sg.det := isUnit_iff_ne_zero.2 hSg
  have c1 : ∀ X : Matrix r nc ℝ, Sg⁻¹ * (Sg * X) = X := fun X =>
    Matrix.nonsing_inv_mul_cancel_left Sg X hUnit
  have c2 : ∀ X : Matrix r nc ℝ, Sg * (Sg⁻¹ * X) = X := fun X =>
    Matrix.mul_nonsing_inv_cancel_left Sg X hUnit
  subst hU' hY' hSg'
  rw [tangentProj_apply]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
    hB, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, c1, c2]
  abel

/-- **Gauge invariance of the composition velocity** (arXiv 2503.18271, the remark after Eq. (9),
"any skew-symmetric choice ... results in equivalent low-rank approximations").  Two gauge
choices `(A₁, B₁)` and `(A₂, B₂)` of the factor velocities give the same velocity
`Φ̂̇ = U̇ Σ Yᵀ + U Σ̇ Yᵀ + U Σ Ẏᵀ` of the approximation.  Only the velocity is compared; the
equality of the trajectories is not formalized (see the module docstring). -/
theorem tdb_velocity_gauge_invariant [DecidableEq n] [DecidableEq nc] [DecidableEq r]
    (U : Matrix n r ℝ) (Sg : Matrix r r ℝ) (Y : Matrix nc r ℝ) (M : Matrix n nc ℝ)
    (hSg : Sg.det ≠ 0)
    (U₁ : Matrix n r ℝ) (Sg₁ : Matrix r r ℝ) (Y₁ : Matrix nc r ℝ) (A₁ B₁ : Matrix r r ℝ)
    (hU₁ : U₁ = (1 - U * Uᵀ) * (M * Y * Sg⁻¹) + U * A₁)
    (hY₁ : Y₁ = (1 - Y * Yᵀ) * (Mᵀ * U * (Sg⁻¹)ᵀ) + Y * B₁)
    (hSg₁ : Sg₁ = Uᵀ * M * Y + Sg * B₁ - A₁ * Sg) (hB₁ : B₁ᵀ = -B₁)
    (U₂ : Matrix n r ℝ) (Sg₂ : Matrix r r ℝ) (Y₂ : Matrix nc r ℝ) (A₂ B₂ : Matrix r r ℝ)
    (hU₂ : U₂ = (1 - U * Uᵀ) * (M * Y * Sg⁻¹) + U * A₂)
    (hY₂ : Y₂ = (1 - Y * Yᵀ) * (Mᵀ * U * (Sg⁻¹)ᵀ) + Y * B₂)
    (hSg₂ : Sg₂ = Uᵀ * M * Y + Sg * B₂ - A₂ * Sg) (hB₂ : B₂ᵀ = -B₂) :
    U₁ * Sg * Yᵀ + U * Sg₁ * Yᵀ + U * Sg * Y₁ᵀ = U₂ * Sg * Yᵀ + U * Sg₂ * Yᵀ + U * Sg * Y₂ᵀ := by
  rw [tdb_velocity_gauge_free U Sg Y M hSg U₁ Sg₁ Y₁ A₁ B₁ hU₁ hY₁ hSg₁ hB₁,
    tdb_velocity_gauge_free U Sg Y M hSg U₂ Sg₂ Y₂ A₂ B₂ hU₂ hY₂ hSg₂ hB₂]

/-- Non-vacuity: the gauge-free factor velocities (`A = B = 0`) satisfy the hypotheses of
`tdb_velocity_gauge_free`, which is then an instance of the statement. -/
example [DecidableEq n] [DecidableEq nc] [DecidableEq r]
    (U : Matrix n r ℝ) (Sg : Matrix r r ℝ) (Y : Matrix nc r ℝ) (M : Matrix n nc ℝ)
    (hSg : Sg.det ≠ 0) :
    ((1 - U * Uᵀ) * (M * Y * Sg⁻¹) + U * (0 : Matrix r r ℝ)) * Sg * Yᵀ
        + U * (Uᵀ * M * Y + Sg * (0 : Matrix r r ℝ) - (0 : Matrix r r ℝ) * Sg) * Yᵀ
        + U * Sg * ((1 - Y * Yᵀ) * (Mᵀ * U * (Sg⁻¹)ᵀ) + Y * (0 : Matrix r r ℝ))ᵀ
      = tangentProj U Y M :=
  tdb_velocity_gauge_free U Sg Y M hSg _ _ _ 0 0 rfl rfl rfl (by simp)

end LeanDLRA.Literature.P2503_18271
