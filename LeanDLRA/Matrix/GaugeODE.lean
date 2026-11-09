import Mathlib
import LeanDLRA.Foundations.ODE
import LeanDLRA.Matrix.Projectors
import LeanDLRA.LinearAlgebra.Frobenius.Defs

/-!
# Gauge-fixed factor ODEs of dynamical low-rank approximation

Dynamical low-rank approximation (DLRA) of a time-dependent matrix `A(t) ∈ ℝ^{m × n}` seeks
`Y(t)` of rank `r` with `Ẏ = P(Y) Ȧ`, where `P(Y)` is the orthogonal projector onto the tangent
space of the rank-`r` manifold at `Y`.  Writing `Y = U S Vᵀ` with `Uᵀ U = 1`, `Vᵀ V = 1` and `S`
invertible, the projector is (Koch–Lubich, SIMAX 29 (2007), Lemma 4.1; Lubich–Oseledets,
arXiv 1301.1058, eq. (7))

  `P(Y) Z = U Uᵀ Z + Z V Vᵀ - U Uᵀ Z V Vᵀ`.

In this library the formula is `LeanDLRA.tangentProj U V` (`Matrix/Projectors.lean`).  That it is
the *orthogonal* projector onto the tangent space `{U B + C Vᵀ}` is `isOrthProj_tangentProj` and
`mem_range_tangentProj` there.  It depends only on `Y`, not on the chosen factorization
(`tangentProj_eq_of_factorization` below).  The main statements are first written with the
explicit formula and then restated with `tangentProj` (last section).

**Koch–Lubich, Prop. 2.1**, as quoted in arXiv 1301.1058, §2, eqs. (3)–(5): given a
decomposition `Y₀ = U₀ S₀ V₀ᵀ` of the starting value and imposing the gauge conditions
`Uᵀ U̇ = 0`, `Vᵀ V̇ = 0`, the DLRA solution `Y(t)` admits a unique decomposition
`Y(t) = U(t) S(t) V(t)ᵀ` of this form, and its factors satisfy

  `U̇ = (I - U Uᵀ) Ȧ V S⁻¹`,  `Ṡ = Uᵀ Ȧ V`,  `V̇ = (I - V Vᵀ) Ȧᵀ U S⁻ᵀ`.

Derivatives are taken in the Frobenius norm (`Matrix.frobeniusNormedAddCommGroup`, activated as a
local instance).

## What is proved, and what is not

* **Pointwise equivalence** (`hasDerivAt_factorProduct_iff_factorODE` and the one-sided
  `hasDerivWithinAt_factorProduct_iff_factorODE`): for factors that are differentiable at `t`,
  orthonormal and gauge-fixed at `t`, with `S t` invertible, `Ẏ = P(Y) Ȧ` holds at `t` if and
  only if the factor ODEs hold at `t`.
* **Trajectory level, factor system ⇒ DLRA** (`factorODE_solution_isDLRA`): solutions of the
  factor system on `[a, b]` with orthonormal initial factors stay orthonormal (Grönwall, without
  assuming the gauge a priori), and `Y = U S Vᵀ` solves the DLRA equation on `[a, b]`.
* **Trajectory level, DLRA ⇒ factor system, for a given factorization**
  (`factorODE_of_isDLRA`): if a DLRA solution is written as `Y = U S Vᵀ` with continuous,
  right-differentiable factors that satisfy the gauge conditions, are orthonormal at the initial
  time and have `S` invertible, then the factors stay orthonormal and solve the factor system.
* **Not proved here**: the *existence and uniqueness* of a differentiable gauge-fixed
  factorization along a given DLRA solution (the "admits a unique decomposition" part of the
  cited statement).  The "⇒" results take such a factorization as a hypothesis.  Koch–Lubich
  obtain it by solving the factor system (local existence while `S` stays invertible), applying
  the "⇐" direction, and invoking uniqueness for the DLRA equation.  Neither the local existence
  theory for the factor system (it is not globally Lipschitz) nor uniqueness for the DLRA
  equation in `Y`-form is formalized in this file.

## Main results

* `LeanDLRA.GaugeODE.hasDerivWithinAt_mul`, `hasDerivWithinAt_transpose`: product rule for
  rectangular matrix products and differentiation of the transpose.
* `LeanDLRA.hasDerivAt_factorProduct_of_factorODE` (Prop. 2.1, "⇐", pointwise): if `U, S, V`
  satisfy the factor ODEs at `t` and `S t` is invertible, then `Y = U S Vᵀ` satisfies
  `Ẏ = U Uᵀ Ȧ + Ȧ V Vᵀ - U Uᵀ Ȧ V Vᵀ = P(Y) Ȧ` at `t`.  (Orthonormality of the factors is not
  needed for this identity; it is needed for `P(Y)` to be the *orthogonal* tangent projector.)
* `LeanDLRA.factorODE_of_hasDerivAt_factorProduct` (Prop. 2.1, "⇒", pointwise, for a given
  gauge-fixed factorization): if `Y = U S Vᵀ` satisfies `Ẏ = P(Y) Ȧ`, `Uᵀ U = 1`, `Vᵀ V = 1`
  and the gauge conditions hold, then `Ṡ = Uᵀ Ȧ V`, `U̇ S = (I - U Uᵀ) Ȧ V`,
  `V̇ Sᵀ = (I - V Vᵀ) Ȧᵀ U`; with `S` invertible these are exactly the factor ODEs
  (`hasDerivAt_factorProduct_iff_factorODE`).
* `LeanDLRA.transpose_mul_self_eq_of_skew`: if `Uᵀ U̇` is skew-symmetric along a convex set, then
  `Uᵀ U` is constant there; in particular (`transpose_mul_self_eq_one_of_gauge`, and the
  right-derivative version `transpose_mul_self_eq_one_of_gauge_right`) the gauge `Uᵀ U̇ = 0`
  preserves orthonormality of the columns.
* `LeanDLRA.transpose_mul_self_eq_one_of_odeSolution`: a solution of the factor ODE
  `U̇ = (I - U Uᵀ) G(t)` starting from orthonormal columns keeps orthonormal columns, without
  assuming the gauge a priori (only local boundedness of `Uᵀ G` on `[a, b)`).  The gauge then
  follows from `transpose_mul_one_sub_eq_zero` / `gauge_of_factorODE`.  This is the
  orthonormality part of the proof of Prop. 2.1.
* `LeanDLRA.factorODE_solution_isDLRA`: on an interval, solutions of the factor system with
  orthonormal initial factors and invertible `S` keep orthonormal factors and `Y = U S Vᵀ`
  solves `Ẏ = P(Y) Ȧ` (in the right-derivative convention of `ODESolution`).
* `LeanDLRA.factorODE_of_isDLRA`: the converse along a trajectory, for a given gauge-fixed
  factorization (see above).
* `LeanDLRA.tangentProj_eq_of_factorization`, `hasDerivAt_factorProduct_tangentProj_iff_factorODE`,
  `factorODE_solution_isDLRA_tangentProj`: `P(Y)` depends only on `Y`, and the main results
  restated with the orthogonal projector `tangentProj`.
* A nondegenerate example (`m = n = 2`, `r = 1`, rotating `U(t)`, `P(Y) ≠ id`) showing that the
  hypotheses of `factorODE_solution_isDLRA` and `factorODE_of_isDLRA` are jointly satisfiable.

## Notes

The time derivative `Ȧ(t)` enters only through its value; we write it as an arbitrary matrix
`Ad` (or a function `Ad : ℝ → Matrix m n ℝ`).  In the trajectory-level statements the right-hand
side of the DLRA equation is the *time-dependent* matrix
`U(t) U(t)ᵀ Ȧ(t) + Ȧ(t) V(t) V(t)ᵀ - U(t) U(t)ᵀ Ȧ(t) V(t) V(t)ᵀ = P(Y(t)) Ȧ(t)`, with `P(Y(t))`
written through the factors `U(t)`, `V(t)`; it is not stated as a vector field
`Y ↦ P(Y) F(t, Y)` in the state `Y`.  Since `P(Y)` depends only on `Y`
(`tangentProj_eq_of_factorization`), this is the DLRA equation evaluated along the trajectory; for
the nonlinear DLRA equation `Ẏ = P(Y) F(t, Y)` take `Ad t := F(t, Y(t))`.  Feeding these results
into uniqueness or stability results for the DLRA equation in `Y`-form requires this
identification as an extra step.  The inverse transpose `S⁻ᵀ` is written `(S⁻¹)ᵀ`.
-/

open Set
open scoped Matrix

namespace LeanDLRA

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

namespace GaugeODE

variable {k l m n : Type*} [Fintype k] [Fintype l] [Fintype m] [Fintype n]

variable {s : Set ℝ} {t : ℝ}

/- The calculus lemmas below only need the outer index types to be finite: their statements use
the product topology, and a `Fintype` structure is chosen in the proofs to apply the Frobenius
norm. -/
omit [Fintype m] [Fintype n]
variable [Finite m] [Finite n]

/-- Product rule for rectangular matrix-valued curves, within a set. -/
theorem hasDerivWithinAt_mul {K : ℝ → Matrix m l ℝ} {L : ℝ → Matrix l n ℝ}
    {K' : Matrix m l ℝ} {L' : Matrix l n ℝ} (hK : HasDerivWithinAt K K' s t)
    (hL : HasDerivWithinAt L L' s t) :
    HasDerivWithinAt (fun t => K t * L t) (K' * L t + K t * L') s t := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  have h := (Frobenius.mulCLM : Matrix m l ℝ →L[ℝ] Matrix l n ℝ →L[ℝ] Matrix m n ℝ)
    |>.hasDerivWithinAt_of_bilinear hK hL
  rw [add_comm] at h
  exact h

/-- Product rule for rectangular matrix-valued curves. -/
theorem hasDerivAt_mul {K : ℝ → Matrix m l ℝ} {L : ℝ → Matrix l n ℝ}
    {K' : Matrix m l ℝ} {L' : Matrix l n ℝ} (hK : HasDerivAt K K' t) (hL : HasDerivAt L L' t) :
    HasDerivAt (fun t => K t * L t) (K' * L t + K t * L') t := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  exact hasDerivWithinAt_univ.mp
    (hasDerivWithinAt_mul (hasDerivWithinAt_univ.mpr hK) (hasDerivWithinAt_univ.mpr hL))

/-- Transposition commutes with differentiation, within a set. -/
theorem hasDerivWithinAt_transpose {K : ℝ → Matrix m n ℝ} {K' : Matrix m n ℝ}
    (hK : HasDerivWithinAt K K' s t) : HasDerivWithinAt (fun t => (K t)ᵀ) K'ᵀ s t := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  exact (Frobenius.transposeCLM : Matrix m n ℝ →L[ℝ] Matrix n m ℝ).hasFDerivAt
    |>.comp_hasDerivWithinAt t hK

/-- Transposition commutes with differentiation. -/
theorem hasDerivAt_transpose {K : ℝ → Matrix m n ℝ} {K' : Matrix m n ℝ}
    (hK : HasDerivAt K K' t) : HasDerivAt (fun t => (K t)ᵀ) K'ᵀ t := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  exact hasDerivWithinAt_univ.mp (hasDerivWithinAt_transpose (hasDerivWithinAt_univ.mpr hK))

/-- Continuity of `t ↦ K t * L t` on a set. -/
theorem continuousOn_mul {K : ℝ → Matrix m l ℝ} {L : ℝ → Matrix l n ℝ}
    (hK : ContinuousOn K s) (hL : ContinuousOn L s) : ContinuousOn (fun t => K t * L t) s := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  exact ((Frobenius.mulCLM : Matrix m l ℝ →L[ℝ] Matrix l n ℝ →L[ℝ] Matrix m n ℝ).continuous
    |>.comp_continuousOn hK).clm_apply hL

/-- Continuity of `t ↦ (K t)ᵀ` on a set. -/
theorem continuousOn_transpose {K : ℝ → Matrix m n ℝ} (hK : ContinuousOn K s) :
    ContinuousOn (fun t => (K t)ᵀ) s := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  exact (Frobenius.transposeCLM : Matrix m n ℝ →L[ℝ] Matrix n m ℝ).continuous
    |>.comp_continuousOn hK

/-- Derivative of a factorized curve `t ↦ U t * S t * (V t)ᵀ`, within a set. -/
theorem hasDerivWithinAt_factorProduct {r : Type*} [Fintype r] {U : ℝ → Matrix m r ℝ}
    {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix n r ℝ} {U' : Matrix m r ℝ} {S' : Matrix r r ℝ}
    {V' : Matrix n r ℝ} (hU : HasDerivWithinAt U U' s t) (hS : HasDerivWithinAt S S' s t)
    (hV : HasDerivWithinAt V V' s t) :
    HasDerivWithinAt (fun t => U t * S t * (V t)ᵀ)
      (U' * S t * (V t)ᵀ + U t * S' * (V t)ᵀ + U t * S t * V'ᵀ) s t := by
  have h := hasDerivWithinAt_mul (hasDerivWithinAt_mul hU hS) (hasDerivWithinAt_transpose hV)
  convert h using 1
  simp only [Matrix.add_mul]

/-- Derivative of a factorized curve `t ↦ U t * S t * (V t)ᵀ`. -/
theorem hasDerivAt_factorProduct {r : Type*} [Fintype r] {U : ℝ → Matrix m r ℝ}
    {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix n r ℝ} {U' : Matrix m r ℝ} {S' : Matrix r r ℝ}
    {V' : Matrix n r ℝ} (hU : HasDerivAt U U' t) (hS : HasDerivAt S S' t)
    (hV : HasDerivAt V V' t) :
    HasDerivAt (fun t => U t * S t * (V t)ᵀ)
      (U' * S t * (V t)ᵀ + U t * S' * (V t)ᵀ + U t * S t * V'ᵀ) t := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  exact hasDerivWithinAt_univ.mp (hasDerivWithinAt_factorProduct (hasDerivWithinAt_univ.mpr hU)
    (hasDerivWithinAt_univ.mpr hS) (hasDerivWithinAt_univ.mpr hV))

end GaugeODE

open GaugeODE

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n]
  [DecidableEq r]

/-! ### Algebraic core of Prop. 2.1 -/

/-- Algebraic core of Koch–Lubich Prop. 2.1 ("⇐"): inserting the factor ODEs into the product
rule `U̇ S Vᵀ + U Ṡ Vᵀ + U S V̇ᵀ` gives `P(Y) Ȧ = U Uᵀ Ȧ + Ȧ V Vᵀ - U Uᵀ Ȧ V Vᵀ`.  Only the
invertibility of `S` is used. -/
theorem factorODE_sum_eq_tangent (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ)
    (Ad : Matrix m n ℝ) (hS : IsUnit S.det) :
    (1 - U * Uᵀ) * Ad * V * S⁻¹ * S * Vᵀ + U * (Uᵀ * Ad * V) * Vᵀ
        + U * S * ((1 - V * Vᵀ) * Adᵀ * U * (S⁻¹)ᵀ)ᵀ
      = U * Uᵀ * Ad + Ad * V * Vᵀ - U * Uᵀ * Ad * V * Vᵀ := by
  have h1 : ((1 - V * Vᵀ) * Adᵀ * U * (S⁻¹)ᵀ)ᵀ = S⁻¹ * (Uᵀ * (Ad * (1 - V * Vᵀ))) := by
    simp [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.mul_assoc]
  rw [h1, Matrix.nonsing_inv_mul_cancel_right _ _ hS, Matrix.mul_assoc U S,
    Matrix.mul_nonsing_inv_cancel_left _ _ hS]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

/-- Algebraic core of Koch–Lubich Prop. 2.1 ("⇒"): if `U̇ S Vᵀ + U Ṡ Vᵀ + U S V̇ᵀ = P(Y) Ȧ` with
orthonormal `U, V` and the gauge conditions `Uᵀ U̇ = 0`, `Vᵀ V̇ = 0`, then
`Ṡ = Uᵀ Ȧ V`, `U̇ S = (I - U Uᵀ) Ȧ V` and `V̇ Sᵀ = (I - V Vᵀ) Ȧᵀ U`. -/
theorem factorODE_of_sum_eq_tangent {U U' : Matrix m r ℝ} {S S' : Matrix r r ℝ}
    {V V' : Matrix n r ℝ} {Ad : Matrix m n ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hgU : Uᵀ * U' = 0) (hgV : Vᵀ * V' = 0)
    (h : U' * S * Vᵀ + U * S' * Vᵀ + U * S * V'ᵀ
      = U * Uᵀ * Ad + Ad * V * Vᵀ - U * Uᵀ * Ad * V * Vᵀ) :
    S' = Uᵀ * Ad * V ∧ U' * S = (1 - U * Uᵀ) * Ad * V ∧ V' * Sᵀ = (1 - V * Vᵀ) * Adᵀ * U := by
  have hV' : V'ᵀ * V = 0 := by
    rw [← Matrix.transpose_transpose (V'ᵀ * V), Matrix.transpose_mul, Matrix.transpose_transpose,
      hgV, Matrix.transpose_zero]
  -- right multiplication by `V`
  have hR : U' * S + U * S' = Ad * V := by
    have := congrArg (· * V) h
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, hV, hV', Matrix.mul_one,
      Matrix.mul_zero, add_zero] at this
    rw [this]; abel
  -- left multiplication by `Uᵀ`
  have hL : S * V'ᵀ + S' * Vᵀ = Uᵀ * Ad := by
    have := congrArg (Uᵀ * ·) h
    simp only [Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc, hU, hgU, Matrix.one_mul,
      Matrix.zero_mul, zero_add] at this
    rw [add_comm, this]; abel
  have hS' : S' = Uᵀ * Ad * V := by
    have := congrArg (Uᵀ * ·) hR
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, hU, hgU, Matrix.one_mul,
      Matrix.zero_mul, zero_add] at this
    exact this
  refine ⟨hS', ?_, ?_⟩
  · rw [eq_sub_of_add_eq hR, hS', Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_assoc U, Matrix.mul_assoc U]
  · have h2 : S * V'ᵀ = Uᵀ * Ad * (1 - V * Vᵀ) := by
      rw [eq_sub_of_add_eq hL, hS', Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc _ V]
    have := congrArg Matrix.transpose h2
    simpa [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.mul_assoc] using this

/-! ### Koch–Lubich Prop. 2.1: factor ODEs ⇒ DLRA equation -/

/-- **Koch–Lubich, Prop. 2.1 (factor ODEs ⇒ `Ẏ = P(Y) Ȧ`)**, within a set (e.g. one-sided).
If at time `t` the factors satisfy
`U̇ = (I - U Uᵀ) Ȧ V S⁻¹`, `Ṡ = Uᵀ Ȧ V`, `V̇ = (I - V Vᵀ) Ȧᵀ U S⁻ᵀ` and `S t` is invertible, then
`Y = U S Vᵀ` satisfies `Ẏ = U Uᵀ Ȧ + Ȧ V Vᵀ - U Uᵀ Ȧ V Vᵀ` (`= P(Y) Ȧ` when `Uᵀ U = 1`,
`Vᵀ V = 1`).  Generalization: orthonormality of `U t, V t` is not needed for this identity. -/
theorem hasDerivWithinAt_factorProduct_of_factorODE {U : ℝ → Matrix m r ℝ}
    {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix n r ℝ} {Ad : Matrix m n ℝ} {s : Set ℝ} {t : ℝ}
    (hdet : IsUnit (S t).det)
    (hU : HasDerivWithinAt U ((1 - U t * (U t)ᵀ) * Ad * V t * (S t)⁻¹) s t)
    (hS : HasDerivWithinAt S ((U t)ᵀ * Ad * V t) s t)
    (hV : HasDerivWithinAt V ((1 - V t * (V t)ᵀ) * Adᵀ * U t * ((S t)⁻¹)ᵀ) s t) :
    HasDerivWithinAt (fun t => U t * S t * (V t)ᵀ)
      (U t * (U t)ᵀ * Ad + Ad * V t * (V t)ᵀ - U t * (U t)ᵀ * Ad * V t * (V t)ᵀ) s t := by
  have h := hasDerivWithinAt_factorProduct hU hS hV
  rwa [factorODE_sum_eq_tangent _ _ _ _ hdet] at h

/-- `Y = U S Vᵀ` satisfies `Ẏ = P(Y) Ȧ` at `t` if the factors satisfy the gauge-fixed factor ODEs
of Koch–Lubich, Prop. 2.1 at `t` and `S t` is invertible (two-sided derivative version of
`hasDerivWithinAt_factorProduct_of_factorODE`). -/
theorem hasDerivAt_factorProduct_of_factorODE {U : ℝ → Matrix m r ℝ}
    {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix n r ℝ} {Ad : Matrix m n ℝ} {t : ℝ}
    (hdet : IsUnit (S t).det)
    (hU : HasDerivAt U ((1 - U t * (U t)ᵀ) * Ad * V t * (S t)⁻¹) t)
    (hS : HasDerivAt S ((U t)ᵀ * Ad * V t) t)
    (hV : HasDerivAt V ((1 - V t * (V t)ᵀ) * Adᵀ * U t * ((S t)⁻¹)ᵀ) t) :
    HasDerivAt (fun t => U t * S t * (V t)ᵀ)
      (U t * (U t)ᵀ * Ad + Ad * V t * (V t)ᵀ - U t * (U t)ᵀ * Ad * V t * (V t)ᵀ) t :=
  hasDerivWithinAt_univ.mp (hasDerivWithinAt_factorProduct_of_factorODE hdet
    (hasDerivWithinAt_univ.mpr hU) (hasDerivWithinAt_univ.mpr hS) (hasDerivWithinAt_univ.mpr hV))

/-- With orthonormal columns, `Uᵀ (I - U Uᵀ) = 0`: the factor ODE `U̇ = (I - U Uᵀ) Ȧ V S⁻¹` is
compatible with the gauge condition `Uᵀ U̇ = 0`. -/
theorem transpose_mul_one_sub_eq_zero {U : Matrix m r ℝ} (hU : Uᵀ * U = 1) :
    Uᵀ * (1 - U * Uᵀ) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hU, Matrix.one_mul, sub_self]

/-- The factor ODEs of Prop. 2.1 satisfy the gauge conditions `Uᵀ U̇ = 0`, `Vᵀ V̇ = 0` whenever
`Uᵀ U = 1` and `Vᵀ V = 1`. -/
theorem gauge_of_factorODE {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ}
    (Ad : Matrix m n ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    Uᵀ * ((1 - U * Uᵀ) * Ad * V * S⁻¹) = 0 ∧ Vᵀ * ((1 - V * Vᵀ) * Adᵀ * U * (S⁻¹)ᵀ) = 0 := by
  constructor
  · simp only [← Matrix.mul_assoc, transpose_mul_one_sub_eq_zero hU, Matrix.zero_mul]
  · simp only [← Matrix.mul_assoc, transpose_mul_one_sub_eq_zero hV, Matrix.zero_mul]

/-! ### Koch–Lubich Prop. 2.1: DLRA equation ⇒ factor ODEs -/

/-- **Koch–Lubich, Prop. 2.1 (`Ẏ = P(Y) Ȧ` ⇒ factor ODEs)**, pointwise, within a set on which
derivatives are unique (e.g. `Ici t`).  Let `U, S, V` have derivatives `U̇, Ṡ, V̇` at `t` with
`Uᵀ U = 1`, `Vᵀ V = 1` at `t` and the gauge conditions `Uᵀ U̇ = 0`, `Vᵀ V̇ = 0`.  If `Y = U S Vᵀ`
satisfies `Ẏ = P(Y) Ȧ = U Uᵀ Ȧ + Ȧ V Vᵀ - U Uᵀ Ȧ V Vᵀ`, then `Ṡ = Uᵀ Ȧ V`,
`U̇ S = (I - U Uᵀ) Ȧ V` and `V̇ Sᵀ = (I - V Vᵀ) Ȧᵀ U`.  (Invertibility of `S` is not needed for
this direction.)

Scope: the differentiable, orthonormal, gauge-fixed factorization is a *hypothesis*; its existence
and uniqueness along a DLRA solution (the "admits a unique decomposition" part of the cited
statement) is not proved in this file.  The trajectory-level version is `factorODE_of_isDLRA`. -/
theorem factorODE_of_hasDerivWithinAt_factorProduct {U : ℝ → Matrix m r ℝ}
    {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix n r ℝ} {U' : Matrix m r ℝ} {S' : Matrix r r ℝ}
    {V' : Matrix n r ℝ} {Ad : Matrix m n ℝ} {s : Set ℝ} {t : ℝ} (hs : UniqueDiffWithinAt ℝ s t)
    (hU : HasDerivWithinAt U U' s t) (hS : HasDerivWithinAt S S' s t)
    (hV : HasDerivWithinAt V V' s t) (hUo : (U t)ᵀ * U t = 1) (hVo : (V t)ᵀ * V t = 1)
    (hgU : (U t)ᵀ * U' = 0) (hgV : (V t)ᵀ * V' = 0)
    (hY : HasDerivWithinAt (fun t => U t * S t * (V t)ᵀ)
      (U t * (U t)ᵀ * Ad + Ad * V t * (V t)ᵀ - U t * (U t)ᵀ * Ad * V t * (V t)ᵀ) s t) :
    S' = (U t)ᵀ * Ad * V t ∧ U' * S t = (1 - U t * (U t)ᵀ) * Ad * V t ∧
      V' * (S t)ᵀ = (1 - V t * (V t)ᵀ) * Adᵀ * U t :=
  factorODE_of_sum_eq_tangent hUo hVo hgU hgV
    (hs.eq_deriv _ (hasDerivWithinAt_factorProduct hU hS hV) hY)

/-- **Koch–Lubich, Prop. 2.1 (`Ẏ = P(Y) Ȧ` ⇒ factor ODEs)**, pointwise, two-sided derivatives:
under the gauge conditions and orthonormality at `t`, `Ṡ = Uᵀ Ȧ V`, `U̇ S = (I - U Uᵀ) Ȧ V`,
`V̇ Sᵀ = (I - V Vᵀ) Ȧᵀ U`.  As in `factorODE_of_hasDerivWithinAt_factorProduct`, the gauge-fixed
factorization is assumed, not constructed. -/
theorem factorODE_of_hasDerivAt_factorProduct {U : ℝ → Matrix m r ℝ}
    {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix n r ℝ} {U' : Matrix m r ℝ} {S' : Matrix r r ℝ}
    {V' : Matrix n r ℝ} {Ad : Matrix m n ℝ} {t : ℝ}
    (hU : HasDerivAt U U' t) (hS : HasDerivAt S S' t)
    (hV : HasDerivAt V V' t) (hUo : (U t)ᵀ * U t = 1) (hVo : (V t)ᵀ * V t = 1)
    (hgU : (U t)ᵀ * U' = 0) (hgV : (V t)ᵀ * V' = 0)
    (hY : HasDerivAt (fun t => U t * S t * (V t)ᵀ)
      (U t * (U t)ᵀ * Ad + Ad * V t * (V t)ᵀ - U t * (U t)ᵀ * Ad * V t * (V t)ᵀ) t) :
    S' = (U t)ᵀ * Ad * V t ∧ U' * S t = (1 - U t * (U t)ᵀ) * Ad * V t ∧
      V' * (S t)ᵀ = (1 - V t * (V t)ᵀ) * Adᵀ * U t :=
  factorODE_of_sum_eq_tangent hUo hVo hgU hgV ((hasDerivAt_factorProduct hU hS hV).unique hY)

/-- **Koch–Lubich, Prop. 2.1 (pointwise equivalence)**, within a set on which derivatives are
unique (e.g. `Ici t` for right derivatives).  Let `U, S, V` have derivatives `U̇, Ṡ, V̇` within `s`
at `t` with `Uᵀ U = 1`, `Vᵀ V = 1`, `S` invertible and the gauge conditions `Uᵀ U̇ = 0`,
`Vᵀ V̇ = 0` at `t`.  Then `Y = U S Vᵀ` satisfies `Ẏ = P(Y) Ȧ` at `t` if and only if
`U̇ = (I - U Uᵀ) Ȧ V S⁻¹`, `Ṡ = Uᵀ Ȧ V`, `V̇ = (I - V Vᵀ) Ȧᵀ U S⁻ᵀ`.  The gauge-fixed
factorization is a hypothesis (see the module docstring). -/
theorem hasDerivWithinAt_factorProduct_iff_factorODE {U : ℝ → Matrix m r ℝ}
    {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix n r ℝ} {U' : Matrix m r ℝ} {S' : Matrix r r ℝ}
    {V' : Matrix n r ℝ} {Ad : Matrix m n ℝ} {s : Set ℝ} {t : ℝ} (hs : UniqueDiffWithinAt ℝ s t)
    (hU : HasDerivWithinAt U U' s t) (hS : HasDerivWithinAt S S' s t)
    (hV : HasDerivWithinAt V V' s t) (hUo : (U t)ᵀ * U t = 1) (hVo : (V t)ᵀ * V t = 1)
    (hdet : IsUnit (S t).det) (hgU : (U t)ᵀ * U' = 0) (hgV : (V t)ᵀ * V' = 0) :
    HasDerivWithinAt (fun t => U t * S t * (V t)ᵀ)
        (U t * (U t)ᵀ * Ad + Ad * V t * (V t)ᵀ - U t * (U t)ᵀ * Ad * V t * (V t)ᵀ) s t ↔
      U' = (1 - U t * (U t)ᵀ) * Ad * V t * (S t)⁻¹ ∧ S' = (U t)ᵀ * Ad * V t ∧
        V' = (1 - V t * (V t)ᵀ) * Adᵀ * U t * ((S t)⁻¹)ᵀ := by
  constructor
  · intro hY
    obtain ⟨h1, h2, h3⟩ :=
      factorODE_of_hasDerivWithinAt_factorProduct hs hU hS hV hUo hVo hgU hgV hY
    refine ⟨?_, h1, ?_⟩
    · rw [← h2, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
    · have hdetT : IsUnit (S t)ᵀ.det := by rwa [Matrix.det_transpose]
      rw [Matrix.transpose_nonsing_inv, ← h3, Matrix.mul_nonsing_inv_cancel_right _ _ hdetT]
  · rintro ⟨rfl, rfl, rfl⟩
    exact hasDerivWithinAt_factorProduct_of_factorODE hdet hU hS hV

/-- **Koch–Lubich, Prop. 2.1 (pointwise equivalence)**.  Let `U, S, V` be differentiable at `t`
with `Uᵀ U = 1`, `Vᵀ V = 1`, `S` invertible and the gauge conditions `Uᵀ U̇ = 0`, `Vᵀ V̇ = 0`.
Then `Y = U S Vᵀ` satisfies `Ẏ = P(Y) Ȧ` at `t` if and only if
`U̇ = (I - U Uᵀ) Ȧ V S⁻¹`, `Ṡ = Uᵀ Ȧ V`, `V̇ = (I - V Vᵀ) Ȧᵀ U S⁻ᵀ`.

Scope: this is the pointwise content of Prop. 2.1 for a *given* differentiable gauge-fixed
factorization; the existence and uniqueness of such a factorization along a DLRA solution is not
proved here (see the module docstring).  Trajectory-level versions: `factorODE_solution_isDLRA`
(factor system ⇒ DLRA) and `factorODE_of_isDLRA` (DLRA ⇒ factor system for a given
factorization). -/
theorem hasDerivAt_factorProduct_iff_factorODE {U : ℝ → Matrix m r ℝ}
    {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix n r ℝ} {U' : Matrix m r ℝ} {S' : Matrix r r ℝ}
    {V' : Matrix n r ℝ} {Ad : Matrix m n ℝ} {t : ℝ}
    (hU : HasDerivAt U U' t) (hS : HasDerivAt S S' t)
    (hV : HasDerivAt V V' t) (hUo : (U t)ᵀ * U t = 1) (hVo : (V t)ᵀ * V t = 1)
    (hdet : IsUnit (S t).det) (hgU : (U t)ᵀ * U' = 0) (hgV : (V t)ᵀ * V' = 0) :
    HasDerivAt (fun t => U t * S t * (V t)ᵀ)
        (U t * (U t)ᵀ * Ad + Ad * V t * (V t)ᵀ - U t * (U t)ᵀ * Ad * V t * (V t)ᵀ) t ↔
      U' = (1 - U t * (U t)ᵀ) * Ad * V t * (S t)⁻¹ ∧ S' = (U t)ᵀ * Ad * V t ∧
        V' = (1 - V t * (V t)ᵀ) * Adᵀ * U t * ((S t)⁻¹)ᵀ := by
  constructor
  · intro hY
    obtain ⟨h1, h2, h3⟩ :=
      factorODE_of_hasDerivAt_factorProduct hU hS hV hUo hVo hgU hgV hY
    refine ⟨?_, h1, ?_⟩
    · rw [← h2, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
    · have hdetT : IsUnit (S t)ᵀ.det := by rwa [Matrix.det_transpose]
      rw [Matrix.transpose_nonsing_inv, ← h3, Matrix.mul_nonsing_inv_cancel_right _ _ hdetT]
  · rintro ⟨rfl, rfl, rfl⟩
    exact hasDerivAt_factorProduct_of_factorODE hdet hU hS hV

/-! ### Orthonormality of the factors is preserved -/

omit [DecidableEq m] [DecidableEq r] [Fintype r] in
/-- If `Uᵀ U̇` is skew-symmetric along a convex set `s` (e.g. an interval), then `Uᵀ U` is
constant on `s`.  (Koch–Lubich, proof of Prop. 2.1.) -/
theorem transpose_mul_self_eq_of_skew [Finite r] {U U' : ℝ → Matrix m r ℝ} {s : Set ℝ}
    (hs : Convex ℝ s)
    (hU : ∀ t ∈ s, HasDerivWithinAt U (U' t) s t)
    (hskew : ∀ t ∈ s, ((U t)ᵀ * U' t)ᵀ + (U t)ᵀ * U' t = 0) {t₀ t : ℝ} (ht₀ : t₀ ∈ s)
    (ht : t ∈ s) : (U t)ᵀ * U t = (U t₀)ᵀ * U t₀ := by
  have := Fintype.ofFinite r
  have hd : ∀ x ∈ s, HasDerivWithinAt (fun t => (U t)ᵀ * U t) 0 s x := by
    intro x hx
    have h := hasDerivWithinAt_mul (hasDerivWithinAt_transpose (hU x hx)) (hU x hx)
    have e : (U' x)ᵀ * U x + (U x)ᵀ * U' x = 0 := by
      rw [← hskew x hx, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [e] at h
    exact h
  have h := hs.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hd (fun x _ => by simp) ht₀ ht
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  exact h

omit [DecidableEq m] [Fintype r] in
/-- **Orthonormality is preserved under the gauge `Uᵀ U̇ = 0`**: if `U` is differentiable along a
convex set `s` with `Uᵀ U̇ = 0` there and `U(t₀)ᵀ U(t₀) = 1`, then `U(t)ᵀ U(t) = 1` on `s`. -/
theorem transpose_mul_self_eq_one_of_gauge [Finite r] {U U' : ℝ → Matrix m r ℝ} {s : Set ℝ}
    (hs : Convex ℝ s) (hU : ∀ t ∈ s, HasDerivWithinAt U (U' t) s t)
    (hg : ∀ t ∈ s, (U t)ᵀ * U' t = 0) {t₀ : ℝ} (ht₀ : t₀ ∈ s) (h₀ : (U t₀)ᵀ * U t₀ = 1)
    {t : ℝ} (ht : t ∈ s) : (U t)ᵀ * U t = 1 := by
  rw [transpose_mul_self_eq_of_skew hs hU
    (fun x hx => by rw [hg x hx, Matrix.transpose_zero, add_zero]) ht₀ ht, h₀]

omit [DecidableEq m] [Fintype r] in
/-- **Orthonormality is preserved under the gauge `Uᵀ U̇ = 0`**, right-derivative version (the
`ODESolution` convention): if `U` is continuous on `[a, b]` with right derivatives `U̇` on `[a, b)`
satisfying `Uᵀ U̇ = 0` there, and `U(a)ᵀ U(a) = 1`, then `U(t)ᵀ U(t) = 1` on `[a, b]`. -/
theorem transpose_mul_self_eq_one_of_gauge_right [Finite r] {U U' : ℝ → Matrix m r ℝ}
    {a b : ℝ} (hUc : ContinuousOn U (Icc a b))
    (hU : ∀ t ∈ Ico a b, HasDerivWithinAt U (U' t) (Ici t) t)
    (hg : ∀ t ∈ Ico a b, (U t)ᵀ * U' t = 0) (ha : (U a)ᵀ * U a = 1) :
    ∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 := by
  have := Fintype.ofFinite r
  have hd : ∀ x ∈ Ico a b,
      HasDerivWithinAt (fun t => (U t)ᵀ * U t) (0 : Matrix r r ℝ) (Ici x) x := by
    intro x hx
    have h := hasDerivWithinAt_mul (hasDerivWithinAt_transpose (hU x hx)) (hU x hx)
    have e1 : (U' x)ᵀ * U x = ((U x)ᵀ * U' x)ᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [e1, hg x hx, Matrix.transpose_zero, add_zero] at h
    exact h
  have h := norm_image_sub_le_of_norm_deriv_right_le_segment (C := 0)
    (continuousOn_mul (continuousOn_transpose hUc) hUc) hd (fun x _ => by simp)
  intro t ht
  have h' := h t ht
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h'
  rw [h', ha]

/-- **The factor ODE `U̇ = (I - U Uᵀ) G(t)` preserves orthonormality**, with a uniform bound
(Koch–Lubich, proof of Prop. 2.1), without assuming the gauge a priori: if `U` solves it on
`[a, b]` (in the `ODESolution` sense), `‖U(t)ᵀ G(t)‖ ≤ C` on `[a, b)` and `U(a)ᵀ U(a) = 1`, then
`U(t)ᵀ U(t) = 1` on `[a, b]`.  Proof: `E = I - Uᵀ U` solves the linear ODE
`Ė = -(Hᵀ E + E H)` with `H = Uᵀ G`, `E(a) = 0`, so `E ≡ 0` by Grönwall.  See
`transpose_mul_self_eq_one_of_odeSolution` for the version with only local bounds. -/
theorem transpose_mul_self_eq_one_of_odeSolution_of_bound {U G : ℝ → Matrix m r ℝ} {a b C : ℝ}
    (hU : ODESolution (fun t X => (1 - X * Xᵀ) * G t) U a b)
    (hC : ∀ t ∈ Ico a b, ‖(U t)ᵀ * G t‖ ≤ C) (ha : (U a)ᵀ * U a = 1) :
    ∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 := by
  set E : ℝ → Matrix r r ℝ := fun t => 1 - (U t)ᵀ * U t with hE
  set H : ℝ → Matrix r r ℝ := fun t => (U t)ᵀ * G t with hH
  have key : ∀ x, (U x)ᵀ * ((1 - U x * (U x)ᵀ) * G x) = E x * H x := by
    intro x
    simp only [hE, hH, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  have hEsymm : ∀ x, (E x)ᵀ = E x := by
    intro x
    simp [hE, Matrix.transpose_sub, Matrix.transpose_mul]
  have hcont : ContinuousOn E (Icc a b) :=
    continuousOn_const.sub (continuousOn_mul (continuousOn_transpose hU.cont) hU.cont)
  have hderiv : ∀ x ∈ Ico a b, HasDerivWithinAt E (-((H x)ᵀ * E x + E x * H x)) (Ici x) x := by
    intro x hx
    have h := (hasDerivWithinAt_const x (Ici x) (1 : Matrix r r ℝ)).sub
      (hasDerivWithinAt_mul (hasDerivWithinAt_transpose (hU.deriv x hx)) (hU.deriv x hx))
    have e : (0 : Matrix r r ℝ) - (((1 - U x * (U x)ᵀ) * G x)ᵀ * U x
        + (U x)ᵀ * ((1 - U x * (U x)ᵀ) * G x)) = -((H x)ᵀ * E x + E x * H x) := by
      rw [key, ← Matrix.transpose_transpose (U x), ← Matrix.transpose_mul,
        Matrix.transpose_transpose, key, Matrix.transpose_mul, hEsymm, zero_sub]
    rw [e] at h
    exact h
  have hbound : ∀ x ∈ Ico a b, ‖-((H x)ᵀ * E x + E x * H x)‖ ≤ (2 * C) * ‖E x‖ := by
    intro x hx
    have h1 : ‖(H x)ᵀ * E x‖ ≤ ‖H x‖ * ‖E x‖ := by
      calc ‖(H x)ᵀ * E x‖ ≤ ‖(H x)ᵀ‖ * ‖E x‖ := Matrix.frobenius_norm_mul _ _
        _ = ‖H x‖ * ‖E x‖ := by rw [Matrix.frobenius_norm_transpose]
    have h2 : ‖E x * H x‖ ≤ ‖E x‖ * ‖H x‖ := Matrix.frobenius_norm_mul _ _
    have h3 : ‖H x‖ ≤ C := hC x hx
    have h4 : 0 ≤ ‖E x‖ := norm_nonneg _
    rw [norm_neg]
    calc ‖(H x)ᵀ * E x + E x * H x‖ ≤ ‖(H x)ᵀ * E x‖ + ‖E x * H x‖ := norm_add_le _ _
      _ ≤ (2 * C) * ‖E x‖ := by nlinarith
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hcont hderiv
    (by simp [hE, ha]) hbound
  intro t ht
  exact (sub_eq_zero.mp (hzero t ht)).symm

/-- **The factor ODE `U̇ = (I - U Uᵀ) G(t)` preserves orthonormality** (Koch–Lubich, proof of
Prop. 2.1), without assuming the gauge a priori: if `U` solves it on `[a, b]` (in the
`ODESolution` sense), `‖U(t)ᵀ G(t)‖` is bounded on every `[a, b')` with `b' < b`, and
`U(a)ᵀ U(a) = 1`, then `U(t)ᵀ U(t) = 1` on `[a, b]`.

Only *local* boundedness on `[a, b)` is assumed, so `Uᵀ G` may blow up as `t → b` (e.g. when the
core `S` of the factor system becomes singular at `b`): orthonormality on `[a, b)` follows from
`transpose_mul_self_eq_one_of_odeSolution_of_bound` on each `[a, b']`, and at `b` by continuity.
The local bound holds e.g. when `t ↦ U(t)ᵀ G(t)` is continuous on `[a, b)`.  Some condition of
this kind is needed for the Grönwall argument, since `G` is arbitrary (compare the scalar ODE
`ė = c(t) e`, which has nonzero solutions with `e(a) = 0` when `c` is unbounded near `a`).
Together with `transpose_mul_one_sub_eq_zero` (or `gauge_of_factorODE`) this gives the gauge
`Uᵀ U̇ = Uᵀ (I - U Uᵀ) G = 0` along the solution. -/
theorem transpose_mul_self_eq_one_of_odeSolution {U G : ℝ → Matrix m r ℝ} {a b : ℝ}
    (hU : ODESolution (fun t X => (1 - X * Xᵀ) * G t) U a b)
    (hC : ∀ b' < b, ∃ C, ∀ t ∈ Ico a b', ‖(U t)ᵀ * G t‖ ≤ C) (ha : (U a)ᵀ * U a = 1) :
    ∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 := by
  have hlt : EqOn (fun t => (U t)ᵀ * U t) (fun _ => 1) (Ico a b) := by
    intro t ht
    obtain ⟨C, hCt⟩ := hC t ht.2
    exact transpose_mul_self_eq_one_of_odeSolution_of_bound (hU.mono le_rfl ht.2.le) hCt ha t
      ⟨ht.1, le_rfl⟩
  intro t ht
  rcases ht.2.lt_or_eq with htb | htb
  · exact hlt ⟨ht.1, htb⟩
  rcases ht.1.eq_or_lt with hat | hat
  · rw [← hat]
    exact ha
  have hab : a < b := htb ▸ hat
  have hcont : ContinuousOn (fun t => (U t)ᵀ * U t) (Icc a b) :=
    continuousOn_mul (continuousOn_transpose hU.cont) hU.cont
  exact hlt.of_subset_closure hcont continuousOn_const Ico_subset_Icc_self
    (closure_Ico hab.ne).ge ht

/-! ### The factor system on an interval -/

/-- **Koch–Lubich, Prop. 2.1 on an interval (factor ODEs ⇒ DLRA)**.  Let `U, S, V` solve the
gauge-fixed factor system
`U̇ = (I - U Uᵀ) Ȧ V S⁻¹`, `Ṡ = Uᵀ Ȧ V`, `V̇ = (I - V Vᵀ) Ȧᵀ U S⁻ᵀ` on `[a, b]` (in the
`ODESolution` sense: continuity on `[a, b]`, right derivatives on `[a, b)`), with `S(t)` invertible
on `[a, b)` and orthonormal initial factors `U(a)ᵀ U(a) = 1`, `V(a)ᵀ V(a) = 1`.  Then the factors
stay orthonormal on `[a, b]` and `Y = U S Vᵀ` solves `Ẏ = P(Y) Ȧ` on `[a, b]`.  (The gauge
conditions then hold along the solution by `gauge_of_factorODE`.)

The conclusion is an `ODESolution` whose right-hand side ignores the state argument: it is the
time-dependent matrix `P(Y(t)) Ȧ(t)` with `P(Y(t))` written through the factors `U(t)`, `V(t)`,
not a vector field `Y ↦ P(Y) F(t, Y)` in the state.  Since `P(Y)` depends only on `Y`
(`tangentProj_eq_of_factorization`), this is the DLRA equation along the trajectory; see
`factorODE_solution_isDLRA_tangentProj` for the statement with the orthogonal projector
`tangentProj`.

The local bounds `hCU`, `hCV` on `‖Uᵀ Ȧ V S⁻¹‖`, `‖Vᵀ Ȧᵀ U S⁻ᵀ‖` (one bound on each `[a, b')`
with `b' < b`) are used in the Grönwall argument for orthonormality.  They hold whenever these
quantities are continuous on `[a, b)`; in particular `S(t)⁻¹` may blow up as `t → b`
(see `transpose_mul_self_eq_one_of_odeSolution`). -/
theorem factorODE_solution_isDLRA {U : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ}
    {V : ℝ → Matrix n r ℝ} {Ad : ℝ → Matrix m n ℝ} {a b : ℝ}
    (hU : ODESolution (fun t X => (1 - X * Xᵀ) * Ad t * V t * (S t)⁻¹) U a b)
    (hS : ODESolution (fun t _ => (U t)ᵀ * Ad t * V t) S a b)
    (hV : ODESolution (fun t X => (1 - X * Xᵀ) * (Ad t)ᵀ * U t * ((S t)⁻¹)ᵀ) V a b)
    (hdet : ∀ t ∈ Ico a b, IsUnit (S t).det)
    (hCU : ∀ b' < b, ∃ C, ∀ t ∈ Ico a b', ‖(U t)ᵀ * (Ad t * V t * (S t)⁻¹)‖ ≤ C)
    (hCV : ∀ b' < b, ∃ C, ∀ t ∈ Ico a b', ‖(V t)ᵀ * ((Ad t)ᵀ * U t * ((S t)⁻¹)ᵀ)‖ ≤ C)
    (hUa : (U a)ᵀ * U a = 1) (hVa : (V a)ᵀ * V a = 1) :
    (∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1) ∧
      ODESolution (fun t _ => U t * (U t)ᵀ * Ad t + Ad t * V t * (V t)ᵀ
        - U t * (U t)ᵀ * Ad t * V t * (V t)ᵀ) (fun t => U t * S t * (V t)ᵀ) a b := by
  have hU' : ODESolution (fun t X => (1 - X * Xᵀ) * (Ad t * V t * (S t)⁻¹)) U a b :=
    ⟨hU.cont, fun t ht => by simpa only [Matrix.mul_assoc] using hU.deriv t ht⟩
  have hV' : ODESolution (fun t X => (1 - X * Xᵀ) * ((Ad t)ᵀ * U t * ((S t)⁻¹)ᵀ)) V a b :=
    ⟨hV.cont, fun t ht => by simpa only [Matrix.mul_assoc] using hV.deriv t ht⟩
  refine ⟨fun t ht => ⟨transpose_mul_self_eq_one_of_odeSolution hU' hCU hUa t ht,
    transpose_mul_self_eq_one_of_odeSolution hV' hCV hVa t ht⟩, ?_, ?_⟩
  · exact continuousOn_mul (continuousOn_mul hU.cont hS.cont) (continuousOn_transpose hV.cont)
  · intro t ht
    exact hasDerivWithinAt_factorProduct_of_factorODE (hdet t ht) (hU.deriv t ht)
      (hS.deriv t ht) (hV.deriv t ht)

/-- **Koch–Lubich, Prop. 2.1 on an interval (DLRA ⇒ factor ODEs), for a given gauge-fixed
factorization**.  Let `Y = U S Vᵀ` solve `Ẏ = P(Y) Ȧ` on `[a, b]` in the sense of the conclusion
of `factorODE_solution_isDLRA`, where the factors are continuous on `[a, b]` with right
derivatives `U̇, Ṡ, V̇` on `[a, b)` satisfying the gauge conditions `Uᵀ U̇ = 0`, `Vᵀ V̇ = 0`,
the initial factors are orthonormal and `S(t)` is invertible on `[a, b)`.  Then the factors stay
orthonormal on `[a, b]` and solve the factor system
`U̇ = (I - U Uᵀ) Ȧ V S⁻¹`, `Ṡ = Uᵀ Ȧ V`, `V̇ = (I - V Vᵀ) Ȧᵀ U S⁻ᵀ` on `[a, b]`.

Scope: the existence and uniqueness of such a factorization of a given DLRA solution (the
"admits a unique decomposition" part of the cited statement) is assumed here, not proved; see the
module docstring. -/
theorem factorODE_of_isDLRA {U U' : ℝ → Matrix m r ℝ} {S S' : ℝ → Matrix r r ℝ}
    {V V' : ℝ → Matrix n r ℝ} {Ad : ℝ → Matrix m n ℝ} {a b : ℝ}
    (hUc : ContinuousOn U (Icc a b)) (hSc : ContinuousOn S (Icc a b))
    (hVc : ContinuousOn V (Icc a b))
    (hU : ∀ t ∈ Ico a b, HasDerivWithinAt U (U' t) (Ici t) t)
    (hS : ∀ t ∈ Ico a b, HasDerivWithinAt S (S' t) (Ici t) t)
    (hV : ∀ t ∈ Ico a b, HasDerivWithinAt V (V' t) (Ici t) t)
    (hgU : ∀ t ∈ Ico a b, (U t)ᵀ * U' t = 0) (hgV : ∀ t ∈ Ico a b, (V t)ᵀ * V' t = 0)
    (hUa : (U a)ᵀ * U a = 1) (hVa : (V a)ᵀ * V a = 1)
    (hdet : ∀ t ∈ Ico a b, IsUnit (S t).det)
    (hY : ODESolution (fun t _ => U t * (U t)ᵀ * Ad t + Ad t * V t * (V t)ᵀ
        - U t * (U t)ᵀ * Ad t * V t * (V t)ᵀ) (fun t => U t * S t * (V t)ᵀ) a b) :
    (∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1) ∧
      ODESolution (fun t X => (1 - X * Xᵀ) * Ad t * V t * (S t)⁻¹) U a b ∧
      ODESolution (fun t _ => (U t)ᵀ * Ad t * V t) S a b ∧
      ODESolution (fun t X => (1 - X * Xᵀ) * (Ad t)ᵀ * U t * ((S t)⁻¹)ᵀ) V a b := by
  have hUo := transpose_mul_self_eq_one_of_gauge_right hUc hU hgU hUa
  have hVo := transpose_mul_self_eq_one_of_gauge_right hVc hV hgV hVa
  have key : ∀ t ∈ Ico a b, U' t = (1 - U t * (U t)ᵀ) * Ad t * V t * (S t)⁻¹ ∧
      S' t = (U t)ᵀ * Ad t * V t ∧ V' t = (1 - V t * (V t)ᵀ) * (Ad t)ᵀ * U t * ((S t)⁻¹)ᵀ :=
    fun t ht => (hasDerivWithinAt_factorProduct_iff_factorODE (uniqueDiffWithinAt_Ici t)
      (hU t ht) (hS t ht) (hV t ht) (hUo t (Ico_subset_Icc_self ht))
      (hVo t (Ico_subset_Icc_self ht)) (hdet t ht) (hgU t ht) (hgV t ht)).1 (hY.deriv t ht)
  refine ⟨fun t ht => ⟨hUo t ht, hVo t ht⟩, ⟨hUc, fun t ht => ?_⟩, ⟨hSc, fun t ht => ?_⟩,
    ⟨hVc, fun t ht => ?_⟩⟩
  · have h := hU t ht
    rwa [(key t ht).1] at h
  · have h := hS t ht
    rwa [(key t ht).2.1] at h
  · have h := hV t ht
    rwa [(key t ht).2.2] at h

/-! ### Restatement with the orthogonal tangent-space projector `tangentProj` -/

section TangentProj

open scoped LeanDLRA.Frobenius

omit [DecidableEq m] [DecidableEq n] in
/-- If `U S Vᵀ = U₁ S₁ V₁ᵀ` with `Vᵀ V = 1`, `S` invertible and `U₁ᵀ U₁ = 1`, then the columns of
`U` lie in the range of `U₁`: `U₁ U₁ᵀ U = U`. -/
theorem mul_transpose_mul_eq_of_factorization {r' : Type*} [Fintype r'] [DecidableEq r']
    {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ} {U₁ : Matrix m r' ℝ}
    {S₁ : Matrix r' r' ℝ} {V₁ : Matrix n r' ℝ} (hV : Vᵀ * V = 1) (hS : IsUnit S.det)
    (hU₁ : U₁ᵀ * U₁ = 1) (h : U * S * Vᵀ = U₁ * S₁ * V₁ᵀ) : U₁ * U₁ᵀ * U = U := by
  have hU : U = U₁ * S₁ * V₁ᵀ * V * S⁻¹ := by
    rw [← h, Matrix.mul_assoc (U * S) Vᵀ V, hV, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_right _ _ hS]
  calc U₁ * U₁ᵀ * U = U₁ * U₁ᵀ * (U₁ * S₁ * V₁ᵀ * V * S⁻¹) := by rw [← hU]
    _ = U₁ * S₁ * V₁ᵀ * V * S⁻¹ := by
      simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_assoc U₁ U₁ᵀ U₁, hU₁, Matrix.mul_one]
    _ = U := hU.symm

omit [DecidableEq m] [DecidableEq r] in
/-- If the columns of `U` lie in the range of `U₁` and vice versa (`U₁ U₁ᵀ U = U`,
`U Uᵀ U₁ = U₁`), then `U Uᵀ = U₁ U₁ᵀ`. -/
theorem mul_transpose_eq_of_mul_transpose_mul_eq {r' : Type*} [Fintype r'] {U : Matrix m r ℝ}
    {U₁ : Matrix m r' ℝ} (h₁ : U₁ * U₁ᵀ * U = U) (h₂ : U * Uᵀ * U₁ = U₁) :
    U * Uᵀ = U₁ * U₁ᵀ := by
  calc U * Uᵀ = (U₁ * U₁ᵀ * U * Uᵀ)ᵀ := by
        rw [h₁, Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = U * Uᵀ * U₁ * U₁ᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = U₁ * U₁ᵀ := by rw [h₂]

omit [DecidableEq m] [DecidableEq n] in
/-- **The projectors `U Uᵀ`, `V Vᵀ` depend only on `Y = U S Vᵀ`.**  If `Y = U S Vᵀ = U₁ S₁ V₁ᵀ`
are two factorizations with orthonormal columns and invertible cores, then `U Uᵀ = U₁ U₁ᵀ` and
`V Vᵀ = V₁ V₁ᵀ` (the orthogonal projectors onto the column and row space of `Y`). -/
theorem mul_transpose_eq_of_factorization {r' : Type*} [Fintype r'] [DecidableEq r']
    {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ} {U₁ : Matrix m r' ℝ}
    {S₁ : Matrix r' r' ℝ} {V₁ : Matrix n r' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hS : IsUnit S.det) (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1) (hS₁ : IsUnit S₁.det)
    (h : U * S * Vᵀ = U₁ * S₁ * V₁ᵀ) : U * Uᵀ = U₁ * U₁ᵀ ∧ V * Vᵀ = V₁ * V₁ᵀ := by
  have hT : V * Sᵀ * Uᵀ = V₁ * S₁ᵀ * U₁ᵀ := by
    have := congrArg Matrix.transpose h
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using this
  have hST : IsUnit Sᵀ.det := by rwa [Matrix.det_transpose]
  have hS₁T : IsUnit S₁ᵀ.det := by rwa [Matrix.det_transpose]
  exact ⟨mul_transpose_eq_of_mul_transpose_mul_eq
      (mul_transpose_mul_eq_of_factorization hV hS hU₁ h)
      (mul_transpose_mul_eq_of_factorization hV₁ hS₁ hU h.symm),
    mul_transpose_eq_of_mul_transpose_mul_eq
      (mul_transpose_mul_eq_of_factorization hU hST hV₁ hT)
      (mul_transpose_mul_eq_of_factorization hU₁ hS₁T hV hT.symm)⟩

omit [DecidableEq m] [DecidableEq n] in
/-- **The tangent-space projector `P(Y)` depends only on `Y`**: for two factorizations
`Y = U S Vᵀ = U₁ S₁ V₁ᵀ` with orthonormal columns and invertible cores,
`tangentProj U V = tangentProj U₁ V₁`.  So `P(Y)` is well defined on the rank-`r` manifold, and
the factor-expressed right-hand sides in this file are the DLRA field `P(Y) Ȧ` evaluated at
`Y = U S Vᵀ`. -/
theorem tangentProj_eq_of_factorization {r' : Type*} [Fintype r'] [DecidableEq r']
    {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ} {U₁ : Matrix m r' ℝ}
    {S₁ : Matrix r' r' ℝ} {V₁ : Matrix n r' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hS : IsUnit S.det) (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1) (hS₁ : IsUnit S₁.det)
    (h : U * S * Vᵀ = U₁ * S₁ * V₁ᵀ) : tangentProj U V = tangentProj U₁ V₁ := by
  obtain ⟨hUU, hVV⟩ := mul_transpose_eq_of_factorization hU hV hS hU₁ hV₁ hS₁ h
  unfold tangentProj leftProj rightProj
  rw [hUU, hVV]

/-- **Koch–Lubich, Prop. 2.1 (pointwise equivalence)**, stated with the orthogonal tangent-space
projector `tangentProj` (`isOrthProj_tangentProj`, `mem_range_tangentProj`) instead of its
explicit formula: under orthonormality, invertibility of `S` and the gauge conditions at `t`,
`Ẏ = P(Y) Ȧ` at `t` iff the factor ODEs hold at `t`.  The gauge-fixed factorization is a
hypothesis (see the module docstring). -/
theorem hasDerivAt_factorProduct_tangentProj_iff_factorODE {U : ℝ → Matrix m r ℝ}
    {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix n r ℝ} {U' : Matrix m r ℝ} {S' : Matrix r r ℝ}
    {V' : Matrix n r ℝ} {Ad : Matrix m n ℝ} {t : ℝ}
    (hU : HasDerivAt U U' t) (hS : HasDerivAt S S' t)
    (hV : HasDerivAt V V' t) (hUo : (U t)ᵀ * U t = 1) (hVo : (V t)ᵀ * V t = 1)
    (hdet : IsUnit (S t).det) (hgU : (U t)ᵀ * U' = 0) (hgV : (V t)ᵀ * V' = 0) :
    HasDerivAt (fun t => U t * S t * (V t)ᵀ) (tangentProj (U t) (V t) Ad) t ↔
      U' = (1 - U t * (U t)ᵀ) * Ad * V t * (S t)⁻¹ ∧ S' = (U t)ᵀ * Ad * V t ∧
        V' = (1 - V t * (V t)ᵀ) * Adᵀ * U t * ((S t)⁻¹)ᵀ := by
  rw [tangentProj_apply]
  exact hasDerivAt_factorProduct_iff_factorODE hU hS hV hUo hVo hdet hgU hgV

/-- **Koch–Lubich, Prop. 2.1 on an interval (factor ODEs ⇒ DLRA)**, stated with the orthogonal
tangent-space projector: under the hypotheses of `factorODE_solution_isDLRA`, for all
`t ∈ [a, b]` the factors are orthonormal and `tangentProj (U t) (V t)` is an orthogonal projector,
and `Y = U S Vᵀ` solves `Ẏ = P(Y(t)) Ȧ(t)` with `P(Y(t)) = tangentProj (U t) (V t)` on `[a, b]`
(a time-dependent right-hand side, see `factorODE_solution_isDLRA`). -/
theorem factorODE_solution_isDLRA_tangentProj {U : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ}
    {V : ℝ → Matrix n r ℝ} {Ad : ℝ → Matrix m n ℝ} {a b : ℝ}
    (hU : ODESolution (fun t X => (1 - X * Xᵀ) * Ad t * V t * (S t)⁻¹) U a b)
    (hS : ODESolution (fun t _ => (U t)ᵀ * Ad t * V t) S a b)
    (hV : ODESolution (fun t X => (1 - X * Xᵀ) * (Ad t)ᵀ * U t * ((S t)⁻¹)ᵀ) V a b)
    (hdet : ∀ t ∈ Ico a b, IsUnit (S t).det)
    (hCU : ∀ b' < b, ∃ C, ∀ t ∈ Ico a b', ‖(U t)ᵀ * (Ad t * V t * (S t)⁻¹)‖ ≤ C)
    (hCV : ∀ b' < b, ∃ C, ∀ t ∈ Ico a b', ‖(V t)ᵀ * ((Ad t)ᵀ * U t * ((S t)⁻¹)ᵀ)‖ ≤ C)
    (hUa : (U a)ᵀ * U a = 1) (hVa : (V a)ᵀ * V a = 1) :
    (∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧
        IsOrthProj (tangentProj (U t) (V t) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ)) ∧
      ODESolution (fun t _ => tangentProj (U t) (V t) (Ad t)) (fun t => U t * S t * (V t)ᵀ)
        a b := by
  obtain ⟨ho, hY⟩ := factorODE_solution_isDLRA hU hS hV hdet hCU hCV hUa hVa
  refine ⟨fun t ht => ⟨(ho t ht).1, (ho t ht).2,
    isOrthProj_tangentProj (ho t ht).1 (ho t ht).2⟩, ?_⟩
  simpa only [tangentProj_apply] using hY

end TangentProj

/-! ### A nondegenerate example

`m = n = 2`, `r = 1`, `U(t) = (cos t, sin t)ᵀ`, `V = e₁`, `S(t) = eᵗ`, and `A(t) = eᵗ U(t) e₁ᵀ`
(so `Y = A`).  Here the factor `U` moves, `Uᵀ Ȧ V S⁻¹ = 1 ≠ 0`, the term `(I - U Uᵀ) Ȧ V S⁻¹`
is nonzero, and `P(Y)` is not the identity (it maps `e₂ e₂ᵀ` to `0` at `t = 0`). -/

namespace GaugeODEExample

noncomputable section

/-- The first standard basis vector of `ℝ²`, as a `2 × 1` matrix. -/
def u₁ : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of ![![1], ![0]]

/-- The second standard basis vector of `ℝ²`, as a `2 × 1` matrix. -/
def u₂ : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of ![![0], ![1]]

/-- The rotating left factor `U(t) = (cos t, sin t)ᵀ`. -/
def Uf (t : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := Real.cos t • u₁ + Real.sin t • u₂

/-- The derivative `U̇(t) = (-sin t, cos t)ᵀ`. -/
def Ud (t : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := (-Real.sin t) • u₁ + Real.cos t • u₂

/-- The constant right factor `V = e₁`. -/
def V0 : Matrix (Fin 2) (Fin 1) ℝ := u₁

/-- The core `S(t) = eᵗ`. -/
def Sf (t : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := Real.exp t • 1

/-- `Ȧ(t)` for `A(t) = eᵗ U(t) V0ᵀ`, of rank one in `ℝ^{2 × 2}`. -/
def Adf (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Real.exp t • ((Uf t + Ud t) * V0ᵀ)

/-- The matrix `e₂ e₂ᵀ`. -/
def E₂₂ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![![0, 0], ![0, 1]]

lemma Sf_inv (t : ℝ) : (Sf t)⁻¹ = (Real.exp t)⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  apply Matrix.inv_eq_left_inv
  rw [Sf, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
    inv_mul_cancel₀ (Real.exp_pos t).ne', one_smul]

lemma isUnit_det_Sf (t : ℝ) : IsUnit (Sf t).det := by
  rw [Sf, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, pow_one, mul_one]
  exact isUnit_iff_ne_zero.mpr (Real.exp_pos t).ne'

lemma hasDerivAt_Uf (t : ℝ) : HasDerivAt Uf (Ud t) t :=
  ((Real.hasDerivAt_cos t).smul_const u₁).add ((Real.hasDerivAt_sin t).smul_const u₂)

lemma hasDerivAt_Sf (t : ℝ) : HasDerivAt Sf (Real.exp t • 1) t :=
  (Real.hasDerivAt_exp t).smul_const _

lemma factorU_eq (t : ℝ) : (1 - Uf t * (Uf t)ᵀ) * Adf t * V0 * (Sf t)⁻¹ = Ud t := by
  rw [Sf_inv]
  have e := Real.exp_pos t
  have hs := Real.sin_sq_add_cos_sq t
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Uf, Ud, Adf, V0, u₁, u₂, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
      Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply, Matrix.vecHead, Pi.smul_apply,
      smul_eq_mul, Matrix.sub_apply] <;>
    field_simp <;> ring_nf <;>
    first
    | linear_combination (-Real.cos t) * hs
    | linear_combination (-Real.sin t) * hs

lemma factorS_eq (t : ℝ) : (Uf t)ᵀ * Adf t * V0 = Real.exp t • 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [Uf, Ud, Adf, V0, u₁, u₂, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
    Matrix.transpose_apply, Matrix.of_apply]
  linear_combination (Real.exp t) * Real.sin_sq_add_cos_sq t

lemma factorV_eq (t : ℝ) : (1 - V0 * V0ᵀ) * (Adf t)ᵀ * Uf t * ((Sf t)⁻¹)ᵀ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Uf, Ud, Adf, V0, u₁, u₂, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
      Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]

lemma boundU_eq (t : ℝ) : (Uf t)ᵀ * (Adf t * V0 * (Sf t)⁻¹) = 1 := by
  rw [Sf_inv]
  have e := (Real.exp_pos t).ne'
  ext i j
  fin_cases i; fin_cases j
  simp [Uf, Ud, Adf, V0, u₁, u₂, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
    Matrix.transpose_apply, Matrix.of_apply, Matrix.vecHead, Matrix.smul_vecMul, smul_eq_mul]
  field_simp
  linear_combination Real.sin_sq_add_cos_sq t

lemma boundV_eq (t : ℝ) : V0ᵀ * ((Adf t)ᵀ * Uf t * ((Sf t)⁻¹)ᵀ) = 1 := by
  rw [Sf_inv]
  have e := (Real.exp_pos t).ne'
  ext i j
  fin_cases i; fin_cases j
  simp [Uf, Ud, Adf, V0, u₁, u₂, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
    Matrix.transpose_apply, Matrix.of_apply, Matrix.vecHead, Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination Real.sin_sq_add_cos_sq t

lemma gauge_Uf (t : ℝ) : (Uf t)ᵀ * Ud t = 0 := by
  ext i j
  fin_cases i; fin_cases j
  simp [Uf, Ud, u₁, u₂, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    Matrix.of_apply]
  ring

lemma orthonormal_Uf (t : ℝ) : (Uf t)ᵀ * Uf t = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [Uf, u₁, u₂, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.of_apply]
  linear_combination Real.cos_sq_add_sin_sq t

lemma orthonormal_V0 : V0ᵀ * V0 = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [V0, u₁, Matrix.mul_apply, Fin.sum_univ_two]

/-- The projector formula at `Y(0)` kills `e₂ e₂ᵀ`. -/
lemma proj_E₂₂ :
    Uf 0 * (Uf 0)ᵀ * E₂₂ + E₂₂ * V0 * V0ᵀ - Uf 0 * (Uf 0)ᵀ * E₂₂ * V0 * V0ᵀ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Uf, V0, E₂₂, u₁, u₂, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
      Matrix.transpose_apply, Matrix.of_apply]

/-- `e₂ e₂ᵀ ≠ 0`. -/
lemma E₂₂_ne : (0 : Matrix (Fin 2) (Fin 2) ℝ) ≠ E₂₂ := by
  intro h
  have := congrArg (fun M => M 1 1) h
  simp [E₂₂] at this

/-- The rotating `U`, the core `S = eᵗ` and the constant `V = e₁` solve the factor system of
Koch–Lubich Prop. 2.1 for `Ȧ = Adf` on `[0, 1]`, and `factorODE_solution_isDLRA` applies. -/
theorem isDLRA :
    (∀ t ∈ Icc (0 : ℝ) 1, (Uf t)ᵀ * Uf t = 1 ∧ V0ᵀ * V0 = 1) ∧
      ODESolution (fun t _ => Uf t * (Uf t)ᵀ * Adf t + Adf t * V0 * V0ᵀ
        - Uf t * (Uf t)ᵀ * Adf t * V0 * V0ᵀ) (fun t => Uf t * Sf t * V0ᵀ) 0 1 := by
  have hU : ODESolution (fun t X => (1 - X * Xᵀ) * Adf t * V0 * (Sf t)⁻¹) Uf 0 1 :=
    ⟨fun t _ => (hasDerivAt_Uf t).continuousAt.continuousWithinAt,
     fun t _ => by rw [factorU_eq]; exact (hasDerivAt_Uf t).hasDerivWithinAt⟩
  have hS : ODESolution (fun t _ => (Uf t)ᵀ * Adf t * V0) Sf 0 1 :=
    ⟨fun t _ => (hasDerivAt_Sf t).continuousAt.continuousWithinAt,
     fun t _ => by rw [factorS_eq]; exact (hasDerivAt_Sf t).hasDerivWithinAt⟩
  have hV : ODESolution (fun t X => (1 - X * Xᵀ) * (Adf t)ᵀ * Uf t * ((Sf t)⁻¹)ᵀ)
      (fun _ => V0) 0 1 :=
    ⟨continuousOn_const, fun t _ => by
      have h := hasDerivWithinAt_const t (Ici t) V0
      rwa [← factorV_eq t] at h⟩
  exact factorODE_solution_isDLRA hU hS hV (fun t _ => isUnit_det_Sf t)
    (fun _ _ => ⟨‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖, fun t _ => by rw [boundU_eq]⟩)
    (fun _ _ => ⟨‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖, fun t _ => by rw [boundV_eq]⟩)
    (orthonormal_Uf 0) orthonormal_V0

/-- The hypotheses of the converse `factorODE_of_isDLRA` are jointly satisfiable with moving
factors: the gauge-fixed factorization `Uf, Sf, V0` of the DLRA solution of `isDLRA`. -/
example : ODESolution (fun t X => (1 - X * Xᵀ) * Adf t * V0 * (Sf t)⁻¹) Uf 0 1 :=
  (factorODE_of_isDLRA (U' := Ud) (S' := fun t => Real.exp t • 1) (V' := fun _ => 0)
    (fun t _ => (hasDerivAt_Uf t).continuousAt.continuousWithinAt)
    (fun t _ => (hasDerivAt_Sf t).continuousAt.continuousWithinAt) continuousOn_const
    (fun t _ => (hasDerivAt_Uf t).hasDerivWithinAt)
    (fun t _ => (hasDerivAt_Sf t).hasDerivWithinAt)
    (fun t _ => hasDerivWithinAt_const t (Ici t) V0)
    (fun t _ => gauge_Uf t) (fun _ _ => Matrix.mul_zero _) (orthonormal_Uf 0) orthonormal_V0
    (fun t _ => isUnit_det_Sf t) isDLRA.2).2.1

open scoped LeanDLRA.Frobenius in
/-- In this example `P(Y)` is not the identity: `tangentProj (U 0) V` maps `e₂ e₂ᵀ` to `0`. -/
example : tangentProj (Uf 0) V0 E₂₂ = 0 ∧ tangentProj (Uf 0) V0 E₂₂ ≠ E₂₂ := by
  have h : tangentProj (Uf 0) V0 E₂₂ = 0 := by
    rw [tangentProj_apply]
    exact proj_E₂₂
  exact ⟨h, h ▸ E₂₂_ne⟩

open scoped LeanDLRA.Frobenius in
/-- The tangent-projector form `factorODE_solution_isDLRA_tangentProj` applies to the example. -/
example : ODESolution (fun t _ => tangentProj (Uf t) V0 (Adf t)) (fun t => Uf t * Sf t * V0ᵀ)
    0 1 := by
  simpa only [tangentProj_apply] using isDLRA.2

end

end GaugeODEExample

end LeanDLRA
