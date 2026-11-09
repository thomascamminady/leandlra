import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Foundations.ODE
import LeanDLRA.LinearAlgebra.Factorization.Defs
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Novel.BlindSpotII

/-!
# Randomized DLRA without the small-normal-component assumption (OP-RS-34)

Open problem OP-RS-34 of `docs/survey/open-problems.json`: arXiv 2410.17091
(Sec. 4.1) asserts that the randomized integrators DRSVD/DGN do not need the small-normal-component
assumption `‖(I - P(Y)) F(Y)‖ ≤ ε` of DLRA error analysis, and asks for an error analysis under a
weaker hypothesis such as low-rank approximability of the exact flow,
`‖Φ^h(Y) - 𝒯_r(Φ^h(Y))‖ ≤ C h ε`.  Everything here is on actual matrices.

## Negative answer for the practical method (Section `Counterexample`)

The **practical** dynamical rangefinder (B-step `Ḃ = F(B Ω†) Ω`, `B(0) = Y₀ Ω`, eq. (7) of
the paper) is not consistent, so no error bound of the form `C (ε + h)` exists for the practical
DRSVD under any hypothesis on `ε` alone.  The instance:

* `F(A) = (e_{i₂} + A_{i₁ j₁} e_{i₃}) (e_{i₁}ᵀ A)` on `m × n` matrices (`field`), a polynomial
  field; `A(0) = e_{i₁} e_{j₁}ᵀ`.
* The exact solution is `A(t) = (e_{i₁} + t (e_{i₂} + e_{i₃})) e_{j₁}ᵀ` (`exactSol_unique`,
  `exactSol_hasDerivAt`): rank one for all `t` (`rank_exactSol_le`), so the flow is rank-one
  approximable with `ε = 0`, and `F(A(t))` is tangent to the rank-one manifold
  (`normal_field_exactSol`), so also the small-normal-component assumption holds with `ε = 0`.
* For every sketch `Ω` with independent columns the B-step solution is
  `B(t) = (e_{i₁} + t (e_{i₂} + c e_{i₃})) (e_{j₁}ᵀ Ω)` with `c = (Ω Ω†)_{j₁ j₁} = ‖Π_Ω e_{j₁}‖²
  ∈ [0, 1]` (`bSol_unique`, `capture_mem_Icc`): the B-step evaluates `F` at `B Ω† = A Π_Ω`,
  whose `(i₁, j₁)` entry is `c` instead of `1` (`bField_of_row`).
* Hence every output `Y₁ = Q M` of the step (`Q = orth[U₀, orth(B(h))]`, any C-step, any
  truncation) satisfies `‖Y₁ - A(h)‖_F ≥ h (1 - c) / √(1 + c²)` (`drsvd_error_ge`,
  `drsvd_truncation_error_ge`): a first-order local error with a constant independent of `ε = 0`.
* In expectation over a one-column isotropic sketch (`p = 0`; the standard Gaussian in
  particular), `E ‖Y₁ - A(h)‖ ≥ h (1 - 1/n) / √2` (`lintegral_error_ge`,
  `lintegral_gaussian_error_ge`), using `E[c] = 1/n` from `BlindSpotII.IsIsotropicLaw`.

This is the DRSVD of Algorithm 3 with `q = 0` power iterations (used in Table 1 and in the
adaptive Algorithm 2 of the paper).  One power iteration repairs this particular instance, since
the corange of this problem is `e_{j₁}` and the second B-step is then an exact K-step; a
counterexample with `q ≥ 1` is not given.  For fields `F(A) = L A + A R + G` a first-order
computation (not formalized) shows the B-step perturbation lies in `range Y₀`, so the mechanism is
absent for the paper's Lyapunov test.  A throwaway multi-step computation on this instance gives a
global error of order one for every step size, as the local bound predicts.

## Positive answer for the idealized rangefinder (Section `Capture`)

If the sketch of the exact flow is captured, `range(A Ω + E) ⊆ range Q` with `E` the B-step
error, then for any `r` orthonormal columns `V₁` with remainder `A₂ = A (I - V₁ V₁ᵀ)` and any
right inverse `X` of `V₁ᵀ Ω`:

* `‖(I - Q Qᵀ) A‖² ≤ ‖A₂‖² + ‖(E + A₂ Ω) X‖²` (`norm_one_sub_proj_mul_sq_le`; with `E = 0` this
  is the deterministic bound of Halko–Martinsson–Tropp, Thm. 9.1, in the Frobenius norm);
* `‖A - 𝒯_r(Q Qᵀ A)‖² ≤ 2 ‖A₂‖² + ‖(E + A₂ Ω) X‖²` (`norm_sub_truncation_proj_sq_le`,
  `norm_sub_truncation_proj_sq_le_svd` with `A₂ = A - 𝒯_r A`).

For `A = Φ^h(Y₀)` the second bound is the wanted capture lemma: the local error of the idealized
DRSVD is controlled by the rank-`r` approximability of the exact flow times the sketch constant
`(2 + ‖Ω₂ Ω₁†‖₂²)^{1/2}`, plus `‖E‖ ‖Ω₁†‖₂`, with no tangent/normal splitting.  Its Gaussian
expectation (HMT: `E ‖Ω₂ Ω₁†‖_F² = r/(p - 1) · …`), the propagation to a global bound, and the error
`E` of the practical B-step are not treated; the counterexample shows that `E` is in general of
order `h` and not of order `h ε`.

The sketch pseudo-inverse `Ω† = (ΩᵀΩ)⁻¹ Ωᵀ` is the core Gram pseudoinverse `Matrix.gramPinv`
(`LinearAlgebra/Factorization/Defs.lean`), the Moore–Penrose inverse for sketches with independent
columns (`Matrix.gramPinv_eq_pinv`); the local `pinvT` of an earlier version of this file was the
same definition (unification batch C1).

Relation to prior work: arXiv 2410.17091 (DRSVD/DGN, Lemma 2.1, 3.1, 3.2), arXiv 2409.06384
(flow approximability, Assumption 3), Halko–Martinsson–Tropp 2011 (Thm. 9.1).
-/

open Set Filter Topology Finset MeasureTheory
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius ENNReal

namespace LeanDLRA.Novel.OpRS34

open LeanDLRA Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

section Counterexample

variable {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ] [DecidableEq m] [DecidableEq n]
  [DecidableEq κ]

variable (i₁ i₂ i₃ : m) (j₁ : n)

/-- The vector field `F(A) = (e_{i₂} + A_{i₁ j₁} e_{i₃}) (e_{i₁}ᵀ A)`: a polynomial field whose
value is a rank-one matrix with the `i₁`-th row of `A` as row. -/
noncomputable def field (A : Matrix m n ℝ) : Matrix m n ℝ :=
  vecMulVec (Pi.single i₂ 1 + A i₁ j₁ • Pi.single i₃ 1) (A i₁)

/-- The exact solution `A(t) = (e_{i₁} + t (e_{i₂} + e_{i₃})) e_{j₁}ᵀ` of `Ȧ = F(A)`,
`A(0) = e_{i₁} e_{j₁}ᵀ`. -/
noncomputable def exactSol (t : ℝ) : Matrix m n ℝ :=
  vecMulVec (Pi.single i₁ 1 + t • (Pi.single i₂ 1 + Pi.single i₃ 1)) (Pi.single j₁ 1)

/-- The **capture** `c = (Ω Ω†)_{j₁ j₁} = ‖Π_Ω e_{j₁}‖²` of the coordinate `e_{j₁}` by the
sketch. -/
noncomputable def capture (Ω : Matrix n κ ℝ) : ℝ := (Ω * Ω.gramPinv) j₁ j₁

/-- The vector field of the practical B-step `Ḃ = F(B Ω†) Ω` (arXiv 2410.17091, eq. (7)). -/
noncomputable def bField (Ω : Matrix n κ ℝ) (b : Matrix m κ ℝ) : Matrix m κ ℝ :=
  field i₁ i₂ i₃ j₁ (b * Ω.gramPinv) * Ω

/-- The solution of the practical B-step from `B(0) = A(0) Ω`:
`B(t) = (e_{i₁} + t (e_{i₂} + c e_{i₃})) (e_{j₁}ᵀ Ω)`. -/
noncomputable def bSol (Ω : Matrix n κ ℝ) (t : ℝ) : Matrix m κ ℝ :=
  vecMulVec (Pi.single i₁ 1 + t • (Pi.single i₂ 1 + capture j₁ Ω • Pi.single i₃ 1)) (Ω j₁)

/-- The row basis `V = e_{j₁}` of the exact solution, as an `n × 1` matrix. -/
noncomputable def rowBasis : Matrix n Unit ℝ := replicateCol Unit (Pi.single j₁ 1)

variable {i₁ i₂ i₃ j₁}

omit [DecidableEq n] in
/-- The row projector `E = e_{i₁} e_{i₁}ᵀ` kills the field. -/
private theorem rowProj_mul_field (h₂ : i₁ ≠ i₂) (h₃ : i₁ ≠ i₃) (A : Matrix m n ℝ) :
    vecMulVec (Pi.single i₁ (1 : ℝ)) (Pi.single i₁ 1) * field i₁ i₂ i₃ j₁ A = 0 := by
  rw [field, vecMulVec_mul_vecMulVec]
  have : Pi.single i₁ (1 : ℝ) ⬝ᵥ (Pi.single i₂ 1 + A i₁ j₁ • Pi.single i₃ 1) = 0 := by
    simp [dotProduct_add, dotProduct_smul, dotProduct_single, h₂, h₃]
  rw [this, zero_smul]
  ext i j
  simp [vecMulVec_apply]

omit [DecidableEq n] in
private theorem rowProj_mul_apply (A : Matrix m n ℝ) :
    (vecMulVec (Pi.single i₁ (1 : ℝ)) (Pi.single i₁ 1) * A) i₁ = A i₁ := by
  rw [vecMulVec_mul, single_one_vecMul]
  ext j
  simp [vecMulVec_apply]

theorem exactSol_eq (t : ℝ) :
    exactSol i₁ i₂ i₃ j₁ t = vecMulVec (Pi.single i₁ 1) (Pi.single j₁ 1) +
      t • vecMulVec (Pi.single i₂ 1 + Pi.single i₃ 1) (Pi.single j₁ 1) := by
  rw [exactSol, add_vecMulVec, smul_vecMulVec]

theorem exactSol_zero : exactSol i₁ i₂ i₃ j₁ 0 = vecMulVec (Pi.single i₁ 1) (Pi.single j₁ 1) := by
  simp [exactSol_eq]

theorem exactSol_apply_row (h₂ : i₁ ≠ i₂) (h₃ : i₁ ≠ i₃) (t : ℝ) :
    exactSol i₁ i₂ i₃ j₁ t i₁ = Pi.single j₁ 1 := by
  ext j
  simp [exactSol, vecMulVec_apply, Pi.single_apply, h₂, h₃]

/-- Along the exact solution the field is the constant `(e_{i₂} + e_{i₃}) e_{j₁}ᵀ`. -/
theorem field_exactSol (h₂ : i₁ ≠ i₂) (h₃ : i₁ ≠ i₃) (t : ℝ) :
    field i₁ i₂ i₃ j₁ (exactSol i₁ i₂ i₃ j₁ t) =
      vecMulVec (Pi.single i₂ 1 + Pi.single i₃ 1) (Pi.single j₁ 1) := by
  rw [field, exactSol_apply_row h₂ h₃]
  simp

/-- `exactSol` solves `Ȧ = F(A)` for all times. -/
theorem exactSol_hasDerivAt (h₂ : i₁ ≠ i₂) (h₃ : i₁ ≠ i₃) (t : ℝ) :
    HasDerivAt (exactSol i₁ i₂ i₃ j₁) (field i₁ i₂ i₃ j₁ (exactSol i₁ i₂ i₃ j₁ t)) t := by
  rw [field_exactSol h₂ h₃]
  have : exactSol i₁ i₂ i₃ j₁ = fun t => vecMulVec (Pi.single i₁ 1) (Pi.single j₁ 1) +
      t • vecMulVec (Pi.single i₂ 1 + Pi.single i₃ 1) (Pi.single j₁ 1) := funext exactSol_eq
  rw [this]
  simpa using ((hasDerivAt_id t).smul_const
    (vecMulVec (Pi.single i₂ 1 + Pi.single i₃ 1) (Pi.single j₁ (1 : ℝ)))).const_add
    (vecMulVec (Pi.single i₁ 1) (Pi.single j₁ 1))

theorem exactSol_odeSolution (h₂ : i₁ ≠ i₂) (h₃ : i₁ ≠ i₃) (a b : ℝ) :
    ODESolution (fun _ A => field i₁ i₂ i₃ j₁ A) (exactSol i₁ i₂ i₃ j₁) a b where
  cont := fun t _ => (exactSol_hasDerivAt h₂ h₃ t).continuousAt.continuousWithinAt
  deriv := fun t _ => (exactSol_hasDerivAt h₂ h₃ t).hasDerivWithinAt

/-- The exact solution has rank at most one. -/
theorem rank_exactSol_le (t : ℝ) : (exactSol i₁ i₂ i₃ j₁ t).rank ≤ 1 :=
  rank_vecMulVec_le _ _

/-- **No normal component.**  The field along the exact solution is tangent to the rank-one
manifold: for the row basis `V = e_{j₁}` (and any column basis `U`) the normal part
`(I - U Uᵀ) F(A(t)) (I - V Vᵀ)` vanishes. -/
theorem normal_field_exactSol (h₂ : i₁ ≠ i₂) (h₃ : i₁ ≠ i₃) {k : Type*} [Fintype k]
    (U : Matrix m k ℝ) (t : ℝ) :
    (1 - U * Uᵀ) * field i₁ i₂ i₃ j₁ (exactSol i₁ i₂ i₃ j₁ t) *
      (1 - rowBasis j₁ * (rowBasis j₁)ᵀ) = 0 := by
  rw [field_exactSol h₂ h₃, Matrix.mul_assoc]
  have : vecMulVec (Pi.single i₂ 1 + Pi.single i₃ 1) (Pi.single j₁ (1 : ℝ)) *
      (1 - rowBasis j₁ * (rowBasis j₁)ᵀ) = 0 := by
    ext i j
    simp [rowBasis, Matrix.mul_apply, vecMulVec_apply, replicateCol_apply,
      Pi.single_apply, Matrix.one_apply]
    split_ifs <;> simp_all
  rw [this, Matrix.mul_zero]

/-! ### Uniqueness of the exact solution and of the B-step solution

Both fields have zero `i₁`-th row, so the `i₁`-th row of every solution is constant; this makes
the field constant along every solution, and no Lipschitz argument is needed. -/

omit [DecidableEq m] [DecidableEq n] in
/-- If the velocity of a curve is killed by `E` on `[a, b)`, so is its displacement. -/
private theorem const_of_mul_deriv_eq_zero {E : Matrix m m ℝ} {A : ℝ → Matrix m n ℝ}
    {v : ℝ → Matrix m n ℝ} {a b : ℝ} (hc : ContinuousOn A (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt A (v t) (Ici t) t) (hv : ∀ t ∈ Ico a b, E * v t = 0) :
    ∀ t ∈ Icc a b, E * A t = E * A a := by
  refine constant_of_has_deriv_right_zero (f := fun t => E * A t) ?_ ?_
  · exact (Frobenius.leftMulCLM E).continuous.comp_continuousOn hc
  · intro t ht
    have := Frobenius.hasDerivWithinAt_const_mul E (hd t ht)
    rwa [hv t ht] at this

omit [DecidableEq m] [DecidableEq n] in
/-- A curve with constant velocity `K` on `[a, b)` is `A(a) + (t - a) K`. -/
private theorem eq_add_smul_of_deriv_const {A : ℝ → Matrix m n ℝ} {K : Matrix m n ℝ} {a b : ℝ}
    (hc : ContinuousOn A (Icc a b)) (hd : ∀ t ∈ Ico a b, HasDerivWithinAt A K (Ici t) t) :
    ∀ t ∈ Icc a b, A t = A a + (t - a) • K := by
  have h : ∀ t ∈ Icc a b, A t - t • K = A a - a • K := by
    refine constant_of_has_deriv_right_zero (f := fun t => A t - t • K) ?_ ?_
    · exact hc.sub (continuousOn_id.smul continuousOn_const)
    · intro t ht
      have h1 := (hd t ht).sub ((hasDerivWithinAt_id t (Ici t)).smul_const K)
      rw [one_smul, sub_self] at h1
      exact h1
  intro t ht
  have := h t ht
  rw [sub_eq_iff_eq_add] at this
  rw [this, sub_smul]
  abel

/-- **Uniqueness of the exact solution.**  Every solution of `Ȧ = F(A)` on `[0, h]` starting at
`e_{i₁} e_{j₁}ᵀ` is `exactSol`. -/
theorem exactSol_unique (h₂ : i₁ ≠ i₂) (h₃ : i₁ ≠ i₃) {A : ℝ → Matrix m n ℝ} {h : ℝ}
    (hA : ODESolution (fun _ X => field i₁ i₂ i₃ j₁ X) A 0 h)
    (hA0 : A 0 = exactSol i₁ i₂ i₃ j₁ 0) : ∀ t ∈ Icc 0 h, A t = exactSol i₁ i₂ i₃ j₁ t := by
  have hrow : ∀ t ∈ Icc 0 h, A t i₁ = Pi.single j₁ 1 := by
    intro t ht
    have := const_of_mul_deriv_eq_zero (E := vecMulVec (Pi.single i₁ 1) (Pi.single i₁ 1)) hA.cont
      hA.deriv (fun t _ => rowProj_mul_field h₂ h₃ (A t)) t ht
    rw [← rowProj_mul_apply (A t), this, rowProj_mul_apply, hA0, exactSol_apply_row h₂ h₃]
  have hK : ∀ t ∈ Ico 0 h, HasDerivWithinAt A
      (vecMulVec (Pi.single i₂ 1 + Pi.single i₃ 1) (Pi.single j₁ 1)) (Ici t) t := by
    intro t ht
    have := hA.deriv t ht
    simp only [field, hrow t (Ico_subset_Icc_self ht)] at this
    simpa using this
  intro t ht
  rw [eq_add_smul_of_deriv_const hA.cont hK t ht, hA0, exactSol_zero, exactSol_eq, sub_zero]

omit [DecidableEq m] [DecidableEq n] in
/-- `Ω† Ω = 1` for a sketch with independent columns (the core `Matrix.gramPinv_mul_self`). -/
theorem pinvT_mul {Ω : Matrix n κ ℝ} (hΩ : IsUnit (Ωᵀ * Ω)) : Ω.gramPinv * Ω = 1 :=
  Matrix.gramPinv_mul_self ((Matrix.isUnit_iff_isUnit_det _).mp hΩ)

omit [DecidableEq n] in
theorem bSol_eq (Ω : Matrix n κ ℝ) (t : ℝ) :
    bSol i₁ i₂ i₃ j₁ Ω t = vecMulVec (Pi.single i₁ 1) (Ω j₁) +
      t • vecMulVec (Pi.single i₂ 1 + capture j₁ Ω • Pi.single i₃ 1) (Ω j₁) := by
  rw [bSol, add_vecMulVec, smul_vecMulVec]

omit [DecidableEq κ] in
theorem exactSol_zero_mul (Ω : Matrix n κ ℝ) :
    exactSol i₁ i₂ i₃ j₁ 0 * Ω = vecMulVec (Pi.single i₁ 1) (Ω j₁) := by
  rw [exactSol_zero, vecMulVec_mul, single_one_vecMul]
  rfl

omit [DecidableEq n] in
/-- The B-step field along a matrix whose `i₁`-th row is `e_{j₁}ᵀ Ω`: the constant
`(e_{i₂} + c e_{i₃}) (e_{j₁}ᵀ Ω)`, with `c = (Ω Ω†)_{j₁ j₁}` in place of the `1` of the exact
field.  This is the whole mechanism: `F` is evaluated at `B Ω†`, whose `(i₁, j₁)` entry is `c`,
not at the solution, whose `(i₁, j₁)` entry is `1`. -/
theorem bField_of_row {Ω : Matrix n κ ℝ} (hΩ : IsUnit (Ωᵀ * Ω)) {b : Matrix m κ ℝ}
    (hb : b i₁ = Ω j₁) :
    bField i₁ i₂ i₃ j₁ Ω b =
      vecMulVec (Pi.single i₂ 1 + capture j₁ Ω • Pi.single i₃ 1) (Ω j₁) := by
  have hrow : (b * Ω.gramPinv) i₁ = (Ω * Ω.gramPinv) j₁ := by
    rw [mul_apply_eq_vecMul, mul_apply_eq_vecMul, hb]
  have hΩrow : (Ω * Ω.gramPinv) j₁ ᵥ* Ω = Ω j₁ := by
    rw [← mul_apply_eq_vecMul, Matrix.mul_assoc, pinvT_mul hΩ, Matrix.mul_one]
  rw [bField, field, vecMulVec_mul, hrow, hΩrow, capture]

/-- **Uniqueness of the B-step solution.**  Every solution of `Ḃ = F(B Ω†) Ω` on `[0, h]`
starting at `A(0) Ω` is `bSol`. -/
theorem bSol_unique (h₂ : i₁ ≠ i₂) (h₃ : i₁ ≠ i₃) {Ω : Matrix n κ ℝ} (hΩ : IsUnit (Ωᵀ * Ω))
    {B : ℝ → Matrix m κ ℝ} {h : ℝ}
    (hB : ODESolution (fun _ b => bField i₁ i₂ i₃ j₁ Ω b) B 0 h)
    (hB0 : B 0 = exactSol i₁ i₂ i₃ j₁ 0 * Ω) : ∀ t ∈ Icc 0 h, B t = bSol i₁ i₂ i₃ j₁ Ω t := by
  have hrow : ∀ t ∈ Icc 0 h, B t i₁ = Ω j₁ := by
    intro t ht
    have := const_of_mul_deriv_eq_zero (E := vecMulVec (Pi.single i₁ 1) (Pi.single i₁ 1)) hB.cont
      hB.deriv (fun t _ => by
        rw [bField, ← Matrix.mul_assoc, rowProj_mul_field h₂ h₃, Matrix.zero_mul]) t ht
    rw [← rowProj_mul_apply (B t), this, rowProj_mul_apply, hB0, exactSol_zero_mul]
    ext j
    simp [vecMulVec_apply]
  have hK : ∀ t ∈ Ico 0 h, HasDerivWithinAt B
      (vecMulVec (Pi.single i₂ 1 + capture j₁ Ω • Pi.single i₃ 1) (Ω j₁)) (Ici t) t := by
    intro t ht
    have := hB.deriv t ht
    rwa [bField_of_row hΩ (hrow t (Ico_subset_Icc_self ht))] at this
  intro t ht
  rw [eq_add_smul_of_deriv_const hB.cont hK t ht, hB0, exactSol_zero_mul, bSol_eq, sub_zero]

/-! ### The lower bound -/

omit [DecidableEq m] [DecidableEq n] in
/-- Columns in the plane `span(e_{i₁}, e_{i₂} + c e_{i₃})` have `i₃`-entry `c` times the
`i₂`-entry; the property passes to spans. -/
theorem ratio_of_mem_span {c : ℝ} {S : Set (m → ℝ)} (hS : ∀ v ∈ S, v i₃ = c * v i₂)
    {v : m → ℝ} (hv : v ∈ Submodule.span ℝ S) : v i₃ = c * v i₂ := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => simp only [Pi.add_apply, hx, hy]; ring
  | smul a x _ hx => simp only [Pi.smul_apply, smul_eq_mul, hx]; ring

omit [DecidableEq n] in
/-- The columns of `B(h)` and `e_{i₁}` lie in the plane `span(e_{i₁}, e_{i₂} + c e_{i₃})`. -/
theorem ratio_of_mem_insert_range_bSol (h₂ : i₁ ≠ i₂) (h₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    (Ω : Matrix n κ ℝ) (h : ℝ) {v : m → ℝ}
    (hv : v ∈ insert (Pi.single i₁ 1) (Set.range (bSol i₁ i₂ i₃ j₁ Ω h)ᵀ)) :
    v i₃ = capture j₁ Ω * v i₂ := by
  rcases hv with rfl | ⟨j, rfl⟩
  · simp [h₂.symm, h₃.symm]
  · simp [bSol, transpose_apply, vecMulVec_apply, h₂.symm, h₃.symm, h₂₃, h₂₃.symm]
    ring

omit [DecidableEq m] [DecidableEq n] in
theorem ratio_mul {q : Type*} [Fintype q] {c : ℝ} {Q : Matrix m q ℝ}
    (hQ : ∀ k, Q i₃ k = c * Q i₂ k) (M : Matrix q n ℝ) (j : n) :
    (Q * M) i₃ j = c * (Q * M) i₂ j := by
  simp only [Matrix.mul_apply, hQ, Finset.mul_sum, mul_assoc]

/-- **The lower bound.**  If every column of `Y` has `i₃`-entry `c` times its `i₂`-entry, then
`‖Y - A(h)‖² ≥ h² (1 - c)² / (1 + c²)`: the distance of the column `e_{i₁} + h (e_{i₂} + e_{i₃})`
of `A(h)` from the plane `span(e_{i₁}, e_{i₂} + c e_{i₃})`. -/
theorem norm_sub_exactSol_sq_ge (h₂ : i₁ ≠ i₂) (h₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    {Y : Matrix m n ℝ} {c h : ℝ} (hY : ∀ j, Y i₃ j = c * Y i₂ j) :
    (h * (1 - c)) ^ 2 / (1 + c ^ 2) ≤ ‖Y - exactSol i₁ i₂ i₃ j₁ h‖ ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  have h1 : ∑ i ∈ ({i₂, i₃} : Finset m), ∑ j, (Y - exactSol i₁ i₂ i₃ j₁ h) i j ^ 2 ≤
      ∑ i, ∑ j, (Y - exactSol i₁ i₂ i₃ j₁ h) i j ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => sum_nonneg fun j _ => sq_nonneg _
  rw [sum_pair h₂₃] at h1
  have h2 : (Y - exactSol i₁ i₂ i₃ j₁ h) i₂ j₁ ^ 2 ≤ ∑ j, (Y - exactSol i₁ i₂ i₃ j₁ h) i₂ j ^ 2 :=
    single_le_sum (fun j _ => sq_nonneg _) (mem_univ j₁)
  have h3 : (Y - exactSol i₁ i₂ i₃ j₁ h) i₃ j₁ ^ 2 ≤ ∑ j, (Y - exactSol i₁ i₂ i₃ j₁ h) i₃ j ^ 2 :=
    single_le_sum (fun j _ => sq_nonneg _) (mem_univ j₁)
  have e2 : (Y - exactSol i₁ i₂ i₃ j₁ h) i₂ j₁ = Y i₂ j₁ - h := by
    simp [exactSol, vecMulVec_apply, h₂.symm, h₂₃]
  have e3 : (Y - exactSol i₁ i₂ i₃ j₁ h) i₃ j₁ = c * Y i₂ j₁ - h := by
    simp [exactSol, vecMulVec_apply, h₃.symm, h₂₃.symm, hY]
  rw [e2] at h2
  rw [e3] at h3
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg ((1 + c ^ 2) * Y i₂ j₁ - (1 + c) * h)]

theorem norm_sub_exactSol_ge (h₂ : i₁ ≠ i₂) (h₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    {Y : Matrix m n ℝ} {c h : ℝ} (hY : ∀ j, Y i₃ j = c * Y i₂ j) (hh : 0 ≤ h) (hc : c ≤ 1) :
    h * (1 - c) / √(1 + c ^ 2) ≤ ‖Y - exactSol i₁ i₂ i₃ j₁ h‖ := by
  have hsq := norm_sub_exactSol_sq_ge h₂ h₃ h₂₃ (j₁ := j₁) (h := h) hY
  have hpos : 0 < 1 + c ^ 2 := by positivity
  have h0 : 0 ≤ h * (1 - c) := mul_nonneg hh (by linarith)
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_div' _ hpos.le, Real.sqrt_sq h0, Real.sqrt_sq (norm_nonneg _)] at this

/-! ### The capture is a number in `[0, 1]` -/

omit [DecidableEq m] [DecidableEq n] in
/-- `Ω Ω†` is symmetric (the core `Matrix.transpose_mul_gramPinv`). -/
theorem transpose_mul_pinvT {Ω : Matrix n κ ℝ} : (Ω * Ω.gramPinv)ᵀ = Ω * Ω.gramPinv :=
  Matrix.transpose_mul_gramPinv Ω

omit [DecidableEq m] [DecidableEq n] in
/-- `Ω Ω†` is idempotent for a sketch with independent columns. -/
theorem mul_pinvT_mul_mul_pinvT {Ω : Matrix n κ ℝ} (hΩ : IsUnit (Ωᵀ * Ω)) :
    Ω * Ω.gramPinv * (Ω * Ω.gramPinv) = Ω * Ω.gramPinv := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Ω.gramPinv), pinvT_mul hΩ, Matrix.one_mul]

omit [DecidableEq m] [DecidableEq n] in
/-- `0 ≤ c ≤ 1`: `c` is the `(j₁, j₁)` entry of the orthogonal projector `Ω Ω†`. -/
theorem capture_mem_Icc {Ω : Matrix n κ ℝ} (hΩ : IsUnit (Ωᵀ * Ω)) :
    capture j₁ Ω ∈ Icc (0 : ℝ) 1 := by
  have hdiag : (Ω * Ω.gramPinv) j₁ j₁ = ∑ k, (Ω * Ω.gramPinv) j₁ k ^ 2 := by
    conv_lhs => rw [← mul_pinvT_mul_mul_pinvT hΩ]
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : (Ω * Ω.gramPinv) k j₁ = (Ω * Ω.gramPinv) j₁ k := by
      rw [← Matrix.transpose_apply (Ω * Ω.gramPinv) j₁ k, transpose_mul_pinvT]
    rw [this, sq]
  have h1 : (Ω * Ω.gramPinv) j₁ j₁ ^ 2 ≤ ∑ k, (Ω * Ω.gramPinv) j₁ k ^ 2 :=
    single_le_sum (fun k _ => sq_nonneg _) (mem_univ j₁)
  have h0 : 0 ≤ ∑ k, (Ω * Ω.gramPinv) j₁ k ^ 2 := sum_nonneg fun k _ => sq_nonneg _
  change (Ω * Ω.gramPinv) j₁ j₁ ∈ Icc (0 : ℝ) 1
  rw [hdiag] at h1 ⊢
  exact ⟨h0, by nlinarith⟩

/-! ### The practical DRSVD step on this problem -/

/-- Every matrix whose columns lie in `span(e_{i₁}, columns of B(h))` has the ratio property. -/
theorem ratio_of_drsvd (h₂ : i₁ ≠ i₂) (h₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) {Ω : Matrix n κ ℝ}
    (hΩ : IsUnit (Ωᵀ * Ω)) {h : ℝ} (hh : 0 ≤ h) {B : ℝ → Matrix m κ ℝ}
    (hB : ODESolution (fun _ b => bField i₁ i₂ i₃ j₁ Ω b) B 0 h)
    (hB0 : B 0 = exactSol i₁ i₂ i₃ j₁ 0 * Ω) {q : Type*} [Fintype q] {Q : Matrix m q ℝ}
    (hQ : ∀ k, Qᵀ k ∈ Submodule.span ℝ (insert (Pi.single i₁ 1) (Set.range (B h)ᵀ)))
    (M : Matrix q n ℝ) (j : n) : (Q * M) i₃ j = capture j₁ Ω * (Q * M) i₂ j := by
  have hBh : B h = bSol i₁ i₂ i₃ j₁ Ω h := bSol_unique h₂ h₃ hΩ hB hB0 h ⟨hh, le_rfl⟩
  refine ratio_mul (fun k => ?_) M j
  have := ratio_of_mem_span (c := capture j₁ Ω)
    (fun v hv => ratio_of_mem_insert_range_bSol h₂ h₃ h₂₃ Ω h (by rwa [← hBh])) (hQ k)
  simpa using this

/-- **The practical dynamical rangefinder is inconsistent (OP-RS-34).**

Problem: `Ȧ = F(A)`, `F(A) = (e_{i₂} + A_{i₁ j₁} e_{i₃}) (e_{i₁}ᵀ A)`, `A(0) = e_{i₁} e_{j₁}ᵀ`,
on `m × n` matrices with three distinct row indices.  The exact solution
`A(t) = (e_{i₁} + t (e_{i₂} + e_{i₃})) e_{j₁}ᵀ` has rank one for all `t` (`rank_exactSol_le`), so
the flow is exactly rank-`1` approximable (`ε = 0`), and `F(A(t))` is tangent to the rank-one
manifold (`normal_field_exactSol`), so the small-normal-component assumption holds with `ε = 0`
as well.

One step of DRSVD (arXiv 2410.17091, Alg. 3 with `q = 0` power iterations) from `Y₀ = A(0)`
with any sketch `Ω ∈ ℝ^{n × κ}` of linearly independent columns:
* the practical B-step `Ḃ = F(B Ω†) Ω`, `B(0) = Y₀ Ω` (any solution `B`, by `bSol_unique` the
  only one);
* `Q = orth[U₀, orth(B(h))]`, any matrix whose columns lie in `span(e_{i₁}, columns of B(h))`;
* the C-step and the truncation produce `Y₁ = Q M` for some `M` (`Y₁ = 𝒯_r(Q C(h)ᵀ)`,
  `drsvd_truncation_error_ge`).

Then `‖Y₁ - A(h)‖_F ≥ h (1 - c) / √(1 + c²)` with `c = (Ω Ω†)_{j₁ j₁} = ‖Π_Ω e_{j₁}‖² ∈ [0, 1]`
(`capture_mem_Icc`); `c < 1` unless `e_{j₁} ∈ range Ω`.  The local error is of first order in
`h` with a constant independent of `ε = 0`, so the method is not consistent: no error bound of the
form `C (ε + h)`, under flow approximability or under the small-normal-component assumption, can
hold for the practical DRSVD.  Mechanism (`bField_of_row`): the B-step evaluates `F` at
`B Ω† = A Π_Ω`, whose `(i₁, j₁)` entry is `c` instead of `1`, so it integrates the field
`(e_{i₂} + c e_{i₃}) e_{j₁}ᵀ Ω` and the range it finds is `e_{i₂} + c e_{i₃}`, not
`e_{i₂} + e_{i₃}`.  For fields `F(A) = L A + A R + G` (the paper's Lyapunov test) a first-order
computation, not formalized, shows that the B-step perturbation lies in `range Y₀`, so the
mechanism needs a field that is nonlinear in the entries. -/
theorem drsvd_error_ge (h₂ : i₁ ≠ i₂) (h₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) {Ω : Matrix n κ ℝ}
    (hΩ : IsUnit (Ωᵀ * Ω)) {h : ℝ} (hh : 0 ≤ h) {B : ℝ → Matrix m κ ℝ}
    (hB : ODESolution (fun _ b => bField i₁ i₂ i₃ j₁ Ω b) B 0 h)
    (hB0 : B 0 = exactSol i₁ i₂ i₃ j₁ 0 * Ω) {q : Type*} [Fintype q] {Q : Matrix m q ℝ}
    (hQ : ∀ k, Qᵀ k ∈ Submodule.span ℝ (insert (Pi.single i₁ 1) (Set.range (B h)ᵀ)))
    (M : Matrix q n ℝ) :
    h * (1 - capture j₁ Ω) / √(1 + capture j₁ Ω ^ 2) ≤ ‖Q * M - exactSol i₁ i₂ i₃ j₁ h‖ :=
  norm_sub_exactSol_ge h₂ h₃ h₂₃ (ratio_of_drsvd h₂ h₃ h₂₃ hΩ hh hB hB0 hQ M) hh
    (capture_mem_Icc hΩ).2

omit [DecidableEq m] in
/-- The truncated SVD of `Q N` has the form `Q M`. -/
theorem truncation_mul_eq {q : Type*} [Fintype q] (Q : Matrix m q ℝ) (N : Matrix q n ℝ)
    (r : ℕ) : EckartYoung.truncation (Q * N) r =
      Q * (N * EckartYoung.topRightSingularVectors (Q * N) r *
        (EckartYoung.topRightSingularVectors (Q * N) r)ᵀ) := by
  simp only [EckartYoung.truncation, Matrix.mul_assoc]

/-- `drsvd_error_ge` for the output `Y₁ = 𝒯_r(Q C(h)ᵀ)` of the C-step and truncation, whatever
`C(h)` and `r` are (in the algorithm `C` solves `Ċ = F(Q Cᵀ)ᵀ Q`, `C(0) = Y₀ᵀ Q`). -/
theorem drsvd_truncation_error_ge (h₂ : i₁ ≠ i₂) (h₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    {Ω : Matrix n κ ℝ} (hΩ : IsUnit (Ωᵀ * Ω)) {h : ℝ} (hh : 0 ≤ h) {B : ℝ → Matrix m κ ℝ}
    (hB : ODESolution (fun _ b => bField i₁ i₂ i₃ j₁ Ω b) B 0 h)
    (hB0 : B 0 = exactSol i₁ i₂ i₃ j₁ 0 * Ω) {q : Type*} [Fintype q] {Q : Matrix m q ℝ}
    (hQ : ∀ k, Qᵀ k ∈ Submodule.span ℝ (insert (Pi.single i₁ 1) (Set.range (B h)ᵀ)))
    (C : Matrix n q ℝ) (r : ℕ) :
    h * (1 - capture j₁ Ω) / √(1 + capture j₁ Ω ^ 2) ≤
      ‖EckartYoung.truncation (Q * Cᵀ) r - exactSol i₁ i₂ i₃ j₁ h‖ := by
  rw [truncation_mul_eq]
  exact drsvd_error_ge h₂ h₃ h₂₃ hΩ hh hB hB0 hQ _

/-! ### Expectation over an isotropic sketch (one column, `p = 0`) -/

omit [DecidableEq m] in
/-- For a one-column sketch `Ω = ω`, `c = ω_{j₁}² / ‖ω‖²`. -/
theorem capture_replicateCol (w : n → ℝ) :
    capture j₁ (replicateCol Unit w) = (w ⬝ᵥ Pi.single j₁ 1) ^ 2 / (w ⬝ᵥ w) := by
  rw [dotProduct_single, mul_one]
  simp [capture, Matrix.gramPinv, Matrix.mul_apply, replicateCol_apply, Matrix.inv_subsingleton,
    Ring.inverse_eq_inv', dotProduct, sq, div_eq_mul_inv]
  ring

omit [DecidableEq m] [DecidableEq n] in
theorem isUnit_transpose_mul_replicateCol {w : n → ℝ} (hw : w ≠ 0) :
    IsUnit ((replicateCol Unit w)ᵀ * replicateCol Unit w) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique, isUnit_iff_ne_zero]
  simpa [Matrix.mul_apply, replicateCol_apply, transpose_apply, dotProduct] using
    dotProduct_self_eq_zero.not.mpr hw

section Expectation

variable {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ] {ω : Ξ → n → ℝ}

/-- **Expected error of the practical DRSVD step for an isotropic one-column sketch.**
For every selection `Y ξ` (measurable or not) with the ratio property of `drsvd_error_ge` for
almost every sketch `ω ξ`, the lower integral of the error is at least
`h (1 - 1/n) / √2`, since `E[c] = E[ω_{j₁}² / ‖ω‖²] = 1/n` (`IsIsotropicLaw`, which the standard
Gaussian satisfies, `BlindSpotII.isIsotropicLaw_stdGaussian`). -/
theorem lintegral_error_ge (hiso : BlindSpotII.IsIsotropicLaw μ ω) (h₂ : i₁ ≠ i₂)
    (h₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) {h : ℝ} (hh : 0 ≤ h) {Y : Ξ → Matrix m n ℝ}
    (hY : ∀ᵐ ξ ∂μ, ∀ j, Y ξ i₃ j = capture j₁ (replicateCol Unit (ω ξ)) * Y ξ i₂ j) :
    ENNReal.ofReal (h * (1 - 1 / Fintype.card n) / √2) ≤
      ∫⁻ ξ, ENNReal.ofReal ‖Y ξ - exactSol i₁ i₂ i₃ j₁ h‖ ∂μ := by
  set e : n → ℝ := Pi.single j₁ 1 with he
  set f : Ξ → ℝ := fun ξ => h * (1 - (ω ξ ⬝ᵥ e) ^ 2 / (ω ξ ⬝ᵥ ω ξ)) / √2 with hf
  have hee : e ⬝ᵥ e = 1 := by simp [he]
  have hint : Integrable f μ := by
    have := ((integrable_const (1 : ℝ)).sub (hiso.integrable_ratio e)).const_mul h
    exact this.div_const _
  have hintf : ∫ ξ, f ξ ∂μ = h * (1 - 1 / Fintype.card n) / √2 := by
    rw [hf, integral_div, integral_const_mul, integral_sub (integrable_const _)
      (hiso.integrable_ratio e), hiso.isotropic e, hee]
    simp
  have hc1 : ∀ ξ, (ω ξ ⬝ᵥ e) ^ 2 / (ω ξ ⬝ᵥ ω ξ) ≤ 1 := fun ξ => by
    simpa [hee] using BlindSpotII.ratio_le (ω ξ) e
  have hf0 : ∀ ξ, 0 ≤ f ξ := fun ξ => by
    have := hc1 ξ
    positivity
  have hle : ∀ᵐ ξ ∂μ, f ξ ≤ ‖Y ξ - exactSol i₁ i₂ i₃ j₁ h‖ := by
    filter_upwards [hY] with ξ hξ
    set c := (ω ξ ⬝ᵥ e) ^ 2 / (ω ξ ⬝ᵥ ω ξ) with hcdef
    have hc : capture j₁ (replicateCol Unit (ω ξ)) = c := capture_replicateCol (ω ξ)
    have hc0 : 0 ≤ c := BlindSpotII.ratio_nonneg _ _
    rw [hc] at hξ
    refine le_trans ?_ (norm_sub_exactSol_ge h₂ h₃ h₂₃ hξ hh (hc1 ξ))
    apply div_le_div_of_nonneg_left (mul_nonneg hh (by linarith [hc1 ξ])) (by positivity)
    exact Real.sqrt_le_sqrt (by nlinarith [hc1 ξ])
  rw [← hintf, ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hf0)]
  exact lintegral_mono_ae (hle.mono fun ξ hξ => ENNReal.ofReal_le_ofReal hξ)

open ProbabilityTheory in
/-- **The practical DRSVD step with a standard Gaussian one-column sketch**: whatever the
B-step solution, the orthonormalisation and the C-step produce for each sketch, the expected
error after one step from `A(0)` is at least `h (1 - 1/n) / √2`, with `ε = 0` (lower integral,
so that nothing needs to be measurable).  Here `Y x = Q_x M_x` with the columns of `Q_x` in
`span(e_{i₁}, columns of B_x(h))`, for almost every `x`, as in `drsvd_error_ge`. -/
theorem lintegral_gaussian_error_ge [Nonempty n] (h₂ : i₁ ≠ i₂) (h₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    {h : ℝ} (hh : 0 ≤ h) {Y : EuclideanSpace ℝ n → Matrix m n ℝ}
    (hY : ∀ x : EuclideanSpace ℝ n, x ≠ 0 →
      ∃ (B : ℝ → Matrix m Unit ℝ) (d : ℕ) (Q : Matrix m (Fin d) ℝ) (M : Matrix (Fin d) n ℝ),
        ODESolution (fun _ b => bField i₁ i₂ i₃ j₁ (replicateCol Unit x.ofLp) b) B 0 h ∧
        B 0 = exactSol i₁ i₂ i₃ j₁ 0 * replicateCol Unit x.ofLp ∧
        (∀ k, Qᵀ k ∈ Submodule.span ℝ (insert (Pi.single i₁ 1) (Set.range (B h)ᵀ))) ∧
        Y x = Q * M) :
    ENNReal.ofReal (h * (1 - 1 / Fintype.card n) / √2) ≤
      ∫⁻ x, ENNReal.ofReal ‖Y x - exactSol i₁ i₂ i₃ j₁ h‖ ∂(stdGaussian (EuclideanSpace ℝ n)) := by
  refine lintegral_error_ge BlindSpotII.isIsotropicLaw_stdGaussian h₂ h₃ h₂₃ hh ?_
  have hne : ∀ᵐ x : EuclideanSpace ℝ n ∂(stdGaussian (EuclideanSpace ℝ n)), x ≠ 0 := by
    have := BlindSpotII.ae_mulVec_ne_zero_stdGaussian (n := n) (N := (1 : Matrix n n ℝ))
      one_ne_zero
    filter_upwards [this] with x hx h0
    exact hx (by rw [h0]; simp)
  filter_upwards [hne] with x hx
  obtain ⟨B, d, Q, M, hB, hB0, hQ, hYx⟩ := hY x hx
  have hw : x.ofLp ≠ 0 := fun h0 => hx (by ext i; simpa using congrFun h0 i)
  rw [hYx]
  exact ratio_of_drsvd h₂ h₃ h₂₃ (isUnit_transpose_mul_replicateCol hw) hh hB hB0 hQ M

end Expectation

end Counterexample

/-! ## The capture lemma from approximability: the idealized rangefinder

The positive counterpart.  If the sketch `A Ω` of the exact flow `A = Φ^h(Y₀)` is captured by the
range of `Q` up to a perturbation `E` (the error of the B-step), then the one-step error of the
idealized DRSVD output `𝒯_r(Q Qᵀ A)` is controlled by the rank-`r` approximability of `A` and a
sketch constant alone: no tangent/normal splitting enters.  Deterministic, every sketch. -/

section Capture

variable {m n q r k : Type*} [Fintype m] [Fintype n] [Fintype q] [Fintype r] [Fintype k]
  [DecidableEq m] [DecidableEq n] [DecidableEq q] [DecidableEq r]

omit [DecidableEq n] in
/-- `(I - Q Qᵀ) W` is shorter than `W` for orthonormal `Q`. -/
theorem norm_one_sub_mul_le {Q : Matrix m q ℝ} (hQ : Qᵀ * Q = 1) (W : Matrix m n ℝ) :
    ‖(1 - Q * Qᵀ) * W‖ ≤ ‖W‖ := by
  have := ((isOrthProj_leftProj (n := n) hQ).compl).norm_le W
  rwa [one_sub_leftProj_apply] at this

omit [DecidableEq m] [DecidableEq n] in
theorem norm_proj_mul_le {Q : Matrix m q ℝ} (hQ : Qᵀ * Q = 1) (W : Matrix m n ℝ) :
    ‖Q * Qᵀ * W‖ ≤ ‖W‖ := by
  have := (isOrthProj_leftProj (n := n) hQ).norm_le W
  rwa [leftProj_apply] at this

/-- **Perturbed deterministic rangefinder bound** (Halko–Martinsson–Tropp 2011, Thm. 9.1, in
the Frobenius norm, with a perturbation `E` of the sketch).  Let `V₁` be any `r` orthonormal
columns, `A₂ = A (I - V₁ V₁ᵀ)` the corresponding remainder (for the top right singular vectors,
`‖A₂‖ = ‖A - 𝒯_r(A)‖`), `Ω` a sketch and `X` a right inverse of `Ω₁ = V₁ᵀ Ω`.  If the range of
the orthonormal `Q` contains the perturbed sketch `A Ω + E`, then

  `‖(I - Q Qᵀ) A‖² ≤ ‖A₂‖² + ‖(E + A₂ Ω) X‖²`.

With `E = 0`, `X = Ω₁†` this is HMT's `‖Σ₂‖² + ‖Σ₂ Ω₂ Ω₁†‖²`; the term `‖E X‖ ≤ ‖E‖ ‖Ω₁†‖₂` is
the price of an inexact B-step.  Proof: `A V₁ = (A Ω + E) X - (E + A₂ Ω) X`, and `(I - Q Qᵀ)`
kills the first term. -/
theorem norm_one_sub_proj_mul_sq_le {Q : Matrix m q ℝ} (hQ : Qᵀ * Q = 1) {V₁ : Matrix n r ℝ}
    (hV : V₁ᵀ * V₁ = 1) (A : Matrix m n ℝ) (Ω : Matrix n k ℝ) (E : Matrix m k ℝ)
    {X : Matrix k r ℝ} (hX : V₁ᵀ * Ω * X = 1) (hcap : Q * Qᵀ * (A * Ω + E) = A * Ω + E) :
    ‖(1 - Q * Qᵀ) * A‖ ^ 2 ≤
      ‖A * (1 - V₁ * V₁ᵀ)‖ ^ 2 + ‖(E + A * (1 - V₁ * V₁ᵀ) * Ω) * X‖ ^ 2 := by
  set P := Q * Qᵀ with hP
  set A₂ := A * (1 - V₁ * V₁ᵀ) with hA₂
  have hpyth : ‖(1 - P) * A * V₁ * V₁ᵀ‖ ^ 2 + ‖(1 - P) * A - (1 - P) * A * V₁ * V₁ᵀ‖ ^ 2 =
      ‖(1 - P) * A‖ ^ 2 := by
    have := (isOrthProj_rightProj (m := m) hV).norm_sq_add ((1 - P) * A)
    simpa only [rightProj_apply] using this
  have hZ2 : (1 - P) * A - (1 - P) * A * V₁ * V₁ᵀ = (1 - P) * A₂ := by
    simp only [hA₂, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  have hkill : (1 - P) * (A * Ω + E) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hcap, sub_self]
  have hsplit : A * Ω = A * V₁ * (V₁ᵀ * Ω) + A₂ * Ω := by
    simp only [hA₂, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have hAV : A * V₁ = (A * Ω + E) * X - (E + A₂ * Ω) * X := by
    have : (A * Ω + E) - (E + A₂ * Ω) = A * V₁ * (V₁ᵀ * Ω) := by rw [hsplit]; abel
    rw [← Matrix.sub_mul, this, Matrix.mul_assoc, hX, Matrix.mul_one]
  have hZV : (1 - P) * A * V₁ = -((1 - P) * ((E + A₂ * Ω) * X)) := by
    rw [Matrix.mul_assoc, hAV, Matrix.mul_sub, ← Matrix.mul_assoc, hkill, Matrix.zero_mul,
      zero_sub]
  have h1 : ‖(1 - P) * A * V₁ * V₁ᵀ‖ ≤ ‖(E + A₂ * Ω) * X‖ := by
    rw [Frobenius.norm_mul_transpose_of_orthonormal hV, hZV, norm_neg]
    exact norm_one_sub_mul_le hQ _
  have h2 : ‖(1 - P) * A₂‖ ≤ ‖A₂‖ := norm_one_sub_mul_le hQ _
  rw [← hpyth, hZ2]
  have h1' := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2' := pow_le_pow_left₀ (norm_nonneg _) h2 2
  linarith

omit [DecidableEq m] [DecidableEq n] in
/-- The projector `Q Qᵀ` is idempotent. -/
theorem proj_mul_proj {Q : Matrix m q ℝ} (hQ : Qᵀ * Q = 1) : Q * Qᵀ * (Q * Qᵀ) = Q * Qᵀ := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ, hQ, Matrix.one_mul]

omit [DecidableEq m] in
/-- **One-step bound for the idealized DRSVD from approximability.**  With the
notation of `norm_one_sub_proj_mul_sq_le` and `r' ≥ r`, the truncated projection
`Y₁ = 𝒯_{r'}(Q Qᵀ A)` (the output of DRSVD with an exact C-step, `Q C(h)ᵀ = Q Qᵀ A(h)`)
satisfies

  `‖A - Y₁‖² ≤ 2 ‖A₂‖² + ‖(E + A₂ Ω) X‖²`.

For `A = Φ^h(Y₀)` the exact flow, `V₁` its top-`r` right singular vectors and `E = 0`, this is
`‖Y₁ - Φ^h(Y₀)‖ ≤ (2 + ‖Ω₂ Ω₁†‖₂²)^{1/2} ‖Φ^h(Y₀) - 𝒯_r(Φ^h(Y₀))‖`: the local error is
controlled by the rank-`r` approximability of the exact flow times a sketch constant, with no
assumption on the normal component of `F`.  The sketch constant is the one of HMT; its Gaussian
expectation `(1 + r/(p - 1))` is not proved here. -/
theorem norm_sub_truncation_proj_sq_le {Q : Matrix m q ℝ} (hQ : Qᵀ * Q = 1)
    {V₁ : Matrix n r ℝ} (hV : V₁ᵀ * V₁ = 1) (A : Matrix m n ℝ) (Ω : Matrix n k ℝ)
    (E : Matrix m k ℝ) {X : Matrix k r ℝ} (hX : V₁ᵀ * Ω * X = 1)
    (hcap : Q * Qᵀ * (A * Ω + E) = A * Ω + E) {r' : ℕ} (hr : Fintype.card r ≤ r') :
    ‖A - EckartYoung.truncation (Q * Qᵀ * A) r'‖ ^ 2 ≤
      2 * ‖A * (1 - V₁ * V₁ᵀ)‖ ^ 2 + ‖(E + A * (1 - V₁ * V₁ᵀ) * Ω) * X‖ ^ 2 := by
  classical
  set P := Q * Qᵀ with hP
  set T := EckartYoung.truncation (P * A) r' with hT
  have hPP : P * P = P := proj_mul_proj hQ
  have hPT : P * T = T := by
    rw [hT, EckartYoung.truncation]
    simp only [← Matrix.mul_assoc, hPP]
  have hpyth : ‖P * (A - T)‖ ^ 2 + ‖(A - T) - P * (A - T)‖ ^ 2 = ‖A - T‖ ^ 2 := by
    have := (isOrthProj_leftProj (n := n) hQ).norm_sq_add (A - T)
    simpa only [leftProj_apply] using this
  have e1 : P * (A - T) = P * A - T := by rw [Matrix.mul_sub, hPT]
  have e2 : (A - T) - (P * A - T) = (1 - P) * A := by
    rw [Matrix.sub_mul, Matrix.one_mul]; abel
  rw [e1, e2] at hpyth
  -- Eckart–Young for the projected matrix, against the competitor `P A V₁ V₁ᵀ`
  have hrank : (P * A * V₁ * V₁ᵀ).rank ≤ r' :=
    (Matrix.rank_mul_le_right _ _).trans ((Matrix.rank_le_card_height _).trans hr)
  have hEY : ‖P * A - T‖ ≤ ‖A * (1 - V₁ * V₁ᵀ)‖ := by
    refine (EckartYoung.norm_sub_truncation_le (P * A) hrank).trans ?_
    have : P * A - P * A * V₁ * V₁ᵀ = P * (A * (1 - V₁ * V₁ᵀ)) := by
      simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    rw [this]
    exact norm_proj_mul_le hQ _
  have hHMT := norm_one_sub_proj_mul_sq_le hQ hV A Ω E hX hcap
  have hEY' := pow_le_pow_left₀ (norm_nonneg _) hEY 2
  rw [← hpyth]
  linarith

omit [DecidableEq m] in
/-- `norm_sub_truncation_proj_sq_le` with `V₁` the top-`r` right singular vectors of `A`, so that
`A₂ = A - 𝒯_r(A)` is the best rank-`r` error: `‖A - 𝒯_r(Q Qᵀ A)‖² ≤ 2 ‖A - 𝒯_r A‖² +
‖(E + (A - 𝒯_r A) Ω) X‖²` for every right inverse `X` of `V_rᵀ Ω`. -/
theorem norm_sub_truncation_proj_sq_le_svd {Q : Matrix m q ℝ} (hQ : Qᵀ * Q = 1)
    (A : Matrix m n ℝ) (Ω : Matrix n k ℝ) (E : Matrix m k ℝ) (r' : ℕ)
    {X : Matrix k {i : Fin (Module.finrank ℝ (EuclideanSpace ℝ n)) // (i : ℕ) < r'} ℝ}
    (hX : (EckartYoung.topRightSingularVectors A r')ᵀ * Ω * X = 1)
    (hcap : Q * Qᵀ * (A * Ω + E) = A * Ω + E) :
    ‖A - EckartYoung.truncation (Q * Qᵀ * A) r'‖ ^ 2 ≤
      2 * ‖A - EckartYoung.truncation A r'‖ ^ 2 +
        ‖(E + (A - EckartYoung.truncation A r') * Ω) * X‖ ^ 2 := by
  have hcard : Fintype.card {i : Fin (Module.finrank ℝ (EuclideanSpace ℝ n)) // (i : ℕ) < r'} ≤
      r' := by
    refine (Fintype.card_le_of_injective (fun i => (⟨i.1, i.2⟩ : Fin r')) fun a b h => ?_).trans
      (Fintype.card_fin r').le
    exact Subtype.ext (Fin.ext (by simpa using congrArg Fin.val h))
  have htr : A - EckartYoung.truncation A r' =
      A * (1 - EckartYoung.topRightSingularVectors A r' *
        (EckartYoung.topRightSingularVectors A r')ᵀ) := by
    rw [EckartYoung.truncation, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  rw [htr]
  exact norm_sub_truncation_proj_sq_le hQ (EckartYoung.transpose_mul_topRightSingularVectors A r')
    A Ω E hX hcap hcard

end Capture

/-- The local sketch pseudo-inverse of this file, replaced by the core `Matrix.gramPinv` (same
definition, `(ΩᵀΩ)⁻¹Ωᵀ`). -/
@[deprecated (since := "2026-11-09")] alias pinvT := Matrix.gramPinv

end LeanDLRA.Novel.OpRS34
