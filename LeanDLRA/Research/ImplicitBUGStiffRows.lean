import LeanDLRA.Stiff.ImplicitGalerkinTangential
import LeanDLRA.Matrix.Frobenius

/-!
# The implicit BUG step is not stable uniformly in the stiffness: a family of `2 × 2` steps

For the fixed-rank BUG integrator with backward Euler substeps and a Sylvester-stiff field
`F(Z) = M Z + Z N` the K-step uses the compression `V₀ᵀ N V₀` of the stiff matrix `N` to the
row space of the NUMERICAL solution. If this row space carries a small rough component, of angle `θ`
against a row space on which `N` vanishes, the compression is of size `‖N‖ θ²`, and the
K-step `(1 - h M - h V₀ᵀ N V₀) K₁ = K₀` takes the effective step size `h/(1 + h ‖N‖ θ²)` for
the column space. This file has an explicit family for `2 × 2` matrices and rank `1`:

  `M = diag(0, -1)`,  `N = diag(0, -lam)`,  `X(t) = (3/5, 4/5 e^{-t})ᵀ (1, 0)`,
  `Y₀ = (3/5, 4/5)ᵀ (c, s)`,  `c² + s² = 1`,  `h lam s² = 1`.

`X` is an exact solution of rank `1` with singular value at least `3/5`, the field is linear
and dissipative (`ℓ = 0`, no non-stiff part), `‖Y₀ - X(0)‖² ≤ 2 s² = 2/(h lam)`, and every step of
the integrator from `Y₀` has `‖Y₁ - X(h)‖ ≥ 2h/25`. So no bound

  `‖Y₁ - X(t₁)‖ ≤ C₁ ‖Y₀ - X(t₀)‖ + C₂ h²`

holds with constants that do not depend on `lam`, whereas the flow of the differential equation
on the rank-`1` matrices is non-expansive.

## Main results

* `StiffRowsExample.two_mul_div_le_norm_sub`: `‖Y₁ - X(h)‖ ≥ 2h/25` for every step.
* `StiffRowsExample.norm_start_sub_sq_le`: `‖Y₀ - X(0)‖² ≤ 2 s²`.
* `StiffRowsExample.odeSolution`: `X` solves `Ẋ = M X + X N`.
* `StiffRowsExample.exists_isMatrixImplicitBUGStep`: a step exists for every `h ≥ 0`,
  `lam ≥ 0`.
* `StiffRowsExample.not_exists_forall_norm_sub_le`: there are no constants `C₁`, `C₂` as above.

## Implementation notes

The lower bound uses the K-step and the capture `U₁ U₁ᵀ K₁ = K₁` only: the result of the step
has its columns in the span of `K₁ = (3/10, 4/(5 (2 + h)))ᵀ`, and the distance of `X(h)` from this
span is at least `2h/25`. The stiff term of
`IsMatrixImplicitBUGStep.norm_kstep_sub_le_of_sylvester_add` is
`h ‖X₁ (1 - Q₀) N Q₀‖ = c ‖X₁‖` here: the K-step result loses a fixed fraction of its norm.
The existence of the Galerkin step is `implicitGalerkin_existsUnique_affine`.

## References

* [CerutiLubich2022] for the BUG integrator; backward Euler substeps as in arXiv 2610.18419.
-/

open Set
open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA

namespace StiffRowsExample

/-- The matrix `diag(0, -1)` acting on the columns. -/
local notation "Mₛ" => (!![0, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ)

/-- The stiff matrix `diag(0, -lam)` acting on the rows. -/
local notation "Nₛ" lam => (!![0, 0; 0, -lam] : Matrix (Fin 2) (Fin 2) ℝ)

/-- The start column `(3/5, 4/5)ᵀ`. -/
local notation "u₀" => (!![3 / 5; 4 / 5] : Matrix (Fin 2) (Fin 1) ℝ)

/-- The field applied to the K-stage, times the old row basis. -/
private theorem field_mul_col (lam c s : ℝ) (K : Matrix (Fin 2) (Fin 1) ℝ) :
    (Mₛ * (K * !![c; s]ᵀ) + K * !![c; s]ᵀ * Nₛ lam) * !![c; s] =
      !![-(lam * s ^ 2) * K 0 0; -(c ^ 2 + s ^ 2) * K 1 0 - lam * s ^ 2 * K 1 0] := by
  ext i j
  fin_cases j
  fin_cases i
  · norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, Matrix.vecHead,
      Function.swap]
    ring
  · norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, Matrix.vecHead,
      Function.swap]
    ring

/-- The transposed field applied to the L-stage, times the old column basis. -/
private theorem transpose_field_mul_col (lam : ℝ) (L : Matrix (Fin 2) (Fin 1) ℝ) :
    (Mₛ * (u₀ * Lᵀ) + u₀ * Lᵀ * Nₛ lam)ᵀ * u₀ =
      !![-(16 / 25) * L 0 0; -(16 / 25) * L 1 0 - lam * L 1 0] := by
  ext i j
  fin_cases j
  fin_cases i
  · norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, Matrix.vecHead]
    ring
  · norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, Matrix.vecHead]
    ring

/-- The squares of the first column are at most the squared Frobenius norm. -/
private theorem sq_add_sq_le_norm_sq (D : Matrix (Fin 2) (Fin 2) ℝ) :
    D 0 0 ^ 2 + D 1 0 ^ 2 ≤ ‖D‖ ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  nlinarith [sq_nonneg (D 0 1), sq_nonneg (D 1 1)]

/-- The distance of `(3/5, 4/5 E)` from the line spanned by a unit vector `(a, b)` that is
parallel to `(3/10, k₁)`, `k₁ (2 + h) = 4/5`, for `E (1 + h) ≤ 1`. -/
private theorem scalar_bound {h a b k1 w E : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hab : a ^ 2 + b ^ 2 = 1) (c0 : a * (a * (3 / 10) + b * k1) = 3 / 10)
    (c1 : b * (a * (3 / 10) + b * k1) = k1) (hk1 : k1 * (2 + h) = 4 / 5)
    (hE : E * (1 + h) ≤ 1) :
    (2 * h / 25) ^ 2 ≤ (a * w - 3 / 5) ^ 2 + (b * w - 4 / 5 * E) ^ 2 := by
  have hsplit : (a * w - 3 / 5) ^ 2 + (b * w - 4 / 5 * E) ^ 2 =
      (w - (a * (3 / 5) + b * (4 / 5 * E))) ^ 2 + (b * (3 / 5) - a * (4 / 5 * E)) ^ 2 := by
    linear_combination (w ^ 2 - (3 / 5) ^ 2 - (4 / 5 * E) ^ 2) * hab
  have hq : (b * (3 / 5) - a * (4 / 5 * E)) * (a * (3 / 10) + b * k1) =
      3 / 5 * k1 - 4 / 5 * E * (3 / 10) := by
    linear_combination (3 / 5 : ℝ) * c1 - 4 / 5 * E * c0
  have hγ : (a * (3 / 10) + b * k1) ^ 2 = (3 / 10) ^ 2 + k1 ^ 2 := by
    linear_combination (3 / 10 : ℝ) * c0 + k1 * c1
  have hk1e : k1 = 4 / 5 / (2 + h) := by
    rw [eq_div_iff (by positivity)]
    exact hk1
  have hk1pos : 0 < k1 := by
    rw [hk1e]
    positivity
  have hk1le : k1 ≤ 2 / 5 := by
    rw [hk1e, div_le_iff₀ (by positivity)]
    nlinarith
  have hpos : 0 < (2 + h) * (1 + h) := by positivity
  have h6 : (2 + h) * (1 + h) ≤ 6 := by nlinarith
  have h3 : (3 / 5 * k1 - 4 / 5 * E * (3 / 10)) * ((2 + h) * (1 + h)) =
      3 / 5 * (k1 * (2 + h)) * (1 + h) - 6 / 25 * (E * (1 + h)) * (2 + h) := by ring
  rw [hk1] at h3
  have h3' : 6 / 25 * h ≤ (3 / 5 * k1 - 4 / 5 * E * (3 / 10)) * ((2 + h) * (1 + h)) := by
    rw [h3]
    nlinarith [mul_le_mul_of_nonneg_right hE (show (0 : ℝ) ≤ 2 + h by positivity)]
  have hD : h / 25 ≤ 3 / 5 * k1 - 4 / 5 * E * (3 / 10) := by
    by_contra hlt
    rw [not_le] at hlt
    have h7 := mul_lt_mul_of_pos_right hlt hpos
    nlinarith [mul_le_mul_of_nonneg_left h6 (show (0 : ℝ) ≤ h / 25 by positivity)]
  have hk1sq : k1 ^ 2 ≤ (2 / 5) ^ 2 := pow_le_pow_left₀ hk1pos.le hk1le 2
  have hγ4 : 4 * (a * (3 / 10) + b * k1) ^ 2 ≤ 1 := by
    rw [hγ]
    nlinarith
  have hD2 : (h / 25) ^ 2 ≤ (3 / 5 * k1 - 4 / 5 * E * (3 / 10)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hD 2
  have h8 := mul_le_mul_of_nonneg_left hγ4 (sq_nonneg (b * (3 / 5) - a * (4 / 5 * E)))
  have h9 : ((b * (3 / 5) - a * (4 / 5 * E)) * (a * (3 / 10) + b * k1)) ^ 2 =
      (b * (3 / 5) - a * (4 / 5 * E)) ^ 2 * (a * (3 / 10) + b * k1) ^ 2 := by ring
  rw [hq] at h9
  rw [hsplit]
  nlinarith [sq_nonneg (w - (a * (3 / 5) + b * (4 / 5 * E)))]

/-- **Every step from the perturbed start value misses the solution by `2h/25`.** Let
`0 < h ≤ 1` and `h lam s² = 1`. For every step of the matrix implicit BUG integrator for
`F(Z) = diag(0, -1) Z + Z diag(0, -lam)` with exact capture and without truncation, started
from `K₀ = U₀ S₀ = (3/5, 4/5)ᵀ` and `V₀ = (c, s)ᵀ`, the result `Y₁` satisfies

  `‖Y₁ - X(h)‖ ≥ 2h/25`,   `X(h) = (3/5, 4/5 e^{-h})ᵀ (1, 0)`. -/
theorem two_mul_div_le_norm_sub {h lam c s ε t₁ : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (ha : h * lam * s ^ 2 = 1) {S₀ S₁ : Matrix (Fin 1) (Fin 1) ℝ}
    {U₀ K₁ L₁ U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ} {Y₁ : Matrix (Fin 2) (Fin 2) ℝ}
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
      Mₛ * Z + Z * Nₛ lam) ε 0 0 t₁ h U₀ S₀ !![c; s] K₁ L₁ U₁ V₁ S₁ Y₁)
    (hK₀ : U₀ * S₀ = u₀) :
    2 * h / 25 ≤ ‖Y₁ - !![3 / 5, 0; 4 / 5 * Real.exp (-h), 0]‖ := by
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    have e := congrFun (congrFun hs.orthV₀ 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.transpose_apply,
      Matrix.one_apply_eq] at e
    simp at e
    linear_combination e
  -- the K-step
  have hk : K₁ =
      u₀ + h • ((Mₛ * (K₁ * !![c; s]ᵀ) + K₁ * !![c; s]ᵀ * Nₛ lam) * !![c; s]) := by
    have h0 := hs.kstep
    rwa [hK₀] at h0
  rw [field_mul_col] at hk
  have e0 : K₁ 0 0 = 3 / 5 + h * (-(lam * s ^ 2) * K₁ 0 0) := by
    simpa using congrFun (congrFun hk 0) 0
  have e1 : K₁ 1 0 = 4 / 5 + h * (-(c ^ 2 + s ^ 2) * K₁ 1 0 - lam * s ^ 2 * K₁ 1 0) := by
    simpa using congrFun (congrFun hk 1) 0
  have hk0 : K₁ 0 0 = 3 / 10 := by
    linear_combination (1 / 2 : ℝ) * e0 - K₁ 0 0 / 2 * ha
  have hk1 : K₁ 1 0 * (2 + h) = 4 / 5 := by
    linear_combination e1 - h * K₁ 1 0 * hcs - K₁ 1 0 * ha
  -- the capture
  have hcap0 : (1 - U₁ * U₁ᵀ) * (K₁ * !![c; s]ᵀ) = 0 := norm_le_zero_iff.1 hs.kcap
  have hcap : U₁ * (U₁ᵀ * K₁) = K₁ := by
    have e := congrArg (fun Z => Z * !![c; s]) hcap0
    simp only [Matrix.zero_mul, Matrix.mul_assoc, hs.orthV₀, Matrix.mul_one] at e
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at e
    rw [← Matrix.mul_assoc]
    exact e.symm
  have hab : U₁ 0 0 ^ 2 + U₁ 1 0 ^ 2 = 1 := by
    have e := congrFun (congrFun hs.orthU₁ 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.transpose_apply,
      Matrix.one_apply_eq] at e
    linear_combination e
  have c0 := congrFun (congrFun hcap 0) 0
  have c1 := congrFun (congrFun hcap 1) 0
  rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, Matrix.transpose_apply, hk0] at c0 c1
  -- the result of the step
  have hY : Y₁ = U₁ * (S₁ * V₁ᵀ) := by
    rw [← Matrix.mul_assoc]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 hs.trunc)
  have y0 : Y₁ 0 0 = U₁ 0 0 * (S₁ * V₁ᵀ) 0 0 := by
    rw [hY, Matrix.mul_apply, Fin.sum_univ_one]
  have y1 : Y₁ 1 0 = U₁ 1 0 * (S₁ * V₁ᵀ) 0 0 := by
    rw [hY, Matrix.mul_apply, Fin.sum_univ_one]
  have hE : Real.exp (-h) * (1 + h) ≤ 1 := by
    have h1 := Real.add_one_le_exp h
    have h2 : Real.exp (-h) * Real.exp h = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith [Real.exp_pos (-h)]
  have key := scalar_bound hh hh1 hab c0 c1 hk1 hE (w := (S₁ * V₁ᵀ) 0 0)
  have hn := sq_add_sq_le_norm_sq (Y₁ - !![3 / 5, 0; 4 / 5 * Real.exp (-h), 0])
  have d0 : (Y₁ - !![3 / 5, 0; 4 / 5 * Real.exp (-h), 0]) 0 0 =
      U₁ 0 0 * (S₁ * V₁ᵀ) 0 0 - 3 / 5 := by
    rw [Matrix.sub_apply, y0]
    simp
  have d1 : (Y₁ - !![3 / 5, 0; 4 / 5 * Real.exp (-h), 0]) 1 0 =
      U₁ 1 0 * (S₁ * V₁ᵀ) 0 0 - 4 / 5 * Real.exp (-h) := by
    rw [Matrix.sub_apply, y1]
    simp
  rw [d0, d1] at hn
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 (key.trans hn)

/-- **The start value is close to the solution.** For `c² + s² = 1` and `c ≥ 0`,
`‖(3/5, 4/5)ᵀ (c, s) - X(0)‖² ≤ 2 s²`. -/
theorem norm_start_sub_sq_le {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hc : 0 ≤ c) :
    ‖u₀ * !![c; s]ᵀ - !![3 / 5, 0; 4 / 5, 0]‖ ^ 2 ≤ 2 * s ^ 2 := by
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg s]
  rw [Frobenius.norm_sq_eq_sum]
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecHead, Function.swap]
  nlinarith [mul_nonneg hc (sub_nonneg.2 hc1)]

/-- **The reference is an exact solution.** `X(t) = (3/5, 4/5 e^{-t})ᵀ (1, 0)` solves
`Ẋ = diag(0, -1) X + X diag(0, -lam)` for every `lam`. -/
theorem odeSolution (lam a b : ℝ) :
    ODESolution (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) => Mₛ * Z + Z * Nₛ lam)
      (fun t : ℝ => !![3 / 5, 0; 4 / 5 * Real.exp (-t), 0]) a b := by
  have e : (fun t : ℝ =>
      (!![3 / 5, 0; 4 / 5 * Real.exp (-t), 0] : Matrix (Fin 2) (Fin 2) ℝ)) =
      fun t : ℝ => (!![3 / 5, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) +
        Real.exp (-t) • (!![0, 0; 4 / 5, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
    funext t
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]
  have hd : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => (!![3 / 5, 0; 4 / 5 * Real.exp (-t), 0] : Matrix (Fin 2) (Fin 2) ℝ))
      (Mₛ * !![3 / 5, 0; 4 / 5 * Real.exp (-t), 0] +
        !![3 / 5, 0; 4 / 5 * Real.exp (-t), 0] * Nₛ lam) t := by
    intro t
    have h1 := (((hasDerivAt_neg t).exp).smul_const
      (!![0, 0; 4 / 5, 0] : Matrix (Fin 2) (Fin 2) ℝ)).const_add
      (!![3 / 5, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
    rw [e]
    convert h1 using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  exact ⟨fun t _ => (hd t).continuousAt.continuousWithinAt,
    fun t _ => (hd t).hasDerivWithinAt⟩

/-- The Sylvester operator of the example is dissipative. -/
private theorem inner_sylvester_nonpos {lam : ℝ} (hlam : 0 ≤ lam)
    (z : Matrix (Fin 2) (Fin 2) ℝ) : ⟪Mₛ * z + z * Nₛ lam, z⟫ ≤ 0 := by
  have e : ⟪Mₛ * z + z * Nₛ lam, z⟫ =
      -(z 1 0 ^ 2 + z 1 1 ^ 2) - lam * (z 0 1 ^ 2 + z 1 1 ^ 2) := by
    norm_num [Frobenius.inner_def, Fin.sum_univ_two, Matrix.mul_apply, Matrix.vecMul,
      dotProduct]
    ring
  rw [e]
  nlinarith [sq_nonneg (z 1 0), sq_nonneg (z 1 1), sq_nonneg (z 0 1),
    mul_nonneg hlam (add_nonneg (sq_nonneg (z 0 1)) (sq_nonneg (z 1 1)))]

/-- A nonzero column, divided by its norm, is orthonormal and spans the column. -/
private theorem normalize_col {k : Matrix (Fin 2) (Fin 1) ℝ} (hk : k ≠ 0) :
    (‖k‖⁻¹ • k)ᵀ * (‖k‖⁻¹ • k) = 1 ∧ (‖k‖⁻¹ • k) * (‖k‖⁻¹ • k)ᵀ * k = k := by
  have hn : ‖k‖ ≠ 0 := norm_ne_zero_iff.2 hk
  have hkk : kᵀ * k = (‖k‖ ^ 2) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i
    fin_cases j
    rw [Frobenius.norm_sq_eq_sum]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have h1 : ‖k‖⁻¹ * ‖k‖⁻¹ * ‖k‖ ^ 2 = 1 := by
    field_simp
  constructor
  · rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hkk, smul_smul, h1,
      one_smul]
  · rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_mul,
      Matrix.mul_assoc, hkk, Matrix.mul_smul, Matrix.mul_one, smul_smul, h1, one_smul]

/-- **A step exists.** For `h ≥ 0`, `lam ≥ 0` and `c² + s² = 1` the matrix implicit BUG
integrator for `F(Z) = diag(0, -1) Z + Z diag(0, -lam)` has a step with exact capture and without
truncation from `U₀ = (3/5, 4/5)ᵀ`, `S₀ = 1`, `V₀ = (c, s)ᵀ`; no restriction on `h lam` is
needed. -/
theorem exists_isMatrixImplicitBUGStep {h lam c s : ℝ} (hh : 0 ≤ h) (hlam : 0 ≤ lam)
    (hcs : c ^ 2 + s ^ 2 = 1) (t₁ : ℝ) :
    ∃ (K₁ L₁ U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ) (S₁ : Matrix (Fin 1) (Fin 1) ℝ)
      (Y₁ : Matrix (Fin 2) (Fin 2) ℝ) (ε : ℝ),
      IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
        Mₛ * Z + Z * Nₛ lam) ε 0 0 t₁ h u₀ 1 !![c; s] K₁ L₁ U₁ V₁ S₁ Y₁ := by
  have hpa : 0 ≤ h * lam * s ^ 2 := mul_nonneg (mul_nonneg hh hlam) (sq_nonneg s)
  obtain ⟨k0, hk0⟩ : ∃ k0 : ℝ, k0 * (1 + h * lam * s ^ 2) = 3 / 5 :=
    ⟨_, div_mul_cancel₀ _ (by positivity)⟩
  obtain ⟨k1, hk1⟩ : ∃ k1 : ℝ, k1 * (1 + h + h * lam * s ^ 2) = 4 / 5 :=
    ⟨_, div_mul_cancel₀ _ (by positivity)⟩
  obtain ⟨l0, hl0⟩ : ∃ l0 : ℝ, l0 * (1 + 16 / 25 * h) = c :=
    ⟨_, div_mul_cancel₀ _ (by positivity)⟩
  obtain ⟨l1, hl1⟩ : ∃ l1 : ℝ, l1 * (1 + 16 / 25 * h + h * lam) = s :=
    ⟨_, div_mul_cancel₀ _ (by positivity)⟩
  have hK : (!![k0; k1] : Matrix (Fin 2) (Fin 1) ℝ) ≠ 0 := fun h0 => by
    have e : k0 = 0 := by simpa using congrFun (congrFun h0 0) 0
    rw [e] at hk0
    norm_num at hk0
  have hL : (!![l0; l1] : Matrix (Fin 2) (Fin 1) ℝ) ≠ 0 := fun h0 => by
    have e0 : l0 = 0 := by simpa using congrFun (congrFun h0 0) 0
    have e1 : l1 = 0 := by simpa using congrFun (congrFun h0 1) 0
    rw [e0] at hl0
    rw [e1] at hl1
    rw [← hl0, ← hl1] at hcs
    norm_num at hcs
  obtain ⟨hU₁, hU₁K⟩ := normalize_col hK
  obtain ⟨hV₁, hV₁L⟩ := normalize_col hL
  set U₁ : Matrix (Fin 2) (Fin 1) ℝ :=
    ‖(!![k0; k1] : Matrix (Fin 2) (Fin 1) ℝ)‖⁻¹ • !![k0; k1]
  set V₁ : Matrix (Fin 2) (Fin 1) ℝ :=
    ‖(!![l0; l1] : Matrix (Fin 2) (Fin 1) ℝ)‖⁻¹ • !![l0; l1]
  have hV₀ : (!![c; s] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * !![c; s] = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.transpose_apply]
    simp
    linear_combination hcs
  obtain ⟨xS, hxS, -⟩ := implicitGalerkin_existsUnique_affine
    (E := Matrix (Fin 2) (Fin 2) ℝ)
    (P := (leftProj U₁ * rightProj V₁ :
      Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ))
    (isOrthProj_leftProj_mul_rightProj hU₁ hV₁)
    (𝒜 := Frobenius.leftMulCLM Mₛ + Frobenius.rightMulCLM (Nₛ lam)) (g := 0) (μ := 0)
    (h := h)
    (fun z _ => by
      rw [zero_mul]
      exact inner_sylvester_nonpos hlam z) hh (by rw [mul_zero]; exact one_pos)
    (u₀ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * !![c; s]ᵀ)
  rw [add_zero] at hxS
  have hx2 : xS = leftProj U₁ (rightProj V₁
      (u₀ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * !![c; s]ᵀ + h • (Mₛ * xS + xS * Nₛ lam))) := hxS
  refine ⟨!![k0; k1], !![l0; l1], U₁, V₁,
    U₁ᵀ * (u₀ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * !![c; s]ᵀ +
      h • (Mₛ * xS + xS * Nₛ lam)) * V₁, xS,
    ‖(1 - U₁ * U₁ᵀ) *
        (Mₛ * (!![k0; k1] * !![c; s]ᵀ) + !![k0; k1] * !![c; s]ᵀ * Nₛ lam) *
        (1 - !![c; s] * !![c; s]ᵀ)‖ +
      ‖(1 - u₀ * u₀ᵀ) * (Mₛ * (u₀ * !![l0; l1]ᵀ) + u₀ * !![l0; l1]ᵀ * Nₛ lam) *
        (1 - V₁ * V₁ᵀ)‖, ?_⟩
  have hS : U₁ * (U₁ᵀ * (u₀ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * !![c; s]ᵀ +
      h • (Mₛ * xS + xS * Nₛ lam)) * V₁) * V₁ᵀ = xS :=
    ((matrix_sstep_iff hU₁ hV₁ _ _).2 rfl).trans hx2.symm
  exact
    { orthU₀ := by
        ext i j
        fin_cases i
        fin_cases j
        norm_num [Matrix.mul_apply, Fin.sum_univ_two]
      orthV₀ := hV₀
      kstep := by
        rw [Matrix.mul_one]
        rw [field_mul_col]
        ext i j
        fin_cases j
        fin_cases i
        · simp
          linear_combination hk0
        · simp
          linear_combination hk1 + h * k1 * hcs
      lstep := by
        rw [Matrix.transpose_one, Matrix.mul_one]
        rw [transpose_field_mul_col]
        ext i j
        fin_cases j
        fin_cases i
        · simp
          linear_combination hl0
        · simp
          linear_combination hl1
      orthU₁ := hU₁
      orthV₁ := hV₁
      kcap := by
        rw [← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hU₁K, sub_self, Matrix.zero_mul,
          norm_zero]
      lcap := by
        have e : (!![l0; l1] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * (V₁ * V₁ᵀ) = !![l0; l1]ᵀ := by
          have e1 := congrArg Matrix.transpose hV₁L
          rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at e1
        rw [Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, e, sub_self, Matrix.mul_zero,
          norm_zero]
      knormal := le_add_of_nonneg_right (norm_nonneg _)
      lnormal := le_add_of_nonneg_left (norm_nonneg _)
      sstep := by rw [hS]
      trunc := by rw [hS, sub_self, norm_zero] }

/-- **Non-vacuity of `IsMatrixImplicitBUGStep.norm_kstep_sub_le_of_sylvester_add` and
`IsMatrixImplicitBUGStep.norm_lstep_sub_le_of_sylvester_add` with an arbitrarily stiff part**,
and through them of the forms for `IsImplicitBUGStep` and of
`implicitGalerkin_compare_of_add` with projectors that do not commute with the stiff operator:
the steps of `exists_isMatrixImplicitBUGStep` for `M = diag(0, -1)`, `N = diag(0, -lam)`,
`G = 0` (`ℓ = 0`, `L = 0`), any `h ≥ 0`, `lam ≥ 0`, and any reference matrices `X₀`, `X₁`. -/
example {h lam c s : ℝ} (hh : 0 ≤ h) (hlam : 0 ≤ lam) (hcs : c ^ 2 + s ^ 2 = 1)
    (X₀ X₁ : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ K₁ L₁ : Matrix (Fin 2) (Fin 1) ℝ,
      (1 - h * 0) * ‖K₁ * !![c; s]ᵀ - X₁ * (!![c; s] * !![c; s]ᵀ)‖ ≤
        ‖u₀ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * !![c; s]ᵀ - X₀‖ +
          ‖(X₁ - X₀ - h • (Mₛ * X₁ + X₁ * (Nₛ lam) + 0)) * (!![c; s] * !![c; s]ᵀ)‖ +
          h * ‖X₁ * (1 - !![c; s] * !![c; s]ᵀ) * (Nₛ lam) * (!![c; s] * !![c; s]ᵀ)‖ +
          h * 0 * ‖X₁ - X₁ * (!![c; s] * !![c; s]ᵀ)‖ ∧
      (1 - h * 0) * ‖u₀ * L₁ᵀ - u₀ * u₀ᵀ * X₁‖ ≤
        ‖u₀ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * !![c; s]ᵀ - X₀‖ +
          ‖u₀ * u₀ᵀ * (X₁ - X₀ - h • (Mₛ * X₁ + X₁ * (Nₛ lam) + 0))‖ +
          h * ‖u₀ * u₀ᵀ * Mₛ * (1 - u₀ * u₀ᵀ) * X₁‖ + h * 0 * ‖X₁ - u₀ * u₀ᵀ * X₁‖ := by
  obtain ⟨K₁, L₁, U₁, V₁, S₁, Y₁, ε, hstep⟩ :=
    exists_isMatrixImplicitBUGStep hh hlam hcs 0
  have hstep' : IsMatrixImplicitBUGStep (fun (t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
      Mₛ * Z + Z * (Nₛ lam) + (fun _ _ => 0 : ℝ → Matrix (Fin 2) (Fin 2) ℝ →
        Matrix (Fin 2) (Fin 2) ℝ) t Z) ε 0 0 0 h u₀ 1 !![c; s] K₁ L₁ U₁ V₁ S₁ Y₁ := by
    simpa only [add_zero] using hstep
  have hℓ : IsOneSidedLipschitzField (fun (t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
      Mₛ * Z + Z * (Nₛ lam) + (fun _ _ => 0 : ℝ → Matrix (Fin 2) (Fin 2) ℝ →
        Matrix (Fin 2) (Fin 2) ℝ) t Z) 0 := fun _ x y => by
    have e : Mₛ * x + x * (Nₛ lam) + 0 - (Mₛ * y + y * (Nₛ lam) + 0) =
        Mₛ * (x - y) + (x - y) * (Nₛ lam) := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
      abel
    change ⟪Mₛ * x + x * (Nₛ lam) + 0 - (Mₛ * y + y * (Nₛ lam) + 0), x - y⟫ ≤ 0 * ‖x - y‖ ^ 2
    rw [e, zero_mul]
    exact inner_sylvester_nonpos hlam _
  exact ⟨K₁, L₁,
    hstep'.norm_kstep_sub_le_of_sylvester_add hh hℓ (fun _ _ _ => by simp) X₀ X₁,
    hstep'.norm_lstep_sub_le_of_sylvester_add hh hℓ (fun _ _ _ => by simp) X₀ X₁⟩

/-- **No one-step bound with constants that do not depend on the stiffness.** There are no
constants `C₁`, `C₂` with

  `‖Y₁ - X(h)‖ ≤ C₁ ‖Y₀ - X(0)‖ + C₂ h²`

for all steps `Y₀ → Y₁` of size `h ∈ (0, 1]` of the matrix implicit BUG integrator (rank `1`,
exact capture, no truncation) for the fields `F(Z) = diag(0, -1) Z + Z diag(0, -lam)`,
`lam ≥ 0`, from the start values `Y₀ = (3/5, 4/5)ᵀ (c, s)`, `c ≥ 0`: here
`X(t) = (3/5, 4/5 e^{-t})ᵀ (1, 0)` is an exact solution of rank `1` for every `lam`, and the
fields are linear with the one-sided Lipschitz constant `0`. -/
theorem not_exists_forall_norm_sub_le :
    ¬ ∃ C₁ C₂ : ℝ, ∀ (h lam c s ε t₁ : ℝ) (S₁ : Matrix (Fin 1) (Fin 1) ℝ)
      (K₁ L₁ U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ) (Y₁ : Matrix (Fin 2) (Fin 2) ℝ),
      0 < h → h ≤ 1 → 0 ≤ lam → 0 ≤ c →
      IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
        Mₛ * Z + Z * Nₛ lam) ε 0 0 t₁ h u₀ 1 !![c; s] K₁ L₁ U₁ V₁ S₁ Y₁ →
      ‖Y₁ - !![3 / 5, 0; 4 / 5 * Real.exp (-h), 0]‖ ≤
        C₁ * ‖u₀ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * !![c; s]ᵀ - !![3 / 5, 0; 4 / 5, 0]‖ +
          C₂ * h ^ 2 := by
  rintro ⟨C₁, C₂, H⟩
  have hD₁ : 0 < |C₁| + 1 := by positivity
  have hD₂ : 0 < |C₂| + 1 := by positivity
  set h : ℝ := 1 / (25 * (|C₂| + 1)) with hh_def
  have hh : 0 < h := by positivity
  have hh1 : h ≤ 1 := by
    rw [hh_def, div_le_one (by positivity)]
    nlinarith [abs_nonneg C₂]
  set p : ℝ := h / (200 * (|C₁| + 1)) with hp_def
  have hp : 0 < p := by positivity
  have hp1 : p ≤ 1 := by
    rw [hp_def, div_le_one (by positivity)]
    nlinarith [abs_nonneg C₁]
  set c : ℝ := (1 - p ^ 2) / (1 + p ^ 2) with hc_def
  set s : ℝ := 2 * p / (1 + p ^ 2) with hs_def
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    rw [hc_def, hs_def]
    field_simp
    ring
  have hc : 0 ≤ c := div_nonneg (by nlinarith) (by positivity)
  have hs0 : 0 < s := by positivity
  have hs2 : s ≤ 2 * p := by
    rw [hs_def, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg p]
  have hlam : 0 ≤ 1 / (h * s ^ 2) := by positivity
  have ha : h * (1 / (h * s ^ 2)) * s ^ 2 = 1 := by
    field_simp
  obtain ⟨K₁, L₁, U₁, V₁, S₁, Y₁, ε, hstep⟩ :=
    exists_isMatrixImplicitBUGStep hh.le hlam hcs 0
  have hlow := two_mul_div_le_norm_sub hh hh1 ha hstep (Matrix.mul_one _)
  have hup := H h (1 / (h * s ^ 2)) c s ε 0 S₁ K₁ L₁ U₁ V₁ Y₁ hh hh1 hlam hc hstep
  rw [Matrix.mul_one] at hup
  have he0 := norm_start_sub_sq_le hcs hc
  have he : ‖u₀ * !![c; s]ᵀ - !![3 / 5, 0; 4 / 5, 0]‖ ≤ 2 * s :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (by nlinarith)
  have h1 : C₁ * ‖u₀ * !![c; s]ᵀ - !![3 / 5, 0; 4 / 5, 0]‖ ≤ (|C₁| + 1) * (4 * p) := by
    have h2 : C₁ ≤ |C₁| + 1 := by linarith [le_abs_self C₁]
    calc C₁ * ‖u₀ * !![c; s]ᵀ - !![3 / 5, 0; 4 / 5, 0]‖
        ≤ (|C₁| + 1) * ‖u₀ * !![c; s]ᵀ - !![3 / 5, 0; 4 / 5, 0]‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ (|C₁| + 1) * (4 * p) := mul_le_mul_of_nonneg_left (by linarith) hD₁.le
  have h3 : (|C₁| + 1) * (4 * p) = h / 50 := by
    rw [hp_def]
    field_simp
    ring
  have h4 : C₂ * h ^ 2 ≤ h / 25 := by
    have h5 : (|C₂| + 1) * h ^ 2 = h / 25 := by
      rw [hh_def]
      field_simp
    have h6 : C₂ ≤ |C₂| + 1 := by linarith [le_abs_self C₂]
    nlinarith [sq_nonneg h]
  linarith

end StiffRowsExample

end LeanDLRA
