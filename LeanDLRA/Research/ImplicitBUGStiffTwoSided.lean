import LeanDLRA.Research.ImplicitBUGStiffRows

/-!
# Stiffness on both sides: one implicit BUG step can lose a fixed part of the solution

For the fixed-rank BUG integrator with backward Euler substeps and the field `F(Z) = N Z + Z N`
with the same stiff matrix on both sides, the stiff energy of the numerical COLUMN basis reduces
the effective step size of the L-step, so that a rough component of the row basis is not damped
by the full resolvent; the S-step then damps the whole component of the solution along this row
vector. This file has an explicit family for `2 × 2` matrices and rank `1`:

  `N = diag(0, -lam)`,  `X(t) = diag(1, 0)` (stationary),  `Y₀ = (c, s)ᵀ (c, s)`,
  `c² + s² = 1`,  `h lam s⁶ = 1`.

`X` is an exact solution of rank `1` with singular value `1`, the field is linear and
dissipative, `‖Y₀ - X‖² = 2 s² = 2 (h lam)^{-1/3}`, and every step of the integrator from `Y₀`
has `‖Y₁ - X‖ ≥ 1/11`, for every step size `h > 0`. So no bound

  `‖Y₁ - X‖ ≤ C₁ ‖Y₀ - X‖ + C₂ h`

holds with constants that do not depend on `lam`: the loss does not vanish with the step size.
With stiffness on one side only and the rows of the reference in the kernel of the stiff matrix,
the loss of a step is at most `2 h μ ‖Y₀‖`
(`IsMatrixImplicitBUGStep.norm_mul_sub_le_of_sylvester`).

## Main results

* `StiffTwoSidedExample.one_div_le_norm_sub`: `‖Y₁ - X‖ ≥ 1/11` for every step.
* `StiffTwoSidedExample.norm_start_sub_sq`: `‖Y₀ - X‖² = 2 s²`.
* `StiffTwoSidedExample.field_stationary`: `N X + X N = 0`.
* `StiffTwoSidedExample.exists_isMatrixImplicitBUGStep`: a step exists for every `h ≥ 0`,
  `lam ≥ 0`.
* `StiffTwoSidedExample.not_exists_forall_norm_sub_le`: there are no constants `C₁`, `C₂` as
  above.

## Implementation notes

With `a = h lam s²` and `p = h lam` the L-step gives `L₁ = (c/(1 + a), s/(1 + a + p))`, the new
row basis `(x, y)` is parallel to `L₁`, and the S-step gives
`S₁ (1 + p b² + p y²) = (U₁ · U₀)(V₀ · V₁)` with `U₁ = (a₁, b)`. From `a³ = p²` one gets
`p y² ≥ 1/10`, hence `|S₁| ≤ 10/11`.

## References

* [CerutiLubich2022] for the BUG integrator; backward Euler substeps as in arXiv 2610.18419.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA

namespace StiffTwoSidedExample

/-- The stiff matrix `diag(0, -lam)`, acting on the columns and on the rows. -/
local notation "Nₜ" lam => (!![0, 0; 0, -lam] : Matrix (Fin 2) (Fin 2) ℝ)

/-- The stationary solution `diag(1, 0)`. -/
local notation "Xₜ" => (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)

/-- The field applied to the K-stage, times the old row basis. -/
private theorem field_mul_col (lam c s : ℝ) (K : Matrix (Fin 2) (Fin 1) ℝ) :
    ((Nₜ lam) * (K * !![c; s]ᵀ) + K * !![c; s]ᵀ * Nₜ lam) * !![c; s] =
      !![-(lam * s ^ 2) * K 0 0; -(lam * (c ^ 2 + s ^ 2)) * K 1 0 - lam * s ^ 2 * K 1 0] := by
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
private theorem transpose_field_mul_col (lam c s : ℝ) (L : Matrix (Fin 2) (Fin 1) ℝ) :
    ((Nₜ lam) * (!![c; s] * Lᵀ) + !![c; s] * Lᵀ * Nₜ lam)ᵀ * !![c; s] =
      !![-(lam * s ^ 2) * L 0 0; -(lam * (c ^ 2 + s ^ 2)) * L 1 0 - lam * s ^ 2 * L 1 0] := by
  ext i j
  fin_cases j
  fin_cases i
  · norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, Matrix.vecHead,
      Function.swap]
    ring
  · norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, Matrix.vecHead,
      Function.swap]
    ring

/-- The entry of the Galerkin step. -/
private theorem sstep_entry (h lam c s : ℝ) (U V : Matrix (Fin 2) (Fin 1) ℝ)
    (S : Matrix (Fin 1) (Fin 1) ℝ) :
    (Uᵀ * (!![c; s] * (1 : Matrix (Fin 1) (Fin 1) ℝ) * !![c; s]ᵀ +
      h • ((Nₜ lam) * (U * S * Vᵀ) + U * S * Vᵀ * Nₜ lam)) * V) 0 0 =
      (U 0 0 * c + U 1 0 * s) * (c * V 0 0 + s * V 1 0) -
        h * lam * U 1 0 ^ 2 * S 0 0 * (V 0 0 ^ 2 + V 1 0 ^ 2) -
        h * lam * (U 0 0 ^ 2 + U 1 0 ^ 2) * S 0 0 * V 1 0 ^ 2 := by
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, Matrix.vecHead,
    Function.swap]
  ring

/-- The scalar core of the lower bound: with `a = p s²`, `p s⁶ = 1`, the new row basis has
`p y² ≥ 1/10`, and the entry of the result is at most `10/11`. -/
private theorem scalar_bound {p c s l0 l1 y σ w : ℝ} (hp : p * s ^ 6 = 1)
    (hcs : c ^ 2 + s ^ 2 = 1) (hl0 : l0 * (1 + p * s ^ 2) = c)
    (hl1 : l1 * (1 + p * s ^ 2 + p) = s) (hy : y ^ 2 * (l0 ^ 2 + l1 ^ 2) = l1 ^ 2)
    (hσ : σ ^ 2 * (1 + p * y ^ 2) ^ 2 ≤ 1) (hw : w ^ 2 ≤ σ ^ 2) : w ≤ 10 / 11 := by
  have hs6 : 0 ≤ s ^ 6 := by positivity
  have hs2 : s ^ 2 ≤ 1 := by linarith [sq_nonneg c]
  have hs20 : 0 ≤ s ^ 2 := sq_nonneg s
  have hs61 : s ^ 6 ≤ 1 := by
    have : s ^ 6 = (s ^ 2) ^ 3 := by ring
    rw [this]
    exact pow_le_one₀ hs20 hs2
  have hp0 : 0 < p := by
    by_contra hneg
    rw [not_lt] at hneg
    have := mul_nonneg (neg_nonneg.2 hneg) hs6
    linarith
  have hp1 : 1 ≤ p := by
    have := mul_le_mul_of_nonneg_left hs61 hp0.le
    linarith
  obtain ⟨a, ha⟩ : ∃ a, a = p * s ^ 2 := ⟨_, rfl⟩
  rw [← ha] at hl0 hl1
  have ha0 : 0 ≤ a := by rw [ha]; exact mul_nonneg hp0.le hs20
  have hap : a ≤ p := by
    have := mul_le_mul_of_nonneg_left hs2 hp0.le
    rw [ha]; linarith
  have ha3 : a ^ 3 = p ^ 2 := by
    rw [ha]
    linear_combination p ^ 2 * hp
  -- `(10 p - 1) l1² ≥ l0²`
  have hA : 0 < 1 + a := by linarith
  have hB : 0 < 1 + a + p := by linarith
  have hpoly : c ^ 2 * (1 + a + p) ^ 2 ≤ (10 * p - 1) * s ^ 2 * (1 + a) ^ 2 := by
    have h1 : (1 + a + p) ^ 2 ≤ (3 * p) ^ 2 := pow_le_pow_left₀ hB.le (by linarith) 2
    have hc1 : c ^ 2 ≤ 1 := by linarith
    have h2 : c ^ 2 * (1 + a + p) ^ 2 ≤ 1 * (1 + a + p) ^ 2 :=
      mul_le_mul_of_nonneg_right hc1 (sq_nonneg _)
    have h3 : 9 * p * (s ^ 2 * a ^ 2) = (3 * p) ^ 2 := by
      have : p * (s ^ 2 * a ^ 2) = a ^ 3 := by rw [ha]; ring
      linear_combination 9 * this + 9 * ha3
    have h4 : a ^ 2 ≤ (1 + a) ^ 2 := pow_le_pow_left₀ ha0 (by linarith) 2
    have h5 : 9 * p * (s ^ 2 * a ^ 2) ≤ 9 * p * (s ^ 2 * (1 + a) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hs20) (by linarith)
    have h6 : 9 * p * (s ^ 2 * (1 + a) ^ 2) ≤ (10 * p - 1) * (s ^ 2 * (1 + a) ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hs20 (sq_nonneg _))
    calc c ^ 2 * (1 + a + p) ^ 2 ≤ (3 * p) ^ 2 := by linarith
      _ ≤ (10 * p - 1) * (s ^ 2 * (1 + a) ^ 2) := by linarith
      _ = (10 * p - 1) * s ^ 2 * (1 + a) ^ 2 := by ring
  have hl : l0 ^ 2 ≤ (10 * p - 1) * l1 ^ 2 := by
    have hD : 0 < (1 + a) ^ 2 * (1 + a + p) ^ 2 := by positivity
    have e : (l0 ^ 2) * ((1 + a) ^ 2 * (1 + a + p) ^ 2) ≤
        ((10 * p - 1) * l1 ^ 2) * ((1 + a) ^ 2 * (1 + a + p) ^ 2) := by
      have e1 : (l0 ^ 2) * ((1 + a) ^ 2 * (1 + a + p) ^ 2) = c ^ 2 * (1 + a + p) ^ 2 := by
        rw [← hl0]; ring
      have e2 : ((10 * p - 1) * l1 ^ 2) * ((1 + a) ^ 2 * (1 + a + p) ^ 2) =
          (10 * p - 1) * s ^ 2 * (1 + a) ^ 2 := by
        rw [← hl1]; ring
      rw [e1, e2]
      exact hpoly
    exact le_of_mul_le_mul_right e hD
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hp
    norm_num at hp
  have hl1ne : l1 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hl1
    exact hs0 hl1.symm
  have hl1pos : 0 < l1 ^ 2 := by positivity
  have hpy : 1 / 10 ≤ p * y ^ 2 := by
    have hsum : 0 < l0 ^ 2 + l1 ^ 2 := by positivity
    have e : (1 / 10) * (l0 ^ 2 + l1 ^ 2) ≤ (p * y ^ 2) * (l0 ^ 2 + l1 ^ 2) := by
      have : p * y ^ 2 * (l0 ^ 2 + l1 ^ 2) = p * l1 ^ 2 := by
        linear_combination p * hy
      rw [this]
      linarith
    exact le_of_mul_le_mul_right e hsum
  by_contra hc
  rw [not_le] at hc
  have h1 : (10 / 11 : ℝ) ^ 2 < w ^ 2 := by nlinarith
  have h2 : (11 / 10 : ℝ) ^ 2 ≤ (1 + p * y ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 2
  nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg σ)]

/-- **Every step from the perturbed start value loses a fixed part of the solution.** Let
`h lam s⁶ = 1`. For every step of the matrix implicit BUG integrator for
`F(Z) = N Z + Z N`, `N = diag(0, -lam)`, with exact capture and without truncation, started from
`Y₀ = (c, s)ᵀ (c, s)`, the result `Y₁` satisfies `‖Y₁ - diag(1, 0)‖ ≥ 1/11`. -/
theorem one_div_le_norm_sub {h lam c s ε t₁ : ℝ} (ha : h * lam * s ^ 6 = 1)
    {S₁ : Matrix (Fin 1) (Fin 1) ℝ} {K₁ L₁ U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ}
    {Y₁ : Matrix (Fin 2) (Fin 2) ℝ}
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
      (Nₜ lam) * Z + Z * Nₜ lam) ε 0 0 t₁ h !![c; s] 1 !![c; s] K₁ L₁ U₁ V₁ S₁ Y₁) :
    1 / 11 ≤ ‖Y₁ - Xₜ‖ := by
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    have e := congrFun (congrFun hs.orthV₀ 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.transpose_apply,
      Matrix.one_apply_eq] at e
    simp at e
    linear_combination e
  -- the L-step
  have hl := hs.lstep
  rw [Matrix.transpose_one, Matrix.mul_one, transpose_field_mul_col] at hl
  have e0 : L₁ 0 0 = c + h * (-(lam * s ^ 2) * L₁ 0 0) := by
    simpa using congrFun (congrFun hl 0) 0
  have e1 : L₁ 1 0 = s + h * (-(lam * (c ^ 2 + s ^ 2)) * L₁ 1 0 - lam * s ^ 2 * L₁ 1 0) := by
    simpa using congrFun (congrFun hl 1) 0
  have hl0 : L₁ 0 0 * (1 + h * lam * s ^ 2) = c := by linear_combination e0
  have hl1 : L₁ 1 0 * (1 + h * lam * s ^ 2 + h * lam) = s := by
    linear_combination e1 - h * lam * L₁ 1 0 * hcs
  -- the capture of the L-step
  have hcap0 : !![c; s] * L₁ᵀ * (1 - V₁ * V₁ᵀ) = 0 := norm_le_zero_iff.1 hs.lcap
  have hcap : V₁ * (V₁ᵀ * L₁) = L₁ := by
    have e := congrArg (fun Z => !![c; s]ᵀ * Z) hcap0
    simp only [Matrix.mul_zero, ← Matrix.mul_assoc, hs.orthU₀, Matrix.one_mul] at e
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at e
    have e' := congrArg Matrix.transpose e
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose] at e'
    rw [← Matrix.mul_assoc]
    exact e'.symm
  have hxy : V₁ 0 0 ^ 2 + V₁ 1 0 ^ 2 = 1 := by
    have e := congrFun (congrFun hs.orthV₁ 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.transpose_apply,
      Matrix.one_apply_eq] at e
    linear_combination e
  have hab : U₁ 0 0 ^ 2 + U₁ 1 0 ^ 2 = 1 := by
    have e := congrFun (congrFun hs.orthU₁ 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.transpose_apply,
      Matrix.one_apply_eq] at e
    linear_combination e
  have c0 := congrFun (congrFun hcap 0) 0
  have c1 := congrFun (congrFun hcap 1) 0
  rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, Matrix.transpose_apply] at c0 c1
  have hy : V₁ 1 0 ^ 2 * (L₁ 0 0 ^ 2 + L₁ 1 0 ^ 2) = L₁ 1 0 ^ 2 := by
    have hγ : (V₁ 0 0 * L₁ 0 0 + V₁ 1 0 * L₁ 1 0) ^ 2 = L₁ 0 0 ^ 2 + L₁ 1 0 ^ 2 := by
      linear_combination L₁ 0 0 * c0 + L₁ 1 0 * c1
    rw [← hγ]
    linear_combination (V₁ 1 0 * (V₁ 0 0 * L₁ 0 0 + V₁ 1 0 * L₁ 1 0) + L₁ 1 0) * c1
  -- the S-step
  have hS0 := hs.sstep
  beta_reduce at hS0
  have hS := congrFun (congrFun hS0 0) 0
  rw [sstep_entry, hxy, hab] at hS
  have hp0 : 0 ≤ h * lam := by
    by_contra hneg
    rw [not_le] at hneg
    have := mul_nonneg (neg_nonneg.2 hneg.le) (by positivity : (0 : ℝ) ≤ s ^ 6)
    linarith
  have hσ : S₁ 0 0 ^ 2 * (1 + h * lam * V₁ 1 0 ^ 2) ^ 2 ≤ 1 := by
    have hS' : S₁ 0 0 * (1 + h * lam * U₁ 1 0 ^ 2 + h * lam * V₁ 1 0 ^ 2) =
        (U₁ 0 0 * c + U₁ 1 0 * s) * (c * V₁ 0 0 + s * V₁ 1 0) := by linear_combination hS
    have h1 : (U₁ 0 0 * c + U₁ 1 0 * s) ^ 2 ≤ 1 := by
      have : (U₁ 0 0 * c + U₁ 1 0 * s) ^ 2 = 1 - (U₁ 0 0 * s - U₁ 1 0 * c) ^ 2 := by
        linear_combination (U₁ 0 0 ^ 2 + U₁ 1 0 ^ 2) * hcs + hab
      linarith [sq_nonneg (U₁ 0 0 * s - U₁ 1 0 * c)]
    have h2 : (c * V₁ 0 0 + s * V₁ 1 0) ^ 2 ≤ 1 := by
      have : (c * V₁ 0 0 + s * V₁ 1 0) ^ 2 = 1 - (c * V₁ 1 0 - s * V₁ 0 0) ^ 2 := by
        linear_combination (V₁ 0 0 ^ 2 + V₁ 1 0 ^ 2) * hcs + hxy
      linarith [sq_nonneg (c * V₁ 1 0 - s * V₁ 0 0)]
    have h3 : (S₁ 0 0 * (1 + h * lam * U₁ 1 0 ^ 2 + h * lam * V₁ 1 0 ^ 2)) ^ 2 ≤ 1 := by
      rw [hS', mul_pow]
      exact (mul_le_mul h1 h2 (sq_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have hy0 : 0 ≤ h * lam * V₁ 1 0 ^ 2 := mul_nonneg hp0 (sq_nonneg _)
    have hb0 : 0 ≤ h * lam * U₁ 1 0 ^ 2 := mul_nonneg hp0 (sq_nonneg _)
    have h4 : (1 + h * lam * V₁ 1 0 ^ 2) ^ 2 ≤
        (1 + h * lam * U₁ 1 0 ^ 2 + h * lam * V₁ 1 0 ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc S₁ 0 0 ^ 2 * (1 + h * lam * V₁ 1 0 ^ 2) ^ 2
        ≤ S₁ 0 0 ^ 2 * (1 + h * lam * U₁ 1 0 ^ 2 + h * lam * V₁ 1 0 ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left h4 (sq_nonneg _)
      _ = (S₁ 0 0 * (1 + h * lam * U₁ 1 0 ^ 2 + h * lam * V₁ 1 0 ^ 2)) ^ 2 := by ring
      _ ≤ 1 := h3
  -- the result of the step
  have hY : Y₁ = U₁ * S₁ * V₁ᵀ := sub_eq_zero.1 (norm_le_zero_iff.1 hs.trunc)
  have y0 : Y₁ 0 0 = U₁ 0 0 * S₁ 0 0 * V₁ 0 0 := by
    rw [hY, Matrix.mul_apply, Fin.sum_univ_one, Matrix.mul_apply, Fin.sum_univ_one,
      Matrix.transpose_apply]
  have hw : Y₁ 0 0 ^ 2 ≤ S₁ 0 0 ^ 2 := by
    have hu : U₁ 0 0 ^ 2 ≤ 1 := by linarith [sq_nonneg (U₁ 1 0)]
    have hv : V₁ 0 0 ^ 2 ≤ 1 := by linarith [sq_nonneg (V₁ 1 0)]
    have : Y₁ 0 0 ^ 2 = U₁ 0 0 ^ 2 * V₁ 0 0 ^ 2 * S₁ 0 0 ^ 2 := by rw [y0]; ring
    rw [this]
    exact mul_le_of_le_one_left (sq_nonneg _)
      ((mul_le_mul hu hv (sq_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have key := scalar_bound (p := h * lam) ha hcs hl0 hl1 hy hσ hw
  have hn := Frobenius.abs_apply_le_norm (Y₁ - Xₜ) 0 0
  have d0 : (Y₁ - Xₜ) 0 0 = Y₁ 0 0 - 1 := by
    rw [Matrix.sub_apply]
    simp
  rw [d0] at hn
  have := neg_abs_le (Y₁ 0 0 - 1)
  linarith

/-- **The start value is close to the solution**: `‖(c, s)ᵀ (c, s) - diag(1, 0)‖² = 2 s²` for
`c² + s² = 1`. -/
theorem norm_start_sub_sq {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    ‖(!![c; s] : Matrix (Fin 2) (Fin 1) ℝ) * !![c; s]ᵀ - Xₜ‖ ^ 2 = 2 * s ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecHead, Function.swap]
  have hc : c ^ 2 = 1 - s ^ 2 := by linarith
  have : (c * c - 1) ^ 2 + (c * s) ^ 2 + ((s * c) ^ 2 + (s * s) ^ 2) = 2 * s ^ 2 := by
    have e1 : c * c = 1 - s ^ 2 := by rw [← hc]; ring
    rw [e1]
    have e2 : (c * s) ^ 2 = (1 - s ^ 2) * s ^ 2 := by rw [← hc]; ring
    have e3 : (s * c) ^ 2 = (1 - s ^ 2) * s ^ 2 := by rw [← hc]; ring
    rw [e2, e3]
    ring
  linarith

/-- **The reference is stationary**: `N diag(1, 0) + diag(1, 0) N = 0` for `N = diag(0, -lam)`. -/
theorem field_stationary (lam : ℝ) : (Nₜ lam) * Xₜ + Xₜ * (Nₜ lam) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The Sylvester operator of the example is dissipative. -/
private theorem inner_sylvester_nonpos {lam : ℝ} (hlam : 0 ≤ lam)
    (z : Matrix (Fin 2) (Fin 2) ℝ) : ⟪(Nₜ lam) * z + z * (Nₜ lam), z⟫ ≤ 0 := by
  have e : ⟪(Nₜ lam) * z + z * (Nₜ lam), z⟫ =
      -(lam * (z 1 0 ^ 2 + z 1 1 ^ 2)) - lam * (z 0 1 ^ 2 + z 1 1 ^ 2) := by
    norm_num [Frobenius.inner_def, Fin.sum_univ_two, Matrix.mul_apply, Matrix.vecMul,
      dotProduct]
    ring
  rw [e]
  nlinarith [mul_nonneg hlam (add_nonneg (sq_nonneg (z 1 0)) (sq_nonneg (z 1 1))),
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
integrator for `F(Z) = N Z + Z N`, `N = diag(0, -lam)`, has a step with exact capture and
without truncation from `U₀ = V₀ = (c, s)ᵀ`, `S₀ = 1`; no restriction on `h lam` is needed. -/
theorem exists_isMatrixImplicitBUGStep {h lam c s : ℝ} (hh : 0 ≤ h) (hlam : 0 ≤ lam)
    (hcs : c ^ 2 + s ^ 2 = 1) (t₁ : ℝ) :
    ∃ (K₁ L₁ U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ) (S₁ : Matrix (Fin 1) (Fin 1) ℝ)
      (Y₁ : Matrix (Fin 2) (Fin 2) ℝ) (ε : ℝ),
      IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
        (Nₜ lam) * Z + Z * (Nₜ lam)) ε 0 0 t₁ h !![c; s] 1 !![c; s] K₁ L₁ U₁ V₁ S₁ Y₁ := by
  have hpa : 0 ≤ h * lam * s ^ 2 := mul_nonneg (mul_nonneg hh hlam) (sq_nonneg s)
  have hp : 0 ≤ h * lam := mul_nonneg hh hlam
  obtain ⟨l0, hl0⟩ : ∃ l0 : ℝ, l0 * (1 + h * lam * s ^ 2) = c :=
    ⟨_, div_mul_cancel₀ _ (by positivity)⟩
  obtain ⟨l1, hl1⟩ : ∃ l1 : ℝ, l1 * (1 + h * lam * s ^ 2 + h * lam) = s :=
    ⟨_, div_mul_cancel₀ _ (by positivity)⟩
  have hL : (!![l0; l1] : Matrix (Fin 2) (Fin 1) ℝ) ≠ 0 := fun h0 => by
    have e0 : l0 = 0 := by simpa using congrFun (congrFun h0 0) 0
    have e1 : l1 = 0 := by simpa using congrFun (congrFun h0 1) 0
    rw [e0] at hl0
    rw [e1] at hl1
    rw [← hl0, ← hl1] at hcs
    norm_num at hcs
  obtain ⟨hV₁, hV₁L⟩ := normalize_col hL
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
    (P := (leftProj V₁ * rightProj V₁ :
      Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ))
    (isOrthProj_leftProj_mul_rightProj hV₁ hV₁)
    (𝒜 := Frobenius.leftMulCLM (Nₜ lam) + Frobenius.rightMulCLM (Nₜ lam)) (g := 0) (μ := 0)
    (h := h)
    (fun z _ => by
      rw [zero_mul]
      exact inner_sylvester_nonpos hlam z) hh (by rw [mul_zero]; exact one_pos)
    ((!![c; s] : Matrix (Fin 2) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) * !![c; s]ᵀ)
  rw [add_zero] at hxS
  have hx2 : xS = leftProj V₁ (rightProj V₁
      ((!![c; s] : Matrix (Fin 2) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) * !![c; s]ᵀ +
        h • ((Nₜ lam) * xS + xS * (Nₜ lam)))) := hxS
  refine ⟨!![l0; l1], !![l0; l1], V₁, V₁,
    V₁ᵀ * ((!![c; s] : Matrix (Fin 2) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) * !![c; s]ᵀ +
      h • ((Nₜ lam) * xS + xS * (Nₜ lam))) * V₁, xS,
    ‖(1 - V₁ * V₁ᵀ) *
        ((Nₜ lam) * (!![l0; l1] * !![c; s]ᵀ) + !![l0; l1] * !![c; s]ᵀ * (Nₜ lam)) *
        (1 - !![c; s] * !![c; s]ᵀ)‖ +
      ‖(1 - !![c; s] * !![c; s]ᵀ) *
        ((Nₜ lam) * (!![c; s] * !![l0; l1]ᵀ) + !![c; s] * !![l0; l1]ᵀ * (Nₜ lam)) *
        (1 - V₁ * V₁ᵀ)‖, ?_⟩
  have hS : V₁ * (V₁ᵀ * ((!![c; s] : Matrix (Fin 2) (Fin 1) ℝ) *
      (1 : Matrix (Fin 1) (Fin 1) ℝ) * !![c; s]ᵀ +
      h • ((Nₜ lam) * xS + xS * (Nₜ lam))) * V₁) * V₁ᵀ = xS :=
    ((matrix_sstep_iff hV₁ hV₁ _ _).2 rfl).trans hx2.symm
  exact
    { orthU₀ := hV₀
      orthV₀ := hV₀
      kstep := by
        rw [Matrix.mul_one]
        rw [field_mul_col]
        ext i j
        fin_cases j
        fin_cases i
        · simp
          linear_combination hl0
        · simp
          linear_combination hl1 + h * lam * l1 * hcs
      lstep := by
        rw [Matrix.transpose_one, Matrix.mul_one]
        rw [transpose_field_mul_col]
        ext i j
        fin_cases j
        fin_cases i
        · simp
          linear_combination hl0
        · simp
          linear_combination hl1 + h * lam * l1 * hcs
      orthU₁ := hV₁
      orthV₁ := hV₁
      kcap := by
        rw [← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hV₁L, sub_self, Matrix.zero_mul,
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

/-- **No one-step bound with constants that do not depend on the stiffness, not even of order
zero in the step size.** There are no constants `C₁`, `C₂` with

  `‖Y₁ - X‖ ≤ C₁ ‖Y₀ - X‖ + C₂ h`

for all steps `Y₀ → Y₁` of size `h ∈ (0, 1]` of the matrix implicit BUG integrator (rank `1`,
exact capture, no truncation) for the fields `F(Z) = N Z + Z N`, `N = diag(0, -lam)`, `lam ≥ 0`,
from the start values `Y₀ = (c, s)ᵀ (c, s)`: here `X = diag(1, 0)` is a stationary solution of
rank `1` for every `lam`, and the fields are linear and dissipative. -/
theorem not_exists_forall_norm_sub_le :
    ¬ ∃ C₁ C₂ : ℝ, ∀ (h lam c s ε t₁ : ℝ) (S₁ : Matrix (Fin 1) (Fin 1) ℝ)
      (K₁ L₁ U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ) (Y₁ : Matrix (Fin 2) (Fin 2) ℝ),
      0 < h → h ≤ 1 → 0 ≤ lam →
      IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
        (Nₜ lam) * Z + Z * (Nₜ lam)) ε 0 0 t₁ h !![c; s] 1 !![c; s] K₁ L₁ U₁ V₁ S₁ Y₁ →
      ‖Y₁ - Xₜ‖ ≤ C₁ * ‖(!![c; s] : Matrix (Fin 2) (Fin 1) ℝ) *
        (1 : Matrix (Fin 1) (Fin 1) ℝ) * !![c; s]ᵀ - Xₜ‖ + C₂ * h := by
  rintro ⟨C₁, C₂, H⟩
  have hD₁ : 0 < |C₁| + 1 := by positivity
  have hD₂ : 0 < |C₂| + 1 := by positivity
  set h : ℝ := 1 / (44 * (|C₂| + 1)) with hh_def
  have hh : 0 < h := by positivity
  have hh1 : h ≤ 1 := by
    rw [hh_def, div_le_one (by positivity)]
    nlinarith [abs_nonneg C₂]
  set p : ℝ := 1 / (176 * (|C₁| + 1)) with hp_def
  have hp : 0 < p := by positivity
  set c : ℝ := (1 - p ^ 2) / (1 + p ^ 2) with hc_def
  set s : ℝ := 2 * p / (1 + p ^ 2) with hs_def
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    rw [hc_def, hs_def]
    field_simp
    ring
  have hs0 : 0 < s := by positivity
  have hs2 : s ≤ 2 * p := by
    rw [hs_def, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg p]
  have hlam : 0 ≤ 1 / (h * s ^ 6) := by positivity
  have ha : h * (1 / (h * s ^ 6)) * s ^ 6 = 1 := by
    field_simp
  obtain ⟨K₁, L₁, U₁, V₁, S₁, Y₁, ε, hstep⟩ :=
    exists_isMatrixImplicitBUGStep hh.le hlam hcs 0
  have hlow := one_div_le_norm_sub ha hstep
  have hup := H h (1 / (h * s ^ 6)) c s ε 0 S₁ K₁ L₁ U₁ V₁ Y₁ hh hh1 hlam hstep
  rw [Matrix.mul_one] at hup
  have he0 := norm_start_sub_sq hcs
  have he : ‖(!![c; s] : Matrix (Fin 2) (Fin 1) ℝ) * !![c; s]ᵀ - Xₜ‖ ≤ 2 * s :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (by nlinarith)
  have h1 : C₁ * ‖(!![c; s] : Matrix (Fin 2) (Fin 1) ℝ) * !![c; s]ᵀ - Xₜ‖ ≤
      (|C₁| + 1) * (4 * p) := by
    have h2 : C₁ ≤ |C₁| + 1 := by linarith [le_abs_self C₁]
    calc C₁ * ‖(!![c; s] : Matrix (Fin 2) (Fin 1) ℝ) * !![c; s]ᵀ - Xₜ‖
        ≤ (|C₁| + 1) * ‖(!![c; s] : Matrix (Fin 2) (Fin 1) ℝ) * !![c; s]ᵀ - Xₜ‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ (|C₁| + 1) * (4 * p) := mul_le_mul_of_nonneg_left (by linarith) hD₁.le
  have h3 : (|C₁| + 1) * (4 * p) = 1 / 44 := by
    rw [hp_def]
    field_simp
    ring
  have h4 : C₂ * h ≤ 1 / 44 := by
    have h5 : (|C₂| + 1) * h = 1 / 44 := by
      rw [hh_def]
      field_simp
    have h6 : C₂ ≤ |C₂| + 1 := by linarith [le_abs_self C₂]
    nlinarith [hh.le]
  linarith

/-- The hypotheses of `one_div_le_norm_sub` hold for every step size and every start angle: with
`lam = 1/(h s⁶)` a step exists, and it loses at least `1/11`. -/
example {h c s : ℝ} (hh : 0 < h) (hs : s ≠ 0) (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ (lam : ℝ) (Y₁ : Matrix (Fin 2) (Fin 2) ℝ), 0 ≤ lam ∧ h * lam * s ^ 6 = 1 ∧
      1 / 11 ≤ ‖Y₁ - Xₜ‖ := by
  have hlam : 0 ≤ 1 / (h * s ^ 6) := by positivity
  have ha : h * (1 / (h * s ^ 6)) * s ^ 6 = 1 := by
    field_simp
  obtain ⟨K₁, L₁, U₁, V₁, S₁, Y₁, ε, hstep⟩ :=
    exists_isMatrixImplicitBUGStep hh.le hlam hcs 0
  exact ⟨_, Y₁, hlam, ha, one_div_le_norm_sub ha hstep⟩

end StiffTwoSidedExample

end LeanDLRA
