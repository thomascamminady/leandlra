import LeanDLRA.Research.ImplicitBUGEnergyProjection

/-!
# Stiffness on both sides: augmenting the bases does not prevent the loss

For the BUG integrator with backward Euler substeps and a field `F(Z) = M Z + Z N` that is stiff
on both sides, the stiff energy of the numerical ROW basis reduces the effective step size of
the K-step. If the rough part of the column basis has two different frequencies of `M`, the
span of the old column basis and of the K-step result contains no vector that is close to the
smooth direction and has a small stiff energy. The S-step is a Galerkin step: it pays the stiff
energy of what it keeps, so it damps the smooth part of the solution, whatever the row basis
is. This file has an explicit family of `3 × 2` matrices of rank `1`:

  `M = diag(0, -μ, -3μ)`,  `N = diag(0, -lam)`,  `X(t) = e₁ e₁ᵀ` (stationary),
  `Y₀ = (c, s, s)ᵀ (c', t)`,  `c² + 2 s² = 1`,  `c'² + t² = 1`,
  `h μ = 1 + h lam t²`,  `4 s² h μ ≥ 31`.

For every step whose new column basis lies in the span of the old one and of the K-step result
(the augmented basis, and also the basis of the fixed-rank integrator), for every new row basis
and every truncation by an orthogonal projector from the right, the result is at distance
`≥ 1/3` from `X`, for every step size. The start error is `‖Y₀ - X‖² = 2 (1 - c c')`, which is
at most `4 s² + 2 t²` for `c, c' ≥ 0` and tends to `0` with `s`, `t` while `4 s² h μ ≥ 31` is kept
by `lam → ∞` (`s² t² h lam ≈ 31/4`).

## Main results

* `StiffAugmentedExample.one_div_three_le_norm_sub`: the loss `≥ 1/3` of every such step.
* `StiffAugmentedExample.norm_start_sub_sq`: `‖Y₀ - X‖² = 2 (1 - c c')`.
* `StiffAugmentedExample.field_stationary`: `M X + X N = 0`.
* `StiffAugmentedExample.exists_isMatrixImplicitBUGStep`: a step with the augmented column basis
  exists for every `h ≥ 0`, `lam ≥ 0`.

## Implementation notes

The K-step gives `K₁ = (c, s/2, s/4) / (h μ)`, so every vector `y` of the span of `(c, s, s)` and
`K₁` satisfies `s y₀ = c (3 y₁ - 2 y₂)`, hence `s² y₀² ≤ (31/3) (y₁² + 3 y₂²)`. The energy identity
of the S-step (`IsMatrixImplicitBUGStep.sq_norm_sstep_eq_inner`) bounds
`h μ ∑ⱼ (Z₁ⱼ² + 3 Z₂ⱼ²) ≤ ‖Z‖ (1 - ‖Z‖)` for the result `Z` of the S-step.

## References

* [CerutiLubich2022], [CerutiKuschLubich2022] for the BUG integrator and its augmented form;
  backward Euler substeps as in arXiv 2610.18419.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA

namespace StiffAugmentedExample

/-- The stiff matrix `diag(0, -μ, -3μ)` acting on the columns. -/
local notation "Mₐ" μ => (!![0, 0, 0; 0, -μ, 0; 0, 0, -(3 * μ)] : Matrix (Fin 3) (Fin 3) ℝ)

/-- The stiff matrix `diag(0, -lam)` acting on the rows. -/
local notation "Nₐ" lam => (!![0, 0; 0, -lam] : Matrix (Fin 2) (Fin 2) ℝ)

/-- The stationary solution `e₁ e₁ᵀ`. -/
local notation "Xₐ" => (!![1, 0; 0, 0; 0, 0] : Matrix (Fin 3) (Fin 2) ℝ)

/-- The field applied to the K-stage, times the old row basis. -/
private theorem field_mul_col (μ lam c' t : ℝ) (K : Matrix (Fin 3) (Fin 1) ℝ) :
    ((Mₐ μ) * (K * !![c'; t]ᵀ) + K * !![c'; t]ᵀ * Nₐ lam) * !![c'; t] =
      !![-(lam * t ^ 2) * K 0 0;
        -(μ * (c' ^ 2 + t ^ 2)) * K 1 0 - lam * t ^ 2 * K 1 0;
        -(3 * μ * (c' ^ 2 + t ^ 2)) * K 2 0 - lam * t ^ 2 * K 2 0] := by
  ext i j
  fin_cases j
  fin_cases i
  · norm_num [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.vecMul, dotProduct,
      Matrix.vecHead, Function.swap]
    ring
  · norm_num [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.vecMul, dotProduct,
      Matrix.vecHead, Function.swap]
    ring
  · norm_num [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.vecMul, dotProduct,
      Matrix.vecHead, Function.swap]
    ring

/-- The quadratic form of the field. -/
private theorem inner_field (μ lam : ℝ) (z : Matrix (Fin 3) (Fin 2) ℝ) :
    ⟪(Mₐ μ) * z + z * (Nₐ lam), z⟫ =
      -(μ * (z 1 0 ^ 2 + z 1 1 ^ 2 + 3 * (z 2 0 ^ 2 + z 2 1 ^ 2))) -
        lam * (z 0 1 ^ 2 + z 1 1 ^ 2 + z 2 1 ^ 2) := by
  norm_num [Frobenius.inner_def, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.mul_apply,
    Matrix.vecMul, dotProduct]
  ring

/-- The start value has norm `1`. -/
private theorem norm_start_sq {c s c' t : ℝ} (hcs : c ^ 2 + 2 * s ^ 2 = 1)
    (hct : c' ^ 2 + t ^ 2 = 1) :
    ‖(!![c; s; s] : Matrix (Fin 3) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) *
      (!![c'; t] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ‖ ^ 2 = 1 := by
  rw [Frobenius.norm_sq_eq_sum]
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.vecHead,
    Function.swap]
  linear_combination (c' ^ 2 + t ^ 2) * hcs + hct

/-- A row vector does not grow under an orthogonal projector of the plane. -/
private theorem row_proj_le {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q * Q = Q) (hQt : Qᵀ = Q)
    (a b : ℝ) :
    (a * Q 0 0 + b * Q 1 0) ^ 2 + (a * Q 0 1 + b * Q 1 1) ^ 2 ≤ a ^ 2 + b ^ 2 := by
  have q10 : Q 1 0 = Q 0 1 := by
    have e := congrFun (congrFun hQt 0) 1
    rwa [Matrix.transpose_apply] at e
  have h1 := congrFun (congrFun hQ 0) 0
  have h2 := congrFun (congrFun hQ 0) 1
  have h3 := congrFun (congrFun hQ 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, q10] at h1 h2 h3
  rw [q10]
  have key : a ^ 2 + b ^ 2 - ((a * Q 0 0 + b * Q 0 1) ^ 2 + (a * Q 0 1 + b * Q 1 1) ^ 2) =
      (a * (1 - Q 0 0) - b * Q 0 1) ^ 2 + (a * Q 0 1 - b * (1 - Q 1 1)) ^ 2 := by
    linear_combination (-2 * a ^ 2) * h1 + (-4 * a * b) * h2 + (-2 * b ^ 2) * h3
  nlinarith [sq_nonneg (a * (1 - Q 0 0) - b * Q 0 1), sq_nonneg (a * Q 0 1 - b * (1 - Q 1 1))]

/-- The scalar core of the lower bound. -/
private theorem scalar_bound {D s c x A q e T1 T2 : ℝ} (hD : 0 < D) (hg : 31 ≤ 4 * s ^ 2 * D)
    (hc : c ^ 2 ≤ 1) (hx0 : 0 ≤ x) (hA0 : 0 ≤ A) (hE : x ^ 2 + D * A ≤ x)
    (hrel : s * q = c * (3 * T1 - 2 * T2)) (hT : T1 ^ 2 + 3 * T2 ^ 2 ≤ A) (hqx : q ^ 2 ≤ x ^ 2)
    (hq : 1 - e ≤ q) : 1 / 3 ≤ e := by
  by_contra hcon
  rw [not_le] at hcon
  have hq1 : 2 / 3 < q := by linarith
  have hDA : 0 ≤ D * A := mul_nonneg hD.le hA0
  have hx1 : x ≤ 1 := by nlinarith
  have hxq : q ≤ x := by nlinarith
  -- `s² q² ≤ (31/3) A`
  have h1 : (3 * T1 - 2 * T2) ^ 2 ≤ 31 / 3 * (T1 ^ 2 + 3 * T2 ^ 2) := by
    nlinarith [sq_nonneg (2 * T1 + 9 * T2)]
  have h2 : s ^ 2 * q ^ 2 ≤ 31 / 3 * A := by
    have e1 : s ^ 2 * q ^ 2 = c ^ 2 * (3 * T1 - 2 * T2) ^ 2 := by
      rw [← mul_pow, hrel, mul_pow]
    rw [e1]
    have := mul_le_mul_of_nonneg_right hc (sq_nonneg (3 * T1 - 2 * T2))
    linarith
  have h3 : D * (s ^ 2 * q ^ 2) ≤ 31 / 3 * (D * A) := by
    have := mul_le_mul_of_nonneg_left h2 hD.le
    linarith
  have h4 : 31 / 4 * q ^ 2 ≤ D * (s ^ 2 * q ^ 2) := by
    have := mul_le_mul_of_nonneg_right hg (sq_nonneg q)
    linarith
  have h5 : D * A ≤ x - x ^ 2 := by linarith
  have h6 : x - x ^ 2 ≤ 1 - x := by nlinarith
  nlinarith

/-- **Augmented bases do not prevent the loss under two-sided stiffness.** Let
`c² + 2 s² = 1`, `c'² + t² = 1` (orthonormal start bases), `h μ = 1 + h lam t²` and
`4 s² h μ ≥ 31`. For every step of the matrix implicit BUG integrator for `F(Z) = M Z + Z N`,
`M = diag(0, -μ, -3μ)`, `N = diag(0, -lam)`, started from `Y₀ = (c, s, s)ᵀ (c', t)`, whose new
column basis `U₁` (with any number of columns) lies in the span of the old column basis and of
the K-step result, for every new row basis `V₁` and every orthogonal projector `Q` (a truncation
of the row space; `Q = 1` for none), the result of the S-step satisfies

  `‖U₁ S₁ V₁ᵀ Q - e₁ e₁ᵀ‖ ≥ 1/3`,

for every step size and whatever the capture and truncation tolerances are. -/
theorem one_div_three_le_norm_sub {h lam μ c s c' t ε τ ϑ t₁ : ℝ}
    (hμ : h * μ = 1 + h * lam * t ^ 2) (hg : 31 ≤ 4 * s ^ 2 * (h * μ))
    {k k' : Type*} [Fintype k] [DecidableEq k] [Fintype k'] [DecidableEq k']
    {K₁ : Matrix (Fin 3) (Fin 1) ℝ} {L₁ : Matrix (Fin 2) (Fin 1) ℝ} {U₁ : Matrix (Fin 3) k ℝ}
    {V₁ : Matrix (Fin 2) k' ℝ} {S₁ : Matrix k k' ℝ} {Y₁ : Matrix (Fin 3) (Fin 2) ℝ}
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 3) (Fin 2) ℝ) =>
      (Mₐ μ) * Z + Z * Nₐ lam) ε τ ϑ t₁ h !![c; s; s] 1 !![c'; t] K₁ L₁ U₁ V₁ S₁ Y₁)
    (hU₁ : ∃ R₀ R₁ : Matrix (Fin 1) k ℝ, U₁ = !![c; s; s] * R₀ + K₁ * R₁)
    {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q * Q = Q) (hQt : Qᵀ = Q) :
    1 / 3 ≤ ‖U₁ * S₁ * V₁ᵀ * Q - Xₐ‖ := by
  have hcs : c ^ 2 + 2 * s ^ 2 = 1 := by
    have e := congrFun (congrFun hs.orthU₀ 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.transpose_apply,
      Matrix.transpose_apply, Matrix.one_apply_eq] at e
    simp at e
    linear_combination e
  have hct : c' ^ 2 + t ^ 2 = 1 := by
    have e := congrFun (congrFun hs.orthV₀ 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.transpose_apply,
      Matrix.one_apply_eq] at e
    simp at e
    linear_combination e
  have hD : 0 < h * μ := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith [mul_nonneg (sq_nonneg s) (neg_nonneg.2 hneg)]
  have hc1 : c ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
  have hlam0 : 0 ≤ h * lam := by
    by_contra hneg
    rw [not_le] at hneg
    have h1 : h * lam * t ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le (sq_nonneg t)
    nlinarith [sq_nonneg s, sq_nonneg c]
  -- the K-step
  have hk := hs.kstep
  rw [Matrix.mul_one, field_mul_col] at hk
  have e0 : K₁ 0 0 = c + h * (-(lam * t ^ 2) * K₁ 0 0) := by
    simpa using congrFun (congrFun hk 0) 0
  have e1 : K₁ 1 0 = s + h * (-(μ * (c' ^ 2 + t ^ 2)) * K₁ 1 0 - lam * t ^ 2 * K₁ 1 0) := by
    simpa using congrFun (congrFun hk 1) 0
  have e2 : K₁ 2 0 = s + h * (-(3 * μ * (c' ^ 2 + t ^ 2)) * K₁ 2 0 - lam * t ^ 2 * K₁ 2 0) := by
    simpa using congrFun (congrFun hk 2) 0
  have k0 : K₁ 0 0 * (h * μ) = c := by linear_combination e0 + K₁ 0 0 * hμ
  have k1 : K₁ 1 0 * (2 * (h * μ)) = s := by
    linear_combination e1 + K₁ 1 0 * hμ - h * μ * K₁ 1 0 * hct
  have k2 : K₁ 2 0 * (4 * (h * μ)) = s := by
    linear_combination e2 + K₁ 2 0 * hμ - 3 * h * μ * K₁ 2 0 * hct
  have hnk : -s * K₁ 0 0 + 3 * c * K₁ 1 0 - 2 * c * K₁ 2 0 = 0 := by
    have e : (-s * K₁ 0 0 + 3 * c * K₁ 1 0 - 2 * c * K₁ 2 0) * (4 * (h * μ)) = 0 := by
      linear_combination (-4 * s) * k0 + (6 * c) * k1 + (-2 * c) * k2
    rcases mul_eq_zero.1 e with e' | e'
    · exact e'
    · linarith
  -- the new column basis lies in a plane
  obtain ⟨R₀, R₁, hR⟩ := hU₁
  have hrelU : ∀ a, s * U₁ 0 a = c * (3 * U₁ 1 a - 2 * U₁ 2 a) := by
    intro a
    have u0 : U₁ 0 a = c * R₀ 0 a + K₁ 0 0 * R₁ 0 a := by
      rw [hR]; simp [Matrix.add_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct]
    have u1 : U₁ 1 a = s * R₀ 0 a + K₁ 1 0 * R₁ 0 a := by
      rw [hR]; simp [Matrix.add_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct]
    have u2 : U₁ 2 a = s * R₀ 0 a + K₁ 2 0 * R₁ 0 a := by
      rw [hR]; simp [Matrix.add_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct]
    rw [u0, u1, u2]
    linear_combination (-(R₁ 0 a)) * hnk
  have hrel : ∀ (W : Matrix k (Fin 2) ℝ) (j : Fin 2),
      s * (U₁ * W) 0 j = c * (3 * (U₁ * W) 1 j - 2 * (U₁ * W) 2 j) := by
    intro W j
    simp only [Matrix.mul_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    linear_combination W a j * hrelU a
  -- the energy identity of the S-step
  have hE := hs.sq_norm_sstep_eq_inner
  beta_reduce at hE
  rw [inner_add_left, real_inner_smul_left, inner_field] at hE
  have hY0 := norm_start_sq hcs hct
  have hY1 : ‖(!![c; s; s] : Matrix (Fin 3) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) *
      (!![c'; t] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ‖ = 1 := by
    have := norm_nonneg ((!![c; s; s] : Matrix (Fin 3) (Fin 1) ℝ) *
      (1 : Matrix (Fin 1) (Fin 1) ℝ) * (!![c'; t] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ)
    nlinarith
  have hin := real_inner_le_norm ((!![c; s; s] : Matrix (Fin 3) (Fin 1) ℝ) *
    (1 : Matrix (Fin 1) (Fin 1) ℝ) * (!![c'; t] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ) (U₁ * S₁ * V₁ᵀ)
  rw [hY1, one_mul] at hin
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = U₁ * S₁ * V₁ᵀ := ⟨_, rfl⟩
  rw [← hZ] at hE hin ⊢
  have hnorm : ‖Z‖ ^ 2 = Z 0 0 ^ 2 + Z 0 1 ^ 2 + (Z 1 0 ^ 2 + Z 1 1 ^ 2) +
      (Z 2 0 ^ 2 + Z 2 1 ^ 2) := by
    rw [Frobenius.norm_sq_eq_sum, Fin.sum_univ_three, Fin.sum_univ_two, Fin.sum_univ_two,
      Fin.sum_univ_two]
  -- the truncated result
  have hTe : ∀ i j, (Z * Q) i j = Z i 0 * Q 0 j + Z i 1 * Q 1 j := fun i j => by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have hT0 := row_proj_le hQ hQt (Z 0 0) (Z 0 1)
  have hT1 := row_proj_le hQ hQt (Z 1 0) (Z 1 1)
  have hT2 := row_proj_le hQ hQt (Z 2 0) (Z 2 1)
  rw [← hTe, ← hTe] at hT0 hT1 hT2
  have hrelT : s * (Z * Q) 0 0 = c * (3 * (Z * Q) 1 0 - 2 * (Z * Q) 2 0) := by
    have e : Z * Q = U₁ * (S₁ * V₁ᵀ * Q) := by rw [hZ]; simp only [Matrix.mul_assoc]
    rw [e]
    exact hrel _ 0
  have hn := Frobenius.abs_apply_le_norm (Z * Q - Xₐ) 0 0
  have d0 : (Z * Q - Xₐ) 0 0 = (Z * Q) 0 0 - 1 := by
    rw [Matrix.sub_apply]
    simp
  rw [d0] at hn
  have hq := neg_abs_le ((Z * Q) 0 0 - 1)
  have hA0 : 0 ≤ Z 1 0 ^ 2 + Z 1 1 ^ 2 + 3 * (Z 2 0 ^ 2 + Z 2 1 ^ 2) := by positivity
  have hB0 : 0 ≤ h * lam * (Z 0 1 ^ 2 + Z 1 1 ^ 2 + Z 2 1 ^ 2) :=
    mul_nonneg hlam0 (by positivity)
  refine scalar_bound (D := h * μ) (x := ‖Z‖)
    (A := Z 1 0 ^ 2 + Z 1 1 ^ 2 + 3 * (Z 2 0 ^ 2 + Z 2 1 ^ 2)) (q := (Z * Q) 0 0)
    (T1 := (Z * Q) 1 0) (T2 := (Z * Q) 2 0) hD hg hc1 (norm_nonneg _) hA0 ?_ hrelT ?_ ?_ ?_
  · linarith
  · linarith [sq_nonneg ((Z * Q) 1 1), sq_nonneg ((Z * Q) 2 1)]
  · linarith [sq_nonneg ((Z * Q) 0 1), sq_nonneg (Z 1 0), sq_nonneg (Z 1 1), sq_nonneg (Z 2 0),
      sq_nonneg (Z 2 1)]
  · linarith

/-- **The start value is close to the solution**: `‖(c, s, s)ᵀ (c', t) - e₁ e₁ᵀ‖² = 2 (1 - c c')`
for `c² + 2 s² = 1`, `c'² + t² = 1`. -/
theorem norm_start_sub_sq {c s c' t : ℝ} (hcs : c ^ 2 + 2 * s ^ 2 = 1)
    (hct : c' ^ 2 + t ^ 2 = 1) :
    ‖(!![c; s; s] : Matrix (Fin 3) (Fin 1) ℝ) * (!![c'; t] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ - Xₐ‖ ^ 2 =
      2 * (1 - c * c') := by
  rw [Frobenius.norm_sq_eq_sum]
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.vecHead,
    Function.swap]
  linear_combination (c' ^ 2 + t ^ 2) * hcs + hct

/-- **The reference is stationary**: `M e₁ e₁ᵀ + e₁ e₁ᵀ N = 0`. -/
theorem field_stationary (μ lam : ℝ) : (Mₐ μ) * Xₐ + Xₐ * (Nₐ lam) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The transposed field applied to the L-stage, times the old column basis. -/
private theorem transpose_field_mul_col (μ lam c s : ℝ) (L : Matrix (Fin 2) (Fin 1) ℝ) :
    ((Mₐ μ) * (!![c; s; s] * Lᵀ) + !![c; s; s] * Lᵀ * Nₐ lam)ᵀ * !![c; s; s] =
      !![-(4 * μ * s ^ 2) * L 0 0;
        -(4 * μ * s ^ 2) * L 1 0 - lam * (c ^ 2 + 2 * s ^ 2) * L 1 0] := by
  ext i j
  fin_cases j
  fin_cases i
  · norm_num [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.vecMul, dotProduct,
      Matrix.vecHead, Function.swap]
    ring
  · norm_num [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.vecMul, dotProduct,
      Matrix.vecHead, Function.swap]
    ring

/-- **A step with the augmented column basis exists.** For `h ≥ 0`, `lam ≥ 0`, `μ ≥ 0`, `s ≠ 0`,
`c² + 2 s² = 1`, `c'² + t² = 1` and `h μ = 1 + h lam t²` the matrix implicit BUG integrator for
`F(Z) = M Z + Z N`, `M = diag(0, -μ, -3μ)`, `N = diag(0, -lam)`, has a step without truncation
from `U₀ = (c, s, s)ᵀ`, `S₀ = 1`, `V₀ = (c', t)ᵀ` whose new column basis has two columns, the
first one `U₀`, both in the span of `U₀` and `K₁`, and whose new row basis is the identity. -/
theorem exists_isMatrixImplicitBUGStep {h lam μ c s c' t : ℝ} (hh : 0 ≤ h) (hlam : 0 ≤ lam)
    (hμ0 : 0 ≤ μ) (hs0 : s ≠ 0) (hcs : c ^ 2 + 2 * s ^ 2 = 1) (hct : c' ^ 2 + t ^ 2 = 1)
    (hμ : h * μ = 1 + h * lam * t ^ 2) (t₁ : ℝ) :
    ∃ (K₁ : Matrix (Fin 3) (Fin 1) ℝ) (L₁ : Matrix (Fin 2) (Fin 1) ℝ)
      (U₁ : Matrix (Fin 3) (Fin 2) ℝ) (S₁ : Matrix (Fin 2) (Fin 2) ℝ)
      (Y₁ : Matrix (Fin 3) (Fin 2) ℝ) (ε τ : ℝ),
      IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 3) (Fin 2) ℝ) =>
        (Mₐ μ) * Z + Z * Nₐ lam) ε τ 0 t₁ h !![c; s; s] 1 !![c'; t] K₁ L₁ U₁
        (1 : Matrix (Fin 2) (Fin 2) ℝ) S₁ Y₁ ∧
      (∀ i, U₁ i 0 = (!![c; s; s] : Matrix (Fin 3) (Fin 1) ℝ) i 0) ∧
      ∃ R₀ R₁ : Matrix (Fin 1) (Fin 2) ℝ, U₁ = !![c; s; s] * R₀ + K₁ * R₁ := by
  have hp : 0 ≤ h * lam * t ^ 2 := mul_nonneg (mul_nonneg hh hlam) (sq_nonneg t)
  have hD : 0 < h * μ := by rw [hμ]; linarith
  have hq : 0 ≤ 4 * (h * μ) * s ^ 2 := mul_nonneg (by linarith) (sq_nonneg s)
  have hhl : 0 ≤ h * lam := mul_nonneg hh hlam
  obtain ⟨k0, hk0⟩ : ∃ k0 : ℝ, k0 * (h * μ) = c := ⟨_, div_mul_cancel₀ _ hD.ne'⟩
  obtain ⟨k1, hk1⟩ : ∃ k1 : ℝ, k1 * (2 * (h * μ)) = s :=
    ⟨_, div_mul_cancel₀ _ (by positivity)⟩
  obtain ⟨k2, hk2⟩ : ∃ k2 : ℝ, k2 * (4 * (h * μ)) = s :=
    ⟨_, div_mul_cancel₀ _ (by positivity)⟩
  obtain ⟨l0, hl0⟩ : ∃ l0 : ℝ, l0 * (1 + 4 * (h * μ) * s ^ 2) = c' :=
    ⟨_, div_mul_cancel₀ _ (by positivity)⟩
  obtain ⟨l1, hl1⟩ : ∃ l1 : ℝ, l1 * (1 + 4 * (h * μ) * s ^ 2 + h * lam) = t :=
    ⟨_, div_mul_cancel₀ _ (by positivity)⟩
  -- the normalisation of the second basis vector
  have hr2 : 0 < 13 * c ^ 2 + s ^ 2 := by positivity
  obtain ⟨ι, hι⟩ : ∃ ι : ℝ, ι ^ 2 * (13 * c ^ 2 + s ^ 2) = 1 :=
    ⟨(√(13 * c ^ 2 + s ^ 2))⁻¹, by
      rw [inv_pow, Real.sq_sqrt hr2.le]
      exact inv_mul_cancel₀ hr2.ne'⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, s * σ = 1 := ⟨s⁻¹, mul_inv_cancel₀ hs0⟩
  obtain ⟨U₁, hUdef⟩ : ∃ U₁ : Matrix (Fin 3) (Fin 2) ℝ,
      U₁ = !![c, ι * (-5 * c * s); s, ι * (2 * c ^ 2 - s ^ 2); s, ι * (3 * c ^ 2 + s ^ 2)] :=
    ⟨_, rfl⟩
  have hU₁ : U₁ᵀ * U₁ = 1 := by
    rw [hUdef]
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_three]
      linear_combination hcs
    · simp [Matrix.mul_apply, Fin.sum_univ_three]
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_three]
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_three]
      linear_combination hι + ι ^ 2 * (13 * c ^ 2 + s ^ 2) * hcs
  have hV₁ : (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1 = 1 := by simp
  have hU₀ : (!![c; s; s] : Matrix (Fin 3) (Fin 1) ℝ)ᵀ * !![c; s; s] = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.transpose_apply,
      Matrix.transpose_apply]
    simp
    linear_combination hcs
  have hV₀ : (!![c'; t] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * !![c'; t] = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.transpose_apply]
    simp
    linear_combination hct
  -- the S-step
  let Φ : Matrix (Fin 3) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 3) (Fin 2) ℝ :=
    { toFun := fun Z => (Mₐ μ) * Z + Z * Nₐ lam
      map_add' := fun Z Z' => by
        simp only [Matrix.mul_add, Matrix.add_mul]
        abel
      map_smul' := fun a Z => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add, RingHom.id_apply] }
  have hdiss : ∀ Z, ⟪Φ Z, Z⟫ ≤ 0 := by
    intro Z
    have e : ⟪Φ Z, Z⟫ = ⟪(Mₐ μ) * Z + Z * (Nₐ lam), Z⟫ := rfl
    rw [e, inner_field]
    have h1 : 0 ≤ μ * (Z 1 0 ^ 2 + Z 1 1 ^ 2 + 3 * (Z 2 0 ^ 2 + Z 2 1 ^ 2)) :=
      mul_nonneg hμ0 (by positivity)
    have h2 : 0 ≤ lam * (Z 0 1 ^ 2 + Z 1 1 ^ 2 + Z 2 1 ^ 2) := mul_nonneg hlam (by positivity)
    linarith
  obtain ⟨S₁, hS₁⟩ := exists_eq_transpose_mul_add_smul_mul Φ hdiss hh hU₁ hV₁
    ((!![c; s; s] : Matrix (Fin 3) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) * !![c'; t]ᵀ)
  refine ⟨!![k0; k1; k2], !![l0; l1], U₁, S₁, U₁ * S₁ * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ,
    ‖(1 - U₁ * U₁ᵀ) *
        ((Mₐ μ) * (!![k0; k1; k2] * !![c'; t]ᵀ) + !![k0; k1; k2] * !![c'; t]ᵀ * (Nₐ lam)) *
        (1 - !![c'; t] * !![c'; t]ᵀ)‖ +
      ‖(1 - !![c; s; s] * !![c; s; s]ᵀ) *
        ((Mₐ μ) * (!![c; s; s] * !![l0; l1]ᵀ) + !![c; s; s] * !![l0; l1]ᵀ * (Nₐ lam)) *
        (1 - (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)‖,
    ‖(1 - U₁ * U₁ᵀ) * (!![k0; k1; k2] * !![c'; t]ᵀ)‖ +
      ‖!![c; s; s] * !![l0; l1]ᵀ *
        (1 - (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)‖, ?_, ?_, ?_⟩
  · exact
      { orthU₀ := hU₀
        orthV₀ := hV₀
        kstep := by
          rw [Matrix.mul_one]
          rw [field_mul_col]
          ext i j
          fin_cases j
          fin_cases i
          · simp
            linear_combination hk0 - k0 * hμ
          · simp
            linear_combination hk1 - k1 * hμ + h * μ * k1 * hct
          · simp
            linear_combination hk2 - k2 * hμ + 3 * h * μ * k2 * hct
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
        orthU₁ := hU₁
        orthV₁ := hV₁
        kcap := le_add_of_nonneg_right (norm_nonneg _)
        lcap := le_add_of_nonneg_left (norm_nonneg _)
        knormal := le_add_of_nonneg_right (norm_nonneg _)
        lnormal := le_add_of_nonneg_left (norm_nonneg _)
        sstep := hS₁
        trunc := by rw [sub_self, norm_zero] }
  · intro i
    rw [hUdef]
    fin_cases i <;> simp
  · refine ⟨!![1, ι * σ * (3 * c ^ 2 + s ^ 2 + 1)], !![0, -(4 * (h * μ) * ι * σ)], ?_⟩
    rw [hUdef]
    ext i j
    fin_cases i <;> fin_cases j
    · simp
    · simp
      linear_combination (4 * ι * σ) * hk0 + (5 * c * ι * s) * hσ - (3 * c * ι * σ) * hcs
    · simp
    · simp
      linear_combination (2 * ι * σ) * hk1 - ι * (3 * c ^ 2 + s ^ 2 - 1) * hσ - ι * hcs
    · simp
    · simp
      linear_combination (ι * σ) * hk2 - ι * (3 * c ^ 2 + s ^ 2) * hσ

/-- The loss occurs for every step size and for arbitrarily small start errors: for `h > 0`,
`s ≠ 0`, `t ≠ 0` with `c² + 2 s² = 1`, `c'² + t² = 1`, choose `lam` and `μ` with
`4 s² (1 + h lam t²) = 31` and `h μ = 1 + h lam t²`; then a step with the augmented column basis
exists and its result is at distance `≥ 1/3` from the stationary solution. -/
example {h c s c' t : ℝ} (hh : 0 < h) (hs0 : s ≠ 0) (ht0 : t ≠ 0)
    (hcs : c ^ 2 + 2 * s ^ 2 = 1) (hct : c' ^ 2 + t ^ 2 = 1) :
    ∃ (lam μ : ℝ) (U₁ : Matrix (Fin 3) (Fin 2) ℝ) (S₁ : Matrix (Fin 2) (Fin 2) ℝ),
      h * μ = 1 + h * lam * t ^ 2 ∧ 4 * s ^ 2 * (h * μ) = 31 ∧
      (∀ i, U₁ i 0 = (!![c; s; s] : Matrix (Fin 3) (Fin 1) ℝ) i 0) ∧
      1 / 3 ≤ ‖U₁ * S₁ * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ) -
        Xₐ‖ := by
  have hs2 : 0 < s ^ 2 := by positivity
  have ht2 : 0 < t ^ 2 := by positivity
  have hs2le : 4 * s ^ 2 ≤ 2 := by nlinarith [sq_nonneg c]
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = 31 / (4 * s ^ 2) := ⟨_, rfl⟩
  have hD4 : 4 * s ^ 2 * D = 31 := by rw [hDdef]; field_simp
  have hD1 : 1 ≤ D := by nlinarith
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ, lam = (D - 1) / (h * t ^ 2) := ⟨_, rfl⟩
  have hlam0 : 0 ≤ lam := by
    rw [hlamdef]
    exact div_nonneg (by linarith) (by positivity)
  have hlamD : 1 + h * lam * t ^ 2 = D := by
    rw [hlamdef]
    field_simp
    ring
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ, μ = D / h := ⟨_, rfl⟩
  have hμ0 : 0 ≤ μ := by rw [hμdef]; exact div_nonneg (by linarith) hh.le
  have hμ : h * μ = 1 + h * lam * t ^ 2 := by
    rw [hlamD, hμdef]
    field_simp
  obtain ⟨K₁, L₁, U₁, S₁, Y₁, ε, τ, hstep, hcol, hspan⟩ :=
    exists_isMatrixImplicitBUGStep hh.le hlam0 hμ0 hs0 hcs hct hμ 0
  have h31 : 4 * s ^ 2 * (h * μ) = 31 := by rw [hμ, hlamD, hD4]
  exact ⟨lam, μ, U₁, S₁, hμ, h31, hcol,
    one_div_three_le_norm_sub hμ h31.ge hstep hspan (Matrix.mul_one 1) Matrix.transpose_one⟩

end StiffAugmentedExample

end LeanDLRA
