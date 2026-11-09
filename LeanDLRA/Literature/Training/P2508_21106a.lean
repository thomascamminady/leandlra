import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Integrators.Matrix.Symmetry
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2508.21106: AdaGram: DLRA of a full-matrix preconditioner

This module formalizes T. Matveeva, A. Katrutsa, E. Frolov, *Dynamic Low-rank Approximation of
Full-Matrix Preconditioner for Training Generalized Linear Models* (arXiv v1, checked in the PDF),
for `G_t = ε I + ∑_{τ ≤ t} g_τ g_τᵀ` (`precond`, eqs. (2), (3)).  **Theorem 1** is `theorem_one`
with base case eq. (18) `factor_one_inv_apply`, and **Lemma 1** is `lemma_one`, both for the
recursive factor `L_{t+1} = L_t (I + α ḡ ḡᵀ)` of eq. (8) (`factor`, `factor_mul_transpose`), with
eq. (5) `one_add_alpha_mul`, `alpha_unique`, eq. (9) `inv_factor_succ`, and eqs. (11)-(13) `stateA`,
`deltaA`, `stateA_succ`.  Lines 5 and 7 of Algorithm 2 are `gbar_eq` and `adagram_update_norm`, the
isometry of §3.2 is `isometry_inv`, `isometry_invSqrt`, and Algorithm 1 is `IsAlgorithm1Step`, which
is the library's KSL step (`IsAlgorithm1Step.isKSLStep`, closed form `IsAlgorithm1Step.eq`).  Two
printed claims are false and are refuted here.  Theorem 1 fails, already at `t = 0`, for the
triangular Cholesky factor, which is what the paper says `L_t` is
(`theorem_one_false_for_triangular_cholesky`); the recursion (8) that its proof uses leaves the
triangular matrices (`factor_one_not_lowerTriangular`), so `L_t` is only some factor of `G_t`.  Eq.
(4) fails with the printed `ḡ = G⁻¹ g` (`eq_four_false_as_printed`); the exponent must be `-1/2`
(`eq_four_corrected`).  Two slips do not affect the results: the appendix writes
`L_0 = (1/√ε) I`, which contradicts `G_0 = ε I` and Algorithm 2 (we use `√ε I`), and the proof of
Lemma 1 multiplies in the wrong order, while the lemma as printed is right.  The two items of the
survey header were inferred from the abstract and are not claims of the paper, whose `A_t` is not
an accumulator of `g gᵀ` and for which it gives no exactness statement.  The spectral identity is
`spectral_lowRank` (any `φ`), `spectral_lowRank_mulVec` (the `O(n r)` form) and `invSqrt_lowRank`.
For DLRA maintenance, exactness is the library's `Exactness.ksl_exact`, `Exactness.bug_exact_ode`
and symmetry is `Symmetry.bug_isTwistSymm`; new here are PSD preservation
(`bug_core_posSemidef`, `bug_maintenance`, `bug_increment_step`, `bug_outerProduct_step`), all
steps of the accumulator (`bug_accumulator_exact`), the direction `G_t^{-1/2}` from the low-rank
factors (`bug_invSqrt_precond`), and exactness of Algorithm 1 and of all of Algorithm 2 while `A_t`
has rank at most `r` (`IsAlgorithm1Step.exact`, `algorithm2_exact`), with instances in every
dimension (`algorithm2_exact_parallel`, `bug_accumulator_parallel`).  The header's "symmetric,
PSD-preserving" holds for BUG only: it is false for the paper's own Algorithm 1
(`algorithm1_not_symmetric`).  Not treated: the damped update (14), which the paper offers as a
heuristic with no claim of exactness, error bounds for rank-truncated runs (the paper gives none),
and the convergence experiments.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2508_21106

open Matrix

/-! ### The accumulated preconditioner and the scalars `α`, `β` -/

section Recursion

variable {n : Type*}

/-- The accumulated preconditioner of arXiv 2508.21106, eq. (2):
`G_t = ε I + ∑_{τ = 1}^t g_τ g_τᵀ`.  The value `g 0` is not used. -/
noncomputable def precond [DecidableEq n] (ε : ℝ) (g : ℕ → n → ℝ) (t : ℕ) : Matrix n n ℝ :=
  ε • 1 + ∑ τ ∈ Finset.Icc 1 t, vecMulVec (g τ) (g τ)

/-- arXiv 2508.21106, eq. (3): `G_{t+1} = G_t + g_{t+1} g_{t+1}ᵀ`. -/
theorem precond_succ [DecidableEq n] (ε : ℝ) (g : ℕ → n → ℝ) (t : ℕ) :
    precond ε g (t + 1) = precond ε g t + vecMulVec (g (t + 1)) (g (t + 1)) := by
  simp only [precond]
  rw [Finset.sum_Icc_succ_top (by omega), add_assoc]

/-- arXiv 2508.21106, eq. (3): `G_0 = ε I`. -/
@[simp] theorem precond_zero [DecidableEq n] (ε : ℝ) (g : ℕ → n → ℝ) :
    precond ε g 0 = ε • 1 := by
  simp [precond]

/-- The scalar `α` of arXiv 2508.21106, eq. (5), as a function of `s = ‖ḡ‖²`:
`α = (√(1 + s) - 1) / s`.  For `s = 0` equation (5) does not restrict `α`, and every occurrence of
`α` multiplies `ḡ ḡᵀ = 0`; Lean's `x / 0 = 0` then gives `α = 0`. -/
noncomputable def alpha (s : ℝ) : ℝ := (√(1 + s) - 1) / s

/-- The scalar `β = α / (1 + α ‖ḡ‖²)` of arXiv 2508.21106, eq. (9). -/
noncomputable def beta (s : ℝ) : ℝ := alpha s / (1 + alpha s * s)

/-- arXiv 2508.21106, eq. (5): `1 + α ‖ḡ‖² = (1 + ‖ḡ‖²)^{1/2}`. -/
theorem one_add_alpha_mul {s : ℝ} (hs : 0 ≤ s) : 1 + alpha s * s = √(1 + s) := by
  rcases hs.eq_or_lt with rfl | h
  · simp
  · simp only [alpha]
    field_simp
    ring

/-- Eq. (5) of arXiv 2508.21106 determines `α` when `ḡ ≠ 0`, so `alpha` is the paper's scalar. -/
theorem alpha_unique {s a : ℝ} (hs : 0 < s) (ha : 1 + a * s = √(1 + s)) : a = alpha s := by
  have h := one_add_alpha_mul hs.le
  have : (a - alpha s) * s = 0 := by linarith
  have := (mul_eq_zero.1 this).resolve_right hs.ne'
  linarith

private theorem dot_self_nonneg [Fintype n] (v : n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

private theorem one_add_alpha_mul_pos {s : ℝ} (hs : 0 ≤ s) : 0 < 1 + alpha s * s := by
  rw [one_add_alpha_mul hs]
  positivity

/-- `1 - β s = 1 / √(1 + s)`: the scalar in Theorem 1 of arXiv 2508.21106. -/
private theorem one_sub_beta_mul {s : ℝ} (hs : 0 ≤ s) : 1 - beta s * s = (√(1 + s))⁻¹ := by
  have h := one_add_alpha_mul hs
  have hp := one_add_alpha_mul_pos hs
  rw [← h]
  simp only [beta]
  field_simp
  ring

/-- With `s = ‖v‖²`, the rank-one matrix `v vᵀ` multiplies by `s`. -/
private theorem vecMulVec_self_mul_self [Fintype n] (v : n → ℝ) :
    vecMulVec v v * vecMulVec v v = (v ⬝ᵥ v) • vecMulVec v v := by
  rw [vecMulVec_mul_vecMulVec]
  ext i j
  simp only [vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem vecMulVec_self_eq_zero [Fintype n] {v : n → ℝ} (h : v ⬝ᵥ v = 0) :
    vecMulVec v v = 0 := by
  have : v = 0 := dotProduct_self_eq_zero.1 h
  simp [this]

private theorem vecMulVec_self_mulVec [Fintype n] (v w : n → ℝ) :
    vecMulVec v v *ᵥ w = (v ⬝ᵥ w) • v := by
  rw [vecMulVec_mulVec]
  ext i
  simp [mul_comm]

/-- Product of two perturbations of the identity by a matrix with `M² = s M`. -/
private theorem one_add_smul_mul_one_add_smul [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} {s : ℝ}
    (hM : M * M = s • M) (a b : ℝ) :
    (1 + a • M) * (1 + b • M) = 1 + (a + b + a * b * s) • M := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, hM]
  module

/-- The identity behind eq. (4) of arXiv 2508.21106:
`(I + α v vᵀ)² = I + v vᵀ` when `α` solves eq. (5). -/
theorem sq_one_add_alpha [Fintype n] [DecidableEq n] (v : n → ℝ) :
    (1 + alpha (v ⬝ᵥ v) • vecMulVec v v) * (1 + alpha (v ⬝ᵥ v) • vecMulVec v v)
      = 1 + vecMulVec v v := by
  have hs0 : 0 ≤ v ⬝ᵥ v := dot_self_nonneg v
  rw [one_add_smul_mul_one_add_smul (vecMulVec_self_mul_self v)]
  rcases hs0.eq_or_lt with h0 | hpos
  · simp [vecMulVec_self_eq_zero h0.symm]
  · set s := v ⬝ᵥ v
    have hsq2 : (1 + alpha s * s) ^ 2 = 1 + s := by
      rw [one_add_alpha_mul hs0, Real.sq_sqrt (by linarith)]
    have key : alpha s + alpha s + alpha s * alpha s * s = 1 := by
      have : (alpha s + alpha s + alpha s * alpha s * s - 1) * s = 0 := by nlinarith
      have := (mul_eq_zero.1 this).resolve_right hpos.ne'
      linarith
    rw [key, one_smul]

/-- `(I + α v vᵀ)(I - β v vᵀ) = I`: the Sherman–Morrison step of arXiv 2508.21106, eq. (9). -/
theorem one_add_alpha_mul_one_sub_beta [Fintype n] [DecidableEq n] (v : n → ℝ) :
    (1 + alpha (v ⬝ᵥ v) • vecMulVec v v) * (1 - beta (v ⬝ᵥ v) • vecMulVec v v) = 1 := by
  have hs0 : 0 ≤ v ⬝ᵥ v := dot_self_nonneg v
  have hp := one_add_alpha_mul_pos hs0
  rw [sub_eq_add_neg, ← neg_smul, one_add_smul_mul_one_add_smul (vecMulVec_self_mul_self v)]
  have : alpha (v ⬝ᵥ v) + -beta (v ⬝ᵥ v) + alpha (v ⬝ᵥ v) * -beta (v ⬝ᵥ v) * (v ⬝ᵥ v) = 0 := by
    simp only [beta]
    field_simp
    ring
  rw [this, zero_smul, add_zero]

/-! ### The recursive factor -/

variable [Fintype n] [DecidableEq n]

/-- The factor `L_t` of arXiv 2508.21106: `L_0 = √ε I` (Algorithm 2) and eq. (8),
`L_{t+1} = L_t (I + α_{t+1} ḡ_{t+1} ḡ_{t+1}ᵀ)`, with `ḡ_{t+1} = L_t⁻¹ g_{t+1}` and `α_{t+1}` from
eq. (5).  This recursion is the object the paper's proofs use.  It is a factor of `G_t`
(`factor_mul_transpose`) but it is not the triangular Cholesky factor
(`factor_one_not_lowerTriangular`).  The appendix of the paper writes `L_0 = (1/√ε) I`, which
contradicts `L_0 L_0ᵀ = G_0 = ε I` and Algorithm 2; we use `√ε I`. -/
noncomputable def factor (ε : ℝ) (g : ℕ → n → ℝ) : ℕ → Matrix n n ℝ
  | 0 => √ε • 1
  | t + 1 =>
    factor ε g t * (1 + alpha (((factor ε g t)⁻¹ *ᵥ g (t + 1)) ⬝ᵥ ((factor ε g t)⁻¹ *ᵥ g (t + 1)))
      • vecMulVec ((factor ε g t)⁻¹ *ᵥ g (t + 1)) ((factor ε g t)⁻¹ *ᵥ g (t + 1)))

/-- The transformed gradient `ḡ_{t+1} = L_t⁻¹ g_{t+1}` of arXiv 2508.21106, eq. (8). -/
noncomputable def gbar (ε : ℝ) (g : ℕ → n → ℝ) (t : ℕ) : n → ℝ :=
  (factor ε g t)⁻¹ *ᵥ g (t + 1)

private theorem factor_succ (ε : ℝ) (g : ℕ → n → ℝ) (t : ℕ) :
    factor ε g (t + 1) = factor ε g t *
      (1 + alpha (gbar ε g t ⬝ᵥ gbar ε g t) • vecMulVec (gbar ε g t) (gbar ε g t)) := rfl

/-- The factors `L_t` of arXiv 2508.21106, eq. (8), are invertible, as the paper uses tacitly. -/
theorem isUnit_factor {ε : ℝ} (hε : 0 < ε) (g : ℕ → n → ℝ) (t : ℕ) : IsUnit (factor ε g t) := by
  induction t with
  | zero =>
    have hs : (√ε)⁻¹ * √ε = 1 := inv_mul_cancel₀ (Real.sqrt_pos.2 hε).ne'
    refine IsUnit.of_mul_eq_one ((√ε)⁻¹ • (1 : Matrix n n ℝ)) ?_
    simp [factor, smul_smul, hs]
  | succ t ih =>
    rw [factor_succ]
    exact ih.mul (IsUnit.of_mul_eq_one _ (one_add_alpha_mul_one_sub_beta (gbar ε g t)))

private theorem factor_mul_gbar {ε : ℝ} (hε : 0 < ε) (g : ℕ → n → ℝ) (t : ℕ) :
    factor ε g t *ᵥ gbar ε g t = g (t + 1) := by
  have hu := isUnit_factor hε g t
  have hd : IsUnit (factor ε g t).det := (Matrix.isUnit_iff_isUnit_det _).1 hu
  rw [gbar, mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, one_mulVec]

/-- **The factorization** of arXiv 2508.21106, §3.2 (eqs. (4), (8) in Cholesky form):
`L_t Lᵀ_t = G_t` for the recursive factor. -/
theorem factor_mul_transpose {ε : ℝ} (hε : 0 < ε) (g : ℕ → n → ℝ) (t : ℕ) :
    factor ε g t * (factor ε g t)ᵀ = precond ε g t := by
  induction t with
  | zero =>
    have h : √ε * √ε = ε := Real.mul_self_sqrt hε.le
    simp [factor, smul_smul, h]
  | succ t ih =>
    set L := factor ε g t with hL
    set v := gbar ε g t with hv
    set C : Matrix n n ℝ := 1 + alpha (v ⬝ᵥ v) • vecMulVec v v with hC
    have hCt : Cᵀ = C := by
      simp [hC, Matrix.transpose_add, Matrix.transpose_smul, transpose_vecMulVec]
    have hsq : C * C = 1 + vecMulVec v v := sq_one_add_alpha v
    have hLv : L *ᵥ v = g (t + 1) := factor_mul_gbar hε g t
    have hrank : L * vecMulVec v v * Lᵀ = vecMulVec (g (t + 1)) (g (t + 1)) := by
      rw [mul_vecMulVec, vecMulVec_mul, hLv, Matrix.vecMul_transpose, hLv]
    rw [factor_succ, ← hL, ← hv, ← hC, Matrix.transpose_mul, hCt, precond_succ, ← ih, ← hrank]
    calc L * C * (C * Lᵀ) = L * (C * C) * Lᵀ := by simp only [Matrix.mul_assoc]
      _ = L * Lᵀ + L * vecMulVec v v * Lᵀ := by
        rw [hsq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]

/-- arXiv 2508.21106, eq. (9): `L_{t+1}⁻¹ = (I - β_{t+1} ḡ_{t+1} ḡ_{t+1}ᵀ) L_t⁻¹`. -/
theorem inv_factor_succ {ε : ℝ} (hε : 0 < ε) (g : ℕ → n → ℝ) (t : ℕ) :
    (factor ε g (t + 1))⁻¹ =
      (1 - beta (gbar ε g t ⬝ᵥ gbar ε g t) • vecMulVec (gbar ε g t) (gbar ε g t)) *
        (factor ε g t)⁻¹ := by
  have hd : IsUnit (factor ε g t).det := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_factor hε g t)
  have h1 := one_add_alpha_mul_one_sub_beta (gbar ε g t)
  have h2 := mul_eq_one_comm.1 h1
  refine Matrix.inv_eq_left_inv ?_
  rw [factor_succ]
  calc _ = (1 - beta (gbar ε g t ⬝ᵥ gbar ε g t) • vecMulVec (gbar ε g t) (gbar ε g t)) *
        ((factor ε g t)⁻¹ * factor ε g t) *
        (1 + alpha (gbar ε g t ⬝ᵥ gbar ε g t) • vecMulVec (gbar ε g t) (gbar ε g t)) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, h2]

/-- **Theorem 1** of arXiv 2508.21106 (recursive preconditioned gradient), for the recursive factor
`L_t` of eq. (8), which is the one the paper's proof constructs:
`L_{t+1}⁻¹ g_{t+1} = (1 + ‖L_t⁻¹ g_{t+1}‖²)^{-1/2} L_t⁻¹ g_{t+1}`.
Here `‖v‖² = v ⬝ᵥ v` (`gbar ε g t = L_t⁻¹ g_{t+1}`).

Difference from the paper: the paper says that `L_t` is "the Cholesky factor" of `G_t` and speaks of
triangular factors.  For the triangular Cholesky factor the statement is false, already at `t = 0`
(`theorem_one_false_for_triangular_cholesky`). -/
theorem theorem_one {ε : ℝ} (hε : 0 < ε) (g : ℕ → n → ℝ) (t : ℕ) :
    (factor ε g (t + 1))⁻¹ *ᵥ g (t + 1) =
      (√(1 + ((factor ε g t)⁻¹ *ᵥ g (t + 1)) ⬝ᵥ ((factor ε g t)⁻¹ *ᵥ g (t + 1))))⁻¹ •
        ((factor ε g t)⁻¹ *ᵥ g (t + 1)) := by
  change _ = (√(1 + gbar ε g t ⬝ᵥ gbar ε g t))⁻¹ • gbar ε g t
  rw [inv_factor_succ hε, ← mulVec_mulVec, ← gbar, sub_mulVec, one_mulVec, smul_mulVec,
    vecMulVec_self_mulVec, smul_smul, ← one_sub_beta_mul (dot_self_nonneg _), sub_smul,
    one_smul]

private theorem inv_factor_zero {ε : ℝ} (hε : 0 < ε) (g : ℕ → n → ℝ) :
    (factor ε g 0)⁻¹ = (√ε)⁻¹ • 1 := by
  have hs : √ε * (√ε)⁻¹ = 1 := mul_inv_cancel₀ (Real.sqrt_pos.2 hε).ne'
  refine Matrix.inv_eq_left_inv ?_
  simp [factor, smul_smul, hs]

/-- arXiv 2508.21106, eq. (18), the base case of Theorem 1:
`L_1⁻¹ g_1 = (ε + ‖g_1‖²)^{-1/2} g_1`, as printed in the PDF (the HTML rendering drops the root).
The paper's base case uses `L_0 = (1/√ε) I`; here `L_0 = √ε I` (see `factor`). -/
theorem factor_one_inv_apply {ε : ℝ} (hε : 0 < ε) (g : ℕ → n → ℝ) :
    (factor ε g 1)⁻¹ *ᵥ g 1 = (√(ε + g 1 ⬝ᵥ g 1))⁻¹ • g 1 := by
  have h := theorem_one hε g 0
  simp only [zero_add] at h
  rw [h, inv_factor_zero hε, smul_mulVec, one_mulVec, smul_dotProduct, dotProduct_smul, smul_smul]
  simp only [smul_eq_mul]
  have hs : 0 < √ε := Real.sqrt_pos.2 hε
  have hg := dot_self_nonneg (g 1)
  have hE : (√ε)⁻¹ * ((√ε)⁻¹ * (g 1 ⬝ᵥ g 1)) = g 1 ⬝ᵥ g 1 / ε := by
    have : √ε * √ε = ε := Real.mul_self_sqrt hε.le
    field_simp
    rw [Real.sq_sqrt hε.le]
    ring
  have hroot : √(1 + g 1 ⬝ᵥ g 1 / ε) * √ε = √(ε + g 1 ⬝ᵥ g 1) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  rw [hE, ← hroot, mul_inv]

/-! ### Lemma 1: the low-rank representation of `L_t⁻¹` -/

omit [Fintype n] [DecidableEq n] in
/-- Appending one column: the matrix `[M, v]`. -/
def appendCol {k : ℕ} (M : Matrix n (Fin k) ℝ) (v : n → ℝ) : Matrix n (Fin (k + 1)) ℝ :=
  Matrix.of fun i => Fin.snoc (α := fun _ => ℝ) (M i) (v i)

omit [Fintype n] [DecidableEq n] in
private theorem appendCol_mul_transpose {k : ℕ} (P Q : Matrix n (Fin k) ℝ) (a b : n → ℝ) :
    appendCol P a * (appendCol Q b)ᵀ = P * Qᵀ + vecMulVec a b := by
  ext i j
  simp [appendCol, Matrix.mul_apply, Fin.sum_univ_castSucc, vecMulVec_apply]

/-- The factors `(P_t, Q_t)` of Lemma 1 of arXiv 2508.21106: `P_0 = Q_0 = ∅`,
`P_{t+1} = [P_t, β_{t+1} ḡ_{t+1}]`, `Q_{t+1} = [Q_t, (I - Q_t P_tᵀ) ḡ_{t+1}]`. -/
noncomputable def factorsPQ (ε : ℝ) (g : ℕ → n → ℝ) :
    (t : ℕ) → Matrix n (Fin t) ℝ × Matrix n (Fin t) ℝ
  | 0 => (0, 0)
  | t + 1 =>
    (appendCol (factorsPQ ε g t).1 (beta (gbar ε g t ⬝ᵥ gbar ε g t) • gbar ε g t),
      appendCol (factorsPQ ε g t).2
        ((1 - (factorsPQ ε g t).2 * (factorsPQ ε g t).1ᵀ) *ᵥ gbar ε g t))

/-- `A_t = P_t Q_tᵀ`, arXiv 2508.21106, eq. (11). -/
noncomputable def stateA (ε : ℝ) (g : ℕ → n → ℝ) (t : ℕ) : Matrix n n ℝ :=
  (factorsPQ ε g t).1 * (factorsPQ ε g t).2ᵀ

/-- `A_0 = 0` in arXiv 2508.21106, since `P_0 = Q_0 = ∅`. -/
@[simp] theorem stateA_zero (ε : ℝ) (g : ℕ → n → ℝ) : stateA ε g 0 = 0 := by
  ext i j
  simp [stateA, factorsPQ, Matrix.mul_apply]

/-- The increment `ΔA_{t+1} = β_{t+1} ḡ_{t+1} ḡ_{t+1}ᵀ (I - P_t Q_tᵀ)`,
arXiv 2508.21106, eq. (12). -/
noncomputable def deltaA (ε : ℝ) (g : ℕ → n → ℝ) (t : ℕ) : Matrix n n ℝ :=
  beta (gbar ε g t ⬝ᵥ gbar ε g t) • (vecMulVec (gbar ε g t) (gbar ε g t) * (1 - stateA ε g t))

/-- arXiv 2508.21106, eq. (13): `P_{t+1} Q_{t+1}ᵀ = A_{t+1} = A_t + ΔA_{t+1}`. -/
theorem stateA_succ (ε : ℝ) (g : ℕ → n → ℝ) (t : ℕ) :
    stateA ε g (t + 1) = stateA ε g t + deltaA ε g t := by
  simp only [stateA, factorsPQ, deltaA]
  rw [appendCol_mul_transpose]
  congr 1
  have ht : (1 - (factorsPQ ε g t).1 * (factorsPQ ε g t).2ᵀ)ᵀ =
      1 - (factorsPQ ε g t).2 * (factorsPQ ε g t).1ᵀ := by
    simp [Matrix.transpose_sub, Matrix.transpose_mul]
  rw [vecMulVec_mul, ← ht, Matrix.mulVec_transpose]
  ext i j
  simp [vecMulVec_apply, mul_assoc]

/-- **Lemma 1** of arXiv 2508.21106: `L_t⁻¹ = (I - P_t Q_tᵀ) L_0⁻¹`, for the recursive factor of
eq. (8) and every `t` (the paper states it at `t + 1`; `t = 0` is the empty case).  The statement
is as printed.  The paper's proof expands `(I - P_t Q_tᵀ) L_0⁻¹ (I - β ḡ ḡᵀ)`, in the wrong order;
it should be `(I - β ḡ ḡᵀ) (I - P_t Q_tᵀ) L_0⁻¹`, which is what the printed `Q_{t+1}` encodes. -/
theorem lemma_one {ε : ℝ} (hε : 0 < ε) (g : ℕ → n → ℝ) (t : ℕ) :
    (factor ε g t)⁻¹ =
      (1 - (factorsPQ ε g t).1 * (factorsPQ ε g t).2ᵀ) * (factor ε g 0)⁻¹ := by
  induction t with
  | zero =>
    have : (factorsPQ ε g 0).1 * (factorsPQ ε g 0).2ᵀ = 0 := stateA_zero ε g
    rw [this, sub_zero, Matrix.one_mul]
  | succ t ih =>
    have h1 := stateA_succ ε g t
    simp only [stateA] at h1
    rw [inv_factor_succ hε, ih, h1, ← Matrix.mul_assoc]
    congr 1
    simp only [deltaA, stateA, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub,
      Matrix.mul_one]
    module

/-- **Algorithm 2 of arXiv 2508.21106, line 5**, the matrix-free transformed gradient:
`ḡ_{t+1} = L_t⁻¹ g_{t+1} = (I - P_t Q_tᵀ) L_0⁻¹ g_{t+1}`, with `L_0⁻¹ = ε^{-1/2} I`. -/
theorem gbar_eq {ε : ℝ} (hε : 0 < ε) (g : ℕ → n → ℝ) (t : ℕ) :
    gbar ε g t = (1 - stateA ε g t) *ᵥ ((√ε)⁻¹ • g (t + 1)) := by
  rw [gbar, lemma_one hε, inv_factor_zero hε, ← mulVec_mulVec, smul_mulVec, one_mulVec]
  rfl

/-! ### The isometry -/

/-- arXiv 2508.21106, §3.2: for any invertible factor `G = L Lᵀ`,
`‖L⁻¹ g‖² = gᵀ G⁻¹ g`.  No triangularity is needed. -/
theorem isometry_inv {L G : Matrix n n ℝ} (hL : IsUnit L) (hG : L * Lᵀ = G) (v : n → ℝ) :
    (L⁻¹ *ᵥ v) ⬝ᵥ (L⁻¹ *ᵥ v) = v ⬝ᵥ (G⁻¹ *ᵥ v) := by
  have hd : IsUnit L.det := (Matrix.isUnit_iff_isUnit_det _).1 hL
  rw [← hG, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv, ← mulVec_mulVec,
    Matrix.mulVec_transpose, dotProduct_comm v, ← Matrix.dotProduct_mulVec]

/-- The principal root `G^{-1/2}`, as a spectral function of `G`. -/
noncomputable def invSqrt (G : Matrix n n ℝ) : Matrix n n ℝ := cfc (fun x : ℝ => (√x)⁻¹) G

/-- **The isometry** of arXiv 2508.21106, §3.2:
`‖G^{-1/2} g‖² = gᵀ G⁻¹ g = gᵀ (L Lᵀ)⁻¹ g = ‖L⁻¹ g‖²`, for every invertible factor `G = L Lᵀ`.
`G^{-1/2}` is the genuine principal root.  The paper only claims equality of norms, and the
vectors differ in general: compare `theorem_one` with
`theorem_one_false_for_triangular_cholesky`. -/
theorem isometry_invSqrt {L G : Matrix n n ℝ} (hL : IsUnit L) (hG : L * Lᵀ = G) (v : n → ℝ) :
    (invSqrt G *ᵥ v) ⬝ᵥ (invSqrt G *ᵥ v) = (L⁻¹ *ᵥ v) ⬝ᵥ (L⁻¹ *ᵥ v) := by
  have hPD : G.PosDef := by
    have := Matrix.PosDef.mul_conjTranspose_self L (Matrix.vecMul_injective_of_isUnit hL)
    rwa [conjTranspose_eq_transpose_of_trivial, hG] at this
  have hH : IsSelfAdjoint G := hPD.isHermitian
  have hpos : ∀ x ∈ spectrum ℝ G, 0 < x := by
    intro x hx
    rw [hPD.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hPD.eigenvalues_pos i
  have hfin : (spectrum ℝ G).Finite := Matrix.finite_real_spectrum
  set R := invSqrt G with hR
  have hRs : IsSelfAdjoint R := cfc_predicate _ _
  have hRt : Rᵀ = R := by
    have := hRs.star_eq
    rwa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have hRR : R * R * G = 1 := by
    have h1 : R * R = cfc (fun x : ℝ => (√x)⁻¹ * (√x)⁻¹) G :=
      (cfc_mul _ _ G (hfin.continuousOn _) (hfin.continuousOn _)).symm
    calc R * R * G = cfc (fun x : ℝ => (√x)⁻¹ * (√x)⁻¹) G * cfc (fun x : ℝ => x) G := by
          rw [h1, cfc_id' ℝ G]
      _ = cfc (fun x : ℝ => (√x)⁻¹ * (√x)⁻¹ * x) G :=
          (cfc_mul _ _ G (hfin.continuousOn _) (hfin.continuousOn _)).symm
      _ = cfc (fun _ : ℝ => (1 : ℝ)) G := by
          refine cfc_congr fun x hx => ?_
          have hx0 := hpos x hx
          have hs : 0 < √x := Real.sqrt_pos.2 hx0
          have hxx : √x * √x = x := Real.mul_self_sqrt hx0.le
          change (√x)⁻¹ * (√x)⁻¹ * x = 1
          rw [← mul_inv, hxx, inv_mul_cancel₀ hx0.ne']
      _ = 1 := cfc_const_one ℝ G
  have hinv : G⁻¹ = R * R := Matrix.inv_eq_left_inv hRR
  have hdot : (R *ᵥ v) ⬝ᵥ (R *ᵥ v) = v ⬝ᵥ (G⁻¹ *ᵥ v) := by
    calc (R *ᵥ v) ⬝ᵥ (R *ᵥ v) = (v ᵥ* R) ⬝ᵥ (R *ᵥ v) := by
          rw [← Matrix.mulVec_transpose, hRt]
      _ = v ⬝ᵥ (R *ᵥ (R *ᵥ v)) := (Matrix.dotProduct_mulVec _ _ _).symm
      _ = v ⬝ᵥ (G⁻¹ *ᵥ v) := by rw [hinv, mulVec_mulVec]
  rw [hdot, isometry_inv hL hG]

/-- **Algorithm 2 of arXiv 2508.21106, line 7**, for the exact state: the update
`ḡ_{t+1} / √(1 + ‖ḡ_{t+1}‖²)` equals `L_{t+1}⁻¹ g_{t+1}` and has the norm of the full-matrix AdaGrad
direction `G_{t+1}^{-1/2} g_{t+1}`.  This is the "equivalence under the isometry condition" of the
paper: only norms agree. -/
theorem adagram_update_norm {ε : ℝ} (hε : 0 < ε) (g : ℕ → n → ℝ) (t : ℕ) :
    let d := (√(1 + gbar ε g t ⬝ᵥ gbar ε g t))⁻¹ • gbar ε g t
    d = (factor ε g (t + 1))⁻¹ *ᵥ g (t + 1) ∧
      d ⬝ᵥ d = (invSqrt (precond ε g (t + 1)) *ᵥ g (t + 1)) ⬝ᵥ
        (invSqrt (precond ε g (t + 1)) *ᵥ g (t + 1)) := by
  intro d
  have h : d = (factor ε g (t + 1))⁻¹ *ᵥ g (t + 1) := (theorem_one hε g t).symm
  refine ⟨h, ?_⟩
  rw [isometry_invSqrt (isUnit_factor hε g (t + 1)) (factor_mul_transpose hε g (t + 1)), h]

end Recursion

/-! ### The spectral identity for `δ I + U Λ Uᵀ` -/

section Spectral

variable {n r : Type*} [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]

/-- The polynomial case of `spectral_lowRank`. -/
private theorem aeval_lowRank (δ : ℝ) {U : Matrix n r ℝ} (hU : Uᵀ * U = 1) (Λ : Matrix r r ℝ)
    (p : Polynomial ℝ) :
    Polynomial.aeval (δ • (1 : Matrix n n ℝ) + U * Λ * Uᵀ) p =
      p.eval δ • (1 - U * Uᵀ) + U * Polynomial.aeval (δ • (1 : Matrix r r ℝ) + Λ) p * Uᵀ := by
  have hPU : (1 - U * Uᵀ) * U = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one, sub_self]
  have hUUB : ∀ B B' : Matrix r r ℝ, U * B * Uᵀ * (U * B' * Uᵀ) = U * (B * B') * Uᵀ := by
    intro B B'
    calc U * B * Uᵀ * (U * B' * Uᵀ) = U * B * (Uᵀ * U) * B' * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = U * (B * B') * Uᵀ := by rw [hU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hmul : ∀ (c : ℝ) (B : Matrix r r ℝ),
      (c • (1 - U * Uᵀ) + U * B * Uᵀ) * (δ • (1 : Matrix n n ℝ) + U * Λ * Uᵀ) =
        (c * δ) • (1 - U * Uᵀ) + U * (B * (δ • (1 : Matrix r r ℝ) + Λ)) * Uᵀ := by
    intro c B
    have h1 : (1 - U * Uᵀ) * (U * Λ * Uᵀ) = 0 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPU, Matrix.zero_mul, Matrix.zero_mul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
      h1, hUUB, smul_zero]
    module
  induction p using Polynomial.induction_on with
  | C a =>
    have : U * (a • (1 : Matrix r r ℝ)) * Uᵀ = a • (U * Uᵀ) := by
      simp [Matrix.mul_smul, Matrix.smul_mul]
    simp only [Polynomial.aeval_C, Polynomial.eval_C, Algebra.algebraMap_eq_smul_one, this]
    module
  | add p q hp hq =>
    simp only [map_add, Polynomial.eval_add, hp, hq, add_smul, Matrix.mul_add, Matrix.add_mul]
    abel
  | monomial k a ih =>
    have e : Polynomial.C a * Polynomial.X ^ (k + 1) =
        (Polynomial.C a * Polynomial.X ^ k) * (Polynomial.X : Polynomial ℝ) := by
      rw [pow_succ, mul_assoc]
    generalize Polynomial.C a * Polynomial.X ^ k = q at ih e
    rw [e, map_mul, map_mul, Polynomial.aeval_X, Polynomial.aeval_X, ih, hmul,
      Polynomial.eval_mul, Polynomial.eval_X]

private theorem isSelfAdjoint_of_transpose {k : Type*} {X : Matrix k k ℝ}
    (h : Xᵀ = X) : IsSelfAdjoint X := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, h]

/-- **Low-rank full-matrix preconditioner** (arXiv 2508.21106, header item; the paper itself works
with Cholesky factors instead, this is the survey's reading of its abstract).  For `U` with
orthonormal columns, `P = U Uᵀ`, symmetric `Λ` and **any** function `φ : ℝ → ℝ`, with `φ` applied
through the functional calculus (`cfc`):
`φ(δ I + U Λ Uᵀ) = φ(δ) (I - P) + U φ(δ I + Λ) Uᵀ`.
No continuity of `φ` and no sign of `δ` or `Λ` is needed, because matrix spectra are finite.
The proof interpolates `φ` by a polynomial on the spectra. -/
theorem spectral_lowRank (φ : ℝ → ℝ) (δ : ℝ) {U : Matrix n r ℝ} (hU : Uᵀ * U = 1)
    {Λ : Matrix r r ℝ} (hΛ : Λ.IsSymm) :
    cfc φ (δ • (1 : Matrix n n ℝ) + U * Λ * Uᵀ) =
      φ δ • (1 - U * Uᵀ) + U * cfc φ (δ • (1 : Matrix r r ℝ) + Λ) * Uᵀ := by
  classical
  have hΛ' : Λᵀ = Λ := hΛ
  have hX : IsSelfAdjoint (δ • (1 : Matrix n n ℝ) + U * Λ * Uᵀ) := by
    refine isSelfAdjoint_of_transpose ?_
    simp [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul, hΛ', Matrix.mul_assoc]
  have hY : IsSelfAdjoint (δ • (1 : Matrix r r ℝ) + Λ) := by
    refine isSelfAdjoint_of_transpose ?_
    simp [Matrix.transpose_add, Matrix.transpose_smul, hΛ']
  set X := δ • (1 : Matrix n n ℝ) + U * Λ * Uᵀ with hXd
  set Y := δ • (1 : Matrix r r ℝ) + Λ with hYd
  have fX : (spectrum ℝ X).Finite := Matrix.finite_real_spectrum
  have fY : (spectrum ℝ Y).Finite := Matrix.finite_real_spectrum
  let s : Finset ℝ := fX.toFinset ∪ fY.toFinset ∪ {δ}
  let p : Polynomial ℝ := Lagrange.interpolate s id φ
  have hp : ∀ x ∈ s, p.eval x = φ x := fun x hx =>
    Lagrange.eval_interpolate_at_node φ (Function.injective_id.injOn) hx
  have h1 : cfc φ X = Polynomial.aeval X p := by
    rw [← cfc_polynomial p X hX]
    exact cfc_congr fun x hx => (hp x (by simp [s, hx])).symm
  have h2 : cfc φ Y = Polynomial.aeval Y p := by
    rw [← cfc_polynomial p Y hY]
    exact cfc_congr fun x hx => (hp x (by simp [s, hx])).symm
  rw [h1, h2, ← hp δ (by simp [s])]
  exact aeval_lowRank δ hU Λ p

/-- **The `O(n r)` form** of `spectral_lowRank` (arXiv 2508.21106, header item):
`φ(δ I + U Λ Uᵀ) v = φ(δ) (v - U (Uᵀ v)) + U (φ(δ I + Λ) (Uᵀ v))`, which needs two products with
an `n × r` matrix and one `r × r` matrix-vector product. -/
theorem spectral_lowRank_mulVec (φ : ℝ → ℝ) (δ : ℝ) {U : Matrix n r ℝ} (hU : Uᵀ * U = 1)
    {Λ : Matrix r r ℝ} (hΛ : Λ.IsSymm) (v : n → ℝ) :
    cfc φ (δ • (1 : Matrix n n ℝ) + U * Λ * Uᵀ) *ᵥ v =
      φ δ • (v - U *ᵥ (Uᵀ *ᵥ v)) + U *ᵥ (cfc φ (δ • (1 : Matrix r r ℝ) + Λ) *ᵥ (Uᵀ *ᵥ v)) := by
  rw [spectral_lowRank φ δ hU hΛ, add_mulVec, smul_mulVec, sub_mulVec, one_mulVec]
  simp only [mulVec_mulVec, Matrix.mul_assoc]

/-- `spectral_lowRank` for `φ(x) = x^{-1/2}`, the AdaGrad direction of arXiv 2508.21106, eq. (1),
in the notation `invSqrt`. -/
theorem invSqrt_lowRank (δ : ℝ) {U : Matrix n r ℝ} (hU : Uᵀ * U = 1)
    {Λ : Matrix r r ℝ} (hΛ : Λ.IsSymm) :
    invSqrt (δ • (1 : Matrix n n ℝ) + U * Λ * Uᵀ) =
      (√δ)⁻¹ • (1 - U * Uᵀ) + U * invSqrt (δ • (1 : Matrix r r ℝ) + Λ) * Uᵀ :=
  spectral_lowRank _ δ hU hΛ

end Spectral

/-! ### Algorithm 1: the projector-splitting step on an increment -/

section AlgorithmOne

open scoped LeanDLRA.Frobenius

variable {m k r : Type*} [Fintype m] [Fintype k] [Fintype r] [DecidableEq r]

/-- **Algorithm 1** of arXiv 2508.21106 (from Lubich–Oseledets, arXiv 1301.1058, §3.2): from
`Y₀ = U₀ S₀ V₀ᵀ` and an increment `ΔA`,
`K₁ = U₀ S₀ + ΔA V₀ = U₁ Ŝ₁` (QR), `S̃₀ = Ŝ₁ - U₁ᵀ ΔA V₀`,
`L₁ = V₀ S̃₀ᵀ + ΔAᵀ U₁ = V₁ S₁ᵀ` (QR), and `Y₁ = U₁ S₁ V₁ᵀ`.  Only the orthonormality of the
QR factors is required. -/
structure IsAlgorithm1Step (ΔA : Matrix m k ℝ) (U₀ : Matrix m r ℝ) (S₀ : Matrix r r ℝ)
    (V₀ : Matrix k r ℝ) (Ŝ₁ : Matrix r r ℝ) (U₁ : Matrix m r ℝ) (S₁ : Matrix r r ℝ)
    (V₁ : Matrix k r ℝ) : Prop where
  orthoU : U₁ᵀ * U₁ = 1
  qrK : U₁ * Ŝ₁ = U₀ * S₀ + ΔA * V₀
  orthoV : V₁ᵀ * V₁ = 1
  qrL : V₁ * S₁ᵀ = V₀ * (Ŝ₁ - U₁ᵀ * ΔA * V₀)ᵀ + ΔAᵀ * U₁

variable {ΔA : Matrix m k ℝ} {U₀ U₁ : Matrix m r ℝ} {S₀ S₁ Ŝ₁ : Matrix r r ℝ}
  {V₀ V₁ : Matrix k r ℝ}

/-- Algorithm 1 of arXiv 2508.21106 is the library's KSL step for the constant field `ΔA` over a
unit time step. -/
theorem IsAlgorithm1Step.isKSLStep (h : IsAlgorithm1Step ΔA U₀ S₀ V₀ Ŝ₁ U₁ S₁ V₁) :
    Symmetry.IsKSLStep (fun _ _ => ΔA) 0 1 U₀ S₀ V₀ U₁ S₁ V₁ :=
  Symmetry.isKSLStep_const (Ŝ₁ := Ŝ₁) h.orthoU (by simpa using h.qrK.symm) h.orthoV
    (by simpa [sub_eq_add_neg] using h.qrL.symm)

/-- The closed form of Algorithm 1 of arXiv 2508.21106:
`Y₁ = Y₀ + ΔA Q₀ + P₁ ΔA (I - Q₀)`, with `P₁ = U₁ U₁ᵀ`, `Q₀ = V₀ V₀ᵀ`. -/
theorem IsAlgorithm1Step.eq [DecidableEq k] (h : IsAlgorithm1Step ΔA U₀ S₀ V₀ Ŝ₁ U₁ S₁ V₁) :
    U₁ * S₁ * V₁ᵀ = U₀ * S₀ * V₀ᵀ + (ΔA * (V₀ * V₀ᵀ) + U₁ * U₁ᵀ * ΔA * (1 - V₀ * V₀ᵀ)) := by
  simpa using h.isKSLStep.eq_const zero_le_one

/-- Exactness of Algorithm 1 of arXiv 2508.21106 (the paper makes no such claim; this is
`Exactness.ksl_exact`, Lubich–Oseledets Theorem 4.1): if `Y₀ = U₀ S₀ V₀ᵀ` with `V₀ᵀ V₀ = I`, and
`Y₀ + ΔA = U S Vᵀ` has rank at most `r` with `Vᵀ V₀` invertible, then `Y₁ = Y₀ + ΔA`. -/
theorem IsAlgorithm1Step.exact (h : IsAlgorithm1Step ΔA U₀ S₀ V₀ Ŝ₁ U₁ S₁ V₁)
    (hV₀ : V₀ᵀ * V₀ = 1) {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix k r ℝ}
    (hA₁ : U₀ * S₀ * V₀ᵀ + ΔA = U * S * Vᵀ) (hV : IsUnit (Vᵀ * V₀)) :
    U₁ * S₁ * V₁ᵀ = U₀ * S₀ * V₀ᵀ + ΔA := by
  have hd : (U₀ * S₀ * V₀ᵀ + ΔA) - U₀ * S₀ * V₀ᵀ = ΔA := add_sub_cancel_left _ _
  exact Exactness.ksl_exact (A₀ := U₀ * S₀ * V₀ᵀ) (A₁ := U₀ * S₀ * V₀ᵀ + ΔA) hV₀ rfl hA₁ hV
    (K₁ := U₀ * S₀ + ΔA * V₀) (St₀ := Ŝ₁ - U₁ᵀ * ΔA * V₀)
    (L₁ := V₀ * (Ŝ₁ - U₁ᵀ * ΔA * V₀)ᵀ + ΔAᵀ * U₁) (by rw [hd]) h.orthoU h.qrK (by rw [hd])
    (by rw [hd]) h.qrL

end AlgorithmOne

/-! ### Algorithm 2 with the low-rank state -/

section AlgorithmTwo

variable {n r : Type*} [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]

/-- The increment that Algorithm 2 of arXiv 2508.21106 hands to Algorithm 1 from a state `Y`
(standing for `P Qᵀ`) and a new gradient `v`: `ΔA = β w wᵀ (I - Y)`, `w = (I - Y) L_0⁻¹ v`.
This is the undamped eq. (12).  The damped variant (14), `A_{t+1} = μ A_t + (1 - μ) ΔA_{t+1}`, is
presented in the paper as a heuristic without a claim of exactness and is not treated here. -/
noncomputable def algIncrement (ε : ℝ) (Y : Matrix n n ℝ) (v : n → ℝ) : Matrix n n ℝ :=
  beta (((1 - Y) *ᵥ ((√ε)⁻¹ • v)) ⬝ᵥ ((1 - Y) *ᵥ ((√ε)⁻¹ • v))) •
    (vecMulVec ((1 - Y) *ᵥ ((√ε)⁻¹ • v)) ((1 - Y) *ᵥ ((√ε)⁻¹ • v)) * (1 - Y))

private theorem algIncrement_stateA {ε : ℝ} (hε : 0 < ε) (g : ℕ → n → ℝ) (t : ℕ) :
    algIncrement ε (stateA ε g t) (g (t + 1)) = deltaA ε g t := by
  simp only [algIncrement, deltaA, ← gbar_eq hε]

/-- **Algorithm 2 of arXiv 2508.21106 is exact while `A_t` has rank at most `r`** (no such claim
is in the paper, which gives no error analysis).  Run Algorithm 1 from `Y_0 = 0` on the increments
of eq. (12), computed from the current low-rank state.  If every `A_{t+1} = P_{t+1} Q_{t+1}ᵀ` has
a factorization `X D Zᵀ` with `r` columns and `Zᵀ V_t` invertible, then the state is exact:
`Y_t = A_t`, and hence `L_t⁻¹ = (I - Y_t) L_0⁻¹`.  See `algorithm2_exact_parallel` for instances. -/
theorem algorithm2_exact {ε : ℝ} (hε : 0 < ε) (g : ℕ → n → ℝ) {U V : ℕ → Matrix n r ℝ}
    {S Ŝ : ℕ → Matrix r r ℝ} (hV0 : (V 0)ᵀ * V 0 = 1) (h0 : U 0 * S 0 * (V 0)ᵀ = 0)
    (hstep : ∀ t, IsAlgorithm1Step (algIncrement ε (U t * S t * (V t)ᵀ) (g (t + 1)))
      (U t) (S t) (V t) (Ŝ t) (U (t + 1)) (S (t + 1)) (V (t + 1)))
    (hrank : ∀ t, ∃ (X Z : Matrix n r ℝ) (D : Matrix r r ℝ),
      stateA ε g (t + 1) = X * D * Zᵀ ∧ IsUnit (Zᵀ * V t)) (t : ℕ) :
    U t * S t * (V t)ᵀ = stateA ε g t ∧
      (factor ε g t)⁻¹ = (1 - U t * S t * (V t)ᵀ) * (factor ε g 0)⁻¹ := by
  have hV : ∀ t, (V t)ᵀ * V t = 1 := by
    intro t
    cases t with
    | zero => exact hV0
    | succ t => exact (hstep t).orthoV
  have key : ∀ t, U t * S t * (V t)ᵀ = stateA ε g t := by
    intro t
    induction t with
    | zero => simpa using h0
    | succ t ih =>
      obtain ⟨X, Z, D, hA, hZ⟩ := hrank t
      have hinc : algIncrement ε (U t * S t * (V t)ᵀ) (g (t + 1)) = deltaA ε g t := by
        rw [ih, algIncrement_stateA hε]
      have hsum : U t * S t * (V t)ᵀ + algIncrement ε (U t * S t * (V t)ᵀ) (g (t + 1)) =
          stateA ε g (t + 1) := by
        rw [hinc, ih, stateA_succ]
      rw [(hstep t).exact (hV t) (hsum.trans hA) hZ, hsum]
  refine ⟨key t, ?_⟩
  rw [key t]
  exact lemma_one hε g t

end AlgorithmTwo

/-! ### Symmetry and positive semidefiniteness for the BUG integrator -/

section BUG

open scoped LeanDLRA.Frobenius

variable {n k r : Type*} [Fintype n] [Fintype k] [Fintype r]

/-- A curve with symmetric right derivative and symmetric start stays symmetric. -/
private theorem isSymm_of_hasDerivWithinAt {S S' : ℝ → Matrix k k ℝ} {t₀ t₁ : ℝ}
    (hc : ContinuousOn S (Icc t₀ t₁))
    (hd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt S (S' t) (Ici t) t)
    (hs : ∀ t ∈ Ico t₀ t₁, (S' t).IsSymm) (h0 : (S t₀).IsSymm) :
    ∀ t ∈ Icc t₀ t₁, (S t).IsSymm := by
  have hDc : ContinuousOn (fun t => (S t)ᵀ - S t) (Icc t₀ t₁) :=
    (Frobenius.transposeCLM.continuous.comp_continuousOn hc).sub hc
  have hDd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => (S t)ᵀ - S t) 0 (Ici t) t := by
    intro t ht
    have h1 := (Frobenius.transposeCLM (m := k) (n := k)).hasFDerivAt.comp_hasDerivWithinAt t
      (hd t ht)
    have h2 := h1.sub (hd t ht)
    have e : Frobenius.transposeCLM (S' t) - S' t = 0 := by
      rw [Frobenius.transposeCLM_apply, (hs t ht).eq, sub_self]
    rw [e] at h2
    exact h2
  intro t ht
  have h := constant_of_has_deriv_right_zero hDc hDd t ht
  simp only [h0.eq, sub_self] at h
  exact sub_eq_zero.1 h

/-- A curve with positive semidefinite right derivative and positive semidefinite start ends
positive semidefinite. -/
private theorem posSemidef_of_hasDerivWithinAt {S S' : ℝ → Matrix k k ℝ} {t₀ t₁ : ℝ}
    (ht : t₀ ≤ t₁) (hc : ContinuousOn S (Icc t₀ t₁))
    (hd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt S (S' t) (Ici t) t)
    (hs : ∀ t ∈ Ico t₀ t₁, (S' t).PosSemidef) (h0 : (S t₀).PosSemidef) :
    (S t₁).PosSemidef := by
  have hsymm : (S t₁).IsSymm := by
    refine isSymm_of_hasDerivWithinAt hc hd (fun t ht' => ?_) ?_ t₁ ⟨ht, le_rfl⟩
    · have := (hs t ht').isHermitian
      rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    · have := h0.isHermitian
      rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hH : (S t₁).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact hsymm
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_
  let ℓ₀ : Matrix k k ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun M => x ⬝ᵥ (M *ᵥ x)
      map_add' := fun A B => by rw [add_mulVec, dotProduct_add]
      map_smul' := fun c A => by rw [smul_mulVec, dotProduct_smul]; rfl }
  let ℓ : Matrix k k ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ℓ₀
  have hℓ : ∀ M, ℓ M = x ⬝ᵥ (M *ᵥ x) := fun _ => rfl
  have hnn : ∀ M : Matrix k k ℝ, M.PosSemidef → 0 ≤ ℓ M := by
    intro M hM
    have := hM.dotProduct_mulVec_nonneg x
    simpa [hℓ] using this
  have hmain := image_le_of_deriv_right_le_deriv_boundary (f := fun t => -ℓ (S t))
    (f' := fun t => -ℓ (S' t)) (a := t₀) (b := t₁) (B := fun _ => -ℓ (S t₀)) (B' := fun _ => 0)
    (ℓ.continuous.comp_continuousOn hc).neg
    (fun t ht' => (ℓ.hasFDerivAt.comp_hasDerivWithinAt t (hd t ht')).neg) le_rfl
    continuousOn_const (fun t _ => hasDerivWithinAt_const t _ _)
    (fun t ht' => neg_nonpos.2 (hnn _ (hs t ht'))) ⟨ht, le_rfl⟩
  have h2 : 0 ≤ ℓ (S t₁) := le_trans (hnn _ h0) (neg_le_neg_iff.1 hmain)
  simpa [hℓ] using h2

private theorem posSemidef_mul_mul_transpose {p : Type*} [Finite p] {S : Matrix k k ℝ}
    (hS : S.PosSemidef) (B : Matrix p k ℝ) : (B * S * Bᵀ).PosSemidef := by
  have := hS.mul_mul_conjTranspose_same B
  rwa [conjTranspose_eq_transpose_of_trivial] at this

private theorem posSemidef_transpose_mul_mul {p : Type*} [Finite p] {S : Matrix k k ℝ}
    (hS : S.PosSemidef) (B : Matrix k p ℝ) : (Bᵀ * S * B).PosSemidef := by
  have := hS.conjTranspose_mul_mul_same B
  rwa [conjTranspose_eq_transpose_of_trivial] at this

/-- **PSD preservation of the BUG core** (arXiv 2508.21106, header item; not claimed in the paper,
whose `A_t` is not a PSD accumulator).  If `F(t, Y)` is positive semidefinite for all `t`, `Y`
(e.g. `F(t, Y) = g(t) g(t)ᵀ`) and `S₀` is positive semidefinite, then the S-step
`S' = U₁ᵀ F(t, U₁ S U₁ᵀ) U₁`, `S(t₀) = M S₀ Mᵀ`, `M = U₁ᵀ U₀`, stays positive semidefinite, and so
does `Y₁ = U₁ S(t₁) U₁ᵀ`.  No Lipschitz, orthonormality or equivariance assumption is needed. -/
theorem bug_core_posSemidef {F : ℝ → Matrix n n ℝ → Matrix n n ℝ} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hP : ∀ t Y, (F t Y).PosSemidef) {U₀ : Matrix n r ℝ} {S₀ : Matrix r r ℝ}
    (hS₀ : S₀.PosSemidef) {U₁ : Matrix n k ℝ} {S : ℝ → Matrix k k ℝ}
    (hS : ODESolution (Symmetry.sField U₁ U₁ F) S t₀ t₁)
    (hS0 : S t₀ = U₁ᵀ * U₀ * S₀ * (U₁ᵀ * U₀)ᵀ) :
    (S t₁).PosSemidef ∧ (U₁ * S t₁ * U₁ᵀ).PosSemidef := by
  have h0 : (S t₀).PosSemidef := by
    rw [hS0]
    exact posSemidef_mul_mul_transpose hS₀ _
  have h1 : (S t₁).PosSemidef :=
    posSemidef_of_hasDerivWithinAt ht hS.cont hS.deriv
      (fun t _ => posSemidef_transpose_mul_mul (hP t _) U₁) h0
  exact ⟨h1, posSemidef_mul_mul_transpose h1 U₁⟩

/-- **DLRA maintenance of a PSD accumulator by BUG** (arXiv 2508.21106, header item), for
`F(t, Y) = Ȧ(t)` with `Ȧ(t)` positive semidefinite, `U₀ = V₀`, and `Y₀ = U₀ S₀ U₀ᵀ = A(t₀)`
with `S₀` positive semidefinite.  One BUG step with `V₁ = U₁` has a positive semidefinite
core and is exact when `A(t₁) = U D Uᵀ` has rank at most `r` with `Uᵀ U₀` invertible.  The L-step
is not listed since here it coincides with the K-step, which is why `V₁ = U₁` is legitimate.
Symmetry in general is `Symmetry.bug_isTwistSymm`, exactness in general `Exactness.bug_exact_ode`.
The paper's own integrator does not have these properties: `algorithm1_not_symmetric`. -/
theorem bug_maintenance [DecidableEq r] {F : ℝ → Matrix n n ℝ → Matrix n n ℝ}
    {A : ℝ → Matrix n n ℝ} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) (hA : IsDerivRHS F A t₀ t₁)
    (hP : ∀ t Y, (F t Y).PosSemidef) {U₀ : Matrix n r ℝ} {S₀ : Matrix r r ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hS₀ : S₀.PosSemidef) (hY₀ : U₀ * S₀ * U₀ᵀ = A t₀)
    {K : ℝ → Matrix n r ℝ} (hK : ODESolution (Symmetry.kField U₀ F) K t₀ t₁)
    (hK₀ : K t₀ = U₀ * S₀) {U₁ : Matrix n k ℝ} (hU₁ : U₁ * U₁ᵀ * K t₁ = K t₁)
    {S : ℝ → Matrix k k ℝ} (hS : ODESolution (Symmetry.sField U₁ U₁ F) S t₀ t₁)
    (hS0 : S t₀ = U₁ᵀ * U₀ * S₀ * (U₁ᵀ * U₀)ᵀ)
    {U : Matrix n r ℝ} {D : Matrix r r ℝ} (hA₁ : A t₁ = U * D * Uᵀ) (hU : IsUnit (Uᵀ * U₀)) :
    (S t₁).PosSemidef ∧ U₁ * S t₁ * U₁ᵀ = A t₁ := by
  classical
  obtain ⟨h1, -⟩ := bug_core_posSemidef ht hP hS₀ hS hS0
  refine ⟨h1, ?_⟩
  have hmem : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have hSym0 : S₀ᵀ = S₀ := by
    have := hS₀.isHermitian
    rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hAs : (A t₁ - A t₀)ᵀ = A t₁ - A t₀ := by
    have h0s : (A t₀).IsSymm := by
      rw [← hY₀, Matrix.IsSymm]
      simp [Matrix.transpose_mul, hSym0, Matrix.mul_assoc]
    have h1s := isSymm_of_hasDerivWithinAt (S' := fun t => F t 0) hA.cont
      (fun t ht' => hA.deriv t ht' 0) (fun t _ => by
        have := (hP t 0).isHermitian
        rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this) h0s t₁ hmem
    rw [Matrix.transpose_sub, h1s.eq, h0s.eq]
  have eK := Exactness.kStepODE_eq_add hA hK t₁ hmem
  have eS := Exactness.factorODE_eq_add hA U₁ᵀ U₁ (fun S => U₁ * S * U₁ᵀ) (fun _ _ => rfl) hS
    t₁ hmem
  rw [hK₀] at eK
  rw [hS0] at eS
  have eL : K t₁ = U₀ * S₀ᵀ + (A t₁ - A t₀)ᵀ * U₀ := by rw [hSym0, hAs]; exact eK
  exact Exactness.bug_exact hU₀ hU₀ hY₀ hA₁ hU hU eK eL hU₁ hU₁ eS

/-- **One BUG step on a PSD increment** (arXiv 2508.21106, header item, outer-product increments in
the discrete form): `K₁ = U₀ S₀ + ΔA U₀ = U₁ R₁`, `S₁ = M S₀ Mᵀ + U₁ᵀ ΔA U₁`, `M = U₁ᵀ U₀`.
The core `S₁` and the result `Y₁ = U₁ S₁ U₁ᵀ` are positive semidefinite, and `Y₁ = Y₀ + ΔA`
whenever `Y₀ + ΔA = U D Uᵀ` has rank at most `r` with `Uᵀ U₀` invertible. -/
theorem bug_increment_step [DecidableEq k] [DecidableEq r] {ΔA : Matrix n n ℝ}
    (hΔ : ΔA.PosSemidef) {U₀ : Matrix n r ℝ} {S₀ : Matrix r r ℝ} (hU₀ : U₀ᵀ * U₀ = 1)
    (hS₀ : S₀.PosSemidef) {U₁ : Matrix n k ℝ} {R₁ : Matrix k r ℝ} (hU₁ : U₁ᵀ * U₁ = 1)
    (hQR : U₁ * R₁ = U₀ * S₀ + ΔA * U₀) {S₁ : Matrix k k ℝ}
    (hS₁ : S₁ = U₁ᵀ * U₀ * S₀ * (U₁ᵀ * U₀)ᵀ + U₁ᵀ * ΔA * U₁) :
    S₁.PosSemidef ∧ (U₁ * S₁ * U₁ᵀ).PosSemidef ∧
      ∀ {U : Matrix n r ℝ} {D : Matrix r r ℝ}, U₀ * S₀ * U₀ᵀ + ΔA = U * D * Uᵀ →
        IsUnit (Uᵀ * U₀) → U₁ * S₁ * U₁ᵀ = U₀ * S₀ * U₀ᵀ + ΔA := by
  have hP : S₁.PosSemidef := by
    rw [hS₁]
    exact (posSemidef_mul_mul_transpose hS₀ _).add (posSemidef_transpose_mul_mul hΔ U₁)
  refine ⟨hP, posSemidef_mul_mul_transpose hP U₁, ?_⟩
  intro U D hA hU
  have hSym0 : S₀ᵀ = S₀ := by
    have := hS₀.isHermitian
    rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hΔs : ΔAᵀ = ΔA := by
    have := hΔ.isHermitian
    rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hd : (U₀ * S₀ * U₀ᵀ + ΔA) - U₀ * S₀ * U₀ᵀ = ΔA := add_sub_cancel_left _ _
  have hcap := (Exactness.capture_of_qr hU₁ hQR).1
  exact Exactness.bug_exact (A₀ := U₀ * S₀ * U₀ᵀ) (A₁ := U₀ * S₀ * U₀ᵀ + ΔA) hU₀ hU₀ rfl hA hU hU
    (K₁ := U₀ * S₀ + ΔA * U₀) (L₁ := U₀ * S₀ + ΔA * U₀) (by rw [hd])
    (by rw [hd, hSym0, hΔs]) hcap hcap (by rw [hd]; exact hS₁)

/-- `bug_increment_step` for the outer-product increment `ΔA = g gᵀ` of AdaGrad, eq. (3) of
arXiv 2508.21106 (header item). -/
theorem bug_outerProduct_step [DecidableEq k] [DecidableEq r] (g : n → ℝ)
    {U₀ : Matrix n r ℝ} {S₀ : Matrix r r ℝ} (hU₀ : U₀ᵀ * U₀ = 1)
    (hS₀ : S₀.PosSemidef) {U₁ : Matrix n k ℝ} {R₁ : Matrix k r ℝ} (hU₁ : U₁ᵀ * U₁ = 1)
    (hQR : U₁ * R₁ = U₀ * S₀ + vecMulVec g g * U₀) {S₁ : Matrix k k ℝ}
    (hS₁ : S₁ = U₁ᵀ * U₀ * S₀ * (U₁ᵀ * U₀)ᵀ + U₁ᵀ * vecMulVec g g * U₁) :
    S₁.PosSemidef ∧ (U₁ * S₁ * U₁ᵀ).PosSemidef ∧
      ∀ {U : Matrix n r ℝ} {D : Matrix r r ℝ}, U₀ * S₀ * U₀ᵀ + vecMulVec g g = U * D * Uᵀ →
        IsUnit (Uᵀ * U₀) → U₁ * S₁ * U₁ᵀ = U₀ * S₀ * U₀ᵀ + vecMulVec g g := by
  have hΔ : (vecMulVec g g).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star g
  exact bug_increment_step hΔ hU₀ hS₀ hU₁ hQR hS₁

end BUG

/-! ### The whole accumulator, and the AdaGrad direction from the low-rank factors -/

section Accumulator

variable {n r : Type*} [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]

omit [DecidableEq n] in
/-- **DLRA maintenance of `∑ g gᵀ` by BUG, all steps** (arXiv 2508.21106, header item).  Run the
BUG steps of `bug_outerProduct_step` from `Y_0 = U_0 S_0 U_0ᵀ = 0` on the increments
`g_{t+1} g_{t+1}ᵀ`.  If every `∑_{τ ≤ t+1} g_τ g_τᵀ` has a factorization `X D Xᵀ` with `r` columns
and `Xᵀ U_t` invertible, then all cores are positive semidefinite and
`U_t S_t U_tᵀ = ∑_{τ ≤ t} g_τ g_τᵀ` for all `t`.  Instances: `bug_accumulator_parallel`. -/
theorem bug_accumulator_exact (g : ℕ → n → ℝ) {U : ℕ → Matrix n r ℝ} {S R : ℕ → Matrix r r ℝ}
    (hU : ∀ t, (U t)ᵀ * U t = 1) (hS0 : (S 0).PosSemidef) (h0 : U 0 * S 0 * (U 0)ᵀ = 0)
    (hQR : ∀ t, U (t + 1) * R t = U t * S t + vecMulVec (g (t + 1)) (g (t + 1)) * U t)
    (hS : ∀ t, S (t + 1) = (U (t + 1))ᵀ * U t * S t * ((U (t + 1))ᵀ * U t)ᵀ +
      (U (t + 1))ᵀ * vecMulVec (g (t + 1)) (g (t + 1)) * U (t + 1))
    (hrank : ∀ t, ∃ (X : Matrix n r ℝ) (D : Matrix r r ℝ),
      ∑ τ ∈ Finset.Icc 1 (t + 1), vecMulVec (g τ) (g τ) = X * D * Xᵀ ∧ IsUnit (Xᵀ * U t))
    (t : ℕ) :
    (S t).PosSemidef ∧ U t * S t * (U t)ᵀ = ∑ τ ∈ Finset.Icc 1 t, vecMulVec (g τ) (g τ) := by
  induction t with
  | zero => simpa [h0] using hS0
  | succ t ih =>
    obtain ⟨hP, hY⟩ := ih
    obtain ⟨hP', -, hex⟩ := bug_outerProduct_step (g (t + 1)) (hU t) hP (hU (t + 1)) (hQR t) (hS t)
    refine ⟨hP', ?_⟩
    obtain ⟨X, D, hA, hX⟩ := hrank t
    have hsum : ∑ τ ∈ Finset.Icc 1 (t + 1), vecMulVec (g τ) (g τ) =
        U t * S t * (U t)ᵀ + vecMulVec (g (t + 1)) (g (t + 1)) := by
      rw [Finset.sum_Icc_succ_top (by omega), hY]
    rw [hsum]
    exact hex (hsum.symm.trans hA) hX

/-- **The AdaGrad direction from the low-rank factors** (arXiv 2508.21106, both header items
together).  In the setting of `bug_accumulator_exact`,
`G_t^{-1/2} = ε^{-1/2} (I - U_t U_tᵀ) + U_t (ε I + S_t)^{-1/2} U_tᵀ`, for the genuine principal root
of the full-matrix preconditioner `G_t = ε I + ∑_{τ ≤ t} g_τ g_τᵀ`. -/
theorem bug_invSqrt_precond (ε : ℝ) (g : ℕ → n → ℝ) {U : ℕ → Matrix n r ℝ}
    {S R : ℕ → Matrix r r ℝ}
    (hU : ∀ t, (U t)ᵀ * U t = 1) (hS0 : (S 0).PosSemidef) (h0 : U 0 * S 0 * (U 0)ᵀ = 0)
    (hQR : ∀ t, U (t + 1) * R t = U t * S t + vecMulVec (g (t + 1)) (g (t + 1)) * U t)
    (hS : ∀ t, S (t + 1) = (U (t + 1))ᵀ * U t * S t * ((U (t + 1))ᵀ * U t)ᵀ +
      (U (t + 1))ᵀ * vecMulVec (g (t + 1)) (g (t + 1)) * U (t + 1))
    (hrank : ∀ t, ∃ (X : Matrix n r ℝ) (D : Matrix r r ℝ),
      ∑ τ ∈ Finset.Icc 1 (t + 1), vecMulVec (g τ) (g τ) = X * D * Xᵀ ∧ IsUnit (Xᵀ * U t))
    (t : ℕ) :
    invSqrt (precond ε g t) =
      (√ε)⁻¹ • (1 - U t * (U t)ᵀ) + U t * invSqrt (ε • (1 : Matrix r r ℝ) + S t) * (U t)ᵀ := by
  obtain ⟨hP, hY⟩ := bug_accumulator_exact g hU hS0 h0 hQR hS hrank t
  have hG : precond ε g t = ε • 1 + U t * S t * (U t)ᵀ := by rw [precond, hY]
  have hsymm : (S t).IsSymm := by
    have := hP.isHermitian
    rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  rw [hG]
  exact invSqrt_lowRank ε (hU t) hsymm

omit [DecidableEq n] in
/-- **Non-vacuity of `bug_accumulator_exact`** (arXiv 2508.21106, header item) in every dimension
and for all time.  For gradients
`g_τ = c_τ e` along one unit vector, `U_t = e` and `S_t = ∑_{τ ≤ t} c_τ²` satisfy every hypothesis
of `bug_accumulator_exact` and `bug_invSqrt_precond`. -/
theorem bug_accumulator_parallel {e : n → ℝ} (he : e ⬝ᵥ e = 1) (c : ℕ → ℝ) :
    ∃ (U : ℕ → Matrix n Unit ℝ) (S R : ℕ → Matrix Unit Unit ℝ),
      (∀ t, (U t)ᵀ * U t = 1) ∧ (S 0).PosSemidef ∧ U 0 * S 0 * (U 0)ᵀ = 0 ∧
      (∀ t, U (t + 1) * R t = U t * S t +
        vecMulVec (c (t + 1) • e) (c (t + 1) • e) * U t) ∧
      (∀ t, S (t + 1) = (U (t + 1))ᵀ * U t * S t * ((U (t + 1))ᵀ * U t)ᵀ +
        (U (t + 1))ᵀ * vecMulVec (c (t + 1) • e) (c (t + 1) • e) * U (t + 1)) ∧
      ∀ t, ∃ (X : Matrix n Unit ℝ) (D : Matrix Unit Unit ℝ),
        ∑ τ ∈ Finset.Icc 1 (t + 1), vecMulVec (c τ • e) (c τ • e) = X * D * Xᵀ ∧
          IsUnit (Xᵀ * U t) := by
  let a : ℕ → ℝ := fun t => ∑ τ ∈ Finset.Icc 1 t, c τ ^ 2
  have has : ∀ t, a (t + 1) = a t + c (t + 1) ^ 2 := fun t =>
    Finset.sum_Icc_succ_top (by omega) _
  let E : Matrix n Unit ℝ := Matrix.of fun i _ => e i
  have hEE : Eᵀ * E = 1 := by
    ext i j
    simpa [E, Matrix.mul_apply, dotProduct] using he
  have hEt : E * Eᵀ = vecMulVec e e := by
    ext i j
    simp [E, Matrix.mul_apply, vecMulVec_apply]
  have hE1 : vecMulVec e e * E = E := by
    rw [← hEt, Matrix.mul_assoc, hEE, Matrix.mul_one]
  have hE2 : ∀ b : ℝ, E * (b • (1 : Matrix Unit Unit ℝ)) = b • E := fun b => by
    rw [Matrix.mul_smul, Matrix.mul_one]
  have hsq : ∀ b : ℝ, vecMulVec (b • e) (b • e) = b ^ 2 • vecMulVec e e := by
    intro b
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
    ring
  refine ⟨fun _ => E, fun t => a t • 1, fun t => a (t + 1) • 1, fun _ => hEE, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [a] using Matrix.PosSemidef.zero
  · change E * (a 0 • 1) * Eᵀ = 0
    simp [a]
  · intro t
    change E * (a (t + 1) • 1) = E * (a t • 1) + vecMulVec (c (t + 1) • e) (c (t + 1) • e) * E
    rw [hsq, Matrix.smul_mul, hE1, hE2, hE2, has, add_smul]
  · intro t
    change a (t + 1) • 1 = Eᵀ * E * (a t • 1) * (Eᵀ * E)ᵀ +
      Eᵀ * vecMulVec (c (t + 1) • e) (c (t + 1) • e) * E
    have hcore : Eᵀ * (c (t + 1) ^ 2 • vecMulVec e e) * E = c (t + 1) ^ 2 • 1 := by
      rw [Matrix.mul_assoc, Matrix.smul_mul, hE1, Matrix.mul_smul, hEE]
    rw [hsq, hcore, hEE, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one, has, add_smul]
  · intro t
    refine ⟨E, a (t + 1) • 1, ?_, by rw [hEE]; exact isUnit_one⟩
    rw [hE2, Matrix.smul_mul, hEt]
    simp only [hsq, a, Finset.sum_smul]

end Accumulator

/-! ### Instances of the hypotheses of `algorithm2_exact` -/

section Parallel

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The update of the rank-one state along a fixed direction. -/
private noncomputable def parInc (ε a c : ℝ) : ℝ :=
  beta (((1 - a) * ((√ε)⁻¹ * c)) ^ 2) * (((1 - a) * ((√ε)⁻¹ * c)) ^ 2 * (1 - a))

omit [DecidableEq n] in
private theorem vecMulVec_unit_mul {e : n → ℝ} (he : e ⬝ᵥ e = 1) :
    vecMulVec e e * vecMulVec e e = vecMulVec e e := by
  rw [vecMulVec_self_mul_self, he, one_smul]

private theorem algIncrement_parallel {e : n → ℝ} (he : e ⬝ᵥ e = 1) (ε a c : ℝ) :
    algIncrement ε (a • vecMulVec e e) (c • e) = parInc ε a c • vecMulVec e e := by
  set w := (1 - a) * ((√ε)⁻¹ * c) with hw
  have hv : (1 - a • vecMulVec e e) *ᵥ ((√ε)⁻¹ • c • e) = w • e := by
    rw [sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_self_mulVec]
    simp only [dotProduct_smul, smul_eq_mul, he, mul_one, smul_smul, hw]
    module
  have hd : (w • e) ⬝ᵥ (w • e) = w ^ 2 := by
    rw [smul_dotProduct, dotProduct_smul, he]
    simp only [smul_eq_mul]
    ring
  have hm : vecMulVec (w • e) (w • e) * (1 - a • vecMulVec e e) =
      (w ^ 2 * (1 - a)) • vecMulVec e e := by
    have h1 : vecMulVec (w • e) (w • e) = w ^ 2 • vecMulVec e e := by
      ext i j
      simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
      ring
    rw [h1, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul,
      vecMulVec_unit_mul he]
    module
  rw [algIncrement, hv, hd, hm, smul_smul, parInc, ← hw]

/-- **Non-vacuity of `algorithm2_exact`** (arXiv 2508.21106, Algorithm 2), in every dimension and
for all time.  If all gradients are multiples `g_τ = c_τ e` of one unit vector, a rank-one run of
Algorithm 1 from `Y_0 = 0` exists and satisfies every hypothesis of `algorithm2_exact`, with
`r = 1` (`Unit` columns). -/
theorem algorithm2_exact_parallel {ε : ℝ} (hε : 0 < ε) {e : n → ℝ} (he : e ⬝ᵥ e = 1) (c : ℕ → ℝ) :
    ∃ (U V : ℕ → Matrix n Unit ℝ) (S Ŝ : ℕ → Matrix Unit Unit ℝ),
      (V 0)ᵀ * V 0 = 1 ∧ U 0 * S 0 * (V 0)ᵀ = 0 ∧
      (∀ t, IsAlgorithm1Step (algIncrement ε (U t * S t * (V t)ᵀ) (c (t + 1) • e))
        (U t) (S t) (V t) (Ŝ t) (U (t + 1)) (S (t + 1)) (V (t + 1))) ∧
      ∀ t, ∃ (X Z : Matrix n Unit ℝ) (D : Matrix Unit Unit ℝ),
        stateA ε (fun τ => c τ • e) (t + 1) = X * D * Zᵀ ∧ IsUnit (Zᵀ * V t) := by
  let a : ℕ → ℝ := fun t => Nat.rec 0 (fun k ak => ak + parInc ε ak (c (k + 1))) t
  have ha0 : a 0 = 0 := rfl
  have has : ∀ t, a (t + 1) = a t + parInc ε (a t) (c (t + 1)) := fun _ => rfl
  let E : Matrix n Unit ℝ := Matrix.of fun i _ => e i
  have hEE : Eᵀ * E = 1 := by
    ext i j
    have := he
    simpa [E, Matrix.mul_apply, dotProduct] using this
  have hEt : E * Eᵀ = vecMulVec e e := by
    ext i j
    simp [E, Matrix.mul_apply, vecMulVec_apply]
  have hE1 : vecMulVec e e * E = E := by
    rw [← hEt, Matrix.mul_assoc, hEE, Matrix.mul_one]
  have hE2 : ∀ b : ℝ, E * (b • (1 : Matrix Unit Unit ℝ)) = b • E := fun b => by
    rw [Matrix.mul_smul, Matrix.mul_one]
  have hY : ∀ b : ℝ, E * (b • (1 : Matrix Unit Unit ℝ)) * Eᵀ = b • vecMulVec e e := by
    intro b
    rw [hE2, Matrix.smul_mul, hEt]
  have hA : ∀ t, stateA ε (fun τ => c τ • e) t = a t • vecMulVec e e := by
    intro t
    induction t with
    | zero => simp [ha0]
    | succ t ih =>
      rw [stateA_succ, ← algIncrement_stateA hε, ih, has, add_smul]
      congr 1
      exact algIncrement_parallel he ε (a t) (c (t + 1))
  refine ⟨fun _ => E, fun _ => E, fun t => a t • 1, fun t => a (t + 1) • 1, hEE, ?_, ?_, ?_⟩
  · change E * (a 0 • 1) * Eᵀ = 0
    rw [hY, ha0, zero_smul]
  · intro t
    simp only [hY]
    rw [algIncrement_parallel he]
    set d := parInc ε (a t) (c (t + 1)) with hd
    have hΔt : (d • vecMulVec e e)ᵀ = d • vecMulVec e e := by
      simp [Matrix.transpose_smul, transpose_vecMulVec]
    have hΔE : d • vecMulVec e e * E = d • E := by rw [Matrix.smul_mul, hE1]
    have hcore : Eᵀ * (d • vecMulVec e e) * E = d • 1 := by
      rw [Matrix.mul_assoc, hΔE, Matrix.mul_smul, hEE]
    have hsub : a (t + 1) • (1 : Matrix Unit Unit ℝ) - d • 1 = a t • 1 := by
      rw [has, ← sub_smul, ← hd, add_sub_cancel_right]
    refine ⟨hEE, ?_, hEE, ?_⟩
    · rw [hΔE, hE2, hE2, has, add_smul, ← hd]
    · rw [hΔt, hΔE, hcore, hsub]
      simp only [Matrix.transpose_smul, Matrix.transpose_one]
      rw [hE2, hE2, has, add_smul, ← hd]
  · intro t
    refine ⟨E, E, a (t + 1) • 1, ?_, ?_⟩
    · rw [hA, hY]
    · rw [hEE]
      exact isUnit_one

end Parallel

/-- Entrywise computation with concrete small matrices. -/
local macro "entries" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two, Fin.sum_univ_one, smul_eq_mul, vecMulVec_apply,
      Matrix.one_apply] <;> norm_num))

/-- `bug_outerProduct_step` is not vacuous, and exactness occurs with `g ≠ 0`: with `U₀ = e₁`,
`S₀ = 1`, `g = 2 e₁` the new basis is `U₁ = U₀`, `R₁ = 5` and `Y₁ = 5 e₁ e₁ᵀ = Y₀ + g gᵀ`. -/
example : ∃ (g : Fin 2 → ℝ) (U₀ U₁ : Matrix (Fin 2) (Fin 1) ℝ)
    (S₀ R₁ S₁ : Matrix (Fin 1) (Fin 1) ℝ), g ≠ 0 ∧ U₀ᵀ * U₀ = 1 ∧ S₀.PosSemidef ∧ U₁ᵀ * U₁ = 1 ∧
      U₁ * R₁ = U₀ * S₀ + vecMulVec g g * U₀ ∧
      S₁ = U₁ᵀ * U₀ * S₀ * (U₁ᵀ * U₀)ᵀ + U₁ᵀ * vecMulVec g g * U₁ ∧
      U₀ * S₀ * U₀ᵀ + vecMulVec g g = U₀ * R₁ * U₀ᵀ := by
  refine ⟨![2, 0], !![1; 0], !![1; 0], 1, (5 : ℝ) • 1, (5 : ℝ) • 1, ?_, ?_,
    Matrix.PosSemidef.one, ?_, ?_, ?_, ?_⟩
  · intro h
    simpa using congrFun h 0
  all_goals entries

/-! ### Claims that are false as printed -/

section Counterexamples

/-- The gradient of the counterexample to Theorem 1: `g_τ = (4/3, 5/4)`. -/
private noncomputable def cexG : ℕ → Fin 2 → ℝ := fun _ => ![4 / 3, 5 / 4]

private theorem precond_cexG_one :
    precond 1 cexG 1 = !![25 / 9, 5 / 3; 5 / 3, 41 / 16] := by
  rw [precond_succ, precond_zero]
  simp only [cexG]
  entries

/-- **Theorem 1 of arXiv 2508.21106 is false for the triangular Cholesky factor**, which is what
the paper says `L_t` is ("the Cholesky factor", "triangular factors"), already at `t = 0`.  With
`ε = 1`, `g₁ = (4/3, 5/4)`, the Cholesky factors of `G_0 = I` and `G_1 = I + g₁ g₁ᵀ` are `L₀ = I`
and `L₁ = [[5/3, 0], [1, 5/4]]`.  Then `L₁⁻¹ g₁ = (4/5, 9/25)`, while the right-hand side of eq. (7)
is `(16/25, 3/5)`.  The two vectors have the same norm, as the isometry predicts.  The theorem is
true for the non-triangular recursive factor of eq. (8): `theorem_one`. -/
theorem theorem_one_false_for_triangular_cholesky :
    ∃ (g : ℕ → Fin 2 → ℝ) (L₀ L₁ : Matrix (Fin 2) (Fin 2) ℝ),
      L₀ * L₀ᵀ = precond 1 g 0 ∧ L₁ * L₁ᵀ = precond 1 g 1 ∧
      (L₀ 0 1 = 0 ∧ 0 < L₀ 0 0 ∧ 0 < L₀ 1 1) ∧ (L₁ 0 1 = 0 ∧ 0 < L₁ 0 0 ∧ 0 < L₁ 1 1) ∧
      L₁⁻¹ *ᵥ g 1 ≠ (√(1 + (L₀⁻¹ *ᵥ g 1) ⬝ᵥ (L₀⁻¹ *ᵥ g 1)))⁻¹ • (L₀⁻¹ *ᵥ g 1) := by
  have hinv : (!![5 / 3, 0; 1, 5 / 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ =
      !![3 / 5, 0; -12 / 25, 4 / 5] := by
    refine Matrix.inv_eq_left_inv ?_
    entries
  refine ⟨cexG, 1, !![5 / 3, 0; 1, 5 / 4], by simp, ?_, ?_, ?_, ?_⟩
  · rw [precond_cexG_one]
    entries
  · simp
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    norm_num
  · rw [hinv, inv_one, one_mulVec]
    have hd : cexG 1 ⬝ᵥ cexG 1 = 481 / 144 := by
      simp [cexG, dotProduct, Fin.sum_univ_two]
      norm_num
    have hr : √(1 + cexG 1 ⬝ᵥ cexG 1) = 25 / 12 := by
      rw [hd, show (1 + 481 / 144 : ℝ) = (25 / 12) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [hr]
    intro h
    have h0 := congrFun h 0
    simp [cexG, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    norm_num at h0

/-- **The recursion (8) of arXiv 2508.21106 leaves the triangular matrices**: with the data of
`theorem_one_false_for_triangular_cholesky`, `L_1 = I + α g₁ g₁ᵀ` has the entry `20/37` above the
diagonal, and `L_0 = I` is triangular.  So the paper's "explicit recursive expression for the
Cholesky factor" is not one: it is another factor of `G_t`. -/
theorem factor_one_not_lowerTriangular : ∃ g : ℕ → Fin 2 → ℝ, factor 1 g 1 0 1 ≠ 0 := by
  refine ⟨cexG, ?_⟩
  have hf : factor (1 : ℝ) cexG 0 = 1 := by simp [factor]
  have hb : gbar 1 cexG 0 = ![4 / 3, 5 / 4] := by
    simp [gbar, hf, cexG]
  have hs : gbar 1 cexG 0 ⬝ᵥ gbar 1 cexG 0 = 481 / 144 := by
    rw [hb]
    simp [dotProduct, Fin.sum_univ_two]
    norm_num
  have ha : alpha (481 / 144) = 12 / 37 := by
    rw [alpha, show (1 + 481 / 144 : ℝ) = (25 / 12) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  rw [factor_succ, hf, Matrix.one_mul, hs, ha, hb]
  simp

/-- **Eq. (4) of arXiv 2508.21106 is false as printed**, with `ḡ_{t+1} = G_t⁻¹ g_{t+1}`: for
`G = 4` (a `1 × 1` matrix), `R = G^{1/2} = 2`, `g = 1`, and every `α` solving eq. (5), the right
side `R (I + α ḡ ḡᵀ)² R` is `17/4`, not `G + g gᵀ = 5`.  The exponent should be `-1/2`:
`eq_four_corrected`. -/
theorem eq_four_false_as_printed :
    ∃ (G R : Matrix (Fin 1) (Fin 1) ℝ) (v : Fin 1 → ℝ), R.PosDef ∧ R * R = G ∧
      ∀ α : ℝ, 1 + α * ((G⁻¹ *ᵥ v) ⬝ᵥ (G⁻¹ *ᵥ v)) = √(1 + (G⁻¹ *ᵥ v) ⬝ᵥ (G⁻¹ *ᵥ v)) →
        G + vecMulVec v v ≠ R * ((1 + α • vecMulVec (G⁻¹ *ᵥ v) (G⁻¹ *ᵥ v)) *
          (1 + α • vecMulVec (G⁻¹ *ᵥ v) (G⁻¹ *ᵥ v))) * R := by
  have hinv : ((4 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ = (1 / 4 : ℝ) • 1 := by
    refine Matrix.inv_eq_left_inv ?_
    simp [smul_smul]
  refine ⟨(4 : ℝ) • 1, (2 : ℝ) • 1, fun _ => 1, ?_, ?_, ?_⟩
  · exact Matrix.PosDef.one.smul (by norm_num)
  · simp [smul_smul]
    norm_num
  · intro α hα h
    rw [hinv] at hα h
    have hw : ((1 / 4 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *ᵥ (fun _ => (1 : ℝ)) =
        fun _ => (1 / 4 : ℝ) := by
      ext i
      simp [smul_mulVec]
    rw [hw] at hα h
    have hs : ((fun _ : Fin 1 => (1 / 4 : ℝ)) ⬝ᵥ (fun _ : Fin 1 => (1 / 4 : ℝ)) : ℝ) = 1 / 16 := by
      simp [dotProduct]
      norm_num
    rw [hs] at hα
    have hsq : (1 + α * (1 / 16)) ^ 2 = 17 / 16 := by
      rw [hα, Real.sq_sqrt (by norm_num)]
      norm_num
    have h00 := congrFun (congrFun h 0) 0
    simp [Matrix.mul_apply, vecMulVec_apply] at h00
    nlinarith

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Eq. (4) of arXiv 2508.21106, corrected**: for any symmetric invertible root `R` of `G`
(in particular `G^{1/2}`) and `ḡ = R⁻¹ g` (exponent `-1/2`, not `-1` as printed):
`G + g gᵀ = R (I + α ḡ ḡᵀ)² R`, with `α` from eq. (5). -/
theorem eq_four_corrected {G R : Matrix n n ℝ} (hR : IsUnit R) (hRt : Rᵀ = R) (hG : R * R = G)
    (v : n → ℝ) :
    G + vecMulVec v v =
      R * ((1 + alpha ((R⁻¹ *ᵥ v) ⬝ᵥ (R⁻¹ *ᵥ v)) • vecMulVec (R⁻¹ *ᵥ v) (R⁻¹ *ᵥ v)) *
        (1 + alpha ((R⁻¹ *ᵥ v) ⬝ᵥ (R⁻¹ *ᵥ v)) • vecMulVec (R⁻¹ *ᵥ v) (R⁻¹ *ᵥ v))) * R := by
  have hd : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det _).1 hR
  have hRv : R *ᵥ (R⁻¹ *ᵥ v) = v := by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, one_mulVec]
  rw [sq_one_add_alpha, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hG, mul_vecMulVec,
    vecMulVec_mul, hRv, ← Matrix.mulVec_transpose, hRt, hRv]

/-- **Algorithm 1 of arXiv 2508.21106 does not preserve symmetry on outer-product increments**,
which refutes the header's "symmetric (`U₀ = V₀`), PSD-preserving" for the paper's own integrator
(it holds for BUG: `bug_outerProduct_step`, `Symmetry.bug_isTwistSymm`; the paper makes no such
claim).  With `g = (2, 6)`, `U₀ = V₀ = e₁`, `S₀ = 5`, a step exists, and every step (any QR
factors) returns a non-symmetric `Y₁`, here `[[9, 108/5], [12, 144/5]]`. -/
theorem algorithm1_not_symmetric :
    ∃ (g : Fin 2 → ℝ) (U₀ : Matrix (Fin 2) (Fin 1) ℝ) (S₀ : Matrix (Fin 1) (Fin 1) ℝ),
      U₀ᵀ * U₀ = 1 ∧ S₀.PosSemidef ∧
      (∃ Ŝ₁ U₁ S₁ V₁, IsAlgorithm1Step (vecMulVec g g) U₀ S₀ U₀ Ŝ₁ U₁ S₁ V₁) ∧
      ∀ Ŝ₁ U₁ S₁ V₁, IsAlgorithm1Step (vecMulVec g g) U₀ S₀ U₀ Ŝ₁ U₁ S₁ V₁ →
        ¬ (U₁ * S₁ * V₁ᵀ).IsSymm := by
  refine ⟨![2, 6], !![1; 0], (5 : ℝ) • 1, ?_, Matrix.PosSemidef.one.smul (by norm_num),
    ⟨!![15], !![3 / 5; 4 / 5], !![39], !![5 / 13; 12 / 13], ?_, ?_, ?_, ?_⟩, ?_⟩
  · entries
  · entries
  · entries
  · entries
  · entries
  · intro Ŝ₁ U₁ S₁ V₁ h hsym
    have hY := h.eq
    have e1 := congrFun (congrFun h.qrK 0) 0
    have e2 := congrFun (congrFun h.qrK 1) 0
    have e3 := congrFun (congrFun h.orthoU 0) 0
    have h01 := Matrix.IsSymm.ext_iff.1 hsym 0 1
    rw [hY] at h01
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply,
      Matrix.sub_apply, Fin.sum_univ_two, Fin.sum_univ_one, smul_eq_mul, vecMulVec_apply,
      Matrix.one_apply] at e1 e2 e3 h01
    norm_num at e1 e2 e3 h01
    have hs : Ŝ₁ 0 0 ^ 2 = 225 := by
      linear_combination (-Ŝ₁ 0 0 ^ 2) * e3 + (U₁ 0 0 * Ŝ₁ 0 0 + 9) * e1 +
        (U₁ 1 0 * Ŝ₁ 0 0 + 12) * e2
    have hfalse : (2700 : ℝ) = 4860 := by
      linear_combination (-12) * hs + Ŝ₁ 0 0 ^ 2 * h01 +
        (12 * (U₁ 0 0 * Ŝ₁ 0 0 + 9) + 36 * (U₁ 1 0 * Ŝ₁ 0 0)) * e1 + 324 * e2
    norm_num at hfalse

end Counterexamples

end LeanDLRA.Literature.P2508_21106
