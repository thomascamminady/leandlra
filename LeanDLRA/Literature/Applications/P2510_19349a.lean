import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Scalable LinUCB with low-rank inverse updates (arXiv 2510.19349)

Formalizes the algebra of Section 2 of arXiv 2510.19349. The inverse design matrix is kept as
`A_t⁻¹ = L_t⁻ᵀ L_t⁻¹` with `L_t⁻¹ = (I - U_t V_tᵀ) L_0⁻¹`, where `A_t = ε I + ∑_{s<t} x_s x_sᵀ`
and `L_0 = √ε I`, so `L_0⁻¹ = ε^{-1/2} I`. Contexts are indexed from `0`. Matrices are over `ℝ`.
The factor widths grow by column concatenation (`appendCols`), and `∑ x_s x_sᵀ` is written with
`Matrix.vecMulVec`. The inverse-root recursion has no counterpart in the core library, so the
file imports only Mathlib and uses no core LeanDLRA definition.

Proved:
* `rankOne_step` and `rankOne_invRoot` (Theorem 1, eq. (3)): the rank-one update
  `L' = L (I + α x̃ x̃ᵀ)`, `x̃ = L⁻¹ x`, `1 + α ‖x̃‖² = √(1 + ‖x̃‖²)`, with
  `U' = [U, β x̃]`, `V' = [V, (I - V Uᵀ) x̃]`, `β = α / (1 + α ‖x̃‖²)`. The sequence version
  asserts the factorization with some `d × t` matrices `U, V` (the explicit recursion is
  `rankOne_step`), together with `L_t L_tᵀ = A_t`. Existence of the scalar `α` at each step is
  `exists_alpha`.
* `batch_update` (Theorems 2 and 3, one step): `L' = L (I + Q (M - I) Qᵀ)` with `L⁻¹ X = Q R`,
  `Qᵀ Q = I` and `M Mᵀ = I + R Rᵀ`. It satisfies `L' L'ᵀ = L Lᵀ + X Xᵀ`, is invertible, and
  `L'⁻¹ = (I - U' V'ᵀ) L_0⁻¹` with `U' = [U, Q (M - I) M⁻¹]`, `V' = [V, (I - V Uᵀ) Q]`. The
  factors `Q` and `M` are any matrices with the stated identities, so the triangularity of `R`
  and `M` is not assumed. `M` is shown invertible from `M Mᵀ = I + R Rᵀ`.
* `correction_spectral` (Section 2.3): for `A = E (εI + Σ) Eᵀ` with `E` orthogonal and `Σ` diagonal
  with `σ ≥ 0`, `ε⁻¹ I - A⁻¹ = E diag(σᵢ / (ε (ε + σᵢ))) Eᵀ`.

Not formalized: the projector-splitting integrator of Section 3 and Algorithm 3 (including the
KSL increment, the rank-`r` truncation and the cost analysis of Remark 1, Table 1); the exactness
claim of Section 3, which rests on the PSI exactness theorem of Lubich–Oseledets; the regret bound;
and the truncation statement at the end of Section 2.3, which the paper gives only as a remark
about approximation quality, not as a precise claim.
-/

open scoped Matrix

namespace LeanDLRA.Literature.P2510_19349

variable {d : ℕ}

/-- Column concatenation `[U A]` of two matrices with `d` rows. -/
def appendCols {k n : ℕ} (U : Matrix (Fin d) (Fin k) ℝ) (A : Matrix (Fin d) (Fin n) ℝ) :
    Matrix (Fin d) (Fin (k + n)) ℝ :=
  Matrix.of fun i => Fin.append (U i) (A i)

lemma appendCols_mul_transpose {k n : ℕ} (U V : Matrix (Fin d) (Fin k) ℝ)
    (A B : Matrix (Fin d) (Fin n) ℝ) :
    appendCols U A * (appendCols V B)ᵀ = U * Vᵀ + A * Bᵀ := by
  ext i j
  simp [appendCols, Matrix.mul_apply, Fin.sum_univ_add]

lemma dot_self_nonneg' {n : ℕ} (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v := by
  simp only [dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

lemma conj_mul_conj {B : ℕ} {Q : Matrix (Fin d) (Fin B) ℝ} (hQ : Qᵀ * Q = 1)
    (Y Z : Matrix (Fin B) (Fin B) ℝ) : Q * Y * Qᵀ * (Q * Z * Qᵀ) = Q * (Y * Z) * Qᵀ := by
  calc Q * Y * Qᵀ * (Q * Z * Qᵀ) = Q * Y * (Qᵀ * Q) * Z * Qᵀ := by
        simp only [Matrix.mul_assoc]
    _ = Q * (Y * Z) * Qᵀ := by
        rw [hQ]
        simp only [Matrix.mul_one, Matrix.mul_assoc]

/-- The scalar condition `1 + α s = √(1 + s)` of Theorem 1 (arXiv 2510.19349) has a solution
for every `s ≥ 0`, so the hypotheses on `α` in `rankOne_invRoot` are satisfiable step by step. -/
lemma exists_alpha (s : ℝ) (hs : 0 ≤ s) : ∃ α : ℝ, 1 + α * s = Real.sqrt (1 + s) := by
  rcases eq_or_lt_of_le hs with h | h
  · exact ⟨0, by rw [← h]; simp⟩
  · refine ⟨(Real.sqrt (1 + s) - 1) / s, ?_⟩
    field_simp
    ring

/-- One rank-one update, arXiv 2510.19349, Theorem 1 (Sec. 2.1, eq. (3)). Here
`L' = L (I + α x̃ x̃ᵀ)` with `x̃ = L⁻¹ x` and `1 + α ‖x̃‖² = √(1 + ‖x̃‖²)`, `β = α / (1 + α ‖x̃‖²)`.
If `L⁻¹ = (I - U Vᵀ) G`, then `L'⁻¹ = (I - U' V'ᵀ) G` with `U' = [U, β x̃]`,
`V' = [V, (I - V Uᵀ) x̃]`, and `L' L'ᵀ = L Lᵀ + x xᵀ`. -/
lemma rankOne_step {k : ℕ} (G : Matrix (Fin d) (Fin d) ℝ)
    (U V : Matrix (Fin d) (Fin k) ℝ) (L : Matrix (Fin d) (Fin d) ℝ) (hL : IsUnit L.det)
    (hinv : L⁻¹ = (1 - U * Vᵀ) * G) (x xt : Fin d → ℝ) (hxt : xt = L⁻¹ *ᵥ x)
    (α β : ℝ) (hα : 1 + α * (xt ⬝ᵥ xt) = Real.sqrt (1 + xt ⬝ᵥ xt))
    (hβ : β = α / (1 + α * (xt ⬝ᵥ xt))) :
    IsUnit (L * (1 + α • Matrix.vecMulVec xt xt)).det ∧
    (L * (1 + α • Matrix.vecMulVec xt xt))⁻¹ =
      (1 - appendCols U (Matrix.of fun i (_ : Fin 1) => β * xt i) *
        (appendCols V (Matrix.of fun i (_ : Fin 1) => ((1 - V * Uᵀ) *ᵥ xt) i))ᵀ) * G ∧
    (L * (1 + α • Matrix.vecMulVec xt xt)) * (L * (1 + α • Matrix.vecMulVec xt xt))ᵀ =
      L * Lᵀ + Matrix.vecMulVec x x := by
  have hs : 0 ≤ xt ⬝ᵥ xt := dot_self_nonneg' xt
  have hpos : 0 < 1 + α * (xt ⬝ᵥ xt) := by
    rw [hα]
    exact Real.sqrt_pos.2 (by linarith)
  have hsq : (1 + α * (xt ⬝ᵥ xt)) ^ 2 = 1 + xt ⬝ᵥ xt := by
    rw [hα, Real.sq_sqrt (by linarith)]
  have hPP : Matrix.vecMulVec xt xt * Matrix.vecMulVec xt xt =
      (xt ⬝ᵥ xt) • Matrix.vecMulVec xt xt :=
    by
      rw [Matrix.vecMulVec_mul_vecMulVec]
      ext i j
      simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have hPt : (Matrix.vecMulVec xt xt)ᵀ = Matrix.vecMulVec xt xt :=
    Matrix.transpose_vecMulVec xt xt
  have hβ' : β * (1 + α * (xt ⬝ᵥ xt)) = α := by
    rw [hβ]
    field_simp
  have hLx : L *ᵥ xt = x := by
    rw [hxt, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv L hL, Matrix.one_mulVec]
  -- right inverse of the rank-one factor
  have hNinv : (1 + α • Matrix.vecMulVec xt xt) * (1 - β • Matrix.vecMulVec xt xt) = 1 := by
    have hc : α - β - α * β * (xt ⬝ᵥ xt) = 0 := by linear_combination (-1 : ℝ) * hβ'
    have : (1 + α • Matrix.vecMulVec xt xt) * (1 - β • Matrix.vecMulVec xt xt) =
        1 + (α - β - α * β * (xt ⬝ᵥ xt)) • Matrix.vecMulVec xt xt := by
      simp only [add_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hPP,
        smul_smul]
      module
    rw [this, hc, zero_smul, add_zero]
  have hright : (L * (1 + α • Matrix.vecMulVec xt xt)) *
      ((1 - β • Matrix.vecMulVec xt xt) * L⁻¹) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 + α • Matrix.vecMulVec xt xt), hNinv,
      Matrix.one_mul, Matrix.mul_nonsing_inv L hL]
  refine ⟨Matrix.isUnit_det_of_right_inverse hright, ?_, ?_⟩
  · -- the inverse
    have hPmul : Matrix.vecMulVec xt xt * (1 - U * Vᵀ) =
        Matrix.vecMulVec xt ((1 - V * Uᵀ) *ᵥ xt) := by
      rw [Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose]
      congr 1
      simp [Matrix.transpose_mul, Matrix.transpose_sub]
    have hAB : (Matrix.of fun i (_ : Fin 1) => β * xt i) *
        (Matrix.of fun i (_ : Fin 1) => ((1 - V * Uᵀ) *ᵥ xt) i)ᵀ =
        β • Matrix.vecMulVec xt ((1 - V * Uᵀ) *ᵥ xt) := by
      ext i j
      simp [Matrix.mul_apply, Matrix.vecMulVec_apply, mul_assoc]
    have key : (1 - β • Matrix.vecMulVec xt xt) * (1 - U * Vᵀ) =
        1 - (U * Vᵀ + β • Matrix.vecMulVec xt ((1 - V * Uᵀ) *ᵥ xt)) := by
      rw [sub_mul, one_mul, smul_mul_assoc, hPmul]
      abel
    rw [Matrix.inv_eq_right_inv hright, appendCols_mul_transpose, hAB, hinv, ← Matrix.mul_assoc,
      key]
  · -- the design matrix
    have hcoef : (2 * α + α ^ 2 * (xt ⬝ᵥ xt)) • Matrix.vecMulVec xt xt =
        Matrix.vecMulVec xt xt := by
      rcases mul_eq_zero.1 (show (xt ⬝ᵥ xt) * (2 * α + α ^ 2 * (xt ⬝ᵥ xt) - 1) = 0 by
        linear_combination hsq) with h0 | h1
      · have hx0 : xt = 0 := dotProduct_self_eq_zero.1 h0
        simp [hx0]
      · rw [show 2 * α + α ^ 2 * (xt ⬝ᵥ xt) = 1 by linarith, one_smul]
    have hNN : (1 + α • Matrix.vecMulVec xt xt) * (1 + α • Matrix.vecMulVec xt xt)ᵀ =
        1 + Matrix.vecMulVec xt xt := by
      rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, hPt]
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hPP,
        smul_smul]
      linear_combination (norm := module) hcoef
    have hLP : L * Matrix.vecMulVec xt xt * Lᵀ = Matrix.vecMulVec x x := by
      rw [Matrix.mul_vecMulVec, hLx, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hLx]
    have hA : (L * (1 + α • Matrix.vecMulVec xt xt)) *
        (L * (1 + α • Matrix.vecMulVec xt xt))ᵀ =
        L * ((1 + α • Matrix.vecMulVec xt xt) * (1 + α • Matrix.vecMulVec xt xt)ᵀ) * Lᵀ := by
      rw [Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [hA, hNN]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
    rw [hLP]

/-- **arXiv 2510.19349, Theorem 1 (rank-one updates), whole sequence.** Contexts `x t`
(0-indexed), `ε > 0`, `L 0 = √ε I` (so `(L 0)⁻¹ = ε^{-1/2} I`), `xt t = (L t)⁻¹ x t`,
`L (t+1) = L t (I + α t x̃ t x̃ tᵀ)` with `1 + α t ‖xt t‖² = √(1 + ‖xt t‖²)` (the paper's
"parameter α such that" condition). Then for every `t`, `L t` is invertible, `(L t)⁻¹ = (I - U Vᵀ)
(L 0)⁻¹` for some `d × t` matrices `U, V`, and `L t (L t)ᵀ = ε I + ∑_{s<t} x_s x_sᵀ`. -/
theorem rankOne_invRoot (ε : ℝ) (hε : 0 < ε) (x xt : ℕ → Fin d → ℝ)
    (L : ℕ → Matrix (Fin d) (Fin d) ℝ) (α : ℕ → ℝ)
    (hL0 : L 0 = Real.sqrt ε • 1)
    (hxt : ∀ t, xt t = (L t)⁻¹ *ᵥ x t)
    (hL : ∀ t, L (t + 1) = L t * (1 + α t • Matrix.vecMulVec (xt t) (xt t)))
    (hα : ∀ t, 1 + α t * (xt t ⬝ᵥ xt t) = Real.sqrt (1 + xt t ⬝ᵥ xt t)) :
    ∀ t, IsUnit (L t).det ∧
      ∃ U V : Matrix (Fin d) (Fin t) ℝ,
        (L t)⁻¹ = (1 - U * Vᵀ) * (L 0)⁻¹ ∧
        L t * (L t)ᵀ = ε • 1 + ∑ s ∈ Finset.range t, Matrix.vecMulVec (x s) (x s) := by
  intro t
  induction t with
  | zero =>
    have hpos : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.2 hε).ne'
    refine ⟨Matrix.isUnit_det_of_right_inverse (B := (Real.sqrt ε)⁻¹ • 1) ?_, 0, 0, ?_, ?_⟩
    · rw [hL0, smul_mul_assoc, one_mul, smul_smul, mul_inv_cancel₀ hpos, one_smul]
    · simp
    · rw [hL0]
      simp [smul_smul, Real.mul_self_sqrt hε.le]
  | succ t ih =>
    obtain ⟨hunit, U, V, hinv, hA⟩ := ih
    obtain ⟨hu, hinv', hA'⟩ := rankOne_step (d := d) (L 0)⁻¹ U V (L t) hunit hinv (x t) (xt t)
      (hxt t) (α t) (α t / (1 + α t * (xt t ⬝ᵥ xt t))) (hα t) rfl
    refine ⟨by rw [hL t]; exact hu,
      appendCols U (Matrix.of fun i (_ : Fin 1) => α t / (1 + α t * (xt t ⬝ᵥ xt t)) * xt t i),
      appendCols V (Matrix.of fun i (_ : Fin 1) => ((1 - V * Uᵀ) *ᵥ xt t) i), ?_, ?_⟩
    · rw [hL t]
      exact hinv'
    · rw [hL t, hA', hA, Finset.sum_range_succ, add_assoc]

/-- **arXiv 2510.19349, Theorems 2 and 3 (batch updates), one step.** Let `L` be invertible with
`L⁻¹ = (I - U Vᵀ) G` (`G` plays the role of `L₀⁻¹`). Let `X` be the batch, `L⁻¹ X = Q R` a QR
factorization with `Qᵀ Q = I`, and `M Mᵀ = I + R Rᵀ` (the paper's Cholesky factor; any such `M`
is allowed). Then `L' = L (I + Q (M - I) Qᵀ)` satisfies `L' L'ᵀ = L Lᵀ + X Xᵀ`, is invertible,
and `L'⁻¹ = (I - U' V'ᵀ) G` with `U' = [U, Q (M - I) M⁻¹]`, `V' = [V, (I - V Uᵀ) Q]`. -/
theorem batch_update {k B : ℕ} (G : Matrix (Fin d) (Fin d) ℝ)
    (U V : Matrix (Fin d) (Fin k) ℝ) (L : Matrix (Fin d) (Fin d) ℝ) (hL : IsUnit L.det)
    (hinv : L⁻¹ = (1 - U * Vᵀ) * G)
    (X Q : Matrix (Fin d) (Fin B) ℝ) (R M : Matrix (Fin B) (Fin B) ℝ)
    (hQ : Qᵀ * Q = 1) (hQR : L⁻¹ * X = Q * R) (hM : M * Mᵀ = 1 + R * Rᵀ) :
    (L * (1 + Q * (M - 1) * Qᵀ)) * (L * (1 + Q * (M - 1) * Qᵀ))ᵀ = L * Lᵀ + X * Xᵀ ∧
    IsUnit (L * (1 + Q * (M - 1) * Qᵀ)).det ∧
    (L * (1 + Q * (M - 1) * Qᵀ))⁻¹ =
      (1 - appendCols U (Q * (M - 1) * M⁻¹) *
        (appendCols V ((1 - V * Uᵀ) * Q))ᵀ) * G := by
  -- M is invertible: its transpose has no kernel, since M Mᵀ = I + R Rᵀ is positive definite
  have hMu : IsUnit M.det := by
    by_contra hnot
    have hdet : M.det = 0 := by
      by_contra h
      exact hnot (isUnit_iff_ne_zero.2 h)
    have hdetT : Mᵀ.det = 0 := by
      rw [Matrix.det_transpose]
      exact hdet
    obtain ⟨w, hw, hMw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdetT
    have h1 : (1 + R * Rᵀ) *ᵥ w = 0 := by
      rw [← hM, ← Matrix.mulVec_mulVec, hMw, Matrix.mulVec_zero]
    have h2 : w + R *ᵥ (Rᵀ *ᵥ w) = 0 := by
      simpa [Matrix.add_mulVec, Matrix.mulVec_mulVec] using h1
    have h3 := congrArg (dotProduct w) h2
    simp only [dotProduct_add, dotProduct_zero] at h3
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose] at h3
    have hw0 : w ⬝ᵥ w = 0 := by
      linarith [dot_self_nonneg' w, dot_self_nonneg' (Rᵀ *ᵥ w)]
    exact hw (dotProduct_self_eq_zero.1 hw0)
  have hMinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMu
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin B) (Fin B) ℝ, Y = M - 1 := ⟨_, rfl⟩
  rw [← hY]
  have hMY : M = 1 + Y := by
    rw [hY]
    abel
  -- (I + Y)(I + Yᵀ) = I + R Rᵀ gives Y + Yᵀ + Y Yᵀ = R Rᵀ
  have hYR : Y + Yᵀ + Y * Yᵀ = R * Rᵀ := by
    calc Y + Yᵀ + Y * Yᵀ = M * Mᵀ - 1 := by
          rw [hMY, Matrix.transpose_add, Matrix.transpose_one]
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
          abel
      _ = R * Rᵀ := by
          rw [hM]
          abel
  have hYGsum : Y * M⁻¹ + Y * (Y * M⁻¹) = Y := by
    calc Y * M⁻¹ + Y * (Y * M⁻¹) = Y * ((1 + Y) * M⁻¹) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul]
      _ = Y := by rw [← hMY, hMinv, Matrix.mul_one]
  -- the inverse of the rank-B factor I + Q Y Qᵀ
  have hK : (1 + Q * Y * Qᵀ) * (1 - Q * Y * M⁻¹ * Qᵀ) = 1 := by
    have e : Q * Y * M⁻¹ * Qᵀ = Q * (Y * M⁻¹) * Qᵀ := by simp only [Matrix.mul_assoc]
    have hAB := conj_mul_conj hQ Y (Y * M⁻¹)
    have hABC : Q * Y * Qᵀ - Q * (Y * M⁻¹) * Qᵀ - Q * (Y * (Y * M⁻¹)) * Qᵀ = 0 := by
      calc Q * Y * Qᵀ - Q * (Y * M⁻¹) * Qᵀ - Q * (Y * (Y * M⁻¹)) * Qᵀ
          = Q * (Y - (Y * M⁻¹ + Y * (Y * M⁻¹))) * Qᵀ := by
            simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul]
            abel
        _ = 0 := by
            rw [hYGsum, sub_self, Matrix.mul_zero, Matrix.zero_mul]
    rw [e, add_mul, one_mul, mul_sub, mul_one, hAB]
    calc 1 - Q * (Y * M⁻¹) * Qᵀ + (Q * Y * Qᵀ - Q * (Y * (Y * M⁻¹)) * Qᵀ)
        = 1 + (Q * Y * Qᵀ - Q * (Y * M⁻¹) * Qᵀ - Q * (Y * (Y * M⁻¹)) * Qᵀ) := by abel
      _ = 1 := by rw [hABC, add_zero]
  have hright : (L * (1 + Q * Y * Qᵀ)) * ((1 - Q * Y * M⁻¹ * Qᵀ) * L⁻¹) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 + Q * Y * Qᵀ), hK, Matrix.one_mul,
      Matrix.mul_nonsing_inv L hL]
  refine ⟨?_, Matrix.isUnit_det_of_right_inverse hright, ?_⟩
  · -- the design matrix: L' L'ᵀ = L Lᵀ + X Xᵀ
    have hT : (Q * Y * Qᵀ)ᵀ = Q * Yᵀ * Qᵀ := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    have hNN : (1 + Q * Y * Qᵀ) * (1 + Q * Y * Qᵀ)ᵀ = 1 + Q * (R * Rᵀ) * Qᵀ := by
      rw [Matrix.transpose_add, Matrix.transpose_one, hT]
      calc (1 + Q * Y * Qᵀ) * (1 + Q * Yᵀ * Qᵀ)
          = 1 + (Q * Y * Qᵀ + Q * Yᵀ * Qᵀ + Q * Y * Qᵀ * (Q * Yᵀ * Qᵀ)) := by
            simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
            abel
        _ = 1 + (Q * Y * Qᵀ + Q * Yᵀ * Qᵀ + Q * (Y * Yᵀ) * Qᵀ) := by
            rw [conj_mul_conj hQ]
        _ = 1 + Q * (Y + Yᵀ + Y * Yᵀ) * Qᵀ := by
            simp only [Matrix.mul_add, Matrix.add_mul]
        _ = 1 + Q * (R * Rᵀ) * Qᵀ := by rw [hYR]
    have hX : L * (Q * R) = X := by
      rw [← hQR]
      exact Matrix.mul_nonsing_inv_cancel_left L X hL
    have hA : (L * (1 + Q * Y * Qᵀ)) * (L * (1 + Q * Y * Qᵀ))ᵀ =
        L * ((1 + Q * Y * Qᵀ) * (1 + Q * Y * Qᵀ)ᵀ) * Lᵀ := by
      rw [Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [hA, hNN, ← hX]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
    congr 1
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  · -- the inverse
    have hVb : ((1 - V * Uᵀ) * Q)ᵀ = Qᵀ * (1 - U * Vᵀ) := by
      simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.transpose_transpose]
    have hfin : (1 - Q * Y * M⁻¹ * Qᵀ) * (1 - U * Vᵀ) =
        1 - (U * Vᵀ + Q * Y * M⁻¹ * (Qᵀ * (1 - U * Vᵀ))) := by
      rw [sub_mul, one_mul]
      simp only [Matrix.mul_assoc]
      abel
    rw [Matrix.inv_eq_right_inv hright, hinv, appendCols_mul_transpose, hVb, ← hfin]
    simp only [Matrix.mul_assoc]

/-- **arXiv 2510.19349, Section 2.3, spectral form of the correction.** Let
`A = E (εI + Σ) Eᵀ` with `E` orthogonal and `Σ = diag(σ)`, `σ ≥ 0` (for `A_t = E_x (εI + Σ_x) E_xᵀ`,
`σ` the singular values of `∑ x_s x_sᵀ`). Then `ε⁻¹ I - A⁻¹ = E diag(σᵢ / (ε (ε + σᵢ))) Eᵀ`. -/
theorem correction_spectral (ε : ℝ) (hε : 0 < ε) (E : Matrix (Fin d) (Fin d) ℝ)
    (hE : Eᵀ * E = 1) (σ : Fin d → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    ε⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) -
        (E * Matrix.diagonal (fun i => ε + σ i) * Eᵀ)⁻¹ =
      E * Matrix.diagonal (fun i => σ i / (ε * (ε + σ i))) * Eᵀ := by
  have hEE : E * Eᵀ = 1 := mul_eq_one_comm.1 hE
  have hdpos : ∀ i, ε + σ i ≠ 0 := fun i => (by linarith [hσ i] : (0 : ℝ) < ε + σ i).ne'
  have hDD : Matrix.diagonal (fun i => ε + σ i) *
      Matrix.diagonal (fun i => (ε + σ i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have h1 : (fun i => (ε + σ i) * (ε + σ i)⁻¹) = fun _ => (1 : ℝ) :=
      funext fun i => mul_inv_cancel₀ (hdpos i)
    rw [h1, ← Matrix.diagonal_one]
  have hinv : (E * Matrix.diagonal (fun i => ε + σ i) * Eᵀ)⁻¹ =
      E * Matrix.diagonal (fun i => (ε + σ i)⁻¹) * Eᵀ := by
    apply Matrix.inv_eq_right_inv
    rw [show E * Matrix.diagonal (fun i => ε + σ i) * Eᵀ *
        (E * Matrix.diagonal (fun i => (ε + σ i)⁻¹) * Eᵀ) =
        E * (Matrix.diagonal (fun i => ε + σ i) * (Eᵀ * E) *
          Matrix.diagonal (fun i => (ε + σ i)⁻¹)) * Eᵀ by simp only [Matrix.mul_assoc],
      hE, Matrix.mul_one, hDD, Matrix.mul_one, hEE]
  have hone : ε⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) = E * (ε⁻¹ • 1) * Eᵀ := by
    rw [Matrix.mul_smul, Matrix.mul_one, smul_mul_assoc, hEE]
  have hcore : ε⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) -
      Matrix.diagonal (fun i => (ε + σ i)⁻¹) =
      Matrix.diagonal (fun i => σ i / (ε * (ε + σ i))) := by
    ext i j
    rcases eq_or_ne i j with rfl | h
    · have h1 := hdpos i
      have h2 : ε ≠ 0 := hε.ne'
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
        Matrix.diagonal_apply_eq, smul_eq_mul]
      field_simp
      ring
    · simp [h]
  rw [hinv, hone, ← hcore]
  simp only [Matrix.mul_assoc, ← Matrix.mul_sub, ← Matrix.sub_mul]

end LeanDLRA.Literature.P2510_19349
