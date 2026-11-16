import LeanDLRA.Integrators.Matrix.BUGRun
import LeanDLRA.Integrators.Matrix.Defs

/-!
# Worked example: an error bound for the BUG integrator on a concrete problem

This file is meant to be read from top to bottom. It starts from nothing but a matrix
differential equation written down with numbers, and ends with a Lean theorem that says: the
fixed-rank BUG integrator of rank one can be run for `100` steps of size `1/1000` from every
rank-one start value within `1/100` of the exact solution, and every value of the run stays
within `3/10` of the exact solution.

The steps:

1. **The problem.** The linear equation `Y' = M Y + Y Nᵀ + G` for `2 × 2` matrices, with
   `M = E₂₁` (the matrix with a single entry `1` below the diagonal), `N = 0`, `G = -E₂₁`. The
   matrix `C = E₁₁` is a stationary point (`M C + C Nᵀ + G = 0`), so the constant function
   `A(t) = C` is the exact solution.
2. **The constants.** The Frobenius norm of `M`, `N` and `G` gives the Lipschitz constant, the
   bound of the field on a tube and the bound for the normal component.
3. **The flagship theorem.** `MatrixBUG.exists_run_norm_sub_le` is applied to the problem.
4. **The numbers.** The smallness condition and the error bound are inequalities between real
   numbers that contain `exp`; they are proved from one bound for `exp (1/10)`.

The example uses core definitions only (`DLRAProblem`, `ODESolution`, `IsRun`,
`MatrixBUG.stepRel`, `uniformGrid`, `bugGlobalBound`). The bound is not sharp: the value
`ε = ‖G‖` for the normal component is the crudest one, and a tube of radius `1` is wide. What
the example shows is that every hypothesis of the theorem can be checked for a concrete field.

## Main results

* `LeanDLRA.Examples.BUGEndToEnd.exists_run_error_le`: the final statement.
* `LeanDLRA.Examples.BUGEndToEnd.odeSolution_const`: `A(t) = C` solves the equation.
* `LeanDLRA.Examples.BUGEndToEnd.bugGlobalBound_le`: the numerical bound.
-/

open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Examples.BUGEndToEnd

open MatrixBUG

/-! ### 1. The problem -/

/-- The matrix `M = E₂₁` of the linear part `Y ↦ M Y`. -/
def M : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- The matrix `N = 0` of the linear part `Y ↦ Y Nᵀ`. -/
def N : Matrix (Fin 2) (Fin 2) ℝ := 0

/-- The source term `G = -E₂₁`. -/
def G : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; -1, 0]

/-- The stationary point `C = E₁₁`, a matrix of rank one. -/
def C : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- The right-hand side `F(t, Y) = M Y + Y Nᵀ + G` of the differential equation. Time is the
first argument of a field, as everywhere in the library; this field does not depend on it. -/
def field : ℝ → Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
  fun _ Y => M * Y + Y * Nᵀ + G

/-- `C` is a stationary point: `F(t, C) = 0`. Hence `A(t) = C` is the exact solution. -/
theorem stationary : M * C + C * Nᵀ + G = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, N, C, G]

/-- The exact solution, as the library states it: the constant function `A(t) = C` is an
`ODESolution` of `Y' = F(t, Y)` on every interval `[a, b]`. The statement is the first component
of `dlraProblem_linear`, which proves it from `stationary`. -/
theorem odeSolution_const (a b : ℝ) : ODESolution field (fun _ => C) a b :=
  (dlraProblem_linear M N G C stationary a b (ρ := 0) le_rfl).sol

/-! ### 2. The constants of the field -/

/-- The Frobenius norm of `M` is `1`. `Frobenius.norm_def` writes it as the square root of the
sum of the squared entries. -/
theorem norm_M : ‖M‖ = 1 := by
  rw [Frobenius.norm_def]
  simp [M, Fin.sum_univ_two]

/-- The matrix `N` is zero. -/
theorem norm_N : ‖N‖ = 0 := by
  simp [N]

/-- The Frobenius norm of `G` is `1`. -/
theorem norm_G : ‖G‖ = 1 := by
  rw [Frobenius.norm_def]
  simp [G, Fin.sum_univ_two]

/-- The Lipschitz constant `‖M‖ + ‖N‖` of the field is `1`. -/
theorem lipschitzConstant : ‖M‖ + ‖N‖ = 1 := by
  rw [norm_M, norm_N, add_zero]

/-! ### 4. The numbers -/

/-- A bound for the one exponential that the constants contain: `exp (1/10) ≤ 10/9`. It
follows from `exp x < 1 / (1 - x)` for `0 < x < 1`. -/
theorem exp_tenth_le : Real.exp (1 * (1 / 10)) ≤ 10 / 9 := by
  have h := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 10) (by norm_num) (by norm_num)
  rw [one_mul]
  refine h.le.trans ?_
  norm_num

/-- **The numerical bound.** For `L = 1`, `B = 1`, `ε = 1`, `H = T = 1/10`, `δ = 1/100` and
`h = 1/1000` the error bound `bugGlobalBound L B H T δ ε h` is at most `3/10`, and the
smallness condition `bugGlobalBound … + 4 B h < ρ` holds for the tube radius `ρ = 1`. The proof
unfolds the constants `bugC₁` and `bugC₂`; what remains is a polynomial inequality in
`x = exp (1/10)`, which `nlinarith` closes from `0 < x ≤ 10/9`. -/
theorem bugGlobalBound_le {L B ε : ℝ} (hL : L = 1) (hB : B = 1) (hε : ε = 1) :
    bugGlobalBound L B (1 / 10) (1 / 10) (1 / 100) ε (1 / 1000) ≤ 3 / 10 ∧
      bugGlobalBound L B (1 / 10) (1 / 10) (1 / 100) ε (1 / 1000) + 4 * B * (1 / 1000) < 1 := by
  subst hL hB hε
  rw [bugGlobalBound_eq]
  unfold bugC₁ bugC₂
  have hx := exp_tenth_le
  have h1 : 0 < Real.exp (1 * (1 / 10)) := Real.exp_pos _
  generalize Real.exp (1 * (1 / 10)) = x at hx h1 ⊢
  constructor <;> nlinarith [mul_pos h1 h1]

/-! ### 3. The flagship theorem applied to the problem -/

/-- **The BUG integrator on the concrete problem.** Let `Y₀` be a `2 × 2` matrix of rank at most
one with `‖Y₀ - C‖ ≤ 1/100`. Then there are matrices `Y 0 = Y₀, Y 1, …, Y 100` such that each
`Y (j + 1)` is the result of one step of the fixed-rank BUG integrator of rank one
(`MatrixBUG.stepRel field 1`) of size `1/1000` from `Y j` (`IsRun` on `uniformGrid 0 (1/1000)`),
and for every `j ≤ 100` the matrix `Y j` has rank at most one and `‖Y j - C‖ ≤ 3/10`.

The proof is one application of `MatrixBUG.exists_run_norm_sub_le`. Its hypotheses, in order:
`hP` is `dlraProblem_linear` (with the tube radius `1`), `hc` is `continuous_uncurry_linear`,
`hε` is `factoredNormalBoundOn_linear` with `ε = ‖G‖`, then `0 ≤ ε`, `0 ≤ h`, `h ≤ H`, `N h ≤ T`
(here `100 · (1/1000) ≤ 1/10`), the rank conditions `1 ≤ 2`, the two facts about `Y₀`, and the
smallness condition. The constants of the theorem are `L = ‖M‖ + ‖N‖`, `B = (‖M‖ + ‖N‖) · 1` and
`ε = ‖G‖`; section 2 showed that they are `1`, `1` and `1`, and `bugGlobalBound_le` turns the
conclusion and the smallness condition into the numbers `3/10` and `1`. -/
theorem exists_run_error_le {Y₀ : Matrix (Fin 2) (Fin 2) ℝ} (hY₀ : Y₀.rank ≤ 1)
    (hδ : ‖Y₀ - C‖ ≤ 1 / 100) :
    ∃ Y : ℕ → Matrix (Fin 2) (Fin 2) ℝ, Y 0 = Y₀ ∧
      IsRun (stepRel field 1) (uniformGrid 0 (1 / 1000)) 100 Y ∧
      ∀ j ≤ 100, (Y j).rank ≤ 1 ∧ ‖Y j - C‖ ≤ 3 / 10 := by
  -- the three constants of the field and the numbers they give
  obtain ⟨hbound, hsmall⟩ := bugGlobalBound_le (L := ‖M‖ + ‖N‖)
    (B := (‖M‖ + ‖N‖) * 1) (ε := ‖G‖) lipschitzConstant
    (by rw [lipschitzConstant, mul_one]) norm_G
  -- the run and its error bound
  obtain ⟨Y, hY0, hrun, hY⟩ := exists_run_norm_sub_le (F := field) (A := fun _ => C) (r := 1)
    (t₀ := 0) (h := 1 / 1000) (N := 100) (H := 1 / 10) (T := 1 / 10) (ρ := 1)
    (L := ‖M‖ + ‖N‖) (B := (‖M‖ + ‖N‖) * 1) (ε := ‖G‖) (δ := 1 / 100)
    (dlraProblem_linear M N G C stationary _ _ zero_le_one)
    (continuous_uncurry_linear M N G).continuousOn
    (factoredNormalBoundOn_linear M N G _) (norm_nonneg G) (by norm_num) (by norm_num)
    (by norm_num) (by simp) (by simp) hY₀ hδ (by simpa using hsmall)
  exact ⟨Y, hY0, hrun, fun j hj => ⟨(hY j hj).1, (hY j hj).2.trans (by simpa using hbound)⟩⟩

end LeanDLRA.Examples.BUGEndToEnd
