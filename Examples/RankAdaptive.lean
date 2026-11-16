import Examples.BUGEndToEnd
import LeanDLRA.Integrators.Matrix.TruncBUGRun

/-!
# Worked example: the BUG integrator with augmented bases, truncated to rank one

This file continues `Examples/BUGEndToEnd.lean` and uses its problem: the linear equation
`Y' = M Y + Y Nᵀ + G` for `2 × 2` matrices with the exact solution `A(t) = C`. The integrator is
now the BUG integrator whose bases are augmented (they have `2 r` columns instead of `r`) and
whose result is truncated back to rank `r`; this is the form in which the rank can adapt. The
truncation need not be the best one: a truncation whose error is at most `κ` times the error of
the best truncation is allowed (`κ ≥ 1`), and `κ = 1` is the best truncation. The theorem is
`MatrixBUG.trunc_exists_run_norm_sub_le`; the hypotheses on the field are those of
`MatrixBUG.exists_run_norm_sub_le`, so everything the first file proved about the problem is used
again. The only new work is the numerical bound, because the error bound of the truncated
integrator is larger:

  `e^{L T} δ + T e^{L T} (κ (10 L B h + ε) + (1 + κ) (c₁ ε + c₂ h))`.

## Main results

* `LeanDLRA.Examples.RankAdaptive.truncBound_le`: the numerical bound.
* `LeanDLRA.Examples.RankAdaptive.exists_run_error_le_trunc`: the final statement.
-/

open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Examples.RankAdaptive

open MatrixBUG BUGEndToEnd

/-- **The numerical bound for the truncated integrator.** For `κ = 1`, `L = B = ε = 1`,
`H = T = 1/10`, `δ = 1/100` and `h = 1/1000` the right-hand side of the error bound is at most
`7/10` and, with the margin `4 B h`, smaller than the tube radius `1`. The proof is the one of
`BUGEndToEnd.bugGlobalBound_le`: a polynomial inequality in `x = exp (1/10)`. -/
theorem truncBound_le {L B ε : ℝ} (hL : L = 1) (hB : B = 1) (hε : ε = 1) :
    Real.exp (L * (1 / 10)) * (1 / 100) + (1 / 10) * Real.exp (L * (1 / 10)) *
      (1 * (10 * L * B * (1 / 1000) + ε) +
        (1 + 1) * (bugC₁ L (1 / 10) * ε + bugC₂ L B (1 / 10) * (1 / 1000))) ≤ 7 / 10 ∧
    Real.exp (L * (1 / 10)) * (1 / 100) + (1 / 10) * Real.exp (L * (1 / 10)) *
      (1 * (10 * L * B * (1 / 1000) + ε) +
        (1 + 1) * (bugC₁ L (1 / 10) * ε + bugC₂ L B (1 / 10) * (1 / 1000))) +
      4 * B * (1 / 1000) < 1 := by
  subst hL hB hε
  unfold bugC₁ bugC₂
  have hx := exp_tenth_le
  have h1 : 0 < Real.exp (1 * (1 / 10)) := Real.exp_pos _
  generalize Real.exp (1 * (1 / 10)) = x at hx h1 ⊢
  constructor <;> nlinarith [mul_pos h1 h1]

/-- **The truncated BUG integrator on the concrete problem.** For every `2 × 2` matrix `Y₀` of
rank at most one with `‖Y₀ - C‖ ≤ 1/100` there are matrices `Y 0 = Y₀, …, Y 100`, each the result
of one step of `MatrixBUG.truncStepRel field 1 1` (augmented bases, truncation to rank one with
the best truncation, `κ = 1`) of size `1/1000`, all of rank at most one, with
`‖Y j - C‖ ≤ 7/10`. The bound is larger than the `3/10` of the integrator whose bases keep one
column: the truncation adds the term `κ (10 L B h + ε)`, and the factor `1 + κ` doubles the error
of the augmented step. The proof is the one of `BUGEndToEnd.exists_run_error_le` with the theorem
`MatrixBUG.trunc_exists_run_norm_sub_le`, which has one more hypothesis, `1 ≤ κ`. -/
theorem exists_run_error_le_trunc {Y₀ : Matrix (Fin 2) (Fin 2) ℝ} (hY₀ : Y₀.rank ≤ 1)
    (hδ : ‖Y₀ - C‖ ≤ 1 / 100) :
    ∃ Y : ℕ → Matrix (Fin 2) (Fin 2) ℝ, Y 0 = Y₀ ∧
      IsRun (truncStepRel field 1 1) (uniformGrid 0 (1 / 1000)) 100 Y ∧
      ∀ j ≤ 100, (Y j).rank ≤ 1 ∧ ‖Y j - C‖ ≤ 7 / 10 := by
  obtain ⟨hbound, hsmall⟩ := truncBound_le (L := ‖M‖ + ‖N‖) (B := (‖M‖ + ‖N‖) * 1)
    (ε := ‖G‖) lipschitzConstant (by rw [lipschitzConstant, mul_one]) norm_G
  obtain ⟨Y, hY0, hrun, hY⟩ := trunc_exists_run_norm_sub_le (F := field) (A := fun _ => C)
    (r := 1) (κ := 1) (t₀ := 0) (h := 1 / 1000) (N := 100) (H := 1 / 10) (T := 1 / 10)
    (ρ := 1) (L := ‖M‖ + ‖N‖) (B := (‖M‖ + ‖N‖) * 1) (ε := ‖G‖) (δ := 1 / 100)
    (dlraProblem_linear M N G C stationary _ _ zero_le_one)
    (continuous_uncurry_linear M N G).continuousOn
    (factoredNormalBoundOn_linear M N G _) (norm_nonneg G) le_rfl (by norm_num) (by norm_num)
    (by norm_num) (by simp) (by simp) hY₀ hδ (by simpa using hsmall)
  exact ⟨Y, hY0, hrun, fun j hj => ⟨(hY j hj).1, (hY j hj).2.trans (by simpa using hbound)⟩⟩

end LeanDLRA.Examples.RankAdaptive
