import LeanDLRA.Stiff.ImplicitBUGStep
import LeanDLRA.Integrators.Method
import LeanDLRA.Integrators.Matrix.LinearFieldExample

/-!
# Runs of the fixed-rank BUG integrator with backward Euler substeps

This file shows that the fixed-rank BUG integrator with backward Euler substeps
(`MatrixImplicitBUG.stepRel`, `LeanDLRA/Stiff/Defs.lean`) can be run near a solution of a matrix
differential equation `Y' = F(t, Y)`, and that every run stays close to the solution. The step and
its local error are in `LeanDLRA/Stiff/ImplicitBUGStep.lean`.

**Setting.** Let `A` solve `Y' = F(t, Y)` on `[t₀, t₀ + N h]`. The field `F` is `L`-Lipschitz and
bounded by `B` on the tube of radius `ρ` around `A` (`DLRAProblem`), jointly continuous there,
Lipschitz in time with constant `Lt` on the tube, and its normal component at the rank-`r`
matrices of the tube is at most `ε` (`FactoredNormalBoundOn`). The step size satisfies
`h L ≤ 1/2`.

**Result** (`MatrixImplicitBUG.exists_run_norm_sub_le`). For every start value `Y₀` of rank at most
`r` with `‖Y₀ - A t₀‖ ≤ δ` there is a run `Y 0 = Y₀, …, Y N` of rank at most `r` with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} ((14 L B + 8 Lt) h + 6 ε)` for all `n ≤ N`,

if `N h ≤ T` and the right-hand side plus `4 B h` is smaller than `ρ`. The constants are those of
`implicitBUG_global_error_le` for fields on the whole space; they do not depend on the singular
values of the `Y n`. The bound holds for every run (`MatrixImplicitBUG.IsRun.norm_sub_le`).

**This is not a stiff error bound.** The constants contain the Lipschitz constant `L` through
`e^{L T}`, `L B` and the step size condition `h L ≤ 1/2`; for a stiff field, whose Lipschitz
constant is large, the bound is as poor as for the explicit integrators. Bounds in which only a
one-sided Lipschitz constant enters are in `LeanDLRA/Stiff/ImplicitBUG.lean`
(`residual_global_error`, `implicitGalerkin_compare_global`), under other hypotheses.

## Main results

* `MatrixImplicitBUG.IsRun.norm_sub_le`: every run satisfies the error bound.
* `MatrixImplicitBUG.exists_run_norm_sub_le`: a run exists, has rank at most `r` and satisfies
  the error bound.

## Implementation notes

The integrator is not an instance of `StepMethod.IsTubeLocal`: property (E) there asks for a step
of every globally Lipschitz field and every step size, while a backward Euler stage need not
exist for `h L ≥ 1` (for `r = m = n = 1` and `G(x) = x / h + 1` the K-stage equation reads
`K = U₀ S₀ + K + h V₀`). The run theorem is therefore proved directly from
`exists_isRun_norm_sub_le_of_tube_uniformGrid`, along the lines of
`StepMethod.IsTubeLocal.exists_run_norm_sub_le`: a step of the extension
`tubeExt F A t₀ (t₀ + N h) ρ` exists because the extension is globally `L`-Lipschitz and `h L < 1`
(`MatrixImplicitBUG.exists_stepRel`), and near `A` it is a step of `F`
(`MatrixImplicitBUG.stepRel_tubeExt_iff_of_near`, margin `4 B h`).
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixImplicitBUG

section Error

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {t₀ h T ρ L Lt B ε δ : ℝ}
  {N : ℕ}

/-- The local error of one step of a uniform grid, from the hypotheses of the run theorems. -/
theorem stepRel.hasLocalError_uniformGrid (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → (s, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ →
      (t, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ → ‖F t x - F s x‖ ≤ Lt * (t - s))
    (hh : 0 ≤ h) (hhL : h * L ≤ 1 / 2) {k : ℕ} (hk : k < N) {Y₀ Y₁ : Matrix m n ℝ}
    (hnear : ‖Y₀ - A (t₀ + k * h)‖ + 4 * B * h < ρ)
    (hstep : stepRel F r (t₀ + k * h) (t₀ + (k + 1) * h) Y₀ Y₁) :
    HasLocalError F (t₀ + k * h) (t₀ + (k + 1) * h) Y₀ Y₁
      (h * ((14 * L * B + 8 * Lt) * h + 6 * ε)) := by
  obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hk
  obtain ⟨U₀, S₀, V₀, K₁, L₁, U₁, V₁, S₁, rfl, hs, rfl⟩ := hstep
  have hloc := hs.hasLocalError_of_tube_le hε hε₀ hP.lipschitz hP.L_nonneg hP.bounded
    hP.B_nonneg hLt hFt ha hb h01 (by rw [hsub]; exact hhL) (hP.sol.mono ha hb)
    (by rw [hsub]; exact hnear)
  rwa [hsub] at hloc

/-- **Every run satisfies the error bound.** Let `A` solve `Y' = F(t, Y)` on `[t₀, t₀ + N h]`,
let `F` be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around `A`
(`DLRAProblem`), jointly continuous there, Lipschitz in time with constant `Lt` on the tube, and
with normal component at most `ε` at the rank-`r` matrices of the tube. Let `0 ≤ h`,
`h L ≤ 1/2`, `N h ≤ T`, and let `Y` be a run of the BUG integrator with backward Euler substeps
with `‖Y 0 - A t₀‖ ≤ δ`. If the bound below plus `4 B h` is smaller than `ρ`, then for `n ≤ N`

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} ((14 L B + 8 Lt) h + 6 ε)`.

This is not a stiff bound: `L` enters through `e^{L T}`, `L B` and `h L ≤ 1/2`. -/
theorem IsRun.norm_sub_le {Y : ℕ → Matrix m n ℝ}
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → (s, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ →
      (t, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ → ‖F t x - F s x‖ ≤ Lt * (t - s))
    (hh : 0 ≤ h) (hhL : h * L ≤ 1 / 2) (hNT : N * h ≤ T)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) * ((14 * L * B + 8 * Lt) * h + 6 * ε) +
      4 * B * h < ρ)
    (hY : IsRun (stepRel F r) (uniformGrid t₀ h) N Y) (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (L * T) * δ + T * Real.exp (L * T) * ((14 * L * B + 8 * Lt) * h + 6 * ε) := by
  have hL := hP.L_nonneg
  have hB := hP.B_nonneg
  have hc₀ : 0 ≤ (14 * L * B + 8 * Lt) * h + 6 * ε := by positivity
  have hBh : 0 ≤ B * h := mul_nonneg hB hh
  exact hY.norm_sub_le_of_tube_uniformGrid hP hc
    (fun k hk Y₀ Y₁ hnear hstep => stepRel.hasLocalError_uniformGrid hP hε hε₀ hLt hFt hh hhL
      hk (by linarith) hstep) hc₀ hδ hNT (by linarith)

/-- **Existence and error bound for the BUG integrator with backward Euler substeps.** Under the
hypotheses of `MatrixImplicitBUG.IsRun.norm_sub_le`, with `r ≤ m`, `r ≤ n` and a start value `Y₀`
of rank at most `r` with `‖Y₀ - A t₀‖ ≤ δ`, there are `Y 0 = Y₀, Y 1, …, Y N`, each obtained from
the previous one by a step of size `h`, all of rank at most `r`, with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} ((14 L B + 8 Lt) h + 6 ε)` for all `n ≤ N`.

Nothing is assumed about `F` outside the tube; the stages of every step are the limits of the
fixed-point iterations from the start values (`MatrixImplicitBUG.IsStep`). This is not a stiff
bound: `L` enters through `e^{L T}`, `L B` and `h L ≤ 1/2`. -/
theorem exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → (s, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ →
      (t, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ → ‖F t x - F s x‖ ≤ Lt * (t - s))
    (hh : 0 ≤ h) (hhL : h * L ≤ 1 / 2) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) * ((14 * L * B + 8 * Lt) * h + 6 * ε) +
      4 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * δ + T * Real.exp (L * T) * ((14 * L * B + 8 * Lt) * h + 6 * ε) := by
  have hL := hP.L_nonneg
  have hB := hP.B_nonneg
  have hc₀ : 0 ≤ (14 * L * B + 8 * Lt) * h + 6 * ε := by positivity
  have hBh : 0 ≤ B * h := mul_nonneg hB hh
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg N) hh).trans hNT
  have hR : 0 ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) * ((14 * L * B + 8 * Lt) * h + 6 * ε) :=
    add_nonneg (mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans hδ))
      (mul_nonneg (mul_nonneg hT (Real.exp_pos _).le) hc₀)
  have hρ : 0 ≤ ρ := by linarith
  have hGL : IsLipschitzField (tubeExt F A t₀ (t₀ + N * h) ρ) L :=
    isLipschitzField_tubeExt hP.lipschitz hL hρ
  refine exists_isRun_norm_sub_le_of_tube_uniformGrid (M := stepRel F r)
    (Adm := fun _ Y => Y.rank ≤ r) hP hc (fun k hk Z₀ hZ₀ hnear => ?_)
    (fun k _ Z₀ Z₁ _ _ hstep => hstep.rank_le)
    (fun k hk Z₀ Z₁ _ hnear hstep => stepRel.hasLocalError_uniformGrid hP hε hε₀ hLt hFt hh hhL
      hk (by linarith) hstep) hc₀ hh hNT hY₀ hδ (by linarith)
  -- a step of the extended field exists, and it is a step of `F`
  obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hk
  obtain ⟨Z₁, hZ₁⟩ := exists_stepRel hGL h01 (by rw [hsub]; linarith) hrm hrn hZ₀
  exact ⟨Z₁, (stepRel_tubeExt_iff_of_near hP.bounded hB ha hb h01 (hP.sol.mono ha hb)
    (by rw [hsub]; linarith)).1 hZ₁⟩

end Error

/-! ### Non-vacuity: the linear field `F(t, Y) = M Y + Y Nᵀ + G` -/

section Examples

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}

/-- **Non-vacuity of `MatrixImplicitBUG.exists_stepRel`.** For the globally Lipschitz linear
field `F(t, Y) = M Y + Y Nᵀ + G` (Lipschitz constant `‖M‖ + ‖N‖`) a step exists from every
start value of rank at most `r` if `h (‖M‖ + ‖N‖) < 1`. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G : Matrix m n ℝ) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    (hhL : (t₁ - t₀) * (‖M‖ + ‖N‖) < 1) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) :
    ∃ Y₁, stepRel (fun _ Y => M * Y + Y * Nᵀ + G) r t₀ t₁ Y₀ Y₁ :=
  exists_stepRel (isLipschitzField_linear M N G) h01 hhL hrm hrn hY₀

variable [DecidableEq m] [DecidableEq n]

/-- **Non-vacuity of `MatrixImplicitBUG.stepRel.hasLocalError_uniformGrid`.** For the linear
field `F(t, Y) = M Y + Y Nᵀ + G` with a stationary point `C` and `h (‖M‖ + ‖N‖) ≤ 1/2`, step
`k < K` of the uniform grid exists from every `Y₀` of rank at most `r`; if `Y₀` lies near `C`,
its local error is at most `h ((14 L B + 8 · 0) h + 6 ‖G‖)` with `L = ‖M‖ + ‖N‖` and
`B = (‖M‖ + ‖N‖) ρ`. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    (t₀ : ℝ) {ρ h : ℝ} {K k : ℕ} (hρ : 0 ≤ ρ) (hh : 0 ≤ h) (hhL : h * (‖M‖ + ‖N‖) ≤ 1 / 2)
    (hk : k < K) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r)
    (hnear : ‖Y₀ - C‖ + 4 * ((‖M‖ + ‖N‖) * ρ) * h < ρ) :
    ∃ Y₁, stepRel (fun _ Y => M * Y + Y * Nᵀ + G) r (t₀ + k * h) (t₀ + (k + 1) * h) Y₀ Y₁ ∧
      HasLocalError (fun _ Y => M * Y + Y * Nᵀ + G) (t₀ + k * h) (t₀ + (k + 1) * h) Y₀ Y₁
        (h * ((14 * (‖M‖ + ‖N‖) * ((‖M‖ + ‖N‖) * ρ) + 8 * 0) * h + 6 * ‖G‖)) := by
  have e : t₀ + (k + 1) * h - (t₀ + k * h) = h := by ring
  obtain ⟨Y₁, hY⟩ := exists_stepRel (isLipschitzField_linear M N G)
    (by rw [← sub_nonneg, e]; exact hh : t₀ + k * h ≤ t₀ + (k + 1) * h) (by rw [e]; linarith)
    hrm hrn hY₀
  exact ⟨Y₁, hY, stepRel.hasLocalError_uniformGrid (A := fun _ => C)
    (dlraProblem_linear M N G C hC _ _ hρ) (factoredNormalBoundOn_linear M N G _) (norm_nonneg G)
    le_rfl (fun _ _ _ _ _ _ => by simp) hh hhL hk hnear hY⟩

/-- **Non-vacuity of `MatrixImplicitBUG.exists_run_norm_sub_le`.** The linear field
`F(t, Y) = M Y + Y Nᵀ + G` with a stationary point `C` (`M C + C Nᵀ + G = 0`, possible with
`G ≠ 0`: `M = -1`, `N = 0`, `C = G`) is `(‖M‖ + ‖N‖)`-Lipschitz and bounded by
`(‖M‖ + ‖N‖) ρ` on the tube of radius `ρ` around `A(t) = C`, does not depend on time (`Lt = 0`),
and its normal component at rank-`r` matrices is at most `‖G‖`. Under `h (‖M‖ + ‖N‖) ≤ 1/2` and
the smallness condition, the integrator can be run from every `Y₀` of rank at most `r` near `C`,
and the run satisfies the error bound with `ε = ‖G‖`. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    (t₀ : ℝ) {ρ T δ h : ℝ} {K : ℕ} (hρ : 0 ≤ ρ) (hh : 0 ≤ h)
    (hhL : h * (‖M‖ + ‖N‖) ≤ 1 / 2) (hKT : K * h ≤ T) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r)
    (hδ : ‖Y₀ - C‖ ≤ δ)
    (hsmall : Real.exp ((‖M‖ + ‖N‖) * T) * δ + T * Real.exp ((‖M‖ + ‖N‖) * T) *
      ((14 * (‖M‖ + ‖N‖) * ((‖M‖ + ‖N‖) * ρ) + 8 * 0) * h + 6 * ‖G‖) +
      4 * ((‖M‖ + ‖N‖) * ρ) * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (stepRel (fun _ Y => M * Y + Y * Nᵀ + G) r) (uniformGrid t₀ h) K Y ∧
      ∀ j ≤ K, (Y j).rank ≤ r ∧ ‖Y j - C‖ ≤ Real.exp ((‖M‖ + ‖N‖) * T) * δ +
        T * Real.exp ((‖M‖ + ‖N‖) * T) *
          ((14 * (‖M‖ + ‖N‖) * ((‖M‖ + ‖N‖) * ρ) + 8 * 0) * h + 6 * ‖G‖) :=
  exists_run_norm_sub_le (A := fun _ => C) (dlraProblem_linear M N G C hC _ _ hρ)
    (continuous_uncurry_linear M N G).continuousOn (factoredNormalBoundOn_linear M N G _)
    (norm_nonneg G) le_rfl (fun _ _ _ _ _ _ => by simp) hh hhL hKT hrm hrn hY₀ hδ hsmall

/-- **Non-vacuity of `MatrixImplicitBUG.IsRun.norm_sub_le`.** Every run of the integrator for the
linear field of the previous example that starts near the stationary point `C` satisfies the
error bound. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) (t₀ : ℝ) {ρ T δ h : ℝ} {K : ℕ} (hρ : 0 ≤ ρ) (hh : 0 ≤ h)
    (hhL : h * (‖M‖ + ‖N‖) ≤ 1 / 2) (hKT : K * h ≤ T) {Y : ℕ → Matrix m n ℝ}
    (hY : IsRun (stepRel (fun _ Y => M * Y + Y * Nᵀ + G) r) (uniformGrid t₀ h) K Y)
    (hδ : ‖Y 0 - C‖ ≤ δ)
    (hsmall : Real.exp ((‖M‖ + ‖N‖) * T) * δ + T * Real.exp ((‖M‖ + ‖N‖) * T) *
      ((14 * (‖M‖ + ‖N‖) * ((‖M‖ + ‖N‖) * ρ) + 8 * 0) * h + 6 * ‖G‖) +
      4 * ((‖M‖ + ‖N‖) * ρ) * h < ρ) :
    ∀ j ≤ K, ‖Y j - C‖ ≤ Real.exp ((‖M‖ + ‖N‖) * T) * δ + T * Real.exp ((‖M‖ + ‖N‖) * T) *
      ((14 * (‖M‖ + ‖N‖) * ((‖M‖ + ‖N‖) * ρ) + 8 * 0) * h + 6 * ‖G‖) :=
  IsRun.norm_sub_le (A := fun _ => C) (dlraProblem_linear M N G C hC _ _ hρ)
    (continuous_uncurry_linear M N G).continuousOn (factoredNormalBoundOn_linear M N G _)
    (norm_nonneg G) le_rfl (fun _ _ _ _ _ _ => by simp) hh hhL hKT hsmall hY hδ

/-- **A concrete instance of `MatrixImplicitBUG.exists_stepRel`** (the data of
`LinearFieldExample`). For the linear field `F(t, Y) = -E Y + E` on `2 × 2` matrices with
`E = e₁ e₁ᵀ` (Lipschitz constant `‖-E‖ + ‖0‖ = 1`), the step size `1/2` satisfies
`h (‖M‖ + ‖N‖) < 1`, and a step of rank `1` exists from the rank-one start value
`(5/4) e₁ e₁ᵀ`. -/
example (t₀ : ℝ) :
    ∃ Y₁, stepRel (fun _ Y => -Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0] * Y +
      Y * (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ + Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]) 1 t₀
      (t₀ + 1 / 2) (Matrix.vecMulVec ![5 / 4, 0] ![1, 0]) Y₁ :=
  exists_stepRel LinearFieldExample.isLipschitzField (by linarith)
    (by rw [add_sub_cancel_left]; norm_num) (by simp) (by simp) (Matrix.rank_vecMulVec_le _ _)

/-- **A concrete instance of `MatrixImplicitBUG.exists_run_norm_sub_le` and
`MatrixImplicitBUG.IsRun.norm_sub_le`** (the data of `LinearFieldExample`). On `2 × 2` matrices
with rank `r = 1`, take `M = -E`, `N = 0` and `G = C = E` with `E = e₁ e₁ᵀ`, so that
`M C + C Nᵀ + G = 0`, `L = ‖M‖ + ‖N‖ = 1`, `B = ρ` and `‖G‖ = 1`; the start value
`Y₀ = (5/4) e₁ e₁ᵀ` has rank one and `‖Y₀ - C‖ = 1/4`. With `K = 10` steps of size `h = 1/100`
(so `h L ≤ 1/2`) up to `T = 1/10` and the tube radius `ρ = 4` the smallness condition holds
(`e^{1/10} ≤ 3`): a run of the implicit BUG integrator exists, and, as every run that starts
near `C`, it satisfies the error bound. -/
example (t₀ : ℝ) :
    ∃ Y : ℕ → Matrix (Fin 2) (Fin 2) ℝ, Y 0 = Matrix.vecMulVec ![5 / 4, 0] ![1, 0] ∧
      IsRun (stepRel (fun _ Y => -Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0] * Y +
        Y * (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ + Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]) 1)
        (uniformGrid t₀ (1 / 100)) 10 Y ∧
      ∀ j ≤ 10, (Y j).rank ≤ 1 ∧ ‖Y j - Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]‖ ≤
        Real.exp (1 * (1 / 10)) * (1 / 4) + 1 / 10 * Real.exp (1 * (1 / 10)) *
          ((14 * 1 * 4 + 8 * 0) * (1 / 100) + 6 * 1) := by
  have he := LinearFieldExample.exp_le_three
  have hsmall : Real.exp (1 * (1 / 10)) * (1 / 4) + 1 / 10 * Real.exp (1 * (1 / 10)) *
      ((14 * 1 * 4 + 8 * 0) * (1 / 100) + 6 * 1) + 4 * 4 * (1 / 100) < 4 := by
    linarith
  have hP := LinearFieldExample.dlraProblem t₀ (t₀ + ((10 : ℕ) : ℝ) * (1 / 100)) (ρ := 4)
    (by norm_num)
  have hε := LinearFieldExample.factoredNormalBoundOn 1
    (tubeSet (fun _ => Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]) t₀
      (t₀ + ((10 : ℕ) : ℝ) * (1 / 100)) 4)
  have hc := (continuous_uncurry_linear (-Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0])
    (0 : Matrix (Fin 2) (Fin 2) ℝ) (Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0])).continuousOn
    (s := tubeSet (fun _ => Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]) t₀
      (t₀ + ((10 : ℕ) : ℝ) * (1 / 100)) 4)
  obtain ⟨Y, hY0, hY, hbd⟩ := exists_run_norm_sub_le hP hc hε zero_le_one le_rfl
    (fun _ _ _ _ _ _ => by simp) (by norm_num) (by norm_num) (by norm_num) (by simp) (by simp)
    (Matrix.rank_vecMulVec_le _ _) LinearFieldExample.norm_start_sub_le hsmall
  have hδY : ‖Y 0 - Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]‖ ≤ 1 / 4 := by
    rw [hY0]
    exact LinearFieldExample.norm_start_sub_le
  have hrun := IsRun.norm_sub_le hP hc hε zero_le_one le_rfl (fun _ _ _ _ _ _ => by simp)
    (by norm_num) (by norm_num) (by norm_num) hsmall hY hδY
  exact ⟨Y, hY0, hY, fun j hj => ⟨(hbd j hj).1, hrun j hj⟩⟩

/-- **A concrete instance of `MatrixImplicitBUG.stepRel.hasLocalError_uniformGrid`** for the
linear field `-E Y + E` of the previous example (`L = 1`, bound `B = 4` on the tube of radius
`ρ = 4`, `‖G‖ = 1`): the first step of size `h = 1/100` from `Y₀ = (5/4) e₁ e₁ᵀ` exists, and since
`‖Y₀ - C‖ + 4 B h = 1/4 + 16/100 < 4` it has local error at most `h ((14 L B + 8 · 0) h + 6)`. -/
example (t₀ : ℝ) :
    ∃ Y₁, stepRel (fun _ Y => -Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0] * Y +
        Y * (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ + Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]) 1
        (t₀ + ((0 : ℕ) : ℝ) * (1 / 100)) (t₀ + (((0 : ℕ) : ℝ) + 1) * (1 / 100))
        (Matrix.vecMulVec ![5 / 4, 0] ![1, 0]) Y₁ ∧
      HasLocalError (fun _ Y => -Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0] * Y +
        Y * (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ + Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0])
        (t₀ + ((0 : ℕ) : ℝ) * (1 / 100)) (t₀ + (((0 : ℕ) : ℝ) + 1) * (1 / 100))
        (Matrix.vecMulVec ![5 / 4, 0] ![1, 0]) Y₁
        (1 / 100 * ((14 * 1 * 4 + 8 * 0) * (1 / 100) + 6 * 1)) := by
  have e : t₀ + (((0 : ℕ) : ℝ) + 1) * (1 / 100) - (t₀ + ((0 : ℕ) : ℝ) * (1 / 100)) = 1 / 100 := by
    push_cast
    ring
  obtain ⟨Y₁, hY⟩ := exists_stepRel LinearFieldExample.isLipschitzField
    (by rw [← sub_nonneg, e]; norm_num) (by rw [e]; norm_num) (by simp) (by simp)
    (Matrix.rank_vecMulVec_le ![(5 / 4 : ℝ), 0] ![1, 0])
  have hP := LinearFieldExample.dlraProblem t₀ (t₀ + ((1 : ℕ) : ℝ) * (1 / 100)) (ρ := 4)
    (by norm_num)
  have hε := LinearFieldExample.factoredNormalBoundOn 1
    (tubeSet (fun _ => Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]) t₀
      (t₀ + ((1 : ℕ) : ℝ) * (1 / 100)) 4)
  exact ⟨Y₁, hY, stepRel.hasLocalError_uniformGrid hP hε zero_le_one le_rfl
    (fun _ _ _ _ _ _ => by simp) (by norm_num) (by norm_num) (k := 0) (by norm_num)
    (by linarith [LinearFieldExample.norm_start_sub_le]) hY⟩

end Examples

end MatrixImplicitBUG

end LeanDLRA
