import LeanDLRA.Integrators.Matrix.AdaptiveBUGStep

/-!
# Runs of the augmented BUG integrator with truncation to a fixed rank

This file closes the theory of the basis-update & Galerkin (BUG) integrator that works with the
augmented bases of Ceruti, Kusch and Lubich ([CerutiKuschLubich2022]) and truncates the result of
every step back to a fixed rank `r`, for a matrix differential equation `Y' = F(t, Y)`: the
integrator can be run, and every run stays close to the exact solution. The step relation
`MatrixBUG.truncStepRel` and its local error are in
`LeanDLRA/Integrators/Matrix/AdaptiveBUGStep.lean`.

**Setting.** Let `A` be a solution of `Y' = F(t, Y)` on `[t₀, t₀ + N h]`. The field `F` is only
assumed to be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around `A`
(`DLRAProblem F A t₀ (t₀ + N h) ρ L B`), jointly continuous there, and to have a small normal
component at the rank-`r` matrices in the tube (`FactoredNormalBoundOn F r _ ε`): for every
`Y = U S Vᵀ` with orthonormal `U`, `V` the part `(I - U Uᵀ) F(t, Y) (I - V Vᵀ)` of the field that
points away from both the column and the row space of `Y` has norm at most `ε`. Nothing is
assumed about `F` outside the tube. The truncation is any matrix of rank at most `r` whose
distance to the augmented matrix is at most `κ` times the smallest possible one, `κ ≥ 1`.

**Result** (`MatrixBUG.trunc_exists_run_norm_sub_le`). For every start value `Y₀` of rank at
most `r` with `‖Y₀ - A t₀‖ ≤ δ` there are matrices `Y 0 = Y₀, Y 1, …, Y N`, each obtained from
the previous one by an augmented BUG step of size `h ≤ H` followed by such a truncation
(`IsRun (MatrixBUG.truncStepRel F r κ) (uniformGrid t₀ h) N Y`), all of rank at most `r`, with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (κ (10 L B h + ε) + (1 + κ) (c₁ ε + c₂ h))`

for all `n ≤ N`, where `N h ≤ T`, `c₁ = bugC₁ L H` and `c₂ = bugC₂ L B H`. The constants do not
depend on the singular values of the matrices `Y n`. The only further hypothesis is that the
right-hand side is smaller than the tube radius, with a margin of four step lengths at the speed
bound: the right-hand side plus `4 B h` is less than `ρ`. The same bound holds for every run
(`MatrixBUG.IsRun.norm_sub_le_of_truncStepRel`).

## Main results

* `MatrixBUG.IsRun.rank_le_of_truncStepRel`: all values of a run have rank at most `r`.
* `MatrixBUG.trunc_exists_run`: for a field that is Lipschitz everywhere there is a run on every
  grid from every start value of rank at most `r`.
* `MatrixBUG.isTubeLocal_truncStepRel`: the integrator is a tube-local method
  (`StepMethod.IsTubeLocal`) with the matrices of rank at most `r` as admissible values and
  margin constant `4`.
* `MatrixBUG.truncStepRel.hasLocalError_uniformGrid`: the local error of one step of a uniform
  grid, from the hypotheses of the run theorem.
* `MatrixBUG.IsRun.norm_sub_le_of_truncStepRel`: every run satisfies the error bound.
* `MatrixBUG.trunc_exists_run_norm_sub_le`: a run exists, has rank at most `r` and satisfies the
  error bound.

The examples at the end apply the result to the field `F(t, Y) = Y / max ‖Y‖ 1`, which has no
normal component, so that `ε = 0`, and to the linear field `F(t, Y) = M Y + Y Nᵀ + G`, which is
not bounded and has `ε = ‖G‖`. The last example treats a truncation that is computed only up to
an error `ϑ`, through the run theorem with a tolerance
(`StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_tol`).

## Implementation notes

`MatrixBUG.trunc_exists_run_norm_sub_le` is an instance of the theorem for tube-local methods,
`StepMethod.IsTubeLocal.exists_run_norm_sub_le`, in the same way as
`MatrixBUG.exists_run_norm_sub_le` for the BUG integrator whose bases keep `r` columns; the
hypotheses they share have the same names and the same order, and `1 ≤ κ` is added. The margin
constant `4` is that of the BUG step; the truncation does not evaluate the field.

No truncation tolerance appears in the bound: the rank after every step is `r`, and the error of
the truncation is bounded by the distance of the exact solution to the matrices of rank at most
`r`, which is small because the start value of the step has rank at most `r`. This is why no
state other than the matrix `Y n` is needed, in particular no rank that changes from step to
step. The integrator whose rank is chosen by a tolerance is `MatrixBUG.adaptiveStepRel`.

For `κ = 1` the constant in front of `h` is `10 L B + 2 c₂` and the one in front of `ε` is
`1 + 2 c₁`. The BUG integrator whose bases keep `r` columns has `c₂` and `c₁`
(`MatrixBUG.exists_run_norm_sub_le`); the constants here are larger because the result of the
augmented step is compared with the exact solution before and after the truncation. They are
not optimised.

## References

* G. Ceruti, J. Kusch, Ch. Lubich, *A rank-adaptive robust integrator for dynamical low-rank
  approximation*, [CerutiKuschLubich2022] (BIT Numer. Math. 2022).
* G. Ceruti, Ch. Lubich, *An unconventional robust integrator for dynamical low-rank
  approximation*, [CerutiLubich2022] (BIT Numer. Math. 2022).
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixBUG

/-! ### Existence of runs for a field that is Lipschitz everywhere -/

section Exists

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
  {L κ : ℝ}

/-- All values of a run of the augmented BUG integrator with truncation to rank `r` have rank at
most `r`, provided the start value has. -/
theorem IsRun.rank_le_of_truncStepRel {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → Matrix m n ℝ}
    (hY : IsRun (truncStepRel F r κ) τ N Y) (h0 : (Y 0).rank ≤ r) : ∀ n ≤ N, (Y n).rank ≤ r
  | 0, _ => h0
  | n + 1, hn => (hY.step n hn).rank_le

/-- **Runs of the augmented BUG integrator with truncation to rank `r` exist.** If `F` is
Lipschitz (globally) and continuous in time on `[τ 0, τ N]`, `r ≤ m`, `r ≤ n` and `κ ≥ 1`, then
on the grid `τ` there is a run of `N` steps from every start value `Y₀` of rank at most `r`. No
bound on the field is needed. For fields that are Lipschitz only near a solution see
`MatrixBUG.trunc_exists_run_norm_sub_le`. -/
theorem trunc_exists_run (hF : IsLipschitzField F L) {τ : ℕ → ℝ} {N : ℕ} (hτ : IsGrid τ N)
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc (τ 0) (τ N))) (hκ : 1 ≤ κ)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (truncStepRel F r κ) τ N Y := by
  refine exists_isRun hτ Y₀ fun n hn Y hY0 hY => ?_
  have hsub : Icc (τ n) (τ (n + 1)) ⊆ Icc (τ 0) (τ N) :=
    Icc_subset_Icc (hτ.le_of_le n.zero_le hn.le) (hτ.le_of_le (Nat.succ_le_of_lt hn) le_rfl)
  exact exists_truncStepRel hF (fun Z => (hc Z).mono hsub) (hτ.mono n hn) hκ hrm hrn
    (IsRun.rank_le_of_truncStepRel hY (by rw [hY0]; exact hY₀) n le_rfl)

/-- **The augmented BUG integrator with truncation to rank `r` is a tube-local method**
(`StepMethod.IsTubeLocal`), with the matrices of rank at most `r` as admissible values and
margin constant `4`, for every `κ ≥ 1`:

* a step exists from every matrix of rank at most `r`, for every globally Lipschitz field that is
  continuous in time on the step interval (`MatrixBUG.exists_truncStepRel`); this is where
  `κ ≥ 1` is used, a best approximation of rank at most `r` being a truncation;
* the result of a step has rank at most `r` (`MatrixBUG.truncStepRel.rank_le`); the augmented
  matrix of rank up to `2 r` is hidden inside the step;
* if `‖Y₀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, a step from `Y₀` of the extended field
  `tubeExt F A a b ρ` is a step of `F` (`MatrixBUG.truncStepRel_tubeExt_iff_of_near`).

With the local error `MatrixBUG.truncStepRel.hasLocalError_of_tube` this is all that
`StepMethod.IsTubeLocal.exists_run_norm_sub_le` needs. -/
theorem isTubeLocal_truncStepRel (hκ : 1 ≤ κ) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) :
    StepMethod.IsTubeLocal (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => truncStepRel G r κ)
      (fun Y => Y.rank ≤ r) 4 where
  exists_step := fun hG hc h01 hY₀ => exists_truncStepRel hG hc h01 hκ hrm hrn hY₀
  adm_of_step := fun _ _ hstep => hstep.rank_le
  step_of_tubeExt := fun hFB hB ha hb h01 hA _ hsmall hstep =>
    (truncStepRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 hstep

end Exists

/-! ### The error bound, and existence of a run near the exact solution -/

section Error

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {t₀ h H T ρ L B ε δ κ : ℝ}
  {N : ℕ}

/-- The constant of the error bound of this file is not negative. -/
private theorem truncConst_nonneg_aux {κ L B H ε h : ℝ} (hκ : 0 ≤ κ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hH : 0 ≤ H) (hε₀ : 0 ≤ ε) (hh : 0 ≤ h) :
    0 ≤ κ * (10 * L * B * h + ε) + (1 + κ) * (bugC₁ L H * ε + bugC₂ L B H * h) :=
  add_nonneg
    (mul_nonneg hκ (add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) hB) hh) hε₀))
    (mul_nonneg (add_nonneg zero_le_one hκ) (add_nonneg (mul_nonneg (bugC₁_nonneg hL hH) hε₀)
      (mul_nonneg (bugC₂_nonneg hL hB hH) hh)))

/-- **Local error of one step of a uniform grid.** Under the hypotheses of the run theorem on
`F` and `A` (`DLRAProblem`, joint continuity and `FactoredNormalBoundOn` on the tube of radius
`ρ` around `A` over `[t₀, t₀ + N h]`), a step of the augmented BUG integrator with truncation to
rank `r` over `[t₀ + k h, t₀ + (k + 1) h]`, `k < N`, `h ≤ H`, whose start value `Z₀` satisfies
`‖Z₀ - A (t₀ + k h)‖ + 4 B h < ρ` has local error
`h (κ (10 L B h + ε) + (1 + κ) (c₁ ε + c₂ h))` with `c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`. -/
theorem truncStepRel.hasLocalError_uniformGrid {k : ℕ} {Z₀ Z₁ : Matrix m n ℝ}
    (hstep : truncStepRel F r κ (t₀ + k * h) (t₀ + (k + 1) * h) Z₀ Z₁) (hκ : 0 ≤ κ)
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hk : k < N)
    (hnear : ‖Z₀ - A (t₀ + k * h)‖ + 4 * B * h < ρ) :
    HasLocalError F (t₀ + k * h) (t₀ + (k + 1) * h) Z₀ Z₁
      (h * (κ * (10 * L * B * h + ε) + (1 + κ) * (bugC₁ L H * ε + bugC₂ L B H * h))) := by
  obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hk
  have hloc := hstep.hasLocalError_of_tube hκ hε hε₀ hP.lipschitz hP.L_nonneg hP.bounded
    hP.B_nonneg hc hP.sol.cont ha hb h01 (hsub.le.trans hhH) (hP.sol.mono ha hb)
    (by rw [hsub]; exact hnear)
  rwa [hsub] at hloc

/-- **Every run of the augmented BUG integrator with truncation to rank `r` satisfies the robust
error bound.** Let `A` solve `Y' = F(t, Y)` on `[t₀, t₀ + N h]`, and let `F` be `L`-Lipschitz
and bounded by `B` on the tube of radius `ρ` around `A` (`DLRAProblem`), jointly continuous
there, with normal component at most `ε` at the rank-`r` matrices of the tube
(`FactoredNormalBoundOn`). Let `Y 0, …, Y N` be a run of the integrator with `κ ≥ 0`, step size
`0 ≤ h ≤ H`, `N h ≤ T`, and `‖Y 0 - A t₀‖ ≤ δ`. If the bound below is smaller than the tube
radius with a margin of `4 B h`, then for all `n ≤ N`

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (κ (10 L B h + ε) + (1 + κ) (c₁ ε + c₂ h))`,

`c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`. The constants do not depend on the singular values of the
`Y n`, and nothing is assumed about `F` outside the tube. The local error of each step comes
from `MatrixBUG.truncStepRel.hasLocalError_uniformGrid`. -/
theorem IsRun.norm_sub_le_of_truncStepRel {Y : ℕ → Matrix m n ℝ}
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hκ : 0 ≤ κ) (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) *
      (κ * (10 * L * B * h + ε) + (1 + κ) * (bugC₁ L H * ε + bugC₂ L B H * h)) + 4 * B * h < ρ)
    (hY : IsRun (truncStepRel F r κ) (uniformGrid t₀ h) N Y) (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) *
      (κ * (10 * L * B * h + ε) + (1 + κ) * (bugC₁ L H * ε + bugC₂ L B H * h)) := by
  have hc₀ := truncConst_nonneg_aux hκ hP.L_nonneg hP.B_nonneg (hh.trans hhH) hε₀ hh
  have hBh : 0 ≤ B * h := mul_nonneg hP.B_nonneg hh
  refine hY.norm_sub_le_of_tube_uniformGrid (T := T) (δ₀ := δ)
    (c := κ * (10 * L * B * h + ε) + (1 + κ) * (bugC₁ L H * ε + bugC₂ L B H * h)) hP hc
    (fun n hn Y₀ Y₁ hnear hstep => ?_) hc₀ hδ hNT (by linarith)
  -- the local error of a step that starts within the error bound of `A`
  exact hstep.hasLocalError_uniformGrid hκ hP hc hε hε₀ hh hhH hn (by linarith)

/-- **Existence and robust error bound for the augmented BUG integrator with truncation to a
fixed rank.** Let `A` solve `Y' = F(t, Y)` on `[t₀, t₀ + N h]`, and let `F` be `L`-Lipschitz and
bounded by `B` on the tube of radius `ρ` around `A` (`DLRAProblem`), jointly continuous there,
with normal component at most `ε` at the rank-`r` matrices of the tube
(`FactoredNormalBoundOn`). Let `r ≤ m`, `r ≤ n`, `κ ≥ 1`, let the step size satisfy `0 ≤ h ≤ H`
and `N h ≤ T`, and let `Y₀` be a start value of rank at most `r` with `‖Y₀ - A t₀‖ ≤ δ`. If

  `e^{L T} δ + T e^{L T} (κ (10 L B h + ε) + (1 + κ) (c₁ ε + c₂ h)) + 4 B h < ρ`,

`c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`, then the integrator can be run from `Y₀`: there are
`Y 0 = Y₀, Y 1, …, Y N`, each obtained from the previous one by an augmented BUG step of size
`h` followed by a truncation to rank `r` that is best up to the factor `κ`, all of rank at most
`r`, with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (κ (10 L B h + ε) + (1 + κ) (c₁ ε + c₂ h))`

for all `n ≤ N`. The constants are independent of the singular values of the matrices `Y n`, and
nothing is assumed about `F` outside the tube. No truncation tolerance appears.

This is `StepMethod.IsTubeLocal.exists_run_norm_sub_le` for the tube-local method
`MatrixBUG.isTubeLocal_truncStepRel`. The bound itself holds for every run
(`MatrixBUG.IsRun.norm_sub_le_of_truncStepRel`). The hypotheses on `F` and `A` are those of
`MatrixBUG.exists_run_norm_sub_le`. -/
theorem trunc_exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hκ : 1 ≤ κ) (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) *
      (κ * (10 * L * B * h + ε) + (1 + κ) * (bugC₁ L H * ε + bugC₂ L B H * h)) + 4 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (truncStepRel F r κ) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ +
        T * Real.exp (L * T) *
          (κ * (10 * L * B * h + ε) + (1 + κ) * (bugC₁ L H * ε + bugC₂ L B H * h)) := by
  have hκ₀ : 0 ≤ κ := zero_le_one.trans hκ
  have hc₀ := truncConst_nonneg_aux hκ₀ hP.L_nonneg hP.B_nonneg (hh.trans hhH) hε₀ hh
  refine (isTubeLocal_truncStepRel hκ hrm hrn).exists_run_norm_sub_le (by norm_num) hP hc
    (fun k hk Z₀ Z₁ _ hnear hstep => ?_) hc₀ hh hNT hY₀ hδ hsmall
  -- the local error of a step that starts within the error bound of `A`
  exact truncStepRel.hasLocalError_uniformGrid hstep hκ₀ hP hc hε hε₀ hh hhH hk (by linarith)

end Error

/-! ### Examples: a nonlinear field, a linear field, a truncation with an error -/

section Examples

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}

/-- **Non-vacuity of the existence and error theorem.** The radial field
`F(t, Y) = Y / max ‖Y‖ 1` is `2`-Lipschitz, bounded by `1`, and has no normal component at any
matrix (`MatrixKSL.radial_normal_eq_zero`), so `ε = 0`. For every solution `A` of `Y' = F(t, Y)`
on `[t₀, t₀ + N h]`, of any rank (the zero function is one), every `κ ≥ 1` and every start value
`Y₀` of rank at most `r` with `‖Y₀ - A t₀‖ ≤ δ`, the augmented BUG integrator with truncation to
rank `r` can be run with any step size `0 ≤ h ≤ H`, and the run stays within
`e^{2 T} δ + T e^{2 T} (20 κ + (1 + κ) bugC₂ 2 1 H) h` of `A`. No smallness condition remains,
because the field is Lipschitz and bounded everywhere and the tube radius can be chosen as large
as needed. -/
example {κ : ℝ} (hκ : 1 ≤ κ) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {A : ℝ → Matrix m n ℝ} {t₀ h H T δ : ℝ} {N : ℕ}
    (hA : ODESolution (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) A t₀ (t₀ + N * h))
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r)
    (hδ : ‖Y₀ - A t₀‖ ≤ δ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (truncStepRel (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) r κ)
        (uniformGrid t₀ h) N Y ∧
      ∀ j ≤ N, (Y j).rank ≤ r ∧ ‖Y j - A (t₀ + j * h)‖ ≤
        Real.exp (2 * T) * δ + T * Real.exp (2 * T) *
          (κ * (10 * 2 * 1 * h + 0) + (1 + κ) * (bugC₁ 2 H * 0 + bugC₂ 2 1 H * h)) := by
  have hcont : Continuous fun Z : Matrix m n ℝ => MatrixKSL.radial Z :=
    (LipschitzWith.of_dist_le' (K := 2) fun X Y => by
      rw [dist_eq_norm, dist_eq_norm]; exact MatrixKSL.norm_radial_sub_le X Y).continuous
  exact trunc_exists_run_norm_sub_le
    (F := fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) (A := A) (L := 2) (B := 1)
    (ε := 0)
    (ρ := Real.exp (2 * T) * δ + T * Real.exp (2 * T) *
      (κ * (10 * 2 * 1 * h + 0) + (1 + κ) * (bugC₁ 2 H * 0 + bugC₂ 2 1 H * h)) + 4 * 1 * h + 1)
    ⟨hA, by norm_num, by norm_num, fun _ _ X Y _ _ => MatrixKSL.norm_radial_sub_le X Y,
      fun _ _ X _ => MatrixKSL.norm_radial_le X⟩
    (hcont.comp continuous_snd).continuousOn
    (fun t U V S hU hV _ => MatrixKSL.radial_normal_eq_zero t U S V hU hV) le_rfl hκ hh hhH hNT
    hrm hrn hY₀ hδ (lt_add_one _)

/-- **Non-vacuity for a field that is not bounded.** The linear field
`F(t, Y) = M Y + Y Nᵀ + G` with a stationary point `C` (`M C + C Nᵀ + G = 0`) is Lipschitz with
constant `‖M‖ + ‖N‖` but not bounded. On the tube of radius `ρ` around the constant solution
`A(t) = C` it is bounded by `(‖M‖ + ‖N‖) ρ`, and its normal component at the rank-`r` matrices
is at most `‖G‖` (`dlraProblem_linear`, `factoredNormalBoundOn_linear`). Hence, under the
smallness condition, the augmented BUG integrator with truncation to rank `r` can be run from
every `Y₀` of rank at most `r` near `C`, and the run satisfies the error bound with `ε = ‖G‖`.
The corresponding example for the BUG integrator whose bases keep `r` columns treats the same
problem. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) {κ : ℝ} (hκ : 1 ≤ κ) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) (t₀ : ℝ) {ρ T H δ h : ℝ} {K : ℕ} (hρ : 0 ≤ ρ) (hh : 0 ≤ h)
    (hhH : h ≤ H) (hKT : K * h ≤ T) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r)
    (hδ : ‖Y₀ - C‖ ≤ δ)
    (hsmall : Real.exp ((‖M‖ + ‖N‖) * T) * δ + T * Real.exp ((‖M‖ + ‖N‖) * T) *
      (κ * (10 * (‖M‖ + ‖N‖) * ((‖M‖ + ‖N‖) * ρ) * h + ‖G‖) +
        (1 + κ) * (bugC₁ (‖M‖ + ‖N‖) H * ‖G‖ + bugC₂ (‖M‖ + ‖N‖) ((‖M‖ + ‖N‖) * ρ) H * h))
      + 4 * ((‖M‖ + ‖N‖) * ρ) * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (truncStepRel (fun (_ : ℝ) (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G) r κ)
        (uniformGrid t₀ h) K Y ∧
      ∀ j ≤ K, (Y j).rank ≤ r ∧ ‖Y j - C‖ ≤ Real.exp ((‖M‖ + ‖N‖) * T) * δ +
        T * Real.exp ((‖M‖ + ‖N‖) * T) *
          (κ * (10 * (‖M‖ + ‖N‖) * ((‖M‖ + ‖N‖) * ρ) * h + ‖G‖) +
            (1 + κ) * (bugC₁ (‖M‖ + ‖N‖) H * ‖G‖ +
              bugC₂ (‖M‖ + ‖N‖) ((‖M‖ + ‖N‖) * ρ) H * h)) :=
  trunc_exists_run_norm_sub_le (A := fun _ => C) (dlraProblem_linear M N G C hC _ _ hρ)
    (continuous_uncurry_linear M N G).continuousOn
    (factoredNormalBoundOn_linear M N G _) (norm_nonneg G) hκ hh hhH hKT hrm hrn hY₀ hδ hsmall

omit [DecidableEq m] [DecidableEq n] in
/-- A step of `MatrixBUG.truncStepRel` followed by a perturbation of size at most `ϑ` that keeps
the rank at most `r` is tube-local with the same admissible values and the same margin constant:
the three properties are those of `MatrixBUG.isTubeLocal_truncStepRel`. -/
private theorem isTubeLocal_truncStepRel_perturbed_aux {κ ϑ : ℝ} (hκ : 1 ≤ κ) (hϑ : 0 ≤ ϑ)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) :
    StepMethod.IsTubeLocal
      (fun (G : ℝ → Matrix m n ℝ → Matrix m n ℝ) s₀ s₁ Z₀ Z₁ =>
        ∃ Zh, truncStepRel G r κ s₀ s₁ Z₀ Zh ∧ Z₁.rank ≤ r ∧ ‖Z₁ - Zh‖ ≤ ϑ)
      (fun Y => Y.rank ≤ r) 4 where
  exists_step := fun hG hc h01 hY₀ => by
    obtain ⟨Zh, hZh⟩ := exists_truncStepRel hG hc h01 hκ hrm hrn hY₀
    exact ⟨Zh, Zh, hZh, hZh.rank_le, by simpa using hϑ⟩
  adm_of_step := fun _ _ ⟨_, _, hrank, _⟩ => hrank
  step_of_tubeExt := fun hFB hB ha hb h01 hA _ hsmall hstep => by
    obtain ⟨Zh, hZh, hrank, hd⟩ := hstep
    exact ⟨Zh, (truncStepRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 hZh, hrank, hd⟩

/-- **A truncation that is computed only up to an error.** Let the truncation to rank `r` of
every step be followed by a perturbation of size at most `ϑ` that keeps the rank at most `r`
(a truncated singular value decomposition computed by an iteration, say). For the radial field
`F(t, Y) = Y / max ‖Y‖ 1`, every solution `A`, every start value of rank at most `r` within `δ`
of `A t₀`, every step size `0 ≤ h ≤ H`, every `κ ≥ 1` and every `ϑ ≥ 0` there is a run of this
perturbed integrator, and it stays within
`e^{2 T} (δ + j ϑ) + T e^{2 T} (20 κ + (1 + κ) bugC₂ 2 1 H) h` of `A` after `j` steps. The local
error of a perturbed step is the one of `MatrixBUG.truncStepRel.hasLocalError_uniformGrid` plus
`ϑ` (`HasLocalError.add_of_norm_sub_le`), and the run theorem with a tolerance
`StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_tol` sums the perturbations. -/
example {κ ϑ : ℝ} (hκ : 1 ≤ κ) (hϑ : 0 ≤ ϑ) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) {A : ℝ → Matrix m n ℝ} {t₀ h H T δ : ℝ} {N : ℕ}
    (hA : ODESolution (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) A t₀ (t₀ + N * h))
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r)
    (hδ : ‖Y₀ - A t₀‖ ≤ δ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (fun s₀ s₁ Z₀ Z₁ => ∃ Zh,
        truncStepRel (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) r κ s₀ s₁ Z₀ Zh ∧
          Z₁.rank ≤ r ∧ ‖Z₁ - Zh‖ ≤ ϑ) (uniformGrid t₀ h) N Y ∧
      ∀ j ≤ N, (Y j).rank ≤ r ∧ ‖Y j - A (t₀ + j * h)‖ ≤
        Real.exp (2 * T) * (δ + j * ϑ) + T * Real.exp (2 * T) *
          (κ * (10 * 2 * 1 * h + 0) + (1 + κ) * (bugC₁ 2 H * 0 + bugC₂ 2 1 H * h)) := by
  have hκ₀ : 0 ≤ κ := zero_le_one.trans hκ
  have hcont : Continuous fun Z : Matrix m n ℝ => MatrixKSL.radial Z :=
    (LipschitzWith.of_dist_le' (K := 2) fun X Y => by
      rw [dist_eq_norm, dist_eq_norm]; exact MatrixKSL.norm_radial_sub_le X Y).continuous
  have hc₀ : 0 ≤ κ * (10 * 2 * 1 * h + 0) + (1 + κ) * (bugC₁ 2 H * 0 + bugC₂ 2 1 H * h) :=
    truncConst_nonneg_aux hκ₀ (by norm_num) (by norm_num) (hh.trans hhH) le_rfl hh
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = Real.exp (2 * T) * (δ + N * ϑ) + T * Real.exp (2 * T) *
      (κ * (10 * 2 * 1 * h + 0) + (1 + κ) * (bugC₁ 2 H * 0 + bugC₂ 2 1 H * h)) + 4 * 1 * h + 1 :=
    ⟨_, rfl⟩
  have hP : DLRAProblem (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) A t₀
      (t₀ + N * h) ρ 2 1 :=
    ⟨hA, by norm_num, by norm_num, fun _ _ X Y _ _ => MatrixKSL.norm_radial_sub_le X Y,
      fun _ _ X _ => MatrixKSL.norm_radial_le X⟩
  have hc : ContinuousOn
      (Function.uncurry fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z)
      (tubeSet A t₀ (t₀ + N * h) ρ) := (hcont.comp continuous_snd).continuousOn
  have hε : FactoredNormalBoundOn (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) r
      (tubeSet A t₀ (t₀ + N * h) ρ) 0 :=
    fun t U V S hU hV _ => MatrixKSL.radial_normal_eq_zero t U S V hU hV
  refine (isTubeLocal_truncStepRel_perturbed_aux hκ hϑ hrm hrn).exists_run_norm_sub_le_of_tol
    (by norm_num) hP hc
    (c := κ * (10 * 2 * 1 * h + 0) + (1 + κ) * (bugC₁ 2 H * 0 + bugC₂ 2 1 H * h)) (T := T)
    (δ := δ) (ϑ := ϑ) (fun k hk Z₀ Z₁ _ hnear hstep => ?_) hc₀ hϑ hh hNT hY₀ hδ
    (by rw [hρ]; exact lt_add_one _)
  -- the local error of a perturbed step that starts within the error bound of `A`
  obtain ⟨Zh, hZh, -, hd⟩ := hstep
  have hloc := hZh.hasLocalError_uniformGrid hκ₀ hP hc hε le_rfl hh hhH hk (by linarith)
  exact hloc.add_of_norm_sub_le hd

end Examples

end MatrixBUG

end LeanDLRA
