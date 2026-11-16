import LeanDLRA.Integrators.Matrix.AdaptiveBUGStep

/-!
# Runs of the rank-adaptive BUG integrator with truncation by a tolerance

This file closes the theory of the rank-adaptive basis-update & Galerkin (BUG) integrator of
Ceruti, Kusch and Lubich (arXiv:2104.05247) for a matrix differential equation `Y' = F(t, Y)`:
the integrator can be run, and every run stays close to the exact solution. Every step augments
the bases, takes a Galerkin step in the augmented bases and truncates the result to a tolerance
`ϑ`; the rank of the values is not fixed. The step relation `MatrixBUG.adaptiveStepRel` and its
local error are in `LeanDLRA/Integrators/Matrix/AdaptiveBUGStep.lean`.

**Setting.** Let `A` be a solution of `Y' = F(t, Y)` on `[t₀, t₀ + N h]`. The field `F` is only
assumed to be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around `A`
(`DLRAProblem F A t₀ (t₀ + N h) ρ L B`), jointly continuous there, and to have a small normal
component at the factored matrices in the tube with `r` columns, for every `r ≥ r₀`
(`FactoredNormalBoundOn F r _ ε`, one `ε` for all `r`): for every `Y = U S Vᵀ` with orthonormal
`U`, `V` the part `(I - U Uᵀ) F(t, Y) (I - V Vᵀ)` of the field that points away from both the
column and the row space of `Y` has norm at most `ε`. Nothing is assumed about `F` outside the
tube. The number `r₀` is a lower bound for the number of columns from which a step starts; a
factorization of a matrix of smaller rank is padded with orthonormal columns.

**Result** (`MatrixBUG.adaptive_exists_run_norm_sub_le`). For every start value `Y₀` with
`‖Y₀ - A t₀‖ ≤ δ` there are matrices `Y 0 = Y₀, Y 1, …, Y N`, each obtained from the previous one
by a step of size `h ≤ H` of the rank-adaptive integrator with tolerance `ϑ`
(`IsRun (MatrixBUG.adaptiveStepRel F (Set.Ici r₀) ϑ) (uniformGrid t₀ h) N Y`), with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (c₁ ε + c₂ h) + e^{L T} n ϑ`

for all `n ≤ N`, where `N h ≤ T`, `c₁ = bugC₁ L H` and `c₂ = bugC₂ L B H`; the terms without
`ϑ` are `bugGlobalBound L B H T δ ε h`, the bound of the BUG integrator whose bases keep their
number of columns. The constants do not depend on the singular values of the matrices `Y n`. The
only further hypothesis is that the bound with `N` in place of `n`, plus `4 B h`, is less than
`ρ`. This is the form of `MatrixBUG.rankAdaptive_global_error_le`, which assumes the field to be
Lipschitz and bounded everywhere and the exact solutions through the `Y n` to be given.

Every run satisfies a bound of the same kind (`MatrixBUG.IsRun.norm_sub_le_of_adaptiveStepRel`),
with `T e^{L T} ϑ / h` in place of `e^{L T} n ϑ`, for `h > 0` and every set `R` of numbers of
columns. The relation contains every truncation within the tolerance, in particular the
truncated singular value decomposition, so this bound holds for the run that an implementation
computes; the existence statement is weak by comparison (the augmented matrix itself is a
truncation within every tolerance `ϑ ≥ 0`).

## Main results

* `MatrixBUG.adaptive_exists_run`: for a field that is Lipschitz everywhere there is a run on
  every grid from every start value.
* `MatrixBUG.isTubeLocal_adaptiveStepRel_Ici`: for `R = Set.Ici r₀` with `r₀ ≤ m`, `r₀ ≤ n`
  the integrator is a tube-local method (`StepMethod.IsTubeLocal`) with every matrix admissible
  and margin constant `4`.
* `MatrixBUG.adaptiveStepRel.hasLocalError_uniformGrid`: the local error `h (c₁ ε + c₂ h) + ϑ`
  of one step of a uniform grid, from the hypotheses of the run theorem.
* `MatrixBUG.IsRun.norm_sub_le_of_adaptiveStepRel`: every run satisfies the error bound with the
  term `T e^{L T} ϑ / h`.
* `MatrixBUG.adaptive_exists_run_norm_sub_le`: a run exists and satisfies the error bound with
  the term `e^{L T} n ϑ`.

The examples at the end apply the result to the field `F(t, Y) = Y / max ‖Y‖ 1`, which has no
normal component, so that `ε = 0`, and to the linear field `F(t, Y) = M Y + Y Nᵀ + G`, which is
not bounded and has `ε = ‖G‖`.

## Implementation notes

The local error of a step is `h c + ϑ` with `c = c₁ ε + c₂ h`: the tolerance is not multiplied
by the step size. `MatrixBUG.adaptive_exists_run_norm_sub_le` is therefore an instance of the
run theorem with a tolerance per step, `StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_tol`,
and not of `StepMethod.IsTubeLocal.exists_run_norm_sub_le`. The bound for every run is the run
theorem for given runs, `IsRun.norm_sub_le_of_tube_uniformGrid`, with the local error written as
`h (c + ϑ / h)`.

The margin constant `4` is that of the BUG step; the truncation does not evaluate the field.
Every matrix is admissible because a step may start from a factorization with any number
`r ≥ r₀` of columns, `r ≤ m`, `r ≤ n` (`MatrixBUG.exists_adaptiveStepRel_Ici`); no state other
than the matrix `Y n` is needed, in particular no rank that changes from step to step.

## References

* G. Ceruti, J. Kusch, Ch. Lubich, *A rank-adaptive robust integrator for dynamical low-rank
  approximation*, arXiv:2104.05247 (BIT Numer. Math. 2022).
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixBUG

/-! ### Existence of runs, and the integrator as a tube-local method -/

section Exists

variable {m n : Type*} [Fintype m] [Fintype n] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L ϑ : ℝ}
  {r₀ : ℕ}

/-- **Runs of the rank-adaptive BUG integrator exist.** If `F` is Lipschitz (globally) and
continuous in time on `[τ 0, τ N]`, `r₀ ≤ m`, `r₀ ≤ n` and `ϑ ≥ 0`, then on the grid `τ` there
is a run of `N` steps with tolerance `ϑ` from every start value `Y₀`, every step starting from a
factorization with at least `r₀` columns. No bound on the field is needed. For fields that are
Lipschitz only near a solution see `MatrixBUG.adaptive_exists_run_norm_sub_le`. -/
theorem adaptive_exists_run (hF : IsLipschitzField F L) {τ : ℕ → ℝ} {N : ℕ} (hτ : IsGrid τ N)
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc (τ 0) (τ N))) (hϑ : 0 ≤ ϑ)
    (hrm : r₀ ≤ Fintype.card m) (hrn : r₀ ≤ Fintype.card n) (Y₀ : Matrix m n ℝ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (adaptiveStepRel F (Set.Ici r₀) ϑ) τ N Y := by
  refine exists_isRun hτ Y₀ fun n hn Y _ _ => ?_
  have hsub : Icc (τ n) (τ (n + 1)) ⊆ Icc (τ 0) (τ N) :=
    Icc_subset_Icc (hτ.le_of_le n.zero_le hn.le) (hτ.le_of_le (Nat.succ_le_of_lt hn) le_rfl)
  exact exists_adaptiveStepRel_Ici hF (fun Z => (hc Z).mono hsub) (hτ.mono n hn) hϑ hrm hrn (Y n)

/-- **The rank-adaptive BUG integrator is a tube-local method** (`StepMethod.IsTubeLocal`) for
`R = Set.Ici r₀`, with every matrix admissible and margin constant `4`, for every tolerance
`ϑ ≥ 0`:

* a step exists from every matrix, for every globally Lipschitz field that is continuous in time
  on the step interval (`MatrixBUG.exists_adaptiveStepRel_Ici`): a factorization of the start
  value is padded to `max (rank Y₀) r₀` columns. This is where `r₀ ≤ m` and `r₀ ≤ n` are used;
  for a larger `r₀` no factorization with `r₀` orthonormal columns exists and the relation is
  empty (`MatrixBUG.augmentedRel.le_card_left`, `MatrixBUG.augmentedRel.le_card_right`);
* the admissible set is that of all matrices, so it is kept by every step;
* if `‖Y₀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, a step from `Y₀` of the extended field
  `tubeExt F A a b ρ` is a step of `F` (`MatrixBUG.adaptiveStepRel_tubeExt_iff_of_near`).

With the local error `MatrixBUG.adaptiveStepRel.hasLocalError_of_tube` this is all that
`StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_tol` needs. -/
theorem isTubeLocal_adaptiveStepRel_Ici (hϑ : 0 ≤ ϑ) (hrm : r₀ ≤ Fintype.card m)
    (hrn : r₀ ≤ Fintype.card n) :
    StepMethod.IsTubeLocal
      (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => adaptiveStepRel G (Set.Ici r₀) ϑ)
      (fun _ => True) 4 where
  exists_step := fun hG hc h01 _ => exists_adaptiveStepRel_Ici hG hc h01 hϑ hrm hrn _
  adm_of_step := fun _ _ _ => trivial
  step_of_tubeExt := fun hFB hB ha hb h01 hA _ hsmall hstep =>
    (adaptiveStepRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 hstep

end Exists

/-! ### The error bound, and existence of a run near the exact solution -/

section Error

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r₀ : ℕ}
  {R : Set ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ}
  {t₀ h H T ρ L B ε δ ϑ : ℝ} {N : ℕ}

/-- **Local error of one step of a uniform grid.** Under the hypotheses of the run theorem on
`F` and `A` (`DLRAProblem`, and `FactoredNormalBoundOn` at every number of columns in `R` on the
tube of radius `ρ` around `A` over `[t₀, t₀ + N h]`), a step of the rank-adaptive BUG integrator
with tolerance `ϑ` over `[t₀ + k h, t₀ + (k + 1) h]`, `k < N`, `h ≤ H`, whose start value `Z₀`
satisfies `‖Z₀ - A (t₀ + k h)‖ + 4 B h < ρ` has local error `h (c₁ ε + c₂ h) + ϑ` with
`c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`. -/
theorem adaptiveStepRel.hasLocalError_uniformGrid {k : ℕ} {Z₀ Z₁ : Matrix m n ℝ}
    (hstep : adaptiveStepRel F R ϑ (t₀ + k * h) (t₀ + (k + 1) * h) Z₀ Z₁)
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hε : ∀ r ∈ R, FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hk : k < N)
    (hnear : ‖Z₀ - A (t₀ + k * h)‖ + 4 * B * h < ρ) :
    HasLocalError F (t₀ + k * h) (t₀ + (k + 1) * h) Z₀ Z₁
      (h * (bugC₁ L H * ε + bugC₂ L B H * h) + ϑ) := by
  obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hk
  have hloc := hstep.hasLocalError_of_tube hε hP.lipschitz hP.L_nonneg hP.bounded hP.B_nonneg
    ha hb h01 (hsub.le.trans hhH) (hP.sol.mono ha hb) (by rw [hsub]; exact hnear)
  rwa [hsub] at hloc

/-- **Every run of the rank-adaptive BUG integrator satisfies the robust error bound.** Let `A`
solve `Y' = F(t, Y)` on `[t₀, t₀ + N h]`, and let `F` be `L`-Lipschitz and bounded by `B` on the
tube of radius `ρ` around `A` (`DLRAProblem`), jointly continuous there, with normal component at
most `ε` at the factored matrices of the tube with `r` columns, for every `r` in the set `R` of
numbers of columns that a step may start from (`FactoredNormalBoundOn`). Let `Y 0, …, Y N` be a
run of the integrator with tolerance `ϑ`, step size `0 < h ≤ H`, `N h ≤ T`, and
`‖Y 0 - A t₀‖ ≤ δ`. If the bound below is smaller than the tube radius with a margin of `4 B h`,
then for all `n ≤ N`

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (c₁ ε + c₂ h) + T e^{L T} ϑ / h`,

`c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`. This is the form `C₀ δ + C₁ h + C₂ ε + C₃ ϑ / h` of the
error bounds of rank-adaptive integrators in the literature (for the parallel integrator
`MatrixParallelBUG.global_error_paper`). The constants do not depend on the singular values of
the `Y n`, and nothing is assumed about `F` outside the tube. The relation contains every
truncation within the tolerance, so the bound holds for the truncated singular value
decomposition. -/
theorem IsRun.norm_sub_le_of_adaptiveStepRel {Y : ℕ → Matrix m n ℝ}
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : ∀ r ∈ R, FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hϑ : 0 ≤ ϑ) (hh : 0 < h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hsmall : bugGlobalBound L B H T δ ε h + T * Real.exp (L * T) * (ϑ / h) + 4 * B * h < ρ)
    (hY : IsRun (adaptiveStepRel F R ϑ) (uniformGrid t₀ h) N Y) (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
      bugGlobalBound L B H T δ ε h + T * Real.exp (L * T) * (ϑ / h) := by
  have hc₀ : 0 ≤ bugC₁ L H * ε + bugC₂ L B H * h + ϑ / h :=
    add_nonneg (add_nonneg (mul_nonneg (bugC₁_nonneg hP.L_nonneg (hh.le.trans hhH)) hε₀)
      (mul_nonneg (bugC₂_nonneg hP.L_nonneg hP.B_nonneg (hh.le.trans hhH)) hh.le))
      (div_nonneg hϑ hh.le)
  have hBh : 0 ≤ B * h := mul_nonneg hP.B_nonneg hh.le
  have e : bugGlobalBound L B H T δ ε h + T * Real.exp (L * T) * (ϑ / h) =
      Real.exp (L * T) * δ +
        T * Real.exp (L * T) * (bugC₁ L H * ε + bugC₂ L B H * h + ϑ / h) := by
    rw [bugGlobalBound_eq]
    ring
  rw [e] at hsmall ⊢
  refine hY.norm_sub_le_of_tube_uniformGrid (T := T) (δ₀ := δ)
    (c := bugC₁ L H * ε + bugC₂ L B H * h + ϑ / h) hP hc
    (fun k hk Z₀ Z₁ hnear hstep => ?_) hc₀ hδ hNT (by linarith)
  -- the local error of a step that starts within the error bound of `A`
  have hloc := hstep.hasLocalError_uniformGrid hP hε hh.le hhH hk (by linarith)
  have e' : h * (bugC₁ L H * ε + bugC₂ L B H * h + ϑ / h) =
      h * (bugC₁ L H * ε + bugC₂ L B H * h) + ϑ := by
    rw [mul_add, mul_div_cancel₀ ϑ hh.ne']
  rwa [e']

/-- **Existence and robust error bound for the rank-adaptive BUG integrator.** Let `A` solve
`Y' = F(t, Y)` on `[t₀, t₀ + N h]`, and let `F` be `L`-Lipschitz and bounded by `B` on the tube
of radius `ρ` around `A` (`DLRAProblem`), jointly continuous there, with normal component at
most `ε` at the factored matrices of the tube with `r` columns, for every `r ≥ r₀`
(`FactoredNormalBoundOn`). Let `r₀ ≤ m`, `r₀ ≤ n`, `ϑ ≥ 0`, let the step size satisfy
`0 ≤ h ≤ H` and `N h ≤ T`, and let `Y₀` be a start value with `‖Y₀ - A t₀‖ ≤ δ`. If

  `e^{L T} δ + T e^{L T} (c₁ ε + c₂ h) + e^{L T} N ϑ + 4 B h < ρ`,

`c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`, then the integrator can be run from `Y₀`: there are
`Y 0 = Y₀, Y 1, …, Y N`, each obtained from the previous one by a step of size `h` from a
factorization with at least `r₀` columns, followed by a truncation to the tolerance `ϑ`, with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (c₁ ε + c₂ h) + e^{L T} n ϑ`

for all `n ≤ N` (arXiv:2104.05247, Theorem 2, for a field that is Lipschitz and bounded near the
exact solution only). The terms without `ϑ` are `bugGlobalBound L B H T δ ε h`. The constants are
independent of the singular values of the matrices `Y n`, and nothing is assumed about `F`
outside the tube.

This is `StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_tol` for the tube-local method
`MatrixBUG.isTubeLocal_adaptiveStepRel_Ici`. The hypotheses on `F` and `A` are those of
`MatrixBUG.exists_run_norm_sub_le`, with the normal bound at every `r ≥ r₀`. For a bound that
holds for every run see `MatrixBUG.IsRun.norm_sub_le_of_adaptiveStepRel`. -/
theorem adaptive_exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : ∀ r ∈ Set.Ici r₀, FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε)
    (hε₀ : 0 ≤ ε) (hϑ : 0 ≤ ϑ) (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hrm : r₀ ≤ Fintype.card m) (hrn : r₀ ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : bugGlobalBound L B H T δ ε h + Real.exp (L * T) * (N * ϑ) + 4 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (adaptiveStepRel F (Set.Ici r₀) ϑ) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
        bugGlobalBound L B H T δ ε h + Real.exp (L * T) * (n * ϑ) := by
  have hH : 0 ≤ H := hh.trans hhH
  have hc₀ : 0 ≤ bugC₁ L H * ε + bugC₂ L B H * h :=
    add_nonneg (mul_nonneg (bugC₁_nonneg hP.L_nonneg hH) hε₀)
      (mul_nonneg (bugC₂_nonneg hP.L_nonneg hP.B_nonneg hH) hh)
  have hBh : 0 ≤ B * h := mul_nonneg hP.B_nonneg hh
  have e : ∀ k : ℝ, bugGlobalBound L B H T δ ε h + Real.exp (L * T) * (k * ϑ) =
      Real.exp (L * T) * (δ + k * ϑ) + T * Real.exp (L * T) *
        (bugC₁ L H * ε + bugC₂ L B H * h) := fun k => by
    rw [bugGlobalBound_eq]
    ring
  rw [e] at hsmall
  obtain ⟨Y, hY0, hY, hbd⟩ :=
    (isTubeLocal_adaptiveStepRel_Ici hϑ hrm hrn).exists_run_norm_sub_le_of_tol (by norm_num) hP
      hc (c := bugC₁ L H * ε + bugC₂ L B H * h) (T := T) (δ := δ) (ϑ := ϑ)
    (fun k hk Z₀ Z₁ _ hnear hstep =>
      -- the local error of a step that starts within the error bound of `A`
      hstep.hasLocalError_uniformGrid hP hε hh hhH hk (by linarith))
    hc₀ hϑ hh hNT trivial hδ hsmall
  exact ⟨Y, hY0, hY, fun n hn => by rw [e]; exact (hbd n hn).2⟩

end Error

/-! ### Examples: a nonlinear field and a linear field -/

section Examples

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r₀ : ℕ}

/-- **Non-vacuity of the existence and error theorem.** The radial field
`F(t, Y) = Y / max ‖Y‖ 1` is `2`-Lipschitz, bounded by `1`, and has no normal component at any
factored matrix, whatever the number of columns (`MatrixKSL.radial_normal_eq_zero`), so `ε = 0`
for every `r ≥ r₀`. For every solution `A` of `Y' = F(t, Y)` on `[t₀, t₀ + N h]`, every
tolerance `ϑ ≥ 0` and every start value `Y₀`, of any rank, with `‖Y₀ - A t₀‖ ≤ δ`, the
rank-adaptive BUG integrator can be run with any step size `0 ≤ h ≤ H`, and the run stays within
`e^{2 T} δ + T e^{2 T} bugC₂ 2 1 H h + e^{2 T} j ϑ` of `A` after `j` steps. No smallness condition
remains, because the field is Lipschitz and bounded everywhere and the tube radius can be chosen
as large as needed. -/
example {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (hrm : r₀ ≤ Fintype.card m) (hrn : r₀ ≤ Fintype.card n)
    {A : ℝ → Matrix m n ℝ} {t₀ h H T δ : ℝ} {N : ℕ}
    (hA : ODESolution (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) A t₀ (t₀ + N * h))
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T) {Y₀ : Matrix m n ℝ}
    (hδ : ‖Y₀ - A t₀‖ ≤ δ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (adaptiveStepRel (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z)
        (Set.Ici r₀) ϑ) (uniformGrid t₀ h) N Y ∧
      ∀ j ≤ N, ‖Y j - A (t₀ + j * h)‖ ≤
        bugGlobalBound 2 1 H T δ 0 h + Real.exp (2 * T) * (j * ϑ) := by
  have hcont : Continuous fun Z : Matrix m n ℝ => MatrixKSL.radial Z :=
    (LipschitzWith.of_dist_le' (K := 2) fun X Y => by
      rw [dist_eq_norm, dist_eq_norm]; exact MatrixKSL.norm_radial_sub_le X Y).continuous
  exact adaptive_exists_run_norm_sub_le
    (F := fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) (A := A) (L := 2) (B := 1)
    (ε := 0)
    (ρ := bugGlobalBound 2 1 H T δ 0 h + Real.exp (2 * T) * (N * ϑ) + 4 * 1 * h + 1)
    ⟨hA, by norm_num, by norm_num, fun _ _ X Y _ _ => MatrixKSL.norm_radial_sub_le X Y,
      fun _ _ X _ => MatrixKSL.norm_radial_le X⟩
    (hcont.comp continuous_snd).continuousOn
    (fun _ _ t U V S hU hV _ => MatrixKSL.radial_normal_eq_zero t U S V hU hV) le_rfl hϑ hh hhH
    hNT hrm hrn hδ (lt_add_one _)

/-- **Non-vacuity for a field that is not bounded, and for every run.** The linear field
`F(t, Y) = M Y + Y Nᵀ + G` with a stationary point `C` (`M C + C Nᵀ + G = 0`) is Lipschitz with
constant `‖M‖ + ‖N‖` but not bounded. On the tube of radius `ρ` around the constant solution
`A(t) = C` it is bounded by `(‖M‖ + ‖N‖) ρ`, and its normal component at the factored matrices
is at most `‖G‖` for every number of columns (`dlraProblem_linear`,
`factoredNormalBoundOn_linear`); `‖G‖` is smaller than the bound of the field as soon as
`‖G‖ < (‖M‖ + ‖N‖) ρ`. Hence, under the smallness condition, a run of the rank-adaptive BUG
integrator with tolerance `ϑ` exists from every `Y₀` near `C`, and every run from such a `Y₀`,
with any set of numbers of columns, satisfies the error bound with `ε = ‖G‖` and the term
`T e^{L T} ϑ / h`. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) {R : Set ℕ} {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (hrm : r₀ ≤ Fintype.card m)
    (hrn : r₀ ≤ Fintype.card n) (t₀ : ℝ) {ρ T H δ h : ℝ} {K : ℕ} (hρ : 0 ≤ ρ) (hh : 0 < h)
    (hhH : h ≤ H) (hKT : K * h ≤ T) {Y₀ : Matrix m n ℝ} (hδ : ‖Y₀ - C‖ ≤ δ)
    (hsmall : bugGlobalBound (‖M‖ + ‖N‖) ((‖M‖ + ‖N‖) * ρ) H T δ ‖G‖ h +
      T * Real.exp ((‖M‖ + ‖N‖) * T) * (ϑ / h) + 4 * ((‖M‖ + ‖N‖) * ρ) * h < ρ) :
    (∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (adaptiveStepRel (fun (_ : ℝ) (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G)
        (Set.Ici r₀) ϑ) (uniformGrid t₀ h) K Y) ∧
    ∀ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ →
      IsRun (adaptiveStepRel (fun (_ : ℝ) (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G) R ϑ)
        (uniformGrid t₀ h) K Y →
      ∀ j ≤ K, ‖Y j - C‖ ≤ bugGlobalBound (‖M‖ + ‖N‖) ((‖M‖ + ‖N‖) * ρ) H T δ ‖G‖ h +
        T * Real.exp ((‖M‖ + ‖N‖) * T) * (ϑ / h) := by
  refine ⟨adaptive_exists_run (isLipschitzField_linear M N G) (isGrid_uniformGrid hh.le K)
    (fun _ => continuousOn_const) hϑ hrm hrn Y₀, fun Y hY0 hY => ?_⟩
  exact IsRun.norm_sub_le_of_adaptiveStepRel (A := fun _ => C)
    (dlraProblem_linear M N G C hC _ _ hρ) (continuous_uncurry_linear M N G).continuousOn
    (fun r _ => factoredNormalBoundOn_linear M N G _) (norm_nonneg G) hϑ hh hhH hKT hsmall hY
    (by rw [hY0]; exact hδ)

end Examples

end MatrixBUG

end LeanDLRA
