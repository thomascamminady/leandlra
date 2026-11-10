import LeanDLRA.Integrators.Matrix.EulerBUGStep

/-!
# Runs of the fixed-rank explicit Euler BUG integrator: existence and error bound

This file closes the theory of the basis-update & Galerkin (BUG) integrator with explicit Euler
substeps and a fixed rank for a matrix differential equation `Y' = F(t, Y)` (Nobile and Riffaud,
arXiv:2502.07040, §2.1, Algorithm 1): it shows that the integrator can be run, and that every
run stays close to the exact solution. The step relation and its local error are in
`LeanDLRA/Integrators/Matrix/EulerBUGStep.lean`. The error analysis at the level of orthogonal
projectors, on which the local error rests, is in `LeanDLRA/Integrators/EulerBUG.lean`. This
file is the place to start reading about the integrator for matrices.

**Setting.** Let `A` be a solution of `Y' = F(t, Y)` on `[t₀, t₀ + N h]`. The field `F` is only
assumed to be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around `A`
(`DLRAProblem F A t₀ (t₀ + N h) ρ L B`), jointly continuous there, and to have a small normal
component at the rank-`r` matrices in the tube (`FactoredNormalBoundOn F r _ ε`): for every
`Y = U S Vᵀ` with orthonormal `U`, `V` the part `(I - U Uᵀ) F(t, Y) (I - V Vᵀ)` of the field that
points away from both the column and the row space of `Y` has norm at most `ε`. Because the
substeps are explicit Euler steps, the field also has to be Lipschitz in time on the tube:
`‖F(t, X) - F(s, X)‖ ≤ Lₜ (t - s)` for `s ≤ t` and every `X` that lies in the tube at both
times. For a field that does not depend on time, `Lₜ = 0`. Nothing is assumed about `F` outside
the tube.

**Result** (`MatrixEulerBUG.exists_run_norm_sub_le`). For every start value `Y₀` of rank at most
`r` with `‖Y₀ - A t₀‖ ≤ δ` there are matrices `Y 0 = Y₀, Y 1, …, Y N`, each obtained from the
previous one by an explicit Euler BUG step of size `h` followed by a best approximation of rank
at most `r` (`IsRun (MatrixEulerBUG.stepRel F r) (uniformGrid t₀ h) N Y`), all of rank at most
`r`, with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} ((11 L B + Lₜ) h + 3 ε)` for all `n ≤ N`,

where `N h ≤ T`. The constants do not depend on the singular values of the matrices `Y n`: the
bound is robust to small singular values. The only further hypothesis is that the right-hand
side is smaller than the tube radius, with a margin of two step lengths at the speed bound:
`e^{L T} δ + T e^{L T} ((11 L B + Lₜ) h + 3 ε) + 2 B h < ρ`. The same bound holds for *every*
run, not only for the one constructed (`MatrixEulerBUG.IsRun.norm_sub_le`).

## Main results

* `MatrixEulerBUG.exists_isStep`: a step of the factors exists for every field and every time
  step; the new bases have at most `2 r` columns.
* `MatrixEulerBUG.exists_stepRel_iff`: a step of `MatrixEulerBUG.stepRel` from `Y₀` exists if
  and only if `Y₀` has rank at most `r`.
* `MatrixEulerBUG.exists_run`: there is a run on every grid from every start value of rank at
  most `r`, for every field.
* `MatrixEulerBUG.isTubeLocal_stepRel`: the integrator is a tube-local method
  (`StepMethod.IsTubeLocal`) with the matrices of rank at most `r` as admissible values and
  margin constant `0`.
* `MatrixEulerBUG.stepRel.hasLocalError_uniformGrid`: the local error of one step of a uniform
  grid, from the hypotheses of the run theorem.
* `MatrixEulerBUG.IsRun.norm_sub_le`: every run satisfies the error bound.
* `MatrixEulerBUG.exists_run_norm_sub_le`: a run exists, has rank at most `r` and satisfies the
  error bound.

The examples at the end apply the result to the field `F(t, Y) = Y / max ‖Y‖ 1`, which has no
normal component, so that `ε = 0`; to the linear field `F(t, Y) = M Y + Y Nᵀ + G`, which is not
bounded and has `ε = ‖G‖`; and to a field that depends on time, with `Lₜ = 2 ‖G‖`. The first two
fields do not depend on time, so `Lₜ = 0` there.

## Implementation notes

`MatrixEulerBUG.exists_run_norm_sub_le` is an instance of the theorem for tube-local methods,
`StepMethod.IsTubeLocal.exists_run_norm_sub_le`, in the same way as
`MatrixBUG.exists_run_norm_sub_le`, `MatrixKSL.exists_run_norm_sub_le` and
`MatrixParallelBUG.exists_run_norm_sub_le`; the hypotheses they share have the same names and
the same order. Two hypotheses are new: the Lipschitz condition in time `hFt` and `0 ≤ Lₜ`.

A step is one evaluation of the field and two orthonormalizations. It therefore exists for
every field, without a Lipschitz or continuity hypothesis (`MatrixEulerBUG.exists_stepRel`). For
the same reason a step of the extended field `tubeExt F A a b ρ` is a step of `F` as soon as the
start value lies in the tube at the start time (`MatrixEulerBUG.stepRel_tubeExt_iff`): the step
evaluates the field only at `(t₀, Y₀)`. This is why the margin constant in
`MatrixEulerBUG.isTubeLocal_stepRel` is `0`. The run theorem asks for a margin constant of at
least `2`, because the exact solutions through the numerical values have to stay in the tube;
`StepMethod.IsTubeLocal.mono` gives it.

The Lipschitz condition in time is stated on the tube. In each step it is used at the start
value `Y₀` with `s` the start time, which is the form of the hypothesis of `euler_defect_le`:
`‖F(t, Y₀) - F(t₀, Y₀)‖ ≤ Lₜ (t - t₀)` during the step. The start value lies in the tube during
the whole step by `IsBoundedOnTube.norm_sub_le_of_near`.

The constants: a step without truncation has local error `h ((L B + Lₜ) / 2 · h + ε)`, the exact
solution through a matrix of rank at most `r` is within `h (10 L B h + ε)` of the matrices of
rank at most `r` after one step, and a best approximation costs this distance plus twice the
error before truncation. This gives `10 + 2 · 1/2 = 11`, `2 · 1/2 = 1` in front of `Lₜ`, and
`1 + 2 · 1 = 3`. Joint continuity of `F` on the tube is needed for the distance to the matrices
of rank at most `r` (`distLR_flow_le_of_tube`) and by the run theorem, not by the step.

Compared with `augmentedBug_euler_global_error`, which is stated for orthogonal projectors, the
results of this file need the Lipschitz bound, the bound on the field and the bound on its
normal component only on the tube around the exact solution, they need no exact flows started
at the numerical values, the steps are shown to exist, and the truncation is the best
approximation of rank at most `r` instead of an unspecified truncation with a tolerance: no
tolerance appears in the bound, and the rank of the numerical values is `r` throughout. The
price is the smallness condition, which keeps the numerical values in the tube, joint
continuity of `F` on the tube, and the larger constants `11 L B + Lₜ` and `3` in place of
`(L B + Lₜ) / 2` and `1`. For the integrator with a truncation tolerance, whose rank changes
from step to step, `augmentedBug_euler_global_error` remains the result to use.

The theorem `eulerBug_global_error` (Hauck and Schnake, arXiv:2209.00550, Theorem 4.1) has other
hypotheses: the new bases are required to contain the results of the explicit Euler K-step and
L-step, the result of a step is not truncated, and the normal component of the field is
measured at these two results. Its constants `(7 L B + 3 Lₜ) / 2` and `2` belong to these
hypotheses and cannot be compared term by term with `11 L B + Lₜ` and `3`.

## References

* F. Nobile, S. Riffaud, *High-order BUG dynamical low-rank integrators based on explicit
  Runge–Kutta methods*, arXiv:2502.07040, §2.1, Algorithm 1.
* C. D. Hauck, S. R. Schnake, *A predictor-corrector strategy for adaptivity in dynamical
  low-rank approximations*, arXiv:2209.00550, Theorem 4.1.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixEulerBUG

/-! ### Existence of one step -/

section Exists

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}

/-- **A step of the factors exists.** For every field `F`, all times `t₀`, `t₁` and all factors
`U₀`, `S₀`, `V₀` with orthonormal `U₀`, `V₀` there are matrices `Û`, `V̂` with orthonormal
columns and a matrix `Ŝ` that form a step of the explicit Euler BUG integrator (`IsStep`). The
range of `Û` contains the columns of `U₀` and of `F₀ V₀`, the range of `V̂` those of `V₀` and of
`F₀ᵀ U₀`, where `F₀ = F(t₀, U₀ S₀ V₀ᵀ)`. The numbers of columns are `min (2 r) m` and
`min (2 r) n`, so at most `2 r`. Nothing is assumed about the field: the step is one evaluation
of `F` and two orthonormalizations. -/
theorem exists_isStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ)
    {U₀ : Matrix m (Fin r) ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    {V₀ : Matrix n (Fin r) ℝ} (hV₀ : V₀ᵀ * V₀ = 1) :
    ∃ (s s' : ℕ) (Ua : Matrix m (Fin s) ℝ) (Sa : Matrix (Fin s) (Fin s') ℝ)
      (Va : Matrix n (Fin s') ℝ), s ≤ 2 * r ∧ s' ≤ 2 * r ∧ IsStep F t₀ t₁ U₀ S₀ V₀ Ua Sa Va := by
  have hK : (Matrix.fromCols (F t₀ (U₀ * S₀ * V₀ᵀ) * V₀) U₀).rank ≤ 2 * r := by
    have := (Matrix.fromCols (F t₀ (U₀ * S₀ * V₀ᵀ) * V₀) U₀).rank_le_card_width
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  have hL : (Matrix.fromCols ((F t₀ (U₀ * S₀ * V₀ᵀ))ᵀ * U₀) V₀).rank ≤ 2 * r := by
    have := (Matrix.fromCols ((F t₀ (U₀ * S₀ * V₀ᵀ))ᵀ * U₀) V₀).rank_le_card_width
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  obtain ⟨Ua, hUa, hcapK, hcapU⟩ := exists_orthonormal_capture_fromCols
    (F t₀ (U₀ * S₀ * V₀ᵀ) * V₀) U₀ (r := min (2 * r) (Fintype.card m))
    (le_min hK (Matrix.rank_le_card_height _)) (min_le_right _ _)
  obtain ⟨Va, hVa, hcapL, hcapV⟩ := exists_orthonormal_capture_fromCols
    ((F t₀ (U₀ * S₀ * V₀ᵀ))ᵀ * U₀) V₀ (r := min (2 * r) (Fintype.card n))
    (le_min hL (Matrix.rank_le_card_height _)) (min_le_right _ _)
  exact ⟨_, _, Ua, _, Va, min_le_left _ _, min_le_left _ _,
    ⟨hU₀, hV₀, hUa, hVa, hcapU, hcapK, hcapV, hcapL, rfl⟩⟩

/-- **An explicit Euler BUG step without truncation exists from every start value of rank at
most `r`.** If `r ≤ m` and `r ≤ n`, then for every field `F` and all times `t₀`, `t₁` every
matrix `Y₀` of rank at most `r` has a successor under `augmentedRel F r`. -/
theorem exists_augmentedRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) : ∃ Yh, augmentedRel F r t₀ t₁ Y₀ Yh := by
  obtain ⟨U₀, S₀, V₀, hU₀, hV₀, rfl⟩ := exists_factor_of_rank_le hY₀ hrm hrn
  obtain ⟨s, s', Ua, Sa, Va, hsr, hsr', hs⟩ := exists_isStep F t₀ t₁ hU₀ S₀ hV₀
  exact ⟨_, hs.augmentedRel hsr hsr'⟩

/-- **A step of the fixed-rank explicit Euler BUG integrator exists from every start value of
rank at most `r`.** If `r ≤ m` and `r ≤ n`, then for every field `F` and all times `t₀`, `t₁`
every matrix `Y₀` of rank at most `r` has a successor under `stepRel F r`. -/
theorem exists_stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) : ∃ Y₁, stepRel F r t₀ t₁ Y₀ Y₁ := by
  obtain ⟨Yh, hYh⟩ := exists_augmentedRel F t₀ t₁ hrm hrn hY₀
  exact hYh.exists_stepRel

/-- **The admissible start values of the fixed-rank explicit Euler BUG integrator are exactly
the matrices of rank at most `r`**: a step of `stepRel F r` from `Y₀` exists if and only if `Y₀`
has rank at most `r` (for `r ≤ m`, `r ≤ n`). -/
theorem exists_stepRel_iff (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ} :
    (∃ Y₁, stepRel F r t₀ t₁ Y₀ Y₁) ↔ Y₀.rank ≤ r :=
  ⟨fun ⟨_, h⟩ => h.rank_start_le, exists_stepRel F t₀ t₁ hrm hrn⟩

/-- **A run of the fixed-rank explicit Euler BUG integrator exists** on every grid, from every
start value of rank at most `r`, for every field. That the run stays near an exact solution is
the content of `exists_run_norm_sub_le`. -/
theorem exists_run (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) {τ : ℕ → ℝ} {N : ℕ}
    (hτ : IsGrid τ N) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) τ N Y := by
  refine exists_isRun hτ Y₀ fun n _ Y hY0 hY => ?_
  exact exists_stepRel F _ _ hrm hrn (IsRun.rank_le hY (by rw [hY0]; exact hY₀) n le_rfl)

end Exists

/-! ### The integrator as a tube-local method -/

section TubeLocal

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}

/-- **The fixed-rank explicit Euler BUG integrator is a tube-local method**
(`StepMethod.IsTubeLocal`), with the matrices of rank at most `r` as admissible values and
margin constant `0`:

* a step exists from every matrix of rank at most `r`, for every field
  (`MatrixEulerBUG.exists_stepRel`);
* the result of a step has rank at most `r` (`MatrixEulerBUG.stepRel.rank_le`); the
  intermediate matrix of rank up to `2 r` is hidden inside the step;
* if `‖Y₀ - A t₀‖ < ρ`, a step from `Y₀` of the extended field `tubeExt F A a b ρ` is a step of
  `F` (`MatrixEulerBUG.stepRel_tubeExt_iff`).

The margin constant is `0` because the step evaluates the field only at `(t₀, Y₀)`: it is enough
that the start value lies in the tube at the start time. The integrators with exactly solved
substeps have margin constant `2`. With the local error
`MatrixEulerBUG.stepRel.hasLocalError_of_tube` this is all that
`StepMethod.IsTubeLocal.exists_run_norm_sub_le` needs, after `StepMethod.IsTubeLocal.mono` has
raised the margin constant to the `2` which that theorem asks for. -/
theorem isTubeLocal_stepRel (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) :
    StepMethod.IsTubeLocal (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => stepRel G r)
      (fun Y => Y.rank ≤ r) 0 where
  exists_step := fun _ _ _ hY₀ => exists_stepRel _ _ _ hrm hrn hY₀
  adm_of_step := fun _ _ hstep => hstep.rank_le
  step_of_tubeExt := fun _ _ ha hb h01 _ _ hsmall hstep =>
    (stepRel_tubeExt_iff ⟨ha, h01.trans hb⟩ (by simpa using hsmall.le)).1 hstep

end TubeLocal

/-! ### The error bound, and existence of a run near the exact solution -/

section Error

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {t₀ h T ρ L B ε Lt δ : ℝ}
  {N : ℕ}

/-- **Local error of one step of a uniform grid.** Under the hypotheses of the run theorem on
`F` and `A` (`DLRAProblem`, joint continuity and `FactoredNormalBoundOn` on the tube of radius
`ρ` around `A` over `[t₀, t₀ + N h]`, and `‖F(t, X) - F(s, X)‖ ≤ Lₜ (t - s)` for `s ≤ t` and
`X` in the tube at both times), a step of the fixed-rank explicit Euler BUG integrator over
`[t₀ + k h, t₀ + (k + 1) h]`, `k < N`, whose start value `Z₀` satisfies
`‖Z₀ - A (t₀ + k h)‖ + 2 B h < ρ` has local error `h ((11 L B + Lₜ) h + 3 ε)`.

The Lipschitz condition in time is used at the start value only, with `s` the start time: `Z₀`
lies in the tube during the whole step (`IsBoundedOnTube.norm_sub_le_of_near`). This is the
form in which `MatrixEulerBUG.stepRel.hasLocalError_of_tube` needs it. -/
theorem stepRel.hasLocalError_uniformGrid {k : ℕ} {Z₀ Z₁ : Matrix m n ℝ}
    (hstep : stepRel F r (t₀ + k * h) (t₀ + (k + 1) * h) Z₀ Z₁)
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hFt : ∀ s t x, s ≤ t → (s, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ →
      (t, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ → ‖F t x - F s x‖ ≤ Lt * (t - s))
    (hh : 0 ≤ h) (hk : k < N) (hnear : ‖Z₀ - A (t₀ + k * h)‖ + 2 * B * h < ρ) :
    HasLocalError F (t₀ + k * h) (t₀ + (k + 1) * h) Z₀ Z₁
      (h * ((11 * L * B + Lt) * h + 3 * ε)) := by
  obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hk
  have hBh : 0 ≤ B * h := mul_nonneg hP.B_nonneg hh
  have hA := hP.sol.mono ha hb
  -- the start value lies in the tube during the whole step
  have hin : ∀ t ∈ Icc (t₀ + k * h) (t₀ + (k + 1) * h), ‖Z₀ - A t‖ ≤ ρ :=
    hP.bounded.norm_sub_le_of_near hP.B_nonneg ha hb hA (by rw [hsub]; linarith)
  have hs : (t₀ + k * h, Z₀) ∈ tubeSet A t₀ (t₀ + N * h) ρ :=
    ⟨⟨ha, h01.trans hb⟩, hin (t₀ + k * h) (left_mem_Icc.2 h01)⟩
  have hFt' : ∀ t ∈ Ico (t₀ + k * h) (t₀ + (k + 1) * h),
      ‖F t Z₀ - F (t₀ + k * h) Z₀‖ ≤ Lt * (t - (t₀ + k * h)) := fun t ht =>
    hFt _ t Z₀ ht.1 hs ⟨⟨ha.trans ht.1, ht.2.le.trans hb⟩, hin t (Ico_subset_Icc_self ht)⟩
  have hloc := hstep.hasLocalError_of_tube hε hε₀ hP.lipschitz hP.L_nonneg hP.bounded
    hP.B_nonneg hc hP.sol.cont ha hb h01 hA hFt' (by rw [hsub]; linarith)
  rwa [hsub] at hloc

/-- **Every run of the fixed-rank explicit Euler BUG integrator satisfies the robust error
bound.** Let `A` solve `Y' = F(t, Y)` on `[t₀, t₀ + N h]`, and let `F` be `L`-Lipschitz and
bounded by `B` on the tube of radius `ρ` around `A` (`DLRAProblem`), jointly continuous there,
with normal component at most `ε` at the rank-`r` matrices of the tube
(`FactoredNormalBoundOn`), and with `‖F(t, X) - F(s, X)‖ ≤ Lₜ (t - s)` for `s ≤ t` and `X` in
the tube at both times. Let `Y 0, …, Y N` be a run of the integrator with step size `h ≥ 0`,
`N h ≤ T`, and `‖Y 0 - A t₀‖ ≤ δ`. If the bound below is smaller than the tube radius with a
margin of `2 B h`, then for all `n ≤ N`

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} ((11 L B + Lₜ) h + 3 ε)`.

The constants do not depend on the singular values of the `Y n`. For a field that does not
depend on time, `Lₜ = 0`.

Nothing is assumed about `F` outside the tube, and no auxiliary exact solutions started at the
numerical values appear: they are constructed in the proof
(`IsRun.norm_sub_le_of_tube_uniformGrid`), and the local error of each step comes from
`MatrixEulerBUG.stepRel.hasLocalError_uniformGrid`. -/
theorem IsRun.norm_sub_le {Y : ℕ → Matrix m n ℝ}
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → (s, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ →
      (t, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ → ‖F t x - F s x‖ ≤ Lt * (t - s))
    (hh : 0 ≤ h) (hNT : N * h ≤ T)
    (hsmall : Real.exp (L * T) * δ +
      T * Real.exp (L * T) * ((11 * L * B + Lt) * h + 3 * ε) + 2 * B * h < ρ)
    (hY : IsRun (stepRel F r) (uniformGrid t₀ h) N Y) (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (L * T) * δ + T * Real.exp (L * T) * ((11 * L * B + Lt) * h + 3 * ε) := by
  have hc₀ : 0 ≤ (11 * L * B + Lt) * h + 3 * ε :=
    add_nonneg (mul_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hP.L_nonneg) hP.B_nonneg) hLt) hh)
      (mul_nonneg (by norm_num) hε₀)
  refine hY.norm_sub_le_of_tube_uniformGrid (T := T) (δ₀ := δ)
    (c := (11 * L * B + Lt) * h + 3 * ε) hP hc (fun n hn Y₀ Y₁ hnear hstep => ?_) hc₀ hδ hNT
    hsmall
  -- the local error of a step that starts within the error bound of `A`
  exact hstep.hasLocalError_uniformGrid hP hc hε hε₀ hFt hh hn (by linarith)

/-- **Existence and robust error bound for the fixed-rank explicit Euler BUG integrator.** Let
`A` solve `Y' = F(t, Y)` on `[t₀, t₀ + N h]`, and let `F` be `L`-Lipschitz and bounded by `B` on
the tube of radius `ρ` around `A` (`DLRAProblem`), jointly continuous there, with normal
component at most `ε` at the rank-`r` matrices of the tube (`FactoredNormalBoundOn`), and with
`‖F(t, X) - F(s, X)‖ ≤ Lₜ (t - s)` for `s ≤ t` and `X` in the tube at both times. Let `r ≤ m`,
`r ≤ n`, let the step size satisfy `h ≥ 0` and `N h ≤ T`, and let `Y₀` be a start value of rank
at most `r` with `‖Y₀ - A t₀‖ ≤ δ`. If

  `e^{L T} δ + T e^{L T} ((11 L B + Lₜ) h + 3 ε) + 2 B h < ρ`,

then the integrator can be run from `Y₀`: there are `Y 0 = Y₀, Y 1, …, Y N`, each obtained from
the previous one by an explicit Euler BUG step of size `h` followed by a best approximation of
rank at most `r`, all of rank at most `r`, with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} ((11 L B + Lₜ) h + 3 ε)` for all `n ≤ N`.

The constants are independent of the singular values of the matrices `Y n`, and nothing is
assumed about `F` outside the tube. No truncation tolerance appears: the truncation to rank `r`
costs no more than a constant times the error of the step itself. For a field that does not
depend on time, `Lₜ = 0`.

This is `StepMethod.IsTubeLocal.exists_run_norm_sub_le` for the tube-local method
`MatrixEulerBUG.isTubeLocal_stepRel`, whose margin constant `0` is raised to `2` by
`StepMethod.IsTubeLocal.mono`: the margin `2 B h` keeps the exact solutions through the
numerical values in the tube, which the local error needs. The bound itself holds for every run
(`MatrixEulerBUG.IsRun.norm_sub_le`). The hypotheses on `F` and `A` are those of
`MatrixBUG.exists_run_norm_sub_le`, `MatrixKSL.exists_run_norm_sub_le` and
`MatrixParallelBUG.exists_run_norm_sub_le` together with the Lipschitz condition in time, so the
four integrators can be compared on the same problem. -/
theorem exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → (s, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ →
      (t, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ → ‖F t x - F s x‖ ≤ Lt * (t - s))
    (hh : 0 ≤ h) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ +
      T * Real.exp (L * T) * ((11 * L * B + Lt) * h + 3 * ε) + 2 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * δ + T * Real.exp (L * T) * ((11 * L * B + Lt) * h + 3 * ε) := by
  have hc₀ : 0 ≤ (11 * L * B + Lt) * h + 3 * ε :=
    add_nonneg (mul_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hP.L_nonneg) hP.B_nonneg) hLt) hh)
      (mul_nonneg (by norm_num) hε₀)
  refine ((isTubeLocal_stepRel hrm hrn).mono (by norm_num : (0 : ℝ) ≤ 2)).exists_run_norm_sub_le
    le_rfl hP hc (fun k hk Z₀ Z₁ _ hnear hstep => ?_) hc₀ hh hNT hY₀ hδ hsmall
  -- the local error of a step that starts within the error bound of `A`
  exact stepRel.hasLocalError_uniformGrid hstep hP hc hε hε₀ hFt hh hk (by linarith)

end Error

/-! ### Examples: a nonlinear field, a linear field, a field that depends on time -/

section Examples

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}

/-- **Non-vacuity of the existence and error theorem.** The radial field
`F(t, Y) = Y / max ‖Y‖ 1` is `2`-Lipschitz, bounded by `1`, and has no normal component at any
matrix (`MatrixKSL.radial_normal_eq_zero`), so `ε = 0`. It does not depend on time, so
`Lₜ = 0`. For every solution `A` of `Y' = F(t, Y)` on `[t₀, t₀ + N h]`, of any rank (the zero
function is one), and every start value `Y₀` of rank at most `r` with `‖Y₀ - A t₀‖ ≤ δ`, the
fixed-rank explicit Euler BUG integrator can be run with any step size `h ≥ 0`, and the run
stays within `e^{2 T} δ + 22 T e^{2 T} h` of `A`. No smallness condition remains, because the
field is Lipschitz and bounded everywhere and the tube radius can be chosen as large as
needed. -/
example (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) {A : ℝ → Matrix m n ℝ}
    {t₀ h T δ : ℝ} {N : ℕ}
    (hA : ODESolution (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) A t₀ (t₀ + N * h))
    (hh : 0 ≤ h) (hNT : N * h ≤ T) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r)
    (hδ : ‖Y₀ - A t₀‖ ≤ δ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (stepRel (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) r)
        (uniformGrid t₀ h) N Y ∧
      ∀ j ≤ N, (Y j).rank ≤ r ∧ ‖Y j - A (t₀ + j * h)‖ ≤
        Real.exp (2 * T) * δ + T * Real.exp (2 * T) * ((11 * 2 * 1 + 0) * h + 3 * 0) := by
  have hcont : Continuous fun Z : Matrix m n ℝ => MatrixKSL.radial Z :=
    (LipschitzWith.of_dist_le' (K := 2) fun X Y => by
      rw [dist_eq_norm, dist_eq_norm]; exact MatrixKSL.norm_radial_sub_le X Y).continuous
  exact exists_run_norm_sub_le (F := fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z)
    (A := A) (L := 2) (B := 1) (ε := 0) (Lt := 0)
    (ρ := Real.exp (2 * T) * δ + T * Real.exp (2 * T) * ((11 * 2 * 1 + 0) * h + 3 * 0)
      + 2 * 1 * h + 1)
    ⟨hA, by norm_num, by norm_num, fun _ _ X Y _ _ => MatrixKSL.norm_radial_sub_le X Y,
      fun _ _ X _ => MatrixKSL.norm_radial_le X⟩
    (hcont.comp continuous_snd).continuousOn
    (fun t U V S hU hV _ => MatrixKSL.radial_normal_eq_zero t U S V hU hV) le_rfl le_rfl
    (fun _ _ _ _ _ _ => by simp) hh hNT hrm hrn hY₀ hδ (lt_add_one _)

/-- **Non-vacuity for a field that is not bounded.** The linear field
`F(t, Y) = M Y + Y Nᵀ + G` with a stationary point `C` (`M C + C Nᵀ + G = 0`) is Lipschitz with
constant `‖M‖ + ‖N‖` but not bounded. On the tube of radius `ρ` around the constant solution
`A(t) = C` it is bounded by `(‖M‖ + ‖N‖) ρ`, and its normal component at the rank-`r` matrices
is at most `‖G‖` (`dlraProblem_linear`, `factoredNormalBoundOn_linear`). It does not depend on
time, so `Lₜ = 0`. Hence, under the smallness condition, the fixed-rank explicit Euler BUG
integrator can be run from every `Y₀` of rank at most `r` near `C`, and the run satisfies the
error bound with `ε = ‖G‖`. The corresponding examples for the BUG integrator, the
projector-splitting integrator and the parallel BUG integrator treat the same problem. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    (t₀ : ℝ) {ρ T δ h : ℝ} {K : ℕ} (hρ : 0 ≤ ρ) (hh : 0 ≤ h) (hKT : K * h ≤ T)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - C‖ ≤ δ)
    (hsmall : Real.exp ((‖M‖ + ‖N‖) * T) * δ + T * Real.exp ((‖M‖ + ‖N‖) * T) *
      ((11 * (‖M‖ + ‖N‖) * ((‖M‖ + ‖N‖) * ρ) + 0) * h + 3 * ‖G‖)
      + 2 * ((‖M‖ + ‖N‖) * ρ) * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (stepRel (fun _ Y => M * Y + Y * Nᵀ + G) r) (uniformGrid t₀ h) K Y ∧
      ∀ j ≤ K, (Y j).rank ≤ r ∧ ‖Y j - C‖ ≤ Real.exp ((‖M‖ + ‖N‖) * T) * δ +
        T * Real.exp ((‖M‖ + ‖N‖) * T) *
          ((11 * (‖M‖ + ‖N‖) * ((‖M‖ + ‖N‖) * ρ) + 0) * h + 3 * ‖G‖) :=
  exists_run_norm_sub_le (A := fun _ => C) (Lt := 0) (dlraProblem_linear M N G C hC _ _ hρ)
    (continuous_uncurry_linear M N G).continuousOn
    (factoredNormalBoundOn_linear M N G _) (norm_nonneg G) le_rfl
    (fun _ _ _ _ _ _ => by simp) hh hKT hrm hrn hY₀ hδ hsmall

/-- **Non-vacuity with a Lipschitz constant in time that is not zero.** The field
`F(t, Y) = Y / max ‖Y‖ 1 + (t / max |t| 1) G` depends on time. It is `2`-Lipschitz in `Y`,
bounded by `1 + ‖G‖`, its normal component is at most `‖G‖` at every matrix, and
`‖F(t, Y) - F(s, Y)‖ ≤ 2 ‖G‖ (t - s)` for `s ≤ t`, so `Lₜ = 2 ‖G‖`. For every initial value `A₀`
the problem `Y' = F(t, Y)`, `Y(t₀) = A₀` has a solution `A` on `[t₀, t₀ + N h]`
(`exists_ODESolution`), and from every start value `Y₀` of rank at most `r` with
`‖Y₀ - A₀‖ ≤ δ` the fixed-rank explicit Euler BUG integrator can be run with any step size
`h ≥ 0`; the run satisfies the error bound with `L = 2`, `B = 1 + ‖G‖`, `ε = ‖G‖` and
`Lₜ = 2 ‖G‖`. All hypotheses of the theorem are satisfied with data that are not zero when
`G ≠ 0`. -/
example (G : Matrix m n ℝ) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) (t₀ : ℝ)
    {h T δ : ℝ} {N : ℕ} (hh : 0 ≤ h) (hNT : N * h ≤ T) (A₀ : Matrix m n ℝ)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A₀‖ ≤ δ) :
    ∃ A : ℝ → Matrix m n ℝ,
      ODESolution (fun (t : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z + MatrixKSL.radial t • G)
        A t₀ (t₀ + N * h) ∧ A t₀ = A₀ ∧
      ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
        IsRun (stepRel (fun (t : ℝ) (Z : Matrix m n ℝ) =>
          MatrixKSL.radial Z + MatrixKSL.radial t • G) r) (uniformGrid t₀ h) N Y ∧
        ∀ j ≤ N, (Y j).rank ≤ r ∧ ‖Y j - A (t₀ + j * h)‖ ≤ Real.exp (2 * T) * δ +
          T * Real.exp (2 * T) * ((11 * 2 * (1 + ‖G‖) + 2 * ‖G‖) * h + 3 * ‖G‖) := by
  have hG : ∀ t : ℝ, ‖MatrixKSL.radial t • G‖ ≤ ‖G‖ := fun t => by
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg G) (MatrixKSL.norm_radial_le t)
  have hLip : ∀ (t : ℝ) (X Y : Matrix m n ℝ),
      ‖MatrixKSL.radial X + MatrixKSL.radial t • G -
        (MatrixKSL.radial Y + MatrixKSL.radial t • G)‖ ≤ 2 * ‖X - Y‖ := fun t X Y => by
    rw [add_sub_add_right_eq_sub]
    exact MatrixKSL.norm_radial_sub_le X Y
  have hBd : ∀ (t : ℝ) (X : Matrix m n ℝ),
      ‖MatrixKSL.radial X + MatrixKSL.radial t • G‖ ≤ 1 + ‖G‖ := fun t X =>
    (norm_add_le _ _).trans (add_le_add (MatrixKSL.norm_radial_le X) (hG t))
  have hTime : ∀ (s t : ℝ) (X : Matrix m n ℝ), s ≤ t →
      ‖MatrixKSL.radial X + MatrixKSL.radial t • G -
        (MatrixKSL.radial X + MatrixKSL.radial s • G)‖ ≤ 2 * ‖G‖ * (t - s) := by
    intro s t X hst
    rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul]
    have h1 := MatrixKSL.norm_radial_sub_le t s
    rw [Real.norm_eq_abs (t - s), abs_of_nonneg (sub_nonneg.2 hst)] at h1
    calc ‖MatrixKSL.radial t - MatrixKSL.radial s‖ * ‖G‖
        ≤ 2 * (t - s) * ‖G‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg G)
      _ = 2 * ‖G‖ * (t - s) := by ring
  have hNormal : ∀ (t : ℝ) (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ)
      (S : Matrix (Fin r) (Fin r) ℝ), Uᵀ * U = 1 → Vᵀ * V = 1 →
      ‖(1 - U * Uᵀ) * (MatrixKSL.radial (U * S * Vᵀ) + MatrixKSL.radial t • G) *
        (1 - V * Vᵀ)‖ ≤ ‖G‖ := by
    intro t U V S hU hV
    have h1 : ‖(1 - U * Uᵀ) * MatrixKSL.radial (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ 0 :=
      MatrixKSL.radial_normal_eq_zero t U S V hU hV
    have h2 := (MatrixKSL.norm_normal_le hU hV (MatrixKSL.radial t • G)).trans (hG t)
    rw [Matrix.mul_add, Matrix.add_mul]
    exact (norm_add_le _ _).trans (by linarith)
  have hcZ : Continuous fun Z : Matrix m n ℝ => MatrixKSL.radial Z :=
    (LipschitzWith.of_dist_le' (K := 2) fun X Y => by
      rw [dist_eq_norm, dist_eq_norm]; exact MatrixKSL.norm_radial_sub_le X Y).continuous
  have hct : Continuous fun t : ℝ => MatrixKSL.radial t :=
    (LipschitzWith.of_dist_le' (K := 2) fun x y => by
      rw [dist_eq_norm, dist_eq_norm]; exact MatrixKSL.norm_radial_sub_le x y).continuous
  have hcF : Continuous fun p : ℝ × Matrix m n ℝ =>
      MatrixKSL.radial p.2 + MatrixKSL.radial p.1 • G :=
    (hcZ.comp continuous_snd).add ((hct.comp continuous_fst).smul continuous_const)
  obtain ⟨A, hA, hA₀⟩ := exists_ODESolution
    (F := fun (t : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z + MatrixKSL.radial t • G)
    (L := 2) (B := 1 + ‖G‖) (fun t X Y => hLip t X Y) (fun t X => hBd t X)
    (fun _ => continuous_const.add (hct.smul continuous_const))
    (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg N) hh)) A₀
  refine ⟨A, hA, hA₀, ?_⟩
  exact exists_run_norm_sub_le
    (F := fun (t : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z + MatrixKSL.radial t • G)
    (A := A) (L := 2) (B := 1 + ‖G‖) (ε := ‖G‖) (Lt := 2 * ‖G‖)
    (ρ := Real.exp (2 * T) * δ +
      T * Real.exp (2 * T) * ((11 * 2 * (1 + ‖G‖) + 2 * ‖G‖) * h + 3 * ‖G‖)
      + 2 * (1 + ‖G‖) * h + 1)
    ⟨hA, by norm_num, by positivity, fun t _ X Y _ _ => hLip t X Y, fun t _ X _ => hBd t X⟩
    hcF.continuousOn (fun t U V S hU hV _ => hNormal t U V S hU hV) (norm_nonneg G)
    (by positivity) (fun s t X hst _ _ => hTime s t X hst) hh hNT hrm hrn hY₀
    (by rw [hA₀]; exact hδ) (lt_add_one _)

end Examples

end MatrixEulerBUG

end LeanDLRA
