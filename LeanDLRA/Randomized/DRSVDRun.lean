import LeanDLRA.Randomized.DRSVDStep

/-!
# Runs of the dynamical randomized SVD: existence and error bound

This file gives runs and the error bound of the dynamical randomized singular value
decomposition (DRSVD) of [Carrel2025], Algorithm 3, in the variant with an augmented sketch and
truncation to rank `r` by a best approximation, for a matrix differential equation
`Y' = F(t, Y)`: the integrator can be run, and every run stays close to the exact solution. The
step relation `MatrixDRSVD.stepRel F r k l` (sketch basis with `k` columns, range basis with `l`
columns) and its local error are in `LeanDLRA/Randomized/DRSVDStep.lean`.

**Setting.** Let `A` be a solution of `Y' = F(t, Y)` on `[t₀, t₀ + N h]`. The field `F` is only
assumed to be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around `A`
(`DLRAProblem F A t₀ (t₀ + N h) ρ L B`), jointly continuous there, and to have a normal component
of size at most `ε` at the factored matrices in the tube with `r` and with `k` columns
(`FactoredNormalBoundOn F s _ ε` for `s ∈ {r, k}`). Nothing is assumed about `F` outside the
tube. The sketch is any orthonormal basis with `k ≥ r` columns whose range contains the row space
of the start value of the step; no probability enters.

**Result** (`MatrixDRSVD.exists_run_norm_sub_le`). Let `r ≤ k ≤ l`, `k ≤ n`, `l ≤ m`. For every
start value `Y₀` of rank at most `r` with `‖Y₀ - A t₀‖ ≤ δ` there are matrices
`Y 0 = Y₀, Y 1, …, Y N`, each obtained from the previous one by a DRSVD step of size `h ≤ H`
followed by a best approximation of rank at most `r`, all of rank at most `r`, with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} ((2 c₁ + 1) ε + (2 c₂ + 10 L B) h)`

for all `n ≤ N`, where `N h ≤ T`, `c₁ = bugC₁ L H` and `c₂ = bugC₂ L B H`. The constants do not
depend on the singular values of the matrices `Y n`. The only further hypothesis is that the
right-hand side plus `3 B h` is less than `ρ`. The same bound holds for every run of the
augmented-sketch variant from a start value of rank at most `r` (`MatrixDRSVD.IsRun.norm_sub_le`):
its sketch bases are orthonormal, have `k` columns and contain the row space of the start value of
their step. The sketch enters the bound only through the hypothesis on the normal component at
the factored matrices of the tube with `k` columns (`FactoredNormalBoundOn F k _ ε`), which must
hold for every such basis. Sketches whose range does not contain the row space of the start
value, and the probabilistic analysis of [Carrel2025], are not covered.

## Main results

* `MatrixDRSVD.exists_augmentedRel`, `MatrixDRSVD.exists_stepRel`: a step exists from every
  start value of rank at most `k`, for every Lipschitz field that is continuous in time on the
  step interval, if `k ≤ n` and `k ≤ l ≤ m`.
* `MatrixDRSVD.exists_run`: for a field that is Lipschitz everywhere there is a run on every grid
  from every start value of rank at most `r ≤ k`.
* `MatrixDRSVD.isTubeLocal_stepRel`: the integrator is a tube-local method
  (`StepMethod.IsTubeLocal`) with the matrices of rank at most `r` as admissible values and
  margin constant `3`.
* `MatrixDRSVD.IsRun.norm_sub_le`: every run from a start value of rank at most `r` satisfies the
  error bound.
* `MatrixDRSVD.exists_run_norm_sub_le`: a run exists, has rank at most `r` and satisfies the
  error bound.

## Implementation notes

`MatrixDRSVD.exists_run_norm_sub_le` is an instance of the theorem for tube-local methods,
`StepMethod.IsTubeLocal.exists_run_norm_sub_le`, in the same way as
`MatrixParallelBUG.exists_run_norm_sub_le`. The margin constant `3` is that of the BUG integrator
with one mode: the B-step starts at `Y₀` and moves by at most `B h`, the C-step starts at
`Q Qᵀ Y₀`, which is within `B h` of `Y₀` because `Q` captures the result of the B-step.

The B- and C-step are differential equations for the factors whose fields are the field `F`
conjugated by linear maps; their solutions exist by
`MatrixBUG.exists_odeSolution_conj_of_lipschitz`. A sketch basis whose range contains the row
space of `Y₀` exists if `rank Y₀ ≤ k ≤ n`, and a range basis that captures the result of the
B-step exists if `k ≤ l ≤ m` (`exists_orthonormal_capture`).

Compared with `RandomizedBUG.drsvd_global_error_le`, the hypotheses on `F` are needed on the tube
around `A` only, no exact flows started at the numerical values have to be supplied, and the
truncation is a best approximation of rank at most `r` instead of a truncation with a tolerance:
no tolerance appears in the bound. The price is the smallness condition, joint continuity of `F`
on the tube, the normal bound at rank `r`, and the larger constants `2 c₁ + 1`, `2 c₂ + 10 L B`.

## References

* [Carrel2025] B. Carrel, *Randomized methods for dynamical low-rank approximation*, §§2–3.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixDRSVD

/-! ### Existence of steps and runs, and the integrator as a tube-local method -/

section Exists

variable {m n : Type*} [Fintype m] [Fintype n] {r k l : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
  {L : ℝ}

/-- **A DRSVD step without truncation exists from every start value of rank at most `k`.** If
`F` is Lipschitz and continuous in time on `[t₀, t₁]`, `k ≤ n` and `k ≤ l ≤ m`, then every `Y₀`
of rank at most `k` has a successor under `MatrixDRSVD.augmentedRel F k l`: a sketch basis with
`k` orthonormal columns whose range contains the row space of `Y₀` and a range basis with `l`
orthonormal columns that captures the result of the B-step exist
(`exists_orthonormal_capture`), and the B- and C-step have solutions
(`MatrixBUG.exists_odeSolution_conj_of_lipschitz`). The field need not be bounded. -/
theorem exists_augmentedRel (hF : IsLipschitzField F L) {t₀ t₁ : ℝ}
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁)
    (hkn : k ≤ Fintype.card n) (hkl : k ≤ l) (hlm : l ≤ Fintype.card m) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ k) : ∃ Yh, augmentedRel F k l t₀ t₁ Y₀ Yh := by
  classical
  -- a sketch basis whose range contains the row space of `Y₀`
  obtain ⟨W, hW, hWY⟩ := exists_orthonormal_capture Y₀ᵀ (by rwa [Matrix.rank_transpose]) hkn
  have haug : Y₀ * W * Wᵀ = Y₀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hWY
  -- the B-step
  obtain ⟨Bs, hB, hB₀⟩ := MatrixBUG.exists_odeSolution_conj_of_lipschitz hF hc
    (Frobenius.rightMulCLM Wᵀ) (Frobenius.rightMulCLM W) (f := fun t X => F t (X * Wᵀ) * W)
    (fun t X => by simp) h01 (Y₀ * W)
  -- a range basis that captures the result of the B-step
  have hBr : (Bs t₁).rank ≤ l := (Bs t₁).rank_le_card_width.trans (by simpa using hkl)
  obtain ⟨Q, hQ, hcap⟩ := exists_orthonormal_capture (Bs t₁) hBr hlm
  -- the C-step
  obtain ⟨Cs, hC, hC₀⟩ := MatrixBUG.exists_odeSolution_conj_of_lipschitz hF hc
    (Frobenius.sandwichTransposeCLM Q (1 : Matrix n n ℝ))
    (Frobenius.sandwichTransposeCLM (1 : Matrix n n ℝ) Q)
    (f := fun t C => (F t (Q * Cᵀ))ᵀ * Q) (fun t C => by simp) h01 (Y₀ᵀ * Q)
  exact ⟨_, W, Q, Bs, Cs, hW, haug, hB, hB₀, hQ, hcap, hC, hC₀, rfl⟩

/-- **A DRSVD step with truncation to rank `r` exists from every start value of rank at most
`k`**, under the hypotheses of `MatrixDRSVD.exists_augmentedRel`: the result of the step without
truncation has a best approximation of rank at most `r`. -/
theorem exists_stepRel (hF : IsLipschitzField F L) {t₀ t₁ : ℝ}
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁)
    (hkn : k ≤ Fintype.card n) (hkl : k ≤ l) (hlm : l ≤ Fintype.card m) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ k) : ∃ Y₁, stepRel F r k l t₀ t₁ Y₀ Y₁ := by
  obtain ⟨Yh, hYh⟩ := exists_augmentedRel hF hc h01 hkn hkl hlm hY₀
  exact hYh.exists_stepRel

/-- All values of a run of the DRSVD integrator with truncation to rank `r` have rank at most
`r`, provided the start value has. -/
theorem IsRun.rank_le {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → Matrix m n ℝ}
    (hY : IsRun (stepRel F r k l) τ N Y) (h0 : (Y 0).rank ≤ r) : ∀ j ≤ N, (Y j).rank ≤ r
  | 0, _ => h0
  | j + 1, hj => (hY.step j hj).rank_le

/-- **Runs of the DRSVD integrator exist.** If `F` is Lipschitz (globally) and continuous in time
on `[τ 0, τ N]`, `r ≤ k ≤ l`, `k ≤ n` and `l ≤ m`, then on the grid `τ` there is a run of `N`
steps from every start value of rank at most `r`. No bound on the field is needed. For fields
that are Lipschitz only near a solution see `MatrixDRSVD.exists_run_norm_sub_le`. -/
theorem exists_run (hF : IsLipschitzField F L) {τ : ℕ → ℝ} {N : ℕ} (hτ : IsGrid τ N)
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc (τ 0) (τ N))) (hrk : r ≤ k)
    (hkn : k ≤ Fintype.card n) (hkl : k ≤ l) (hlm : l ≤ Fintype.card m) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r k l) τ N Y := by
  refine exists_isRun hτ Y₀ fun j hj Y hY0 hY => ?_
  have hsub : Icc (τ j) (τ (j + 1)) ⊆ Icc (τ 0) (τ N) :=
    Icc_subset_Icc (hτ.le_of_le j.zero_le hj.le) (hτ.le_of_le (Nat.succ_le_of_lt hj) le_rfl)
  exact exists_stepRel hF (fun Z => (hc Z).mono hsub) (hτ.mono j hj) hkn hkl hlm
    ((IsRun.rank_le hY (by rw [hY0]; exact hY₀) j le_rfl).trans hrk)

/-- **The DRSVD integrator with truncation to rank `r` is a tube-local method**
(`StepMethod.IsTubeLocal`), with the matrices of rank at most `r` as admissible values and
margin constant `3`, if `r ≤ k ≤ l`, `k ≤ n` and `l ≤ m`:

* a step exists from every matrix of rank at most `r`, for every globally Lipschitz field that is
  continuous in time on the step interval (`MatrixDRSVD.exists_stepRel`);
* the result of a step has rank at most `r` (`MatrixDRSVD.stepRel.rank_le`);
* if `‖Y₀ - A t₀‖ + 3 B (t₁ - t₀) < ρ`, a step from `Y₀` of the extended field
  `tubeExt F A a b ρ` is a step of `F` (`MatrixDRSVD.stepRel_tubeExt_iff_of_near`).

With the local error `MatrixDRSVD.stepRel.hasLocalError_of_tube` this is all that
`StepMethod.IsTubeLocal.exists_run_norm_sub_le` needs. -/
theorem isTubeLocal_stepRel (hrk : r ≤ k) (hkn : k ≤ Fintype.card n) (hkl : k ≤ l)
    (hlm : l ≤ Fintype.card m) :
    StepMethod.IsTubeLocal (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => stepRel G r k l)
      (fun Y => Y.rank ≤ r) 3 where
  exists_step := fun hG hc h01 hY₀ => exists_stepRel hG hc h01 hkn hkl hlm (hY₀.trans hrk)
  adm_of_step := fun _ _ hstep => hstep.rank_le
  step_of_tubeExt := fun hFB hB ha hb h01 hA _ hsmall hstep =>
    (stepRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 hstep

end Exists

/-! ### The error bound, and existence of a run near the exact solution -/

section Error

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r k l : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {t₀ h H T ρ L B ε δ : ℝ}
  {N : ℕ}

/-- The constant of the error bound of this file is not negative. -/
private theorem drsvdConst_nonneg_aux {L B H ε h : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hε₀ : 0 ≤ ε) (hh : 0 ≤ h) :
    0 ≤ (2 * bugC₁ L H + 1) * ε + (2 * bugC₂ L B H + 10 * L * B) * h := by
  have h1 := bugC₁_nonneg hL hH
  have h2 := bugC₂_nonneg hL hB hH
  positivity

/-- **Local error of one step of a uniform grid.** Under the hypotheses of the run theorem on
`F` and `A` (`DLRAProblem`, joint continuity and `FactoredNormalBoundOn` at `r` and at `k`
columns on the tube of radius `ρ` around `A` over `[t₀, t₀ + N h]`), a DRSVD step with
truncation to rank `r` over `[t₀ + j h, t₀ + (j + 1) h]`, `j < N`, `h ≤ H`, `k ≤ l`, whose start
value `Z₀` has rank at most `r` and satisfies `‖Z₀ - A (t₀ + j h)‖ + 3 B h < ρ` has local error
`h ((2 c₁ + 1) ε + (2 c₂ + 10 L B) h)` with `c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`. -/
theorem stepRel.hasLocalError_uniformGrid {j : ℕ} {Z₀ Z₁ : Matrix m n ℝ}
    (hstep : stepRel F r k l (t₀ + j * h) (t₀ + (j + 1) * h) Z₀ Z₁) (hkl : k ≤ l)
    (hZ₀ : Z₀.rank ≤ r) (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : ∀ s ∈ ({r, k} : Set ℕ), FactoredNormalBoundOn F s (tubeSet A t₀ (t₀ + N * h) ρ) ε)
    (hε₀ : 0 ≤ ε) (hh : 0 ≤ h) (hhH : h ≤ H) (hj : j < N)
    (hnear : ‖Z₀ - A (t₀ + j * h)‖ + 3 * B * h < ρ) :
    HasLocalError F (t₀ + j * h) (t₀ + (j + 1) * h) Z₀ Z₁
      (h * ((2 * bugC₁ L H + 1) * ε + (2 * bugC₂ L B H + 10 * L * B) * h)) := by
  obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hj
  have hloc := hstep.hasLocalError_of_tube hkl hZ₀ hε hε₀ hP.lipschitz hP.L_nonneg hP.bounded
    hP.B_nonneg hc hP.sol.cont ha hb h01 (hsub.le.trans hhH) (hP.sol.mono ha hb)
    (by rw [hsub]; exact hnear)
  rwa [hsub] at hloc

/-- **Every run of the DRSVD integrator satisfies the robust error bound.** Let `A` solve
`Y' = F(t, Y)` on `[t₀, t₀ + N h]`, and let `F` be `L`-Lipschitz and bounded by `B` on the tube
of radius `ρ` around `A` (`DLRAProblem`), jointly continuous there, with normal component at most
`ε` at the factored matrices of the tube with `r` and with `k` columns
(`FactoredNormalBoundOn`), `k ≤ l`. Let `Y 0, …, Y N` be a run of the DRSVD integrator with
truncation to rank `r`, step size `0 ≤ h ≤ H`, `N h ≤ T`, `rank (Y 0) ≤ r` and
`‖Y 0 - A t₀‖ ≤ δ`. If the bound below is smaller than the tube radius with a margin of `3 B h`,
then for all `n ≤ N`

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} ((2 c₁ + 1) ε + (2 c₂ + 10 L B) h)`,

`c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`. The constants do not depend on the singular values of the
`Y n`; the sketch bases enter only through the normal bound at `k` columns, which is a
hypothesis. Nothing is assumed about `F` outside the tube. The rank of the
values is carried along as an invariant (`IsRun.adm_and_norm_sub_le_of_tube_uniformGrid`): a
step may start from a matrix of rank up to `k`, but the bound on the truncation needs rank at
most `r`. -/
theorem IsRun.norm_sub_le {Y : ℕ → Matrix m n ℝ}
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : ∀ s ∈ ({r, k} : Set ℕ), FactoredNormalBoundOn F s (tubeSet A t₀ (t₀ + N * h) ρ) ε)
    (hε₀ : 0 ≤ ε) (hkl : k ≤ l) (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) *
      ((2 * bugC₁ L H + 1) * ε + (2 * bugC₂ L B H + 10 * L * B) * h) + 3 * B * h < ρ)
    (hY : IsRun (stepRel F r k l) (uniformGrid t₀ h) N Y) (hY0 : (Y 0).rank ≤ r)
    (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) *
      ((2 * bugC₁ L H + 1) * ε + (2 * bugC₂ L B H + 10 * L * B) * h) := by
  have hc₀ := drsvdConst_nonneg_aux hP.L_nonneg hP.B_nonneg (hh.trans hhH) hε₀ hh
  have hBh : 0 ≤ B * h := mul_nonneg hP.B_nonneg hh
  have hbd := hY.adm_and_norm_sub_le_of_tube_uniformGrid (Adm := fun _ Z => Z.rank ≤ r)
    (T := T) (δ₀ := δ) (c := (2 * bugC₁ L H + 1) * ε + (2 * bugC₂ L B H + 10 * L * B) * h) hP hc
    (fun _ _ _ _ _ _ hstep => hstep.rank_le)
    (fun j hj Z₀ Z₁ hZ₀ hnear hstep =>
      -- the local error of a step that starts within the error bound of `A`
      hstep.hasLocalError_uniformGrid hkl hZ₀ hP hc hε hε₀ hh hhH hj (by linarith))
    hc₀ hY0 hδ hNT (by linarith)
  exact fun n hn => (hbd n hn).2

/-- **Existence and robust error bound for the DRSVD integrator.** Let `A` solve `Y' = F(t, Y)`
on `[t₀, t₀ + N h]`, and let `F` be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ`
around `A` (`DLRAProblem`), jointly continuous there, with normal component at most `ε` at the
factored matrices of the tube with `r` and with `k` columns (`FactoredNormalBoundOn`). Let
`r ≤ k ≤ l`, `k ≤ n`, `l ≤ m`, let the step size satisfy `0 ≤ h ≤ H` and `N h ≤ T`, and let `Y₀`
be a start value of rank at most `r` with `‖Y₀ - A t₀‖ ≤ δ`. If

  `e^{L T} δ + T e^{L T} ((2 c₁ + 1) ε + (2 c₂ + 10 L B) h) + 3 B h < ρ`,

`c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`, then the integrator can be run from `Y₀`: there are
`Y 0 = Y₀, Y 1, …, Y N`, each obtained from the previous one by a DRSVD step of size `h` with an
augmented sketch of `k` columns and a range basis of `l` columns, followed by a best
approximation of rank at most `r`, all of rank at most `r`, with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} ((2 c₁ + 1) ε + (2 c₂ + 10 L B) h)`

for all `n ≤ N`. The constants are independent of the singular values of the matrices `Y n`; the
sketch bases enter only through the normal bound at `k` columns, which is a hypothesis. Nothing
is assumed about `F` outside the tube. No truncation tolerance
appears.

This is `StepMethod.IsTubeLocal.exists_run_norm_sub_le` for the tube-local method
`MatrixDRSVD.isTubeLocal_stepRel`. The bound itself holds for every run
(`MatrixDRSVD.IsRun.norm_sub_le`). -/
theorem exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : ∀ s ∈ ({r, k} : Set ℕ), FactoredNormalBoundOn F s (tubeSet A t₀ (t₀ + N * h) ρ) ε)
    (hε₀ : 0 ≤ ε) (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T) (hrk : r ≤ k)
    (hkn : k ≤ Fintype.card n) (hkl : k ≤ l) (hlm : l ≤ Fintype.card m)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) *
      ((2 * bugC₁ L H + 1) * ε + (2 * bugC₂ L B H + 10 * L * B) * h) + 3 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r k l) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ +
        T * Real.exp (L * T) * ((2 * bugC₁ L H + 1) * ε + (2 * bugC₂ L B H + 10 * L * B) * h) := by
  have hc₀ := drsvdConst_nonneg_aux hP.L_nonneg hP.B_nonneg (hh.trans hhH) hε₀ hh
  have hBh : 0 ≤ B * h := mul_nonneg hP.B_nonneg hh
  refine (isTubeLocal_stepRel hrk hkn hkl hlm).exists_run_norm_sub_le (by norm_num) hP hc
    (fun j hj Z₀ Z₁ hZ₀ hnear hstep => ?_) hc₀ hh hNT hY₀ hδ hsmall
  -- the local error of a step that starts within the error bound of `A`
  exact hstep.hasLocalError_uniformGrid hkl hZ₀ hP hc hε hε₀ hh hhH hj (by linarith)

end Error

/-! ### Examples: a nonlinear field and a linear field -/

section Examples

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r k l : ℕ}

/-- **Non-vacuity of the existence and error theorem.** The radial field
`F(t, Y) = Y / max ‖Y‖ 1` is `2`-Lipschitz, bounded by `1`, and has no normal component at any
factored matrix, whatever the number of columns (`MatrixKSL.radial_normal_eq_zero`), so `ε = 0`
at `r` and at `k` columns. For every solution `A` of `Y' = F(t, Y)` on `[t₀, t₀ + N h]`, every
`r ≤ k ≤ l` with `k ≤ n`, `l ≤ m`, and every start value `Y₀` of rank at most `r` with
`‖Y₀ - A t₀‖ ≤ δ`, the DRSVD integrator can be run with any step size `0 ≤ h ≤ H`, and the run
stays within `e^{2 T} δ + T e^{2 T} (2 bugC₂ 2 1 H + 20) h` of `A`. No smallness condition
remains, because the field is Lipschitz and bounded everywhere and the tube radius can be chosen
as large as needed. -/
example (hrk : r ≤ k) (hkn : k ≤ Fintype.card n) (hkl : k ≤ l) (hlm : l ≤ Fintype.card m)
    {A : ℝ → Matrix m n ℝ} {t₀ h H T δ : ℝ} {N : ℕ}
    (hA : ODESolution (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) A t₀ (t₀ + N * h))
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r)
    (hδ : ‖Y₀ - A t₀‖ ≤ δ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (stepRel (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) r k l)
        (uniformGrid t₀ h) N Y ∧
      ∀ j ≤ N, (Y j).rank ≤ r ∧ ‖Y j - A (t₀ + j * h)‖ ≤
        Real.exp (2 * T) * δ + T * Real.exp (2 * T) *
          ((2 * bugC₁ 2 H + 1) * 0 + (2 * bugC₂ 2 1 H + 10 * 2 * 1) * h) := by
  have hcont : Continuous fun Z : Matrix m n ℝ => MatrixKSL.radial Z :=
    (LipschitzWith.of_dist_le' (K := 2) fun X Y => by
      rw [dist_eq_norm, dist_eq_norm]; exact MatrixKSL.norm_radial_sub_le X Y).continuous
  exact exists_run_norm_sub_le
    (F := fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) (A := A) (L := 2) (B := 1)
    (ε := 0)
    (ρ := Real.exp (2 * T) * δ + T * Real.exp (2 * T) *
      ((2 * bugC₁ 2 H + 1) * 0 + (2 * bugC₂ 2 1 H + 10 * 2 * 1) * h) + 3 * 1 * h + 1)
    ⟨hA, by norm_num, by norm_num, fun _ _ X Y _ _ => MatrixKSL.norm_radial_sub_le X Y,
      fun _ _ X _ => MatrixKSL.norm_radial_le X⟩
    (hcont.comp continuous_snd).continuousOn
    (fun _ _ t U V S hU hV _ => MatrixKSL.radial_normal_eq_zero t U S V hU hV) le_rfl hh hhH hNT
    hrk hkn hkl hlm hY₀ hδ (lt_add_one _)

/-- **Non-vacuity for a field that is not bounded, and for every run.** The linear field
`F(t, Y) = M Y + Y Nᵀ + G` with a stationary point `C` (`M C + C Nᵀ + G = 0`) is Lipschitz with
constant `‖M‖ + ‖N‖` but not bounded. On the tube of radius `ρ` around the constant solution
`A(t) = C` it is bounded by `(‖M‖ + ‖N‖) ρ`, and its normal component at the factored matrices
is at most `‖G‖` for every number of columns (`dlraProblem_linear`,
`factoredNormalBoundOn_linear`). Hence a run of the DRSVD integrator exists from every `Y₀` of
rank at most `r`, and under the smallness condition every such run from a `Y₀` near `C`
satisfies the error bound with `ε = ‖G‖`, whatever sketches it uses. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) (hrk : r ≤ k) (hkn : k ≤ Fintype.card n) (hkl : k ≤ l)
    (hlm : l ≤ Fintype.card m) (t₀ : ℝ) {ρ T H δ h : ℝ} {K : ℕ} (hρ : 0 ≤ ρ) (hh : 0 ≤ h)
    (hhH : h ≤ H) (hKT : K * h ≤ T) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r)
    (hδ : ‖Y₀ - C‖ ≤ δ)
    (hsmall : Real.exp ((‖M‖ + ‖N‖) * T) * δ + T * Real.exp ((‖M‖ + ‖N‖) * T) *
      ((2 * bugC₁ (‖M‖ + ‖N‖) H + 1) * ‖G‖ + (2 * bugC₂ (‖M‖ + ‖N‖) ((‖M‖ + ‖N‖) * ρ) H +
        10 * (‖M‖ + ‖N‖) * ((‖M‖ + ‖N‖) * ρ)) * h) + 3 * ((‖M‖ + ‖N‖) * ρ) * h < ρ) :
    (∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (stepRel (fun (_ : ℝ) (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G) r k l)
        (uniformGrid t₀ h) K Y) ∧
    ∀ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ →
      IsRun (stepRel (fun (_ : ℝ) (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G) r k l)
        (uniformGrid t₀ h) K Y →
      ∀ j ≤ K, ‖Y j - C‖ ≤ Real.exp ((‖M‖ + ‖N‖) * T) * δ +
        T * Real.exp ((‖M‖ + ‖N‖) * T) * ((2 * bugC₁ (‖M‖ + ‖N‖) H + 1) * ‖G‖ +
          (2 * bugC₂ (‖M‖ + ‖N‖) ((‖M‖ + ‖N‖) * ρ) H +
            10 * (‖M‖ + ‖N‖) * ((‖M‖ + ‖N‖) * ρ)) * h) := by
  refine ⟨exists_run (isLipschitzField_linear M N G) (isGrid_uniformGrid hh K)
    (fun _ => continuousOn_const) hrk hkn hkl hlm hY₀, fun Y hY0 hY => ?_⟩
  exact IsRun.norm_sub_le (A := fun _ => C) (dlraProblem_linear M N G C hC _ _ hρ)
    (continuous_uncurry_linear M N G).continuousOn
    (fun s _ => factoredNormalBoundOn_linear M N G _) (norm_nonneg G) hkl hh hhH hKT hsmall hY
    (by rw [hY0]; exact hY₀) (by rw [hY0]; exact hδ)

end Examples

end MatrixDRSVD

end LeanDLRA
