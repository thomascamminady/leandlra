import LeanDLRA.Tensor.Tucker.BUGStep
import LeanDLRA.Integrators.Method
import LeanDLRA.Foundations.ConjugatedField

/-!
# Runs of the Tucker BUG integrator: existence and error bound

This file closes the theory of the basis-update & Galerkin (BUG) integrator for tensors in Tucker
format with fixed multilinear rank `r` (Ceruti and Lubich, arXiv:2010.02022, §5), for a
differential equation `Y' = F(t, Y)` on `Tensor ι` with `d` modes: the integrator can be run, and
every run stays close to the exact solution. The step relation `TuckerBUG.stepRel F r` and its
local error are in `LeanDLRA/Tensor/Tucker/BUGStep.lean`.

**Setting.** Let `A` be a solution of `Y' = F(t, Y)` on `[t₀, t₀ + N h]`. The field `F` is only
assumed to be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around `A`
(`DLRAProblem F A t₀ (t₀ + N h) ρ L B`), jointly continuous there, and to have a normal part of
size at most `ε` at the normal triples of the tube (`NormalBoundOn F (TuckerBUG.normalTriples r)
_ ε`): for every mode `i`, every tensor `Y` fixed by a mode projector `P` of rank `r i` and by a
co-range projector `Q` of rank `r i`, `‖(1 - P) ((1 - Q) F(t, Y))‖ ≤ ε`. Nothing is assumed about
`F` outside the tube.

**Result** (`TuckerBUG.exists_run_norm_sub_le`). Let `r i ≤ card (ι i)` and `r i` be at most the
number of multi-indices of the modes other than `i`. For every start value `Y₀` of multilinear
rank at most `r` with `‖Y₀ - A t₀‖ ≤ δ` there are tensors `Y 0 = Y₀, Y 1, …, Y N`, each obtained
from the previous one by a Tucker BUG step of size `h ≤ H`, all of multilinear rank at most `r`,
with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (c₁ ε + c₂ h)`

for all `n ≤ N`, where `N h ≤ T`, `c₁ = tuckerC₁ d L H` and `c₂ = tuckerC₂ d L B H`
(arXiv:2010.02022, Theorem 7, for a field that is Lipschitz and bounded near the exact solution
only, with the steps shown to exist). The constants do not depend on the singular values of the
unfoldings of the `Y n`. The only further hypothesis is that the right-hand side plus
`(d + 2) B h` is less than `ρ`. The same bound holds for every run (`TuckerBUG.IsRun.norm_sub_le`).

## Main results

* `TuckerBUG.exists_stepRel`: a step exists from every tensor of multilinear rank at most `r`,
  for every Lipschitz field that is continuous in time on the step interval.
* `TuckerBUG.exists_run`: for a field that is Lipschitz everywhere there is a run on every grid.
* `TuckerBUG.isTubeLocal_stepRel`: the integrator is a tube-local method
  (`StepMethod.IsTubeLocal`) with the tensors of multilinear rank at most `r` as admissible
  values and margin constant `d + 2`.
* `TuckerBUG.IsRun.norm_sub_le`: every run satisfies the error bound.
* `TuckerBUG.exists_run_norm_sub_le`: a run exists, has multilinear rank at most `r` and
  satisfies the error bound.

## Implementation notes

Existence of a step: the co-range bases come from the rank of the unfoldings of `Y₀`
(`Tensor.ModeRankLE.exists_coRange`); the K-step of mode `i` stays in the range of its co-range
projector, so its result has a mode-`i` unfolding of rank at most `r i`, and a new mode basis
with `r i` columns that fixes it exists (`Tensor.exists_modeProj_eq_self`); the K-steps and the
Galerkin step are differential equations with the field `F` followed by a projector, whose
solutions exist by `MatrixBUG.exists_odeSolution_conj_of_lipschitz`. For two modes the margin
constant `d + 2 = 4` is that of the matrix BUG integrator.

## References

* G. Ceruti, Ch. Lubich, *An unconventional robust integrator for dynamical low-rank
  approximation*, arXiv:2010.02022 (BIT Numer. Math. 2022), §5, Theorem 7.
-/

open Set
open scoped Matrix

namespace LeanDLRA

namespace TuckerBUG

open Tensor

/-! ### Existence of steps and runs, and the integrator as a tube-local method -/

section Exists

variable {d : ℕ} {ι : Fin d → Type*} [∀ i, Fintype (ι i)] {r : Fin d → ℕ}
  {F : ℝ → Tensor ι → Tensor ι} {L : ℝ}

/-- **A Tucker BUG step exists from every tensor of multilinear rank at most `r`.** If `F` is
Lipschitz and continuous in time on `[t₀, t₁]`, `r i ≤ card (ι i)` and `r i` is at most the
number of multi-indices of the modes other than `i`, then every `Y₀` of multilinear rank at most
`r` has a successor under `TuckerBUG.stepRel F r`. The field need not be bounded. -/
theorem exists_stepRel (hF : IsLipschitzField F L) {t₀ t₁ : ℝ}
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁)
    (hr : ∀ i, r i ≤ Fintype.card (ι i))
    (hr' : ∀ i, r i ≤ Fintype.card (∀ k : {k : Fin d // k ≠ i}, ι k))
    {Y₀ : Tensor ι} (hY₀ : ModeRankLE r Y₀) : ∃ Y₁, stepRel F r t₀ t₁ Y₀ Y₁ := by
  -- co-range bases that fix the start value
  choose V₀ hV₀ hVY using fun i => hY₀.exists_coRange i (hr' i)
  -- the K-steps
  choose YK hK hK₀ using fun i => MatrixBUG.exists_odeSolution_conj_of_lipschitz hF hc
    (ContinuousLinearMap.id ℝ (Tensor ι)) (actOn (· ≠ i) (V₀ i * (V₀ i)ᵀ))
    (f := fun t x => actOn (· ≠ i) (V₀ i * (V₀ i)ᵀ) (F t x)) (fun t x => rfl) h01 Y₀
  -- the results of the K-steps stay in the ranges of the co-range projectors
  have hQ : ∀ i, actOn (· ≠ i) (V₀ i * (V₀ i)ᵀ) (YK i t₁) = YK i t₁ := fun i =>
    (hK i).galerkin_mem_range (isOrthProj_coRangeProj i (hV₀ i)) (by rw [hK₀ i]; exact hVY i)
      t₁ ⟨h01, le_rfl⟩
  -- new mode bases that fix the results of the K-steps
  choose U₁ hU₁ hcap using fun i => exists_modeProj_eq_self i (by
    have h := rank_unfold_ne_le_of_actOn_eq_self i (hQ i)
    rw [rank_unfold_ne] at h
    simpa using h) (hr i)
  -- the Galerkin step
  obtain ⟨YS, hS, hS₀⟩ := MatrixBUG.exists_odeSolution_conj_of_lipschitz hF hc
    (ContinuousLinearMap.id ℝ (Tensor ι)) (modeProd fun i => modeProj i (U₁ i))
    (f := fun t x => modeProd (fun i => modeProj i (U₁ i)) (F t x)) (fun t x => rfl) h01
    (modeProd (fun i => modeProj i (U₁ i)) Y₀)
  exact ⟨_, V₀, U₁, YK, YS, hV₀, hVY, hU₁, hK, hK₀, hcap, hS, hS₀, rfl⟩

/-- All values of a run of the Tucker BUG integrator have multilinear rank at most `r`, provided
the start value has. -/
theorem IsRun.modeRankLE {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → Tensor ι}
    (hY : IsRun (stepRel F r) τ N Y) (h0 : ModeRankLE r (Y 0)) : ∀ n ≤ N, ModeRankLE r (Y n)
  | 0, _ => h0
  | n + 1, hn => (hY.step n hn).modeRankLE (hY.grid.mono n hn)

/-- **Runs of the Tucker BUG integrator exist.** If `F` is Lipschitz (globally) and continuous in
time on `[τ 0, τ N]` and `r` satisfies the conditions of `TuckerBUG.exists_stepRel`, then on the
grid `τ` there is a run of `N` steps from every start value of multilinear rank at most `r`. -/
theorem exists_run (hF : IsLipschitzField F L) {τ : ℕ → ℝ} {N : ℕ} (hτ : IsGrid τ N)
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc (τ 0) (τ N)))
    (hr : ∀ i, r i ≤ Fintype.card (ι i))
    (hr' : ∀ i, r i ≤ Fintype.card (∀ k : {k : Fin d // k ≠ i}, ι k))
    {Y₀ : Tensor ι} (hY₀ : ModeRankLE r Y₀) :
    ∃ Y : ℕ → Tensor ι, Y 0 = Y₀ ∧ IsRun (stepRel F r) τ N Y := by
  refine exists_isRun hτ Y₀ fun n hn Y hY0 hY => ?_
  have hsub : Icc (τ n) (τ (n + 1)) ⊆ Icc (τ 0) (τ N) :=
    Icc_subset_Icc (hτ.le_of_le n.zero_le hn.le) (hτ.le_of_le (Nat.succ_le_of_lt hn) le_rfl)
  exact exists_stepRel hF (fun Z => (hc Z).mono hsub) (hτ.mono n hn) hr hr'
    (IsRun.modeRankLE hY (by rw [hY0]; exact hY₀) n le_rfl)

/-- **The Tucker BUG integrator is a tube-local method** (`StepMethod.IsTubeLocal`), with the
tensors of multilinear rank at most `r` as admissible values and margin constant `d + 2`:

* a step exists from every tensor of multilinear rank at most `r`, for every globally Lipschitz
  field that is continuous in time on the step interval (`TuckerBUG.exists_stepRel`);
* the result of a step has multilinear rank at most `r` (`TuckerBUG.stepRel.modeRankLE`);
* if `‖Y₀ - A t₀‖ + (d + 2) B (t₁ - t₀) < ρ`, a step from `Y₀` of the extended field
  `tubeExt F A a b ρ` is a step of `F` (`TuckerBUG.stepRel_tubeExt_iff_of_near`).

With the local error `TuckerBUG.stepRel.hasLocalError_of_tube` this is all that
`StepMethod.IsTubeLocal.exists_run_norm_sub_le` needs. -/
theorem isTubeLocal_stepRel (hr : ∀ i, r i ≤ Fintype.card (ι i))
    (hr' : ∀ i, r i ≤ Fintype.card (∀ k : {k : Fin d // k ≠ i}, ι k)) :
    StepMethod.IsTubeLocal (fun G : ℝ → Tensor ι → Tensor ι => stepRel G r) (ModeRankLE r)
      (d + 2) where
  exists_step := fun hG hc h01 hY₀ => exists_stepRel hG hc h01 hr hr' hY₀
  adm_of_step := fun h01 _ hstep => hstep.modeRankLE h01
  step_of_tubeExt := fun hFB hB ha hb h01 hA _ hsmall hstep =>
    (stepRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 hstep

end Exists

/-! ### The error bound, and existence of a run near the exact solution -/

section Error

variable {d : ℕ} {ι : Fin d → Type*} [∀ i, Fintype (ι i)] {r : Fin d → ℕ}
  {F : ℝ → Tensor ι → Tensor ι} {A : ℝ → Tensor ι} {t₀ h H T ρ L B ε δ : ℝ} {N : ℕ}

/-- **Local error of one step of a uniform grid.** Under the hypotheses of the run theorem on
`F` and `A` (`DLRAProblem`, and `NormalBoundOn` at the normal triples on the tube of radius `ρ`
around `A` over `[t₀, t₀ + N h]`), a Tucker BUG step over `[t₀ + j h, t₀ + (j + 1) h]`, `j < N`,
`h ≤ H`, whose start value `Z₀` satisfies `‖Z₀ - A (t₀ + j h)‖ + (d + 2) B h < ρ` has local
error `h (c₁ ε + c₂ h)` with `c₁ = tuckerC₁ d L H`, `c₂ = tuckerC₂ d L B H`. -/
theorem stepRel.hasLocalError_uniformGrid {j : ℕ} {Z₀ Z₁ : Tensor ι}
    (hstep : stepRel F r (t₀ + j * h) (t₀ + (j + 1) * h) Z₀ Z₁)
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hε : NormalBoundOn F (normalTriples r) (tubeSet A t₀ (t₀ + N * h) ρ) ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hj : j < N)
    (hnear : ‖Z₀ - A (t₀ + j * h)‖ + (d + 2) * B * h < ρ) :
    HasLocalError F (t₀ + j * h) (t₀ + (j + 1) * h) Z₀ Z₁
      (h * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h)) := by
  obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hj
  have hloc := hstep.hasLocalError_of_tube hε hP.lipschitz hP.L_nonneg hP.bounded hP.B_nonneg
    ha hb h01 (hsub.le.trans hhH) (hP.sol.mono ha hb) (by rw [hsub]; exact hnear)
  rwa [hsub] at hloc

/-- **Every run of the Tucker BUG integrator satisfies the robust error bound.** Let `A` solve
`Y' = F(t, Y)` on `[t₀, t₀ + N h]`, and let `F` be `L`-Lipschitz and bounded by `B` on the tube
of radius `ρ` around `A` (`DLRAProblem`), jointly continuous there, with normal part at most `ε`
at the normal triples of the tube (`NormalBoundOn F (TuckerBUG.normalTriples r) _ ε`). Let
`Y 0, …, Y N` be a run of the integrator with step size `0 ≤ h ≤ H`, `N h ≤ T`, and
`‖Y 0 - A t₀‖ ≤ δ`. If the bound below is smaller than the tube radius with a margin of
`(d + 2) B h`, then for all `n ≤ N`

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (c₁ ε + c₂ h)`,

`c₁ = tuckerC₁ d L H`, `c₂ = tuckerC₂ d L B H`. Nothing is assumed about `F` outside the tube,
and no exact solutions started at the numerical values have to be supplied (compare
`tucker_global_error_le_of_tube`). -/
theorem IsRun.norm_sub_le {Y : ℕ → Tensor ι}
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : NormalBoundOn F (normalTriples r) (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hsmall : Real.exp (L * T) * δ +
      T * Real.exp (L * T) * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) + (d + 2) * B * h < ρ)
    (hY : IsRun (stepRel F r) (uniformGrid t₀ h) N Y) (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ +
      T * Real.exp (L * T) * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) := by
  have hH : 0 ≤ H := hh.trans hhH
  have hc₀ : 0 ≤ tuckerC₁ d L H * ε + tuckerC₂ d L B H * h :=
    add_nonneg (mul_nonneg (tuckerC₁_nonneg d hP.L_nonneg hH) hε₀)
      (mul_nonneg (tuckerC₂_nonneg d hP.L_nonneg hP.B_nonneg hH) hh)
  have hdBh : 0 ≤ (d : ℝ) * (B * h) := mul_nonneg (Nat.cast_nonneg d) (mul_nonneg hP.B_nonneg hh)
  refine hY.norm_sub_le_of_tube_uniformGrid (T := T) (δ₀ := δ)
    (c := tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) hP hc
    (fun j hj Z₀ Z₁ hnear hstep => ?_) hc₀ hδ hNT (by linarith)
  -- the local error of a step that starts within the error bound of `A`
  exact hstep.hasLocalError_uniformGrid hP hε hh hhH hj (by linarith)

/-- **Existence and robust error bound for the Tucker BUG integrator** (arXiv:2010.02022,
Theorem 7, for a field that is Lipschitz and bounded near the exact solution only). Let `A` solve
`Y' = F(t, Y)` on `[t₀, t₀ + N h]`, and let `F` be `L`-Lipschitz and bounded by `B` on the tube of
radius `ρ` around `A` (`DLRAProblem`), jointly continuous there, with normal part at most `ε` at
the normal triples of the tube (`NormalBoundOn F (TuckerBUG.normalTriples r) _ ε`). Let
`r i ≤ card (ι i)` and `r i` be at most the number of multi-indices of the modes other than `i`,
let the step size satisfy `0 ≤ h ≤ H` and `N h ≤ T`, and let `Y₀` be a start value of
multilinear rank at most `r` with `‖Y₀ - A t₀‖ ≤ δ`. If

  `e^{L T} δ + T e^{L T} (c₁ ε + c₂ h) + (d + 2) B h < ρ`,

`c₁ = tuckerC₁ d L H`, `c₂ = tuckerC₂ d L B H`, then the integrator can be run from `Y₀`: there
are `Y 0 = Y₀, Y 1, …, Y N`, each obtained from the previous one by a Tucker BUG step of size
`h`, all of multilinear rank at most `r`, with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (c₁ ε + c₂ h)` for all `n ≤ N`.

This is `StepMethod.IsTubeLocal.exists_run_norm_sub_le` for the tube-local method
`TuckerBUG.isTubeLocal_stepRel`. The bound itself holds for every run
(`TuckerBUG.IsRun.norm_sub_le`). -/
theorem exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : NormalBoundOn F (normalTriples r) (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hr : ∀ i, r i ≤ Fintype.card (ι i))
    (hr' : ∀ i, r i ≤ Fintype.card (∀ k : {k : Fin d // k ≠ i}, ι k))
    {Y₀ : Tensor ι} (hY₀ : ModeRankLE r Y₀) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ +
      T * Real.exp (L * T) * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) + (d + 2) * B * h < ρ) :
    ∃ Y : ℕ → Tensor ι, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, ModeRankLE r (Y n) ∧ ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * δ +
          T * Real.exp (L * T) * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) := by
  have hH : 0 ≤ H := hh.trans hhH
  have hc₀ : 0 ≤ tuckerC₁ d L H * ε + tuckerC₂ d L B H * h :=
    add_nonneg (mul_nonneg (tuckerC₁_nonneg d hP.L_nonneg hH) hε₀)
      (mul_nonneg (tuckerC₂_nonneg d hP.L_nonneg hP.B_nonneg hH) hh)
  have hd : (2 : ℝ) ≤ d + 2 := by have := Nat.cast_nonneg (α := ℝ) d; linarith
  refine (isTubeLocal_stepRel hr hr').exists_run_norm_sub_le hd hP hc
    (fun j hj Z₀ Z₁ _ hnear hstep => ?_) hc₀ hh hNT hY₀ hδ hsmall
  -- the local error of a step that starts within the error bound of `A`
  exact hstep.hasLocalError_uniformGrid hP hε hh hhH hj (by linarith)

end Error

/-! ### Example: the linear field `F(t, Y) = Y` near the zero solution -/

section Examples

variable {d : ℕ} {ι : Fin d → Type*} [∀ i, Fintype (ι i)] {r : Fin d → ℕ}

/-- **Non-vacuity of the existence and error theorem.** The field `F(t, Y) = Y` is `1`-Lipschitz
and not bounded; on the tube of radius `ρ` around its solution `A = 0` it is bounded by `ρ`. Its
normal part vanishes at every normal triple, because the tensor of a normal triple is fixed by
the co-range projector, so `ε = 0` while the field has size up to `ρ`. Hence, under the
smallness condition, the Tucker BUG integrator can be run from every `Y₀` of multilinear rank at
most `r` with `‖Y₀‖ ≤ δ`, and the run stays within `e^{T} δ + T e^{T} c₂ h` of `0`,
`c₂ = tuckerC₂ d 1 ρ H`. -/
example (hr : ∀ i, r i ≤ Fintype.card (ι i))
    (hr' : ∀ i, r i ≤ Fintype.card (∀ k : {k : Fin d // k ≠ i}, ι k)) {t₀ h H T δ ρ : ℝ}
    {N : ℕ} (hρ : 0 ≤ ρ) (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T) {Y₀ : Tensor ι}
    (hY₀ : ModeRankLE r Y₀) (hδ : ‖Y₀‖ ≤ δ)
    (hsmall : Real.exp (1 * T) * δ +
      T * Real.exp (1 * T) * (tuckerC₁ d 1 H * 0 + tuckerC₂ d 1 ρ H * h) + (d + 2) * ρ * h < ρ) :
    ∃ Y : ℕ → Tensor ι, Y 0 = Y₀ ∧
      IsRun (stepRel (fun (_ : ℝ) (Z : Tensor ι) => Z) r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, ModeRankLE r (Y n) ∧ ‖Y n‖ ≤ Real.exp (1 * T) * δ +
        T * Real.exp (1 * T) * (tuckerC₁ d 1 H * 0 + tuckerC₂ d 1 ρ H * h) := by
  have hA : ODESolution (fun (_ : ℝ) (Z : Tensor ι) => Z) (fun _ => 0) t₀ (t₀ + N * h) :=
    ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) (0 : Tensor ι)⟩
  have hP : DLRAProblem (fun (_ : ℝ) (Z : Tensor ι) => Z) (fun _ => 0) t₀ (t₀ + N * h) ρ 1 ρ :=
    ⟨hA, zero_le_one, hρ, fun _ _ X Y _ _ => by simp, fun _ _ X hX => by simpa using hX⟩
  have hε : NormalBoundOn (fun (_ : ℝ) (Z : Tensor ι) => Z) (normalTriples r)
      (tubeSet (fun _ => 0) t₀ (t₀ + N * h) ρ) 0 := by
    intro t P Q Y hT _
    obtain ⟨i, U, V, Y', -, -, -, hVY, he⟩ := hT
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    simp [hVY]
  obtain ⟨Y, hY0, hY, hbd⟩ := exists_run_norm_sub_le hP continuous_snd.continuousOn hε le_rfl hh
    hhH hNT hr hr' hY₀ (by simpa using hδ) hsmall
  exact ⟨Y, hY0, hY, fun n hn => ⟨(hbd n hn).1, by simpa using (hbd n hn).2⟩⟩

end Examples

end TuckerBUG

end LeanDLRA
