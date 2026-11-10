import LeanDLRA.Analysis.Defs
import Mathlib.Analysis.ODE.Gronwall

/-!
# Definitions: time grids, local errors, step relations and runs

The vocabulary of the integrator layer (`Integrators/`). A time integrator advances an
approximation `Y n ≈ A (τ n)` of the solution of `y' = F(t, y)` along a grid of times
`τ 0 ≤ τ 1 ≤ ⋯ ≤ τ N`. Its global error is controlled by two independent ingredients:

* the **local error** of the method: how far one step from `Y n` lands from the exact solution
  started at `Y n` (`HasLocalError`, for a method `StepRel.HasLocalErrorOn`);
* the **stability of the exact flow**: how the exact solutions started at the numerical values
  (the exact-flow fan, `IsExactFan`) propagate a deviation from the reference solution `A`
  (`FanStable`).

A method is described by the relation between the start and the result of one step
(`StepRel`), because the low-rank integrators involve choices (bases from QR or SVD
factorizations are not unique); a numerical solution is a run of the relation on a grid
(`IsRun`).

## Main definitions

* `LeanDLRA.IsGrid τ N`: `τ 0 ≤ τ 1 ≤ ⋯ ≤ τ N`; `LeanDLRA.uniformGrid t₀ h n = t₀ + n h`.
* `LeanDLRA.IsExactFan F τ N Y Φ`: `Φ n` solves the ODE on `[τ n, τ (n + 1)]` with
  `Φ n (τ n) = Y n`.
* `LeanDLRA.FanStable A τ N Φ a`: `‖Φ n (τ (n+1)) - A (τ (n+1))‖ ≤ a n ‖Φ n (τ n) - A (τ n)‖`.
* `LeanDLRA.HasLocalError F t₀ t₁ Y₀ Y₁ δ`: `‖Y₁ - Φ t₁‖ ≤ δ` for every exact solution `Φ` with
  `Φ t₀ = Y₀`.
* `LeanDLRA.StepRel E`: one-step methods as relations `M t₀ t₁ Y₀ Y₁`;
  `LeanDLRA.IsRun M τ N Y`: `Y` is a run of `M` on the grid `τ`.
* `LeanDLRA.StepRel.HasLocalErrorOn`, `LeanDLRA.StepRel.ConservesUpTo`,
  `LeanDLRA.StepRel.IsExactFor`: local error, conservation up to a tolerance, and exactness of a
  method.

## Main results

* `LeanDLRA.isExactFan_uniformGrid_iff`, `LeanDLRA.isRun_uniformGrid_iff`: on the uniform grid,
  the fan and the run are the hypotheses `∀ n < N, …` of `lady_windermere` and of the global
  error theorems, written with `t₀ + n * h`.
* `LeanDLRA.IsExactFan.norm_sub_le_of_hasLocalError`, `LeanDLRA.IsRun.hasLocalError`: a run of a
  method with local error `δ` has the local errors `‖Y (n+1) - Φ n (τ (n+1))‖ ≤ δ` along any fan.
* `LeanDLRA.StepRel.HasLocalErrorOn.isExactFor`: a method with local error `0` is exact.

## Implementation notes

Step relations contain the algorithm only; analysis constants (Lipschitz constants,
normal-component bounds) are hypotheses of the theorems. The predicates on step relations
constrain forward steps `t₀ ≤ t₁` only: the substeps of a method are specified by ODE solutions
on `[t₀, t₁]`, which say nothing when `t₁ < t₀`.
-/

open Set

namespace LeanDLRA

/-! ### Time grids -/

section Grid

/-- A **time grid** with `N` steps: times `τ 0 ≤ τ 1 ≤ ⋯ ≤ τ N`. Step `n` goes from `τ n` to
`τ (n + 1)` with step size `τ (n + 1) - τ n`, which may vary from step to step (step-size
control); the values `τ n` for `n > N` play no role. The uniform grid `t₀ + n h` is
`uniformGrid t₀ h` (`isGrid_uniformGrid`). -/
structure IsGrid (τ : ℕ → ℝ) (N : ℕ) : Prop where
  /-- The grid times are nondecreasing up to step `N`. -/
  mono : ∀ n < N, τ n ≤ τ (n + 1)

/-- The uniform grid `n ↦ t₀ + n h` with start `t₀` and step size `h`. -/
abbrev uniformGrid (t₀ h : ℝ) : ℕ → ℝ := fun n => t₀ + n * h

/-- `IsGrid` is the monotonicity hypothesis `∀ n < N, τ n ≤ τ (n + 1)` of the existing
variable-step statements. -/
theorem isGrid_iff {τ : ℕ → ℝ} {N : ℕ} : IsGrid τ N ↔ ∀ n < N, τ n ≤ τ (n + 1) :=
  ⟨fun h => h.mono, fun h => ⟨h⟩⟩

/-- The step size of the uniform grid is `h`. -/
theorem uniformGrid_succ_sub (t₀ h : ℝ) (n : ℕ) :
    uniformGrid t₀ h (n + 1) - uniformGrid t₀ h n = h := by
  simp only [uniformGrid]
  push_cast
  ring

/-- The uniform grid with step size `h ≥ 0` is a grid. -/
theorem isGrid_uniformGrid {t₀ h : ℝ} (hh : 0 ≤ h) (N : ℕ) : IsGrid (uniformGrid t₀ h) N :=
  ⟨fun n _ => by linarith [uniformGrid_succ_sub t₀ h n]⟩

/-- A grid with variable step sizes: the squares `τ n = n²` (step sizes `2 n + 1`). -/
example (N : ℕ) : IsGrid (fun n => (n : ℝ) ^ 2) N :=
  ⟨fun n _ => by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) n]⟩

end Grid

/-! ### Exact-flow fans, stability along the fan, local errors -/

section Fan

variable {E : Type*} [NormedAddCommGroup E]

/-- **Stability of the exact flow along the fan**, relative to the reference solution `A`: on
step `n` the exact solution `Φ n` started at time `τ n` ends within the factor `a n` of its
initial distance to `A`,
`‖Φ n (τ (n + 1)) - A (τ (n + 1))‖ ≤ a n ‖Φ n (τ n) - A (τ n)‖`. Only the pairs `(Φ n, A)` are
compared, not all pairs of solutions, so conditions on `F` near `A` (on a tube, or one-sided on a
set) suffice. For an `L`-Lipschitz field one can take `a n = exp (L (τ (n + 1) - τ n))`
(`ODESolution.norm_sub_le_exp`); a dissipative field gives factors below `1`. -/
def FanStable (A : ℝ → E) (τ : ℕ → ℝ) (N : ℕ) (Φ : ℕ → ℝ → E) (a : ℕ → ℝ) : Prop :=
  ∀ n < N, ‖Φ n (τ (n + 1)) - A (τ (n + 1))‖ ≤ a n * ‖Φ n (τ n) - A (τ n)‖

variable [NormedSpace ℝ E]

/-- The **exact-flow fan** of the numerical values `Y 0, …, Y N` on the grid `τ`: for each step
`n < N`, `Φ n` is an exact solution of `y' = F(t, y)` on `[τ n, τ (n + 1)]` that starts at the
numerical value, `Φ n (τ n) = Y n`. The local error of step `n` is `Y (n + 1) - Φ n (τ (n + 1))`;
propagating these errors along the fan with the exact flow ("Lady Windermere's fan") gives the
global error. The fan is a property of the problem and of the values `Y n`, not of the method.
On the uniform grid it is the pair of hypotheses `hΦ`, `hΦ₀` of `lady_windermere`
(`isExactFan_uniformGrid_iff`). -/
structure IsExactFan (F : ℝ → E → E) (τ : ℕ → ℝ) (N : ℕ) (Y : ℕ → E) (Φ : ℕ → ℝ → E) :
    Prop where
  /-- `Φ n` solves `y' = F(t, y)` on `[τ n, τ (n + 1)]`. -/
  sol : ∀ n < N, ODESolution F (Φ n) (τ n) (τ (n + 1))
  /-- `Φ n` starts at the numerical value `Y n`. -/
  start : ∀ n < N, Φ n (τ n) = Y n

/-- **Local error of one step**: the step from `Y₀` at time `t₀` to `Y₁` at time `t₁` has local
error at most `δ` if `‖Y₁ - Φ t₁‖ ≤ δ` for every exact solution `Φ` of `y' = F(t, y)` on
`[t₀, t₁]` with `Φ t₀ = Y₀`. The exact solution is quantified, not given, so a local error
statement about a method carries no flow argument. When the exact solution is unique (for
Lipschitz `F`) this is the usual local error; when there is no exact solution the condition is
vacuous, which is why global error bounds combine it with an exact fan
(`IsExactFan.norm_sub_le_of_hasLocalError`). Intended for `t₀ ≤ t₁`. -/
def HasLocalError (F : ℝ → E → E) (t₀ t₁ : ℝ) (Y₀ Y₁ : E) (δ : ℝ) : Prop :=
  ∀ Φ : ℝ → E, ODESolution F Φ t₀ t₁ → Φ t₀ = Y₀ → ‖Y₁ - Φ t₁‖ ≤ δ

variable {F : ℝ → E → E} {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → E} {Φ : ℕ → ℝ → E}

/-- On the uniform grid, the exact-flow fan is the pair of hypotheses
`hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h)` and
`hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n` of `lady_windermere`. -/
theorem isExactFan_uniformGrid_iff {t₀ h : ℝ} :
    IsExactFan F (uniformGrid t₀ h) N Y Φ ↔
      (∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h)) ∧
        ∀ n < N, Φ n (t₀ + n * h) = Y n := by
  have e : ∀ n : ℕ, uniformGrid t₀ h (n + 1) = t₀ + ((n : ℝ) + 1) * h := fun n => by
    simp [uniformGrid]
  constructor
  · exact fun hΦ => ⟨fun n hn => e n ▸ hΦ.sol n hn, hΦ.start⟩
  · exact fun hΦ => ⟨fun n hn => (e n).symm ▸ hΦ.1 n hn, hΦ.2⟩

/-- A larger bound is a bound. -/
theorem HasLocalError.mono {t₀ t₁ : ℝ} {Y₀ Y₁ : E} {δ δ' : ℝ}
    (h : HasLocalError F t₀ t₁ Y₀ Y₁ δ) (hδ : δ ≤ δ') : HasLocalError F t₀ t₁ Y₀ Y₁ δ' :=
  fun Φ hΦ hΦ₀ => (h Φ hΦ hΦ₀).trans hδ

/-- Local errors of the steps give the local errors along any exact-flow fan: the hypothesis
`hloc : ∀ n < N, ‖Y (n + 1) - Φ n (τ (n + 1))‖ ≤ δ n` of the Lady Windermere argument. -/
theorem IsExactFan.norm_sub_le_of_hasLocalError (hΦ : IsExactFan F τ N Y Φ) {δ : ℕ → ℝ}
    (hloc : ∀ n < N, HasLocalError F (τ n) (τ (n + 1)) (Y n) (Y (n + 1)) (δ n)) :
    ∀ n < N, ‖Y (n + 1) - Φ n (τ (n + 1))‖ ≤ δ n :=
  fun n hn => hloc n hn (Φ n) (hΦ.sol n hn) (hΦ.start n hn)

end Fan

/-! ### Non-vacuity of the fan predicates: the linear field `F(t, x) = c x` -/

section FanExamples

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `t ↦ exp (c (t - s)) y` solves `y' = c y`. -/
private theorem odeSolution_exp_mul_sub_smul (c s : ℝ) (y : E) (a b : ℝ) :
    ODESolution (fun _ x => c • x) (fun t => Real.exp (c * (t - s)) • y) a b := by
  have hd : ∀ t, HasDerivAt (fun t => Real.exp (c * (t - s)) • y)
      (c • (Real.exp (c * (t - s)) • y)) t := fun t => by
    have h1 : HasDerivAt (fun t => c * (t - s)) c t := by
      simpa using ((hasDerivAt_id t).sub_const s).const_mul c
    convert h1.exp.smul_const y using 1
    rw [smul_smul, mul_comm c (Real.exp (c * (t - s)))]
  exact ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => (hd t).hasDerivWithinAt⟩

/-- The exact step `Y₁ = exp (c (t₁ - t₀)) Y₀` of `y' = c y` has local error `0`. -/
private theorem hasLocalError_exp_smul (c : ℝ) {t₀ t₁ : ℝ} (h : t₀ ≤ t₁) (Y₀ : E) :
    HasLocalError (fun _ x => c • x) t₀ t₁ Y₀ (Real.exp (c * (t₁ - t₀)) • Y₀) 0 := by
  intro Φ hΦ hΦ₀
  have hΨ := odeSolution_exp_mul_sub_smul c t₀ Y₀ t₀ t₁
  have hd := dist_le_of_trajectories_ODE (v := fun _ x => c • x) (K := ‖c‖₊) (δ := 0)
    (fun _ => lipschitzWith_smul c) hΨ.cont hΨ.deriv hΦ.cont hΦ.deriv (by simp [hΦ₀]) t₁
    ⟨h, le_rfl⟩
  rw [zero_mul, dist_le_zero] at hd
  rw [← hd]
  simp

/-- **Non-vacuity of `IsExactFan`.** For `y' = c y` the curves `t ↦ exp (c (t - τ n)) Y n` form
the exact-flow fan of any values `Y n` on any grid. -/
example (c : ℝ) (τ : ℕ → ℝ) (N : ℕ) (Y : ℕ → E) :
    IsExactFan (fun _ x => c • x) τ N Y fun n t => Real.exp (c * (t - τ n)) • Y n :=
  ⟨fun n _ => odeSolution_exp_mul_sub_smul c (τ n) (Y n) _ _, fun n _ => by simp⟩

/-- **Non-vacuity of `FanStable`, with equality.** For `y' = c y`, the fan of the previous example
and the reference solution `A t = exp (c t) x₀` satisfy the stability estimate with the factors
`a n = exp (c (τ (n + 1) - τ n))`, below `1` for `c < 0` and forward steps. -/
example (c : ℝ) (x₀ : E) (τ : ℕ → ℝ) (N : ℕ) (Y : ℕ → E) :
    FanStable (fun t => Real.exp (c * t) • x₀) τ N (fun n t => Real.exp (c * (t - τ n)) • Y n)
      fun n => Real.exp (c * (τ (n + 1) - τ n)) := by
  intro n _
  have h : Real.exp (c * τ (n + 1)) = Real.exp (c * (τ (n + 1) - τ n)) * Real.exp (c * τ n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  refine le_of_eq ?_
  simp only [sub_self, mul_zero, Real.exp_zero, one_smul]
  rw [h, mul_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- **Non-vacuity of `HasLocalError`.** For `y' = c y` the exact step has local error `0`. -/
example (c : ℝ) {t₀ t₁ : ℝ} (h : t₀ ≤ t₁) (Y₀ : E) :
    HasLocalError (fun _ x => c • x) t₀ t₁ Y₀ (Real.exp (c * (t₁ - t₀)) • Y₀) 0 :=
  hasLocalError_exp_smul c h Y₀

end FanExamples

/-! ### Methods as relations and runs -/

section StepRel

/-- A **one-step method as a relation on states**: `M t₀ t₁ Y₀ Y₁` says that `Y₁` is an admissible
result of one step of the method from the state `Y₀` at time `t₀` to time `t₁`. It is a relation
and not a function because the low-rank integrators involve choices (bases from QR or SVD
factorizations are not unique, substeps are specified by the ODE they solve); error bounds hold
for every admissible result. The relation describes the algorithm only: Lipschitz constants and
normal-component bounds are hypotheses of the theorems, not part of the method. -/
abbrev StepRel (E : Type*) : Type _ := ℝ → ℝ → E → E → Prop

variable {E : Type*}

/-- A **run** of the method `M` on the grid `τ` with `N` steps: `τ` is a grid, and each value
`Y (n + 1)` is an admissible result of one step of `M` from `Y n`, from time `τ n` to
`τ (n + 1)`. -/
structure IsRun (M : StepRel E) (τ : ℕ → ℝ) (N : ℕ) (Y : ℕ → E) : Prop where
  /-- `τ` is a grid with `N` steps. -/
  grid : IsGrid τ N
  /-- Step `n` of the run is a step of `M`. -/
  step : ∀ n < N, M (τ n) (τ (n + 1)) (Y n) (Y (n + 1))

/-- The method `M` **conserves the quantity `I` up to `ϑ`** in each forward step:
`|I Y₁ - I Y₀| ≤ ϑ` whenever `t₀ ≤ t₁` and `M t₀ t₁ Y₀ Y₁`. `ϑ = 0` is exact conservation (for
example of the norm or the mass); `ϑ > 0` covers methods that conserve a quantity up to a
truncation tolerance. -/
def StepRel.ConservesUpTo (M : StepRel E) (I : E → ℝ) (ϑ : ℝ) : Prop :=
  ∀ ⦃t₀ t₁ Y₀ Y₁⦄, t₀ ≤ t₁ → M t₀ t₁ Y₀ Y₁ → |I Y₁ - I Y₀| ≤ ϑ

/-- On the uniform grid with `h ≥ 0`, a run is the hypothesis
`∀ n < N, M (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (Y (n + 1))` of the global error theorems. -/
theorem isRun_uniformGrid_iff {M : StepRel E} {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {Y : ℕ → E} :
    IsRun M (uniformGrid t₀ h) N Y ↔
      ∀ n < N, M (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (Y (n + 1)) := by
  have e : ∀ n : ℕ, uniformGrid t₀ h (n + 1) = t₀ + ((n : ℝ) + 1) * h := fun n => by
    simp [uniformGrid]
  exact ⟨fun hY n hn => e n ▸ hY.step n hn,
    fun hY => ⟨isGrid_uniformGrid hh N, fun n hn => (e n).symm ▸ hY n hn⟩⟩

/-- **Non-vacuity of `ConservesUpTo`.** A method whose steps move the state by at most `ϑ`
conserves the norm up to `ϑ`. -/
example [NormedAddCommGroup E] (ϑ : ℝ) :
    StepRel.ConservesUpTo (fun _ _ (Y₀ Y₁ : E) => ‖Y₁ - Y₀‖ ≤ ϑ) (fun Y => ‖Y‖) ϑ :=
  fun _ _ Y₀ Y₁ _ h => (abs_norm_sub_norm_le Y₁ Y₀).trans h

end StepRel

section StepRelAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The method `M` has **local error at most `δ t₀ t₁` on the region `D`** for the equation
`y' = F(t, y)`: every forward step `t₀ ≤ t₁` of `M` from a state `Y₀` with `(t₀, Y₀) ∈ D`
satisfies `HasLocalError F t₀ t₁ Y₀ Y₁ (δ t₀ t₁)`. For a method of order `p` typically
`δ t₀ t₁ = C (t₁ - t₀) ^ (p + 1)`. -/
def StepRel.HasLocalErrorOn (M : StepRel E) (F : ℝ → E → E) (D : Set (ℝ × E))
    (δ : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃t₀ t₁ Y₀ Y₁⦄, t₀ ≤ t₁ → (t₀, Y₀) ∈ D → M t₀ t₁ Y₀ Y₁ → HasLocalError F t₀ t₁ Y₀ Y₁ (δ t₀ t₁)

/-- The method `M` is **exact for the solution `A`** of a problem with state-independent
right-hand side: on every interval `[t₀, t₁]` (`t₀ ≤ t₁`) on which `F t Y = Ȧ(t)` for all states
(`IsDerivRHS F A t₀ t₁`), every step of `M` from `A t₀` ends at `A t₁`. Low-rank integrators are
exact in this sense when `A (t)` has low rank (robust exactness). -/
def StepRel.IsExactFor (M : StepRel E) (F : ℝ → E → E) (A : ℝ → E) : Prop :=
  ∀ ⦃t₀ t₁ Y₁⦄, t₀ ≤ t₁ → IsDerivRHS F A t₀ t₁ → M t₀ t₁ (A t₀) Y₁ → Y₁ = A t₁

variable {M : StepRel E} {F : ℝ → E → E} {D : Set (ℝ × E)} {δ : ℝ → ℝ → ℝ}

/-- The steps of a run of a method with local error `δ` on `D` have local error
`δ (τ n) (τ (n + 1))`, as long as the run stays in `D`. -/
theorem IsRun.hasLocalError {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → E} (hY : IsRun M τ N Y)
    (hM : M.HasLocalErrorOn F D δ) (hD : ∀ n < N, (τ n, Y n) ∈ D) :
    ∀ n < N, HasLocalError F (τ n) (τ (n + 1)) (Y n) (Y (n + 1)) (δ (τ n) (τ (n + 1))) :=
  fun n hn => hM (hY.grid.mono n hn) (hD n hn) (hY.step n hn)

/-- A method with local error `0` on a region containing the graph of `A` is exact for `A`: when
`F t Y = Ȧ(t)` for all states, `A` itself is an exact solution started at `A t₀`. -/
theorem StepRel.HasLocalErrorOn.isExactFor {A : ℝ → E} (hM : M.HasLocalErrorOn F D fun _ _ => 0)
    (hA : ∀ t, (t, A t) ∈ D) : M.IsExactFor F A := by
  intro t₀ t₁ Y₁ ht hF hY
  have hsol : ODESolution F A t₀ t₁ := ⟨hF.cont, fun t ht' => hF.deriv t ht' (A t)⟩
  have h : ‖Y₁ - A t₁‖ ≤ 0 := hM ht (hA t₀) hY A hsol rfl
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

/-- **Non-vacuity of `HasLocalErrorOn`.** The exact method `Y₁ = exp (c (t₁ - t₀)) Y₀` of
`y' = c y` has local error `0` everywhere. -/
example (c : ℝ) :
    StepRel.HasLocalErrorOn (fun s₀ s₁ (Y₀ Y₁ : E) => Y₁ = Real.exp (c * (s₁ - s₀)) • Y₀)
      (fun _ x => c • x) univ fun _ _ => 0 := by
  rintro s₀ s₁ Y₀ Y₁ hs - rfl
  exact hasLocalError_exp_smul c hs Y₀

/-- **Non-vacuity of `IsExactFor`.** The explicit Euler step `Y₁ = Y₀ + (t₁ - t₀) v` is exact for
the constant field `v` and the solutions `A t = t v + w`. -/
example (v w : E) :
    StepRel.IsExactFor (fun s₀ s₁ (Y₀ Y₁ : E) => Y₁ = Y₀ + (s₁ - s₀) • v) (fun _ _ => v)
      fun t => t • v + w := by
  rintro s₀ s₁ Y₁ - - rfl
  simp only [sub_smul]
  abel

/-- **Why `IsExactFor` constrains forward steps only.** Without `t₀ ≤ t₁` exactness would fail
already for the exact flow `M t₀ t₁ Y₀ Y₁ := ∃ Φ, ODESolution F Φ t₀ t₁ ∧ Φ t₀ = Y₀ ∧ Φ t₁ = Y₁`:
for `t₀ > t₁` the interval `[t₀, t₁]` is empty, so `IsDerivRHS` and `ODESolution` hold for every
curve and the relation allows every `Y₁`. Here `F = 0`, `A = 0`, `t₀ = 1`, `t₁ = 0`, `Y₁ = 1`. -/
example : ¬ ∀ ⦃t₀ t₁ Y₁ : ℝ⦄, IsDerivRHS (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ)) t₀ t₁ →
    (∃ Φ : ℝ → ℝ, ODESolution (fun _ _ => (0 : ℝ)) Φ t₀ t₁ ∧ Φ t₀ = 0 ∧ Φ t₁ = Y₁) →
      Y₁ = 0 := by
  intro h
  have h1 := @h 1 0 1 ⟨by simp, by simp⟩
    ⟨fun t => if t = 1 then 0 else 1, ⟨by simp, by simp⟩, by simp, by simp⟩
  norm_num at h1

end StepRelAnalysis

section RunExample

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Non-vacuity of `IsRun`.** The iterates `projEulerIter P F h t₀ x₀` of the projected Euler
method are a run, on the uniform grid, of the relation `Y₁ = Y₀ + (t₁ - t₀) P F(t₀, Y₀)`. -/
example (P : E →L[ℝ] E) (F : ℝ → E → E) {t₀ h : ℝ} (hh : 0 ≤ h) (x₀ : E) (N : ℕ) :
    IsRun (fun s₀ s₁ Y₀ Y₁ => Y₁ = projEuler P F (s₁ - s₀) s₀ Y₀) (uniformGrid t₀ h) N
      (projEulerIter P F h t₀ x₀) := by
  refine ⟨isGrid_uniformGrid hh N, fun n _ => ?_⟩
  exact (congrArg (fun k => projEuler P F k (uniformGrid t₀ h n) (projEulerIter P F h t₀ x₀ n))
    (uniformGrid_succ_sub t₀ h n)).symm

end RunExample

end LeanDLRA
