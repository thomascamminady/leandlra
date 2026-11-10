import LeanDLRA.Integrators.GlobalError

/-!
# The tube theorem: global error bounds from hypotheses near the solution

The global error bound of `LeanDLRA/Integrators/GlobalError.lean` for a Lipschitz field needs the
Lipschitz condition wherever the exact solutions started at the numerical values run. The
differential equations of dynamical low-rank approximation are Lipschitz and bounded only near
the solution `A` that is approximated: on the tube `‖x - A t‖ ≤ ρ` (`IsLipschitzOnTube`,
`IsBoundedOnTube`, bundled in `DLRAProblem`). The **tube theorem** of this file shows that these
hypotheses are enough, by induction along the time grid:

* as long as the numerical values `Y 0, …, Y n` are at distance at most `R k` from `A`, the
  local errors of the steps `0, …, n - 1` are available, the exact solutions started at these
  values stay in the tube (a solution of a field bounded by `B` moves away from `A` by at most
  `2 B (τ (k + 1) - τ k)` during step `k`, and `R k + 2 B (τ (k + 1) - τ k) < ρ`), and the global
  error bound holds up to step `n`;
* if this bound is at most `R n`, the value `Y n` is again at distance at most `R n` from `A`.

So a method whose error bound stays below the radii `R n` never leaves the tube, and its global
error is bounded exactly as for a globally Lipschitz field. Nothing is assumed about `F` outside
the tube, and the local error of step `n` is needed only if `‖Y n - A (τ n)‖ ≤ R n`.

## Main results

* `IsExactFan.norm_sub_le_of_near`: the global error bound for values that are known to lie well
  inside the tube.
* `IsLipschitzOnTube.norm_sub_le_of_fan`: the tube theorem with the exact solutions on the steps
  given (no completeness, no continuity in time).
* `IsLipschitzOnTube.norm_sub_le_of_hasLocalError`, `DLRAProblem.norm_sub_le_of_hasLocalError`:
  the tube theorem for local errors in the form `HasLocalError`; the exact solutions are
  constructed.
* `IsRun.norm_sub_le_of_tube`, `IsRun.norm_sub_le_of_hasLocalErrorOn`: the tube theorem for the
  runs of a method `M : StepRel E`.
* `uniformGrid_errorBound_le`, `IsLipschitzOnTube.norm_sub_le_of_fan_uniformGrid`,
  `IsRun.norm_sub_le_of_tube_uniformGrid`: on the uniform grid `t₀ + n h` with local errors
  `h c` the bound is `e^{L T} δ₀ + T e^{L T} c` for `n h ≤ T`. This is the form in which the
  error bounds of the low-rank integrators are stated. `uniformGrid_step` collects the
  elementary facts about one step of this grid.
* `DLRAProblem.tubeExt`: the extension `tubeExt F A a b ρ` of a `DLRAProblem` is globally
  Lipschitz and bounded and has the same solution `A`.
* `IsGrid.of_le`, `IsGrid.le_of_le`, `IsExactFan.of_le`, `IsRun.of_le`: restriction of grids,
  fans and runs to the first `n` steps.
* `exists_isRun`: a run exists if every shorter run can be continued by one step.

## Implementation notes

The radii `R n` may depend on the step. A constant radius is the usual choice; `R n` equal to the
error bound at step `n` gives the weakest smallness condition.
-/

open Set Finset

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : ℝ → E → E} {A : ℝ → E}

/-! ### Restriction to the first steps -/

section Restrict

/-- The first `n ≤ N` steps of a grid with `N` steps form a grid. -/
theorem IsGrid.of_le {τ : ℕ → ℝ} {N n : ℕ} (hτ : IsGrid τ N) (hn : n ≤ N) : IsGrid τ n :=
  ⟨fun k hk => hτ.mono k (hk.trans_le hn)⟩

/-- The times of a grid are nondecreasing: `τ m ≤ τ n` for `m ≤ n ≤ N`. -/
theorem IsGrid.le_of_le {τ : ℕ → ℝ} {N m n : ℕ} (hτ : IsGrid τ N) (hmn : m ≤ n) (hn : n ≤ N) :
    τ m ≤ τ n :=
  isGrid_iff_monotoneOn.1 hτ (Set.mem_Iic.2 (hmn.trans hn)) (Set.mem_Iic.2 hn) hmn

/-- The first `n ≤ N` curves of an exact-flow fan form an exact-flow fan. -/
theorem IsExactFan.of_le {τ : ℕ → ℝ} {N n : ℕ} {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : IsExactFan F τ N Y Φ) (hn : n ≤ N) : IsExactFan F τ n Y Φ :=
  ⟨fun k hk => hΦ.sol k (hk.trans_le hn), fun k hk => hΦ.start k (hk.trans_le hn)⟩

/-- The first `n ≤ N` steps of a run form a run. -/
theorem IsRun.of_le {E : Type*} {M : StepRel E} {τ : ℕ → ℝ} {N n : ℕ} {Y : ℕ → E}
    (hY : IsRun M τ N Y) (hn : n ≤ N) : IsRun M τ n Y :=
  ⟨hY.grid.of_le hn, fun k hk => hY.step k (hk.trans_le hn)⟩

end Restrict

/-! ### Construction of runs -/

/-- **Runs can be constructed step by step.** Let `τ` be a grid with `N` steps. If every run of
the method `M` over the first `n < N` steps that starts at `Y₀` can be continued by one more step,
then there is a run over all `N` steps that starts at `Y₀`. The hypothesis hands over the whole
run constructed so far, so the continuation may use everything that is known about runs, for
example an error bound that keeps the last value in the region where a step exists. -/
theorem exists_isRun {E : Type*} {M : StepRel E} {τ : ℕ → ℝ} {N : ℕ} (hτ : IsGrid τ N) (Y₀ : E)
    (hstep : ∀ n < N, ∀ Y : ℕ → E, Y 0 = Y₀ → IsRun M τ n Y →
      ∃ Y₁, M (τ n) (τ (n + 1)) (Y n) Y₁) :
    ∃ Y : ℕ → E, Y 0 = Y₀ ∧ IsRun M τ N Y := by
  induction N with
  | zero => exact ⟨fun _ => Y₀, rfl, hτ, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
  | succ N ih =>
    obtain ⟨Y, hY₀, hY⟩ := ih (hτ.of_le N.le_succ) fun n hn => hstep n (hn.trans N.lt_succ_self)
    obtain ⟨Y₁, hY₁⟩ := hstep N N.lt_succ_self Y hY₀ hY
    refine ⟨Function.update Y (N + 1) Y₁, ?_, hτ, fun n hn => ?_⟩
    · rw [Function.update_of_ne (by omega : (0 : ℕ) ≠ N + 1), hY₀]
    · rw [Function.update_of_ne (by omega : n ≠ N + 1)]
      rcases (Nat.le_of_lt_succ hn).lt_or_eq with hlt | rfl
      · rw [Function.update_of_ne (by omega : n + 1 ≠ N + 1)]
        exact hY.step n hlt
      · rw [Function.update_self]
        exact hY₁

/-! ### The extension of a problem on a tube -/

/-- **A problem on a tube becomes a global problem.** If `F` is `L`-Lipschitz and bounded by `B`
on the tube of radius `ρ ≥ 0` around the solution `A` (`DLRAProblem`), the field
`tubeExt F A a b ρ`, which agrees with `F` on the tube, is `L`-Lipschitz and bounded by `B`
everywhere and `A` solves its differential equation. Statements for globally Lipschitz and
bounded fields therefore apply to `tubeExt F A a b ρ`; they are statements about `F` as long as
the curves involved stay in the tube (`odeSolution_tubeExt_iff`). -/
theorem DLRAProblem.tubeExt {a b ρ L B : ℝ} (hP : DLRAProblem F A a b ρ L B) (hρ : 0 ≤ ρ) :
    IsLipschitzField (LeanDLRA.tubeExt F A a b ρ) L ∧
      IsBoundedField (LeanDLRA.tubeExt F A a b ρ) B ∧
      ODESolution (LeanDLRA.tubeExt F A a b ρ) A a b :=
  ⟨isLipschitzField_tubeExt hP.lipschitz hP.L_nonneg hρ,
    isBoundedField_tubeExt hP.bounded hP.B_nonneg hρ, hP.sol.tubeExt_self hρ⟩

/-! ### The tube theorem -/

section Tube

variable {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → E} {Φ : ℕ → ℝ → E} {δ : ℕ → ℝ} {ρ L B : ℝ} {R : ℕ → ℝ}

/-- **Global error for values well inside the tube.** Let `F` be `L`-Lipschitz and bounded by `B`
on the tube of radius `ρ` around the exact solution `A`, let `Φ` be the exact-flow fan of the
values `Y n`, and suppose every value has a margin for one step,
`‖Y n - A (τ n)‖ + 2 B (τ (n + 1) - τ n) < ρ`. Then the fan stays in the tube, and local errors
`δ n` give for `n ≤ N`

  `‖Y n - A (τ n)‖ ≤ e^{L (τ n - τ 0)} ‖Y 0 - A (τ 0)‖ + ∑_{k<n} e^{L (τ n - τ (k + 1))} δ k`.

In `IsLipschitzOnTube.norm_sub_le_of_fan` the margin is a consequence of the error bound and not
a hypothesis. -/
theorem IsExactFan.norm_sub_le_of_near (hΦ : IsExactFan F τ N Y Φ)
    (hFL : IsLipschitzOnTube F A (τ 0) (τ N) ρ L) (hL : 0 ≤ L)
    (hFB : IsBoundedOnTube F A (τ 0) (τ N) ρ B) (hB : 0 ≤ B) (hτ : IsGrid τ N)
    (hA : ODESolution F A (τ 0) (τ N))
    (hnear : ∀ n < N, ‖Y n - A (τ n)‖ + 2 * B * (τ (n + 1) - τ n) < ρ)
    (hloc : ∀ n < N, ‖Y (n + 1) - Φ n (τ (n + 1))‖ ≤ δ n) :
    ∀ n ≤ N, ‖Y n - A (τ n)‖ ≤ Real.exp (L * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k := by
  have hin : ∀ n < N, ∀ t ∈ Icc (τ n) (τ (n + 1)), ‖Φ n t - A t‖ ≤ ρ := by
    intro k hk t ht
    have hsub := hτ.Icc_subset hk
    have hle := hτ.mono k hk
    have hk0 : τ 0 ≤ τ k := (hsub (left_mem_Icc.2 hle)).1
    have hk1 : τ (k + 1) ≤ τ N := (hsub (right_mem_Icc.2 hle)).2
    have hρ : 0 ≤ ρ := by
      have h1 := hnear k hk
      have h2 := mul_nonneg (mul_nonneg zero_le_two hB) (sub_nonneg.2 hle)
      have h3 := norm_nonneg (Y k - A (τ k))
      linarith
    have h2B : (B + B) * (τ (k + 1) - τ k) = 2 * B * (τ (k + 1) - τ k) := by ring
    refine (tube_trap (hA.mono hk0 hk1) (hΦ.sol k hk) hB hB (hFB.along hρ hk0 hk1)
      (fun s hs x hx => hFB s ⟨hk0.trans hs.1, hs.2.le.trans hk1⟩ x hx) ?_ t ht).le
    rw [hΦ.start k hk, h2B]
    exact hnear k hk
  intro n hn
  refine ((hFL.fanStable hL hτ hA hΦ hin).norm_sub_le (fun _ _ => (Real.exp_pos _).le) hΦ.start
    hloc n hn).trans_eq ?_
  rw [range_eq_Ico, prod_Ico_exp_mul_sub τ L (Nat.zero_le n)]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  rw [prod_Ico_exp_mul_sub τ L (mem_Ico.1 hk).2]

/-- **The tube theorem.** Let `F` be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ`
around the exact solution `A` on `[τ 0, τ N]`. Let `Y n` be numerical values and `R n` radii with
`R n + 2 B (τ (n + 1) - τ n) < ρ`, and suppose that for every step `n` whose start value satisfies
`‖Y n - A (τ n)‖ ≤ R n` the curve `Φ n` is an exact solution on the step started at `Y n` and the
step has local error `‖Y (n + 1) - Φ n (τ (n + 1))‖ ≤ δ n`. If the error bound

  `e^{L (τ n - τ 0)} ‖Y 0 - A (τ 0)‖ + ∑_{k<n} e^{L (τ n - τ (k + 1))} δ k`

is at most `R n` for `n < N`, then it bounds `‖Y n - A (τ n)‖` for all `n ≤ N`; in particular
`‖Y n - A (τ n)‖ ≤ R n < ρ` for `n < N`, so the values never leave the tube. Nothing is assumed
about `F` outside the tube, and nothing about a step whose start value is farther than `R n` from
`A`: such steps do not occur. -/
theorem IsLipschitzOnTube.norm_sub_le_of_fan (hFL : IsLipschitzOnTube F A (τ 0) (τ N) ρ L)
    (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A (τ 0) (τ N) ρ B) (hB : 0 ≤ B) (hτ : IsGrid τ N)
    (hA : ODESolution F A (τ 0) (τ N))
    (hΦ : ∀ n < N, ‖Y n - A (τ n)‖ ≤ R n → ODESolution F (Φ n) (τ n) (τ (n + 1)) ∧
      Φ n (τ n) = Y n ∧ ‖Y (n + 1) - Φ n (τ (n + 1))‖ ≤ δ n)
    (hR : ∀ n < N, Real.exp (L * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k ≤ R n)
    (hsmall : ∀ n < N, R n + 2 * B * (τ (n + 1) - τ n) < ρ) :
    ∀ n ≤ N, ‖Y n - A (τ n)‖ ≤ Real.exp (L * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hRn : ∀ k < n, ‖Y k - A (τ k)‖ ≤ R k := fun k hk =>
      (ih k hk (hk.le.trans hn)).trans (hR k (hk.trans_le hn))
    have hτn : τ n ≤ τ N := hτ.le_of_le hn le_rfl
    have hfan : IsExactFan F τ n Y Φ :=
      ⟨fun k hk => (hΦ k (hk.trans_le hn) (hRn k hk)).1,
        fun k hk => (hΦ k (hk.trans_le hn) (hRn k hk)).2.1⟩
    exact hfan.norm_sub_le_of_near (hFL.mono le_rfl hτn le_rfl) hL
      (hFB.mono le_rfl hτn le_rfl) hB (hτ.of_le hn) (hA.mono le_rfl hτn)
      (fun k hk => (add_le_add (hRn k hk) le_rfl).trans_lt (hsmall k (hk.trans_le hn)))
      (fun k hk => (hΦ k (hk.trans_le hn) (hRn k hk)).2.2) n le_rfl

/-- **The tube theorem for local errors.** Let `F` be `L`-Lipschitz and bounded by `B` on the tube
of radius `ρ` around the exact solution `A` on `[τ 0, τ N]` and continuous on the tube. Let `Y n`
be numerical values and `R n` radii with `R n + 2 B (τ (n + 1) - τ n) < ρ`, and suppose every step
whose start value satisfies `‖Y n - A (τ n)‖ ≤ R n` has local error `δ n` (`HasLocalError`). If
the error bound is at most `R n` for `n < N`, then for `n ≤ N`

  `‖Y n - A (τ n)‖ ≤ e^{L (τ n - τ 0)} ‖Y 0 - A (τ 0)‖ + ∑_{k<n} e^{L (τ n - τ (k + 1))} δ k`.

The exact solutions started at the numerical values are constructed in the proof
(`exists_ODESolution_near`), so no solution other than `A` appears in the statement. -/
theorem IsLipschitzOnTube.norm_sub_le_of_hasLocalError [CompleteSpace E]
    (hFL : IsLipschitzOnTube F A (τ 0) (τ N) ρ L) (hL : 0 ≤ L)
    (hFB : IsBoundedOnTube F A (τ 0) (τ N) ρ B) (hB : 0 ≤ B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A (τ 0) (τ N) ρ)) (hτ : IsGrid τ N)
    (hA : ODESolution F A (τ 0) (τ N))
    (hloc : ∀ n < N, ‖Y n - A (τ n)‖ ≤ R n →
      HasLocalError F (τ n) (τ (n + 1)) (Y n) (Y (n + 1)) (δ n))
    (hR : ∀ n < N, Real.exp (L * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k ≤ R n)
    (hsmall : ∀ n < N, R n + 2 * B * (τ (n + 1) - τ n) < ρ) :
    ∀ n ≤ N, ‖Y n - A (τ n)‖ ≤ Real.exp (L * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k := by
  have hex : ∀ n, ∃ φ : ℝ → E, n < N → ‖Y n - A (τ n)‖ ≤ R n →
      ODESolution F φ (τ n) (τ (n + 1)) ∧ φ (τ n) = Y n := by
    intro n
    by_cases h : n < N ∧ ‖Y n - A (τ n)‖ ≤ R n
    · obtain ⟨hn, hRn⟩ := h
      have hsub := hτ.Icc_subset hn
      have hle := hτ.mono n hn
      have h0 : τ 0 ≤ τ n := (hsub (left_mem_Icc.2 hle)).1
      have h1 : τ (n + 1) ≤ τ N := (hsub (right_mem_Icc.2 hle)).2
      obtain ⟨φ, hφ, hφ₀, -⟩ := exists_ODESolution_near (hFL.mono h0 h1 le_rfl) hL
        (hFB.mono h0 h1 le_rfl) hB
        (hc.mono fun p hp => ⟨⟨h0.trans hp.1.1, hp.1.2.trans h1⟩, hp.2⟩) (hA.mono h0 h1) hle
        (Y n) ((add_le_add hRn le_rfl).trans_lt (hsmall n hn))
      exact ⟨φ, fun _ _ => ⟨hφ, hφ₀⟩⟩
    · exact ⟨fun _ => Y n, fun hn hRn => absurd ⟨hn, hRn⟩ h⟩
  choose Φ hΦ using hex
  exact hFL.norm_sub_le_of_fan hL hFB hB hτ hA
    (fun n hn hRn => ⟨(hΦ n hn hRn).1, (hΦ n hn hRn).2,
      hloc n hn hRn (Φ n) (hΦ n hn hRn).1 (hΦ n hn hRn).2⟩) hR hsmall

/-- **The tube theorem for a problem on a tube** (`DLRAProblem`): the bundled form of
`IsLipschitzOnTube.norm_sub_le_of_hasLocalError`. -/
theorem DLRAProblem.norm_sub_le_of_hasLocalError [CompleteSpace E]
    (hP : DLRAProblem F A (τ 0) (τ N) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A (τ 0) (τ N) ρ)) (hτ : IsGrid τ N)
    (hloc : ∀ n < N, ‖Y n - A (τ n)‖ ≤ R n →
      HasLocalError F (τ n) (τ (n + 1)) (Y n) (Y (n + 1)) (δ n))
    (hR : ∀ n < N, Real.exp (L * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k ≤ R n)
    (hsmall : ∀ n < N, R n + 2 * B * (τ (n + 1) - τ n) < ρ) :
    ∀ n ≤ N, ‖Y n - A (τ n)‖ ≤ Real.exp (L * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k :=
  hP.lipschitz.norm_sub_le_of_hasLocalError hP.L_nonneg hP.bounded hP.B_nonneg hc hτ hP.sol hloc
    hR hsmall

/-- **The tube theorem for the runs of a method.** Let `Y` be a run of the method `M` on the grid
`τ` for a problem on a tube (`DLRAProblem`) with `F` continuous on the tube. If every step of `M`
from time `τ n` whose start value is at distance at most `R n` from `A (τ n)` has local error
`δ n`, the error bound is at most `R n` for `n < N`, and `R n + 2 B (τ (n + 1) - τ n) < ρ`, then
for `n ≤ N`

  `‖Y n - A (τ n)‖ ≤ e^{L (τ n - τ 0)} ‖Y 0 - A (τ 0)‖ + ∑_{k<n} e^{L (τ n - τ (k + 1))} δ k`.

The local error hypothesis is about the method near `A` and not about the run. -/
theorem IsRun.norm_sub_le_of_tube [CompleteSpace E] {M : StepRel E} (hY : IsRun M τ N Y)
    (hP : DLRAProblem F A (τ 0) (τ N) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A (τ 0) (τ N) ρ))
    (hM : ∀ n < N, ∀ Y₀ Y₁, ‖Y₀ - A (τ n)‖ ≤ R n → M (τ n) (τ (n + 1)) Y₀ Y₁ →
      HasLocalError F (τ n) (τ (n + 1)) Y₀ Y₁ (δ n))
    (hR : ∀ n < N, Real.exp (L * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k ≤ R n)
    (hsmall : ∀ n < N, R n + 2 * B * (τ (n + 1) - τ n) < ρ) :
    ∀ n ≤ N, ‖Y n - A (τ n)‖ ≤ Real.exp (L * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k :=
  hP.norm_sub_le_of_hasLocalError hc hY.grid
    (fun n hn hRn => hM n hn (Y n) (Y (n + 1)) hRn (hY.step n hn)) hR hsmall

/-- **The tube theorem for a method with local error on an inner tube.** If the method `M` has
local error `δ t₀ t₁` for all steps that start in the tube of radius `r` around `A`
(`StepRel.HasLocalErrorOn`), the error bound is at most `r` and `r + 2 B (τ (n + 1) - τ n) < ρ`,
then every run of `M` satisfies the error bound. -/
theorem IsRun.norm_sub_le_of_hasLocalErrorOn [CompleteSpace E] {M : StepRel E} {δ : ℝ → ℝ → ℝ}
    {r : ℝ} (hY : IsRun M τ N Y) (hP : DLRAProblem F A (τ 0) (τ N) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A (τ 0) (τ N) ρ))
    (hM : M.HasLocalErrorOn F (tubeSet A (τ 0) (τ N) r) δ)
    (hR : ∀ n < N, Real.exp (L * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ (τ k) (τ (k + 1)) ≤ r)
    (hsmall : ∀ n < N, r + 2 * B * (τ (n + 1) - τ n) < ρ) :
    ∀ n ≤ N, ‖Y n - A (τ n)‖ ≤ Real.exp (L * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ (τ k) (τ (k + 1)) :=
  hY.norm_sub_le_of_tube (R := fun _ => r) (δ := fun n => δ (τ n) (τ (n + 1))) hP hc
    (fun n hn _ _ hY₀ hstep => hM (hY.grid.mono n hn)
      ⟨hY.grid.Icc_subset hn (left_mem_Icc.2 (hY.grid.mono n hn)), hY₀⟩ hstep) hR hsmall

end Tube

/-! ### The uniform grid -/

section Uniform

/-- On the uniform grid `t₀ + n h` with local errors `h c`, the global error bound of
`IsExactFan.norm_sub_le` is at most `e^{L T} δ₀ + T e^{L T} c` as long as `n h ≤ T`: every
propagation factor is at most `e^{L T}`, and the `n` local errors add up to `n h c ≤ T c`. -/
theorem uniformGrid_errorBound_le {L h T c e₀ δ₀ : ℝ} (t₀ : ℝ) {n : ℕ} (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hc : 0 ≤ c) (hnT : n * h ≤ T) (he₀ : 0 ≤ e₀) (he : e₀ ≤ δ₀) :
    Real.exp (L * (uniformGrid t₀ h n - uniformGrid t₀ h 0)) * e₀ +
        ∑ k ∈ range n, Real.exp (L * (uniformGrid t₀ h n - uniformGrid t₀ h (k + 1))) * (h * c) ≤
      Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c := by
  have h0 : Real.exp (L * (uniformGrid t₀ h n - uniformGrid t₀ h 0)) ≤ Real.exp (L * T) := by
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hL)
    have hn0 : uniformGrid t₀ h n - uniformGrid t₀ h 0 = n * h := by simp [uniformGrid]
    rw [hn0]
    exact hnT
  have hk : ∀ k ∈ range n,
      Real.exp (L * (uniformGrid t₀ h n - uniformGrid t₀ h (k + 1))) * (h * c) ≤
        Real.exp (L * T) * (h * c) := by
    intro k _
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hL))
      (mul_nonneg hh hc)
    have hnk : uniformGrid t₀ h n - uniformGrid t₀ h (k + 1) = n * h - (k + 1) * h := by
      simp only [uniformGrid, Nat.cast_add, Nat.cast_one]
      ring
    have hk0 : 0 ≤ ((k : ℝ) + 1) * h := mul_nonneg (by positivity) hh
    rw [hnk]
    linarith
  have hsum : ∑ k ∈ range n,
      Real.exp (L * (uniformGrid t₀ h n - uniformGrid t₀ h (k + 1))) * (h * c) ≤
        T * Real.exp (L * T) * c :=
    calc ∑ k ∈ range n, Real.exp (L * (uniformGrid t₀ h n - uniformGrid t₀ h (k + 1))) * (h * c)
        ≤ ∑ _k ∈ range n, Real.exp (L * T) * (h * c) := sum_le_sum hk
      _ = n * h * (Real.exp (L * T) * c) := by
        rw [sum_const, card_range, nsmul_eq_mul]
        ring
      _ ≤ T * (Real.exp (L * T) * c) :=
        mul_le_mul_of_nonneg_right hnT (mul_nonneg (Real.exp_pos _).le hc)
      _ = T * Real.exp (L * T) * c := by ring
  exact add_le_add (mul_le_mul h0 he he₀ (Real.exp_pos _).le) hsum

/-- Step `n < N` of the uniform grid with step size `h ≥ 0`: the interval
`[t₀ + n h, t₀ + (n + 1) h]` lies in `[t₀, t₀ + N h]` and has length `h`. -/
theorem uniformGrid_step {t₀ h : ℝ} (hh : 0 ≤ h) {n N : ℕ} (hn : n < N) :
    t₀ ≤ t₀ + n * h ∧ t₀ + n * h ≤ t₀ + (n + 1) * h ∧ t₀ + (n + 1) * h ≤ t₀ + N * h ∧
      t₀ + (n + 1) * h - (t₀ + n * h) = h := by
  have h1 : (n : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hn
  have h2 : ((n : ℝ) + 1) * h ≤ N * h := mul_le_mul_of_nonneg_right h1 hh
  have h3 : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg n) hh
  exact ⟨by linarith, by linarith, by linarith, by ring⟩

variable {t₀ h T c δ₀ ρ L B : ℝ} {N : ℕ} {Y : ℕ → E}

/-- **Tube theorem on the uniform grid, exact solutions given.** Let `F` be Lipschitz and bounded
on the tube of radius `ρ` around a solution `A` over `[t₀, t₀ + N h]`. Suppose that, whenever
`Y n` is within the error bound `e^{L T} δ₀ + T e^{L T} c` of `A (t₀ + n h)`, the function `Φ n`
is the solution of `ẏ = F t y` on step `n` started at `Y n`, and `Y (n + 1)` differs from its end
value by at most `h c`. If the error bound plus `2 B h` is below `ρ`, `‖Y 0 - A t₀‖ ≤ δ₀` and
`N h ≤ T`, then the error bound holds at every grid point. -/
theorem IsLipschitzOnTube.norm_sub_le_of_fan_uniformGrid {Φ : ℕ → ℝ → E}
    (hFL : IsLipschitzOnTube F A t₀ (t₀ + N * h) ρ L) (hL : 0 ≤ L)
    (hFB : IsBoundedOnTube F A t₀ (t₀ + N * h) ρ B) (hB : 0 ≤ B) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ (t₀ + N * h))
    (hΦ : ∀ n < N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c →
      ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h) ∧ Φ n (t₀ + n * h) = Y n ∧
        ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤ h * c)
    (hc : 0 ≤ c) (hδ : ‖Y 0 - A t₀‖ ≤ δ₀) (hNT : N * h ≤ T)
    (hsmall : Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c + 2 * B * h < ρ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c := by
  have e : ∀ n : ℕ, uniformGrid t₀ h (n + 1) = t₀ + ((n : ℝ) + 1) * h := fun n => by
    simp [uniformGrid]
  have e0 : uniformGrid t₀ h 0 = t₀ := by simp [uniformGrid]
  have hFL' : IsLipschitzOnTube F A (uniformGrid t₀ h 0) (uniformGrid t₀ h N) ρ L := by
    rw [e0]
    exact hFL
  have hFB' : IsBoundedOnTube F A (uniformGrid t₀ h 0) (uniformGrid t₀ h N) ρ B := by
    rw [e0]
    exact hFB
  have hA' : ODESolution F A (uniformGrid t₀ h 0) (uniformGrid t₀ h N) := by
    rw [e0]
    exact hA
  have hb : ∀ k ≤ N, Real.exp (L * (uniformGrid t₀ h k - uniformGrid t₀ h 0)) *
      ‖Y 0 - A (uniformGrid t₀ h 0)‖ + ∑ j ∈ range k,
        Real.exp (L * (uniformGrid t₀ h k - uniformGrid t₀ h (j + 1))) * (h * c) ≤
      Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c := fun k hk =>
    uniformGrid_errorBound_le t₀ hL hh hc
      ((mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) hh).trans hNT) (norm_nonneg _)
      (by rw [e0]; exact hδ)
  intro n hn
  refine (IsLipschitzOnTube.norm_sub_le_of_fan (τ := uniformGrid t₀ h) (Φ := Φ)
    (R := fun _ => Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c) (δ := fun _ => h * c)
    hFL' hL hFB' hB (isGrid_uniformGrid hh N) hA' ?_ (fun k hk => hb k hk.le) ?_ n hn).trans
    (hb n hn)
  · intro k hk hRk
    rw [e k]
    exact hΦ k hk hRk
  · intro k _
    rw [uniformGrid_succ_sub]
    exact hsmall

/-- **Tube theorem for runs on the uniform grid.** Let `(F, A)` be a `DLRAProblem` over
`[t₀, t₀ + N h]` with tube radius `ρ`, `F` continuous on the tube, and let `Y` be a run of the
method `M` on the grid `t₀ + n h`. Suppose every step of `M` that starts within the error bound
`e^{L T} δ₀ + T e^{L T} c` of `A` has local error `h c`. If the error bound plus `2 B h` is below
`ρ`, `‖Y 0 - A t₀‖ ≤ δ₀` and `N h ≤ T`, then the run satisfies the error bound at every grid
point. The step size is nonnegative because `Y` is a run. -/
theorem IsRun.norm_sub_le_of_tube_uniformGrid [CompleteSpace E] {M : StepRel E}
    (hY : IsRun M (uniformGrid t₀ h) N Y) (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hM : ∀ n < N, ∀ Y₀ Y₁,
      ‖Y₀ - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c →
      M (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ →
      HasLocalError F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ (h * c))
    (hc₀ : 0 ≤ c) (hδ : ‖Y 0 - A t₀‖ ≤ δ₀) (hNT : N * h ≤ T)
    (hsmall : Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c + 2 * B * h < ρ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c := by
  obtain rfl | hN := Nat.eq_zero_or_pos N
  · intro n hn
    obtain rfl := Nat.le_zero.1 hn
    have hT : 0 ≤ T := by simpa using hNT
    have h1 : δ₀ ≤ Real.exp (L * T) * δ₀ :=
      le_mul_of_one_le_left ((norm_nonneg _).trans hδ)
        (Real.one_le_exp (mul_nonneg hP.L_nonneg hT))
    have h2 : 0 ≤ T * Real.exp (L * T) * c :=
      mul_nonneg (mul_nonneg hT (Real.exp_pos _).le) hc₀
    have h3 : ‖Y 0 - A (t₀ + ((0 : ℕ) : ℝ) * h)‖ = ‖Y 0 - A t₀‖ := by simp
    rw [h3]
    linarith
  have hh : 0 ≤ h := by simpa [uniformGrid] using hY.grid.mono 0 hN
  have e : ∀ n : ℕ, uniformGrid t₀ h (n + 1) = t₀ + ((n : ℝ) + 1) * h := fun n => by
    simp [uniformGrid]
  have e0 : uniformGrid t₀ h 0 = t₀ := by simp [uniformGrid]
  have hP' : DLRAProblem F A (uniformGrid t₀ h 0) (uniformGrid t₀ h N) ρ L B := by
    rw [e0]
    exact hP
  have hc' : ContinuousOn (Function.uncurry F)
      (tubeSet A (uniformGrid t₀ h 0) (uniformGrid t₀ h N) ρ) := by
    rw [e0]
    exact hc
  have hb : ∀ k ≤ N, Real.exp (L * (uniformGrid t₀ h k - uniformGrid t₀ h 0)) *
      ‖Y 0 - A (uniformGrid t₀ h 0)‖ + ∑ j ∈ range k,
        Real.exp (L * (uniformGrid t₀ h k - uniformGrid t₀ h (j + 1))) * (h * c) ≤
      Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c := fun k hk =>
    uniformGrid_errorBound_le t₀ hP.L_nonneg hh hc₀
      ((mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) hh).trans hNT) (norm_nonneg _)
      (by rw [e0]; exact hδ)
  intro n hn
  refine (hY.norm_sub_le_of_tube
    (R := fun _ => Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c) (δ := fun _ => h * c)
    hP' hc' ?_ (fun k hk => hb k hk.le) ?_ n hn).trans (hb n hn)
  · intro k hk Y₀ Y₁ hY₀ hstep
    rw [e k] at hstep ⊢
    exact hM k hk Y₀ Y₁ hY₀ hstep
  · intro k _
    rw [uniformGrid_succ_sub]
    exact hsmall

end Uniform

/-- Non-vacuity of the tube theorem, for the nonzero constant field `F t x = v` with the solution
`A t = x₀ + (t - τ 0) v`: the field is Lipschitz with constant `0` and bounded by `‖v‖` on every
tube, the exact solution started at `Y n` is `Y n + (t - τ n) v`, and the theorem bounds the
distance of `Y n` from `A (τ n)` by the initial distance plus the sum of the defects `δ k`. -/
example {v x₀ : E} {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → E} {δ : ℕ → ℝ} {ρ r : ℝ} (hτ : IsGrid τ N)
    (hY : ∀ n < N, ‖Y (n + 1) - (Y n + (τ (n + 1) - τ n) • v)‖ ≤ δ n)
    (hR : ∀ n < N, ‖Y 0 - x₀‖ + ∑ k ∈ range n, δ k ≤ r)
    (hsmall : ∀ n < N, r + 2 * ‖v‖ * (τ (n + 1) - τ n) < ρ) :
    ∀ n ≤ N, ‖Y n - (x₀ + (τ n - τ 0) • v)‖ ≤ ‖Y 0 - x₀‖ + ∑ k ∈ range n, δ k := by
  have aff : ∀ (y₀ : E) (a b : ℝ),
      ODESolution (fun _ _ => v) (fun t => y₀ + (t - a) • v) a b := fun y₀ a b =>
    ⟨by fun_prop, fun t _ => by
      have hd : HasDerivAt (fun t : ℝ => y₀ + (t - a) • v) v t := by
        simpa using (((hasDerivAt_id t).sub_const a).smul_const v).const_add y₀
      exact hd.hasDerivWithinAt⟩
  have key := IsLipschitzOnTube.norm_sub_le_of_fan (F := fun _ _ => v)
    (A := fun t => x₀ + (t - τ 0) • v) (τ := τ) (N := N) (Y := Y)
    (Φ := fun n t => Y n + (t - τ n) • v) (δ := δ) (ρ := ρ) (L := 0) (B := ‖v‖)
    (R := fun _ => r) (fun t _ x y _ _ => by simp) le_rfl (fun t _ x _ => le_rfl)
    (norm_nonneg v) hτ (aff x₀ (τ 0) (τ N))
    (fun n hn _ => ⟨aff (Y n) (τ n) (τ (n + 1)), by simp, hY n hn⟩)
    (fun n hn => by simpa using hR n hn) hsmall
  intro n hn
  simpa using key n hn

end LeanDLRA
