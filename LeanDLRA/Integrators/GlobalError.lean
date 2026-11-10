import LeanDLRA.DLRA.Defs
import LeanDLRA.Integrators.Defs
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Foundations.Localization
import LeanDLRA.Foundations.OneSided

/-!
# Global error from local errors on a time grid

A one-step method produces values `Y 0, Y 1, …, Y N` at the times `τ 0 ≤ τ 1 ≤ ⋯ ≤ τ N` of a grid.
Its global error `‖Y n - A (τ n)‖` against an exact solution `A` is bounded by the classical
argument known as **Lady Windermere's fan**: on each step `n` let `Φ n` be the exact solution
started at the numerical value, `Φ n (τ n) = Y n` (the curves `Φ 0, Φ 1, …` form the *fan*,
`IsExactFan`). The error of step `n` is then split into

* the **local error** `‖Y (n + 1) - Φ n (τ (n + 1))‖ ≤ δ n`, a property of the method alone
  (`HasLocalError`), and
* the **propagated error** `‖Φ n (τ (n + 1)) - A (τ (n + 1))‖ ≤ a n ‖Y n - A (τ n)‖`, a property of
  the exact flow (`FanStable`).

Stability is needed only along the fan, between `Φ n` and `A`, not between arbitrary solutions;
this is why conditions on `F` near `A` (on a tube, `DLRAProblem`) or one-sided conditions suffice.
Adding up gives **G1**:

  `‖Y n - A (τ n)‖ ≤ (∏_{k<n} a k) ‖Y 0 - A (τ 0)‖ + ∑_{k<n} (∏_{k<j<n} a j) δ k`.

For an `L`-Lipschitz field `a k = exp (L (τ (k + 1) - τ k))`, and the bound reads
`e^{L (τ n - τ 0)} ‖Y 0 - A (τ 0)‖ + ∑_{k<n} e^{L (τ n - τ (k+1))} δ k`; on the uniform grid
`τ n = t₀ + n h` with local errors `δ k ≤ ℓ` it gives `e^{L n h} (‖Y 0 - A t₀‖ + n ℓ)`
(`lady_windermere`).

## Main results

* `LeanDLRA.discrete_gronwall_prod_le`: `e (n + 1) ≤ a n e n + b n` ⟹ the product-sum bound.
* `LeanDLRA.FanStable.norm_sub_le`, `LeanDLRA.IsExactFan.norm_sub_le`: G1.
* `LeanDLRA.fanStable_of_inner_le`, `LeanDLRA.IsOneSidedLipschitzFieldOn.fanStable`,
  `LeanDLRA.IsOneSidedLipschitzField.fanStable`, `LeanDLRA.IsLipschitzFieldOn.fanStable`,
  `LeanDLRA.IsLipschitzField.fanStable`, `LeanDLRA.IsLipschitzOnTube.fanStable`,
  `LeanDLRA.DLRAProblem.fanStable`: stability along the fan from conditions on `F`.
* `LeanDLRA.exists_isExactFan`: the fan exists for Lipschitz fields continuous in time;
  `LeanDLRA.IsLipschitzField.norm_sub_le_of_hasLocalError`: G1 without a fan in the hypotheses.
* `LeanDLRA.perturbed_iteration_le_prod` (G1′): comparison with a stable one-step map.
* `LeanDLRA.amplified_sum_le_prod` (G1″): the recursion `e (n + 1) ≤ a n (e n + c n)`.
* `LeanDLRA.IsRun.abs_sub_le`, `LeanDLRA.IsRun.eq_of_isExactFor`: conservation and exactness
  along a run.

## Implementation notes

The `example`s at the end restate `lady_windermere`, `lady_windermere_sum`,
`lady_windermere_of_le`, `InexactSubsteps.lady_windermere_defect`, both
`lady_windermere_oneSided`, `perturbed_iteration_le` and `amplified_sum_le` verbatim and prove them
from the grid theorems; the original proofs are unchanged.
-/

open Set Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

/-! ### Discrete Grönwall inequalities with per-step factors -/

section Discrete

/-- **Discrete Grönwall inequality with per-step factors.** If `e (n + 1) ≤ a n e n + b n` for
`n < N` with `a n ≥ 0`, then for `n ≤ N`

  `e n ≤ (∏_{k<n} a k) e 0 + ∑_{k<n} (∏_{k<j<n} a j) b k`.

No sign condition on `e` or `b` is needed. For a constant factor this is
`discrete_gronwall_le`. -/
theorem discrete_gronwall_prod_le {e a b : ℕ → ℝ} {N : ℕ} (ha : ∀ n < N, 0 ≤ a n)
    (he : ∀ n < N, e (n + 1) ≤ a n * e n + b n) :
    ∀ n ≤ N, e n ≤ (∏ k ∈ range n, a k) * e 0 +
      ∑ k ∈ range n, (∏ j ∈ Ico (k + 1) n, a j) * b k := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have hsum : ∑ k ∈ range (n + 1), (∏ j ∈ Ico (k + 1) (n + 1), a j) * b k
        = a n * ∑ k ∈ range n, (∏ j ∈ Ico (k + 1) n, a j) * b k + b n := by
      rw [sum_range_succ, Finset.Ico_self, Finset.prod_empty, one_mul, mul_sum]
      congr 1
      refine sum_congr rfl fun k hk => ?_
      rw [prod_Ico_succ_top (mem_range.1 hk)]
      ring
    rw [hsum, prod_range_succ]
    calc e (n + 1) ≤ a n * e n + b n := he n (by omega)
      _ ≤ a n * ((∏ k ∈ range n, a k) * e 0 +
            ∑ k ∈ range n, (∏ j ∈ Ico (k + 1) n, a j) * b k) + b n :=
        add_le_add_left (mul_le_mul_of_nonneg_left h1 (ha n (by omega))) _
      _ = _ := by ring

/-- **G1″: amplified recursion with per-step factors.** If `e (n + 1) ≤ a n (e n + c n)` for
`n < N` with `a n ≥ 0` (the error of an implicit step: the defect `c n` is added before the
step amplifies by `a n`), then

  `e n ≤ (∏_{k<n} a k) e 0 + ∑_{k<n} (∏_{k≤j<n} a j) c k`.

`amplified_sum_le` is the constant-factor case, coarsened to `(max 1 a)ⁿ (e 0 + ∑ c k)`. -/
theorem amplified_sum_le_prod {e a c : ℕ → ℝ} {N : ℕ} (ha : ∀ n < N, 0 ≤ a n)
    (hrec : ∀ n < N, e (n + 1) ≤ a n * (e n + c n)) :
    ∀ n ≤ N, e n ≤ (∏ k ∈ range n, a k) * e 0 + ∑ k ∈ range n, (∏ j ∈ Ico k n, a j) * c k := by
  intro n hn
  refine (discrete_gronwall_prod_le (b := fun n => a n * c n) ha
    (fun n hn => (hrec n hn).trans_eq (mul_add _ _ _)) n hn).trans_eq ?_
  congr 1
  refine sum_congr rfl fun k hk => ?_
  rw [prod_eq_prod_Ico_succ_bot (mem_range.1 hk)]
  ring

end Discrete

/-! ### Grids -/

section Grid

/-- A grid is a sequence that is monotone on `{0, …, N}`. -/
theorem isGrid_iff_monotoneOn {τ : ℕ → ℝ} {N : ℕ} : IsGrid τ N ↔ MonotoneOn τ (Set.Iic N) := by
  refine ⟨fun hτ m _ n hn hmn => ?_, fun h =>
    ⟨fun n hn => h (Set.mem_Iic.2 hn.le) (Set.mem_Iic.2 hn) (Nat.le_succ n)⟩⟩
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih =>
    have hk : k < N := Nat.lt_of_succ_le (Set.mem_Iic.1 hn)
    exact (ih (Set.mem_Iic.2 hk.le)).trans (hτ.mono k hk)

/-- Every step interval `[τ n, τ (n + 1)]`, `n < N`, of a grid lies in `[τ 0, τ N]`. -/
theorem IsGrid.Icc_subset {τ : ℕ → ℝ} {N n : ℕ} (hτ : IsGrid τ N) (hn : n < N) :
    Icc (τ n) (τ (n + 1)) ⊆ Icc (τ 0) (τ N) := by
  have h := isGrid_iff_monotoneOn.1 hτ
  exact Icc_subset_Icc (h (Set.mem_Iic.2 (Nat.zero_le N)) (Set.mem_Iic.2 hn.le) (Nat.zero_le n))
    (h (Set.mem_Iic.2 hn) (Set.mem_Iic.2 le_rfl) hn)

/-- The products of the exponential factors of a grid telescope:
`∏_{m≤j<n} exp (c (τ (j + 1) - τ j)) = exp (c (τ n - τ m))`. -/
theorem prod_Ico_exp_mul_sub (τ : ℕ → ℝ) (c : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ∏ j ∈ Ico m n, Real.exp (c * (τ (j + 1) - τ j)) = Real.exp (c * (τ n - τ m)) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ k hmk ih =>
    rw [prod_Ico_succ_top hmk, ih, ← Real.exp_add]
    congr 1
    ring

end Grid

/-! ### G1: global error from local errors and stability along the fan -/

section G1

variable {E : Type*} [NormedAddCommGroup E]

/-- **G1, primary form.** Let the curves `Φ n` start at the numerical values, `Φ n (τ n) = Y n`,
be stable along the fan with factors `a n ≥ 0` (`FanStable A τ N Φ a`), and let the local errors
be `‖Y (n + 1) - Φ n (τ (n + 1))‖ ≤ δ n`. Then for `n ≤ N`

  `‖Y n - A (τ n)‖ ≤ (∏_{k<n} a k) ‖Y 0 - A (τ 0)‖ + ∑_{k<n} (∏_{k<j<n} a j) δ k`:

the initial error and each local error are propagated by the factors of the later steps.
Nothing is assumed about `Φ n` beyond its two ends; `IsExactFan.norm_sub_le` is the form with
exact solutions and the method's local error. -/
theorem FanStable.norm_sub_le {A : ℝ → E} {τ : ℕ → ℝ} {N : ℕ} {Φ : ℕ → ℝ → E} {a : ℕ → ℝ}
    {Y : ℕ → E} {δ : ℕ → ℝ} (hS : FanStable A τ N Φ a) (ha : ∀ n < N, 0 ≤ a n)
    (h₀ : ∀ n < N, Φ n (τ n) = Y n) (hloc : ∀ n < N, ‖Y (n + 1) - Φ n (τ (n + 1))‖ ≤ δ n) :
    ∀ n ≤ N, ‖Y n - A (τ n)‖ ≤ (∏ k ∈ range n, a k) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, (∏ j ∈ Ico (k + 1) n, a j) * δ k :=
  discrete_gronwall_prod_le (e := fun n => ‖Y n - A (τ n)‖) ha fun n hn =>
    calc ‖Y (n + 1) - A (τ (n + 1))‖
        ≤ ‖Y (n + 1) - Φ n (τ (n + 1))‖ + ‖Φ n (τ (n + 1)) - A (τ (n + 1))‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ δ n + a n * ‖Φ n (τ n) - A (τ n)‖ := add_le_add (hloc n hn) (hS n hn)
      _ = a n * ‖Y n - A (τ n)‖ + δ n := by rw [h₀ n hn, add_comm]

variable [NormedSpace ℝ E] {F : ℝ → E → E} {A : ℝ → E} {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → E}
  {Φ : ℕ → ℝ → E}

/-- **G1**, the global error bound on a grid. For an exact-flow fan `Φ` of the values `Y n` that is
stable with factors `a n ≥ 0`, and steps with local errors `δ n` (`HasLocalError`),

  `‖Y n - A (τ n)‖ ≤ (∏_{k<n} a k) ‖Y 0 - A (τ 0)‖ + ∑_{k<n} (∏_{k<j<n} a j) δ k`

for `n ≤ N`. The factors come from conditions on `F` along the fan (`IsLipschitzField.fanStable`
and its variants); on the uniform grid with `a k = exp (L h)` this is `lady_windermere_sum`. -/
theorem IsExactFan.norm_sub_le {a δ : ℕ → ℝ} (hΦ : IsExactFan F τ N Y Φ)
    (hS : FanStable A τ N Φ a) (ha : ∀ n < N, 0 ≤ a n)
    (hloc : ∀ n < N, HasLocalError F (τ n) (τ (n + 1)) (Y n) (Y (n + 1)) (δ n)) :
    ∀ n ≤ N, ‖Y n - A (τ n)‖ ≤ (∏ k ∈ range n, a k) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, (∏ j ∈ Ico (k + 1) n, a j) * δ k :=
  hS.norm_sub_le ha hΦ.start (hΦ.norm_sub_le_of_hasLocalError hloc)

/-! ### Stability along the fan -/

/-- **Fan stability from a Lipschitz condition on a region.** If `F` is `L`-Lipschitz (`L ≥ 0`)
on a region `D` that contains the fan and the reference solution on every step, the fan is stable
with the factors `exp (L (τ (n + 1) - τ n))` (Grönwall on each step). -/
theorem IsLipschitzFieldOn.fanStable {D : Set (ℝ × E)} {L : ℝ} (hF : IsLipschitzFieldOn F D L)
    (hL : 0 ≤ L) (hτ : IsGrid τ N) (hA : ODESolution F A (τ 0) (τ N))
    (hΦ : IsExactFan F τ N Y Φ) (hΦD : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)), (t, Φ n t) ∈ D)
    (hAD : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)), (t, A t) ∈ D) :
    FanStable A τ N Φ fun n => Real.exp (L * (τ (n + 1) - τ n)) := fun n hn => by
  have hsub := hτ.Icc_subset hn
  have hle := hτ.mono n hn
  have hAn : ODESolution F A (τ n) (τ (n + 1)) :=
    hA.mono (hsub (left_mem_Icc.2 hle)).1 (hsub (right_mem_Icc.2 hle)).2
  have hlip := (isLipschitzFieldOn_iff_lipschitzOnWith hL).1 hF
  have h := dist_le_of_trajectories_ODE_of_mem (v := F) (s := fun t => {x | (t, x) ∈ D})
    (fun t _ => hlip t) (hΦ.sol n hn).cont (hΦ.sol n hn).deriv (hΦD n hn) hAn.cont hAn.deriv
    (hAD n hn) le_rfl (τ (n + 1)) ⟨hle, le_rfl⟩
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL] at h
  exact h.trans_eq (mul_comm _ _)

/-- **Fan stability for a globally Lipschitz field**: factors `exp (L (τ (n + 1) - τ n))`. -/
theorem IsLipschitzField.fanStable {L : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hτ : IsGrid τ N) (hA : ODESolution F A (τ 0) (τ N)) (hΦ : IsExactFan F τ N Y Φ) :
    FanStable A τ N Φ fun n => Real.exp (L * (τ (n + 1) - τ n)) :=
  (isLipschitzField_iff_univ.1 hF).fanStable hL hτ hA hΦ (fun _ _ _ _ => trivial)
    fun _ _ _ _ => trivial

/-- **Fan stability on a tube.** If `F` is `L`-Lipschitz on the tube of radius `ρ` around `A`
and the fan stays in the tube, the fan is stable with factors `exp (L (τ (n + 1) - τ n))`. -/
theorem IsLipschitzOnTube.fanStable {ρ L : ℝ} (hF : IsLipschitzOnTube F A (τ 0) (τ N) ρ L)
    (hL : 0 ≤ L) (hτ : IsGrid τ N) (hA : ODESolution F A (τ 0) (τ N))
    (hΦ : IsExactFan F τ N Y Φ) (hin : ∀ n < N, ∀ t ∈ Icc (τ n) (τ (n + 1)), ‖Φ n t - A t‖ ≤ ρ) :
    FanStable A τ N Φ fun n => Real.exp (L * (τ (n + 1) - τ n)) :=
  (isLipschitzOnTube_iff.1 hF).fanStable hL hτ hA hΦ
    (fun n hn t ht =>
      ⟨hτ.Icc_subset hn (Ico_subset_Icc_self ht), hin n hn t (Ico_subset_Icc_self ht)⟩)
    fun n hn t ht => ⟨hτ.Icc_subset hn (Ico_subset_Icc_self ht),
      by simpa using (norm_nonneg _).trans (hin n hn t (Ico_subset_Icc_self ht))⟩

/-- **Existence of the exact-flow fan** for a Lipschitz field that is continuous in time: on
every step `[τ n, τ (n + 1)]` of a grid there is an exact solution started at `Y n`. Global
error bounds therefore need no fan in their hypotheses
(`IsLipschitzField.norm_sub_le_of_hasLocalError`). -/
theorem exists_isExactFan {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : ℝ → E → E} {τ : ℕ → ℝ} {N : ℕ} {L : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hc : ∀ x, Continuous fun t => F t x) (hτ : IsGrid τ N) (Y : ℕ → E) :
    ∃ Φ, IsExactFan F τ N Y Φ := by
  have h : ∀ n, ∃ φ : ℝ → E, n < N → ODESolution F φ (τ n) (τ (n + 1)) ∧ φ (τ n) = Y n := by
    intro n
    by_cases hn : n < N
    · obtain ⟨K, hK⟩ := (isCompact_Icc (a := τ n) (b := τ (n + 1))).exists_bound_of_continuousOn
        (hc 0).continuousOn
      obtain ⟨φ, hφ, hφ₀⟩ := exists_ODESolution_of_linearGrowth hF hL hK
        (fun x => (hc x).continuousOn) (hτ.mono n hn) (Y n)
      exact ⟨φ, fun _ => ⟨hφ, hφ₀⟩⟩
    · exact ⟨fun _ => Y n, fun h => absurd h hn⟩
  choose Φ hΦ using h
  exact ⟨Φ, fun n hn => (hΦ n hn).1, fun n hn => (hΦ n hn).2⟩

/-- **G1 for Lipschitz fields, without a fan.** Let `F` be `L`-Lipschitz (`L ≥ 0`) and continuous
in time, `A` an exact solution on `[τ 0, τ N]`, and let step `n` of the numerical method have
local error `δ n`. Then for `n ≤ N`

  `‖Y n - A (τ n)‖ ≤ e^{L (τ n - τ 0)} ‖Y 0 - A (τ 0)‖ + ∑_{k<n} e^{L (τ n - τ (k + 1))} δ k`. -/
theorem IsLipschitzField.norm_sub_le_of_hasLocalError {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {F : ℝ → E → E} {A : ℝ → E} {τ : ℕ → ℝ} {N : ℕ}
    {Y : ℕ → E} {L : ℝ} {δ : ℕ → ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hc : ∀ x, Continuous fun t => F t x) (hτ : IsGrid τ N) (hA : ODESolution F A (τ 0) (τ N))
    (hloc : ∀ n < N, HasLocalError F (τ n) (τ (n + 1)) (Y n) (Y (n + 1)) (δ n)) :
    ∀ n ≤ N, ‖Y n - A (τ n)‖ ≤ Real.exp (L * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k := by
  obtain ⟨Φ, hΦ⟩ := exists_isExactFan hF hL hc hτ Y
  intro n hn
  refine (hΦ.norm_sub_le (hF.fanStable hL hτ hA hΦ) (fun _ _ => (Real.exp_pos _).le) hloc n
    hn).trans_eq ?_
  rw [range_eq_Ico, prod_Ico_exp_mul_sub τ L (Nat.zero_le n)]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  rw [prod_Ico_exp_mul_sub τ L (mem_Ico.1 hk).2]

end G1

section OneSided

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : ℝ → E → E} {A : ℝ → E}
  {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → E} {Φ : ℕ → ℝ → E}

/-- **Fan stability from the one-sided inequality along the fan**, with per-step constants `ℓ n`
of any sign: if `⟪F t (Φ n t) - F t (A t), Φ n t - A t⟫ ≤ ℓ n ‖Φ n t - A t‖²` on step `n`, the
fan is stable with the factors `exp (ℓ n (τ (n + 1) - τ n))`. This is the weakest form; the
conditions on `F` below are its instances. -/
theorem fanStable_of_inner_le (hτ : IsGrid τ N) (hA : ODESolution F A (τ 0) (τ N))
    (hΦ : IsExactFan F τ N Y Φ) {ℓ : ℕ → ℝ}
    (h : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)),
      ⟪F t (Φ n t) - F t (A t), Φ n t - A t⟫ ≤ ℓ n * ‖Φ n t - A t‖ ^ 2) :
    FanStable A τ N Φ fun n => Real.exp (ℓ n * (τ (n + 1) - τ n)) := fun n hn => by
  have hsub := hτ.Icc_subset hn
  have hle := hτ.mono n hn
  have hAn : ODESolution F A (τ n) (τ (n + 1)) :=
    hA.mono (hsub (left_mem_Icc.2 hle)).1 (hsub (right_mem_Icc.2 hle)).2
  exact (hΦ.sol n hn).norm_sub_le_exp_of_inner_le hAn (h n hn) (τ (n + 1)) ⟨hle, le_rfl⟩

/-- **Fan stability for a field that is one-sided Lipschitz on a region** containing the fan and
the reference solution: factors `exp (ℓ (τ (n + 1) - τ n))`, below `1` for `ℓ < 0`. -/
theorem IsOneSidedLipschitzFieldOn.fanStable {D : Set (ℝ × E)} {ℓ : ℝ}
    (hF : IsOneSidedLipschitzFieldOn F D ℓ) (hτ : IsGrid τ N) (hA : ODESolution F A (τ 0) (τ N))
    (hΦ : IsExactFan F τ N Y Φ) (hΦD : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)), (t, Φ n t) ∈ D)
    (hAD : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)), (t, A t) ∈ D) :
    FanStable A τ N Φ fun n => Real.exp (ℓ * (τ (n + 1) - τ n)) :=
  fanStable_of_inner_le (ℓ := fun _ => ℓ) hτ hA hΦ fun n hn t ht =>
    hF (hΦD n hn t ht) (hAD n hn t ht)

/-- **Fan stability for a one-sided Lipschitz field** (any real `ℓ`): factors
`exp (ℓ (τ (n + 1) - τ n))`. -/
theorem IsOneSidedLipschitzField.fanStable {ℓ : ℝ} (hF : IsOneSidedLipschitzField F ℓ)
    (hτ : IsGrid τ N) (hA : ODESolution F A (τ 0) (τ N)) (hΦ : IsExactFan F τ N Y Φ) :
    FanStable A τ N Φ fun n => Real.exp (ℓ * (τ (n + 1) - τ n)) :=
  fanStable_of_inner_le (ℓ := fun _ => ℓ) hτ hA hΦ fun _ _ t _ => hF t _ _

/-- **Fan stability for a DLRA problem**: if the fan stays in the tube of the problem, it is
stable with the factors `exp (L (τ (n + 1) - τ n))`. -/
theorem DLRAProblem.fanStable {ρ L B : ℝ} (hP : DLRAProblem F A (τ 0) (τ N) ρ L B)
    (hτ : IsGrid τ N) (hΦ : IsExactFan F τ N Y Φ)
    (hin : ∀ n < N, ∀ t ∈ Icc (τ n) (τ (n + 1)), ‖Φ n t - A t‖ ≤ ρ) :
    FanStable A τ N Φ fun n => Real.exp (L * (τ (n + 1) - τ n)) :=
  hP.lipschitz.fanStable hP.L_nonneg hτ hP.sol hΦ hin

end OneSided

/-! ### G1′: comparison with a stable one-step map -/

section Perturbed

variable {E : Type*} [NormedAddCommGroup E]

/-- **G1′: a perturbed iteration stays close to a stable one.** Let the one-step maps `Ψ n` be
`a n`-Lipschitz (`a n ≥ 0`), `u (n + 1) = Ψ n (u n)`, and let `Y` follow the maps up to defects,
`‖Y (n + 1) - Ψ n (Y n)‖ ≤ η n`. Then for `n ≤ N`

  `‖Y n - u n‖ ≤ (∏_{k<n} a k) ‖Y 0 - u 0‖ + ∑_{k<n} (∏_{k<j<n} a j) η k`.

Here stability is a property of the method, not of the exact flow. `perturbed_iteration_le` is
the case `a n = 1 + C h`, `η n = η`. -/
theorem perturbed_iteration_le_prod {Ψ : ℕ → E → E} {a η : ℕ → ℝ} {N : ℕ} {u Y : ℕ → E}
    (ha : ∀ n < N, 0 ≤ a n) (hΨ : ∀ n < N, ∀ x y, ‖Ψ n x - Ψ n y‖ ≤ a n * ‖x - y‖)
    (hu : ∀ n < N, u (n + 1) = Ψ n (u n)) (hY : ∀ n < N, ‖Y (n + 1) - Ψ n (Y n)‖ ≤ η n) :
    ∀ n ≤ N, ‖Y n - u n‖ ≤ (∏ k ∈ range n, a k) * ‖Y 0 - u 0‖ +
      ∑ k ∈ range n, (∏ j ∈ Ico (k + 1) n, a j) * η k :=
  discrete_gronwall_prod_le (e := fun n => ‖Y n - u n‖) ha fun n hn =>
    calc ‖Y (n + 1) - u (n + 1)‖ ≤ ‖Y (n + 1) - Ψ n (Y n)‖ + ‖Ψ n (Y n) - Ψ n (u n)‖ := by
          rw [hu n hn]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ η n + a n * ‖Y n - u n‖ := add_le_add (hY n hn) (hΨ n hn _ _)
      _ = a n * ‖Y n - u n‖ + η n := add_comm _ _

end Perturbed

/-! ### Conservation and exactness along a run -/

section Run

/-- **Conservation along a run.** If every forward step of `M` changes the quantity `I` by at
most `ϑ`, then after `n` steps of a run the change is at most `n ϑ`. -/
theorem IsRun.abs_sub_le {E : Type*} {M : StepRel E} {I : E → ℝ} {ϑ : ℝ} {τ : ℕ → ℝ} {N : ℕ}
    {Y : ℕ → E} (hM : M.ConservesUpTo I ϑ) (hY : IsRun M τ N Y) :
    ∀ n ≤ N, |I (Y n) - I (Y 0)| ≤ n * ϑ := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    calc |I (Y (n + 1)) - I (Y 0)| ≤ |I (Y (n + 1)) - I (Y n)| + |I (Y n) - I (Y 0)| :=
          _root_.abs_sub_le _ _ _
      _ ≤ ϑ + n * ϑ :=
          add_le_add (hM (hY.grid.mono n (by omega)) (hY.step n (by omega))) (ih (by omega))
      _ = ((n + 1 : ℕ) : ℝ) * ϑ := by push_cast; ring

/-- **Exactness along a run.** If `M` is exact for `A` and `F t Y = Ȧ(t)` on every step, a run
started at `A (τ 0)` reproduces `A` at every grid point. -/
theorem IsRun.eq_of_isExactFor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : StepRel E} {F : ℝ → E → E} {A : ℝ → E} {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → E}
    (hM : M.IsExactFor F A) (hA : ∀ n < N, IsDerivRHS F A (τ n) (τ (n + 1)))
    (hY : IsRun M τ N Y) (h0 : Y 0 = A (τ 0)) : ∀ n ≤ N, Y n = A (τ n) := by
  intro n
  induction n with
  | zero => intro _; exact h0
  | succ n ih =>
    intro hn
    have hstep := hY.step n (by omega)
    rw [ih (by omega)] at hstep
    exact hM (hY.grid.mono n (by omega)) (hA n (by omega)) hstep

end Run

/-! ### Non-vacuity: a linear field on a non-uniform grid -/

section Examples

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `t ↦ exp (c (t - s)) y` solves `y' = c y`. -/
private theorem odeSolution_exp_smul_aux (c s : ℝ) (y : E) (a b : ℝ) :
    ODESolution (fun _ x => c • x) (fun t => Real.exp (c * (t - s)) • y) a b := by
  have hd : ∀ t, HasDerivAt (fun t => Real.exp (c * (t - s)) • y)
      (c • (Real.exp (c * (t - s)) • y)) t := fun t => by
    have h1 : HasDerivAt (fun t => c * (t - s)) c t := by
      simpa using ((hasDerivAt_id t).sub_const s).const_mul c
    convert h1.exp.smul_const y using 1
    rw [smul_smul, mul_comm c (Real.exp (c * (t - s)))]
  exact ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => (hd t).hasDerivWithinAt⟩

/-- **G1 on a non-uniform grid, with unequal factors.** For the linear field `F(t, x) = c x`
(one-sided Lipschitz with constant `c`) and the grid `τ n = n²` (step sizes `2 n + 1`), values
`Y n` that follow the exact flow up to defects `δ n` stay within the G1 bound of the exact
solution `exp (c t) x₀`. The per-step factors `exp (c (2 n + 1))` differ from step to step for
`c ≠ 0`, and are below `1` for `c < 0`. -/
example (c : ℝ) (x₀ : E) (Y : ℕ → E) (δ : ℕ → ℝ) (N : ℕ)
    (hY : ∀ n < N, ‖Y (n + 1) - Real.exp (c * (2 * n + 1)) • Y n‖ ≤ δ n) :
    ∀ n ≤ N, ‖Y n - Real.exp (c * (n : ℝ) ^ 2) • x₀‖ ≤
      (∏ k ∈ range n, Real.exp (c * (2 * k + 1))) * ‖Y 0 - x₀‖ +
        ∑ k ∈ range n, (∏ j ∈ Ico (k + 1) n, Real.exp (c * (2 * j + 1))) * δ k := by
  have hstep : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 2 - (n : ℝ) ^ 2 = 2 * n + 1 := fun n => by
    push_cast
    ring
  have hτ : IsGrid (fun n : ℕ => (n : ℝ) ^ 2) N :=
    ⟨fun n _ => by nlinarith [hstep n, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩
  have hfan : IsExactFan (fun _ x => c • x) (fun n : ℕ => (n : ℝ) ^ 2) N Y
      fun n t => Real.exp (c * (t - (n : ℝ) ^ 2)) • Y n :=
    ⟨fun n _ => odeSolution_exp_smul_aux c _ (Y n) _ _, fun n _ => by simp⟩
  have hA : ODESolution (fun _ x => c • x) (fun t => Real.exp (c * (t - 0)) • x₀)
      (((0 : ℕ) : ℝ) ^ 2) ((N : ℝ) ^ 2) := odeSolution_exp_smul_aux c 0 x₀ _ _
  have hF : IsOneSidedLipschitzField (fun _ (x : E) => c • x) c := fun _ x y => by
    rw [← smul_sub, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hS : FanStable (fun t => Real.exp (c * (t - 0)) • x₀) (fun n : ℕ => (n : ℝ) ^ 2) N
      (fun n t => Real.exp (c * (t - (n : ℝ) ^ 2)) • Y n)
      fun n => Real.exp (c * (2 * n + 1)) := fun n hn => by
    simpa only [hstep] using hF.fanStable hτ hA hfan n hn
  intro n hn
  have key := hS.norm_sub_le (δ := δ) (fun _ _ => (Real.exp_pos _).le) hfan.start
    (fun k hk => by simpa only [hstep] using hY k hk) n hn
  simpa using key

end Examples

/-! ### The uniform-grid theorems of the library as instances

Each `example` below states one existing theorem verbatim and proves it from the grid theorems
of this file (through `isExactFan_uniformGrid_iff` and `uniformGrid_succ_sub`). -/

section Instances

/-- G1 with a constant factor `q ≥ 1`, coarsened to `qⁿ (‖Y 0 - A (τ 0)‖ + ∑_{k<n} ℓ k)`. -/
private theorem norm_sub_le_pow_mul_of_fanStable {E : Type*} [NormedAddCommGroup E] {A : ℝ → E}
    {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → E} {Φ : ℕ → ℝ → E} {q : ℝ} {ℓ : ℕ → ℝ}
    (hS : FanStable A τ N Φ fun _ => q) (hq : 1 ≤ q) (h₀ : ∀ n < N, Φ n (τ n) = Y n)
    (hloc : ∀ n < N, ‖Y (n + 1) - Φ n (τ (n + 1))‖ ≤ ℓ n) :
    ∀ n ≤ N, ‖Y n - A (τ n)‖ ≤ q ^ n * (‖Y 0 - A (τ 0)‖ + ∑ k ∈ range n, ℓ k) := by
  intro n hn
  refine (hS.norm_sub_le (fun _ _ => zero_le_one.trans hq) h₀ hloc n hn).trans ?_
  simp only [prod_const, card_range, Nat.card_Ico]
  rw [mul_add, mul_sum]
  refine add_le_add le_rfl (sum_le_sum fun k hk => ?_)
  have hk : k < n := mem_range.1 hk
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq (by omega))
    ((norm_nonneg _).trans (hloc k (by omega)))

/-- `lady_windermere_sum` from the grid theorems. -/
private theorem lady_windermere_sum_of_grid {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h))
    {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    {ℓ : ℕ → ℝ} (hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤ ℓ n) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (L * (n * h)) * (‖Y 0 - A t₀‖ + ∑ k ∈ range n, ℓ k) := by
  have e : ∀ n : ℕ, uniformGrid t₀ h (n + 1) = t₀ + ((n : ℝ) + 1) * h := fun n => by
    simp [uniformGrid]
  have e0 : uniformGrid t₀ h 0 = t₀ := by simp [uniformGrid]
  have hfan : IsExactFan F (uniformGrid t₀ h) N Y Φ := isExactFan_uniformGrid_iff.2 ⟨hΦ, hΦ₀⟩
  have hA' : ODESolution F A (uniformGrid t₀ h 0) (uniformGrid t₀ h N) := by
    rw [e0]
    exact hA
  have hS : FanStable A (uniformGrid t₀ h) N Φ fun _ => Real.exp (L * h) := fun n hn => by
    have h1 := hF.fanStable hL (isGrid_uniformGrid hh N) hA' hfan n hn
    beta_reduce at h1 ⊢
    rwa [uniformGrid_succ_sub] at h1
  intro n hn
  have key := norm_sub_le_pow_mul_of_fanStable hS (Real.one_le_exp (mul_nonneg hL hh))
    hfan.start (fun k hk => (e k).symm ▸ hloc k hk) n hn
  rw [e0, ← Real.exp_nat_mul, show (n : ℝ) * (L * h) = L * (n * h) by ring] at key
  exact key

/-- The one-sided fan on the uniform grid, with the factors `exp (ℓ h)` kept as powers. -/
private theorem lady_windermere_oneSided_pow {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {F : ℝ → E → E} {ℓ : ℝ} (hF : IsOneSidedLipschitzField F ℓ)
    {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h))
    {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {lam : ℕ → ℝ}
    (hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤ lam n) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (ℓ * h) ^ n * ‖Y 0 - A t₀‖ +
      ∑ k ∈ range n, Real.exp (ℓ * h) ^ (n - 1 - k) * lam k := by
  have e : ∀ n : ℕ, uniformGrid t₀ h (n + 1) = t₀ + ((n : ℝ) + 1) * h := fun n => by
    simp [uniformGrid]
  have e0 : uniformGrid t₀ h 0 = t₀ := by simp [uniformGrid]
  have hfan : IsExactFan F (uniformGrid t₀ h) N Y Φ := isExactFan_uniformGrid_iff.2 ⟨hΦ, hΦ₀⟩
  have hA' : ODESolution F A (uniformGrid t₀ h 0) (uniformGrid t₀ h N) := by
    rw [e0]
    exact hA
  have hS : FanStable A (uniformGrid t₀ h) N Φ fun _ => Real.exp (ℓ * h) := fun n hn => by
    have h1 := hF.fanStable (isGrid_uniformGrid hh N) hA' hfan n hn
    beta_reduce at h1 ⊢
    rwa [uniformGrid_succ_sub] at h1
  intro n hn
  have key := hS.norm_sub_le (fun _ _ => (Real.exp_pos _).le) hfan.start
    (fun k hk => (e k).symm ▸ hloc k hk) n hn
  simp only [prod_const, card_range, Nat.card_Ico] at key
  rw [e0] at key
  refine key.trans_eq ?_
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [show n - (k + 1) = n - 1 - k by omega]

/-- `lady_windermere_sum` (`Foundations/Gronwall.lean`) is an instance. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → E → E} {L : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    {ℓ : ℕ → ℝ} (hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤ ℓ n) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (L * (n * h)) * (‖Y 0 - A t₀‖ + ∑ k ∈ range n, ℓ k) :=
  lady_windermere_sum_of_grid hF hL hh hA hΦ hΦ₀ hloc

/-- `lady_windermere` (`Foundations/Gronwall.lean`) is an instance. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → E → E} {L : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    {ℓ : ℝ} (hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤ ℓ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * (n * h)) * (‖Y 0 - A t₀‖ + n * ℓ) := by
  intro n hn
  simpa [sum_const, card_range, nsmul_eq_mul] using
    lady_windermere_sum_of_grid hF hL hh hA hΦ hΦ₀ (ℓ := fun _ => ℓ) hloc n hn

/-- `lady_windermere_of_le` (`Foundations/Gronwall.lean`) is an instance. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → E → E} {L : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    {g : ℝ} (hg : 0 ≤ g) (hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤ h * g)
    {T : ℝ} :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * g) := by
  intro n hn hT
  have h1 : ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * (n * h)) * (‖Y 0 - A t₀‖ + n * (h * g)) := by
    simpa [sum_const, card_range, nsmul_eq_mul] using
      lady_windermere_sum_of_grid hF hL hh hA hΦ hΦ₀ (ℓ := fun _ => h * g) hloc n hn
  have hexp : Real.exp (L * (n * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  have hsum : ‖Y 0 - A t₀‖ + n * (h * g) ≤ ‖Y 0 - A t₀‖ + T * g := by
    rw [← mul_assoc]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hT hg)
  have hsum0 : 0 ≤ ‖Y 0 - A t₀‖ + n * (h * g) :=
    add_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg n) (mul_nonneg hh hg))
  exact h1.trans (mul_le_mul hexp hsum hsum0 (Real.exp_pos _).le)

/-- `InexactSubsteps.lady_windermere_defect` (`Integrators/InexactSubsteps.lean`) is an
instance. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : ℝ → E → E} {L : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) {t₀ h : ℝ}
    (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {Y : ℕ → E}
    {Φ : ℕ → ℝ → E} (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {g ρ : ℝ} (hg : 0 ≤ g) (hρ : 0 ≤ ρ)
    (hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤ h * g + ρ) {δ T : ℝ}
    (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * (δ + T * g + n * ρ) := by
  intro n hn hT
  have h1 := lady_windermere_sum_of_grid hF hL hh hA hΦ hΦ₀ (ℓ := fun _ => h * g + ρ) hloc n hn
  rw [sum_const, card_range, nsmul_eq_mul] at h1
  have hexp : Real.exp (L * (n * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  have hT' : (n : ℝ) * h * g ≤ T * g := mul_le_mul_of_nonneg_right hT hg
  have hin : ‖Y 0 - A t₀‖ + n * (h * g + ρ) ≤ δ + T * g + n * ρ := by nlinarith
  have hin0 : 0 ≤ ‖Y 0 - A t₀‖ + n * (h * g + ρ) :=
    add_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg n) (add_nonneg (mul_nonneg hh hg) hρ))
  exact h1.trans (mul_le_mul hexp hin hin0 (Real.exp_pos _).le)

/-- `lady_windermere_oneSided` (`OpenProblems/Curated/StiffAndStochastica.lean`, any real `ℓ`,
per-step local errors) is an instance. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : ℝ → E → E} {ℓ : ℝ}
    (hos : IsOneSidedLipschitzField F ℓ) {t₀ h : ℝ} (hh : 0 ≤ h)
    {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {lam : ℕ → ℝ}
    (hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤ lam n) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (ℓ * (n * h)) * ‖Y 0 - A t₀‖ +
      ∑ k ∈ range n, Real.exp (ℓ * (((n : ℝ) - 1 - k) * h)) * lam k := by
  have hq : ∀ m : ℕ, Real.exp (ℓ * h) ^ m = Real.exp (ℓ * (m * h)) := fun m => by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  intro n hn
  refine (lady_windermere_oneSided_pow hos hh hA hΦ hΦ₀ hloc n hn).trans_eq ?_
  rw [hq]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  obtain ⟨j, rfl⟩ : ∃ j, n = k + 1 + j := ⟨n - (k + 1), by have := mem_range.1 hk; omega⟩
  rw [show k + 1 + j - 1 - k = j by omega, hq]
  congr 2
  push_cast
  ring

/-- `OpenProblems.Stability.lady_windermere_oneSided` (`OpenProblems/Stability/Part1b.lean`,
`ℓ < 0`, time-uniform bound) is an instance. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : ℝ → E → E} {ℓ : ℝ}
    (hF : IsOneSidedLipschitzField F ℓ) (hℓ : ℓ < 0) {t₀ h lam : ℝ} (hh : 0 < h)
    (hlam : 0 ≤ lam) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {Y : ℕ → E}
    {Φ : ℕ → ℝ → E} (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    (hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤ lam) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (ℓ * (n * h)) * ‖Y 0 - A t₀‖ + lam / (1 - Real.exp (ℓ * h)) := by
  intro n hn
  have hq0 : 0 ≤ Real.exp (ℓ * h) := (Real.exp_pos _).le
  have hq1 : Real.exp (ℓ * h) < 1 := Real.exp_lt_one_iff.2 (mul_neg_of_neg_of_pos hℓ hh)
  refine (lady_windermere_oneSided_pow hF hh.le hA hΦ hΦ₀ (lam := fun _ => lam) hloc n
    hn).trans ?_
  rw [← Real.exp_nat_mul, show (n : ℝ) * (ℓ * h) = ℓ * (n * h) by ring, ← sum_mul,
    sum_range_reflect (fun i => Real.exp (ℓ * h) ^ i) n]
  refine add_le_add le_rfl ?_
  rw [mul_comm, div_eq_mul_one_div]
  refine mul_le_mul_of_nonneg_left ?_ hlam
  have hgeom := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hq0 hq1
  rwa [Nat.Ico_zero_eq_range, pow_zero] at hgeom

/-- `perturbed_iteration_le` (`Integrators/EulerBUG.lean`) is an instance of G1′. -/
example {E : Type*} [NormedAddCommGroup E] {Φ : ℕ → E → E} {C h η : ℝ} (hC : 0 ≤ C)
    (hh : 0 ≤ h) (hη : 0 ≤ η) {N : ℕ}
    (hΦ : ∀ n < N, ∀ x y, ‖Φ n x - Φ n y‖ ≤ (1 + C * h) * ‖x - y‖)
    {u Y : ℕ → E} (hu : ∀ n < N, u (n + 1) = Φ n (u n))
    (hY : ∀ n < N, ‖Y (n + 1) - Φ n (Y n)‖ ≤ η) :
    ∀ n ≤ N, ‖Y n - u n‖ ≤ Real.exp (C * (n * h)) * (‖Y 0 - u 0‖ + n * η) := by
  intro n hn
  have hq : 1 ≤ 1 + C * h := le_add_of_nonneg_right (mul_nonneg hC hh)
  have key := perturbed_iteration_le_prod (a := fun _ => 1 + C * h) (η := fun _ => η)
    (fun _ _ => zero_le_one.trans hq) hΦ hu hY n hn
  simp only [prod_const, card_range, Nat.card_Ico] at key
  have hexp : 1 + C * h ≤ Real.exp (C * h) := by linarith [Real.add_one_le_exp (C * h)]
  have hpow : ∀ m ≤ n, (1 + C * h) ^ m ≤ Real.exp (C * (n * h)) := fun m hm =>
    calc (1 + C * h) ^ m ≤ (1 + C * h) ^ n := pow_le_pow_right₀ hq hm
      _ ≤ Real.exp (C * h) ^ n := pow_le_pow_left₀ (zero_le_one.trans hq) hexp n
      _ = Real.exp (C * (n * h)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  refine key.trans ?_
  calc _ ≤ Real.exp (C * (n * h)) * ‖Y 0 - u 0‖ + ∑ k ∈ range n, Real.exp (C * (n * h)) * η :=
        add_le_add (mul_le_mul_of_nonneg_right (hpow n le_rfl) (norm_nonneg _))
          (sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hpow _ (by omega)) hη)
    _ = Real.exp (C * (n * h)) * (‖Y 0 - u 0‖ + n * η) := by
        rw [sum_const, card_range, nsmul_eq_mul]
        ring

/-- `amplified_sum_le` (`Stiff/ImplicitBUG.lean`) is an instance of G1″. -/
example {e c : ℕ → ℝ} {a : ℝ} {N : ℕ} (he : ∀ n, 0 ≤ e n) (hc : ∀ n, 0 ≤ c n)
    (hrec : ∀ n < N, e (n + 1) ≤ a * (e n + c n)) :
    ∀ n ≤ N, e n ≤ max 1 a ^ n * (e 0 + ∑ k ∈ range n, c k) := by
  intro n hn
  have hm : 1 ≤ max 1 a := le_max_left _ _
  have key := amplified_sum_le_prod (a := fun _ => max 1 a) (fun _ _ => zero_le_one.trans hm)
    (fun k hk => (hrec k hk).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (add_nonneg (he k) (hc k)))) n hn
  simp only [prod_const, card_range, Nat.card_Ico] at key
  refine key.trans ?_
  rw [mul_add, mul_sum]
  exact add_le_add le_rfl (sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hm (by omega)) (hc k))

end Instances

end LeanDLRA
