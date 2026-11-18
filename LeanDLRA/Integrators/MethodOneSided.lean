import LeanDLRA.Integrators.Method

/-!
# Runs of a method with a one-sided Lipschitz constant in the error bound

The tube theorem (`LeanDLRA/Integrators/Tube.lean`) and the run theorems of
`LeanDLRA/Integrators/Method.lean` propagate errors with the factor `e^{L t}`, where `L` is the
Lipschitz constant of the field on the tube around the solution `A`. In the proof the Lipschitz
constant plays two parts: it gives the exact solutions started at the numerical values (and the
steps of the globally Lipschitz extension, property (E) of `StepMethod.IsTubeLocal`), and it
bounds the distance of two exact solutions in the tube. For the second part a one-sided
Lipschitz constant `ℓ` on the tube (`IsOneSidedLipschitzFieldOn F (tubeSet A a b ρ) ℓ`) is
enough: the exact solutions started at the numerical values stay in the tube, and the one-sided
inequality between them and `A` bounds their distance by `e^{ℓ t}` times the initial distance
(`IsOneSidedLipschitzFieldOn.fanStable`). The constant `ℓ` is at most `L`
(`DLRAProblem.isOneSidedLipschitzFieldOn`), and it is negative for dissipative problems, where
`L` can be large.

## Main results

* `IsOneSidedLipschitzFieldOn.norm_sub_le_of_fan`: the tube theorem with the exact solutions on
  the steps given, with `e^{ℓ t}` in place of `e^{L t}`; no Lipschitz condition at all.
* `DLRAProblem.norm_sub_le_of_hasLocalError_of_oneSided`,
  `IsRun.adm_and_norm_sub_le_of_tube_of_oneSided`,
  `exists_isRun_norm_sub_le_of_tube_of_oneSided`: the tube theorem for local errors, for runs
  with an invariant, and the existence of a run, with `e^{ℓ t}`.
* `StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_oneSided`: for `0 ≤ ℓ`, a run of a
  tube-local method with `‖Y n - A (t₀ + n h)‖ ≤ e^{ℓ T} δ + T e^{ℓ T} c`.
* `StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_oneSided_neg`: for `ℓ < 0`, a run of every
  length `N` with `‖Y n - A (t₀ + n h)‖ ≤ e^{ℓ n h} δ + (h - ℓ⁻¹) c`, under the smallness
  condition `δ + (h - ℓ⁻¹) c + κ B h < ρ`, which does not contain the final time.
* `uniformGrid_errorBound_le_of_neg`: the sum of the propagated local errors on the uniform grid
  is at most `(h - ℓ⁻¹) c` for `ℓ < 0`.

## Implementation notes

The Lipschitz constant `L` stays in the hypotheses (`DLRAProblem`) of the theorems that construct
exact solutions or runs: there it gives existence, and it does not enter the bounds. The
theorem with the fan given (`IsOneSidedLipschitzFieldOn.norm_sub_le_of_fan`) needs neither `L` nor
completeness. The `example`s at the end restate `StepMethod.IsTubeLocal.exists_run_norm_sub_le`
verbatim and prove it from `StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_oneSided` with
`ℓ = L`, and show that the hypotheses of the two theorems for runs can hold with `ℓ < L`.
-/

open Set Finset

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : ℝ → E → E} {A : ℝ → E}

/-- The Lipschitz constant of a problem on a tube (`DLRAProblem`) is a one-sided Lipschitz constant
on the tube (Cauchy–Schwarz). -/
theorem DLRAProblem.isOneSidedLipschitzFieldOn {a b ρ L B : ℝ} (hP : DLRAProblem F A a b ρ L B) :
    IsOneSidedLipschitzFieldOn F (tubeSet A a b ρ) L :=
  (isLipschitzOnTube_iff.1 hP.lipschitz).isOneSidedLipschitzFieldOn

/-! ### The tube theorem with a one-sided Lipschitz constant -/

section Tube

variable {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → E} {Φ : ℕ → ℝ → E} {δ : ℕ → ℝ} {ρ ℓ L B : ℝ} {R : ℕ → ℝ}

/-- **Global error for values well inside the tube, one-sided form.** Let `F` be one-sided
Lipschitz with constant `ℓ` (of any sign) and bounded by `B` on the tube of radius `ρ` around the
exact solution `A`, let `Φ` be the exact-flow fan of the values `Y n`, and suppose every value has
a margin for one step, `‖Y n - A (τ n)‖ + 2 B (τ (n + 1) - τ n) < ρ`. Then local errors `δ n`
give for `n ≤ N`

  `‖Y n - A (τ n)‖ ≤ e^{ℓ (τ n - τ 0)} ‖Y 0 - A (τ 0)‖ + ∑_{k<n} e^{ℓ (τ n - τ (k + 1))} δ k`.

No Lipschitz condition is assumed. -/
theorem IsExactFan.norm_sub_le_of_near_of_oneSided (hΦ : IsExactFan F τ N Y Φ)
    (hℓ : IsOneSidedLipschitzFieldOn F (tubeSet A (τ 0) (τ N) ρ) ℓ)
    (hFB : IsBoundedOnTube F A (τ 0) (τ N) ρ B) (hB : 0 ≤ B) (hτ : IsGrid τ N)
    (hA : ODESolution F A (τ 0) (τ N))
    (hnear : ∀ n < N, ‖Y n - A (τ n)‖ + 2 * B * (τ (n + 1) - τ n) < ρ)
    (hloc : ∀ n < N, ‖Y (n + 1) - Φ n (τ (n + 1))‖ ≤ δ n) :
    ∀ n ≤ N, ‖Y n - A (τ n)‖ ≤ Real.exp (ℓ * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (ℓ * (τ n - τ (k + 1))) * δ k := by
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
  have hS : FanStable A τ N Φ fun n => Real.exp (ℓ * (τ (n + 1) - τ n)) :=
    hℓ.fanStable hτ hA hΦ
      (fun n hn t ht => ⟨hτ.Icc_subset hn (Ico_subset_Icc_self ht),
        hin n hn t (Ico_subset_Icc_self ht)⟩)
      fun n hn t ht => ⟨hτ.Icc_subset hn (Ico_subset_Icc_self ht),
        by simpa using (norm_nonneg _).trans (hin n hn t (Ico_subset_Icc_self ht))⟩
  intro n hn
  refine (hS.norm_sub_le (fun _ _ => (Real.exp_pos _).le) hΦ.start hloc n hn).trans_eq ?_
  rw [range_eq_Ico, prod_Ico_exp_mul_sub τ ℓ (Nat.zero_le n)]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  rw [prod_Ico_exp_mul_sub τ ℓ (mem_Ico.1 hk).2]

/-- **The tube theorem with a one-sided Lipschitz constant.** Let `F` be one-sided Lipschitz with
constant `ℓ` (of any sign) and bounded by `B` on the tube of radius `ρ` around the exact solution
`A` on `[τ 0, τ N]`. Let `Y n` be numerical values and `R n` radii with
`R n + 2 B (τ (n + 1) - τ n) < ρ`, and suppose that for every step `n` whose start value satisfies
`‖Y n - A (τ n)‖ ≤ R n` the curve `Φ n` is an exact solution on the step started at `Y n` and the
step has local error `‖Y (n + 1) - Φ n (τ (n + 1))‖ ≤ δ n`. If the error bound

  `e^{ℓ (τ n - τ 0)} ‖Y 0 - A (τ 0)‖ + ∑_{k<n} e^{ℓ (τ n - τ (k + 1))} δ k`

is at most `R n` for `n < N`, then it bounds `‖Y n - A (τ n)‖` for all `n ≤ N`. This is
`IsLipschitzOnTube.norm_sub_le_of_fan` with the Lipschitz condition replaced by the one-sided
condition: a Lipschitz constant `L` is a one-sided Lipschitz constant, and `ℓ` may be much
smaller, or negative. -/
theorem IsOneSidedLipschitzFieldOn.norm_sub_le_of_fan
    (hℓ : IsOneSidedLipschitzFieldOn F (tubeSet A (τ 0) (τ N) ρ) ℓ)
    (hFB : IsBoundedOnTube F A (τ 0) (τ N) ρ B) (hB : 0 ≤ B) (hτ : IsGrid τ N)
    (hA : ODESolution F A (τ 0) (τ N))
    (hΦ : ∀ n < N, ‖Y n - A (τ n)‖ ≤ R n → ODESolution F (Φ n) (τ n) (τ (n + 1)) ∧
      Φ n (τ n) = Y n ∧ ‖Y (n + 1) - Φ n (τ (n + 1))‖ ≤ δ n)
    (hR : ∀ n < N, Real.exp (ℓ * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (ℓ * (τ n - τ (k + 1))) * δ k ≤ R n)
    (hsmall : ∀ n < N, R n + 2 * B * (τ (n + 1) - τ n) < ρ) :
    ∀ n ≤ N, ‖Y n - A (τ n)‖ ≤ Real.exp (ℓ * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (ℓ * (τ n - τ (k + 1))) * δ k := by
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
    exact hfan.norm_sub_le_of_near_of_oneSided
      (hℓ.mono (fun p hp => ⟨⟨hp.1.1, hp.1.2.trans hτn⟩, hp.2⟩) le_rfl)
      (hFB.mono le_rfl hτn le_rfl) hB (hτ.of_le hn) (hA.mono le_rfl hτn)
      (fun k hk => (add_le_add (hRn k hk) le_rfl).trans_lt (hsmall k (hk.trans_le hn)))
      (fun k hk => (hΦ k (hk.trans_le hn) (hRn k hk)).2.2) n le_rfl

/-- **The tube theorem for local errors with a one-sided Lipschitz constant.** Let `(F, A)` be a
problem on a tube (`DLRAProblem`) with `F` continuous on the tube, and let `ℓ` be a one-sided
Lipschitz constant of `F` on the tube. If every step whose start value satisfies
`‖Y n - A (τ n)‖ ≤ R n` has local error `δ n` (`HasLocalError`), the error bound is at most `R n`
for `n < N` and `R n + 2 B (τ (n + 1) - τ n) < ρ`, then for `n ≤ N`

  `‖Y n - A (τ n)‖ ≤ e^{ℓ (τ n - τ 0)} ‖Y 0 - A (τ 0)‖ + ∑_{k<n} e^{ℓ (τ n - τ (k + 1))} δ k`.

The Lipschitz constant `L` of the problem gives the exact solutions started at the numerical
values and does not enter the bound. -/
theorem DLRAProblem.norm_sub_le_of_hasLocalError_of_oneSided [CompleteSpace E]
    (hP : DLRAProblem F A (τ 0) (τ N) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A (τ 0) (τ N) ρ))
    (hℓ : IsOneSidedLipschitzFieldOn F (tubeSet A (τ 0) (τ N) ρ) ℓ) (hτ : IsGrid τ N)
    (hloc : ∀ n < N, ‖Y n - A (τ n)‖ ≤ R n →
      HasLocalError F (τ n) (τ (n + 1)) (Y n) (Y (n + 1)) (δ n))
    (hR : ∀ n < N, Real.exp (ℓ * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (ℓ * (τ n - τ (k + 1))) * δ k ≤ R n)
    (hsmall : ∀ n < N, R n + 2 * B * (τ (n + 1) - τ n) < ρ) :
    ∀ n ≤ N, ‖Y n - A (τ n)‖ ≤ Real.exp (ℓ * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (ℓ * (τ n - τ (k + 1))) * δ k := by
  have hex : ∀ n, ∃ φ : ℝ → E, n < N → ‖Y n - A (τ n)‖ ≤ R n →
      ODESolution F φ (τ n) (τ (n + 1)) ∧ φ (τ n) = Y n := by
    intro n
    by_cases h : n < N ∧ ‖Y n - A (τ n)‖ ≤ R n
    · obtain ⟨hn, hRn⟩ := h
      have hsub := hτ.Icc_subset hn
      have hle := hτ.mono n hn
      have h0 : τ 0 ≤ τ n := (hsub (left_mem_Icc.2 hle)).1
      have h1 : τ (n + 1) ≤ τ N := (hsub (right_mem_Icc.2 hle)).2
      obtain ⟨φ, hφ, hφ₀, -⟩ := exists_ODESolution_near (hP.lipschitz.mono h0 h1 le_rfl)
        hP.L_nonneg (hP.bounded.mono h0 h1 le_rfl) hP.B_nonneg
        (hc.mono fun p hp => ⟨⟨h0.trans hp.1.1, hp.1.2.trans h1⟩, hp.2⟩) (hP.sol.mono h0 h1) hle
        (Y n) ((add_le_add hRn le_rfl).trans_lt (hsmall n hn))
      exact ⟨φ, fun _ _ => ⟨hφ, hφ₀⟩⟩
    · exact ⟨fun _ => Y n, fun hn hRn => absurd ⟨hn, hRn⟩ h⟩
  choose Φ hΦ using hex
  exact hℓ.norm_sub_le_of_fan hP.bounded hP.B_nonneg hτ hP.sol
    (fun n hn hRn => ⟨(hΦ n hn hRn).1, (hΦ n hn hRn).2,
      hloc n hn hRn (Φ n) (hΦ n hn hRn).1 (hΦ n hn hRn).2⟩) hR hsmall

end Tube

/-! ### Runs of a step relation -/

section Run

variable {M : StepRel E} {Adm : ℕ → E → Prop} {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → E} {δ R : ℕ → ℝ}
  {ρ ℓ L B : ℝ}

/-- **The tube theorem for runs with an invariant, one-sided form.** Under the hypotheses of
`IsRun.adm_and_norm_sub_le_of_tube`, with `ℓ` a one-sided Lipschitz constant of `F` on the tube
in the error bound in place of the Lipschitz constant `L`: if `Adm 0 (Y 0)`, the error bound is
at most `R n` for `n < N`, and `R n + 2 B (τ (n + 1) - τ n) < ρ`, then for `n ≤ N`

  `Adm n (Y n)` and
  `‖Y n - A (τ n)‖ ≤ e^{ℓ (τ n - τ 0)} ‖Y 0 - A (τ 0)‖ + ∑_{k<n} e^{ℓ (τ n - τ (k + 1))} δ k`. -/
theorem IsRun.adm_and_norm_sub_le_of_tube_of_oneSided [CompleteSpace E] (hY : IsRun M τ N Y)
    (hP : DLRAProblem F A (τ 0) (τ N) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A (τ 0) (τ N) ρ))
    (hℓ : IsOneSidedLipschitzFieldOn F (tubeSet A (τ 0) (τ N) ρ) ℓ)
    (hadm : ∀ n < N, ∀ Y₀ Y₁, Adm n Y₀ → ‖Y₀ - A (τ n)‖ ≤ R n → M (τ n) (τ (n + 1)) Y₀ Y₁ →
      Adm (n + 1) Y₁)
    (hloc : ∀ n < N, ∀ Y₀ Y₁, Adm n Y₀ → ‖Y₀ - A (τ n)‖ ≤ R n → M (τ n) (τ (n + 1)) Y₀ Y₁ →
      HasLocalError F (τ n) (τ (n + 1)) Y₀ Y₁ (δ n))
    (hY₀ : Adm 0 (Y 0))
    (hR : ∀ n < N, Real.exp (ℓ * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (ℓ * (τ n - τ (k + 1))) * δ k ≤ R n)
    (hsmall : ∀ n < N, R n + 2 * B * (τ (n + 1) - τ n) < ρ) :
    ∀ n ≤ N, Adm n (Y n) ∧
      ‖Y n - A (τ n)‖ ≤ Real.exp (ℓ * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
        ∑ k ∈ range n, Real.exp (ℓ * (τ n - τ (k + 1))) * δ k := by
  have key : ∀ n ≤ N, (∀ k < n, Adm k (Y k)) →
      ‖Y n - A (τ n)‖ ≤ Real.exp (ℓ * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
        ∑ k ∈ range n, Real.exp (ℓ * (τ n - τ (k + 1))) * δ k := by
    intro n hn hadmn
    have hτn : τ n ≤ τ N := hY.grid.le_of_le hn le_rfl
    exact (hP.mono le_rfl hτn le_rfl).norm_sub_le_of_hasLocalError_of_oneSided
      (hc.mono fun p hp => ⟨⟨hp.1.1, hp.1.2.trans hτn⟩, hp.2⟩)
      (hℓ.mono (fun p hp => ⟨⟨hp.1.1, hp.1.2.trans hτn⟩, hp.2⟩) le_rfl) (hY.grid.of_le hn)
      (fun k hk hRk => hloc k (hk.trans_le hn) (Y k) (Y (k + 1)) (hadmn k hk) hRk
        (hY.step k (hk.trans_le hn)))
      (fun k hk => hR k (hk.trans_le hn)) (fun k hk => hsmall k (hk.trans_le hn)) n le_rfl
  have hall : ∀ n ≤ N, Adm n (Y n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rcases n with _ | n
      · exact hY₀
      · have hn1 : n < N := hn
        exact hadm n hn1 (Y n) (Y (n + 1)) (ih n n.lt_succ_self hn1.le)
          ((key n hn1.le fun k hk => ih k (hk.trans n.lt_succ_self)
            ((hk.trans hn1).le)).trans (hR n hn1)) (hY.step n hn1)
  exact fun n hn => ⟨hall n hn, key n hn fun k hk => hall k (hk.le.trans hn)⟩

/-- **Existence of a run and error bound with a one-sided Lipschitz constant.** Under the
hypotheses of `exists_isRun_norm_sub_le_of_tube`, with `ℓ` a one-sided Lipschitz constant of `F`
on the tube in the error bound in place of `L`: there is a run `Y 0 = Y₀, …, Y N` of `M`, and for
`n ≤ N`

  `Adm n (Y n)` and
  `‖Y n - A (τ n)‖ ≤ e^{ℓ (τ n - τ 0)} ‖Y₀ - A (τ 0)‖ + ∑_{k<n} e^{ℓ (τ n - τ (k + 1))} δ k`. -/
theorem exists_isRun_norm_sub_le_of_tube_of_oneSided [CompleteSpace E] (hτ : IsGrid τ N)
    (hP : DLRAProblem F A (τ 0) (τ N) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A (τ 0) (τ N) ρ))
    (hℓ : IsOneSidedLipschitzFieldOn F (tubeSet A (τ 0) (τ N) ρ) ℓ)
    (hex : ∀ n < N, ∀ Y₀, Adm n Y₀ → ‖Y₀ - A (τ n)‖ ≤ R n → ∃ Y₁, M (τ n) (τ (n + 1)) Y₀ Y₁)
    (hadm : ∀ n < N, ∀ Y₀ Y₁, Adm n Y₀ → ‖Y₀ - A (τ n)‖ ≤ R n → M (τ n) (τ (n + 1)) Y₀ Y₁ →
      Adm (n + 1) Y₁)
    (hloc : ∀ n < N, ∀ Y₀ Y₁, Adm n Y₀ → ‖Y₀ - A (τ n)‖ ≤ R n → M (τ n) (τ (n + 1)) Y₀ Y₁ →
      HasLocalError F (τ n) (τ (n + 1)) Y₀ Y₁ (δ n))
    {Y₀ : E} (hY₀ : Adm 0 Y₀)
    (hR : ∀ n < N, Real.exp (ℓ * (τ n - τ 0)) * ‖Y₀ - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (ℓ * (τ n - τ (k + 1))) * δ k ≤ R n)
    (hsmall : ∀ n < N, R n + 2 * B * (τ (n + 1) - τ n) < ρ) :
    ∃ Y : ℕ → E, Y 0 = Y₀ ∧ IsRun M τ N Y ∧ ∀ n ≤ N, Adm n (Y n) ∧
      ‖Y n - A (τ n)‖ ≤ Real.exp (ℓ * (τ n - τ 0)) * ‖Y₀ - A (τ 0)‖ +
        ∑ k ∈ range n, Real.exp (ℓ * (τ n - τ (k + 1))) * δ k := by
  obtain ⟨Y, hY0, hY⟩ : ∃ Y : ℕ → E, Y 0 = Y₀ ∧ IsRun M τ N Y := by
    refine exists_isRun hτ Y₀ fun n hn Y hY0 hY => ?_
    subst hY0
    have hτn : τ n ≤ τ N := hτ.le_of_le hn.le le_rfl
    have hpre := hY.adm_and_norm_sub_le_of_tube_of_oneSided (Adm := Adm) (R := R) (δ := δ)
      (hP.mono le_rfl hτn le_rfl) (hc.mono fun p hp => ⟨⟨hp.1.1, hp.1.2.trans hτn⟩, hp.2⟩)
      (hℓ.mono (fun p hp => ⟨⟨hp.1.1, hp.1.2.trans hτn⟩, hp.2⟩) le_rfl)
      (fun k hk => hadm k (hk.trans hn)) (fun k hk => hloc k (hk.trans hn)) hY₀
      (fun k hk => hR k (hk.trans hn)) (fun k hk => hsmall k (hk.trans hn)) n le_rfl
    exact hex n hn (Y n) hpre.1 (hpre.2.trans (hR n hn))
  subst hY0
  exact ⟨Y, rfl, hY, hY.adm_and_norm_sub_le_of_tube_of_oneSided hP hc hℓ hadm hloc hY₀ hR hsmall⟩

end Run

/-! ### The uniform grid for a negative one-sided Lipschitz constant -/

/-- **Propagated local errors for a negative one-sided Lipschitz constant.** On the uniform grid
`t₀ + n h` with local errors `h c` and `ℓ < 0`, the global error bound of the tube theorem is at
most `e^{ℓ n h} δ₀ + (h - ℓ⁻¹) c` for every `n`: the propagated local errors form a geometric sum
with ratio `e^{ℓ h} < 1`, which is at most `h / (1 - e^{ℓ h}) ≤ h - ℓ⁻¹` times `c`. The bound
does not grow with `n`. -/
theorem uniformGrid_errorBound_le_of_neg {ℓ h c e₀ δ₀ : ℝ} (t₀ : ℝ) (n : ℕ) (hℓ : ℓ < 0)
    (hh : 0 ≤ h) (hc : 0 ≤ c) (he : e₀ ≤ δ₀) :
    Real.exp (ℓ * (uniformGrid t₀ h n - uniformGrid t₀ h 0)) * e₀ +
        ∑ k ∈ range n, Real.exp (ℓ * (uniformGrid t₀ h n - uniformGrid t₀ h (k + 1))) * (h * c) ≤
      Real.exp (ℓ * (n * h)) * δ₀ + (h - ℓ⁻¹) * c := by
  have hm0 : 0 < -ℓ⁻¹ := neg_pos.2 (inv_lt_zero.2 hℓ)
  have hx1 : Real.exp (ℓ * h) * (1 - ℓ * h) ≤ 1 := by
    have h1 := Real.add_one_le_exp (-(ℓ * h))
    have h2 : Real.exp (ℓ * h) * Real.exp (-(ℓ * h)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h3 := Real.exp_pos (ℓ * h)
    nlinarith
  have hkey : Real.exp (ℓ * h) * (h - ℓ⁻¹) ≤ -ℓ⁻¹ := by
    have hinv : ℓ⁻¹ * ℓ = 1 := inv_mul_cancel₀ hℓ.ne
    have e : Real.exp (ℓ * h) * (h - ℓ⁻¹) = -ℓ⁻¹ * (Real.exp (ℓ * h) * (1 - ℓ * h)) := by
      linear_combination (-(Real.exp (ℓ * h) * h)) * hinv
    rw [e]
    exact mul_le_of_le_one_right hm0.le hx1
  have hsum : ∀ n : ℕ, ∑ k ∈ range n,
      Real.exp (ℓ * (uniformGrid t₀ h n - uniformGrid t₀ h (k + 1))) * (h * c) ≤
        (h - ℓ⁻¹) * c := by
    intro n
    induction n with
    | zero =>
      rw [range_zero, sum_empty]
      exact mul_nonneg (by linarith) hc
    | succ n ih =>
      rw [sum_range_succ, sub_self, mul_zero, Real.exp_zero, one_mul]
      have hsplit : ∑ k ∈ range n,
          Real.exp (ℓ * (uniformGrid t₀ h (n + 1) - uniformGrid t₀ h (k + 1))) * (h * c) =
          Real.exp (ℓ * h) * ∑ k ∈ range n,
            Real.exp (ℓ * (uniformGrid t₀ h n - uniformGrid t₀ h (k + 1))) * (h * c) := by
        rw [mul_sum]
        refine sum_congr rfl fun k _ => ?_
        rw [← mul_assoc (Real.exp (ℓ * h)), ← Real.exp_add]
        congr 2
        simp only [uniformGrid]
        push_cast
        ring
      rw [hsplit]
      calc Real.exp (ℓ * h) * ∑ k ∈ range n,
            Real.exp (ℓ * (uniformGrid t₀ h n - uniformGrid t₀ h (k + 1))) * (h * c) + h * c
          ≤ Real.exp (ℓ * h) * ((h - ℓ⁻¹) * c) + h * c := by
            have := mul_le_mul_of_nonneg_left ih (Real.exp_pos (ℓ * h)).le
            linarith
        _ = Real.exp (ℓ * h) * (h - ℓ⁻¹) * c + h * c := by ring
        _ ≤ -ℓ⁻¹ * c + h * c := by
            have := mul_le_mul_of_nonneg_right hkey hc
            linarith
        _ = (h - ℓ⁻¹) * c := by ring
  have hn0 : uniformGrid t₀ h n - uniformGrid t₀ h 0 = n * h := by simp [uniformGrid]
  rw [hn0]
  have := mul_le_mul_of_nonneg_left he (Real.exp_pos (ℓ * (n * h))).le
  linarith [hsum n]

/-! ### Methods defined for all fields -/

section Method

variable {M : StepMethod E} {Adm : E → Prop} {κ : ℝ} {N : ℕ} {t₀ h T c δ ρ ℓ L B : ℝ}

/-- A run of a tube-local method on the uniform grid with radii `R n`, one-sided form. -/
private theorem StepMethod.IsTubeLocal.exists_run_of_oneSided_aux [CompleteSpace E]
    (hM : M.IsTubeLocal Adm κ) (hκ : 2 ≤ κ) (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hℓ : IsOneSidedLipschitzFieldOn F (tubeSet A t₀ (t₀ + N * h) ρ) ℓ) {R : ℕ → ℝ}
    (hloc : ∀ n < N, ∀ Y₀ Y₁, Adm Y₀ → ‖Y₀ - A (t₀ + n * h)‖ ≤ R n →
      M F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ →
      HasLocalError F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ (h * c))
    (hh : 0 ≤ h) {Y₀ : E} (hY₀ : Adm Y₀)
    (hR : ∀ n < N, Real.exp (ℓ * (uniformGrid t₀ h n - uniformGrid t₀ h 0)) *
      ‖Y₀ - A (uniformGrid t₀ h 0)‖ + ∑ k ∈ range n,
        Real.exp (ℓ * (uniformGrid t₀ h n - uniformGrid t₀ h (k + 1))) * (h * c) ≤ R n)
    (hsmall : ∀ n < N, R n + κ * B * h < ρ) :
    ∃ Y : ℕ → E, Y 0 = Y₀ ∧ IsRun (M F) (uniformGrid t₀ h) N Y ∧ ∀ n ≤ N, Adm (Y n) ∧
      ‖Y n - A (uniformGrid t₀ h n)‖ ≤
        Real.exp (ℓ * (uniformGrid t₀ h n - uniformGrid t₀ h 0)) *
          ‖Y₀ - A (uniformGrid t₀ h 0)‖ + ∑ k ∈ range n,
            Real.exp (ℓ * (uniformGrid t₀ h n - uniformGrid t₀ h (k + 1))) * (h * c) := by
  have e : ∀ n : ℕ, uniformGrid t₀ h (n + 1) = t₀ + ((n : ℝ) + 1) * h := fun n => by
    simp [uniformGrid]
  have e0 : uniformGrid t₀ h 0 = t₀ := by simp [uniformGrid]
  have hP0 : DLRAProblem F A (uniformGrid t₀ h 0) (uniformGrid t₀ h N) ρ L B := by
    rw [e0]
    exact hP
  have hc0 : ContinuousOn (Function.uncurry F)
      (tubeSet A (uniformGrid t₀ h 0) (uniformGrid t₀ h N) ρ) := by
    rw [e0]
    exact hc
  have hℓ0 : IsOneSidedLipschitzFieldOn F
      (tubeSet A (uniformGrid t₀ h 0) (uniformGrid t₀ h N) ρ) ℓ := by
    rw [e0]
    exact hℓ
  have hBh : 0 ≤ B * h := mul_nonneg hP.B_nonneg hh
  have hκB : 2 * (B * h) ≤ κ * (B * h) := mul_le_mul_of_nonneg_right hκ hBh
  have hκB' : 0 ≤ κ * (B * h) := by linarith
  refine exists_isRun_norm_sub_le_of_tube_of_oneSided (M := M F) (Adm := fun _ => Adm) (R := R)
    (δ := fun _ => h * c) (isGrid_uniformGrid hh N) hP0 hc0 hℓ0
    (fun n hn Z₀ hZ₀ hnear => ?_) (fun n hn Z₀ Z₁ hZ₀ _ hstep => ?_)
    (fun n hn Z₀ Z₁ hZ₀ hnear hstep => ?_) hY₀ hR (fun n hn => ?_)
  · -- a step of the extended field exists, and it is a step of `F`
    have hnear' : ‖Z₀ - A (t₀ + n * h)‖ ≤ R n := hnear
    have hρ : 0 ≤ ρ := by
      have := hsmall n hn
      have := norm_nonneg (Z₀ - A (t₀ + n * h))
      nlinarith
    have hGL : IsLipschitzField (tubeExt F A t₀ (t₀ + N * h) ρ) L :=
      isLipschitzField_tubeExt hP.lipschitz hP.L_nonneg hρ
    have hGc : ∀ x, ContinuousOn (fun t => tubeExt F A t₀ (t₀ + N * h) ρ t x)
        (Icc t₀ (t₀ + N * h)) := fun x => continuousOn_tubeExt hc hP.sol.cont hρ x
    obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hn
    obtain ⟨Y₁, hY₁⟩ := hM.exists_step hGL (fun x => (hGc x).mono (Icc_subset_Icc ha hb)) h01
      hZ₀
    refine ⟨Y₁, ?_⟩
    rw [e n]
    exact hM.step_of_tubeExt hP.bounded hP.B_nonneg ha hb h01 (hP.sol.mono ha hb) hZ₀
      (by rw [hsub]; linarith [hsmall n hn]) hY₁
  · rw [e n] at hstep
    exact hM.adm_of_step (uniformGrid_step (t₀ := t₀) hh hn).2.1 hZ₀ hstep
  · rw [e n] at hstep ⊢
    exact hloc n hn Z₀ Z₁ hZ₀ hnear hstep
  · rw [uniformGrid_succ_sub]
    linarith [hsmall n hn]

/-- **Existence of a run and error bound for a tube-local method, one-sided form.** Under the
hypotheses of `StepMethod.IsTubeLocal.exists_run_norm_sub_le`, let `ℓ ≥ 0` be a one-sided
Lipschitz constant of `F` on the tube. If

  `e^{ℓ T} δ + T e^{ℓ T} c + κ B h < ρ`,

then the method can be run from `Y₀`: there are `Y 0 = Y₀, Y 1, …, Y N`, each obtained from the
previous one by a step of `M F` of size `h`, with

  `Adm (Y n)` and `‖Y n - A (t₀ + n h)‖ ≤ e^{ℓ T} δ + T e^{ℓ T} c` for all `n ≤ N`.

The Lipschitz constant `L` of the problem is needed for the existence of the steps and is not in
the bound; with `ℓ = L` this is `StepMethod.IsTubeLocal.exists_run_norm_sub_le`. -/
theorem StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_oneSided [CompleteSpace E]
    (hM : M.IsTubeLocal Adm κ) (hκ : 2 ≤ κ) (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hℓ : IsOneSidedLipschitzFieldOn F (tubeSet A t₀ (t₀ + N * h) ρ) ℓ) (hℓ₀ : 0 ≤ ℓ)
    (hloc : ∀ n < N, ∀ Y₀ Y₁, Adm Y₀ →
      ‖Y₀ - A (t₀ + n * h)‖ ≤ Real.exp (ℓ * T) * δ + T * Real.exp (ℓ * T) * c →
      M F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ →
      HasLocalError F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ (h * c))
    (hc₀ : 0 ≤ c) (hh : 0 ≤ h) (hNT : N * h ≤ T) {Y₀ : E} (hY₀ : Adm Y₀)
    (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (ℓ * T) * δ + T * Real.exp (ℓ * T) * c + κ * B * h < ρ) :
    ∃ Y : ℕ → E, Y 0 = Y₀ ∧ IsRun (M F) (uniformGrid t₀ h) N Y ∧ ∀ n ≤ N, Adm (Y n) ∧
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (ℓ * T) * δ + T * Real.exp (ℓ * T) * c := by
  have e0 : uniformGrid t₀ h 0 = t₀ := by simp [uniformGrid]
  have hb : ∀ k ≤ N, Real.exp (ℓ * (uniformGrid t₀ h k - uniformGrid t₀ h 0)) *
      ‖Y₀ - A (uniformGrid t₀ h 0)‖ + ∑ j ∈ range k,
        Real.exp (ℓ * (uniformGrid t₀ h k - uniformGrid t₀ h (j + 1))) * (h * c) ≤
      Real.exp (ℓ * T) * δ + T * Real.exp (ℓ * T) * c := fun k hk =>
    uniformGrid_errorBound_le t₀ hℓ₀ hh hc₀
      ((mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) hh).trans hNT) (norm_nonneg _)
      (by rw [e0]; exact hδ)
  obtain ⟨Y, hY0, hY, hbd⟩ := hM.exists_run_of_oneSided_aux hκ hP hc hℓ
    (R := fun _ => Real.exp (ℓ * T) * δ + T * Real.exp (ℓ * T) * c) hloc hh hY₀
    (fun k hk => hb k hk.le) fun _ _ => hsmall
  exact ⟨Y, hY0, hY, fun n hn => ⟨(hbd n hn).1, (hbd n hn).2.trans (hb n hn)⟩⟩

/-- **Runs of every length for a dissipative problem.** Under the hypotheses of
`StepMethod.IsTubeLocal.exists_run_norm_sub_le`, let `ℓ < 0` be a one-sided Lipschitz constant
of `F` on the tube. If every step `n` whose start value satisfies `Adm` and lies within
`δ + (h - ℓ⁻¹) c` of `A` has local error `h c`, `‖Y₀ - A t₀‖ ≤ δ`, and

  `δ + (h - ℓ⁻¹) c + κ B h < ρ`,

then the method can be run from `Y₀` for `N` steps, and

  `Adm (Y n)` and `‖Y n - A (t₀ + n h)‖ ≤ e^{ℓ n h} δ + (h - ℓ⁻¹) c` for all `n ≤ N`.

Neither the smallness condition nor the bound contains the final time `t₀ + N h`: the initial
error decays, and the local errors add up to at most `(h - ℓ⁻¹) c`. -/
theorem StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_oneSided_neg [CompleteSpace E]
    (hM : M.IsTubeLocal Adm κ) (hκ : 2 ≤ κ) (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hℓ : IsOneSidedLipschitzFieldOn F (tubeSet A t₀ (t₀ + N * h) ρ) ℓ) (hℓ₀ : ℓ < 0)
    (hloc : ∀ n < N, ∀ Y₀ Y₁, Adm Y₀ → ‖Y₀ - A (t₀ + n * h)‖ ≤ δ + (h - ℓ⁻¹) * c →
      M F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ →
      HasLocalError F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ (h * c))
    (hc₀ : 0 ≤ c) (hh : 0 ≤ h) {Y₀ : E} (hY₀ : Adm Y₀) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : δ + (h - ℓ⁻¹) * c + κ * B * h < ρ) :
    ∃ Y : ℕ → E, Y 0 = Y₀ ∧ IsRun (M F) (uniformGrid t₀ h) N Y ∧ ∀ n ≤ N, Adm (Y n) ∧
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (ℓ * (n * h)) * δ + (h - ℓ⁻¹) * c := by
  have e0 : uniformGrid t₀ h 0 = t₀ := by simp [uniformGrid]
  have hb : ∀ k : ℕ, Real.exp (ℓ * (uniformGrid t₀ h k - uniformGrid t₀ h 0)) *
      ‖Y₀ - A (uniformGrid t₀ h 0)‖ + ∑ j ∈ range k,
        Real.exp (ℓ * (uniformGrid t₀ h k - uniformGrid t₀ h (j + 1))) * (h * c) ≤
      Real.exp (ℓ * (k * h)) * δ + (h - ℓ⁻¹) * c := fun k =>
    uniformGrid_errorBound_le_of_neg t₀ k hℓ₀ hh hc₀ (by rw [e0]; exact hδ)
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hdec : ∀ k : ℕ, Real.exp (ℓ * (k * h)) * δ + (h - ℓ⁻¹) * c ≤ δ + (h - ℓ⁻¹) * c := by
    intro k
    have h1 : Real.exp (ℓ * (k * h)) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hℓ₀.le
        (mul_nonneg (Nat.cast_nonneg k) hh))
    have := mul_le_mul_of_nonneg_right h1 hδ0
    linarith
  obtain ⟨Y, hY0, hY, hbd⟩ := hM.exists_run_of_oneSided_aux hκ hP hc hℓ
    (R := fun _ => δ + (h - ℓ⁻¹) * c) hloc hh hY₀ (fun k _ => (hb k).trans (hdec k))
    fun _ _ => hsmall
  exact ⟨Y, hY0, hY, fun n hn => ⟨(hbd n hn).1, (hbd n hn).2.trans (hb n)⟩⟩

end Method


/-! ### The theorem with the Lipschitz constant, and non-vacuity -/

section Examples

/-- `StepMethod.IsTubeLocal.exists_run_norm_sub_le`, restated verbatim, is the case `ℓ = L` of
`StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_oneSided`. -/
example [CompleteSpace E] {M : StepMethod E} {Adm : E → Prop} {κ : ℝ} {N : ℕ}
    {t₀ h T c δ ρ L B : ℝ}
    (hM : M.IsTubeLocal Adm κ) (hκ : 2 ≤ κ) (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hloc : ∀ n < N, ∀ Y₀ Y₁, Adm Y₀ →
      ‖Y₀ - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) * c →
      M F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ →
      HasLocalError F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ (h * c))
    (hc₀ : 0 ≤ c) (hh : 0 ≤ h) (hNT : N * h ≤ T) {Y₀ : E} (hY₀ : Adm Y₀)
    (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) * c + κ * B * h < ρ) :
    ∃ Y : ℕ → E, Y 0 = Y₀ ∧ IsRun (M F) (uniformGrid t₀ h) N Y ∧ ∀ n ≤ N, Adm (Y n) ∧
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) * c :=
  hM.exists_run_norm_sub_le_of_oneSided hκ hP hc hP.isOneSidedLipschitzFieldOn hP.L_nonneg hloc
    hc₀ hh hNT hY₀ hδ hsmall

/-- `t ↦ e^{-(t - s₀)} y₀` solves `y' = -y`. -/
private theorem odeSolution_exp_neg_smul (y₀ : E) (s₀ a b : ℝ) :
    ODESolution (fun _ (x : E) => (-1 : ℝ) • x) (fun t => Real.exp (-(t - s₀)) • y₀) a b :=
  ⟨by fun_prop, fun t _ => by
    have h1 := ((Real.hasDerivAt_exp (-(t - s₀))).comp t
      ((hasDerivAt_id t).sub_const s₀).neg).smul_const y₀
    have hd : HasDerivAt (fun t : ℝ => Real.exp (-(t - s₀)) • y₀)
        ((-1 : ℝ) • (Real.exp (-(t - s₀)) • y₀)) t := by
      rw [smul_smul, mul_comm]
      exact h1
    exact hd.hasDerivWithinAt⟩

/-- The field `F t x = -x` with the solution `A = 0` is a problem on every tube of radius
`ρ ≥ 0`, with Lipschitz constant `1`, bound `ρ` and one-sided Lipschitz constant `-1`. -/
private theorem dlraProblem_neg {a b ρ : ℝ} (hρ : 0 ≤ ρ) :
    DLRAProblem (fun _ (x : E) => (-1 : ℝ) • x) (fun _ => 0) a b ρ 1 ρ ∧
      IsOneSidedLipschitzFieldOn (fun _ (x : E) => (-1 : ℝ) • x) (tubeSet (fun _ => 0) a b ρ)
        (-1) := by
  refine ⟨⟨⟨continuousOn_const, fun t _ => ?_⟩, zero_le_one, hρ, fun t _ x y _ _ => ?_,
    fun t _ x hx => ?_⟩, fun t x y _ _ => isOneSidedLipschitzField_smul_id (-1) t x y⟩
  · simpa using hasDerivWithinAt_const t (Ici t) (0 : E)
  · exact le_of_eq (by rw [← smul_sub, norm_smul, norm_neg, norm_one, one_mul])
  · simpa [norm_smul] using hx

/-- The method that multiplies by `e^{-h}` has local error `0` for `F t x = -x`. -/
private theorem hasLocalError_exp_neg {s₀ s₁ c : ℝ} (h01 : s₀ ≤ s₁) (hc : 0 ≤ c) {Y₀ Y₁ : E}
    (hstep : Y₁ = Real.exp (-(s₁ - s₀)) • Y₀) :
    HasLocalError (fun _ (x : E) => (-1 : ℝ) • x) s₀ s₁ Y₀ Y₁ c := fun Φ hΦ hΦ₀ => by
  have heq := hΦ.eqOn_of_oneSided (odeSolution_exp_neg_smul Y₀ s₀ s₀ s₁)
    (isOneSidedLipschitzField_smul_id (-1)) (by rw [hΦ₀]; simp) ⟨h01, le_rfl⟩
  rw [heq, hstep, sub_self, norm_zero]
  exact hc

/-- The method that multiplies by `e^{-h}` (it does not depend on the field) is tube-local. -/
private theorem isTubeLocal_exp_neg :
    StepMethod.IsTubeLocal (E := E) (fun _ s₀ s₁ Y₀ Y₁ => Y₁ = Real.exp (-(s₁ - s₀)) • Y₀)
      (fun _ => True) 2 where
  exists_step := fun _ _ _ _ => ⟨_, rfl⟩
  adm_of_step := fun _ _ _ => trivial
  step_of_tubeExt := fun _ _ _ _ _ _ _ _ hstep => hstep

/-- The values `Y n = e^{-n/4} / 4` follow the exact flow of `y' = -y` with step size `1/4`. -/
private theorem quarter_mul_exp_pow_succ (n : ℕ) :
    (1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ (n + 1) =
      Real.exp (-(1 / 4)) • ((1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ n) := by
  rw [smul_eq_mul, pow_succ]
  ring

/-- **Non-vacuity of `StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_oneSided_neg`**, for the
dissipative field `F t x = -x` on `ℝ` (Lipschitz constant `1`, one-sided Lipschitz constant `-1`,
bounded by `ρ = 1` on the tube of radius `1` around the solution `A = 0`) and the method that
multiplies by `e^{-h}`, whose local error is at most `h c` for every `c ≥ 0`. With the step size
`h = 1/4`, `c = 1/10` and the start value `Y₀ = 1/4` the smallness condition
`δ + (h + 1) c + 2 ρ h < ρ` reads `1/4 + 1/8 + 1/2 < 1`, and for every number of steps `N` the
theorem gives a run with `|Y n| ≤ e^{-n/4} / 4 + 1/8`. -/
example (t₀ : ℝ) (N : ℕ) :
    ∃ Y : ℕ → ℝ, Y 0 = 1 / 4 ∧
      IsRun (fun s₀ s₁ Y₀ Y₁ => Y₁ = Real.exp (-(s₁ - s₀)) • Y₀) (uniformGrid t₀ (1 / 4)) N Y ∧
      ∀ n ≤ N, ‖Y n‖ ≤ Real.exp (-(n * (1 / 4))) * (1 / 4) + (1 / 4 + 1) * (1 / 10) := by
  have hh : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have e : (1 / 4 : ℝ) - (-1 : ℝ)⁻¹ = 1 / 4 + 1 := by norm_num
  obtain ⟨hP, hℓ⟩ := dlraProblem_neg (E := ℝ) (a := t₀) (b := t₀ + N * (1 / 4)) zero_le_one
  obtain ⟨Y, hY0, hY, hbd⟩ := (isTubeLocal_exp_neg (E := ℝ)).exists_run_norm_sub_le_of_oneSided_neg
    le_rfl hP (continuous_snd.const_smul (-1 : ℝ)).continuousOn hℓ (by norm_num) (c := 1 / 10)
    (δ := 1 / 4) (Y₀ := 1 / 4) (fun n _ Z₀ Z₁ _ _ hstep => hasLocalError_exp_neg
      (uniformGrid_step (t₀ := t₀) hh (Nat.lt_succ_self n)).2.1 (by norm_num) hstep)
    (by norm_num) hh trivial (by norm_num [Real.norm_eq_abs, abs_of_pos]) (by norm_num)
  refine ⟨Y, hY0, hY, fun n hn => ?_⟩
  have h1 := (hbd n hn).2
  rw [e, neg_one_mul, sub_zero] at h1
  exact h1

/-- **Non-vacuity of `StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_oneSided`** with a
one-sided Lipschitz constant `ℓ = 0` below the Lipschitz constant `L = 1`: for `F t x = -x` on `ℝ`
and the method that multiplies by `e^{-h}`, with `N = 4` steps of size `h = 1/4` up to `T = 1`,
`c = 1/10`, `ρ = 1` and the start value `Y₀ = 1/4`, the smallness condition
`δ + T c + 2 ρ h < ρ` reads `1/4 + 1/10 + 1/2 < 1`, and the theorem gives a run with
`|Y n| ≤ 1/4 + 1/10`. -/
example (t₀ : ℝ) :
    ∃ Y : ℕ → ℝ, Y 0 = 1 / 4 ∧
      IsRun (fun s₀ s₁ Y₀ Y₁ => Y₁ = Real.exp (-(s₁ - s₀)) • Y₀) (uniformGrid t₀ (1 / 4)) 4 Y ∧
      ∀ n ≤ 4, ‖Y n‖ ≤ 1 / 4 + 1 / 10 := by
  have hh : (0 : ℝ) ≤ 1 / 4 := by norm_num
  obtain ⟨hP, hℓ⟩ := dlraProblem_neg (E := ℝ) (a := t₀) (b := t₀ + ((4 : ℕ) : ℝ) * (1 / 4))
    zero_le_one
  obtain ⟨Y, hY0, hY, hbd⟩ := (isTubeLocal_exp_neg (E := ℝ)).exists_run_norm_sub_le_of_oneSided
    le_rfl hP (continuous_snd.const_smul (-1 : ℝ)).continuousOn (hℓ.mono subset_rfl
      (by norm_num : (-1 : ℝ) ≤ 0)) le_rfl (c := 1 / 10) (δ := 1 / 4) (T := 1) (Y₀ := 1 / 4)
    (fun n _ Z₀ Z₁ _ _ hstep => hasLocalError_exp_neg
      (uniformGrid_step (t₀ := t₀) hh (Nat.lt_succ_self n)).2.1 (by norm_num) hstep)
    (by norm_num) hh (by norm_num) trivial (by norm_num [Real.norm_eq_abs, abs_of_pos])
    (by norm_num)
  refine ⟨Y, hY0, hY, fun n hn => ?_⟩
  have h1 := (hbd n hn).2
  norm_num at h1 ⊢
  linarith

omit [InnerProductSpace ℝ E] in
/-- The bound of the tube theorems for `F t x = -x` with `ℓ = -1`, `A = 0` and local errors `0`
on the uniform grid is `e^{-n h} ‖Y 0‖`. -/
private theorem norm_le_of_errorBound {y z : E} {t₀ h : ℝ} {n : ℕ}
    (hz : ‖z - 0‖ ≤ Real.exp (-1 * (uniformGrid t₀ h n - uniformGrid t₀ h 0)) * ‖y - 0‖ +
      ∑ k ∈ range n, Real.exp (-1 * (uniformGrid t₀ h n - uniformGrid t₀ h (k + 1))) * 0) :
    ‖z‖ ≤ Real.exp (-(n * h)) * ‖y‖ := by
  have e : uniformGrid t₀ h n - uniformGrid t₀ h 0 = n * h := by simp [uniformGrid]
  rw [e, neg_one_mul, sub_zero, sub_zero] at hz
  simpa only [mul_zero, sum_const_zero, add_zero] using hz

omit [InnerProductSpace ℝ E] in
/-- The error bound of the tube theorems for `ℓ = -1`, `A = 0` and local errors `0` on the
uniform grid is at most `‖Y 0‖`. -/
private theorem errorBound_exp_neg_le (y : E) {t₀ h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    Real.exp (-1 * (uniformGrid t₀ h n - uniformGrid t₀ h 0)) * ‖y - 0‖ +
      ∑ k ∈ range n, Real.exp (-1 * (uniformGrid t₀ h n - uniformGrid t₀ h (k + 1))) * 0 ≤
      ‖y‖ := by
  have e : uniformGrid t₀ h n - uniformGrid t₀ h 0 = n * h := by simp [uniformGrid]
  rw [e, sub_zero]
  simp only [mul_zero, sum_const_zero, add_zero]
  refine mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 ?_)
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hh]

/-- Values that follow the flow of `y' = -y` on the uniform grid do not grow. -/
private theorem norm_le_of_exp_neg_step {Y : ℕ → E} {h : ℝ} {N : ℕ} (hh : 0 ≤ h)
    (hY : ∀ n < N, Y (n + 1) = Real.exp (-h) • Y n) : ∀ n ≤ N, ‖Y n‖ ≤ ‖Y 0‖ := by
  intro n
  induction n with
  | zero => exact fun _ => le_rfl
  | succ n ih =>
    intro hn
    rw [hY n hn, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 (by linarith))).trans
      (ih (by omega))

/-- **Non-vacuity of `DLRAProblem.norm_sub_le_of_hasLocalError_of_oneSided`** for `F t x = -x` on
`ℝ` (`L = 1`, `ℓ = -1`, `B = ρ = 1`, `A = 0`): the values `Y n = e^{-n/4} / 4` on the uniform grid
with step size `h = 1/4` follow the exact flow, `Y (n + 1) = e^{-h} Y n`, so they have local
errors `0`, and with the radii `R n = |Y 0| = 1/4` the margin `|Y 0| + 2 ρ h < ρ` reads
`1/4 + 1/2 < 1`. For every number of steps the theorem gives `|Y n| ≤ e^{-n/4} / 4`. -/
example (t₀ : ℝ) (N : ℕ) :
    ∀ n ≤ N, ‖(1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ n‖ ≤ Real.exp (-(n * (1 / 4))) * (1 / 4) := by
  have hh : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hq : ‖(1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ 0‖ = 1 / 4 := by
    norm_num [Real.norm_eq_abs, abs_of_pos]
  obtain ⟨hP, hℓ⟩ := dlraProblem_neg (E := ℝ) (a := uniformGrid t₀ (1 / 4) 0)
    (b := uniformGrid t₀ (1 / 4) N) zero_le_one
  intro n hn
  have h1 : ‖(1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ n‖ ≤
      Real.exp (-(n * (1 / 4))) * ‖(1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ 0‖ :=
    norm_le_of_errorBound (hP.norm_sub_le_of_hasLocalError_of_oneSided
      (Y := fun n => (1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ n) (δ := fun _ => 0)
      (R := fun _ => ‖(1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ 0‖)
      (continuous_snd.const_smul (-1 : ℝ)).continuousOn hℓ (isGrid_uniformGrid hh N)
      (fun k hk _ => hasLocalError_exp_neg ((isGrid_uniformGrid hh N).mono k hk) le_rfl
        (by rw [uniformGrid_succ_sub]; exact quarter_mul_exp_pow_succ k))
      (fun k _ => errorBound_exp_neg_le _ hh k)
      (fun k _ => by rw [uniformGrid_succ_sub, hq]; norm_num) n hn)
  rwa [hq] at h1

/-- **Non-vacuity of `IsRun.adm_and_norm_sub_le_of_tube_of_oneSided`** for `F t x = -x` on `ℝ`
and the method that multiplies by `e^{-h}`, with the invariant `True`: the values
`Y n = e^{-n/4} / 4` are a run on the uniform grid with step size `h = 1/4`, the margin
`|Y 0| + 2 ρ h < ρ` with `ρ = 1` reads `1/4 + 1/2 < 1`, and the theorem gives
`|Y n| ≤ e^{-n/4} / 4`. -/
example (t₀ : ℝ) (N : ℕ) :
    ∀ n ≤ N, ‖(1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ n‖ ≤ Real.exp (-(n * (1 / 4))) * (1 / 4) := by
  have hh : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hq : ‖(1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ 0‖ = 1 / 4 := by
    norm_num [Real.norm_eq_abs, abs_of_pos]
  have hY : IsRun (fun s₀ s₁ (Y₀ Y₁ : ℝ) => Y₁ = Real.exp (-(s₁ - s₀)) • Y₀)
      (uniformGrid t₀ (1 / 4)) N fun n => (1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ n :=
    ⟨isGrid_uniformGrid hh N, fun k _ => by
      rw [uniformGrid_succ_sub]
      exact quarter_mul_exp_pow_succ k⟩
  obtain ⟨hP, hℓ⟩ := dlraProblem_neg (E := ℝ) (a := uniformGrid t₀ (1 / 4) 0)
    (b := uniformGrid t₀ (1 / 4) N) zero_le_one
  intro n hn
  have h1 : ‖(1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ n‖ ≤
      Real.exp (-(n * (1 / 4))) * ‖(1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ 0‖ :=
    norm_le_of_errorBound (hY.adm_and_norm_sub_le_of_tube_of_oneSided
      (Adm := fun _ _ => True) (δ := fun _ => 0)
      (R := fun _ => ‖(1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ 0‖) hP
      (continuous_snd.const_smul (-1 : ℝ)).continuousOn hℓ (fun _ _ _ _ _ _ _ => trivial)
      (fun k hk _ _ _ _ hstep => hasLocalError_exp_neg ((isGrid_uniformGrid hh N).mono k hk)
        le_rfl hstep)
      trivial (fun k _ => errorBound_exp_neg_le _ hh k)
      (fun k _ => by rw [uniformGrid_succ_sub, hq]; norm_num) n hn).2
  rwa [hq] at h1

/-- **Non-vacuity of `exists_isRun_norm_sub_le_of_tube_of_oneSided`** for `F t x = -x` on `ℝ` and
the method that multiplies by `e^{-h}`, with the invariant `True`: from `Y₀ = 1/4`, with the step
size `h = 1/4` and `ρ = 1` (margin `1/4 + 1/2 < 1`), there is a run on the uniform grid with
`|Y n| ≤ e^{-n/4} / 4` for every number of steps. -/
example (t₀ : ℝ) (N : ℕ) :
    ∃ Y : ℕ → ℝ, Y 0 = 1 / 4 ∧
      IsRun (fun s₀ s₁ Y₀ Y₁ => Y₁ = Real.exp (-(s₁ - s₀)) • Y₀) (uniformGrid t₀ (1 / 4)) N Y ∧
      ∀ n ≤ N, ‖Y n‖ ≤ Real.exp (-(n * (1 / 4))) * (1 / 4) := by
  have hh : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hq : ‖(1 / 4 : ℝ)‖ = 1 / 4 := by norm_num [Real.norm_eq_abs, abs_of_pos]
  obtain ⟨hP, hℓ⟩ := dlraProblem_neg (E := ℝ) (a := uniformGrid t₀ (1 / 4) 0)
    (b := uniformGrid t₀ (1 / 4) N) zero_le_one
  obtain ⟨Y, hY0, hY, hbd⟩ := exists_isRun_norm_sub_le_of_tube_of_oneSided
    (isGrid_uniformGrid hh N) hP (continuous_snd.const_smul (-1 : ℝ)).continuousOn hℓ
    (M := fun s₀ s₁ (Z₀ Z₁ : ℝ) => Z₁ = Real.exp (-(s₁ - s₀)) • Z₀) (Adm := fun _ _ => True)
    (δ := fun _ => 0) (R := fun _ => ‖(1 / 4 : ℝ)‖) (Y₀ := 1 / 4) (fun _ _ _ _ _ => ⟨_, rfl⟩)
    (fun _ _ _ _ _ _ _ => trivial)
    (fun k hk _ _ _ _ hstep => hasLocalError_exp_neg ((isGrid_uniformGrid hh N).mono k hk) le_rfl
      hstep)
    trivial (fun k _ => errorBound_exp_neg_le _ hh k)
    (fun k _ => by rw [uniformGrid_succ_sub, hq]; norm_num)
  refine ⟨Y, hY0, hY, fun n hn => ?_⟩
  have h1 := norm_le_of_errorBound (hbd n hn).2
  rwa [hq] at h1

/-- **Non-vacuity of `IsOneSidedLipschitzFieldOn.norm_sub_le_of_fan`** for `F t x = -x` on `ℝ`
(`ℓ = -1`, `B = ρ = 1`, `A = 0`) with the exact solutions `Φ n t = e^{-(t - t_n)} Y n` on the
steps: the values `Y n = e^{-n/4} / 4` follow the exact flow with step size `h = 1/4`, the margin
`|Y 0| + 2 ρ h < ρ` reads `1/4 + 1/2 < 1`, and the theorem gives `|Y n| ≤ e^{-n/4} / 4`. -/
example (t₀ : ℝ) (N : ℕ) :
    ∀ n ≤ N, ‖(1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ n‖ ≤ Real.exp (-(n * (1 / 4))) * (1 / 4) := by
  have hh : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hq : ‖(1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ 0‖ = 1 / 4 := by
    norm_num [Real.norm_eq_abs, abs_of_pos]
  obtain ⟨hP, hℓ⟩ := dlraProblem_neg (E := ℝ) (a := uniformGrid t₀ (1 / 4) 0)
    (b := uniformGrid t₀ (1 / 4) N) zero_le_one
  intro n hn
  have h1 : ‖(1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ n‖ ≤
      Real.exp (-(n * (1 / 4))) * ‖(1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ 0‖ :=
    norm_le_of_errorBound (hℓ.norm_sub_le_of_fan (δ := fun _ => 0)
      (Y := fun n => (1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ n)
      (R := fun _ => ‖(1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ 0‖)
      (Φ := fun n t => Real.exp (-(t - uniformGrid t₀ (1 / 4) n)) •
        ((1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ n)) hP.bounded zero_le_one
      (isGrid_uniformGrid hh N) hP.sol
      (fun k _ _ => ⟨odeSolution_exp_neg_smul _ _ _ _, by simp,
        by rw [uniformGrid_succ_sub, quarter_mul_exp_pow_succ k, sub_self, norm_zero]⟩)
      (fun k _ => errorBound_exp_neg_le _ hh k)
      (fun k _ => by rw [uniformGrid_succ_sub, hq]; norm_num) n hn)
  rwa [hq] at h1

/-- **Non-vacuity of `IsExactFan.norm_sub_le_of_near_of_oneSided`** for `F t x = -x` on `ℝ`
(`ℓ = -1`, `B = ρ = 1`, `A = 0`) and the exact-flow fan `Φ n t = e^{-(t - t_n)} Y n` of the values
`Y n = e^{-n/4} / 4`, which follow the exact flow with step size `h = 1/4`: they do not grow, so
the margin `|Y 0| + 2 ρ h < ρ`, that is `1/4 + 1/2 < 1`, holds on every step, and the theorem
gives `|Y n| ≤ e^{-n/4} / 4`. -/
example (t₀ : ℝ) (N : ℕ) :
    ∀ n ≤ N, ‖(1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ n‖ ≤ Real.exp (-(n * (1 / 4))) * (1 / 4) := by
  have hh : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hq : ‖(1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ 0‖ = 1 / 4 := by
    norm_num [Real.norm_eq_abs, abs_of_pos]
  obtain ⟨hP, hℓ⟩ := dlraProblem_neg (E := ℝ) (a := uniformGrid t₀ (1 / 4) 0)
    (b := uniformGrid t₀ (1 / 4) N) zero_le_one
  have hΦ : IsExactFan (fun _ (x : ℝ) => (-1 : ℝ) • x) (uniformGrid t₀ (1 / 4)) N
      (fun n => (1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ n)
      (fun n t => Real.exp (-(t - uniformGrid t₀ (1 / 4) n)) •
        ((1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ n)) :=
    ⟨fun k _ => odeSolution_exp_neg_smul _ _ _ _, fun k _ => by simp⟩
  have hbd := norm_le_of_exp_neg_step (Y := fun n => (1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ n)
    (N := N) hh fun k _ => quarter_mul_exp_pow_succ k
  intro n hn
  have h1 : ‖(1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ n‖ ≤
      Real.exp (-(n * (1 / 4))) * ‖(1 / 4 : ℝ) * Real.exp (-(1 / 4)) ^ 0‖ :=
    norm_le_of_errorBound (hΦ.norm_sub_le_of_near_of_oneSided (δ := fun _ => 0) hℓ
      hP.bounded zero_le_one (isGrid_uniformGrid hh N) hP.sol
      (fun k hk => by
        simp only [sub_zero, uniformGrid_succ_sub]
        linarith [hbd k hk.le, hq])
      (fun k _ => by
        rw [uniformGrid_succ_sub, quarter_mul_exp_pow_succ k, sub_self, norm_zero]) n hn)
  rwa [hq] at h1

/-- **Non-vacuity of `uniformGrid_errorBound_le_of_neg`** with `ℓ = -1`, step size `h = 1/10`,
local errors `h c` with `c = 1` and initial error `1`: the propagated errors are at most
`e^{-n/10} + 11/10` for every number of steps `n`. -/
example (t₀ : ℝ) (n : ℕ) :
    Real.exp (-1 * (uniformGrid t₀ (1 / 10) n - uniformGrid t₀ (1 / 10) 0)) * 1 +
        ∑ k ∈ range n, Real.exp (-1 * (uniformGrid t₀ (1 / 10) n -
          uniformGrid t₀ (1 / 10) (k + 1))) * (1 / 10 * 1) ≤
      Real.exp (-1 * (n * (1 / 10))) * 1 + (1 / 10 - (-1)⁻¹) * 1 :=
  uniformGrid_errorBound_le_of_neg t₀ n (by norm_num) (by norm_num) zero_le_one le_rfl

end Examples

end LeanDLRA
