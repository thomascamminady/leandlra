import LeanDLRA.Integrators.Tube

/-!
# Step methods: existence of a run and error bound from four properties of one step

A one-step method for `y' = F(t, y)` is a map `M` from fields to step relations
(`StepMethod E`): `M F t₀ t₁ Y₀ Y₁` says that `Y₁` is a result of one step of the method for the
field `F` from the value `Y₀` at time `t₀` to time `t₁`. This file proves once, for all such
methods, that the method can be run near a solution `A` and that the run satisfies the error bound
`e^{L T} δ + T e^{L T} c`, where `h c` is the local error of one step of size `h`. The field is
only assumed to be Lipschitz and bounded on a tube around `A` (`DLRAProblem`) and continuous
there. The fixed-rank BUG integrator is the model instance (`MatrixBUG.isTubeLocal_stepRel`,
`MatrixBUG.exists_run_norm_sub_le`).

## How to treat a new integrator

Write the integrator as `M : StepMethod E` and choose a predicate `Adm : E → Prop` for the values
from which a step can be started (for the low-rank integrators: rank at most `r`). Prove four
statements about **one step**.

* **(E) Existence.** For every *globally* Lipschitz field `G` that is continuous in time on
  `[t₀, t₁]` and every `Y₀` with `Adm Y₀` there is `Y₁` with `M G t₀ t₁ Y₀ Y₁`. No bound on `G`
  is available here; for substeps that are differential equations use
  `exists_ODESolution_of_linearGrowth`.
* **(I) Invariance.** A step from a value with `Adm` ends at a value with `Adm`.
* **(T) Locality.** If `F` is bounded by `B` on the tube of radius `ρ` around `A` and
  `‖Y₀ - A t₀‖ + κ B (t₁ - t₀) < ρ`, then every step of the extended field `tubeExt F A a b ρ`
  from `Y₀` is a step of `F`. The proof is an a priori estimate: all points at which the step
  evaluates the field lie in the tube (`tube_trap`), and there the two fields agree. The number
  `κ` counts how far the substeps can move away from `A`, in units of `B (t₁ - t₀)`; it is `4`
  for the BUG integrator. The same estimate gives the converse, which is needed for (L).
* **(L) Local error.** A step of `F` from `Y₀` near `A` has local error `(t₁ - t₀) c`
  (`HasLocalError`). If the local error is known for globally Lipschitz and bounded fields, apply
  that result to `tubeExt F A a b ρ` (whose steps near `A` are the steps of `F`, by the converse
  of (T)) and transfer it to `F` with `HasLocalError.of_tubeExt`.

State (E), (I), (T) in one lemma `StepMethod.IsTubeLocal M Adm κ`. Then
`StepMethod.IsTubeLocal.exists_run_norm_sub_le` gives, for a problem on a tube over
`[t₀, t₀ + N h]`, a start value `Y₀` with `Adm Y₀` and `‖Y₀ - A t₀‖ ≤ δ`, and under the single
smallness condition `e^{L T} δ + T e^{L T} c + κ B h < ρ`, a run `Y 0 = Y₀, …, Y N` of `M F` with

  `Adm (Y n)` and `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} c` for all `n ≤ N`.

The error bound for *every* run needs (L) only: it is `IsRun.norm_sub_le_of_tube_uniformGrid`,
or `IsRun.adm_and_norm_sub_le_of_tube_uniformGrid` when (L) holds only for start values with
`Adm` (then (I) is needed as well).

## Main definitions

* `StepMethod E`: methods as maps from fields to step relations.
* `StepMethod.IsTubeLocal M Adm κ`: the properties (E), (I), (T) of the method `M`.

## Main results

* `HasLocalError.of_tubeExt`: a local error with respect to the extended field is a local error
  with respect to `F` for start values well inside the tube.
* `IsRun.adm_and_norm_sub_le_of_tube`, `IsRun.adm_and_norm_sub_le_of_tube_uniformGrid`: the tube
  theorem for runs of a step relation with an invariant: every run from a start value with `Adm`
  keeps `Adm` and satisfies the error bound.
* `exists_isRun_norm_sub_le_of_tube`, `exists_isRun_norm_sub_le_of_tube_uniformGrid`: if in
  addition steps exist from values with `Adm` near the solution, a run exists.
* `StepMethod.IsTubeLocal.exists_run_norm_sub_le`: existence of a run and error bound for a
  method with (E), (I), (T), (L).

## Implementation notes

The theorems for a single step relation are primary and have minimal hypotheses: an arbitrary
grid, local errors `δ n` that may differ from step to step (for example a step followed by a
truncation with its own tolerance), radii `R n`, and a predicate `Adm n` that may depend on the
step index (for example a rank bound that changes along the run). Steps need to exist, to keep
`Adm` and to have a local error only from values with `Adm` within `R n` of the solution.
`StepMethod.IsTubeLocal` is the front end for methods defined for all fields.

The run is constructed step by step (`exists_isRun`). The tube theorem, applied to the run
constructed so far, shows that its last value is close to `A`. From there a step of the globally
Lipschitz extension `tubeExt F A t₀ (t₀ + N h) ρ` exists by (E), and it is a step of `F` by (T).
This is why (E) is required for globally Lipschitz fields although `F` is Lipschitz only on the
tube. The margin `κ B h` of the smallness condition is used twice: `2 B h` keeps the exact
solutions started at the numerical values in the tube (tube theorem), and `κ B h` keeps the
substeps of the method in the tube (T); hence `2 ≤ κ`, which is no restriction
(`StepMethod.IsTubeLocal.mono`).

Property (T) is stated with the extension `tubeExt` of a field on a tube. An intrinsic form
(two fields that agree near `Y₀` have the same steps from `Y₀`) would not mention a solution `A`,
but the a priori estimates of the low-rank integrators are estimates of the distance to `A`.
-/

open Set Finset

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Local errors with respect to the extended field -/

/-- **A local error for the extended field is a local error for the field.** Let `F` be bounded
by `B` on the tube of radius `ρ` around the solution `A`. If the step from `Y₀` to `Y₁` has local
error `δ` with respect to the extension `tubeExt F A a b ρ` and `Y₀` has the margin
`‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, then it has local error `δ` with respect to `F`: an exact
solution of `F` started at `Y₀` stays in the tube, so it is a solution of the extension. This
turns a local error theorem for globally Lipschitz and bounded fields into one for fields on a
tube. -/
theorem HasLocalError.of_tubeExt {F : ℝ → E → E} {A : ℝ → E} {a b ρ B t₀ t₁ δ : ℝ} {Y₀ Y₁ : E}
    (hloc : HasLocalError (tubeExt F A a b ρ) t₀ t₁ Y₀ Y₁ δ)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Y₁ δ := fun Φ hΦ hΦ₀ =>
  hloc Φ (hΦ.tubeExt_of_near hFB hB (sub_nonneg.2 h01) ha hb (by ring) hA
    (by rw [hΦ₀]; exact hsmall)) hΦ₀

/-! ### Runs of a step relation with an invariant -/

section Run

variable {F : ℝ → E → E} {A : ℝ → E} {M : StepRel E} {Adm : ℕ → E → Prop} {τ : ℕ → ℝ} {N : ℕ}
  {Y : ℕ → E} {δ R : ℕ → ℝ} {ρ L B : ℝ}

/-- **The tube theorem for runs with an invariant.** Let `Y` be a run of the step relation `M` on
the grid `τ` for a problem on a tube (`DLRAProblem`) with `F` continuous on the tube, and let
`Adm n` be predicates on the values. Suppose that every step of `M` from time `τ n` whose start
value satisfies `Adm n` and is at distance at most `R n` from `A (τ n)` ends at a value with
`Adm (n + 1)` and has local error `δ n`. If `Adm 0 (Y 0)`, the error bound is at most `R n` for
`n < N`, and `R n + 2 B (τ (n + 1) - τ n) < ρ`, then for `n ≤ N`

  `Adm n (Y n)` and
  `‖Y n - A (τ n)‖ ≤ e^{L (τ n - τ 0)} ‖Y 0 - A (τ 0)‖ + ∑_{k<n} e^{L (τ n - τ (k + 1))} δ k`.

For the trivial invariant this is `IsRun.norm_sub_le_of_tube`. -/
theorem IsRun.adm_and_norm_sub_le_of_tube [CompleteSpace E] (hY : IsRun M τ N Y)
    (hP : DLRAProblem F A (τ 0) (τ N) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A (τ 0) (τ N) ρ))
    (hadm : ∀ n < N, ∀ Y₀ Y₁, Adm n Y₀ → ‖Y₀ - A (τ n)‖ ≤ R n → M (τ n) (τ (n + 1)) Y₀ Y₁ →
      Adm (n + 1) Y₁)
    (hloc : ∀ n < N, ∀ Y₀ Y₁, Adm n Y₀ → ‖Y₀ - A (τ n)‖ ≤ R n → M (τ n) (τ (n + 1)) Y₀ Y₁ →
      HasLocalError F (τ n) (τ (n + 1)) Y₀ Y₁ (δ n))
    (hY₀ : Adm 0 (Y 0))
    (hR : ∀ n < N, Real.exp (L * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k ≤ R n)
    (hsmall : ∀ n < N, R n + 2 * B * (τ (n + 1) - τ n) < ρ) :
    ∀ n ≤ N, Adm n (Y n) ∧
      ‖Y n - A (τ n)‖ ≤ Real.exp (L * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
        ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k := by
  -- the error bound over the first `n` steps, if the values before step `n` satisfy `Adm`
  have key : ∀ n ≤ N, (∀ k < n, Adm k (Y k)) →
      ‖Y n - A (τ n)‖ ≤ Real.exp (L * (τ n - τ 0)) * ‖Y 0 - A (τ 0)‖ +
        ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k := by
    intro n hn hadmn
    have hτn : τ n ≤ τ N := hY.grid.le_of_le hn le_rfl
    exact (hP.mono le_rfl hτn le_rfl).norm_sub_le_of_hasLocalError
      (hc.mono fun p hp => ⟨⟨hp.1.1, hp.1.2.trans hτn⟩, hp.2⟩) (hY.grid.of_le hn)
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

/-- **Existence of a run and error bound for a step relation with an invariant.** Let `τ` be a
grid, `(F, A)` a problem on a tube (`DLRAProblem`) with `F` continuous on the tube, `M` a step
relation and `Adm n` predicates on the values. Suppose that from every value `Y₀` at time `τ n`
with `Adm n Y₀` and `‖Y₀ - A (τ n)‖ ≤ R n`

* a step of `M` exists,
* every step of `M` ends at a value with `Adm (n + 1)`,
* every step of `M` has local error `δ n`.

If `Adm 0 Y₀`, the error bound is at most `R n` for `n < N`, and
`R n + 2 B (τ (n + 1) - τ n) < ρ`, then there is a run `Y 0 = Y₀, …, Y N` of `M`, and for `n ≤ N`

  `Adm n (Y n)` and
  `‖Y n - A (τ n)‖ ≤ e^{L (τ n - τ 0)} ‖Y₀ - A (τ 0)‖ + ∑_{k<n} e^{L (τ n - τ (k + 1))} δ k`.

Nothing is assumed about `F` outside the tube and nothing about steps from other values: the
error bound for the run constructed so far shows that they do not occur. -/
theorem exists_isRun_norm_sub_le_of_tube [CompleteSpace E] (hτ : IsGrid τ N)
    (hP : DLRAProblem F A (τ 0) (τ N) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A (τ 0) (τ N) ρ))
    (hex : ∀ n < N, ∀ Y₀, Adm n Y₀ → ‖Y₀ - A (τ n)‖ ≤ R n → ∃ Y₁, M (τ n) (τ (n + 1)) Y₀ Y₁)
    (hadm : ∀ n < N, ∀ Y₀ Y₁, Adm n Y₀ → ‖Y₀ - A (τ n)‖ ≤ R n → M (τ n) (τ (n + 1)) Y₀ Y₁ →
      Adm (n + 1) Y₁)
    (hloc : ∀ n < N, ∀ Y₀ Y₁, Adm n Y₀ → ‖Y₀ - A (τ n)‖ ≤ R n → M (τ n) (τ (n + 1)) Y₀ Y₁ →
      HasLocalError F (τ n) (τ (n + 1)) Y₀ Y₁ (δ n))
    {Y₀ : E} (hY₀ : Adm 0 Y₀)
    (hR : ∀ n < N, Real.exp (L * (τ n - τ 0)) * ‖Y₀ - A (τ 0)‖ +
      ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k ≤ R n)
    (hsmall : ∀ n < N, R n + 2 * B * (τ (n + 1) - τ n) < ρ) :
    ∃ Y : ℕ → E, Y 0 = Y₀ ∧ IsRun M τ N Y ∧ ∀ n ≤ N, Adm n (Y n) ∧
      ‖Y n - A (τ n)‖ ≤ Real.exp (L * (τ n - τ 0)) * ‖Y₀ - A (τ 0)‖ +
        ∑ k ∈ range n, Real.exp (L * (τ n - τ (k + 1))) * δ k := by
  obtain ⟨Y, hY0, hY⟩ : ∃ Y : ℕ → E, Y 0 = Y₀ ∧ IsRun M τ N Y := by
    refine exists_isRun hτ Y₀ fun n hn Y hY0 hY => ?_
    subst hY0
    have hτn : τ n ≤ τ N := hτ.le_of_le hn.le le_rfl
    -- the run constructed so far keeps the invariant and satisfies the error bound
    have hpre := hY.adm_and_norm_sub_le_of_tube (Adm := Adm) (R := R) (δ := δ)
      (hP.mono le_rfl hτn le_rfl) (hc.mono fun p hp => ⟨⟨hp.1.1, hp.1.2.trans hτn⟩, hp.2⟩)
      (fun k hk => hadm k (hk.trans hn)) (fun k hk => hloc k (hk.trans hn)) hY₀
      (fun k hk => hR k (hk.trans hn)) (fun k hk => hsmall k (hk.trans hn)) n le_rfl
    exact hex n hn (Y n) hpre.1 (hpre.2.trans (hR n hn))
  subst hY0
  exact ⟨Y, rfl, hY, hY.adm_and_norm_sub_le_of_tube hP hc hadm hloc hY₀ hR hsmall⟩

end Run

/-! ### The uniform grid -/

section Uniform

variable {F : ℝ → E → E} {A : ℝ → E} {M : StepRel E} {Adm : ℕ → E → Prop} {N : ℕ} {Y : ℕ → E}
  {t₀ h T c δ₀ ρ L B : ℝ}

/-- **Tube theorem for runs with an invariant on the uniform grid.** Let `(F, A)` be a
`DLRAProblem` over `[t₀, t₀ + N h]` with tube radius `ρ`, `F` continuous on the tube, and let `Y`
be a run of the step relation `M` on the grid `t₀ + n h`. Suppose every step `n` of `M` whose
start value satisfies `Adm n` and lies within the error bound `e^{L T} δ₀ + T e^{L T} c` of `A`
ends at a value with `Adm (n + 1)` and has local error `h c`. If `Adm 0 (Y 0)`, the error bound
plus `2 B h` is below `ρ`, `‖Y 0 - A t₀‖ ≤ δ₀` and `N h ≤ T`, then every `Y n` satisfies `Adm n`
and the error bound. For the trivial invariant this is `IsRun.norm_sub_le_of_tube_uniformGrid`. -/
theorem IsRun.adm_and_norm_sub_le_of_tube_uniformGrid [CompleteSpace E]
    (hY : IsRun M (uniformGrid t₀ h) N Y) (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hadm : ∀ n < N, ∀ Y₀ Y₁, Adm n Y₀ →
      ‖Y₀ - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c →
      M (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ → Adm (n + 1) Y₁)
    (hloc : ∀ n < N, ∀ Y₀ Y₁, Adm n Y₀ →
      ‖Y₀ - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c →
      M (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ →
      HasLocalError F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ (h * c))
    (hc₀ : 0 ≤ c) (hY₀ : Adm 0 (Y 0)) (hδ : ‖Y 0 - A t₀‖ ≤ δ₀) (hNT : N * h ≤ T)
    (hsmall : Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c + 2 * B * h < ρ) :
    ∀ n ≤ N, Adm n (Y n) ∧
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c := by
  obtain rfl | hN := Nat.eq_zero_or_pos N
  · intro n hn
    obtain rfl := Nat.le_zero.1 hn
    exact ⟨hY₀, hY.norm_sub_le_of_tube_uniformGrid hP hc
      (fun n hn => absurd hn (Nat.not_lt_zero n)) hc₀ hδ hNT hsmall 0 le_rfl⟩
  have hh : 0 ≤ h := by simpa [uniformGrid] using hY.grid.mono 0 hN
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
  have hb : ∀ k ≤ N, Real.exp (L * (uniformGrid t₀ h k - uniformGrid t₀ h 0)) *
      ‖Y 0 - A (uniformGrid t₀ h 0)‖ + ∑ j ∈ range k,
        Real.exp (L * (uniformGrid t₀ h k - uniformGrid t₀ h (j + 1))) * (h * c) ≤
      Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c := fun k hk =>
    uniformGrid_errorBound_le t₀ hP.L_nonneg hh hc₀
      ((mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) hh).trans hNT) (norm_nonneg _)
      (by rw [e0]; exact hδ)
  intro n hn
  have key := hY.adm_and_norm_sub_le_of_tube (Adm := Adm)
    (R := fun _ => Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c) (δ := fun _ => h * c)
    hP0 hc0
    (fun k hk Y₀ Y₁ hY₀ hnear hstep => by
      rw [e k] at hstep
      exact hadm k hk Y₀ Y₁ hY₀ hnear hstep)
    (fun k hk Y₀ Y₁ hY₀ hnear hstep => by
      rw [e k] at hstep ⊢
      exact hloc k hk Y₀ Y₁ hY₀ hnear hstep)
    hY₀ (fun k hk => hb k hk.le)
    (fun k _ => by
      rw [uniformGrid_succ_sub]
      exact hsmall) n hn
  exact ⟨key.1, key.2.trans (hb n hn)⟩

/-- **Existence of a run and error bound on the uniform grid, for a step relation with an
invariant.** Let `(F, A)` be a `DLRAProblem` over `[t₀, t₀ + N h]` with tube radius `ρ` and `F`
continuous on the tube. Suppose that from every value at time `t₀ + n h` that satisfies `Adm n`
and lies within the error bound `e^{L T} δ₀ + T e^{L T} c` of `A` a step of `M` exists, and that
every such step ends at a value with `Adm (n + 1)` and has local error `h c`. If `Adm 0 Y₀`,
`‖Y₀ - A t₀‖ ≤ δ₀`, `N h ≤ T` and the error bound plus `2 B h` is below `ρ`, then there is a run
`Y 0 = Y₀, …, Y N` of `M`, and every `Y n` satisfies `Adm n` and the error bound. -/
theorem exists_isRun_norm_sub_le_of_tube_uniformGrid [CompleteSpace E]
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hex : ∀ n < N, ∀ Y₀, Adm n Y₀ →
      ‖Y₀ - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c →
      ∃ Y₁, M (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁)
    (hadm : ∀ n < N, ∀ Y₀ Y₁, Adm n Y₀ →
      ‖Y₀ - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c →
      M (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ → Adm (n + 1) Y₁)
    (hloc : ∀ n < N, ∀ Y₀ Y₁, Adm n Y₀ →
      ‖Y₀ - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c →
      M (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ →
      HasLocalError F (t₀ + n * h) (t₀ + (n + 1) * h) Y₀ Y₁ (h * c))
    (hc₀ : 0 ≤ c) (hh : 0 ≤ h) (hNT : N * h ≤ T) {Y₀ : E} (hY₀ : Adm 0 Y₀)
    (hδ : ‖Y₀ - A t₀‖ ≤ δ₀)
    (hsmall : Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c + 2 * B * h < ρ) :
    ∃ Y : ℕ → E, Y 0 = Y₀ ∧ IsRun M (uniformGrid t₀ h) N Y ∧ ∀ n ≤ N, Adm n (Y n) ∧
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c := by
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
  have hb : ∀ k ≤ N, Real.exp (L * (uniformGrid t₀ h k - uniformGrid t₀ h 0)) *
      ‖Y₀ - A (uniformGrid t₀ h 0)‖ + ∑ j ∈ range k,
        Real.exp (L * (uniformGrid t₀ h k - uniformGrid t₀ h (j + 1))) * (h * c) ≤
      Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c := fun k hk =>
    uniformGrid_errorBound_le t₀ hP.L_nonneg hh hc₀
      ((mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) hh).trans hNT) (norm_nonneg _)
      (by rw [e0]; exact hδ)
  obtain ⟨Y, hY0, hY, hbd⟩ := exists_isRun_norm_sub_le_of_tube (M := M) (Adm := Adm)
    (R := fun _ => Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * c) (δ := fun _ => h * c)
    (isGrid_uniformGrid hh N) hP0 hc0
    (fun k hk Z₀ hZ₀ hnear => by
      rw [e k]
      exact hex k hk Z₀ hZ₀ hnear)
    (fun k hk Z₀ Z₁ hZ₀ hnear hstep => by
      rw [e k] at hstep
      exact hadm k hk Z₀ Z₁ hZ₀ hnear hstep)
    (fun k hk Z₀ Z₁ hZ₀ hnear hstep => by
      rw [e k] at hstep ⊢
      exact hloc k hk Z₀ Z₁ hZ₀ hnear hstep)
    hY₀ (fun k hk => hb k hk.le)
    (fun k _ => by
      rw [uniformGrid_succ_sub]
      exact hsmall)
  exact ⟨Y, hY0, hY, fun n hn => ⟨(hbd n hn).1, (hbd n hn).2.trans (hb n hn)⟩⟩

end Uniform

/-! ### Methods defined for all fields -/

/-- A **one-step method**: a map from fields `F : ℝ → E → E` to step relations.
`M F t₀ t₁ Y₀ Y₁` says that `Y₁` is a result of one step of the method for the differential
equation `y' = F(t, y)` from the value `Y₀` at time `t₀` to time `t₁`. A step relation
(`StepRel`) describes the method for one field; the dependence on the field is needed to compare
the steps of a field on a tube with the steps of its globally Lipschitz extension. -/
abbrev StepMethod (E : Type*) : Type _ := (ℝ → E → E) → StepRel E

/-- The method `M` is **tube-local** with admissible values `Adm` and margin constant `κ`: its
steps exist for globally Lipschitz fields, keep `Adm`, and near a solution do not see the field
outside a tube. These are the properties (E), (I), (T) of one step from which
`StepMethod.IsTubeLocal.exists_run_norm_sub_le` constructs a run that satisfies the error
bound. -/
structure StepMethod.IsTubeLocal (M : StepMethod E) (Adm : E → Prop) (κ : ℝ) : Prop where
  /-- (E) A step exists from every value with `Adm`, for every globally Lipschitz field that is
  continuous in time on the step interval. No bound on the field is assumed. -/
  exists_step : ∀ {G : ℝ → E → E} {L t₀ t₁ : ℝ} {Y₀ : E}, IsLipschitzField G L →
    (∀ x, ContinuousOn (fun t => G t x) (Icc t₀ t₁)) → t₀ ≤ t₁ → Adm Y₀ → ∃ Y₁, M G t₀ t₁ Y₀ Y₁
  /-- (I) A forward step from a value with `Adm` ends at a value with `Adm`. -/
  adm_of_step : ∀ {G : ℝ → E → E} {t₀ t₁ : ℝ} {Y₀ Y₁ : E}, t₀ ≤ t₁ → Adm Y₀ →
    M G t₀ t₁ Y₀ Y₁ → Adm Y₁
  /-- (T) If `F` is bounded by `B` on the tube of radius `ρ` around a solution `A` and the start
  value has the margin `‖Y₀ - A t₀‖ + κ B (t₁ - t₀) < ρ`, then a step of the extended field
  `tubeExt F A a b ρ` from `Y₀` is a step of `F`. -/
  step_of_tubeExt : ∀ {F : ℝ → E → E} {A : ℝ → E} {a b ρ B t₀ t₁ : ℝ} {Y₀ Y₁ : E},
    IsBoundedOnTube F A a b ρ B → 0 ≤ B → a ≤ t₀ → t₁ ≤ b → t₀ ≤ t₁ → ODESolution F A t₀ t₁ →
    Adm Y₀ → ‖Y₀ - A t₀‖ + κ * B * (t₁ - t₀) < ρ → M (tubeExt F A a b ρ) t₀ t₁ Y₀ Y₁ →
    M F t₀ t₁ Y₀ Y₁

section Method

variable {F : ℝ → E → E} {A : ℝ → E} {M : StepMethod E} {Adm : E → Prop} {κ κ₂ : ℝ} {N : ℕ}
  {t₀ h T c δ ρ L B : ℝ}

/-- The margin constant of a tube-local method can be increased. -/
theorem StepMethod.IsTubeLocal.mono (hM : M.IsTubeLocal Adm κ) (hκ : κ ≤ κ₂) :
    M.IsTubeLocal Adm κ₂ where
  exists_step := hM.exists_step
  adm_of_step := hM.adm_of_step
  step_of_tubeExt := fun hFB hB ha hb h01 hA hY₀ hsmall hstep => by
    have hle := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hκ hB) (sub_nonneg.2 h01)
    exact hM.step_of_tubeExt hFB hB ha hb h01 hA hY₀ (by linarith) hstep

/-- **Existence of a run and error bound for a tube-local method.** Let `A` solve `y' = F(t, y)`
on `[t₀, t₀ + N h]`, and let `F` be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ`
around `A` (`DLRAProblem`) and continuous there. Let the method `M` be tube-local with admissible
values `Adm` and margin constant `κ ≥ 2` (`StepMethod.IsTubeLocal`), and suppose that every step
`n` of `M F` whose start value satisfies `Adm` and lies within the error bound of `A` has local
error `h c`. Let `0 ≤ h`, `N h ≤ T`, and let `Y₀` satisfy `Adm Y₀` and `‖Y₀ - A t₀‖ ≤ δ`. If

  `e^{L T} δ + T e^{L T} c + κ B h < ρ`,

then the method can be run from `Y₀`: there are `Y 0 = Y₀, Y 1, …, Y N`, each obtained from the
previous one by a step of `M F` of size `h`, with

  `Adm (Y n)` and `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} c` for all `n ≤ N`.

Nothing is assumed about `F` outside the tube. The bound holds for every run
(`IsRun.norm_sub_le_of_tube_uniformGrid`, `IsRun.adm_and_norm_sub_le_of_tube_uniformGrid`). -/
theorem StepMethod.IsTubeLocal.exists_run_norm_sub_le [CompleteSpace E]
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
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) * c := by
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg N) hh).trans hNT
  have hBh : 0 ≤ B * h := mul_nonneg hP.B_nonneg hh
  have hκB : 2 * (B * h) ≤ κ * (B * h) := mul_le_mul_of_nonneg_right hκ hBh
  have hR : 0 ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) * c :=
    add_nonneg (mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans hδ))
      (mul_nonneg (mul_nonneg hT (Real.exp_pos _).le) hc₀)
  have hρ : 0 ≤ ρ := by linarith
  have hGL : IsLipschitzField (tubeExt F A t₀ (t₀ + N * h) ρ) L :=
    isLipschitzField_tubeExt hP.lipschitz hP.L_nonneg hρ
  have hGc : ∀ x, ContinuousOn (fun t => tubeExt F A t₀ (t₀ + N * h) ρ t x)
      (Icc t₀ (t₀ + N * h)) := fun x => continuousOn_tubeExt hc hP.sol.cont hρ x
  refine exists_isRun_norm_sub_le_of_tube_uniformGrid (M := M F) (Adm := fun _ => Adm) hP hc
    (fun n hn Y₀ hY₀ hnear => ?_) (fun n hn Y₀ Y₁ hY₀ _ hstep => ?_) hloc hc₀ hh hNT hY₀ hδ
    (by linarith)
  · -- a step of the extended field exists, and it is a step of `F`
    obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hn
    obtain ⟨Y₁, hY₁⟩ := hM.exists_step hGL (fun x => (hGc x).mono (Icc_subset_Icc ha hb)) h01
      hY₀
    exact ⟨Y₁, hM.step_of_tubeExt hP.bounded hP.B_nonneg ha hb h01 (hP.sol.mono ha hb) hY₀
      (by rw [hsub]; linarith) hY₁⟩
  · exact hM.adm_of_step (uniformGrid_step (t₀ := t₀) hh hn).2.1 hY₀ hstep

end Method

/-! ### Non-vacuity: the explicit Euler method -/

section Examples

/-- The explicit Euler method `Y₁ = Y₀ + (t₁ - t₀) G(t₀, Y₀)` is tube-local for every margin
constant `κ ≥ 0`, with every value admissible: the step evaluates the field only at the start
value. -/
private theorem isTubeLocal_euler_aux {κ : ℝ} (hκ : 0 ≤ κ) :
    StepMethod.IsTubeLocal (E := E) (fun G s₀ s₁ Y₀ Y₁ => Y₁ = Y₀ + (s₁ - s₀) • G s₀ Y₀)
      (fun _ => True) κ where
  exists_step := fun _ _ _ _ => ⟨_, rfl⟩
  adm_of_step := fun _ _ _ => trivial
  step_of_tubeExt := @fun F A a b ρ B t₀ t₁ Y₀ Y₁ _ hB ha hb h01 _ _ hsmall hstep => by
    have h0 : 0 ≤ κ * B * (t₁ - t₀) := mul_nonneg (mul_nonneg hκ hB) (sub_nonneg.2 h01)
    have hmem : t₀ ∈ Icc a b := ⟨ha, h01.trans hb⟩
    have hnear : ‖Y₀ - A t₀‖ ≤ ρ := by linarith
    simpa only [tubeExt_eq hmem hnear] using hstep

/-- **Non-vacuity of `StepMethod.IsTubeLocal`**: the explicit Euler method is tube-local. -/
example : StepMethod.IsTubeLocal (E := E) (fun G s₀ s₁ Y₀ Y₁ => Y₁ = Y₀ + (s₁ - s₀) • G s₀ Y₀)
    (fun _ => True) 2 :=
  isTubeLocal_euler_aux zero_le_two

/-- **Non-vacuity of `StepMethod.IsTubeLocal.exists_run_norm_sub_le`**, for the explicit Euler
method and the nonzero constant field `F t x = v` with the solution `A t = x₀ + (t - t₀) v`. The
field is Lipschitz with constant `0` and bounded by `‖v‖` on every tube, and an Euler step is
exact, so its local error is `h · 0`. The theorem gives an Euler run from every `Y₀` with
`‖Y₀ - x₀‖ ≤ δ` that stays within `δ` of the solution, if `δ + 2 ‖v‖ h < ρ`. -/
example [CompleteSpace E] (v x₀ Y₀ : E) {t₀ h T δ ρ : ℝ} {N : ℕ} (hh : 0 ≤ h) (hNT : N * h ≤ T)
    (hδ : ‖Y₀ - x₀‖ ≤ δ) (hsmall : δ + 2 * ‖v‖ * h < ρ) :
    ∃ Y : ℕ → E, Y 0 = Y₀ ∧
      IsRun (fun s₀ s₁ Y₀ Y₁ => Y₁ = Y₀ + (s₁ - s₀) • v) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, ‖Y n - (x₀ + ((n : ℝ) * h) • v)‖ ≤ δ := by
  have aff : ∀ (y₀ : E) (a b : ℝ),
      ODESolution (fun _ _ => v) (fun t => y₀ + (t - a) • v) a b := fun y₀ a b =>
    ⟨by fun_prop, fun t _ => by
      have hd : HasDerivAt (fun t : ℝ => y₀ + (t - a) • v) v t := by
        simpa using (((hasDerivAt_id t).sub_const a).smul_const v).const_add y₀
      exact hd.hasDerivWithinAt⟩
  have hP : DLRAProblem (fun _ _ => v) (fun t => x₀ + (t - t₀) • v) t₀ (t₀ + N * h) ρ 0 ‖v‖ :=
    ⟨aff x₀ t₀ _, le_rfl, norm_nonneg v, fun t _ x y _ _ => by simp, fun t _ x _ => le_rfl⟩
  obtain ⟨Y, hY0, hY, hbd⟩ := (isTubeLocal_euler_aux (E := E) zero_le_two).exists_run_norm_sub_le
    le_rfl hP continuousOn_const (c := 0) (T := T) (δ := δ)
    (fun n _ Z₀ Z₁ _ _ hstep Φ hΦ hΦ₀ => by
      have hΨ := aff Z₀ (t₀ + n * h) (t₀ + (n + 1) * h)
      have hd := dist_le_of_trajectories_ODE (v := fun _ _ => v) (K := 0) (δ := 0)
        (fun _ => LipschitzWith.const v) hΨ.cont hΨ.deriv hΦ.cont hΦ.deriv (by simp [hΦ₀])
        (t₀ + (n + 1) * h) (right_mem_Icc.2 (by nlinarith))
      rw [zero_mul, dist_le_zero] at hd
      rw [hstep, ← hd]
      simp)
    le_rfl hh hNT trivial (by simpa using hδ) (by simpa using hsmall)
  exact ⟨Y, hY0, hY, fun n hn => by simpa using (hbd n hn).2⟩

end Examples

end LeanDLRA
