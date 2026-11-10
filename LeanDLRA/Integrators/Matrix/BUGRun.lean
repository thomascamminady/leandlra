import LeanDLRA.Integrators.Matrix.BUGTube
import LeanDLRA.Integrators.Method
import LeanDLRA.Matrix.LowRankDistance

/-!
# Runs of the fixed-rank BUG integrator: existence and error bound

This file closes the theory of the fixed-rank BUG integrator for a matrix differential equation
`Y' = F(t, Y)` [CerutiLubich2022]: it shows that the integrator can be run, and that every run
stays close to the exact solution. It is the place to start reading about the integrator.

**Setting.** Let `A` be a solution of `Y' = F(t, Y)` on `[t₀, t₀ + N h]`. The field `F` is only
assumed to be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around `A`
(`DLRAProblem F A t₀ (t₀ + N h) ρ L B`), jointly continuous there, and to have a small normal
component at the rank-`r` matrices in the tube (`FactoredNormalBoundOn F r _ ε`): for every
`Y = U S Vᵀ` with orthonormal `U`, `V` the part `(I - U Uᵀ) F(t, Y) (I - V Vᵀ)` of the field that
points away from both the column and the row space of `Y` has norm at most `ε`. Nothing is
assumed about `F` outside the tube.

**Result** (`MatrixBUG.exists_run_norm_sub_le`). For every start value `Y₀` of rank at most `r`
with `‖Y₀ - A t₀‖ ≤ δ` there are matrices `Y 0 = Y₀, Y 1, …, Y N`, each obtained from the previous
one by a BUG step of size `h` (`IsRun (MatrixBUG.stepRel F r) (uniformGrid t₀ h) N Y`), all of
rank at most `r`, with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (c₁ ε + c₂ h)` for all `n ≤ N`,

where `N h ≤ T`, `c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`, and `h ≤ H`
(the right-hand side is `bugGlobalBound L B H T δ ε h`). The constants do not depend on the
singular values of the matrices `Y n`: the bound is robust to small singular values. The only
further hypothesis is that the right-hand side is smaller than the tube radius,
`bugGlobalBound L B H T δ ε h + 4 B h < ρ`; this can always be achieved by small `δ` and `h` if
`T e^{L T} c₁ ε < ρ` (`exists_bugGlobalBound_lt`). The same bound holds for *every* run, not only
for the one constructed (`MatrixBUG.IsRun.norm_sub_le`).

## Main results

* `MatrixBUG.exists_isStep_of_lipschitz`: a BUG step exists for every Lipschitz field that is
  continuous in time on the step interval; no bound on the field is needed.
* `MatrixBUG.exists_stepRel_iff`: a step of `MatrixBUG.stepRel` from `Y₀` exists if and only if
  `Y₀` has rank at most `r`.
* `MatrixBUG.exists_run`: for a globally Lipschitz field there is a run on every grid from every
  start value of rank at most `r`.
* `MatrixBUG.IsRun.norm_sub_le`: every run satisfies the error bound.
* `MatrixBUG.norm_sub_le_of_isStep`: the error bound for a chain of factor steps
  (`MatrixBUG.IsStep`).
* `MatrixBUG.isTubeLocal_stepRel`: the integrator is a tube-local method
  (`StepMethod.IsTubeLocal`) with the matrices of rank at most `r` as admissible values and
  margin constant `4`.
* `MatrixBUG.exists_run_norm_sub_le`: a run exists, has rank at most `r` and satisfies the error
  bound.
* `exists_bugGlobalBound_lt`: the smallness condition can be met.

The examples at the end apply the results to the linear field `F(t, Y) = M Y + Y Nᵀ + G` near a
stationary point. This field is not bounded, so it is covered only by the tube form.

## Implementation notes

`MatrixBUG.exists_run_norm_sub_le` is an instance of the theorem for tube-local methods,
`StepMethod.IsTubeLocal.exists_run_norm_sub_le`. That theorem constructs the run step by step:
the field `F` is replaced by its extension `tubeExt F A t₀ (t₀ + N h) ρ`, which is globally
Lipschitz, so a step of the extension exists; the error bound for the run constructed so far
shows that the last value lies well inside the tube, and there the steps of the extension are
steps of `F`. What is specific to the BUG integrator is collected in
`MatrixBUG.isTubeLocal_stepRel` (existence of a step for globally Lipschitz fields,
`MatrixBUG.exists_stepRel`; the rank bound, `MatrixBUG.stepRel.rank_le`; locality,
`MatrixBUG.stepRel_tubeExt_iff_of_near`) and in the local error
`MatrixBUG.stepRel.hasLocalError_of_tube`.

## References

* [CerutiLubich2022] G. Ceruti, Ch. Lubich, *An unconventional robust integrator for dynamical
  low-rank approximation*, BIT Numer. Math. 62 (2022), Theorem 4.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixBUG

/-! ### Existence of one step -/

section Lift

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [InnerProductSpace ℝ E'] [CompleteSpace E']

/-- **Existence for conjugated Lipschitz fields.** If `F` is Lipschitz and continuous in time on
`[a, b]`, every field of the form `f t x = Ψ (F t (Φ x))` with continuous linear maps `Φ`, `Ψ`
(the fields of the K-, L- and S-step of the BUG integrator have this form) has a solution on
`[a, b]` with arbitrary initial value. In contrast to `exists_odeSolution_conj` the field need
not be bounded. -/
theorem exists_odeSolution_conj_of_lipschitz {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L)
    {a b : ℝ} (hc : ∀ x, ContinuousOn (fun t => F t x) (Icc a b)) (Φ : E' →L[ℝ] E)
    (Ψ : E →L[ℝ] E') {f : ℝ → E' → E'} (hf : ∀ t x, f t x = Ψ (F t (Φ x))) (hab : a ≤ b)
    (y₀ : E') : ∃ y : ℝ → E', ODESolution f y a b ∧ y a = y₀ := by
  obtain rfl : f = fun t x => Ψ (F t (Φ x)) := funext fun t => funext fun x => hf t x
  have hF' : IsLipschitzField F (max L 0) := fun t x y =>
    (hF t x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hcΨ : ∀ x, ContinuousOn (fun t => Ψ (F t (Φ x))) (Icc a b) := fun x =>
    Ψ.continuous.comp_continuousOn (hc (Φ x))
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn (hcΨ 0)
  exact exists_ODESolution_of_linearGrowth (isLipschitzField_conj hF' (le_max_right _ _) Φ Ψ)
    (mul_nonneg (mul_nonneg (norm_nonneg _) (le_max_right _ _)) (norm_nonneg _)) hK hcΨ hab y₀

end Lift

section Exists

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
  {L : ℝ}

/-- **A BUG step exists.** If `F` is Lipschitz and continuous in time on `[t₀, t₁]`, the matrices
`U₀`, `V₀` have orthonormal columns and `r ≤ m`, `r ≤ n`, then for every `S₀` the K-, L- and
S-step have solutions and the new bases exist: there are `U₁`, `V₁`, `K`, `Lf`, `S` forming a
step of the matrix BUG integrator (`IsStep`). In contrast to `exists_isStep` the field need not be
bounded, the Lipschitz constant may have any sign, and continuity in time is needed only on the
step interval. -/
theorem exists_isStep_of_lipschitz (hF : IsLipschitzField F L) {t₀ t₁ : ℝ}
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁)
    {U₀ : Matrix m (Fin r) ℝ} (S₀ : Matrix (Fin r) (Fin r) ℝ) {V₀ : Matrix n (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) :
    ∃ (U₁ : Matrix m (Fin r) ℝ) (V₁ : Matrix n (Fin r) ℝ) (K : ℝ → Matrix m (Fin r) ℝ)
      (Lf : ℝ → Matrix n (Fin r) ℝ) (S : ℝ → Matrix (Fin r) (Fin r) ℝ),
      IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S := by
  obtain ⟨K, hK, hK₀⟩ := exists_odeSolution_conj_of_lipschitz hF hc _ _
    (fun t x => kField_eq V₀ t x) h01 (U₀ * S₀)
  obtain ⟨Lf, hLf, hLf₀⟩ := exists_odeSolution_conj_of_lipschitz hF hc _ _
    (fun t x => lField_eq U₀ t x) h01 (V₀ * S₀ᵀ)
  obtain ⟨U₁, hU₁, hKcap⟩ := exists_qr hrm (K t₁)
  obtain ⟨V₁, hV₁, hLcap⟩ := exists_qr hrn (Lf t₁)
  obtain ⟨S, hS, hS₀⟩ := exists_odeSolution_conj_of_lipschitz hF hc _ _
    (fun t x => sField_eq U₁ V₁ t x) h01 (U₁ᵀ * U₀ * S₀ * (V₀ᵀ * V₁))
  exact ⟨U₁, V₁, K, Lf, S, hU₀, hV₀, hK, hK₀, hLf, hLf₀, hU₁, hKcap, hV₁, hLcap, hS, hS₀⟩

/-- `exists_isStep` is the special case of `exists_isStep_of_lipschitz` for a field that is
continuous in time on all of `ℝ`; the bound on the field is not used. -/
example {B : ℝ} (hF : IsLipschitzField F L) (_hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    {U₀ : Matrix m (Fin r) ℝ} (S₀ : Matrix (Fin r) (Fin r) ℝ) {V₀ : Matrix n (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) :
    ∃ (U₁ : Matrix m (Fin r) ℝ) (V₁ : Matrix n (Fin r) ℝ) (K : ℝ → Matrix m (Fin r) ℝ)
      (Lf : ℝ → Matrix n (Fin r) ℝ) (S : ℝ → Matrix (Fin r) (Fin r) ℝ),
      IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S :=
  exists_isStep_of_lipschitz hF (fun Y => (hc Y).continuousOn) h01 S₀ hU₀ hV₀ hrm hrn

/-- **A step of the BUG integrator exists from every start value of rank at most `r`.** If `F` is
Lipschitz and continuous in time on `[t₀, t₁]` and `r ≤ m`, `r ≤ n`, then every `Y₀` of rank at
most `r` has a successor `Y₁` under `MatrixBUG.stepRel F r`: factor `Y₀ = U₀ S₀ V₀ᵀ` with
orthonormal `U₀`, `V₀` (`exists_factor_of_rank_le`) and apply `exists_isStep_of_lipschitz`. -/
theorem exists_stepRel (hF : IsLipschitzField F L) {t₀ t₁ : ℝ}
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) : ∃ Y₁, stepRel F r t₀ t₁ Y₀ Y₁ := by
  classical
  obtain ⟨U₀, S₀, V₀, hU₀, hV₀, rfl⟩ := exists_factor_of_rank_le hY₀ hrm hrn
  obtain ⟨U₁, V₁, K, Lf, S, hs⟩ := exists_isStep_of_lipschitz hF hc h01 S₀ hU₀ hV₀ hrm hrn
  exact ⟨_, hs.stepRel⟩

/-- A step of the BUG integrator from `Y₀` exists if and only if `Y₀` has rank at most `r`
(for a Lipschitz field that is continuous in time on the step interval, and `r ≤ m`, `r ≤ n`). -/
theorem exists_stepRel_iff (hF : IsLipschitzField F L) {t₀ t₁ : ℝ}
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ} :
    (∃ Y₁, stepRel F r t₀ t₁ Y₀ Y₁) ↔ Y₀.rank ≤ r :=
  ⟨fun ⟨_, h⟩ => h.rank_start_le, exists_stepRel hF hc h01 hrm hrn⟩

/-- **Runs of the BUG integrator exist.** If `F` is Lipschitz (globally) and continuous in time on
`[τ 0, τ N]` and `r ≤ m`, `r ≤ n`, then on the grid `τ` there is a run of `N` steps of the
fixed-rank BUG integrator from every start value `Y₀` of rank at most `r`. No bound on the field
is needed. For fields that are Lipschitz only near a solution see `exists_run_norm_sub_le`. -/
theorem exists_run (hF : IsLipschitzField F L) {τ : ℕ → ℝ} {N : ℕ} (hτ : IsGrid τ N)
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc (τ 0) (τ N))) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) τ N Y := by
  refine exists_isRun hτ Y₀ fun n hn Y hY0 hY => ?_
  have hsub : Icc (τ n) (τ (n + 1)) ⊆ Icc (τ 0) (τ N) :=
    Icc_subset_Icc (hτ.le_of_le n.zero_le hn.le) (hτ.le_of_le (Nat.succ_le_of_lt hn) le_rfl)
  exact exists_stepRel hF (fun Z => (hc Z).mono hsub) (hτ.mono n hn) hrm hrn
    (IsRun.rank_le hY (by rw [hY0]; exact hY₀) n le_rfl)

end Exists

/-! ### The error bound for runs -/

section Error

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {t₀ h H T ρ L B ε δ : ℝ} {N : ℕ}

/-- **Every run of the fixed-rank BUG integrator satisfies the robust error bound**
[CerutiLubich2022, Thm. 4]. Let `A` solve `Y' = F(t, Y)` on `[t₀, t₀ + N h]` and let `F` be
`L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around `A` (`DLRAProblem`), jointly
continuous there, with normal component at most `ε` at the rank-`r` matrices of the tube
(`FactoredNormalBoundOn`). Let `Y 0, …, Y N` be a run of the integrator with step size `h ≤ H`,
`N h ≤ T`, and `‖Y 0 - A t₀‖ ≤ δ`. If the bound below is smaller than the tube radius,
`bugGlobalBound L B H T δ ε h + 4 B h < ρ`, then for all `n ≤ N`

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (bugC₁ L H ε + bugC₂ L B H h)`,

the right-hand side being `bugGlobalBound L B H T δ ε h`. The constants do not depend on the
singular values of the `Y n`.

Nothing is assumed about `F` outside the tube, and no auxiliary exact solutions started at the
numerical values appear: they are constructed in the proof
(`IsRun.norm_sub_le_of_tube_uniformGrid`), and the local error of each step comes from
`MatrixBUG.stepRel.hasLocalError_of_tube`. -/
theorem IsRun.norm_sub_le {Y : ℕ → Matrix m n ℝ}
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hsmall : bugGlobalBound L B H T δ ε h + 4 * B * h < ρ)
    (hY : IsRun (stepRel F r) (uniformGrid t₀ h) N Y) (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ bugGlobalBound L B H T δ ε h := by
  have hH : 0 ≤ H := hh.trans hhH
  have hc₀ : 0 ≤ bugC₁ L H * ε + bugC₂ L B H * h :=
    add_nonneg (mul_nonneg (bugC₁_nonneg hP.L_nonneg hH) hε₀)
      (mul_nonneg (bugC₂_nonneg hP.L_nonneg hP.B_nonneg hH) hh)
  have hBh : 0 ≤ B * h := mul_nonneg hP.B_nonneg hh
  rw [bugGlobalBound_eq] at hsmall ⊢
  refine hY.norm_sub_le_of_tube_uniformGrid (T := T) (δ₀ := δ)
    (c := bugC₁ L H * ε + bugC₂ L B H * h) hP hc (fun n hn Y₀ Y₁ hnear hstep => ?_) hc₀ hδ hNT
    (by linarith)
  obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hn
  have hloc := hstep.hasLocalError_of_tube hε hP.lipschitz hP.L_nonneg hP.bounded hP.B_nonneg
    ha hb h01 (hsub.le.trans hhH) (hP.sol.mono ha hb) (by rw [hsub]; linarith)
  rwa [hsub] at hloc

/-- **Error bound for a chain of factor steps.** The statement of `MatrixBUG.IsRun.norm_sub_le`
for factors: if `(U j, Sm j, V j)` are advanced by steps of the matrix BUG integrator
(`IsStep`) of size `h` and `Sm (j + 1)` is the value of the S-step at the end of step `j`, then
the matrices `U j * Sm j * (V j)ᵀ` satisfy the error bound. -/
theorem norm_sub_le_of_isStep {U : ℕ → Matrix m (Fin r) ℝ} {Sm : ℕ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℕ → Matrix n (Fin r) ℝ} {K : ℕ → ℝ → Matrix m (Fin r) ℝ}
    {Lf : ℕ → ℝ → Matrix n (Fin r) ℝ} {S : ℕ → ℝ → Matrix (Fin r) (Fin r) ℝ}
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hsmall : bugGlobalBound L B H T δ ε h + 4 * B * h < ρ)
    (hstep : ∀ j < N, IsStep F (t₀ + j * h) (t₀ + (j + 1) * h) (U j) (Sm j) (V j) (U (j + 1))
      (V (j + 1)) (K j) (Lf j) (S j))
    (hS : ∀ j < N, Sm (j + 1) = S j (t₀ + (j + 1) * h))
    (hδ : ‖U 0 * Sm 0 * (V 0)ᵀ - A t₀‖ ≤ δ) :
    ∀ j ≤ N, ‖U j * Sm j * (V j)ᵀ - A (t₀ + j * h)‖ ≤ bugGlobalBound L B H T δ ε h := by
  have e : ∀ j : ℕ, uniformGrid t₀ h (j + 1) = t₀ + ((j : ℝ) + 1) * h := fun j => by
    simp [uniformGrid]
  have hrun : IsRun (stepRel F r) (uniformGrid t₀ h) N fun j => U j * Sm j * (V j)ᵀ :=
    isRun_stepRel_of_isStep (U := U) (Sm := Sm) (V := V) (K := K) (Lf := Lf) (S := S)
      (isGrid_uniformGrid hh N) (fun j hj => by rw [e j]; exact hstep j hj)
      (fun j hj => by rw [e j]; exact hS j hj)
  exact IsRun.norm_sub_le hP hc hε hε₀ hh hhH hNT hsmall hrun hδ

omit [DecidableEq m] [DecidableEq n] in
/-- **The fixed-rank BUG integrator is a tube-local method** (`StepMethod.IsTubeLocal`), with
the matrices of rank at most `r` as admissible values and margin constant `4`:

* a step exists from every matrix of rank at most `r`, for every globally Lipschitz field that is
  continuous in time on the step interval (`MatrixBUG.exists_stepRel`);
* the result of a step has rank at most `r` (`MatrixBUG.stepRel.rank_le`);
* if `‖Y₀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, a step from `Y₀` of the extended field
  `tubeExt F A a b ρ` is a step of `F` (`MatrixBUG.stepRel_tubeExt_iff_of_near`).

With the local error `MatrixBUG.stepRel.hasLocalError_of_tube` this is all that
`StepMethod.IsTubeLocal.exists_run_norm_sub_le` needs. -/
theorem isTubeLocal_stepRel (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) :
    StepMethod.IsTubeLocal (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => stepRel G r)
      (fun Y => Y.rank ≤ r) 4 where
  exists_step := fun hG hc h01 hY₀ => exists_stepRel hG hc h01 hrm hrn hY₀
  adm_of_step := fun _ _ hstep => hstep.rank_le
  step_of_tubeExt := fun hFB hB ha hb h01 hA _ hsmall hstep =>
    (stepRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 hstep

/-- **Existence and robust error bound for the fixed-rank BUG integrator**
[CerutiLubich2022, Thm. 4]. Let `A` solve `Y' = F(t, Y)` on `[t₀, t₀ + N h]`, and let `F` be
`L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around `A` (`DLRAProblem`), jointly
continuous there, with normal component at most `ε` at the rank-`r` matrices of the tube
(`FactoredNormalBoundOn`). Let `r ≤ m`, `r ≤ n`, let the step size satisfy `0 ≤ h ≤ H` and
`N h ≤ T`, and let `Y₀` be a start value of rank at most `r` with `‖Y₀ - A t₀‖ ≤ δ`. If

  `bugGlobalBound L B H T δ ε h + 4 B h < ρ`,

then the integrator can be run from `Y₀`: there are `Y 0 = Y₀, Y 1, …, Y N`, each obtained from
the previous one by a BUG step of size `h`, all of rank at most `r`, with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (bugC₁ L H ε + bugC₂ L B H h)` for all `n ≤ N`,

the right-hand side being `bugGlobalBound L B H T δ ε h`. The constants are independent of the
singular values of the matrices `Y n`, and nothing is assumed about `F` outside the tube.

This is `StepMethod.IsTubeLocal.exists_run_norm_sub_le` for the tube-local method
`MatrixBUG.isTubeLocal_stepRel`: the steps exist because the error bound keeps the run constructed
so far inside the tube, where `F` and its globally Lipschitz extension
`tubeExt F A t₀ (t₀ + N h) ρ` have the same steps. The bound itself holds for every run
(`MatrixBUG.IsRun.norm_sub_le`), and the smallness condition can be met by small `δ` and `h`
(`exists_bugGlobalBound_lt`). -/
theorem exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : bugGlobalBound L B H T δ ε h + 4 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤ bugGlobalBound L B H T δ ε h := by
  have hH : 0 ≤ H := hh.trans hhH
  have hc₀ : 0 ≤ bugC₁ L H * ε + bugC₂ L B H * h :=
    add_nonneg (mul_nonneg (bugC₁_nonneg hP.L_nonneg hH) hε₀)
      (mul_nonneg (bugC₂_nonneg hP.L_nonneg hP.B_nonneg hH) hh)
  have hBh : 0 ≤ B * h := mul_nonneg hP.B_nonneg hh
  rw [bugGlobalBound_eq] at hsmall ⊢
  refine (isTubeLocal_stepRel hrm hrn).exists_run_norm_sub_le (by norm_num) hP hc
    (fun k hk Z₀ Z₁ _ hnear hstep => ?_) hc₀ hh hNT hY₀ hδ hsmall
  -- the local error of a step that starts within the error bound of `A`
  obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hk
  have hloc := stepRel.hasLocalError_of_tube hstep hε hP.lipschitz hP.L_nonneg hP.bounded
    hP.B_nonneg ha hb h01 (hsub.le.trans hhH) (hP.sol.mono ha hb) (by rw [hsub]; linarith)
  rwa [hsub] at hloc

end Error

end MatrixBUG

/-! ### The smallness condition can be met -/

/-- **The smallness condition of the BUG error bound can be met.** If the part of the bound that
comes from the normal component of the field is smaller than the tube radius,
`T e^{L T} bugC₁ L H ε < ρ`, then there are a start tolerance `δ > 0` and a step size
`0 < h ≤ H` with `bugGlobalBound L B H T δ ε h + 4 B h < ρ`, the hypothesis of
`MatrixBUG.exists_run_norm_sub_le`. -/
theorem exists_bugGlobalBound_lt {L B H T ε ρ : ℝ} (hH : 0 < H)
    (hε : T * Real.exp (L * T) * bugC₁ L H * ε < ρ) :
    ∃ δ > 0, ∃ h > 0, h ≤ H ∧ bugGlobalBound L B H T δ ε h + 4 * B * h < ρ := by
  have key : ∀ δ h : ℝ, bugGlobalBound L B H T δ ε h + 4 * B * h =
      Real.exp (L * T) * δ + T * Real.exp (L * T) * bugC₁ L H * ε +
        (T * Real.exp (L * T) * bugC₂ L B H + 4 * B) * h := fun δ h => by
    unfold bugGlobalBound
    ring
  have he := Real.exp_pos (L * T)
  generalize Real.exp (L * T) = e at key he hε
  generalize T * e * bugC₁ L H * ε = a at key hε
  generalize T * e * bugC₂ L B H + 4 * B = c at key
  have hg : 0 < ρ - a := sub_pos.2 hε
  have hc : 0 < 4 * (|c| + 1) := by positivity
  have hc₁ : |c| + 1 ≠ 0 := by positivity
  have hm : 0 < (ρ - a) / (4 * (|c| + 1)) := div_pos hg hc
  refine ⟨(ρ - a) / (4 * e), div_pos hg (by positivity), min H ((ρ - a) / (4 * (|c| + 1))),
    lt_min hH hm, min_le_left _ _, ?_⟩
  have h1 : e * ((ρ - a) / (4 * e)) = (ρ - a) / 4 := by
    rw [mul_div_assoc', mul_comm e (ρ - a), mul_div_mul_right _ _ he.ne']
  have h2 : c * min H ((ρ - a) / (4 * (|c| + 1))) ≤ (ρ - a) / 4 :=
    calc c * min H ((ρ - a) / (4 * (|c| + 1)))
        ≤ |c| * min H ((ρ - a) / (4 * (|c| + 1))) :=
          mul_le_mul_of_nonneg_right (le_abs_self c) (le_min hH.le hm.le)
      _ ≤ |c| * ((ρ - a) / (4 * (|c| + 1))) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg c)
      _ ≤ (|c| + 1) * ((ρ - a) / (4 * (|c| + 1))) :=
          mul_le_mul_of_nonneg_right (by linarith) hm.le
      _ = (ρ - a) / 4 := by
          rw [mul_div_assoc', mul_comm (|c| + 1) (ρ - a), mul_div_mul_right _ _ hc₁]
  rw [key, h1]
  linarith

namespace MatrixBUG

/-! ### Non-vacuity: the linear field `F(t, Y) = M Y + Y Nᵀ + G` -/

section Examples

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}

/-- The linear field `Y ↦ M Y + Y Nᵀ + G` changes by at most `(‖M‖ + ‖N‖) ‖X - Y‖`. -/
private theorem norm_linear_sub_le_aux (M : Matrix m m ℝ) (N : Matrix n n ℝ)
    (G X Y : Matrix m n ℝ) :
    ‖M * X + X * Nᵀ + G - (M * Y + Y * Nᵀ + G)‖ ≤ (‖M‖ + ‖N‖) * ‖X - Y‖ :=
  calc ‖M * X + X * Nᵀ + G - (M * Y + Y * Nᵀ + G)‖ = ‖M * (X - Y) + (X - Y) * Nᵀ‖ := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
        congr 1
        abel
    _ ≤ ‖M‖ * ‖X - Y‖ + ‖X - Y‖ * ‖N‖ :=
        (norm_add_le _ _).trans (add_le_add (Frobenius.norm_mul_le _ _)
          ((Frobenius.norm_mul_le _ _).trans_eq (by rw [Frobenius.norm_transpose])))
    _ = (‖M‖ + ‖N‖) * ‖X - Y‖ := by ring

/-- The linear field is globally Lipschitz with constant `‖M‖ + ‖N‖`. -/
private theorem isLipschitzField_linear_aux (M : Matrix m m ℝ) (N : Matrix n n ℝ)
    (G : Matrix m n ℝ) :
    IsLipschitzField (fun _ (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G) (‖M‖ + ‖N‖) :=
  fun _ X Y => norm_linear_sub_le_aux M N G X Y

/-- Around a stationary point `C` the linear field is a `DLRAProblem` on the tube of every radius
`ρ ≥ 0`, with Lipschitz constant `‖M‖ + ‖N‖` and bound `(‖M‖ + ‖N‖) ρ`. -/
private theorem dlraProblem_linear_aux (M : Matrix m m ℝ) (N : Matrix n n ℝ)
    (G C : Matrix m n ℝ) (hC : M * C + C * Nᵀ + G = 0) (a b : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    DLRAProblem (fun _ Y => M * Y + Y * Nᵀ + G) (fun _ => C) a b ρ (‖M‖ + ‖N‖)
      ((‖M‖ + ‖N‖) * ρ) := by
  have hL : 0 ≤ ‖M‖ + ‖N‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨⟨continuousOn_const, fun t _ => ?_⟩, hL, mul_nonneg hL hρ,
    fun _ _ X Y _ _ => norm_linear_sub_le_aux M N G X Y, fun _ _ X hX => ?_⟩
  · exact (hasDerivWithinAt_const t (Ici t) C).congr_deriv hC.symm
  · calc ‖M * X + X * Nᵀ + G‖ = ‖M * X + X * Nᵀ + G - (M * C + C * Nᵀ + G)‖ := by
          rw [hC, sub_zero]
      _ ≤ (‖M‖ + ‖N‖) * ‖X - C‖ := norm_linear_sub_le_aux M N G X C
      _ ≤ (‖M‖ + ‖N‖) * ρ := mul_le_mul_of_nonneg_left hX hL

/-- The linear field is jointly continuous. -/
private theorem continuous_uncurry_linear_aux (M : Matrix m m ℝ) (N : Matrix n n ℝ)
    (G : Matrix m n ℝ) :
    Continuous (Function.uncurry fun (_ : ℝ) (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G) := by
  change Continuous fun p : ℝ × Matrix m n ℝ =>
    Frobenius.leftMulCLM M p.2 + Frobenius.rightMulCLM Nᵀ p.2 + G
  exact (((Frobenius.leftMulCLM M).continuous.comp continuous_snd).add
    ((Frobenius.rightMulCLM Nᵀ).continuous.comp continuous_snd)).add continuous_const

/-- **Non-vacuity of `exists_run`.** The linear field `F(t, Y) = M Y + Y Nᵀ + G` is globally
Lipschitz but not bounded (so `exists_isStep` does not apply to it). On every grid it has a run
of the fixed-rank BUG integrator from every start value of rank at most `r`. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G : Matrix m n ℝ) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) {τ : ℕ → ℝ} {K : ℕ} (hτ : IsGrid τ K) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (stepRel (fun _ Y => M * Y + Y * Nᵀ + G) r) τ K Y :=
  exists_run (isLipschitzField_linear_aux M N G) hτ (fun _ => continuousOn_const) hrm hrn hY₀

variable [DecidableEq m] [DecidableEq n]

/-- The linear part `M Y + Y Nᵀ` has no normal component at `Y = U S Vᵀ`, so the linear field
satisfies the factored normal bound on every region with `ε = ‖G‖`. -/
private theorem factoredNormalBoundOn_linear_aux (M : Matrix m m ℝ) (N : Matrix n n ℝ)
    (G : Matrix m n ℝ) (D : Set (ℝ × Matrix m n ℝ)) :
    FactoredNormalBoundOn (fun _ (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G) r D ‖G‖ := by
  intro t U V S hU hV _
  have hU' : (1 - U * Uᵀ) * U = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one, sub_self]
  have hV' : Vᵀ * (1 - V * Vᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hV, Matrix.one_mul, sub_self]
  have h1 : (1 - U * Uᵀ) * (M * (U * S * Vᵀ)) * (1 - V * Vᵀ) = 0 := by
    rw [show (1 - U * Uᵀ) * (M * (U * S * Vᵀ)) * (1 - V * Vᵀ) =
        (1 - U * Uᵀ) * (M * U * S) * (Vᵀ * (1 - V * Vᵀ)) by simp only [Matrix.mul_assoc],
      hV', Matrix.mul_zero]
  have h2 : (1 - U * Uᵀ) * (U * S * Vᵀ * Nᵀ) * (1 - V * Vᵀ) = 0 := by
    rw [show (1 - U * Uᵀ) * (U * S * Vᵀ * Nᵀ) * (1 - V * Vᵀ) =
        (1 - U * Uᵀ) * U * (S * Vᵀ * Nᵀ * (1 - V * Vᵀ)) by simp only [Matrix.mul_assoc],
      hU', Matrix.zero_mul]
  change ‖(1 - U * Uᵀ) * (M * (U * S * Vᵀ) + U * S * Vᵀ * Nᵀ + G) * (1 - V * Vᵀ)‖ ≤ ‖G‖
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, h1, h2, zero_add, zero_add]
  exact norm_normal_le hU hV G

/-- The stationary-point hypothesis `M C + C Nᵀ + G = 0` of the examples below can be met with
any source term `G`, in particular a nonzero one: take `M = -1`, `N = 0` and `C = G`. -/
example (G : Matrix m n ℝ) : (-1 : Matrix m m ℝ) * G + G * (0 : Matrix n n ℝ)ᵀ + G = 0 := by
  rw [Matrix.neg_mul, Matrix.one_mul, Matrix.transpose_zero, Matrix.mul_zero, add_zero,
    neg_add_cancel]

/-- **Non-vacuity of the existence and error theorem, tube form.** The linear field
`F(t, Y) = M Y + Y Nᵀ + G` with a stationary point `C` (`M C + C Nᵀ + G = 0`) is not bounded, so
only the tube form of the theory applies to it. On the tube of radius `ρ` around the constant
solution `A(t) = C` it is `(‖M‖ + ‖N‖)`-Lipschitz and bounded by `(‖M‖ + ‖N‖) ρ`, and its normal
component at rank-`r` matrices is at most `‖G‖`. Hence, under the smallness condition, the
fixed-rank BUG integrator can be run from every `Y₀` of rank at most `r` near `C`, and the run
satisfies the robust error bound with `ε = ‖G‖`. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    (t₀ : ℝ) {ρ T H δ h : ℝ} {K : ℕ} (hρ : 0 ≤ ρ) (hh : 0 ≤ h) (hhH : h ≤ H)
    (hKT : K * h ≤ T) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - C‖ ≤ δ)
    (hsmall : bugGlobalBound (‖M‖ + ‖N‖) ((‖M‖ + ‖N‖) * ρ) H T δ ‖G‖ h +
      4 * ((‖M‖ + ‖N‖) * ρ) * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (stepRel (fun _ Y => M * Y + Y * Nᵀ + G) r) (uniformGrid t₀ h) K Y ∧
      ∀ j ≤ K, (Y j).rank ≤ r ∧
        ‖Y j - C‖ ≤ bugGlobalBound (‖M‖ + ‖N‖) ((‖M‖ + ‖N‖) * ρ) H T δ ‖G‖ h :=
  exists_run_norm_sub_le (A := fun _ => C) (dlraProblem_linear_aux M N G C hC _ _ hρ)
    (continuous_uncurry_linear_aux M N G).continuousOn
    (factoredNormalBoundOn_linear_aux M N G _) (norm_nonneg G) hh hhH hKT hrm hrn hY₀ hδ hsmall

/-- **Non-vacuity, closed form.** For the linear field of the previous example, if the
contribution of the source term to the error bound is smaller than the tube radius,
`T e^{L T} bugC₁ L H ‖G‖ < ρ` with `L = ‖M‖ + ‖N‖`, then there are a start tolerance `δ > 0` and a
step size `h > 0` such that for every number `K` of steps with `K h ≤ T` and every start value
`Y₀` of rank at most `r` with `‖Y₀ - C‖ ≤ δ` a run of the fixed-rank BUG integrator exists, stays
of rank at most `r` and satisfies the robust error bound. No hypothesis is left open. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    (t₀ : ℝ) {ρ T H : ℝ} (hT : 0 ≤ T) (hH : 0 < H)
    (hG : T * Real.exp ((‖M‖ + ‖N‖) * T) * bugC₁ (‖M‖ + ‖N‖) H * ‖G‖ < ρ) :
    ∃ δ > 0, ∃ h > 0, ∀ K : ℕ, K * h ≤ T → ∀ Y₀ : Matrix m n ℝ, Y₀.rank ≤ r → ‖Y₀ - C‖ ≤ δ →
      ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
        IsRun (stepRel (fun _ Y => M * Y + Y * Nᵀ + G) r) (uniformGrid t₀ h) K Y ∧
        ∀ j ≤ K, (Y j).rank ≤ r ∧
          ‖Y j - C‖ ≤ bugGlobalBound (‖M‖ + ‖N‖) ((‖M‖ + ‖N‖) * ρ) H T δ ‖G‖ h := by
  have hL : 0 ≤ ‖M‖ + ‖N‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hρ : 0 ≤ ρ := (mul_nonneg (mul_nonneg (mul_nonneg hT (Real.exp_pos _).le)
    (bugC₁_nonneg hL hH.le)) (norm_nonneg _)).trans hG.le
  obtain ⟨δ, hδ, h, hh, hhH, hsmall⟩ :=
    exists_bugGlobalBound_lt (B := (‖M‖ + ‖N‖) * ρ) hH hG
  exact ⟨δ, hδ, h, hh, fun K hK Y₀ hY₀ hY₀δ =>
    exists_run_norm_sub_le (A := fun _ => C) (dlraProblem_linear_aux M N G C hC _ _ hρ)
      (continuous_uncurry_linear_aux M N G).continuousOn
      (factoredNormalBoundOn_linear_aux M N G _) (norm_nonneg G) hh.le hhH hK hrm hrn hY₀ hY₀δ
      hsmall⟩

/-- **Non-vacuity of `MatrixBUG.IsRun.norm_sub_le`.** Every run of the fixed-rank BUG integrator
for the linear field that starts near the stationary point `C` satisfies the error bound. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) (t₀ : ℝ) {ρ T H δ h : ℝ} {K : ℕ} (hρ : 0 ≤ ρ) (hh : 0 ≤ h)
    (hhH : h ≤ H) (hKT : K * h ≤ T) {Y : ℕ → Matrix m n ℝ}
    (hY : IsRun (stepRel (fun _ Y => M * Y + Y * Nᵀ + G) r) (uniformGrid t₀ h) K Y)
    (hδ : ‖Y 0 - C‖ ≤ δ)
    (hsmall : bugGlobalBound (‖M‖ + ‖N‖) ((‖M‖ + ‖N‖) * ρ) H T δ ‖G‖ h +
      4 * ((‖M‖ + ‖N‖) * ρ) * h < ρ) :
    ∀ j ≤ K, ‖Y j - C‖ ≤ bugGlobalBound (‖M‖ + ‖N‖) ((‖M‖ + ‖N‖) * ρ) H T δ ‖G‖ h :=
  IsRun.norm_sub_le (A := fun _ => C) (dlraProblem_linear_aux M N G C hC _ _ hρ)
    (continuous_uncurry_linear_aux M N G).continuousOn
    (factoredNormalBoundOn_linear_aux M N G _) (norm_nonneg G) hh hhH hKT hsmall hY hδ

end Examples

end MatrixBUG

end LeanDLRA
