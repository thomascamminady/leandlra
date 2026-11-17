import LeanDLRA.HighOrder.ProjectedRK
import LeanDLRA.Integrators.Matrix.FlowDistance
import LeanDLRA.Integrators.Matrix.ProjectedEuler
import LeanDLRA.HighOrder.Defs

/-!
# Projected Runge–Kutta methods for matrices: runs and global error

The projected Runge–Kutta method of Kieri and Vandereycken [KieriVandereycken2019] with an
explicit tableau `(a, b, c)` of `s` stages advances a matrix `Y₀` of rank at most `r` over
`[t₀, t₁]`, `h = t₁ - t₀`, by

  `η_j = ℛ(Y₀ + h ∑_l a_{jl} P(η_l) F(t₀ + c_l h, η_l))`,
  `Y₁ = ℛ(Y₀ + h ∑_j b_j P(η_j) F(t₀ + c_j h, η_j))`

([KieriVandereycken2019], eqs. (26), (27)), with tangent projectors `P(η_j) = tangentProj U_j V_j`
at `η_j = U_j S_j V_jᵀ` and a `κ`-quasi-optimal retraction `ℛ` to the matrices of rank at most `r`.
The stages `η_j` have rank at most `r`; the arguments of the retraction have rank at most `2 s r`.

This file states the method as a step relation (`MatrixPRK.stepRel`), shows that it is a
tube-local method, proves its local error near a reference solution and obtains the existence of
runs and the global error bound ([KieriVandereycken2019], Theorem 6) from
`StepMethod.IsTubeLocal.exists_run_norm_sub_le`.

**Assumptions.** As for the projected Euler method (`MatrixProjEuler`): the field is Lipschitz
and bounded on a tube around the exact solution (`DLRAProblem`), continuous there, with normal
part at most `ε` at the factored rank-`r` points of the tube (`FactoredNormalBoundOn`); the
one-sided constant `ℓ` of the paper is not used (the bounds carry `e^{L T}`), and neither the
projected solution nor full rank of the numerical values is assumed. The paper's smoothness
assumption enters only through the order `p` and the stage orders `q_j` of the classical
Runge–Kutta method (their (19) and (30)), and these are **hypotheses** here (`hRK`): the
classical Runge–Kutta step of `F` from every admissible start value near `A` must have local
error `K h^{p+1}` and stage errors `K h^{q_j+1}`. The library has no order theory of Runge–Kutta
methods, so this makes the theorem weaker than the run theorems of the other integrators, whose
local errors are proved from the hypotheses on `F`. The distance of the exact flow to the
matrices of rank at most `r` (their (15)) is bounded by `distLR_flow_le_exp_of_tube`.

## Main definitions

The definitions are in `LeanDLRA/HighOrder/Defs.lean`.

* `MatrixPRK.stageDeriv`: the projected stage derivative `P(η_l) F(t₀ + c_l h, η_l)`.
* `MatrixPRK.stepRel F r κ a b c`: one step of the projected Runge–Kutta method.

## Main results

* `MatrixPRK.exists_stepRel`, `MatrixPRK.isTubeLocal_stepRel`: steps exist from every matrix of
  rank at most `r`, and the method is tube-local with margin constant `(1 + κ) α + 1`,
  `α = tabWeight a b`.
* `MatrixPRK.stepRel.hasLocalError_of_tube` (local error, [KieriVandereycken2019], Lemma 7 and
  proof of Theorem 6): `h · localErrorConst a b L κ · (ε + ε e^{L h} + K h^{q'})`.
* `MatrixPRK.exists_run_norm_sub_le` ([KieriVandereycken2019], Theorem 6): runs exist, have rank
  at most `r` and satisfy
  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} C (ε + ε e^{L h} + K h^{q'})`,
  `C = localErrorConst a b L κ`,
  for every admissible exponent `q'` (`ProjectedRK.admissible_min_q₂`,
  `ProjectedRK.admissible_of_b₂_eq_zero`: the exponent `q` of Theorem 6).

## References

* [KieriVandereycken2019], §5
-/

open Set Finset
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixPRK

open LeanDLRA.RungeKuttaBUG LeanDLRA.ProjectedRK

/-! ### The step relation -/

section Rel

variable {m n : Type*} [Fintype m] [Fintype n] {r s : ℕ}

/- `MatrixPRK.stageDeriv`, `MatrixPRK.stageSum` and `MatrixPRK.stepRel` are defined in
`LeanDLRA/HighOrder/Defs.lean`. -/

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {κ t₀ t₁ : ℝ} {a : Fin s → Fin s → ℝ}
  {b c : Fin s → ℝ} {Y₀ Y₁ : Matrix m n ℝ}

/-- The result of a projected Runge–Kutta step has rank at most `r`. -/
theorem stepRel.rank_le (h : stepRel F r κ a b c t₀ t₁ Y₀ Y₁) : Y₁.rank ≤ r := by
  obtain ⟨U, S, V, -, -, hr, -⟩ := h
  exact hr

/-- All values of a run of the projected Runge–Kutta method have rank at most `r`, provided the
start value has. -/
theorem IsRun.rank_le {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → Matrix m n ℝ}
    (hY : IsRun (stepRel F r κ a b c) τ N Y) (h0 : (Y 0).rank ≤ r) : ∀ k ≤ N, (Y k).rank ≤ r
  | 0, _ => h0
  | k + 1, hk => (hY.step k hk).rank_le

/-- A combination `Y₀ + h ∑_l w_l d_l` with `∑_l |w_l| ≤ α` and `‖d_l‖ ≤ B` for `w_l ≠ 0` is
within `α B h` of `Y₀`. -/
theorem norm_comb_sub_le {w : Fin s → ℝ} {d : Fin s → Matrix m n ℝ} {h α B : ℝ} (hh : 0 ≤ h)
    (hB : 0 ≤ B) (hw : ∑ l, |w l| ≤ α) (hd : ∀ l, w l ≠ 0 → ‖d l‖ ≤ B) :
    ‖Y₀ + h • ∑ l, w l • d l - Y₀‖ ≤ α * B * h := by
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hh]
  have h₁ : ‖∑ l, w l • d l‖ ≤ α * B :=
    calc ‖∑ l, w l • d l‖ ≤ ∑ l, ‖w l • d l‖ := norm_sum_le _ _
      _ = ∑ l, |w l| * ‖d l‖ := by simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ α * B := sum_abs_mul_le hB hd hw
  calc h * ‖∑ l, w l • d l‖ ≤ h * (α * B) := mul_le_mul_of_nonneg_left h₁ hh
    _ = α * B * h := by ring

/-- The projected stage derivative is not longer than the field at the stage. -/
theorem norm_stageDeriv_le {U : Fin s → Matrix m (Fin r) ℝ} {S : Fin s → Matrix (Fin r) (Fin r) ℝ}
    {V : Fin s → Matrix n (Fin r) ℝ} {h : ℝ} (horth : ∀ j, (U j)ᵀ * U j = 1 ∧ (V j)ᵀ * V j = 1)
    (l : Fin s) :
    ‖stageDeriv F c t₀ h U S V l‖ ≤ ‖F (t₀ + c l * h) (U l * S l * (V l)ᵀ)‖ :=
  (isOrthProj_tangentProj (horth l).1 (horth l).2).norm_le _

/-- **A priori bound of a stage.** If the start value has rank at most `r` and the field is
bounded by `B` at the earlier stages that enter stage `j`, then the stage `η_j` of a projected
Runge–Kutta step is within `(1 + κ) α B h` of the start value, `α = tabWeight a b`. -/
theorem norm_stage_sub_start_le {U : Fin s → Matrix m (Fin r) ℝ}
    {S : Fin s → Matrix (Fin r) (Fin r) ℝ} {V : Fin s → Matrix n (Fin r) ℝ} {h B : ℝ}
    (horth : ∀ j, (U j)ᵀ * U j = 1 ∧ (V j)ᵀ * V j = 1) (hY₀ : Y₀.rank ≤ r) (hκ : 0 ≤ κ)
    (hh : 0 ≤ h) (hB : 0 ≤ B) (j : Fin s)
    (hj : ‖U j * S j * (V j)ᵀ - stageSum F c t₀ h Y₀ (a j) U S V‖ ≤
      κ * distLR r (stageSum F c t₀ h Y₀ (a j) U S V))
    (hbd : ∀ l, a j l ≠ 0 → ‖F (t₀ + c l * h) (U l * S l * (V l)ᵀ)‖ ≤ B) :
    ‖U j * S j * (V j)ᵀ - Y₀‖ ≤ (1 + κ) * (tabWeight a b * B * h) := by
  set X := stageSum F c t₀ h Y₀ (a j) U S V with hX
  have h₁ : ‖X - Y₀‖ ≤ tabWeight a b * B * h :=
    norm_comb_sub_le hh hB (row_le_tabWeight a b j) fun l hl =>
      (norm_stageDeriv_le horth l).trans (hbd l hl)
  have h₂ : distLR r X ≤ ‖X - Y₀‖ := distLR_le_norm_sub hY₀
  have h₃ := norm_sub_le_norm_sub_add_norm_sub (U j * S j * (V j)ᵀ) X Y₀
  have h₄ := mul_le_mul_of_nonneg_left h₂ hκ
  have h₅ := mul_le_mul_of_nonneg_left h₁ hκ
  linarith

end Rel

/-! ### Existence of steps -/

section Exists

variable {m n : Type*} [Fintype m] [Fintype n] {r s : ℕ}

/-- **A projected Runge–Kutta step exists from every matrix**, for every field, every explicit
tableau and every `κ ≥ 1`, if `r ≤ m` and `r ≤ n`: the stages are chosen one after the other
(`ProjectedRK.exists_explicit_stages`), each as a factorized best approximation of rank at most
`r` (`exists_best_approx`, `exists_factor_of_rank_le`), and the result as a best approximation. -/
theorem exists_stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) {a : Fin s → Fin s → ℝ}
    (b c : Fin s → ℝ) (ha : ∀ i j, i ≤ j → a i j = 0) (t₀ t₁ : ℝ) {κ : ℝ} (hκ : 1 ≤ κ)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) (Y₀ : Matrix m n ℝ) :
    ∃ Y₁, stepRel F r κ a b c t₀ t₁ Y₀ Y₁ := by
  obtain ⟨Z, hZ⟩ := exists_explicit_stages
    (fun j (Z : Fin s → Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ)
      (x : Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ) =>
      x.1ᵀ * x.1 = 1 ∧ x.2.2ᵀ * x.2.2 = 1 ∧
        ‖x.1 * x.2.1 * x.2.2ᵀ - stageSum F c t₀ (t₁ - t₀) Y₀ (a j) (fun l => (Z l).1)
          (fun l => (Z l).2.1) (fun l => (Z l).2.2)‖ ≤
        κ * distLR r (stageSum F c t₀ (t₁ - t₀) Y₀ (a j) (fun l => (Z l).1)
          (fun l => (Z l).2.1) (fun l => (Z l).2.2)))
    (fun j Z Z' x hZZ' hx => by
      have hXe : stageSum F c t₀ (t₁ - t₀) Y₀ (a j) (fun l => (Z l).1) (fun l => (Z l).2.1)
          (fun l => (Z l).2.2) = stageSum F c t₀ (t₁ - t₀) Y₀ (a j) (fun l => (Z' l).1)
          (fun l => (Z' l).2.1) (fun l => (Z' l).2.2) := by
        unfold stageSum
        congr 2
        refine Finset.sum_congr rfl fun l _ => ?_
        by_cases hl : a j l = 0
        · simp [hl]
        · have hlj : l < j := lt_of_not_ge fun hjl => hl (ha j l hjl)
          simp only [stageDeriv, hZZ' l hlj]
      rw [← hXe]
      exact hx)
    (fun j Z => by
      obtain ⟨T, hT, hTd⟩ := exists_best_approx r (stageSum F c t₀ (t₁ - t₀) Y₀ (a j)
        (fun l => (Z l).1) (fun l => (Z l).2.1) (fun l => (Z l).2.2))
      obtain ⟨U, S, V, hU, hV, hTe⟩ := exists_factor_of_rank_le hT hrm hrn
      refine ⟨(U, S, V), hU, hV, ?_⟩
      change ‖U * S * Vᵀ - _‖ ≤ _
      rw [← hTe, norm_sub_rev, hTd]
      exact le_mul_of_one_le_left distLR_nonneg hκ)
  obtain ⟨T, hT, hTd⟩ := exists_best_approx r (stageSum F c t₀ (t₁ - t₀) Y₀ b
    (fun l => (Z l).1) (fun l => (Z l).2.1) (fun l => (Z l).2.2))
  refine ⟨T, fun l => (Z l).1, fun l => (Z l).2.1, fun l => (Z l).2.2,
    fun j => ⟨(hZ j).1, (hZ j).2.1⟩, fun j => (hZ j).2.2, hT, ?_⟩
  rw [norm_sub_rev, hTd]
  exact le_mul_of_one_le_left distLR_nonneg hκ

end Exists

/-! ### Near the reference solution -/

section Tube

variable {m n : Type*} [Fintype m] [Fintype n] {r s : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {κ t₀ t₁ : ℝ} {a : Fin s → Fin s → ℝ}
  {b c : Fin s → ℝ} {Y₀ Y₁ : Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {a₀ b₀ ρ B : ℝ}

/-- **A step of the tube extension near the reference solution is a step of the field.** Let
`F` be bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a₀, b₀]`, let the
nodes satisfy `0 ≤ c_j ≤ 1`, and let `Y₀` have rank at most `r` with
`‖Y₀ - A t₀‖ + ((1 + κ) α + 1) B (t₁ - t₀) < ρ`, `α = tabWeight a b`. Then every stage of a
projected Runge–Kutta step of `tubeExt F A a₀ b₀ ρ` from `Y₀` over `[t₀, t₁] ⊆ [a₀, b₀]` lies
in the tube at its stage time (`MatrixPRK.norm_stage_sub_start_le`: the stages move by at most
`(1 + κ) α B (t₁ - t₀)`), where the extension is `F`; so the step is a step of `F`. -/
theorem stepRel_of_tubeExt (hc : ∀ j, 0 ≤ c j ∧ c j ≤ 1) (hκ : 0 ≤ κ)
    (hFB : IsBoundedOnTube F A a₀ b₀ ρ B) (hB : 0 ≤ B) (ha₀ : a₀ ≤ t₀) (hb₀ : t₁ ≤ b₀)
    (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁) (hY₀ : Y₀.rank ≤ r)
    (hsmall : ‖Y₀ - A t₀‖ + ((1 + κ) * tabWeight a b + 1) * B * (t₁ - t₀) < ρ)
    (hstep : stepRel (tubeExt F A a₀ b₀ ρ) r κ a b c t₀ t₁ Y₀ Y₁) :
    stepRel F r κ a b c t₀ t₁ Y₀ Y₁ := by
  obtain ⟨U, S, V, horth, hstages, hr, hfin⟩ := hstep
  have hh : 0 ≤ t₁ - t₀ := sub_nonneg.2 h01
  have hα := tabWeight_nonneg a b
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB hh
  have hρ : 0 ≤ ρ := by
    have : 0 ≤ ((1 + κ) * tabWeight a b + 1) * B * (t₁ - t₀) := by positivity
    linarith [norm_nonneg (Y₀ - A t₀)]
  have hGB := isBoundedField_tubeExt hFB hB hρ
  -- the stage times lie in `[t₀, t₁]`
  have htj : ∀ j, t₀ ≤ t₀ + c j * (t₁ - t₀) ∧ t₀ + c j * (t₁ - t₀) ≤ t₁ := fun j => by
    have h₁ := mul_nonneg (hc j).1 hh
    have h₂ := mul_le_mul_of_nonneg_right (hc j).2 hh
    constructor <;> linarith
  have hin : ∀ j, ‖U j * S j * (V j)ᵀ - A (t₀ + c j * (t₁ - t₀))‖ ≤ ρ := by
    intro j
    have h₁ := norm_stage_sub_start_le (F := tubeExt F A a₀ b₀ ρ) (b := b) horth hY₀ hκ hh hB j
      (hstages j) fun l _ => hGB _ _
    have h₂ : ‖A (t₀ + c j * (t₁ - t₀)) - A t₀‖ ≤ B * (t₀ + c j * (t₁ - t₀) - t₀) :=
      hA.norm_sub_le (hFB.along hρ ha₀ hb₀) _ (htj j)
    have h₃ : B * (t₀ + c j * (t₁ - t₀) - t₀) ≤ B * (t₁ - t₀) :=
      mul_le_mul_of_nonneg_left (by linarith [(htj j).2]) hB
    have e : U j * S j * (V j)ᵀ - A (t₀ + c j * (t₁ - t₀)) =
        (U j * S j * (V j)ᵀ - Y₀) + (Y₀ - A t₀) - (A (t₀ + c j * (t₁ - t₀)) - A t₀) := by abel
    rw [e]
    have h₄ := norm_sub_le ((U j * S j * (V j)ᵀ - Y₀) + (Y₀ - A t₀))
      (A (t₀ + c j * (t₁ - t₀)) - A t₀)
    have h₅ := norm_add_le (U j * S j * (V j)ᵀ - Y₀) (Y₀ - A t₀)
    have h₆ : ((1 + κ) * tabWeight a b + 1) * B * (t₁ - t₀) =
        (1 + κ) * (tabWeight a b * B * (t₁ - t₀)) + B * (t₁ - t₀) := by ring
    linarith
  have hd : ∀ l, stageDeriv (tubeExt F A a₀ b₀ ρ) c t₀ (t₁ - t₀) U S V l =
      stageDeriv F c t₀ (t₁ - t₀) U S V l := fun l => by
    unfold stageDeriv
    rw [tubeExt_eq ⟨ha₀.trans (htj l).1, (htj l).2.trans hb₀⟩ (hin l)]
  have hsum : ∀ w : Fin s → ℝ, stageSum (tubeExt F A a₀ b₀ ρ) c t₀ (t₁ - t₀) Y₀ w U S V =
      stageSum F c t₀ (t₁ - t₀) Y₀ w U S V := fun w => by
    unfold stageSum
    simp only [hd]
  refine ⟨U, S, V, horth, fun j => ?_, hr, ?_⟩
  · rw [← hsum]; exact hstages j
  · rw [← hsum]; exact hfin

end Tube

/-! ### Local error -/

section Error

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r s : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {κ t₀ t₁ : ℝ} {a : Fin s → Fin s → ℝ}
  {b c : Fin s → ℝ} {Y₀ Y₁ : Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {a₀ b₀ ρ L B ε K : ℝ}

/-- **Local error of a projected Runge–Kutta step near a reference solution**
([KieriVandereycken2019], Lemma 7 and the proof of Theorem 6, with explicit constants and tube
hypotheses). Let `F` be continuous, `L`-Lipschitz and bounded by `B` on the tube of radius `ρ`
around a solution `A` over `[a₀, b₀]`, with normal part at most `ε` at the factored rank-`r`
points of the tube. Let the tableau be explicit with nodes `0 ≤ c_j ≤ 1`, `κ ≥ 0`, and let the
step over `[t₀, t₁] ⊆ [a₀, b₀]`, `h = t₁ - t₀ ≤ 1`, start at `Y₀` of rank at most `r` with
`‖Y₀ - A t₀‖ + ((1 + κ) α + 3) B h < ρ`, `α = tabWeight a b`. Suppose (`hRK`) that the
classical Runge–Kutta step of `F` from `Y₀` has stage errors `K h^{q_j + 1}` and local error
`K h^{p + 1}` with respect to the exact solution through `Y₀`. If `q₂ ≤ q_j` for the later stages
and `q'` is admissible (`q' ≤ p`, `q' ≤ min(q_j, q₂ + 1) + 1` for the later stages with
`b_j ≠ 0`), then the projected step has local error

  `h · localErrorConst a b L κ · (ε + ε e^{L h} + K h^{q'})`.

The proof checks the hypotheses of `ProjectedRK.norm_sub_le_of_stages`: the stages and the
classical stages stay in the tube (a priori bounds, by induction over the stages), the normal
bound and the Lipschitz bound hold there, and the exact solution at the stage times and at `t₁`
is within `h ε e^{L h}` of the matrices of rank at most `r` (`distLR_flow_le_exp_of_tube`). -/
theorem stepRel.hasLocalError_of_tube (hstep : stepRel F r κ a b c t₀ t₁ Y₀ Y₁)
    (ha : ∀ i j, i ≤ j → a i j = 0) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ 1) (hκ : 0 ≤ κ)
    (hε : FactoredNormalBoundOn F r (tubeSet A a₀ b₀ ρ) ε) (hε₀ : 0 ≤ ε)
    (hFL : IsLipschitzOnTube F A a₀ b₀ ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a₀ b₀ ρ B)
    (hB : 0 ≤ B) (hcont : ContinuousOn (Function.uncurry F) (tubeSet A a₀ b₀ ρ))
    (hAc : ContinuousOn A (Icc a₀ b₀)) (ha₀ : a₀ ≤ t₀) (hb₀ : t₁ ≤ b₀) (h01 : t₀ ≤ t₁)
    (hh1 : t₁ - t₀ ≤ 1) (hA : ODESolution F A t₀ t₁) (hY₀ : Y₀.rank ≤ r)
    (hsmall : ‖Y₀ - A t₀‖ + ((1 + κ) * tabWeight a b + 3) * B * (t₁ - t₀) < ρ) (hK : 0 ≤ K)
    {q : Fin s → ℕ} {q₂ p q' : ℕ} (hq : ∀ j : Fin s, 0 < j.val → q₂ ≤ q j) (hqp : q' ≤ p)
    (hqb : ∀ j : Fin s, 0 < j.val → b j ≠ 0 → q' ≤ min (q j) (q₂ + 1) + 1)
    (hRK : ∀ (Zt : Fin s → Matrix m n ℝ) (zt : Matrix m n ℝ),
      IsGalerkinRKStep F a b c (fun _ => 1) 1 t₀ (t₁ - t₀) Y₀ Zt zt →
      ∀ Φ : ℝ → Matrix m n ℝ, ODESolution F Φ t₀ t₁ → Φ t₀ = Y₀ →
        (∀ j : Fin s, 0 < j.val →
          ‖Zt j - Φ (t₀ + c j * (t₁ - t₀))‖ ≤ K * (t₁ - t₀) ^ (q j + 1)) ∧
        ‖zt - Φ t₁‖ ≤ K * (t₁ - t₀) ^ (p + 1)) :
    HasLocalError F t₀ t₁ Y₀ Y₁ ((t₁ - t₀) *
      (localErrorConst a b L κ * (ε + ε * Real.exp (L * (t₁ - t₀)) + K * (t₁ - t₀) ^ q'))) := by
  intro Φ hΦ hΦ₀
  obtain ⟨U, S, V, horth, hstages, -, hfin⟩ := hstep
  set h := t₁ - t₀ with hhdef
  have hh : 0 ≤ h := sub_nonneg.2 h01
  have hα := tabWeight_nonneg a b
  have hBh : 0 ≤ B * h := mul_nonneg hB hh
  have hαB : 0 ≤ (1 + κ) * (tabWeight a b * B * h) := by positivity
  have hρ : 0 ≤ ρ := by
    have : 0 ≤ ((1 + κ) * tabWeight a b + 3) * B * h := by positivity
    linarith [norm_nonneg (Y₀ - A t₀)]
  -- stage times
  have htj : ∀ j, t₀ ≤ t₀ + c j * h ∧ t₀ + c j * h ≤ t₁ := fun j => by
    have h₁ := mul_nonneg (hc j).1 hh
    have h₂ := mul_le_mul_of_nonneg_right (hc j).2 hh
    constructor <;> linarith
  have htjI : ∀ j, t₀ + c j * h ∈ Icc a₀ b₀ := fun j =>
    ⟨ha₀.trans (htj j).1, (htj j).2.trans hb₀⟩
  have hAt : ∀ j, ‖A (t₀ + c j * h) - A t₀‖ ≤ B * h := fun j =>
    (hA.norm_sub_le (hFB.along hρ ha₀ hb₀) _ (htj j)).trans
      (mul_le_mul_of_nonneg_left (by linarith [(htj j).2]) hB)
  -- points near `Y₀` lie in the tube at every stage time
  have hnear : ∀ j (X : Matrix m n ℝ), ‖X - Y₀‖ ≤ (1 + κ) * (tabWeight a b * B * h) →
      ‖X - A (t₀ + c j * h)‖ ≤ ρ := by
    intro j X hX
    have e : X - A (t₀ + c j * h) = (X - Y₀) + (Y₀ - A t₀) - (A (t₀ + c j * h) - A t₀) := by
      abel
    rw [e]
    have h₄ := norm_sub_le ((X - Y₀) + (Y₀ - A t₀)) (A (t₀ + c j * h) - A t₀)
    have h₅ := norm_add_le (X - Y₀) (Y₀ - A t₀)
    have h₆ := hAt j
    linarith
  -- the stages stay near `Y₀`
  have hη : ∀ j, ‖U j * S j * (V j)ᵀ - Y₀‖ ≤ (1 + κ) * (tabWeight a b * B * h) := by
    intro j
    induction j using WellFoundedLT.induction with
    | ind j ih =>
      exact norm_stage_sub_start_le horth hY₀ hκ hh hB j (hstages j) fun l hl =>
        hFB _ (htjI l) _ (hnear l _ (ih l (lt_of_not_ge fun hjl => hl (ha j l hjl))))
  have hinη : ∀ j, ‖U j * S j * (V j)ᵀ - A (t₀ + c j * h)‖ ≤ ρ := fun j => hnear j _ (hη j)
  -- the classical stages
  obtain ⟨Zt, hZt⟩ := exists_explicit_stages (X := Matrix m n ℝ)
    (fun j Z x => x = Y₀ + h • ∑ l, a j l • F (t₀ + c l * h) (Z l))
    (fun j Z Z' x hZZ' hx => by
      rw [hx]
      congr 2
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : a j l = 0
      · simp [hl]
      · rw [hZZ' l (lt_of_not_ge fun hjl => hl (ha j l hjl))])
    (fun j Z => ⟨_, rfl⟩)
  have hZtY : ∀ j, ‖Zt j - Y₀‖ ≤ tabWeight a b * B * h := by
    intro j
    induction j using WellFoundedLT.induction with
    | ind j ih =>
      rw [hZt j]
      refine norm_comb_sub_le hh hB (row_le_tabWeight a b j) fun l hl => ?_
      have hlj : l < j := lt_of_not_ge fun hjl => hl (ha j l hjl)
      refine hFB _ (htjI l) _ (hnear l _ ((ih l hlj).trans ?_))
      have : 0 ≤ κ * (tabWeight a b * B * h) := by positivity
      linarith
  have hinZt : ∀ j, ‖Zt j - A (t₀ + c j * h)‖ ≤ ρ := fun j => hnear j _ (by
    have : 0 ≤ κ * (tabWeight a b * B * h) := by positivity
    linarith [hZtY j])
  obtain ⟨zt, hzt⟩ : ∃ zt, zt = Y₀ + h • ∑ j, b j • F (t₀ + c j * h) (Zt j) := ⟨_, rfl⟩
  have hRKstep : IsGalerkinRKStep F a b c (fun _ => 1) 1 t₀ h Y₀ Zt zt :=
    ⟨fun i => by simpa using hZt i, by simp [hzt]⟩
  obtain ⟨hw, hp⟩ := hRK Zt zt hRKstep Φ hΦ hΦ₀
  -- the exact solution stays close to the matrices of rank at most `r`
  have hclose : ∀ t', t₀ ≤ t' → t' ≤ t₁ →
      ∃ z ∈ {Z : Matrix m n ℝ | Z.rank ≤ r}, ‖z - Φ t'‖ ≤ h * (ε * Real.exp (L * h)) := by
    intro t' h₁ h₂
    have h₃ : B * (t' - t₀) ≤ B * h := mul_le_mul_of_nonneg_left (by linarith) hB
    have hd := distLR_flow_le_exp_of_tube hε hε₀ hFL hL hFB hB hcont hAc ha₀ (h₂.trans hb₀) h₁
      (hA.mono le_rfl h₂) (hΦ.mono le_rfl h₂) (by rw [hΦ₀]; exact hY₀)
      (by rw [hΦ₀]; linarith)
    obtain ⟨z, hz, hzd⟩ := exists_best_approx r (Φ t')
    refine ⟨z, hz, ?_⟩
    rw [norm_sub_rev, hzd]
    refine hd.trans ?_
    have h₄ : (t' - t₀) * ε ≤ h * ε := mul_le_mul_of_nonneg_right (by linarith) hε₀
    have h₅ : Real.exp (L * (t' - t₀)) ≤ Real.exp (L * h) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hL)
    calc (t' - t₀) * ε * Real.exp (L * (t' - t₀)) ≤ h * ε * Real.exp (L * h) :=
          mul_le_mul h₄ h₅ (Real.exp_pos _).le (mul_nonneg hh hε₀)
      _ = h * (ε * Real.exp (L * h)) := by ring
  exact norm_sub_le_of_stages (ℳ := {Z : Matrix m n ℝ | Z.rank ≤ r}) (b := b)
    (g := ε * Real.exp (L * h)) (y := Y₀) (Z := fun j => stageSum F c t₀ h Y₀ (a j) U S V)
    (η := fun j => U j * S j * (V j)ᵀ) (e := stageDeriv F c t₀ h U S V)
    (Fη := fun j => F (t₀ + c j * h) (U j * S j * (V j)ᵀ)) (Zt := Zt)
    (FZt := fun j => F (t₀ + c j * h) (Zt j)) (w := fun j => Φ (t₀ + c j * h))
    ha hκ hL hε₀ (mul_nonneg hε₀ (Real.exp_pos _).le) hK hh hh1 hY₀ (fun j => rfl)
    (fun j z hz => (hstages j).trans (mul_le_mul_of_nonneg_left
      ((distLR_le_norm_sub hz).trans (norm_sub_rev _ _).le) hκ))
    (fun j => by
      change ‖tangentProj (U j) (V j) (F (t₀ + c j * h) (U j * S j * (V j)ᵀ)) -
        F (t₀ + c j * h) (U j * S j * (V j)ᵀ)‖ ≤ ε
      rw [norm_sub_rev, sub_tangentProj_apply]
      exact hε _ (U j) (V j) (S j) (horth j).1 (horth j).2 ⟨htjI j, hinη j⟩)
    (fun j => hFL _ (htjI j) _ _ (hinη j) (hinZt j)) hZt hq hw
    (fun j _ => hclose _ (htj j).1 (htj j).2)
    (fun z hz => hfin.trans (mul_le_mul_of_nonneg_left
      ((distLR_le_norm_sub hz).trans (norm_sub_rev _ _).le) hκ))
    hzt hp (hclose t₁ h01 le_rfl) hqp hqb

end Error

/-! ### The method is tube-local; runs and the global error -/

section Run

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r s : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {a : Fin s → Fin s → ℝ}
  {b c : Fin s → ℝ} {t₀ h T ρ L B ε δ κ K : ℝ} {N : ℕ}

omit [DecidableEq m] [DecidableEq n] in
/-- **The projected Runge–Kutta method is a tube-local method** (`StepMethod.IsTubeLocal`) with
the matrices of rank at most `r` as admissible values and margin constant `(1 + κ) α + 1`,
`α = tabWeight a b`, for an explicit tableau with nodes `0 ≤ c_j ≤ 1`, `κ ≥ 1`, `r ≤ m`,
`r ≤ n`: steps exist from every matrix (`MatrixPRK.exists_stepRel`), their results have rank at
most `r`, and near the reference solution a step of the tube extension is a step of the field
(`MatrixPRK.stepRel_of_tubeExt`). -/
theorem isTubeLocal_stepRel (ha : ∀ i j, i ≤ j → a i j = 0) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ 1)
    (hκ : 1 ≤ κ) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) :
    StepMethod.IsTubeLocal (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => stepRel G r κ a b c)
      (fun Y => Y.rank ≤ r) ((1 + κ) * tabWeight a b + 1) where
  exists_step := fun _ _ _ _ => exists_stepRel _ b c ha _ _ hκ hrm hrn _
  adm_of_step := fun _ _ hstep => hstep.rank_le
  step_of_tubeExt := fun hFB hB ha₀ hb₀ h01 hA hY₀ hsmall hstep =>
    stepRel_of_tubeExt hc (zero_le_one.trans hκ) hFB hB ha₀ hb₀ h01 hA hY₀ hsmall hstep

/-- **Local error of one step of a uniform grid.** Under the hypotheses of the run theorem, a
projected Runge–Kutta step over `[t₀ + k h, t₀ + (k + 1) h]`, `k < N`, `0 ≤ h ≤ 1`, from `Z₀` of
rank at most `r` with `‖Z₀ - A (t₀ + k h)‖ + ((1 + κ) α + 3) B h < ρ` has local error
`h · localErrorConst a b L κ · (ε + ε e^{L h} + K h^{q'})`, provided the classical Runge–Kutta
step of `F` from `Z₀` has stage errors `K h^{q_j + 1}` and local error `K h^{p + 1}`. -/
theorem stepRel.hasLocalError_uniformGrid {k : ℕ} {Z₀ Z₁ : Matrix m n ℝ}
    (hstep : stepRel F r κ a b c (t₀ + k * h) (t₀ + (k + 1) * h) Z₀ Z₁)
    (ha : ∀ i j, i ≤ j → a i j = 0) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ 1) (hκ : 0 ≤ κ)
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hcont : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hk : k < N) (hZ₀ : Z₀.rank ≤ r)
    (hnear : ‖Z₀ - A (t₀ + k * h)‖ + ((1 + κ) * tabWeight a b + 3) * B * h < ρ) (hK : 0 ≤ K)
    {q : Fin s → ℕ} {q₂ p q' : ℕ} (hq : ∀ j : Fin s, 0 < j.val → q₂ ≤ q j) (hqp : q' ≤ p)
    (hqb : ∀ j : Fin s, 0 < j.val → b j ≠ 0 → q' ≤ min (q j) (q₂ + 1) + 1)
    (hRK : ∀ (Zt : Fin s → Matrix m n ℝ) (zt : Matrix m n ℝ),
      IsGalerkinRKStep F a b c (fun _ => 1) 1 (t₀ + k * h) h Z₀ Zt zt →
      ∀ Φ : ℝ → Matrix m n ℝ, ODESolution F Φ (t₀ + k * h) (t₀ + (k + 1) * h) →
        Φ (t₀ + k * h) = Z₀ →
        (∀ j : Fin s, 0 < j.val → ‖Zt j - Φ (t₀ + k * h + c j * h)‖ ≤ K * h ^ (q j + 1)) ∧
        ‖zt - Φ (t₀ + (k + 1) * h)‖ ≤ K * h ^ (p + 1)) :
    HasLocalError F (t₀ + k * h) (t₀ + (k + 1) * h) Z₀ Z₁
      (h * (localErrorConst a b L κ * (ε + ε * Real.exp (L * h) + K * h ^ q'))) := by
  obtain ⟨ha₀, h01, hb₀, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hk
  have hloc := hstep.hasLocalError_of_tube ha hc hκ hε hε₀ hP.lipschitz hP.L_nonneg hP.bounded
    hP.B_nonneg hcont hP.sol.cont ha₀ hb₀ h01 (by rw [hsub]; exact hh1) (hP.sol.mono ha₀ hb₀)
    hZ₀ (by rw [hsub]; exact hnear) hK hq hqp hqb (by rw [hsub]; exact hRK)
  rwa [hsub] at hloc

/-- **Every run of the projected Runge–Kutta method satisfies the error bound**
([KieriVandereycken2019], Theorem 6, for every run). Let `A` solve `Y' = F(t, Y)` on
`[t₀, t₀ + N h]`, let `F` be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around
`A` (`DLRAProblem`), continuous there, with normal part at most `ε` at the factored rank-`r`
points of the tube. Let the tableau be explicit with nodes in `[0, 1]`, `κ ≥ 0`, `0 ≤ h ≤ 1`,
`N h ≤ T`, and let `Y` be a run with `Y 0` of rank at most `r` and `‖Y 0 - A t₀‖ ≤ δ`. Write
`R = e^{L T} δ + T e^{L T} · localErrorConst a b L κ · (ε + ε e^{L h} + K h^{q'})`. If the
classical Runge–Kutta step of `F` from every matrix of rank at most `r` within `R` of `A` has
stage errors `K h^{q_j + 1}` and local error `K h^{p + 1}` (`hRK`), `q'` is admissible and
`R + ((1 + κ) α + 3) B h < ρ`, then `‖Y n - A (t₀ + n h)‖ ≤ R` for all `n ≤ N`. -/
theorem IsRun.norm_sub_le {Y : ℕ → Matrix m n ℝ}
    (ha : ∀ i j, i ≤ j → a i j = 0) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ 1)
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hcont : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hκ : 0 ≤ κ) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hNT : N * h ≤ T) (hK : 0 ≤ K)
    {q : Fin s → ℕ} {q₂ p q' : ℕ} (hq : ∀ j : Fin s, 0 < j.val → q₂ ≤ q j) (hqp : q' ≤ p)
    (hqb : ∀ j : Fin s, 0 < j.val → b j ≠ 0 → q' ≤ min (q j) (q₂ + 1) + 1)
    (hRK : ∀ k < N, ∀ Z₀ : Matrix m n ℝ, Z₀.rank ≤ r →
      ‖Z₀ - A (t₀ + k * h)‖ ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) *
        (localErrorConst a b L κ * (ε + ε * Real.exp (L * h) + K * h ^ q')) →
      ∀ (Zt : Fin s → Matrix m n ℝ) (zt : Matrix m n ℝ),
      IsGalerkinRKStep F a b c (fun _ => 1) 1 (t₀ + k * h) h Z₀ Zt zt →
      ∀ Φ : ℝ → Matrix m n ℝ, ODESolution F Φ (t₀ + k * h) (t₀ + (k + 1) * h) →
        Φ (t₀ + k * h) = Z₀ →
        (∀ j : Fin s, 0 < j.val → ‖Zt j - Φ (t₀ + k * h + c j * h)‖ ≤ K * h ^ (q j + 1)) ∧
        ‖zt - Φ (t₀ + (k + 1) * h)‖ ≤ K * h ^ (p + 1))
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) *
      (localErrorConst a b L κ * (ε + ε * Real.exp (L * h) + K * h ^ q')) +
        ((1 + κ) * tabWeight a b + 3) * B * h < ρ)
    (hY : IsRun (stepRel F r κ a b c) (uniformGrid t₀ h) N Y) (hY₀ : (Y 0).rank ≤ r)
    (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ k ≤ N, ‖Y k - A (t₀ + k * h)‖ ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) *
      (localErrorConst a b L κ * (ε + ε * Real.exp (L * h) + K * h ^ q')) := by
  have hc₀ : 0 ≤ localErrorConst a b L κ * (ε + ε * Real.exp (L * h) + K * h ^ q') :=
    mul_nonneg (localErrorConst_nonneg a b hP.L_nonneg hκ) (by positivity)
  have hm : 2 * B * h ≤ ((1 + κ) * tabWeight a b + 3) * B * h := by
    have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + κ) (tabWeight_nonneg a b))
      (mul_nonneg hP.B_nonneg hh)
    nlinarith [mul_nonneg hP.B_nonneg hh]
  intro k hk
  refine (hY.adm_and_norm_sub_le_of_tube_uniformGrid (Adm := fun _ Z => Z.rank ≤ r)
    (T := T) (δ₀ := δ) hP hcont (fun j _ _ _ _ _ hstep => hstep.rank_le)
    (fun j hj Z₀ Z₁ hZ₀ hnear hstep => ?_) hc₀ hY₀ hδ hNT (by linarith) k hk).2
  exact hstep.hasLocalError_uniformGrid ha hc hκ hP hcont hε hε₀ hh hh1 hj hZ₀ (by linarith) hK
    hq hqp hqb (hRK j hj Z₀ hZ₀ hnear)

/-- **Existence and error bound for the projected Runge–Kutta method** ([KieriVandereycken2019],
Theorem 6, with explicit constants and tube hypotheses). Let `A` solve `Y' = F(t, Y)` on
`[t₀, t₀ + N h]`, let `F` be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around
`A` (`DLRAProblem`), continuous there, with normal part at most `ε` at the factored rank-`r`
points of the tube (`FactoredNormalBoundOn`). Let the tableau `(a, b, c)` be explicit with nodes
in `[0, 1]`, `κ ≥ 1`, `r ≤ m`, `r ≤ n`, `0 ≤ h ≤ 1`, `N h ≤ T`, and let `Y₀` have rank at most `r`
with `‖Y₀ - A t₀‖ ≤ δ`. Write

  `R = e^{L T} δ + T e^{L T} · localErrorConst a b L κ · (ε + ε e^{L h} + K h^{q'})`.

Suppose (`hRK`) that the classical Runge–Kutta step of `F` from every matrix of rank at most `r`
within `R` of `A` has stage errors `K h^{q_j + 1}` and local error `K h^{p + 1}` with respect to
the exact solution through it (the paper's (30) and (19)), that `q₂ ≤ q_j` for the later stages,
that `q'` is admissible, and that `R + ((1 + κ) α + 3) B h < ρ`, `α = tabWeight a b`. Then the
projected Runge–Kutta method with a `κ`-quasi-optimal retraction can be run from `Y₀`: there are
`Y 0 = Y₀, …, Y N` of rank at most `r` with `‖Y n - A (t₀ + n h)‖ ≤ R` for all `n ≤ N`.

This is the paper's `C (δ + ε + h^q)` with an explicit `C`, independent of the singular values
of the `Y n`: for `q'` take `min(p, q₂ + 1)` (`ProjectedRK.admissible_min_q₂`) or, if `b₂ = 0`,
`min(p, q₃ + 1, q₂ + 2)` (`ProjectedRK.admissible_of_b₂_eq_zero`). The paper's one-sided
constant `ℓ` is not used (the bound carries `e^{L T}`), the field is controlled only on the
tube, and neither the projected solution nor full rank of the `Y n` is assumed. The classical
order and stage orders are hypotheses, not consequences of the order conditions of the tableau:
in this the theorem is weaker than the run theorems of the other integrators. -/
theorem exists_run_norm_sub_le
    (ha : ∀ i j, i ≤ j → a i j = 0) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ 1)
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hcont : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hκ : 1 ≤ κ) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) (hK : 0 ≤ K)
    {q : Fin s → ℕ} {q₂ p q' : ℕ} (hq : ∀ j : Fin s, 0 < j.val → q₂ ≤ q j) (hqp : q' ≤ p)
    (hqb : ∀ j : Fin s, 0 < j.val → b j ≠ 0 → q' ≤ min (q j) (q₂ + 1) + 1)
    (hRK : ∀ k < N, ∀ Z₀ : Matrix m n ℝ, Z₀.rank ≤ r →
      ‖Z₀ - A (t₀ + k * h)‖ ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) *
        (localErrorConst a b L κ * (ε + ε * Real.exp (L * h) + K * h ^ q')) →
      ∀ (Zt : Fin s → Matrix m n ℝ) (zt : Matrix m n ℝ),
      IsGalerkinRKStep F a b c (fun _ => 1) 1 (t₀ + k * h) h Z₀ Zt zt →
      ∀ Φ : ℝ → Matrix m n ℝ, ODESolution F Φ (t₀ + k * h) (t₀ + (k + 1) * h) →
        Φ (t₀ + k * h) = Z₀ →
        (∀ j : Fin s, 0 < j.val → ‖Zt j - Φ (t₀ + k * h + c j * h)‖ ≤ K * h ^ (q j + 1)) ∧
        ‖zt - Φ (t₀ + (k + 1) * h)‖ ≤ K * h ^ (p + 1))
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) *
      (localErrorConst a b L κ * (ε + ε * Real.exp (L * h) + K * h ^ q')) +
        ((1 + κ) * tabWeight a b + 3) * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r κ a b c) (uniformGrid t₀ h) N Y ∧
      ∀ k ≤ N, (Y k).rank ≤ r ∧ ‖Y k - A (t₀ + k * h)‖ ≤ Real.exp (L * T) * δ +
        T * Real.exp (L * T) *
          (localErrorConst a b L κ * (ε + ε * Real.exp (L * h) + K * h ^ q')) := by
  have hκ₀ : 0 ≤ κ := zero_le_one.trans hκ
  have hα : 0 ≤ (1 + κ) * tabWeight a b :=
    mul_nonneg (by linarith) (tabWeight_nonneg a b)
  have hc₀ : 0 ≤ localErrorConst a b L κ * (ε + ε * Real.exp (L * h) + K * h ^ q') :=
    mul_nonneg (localErrorConst_nonneg a b hP.L_nonneg hκ₀) (by positivity)
  have hmono : (1 + κ) * tabWeight a b + 1 ≤ (1 + κ) * tabWeight a b + 3 := by linarith
  refine ((isTubeLocal_stepRel ha hc hκ hrm hrn).mono hmono).exists_run_norm_sub_le
    (by linarith) hP hcont (fun k hk Z₀ Z₁ hZ₀ hnear hstep => ?_) hc₀ hh hNT hY₀ hδ hsmall
  exact hstep.hasLocalError_uniformGrid ha hc hκ₀ hP hcont hε hε₀ hh hh1 hk hZ₀ (by linarith) hK
    hq hqp hqb (hRK k hk Z₀ hZ₀ hnear)

end Run

/-! ### Non-vacuity: the projected Heun method -/

section Examples

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}

/-- **Non-vacuity of `MatrixPRK.exists_run_norm_sub_le`**, for the projected Heun method (PRK2
of [KieriVandereycken2019], eq. (29): `a₂₁ = 1`, `b = (1/2, 1/2)`, `c = (0, 1)`; order `p = 2`,
stage order `q₂ = 1`, exponent `q' = 2`) and the constant field `F(t, Y) = G` with the solution
`A(t) = C + (t - t₀) G`. The field is `0`-Lipschitz, bounded by `‖G‖`, and its normal part is
at most `‖G‖`; the classical Heun step is exact for it, so `hRK` holds with `K = 0`. The projected
method is not exact (it loses the normal part of `G`), and the theorem bounds its error by the
initial error plus `T · localErrorConst · 2 ‖G‖`, for every `κ ≥ 1` and every step size
`0 ≤ h ≤ 1`. -/
example (G C : Matrix m n ℝ) {κ : ℝ} (hκ : 1 ≤ κ) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) {t₀ h T δ : ℝ} {N : ℕ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hNT : N * h ≤ T) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - C‖ ≤ δ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (stepRel (fun _ _ => G) r κ ![![0, 0], ![1, 0]] ![1 / 2, 1 / 2] ![0, 1])
        (uniformGrid t₀ h) N Y ∧
      ∀ k ≤ N, (Y k).rank ≤ r ∧ ‖Y k - (C + (t₀ + k * h - t₀) • G)‖ ≤ Real.exp (0 * T) * δ +
        T * Real.exp (0 * T) * (localErrorConst ![![0, 0], ![1, 0]] ![1 / 2, 1 / 2] 0 κ *
          (‖G‖ + ‖G‖ * Real.exp (0 * h) + 0 * h ^ 2)) := by
  -- the affine solutions of the constant field, and their uniqueness
  have aff : ∀ (y₀ : Matrix m n ℝ) (s₀ s₁ : ℝ),
      ODESolution (fun _ _ => G) (fun t => y₀ + (t - s₀) • G) s₀ s₁ := fun y₀ s₀ s₁ =>
    ⟨by fun_prop, fun t _ => by
      have hd : HasDerivAt (fun t : ℝ => y₀ + (t - s₀) • G) G t := by
        simpa using (((hasDerivAt_id t).sub_const s₀).smul_const G).const_add y₀
      exact hd.hasDerivWithinAt⟩
  have hLip : IsLipschitzField (fun (_ : ℝ) (_ : Matrix m n ℝ) => G) 0 := fun _ _ _ => by simp
  set R := Real.exp (0 * T) * δ + T * Real.exp (0 * T) *
    (localErrorConst ![![0, 0], ![1, 0]] ![1 / 2, 1 / 2] 0 κ *
      (‖G‖ + ‖G‖ * Real.exp (0 * h) + 0 * h ^ 2)) with hR
  set ρ := R + ((1 + κ) * tabWeight ![![(0 : ℝ), 0], ![1, 0]] ![1 / 2, 1 / 2] + 3) * ‖G‖ * h + 1
    with hρ
  have hP : DLRAProblem (fun _ _ => G) (fun t => C + (t - t₀) • G) t₀ (t₀ + N * h) ρ 0 ‖G‖ :=
    ⟨aff C t₀ _, le_rfl, norm_nonneg G, fun _ _ x y _ _ => by simp, fun _ _ _ _ => le_rfl⟩
  have hε : FactoredNormalBoundOn (fun (_ : ℝ) (_ : Matrix m n ℝ) => G) r
      (tubeSet (fun t => C + (t - t₀) • G) t₀ (t₀ + N * h) ρ) ‖G‖ := fun t U V S hU hV hmem => by
    simpa using factoredNormalBoundOn_linear (r := r) (0 : Matrix m m ℝ) (0 : Matrix n n ℝ) G
      (tubeSet (fun t => C + (t - t₀) • G) t₀ (t₀ + N * h) ρ) t U V S hU hV hmem
  have hRK : ∀ k < N, ∀ Z₀ : Matrix m n ℝ, Z₀.rank ≤ r → ‖Z₀ - (C + (t₀ + k * h - t₀) • G)‖ ≤ R →
      ∀ (Zt : Fin 2 → Matrix m n ℝ) (zt : Matrix m n ℝ),
      IsGalerkinRKStep (fun _ _ => G) ![![0, 0], ![1, 0]] ![1 / 2, 1 / 2] ![0, 1] (fun _ => 1) 1
        (t₀ + k * h) h Z₀ Zt zt →
      ∀ Φ : ℝ → Matrix m n ℝ, ODESolution (fun _ _ => G) Φ (t₀ + k * h) (t₀ + (k + 1) * h) →
        Φ (t₀ + k * h) = Z₀ →
        (∀ j : Fin 2, 0 < j.val →
          ‖Zt j - Φ (t₀ + k * h + (![0, 1] : Fin 2 → ℝ) j * h)‖ ≤ 0 * h ^ ((fun _ => 1) j + 1)) ∧
        ‖zt - Φ (t₀ + (k + 1) * h)‖ ≤ 0 * h ^ (2 + 1) := by
    intro k _ Z₀ _ _ Zt zt hs Φ hΦ hΦ₀
    have huniq : ∀ t ∈ Icc (t₀ + k * h) (t₀ + (k + 1) * h),
        Φ t = Z₀ + (t - (t₀ + k * h)) • G := fun t ht =>
      hΦ.eqOn (aff Z₀ _ _) hLip le_rfl (by simp [hΦ₀]) ht
    have hZt1 : Zt 1 = Z₀ + h • G := by
      rw [hs.1 1]
      simp [Fin.sum_univ_two]
    have hzt : zt = Z₀ + h • G := by
      rw [hs.2]
      simp only [one_apply_eq_self, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      rw [← add_smul]
      norm_num
    have hk1 : t₀ + k * h ≤ t₀ + (k + 1) * h := by nlinarith
    constructor
    · intro j hj
      fin_cases j
      · simp at hj
      · have hc1 : (![0, 1] : Fin 2 → ℝ) 1 = 1 := by simp
        have hmem : t₀ + k * h + (![0, 1] : Fin 2 → ℝ) 1 * h ∈
            Icc (t₀ + k * h) (t₀ + (k + 1) * h) := by
          rw [hc1, one_mul]
          constructor <;> linarith
        simp only [Fin.mk_one] at hmem ⊢
        rw [hZt1, huniq _ hmem]
        simp
    · rw [hzt, huniq _ ⟨hk1, le_rfl⟩]
      have e : t₀ + (k + 1) * h - (t₀ + k * h) = h := by ring
      rw [e]
      simp
  obtain ⟨Y, hY0, hrun, hbd⟩ := exists_run_norm_sub_le (F := fun _ _ => G)
    (A := fun t => C + (t - t₀) • G) (a := ![![0, 0], ![1, 0]]) (b := ![1 / 2, 1 / 2])
    (c := ![0, 1]) (κ := κ) (K := 0) (q := fun _ => 1) (q₂ := 1) (p := 2) (q' := 2)
    (fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all)
    (fun j => by fin_cases j <;> norm_num) hP
    (continuous_const : Continuous fun _ : ℝ × Matrix m n ℝ => G).continuousOn hε
    (norm_nonneg G) hκ hh hh1 hNT hrm hrn le_rfl (fun _ _ => le_rfl) le_rfl
    (fun j hj _ => by fin_cases j <;> simp_all) hRK hY₀ (by simpa using hδ) (lt_add_one _)
  exact ⟨Y, hY0, hrun, hbd⟩

/-- **Non-vacuity of `MatrixPRK.exists_run_norm_sub_le` with `K > 0` and `L = 1`**, for the
projected Heun method and the time-dependent field `F(t, Y) = 2t G` with the solution
`A(t) = C + t² G` from `t₀ = 0`. The field does not depend on the state, so every `L ≥ 0` is a
Lipschitz constant; the example takes `L = 1`. On `[0, T]` the field and its normal part are
bounded by `2 T ‖G‖`. From every start `Z₀` the classical Heun step is exact (the trapezoidal
rule integrates `2t` exactly), but its second stage `Z₀ + 2 t_k h G` misses the exact solution
by `h² G`: `hRK` holds with `K = ‖G‖`, stage order `q₂ = 1` and `q' = 2`. -/
example (G C : Matrix m n ℝ) {κ : ℝ} (hκ : 1 ≤ κ) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) {h T δ : ℝ} {N : ℕ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hNT : N * h ≤ T) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - C‖ ≤ δ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (stepRel (fun t _ => (2 * t) • G) r κ ![![0, 0], ![1, 0]] ![1 / 2, 1 / 2] ![0, 1])
        (uniformGrid 0 h) N Y ∧
      ∀ k ≤ N, (Y k).rank ≤ r ∧ ‖Y k - (C + (0 + k * h) ^ 2 • G)‖ ≤ Real.exp (1 * T) * δ +
        T * Real.exp (1 * T) * (localErrorConst ![![0, 0], ![1, 0]] ![1 / 2, 1 / 2] 1 κ *
          (2 * T * ‖G‖ + 2 * T * ‖G‖ * Real.exp (1 * h) + ‖G‖ * h ^ 2)) := by
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg N) hh).trans hNT
  -- the solutions of the field `2t G`, and their uniqueness
  have aff : ∀ (y₀ : Matrix m n ℝ) (s₀ s₁ : ℝ),
      ODESolution (fun t (_ : Matrix m n ℝ) => (2 * t) • G) (fun t => y₀ + (t ^ 2 - s₀ ^ 2) • G)
        s₀ s₁ := fun y₀ s₀ s₁ =>
    ⟨by fun_prop, fun t _ => by
      have hd : HasDerivAt (fun t : ℝ => y₀ + (t ^ 2 - s₀ ^ 2) • G) ((2 * t) • G) t := by
        simpa using (((hasDerivAt_pow 2 t).sub_const (s₀ ^ 2)).smul_const G).const_add y₀
      exact hd.hasDerivWithinAt⟩
  have hAsol : ODESolution (fun t (_ : Matrix m n ℝ) => (2 * t) • G) (fun t => C + t ^ 2 • G) 0
      (0 + N * h) :=
    ⟨by fun_prop, fun t _ => by
      have hd : HasDerivAt (fun t : ℝ => C + t ^ 2 • G) ((2 * t) • G) t := by
        simpa using ((hasDerivAt_pow 2 t).smul_const G).const_add C
      exact hd.hasDerivWithinAt⟩
  have hLip0 : IsLipschitzField (fun (t : ℝ) (_ : Matrix m n ℝ) => (2 * t) • G) 0 :=
    fun _ _ _ => by simp
  set R := Real.exp (1 * T) * δ + T * Real.exp (1 * T) *
    (localErrorConst ![![0, 0], ![1, 0]] ![1 / 2, 1 / 2] 1 κ *
      (2 * T * ‖G‖ + 2 * T * ‖G‖ * Real.exp (1 * h) + ‖G‖ * h ^ 2)) with hR
  set ρ := R + ((1 + κ) * tabWeight ![![(0 : ℝ), 0], ![1, 0]] ![1 / 2, 1 / 2] + 3) *
    (2 * T * ‖G‖) * h + 1 with hρ
  have hP : DLRAProblem (fun t (_ : Matrix m n ℝ) => (2 * t) • G) (fun t => C + t ^ 2 • G) 0
      (0 + N * h) ρ 1 (2 * T * ‖G‖) :=
    ⟨hAsol, zero_le_one, by positivity, fun _ _ x y _ _ => by simp, fun t ht x _ => by
      rw [norm_smul, Real.norm_of_nonneg (by linarith [ht.1])]
      have : t ≤ T := by linarith [ht.2]
      nlinarith [norm_nonneg G]⟩
  have hε : FactoredNormalBoundOn (fun t (_ : Matrix m n ℝ) => (2 * t) • G) r
      (tubeSet (fun t => C + t ^ 2 • G) 0 (0 + N * h) ρ) (2 * T * ‖G‖) :=
    fun t U V S hU hV hmem => by
      have h1 := factoredNormalBoundOn_linear (r := r) (0 : Matrix m m ℝ) (0 : Matrix n n ℝ)
        ((2 * t) • G) (tubeSet (fun t => C + t ^ 2 • G) 0 (0 + N * h) ρ) t U V S hU hV hmem
      simp only [Matrix.zero_mul, Matrix.transpose_zero, Matrix.mul_zero, zero_add] at h1
      refine h1.trans ?_
      rw [norm_smul, Real.norm_of_nonneg (by linarith [hmem.1.1])]
      have : t ≤ T := by linarith [hmem.1.2]
      nlinarith [norm_nonneg G]
  have hRK : ∀ k < N, ∀ Z₀ : Matrix m n ℝ, Z₀.rank ≤ r → ‖Z₀ - (C + (0 + k * h) ^ 2 • G)‖ ≤ R →
      ∀ (Zt : Fin 2 → Matrix m n ℝ) (zt : Matrix m n ℝ),
      IsGalerkinRKStep (fun t (_ : Matrix m n ℝ) => (2 * t) • G) ![![0, 0], ![1, 0]]
        ![1 / 2, 1 / 2] ![0, 1] (fun _ => 1) 1 (0 + k * h) h Z₀ Zt zt →
      ∀ Φ : ℝ → Matrix m n ℝ, ODESolution (fun t (_ : Matrix m n ℝ) => (2 * t) • G) Φ
        (0 + k * h) (0 + (k + 1) * h) → Φ (0 + k * h) = Z₀ →
        (∀ j : Fin 2, 0 < j.val →
          ‖Zt j - Φ (0 + k * h + (![0, 1] : Fin 2 → ℝ) j * h)‖ ≤
            ‖G‖ * h ^ ((fun _ => 1) j + 1)) ∧
        ‖zt - Φ (0 + (k + 1) * h)‖ ≤ ‖G‖ * h ^ (2 + 1) := by
    intro k _ Z₀ _ _ Zt zt hs Φ hΦ hΦ₀
    have huniq : ∀ t ∈ Icc (0 + k * h) (0 + (k + 1) * h),
        Φ t = Z₀ + (t ^ 2 - (0 + k * h) ^ 2) • G := fun t ht =>
      hΦ.eqOn (aff Z₀ _ _) hLip0 le_rfl (by rw [hΦ₀]; simp) ht
    have hZt1 : Zt 1 = Z₀ + (2 * (0 + k * h) * h) • G := by
      rw [hs.1 1]
      simp only [Fin.sum_univ_two, one_apply_eq_self, Matrix.cons_val_zero, Matrix.cons_val_one]
      module
    have hzt : zt = Z₀ + (2 * (0 + k * h) * h + h ^ 2) • G := by
      rw [hs.2]
      simp only [Fin.sum_univ_two, one_apply_eq_self, Matrix.cons_val_zero, Matrix.cons_val_one]
      module
    have hk1 : (0 : ℝ) + k * h ≤ 0 + (k + 1) * h := by nlinarith
    constructor
    · intro j hj
      fin_cases j
      · simp at hj
      · have hmem : 0 + k * h + (![0, 1] : Fin 2 → ℝ) 1 * h ∈
            Icc ((0 : ℝ) + k * h) (0 + (k + 1) * h) := by
          simp only [Matrix.cons_val_one, Matrix.cons_val_zero, one_mul]
          constructor <;> linarith
        simp only [Fin.mk_one] at hmem ⊢
        rw [hZt1, huniq _ hmem]
        calc _ = ‖(-(h ^ 2)) • G‖ := by
              congr 1
              simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
              module
          _ = ‖G‖ * h ^ (1 + 1) := by
              rw [norm_smul, norm_neg, Real.norm_of_nonneg (sq_nonneg h)]
              ring
          _ ≤ _ := le_rfl
    · rw [hzt, huniq _ ⟨hk1, le_rfl⟩]
      calc _ = ‖(0 : ℝ) • G‖ := by
            congr 1
            module
        _ ≤ _ := by
            rw [zero_smul, norm_zero]
            positivity
  obtain ⟨Y, hY0, hrun, hbd⟩ := exists_run_norm_sub_le (F := fun t _ => (2 * t) • G)
    (A := fun t => C + t ^ 2 • G) (a := ![![0, 0], ![1, 0]]) (b := ![1 / 2, 1 / 2])
    (c := ![0, 1]) (κ := κ) (K := ‖G‖) (q := fun _ => 1) (q₂ := 1) (p := 2) (q' := 2)
    (fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all)
    (fun j => by fin_cases j <;> norm_num) hP
    (Continuous.smul (continuous_const.mul continuous_fst) continuous_const :
      Continuous fun p : ℝ × Matrix m n ℝ => (2 * p.1) • G).continuousOn hε
    (by positivity) hκ hh hh1 hNT hrm hrn (norm_nonneg G) (fun _ _ => le_rfl) le_rfl
    (fun j hj _ => by fin_cases j <;> simp_all) hRK hY₀ (by simpa using hδ) (lt_add_one _)
  exact ⟨Y, hY0, hrun, hbd⟩

end Examples

end MatrixPRK

end LeanDLRA
