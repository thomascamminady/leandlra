import LeanDLRA.Integrators.Matrix.EulerBUGStep
import LeanDLRA.Integrators.Matrix.LinearFieldExample

/-!
# The projected Euler method for matrices

The projected Euler method of Kieri and Vandereycken advances a matrix `Y₀` of rank at most `r`
over a time step `[t₀, t₁]` by one explicit Euler step of the projected differential equation
`Y' = P(Y) F(t, Y)` and a retraction to the matrices of rank at most `r`:

  `Y₁ = ℛ(Y₀ + (t₁ - t₀) P(Y₀) F(t₀, Y₀))`

([KieriVandereycken2019], eq. (21)). Here `P(Y₀) Z = U Uᵀ Z + Z V Vᵀ - U Uᵀ Z V Vᵀ` is the
orthogonal projector onto the tangent space at `Y₀ = U S Vᵀ` (`tangentProj U V`), and the
retraction is quasi-optimal: `ℛ(X)` has rank at most `r` and `‖ℛ(X) - X‖ ≤ κ dist(X, M_{≤ r})`
(their eq. (13) with `C_ℛ = κ`; the truncated singular value decomposition has `κ = 1`). The
argument `Y₀ + (t₁ - t₀) P(Y₀) F(t₀, Y₀)` of the retraction has rank at most `2 r`.

This file states the method as a step relation (`MatrixProjEuler.stepRel`), shows that it is a
tube-local method (`StepMethod.IsTubeLocal`), proves its local error ([KieriVandereycken2019],
Lemma 3) and obtains the existence of runs and the global error bound ([KieriVandereycken2019],
Theorem 4) from `StepMethod.IsTubeLocal.exists_run_norm_sub_le`.

**Assumptions.** The paper assumes a globally Lipschitz field, a one-sided Lipschitz constant
`ℓ`, smoothness of the exact flow, the normal bound `‖F(Y) - P(Y) F(Y)‖ ≤ ε` on the manifold of
rank-`r` matrices near the exact solution, and full rank `r` of the projected solution and of
the numerical values. Here the field is only Lipschitz and bounded on a tube around the exact
solution (`DLRAProblem`) and Lipschitz in time there (constant `Lₜ`), and the normal bound is
asked at every factorization `U S Vᵀ` in the tube (`FactoredNormalBoundOn`, `S` may be
singular). The one-sided constant `ℓ` is not used: the bounds carry `e^{L T}` with the full
Lipschitz constant `L`. No projected (DLRA) solution and no rank condition on the numerical
values is assumed: the distance of the exact flow to the matrices of rank at most `r`, which the
paper bounds with the projected solution (proof of Theorem 2, eq. (15)), is bounded by
`distLR_flow_le_of_tube`, and at a matrix of rank below `r` the step uses the tangent projector
of any factorization with `r` orthonormal columns.

## Main definitions

* `MatrixProjEuler.tangentRel F r`: the step before the retraction, `X = Y₀ + (t₁ - t₀) P F₀`.
* `MatrixProjEuler.stepRel F r κ`: the projected Euler step with a `κ`-quasi-optimal retraction.

## Main results

* `sub_tangentProj_apply`: `Z - P Z = (I - U Uᵀ) Z (I - V Vᵀ)`.
* `MatrixProjEuler.tangentRel.hasLocalError_of_tube`: the step before the retraction has local
  error `(t₁ - t₀) ((L B + Lₜ) / 2 (t₁ - t₀) + ε)`.
* `MatrixProjEuler.stepRel.hasLocalError_of_tube` ([KieriVandereycken2019], Lemma 3): the
  projected Euler step has local error
  `(t₁ - t₀) ((10 κ L B + (1 + κ) (L B + Lₜ) / 2) (t₁ - t₀) + (1 + 2 κ) ε)`.
* `MatrixProjEuler.isTubeLocal_stepRel`: the method is tube-local with margin constant `0`.
* `MatrixProjEuler.IsRun.norm_sub_le`, `MatrixProjEuler.exists_run_norm_sub_le`
  ([KieriVandereycken2019], Theorem 4): runs exist, keep rank at most `r`, and satisfy
  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} c` with
  `c = (10 κ L B + (1 + κ) (L B + Lₜ) / 2) h + (1 + 2 κ) ε`.

## Implementation notes

For `κ = 1` the constant is `(11 L B + Lₜ) h + 3 ε`, the constant of the fixed-rank explicit
Euler BUG integrator (`MatrixEulerBUG.exists_run_norm_sub_le`). The two methods differ: the
explicit Euler BUG step projects `Y₀ + (t₁ - t₀) F₀` onto augmented bases from both sides, the
projected Euler step adds the tangent part of `F₀` only; before the retraction both are within
`(t₁ - t₀) ε` of the explicit Euler step `Y₀ + (t₁ - t₀) F₀`, which is all the analysis uses.

## References

* [KieriVandereycken2019] E. Kieri, B. Vandereycken, *Projection methods for dynamical low-rank
  approximation of high-dimensional problems*, Comput. Methods Appl. Math. 19 (2019), §4.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

section NormalPart

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k'] [DecidableEq m]
  [DecidableEq n]

/-- **The tangent projector removes the doubly normal part.** For all `U`, `V` (orthonormality
is not needed), `Z - P Z = (I - U Uᵀ) Z (I - V Vᵀ)` with `P = tangentProj U V`. -/
theorem sub_tangentProj_apply (U : Matrix m k ℝ) (V : Matrix n k' ℝ) (Z : Matrix m n ℝ) :
    Z - tangentProj U V Z = (1 - U * Uᵀ) * Z * (1 - V * Vᵀ) := by
  rw [tangentProj_apply]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

end NormalPart

namespace MatrixProjEuler

/-! ### The step relations -/

section Rel

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}

/-- **The projected Euler step before the retraction.** `tangentRel F r t₀ t₁ Y₀ X` holds if
`Y₀ = U S Vᵀ` for some `U : m × r`, `V : n × r` with orthonormal columns and `S : r × r`, and
`X = Y₀ + (t₁ - t₀) P F(t₀, Y₀)` with the tangent projector `P = tangentProj U V` at `Y₀`
(the argument of the retraction in [KieriVandereycken2019], eq. (21)). For `Y₀` of rank `r` the
projector does not depend on the factorization; for smaller rank every factorization is
allowed. -/
def tangentRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ X => ∃ (U : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ)
    (V : Matrix n (Fin r) ℝ), Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ Y₀ = U * S * Vᵀ ∧
      X = Y₀ + (t₁ - t₀) • tangentProj U V (F t₀ Y₀)

/-- **The projected Euler step** ([KieriVandereycken2019], eq. (21)) with a `κ`-quasi-optimal
retraction (their eq. (13), `C_ℛ = κ`): `stepRel F r κ t₀ t₁ Y₀ Y₁` holds if `Y₁` has rank at
most `r` and `‖Y₁ - X‖ ≤ κ dist(X, M_{≤ r})` for a result `X` of `tangentRel F r` from `Y₀`.
For `κ = 1` these are the best approximations of rank at most `r`, among them the truncated
singular value decomposition (`MatrixProjEuler.tangentRel.stepRel_truncation`). -/
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) (κ : ℝ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ => ∃ X : Matrix m n ℝ, tangentRel F r t₀ t₁ Y₀ X ∧ Y₁.rank ≤ r ∧
    ‖Y₁ - X‖ ≤ κ * distLR r X

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {κ t₀ t₁ : ℝ} {Y₀ Y₁ X : Matrix m n ℝ}

/-- A projected Euler step can only be started from a matrix of rank at most `r`. -/
theorem tangentRel.rank_start_le (h : tangentRel F r t₀ t₁ Y₀ X) : Y₀.rank ≤ r := by
  obtain ⟨U, S, V, -, -, rfl, -⟩ := h
  exact rank_mul_mul_transpose_le _ _ _

/-- The result of a projected Euler step has rank at most `r`. -/
theorem stepRel.rank_le (h : stepRel F r κ t₀ t₁ Y₀ Y₁) : Y₁.rank ≤ r := by
  obtain ⟨X, -, hr, -⟩ := h
  exact hr

/-- A projected Euler step can only be started from a matrix of rank at most `r`. -/
theorem stepRel.rank_start_le (h : stepRel F r κ t₀ t₁ Y₀ Y₁) : Y₀.rank ≤ r := by
  obtain ⟨X, hX, -, -⟩ := h
  exact hX.rank_start_le

/-- All values of a run of the projected Euler method have rank at most `r`, provided the start
value has. -/
theorem IsRun.rank_le {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → Matrix m n ℝ}
    (hY : IsRun (stepRel F r κ) τ N Y) (h0 : (Y 0).rank ≤ r) : ∀ n ≤ N, (Y n).rank ≤ r
  | 0, _ => h0
  | n + 1, hn => (hY.step n hn).rank_le

/-- **The step before the retraction exists** from every matrix of rank at most `r`, for every
field, if `r ≤ m` and `r ≤ n`. -/
theorem exists_tangentRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) (hY₀ : Y₀.rank ≤ r) :
    ∃ X, tangentRel F r t₀ t₁ Y₀ X := by
  obtain ⟨U, S, V, hU, hV, rfl⟩ := exists_factor_of_rank_le hY₀ hrm hrn
  exact ⟨_, U, S, V, hU, hV, rfl, rfl⟩

/-- **The retraction exists**: for `κ ≥ 1` a best approximation of rank at most `r`
(`exists_best_approx`) completes every step before the retraction to a projected Euler step. -/
theorem tangentRel.exists_stepRel (h : tangentRel F r t₀ t₁ Y₀ X) (hκ : 1 ≤ κ) :
    ∃ Y₁, stepRel F r κ t₀ t₁ Y₀ Y₁ := by
  obtain ⟨Z, hZ, hd⟩ := exists_best_approx r X
  refine ⟨Z, X, h, hZ, ?_⟩
  rw [norm_sub_rev, hd]
  exact le_mul_of_one_le_left distLR_nonneg hκ

/-- **The truncated singular value decomposition is a retraction of the step**: by the
Eckart–Young theorem (`EckartYoung.norm_sub_truncation_le`) it is a best approximation of rank
at most `r`, hence `κ`-quasi-optimal for every `κ ≥ 1`. -/
theorem tangentRel.stepRel_truncation [DecidableEq n] (h : tangentRel F r t₀ t₁ Y₀ X)
    (hκ : 1 ≤ κ) : stepRel F r κ t₀ t₁ Y₀ (EckartYoung.truncation X r) := by
  refine ⟨X, h, EckartYoung.rank_truncation_le X r, ?_⟩
  have h₁ : ‖EckartYoung.truncation X r - X‖ ≤ distLR r X := by
    rw [norm_sub_rev]
    exact le_distLR_iff.2 fun Z hZ => EckartYoung.norm_sub_truncation_le X hZ
  exact h₁.trans (le_mul_of_one_le_left distLR_nonneg hκ)

/-- **A projected Euler step exists from every start value of rank at most `r`**, for every
field and every `κ ≥ 1`, if `r ≤ m` and `r ≤ n`. -/
theorem exists_stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ) (hκ : 1 ≤ κ)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) (hY₀ : Y₀.rank ≤ r) :
    ∃ Y₁, stepRel F r κ t₀ t₁ Y₀ Y₁ := by
  obtain ⟨X, hX⟩ := exists_tangentRel F t₀ t₁ hrm hrn hY₀
  exact hX.exists_stepRel hκ

/-! ### Near the reference solution -/

section Tube

variable {A : ℝ → Matrix m n ℝ} {a b ρ : ℝ}

/-- **The step evaluates the field only at the start.** If `Y₀` lies in the tube of radius `ρ`
around `A` at time `t₀ ∈ [a, b]`, the relation `tangentRel` is the same for the tube extension
`tubeExt F A a b ρ` and for `F`. -/
theorem tangentRel_tubeExt_iff (ht₀ : t₀ ∈ Icc a b) (hx : ‖Y₀ - A t₀‖ ≤ ρ) :
    tangentRel (tubeExt F A a b ρ) r t₀ t₁ Y₀ X ↔ tangentRel F r t₀ t₁ Y₀ X := by
  simp only [tangentRel, tubeExt_eq ht₀ hx]

/-- If `Y₀` lies in the tube of radius `ρ` around `A` at time `t₀ ∈ [a, b]`, the relation
`stepRel` is the same for the tube extension `tubeExt F A a b ρ` and for `F`. -/
theorem stepRel_tubeExt_iff (ht₀ : t₀ ∈ Icc a b) (hx : ‖Y₀ - A t₀‖ ≤ ρ) :
    stepRel (tubeExt F A a b ρ) r κ t₀ t₁ Y₀ Y₁ ↔ stepRel F r κ t₀ t₁ Y₀ Y₁ :=
  ⟨fun ⟨X, h, hr⟩ => ⟨X, (tangentRel_tubeExt_iff ht₀ hx).1 h, hr⟩,
    fun ⟨X, h, hr⟩ => ⟨X, (tangentRel_tubeExt_iff ht₀ hx).2 h, hr⟩⟩

end Tube

/-! ### Local error -/

section Error

variable [DecidableEq m] [DecidableEq n] {L B ε Lt : ℝ} {A : ℝ → Matrix m n ℝ} {a b ρ : ℝ}

/-- **Local error of the projected Euler step before the retraction, near a reference
solution.** Let `F` be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around a
solution `A` over `[a, b]`, let the normal part of `F` be at most `ε` at the factored rank-`r`
points of this tube, and let `‖F t Y₀ - F t₀ Y₀‖ ≤ Lₜ (t - t₀)` during the step. If
`‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ` for a step over `[t₀, t₁] ⊆ [a, b]`, then every result `X` of
`MatrixProjEuler.tangentRel` from `Y₀` has local error `(t₁ - t₀) ((L B + Lₜ) / 2 (t₁ - t₀) + ε)`:
`X` differs from the explicit Euler step `Y₀ + (t₁ - t₀) F₀` by `(t₁ - t₀)` times the normal part
of `F₀` (`sub_tangentProj_apply`), and the explicit Euler step has local error
`(L B + Lₜ) (t₁ - t₀)² / 2` (`norm_sub_exact_le_of_sub_euler`). -/
theorem tangentRel.hasLocalError_of_tube (h : tangentRel F r t₀ t₁ Y₀ X)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀))
    (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ X ((t₁ - t₀) * ((L * B + Lt) / 2 * (t₁ - t₀) + ε)) := by
  obtain ⟨U, S, V, hU, hV, hY, rfl⟩ := h
  have h0 : 0 ≤ t₁ - t₀ := sub_nonneg.2 h01
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB h0
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (Y₀ - A t₀)]
  have hnear : ∀ t ∈ Icc t₀ t₁, ‖Y₀ - A t‖ ≤ ρ :=
    hFB.norm_sub_le_of_near hB ha hb hA (by linarith)
  have heq : ∀ t ∈ Icc t₀ t₁, tubeExt F A a b ρ t Y₀ = F t Y₀ := fun t ht =>
    tubeExt_eq ⟨ha.trans ht.1, ht.2.trans hb⟩ (hnear t ht)
  have ht₀ : t₀ ∈ Icc t₀ t₁ := left_mem_Icc.2 h01
  -- the normal part of the field at the start value
  have hN : ‖(1 - U * Uᵀ) * F t₀ Y₀ * (1 - V * Vᵀ)‖ ≤ ε := by
    have hmem : (t₀, U * S * Vᵀ) ∈ tubeSet A a b ρ :=
      ⟨⟨ha, h01.trans hb⟩, by rw [← hY]; exact hnear t₀ ht₀⟩
    have h₁ := hε t₀ U V S hU hV hmem
    rwa [← hY] at h₁
  -- distance to the explicit Euler step of the extended field
  have hη : ‖Y₀ + (t₁ - t₀) • tangentProj U V (F t₀ Y₀) -
      (Y₀ + (t₁ - t₀) • tubeExt F A a b ρ t₀ Y₀)‖ ≤ (t₁ - t₀) * ε := by
    rw [heq t₀ ht₀, add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg h0,
      norm_sub_rev, sub_tangentProj_apply]
    exact mul_le_mul_of_nonneg_left hN h0
  have hFt' : ∀ t ∈ Ico t₀ t₁,
      ‖tubeExt F A a b ρ t Y₀ - tubeExt F A a b ρ t₀ Y₀‖ ≤ Lt * (t - t₀) := fun t ht => by
    rw [heq t (Ico_subset_Icc_self ht), heq t₀ ht₀]
    exact hFt t ht
  refine HasLocalError.of_tubeExt (fun Φ hΦ hΦ₀ => ?_) hFB hB ha hb h01 hA hsmall
  have h₁ := norm_sub_exact_le_of_sub_euler (isLipschitzField_tubeExt hFL hL hρ) hL
    (isBoundedField_tubeExt hFB hB hρ) (by ring : t₁ = t₀ + (t₁ - t₀)) h0 hΦ hΦ₀ hFt' hη
  calc _ ≤ _ := h₁
    _ = _ := by ring

/-- **Local error of the projected Euler step near a reference solution** ([KieriVandereycken2019],
Lemma 3, with explicit constants and tube hypotheses). Let `F` be continuous,
`L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`,
let the normal part of `F` be at most `ε` at the factored rank-`r` points of this tube, and let
`‖F t Y₀ - F t₀ Y₀‖ ≤ Lₜ (t - t₀)` during the step. If `‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ` for a
step over `[t₀, t₁] ⊆ [a, b]` and `κ ≥ 0`, then the projected Euler step from `Y₀` has local
error

  `(t₁ - t₀) ((10 κ L B + (1 + κ) (L B + Lₜ) / 2) (t₁ - t₀) + (1 + 2 κ) ε)`.

The proof is the paper's: the retraction costs `κ` times the distance of the exact solution
`Φ t₁` to the matrices of rank at most `r` plus `1 + κ` times the error before the retraction
(their eq. (23), `norm_trunc_sub_le`). The distance is bounded by
`(t₁ - t₀) (10 L B (t₁ - t₀) + ε)` (`distLR_flow_le_of_tube`) instead of with the projected
solution, so no rank condition is needed. No singular value of `Y₀` enters. -/
theorem stepRel.hasLocalError_of_tube (h : stepRel F r κ t₀ t₁ Y₀ Y₁) (hκ : 0 ≤ κ)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε) (hε₀ : 0 ≤ ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (hc : ContinuousOn (Function.uncurry F) (tubeSet A a b ρ))
    (hAc : ContinuousOn A (Icc a b)) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀))
    (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Y₁ ((t₁ - t₀) *
      ((10 * κ * L * B + (1 + κ) * (L * B + Lt) / 2) * (t₁ - t₀) + (1 + 2 * κ) * ε)) := by
  obtain ⟨X, hX, -, htr⟩ := h
  intro Φ hΦ hΦ₀
  have h₁ := hX.hasLocalError_of_tube hε hFL hL hFB hB ha hb h01 hA hFt hsmall Φ hΦ hΦ₀
  have h₂ := distLR_flow_le_of_tube hε hε₀ hFL hL hFB hB hc hAc ha hb h01 hA hΦ
    (by rw [hΦ₀]; exact hX.rank_start_le) (by rwa [hΦ₀])
  have h₃ := norm_trunc_sub_le (A₁ := Φ t₁) hκ htr
  have h₄ := mul_le_mul_of_nonneg_left h₂ hκ
  have h₅ := mul_le_mul_of_nonneg_left h₁ (by linarith : (0 : ℝ) ≤ 1 + κ)
  have e : (t₁ - t₀) *
      ((10 * κ * L * B + (1 + κ) * (L * B + Lt) / 2) * (t₁ - t₀) + (1 + 2 * κ) * ε) =
      κ * ((t₁ - t₀) * (10 * L * B * (t₁ - t₀) + ε)) +
        (1 + κ) * ((t₁ - t₀) * ((L * B + Lt) / 2 * (t₁ - t₀) + ε)) := by ring
  rw [e]
  linarith

end Error

end Rel

/-! ### The method is tube-local -/

section TubeLocal

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ} {κ : ℝ}

/-- **The projected Euler method is a tube-local method** (`StepMethod.IsTubeLocal`), with the
matrices of rank at most `r` as admissible values and margin constant `0`, for every `κ ≥ 1` and
`r ≤ m`, `r ≤ n`: a step exists from every matrix of rank at most `r` for every field
(`MatrixProjEuler.exists_stepRel`), its result has rank at most `r`, and since the step
evaluates the field only at `(t₀, Y₀)`, a step of the tube extension from a start value in the
tube is a step of the field (`MatrixProjEuler.stepRel_tubeExt_iff`). -/
theorem isTubeLocal_stepRel (hκ : 1 ≤ κ) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) :
    StepMethod.IsTubeLocal (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => stepRel G r κ)
      (fun Y => Y.rank ≤ r) 0 where
  exists_step := fun _ _ _ hY₀ => exists_stepRel _ _ _ hκ hrm hrn hY₀
  adm_of_step := fun _ _ hstep => hstep.rank_le
  step_of_tubeExt := fun _ _ ha hb h01 _ _ hsmall hstep =>
    (stepRel_tubeExt_iff ⟨ha, h01.trans hb⟩ (by simpa using hsmall.le)).1 hstep

end TubeLocal

/-! ### The error bound, and existence of a run near the exact solution -/

section Run

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {t₀ h T ρ L B ε Lt δ κ : ℝ}
  {N : ℕ}

/-- The constant of the error bound of this file is not negative. -/
private theorem projEulerConst_nonneg_aux (hκ : 0 ≤ κ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hLt : 0 ≤ Lt) (hε₀ : 0 ≤ ε) (hh : 0 ≤ h) :
    0 ≤ (10 * κ * L * B + (1 + κ) * (L * B + Lt) / 2) * h + (1 + 2 * κ) * ε := by
  positivity

/-- **Local error of one step of a uniform grid.** Under the hypotheses of the run theorem
(`DLRAProblem`, joint continuity and `FactoredNormalBoundOn` on the tube of radius `ρ` around
`A` over `[t₀, t₀ + N h]`, and `‖F(t, X) - F(s, X)‖ ≤ Lₜ (t - s)` for `s ≤ t` and `X` in the
tube at both times), a projected Euler step over `[t₀ + k h, t₀ + (k + 1) h]`, `k < N`, whose
start value `Z₀` satisfies `‖Z₀ - A (t₀ + k h)‖ + 2 B h < ρ` has local error
`h ((10 κ L B + (1 + κ) (L B + Lₜ) / 2) h + (1 + 2 κ) ε)`. -/
theorem stepRel.hasLocalError_uniformGrid {k : ℕ} {Z₀ Z₁ : Matrix m n ℝ}
    (hstep : stepRel F r κ (t₀ + k * h) (t₀ + (k + 1) * h) Z₀ Z₁) (hκ : 0 ≤ κ)
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hFt : ∀ s t x, s ≤ t → (s, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ →
      (t, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ → ‖F t x - F s x‖ ≤ Lt * (t - s))
    (hh : 0 ≤ h) (hk : k < N) (hnear : ‖Z₀ - A (t₀ + k * h)‖ + 2 * B * h < ρ) :
    HasLocalError F (t₀ + k * h) (t₀ + (k + 1) * h) Z₀ Z₁
      (h * ((10 * κ * L * B + (1 + κ) * (L * B + Lt) / 2) * h + (1 + 2 * κ) * ε)) := by
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
  have hloc := hstep.hasLocalError_of_tube hκ hε hε₀ hP.lipschitz hP.L_nonneg hP.bounded
    hP.B_nonneg hc hP.sol.cont ha hb h01 hA hFt' (by rw [hsub]; linarith)
  rwa [hsub] at hloc

/-- **Every run of the projected Euler method satisfies the robust error bound**
([KieriVandereycken2019], Theorem 4, for every run). Let `A` solve `Y' = F(t, Y)` on
`[t₀, t₀ + N h]`, and let `F` be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ`
around `A` (`DLRAProblem`), jointly continuous there, with normal component at most `ε` at the
rank-`r` matrices of the tube (`FactoredNormalBoundOn`), and with
`‖F(t, X) - F(s, X)‖ ≤ Lₜ (t - s)` for `s ≤ t` and `X` in the tube at both times. Let
`Y 0, …, Y N` be a run of the projected Euler method with a `κ`-quasi-optimal retraction,
`κ ≥ 0`, step size `h ≥ 0`, `N h ≤ T` and `‖Y 0 - A t₀‖ ≤ δ`. If the bound below plus `2 B h` is
smaller than `ρ`, then for all `n ≤ N`

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} c`,
  `c = (10 κ L B + (1 + κ) (L B + Lₜ) / 2) h + (1 + 2 κ) ε`.

The constants do not depend on the singular values of the `Y n`. -/
theorem IsRun.norm_sub_le {Y : ℕ → Matrix m n ℝ}
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → (s, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ →
      (t, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ → ‖F t x - F s x‖ ≤ Lt * (t - s))
    (hκ : 0 ≤ κ) (hh : 0 ≤ h) (hNT : N * h ≤ T)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) *
      ((10 * κ * L * B + (1 + κ) * (L * B + Lt) / 2) * h + (1 + 2 * κ) * ε) + 2 * B * h < ρ)
    (hY : IsRun (stepRel F r κ) (uniformGrid t₀ h) N Y) (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) *
      ((10 * κ * L * B + (1 + κ) * (L * B + Lt) / 2) * h + (1 + 2 * κ) * ε) := by
  have hc₀ := projEulerConst_nonneg_aux hκ hP.L_nonneg hP.B_nonneg hLt hε₀ hh
  refine hY.norm_sub_le_of_tube_uniformGrid (T := T) (δ₀ := δ)
    (c := (10 * κ * L * B + (1 + κ) * (L * B + Lt) / 2) * h + (1 + 2 * κ) * ε) hP hc
    (fun n hn Y₀ Y₁ hnear hstep => ?_) hc₀ hδ hNT hsmall
  exact hstep.hasLocalError_uniformGrid hκ hP hc hε hε₀ hFt hh hn (by linarith)

/-- **Existence and robust error bound for the projected Euler method** ([KieriVandereycken2019],
Theorem 4, with explicit constants and tube hypotheses). Let `A` solve `Y' = F(t, Y)` on
`[t₀, t₀ + N h]`, and let `F` be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ`
around `A` (`DLRAProblem`), jointly continuous there, with normal component at most `ε` at the
rank-`r` matrices of the tube (`FactoredNormalBoundOn`), and with
`‖F(t, X) - F(s, X)‖ ≤ Lₜ (t - s)` for `s ≤ t` and `X` in the tube at both times. Let `r ≤ m`,
`r ≤ n`, `κ ≥ 1`, `h ≥ 0`, `N h ≤ T`, and let `Y₀` have rank at most `r` with
`‖Y₀ - A t₀‖ ≤ δ`. If

  `e^{L T} δ + T e^{L T} c + 2 B h < ρ`,  `c = (10 κ L B + (1 + κ) (L B + Lₜ) / 2) h + (1 + 2 κ) ε`,

then the projected Euler method with a `κ`-quasi-optimal retraction can be run from `Y₀`: there
are `Y 0 = Y₀, …, Y N` of rank at most `r`, each a projected Euler step of size `h` from the
previous one, with `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} c` for all `n ≤ N`.

This is the paper's `C (δ + ε + h)` with an explicit `C`; it depends on `L`, `B`, `Lₜ`, `T` and
`κ = C_ℛ`, not on the singular values of the `Y n`. The paper's one-sided constant `ℓ` is not
used (the bound carries `e^{L T}`), the field is controlled only on the tube, and neither the
projected solution nor full rank of the `Y n` is assumed. For a field that does not depend on
time, `Lₜ = 0`; for `κ = 1`, `c = (11 L B + Lₜ) h + 3 ε`. -/
theorem exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → (s, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ →
      (t, x) ∈ tubeSet A t₀ (t₀ + N * h) ρ → ‖F t x - F s x‖ ≤ Lt * (t - s))
    (hκ : 1 ≤ κ) (hh : 0 ≤ h) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) *
      ((10 * κ * L * B + (1 + κ) * (L * B + Lt) / 2) * h + (1 + 2 * κ) * ε) + 2 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r κ) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ +
        T * Real.exp (L * T) *
          ((10 * κ * L * B + (1 + κ) * (L * B + Lt) / 2) * h + (1 + 2 * κ) * ε) := by
  have hκ₀ : 0 ≤ κ := zero_le_one.trans hκ
  have hc₀ := projEulerConst_nonneg_aux hκ₀ hP.L_nonneg hP.B_nonneg hLt hε₀ hh
  refine ((isTubeLocal_stepRel hκ hrm hrn).mono (by norm_num : (0 : ℝ) ≤ 2)).exists_run_norm_sub_le
    le_rfl hP hc (fun k hk Z₀ Z₁ _ hnear hstep => ?_) hc₀ hh hNT hY₀ hδ hsmall
  exact stepRel.hasLocalError_uniformGrid hstep hκ₀ hP hc hε hε₀ hFt hh hk (by linarith)

end Run

/-! ### Examples: a nonlinear field and a linear field -/

section Examples

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}

/-- **Non-vacuity of the existence and error theorem.** The radial field
`F(t, Y) = Y / max ‖Y‖ 1` is `2`-Lipschitz, bounded by `1`, does not depend on time and has no
normal component at any matrix (`MatrixKSL.radial_normal_eq_zero`), so `ε = 0` and `Lₜ = 0`.
For every solution `A` on `[t₀, t₀ + N h]` (of any rank), every `κ ≥ 1` and every start value
`Y₀` of rank at most `r` with `‖Y₀ - A t₀‖ ≤ δ`, the projected Euler method can be run with any
step size `h ≥ 0`, and the run stays within `e^{2 T} δ + T e^{2 T} (20 κ + (1 + κ)) h` of `A`. -/
example {κ : ℝ} (hκ : 1 ≤ κ) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {A : ℝ → Matrix m n ℝ} {t₀ h T δ : ℝ} {N : ℕ}
    (hA : ODESolution (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) A t₀ (t₀ + N * h))
    (hh : 0 ≤ h) (hNT : N * h ≤ T) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r)
    (hδ : ‖Y₀ - A t₀‖ ≤ δ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (stepRel (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) r κ)
        (uniformGrid t₀ h) N Y ∧
      ∀ j ≤ N, (Y j).rank ≤ r ∧ ‖Y j - A (t₀ + j * h)‖ ≤ Real.exp (2 * T) * δ +
        T * Real.exp (2 * T) *
          ((10 * κ * 2 * 1 + (1 + κ) * (2 * 1 + 0) / 2) * h + (1 + 2 * κ) * 0) := by
  have hcont : Continuous fun Z : Matrix m n ℝ => MatrixKSL.radial Z :=
    (LipschitzWith.of_dist_le' (K := 2) fun X Y => by
      rw [dist_eq_norm, dist_eq_norm]; exact MatrixKSL.norm_radial_sub_le X Y).continuous
  exact exists_run_norm_sub_le (F := fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z)
    (A := A) (L := 2) (B := 1) (ε := 0) (Lt := 0)
    (ρ := Real.exp (2 * T) * δ + T * Real.exp (2 * T) *
      ((10 * κ * 2 * 1 + (1 + κ) * (2 * 1 + 0) / 2) * h + (1 + 2 * κ) * 0) + 2 * 1 * h + 1)
    ⟨hA, by norm_num, by norm_num, fun _ _ X Y _ _ => MatrixKSL.norm_radial_sub_le X Y,
      fun _ _ X _ => MatrixKSL.norm_radial_le X⟩
    (hcont.comp continuous_snd).continuousOn
    (fun t U V S hU hV _ => MatrixKSL.radial_normal_eq_zero t U S V hU hV) le_rfl le_rfl
    (fun _ _ _ _ _ _ => by simp) hκ hh hNT hrm hrn hY₀ hδ (lt_add_one _)

/-- **Non-vacuity for a field that is not bounded.** The linear field
`F(t, Y) = M Y + Y Nᵀ + G` with a stationary point `C` (`M C + C Nᵀ + G = 0`) is Lipschitz with
constant `‖M‖ + ‖N‖`, bounded by `(‖M‖ + ‖N‖) ρ` on the tube of radius `ρ` around `A(t) = C`,
and its normal component at the rank-`r` matrices is at most `‖G‖` (`dlraProblem_linear`,
`factoredNormalBoundOn_linear`). Under the smallness condition the projected Euler method can
be run from every `Y₀` of rank at most `r` near `C`, and the run satisfies the error bound with
`ε = ‖G‖`, `Lₜ = 0`. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) {κ : ℝ} (hκ : 1 ≤ κ) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) (t₀ : ℝ) {ρ T δ h : ℝ} {K : ℕ} (hρ : 0 ≤ ρ) (hh : 0 ≤ h)
    (hKT : K * h ≤ T) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - C‖ ≤ δ)
    (hsmall : Real.exp ((‖M‖ + ‖N‖) * T) * δ + T * Real.exp ((‖M‖ + ‖N‖) * T) *
      ((10 * κ * (‖M‖ + ‖N‖) * ((‖M‖ + ‖N‖) * ρ) +
        (1 + κ) * ((‖M‖ + ‖N‖) * ((‖M‖ + ‖N‖) * ρ) + 0) / 2) * h + (1 + 2 * κ) * ‖G‖)
      + 2 * ((‖M‖ + ‖N‖) * ρ) * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (stepRel (fun _ Y => M * Y + Y * Nᵀ + G) r κ) (uniformGrid t₀ h) K Y ∧
      ∀ j ≤ K, (Y j).rank ≤ r ∧ ‖Y j - C‖ ≤ Real.exp ((‖M‖ + ‖N‖) * T) * δ +
        T * Real.exp ((‖M‖ + ‖N‖) * T) *
          ((10 * κ * (‖M‖ + ‖N‖) * ((‖M‖ + ‖N‖) * ρ) +
            (1 + κ) * ((‖M‖ + ‖N‖) * ((‖M‖ + ‖N‖) * ρ) + 0) / 2) * h + (1 + 2 * κ) * ‖G‖) :=
  exists_run_norm_sub_le (A := fun _ => C) (Lt := 0) (dlraProblem_linear M N G C hC _ _ hρ)
    (continuous_uncurry_linear M N G).continuousOn
    (factoredNormalBoundOn_linear M N G _) (norm_nonneg G) le_rfl
    (fun _ _ _ _ _ _ => by simp) hκ hh hKT hrm hrn hY₀ hδ hsmall

/-- **A concrete instance of the previous example** (the data of `LinearFieldExample`). On
`2 × 2` matrices with rank `r = 1` and the exact truncation `κ = 1`, take `M = -E`, `N = 0` and
`G = C = E` with `E = e₁ e₁ᵀ`, so that `L = ‖M‖ + ‖N‖ = 1`, `B = ρ`, `‖G‖ = 1` and `Lₜ = 0`; the
start value `Y₀ = (5/4) E` has rank one and `‖Y₀ - C‖ = 1/4`. With `K = 10` steps of size
`h = 1/100` up to `T = 1/10` and the tube radius `ρ = 4` the smallness condition holds
(`e^{1/10} ≤ 3`): a run of the projected Euler method exists, stays of rank one and satisfies the
error bound. -/
example (t₀ : ℝ) :
    ∃ Y : ℕ → Matrix (Fin 2) (Fin 2) ℝ, Y 0 = Matrix.vecMulVec ![5 / 4, 0] ![1, 0] ∧
      IsRun (stepRel (fun _ Y => -Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0] * Y +
        Y * (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ + Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]) 1 1)
        (uniformGrid t₀ (1 / 100)) 10 Y ∧
      ∀ j ≤ 10, (Y j).rank ≤ 1 ∧ ‖Y j - Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]‖ ≤
        Real.exp (1 * (1 / 10)) * (1 / 4) + 1 / 10 * Real.exp (1 * (1 / 10)) *
          ((10 * 1 * 1 * 4 + (1 + 1) * (1 * 4 + 0) / 2) * (1 / 100) + (1 + 2 * 1) * 1) := by
  have he := LinearFieldExample.exp_le_three
  exact exists_run_norm_sub_le (LinearFieldExample.dlraProblem _ _ (ρ := 4) (by norm_num))
    (continuous_uncurry_linear _ _ _).continuousOn (LinearFieldExample.factoredNormalBoundOn _ _)
    zero_le_one le_rfl (fun _ _ _ _ _ _ => by simp) le_rfl (by norm_num) (by norm_num) (by simp)
    (by simp) (Matrix.rank_vecMulVec_le _ _) LinearFieldExample.norm_start_sub_le (by linarith)

end Examples

end MatrixProjEuler

end LeanDLRA
