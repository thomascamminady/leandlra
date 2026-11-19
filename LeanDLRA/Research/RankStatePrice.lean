import LeanDLRA.Research.RankInformationUpperBound
import LeanDLRA.DLRA.QuasiOptimalityNormal

/-!
# The loss of a state of rank `r` along a turning frame, and buffer modes

For a field without dependence on the state, `F(t, Z) = Ȧ(t)` (Lipschitz constant `0`), a method
that integrates `Ȧ` and truncates has the error `dist(A(T), M_{≤ r})`. The projected equation
`Ẏ = P(Y) Ȧ` of rank `r` loses the part of `Ȧ` that is normal at `Y`, and the loss adds up while
the tangent space turns. This file has an explicit family in `ℝ^{2 × 2}`, `r = 1`, with
`u(t) = (cos t, sin t)`, `u⊥(t) = (-sin t, cos t)`,

  `Y t = u(t) e₁ᵀ`,   `A t = u(t) (e₁ + ε t e₂)ᵀ + ε u⊥(t) e₂ᵀ`,   `Ȧ(t) = u⊥(t) (e₁ + ε t e₂)ᵀ`:

`Y` is the solution of rank one of the projected equation from `Y 0`, a best approximation of
`A 0 = diag(1, ε)`; `dist(A t, M_{≤ 1}) ≤ ε` for all `t`; and `‖A t - Y t‖ = ε √(1 + t²)`. The
second column of `A` is `ε` times an involute of the unit circle: its velocity `ε t u⊥(t)` is
normal at `Y t` at every time.

A state of rank `k ≥ r` whose result is truncated to rank `r` (buffer modes) has the error
`dist(A(t), M_{≤ r})` plus twice the error of the state of rank `k`
(`RankInformationUpperBound.norm_sub_le_distLR_add_two_mul`); with the quasi-optimality bound of
`LeanDLRA/DLRA/QuasiOptimalityNormal.lean` for the rank `k` this is a bound in which the
singular value and the distance of the rank `k` take the place of those of the rank `r`.

## Main results

* `RankStatePrice.norm_sub_le_distLR_add_two_mul_of_isDLRASolution`: the bound for a solution of
  rank `k` of the projected equation whose value is truncated to rank `r`.
* `RankStatePriceExample.isDLRASolution_involuteState`, `odeSolution_involuteData`,
  `distLR_involuteData_le`, `norm_involuteData_sub`, `dlra_error_eq_mul_sqrt`: the family.
-/

open Set Matrix
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA.RankStatePrice

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Buffer modes.** Let `Y` be a solution of rank `k` of the projected equation, `X` a curve of
critical points of rank `k` of the distance to the exact solution `A` with `ρ ≤ σ_k(X)` and the
margin `‖X - A‖ ≤ θ ρ`, `θ < 1`, and `W` a best approximation of rank at most `r` of `Y t`. Then
`‖W - A t‖ ≤ dist(A t, M_{≤ r}) + 2 (‖X t - A t‖ + e^{(L + μ/ρ + κ)(t - a)} (δ + (L + κ) ∫ₐᵗ
‖X s - A s‖ ds))`, `κ = μ / ((1 - θ) ρ)`: the singular value and the distance in the second term
are those of the rank `k` of the state, not of the rank `r` of the result. -/
theorem norm_sub_le_distLR_add_two_mul_of_isDLRASolution {k r : ℕ}
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A X X' Y : ℝ → Matrix m n ℝ} {a b L μ ρ θ δ : ℝ}
    (hY : IsDLRASolution k F Y a b) (hρ : 0 < ρ) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hA : ODESolution F A a b) (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ)
    (hXc : ContinuousOn X (Icc a b)) (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Icc a b, (X t).rank = k)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (X t)).singularValues (k - 1))
    (hopt : ∀ t ∈ Icc a b, tangentProjAt (X t) (A t - X t) = 0) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc a b, ‖X t - A t‖ ≤ θ * ρ) (hδ : ‖Y a - X a‖ ≤ δ) {t : ℝ} (ht : t ∈ Icc a b)
    {W : Matrix m n ℝ} (hW : ‖W - Y t‖ = distLR r (Y t)) :
    ‖W - A t‖ ≤ distLR r (A t) + 2 * (‖X t - A t‖ +
      Real.exp ((L + μ / ρ + μ / ((1 - θ) * ρ)) * (t - a)) *
        (δ + (L + μ / ((1 - θ) * ρ)) * ∫ s in a..t, ‖X s - A s‖)) := by
  have h1 := RankInformationUpperBound.norm_sub_le_distLR_add_two_mul (A := A t) hW
  have h2 := hY.norm_sub_le_integral_of_margin_lt_one hρ hL hF hA hμ hXc hX hXr hσ hopt hθ hd hδ
    t ht
  have h3 : ‖Y t - A t‖ ≤ ‖Y t - X t‖ + ‖X t - A t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  linarith

end LeanDLRA.RankStatePrice

/-! ### A rank-one state on a turning frame -/

namespace LeanDLRA.RankStatePriceExample

open LeanDLRA.QuasiOptimalitySpeedExample

/-- The state `Y t = u(t) e₁ᵀ`, `u(t) = (cos t, sin t)`. -/
noncomputable def involuteState (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos t, 0; Real.sin t, 0]

/-- The derivative `u⊥(t) e₁ᵀ` of the state. -/
noncomputable def involuteStateDeriv (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-Real.sin t, 0; Real.cos t, 0]

/-- The data `A t = u(t) (e₁ + ε t e₂)ᵀ + ε u⊥(t) e₂ᵀ`. -/
noncomputable def involuteData (ε t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos t, ε * (t * Real.cos t - Real.sin t); Real.sin t, ε * (t * Real.sin t + Real.cos t)]

/-- The derivative `u⊥(t) (e₁ + ε t e₂)ᵀ` of the data. -/
noncomputable def involuteDeriv (ε t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-Real.sin t, -(ε * (t * Real.sin t)); Real.cos t, ε * (t * Real.cos t)]

/-- `Y t = u(t) 1 e₁ᵀ`. -/
theorem involuteState_eq (t : ℝ) :
    involuteState t = rotCol t * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (rotCol 0)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [involuteState, rotCol, Matrix.mul_apply]

/-- `Y t` has rank `1`. -/
theorem rank_involuteState (t : ℝ) : (involuteState t).rank = 1 :=
  (SVD.rank_eq_iff_exists_factor _).2 ⟨rotCol t, 1, rotCol 0, rotCol_transpose_mul_self t,
    rotCol_transpose_mul_self 0, by simp, involuteState_eq t⟩

/-- The derivative of the state. -/
theorem hasDerivAt_involuteState (t : ℝ) :
    HasDerivAt involuteState (involuteStateDeriv t) t := by
  have e : involuteState = fun s : ℝ =>
      Real.cos s • (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
        + Real.sin s • (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
    funext s
    ext i j
    fin_cases i <;> fin_cases j <;> simp [involuteState]
  have h := ((Real.hasDerivAt_cos t).smul_const (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)).add
    ((Real.hasDerivAt_sin t).smul_const (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ))
  rw [e]
  convert h using 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [involuteStateDeriv]

/-- The derivative of the data. -/
theorem hasDerivAt_involuteData (ε t : ℝ) :
    HasDerivAt (involuteData ε) (involuteDeriv ε t) t := by
  have e : involuteData ε = fun s : ℝ =>
      Real.cos s • (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
        + Real.sin s • (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)
        + (ε * (s * Real.cos s - Real.sin s)) • (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
        + (ε * (s * Real.sin s + Real.cos s)) • (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
    funext s
    ext i j
    fin_cases i <;> fin_cases j <;> simp [involuteData]
  have hc := Real.hasDerivAt_cos t
  have hs := Real.hasDerivAt_sin t
  have hi := hasDerivAt_id t
  have h3 : HasDerivAt (fun s : ℝ => ε * (s * Real.cos s - Real.sin s))
      (ε * (1 * Real.cos t + t * -Real.sin t - Real.cos t)) t :=
    ((hi.mul hc).sub hs).const_mul ε
  have h4 : HasDerivAt (fun s : ℝ => ε * (s * Real.sin s + Real.cos s))
      (ε * (1 * Real.sin t + t * Real.cos t + -Real.sin t)) t :=
    ((hi.mul hs).add hc).const_mul ε
  have h := (((hc.smul_const (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)).add
    (hs.smul_const (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ))).add
    (h3.smul_const (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ))).add
    (h4.smul_const (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ))
  rw [e]
  refine h.congr_deriv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [involuteDeriv]

/-- The tangent projector at `Y t` maps the velocity of the data to the velocity of the state:
the velocity `ε t u⊥(t) e₂ᵀ` of the second column is normal at `Y t`. -/
theorem tangentProjAt_involuteDeriv (ε t : ℝ) :
    tangentProjAt (involuteState t) (involuteDeriv ε t) = involuteStateDeriv t := by
  have h := tangentProjAt_eq_tangentProj (S := (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (rotCol_transpose_mul_self t) (rotCol_transpose_mul_self 0) (by simp)
  rw [← involuteState_eq] at h
  have key : tangentProj (rotCol t) (rotCol 0) (involuteDeriv ε t) =
      rotProj t * involuteDeriv ε t + involuteDeriv ε t * rotProj 0
        - rotProj t * involuteDeriv ε t * rotProj 0 := by
    rw [tangentProj_apply]
    simp only [rotProj, Matrix.mul_assoc]
  rw [h, key, rotProj_eq_of, rotProj_eq_of]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [involuteDeriv, involuteStateDeriv] <;> ring

/-- `Y` is the solution of rank one of the projected equation for the field `F(t, Z) = Ȧ(t)`. -/
theorem isDLRASolution_involuteState (ε T : ℝ) :
    IsDLRASolution 1 (fun t _ => involuteDeriv ε t) involuteState 0 T := by
  refine ⟨⟨fun t _ => (hasDerivAt_involuteState t).continuousAt.continuousWithinAt,
    fun t _ => ?_⟩, fun t _ => rank_involuteState t⟩
  beta_reduce
  rw [tangentProjAt_involuteDeriv]
  exact (hasDerivAt_involuteState t).hasDerivWithinAt

/-- The data solve `y' = Ȧ(t)`. -/
theorem odeSolution_involuteData (ε T : ℝ) :
    ODESolution (fun t _ => involuteDeriv ε t) (involuteData ε) 0 T :=
  ⟨fun t _ => (hasDerivAt_involuteData ε t).continuousAt.continuousWithinAt,
    fun t _ => (hasDerivAt_involuteData ε t).hasDerivWithinAt⟩

/-- The data are at the distance at most `ε` from the matrices of rank at most one, at every
time: `A t - u(t) (e₁ + ε t e₂)ᵀ = ε u⊥(t) e₂ᵀ`. -/
theorem distLR_involuteData_le {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    distLR 1 (involuteData ε t) ≤ ε := by
  have hr : (rotCol t * (1 : Matrix (Fin 1) (Fin 1) ℝ) *
      (!![1; ε * t] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ).rank ≤ 1 := rank_mul_mul_transpose_le _ _ _
  refine (distLR_le_norm_sub hr).trans (le_of_eq ?_)
  have h : ‖involuteData ε t - rotCol t * (1 : Matrix (Fin 1) (Fin 1) ℝ) *
      (!![1; ε * t] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ‖ ^ 2 = ε ^ 2 := by
    rw [Curvature.frob_sq]
    simp only [involuteData, rotCol, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply]
    simp
    nlinarith [Real.cos_sq_add_sin_sq t]
  rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_sq hε]

/-- **The error of the state:** `‖A t - Y t‖ = ε √(1 + t²)`. -/
theorem norm_involuteData_sub {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    ‖involuteData ε t - involuteState t‖ = ε * √(1 + t ^ 2) := by
  have h : ‖involuteData ε t - involuteState t‖ ^ 2 = (ε * √(1 + t ^ 2)) ^ 2 := by
    rw [Curvature.frob_sq, mul_pow, Real.sq_sqrt (by positivity)]
    simp only [involuteData, involuteState, Fin.sum_univ_two, Matrix.sub_apply]
    simp
    nlinarith [Real.cos_sq_add_sin_sq t]
  rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_sq (by positivity)]

/-- The error of the state is at least `ε t`. -/
theorem mul_le_norm_involuteData_sub {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    ε * t ≤ ‖involuteData ε t - involuteState t‖ := by
  rw [norm_involuteData_sub hε]
  refine mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le ?_) hε
  linarith

/-- The start `Y 0` is at the distance `ε = dist(A 0, M_{≤ 1})` from `A 0 = diag(1, ε)`. -/
theorem distLR_involuteData_zero {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    distLR 1 (involuteData ε 0) = ε := by
  have e : involuteData ε 0 = Matrix.diagonal ![1, ε] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [involuteData]
  rw [e]
  exact InformationLowerBoundExample.distLR_one_diagonal hε hε1

/-- **The projected equation of rank one loses `ε` per unit of the turning angle.** For
`0 ≤ ε ≤ 1` and every `T`: `Y` solves the projected equation of rank one from a best approximation
of `A 0`; the data `A` solve the equation, whose field has the Lipschitz constant `0`; the data
stay at the distance at most `ε` from the matrices of rank at most one; and the error of `Y` at
the time `t` is `ε √(1 + t²)`. -/
theorem dlra_error_eq_mul_sqrt {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (T : ℝ) :
    IsDLRASolution 1 (fun t _ => involuteDeriv ε t) involuteState 0 T ∧
      ODESolution (fun t _ => involuteDeriv ε t) (involuteData ε) 0 T ∧
      IsLipschitzField (fun t (_ : Matrix (Fin 2) (Fin 2) ℝ) => involuteDeriv ε t) 0 ∧
      ‖involuteData ε 0 - involuteState 0‖ = distLR 1 (involuteData ε 0) ∧
      (∀ t, distLR 1 (involuteData ε t) ≤ ε) ∧
      ∀ t, ‖involuteData ε t - involuteState t‖ = ε * √(1 + t ^ 2) := by
  refine ⟨isDLRASolution_involuteState ε T, odeSolution_involuteData ε T, fun t x y => by simp,
    ?_, distLR_involuteData_le hε, norm_involuteData_sub hε⟩
  rw [norm_involuteData_sub hε, distLR_involuteData_zero hε hε1]
  simp

/-- The hypotheses of `RankStatePrice.norm_sub_le_distLR_add_two_mul_of_isDLRASolution` hold for
the rotating projector `A = X = Y`, with `k = r = 1`, `L = θ = δ = 0`, `μ = √2`, `ρ = 1`. -/
example : ‖rotProj 1 - rotProj 1‖ ≤ distLR 1 (rotProj 1) + 2 * (‖rotProj 1 - rotProj 1‖ +
    Real.exp ((0 + √2 / 1 + √2 / ((1 - 0) * 1)) * (1 - 0)) *
      (0 + (0 + √2 / ((1 - 0) * 1)) * ∫ s in (0 : ℝ)..1, ‖rotProj s - rotProj s‖)) :=
  RankStatePrice.norm_sub_le_distLR_add_two_mul_of_isDLRASolution (X' := rotProjDeriv)
    (RankInformationUpperBoundExample.isDLRASolution_rotProj 1) one_pos le_rfl
    (fun t x y => by simp)
    ⟨fun t _ => (hasDerivAt_rotProj t).continuousAt.continuousWithinAt,
      fun t _ => (hasDerivAt_rotProj t).hasDerivWithinAt⟩
    (fun t _ => (norm_rotProjDeriv t).le)
    (fun t _ => (hasDerivAt_rotProj t).continuousAt.continuousWithinAt)
    (fun t _ => (hasDerivAt_rotProj t).hasDerivWithinAt) (fun t _ => rank_rotProj t)
    (fun t _ => one_le_singularValues_rotProj t) (fun t _ => by simp) zero_lt_one
    (fun t _ => by simp) (by simp) (right_mem_Icc.2 zero_le_one)
    (by rw [sub_self, norm_zero]; exact (distLR_eq_zero_iff.2 (rank_rotProj 1).le).symm)

end LeanDLRA.RankStatePriceExample
