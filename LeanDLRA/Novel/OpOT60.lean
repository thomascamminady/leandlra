import LeanDLRA.Dynamics.ContinuousDLRA
import LeanDLRA.Integrators.ProjectorSplitting
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Projectors

/-!
# Weak (observable) error of dynamical low-rank approximation

Open problem OP-OT-60 of `docs/survey/open-problems.json` (arXiv 1902.00424, Secs. 8 and 10).  The
question: for a linear observable `⟪φ, Y(t)⟫` of the DLRA solution
`Ẏ = P(Y) F(t, Y)` of `Ȧ = F(t, A)`, is the error `⟪φ, Y(t) - A(t)⟫` smaller in order than the
strong error `‖Y(t) - A(t)‖ = O(ε)` (`ε` the normal component of the field), can it be `O(ε²)`,
or is there a sharp lower bound of order `ε`; and what happens for BUG and KSL.

## Results

Everything is on a real inner product space `E` with a time-dependent projector family `P(t)`
along the trajectory, as in `Dynamics/ContinuousDLRA`.  The dual solution `ψ` is a curve with
`⟪ψ', Y - A⟫ = -⟪ψ, F(Y) - F(A)⟫` (`IsDualAlong`); for the affine model `F = ℒ x + g(t)` it is
`ψ(t) = exp((T - t) ℒ*) φ`, the solution of the adjoint equation (`expDual`,
`isDualAlong_expDual`), independent of the trajectories.

* **Identity** (`hasDerivWithinAt_inner_sub`, `hasDerivWithinAt_inner_sub_normal`): for any
  substep equation `Ẏ = Q(t) F(t, Y)`, `d/dt ⟪ψ, Y - A⟫ = -⟪ψ, (1 - Q) F(Y)⟫`, and for an
  orthogonal projector `= -⟪(1 - P) ψ, (1 - P) F(Y)⟫`: the weak error is the defect weighted by
  the *normal component of the dual solution*.
* **Bound** (`abs_inner_sub_le`, `abs_inner_le_of_start`): `|⟪φ, Y b - A b⟫| ≤ ε η (b - a)` with
  `η = sup ‖(1 - P(t)) ψ(t)‖`; no Lipschitz constant and no exponential, unlike the strong bound.
* **Exact conservation** (`inner_sub_const`, `inner_sub_const_of_tangent`) when the dual solution
  is tangent along `Y`, generalising `ODESolution.dlra_inner_const` to time-dependent `ψ`.
* **Observables in the basis ranges** (`abs_inner_le_of_tangent_observable`): if `P(t) φ = φ`
  along the trajectory, `|⟪φ, Y b - A b⟫| ≤ ε Lψ (b - a)² / 2`, one power of the *time* better
  than the strong error, not of `ε`.
* **Sharpness** (`weak_error_sharp`, `weak_error_sharp_matrix`, `exists_nonzero_normal`): for
  the constant normal field `N = c (1 - P₀) φ` the DLRA solution is stationary and
  `|⟪φ, Y b - A b⟫| = ε ‖(1 - P₀) φ‖ (b - a)` exactly.  The weak error is of first order in `ε`
  for every observable with a nonzero normal component, with the sharp constant `η`; `O(ε²)` is
  impossible in general.
* **Superconvergence** (`norm_normal_le_of_curvature`, `abs_inner_le_of_tangent_curvature`,
  `abs_inner_le_sq_of_tangent`, `norm_normal_le_of_tangent_matrix`): if the dual solution is
  tangent along a curve `X` on the manifold at distance `d` from `Y` and the Koch–Lubich
  curvature bound holds with constant `γ` (`2/σ_r` on matrices, `koch_lubich_tangent_frob`), then
  `|⟪φ, Y b - A b⟫| ≤ ε γ d M (b - a)`; with `X = A` and the robust strong bound this is
  `γ M e^{L(b-a)} (b - a)² ε²`.  This is the dual-weighted-residual / Aubin–Nitsche mechanism, and
  the price is `1/σ_r`.
* **BUG** (`IsRankAdaptiveBUGStep.weak_error_le`): one augmented BUG step satisfies
  `|⟪ψ t₁, Y₁ - A t₁⟫ - ⟪ψ t₀, Y₀ - A t₀⟫| ≤ ε̂ η (t₁ - t₀) + ‖P̂ ψ(t₁)‖ ϑ`, with `P̂` the
  augmented projector, `ε̂` the S-step defect, `η` the normal component of `ψ` w.r.t. the augmented
  bases and `ϑ` the truncation.
* **BUG and KSL lower bound** (`stationary_of_normal`): at a normal fixed point both integrators
  return `Y₀`, so the one-step weak error is exactly `-(t₁ - t₀) ⟪(1 - P₀) φ, N⟫` and the sharpness
  statement holds for them verbatim.

## Not covered

An upper weak-error bound for KSL (its substep defects are `O(1)` individually; only the
composition is `O(ε)`), nonlinear observables (electric energy), and a formalized instance of the
superconvergence hypotheses with `ε > 0` (a `2 × 2` example was checked numerically).
-/

open Set
open scoped RealInnerProductSpace

namespace LeanDLRA.Novel.OpOT60

open LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Identity

variable {Q P : ℝ → E →L[ℝ] E} {F : ℝ → E → E} {Y A ψ ψ' : ℝ → E} {a b : ℝ}

/-- **Weak-error identity, pointwise form.**  Let `Ẏ = Q(t) F(t, Y)` be any projected (or
substep) equation, `Ȧ = F(t, A)` the full model, and let `ψ` be a *dual solution along the
error*: a curve with right derivative `ψ'` satisfying `⟪ψ', Y - A⟫ = -⟪ψ, F(Y) - F(A)⟫`
(for `F(t, x) = ℒ x + g(t)` this is the adjoint equation `ψ' = -ℒ* ψ`, see
`hasDerivAt_expAdjoint`).  Then

  `d/dt ⟪ψ, Y - A⟫ = -⟪ψ, (1 - Q(t)) F(t, Y)⟫`,

i.e. the weak error is driven by the *defect* `(1 - Q) F(Y)` of the projected equation, weighted
by the dual solution.  No projector property of `Q` is used, so this also covers the backward
S-step `Q = -P₁ Q₀` of the projector-splitting integrator.  This is the dual-weighted-residual
identity (Becker–Rannacher) for DLRA. -/
theorem hasDerivWithinAt_inner_sub (hY : ODESolution (fun t x => Q t (F t x)) Y a b)
    (hA : ODESolution F A a b) {t : ℝ} (ht : t ∈ Ico a b)
    (hψ : HasDerivWithinAt ψ (ψ' t) (Ici t) t)
    (hadj : ⟪ψ' t, Y t - A t⟫ = -⟪ψ t, F t (Y t) - F t (A t)⟫) :
    HasDerivWithinAt (fun s => ⟪ψ s, Y s - A s⟫)
      (-⟪ψ t, F t (Y t) - Q t (F t (Y t))⟫) (Ici t) t := by
  have h := hψ.inner ℝ ((hY.deriv t ht).sub (hA.deriv t ht))
  refine h.congr_deriv ?_
  simp only [Pi.sub_apply]
  rw [hadj, inner_sub_right, inner_sub_right, inner_sub_right]
  ring

/-- For an orthogonal projector `P(t)` the driving term is the inner product of the *normal
components* of the dual solution and of the vector field:
`d/dt ⟪ψ, Y - A⟫ = -⟪(1 - P) ψ, (1 - P) F(Y)⟫`. -/
theorem hasDerivWithinAt_inner_sub_normal (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hA : ODESolution F A a b) {t : ℝ} (ht : t ∈ Ico a b) (hP : IsOrthProj (P t))
    (hψ : HasDerivWithinAt ψ (ψ' t) (Ici t) t)
    (hadj : ⟪ψ' t, Y t - A t⟫ = -⟪ψ t, F t (Y t) - F t (A t)⟫) :
    HasDerivWithinAt (fun s => ⟪ψ s, Y s - A s⟫)
      (-⟪(1 - P t) (ψ t), (1 - P t) (F t (Y t))⟫) (Ici t) t := by
  refine (hasDerivWithinAt_inner_sub hY hA ht hψ hadj).congr_deriv ?_
  congr 1
  rw [hP.compl.symm, hP.compl.idem]
  rfl

/-- The hypotheses on the dual solution along the whole interval. -/
structure IsDualAlong (F : ℝ → E → E) (Y A ψ ψ' : ℝ → E) (a b : ℝ) : Prop where
  cont : ContinuousOn ψ (Icc a b)
  deriv : ∀ t ∈ Ico a b, HasDerivWithinAt ψ (ψ' t) (Ici t) t
  adj : ∀ t ∈ Ico a b, ⟪ψ' t, Y t - A t⟫ = -⟪ψ t, F t (Y t) - F t (A t)⟫

/-- **Weak error bound.**  If `‖(1 - P(t)) F(t, Y)‖ ≤ ε` (the normal component of the field, the
quantity of the robust strong error bound) and `‖(1 - P(t)) ψ(t)‖ ≤ η` (the normal component of
the dual solution), then

  `|⟪ψ t, Y t - A t⟫ - ⟪ψ a, Y a - A a⟫| ≤ ε η (t - a)`.

Compared with the strong bound `‖Y - A‖ ≤ ε (e^{L(t-a)} - 1) / L` of
`ODESolution.dlra_norm_sub_le_gronwallBound`, the weak error carries the factor `η` instead of
`‖ψ‖` and *no Lipschitz constant and no exponential*: the growth of the full model is entirely
inside the dual solution.  The order in `ε` is one, and `weak_error_sharp` shows that this and the
constant `η` cannot be improved in general. -/
theorem abs_inner_sub_le (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hA : ODESolution F A a b) (hP : ∀ t ∈ Ico a b, IsOrthProj (P t))
    (hψ : IsDualAlong F Y A ψ ψ' a b) {ε η : ℝ}
    (hε : ∀ t ∈ Ico a b, ‖(1 - P t) (F t (Y t))‖ ≤ ε)
    (hη : ∀ t ∈ Ico a b, ‖(1 - P t) (ψ t)‖ ≤ η) :
    ∀ t ∈ Icc a b, |⟪ψ t, Y t - A t⟫ - ⟪ψ a, Y a - A a⟫| ≤ ε * η * (t - a) := by
  intro t ht
  have hcont : ContinuousOn (fun s => ⟪ψ s, Y s - A s⟫) (Icc a b) :=
    hψ.cont.inner (hY.cont.sub hA.cont)
  have hbound : ∀ s ∈ Ico a b,
      ‖-⟪(1 - P s) (ψ s), (1 - P s) (F s (Y s))⟫‖ ≤ ε * η := by
    intro s hs
    rw [norm_neg, Real.norm_eq_abs, mul_comm]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hη s hs) (hε s hs) (norm_nonneg _) ((norm_nonneg _).trans (hη s hs)))
  have := norm_image_sub_le_of_norm_deriv_right_le_segment hcont
    (fun s hs => hasDerivWithinAt_inner_sub_normal hY hA hs (hP s hs) (hψ.deriv s hs)
      (hψ.adj s hs)) hbound t ht
  simpa [Real.norm_eq_abs] using this

/-- **Weak error with exact initial data.**  If `Y a = A a`, then
`|⟪ψ b, Y b - A b⟫| ≤ ε η (b - a)`; with `ψ b = φ` this is the error of the observable
`⟪φ, ·⟫` at the final time. -/
theorem abs_inner_le_of_start (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hA : ODESolution F A a b) (hP : ∀ t ∈ Ico a b, IsOrthProj (P t))
    (hψ : IsDualAlong F Y A ψ ψ' a b) {ε η : ℝ}
    (hε : ∀ t ∈ Ico a b, ‖(1 - P t) (F t (Y t))‖ ≤ ε)
    (hη : ∀ t ∈ Ico a b, ‖(1 - P t) (ψ t)‖ ≤ η) (h0 : Y a = A a) (hab : a ≤ b) :
    |⟪ψ b, Y b - A b⟫| ≤ ε * η * (b - a) := by
  have := abs_inner_sub_le hY hA hP hψ hε hη b ⟨hab, le_rfl⟩
  simpa [h0] using this

/-- **Exact weak conservation for a tangent dual solution.**  If the dual solution is orthogonal
to the defect along the trajectory, `⟪ψ(t), (1 - P(t)) F(t, Y)⟫ = 0` (in particular if
`P(t) ψ(t) = ψ(t)`, `inner_sub_const_of_tangent`), then `⟪ψ t, Y t - A t⟫` is constant: the
observable `⟪ψ b, ·⟫` of the DLRA solution is exact when the initial data are.  This
generalises the conservation of linear invariants `ODESolution.galerkin_inner_const` /
`ODESolution.dlra_inner_const` (where `ψ ≡ c` is constant and `⟪c, F⟫ = 0`) to time-dependent
dual solutions and to observables that are not invariants of the full model. -/
theorem inner_sub_const (hY : ODESolution (fun t x => Q t (F t x)) Y a b)
    (hA : ODESolution F A a b) (hψ : IsDualAlong F Y A ψ ψ' a b)
    (hdef : ∀ t ∈ Ico a b, ⟪ψ t, F t (Y t) - Q t (F t (Y t))⟫ = 0) :
    ∀ t ∈ Icc a b, ⟪ψ t, Y t - A t⟫ = ⟪ψ a, Y a - A a⟫ := by
  refine constant_of_has_deriv_right_zero (hψ.cont.inner (hY.cont.sub hA.cont)) fun t ht => ?_
  have := hasDerivWithinAt_inner_sub hY hA ht (hψ.deriv t ht) (hψ.adj t ht)
  rwa [hdef t ht, neg_zero] at this

/-- Exact weak conservation when the dual solution lies in the tangent space along the DLRA
trajectory, `P(t) ψ(t) = ψ(t)`. -/
theorem inner_sub_const_of_tangent (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hA : ODESolution F A a b) (hP : ∀ t ∈ Ico a b, IsOrthProj (P t))
    (hψ : IsDualAlong F Y A ψ ψ' a b) (htan : ∀ t ∈ Ico a b, P t (ψ t) = ψ t) :
    ∀ t ∈ Icc a b, ⟪ψ t, Y t - A t⟫ = ⟪ψ a, Y a - A a⟫ := by
  refine inner_sub_const hY hA hψ fun t ht => ?_
  rw [← htan t ht]
  exact (hP t ht).inner_sub_self _ _


/-- **Observables lying in the basis ranges gain one power of the time, not of `ε`.**  If the
observable `φ` itself is tangent along the DLRA trajectory, `P(t) φ = φ` (e.g. a low-order
moment `u vᵀ` with `v` kept in the velocity basis, as in conservative DLRA), and the dual solution
`ψ` with `ψ(b) = φ` has `‖ψ'‖ ≤ Lψ` (for the linear model `Lψ = ‖ℒ*‖ sup ‖ψ‖`), then

  `|⟪φ, Y b - A b⟫| ≤ ε Lψ (b - a)² / 2`,

against `ε (b - a)` for the strong error: the normal component of the dual solution is
`‖(1 - P(t)) ψ(t)‖ = ‖(1 - P(t)) (ψ(t) - φ)‖ ≤ Lψ (b - t)`, so the defect is weighted by the time
to the final time.  The order in `ε` stays one (`weak_error_sharp` with `φ` normal does not apply
here, but the swap model `ℒ = e₁ e₂ᵀ + e₂ e₁ᵀ` on `ℝ²` with `P = e₁ e₁ᵀ`, `Y ≡ e₁`, `φ = e₁` has
the weak error `1 - cosh(b - a)`, of the size `ε (b - a)²/2` with `ε = 1`; this example is checked
by hand and not formalized). -/
theorem abs_inner_le_of_tangent_observable (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hA : ODESolution F A a b) (hP : ∀ t ∈ Ico a b, IsOrthProj (P t))
    (hψ : IsDualAlong F Y A ψ ψ' a b) {ε Lψ : ℝ} {φ : E}
    (hε : ∀ t ∈ Ico a b, ‖(1 - P t) (F t (Y t))‖ ≤ ε) (hφ : ∀ t ∈ Ico a b, P t φ = φ)
    (hψb : ψ b = φ) (hLψ : ∀ t ∈ Ico a b, ‖ψ' t‖ ≤ Lψ) (hL0 : 0 ≤ Lψ) (h0 : Y a = A a)
    (hab : a ≤ b) :
    |⟪φ, Y b - A b⟫| ≤ ε * Lψ * (b - a) ^ 2 / 2 := by
  have hcont : ContinuousOn (fun s => ⟪ψ s, Y s - A s⟫) (Icc a b) :=
    hψ.cont.inner (hY.cont.sub hA.cont)
  have hderiv : ∀ s ∈ Ico a b, HasDerivWithinAt (fun s => ⟪ψ s, Y s - A s⟫)
      (-⟪(1 - P s) (ψ s), (1 - P s) (F s (Y s))⟫) (Ici s) s := fun s hs =>
    hasDerivWithinAt_inner_sub_normal hY hA hs (hP s hs) (hψ.deriv s hs) (hψ.adj s hs)
  have hη : ∀ t ∈ Ico a b, ‖(1 - P t) (ψ t)‖ ≤ Lψ * (b - t) := by
    intro t ht
    have hφ' : (1 - P t) φ = 0 := by rw [sub_apply, one_apply_eq_self, hφ t ht, sub_self]
    have h1 : (1 - P t) (ψ t) = (1 - P t) (ψ t - φ) := by rw [map_sub, hφ', sub_zero]
    have h2 : ‖ψ b - ψ t‖ ≤ Lψ * (b - t) :=
      norm_image_sub_le_of_norm_deriv_right_le_segment (hψ.cont.mono (Icc_subset_Icc ht.1 le_rfl))
        (fun s hs => hψ.deriv s ⟨ht.1.trans hs.1, hs.2⟩)
        (fun s hs => hLψ s ⟨ht.1.trans hs.1, hs.2⟩) b ⟨ht.2.le, le_rfl⟩
    rw [h1]
    refine ((hP t ht).compl.norm_le _).trans ?_
    rwa [← hψb, norm_sub_rev]
  have hbound : ∀ t ∈ Ico a b,
      ‖-⟪(1 - P t) (ψ t), (1 - P t) (F t (Y t))⟫‖ ≤ ε * Lψ * (b - t) := by
    intro t ht
    rw [norm_neg, Real.norm_eq_abs]
    have hbt : 0 ≤ Lψ * (b - t) := mul_nonneg hL0 (by linarith [ht.2])
    calc |⟪(1 - P t) (ψ t), (1 - P t) (F t (Y t))⟫|
        ≤ ‖(1 - P t) (ψ t)‖ * ‖(1 - P t) (F t (Y t))‖ := abs_real_inner_le_norm _ _
      _ ≤ (Lψ * (b - t)) * ε := mul_le_mul (hη t ht) (hε t ht) (norm_nonneg _) hbt
      _ = ε * Lψ * (b - t) := by ring
  have hB : ∀ t, HasDerivAt (fun t => ε * Lψ * ((b - a) ^ 2 - (b - t) ^ 2) / 2)
      (ε * Lψ * (b - t)) t := by
    intro t
    have h := ((((hasDerivAt_id t).const_sub b).pow 2).const_sub ((b - a) ^ 2)).const_mul
      (ε * Lψ) |>.div_const 2
    convert h using 1
    · funext s
      simp only [Pi.pow_apply, id]
    · simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      ring
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont hderiv
    (B := fun t => ε * Lψ * ((b - a) ^ 2 - (b - t) ^ 2) / 2) (by simp [h0]) hB hbound
    ⟨hab, le_rfl⟩
  simp only [hψb, sub_self, zero_pow two_ne_zero, sub_zero, Real.norm_eq_abs] at hmain
  exact hmain

end Identity

/-! ### The dual solution of a linear model -/

section Linear

variable [CompleteSpace E] (ℒ : E →L[ℝ] E) (φ : E) (T : ℝ)

/-- The dual (adjoint) solution of the linear model `Ȧ = ℒ A + g(t)` with final value `φ` at
time `T`: `ψ(t) = exp((T - t) ℒ*) φ`, the solution of `ψ' = -ℒ* ψ`, `ψ(T) = φ`. -/
noncomputable def expDual (t : ℝ) : E :=
  NormedSpace.exp ((T - t) • ContinuousLinearMap.adjoint ℒ) φ

theorem expDual_final : expDual ℒ φ T T = φ := by
  simp [expDual]

theorem hasDerivAt_expDual (t : ℝ) :
    HasDerivAt (expDual ℒ φ T) (-(ContinuousLinearMap.adjoint ℒ (expDual ℒ φ T t))) t := by
  have h1 : HasDerivAt (fun s : ℝ => T - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub T
  have h2 := (hasDerivAt_exp_smul_const' (𝕂 := ℝ)
    (ContinuousLinearMap.adjoint ℒ) (T - t)).scomp t h1
  have h3 := h2.clm_apply (hasDerivAt_const t φ)
  unfold expDual
  simpa [mul_apply_eq_comp, neg_one_smul] using h3

theorem continuous_expDual : Continuous (expDual ℒ φ T) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_expDual ℒ φ T t).continuousAt

/-- For the affine model `F(t, x) = ℒ x + g(t)` the curve `expDual` is a dual solution along
*any* pair of curves `Y`, `A`: the adjoint equation does not depend on the trajectories. -/
theorem isDualAlong_expDual (g : ℝ → E) (Y A : ℝ → E) (a b : ℝ) :
    IsDualAlong (fun t x => ℒ x + g t) Y A (expDual ℒ φ T)
      (fun t => -(ContinuousLinearMap.adjoint ℒ (expDual ℒ φ T t))) a b where
  cont := (continuous_expDual ℒ φ T).continuousOn
  deriv t _ := (hasDerivAt_expDual ℒ φ T t).hasDerivWithinAt
  adj t _ := by
    rw [inner_neg_left, ContinuousLinearMap.adjoint_inner_left, add_sub_add_right_eq_sub, map_sub]

end Linear

/-! ### Sharpness: a constant normal field -/

section Sharp

variable {P₀ : E →L[ℝ] E} {Y₀ N : E} {a b : ℝ}

/-- For a constant field `F ≡ N` with `P₀ N = 0` (a *normal* direction at `Y₀`), the constant
curve `Y ≡ Y₀` solves the DLRA equation `Ẏ = P₀ F`: the low-rank approximation does not move. -/
theorem odeSolution_const_of_normal (hN : P₀ N = 0) :
    ODESolution (fun _ _ => P₀ N) (fun _ => Y₀) a b :=
  ⟨continuousOn_const, fun t _ => by rw [hN]; exact hasDerivWithinAt_const t _ Y₀⟩

/-- The full model `Ȧ = N` moves along the straight line `A(t) = Y₀ + (t - a) N`. -/
theorem odeSolution_affine (Y₀ N : E) (a b : ℝ) :
    ODESolution (fun _ _ => N) (fun t => Y₀ + (t - a) • N) a b :=
  ⟨by fun_prop, fun t _ => by
    simpa using (((hasDerivWithinAt_id t (Ici t)).sub_const a).smul_const N).const_add Y₀⟩

/-- A constant observable is a dual solution for a constant field. -/
theorem isDualAlong_const (φ : E) (Y A : ℝ → E) (a b : ℝ) :
    IsDualAlong (fun _ _ => N) Y A (fun _ => φ) (fun _ => 0) a b where
  cont := continuousOn_const
  deriv t _ := hasDerivWithinAt_const t _ φ
  adj _ _ := by simp

/-- **The weak error of a constant normal field is the full error.**  With `Y ≡ Y₀` and
`A(t) = Y₀ + (t - a) N`, `⟪φ, Y t - A t⟫ = -(t - a) ⟪φ, N⟫ = -(t - a) ⟪(1 - P₀) φ, N⟫` for an
orthogonal projector `P₀` with `P₀ N = 0`: only the normal component of the observable sees the
error, and it sees all of it. -/
theorem inner_sub_affine (hP : IsOrthProj P₀) (hN : P₀ N = 0) (φ : E) (t : ℝ) :
    ⟪φ, Y₀ - (Y₀ + (t - a) • N)⟫ = -((t - a) * ⟪(1 - P₀) φ, N⟫) := by
  have h : ⟪(1 - P₀) φ, N⟫ = ⟪φ, N⟫ := by
    rw [sub_apply, one_apply_eq_self, inner_sub_left, hP.symm, hN, inner_zero_right, sub_zero]
  rw [h]
  simp [inner_smul_right]

/-- **Sharpness of the weak error bound.**  Let `P₀` be an orthogonal projector (the tangent
projector at `Y₀`), `φ` any observable and `c ≥ 0`.  For the constant field
`N = c (1 - P₀) φ`, whose normal component has size `ε = c ‖(1 - P₀) φ‖`, the DLRA solution is
`Y ≡ Y₀` and the full solution is `A(t) = Y₀ + (t - a) N`, and the weak error is

  `|⟪φ, Y b - A b⟫| = ε ‖(1 - P₀) φ‖ (b - a)`,

exactly the bound `ε η (b - a)` of `abs_inner_le_of_start` with `η = ‖(1 - P₀) φ‖`.  So the
weak error of DLRA is of *first* order in `ε` for every observable with a nonzero normal
component, with the sharp constant `η`; a gain of order `ε²` is impossible without a condition on
the normal component of the dual solution (see `abs_inner_le_of_tangent_curvature`). -/
theorem weak_error_sharp (hP : IsOrthProj P₀) (φ : E) {c : ℝ} (hc : 0 ≤ c) (hab : a ≤ b) :
    ODESolution (fun _ _ => P₀ (c • (1 - P₀) φ)) (fun _ => Y₀) a b ∧
    ODESolution (fun _ _ => c • (1 - P₀) φ) (fun t => Y₀ + (t - a) • c • (1 - P₀) φ) a b ∧
    ‖(1 - P₀) (c • (1 - P₀) φ)‖ = c * ‖(1 - P₀) φ‖ ∧
    |⟪φ, Y₀ - (Y₀ + (b - a) • c • (1 - P₀) φ)⟫| = (c * ‖(1 - P₀) φ‖) * ‖(1 - P₀) φ‖ * (b - a) ∧
    ‖Y₀ - (Y₀ + (b - a) • c • (1 - P₀) φ)‖ = (c * ‖(1 - P₀) φ‖) * (b - a) := by
  have hN : P₀ (c • (1 - P₀) φ) = 0 := by
    rw [map_smul, sub_apply, one_apply_eq_self, map_sub, hP.idem, sub_self, smul_zero]
  have hcompl : (1 - P₀) ((1 - P₀) φ) = (1 - P₀) φ := hP.compl.idem φ
  refine ⟨odeSolution_const_of_normal hN, odeSolution_affine _ _ a b, ?_, ?_, ?_⟩
  · rw [map_smul, hcompl, norm_smul, Real.norm_of_nonneg hc]
  · rw [inner_sub_affine hP hN, abs_neg, abs_mul, abs_of_nonneg (by linarith),
      inner_smul_right, real_inner_self_eq_norm_sq, abs_mul, abs_of_nonneg hc, abs_of_nonneg
      (by positivity)]
    ring
  · rw [sub_add_cancel_left, norm_neg, norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
      Real.norm_of_nonneg hc]
    ring

end Sharp

/-! ### Superconvergence through curvature -/

section Curvature

variable {P PX : ℝ → E →L[ℝ] E} {F : ℝ → E → E} {Y A X ψ ψ' : ℝ → E} {a b : ℝ}

/-- If `ψ` is tangent at a nearby point `x` (`PX ψ = ψ`) and the projectors satisfy the curvature
bound `‖(P - PX) z‖ ≤ γ ‖y - x‖ ‖z‖` (Koch–Lubich 2007, Lemma 4.2; `koch_lubich_tangent_frob` on
matrices), then the normal component of `ψ` at `y` is of the size of the distance:
`‖(1 - P) ψ‖ ≤ γ ‖y - x‖ ‖ψ‖`. -/
theorem norm_normal_le_of_curvature {P PX : E →L[ℝ] E} {ψ y x : E} {γ : ℝ}
    (hψ : PX ψ = ψ) (hcurv : ∀ z, ‖(P - PX) z‖ ≤ γ * ‖y - x‖ * ‖z‖) :
    ‖(1 - P) ψ‖ ≤ γ * ‖y - x‖ * ‖ψ‖ := by
  have h : (1 - P) ψ = -((P - PX) ψ) := by
    simp only [sub_apply, one_apply_eq_self, hψ]
    abel
  rw [h, norm_neg]
  exact hcurv ψ

/-- **Second-order weak error for observables tangent along a nearby low-rank curve.**  Let `X`
be a curve on the manifold with tangent projectors `PX(t)` such that the dual solution is tangent
along `X`, `PX(t) ψ(t) = ψ(t)`, let the curvature bound
`‖(P(t) - PX(t)) z‖ ≤ γ ‖Y t - X t‖ ‖z‖` hold, and let `‖Y - X‖ ≤ d`, `‖ψ‖ ≤ M` on the interval.
Then `|⟪ψ b, Y b - A b⟫| ≤ ε (γ d M) (b - a)`: the weak error is the strong error `ε (b - a)`
times the *distance to the curve on which the observable is tangent*.  With `X = A` and the
robust strong bound `d = O(ε)` this is of order `ε²` (`abs_inner_le_sq_of_tangent`), the
superconvergence asked for in the open problem; by `weak_error_sharp` it needs the tangency
hypothesis. -/
theorem abs_inner_le_of_tangent_curvature (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hA : ODESolution F A a b) (hP : ∀ t ∈ Ico a b, IsOrthProj (P t))
    (hψ : IsDualAlong F Y A ψ ψ' a b) {ε γ d M : ℝ}
    (hε : ∀ t ∈ Ico a b, ‖(1 - P t) (F t (Y t))‖ ≤ ε)
    (hX : ∀ t ∈ Ico a b, PX t (ψ t) = ψ t)
    (hcurv : ∀ t ∈ Ico a b, ∀ z, ‖(P t - PX t) z‖ ≤ γ * ‖Y t - X t‖ * ‖z‖)
    (hd : ∀ t ∈ Ico a b, ‖Y t - X t‖ ≤ d) (hM : ∀ t ∈ Ico a b, ‖ψ t‖ ≤ M) (hγ : 0 ≤ γ)
    (hd0 : 0 ≤ d) (h0 : Y a = A a) (hab : a ≤ b) :
    |⟪ψ b, Y b - A b⟫| ≤ ε * (γ * d * M) * (b - a) := by
  refine abs_inner_le_of_start hY hA hP hψ hε (fun t ht => ?_) h0 hab
  calc ‖(1 - P t) (ψ t)‖ ≤ γ * ‖Y t - X t‖ * ‖ψ t‖ :=
        norm_normal_le_of_curvature (hX t ht) (hcurv t ht)
    _ ≤ γ * d * M :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hd t ht) hγ) (hM t ht) (norm_nonneg _)
          (by positivity)

/-- **Weak error of order `ε²`.**  If `F` is `L`-Lipschitz, `Y a = A a`, the dual solution is
tangent along the exact solution (`PA(t) ψ(t) = ψ(t)`, with `PA(t)` the tangent projector at
`A(t)`, which presupposes that `A` stays on the manifold), the curvature bound
`‖(P(t) - PA(t)) z‖ ≤ γ ‖Y t - A t‖ ‖z‖` holds and `‖ψ‖ ≤ M`, then

  `|⟪ψ b, Y b - A b⟫| ≤ γ M e^{L(b-a)} (b - a)² ε²`.

The strong error is only `O(ε)` (`ODESolution.dlra_norm_sub_le_gronwallBound`): this is the
Aubin–Nitsche-type gain, and the price is the curvature constant `γ ~ 1/σ_r`. -/
theorem abs_inner_le_sq_of_tangent {L : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hY : ODESolution (fun t x => P t (F t x)) Y a b) (hA : ODESolution F A a b)
    (hP : ∀ t ∈ Ico a b, IsOrthProj (P t)) (hψ : IsDualAlong F Y A ψ ψ' a b) {ε γ M : ℝ}
    (hε0 : 0 ≤ ε) (hε : ∀ t ∈ Ico a b, ‖(1 - P t) (F t (Y t))‖ ≤ ε)
    (hX : ∀ t ∈ Ico a b, PX t (ψ t) = ψ t)
    (hcurv : ∀ t ∈ Ico a b, ∀ z, ‖(P t - PX t) z‖ ≤ γ * ‖Y t - A t‖ * ‖z‖)
    (hM : ∀ t ∈ Ico a b, ‖ψ t‖ ≤ M) (hγ : 0 ≤ γ) (h0 : Y a = A a) (hab : a ≤ b) :
    |⟪ψ b, Y b - A b⟫| ≤ γ * M * Real.exp (L * (b - a)) * (b - a) ^ 2 * ε ^ 2 := by
  have hstrong := ODESolution.dlra_norm_sub_le_gronwallBound hF hL hA hY hε (δ := 0) (by simp [h0])
  have hd : ∀ t ∈ Ico a b, ‖Y t - A t‖ ≤ Real.exp (L * (b - a)) * (ε * (b - a)) := by
    intro t ht
    have h1 := hstrong t (Ico_subset_Icc_self ht)
    have h2 := gronwallBound_le_exp_mul (δ := 0) (x := t - a) hL hε0
    have h3 : Real.exp (L * (t - a)) ≤ Real.exp (L * (b - a)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hL)
    have h4 : ε * (t - a) ≤ ε * (b - a) := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hε0
    have h5 : 0 ≤ ε * (t - a) := mul_nonneg hε0 (by linarith [ht.1])
    calc ‖Y t - A t‖ ≤ Real.exp (L * (t - a)) * (0 + ε * (t - a)) := h1.trans h2
      _ ≤ Real.exp (L * (b - a)) * (ε * (b - a)) := by
          rw [zero_add]
          exact mul_le_mul h3 h4 h5 (Real.exp_pos _).le
  have := abs_inner_le_of_tangent_curvature hY hA hP hψ hε hX hcurv hd hM hγ
    (by positivity) h0 hab
  calc |⟪ψ b, Y b - A b⟫| ≤ ε * (γ * (Real.exp (L * (b - a)) * (ε * (b - a))) * M) * (b - a) :=
        this
    _ = γ * M * Real.exp (L * (b - a)) * (b - a) ^ 2 * ε ^ 2 := by ring

end Curvature

/-! ### The BUG integrator -/

section BUG

variable {F : ℝ → E → E} {ε ϑ : ℝ} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ Y₁ : E}
  {YK YL YS A ψ ψ' : ℝ → E}

/-- **Weak error of one (augmented, rank-adaptive) BUG step.**  The S-step is a Galerkin ODE with
the *constant* augmented projector `P̂ = P₁ Q₁`, started at `Y₀` (`augP`, `augQ`), followed by a
truncation of size `ϑ` inside `range P̂`.  If the defect of the S-step is `‖(1 - P̂) F(t, Ŷ)‖ ≤ εS`
and the dual solution has normal component `‖(1 - P̂) ψ‖ ≤ η` *with respect to the augmented
bases*, then

  `|⟪ψ t₁, Y₁ - A t₁⟫ - ⟪ψ t₀, Y₀ - A t₀⟫| ≤ εS η (t₁ - t₀) + ‖P̂ ψ(t₁)‖ ϑ`.

So an observable whose dual solution is captured by the augmented bases (`η = 0`) is exact up to
the truncation, and the truncation error is only seen by the tangential part of `ψ`.  The
hypothesis `P̂ Y₁ = Y₁` holds for the SVD truncation of `Ŷ₁ = Û Ŝ V̂ᵀ`. -/
theorem IsRankAdaptiveBUGStep.weak_error_le
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hA : ODESolution F A t₀ t₁) (hψ : IsDualAlong F YS A ψ ψ' t₀ t₁) {εS η : ℝ}
    (hεS : ∀ t ∈ Ico t₀ t₁, ‖(1 - P₁ * Q₁) (F t (YS t))‖ ≤ εS)
    (hη : ∀ t ∈ Ico t₀ t₁, ‖(1 - P₁ * Q₁) (ψ t)‖ ≤ η) (hY₁ : P₁ (Q₁ Y₁) = Y₁) (h01 : t₀ ≤ t₁) :
    |⟪ψ t₁, Y₁ - A t₁⟫ - ⟪ψ t₀, Y₀ - A t₀⟫| ≤
      εS * η * (t₁ - t₀) + ‖P₁ (Q₁ (ψ t₁))‖ * ϑ := by
  have hPQ : IsOrthProj (P₁ * Q₁) := hs.projP₁.mul hs.projQ₁ hs.comm₁
  have hS : ODESolution (fun t x => (fun _ => P₁ * Q₁) t (F t x)) YS t₀ t₁ := hs.sSol
  have h1 := abs_inner_sub_le hS hA (fun _ _ => hPQ) hψ hεS hη t₁ ⟨h01, le_rfl⟩
  have hYS0 : YS t₀ = Y₀ := by rw [hs.sStart, hs.augQ, hs.augP]
  have hYS1 : (P₁ * Q₁) (YS t₁) = YS t₁ :=
    hs.sSol.fixed_of_fixed_field (P := P₁ * Q₁) (fun t x => hPQ.idem (F t x))
      (by rw [hs.sStart]; exact hPQ.idem Y₀) t₁ ⟨h01, le_rfl⟩
  have hD : (P₁ * Q₁) (Y₁ - YS t₁) = Y₁ - YS t₁ := by
    rw [map_sub, hYS1]
    exact congrArg (· - YS t₁) hY₁
  have hinner : ⟪ψ t₁, Y₁ - YS t₁⟫ = ⟪P₁ (Q₁ (ψ t₁)), Y₁ - YS t₁⟫ := by
    have h := hPQ.symm (ψ t₁) (Y₁ - YS t₁)
    rw [hD] at h
    exact h.symm
  have h2 : |⟪P₁ (Q₁ (ψ t₁)), Y₁ - YS t₁⟫| ≤ ‖P₁ (Q₁ (ψ t₁))‖ * ϑ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hs.trunc (norm_nonneg _))
  have hsplit : Y₁ - A t₁ = (YS t₁ - A t₁) + (Y₁ - YS t₁) := by abel
  rw [hsplit, inner_add_right, hinner, ← hYS0]
  calc |⟪ψ t₁, YS t₁ - A t₁⟫ + ⟪P₁ (Q₁ (ψ t₁)), Y₁ - YS t₁⟫ - ⟪ψ t₀, YS t₀ - A t₀⟫|
      = |(⟪ψ t₁, YS t₁ - A t₁⟫ - ⟪ψ t₀, YS t₀ - A t₀⟫) + ⟪P₁ (Q₁ (ψ t₁)), Y₁ - YS t₁⟫| := by
        ring_nf
    _ ≤ |⟪ψ t₁, YS t₁ - A t₁⟫ - ⟪ψ t₀, YS t₀ - A t₀⟫| + |⟪P₁ (Q₁ (ψ t₁)), Y₁ - YS t₁⟫| :=
        abs_add_le _ _
    _ ≤ εS * η * (t₁ - t₀) + ‖P₁ (Q₁ (ψ t₁))‖ * ϑ := add_le_add h1 h2

/-- A curve is a solution of an ODE whose field vanishes along it if it is constant. -/
theorem odeSolution_const_of_eq_zero {f : ℝ → E → E} (hf : ∀ t x, f t x = 0) (Y₀ : E)
    (a b : ℝ) : ODESolution f (fun _ => Y₀) a b :=
  ⟨continuousOn_const, fun t _ => by rw [hf]; exact hasDerivWithinAt_const t _ Y₀⟩

variable {N : E}

/-- **Every DLRA integrator is stationary at a normal fixed point.**  For the constant field
`F ≡ N` with `P₀ N = 0`, `Q₀ N = 0` (`N` normal at `Y₀ = U₀ S₀ V₀ᵀ`) the K-, L- and S-steps of
the augmented BUG integrator and the K-, S-, L-steps of the projector-splitting (KSL) integrator
do not move: all substep trajectories are `≡ Y₀`, the bases are not enlarged, and the step
returns `Y₁ = Y₀` with normal-component bound `ε = ‖N‖` and truncation `ϑ = 0`.  Together with
`inner_sub_affine`, the weak error of one step is exactly `-(t₁ - t₀) ⟪(1 - P₀) φ, N⟫` for both
integrators, so `weak_error_sharp` applies verbatim to BUG and KSL: no integrator can have a
weak error of order `ε²` without a condition on the normal component of the observable. -/
theorem stationary_of_normal (hP₀ : IsOrthProj P₀) (hQ₀ : IsOrthProj Q₀)
    (hc : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x)) (hY₀ : P₀ Y₀ = Y₀) (hY₀' : Q₀ Y₀ = Y₀) (hNP : P₀ N = 0)
    (hNQ : Q₀ N = 0) :
    IsRankAdaptiveBUGStep (fun _ _ => N) ‖N‖ 0 P₀ Q₀ P₀ Q₀ t₀ t₁ Y₀ (fun _ => Y₀)
        (fun _ => Y₀) (fun _ => Y₀) Y₀ ∧
      IsKSLStep (fun _ _ => N) ‖N‖ P₀ Q₀ t₀ t₁ Y₀ (fun _ => Y₀) (fun _ => Y₀) (fun _ => Y₀) := by
  have hnorm : ‖(1 - P₀) ((1 - Q₀) N)‖ = ‖N‖ := by
    simp [sub_apply, hNP, hNQ]
  refine ⟨?_, ?_⟩
  · exact
      { projP₀ := hP₀
        projQ₀ := hQ₀
        projP₁ := hP₀
        projQ₁ := hQ₀
        comm₁ := hc
        kSol := odeSolution_const_of_eq_zero (fun _ _ => hNQ) Y₀ t₀ t₁
        kStart := rfl
        kCap := hY₀
        kNormal := fun _ _ => hnorm.le
        lSol := odeSolution_const_of_eq_zero (fun _ _ => hNP) Y₀ t₀ t₁
        lStart := rfl
        lCap := hY₀'
        lNormal := fun _ _ => by simp [sub_apply, hNP, hNQ]
        sSol := odeSolution_const_of_eq_zero (fun _ _ => by simp [hNQ]) Y₀ t₀ t₁
        sStart := by rw [hY₀', hY₀]
        augP := hY₀
        augQ := hY₀'
        trunc := by simp }
  · exact
      { projP₁ := hP₀
        projQ₀ := hQ₀
        kSol := odeSolution_const_of_eq_zero (fun _ _ => hNQ) Y₀ t₀ t₁
        kStart := rfl
        kCap := hY₀
        kNormal := fun _ _ => hnorm.le
        sSol := odeSolution_const_of_eq_zero (fun _ _ => by simp [hNQ]) Y₀ t₀ t₁
        sStart := rfl
        lSol := odeSolution_const_of_eq_zero (fun _ _ => hNP) Y₀ t₀ t₁
        lStart := rfl }

end BUG

/-! ### Matrices -/

section Matrices

open Matrix
open scoped LeanDLRA.Frobenius

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n]
  [DecidableEq k]

omit [DecidableEq k] in
/-- The normal part of `Z` at `Y = U S Vᵀ`: `Z - P(Y) Z = (I - U Uᵀ) Z (I - V Vᵀ)`. -/
theorem one_sub_tangentProj_apply (U : Matrix m k ℝ) (V : Matrix n k ℝ) (Z : Matrix m n ℝ) :
    (1 - tangentProj U V) Z = (1 - U * Uᵀ) * Z * (1 - V * Vᵀ) := by
  rw [sub_apply, one_apply_eq_self]
  exact (eq_sub_of_add_eq' (tangentProj_add_normal U V Z)).symm

/-- **Sharpness on matrices.**  At `Y₀ = U S Vᵀ` with orthonormal `U`, `V`, for every observable
`φ` and `c ≥ 0`, the constant field `N = c (I - U Uᵀ) φ (I - V Vᵀ)` is normal, the DLRA solution
`Ẏ = P(Y) N` is `Y ≡ Y₀`, the full solution is `A(t) = Y₀ + (t - a) N`, and

  `|⟪φ, Y b - A b⟫| = ε ‖(I - U Uᵀ) φ (I - V Vᵀ)‖ (b - a)`  with  `ε = ‖N‖ = ‖(1 - P(Y₀)) N‖`,

the weak error bound `abs_inner_le_of_start` with equality.  (`exists_nonzero_normal` gives a
`2 × 2`, rank-one instance with `(I - U Uᵀ) φ (I - V Vᵀ) ≠ 0`.) -/
theorem weak_error_sharp_matrix {U : Matrix m k ℝ} {V : Matrix n k ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (Y₀ φ : Matrix m n ℝ) {c : ℝ} (hc : 0 ≤ c) {a b : ℝ} (hab : a ≤ b)
    {N : Matrix m n ℝ} (hN : N = c • ((1 - U * Uᵀ) * φ * (1 - V * Vᵀ))) :
    ODESolution (fun _ _ => tangentProj U V N) (fun _ => Y₀) a b ∧
    ODESolution (fun _ _ => N) (fun t => Y₀ + (t - a) • N) a b ∧
    ‖(1 - tangentProj U V) N‖ = c * ‖(1 - U * Uᵀ) * φ * (1 - V * Vᵀ)‖ ∧
    |⟪φ, Y₀ - (Y₀ + (b - a) • N)⟫| =
      (c * ‖(1 - U * Uᵀ) * φ * (1 - V * Vᵀ)‖) * ‖(1 - U * Uᵀ) * φ * (1 - V * Vᵀ)‖ * (b - a) ∧
    ‖Y₀ - (Y₀ + (b - a) • N)‖ = (c * ‖(1 - U * Uᵀ) * φ * (1 - V * Vᵀ)‖) * (b - a) := by
  have h := weak_error_sharp (P₀ := tangentProj U V) (Y₀ := Y₀) (isOrthProj_tangentProj hU hV)
    φ hc hab
  rw [one_sub_tangentProj_apply, ← hN] at h
  exact h

/-- A `2 × 2`, rank-one instance of `weak_error_sharp_matrix` with a nonzero normal component:
`U = V = e₁`, `φ = e₂ e₂ᵀ`. -/
theorem exists_nonzero_normal :
    ∃ (U V : Matrix (Fin 2) (Fin 1) ℝ) (φ : Matrix (Fin 2) (Fin 2) ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ (1 - U * Uᵀ) * φ * (1 - V * Vᵀ) ≠ 0 := by
  have h1 : (1 - (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) * (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ) =
      !![0, 0; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.vecMul, dotProduct,
        Function.swap, Matrix.vecHead, Matrix.vecTail]
  refine ⟨!![1; 0], !![1; 0], !![0, 0; 0, 1], ?_, ?_, ?_⟩
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · rw [h1]
    intro h0
    have := congrFun (congrFun h0 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this

omit [DecidableEq m] [DecidableEq n] in
/-- **The curvature gain on matrices.**  If the observable (dual solution) `ψ` is tangent at
`X = U S Vᵀ` with `σ_min(S) ≥ ρ > 0`, then at `Y = U' S' V'ᵀ` its normal component is bounded by
`‖(1 - P(Y)) ψ‖ ≤ 2 ρ⁻¹ ‖Y - X‖ ‖ψ‖` (`koch_lubich_tangent_frob`), the factor `η` of
`abs_inner_sub_le` with `γ = 2/ρ` in `abs_inner_le_of_tangent_curvature`. -/
theorem norm_normal_le_of_tangent_matrix {U U' : Matrix m k ℝ} {V V' : Matrix n k ℝ}
    {S S' : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) {ψ : Matrix m n ℝ}
    (hψ : tangentProj U V ψ = ψ) :
    ‖(1 - tangentProj U' V') ψ‖ ≤ 2 * ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖ψ‖ := by
  refine norm_normal_le_of_curvature (PX := tangentProj U V) hψ fun z => ?_
  have h := Curvature.koch_lubich_tangent_frob (S' := S') hρ hU hV hU' hV' hS z
  rwa [Curvature.tangentProjMat_eq_tangentProj, Curvature.tangentProjMat_eq_tangentProj] at h

end Matrices

end LeanDLRA.Novel.OpOT60
