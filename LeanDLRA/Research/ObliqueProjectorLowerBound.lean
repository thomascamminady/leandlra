import LeanDLRA.Research.RankStatePrice

/-!
# Oblique tangent projectors on `2 × 2` rank-one states: error `2π k ε` at normal component `ε`

This file is about `2 × 2` matrices, rank one, and data `A(t)` given as a curve (the right-hand
side does not depend on the state: Lipschitz constant `L = 0`). A method of the form
`Ẏ = Π(Y) Ȧ` with `Π(Y)` a linear map that is the identity on the tangent space `T_Y M_1` and
maps into it (an oblique projector onto `T_Y M_1`; the projected equation of dynamical low-rank
approximation is the orthogonal one) is exact on data of rank one. The hypotheses are imposed
only along the circle of states `Y(θ) = u(θ) e₁ᵀ`, `u(θ) = (cos θ, sin θ)`, together with the
continuity of `θ ↦ Π(Y(θ)) N(θ)`, where `N(θ) = u⊥(θ) e₂ᵀ` is the unit normal. For every such
method and all `ε ≥ 0`, `k : ℕ` this file gives data `A` on which the state of the method turns
by the angle `2π k`, the error starts as `A(0) - Y(0) = ± ε N`, its normal component
`⟪N(Y), A - Y⟫` stays equal to `± ε`, and the error at the end is at least `2π k ε`.

Here `ε` is the normal component of the error, not the distance of `A` to `M_1`. For a general
`Π` nothing is proved about `dist(A(t), M_1)`: the data need not stay close to `M_1`, and when
`dist(A(2π k), M_1) ≥ 2π k ε` the bound holds for every matrix of rank one and says nothing about
the method. If `Π(Y(θ)) N(θ)` has a zero first column for every `θ` (the kernel direction `q`
below lies in `span {N, B}`), as for the family `Π_κ` at the end of this file, the data stay
within `ε` of `M_1` at all times, and this is part of the statement. In that subclass `ε` bounds
the best-approximation error and the method loses at least `ε` per radian of turning, as the
projected equation does on the family of `LeanDLRA/Research/RankStatePrice.lean` (where also
`dist(A, M_1) ≤ ε`). For other `Π` no relation between the normal component and `dist(A, M_1)`
is proved here.

The data are explicit. Write `B(θ) = u(θ) e₂ᵀ`, `q(θ) = N(θ) - Π(Y(θ)) N(θ)` (the kernel of the
projector) and `f(θ) = ⟪B(θ), q(θ)⟫`. For a direction `s = ± 1` and a start angle `θ₀` the
state is `Y(t) = Y(θ₀ + s t)` and the data are `A = Y + D` with

    D(t) = β(t) B(θ₀ + s t) + s ε N(θ₀ + s t) + ∫₀ᵗ s β (q - f B - N)(θ₀ + s r) dr,
    β(t) = ε ∫₀ᵗ exp(G(t) - G(r)) dr,   G(t) = ∫_{θ₀}^{θ₀ + s t} f.

Then `Ȧ - Ẏ = s β q` lies in the kernel of `Π(Y)`, so `Y` solves `Ẏ = Π(Y) Ȧ`; the error has the
tangential component `⟪B, D⟫ = β` and the normal component `s ε`. With `s` the sign of
`∫₀^{2π} f` and `θ₀` a maximum of the periodic part of `θ ↦ ∫₀^θ f`, the exponent
`G(2πk) - G(r)` is nonnegative for `0 ≤ r ≤ 2πk`, hence `β(2πk) ≥ 2π k ε`. The second column
of `q - f B - N` vanishes for every method of the class; if `q` also has a zero first column,
then `q - f B - N = 0`, the integral term is zero and `A - (Y + β B) = s ε N`, where `Y + β B`
has rank at most one, so `dist(A, M_1) ≤ ε`.

## Main results

* `ObliqueProjectorLowerBound.exists_data_two_pi_mul_le_norm_sub`: the data for every method of
  the class, and `dist(A, M_1) ≤ ε` in the subclass.
* `ObliqueProjectorLowerBoundExample.hasDerivAt_advData`, `proj_advDeriv`,
  `inner_loopNormal_advData_sub`, `inner_loopSide_advData_sub`, `mul_le_tanErr`,
  `exists_start_gain_le`, `distLR_advData_le`: the steps.
* `ObliqueProjectorLowerBoundExample.tangentObliqueProj`: the methods
  `Π_κ(Y) a = a - ⟪N, a⟫ (N + κ B)`, which satisfy the hypotheses and lie in the subclass (on the
  circle, `κ = 0` is the orthogonal projection of the projected equation).
-/

open Set MeasureTheory Real
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.ObliqueProjectorLowerBoundExample

open LeanDLRA.RankStatePriceExample

/-! ### The circle of rank-one states and its frame -/

/-- The unit normal `u⊥(θ) e₂ᵀ` of `M_1` at `u(θ) e₁ᵀ`. -/
noncomputable def loopNormal (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -Real.sin θ; 0, Real.cos θ]

/-- The tangent direction `u(θ) e₂ᵀ` at `u(θ) e₁ᵀ`. -/
noncomputable def loopSide (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, Real.cos θ; 0, Real.sin θ]

lemma inner_loopNormal (θ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    ⟪loopNormal θ, X⟫ = -Real.sin θ * X 0 1 + Real.cos θ * X 1 1 := by
  simp [Frobenius.inner_def, loopNormal, Fin.sum_univ_two]

lemma inner_loopSide (θ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    ⟪loopSide θ, X⟫ = Real.cos θ * X 0 1 + Real.sin θ * X 1 1 := by
  simp [Frobenius.inner_def, loopSide, Fin.sum_univ_two]

lemma inner_loopNormal_self (θ : ℝ) : ⟪loopNormal θ, loopNormal θ⟫ = 1 := by
  rw [inner_loopNormal]
  simp only [loopNormal, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  nlinarith [Real.sin_sq_add_cos_sq θ]

lemma inner_loopSide_self (θ : ℝ) : ⟪loopSide θ, loopSide θ⟫ = 1 := by
  rw [inner_loopSide]
  simp only [loopSide, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  nlinarith [Real.sin_sq_add_cos_sq θ]

lemma inner_loopNormal_loopSide (θ : ℝ) : ⟪loopNormal θ, loopSide θ⟫ = 0 := by
  rw [inner_loopNormal]
  simp only [loopSide, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

lemma inner_loopSide_loopNormal (θ : ℝ) : ⟪loopSide θ, loopNormal θ⟫ = 0 := by
  rw [real_inner_comm, inner_loopNormal_loopSide]

/-- The velocity `u⊥ e₁ᵀ` of the state is tangent. -/
lemma inner_loopNormal_involuteStateDeriv (θ : ℝ) :
    ⟪loopNormal θ, involuteStateDeriv θ⟫ = 0 := by
  rw [inner_loopNormal]
  simp [involuteStateDeriv]

lemma norm_loopSide (θ : ℝ) : ‖loopSide θ‖ = 1 := by
  have h := inner_loopSide_self θ
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (loopSide θ)]

lemma norm_loopNormal (θ : ℝ) : ‖loopNormal θ‖ = 1 := by
  have h := inner_loopNormal_self θ
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (loopNormal θ)]

/-- `Y(θ) + β B(θ) = u(θ) (e₁ + β e₂)ᵀ` has rank at most one. -/
lemma rank_involuteState_add_smul_loopSide_le (θ β : ℝ) :
    (involuteState θ + β • loopSide θ).rank ≤ 1 := by
  have e : involuteState θ + β • loopSide θ =
      Matrix.vecMulVec ![Real.cos θ, Real.sin θ] ![1, β] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [involuteState, loopSide, Matrix.vecMulVec_apply, mul_comm]
  rw [e]
  exact Matrix.rank_vecMulVec_le _ _

/-- A matrix orthogonal to `B(φ)` and `N(φ)` has a zero second column. -/
lemma col_eq_zero_of_inner {φ : ℝ} {X : Matrix (Fin 2) (Fin 2) ℝ}
    (h1 : ⟪loopSide φ, X⟫ = 0) (h2 : ⟪loopNormal φ, X⟫ = 0) : X 0 1 = 0 ∧ X 1 1 = 0 := by
  rw [inner_loopSide] at h1
  rw [inner_loopNormal] at h2
  have h3 := Real.sin_sq_add_cos_sq φ
  constructor
  · linear_combination Real.cos φ * h1 - Real.sin φ * h2 - X 0 1 * h3
  · linear_combination Real.sin φ * h1 + Real.cos φ * h2 - X 1 1 * h3

theorem hasDerivAt_loopNormal (θ : ℝ) : HasDerivAt loopNormal (-loopSide θ) θ := by
  have e : loopNormal = fun s : ℝ =>
      (-Real.sin s) • (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
        + Real.cos s • (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
    funext s
    ext i j
    fin_cases i <;> fin_cases j <;> simp [loopNormal]
  have h := ((Real.hasDerivAt_sin θ).neg.smul_const
    (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)).add
    ((Real.hasDerivAt_cos θ).smul_const (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ))
  rw [e]
  refine h.congr_deriv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [loopSide]

theorem hasDerivAt_loopSide (θ : ℝ) : HasDerivAt loopSide (loopNormal θ) θ := by
  have e : loopSide = fun s : ℝ =>
      Real.cos s • (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
        + Real.sin s • (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
    funext s
    ext i j
    fin_cases i <;> fin_cases j <;> simp [loopSide]
  have h := ((Real.hasDerivAt_cos θ).smul_const
    (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)).add
    ((Real.hasDerivAt_sin θ).smul_const (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ))
  rw [e]
  refine h.congr_deriv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [loopNormal]

lemma continuous_loopNormal : Continuous loopNormal :=
  continuous_iff_continuousAt.2 fun θ => (hasDerivAt_loopNormal θ).continuousAt

lemma continuous_loopSide : Continuous loopSide :=
  continuous_iff_continuousAt.2 fun θ => (hasDerivAt_loopSide θ).continuousAt

lemma loopNormal_add_two_pi (θ : ℝ) : loopNormal (θ + 2 * π) = loopNormal θ := by
  simp [loopNormal, Real.sin_add_two_pi, Real.cos_add_two_pi]

lemma loopSide_add_two_pi (θ : ℝ) : loopSide (θ + 2 * π) = loopSide θ := by
  simp [loopSide, Real.sin_add_two_pi, Real.cos_add_two_pi]

lemma involuteState_add_two_pi (θ : ℝ) : involuteState (θ + 2 * π) = involuteState θ := by
  simp [involuteState, Real.sin_add_two_pi, Real.cos_add_two_pi]

lemma hasDerivAt_affine (θ₀ s t : ℝ) : HasDerivAt (fun t => θ₀ + s * t) s t := by
  simpa using ((hasDerivAt_id t).const_mul s).const_add θ₀

/-! ### The data for a given method -/

section Method

variable (proj : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ)

/-- The kernel direction `q(θ) = N(θ) - Π(Y(θ)) N(θ)` of the projector at `Y(θ) = u(θ) e₁ᵀ`. -/
noncomputable def kerDir (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  loopNormal θ - proj (involuteState θ) (loopNormal θ)

/-- The rate `f(θ) = ⟪B(θ), q(θ)⟫` at which the method feeds the tangential error back. -/
noncomputable def feedRate (θ : ℝ) : ℝ := ⟪loopSide θ, kerDir proj θ⟫

/-- `F(x) = ∫₀ˣ f`. -/
noncomputable def feedInt (x : ℝ) : ℝ := ∫ θ in (0 : ℝ)..x, feedRate proj θ

/-- The periodic part `p(x) = F(x) - x F(2π) / (2π)` of `F`. -/
noncomputable def feedPer (x : ℝ) : ℝ := feedInt proj x - x * (feedInt proj (2 * π) / (2 * π))

/-- The exponent `G(t) = F(θ₀ + s t) - F(θ₀)`. -/
noncomputable def gain (θ₀ s t : ℝ) : ℝ := feedInt proj (θ₀ + s * t) - feedInt proj θ₀

/-- The tangential error `β(t) = ε e^{G(t)} ∫₀ᵗ e^{-G(r)} dr`. -/
noncomputable def tanErr (θ₀ s ε t : ℝ) : ℝ :=
  ε * Real.exp (gain proj θ₀ s t) * ∫ r in (0 : ℝ)..t, Real.exp (-gain proj θ₀ s r)

/-- The rate `s β(r) (q - f B - N)(θ₀ + s r)` of the remaining part of the error. -/
noncomputable def restRate (θ₀ s ε r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (s * tanErr proj θ₀ s ε r) • (kerDir proj (θ₀ + s * r) -
    feedRate proj (θ₀ + s * r) • loopSide (θ₀ + s * r) - loopNormal (θ₀ + s * r))

/-- The data `A(t) = Y(θ₀ + s t) + β(t) B(θ₀ + s t) + s ε N(θ₀ + s t) + ∫₀ᵗ restRate`. -/
noncomputable def advData (θ₀ s ε t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  involuteState (θ₀ + s * t) + (tanErr proj θ₀ s ε t • loopSide (θ₀ + s * t) +
    (s * ε) • loopNormal (θ₀ + s * t) + ∫ r in (0 : ℝ)..t, restRate proj θ₀ s ε r)

/-- The velocity of the data, `s u⊥ e₁ᵀ + s β q`. -/
noncomputable def advDeriv (θ₀ s ε t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  s • involuteStateDeriv (θ₀ + s * t) + (s * tanErr proj θ₀ s ε t) • kerDir proj (θ₀ + s * t)

variable {proj}

lemma continuous_kerDir (hC : Continuous fun θ => proj (involuteState θ) (loopNormal θ)) :
    Continuous (kerDir proj) :=
  continuous_loopNormal.sub hC

lemma continuous_feedRate (hC : Continuous fun θ => proj (involuteState θ) (loopNormal θ)) :
    Continuous (feedRate proj) :=
  continuous_loopSide.inner (continuous_kerDir hC)

lemma hasDerivAt_feedInt (hC : Continuous fun θ => proj (involuteState θ) (loopNormal θ))
    (x : ℝ) : HasDerivAt (feedInt proj) (feedRate proj x) x :=
  ((continuous_feedRate hC).integral_hasStrictDerivAt 0 x).hasDerivAt

lemma hasDerivAt_gain (hC : Continuous fun θ => proj (involuteState θ) (loopNormal θ))
    (θ₀ s t : ℝ) : HasDerivAt (gain proj θ₀ s) (s * feedRate proj (θ₀ + s * t)) t := by
  have h := ((hasDerivAt_feedInt hC (θ₀ + s * t)).comp t (hasDerivAt_affine θ₀ s t)).sub_const
    (feedInt proj θ₀)
  exact h.congr_deriv (mul_comm _ _)

lemma continuous_gain (hC : Continuous fun θ => proj (involuteState θ) (loopNormal θ))
    (θ₀ s : ℝ) : Continuous (gain proj θ₀ s) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_gain hC θ₀ s t).continuousAt

/-- `β' = s f(θ₀ + s t) β + ε`. -/
theorem hasDerivAt_tanErr (hC : Continuous fun θ => proj (involuteState θ) (loopNormal θ))
    (θ₀ s ε t : ℝ) : HasDerivAt (tanErr proj θ₀ s ε)
      (s * feedRate proj (θ₀ + s * t) * tanErr proj θ₀ s ε t + ε) t := by
  have hI : HasDerivAt (fun u => ∫ r in (0 : ℝ)..u, Real.exp (-gain proj θ₀ s r))
      (Real.exp (-gain proj θ₀ s t)) t :=
    (((continuous_gain hC θ₀ s).neg.rexp).integral_hasStrictDerivAt 0 t).hasDerivAt
  have h := ((hasDerivAt_gain hC θ₀ s t).exp.const_mul ε).mul hI
  refine h.congr_deriv ?_
  have e : Real.exp (gain proj θ₀ s t) * Real.exp (-gain proj θ₀ s t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [tanErr]
  linear_combination ε * e

lemma continuous_tanErr (hC : Continuous fun θ => proj (involuteState θ) (loopNormal θ))
    (θ₀ s ε : ℝ) : Continuous (tanErr proj θ₀ s ε) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_tanErr hC θ₀ s ε t).continuousAt

lemma continuous_restRate (hC : Continuous fun θ => proj (involuteState θ) (loopNormal θ))
    (θ₀ s ε : ℝ) : Continuous (restRate proj θ₀ s ε) := by
  have hA : Continuous fun r : ℝ => θ₀ + s * r := by fun_prop
  exact (continuous_const.mul (continuous_tanErr hC θ₀ s ε)).smul
    ((((continuous_kerDir hC).comp hA).sub (((continuous_feedRate hC).comp hA).smul
      (continuous_loopSide.comp hA))).sub (continuous_loopNormal.comp hA))

/-- **The data have the velocity `advDeriv`.** -/
theorem hasDerivAt_advData (hC : Continuous fun θ => proj (involuteState θ) (loopNormal θ))
    {θ₀ s : ℝ} (hs : s = 1 ∨ s = -1) (ε t : ℝ) :
    HasDerivAt (advData proj θ₀ s ε) (advDeriv proj θ₀ s ε t) t := by
  have hA := hasDerivAt_affine θ₀ s t
  have hY : HasDerivAt (fun t => involuteState (θ₀ + s * t))
      (s • involuteStateDeriv (θ₀ + s * t)) t :=
    HasDerivAt.scomp t (hasDerivAt_involuteState (θ₀ + s * t)) hA (h := fun t => θ₀ + s * t)
  have hB : HasDerivAt (fun t => loopSide (θ₀ + s * t)) (s • loopNormal (θ₀ + s * t)) t :=
    HasDerivAt.scomp t (hasDerivAt_loopSide (θ₀ + s * t)) hA (h := fun t => θ₀ + s * t)
  have hN : HasDerivAt (fun t => loopNormal (θ₀ + s * t)) (s • -loopSide (θ₀ + s * t)) t :=
    HasDerivAt.scomp t (hasDerivAt_loopNormal (θ₀ + s * t)) hA (h := fun t => θ₀ + s * t)
  have hR : HasDerivAt (fun u => ∫ r in (0 : ℝ)..u, restRate proj θ₀ s ε r)
      (restRate proj θ₀ s ε t) t :=
    ((continuous_restRate hC θ₀ s ε).integral_hasStrictDerivAt 0 t).hasDerivAt
  have h := hY.add ((((hasDerivAt_tanErr hC θ₀ s ε t).smul hB).add
    (hN.const_smul (s * ε))).add hR)
  refine h.congr_deriv ?_
  rw [advDeriv, restRate]
  rcases hs with rfl | rfl <;> module

/-- **The state solves the method's equation for the data:** `Π(Y) Ȧ = Ẏ`. -/
theorem proj_advDeriv (hT : ∀ θ X, ⟪loopNormal θ, X⟫ = 0 → proj (involuteState θ) X = X)
    (hR : ∀ θ X, ⟪loopNormal θ, proj (involuteState θ) X⟫ = 0) (θ₀ s ε t : ℝ) :
    proj (involuteState (θ₀ + s * t)) (advDeriv proj θ₀ s ε t) =
      s • involuteStateDeriv (θ₀ + s * t) := by
  have h1 := hT (θ₀ + s * t) _ (inner_loopNormal_involuteStateDeriv (θ₀ + s * t))
  have h2 := hT (θ₀ + s * t) _ (hR (θ₀ + s * t) (loopNormal (θ₀ + s * t)))
  rw [advDeriv, kerDir, map_add, map_smul, map_smul, map_sub, h1, h2, sub_self, smul_zero,
    add_zero]

/-- `q - f B - N` is orthogonal to `B` and `N` at its angle, so its second column vanishes. -/
lemma col_restDir (hR : ∀ θ X, ⟪loopNormal θ, proj (involuteState θ) X⟫ = 0) (φ : ℝ) :
    (kerDir proj φ - feedRate proj φ • loopSide φ - loopNormal φ) 0 1 = 0 ∧
      (kerDir proj φ - feedRate proj φ • loopSide φ - loopNormal φ) 1 1 = 0 := by
  refine col_eq_zero_of_inner (φ := φ) ?_ ?_
  · rw [inner_sub_right, inner_sub_right, real_inner_smul_right, inner_loopSide_self,
      inner_loopSide_loopNormal, feedRate]
    ring
  · rw [inner_sub_right, inner_sub_right, real_inner_smul_right, inner_loopNormal_loopSide,
      inner_loopNormal_self, kerDir, inner_sub_right, inner_loopNormal_self, hR]
    ring

/-- If `Π(Y(φ)) N(φ)` has a zero first column, then `q - f B - N = 0` at the angle `φ`. -/
lemma restDir_eq_zero (hR : ∀ θ X, ⟪loopNormal θ, proj (involuteState θ) X⟫ = 0) {φ : ℝ}
    (h0 : proj (involuteState φ) (loopNormal φ) 0 0 = 0)
    (h1 : proj (involuteState φ) (loopNormal φ) 1 0 = 0) :
    kerDir proj φ - feedRate proj φ • loopSide φ - loopNormal φ = 0 := by
  obtain ⟨c0, c1⟩ := col_restDir hR φ
  have e0 : (kerDir proj φ - feedRate proj φ • loopSide φ - loopNormal φ) 0 0 = 0 := by
    rw [kerDir, Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply, h0]
    simp [loopSide, loopNormal]
  have e1 : (kerDir proj φ - feedRate proj φ • loopSide φ - loopNormal φ) 1 0 = 0 := by
    rw [kerDir, Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply, h1]
    simp [loopSide, loopNormal]
  ext i j
  fin_cases i <;> fin_cases j
  exacts [e0, c0, e1, c1]

lemma inner_loopNormal_restRate (hR : ∀ θ X, ⟪loopNormal θ, proj (involuteState θ) X⟫ = 0)
    (θ θ₀ s ε r : ℝ) : ⟪loopNormal θ, restRate proj θ₀ s ε r⟫ = 0 := by
  obtain ⟨h1, h2⟩ := col_restDir hR (θ₀ + s * r)
  rw [inner_loopNormal, restRate, Matrix.smul_apply, Matrix.smul_apply, h1, h2]
  simp

lemma inner_loopSide_restRate (hR : ∀ θ X, ⟪loopNormal θ, proj (involuteState θ) X⟫ = 0)
    (θ θ₀ s ε r : ℝ) : ⟪loopSide θ, restRate proj θ₀ s ε r⟫ = 0 := by
  obtain ⟨h1, h2⟩ := col_restDir hR (θ₀ + s * r)
  rw [inner_loopSide, restRate, Matrix.smul_apply, Matrix.smul_apply, h1, h2]
  simp

lemma inner_loopNormal_integral_restRate
    (hC : Continuous fun θ => proj (involuteState θ) (loopNormal θ))
    (hR : ∀ θ X, ⟪loopNormal θ, proj (involuteState θ) X⟫ = 0) (θ θ₀ s ε t : ℝ) :
    ⟪loopNormal θ, ∫ r in (0 : ℝ)..t, restRate proj θ₀ s ε r⟫ = 0 := by
  have h := (innerSL ℝ (loopNormal θ)).intervalIntegral_comp_comm
    ((continuous_restRate hC θ₀ s ε).intervalIntegrable (μ := volume) 0 t)
  simp only [innerSL_apply_apply, inner_loopNormal_restRate hR,
    intervalIntegral.integral_zero] at h
  exact h.symm

lemma inner_loopSide_integral_restRate
    (hC : Continuous fun θ => proj (involuteState θ) (loopNormal θ))
    (hR : ∀ θ X, ⟪loopNormal θ, proj (involuteState θ) X⟫ = 0) (θ θ₀ s ε t : ℝ) :
    ⟪loopSide θ, ∫ r in (0 : ℝ)..t, restRate proj θ₀ s ε r⟫ = 0 := by
  have h := (innerSL ℝ (loopSide θ)).intervalIntegral_comp_comm
    ((continuous_restRate hC θ₀ s ε).intervalIntegrable (μ := volume) 0 t)
  simp only [innerSL_apply_apply, inner_loopSide_restRate hR,
    intervalIntegral.integral_zero] at h
  exact h.symm

/-- **The normal component of the error is `s ε` at all times.** -/
theorem inner_loopNormal_advData_sub
    (hC : Continuous fun θ => proj (involuteState θ) (loopNormal θ))
    (hR : ∀ θ X, ⟪loopNormal θ, proj (involuteState θ) X⟫ = 0) (θ₀ s ε t : ℝ) :
    ⟪loopNormal (θ₀ + s * t), advData proj θ₀ s ε t - involuteState (θ₀ + s * t)⟫ = s * ε := by
  rw [advData, add_sub_cancel_left, inner_add_right, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, inner_loopNormal_loopSide, inner_loopNormal_self,
    inner_loopNormal_integral_restRate hC hR]
  ring

/-- **The tangential component `⟪B, A - Y⟫` of the error is `β`.** -/
theorem inner_loopSide_advData_sub
    (hC : Continuous fun θ => proj (involuteState θ) (loopNormal θ))
    (hR : ∀ θ X, ⟪loopNormal θ, proj (involuteState θ) X⟫ = 0) (θ₀ s ε t : ℝ) :
    ⟪loopSide (θ₀ + s * t), advData proj θ₀ s ε t - involuteState (θ₀ + s * t)⟫ =
      tanErr proj θ₀ s ε t := by
  rw [advData, add_sub_cancel_left, inner_add_right, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, inner_loopSide_self, inner_loopSide_loopNormal,
    inner_loopSide_integral_restRate hC hR]
  ring

theorem abs_tanErr_le_norm (hC : Continuous fun θ => proj (involuteState θ) (loopNormal θ))
    (hR : ∀ θ X, ⟪loopNormal θ, proj (involuteState θ) X⟫ = 0) (θ₀ s ε t : ℝ) :
    |tanErr proj θ₀ s ε t| ≤ ‖advData proj θ₀ s ε t - involuteState (θ₀ + s * t)‖ := by
  rw [← inner_loopSide_advData_sub hC hR]
  calc _ ≤ ‖loopSide (θ₀ + s * t)‖ * ‖advData proj θ₀ s ε t - involuteState (θ₀ + s * t)‖ :=
        abs_real_inner_le_norm _ _
    _ = _ := by rw [norm_loopSide, one_mul]

/-- **Within `|ε|` of `M_1` in the subclass.** If `Π(Y(θ)) N(θ)` has a zero first column for
every `θ` (the kernel direction lies in `span {N, B}`), the remaining part of the error vanishes:
`A - (Y + β B) = s ε N` with `Y + β B` of rank at most one, so `dist(A(t), M_1) ≤ |ε|`. -/
theorem distLR_advData_le (hR : ∀ θ X, ⟪loopNormal θ, proj (involuteState θ) X⟫ = 0)
    (hF : ∀ θ, proj (involuteState θ) (loopNormal θ) 0 0 = 0 ∧
      proj (involuteState θ) (loopNormal θ) 1 0 = 0)
    {θ₀ s : ℝ} (hs : s = 1 ∨ s = -1) (ε t : ℝ) :
    distLR 1 (advData proj θ₀ s ε t) ≤ |ε| := by
  have hr : ∀ r, restRate proj θ₀ s ε r = 0 := fun r => by
    obtain ⟨h0, h1⟩ := hF (θ₀ + s * r)
    rw [restRate, restDir_eq_zero hR h0 h1, smul_zero]
  have hI : ∫ r in (0 : ℝ)..t, restRate proj θ₀ s ε r = 0 := by
    simp only [hr, intervalIntegral.integral_zero]
  have e : advData proj θ₀ s ε t -
      (involuteState (θ₀ + s * t) + tanErr proj θ₀ s ε t • loopSide (θ₀ + s * t)) =
      (s * ε) • loopNormal (θ₀ + s * t) := by
    rw [advData, hI]
    abel
  calc distLR 1 (advData proj θ₀ s ε t)
      ≤ ‖advData proj θ₀ s ε t -
          (involuteState (θ₀ + s * t) + tanErr proj θ₀ s ε t • loopSide (θ₀ + s * t))‖ :=
        distLR_le_norm_sub (rank_involuteState_add_smul_loopSide_le _ _)
    _ = |ε| := by
        rw [e, norm_smul, norm_loopNormal, mul_one, Real.norm_eq_abs, abs_mul]
        rcases hs with rfl | rfl <;> simp

/-- **The tangential error grows at least linearly** while the exponent does not decrease below
its final value: if `G(r) ≤ G(T)` on `[0, T]`, then `β(T) ≥ ε T`. -/
theorem mul_le_tanErr (hC : Continuous fun θ => proj (involuteState θ) (loopNormal θ))
    {θ₀ s ε T : ℝ} (hε : 0 ≤ ε) (hT : 0 ≤ T)
    (h : ∀ r ∈ Icc 0 T, gain proj θ₀ s r ≤ gain proj θ₀ s T) : ε * T ≤ tanErr proj θ₀ s ε T := by
  have hG := continuous_gain hC θ₀ s
  have hc : Continuous fun r => Real.exp (gain proj θ₀ s T - gain proj θ₀ s r) := by fun_prop
  have e : tanErr proj θ₀ s ε T =
      ε * ∫ r in (0 : ℝ)..T, Real.exp (gain proj θ₀ s T - gain proj θ₀ s r) := by
    rw [tanErr, mul_assoc, ← intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [← Real.exp_add, ← sub_eq_add_neg]
  have hmono : ∫ _ in (0 : ℝ)..T, (1 : ℝ) ≤
      ∫ r in (0 : ℝ)..T, Real.exp (gain proj θ₀ s T - gain proj θ₀ s r) :=
    intervalIntegral.integral_mono_on hT (intervalIntegrable_const (μ := volume))
      (hc.intervalIntegrable (μ := volume) 0 T)
      fun r hr => Real.one_le_exp (sub_nonneg.2 (h r hr))
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at hmono
  rw [e]
  exact mul_le_mul_of_nonneg_left hmono hε

/-! ### The direction and the start angle -/

lemma feedRate_add_two_pi (θ : ℝ) : feedRate proj (θ + 2 * π) = feedRate proj θ := by
  simp only [feedRate, kerDir, loopNormal_add_two_pi, loopSide_add_two_pi,
    involuteState_add_two_pi]

lemma feedInt_add_two_pi (hC : Continuous fun θ => proj (involuteState θ) (loopNormal θ))
    (x : ℝ) : feedInt proj (x + 2 * π) = feedInt proj x + feedInt proj (2 * π) := by
  have hc := continuous_feedRate hC
  have hper : Function.Periodic (feedRate proj) (2 * π) := feedRate_add_two_pi
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 x)
    (hc.intervalIntegrable (μ := volume) x (x + 2 * π))
  have h2 := hper.intervalIntegral_add_eq x 0
  rw [zero_add] at h2
  rw [feedInt, feedInt, feedInt, ← h1, h2]

lemma feedPer_periodic (hC : Continuous fun θ => proj (involuteState θ) (loopNormal θ)) :
    Function.Periodic (feedPer proj) (2 * π) := by
  intro x
  have hπ : (2 * π) ≠ 0 := by positivity
  have e : (2 * π) * (feedInt proj (2 * π) / (2 * π)) = feedInt proj (2 * π) := by
    field_simp
  rw [feedPer, feedPer, feedInt_add_two_pi hC]
  linear_combination -e

/-- **Choice of the direction and of the start angle.** With `s` the sign of `∫₀^{2π} f` and
`θ₀` a maximum of the periodic part of `θ ↦ ∫₀^θ f`, the exponent satisfies `G(r) ≤ G(2π k)` on
`[0, 2π k]`. -/
theorem exists_start_gain_le (hC : Continuous fun θ => proj (involuteState θ) (loopNormal θ))
    (k : ℕ) : ∃ θ₀ s : ℝ, (s = 1 ∨ s = -1) ∧
      ∀ r ∈ Icc (0 : ℝ) (2 * π * k), gain proj θ₀ s r ≤ gain proj θ₀ s (2 * π * k) := by
  have hper := feedPer_periodic hC
  have hF : Continuous (feedInt proj) :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_feedInt hC x).continuousAt
  have hcont : Continuous (feedPer proj) := by
    unfold feedPer
    fun_prop
  have hpi : 0 < 2 * π := by positivity
  obtain ⟨θ₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hpi.le)
    hcont.continuousOn
  have hle : ∀ x, feedPer proj x ≤ feedPer proj θ₀ := fun x => by
    obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico₀ hpi x
    rw [hxy]
    exact hmax (Ico_subset_Icc_self hy)
  have hFp : ∀ x, feedInt proj x =
      feedPer proj x + x * (feedInt proj (2 * π) / (2 * π)) := fun x => by
    rw [feedPer]
    ring
  by_cases h0 : 0 ≤ feedInt proj (2 * π)
  · refine ⟨θ₀, 1, Or.inl rfl, fun r hr => ?_⟩
    have hk : feedPer proj (θ₀ + 1 * (2 * π * k)) = feedPer proj θ₀ := by
      rw [one_mul, show 2 * π * (k : ℝ) = k * (2 * π) by ring]
      exact hper.nat_mul k θ₀
    have h1 := hle (θ₀ + 1 * r)
    have h2 : 0 ≤ (2 * π * k - r) * (feedInt proj (2 * π) / (2 * π)) :=
      mul_nonneg (by linarith [hr.2]) (div_nonneg h0 hpi.le)
    rw [gain, gain, hFp (θ₀ + 1 * r), hFp (θ₀ + 1 * (2 * π * k)), hk]
    nlinarith
  · refine ⟨θ₀, -1, Or.inr rfl, fun r hr => ?_⟩
    have hk : feedPer proj (θ₀ + -1 * (2 * π * k)) = feedPer proj θ₀ := by
      rw [show θ₀ + -1 * (2 * π * (k : ℝ)) = θ₀ - k * (2 * π) by ring]
      exact hper.sub_nat_mul_eq k
    have h1 := hle (θ₀ + -1 * r)
    have h3 : feedInt proj (2 * π) / (2 * π) < 0 := div_neg_of_neg_of_pos (not_le.1 h0) hpi
    have h2 : 0 ≤ (2 * π * k - r) * (-(feedInt proj (2 * π) / (2 * π))) :=
      mul_nonneg (by linarith [hr.2]) (by linarith)
    rw [gain, gain, hFp (θ₀ + -1 * r), hFp (θ₀ + -1 * (2 * π * k)), hk]
    nlinarith

end Method

/-! ### A family of methods in the class -/

/-- The method `Π_κ(Y) a = a - ⟪N(Y), a⟫ (N(Y) + κ B(Y))` with `N(Y) = [[0, -Y₁₀], [0, Y₀₀]]` and
`B(Y) = [[0, Y₀₀], [0, Y₁₀]]`. On the circle `N(Y(θ)) = N(θ)`, `B(Y(θ)) = B(θ)` and `f ≡ κ`;
on the circle, `κ = 0` is the orthogonal projection onto the tangent space (the projected
equation). Off the circle `N(Y)` need not be a unit vector, and `Π_0(Y)` need not be a
projection. -/
noncomputable def tangentObliqueProj (κ : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun X := X - ⟪!![0, -Y 1 0; 0, Y 0 0], X⟫ •
    (!![0, -Y 1 0; 0, Y 0 0] + κ • !![0, Y 0 0; 0, Y 1 0])
  map_add' X Z := by
    simp only [inner_add_right, add_smul]
    abel
  map_smul' c X := by
    simp only [real_inner_smul_right, RingHom.id_apply, smul_sub, smul_smul]

lemma tangentObliqueProj_apply (κ θ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    tangentObliqueProj κ (involuteState θ) X =
      X - ⟪loopNormal θ, X⟫ • (loopNormal θ + κ • loopSide θ) := by
  have e1 : (!![0, -(involuteState θ) 1 0; 0, (involuteState θ) 0 0] :
      Matrix (Fin 2) (Fin 2) ℝ) = loopNormal θ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [involuteState, loopNormal]
  have e2 : (!![0, (involuteState θ) 0 0; 0, (involuteState θ) 1 0] :
      Matrix (Fin 2) (Fin 2) ℝ) = loopSide θ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [involuteState, loopSide]
  change X - ⟪!![0, -(involuteState θ) 1 0; 0, (involuteState θ) 0 0], X⟫ •
    (!![0, -(involuteState θ) 1 0; 0, (involuteState θ) 0 0] +
      κ • !![0, (involuteState θ) 0 0; 0, (involuteState θ) 1 0]) = _
  rw [e1, e2]

/-- `Π_κ` is the identity on the tangent space along the circle. -/
lemma tangentObliqueProj_of_inner_eq_zero (κ θ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ)
    (h : ⟪loopNormal θ, X⟫ = 0) : tangentObliqueProj κ (involuteState θ) X = X := by
  rw [tangentObliqueProj_apply, h, zero_smul, sub_zero]

/-- `Π_κ` maps into the tangent space along the circle. -/
lemma inner_loopNormal_tangentObliqueProj (κ θ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    ⟪loopNormal θ, tangentObliqueProj κ (involuteState θ) X⟫ = 0 := by
  rw [tangentObliqueProj_apply, inner_sub_right, real_inner_smul_right, inner_add_right,
    real_inner_smul_right, inner_loopNormal_self, inner_loopNormal_loopSide]
  ring

lemma continuous_tangentObliqueProj_loopNormal (κ : ℝ) :
    Continuous fun θ => tangentObliqueProj κ (involuteState θ) (loopNormal θ) := by
  have e : (fun θ => tangentObliqueProj κ (involuteState θ) (loopNormal θ)) =
      fun θ => loopNormal θ - (1 : ℝ) • (loopNormal θ + κ • loopSide θ) := by
    funext θ
    rw [tangentObliqueProj_apply, inner_loopNormal_self]
  rw [e]
  have h1 := continuous_loopNormal
  have h2 := continuous_loopSide
  fun_prop

/-- `Π_κ(Y(θ)) N(θ) = -κ B(θ)` has a zero first column, so `Π_κ` lies in the subclass where the
data stay within `ε` of `M_1`. -/
lemma tangentObliqueProj_loopNormal_col (κ θ : ℝ) :
    tangentObliqueProj κ (involuteState θ) (loopNormal θ) 0 0 = 0 ∧
      tangentObliqueProj κ (involuteState θ) (loopNormal θ) 1 0 = 0 := by
  rw [tangentObliqueProj_apply, inner_loopNormal_self, one_smul]
  simp [loopNormal, loopSide]

end LeanDLRA.ObliqueProjectorLowerBoundExample

namespace LeanDLRA.ObliqueProjectorLowerBound

open LeanDLRA.RankStatePriceExample LeanDLRA.ObliqueProjectorLowerBoundExample

/-- **Oblique tangent projectors on `2 × 2` rank-one states: error `2π k ε` at normal component
`ε`.** Let `Π(Y)` be linear maps on `2 × 2` matrices such that along the circle `Y(θ) = u(θ) e₁ᵀ`
of states of rank one `Π(Y(θ))` is the identity on the tangent space `{X : ⟪N(θ), X⟫ = 0}`, maps
into it, and `θ ↦ Π(Y(θ)) N(θ)` is continuous. For every `ε ≥ 0` and `k : ℕ` there are a
direction `s = ± 1`, a start angle `θ₀`, data `A` with velocity `A'` and a state
`Y(t) = Y(θ₀ + s t)` of rank one (turning by the angle `2π k` on `[0, 2π k]`) such that `Y`
solves `Ẏ = Π(Y) Ȧ`, the error starts as `A(0) - Y(0) = s ε N(θ₀)`, its normal component
`⟪N, A - Y⟫` is `s ε` at all times, and the error at `t = 2π k` is at least `2π k ε`.

Here `ε` is the normal component of the error, not the best-approximation error: for a general
`Π` the statement gives no bound on `dist(A(t), M_1)`. The last conjunct gives one in a
subclass: if `Π(Y(θ)) N(θ)` has a zero first column for every `θ`, then `dist(A(t), M_1) ≤ ε`
for all `t`. -/
theorem exists_data_two_pi_mul_le_norm_sub
    (proj : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ)
    (hT : ∀ θ X, ⟪loopNormal θ, X⟫ = 0 → proj (involuteState θ) X = X)
    (hR : ∀ θ X, ⟪loopNormal θ, proj (involuteState θ) X⟫ = 0)
    (hC : Continuous fun θ => proj (involuteState θ) (loopNormal θ)) {ε : ℝ} (hε : 0 ≤ ε)
    (k : ℕ) :
    ∃ (A A' Y : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ₀ s : ℝ), (s = 1 ∨ s = -1) ∧
      (∀ t, Y t = involuteState (θ₀ + s * t)) ∧ (∀ t, (Y t).rank = 1) ∧
      (∀ t, HasDerivAt A (A' t) t) ∧ (∀ t, HasDerivAt Y (proj (Y t) (A' t)) t) ∧
      (∀ t, ⟪loopNormal (θ₀ + s * t), A t - Y t⟫ = s * ε) ∧
      A 0 - Y 0 = (s * ε) • loopNormal θ₀ ∧
      2 * π * k * ε ≤ ‖A (2 * π * k) - Y (2 * π * k)‖ ∧
      ((∀ θ, proj (involuteState θ) (loopNormal θ) 0 0 = 0 ∧
        proj (involuteState θ) (loopNormal θ) 1 0 = 0) → ∀ t, distLR 1 (A t) ≤ ε) := by
  obtain ⟨θ₀, s, hs, hgain⟩ := exists_start_gain_le hC k
  refine ⟨advData proj θ₀ s ε, advDeriv proj θ₀ s ε, fun t => involuteState (θ₀ + s * t), θ₀,
    s, hs, fun t => rfl, fun t => rank_involuteState _, fun t => hasDerivAt_advData hC hs ε t,
    fun t => ?_, fun t => inner_loopNormal_advData_sub hC hR θ₀ s ε t, ?_, ?_,
    fun hF t => (distLR_advData_le hR hF hs ε t).trans_eq (abs_of_nonneg hε)⟩
  · rw [proj_advDeriv hT hR]
    exact HasDerivAt.scomp t (hasDerivAt_involuteState (θ₀ + s * t)) (hasDerivAt_affine θ₀ s t)
      (h := fun t => θ₀ + s * t)
  · simp [advData, tanErr]
  · have h1 := mul_le_tanErr hC hε (by positivity) hgain
    have h2 := abs_tanErr_le_norm hC hR θ₀ s ε (2 * π * k)
    have h3 := le_abs_self (tanErr proj θ₀ s ε (2 * π * k))
    change 2 * π * k * ε ≤
      ‖advData proj θ₀ s ε (2 * π * k) - involuteState (θ₀ + s * (2 * π * k))‖
    linarith

/-- Non-vacuity: the oblique method `Π_{1/2}` (not the orthogonal projection) satisfies the
hypotheses and lies in the subclass. For `ε = 1/10` and `k = 1` the state stays on the circle
and has rank one, the error starts as `ε N(θ₀)` up to sign, keeps the normal component `s ε`,
the data stay within `ε` of the matrices of rank at most one, and the error after one turn is
at least `2π ε`. -/
example : ∃ (A A' Y : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ₀ s : ℝ), (s = 1 ∨ s = -1) ∧
    (∀ t, Y t = involuteState (θ₀ + s * t)) ∧ (∀ t, (Y t).rank = 1) ∧
    (∀ t, HasDerivAt A (A' t) t) ∧
    (∀ t, HasDerivAt Y (tangentObliqueProj (1 / 2) (Y t) (A' t)) t) ∧
    (∀ t, ⟪loopNormal (θ₀ + s * t), A t - Y t⟫ = s * (1 / 10)) ∧
    A 0 - Y 0 = (s * (1 / 10)) • loopNormal θ₀ ∧
    (∀ t, distLR 1 (A t) ≤ 1 / 10) ∧ 2 * π * (1 / 10) ≤ ‖A (2 * π) - Y (2 * π)‖ := by
  obtain ⟨A, A', Y, θ₀, s, hs, hY, hr, hA, hYd, hN, h0, h, hd⟩ :=
    exists_data_two_pi_mul_le_norm_sub (tangentObliqueProj (1 / 2))
      (tangentObliqueProj_of_inner_eq_zero (1 / 2)) (inner_loopNormal_tangentObliqueProj (1 / 2))
      (continuous_tangentObliqueProj_loopNormal (1 / 2)) (ε := 1 / 10) (by norm_num) 1
  refine ⟨A, A', Y, θ₀, s, hs, hY, hr, hA, hYd, hN, h0,
    hd (tangentObliqueProj_loopNormal_col (1 / 2)), ?_⟩
  simpa using h

end LeanDLRA.ObliqueProjectorLowerBound
