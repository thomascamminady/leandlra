import LeanDLRA.HighOrder.MidpointBUG
import LeanDLRA.Integrators.Defs
import LeanDLRA.LinearAlgebra.Factorization.Defs
import LeanDLRA.Matrix.LowRankDistance

/-!
# Galerkin steps that contain a predictor: a two-column K-step basis, Sylvester fields

## Setting

One step of a BUG-type integrator for `A' = F(t, A)` from `Y₀ = U₀ S₀ V₀ᵀ` (rank `r`) is a
Galerkin step `YS' = R F(t, YS)`, `YS(t₀) = Y₀`, with an orthogonal projector `R` that fixes
`Y₀`.  The rank-adaptive BUG integrator (Ceruti–Kusch–Lubich, arXiv:2104.05247) uses
`R X = Û Ûᵀ X V̂ V̂ᵀ`, where the range of `Û` contains the ranges of `U₀` and of the K-step
solution `K(t₁)`, and the range of `V̂` contains the ranges of `V₀` and of the L-step solution
`L(t₁)` (`MatrixBUG.IsRankAdaptiveStep`).

## Main results

* `galerkin_error_of_predictor`, `hasLocalError_of_predictor`: if the orthogonal projector `R`
  fixes the starting value and a point `Y⋆` with `‖Y⋆ - A(t₁)‖ ≤ μ`, then the Galerkin step has
  error at most `(e^{L h} - 1) (μ + M₂ h²) + μ`, where `M₂` bounds the derivative of
  `t ↦ F(t, A(t))`.  The point `Y⋆` is arbitrary; for matrices it can be any rank-`r` point
  `Y⋆` with `‖Y⋆ - A(t₁)‖ ≤ μ`.
* `galerkin_error_of_capture`: the case `Y⋆ = A(t₁)`, `μ = 0`.
* `error_ge_of_isRankAdaptiveStep`, `not_hasLocalError_of_isRankAdaptiveStep`: for the
  polynomial field `Examples.rowField` on `3 × 2` matrices, whose normal component vanishes at
  every rank-one point (`rowField_normal`, `factoredNormalBoundOn_rowField`), and the start
  `Y₀ = e₁ e₁ᵀ` with singular value `1`, every rank-adaptive BUG step with a two-column left
  basis `Û` and truncation tolerance `ϑ` has error at least `h² / 2 - ϑ`, for every `h > 0`.
  `exists_error_ge_of_isRankAdaptiveStep` is the same statement without the names of the
  example.
* `rowField_mul_row_two`, `eq_kSolution_of_odeSolution`, `row_two_eq_zero_of_capture`,
  `error_ge_of_row_two_eq_zero`: the steps of the proof.  The field has a zero third row at
  every matrix `M V₀ᵀ` whose left factor `M` has a zero third entry; every solution of the
  K-step equation from `U₀ S₀` is `K(t) = (1, t, 0)ᵀ`; an orthonormal two-column basis whose
  range contains `U₀` and `K(h)` has a zero third row; and every matrix with such a left factor
  has distance at least `h² / 2` from the exact solution.
* `isRankAdaptiveStep_example`: an explicit rank-adaptive BUG step for this field and start,
  so that the hypothesis of the lower bound can be met.
* `capture_of_sylvester`, `error_le_of_sylvester`: for a Lipschitz field of Sylvester type,
  `F(t, Y) = 𝒜(t) Y + Y ℬ(t)`, the Galerkin space of every rank-adaptive BUG step contains the
  exact solution `A(t₁)`, and the step has error at most `(e^{L h} - 1) M₂ h² + ϑ`.  The
  solutions `P`, `Q` of two auxiliary linear equations are hypotheses of both theorems.
* `kField_of_sylvester`, `transpose_lField_of_sylvester`, `odeSolution_kCurve`,
  `odeSolution_lCurve`, `eq_kStep_mul_of_sylvester`, `eq_mul_lStep_of_sylvester`: the steps of
  that proof.  The K-step equation is `K' = 𝒜 K + K (V₀ᵀ ℬ V₀)`, the curve `K(t) P(t)` solves
  `A' = F(t, A)`, and so `A(t) = K(t) P(t)` by uniqueness; the L-step is the mirror image.
* `isLipschitzField_sylField`, `isRankAdaptiveStep_sylField`: the linear field
  `Examples.sylField`, which is `Examples.rowField` without its quadratic term, satisfies the
  hypotheses of `error_le_of_sylvester` with the step data of `isRankAdaptiveStep_example`.

## Implementation notes

* The concrete matrices of the example are in the namespace `Examples`.
* `Examples.rowField` is a polynomial of degree two and is not globally Lipschitz.  The lower
  bound needs no Lipschitz hypothesis on it: the proof uses uniqueness only for the K-step
  equation, which is linear for this field (`kField_rowField`).
* The first three theorems are stated for an orthogonal projector on a real inner product
  space.  For matrices, `galerkinProj Û V̂ = leftProj Û * rightProj V̂` is such a projector
  (`isOrthProj_galerkinProj`); `error_le_of_sylvester` uses it.

## References

* Ceruti–Kusch–Lubich, arXiv:2104.05247 (rank-adaptive BUG integrator).
* Ceruti–Einkemmer–Kusch–Lubich, arXiv:2402.08607 (the argument behind
  `MidpointBUG.interior_capture`, which `galerkin_error_of_predictor` uses).
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace AugmentationRank

/-! ### A Galerkin space that contains a predictor -/

section Predictor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : ℝ → E → E} {L : ℝ}
  {t₀ t₁ h : ℝ} {A : ℝ → E}

/-- **Galerkin step in a space that contains a predictor.**  Let `R` be an orthogonal projector
that fixes the starting value `A(t₀)` and a point `Y⋆` with `‖Y⋆ - A(t₁)‖ ≤ μ`, and let
`t ↦ F(t, A t)` have a derivative bounded by `M₂`.  Then the Galerkin step `YS' = R F(t, YS)`,
`YS(t₀) = A(t₀)`, satisfies

    ‖YS(t₁) - A(t₁)‖ ≤ (e^{L h} - 1) (μ + M₂ h²) + μ.

No singular value enters.  The proof combines the best-approximation property of `R`
(`IsOrthProj.norm_sub_le_of_mem_range`) with `MidpointBUG.interior_capture` and
`MidpointBUG.galerkin_step_error_interior`. -/
theorem galerkin_error_of_predictor {R : E →L[ℝ] E} (hR : IsOrthProj R)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hRA : R (A t₀) = A t₀) {a₂ : ℝ → E} {M₂ : ℝ}
    (ha : ContinuousOn (fun t => F t (A t)) (Icc t₀ t₁))
    (ha' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => F t (A t)) (a₂ s) (Ici s) s)
    (hM₂ : ∀ s ∈ Ico t₀ t₁, ‖a₂ s‖ ≤ M₂) {Ystar : E} (hfix : R Ystar = Ystar) {μ : ℝ}
    (hμ : ‖Ystar - A t₁‖ ≤ μ) {YS : ℝ → E}
    (hS : ODESolution (fun t x => R (F t x)) YS t₀ t₁) (hS₀ : YS t₀ = A t₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (μ + M₂ * h ^ 2) + μ := by
  have hθ : ‖A t₁ - R (A t₁)‖ ≤ μ :=
    (hR.norm_sub_le_of_mem_range (A t₁) Ystar hfix).trans (by rwa [norm_sub_rev])
  have hρ := MidpointBUG.interior_capture hR ht₁ hh hA hRA ha ha' hM₂ hθ
  exact MidpointBUG.galerkin_step_error_interior hR hF hL ht₁ hh hA hS (by rw [hS₀, hRA]) hρ hθ

/-- The bound of `galerkin_error_of_predictor` as a local error in the sense of
`HasLocalError`: every exact solution that starts at `A(t₀)` agrees with `A` at `t₁`
(uniqueness, `ODESolution.norm_sub_le_exp`). -/
theorem hasLocalError_of_predictor {R : E →L[ℝ] E} (hR : IsOrthProj R)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hRA : R (A t₀) = A t₀) {a₂ : ℝ → E} {M₂ : ℝ}
    (ha : ContinuousOn (fun t => F t (A t)) (Icc t₀ t₁))
    (ha' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => F t (A t)) (a₂ s) (Ici s) s)
    (hM₂ : ∀ s ∈ Ico t₀ t₁, ‖a₂ s‖ ≤ M₂) {Ystar : E} (hfix : R Ystar = Ystar) {μ : ℝ}
    (hμ : ‖Ystar - A t₁‖ ≤ μ) {YS : ℝ → E}
    (hS : ODESolution (fun t x => R (F t x)) YS t₀ t₁) (hS₀ : YS t₀ = A t₀) :
    HasLocalError F t₀ t₁ (A t₀) (YS t₁)
      ((Real.exp (L * h) - 1) * (μ + M₂ * h ^ 2) + μ) := by
  intro Φ hΦ hΦ₀
  have hle : t₀ ≤ t₁ := by linarith
  have hd := ODESolution.norm_sub_le_exp hF hL hΦ hA t₁ (right_mem_Icc.2 hle)
  rw [hΦ₀, sub_self, norm_zero, mul_zero] at hd
  rw [sub_eq_zero.1 (norm_le_zero_iff.1 hd)]
  exact galerkin_error_of_predictor hR hF hL ht₁ hh hA hRA ha ha' hM₂ hfix hμ hS hS₀

/-- **Exact capture of the endpoint.**  If the orthogonal projector `R` fixes `A(t₀)` and
`A(t₁)`, the Galerkin step has error at most `(e^{L h} - 1) M₂ h²`, with no singular value and
no normal component in the bound.  This is `galerkin_error_of_predictor` with `Y⋆ = A(t₁)` and
`μ = 0`. -/
theorem galerkin_error_of_capture {R : E →L[ℝ] E} (hR : IsOrthProj R)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hRA : R (A t₀) = A t₀) {a₂ : ℝ → E} {M₂ : ℝ}
    (ha : ContinuousOn (fun t => F t (A t)) (Icc t₀ t₁))
    (ha' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => F t (A t)) (a₂ s) (Ici s) s)
    (hM₂ : ∀ s ∈ Ico t₀ t₁, ‖a₂ s‖ ≤ M₂) (hcap : R (A t₁) = A t₁) {YS : ℝ → E}
    (hS : ODESolution (fun t x => R (F t x)) YS t₀ t₁) (hS₀ : YS t₀ = A t₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (M₂ * h ^ 2) := by
  have hb := galerkin_error_of_predictor hR hF hL ht₁ hh hA hRA ha ha' hM₂ hcap (μ := 0)
    (by rw [sub_self, norm_zero]) hS hS₀
  rwa [zero_add, add_zero] at hb

end Predictor

/-! ### The data of the example -/

namespace Examples

/-- The polynomial field `F(Y) = (E₂₁ + Y₁₂ E₃₁) Y + Y E₁₂` on `3 × 2` matrices (entries of the
unit matrices counted from one).  It has the form `𝒜(Y) Y + Y ℬ` (`rowField_eq`), and its
normal component vanishes at every rank-one point (`rowField_normal`). -/
noncomputable def rowField (Y : Matrix (Fin 3) (Fin 2) ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  !![0, Y 0 0; Y 0 0, Y 0 1 + Y 1 0; Y 0 1 * Y 0 0, Y 0 1 * Y 0 1 + Y 2 0]

/-- The left factor `𝒜(Y) = E₂₁ + a E₃₁` of `rowField`, with `a = Y₁₂`. -/
noncomputable def rowFieldLeft (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0; 1, 0, 0; a, 0, 0]

/-- The right factor `ℬ = E₁₂` of `rowField`. -/
noncomputable def rowFieldRight : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- The starting left basis `U₀ = e₁ ∈ ℝ³`. -/
noncomputable def startLeft : Matrix (Fin 3) (Fin 1) ℝ := !![1; 0; 0]

/-- The starting right basis `V₀ = e₁ ∈ ℝ²`. -/
noncomputable def startRight : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The direction `e₂ ∈ ℝ³` of the K-step. -/
private noncomputable def kDirection : Matrix (Fin 3) (Fin 1) ℝ := !![0; 1; 0]

/-- The direction `e₂ ∈ ℝ²` of the L-step. -/
private noncomputable def lDirection : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]

/-- Coefficient of `1` in the exact solution: the starting value `Y₀ = e₁ e₁ᵀ`. -/
private noncomputable def exactCoeff0 : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 0; 0, 0]

/-- Coefficient of `t` in the exact solution. -/
private noncomputable def exactCoeff1 : Matrix (Fin 3) (Fin 2) ℝ := !![0, 1; 1, 0; 0, 0]

/-- Coefficient of `t²` in the exact solution. -/
private noncomputable def exactCoeff2 : Matrix (Fin 3) (Fin 2) ℝ := !![0, 0; 0, 1; 1 / 2, 0]

/-- Coefficient of `t³` in the exact solution. -/
private noncomputable def exactCoeff3 : Matrix (Fin 3) (Fin 2) ℝ := !![0, 0; 0, 0; 0, 1 / 2]

/-- The exact solution `A(t) = (1, t, t²/2)ᵀ (1, t)` of `A' = rowField A`, `A(0) = e₁ e₁ᵀ`. -/
noncomputable def exactSolution (t : ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  exactCoeff0 + t • exactCoeff1 + t ^ 2 • exactCoeff2 + t ^ 3 • exactCoeff3

/-- The K-step solution `K(t) = (1, t, 0)ᵀ`. -/
noncomputable def kSolution (t : ℝ) : Matrix (Fin 3) (Fin 1) ℝ := startLeft + t • kDirection

/-- The L-step solution `L(t) = (1, t)ᵀ`. -/
noncomputable def lSolution (t : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := startRight + t • lDirection

/-- The augmented left basis `Û = [e₁, e₂]`, an orthonormal basis of the range of
`[U₀, K(h)]` for `h ≠ 0`. -/
noncomputable def augmentedLeft : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; 0, 0]

/-- Coefficient of `1` in the Galerkin solution. -/
private noncomputable def galerkinCoeff0 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- Coefficient of `t` in the Galerkin solution. -/
private noncomputable def galerkinCoeff1 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- Coefficient of `t²` in the Galerkin solution. -/
private noncomputable def galerkinCoeff2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]

/-- The Galerkin solution `Ŝ(t) = [[1, t], [t, t²]]` in the bases `Û = [e₁, e₂]`, `V̂ = I₂`. -/
noncomputable def galerkinSolution (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  galerkinCoeff0 + t • galerkinCoeff1 + t ^ 2 • galerkinCoeff2

end Examples

open Examples

/-- The starting left basis has an orthonormal column. -/
theorem startLeft_orth : startLeftᵀ * startLeft = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [startLeft, Matrix.mul_apply, Fin.sum_univ_three]

/-- The starting right basis has an orthonormal column. -/
theorem startRight_orth : startRightᵀ * startRight = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [startRight, Matrix.mul_apply]

/-- Non-vacuity of `galerkin_error_of_predictor` with nonzero data: the constant field
`F ≡ C₁`, the projector `R = U₀ U₀ᵀ ·` (which does not fix `C₁`), the exact solution
`Y₀ + t C₁`, the predictor `Y⋆ = Y₀` and the Galerkin solution `Y₀ + t R C₁`. -/
example (h : ℝ) (hh : 0 ≤ h) :
    ‖(startLeft * startRightᵀ + (h - 0) • leftProj startLeft exactCoeff1) -
        (startLeft * startRightᵀ + (h - 0) • exactCoeff1)‖ ≤
      (Real.exp (1 * h) - 1) *
          (‖startLeft * startRightᵀ - (startLeft * startRightᵀ + (h - 0) • exactCoeff1)‖ +
            1 * h ^ 2) +
        ‖startLeft * startRightᵀ - (startLeft * startRightᵀ + (h - 0) • exactCoeff1)‖ :=
  galerkin_error_of_predictor (F := fun _ _ => exactCoeff1)
    (A := fun t => startLeft * startRightᵀ + (t - 0) • exactCoeff1)
    (YS := fun t => startLeft * startRightᵀ + (t - 0) • leftProj startLeft exactCoeff1)
    (a₂ := fun _ => 0) (t₀ := 0) (t₁ := h) (isOrthProj_leftProj startLeft_orth)
    (fun _ _ _ => by simp) zero_le_one (zero_add h).symm hh
    (MatrixBUG.odeSolution_affine _ _ _ _)
    (by simpa using leftProj_mul_left (n := Fin 2) startLeft_orth startRightᵀ) continuousOn_const
    (fun s _ => hasDerivWithinAt_const s (Ici s) exactCoeff1) (fun _ _ => by simp)
    (leftProj_mul_left startLeft_orth startRightᵀ) le_rfl
    (MatrixBUG.odeSolution_affine _ _ _ _) (by simp)

/-- Non-vacuity of `hasLocalError_of_predictor` on the same data. -/
example (h : ℝ) (hh : 0 ≤ h) :
    HasLocalError (fun _ _ => exactCoeff1) 0 h
      (startLeft * startRightᵀ + ((0 : ℝ) - 0) • exactCoeff1)
      (startLeft * startRightᵀ + (h - 0) • leftProj startLeft exactCoeff1)
      ((Real.exp (1 * h) - 1) *
          (‖startLeft * startRightᵀ - (startLeft * startRightᵀ + (h - 0) • exactCoeff1)‖ +
            1 * h ^ 2) +
        ‖startLeft * startRightᵀ - (startLeft * startRightᵀ + (h - 0) • exactCoeff1)‖) :=
  hasLocalError_of_predictor (F := fun _ _ => exactCoeff1)
    (A := fun t => startLeft * startRightᵀ + (t - 0) • exactCoeff1)
    (YS := fun t => startLeft * startRightᵀ + (t - 0) • leftProj startLeft exactCoeff1)
    (a₂ := fun _ => 0) (t₀ := 0) (t₁ := h) (isOrthProj_leftProj startLeft_orth)
    (fun _ _ _ => by simp) zero_le_one (zero_add h).symm hh
    (MatrixBUG.odeSolution_affine _ _ _ _)
    (by simpa using leftProj_mul_left (n := Fin 2) startLeft_orth startRightᵀ) continuousOn_const
    (fun s _ => hasDerivWithinAt_const s (Ici s) exactCoeff1) (fun _ _ => by simp)
    (leftProj_mul_left startLeft_orth startRightᵀ) le_rfl
    (MatrixBUG.odeSolution_affine _ _ _ _) (by simp)

/-- Non-vacuity of `galerkin_error_of_capture` with nonzero data: the constant field
`F ≡ U₀ V₀ᵀ`, the projector `R = U₀ U₀ᵀ ·`, the exact solution `(1 + t) U₀ V₀ᵀ`, which stays
in the range of `R`. -/
example (h : ℝ) (hh : 0 ≤ h) :
    ‖(startLeft * startRightᵀ + (h - 0) • leftProj startLeft (startLeft * startRightᵀ)) -
        (startLeft * startRightᵀ + (h - 0) • (startLeft * startRightᵀ))‖ ≤
      (Real.exp (1 * h) - 1) * (1 * h ^ 2) :=
  galerkin_error_of_capture (F := fun _ _ => startLeft * startRightᵀ)
    (A := fun t => startLeft * startRightᵀ + (t - 0) • (startLeft * startRightᵀ))
    (YS := fun t =>
      startLeft * startRightᵀ + (t - 0) • leftProj startLeft (startLeft * startRightᵀ))
    (a₂ := fun _ => 0) (t₀ := 0) (t₁ := h) (isOrthProj_leftProj startLeft_orth)
    (fun _ _ _ => by simp) zero_le_one (zero_add h).symm hh
    (MatrixBUG.odeSolution_affine _ _ _ _)
    (by simpa using leftProj_mul_left (n := Fin 2) startLeft_orth startRightᵀ) continuousOn_const
    (fun s _ => hasDerivWithinAt_const s (Ici s) (startLeft * startRightᵀ))
    (fun _ _ => by simp)
    (by simp only [map_add, map_smul, leftProj_mul_left (n := Fin 2) startLeft_orth startRightᵀ])
    (MatrixBUG.odeSolution_affine _ _ _ _) (by simp)

/-! ### A lower bound for the K-step basis with two columns -/

section Barrier

open MatrixBUG

/-- `rowField Y = 𝒜(Y) Y + Y ℬ` with `𝒜(Y) = E₂₁ + Y₁₂ E₃₁` and `ℬ = E₁₂`. -/
theorem rowField_eq (Y : Matrix (Fin 3) (Fin 2) ℝ) :
    rowField Y = rowFieldLeft (Y 0 1) * Y + Y * rowFieldRight := by
  ext i j
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [rowField, rowFieldLeft, rowFieldRight]

/-- **The normal component of the field vanishes at every rank-one point**: at every factored
point `U S Vᵀ` with orthonormal `U`, `V`. -/
theorem rowField_normal {U : Matrix (Fin 3) (Fin 1) ℝ} {V : Matrix (Fin 2) (Fin 1) ℝ}
    (S : Matrix (Fin 1) (Fin 1) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    (1 - U * Uᵀ) * rowField (U * S * Vᵀ) * (1 - V * Vᵀ) = 0 := by
  have hl : ∀ X : Matrix (Fin 1) (Fin 2) ℝ, (1 - U * Uᵀ) * (U * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc U, hU,
      Matrix.mul_one, sub_self, Matrix.zero_mul]
  have hr : Vᵀ * (1 - V * Vᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hV, Matrix.one_mul, sub_self]
  rw [rowField_eq, Matrix.mul_add, Matrix.add_mul]
  simp only [Matrix.mul_assoc, hl, hr, Matrix.mul_zero, Matrix.zero_mul, add_zero]

/-- The normal bound of the rank-one manifold holds with `ε = 0` on the whole space. -/
theorem factoredNormalBoundOn_rowField :
    FactoredNormalBoundOn (fun _ => rowField) 1 Set.univ 0 := fun _ U V S hU hV _ => by
  rw [rowField_normal S hU hV, norm_zero]

/-- The exact solution has the derivative `rowField (A t)`. -/
private theorem hasDerivAt_exactSolution (t : ℝ) :
    HasDerivAt exactSolution (rowField (exactSolution t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => s • exactCoeff1) exactCoeff1 t := by
    simpa using (hasDerivAt_id t).smul_const exactCoeff1
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2 • exactCoeff2) ((2 * t) • exactCoeff2) t := by
    simpa using (hasDerivAt_pow 2 t).smul_const exactCoeff2
  have h3 : HasDerivAt (fun s : ℝ => s ^ 3 • exactCoeff3) ((3 * t ^ 2) • exactCoeff3) t := by
    simpa using (hasDerivAt_pow 3 t).smul_const exactCoeff3
  have he : rowField (exactSolution t) =
      exactCoeff1 + (2 * t) • exactCoeff2 + (3 * t ^ 2) • exactCoeff3 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rowField, exactSolution, exactCoeff0, exactCoeff1, exactCoeff2, exactCoeff3] <;>
      ring
  rw [he]
  exact ((h1.const_add exactCoeff0).add h2).add h3

/-- `A` solves `A' = rowField A` on every interval `[0, h]`. -/
theorem odeSolution_exactSolution (h : ℝ) :
    ODESolution (fun _ => rowField) exactSolution 0 h where
  cont := fun t _ => (hasDerivAt_exactSolution t).continuousAt.continuousWithinAt
  deriv := fun t _ => (hasDerivAt_exactSolution t).hasDerivWithinAt

/-- `A(0) = U₀ S₀ V₀ᵀ` with `S₀ = 1`: a rank-one matrix with singular value `1`. -/
theorem exactSolution_zero :
    exactSolution 0 = startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ := by
  rw [Matrix.mul_one]
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_one]
  fin_cases i <;> fin_cases j <;> simp [exactSolution, exactCoeff0, startLeft, startRight]

/-- **Evaluations with the row space of the start do not see the third row.**  If `M` has a
zero third entry, then `rowField (M V₀ᵀ)` has a zero third row.  The K-step equation
(`MatrixBUG.kField`) evaluates the field only at matrices of the form `K V₀ᵀ`. -/
theorem rowField_mul_row_two {M : Matrix (Fin 3) (Fin 1) ℝ} (hM : M 2 0 = 0) (j : Fin 2) :
    rowField (M * startRightᵀ) 2 j = 0 := by
  fin_cases j <;> simp [rowField, startRight, Matrix.mul_apply, hM]

/-- On this example the K-step field is linear: `F(K V₀ᵀ) V₀ = E₂₁ K`. -/
theorem kField_rowField (t : ℝ) (K : Matrix (Fin 3) (Fin 1) ℝ) :
    kField startRight (fun _ => rowField) t K = rowFieldLeft 0 * K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kField, rowField, rowFieldLeft, startRight, Matrix.mul_apply, Fin.sum_univ_three]

/-- `K(t) = (1, t, 0)ᵀ` solves the K-step equation. -/
theorem odeSolution_kSolution (h : ℝ) :
    ODESolution (kField startRight fun _ => rowField) kSolution 0 h := by
  have hd : ∀ t : ℝ,
      HasDerivAt kSolution (kField startRight (fun _ => rowField) t (kSolution t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s • kDirection) kDirection t := by
      simpa using (hasDerivAt_id t).smul_const kDirection
    have he : kField startRight (fun _ => rowField) t (kSolution t) = kDirection := by
      rw [kField_rowField]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [rowFieldLeft, kSolution, startLeft, kDirection, Matrix.mul_apply,
          Fin.sum_univ_three]
    rw [he]
    exact h1.const_add startLeft
  exact ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => (hd t).hasDerivWithinAt⟩

/-- **The K-step of the example.**  Every solution of the K-step equation that starts at
`U₀ S₀` is `K(t) = (1, t, 0)ᵀ` (uniqueness, `ODESolution.norm_sub_le_exp`). -/
theorem eq_kSolution_of_odeSolution {h : ℝ} {K : ℝ → Matrix (Fin 3) (Fin 1) ℝ}
    (hK : ODESolution (kField startRight fun _ => rowField) K 0 h)
    (hK₀ : K 0 = startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ)) :
    ∀ t ∈ Icc (0 : ℝ) h, K t = kSolution t := by
  have hF : IsLipschitzField (kField startRight fun _ => rowField) ‖rowFieldLeft 0‖ :=
    fun t x y => by
      rw [kField_rowField, kField_rowField, ← Matrix.mul_sub]
      exact Frobenius.norm_mul_le _ _
  intro t ht
  have hd := ODESolution.norm_sub_le_exp hF (norm_nonneg _) hK (odeSolution_kSolution h) t ht
  have h0 : K 0 - kSolution 0 = 0 := by
    rw [hK₀]
    simp [kSolution]
  rw [h0, norm_zero, mul_zero] at hd
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hd)

/-- **Lower bound for a left factor with a zero third row.**  Every matrix `Û C` whose left
factor has a zero third row has distance at least `h² / 2` from the exact solution `A(h)`: the
entry `(3, 1)` of `A(h)` is `h² / 2`. -/
theorem error_ge_of_row_two_eq_zero {k : Type*} [Fintype k] {Uh : Matrix (Fin 3) k ℝ}
    (hUh : ∀ j, Uh 2 j = 0) (C : Matrix k (Fin 2) ℝ) (h : ℝ) :
    h ^ 2 / 2 ≤ ‖Uh * C - exactSolution h‖ := by
  have h20 : (Uh * C - exactSolution h) 2 0 = -(h ^ 2 / 2) := by
    simp [Matrix.mul_apply, hUh, exactSolution, exactCoeff0, exactCoeff1, exactCoeff2,
      exactCoeff3]
    ring
  have hle := Frobenius.abs_apply_le_norm (Uh * C - exactSolution h) 2 0
  rwa [h20, abs_neg, abs_of_nonneg (by positivity)] at hle

/-- An orthonormal two-column basis of `ℝ³` that captures `U₀ = e₁` and `K(h) = (1, h, 0)ᵀ`
with `h ≠ 0` has a zero third row (its range is `span(e₁, e₂)`): the projector `Û Ûᵀ` has
trace `2` and the diagonal entries `1`, `1`, so the third one, `Û₃₁² + Û₃₂²`, is zero. -/
theorem row_two_eq_zero_of_capture {h : ℝ} (hh : h ≠ 0) {Ua : Matrix (Fin 3) (Fin 2) ℝ}
    (hUa : Uaᵀ * Ua = 1) (h0 : Ua * Uaᵀ * startLeft = startLeft)
    (h1 : Ua * Uaᵀ * kSolution h = kSolution h) : ∀ j, Ua 2 j = 0 := by
  have u0 : startLeft 0 0 = 1 := by simp [startLeft]
  have u1 : startLeft 1 0 = 0 := by simp [startLeft]
  have u2 : startLeft 2 0 = 0 := by simp [startLeft]
  have k0 : kSolution h 0 0 = 1 := by simp [kSolution, startLeft, kDirection]
  have k1 : kSolution h 1 0 = h := by simp [kSolution, startLeft, kDirection]
  have k2 : kSolution h 2 0 = 0 := by simp [kSolution, startLeft, kDirection]
  have o0 := congrFun (congrFun hUa 0) 0
  have o1 := congrFun (congrFun hUa 1) 1
  have p0 := congrFun (congrFun h0 0) 0
  have p1 := congrFun (congrFun h0 1) 0
  have p2 := congrFun (congrFun h1 1) 0
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
    Matrix.one_apply_eq] at o0 o1
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Fin.sum_univ_two,
    u0, u1, u2] at p0 p1
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Fin.sum_univ_two,
    k0, k1, k2] at p2
  have hc : (Ua 1 0 ^ 2 + Ua 1 1 ^ 2 - 1) * h = 0 := by linear_combination p2 - p1
  have hc' : Ua 1 0 ^ 2 + Ua 1 1 ^ 2 - 1 = 0 := (mul_eq_zero.1 hc).resolve_right hh
  have hs : Ua 2 0 ^ 2 + Ua 2 1 ^ 2 = 0 := by linear_combination o0 + o1 - p0 - hc'
  have a0 : Ua 2 0 ^ 2 = 0 := by linarith [sq_nonneg (Ua 2 0), sq_nonneg (Ua 2 1)]
  have a1 : Ua 2 1 ^ 2 = 0 := by linarith [sq_nonneg (Ua 2 0), sq_nonneg (Ua 2 1)]
  exact Fin.forall_fin_two.2
    ⟨(pow_eq_zero_iff two_ne_zero).1 a0, (pow_eq_zero_iff two_ne_zero).1 a1⟩

/-- **Lower bound for the rank-adaptive BUG step with a two-column left basis.**  For the
field `rowField` (zero normal component, `factoredNormalBoundOn_rowField`) and the start
`Y₀ = e₁ e₁ᵀ` (rank one, singular value `1`), every rank-adaptive BUG step
(Ceruti–Kusch–Lubich, arXiv:2104.05247; `MatrixBUG.IsRankAdaptiveStep`) with a two-column
left basis `Û`, any right basis `V̂` and any truncation tolerance `ϑ` has error at least
`h² / 2 - ϑ` at `t₁ = h`. -/
theorem error_ge_of_isRankAdaptiveStep {h ϑ : ℝ} (hh : 0 < h) {k' : Type*} [Fintype k']
    [DecidableEq k'] {Ua : Matrix (Fin 3) (Fin 2) ℝ} {Va : Matrix (Fin 2) k' ℝ}
    {K : ℝ → Matrix (Fin 3) (Fin 1) ℝ} {Lf : ℝ → Matrix (Fin 2) (Fin 1) ℝ}
    {Sa : ℝ → Matrix (Fin 2) k' ℝ} {Y₁ : Matrix (Fin 3) (Fin 2) ℝ}
    (hstep : IsRankAdaptiveStep (fun _ => rowField) ϑ 0 h startLeft 1 startRight Ua Va K Lf Sa
      Y₁) :
    h ^ 2 / 2 - ϑ ≤ ‖Y₁ - exactSolution h‖ := by
  have hK := eq_kSolution_of_odeSolution hstep.kSol hstep.kStart h (right_mem_Icc.2 hh.le)
  have hrow := row_two_eq_zero_of_capture hh.ne' hstep.orthUa hstep.augU (hK ▸ hstep.kCap)
  have hlow := error_ge_of_row_two_eq_zero hrow (Sa h * Vaᵀ) h
  have htri : ‖Ua * (Sa h * Vaᵀ) - exactSolution h‖ ≤
      ‖Y₁ - Ua * Sa h * Vaᵀ‖ + ‖Y₁ - exactSolution h‖ := by
    rw [← Matrix.mul_assoc, norm_sub_rev Y₁ (Ua * Sa h * Vaᵀ)]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  linarith [hstep.trunc]

/-- The lower bound as a statement about `HasLocalError`: no rank-adaptive BUG step with a
two-column left basis `Û` on this problem has a local error bound below `h² / 2 - ϑ`. -/
theorem not_hasLocalError_of_isRankAdaptiveStep {h ϑ δ : ℝ} (hh : 0 < h) {k' : Type*}
    [Fintype k'] [DecidableEq k'] {Ua : Matrix (Fin 3) (Fin 2) ℝ} {Va : Matrix (Fin 2) k' ℝ}
    {K : ℝ → Matrix (Fin 3) (Fin 1) ℝ} {Lf : ℝ → Matrix (Fin 2) (Fin 1) ℝ}
    {Sa : ℝ → Matrix (Fin 2) k' ℝ} {Y₁ : Matrix (Fin 3) (Fin 2) ℝ}
    (hstep : IsRankAdaptiveStep (fun _ => rowField) ϑ 0 h startLeft 1 startRight Ua Va K Lf Sa
      Y₁)
    (hδ : δ < h ^ 2 / 2 - ϑ) :
    ¬ HasLocalError (fun _ => rowField) 0 h
      (startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ) Y₁ δ := fun hloc => by
  have h1 := hloc exactSolution (odeSolution_exactSolution h) exactSolution_zero
  have h2 := error_ge_of_isRankAdaptiveStep hh hstep
  linarith

/-- The augmented left basis has orthonormal columns. -/
private theorem augmentedLeft_orth : augmentedLeftᵀ * augmentedLeft = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [augmentedLeft, Matrix.mul_apply, Fin.sum_univ_three]

/-- On this example the L-step field is `L ↦ (0, L₁)ᵀ`. -/
private theorem lField_rowField (t : ℝ) (L : Matrix (Fin 2) (Fin 1) ℝ) :
    lField startLeft (fun _ => rowField) t L = L 0 0 • lDirection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lField, rowField, startLeft, lDirection, Matrix.mul_apply, Fin.sum_univ_three]

/-- `L(t) = (1, t)ᵀ` solves the L-step equation. -/
private theorem odeSolution_lSolution (h : ℝ) :
    ODESolution (lField startLeft fun _ => rowField) lSolution 0 h := by
  have hd : ∀ t : ℝ,
      HasDerivAt lSolution (lField startLeft (fun _ => rowField) t (lSolution t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s • lDirection) lDirection t := by
      simpa using (hasDerivAt_id t).smul_const lDirection
    have he : lField startLeft (fun _ => rowField) t (lSolution t) = lDirection := by
      rw [lField_rowField]
      simp [lSolution, startRight, lDirection]
    rw [he]
    exact h1.const_add startRight
  exact ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => (hd t).hasDerivWithinAt⟩

/-- `Ŝ(t) = [[1, t], [t, t²]]` solves the Galerkin equation in the bases `Û = [e₁, e₂]`,
`V̂ = I₂`. -/
private theorem odeSolution_galerkinSolution (h : ℝ) :
    ODESolution (sField augmentedLeft (1 : Matrix (Fin 2) (Fin 2) ℝ) fun _ => rowField)
      galerkinSolution 0 h := by
  have hd : ∀ t : ℝ, HasDerivAt galerkinSolution
      (sField augmentedLeft (1 : Matrix (Fin 2) (Fin 2) ℝ) (fun _ => rowField) t
        (galerkinSolution t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s • galerkinCoeff1) galerkinCoeff1 t := by
      simpa using (hasDerivAt_id t).smul_const galerkinCoeff1
    have h2 : HasDerivAt (fun s : ℝ => s ^ 2 • galerkinCoeff2) ((2 * t) • galerkinCoeff2) t := by
      simpa using (hasDerivAt_pow 2 t).smul_const galerkinCoeff2
    have he : sField augmentedLeft (1 : Matrix (Fin 2) (Fin 2) ℝ) (fun _ => rowField) t
        (galerkinSolution t) = galerkinCoeff1 + (2 * t) • galerkinCoeff2 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sField, rowField, augmentedLeft, galerkinSolution, galerkinCoeff0, galerkinCoeff1,
          galerkinCoeff2, Matrix.mul_apply, Fin.sum_univ_three]
      ring
    rw [he]
    exact (h1.const_add galerkinCoeff0).add h2
  exact ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => (hd t).hasDerivWithinAt⟩

/-- **The lower bound is not vacuous**: the explicit step with `K(t) = (1, t, 0)ᵀ`,
`L(t) = (1, t)ᵀ`, `Û = [e₁, e₂]`, `V̂ = I₂`, `Ŝ(t) = [[1, t], [t, t²]]` and no truncation is a
rank-adaptive BUG step for `rowField` from `Y₀ = e₁ e₁ᵀ`. -/
theorem isRankAdaptiveStep_example (h : ℝ) :
    IsRankAdaptiveStep (fun _ => rowField) 0 0 h startLeft 1 startRight augmentedLeft
      (1 : Matrix (Fin 2) (Fin 2) ℝ) kSolution lSolution galerkinSolution
      (augmentedLeft * galerkinSolution h * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ) where
  orthU₀ := startLeft_orth
  orthV₀ := startRight_orth
  kSol := odeSolution_kSolution h
  kStart := by simp [kSolution]
  lSol := odeSolution_lSolution h
  lStart := by simp [lSolution]
  orthUa := augmentedLeft_orth
  kCap := by
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.transpose_apply]
    fin_cases i <;> fin_cases j <;> simp [augmentedLeft, kSolution, startLeft, kDirection]
  augU := by
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.transpose_apply]
    fin_cases i <;> fin_cases j <;> simp [augmentedLeft, startLeft]
  orthVa := by simp
  lCap := by simp
  augV := by simp
  sSol := odeSolution_galerkinSolution h
  sStart := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [galerkinSolution, galerkinCoeff0, augmentedLeft, startLeft, startRight,
        Matrix.mul_apply, Fin.sum_univ_three]
  trunc := by simp

/-- The explicit step of `isRankAdaptiveStep_example` has error at least `h² / 2`
(`error_ge_of_isRankAdaptiveStep` applied to nonzero data). -/
example (h : ℝ) (hh : 0 < h) :
    h ^ 2 / 2 - 0 ≤
      ‖augmentedLeft * galerkinSolution h * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ - exactSolution h‖ :=
  error_ge_of_isRankAdaptiveStep hh (isRankAdaptiveStep_example h)

/-- Non-vacuity of `not_hasLocalError_of_isRankAdaptiveStep`: the explicit step has no local
error bound `h² / 4`. -/
example (h : ℝ) (hh : 0 < h) :
    ¬ HasLocalError (fun _ => rowField) 0 h
      (startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ)
      (augmentedLeft * galerkinSolution h * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ) (h ^ 2 / 4) :=
  not_hasLocalError_of_isRankAdaptiveStep hh (isRankAdaptiveStep_example h)
    (by have := pow_pos hh 2; linarith)

/-- **The lower bound without the names of the example.**  There are a field `F` on `3 × 2`
matrices whose normal component `(1 - U Uᵀ) F(U S Vᵀ) (1 - V Vᵀ)` vanishes at every rank-one
point (`FactoredNormalBoundOn` with `ε = 0` on the whole space), a rank-one start
`Y₀ = U₀ V₀ᵀ` with orthonormal factors and singular value `1`, and an exact solution `A` of
`A' = F(A)`, `A(0) = Y₀`, on every interval `[0, h]`, such that

* for every `h` there is a rank-adaptive BUG step (`MatrixBUG.IsRankAdaptiveStep`) from `Y₀`
  with a two-column left basis and tolerance `0`, and
* for every `h > 0` and every `ϑ`, every rank-adaptive BUG step from `Y₀` with a two-column
  left basis `Û`, any right basis `V̂` and tolerance `ϑ` has error at least `h² / 2 - ϑ`.

The witnesses are `rowField`, `startLeft`, `startRight` and `exactSolution`
(`error_ge_of_isRankAdaptiveStep`, `isRankAdaptiveStep_example`). -/
theorem exists_error_ge_of_isRankAdaptiveStep.{u} :
    ∃ (F : Matrix (Fin 3) (Fin 2) ℝ → Matrix (Fin 3) (Fin 2) ℝ)
      (U₀ : Matrix (Fin 3) (Fin 1) ℝ) (V₀ : Matrix (Fin 2) (Fin 1) ℝ)
      (A : ℝ → Matrix (Fin 3) (Fin 2) ℝ),
      FactoredNormalBoundOn (fun _ => F) 1 Set.univ 0 ∧
      U₀ᵀ * U₀ = 1 ∧ V₀ᵀ * V₀ = 1 ∧ A 0 = U₀ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * V₀ᵀ ∧
      (∀ h : ℝ, ODESolution (fun _ => F) A 0 h) ∧
      (∀ h : ℝ, ∃ (Ua : Matrix (Fin 3) (Fin 2) ℝ) (Va : Matrix (Fin 2) (Fin 2) ℝ)
        (K : ℝ → Matrix (Fin 3) (Fin 1) ℝ) (Lf : ℝ → Matrix (Fin 2) (Fin 1) ℝ)
        (Sa : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (Y₁ : Matrix (Fin 3) (Fin 2) ℝ),
        IsRankAdaptiveStep (fun _ => F) 0 0 h U₀ 1 V₀ Ua Va K Lf Sa Y₁) ∧
      ∀ (h ϑ : ℝ), 0 < h → ∀ (k' : Type u) [Fintype k'] [DecidableEq k']
        (Ua : Matrix (Fin 3) (Fin 2) ℝ) (Va : Matrix (Fin 2) k' ℝ)
        (K : ℝ → Matrix (Fin 3) (Fin 1) ℝ) (Lf : ℝ → Matrix (Fin 2) (Fin 1) ℝ)
        (Sa : ℝ → Matrix (Fin 2) k' ℝ) (Y₁ : Matrix (Fin 3) (Fin 2) ℝ),
        IsRankAdaptiveStep (fun _ => F) ϑ 0 h U₀ 1 V₀ Ua Va K Lf Sa Y₁ →
        h ^ 2 / 2 - ϑ ≤ ‖Y₁ - A h‖ :=
  ⟨rowField, startLeft, startRight, exactSolution, factoredNormalBoundOn_rowField,
    startLeft_orth, startRight_orth, exactSolution_zero, odeSolution_exactSolution,
    fun h => ⟨augmentedLeft, 1, kSolution, lSolution, galerkinSolution, _,
      isRankAdaptiveStep_example h⟩,
    fun _ _ hh _ _ _ _ _ _ _ _ _ hstep => error_ge_of_isRankAdaptiveStep hh hstep⟩

end Barrier

/-! ### Fields of Sylvester type -/

section Sylvester

open MatrixBUG

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k'] [DecidableEq k]
  [DecidableEq k'] {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {𝒜 : ℝ → Matrix m m ℝ}
  {ℬ : ℝ → Matrix n n ℝ} {t₀ t₁ : ℝ} {U₀ : Matrix m (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}

/-- For a field of Sylvester type, `F(t, Y) = 𝒜(t) Y + Y ℬ(t)`, the K-step equation is linear:
`K' = 𝒜(t) K + K (V₀ᵀ ℬ(t) V₀)`. -/
theorem kField_of_sylvester (hFS : ∀ t Y, F t Y = 𝒜 t * Y + Y * ℬ t) (hV₀ : V₀ᵀ * V₀ = 1)
    (t : ℝ) (K : Matrix m (Fin r) ℝ) :
    kField V₀ F t K = 𝒜 t * K + K * (V₀ᵀ * ℬ t * V₀) := by
  rw [kField, hFS, Matrix.add_mul]
  simp only [Matrix.mul_assoc]
  rw [hV₀, Matrix.mul_one]

/-- For a field of Sylvester type the transposed L-step equation is linear:
`(Lᵀ)' = (U₀ᵀ 𝒜(t) U₀) Lᵀ + Lᵀ ℬ(t)`. -/
theorem transpose_lField_of_sylvester (hFS : ∀ t Y, F t Y = 𝒜 t * Y + Y * ℬ t)
    (hU₀ : U₀ᵀ * U₀ = 1) (t : ℝ) (Lm : Matrix n (Fin r) ℝ) :
    (lField U₀ F t Lm)ᵀ = U₀ᵀ * 𝒜 t * U₀ * Lmᵀ + Lmᵀ * ℬ t := by
  rw [lField, hFS, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U₀ᵀ U₀, hU₀, Matrix.one_mul]

/-- **The K-step solution carries the column space of the exact solution.**  For a field of
Sylvester type, if `K` solves the K-step equation and `P` solves the linear equation
`P' = P ℬ(t) - (V₀ᵀ ℬ(t) V₀) P`, then `K P` solves `A' = F(t, A)`. -/
theorem odeSolution_kCurve (hFS : ∀ t Y, F t Y = 𝒜 t * Y + Y * ℬ t) (hV₀ : V₀ᵀ * V₀ = 1)
    {K : ℝ → Matrix m (Fin r) ℝ} (hK : ODESolution (kField V₀ F) K t₀ t₁)
    {P : ℝ → Matrix (Fin r) n ℝ}
    (hP : ODESolution (fun t X => X * ℬ t - V₀ᵀ * ℬ t * V₀ * X) P t₀ t₁) :
    ODESolution F (fun t => K t * P t) t₀ t₁ where
  cont := ((Frobenius.mulCLM (m := m) (l := Fin r) (n := n)).continuous.comp_continuousOn
    hK.cont).clm_apply hP.cont
  deriv t ht := by
    refine (Frobenius.hasDerivWithinAt_mul (hK.deriv t ht) (hP.deriv t ht)).congr_deriv ?_
    simp only [hFS, kField_of_sylvester hFS hV₀, Matrix.add_mul, Matrix.mul_sub,
      Matrix.mul_assoc]
    abel

/-- **The L-step solution carries the row space of the exact solution.**  For a field of
Sylvester type, if `L` solves the L-step equation and `Q` solves the linear equation
`Q' = 𝒜(t) Q - Q (U₀ᵀ 𝒜(t) U₀)`, then `Q Lᵀ` solves `A' = F(t, A)`. -/
theorem odeSolution_lCurve (hFS : ∀ t Y, F t Y = 𝒜 t * Y + Y * ℬ t) (hU₀ : U₀ᵀ * U₀ = 1)
    {Lf : ℝ → Matrix n (Fin r) ℝ} (hLf : ODESolution (lField U₀ F) Lf t₀ t₁)
    {Q : ℝ → Matrix m (Fin r) ℝ}
    (hQ : ODESolution (fun t X => 𝒜 t * X - X * (U₀ᵀ * 𝒜 t * U₀)) Q t₀ t₁) :
    ODESolution F (fun t => Q t * (Lf t)ᵀ) t₀ t₁ where
  cont := ((Frobenius.mulCLM (m := m) (l := Fin r) (n := n)).continuous.comp_continuousOn
    hQ.cont).clm_apply
    ((Frobenius.transposeCLM (m := n) (n := Fin r)).continuous.comp_continuousOn hLf.cont)
  deriv t ht := by
    refine (Frobenius.hasDerivWithinAt_mul (hQ.deriv t ht)
      (Frobenius.hasDerivWithinAt_transpose (hLf.deriv t ht))).congr_deriv ?_
    simp only [hFS, transpose_lField_of_sylvester hFS hU₀, Matrix.sub_mul, Matrix.mul_add,
      Matrix.mul_assoc]
    abel

/-- For a Lipschitz field of Sylvester type the exact solution from `A(t₀) = K(t₀) V₀ᵀ` is
`A(t) = K(t) P(t)`, where `P` is the solution of `P' = P ℬ(t) - (V₀ᵀ ℬ(t) V₀) P` with
`P(t₀) = V₀ᵀ` (uniqueness, `ODESolution.eqOn`). -/
theorem eq_kStep_mul_of_sylvester {L : ℝ} (hFS : ∀ t Y, F t Y = 𝒜 t * Y + Y * ℬ t)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hV₀ : V₀ᵀ * V₀ = 1)
    {K : ℝ → Matrix m (Fin r) ℝ} (hK : ODESolution (kField V₀ F) K t₀ t₁)
    {P : ℝ → Matrix (Fin r) n ℝ}
    (hP : ODESolution (fun t X => X * ℬ t - V₀ᵀ * ℬ t * V₀ * X) P t₀ t₁) (hP₀ : P t₀ = V₀ᵀ)
    {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = K t₀ * V₀ᵀ) :
    ∀ t ∈ Icc t₀ t₁, A t = K t * P t := by
  have h0 : A t₀ = K t₀ * P t₀ := by rw [hA₀, hP₀]
  exact fun t ht => hA.eqOn (odeSolution_kCurve hFS hV₀ hK hP) hF hL h0 ht

/-- For a Lipschitz field of Sylvester type the exact solution from `A(t₀) = U₀ L(t₀)ᵀ` is
`A(t) = Q(t) L(t)ᵀ`, where `Q` is the solution of `Q' = 𝒜(t) Q - Q (U₀ᵀ 𝒜(t) U₀)` with
`Q(t₀) = U₀`. -/
theorem eq_mul_lStep_of_sylvester {L : ℝ} (hFS : ∀ t Y, F t Y = 𝒜 t * Y + Y * ℬ t)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hU₀ : U₀ᵀ * U₀ = 1)
    {Lf : ℝ → Matrix n (Fin r) ℝ} (hLf : ODESolution (lField U₀ F) Lf t₀ t₁)
    {Q : ℝ → Matrix m (Fin r) ℝ}
    (hQ : ODESolution (fun t X => 𝒜 t * X - X * (U₀ᵀ * 𝒜 t * U₀)) Q t₀ t₁) (hQ₀ : Q t₀ = U₀)
    {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * (Lf t₀)ᵀ) :
    ∀ t ∈ Icc t₀ t₁, A t = Q t * (Lf t)ᵀ := by
  have h0 : A t₀ = Q t₀ * (Lf t₀)ᵀ := by rw [hA₀, hQ₀]
  exact fun t ht => hA.eqOn (odeSolution_lCurve hFS hU₀ hLf hQ) hF hL h0 ht

variable {S₀ : Matrix (Fin r) (Fin r) ℝ} {Ua : Matrix m k ℝ} {Va : Matrix n k' ℝ}
  {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ} {Sa : ℝ → Matrix k k' ℝ}
  {Y₁ : Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {P : ℝ → Matrix (Fin r) n ℝ}
  {Q : ℝ → Matrix m (Fin r) ℝ} {L ϑ : ℝ}

/-- **The Galerkin space of a rank-adaptive BUG step contains the exact solution** when the
field is of Sylvester type, `F(t, Y) = 𝒜(t) Y + Y ℬ(t)`.  For every rank-adaptive BUG step
(`MatrixBUG.IsRankAdaptiveStep`) the augmented bases satisfy `Û Ûᵀ A(t₁) = A(t₁)` and
`A(t₁) V̂ V̂ᵀ = A(t₁)`: the range of `K(t₁)` contains the column space of `A(t₁)`, and the range
of `L(t₁)` contains its row space.  No singular value of the starting value enters.  The
solutions `P`, `Q` of the two auxiliary linear equations (`P(t₀) = V₀ᵀ`, `Q(t₀) = U₀`) are
hypotheses; they do not appear in the conclusion. -/
theorem capture_of_sylvester (hFS : ∀ t Y, F t Y = 𝒜 t * Y + Y * ℬ t)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁) (ht : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    (hPf : ODESolution (fun t X => X * ℬ t - V₀ᵀ * ℬ t * V₀ * X) P t₀ t₁) (hP₀ : P t₀ = V₀ᵀ)
    (hQf : ODESolution (fun t X => 𝒜 t * X - X * (U₀ᵀ * 𝒜 t * U₀)) Q t₀ t₁)
    (hQ₀ : Q t₀ = U₀) :
    Ua * Uaᵀ * A t₁ = A t₁ ∧ A t₁ * Va * Vaᵀ = A t₁ := by
  have hKP : A t₁ = K t₁ * P t₁ :=
    eq_kStep_mul_of_sylvester hFS hF hL hs.orthV₀ hs.kSol hPf hP₀ hA (by rw [hA₀, hs.kStart]) t₁
      (right_mem_Icc.2 ht)
  have hQL : A t₁ = Q t₁ * (Lf t₁)ᵀ :=
    eq_mul_lStep_of_sylvester hFS hF hL hs.orthU₀ hs.lSol hQf hQ₀ hA
      (by rw [hA₀, hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.mul_assoc]) t₁ (right_mem_Icc.2 ht)
  have hcapU : Ua * Uaᵀ * A t₁ = A t₁ := by rw [hKP, ← Matrix.mul_assoc, hs.kCap]
  have hT : (Lf t₁)ᵀ * Va * Vaᵀ = (Lf t₁)ᵀ := by
    have hc := congrArg Matrix.transpose hs.lCap
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      ← Matrix.mul_assoc] at hc
  have hcapV : A t₁ * Va * Vaᵀ = A t₁ := by
    rw [hQL, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Lf t₁)ᵀ, hT]
  exact ⟨hcapU, hcapV⟩

/-- `galerkinProj Ub Vb X = leftProj Ub (rightProj Vb X)`, by definition. -/
private theorem galerkinProj_eq {b b' : Type*} [Fintype b] [Fintype b'] (Ub : Matrix m b ℝ)
    (Vb : Matrix n b' ℝ) (X : Matrix m n ℝ) :
    galerkinProj Ub Vb X = leftProj Ub (rightProj Vb X) := rfl

/-- **Error of the rank-adaptive BUG step on fields of Sylvester type.**  Let
`F(t, Y) = 𝒜(t) Y + Y ℬ(t)` be `L`-Lipschitz, let `A` be the exact solution from
`Y₀ = U₀ S₀ V₀ᵀ`, and let `t ↦ F(t, A(t))` have a derivative bounded by `M₂`.  Then every step
of the rank-adaptive BUG integrator (Ceruti–Kusch–Lubich, arXiv:2104.05247;
`MatrixBUG.IsRankAdaptiveStep`) with truncation tolerance `ϑ` satisfies

    ‖Y₁ - A(t₁)‖ ≤ (e^{L h} - 1) M₂ h² + ϑ.

No singular value of `S₀` and no normal component enters the bound.  The solutions `P`, `Q` of
the two auxiliary linear equations (`P(t₀) = V₀ᵀ`, `Q(t₀) = U₀`) are hypotheses; they do not
appear in the bound. -/
theorem error_le_of_sylvester {h : ℝ} (hFS : ∀ t Y, F t Y = 𝒜 t * Y + Y * ℬ t)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    (hPf : ODESolution (fun t X => X * ℬ t - V₀ᵀ * ℬ t * V₀ * X) P t₀ t₁) (hP₀ : P t₀ = V₀ᵀ)
    (hQf : ODESolution (fun t X => 𝒜 t * X - X * (U₀ᵀ * 𝒜 t * U₀)) Q t₀ t₁)
    (hQ₀ : Q t₀ = U₀) {a₂ : ℝ → Matrix m n ℝ} {M₂ : ℝ}
    (ha : ContinuousOn (fun t => F t (A t)) (Icc t₀ t₁))
    (ha' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => F t (A t)) (a₂ s) (Ici s) s)
    (hM₂ : ∀ s ∈ Ico t₀ t₁, ‖a₂ s‖ ≤ M₂) :
    ‖Y₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (M₂ * h ^ 2) + ϑ := by
  have ht : t₀ ≤ t₁ := by linarith
  obtain ⟨hcapU, hcapV⟩ := capture_of_sylvester hFS hF hL hs ht hA hA₀ hPf hP₀ hQf hQ₀
  have hR : IsOrthProj (galerkinProj Ua Va : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
    isOrthProj_galerkinProj hs.orthUa hs.orthVa
  have hRA : galerkinProj Ua Va (A t₀) = A t₀ := by
    rw [galerkinProj_eq, hA₀, hs.aug_right, hs.aug_left]
  have hcap : galerkinProj Ua Va (A t₁) = A t₁ := by
    rw [galerkinProj_eq, rightProj_apply, hcapV, leftProj_apply, hcapU]
  have hYS : ODESolution (fun t x => galerkinProj Ua Va (F t x)) (fun t => Ua * Sa t * Vaᵀ)
      t₀ t₁ := by
    have h1 := odeSolution_sField hs.sSol
    simp only [galerkinProj_eq]
    exact h1
  have hS₀ : (fun t => Ua * Sa t * Vaᵀ) t₀ = A t₀ := hs.start_eq.trans hA₀.symm
  have hb := galerkin_error_of_capture (E := Matrix m n ℝ) (R := galerkinProj Ua Va)
    (YS := fun t => Ua * Sa t * Vaᵀ) hR hF hL ht₁ hh hA hRA ha ha' hM₂ hcap hYS hS₀
  have hb' : ‖Ua * Sa t₁ * Vaᵀ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (M₂ * h ^ 2) := hb
  have htri := norm_sub_le_norm_sub_add_norm_sub Y₁ (Ua * Sa t₁ * Vaᵀ) (A t₁)
  linarith [hs.trunc]

end Sylvester

/-! ### An example of Sylvester type -/

namespace Examples

/-- The linear field `F(Y) = E₂₁ Y + Y E₁₂` on `3 × 2` matrices, of Sylvester type.  It is
`rowField` without the term `Y₁₂ E₃₁ Y`, the one that makes the left factor depend on the
state. -/
noncomputable def sylField (Y : Matrix (Fin 3) (Fin 2) ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  rowFieldLeft 0 * Y + Y * rowFieldRight

/-- The derivative of `t ↦ sylField (A t)` along the exact solution of the example. -/
private noncomputable def sylCurveDeriv : Matrix (Fin 3) (Fin 2) ℝ := !![0, 0; 0, 2; 0, 0]

end Examples

section SylvesterExample

open MatrixBUG

/-- `sylField` is Lipschitz with the constant `‖E₂₁‖ + ‖E₁₂‖`. -/
theorem isLipschitzField_sylField :
    IsLipschitzField (fun _ : ℝ => sylField) (‖rowFieldLeft 0‖ + ‖rowFieldRight‖) :=
  fun _ X Y => by
    change ‖sylField X - sylField Y‖ ≤ (‖rowFieldLeft 0‖ + ‖rowFieldRight‖) * ‖X - Y‖
    have he : sylField X - sylField Y =
        rowFieldLeft 0 * (X - Y) + (X - Y) * rowFieldRight := by
      simp only [sylField, Matrix.mul_sub, Matrix.sub_mul]
      abel
    rw [he, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (Frobenius.norm_mul_le _ _)
      ((Frobenius.norm_mul_le _ _).trans_eq (mul_comm _ _)))

/-- `V₀ᵀ ℬ V₀ = 0` for `ℬ = E₁₂` and `V₀ = e₁`. -/
private theorem startRight_rowFieldRight : startRightᵀ * rowFieldRight * startRight = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  fin_cases i
  fin_cases j
  simp [startRight, rowFieldRight]

/-- `U₀ᵀ 𝒜 U₀ = 0` for `𝒜 = E₂₁` and `U₀ = e₁`. -/
private theorem startLeft_rowFieldLeft : startLeftᵀ * rowFieldLeft 0 * startLeft = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  fin_cases i
  fin_cases j
  simp [startLeft, rowFieldLeft]

/-- The K-step field of `sylField` is `K ↦ E₂₁ K` (`kField_of_sylvester`). -/
private theorem kField_sylField (t : ℝ) (K : Matrix (Fin 3) (Fin 1) ℝ) :
    kField startRight (fun _ => sylField) t K = rowFieldLeft 0 * K := by
  rw [kField_of_sylvester (F := fun _ => sylField) (𝒜 := fun _ => rowFieldLeft 0)
    (ℬ := fun _ => rowFieldRight) (fun _ _ => rfl) startRight_orth, startRight_rowFieldRight,
    Matrix.mul_zero, add_zero]

/-- `K(t) = (1, t, 0)ᵀ` solves the K-step equation of `sylField`: the K-step fields of
`sylField` and of `rowField` agree. -/
private theorem odeSolution_kField_sylField (h : ℝ) :
    ODESolution (kField startRight fun _ => sylField) kSolution 0 h := by
  have he : (kField startRight fun _ : ℝ => sylField) = kField startRight fun _ => rowField := by
    funext t K
    rw [kField_sylField, kField_rowField]
  rw [he]
  exact odeSolution_kSolution h

/-- The L-step field of `sylField` is `L ↦ L₁₁ e₂` (`transpose_lField_of_sylvester`). -/
private theorem lField_sylField (t : ℝ) (L : Matrix (Fin 2) (Fin 1) ℝ) :
    lField startLeft (fun _ => sylField) t L = L 0 0 • lDirection := by
  have hT := transpose_lField_of_sylvester (F := fun _ => sylField)
    (𝒜 := fun _ => rowFieldLeft 0) (ℬ := fun _ => rowFieldRight) (fun _ _ => rfl)
    startLeft_orth t L
  rw [startLeft_rowFieldLeft, Matrix.zero_mul, zero_add] at hT
  ext i j
  have hij := congrFun (congrFun hT j) i
  rw [Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_two] at hij
  rw [hij]
  fin_cases i <;> fin_cases j <;> simp [rowFieldRight, lDirection]

/-- `L(t) = (1, t)ᵀ` solves the L-step equation of `sylField`: the L-step fields of `sylField`
and of `rowField` agree. -/
private theorem odeSolution_lField_sylField (h : ℝ) :
    ODESolution (lField startLeft fun _ => sylField) lSolution 0 h := by
  have he : (lField startLeft fun _ : ℝ => sylField) = lField startLeft fun _ => rowField := by
    funext t L
    rw [lField_sylField, lField_rowField]
  rw [he]
  exact odeSolution_lSolution h

/-- `Ŝ(t) = [[1, t], [t, t²]]` solves the Galerkin equation of `sylField` in the bases
`Û = [e₁, e₂]`, `V̂ = I₂`. -/
private theorem odeSolution_sField_sylField (h : ℝ) :
    ODESolution (sField augmentedLeft (1 : Matrix (Fin 2) (Fin 2) ℝ) fun _ => sylField)
      galerkinSolution 0 h := by
  have hd : ∀ t : ℝ, HasDerivAt galerkinSolution
      (sField augmentedLeft (1 : Matrix (Fin 2) (Fin 2) ℝ) (fun _ => sylField) t
        (galerkinSolution t)) t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => s • galerkinCoeff1) galerkinCoeff1 t := by
      simpa using (hasDerivAt_id t).smul_const galerkinCoeff1
    have h2 : HasDerivAt (fun s : ℝ => s ^ 2 • galerkinCoeff2) ((2 * t) • galerkinCoeff2) t := by
      simpa using (hasDerivAt_pow 2 t).smul_const galerkinCoeff2
    have he : sField augmentedLeft (1 : Matrix (Fin 2) (Fin 2) ℝ) (fun _ => sylField) t
        (galerkinSolution t) = galerkinCoeff1 + (2 * t) • galerkinCoeff2 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sField, sylField, rowFieldLeft, rowFieldRight, augmentedLeft, galerkinSolution,
          galerkinCoeff0, galerkinCoeff1, galerkinCoeff2, Matrix.mul_apply, Fin.sum_univ_three]
      ring
    rw [he]
    exact (h1.const_add galerkinCoeff0).add h2
  exact ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => (hd t).hasDerivWithinAt⟩

/-- `P(t) = (1, t)` solves `P' = P ℬ - (V₀ᵀ ℬ V₀) P` with `ℬ = E₁₂`. -/
private theorem odeSolution_rightFlow (h : ℝ) :
    ODESolution (fun (_ : ℝ) (X : Matrix (Fin 1) (Fin 2) ℝ) =>
      X * rowFieldRight - startRightᵀ * rowFieldRight * startRight * X)
      (fun t => (lSolution t)ᵀ) 0 h := by
  have hd : ∀ t : ℝ, HasDerivAt (fun s => (lSolution s)ᵀ)
      ((lSolution t)ᵀ * rowFieldRight -
        startRightᵀ * rowFieldRight * startRight * (lSolution t)ᵀ) t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => s • lDirection) lDirection t := by
      simpa using (hasDerivAt_id t).smul_const lDirection
    have he : (lSolution t)ᵀ * rowFieldRight -
        startRightᵀ * rowFieldRight * startRight * (lSolution t)ᵀ = lDirectionᵀ := by
      ext i j
      fin_cases i
      fin_cases j <;> simp [lSolution, startRight, lDirection, rowFieldRight, Matrix.mul_apply]
    rw [he]
    exact Frobenius.hasDerivAt_transpose (K := lSolution) (h1.const_add startRight)
  exact ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => (hd t).hasDerivWithinAt⟩

/-- `Q(t) = (1, t, 0)ᵀ` solves `Q' = 𝒜 Q - Q (U₀ᵀ 𝒜 U₀)` with `𝒜 = E₂₁`: this field is the
K-step field of `rowField`. -/
private theorem odeSolution_leftFlow (h : ℝ) :
    ODESolution (fun (_ : ℝ) (X : Matrix (Fin 3) (Fin 1) ℝ) =>
      rowFieldLeft 0 * X - X * (startLeftᵀ * rowFieldLeft 0 * startLeft)) kSolution 0 h := by
  have he : (fun (_ : ℝ) (X : Matrix (Fin 3) (Fin 1) ℝ) =>
      rowFieldLeft 0 * X - X * (startLeftᵀ * rowFieldLeft 0 * startLeft)) =
      kField startRight fun _ => rowField := by
    funext t X
    rw [startLeft_rowFieldLeft, Matrix.mul_zero, sub_zero, kField_rowField]
  have hk := odeSolution_kSolution h
  rwa [← he] at hk

/-- The exact solution `A(t) = (1, t, 0)ᵀ (1, t)` of `A' = sylField A`, `A(0) = e₁ e₁ᵀ`, as the
product of the K-step solution and the auxiliary flow `P` (`odeSolution_kCurve`). -/
private theorem odeSolution_sylField (h : ℝ) :
    ODESolution (fun _ => sylField) (fun t => kSolution t * (lSolution t)ᵀ) 0 h :=
  odeSolution_kCurve (F := fun _ => sylField) (𝒜 := fun _ => rowFieldLeft 0)
    (ℬ := fun _ => rowFieldRight) (fun _ _ => rfl) startRight_orth
    (odeSolution_kField_sylField h) (odeSolution_rightFlow h)

/-- Along the exact solution, `F(A(s)) = C₁ + s G` with `G = 2 E₂₂`. -/
private theorem sylField_curve (s : ℝ) :
    sylField (kSolution s * (lSolution s)ᵀ) = exactCoeff1 + s • sylCurveDeriv := by
  ext i j
  simp only [sylField, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_three, Fin.sum_univ_two, Fin.sum_univ_one]
  fin_cases i <;> fin_cases j <;>
    simp [rowFieldLeft, rowFieldRight, kSolution, lSolution, startLeft, kDirection, startRight,
      lDirection, exactCoeff1, sylCurveDeriv]
  ring

/-- Along the exact solution, `(d/dt) F(A(t)) = G`. -/
private theorem hasDerivAt_sylField_curve (s : ℝ) :
    HasDerivAt (fun t => sylField (kSolution t * (lSolution t)ᵀ)) sylCurveDeriv s := by
  have he : (fun t => sylField (kSolution t * (lSolution t)ᵀ)) =
      fun t => exactCoeff1 + t • sylCurveDeriv := funext sylField_curve
  have h1 : HasDerivAt (fun t : ℝ => t • sylCurveDeriv) sylCurveDeriv s := by
    simpa using (hasDerivAt_id s).smul_const sylCurveDeriv
  rw [he]
  exact h1.const_add exactCoeff1

/-- The step of `isRankAdaptiveStep_example` (`K(t) = (1, t, 0)ᵀ`, `L(t) = (1, t)ᵀ`,
`Û = [e₁, e₂]`, `V̂ = I₂`, `Ŝ(t) = [[1, t], [t, t²]]`, no truncation) is also a rank-adaptive
BUG step for the linear field `sylField`. -/
theorem isRankAdaptiveStep_sylField (h : ℝ) :
    IsRankAdaptiveStep (fun _ => sylField) 0 0 h startLeft 1 startRight augmentedLeft
      (1 : Matrix (Fin 2) (Fin 2) ℝ) kSolution lSolution galerkinSolution
      (augmentedLeft * galerkinSolution h * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ) where
  orthU₀ := startLeft_orth
  orthV₀ := startRight_orth
  kSol := odeSolution_kField_sylField h
  kStart := (isRankAdaptiveStep_example h).kStart
  lSol := odeSolution_lField_sylField h
  lStart := (isRankAdaptiveStep_example h).lStart
  orthUa := augmentedLeft_orth
  kCap := (isRankAdaptiveStep_example h).kCap
  augU := (isRankAdaptiveStep_example h).augU
  orthVa := (isRankAdaptiveStep_example h).orthVa
  lCap := (isRankAdaptiveStep_example h).lCap
  augV := (isRankAdaptiveStep_example h).augV
  sSol := odeSolution_sField_sylField h
  sStart := (isRankAdaptiveStep_example h).sStart
  trunc := (isRankAdaptiveStep_example h).trunc

/-- Non-vacuity of `capture_of_sylvester` with nonzero data: the field `sylField`, the start
`Y₀ = e₁ e₁ᵀ`, the step of `isRankAdaptiveStep_sylField`, the exact solution
`A(t) = (1, t, 0)ᵀ (1, t)` and the auxiliary flows `P(t) = (1, t)`, `Q(t) = (1, t, 0)ᵀ`. -/
example (h : ℝ) (hh : 0 ≤ h) :
    augmentedLeft * augmentedLeftᵀ * (kSolution h * (lSolution h)ᵀ) =
        kSolution h * (lSolution h)ᵀ ∧
      kSolution h * (lSolution h)ᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ) *
        (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = kSolution h * (lSolution h)ᵀ :=
  capture_of_sylvester (F := fun _ => sylField) (𝒜 := fun _ => rowFieldLeft 0)
    (ℬ := fun _ => rowFieldRight) (A := fun t => kSolution t * (lSolution t)ᵀ)
    (P := fun t => (lSolution t)ᵀ) (Q := kSolution) (t₀ := 0) (t₁ := h) (fun _ _ => rfl)
    isLipschitzField_sylField (by positivity) (isRankAdaptiveStep_sylField h) hh
    (odeSolution_sylField h) (by simp [kSolution, lSolution]) (odeSolution_rightFlow h)
    (by simp [lSolution]) (odeSolution_leftFlow h) (by simp [kSolution])

/-- Non-vacuity of `error_le_of_sylvester` on the same data.  The same `K`, `L`, `Û`, `V̂`, `Ŝ`
form a step for `rowField`, where the error is at least `h² / 2`
(`error_ge_of_isRankAdaptiveStep`). -/
example (h : ℝ) (hh : 0 ≤ h) :
    ‖augmentedLeft * galerkinSolution h * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ -
        kSolution h * (lSolution h)ᵀ‖ ≤
      (Real.exp ((‖rowFieldLeft 0‖ + ‖rowFieldRight‖) * h) - 1) * (‖sylCurveDeriv‖ * h ^ 2) + 0 :=
  error_le_of_sylvester (F := fun _ => sylField) (𝒜 := fun _ => rowFieldLeft 0)
    (ℬ := fun _ => rowFieldRight) (A := fun t => kSolution t * (lSolution t)ᵀ)
    (P := fun t => (lSolution t)ᵀ) (Q := kSolution) (a₂ := fun _ => sylCurveDeriv)
    (M₂ := ‖sylCurveDeriv‖) (t₀ := 0) (t₁ := h) (fun _ _ => rfl) isLipschitzField_sylField
    (by positivity) (zero_add h).symm hh (isRankAdaptiveStep_sylField h) (odeSolution_sylField h)
    (by simp [kSolution, lSolution]) (odeSolution_rightFlow h) (by simp [lSolution])
    (odeSolution_leftFlow h) (by simp [kSolution])
    (fun s _ => (hasDerivAt_sylField_curve s).continuousAt.continuousWithinAt)
    (fun s _ => (hasDerivAt_sylField_curve s).hasDerivWithinAt) (fun _ _ => le_rfl)

end SylvesterExample

end AugmentationRank

end LeanDLRA
