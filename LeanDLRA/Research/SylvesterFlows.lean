import LeanDLRA.Foundations.Localization
import LeanDLRA.Research.AugmentationRank

/-!
# The rank-adaptive BUG step on fields of Sylvester type: the auxiliary flows exist

## Setting

`F(t, Y) = 𝒜(t) Y + Y ℬ(t)` on `m × n` matrices, one step of the rank-adaptive BUG integrator
(Ceruti–Kusch–Lubich, arXiv:2104.05247; `MatrixBUG.IsRankAdaptiveStep`) from
`Y₀ = U₀ S₀ V₀ᵀ`.  `capture_of_sylvester` and `error_le_of_sylvester` take the solutions `P`, `Q`
of the two linear equations

    P' = P ℬ(t) - (V₀ᵀ ℬ(t) V₀) P,  P(t₀) = V₀ᵀ,      Q' = 𝒜(t) Q - Q (U₀ᵀ 𝒜(t) U₀),  Q(t₀) = U₀

as hypotheses.  For coefficients that are continuous on `[t₀, t₁]` these solutions exist, and
the two theorems hold without them.

## Main results

* `exists_odeSolution_sylvester`: the linear equation `X' = C(t) X + X D(t)` with coefficients
  continuous on `[t₀, t₁]` has a solution on `[t₀, t₁]` from every starting value.
* `exists_rightFactor_of_sylvester`, `exists_leftFactor_of_sylvester`: the flows `P` and `Q`.
* `exists_factor_of_sylvester`: `A(t₁) = K(t₁) N_K = N_L L(t₁)ᵀ` for suitable matrices `N_K`,
  `N_L`, where `K`, `L` are the K- and L-step solutions.
* `capture_of_sylvester_of_continuousOn`: `Û Ûᵀ A(t₁) = A(t₁)` and `A(t₁) V̂ V̂ᵀ = A(t₁)`.
* `error_le_of_sylvester_of_continuousOn`: `‖Y₁ - A(t₁)‖ ≤ (e^{L h} - 1) M₂ h² + ϑ`.

## Implementation notes

The existence proof extends the coefficients constantly outside `[t₀, t₁]` and uses
`exists_ODESolution_of_linearGrowth`; no matrix exponential is needed, and the coefficients may
depend on time.

## References

* Ceruti–Kusch–Lubich, arXiv:2104.05247 (rank-adaptive BUG integrator).
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace AugmentationRank

section LinearEquation

variable {p q : Type*} [Fintype p] [Fintype q]

/-- The field `X ↦ C X + X D` is Lipschitz with the constant `‖C‖ + ‖D‖`. -/
private theorem norm_sylvester_sub_le (C : Matrix p p ℝ) (D : Matrix q q ℝ) (X Y : Matrix p q ℝ)
    {c d : ℝ} (hc : ‖C‖ ≤ c) (hd : ‖D‖ ≤ d) :
    ‖(C * X + X * D) - (C * Y + Y * D)‖ ≤ (c + d) * ‖X - Y‖ := by
  have e : (C * X + X * D) - (C * Y + Y * D) = C * (X - Y) + (X - Y) * D := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [e, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (Frobenius.norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  · exact ((Frobenius.norm_mul_le _ _).trans_eq (mul_comm _ _)).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg _))

/-- **Linear matrix equations of Sylvester type have solutions.**  If `C` and `D` are continuous
on `[t₀, t₁]`, then `X' = C(t) X + X D(t)`, `X(t₀) = X₀` has a solution on `[t₀, t₁]`, for
rectangular `X` and every starting value. -/
theorem exists_odeSolution_sylvester {C : ℝ → Matrix p p ℝ} {D : ℝ → Matrix q q ℝ} {t₀ t₁ : ℝ}
    (hC : ContinuousOn C (Icc t₀ t₁)) (hD : ContinuousOn D (Icc t₀ t₁)) (ht : t₀ ≤ t₁)
    (X₀ : Matrix p q ℝ) :
    ∃ X : ℝ → Matrix p q ℝ,
      ODESolution (fun t Y => C t * Y + Y * D t) X t₀ t₁ ∧ X t₀ = X₀ := by
  obtain ⟨c, hc⟩ := isCompact_Icc.exists_bound_of_continuousOn hC
  obtain ⟨d, hd⟩ := isCompact_Icc.exists_bound_of_continuousOn hD
  have hmem : ∀ t : ℝ, max t₀ (min t₁ t) ∈ Icc t₀ t₁ := fun t =>
    ⟨le_max_left _ _, max_le ht (min_le_left _ _)⟩
  have hfix : ∀ t ∈ Icc t₀ t₁, max t₀ (min t₁ t) = t := fun t h => by
    rw [min_eq_right h.2, max_eq_right h.1]
  have hLip : IsLipschitzField (fun (t : ℝ) (Y : Matrix p q ℝ) =>
      C (max t₀ (min t₁ t)) * Y + Y * D (max t₀ (min t₁ t))) (c + d) := fun t X Y =>
    norm_sylvester_sub_le _ _ X Y (hc _ (hmem t)) (hd _ (hmem t))
  have hL : 0 ≤ c + d :=
    add_nonneg ((norm_nonneg _).trans (hc t₀ (left_mem_Icc.2 ht)))
      ((norm_nonneg _).trans (hd t₀ (left_mem_Icc.2 ht)))
  have hcont : ∀ x : Matrix p q ℝ, ContinuousOn (fun t : ℝ =>
      C (max t₀ (min t₁ t)) * x + x * D (max t₀ (min t₁ t))) (Icc t₀ t₁) := fun x => by
    have h1 : ContinuousOn (fun t : ℝ => C t * x + x * D t) (Icc t₀ t₁) :=
      ((Frobenius.rightMulCLM x).continuous.comp_continuousOn hC).add
        ((Frobenius.leftMulCLM x).continuous.comp_continuousOn hD)
    refine h1.congr fun t h => ?_
    change C (max t₀ (min t₁ t)) * x + x * D (max t₀ (min t₁ t)) = C t * x + x * D t
    rw [hfix t h]
  obtain ⟨X, hX, hX₀⟩ := exists_ODESolution_of_linearGrowth (K := 0) hLip hL
    (fun t _ => by simp) hcont ht X₀
  refine ⟨X, ⟨hX.cont, fun t h => ?_⟩, hX₀⟩
  have hd' := hX.deriv t h
  simp only [hfix t (Ico_subset_Icc_self h)] at hd'
  exact hd'

end LinearEquation

section Flows

open MatrixBUG

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k'] [DecidableEq k]
  [DecidableEq k'] {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {𝒜 : ℝ → Matrix m m ℝ}
  {ℬ : ℝ → Matrix n n ℝ} {t₀ t₁ : ℝ} {U₀ : Matrix m (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}

omit [Fintype m] in
/-- **The auxiliary flow of the K-step exists.**  For `ℬ` continuous on `[t₀, t₁]` the linear
equation `P' = P ℬ(t) - (V₀ᵀ ℬ(t) V₀) P`, `P(t₀) = V₀ᵀ` of `capture_of_sylvester` has a solution
on `[t₀, t₁]`. -/
theorem exists_rightFactor_of_sylvester (hℬ : ContinuousOn ℬ (Icc t₀ t₁)) (ht : t₀ ≤ t₁)
    (V₀ : Matrix n (Fin r) ℝ) :
    ∃ P : ℝ → Matrix (Fin r) n ℝ,
      ODESolution (fun t X => X * ℬ t - V₀ᵀ * ℬ t * V₀ * X) P t₀ t₁ ∧ P t₀ = V₀ᵀ := by
  have hC : ContinuousOn (fun t => -(V₀ᵀ * (ℬ t * V₀))) (Icc t₀ t₁) :=
    ((Frobenius.leftMulCLM V₀ᵀ).continuous.comp_continuousOn
      ((Frobenius.rightMulCLM V₀).continuous.comp_continuousOn hℬ)).neg
  obtain ⟨P, hP, hP₀⟩ := exists_odeSolution_sylvester hC hℬ ht V₀ᵀ
  refine ⟨P, ⟨hP.cont, fun t h => (hP.deriv t h).congr_deriv ?_⟩, hP₀⟩
  simp only [Matrix.neg_mul, Matrix.mul_assoc]
  abel

omit [Fintype n] in
/-- **The auxiliary flow of the L-step exists.**  For `𝒜` continuous on `[t₀, t₁]` the linear
equation `Q' = 𝒜(t) Q - Q (U₀ᵀ 𝒜(t) U₀)`, `Q(t₀) = U₀` of `capture_of_sylvester` has a solution
on `[t₀, t₁]`. -/
theorem exists_leftFactor_of_sylvester (h𝒜 : ContinuousOn 𝒜 (Icc t₀ t₁)) (ht : t₀ ≤ t₁)
    (U₀ : Matrix m (Fin r) ℝ) :
    ∃ Q : ℝ → Matrix m (Fin r) ℝ,
      ODESolution (fun t X => 𝒜 t * X - X * (U₀ᵀ * 𝒜 t * U₀)) Q t₀ t₁ ∧ Q t₀ = U₀ := by
  have hD : ContinuousOn (fun t => -(U₀ᵀ * (𝒜 t * U₀))) (Icc t₀ t₁) :=
    ((Frobenius.leftMulCLM U₀ᵀ).continuous.comp_continuousOn
      ((Frobenius.rightMulCLM U₀).continuous.comp_continuousOn h𝒜)).neg
  obtain ⟨Q, hQ, hQ₀⟩ := exists_odeSolution_sylvester h𝒜 hD ht U₀
  refine ⟨Q, ⟨hQ.cont, fun t h => (hQ.deriv t h).congr_deriv ?_⟩, hQ₀⟩
  simp only [Matrix.mul_neg, Matrix.mul_assoc]
  abel

variable {S₀ : Matrix (Fin r) (Fin r) ℝ} {Ua : Matrix m k ℝ} {Va : Matrix n k' ℝ}
  {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ} {Sa : ℝ → Matrix k k' ℝ}
  {Y₁ : Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {L ϑ : ℝ}

/-- **The exact solution factorises through the K-step and through the L-step solution.**  For
an `L`-Lipschitz field of Sylvester type, `F(t, Y) = 𝒜(t) Y + Y ℬ(t)`, with coefficients
continuous on `[t₀, t₁]`, and every rank-adaptive BUG step from `Y₀ = U₀ S₀ V₀ᵀ`, the exact
solution satisfies `A(t₁) = K(t₁) N_K = N_L L(t₁)ᵀ` for suitable matrices `N_K`, `N_L`.  The
starting value may be rank deficient: no inverse of `S₀` is used. -/
theorem exists_factor_of_sylvester (hFS : ∀ t Y, F t Y = 𝒜 t * Y + Y * ℬ t)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (h𝒜 : ContinuousOn 𝒜 (Icc t₀ t₁))
    (hℬ : ContinuousOn ℬ (Icc t₀ t₁))
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁) (ht : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    (∃ N : Matrix (Fin r) n ℝ, A t₁ = K t₁ * N) ∧
      ∃ N : Matrix m (Fin r) ℝ, A t₁ = N * (Lf t₁)ᵀ := by
  obtain ⟨P, hP, hP₀⟩ := exists_rightFactor_of_sylvester hℬ ht V₀
  obtain ⟨Q, hQ, hQ₀⟩ := exists_leftFactor_of_sylvester h𝒜 ht U₀
  exact ⟨⟨P t₁, eq_kStep_mul_of_sylvester hFS hF hL hs.orthV₀ hs.kSol hP hP₀ hA
      (by rw [hA₀, hs.kStart]) t₁ (right_mem_Icc.2 ht)⟩,
    ⟨Q t₁, eq_mul_lStep_of_sylvester hFS hF hL hs.orthU₀ hs.lSol hQ hQ₀ hA
      (by rw [hA₀, hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.mul_assoc]) t₁ (right_mem_Icc.2 ht)⟩⟩

/-- **The Galerkin space of a rank-adaptive BUG step contains the exact solution** when the
field is of Sylvester type, `F(t, Y) = 𝒜(t) Y + Y ℬ(t)`, with coefficients continuous on
`[t₀, t₁]`: `Û Ûᵀ A(t₁) = A(t₁)` and `A(t₁) V̂ V̂ᵀ = A(t₁)` for every rank-adaptive BUG step
(`MatrixBUG.IsRankAdaptiveStep`).  This is `capture_of_sylvester` without the auxiliary flows,
which exist by `exists_rightFactor_of_sylvester` and `exists_leftFactor_of_sylvester`. -/
theorem capture_of_sylvester_of_continuousOn (hFS : ∀ t Y, F t Y = 𝒜 t * Y + Y * ℬ t)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (h𝒜 : ContinuousOn 𝒜 (Icc t₀ t₁))
    (hℬ : ContinuousOn ℬ (Icc t₀ t₁))
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁) (ht : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    Ua * Uaᵀ * A t₁ = A t₁ ∧ A t₁ * Va * Vaᵀ = A t₁ := by
  obtain ⟨P, hP, hP₀⟩ := exists_rightFactor_of_sylvester hℬ ht V₀
  obtain ⟨Q, hQ, hQ₀⟩ := exists_leftFactor_of_sylvester h𝒜 ht U₀
  exact capture_of_sylvester hFS hF hL hs ht hA hA₀ hP hP₀ hQ hQ₀

/-- **Error of the rank-adaptive BUG step on fields of Sylvester type.**  Let
`F(t, Y) = 𝒜(t) Y + Y ℬ(t)` be `L`-Lipschitz with coefficients continuous on `[t₀, t₁]`, let `A`
be the exact solution from `Y₀ = U₀ S₀ V₀ᵀ`, and let `t ↦ F(t, A(t))` have a derivative bounded
by `M₂`.  Then every step of the rank-adaptive BUG integrator (Ceruti–Kusch–Lubich,
arXiv:2104.05247; `MatrixBUG.IsRankAdaptiveStep`) with truncation tolerance `ϑ` satisfies

    ‖Y₁ - A(t₁)‖ ≤ (e^{L h} - 1) M₂ h² + ϑ.

No singular value of `S₀` and no normal component enters the bound.  This is
`error_le_of_sylvester` without the auxiliary flows. -/
theorem error_le_of_sylvester_of_continuousOn {h : ℝ}
    (hFS : ∀ t Y, F t Y = 𝒜 t * Y + Y * ℬ t) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (h𝒜 : ContinuousOn 𝒜 (Icc t₀ t₁)) (hℬ : ContinuousOn ℬ (Icc t₀ t₁)) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) {a₂ : ℝ → Matrix m n ℝ} {M₂ : ℝ}
    (ha : ContinuousOn (fun t => F t (A t)) (Icc t₀ t₁))
    (ha' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => F t (A t)) (a₂ s) (Ici s) s)
    (hM₂ : ∀ s ∈ Ico t₀ t₁, ‖a₂ s‖ ≤ M₂) :
    ‖Y₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (M₂ * h ^ 2) + ϑ := by
  have ht : t₀ ≤ t₁ := by linarith
  obtain ⟨P, hP, hP₀⟩ := exists_rightFactor_of_sylvester hℬ ht V₀
  obtain ⟨Q, hQ, hQ₀⟩ := exists_leftFactor_of_sylvester h𝒜 ht U₀
  exact error_le_of_sylvester hFS hF hL ht₁ hh hs hA hA₀ hP hP₀ hQ hQ₀ ha ha' hM₂

end Flows

/-! ### An example -/

namespace Examples

/-- Coefficient of `1` in the exact solution of `A' = sylField A`, `A(0) = e₁ e₁ᵀ`. -/
private noncomputable def sylCoeff0 : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 0; 0, 0]

/-- Coefficient of `t` in that solution. -/
private noncomputable def sylCoeff1 : Matrix (Fin 3) (Fin 2) ℝ := !![0, 1; 1, 0; 0, 0]

/-- Coefficient of `t²` in that solution. -/
private noncomputable def sylCoeff2 : Matrix (Fin 3) (Fin 2) ℝ := !![0, 0; 0, 1; 0, 0]

/-- The exact solution `A(t) = (1, t, 0)ᵀ (1, t)` of `A' = sylField A`, `A(0) = e₁ e₁ᵀ`. -/
noncomputable def sylSolution (t : ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  sylCoeff0 + t • sylCoeff1 + t ^ 2 • sylCoeff2

end Examples

section FlowsExample

open MatrixBUG Examples

/-- Along `sylSolution` the field is `C₁ + 2 t C₂`. -/
private theorem sylField_sylSolution (t : ℝ) :
    sylField (sylSolution t) = sylCoeff1 + (2 * t) • sylCoeff2 := by
  ext i j
  simp only [sylField, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [rowFieldLeft, rowFieldRight, sylSolution, sylCoeff0, sylCoeff1, sylCoeff2]
  ring

/-- `sylSolution` has the derivative `sylField (sylSolution t)`. -/
private theorem hasDerivAt_sylSolution (t : ℝ) :
    HasDerivAt sylSolution (sylField (sylSolution t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => s • sylCoeff1) sylCoeff1 t := by
    simpa using (hasDerivAt_id t).smul_const sylCoeff1
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2 • sylCoeff2) ((2 * t) • sylCoeff2) t := by
    simpa using (hasDerivAt_pow 2 t).smul_const sylCoeff2
  rw [sylField_sylSolution]
  exact (h1.const_add sylCoeff0).add h2

/-- `sylSolution` solves `A' = sylField A` on every interval `[0, h]`. -/
theorem odeSolution_sylSolution (h : ℝ) :
    ODESolution (fun _ => sylField) sylSolution 0 h where
  cont := fun t _ => (hasDerivAt_sylSolution t).continuousAt.continuousWithinAt
  deriv := fun t _ => (hasDerivAt_sylSolution t).hasDerivWithinAt

/-- `sylSolution 0 = U₀ S₀ V₀ᵀ` with `S₀ = 1`. -/
theorem sylSolution_zero :
    sylSolution 0 = startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ := by
  rw [Matrix.mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sylSolution, sylCoeff0, startLeft, startRight, Matrix.mul_apply]

/-- Along the exact solution, `(d/dt) F(A(t)) = 2 C₂`. -/
private theorem hasDerivAt_sylField_sylSolution (s : ℝ) :
    HasDerivAt (fun t => sylField (sylSolution t)) ((2 : ℝ) • sylCoeff2) s := by
  have he : (fun t => sylField (sylSolution t)) = fun t => sylCoeff1 + (2 * t) • sylCoeff2 :=
    funext sylField_sylSolution
  have h1 : HasDerivAt (fun t : ℝ => (2 * t) • sylCoeff2) ((2 : ℝ) • sylCoeff2) s := by
    simpa using ((hasDerivAt_id s).const_mul (2 : ℝ)).smul_const sylCoeff2
  rw [he]
  exact h1.const_add sylCoeff1

/-- Non-vacuity of `exists_factor_of_sylvester` and `capture_of_sylvester_of_continuousOn` with
nonzero data: the field `sylField` (constant coefficients `E₂₁`, `E₁₂`), the start
`Y₀ = e₁ e₁ᵀ`, the step of `isRankAdaptiveStep_sylField` and the exact solution `sylSolution`.
No auxiliary flow is supplied. -/
example (h : ℝ) (hh : 0 ≤ h) :
    ((∃ N : Matrix (Fin 1) (Fin 2) ℝ, sylSolution h = kSolution h * N) ∧
        ∃ N : Matrix (Fin 3) (Fin 1) ℝ, sylSolution h = N * (lSolution h)ᵀ) ∧
      augmentedLeft * augmentedLeftᵀ * sylSolution h = sylSolution h ∧
      sylSolution h * (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ =
        sylSolution h :=
  ⟨exists_factor_of_sylvester (F := fun _ => sylField) (𝒜 := fun _ => rowFieldLeft 0)
      (ℬ := fun _ => rowFieldRight) (fun _ _ => rfl) isLipschitzField_sylField (by positivity)
      continuousOn_const continuousOn_const (isRankAdaptiveStep_sylField h) hh
      (odeSolution_sylSolution h) sylSolution_zero,
    capture_of_sylvester_of_continuousOn (F := fun _ => sylField)
      (𝒜 := fun _ => rowFieldLeft 0) (ℬ := fun _ => rowFieldRight) (fun _ _ => rfl)
      isLipschitzField_sylField (by positivity) continuousOn_const continuousOn_const
      (isRankAdaptiveStep_sylField h) hh (odeSolution_sylSolution h) sylSolution_zero⟩

/-- Non-vacuity of `error_le_of_sylvester_of_continuousOn` on the same data, with
`M₂ = ‖2 E₂₂‖`. -/
example (h : ℝ) (hh : 0 ≤ h) :
    ‖augmentedLeft * galerkinSolution h * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ - sylSolution h‖ ≤
      (Real.exp ((‖rowFieldLeft 0‖ + ‖rowFieldRight‖) * h) - 1) *
        (‖(2 : ℝ) • sylCoeff2‖ * h ^ 2) + 0 :=
  error_le_of_sylvester_of_continuousOn (F := fun _ => sylField)
    (𝒜 := fun _ => rowFieldLeft 0) (ℬ := fun _ => rowFieldRight)
    (a₂ := fun _ => (2 : ℝ) • sylCoeff2) (t₀ := 0) (t₁ := h) (fun _ _ => rfl)
    isLipschitzField_sylField (by positivity) continuousOn_const continuousOn_const
    (zero_add h).symm hh (isRankAdaptiveStep_sylField h) (odeSolution_sylSolution h)
    sylSolution_zero
    (fun s _ => (hasDerivAt_sylField_sylSolution s).continuousAt.continuousWithinAt)
    (fun s _ => (hasDerivAt_sylField_sylSolution s).hasDerivWithinAt) (fun _ _ => le_rfl)

end FlowsExample

end AugmentationRank

end LeanDLRA
