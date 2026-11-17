import LeanDLRA.Research.SylvesterFlows

/-!
# The rank-adaptive BUG integrator is of global order two on fields of Sylvester type

## Setting

`F(t, Y) = 𝒜(t) Y + Y ℬ(t)` on `m × n` matrices with coefficients continuous on `[t₀, t₀ + N h]`,
and `N` steps of the rank-adaptive BUG integrator (Ceruti–Kusch–Lubich, [CerutiKuschLubich2022];
`MatrixBUG.IsRankAdaptiveStep`) with step size `h` and truncation tolerance `ϑ`.  The rank may
change from step to step.

## Main result

* `rankAdaptive_global_error_le_of_sylvester`: for `j h ≤ T`,
  `‖Yⱼ - A(tⱼ)‖ ≤ e^{L T} (δ + T L e^{L h} M₂ h² + j ϑ)`, where `δ` bounds the initial error and
  `M₂` the derivative of `t ↦ F(t, Φ(t))` along the exact solutions `Φ` started at the numerical
  values.  No singular value and no normal component enters.

## Implementation notes

The proof is Lady Windermere's fan (`lady_windermere`) with the local bound
`error_le_of_sylvester_of_continuousOn`.  The truncation errors add up to `j ϑ`, as in
`MatrixBUG.rankAdaptive_global_error_le`.

## References

* Ceruti–Kusch–Lubich, [CerutiKuschLubich2022] (rank-adaptive BUG integrator, Theorem 2).
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace AugmentationRank

section Global

open MatrixBUG

variable {m n : Type*} [Fintype m] [Fintype n] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
  {𝒜 : ℝ → Matrix m m ℝ} {ℬ : ℝ → Matrix n n ℝ} {L ϑ : ℝ}

/-- **Global error of the rank-adaptive BUG integrator on fields of Sylvester type.**  Let
`F(t, Y) = 𝒜(t) Y + Y ℬ(t)` be `L`-Lipschitz with coefficients continuous on `[t₀, t₀ + N h]`,
`tⱼ = t₀ + j h`, and `A` a solution of `A' = F(t, A)` on `[t₀, t₀ + N h]`.  Step `j`
(`MatrixBUG.IsRankAdaptiveStep`) goes from `Yⱼ = Uⱼ Sⱼ Vⱼᵀ` of rank `rⱼ` to `Yⱼ₊₁` with
truncation tolerance `ϑ`.  With `Φ j` the exact flow on `[tⱼ, tⱼ₊₁]` from `Yⱼ`, `M₂` a bound of
the derivative of `t ↦ F(t, Φ j t)`, `‖Y₀ - A(t₀)‖ ≤ δ` and `j h ≤ T`:

    ‖Yⱼ - A(tⱼ)‖ ≤ e^{L T} (δ + T L e^{L h} M₂ h² + j ϑ).

So the integrator is of order two on such fields, with constants that do not depend on singular
values; for general fields its order is one (`error_ge_of_isRankAdaptiveStep`). -/
theorem rankAdaptive_global_error_le_of_sylvester (hFS : ∀ t Y, F t Y = 𝒜 t * Y + Y * ℬ t)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ}
    (h𝒜 : ContinuousOn 𝒜 (Icc t₀ (t₀ + N * h))) (hℬ : ContinuousOn ℬ (Icc t₀ (t₀ + N * h)))
    {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ (t₀ + N * h)) {r ka kb : ℕ → ℕ}
    {U : (j : ℕ) → Matrix m (Fin (r j)) ℝ} {Sm : (j : ℕ) → Matrix (Fin (r j)) (Fin (r j)) ℝ}
    {V : (j : ℕ) → Matrix n (Fin (r j)) ℝ} {Ua : (j : ℕ) → Matrix m (Fin (ka j)) ℝ}
    {Va : (j : ℕ) → Matrix n (Fin (kb j)) ℝ} {K : (j : ℕ) → ℝ → Matrix m (Fin (r j)) ℝ}
    {Lf : (j : ℕ) → ℝ → Matrix n (Fin (r j)) ℝ}
    {Sa : (j : ℕ) → ℝ → Matrix (Fin (ka j)) (Fin (kb j)) ℝ} {Y : ℕ → Matrix m n ℝ}
    {Φ : ℕ → ℝ → Matrix m n ℝ} (hY : ∀ j < N, Y j = U j * Sm j * (V j)ᵀ)
    (hstep : ∀ j < N, IsRankAdaptiveStep F ϑ (t₀ + j * h) (t₀ + (j + 1) * h) (U j) (Sm j) (V j)
      (Ua j) (Va j) (K j) (Lf j) (Sa j) (Y (j + 1)))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = Y j) {a₂ : ℕ → ℝ → Matrix m n ℝ} {M₂ : ℝ}
    (hM₂0 : 0 ≤ M₂)
    (ha : ∀ j < N, ContinuousOn (fun t => F t (Φ j t)) (Icc (t₀ + j * h) (t₀ + (j + 1) * h)))
    (ha' : ∀ j < N, ∀ s ∈ Ico (t₀ + j * h) (t₀ + (j + 1) * h),
      HasDerivWithinAt (fun t => F t (Φ j t)) (a₂ j s) (Ici s) s)
    (hM₂ : ∀ j < N, ∀ s ∈ Ico (t₀ + j * h) (t₀ + (j + 1) * h), ‖a₂ j s‖ ≤ M₂) {δ T : ℝ}
    (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖Y j - A (t₀ + j * h)‖
        ≤ Real.exp (L * T) * (δ + T * (L * Real.exp (L * h) * M₂ * h ^ 2) + j * ϑ) := by
  have hloc : ∀ j < N, ‖Y (j + 1) - Φ j (t₀ + (j + 1) * h)‖
      ≤ (Real.exp (L * h) - 1) * (M₂ * h ^ 2) + ϑ := fun j hj => by
    have hj' : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
    have h1 : t₀ ≤ t₀ + j * h := by linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hh]
    have h2 : t₀ + (j + 1) * h ≤ t₀ + N * h := by
      linarith [mul_le_mul_of_nonneg_right hj' hh]
    exact error_le_of_sylvester_of_continuousOn hFS hF hL (h𝒜.mono (Icc_subset_Icc h1 h2))
      (hℬ.mono (Icc_subset_Icc h1 h2)) (by ring) hh (hstep j hj) (hΦ j hj)
      ((hΦ₀ j hj).trans (hY j hj)) (ha j hj) (ha' j hj) (hM₂ j hj)
  intro j hj hT
  have h1 := lady_windermere hF hL hh hA hΦ hΦ₀ hloc j hj
  have hexp : Real.exp (L * h) - 1 ≤ L * h * Real.exp (L * h) := by
    have e1 : Real.exp (-(L * h)) * Real.exp (L * h) = 1 := by rw [← Real.exp_add]; simp
    have e2 := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(L * h)))
      (Real.exp_pos (L * h)).le
    linarith
  have hE : Real.exp (L * (j * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  have hc : 0 ≤ L * Real.exp (L * h) * M₂ * h ^ 2 := by positivity
  have hX : ‖Y 0 - A t₀‖ + j * ((Real.exp (L * h) - 1) * (M₂ * h ^ 2) + ϑ)
      ≤ δ + T * (L * Real.exp (L * h) * M₂ * h ^ 2) + j * ϑ := by
    have s1 : (j : ℝ) * ((Real.exp (L * h) - 1) * (M₂ * h ^ 2))
        ≤ (j * h) * (L * Real.exp (L * h) * M₂ * h ^ 2) :=
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp
        (by positivity : 0 ≤ M₂ * h ^ 2)) (Nat.cast_nonneg j)).trans_eq (by ring)
    have s2 := mul_le_mul_of_nonneg_right hT hc
    linarith
  have hX0 : 0 ≤ ‖Y 0 - A t₀‖ + j * ((Real.exp (L * h) - 1) * (M₂ * h ^ 2) + ϑ) := by
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp
    · have hℓ : 0 ≤ (Real.exp (L * h) - 1) * (M₂ * h ^ 2) + ϑ :=
        (norm_nonneg _).trans (hloc 0 (lt_of_lt_of_le hjpos hj))
      positivity
  calc ‖Y j - A (t₀ + j * h)‖
      ≤ Real.exp (L * (j * h))
        * (‖Y 0 - A t₀‖ + j * ((Real.exp (L * h) - 1) * (M₂ * h ^ 2) + ϑ)) := h1
    _ ≤ Real.exp (L * T)
        * (‖Y 0 - A t₀‖ + j * ((Real.exp (L * h) - 1) * (M₂ * h ^ 2) + ϑ)) :=
      mul_le_mul_of_nonneg_right hE hX0
    _ ≤ Real.exp (L * T) * (δ + T * (L * Real.exp (L * h) * M₂ * h ^ 2) + j * ϑ) :=
      mul_le_mul_of_nonneg_left hX (Real.exp_pos _).le

end Global

section GlobalExample

open MatrixBUG Examples

/-- Non-vacuity of `rankAdaptive_global_error_le_of_sylvester` with nonzero data: one step
(`N = 1`) of `isRankAdaptiveStep_sylField` for the field `sylField` from `Y₀ = e₁ e₁ᵀ`, the exact
solution `sylSolution`, and `M₂` a bound of the second derivative of the exact solution on
`[0, h]`. -/
example (h : ℝ) (hh : 0 ≤ h) : ∃ M₂ : ℝ,
    ‖augmentedLeft * galerkinSolution h * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ - sylSolution h‖
      ≤ Real.exp ((‖rowFieldLeft 0‖ + ‖rowFieldRight‖) * h)
        * (0 + h * ((‖rowFieldLeft 0‖ + ‖rowFieldRight‖)
          * Real.exp ((‖rowFieldLeft 0‖ + ‖rowFieldRight‖) * h) * M₂ * h ^ 2)
          + ((1 : ℕ) : ℝ) * 0) := by
  have e0 : (0 : ℝ) + ((0 : ℕ) : ℝ) * h = 0 := by simp
  have e1 : (0 : ℝ) + (((0 : ℕ) : ℝ) + 1) * h = h := by simp
  have eN : (0 : ℝ) + ((1 : ℕ) : ℝ) * h = h := by simp
  have hsol := odeSolution_sylSolution h
  have hcont1 : ContinuousOn
      (fun s => rowFieldLeft 0 * sylSolution s + sylSolution s * rowFieldRight) (Icc 0 h) := by
    have h1 := (Frobenius.leftMulCLM (rowFieldLeft 0)).continuous.comp_continuousOn hsol.cont
    have h2 := (Frobenius.rightMulCLM rowFieldRight).continuous.comp_continuousOn hsol.cont
    simpa only [Function.comp_def, Frobenius.leftMulCLM_apply, Frobenius.rightMulCLM_apply,
      Pi.add_def] using h1.add h2
  have hcont : ContinuousOn
      (fun s => rowFieldLeft 0 * (rowFieldLeft 0 * sylSolution s + sylSolution s * rowFieldRight)
        + (rowFieldLeft 0 * sylSolution s + sylSolution s * rowFieldRight) * rowFieldRight)
      (Icc 0 h) := by
    have h1 := (Frobenius.leftMulCLM (rowFieldLeft 0)).continuous.comp_continuousOn hcont1
    have h2 := (Frobenius.rightMulCLM rowFieldRight).continuous.comp_continuousOn hcont1
    simpa only [Function.comp_def, Frobenius.leftMulCLM_apply, Frobenius.rightMulCLM_apply,
      Pi.add_def] using h1.add h2
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨Y, hY0, hY1⟩ : ∃ Y : ℕ → Matrix (Fin 3) (Fin 2) ℝ,
      Y 0 = startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ ∧
        Y 1 = augmentedLeft * galerkinSolution h * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ :=
    ⟨fun j => if j = 0 then startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ
      else augmentedLeft * galerkinSolution h * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ, rfl, rfl⟩
  have hA : ODESolution (fun _ => sylField) sylSolution 0 (0 + ((1 : ℕ) : ℝ) * h) := by
    rw [eN]
    exact hsol
  have hYf : ∀ j : ℕ, j < 1 → Y j = startLeft * (1 : Matrix (Fin 1) (Fin 1) ℝ) * startRightᵀ := by
    intro j hj
    obtain rfl : j = 0 := Nat.lt_one_iff.1 hj
    exact hY0
  have hstep : ∀ j : ℕ, j < 1 → IsRankAdaptiveStep (fun _ => sylField) 0 (0 + (j : ℝ) * h)
      (0 + ((j : ℝ) + 1) * h) startLeft 1 startRight augmentedLeft
      (1 : Matrix (Fin 2) (Fin 2) ℝ) kSolution lSolution galerkinSolution (Y (j + 1)) := by
    intro j hj
    obtain rfl : j = 0 := Nat.lt_one_iff.1 hj
    rw [e0, e1, zero_add, hY1]
    exact isRankAdaptiveStep_sylField h
  have hΦ : ∀ j : ℕ, j < 1 → ODESolution (fun _ => sylField) sylSolution (0 + (j : ℝ) * h)
      (0 + ((j : ℝ) + 1) * h) := by
    intro j hj
    obtain rfl : j = 0 := Nat.lt_one_iff.1 hj
    rw [e0, e1]
    exact hsol
  have hΦ₀ : ∀ j : ℕ, j < 1 → sylSolution (0 + (j : ℝ) * h) = Y j := by
    intro j hj
    obtain rfl : j = 0 := Nat.lt_one_iff.1 hj
    rw [e0, hY0]
    exact sylSolution_zero
  have ha : ∀ j : ℕ, j < 1 → ContinuousOn (fun t => sylField (sylSolution t))
      (Icc (0 + (j : ℝ) * h) (0 + ((j : ℝ) + 1) * h)) := by
    intro j hj
    obtain rfl : j = 0 := Nat.lt_one_iff.1 hj
    rw [e0, e1]
    exact hcont1
  have ha' : ∀ j : ℕ, j < 1 → ∀ s ∈ Ico (0 + (j : ℝ) * h) (0 + ((j : ℝ) + 1) * h),
      HasDerivWithinAt (fun t => sylField (sylSolution t))
        (sylField (sylField (sylSolution s))) (Ici s) s := by
    intro j hj
    obtain rfl : j = 0 := Nat.lt_one_iff.1 hj
    rw [e0, e1]
    intro s hs
    have hd : HasDerivWithinAt sylSolution (sylField (sylSolution s)) (Ici s) s :=
      hsol.deriv s hs
    exact (Frobenius.hasDerivWithinAt_const_mul (rowFieldLeft 0) hd).add
      (Frobenius.hasDerivWithinAt_mul_const rowFieldRight hd)
  have hM₂ : ∀ j : ℕ, j < 1 → ∀ s ∈ Ico (0 + (j : ℝ) * h) (0 + ((j : ℝ) + 1) * h),
      ‖sylField (sylField (sylSolution s))‖ ≤ |C| := by
    intro j hj
    obtain rfl : j = 0 := Nat.lt_one_iff.1 hj
    rw [e0, e1]
    exact fun s hs => (hC s (Ico_subset_Icc_self hs)).trans (le_abs_self C)
  have hδ : ‖Y 0 - sylSolution 0‖ ≤ 0 := by rw [hY0, sylSolution_zero, sub_self, norm_zero]
  have key := rankAdaptive_global_error_le_of_sylvester (F := fun _ => sylField)
    (𝒜 := fun _ => rowFieldLeft 0) (ℬ := fun _ => rowFieldRight) (N := 1) (t₀ := 0)
    (A := sylSolution) (r := fun _ => 1) (ka := fun _ => 2) (kb := fun _ => 2)
    (U := fun _ => startLeft) (Sm := fun _ => 1) (V := fun _ => startRight)
    (Ua := fun _ => augmentedLeft) (Va := fun _ => 1) (K := fun _ => kSolution)
    (Lf := fun _ => lSolution) (Sa := fun _ => galerkinSolution) (Y := Y)
    (Φ := fun _ => sylSolution) (a₂ := fun _ s => sylField (sylField (sylSolution s)))
    (T := h) (fun _ _ => rfl) isLipschitzField_sylField (by positivity) hh continuousOn_const
    continuousOn_const hA hYf hstep hΦ hΦ₀ (abs_nonneg C) ha ha' hM₂ hδ 1 le_rfl (by simp)
  rw [hY1, eN] at key
  exact ⟨|C|, key⟩

end GlobalExample

end AugmentationRank

end LeanDLRA
