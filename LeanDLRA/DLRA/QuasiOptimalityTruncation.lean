import LeanDLRA.DLRA.QuasiOptimalityNormal

/-!
# Quasi-optimality of matrix DLRA against the truncated SVD with a margin below `ρ`

`dlra_norm_sub_truncation_le_integral` of `LeanDLRA/DLRA/QuasiOptimality.lean` bounds the distance
of the dynamical low-rank approximation `Y` of `A` to the truncated SVD `X t = T_r(A t)`,

  `‖Y t - X t‖ ≤ 2 β e^{β t} ∫₀ᵗ ‖X s - A s‖ ds`,   `β = 8 μ / ρ`,

if `ρ ≤ σ_{r-1}(A t)`, `‖Ȧ‖ ≤ μ` and `‖X t - A t‖ ≤ ρ / 16`. It is a case of the bound along a
curve of critical points, whose constants come from the Lipschitz constant of the tangent
projector. This file states the same case of the bound with the Lipschitz constant `1`
(`dlra_norm_sub_le_integral_of_margin_lt_one`): for every margin `‖X t - A t‖ ≤ θ ρ`, `θ < 1`,

  `‖Y t - X t‖ ≤ κ e^{(μ/ρ + κ) t} ∫₀ᵗ ‖X s - A s‖ ds`,   `κ = μ / ((1 - θ) ρ)`.

## Main results

* `dlra_norm_sub_truncation_le_integral_of_margin_lt_one`: the bound for the margin `θ ρ`,
  `θ < 1`. For `θ = 1 / 16` the factor is `16 μ / (15 ρ)` and the exponent `31 μ / (15 ρ)`, in
  place of `16 μ / ρ` and `8 μ / ρ`.
* `dlra_norm_sub_truncation_le_integral_of_norm_sub_le_half`: the margin `ρ / 2`,
  `‖Y t - X t‖ ≤ (2 μ / ρ) e^{(3 μ / ρ) t} ∫₀ᵗ ‖X s - A s‖ ds`.

## Implementation notes

The hypotheses are those of `dlra_norm_sub_truncation_le_integral` with the margin changed; that
`T_r(A t)` has rank `r` and `ρ ≤ σ_{r-1}(T_r(A t))` is
`EckartYoung.rank_truncation_of_le_singularValues` and `EckartYoung.le_singularValues_truncation`.
The `example`s restate `dlra_norm_sub_truncation_le_integral` and its recorded form
`dlra_quasiOptimal_matrix` verbatim and prove them from the bound with the margin `ρ / 2`, whose
hypothesis is weaker and whose two constants are smaller; the last one shows the hypotheses for a
curve with `A ≠ X`. Nothing is claimed on the optimality of the constants `κ` and `μ/ρ + κ`.

## References

* [KochLubich2007]
-/

open Set Matrix
open scoped LeanDLRA.Frobenius

namespace LeanDLRA

open EckartYoung

section Truncation

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Quasi-optimality of matrix DLRA against the truncated SVD, margin `θ ρ` with `θ < 1`.**
Let `X t = T_r(A t)` be differentiable with `ρ ≤ σ_{r-1}(A t)`, `‖X t - A t‖ ≤ θ ρ` for a
`θ < 1`, and `‖Ȧ‖ ≤ μ`, and let `Y = U S Vᵀ` solve the DLRA equation `Ẏ = P(Y) Ȧ` with
`Y 0 = X 0`. Then, with `κ = μ / ((1 - θ) ρ)`, for every `t ∈ [0, T]`

  `‖Y t - X t‖ ≤ κ e^{(μ/ρ + κ) t} ∫₀ᵗ ‖X s - A s‖ ds`.

These are the hypotheses of `dlra_norm_sub_truncation_le_integral` with the margin `θ ρ` in place
of `ρ / 16`. It is the case `F(t, Y) = Ȧ(t)`, `L = 0`, `δ = 0` of
`dlra_norm_sub_le_integral_of_margin_lt_one`. -/
theorem dlra_norm_sub_truncation_le_integral_of_margin_lt_one {r : ℕ} (hr : 0 < r)
    {A A' X X' Y : ℝ → Matrix m n ℝ} {T μ ρ θ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ t ∈ Icc 0 T, HasDerivAt A (A' t) t)
    (hμ : ∀ t ∈ Icc 0 T, ‖A' t‖ ≤ μ) (hXbest : ∀ t ∈ Icc 0 T, X t = truncation (A t) r)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (X' t) t)
    (hσ : ∀ t ∈ Icc 0 T, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1)) (hθ : θ < 1)
    (hd : ∀ t ∈ Icc 0 T, ‖X t - A t‖ ≤ θ * ρ)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc 0 T, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t _ => tangentProj (U t) (V t) (A' t)) Y 0 T) (hY₀ : Y 0 = X 0) :
    ∀ t ∈ Icc 0 T, ‖Y t - X t‖ ≤
      μ / ((1 - θ) * ρ) * Real.exp ((μ / ρ + μ / ((1 - θ) * ρ)) * t) *
        ∫ s in (0 : ℝ)..t, ‖X s - A s‖ := by
  intro t ht
  have hA' : ODESolution (fun t (_ : Matrix m n ℝ) => A' t) A 0 T :=
    ⟨fun s hs => (hA s hs).continuousAt.continuousWithinAt,
      fun s hs => (hA s (Ico_subset_Icc_self hs)).hasDerivWithinAt⟩
  have h := dlra_norm_sub_le_integral_of_margin_lt_one (F := fun t _ => A' t) (L := 0) (δ := 0)
    hρ le_rfl (fun t x y => by simp) hA' (fun s hs => hμ s (Ico_subset_Icc_self hs))
    (fun s hs => (hX s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hX s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (fun s hs => by
      rw [hXbest s hs]
      exact rank_truncation_of_le_singularValues hρ (hσ s hs))
    (fun s hs => by
      rw [hXbest s hs]
      exact le_singularValues_truncation hr hρ (hσ s hs))
    (fun s hs => by
      rw [hXbest s hs]
      exact tangentProjAt_truncation_sub_eq_zero _ _)
    hθ hd hUV hY (by rw [hY₀, sub_self, norm_zero]) t ht
  calc ‖Y t - X t‖ ≤ _ := h
    _ = _ := by
      simp only [zero_add, sub_zero]
      ring

/-- **Quasi-optimality of matrix DLRA against the truncated SVD, margin `ρ / 2`.** Under the
hypotheses of `dlra_norm_sub_truncation_le_integral` with `‖X t - A t‖ ≤ ρ / 2` in place of
`‖X t - A t‖ ≤ ρ / 16`, for every `t ∈ [0, T]`

  `‖Y t - X t‖ ≤ (2 μ / ρ) e^{(3 μ / ρ) t} ∫₀ᵗ ‖X s - A s‖ ds`.

It is `dlra_norm_sub_truncation_le_integral_of_margin_lt_one` for `θ = 1 / 2`. -/
theorem dlra_norm_sub_truncation_le_integral_of_norm_sub_le_half {r : ℕ} (hr : 0 < r)
    {A A' X X' Y : ℝ → Matrix m n ℝ} {T μ ρ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ t ∈ Icc 0 T, HasDerivAt A (A' t) t)
    (hμ : ∀ t ∈ Icc 0 T, ‖A' t‖ ≤ μ) (hXbest : ∀ t ∈ Icc 0 T, X t = truncation (A t) r)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (X' t) t)
    (hσ : ∀ t ∈ Icc 0 T, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1))
    (hd : ∀ t ∈ Icc 0 T, ‖X t - A t‖ ≤ ρ / 2)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc 0 T, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t _ => tangentProj (U t) (V t) (A' t)) Y 0 T) (hY₀ : Y 0 = X 0) :
    ∀ t ∈ Icc 0 T, ‖Y t - X t‖ ≤
      2 * μ / ρ * Real.exp (3 * μ / ρ * t) * ∫ s in (0 : ℝ)..t, ‖X s - A s‖ := by
  intro t ht
  have h := dlra_norm_sub_truncation_le_integral_of_margin_lt_one (θ := 1 / 2) hr hρ hA hμ hXbest
    hX hσ (by norm_num) (fun t ht => (hd t ht).trans_eq (by ring)) hUV hY hY₀ t ht
  have e1 : μ / ((1 - 1 / 2) * ρ) = 2 * μ / ρ := by
    rw [div_eq_div_iff (mul_pos (by norm_num) hρ).ne' hρ.ne']
    ring
  have e2 : μ / ρ + 2 * μ / ρ = 3 * μ / ρ := by ring
  rwa [e1, e2] at h

/-- The bound with the margin `ρ / 2` is below the bound of
`dlra_norm_sub_truncation_le_integral`. -/
private theorem half_bound_le {t μ ρ I : ℝ} (hρ : 0 < ρ) (hμ : 0 ≤ μ) (ht : 0 ≤ t)
    (hI : 0 ≤ I) :
    2 * μ / ρ * Real.exp (3 * μ / ρ * t) * I ≤
      2 * (8 * μ / ρ) * Real.exp (8 * μ / ρ * t) * I := by
  have hq : 0 ≤ μ / ρ := div_nonneg hμ hρ.le
  have hexp : Real.exp (3 * μ / ρ * t) ≤ Real.exp (8 * μ / ρ * t) := by
    refine Real.exp_le_exp.2 ?_
    have e1 : 3 * μ / ρ * t = 3 * (μ / ρ) * t := by ring
    have e2 : 8 * μ / ρ * t = 8 * (μ / ρ) * t := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (by linarith) ht
  have hc : 2 * μ / ρ ≤ 2 * (8 * μ / ρ) := by
    have e1 : 2 * μ / ρ = 2 * (μ / ρ) := by ring
    have e2 : 2 * (8 * μ / ρ) = 16 * (μ / ρ) := by ring
    rw [e1, e2]
    linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hc hexp (Real.exp_pos _).le (by positivity)) hI

/-- `dlra_norm_sub_truncation_le_integral`, restated verbatim, follows from the bound with the
margin `ρ / 2`: `ρ / 16 ≤ ρ / 2`, `2 μ / ρ ≤ 2 (8 μ / ρ)` and `3 μ / ρ ≤ 8 μ / ρ`. -/
example {r : ℕ} (hr : 0 < r)
    {A A' X X' Y : ℝ → Matrix m n ℝ} {T μ ρ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ t ∈ Icc 0 T, HasDerivAt A (A' t) t)
    (hμ : ∀ t ∈ Icc 0 T, ‖A' t‖ ≤ μ) (hXbest : ∀ t ∈ Icc 0 T, X t = truncation (A t) r)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (X' t) t)
    (hσ : ∀ t ∈ Icc 0 T, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1))
    (hd : ∀ t ∈ Icc 0 T, ‖X t - A t‖ ≤ ρ / 16)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc 0 T, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t _ => tangentProj (U t) (V t) (A' t)) Y 0 T) (hY₀ : Y 0 = X 0) :
    ∀ t ∈ Icc 0 T, ‖Y t - X t‖ ≤
      2 * (8 * μ / ρ) * Real.exp (8 * μ / ρ * t) * ∫ s in (0 : ℝ)..t, ‖X s - A s‖ := by
  intro t ht
  have h := dlra_norm_sub_truncation_le_integral_of_norm_sub_le_half hr hρ hA hμ hXbest hX hσ
    (fun t ht => (hd t ht).trans (by linarith)) hUV hY hY₀ t ht
  exact h.trans (half_bound_le hρ ((norm_nonneg _).trans (hμ 0 ⟨le_rfl, ht.1.trans ht.2⟩)) ht.1
    (intervalIntegral.integral_nonneg ht.1 fun _ _ => norm_nonneg _))

/-- `dlra_quasiOptimal_matrix`, the recorded form of the quasi-optimality theorem for matrices,
restated verbatim (with its redundant hypotheses and its instance `DecidableEq m`), follows from
the bound with the margin `ρ / 2`. -/
example [DecidableEq m] {r : ℕ} (hr : 0 < r) {A A' X X' Y : ℝ → Matrix m n ℝ}
    {T μ ρ : ℝ} (hρ : 0 < ρ) (hA : ∀ t ∈ Icc 0 T, HasDerivAt A (A' t) t)
    (hμ : ∀ t ∈ Icc 0 T, ‖A' t‖ ≤ μ) (hXbest : ∀ t ∈ Icc 0 T, X t = truncation (A t) r)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (X' t) t) (_hX'c : ContinuousOn X' (Icc 0 T))
    (hσ : ∀ t ∈ Icc 0 T, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1))
    (hd : ∀ t ∈ Icc 0 T, ‖X t - A t‖ ≤ ρ / 16)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc 0 T, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t _ => tangentProj (U t) (V t) (A' t)) Y 0 T) (hY₀ : Y 0 = X 0) :
    ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, ‖Y s - X s‖ ≤ ρ / 16) →
      ‖Y t - X t‖ ≤
        2 * (8 * μ / ρ) * Real.exp (8 * μ / ρ * t) * ∫ s in (0 : ℝ)..t, ‖X s - A s‖ := by
  intro t ht _
  have h := dlra_norm_sub_truncation_le_integral_of_norm_sub_le_half hr hρ hA hμ hXbest hX hσ
    (fun t ht => (hd t ht).trans (by linarith)) hUV hY hY₀ t ht
  exact h.trans (half_bound_le hρ ((norm_nonneg _).trans (hμ 0 ⟨le_rfl, ht.1.trans ht.2⟩)) ht.1
    (intervalIntegral.integral_nonneg ht.1 fun _ _ => norm_nonneg _))

end Truncation

/-! ### Examples -/

namespace QuasiOptimalityTruncationExamples

open QuasiOptimalityExamples

/-- **Non-vacuity of `dlra_norm_sub_truncation_le_integral_of_margin_lt_one` and of
`dlra_norm_sub_truncation_le_integral_of_norm_sub_le_half`** for `2 × 2` matrices, `r = 1`,
`A t = (1 + t) e₁ e₁ᵀ + diag(0, 1/16)` on `[0, 1]` (`Ȧ = e₁ e₁ᵀ`, `μ = ρ = 1`): the truncation
`X t = T₁(A t) = (1 + t) e₁ e₁ᵀ` differs from `A t`, `‖X t - A t‖ = 1/16`, which is below the
margins `θ ρ` with `θ = 1 / 16` and `ρ / 2`; the right-hand sides are positive for `t > 0`. Here
`Ȧ` is tangent at `X t`, so the DLRA solution is `X` itself and the left-hand sides are `0`. -/
example :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(1 + t) • (e₁ * e₁ᵀ) - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
      1 / ((1 - 1 / 16) * 1) * Real.exp ((1 / 1 + 1 / ((1 - 1 / 16) * 1)) * t) *
        ∫ s in (0 : ℝ)..t,
          ‖(1 + s) • (e₁ * e₁ᵀ) - ((1 + s) • (e₁ * e₁ᵀ) + !![0, 0; 0, 1 / 16])‖) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(1 + t) • (e₁ * e₁ᵀ) - (1 + t) • (e₁ * e₁ᵀ)‖ ≤
      2 * 1 / 1 * Real.exp (3 * 1 / 1 * t) *
        ∫ s in (0 : ℝ)..t,
          ‖(1 + s) • (e₁ * e₁ᵀ) - ((1 + s) • (e₁ * e₁ᵀ) + !![0, 0; 0, 1 / 16])‖) := by
  have hA : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + !![0, 0; 0, 1 / 16])
      ((fun _ : ℝ => e₁ * e₁ᵀ) t) t :=
    fun t _ => (hasDerivAt_smul_e₁ 1 t).add_const _
  have hμ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(fun _ : ℝ => e₁ * e₁ᵀ) t‖ ≤ 1 :=
    fun _ _ => norm_e₁_mul_le
  have hXbest : ∀ t ∈ Set.Icc (0 : ℝ) 1, (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) t =
      truncation ((fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + !![0, 0; 0, 1 / 16]) t) 1 :=
    fun t ht => (truncation_smul_e₁_add ht.1).symm
  have hX : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ))
      ((fun _ : ℝ => e₁ * e₁ᵀ) t) t := fun t _ => hasDerivAt_smul_e₁ 1 t
  have hσ : ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 : ℝ) ≤ (toEuclideanLin
      ((fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + !![0, 0; 0, 1 / 16]) t)).singularValues (1 - 1) :=
    fun t ht => one_le_singularValues_smul_e₁_add ht.1
  have hUV : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((fun _ : ℝ => e₁) t)ᵀ * (fun _ : ℝ => e₁) t = 1 ∧
      ((fun _ : ℝ => e₁) t)ᵀ * (fun _ : ℝ => e₁) t = 1 ∧
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) t =
        (fun _ : ℝ => e₁) t * (fun t : ℝ => (1 + t) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) t *
          ((fun _ : ℝ => e₁) t)ᵀ :=
    fun t _ => ⟨e₁_transpose_mul_self, e₁_transpose_mul_self, smul_e₁_mul _⟩
  have hY : ODESolution (fun t (_ : Matrix (Fin 2) (Fin 2) ℝ) =>
      tangentProj ((fun _ : ℝ => e₁) t) ((fun _ : ℝ => e₁) t) ((fun _ : ℝ => e₁ * e₁ᵀ) t))
      (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ)) 0 1 := by
    refine ⟨fun s _ => (hasDerivAt_smul_e₁ 1 s).continuousAt.continuousWithinAt, fun s hs => ?_⟩
    have h := (hasDerivAt_smul_e₁ 1 s).hasDerivWithinAt (s := Ici s)
    have hc : (1 + s) ≠ 0 := ne_of_gt (by linarith [hs.1])
    convert h using 1
    rw [← tangentProjAt_smul_e₁ hc]
    exact tangentProjAt_smul_e₁_apply hc
  exact ⟨dlra_norm_sub_truncation_le_integral_of_margin_lt_one (θ := 1 / 16) one_pos one_pos hA
      hμ hXbest hX hσ (by norm_num)
      (fun t _ => (norm_smul_e₁_sub_add_le t).trans_eq (by norm_num)) hUV hY rfl,
    dlra_norm_sub_truncation_le_integral_of_norm_sub_le_half one_pos one_pos hA hμ hXbest hX hσ
      (fun t _ => (norm_smul_e₁_sub_add_le t).trans (by norm_num)) hUV hY rfl⟩

end QuasiOptimalityTruncationExamples

end LeanDLRA
