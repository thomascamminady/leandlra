import LeanDLRA.Tensor.Tucker.NormalSecondOrder
import LeanDLRA.DLRA.QuasiOptimalityNormalVelocity

/-!
# Quasi-optimality of Tucker DLRA with the normal velocity as growth rate

`LeanDLRA/DLRA/QuasiOptimalityNormalVelocity.lean` bounds the error of matrix DLRA against a curve
`X` of rank-`r` matrices with a growth rate that contains the velocity of the exact solution only
through its component normal to the manifold at `X`. This file has the analogue for Tucker
tensors with `d` modes, with a rate that does not depend on `d`:

  `‖Y t - X t‖ ≤ e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖X s - A s‖ + g s) ds`,
  `k = L + (ν + ν') / √(2 ρ (ρ - 2 ε))`,

for a solution `Y` of `Ẏ = P(Y) F(t, Y)` in the tube `‖Y - X‖ ≤ ε < ρ/2` around a curve `X` of
Tucker tensors, where `ν ≥ ‖(1 - P(X)) F(t, A)‖`, `ν' ≥ ‖(1 - P(Y)) F(t, A)‖`,
`g ≥ ‖P(X) F(t, A) - Ẋ‖`, and `ρ` is a lower bound of the smallest nonzero singular values of
all matricizations of `X` and of `Y`. To first order in `ε` the rate is `L + √2 ν/ρ`.

## Main results

* `LeanDLRA.norm_sub_le_integral_exp_integral_of_inner_apply_sub_apply_le`: the error bound in a
  real inner product space for a curve `Y` with `Ẏ = P_Y(t) F(t, Y)`, orthogonal projectors
  `P_Y(t)`, and any rate `κ` with `⟪Y - X, (P_Y - P_X) F(t, A)⟫ ≤ κ ‖Y - X‖²`.
* `LeanDLRA.Tensor.sub_norm_sub_le_singularValues_unfold_ne`: Weyl's inequality for unfoldings.
* `LeanDLRA.Tensor.tuckerTangentProj_tucker`: the tangent projector at a Tucker tensor fixes it.
* `LeanDLRA.Tensor.inner_sub_tuckerTangentProj_sub_le`: for Tucker tensors `X`, `Y` with
  `2 ‖Y - X‖ < ρ`,
  `⟪Y - X, P(Y) Z - P(X) Z⟫ ≤ (‖Z - P(Y) Z‖ + ‖Z - P(X) Z‖) ‖Y - X‖² / √(2 ρ (ρ - 2 ‖Y - X‖))`.
* `LeanDLRA.Tensor.norm_tucker_sub_tucker_le_integral_exp_integral`: the error bound above.

## Implementation notes

By `IsOrthProj.inner_sub_apply_sub_apply` the inner product is the sum of the inner products of
the normal component of `X` at `Y` with that of `Z`, and of the normal component of `Y` at `X`
with that of `Z`. The normal components of the points are of second order with a constant
independent of the number of modes (`norm_sub_tuckerTangentProj_tucker_le`). The number of modes
enters only when `ν'` is bounded by data at `X`: `ν' ≤ ν + √d ρ⁻¹ ε ‖F(t, A)‖` by
`norm_tuckerTangentProj_sub_le`, a term of second order in `ε` in the rate.

## References

* [BachmayrEisenmannUschmajew2025]
-/

open Set Finset Matrix Filter
open scoped Topology RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Error bound for projected dynamics from a rate of the projector difference.** Let `F` be
`L`-Lipschitz, `Y` a curve with right derivatives `P_Y(t) F(t, Y t)` on `[a, b)` for orthogonal
projectors `P_Y(t)`, `A` a continuous curve and `X` a continuous curve with right derivatives
`X'`. Let `κ`, `g` be continuous on `[a, b]` with

  `⟪Y t - X t, P_Y(t) F(t, A t) - P_X(t) F(t, A t)⟫ ≤ κ t ‖Y t - X t‖²`,
  `‖P_X(t) F(t, A t) - X' t‖ ≤ g t`

on `[a, b)`. If `‖Y a - X a‖ ≤ δ`, then for `t ∈ [a, b]`

  `‖Y t - X t‖ ≤ e^{∫ₐᵗ (L + κ)} δ + ∫ₐᵗ e^{∫ₛᵗ (L + κ)} (L ‖X s - A s‖ + g s) ds`. -/
theorem norm_sub_le_integral_exp_integral_of_inner_apply_sub_apply_le {F : ℝ → E → E}
    {A X X' Y : ℝ → E} {PY PX : ℝ → E →L[ℝ] E} {κ g : ℝ → ℝ} {a b L δ : ℝ} (hL : 0 ≤ L)
    (hF : IsLipschitzField F L) (hPY : ∀ t ∈ Ico a b, IsOrthProj (PY t))
    (hYc : ContinuousOn Y (Icc a b))
    (hY : ∀ t ∈ Ico a b, HasDerivWithinAt Y (PY t (F t (Y t))) (Ici t) t)
    (hAc : ContinuousOn A (Icc a b)) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hκc : ContinuousOn κ (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hκ : ∀ t ∈ Ico a b,
      ⟪Y t - X t, PY t (F t (A t)) - PX t (F t (A t))⟫ ≤ κ t * ‖Y t - X t‖ ^ 2)
    (hg : ∀ t ∈ Ico a b, ‖PX t (F t (A t)) - X' t‖ ≤ g t) (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      Real.exp (∫ u in a..t, (L + κ u)) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t, (L + κ u)) * (L * ‖X s - A s‖ + g s) := by
  intro t0 ht0
  rcases eq_or_lt_of_le ht0.1 with h0 | hpos
  · subst h0
    simpa using hδ
  have hab : a < b := hpos.trans_le ht0.2
  have hIcc : Icc a t0 ⊆ Icc a b := Icc_subset_Icc_right ht0.2
  have hIco : ∀ s ∈ Ico a t0, s ∈ Ico a b := fun s hs => ⟨hs.1, hs.2.trans_le ht0.2⟩
  have hkOn : ContinuousOn (fun u => L + κ u) (Icc a b) := continuousOn_const.add hκc
  have hgOn : ContinuousOn (fun s => L * ‖X s - A s‖ + g s) (Icc a b) :=
    (continuousOn_const.mul (hXc.sub hAc).norm).add hgc
  obtain ⟨kc, hkc, hkeq⟩ : ∃ kc : ℝ → ℝ, Continuous kc ∧ ∀ s ∈ Icc a b, kc s = L + κ s :=
    ⟨fun s => L + κ (projIcc a b hab.le s),
      hkOn.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        fun s => (projIcc a b hab.le s).2,
      fun s hs => by simp only [projIcc_of_mem _ hs]⟩
  obtain ⟨gc, hgcc, hgeq⟩ : ∃ gc : ℝ → ℝ, Continuous gc ∧ ∀ s ∈ Icc a b, gc s =
      L * ‖X s - A s‖ + g s :=
    ⟨fun s => L * ‖X (projIcc a b hab.le s) - A (projIcc a b hab.le s)‖ +
        g (projIcc a b hab.le s),
      hgOn.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        fun s => (projIcc a b hab.le s).2,
      fun s hs => by simp only [projIcc_of_mem _ hs]⟩
  have hg0 : ∀ s ∈ Ico a t0, 0 ≤ gc s := fun s hs => by
    rw [hgeq s (Ico_subset_Icc_self (hIco s hs))]
    exact add_nonneg (mul_nonneg hL (norm_nonneg _))
      ((norm_nonneg _).trans (hg s (hIco s hs)))
  have hbound : ∀ s ∈ Ico a t0,
      ⟪Y s - X s, PY s (F s (Y s)) - X' s⟫ ≤ (kc s * ‖Y s - X s‖ + gc s) * ‖Y s - X s‖ :=
    fun s hs => by
      have hsb := hIco s hs
      have hsI := Ico_subset_Icc_self hsb
      have hsplit : PY s (F s (Y s)) - X' s = PY s (F s (Y s) - F s (A s)) +
          (PY s (F s (A s)) - PX s (F s (A s))) + (PX s (F s (A s)) - X' s) := by
        rw [map_sub]
        abel
      have i1 : ⟪Y s - X s, PY s (F s (Y s) - F s (A s))⟫ ≤
          ‖Y s - X s‖ * (L * ‖Y s - X s‖ + L * ‖X s - A s‖) := by
        refine (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        refine ((hPY s hsb).norm_le _).trans ((hF s _ _).trans ?_)
        rw [← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ hL
        calc ‖Y s - A s‖ = ‖(Y s - X s) + (X s - A s)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖Y s - X s‖ + ‖X s - A s‖ := norm_add_le _ _
      have i3 : ⟪Y s - X s, PX s (F s (A s)) - X' s⟫ ≤ ‖Y s - X s‖ * g s :=
        (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hg s hsb) (norm_nonneg _))
      rw [hsplit, inner_add_right, inner_add_right, hkeq s hsI, hgeq s hsI]
      calc _ ≤ ‖Y s - X s‖ * (L * ‖Y s - X s‖ + L * ‖X s - A s‖) +
            κ s * ‖Y s - X s‖ ^ 2 + ‖Y s - X s‖ * g s := add_le_add (add_le_add i1 (hκ s hsb)) i3
        _ = _ := by ring
  have hcmp := norm_le_exp_integral_mul_add_integral_exp_integral_mul_of_inner_le
    (f := fun t => Y t - X t) (f' := fun t => PY t (F t (Y t)) - X' t) (δ := δ) hkc hgcc hg0
    ((hYc.sub hXc).mono hIcc)
    (fun s hs => (hY s (hIco s hs)).sub (hX s (hIco s hs))) hδ hbound t0 ⟨ht0.1, le_rfl⟩
  have e1 : ∫ u in a..t0, kc u = ∫ u in a..t0, (L + κ u) :=
    intervalIntegral.integral_congr fun u hu => by
      rw [uIcc_of_le ht0.1] at hu
      exact hkeq u (hIcc hu)
  have e2 : ∫ s in a..t0, Real.exp (∫ u in s..t0, kc u) * gc s =
      ∫ s in a..t0, Real.exp (∫ u in s..t0, (L + κ u)) * (L * ‖X s - A s‖ + g s) :=
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le ht0.1] at hs
      have e3 : ∫ u in s..t0, kc u = ∫ u in s..t0, (L + κ u) :=
        intervalIntegral.integral_congr fun u hu => by
          rw [uIcc_of_le hs.2] at hu
          exact hkeq u ⟨hs.1.trans hu.1, hu.2.trans ht0.2⟩
      change Real.exp (∫ u in s..t0, kc u) * gc s = _
      rw [e3, hgeq s (hIcc hs)]
  rw [e1, e2] at hcmp
  exact hcmp

/-- Non-vacuity of `norm_sub_le_integral_exp_integral_of_inner_apply_sub_apply_le`: on the real
line, the field `F = 0`, the constant curves `Y = 1`, `X = A = 0`, the projectors `1`, the rates
`κ = g = 0`, `L = 0` and `δ = 1` on `[0, 1]`. -/
example : ∀ t ∈ Icc (0 : ℝ) 1, ‖(1 : ℝ) - 0‖ ≤
    Real.exp (∫ _ in (0 : ℝ)..t, ((0 : ℝ) + 0)) * 1 +
      ∫ s in (0 : ℝ)..t, Real.exp (∫ _ in s..t, ((0 : ℝ) + 0)) * (0 * ‖(0 : ℝ) - 0‖ + 0) :=
  norm_sub_le_integral_exp_integral_of_inner_apply_sub_apply_le (F := fun _ _ => (0 : ℝ))
    (A := fun _ => 0) (X := fun _ => 0) (X' := fun _ => 0) (Y := fun _ => 1)
    (PY := fun _ => 1) (PX := fun _ => 1) (κ := fun _ => 0) (g := fun _ => 0) le_rfl
    (fun _ _ _ => by simp) (fun _ _ => IsOrthProj.one) continuousOn_const
    (fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) (1 : ℝ)) continuousOn_const
    continuousOn_const (fun t _ => hasDerivWithinAt_const t (Ici t) (0 : ℝ)) continuousOn_const
    continuousOn_const (fun _ _ => by simp) (fun _ _ => by simp) (by simp)

end Abstract

namespace Tensor

section TuckerQuasiOptimality

variable {d : ℕ} {ι r : Fin d → Type*} [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)]
  [∀ k, Fintype (r k)] [∀ k, DecidableEq (r k)] {s s' : Fin d → Type*} [∀ k, Fintype (s k)]
  [∀ k, Fintype (s' k)]

/-- **Weyl's inequality for the unfoldings of two tensors**:
`σᵢ(Mat_{≠k}(X)) - ‖Y - X‖ ≤ σᵢ(Mat_{≠k}(Y))`. -/
theorem sub_norm_sub_le_singularValues_unfold_ne (k : Fin d) (X Y : Tensor ι) (i : ℕ) :
    (toEuclideanLin (unfold (· ≠ k) X)).singularValues i - ‖Y - X‖ ≤
      (toEuclideanLin (unfold (· ≠ k) Y)).singularValues i := by
  have h := (abs_le.1 (WeylSingular.abs_singularValues_sub_le_frobenius (unfold (· ≠ k) Y)
    (unfold (· ≠ k) X) i)).1
  rw [← unfold_sub, norm_unfold] at h
  linarith

omit [∀ k, DecidableEq (ι k)] in
/-- The tangent projector at a Tucker tensor `X = C ×ₖ Uₖ` with orthonormal `Uₖ` and co-range
bases `W` fixing `X` maps `X` to itself. -/
theorem tuckerTangentProj_tucker {U : ∀ k, Matrix (ι k) (r k) ℝ} {C : Tensor r}
    {W : ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s k) ℝ} (hU : ∀ k, (U k)ᵀ * U k = 1)
    (hWX : ∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U) :
    tuckerTangentProj U 1 W (tucker C U) = tucker C U := by
  have h : modeTangentProj (fun k => modeProj k (U k))
      (fun k => actOn (· ≠ k) (W k * (W k)ᵀ)) (tucker C U) =
      modeProd (fun k => modeProj k (U k)) (tucker C U) +
        ∑ k, (actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) -
          modeProj k (U k) (actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U))) := by
    simp [modeTangentProj]
  rw [tuckerTangentProj_one_eq, h, modeProd_modeProj_tucker hU C,
    Finset.sum_eq_zero fun k _ => by rw [hWX k, modeProj_tucker k (hU k) C, sub_self],
    add_zero]

variable {U U' : ∀ k, Matrix (ι k) (r k) ℝ} {C C' : Tensor r}
  {W : ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s k) ℝ}
  {W' : ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s' k) ℝ}

/-- **The tangent projectors at two Tucker tensors, tested with their difference.** Let
`X = C ×ₖ Uₖ` and `Y = C' ×ₖ U'ₖ` be Tucker tensors with `d` modes, orthonormal `Uₖ`, `U'ₖ` and
co-range bases `W`, `W'` as in `tuckerTangentProj_eq_starProjection`, let `ρ` be a lower bound of
the singular values `σ_{|r k|}` of all unfoldings of `X` and of `Y`, and `2 ‖Y - X‖ < ρ`. For
every tensor `Z`

  `⟪Y - X, P(Y) Z - P(X) Z⟫ ≤ (‖Z - P(Y) Z‖ + ‖Z - P(X) Z‖) ‖Y - X‖² / √(2 ρ (ρ - 2 ‖Y - X‖))`.

The right-hand side has the normal components of `Z` only, and no constant depends on `d`. -/
theorem inner_sub_tuckerTangentProj_sub_le (hU : ∀ k, (U k)ᵀ * U k = 1)
    (hWX : ∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U)
    (hWB : ∀ k, ∃ B : Matrix _ (s k) ℝ, W k = unfold (· ≠ k) (tucker C U) * B)
    (hU' : ∀ k, (U' k)ᵀ * U' k = 1)
    (hWX' : ∀ k, actOn (· ≠ k) (W' k * (W' k)ᵀ) (tucker C' U') = tucker C' U')
    (hWB' : ∀ k, ∃ B : Matrix _ (s' k) ℝ, W' k = unfold (· ≠ k) (tucker C' U') * B) {ρ : ℝ}
    (hσ : ∀ k, ρ ≤ (toEuclideanLin (unfold (· ≠ k) (tucker C U))).singularValues
      (Fintype.card (r k) - 1))
    (hσ' : ∀ k, ρ ≤ (toEuclideanLin (unfold (· ≠ k) (tucker C' U'))).singularValues
      (Fintype.card (r k) - 1))
    (he : 2 * ‖tucker C' U' - tucker C U‖ < ρ) (Z : Tensor ι) :
    ⟪tucker C' U' - tucker C U, tuckerTangentProj U' 1 W' Z - tuckerTangentProj U 1 W Z⟫ ≤
      (‖Z - tuckerTangentProj U' 1 W' Z‖ + ‖Z - tuckerTangentProj U 1 W Z‖) *
        (‖tucker C' U' - tucker C U‖ ^ 2 /
          √(2 * ρ * (ρ - 2 * ‖tucker C' U' - tucker C U‖))) := by
  have hPX := isOrthProj_tuckerTangentProj hU IsOrthProj.one hWX hWB
  have hPY := isOrthProj_tuckerTangentProj hU' IsOrthProj.one hWX' hWB'
  have hid := hPY.inner_sub_apply_sub_apply hPX (tuckerTangentProj_tucker hU' hWX')
    (tuckerTangentProj_tucker hU hWX) Z
  have he' : 2 * ‖tucker C U - tucker C' U'‖ < ρ := by rwa [norm_sub_rev]
  have n1 := norm_sub_tuckerTangentProj_tucker_le hU hU' hWX' hWB' hσ' he'
  rw [norm_sub_rev (tucker C U) (tucker C' U')] at n1
  have n2 := norm_sub_tuckerTangentProj_tucker_le hU' hU hWX hWB hσ he
  rw [hid]
  calc ⟪tucker C U - tuckerTangentProj U' 1 W' (tucker C U), Z - tuckerTangentProj U' 1 W' Z⟫ +
        ⟪tucker C' U' - tuckerTangentProj U 1 W (tucker C' U'), Z - tuckerTangentProj U 1 W Z⟫
      ≤ ‖tucker C U - tuckerTangentProj U' 1 W' (tucker C U)‖ *
          ‖Z - tuckerTangentProj U' 1 W' Z‖ +
        ‖tucker C' U' - tuckerTangentProj U 1 W (tucker C' U')‖ *
          ‖Z - tuckerTangentProj U 1 W Z‖ :=
        add_le_add (real_inner_le_norm _ _) (real_inner_le_norm _ _)
    _ ≤ ‖tucker C' U' - tucker C U‖ ^ 2 / √(2 * ρ * (ρ - 2 * ‖tucker C' U' - tucker C U‖)) *
          ‖Z - tuckerTangentProj U' 1 W' Z‖ +
        ‖tucker C' U' - tucker C U‖ ^ 2 / √(2 * ρ * (ρ - 2 * ‖tucker C' U' - tucker C U‖)) *
          ‖Z - tuckerTangentProj U 1 W Z‖ :=
        add_le_add (mul_le_mul_of_nonneg_right n1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right n2 (norm_nonneg _))
    _ = _ := by ring

/-- **Quasi-optimality of Tucker DLRA with the normal velocity as growth rate.** Let `F` be
`L`-Lipschitz, let `Y t = C_Y(t) ×ₖ U_Y(t)ₖ` solve `Ẏ = P(Y) F(t, Y)` on `[a, b]` (right
derivatives), let `A` be a continuous curve and `X t = C_X(t) ×ₖ U_X(t)ₖ` a continuous curve of
Tucker tensors with right derivatives `X'`, with orthonormal bases and co-range bases as in
`tuckerTangentProj_eq_starProjection` at every time. Let `ρ`, `ν`, `ν'`, `g`, `ε` be continuous
on `[a, b]`, `ρ t` a lower bound of the singular values `σ_{|r k|}` of all unfoldings of `X t`
and of `Y t`, `‖(1 - P(X t)) F(t, A t)‖ ≤ ν t`, `‖(1 - P(Y t)) F(t, A t)‖ ≤ ν' t`,
`‖P(X t) F(t, A t) - X' t‖ ≤ g t`, `0 ≤ 2 ε t < ρ t` and `‖Y t - X t‖ ≤ ε t`. If
`‖Y a - X a‖ ≤ δ`, then with `k = L + (ν + ν') / √(2 ρ (ρ - 2 ε))`, for `t ∈ [a, b]`

  `‖Y t - X t‖ ≤ e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖X s - A s‖ + g s) ds`.

No constant depends on the number `d` of modes. -/
theorem norm_tucker_sub_tucker_le_integral_exp_integral {F : ℝ → Tensor ι → Tensor ι}
    {A X' : ℝ → Tensor ι} {CX CY : ℝ → Tensor r} {UX UY : ℝ → ∀ k, Matrix (ι k) (r k) ℝ}
    {WX : ℝ → ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s k) ℝ}
    {WY : ℝ → ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s' k) ℝ}
    {ρ ν ν' g ε : ℝ → ℝ} {a b L δ : ℝ} (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hUX : ∀ t ∈ Icc a b, ∀ k, (UX t k)ᵀ * UX t k = 1)
    (hWXfix : ∀ t ∈ Icc a b, ∀ k,
      actOn (· ≠ k) (WX t k * (WX t k)ᵀ) (tucker (CX t) (UX t)) = tucker (CX t) (UX t))
    (hWXB : ∀ t ∈ Icc a b, ∀ k,
      ∃ B : Matrix _ (s k) ℝ, WX t k = unfold (· ≠ k) (tucker (CX t) (UX t)) * B)
    (hUY : ∀ t ∈ Icc a b, ∀ k, (UY t k)ᵀ * UY t k = 1)
    (hWYfix : ∀ t ∈ Icc a b, ∀ k,
      actOn (· ≠ k) (WY t k * (WY t k)ᵀ) (tucker (CY t) (UY t)) = tucker (CY t) (UY t))
    (hWYB : ∀ t ∈ Icc a b, ∀ k,
      ∃ B : Matrix _ (s' k) ℝ, WY t k = unfold (· ≠ k) (tucker (CY t) (UY t)) * B)
    (hσX : ∀ t ∈ Icc a b, ∀ k, ρ t ≤ (toEuclideanLin (unfold (· ≠ k)
      (tucker (CX t) (UX t)))).singularValues (Fintype.card (r k) - 1))
    (hσY : ∀ t ∈ Icc a b, ∀ k, ρ t ≤ (toEuclideanLin (unfold (· ≠ k)
      (tucker (CY t) (UY t)))).singularValues (Fintype.card (r k) - 1))
    (hYc : ContinuousOn (fun t => tucker (CY t) (UY t)) (Icc a b))
    (hY : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => tucker (CY t) (UY t))
      (tuckerTangentProj (UY t) 1 (WY t) (F t (tucker (CY t) (UY t)))) (Ici t) t)
    (hAc : ContinuousOn A (Icc a b))
    (hXc : ContinuousOn (fun t => tucker (CX t) (UX t)) (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => tucker (CX t) (UX t)) (X' t) (Ici t) t)
    (hρc : ContinuousOn ρ (Icc a b)) (hνc : ContinuousOn ν (Icc a b))
    (hν'c : ContinuousOn ν' (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hεc : ContinuousOn ε (Icc a b))
    (hν : ∀ t ∈ Ico a b,
      ‖F t (A t) - tuckerTangentProj (UX t) 1 (WX t) (F t (A t))‖ ≤ ν t)
    (hν' : ∀ t ∈ Ico a b,
      ‖F t (A t) - tuckerTangentProj (UY t) 1 (WY t) (F t (A t))‖ ≤ ν' t)
    (hg : ∀ t ∈ Ico a b, ‖tuckerTangentProj (UX t) 1 (WX t) (F t (A t)) - X' t‖ ≤ g t)
    (hε0 : ∀ t ∈ Icc a b, 0 ≤ ε t) (hερ : ∀ t ∈ Icc a b, 2 * ε t < ρ t)
    (htube : ∀ t ∈ Ico a b, ‖tucker (CY t) (UY t) - tucker (CX t) (UX t)‖ ≤ ε t)
    (hδ : ‖tucker (CY a) (UY a) - tucker (CX a) (UX a)‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖tucker (CY t) (UY t) - tucker (CX t) (UX t)‖ ≤
      Real.exp (∫ u in a..t, (L + (ν u + ν' u) / √(2 * ρ u * (ρ u - 2 * ε u)))) * δ +
        ∫ s in a..t,
          Real.exp (∫ u in s..t, (L + (ν u + ν' u) / √(2 * ρ u * (ρ u - 2 * ε u)))) *
            (L * ‖tucker (CX s) (UX s) - A s‖ + g s) := by
  have hpos : ∀ t ∈ Icc a b, 0 < 2 * ρ t * (ρ t - 2 * ε t) := fun t ht =>
    mul_pos (by linarith [hε0 t ht, hερ t ht]) (by linarith [hερ t ht])
  refine norm_sub_le_integral_exp_integral_of_inner_apply_sub_apply_le
    (PY := fun t => tuckerTangentProj (UY t) 1 (WY t))
    (PX := fun t => tuckerTangentProj (UX t) 1 (WX t))
    (κ := fun t => (ν t + ν' t) / √(2 * ρ t * (ρ t - 2 * ε t))) hL hF
    (fun t ht => isOrthProj_tuckerTangentProj (hUY t (Ico_subset_Icc_self ht)) IsOrthProj.one
      (hWYfix t (Ico_subset_Icc_self ht)) (hWYB t (Ico_subset_Icc_self ht)))
    hYc hY hAc hXc hX ?_ hgc (fun t ht => ?_) hg hδ
  · exact (hνc.add hν'c).div (Real.continuous_sqrt.comp_continuousOn
      ((continuousOn_const.mul hρc).mul (hρc.sub (continuousOn_const.mul hεc))))
      fun t ht => (Real.sqrt_pos.2 (hpos t ht)).ne'
  · have hI := Ico_subset_Icc_self ht
    have he := htube t ht
    have he0 := norm_nonneg (tucker (CY t) (UY t) - tucker (CX t) (UX t))
    have h := inner_sub_tuckerTangentProj_sub_le (hUX t hI) (hWXfix t hI) (hWXB t hI)
      (hUY t hI) (hWYfix t hI) (hWYB t hI) (hσX t hI) (hσY t hI)
      (by linarith [hερ t hI]) (F t (A t))
    refine h.trans ?_
    have hρ0 : 0 < ρ t := by linarith [hε0 t hI, hερ t hI]
    have hs : √(2 * ρ t * (ρ t - 2 * ε t)) ≤
        √(2 * ρ t * (ρ t - 2 * ‖tucker (CY t) (UY t) - tucker (CX t) (UX t)‖)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
    have hn := norm_nonneg (F t (A t) - tuckerTangentProj (UY t) 1 (WY t) (F t (A t)))
    have hn' := norm_nonneg (F t (A t) - tuckerTangentProj (UX t) 1 (WX t) (F t (A t)))
    calc (‖F t (A t) - tuckerTangentProj (UY t) 1 (WY t) (F t (A t))‖ +
          ‖F t (A t) - tuckerTangentProj (UX t) 1 (WX t) (F t (A t))‖) *
          (‖tucker (CY t) (UY t) - tucker (CX t) (UX t)‖ ^ 2 /
            √(2 * ρ t * (ρ t - 2 * ‖tucker (CY t) (UY t) - tucker (CX t) (UX t)‖)))
        ≤ (ν t + ν' t) * (‖tucker (CY t) (UY t) - tucker (CX t) (UX t)‖ ^ 2 /
            √(2 * ρ t * (ρ t - 2 * ε t))) :=
          mul_le_mul (by linarith [hν t ht, hν' t ht])
            (div_le_div_of_nonneg_left (sq_nonneg _) (Real.sqrt_pos.2 (hpos t hI)) hs)
            (div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
            (by linarith [hν t ht, hν' t ht])
      _ = (ν t + ν' t) / √(2 * ρ t * (ρ t - 2 * ε t)) *
            ‖tucker (CY t) (UY t) - tucker (CX t) (UX t)‖ ^ 2 := by ring

end TuckerQuasiOptimality

/-! ### Examples -/

namespace TuckerQuasiOptimalityNormalVelocityExamples

open TuckerNormalSecondOrderExamples

/-- The singular value of the unfolding of a constant tensor changes by at most the change of
the constant. -/
theorem sub_abs_le_singularValues_unfold_const (k : Fin 1) (c η : ℝ) :
    (toEuclideanLin (unfold (ι := fun _ : Fin 1 => Fin 1) (· ≠ k)
        (WithLp.toLp 2 fun _ => c))).singularValues (Fintype.card (Fin 1) - 1) - |η| ≤
      (toEuclideanLin (unfold (ι := fun _ : Fin 1 => Fin 1) (· ≠ k)
        (WithLp.toLp 2 fun _ => c + η))).singularValues (Fintype.card (Fin 1) - 1) := by
  have h := sub_norm_sub_le_singularValues_unfold_ne k
    (WithLp.toLp 2 fun _ => c : Tensor fun _ : Fin 1 => Fin 1) (WithLp.toLp 2 fun _ => c + η)
    (Fintype.card (Fin 1) - 1)
  rw [norm_const_sub_const, add_sub_cancel_left] at h
  exact h

/-- Non-vacuity of `inner_sub_tuckerTangentProj_sub_le` with `X ≠ Y`: one mode of dimension one,
`X` the tensor with the entry `3`, `s` the singular value of its unfolding, `Y` the tensor with
the entry `3 + s/8`, and `ρ = s/2`. All hypotheses hold. (With one mode both tangent projectors
are the identity.) -/
example : ∃ s : ℝ, 0 < s ∧ ∀ Z : Tensor fun _ : Fin 1 => Fin 1,
    ⟪tucker (ι := fun _ : Fin 1 => Fin 1) (WithLp.toLp 2 fun _ => 3 + s / 8)
          (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) -
        tucker (WithLp.toLp 2 fun _ => (3 : ℝ)) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)),
      tuckerTangentProj (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) 1
          (fun k => (Matrix.of fun _ _ => 1 : Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ)) Z -
        tuckerTangentProj (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) 1
          (fun k => (Matrix.of fun _ _ => 1 : Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ))
          Z⟫ ≤
      (‖Z - tuckerTangentProj (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) 1
          (fun k => (Matrix.of fun _ _ => 1 : Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ))
          Z‖ +
        ‖Z - tuckerTangentProj (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) 1
          (fun k => (Matrix.of fun _ _ => 1 : Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ))
          Z‖) *
        (‖tucker (ι := fun _ : Fin 1 => Fin 1) (WithLp.toLp 2 fun _ => 3 + s / 8)
              (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) -
            tucker (WithLp.toLp 2 fun _ => (3 : ℝ))
              (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))‖ ^ 2 /
          √(2 * (s / 2) * (s / 2 - 2 *
            ‖tucker (ι := fun _ : Fin 1 => Fin 1) (WithLp.toLp 2 fun _ => 3 + s / 8)
                (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) -
              tucker (WithLp.toLp 2 fun _ => (3 : ℝ))
                (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))‖))) := by
  have hs := singularValues_unfold_const_pos
  refine ⟨_, hs, fun Z => ?_⟩
  refine inner_sub_tuckerTangentProj_sub_le (fun _ => by simp)
    (fun k => by rw [tucker_const]; exact actOn_const k 3)
    (fun k => by rw [tucker_const]; exact coRange_const k three_ne_zero) (fun _ => by simp)
    (fun k => by rw [tucker_const]; exact actOn_const k _)
    (fun k => by rw [tucker_const]; exact coRange_const k (by positivity))
    (fun k => by
      obtain rfl : k = 0 := Subsingleton.elim _ _
      rw [tucker_const]
      linarith)
    (fun k => by
      obtain rfl : k = 0 := Subsingleton.elim _ _
      rw [tucker_const]
      have h := sub_abs_le_singularValues_unfold_const 0 3
        ((toEuclideanLin (unfold (ι := fun _ : Fin 1 => Fin 1) (· ≠ (0 : Fin 1))
          (WithLp.toLp 2 fun _ => (3 : ℝ)))).singularValues (Fintype.card (Fin 1) - 1) / 8)
      rw [abs_of_pos (by positivity)] at h
      linarith) ?_ Z
  rw [tucker_const, tucker_const, norm_const_sub_const, add_sub_cancel_left,
    abs_of_pos (by positivity)]
  linarith

/-- Non-vacuity of `norm_tucker_sub_tucker_le_integral_exp_integral` with `X ≠ Y`: one mode of
dimension one, `X` the constant curve with the entry `3`, `s` the singular value of its
unfolding, `Y` the constant curve with the entry `3 + s/8`, the field `F = 0`, `ρ = s/2`,
`ε = δ = s/8`, `ν = ν' = g = L = 0` on `[0, 1]`. All hypotheses hold (the rate and the source are
zero here). -/
example : ∃ s : ℝ, 0 < s ∧ ∀ t ∈ Icc (0 : ℝ) 1,
    ‖tucker (ι := fun _ : Fin 1 => Fin 1) (WithLp.toLp 2 fun _ => 3 + s / 8)
          (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) -
        tucker (WithLp.toLp 2 fun _ => (3 : ℝ)) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))‖ ≤
      Real.exp (∫ _ in (0 : ℝ)..t,
          ((0 : ℝ) + (0 + 0) / √(2 * (s / 2) * (s / 2 - 2 * (s / 8))))) * (s / 8) +
        ∫ u in (0 : ℝ)..t,
          Real.exp (∫ _ in u..t, ((0 : ℝ) + (0 + 0) / √(2 * (s / 2) * (s / 2 - 2 * (s / 8))))) *
            (0 * ‖tucker (ι := fun _ : Fin 1 => Fin 1) (WithLp.toLp 2 fun _ => (3 : ℝ))
              (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) - 0‖ + 0) := by
  have hs := singularValues_unfold_const_pos
  refine ⟨_, hs, ?_⟩
  have hd : ‖tucker (ι := fun _ : Fin 1 => Fin 1) (WithLp.toLp 2 fun _ => 3 +
        (toEuclideanLin (unfold (ι := fun _ : Fin 1 => Fin 1) (· ≠ (0 : Fin 1))
          (WithLp.toLp 2 fun _ => (3 : ℝ)))).singularValues (Fintype.card (Fin 1) - 1) / 8)
        (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) -
      tucker (WithLp.toLp 2 fun _ => (3 : ℝ)) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))‖ =
      (toEuclideanLin (unfold (ι := fun _ : Fin 1 => Fin 1) (· ≠ (0 : Fin 1))
        (WithLp.toLp 2 fun _ => (3 : ℝ)))).singularValues (Fintype.card (Fin 1) - 1) / 8 := by
    rw [tucker_const, tucker_const, norm_const_sub_const, add_sub_cancel_left,
      abs_of_pos (by positivity)]
  exact norm_tucker_sub_tucker_le_integral_exp_integral
    (F := fun _ _ => (0 : Tensor fun _ : Fin 1 => Fin 1)) (A := fun _ => 0) (X' := fun _ => 0)
    (CX := fun _ => WithLp.toLp 2 fun _ => (3 : ℝ))
    (CY := fun _ => WithLp.toLp 2 fun _ => 3 +
      (toEuclideanLin (unfold (ι := fun _ : Fin 1 => Fin 1) (· ≠ (0 : Fin 1))
        (WithLp.toLp 2 fun _ => (3 : ℝ)))).singularValues (Fintype.card (Fin 1) - 1) / 8)
    (UX := fun _ _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (UY := fun _ _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (WX := fun _ k => (Matrix.of fun _ _ => 1 :
      Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ))
    (WY := fun _ k => (Matrix.of fun _ _ => 1 :
      Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ))
    (ρ := fun _ => (toEuclideanLin (unfold (ι := fun _ : Fin 1 => Fin 1) (· ≠ (0 : Fin 1))
      (WithLp.toLp 2 fun _ => (3 : ℝ)))).singularValues (Fintype.card (Fin 1) - 1) / 2)
    (ν := fun _ => 0) (ν' := fun _ => 0) (g := fun _ => 0)
    (ε := fun _ => (toEuclideanLin (unfold (ι := fun _ : Fin 1 => Fin 1) (· ≠ (0 : Fin 1))
      (WithLp.toLp 2 fun _ => (3 : ℝ)))).singularValues (Fintype.card (Fin 1) - 1) / 8)
    le_rfl (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun _ _ k => by rw [tucker_const]; exact actOn_const k 3)
    (fun _ _ k => by rw [tucker_const]; exact coRange_const k three_ne_zero)
    (fun _ _ _ => by simp) (fun _ _ k => by rw [tucker_const]; exact actOn_const k _)
    (fun _ _ k => by rw [tucker_const]; exact coRange_const k (by positivity))
    (fun _ _ k => by
      obtain rfl : k = 0 := Subsingleton.elim _ _
      rw [tucker_const]
      linarith)
    (fun _ _ k => by
      obtain rfl : k = 0 := Subsingleton.elim _ _
      rw [tucker_const]
      have h := sub_abs_le_singularValues_unfold_const 0 3
        ((toEuclideanLin (unfold (ι := fun _ : Fin 1 => Fin 1) (· ≠ (0 : Fin 1))
          (WithLp.toLp 2 fun _ => (3 : ℝ)))).singularValues (Fintype.card (Fin 1) - 1) / 8)
      rw [abs_of_pos (by positivity)] at h
      linarith)
    continuousOn_const (fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) _)
    continuousOn_const continuousOn_const (fun t _ => hasDerivWithinAt_const t (Ici t) _)
    continuousOn_const continuousOn_const continuousOn_const continuousOn_const
    continuousOn_const (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp)
    (fun _ _ => by positivity) (fun _ _ => by linarith) (fun _ _ => hd.le) hd.le

end TuckerQuasiOptimalityNormalVelocityExamples

end Tensor

end LeanDLRA
