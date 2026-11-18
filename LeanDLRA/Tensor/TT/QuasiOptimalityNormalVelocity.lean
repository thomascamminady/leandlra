import LeanDLRA.Tensor.TT.TangentNormal
import LeanDLRA.Tensor.Tucker.QuasiOptimalityNormalVelocity

/-!
# Quasi-optimality of tensor-train DLRA with the normal velocity as growth rate

For a solution `Y` of `Ẏ = P(Y) F(t, Y)` on the manifold of tensor trains with `d` modes and
fixed bond dimensions, and a curve `X` of such tensor trains, this file bounds the error by

  `‖Y t - X t‖ ≤ e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖X s - A s‖ + g s) ds`

in a tube `‖Y - X‖ ≤ ε < ρ/2`, where `ρ` is a lower bound of the singular values of the
unfoldings of `X` only, `ν ≥ ‖(1 - P(X)) F(t, A)‖`, `g ≥ ‖P(X) F(t, A) - Ẋ‖`, and the rate is

* `k = L + (ν + ν') / √(2 ρ (ρ - 2 ε))` with `ν' ≥ ‖(1 - P(Y)) F(t, A)‖`, or
* `k = L + (2 ν + 2 ε μ / ρ) / √(2 ρ (ρ - 2 ε))` with `μ ≥ ‖P(X) F(t, A)‖`: all data are taken
  at the curve `X`.

No constant depends on the number `d` of modes. To first order in `ε` the rate is `L + √2 ν/ρ`.

## Main results

* `LeanDLRA.Tensor.inner_sub_ttTangentProj_sub_le`: for tensor trains `X`, `Y` with
  `2 ‖Y - X‖ < ρ`,
  `⟪Y - X, P(Y) Z - P(X) Z⟫ ≤ (‖Z - P(Y) Z‖ + ‖Z - P(X) Z‖) ‖Y - X‖² / √(2 ρ (ρ - 2 ‖Y - X‖))`.
* `LeanDLRA.Tensor.norm_tt_sub_tt_le_integral_exp_integral`: the error bound with the first
  rate.
* `LeanDLRA.Tensor.norm_tt_sub_tt_le_integral_exp_integral_of_norm_ttTangentProj_le`: the error
  bound with the second rate.

## References

* [LubichOseledetsVandereycken2015]
-/

open Set Finset Matrix Filter
open scoped Topology RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA.Tensor

section Train

variable {d : ℕ} {ι : Fin d → Type*} [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
  {β : ℕ → Type*} [∀ k, Fintype (β k)] [∀ k, DecidableEq (β k)]

/-- **The tangent projectors at two tensor trains, tested with their difference.** Let
`X = tt AX = tt BX` and `Y = tt AY = tt BY` be tensor trains with `d ≥ 1` modes, left-orthogonal
cores `AX`, `AY` and right-orthogonal cores `BX`, `BY`, let `ρ` be a lower bound of the singular
values `σ_{|β k|}` of the unfoldings `X⟨k⟩`, `0 < k < d`, and `2 ‖Y - X‖ < ρ`. For every tensor
`Z`

  `⟪Y - X, P(Y) Z - P(X) Z⟫ ≤ (‖Z - P(Y) Z‖ + ‖Z - P(X) Z‖) ‖Y - X‖² / √(2 ρ (ρ - 2 ‖Y - X‖))`.

The right-hand side has the normal components of `Z` only, and no constant depends on `d`. -/
theorem inner_sub_ttTangentProj_sub_le [Unique (β 0)] [Unique (β d)]
    {AX BX AY BY : TTCores ι β} (hd : 0 < d) (hAX : ∀ i, IsLeftOrth AX i)
    (hBX : ∀ i, IsRightOrth BX i) (hABX : tt BX = tt AX) (hAY : ∀ i, IsLeftOrth AY i)
    (hBY : ∀ i, IsRightOrth BY i) (hABY : tt BY = tt AY) {ρ : ℝ}
    (hσ : ∀ k, 0 < k → k < d → ρ ≤ (toEuclideanLin (unfold (fun i : Fin d => i.val < k)
      (tt AX))).singularValues (Fintype.card (β k) - 1))
    (he : 2 * ‖tt AY - tt AX‖ < ρ) (Z : Tensor ι) :
    ⟪tt AY - tt AX, ttTangentProj AY BY Z - ttTangentProj AX BX Z⟫ ≤
      (‖Z - ttTangentProj AY BY Z‖ + ‖Z - ttTangentProj AX BX Z‖) *
        (‖tt AY - tt AX‖ ^ 2 / √(2 * ρ * (ρ - 2 * ‖tt AY - tt AX‖))) := by
  have hPX := isOrthProj_ttTangentProj hAX hBX
  have hPY := isOrthProj_ttTangentProj hAY hBY
  have hid := hPY.inner_sub_apply_sub_apply hPX (ttTangentProj_tt (B := BY) hd hAY)
    (ttTangentProj_tt (B := BX) hd hAX) Z
  have he' : 2 * ‖tt AX - tt AY‖ < ρ := by rwa [norm_sub_rev]
  have n1 := norm_sub_ttTangentProj_tt_le_of_le_singularValues_tt hd hAY hBY hABY hσ he'
  rw [norm_sub_rev (tt AX) (tt AY)] at n1
  have n2 := norm_sub_ttTangentProj_tt_le hd hAX hBX hABX hσ he
  rw [hid]
  calc ⟪tt AX - ttTangentProj AY BY (tt AX), Z - ttTangentProj AY BY Z⟫ +
        ⟪tt AY - ttTangentProj AX BX (tt AY), Z - ttTangentProj AX BX Z⟫
      ≤ ‖tt AX - ttTangentProj AY BY (tt AX)‖ * ‖Z - ttTangentProj AY BY Z‖ +
        ‖tt AY - ttTangentProj AX BX (tt AY)‖ * ‖Z - ttTangentProj AX BX Z‖ :=
        add_le_add (real_inner_le_norm _ _) (real_inner_le_norm _ _)
    _ ≤ ‖tt AY - tt AX‖ ^ 2 / √(2 * ρ * (ρ - 2 * ‖tt AY - tt AX‖)) *
          ‖Z - ttTangentProj AY BY Z‖ +
        ‖tt AY - tt AX‖ ^ 2 / √(2 * ρ * (ρ - 2 * ‖tt AY - tt AX‖)) *
          ‖Z - ttTangentProj AX BX Z‖ :=
        add_le_add (mul_le_mul_of_nonneg_right n1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right n2 (norm_nonneg _))
    _ = _ := by ring

/-- **The rate of the difference of the tangent projectors in a tube.** Under the hypotheses of
`inner_sub_ttTangentProj_sub_le`, if `‖Y - X‖ ≤ ε` with `2 ε < ρ`, `‖Z - P(X) Z‖ ≤ ν` and
`‖Z - P(Y) Z‖ ≤ ν'`, then
`⟪Y - X, P(Y) Z - P(X) Z⟫ ≤ (ν + ν') / √(2 ρ (ρ - 2 ε)) ‖Y - X‖²`. -/
theorem inner_sub_ttTangentProj_sub_le_div_sqrt_mul [Unique (β 0)] [Unique (β d)]
    {AX BX AY BY : TTCores ι β} (hd : 0 < d) (hAX : ∀ i, IsLeftOrth AX i)
    (hBX : ∀ i, IsRightOrth BX i) (hABX : tt BX = tt AX) (hAY : ∀ i, IsLeftOrth AY i)
    (hBY : ∀ i, IsRightOrth BY i) (hABY : tt BY = tt AY) {ρ ε ν ν' : ℝ}
    (hσ : ∀ k, 0 < k → k < d → ρ ≤ (toEuclideanLin (unfold (fun i : Fin d => i.val < k)
      (tt AX))).singularValues (Fintype.card (β k) - 1))
    (hε : 2 * ε < ρ) (he : ‖tt AY - tt AX‖ ≤ ε) {Z : Tensor ι}
    (hν : ‖Z - ttTangentProj AX BX Z‖ ≤ ν) (hν' : ‖Z - ttTangentProj AY BY Z‖ ≤ ν') :
    ⟪tt AY - tt AX, ttTangentProj AY BY Z - ttTangentProj AX BX Z⟫ ≤
      (ν + ν') / √(2 * ρ * (ρ - 2 * ε)) * ‖tt AY - tt AX‖ ^ 2 := by
  have he0 := norm_nonneg (tt AY - tt AX)
  have h := inner_sub_ttTangentProj_sub_le hd hAX hBX hABX hAY hBY hABY hσ
    (by linarith) Z
  refine h.trans ?_
  have hpos : 0 < 2 * ρ * (ρ - 2 * ε) := mul_pos (by linarith) (by linarith)
  have hs : √(2 * ρ * (ρ - 2 * ε)) ≤ √(2 * ρ * (ρ - 2 * ‖tt AY - tt AX‖)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
  have hn := norm_nonneg (Z - ttTangentProj AY BY Z)
  have hn' := norm_nonneg (Z - ttTangentProj AX BX Z)
  calc (‖Z - ttTangentProj AY BY Z‖ + ‖Z - ttTangentProj AX BX Z‖) *
        (‖tt AY - tt AX‖ ^ 2 / √(2 * ρ * (ρ - 2 * ‖tt AY - tt AX‖)))
      ≤ (ν + ν') * (‖tt AY - tt AX‖ ^ 2 / √(2 * ρ * (ρ - 2 * ε))) :=
        mul_le_mul (by linarith)
          (div_le_div_of_nonneg_left (sq_nonneg _) (Real.sqrt_pos.2 hpos) hs)
          (div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)) (by linarith)
    _ = (ν + ν') / √(2 * ρ * (ρ - 2 * ε)) * ‖tt AY - tt AX‖ ^ 2 := by ring

/-- **Quasi-optimality of tensor-train DLRA with the normal velocity as growth rate.** Let `F`
be `L`-Lipschitz, let `Y t = tt (AY t)` solve `Ẏ = P(Y) F(t, Y)` on `[a, b]` (right
derivatives), let `A` be a continuous curve and `X t = tt (AX t)` a continuous curve of tensor
trains with right derivatives `X'`, with left-orthogonal cores `AX t`, `AY t` and right-orthogonal
cores `BX t`, `BY t` of the same tensors at every time, `d ≥ 1` modes. Let `ρ`, `ν`, `ν'`, `g`,
`ε` be continuous on `[a, b]`, `ρ t` a lower bound of the singular values `σ_{|β k|}` of the
unfoldings of `X t`, `‖(1 - P(X t)) F(t, A t)‖ ≤ ν t`, `‖(1 - P(Y t)) F(t, A t)‖ ≤ ν' t`,
`‖P(X t) F(t, A t) - X' t‖ ≤ g t`, `0 ≤ 2 ε t < ρ t` and `‖Y t - X t‖ ≤ ε t`. If
`‖Y a - X a‖ ≤ δ`, then with `k = L + (ν + ν') / √(2 ρ (ρ - 2 ε))`, for `t ∈ [a, b]`

  `‖Y t - X t‖ ≤ e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖X s - A s‖ + g s) ds`.

No constant depends on the number `d` of modes. -/
theorem norm_tt_sub_tt_le_integral_exp_integral [Unique (β 0)] [Unique (β d)]
    {F : ℝ → Tensor ι → Tensor ι} {A X' : ℝ → Tensor ι} {AX BX AY BY : ℝ → TTCores ι β}
    {ρ ν ν' g ε : ℝ → ℝ} {a b L δ : ℝ} (hd : 0 < d) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hAX : ∀ t ∈ Icc a b, ∀ i, IsLeftOrth (AX t) i)
    (hBX : ∀ t ∈ Icc a b, ∀ i, IsRightOrth (BX t) i)
    (hABX : ∀ t ∈ Icc a b, tt (BX t) = tt (AX t))
    (hAY : ∀ t ∈ Icc a b, ∀ i, IsLeftOrth (AY t) i)
    (hBY : ∀ t ∈ Icc a b, ∀ i, IsRightOrth (BY t) i)
    (hABY : ∀ t ∈ Icc a b, tt (BY t) = tt (AY t))
    (hσX : ∀ t ∈ Icc a b, ∀ k, 0 < k → k < d → ρ t ≤ (toEuclideanLin
      (unfold (fun i : Fin d => i.val < k) (tt (AX t)))).singularValues
        (Fintype.card (β k) - 1))
    (hYc : ContinuousOn (fun t => tt (AY t)) (Icc a b))
    (hY : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => tt (AY t))
      (ttTangentProj (AY t) (BY t) (F t (tt (AY t)))) (Ici t) t)
    (hAc : ContinuousOn A (Icc a b)) (hXc : ContinuousOn (fun t => tt (AX t)) (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => tt (AX t)) (X' t) (Ici t) t)
    (hρc : ContinuousOn ρ (Icc a b)) (hνc : ContinuousOn ν (Icc a b))
    (hν'c : ContinuousOn ν' (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hεc : ContinuousOn ε (Icc a b))
    (hν : ∀ t ∈ Ico a b, ‖F t (A t) - ttTangentProj (AX t) (BX t) (F t (A t))‖ ≤ ν t)
    (hν' : ∀ t ∈ Ico a b, ‖F t (A t) - ttTangentProj (AY t) (BY t) (F t (A t))‖ ≤ ν' t)
    (hg : ∀ t ∈ Ico a b, ‖ttTangentProj (AX t) (BX t) (F t (A t)) - X' t‖ ≤ g t)
    (hε0 : ∀ t ∈ Icc a b, 0 ≤ ε t) (hερ : ∀ t ∈ Icc a b, 2 * ε t < ρ t)
    (htube : ∀ t ∈ Ico a b, ‖tt (AY t) - tt (AX t)‖ ≤ ε t)
    (hδ : ‖tt (AY a) - tt (AX a)‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖tt (AY t) - tt (AX t)‖ ≤
      Real.exp (∫ u in a..t, (L + (ν u + ν' u) / √(2 * ρ u * (ρ u - 2 * ε u)))) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t, (L + (ν u + ν' u) / √(2 * ρ u * (ρ u - 2 * ε u)))) *
          (L * ‖tt (AX s) - A s‖ + g s) := by
  have hpos : ∀ t ∈ Icc a b, 0 < 2 * ρ t * (ρ t - 2 * ε t) := fun t ht =>
    mul_pos (by linarith [hε0 t ht, hερ t ht]) (by linarith [hερ t ht])
  have hsc : ContinuousOn (fun t => √(2 * ρ t * (ρ t - 2 * ε t))) (Icc a b) :=
    Real.continuous_sqrt.comp_continuousOn
      ((continuousOn_const.mul hρc).mul (hρc.sub (continuousOn_const.mul hεc)))
  refine norm_sub_le_integral_exp_integral_of_inner_apply_sub_apply_le
    (PY := fun t => ttTangentProj (AY t) (BY t)) (PX := fun t => ttTangentProj (AX t) (BX t))
    (κ := fun t => (ν t + ν' t) / √(2 * ρ t * (ρ t - 2 * ε t))) hL hF
    (fun t ht => isOrthProj_ttTangentProj (hAY t (Ico_subset_Icc_self ht))
      (hBY t (Ico_subset_Icc_self ht)))
    hYc hY hAc hXc hX ?_ hgc (fun t ht => ?_) hg hδ
  · exact (hνc.add hν'c).div hsc fun t ht => (Real.sqrt_pos.2 (hpos t ht)).ne'
  · have hI := Ico_subset_Icc_self ht
    exact inner_sub_ttTangentProj_sub_le_div_sqrt_mul hd (hAX t hI) (hBX t hI) (hABX t hI)
      (hAY t hI) (hBY t hI) (hABY t hI) (hσX t hI) (hερ t hI) (htube t ht) (hν t ht) (hν' t ht)

/-- **Quasi-optimality of tensor-train DLRA, with data at the reference curve only.** Let `F`
be `L`-Lipschitz, let `Y t = tt (AY t)` solve `Ẏ = P(Y) F(t, Y)` on `[a, b]` (right
derivatives), let `A` be a continuous curve and `X t = tt (AX t)` a continuous curve of tensor
trains with right derivatives `X'`, with left-orthogonal cores `AX t`, `AY t` and right-orthogonal
cores `BX t`, `BY t` of the same tensors at every time, `d ≥ 1` modes. Let `ρ`, `ν`, `μ`, `g`,
`ε` be continuous on `[a, b]`, `ρ t` a lower bound of the singular values `σ_{|β k|}` of the
unfoldings of `X t`, `‖(1 - P(X t)) F(t, A t)‖ ≤ ν t`, `‖P(X t) F(t, A t)‖ ≤ μ t`,
`‖P(X t) F(t, A t) - X' t‖ ≤ g t`, `0 ≤ 2 ε t < ρ t` and `‖Y t - X t‖ ≤ ε t`. If
`‖Y a - X a‖ ≤ δ`, then with `k = L + (2 ν + 2 ε μ / ρ) / √(2 ρ (ρ - 2 ε))`, for `t ∈ [a, b]`

  `‖Y t - X t‖ ≤ e^{∫ₐᵗ k} δ + ∫ₐᵗ e^{∫ₛᵗ k} (L ‖X s - A s‖ + g s) ds`.

The normal velocity `ν`, the tangential velocity `μ` and the singular values `ρ` are taken at
`X`; the solution `Y` enters through the tube `ε` only, and no constant depends on the number
`d` of modes. -/
theorem norm_tt_sub_tt_le_integral_exp_integral_of_norm_ttTangentProj_le [Unique (β 0)]
    [Unique (β d)]
    {F : ℝ → Tensor ι → Tensor ι} {A X' : ℝ → Tensor ι} {AX BX AY BY : ℝ → TTCores ι β}
    {ρ ν μ g ε : ℝ → ℝ} {a b L δ : ℝ} (hd : 0 < d) (hL : 0 ≤ L) (hF : IsLipschitzField F L)
    (hAX : ∀ t ∈ Icc a b, ∀ i, IsLeftOrth (AX t) i)
    (hBX : ∀ t ∈ Icc a b, ∀ i, IsRightOrth (BX t) i)
    (hABX : ∀ t ∈ Icc a b, tt (BX t) = tt (AX t))
    (hAY : ∀ t ∈ Icc a b, ∀ i, IsLeftOrth (AY t) i)
    (hBY : ∀ t ∈ Icc a b, ∀ i, IsRightOrth (BY t) i)
    (hABY : ∀ t ∈ Icc a b, tt (BY t) = tt (AY t))
    (hσX : ∀ t ∈ Icc a b, ∀ k, 0 < k → k < d → ρ t ≤ (toEuclideanLin
      (unfold (fun i : Fin d => i.val < k) (tt (AX t)))).singularValues
        (Fintype.card (β k) - 1))
    (hYc : ContinuousOn (fun t => tt (AY t)) (Icc a b))
    (hY : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => tt (AY t))
      (ttTangentProj (AY t) (BY t) (F t (tt (AY t)))) (Ici t) t)
    (hAc : ContinuousOn A (Icc a b)) (hXc : ContinuousOn (fun t => tt (AX t)) (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => tt (AX t)) (X' t) (Ici t) t)
    (hρc : ContinuousOn ρ (Icc a b)) (hνc : ContinuousOn ν (Icc a b))
    (hμc : ContinuousOn μ (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hεc : ContinuousOn ε (Icc a b))
    (hν : ∀ t ∈ Ico a b, ‖F t (A t) - ttTangentProj (AX t) (BX t) (F t (A t))‖ ≤ ν t)
    (hμ : ∀ t ∈ Ico a b, ‖ttTangentProj (AX t) (BX t) (F t (A t))‖ ≤ μ t)
    (hg : ∀ t ∈ Ico a b, ‖ttTangentProj (AX t) (BX t) (F t (A t)) - X' t‖ ≤ g t)
    (hε0 : ∀ t ∈ Icc a b, 0 ≤ ε t) (hερ : ∀ t ∈ Icc a b, 2 * ε t < ρ t)
    (htube : ∀ t ∈ Ico a b, ‖tt (AY t) - tt (AX t)‖ ≤ ε t)
    (hδ : ‖tt (AY a) - tt (AX a)‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖tt (AY t) - tt (AX t)‖ ≤
      Real.exp (∫ u in a..t,
          (L + (2 * ν u + 2 * ε u * μ u / ρ u) / √(2 * ρ u * (ρ u - 2 * ε u)))) * δ +
        ∫ s in a..t, Real.exp (∫ u in s..t,
            (L + (2 * ν u + 2 * ε u * μ u / ρ u) / √(2 * ρ u * (ρ u - 2 * ε u)))) *
          (L * ‖tt (AX s) - A s‖ + g s) := by
  have hpos : ∀ t ∈ Icc a b, 0 < 2 * ρ t * (ρ t - 2 * ε t) := fun t ht =>
    mul_pos (by linarith [hε0 t ht, hερ t ht]) (by linarith [hερ t ht])
  have hsc : ContinuousOn (fun t => √(2 * ρ t * (ρ t - 2 * ε t))) (Icc a b) :=
    Real.continuous_sqrt.comp_continuousOn
      ((continuousOn_const.mul hρc).mul (hρc.sub (continuousOn_const.mul hεc)))
  refine norm_sub_le_integral_exp_integral_of_inner_apply_sub_apply_le
    (PY := fun t => ttTangentProj (AY t) (BY t)) (PX := fun t => ttTangentProj (AX t) (BX t))
    (κ := fun t => (2 * ν t + 2 * ε t * μ t / ρ t) / √(2 * ρ t * (ρ t - 2 * ε t))) hL hF
    (fun t ht => isOrthProj_ttTangentProj (hAY t (Ico_subset_Icc_self ht))
      (hBY t (Ico_subset_Icc_self ht)))
    hYc hY hAc hXc hX ?_ hgc (fun t ht => ?_) hg hδ
  · have hρ0 : ∀ t ∈ Icc a b, ρ t ≠ 0 := fun t ht => by linarith [hε0 t ht, hερ t ht]
    exact ((continuousOn_const.mul hνc).add
      (((continuousOn_const.mul hεc).mul hμc).div hρc hρ0)).div hsc
      fun t ht => (Real.sqrt_pos.2 (hpos t ht)).ne'
  · have hI := Ico_subset_Icc_self ht
    have hρ0 : 0 < ρ t := by linarith [hε0 t hI, hερ t hI]
    have hμ0 : 0 ≤ μ t := (norm_nonneg _).trans (hμ t ht)
    have h1 := norm_sub_ttTangentProj_apply_le_add hd (hAY t hI) (hBY t hI) (hABY t hI)
      (hAX t hI) (hBX t hI) (hABX t hI) hρ0 (hσX t hI) (F t (A t))
    rw [norm_sub_rev (tt (AX t)) (tt (AY t))] at h1
    have h2 : 2 * (ρ t)⁻¹ * ‖tt (AY t) - tt (AX t)‖ *
        ‖ttTangentProj (AX t) (BX t) (F t (A t))‖ ≤ 2 * ε t * μ t / ρ t := by
      rw [show 2 * ε t * μ t / ρ t = 2 * (ρ t)⁻¹ * ε t * μ t by field_simp]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (htube t ht) (by positivity)) (hμ t ht)
        (norm_nonneg _) (mul_nonneg (by positivity) (hε0 t hI))
    refine (inner_sub_ttTangentProj_sub_le_div_sqrt_mul (ν' := ν t + 2 * ε t * μ t / ρ t) hd
      (hAX t hI) (hBX t hI) (hABX t hI) (hAY t hI) (hBY t hI) (hABY t hI) (hσX t hI)
      (hερ t hI) (htube t ht) (hν t ht) (by linarith [hν t ht])).trans_eq ?_
    ring

end Train

/-! ### Examples -/

namespace TTQuasiOptimalityNormalVelocityExamples

open TTNormalSecondOrderTrainExamples

/-- Non-vacuity of `inner_sub_ttTangentProj_sub_le` with three modes of dimension two:
`X = e₁ ⊗ e₁ ⊗ e₁`, `Y = v ⊗ v ⊗ v` with `v = (40/41, 9/41)` and `ρ = 1`. All hypotheses hold and
`X ≠ Y`. -/
example (Z : Tensor fun _ : Fin 3 => Fin 2) : tt nearCores ≠ tt baseCores ∧
    ⟪tt nearCores - tt baseCores,
        ttTangentProj nearCores nearCores Z - ttTangentProj baseCores baseCores Z⟫ ≤
      (‖Z - ttTangentProj nearCores nearCores Z‖ + ‖Z - ttTangentProj baseCores baseCores Z‖) *
        (‖tt nearCores - tt baseCores‖ ^ 2 /
          √(2 * 1 * (1 - 2 * ‖tt nearCores - tt baseCores‖))) :=
  by
  refine ⟨tt_nearCores_ne_tt_baseCores,
    inner_sub_ttTangentProj_sub_le (AX := baseCores) (BX := baseCores) (AY := nearCores)
      (BY := nearCores) (ρ := 1) (by norm_num) isLeftOrth_baseCores isRightOrth_baseCores rfl
      isLeftOrth_nearCores isRightOrth_nearCores rfl ?_
      (by linarith [norm_tt_nearCores_sub_tt_baseCores_pos_lt.2]) Z⟩
  exact one_le_singularValues_unfold_tt_baseCores

/-- Non-vacuity of `norm_tt_sub_tt_le_integral_exp_integral` (and of
`inner_sub_ttTangentProj_sub_le_div_sqrt_mul`) with three modes of dimension two and `X ≠ Y`:
the constant curves `X = e₁ ⊗ e₁ ⊗ e₁` and `Y = v ⊗ v ⊗ v`, `v = (40/41, 9/41)`, the field
`F = 0`, `ρ = 1`, `ν = ν' = 1`, `g = L = 0` and `ε = δ = 2/5` on `[0, 1]`. All hypotheses hold;
the rate is positive (the field of this example has no normal velocity, `ν` is an upper
bound). -/
example : ∀ t ∈ Icc (0 : ℝ) 1, ‖tt nearCores - tt baseCores‖ ≤
    Real.exp (∫ _ in (0 : ℝ)..t,
        ((0 : ℝ) + (1 + 1) / √(2 * 1 * (1 - 2 * (2 / 5))))) * (2 / 5) +
      ∫ u in (0 : ℝ)..t,
        Real.exp (∫ _ in u..t, ((0 : ℝ) + (1 + 1) / √(2 * 1 * (1 - 2 * (2 / 5))))) *
          (0 * ‖tt baseCores - 0‖ + 0) := by
  refine norm_tt_sub_tt_le_integral_exp_integral
    (F := fun _ _ => (0 : Tensor fun _ : Fin 3 => Fin 2)) (A := fun _ => 0) (X' := fun _ => 0)
    (AX := fun _ => baseCores) (BX := fun _ => baseCores) (AY := fun _ => nearCores)
    (BY := fun _ => nearCores) (ρ := fun _ => 1) (ν := fun _ => 1) (ν' := fun _ => 1)
    (g := fun _ => 0) (ε := fun _ => 2 / 5) (by norm_num) le_rfl (fun _ _ _ => by simp)
    (fun _ _ => isLeftOrth_baseCores) (fun _ _ => isRightOrth_baseCores) (fun _ _ => rfl)
    (fun _ _ => isLeftOrth_nearCores) (fun _ _ => isRightOrth_nearCores) (fun _ _ => rfl)
    ?_ continuousOn_const
    (fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) _) continuousOn_const
    continuousOn_const (fun t _ => hasDerivWithinAt_const t (Ici t) _) continuousOn_const
    continuousOn_const continuousOn_const continuousOn_const continuousOn_const
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by norm_num)
    (fun _ _ => by norm_num) (fun _ _ => norm_tt_nearCores_sub_tt_baseCores_pos_lt.2.le)
    norm_tt_nearCores_sub_tt_baseCores_pos_lt.2.le
  exact fun _ _ => one_le_singularValues_unfold_tt_baseCores

/-- Non-vacuity of `norm_tt_sub_tt_le_integral_exp_integral_of_norm_ttTangentProj_le` for the
same curves, with `μ = 1`. -/
example : ∀ t ∈ Icc (0 : ℝ) 1, ‖tt nearCores - tt baseCores‖ ≤
    Real.exp (∫ _ in (0 : ℝ)..t,
        ((0 : ℝ) + (2 * 1 + 2 * (2 / 5) * 1 / 1) / √(2 * 1 * (1 - 2 * (2 / 5))))) * (2 / 5) +
      ∫ u in (0 : ℝ)..t,
        Real.exp (∫ _ in u..t,
            ((0 : ℝ) + (2 * 1 + 2 * (2 / 5) * 1 / 1) / √(2 * 1 * (1 - 2 * (2 / 5))))) *
          (0 * ‖tt baseCores - 0‖ + 0) := by
  refine norm_tt_sub_tt_le_integral_exp_integral_of_norm_ttTangentProj_le
    (F := fun _ _ => (0 : Tensor fun _ : Fin 3 => Fin 2)) (A := fun _ => 0) (X' := fun _ => 0)
    (AX := fun _ => baseCores) (BX := fun _ => baseCores) (AY := fun _ => nearCores)
    (BY := fun _ => nearCores) (ρ := fun _ => 1) (ν := fun _ => 1) (μ := fun _ => 1)
    (g := fun _ => 0) (ε := fun _ => 2 / 5) (by norm_num) le_rfl (fun _ _ _ => by simp)
    (fun _ _ => isLeftOrth_baseCores) (fun _ _ => isRightOrth_baseCores) (fun _ _ => rfl)
    (fun _ _ => isLeftOrth_nearCores) (fun _ _ => isRightOrth_nearCores) (fun _ _ => rfl)
    ?_ continuousOn_const
    (fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) _) continuousOn_const
    continuousOn_const (fun t _ => hasDerivWithinAt_const t (Ici t) _) continuousOn_const
    continuousOn_const continuousOn_const continuousOn_const continuousOn_const
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by norm_num)
    (fun _ _ => by norm_num) (fun _ _ => norm_tt_nearCores_sub_tt_baseCores_pos_lt.2.le)
    norm_tt_nearCores_sub_tt_baseCores_pos_lt.2.le
  exact fun _ _ => one_le_singularValues_unfold_tt_baseCores

end TTQuasiOptimalityNormalVelocityExamples

end LeanDLRA.Tensor
