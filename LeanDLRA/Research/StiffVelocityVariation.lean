import LeanDLRA.Research.StiffOldColumnGalerkin

/-!
# Stiff problems: the variation of the velocities of the L-steps is not bounded by the data

`StiffOldColumnVariation` bounds the difference between the Galerkin result on the old columns
and the result of the L-step by `2 μ (t₁ - t₀)`, where `μ` bounds the change
`‖𝓛 (Y_L(t) - Y₀)‖` of the velocity of the L-step during the step. A bound for the global error
of the rank-adaptive BUG integrator that is proportional to the step size would follow if the sum
of the numbers `μₙ` over the steps were bounded by a constant times the velocity at the start
plus the variation of the forcing, with a constant that does not depend on the operator `𝓛`.

This file shows that there is no such constant. For every `K` and every step size `h > 0` it
gives `2 ^ K` steps of the integrator for a field `F(t, x) = 𝓛 x + c` with a symmetric negative
semidefinite `𝓛`, a constant forcing `c` and all normal parts and truncation errors equal to
zero, for which

`∑ₙ ‖𝓛 (Y_{L,n}(τₙ₊₁) - Yₙ)‖ ≥ (√K / 4) ‖𝓛 Y₀ + c‖`.

The operator has the `K` eigenvalues `-log 2 / (h 2 ^ k)`, the velocity at the start has the
same size on each eigenvector, and the steps are exact: the projectors fix the eigenvectors, so
that K-step, L-step and Galerkin step all follow the exact solution. With `N = 2 ^ K` steps the
factor is `√(log₂ N) / 4`, a square root of a logarithm of the number of steps; the eigenvalues
range over the factor `N / 2`.

## Main results

* `StiffVelocityVariation.hasDerivAt_dyadicTrajectory`,
  `StiffVelocityVariation.map_dyadicTrajectory_add`: the trajectory solves `x' = 𝓛 x + c`, with
  velocity `dyadicVelocity`.
* `StiffVelocityVariation.isRankAdaptiveBUGStep_dyadicTrajectory`: the trajectory on any time
  interval is a step of the rank-adaptive BUG integrator with `ε = 0` and `ϑ = 0`, for all
  commuting orthogonal projectors that fix the eigenvectors and the stationary point.
* `StiffVelocityVariation.sqrt_mul_norm_le_sum_norm_map_sub`: the lower bound displayed above.
* `StiffVelocityVariation.sqrt_mul_norm_le_sum_of_forall_norm_map_sub_le`: the same for every
  sequence `μₙ` of bounds for `‖𝓛 (Y_{L,n}(t) - Yₙ)‖` on the steps.

## Remarks

* The steps of this family have Galerkin results equal to the results of the L-steps, so the
  global error of the integrator is zero. The file shows that the sum of the velocity changes
  is the wrong quantity to bound, not that the error is large.
* For this family the square root of the logarithm is the true size: by the Cauchy–Schwarz
  inequality with the weights `n + 1`, the sum over `N` steps of the velocity changes of an
  exact solution with constant forcing is at most `√(1 + log N)` times the velocity at the
  start. This upper bound is not proved here.
* Nothing is shown here for steps whose augmented row space is not invariant under `𝓛`.

## Relation to the literature

The integrator is the one of [CerutiKuschLubich2022].
-/

open Set
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace StiffVelocityVariation

/-- The decay rate of the `k`-th mode: `exp (-(dyadicRate h k) t)` equals `1 / 2` at the time
`2 ^ k h` and `1 / 4` at the time `2 ^ (k + 1) h`. -/
noncomputable def dyadicRate (h : ℝ) (k : ℕ) : ℝ :=
  Real.log 2 / (h * 2 ^ k)

/-- The velocity `∑ₖ exp (-(dyadicRate h k) t) eₖ` of `dyadicTrajectory`, with `K` modes. -/
noncomputable def dyadicVelocity (e : ℕ → E) (h : ℝ) (K : ℕ) (t : ℝ) : E :=
  ∑ k ∈ Finset.range K, Real.exp (-(dyadicRate h k * t)) • e k

/-- The trajectory `x⋆ - ∑ₖ (dyadicRate h k)⁻¹ exp (-(dyadicRate h k) t) eₖ` with `K` modes. If
`𝓛 eₖ = -(dyadicRate h k) eₖ`, it solves `x' = 𝓛 x - 𝓛 x⋆`. -/
noncomputable def dyadicTrajectory (e : ℕ → E) (xs : E) (h : ℝ) (K : ℕ) (t : ℝ) : E :=
  xs - ∑ k ∈ Finset.range K, ((dyadicRate h k)⁻¹ * Real.exp (-(dyadicRate h k * t))) • e k

variable {e : ℕ → E} {xs c : E} {h : ℝ} {K : ℕ} {𝓛 P Q : E →L[ℝ] E}

/-- The decay rates are positive. -/
lemma dyadicRate_pos (hh : 0 < h) (k : ℕ) : 0 < dyadicRate h k :=
  div_pos (Real.log_pos one_lt_two) (mul_pos hh (pow_pos two_pos k))

/-- A sum over the dyadic blocks `[2 ^ k, 2 ^ (k + 1))`, `k < K`, of terms below a nonnegative
sequence is at most the sum of the sequence over `[0, 2 ^ K)`. -/
private lemma sum_dyadic_blocks_le {g : ℕ → ℕ → ℝ} {d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n) (K : ℕ)
    (hg : ∀ k < K, ∀ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), g k n ≤ d n) :
    ∑ k ∈ Finset.range K, ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), g k n
      ≤ ∑ n ∈ Finset.range (2 ^ K), d n := by
  induction K with
  | zero => simpa using hd 0
  | succ K ih =>
    have h1 := ih (fun k hk => hg k (hk.trans (Nat.lt_succ_self K)))
    have h2 : ∑ n ∈ Finset.Ico (2 ^ K) (2 ^ (K + 1)), g K n
        ≤ ∑ n ∈ Finset.Ico (2 ^ K) (2 ^ (K + 1)), d n :=
      Finset.sum_le_sum (hg K (Nat.lt_succ_self K))
    have h3 := Finset.sum_range_add_sum_Ico d
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_succ K))
    rw [Finset.sum_range_succ]
    linarith

/-- A telescoping sum over an interval of natural numbers. -/
private lemma sum_Ico_sub_succ (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (f n - f (n + 1)) = f a - f b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ico_succ_top hb, ih]
    ring

/-- The trajectory has the velocity `dyadicVelocity`. -/
theorem hasDerivAt_dyadicTrajectory (hh : 0 < h) (t : ℝ) :
    HasDerivAt (dyadicTrajectory e xs h K) (dyadicVelocity e h K t) t := by
  have hS : HasDerivAt (fun s => ∑ k ∈ Finset.range K,
      ((dyadicRate h k)⁻¹ * Real.exp (-(dyadicRate h k * s))) • e k)
      (-(dyadicVelocity e h K t)) t := by
    induction K with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, dyadicVelocity, neg_zero]
      exact hasDerivAt_const t (0 : E)
    | succ K ih =>
      have hr := inv_mul_cancel₀ (dyadicRate_pos hh K).ne'
      have h0 : HasDerivAt (fun s => -(dyadicRate h K * s)) (-(dyadicRate h K * 1)) t :=
        ((hasDerivAt_id t).const_mul (dyadicRate h K)).neg
      have h1 : HasDerivAt
          (fun s => ((dyadicRate h K)⁻¹ * Real.exp (-(dyadicRate h K * s))) • e K)
          (-(Real.exp (-(dyadicRate h K * t)) • e K)) t := by
        refine ((h0.exp.const_mul (dyadicRate h K)⁻¹).smul_const (e K)).congr_deriv ?_
        rw [← neg_smul]
        congr 1
        linear_combination (-Real.exp (-(dyadicRate h K * t))) * hr
      have key : (fun s => ∑ k ∈ Finset.range (K + 1),
            ((dyadicRate h k)⁻¹ * Real.exp (-(dyadicRate h k * s))) • e k)
          = fun s => (∑ k ∈ Finset.range K,
            ((dyadicRate h k)⁻¹ * Real.exp (-(dyadicRate h k * s))) • e k)
            + ((dyadicRate h K)⁻¹ * Real.exp (-(dyadicRate h K * s))) • e K := by
        funext s
        rw [Finset.sum_range_succ]
      have kv : dyadicVelocity e h (K + 1) t
          = dyadicVelocity e h K t + Real.exp (-(dyadicRate h K * t)) • e K :=
        Finset.sum_range_succ _ _
      rw [key, kv, neg_add]
      exact ih.add h1
  have h3 := (hasDerivAt_const t xs).sub hS
  rw [zero_sub, neg_neg] at h3
  exact h3

/-- Along the trajectory the field `𝓛 x + c` with `c = -𝓛 x⋆` is `dyadicVelocity`. -/
theorem map_dyadicTrajectory_add (hh : 0 < h)
    (h𝓛 : ∀ k < K, 𝓛 (e k) = -(dyadicRate h k) • e k) (hc : 𝓛 xs + c = 0) (t : ℝ) :
    𝓛 (dyadicTrajectory e xs h K t) + c = dyadicVelocity e h K t := by
  rw [eq_neg_of_add_eq_zero_right hc]
  simp only [dyadicTrajectory, dyadicVelocity, map_sub, map_sum, map_smul]
  rw [sub_add_eq_add_sub, add_neg_cancel, zero_sub, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hr := inv_mul_cancel₀ (dyadicRate_pos hh k).ne'
  rw [h𝓛 k (Finset.mem_range.1 hk), smul_smul, ← neg_smul]
  congr 1
  linear_combination Real.exp (-(dyadicRate h k * t)) * hr

/-- A continuous linear map that fixes the eigenvectors fixes the velocity. -/
private lemma map_dyadicVelocity (hPe : ∀ k < K, P (e k) = e k) (t : ℝ) :
    P (dyadicVelocity e h K t) = dyadicVelocity e h K t := by
  simp only [dyadicVelocity, map_sum, map_smul]
  exact Finset.sum_congr rfl fun k hk => by rw [hPe k (Finset.mem_range.1 hk)]

/-- A continuous linear map that fixes the eigenvectors and `x⋆` fixes the trajectory. -/
private lemma map_dyadicTrajectory (hPe : ∀ k < K, P (e k) = e k) (hPx : P xs = xs) (t : ℝ) :
    P (dyadicTrajectory e xs h K t) = dyadicTrajectory e xs h K t := by
  simp only [dyadicTrajectory, map_sub, map_sum, map_smul, hPx]
  congr 1
  exact Finset.sum_congr rfl fun k hk => by rw [hPe k (Finset.mem_range.1 hk)]

/-- **The trajectory is a sequence of exact steps of the rank-adaptive BUG integrator.** Let
`𝓛 eₖ = -(dyadicRate h k) eₖ` for `k < K`, `c = -𝓛 x⋆`, and let `P`, `Q` be commuting
orthogonal projectors that fix the vectors `eₖ` and `x⋆`. Then on every time interval the
trajectory is K-step, L-step and Galerkin step of a step of the integrator for the field
`𝓛 x + c`, with old and augmented projectors `P`, `Q`, with `ε = 0` and without truncation. -/
theorem isRankAdaptiveBUGStep_dyadicTrajectory (hh : 0 < h)
    (h𝓛 : ∀ k < K, 𝓛 (e k) = -(dyadicRate h k) • e k) (hc : 𝓛 xs + c = 0)
    (hP : IsOrthProj P) (hQ : IsOrthProj Q) (hPQ : ∀ x, P (Q x) = Q (P x))
    (hPe : ∀ k < K, P (e k) = e k) (hQe : ∀ k < K, Q (e k) = e k) (hPx : P xs = xs)
    (hQx : Q xs = xs) (t₀ t₁ : ℝ) :
    IsRankAdaptiveBUGStep (fun _ x => 𝓛 x + c) 0 0 P Q P Q t₀ t₁ (dyadicTrajectory e xs h K t₀)
      (dyadicTrajectory e xs h K) (dyadicTrajectory e xs h K) (dyadicTrajectory e xs h K)
      (dyadicTrajectory e xs h K t₁) := by
  have hF := map_dyadicTrajectory_add (xs := xs) hh h𝓛 hc
  have hPv := map_dyadicVelocity (h := h) hPe
  have hQv := map_dyadicVelocity (h := h) hQe
  have hPt := map_dyadicTrajectory (h := h) hPe hPx
  have hQt := map_dyadicTrajectory (h := h) hQe hQx
  have hcont : ContinuousOn (dyadicTrajectory e xs h K) (Icc t₀ t₁) :=
    (continuous_iff_continuousAt.2 fun t =>
      (hasDerivAt_dyadicTrajectory (e := e) (xs := xs) (K := K) hh t).continuousAt).continuousOn
  have hd : ∀ t, HasDerivWithinAt (dyadicTrajectory e xs h K) (dyadicVelocity e h K t)
      (Ici t) t := fun t => (hasDerivAt_dyadicTrajectory hh t).hasDerivWithinAt
  have hzQ : ∀ t, (1 - Q) (𝓛 (dyadicTrajectory e xs h K t) + c) = 0 := fun t => by
    rw [hF]
    simp [hQv]
  have hzP : ∀ t, (1 - P) (𝓛 (dyadicTrajectory e xs h K t) + c) = 0 := fun t => by
    rw [hF]
    simp [hPv]
  exact
    { projP₀ := hP
      projQ₀ := hQ
      projP₁ := hP
      projQ₁ := hQ
      comm₁ := hPQ
      kSol := ⟨hcont, fun t _ => by
        rw [hF, hQv]
        exact hd t⟩
      kStart := rfl
      kCap := hPt t₁
      kNormal := fun t _ => le_of_eq (by
        rw [hzQ, map_zero, norm_zero])
      lSol := ⟨hcont, fun t _ => by
        rw [hF, hPv]
        exact hd t⟩
      lStart := rfl
      lCap := hQt t₁
      lNormal := fun t _ => le_of_eq (by
        rw [hzP, map_zero, norm_zero])
      sSol := ⟨hcont, fun t _ => by
        rw [hF, hQv, hPv]
        exact hd t⟩
      sStart := by rw [hQt, hPt]
      augP := hPt t₀
      augQ := hQt t₀
      trunc := le_of_eq (by rw [sub_self, norm_zero]) }

/-- The component of the velocity along the `k`-th eigenvector. -/
private lemma inner_dyadicVelocity (he : ∀ j < K, ∀ k < K, ⟪e j, e k⟫ = if j = k then 1 else 0)
    {k : ℕ} (hk : k < K) (t : ℝ) :
    ⟪dyadicVelocity e h K t, e k⟫ = Real.exp (-(dyadicRate h k * t)) := by
  calc ⟪dyadicVelocity e h K t, e k⟫
      = ∑ j ∈ Finset.range K, Real.exp (-(dyadicRate h j * t)) * ⟪e j, e k⟫ := by
        simp only [dyadicVelocity, sum_inner, real_inner_smul_left]
    _ = ∑ j ∈ Finset.range K, if j = k then Real.exp (-(dyadicRate h j * t)) else 0 :=
        Finset.sum_congr rfl fun j hj => by
          rw [he j (Finset.mem_range.1 hj) k hk]
          split_ifs <;> simp
    _ = Real.exp (-(dyadicRate h k * t)) := by
        simp only [Finset.sum_ite_eq', Finset.mem_range, hk, ite_true]

/-- The velocity at time zero has norm `√K`. -/
theorem norm_dyadicVelocity_zero
    (he : ∀ j < K, ∀ k < K, ⟪e j, e k⟫ = if j = k then 1 else 0) :
    ‖dyadicVelocity e h K 0‖ = √K := by
  have h1 : ∀ w : E, ⟪w, dyadicVelocity e h K 0⟫ = ∑ k ∈ Finset.range K, ⟪w, e k⟫ := by
    intro w
    simp [dyadicVelocity, inner_sum]
  have h3 : ∀ k ∈ Finset.range K, ⟪dyadicVelocity e h K 0, e k⟫ = 1 := fun k hk => by
    rw [inner_dyadicVelocity he (Finset.mem_range.1 hk), mul_zero, neg_zero, Real.exp_zero]
  have h2 : ‖dyadicVelocity e h K 0‖ ^ 2 = (K : ℝ) := by
    rw [← real_inner_self_eq_norm_sq, h1, Finset.sum_congr rfl h3]
    simp
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

/-- **The velocity changes of the steps add up to `√K / 4` times the velocity at the start.**
Let `e₀, …, e_{K-1}` be orthonormal with `𝓛 eₖ = -(dyadicRate h k) eₖ` and `c = -𝓛 x⋆`. For the
`2 ^ K` steps of size `h` along `dyadicTrajectory`, which are steps of the rank-adaptive BUG
integrator with `ε = 0` and `ϑ = 0` (`isRankAdaptiveBUGStep_dyadicTrajectory`) with constant
forcing,

`(√K / 4) ‖𝓛 Y₀ + c‖ ≤ ∑ₙ ‖𝓛 (Y_{L,n}(τₙ₊₁) - Yₙ)‖`, `τₙ = n h`.

The left-hand side equals `K / 4`. -/
theorem sqrt_mul_norm_le_sum_norm_map_sub (hh : 0 < h)
    (he : ∀ j < K, ∀ k < K, ⟪e j, e k⟫ = if j = k then 1 else 0)
    (h𝓛 : ∀ k < K, 𝓛 (e k) = -(dyadicRate h k) • e k) (hc : 𝓛 xs + c = 0) :
    √K / 4 * ‖𝓛 (dyadicTrajectory e xs h K 0) + c‖
      ≤ ∑ n ∈ Finset.range (2 ^ K), ‖𝓛 (dyadicTrajectory e xs h K ((n + 1) * h)
        - dyadicTrajectory e xs h K (n * h))‖ := by
  have hF := map_dyadicTrajectory_add (xs := xs) hh h𝓛 hc
  -- the velocity change of a step
  have hstep : ∀ n : ℕ, 𝓛 (dyadicTrajectory e xs h K ((n + 1) * h)
      - dyadicTrajectory e xs h K (n * h))
      = dyadicVelocity e h K ((n + 1) * h) - dyadicVelocity e h K (n * h) := fun n => by
    rw [← hF, ← hF, map_sub]
    abel
  have hnorm : ∀ k < K, ‖e k‖ = 1 := fun k hk => by
    rw [norm_eq_sqrt_real_inner, he k hk k hk]
    simp
  -- every mode bounds the change from below
  have hg : ∀ k < K, ∀ n ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1)),
      Real.exp (-(dyadicRate h k * (n * h))) - Real.exp (-(dyadicRate h k * ((n + 1 : ℕ) * h)))
        ≤ ‖𝓛 (dyadicTrajectory e xs h K ((n + 1) * h)
          - dyadicTrajectory e xs h K (n * h))‖ := by
    intro k hk n _
    have h1 := real_inner_le_norm
      (dyadicVelocity e h K (n * h) - dyadicVelocity e h K ((n + 1) * h)) (e k)
    rw [inner_sub_left, inner_dyadicVelocity he hk, inner_dyadicVelocity he hk, hnorm k hk,
      mul_one, norm_sub_rev] at h1
    rw [hstep]
    push_cast
    exact h1
  -- the sum of the lower bounds over a dyadic block
  have hblock : ∀ k : ℕ, ∑ n ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1)),
      (Real.exp (-(dyadicRate h k * (n * h)))
        - Real.exp (-(dyadicRate h k * ((n + 1 : ℕ) * h)))) = 1 / 4 := by
    intro k
    have hne : h ≠ 0 := hh.ne'
    have e1 : dyadicRate h k * (((2 ^ k : ℕ) : ℝ) * h) = Real.log 2 := by
      unfold dyadicRate
      push_cast
      field_simp
    have e2 : dyadicRate h k * (((2 ^ (k + 1) : ℕ) : ℝ) * h) = Real.log 2 + Real.log 2 := by
      unfold dyadicRate
      push_cast
      field_simp
      ring
    have e3 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log two_pos, one_div]
    rw [sum_Ico_sub_succ (fun n : ℕ => Real.exp (-(dyadicRate h k * (n * h))))
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_succ k))]
    simp only [e1, e2, neg_add, Real.exp_add, e3]
    norm_num
  have hsum := sum_dyadic_blocks_le (d := fun n => ‖𝓛 (dyadicTrajectory e xs h K ((n + 1) * h)
    - dyadicTrajectory e xs h K (n * h))‖) (fun n => norm_nonneg _) K hg
  rw [Finset.sum_congr rfl fun k _ => hblock k, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  rw [hF, norm_dyadicVelocity_zero he]
  have hK : √(K : ℝ) * √(K : ℝ) = K := Real.mul_self_sqrt (Nat.cast_nonneg K)
  linarith

/-- **No bound for the sum of the velocity changes of the L-steps by the data.** In the
situation of `sqrt_mul_norm_le_sum_norm_map_sub`, let `μₙ` bound the change of the velocity of
the L-step on step `n`, `‖𝓛 (Y_{L,n}(t) - Yₙ)‖ ≤ μₙ` for `t` in the step; this is the hypothesis
of `IsRankAdaptiveBUGStep.norm_left_galerkin_sub_lstep_le`. Then

`(√K / 4) ‖𝓛 Y₀ + c‖ ≤ ∑ₙ μₙ`,

although the forcing is constant and all normal parts vanish. -/
theorem sqrt_mul_norm_le_sum_of_forall_norm_map_sub_le (hh : 0 < h)
    (he : ∀ j < K, ∀ k < K, ⟪e j, e k⟫ = if j = k then 1 else 0)
    (h𝓛 : ∀ k < K, 𝓛 (e k) = -(dyadicRate h k) • e k) (hc : 𝓛 xs + c = 0) {μ : ℕ → ℝ}
    (hμ : ∀ n : ℕ, n < 2 ^ K → ∀ t ∈ Icc ((n : ℝ) * h) ((n + 1) * h),
      ‖𝓛 (dyadicTrajectory e xs h K t - dyadicTrajectory e xs h K (n * h))‖ ≤ μ n) :
    √K / 4 * ‖𝓛 (dyadicTrajectory e xs h K 0) + c‖ ≤ ∑ n ∈ Finset.range (2 ^ K), μ n :=
  (sqrt_mul_norm_le_sum_norm_map_sub hh he h𝓛 hc).trans <|
    Finset.sum_le_sum fun n hn => hμ n (Finset.mem_range.1 hn) _
      ⟨mul_le_mul_of_nonneg_right (by linarith) hh.le, le_rfl⟩

/-- Non-vacuity of `isRankAdaptiveBUGStep_dyadicTrajectory`, `norm_dyadicVelocity_zero` and
`sqrt_mul_norm_le_sum_norm_map_sub` with two modes and four steps: on `ℂ` with the orthonormal
vectors `1` and `i`, the operator `𝓛 z = -a₀ (re z) - a₁ (im z) i` with `a₀ = log 2 / h` and
`a₁ = log 2 / (2 h)` is dissipative, the trajectory `x` from `0` consists of exact steps of the
integrator with identity projectors, the velocity at the start has norm `√2`, and the velocity
changes of the four steps add up to at least `(√2 / 4) √2 = 1 / 2`. -/
example {h : ℝ} (hh : 0 < h) :
    ∃ (𝓛 : ℂ →L[ℝ] ℂ) (x : ℝ → ℂ), (∀ z, ⟪𝓛 z, z⟫ ≤ 0) ∧
      (∀ n : ℕ, IsRankAdaptiveBUGStep (fun _ y => 𝓛 y + 0) 0 0 1 1 1 1 (n * h) ((n + 1) * h)
        (x (n * h)) x x x (x ((n + 1) * h))) ∧
      ‖𝓛 (x 0) + 0‖ = √(2 : ℕ) ∧
      √(2 : ℕ) / 4 * ‖𝓛 (x 0) + 0‖
        ≤ ∑ n ∈ Finset.range (2 ^ 2), ‖𝓛 (x ((n + 1) * h) - x (n * h))‖ := by
  obtain ⟨𝓛, h𝓛def⟩ : ∃ 𝓛 : ℂ →L[ℝ] ℂ, 𝓛 = -(dyadicRate h 0) • Complex.reCLM.smulRight (1 : ℂ)
      - dyadicRate h 1 • Complex.imCLM.smulRight Complex.I := ⟨_, rfl⟩
  obtain ⟨e, hedef⟩ : ∃ e : ℕ → ℂ, e = fun k => if k = 0 then 1 else Complex.I := ⟨_, rfl⟩
  have he : ∀ j < 2, ∀ k < 2, ⟪e j, e k⟫ = if j = k then 1 else 0 := by
    intro j hj k hk
    interval_cases j <;> interval_cases k <;> simp [hedef, Complex.inner]
  have h𝓛 : ∀ k < 2, 𝓛 (e k) = -(dyadicRate h k) • e k := by
    intro k hk
    interval_cases k <;> simp [hedef, h𝓛def]
  have hc : 𝓛 0 + 0 = 0 := by simp
  have hI : IsOrthProj (1 : ℂ →L[ℝ] ℂ) := ⟨fun _ => rfl, fun _ _ => rfl⟩
  have hdiss : ∀ z, ⟪𝓛 z, z⟫ ≤ 0 := by
    intro z
    have key : ⟪𝓛 z, z⟫ = -(dyadicRate h 0 * z.re ^ 2 + dyadicRate h 1 * z.im ^ 2) := by
      simp [h𝓛def, Complex.inner]
      ring
    rw [key]
    have h0 := mul_nonneg (dyadicRate_pos hh 0).le (sq_nonneg z.re)
    have h1 := mul_nonneg (dyadicRate_pos hh 1).le (sq_nonneg z.im)
    linarith
  exact ⟨𝓛, dyadicTrajectory e 0 h 2, hdiss,
    fun n => isRankAdaptiveBUGStep_dyadicTrajectory hh h𝓛 hc hI hI (fun _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl _ _,
    by rw [map_dyadicTrajectory_add hh h𝓛 hc, norm_dyadicVelocity_zero he],
    sqrt_mul_norm_le_sum_norm_map_sub hh he h𝓛 hc⟩

/-- Non-vacuity of `hasDerivAt_dyadicTrajectory` with nonzero data: on `ℂ` with the two modes
`1` and `i`, the stationary point `1` and the step size `h = 1`, the trajectory has the velocity
`dyadicVelocity` at every time. -/
example (t : ℝ) :
    HasDerivAt (dyadicTrajectory (fun k => Complex.I ^ k) 1 1 2)
      (dyadicVelocity (fun k => Complex.I ^ k) 1 2 t) t :=
  hasDerivAt_dyadicTrajectory one_pos t

/-- Non-vacuity of `sqrt_mul_norm_le_sum_of_forall_norm_map_sub_le` with nonzero data: in the
example of `sqrt_mul_norm_le_sum_norm_map_sub` (two modes on `ℂ`, four steps of size `h`) the
velocity has norm at most `2` at every time `t ≥ 0`, so `μₙ = 4` bounds the change of the
velocity on every step. The velocity at the start has norm `√2`, and the bound reads
`(√2 / 4) √2 ≤ 16`. -/
example {h : ℝ} (hh : 0 < h) :
    ∃ (𝓛 : ℂ →L[ℝ] ℂ) (x : ℝ → ℂ), (∀ z, ⟪𝓛 z, z⟫ ≤ 0) ∧ ‖𝓛 (x 0) + 0‖ = √(2 : ℕ) ∧
      (∀ n : ℕ, n < 2 ^ 2 → ∀ t ∈ Icc ((n : ℝ) * h) ((n + 1) * h),
        ‖𝓛 (x t - x (n * h))‖ ≤ 4) ∧
      √(2 : ℕ) / 4 * ‖𝓛 (x 0) + 0‖ ≤ ∑ _n ∈ Finset.range (2 ^ 2), (4 : ℝ) := by
  obtain ⟨𝓛, h𝓛def⟩ : ∃ 𝓛 : ℂ →L[ℝ] ℂ, 𝓛 = -(dyadicRate h 0) • Complex.reCLM.smulRight (1 : ℂ)
      - dyadicRate h 1 • Complex.imCLM.smulRight Complex.I := ⟨_, rfl⟩
  obtain ⟨e, hedef⟩ : ∃ e : ℕ → ℂ, e = fun k => if k = 0 then 1 else Complex.I := ⟨_, rfl⟩
  have he : ∀ j < 2, ∀ k < 2, ⟪e j, e k⟫ = if j = k then 1 else 0 := by
    intro j hj k hk
    interval_cases j <;> interval_cases k <;> simp [hedef, Complex.inner]
  have h𝓛 : ∀ k < 2, 𝓛 (e k) = -(dyadicRate h k) • e k := by
    intro k hk
    interval_cases k <;> simp [hedef, h𝓛def]
  have hc : 𝓛 0 + 0 = 0 := by simp
  have hdiss : ∀ z, ⟪𝓛 z, z⟫ ≤ 0 := by
    intro z
    have key : ⟪𝓛 z, z⟫ = -(dyadicRate h 0 * z.re ^ 2 + dyadicRate h 1 * z.im ^ 2) := by
      simp [h𝓛def, Complex.inner]
      ring
    rw [key]
    have h0 := mul_nonneg (dyadicRate_pos hh 0).le (sq_nonneg z.re)
    have h1 := mul_nonneg (dyadicRate_pos hh 1).le (sq_nonneg z.im)
    linarith
  have hF : ∀ t, 𝓛 (dyadicTrajectory e 0 h 2 t) = dyadicVelocity e h 2 t := fun t => by
    simpa using map_dyadicTrajectory_add hh h𝓛 hc t
  have hv : ∀ t : ℝ, 0 ≤ t → ‖dyadicVelocity e h 2 t‖ ≤ 2 := by
    intro t ht
    have hk : ∀ k ∈ Finset.range 2, ‖Real.exp (-(dyadicRate h k * t)) • e k‖ ≤ 1 := by
      intro k hk
      have he1 : ‖e k‖ = 1 := by
        have hk2 := Finset.mem_range.1 hk
        interval_cases k <;> simp [hedef]
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, he1, mul_one, Real.exp_le_one_iff]
      have := mul_nonneg (dyadicRate_pos hh k).le ht
      linarith
    calc ‖dyadicVelocity e h 2 t‖ ≤ ∑ k ∈ Finset.range 2, (1 : ℝ) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum hk)
      _ = 2 := by simp
  have hμ : ∀ n : ℕ, n < 2 ^ 2 → ∀ t ∈ Icc ((n : ℝ) * h) ((n + 1) * h),
      ‖𝓛 (dyadicTrajectory e 0 h 2 t - dyadicTrajectory e 0 h 2 (n * h))‖ ≤ 4 := by
    intro n _ t ht
    have h0 : 0 ≤ (n : ℝ) * h := mul_nonneg n.cast_nonneg hh.le
    rw [map_sub, hF, hF]
    calc _ ≤ ‖dyadicVelocity e h 2 t‖ + ‖dyadicVelocity e h 2 (n * h)‖ := norm_sub_le _ _
      _ ≤ 2 + 2 := add_le_add (hv t (h0.trans ht.1)) (hv _ h0)
      _ = 4 := by norm_num
  exact ⟨𝓛, dyadicTrajectory e 0 h 2, hdiss,
    by rw [map_dyadicTrajectory_add hh h𝓛 hc, norm_dyadicVelocity_zero he], hμ,
    sqrt_mul_norm_le_sum_of_forall_norm_map_sub_le hh he h𝓛 hc hμ⟩

end StiffVelocityVariation

end LeanDLRA
