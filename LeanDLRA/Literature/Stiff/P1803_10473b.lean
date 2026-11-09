import LeanDLRA.Literature.Stiff.P1803_10473a

/-!
# Results of arXiv 1803.10473, part b: the full-rank splitting error and Theorem 1

Ostermann, Piazzola, Walach, *Convergence of a low-rank Lie–Trotter splitting for stiff matrix
differential equations* (arXiv 1803.10473), Proposition 1 and Theorem 1, for
`Ẋ = 𝒜 X + G(t, X)` with a bounded linear operator `𝒜` on a real inner product space `E`
(finite-dimensional setting: every linear operator on `ℝ^{m×m}` is bounded) and the stiff flow
`e^{t𝒜}` (`NormedSpace.exp (t • 𝒜)`). The paper's case is `𝒜 Z = A Z + Z A*` on matrices with the
Frobenius norm, where `e^{t𝒜} Z = e^{tA} Z e^{tA*}` (`exp_lyapunov_apply`). Lemma 1 and
Proposition 2 are in `LeanDLRA.Literature.Stiff.P1803_10473a`.

Assumption 1(a) is used as printed, for `t > 0` and all `Z`:
(10) `‖e^{t𝒜} Z‖ ≤ e^{tω} ‖Z‖` and (11) `‖e^{t𝒜} (𝒜 Z)‖ ≤ (C_s / t) e^{tω} ‖Z‖`.

## Main results

* `fullRank_lieTrotter_error` (**Proposition 1**): the full-rank Lie–Trotter splitting
  `Zₖ₊₁ = e^{τ𝒜} Φ^G_τ(Zₖ)`, `Z₀ = X(t₀)`, satisfies `‖X(t₀ + n τ) - Zₙ‖ ≤ C τ (1 + |log τ|)` for
  `n τ ≤ T`, with an explicit `C` depending on `ω`, `C_s`, `L`, `B`, `T` and the two regularity
  constants `L_t`, `K_x` below.
* `lowRank_lieTrotter_global_error` (**Theorem 1**): the low-rank Lie–Trotter splitting
  `Yₖ₊₁ = e^{τ𝒜} Φ̃^G_τ(Yₖ)` (one step of the projector-splitting integrator, core
  `IsKSLStep`) satisfies `‖X(t₀ + n τ) - Yₙ‖ ≤ c₀ τ (1 + |log τ|) + c₁ δ + c₂ ε` for `n τ ≤ T`,
  with `‖X(t₀) - Y₀‖ ≤ δ`. Proof: Proposition 1 plugged into
  `lowRank_lieTrotter_error_of_fullRank` (part a: Proposition 2 and the propagation of `δ`).
* `exp_lyapunov_apply`: for `𝒜 Z = A Z + Z Aᵀ`, `e^{t𝒜} Z = e^{tA} Z (e^{tA})ᵀ`
  (`sylvesterFlow A A t Z`), for `t ≥ 0`; `fullRank_lieTrotter_error_matrix` and
  `lowRank_lieTrotter_global_error_matrix` are the two results in the paper's matrix form, with
  (10), (11) and the scheme written with `e^{tA} Z e^{tAᵀ}`.
* `sylvesterFlow_smoothing_of_negSemidef`: (11) holds with `ω = 0`, `C_s = e⁻¹` for every
  symmetric negative semidefinite `A` (discrete Laplacians), from
  `sylvester_dissipative_smoothing`; with `sylvesterFlow_bound_of_negSemidef` (part a) this
  verifies Assumption 1(a) for the paper's parabolic examples, with grid-independent constants.

## Proof of Proposition 1

The paper expands the local error to second order (eq. (16)) and solves the error recursion
first (eq. (18)). We follow the same structure without integrals. For the local error
`eₖ = X(tₖ₊₁) - e^{τ𝒜} Φ^G_τ(X(tₖ))` propagated by `e^{jτ𝒜}`, the function
`w(t) = e^{(tₖ₊₁ + jτ - t)𝒜} X(t) - e^{(j+1)τ𝒜} W(t)` (`W` the `G`-flow from `X(tₖ)`) has
`w(tₖ) = 0`, `w(tₖ₊₁) = e^{jτ𝒜} eₖ` and derivative
`e^{(c-t)𝒜} G(t, X(t)) - e^{(j+1)τ𝒜} G(t, W(t))`; splitting it as in (16) gives
`‖e^{jτ𝒜} eₖ‖ ≤ M τ² (K_x + L_t + L B) + τ D_j` with `M = e^{ω⁺ T}`, `D_0 = 2 M B` and, by the
smoothing bound (11), `D_j = C_s M B / j` for `j ≥ 1` (`norm_exp_localError_le`). The error
recursion `Eₖ₊₁ = eₖ + e^{τ𝒜}(Eₖ + Hₖ)` with `‖Hₖ‖ ≤ L e^{Lτ} τ ‖Eₖ‖` is solved exactly,
`Eₙ = ∑ₖ (e^{(n-1-k)τ𝒜} eₖ + e^{(n-k)τ𝒜} Hₖ)` (eq. (18)); the harmonic sum `∑_{j<n} 1/j ≤
1 + log n` (eq. (20)) and a discrete Grönwall inequality (sum form) finish the proof.

## Deviations from the paper

* A real inner product space `E` and a bounded generator `𝒜` (the finite-dimensional case,
  which covers `ℝ^{m×m}` with the Frobenius norm) instead of `ℂ^{m×m}`.
* **Global constants and regularity made explicit.** Assumption 1(b) (`G` is `C¹` near the exact
  solution) is replaced by: `G` is `L`-Lipschitz in `X` and bounded by `B` globally (as in part a),
  and `L_t`-Lipschitz in `t` (`‖G(s, X) - G(t, X)‖ ≤ L_t |s - t|`), which is how the boundedness
  of `Ẍ₂ = ∂_t G + ∂_X G · G` in the proof of Proposition 1 is used. The proof also uses that
  `dG/ds = d/ds G(s, X(s))` is bounded along the exact solution (the step before (16)); this
  depends on `Ẋ = 𝒜X + G` and hence on the solution, not only on `ω, C_s, L, B, T`, and the paper
  does not list it among the constants. We assume it explicitly:
  `‖G(s, X(s)) - G(t, X(t))‖ ≤ K_x |s - t|` on `[t₀, t₀ + N τ]`.
* All `τ > 0` are allowed (no `τ₀`), since the constants are global; constants are explicit.
* The normal-component bound (Assumption 1(c)) enters through `IsKSLStep.kNormal`, see part a.
* The exact `G`-flows of the scheme from its own iterates are hypotheses (`ODESolution`); the
  auxiliary flows of the proofs are constructed with `exists_ODESolution`.

Core definitions used: `ODESolution`, `IsLipschitzField`, `IsBoundedField`, `IsKSLStep`,
`Frobenius.leftMulCLM`, `Frobenius.rightMulCLM`, `sylvesterFlow`. No new public definitions;
`expT` is a private proof helper (the matrix exponential with Mathlib's topology).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P1803_10473

open LeanDLRA LeanDLRA.OpenProblems.Stiff

/-! ### The stiff semigroup `e^{t𝒜}` -/

section Semigroup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Semigroup property `e^{(a+b)𝒜} z = e^{a𝒜} (e^{b𝒜} z)` of the stiff flow. -/
theorem exp_smul_add_apply (𝒜 : E →L[ℝ] E) (a b : ℝ) (z : E) :
    NormedSpace.exp ((a + b) • 𝒜) z = NormedSpace.exp (a • 𝒜) (NormedSpace.exp (b • 𝒜) z) := by
  let : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ _
  rw [add_smul, NormedSpace.exp_add_of_commute (((Commute.refl 𝒜).smul_left a).smul_right b)]
  rfl

/-- The stiff flow solves `ż = 𝒜 z`: `t ↦ e^{t𝒜} z` has derivative `e^{t𝒜} (𝒜 z)`. -/
theorem hasDerivAt_exp_smul_apply (𝒜 : E →L[ℝ] E) (z : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • 𝒜) z) (NormedSpace.exp (t • 𝒜) (𝒜 z)) t := by
  have h := (hasDerivAt_exp_smul_const 𝒜 t).clm_apply (hasDerivAt_const t z)
  simpa using h

/-- Derivative of the operator-valued map `s ↦ e^{(c-s)𝒜}`. -/
private theorem hasDerivAt_exp_sub_smul (𝒜 : E →L[ℝ] E) (c s : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((c - s) • 𝒜))
      (-(NormedSpace.exp ((c - s) • 𝒜) * 𝒜)) s := by
  have h1 : HasDerivAt (fun s : ℝ => c - s) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub c
  have h2 := (hasDerivAt_exp_smul_const 𝒜 (c - s)).scomp s h1
  exact h2.congr_deriv (neg_one_smul ℝ _)

omit [CompleteSpace E] in
/-- Bound (10) on `[0, T]` with the uniform constant `e^{ω⁺ T}`. -/
private theorem norm_exp_apply_le {𝒜 : E →L[ℝ] E} {ω T t : ℝ}
    (h10 : ∀ t > 0, ∀ z, ‖NormedSpace.exp (t • 𝒜) z‖ ≤ Real.exp (t * ω) * ‖z‖)
    (ht0 : 0 ≤ t) (htT : t ≤ T) (z : E) :
    ‖NormedSpace.exp (t • 𝒜) z‖ ≤ Real.exp (max ω 0 * T) * ‖z‖ := by
  rcases ht0.eq_or_lt with rfl | ht
  · simp only [zero_smul, NormedSpace.exp_zero, one_apply_eq_self]
    exact le_mul_of_one_le_left (norm_nonneg _)
      (Real.one_le_exp (mul_nonneg (le_max_right _ _) htT))
  · refine (h10 t ht z).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _))
    calc t * ω ≤ t * max ω 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) ht.le
      _ ≤ T * max ω 0 := mul_le_mul_of_nonneg_right htT (le_max_right _ _)
      _ = max ω 0 * T := mul_comm _ _

/-- **Parabolic smoothing, difference form.** If `‖e^{r𝒜} (𝒜 z)‖ ≤ (D / r) ‖z‖` for
`0 < r ≤ T`, then `‖e^{b𝒜} z - e^{a𝒜} z‖ ≤ (D / a) ‖z‖ (b - a)` for `0 < a ≤ b ≤ T`. -/
private theorem norm_exp_sub_le {𝒜 : E →L[ℝ] E} {D T a b : ℝ}
    (hSm : ∀ r > 0, r ≤ T → ∀ z, ‖NormedSpace.exp (r • 𝒜) (𝒜 z)‖ ≤ D / r * ‖z‖)
    (hD : 0 ≤ D) (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T) (z : E) :
    ‖NormedSpace.exp (b • 𝒜) z - NormedSpace.exp (a • 𝒜) z‖ ≤ D / a * ‖z‖ * (b - a) := by
  have hd : ∀ s ∈ Icc a b, HasDerivWithinAt (fun s : ℝ => NormedSpace.exp (s • 𝒜) z)
      (NormedSpace.exp (s • 𝒜) (𝒜 z)) (Icc a b) s := fun s _ =>
    (hasDerivAt_exp_smul_apply 𝒜 z s).hasDerivWithinAt
  have hbd : ∀ s ∈ Ico a b, ‖NormedSpace.exp (s • 𝒜) (𝒜 z)‖ ≤ D / a * ‖z‖ := by
    intro s hs
    have hs0 : 0 < s := ha.trans_le hs.1
    exact (hSm s hs0 (hs.2.le.trans hbT) z).trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left hD ha hs.1) (norm_nonneg _))
  exact norm_image_sub_le_of_norm_deriv_le_segment' hd hbd b ⟨hab, le_rfl⟩

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- A field that is `L_t`-Lipschitz in time is continuous in time. -/
private theorem continuous_of_timeLipschitz {G : ℝ → E → E} {Lt : ℝ} (hLt : 0 ≤ Lt)
    (hGt : ∀ s t x, ‖G s x - G t x‖ ≤ Lt * |s - t|) (x : E) : Continuous fun t => G t x :=
  (LipschitzWith.of_dist_le_mul (f := fun t => G t x) (K := ⟨Lt, hLt⟩) fun s t => by
    rw [dist_eq_norm, Real.dist_eq]; exact hGt s t x).continuous

/-- Discrete Grönwall inequality, sum form: `a n ≤ β + α ∑_{k<n} a k` for `n ≤ N` implies
`a n ≤ β (1 + α)ⁿ`. -/
private theorem le_mul_pow_of_le_sum {a : ℕ → ℝ} {α β : ℝ} {N : ℕ} (hα : 0 ≤ α)
    (h : ∀ n ≤ N, a n ≤ β + α * ∑ k ∈ range n, a k) : ∀ n ≤ N, a n ≤ β * (1 + α) ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hsum : ∑ k ∈ range n, a k ≤ ∑ k ∈ range n, β * (1 + α) ^ k :=
      Finset.sum_le_sum fun k hk => ih k (Finset.mem_range.1 hk)
        (by have := Finset.mem_range.1 hk; omega)
    have hgeom : α * ∑ k ∈ range n, (1 + α) ^ k = (1 + α) ^ n - 1 := by
      have := geom_sum_mul (1 + α) n
      rw [show 1 + α - 1 = α by ring] at this
      rw [mul_comm]
      exact this
    calc a n ≤ β + α * ∑ k ∈ range n, a k := h n hn
      _ ≤ β + α * ∑ k ∈ range n, β * (1 + α) ^ k := by
          linarith [mul_le_mul_of_nonneg_left hsum hα]
      _ = β + β * (α * ∑ k ∈ range n, (1 + α) ^ k) := by rw [← Finset.mul_sum]; ring
      _ = β * (1 + α) ^ n := by rw [hgeom]; ring

/-- `log j ≤ |log T| + |log τ|` whenever `j τ ≤ T`, `τ > 0`. -/
private theorem log_le_of_mul_le {τ T : ℝ} (hτ : 0 < τ) {j : ℕ} (hj : (j : ℝ) * τ ≤ T) :
    Real.log j ≤ |Real.log T| + |Real.log τ| := by
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · simp only [Nat.cast_zero, Real.log_zero]
    positivity
  · have hj1 : (0 : ℝ) < j := Nat.cast_pos.2 hjpos
    have hTpos : 0 < T := lt_of_lt_of_le (mul_pos hj1 hτ) hj
    have hjT : (j : ℝ) ≤ T / τ := by rw [le_div_iff₀ hτ]; exact hj
    calc Real.log j ≤ Real.log (T / τ) := Real.log_le_log hj1 hjT
      _ = Real.log T - Real.log τ := Real.log_div hTpos.ne' hτ.ne'
      _ ≤ |Real.log T| + |Real.log τ| := by
          linarith [le_abs_self (Real.log T), neg_abs_le (Real.log τ)]

end Semigroup

/-! ### Proposition 1: error of the full-rank Lie–Trotter splitting -/

section FullRank

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The propagated local error of the full-rank splitting** (arXiv 1803.10473, proof of
Proposition 1, eqs. (16) and (20)). On a step `[a, b]`, `b = a + τ`, let `X` solve
`Ẋ = 𝒜 X + G(t, X)` with `‖G(t, X(t)) - G(a, X(a))‖ ≤ K_x (t - a)`, and let `W` be the
`G`-flow from `X(a)`. If `e^{r𝒜}` is bounded by `M` on `[0, T]` and smooths as
`‖e^{r𝒜} (𝒜 z)‖ ≤ (C_s M / r) ‖z‖`, then the local error `X(b) - e^{τ𝒜} W(b)`, propagated by
`e^{jτ𝒜}` with `(j + 1) τ ≤ T`, is at most `τ · M τ (K_x + L_t + L B) + τ D_j` with
`D_0 = 2 M B`, `D_j = C_s M B / j` (`j ≥ 1`). -/
private theorem norm_exp_localError_le {𝒜 : E →L[ℝ] E} {G : ℝ → E → E}
    {M Cs L B Lt Kx T τ a b : ℝ}
    (hMb : ∀ r, 0 ≤ r → r ≤ T → ∀ z, ‖NormedSpace.exp (r • 𝒜) z‖ ≤ M * ‖z‖)
    (hSm : ∀ r > 0, r ≤ T → ∀ z, ‖NormedSpace.exp (r • 𝒜) (𝒜 z)‖ ≤ Cs * M / r * ‖z‖)
    (hM : 0 ≤ M) (hCsM : 0 ≤ Cs * M) (hG : IsLipschitzField G L) (hL : 0 ≤ L)
    (hB : IsBoundedField G B) (hGt : ∀ s t x, ‖G s x - G t x‖ ≤ Lt * |s - t|) (hLt : 0 ≤ Lt)
    (hKx : 0 ≤ Kx) (hτ : 0 < τ) (hb : b = a + τ) {X W : ℝ → E}
    (hX : ODESolution (fun t x => 𝒜 x + G t x) X a b)
    (hXreg : ∀ t ∈ Icc a b, ‖G t (X t) - G a (X a)‖ ≤ Kx * (t - a))
    (hW : ODESolution G W a b) (hW₀ : W a = X a) (j : ℕ) (hj : ((j : ℝ) + 1) * τ ≤ T) :
    ‖NormedSpace.exp (((j : ℝ) * τ) • 𝒜) (X b - NormedSpace.exp (τ • 𝒜) (W b))‖ ≤
      τ * (M * τ * (Kx + Lt + L * B)) + τ * (if j = 0 then 2 * M * B else Cs * M * B / j) := by
  have hB0 : 0 ≤ B := hB.nonneg
  have hab : a ≤ b := by linarith
  have hjτ : 0 ≤ (j : ℝ) * τ := mul_nonneg (Nat.cast_nonneg _) hτ.le
  set c' : ℝ := ((j : ℝ) + 1) * τ with hc'
  set c : ℝ := b + (j : ℝ) * τ with hc
  have hSd : ∀ t, HasDerivAt (fun s => NormedSpace.exp ((c - s) • 𝒜))
      (-(NormedSpace.exp ((c - t) • 𝒜) * 𝒜)) t := fun t => hasDerivAt_exp_sub_smul 𝒜 c t
  have hwc : ContinuousOn (fun t => NormedSpace.exp ((c - t) • 𝒜) (X t) -
      NormedSpace.exp (c' • 𝒜) (W t)) (Icc a b) := by
    have h1 : Continuous fun s => NormedSpace.exp ((c - s) • 𝒜) :=
      continuous_iff_continuousAt.2 fun s => (hSd s).continuousAt
    exact (h1.continuousOn.clm_apply hX.cont).sub
      ((NormedSpace.exp (c' • 𝒜)).continuous.comp_continuousOn hW.cont)
  have hwd : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => NormedSpace.exp ((c - t) • 𝒜) (X t) -
      NormedSpace.exp (c' • 𝒜) (W t))
      (NormedSpace.exp ((c - t) • 𝒜) (G t (X t)) - NormedSpace.exp (c' • 𝒜) (G t (W t)))
      (Ici t) t := by
    intro t ht
    have h1 := ((hSd t).hasDerivWithinAt (s := Ici t)).clm_apply (hX.deriv t ht)
    have h2 := (NormedSpace.exp (c' • 𝒜)).hasFDerivAt.comp_hasDerivWithinAt t (hW.deriv t ht)
    refine (h1.sub h2).congr_deriv ?_
    simp only [neg_apply, mul_apply_eq_comp, map_add]
    abel
  have hbound : ∀ t ∈ Ico a b, ‖NormedSpace.exp ((c - t) • 𝒜) (G t (X t)) -
      NormedSpace.exp (c' • 𝒜) (G t (W t))‖ ≤
      M * τ * (Kx + Lt + L * B) + (if j = 0 then 2 * M * B else Cs * M * B / j) := by
    intro t ht
    have htI : t ∈ Icc a b := Ico_subset_Icc_self ht
    have hta : 0 ≤ t - a := by linarith [ht.1]
    have htb : t - a < τ := by linarith [ht.2]
    have hct : c - t = c' - (t - a) := by rw [hc, hc', hb]; ring
    have hct0 : (j : ℝ) * τ < c - t := by rw [hct, hc']; linarith
    have hctT : c - t ≤ T := by rw [hct]; linarith
    have hc'0 : 0 ≤ c' := by rw [hc']; exact mul_nonneg (by positivity) hτ.le
    have hdec : NormedSpace.exp ((c - t) • 𝒜) (G t (X t)) -
        NormedSpace.exp (c' • 𝒜) (G t (W t)) =
        NormedSpace.exp ((c - t) • 𝒜) (G t (X t) - G a (X a)) +
        (NormedSpace.exp ((c - t) • 𝒜) (G a (X a)) - NormedSpace.exp (c' • 𝒜) (G a (X a))) +
        NormedSpace.exp (c' • 𝒜) (G a (X a) - G t (W t)) := by
      simp only [map_sub]
      abel
    rw [hdec]
    have e1 : ‖NormedSpace.exp ((c - t) • 𝒜) (G t (X t) - G a (X a))‖ ≤ M * (Kx * τ) :=
      (hMb _ (by linarith) hctT _).trans (mul_le_mul_of_nonneg_left ((hXreg t htI).trans
        (mul_le_mul_of_nonneg_left htb.le hKx)) hM)
    have e3 : ‖NormedSpace.exp (c' • 𝒜) (G a (X a) - G t (W t))‖ ≤
        M * ((Lt + L * B) * τ) := by
      refine (hMb _ hc'0 hj _).trans (mul_le_mul_of_nonneg_left ?_ hM)
      have hWt : ‖W t - W a‖ ≤ B * (t - a) := hW.norm_sub_le_of_bounded hB t htI
      have h1 : |a - t| ≤ τ := by rw [abs_sub_comm, abs_of_nonneg hta]; exact htb.le
      have h2 : ‖W a - W t‖ ≤ B * τ := by
        rw [norm_sub_rev]; exact hWt.trans (mul_le_mul_of_nonneg_left htb.le hB0)
      rw [← hW₀]
      calc ‖G a (W a) - G t (W t)‖ ≤ ‖G a (W a) - G t (W a)‖ + ‖G t (W a) - G t (W t)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ Lt * |a - t| + L * ‖W a - W t‖ := add_le_add (hGt _ _ _) (hG _ _ _)
        _ ≤ Lt * τ + L * (B * τ) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 hLt) (mul_le_mul_of_nonneg_left h2 hL)
        _ = (Lt + L * B) * τ := by ring
    have e2 : ‖NormedSpace.exp ((c - t) • 𝒜) (G a (X a)) -
        NormedSpace.exp (c' • 𝒜) (G a (X a))‖ ≤
        (if j = 0 then 2 * M * B else Cs * M * B / j) := by
      split_ifs with hj0
      · calc _ ≤ ‖NormedSpace.exp ((c - t) • 𝒜) (G a (X a))‖ +
              ‖NormedSpace.exp (c' • 𝒜) (G a (X a))‖ := norm_sub_le _ _
          _ ≤ M * B + M * B := add_le_add
              ((hMb _ (by linarith) hctT _).trans (mul_le_mul_of_nonneg_left (hB _ _) hM))
              ((hMb _ hc'0 hj _).trans (mul_le_mul_of_nonneg_left (hB _ _) hM))
          _ = 2 * M * B := by ring
      · have hjpos : (0 : ℝ) < j := Nat.cast_pos.2 (Nat.pos_of_ne_zero hj0)
        have hjτpos : 0 < (j : ℝ) * τ := mul_pos hjpos hτ
        have hpos : 0 < c - t := hjτpos.trans hct0
        have h := norm_exp_sub_le hSm hCsM hpos (show c - t ≤ c' by linarith) hj (G a (X a))
        rw [norm_sub_rev]
        refine h.trans ?_
        have h1 : Cs * M / (c - t) ≤ Cs * M / ((j : ℝ) * τ) :=
          div_le_div_of_nonneg_left hCsM hjτpos hct0.le
        have h2 : c' - (c - t) ≤ τ := by linarith
        have h3 : 0 ≤ c' - (c - t) := by linarith
        have h4 : 0 ≤ Cs * M / ((j : ℝ) * τ) := div_nonneg hCsM hjτpos.le
        calc Cs * M / (c - t) * ‖G a (X a)‖ * (c' - (c - t)) ≤
              Cs * M / ((j : ℝ) * τ) * B * τ :=
            mul_le_mul (mul_le_mul h1 (hB _ _) (norm_nonneg _) h4) h2 h3 (mul_nonneg h4 hB0)
          _ = Cs * M * B * τ / ((j : ℝ) * τ) := by ring
          _ = Cs * M * B / j := mul_div_mul_right _ _ hτ.ne'
    calc ‖NormedSpace.exp ((c - t) • 𝒜) (G t (X t) - G a (X a)) +
          (NormedSpace.exp ((c - t) • 𝒜) (G a (X a)) - NormedSpace.exp (c' • 𝒜) (G a (X a))) +
          NormedSpace.exp (c' • 𝒜) (G a (X a) - G t (W t))‖ ≤
          ‖NormedSpace.exp ((c - t) • 𝒜) (G t (X t) - G a (X a))‖ +
          ‖NormedSpace.exp ((c - t) • 𝒜) (G a (X a)) - NormedSpace.exp (c' • 𝒜) (G a (X a))‖ +
          ‖NormedSpace.exp (c' • 𝒜) (G a (X a) - G t (W t))‖ := norm_add₃_le
      _ ≤ M * (Kx * τ) + (if j = 0 then 2 * M * B else Cs * M * B / j) +
          M * ((Lt + L * B) * τ) := add_le_add (add_le_add e1 e2) e3
      _ = M * τ * (Kx + Lt + L * B) + (if j = 0 then 2 * M * B else Cs * M * B / j) := by ring
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hwc hwd hbound b ⟨hab, le_rfl⟩
  have hwa : NormedSpace.exp ((c - a) • 𝒜) (X a) - NormedSpace.exp (c' • 𝒜) (W a) = 0 := by
    rw [show c - a = c' by rw [hc, hc', hb]; ring, hW₀, sub_self]
  have hwb : NormedSpace.exp ((c - b) • 𝒜) (X b) - NormedSpace.exp (c' • 𝒜) (W b) =
      NormedSpace.exp (((j : ℝ) * τ) • 𝒜) (X b - NormedSpace.exp (τ • 𝒜) (W b)) := by
    rw [show c - b = (j : ℝ) * τ by rw [hc]; ring,
      show c' = (j : ℝ) * τ + τ by rw [hc']; ring, exp_smul_add_apply, map_sub]
  calc ‖NormedSpace.exp (((j : ℝ) * τ) • 𝒜) (X b - NormedSpace.exp (τ • 𝒜) (W b))‖
      = ‖(NormedSpace.exp ((c - b) • 𝒜) (X b) - NormedSpace.exp (c' • 𝒜) (W b)) -
          (NormedSpace.exp ((c - a) • 𝒜) (X a) - NormedSpace.exp (c' • 𝒜) (W a))‖ := by
        rw [hwa, sub_zero, hwb]
    _ ≤ (M * τ * (Kx + Lt + L * B) + (if j = 0 then 2 * M * B else Cs * M * B / j)) *
          (b - a) := hmvt
    _ = τ * (M * τ * (Kx + Lt + L * B)) + τ * (if j = 0 then 2 * M * B else Cs * M * B / j) := by
        rw [hb]; ring

/-- **arXiv 1803.10473, Proposition 1** (global error of the full-rank Lie–Trotter splitting,
finite-dimensional form). Let `𝒜` be a bounded operator on a real inner product space `E`
satisfying Assumption 1(a) for `t > 0`: (10) `‖e^{t𝒜} z‖ ≤ e^{tω} ‖z‖` and (11)
`‖e^{t𝒜} (𝒜 z)‖ ≤ (C_s / t) e^{tω} ‖z‖`, `C_s > 0`. Let `G` be `L`-Lipschitz in the state,
bounded by `B` and `L_t`-Lipschitz in time, and let `X` solve `Ẋ = 𝒜 X + G(t, X)` on
`[t₀, t₀ + N τ]`, `N τ ≤ T`, `τ > 0`, with `‖G(s, X(s)) - G(t, X(t))‖ ≤ K_x |s - t|`. Let `Z` be
the full-rank Lie–Trotter splitting from `Z 0 = X(t₀)`:
`Z (k+1) = e^{τ𝒜} V k(tₖ₊₁)`, `V k` the exact flow of `Ẋ = G(t, X)` on `[tₖ, tₖ₊₁]` from `Z k`.
Then for all `n ≤ N`

    ‖X(t₀ + n τ) - Zₙ‖ ≤ C τ (1 + |log τ|),
    C = e^{M L e^{L T} T} · M (T (K_x + L_t + L B) + 2 B + C_s B (1 + |log T|)),  M = e^{ω⁺ T}.

Deviations (see the module docstring): finite-dimensional real setting with bounded `𝒜`; global
`L`, `B`, `L_t` instead of `C¹` near the solution; the bound `K_x` on `dG/ds` along the exact
solution, used but not listed by the paper, is an explicit hypothesis, and `C` depends on it. -/
theorem fullRank_lieTrotter_error {𝒜 : E →L[ℝ] E} {G : ℝ → E → E}
    {ω Cs L B Lt Kx τ t₀ T : ℝ}
    (h10 : ∀ t > 0, ∀ z, ‖NormedSpace.exp (t • 𝒜) z‖ ≤ Real.exp (t * ω) * ‖z‖)
    (h11 : ∀ t > 0, ∀ z, ‖NormedSpace.exp (t • 𝒜) (𝒜 z)‖ ≤ Cs / t * Real.exp (t * ω) * ‖z‖)
    (hCs : 0 < Cs) (hG : IsLipschitzField G L) (hL : 0 ≤ L) (hB : IsBoundedField G B)
    (hGt : ∀ s t x, ‖G s x - G t x‖ ≤ Lt * |s - t|) (hLt : 0 ≤ Lt) (hKx : 0 ≤ Kx)
    (hτ : 0 < τ) {N : ℕ} (hNT : (N : ℝ) * τ ≤ T) {X : ℝ → E}
    (hX : ODESolution (fun t x => 𝒜 x + G t x) X t₀ (t₀ + N * τ))
    (hXreg : ∀ s ∈ Icc t₀ (t₀ + N * τ), ∀ t ∈ Icc t₀ (t₀ + N * τ),
      ‖G s (X s) - G t (X t)‖ ≤ Kx * |s - t|)
    {Z : ℕ → E} {V : ℕ → ℝ → E} (hZ0 : Z 0 = X t₀)
    (hV : ∀ k < N, ODESolution G (V k) (t₀ + k * τ) (t₀ + (k + 1) * τ))
    (hV₀ : ∀ k < N, V k (t₀ + k * τ) = Z k)
    (hZ : ∀ k < N, Z (k + 1) = NormedSpace.exp (τ • 𝒜) (V k (t₀ + (k + 1) * τ))) :
    ∀ n ≤ N, ‖X (t₀ + n * τ) - Z n‖ ≤
      Real.exp (Real.exp (max ω 0 * T) * L * Real.exp (L * T) * T) *
        (Real.exp (max ω 0 * T) * (T * (Kx + Lt + L * B) + 2 * B + Cs * B * (1 + |Real.log T|)))
        * τ * (1 + |Real.log τ|) := by
  have hT0 : 0 ≤ T := le_trans (mul_nonneg (Nat.cast_nonneg _) hτ.le) hNT
  have hB0 : 0 ≤ B := hB.nonneg
  obtain ⟨M, hMdef⟩ : ∃ M, M = Real.exp (max ω 0 * T) := ⟨_, rfl⟩
  rw [← hMdef]
  have hM1 : 1 ≤ M := by rw [hMdef]; exact Real.one_le_exp (mul_nonneg (le_max_right _ _) hT0)
  have hM0 : 0 ≤ M := by linarith
  have hMb : ∀ r, 0 ≤ r → r ≤ T → ∀ z, ‖NormedSpace.exp (r • 𝒜) z‖ ≤ M * ‖z‖ :=
    fun r h0 h1 z => by rw [hMdef]; exact norm_exp_apply_le h10 h0 h1 z
  have hSm : ∀ r > 0, r ≤ T → ∀ z, ‖NormedSpace.exp (r • 𝒜) (𝒜 z)‖ ≤ Cs * M / r * ‖z‖ := by
    intro r hr hrT z
    refine (h11 r hr z).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have he : Real.exp (r * ω) ≤ M := by
      rw [hMdef]
      apply Real.exp_le_exp.2
      calc r * ω ≤ r * max ω 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hr.le
        _ ≤ T * max ω 0 := mul_le_mul_of_nonneg_right hrT (le_max_right _ _)
        _ = max ω 0 * T := mul_comm _ _
    calc Cs / r * Real.exp (r * ω) ≤ Cs / r * M :=
          mul_le_mul_of_nonneg_left he (div_nonneg hCs.le hr.le)
      _ = Cs * M / r := by ring
  have hCsM : 0 ≤ Cs * M := mul_nonneg hCs.le hM0
  have hGc := continuous_of_timeLipschitz hLt hGt
  have hle : ∀ k : ℕ, t₀ + k * τ ≤ t₀ + (k + 1) * τ := fun k => by linarith
  choose W hW hW₀ using fun k : ℕ => exists_ODESolution hG hB hGc (hle k) (X (t₀ + k * τ))
  -- the exact solution on each step
  have hkN : ∀ k < N, t₀ ≤ t₀ + k * τ ∧ t₀ + (k + 1) * τ ≤ t₀ + N * τ := by
    intro k hk
    have hk1 : (k : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hk
    exact ⟨by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hτ.le],
      by nlinarith [mul_le_mul_of_nonneg_right hk1 hτ.le]⟩
  have hXk : ∀ k < N,
      ODESolution (fun t x => 𝒜 x + G t x) X (t₀ + k * τ) (t₀ + (k + 1) * τ) :=
    fun k hk => hX.mono (hkN k hk).1 (hkN k hk).2
  have hXregk : ∀ k < N, ∀ t ∈ Icc (t₀ + k * τ) (t₀ + (k + 1) * τ),
      ‖G t (X t) - G (t₀ + k * τ) (X (t₀ + k * τ))‖ ≤ Kx * (t - (t₀ + k * τ)) := by
    intro k hk t ht
    obtain ⟨h0k, hkN'⟩ := hkN k hk
    have h := hXreg t ⟨h0k.trans ht.1, ht.2.trans hkN'⟩ (t₀ + k * τ) ⟨h0k, (hle k).trans hkN'⟩
    rwa [abs_of_nonneg (show (0 : ℝ) ≤ t - (t₀ + k * τ) by linarith [ht.1])] at h
  -- local errors `e k` and propagation defects `H k`
  obtain ⟨e, he⟩ : ∃ e : ℕ → E, ∀ k, e k =
      X (t₀ + (k + 1) * τ) - NormedSpace.exp (τ • 𝒜) (W k (t₀ + (k + 1) * τ)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℕ → E, ∀ k, H k =
      (W k (t₀ + (k + 1) * τ) - V k (t₀ + (k + 1) * τ)) - (X (t₀ + k * τ) - Z k) :=
    ⟨_, fun _ => rfl⟩
  have hstep1 : ∀ k < N, X (t₀ + (k + 1) * τ) - Z (k + 1) =
      e k + NormedSpace.exp (τ • 𝒜) ((X (t₀ + k * τ) - Z k) + H k) := by
    intro k hk
    rw [he, hH, hZ k hk]
    simp only [map_sub, map_add]
    abel
  have hHk : ∀ k < N, ‖H k‖ ≤ L * Real.exp (L * τ) * ‖X (t₀ + k * τ) - Z k‖ * τ := by
    intro k hk
    have hdist : ∀ t ∈ Icc (t₀ + k * τ) (t₀ + (k + 1) * τ),
        ‖W k t - V k t‖ ≤ Real.exp (L * τ) * ‖X (t₀ + k * τ) - Z k‖ := by
      intro t ht
      have h := (hW k).norm_sub_le_exp hG hL (hV k hk) t ht
      rw [hW₀ k, hV₀ k hk] at h
      refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _))
      exact mul_le_mul_of_nonneg_left (by linarith [ht.2]) hL
    have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment
      ((hW k).cont.sub (hV k hk).cont)
      (fun t ht => ((hW k).deriv t ht).sub ((hV k hk).deriv t ht))
      (fun t ht => (hG t (W k t) (V k t)).trans
        (mul_le_mul_of_nonneg_left (hdist t (Ico_subset_Icc_self ht)) hL))
      (t₀ + (k + 1) * τ) ⟨hle k, le_rfl⟩
    have hval : H k = (W k (t₀ + (k + 1) * τ) - V k (t₀ + (k + 1) * τ)) -
        (W k (t₀ + k * τ) - V k (t₀ + k * τ)) := by
      rw [hH, hW₀ k, hV₀ k hk]
    rw [hval]
    calc _ ≤ L * (Real.exp (L * τ) * ‖X (t₀ + k * τ) - Z k‖) *
          (t₀ + (k + 1) * τ - (t₀ + k * τ)) := hmvt
      _ = _ := by ring
  -- the error recursion, solved exactly (eq. (18))
  have hshift : ∀ (r : ℕ) (x : E), NormedSpace.exp (τ • 𝒜)
      (NormedSpace.exp (((r : ℝ) * τ) • 𝒜) x) =
      NormedSpace.exp ((((r + 1 : ℕ) : ℝ) * τ) • 𝒜) x := by
    intro r x
    have hr : τ + (r : ℝ) * τ = ((r + 1 : ℕ) : ℝ) * τ := by push_cast; ring
    rw [← exp_smul_add_apply, hr]
  have hunroll : ∀ n ≤ N, X (t₀ + n * τ) - Z n = ∑ k ∈ range n,
      (NormedSpace.exp ((((n - 1 - k : ℕ) : ℝ) * τ) • 𝒜) (e k) +
        NormedSpace.exp ((((n - k : ℕ) : ℝ) * τ) • 𝒜) (H k)) := by
    intro n
    induction n with
    | zero => intro _; simp [hZ0]
    | succ n ih =>
      intro hn
      have hnN : n < N := by omega
      have hcast : t₀ + ((n + 1 : ℕ) : ℝ) * τ = t₀ + ((n : ℝ) + 1) * τ := by push_cast; ring
      rw [hcast, hstep1 n hnN, ih (by omega), Finset.sum_range_succ, map_add, map_sum]
      have hsum : ∑ k ∈ range n, NormedSpace.exp (τ • 𝒜)
          (NormedSpace.exp ((((n - 1 - k : ℕ) : ℝ) * τ) • 𝒜) (e k) +
            NormedSpace.exp ((((n - k : ℕ) : ℝ) * τ) • 𝒜) (H k)) =
          ∑ k ∈ range n, (NormedSpace.exp ((((n + 1 - 1 - k : ℕ) : ℝ) * τ) • 𝒜) (e k) +
            NormedSpace.exp ((((n + 1 - k : ℕ) : ℝ) * τ) • 𝒜) (H k)) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k < n := Finset.mem_range.1 hk
        rw [map_add, hshift, hshift, show n - 1 - k + 1 = n + 1 - 1 - k by omega,
          show n - k + 1 = n + 1 - k by omega]
      rw [hsum, show n + 1 - 1 - n = 0 by omega, show n + 1 - n = 1 by omega]
      simp only [Nat.cast_zero, zero_mul, zero_smul, NormedSpace.exp_zero,
        one_apply_eq_self, Nat.cast_one, one_mul]
      abel
  -- the weights `D j` of the propagated local errors and their sum (eq. (20))
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, ∀ j, D j = if j = 0 then 2 * M * B else Cs * M * B / j :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = |Real.log T| + |Real.log τ| := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  have hDsum : ∀ n ≤ N, ∑ j ∈ range n, D j ≤ 2 * M * B + Cs * M * B * (1 + Λ) := by
    intro n hn
    have hnonneg : 0 ≤ 2 * M * B + Cs * M * B * (1 + Λ) :=
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0) hB0)
        (mul_nonneg (mul_nonneg hCsM hB0) (by linarith))
    cases n with
    | zero => simpa using hnonneg
    | succ m =>
      have hD0 : D 0 = 2 * M * B := by simp [hD]
      rw [Finset.sum_range_succ', hD0]
      have hterm : ∀ j ∈ range m, D (j + 1) = Cs * M * B * (((j + 1 : ℕ) : ℝ))⁻¹ := by
        intro j _
        rw [hD]
        simp [div_eq_mul_inv]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      have hharm : ∑ j ∈ range m, (((j + 1 : ℕ) : ℝ))⁻¹ = (harmonic m : ℝ) := by
        simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      have hm : (m : ℝ) * τ ≤ T := by
        have hmN : (m : ℝ) ≤ N := by exact_mod_cast (show m ≤ N by omega)
        exact (mul_le_mul_of_nonneg_right hmN hτ.le).trans hNT
      have hlog := log_le_of_mul_le hτ hm
      have hh := harmonic_le_one_add_log m
      rw [hharm]
      have : Cs * M * B * (harmonic m : ℝ) ≤ Cs * M * B * (1 + Λ) :=
        mul_le_mul_of_nonneg_left (by rw [hΛ]; linarith) (mul_nonneg hCsM hB0)
      linarith
  -- the error inequality `‖Eₙ‖ ≤ β + α ∑_{k<n} ‖Eₖ‖`
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = M * L * Real.exp (L * τ) * τ := ⟨_, rfl⟩
  have hα0 : 0 ≤ α := by
    rw [hα]; exact mul_nonneg (mul_nonneg (mul_nonneg hM0 hL) (Real.exp_pos _).le) hτ.le
  have hXc : 0 ≤ Kx + Lt + L * B := add_nonneg (add_nonneg hKx hLt) (mul_nonneg hL hB0)
  obtain ⟨β, hβ⟩ : ∃ β : ℝ,
      β = τ * (M * T * (Kx + Lt + L * B) + 2 * M * B + Cs * M * B * (1 + Λ)) := ⟨_, rfl⟩
  have hrec : ∀ n ≤ N, ‖X (t₀ + n * τ) - Z n‖ ≤
      β + α * ∑ k ∈ range n, ‖X (t₀ + k * τ) - Z k‖ := by
    intro n hn
    rw [hunroll n hn]
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
    have hnT : (n : ℝ) * τ ≤ T := (mul_le_mul_of_nonneg_right hnN hτ.le).trans hNT
    have hloc : ∀ k ∈ range n,
        ‖NormedSpace.exp ((((n - 1 - k : ℕ) : ℝ) * τ) • 𝒜) (e k)‖ ≤
        τ * (M * τ * (Kx + Lt + L * B)) + τ * D (n - 1 - k) := by
      intro k hk
      have hk' : k < n := Finset.mem_range.1 hk
      have hkN' : k < N := lt_of_lt_of_le hk' hn
      have hj : (((n - 1 - k : ℕ) : ℝ) + 1) * τ ≤ T := by
        have h1 : ((n - 1 - k : ℕ) : ℝ) + 1 ≤ n := by
          have h2 : n - 1 - k + 1 ≤ n := by omega
          exact_mod_cast h2
        exact (mul_le_mul_of_nonneg_right h1 hτ.le).trans hnT
      rw [hD, he]
      exact norm_exp_localError_le hMb hSm hM0 hCsM hG hL hB hGt hLt hKx hτ (by ring)
        (hXk k hkN') (hXregk k hkN') (hW k) (hW₀ k) (n - 1 - k) hj
    have hprop : ∀ k ∈ range n,
        ‖NormedSpace.exp ((((n - k : ℕ) : ℝ) * τ) • 𝒜) (H k)‖ ≤
        α * ‖X (t₀ + k * τ) - Z k‖ := by
      intro k hk
      have hk' : k < n := Finset.mem_range.1 hk
      have hkN' : k < N := lt_of_lt_of_le hk' hn
      have hr0 : 0 ≤ ((n - k : ℕ) : ℝ) * τ := mul_nonneg (Nat.cast_nonneg _) hτ.le
      have hrT : ((n - k : ℕ) : ℝ) * τ ≤ T := by
        have h1 : ((n - k : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n k
        exact (mul_le_mul_of_nonneg_right h1 hτ.le).trans hnT
      refine (hMb _ hr0 hrT _).trans ?_
      rw [hα]
      calc M * ‖H k‖ ≤ M * (L * Real.exp (L * τ) * ‖X (t₀ + k * τ) - Z k‖ * τ) :=
            mul_le_mul_of_nonneg_left (hHk k hkN') hM0
        _ = M * L * Real.exp (L * τ) * τ * ‖X (t₀ + k * τ) - Z k‖ := by ring
    have h1 : (n : ℝ) * (τ * (M * τ * (Kx + Lt + L * B))) ≤ τ * (M * T * (Kx + Lt + L * B)) := by
      have heq : (n : ℝ) * (τ * (M * τ * (Kx + Lt + L * B))) =
          τ * (M * ((n : ℝ) * τ) * (Kx + Lt + L * B)) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnT hM0) hXc) hτ.le
    have h2 : τ * ∑ j ∈ range n, D j ≤ τ * (2 * M * B + Cs * M * B * (1 + Λ)) :=
      mul_le_mul_of_nonneg_left (hDsum n hn) hτ.le
    calc _ ≤ ∑ k ∈ range n, (‖NormedSpace.exp ((((n - 1 - k : ℕ) : ℝ) * τ) • 𝒜) (e k)‖ +
          ‖NormedSpace.exp ((((n - k : ℕ) : ℝ) * τ) • 𝒜) (H k)‖) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_add_le _ _)
      _ ≤ ∑ k ∈ range n, ((τ * (M * τ * (Kx + Lt + L * B)) + τ * D (n - 1 - k)) +
          α * ‖X (t₀ + k * τ) - Z k‖) :=
          Finset.sum_le_sum fun k hk => add_le_add (hloc k hk) (hprop k hk)
      _ = n * (τ * (M * τ * (Kx + Lt + L * B))) + τ * ∑ j ∈ range n, D j +
          α * ∑ k ∈ range n, ‖X (t₀ + k * τ) - Z k‖ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum,
            Finset.sum_range_reflect D n]
      _ ≤ β + α * ∑ k ∈ range n, ‖X (t₀ + k * τ) - Z k‖ := by
          rw [hβ]
          linarith
  -- discrete Grönwall
  have hgr := le_mul_pow_of_le_sum (a := fun k => ‖X (t₀ + k * τ) - Z k‖) hα0 hrec
  intro n hn
  have hβ0 : 0 ≤ β := by
    rw [hβ]
    exact mul_nonneg hτ.le (add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg hM0 hT0) hXc) (mul_nonneg (mul_nonneg (by norm_num) hM0) hB0))
      (mul_nonneg (mul_nonneg hCsM hB0) (by linarith)))
  have hnα : (n : ℝ) * α ≤ M * L * Real.exp (L * T) * T := by
    have hR0 : 0 ≤ M * L * Real.exp (L * T) * T :=
      mul_nonneg (mul_nonneg (mul_nonneg hM0 hL) (Real.exp_pos _).le) hT0
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simpa using hR0
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      have hnT : (n : ℝ) * τ ≤ T :=
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hτ.le).trans hNT
      have hτT : τ ≤ T := by nlinarith [mul_le_mul_of_nonneg_right hn1 hτ.le]
      have hexp : Real.exp (L * τ) ≤ Real.exp (L * T) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτT hL)
      have heq : (n : ℝ) * α = M * L * Real.exp (L * τ) * ((n : ℝ) * τ) := by rw [hα]; ring
      rw [heq]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hexp (mul_nonneg hM0 hL)) hnT
        (mul_nonneg (Nat.cast_nonneg _) hτ.le)
        (mul_nonneg (mul_nonneg hM0 hL) (Real.exp_pos _).le)
  have hpow : (1 + α) ^ n ≤ Real.exp (M * L * Real.exp (L * T) * T) :=
    calc (1 + α) ^ n ≤ Real.exp α ^ n :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp α]) n
      _ = Real.exp (n * α) := (Real.exp_nat_mul α n).symm
      _ ≤ Real.exp (M * L * Real.exp (L * T) * T) := Real.exp_le_exp.2 hnα
  have hβle : β ≤ M * (T * (Kx + Lt + L * B) + 2 * B + Cs * B * (1 + |Real.log T|)) * τ *
      (1 + |Real.log τ|) := by
    have hl0 : 0 ≤ |Real.log τ| := abs_nonneg _
    have hP : 0 ≤ M * T * (Kx + Lt + L * B) + 2 * M * B + Cs * M * B * |Real.log T| :=
      add_nonneg (add_nonneg (mul_nonneg (mul_nonneg hM0 hT0) hXc)
        (mul_nonneg (mul_nonneg (by norm_num) hM0) hB0))
        (mul_nonneg (mul_nonneg hCsM hB0) (abs_nonneg _))
    rw [hβ, hΛ]
    nlinarith [mul_nonneg (mul_nonneg hτ.le hl0) hP]
  calc ‖X (t₀ + n * τ) - Z n‖ ≤ β * (1 + α) ^ n := hgr n hn
    _ ≤ β * Real.exp (M * L * Real.exp (L * T) * T) := mul_le_mul_of_nonneg_left hpow hβ0
    _ ≤ M * (T * (Kx + Lt + L * B) + 2 * B + Cs * B * (1 + |Real.log T|)) * τ *
          (1 + |Real.log τ|) * Real.exp (M * L * Real.exp (L * T) * T) :=
        mul_le_mul_of_nonneg_right hβle (Real.exp_pos _).le
    _ = _ := by ring

/-- **arXiv 1803.10473, Theorem 1** (global error of the low-rank Lie–Trotter splitting,
finite-dimensional form). Under the hypotheses of `fullRank_lieTrotter_error` (Assumption 1(a)
as (10), (11); `G` Lipschitz, bounded and Lipschitz in time; the regularity bound `K_x` along the
exact solution `X` on `[t₀, t₀ + N τ]`, `N τ ≤ T`), let `Y` be the low-rank Lie–Trotter
splitting `Y (k+1) = e^{τ𝒜} Φ̃^G_τ(Y k)`, where `Φ̃^G_τ(Y k) = YL k tₖ₊₁` is one step of the
projector-splitting integrator (`IsKSLStep`, normal-component bound `ε ≥ 0`, the paper's
Assumption 1(c)), and `‖X(t₀) - Y 0‖ ≤ δ`. Then for all `n ≤ N` and all `τ > 0`

    ‖X(t₀ + n τ) - Yₙ‖ ≤ c₀ τ (1 + |log τ|) + c₁ δ + c₂ ε,

`c₀ = C + 11 L B T e^{(L+ω⁺)T}` (`C` from Proposition 1), `c₁ = e^{(L+ω⁺)T}`,
`c₂ = T e^{(L+ω⁺)T}`. Proof as in the paper (Sec. 5.3): Proposition 1
(`fullRank_lieTrotter_error`) for `E_sp`, then `lowRank_lieTrotter_error_of_fullRank` (part a)
for `E_δ` and `E_lr`. The paper's `τ₀` is not needed since the constants are global. -/
theorem lowRank_lieTrotter_global_error {𝒜 : E →L[ℝ] E} {G : ℝ → E → E}
    {ω Cs L B Lt Kx ε δ τ t₀ T : ℝ}
    (h10 : ∀ t > 0, ∀ z, ‖NormedSpace.exp (t • 𝒜) z‖ ≤ Real.exp (t * ω) * ‖z‖)
    (h11 : ∀ t > 0, ∀ z, ‖NormedSpace.exp (t • 𝒜) (𝒜 z)‖ ≤ Cs / t * Real.exp (t * ω) * ‖z‖)
    (hCs : 0 < Cs) (hG : IsLipschitzField G L) (hL : 0 ≤ L) (hB : IsBoundedField G B)
    (hGt : ∀ s t x, ‖G s x - G t x‖ ≤ Lt * |s - t|) (hLt : 0 ≤ Lt) (hKx : 0 ≤ Kx)
    (hε : 0 ≤ ε) (hτ : 0 < τ) {N : ℕ} (hNT : (N : ℝ) * τ ≤ T) {X : ℝ → E}
    (hX : ODESolution (fun t x => 𝒜 x + G t x) X t₀ (t₀ + N * τ))
    (hXreg : ∀ s ∈ Icc t₀ (t₀ + N * τ), ∀ t ∈ Icc t₀ (t₀ + N * τ),
      ‖G s (X s) - G t (X t)‖ ≤ Kx * |s - t|)
    {Y : ℕ → E} {P Q : ℕ → E →L[ℝ] E} {YK YS YL : ℕ → ℝ → E}
    (hstep : ∀ k < N, IsKSLStep G ε (P k) (Q k) (t₀ + k * τ) (t₀ + (k + 1) * τ) (Y k) (YK k)
      (YS k) (YL k))
    (hY : ∀ k < N, Y (k + 1) = NormedSpace.exp (τ • 𝒜) (YL k (t₀ + (k + 1) * τ)))
    (hδ : ‖X t₀ - Y 0‖ ≤ δ) :
    ∀ n ≤ N, ‖X (t₀ + n * τ) - Y n‖ ≤
      (Real.exp (Real.exp (max ω 0 * T) * L * Real.exp (L * T) * T) *
          (Real.exp (max ω 0 * T) * (T * (Kx + Lt + L * B) + 2 * B + Cs * B * (1 + |Real.log T|)))
        + 11 * L * B * T * Real.exp ((L + max ω 0) * T)) * τ * (1 + |Real.log τ|)
        + Real.exp ((L + max ω 0) * T) * δ + T * Real.exp ((L + max ω 0) * T) * ε := by
  have hGc := continuous_of_timeLipschitz hLt hGt
  have hle : ∀ k : ℕ, t₀ + k * τ ≤ t₀ + (k + 1) * τ := fun k => by linarith
  choose U hU hU₀ using fun (k : ℕ) (z : E) => exists_ODESolution hG hB hGc (hle k) z
  let Z : ℕ → E := fun n => Nat.rec (motive := fun _ => E) (X t₀)
    (fun k x => NormedSpace.exp (τ • 𝒜) (U k x (t₀ + (k + 1) * τ))) n
  have hZ0 : Z 0 = X t₀ := rfl
  have hZs : ∀ k, Z (k + 1) = NormedSpace.exp (τ • 𝒜) (U k (Z k) (t₀ + (k + 1) * τ)) :=
    fun k => rfl
  have hsp := fullRank_lieTrotter_error h10 h11 hCs hG hL hB hGt hLt hKx hτ hNT hX hXreg
    (V := fun k => U k (Z k)) hZ0 (fun k _ => hU k (Z k)) (fun k _ => hU₀ k (Z k))
    (fun k _ => hZs k)
  have hΦ : ∀ x y, ‖NormedSpace.exp (τ • 𝒜) x - NormedSpace.exp (τ • 𝒜) y‖ ≤
      Real.exp (τ * ω) * ‖x - y‖ := fun x y => by
    rw [← map_sub]; exact h10 τ hτ _
  intro n hn
  have hnT : (n : ℝ) * τ ≤ T :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hτ.le).trans hNT
  rw [← hZ0] at hδ
  exact lowRank_lieTrotter_error_of_fullRank (Φ := ⇑(NormedSpace.exp (τ • 𝒜))) hG hL hB hGc hε
    hτ hΦ (U := fun k => U k (Z k)) (fun k _ => hU k (Z k)) (fun k _ => hU₀ k (Z k))
    (fun k _ => hZs k) (fun n hn _ => hsp n hn) hstep hY hδ n hn hnT

end FullRank

/-! ### The paper's matrix setting -/

section ExpHelper

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The matrix exponential `t ↦ e^{tA}` with Mathlib's entrywise topology (proof helper,
elaborated outside the Frobenius scope). -/
private noncomputable def expT (A : Matrix m m ℝ) (t : ℝ) : Matrix m m ℝ :=
  NormedSpace.exp (t • A)

private lemma sylvesterFlow_eq_expT (A : Matrix m m ℝ) (t : ℝ) (Z : Matrix m m ℝ) :
    sylvesterFlow A A t Z = expT A t * Z * (expT A t)ᵀ := rfl

end ExpHelper

section MatrixForm

open scoped LeanDLRA.Frobenius

variable {m : Type*} [Fintype m] [DecidableEq m]

private lemma hasDerivAt_expT (A : Matrix m m ℝ) (t : ℝ) :
    HasDerivAt (expT A) (A * expT A t) t := by
  let _ := Matrix.frobeniusNormedRing (m := m) (α := ℝ)
  let _ := Matrix.frobeniusNormedAlgebra (m := m) (α := ℝ) (R := ℝ)
  exact hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t

/-- The stiff flow `s ↦ e^{sA} Z e^{sAᵀ}` solves `Ẏ = A Y + Y Aᵀ` (Frobenius norm). -/
theorem hasDerivAt_sylvesterFlow (A Z : Matrix m m ℝ) (t : ℝ) :
    HasDerivAt (fun s => sylvesterFlow A A s Z)
      (A * sylvesterFlow A A t Z + sylvesterFlow A A t Z * Aᵀ) t := by
  have h := Frobenius.hasDerivAt_mul_mul (hasDerivAt_expT A t) (hasDerivAt_const t Z)
    (Frobenius.hasDerivAt_transpose (hasDerivAt_expT A t))
  simp only [sylvesterFlow_eq_expT]
  convert h using 1
  simp only [Matrix.transpose_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.mul_assoc]

/-- **The stiff flow is the operator exponential of the Lyapunov operator.** For
`𝒜 Z = A Z + Z Aᵀ` on `ℝ^{m×m}` with the Frobenius norm and `t ≥ 0`,
`e^{t𝒜} Z = e^{tA} Z (e^{tA})ᵀ = sylvesterFlow A A t Z` (arXiv 1803.10473, eq. (13); the paper's
`Φ^A_t`). Both sides solve `Ẏ = 𝒜 Y`, `Y(0) = Z`. -/
theorem exp_lyapunov_apply (A : Matrix m m ℝ) {t : ℝ} (ht : 0 ≤ t) (Z : Matrix m m ℝ) :
    NormedSpace.exp (t • (Frobenius.leftMulCLM A + Frobenius.rightMulCLM Aᵀ :
      Matrix m m ℝ →L[ℝ] Matrix m m ℝ)) Z = sylvesterFlow A A t Z := by
  set 𝒜 : Matrix m m ℝ →L[ℝ] Matrix m m ℝ :=
    Frobenius.leftMulCLM A + Frobenius.rightMulCLM Aᵀ with h𝒜
  have h𝒜a : ∀ X, 𝒜 X = A * X + X * Aᵀ := fun X => rfl
  have hf : ∀ s, HasDerivAt (fun s : ℝ => NormedSpace.exp (s • 𝒜) Z)
      (𝒜 (NormedSpace.exp (s • 𝒜) Z)) s := fun s => by
    have h := (hasDerivAt_exp_smul_const' 𝒜 s).clm_apply (hasDerivAt_const s Z)
    simpa using h
  have hg : ∀ s, HasDerivAt (fun s : ℝ => sylvesterFlow A A s Z)
      (𝒜 (sylvesterFlow A A s Z)) s := fun s => by
    rw [h𝒜a]; exact hasDerivAt_sylvesterFlow A Z s
  have hlip : IsLipschitzField (fun (_ : ℝ) (X : Matrix m m ℝ) => 𝒜 X) ‖𝒜‖ :=
    fun _ x y => by rw [← map_sub]; exact 𝒜.le_opNorm _
  have hsol1 : ODESolution (fun _ X => 𝒜 X) (fun s => NormedSpace.exp (s • 𝒜) Z) 0 t :=
    ⟨fun s _ => (hf s).continuousAt.continuousWithinAt, fun s _ => (hf s).hasDerivWithinAt⟩
  have hsol2 : ODESolution (fun _ X => 𝒜 X) (fun s => sylvesterFlow A A s Z) 0 t :=
    ⟨fun s _ => (hg s).continuousAt.continuousWithinAt, fun s _ => (hg s).hasDerivWithinAt⟩
  exact hsol1.eqOn hsol2 hlip (norm_nonneg _) (by simp [sylvesterFlow_zero_time])
    ⟨ht, le_rfl⟩

/-- **Assumption 1(a), bound (11), for discrete Laplacians.** If `-A` is positive semidefinite,
then `‖e^{tA} (AZ + ZAᵀ) e^{tAᵀ}‖ ≤ (e⁻¹ / t) e^{t·0} ‖Z‖` for all `t > 0`: (11) holds with
`ω = 0` and the grid-independent constant `C_s = e⁻¹` (`sylvester_dissipative_smoothing`,
OP-ST-14). Together with `sylvesterFlow_bound_of_negSemidef` this verifies Assumption 1(a). -/
theorem sylvesterFlow_smoothing_of_negSemidef {A : Matrix m m ℝ} (hA : (-A).PosSemidef) :
    ∀ t > 0, ∀ Z : Matrix m m ℝ,
      ‖sylvesterFlow A A t (A * Z + Z * Aᵀ)‖ ≤ Real.exp (-1) / t * Real.exp (t * 0) * ‖Z‖ := by
  intro t ht Z
  have h := (sylvester_dissipative_smoothing hA hA ht.le Z).2.2
  rw [norm_smul, Real.norm_of_nonneg ht.le] at h
  rw [sylvesterFlow_lyapunov, mul_zero, Real.exp_zero, mul_one, div_mul_eq_mul_div,
    le_div_iff₀ ht]
  linarith

omit [DecidableEq m] in
/-- The equation `Ẋ = AX + XAᵀ + G` written with the Lyapunov operator, as used by the abstract
results. -/
private lemma odeSolution_lyapunov {A : Matrix m m ℝ} {G : ℝ → Matrix m m ℝ → Matrix m m ℝ}
    {X : ℝ → Matrix m m ℝ} {a b : ℝ}
    (hX : ODESolution (fun t X => A * X + X * Aᵀ + G t X) X a b) :
    ODESolution (fun t x => (Frobenius.leftMulCLM A + Frobenius.rightMulCLM Aᵀ :
      Matrix m m ℝ →L[ℝ] Matrix m m ℝ) x + G t x) X a b :=
  ⟨hX.cont, fun t ht => by simpa using hX.deriv t ht⟩

/-- **arXiv 1803.10473, Proposition 1, matrix form.** For `Ẋ = AX + XAᵀ + G(t, X)` on real
`m × m` matrices with the Frobenius norm, Assumption 1(a) as printed, (10)
`‖e^{tA} Z e^{tAᵀ}‖ ≤ e^{tω} ‖Z‖` and (11) `‖e^{tA}(AZ + ZAᵀ)e^{tAᵀ}‖ ≤ (C_s / t) e^{tω} ‖Z‖`
for `t > 0`, and the hypotheses on `G` and `X` of `fullRank_lieTrotter_error`, the full-rank
Lie–Trotter splitting `Zₖ₊₁ = e^{τA} Φ^G_τ(Zₖ) e^{τAᵀ}`, `Z₀ = X(t₀)`, satisfies
`‖X(t₀ + n τ) - Zₙ‖ ≤ C τ (1 + |log τ|)` for `n ≤ N`, `N τ ≤ T`. -/
theorem fullRank_lieTrotter_error_matrix {A : Matrix m m ℝ}
    {G : ℝ → Matrix m m ℝ → Matrix m m ℝ} {ω Cs L B Lt Kx τ t₀ T : ℝ}
    (h10 : ∀ t > 0, ∀ Z : Matrix m m ℝ, ‖sylvesterFlow A A t Z‖ ≤ Real.exp (t * ω) * ‖Z‖)
    (h11 : ∀ t > 0, ∀ Z : Matrix m m ℝ,
      ‖sylvesterFlow A A t (A * Z + Z * Aᵀ)‖ ≤ Cs / t * Real.exp (t * ω) * ‖Z‖)
    (hCs : 0 < Cs) (hG : IsLipschitzField G L) (hL : 0 ≤ L) (hB : IsBoundedField G B)
    (hGt : ∀ s t X, ‖G s X - G t X‖ ≤ Lt * |s - t|) (hLt : 0 ≤ Lt) (hKx : 0 ≤ Kx)
    (hτ : 0 < τ) {N : ℕ} (hNT : (N : ℝ) * τ ≤ T) {X : ℝ → Matrix m m ℝ}
    (hX : ODESolution (fun t X => A * X + X * Aᵀ + G t X) X t₀ (t₀ + N * τ))
    (hXreg : ∀ s ∈ Icc t₀ (t₀ + N * τ), ∀ t ∈ Icc t₀ (t₀ + N * τ),
      ‖G s (X s) - G t (X t)‖ ≤ Kx * |s - t|)
    {Z : ℕ → Matrix m m ℝ} {V : ℕ → ℝ → Matrix m m ℝ} (hZ0 : Z 0 = X t₀)
    (hV : ∀ k < N, ODESolution G (V k) (t₀ + k * τ) (t₀ + (k + 1) * τ))
    (hV₀ : ∀ k < N, V k (t₀ + k * τ) = Z k)
    (hZ : ∀ k < N, Z (k + 1) = sylvesterFlow A A τ (V k (t₀ + (k + 1) * τ))) :
    ∀ n ≤ N, ‖X (t₀ + n * τ) - Z n‖ ≤
      Real.exp (Real.exp (max ω 0 * T) * L * Real.exp (L * T) * T) *
        (Real.exp (max ω 0 * T) * (T * (Kx + Lt + L * B) + 2 * B + Cs * B * (1 + |Real.log T|)))
        * τ * (1 + |Real.log τ|) :=
  fullRank_lieTrotter_error (𝒜 := Frobenius.leftMulCLM A + Frobenius.rightMulCLM Aᵀ)
    (fun t ht z => by rw [exp_lyapunov_apply A ht.le]; exact h10 t ht z)
    (fun t ht z => by rw [exp_lyapunov_apply A ht.le]; simpa using h11 t ht z)
    hCs hG hL hB hGt hLt hKx hτ hNT (odeSolution_lyapunov hX) hXreg hZ0 hV hV₀
    (fun k hk => by rw [exp_lyapunov_apply A hτ.le]; exact hZ k hk)

/-- **arXiv 1803.10473, Theorem 1, matrix form.** For `Ẋ = AX + XAᵀ + G(t, X)` on real `m × m`
matrices (Frobenius norm), under Assumption 1(a) as printed ((10), (11)) and the hypotheses of
`lowRank_lieTrotter_global_error`, the low-rank Lie–Trotter splitting
`Yₖ₊₁ = e^{τA} Φ̃^G_τ(Yₖ) e^{τAᵀ}` (one projector-splitting step `IsKSLStep` per time step, e.g.
from the factor ODEs via `MatrixKSL.IsStep.isKSLStep`) with `‖X(t₀) - Y₀‖ ≤ δ` satisfies
`‖X(t₀ + n τ) - Yₙ‖ ≤ c₀ τ (1 + |log τ|) + c₁ δ + c₂ ε` for `n ≤ N`, `N τ ≤ T`. For symmetric
negative semidefinite `A`, (10) and (11) hold with `ω = 0`, `C_s = e⁻¹`
(`sylvesterFlow_bound_of_negSemidef`, `sylvesterFlow_smoothing_of_negSemidef`). -/
theorem lowRank_lieTrotter_global_error_matrix {A : Matrix m m ℝ}
    {G : ℝ → Matrix m m ℝ → Matrix m m ℝ} {ω Cs L B Lt Kx ε δ τ t₀ T : ℝ}
    (h10 : ∀ t > 0, ∀ Z : Matrix m m ℝ, ‖sylvesterFlow A A t Z‖ ≤ Real.exp (t * ω) * ‖Z‖)
    (h11 : ∀ t > 0, ∀ Z : Matrix m m ℝ,
      ‖sylvesterFlow A A t (A * Z + Z * Aᵀ)‖ ≤ Cs / t * Real.exp (t * ω) * ‖Z‖)
    (hCs : 0 < Cs) (hG : IsLipschitzField G L) (hL : 0 ≤ L) (hB : IsBoundedField G B)
    (hGt : ∀ s t X, ‖G s X - G t X‖ ≤ Lt * |s - t|) (hLt : 0 ≤ Lt) (hKx : 0 ≤ Kx)
    (hε : 0 ≤ ε) (hτ : 0 < τ) {N : ℕ} (hNT : (N : ℝ) * τ ≤ T) {X : ℝ → Matrix m m ℝ}
    (hX : ODESolution (fun t X => A * X + X * Aᵀ + G t X) X t₀ (t₀ + N * τ))
    (hXreg : ∀ s ∈ Icc t₀ (t₀ + N * τ), ∀ t ∈ Icc t₀ (t₀ + N * τ),
      ‖G s (X s) - G t (X t)‖ ≤ Kx * |s - t|)
    {Y : ℕ → Matrix m m ℝ} {P Q : ℕ → Matrix m m ℝ →L[ℝ] Matrix m m ℝ}
    {YK YS YL : ℕ → ℝ → Matrix m m ℝ}
    (hstep : ∀ k < N, IsKSLStep G ε (P k) (Q k) (t₀ + k * τ) (t₀ + (k + 1) * τ) (Y k) (YK k)
      (YS k) (YL k))
    (hY : ∀ k < N, Y (k + 1) = sylvesterFlow A A τ (YL k (t₀ + (k + 1) * τ)))
    (hδ : ‖X t₀ - Y 0‖ ≤ δ) :
    ∀ n ≤ N, ‖X (t₀ + n * τ) - Y n‖ ≤
      (Real.exp (Real.exp (max ω 0 * T) * L * Real.exp (L * T) * T) *
          (Real.exp (max ω 0 * T) * (T * (Kx + Lt + L * B) + 2 * B + Cs * B * (1 + |Real.log T|)))
        + 11 * L * B * T * Real.exp ((L + max ω 0) * T)) * τ * (1 + |Real.log τ|)
        + Real.exp ((L + max ω 0) * T) * δ + T * Real.exp ((L + max ω 0) * T) * ε :=
  lowRank_lieTrotter_global_error (𝒜 := Frobenius.leftMulCLM A + Frobenius.rightMulCLM Aᵀ)
    (fun t ht z => by rw [exp_lyapunov_apply A ht.le]; exact h10 t ht z)
    (fun t ht z => by rw [exp_lyapunov_apply A ht.le]; simpa using h11 t ht z)
    hCs hG hL hB hGt hLt hKx hε hτ hNT (odeSolution_lyapunov hX) hXreg hstep
    (fun k hk => by rw [exp_lyapunov_apply A hτ.le]; exact hY k hk) hδ

end MatrixForm

/-! ### Satisfiability of the hypotheses -/

section Examples

open LeanDLRA.KSLExample

/-- Non-vacuity of Theorem 1 (and of Proposition 1, whose hypotheses it contains): one step on
`E = ℂ ≅ ℝ²` with `𝒜 = 0` (so (10), (11) hold with `ω = 0`, `C_s = 1`), the constant field
`G ≡ 1 + i` (`L = L_t = K_x = 0`), the exact solution `X(t) = t (1 + i)`, and the KSL step
`KSLExample.isKSLStep` (`ε = 1`). Genuinely stiff operators satisfying (10) and (11) are given by
`sylvesterFlow_bound_of_negSemidef` and `sylvesterFlow_smoothing_of_negSemidef`. -/
example := lowRank_lieTrotter_global_error (E := ℂ) (𝒜 := 0)
    (G := fun _ _ => 1 + Complex.I) (ω := 0) (Cs := 1) (L := 0) (B := ‖1 + Complex.I‖) (Lt := 0)
    (Kx := 0) (ε := 1) (δ := 0) (τ := 1) (t₀ := 0) (T := 1) (N := 1)
    (X := fun t => 0 + (t : ℂ) * (1 + Complex.I)) (Y := fun k => if k = 0 then 0 else 1)
    (P := fun _ => reProj) (Q := fun _ => reProj) (YK := fun _ t => 0 + (t : ℂ) * 1)
    (YS := fun _ t => 1 + (t : ℂ) * (-1)) (YL := fun _ t => 0 + (t : ℂ) * 1)
    (fun t _ z => by simp)
    (fun t ht z => by
      simp only [smul_zero, NormedSpace.exp_zero, zero_apply, map_zero,
        norm_zero]
      exact mul_nonneg (mul_nonneg (div_nonneg zero_le_one ht.le) (Real.exp_pos _).le)
        (norm_nonneg _))
    one_pos (fun _ _ _ => by simp) le_rfl (fun _ _ => le_rfl) (fun _ _ _ => by simp) le_rfl
    le_rfl zero_le_one one_pos (by norm_num)
    (odeSolution_affine (fun _ _ => by simp) _ _ _) (fun _ _ _ _ => by simp)
    (fun k hk => by rw [Nat.lt_one_iff.1 hk]; simpa using isKSLStep)
    (fun k hk => by rw [Nat.lt_one_iff.1 hk]; simp) (by simp)

end Examples

end LeanDLRA.Literature.P1803_10473
