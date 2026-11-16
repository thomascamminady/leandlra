import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Integrators.TuckerBUG

/-!
# Midpoint and trapezoidal BUG: interior capture and quadrature defects

Robust **second-order** building blocks for the midpoint BUG integrator of
Ceruti–Einkemmer–Kusch–Lubich (arXiv 2402.08607, Algorithm 1 (4r) and Remark 5 (3r)) and its
trapezoidal variant (arXiv 2402.08607, Remark 2), in the abstract projector framework of
`LeanDLRA` (`IsOrthProj`, `ODESolution`, `IsLipschitzField`).

## Main results

* `galerkin_step_error_interior` (OP-HO-11 (a), fully proved; this is the statement
  `galerkin_step_error_of_interior`):
  if `R` captures the exact solution to `ρ` on the whole step and to `θ` at the endpoint, the
  Galerkin S-step started at `R A(t₀)` has error `≤ (e^{L h} - 1) ρ + θ`.  This generalizes the
  certified endpoint-only `galerkin_step_error` (the case `ρ = B h + θ`).
* `norm_taylor_one_le`, `norm_taylor_two_le`: vector-valued Taylor remainders of order one and
  two from one-sided derivatives.
* `interior_capture`: if `R` fixes `A(t₀)`, `‖(1 - R) A(t₁)‖ ≤ θ` and `t ↦ F(t, A t)` has a
  derivative bounded by `M₂`, then `‖(1 - R) A(t)‖ ≤ θ + M₂ h²` on the whole step: the `p = 2`
  case of the interior-capture problem OP-HO-11 (b).
* `midpoint_defect_le`, `trapezoid_defect_le`: quadrature defects of the exact solution from a
  bound `M` on its third derivative, with constants `7/24` and `5/12` (OP-HO-03: an explicit
  hypothesis on the exact solution replaces "`F ∈ C^p`" on the substep flows).
* `exact_second_deriv`, `projected_trajectory_second_deriv` (OP-HO-03, case `k = 1`): for
  `y' = R F(t, y)` with a contraction `R`, `‖∂ₜF‖ ≤ Mₜ`, `‖∂ₓF‖ ≤ M₁` and `‖F‖ ≤ B`, the
  second derivative of `y` exists and is bounded by `Mₜ + M₁ B`, independently of singular
  values.
* `quadrature_capture`: abstract capture lemma for a quadrature rule
  `A(t₁) ≈ A(t₀) + ∑ⱼ wⱼ F(sⱼ, Xⱼ)` whose nodes are captured by `R` up to predictor errors `ηⱼ`
  and normal components `εⱼ`.
* `midpoint_galerkin_local_error` (OP-HO-02, Galerkin core of arXiv 2402.08607, Theorem 1):
  `‖YS t₁ - A t₁‖ ≤ (e^{L h} - 1)(θ + M₂ h²) + θ` with `θ = q + h (L η + ε')`, where `q` is the
  midpoint defect, `η` the error of the half-step predictor and `ε'` the normal component of
  `F` at the predictor.  With `q = O(h³)` and `η = O(h (h + ε))` (first-order BUG half step)
  this is `O(h (h² + h ε + ε'))`, robust in the singular values.
* `trapezoid_galerkin_local_error` (OP-HO-08): the same for the trapezoidal variant with two
  captured nodes, `θ = q + (h/2)(ε₀ + L η + ε₁)`.
* `norm_sub_apply_apply_le_normal`: the doubly-normal estimate
  `‖x - P Q x‖ ≤ ‖(1 - p)(1 - q) x‖` for augmented bases that contain the old ones.

* `midpoint_defect_le_sharp`, `trapezoid_defect_le_sharp`: the sharp constants `1/24`, `1/12`
  (symmetric expansion around the midpoint).
* `midpointGalerkin_local_error`, `trapezoidalGalerkin_local_error`: the local error bounds
  (hypotheses `ContDiffOn ℝ 3 A`, `‖iteratedDerivWithin 3 A‖ ≤ M₃`,
  time-Lipschitz `F`), fully proved.
* `IsMidpointBUGStep` and `IsMidpointBUGStep.local_error_le`
  (arXiv 2402.08607, Thm 1, 4r variant; OP-HO-02 Claim 1): robust local error
  `≤ C h (h² + h ε + ε₂) + ϑ` with an explicit `C = midpointBUGConst` depending only on
  `L, Lₜ, B, M₃, H`.  The half step is any `IsBUGStep` (fixed-rank or augmented), so the same
  theorem covers the 3r variant of Remark 5 (Claim 2 of OP-HO-02) whenever its enlarged bases
  satisfy `fix` and `normal`.

## What is not claimed

Endpoint-only interior bounds for order `p ≥ 4` (OP-HO-11 (b)) are not claimed here.
The global second-order error bound with explicit constants, for `F` of class `C²` with bounded
first and second derivatives, is `midpointBUG_global_error_le` in
`LeanDLRA.HighOrder.MidpointBUGGlobal`. Still open: a bundled trapezoidal BUG step, and the
Tucker versions (arXiv 2610.11747, Lemmas 3.4 and 3.7 with mode projectors).
-/

open Set LeanDLRA

namespace LeanDLRA.MidpointBUG

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Interior

variable {F : ℝ → E → E} {L : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

/-- **Galerkin step with interior and endpoint capture** (OP-HO-11 (a); arXiv 2608.27749,
Thm 1 (b); arXiv 2610.11747, Remark 4.2).  If `R` captures the exact solution to `ρ` on
`[t₀, t₁]` and to `θ` at `t₁`, the Galerkin S-step `YS' = R F(t, YS)`, `YS t₀ = R A(t₀)`, has
error `≤ (e^{L h} - 1) ρ + θ`.  Proof: Grönwall comparison of `YS` with `R A`, whose defect is
`‖R (F(A) - F(R A))‖ ≤ L ρ`.  Fully proved; `galerkin_step_error_of_interior`
had exactly this statement. -/
theorem galerkin_step_error_interior {R : E →L[ℝ] E} (hR : IsOrthProj R)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) {YS : ℝ → E}
    (hS : ODESolution (fun t x => R (F t x)) YS t₀ t₁) (hS₀ : YS t₀ = R (A t₀)) {ρ θ : ℝ}
    (hρ : ∀ t ∈ Icc t₀ t₁, ‖A t - R (A t)‖ ≤ ρ) (hθ : ‖A t₁ - R (A t₁)‖ ≤ θ) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * ρ + θ := by
  have hle : t₀ ≤ t₁ := by linarith
  have hfL : IsLipschitzField (fun t x => R (F t x)) L := hF.comp_contraction R hR.norm_le
  have hZc : ContinuousOn (fun t => R (A t)) (Icc t₀ t₁) :=
    R.continuous.comp_continuousOn hA.cont
  have hZd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => R (A t)) (R (F t (A t))) (Ici t) t :=
    fun t ht => R.hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht)
  have hdef : ∀ t ∈ Ico t₀ t₁, ‖R (F t (A t)) - R (F t (R (A t)))‖ ≤ L * ρ := by
    intro t ht
    calc ‖R (F t (A t)) - R (F t (R (A t)))‖ ≤ L * ‖A t - R (A t)‖ := hfL t _ _
      _ ≤ L * ρ := mul_le_mul_of_nonneg_left (hρ t (Ico_subset_Icc_self ht)) hL
  have hgr := norm_sub_le_gronwallBound hfL hL (y := YS) (z := fun t => R (A t))
    (u := fun t => R (F t (YS t))) (w := fun t => R (F t (A t))) (ηy := 0)
    (ηz := L * ρ) (δ := 0) hS.cont hS.deriv (fun _ _ => by simp) hZc hZd hdef
    (by simp [hS₀]) t₁ ⟨hle, le_rfl⟩
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [zero_add, hlen, gronwallBound_zero_mul] at hgr
  calc ‖YS t₁ - A t₁‖ ≤ ‖YS t₁ - R (A t₁)‖ + ‖R (A t₁) - A t₁‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (Real.exp (L * h) - 1) * ρ + θ := by
        rw [norm_sub_rev (R (A t₁))]
        exact add_le_add hgr hθ

end Interior

section Taylor

/-- First-order vector-valued Taylor remainder from right derivatives:
`‖g t - g a - (t - a) g₁ a‖ ≤ M (t - a)² / 2` if `‖g₂‖ ≤ M`. -/
theorem norm_taylor_one_le {g g₁ g₂ : ℝ → E} {a b M : ℝ}
    (hg : ContinuousOn g (Icc a b)) (hg' : ∀ s ∈ Ico a b, HasDerivWithinAt g (g₁ s) (Ici s) s)
    (hg₁ : ContinuousOn g₁ (Icc a b))
    (hg₁' : ∀ s ∈ Ico a b, HasDerivWithinAt g₁ (g₂ s) (Ici s) s)
    (hM : ∀ s ∈ Ico a b, ‖g₂ s‖ ≤ M) :
    ∀ t ∈ Icc a b, ‖g t - g a - (t - a) • g₁ a‖ ≤ M * (t - a) ^ 2 / 2 := by
  have h1 := norm_image_sub_le_of_norm_deriv_right_le_segment hg₁ hg₁' hM
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun t => g t - g a - (t - a) • g₁ a) (f' := fun s => g₁ s - g₁ a)
    (B := fun t => M * (t - a) ^ 2 / 2) (B' := fun t => M * (t - a)) ?_ ?_ ?_ ?_ ?_
  · exact (hg.sub continuousOn_const).sub
      ((continuousOn_id.sub continuousOn_const).smul continuousOn_const)
  · intro s hs
    have : HasDerivWithinAt (fun t => g t - g a - (t - a) • g₁ a) (g₁ s - (1 : ℝ) • g₁ a)
        (Ici s) s := ((hg' s hs).sub_const (g a)).sub
      (((hasDerivWithinAt_id s (Ici s)).sub_const a).smul_const (g₁ a))
    exact this.congr_deriv (by simp)
  · simp
  · intro t
    have : HasDerivAt (fun t => M * (t - a) ^ 2 / 2) (M * ((2 : ℕ) * (t - a) ^ (2 - 1) * 1) / 2)
        t := (((hasDerivAt_id t).sub_const a).pow 2).const_mul M |>.div_const 2
    exact this.congr_deriv (by push_cast; ring)
  · intro s hs
    exact h1 s (Ico_subset_Icc_self hs)

/-- Second-order vector-valued Taylor remainder from right derivatives:
`‖g t - g a - (t - a) g₁ a - (t - a)²/2 g₂ a‖ ≤ M (t - a)³ / 6` if `‖g₃‖ ≤ M`. -/
theorem norm_taylor_two_le {g g₁ g₂ g₃ : ℝ → E} {a b M : ℝ}
    (hg : ContinuousOn g (Icc a b)) (hg' : ∀ s ∈ Ico a b, HasDerivWithinAt g (g₁ s) (Ici s) s)
    (hg₁ : ContinuousOn g₁ (Icc a b))
    (hg₁' : ∀ s ∈ Ico a b, HasDerivWithinAt g₁ (g₂ s) (Ici s) s)
    (hg₂ : ContinuousOn g₂ (Icc a b))
    (hg₂' : ∀ s ∈ Ico a b, HasDerivWithinAt g₂ (g₃ s) (Ici s) s)
    (hM : ∀ s ∈ Ico a b, ‖g₃ s‖ ≤ M) :
    ∀ t ∈ Icc a b, ‖g t - g a - (t - a) • g₁ a - ((t - a) ^ 2 / 2) • g₂ a‖
      ≤ M * (t - a) ^ 3 / 6 := by
  have h1 := norm_taylor_one_le hg₁ hg₁' hg₂ hg₂' hM
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun t => g t - g a - (t - a) • g₁ a - ((t - a) ^ 2 / 2) • g₂ a)
    (f' := fun s => g₁ s - g₁ a - (s - a) • g₂ a)
    (B := fun t => M * (t - a) ^ 3 / 6) (B' := fun t => M * (t - a) ^ 2 / 2) ?_ ?_ ?_ ?_ ?_
  · exact ((hg.sub continuousOn_const).sub
      ((continuousOn_id.sub continuousOn_const).smul continuousOn_const)).sub
      ((((continuousOn_id.sub continuousOn_const).pow 2).div_const 2).smul continuousOn_const)
  · intro s hs
    have hq : HasDerivWithinAt (fun t : ℝ => (t - a) ^ 2 / 2)
        (((2 : ℕ) * (s - a) ^ (2 - 1) * 1) / 2) (Ici s) s :=
      (((hasDerivWithinAt_id s (Ici s)).sub_const a).pow 2).div_const 2
    have : HasDerivWithinAt (fun t => g t - g a - (t - a) • g₁ a - ((t - a) ^ 2 / 2) • g₂ a)
        (g₁ s - (1 : ℝ) • g₁ a - (((2 : ℕ) * (s - a) ^ (2 - 1) * 1) / 2) • g₂ a) (Ici s) s :=
      (((hg' s hs).sub_const (g a)).sub
        (((hasDerivWithinAt_id s (Ici s)).sub_const a).smul_const (g₁ a))).sub
        (hq.smul_const (g₂ a))
    have e : (((2 : ℕ) : ℝ) * (s - a) ^ (2 - 1) * 1) / 2 = s - a := by push_cast; ring
    exact this.congr_deriv (by rw [e, one_smul])
  · simp
  · intro t
    have : HasDerivAt (fun t => M * (t - a) ^ 3 / 6) (M * ((3 : ℕ) * (t - a) ^ (3 - 1) * 1) / 6)
        t := (((hasDerivAt_id t).sub_const a).pow 3).const_mul M |>.div_const 6
    exact this.congr_deriv (by push_cast; ring)
  · intro s hs
    exact h1 s (Ico_subset_Icc_self hs)

/-- A function vanishing at `t₀`, of size `≤ θ` at `t₁ = t₀ + h` and with second derivative
bounded by `M` is bounded by `θ + M h²` on the whole step (interpolation between the endpoint
bound and the second-order Taylor remainder). -/
theorem norm_le_of_second_deriv {g g₁ g₂ : ℝ → E} {t₀ t₁ h M θ : ℝ} (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hg : ContinuousOn g (Icc t₀ t₁))
    (hg' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt g (g₁ s) (Ici s) s)
    (hg₁ : ContinuousOn g₁ (Icc t₀ t₁))
    (hg₁' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt g₁ (g₂ s) (Ici s) s)
    (hM : ∀ s ∈ Ico t₀ t₁, ‖g₂ s‖ ≤ M) (h0 : g t₀ = 0) (hθ : ‖g t₁‖ ≤ θ) :
    ∀ t ∈ Icc t₀ t₁, ‖g t‖ ≤ θ + M * h ^ 2 := by
  intro t ht
  have hT := norm_taylor_one_le hg hg' hg₁ hg₁' hM
  have hθ0 : 0 ≤ θ := (norm_nonneg _).trans hθ
  rcases hh.eq_or_lt with rfl | hpos
  · have htt : t = t₀ := le_antisymm (by linarith [ht.2]) ht.1
    rw [htt, h0, norm_zero]
    simpa using hθ0
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM t₀ ⟨le_rfl, by linarith⟩)
  have h1 := hT t₁ ⟨by linarith, le_rfl⟩
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [h0, sub_zero, hlen] at h1
  have hv : h * ‖g₁ t₀‖ ≤ θ + M * h ^ 2 / 2 := by
    have hdec : h • g₁ t₀ = g t₁ - (g t₁ - h • g₁ t₀) := by abel
    have := norm_sub_le (g t₁) (g t₁ - h • g₁ t₀)
    rw [← hdec, norm_smul, Real.norm_of_nonneg hh] at this
    linarith
  have h2 := hT t ht
  rw [h0, sub_zero] at h2
  have hτ0 : 0 ≤ t - t₀ := by linarith [ht.1]
  have hτh : t - t₀ ≤ h := by linarith [ht.2]
  have hw : (t - t₀) * ‖g₁ t₀‖ ≤ θ + M * h ^ 2 / 2 := by
    have hX : 0 ≤ θ + M * h ^ 2 / 2 := by positivity
    have : h * ((t - t₀) * ‖g₁ t₀‖) ≤ h * (θ + M * h ^ 2 / 2) := by
      calc h * ((t - t₀) * ‖g₁ t₀‖) = (t - t₀) * (h * ‖g₁ t₀‖) := by ring
        _ ≤ (t - t₀) * (θ + M * h ^ 2 / 2) := mul_le_mul_of_nonneg_left hv hτ0
        _ ≤ h * (θ + M * h ^ 2 / 2) := mul_le_mul_of_nonneg_right hτh hX
    exact le_of_mul_le_mul_left this hpos
  have hsq : (t - t₀) ^ 2 ≤ h ^ 2 := pow_le_pow_left₀ hτ0 hτh 2
  have hdec : g t = (t - t₀) • g₁ t₀ + (g t - (t - t₀) • g₁ t₀) := by abel
  rw [hdec]
  calc _ ≤ ‖(t - t₀) • g₁ t₀‖ + ‖g t - (t - t₀) • g₁ t₀‖ := norm_add_le _ _
    _ ≤ (t - t₀) * ‖g₁ t₀‖ + M * (t - t₀) ^ 2 / 2 := by
        rw [norm_smul, Real.norm_of_nonneg hτ0]; linarith
    _ ≤ θ + M * h ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hsq hM0]

end Taylor

/-! ### Quadrature capture -/

section Capture

variable {F : ℝ → E → E} {L : ℝ}

/-- **Capture by a quadrature rule.**  If `R` fixes `x₀`, `x - x₀` is approximated by the
quadrature `∑ⱼ wⱼ F(sⱼ, Xⱼ)` up to `q`, the nodes `Xⱼ` are approximated by predictors `Zⱼ` up
to `ηⱼ` and `R` captures `F(sⱼ, Zⱼ)` up to `εⱼ`, then `‖x - R x‖ ≤ q + ∑ⱼ |wⱼ| (L ηⱼ + εⱼ)`.
This is the endpoint-capture step of the robust midpoint and trapezoidal BUG proofs
(arXiv 2402.08607, proof of Thm 1 and Remark 2). -/
theorem quadrature_capture {R : E →L[ℝ] E} (hR : IsOrthProj R) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) {x₀ x : E} (hx₀ : R x₀ = x₀) {k : ℕ} (s w : Fin k → ℝ) (X Z : Fin k → E)
    {q : ℝ} (hq : ‖x - x₀ - ∑ j, w j • F (s j) (X j)‖ ≤ q) {η ε : Fin k → ℝ}
    (hη : ∀ j, ‖X j - Z j‖ ≤ η j) (hε : ∀ j, ‖F (s j) (Z j) - R (F (s j) (Z j))‖ ≤ ε j) :
    ‖x - R x‖ ≤ q + ∑ j, |w j| * (L * η j + ε j) := by
  set T : E →L[ℝ] E := 1 - R with hTdef
  have hT : ∀ y, T y = y - R y := fun y => by simp [hTdef]
  have hTn : ∀ y, ‖T y‖ ≤ ‖y‖ := hR.compl.norm_le
  set S := ∑ j, w j • F (s j) (X j) with hS
  have hsplit : x - R x = T (x - x₀ - S) + ∑ j, w j • T (F (s j) (X j)) := by
    have hTS : T S = ∑ j, w j • T (F (s j) (X j)) := by
      rw [hS, map_sum]; simp only [map_smul]
    rw [← hTS, ← map_add, sub_add_cancel, map_sub, hT x, hT x₀, hx₀, sub_self, sub_zero]
  have hj : ∀ j, ‖T (F (s j) (X j))‖ ≤ L * η j + ε j := by
    intro j
    have hdec : T (F (s j) (X j)) = T (F (s j) (X j) - F (s j) (Z j)) + T (F (s j) (Z j)) := by
      rw [← map_add, sub_add_cancel]
    rw [hdec]
    calc _ ≤ ‖T (F (s j) (X j) - F (s j) (Z j))‖ + ‖T (F (s j) (Z j))‖ := norm_add_le _ _
      _ ≤ ‖F (s j) (X j) - F (s j) (Z j)‖ + ‖F (s j) (Z j) - R (F (s j) (Z j))‖ :=
          add_le_add (hTn _) (by rw [hT])
      _ ≤ L * ‖X j - Z j‖ + ε j := add_le_add (hF _ _ _) (hε j)
      _ ≤ L * η j + ε j := by gcongr; exact hη j
  rw [hsplit]
  calc _ ≤ ‖T (x - x₀ - S)‖ + ‖∑ j, w j • T (F (s j) (X j))‖ := norm_add_le _ _
    _ ≤ q + ∑ j, |w j| * (L * η j + ε j) := by
        refine add_le_add ((hTn _).trans hq) ((norm_sum_le _ _).trans ?_)
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hj j) (abs_nonneg _)

/-- **Doubly normal component for augmented bases.**  If the new projectors `P, Q` contain the
old ones `p, q` (`P p = p`, `Q q = q`) and capture `q x`, `p x` respectively, then
`‖x - P Q x‖ ≤ ‖(1 - p)(1 - q) x‖`: only the doubly normal part of `x` is lost
(arXiv 2402.08607, Algorithm 1, bases `[U₀, U_{1/2}, F V_{1/2}]`). -/
theorem norm_sub_apply_apply_le_normal {P Q p q : E →L[ℝ] E} (hPQ : IsOrthProj (P * Q))
    (hpq : ∀ z, p (q z) = q (p z)) (hPp : ∀ z, P (p z) = p z) (hQq : ∀ z, Q (q z) = q z)
    {x : E} (hPx : P (q x) = q x) (hQx : Q (p x) = p x) :
    ‖x - P (Q x)‖ ≤ ‖(1 - p) ((1 - q) x)‖ := by
  set y := (1 - p) ((1 - q) x) with hy
  have hxy : x - y = q x + p x - p (q x) := by
    rw [hy]; simp only [sub_apply, one_apply_eq_self, map_sub]
    abel
  have e1 : P (Q (q x)) = q x := by rw [hQq, hPx]
  have e2 : P (Q (p x)) = p x := by rw [hQx, hPp]
  have e3 : P (Q (p (q x))) = p (q x) := by rw [hpq x, hQq, ← hpq x, hPp]
  have hfix : P (Q (x - y)) = x - y := by
    rw [hxy, map_sub, map_add, map_sub, map_add, e1, e2, e3]
  have hPQx : P (Q x) = P (Q y) + (x - y) := by
    rw [← hfix, map_sub, map_sub]; abel
  have : x - P (Q x) = y - P (Q y) := by rw [hPQx]; abel
  rw [this]
  exact hPQ.norm_sub_le y

end Capture

/-! ### Second derivatives along (projected) trajectories -/

section SecondDeriv

variable {F : ℝ → E → E}

/-- Continuity of `t ↦ F(t, y t)` along a continuous trajectory for a jointly differentiable
field. -/
theorem continuousOn_field_comp {D : ℝ → E → (ℝ × E) →L[ℝ] E}
    (hD : ∀ t x, HasFDerivAt (fun p : ℝ × E => F p.1 p.2) (D t x) (t, x)) {y : ℝ → E}
    {a b : ℝ} (hy : ContinuousOn y (Icc a b)) : ContinuousOn (fun t => F t (y t)) (Icc a b) := by
  have hc : Continuous (fun p : ℝ × E => F p.1 p.2) :=
    continuous_iff_continuousAt.2 fun p => (hD p.1 p.2).continuousAt
  exact hc.comp_continuousOn (continuousOn_id.prodMk hy)

/-- Chain rule for `t ↦ F(t, y t)`: its derivative is `DF(t, y t)(1, y' t)`. -/
theorem hasDerivWithinAt_field_comp {D : ℝ → E → (ℝ × E) →L[ℝ] E}
    (hD : ∀ t x, HasFDerivAt (fun p : ℝ × E => F p.1 p.2) (D t x) (t, x)) {y v : ℝ → E}
    {s : ℝ} {U : Set ℝ} (hy : HasDerivWithinAt y (v s) U s) :
    HasDerivWithinAt (fun t => F t (y t)) (D s (y s) (1, v s)) U s := by
  have h1 : HasDerivWithinAt (fun t : ℝ => (t, y t)) ((1 : ℝ), v s) U s :=
    (hasDerivWithinAt_id s U).prodMk hy
  exact (hD s (y s)).comp_hasDerivWithinAt (f := fun t : ℝ => (t, y t)) s h1

/-- `‖DF(t, x)(1, v)‖ ≤ Mₜ + M₁ B` from `‖∂ₜF‖ ≤ Mₜ`, `‖∂ₓF‖ ≤ M₁` and `‖v‖ ≤ B`. -/
theorem norm_fderiv_one_le {D : ℝ → E → (ℝ × E) →L[ℝ] E} {Mt M₁ B : ℝ}
    (hDt : ∀ t x, ‖D t x (1, 0)‖ ≤ Mt) (hDx : ∀ t x v, ‖D t x (0, v)‖ ≤ M₁ * ‖v‖)
    (hM₁ : 0 ≤ M₁) (t : ℝ) (x : E) {v : E} (hv : ‖v‖ ≤ B) : ‖D t x (1, v)‖ ≤ Mt + M₁ * B := by
  have : ((1 : ℝ), v) = (1, 0) + (0, v) := by simp
  rw [this, map_add]
  calc _ ≤ ‖D t x (1, 0)‖ + ‖D t x (0, v)‖ := norm_add_le _ _
    _ ≤ Mt + M₁ * ‖v‖ := add_le_add (hDt t x) (hDx t x v)
    _ ≤ Mt + M₁ * B := by gcongr

/-- **Singular-value-free second derivative of projected flows** (OP-HO-03, case `k = 1`;
cf. arXiv 2608.17157, Lemma 6.2).  If `y' = R F(t, y)` with a contraction `R` (exact flow,
K-, L- or S-substep), `‖∂ₜF‖ ≤ Mₜ`, `‖∂ₓF‖ ≤ M₁` and `‖F‖ ≤ B`, then `t ↦ R F(t, y t)` (that is,
`y'`) is differentiable from the right with derivative bounded by `Mₜ + M₁ B`.  The general
`k`-th derivative (Faà di Bruno) remains open. -/
theorem projected_trajectory_second_deriv {D : ℝ → E → (ℝ × E) →L[ℝ] E}
    (hD : ∀ t x, HasFDerivAt (fun p : ℝ × E => F p.1 p.2) (D t x) (t, x)) {Mt M₁ B : ℝ}
    (hDt : ∀ t x, ‖D t x (1, 0)‖ ≤ Mt) (hDx : ∀ t x v, ‖D t x (0, v)‖ ≤ M₁ * ‖v‖)
    (hM₁ : 0 ≤ M₁) (hB : IsBoundedField F B) {R : E →L[ℝ] E} (hR : ∀ x, ‖R x‖ ≤ ‖x‖)
    {y : ℝ → E} {a b : ℝ} (hy : ODESolution (fun t x => R (F t x)) y a b) :
    ContinuousOn (fun t => R (F t (y t))) (Icc a b) ∧
    ∀ s ∈ Ico a b,
      HasDerivWithinAt (fun t => R (F t (y t))) (R (D s (y s) (1, R (F s (y s))))) (Ici s) s ∧
      ‖R (D s (y s) (1, R (F s (y s))))‖ ≤ Mt + M₁ * B := by
  refine ⟨R.continuous.comp_continuousOn (continuousOn_field_comp hD hy.cont), fun s hs => ⟨?_, ?_⟩⟩
  · exact R.hasFDerivAt.comp_hasDerivWithinAt s
      (hasDerivWithinAt_field_comp hD (v := fun t => R (F t (y t))) (hy.deriv s hs))
  · exact (hR _).trans (norm_fderiv_one_le hDt hDx hM₁ s (y s) ((hR _).trans (hB s (y s))))

/-- The exact-flow case `R = 1` of `projected_trajectory_second_deriv`:
`‖A''‖ ≤ Mₜ + M₁ B` (OP-HO-03, case `k = 1`). -/
theorem exact_second_deriv {D : ℝ → E → (ℝ × E) →L[ℝ] E}
    (hD : ∀ t x, HasFDerivAt (fun p : ℝ × E => F p.1 p.2) (D t x) (t, x)) {Mt M₁ B : ℝ}
    (hDt : ∀ t x, ‖D t x (1, 0)‖ ≤ Mt) (hDx : ∀ t x v, ‖D t x (0, v)‖ ≤ M₁ * ‖v‖)
    (hM₁ : 0 ≤ M₁) (hB : IsBoundedField F B) {A : ℝ → E} {a b : ℝ} (hA : ODESolution F A a b) :
    ContinuousOn (fun t => F t (A t)) (Icc a b) ∧
    ∀ s ∈ Ico a b,
      HasDerivWithinAt (fun t => F t (A t)) (D s (A s) (1, F s (A s))) (Ici s) s ∧
      ‖D s (A s) (1, F s (A s))‖ ≤ Mt + M₁ * B :=
  ⟨continuousOn_field_comp hD hA.cont, fun s hs =>
    ⟨hasDerivWithinAt_field_comp hD (v := fun t => F t (A t)) (hA.deriv s hs),
      norm_fderiv_one_le hDt hDx hM₁ s (A s) (hB s (A s))⟩⟩

end SecondDeriv

/-! ### Interior capture and the quadrature defects -/

section Quadrature

/-- **Interior capture from endpoint capture** (OP-HO-11 (b), case `p = 2`).  If `R` fixes
`A(t₀)`, captures `A(t₁)` up to `θ`, and `t ↦ F(t, A t)` has derivative bounded by `M₂`, then
`‖(1 - R) A(t)‖ ≤ θ + M₂ h²` for all `t ∈ [t₀, t₁]`.  Uses no information on `R` beyond being
an orthogonal projector; for `p ≥ 4` the analogous statement is false in general and is not
claimed. -/
theorem interior_capture {F : ℝ → E → E} {R : E →L[ℝ] E} (hR : IsOrthProj R) {A : ℝ → E}
    {t₀ t₁ h : ℝ} (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hRA : R (A t₀) = A t₀) {a₂ : ℝ → E} {M₂ : ℝ}
    (ha : ContinuousOn (fun t => F t (A t)) (Icc t₀ t₁))
    (ha' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => F t (A t)) (a₂ s) (Ici s) s)
    (hM₂ : ∀ s ∈ Ico t₀ t₁, ‖a₂ s‖ ≤ M₂) {θ : ℝ} (hθ : ‖A t₁ - R (A t₁)‖ ≤ θ) :
    ∀ t ∈ Icc t₀ t₁, ‖A t - R (A t)‖ ≤ θ + M₂ * h ^ 2 := by
  refine norm_le_of_second_deriv (g := fun t => A t - R (A t))
    (g₁ := fun t => F t (A t) - R (F t (A t))) (g₂ := fun s => a₂ s - R (a₂ s)) ht₁ hh
    ?_ ?_ ?_ ?_ ?_ (by simp [hRA]) hθ
  · exact hA.cont.sub (R.continuous.comp_continuousOn hA.cont)
  · intro s hs
    exact (hA.deriv s hs).sub (R.hasFDerivAt.comp_hasDerivWithinAt s (hA.deriv s hs))
  · exact ha.sub (R.continuous.comp_continuousOn ha)
  · intro s hs
    exact (ha' s hs).sub (R.hasFDerivAt.comp_hasDerivWithinAt s (ha' s hs))
  · intro s hs
    exact (hR.norm_sub_le _).trans (hM₂ s hs)

/-- **Midpoint-rule defect of a `C³` curve** (OP-HO-03, OP-HO-02):
`‖A t₁ - A t₀ - h A'(t₀ + h/2)‖ ≤ 7/24 M h³` if `‖A'''‖ ≤ M`, using one-sided derivatives only.
The sharp constant `1/24` (two-sided derivatives in the interior) is
`midpoint_defect_le_sharp`. -/
theorem midpoint_defect_le {A a a₁ a₂ : ℝ → E} {t₀ t₁ h M : ℝ} (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ContinuousOn A (Icc t₀ t₁))
    (hA' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt A (a s) (Ici s) s)
    (ha : ContinuousOn a (Icc t₀ t₁)) (ha' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt a (a₁ s) (Ici s) s)
    (ha₁ : ContinuousOn a₁ (Icc t₀ t₁))
    (ha₁' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt a₁ (a₂ s) (Ici s) s)
    (hM : ∀ s ∈ Ico t₀ t₁, ‖a₂ s‖ ≤ M) :
    ‖A t₁ - A t₀ - h • a (t₀ + h / 2)‖ ≤ 7 / 24 * M * h ^ 3 := by
  have T2 := norm_taylor_two_le hA hA' ha ha' ha₁ ha₁' hM t₁ ⟨by linarith, le_rfl⟩
  have T1 := norm_taylor_one_le ha ha' ha₁ ha₁' hM (t₀ + h / 2) ⟨by linarith, by linarith⟩
  have e1 : t₁ - t₀ = h := by rw [ht₁]; ring
  have e2 : t₀ + h / 2 - t₀ = h / 2 := by ring
  rw [e1] at T2
  rw [e2] at T1
  have hid : A t₁ - A t₀ - h • a (t₀ + h / 2)
      = (A t₁ - A t₀ - h • a t₀ - (h ^ 2 / 2) • a₁ t₀)
        - h • (a (t₀ + h / 2) - a t₀ - (h / 2) • a₁ t₀) := by
    module
  rw [hid]
  calc _ ≤ ‖A t₁ - A t₀ - h • a t₀ - (h ^ 2 / 2) • a₁ t₀‖
        + ‖h • (a (t₀ + h / 2) - a t₀ - (h / 2) • a₁ t₀)‖ := norm_sub_le _ _
    _ ≤ M * h ^ 3 / 6 + h * (M * (h / 2) ^ 2 / 2) := by
        rw [norm_smul, Real.norm_of_nonneg hh]
        exact add_le_add T2 (mul_le_mul_of_nonneg_left T1 hh)
    _ = 7 / 24 * M * h ^ 3 := by ring

/-- **Trapezoidal-rule defect of a `C³` curve** (OP-HO-03, OP-HO-08):
`‖A t₁ - A t₀ - (h/2)(A' t₀ + A' t₁)‖ ≤ 5/12 M h³` if `‖A'''‖ ≤ M`, using one-sided
derivatives only.  The sharp constant `1/12` is `trapezoid_defect_le_sharp`. -/
theorem trapezoid_defect_le {A a a₁ a₂ : ℝ → E} {t₀ t₁ h M : ℝ} (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ContinuousOn A (Icc t₀ t₁))
    (hA' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt A (a s) (Ici s) s)
    (ha : ContinuousOn a (Icc t₀ t₁)) (ha' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt a (a₁ s) (Ici s) s)
    (ha₁ : ContinuousOn a₁ (Icc t₀ t₁))
    (ha₁' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt a₁ (a₂ s) (Ici s) s)
    (hM : ∀ s ∈ Ico t₀ t₁, ‖a₂ s‖ ≤ M) :
    ‖A t₁ - A t₀ - (h / 2) • (a t₀ + a t₁)‖ ≤ 5 / 12 * M * h ^ 3 := by
  have T2 := norm_taylor_two_le hA hA' ha ha' ha₁ ha₁' hM t₁ ⟨by linarith, le_rfl⟩
  have T1 := norm_taylor_one_le ha ha' ha₁ ha₁' hM t₁ ⟨by linarith, le_rfl⟩
  have e1 : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [e1] at T2 T1
  have hid : A t₁ - A t₀ - (h / 2) • (a t₀ + a t₁)
      = (A t₁ - A t₀ - h • a t₀ - (h ^ 2 / 2) • a₁ t₀)
        - (h / 2) • (a t₁ - a t₀ - h • a₁ t₀) := by
    module
  rw [hid]
  have hh2 : 0 ≤ h / 2 := by linarith
  calc _ ≤ ‖A t₁ - A t₀ - h • a t₀ - (h ^ 2 / 2) • a₁ t₀‖
        + ‖(h / 2) • (a t₁ - a t₀ - h • a₁ t₀)‖ := norm_sub_le _ _
    _ ≤ M * h ^ 3 / 6 + h / 2 * (M * h ^ 2 / 2) := by
        rw [norm_smul, Real.norm_of_nonneg hh2]
        exact add_le_add T2 (mul_le_mul_of_nonneg_left T1 hh2)
    _ = 5 / 12 * M * h ^ 3 := by ring

end Quadrature

/-! ### Midpoint and trapezoidal Galerkin steps -/

section Local

variable {F : ℝ → E → E} {L : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

/-- **Endpoint capture of the midpoint BUG** (arXiv 2402.08607, proof of Thm 1): if `R` fixes
`A(t₀)` and captures `F` at the midpoint predictor `Yh` up to `ε'`, then
`‖(1 - R) A(t₁)‖ ≤ q + h (L η + ε')` where `q` is the midpoint defect and
`η ≥ ‖A(t₀ + h/2) - Yh‖`. -/
theorem midpoint_capture {R : E →L[ℝ] E} (hR : IsOrthProj R) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hh : 0 ≤ h) (hRA : R (A t₀) = A t₀) {q : ℝ}
    (hq : ‖A t₁ - A t₀ - h • F (t₀ + h / 2) (A (t₀ + h / 2))‖ ≤ q) {Yh : E} {η ε' : ℝ}
    (hη : ‖A (t₀ + h / 2) - Yh‖ ≤ η) (hε : ‖F (t₀ + h / 2) Yh - R (F (t₀ + h / 2) Yh)‖ ≤ ε') :
    ‖A t₁ - R (A t₁)‖ ≤ q + h * (L * η + ε') := by
  have := quadrature_capture hR hF hL hRA (fun _ : Fin 1 => t₀ + h / 2) (fun _ => h)
    (fun _ => A (t₀ + h / 2)) (fun _ => Yh) (x := A t₁) (q := q) (η := fun _ => η)
    (ε := fun _ => ε') (by simpa using hq) (fun _ => hη) (fun _ => hε)
  simpa [abs_of_nonneg hh] using this

/-- **Robust local error of the midpoint Galerkin step** (OP-HO-02; arXiv 2402.08607, Thm 1,
4r and 3r variants alike: only the capture of `F` at the predictor enters).  The bound is
`(e^{L h} - 1)(θ + M₂ h²) + θ` with `θ = q + h (L η + ε')`, which is
`O(h³ + h η + h ε')` and does not depend on singular values. -/
theorem midpoint_galerkin_local_error {R : E →L[ℝ] E} (hR : IsOrthProj R)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hRA : R (A t₀) = A t₀) {YS : ℝ → E}
    (hS : ODESolution (fun t x => R (F t x)) YS t₀ t₁) (hS₀ : YS t₀ = A t₀) {q : ℝ}
    (hq : ‖A t₁ - A t₀ - h • F (t₀ + h / 2) (A (t₀ + h / 2))‖ ≤ q) {Yh : E} {η ε' : ℝ}
    (hη : ‖A (t₀ + h / 2) - Yh‖ ≤ η) (hε : ‖F (t₀ + h / 2) Yh - R (F (t₀ + h / 2) Yh)‖ ≤ ε')
    {a₂ : ℝ → E} {M₂ : ℝ} (ha : ContinuousOn (fun t => F t (A t)) (Icc t₀ t₁))
    (ha' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => F t (A t)) (a₂ s) (Ici s) s)
    (hM₂ : ∀ s ∈ Ico t₀ t₁, ‖a₂ s‖ ≤ M₂) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (q + h * (L * η + ε') + M₂ * h ^ 2)
      + (q + h * (L * η + ε')) := by
  have hθ := midpoint_capture hR hF hL hh hRA hq hη hε
  exact galerkin_step_error_interior hR hF hL ht₁ hh hA hS (hS₀.trans hRA.symm)
    (interior_capture hR ht₁ hh hA hRA ha ha' hM₂ hθ) hθ

/-- **Endpoint capture of the trapezoidal BUG** (OP-HO-08; arXiv 2402.08607, Remark 2):
`‖(1 - R) A(t₁)‖ ≤ q + (h/2)(ε₀ + L η + ε₁)`. -/
theorem trapezoid_capture {R : E →L[ℝ] E} (hR : IsOrthProj R) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hh : 0 ≤ h) (hRA : R (A t₀) = A t₀) {q : ℝ}
    (hq : ‖A t₁ - A t₀ - (h / 2) • (F t₀ (A t₀) + F t₁ (A t₁))‖ ≤ q) {Y₁ : E} {η ε₀ ε₁ : ℝ}
    (hη : ‖A t₁ - Y₁‖ ≤ η) (hε₀ : ‖F t₀ (A t₀) - R (F t₀ (A t₀))‖ ≤ ε₀)
    (hε₁ : ‖F t₁ Y₁ - R (F t₁ Y₁)‖ ≤ ε₁) :
    ‖A t₁ - R (A t₁)‖ ≤ q + h / 2 * (ε₀ + L * η + ε₁) := by
  have := quadrature_capture hR hF hL hRA ![t₀, t₁] ![h / 2, h / 2] ![A t₀, A t₁] ![A t₀, Y₁]
    (x := A t₁) (q := q) (η := ![0, η]) (ε := ![ε₀, ε₁]) (by simpa [smul_add] using hq)
    (fun j => by fin_cases j <;> simp [hη]) (fun j => by fin_cases j <;> simp [hε₀, hε₁])
  have hh2 : |h / 2| = h / 2 := abs_of_nonneg (by linarith)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hh2] at this
  linarith

/-- **Robust local error of the trapezoidal Galerkin step** (OP-HO-08; arXiv 2402.08607,
Remark 2, claimed there without proof).  The bound is `(e^{L h} - 1)(θ + M₂ h²) + θ` with
`θ = q + (h/2)(ε₀ + L η + ε₁)`, i.e. `O(h³ + h η + h ε)`. -/
theorem trapezoid_galerkin_local_error {R : E →L[ℝ] E} (hR : IsOrthProj R)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hRA : R (A t₀) = A t₀) {YS : ℝ → E}
    (hS : ODESolution (fun t x => R (F t x)) YS t₀ t₁) (hS₀ : YS t₀ = A t₀) {q : ℝ}
    (hq : ‖A t₁ - A t₀ - (h / 2) • (F t₀ (A t₀) + F t₁ (A t₁))‖ ≤ q) {Y₁ : E} {η ε₀ ε₁ : ℝ}
    (hη : ‖A t₁ - Y₁‖ ≤ η) (hε₀ : ‖F t₀ (A t₀) - R (F t₀ (A t₀))‖ ≤ ε₀)
    (hε₁ : ‖F t₁ Y₁ - R (F t₁ Y₁)‖ ≤ ε₁)
    {a₂ : ℝ → E} {M₂ : ℝ} (ha : ContinuousOn (fun t => F t (A t)) (Icc t₀ t₁))
    (ha' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => F t (A t)) (a₂ s) (Ici s) s)
    (hM₂ : ∀ s ∈ Ico t₀ t₁, ‖a₂ s‖ ≤ M₂) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (q + h / 2 * (ε₀ + L * η + ε₁) + M₂ * h ^ 2)
      + (q + h / 2 * (ε₀ + L * η + ε₁)) := by
  have hθ := trapezoid_capture hR hF hL hh hRA hq hη hε₀ hε₁
  exact galerkin_step_error_interior hR hF hL ht₁ hh hA hS (hS₀.trans hRA.symm)
    (interior_capture hR ht₁ hh hA hRA ha ha' hM₂ hθ) hθ

end Local

/-! ### Sharp quadrature defects and the local error statements -/

section Sharp

/-- Derivatives of `u ↦ f (m + u)` and `u ↦ f (m - u)` on `[0, h/2)` for `m = t₀ + h/2`, from
derivatives of `f` in the open interval `(t₀, t₀ + h)`. -/
theorem hasDerivAt_reflect {f f' : ℝ → E} {t₀ h : ℝ}
    (hf : ∀ x ∈ Ioo t₀ (t₀ + h), HasDerivAt f (f' x) x) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) (h / 2)) :
    HasDerivAt (fun u => f (t₀ + h / 2 + u)) (f' (t₀ + h / 2 + u)) u ∧
      HasDerivAt (fun u => f (t₀ + h / 2 - u)) (-f' (t₀ + h / 2 - u)) u := by
  constructor
  · have := (hf (t₀ + h / 2 + u) ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩).scomp u
      ((hasDerivAt_id' u).const_add (t₀ + h / 2))
    simpa [Function.comp_def] using this
  · have := (hf (t₀ + h / 2 - u) ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩).scomp u
      ((hasDerivAt_id' u).const_sub (t₀ + h / 2))
    simpa [Function.comp_def] using this

/-- **Sharp midpoint-rule defect** (symmetric Taylor expansion around the midpoint): if `A`, `a₁`,
`a₂` are continuous on `[t₀, t₀ + h]`, `A' = a₁`, `a₁' = a₂`, `a₂' = a₃` in the interior and
`‖a₃‖ ≤ M` there, then `‖A(t₀ + h) - A t₀ - h a₁(t₀ + h/2)‖ ≤ M h³ / 24`. -/
theorem midpoint_defect_le_sharp {A a₁ a₂ a₃ : ℝ → E} {t₀ h M : ℝ} (hh : 0 < h)
    (hA : ContinuousOn A (Icc t₀ (t₀ + h))) (ha₁ : ContinuousOn a₁ (Icc t₀ (t₀ + h)))
    (ha₂ : ContinuousOn a₂ (Icc t₀ (t₀ + h)))
    (dA : ∀ x ∈ Ioo t₀ (t₀ + h), HasDerivAt A (a₁ x) x)
    (da₁ : ∀ x ∈ Ioo t₀ (t₀ + h), HasDerivAt a₁ (a₂ x) x)
    (da₂ : ∀ x ∈ Ioo t₀ (t₀ + h), HasDerivAt a₂ (a₃ x) x)
    (hM : ∀ x ∈ Ioo t₀ (t₀ + h), ‖a₃ x‖ ≤ M) :
    ‖A (t₀ + h) - A t₀ - h • a₁ (t₀ + h / 2)‖ ≤ M * h ^ 3 / 24 := by
  set m := t₀ + h / 2 with hm
  have hp : MapsTo (fun u => m + u) (Icc (0 : ℝ) (h / 2)) (Icc t₀ (t₀ + h)) := fun u hu =>
    ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩
  have hn : MapsTo (fun u => m - u) (Icc (0 : ℝ) (h / 2)) (Icc t₀ (t₀ + h)) := fun u hu =>
    ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩
  have cp : ∀ {f : ℝ → E}, ContinuousOn f (Icc t₀ (t₀ + h)) →
      ContinuousOn (fun u => f (m + u)) (Icc 0 (h / 2)) := fun hf =>
    hf.comp (continuousOn_const.add continuousOn_id) hp
  have cn : ∀ {f : ℝ → E}, ContinuousOn f (Icc t₀ (t₀ + h)) →
      ContinuousOn (fun u => f (m - u)) (Icc 0 (h / 2)) := fun hf =>
    hf.comp (continuousOn_const.sub continuousOn_id) hn
  have T := norm_taylor_two_le (g := fun u => A (m + u) - A (m - u))
    (g₁ := fun u => a₁ (m + u) + a₁ (m - u)) (g₂ := fun u => a₂ (m + u) - a₂ (m - u))
    (g₃ := fun u => a₃ (m + u) + a₃ (m - u)) (a := 0) (b := h / 2) (M := 2 * M)
    ((cp hA).sub (cn hA))
    (fun u hu => by
      obtain ⟨h1, h2⟩ := hasDerivAt_reflect dA hu
      exact (h1.sub h2).hasDerivWithinAt.congr_deriv (by rw [sub_neg_eq_add]))
    ((cp ha₁).add (cn ha₁))
    (fun u hu => by
      obtain ⟨h1, h2⟩ := hasDerivAt_reflect da₁ hu
      exact (h1.add h2).hasDerivWithinAt.congr_deriv (by rw [← sub_eq_add_neg]))
    ((cp ha₂).sub (cn ha₂))
    (fun u hu => by
      obtain ⟨h1, h2⟩ := hasDerivAt_reflect da₂ hu
      exact (h1.sub h2).hasDerivWithinAt.congr_deriv (by rw [sub_neg_eq_add]))
    (fun u hu => by
      calc ‖a₃ (m + u) + a₃ (m - u)‖ ≤ ‖a₃ (m + u)‖ + ‖a₃ (m - u)‖ := norm_add_le _ _
        _ ≤ M + M := add_le_add (hM _ ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩)
            (hM _ ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩)
        _ = 2 * M := by ring)
    (h / 2) ⟨by linarith, le_rfl⟩
  have e1 : m + h / 2 = t₀ + h := by rw [hm]; ring
  have e2 : m - h / 2 = t₀ := by rw [hm]; ring
  simp only [add_zero, sub_zero, sub_self, smul_zero, e1, e2] at T
  have hid : A (t₀ + h) - A t₀ - h • a₁ m
      = A (t₀ + h) - A t₀ - (h / 2) • (a₁ m + a₁ m) := by module
  rw [hid]
  calc _ ≤ 2 * M * (h / 2) ^ 3 / 6 := T
    _ = M * h ^ 3 / 24 := by ring

/-- **Sharp trapezoidal-rule defect** (symmetric expansion around the midpoint): under the
hypotheses of `midpoint_defect_le_sharp`,
`‖A(t₀ + h) - A t₀ - (h/2)(a₁ t₀ + a₁(t₀ + h))‖ ≤ M h³ / 12`. -/
theorem trapezoid_defect_le_sharp {A a₁ a₂ a₃ : ℝ → E} {t₀ h M : ℝ} (hh : 0 < h)
    (hA : ContinuousOn A (Icc t₀ (t₀ + h))) (ha₁ : ContinuousOn a₁ (Icc t₀ (t₀ + h)))
    (dA : ∀ x ∈ Ioo t₀ (t₀ + h), HasDerivAt A (a₁ x) x)
    (da₁ : ∀ x ∈ Ioo t₀ (t₀ + h), HasDerivAt a₁ (a₂ x) x)
    (da₂ : ∀ x ∈ Ioo t₀ (t₀ + h), HasDerivAt a₂ (a₃ x) x)
    (hM : ∀ x ∈ Ioo t₀ (t₀ + h), ‖a₃ x‖ ≤ M) :
    ‖A (t₀ + h) - A t₀ - (h / 2) • (a₁ t₀ + a₁ (t₀ + h))‖ ≤ M * h ^ 3 / 12 := by
  set m := t₀ + h / 2 with hm
  have hp : MapsTo (fun u => m + u) (Icc (0 : ℝ) (h / 2)) (Icc t₀ (t₀ + h)) := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hn : MapsTo (fun u => m - u) (Icc (0 : ℝ) (h / 2)) (Icc t₀ (t₀ + h)) := fun u hu =>
    ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have cp : ∀ {f : ℝ → E}, ContinuousOn f (Icc t₀ (t₀ + h)) →
      ContinuousOn (fun u => f (m + u)) (Icc 0 (h / 2)) := fun hf =>
    hf.comp (continuousOn_const.add continuousOn_id) hp
  have cn : ∀ {f : ℝ → E}, ContinuousOn f (Icc t₀ (t₀ + h)) →
      ContinuousOn (fun u => f (m - u)) (Icc 0 (h / 2)) := fun hf =>
    hf.comp (continuousOn_const.sub continuousOn_id) hn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM m ⟨by linarith, by linarith⟩)
  -- `‖a₂(m + u) - a₂(m - u)‖ ≤ 2 M u` by the mean value theorem on `(t₀, t₀ + h)`
  have hmv : ∀ u ∈ Ico (0 : ℝ) (h / 2), ‖a₂ (m + u) - a₂ (m - u)‖ ≤ M * (2 * u) := by
    intro u hu
    have := (convex_Ioo t₀ (t₀ + h)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := a₂) (f' := a₃) (fun x hx => (da₂ x hx).hasDerivWithinAt) hM
      (x := m - u) (y := m + u) ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩
      ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩
    have e : ‖m + u - (m - u)‖ = 2 * u := by
      rw [show m + u - (m - u) = 2 * u by ring, Real.norm_of_nonneg (by linarith [hu.1])]
    rwa [e] at this
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun u => A (m + u) - A (m - u) - u • (a₁ (m + u) + a₁ (m - u)))
    (f' := fun u => -(u • (a₂ (m + u) - a₂ (m - u))))
    (B := fun u => 2 * M * u ^ 3 / 3) (B' := fun u => 2 * M * u ^ 2) (a := 0) (b := h / 2)
    (((cp hA).sub (cn hA)).sub (continuousOn_id.smul ((cp ha₁).add (cn ha₁))))
    (fun u hu => by
      obtain ⟨h1, h2⟩ := hasDerivAt_reflect dA hu
      obtain ⟨k1, k2⟩ := hasDerivAt_reflect da₁ hu
      have := ((h1.sub h2).sub ((hasDerivAt_id' u).smul (k1.add k2))).hasDerivWithinAt
        (s := Ici u)
      refine this.congr_deriv ?_
      rw [hm, one_smul, Pi.add_apply]
      module)
    (by simp)
    (fun u => by
      have := ((hasDerivAt_pow 3 u).const_mul (2 * M)).div_const 3
      exact this.congr_deriv (by push_cast; ring))
    (fun u hu => by
      rw [norm_neg, norm_smul, Real.norm_of_nonneg hu.1]
      calc u * ‖a₂ (m + u) - a₂ (m - u)‖ ≤ u * (M * (2 * u)) :=
            mul_le_mul_of_nonneg_left (hmv u hu) hu.1
        _ = 2 * M * u ^ 2 := by ring)
    (right_mem_Icc.2 (by linarith : (0 : ℝ) ≤ h / 2))
  have e1 : m + h / 2 = t₀ + h := by rw [hm]; ring
  have e2 : m - h / 2 = t₀ := by rw [hm]; ring
  simp only [e1, e2] at key
  have hid : A (t₀ + h) - A t₀ - (h / 2) • (a₁ t₀ + a₁ (t₀ + h))
      = A (t₀ + h) - A t₀ - (h / 2) • (a₁ (t₀ + h) + a₁ t₀) := by rw [add_comm (a₁ t₀)]
  rw [hid]
  calc _ ≤ 2 * M * (h / 2) ^ 3 / 3 := key
    _ = M * h ^ 3 / 12 := by ring

/-- Data of a `C³` curve on `[t₀, t₀ + h]`, `h > 0`: the iterated derivatives within the interval
are continuous up to order three and are genuine derivatives of each other in the interior. -/
theorem contDiffOn_three_data {A : ℝ → E} {t₀ h : ℝ} (hh : 0 < h)
    (hA3 : ContDiffOn ℝ 3 A (Icc t₀ (t₀ + h))) :
    (∀ k ≤ 3, ContinuousOn (iteratedDerivWithin k A (Icc t₀ (t₀ + h))) (Icc t₀ (t₀ + h))) ∧
      (∀ k < 3, ∀ x ∈ Icc t₀ (t₀ + h),
        HasDerivWithinAt (iteratedDerivWithin k A (Icc t₀ (t₀ + h)))
          (iteratedDerivWithin (k + 1) A (Icc t₀ (t₀ + h)) x) (Icc t₀ (t₀ + h)) x) ∧
      ∀ k < 3, ∀ x ∈ Ioo t₀ (t₀ + h),
        HasDerivAt (iteratedDerivWithin k A (Icc t₀ (t₀ + h)))
          (iteratedDerivWithin (k + 1) A (Icc t₀ (t₀ + h)) x) x := by
  have hU : UniqueDiffOn ℝ (Icc t₀ (t₀ + h)) := uniqueDiffOn_Icc (by linarith)
  have hc := (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv (n := 3) hU).1 hA3
  have hw : ∀ k < 3, ∀ x ∈ Icc t₀ (t₀ + h),
      HasDerivWithinAt (iteratedDerivWithin k A (Icc t₀ (t₀ + h)))
        (iteratedDerivWithin (k + 1) A (Icc t₀ (t₀ + h)) x) (Icc t₀ (t₀ + h)) x := by
    intro k hk x hx
    rw [iteratedDerivWithin_succ]
    exact ((hc.2 k hk) x hx).hasDerivWithinAt
  exact ⟨hc.1, hw, fun k hk x hx =>
    (hw k hk x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)⟩

/-- For an exact solution that is `C³` on `[t₀, t₀ + h]`, the first iterated derivative within
the interval is the vector field along the solution, also at the right endpoint (where
`ODESolution` alone gives no derivative), provided `t ↦ F(t, A t)` is continuous there. -/
theorem iteratedDerivWithin_one_eq_field {F : ℝ → E → E} {A : ℝ → E} {t₀ h : ℝ} (hh : 0 < h)
    (hA : ODESolution F A t₀ (t₀ + h)) (hA3 : ContDiffOn ℝ 3 A (Icc t₀ (t₀ + h)))
    (hG : ContinuousWithinAt (fun t => F t (A t)) (Ico t₀ (t₀ + h)) (t₀ + h)) :
    ∀ t ∈ Icc t₀ (t₀ + h), iteratedDerivWithin 1 A (Icc t₀ (t₀ + h)) t = F t (A t) := by
  obtain ⟨hc, hw, -⟩ := contDiffOn_three_data hh hA3
  have hIco : ∀ t ∈ Ico t₀ (t₀ + h),
      iteratedDerivWithin 1 A (Icc t₀ (t₀ + h)) t = F t (A t) := by
    intro t ht
    have h1 := hw 0 (by norm_num) t (Ico_subset_Icc_self ht)
    rw [iteratedDerivWithin_zero] at h1
    have hsub : Icc t (t₀ + h) ⊆ Icc t₀ (t₀ + h) := Icc_subset_Icc_left ht.1
    exact (uniqueDiffOn_Icc ht.2 t ⟨le_rfl, ht.2.le⟩).eq_deriv _ (h1.mono hsub)
      ((hA.deriv t ht).mono Icc_subset_Ici_self)
  intro t ht
  rcases ht.2.lt_or_eq with hlt | heq
  · exact hIco t ⟨ht.1, hlt⟩
  subst heq
  have hne : (nhdsWithin (t₀ + h) (Ico t₀ (t₀ + h))).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico (by linarith)]
    exact right_mem_Icc.2 (by linarith)
  have hD : ContinuousWithinAt (iteratedDerivWithin 1 A (Icc t₀ (t₀ + h))) (Ico t₀ (t₀ + h))
      (t₀ + h) :=
    ((hc 1 (by norm_num)) _ (right_mem_Icc.2 (by linarith))).mono Ico_subset_Icc_self
  have hev : iteratedDerivWithin 1 A (Icc t₀ (t₀ + h)) =ᶠ[nhdsWithin (t₀ + h) (Ico t₀ (t₀ + h))]
      fun t => F t (A t) := eventually_nhdsWithin_of_forall hIco
  exact tendsto_nhds_unique (hD.tendsto.congr' hev) hG

omit [InnerProductSpace ℝ E] in
/-- Continuity of `t ↦ F(t, A t)` from the left at `t₁` for a Lipschitz, time-Lipschitz field
along a continuous curve. -/
theorem continuousWithinAt_field {F : ℝ → E → E} {L Lₜ : ℝ} (hF : IsLipschitzField F L)
    (hFt : ∀ s t x, ‖F s x - F t x‖ ≤ Lₜ * |s - t|) {A : ℝ → E} {S : Set ℝ} {t₁ : ℝ}
    (hA : ContinuousWithinAt A S t₁) : ContinuousWithinAt (fun t => F t (A t)) S t₁ := by
  have hb : ∀ s, ‖F s (A s) - F t₁ (A t₁)‖ ≤ Lₜ * |s - t₁| + L * ‖A s - A t₁‖ := fun s =>
    calc ‖F s (A s) - F t₁ (A t₁)‖ ≤ ‖F s (A s) - F t₁ (A s)‖ + ‖F t₁ (A s) - F t₁ (A t₁)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add (hFt _ _ _) (hF _ _ _)
  have hlim : Filter.Tendsto (fun s => Lₜ * |s - t₁| + L * ‖A s - A t₁‖) (nhdsWithin t₁ S)
      (nhds (Lₜ * |t₁ - t₁| + L * ‖A t₁ - A t₁‖)) := by
    refine Filter.Tendsto.add (Filter.Tendsto.const_mul _ ?_)
      (Filter.Tendsto.const_mul _ (hA.tendsto.sub tendsto_const_nhds).norm)
    exact ((continuous_id.sub continuous_const).abs.tendsto t₁).mono_left nhdsWithin_le_nhds
  simp only [sub_self, abs_zero, mul_zero, norm_zero, add_zero] at hlim
  exact tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun _ => norm_nonneg _) hb hlim)

/-- Speed bound around an interior point: `‖A s - A m‖ ≤ B |s - m|` for `s, m ∈ [a, b]`. -/
theorem odeSolution_norm_sub_le_abs {F : ℝ → E → E} {A : ℝ → E} {a b B : ℝ}
    (hA : ODESolution F A a b) (hB : IsBoundedField F B) {s m : ℝ} (hs : s ∈ Icc a b)
    (hm : m ∈ Icc a b) : ‖A s - A m‖ ≤ B * |s - m| := by
  rcases le_total m s with hms | hsm
  · have := (hA.mono hm.1 le_rfl).norm_sub_le_of_bounded hB s ⟨hms, hs.2⟩
    rwa [abs_of_nonneg (sub_nonneg.2 hms)]
  · have := (hA.mono hs.1 le_rfl).norm_sub_le_of_bounded hB m ⟨hsm, hm.2⟩
    rwa [norm_sub_rev, abs_of_nonpos (sub_nonpos.2 hsm), neg_sub]

/-- **Interior capture by a single node** (arXiv 2402.08607, proof of Thm 1): if `R` fixes
`A(t₀)` and captures `F(τ, Y)` up to `ε`, where `τ ∈ [t₀, t₀ + h]` and `‖Y - A(τ)‖ ≤ η`, then
`‖(1 - R) A(t)‖ ≤ h ((L B + Lₜ) d + L η + ε)` on the whole step, where `d` bounds `|s - τ|`
for `s ∈ [t₀, t₀ + h]`. -/
theorem interior_capture_node {F : ℝ → E → E} {L Lₜ B : ℝ} {R : E →L[ℝ] E} (hR : IsOrthProj R)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hFt : ∀ s t x, ‖F s x - F t x‖ ≤ Lₜ * |s - t|) {t₀ h : ℝ} (hh : 0 ≤ h) {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + h)) (hfix : R (A t₀) = A t₀) {τ d η ε : ℝ}
    (hτ : τ ∈ Icc t₀ (t₀ + h)) (hd : ∀ s ∈ Icc t₀ (t₀ + h), |s - τ| ≤ d) (hLt : 0 ≤ Lₜ) {Y : E}
    (hY : ‖Y - A τ‖ ≤ η) (hn : ‖(1 - R) (F τ Y)‖ ≤ ε) :
    ∀ t ∈ Icc t₀ (t₀ + h), ‖A t - R (A t)‖ ≤ h * ((L * B + Lₜ) * d + L * η + ε) := by
  have hb : ∀ s ∈ Ico t₀ (t₀ + h),
      ‖F s (A s) - R (F s (A s))‖ ≤ (L * B + Lₜ) * d + L * η + ε := by
    intro s hs
    have hs' := Ico_subset_Icc_self hs
    set x := F s (A s)
    set y := F τ Y
    have hdec : x - R x = ((x - y) - R (x - y)) + (y - R y) := by rw [map_sub]; abel
    have hy : ‖y - R y‖ ≤ ε := by simpa using hn
    have hxy : ‖x - y‖ ≤ (L * B + Lₜ) * d + L * η := by
      have h1 : ‖F s (A s) - F τ (A s)‖ ≤ Lₜ * d :=
        (hFt _ _ _).trans (mul_le_mul_of_nonneg_left (hd s hs') hLt)
      have h2 : ‖F τ (A s) - F τ (A τ)‖ ≤ L * (B * d) :=
        (hF _ _ _).trans (mul_le_mul_of_nonneg_left
          ((odeSolution_norm_sub_le_abs hA hB hs' hτ).trans
          (mul_le_mul_of_nonneg_left (hd s hs') hB.nonneg)) hL)
      have h3 : ‖F τ (A τ) - F τ Y‖ ≤ L * η :=
        (hF _ _ _).trans (mul_le_mul_of_nonneg_left (by rw [norm_sub_rev]; exact hY) hL)
      calc ‖x - y‖ ≤ ‖F s (A s) - F τ (A s)‖ + ‖F τ (A s) - F τ (A τ)‖
            + ‖F τ (A τ) - F τ Y‖ := by
            refine (norm_sub_le_norm_sub_add_norm_sub x (F τ (A τ)) y).trans ?_
            linarith [norm_sub_le_norm_sub_add_norm_sub x (F τ (A s)) (F τ (A τ))]
        _ ≤ Lₜ * d + L * (B * d) + L * η := add_le_add (add_le_add h1 h2) h3
        _ = (L * B + Lₜ) * d + L * η := by ring
    rw [hdec]
    calc _ ≤ ‖(x - y) - R (x - y)‖ + ‖y - R y‖ := norm_add_le _ _
      _ ≤ ‖x - y‖ + ε := add_le_add (hR.norm_sub_le _) hy
      _ ≤ _ := by linarith
  intro t ht
  have hg := norm_image_sub_le_of_norm_deriv_right_le_segment
    (f := fun t => A t - R (A t)) (f' := fun s => F s (A s) - R (F s (A s)))
    (hA.cont.sub (R.continuous.comp_continuousOn hA.cont))
    (fun s hs => (hA.deriv s hs).sub (R.hasFDerivAt.comp_hasDerivWithinAt s (hA.deriv s hs)))
    hb t ht
  simp only [hfix, sub_self, sub_zero] at hg
  rcases hh.eq_or_lt with h0 | h0
  · have : t = t₀ := le_antisymm (by linarith [ht.2]) ht.1
    subst this
    rw [hfix, sub_self, norm_zero, ← h0, zero_mul]
  · have hC : 0 ≤ (L * B + Lₜ) * d + L * η + ε :=
      (norm_nonneg _).trans (hb t₀ ⟨le_rfl, by linarith⟩)
    calc _ ≤ _ := hg
      _ ≤ ((L * B + Lₜ) * d + L * η + ε) * h :=
          mul_le_mul_of_nonneg_left (by linarith [ht.2]) hC
      _ = _ := by ring

/-- **Robust midpoint Galerkin step** (OP-HO-02; arXiv 2402.08607, proof of Thm 1; this is the
statement `midpointGalerkin_local_error`). Let `R` fix `Y₀ = A(t₀)` and capture the tangent part of
`F` at a midpoint predictor `Yh` with `‖Yh - A(t₀ + h/2)‖ ≤ η` up to `ε`, and let `A` be `C³` with
third derivative bounded by `M₃`. Then the Galerkin S-step from `Y₀` has local error `(e^{L h} - 1)
h ((L B + Lₜ) h/2 + L η + ε) + h (L η + ε) + M₃ h³/24 = O(h³ + h η + h ε)`, with the sharp
midpoint-rule constant `1/24` and no dependence on singular values. -/
theorem midpointGalerkin_local_error {F : ℝ → E → E} {L Lₜ B M₃ η ε : ℝ} {R : E →L[ℝ] E}
    (hR : IsOrthProj R) (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hFt : ∀ s t x, ‖F s x - F t x‖ ≤ Lₜ * |s - t|) {t₀ t₁ h : ℝ} (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) {A : ℝ → E} (hA : ODESolution F A t₀ t₁) (hA3 : ContDiffOn ℝ 3 A (Icc t₀ t₁))
    (hM₃ : ∀ t ∈ Icc t₀ t₁, ‖iteratedDerivWithin 3 A (Icc t₀ t₁) t‖ ≤ M₃)
    (hfix : R (A t₀) = A t₀) {Yh : E} (hYh : ‖Yh - A (t₀ + h / 2)‖ ≤ η)
    (hnormal : ‖(1 - R) (F (t₀ + h / 2) Yh)‖ ≤ ε) {YS : ℝ → E}
    (hS : ODESolution (fun t x => R (F t x)) YS t₀ t₁) (hS₀ : YS t₀ = A t₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (h * ((L * B + Lₜ) * h / 2 + L * η + ε))
      + (h * (L * η + ε) + M₃ * h ^ 3 / 24) := by
  subst ht₁
  rcases hh.eq_or_lt with h0 | hpos
  · subst h0; simp [hS₀]
  have hLt : 0 ≤ Lₜ := by
    have := (norm_nonneg _).trans (hFt (t₀ + h) t₀ (A t₀))
    rw [add_sub_cancel_left, abs_of_pos hpos] at this
    exact nonneg_of_mul_nonneg_left this hpos
  have hm : t₀ + h / 2 ∈ Ioo t₀ (t₀ + h) := ⟨by linarith, by linarith⟩
  obtain ⟨hc, -, hd⟩ := contDiffOn_three_data hpos hA3
  have hG := continuousWithinAt_field hF hFt
    ((hA.cont _ (right_mem_Icc.2 (le_add_of_nonneg_right hh))).mono
      (Ico_subset_Icc_self : Ico t₀ (t₀ + h) ⊆ _))
  have h1 := iteratedDerivWithin_one_eq_field hpos hA hA3 hG
  -- the midpoint defect with the sharp constant
  have hq : ‖A (t₀ + h) - A t₀ - h • F (t₀ + h / 2) (A (t₀ + h / 2))‖ ≤ M₃ * h ^ 3 / 24 := by
    have := midpoint_defect_le_sharp (A := A) hpos hA.cont (hc 1 (by norm_num))
      (hc 2 (by norm_num))
      (fun x hx => by simpa [iteratedDerivWithin_zero] using hd 0 (by norm_num) x hx)
      (hd 1 (by norm_num)) (hd 2 (by norm_num)) (fun x hx => hM₃ x (Ioo_subset_Icc_self hx))
    rwa [h1 _ (Ioo_subset_Icc_self hm)] at this
  have hθ := midpoint_capture hR hF hL hh hfix hq (Yh := Yh) (η := η) (ε' := ε)
    (by rw [norm_sub_rev]; exact hYh) (by simpa using hnormal)
  have hρ := interior_capture_node hR hF hL hB hFt hh hA hfix (Ioo_subset_Icc_self hm)
    (d := h / 2) (fun s hs => by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]) hLt hYh
    hnormal
  have := galerkin_step_error_interior hR hF hL rfl hh hA hS (hS₀.trans hfix.symm)
    (ρ := h * ((L * B + Lₜ) * (h / 2) + L * η + ε)) hρ hθ
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **Robust trapezoidal Galerkin step** (OP-HO-08; arXiv 2402.08607, Remark 2, claimed there
without proof; this is the statement `trapezoidalGalerkin_local_error`). Let `R` fix `Y₀ = A(t₀)`,
capture the tangent part of `F(t₀, Y₀)` up to `ε₀` and of `F(t₁, Ŷ₁)` up to `ε₁`, where `‖Ŷ₁ -
A(t₁)‖ ≤ η`, and let `A` be `C³` with third derivative bounded by `M₃`. Then the Galerkin S-step
from `Y₀` has local error `(e^{L h} - 1) h ((L B + Lₜ) h + ε₀) + (h/2)(ε₀ + L η + ε₁) + M₃ h³/12`,
with the sharp trapezoidal constant `1/12`. With `η = O(h (h + ε))` (augmented Euler-BUG predictor)
this is the claimed `O(h (h² + ε))`. -/
theorem trapezoidalGalerkin_local_error {F : ℝ → E → E} {L Lₜ B M₃ η ε₀ ε₁ : ℝ}
    {R : E →L[ℝ] E} (hR : IsOrthProj R) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hFt : ∀ s t x, ‖F s x - F t x‖ ≤ Lₜ * |s - t|) {t₀ t₁ h : ℝ}
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {A : ℝ → E} (hA : ODESolution F A t₀ t₁)
    (hA3 : ContDiffOn ℝ 3 A (Icc t₀ t₁))
    (hM₃ : ∀ t ∈ Icc t₀ t₁, ‖iteratedDerivWithin 3 A (Icc t₀ t₁) t‖ ≤ M₃)
    (hfix : R (A t₀) = A t₀) (hn₀ : ‖(1 - R) (F t₀ (A t₀))‖ ≤ ε₀) {Ŷ₁ : E}
    (hŶ : ‖Ŷ₁ - A t₁‖ ≤ η) (hn₁ : ‖(1 - R) (F t₁ Ŷ₁)‖ ≤ ε₁) {YS : ℝ → E}
    (hS : ODESolution (fun t x => R (F t x)) YS t₀ t₁) (hS₀ : YS t₀ = A t₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (h * ((L * B + Lₜ) * h + ε₀))
      + (h / 2 * (ε₀ + L * η + ε₁) + M₃ * h ^ 3 / 12) := by
  subst ht₁
  rcases hh.eq_or_lt with h0 | hpos
  · subst h0; simp [hS₀]
  have hLt : 0 ≤ Lₜ := by
    have := (norm_nonneg _).trans (hFt (t₀ + h) t₀ (A t₀))
    rw [add_sub_cancel_left, abs_of_pos hpos] at this
    exact nonneg_of_mul_nonneg_left this hpos
  obtain ⟨hc, -, hd⟩ := contDiffOn_three_data hpos hA3
  have hG := continuousWithinAt_field hF hFt
    ((hA.cont _ (right_mem_Icc.2 (le_add_of_nonneg_right hh))).mono
      (Ico_subset_Icc_self : Ico t₀ (t₀ + h) ⊆ _))
  have h1 := iteratedDerivWithin_one_eq_field hpos hA hA3 hG
  have hq : ‖A (t₀ + h) - A t₀ - (h / 2) • (F t₀ (A t₀) + F (t₀ + h) (A (t₀ + h)))‖
      ≤ M₃ * h ^ 3 / 12 := by
    have := trapezoid_defect_le_sharp (A := A) hpos hA.cont (hc 1 (by norm_num))
      (fun x hx => by simpa [iteratedDerivWithin_zero] using hd 0 (by norm_num) x hx)
      (hd 1 (by norm_num)) (hd 2 (by norm_num)) (fun x hx => hM₃ x (Ioo_subset_Icc_self hx))
    rwa [h1 _ (left_mem_Icc.2 (le_add_of_nonneg_right hh)),
      h1 _ (right_mem_Icc.2 (le_add_of_nonneg_right hh))] at this
  have hθ := trapezoid_capture hR hF hL hh hfix hq (Y₁ := Ŷ₁) (η := η) (ε₀ := ε₀) (ε₁ := ε₁)
    (by rw [norm_sub_rev]; exact hŶ) (by simpa using hn₀) (by simpa using hn₁)
  have hρ := interior_capture_node hR hF hL hB hFt hh hA hfix
    (left_mem_Icc.2 (le_add_of_nonneg_right hh)) (d := h)
    (fun s hs => by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]) hLt
    (Y := A t₀) (η := 0) (by simp) hn₀
  have := galerkin_step_error_interior hR hF hL rfl hh hA hS (hS₀.trans hfix.symm)
    (ρ := h * ((L * B + Lₜ) * h + L * 0 + ε₀)) hρ hθ
  calc _ ≤ _ := this
    _ = _ := by ring

end Sharp

/-! ### The bundled midpoint BUG step -/

section Step

/-- One step of the **midpoint BUG integrator** (Ceruti–Einkemmer–Kusch–Lubich, arXiv
2402.08607, Algorithm 1) from `(t₀, Y₀)` to `t₀ + h`: a first-order BUG half step (`half`,
`IsBUGStep` on `[t₀, t₀ + h/2]`, result `Yh = YH (t₀ + h/2)`), an augmented Galerkin projector `R`
(bases `[U₀, U_{1/2}, F(Yh) V_{1/2}]` and `[V₀, V_{1/2}, F(Yh)ᵀ U_{1/2}]`) that fixes `Y₀` and
captures the tangent part of `F(t₀ + h/2, Yh)` up to `ε₂` (the doubly normal component at the
rank-`2r` point `Yh`), the Galerkin S-step on the full step started at `Y₀`, and a truncation
to the tolerance `ϑ`. -/
structure IsMidpointBUGStep (F : ℝ → E → E) (ε ε₂ ϑ : ℝ) (P₀ Q₀ Ph Qh R : E →L[ℝ] E)
    (t₀ h : ℝ) (Y₀ : E) (YK YL YH YS : ℝ → E) (Y₁ : E) : Prop where
  /-- First-order (fixed-rank or augmented) BUG half step producing the midpoint predictor. -/
  half : IsBUGStep F ε P₀ Q₀ Ph Qh t₀ (t₀ + h / 2) Y₀ YK YL YH
  projR : IsOrthProj R
  /-- The enlarged bases contain the old ones, so the Galerkin space contains `Y₀`. -/
  fix : R Y₀ = Y₀
  /-- The enlarged bases capture the tangent part of `F` at the midpoint predictor. -/
  normal : ‖(1 - R) (F (t₀ + h / 2) (YH (t₀ + h / 2)))‖ ≤ ε₂
  /-- Galerkin S-step on `[t₀, t₀ + h]`, started at `Y₀`. -/
  sSol : ODESolution (fun t x => R (F t x)) YS t₀ (t₀ + h)
  sStart : YS t₀ = Y₀
  /-- Truncation of `Ŷ₁ = YS (t₀ + h)` to the tolerance `ϑ`. -/
  trunc : ‖Y₁ - YS (t₀ + h)‖ ≤ ϑ

/-- The robust constant of the midpoint BUG local error (`h ≤ H`), with `L, Lₜ, B, M₃, H` already
made nonnegative: `C = a + b + c` for the coefficients of `h³`, `h² ε` and `h ε₂`. -/
noncomputable def midpointBUGConst (L Lₜ B M₃ H : ℝ) : ℝ :=
  let K := Real.exp (L * H)
  let c₁ := bugC₁ L H
  let c₂ := bugC₂ L B H
  (L * K * (L * B + Lₜ) / 2 + L ^ 2 * K * c₂ * H / 4 + L * c₂ / 4 + M₃ / 24)
    + (L ^ 2 * K * c₁ * H / 2 + L * c₁ / 2) + (L * K * H + 1)

/-- The scalar estimate behind `IsMidpointBUGStep.local_error_le`. -/
theorem midpoint_bound_le {L Lₜ B M₃ H h ε ε₂ : ℝ} (hL : 0 ≤ L) (hLt : 0 ≤ Lₜ) (hB : 0 ≤ B)
    (hM : 0 ≤ M₃) (hh : 0 ≤ h) (hhH : h ≤ H) (hε : 0 ≤ ε) (hε₂ : 0 ≤ ε₂) :
    (Real.exp (L * h) - 1) * (h * ((L * B + Lₜ) * h / 2
        + L * (h / 2 * (bugC₁ L H * ε + bugC₂ L B H * (h / 2))) + ε₂))
      + (h * (L * (h / 2 * (bugC₁ L H * ε + bugC₂ L B H * (h / 2))) + ε₂) + M₃ * h ^ 3 / 24)
      ≤ midpointBUGConst L Lₜ B M₃ H * h * (h ^ 2 + h * ε + ε₂) := by
  have hH : 0 ≤ H := hh.trans hhH
  set K := Real.exp (L * H) with hK
  set c₁ := bugC₁ L H with hc₁
  set c₂ := bugC₂ L B H with hc₂
  have hc₁0 : 0 ≤ c₁ := bugC₁_nonneg hL hH
  have hc₂0 : 0 ≤ c₂ := bugC₂_nonneg hL hB hH
  have hK0 : 0 ≤ K := (Real.exp_pos _).le
  have hLh : 0 ≤ L * h := mul_nonneg hL hh
  have hexp : Real.exp (L * h) - 1 ≤ L * h * K :=
    (exp_sub_one_le_mul_exp (L * h)).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hL)) hLh)
  set X := h * ((L * B + Lₜ) * h / 2 + L * (h / 2 * (c₁ * ε + c₂ * (h / 2))) + ε₂) with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have h1 : (Real.exp (L * h) - 1) * X ≤ L * h * K * X := mul_le_mul_of_nonneg_right hexp hX0
  obtain ⟨δ, hδ, rfl⟩ : ∃ δ, 0 ≤ δ ∧ H = h + δ := ⟨H - h, by linarith, by ring⟩
  set a := L * K * (L * B + Lₜ) / 2 + L ^ 2 * K * c₂ * (h + δ) / 4 + L * c₂ / 4 + M₃ / 24
  set b := L ^ 2 * K * c₁ * (h + δ) / 2 + L * c₁ / 2
  set c := L * K * (h + δ) + 1
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hc : 0 ≤ c := by positivity
  have h2 : L * h * K * X + (h * (L * (h / 2 * (c₁ * ε + c₂ * (h / 2))) + ε₂) + M₃ * h ^ 3 / 24)
      ≤ h * (a * h ^ 2 + b * (h * ε) + c * ε₂) := by
    have hgap : 0 ≤ L ^ 2 * K * c₁ / 2 * h ^ 2 * ε * δ + L ^ 2 * K * c₂ / 4 * h ^ 3 * δ
        + L * K * h * ε₂ * δ := by positivity
    have hid : h * (a * h ^ 2 + b * (h * ε) + c * ε₂)
        = L * h * K * X + (h * (L * (h / 2 * (c₁ * ε + c₂ * (h / 2))) + ε₂) + M₃ * h ^ 3 / 24)
          + (L ^ 2 * K * c₁ / 2 * h ^ 2 * ε * δ + L ^ 2 * K * c₂ / 4 * h ^ 3 * δ
            + L * K * h * ε₂ * δ) := by
      simp only [a, b, c, hX]; ring
    linarith
  have h3 : h * (a * h ^ 2 + b * (h * ε) + c * ε₂) ≤ (a + b + c) * h * (h ^ 2 + h * ε + ε₂) := by
    have hq : 0 ≤ h ^ 2 := sq_nonneg h
    have hp : 0 ≤ h * ε := mul_nonneg hh hε
    have : a * h ^ 2 + b * (h * ε) + c * ε₂ ≤ (a + b + c) * (h ^ 2 + h * ε + ε₂) := by
      nlinarith [mul_nonneg ha hp, mul_nonneg ha hε₂, mul_nonneg hb hq, mul_nonneg hb hε₂,
        mul_nonneg hc hq, mul_nonneg hc hp]
    calc _ ≤ h * ((a + b + c) * (h ^ 2 + h * ε + ε₂)) := mul_le_mul_of_nonneg_left this hh
      _ = _ := by ring
  have hC : midpointBUGConst L Lₜ B M₃ (h + δ) = a + b + c := rfl
  rw [hC]
  linarith

/-- **Robust second-order local error of the midpoint BUG** (arXiv 2402.08607, Thm 1, 4r
variant; Claim 1 of OP-HO-02; this is the statement `IsMidpointBUGStep.local_error_le`). With step
sizes `0 ≤ h ≤ H`, the local error is `≤ C h (h² + h ε + ε₂) + ϑ`, where `C` depends only on `L, Lₜ,
B, M₃, H` (explicitly, `C = midpointBUGConst` of their positive parts) and not on `E`, the rank, or
singular values. Here `ε` is the normal-component bound of the first-order half step and `ε₂` the
normal component of `F` at the midpoint predictor (the doubly normal part `ε_{r̂}` in the paper). -/
theorem IsMidpointBUGStep.local_error_le (L Lₜ B M₃ H : ℝ) :
    ∃ C : ℝ, ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : ℝ → E → E}
      {ε ε₂ ϑ t₀ h : ℝ} {P₀ Q₀ Ph Qh R : E →L[ℝ] E} {Y₀ Y₁ : E} {YK YL YH YS A : ℝ → E},
      IsMidpointBUGStep F ε ε₂ ϑ P₀ Q₀ Ph Qh R t₀ h Y₀ YK YL YH YS Y₁ →
      IsLipschitzField F L → IsBoundedField F B →
      (∀ s t x, ‖F s x - F t x‖ ≤ Lₜ * |s - t|) → 0 ≤ h → h ≤ H →
      ODESolution F A t₀ (t₀ + h) → A t₀ = Y₀ → ContDiffOn ℝ 3 A (Icc t₀ (t₀ + h)) →
      (∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 3 A (Icc t₀ (t₀ + h)) t‖ ≤ M₃) →
      ‖Y₁ - A (t₀ + h)‖ ≤ C * h * (h ^ 2 + h * ε + ε₂) + ϑ := by
  refine ⟨midpointBUGConst (max L 0) (max Lₜ 0) (max B 0) (max M₃ 0) (max H 0), ?_⟩
  intro E _ _ F ε ε₂ ϑ t₀ h P₀ Q₀ Ph Qh R Y₀ Y₁ YK YL YH YS A hs hF hB hFt hh hhH hA hA₀ hA3 hM₃
  set L' := max L 0
  set Lₜ' := max Lₜ 0
  set B' := max B 0
  set M' := max M₃ 0
  set H' := max H 0
  have hL' : 0 ≤ L' := le_max_right _ _
  have hF' : IsLipschitzField F L' := fun t x y =>
    (hF t x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hB' : IsBoundedField F B' := fun t x => (hB t x).trans (le_max_left _ _)
  have hFt' : ∀ s t x, ‖F s x - F t x‖ ≤ Lₜ' * |s - t| := fun s t x =>
    (hFt s t x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have hM' : ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 3 A (Icc t₀ (t₀ + h)) t‖ ≤ M' :=
    fun t ht => (hM₃ t ht).trans (le_max_left _ _)
  have hhH' : h ≤ H' := hhH.trans (le_max_left _ _)
  have hh2 : 0 ≤ h / 2 := by linarith
  have hε : 0 ≤ ε := hs.half.eps_nonneg (by linarith)
  have hε₂ : 0 ≤ ε₂ := (norm_nonneg _).trans hs.normal
  -- half-step accuracy
  have hη := hs.half.local_error_le hF' hL' hB' rfl hh2 (H := H') (by linarith)
    (hA.mono le_rfl (by linarith)) hA₀
  -- Galerkin step
  have hG := midpointGalerkin_local_error hs.projR hF' hL' hB' hFt' rfl hh hA hA3 hM'
    (by rw [hA₀]; exact hs.fix) hη hs.normal hs.sSol (hs.sStart.trans hA₀.symm)
  have hbd := midpoint_bound_le hL' (le_max_right Lₜ 0) (le_max_right B 0) (le_max_right M₃ 0) hh
    hhH' hε hε₂
  calc ‖Y₁ - A (t₀ + h)‖ ≤ ‖Y₁ - YS (t₀ + h)‖ + ‖YS (t₀ + h) - A (t₀ + h)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ϑ + _ := add_le_add hs.trunc (hG.trans hbd)
    _ = _ := by ring

end Step

/-! ### Sharpness example -/

/-- **Sharpness and satisfiability** of `midpoint_defect_le_sharp`: for `A t = t³` on `[0, 1]`
(`M = 6`), the hypotheses hold and the bound `M h³/24 = 1/4` is attained. -/
theorem midpoint_defect_le_sharp_cubic :
    ‖(fun t : ℝ => t ^ 3) (0 + 1) - (fun t : ℝ => t ^ 3) 0
        - (1 : ℝ) • (fun t : ℝ => 3 * t ^ 2) (0 + 1 / 2)‖ = 6 * 1 ^ 3 / 24 ∧
      ‖(fun t : ℝ => t ^ 3) (0 + 1) - (fun t : ℝ => t ^ 3) 0
        - (1 : ℝ) • (fun t : ℝ => 3 * t ^ 2) (0 + 1 / 2)‖ ≤ 6 * 1 ^ 3 / 24 := by
  have h := midpoint_defect_le_sharp (E := ℝ) (A := fun t => t ^ 3) (a₁ := fun t => 3 * t ^ 2)
    (a₂ := fun t => 6 * t) (a₃ := fun _ => 6) (t₀ := 0) (h := 1) (M := 6) one_pos
    (by fun_prop) (by fun_prop) (by fun_prop)
    (fun x _ => by simpa using hasDerivAt_pow 3 x)
    (fun x _ => by
      have := (hasDerivAt_pow 2 x).const_mul 3
      exact this.congr_deriv (by push_cast; ring))
    (fun x _ => by simpa using (hasDerivAt_id x).const_mul 6)
    (fun _ _ => by norm_num)
  refine ⟨?_, h⟩
  norm_num

end LeanDLRA.MidpointBUG
