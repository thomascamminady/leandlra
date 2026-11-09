import LeanDLRA.Dynamics.ContinuousDLRA

/-!
# arXiv 2008.07427: quasi-optimality of the dynamical reduced basis

Theorem 4.11 (cited by the paper as [14, Theorem 32], Feppon-Lermusiaux).

The paper cites the quasi-optimality estimate for the DLRA solution `C~` compared with the best
rank-`n` approximation `Pi_M C` of the exact solution `C`, printed as

    ‖C~(t) - Pi_M C(t)‖ ≤ ∫_𝒯 ν ‖C(s) - Pi_M C(s)‖ e^{μ (t-s)} ds,
    μ = L + 2 sup_t ‖X_H(C(t))‖ / σ_n(C(t)),    ν = L + ‖X_H(C(s))‖ / (σ_n - σ_{n+1})(C(s)).

This module proves the estimate, **conditional on** the geometric input from singular value theory,
with uniform constants (`B ≥ ‖X_H‖`, `σ ≤ σ_n`, `σ - σ' ≤ σ_n - σ_{n+1}` in the intended reading)
on an arbitrary real inner product space `E`.  The geometric input (the curvature bound of the
tangent projectors with constant `1/σ_n`, the bound
`‖X'(t) - P_X(t) Ċ(t)‖ ≤ ‖Ċ‖/(σ_n - σ_{n+1}) · ‖C - X‖` on the derivative of the truncated SVD,
and a bound on `‖X'‖`) is not derived; it enters as hypotheses.  The analytic part, the Grönwall
argument that turns them into the integral estimate, is proved here.  Lemma 4.8 and Prop. 4.10,
which transfer the estimate to the symplectic setting of the paper, are not formalized.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2008_07427

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma tangential_bound {Q QX : E →L[ℝ] E} (hQ : IsOrthProj Q) (hQX : IsOrthProj QX)
    {fx fa x' : E} {r e L γ μ c : ℝ} (hγr : 0 ≤ γ * r) (hfx : ‖fx - fa‖ ≤ L * e)
    (hcurv : ∀ z, ‖(Q - QX) z‖ ≤ γ * r * ‖z‖) (hbest : ‖x' - QX fa‖ ≤ c * e)
    (hμ : ‖fa‖ ≤ μ) : ‖Q (fx - x')‖ ≤ γ * μ * r + (L + c) * e := by
  have hidem : QX ((1 - QX) fa) = 0 := by simp [hQX.idem]
  have hmid : (Q - QX) ((1 - QX) fa) = Q (fa - QX fa) := by
    rw [sub_apply, hidem, sub_zero, sub_apply, one_apply_eq_self]
  have hsplit : Q (fx - x') = Q (fx - fa) + (Q - QX) ((1 - QX) fa) + Q (QX fa - x') := by
    rw [hmid]
    simp only [map_sub]
    abel
  have hA2 : ‖(Q - QX) ((1 - QX) fa)‖ ≤ γ * μ * r :=
    calc ‖(Q - QX) ((1 - QX) fa)‖ ≤ γ * r * ‖(1 - QX) fa‖ := hcurv _
      _ ≤ γ * r * μ :=
          mul_le_mul_of_nonneg_left ((hQX.compl.norm_le fa).trans hμ) hγr
      _ = γ * μ * r := by ring
  have hA3 : ‖Q (QX fa - x')‖ ≤ c * e := by
    refine (hQ.norm_le _).trans ?_
    rw [norm_sub_rev]
    exact hbest
  rw [hsplit]
  calc ‖Q (fx - fa) + (Q - QX) ((1 - QX) fa) + Q (QX fa - x')‖
      ≤ ‖Q (fx - fa)‖ + ‖(Q - QX) ((1 - QX) fa)‖ + ‖Q (QX fa - x')‖ := norm_add₃_le
    _ ≤ L * e + γ * μ * r + c * e :=
        add_le_add (add_le_add ((hQ.norm_le _).trans hfx) hA2) hA3
    _ = γ * μ * r + (L + c) * e := by ring

private lemma normal_bound {Q QX : E →L[ℝ] E} {x' : E} {r γ μ' : ℝ} (hx' : QX x' = x')
    (hγr : 0 ≤ γ * r) (hcurv : ∀ z, ‖(Q - QX) z‖ ≤ γ * r * ‖z‖) (hμ' : ‖x'‖ ≤ μ') :
    ‖(1 - Q) x'‖ ≤ γ * μ' * r + 0 := by
  have he : (1 - Q) x' = -((Q - QX) x') := by
    simp only [sub_apply, one_apply_eq_self, hx']
    abel
  rw [he, norm_neg, add_zero]
  calc ‖(Q - QX) x'‖ ≤ γ * r * ‖x'‖ := hcurv _
    _ ≤ γ * r * μ' := mul_le_mul_of_nonneg_left hμ' hγr
    _ = γ * μ' * r := by ring

/-- **Theorem 4.11 of arXiv 2008.07427, conditional on the geometric bounds below**
(quasi-optimality of the DLRA, cited from [14, Theorem 32]), in the abstract setting of a real
inner product space `E` (the paper: `ℂ^{N × p}`).

* `Y` is the DLRA solution `Ẏ = P(t) F(t, Y)` (`C~`), `F` is `L`-Lipschitz (`ODESolution`,
  `IsLipschitzField`), `A` the exact solution (`C`), `X` the best approximation of `A` on the
  manifold (`Pi_M C`), `PX t` the orthogonal projector onto its tangent space.
* `B` bounds `‖F(t, A t)‖` (`sup ‖X_H‖`) and `‖X'‖`; `σ` stands for `σ_n` and `σ'` for `σ_{n+1}`
  only `σ' < σ` and `0 < σ` are needed.
* Geometric facts taken as hypotheses (not derived from the SVD; steps of the cited proof): the
  curvature bound `‖(P(t) - PX(t)) z‖ ≤ (1/σ) ‖Y - X‖ ‖z‖`, `X' ∈ range PX`, the derivative bound
  `‖X' - PX F(A)‖ ≤ (B/(σ - σ')) ‖A - X‖`, and `‖X'‖ ≤ B` (not in the printed constants).
* `Y(a) = X(a)` (the paper starts from the best approximation of the initial value).

Conclusion, with `μ = L + 2B/σ` and `ν = L + B/(σ - σ')`:
`‖Y t - X t‖ ≤ ∫ₐᵗ ν ‖A s - X s‖ e^{μ (t-s)} ds`.
Differences from the paper: uniform constants `B`, `σ`, `σ'` replace the paper's pointwise ratios
(its `ν` depends on `s`, its `μ` is a supremum of ratios); the printed integral runs over all of
`𝒯`, here over `[a, t]` (a smaller domain of a nonnegative integrand); `A` and `X` are required
continuous on `[a, b]` (so that the integral makes sense); the starting time is a general `a`. -/
theorem quasi_optimality {P PX : ℝ → E →L[ℝ] E} {F : ℝ → E → E} {Y A X X' : ℝ → E}
    {a b L B σ σ' : ℝ} (hF : IsLipschitzField F L) (hσ : 0 < σ) (hσσ : σ' < σ)
    (hY : ODESolution (fun t x => P t (F t x)) Y a b) (hP : ∀ t ∈ Ico a b, IsOrthProj (P t))
    (hPX : ∀ t ∈ Ico a b, IsOrthProj (PX t))
    (hAc : ContinuousOn A (Icc a b)) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXtan : ∀ t ∈ Ico a b, PX t (X' t) = X' t)
    (hcurv : ∀ t ∈ Ico a b, ∀ z, ‖(P t - PX t) z‖ ≤ (1 / σ) * ‖Y t - X t‖ * ‖z‖)
    (hbest : ∀ t ∈ Ico a b,
      ‖X' t - PX t (F t (A t))‖ ≤ (B / (σ - σ')) * ‖A t - X t‖)
    (hB : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ B) (hB' : ∀ t ∈ Ico a b, ‖X' t‖ ≤ B)
    (h0 : Y a = X a) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      ∫ s in a..t, (L + B / (σ - σ')) * ‖A s - X s‖ * Real.exp ((L + 2 * B / σ) * (t - s)) := by
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  rcases eq_or_lt_of_le ht.1 with hat | hat
  · subst hat
    simp [h0]
  have hab' : a < b := hat.trans_le ht.2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB a ⟨le_rfl, hab'⟩)
  have hc : 0 ≤ B / (σ - σ') := div_nonneg hB0 (sub_pos.2 hσσ).le
  set η : ℝ → ℝ := fun s => ‖A (Set.projIcc a b hab s) - X (Set.projIcc a b hab s)‖ with hη
  have hηc : Continuous η := by
    have hp : Continuous fun s : ℝ => ((Set.projIcc a b hab s : Icc a b) : ℝ) :=
      continuous_subtype_val.comp continuous_projIcc
    have h1 := hAc.comp_continuous hp fun s => (Set.projIcc a b hab s).2
    have h2 := hXc.comp_continuous hp fun s => (Set.projIcc a b hab s).2
    exact (h1.sub h2).norm
  have hηeq : ∀ s ∈ Icc a b, η s = ‖A s - X s‖ := fun s hs => by
    simp only [hη, Set.projIcc_of_mem hab hs]
  have hσ1 : 0 ≤ 1 / σ := by positivity
  have hγe : ∀ t, 0 ≤ 1 / σ * ‖Y t - X t‖ := fun t => mul_nonneg hσ1 (norm_nonneg _)
  have h₁ : ∀ t ∈ Ico a b, ‖P t (F t (X t) - X' t)‖ ≤
      1 / σ * B * ‖Y t - X t‖ + (L + B / (σ - σ')) * η t := fun t ht => by
    have := tangential_bound (hP t ht) (hPX t ht) (hγe t)
      ((hF t _ _).trans_eq (by rw [norm_sub_rev])) (hcurv t ht) (hbest t ht) (hB t ht)
    rwa [hηeq t (Ico_subset_Icc_self ht)]
  have h₂ : ∀ t ∈ Ico a b, ‖(1 - P t) (X' t)‖ ≤ 1 / σ * B * ‖Y t - X t‖ + (fun _ => (0:ℝ)) t :=
    fun t ht => normal_bound (hXtan t ht) (hγe t) (hcurv t ht) (hB' t ht)
  have key := ODESolution.dlra_norm_sub_le_of_comparison_integral
    (η₁ := fun s => (L + B / (σ - σ')) * η s) (η₂ := fun _ => 0)
    (continuous_const.mul hηc) continuous_const hF hY hP hXc hX h₁ h₂
    (δ := 0) (by rw [h0, sub_self, norm_zero]) t ht
  have hK : L + 1 / σ * B + 1 / σ * B = L + 2 * B / σ := by field_simp; ring
  rw [hK] at key
  refine key.trans (le_of_eq ?_)
  unfold gronwallIntegralBound
  rw [zero_add, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hs' : s ∈ Icc a t := by rwa [uIcc_of_le ht.1] at hs
  have hsb : s ∈ Icc a b := ⟨hs'.1, hs'.2.trans ht.2⟩
  simp only [add_zero]
  rw [hηeq s hsb]
  have he : Real.exp ((L + 2 * B / σ) * (t - a)) * Real.exp (-((L + 2 * B / σ) * (s - a))) =
      Real.exp ((L + 2 * B / σ) * (t - s)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc _ = (L + B / (σ - σ')) * ‖A s - X s‖ *
        (Real.exp ((L + 2 * B / σ) * (t - a)) * Real.exp (-((L + 2 * B / σ) * (s - a)))) := by
          ring
    _ = _ := by rw [he]

/-- Non-vacuity: the hypotheses of `quasi_optimality` hold for `E = ℝ`, `F = 0`, `Y = A = X = 0`
and `P = PX = 1`. -/
example : ∀ t ∈ Icc (0:ℝ) 1, ‖(fun _ : ℝ => (0:ℝ)) t - (fun _ : ℝ => (0:ℝ)) t‖ ≤
    ∫ s in (0:ℝ)..t, (0 + 0 / (1 - 0)) * ‖(fun _ : ℝ => (0:ℝ)) s - (fun _ : ℝ => (0:ℝ)) s‖ *
      Real.exp ((0 + 2 * 0 / 1) * (t - s)) := by
  refine quasi_optimality (P := fun _ => 1) (PX := fun _ => 1) (F := fun _ _ => (0:ℝ))
    (X' := fun _ => 0) (L := 0) (B := 0) (σ := 1) (σ' := 0) ?_ one_pos one_pos ?_ ?_ ?_
    continuousOn_const continuousOn_const ?_ ?_ ?_ ?_ ?_ ?_ rfl
  · intro t x y; simp
  · refine ⟨continuousOn_const, fun t _ => ?_⟩
    exact ((hasDerivAt_const t (0:ℝ)).hasDerivWithinAt).congr_deriv (by simp)
  · intro t _; exact ⟨by simp, by simp⟩
  · intro t _; exact ⟨by simp, by simp⟩
  · intro t _; exact (hasDerivAt_const t (0:ℝ)).hasDerivWithinAt
  · intro t _; simp
  · intro t _ z; simp
  · intro t _; simp
  · intro t _; simp
  · intro t _; simp

end LeanDLRA.Literature.P2008_07427
