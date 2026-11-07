import LeanDLRA.Foundations.OneSided
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2501.07439 (Saluzzi–Strazzullo): sensitivity of closed-loop SDRE dynamics

Core definitions used: `LeanDLRA.IsOneSidedLipschitzOn` and `LeanDLRA.ODESolution` with the
stability estimate `LeanDLRA.ODESolution.norm_sub_le_exp_of_oneSidedOn` (Foundations/OneSided).
Nothing local is defined; the logarithmic norm is kept in its bound form.

Setting: a real inner product space `E` in place of `ℝ^d`, parameters in a set `PS` of a normed
space `P` in place of `ℝ^p`. The logarithmic norm `logm(M)` (Definition 3.2) is used only through
its defining inequality `⟪M v, v⟫ ≤ m ‖v‖²`, which for real matrices is the same as
`logm(M) ≤ m` (the sup over complex vectors reduces to the sup over real vectors).

Proved here, following the paper's appendix and Section 3:

* `closedLoop_isOneSidedLipschitzOn`: Proposition A.2. For a closed loop `A_cl` Lipschitz on `Ω`
  with constant `L_cl`, with `logm(A_cl(x)) ≤ m` on `Ω` and `‖y‖ ≤ M` on `Ω`, the field
  `y ↦ A_cl(y) y` is one-sided Lipschitz on `Ω` with constant `m + L_cl M`.
* `closedLoop_param_sensitivity`: Corollary A.3. Trajectories of `ẏ = A_cl(y) y` started at
  `y₀(μ)`, `y₀(μ̃)` stay in `Ω`; then `‖y(t;μ) − y(t;μ̃)‖ ≤ L_y0 ‖μ − μ̃‖ e^{Lt}` on `[0,T]`
  (the stability part comes from the core lemma; A.1 itself is the core lemma).
* `open_loop_sensitivity`: the estimate `‖A(y(t;μ)) − A(y(t;μ̃))‖ ≤ L_A L_y0 ‖μ − μ̃‖ e^{Lt}` that
  opens the proof of Proposition 3.5 (Assumption 3.3(e) composed with the previous item).
* `closedLoop_speed_antitone`: Proposition A.4. With `A_cl` differentiable on `Ω`, and
  `logm(A_cl(x)) ≤ m₁(x)`, `logm((∇A_cl(x))x) ≤ m₂(x)`, `m₁(x) + m₂(x) ≤ 0` on `Ω`
  (Assumption 3.3(f) with `m₁ + m₂ ≤ 0` in place of `< 0`), the map `t ↦ ‖A_cl(y(t)) y(t)‖` is
  nonincreasing along any trajectory of `ẏ = A_cl(y) y` in `Ω`. The derivative of `z = A_cl(y)y`
  is derived from the chain rule, not assumed. The paper writes `A(y)` where the chain rule gives
  `A_cl(y)`; the proof uses the latter. Assumption C^1 is weakened to differentiability on `Ω`.

Not formalized, and why:

* Proposition 3.5 (the Riccati statements `A_{μ̃,0} − F P_{μ,0}` stable, and `(3.10)`) and
  Proposition 3.7 (the time cascade) rest on Theorem 3.4 (perturbed algebraic Riccati equation and
  Lyapunov-based Hurwitz stability, from Kenney–Hewer and Gahinet–Laub). The library has no Riccati
  or Lyapunov theory, so these are left out, along with Remarks 3.6 and 3.8 which build on them.
* Proposition A.1 (`‖y(t;y₀) − y(t;ỹ₀)‖ ≤ e^{Lt}‖y₀ − ỹ₀‖`) is already proved in the library as
  `LeanDLRA.ODESolution.norm_sub_le_exp_of_oneSided`; it is not duplicated here.
* Equations (4.5) and (4.12) (factor equations for `Y = U Zᵀ`) are left out. The library's
  `Matrix/GaugeODE.lean` covers the analogous `U S Vᵀ` factorization, but the adaptation was not
  done in this file.
* Section 2 (Theorem 2.5, Newton–Kleinman convergence) and the numerical Appendix A.2 are not
  formalized.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2501_07439

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Proposition A.2 (arXiv 2501.07439).** Let `A_cl` be `L_cl`-Lipschitz on `Ω`, let
`logm(A_cl(x)) ≤ m` for `x ∈ Ω` (in the bound form `⟪A_cl(x) v, v⟫ ≤ m ‖v‖²`), and let `‖y‖ ≤ M`
on `Ω`. Then `y ↦ A_cl(y) y` is one-sided Lipschitz on `Ω` with constant `m + L_cl M`. -/
theorem closedLoop_isOneSidedLipschitzOn {Ω : Set E} {Acl : E → E →L[ℝ] E} {Lcl m M : ℝ}
    (hLcl : 0 ≤ Lcl) (hLip : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖Acl x - Acl y‖ ≤ Lcl * ‖x - y‖)
    (hlog : ∀ x ∈ Ω, ∀ v : E, ⟪Acl x v, v⟫ ≤ m * ‖v‖ ^ 2)
    (hbd : ∀ y ∈ Ω, ‖y‖ ≤ M) :
    IsOneSidedLipschitzOn (fun _ y => Acl y y) Ω (m + Lcl * M) := by
  intro _ x hx y hy
  have key : Acl x x - Acl y y = Acl x (x - y) + (Acl x - Acl y) y := by
    simp only [map_sub, sub_apply]
    abel
  have h1 : ⟪Acl x (x - y), x - y⟫ ≤ m * ‖x - y‖ ^ 2 := hlog x hx (x - y)
  have h2 : ‖(Acl x - Acl y) y‖ * ‖x - y‖ ≤ Lcl * M * ‖x - y‖ ^ 2 := by
    have hA : ‖Acl x - Acl y‖ * ‖y‖ ≤ Lcl * ‖x - y‖ * M :=
      mul_le_mul (hLip x hx y hy) (hbd y hy) (norm_nonneg _)
        (mul_nonneg hLcl (norm_nonneg _))
    have hB : ‖(Acl x - Acl y) y‖ ≤ ‖Acl x - Acl y‖ * ‖y‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hC : ‖(Acl x - Acl y) y‖ * ‖x - y‖ ≤ Lcl * ‖x - y‖ * M * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right (hB.trans hA) (norm_nonneg _)
    nlinarith [hC]
  have h3 : ⟪(Acl x - Acl y) y, x - y⟫ ≤ Lcl * M * ‖x - y‖ ^ 2 :=
    (real_inner_le_norm _ _).trans h2
  have hsplit : ⟪Acl x x - Acl y y, x - y⟫
      = ⟪Acl x (x - y), x - y⟫ + ⟪(Acl x - Acl y) y, x - y⟫ := by
    rw [key, inner_add_left]
  change ⟪Acl x x - Acl y y, x - y⟫ ≤ (m + Lcl * M) * ‖x - y‖ ^ 2
  rw [hsplit]
  nlinarith [h1, h3]

/-- **Corollary A.3 (arXiv 2501.07439), with the parameter-to-state map.** Let `y₀ : P → E` be
`L_y0`-Lipschitz on `PS`. Let `y(·;μ)` and `y(·;μ̃)` solve `ẏ = A_cl(y) y` on `[0, T]` with
initial data `y₀(μ)` and `y₀(μ̃)`, and stay in `Ω` (Assumption 3.3(a)–(d) with the constants of
`closedLoop_isOneSidedLipschitzOn`).
Then `‖y(t;μ) − y(t;μ̃)‖ ≤ L_y0 ‖μ − μ̃‖ e^{(m + L_cl M) t}`. -/
theorem closedLoop_param_sensitivity {P : Type*} [NormedAddCommGroup P]
    {Ω : Set E} {Acl : E → E →L[ℝ] E} {Lcl m M Ly0 T : ℝ} {PS : Set P} {y0 : P → E}
    (hLcl : 0 ≤ Lcl) (hLip : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖Acl x - Acl y‖ ≤ Lcl * ‖x - y‖)
    (hlog : ∀ x ∈ Ω, ∀ v : E, ⟪Acl x v, v⟫ ≤ m * ‖v‖ ^ 2)
    (hbd : ∀ y ∈ Ω, ‖y‖ ≤ M)
    (hy0 : ∀ μ₁ ∈ PS, ∀ μ₂ ∈ PS, ‖y0 μ₁ - y0 μ₂‖ ≤ Ly0 * ‖μ₁ - μ₂‖)
    {μ μ' : P} (hμ : μ ∈ PS) (hμ' : μ' ∈ PS) {y y' : ℝ → E}
    (hsol : ODESolution (fun _ y => Acl y y) y 0 T)
    (hsol' : ODESolution (fun _ y => Acl y y) y' 0 T)
    (h0 : y 0 = y0 μ) (h0' : y' 0 = y0 μ')
    (hyΩ : ∀ t ∈ Ico 0 T, y t ∈ Ω) (hy'Ω : ∀ t ∈ Ico 0 T, y' t ∈ Ω) :
    ∀ t ∈ Icc 0 T, ‖y t - y' t‖ ≤ Ly0 * ‖μ - μ'‖ * Real.exp ((m + Lcl * M) * t) := by
  intro t ht
  have hF := closedLoop_isOneSidedLipschitzOn hLcl hLip hlog hbd
  have hstab := hsol.norm_sub_le_exp_of_oneSidedOn hsol' hF hyΩ hy'Ω t ht
  have hini : ‖y 0 - y' 0‖ ≤ Ly0 * ‖μ - μ'‖ := by
    rw [h0, h0']
    exact hy0 μ hμ μ' hμ'
  have hexp : 0 ≤ Real.exp ((m + Lcl * M) * (t - 0)) := (Real.exp_pos _).le
  calc ‖y t - y' t‖ ≤ Real.exp ((m + Lcl * M) * (t - 0)) * ‖y 0 - y' 0‖ := hstab
    _ ≤ Real.exp ((m + Lcl * M) * (t - 0)) * (Ly0 * ‖μ - μ'‖) :=
        mul_le_mul_of_nonneg_left hini hexp
    _ = Ly0 * ‖μ - μ'‖ * Real.exp ((m + Lcl * M) * t) := by
        rw [sub_zero]; ring

/-- **Estimate opening the proof of Proposition 3.5 (arXiv 2501.07439).** Under the Lipschitz
condition `‖A(x) − A(x')‖ ≤ L_A ‖x − x'‖` on `Ω` (Assumption 3.3(e), open-loop matrix `A`) and the
hypotheses of `closedLoop_param_sensitivity`,
`‖A(y(t;μ)) − A(y(t;μ̃))‖ ≤ L_A L_y0 ‖μ − μ̃‖ e^{(m + L_cl M) t}` on `[0, T]`. -/
theorem open_loop_sensitivity {P : Type*} [NormedAddCommGroup P]
    {Ω : Set E} {Acl : E → E →L[ℝ] E} {Am : E → E →L[ℝ] E} {LA Lcl m M Ly0 T : ℝ}
    {PS : Set P} {y0 : P → E}
    (hLA0 : 0 ≤ LA) (hLA : ∀ x ∈ Ω, ∀ x' ∈ Ω, ‖Am x - Am x'‖ ≤ LA * ‖x - x'‖)
    (hLcl : 0 ≤ Lcl) (hLip : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖Acl x - Acl y‖ ≤ Lcl * ‖x - y‖)
    (hlog : ∀ x ∈ Ω, ∀ v : E, ⟪Acl x v, v⟫ ≤ m * ‖v‖ ^ 2)
    (hbd : ∀ y ∈ Ω, ‖y‖ ≤ M)
    (hy0 : ∀ μ₁ ∈ PS, ∀ μ₂ ∈ PS, ‖y0 μ₁ - y0 μ₂‖ ≤ Ly0 * ‖μ₁ - μ₂‖)
    {μ μ' : P} (hμ : μ ∈ PS) (hμ' : μ' ∈ PS) {y y' : ℝ → E}
    (hsol : ODESolution (fun _ y => Acl y y) y 0 T)
    (hsol' : ODESolution (fun _ y => Acl y y) y' 0 T)
    (h0 : y 0 = y0 μ) (h0' : y' 0 = y0 μ')
    (hyΩ : ∀ t ∈ Icc 0 T, y t ∈ Ω) (hy'Ω : ∀ t ∈ Icc 0 T, y' t ∈ Ω) :
    ∀ t ∈ Icc 0 T, ‖Am (y t) - Am (y' t)‖
      ≤ LA * (Ly0 * ‖μ - μ'‖ * Real.exp ((m + Lcl * M) * t)) := by
  intro t ht
  have hs := closedLoop_param_sensitivity hLcl hLip hlog hbd hy0 hμ hμ' hsol hsol' h0 h0'
    (fun s hs => hyΩ s (Ico_subset_Icc_self hs)) (fun s hs => hy'Ω s (Ico_subset_Icc_self hs))
    t ht
  have hA := hLA (y t) (hyΩ t ht) (y' t) (hy'Ω t ht)
  exact hA.trans (mul_le_mul_of_nonneg_left hs hLA0)

/-- **Proposition A.4 (arXiv 2501.07439).** Let `A_cl` be differentiable on `Ω` with derivative
`DA x` at `x`. Let `logm(A_cl(x)) ≤ m₁ x` and `logm((∇A_cl(x)) x) ≤ m₂ x` on `Ω` (bound form), and
`m₁ x + m₂ x ≤ 0` on `Ω` (Assumption 3.3(f)). Along any trajectory `ẏ = A_cl(y) y` in `Ω` on
`[a, b]`, the speed `t ↦ ‖A_cl(y(t)) y(t)‖` is nonincreasing. -/
theorem closedLoop_speed_antitone {Ω : Set E} {Acl : E → E →L[ℝ] E}
    {DA : E → E →L[ℝ] (E →L[ℝ] E)} {m₁ m₂ : E → ℝ} {y : ℝ → E} {a b : ℝ}
    (hA : ∀ x ∈ Ω, HasFDerivAt Acl (DA x) x)
    (hm₁ : ∀ x ∈ Ω, ∀ v : E, ⟪Acl x v, v⟫ ≤ m₁ x * ‖v‖ ^ 2)
    (hm₂ : ∀ x ∈ Ω, ∀ v : E, ⟪DA x v x, v⟫ ≤ m₂ x * ‖v‖ ^ 2)
    (hf : ∀ x ∈ Ω, m₁ x + m₂ x ≤ 0)
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (Acl (y t) (y t)) t)
    (hyΩ : ∀ t ∈ Icc a b, y t ∈ Ω) :
    AntitoneOn (fun t => ‖Acl (y t) (y t)‖) (Icc a b) := by
  -- chain rule: z(t) = A_cl(y(t)) y(t) has derivative A_cl(y) z + (DA(y) z) y
  have hz : ∀ t ∈ Icc a b, HasDerivAt (fun t => Acl (y t) (y t))
      (Acl (y t) (Acl (y t) (y t)) + DA (y t) (Acl (y t) (y t)) (y t)) t := by
    intro t ht
    have hF : HasFDerivAt (fun x => Acl x x)
        ((Acl (y t)).comp (ContinuousLinearMap.id ℝ E) + (DA (y t)).flip (y t)) (y t) := by
      have h := (hA (y t) (hyΩ t ht)).clm_apply (hasFDerivAt_id (y t))
      convert h using 1 <;> simp
    have h := hF.comp_hasDerivAt t (hy t ht)
    convert h using 1 <;> simp [Function.comp_def]
  have hg : ∀ t ∈ Icc a b, HasDerivAt (fun t => ‖Acl (y t) (y t)‖ ^ 2)
      (2 * ⟪Acl (y t) (y t),
        Acl (y t) (Acl (y t) (y t)) + DA (y t) (Acl (y t) (y t)) (y t)⟫) t :=
    fun t ht => (hz t ht).norm_sq
  have hneg : ∀ t ∈ Icc a b,
      2 * ⟪Acl (y t) (y t),
        Acl (y t) (Acl (y t) (y t)) + DA (y t) (Acl (y t) (y t)) (y t)⟫ ≤ 0 := by
    intro t ht
    set v := Acl (y t) (y t) with hv
    have hΩ := hyΩ t ht
    have h1 : ⟪v, Acl (y t) v⟫ ≤ m₁ (y t) * ‖v‖ ^ 2 := by
      rw [real_inner_comm]
      exact hm₁ _ hΩ v
    have h2 : ⟪v, DA (y t) v (y t)⟫ ≤ m₂ (y t) * ‖v‖ ^ 2 := by
      rw [real_inner_comm]
      exact hm₂ _ hΩ v
    have h3 : ⟪v, Acl (y t) v + DA (y t) v (y t)⟫ = ⟪v, Acl (y t) v⟫ + ⟪v, DA (y t) v (y t)⟫ :=
      inner_add_right _ _ _
    have h4 : (m₁ (y t) + m₂ (y t)) * ‖v‖ ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (hf _ hΩ) (sq_nonneg _)
    rw [hv, h3] at *
    nlinarith [h1, h2, h4]
  have hanti : AntitoneOn (fun t => ‖Acl (y t) (y t)‖ ^ 2) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    · intro t ht
      exact (hg t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hg t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hg t (Ioo_subset_Icc_self ht)).deriv]
      exact hneg t (Ioo_subset_Icc_self ht)
  intro s hs t ht hst
  have h := hanti hs ht hst
  nlinarith [norm_nonneg (Acl (y t) (y t)), norm_nonneg (Acl (y s) (y s)), h]

end LeanDLRA.Literature.P2501_07439
