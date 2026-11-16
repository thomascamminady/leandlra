import LeanDLRA.HighOrder.MidpointBUG
import LeanDLRA.Integrators.Defs

/-!
# Second-order global error bound of the midpoint BUG integrator

For a right-hand side `F` of class `C²` with bounded first and second derivatives, the midpoint
BUG integrator (`MidpointBUG.IsMidpointBUGStep`) is robustly of second order with explicit
constants: after `n` steps of size `h` from `Y 0` with `‖Y 0 - A t₀‖ ≤ δ`,

  `‖Y n - A (t₀ + n h)‖ ≤ c₀ δ + c₁ ε₂ + c₂ h ε + c₃ h² + c₄ n ϑ`,

where `ε` bounds the normal components in the first-order half step (rank `r`), `ε₂` the normal
component of `F` at the midpoint predictor in the augmented bases (augmented rank), and `ϑ` is the
truncation tolerance; `c₀ = c₄ = e^{L T}` and `c₁ = c₂ = c₃ = T e^{L T} C` with
`C = midpointBUGConst L M₁ B (M₂ (1 + B)² + M₁² (1 + B)) H`, which depends only on the Lipschitz
constant `L`, the bound `B` of `F`, the bounds `M₁`, `M₂` of its first and second derivatives, the
horizon `T` and the step-size bound `H`, and not on singular values
(Ceruti–Einkemmer–Kusch–Lubich, arXiv 2402.08607, Theorem 2).

## Main results

* `ODESolution.contDiffOn_three`, `ODESolution.norm_iteratedDerivWithin_three_le_of_contDiff`:
  a solution of `y' = F(t, y)` with `F` of class `C²` is `C³`, and
  `‖y'''‖ ≤ M₂ (1 + B)² + M₁² (1 + B)`, independently of the solution.
* `MidpointBUG.IsMidpointBUGStep.norm_sub_le`: the local error of one step with the explicit
  constant `midpointBUGConst L Lₜ B M₃ H` (arXiv 2402.08607, Theorem 1).
* `MidpointBUG.IsMidpointBUGStep.hasLocalError`: the same for `F` of class `C²`, as a
  `HasLocalError` statement.
* `midpointBUG_global_error_le`: the global error bound above.

## Implementation notes

The hypotheses on `F` are global: the uncurried field `(t, x) ↦ F t x` is of class `C²` on
`ℝ × E` with first and second derivatives bounded by `M₁` and `M₂` everywhere, and `F` is
`L`-Lipschitz in the state and bounded by `B` everywhere. The regularity of the exact solutions,
which the paper takes from "a bound of the third derivative of exact solutions", is derived from
`F`: with `‖DF‖ ≤ M₁` the field is Lipschitz in time with constant `M₁`, and the third derivative
of every solution is bounded by `M₂ (1 + B)² + M₁² (1 + B)`. The steps are the projector-level
`MidpointBUG.IsMidpointBUGStep`, whose fields contain the normal-component bounds `ε` and `ε₂`;
the exact flows `Φ n` started at the numerical values are hypotheses, as in
`bug_global_error_le`.

## TODO

* The tube-local version: `F` of class `C²` with bounded derivatives only on a tube around the
  exact solution, as in the paper ("in a neighbourhood").
* The factor-level midpoint BUG step as a `StepMethod`, with the bridge from the matrix step of
  the paper (bases `[U₀, U_{1/2}, F(Yh) V_{1/2}]`) to `MidpointBUG.IsMidpointBUGStep`.

## References

* G. Ceruti, L. Einkemmer, J. Kusch, Ch. Lubich, *A robust second-order low-rank BUG integrator
  based on the midpoint rule*, arXiv 2402.08607.
-/

open Set

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Third derivatives of solutions for a field of class `C²` -/

section Regularity

/-- A curve with continuous right derivatives `g` on `[a, b)`, `g` continuous on `[a, b]`, has the
derivative `g t` within `[a, b]` at every `t ∈ [a, b]`. -/
private theorem hasDerivWithinAt_Icc_of_right_aux {y g : ℝ → E} {a b : ℝ}
    (hyc : ContinuousOn y (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt y (g t) (Ici t) t) (hgc : ContinuousOn g (Icc a b)) :
    ∀ t ∈ Icc a b, HasDerivWithinAt y (g t) (Icc a b) t := by
  intro t ht
  -- mean value estimate on a subinterval where `g` is close to `g t`
  have key : ∀ {c : ℝ} {s r : ℝ}, s ∈ Icc a b → r ∈ Icc a b → s ≤ r →
      (∀ u ∈ Icc s r, ‖g u - g t‖ ≤ c) → ‖y r - y s - (r - s) • g t‖ ≤ c * (r - s) := by
    intro c s r hs hr hsr hc
    have hφc : ContinuousOn (fun u => y u - u • g t) (Icc s r) :=
      (hyc.mono (Icc_subset_Icc hs.1 hr.2)).sub (continuous_id.smul continuous_const).continuousOn
    have hφd : ∀ u ∈ Ico s r, HasDerivWithinAt (fun u => y u - u • g t) (g u - g t) (Ici u) u := by
      intro u hu
      have h1 : HasDerivAt (fun u : ℝ => u • g t) ((1 : ℝ) • g t) u :=
        (hasDerivAt_id u).smul_const (g t)
      rw [one_smul] at h1
      exact (hd u ⟨hs.1.trans hu.1, hu.2.trans_le hr.2⟩).sub h1.hasDerivWithinAt
    have := norm_image_sub_le_of_norm_deriv_right_le_segment hφc hφd
      (fun u hu => hc u ⟨hu.1, hu.2.le⟩) r ⟨hsr, le_rfl⟩
    have e : (y r - r • g t) - (y s - s • g t) = y r - y s - (r - s) • g t := by
      rw [sub_smul]; abel
    rwa [e] at this
  rw [hasDerivWithinAt_iff_isLittleO]
  refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
  have hev := (hgc t ht).eventually (Metric.ball_mem_nhds (g t) hc)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds t hδ)]
    with x hxI hxb
  have hclose : ∀ u ∈ Icc a b, dist u t < δ → ‖g u - g t‖ ≤ c := fun u hu hd' => by
    have := hball hd' hu
    rw [dist_eq_norm] at this
    exact this.le
  have hxb' : |x - t| < δ := by
    rw [Metric.mem_ball, Real.dist_eq] at hxb; exact hxb
  rw [abs_lt] at hxb'
  rcases le_total t x with htx | hxt
  · have := key (c := c) ht hxI htx (fun u hu => hclose u ⟨ht.1.trans hu.1, hu.2.trans hxI.2⟩
      (by rw [Real.dist_eq, abs_lt]
          constructor <;> linarith [hu.1, hu.2, hxb'.1, hxb'.2]))
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 htx)]
    exact this
  · have := key (c := c) hxI ht hxt (fun u hu => hclose u ⟨hxI.1.trans hu.1, hu.2.trans ht.2⟩
      (by rw [Real.dist_eq, abs_lt]
          constructor <;> linarith [hu.1, hu.2, hxb'.1, hxb'.2]))
    have e : y x - y t - (x - t) • g t = -(y t - y x - (t - x) • g t) := by
      simp only [sub_smul]; abel
    rw [e, norm_neg, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.2 hxt)]
    calc _ ≤ c * (t - x) := this
      _ = c * -(x - t) := by ring

/-- On `[a, b]` with `a < b`, a solution of `y' = F(t, y)` for `F` of class `C²` is `C³`, and its
third derivative is `D²F[(1, F), (1, F)] + DF(0, DF(1, F))` along the solution. -/
private theorem odeSolution_contDiffOn_three_aux {F : ℝ → E → E}
    (hF : ContDiff ℝ 2 (Function.uncurry F)) {y : ℝ → E} {a b : ℝ} (hab : a < b)
    (hy : ODESolution F y a b) :
    ContDiffOn ℝ 3 y (Icc a b) ∧ ∀ t ∈ Icc a b, iteratedDerivWithin 3 y (Icc a b) t =
      fderiv ℝ (fderiv ℝ (Function.uncurry F)) (t, y t) ((1 : ℝ), F t (y t)) ((1 : ℝ), F t (y t))
        + fderiv ℝ (Function.uncurry F) (t, y t)
          ((0 : ℝ), fderiv ℝ (Function.uncurry F) (t, y t) ((1 : ℝ), F t (y t))) := by
  set Gu := Function.uncurry F with hGu
  have hU : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  set p : ℝ → ℝ × E := fun t => (t, y t) with hp
  set g : ℝ → E := fun t => Gu (p t) with hg
  have hpc : ContinuousOn p (Icc a b) := continuousOn_id.prodMk hy.cont
  have hgc : ContinuousOn g (Icc a b) := hF.continuous.comp_continuousOn hpc
  have hy1 : ∀ t ∈ Icc a b, HasDerivWithinAt y (g t) (Icc a b) t :=
    hasDerivWithinAt_Icc_of_right_aux hy.cont hy.deriv hgc
  have hdw : EqOn (derivWithin y (Icc a b)) g (Icc a b) := fun t ht =>
    (hy1 t ht).derivWithin (hU t ht)
  have hdiff : DifferentiableOn ℝ y (Icc a b) := fun t ht => (hy1 t ht).differentiableWithinAt
  have hC1 : ContDiffOn ℝ 1 y (Icc a b) :=
    (contDiffOn_one_iff_derivWithin hU).2 ⟨hdiff, hgc.congr hdw⟩
  have hGd : Differentiable ℝ Gu := hF.differentiable (by norm_num)
  have hp' : ∀ t ∈ Icc a b, HasDerivWithinAt p ((1 : ℝ), g t) (Icc a b) t := fun t ht =>
    (hasDerivWithinAt_id t _).prodMk (hy1 t ht)
  have hgC : ∀ k : ℕ, k ≤ 2 → ContDiffOn ℝ k y (Icc a b) → ContDiffOn ℝ k g (Icc a b) :=
    fun k hk hyk => (hF.of_le (by exact_mod_cast hk)).comp_contDiffOn (contDiffOn_id.prodMk hyk)
  have hC2 : ContDiffOn ℝ 2 y (Icc a b) := by
    have : ContDiffOn ℝ ((1 : WithTop ℕ∞) + 1) y (Icc a b) :=
      (contDiffOn_succ_iff_derivWithin hU).2 ⟨hdiff, fun h => absurd h (by simp),
        (hgC 1 (by norm_num) hC1).congr hdw⟩
    have e : (1 : WithTop ℕ∞) + 1 = 2 := by norm_num
    rwa [e] at this
  have hC3 : ContDiffOn ℝ 3 y (Icc a b) := by
    have : ContDiffOn ℝ ((2 : WithTop ℕ∞) + 1) y (Icc a b) :=
      (contDiffOn_succ_iff_derivWithin hU).2 ⟨hdiff, fun h => absurd h (by simp),
        (hgC 2 le_rfl hC2).congr hdw⟩
    have e : (2 : WithTop ℕ∞) + 1 = 3 := by norm_num
    rwa [e] at this
  refine ⟨hC3, ?_⟩
  -- second derivative
  set g₂ : ℝ → E := fun t => fderiv ℝ Gu (p t) ((1 : ℝ), g t) with hg₂
  have hg' : ∀ t ∈ Icc a b, HasDerivWithinAt g (g₂ t) (Icc a b) t := fun t ht =>
    (hGd (p t)).hasFDerivAt.comp_hasDerivWithinAt t (hp' t ht)
  have hdw2 : EqOn (iteratedDerivWithin 2 y (Icc a b)) g₂ (Icc a b) := by
    intro t ht
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDerivWithin_succ, iteratedDerivWithin_one]
    rw [derivWithin_congr hdw (hdw ht)]
    exact (hg' t ht).derivWithin (hU t ht)
  -- third derivative
  have hF1 : Differentiable ℝ (fderiv ℝ Gu) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hc' : ∀ t ∈ Icc a b, HasDerivWithinAt (fun t => fderiv ℝ Gu (p t))
      (fderiv ℝ (fderiv ℝ Gu) (p t) ((1 : ℝ), g t)) (Icc a b) t := fun t ht =>
    (hF1 (p t)).hasFDerivAt.comp_hasDerivWithinAt t (hp' t ht)
  have hu' : ∀ t ∈ Icc a b, HasDerivWithinAt (fun t => ((1 : ℝ), g t)) ((0 : ℝ), g₂ t)
      (Icc a b) t := fun t ht => (hasDerivWithinAt_const t _ (1 : ℝ)).prodMk (hg' t ht)
  have hg₂' : ∀ t ∈ Icc a b, HasDerivWithinAt g₂
      (fderiv ℝ (fderiv ℝ Gu) (p t) ((1 : ℝ), g t) ((1 : ℝ), g t) +
        fderiv ℝ Gu (p t) ((0 : ℝ), g₂ t)) (Icc a b) t := fun t ht =>
    (hc' t ht).clm_apply (hu' t ht)
  intro t ht
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDerivWithin_succ,
    derivWithin_congr hdw2 (hdw2 ht)]
  exact (hg₂' t ht).derivWithin (hU t ht)

/-- **Solutions are `C³` for a field of class `C²`.** If `F` is jointly of class `C²` as a
function of `(t, x)`, every solution of `y' = F(t, y)` on `[a, b]` is of class `C³` on
`[a, b]`. -/
theorem ODESolution.contDiffOn_three {F : ℝ → E → E} (hF : ContDiff ℝ 2 (Function.uncurry F))
    {y : ℝ → E} {a b : ℝ} (hy : ODESolution F y a b) : ContDiffOn ℝ 3 y (Icc a b) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact (odeSolution_contDiffOn_three_aux hF hab hy).1
  · rw [Icc_self]
    intro x hx
    rw [mem_singleton_iff] at hx
    subst hx
    exact contDiffWithinAt_singleton
  · rw [Icc_eq_empty hba.not_ge]
    exact contDiffOn_empty

/-- **Third derivative of solutions for a field of class `C²`.** Let `F` be jointly of class `C²`
as a function of `(t, x)`, bounded by `B`, with `‖DF‖ ≤ M₁` and `‖D²F‖ ≤ M₂` everywhere (norms on
`ℝ × E` with the maximum norm). Then every solution of `y' = F(t, y)` on `[a, b]` satisfies
`‖y'''‖ ≤ M₂ (1 + B)² + M₁² (1 + B)` on `[a, b]`, since
`y''' = D²F[(1, F), (1, F)] + DF(0, DF(1, F))` along the solution. The bound does not depend on
the solution. -/
theorem ODESolution.norm_iteratedDerivWithin_three_le_of_contDiff {F : ℝ → E → E} {B M₁ M₂ : ℝ}
    (hF : ContDiff ℝ 2 (Function.uncurry F)) (hB : IsBoundedField F B)
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂) {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution F y a b) :
    ∀ t ∈ Icc a b, ‖iteratedDerivWithin 3 y (Icc a b) t‖ ≤ M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  rcases lt_trichotomy a b with hab | rfl | hba
  · intro t ht
    rw [(odeSolution_contDiffOn_three_aux hF hab hy).2 t ht]
    set Gu := Function.uncurry F
    have hw : ‖((1 : ℝ), F t (y t))‖ ≤ 1 + B := by
      rw [Prod.norm_def]
      exact max_le (by linarith [norm_one (α := ℝ)]) ((hB _ _).trans (by linarith))
    have hn1 : ‖fderiv ℝ (fderiv ℝ Gu) (t, y t) ((1 : ℝ), F t (y t)) ((1 : ℝ), F t (y t))‖
        ≤ M₂ * (1 + B) ^ 2 := by
      have h2 := iteratedFDeriv_two_apply (𝕜 := ℝ) Gu (t, y t)
        ![((1 : ℝ), F t (y t)), ((1 : ℝ), F t (y t))]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
      rw [← h2]
      refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      calc _ ≤ M₂ * (‖((1 : ℝ), F t (y t))‖ * ‖((1 : ℝ), F t (y t))‖) :=
            mul_le_mul_of_nonneg_right (hM₂ _) (by positivity)
        _ ≤ M₂ * ((1 + B) * (1 + B)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hw hw (norm_nonneg _) (by linarith)) hM₂0
        _ = _ := by ring
    have hn2 : ‖fderiv ℝ Gu (t, y t) ((1 : ℝ), F t (y t))‖ ≤ M₁ * (1 + B) :=
      ((fderiv ℝ Gu (t, y t)).le_opNorm _).trans (mul_le_mul (hM₁ _) hw (norm_nonneg _) hM₁0)
    have hn3 : ‖fderiv ℝ Gu (t, y t) ((0 : ℝ), fderiv ℝ Gu (t, y t) ((1 : ℝ), F t (y t)))‖
        ≤ M₁ ^ 2 * (1 + B) := by
      refine ((fderiv ℝ Gu (t, y t)).le_opNorm _).trans ?_
      have : ‖((0 : ℝ), fderiv ℝ Gu (t, y t) ((1 : ℝ), F t (y t)))‖
          = ‖fderiv ℝ Gu (t, y t) ((1 : ℝ), F t (y t))‖ := by
        rw [Prod.norm_def]; simp
      rw [this]
      calc _ ≤ M₁ * (M₁ * (1 + B)) := mul_le_mul (hM₁ _) hn2 (norm_nonneg _) hM₁0
        _ = _ := by ring
    exact (norm_add_le _ _).trans (add_le_add hn1 hn3)
  · intro t ht
    rw [Icc_self, mem_singleton_iff] at ht
    subst ht
    have hacc : ¬ AccPt t (Filter.principal {t}) := by
      rw [accPt_principal_iff_nhdsWithin, Set.sdiff_self, nhdsWithin_empty]; simp
    have : iteratedDerivWithin 3 y (Icc t t) t = 0 := by
      rw [Icc_self, show (3 : ℕ) = 2 + 1 from rfl, iteratedDerivWithin_succ]
      exact derivWithin_zero_of_not_accPt hacc
    rw [this, norm_zero]
    positivity
  · intro t ht
    rw [Icc_eq_empty hba.not_ge] at ht
    exact absurd ht (notMem_empty t)

/-- A field whose uncurried form has derivative bounded by `M₁` is `M₁`-Lipschitz in time. -/
private theorem norm_sub_le_of_norm_fderiv_uncurry_le_aux {F : ℝ → E → E} {M₁ : ℝ}
    (hF : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁) (s t : ℝ) (x : E) :
    ‖F s x - F t x‖ ≤ M₁ * |s - t| := by
  have hd : ∀ p ∈ (univ : Set (ℝ × E)), DifferentiableAt ℝ (Function.uncurry F) p :=
    fun p _ => hF.differentiable (by norm_num) p
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le hd (fun p _ => hM₁ p) convex_univ
    (mem_univ (t, x)) (mem_univ (s, x))
  have hn : ‖((s, x) : ℝ × E) - (t, x)‖ = |s - t| := by
    rw [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero, Real.norm_eq_abs]
    exact max_eq_left (abs_nonneg _)
  rw [hn] at h
  exact h

end Regularity

/-! ### The local error with an explicit constant -/

namespace MidpointBUG

section Local

/-- The constant `midpointBUGConst` is nonnegative for nonnegative data. -/
private theorem midpointBUGConst_nonneg_aux {L Lₜ B M₃ H : ℝ} (hL : 0 ≤ L) (hLt : 0 ≤ Lₜ)
    (hB : 0 ≤ B) (hM : 0 ≤ M₃) (hH : 0 ≤ H) : 0 ≤ midpointBUGConst L Lₜ B M₃ H := by
  have h1 : 0 ≤ bugC₁ L H := bugC₁_nonneg hL hH
  have h2 : 0 ≤ bugC₂ L B H := bugC₂_nonneg hL hB hH
  have hK : 0 ≤ Real.exp (L * H) := (Real.exp_pos _).le
  simp only [midpointBUGConst]
  positivity

variable {F : ℝ → E → E} {ε ε₂ ϑ L B H t₀ h : ℝ} {P₀ Q₀ Ph Qh R : E →L[ℝ] E} {Y₀ Y₁ : E}
  {YK YL YH YS : ℝ → E}

/-- **Local error of the midpoint BUG with an explicit constant** (Ceruti–Einkemmer–Kusch–Lubich,
arXiv 2402.08607, Theorem 1, 4r variant). Let `F` be `L`-Lipschitz (`L ≥ 0`), bounded by `B` and
`Lₜ`-Lipschitz in time, and let the exact solution `A` with `A t₀ = Y₀` be `C³` on the step with
third derivative bounded by `M₃`. Then a midpoint BUG step of size `0 ≤ h ≤ H` has local error

  `‖Y₁ - A (t₀ + h)‖ ≤ C h (h² + h ε + ε₂) + ϑ`,  `C = midpointBUGConst L Lₜ B M₃ H`,

where `ε` is the normal-component bound of the first-order half step, `ε₂` the normal component
of `F` at the midpoint predictor in the augmented bases, and `ϑ` the truncation tolerance. This is
`IsMidpointBUGStep.local_error_le` with the constant named. -/
theorem IsMidpointBUGStep.norm_sub_le {Lₜ M₃ : ℝ} {A : ℝ → E}
    (hs : IsMidpointBUGStep F ε ε₂ ϑ P₀ Q₀ Ph Qh R t₀ h Y₀ YK YL YH YS Y₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hFt : ∀ s t x, ‖F s x - F t x‖ ≤ Lₜ * |s - t|) (hh : 0 ≤ h) (hhH : h ≤ H)
    (hA : ODESolution F A t₀ (t₀ + h)) (hA₀ : A t₀ = Y₀)
    (hA3 : ContDiffOn ℝ 3 A (Icc t₀ (t₀ + h)))
    (hM₃ : ∀ t ∈ Icc t₀ (t₀ + h), ‖iteratedDerivWithin 3 A (Icc t₀ (t₀ + h)) t‖ ≤ M₃) :
    ‖Y₁ - A (t₀ + h)‖ ≤ midpointBUGConst L Lₜ B M₃ H * h * (h ^ 2 + h * ε + ε₂) + ϑ := by
  have hLt : 0 ≤ Lₜ := by
    have := (norm_nonneg _).trans (hFt 1 0 (0 : E))
    simpa using this
  have hM : 0 ≤ M₃ := (norm_nonneg _).trans (hM₃ t₀ (left_mem_Icc.2 (by linarith)))
  have hh2 : 0 ≤ h / 2 := by linarith
  have hε : 0 ≤ ε := hs.half.eps_nonneg (by linarith)
  have hε₂ : 0 ≤ ε₂ := (norm_nonneg _).trans hs.normal
  -- half-step accuracy
  have hη := hs.half.local_error_le hF hL hB rfl hh2 (H := H) (by linarith)
    (hA.mono le_rfl (by linarith)) hA₀
  -- Galerkin step
  have hG := midpointGalerkin_local_error hs.projR hF hL hB hFt rfl hh hA hA3 hM₃
    (by rw [hA₀]; exact hs.fix) hη hs.normal hs.sSol (hs.sStart.trans hA₀.symm)
  have hbd := midpoint_bound_le hL hLt hB.nonneg hM hh hhH hε hε₂
  calc ‖Y₁ - A (t₀ + h)‖ ≤ ‖Y₁ - YS (t₀ + h)‖ + ‖YS (t₀ + h) - A (t₀ + h)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ϑ + _ := add_le_add hs.trunc (hG.trans hbd)
    _ = _ := by ring

/-- **Local error of the midpoint BUG for a field of class `C²`** (Ceruti–Einkemmer–Kusch–Lubich,
arXiv 2402.08607, Theorem 1, 4r variant). The regularity is global: let the uncurried field
`(t, x) ↦ F t x` be of class `C²` on `ℝ × E` with `‖DF‖ ≤ M₁` and `‖D²F‖ ≤ M₂` everywhere, and let
`F` be `L`-Lipschitz in the state (`L ≥ 0`) and bounded by `B` everywhere. Then a midpoint BUG
step of size `0 ≤ h ≤ H` has local error `C h (h² + h ε + ε₂) + ϑ` with
`C = midpointBUGConst L M₁ B (M₂ (1 + B)² + M₁² (1 + B)) H`: the exact solution from `Y₀` is `C³`
with `‖A'''‖ ≤ M₂ (1 + B)² + M₁² (1 + B)`
(`ODESolution.norm_iteratedDerivWithin_three_le_of_contDiff`), and `F` is `M₁`-Lipschitz in
time. -/
theorem IsMidpointBUGStep.hasLocalError {M₁ M₂ : ℝ}
    (hs : IsMidpointBUGStep F ε ε₂ ϑ P₀ Q₀ Ph Qh R t₀ h Y₀ YK YL YH YS Y₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hF₂ : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂) (hh : 0 ≤ h) (hhH : h ≤ H) :
    HasLocalError F t₀ (t₀ + h) Y₀ Y₁
      (midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H * h
        * (h ^ 2 + h * ε + ε₂) + ϑ) := fun _ hΦ hΦ₀ =>
  hs.norm_sub_le hF hL hB (norm_sub_le_of_norm_fderiv_uncurry_le_aux hF₂ hM₁) hh hhH hΦ hΦ₀
    (hΦ.contDiffOn_three hF₂) (hΦ.norm_iteratedDerivWithin_three_le_of_contDiff hF₂ hB hM₁ hM₂)

end Local

end MidpointBUG

/-! ### The global error -/

section Global

open MidpointBUG

/-- **Robust second-order global error bound of the midpoint BUG integrator, explicit constants**
(Ceruti–Einkemmer–Kusch–Lubich, arXiv 2402.08607, Theorem 2). The regularity of `F` is global:
let the uncurried field `(t, x) ↦ F t x` be of class `C²` on `ℝ × E` with `‖DF‖ ≤ M₁` and
`‖D²F‖ ≤ M₂` everywhere, and let `F` be `L`-Lipschitz in the state (`L ≥ 0`) and bounded by `B`
everywhere. Let `A` solve `A' = F(t, A)` on `[t₀, t₀ + N h]`, `0 ≤ h ≤ H`, and let `Y 0, …, Y N`
be obtained by `N` steps of the midpoint BUG integrator (`IsMidpointBUGStep`) with truncation
tolerance `ϑ`, where `ε ≥ 0` bounds the normal components in the first-order half step (rank `r`)
and `ε₂ ≥ 0` the normal component of `F` at the midpoint predictor in the augmented bases
(augmented rank). Let `Φ n` be the exact flow on `[t₀ + n h, t₀ + (n + 1) h]` started at `Y n`,
and `‖Y 0 - A t₀‖ ≤ δ`. Then for `n ≤ N` with `n h ≤ T`

  `‖Y n - A (t₀ + n h)‖ ≤ c₀ δ + c₁ ε₂ + c₂ h ε + c₃ h² + c₄ n ϑ`,

with `c₀ = c₄ = e^{L T}` and `c₁ = c₂ = c₃ = T e^{L T} C`,
`C = midpointBUGConst L M₁ B (M₂ (1 + B)² + M₁² (1 + B)) H`. The constants depend only on `L`,
`B`, `M₁`, `M₂`, `T` and `H`, not on singular values. Differences from the paper: the paper
assumes the bounds on `F` and the normal components only in a neighbourhood of the exact
solution and a bound of the third derivative of exact solutions; here the bounds on `F` are
global, the third derivative is bounded through `M₁` and `M₂`, and the normal-component bounds
are those of the steps. -/
theorem midpointBUG_global_error_le {F : ℝ → E → E} {L B M₁ M₂ ε ε₂ ϑ : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hF₂ : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂) (hε : 0 ≤ ε) (hε₂ : 0 ≤ ε₂)
    {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q Ph Qh R : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YK YL YH YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsMidpointBUGStep F ε ε₂ ϑ (P n) (Q n) (Ph n) (Qh n) (R n) (t₀ + n * h) h
      (Y n) (YK n) (YL n) (YH n) (YS n) (Y (n + 1)))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H
          * ε₂
        + T * Real.exp (L * T) * midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H
          * (h * ε)
        + T * Real.exp (L * T) * midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H
          * h ^ 2
        + Real.exp (L * T) * n * ϑ := by
  intro n hn hT
  have hB0 : 0 ≤ B := hB.nonneg
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  have hC0 : 0 ≤ midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H :=
    midpointBUGConst_nonneg_aux hL hM₁0 hB0 (by positivity) (hh.trans hhH)
  set C := midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H with hC
  set S := h ^ 2 + h * ε + ε₂ with hS
  have hS0 : 0 ≤ S := by positivity
  -- local errors along the fan
  have hloc : ∀ k < N, ‖Y (k + 1) - Φ k (t₀ + (k + 1) * h)‖ ≤ C * h * S + ϑ := by
    intro k hk
    have e : t₀ + ((k : ℝ) + 1) * h = t₀ + k * h + h := by ring
    have hΦk : ODESolution F (Φ k) (t₀ + k * h) (t₀ + k * h + h) := by
      rw [← e]; exact hΦ k hk
    have := (hstep k hk).hasLocalError hF hL hB hF₂ hM₁ hM₂ hh hhH (Φ k) hΦk (hΦ₀ k hk)
    rwa [← e] at this
  have key := lady_windermere hF hL hh hA hΦ hΦ₀ hloc n hn
  have hϑ : 0 ≤ (n : ℝ) * ϑ := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp
    · exact mul_nonneg (Nat.cast_nonneg n)
        ((norm_nonneg _).trans (hstep (n - 1) (by omega)).trunc)
  have hexp : Real.exp (L * (n * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  have e1 : (n : ℝ) * (C * h * S + ϑ) = n * h * (C * S) + n * ϑ := by ring
  have hnh : 0 ≤ (n : ℝ) * h * (C * S) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hh) (mul_nonneg hC0 hS0)
  have hp : 0 ≤ ‖Y 0 - A t₀‖ + n * (C * h * S + ϑ) := by
    rw [e1]; linarith [norm_nonneg (Y 0 - A t₀)]
  have h2 : ‖Y 0 - A t₀‖ + n * (C * h * S + ϑ) ≤ δ + T * (C * S) + n * ϑ := by
    have h3 : (n : ℝ) * h * (C * S) ≤ T * (C * S) :=
      mul_le_mul_of_nonneg_right hT (mul_nonneg hC0 hS0)
    rw [e1]; linarith
  calc _ ≤ _ := key
    _ ≤ Real.exp (L * T) * (δ + T * (C * S) + n * ϑ) :=
        mul_le_mul hexp h2 hp (Real.exp_pos _).le
    _ = _ := by rw [hS]; ring

end Global

/-! ### Non-vacuity: the field `F t x = sin x` on `ℝ` -/

section Examples

/-- The derivatives of order at most two of `(t, x) ↦ sin x` are bounded by `1`. -/
private theorem norm_iteratedFDeriv_sin_snd_le_aux {i : ℕ} (hi : i ≤ 2) (p : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ i (Function.uncurry fun (_ : ℝ) (x : ℝ) => Real.sin x) p‖ ≤ 1 := by
  have e : (Function.uncurry fun (_ : ℝ) (x : ℝ) => Real.sin x) =
      Real.sin ∘ (ContinuousLinearMap.snd ℝ ℝ ℝ) := by
    funext q; rfl
  rw [e, (ContinuousLinearMap.snd ℝ ℝ ℝ).iteratedFDeriv_comp_right
    (Real.contDiff_sin (n := 2)) p (by exact_mod_cast hi)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _j : Fin i, ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
  have hd : ‖iteratedFDeriv ℝ i Real.sin ((ContinuousLinearMap.snd ℝ ℝ ℝ) p)‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    interval_cases i
    · simpa [Real.norm_eq_abs] using Real.abs_sin_le_one p.2
    · simpa [Real.norm_eq_abs, Real.deriv_sin] using Real.abs_cos_le_one p.2
    · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, Real.deriv_sin,
        Real.deriv_cos']
      simpa [Real.norm_eq_abs] using Real.abs_sin_le_one p.2
  calc _ ≤ 1 * 1 :=
        mul_le_mul hd hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The field `F t x = sin x` on `ℝ` is `1`-Lipschitz, bounded by `1`, of class `C²` as a
function of `(t, x)`, with first and second derivatives bounded by `1`. -/
private theorem sin_field_aux :
    IsLipschitzField (fun (_ : ℝ) (x : ℝ) => Real.sin x) 1 ∧
      IsBoundedField (fun (_ : ℝ) (x : ℝ) => Real.sin x) 1 ∧
      ContDiff ℝ 2 (Function.uncurry fun (_ : ℝ) (x : ℝ) => Real.sin x) ∧
      (∀ p, ‖fderiv ℝ (Function.uncurry fun (_ : ℝ) (x : ℝ) => Real.sin x) p‖ ≤ 1) ∧
      ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry fun (_ : ℝ) (x : ℝ) => Real.sin x) p‖ ≤ 1 := by
  refine ⟨fun _ x y => ?_, fun _ x => ?_, ?_, fun p => ?_,
    fun p => norm_iteratedFDeriv_sin_snd_le_aux le_rfl p⟩
  · simpa [Real.norm_eq_abs] using Real.abs_sin_sub_sin_le x y
  · simpa [Real.norm_eq_abs] using Real.abs_sin_le_one x
  · exact Real.contDiff_sin.comp contDiff_snd
  · rw [← norm_iteratedFDeriv_one]
    exact norm_iteratedFDeriv_sin_snd_le_aux (by norm_num) p

/-- A midpoint BUG step whose projectors are all the identity: every substep is the exact
solution `z`, and the result lies within `ϑ` of its end value. -/
private theorem isMidpointBUGStep_one_aux {F : ℝ → E → E} {z : ℝ → E} {t₀ h ϑ : ℝ} (hh : 0 ≤ h)
    (hz : ODESolution F z t₀ (t₀ + h)) {Y₁ : E} (hY₁ : ‖Y₁ - z (t₀ + h)‖ ≤ ϑ) :
    MidpointBUG.IsMidpointBUGStep F 0 0 ϑ 1 1 1 1 1 t₀ h (z t₀) z z z z Y₁ where
  half :=
    { projP₀ := IsOrthProj.one
      projQ₀ := IsOrthProj.one
      projP₁ := IsOrthProj.one
      projQ₁ := IsOrthProj.one
      comm₁ := fun _ => rfl
      kSol := hz.mono le_rfl (by linarith)
      kStart := rfl
      kCap := rfl
      kNormal := fun _ _ => by simp
      lSol := hz.mono le_rfl (by linarith)
      lStart := rfl
      lCap := rfl
      lNormal := fun _ _ => by simp
      sSol := hz.mono le_rfl (by linarith)
      sStart := rfl }
  projR := IsOrthProj.one
  fix := rfl
  normal := by simp
  sSol := hz
  sStart := rfl
  trunc := hY₁

open MidpointBUG

/-- **Non-vacuity of `ODESolution.contDiffOn_three`**: for the field `F t x = sin x` on `ℝ`, the
solution from `3` on `[0, 1]` is `C³`. -/
example : ∃ y : ℝ → ℝ, ODESolution (fun _ x => Real.sin x) y 0 1 ∧ y 0 = 3 ∧
    ContDiffOn ℝ 3 y (Icc 0 1) := by
  obtain ⟨hL, hB, hF₂, -, -⟩ := sin_field_aux
  obtain ⟨y, hy, hy0⟩ := exists_ODESolution hL hB (fun _ => continuous_const) zero_le_one 3
  exact ⟨y, hy, hy0, hy.contDiffOn_three hF₂⟩

/-- **Non-vacuity of `ODESolution.norm_iteratedDerivWithin_three_le_of_contDiff`**: for the field
`F t x = sin x` on `ℝ` (`B = M₁ = M₂ = 1`), the solution from `3` on `[0, 1]` has
`‖y'''‖ ≤ 6`. -/
example : ∃ y : ℝ → ℝ, ODESolution (fun _ x => Real.sin x) y 0 1 ∧ y 0 = 3 ∧
    ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedDerivWithin 3 y (Icc 0 1) t‖ ≤ 6 := by
  obtain ⟨hL, hB, hF₂, hM₁, hM₂⟩ := sin_field_aux
  obtain ⟨y, hy, hy0⟩ := exists_ODESolution hL hB (fun _ => continuous_const) zero_le_one 3
  refine ⟨y, hy, hy0, fun t ht => ?_⟩
  exact (hy.norm_iteratedDerivWithin_three_le_of_contDiff hF₂ hB hM₁ hM₂ t ht).trans
    (by norm_num)

/-- **Non-vacuity of `IsMidpointBUGStep.norm_sub_le`**: for the field `F t x = sin x` on `ℝ`
(`L = B = 1`, `Lₜ = 0`, `M₃ = 6`), the midpoint BUG step with identity projectors from the exact
solution, whose result is moved by `ϑ > 0` in the truncation, satisfies the hypotheses. -/
example {h ϑ : ℝ} (hh : 0 < h) (hϑ : 0 < ϑ) :
    ∃ A : ℝ → ℝ, ODESolution (fun _ x => Real.sin x) A 0 (0 + h) ∧ A 0 = 3 ∧
      ‖(A (0 + h) + ϑ) - A (0 + h)‖ ≤ midpointBUGConst 1 0 1 6 h * h * (h ^ 2 + h * 0 + 0) + ϑ := by
  obtain ⟨hL, hB, hF₂, hM₁, hM₂⟩ := sin_field_aux
  obtain ⟨A, hA, hA0⟩ :=
    exists_ODESolution hL hB (fun _ => continuous_const) (by linarith : (0 : ℝ) ≤ 0 + h) 3
  refine ⟨A, hA, hA0, ?_⟩
  have hs := isMidpointBUGStep_one_aux hh.le hA (Y₁ := A (0 + h) + ϑ)
    (by rw [add_sub_cancel_left, Real.norm_eq_abs, abs_of_pos hϑ])
  have hM : ∀ t ∈ Icc 0 (0 + h), ‖iteratedDerivWithin 3 A (Icc 0 (0 + h)) t‖ ≤ 6 := by
    intro t ht
    exact (hA.norm_iteratedDerivWithin_three_le_of_contDiff hF₂ hB hM₁ hM₂ t ht).trans
      (by norm_num)
  exact hs.norm_sub_le hL zero_le_one hB (Lₜ := 0) (fun s t x => by simp) hh.le le_rfl hA rfl
    (hA.contDiffOn_three hF₂) hM

/-- **Non-vacuity of `IsMidpointBUGStep.hasLocalError`**: for the field `F t x = sin x` on `ℝ`
(`L = B = M₁ = M₂ = 1`), the midpoint BUG step with identity projectors along the exact solution
satisfies the hypotheses. -/
example {h : ℝ} (hh : 0 < h) :
    ∃ A : ℝ → ℝ, A 0 = 3 ∧ HasLocalError (fun _ x => Real.sin x) 0 (0 + h) (A 0) (A (0 + h))
      (midpointBUGConst 1 1 1 (1 * (1 + 1) ^ 2 + 1 ^ 2 * (1 + 1)) h * h * (h ^ 2 + h * 0 + 0)
        + 0) := by
  obtain ⟨hL, hB, hF₂, hM₁, hM₂⟩ := sin_field_aux
  obtain ⟨A, hA, hA0⟩ :=
    exists_ODESolution hL hB (fun _ => continuous_const) (by linarith : (0 : ℝ) ≤ 0 + h) 3
  have hs := isMidpointBUGStep_one_aux hh.le hA (Y₁ := A (0 + h)) (ϑ := 0) (by simp)
  exact ⟨A, hA0, hs.hasLocalError hL zero_le_one hB hF₂ hM₁ hM₂ hh.le le_rfl⟩

/-- **Non-vacuity of `midpointBUG_global_error_le`**: for the field `F t x = sin x` on `ℝ`
(`L = B = M₁ = M₂ = 1`, so `M₃ = 6`), the run of midpoint BUG steps with identity projectors along
the exact solution `z` from `4` satisfies the hypotheses with respect to the exact solution `y`
from `3` (initial error `δ = 1`, `ε = ε₂ = ϑ = 0`), and the bound reads
`‖z (n h) - y (n h)‖ ≤ e^T + T e^T C h²`. -/
example {h H T : ℝ} (hh : 0 < h) (hhH : h ≤ H) (N : ℕ) :
    ∃ y z : ℝ → ℝ, y 0 = 3 ∧ z 0 = 4 ∧ ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖z (n * h) - y (n * h)‖ ≤
        Real.exp T + T * Real.exp T * midpointBUGConst 1 1 1 6 H * h ^ 2 := by
  obtain ⟨hL, hB, hF₂, hM₁, hM₂⟩ := sin_field_aux
  have hN : (0 : ℝ) ≤ 0 + N * h := by positivity
  obtain ⟨y, hy, hy0⟩ := exists_ODESolution hL hB (fun _ => continuous_const) hN 3
  obtain ⟨z, hz, hz0⟩ := exists_ODESolution hL hB (fun _ => continuous_const) hN 4
  refine ⟨y, z, hy0, hz0, fun n hn hT => ?_⟩
  have hsub : ∀ k < N, 0 ≤ 0 + (k : ℝ) * h ∧ 0 + (k : ℝ) * h + h ≤ 0 + N * h := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
    constructor <;> nlinarith
  have hstep : ∀ k < N, IsMidpointBUGStep (fun _ x => Real.sin x) 0 0 0 1 1 1 1 1
      (0 + k * h) h (z (0 + k * h)) z z z z (z (0 + ((k + 1 : ℕ) : ℝ) * h)) := by
    intro k hk
    have e : (0 : ℝ) + ((k + 1 : ℕ) : ℝ) * h = 0 + k * h + h := by push_cast; ring
    refine isMidpointBUGStep_one_aux hh.le (hz.mono (hsub k hk).1 (hsub k hk).2) ?_
    rw [e, sub_self, norm_zero]
  have hΦ : ∀ k < N, ODESolution (fun _ x => Real.sin x) z (0 + k * h) (0 + (k + 1) * h) := by
    intro k hk
    have e : (0 : ℝ) + ((k : ℝ) + 1) * h = 0 + k * h + h := by ring
    rw [e]
    exact hz.mono (hsub k hk).1 (hsub k hk).2
  have key := midpointBUG_global_error_le hL zero_le_one hB hF₂ hM₁ hM₂ le_rfl le_rfl hh.le hhH
    hy (Y := fun k => z (0 + k * h)) (YK := fun _ => z) (YL := fun _ => z) (YH := fun _ => z)
    (YS := fun _ => z) (Φ := fun _ => z) hstep hΦ (fun _ _ => rfl) (δ := 1)
    (by simp [hz0, hy0]; norm_num) n hn hT
  have e6 : (1 : ℝ) * (1 + 1) ^ 2 + 1 ^ 2 * (1 + 1) = 6 := by norm_num
  rw [e6] at key
  simpa using key

end Examples

end LeanDLRA
