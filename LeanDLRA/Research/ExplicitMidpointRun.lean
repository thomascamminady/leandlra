import LeanDLRA.HighOrder.Defs
import LeanDLRA.HighOrder.MidpointBUGGlobal
import LeanDLRA.Integrators.Matrix.FlowDistance
import LeanDLRA.Integrators.Method
import LeanDLRA.Research.ExplicitMidpointGalerkin

/-!
# Runs of the explicit midpoint method in augmented bases: existence and second-order error

This file shows that the explicit midpoint step in bases with `2 r` columns, followed by a best
approximation of rank `r` (`ExplicitMidpoint.stepRel`), is a tube-local method
(`StepMethod.IsTubeLocal`), and that its runs are robustly of second order: the error after
`N` steps of size `h` is `O(h² + ε)` with constants that contain no inverse of a singular value.

**The step.** From `Y₀ = U₀ S₀ V₀ᵀ` with `r` orthonormal columns in `U₀`, `V₀`: the explicit
predictor `Z = Y₀ + (h/2) P₀ F(t₀, Y₀)`, `P₀ = tangentProj U₀ V₀`; one evaluation
`G = F(t₀ + h/2, Z)`; bases `Ua`, `Va` with `2 r` orthonormal columns whose ranges contain those
of `(U₀, G V₀)` and `(V₀, Gᵀ U₀)`; the update `Ȳ = Y₀ + h Ua Uaᵀ G Va Vaᵀ`; a best approximation
of `Ȳ` of rank at most `r`. Two evaluations of `F`, no differential equation.

**Setting.** As for the midpoint BUG integrator (`MatrixMidpointBUG.exists_run_norm_sub_le`): the
field `F` is `L`-Lipschitz and bounded by `B`, and the uncurried field is of class `C²` with
`‖DF‖ ≤ M₁` and `‖D²F‖ ≤ M₂`, everywhere; the normal part of `F` is at most `ε` at the factored
points with `r` columns of the tube of radius `ρ` around a solution `A` on `[t₀, t₀ + N h]`
(`FactoredNormalBoundOn`). No normal bound at rank `2 r` is needed.

**Result** (`ExplicitMidpoint.exists_run_norm_sub_le`). Let `0 < r`, `2 r ≤ m`, `2 r ≤ n`,
`0 ≤ h ≤ H`, `N h ≤ T`, and let `σ > 0` be the radius of the balls around the numerical values
on which the capture of the field by the bases is estimated
(`norm_capture_defect_le_sq_add`). For constants `C₁`, `C₂` above explicit expressions in
`r`, `L`, `B`, `M₁`, `M₂`, `H`, `σ` and `‖A t₀‖ + B T + ρ`, and under the smallness conditions
`h B/2 + D₁ h² + D₂ ε ≤ σ/2` and `e^{L T} δ + T e^{L T} (C₁ h² + C₂ ε) + 3 B h + σ < ρ`, every
start value `Y₀` of rank at most `r` with `‖Y₀ - A t₀‖ ≤ δ` starts a run `Y 0 = Y₀, …, Y N` of
rank at most `r` with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (C₁ h² + C₂ ε)`.

The same bound holds for every run (`ExplicitMidpoint.IsRun.norm_sub_le`).

## Main results

* `ODESolution.norm_iteratedDerivWithin_two_le_of_contDiff`: a solution of `y' = F(t, y)` with
  `F` of class `C²` satisfies `‖y''‖ ≤ M₁ (1 + B)`.
* `ExplicitMidpoint.exists_augmentedRel`, `ExplicitMidpoint.exists_stepRel`: steps exist from
  every matrix of rank at most `r`, for every field, if `2 r ≤ m` and `2 r ≤ n`.
* `ExplicitMidpoint.stepRel_tubeExt_iff_of_near`, `ExplicitMidpoint.isTubeLocal_stepRel`: near
  the reference solution the tube extension has the same steps as the field; the method is
  tube-local with margin constant `2`.
* `ExplicitMidpoint.stepRel.hasLocalError`: the local error `h (C₁ h² + C₂ ε)` of one step near
  the reference solution.
* `ExplicitMidpoint.IsRun.norm_sub_le`, `ExplicitMidpoint.exists_run_norm_sub_le`: the global
  error bound for every run, and the existence of a run.

## Implementation notes

The local error of the update before truncation is `ExplicitMidpoint.norm_update_sub_le_cube_add`;
its derivative bounds of the exact solution are obtained from `M₁`, `M₂`
(`ODESolution.norm_iteratedDerivWithin_two_le_of_contDiff`,
`ODESolution.norm_iteratedDerivWithin_three_le_of_contDiff`), and its region is the tube. The
capture constants contain `‖S₀‖ = ‖Y₀‖`, which is at most `‖A t₀‖ + B T + ρ` along a run. The
truncation costs the distance of the exact solution to the matrices of rank at most `r`, at most
`h ε e^{L h}` (`distLR_flow_le_exp_of_tube`), plus twice the error before truncation
(`norm_bestTrunc_sub_le`). The constants `κ`, `D₁`, `D₂`, `C₁`, `C₂` are parameters bounded
below by explicit expressions, as in `norm_capture_defect_le_sq_add`.

The regularity hypotheses on `F` are global, as for the midpoint BUG integrator; the tube enters
through the normal bound and the smallness conditions.

## References

* [KieriVandereycken2019], Theorem 6: robust second order of projected explicit Runge–Kutta
  methods of order two at rank `r`, the first robust second-order scheme.
* [CerutiEtAl2024b]: the midpoint BUG integrator, whose Galerkin space contains `U₀` and `G V₀`
  in the same way.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

/-! ### The second derivative of solutions for a field of class `C²` -/

section Regularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Second derivative of solutions for a field of class `C²`.** Let `F` be jointly of class
`C²` as a function of `(t, x)`, bounded by `B`, with `‖DF‖ ≤ M₁` everywhere (norms on `ℝ × E`
with the maximum norm). Then every solution of `y' = F(t, y)` on `[a, b]` satisfies
`‖y''‖ ≤ M₁ (1 + B)` on `[a, b]`, since `y'' = DF(1, F)` along the solution. -/
theorem ODESolution.norm_iteratedDerivWithin_two_le_of_contDiff {F : ℝ → E → E} {B M₁ : ℝ}
    (hF : ContDiff ℝ 2 (Function.uncurry F)) (hB : IsBoundedField F B)
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁) {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution F y a b) :
    ∀ t ∈ Icc a b, ‖iteratedDerivWithin 2 y (Icc a b) t‖ ≤ M₁ * (1 + B) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  rcases lt_trichotomy a b with hab | rfl | hba
  · have hU : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
    have h3 := hy.contDiffOn_three hF
    have hdiff : DifferentiableOn ℝ y (Icc a b) := h3.differentiableOn (by norm_num)
    have hgc : ContinuousOn (fun t => F t (y t)) (Icc a b) :=
      hF.continuous.comp_continuousOn (continuousOn_id.prodMk hy.cont)
    have hdc : ContinuousOn (derivWithin y (Icc a b)) (Icc a b) :=
      h3.continuousOn_derivWithin hU (by norm_num)
    -- the derivative within `[a, b]` is the field along the solution, also at `b`
    have heq : EqOn (derivWithin y (Icc a b)) (fun t => F t (y t)) (Icc a b) := by
      have hIco : EqOn (derivWithin y (Icc a b)) (fun t => F t (y t)) (Ico a b) := fun t ht =>
        hy.eq_field_of_hasDerivWithinAt (fun x hx => (hdiff x hx).hasDerivWithinAt) t ht
      exact hIco.of_subset_closure hdc hgc Ico_subset_Icc_self
        (fun x hx => by rwa [closure_Ico hab.ne])
    intro t ht
    have hy' : HasDerivWithinAt y (F t (y t)) (Icc a b) t := by
      have := (hdiff t ht).hasDerivWithinAt
      rwa [heq ht] at this
    have hFd : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (t, y t))
        (t, y t) := ((hF.differentiable (by norm_num)) (t, y t)).hasFDerivAt
    have hγ : HasDerivWithinAt (fun s => (s, y s)) ((1 : ℝ), F t (y t)) (Icc a b) t :=
      (hasDerivWithinAt_id t _).prodMk hy'
    have h0 : HasDerivWithinAt (fun s => F s (y s))
        (fderiv ℝ (Function.uncurry F) (t, y t) ((1 : ℝ), F t (y t))) (Icc a b) t :=
      HasFDerivAt.comp_hasDerivWithinAt (l := Function.uncurry F) t hFd hγ
    have h2 : iteratedDerivWithin 2 y (Icc a b) t =
        derivWithin (fun s => F s (y s)) (Icc a b) t := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDerivWithin_succ', iteratedDerivWithin_one]
      exact derivWithin_congr heq (heq ht)
    rw [h2, h0.derivWithin (hU t ht)]
    calc ‖fderiv ℝ (Function.uncurry F) (t, y t) ((1 : ℝ), F t (y t))‖
        ≤ ‖fderiv ℝ (Function.uncurry F) (t, y t)‖ * ‖((1 : ℝ), F t (y t))‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ M₁ * (1 + B) := by
        refine mul_le_mul (hM₁ _) ?_ (norm_nonneg _) hM₁0
        rw [Prod.norm_def]
        exact max_le (by rw [norm_one]; linarith) ((hB _ _).trans (by linarith))
  · intro t ht
    rw [Icc_self, mem_singleton_iff] at ht
    subst ht
    have hacc : ¬ AccPt t (Filter.principal {t}) := by
      rw [accPt_principal_iff_nhdsWithin, Set.sdiff_self, nhdsWithin_empty]; simp
    have : iteratedDerivWithin 2 y (Icc t t) t = 0 := by
      rw [Icc_self, show (2 : ℕ) = 1 + 1 from rfl, iteratedDerivWithin_succ]
      exact derivWithin_zero_of_not_accPt hacc
    rw [this, norm_zero]
    positivity
  · intro t ht
    rw [Icc_eq_empty hba.not_ge] at ht
    exact absurd ht (notMem_empty t)

/-- A field whose uncurried form has derivative bounded by `M₁` is `M₁`-Lipschitz in time. -/
private theorem norm_field_sub_le_of_norm_fderiv_le_aux {F : ℝ → E → E} {M₁ : ℝ}
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

namespace ExplicitMidpoint

/-! ### Existence of a step -/

section Exists

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {Y₀ Y₁ Yh : Matrix m n ℝ}

/-- An explicit midpoint step can only be started from a matrix of rank at most `r`. -/
theorem augmentedRel.rank_start_le (h : augmentedRel F r t₀ t₁ Y₀ Yh) : Y₀.rank ≤ r := by
  obtain ⟨U₀, S₀, V₀, Ua, Va, Z, G, -, -, rfl, -⟩ := h
  exact rank_mul_mul_transpose_le _ _ _

/-- **A step without truncation exists from every matrix of rank at most `r`**, for every field,
if `2 r ≤ m` and `2 r ≤ n`: factor `Y₀ = U₀ S₀ V₀ᵀ` with `r` orthonormal columns
(`exists_factor_of_rank_le`), evaluate the predictor and the field, and take orthonormal bases
with `2 r` columns whose ranges contain those of `(U₀, G V₀)` and `(V₀, Gᵀ U₀)`
(`exists_orthonormal_capture_fromCols`). No property of the field is needed: the step solves no
differential equation. -/
theorem exists_augmentedRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ)
    (hrm : 2 * r ≤ Fintype.card m) (hrn : 2 * r ≤ Fintype.card n) (hY₀ : Y₀.rank ≤ r) :
    ∃ Yh, augmentedRel F r t₀ t₁ Y₀ Yh := by
  classical
  obtain ⟨U₀, S₀, V₀, hU₀, hV₀, rfl⟩ := exists_factor_of_rank_le hY₀ (by omega) (by omega)
  set Z := U₀ * S₀ * V₀ᵀ + ((t₁ - t₀) / 2) • tangentProj U₀ V₀ (F t₀ (U₀ * S₀ * V₀ᵀ)) with hZ
  set G := F (t₀ + (t₁ - t₀) / 2) Z with hG
  have hUr : (Matrix.fromCols U₀ (G * V₀)).rank ≤ 2 * r := by
    have := (Matrix.fromCols U₀ (G * V₀)).rank_le_card_width
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  have hVr : (Matrix.fromCols V₀ (Gᵀ * U₀)).rank ≤ 2 * r := by
    have := (Matrix.fromCols V₀ (Gᵀ * U₀)).rank_le_card_width
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  obtain ⟨Ua, hUa, augU, kCap⟩ := exists_orthonormal_capture_fromCols U₀ (G * V₀) hUr hrm
  obtain ⟨Va, hVa, augV, lCap⟩ := exists_orthonormal_capture_fromCols V₀ (Gᵀ * U₀) hVr hrn
  exact ⟨_, U₀, S₀, V₀, Ua, Va, Z, G, hU₀, hV₀, rfl, hZ, hG, hUa, hVa, augU, augV, kCap, lCap,
    rfl⟩

/-- **The truncation exists.** Every result of the step without truncation has a best
approximation of rank at most `r`, so it can be completed to a step of
`ExplicitMidpoint.stepRel`. -/
theorem augmentedRel.exists_stepRel (h : augmentedRel F r t₀ t₁ Y₀ Yh) :
    ∃ Y₁, stepRel F r t₀ t₁ Y₀ Y₁ := by
  obtain ⟨Z, hZ, hd⟩ := exists_best_approx r Yh
  exact ⟨Z, Yh, h, hZ, by rw [norm_sub_rev, hd]⟩

/-- **A step of the explicit midpoint method with rank `r` exists from every matrix of rank at
most `r`**, for every field, if `2 r ≤ m` and `2 r ≤ n`. -/
theorem exists_stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ)
    (hrm : 2 * r ≤ Fintype.card m) (hrn : 2 * r ≤ Fintype.card n) (hY₀ : Y₀.rank ≤ r) :
    ∃ Y₁, stepRel F r t₀ t₁ Y₀ Y₁ := by
  obtain ⟨Yh, hYh⟩ := exists_augmentedRel F t₀ t₁ hrm hrn hY₀
  exact hYh.exists_stepRel

/-- The result of a step of the explicit midpoint method with rank `r` has rank at most `r`. -/
theorem stepRel.rank_le (h : stepRel F r t₀ t₁ Y₀ Y₁) : Y₁.rank ≤ r := by
  obtain ⟨Yh, -, hr, -⟩ := h
  exact hr

/-- A step of the explicit midpoint method with rank `r` can only be started from a matrix of
rank at most `r`. -/
theorem stepRel.rank_start_le (h : stepRel F r t₀ t₁ Y₀ Y₁) : Y₀.rank ≤ r := by
  obtain ⟨Yh, hYh, -, -⟩ := h
  exact hYh.rank_start_le

/-- All values of a run of the explicit midpoint method with rank `r` have rank at most `r`,
provided the start value has. -/
theorem IsRun.rank_le {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → Matrix m n ℝ}
    (hY : IsRun (stepRel F r) τ N Y) (h0 : (Y 0).rank ≤ r) : ∀ k ≤ N, (Y k).rank ≤ r
  | 0, _ => h0
  | k + 1, hk => (hY.step k hk).rank_le

end Exists

/-! ### Near the reference solution -/

section Tube

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {a b ρ B t₀ t₁ : ℝ}
  {Y₀ Y₁ Yh : Matrix m n ℝ}

/-- **The step sees the field only in the tube.** Let `F` be bounded by `B` on the tube of
radius `ρ` around a solution `A` over `[a, b] ⊇ [t₀, t₁]`, and let
`‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`. Then the tube extension `tubeExt F A a b ρ` agrees with `F` at
`(t₀, Y₀)` and, for all `U₀`, `V₀` with orthonormal columns, at the predictor
`Z = Y₀ + (h/2) P₀ F(t₀, Y₀)` at time `t₀ + h/2`, `h = t₁ - t₀`: the predictor moves at most
`B h/2` away from `Y₀`, and `A` at most `B h/2` away from `A t₀`. -/
theorem tubeExt_eq_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (ha : a ≤ t₀)
    (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) {k k' : Type*} [Fintype k] [Fintype k']
    [DecidableEq k] [DecidableEq k'] {U₀ : Matrix m k ℝ} {V₀ : Matrix n k' ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) :
    tubeExt F A a b ρ t₀ Y₀ = F t₀ Y₀ ∧
      tubeExt F A a b ρ (t₀ + (t₁ - t₀) / 2)
          (Y₀ + ((t₁ - t₀) / 2) • tangentProj U₀ V₀ (F t₀ Y₀)) =
        F (t₀ + (t₁ - t₀) / 2) (Y₀ + ((t₁ - t₀) / 2) • tangentProj U₀ V₀ (F t₀ Y₀)) := by
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hρ : 0 < ρ := by linarith [norm_nonneg (Y₀ - A t₀)]
  have hY₀ : ‖Y₀ - A t₀‖ ≤ ρ := by linarith
  have ht₀ : t₀ ∈ Icc a b := ⟨ha, h01.trans hb⟩
  have hFY : ‖F t₀ Y₀‖ ≤ B := hFB t₀ ht₀ Y₀ hY₀
  have hs : t₀ + (t₁ - t₀) / 2 ∈ Icc t₀ t₁ := ⟨by linarith, by linarith⟩
  have hAs : ‖A (t₀ + (t₁ - t₀) / 2) - A t₀‖ ≤ B * (t₀ + (t₁ - t₀) / 2 - t₀) :=
    hA.norm_sub_start_le_of_tube (A := A) (ρ := ρ)
      (fun t ht x hx => hFB t ⟨ha.trans ht.1, ht.2.le.trans hb⟩ x hx)
      (fun t _ => by rw [sub_self, norm_zero]; exact hρ) _ hs
  have hP : ‖((t₁ - t₀) / 2) • tangentProj U₀ V₀ (F t₀ Y₀)‖ ≤ (t₁ - t₀) / 2 * B := by
    rw [norm_smul, Real.norm_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_left (((isOrthProj_tangentProj hU₀ hV₀).norm_le _).trans hFY)
      (by linarith)
  have e : Y₀ + ((t₁ - t₀) / 2) • tangentProj U₀ V₀ (F t₀ Y₀) - A (t₀ + (t₁ - t₀) / 2) =
      (Y₀ - A t₀) + ((t₁ - t₀) / 2) • tangentProj U₀ V₀ (F t₀ Y₀) -
        (A (t₀ + (t₁ - t₀) / 2) - A t₀) := by abel
  have hZ : ‖Y₀ + ((t₁ - t₀) / 2) • tangentProj U₀ V₀ (F t₀ Y₀) - A (t₀ + (t₁ - t₀) / 2)‖ ≤
      ρ := by
    rw [e]
    have h1 := norm_sub_le ((Y₀ - A t₀) + ((t₁ - t₀) / 2) • tangentProj U₀ V₀ (F t₀ Y₀))
      (A (t₀ + (t₁ - t₀) / 2) - A t₀)
    have h2 := norm_add_le (Y₀ - A t₀) (((t₁ - t₀) / 2) • tangentProj U₀ V₀ (F t₀ Y₀))
    linarith
  exact ⟨tubeExt_eq ht₀ hY₀, tubeExt_eq ⟨ha.trans hs.1, hs.2.trans hb⟩ hZ⟩

/-- **Near the reference solution, the tube extension has the same steps without truncation as
the field**, if `‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ` (`ExplicitMidpoint.tubeExt_eq_of_near`). -/
theorem augmentedRel_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    augmentedRel (tubeExt F A a b ρ) r t₀ t₁ Y₀ Yh ↔ augmentedRel F r t₀ t₁ Y₀ Yh := by
  constructor
  · rintro ⟨U₀, S₀, V₀, Ua, Va, Z, G, hU₀, hV₀, hY₀, hZ, hG, hUa, hVa, augU, augV, kCap, lCap,
      rfl⟩
    obtain ⟨e₀, e₁⟩ := tubeExt_eq_of_near hFB hB ha hb h01 hA hsmall hU₀ hV₀
    rw [e₀] at hZ
    subst hZ
    rw [e₁] at hG
    exact ⟨U₀, S₀, V₀, Ua, Va, _, G, hU₀, hV₀, hY₀, rfl, hG, hUa, hVa, augU, augV, kCap, lCap,
      rfl⟩
  · rintro ⟨U₀, S₀, V₀, Ua, Va, Z, G, hU₀, hV₀, hY₀, hZ, hG, hUa, hVa, augU, augV, kCap, lCap,
      rfl⟩
    obtain ⟨e₀, e₁⟩ := tubeExt_eq_of_near hFB hB ha hb h01 hA hsmall hU₀ hV₀
    subst hZ
    rw [← e₁] at hG
    rw [← e₀] at hG
    exact ⟨U₀, S₀, V₀, Ua, Va, _, G, hU₀, hV₀, hY₀, rfl, hG, hUa, hVa, augU, augV, kCap, lCap,
      rfl⟩

/-- **Near the reference solution, the tube extension has the same steps as the field**, if
`‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`. -/
theorem stepRel_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    stepRel (tubeExt F A a b ρ) r t₀ t₁ Y₀ Y₁ ↔ stepRel F r t₀ t₁ Y₀ Y₁ :=
  ⟨fun ⟨Yh, h, hr⟩ => ⟨Yh, (augmentedRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 h, hr⟩,
    fun ⟨Yh, h, hr⟩ => ⟨Yh, (augmentedRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).2 h, hr⟩⟩

/-- **The explicit midpoint method with rank `r` is a tube-local method**
(`StepMethod.IsTubeLocal`), with the matrices of rank at most `r` as admissible values and
margin constant `2`, if `2 r ≤ m` and `2 r ≤ n`:

* a step exists from every matrix of rank at most `r`, for every field
  (`ExplicitMidpoint.exists_stepRel`);
* the result of a step has rank at most `r` (`ExplicitMidpoint.stepRel.rank_le`);
* if `‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, a step from `Y₀` of the extended field
  `tubeExt F A a b ρ` is a step of `F` (`ExplicitMidpoint.stepRel_tubeExt_iff_of_near`): the step
  evaluates the field at `Y₀` and at the predictor, and both lie in the tube. -/
theorem isTubeLocal_stepRel (hrm : 2 * r ≤ Fintype.card m) (hrn : 2 * r ≤ Fintype.card n) :
    StepMethod.IsTubeLocal (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => stepRel G r)
      (fun Y => Y.rank ≤ r) 2 where
  exists_step := fun _ _ _ hY₀ => exists_stepRel _ _ _ hrm hrn hY₀
  adm_of_step := fun _ _ hstep => hstep.rank_le
  step_of_tubeExt := fun hFB hB ha hb h01 hA _ hsmall hstep =>
    (stepRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 hstep

end Tube

/-! ### Local error -/

section Error

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ}
  {a b ρ L B M₁ M₂ ε H σ κ D₁ D₂ C₁ C₂ Λ t₀ t₁ : ℝ} {Y₀ Y₁ : Matrix m n ℝ}

/-- **Local error of a step of the explicit midpoint method with rank `r`, near a reference
solution.** Let `F` be `L`-Lipschitz (`L ≥ 0`) and bounded by `B` everywhere, let the uncurried
field be of class `C²` with `‖DF‖ ≤ M₁` and `‖D²F‖ ≤ M₂` everywhere, and let the normal part of
`F` be at most `ε ≥ 0` at the factored points with `r` columns of the tube of radius `ρ` around a
solution `A` over `[a, b] ⊇ [t₀, t₁]`. Let `0 < r`, `2 r ≤ m`, `2 r ≤ n`, `h = t₁ - t₀ ≤ H`,
`σ > 0`, `L̃ = max L (2 B/σ)`, and let `κ`, `D₁`, `D₂`, `C₁`, `C₂` be at least the expressions
below, with `Λ ≥ ‖Y₀‖`. If `h B/2 + D₁ h² + D₂ ε ≤ σ/2` and `‖Y₀ - A t₀‖ + 3 B h + σ < ρ`, then
every step of `ExplicitMidpoint.stepRel F r` from `Y₀` has local error `h (C₁ h² + C₂ ε)`.

The update before truncation has error `h³ K₁ + h ε (K₂ + L h/2)`
(`ExplicitMidpoint.norm_update_sub_le_cube_add`, with the derivative bounds `M₁ (1 + B)` and
`M₂ (1 + B)² + M₁² (1 + B)` of the exact solution and the time-Lipschitz constant `M₁`). The
truncation to rank `r` costs the distance `h ε e^{L h}` of the exact solution to the matrices of
rank at most `r` plus twice that error. The constants contain `‖Y₀‖` through `Λ`, and no inverse
of a singular value. -/
theorem stepRel.hasLocalError (hstep : stepRel F r t₀ t₁ Y₀ Y₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hF₂ : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε) (hε₀ : 0 ≤ ε)
    (hr : 0 < r) (hrm : 2 * r ≤ Fintype.card m) (hrn : 2 * r ≤ Fintype.card n)
    (hσ : 0 < σ) (hκ : Real.sqrt r * (1 / 2 + max L (2 * B / σ)) ≤ κ)
    (hD₁ : Real.sqrt r * H * max L (2 * B / σ) / 2 + (2 * κ * B + κ ^ 2 * Λ) / 4 +
      H * κ ^ 2 * B / 8 ≤ D₁)
    (hD₂ : Real.sqrt r * H * (1 + max L (2 * B / σ) / 2) ≤ D₂)
    (hC₁ : 2 * (2 * ((L + κ + H / 2 * L * κ) * D₁ + Real.sqrt r * max L (2 * B / σ) / 2 +
        κ * (L * B + M₁ + B * κ) / 4) + (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) / 24 +
        L * (M₁ * (1 + B)) / 8) ≤ C₁)
    (hC₂ : Real.exp (L * H) + 2 * (2 * ((L + κ + H / 2 * L * κ) * D₂ + 1 +
        Real.sqrt r * (1 + max L (2 * B / σ) / 2))) + L * H ≤ C₂)
    (hAc : ContinuousOn A (Icc a b)) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁)
    (hH : t₁ - t₀ ≤ H) (hA : ODESolution F A t₀ t₁) (hΛ : ‖Y₀‖ ≤ Λ)
    (hstepσ : (t₁ - t₀) / 2 * B + (D₁ * (t₁ - t₀) ^ 2 + D₂ * ε) ≤ σ / 2)
    (hnear : ‖Y₀ - A t₀‖ + 3 * B * (t₁ - t₀) + σ < ρ) :
    HasLocalError F t₀ t₁ Y₀ Y₁ ((t₁ - t₀) * (C₁ * (t₁ - t₀) ^ 2 + C₂ * ε)) := by
  intro Φ hΦ hΦ₀
  obtain ⟨Yh, hYh, -, htr⟩ := hstep
  have hY₀r : Y₀.rank ≤ r := hYh.rank_start_le
  have hB0 : 0 ≤ B := hB.nonneg
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB0 (sub_nonneg.2 h01)
  -- the distance of the exact solution to the matrices of rank at most `r`
  have hdist : distLR r (Φ t₁) ≤ (t₁ - t₀) * ε * Real.exp (L * (t₁ - t₀)) :=
    distLR_flow_le_exp_of_tube hε hε₀ (fun t _ x y _ _ => hF t x y) hL (fun t _ x _ => hB t x)
      hB0 hF₂.continuous.continuousOn hAc ha hb h01 hA hΦ (by rw [hΦ₀]; exact hY₀r)
      (by rw [hΦ₀]; linarith)
  have htrunc := norm_bestTrunc_sub_le (A₁ := Φ t₁) htr
  obtain ⟨U₀, S₀, V₀, Ua, Va, Z, G, hU₀, hV₀, rfl, hZ, hG, hUa, hVa, augU, augV, kCap, lCap,
    hYh'⟩ := hYh
  rcases h01.lt_or_eq with hlt | heq
  swap
  · -- a step of size zero is exact
    have e0 : t₁ - t₀ = 0 := sub_eq_zero.2 heq.symm
    rw [e0, zero_smul, add_zero] at hYh'
    have hd0 : distLR r (Φ t₀) = 0 := distLR_eq_zero_iff.2 (by rw [hΦ₀]; exact hY₀r)
    rw [← heq, hYh', ← hΦ₀, sub_self, norm_zero, mul_zero, add_zero, hd0] at htrunc
    rw [e0, zero_mul, ← heq]
    exact htrunc
  set h := t₁ - t₀ with hdef
  have hh : 0 < h := sub_pos.2 hlt
  have ht₁ : t₁ = t₀ + h := by rw [hdef]; ring
  have hΦ' : ODESolution F Φ t₀ (t₀ + h) := by rw [← ht₁]; exact hΦ
  -- the exact solutions move with speed at most `B`
  have hAt : ∀ t ∈ Icc t₀ t₁, ‖A t - A t₀‖ ≤ B * h := hA.norm_sub_start_le hB ht₁
  have hΦt : ∀ t ∈ Icc t₀ t₁, ‖Φ t - Φ t₀‖ ≤ B * h := hΦ.norm_sub_start_le hB ht₁
  -- the region of the capture estimates lies in the tube
  have hDσ : ∀ t ∈ Icc t₀ (t₀ + h), ∀ X, ‖X - U₀ * S₀ * V₀ᵀ‖ ≤ σ →
      (t, X) ∈ tubeSet A a b ρ := by
    intro t ht X hX
    rw [← ht₁] at ht
    refine ⟨⟨ha.trans ht.1, ht.2.trans hb⟩, ?_⟩
    have e : X - A t = (X - U₀ * S₀ * V₀ᵀ) + (U₀ * S₀ * V₀ᵀ - A t₀) - (A t - A t₀) := by abel
    change ‖X - A t‖ ≤ ρ
    rw [e]
    have h1 := norm_sub_le ((X - U₀ * S₀ * V₀ᵀ) + (U₀ * S₀ * V₀ᵀ - A t₀)) (A t - A t₀)
    have h2 := norm_add_le (X - U₀ * S₀ * V₀ᵀ) (U₀ * S₀ * V₀ᵀ - A t₀)
    linarith [hAt t ht]
  have hs : t₀ + h / 2 ∈ Icc t₀ t₁ := ⟨by linarith, by linarith⟩
  have hDA : (t₀ + h / 2, Φ (t₀ + h / 2)) ∈ tubeSet A a b ρ := by
    refine ⟨⟨ha.trans hs.1, hs.2.trans hb⟩, ?_⟩
    have e : Φ (t₀ + h / 2) - A (t₀ + h / 2) =
        (Φ (t₀ + h / 2) - Φ t₀) + (Φ t₀ - A t₀) - (A (t₀ + h / 2) - A t₀) := by abel
    change ‖Φ (t₀ + h / 2) - A (t₀ + h / 2)‖ ≤ ρ
    rw [e]
    have h1 := norm_sub_le ((Φ (t₀ + h / 2) - Φ t₀) + (Φ t₀ - A t₀)) (A (t₀ + h / 2) - A t₀)
    have h2 := norm_add_le (Φ (t₀ + h / 2) - Φ t₀) (Φ t₀ - A t₀)
    have hn : ‖Φ t₀ - A t₀‖ + 3 * B * h + σ < ρ := by rw [hΦ₀]; exact hnear
    linarith [hAt _ hs, hΦt _ hs]
  -- the core of `Y₀` has the norm of `Y₀`
  have hS₀ : ‖S₀‖ ≤ Λ := by
    rwa [Frobenius.norm_mul_transpose_of_orthonormal hV₀,
      Frobenius.norm_mul_of_orthonormal hU₀] at hΛ
  have hD₁' : Real.sqrt r * H * max L (2 * B / σ) / 2 + (2 * κ * B + κ ^ 2 * ‖S₀‖) / 4 +
      H * κ ^ 2 * B / 8 ≤ D₁ := by
    have := mul_le_mul_of_nonneg_left hS₀ (sq_nonneg κ)
    linarith
  -- the update before truncation
  have hupd := norm_update_sub_le_cube_add (D := tubeSet A a b ρ) (Lₜ := M₁) (ρ := σ)
    (M₂ := M₁ * (1 + B)) (M₃ := M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) hε
    (by intro t x y _ _; exact hF t x y) hL (by intro t x _; exact hB t x)
    (fun s t X _ _ => norm_field_sub_le_of_norm_fderiv_le_aux hF₂ hM₁ s t X)
    (by omega) (by omega) hU₀ hV₀ hh hH hσ hDσ hκ hD₁' hD₂ hstepσ hΦ' hΦ₀
    (hΦ'.contDiffOn_three hF₂) (hΦ'.norm_iteratedDerivWithin_two_le_of_contDiff hF₂ hB hM₁)
    (hΦ'.norm_iteratedDerivWithin_three_le_of_contDiff hF₂ hB hM₁ hM₂) hDA hZ hG hUa hVa augU
    augV kCap lCap
  rw [← hYh', ← ht₁] at hupd
  -- the truncation
  set K₁ := 2 * ((L + κ + H / 2 * L * κ) * D₁ + Real.sqrt r * max L (2 * B / σ) / 2 +
      κ * (L * B + M₁ + B * κ) / 4) + (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) / 24 +
      L * (M₁ * (1 + B)) / 8 with hK₁
  set K₂ := 2 * ((L + κ + H / 2 * L * κ) * D₂ + 1 +
      Real.sqrt r * (1 + max L (2 * B / σ) / 2)) with hK₂
  have hexp : h * ε * Real.exp (L * h) ≤ h * ε * Real.exp (L * H) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hH hL))
      (mul_nonneg hh.le hε₀)
  have p₁ : 0 ≤ h ^ 3 * (C₁ - 2 * K₁) := mul_nonneg (pow_nonneg hh.le 3) (by linarith)
  have p₂ : 0 ≤ h * ε * (C₂ - Real.exp (L * H) - 2 * K₂ - L * H) :=
    mul_nonneg (mul_nonneg hh.le hε₀) (by linarith)
  have p₃ : h * ε * (L * h) ≤ h * ε * (L * H) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH hL) (mul_nonneg hh.le hε₀)
  linarith

/-- Local error of one step of a uniform grid. Under the hypotheses of the run theorem, a step
of `ExplicitMidpoint.stepRel F r` over `[t₀ + k h, t₀ + (k + 1) h]`, `k < N`, `0 ≤ h ≤ H`,
`N h ≤ T`, whose start value `Z₀` satisfies `‖Z₀ - A (t₀ + k h)‖ + 3 B h + σ < ρ` has local error
`h (C₁ h² + C₂ ε)` (`ExplicitMidpoint.stepRel.hasLocalError`, with `Λ = ‖A t₀‖ + B T + ρ`). -/
private theorem stepRel.hasLocalError_uniformGrid {N k : ℕ} {h T : ℝ} {Z₀ Z₁ : Matrix m n ℝ}
    (hstep : stepRel F r (t₀ + k * h) (t₀ + (k + 1) * h) Z₀ Z₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hF₂ : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂)
    (hA : ODESolution F A t₀ (t₀ + N * h))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hr : 0 < r) (hrm : 2 * r ≤ Fintype.card m) (hrn : 2 * r ≤ Fintype.card n)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T) (hk : k < N)
    (hσ : 0 < σ) (hκ : Real.sqrt r * (1 / 2 + max L (2 * B / σ)) ≤ κ)
    (hD₁ : Real.sqrt r * H * max L (2 * B / σ) / 2 +
      (2 * κ * B + κ ^ 2 * (‖A t₀‖ + B * T + ρ)) / 4 + H * κ ^ 2 * B / 8 ≤ D₁)
    (hD₂ : Real.sqrt r * H * (1 + max L (2 * B / σ) / 2) ≤ D₂)
    (hC₁ : 2 * (2 * ((L + κ + H / 2 * L * κ) * D₁ + Real.sqrt r * max L (2 * B / σ) / 2 +
        κ * (L * B + M₁ + B * κ) / 4) + (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) / 24 +
        L * (M₁ * (1 + B)) / 8) ≤ C₁)
    (hC₂ : Real.exp (L * H) + 2 * (2 * ((L + κ + H / 2 * L * κ) * D₂ + 1 +
        Real.sqrt r * (1 + max L (2 * B / σ) / 2))) + L * H ≤ C₂)
    (hstepσ : h / 2 * B + (D₁ * h ^ 2 + D₂ * ε) ≤ σ / 2)
    (hnear : ‖Z₀ - A (t₀ + k * h)‖ + 3 * B * h + σ < ρ) :
    HasLocalError F (t₀ + k * h) (t₀ + (k + 1) * h) Z₀ Z₁ (h * (C₁ * h ^ 2 + C₂ * ε)) := by
  obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hk
  have hB0 : 0 ≤ B := hB.nonneg
  -- the start value is bounded through the reference solution
  have hΛ : ‖Z₀‖ ≤ ‖A t₀‖ + B * T + ρ := by
    have hAk := hA.norm_sub_start_le hB rfl (t₀ + k * h) ⟨ha, h01.trans hb⟩
    have hBT : B * (N * h) ≤ B * T := mul_le_mul_of_nonneg_left hNT hB0
    have e : Z₀ = (Z₀ - A (t₀ + k * h)) + (A (t₀ + k * h) - A t₀) + A t₀ := by abel
    rw [e]
    have h1 := norm_add_le ((Z₀ - A (t₀ + k * h)) + (A (t₀ + k * h) - A t₀)) (A t₀)
    have h2 := norm_add_le (Z₀ - A (t₀ + k * h)) (A (t₀ + k * h) - A t₀)
    have hσh : 0 ≤ 3 * B * h + σ :=
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB0) hh) hσ.le
    linarith
  have hloc := hstep.hasLocalError hF hL hB hF₂ hM₁ hM₂ hε hε₀ hr hrm hrn hσ hκ hD₁ hD₂ hC₁ hC₂
    hA.cont ha hb h01 (by rw [hsub]; exact hhH) (hA.mono ha hb) hΛ
    (by rw [hsub]; exact hstepσ) (by rw [hsub]; exact hnear)
  rwa [hsub] at hloc

/-- The constants `C₁`, `C₂` of the local error are nonnegative. -/
private theorem consts_nonneg_aux (hL : 0 ≤ L) (hB : 0 ≤ B) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hH : 0 ≤ H) (hΛ : 0 ≤ Λ) (hκ : Real.sqrt r * (1 / 2 + max L (2 * B / σ)) ≤ κ)
    (hD₁ : Real.sqrt r * H * max L (2 * B / σ) / 2 + (2 * κ * B + κ ^ 2 * Λ) / 4 +
      H * κ ^ 2 * B / 8 ≤ D₁)
    (hD₂ : Real.sqrt r * H * (1 + max L (2 * B / σ) / 2) ≤ D₂)
    (hC₁ : 2 * (2 * ((L + κ + H / 2 * L * κ) * D₁ + Real.sqrt r * max L (2 * B / σ) / 2 +
        κ * (L * B + M₁ + B * κ) / 4) + (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) / 24 +
        L * (M₁ * (1 + B)) / 8) ≤ C₁)
    (hC₂ : Real.exp (L * H) + 2 * (2 * ((L + κ + H / 2 * L * κ) * D₂ + 1 +
        Real.sqrt r * (1 + max L (2 * B / σ) / 2))) + L * H ≤ C₂) :
    0 ≤ C₁ ∧ 0 ≤ C₂ := by
  have hm : 0 ≤ max L (2 * B / σ) := hL.trans (le_max_left _ _)
  have hq : 0 ≤ Real.sqrt r := Real.sqrt_nonneg _
  have hκ0 : 0 ≤ κ := le_trans (mul_nonneg hq (by linarith)) hκ
  have hLκ : 0 ≤ L + κ + H / 2 * L * κ := by
    have := mul_nonneg (mul_nonneg hH hL) hκ0
    linarith
  have hD₂0 : 0 ≤ D₂ := le_trans (mul_nonneg (mul_nonneg hq hH) (by linarith)) hD₂
  have hD₁0 : 0 ≤ D₁ := by
    have h1 := mul_nonneg (mul_nonneg hq hH) hm
    have h3 := mul_nonneg (sq_nonneg κ) hΛ
    have h4 := mul_nonneg (mul_nonneg hH (sq_nonneg κ)) hB
    have h5 := mul_nonneg hκ0 hB
    linarith
  constructor
  · have h1 := mul_nonneg hLκ hD₁0
    have h2 := mul_nonneg hq hm
    have h3 := mul_nonneg hκ0 (add_nonneg (add_nonneg (mul_nonneg hL hB) hM₁) (mul_nonneg hB hκ0))
    have h4 := mul_nonneg hM₂ (sq_nonneg (1 + B))
    have h5 := mul_nonneg (sq_nonneg M₁) (by linarith : (0 : ℝ) ≤ 1 + B)
    have h6 := mul_nonneg hL (mul_nonneg hM₁ (by linarith : (0 : ℝ) ≤ 1 + B))
    linarith
  · have h1 := mul_nonneg hLκ hD₂0
    have h2 := mul_nonneg hq (by linarith : (0 : ℝ) ≤ 1 + max L (2 * B / σ) / 2)
    have h3 := Real.exp_pos (L * H)
    have h4 := mul_nonneg hL hH
    linarith

/-- **Every run of the explicit midpoint method with rank `r` satisfies the second-order error
bound.** Let `F` be `L`-Lipschitz (`L ≥ 0`) and bounded by `B`, and let the uncurried field be of
class `C²` with `‖DF‖ ≤ M₁` and `‖D²F‖ ≤ M₂`, everywhere. Let `A` solve `Y' = F(t, Y)` on
`[t₀, t₀ + N h]`, and let the normal part of `F` be at most `ε ≥ 0` at the factored points with
`r` columns of the tube of radius `ρ ≥ 0` around `A`. Let `0 < r`, `2 r ≤ m`, `2 r ≤ n`,
`0 ≤ h ≤ H`, `N h ≤ T`, `σ > 0`, `L̃ = max L (2B/σ)`, and let `κ`, `D₁`, `D₂`, `C₁`, `C₂` be at
least the expressions in the hypotheses, which contain `r`, `L`, `B`, `M₁`, `M₂`, `H`, `σ` and
`‖A t₀‖ + B T + ρ`. Let `Y 0, …, Y N` be a run with `‖Y 0 - A t₀‖ ≤ δ`. If
`h B/2 + D₁ h² + D₂ ε ≤ σ/2` and `e^{L T} δ + T e^{L T} (C₁ h² + C₂ ε) + 3 B h + σ < ρ`, then for
all `n ≤ N`

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (C₁ h² + C₂ ε)`.

The constants contain no inverse of a singular value of the `Y n`. -/
theorem IsRun.norm_sub_le {N : ℕ} {h T δ : ℝ} {Y : ℕ → Matrix m n ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hF₂ : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂)
    (hA : ODESolution F A t₀ (t₀ + N * h))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (hr : 0 < r) (hrm : 2 * r ≤ Fintype.card m) (hrn : 2 * r ≤ Fintype.card n)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hσ : 0 < σ) (hκ : Real.sqrt r * (1 / 2 + max L (2 * B / σ)) ≤ κ)
    (hD₁ : Real.sqrt r * H * max L (2 * B / σ) / 2 +
      (2 * κ * B + κ ^ 2 * (‖A t₀‖ + B * T + ρ)) / 4 + H * κ ^ 2 * B / 8 ≤ D₁)
    (hD₂ : Real.sqrt r * H * (1 + max L (2 * B / σ) / 2) ≤ D₂)
    (hC₁ : 2 * (2 * ((L + κ + H / 2 * L * κ) * D₁ + Real.sqrt r * max L (2 * B / σ) / 2 +
        κ * (L * B + M₁ + B * κ) / 4) + (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) / 24 +
        L * (M₁ * (1 + B)) / 8) ≤ C₁)
    (hC₂ : Real.exp (L * H) + 2 * (2 * ((L + κ + H / 2 * L * κ) * D₂ + 1 +
        Real.sqrt r * (1 + max L (2 * B / σ) / 2))) + L * H ≤ C₂)
    (hstepσ : h / 2 * B + (D₁ * h ^ 2 + D₂ * ε) ≤ σ / 2)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) * (C₁ * h ^ 2 + C₂ * ε) +
      3 * B * h + σ < ρ)
    (hY : IsRun (stepRel F r) (uniformGrid t₀ h) N Y) (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (L * T) * δ + T * Real.exp (L * T) * (C₁ * h ^ 2 + C₂ * ε) := by
  have hB0 : 0 ≤ B := hB.nonneg
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg N) hh).trans hNT
  obtain ⟨hC₁0, hC₂0⟩ := consts_nonneg_aux hL hB0 ((norm_nonneg _).trans (hM₁ 0))
    ((norm_nonneg _).trans (hM₂ 0)) (hh.trans hhH)
    (add_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg hB0 hT)) hρ) hκ hD₁ hD₂ hC₁ hC₂
  have hc₀ : 0 ≤ C₁ * h ^ 2 + C₂ * ε :=
    add_nonneg (mul_nonneg hC₁0 (sq_nonneg h)) (mul_nonneg hC₂0 hε₀)
  refine hY.norm_sub_le_of_tube_uniformGrid (T := T) (δ₀ := δ)
    (DLRAProblem.of_global hF hL hB hA ρ) hF₂.continuous.continuousOn
    (fun k hk Z₀ Z₁ hnear hstep => ?_) hc₀ hδ hNT (by linarith [mul_nonneg hB0 hh])
  exact hstep.hasLocalError_uniformGrid hF hL hB hF₂ hM₁ hM₂ hA hε hε₀ hr hrm hrn hh hhH hNT hk
    hσ hκ hD₁ hD₂ hC₁ hC₂ hstepσ (by linarith)

/-- **Existence and second-order error bound for the explicit midpoint method with rank `r`.**
Under the hypotheses of `ExplicitMidpoint.IsRun.norm_sub_le` (with `ρ ≥ 0`), every start value
`Y₀` of rank at most `r` with `‖Y₀ - A t₀‖ ≤ δ` starts a run: there are `Y 0 = Y₀, Y 1, …, Y N`,
each obtained from the previous one by an explicit midpoint step of size `h` in bases with `2 r`
columns followed by a best approximation of rank at most `r`, all of rank at most `r`, with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (C₁ h² + C₂ ε)`

for all `n ≤ N`. The error is of order `h² + ε`, with constants that contain no inverse of a
singular value. Robust second order at rank `r` was first proved for projected Runge–Kutta
methods ([KieriVandereycken2019], Theorem 6). This is
`StepMethod.IsTubeLocal.exists_run_norm_sub_le` for the tube-local method
`ExplicitMidpoint.isTubeLocal_stepRel` with margin constant `3`. -/
theorem exists_run_norm_sub_le {N : ℕ} {h T δ : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hF₂ : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂)
    (hA : ODESolution F A t₀ (t₀ + N * h))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (hr : 0 < r) (hrm : 2 * r ≤ Fintype.card m) (hrn : 2 * r ≤ Fintype.card n)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hσ : 0 < σ) (hκ : Real.sqrt r * (1 / 2 + max L (2 * B / σ)) ≤ κ)
    (hD₁ : Real.sqrt r * H * max L (2 * B / σ) / 2 +
      (2 * κ * B + κ ^ 2 * (‖A t₀‖ + B * T + ρ)) / 4 + H * κ ^ 2 * B / 8 ≤ D₁)
    (hD₂ : Real.sqrt r * H * (1 + max L (2 * B / σ) / 2) ≤ D₂)
    (hC₁ : 2 * (2 * ((L + κ + H / 2 * L * κ) * D₁ + Real.sqrt r * max L (2 * B / σ) / 2 +
        κ * (L * B + M₁ + B * κ) / 4) + (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) / 24 +
        L * (M₁ * (1 + B)) / 8) ≤ C₁)
    (hC₂ : Real.exp (L * H) + 2 * (2 * ((L + κ + H / 2 * L * κ) * D₂ + 1 +
        Real.sqrt r * (1 + max L (2 * B / σ) / 2))) + L * H ≤ C₂)
    (hstepσ : h / 2 * B + (D₁ * h ^ 2 + D₂ * ε) ≤ σ / 2)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) * (C₁ * h ^ 2 + C₂ * ε) +
      3 * B * h + σ < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * δ + T * Real.exp (L * T) * (C₁ * h ^ 2 + C₂ * ε) := by
  have hB0 : 0 ≤ B := hB.nonneg
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg N) hh).trans hNT
  obtain ⟨hC₁0, hC₂0⟩ := consts_nonneg_aux hL hB0 ((norm_nonneg _).trans (hM₁ 0))
    ((norm_nonneg _).trans (hM₂ 0)) (hh.trans hhH)
    (add_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg hB0 hT)) hρ) hκ hD₁ hD₂ hC₁ hC₂
  have hc₀ : 0 ≤ C₁ * h ^ 2 + C₂ * ε :=
    add_nonneg (mul_nonneg hC₁0 (sq_nonneg h)) (mul_nonneg hC₂0 hε₀)
  refine ((isTubeLocal_stepRel hrm hrn).mono (by norm_num : (2 : ℝ) ≤ 3)).exists_run_norm_sub_le
    (by norm_num) (DLRAProblem.of_global hF hL hB hA ρ) hF₂.continuous.continuousOn
    (fun k hk Z₀ Z₁ _ hnear hstep => ?_) hc₀ hh hNT hY₀ hδ (by linarith)
  exact hstep.hasLocalError_uniformGrid hF hL hB hF₂ hM₁ hM₂ hA hε hε₀ hr hrm hrn hh hhH hNT hk
    hσ hκ hD₁ hD₂ hC₁ hC₂ hstepσ (by linarith)

end Error

/-! ### Non-vacuity: the constant field `G = Matrix.single 0 1 1` on `2 × 2` matrices -/

section Examples

/-- The matrix `Matrix.single 0 1 1` of the examples has norm at most one. -/
private theorem norm_single_le_one :
    ‖(Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤ 1 := by
  have h2 : ‖(Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℝ)‖ ^ 2 = 1 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp only [Fin.sum_univ_two, Matrix.single_apply]
    norm_num [Fin.ext_iff]
  nlinarith [norm_nonneg (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℝ)]

/-- The normal part of the constant field `Matrix.single 0 1 1` is at most one everywhere. -/
private theorem factoredNormalBoundOn_single (D : Set (ℝ × Matrix (Fin 2) (Fin 2) ℝ)) :
    FactoredNormalBoundOn (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) =>
      (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℝ)) 1 D 1 :=
  (factoredNormalBound_iff_univ.1 (MatrixBUG.factoredNormalBound_const _ 1)).mono
    (subset_univ _) norm_single_le_one

/-- The derivative of a constant field vanishes. -/
private theorem norm_fderiv_const_le (G : Matrix (Fin 2) (Fin 2) ℝ)
    (p : ℝ × Matrix (Fin 2) (Fin 2) ℝ) :
    ‖fderiv ℝ (Function.uncurry fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => G) p‖ ≤ 0 := by
  change ‖fderiv ℝ (fun _ : ℝ × Matrix (Fin 2) (Fin 2) ℝ => G) p‖ ≤ 0
  simp

/-- The second derivative of a constant field vanishes. -/
private theorem norm_iteratedFDeriv_const_le (G : Matrix (Fin 2) (Fin 2) ℝ)
    (p : ℝ × Matrix (Fin 2) (Fin 2) ℝ) :
    ‖iteratedFDeriv ℝ 2 (Function.uncurry fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => G) p‖ ≤
      0 := by
  change ‖iteratedFDeriv ℝ 2 (fun _ : ℝ × Matrix (Fin 2) (Fin 2) ℝ => G) p‖ ≤ 0
  rw [iteratedFDeriv_const_of_ne (n := 2) (by norm_num) G]
  simp

private theorem sqrt_one_cast : Real.sqrt ((1 : ℕ) : ℝ) = 1 := by simp

/-- **Non-vacuity of `ODESolution.norm_iteratedDerivWithin_two_le_of_contDiff`**: the solution
`t ↦ t G` of the constant field `G` on `[0, 1]`, with `B = ‖G‖` and `M₁ = 0`. -/
example (G : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedDerivWithin 2
      (fun t : ℝ => (0 : Matrix (Fin 2) (Fin 2) ℝ) + (t - 0) • G) (Icc 0 1) t‖ ≤
        0 * (1 + ‖G‖) :=
  ODESolution.norm_iteratedDerivWithin_two_le_of_contDiff contDiff_const (fun _ _ => le_rfl)
    (norm_fderiv_const_le G) (MatrixBUG.odeSolution_affine (0 : Matrix (Fin 2) (Fin 2) ℝ) G 0 1)

/-- **Non-vacuity of the existence theorems** (`ExplicitMidpoint.exists_augmentedRel`,
`ExplicitMidpoint.augmentedRel.exists_stepRel`, `ExplicitMidpoint.stepRel.rank_le`,
`ExplicitMidpoint.stepRel.rank_start_le`): from `Y₀ = 0` a step of the explicit midpoint method
with rank one exists for every field on `2 × 2` matrices and every step interval. -/
example (F : ℝ → Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) (t₀ t₁ : ℝ) :
    ∃ Yh Y₁ : Matrix (Fin 2) (Fin 2) ℝ, augmentedRel F 1 t₀ t₁ 0 Yh ∧
      stepRel F 1 t₀ t₁ 0 Y₁ ∧ (0 : Matrix (Fin 2) (Fin 2) ℝ).rank ≤ 1 ∧ Y₁.rank ≤ 1 := by
  obtain ⟨Yh, hYh⟩ := exists_augmentedRel F t₀ t₁ (r := 1) (by simp) (by simp)
    (by simp : (0 : Matrix (Fin 2) (Fin 2) ℝ).rank ≤ 1)
  obtain ⟨Y₁, hY₁⟩ := hYh.exists_stepRel
  exact ⟨Yh, Y₁, hYh, hY₁, hY₁.rank_start_le, hY₁.rank_le⟩

/-- **Non-vacuity of the tube theorems** (`ExplicitMidpoint.isTubeLocal_stepRel`,
`ExplicitMidpoint.tubeExt_eq_of_near`, `ExplicitMidpoint.augmentedRel_tubeExt_iff_of_near`,
`ExplicitMidpoint.stepRel_tubeExt_iff_of_near`): the method with rank one on `2 × 2` matrices is
tube-local; for a constant field `G`, its solution `t ↦ t G`, the tube of radius `2 ‖G‖ + 1`
over `[0, 1]` and the start value `0`, the tube extension agrees with the field at the start value
and has the same steps. -/
example (G Yh Y₁ : Matrix (Fin 2) (Fin 2) ℝ) :
    StepMethod.IsTubeLocal (fun F : ℝ → Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ =>
      stepRel F 1) (fun Y => Y.rank ≤ 1) 2 ∧
    tubeExt (fun _ _ => G) (fun t => (0 : Matrix (Fin 2) (Fin 2) ℝ) + (t - 0) • G) 0 1
      (2 * ‖G‖ + 1) 0 0 = G ∧
    (augmentedRel (tubeExt (fun _ _ => G) (fun t => (0 : Matrix (Fin 2) (Fin 2) ℝ) + (t - 0) • G)
      0 1 (2 * ‖G‖ + 1)) 1 0 1 0 Yh ↔ augmentedRel (fun _ _ => G) 1 0 1 0 Yh) ∧
    (stepRel (tubeExt (fun _ _ => G) (fun t => (0 : Matrix (Fin 2) (Fin 2) ℝ) + (t - 0) • G)
      0 1 (2 * ‖G‖ + 1)) 1 0 1 0 Y₁ ↔ stepRel (fun _ _ => G) 1 0 1 0 Y₁) := by
  have hFB : IsBoundedOnTube (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => G)
      (fun t => (0 : Matrix (Fin 2) (Fin 2) ℝ) + (t - 0) • G) 0 1 (2 * ‖G‖ + 1) ‖G‖ :=
    fun _ _ _ _ => le_rfl
  have hA := MatrixBUG.odeSolution_affine (0 : Matrix (Fin 2) (Fin 2) ℝ) G 0 1
  have hs : ‖(0 : Matrix (Fin 2) (Fin 2) ℝ) -
      ((0 : Matrix (Fin 2) (Fin 2) ℝ) + ((0 : ℝ) - 0) • G)‖ + 2 * ‖G‖ * (1 - 0) <
      2 * ‖G‖ + 1 := by simp
  exact ⟨isTubeLocal_stepRel (by simp) (by simp),
    (tubeExt_eq_of_near hFB (norm_nonneg G) le_rfl le_rfl zero_le_one hA hs
      (U₀ := (1 : Matrix (Fin 2) (Fin 2) ℝ)) (V₀ := (1 : Matrix (Fin 2) (Fin 2) ℝ)) (by simp)
      (by simp)).1,
    augmentedRel_tubeExt_iff_of_near hFB (norm_nonneg G) le_rfl le_rfl zero_le_one hA hs,
    stepRel_tubeExt_iff_of_near hFB (norm_nonneg G) le_rfl le_rfl zero_le_one hA hs⟩

/-- **Non-vacuity of `ExplicitMidpoint.stepRel.hasLocalError`**: a step from `0` of size `1/100`
for the constant field `G = Matrix.single 0 1 1` (`L = M₁ = M₂ = 0`, `B = ε = 1`), on the tube of
radius `5` around `t ↦ t G` over `[0, 1/100]`, with `H = 1/100`, `σ = 4`, `κ = 1`, `D₁ = 2`,
`D₂ = 1/50`, `C₁ = 10`, `C₂ = 11`, `Λ = 5`, exists and has local error
`(1/100) (10 (1/100)² + 11)`. -/
example : ∃ Y₁ : Matrix (Fin 2) (Fin 2) ℝ,
    stepRel (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) =>
      (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 (1 / 100) 0 Y₁ ∧
    HasLocalError (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) =>
      (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 (1 / 100) 0 Y₁
      ((1 / 100 - 0) * (10 * (1 / 100 - 0) ^ 2 + 11 * 1)) := by
  obtain ⟨Y₁, hY₁⟩ := exists_stepRel (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) =>
    (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 (1 / 100) (r := 1) (by simp) (by simp)
    (by simp : (0 : Matrix (Fin 2) (Fin 2) ℝ).rank ≤ 1)
  refine ⟨Y₁, hY₁, hY₁.hasLocalError (L := 0) (B := 1) (M₁ := 0) (M₂ := 0) (ε := 1)
    (H := 1 / 100) (σ := 4) (κ := 1) (D₁ := 2) (D₂ := 1 / 50) (C₁ := 10) (C₂ := 11) (Λ := 5)
    (a := 0) (b := 1 / 100) (ρ := 5)
    (A := fun t => (0 : Matrix (Fin 2) (Fin 2) ℝ) + (t - 0) • Matrix.single 0 1 1)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => norm_single_le_one) contDiff_const
    (norm_fderiv_const_le _) (norm_iteratedFDeriv_const_le _) (factoredNormalBoundOn_single _)
    zero_le_one (by norm_num) (by simp) (by simp) (by norm_num)
    (by rw [sqrt_one_cast]; norm_num [max_def]) (by rw [sqrt_one_cast]; norm_num [max_def])
    (by rw [sqrt_one_cast]; norm_num [max_def]) (by rw [sqrt_one_cast]; norm_num [max_def])
    (by rw [sqrt_one_cast]; norm_num [max_def]) (MatrixBUG.odeSolution_affine _ _ _ _).cont
    le_rfl le_rfl (by norm_num) (by norm_num) (MatrixBUG.odeSolution_affine _ _ _ _) (by simp)
    (by norm_num) (by norm_num)⟩

/-- **Non-vacuity of `ExplicitMidpoint.exists_run_norm_sub_le`, with two steps.** The constant
field `F(t, Y) = G`, `G = Matrix.single 0 1 1` on `2 × 2` matrices, is `0`-Lipschitz, bounded by
`1`, of class `C²` with vanishing derivatives (`M₁ = M₂ = 0`), and its normal part at every
factored matrix is at most `‖G‖ ≤ 1`, so `ε = 1`. With rank `r = 1`, the exact solution
`A t = t G`, the start value `Y₀ = 0`, the step size `h = H = 1/100`, `N = 2` steps, `T = 1/50`,
and the constants `σ = 4`, `κ = 1`, `D₁ = 2`, `D₂ = 1/50`, `C₁ = 10`, `C₂ = 11`, `ρ = 5`, all
hypotheses hold: a run of the explicit midpoint method exists, has rank at most one and stays
within `1/4` of the exact solution. -/
example : ∃ Y : ℕ → Matrix (Fin 2) (Fin 2) ℝ, Y 0 = 0 ∧
    IsRun (stepRel (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) =>
      (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℝ)) 1) (uniformGrid 0 (1 / 100)) 2 Y ∧
    ∀ j ≤ 2, (Y j).rank ≤ 1 ∧
      ‖Y j - ((j : ℝ) / 100) • (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤ 1 / 4 := by
  obtain ⟨Y, hY0, hY, hbd⟩ := exists_run_norm_sub_le
    (F := fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) =>
      (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℝ))
    (A := fun t => (0 : Matrix (Fin 2) (Fin 2) ℝ) + (t - 0) • Matrix.single 0 1 1) (r := 1)
    (t₀ := 0) (h := 1 / 100) (N := 2) (T := 1 / 50) (L := 0) (B := 1) (M₁ := 0) (M₂ := 0)
    (ε := 1) (H := 1 / 100) (σ := 4) (κ := 1) (D₁ := 2) (D₂ := 1 / 50) (C₁ := 10) (C₂ := 11)
    (ρ := 5) (δ := 0) (Y₀ := 0)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => norm_single_le_one) contDiff_const
    (norm_fderiv_const_le _) (norm_iteratedFDeriv_const_le _)
    (MatrixBUG.odeSolution_affine _ _ _ _) (factoredNormalBoundOn_single _) zero_le_one
    (by norm_num) (by norm_num) (by simp) (by simp) (by norm_num) le_rfl (by norm_num)
    (by norm_num) (by rw [sqrt_one_cast]; norm_num [max_def])
    (by rw [sqrt_one_cast]; norm_num [max_def]) (by rw [sqrt_one_cast]; norm_num [max_def])
    (by rw [sqrt_one_cast]; norm_num [max_def]) (by rw [sqrt_one_cast]; norm_num [max_def])
    (by norm_num) (by simp) (by simp) (by norm_num)
  refine ⟨Y, hY0, hY, fun j hj => ⟨(hbd j hj).1, ?_⟩⟩
  have hj' := (hbd j hj).2
  simp only [zero_add, sub_zero] at hj'
  have e : (j : ℝ) / 100 = (j : ℝ) * (1 / 100) := by ring
  rw [e]
  exact hj'.trans (by norm_num)

/-- **Non-vacuity of `ExplicitMidpoint.IsRun.norm_sub_le`**: every run of two steps of size
`1/100` from `0` for the constant field `G = Matrix.single 0 1 1` stays within `1/4` of
`t ↦ t G`, with the constants of the previous example (such runs exist, by that example). -/
example {Y : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (hY : IsRun (stepRel (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) =>
      (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℝ)) 1) (uniformGrid 0 (1 / 100)) 2 Y)
    (hY0 : Y 0 = 0) :
    ∀ j ≤ 2, ‖Y j - ((j : ℝ) / 100) • (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤
      1 / 4 := by
  intro j hj
  have hj' := ExplicitMidpoint.IsRun.norm_sub_le
    (A := fun t => (0 : Matrix (Fin 2) (Fin 2) ℝ) + (t - 0) • Matrix.single 0 1 1) (r := 1)
    (t₀ := 0) (h := 1 / 100) (N := 2) (T := 1 / 50) (L := 0) (B := 1) (M₁ := 0) (M₂ := 0)
    (ε := 1) (H := 1 / 100) (σ := 4) (κ := 1) (D₁ := 2) (D₂ := 1 / 50) (C₁ := 10) (C₂ := 11)
    (ρ := 5) (δ := 0)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => norm_single_le_one) contDiff_const
    (norm_fderiv_const_le _) (norm_iteratedFDeriv_const_le _)
    (MatrixBUG.odeSolution_affine _ _ _ _) (factoredNormalBoundOn_single _) zero_le_one
    (by norm_num) (by norm_num) (by simp) (by simp) (by norm_num) le_rfl (by norm_num)
    (by norm_num) (by rw [sqrt_one_cast]; norm_num [max_def])
    (by rw [sqrt_one_cast]; norm_num [max_def]) (by rw [sqrt_one_cast]; norm_num [max_def])
    (by rw [sqrt_one_cast]; norm_num [max_def]) (by rw [sqrt_one_cast]; norm_num [max_def])
    (by norm_num) (by norm_num) hY (by simp [hY0]) j hj
  simp only [zero_add, sub_zero] at hj'
  have e : (j : ℝ) / 100 = (j : ℝ) * (1 / 100) := by ring
  rw [e]
  exact hj'.trans (by norm_num)

end Examples

end ExplicitMidpoint

end LeanDLRA
