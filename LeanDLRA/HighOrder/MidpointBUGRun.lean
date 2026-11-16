import LeanDLRA.HighOrder.MidpointBUGStep

/-!
# Runs of the fixed-rank midpoint BUG integrator: existence and second-order error bound

This file shows that the midpoint basis-update & Galerkin (BUG) integrator with a fixed rank
(Ceruti, Einkemmer, Kusch and Lubich, arXiv:2402.08607, §3, Algorithm 1, the 4r variant,
followed by a best approximation of rank `r`) can be run for a matrix differential equation
`Y' = F(t, Y)`, and that every run is robustly of second order. The step relation and its local
error are in `LeanDLRA/HighOrder/MidpointBUGStep.lean`; the error analysis at the level of
orthogonal projectors, on which the local error rests, is in
`LeanDLRA/HighOrder/MidpointBUG.lean` and `LeanDLRA/HighOrder/MidpointBUGGlobal.lean`.

**Setting.** The field `F` is `L`-Lipschitz and bounded by `B`, and the uncurried field
`(t, Y) ↦ F(t, Y)` is of class `C²` with `‖DF‖ ≤ M₁` and `‖D²F‖ ≤ M₂`, everywhere. Let `A` be a
solution of `Y' = F(t, Y)` on `[t₀, t₀ + N h]`. The normal part of the field is small only near
`A`: for every `Y = U S Vᵀ` in the tube of radius `ρ` around `A` with orthonormal `U`, `V`, the
part `(I - U Uᵀ) F(t, Y) (I - V Vᵀ)` has norm at most `ε` if `U`, `V` have `r` columns and at
most `ε₂` if they have `2 r` columns (`FactoredNormalBoundOn`).

**Result** (`MatrixMidpointBUG.exists_run_norm_sub_le`). Let `2 r ≤ m`, `2 r ≤ n`,
`0 ≤ h ≤ H` and `N h ≤ T`. For every start value `Y₀` of rank at most `r` with
`‖Y₀ - A t₀‖ ≤ δ` there are matrices `Y 0 = Y₀, Y 1, …, Y N`, each obtained from the previous
one by a midpoint BUG step of size `h` followed by a best approximation of rank at most `r`, all
of rank at most `r`, with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (e^{L H} ε + 2 C (h² + h ε + ε₂))`,

`C = midpointBUGConst L M₁ B (M₂ (1 + B)² + M₁² (1 + B)) H`, provided the right-hand side plus
`3 B h` is smaller than `ρ`. The constants depend on `L`, `B`, `M₁`, `M₂`, `T`, `H` only, not on
the singular values of the matrices `Y n`. The same bound holds for every run
(`MatrixMidpointBUG.IsRun.norm_sub_le`).

## Main results

* `MatrixMidpointBUG.exists_isStep`: a step of the factors exists for every Lipschitz field that
  is continuous in time on the step interval, if `2 r ≤ m` and `2 r ≤ n`.
* `MatrixMidpointBUG.exists_stepRel`, `MatrixMidpointBUG.exists_run`: steps and runs of the
  fixed-rank integrator exist from every start value of rank at most `r`.
* `MatrixMidpointBUG.isTubeLocal_stepRel`: the integrator is a tube-local method
  (`StepMethod.IsTubeLocal`) with the matrices of rank at most `r` as admissible values and
  margin constant `2`.
* `MatrixMidpointBUG.stepRel.hasLocalError_uniformGrid`: the local error of one step of a
  uniform grid.
* `MatrixMidpointBUG.IsRun.norm_sub_le`: every run satisfies the error bound.
* `MatrixMidpointBUG.exists_run_norm_sub_le`: a run exists, has rank at most `r` and satisfies
  the error bound.

## Implementation notes

`MatrixMidpointBUG.exists_run_norm_sub_le` is an instance of
`StepMethod.IsTubeLocal.exists_run_norm_sub_le`, with the margin constant raised from `2` to `3`
(`StepMethod.IsTubeLocal.mono`): the distance of the exact solution to the matrices of rank at
most `r` is bounded near `A` only for start values with the margin `3 B h`
(`distLR_flow_le_exp_of_tube`). The properties (E), (I), (T) of the method hold for fields that
are Lipschitz and bounded only on a tube. The local error (L), however, is taken from
`MidpointBUG.IsMidpointBUGStep.hasLocalError`, whose hypotheses on the regularity of `F` are
global; the tube extension `tubeExt F A a b ρ` is neither of class `C²` nor Lipschitz in time,
so these hypotheses cannot be localized in the way the first-order integrators are. Here the
tube enters only through the normal bounds. The paper assumes the bounds on `F` near the exact
solution only.

Compared with `midpointBUG_global_error_le`, the steps are factor steps that are shown to
exist, the truncation is a best approximation of rank `r` instead of an unspecified truncation
with a tolerance `ϑ` (so no term `n ϑ` appears, and the rank stays `r`), the normal bounds are
hypotheses on the field near `A` instead of fields of the steps, and no exact flows started at
the numerical values appear. The price is the factor `2` in front of `C`, the term `e^{L H} ε`
of the truncation, and the smallness condition.

## References

* G. Ceruti, L. Einkemmer, J. Kusch, Ch. Lubich, *A robust second-order low-rank BUG integrator
  based on the midpoint rule*, arXiv:2402.08607, Theorems 1 and 2.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixMidpointBUG

/-! ### Existence of one step -/

section Exists

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
  {L t₀ t₁ : ℝ}

/-- **A step of the factors exists.** If `F` is Lipschitz and continuous in time on `[t₀, t₁]`,
`2 r ≤ m`, `2 r ≤ n`, and `U₀`, `V₀` have orthonormal columns, then for every `S₀` there is a
midpoint BUG step of the factors (`MatrixMidpointBUG.IsStep`) whose half step has `2 r` columns
and whose Galerkin bases have `min (4 r) m` and `min (4 r) n` columns, so at most `4 r`. The
field need not be bounded. The bases of the half step are orthonormal bases of `2 r` columns
whose ranges contain those of `(K(t½), U₀)` and `(L(t½), V₀)` (`exists_orthonormal_capture`);
this is where `2 r ≤ m` and `2 r ≤ n` are used. -/
theorem exists_isStep (hF : IsLipschitzField F L)
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁)
    (hrm : 2 * r ≤ Fintype.card m) (hrn : 2 * r ≤ Fintype.card n)
    {U₀ : Matrix m (Fin r) ℝ} (S₀ : Matrix (Fin r) (Fin r) ℝ) {V₀ : Matrix n (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) :
    ∃ (Uh : Matrix m (Fin (2 * r)) ℝ) (Vh : Matrix n (Fin (2 * r)) ℝ)
      (K : ℝ → Matrix m (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ)
      (Sh : ℝ → Matrix (Fin (2 * r)) (Fin (2 * r)) ℝ) (l l' : ℕ) (Ub : Matrix m (Fin l) ℝ)
      (Vb : Matrix n (Fin l') ℝ) (Sb : ℝ → Matrix (Fin l) (Fin l') ℝ),
      l ≤ 4 * r ∧ l' ≤ 4 * r ∧ IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb := by
  have hm0 : t₀ ≤ (t₀ + t₁) / 2 := by linarith
  have hm1 : (t₀ + t₁) / 2 ≤ t₁ := by linarith
  have hc' : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ ((t₀ + t₁) / 2)) := fun Y =>
    (hc Y).mono (Icc_subset_Icc le_rfl hm1)
  -- the half step
  obtain ⟨K, hK, hK₀⟩ := MatrixBUG.exists_odeSolution_conj_of_lipschitz hF hc' _ _
    (fun t x => MatrixBUG.kField_eq V₀ t x) hm0 (U₀ * S₀)
  obtain ⟨Lf, hLf, hLf₀⟩ := MatrixBUG.exists_odeSolution_conj_of_lipschitz hF hc' _ _
    (fun t x => MatrixBUG.lField_eq U₀ t x) hm0 (V₀ * S₀ᵀ)
  have hKr : (Matrix.fromCols (K ((t₀ + t₁) / 2)) U₀).rank ≤ 2 * r := by
    have := (Matrix.fromCols (K ((t₀ + t₁) / 2)) U₀).rank_le_card_width
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  have hLr : (Matrix.fromCols (Lf ((t₀ + t₁) / 2)) V₀).rank ≤ 2 * r := by
    have := (Matrix.fromCols (Lf ((t₀ + t₁) / 2)) V₀).rank_le_card_width
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  obtain ⟨Uh, hUh, hKcap, haugU⟩ :=
    exists_orthonormal_capture_fromCols (K ((t₀ + t₁) / 2)) U₀ hKr hrm
  obtain ⟨Vh, hVh, hLcap, haugV⟩ :=
    exists_orthonormal_capture_fromCols (Lf ((t₀ + t₁) / 2)) V₀ hLr hrn
  obtain ⟨Sh, hSh, hSh₀⟩ := MatrixBUG.exists_odeSolution_conj_of_lipschitz hF hc' _ _
    (fun t x => MatrixBUG.sField_eq Uh Vh t x) hm0 (Uhᵀ * U₀ * S₀ * (V₀ᵀ * Vh))
  have hhalf : MatrixBUG.IsRankAdaptiveStep F 0 t₀ ((t₀ + t₁) / 2) U₀ S₀ V₀ Uh Vh K Lf Sh
      (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ) :=
    ⟨hU₀, hV₀, hK, hK₀, hLf, hLf₀, hUh, hKcap, haugU, hVh, hLcap, haugV, hSh, hSh₀, by simp⟩
  -- the bases of the Galerkin step
  have hUr : (Matrix.fromCols Uh
      (F ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ) * Vh)).rank ≤ 4 * r := by
    have := (Matrix.fromCols Uh
      (F ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ) * Vh)).rank_le_card_width
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  have hVr : (Matrix.fromCols Vh
      ((F ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ))ᵀ * Uh)).rank ≤ 4 * r := by
    have := (Matrix.fromCols Vh
      ((F ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ))ᵀ * Uh)).rank_le_card_width
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  obtain ⟨Ub, hUb, hcapU, hcapF⟩ := exists_orthonormal_capture_fromCols Uh
    (F ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ) * Vh)
    (r := min (4 * r) (Fintype.card m)) (le_min hUr (Matrix.rank_le_card_height _))
    (min_le_right _ _)
  obtain ⟨Vb, hVb, hcapV, hcapFt⟩ := exists_orthonormal_capture_fromCols Vh
    ((F ((t₀ + t₁) / 2) (Uh * Sh ((t₀ + t₁) / 2) * Vhᵀ))ᵀ * Uh)
    (r := min (4 * r) (Fintype.card n)) (le_min hVr (Matrix.rank_le_card_height _))
    (min_le_right _ _)
  -- the Galerkin step
  obtain ⟨Sb, hSb, hSb₀⟩ := MatrixBUG.exists_odeSolution_conj_of_lipschitz hF hc _ _
    (fun t x => MatrixBUG.sField_eq Ub Vb t x) h01 (Ubᵀ * U₀ * S₀ * (V₀ᵀ * Vb))
  exact ⟨Uh, Vh, K, Lf, Sh, _, _, Ub, Vb, Sb, min_le_left _ _, min_le_left _ _,
    ⟨hhalf, hUb, hVb, hcapU, hcapV, hcapF, hcapFt, hSb, hSb₀⟩⟩

/-- **A midpoint BUG step without truncation exists from every start value of rank at most
`r`**, for every Lipschitz field that is continuous in time on the step interval, if `2 r ≤ m`
and `2 r ≤ n`: factor `Y₀ = U₀ S₀ V₀ᵀ` with `r` orthonormal columns
(`exists_factor_of_rank_le`) and apply `MatrixMidpointBUG.exists_isStep`. -/
theorem exists_augmentedRel (hF : IsLipschitzField F L)
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁)
    (hrm : 2 * r ≤ Fintype.card m) (hrn : 2 * r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) : ∃ Yh, augmentedRel F r t₀ t₁ Y₀ Yh := by
  obtain ⟨U₀, S₀, V₀, hU₀, hV₀, rfl⟩ := exists_factor_of_rank_le hY₀ (by omega) (by omega)
  obtain ⟨Uh, Vh, K, Lf, Sh, l, l', Ub, Vb, Sb, hl, hl', hs⟩ :=
    exists_isStep hF hc h01 hrm hrn S₀ hU₀ hV₀
  exact ⟨_, hs.augmentedRel hl hl'⟩

/-- **A step of the fixed-rank midpoint BUG integrator exists from every start value of rank at
most `r`**, for every Lipschitz field that is continuous in time on the step interval, if
`2 r ≤ m` and `2 r ≤ n`. -/
theorem exists_stepRel (hF : IsLipschitzField F L)
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁)
    (hrm : 2 * r ≤ Fintype.card m) (hrn : 2 * r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) : ∃ Y₁, stepRel F r t₀ t₁ Y₀ Y₁ := by
  obtain ⟨Yh, hYh⟩ := exists_augmentedRel hF hc h01 hrm hrn hY₀
  exact hYh.exists_stepRel

/-- **A run of the fixed-rank midpoint BUG integrator exists** on every grid, from every start
value of rank at most `r`, for every Lipschitz field that is continuous in time on `[τ 0, τ N]`,
if `2 r ≤ m` and `2 r ≤ n`. That the run stays near an exact solution is the content of
`MatrixMidpointBUG.exists_run_norm_sub_le`. -/
theorem exists_run (hF : IsLipschitzField F L) {τ : ℕ → ℝ} {N : ℕ} (hτ : IsGrid τ N)
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc (τ 0) (τ N)))
    (hrm : 2 * r ≤ Fintype.card m) (hrn : 2 * r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) : ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) τ N Y := by
  refine exists_isRun hτ Y₀ fun n hn Y hY0 hY => ?_
  have hsub : Icc (τ n) (τ (n + 1)) ⊆ Icc (τ 0) (τ N) :=
    Icc_subset_Icc (hτ.le_of_le n.zero_le hn.le) (hτ.le_of_le (Nat.succ_le_of_lt hn) le_rfl)
  exact exists_stepRel hF (fun Z => (hc Z).mono hsub) (hτ.mono n hn) hrm hrn
    (IsRun.rank_le hY (by rw [hY0]; exact hY₀) n le_rfl)

/-- **The fixed-rank midpoint BUG integrator is a tube-local method**
(`StepMethod.IsTubeLocal`), with the matrices of rank at most `r` as admissible values and
margin constant `2`, if `2 r ≤ m` and `2 r ≤ n`:

* a step exists from every matrix of rank at most `r`, for every globally Lipschitz field that
  is continuous in time on the step interval (`MatrixMidpointBUG.exists_stepRel`);
* the result of a step has rank at most `r` (`MatrixMidpointBUG.stepRel.rank_le`);
* if `‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, a step from `Y₀` of the extended field
  `tubeExt F A a b ρ` is a step of `F` (`MatrixMidpointBUG.stepRel_tubeExt_iff_of_near`): the
  half step over `[t₀, t½]` needs the margin `4 B (t½ - t₀)`, and the Galerkin step over
  `[t₀, t₁]` starts at `Y₀` and moves with speed at most `B`. -/
theorem isTubeLocal_stepRel (hrm : 2 * r ≤ Fintype.card m) (hrn : 2 * r ≤ Fintype.card n) :
    StepMethod.IsTubeLocal (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => stepRel G r)
      (fun Y => Y.rank ≤ r) 2 where
  exists_step := fun hG hc h01 hY₀ => exists_stepRel hG hc h01 hrm hrn hY₀
  adm_of_step := fun _ _ hstep => hstep.rank_le
  step_of_tubeExt := fun hFB hB ha hb h01 hA _ hsmall hstep =>
    (stepRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 hstep

end Exists

/-! ### The error bound, and existence of a run near the exact solution -/

section Error

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ}
  {t₀ h H T ρ L B M₁ M₂ ε ε₂ δ : ℝ} {N : ℕ}

/-- The constant of the midpoint BUG local error is nonnegative for nonnegative data. -/
private theorem midpointBUGConst_nonneg_aux {L Lₜ B M₃ H : ℝ} (hL : 0 ≤ L) (hLt : 0 ≤ Lₜ)
    (hB : 0 ≤ B) (hM : 0 ≤ M₃) (hH : 0 ≤ H) :
    0 ≤ MidpointBUG.midpointBUGConst L Lₜ B M₃ H := by
  have h1 : 0 ≤ bugC₁ L H := bugC₁_nonneg hL hH
  have h2 : 0 ≤ bugC₂ L B H := bugC₂_nonneg hL hB hH
  have hK : 0 ≤ Real.exp (L * H) := (Real.exp_pos _).le
  simp only [MidpointBUG.midpointBUGConst]
  positivity

/-- **Local error of one step of a uniform grid.** Under the hypotheses of the run theorem
(`F` Lipschitz, bounded and of class `C²` with bounded derivatives everywhere, normal bounds `ε`
at rank `r` and `ε₂` at rank `2 r` on the tube of radius `ρ` around the solution `A` over
`[t₀, t₀ + N h]`), a step of the fixed-rank midpoint BUG integrator over
`[t₀ + k h, t₀ + (k + 1) h]`, `k < N`, `0 ≤ h ≤ H`, whose start value `Z₀` satisfies
`‖Z₀ - A (t₀ + k h)‖ + 3 B h < ρ` has local error
`h (e^{L H} ε + 2 C (h² + h ε + ε₂))` (`MatrixMidpointBUG.stepRel.hasLocalError`). -/
theorem stepRel.hasLocalError_uniformGrid {k : ℕ} {Z₀ Z₁ : Matrix m n ℝ}
    (hstep : stepRel F r (t₀ + k * h) (t₀ + (k + 1) * h) Z₀ Z₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hF₂ : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂)
    (hA : ODESolution F A t₀ (t₀ + N * h))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hε₂ : FactoredNormalBoundOn F (2 * r) (tubeSet A t₀ (t₀ + N * h) ρ) ε₂)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hk : k < N) (hnear : ‖Z₀ - A (t₀ + k * h)‖ + 3 * B * h < ρ) :
    HasLocalError F (t₀ + k * h) (t₀ + (k + 1) * h) Z₀ Z₁
      (h * (Real.exp (L * H) * ε +
        2 * MidpointBUG.midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H *
          (h ^ 2 + h * ε + ε₂))) := by
  obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hk
  have hloc := hstep.hasLocalError hε hε₀ hε₂ hF hL hB hF₂ hM₁ hM₂ hA.cont ha hb h01
    (hsub.le.trans hhH) (hA.mono ha hb) (by rw [hsub]; exact hnear)
  rwa [hsub] at hloc

/-- **Every run of the fixed-rank midpoint BUG integrator satisfies the second-order error
bound** (arXiv:2402.08607, Theorem 2, for the integrator with truncation to rank `r`). Let `F` be
`L`-Lipschitz (`L ≥ 0`) and bounded by `B`, and let the uncurried field be of class `C²` with
`‖DF‖ ≤ M₁` and `‖D²F‖ ≤ M₂`, everywhere. Let `A` solve `Y' = F(t, Y)` on `[t₀, t₀ + N h]`, and
let the normal part of `F` be at most `ε ≥ 0` at the factored points with `r` columns and at most
`ε₂ ≥ 0` at those with `2 r` columns of the tube of radius `ρ` around `A`. Let `Y 0, …, Y N` be a
run of the integrator with step size `0 ≤ h ≤ H`, `N h ≤ T`, and `‖Y 0 - A t₀‖ ≤ δ`. If the bound
below plus `3 B h` is smaller than `ρ`, then for all `n ≤ N`

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (e^{L H} ε + 2 C (h² + h ε + ε₂))`,

`C = midpointBUGConst L M₁ B (M₂ (1 + B)² + M₁² (1 + B)) H`. The constants do not depend on the
singular values of the `Y n`. -/
theorem IsRun.norm_sub_le {Y : ℕ → Matrix m n ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hF₂ : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂)
    (hA : ODESolution F A t₀ (t₀ + N * h))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hε₂ : FactoredNormalBoundOn F (2 * r) (tubeSet A t₀ (t₀ + N * h) ρ) ε₂) (hε₂₀ : 0 ≤ ε₂)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) * (Real.exp (L * H) * ε +
      2 * MidpointBUG.midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H *
        (h ^ 2 + h * ε + ε₂)) + 3 * B * h < ρ)
    (hY : IsRun (stepRel F r) (uniformGrid t₀ h) N Y) (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) *
      (Real.exp (L * H) * ε +
        2 * MidpointBUG.midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H *
          (h ^ 2 + h * ε + ε₂)) := by
  have hB0 : 0 ≤ B := hB.nonneg
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  have hC0 := midpointBUGConst_nonneg_aux hL hM₁0 hB0
    (by positivity : 0 ≤ M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) (hh.trans hhH)
  have hc₀ : 0 ≤ Real.exp (L * H) * ε +
      2 * MidpointBUG.midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H *
        (h ^ 2 + h * ε + ε₂) :=
    add_nonneg (mul_nonneg (Real.exp_pos _).le hε₀)
      (mul_nonneg (mul_nonneg (by norm_num) hC0) (by positivity))
  have hBh : 0 ≤ B * h := mul_nonneg hB0 hh
  refine hY.norm_sub_le_of_tube_uniformGrid (T := T) (δ₀ := δ) (DLRAProblem.of_global hF hL hB hA ρ)
    hF₂.continuous.continuousOn (fun k hk Z₀ Z₁ hnear hstep => ?_) hc₀ hδ hNT (by linarith)
  exact hstep.hasLocalError_uniformGrid hF hL hB hF₂ hM₁ hM₂ hA hε hε₀ hε₂ hh hhH hk
    (by linarith)

/-- **Existence and second-order error bound for the fixed-rank midpoint BUG integrator**
(arXiv:2402.08607, Theorems 1 and 2, with truncation to rank `r`). Let `F` be `L`-Lipschitz
(`L ≥ 0`) and bounded by `B`, and let the uncurried field be of class `C²` with `‖DF‖ ≤ M₁` and
`‖D²F‖ ≤ M₂`, everywhere. Let `A` solve `Y' = F(t, Y)` on `[t₀, t₀ + N h]`, and let the normal
part of `F` be at most `ε ≥ 0` at the factored points with `r` columns and at most `ε₂ ≥ 0` at
those with `2 r` columns of the tube of radius `ρ` around `A`. Let `2 r ≤ m`, `2 r ≤ n`,
`0 ≤ h ≤ H`, `N h ≤ T`, and let `Y₀` have rank at most `r` with `‖Y₀ - A t₀‖ ≤ δ`. If

  `e^{L T} δ + T e^{L T} (e^{L H} ε + 2 C (h² + h ε + ε₂)) + 3 B h < ρ`,

`C = midpointBUGConst L M₁ B (M₂ (1 + B)² + M₁² (1 + B)) H`, then the integrator can be run from
`Y₀`: there are `Y 0 = Y₀, Y 1, …, Y N`, each obtained from the previous one by a midpoint BUG
step of size `h` followed by a best approximation of rank at most `r`, all of rank at most `r`,
with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (e^{L H} ε + 2 C (h² + h ε + ε₂))`

for all `n ≤ N`. The error is of order `h² + ε + ε₂`, robustly in the singular values. This is
`StepMethod.IsTubeLocal.exists_run_norm_sub_le` for the tube-local method
`MatrixMidpointBUG.isTubeLocal_stepRel` with margin constant `3`. -/
theorem exists_run_norm_sub_le
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hF₂ : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂)
    (hA : ODESolution F A t₀ (t₀ + N * h))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hε₂ : FactoredNormalBoundOn F (2 * r) (tubeSet A t₀ (t₀ + N * h) ρ) ε₂) (hε₂₀ : 0 ≤ ε₂)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hrm : 2 * r ≤ Fintype.card m) (hrn : 2 * r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) * (Real.exp (L * H) * ε +
      2 * MidpointBUG.midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H *
        (h ^ 2 + h * ε + ε₂)) + 3 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ +
        T * Real.exp (L * T) * (Real.exp (L * H) * ε +
          2 * MidpointBUG.midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H *
            (h ^ 2 + h * ε + ε₂)) := by
  have hB0 : 0 ≤ B := hB.nonneg
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  have hC0 := midpointBUGConst_nonneg_aux hL hM₁0 hB0
    (by positivity : 0 ≤ M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) (hh.trans hhH)
  have hc₀ : 0 ≤ Real.exp (L * H) * ε +
      2 * MidpointBUG.midpointBUGConst L M₁ B (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) H *
        (h ^ 2 + h * ε + ε₂) :=
    add_nonneg (mul_nonneg (Real.exp_pos _).le hε₀)
      (mul_nonneg (mul_nonneg (by norm_num) hC0) (by positivity))
  refine ((isTubeLocal_stepRel hrm hrn).mono (by norm_num : (2 : ℝ) ≤ 3)).exists_run_norm_sub_le
    (by norm_num) (DLRAProblem.of_global hF hL hB hA ρ) hF₂.continuous.continuousOn
    (fun k hk Z₀ Z₁ _ hnear hstep => ?_) hc₀ hh hNT hY₀ hδ hsmall
  exact stepRel.hasLocalError_uniformGrid hstep hF hL hB hF₂ hM₁ hM₂ hA hε hε₀ hε₂ hh hhH hk
    (by linarith)

end Error

/-! ### Examples: a constant field -/

section Examples

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}

/-- The curve `A(t) = A₀ + (t - t₀) G` solves `Y' = G`. -/
example (G A₀ : Matrix m n ℝ) (t₀ t₁ : ℝ) :
    ODESolution (fun (_ : ℝ) (_ : Matrix m n ℝ) => G) (fun t => A₀ + (t - t₀) • G) t₀ t₁ := by
  refine ⟨(continuous_const.add
    ((continuous_id.sub continuous_const).smul continuous_const)).continuousOn, fun t _ => ?_⟩
  have h := (((hasDerivAt_id t).sub_const t₀).smul_const G).const_add A₀
  rw [one_smul] at h
  exact h.hasDerivWithinAt

/-- **Non-vacuity of the existence and error theorem.** The constant field `F(t, Y) = G` is
`0`-Lipschitz, bounded by `‖G‖`, of class `C²` with vanishing first and second derivatives
(`M₁ = M₂ = 0`), and its normal part at every factored matrix is at most `‖G‖`
(`factoredNormalBoundOn_linear` with zero linear part), so `ε = ε₂ = ‖G‖`. For every solution
`A` of `Y' = G` on `[t₀, t₀ + N h]` (the curve `A₀ + (t - t₀) G` is one) and every start value
`Y₀` of rank at most `r` with `2 r ≤ m`, `2 r ≤ n` and `‖Y₀ - A t₀‖ ≤ δ`, the fixed-rank midpoint
BUG integrator can be run with every step size `0 ≤ h ≤ H`, and the run satisfies the error
bound with these constants. No smallness condition remains, because the tube radius can be
chosen as large as needed. -/
example (G : Matrix m n ℝ) (hrm : 2 * r ≤ Fintype.card m) (hrn : 2 * r ≤ Fintype.card n)
    {A : ℝ → Matrix m n ℝ} {t₀ h H T δ : ℝ} {N : ℕ}
    (hA : ODESolution (fun (_ : ℝ) (_ : Matrix m n ℝ) => G) A t₀ (t₀ + N * h))
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r)
    (hδ : ‖Y₀ - A t₀‖ ≤ δ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (stepRel (fun (_ : ℝ) (_ : Matrix m n ℝ) => G) r) (uniformGrid t₀ h) N Y ∧
      ∀ j ≤ N, (Y j).rank ≤ r ∧ ‖Y j - A (t₀ + j * h)‖ ≤ Real.exp (0 * T) * δ +
        T * Real.exp (0 * T) * (Real.exp (0 * H) * ‖G‖ +
          2 * MidpointBUG.midpointBUGConst 0 0 ‖G‖ (0 * (1 + ‖G‖) ^ 2 + 0 ^ 2 * (1 + ‖G‖)) H *
            (h ^ 2 + h * ‖G‖ + ‖G‖)) := by
  have hfield : (fun (_ : ℝ) (Y : Matrix m n ℝ) => (0 : Matrix m m ℝ) * Y +
      Y * (0 : Matrix n n ℝ)ᵀ + G) = fun _ _ => G := by
    funext t Y
    simp
  have hN : ∀ s (D : Set (ℝ × Matrix m n ℝ)),
      FactoredNormalBoundOn (fun (_ : ℝ) (_ : Matrix m n ℝ) => G) s D ‖G‖ := fun s D => by
    rw [← hfield]
    exact factoredNormalBoundOn_linear 0 0 G D
  have hF₂ : ContDiff ℝ 2 (Function.uncurry fun (_ : ℝ) (_ : Matrix m n ℝ) => G) :=
    contDiff_const
  exact exists_run_norm_sub_le (F := fun (_ : ℝ) (_ : Matrix m n ℝ) => G) (A := A) (L := 0)
    (B := ‖G‖) (M₁ := 0) (M₂ := 0) (ε := ‖G‖) (ε₂ := ‖G‖)
    (ρ := Real.exp (0 * T) * δ + T * Real.exp (0 * T) * (Real.exp (0 * H) * ‖G‖ +
      2 * MidpointBUG.midpointBUGConst 0 0 ‖G‖ (0 * (1 + ‖G‖) ^ 2 + 0 ^ 2 * (1 + ‖G‖)) H *
        (h ^ 2 + h * ‖G‖ + ‖G‖)) + 3 * ‖G‖ * h + 1)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => le_rfl) hF₂
    (fun p => by
      change ‖fderiv ℝ (fun _ : ℝ × Matrix m n ℝ => G) p‖ ≤ 0
      simp)
    (fun p => by
      change ‖iteratedFDeriv ℝ 2 (fun _ : ℝ × Matrix m n ℝ => G) p‖ ≤ 0
      rw [iteratedFDeriv_const_of_ne (n := 2) (by norm_num) G]
      simp)
    hA (hN r _) (norm_nonneg G) (hN (2 * r) _) (norm_nonneg G) hh hhH hNT hrm hrn hY₀ hδ
    (lt_add_one _)

end Examples

end MatrixMidpointBUG

end LeanDLRA
