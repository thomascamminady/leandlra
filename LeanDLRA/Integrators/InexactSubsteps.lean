import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Integrators.ProjectorSplitting
import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Integrators.ParallelBUG

/-!
# Inexact and incompletely augmented substeps (BUG, Tucker BUG, parallel BUG)

This file treats one-step integrators of dynamical low-rank approximation whose substeps are
**not solved exactly** or whose new bases **do not capture** the exact substep values.  All
results are robust: the constants depend only on the Lipschitz constant `L`, the bound `B` of the
vector field, the final time `T`, the maximal step size `H` (and, for Tucker, linearly on the
number of modes `d`), never on singular values.

## Main results

* `kstep_capture_defect` (OP-TN-02, OP-SB-01): the K-step capture lemma with a **capture
  defect** `‖(1 - P₁) YK(t₁)‖ ≤ η` instead of exact capture gives
  `‖(1 - P₁) A(t₁)‖ ≤ h (4 L B h + ε) + η`.  The defect covers inexact K-steps
  (`norm_compl_le_of_computed`), incomplete augmentation and rank-revealing thresholds (lost
  component `μ`: `η + μ`), and **frozen bonds** (`norm_compl_kstep_le_of_frozen`: `η = h ν` with
  `ν` the K-step velocity normal to the frozen basis).
* `IsDefectBUGStep`: a BUG step (fixed rank or augmented, S-step started at `P₁ Q₁ Y₀`) with
  capture defects `ηK`, `ηL` and S-step endpoint error `ηS`.  Exact BUG steps (`ofBUGStep`),
  inexact rank-adaptive steps (`IsInexactRankAdaptiveBUGStep.toInexactBUGStep`) and steps with
  computed substep values (`IsInexactBUGStep.toDefect`) are special cases.
  `capture_defect_attained`: a step with `P₁ = 0` and strictly positive capture defect whose error
  equals the bound of `local_error_le` (non-vacuity and sharpness of the `ηK` term).
  `IsDefectBUGStep.local_error_le`: `‖Y₁ - A(t₁)‖ ≤ h (c₁ ε + c₂ h) + e^{L H} (ηK + ηL) + ηS`
  with the constants `c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H` of the exact BUG integrator.
  `IsDefectBUGStep.abs_norm_sub_le` (OP-TN-02, norm conservation): for norm-conserving fields
  `|‖Y₁‖ - ‖Y₀‖| ≤ ‖Y₀ - P₁ Q₁ Y₀‖ + ηS`, i.e. norm conservation fails at most by the lost
  component of `Y₀` (zero under complete augmentation) plus the S-step error.
* `defectBUG_global_error`, `defectBUG_global_error_le` (OP-SB-01): global error
  `e^{L T} (δ + T (c₁ ε + c₂ h) + n (2 e^{L H} + 1) η)`, i.e. `c₀ δ + c₁ ε + c₂ h + c₃ n η`.
  `inexactBUG_global_error` is the statement in robust `∃ C` form: `‖Y n - A tₙ‖ ≤ C (δ + ε + h + n
  η)`.
* `defectBUG_global_error_order`, `defectBUG_global_error_first_order` (OP-HO-05): if the
  substeps are solved by a one-step method of order `q` (`η ≤ C_η h^{q+1}`), the global error is
  `O(δ + ε + h + h^q)`; for `q ≥ 1` the robust first order is kept.
* `defectBUG_global_error_of_tolerance` (OP-OT-05): iterative (Krylov) solves to tolerance `τ`
  add `(2 e^{L H} + 1) e^{L T} T τ / h`, which is `O(h)` iff `τ = O(h²)`.
* `defectBUG_sharp`: the accumulated term `n η` is attained (`F = 0`, S-step results off by
  exactly `η`), so neither the `n η = T η / h` growth nor the order reduction can be avoided in
  general.
* Tucker (OP-SB-01 with explicit `d`-dependence): `IsDefectTuckerBUGStep` (mode-wise capture
  defects, `IsDefectTuckerBUGStep.capture`: `‖A₁ - Π A₁‖ ≤ d (ϑ + ηK)`),
  `IsDefectTuckerBUGStep.local_error_le`: `h (c₁ ε + c₂ h) + e^{L H} d ηK + ηS` with the Tucker
  constants, `defectTuckerBUG_global_error_le`, and the statement
  `inexactTuckerBUG_global_error`: `‖Y n - A tₙ‖ ≤ C (δ + (d + 1) (ε + h + n η))` with `C`
  independent of `d`.  The growth in `d` is
  linear, not `d e^{d L h}`.
* Parallel BUG: the update is affine with contraction coefficients
  (`parallelBUG_sub_parallelBUG`, `norm_parallelBUG_sub_le`), so computed substep values add
  `ηK + ηL + ηS` to the local error (`parallelBUG_local_error_inexact`) and `n (ϑ + 3 η)` to the
  global error (`parallelBUG_global_error_inexact`).
* `lady_windermere_defect`: Lady Windermere's fan with an additive per-step defect,
  `e^{L T} (δ + T g + n ρ)`.

## Relation to the literature and what is new

Ceruti–Lubich ([CerutiLubich2022], after Thm 4), Ceruti–Kusch–Lubich
([CerutiKuschLubich2022, §2.2]), Kieri–Lubich–Walach (2016, §2.6.3, for KSL), the low-rank Strang
splitting with BUG2 substeps solved by Heun's method ([ScaloneGuglielmi2026], "Implementation and
further remarks") and the high-order robust BUG paper ([HauckKuschSchotthofer2026, §6]-7) state that
inexact substeps add `O(η)` to the local error but analyse only exact substeps (except KSL). Here
the fixed-rank case (S-step started at `P₁ Q₁ Y₀`, no augmentation property `P₁ Y₀ = Y₀`), the
capture-defect formulation (which unifies inexact solves, incomplete augmentation, thresholds and
frozen bonds, OP-TN-02), the explicit order statement for substep solvers and the sharpness examples
are proved. The defect enters as `n η`, not `T η`: the endpoint error of a step is not divided by
`h`, which is why an order-`q` substep solver must satisfy `η = O(h^{q+1})`.

## What remains

* The defect model is the **endpoint** model (`‖YK t₁ - K₁‖ ≤ η` per step), which accumulates as
  `n η`; the "defect per unit time" model of OP-SB-01 is the special case `η = h η'`
  (accumulating as `T η'`).  A defect-solution predicate (`‖y' - Π F(t, y)‖ ≤ η'` along the
  computed substep) is not formalised.
* The stiff case (substep error constants depending on stiffness, implicit or exponential
  substeps of OP-OT-05 for kinetic equations) is not covered: all constants use the Lipschitz
  constant `L` of the full field.
* The recursive Tucker KSL integrator of [LubichVandereyckenWalach2018] (whose `d`-fold recursion
  OP-SB-01 asks to quantify) and the symmetric and anti-symmetric Tucker variants are not treated;
  the KSL matrix case is `ksl_local_error_inexact` in `Integrators/ProjectorSplitting.lean`.
* The exact lost-part formula of MPS centre augmentation ([FrohlichEtAl2026, Prop. 2], OP-TN-02)
  is not formalised; it would enter as a capture defect `η`.
* Second- and higher-order BUG integrators (`p > 1` in OP-HO-05) are not yet in the library;
  `defectBUG_global_error_order` is the generic real-number mechanism
  (`n C_η h^{q+1} ≤ T C_η h^q`, `natCast_mul_le_of_order`) that will apply to them.
-/

open Set Finset
open scoped RealInnerProductSpace

universe u

namespace LeanDLRA.InexactSubsteps

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Capture with a defect -/

section CaptureDefect

variable {F : ℝ → E → E} {L B ε : ℝ} {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ h : ℝ} {A YK : ℝ → E}

/-- For an orthogonal projector `P`, the normal component of `y` is at most the distance of `y`
to any `k` plus the normal component of `k`: `‖(1 - P) y‖ ≤ ‖y - k‖ + ‖(1 - P) k‖`. -/
lemma norm_compl_le_of_approx {P : E →L[ℝ] E} (hP : IsOrthProj P) (y k : E) :
    ‖(1 - P) y‖ ≤ ‖y - k‖ + ‖(1 - P) k‖ := by
  have hdec : (1 - P) y = (1 - P) (y - k) + (1 - P) k := by rw [map_sub]; abel
  rw [hdec]
  exact (norm_add_le _ _).trans (add_le_add (hP.compl.norm_le _) le_rfl)

/-- **Transfer of the normal-component bound.**  If the doubly normal component of `F` is
`ε`-small at a reference point `z` and `‖z - y‖ ≤ ρ`, then it is `(ε + L ρ)`-small at `y`.  This
converts a normal-component assumption at a *computed* substep value (where, in the matrix
layer, it follows from the factored assumption) into one at the *exact* substep value. -/
lemma normal_le_of_near (hF : IsLipschitzField F L) (hL : 0 ≤ L) {P Q : E →L[ℝ] E}
    (hP : IsOrthProj P) (hQ : IsOrthProj Q) (t : ℝ) {y z : E} {ρ : ℝ} (hzy : ‖z - y‖ ≤ ρ)
    (hε : ‖(1 - P) ((1 - Q) (F t z))‖ ≤ ε) :
    ‖(1 - P) ((1 - Q) (F t y))‖ ≤ ε + L * ρ := by
  have hdec : (1 - P) ((1 - Q) (F t y)) =
      (1 - P) ((1 - Q) (F t z)) + (1 - P) ((1 - Q) (F t y - F t z)) := by
    rw [map_sub, map_sub]; abel
  rw [hdec]
  refine (norm_add_le _ _).trans (add_le_add hε ?_)
  calc ‖(1 - P) ((1 - Q) (F t y - F t z))‖ ≤ ‖(1 - Q) (F t y - F t z)‖ := hP.compl.norm_le _
    _ ≤ ‖F t y - F t z‖ := hQ.compl.norm_le _
    _ ≤ L * ‖y - z‖ := hF t _ _
    _ ≤ L * ρ := mul_le_mul_of_nonneg_left (by rwa [norm_sub_rev]) hL

/-- **K-step capture lemma with a capture defect** (OP-TN-02, OP-SB-01).  As `kstep_capture`,
but the new basis captures the exact K-step value only up to a defect,
`‖(1 - P₁) (YK t₁)‖ ≤ η`, instead of `P₁ (YK t₁) = YK t₁`.  Then

    ‖(1 - P₁) (A t₁)‖ ≤ h (4 L B h + ε) + η.

The defect `η` covers at once an inexactly computed K-step (`P₁` spans a computed `K₁` with
`‖YK t₁ - K₁‖ ≤ ηK`: `η = ηK`), an incomplete augmentation or a rank-revealing threshold that
drops a direction of `K₁` of weight `μ` (`η = ηK + μ`, see `norm_compl_le_of_approx`), and a
frozen bond (`P₁ = P₀`, see `norm_compl_kstep_le_of_frozen`). -/
theorem kstep_capture_defect (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = A t₀) {η : ℝ}
    (hmiss : ‖(1 - P₁) (YK t₁)‖ ≤ η)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε) :
    ‖(1 - P₁) (A t₁)‖ ≤ h * (4 * L * B * h + ε) + η := by
  refine kstep_capture_approx hF hL hB hP₁ hQ₀ ht₁ hh hA hK hK₀ (K₁ := P₁ (YK t₁))
    (hP₁.idem _) ?_ hε
  simpa using hmiss

/-- **Frozen bond.**  If the left basis is not updated in the K-step (`P₁ = P₀`, e.g. a
classical–quantum bond of a hybrid tensor network that is not augmented), `P₀ Y₀ = Y₀`, and the
component of the K-step velocity normal to the frozen basis is bounded,
`‖(1 - P₀) (Q₀ F(t, YK t))‖ ≤ ν`, then the capture defect is at most `h ν`:
`‖(1 - P₀) (YK t₁)‖ ≤ h ν`. -/
theorem norm_compl_kstep_le_of_frozen {P₀ : E →L[ℝ] E} {Y₀ : E} (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = Y₀)
    (hP₀ : P₀ Y₀ = Y₀) {ν : ℝ} (hν : ∀ t ∈ Ico t₀ t₁, ‖(1 - P₀) (Q₀ (F t (YK t)))‖ ≤ ν) :
    ‖(1 - P₀) (YK t₁)‖ ≤ h * ν := by
  have hle : t₀ ≤ t₁ := by linarith
  set g : ℝ → E := fun t => (1 - P₀) (YK t) with hg
  have hgc : ContinuousOn g (Icc t₀ t₁) := (1 - P₀).continuous.comp_continuousOn hK.cont
  have hgd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt g ((1 - P₀) (Q₀ (F t (YK t)))) (Ici t) t :=
    fun t ht => (1 - P₀).hasFDerivAt.comp_hasDerivWithinAt t (hK.deriv t ht)
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd hν t₁ ⟨hle, le_rfl⟩
  have hg₀ : g t₀ = 0 := by simp [hg, hK₀, hP₀]
  rw [hg₀, sub_zero, show t₁ - t₀ = h by rw [ht₁]; ring] at hmvt
  rw [mul_comm]
  exact hmvt

end CaptureDefect

/-! ### A final-form Lady Windermere's fan -/

section Fan

variable {F : ℝ → E → E} {L : ℝ}

/-- **Lady Windermere's fan, final form with an additive local defect.**  If the local errors
are `‖Y (n+1) - Φ n tₙ₊₁‖ ≤ h g + ρ` (a consistency part `h g` and a per-step defect `ρ`, with
`g, ρ ≥ 0`), the initial error is at most `δ` and `n h ≤ T`, then

    ‖Y n - A tₙ‖ ≤ e^{L T} (δ + T g + n ρ).

The defect is *not* divided by `h`: it accumulates as `n ρ ≤ T ρ / h`. -/
theorem lady_windermere_defect (hF : IsLipschitzField F L) (hL : 0 ≤ L) {t₀ h : ℝ}
    (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {Y : ℕ → E}
    {Φ : ℕ → ℝ → E} (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {g ρ : ℝ} (hg : 0 ≤ g) (hρ : 0 ≤ ρ)
    (hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤ h * g + ρ) {δ T : ℝ}
    (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * (δ + T * g + n * ρ) := by
  intro n hn hT
  have h1 := lady_windermere hF hL hh hA hΦ hΦ₀ hloc n hn
  have hnh : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg n) hh
  have hexp : Real.exp (L * (n * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  have hin : ‖Y 0 - A t₀‖ + n * (h * g + ρ) ≤ δ + T * g + n * ρ := by
    have : (n : ℝ) * h * g ≤ T * g := mul_le_mul_of_nonneg_right hT hg
    nlinarith
  have hin0 : 0 ≤ ‖Y 0 - A t₀‖ + n * (h * g + ρ) := by positivity
  exact h1.trans (mul_le_mul hexp hin hin0 (Real.exp_pos _).le)

end Fan

/-! ### The fixed-rank BUG integrator with inexact substeps -/

/-- One step of the (fixed-rank or augmented) **BUG integrator with inexact substeps and
incomplete basis capture**, from `(t₀, Y₀)` to `t₁` (OP-SB-01, OP-HO-05, OP-TN-02).

* `YK`, `YL`, `YS` are the *exact* solutions of the K-, L- and S-step differential equations
  `YK' = Q₀ F(t, YK)`, `YL' = P₀ F(t, YL)` (from `Y₀`) and `YS' = P₁ Q₁ F(t, YS)` (from
  `P₁ Q₁ Y₀`, i.e. the Galerkin start `S(t₀) = (U₁ᵀ U₀) S₀ (V₀ᵀ V₁)`), as in `IsBUGStep`;
* the new bases capture the exact K- and L-step values only up to **capture defects**
  `‖(1 - P₁) (YK t₁)‖ ≤ ηK`, `‖(1 - Q₁) (YL t₁)‖ ≤ ηL` (instead of `P₁ (YK t₁) = YK t₁`);
* the new approximation `Y₁` is the computed S-step result, `‖Y₁ - YS t₁‖ ≤ ηS` (this also
  absorbs a truncation, as in the rank-adaptive BUG integrator).

The defects cover inexact K- and L-steps (bases spanning computed values `K₁` with
`‖YK t₁ - K₁‖ ≤ ηK`), incomplete augmentation, rank-revealing thresholds and frozen bonds (see
`kstep_capture_defect`).  The S-step may start at `P₁ Q₁ Y₀ ≠ Y₀`: the augmentation property
`P₁ Y₀ = Y₀` is not needed for the error bound.  Special cases: `ofBUGStep`
(all defects `0`) and `IsInexactRankAdaptiveBUGStep.toInexactBUGStep`. -/
structure IsDefectBUGStep (F : ℝ → E → E) (ε ηK ηL ηS : ℝ) (P₀ Q₀ P₁ Q₁ : E →L[ℝ] E)
    (t₀ t₁ : ℝ) (Y₀ : E) (YK YL YS : ℝ → E) (Y₁ : E) : Prop where
  projP₀ : IsOrthProj P₀
  projQ₀ : IsOrthProj Q₀
  projP₁ : IsOrthProj P₁
  projQ₁ : IsOrthProj Q₁
  /-- The new left and right projectors commute. -/
  comm₁ : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)
  /-- Exact K-step `YK' = Q₀ F(t, YK)`. -/
  kSol : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁
  kStart : YK t₀ = Y₀
  kNormal : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε
  /-- Capture defect of the new left basis. -/
  kDefect : ‖(1 - P₁) (YK t₁)‖ ≤ ηK
  /-- Exact L-step `YL' = P₀ F(t, YL)`. -/
  lSol : ODESolution (fun t x => P₀ (F t x)) YL t₀ t₁
  lStart : YL t₀ = Y₀
  lNormal : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε
  /-- Capture defect of the new right basis. -/
  lDefect : ‖(1 - Q₁) (YL t₁)‖ ≤ ηL
  /-- Exact Galerkin S-step `YS' = P₁ Q₁ F(t, YS)` from `P₁ Q₁ Y₀`. -/
  sSol : ODESolution (fun t x => P₁ (Q₁ (F t x))) YS t₀ t₁
  sStart : YS t₀ = P₁ (Q₁ Y₀)
  /-- Error of the computed S-step result (and of a truncation). -/
  sErr : ‖Y₁ - YS t₁‖ ≤ ηS

/-- An exact BUG step is an inexact BUG step with zero defects. -/
theorem ofBUGStep {F : ℝ → E → E} {ε : ℝ} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E}
    {t₀ t₁ : ℝ} {Y₀ : E} {YK YL YS : ℝ → E}
    (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS) :
    IsDefectBUGStep F ε 0 0 0 P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS (YS t₁) where
  projP₀ := hs.projP₀
  projQ₀ := hs.projQ₀
  projP₁ := hs.projP₁
  projQ₁ := hs.projQ₁
  comm₁ := hs.comm₁
  kSol := hs.kSol
  kStart := hs.kStart
  kNormal := hs.kNormal
  kDefect := by simp [hs.kCap]
  lSol := hs.lSol
  lStart := hs.lStart
  lNormal := hs.lNormal
  lDefect := by simp [hs.lCap]
  sSol := hs.sSol
  sStart := hs.sStart
  sErr := by simp

/-- A rank-adaptive BUG step with inexact substeps (`IsInexactRankAdaptiveBUGStep`, substep
errors `η`, truncation `ϑ`) is an inexact BUG step with defects `ηK = ηL = η`, `ηS = η + ϑ`. -/
theorem IsInexactRankAdaptiveBUGStep.toInexactBUGStep {F : ℝ → E → E} {ε η ϑ : ℝ}
    {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E} {YK YL YS : ℝ → E} {K₁ L₁ Ŷ₁ Y₁ : E}
    (hs : IsInexactRankAdaptiveBUGStep F ε η ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS K₁ L₁ Ŷ₁ Y₁) :
    IsDefectBUGStep F ε η η (η + ϑ) P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁ where
  projP₀ := hs.projP₀
  projQ₀ := hs.projQ₀
  projP₁ := hs.projP₁
  projQ₁ := hs.projQ₁
  comm₁ := hs.comm₁
  kSol := hs.kSol
  kStart := hs.kStart
  kNormal := hs.kNormal
  kDefect := by
    have := norm_compl_le_of_approx hs.projP₁ (YK t₁) K₁
    simp only [sub_apply, one_apply_eq_self, hs.kCap,
      sub_self, norm_zero, add_zero] at this
    exact this.trans hs.kApprox
  lSol := hs.lSol
  lStart := hs.lStart
  lNormal := hs.lNormal
  lDefect := by
    have := norm_compl_le_of_approx hs.projQ₁ (YL t₁) L₁
    simp only [sub_apply, one_apply_eq_self, hs.lCap,
      sub_self, norm_zero, add_zero] at this
    exact this.trans hs.lApprox
  sSol := hs.sSol
  sStart := hs.sStart
  sErr := by
    have := norm_sub_le_norm_sub_add_norm_sub Y₁ Ŷ₁ (YS t₁)
    linarith [hs.trunc, hs.sApprox]

namespace IsDefectBUGStep

variable {F : ℝ → E → E} {ε ηK ηL ηS : ℝ} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E}
  {YK YL YS : ℝ → E} {Y₁ : E} {L B h : ℝ} {A : ℝ → E}

lemma eps_nonneg (hs : IsDefectBUGStep F ε ηK ηL ηS P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (h01 : t₀ ≤ t₁) : 0 ≤ ε :=
  (norm_nonneg _).trans (hs.kNormal t₀ ⟨le_rfl, h01⟩)

lemma etaK_nonneg (hs : IsDefectBUGStep F ε ηK ηL ηS P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) :
    0 ≤ ηK :=
  (norm_nonneg _).trans hs.kDefect

lemma etaL_nonneg (hs : IsDefectBUGStep F ε ηK ηL ηS P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) :
    0 ≤ ηL :=
  (norm_nonneg _).trans hs.lDefect

lemma etaS_nonneg (hs : IsDefectBUGStep F ε ηK ηL ηS P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) :
    0 ≤ ηS :=
  (norm_nonneg _).trans hs.sErr

/-- **Capture with defects**: `‖A t₁ - P₁ Q₁ A t₁‖ ≤ 2 ϑ + ηK + ηL`, `ϑ = h (4 L B h + ε)`. -/
theorem capture (hs : IsDefectBUGStep F ε ηK ηL ηS P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖A t₁ - P₁ (Q₁ (A t₁))‖ ≤ 2 * (h * (4 * L * B * h + ε)) + (ηK + ηL) := by
  have h1 := kstep_capture_defect hF hL hB hs.projP₁ hs.projQ₀ ht₁ hh hA hs.kSol
    (hs.kStart.trans hA₀.symm) hs.kDefect hs.kNormal
  have h2 := kstep_capture_defect hF hL hB hs.projQ₁ hs.projP₀ ht₁ hh hA hs.lSol
    (hs.lStart.trans hA₀.symm) hs.lDefect hs.lNormal
  have h3 := norm_sub_apply_apply_le (Q := Q₁) hs.projP₁ (A t₁)
  linarith

/-- **Local error of the BUG integrator with inexact substeps** (OP-SB-01, explicit form):
with `ϑ = h (4 L B h + ε)` and `θ = 2 ϑ + ηK + ηL`,

    ‖Y₁ - A t₁‖ ≤ (e^{L h} - 1) (B h + θ) + θ + ηS. -/
theorem local_error (hs : IsDefectBUGStep F ε ηK ηL ηS P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + (2 * (h * (4 * L * B * h + ε)) + (ηK + ηL)))
      + (2 * (h * (4 * L * B * h + ε)) + (ηK + ηL)) + ηS := by
  have hS := galerkin_step_error (R := P₁ * Q₁) (hs.projP₁.mul hs.projQ₁ hs.comm₁) hF hL hB ht₁
    hh hA hs.sSol (by rw [hs.sStart, hA₀]; rfl) (hs.capture hF hL hB ht₁ hh hA hA₀)
  have h1 := norm_sub_le_norm_sub_add_norm_sub Y₁ (YS t₁) (A t₁)
  linarith [hs.sErr]

/-- **Local error of the BUG integrator with inexact substeps, `O`-form** (OP-SB-01): for
`0 ≤ h ≤ H`,

    ‖Y₁ - A t₁‖ ≤ h (c₁ ε + c₂ h) + e^{L H} (ηK + ηL) + ηS

with the constants `c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H` of the exact BUG integrator: the
substep defects enter additively, with constants independent of singular values. -/
theorem local_error_le (hs : IsDefectBUGStep F ε ηK ηL ηS P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ h * (bugC₁ L H * ε + bugC₂ L B H * h) + Real.exp (L * H) * (ηK + ηL) + ηS := by
  have h0 := hs.local_error hF hL hB ht₁ hh hA hA₀
  have hb := bug_bound_le hL hB.nonneg (hs.eps_nonneg (by linarith)) hh hhH
  have hη : 0 ≤ ηK + ηL := add_nonneg hs.etaK_nonneg hs.etaL_nonneg
  have hexp : Real.exp (L * h) ≤ Real.exp (L * H) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hL)
  have h3 : Real.exp (L * h) * (ηK + ηL) ≤ Real.exp (L * H) * (ηK + ηL) :=
    mul_le_mul_of_nonneg_right hexp hη
  have hsplit : (Real.exp (L * h) - 1) * (B * h + (2 * (h * (4 * L * B * h + ε)) + (ηK + ηL)))
      + (2 * (h * (4 * L * B * h + ε)) + (ηK + ηL)) + ηS
      = ((Real.exp (L * h) - 1) * (B * h + 2 * (h * (4 * L * B * h + ε)))
        + 2 * (h * (4 * L * B * h + ε))) + Real.exp (L * h) * (ηK + ηL) + ηS := by ring
  linarith

/-- **Norm conservation up to the lost component and the S-step error** (OP-TN-02; cf.
[CerutiKuschLubich2022, Thm. 4]).  If `⟪F(t, x), x⟫ = 0` on the Galerkin space `range (P₁ Q₁)`,
then `|‖Y₁‖ - ‖Y₀‖| ≤ ‖Y₀ - P₁ Q₁ Y₀‖ + ηS`, independently of the step size.  With complete
augmentation (`P₁ Y₀ = Q₁ Y₀ = Y₀`) the lost component vanishes; in general it is at most
`‖(1 - P₁) Y₀‖ + ‖(1 - Q₁) Y₀‖` (`norm_sub_apply_apply_le`), e.g. the weight of the directions
of `Y₀` dropped by a frozen bond or a rank-revealing threshold. -/
theorem abs_norm_sub_le (hs : IsDefectBUGStep F ε ηK ηL ηS P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (h01 : t₀ ≤ t₁) (hF : ∀ t x, P₁ (Q₁ x) = x → ⟪F t x, x⟫ = 0) :
    |‖Y₁‖ - ‖Y₀‖| ≤ ‖Y₀ - P₁ (Q₁ Y₀)‖ + ηS := by
  have hR : IsOrthProj (P₁ * Q₁) := hs.projP₁.mul hs.projQ₁ hs.comm₁
  have hmem : (P₁ * Q₁) (YS t₀) = YS t₀ := by
    rw [hs.sStart]
    exact hR.idem Y₀
  have hnorm := ODESolution.galerkin_norm_eq' hR hs.sSol hmem hF t₁ ⟨h01, le_rfl⟩
  rw [hs.sStart] at hnorm
  have h1 := abs_norm_sub_norm_le Y₁ (YS t₁)
  have h2 := abs_norm_sub_norm_le (P₁ (Q₁ Y₀)) Y₀
  rw [norm_sub_rev] at h2
  have h3 : |‖Y₁‖ - ‖Y₀‖| ≤ |‖Y₁‖ - ‖YS t₁‖| + |‖YS t₁‖ - ‖Y₀‖| := abs_sub_le _ _ _
  rw [hnorm] at h1 h3
  linarith [hs.sErr]

end IsDefectBUGStep

/-- Capture defect of a basis spanning a computed value up to a lost component: if
`‖y - k‖ ≤ η` (local error of the computed substep value `k`) and `‖(1 - P) k‖ ≤ μ` (the part of
`k` dropped by an incomplete augmentation or a rank-revealing threshold; `μ = 0` if `P k = k`),
then `‖(1 - P) y‖ ≤ η + μ`. -/
lemma norm_compl_le_of_computed {P : E →L[ℝ] E} (hP : IsOrthProj P) {y k : E} {η μ : ℝ}
    (hη : ‖y - k‖ ≤ η) (hμ : ‖(1 - P) k‖ ≤ μ) : ‖(1 - P) y‖ ≤ η + μ :=
  (norm_compl_le_of_approx hP y k).trans (add_le_add hη hμ)

section GlobalBUG

variable {F : ℝ → E → E} {L B ε : ℝ}

/-- **Global error of the BUG integrator with inexact substeps** (OP-SB-01; per-step defects).
Let `F` be `L`-Lipschitz (`L ≥ 0`) and bounded by `B`, `tₙ = t₀ + n h` with `0 ≤ h ≤ H`, `A`
the exact solution on `[t₀, t₀ + N h]`, and for `n < N` let step `n` be an inexact BUG step
(`IsDefectBUGStep`) from `(tₙ, Y n)` to `Y (n+1)` with old projectors `P n, Q n`, new
projectors `P' n, Q' n` and defects `ηK n, ηL n, ηS n`; `Φ n` is the exact flow from
`(tₙ, Y n)`.  Then for `n ≤ N`

    ‖Y n - A tₙ‖ ≤ e^{L n h} (‖Y 0 - A t₀‖ + n h (c₁ ε + c₂ h)
                      + ∑_{k<n} (e^{L H} (ηK k + ηL k) + ηS k)),

`c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`. -/
theorem defectBUG_global_error (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q P' Q' : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YK YL YS Φ : ℕ → ℝ → E} {ηK ηL ηS : ℕ → ℝ}
    (hstep : ∀ n < N, IsDefectBUGStep F ε (ηK n) (ηL n) (ηS n) (P n) (Q n) (P' n) (Q' n)
      (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * (n * h)) * (‖Y 0 - A t₀‖
      + n * h * (bugC₁ L H * ε + bugC₂ L B H * h)
      + ∑ k ∈ range n, (Real.exp (L * H) * (ηK k + ηL k) + ηS k)) := by
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤
      h * (bugC₁ L H * ε + bugC₂ L B H * h) + (Real.exp (L * H) * (ηK n + ηL n) + ηS n) :=
    fun n hn => by
      have := (hstep n hn).local_error_le hF hL hB (by ring) hh hhH (hΦ n hn) (hΦ₀ n hn)
      linarith
  intro n hn
  have h1 := lady_windermere_sum hF hL hh hA hΦ hΦ₀ hloc n hn
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at h1
  calc _ ≤ _ := h1
    _ = _ := by ring

/-- **Global error of the BUG integrator with inexact substeps, final form** (OP-SB-01): under
the hypotheses of `defectBUG_global_error`, if all substep defects are bounded by `η`, the
initial error by `δ`, `ε ≥ 0` and `n h ≤ T`, then

    ‖Y n - A tₙ‖ ≤ e^{L T} (δ + T (c₁ ε + c₂ h) + n (2 e^{L H} + 1) η),

i.e. `c₀ δ + c₁' ε + c₂' h + c₃ n η` with constants depending only on `L`, `B`, `T`, `H`. -/
theorem defectBUG_global_error_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ}
    {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q P' Q' : ℕ → E →L[ℝ] E}
    {Y : ℕ → E} {YK YL YS Φ : ℕ → ℝ → E} {ηK ηL ηS : ℕ → ℝ}
    (hstep : ∀ n < N, IsDefectBUGStep F ε (ηK n) (ηL n) (ηS n) (P n) (Q n) (P' n) (Q' n)
      (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {η δ T : ℝ} (hη0 : 0 ≤ η)
    (hηK : ∀ n < N, ηK n ≤ η) (hηL : ∀ n < N, ηL n ≤ η) (hηS : ∀ n < N, ηS n ≤ η)
    (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T → ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) *
      (δ + T * (bugC₁ L H * ε + bugC₂ L B H * h) + n * ((2 * Real.exp (L * H) + 1) * η)) := by
  have hH : 0 ≤ H := hh.trans hhH
  have hg : 0 ≤ bugC₁ L H * ε + bugC₂ L B H * h :=
    add_nonneg (mul_nonneg (bugC₁_nonneg hL hH) hε)
      (mul_nonneg (bugC₂_nonneg hL hB.nonneg hH) hh)
  refine lady_windermere_defect hF hL hh hA hΦ hΦ₀ hg (by positivity) (fun n hn => ?_) hδ
  have h1 := (hstep n hn).local_error_le hF hL hB (by ring) hh hhH (hΦ n hn) (hΦ₀ n hn)
  have he := Real.exp_pos (L * H)
  have h2 : Real.exp (L * H) * (ηK n + ηL n) ≤ Real.exp (L * H) * (η + η) :=
    mul_le_mul_of_nonneg_left (add_le_add (hηK n hn) (hηL n hn)) he.le
  linarith [hηS n hn]

end GlobalBUG


/-! ### Auxiliary real-number facts -/

section Aux

omit [InnerProductSpace ℝ E] in
/-- A Lipschitz bound with constant `L` is also one with `max L 0`. -/
lemma isLipschitzField_max_zero {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L) :
    IsLipschitzField F (max L 0) := fun t x y =>
  (hF t x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

/-- `a x + b y + c z + d w ≤ (a + b + c + d) (x + y + z + w)` for nonnegative reals. -/
lemma add4_mul_le {a b c d x y z w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    a * x + b * y + c * z + d * w ≤ (a + b + c + d) * (x + y + z + w) := by
  nlinarith [mul_nonneg ha hy, mul_nonneg ha hz, mul_nonneg ha hw, mul_nonneg hb hx,
    mul_nonneg hb hz, mul_nonneg hb hw, mul_nonneg hc hx, mul_nonneg hc hy, mul_nonneg hc hw,
    mul_nonneg hd hx, mul_nonneg hd hy, mul_nonneg hd hz]

/-- **Accumulated defects of a substep solver of order `q`** (OP-HO-05).  If every per-step
defect is at most `C_η h^{q+1}` and `n h ≤ T`, then `n η ≤ T C_η h^q`. -/
lemma natCast_mul_le_of_order {n : ℕ} {h T η Cη : ℝ} {q : ℕ} (hh : 0 ≤ h)
    (hT : (n : ℝ) * h ≤ T) (hC : 0 ≤ Cη) (hη : η ≤ Cη * h ^ (q + 1)) :
    (n : ℝ) * η ≤ T * Cη * h ^ q := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hq : 0 ≤ Cη * h ^ q := mul_nonneg hC (pow_nonneg hh q)
  calc (n : ℝ) * η ≤ n * (Cη * h ^ (q + 1)) := mul_le_mul_of_nonneg_left hη hn
    _ = (n * h) * (Cη * h ^ q) := by ring
    _ ≤ T * (Cη * h ^ q) := mul_le_mul_of_nonneg_right hT hq
    _ = T * Cη * h ^ q := by ring

/-- **Accumulated tolerances of iterative substep solvers** (OP-OT-05).  If every solve is
accurate to the tolerance `τ ≥ 0` and `n h ≤ T` with `h > 0`, then `n τ ≤ T τ / h`. -/
lemma natCast_mul_le_div {n : ℕ} {h T τ : ℝ} (hh : 0 < h) (hT : (n : ℝ) * h ≤ T)
    (hτ : 0 ≤ τ) : (n : ℝ) * τ ≤ T * τ / h := by
  rw [le_div_iff₀ hh]
  calc (n : ℝ) * τ * h = (n * h) * τ := by ring
    _ ≤ T * τ := mul_le_mul_of_nonneg_right hT hτ

end Aux

/-! ### Order of the substep solver (OP-HO-05) and iterative solves (OP-OT-05) -/

section Order

variable {F : ℝ → E → E} {L B ε : ℝ}

/-- **Order preservation with inexact substeps** (OP-HO-05).  Under the hypotheses of
`defectBUG_global_error_le`, if every substep is solved by a one-step method of order `q`, so
that all endpoint errors are at most `C_η h^{q+1}` (`C_η ≥ 0`), then for `n h ≤ T`

    ‖Y n - A tₙ‖ ≤ e^{L T} (δ + T (c₁ ε + c₂ h) + (2 e^{L H} + 1) T C_η h^q),

i.e. the global error is `O(δ + ε + h + h^q) = O(δ + ε + h^{min(1, q)})` with constants depending
only on `L, B, T, H, C_η`.  For `q ≥ 1` the robust first order is kept
(`defectBUG_global_error_first_order`); `defectBUG_sharp` shows that the term `n η` (hence the
order reduction to `q` for `q = 0`) cannot be improved. -/
theorem defectBUG_global_error_order (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ}
    {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q P' Q' : ℕ → E →L[ℝ] E}
    {Y : ℕ → E} {YK YL YS Φ : ℕ → ℝ → E} {ηK ηL ηS : ℕ → ℝ}
    (hstep : ∀ n < N, IsDefectBUGStep F ε (ηK n) (ηL n) (ηS n) (P n) (Q n) (P' n) (Q' n)
      (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {Cη : ℝ} {q : ℕ} (hC : 0 ≤ Cη)
    (hηK : ∀ n < N, ηK n ≤ Cη * h ^ (q + 1)) (hηL : ∀ n < N, ηL n ≤ Cη * h ^ (q + 1))
    (hηS : ∀ n < N, ηS n ≤ Cη * h ^ (q + 1)) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T → ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) *
      (δ + T * (bugC₁ L H * ε + bugC₂ L B H * h)
        + (2 * Real.exp (L * H) + 1) * (T * Cη * h ^ q)) := by
  intro n hn hT
  have h1 := defectBUG_global_error_le hF hL hB hε hh hhH hA hstep hΦ hΦ₀
    (mul_nonneg hC (pow_nonneg hh _)) hηK hηL hηS hδ n hn hT
  have h2 := natCast_mul_le_of_order hh hT hC (le_refl (Cη * h ^ (q + 1)))
  have hk : 0 ≤ 2 * Real.exp (L * H) + 1 := by positivity
  have h3 : (n : ℝ) * ((2 * Real.exp (L * H) + 1) * (Cη * h ^ (q + 1)))
      ≤ (2 * Real.exp (L * H) + 1) * (T * Cη * h ^ q) := by
    calc (n : ℝ) * ((2 * Real.exp (L * H) + 1) * (Cη * h ^ (q + 1)))
        = (2 * Real.exp (L * H) + 1) * (n * (Cη * h ^ (q + 1))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hk
  exact h1.trans (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le)

/-- **Inexact substeps of order `q ≥ 1` keep the robust first order** (OP-HO-05, `p = 1`):
under the hypotheses of `defectBUG_global_error_order` with `q ≥ 1`,

    ‖Y n - A tₙ‖ ≤ e^{L T} (δ + T c₁ ε + T (c₂ + (2 e^{L H} + 1) C_η H^{q-1}) h). -/
theorem defectBUG_global_error_first_order (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ}
    {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q P' Q' : ℕ → E →L[ℝ] E}
    {Y : ℕ → E} {YK YL YS Φ : ℕ → ℝ → E} {ηK ηL ηS : ℕ → ℝ}
    (hstep : ∀ n < N, IsDefectBUGStep F ε (ηK n) (ηL n) (ηS n) (P n) (Q n) (P' n) (Q' n)
      (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {Cη : ℝ} {q : ℕ} (hq : 1 ≤ q) (hC : 0 ≤ Cη)
    (hηK : ∀ n < N, ηK n ≤ Cη * h ^ (q + 1)) (hηL : ∀ n < N, ηL n ≤ Cη * h ^ (q + 1))
    (hηS : ∀ n < N, ηS n ≤ Cη * h ^ (q + 1)) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T → ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) *
      (δ + T * bugC₁ L H * ε
        + T * (bugC₂ L B H + (2 * Real.exp (L * H) + 1) * Cη * H ^ (q - 1)) * h) := by
  intro n hn hT
  have h1 := defectBUG_global_error_order hF hL hB hε hh hhH hA hstep hΦ hΦ₀ hC hηK hηL hηS hδ
    n hn hT
  have hT0 : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg n) hh).trans hT
  have hpow : h ^ q ≤ H ^ (q - 1) * h := by
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    rw [pow_succ, Nat.add_sub_cancel]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hh hhH k) hh
  have hk : 0 ≤ (2 * Real.exp (L * H) + 1) * (T * Cη) := by positivity
  have h2 : (2 * Real.exp (L * H) + 1) * (T * Cη * h ^ q)
      ≤ (2 * Real.exp (L * H) + 1) * (T * Cη) * (H ^ (q - 1) * h) := by
    rw [← mul_assoc ((2 * Real.exp (L * H) + 1))]
    exact mul_le_mul_of_nonneg_left hpow hk
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  have h3 : (2 * Real.exp (L * H) + 1) * (T * Cη) * (H ^ (q - 1) * h)
      = T * ((2 * Real.exp (L * H) + 1) * Cη * H ^ (q - 1)) * h := by ring
  nlinarith

/-- **Iterative (Krylov) substep solves to a tolerance `τ`** (OP-OT-05).  Under the hypotheses
of `defectBUG_global_error_le` with all substep endpoint errors at most `τ ≥ 0` and `h > 0`,

    ‖Y n - A tₙ‖ ≤ e^{L T} (δ + T (c₁ ε + c₂ h) + (2 e^{L H} + 1) T τ / h):

the solver tolerance accumulates like `n τ ≤ T τ / h`, an `O(h)` contribution exactly when
`τ = O(h²)` (sufficiency: `defectBUG_global_error_order` with `q = 1`; necessity of the `n τ`
term: `defectBUG_sharp`). -/
theorem defectBUG_global_error_of_tolerance (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 < h) (hhH : h ≤ H) {N : ℕ}
    {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q P' Q' : ℕ → E →L[ℝ] E}
    {Y : ℕ → E} {YK YL YS Φ : ℕ → ℝ → E} {ηK ηL ηS : ℕ → ℝ}
    (hstep : ∀ n < N, IsDefectBUGStep F ε (ηK n) (ηL n) (ηS n) (P n) (Q n) (P' n) (Q' n)
      (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {τ : ℝ} (hτ : 0 ≤ τ)
    (hηK : ∀ n < N, ηK n ≤ τ) (hηL : ∀ n < N, ηL n ≤ τ) (hηS : ∀ n < N, ηS n ≤ τ) {δ T : ℝ}
    (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T → ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) *
      (δ + T * (bugC₁ L H * ε + bugC₂ L B H * h) + (2 * Real.exp (L * H) + 1) * (T * τ / h)) := by
  intro n hn hT
  have h1 := defectBUG_global_error_le hF hL hB hε hh.le hhH hA hstep hΦ hΦ₀ hτ hηK hηL hηS hδ
    n hn hT
  have h2 := natCast_mul_le_div hh hT hτ
  have hk : 0 ≤ 2 * Real.exp (L * H) + 1 := by positivity
  have h3 : (n : ℝ) * ((2 * Real.exp (L * H) + 1) * τ)
      ≤ (2 * Real.exp (L * H) + 1) * (T * τ / h) := by
    calc (n : ℝ) * ((2 * Real.exp (L * H) + 1) * τ)
        = (2 * Real.exp (L * H) + 1) * (n * τ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hk
  exact h1.trans (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le)

end Order

/-! ### Sharpness of the accumulated defect -/

/-- A constant function solves `y' = 0`, written with identity projectors. -/
lemma odeSolution_const_zero (c a b : ℝ) (R : ℝ →L[ℝ] ℝ) :
    ODESolution (fun _ x => R ((fun (_ : ℝ) (_ : ℝ) => (0 : ℝ)) 0 x)) (fun _ => c) a b :=
  ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) c⟩

/-- **The accumulated defect `n η` is attained** (sharpness for OP-SB-01, OP-HO-05, OP-OT-05).
On `E = ℝ` with `F = 0` (so `L = B = ε = 0` and the exact solution `A ≡ 0`), identity
projectors, and S-step results that are off by exactly `η ≥ 0` per step (`Y k = k η`), every
step is an `IsDefectBUGStep` with defects `(0, 0, η)`, and the error after `n` steps is exactly
`n η`.  With `η = C_η h^{q+1}` and `n = T / h` this is `T C_η h^q`: the bound of
`defectBUG_global_error_order` is attained up to the factor `2 e^{L H} + 1`, so an order-`q`
substep solver reduces the global order to `q` when `q < 1` (and a tolerance `τ` gives exactly
`T τ / h`, OP-OT-05). -/
theorem defectBUG_sharp {η : ℝ} (hη : 0 ≤ η) (h : ℝ) :
    (∀ k : ℕ, IsDefectBUGStep (E := ℝ) (fun _ _ => 0) 0 0 0 η 1 1 1 1 (k * h) ((k + 1) * h)
      (k * η) (fun _ => k * η) (fun _ => k * η) (fun _ => k * η) ((k + 1 : ℕ) * η)) ∧
    ∀ n : ℕ, ‖(n : ℝ) * η - 0‖ = n * η := by
  refine ⟨fun k => ?_, fun n => by
    rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hη)]⟩
  exact {
    projP₀ := IsOrthProj.one
    projQ₀ := IsOrthProj.one
    projP₁ := IsOrthProj.one
    projQ₁ := IsOrthProj.one
    comm₁ := fun _ => rfl
    kSol := odeSolution_const_zero _ _ _ 1
    kStart := rfl
    kNormal := fun _ _ => by simp
    kDefect := by simp
    lSol := odeSolution_const_zero _ _ _ 1
    lStart := rfl
    lNormal := fun _ _ => by simp
    lDefect := by simp
    sSol := odeSolution_const_zero _ _ _ 1
    sStart := by simp
    sErr := by
      rw [Real.norm_eq_abs]
      push_cast
      rw [show ((k : ℝ) + 1) * η - k * η = η by ring, abs_of_nonneg hη] }

/-! ### Computed substep values (fixed-rank BUG) -/

/-- One step of the fixed-rank **BUG integrator with inexactly solved substeps**, in the
"computed values" form (OP-SB-01, OP-HO-05): exact K-, L-, S-trajectories `YK`, `YL`, `YS`,
computed values `K₁`, `L₁`, `Ŷ₁` within `η` of their endpoints, new bases spanning the computed
`K₁`, `L₁` (fixed rank: no augmentation, S-step started at `P₁ Q₁ Y₀`); the new approximation is
`Ŷ₁`.  This is a special case of `IsDefectBUGStep` (`IsInexactBUGStep.toDefect`). -/
structure IsInexactBUGStep (F : ℝ → E → E) (ε η : ℝ) (P₀ Q₀ P₁ Q₁ : E →L[ℝ] E) (t₀ t₁ : ℝ)
    (Y₀ : E) (YK YL YS : ℝ → E) (K₁ L₁ Ŷ₁ : E) : Prop where
  projP₀ : IsOrthProj P₀
  projQ₀ : IsOrthProj Q₀
  projP₁ : IsOrthProj P₁
  projQ₁ : IsOrthProj Q₁
  /-- The new left and right projectors commute. -/
  comm₁ : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)
  /-- Exact K-step `YK' = Q₀ F(t, YK)`. -/
  kSol : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁
  kStart : YK t₀ = Y₀
  /-- Error of the computed K-step value. -/
  kApprox : ‖YK t₁ - K₁‖ ≤ η
  /-- The new left basis spans the computed `K₁`. -/
  kCap : P₁ K₁ = K₁
  kNormal : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε
  /-- Exact L-step `YL' = P₀ F(t, YL)`. -/
  lSol : ODESolution (fun t x => P₀ (F t x)) YL t₀ t₁
  lStart : YL t₀ = Y₀
  /-- Error of the computed L-step value. -/
  lApprox : ‖YL t₁ - L₁‖ ≤ η
  /-- The new right basis spans the computed `L₁`. -/
  lCap : Q₁ L₁ = L₁
  lNormal : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε
  /-- Exact Galerkin S-step `YS' = P₁ Q₁ F(t, YS)` from `P₁ Q₁ Y₀`. -/
  sSol : ODESolution (fun t x => P₁ (Q₁ (F t x))) YS t₀ t₁
  sStart : YS t₀ = P₁ (Q₁ Y₀)
  /-- Error of the computed S-step value. -/
  sApprox : ‖Ŷ₁ - YS t₁‖ ≤ η

/-- A step with computed substep values is a step with capture defects `η` and S-step error
`η`: the basis spanning the computed `K₁` misses at most `‖YK t₁ - K₁‖ ≤ η` of `YK t₁`. -/
theorem IsInexactBUGStep.toDefect {F : ℝ → E → E} {ε η : ℝ} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E}
    {t₀ t₁ : ℝ} {Y₀ : E} {YK YL YS : ℝ → E} {K₁ L₁ Ŷ₁ : E}
    (hs : IsInexactBUGStep F ε η P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS K₁ L₁ Ŷ₁) :
    IsDefectBUGStep F ε η η η P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Ŷ₁ where
  projP₀ := hs.projP₀
  projQ₀ := hs.projQ₀
  projP₁ := hs.projP₁
  projQ₁ := hs.projQ₁
  comm₁ := hs.comm₁
  kSol := hs.kSol
  kStart := hs.kStart
  kNormal := hs.kNormal
  kDefect := (norm_compl_le_of_computed hs.projP₁ hs.kApprox (μ := 0)
    (by simp [hs.kCap])).trans_eq (add_zero η)
  lSol := hs.lSol
  lStart := hs.lStart
  lNormal := hs.lNormal
  lDefect := (norm_compl_le_of_computed hs.projQ₁ hs.lApprox (μ := 0)
    (by simp [hs.lCap])).trans_eq (add_zero η)
  sSol := hs.sSol
  sStart := hs.sStart
  sErr := hs.sApprox

/-- The constant of `inexactBUG_global_error`:
`e^{L⁺ T} (2 + T c₁ + T c₂ + 2 e^{L⁺ H})`, `L⁺ = max L 0`, `cᵢ` the BUG constants. -/
noncomputable def inexactBUGConst (L B T H : ℝ) : ℝ :=
  Real.exp (max L 0 * T) * (1 + T * bugC₁ (max L 0) H + T * bugC₂ (max L 0) B H
    + (2 * Real.exp (max L 0 * H) + 1))

/-- **Robust global error of the fixed-rank BUG integrator with inexact substeps** (OP-SB-01,
OP-HO-05; Ceruti–Lubich [CerutiLubich2022], remark on inexact substeps, here proved).  With
substep errors `η` per step, `‖Y n - A tₙ‖ ≤ C (δ + ε + h + n η)` for `n h ≤ T`, where
`C = inexactBUGConst L B T H` depends only on `L, B, T, H` (never on `E`, the rank, or singular
values).  No sign condition on `L` is needed (`max L 0` is used). -/
theorem inexactBUG_global_error (L B T H : ℝ) :
    ∃ C : ℝ, ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : ℝ → E → E}
      {ε η t₀ h : ℝ} {N : ℕ} {A : ℝ → E} {P Q : ℕ → E →L[ℝ] E} {Y K₁ L₁ : ℕ → E}
      {YK YL YS Φ : ℕ → ℝ → E},
      IsLipschitzField F L → IsBoundedField F B → 0 ≤ h → h ≤ H → 0 ≤ ε →
      ODESolution F A t₀ (t₀ + N * h) →
      (∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h)) →
      (∀ n < N, Φ n (t₀ + n * h) = Y n) →
      (∀ n < N, IsInexactBUGStep F ε η (P n) (Q n) (P (n + 1)) (Q (n + 1)) (t₀ + n * h)
        (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n) (K₁ n) (L₁ n) (Y (n + 1))) →
      ∀ n ≤ N, (n : ℝ) * h ≤ T →
        ‖Y n - A (t₀ + n * h)‖ ≤ C * (‖Y 0 - A t₀‖ + ε + h + n * η) := by
  refine ⟨inexactBUGConst L B T H, ?_⟩
  intro E _ _ F ε η t₀ h N A P Q Y K₁ L₁ YK YL YS Φ hF hB hh hhH hε hA hΦ hΦ₀ hstep n hn hT
  have hL0 : 0 ≤ max L 0 := le_max_right _ _
  have hF' := isLipschitzField_max_zero hF
  have hH : 0 ≤ H := hh.trans hhH
  have hT0 : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg n) hh).trans hT
  have hB0 : 0 ≤ B := hB.nonneg
  have hc₁ := bugC₁_nonneg hL0 hH
  have hc₂ := bugC₂_nonneg hL0 hB0 hH
  have he1 : 1 ≤ Real.exp (max L 0 * T) := Real.one_le_exp (mul_nonneg hL0 hT0)
  have hk : 0 ≤ 2 * Real.exp (max L 0 * H) + 1 := by positivity
  have hδ0 := norm_nonneg (Y 0 - A t₀)
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · have hC1 : 1 ≤ inexactBUGConst L B T H := by
      unfold inexactBUGConst
      have : 1 ≤ 1 + T * bugC₁ (max L 0) H + T * bugC₂ (max L 0) B H
          + (2 * Real.exp (max L 0 * H) + 1) := by
        have := mul_nonneg hT0 hc₁
        have := mul_nonneg hT0 hc₂
        linarith
      nlinarith
    rw [Nat.cast_zero, zero_mul, add_zero, zero_mul, add_zero]
    nlinarith
  · have hη0 : 0 ≤ η := (norm_nonneg _).trans (hstep 0 (by omega)).sApprox
    have h1 := defectBUG_global_error_le hF' hL0 hB hε hh hhH hA (P' := fun k => P (k + 1))
      (Q' := fun k => Q (k + 1)) (ηK := fun _ => η) (ηL := fun _ => η) (ηS := fun _ => η)
      (fun k hk => (hstep k hk).toDefect) hΦ hΦ₀ hη0 (fun _ _ => le_rfl) (fun _ _ => le_rfl)
      (fun _ _ => le_rfl) le_rfl n hn hT
    have h2 := add4_mul_le zero_le_one (mul_nonneg hT0 hc₁) (mul_nonneg hT0 hc₂) hk hδ0 hε hh
      (mul_nonneg (Nat.cast_nonneg n) hη0)
    have h3 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (max L 0 * T)).le
    calc _ ≤ _ := h1
      _ = Real.exp (max L 0 * T) * (1 * ‖Y 0 - A t₀‖ + T * bugC₁ (max L 0) H * ε
          + T * bugC₂ (max L 0) B H * h + (2 * Real.exp (max L 0 * H) + 1) * (n * η)) := by
          ring
      _ ≤ _ := h3
      _ = _ := by unfold inexactBUGConst; ring


/-! ### Tucker BUG with capture defects and inexact substeps -/

section Tucker

variable {F : ℝ → E → E} {L B ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E} {d : ℕ}

/-- One step of the **Tucker BUG integrator** (`IsTuckerBUGStep`, [CerutiLubich2022, §5]) with
**capture defects** and an inexact core step (OP-SB-01, OP-TN-02): the new mode-`i` basis
captures the exact mode-`i` K-step value only up to `‖(1 - P₁ i) (YK i t₁)‖ ≤ ηK`, and the new
approximation `Y₁` is within `ηS` of the exact core-step value `YS t₁`. -/
structure IsDefectTuckerBUGStep (F : ℝ → E → E) (ε ηK ηS : ℝ) {d : ℕ}
    (Q₀ P₁ : Fin d → E →L[ℝ] E) (t₀ t₁ : ℝ) (Y₀ : E) (YK : Fin d → ℝ → E) (YS : ℝ → E)
    (Y₁ : E) : Prop where
  projQ₀ : ∀ i, IsOrthProj (Q₀ i)
  projP₁ : ∀ i, IsOrthProj (P₁ i)
  /-- The new mode projectors commute. -/
  comm₁ : ∀ i j x, P₁ i (P₁ j x) = P₁ j (P₁ i x)
  /-- Exact mode-`i` K-step `YK i' = Q₀ i F(t, YK i)`. -/
  kSol : ∀ i, ODESolution (fun t x => Q₀ i (F t x)) (YK i) t₀ t₁
  kStart : ∀ i, YK i t₀ = Y₀
  /-- Capture defect of the new mode-`i` basis. -/
  kDefect : ∀ i, ‖(1 - P₁ i) (YK i t₁)‖ ≤ ηK
  kNormal : ∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁ i) ((1 - Q₀ i) (F t (YK i t₁)))‖ ≤ ε
  /-- Exact core (Galerkin) step `YS' = Π F(t, YS)`, `Π = P₁ 0 ∘ ⋯ ∘ P₁ (d-1)`. -/
  sSol : ODESolution (fun t x => modeProd P₁ (F t x)) YS t₀ t₁
  sStart : YS t₀ = modeProd P₁ Y₀
  /-- Error of the computed core step. -/
  sErr : ‖Y₁ - YS t₁‖ ≤ ηS

/-- An exact Tucker BUG step is a Tucker step with zero defects. -/
theorem ofTuckerBUGStep {Q₀ P₁ : Fin d → E →L[ℝ] E} {Y₀ : E} {YK : Fin d → ℝ → E}
    {YS : ℝ → E} (hs : IsTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS) :
    IsDefectTuckerBUGStep F ε 0 0 Q₀ P₁ t₀ t₁ Y₀ YK YS (YS t₁) where
  projQ₀ := hs.projQ₀
  projP₁ := hs.projP₁
  comm₁ := hs.comm₁
  kSol := hs.kSol
  kStart := hs.kStart
  kDefect i := by simp [hs.kCap i]
  kNormal := hs.kNormal
  sSol := hs.sSol
  sStart := hs.sStart
  sErr := by simp

namespace IsDefectTuckerBUGStep

variable {ηK ηS : ℝ} {Q₀ P₁ : Fin d → E →L[ℝ] E} {Y₀ : E} {YK : Fin d → ℝ → E} {YS : ℝ → E}
  {Y₁ : E}

/-- `d ε ≥ 0` on a nonempty step. -/
lemma natCast_mul_eps_nonneg (hs : IsDefectTuckerBUGStep F ε ηK ηS Q₀ P₁ t₀ t₁ Y₀ YK YS Y₁)
    (h01 : t₀ ≤ t₁) : 0 ≤ (d : ℝ) * ε := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · exact mul_nonneg (Nat.cast_nonneg d)
      ((norm_nonneg _).trans (hs.kNormal ⟨0, hd⟩ t₀ ⟨le_rfl, h01⟩))

/-- `d ηK ≥ 0`. -/
lemma natCast_mul_etaK_nonneg (hs : IsDefectTuckerBUGStep F ε ηK ηS Q₀ P₁ t₀ t₁ Y₀ YK YS Y₁) :
    0 ≤ (d : ℝ) * ηK := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · exact mul_nonneg (Nat.cast_nonneg d) ((norm_nonneg _).trans (hs.kDefect ⟨0, hd⟩))

lemma etaS_nonneg (hs : IsDefectTuckerBUGStep F ε ηK ηS Q₀ P₁ t₀ t₁ Y₀ YK YS Y₁) : 0 ≤ ηS :=
  (norm_nonneg _).trans hs.sErr

/-- **Tucker capture with defects** (Lemma 6 of [CerutiLubich2022] with capture defects):
`‖A t₁ - Π A t₁‖ ≤ d (ϑ + ηK)`, `ϑ = h (4 L B h + ε)`: the mode defects add up over the `d`
modes (`norm_sub_modeProd_apply_le`). -/
theorem capture (hs : IsDefectTuckerBUGStep F ε ηK ηS Q₀ P₁ t₀ t₁ Y₀ YK YS Y₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖A t₁ - modeProd P₁ (A t₁)‖ ≤ d * (h * (4 * L * B * h + ε) + ηK) := by
  refine (norm_sub_modeProd_apply_le (fun i => (hs.projP₁ i).norm_le) (A t₁)).trans ?_
  calc ∑ i, ‖A t₁ - P₁ i (A t₁)‖ ≤ ∑ _i : Fin d, (h * (4 * L * B * h + ε) + ηK) :=
        Finset.sum_le_sum fun i _ => by
          have := kstep_capture_defect hF hL hB (hs.projP₁ i) (hs.projQ₀ i) ht₁ hh hA
            (hs.kSol i) ((hs.kStart i).trans hA₀.symm) (hs.kDefect i) (hs.kNormal i)
          simpa using this
    _ = d * (h * (4 * L * B * h + ε) + ηK) := by simp [mul_add]

/-- **Local error of the Tucker BUG integrator with defects** (explicit form):
`‖Y₁ - A t₁‖ ≤ (e^{L h} - 1) (B h + θ) + θ + ηS` with `θ = d (ϑ + ηK)`. -/
theorem local_error (hs : IsDefectTuckerBUGStep F ε ηK ηS Q₀ P₁ t₀ t₁ Y₀ YK YS Y₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + d * (h * (4 * L * B * h + ε) + ηK))
      + d * (h * (4 * L * B * h + ε) + ηK) + ηS := by
  have hS := galerkin_step_error (IsOrthProj.modeProd hs.projP₁ hs.comm₁) hF hL hB ht₁ hh hA
    hs.sSol (by rw [hs.sStart, hA₀]) (hs.capture hF hL hB ht₁ hh hA hA₀)
  have h1 := norm_sub_le_norm_sub_add_norm_sub Y₁ (YS t₁) (A t₁)
  linarith [hs.sErr]

/-- **Local error of the Tucker BUG integrator with defects, `O`-form** (OP-SB-01): for
`0 ≤ h ≤ H`, `‖Y₁ - A t₁‖ ≤ h (c₁ ε + c₂ h) + e^{L H} d ηK + ηS` with the Tucker constants
`c₁ = tuckerC₁ d L H`, `c₂ = tuckerC₂ d L B H` (linear in `d`). -/
theorem local_error_le (hs : IsDefectTuckerBUGStep F ε ηK ηS Q₀ P₁ t₀ t₁ Y₀ YK YS Y₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ h * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h)
      + Real.exp (L * H) * (d * ηK) + ηS := by
  have h0 := hs.local_error hF hL hB ht₁ hh hA hA₀
  have hb := tucker_bound_le hL hB.nonneg (hs.natCast_mul_eps_nonneg (by linarith)) hh hhH
  have hη := hs.natCast_mul_etaK_nonneg
  have hexp : Real.exp (L * h) ≤ Real.exp (L * H) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hL)
  have h3 : Real.exp (L * h) * (d * ηK) ≤ Real.exp (L * H) * (d * ηK) :=
    mul_le_mul_of_nonneg_right hexp hη
  have hsplit : (Real.exp (L * h) - 1) * (B * h + d * (h * (4 * L * B * h + ε) + ηK))
      + d * (h * (4 * L * B * h + ε) + ηK) + ηS
      = ((Real.exp (L * h) - 1) * (B * h + d * (h * (4 * L * B * h + ε)))
        + d * (h * (4 * L * B * h + ε))) + Real.exp (L * h) * (d * ηK) + ηS := by ring
  linarith

end IsDefectTuckerBUGStep

/-- **Global error of the Tucker BUG integrator with defects** (OP-SB-01 for Tucker, with the
explicit dependence on the tensor order `d` asked for there).  If every step `n < N` is an
`IsDefectTuckerBUGStep` with defects at most `η ≥ 0`, `ε ≥ 0`, `‖Y 0 - A t₀‖ ≤ δ` and
`n h ≤ T`, then

    ‖Y n - A tₙ‖ ≤ e^{L T} (δ + T (c₁ ε + c₂ h) + n (d e^{L H} + 1) η),

`c₁ = tuckerC₁ d L H`, `c₂ = tuckerC₂ d L B H`.  All constants grow at most linearly in `d`
(not like `d e^{d L h}` as feared for the recursive Tucker KSL in OP-SB-01). -/
theorem defectTuckerBUG_global_error_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε : 0 ≤ ε) {h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {Q P : ℕ → Fin d → E →L[ℝ] E} {Y : ℕ → E}
    {YK : ℕ → Fin d → ℝ → E} {YS Φ : ℕ → ℝ → E} {ηK ηS : ℕ → ℝ}
    (hstep : ∀ n < N, IsDefectTuckerBUGStep F ε (ηK n) (ηS n) (Q n) (P n) (t₀ + n * h)
      (t₀ + (n + 1) * h) (Y n) (YK n) (YS n) (Y (n + 1)))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {η δ T : ℝ} (hη0 : 0 ≤ η)
    (hηK : ∀ n < N, ηK n ≤ η) (hηS : ∀ n < N, ηS n ≤ η) (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T → ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) *
      (δ + T * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h)
        + n * ((d * Real.exp (L * H) + 1) * η)) := by
  have hH : 0 ≤ H := hh.trans hhH
  have hg : 0 ≤ tuckerC₁ d L H * ε + tuckerC₂ d L B H * h :=
    add_nonneg (mul_nonneg (tuckerC₁_nonneg d hL hH) hε)
      (mul_nonneg (tuckerC₂_nonneg d hL hB.nonneg hH) hh)
  refine lady_windermere_defect hF hL hh hA hΦ hΦ₀ hg (by positivity) (fun n hn => ?_) hδ
  have h1 := (hstep n hn).local_error_le hF hL hB (by ring) hh hhH (hΦ n hn) (hΦ₀ n hn)
  have he := Real.exp_pos (L * H)
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h2 : Real.exp (L * H) * (d * ηK n) ≤ Real.exp (L * H) * (d * η) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hηK n hn) hd) he.le
  have h3 : Real.exp (L * H) * (d * η) + η = (d * Real.exp (L * H) + 1) * η := by ring
  linarith [hηS n hn]

/-- One step of the **Tucker BUG integrator with inexactly solved substeps** in the "computed
values" form (OP-SB-01): `IsTuckerBUGStep` with computed mode values `K₁ i` within `η` of
`YK i t₁`, captured by the new mode bases, and a computed core result `Ŷ₁` within `η` of
`YS t₁`.  Special case of `IsDefectTuckerBUGStep` (`IsInexactTuckerBUGStep.toDefect`). -/
structure IsInexactTuckerBUGStep (F : ℝ → E → E) (ε η : ℝ) {d : ℕ}
    (Q₀ P₁ : Fin d → E →L[ℝ] E) (t₀ t₁ : ℝ) (Y₀ : E) (YK : Fin d → ℝ → E) (YS : ℝ → E)
    (K₁ : Fin d → E) (Ŷ₁ : E) : Prop where
  projQ₀ : ∀ i, IsOrthProj (Q₀ i)
  projP₁ : ∀ i, IsOrthProj (P₁ i)
  /-- The new mode projectors commute. -/
  comm₁ : ∀ i j x, P₁ i (P₁ j x) = P₁ j (P₁ i x)
  /-- Exact mode-`i` K-step. -/
  kSol : ∀ i, ODESolution (fun t x => Q₀ i (F t x)) (YK i) t₀ t₁
  kStart : ∀ i, YK i t₀ = Y₀
  /-- Error of the computed mode-`i` K-step value. -/
  kApprox : ∀ i, ‖YK i t₁ - K₁ i‖ ≤ η
  /-- The new mode-`i` basis spans the computed value. -/
  kCap : ∀ i, P₁ i (K₁ i) = K₁ i
  kNormal : ∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁ i) ((1 - Q₀ i) (F t (YK i t₁)))‖ ≤ ε
  /-- Exact core step. -/
  sSol : ODESolution (fun t x => modeProd P₁ (F t x)) YS t₀ t₁
  sStart : YS t₀ = modeProd P₁ Y₀
  /-- Error of the computed core-step value. -/
  sApprox : ‖Ŷ₁ - YS t₁‖ ≤ η

/-- A Tucker step with computed substep values is a Tucker step with defects `(η, η)`. -/
theorem IsInexactTuckerBUGStep.toDefect {ε η : ℝ} {Q₀ P₁ : Fin d → E →L[ℝ] E} {Y₀ : E}
    {YK : Fin d → ℝ → E} {YS : ℝ → E} {K₁ : Fin d → E} {Ŷ₁ : E}
    (hs : IsInexactTuckerBUGStep F ε η Q₀ P₁ t₀ t₁ Y₀ YK YS K₁ Ŷ₁) :
    IsDefectTuckerBUGStep F ε η η Q₀ P₁ t₀ t₁ Y₀ YK YS Ŷ₁ where
  projQ₀ := hs.projQ₀
  projP₁ := hs.projP₁
  comm₁ := hs.comm₁
  kSol := hs.kSol
  kStart := hs.kStart
  kDefect i := (norm_compl_le_of_computed (hs.projP₁ i) (hs.kApprox i) (μ := 0)
    (by simp [hs.kCap i])).trans_eq (add_zero η)
  kNormal := hs.kNormal
  sSol := hs.sSol
  sStart := hs.sStart
  sErr := hs.sApprox

/-- The constant of `inexactTuckerBUG_global_error` (independent of `d`):
`e^{L⁺ T} (1 + T k₁ + T k₂ + e^{L⁺ H})` with `k₁ = 1 + L⁺ H e^{L⁺ H}`,
`k₂ = L⁺ B (4 + e^{L⁺ H} (1 + 4 L⁺ H))`, `L⁺ = max L 0`. -/
noncomputable def inexactTuckerConst (L B T H : ℝ) : ℝ :=
  Real.exp (max L 0 * T) * (1 + T * (1 + max L 0 * H * Real.exp (max L 0 * H))
    + T * (max L 0 * B * (4 + Real.exp (max L 0 * H) * (1 + 4 * max L 0 * H)))
    + Real.exp (max L 0 * H))

/-- **Robust global error of the Tucker BUG integrator with inexact substeps** (OP-SB-01, with
the explicit dependence on the tensor order `d`; [CerutiLubich2022, Thm. 7], here with inexact
substeps).  `‖Y n - A tₙ‖ ≤ C (δ + (d + 1) (ε + h + n η))` for `n h ≤ T`, with
`C = inexactTuckerConst L B T H` depending only on `L, B, T, H` (not on `d`, `E` or singular
values of matricizations): the order-`d` dependence is exactly linear. -/
theorem inexactTuckerBUG_global_error (L B T H : ℝ) :
    ∃ C : ℝ, ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : ℝ → E → E}
      {ε η t₀ h : ℝ} {d N : ℕ} {A : ℝ → E} {Q P : ℕ → Fin d → E →L[ℝ] E} {Y : ℕ → E}
      {K₁ : ℕ → Fin d → E} {YK : ℕ → Fin d → ℝ → E} {YS Φ : ℕ → ℝ → E},
      IsLipschitzField F L → IsBoundedField F B → 0 ≤ h → h ≤ H → 0 ≤ ε →
      ODESolution F A t₀ (t₀ + N * h) →
      (∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h)) →
      (∀ n < N, Φ n (t₀ + n * h) = Y n) →
      (∀ n < N, IsInexactTuckerBUGStep F ε η (Q n) (P n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
        (YK n) (YS n) (K₁ n) (Y (n + 1))) →
      ∀ n ≤ N, (n : ℝ) * h ≤ T →
        ‖Y n - A (t₀ + n * h)‖ ≤ C * (‖Y 0 - A t₀‖ + (d + 1) * (ε + h + n * η)) := by
  refine ⟨inexactTuckerConst L B T H, ?_⟩
  intro E _ _ F ε η t₀ h d N A Q P Y K₁ YK YS Φ hF hB hh hhH hε hA hΦ hΦ₀ hstep n hn hT
  set M := max L 0 with hM
  have hL0 : 0 ≤ M := le_max_right _ _
  have hF' := isLipschitzField_max_zero hF
  have hH : 0 ≤ H := hh.trans hhH
  have hT0 : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg n) hh).trans hT
  have hB0 : 0 ≤ B := hB.nonneg
  set e := Real.exp (M * H) with he
  have he1 : 1 ≤ e := Real.one_le_exp (mul_nonneg hL0 hH)
  have hE1 : 1 ≤ Real.exp (M * T) := Real.one_le_exp (mul_nonneg hL0 hT0)
  set k₁ := 1 + M * H * e with hk₁
  set k₂ := M * B * (4 + e * (1 + 4 * M * H)) with hk₂
  have hk₁0 : 0 ≤ k₁ := by positivity
  have hk₂0 : 0 ≤ k₂ := by positivity
  have hD : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hδ0 := norm_nonneg (Y 0 - A t₀)
  have hCdef : inexactTuckerConst L B T H = Real.exp (M * T) * (1 + T * k₁ + T * k₂ + e) := rfl
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · have hC1 : 1 ≤ inexactTuckerConst L B T H := by
      rw [hCdef]
      have : 1 ≤ 1 + T * k₁ + T * k₂ + e := by
        have := mul_nonneg hT0 hk₁0
        have := mul_nonneg hT0 hk₂0
        linarith
      nlinarith
    rw [Nat.cast_zero, zero_mul, add_zero, zero_mul, add_zero]
    have : 0 ≤ ((d : ℝ) + 1) * (ε + h) := by positivity
    nlinarith
  · have hη0 : 0 ≤ η := (norm_nonneg _).trans (hstep 0 (by omega)).sApprox
    have h1 := defectTuckerBUG_global_error_le hF' hL0 hB hε hh hhH hA
      (ηK := fun _ => η) (ηS := fun _ => η) (fun k hk => (hstep k hk).toDefect) hΦ hΦ₀ hη0
      (fun _ _ => le_rfl) (fun _ _ => le_rfl) le_rfl n hn hT
    have hc₁ : tuckerC₁ d M H ≤ k₁ * (d + 1) := by
      unfold tuckerC₁; rw [← he, ← hk₁]; nlinarith
    have hc₂ : tuckerC₂ d M B H ≤ k₂ * (d + 1) := by
      unfold tuckerC₂; rw [← he, hk₂]
      have : 0 ≤ M * B * (4 + e * (4 * M * H) + e * d) := by positivity
      nlinarith
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hc₃ : (d * e + 1) * η * n ≤ e * ((d + 1) * (n * η)) := by
      have : 0 ≤ (e - 1) * η * n := mul_nonneg (mul_nonneg (by linarith) hη0) hn0
      nlinarith
    have hA1 : T * (tuckerC₁ d M H * ε) ≤ T * k₁ * ((d + 1) * ε) := by
      have := mul_le_mul_of_nonneg_right hc₁ hε
      nlinarith
    have hA2 : T * (tuckerC₂ d M B H * h) ≤ T * k₂ * ((d + 1) * h) := by
      have := mul_le_mul_of_nonneg_right hc₂ hh
      nlinarith
    have h2 := add4_mul_le zero_le_one (mul_nonneg hT0 hk₁0) (mul_nonneg hT0 hk₂0)
      (by linarith : (0 : ℝ) ≤ e) hδ0 (by positivity : (0 : ℝ) ≤ (d + 1) * ε)
      (by positivity : (0 : ℝ) ≤ (d + 1) * h)
      (by positivity : (0 : ℝ) ≤ (d + 1) * (n * η))
    have hin : ‖Y 0 - A t₀‖ + T * (tuckerC₁ d M H * ε + tuckerC₂ d M B H * h)
        + n * ((d * e + 1) * η)
        ≤ 1 * ‖Y 0 - A t₀‖ + T * k₁ * ((d + 1) * ε) + T * k₂ * ((d + 1) * h)
          + e * ((d + 1) * (n * η)) := by linarith [hA1, hA2, hc₃]
    have h3 := mul_le_mul_of_nonneg_left (hin.trans h2) (Real.exp_pos (M * T)).le
    calc _ ≤ _ := h1
      _ ≤ _ := h3
      _ = _ := by rw [hCdef]; ring

end Tucker

/-! ### Parallel BUG with inexact substeps -/

section Parallel

/-- The parallel BUG update is affine in the substep values: a perturbation of the K-, L- and
S-step results by `zK - yK`, `zL - yL`, `zS - yS` changes it by
`(zS - yS) + (1 - P₀) (zK - yK) + (1 - Q₀) (zL - yL)`. -/
theorem parallelBUG_sub_parallelBUG (P₀ Q₀ : E →L[ℝ] E) (yK yL yS zK zL zS : E) :
    parallelBUG P₀ Q₀ zK zL zS - parallelBUG P₀ Q₀ yK yL yS
      = (zS - yS) + (1 - P₀) (zK - yK) + (1 - Q₀) (zL - yL) := by
  simp only [parallelBUG, map_sub]
  abel

/-- The parallel BUG update is `1`-Lipschitz in each substep value (contraction coefficients
`1`, `‖1 - P₀‖ ≤ 1`, `‖1 - Q₀‖ ≤ 1`). -/
theorem norm_parallelBUG_sub_le {P₀ Q₀ : E →L[ℝ] E} (hP : IsOrthProj P₀) (hQ : IsOrthProj Q₀)
    (yK yL yS zK zL zS : E) :
    ‖parallelBUG P₀ Q₀ zK zL zS - parallelBUG P₀ Q₀ yK yL yS‖
      ≤ ‖zK - yK‖ + ‖zL - yL‖ + ‖zS - yS‖ := by
  rw [parallelBUG_sub_parallelBUG]
  calc ‖(zS - yS) + (1 - P₀) (zK - yK) + (1 - Q₀) (zL - yL)‖
      ≤ ‖zS - yS‖ + ‖(1 - P₀) (zK - yK)‖ + ‖(1 - Q₀) (zL - yL)‖ := norm_add₃_le
    _ ≤ ‖zS - yS‖ + ‖zK - yK‖ + ‖zL - yL‖ :=
        add_le_add (add_le_add le_rfl (hP.compl.norm_le _)) (hQ.compl.norm_le _)
    _ = _ := by ring

/-- **Local error of the parallel BUG integrator with inexact substeps** (OP-SB-01 for parallel
BUG, [CerutiKuschLubich2024] §4.1 with computed substep values).  If the computed K-, L- and S-step
values `K̃`, `L̃`, `S̃` are within `ηK`, `ηL`, `ηS` of the exact ones, then, with `h = t₁ - t₀`,

    ‖parallelBUG P₀ Q₀ K̃ L̃ S̃ - A t₁‖ ≤ h (7 L B h + ε) + ηK + ηL + ηS. -/
theorem parallelBUG_local_error_inexact {F : ℝ → E → E} {P₀ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ}
    {Y₀ : E} {YK YL YS : ℝ → E} (hs : IsParallelBUGStep F P₀ Q₀ t₀ t₁ Y₀ YK YL YS) {L B ε : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht : t₀ ≤ t₁)
    {A : ℝ → E} (hA : ODESolution F A t₀ t₁) (hA0 : A t₀ = Y₀)
    (hε : ∀ t ∈ Ico t₀ t₁, ‖(1 - P₀) ((1 - Q₀) (F t Y₀))‖ ≤ ε) {K L' S : E} {ηK ηL ηS : ℝ}
    (hK : ‖K - YK t₁‖ ≤ ηK) (hL' : ‖L' - YL t₁‖ ≤ ηL) (hS : ‖S - YS t₁‖ ≤ ηS) :
    ‖parallelBUG P₀ Q₀ K L' S - A t₁‖ ≤ (t₁ - t₀) * (7 * L * B * (t₁ - t₀) + ε)
      + (ηK + ηL + ηS) := by
  have h1 := hs.local_error hF hL hB ht hA hA0 hε
  have h2 := norm_parallelBUG_sub_le hs.orthP hs.orthQ (YK t₁) (YL t₁) (YS t₁) K L' S
  have h3 := norm_sub_le_norm_sub_add_norm_sub (parallelBUG P₀ Q₀ K L' S)
    (parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁)) (A t₁)
  linarith

/-- **Global error of the parallel BUG integrator with inexact substeps** (OP-SB-01).  Under the
hypotheses of `parallelBUG_global_error_sum`, if the new approximation is within `ϑ` (truncation)
of the parallel update of *computed* substep values that are within `η` of the exact ones, then

    ‖Y n - A tₙ‖ ≤ e^{L n h} (‖Y 0 - A t₀‖ + n h (7 L B h + ε) + n (ϑ + 3 η)). -/
theorem parallelBUG_global_error_inexact {F : ℝ → E → E} {L B ε : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) {t₀ h : ℝ} (hh : 0 ≤ h)
    {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {Y : ℕ → E}
    {P Q : ℕ → E →L[ℝ] E} {YK YL YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsParallelBUGStep F (P n) (Q n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
      (YK n) (YL n) (YS n))
    (hε : ∀ n < N, ∀ t ∈ Ico (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖(1 - P n) ((1 - Q n) (F t (Y n)))‖ ≤ ε)
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {K L' S : ℕ → E} {η ϑ : ℝ}
    (hK : ∀ n < N, ‖K n - YK n (t₀ + (n + 1) * h)‖ ≤ η)
    (hL' : ∀ n < N, ‖L' n - YL n (t₀ + (n + 1) * h)‖ ≤ η)
    (hS : ∀ n < N, ‖S n - YS n (t₀ + (n + 1) * h)‖ ≤ η)
    (htr : ∀ n < N, ‖Y (n + 1) - parallelBUG (P n) (Q n) (K n) (L' n) (S n)‖ ≤ ϑ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (L * (n * h)) * (‖Y 0 - A t₀‖ + n * (h * (7 * L * B * h + ε))
        + n * (ϑ + 3 * η)) := by
  have htr' : ∀ n < N, ‖Y (n + 1) - parallelBUG (P n) (Q n) (YK n (t₀ + (n + 1) * h))
      (YL n (t₀ + (n + 1) * h)) (YS n (t₀ + (n + 1) * h))‖ ≤ ϑ + 3 * η := by
    intro n hn
    have h1 := norm_parallelBUG_sub_le (hstep n hn).orthP (hstep n hn).orthQ
      (YK n (t₀ + (n + 1) * h)) (YL n (t₀ + (n + 1) * h)) (YS n (t₀ + (n + 1) * h))
      (K n) (L' n) (S n)
    have h2 := norm_sub_le_norm_sub_add_norm_sub (Y (n + 1))
      (parallelBUG (P n) (Q n) (K n) (L' n) (S n))
      (parallelBUG (P n) (Q n) (YK n (t₀ + (n + 1) * h)) (YL n (t₀ + (n + 1) * h))
        (YS n (t₀ + (n + 1) * h)))
    linarith [htr n hn, hK n hn, hL' n hn, hS n hn]
  intro n hn
  have h := parallelBUG_global_error_sum hF hL hB hh hA hstep hε hΦ hΦ₀ (ϑ := fun _ => ϑ + 3 * η)
    htr' n hn
  simp only [sum_const, card_range, nsmul_eq_mul] at h
  calc _ ≤ _ := h
    _ = _ := by ring

end Parallel


/-! ### Satisfiability of the hypotheses -/

/-- The hypotheses of a BUG step with computed substep values are satisfiable with a nonzero
field and nonzero substep errors: on `ℝ`, `F = 1`, identity projectors, exact trajectories
`t ↦ t` on `[0, 1]`, computed values `K₁ = L₁ = Ŷ₁ = 3/2` (errors `η = 1/2`). -/
example : IsInexactBUGStep (E := ℝ) (fun _ _ => 1) 0 (1 / 2) 1 1 1 1 0 1 0 (fun t => t)
    (fun t => t) (fun t => t) (3 / 2) (3 / 2) (3 / 2) where
  projP₀ := IsOrthProj.one
  projQ₀ := IsOrthProj.one
  projP₁ := IsOrthProj.one
  projQ₁ := IsOrthProj.one
  comm₁ _ := rfl
  kSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
  kStart := rfl
  kApprox := by norm_num
  kCap := rfl
  kNormal _ _ := by simp
  lSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
  lStart := rfl
  lApprox := by norm_num
  lCap := rfl
  lNormal _ _ := by simp
  sSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
  sStart := rfl
  sApprox := by norm_num

/-- **A capture defect is attained, with a non-identity projector** (non-vacuity and sharpness
of the `e^{L H} ηK` term of `IsDefectBUGStep.local_error_le`).  On `ℝ` with `F = 1` (so `L = 0`,
`B = 1`), `P₀ = Q₀ = Q₁ = 1` and a new left basis that drops everything, `P₁ = 0` (a
rank-revealing threshold that discards the only direction, or a frozen empty bond), one step
from `Y₀ = 0` over `[0, 1]` is an `IsDefectBUGStep` with the strictly positive capture defect
`ηK = 1` (and `ε = ηL = ηS = 0`); the computed approximation is `Y₁ = 0`, the exact solution
`A t = t`, and the error is exactly `1 = ηK`.  Here the bound of `local_error_le` with
`h = H = 1` equals `1 · (c₁ · 0 + c₂(0, 1, 1) · 1) + e⁰ · (1 + 0) + 0 = 1`
(`bugC₂ 0 B H = 0`), so it is attained with equality. -/
theorem capture_defect_attained :
    IsDefectBUGStep (E := ℝ) (fun _ _ => 1) 0 1 0 0 1 1 0 1 0 1 0 (fun t => t) (fun t => t)
      (fun _ => 0) 0 ∧ ODESolution (fun _ _ => (1 : ℝ)) (fun t => t) 0 1 ∧
    ‖(0 : ℝ) - 1‖ = 1 := by
  refine ⟨{
    projP₀ := IsOrthProj.one
    projQ₀ := IsOrthProj.one
    projP₁ := IsOrthProj.zero
    projQ₁ := IsOrthProj.one
    comm₁ := fun _ => by simp
    kSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
    kStart := rfl
    kNormal := fun _ _ => by simp
    kDefect := by simp
    lSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
    lStart := rfl
    lNormal := fun _ _ => by simp
    lDefect := by simp
    sSol := ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) (0 : ℝ)⟩
    sStart := by simp
    sErr := by simp }, odeSolution_id_of_eq_one (fun _ _ => rfl) _ _, by norm_num⟩

/-- `modeProd` of identity projectors is the identity. -/
lemma modeProd_one (d : ℕ) : modeProd (fun _ : Fin d => (1 : E →L[ℝ] E)) = 1 := by
  simp [modeProd]

/-- The hypotheses of a Tucker step with computed substep values are satisfiable (`d = 2`,
`F = 1` on `ℝ`, identity mode projectors, errors `η = 1/2`). -/
example : IsInexactTuckerBUGStep (E := ℝ) (fun _ _ => 1) 0 (1 / 2) (d := 2) (fun _ => 1)
    (fun _ => 1) 0 1 0 (fun _ t => t) (fun t => t) (fun _ => 3 / 2) (3 / 2) where
  projQ₀ _ := IsOrthProj.one
  projP₁ _ := IsOrthProj.one
  comm₁ _ _ _ := rfl
  kSol _ := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
  kStart _ := rfl
  kApprox _ := by norm_num
  kCap _ := rfl
  kNormal _ _ _ := by simp
  sSol := odeSolution_id_of_eq_one (fun _ _ => by simp [modeProd_one]) _ _
  sStart := by simp [modeProd_one]
  sApprox := by norm_num

end LeanDLRA.InexactSubsteps
