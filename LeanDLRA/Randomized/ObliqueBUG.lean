import LeanDLRA.Matrix.Interpolation
import LeanDLRA.Integrators.KStep
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.ProjectorSplitting
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Integrators.Exactness

/-!
# Interpolatory (DEIM/CUR) and sketched BUG: oblique capture and Lebesgue-constant bounds

Interpolatory integrators replace the orthogonal projectors of the BUG integrator by oblique
ones: DEIM/CUR row and column selection in the K-, L- and S-steps (BUC, [DektorEinkemmer2024],
eqs. (27)–(29); interpolatory projector splitting, eqs. (21)–(23); TDB-CUR,
[NaderiAkhavanBabaee2024]), or sketched inner products (sBUG/sKSL, [CarrelGrigori2026, §5]).
Robustness to small singular values was claimed for these methods without proof (OP-RS-02,
OP-HO-10). This file proves it with constants depending only on `L`, `B` and the **Lebesgue
constants** `η ≥ ‖oblique map‖`.

## Main results

* `capture_of_opNorm`: the K-step capture lemma for *arbitrary bounded* maps: if
  `YK' = R F(YK)`, `‖R‖ ≤ η`, `‖1 - P₁‖ ≤ a`, `P₁ YK(t₁) = YK(t₁)` and
  `‖(1 - P₁)(1 - R) F(YK(t₁))‖ ≤ ε`, then `‖(1 - P₁) A(t₁)‖ ≤ h (a (1 + η + η²) L B h + ε)`.
  Its instance `kstep_capture_oblique` is the OP-HO-10 statement (proved).
* `kstep_capture_obliqueProj` (**oblique capture lemma**, OP-RS-02 (a)): for an oblique projector
  `R` onto the orthogonal `Q₀` commuting with the orthogonal `P₁`, and the *orthogonal* normal
  bound `‖(1 - P₁)(1 - Q₀) F(YK(t₁))‖ ≤ ε`:
  `‖(1 - P₁) A(t₁)‖ ≤ h ((1 + η + η²) L B h + η ε)`.  Key identity
  `(1 - P₁)(1 - R) = (1 - R)(1 - P₁)(1 - Q₀)` (`one_sub_one_sub_eq`) and `‖1 - R‖ ≤ ‖R‖`.
* `galerkin_of_opNorm`, `obliqueGalerkin_step_error` (OP-HO-10 statement, proved),
  `obliqueGalerkin_step_error_of_end`: a Galerkin step `YS' = R F(YS)` with `‖R‖ ≤ η` has error
  `(e^{η L h} - 1)((1 + η) B h + θ) + θ` if `‖A(t₁) - R A(t₁)‖ ≤ θ`.
* `IsObliqueBUGStep` (interpolatory BUG / BUC step with oblique K-, L- and S-step maps of norm
  `≤ η`), `IsObliqueBUGStep.capture` (`‖A(t₁) - P^a Q^a A(t₁)‖ ≤ (η + η²) ϑ`,
  `ϑ = h((1 + η + η²) L B h + η ε)`), `IsObliqueBUGStep.local_error`,
  `IsObliqueBUGStep.local_error_le` (`≤ h (C₁(η) ε + C₂(η) h)`, constants `obC₁`, `obC₂`), and
  `oblique_global_error_le`: `‖Yₙ - A(tₙ)‖ ≤ e^{LT} δ + T e^{LT} C₁ ε + T e^{LT} C₂ h`.  This
  **resolves OP-RS-02 for interpolatory BUG/BUC** in the form asked for (`C(η)(δ + ε + h)`), and
  OP-HO-10 for oblique BUG-type integrators.
* **OP-RS-05 (resolved).**  `leftOblique_self_mul_right`, `rightOblique_self_mul_right`: for any
  basis `W = V M` (`M` invertible) of the range of an orthonormal `V`, `X ↦ X W (WᵀW)⁻¹ Wᵀ` *is*
  `X ↦ X V Vᵀ` (likewise on the left).  Hence `isBUGStep_of_orthSketch` and
  `isKSLStep_of_orthSketch`: the orthogonal-sketch integrators sBUG / sKSL of [CarrelGrigori2026],
  §5, written with non-orthonormal (e.g. randomized Gram–Schmidt) bases, satisfy `IsBUGStep` /
  `IsKSLStep` and inherit `bug_global_error_le` / `ksl_global_error_le`; `transfer_eq`: the
  Galerkin transfer through a non-orthonormal new basis realizes `U₁ U₁ᵀ Y₀`.
  `sketchedBUG_isBUGStep` is the OP-RS-05 statement in raw matrix form (proved). (The *oblique*
  sketched BUG variant is covered by `IsObliqueBUGStep`; the oblique sKSL variant is not, see
  below.)
* `buc_start_eq`: for the augmented BUC bases (`P₁ Y₀ = Y₀`, `Q₁ Y₀ = Y₀`) the oblique start
  value `PA QA Y₀` of `IsObliqueBUGStep` equals the Galerkin transfer `M̂ S(t₀) N̂ᵀ = P₁ Q₁ Y₀ = Y₀`
  of [DektorEinkemmer2024, eq. (29)], so the structure models BUC faithfully.
* Algebraic identities: `transpose_mul_residual_eq_zero` (implicit TDB-CUR is residual
  collocation, [NaderiAkhavanBabaee2024] §3.3.1), `obliqueConversion` ([YeYang2025] §3.2), and
  `norm_sq_bounds_of_sketch` (norm equivalence for sketch-orthonormal bases, [CarrelGrigori2026]
  §5.2).
* Satisfiability: a genuinely oblique `IsObliqueBUGStep` instance on `ℝ^{2×2}` (`U = V = e₁`,
  selection `S = (1, 1)ᵀ`, all four oblique maps different from the orthogonal projectors,
  nonzero field), a scalar instance on `ℝ`, and a genuinely oblique interpolatory projector on
  `ℝ^{2×1}`.

## Why this is new, and what it implies

The papers prove no robust bound for oblique integrators ([DektorEinkemmer2024] and 2510.19518 bound
the continuous interpolatory DLRA or give numerical evidence; [CarrelGrigori2026] treats sketched
*continuous* DLRA).  The proofs here show that only operator norms enter: the error constants
are polynomial in the Lebesgue constants (`η³` in the capture, `η²` in the Galerkin Lipschitz
constant), so any index-selection strategy with uniformly bounded Lebesgue constants (e.g.
strong rank-revealing QR selection, `η ≤ √(1 + 4 r (n - r))`, or Q-DEIM,
`η ≤ √(n - r + 1) · O(2^r)`; neither bound is formalized) yields a robust integrator.  Global error
propagation uses the exact flow, so the exponential is `e^{L T}` (not `e^{η L T}`).

## What remains

* **Interpolatory projector splitting** ([DektorEinkemmer2024, eqs. (21)–(23)]): its backward S-step
  `YS' = -P^a Q^a F` is not covered; the KSL local-error algebra of `ksl_local_error` uses that
  the backward step undoes the K-step on `range P₁ Q₀`, which fails for oblique maps unless the
  K-step and S-step use the *same* oblique co-range map.  Not formalized; the same applies to
  the oblique (sketched inner product) sKSL variant of [CarrelGrigori2026, §5]
* **Rank truncation.**  The bounds are for the augmented (rank `≤ 2r`) step before the SVD
  truncation of BUC; truncation with tolerance `ϑ` adds the usual `ϑ` per step (as for the
  rank-adaptive BUG), which is not repeated here.
* **TDB-CUR as step truncation** ([NaderiAkhavanBabaee2024], §§4–5): the plateau `c σ_{r+1}` of the
  implicit CUR step needs a perturbation analysis of the CUR truncation; only the algebraic
  residual-collocation identity is formalized here.
* Uniform bounds on the Lebesgue constants along the trajectory are hypotheses (the field
  `normRK`, ... of `IsObliqueBUGStep`); bounds for specific index-selection strategies are not.
* The BUC "exact representation of `F(t₀)` by `2r` collocation indices" (2411.15990, eq. (29))
  is an exactness statement; here BUC is covered through the generic oblique S-step.
-/

open Set

namespace LeanDLRA.ObliqueBUG

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Fields composed with bounded (oblique) operators -/

section Fields

variable {F : ℝ → E → E} {L B η : ℝ} {R : E →L[ℝ] E}

/-- If `‖F‖ ≤ B` and `‖R‖ ≤ η`, then `‖R F‖ ≤ η B`. -/
lemma isBoundedField_comp (hB : IsBoundedField F B) (hR : ‖R‖ ≤ η) :
    IsBoundedField (fun t x => R (F t x)) (η * B) := fun t x =>
  (R.le_opNorm _).trans (mul_le_mul hR (hB t x) (norm_nonneg _) ((norm_nonneg _).trans hR))

/-- If `F` is `L`-Lipschitz and `‖R‖ ≤ η`, then `R F` is `η L`-Lipschitz. -/
lemma isLipschitzField_comp (hF : IsLipschitzField F L) (hR : ‖R‖ ≤ η) :
    IsLipschitzField (fun t x => R (F t x)) (η * L) := fun t x y => by
  calc ‖R (F t x) - R (F t y)‖ = ‖R (F t x - F t y)‖ := by rw [map_sub]
    _ ≤ ‖R‖ * ‖F t x - F t y‖ := R.le_opNorm _
    _ ≤ η * (L * ‖x - y‖) :=
        mul_le_mul hR (hF t x y) (norm_nonneg _) ((norm_nonneg _).trans hR)
    _ = η * L * ‖x - y‖ := by ring

end Fields

/-! ## The oblique K-step capture lemma (OP-RS-02, OP-HO-10) -/

section Capture

variable {F : ℝ → E → E} {L B ε a η : ℝ} {P₁ R : E →L[ℝ] E} {t₀ t₁ h : ℝ} {A YK : ℝ → E}

/-- **Capture lemma for K-steps with bounded (oblique) maps**, the operator-norm generalisation
of `LeanDLRA.kstep_capture`.  Let `F` be `L`-Lipschitz (`L ≥ 0`) and bounded by `B`, `A` solve
`A' = F(t, A)` on `[t₀, t₁]`, `t₁ = t₀ + h`, `h ≥ 0`, and let the K-step trajectory solve
`YK' = R F(t, YK)`, `YK t₀ = A t₀`, for an arbitrary bounded operator `R` with `‖R‖ ≤ η`.  If
the new left map `P₁` (arbitrary bounded operator with `‖1 - P₁‖ ≤ a`) fixes `YK t₁` and
`‖(1 - P₁) ((1 - R) F(t, YK t₁))‖ ≤ ε` on the step, then

    ‖(1 - P₁) A(t₁)‖ ≤ h (a (1 + η + η²) L B h + ε).

Proof: `g = (1 - P₁)(A - YK)` vanishes at `t₀`, equals `(1 - P₁) A(t₁)` at `t₁`, and
`g' = (1 - P₁)[F(A) - F(YK₁)] + (1 - P₁)(1 - R) F(YK₁) + (1 - P₁) R [F(YK₁) - F(YK)]` with
`‖A(t) - YK(t₁)‖ ≤ (1 + η) B h` and `‖YK(t₁) - YK(t)‖ ≤ η B h`; mean-value inequality.  No
idempotency, commutation or orthogonality is used. -/
theorem capture_of_opNorm (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (ha : ‖1 - P₁‖ ≤ a) (hη : ‖R‖ ≤ η) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hK : ODESolution (fun t x => R (F t x)) YK t₀ t₁)
    (hK₀ : YK t₀ = A t₀) (hKcap : P₁ (YK t₁) = YK t₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - R) (F t (YK t₁)))‖ ≤ ε) :
    ‖(1 - P₁) (A t₁)‖ ≤ h * (a * (1 + η + η ^ 2) * L * B * h + ε) := by
  have hle : t₀ ≤ t₁ := by linarith
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hη
  have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
  have hBK := isBoundedField_comp hB hη
  set g : ℝ → E := fun t => (1 - P₁) (A t - YK t) with hg
  have hgc : ContinuousOn g (Icc t₀ t₁) :=
    (1 - P₁).continuous.comp_continuousOn (hA.cont.sub hK.cont)
  have hgd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt g ((1 - P₁) (F t (A t) - R (F t (YK t))))
      (Ici t) t := fun t ht =>
    (1 - P₁).hasFDerivAt.comp_hasDerivWithinAt t ((hA.deriv t ht).sub (hK.deriv t ht))
  have ht₁mem : t₁ ∈ Icc t₀ t₁ := ⟨hle, le_rfl⟩
  have hbound : ∀ t ∈ Ico t₀ t₁, ‖(1 - P₁) (F t (A t) - R (F t (YK t)))‖
      ≤ a * (1 + η + η ^ 2) * L * B * h + ε := by
    intro t ht
    have htI := Ico_subset_Icc_self ht
    have hA1 := hA.norm_sub_start_le hB ht₁ t htI
    have hK1 := hK.norm_sub_start_le hBK ht₁ t₁ ht₁mem
    have hK2 := hK.norm_end_sub_le hBK ht₁ t htI
    have hd1 : ‖A t - YK t₁‖ ≤ (1 + η) * B * h := by
      have hdec : A t - YK t₁ = (A t - A t₀) - (YK t₁ - YK t₀) := by rw [hK₀]; abel
      rw [hdec]
      refine (norm_sub_le _ _).trans ?_
      linarith
    have hsplit : (1 - P₁) (F t (A t) - R (F t (YK t))) =
        (1 - P₁) (F t (A t) - F t (YK t₁)) + (1 - P₁) ((1 - R) (F t (YK t₁)))
          + (1 - P₁) (R (F t (YK t₁) - F t (YK t))) := by
      rw [← map_add, ← map_add]
      congr 1
      simp only [sub_apply, one_apply_eq_self, map_sub]
      abel
    have hc1 : ‖(1 - P₁) (F t (A t) - F t (YK t₁))‖ ≤ a * (L * ((1 + η) * B * h)) :=
      ((1 - P₁).le_opNorm _).trans (mul_le_mul ha
        ((hF t _ _).trans (mul_le_mul_of_nonneg_left hd1 hL)) (norm_nonneg _) ha0)
    have hc3 : ‖(1 - P₁) (R (F t (YK t₁) - F t (YK t)))‖ ≤ a * (η * (L * (η * B * h))) :=
      ((1 - P₁).le_opNorm _).trans (mul_le_mul ha ((R.le_opNorm _).trans
        (mul_le_mul hη ((hF t _ _).trans (mul_le_mul_of_nonneg_left hK2 hL)) (norm_nonneg _)
          hη0)) (norm_nonneg _) ha0)
    rw [hsplit]
    have h3 := norm_add₃_le (a := (1 - P₁) (F t (A t) - F t (YK t₁)))
      (b := (1 - P₁) ((1 - R) (F t (YK t₁)))) (c := (1 - P₁) (R (F t (YK t₁) - F t (YK t))))
    have hε' := hε t htI
    have key : a * (L * ((1 + η) * B * h)) + a * (η * (L * (η * B * h)))
        = a * (1 + η + η ^ 2) * L * B * h := by ring
    linarith
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd hbound t₁ ⟨hle, le_rfl⟩
  have hg₀ : g t₀ = 0 := by simp [hg, hK₀]
  have hg₁ : g t₁ = (1 - P₁) (A t₁) := by
    simp only [hg, map_sub, hKcap, sub_apply,
      one_apply_eq_self, sub_self, sub_zero]
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [hg₀, hg₁, sub_zero, hlen] at hmvt
  rw [mul_comm h]
  exact hmvt

/-- **OP-HO-10, oblique K-step capture** (proved): if `‖1 - P₁‖ ≤ η` and the K-step map
satisfies `‖Q₀‖ ≤ η`, the capture bound holds with the `η`-dependent constant
`‖(1 - P₁) A(t₁)‖ ≤ h (η (1 + η + η²) L B h + ε)`.  The idempotency hypothesis `hP₁` is kept for
fidelity with the original statement but is not needed (`capture_of_opNorm`). -/
theorem kstep_capture_oblique {F : ℝ → E → E} {L B ε η : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) {P₁ Q₀ : E →L[ℝ] E} (_hP₁ : ∀ x, P₁ (P₁ x) = P₁ x)
    (hP₁n : ‖1 - P₁‖ ≤ η) (hQ₀n : ‖Q₀‖ ≤ η) {t₀ t₁ h : ℝ} (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    {A YK : ℝ → E} (hA : ODESolution F A t₀ t₁)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = A t₀)
    (hKcap : P₁ (YK t₁) = YK t₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε) :
    ‖(1 - P₁) (A t₁)‖ ≤ h * (η * (1 + η + η ^ 2) * L * B * h + ε) :=
  capture_of_opNorm hF hL hB hP₁n hQ₀n ht₁ hh hA hK hK₀ hKcap hε

/-- `‖1 - P‖ ≤ 1` for an orthogonal projector. -/
lemma opNorm_one_sub_le_one {P : E →L[ℝ] E} (hP : IsOrthProj P) : ‖1 - P‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]; exact hP.compl.norm_le x

/-- The doubly-normal identity behind the oblique capture lemma:
`(1 - P₁)(1 - R) x = (1 - R)(1 - P₁)(1 - Q₀) x` if `R` is an oblique projector onto the
orthogonal projector `Q₀` (`(1 - R) = (1 - R)(1 - Q₀)`, [CarrelEtAl2025] eq. (14)) and `R`
commutes with `P₁`. -/
lemma one_sub_one_sub_eq {Q₀ : E →L[ℝ] E} (hR : IsObliqueProj R Q₀)
    (hc : ∀ x, P₁ (R x) = R (P₁ x)) (x : E) :
    (1 - P₁) ((1 - R) x) = (1 - R) ((1 - P₁) ((1 - Q₀) x)) := by
  have h1 : (1 - R) x = (1 - R) ((1 - Q₀) x) := by
    simp only [sub_apply, one_apply_eq_self]
    exact hR.sub_apply_eq x
  rw [h1]
  simp only [sub_apply, one_apply_eq_self, map_sub, hc]
  abel

/-- **Oblique (interpolatory / DEIM) K-step capture lemma** (OP-RS-02, part (a); the K-step of
the interpolatory BUG / BUC integrators of [DektorEinkemmer2024, eqs. (21)–(23)], (27)–(29)). Let
the K-step use an oblique projector `R` onto the orthogonal projector `Q₀ ≠ 0` (`R Q₀ = Q₀`,
`Q₀ R = R`; for matrices `X ↦ X S (V₀ᵀ S)⁻¹ V₀ᵀ`), commuting with the orthogonal projector `P₁` of
the new basis, with Lebesgue constant `‖R‖ ≤ η`. If `P₁` captures `YK(t₁)` and the **orthogonal**
doubly-normal component is small, `‖(1 - P₁)(1 - Q₀) F(t, YK(t₁))‖ ≤ ε`, then

    ‖(1 - P₁) A(t₁)‖ ≤ h ((1 + η + η²) L B h + η ε).

The constant depends only on `L`, `B` and the Lebesgue constant `η`, not on singular values.
For `R = Q₀` (`η = 1`) this is `kstep_capture` with `3 L B h` in place of `4 L B h`. -/
theorem kstep_capture_obliqueProj (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) {Q₀ : E →L[ℝ] E} (hR : IsObliqueProj R Q₀) (hQ₀ : Q₀ ≠ 0)
    (hP₁ : IsOrthProj P₁) (hc : ∀ x, P₁ (R x) = R (P₁ x)) (hη : ‖R‖ ≤ η) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hK : ODESolution (fun t x => R (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = A t₀)
    (hKcap : P₁ (YK t₁) = YK t₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε) :
    ‖(1 - P₁) (A t₁)‖ ≤ h * ((1 + η + η ^ 2) * L * B * h + η * ε) := by
  have hle : t₀ ≤ t₁ := by linarith
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε t₀ ⟨le_rfl, hle⟩)
  have h1R : ‖1 - R‖ ≤ η := (hR.opNorm_one_sub_le hQ₀).trans hη
  have hε' : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - R) (F t (YK t₁)))‖ ≤ η * ε := fun t ht => by
    rw [one_sub_one_sub_eq hR hc]
    exact ((1 - R).le_opNorm _).trans
      (mul_le_mul h1R (hε t ht) (norm_nonneg _) ((norm_nonneg _).trans h1R))
  exact (capture_of_opNorm hF hL hB (opNorm_one_sub_le_one hP₁) hη ht₁ hh hA hK hK₀ hKcap
    hε').trans_eq (by ring)

end Capture

/-! ## The oblique Galerkin (S-) step -/

section Galerkin

variable {F : ℝ → E → E} {L B η ρ θ : ℝ} {R : E →L[ℝ] E} {t₀ t₁ h : ℝ} {A YS : ℝ → E}

/-- **Galerkin step with a bounded map** (the core of `obliqueGalerkin_step_error`; Petrov–Galerkin
/ DEIM / CUR S-steps): for a bounded operator `R` with `‖R‖ ≤ η`, the step `YS' = R F(t, YS)`,
`YS(t₀) = R A(t₀)`, satisfies `‖YS(t₁) - A(t₁)‖ ≤ (e^{η L h} - 1) ρ + θ`, where `ρ` bounds `‖A - R
A‖` on the step and `θ` at the endpoint. Proof: Grönwall for `YS - R A`, whose defect is `‖R F(A) -
R F(R A)‖ ≤ η L ρ`. No idempotency is needed; see `obliqueGalerkin_step_error` for the idempotent
form. -/
theorem galerkin_of_opNorm (hRn : ‖R‖ ≤ η)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hS : ODESolution (fun t x => R (F t x)) YS t₀ t₁)
    (hS₀ : YS t₀ = R (A t₀)) (hρ : ∀ t ∈ Icc t₀ t₁, ‖A t - R (A t)‖ ≤ ρ)
    (hθ : ‖A t₁ - R (A t₁)‖ ≤ θ) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (η * L * h) - 1) * ρ + θ := by
  have hle : t₀ ≤ t₁ := by linarith
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hRn
  have hfL := isLipschitzField_comp hF hRn
  have hZc : ContinuousOn (fun t => R (A t)) (Icc t₀ t₁) :=
    R.continuous.comp_continuousOn hA.cont
  have hZd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => R (A t)) (R (F t (A t))) (Ici t) t :=
    fun t ht => R.hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht)
  have hdef : ∀ t ∈ Ico t₀ t₁, ‖R (F t (A t)) - R (F t (R (A t)))‖ ≤ η * L * ρ := fun t ht =>
    (hfL t _ _).trans
      (mul_le_mul_of_nonneg_left (hρ t (Ico_subset_Icc_self ht)) (mul_nonneg hη0 hL))
  have hgr := norm_sub_le_gronwallBound hfL (mul_nonneg hη0 hL) (y := YS)
    (z := fun t => R (A t)) (u := fun t => R (F t (YS t))) (w := fun t => R (F t (A t)))
    (ηy := 0) (ηz := η * L * ρ) (δ := 0) hS.cont hS.deriv (fun _ _ => by simp) hZc hZd hdef
    (by simp [hS₀]) t₁ ⟨hle, le_rfl⟩
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [zero_add, hlen, gronwallBound_zero_mul] at hgr
  calc ‖YS t₁ - A t₁‖ ≤ ‖YS t₁ - R (A t₁)‖ + ‖R (A t₁) - A t₁‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
        rw [norm_sub_rev (R (A t₁))]
        exact add_le_add hgr hθ

/-- **OP-HO-10, oblique Galerkin step** (proved): for an idempotent `R` with
`‖R‖ ≤ η`, `‖YS(t₁) - A(t₁)‖ ≤ (e^{η L h} - 1) ρ + θ`.  Idempotency is not used
(`galerkin_of_opNorm`). -/
theorem obliqueGalerkin_step_error (_hR : ∀ x, R (R x) = R x) (hRn : ‖R‖ ≤ η)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hS : ODESolution (fun t x => R (F t x)) YS t₀ t₁)
    (hS₀ : YS t₀ = R (A t₀)) (hρ : ∀ t ∈ Icc t₀ t₁, ‖A t - R (A t)‖ ≤ ρ)
    (hθ : ‖A t₁ - R (A t₁)‖ ≤ θ) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (η * L * h) - 1) * ρ + θ :=
  galerkin_of_opNorm hRn hF hL ht₁ hh hA hS hS₀ hρ hθ

/-- Interior projection error from the endpoint one: if `‖R‖ ≤ η` and
`‖A(t₁) - R A(t₁)‖ ≤ θ`, then `‖A(t) - R A(t)‖ ≤ (1 + η) B h + θ` on the step. -/
lemma norm_sub_apply_le_of_end (hRn : ‖R‖ ≤ η) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hA : ODESolution F A t₀ t₁) (hθ : ‖A t₁ - R (A t₁)‖ ≤ θ) :
    ∀ t ∈ Icc t₀ t₁, ‖A t - R (A t)‖ ≤ (1 + η) * B * h + θ := by
  intro t ht
  have h1 : ‖A t - A t₁‖ ≤ B * h := by
    rw [norm_sub_rev]; exact hA.norm_end_sub_le hB ht₁ t ht
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hRn
  have hdec : A t - R (A t) = ((A t - A t₁) - R (A t - A t₁)) + (A t₁ - R (A t₁)) := by
    rw [map_sub]; abel
  have h2 : ‖R (A t - A t₁)‖ ≤ η * (B * h) :=
    (R.le_opNorm _).trans (mul_le_mul hRn h1 (norm_nonneg _) hη0)
  rw [hdec]
  calc _ ≤ ‖(A t - A t₁) - R (A t - A t₁)‖ + ‖A t₁ - R (A t₁)‖ := norm_add_le _ _
    _ ≤ (‖A t - A t₁‖ + ‖R (A t - A t₁)‖) + θ := add_le_add (norm_sub_le _ _) hθ
    _ ≤ (1 + η) * B * h + θ := by nlinarith

/-- **Oblique Galerkin step, endpoint form**: for `‖R‖ ≤ η`, `F` bounded by `B`, and
`‖A(t₁) - R A(t₁)‖ ≤ θ`, the step `YS' = R F(t, YS)`, `YS(t₀) = R A(t₀)` satisfies
`‖YS(t₁) - A(t₁)‖ ≤ (e^{η L h} - 1)((1 + η) B h + θ) + θ` (for `η = 1`, `R` orthogonal, this is
`galerkin_step_error` up to `2 B h` in place of `B h`). -/
theorem obliqueGalerkin_step_error_of_end (hRn : ‖R‖ ≤ η) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hS : ODESolution (fun t x => R (F t x)) YS t₀ t₁)
    (hS₀ : YS t₀ = R (A t₀)) (hθ : ‖A t₁ - R (A t₁)‖ ≤ θ) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (η * L * h) - 1) * ((1 + η) * B * h + θ) + θ :=
  galerkin_of_opNorm hRn hF hL ht₁ hh hA hS hS₀
    (norm_sub_apply_le_of_end hRn hB ht₁ hA hθ) hθ

end Galerkin

/-! ## The interpolatory BUG / BUC step: local and global error (OP-RS-02) -/

section Step

/-- All hypotheses of one step of the **interpolatory (DEIM / CUR) BUG integrator** with
Lebesgue constant `η` ([DektorEinkemmer2024, eqs. (27)–(29)] for BUC; [CarrelEtAl2025] for the
interpolatory tangent projector).  As in `LeanDLRA.IsBUGStep`, the step is written through
full-space trajectories:

* K-step `YK' = RK F(t, YK)`, `YK(t₀) = Y₀`, with an oblique projector `RK` onto the orthogonal
  co-range projector `Q₀ ≠ 0` (`X ↦ X S (V₀ᵀ S)⁻¹ V₀ᵀ`), commuting with the orthogonal projector
  `P₁` of the new left basis, which captures `YK(t₁)`;
* L-step `YL' = RL F(t, YL)`, symmetric, with `RL` oblique onto `P₀ ≠ 0`, commuting with `Q₁`;
* S-step (collocation) `YS' = PA QA F(t, YS)`, `YS(t₀) = PA QA Y₀`, with oblique projectors `PA`,
  `QA` onto the new orthogonal projectors `P₁ ≠ 0`, `Q₁ ≠ 0` (the two-sided interpolatory
  projector `X ↦ 𝒫_U X 𝒫_Vᵀ`);
* all four oblique maps have operator norm `≤ η` (Lebesgue constants), and the orthogonal
  doubly-normal components at `YK(t₁)`, `YL(t₁)` are `≤ ε`. -/
structure IsObliqueBUGStep (F : ℝ → E → E) (ε η : ℝ) (P₀ Q₀ P₁ Q₁ RK RL PA QA : E →L[ℝ] E)
    (t₀ t₁ : ℝ) (Y₀ : E) (YK YL YS : ℝ → E) : Prop where
  obliqueK : IsObliqueProj RK Q₀
  obliqueL : IsObliqueProj RL P₀
  ne_Q₀ : Q₀ ≠ 0
  ne_P₀ : P₀ ≠ 0
  projP₁ : IsOrthProj P₁
  projQ₁ : IsOrthProj Q₁
  /-- The K-step map acts on the right, the new left projector on the left. -/
  commK : ∀ x, P₁ (RK x) = RK (P₁ x)
  /-- The L-step map acts on the left, the new right projector on the right. -/
  commL : ∀ x, Q₁ (RL x) = RL (Q₁ x)
  obliqueA : IsObliqueProj PA P₁
  obliqueB : IsObliqueProj QA Q₁
  ne_P₁ : P₁ ≠ 0
  ne_Q₁ : Q₁ ≠ 0
  normRK : ‖RK‖ ≤ η
  normRL : ‖RL‖ ≤ η
  normPA : ‖PA‖ ≤ η
  normQA : ‖QA‖ ≤ η
  kSol : ODESolution (fun t x => RK (F t x)) YK t₀ t₁
  kStart : YK t₀ = Y₀
  kCap : P₁ (YK t₁) = YK t₁
  kNormal : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε
  lSol : ODESolution (fun t x => RL (F t x)) YL t₀ t₁
  lStart : YL t₀ = Y₀
  lCap : Q₁ (YL t₁) = YL t₁
  lNormal : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε
  sSol : ODESolution (fun t x => PA (QA (F t x))) YS t₀ t₁
  sStart : YS t₀ = PA (QA Y₀)

/-- **The BUC start value** ([DektorEinkemmer2024, eq. (29)]): BUC starts its S-step at the
Galerkin transfer `M̂ S(t₀) N̂ᵀ`, i.e. at `P₁ Q₁ Y₀`, and augments the new bases by `X(t₀)`,
`V(t₀)`, so `P₁ Y₀ = Y₀` and `Q₁ Y₀ = Y₀`.  Then the oblique start `PA QA Y₀` of
`IsObliqueBUGStep.sStart` coincides with it: `PA QA Y₀ = P₁ Q₁ Y₀ = Y₀`.  (Without augmentation
the two start values differ in general; `IsObliqueBUGStep` then models the variant with an
oblique initial transfer.) -/
lemma buc_start_eq {P₁ Q₁ PA QA : E →L[ℝ] E} (hA : IsObliqueProj PA P₁)
    (hB : IsObliqueProj QA Q₁) {Y₀ : E} (hP : P₁ Y₀ = Y₀) (hQ : Q₁ Y₀ = Y₀) :
    PA (QA Y₀) = Y₀ ∧ P₁ (Q₁ Y₀) = Y₀ := by
  have hQA : QA Y₀ = Y₀ := by rw [← hQ, hB.fix, hQ]
  have hPA : PA Y₀ = Y₀ := by rw [← hP, hA.fix, hP]
  exact ⟨by rw [hQA, hPA], by rw [hQ, hP]⟩

/-- Local-error constant of the interpolatory BUG step in front of `ε`:
`C₁ = (1 + η² L H e^{η² L H}) (η + η²) η`. -/
noncomputable def obC₁ (η L H : ℝ) : ℝ :=
  (1 + η ^ 2 * L * H * Real.exp (η ^ 2 * L * H)) * (η + η ^ 2) * η

/-- Local-error constant of the interpolatory BUG step in front of `h`:
`C₂ = η² L e^{η² L H} (1 + η²) B + (1 + η² L H e^{η² L H}) (η + η²)(1 + η + η²) L B`. -/
noncomputable def obC₂ (η L B H : ℝ) : ℝ :=
  η ^ 2 * L * Real.exp (η ^ 2 * L * H) * (1 + η ^ 2) * B
    + (1 + η ^ 2 * L * H * Real.exp (η ^ 2 * L * H)) * (η + η ^ 2) * (1 + η + η ^ 2) * L * B

lemma obC₁_nonneg {η L H : ℝ} (hη : 0 ≤ η) (hL : 0 ≤ L) (hH : 0 ≤ H) : 0 ≤ obC₁ η L H := by
  unfold obC₁; positivity

lemma obC₂_nonneg {η L B H : ℝ} (hη : 0 ≤ η) (hL : 0 ≤ L) (hB : 0 ≤ B) (hH : 0 ≤ H) :
    0 ≤ obC₂ η L B H := by
  unfold obC₂; positivity

/-- The explicit local bound `(e^{η² L h} - 1)((1 + η²) B h + θ) + θ`,
`θ = (η + η²) h ((1 + η + η²) L B h + η ε)`, is `≤ h (C₁ ε + C₂ h)` for `0 ≤ h ≤ H`. -/
lemma ob_bound_le {η L B ε h H : ℝ} (hη : 0 ≤ η) (hL : 0 ≤ L) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) :
    (Real.exp (η ^ 2 * L * h) - 1) * ((1 + η ^ 2) * B * h
        + (η + η ^ 2) * (h * ((1 + η + η ^ 2) * L * B * h + η * ε)))
      + (η + η ^ 2) * (h * ((1 + η + η ^ 2) * L * B * h + η * ε))
      ≤ h * (obC₁ η L H * ε + obC₂ η L B H * h) := by
  set e := Real.exp (η ^ 2 * L * H) with he
  set θ := (η + η ^ 2) * (h * ((1 + η + η ^ 2) * L * B * h + η * ε)) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hq : 0 ≤ η ^ 2 * L := by positivity
  have hexp : Real.exp (η ^ 2 * L * h) ≤ e :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hq)
  have h1 : Real.exp (η ^ 2 * L * h) - 1 ≤ η ^ 2 * L * h * e :=
    (exp_sub_one_le_mul_exp _).trans (mul_le_mul_of_nonneg_left hexp (mul_nonneg hq hh))
  have hX : 0 ≤ (1 + η ^ 2) * B * h + θ := by positivity
  have h2 := mul_le_mul_of_nonneg_right h1 hX
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hgap : (η ^ 2 * L * h * e + 1) * θ ≤ (η ^ 2 * L * H * e + 1) * θ := by
    have : η ^ 2 * L * h * e ≤ η ^ 2 * L * H * e :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhH hq) he0
    exact mul_le_mul_of_nonneg_right (by linarith) hθ0
  have hid : h * (obC₁ η L H * ε + obC₂ η L B H * h)
      = η ^ 2 * L * e * (1 + η ^ 2) * B * h ^ 2 + (η ^ 2 * L * H * e + 1) * θ := by
    unfold obC₁ obC₂; rw [← he, hθ]; ring
  have hid2 : η ^ 2 * L * h * e * ((1 + η ^ 2) * B * h + θ) + θ
      = η ^ 2 * L * e * (1 + η ^ 2) * B * h ^ 2 + (η ^ 2 * L * h * e + 1) * θ := by ring
  rw [hid]
  linarith

namespace IsObliqueBUGStep

variable {F : ℝ → E → E} {L B ε η : ℝ} {P₀ Q₀ P₁ Q₁ RK RL PA QA : E →L[ℝ] E} {t₀ t₁ h : ℝ}
  {Y₀ : E} {YK YL YS A : ℝ → E}

/-- The normal-component bound forces `ε ≥ 0` on a nonempty step. -/
lemma eps_nonneg (hs : IsObliqueBUGStep F ε η P₀ Q₀ P₁ Q₁ RK RL PA QA t₀ t₁ Y₀ YK YL YS)
    (h01 : t₀ ≤ t₁) : 0 ≤ ε :=
  (norm_nonneg _).trans (hs.kNormal t₀ ⟨le_rfl, h01⟩)

/-- The Lebesgue constant is nonnegative (in fact `≥ 1`). -/
lemma eta_nonneg (hs : IsObliqueBUGStep F ε η P₀ Q₀ P₁ Q₁ RK RL PA QA t₀ t₁ Y₀ YK YL YS) :
    0 ≤ η :=
  (norm_nonneg _).trans hs.normPA

/-- **Capture by the two-sided interpolatory projector** (oblique analogue of Lemma 3 of
[CerutiLubich2022]): with `ϑ = h ((1 + η + η²) L B h + η ε)`,
`‖A(t₁) - PA QA A(t₁)‖ ≤ (η + η²) ϑ`. -/
theorem capture (hs : IsObliqueBUGStep F ε η P₀ Q₀ P₁ Q₁ RK RL PA QA t₀ t₁ Y₀ YK YL YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖A t₁ - PA (QA (A t₁))‖ ≤
      (η + η ^ 2) * (h * ((1 + η + η ^ 2) * L * B * h + η * ε)) := by
  have hη := hs.eta_nonneg
  have h1 := kstep_capture_obliqueProj hF hL hB hs.obliqueK hs.ne_Q₀ hs.projP₁ hs.commK
    hs.normRK ht₁ hh hA hs.kSol (hs.kStart.trans hA₀.symm) hs.kCap hs.kNormal
  have h2 := kstep_capture_obliqueProj hF hL hB hs.obliqueL hs.ne_P₀ hs.projQ₁ hs.commL
    hs.normRL ht₁ hh hA hs.lSol (hs.lStart.trans hA₀.symm) hs.lCap hs.lNormal
  have h3 := hs.obliqueA.norm_sub_mul_le hs.obliqueB hs.ne_P₁ hs.ne_Q₁ (A t₁)
  set ϑ := h * ((1 + η + η ^ 2) * L * B * h + η * ε)
  have h1' : ‖A t₁ - P₁ (A t₁)‖ ≤ ϑ := h1
  have h2' : ‖A t₁ - Q₁ (A t₁)‖ ≤ ϑ := h2
  have hPA := hs.normPA
  have hQA := hs.normQA
  have e1 : ‖PA‖ * ‖A t₁ - P₁ (A t₁)‖ ≤ η * ϑ :=
    mul_le_mul hPA h1' (norm_nonneg _) hη
  have e2 : ‖PA‖ * ‖QA‖ * ‖A t₁ - Q₁ (A t₁)‖ ≤ η * η * ϑ :=
    mul_le_mul (mul_le_mul hPA hQA (norm_nonneg _) hη) h2' (norm_nonneg _) (mul_nonneg hη hη)
  nlinarith

/-- **Robust local error of the interpolatory BUG / BUC integrator** (OP-RS-02, explicit form).
Under `IsObliqueBUGStep` with Lebesgue constant `η`, `F` `L`-Lipschitz and bounded by `B`, and
`A(t₀) = Y₀`:

    ‖Y₁ - A(t₁)‖ ≤ (e^{η² L h} - 1)((1 + η²) B h + θ) + θ,
    θ = (η + η²) h ((1 + η + η²) L B h + η ε),

i.e. `O(h (h + ε))` with constants depending only on `L`, `B`, `η` — not on singular values. -/
theorem local_error (hs : IsObliqueBUGStep F ε η P₀ Q₀ P₁ Q₁ RK RL PA QA t₀ t₁ Y₀ YK YL YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (η ^ 2 * L * h) - 1) * ((1 + η ^ 2) * B * h
        + (η + η ^ 2) * (h * ((1 + η + η ^ 2) * L * B * h + η * ε)))
      + (η + η ^ 2) * (h * ((1 + η + η ^ 2) * L * B * h + η * ε)) := by
  have hη := hs.eta_nonneg
  have hS : ‖PA * QA‖ ≤ η ^ 2 :=
    (norm_mul_le _ _).trans (by rw [sq]; exact mul_le_mul hs.normPA hs.normQA (norm_nonneg _) hη)
  exact obliqueGalerkin_step_error_of_end (R := PA * QA) hS hF hL hB ht₁ hh hA hs.sSol
    (by rw [hs.sStart, hA₀]; rfl) (hs.capture hF hL hB ht₁ hh hA hA₀)

/-- **Robust local error of the interpolatory BUG / BUC integrator, `O`-form**: for
`0 ≤ h ≤ H`, `‖Y₁ - A(t₁)‖ ≤ h (C₁ ε + C₂ h)` with `C₁ = obC₁ η L H`, `C₂ = obC₂ η L B H`. -/
theorem local_error_le (hs : IsObliqueBUGStep F ε η P₀ Q₀ P₁ Q₁ RK RL PA QA t₀ t₁ Y₀ YK YL YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤ h * (obC₁ η L H * ε + obC₂ η L B H * h) :=
  (hs.local_error hF hL hB ht₁ hh hA hA₀).trans
    (ob_bound_le hs.eta_nonneg hL hB.nonneg (hs.eps_nonneg (by linarith)) hh hhH)

end IsObliqueBUGStep

/-- **Robust global error of the interpolatory BUG / BUC integrator** (OP-RS-02, target
statement `C(η)(δ + ε + h)`).  For a sequence of `IsObliqueBUGStep`s on the grid
`tₙ = t₀ + n h`, `0 ≤ h ≤ H`, with uniform Lebesgue constant `η`, exact flows `Φ n` from the
numerical values, `‖Y 0 - A t₀‖ ≤ δ`, `ε ≥ 0` and `n h ≤ T`:

    ‖Yₙ - A(tₙ)‖ ≤ e^{L T} δ + T e^{L T} C₁ ε + T e^{L T} C₂ h,

with `C₁ = obC₁ η L H`, `C₂ = obC₂ η L B H`.  The error propagation uses the exact flow
(Lady Windermere's fan), so the exponent is `L T`; `η` enters only through the local constants. -/
theorem oblique_global_error_le {F : ℝ → E → E} {L B ε η : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (hε : 0 ≤ ε) (hη : 0 ≤ η) {t₀ h H : ℝ} (hh : 0 ≤ h)
    (hhH : h ≤ H) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h))
    {P Q RK RL PA QA : ℕ → E →L[ℝ] E} {Y : ℕ → E} {YK YL YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsObliqueBUGStep F ε η (P n) (Q n) (P (n + 1)) (Q (n + 1)) (RK n) (RL n)
      (PA n) (QA n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n))
    (hY : ∀ n < N, Y (n + 1) = YS n (t₀ + (n + 1) * h))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * obC₁ η L H * ε + T * Real.exp (L * T) * obC₂ η L B H * h := by
  intro n hn hT
  have hH : 0 ≤ H := hh.trans hhH
  have hg : 0 ≤ obC₁ η L H * ε + obC₂ η L B H * h :=
    add_nonneg (mul_nonneg (obC₁_nonneg hη hL hH) hε)
      (mul_nonneg (obC₂_nonneg hη hL hB.nonneg hH) hh)
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤
      h * (obC₁ η L H * ε + obC₂ η L B H * h) := by
    intro n hn
    rw [hY n hn]
    exact (hstep n hn).local_error_le hF hL hB (by ring) hh hhH (hΦ n hn) (hΦ₀ n hn)
  have h1 := lady_windermere_of_le hF hL hh hA hΦ hΦ₀ hg hloc n hn hT
  have h2 : Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * (obC₁ η L H * ε + obC₂ η L B H * h))
      ≤ Real.exp (L * T) * (δ + T * (obC₁ η L H * ε + obC₂ η L B H * h)) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  calc _ ≤ _ := h1.trans h2
    _ = _ := by ring

end Step

/-! ## Orthogonal sketched integrators coincide with BUG / KSL (OP-RS-05) -/

section Sketch

open Matrix
open scoped LeanDLRA.Frobenius

variable {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq k] [Fintype l]
  [DecidableEq l]

/-- **OP-RS-05 (i), left factor.**  For any basis `P = U M` (`M` invertible) of the range of an
orthonormal `U`, the left map `X ↦ P (PᵀP)⁻¹ Pᵀ X` built from the non-orthonormal basis is the
orthogonal projector `X ↦ U Uᵀ X`. -/
theorem leftOblique_self_mul_right {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) {M : Matrix k k ℝ}
    (hM : IsUnit M.det) :
    (leftOblique (U * M) (U * M) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) = leftProj U :=
  ContinuousLinearMap.ext fun X => by
    rw [leftOblique_apply, leftProj_apply, obliqueProj_self_mul_right hU hM]

/-- **OP-RS-05 (i), right factor.**  For a sketched co-range basis `W = V M` (`M` invertible) of
the range of an orthonormal `V`, `X ↦ X W (WᵀW)⁻¹ Wᵀ` is the orthogonal projector
`X ↦ X V Vᵀ`. -/
theorem rightOblique_self_mul_right {V : Matrix n k ℝ} (hV : Vᵀ * V = 1) {M : Matrix k k ℝ}
    (hM : IsUnit M.det) :
    (rightOblique (V * M) (V * M) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) = rightProj V :=
  ContinuousLinearMap.ext fun X => by
    rw [rightOblique_apply, rightProj_apply', obliqueProj_self_mul_right hV hM,
      Matrix.transpose_mul, Matrix.transpose_transpose]

/-- **OP-RS-05: the orthogonal-sketch BUG step (sBUG, [CarrelGrigori2026, §5]) is a BUG step.**
Write the sBUG substeps in full-space form with non-orthonormal bases: the K-step with the
sketched co-range basis `W = V₀ M_W`, `YK' = F(t, YK) W (WᵀW)⁻¹ Wᵀ`; the new left basis `P = U₁ M_P`
(e.g. from randomized Gram–Schmidt) spanning `K(t₁)`, `P (PᵀP)⁻¹ Pᵀ YK(t₁) = YK(t₁)`; the L-step
symmetric; and the Galerkin S-step with the transfer `(PᵀP)⁻¹ Pᵀ (·) Q (QᵀQ)⁻¹`, i.e.
`YS' = 𝒫_P F(t, YS) 𝒫_Qᵀ`, `YS(t₀) = 𝒫_P Y₀ 𝒫_Qᵀ`.  Then the step satisfies `IsBUGStep` with the
orthogonal projectors of `U₀, V₀, U₁, V₁`; hence it **inherits** `IsBUGStep.local_error_le`
and `bug_global_error_le` (robust bounds independent of singular values and of the sketch). -/
theorem isBUGStep_of_orthSketch {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {ε t₀ t₁ : ℝ}
    {Y₀ : Matrix m n ℝ} {U₀ : Matrix m k ℝ} {V₀ : Matrix n k ℝ} {U₁ : Matrix m l ℝ}
    {V₁ : Matrix n l ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hU₁ : U₁ᵀ * U₁ = 1)
    (hV₁ : V₁ᵀ * V₁ = 1) {MW MZ : Matrix k k ℝ} (hMW : IsUnit MW.det) (hMZ : IsUnit MZ.det)
    {MP MQ : Matrix l l ℝ} (hMP : IsUnit MP.det) (hMQ : IsUnit MQ.det)
    {YK YL YS : ℝ → Matrix m n ℝ}
    (hK : ODESolution (fun t X => rightOblique (V₀ * MW) (V₀ * MW) (F t X)) YK t₀ t₁)
    (hK₀ : YK t₀ = Y₀) (hKcap : leftOblique (U₁ * MP) (U₁ * MP) (YK t₁) = YK t₁)
    (hεK : ∀ t ∈ Icc t₀ t₁, ‖(1 - leftProj U₁) ((1 - rightProj V₀) (F t (YK t₁)))‖ ≤ ε)
    (hL : ODESolution (fun t X => leftOblique (U₀ * MZ) (U₀ * MZ) (F t X)) YL t₀ t₁)
    (hL₀ : YL t₀ = Y₀) (hLcap : rightOblique (V₁ * MQ) (V₁ * MQ) (YL t₁) = YL t₁)
    (hεL : ∀ t ∈ Icc t₀ t₁, ‖(1 - rightProj V₁) ((1 - leftProj U₀) (F t (YL t₁)))‖ ≤ ε)
    (hS : ODESolution (fun t X => leftOblique (U₁ * MP) (U₁ * MP)
      (rightOblique (V₁ * MQ) (V₁ * MQ) (F t X))) YS t₀ t₁)
    (hS₀ : YS t₀ = leftOblique (U₁ * MP) (U₁ * MP) (rightOblique (V₁ * MQ) (V₁ * MQ) Y₀)) :
    IsBUGStep F ε (leftProj U₀) (rightProj V₀) (leftProj U₁) (rightProj V₁) t₀ t₁ Y₀ YK YL
      YS := by
  rw [rightOblique_self_mul_right hV₀ hMW] at hK
  rw [leftOblique_self_mul_right hU₀ hMZ] at hL
  rw [leftOblique_self_mul_right hU₁ hMP] at hKcap hS hS₀
  rw [rightOblique_self_mul_right hV₁ hMQ] at hLcap hS hS₀
  exact ⟨isOrthProj_leftProj hU₀, isOrthProj_rightProj hV₀, isOrthProj_leftProj hU₁,
    isOrthProj_rightProj hV₁, fun X => leftProj_rightProj_comm U₁ V₁ X, hK, hK₀, hKcap, hεK, hL,
    hL₀, hLcap, hεL, hS, hS₀⟩

/-- **OP-RS-05: the orthogonal-sketch projector-splitting step (sKSL, [CarrelGrigori2026, §5]) is a
KSL step.**  With the sketched co-range basis `W = V₀ M_W` and the new non-orthonormal left
basis `P = U₁ M_P`, the K-step `YK' = F(YK) 𝒫_Wᵀ`, the backward S-step
`YS' = -𝒫_P F(YS) 𝒫_Wᵀ`, `YS(t₀) = YK(t₁)`, and the L-step `YL' = 𝒫_P F(YL)`,
`YL(t₀) = YS(t₁)` satisfy `IsKSLStep` with the orthogonal projectors of `U₁`, `V₀`; hence the
sKSL integrator inherits `IsKSLStep.local_error` and `ksl_global_error_le`. -/
theorem isKSLStep_of_orthSketch {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {ε t₀ t₁ : ℝ}
    {Y₀ : Matrix m n ℝ} {V₀ : Matrix n k ℝ} {U₁ : Matrix m k ℝ} (hV₀ : V₀ᵀ * V₀ = 1)
    (hU₁ : U₁ᵀ * U₁ = 1) {MW MP : Matrix k k ℝ} (hMW : IsUnit MW.det) (hMP : IsUnit MP.det)
    {YK YS YL : ℝ → Matrix m n ℝ}
    (hK : ODESolution (fun t X => rightOblique (V₀ * MW) (V₀ * MW) (F t X)) YK t₀ t₁)
    (hK₀ : YK t₀ = Y₀) (hKcap : leftOblique (U₁ * MP) (U₁ * MP) (YK t₁) = YK t₁)
    (hεK : ∀ t ∈ Icc t₀ t₁, ‖(1 - leftProj U₁) ((1 - rightProj V₀) (F t (YK t₁)))‖ ≤ ε)
    (hS : ODESolution (fun t X => -leftOblique (U₁ * MP) (U₁ * MP)
      (rightOblique (V₀ * MW) (V₀ * MW) (F t X))) YS t₀ t₁) (hS₀ : YS t₀ = YK t₁)
    (hL : ODESolution (fun t X => leftOblique (U₁ * MP) (U₁ * MP) (F t X)) YL t₀ t₁)
    (hL₀ : YL t₀ = YS t₁) :
    IsKSLStep F ε (leftProj U₁) (rightProj V₀) t₀ t₁ Y₀ YK YS YL := by
  rw [rightOblique_self_mul_right hV₀ hMW] at hK hS
  rw [leftOblique_self_mul_right hU₁ hMP] at hKcap hS hL
  exact ⟨isOrthProj_leftProj hU₁, isOrthProj_rightProj hV₀, hK, hK₀, hKcap, hεK, hS, hS₀, hL,
    hL₀⟩

omit [Fintype n] in
/-- **OP-RS-05 (iii), transfer matrix.**  For the new basis `P = U₁ M` (`M` invertible), the
Galerkin transfer `P (PᵀP)⁻¹ Pᵀ Y₀` of the old approximation equals `U₁ U₁ᵀ Y₀`. -/
theorem transfer_eq {U₁ : Matrix m l ℝ} (hU₁ : U₁ᵀ * U₁ = 1) {M : Matrix l l ℝ}
    (hM : IsUnit M.det) (Y₀ : Matrix m n ℝ) :
    U₁ * M * (((U₁ * M)ᵀ * (U₁ * M))⁻¹ * ((U₁ * M)ᵀ * Y₀)) = U₁ * U₁ᵀ * Y₀ := by
  have h := obliqueProj_self_mul_right hU₁ hM
  rw [obliqueProj] at h
  rw [← h]
  simp only [Matrix.mul_assoc]

end Sketch

section SketchBound

open Matrix
open scoped LeanDLRA.Frobenius

/-- **OP-RS-05** (sBUG, [CarrelGrigori2026, §5]; proved): the orthogonal-sketch BUG step in
raw matrix form, whose K-step uses the right factor `W₀ (W₀ᵀ W₀)⁻¹ W₀ᵀ` of a sketched co-range
basis `W₀ = V₀ R₀`, whose L-step uses `Z₀ (Z₀ᵀ Z₀)⁻¹ Z₀ᵀ` with `Z₀ = U₀ R₀'`, and whose new
bases `Uh = U₁ R₁`, `Vh = V₁ R₁'` (only sketch-orthonormal; `R₀, R₀', R₁, R₁'` invertible)
enter through `Uh (Uhᵀ Uh)⁻¹ Uhᵀ` and `Vh (Vhᵀ Vh)⁻¹ Vhᵀ`, **is** a BUG step (`IsBUGStep`) for
the orthonormal bases `U₀, V₀, U₁, V₁`.  Hence it inherits `IsBUGStep.local_error_le` and
`bug_global_error_le`: in exact arithmetic orthogonal sketching changes nothing.  (The new bases are
named `Uh`, `Vh` in place of `Û`, `V̂`, which are not Lean identifiers.) -/
theorem sketchedBUG_isBUGStep {m n r k l : Type*} [Fintype m] [Fintype n] [Fintype r]
    [Fintype k] [Fintype l] [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq k]
    [DecidableEq l] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {ε t₀ t₁ : ℝ}
    {U₀ Z₀ : Matrix m r ℝ} {V₀ W₀ : Matrix n r ℝ} {U₁ Uh : Matrix m k ℝ} {V₁ Vh : Matrix n l ℝ}
    {R₀ R₀' : Matrix r r ℝ} {R₁ : Matrix k k ℝ} {R₁' : Matrix l l ℝ} {Y₀ : Matrix m n ℝ}
    {YK YL YS : ℝ → Matrix m n ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1)
    (hW₀ : W₀ = V₀ * R₀) (hZ₀ : Z₀ = U₀ * R₀') (hUh : Uh = U₁ * R₁) (hVh : Vh = V₁ * R₁')
    (hR₀ : IsUnit R₀.det) (hR₀' : IsUnit R₀'.det) (hR₁ : IsUnit R₁.det) (hR₁' : IsUnit R₁'.det)
    (hK : ODESolution (fun t X => F t X * obliqueProj W₀ W₀) YK t₀ t₁) (hK₀ : YK t₀ = Y₀)
    (hKcap : obliqueProj Uh Uh * YK t₁ = YK t₁)
    (hεK : ∀ t ∈ Icc t₀ t₁, ‖(1 - U₁ * U₁ᵀ) * F t (YK t₁) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hL : ODESolution (fun t X => obliqueProj Z₀ Z₀ * F t X) YL t₀ t₁) (hL₀ : YL t₀ = Y₀)
    (hLcap : YL t₁ * obliqueProj Vh Vh = YL t₁)
    (hεL : ∀ t ∈ Icc t₀ t₁, ‖(1 - U₀ * U₀ᵀ) * F t (YL t₁) * (1 - V₁ * V₁ᵀ)‖ ≤ ε)
    (hS : ODESolution (fun t X => obliqueProj Uh Uh * F t X * obliqueProj Vh Vh) YS t₀ t₁)
    (hS₀ : YS t₀ = obliqueProj Uh Uh * Y₀ * obliqueProj Vh Vh) :
    IsBUGStep F ε (leftProj U₀) (rightProj V₀) (leftProj U₁) (rightProj V₁) t₀ t₁ Y₀ YK YL
      YS := by
  subst hW₀ hZ₀ hUh hVh
  rw [obliqueProj_self_mul_right hV₀ hR₀] at hK
  rw [obliqueProj_self_mul_right hU₀ hR₀'] at hL
  rw [obliqueProj_self_mul_right hU₁ hR₁] at hKcap hS hS₀
  rw [obliqueProj_self_mul_right hV₁ hR₁'] at hLcap hS hS₀
  have hSf : (fun t X => leftProj U₁ (rightProj V₁ (F t X))) =
      fun t X => U₁ * U₁ᵀ * F t X * (V₁ * V₁ᵀ) := by
    funext t X; simp only [leftProj_apply, rightProj_apply', Matrix.mul_assoc]
  refine ⟨isOrthProj_leftProj hU₀, isOrthProj_rightProj hV₀, isOrthProj_leftProj hU₁,
    isOrthProj_rightProj hV₁, fun X => leftProj_rightProj_comm U₁ V₁ X, hK, hK₀, hKcap,
    fun t ht => ?_, hL, hL₀, hLcap, fun t ht => ?_, hSf ▸ hS, ?_⟩
  · rw [one_sub_leftProj_apply, one_sub_rightProj_apply, ← Matrix.mul_assoc]
    exact hεK t ht
  · rw [one_sub_rightProj_apply, one_sub_leftProj_apply]
    exact hεL t ht
  · rw [hS₀]; simp only [leftProj_apply, rightProj_apply', Matrix.mul_assoc]

end SketchBound

/-! ## Algebraic identities of sketched and interpolatory steps -/

section Identities

open Matrix

variable {m n k : Type*} [Fintype m] [Fintype k] [DecidableEq k]

/-- **Implicit TDB-CUR as residual collocation** ([NaderiAkhavanBabaee2024, §3.3.1], algebraic
core): the residual `X - 𝒫 X` of the interpolatory projection `𝒫 = U (SᵀU)⁻¹ Sᵀ` vanishes on the
selected rows, `Sᵀ (X - 𝒫 X) = 0`. Applied to `X = Y₀ + h F(Y₁)` this says that the implicit CUR
step satisfies the time-discrete equation exactly at the selected rows/columns. -/
theorem transpose_mul_residual_eq_zero {U S : Matrix m k ℝ} (hSU : IsUnit (Sᵀ * U).det)
    (X : Matrix m n ℝ) : Sᵀ * (X - obliqueProj U S * X) = 0 := by
  rw [Matrix.mul_sub, transpose_mul_obliqueProj_mul hSU, sub_self]

/-- **Oblique conversion** ([YeYang2025, §3.2]): `E_X = U (SᵀU)⁻¹` is the basis of
`range U` dual to the selection `S` (`Sᵀ E_X = 1`), and `E_X Sᵀ` is the oblique projector
`𝒫 = U (SᵀU)⁻¹ Sᵀ`. -/
theorem obliqueConversion {U S : Matrix m k ℝ} (hSU : IsUnit (Sᵀ * U).det) :
    Sᵀ * (U * (Sᵀ * U)⁻¹) = 1 ∧ U * (Sᵀ * U)⁻¹ * Sᵀ = obliqueProj U S := by
  refine ⟨?_, rfl⟩
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hSU]

end Identities

/-- **Norm equivalence for sketch-orthonormal bases** ([CarrelGrigori2026, §5.2]): if the sketch
`Θ` is an `ε`-embedding at `y = P x` (`(1 - ε)‖y‖² ≤ ‖Θ y‖² ≤ (1 + ε)‖y‖²`, `0 ≤ ε < 1`) and the
sketched basis `Θ P` has orthonormal columns (`‖Θ P x‖ = ‖x‖`), then
`‖x‖²/(1 + ε) ≤ ‖P x‖² ≤ ‖x‖²/(1 - ε)` (the Loewner bounds on `PᵀP`, coordinatewise). -/
theorem norm_sq_bounds_of_sketch {X Y Z : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedAddCommGroup Z] {P : X → Y} {Θ : Y → Z} {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) {x : X}
    (hlo : (1 - ε) * ‖P x‖ ^ 2 ≤ ‖Θ (P x)‖ ^ 2) (hhi : ‖Θ (P x)‖ ^ 2 ≤ (1 + ε) * ‖P x‖ ^ 2)
    (horth : ‖Θ (P x)‖ = ‖x‖) :
    ‖x‖ ^ 2 / (1 + ε) ≤ ‖P x‖ ^ 2 ∧ ‖P x‖ ^ 2 ≤ ‖x‖ ^ 2 / (1 - ε) := by
  rw [horth] at hlo hhi
  constructor
  · rw [div_le_iff₀ (by linarith)]; linarith
  · rw [le_div_iff₀ (by linarith)]; linarith

section ObliqueExample

open Matrix
open scoped LeanDLRA.Frobenius

/-- A genuinely oblique interpolatory projector (so `IsObliqueBUGStep` is not restricted to
orthogonal maps): with `U = e₁`, `S = (1, 1)ᵀ` in `ℝ²`, `X ↦ U (SᵀU)⁻¹ Sᵀ X` is an oblique
projector onto `X ↦ U Uᵀ X` that differs from it. -/
example : IsObliqueProj (leftOblique !![(1 : ℝ); 0] !![1; 1] :
      Matrix (Fin 2) (Fin 1) ℝ →L[ℝ] Matrix (Fin 2) (Fin 1) ℝ) (leftProj !![(1 : ℝ); 0]) ∧
    (leftOblique !![(1 : ℝ); 0] !![1; 1] :
      Matrix (Fin 2) (Fin 1) ℝ →L[ℝ] Matrix (Fin 2) (Fin 1) ℝ) ≠ leftProj !![(1 : ℝ); 0] := by
  have hU : (!![(1 : ℝ); 0])ᵀ * !![(1 : ℝ); 0] = 1 := by
    ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  have hSU : (!![(1 : ℝ); 1])ᵀ * !![(1 : ℝ); 0] = 1 := by
    ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  have hdet : IsUnit ((!![(1 : ℝ); 1])ᵀ * !![(1 : ℝ); 0]).det := by rw [hSU]; simp
  refine ⟨isObliqueProj_leftOblique hU hdet, fun h => ?_⟩
  have h1 := congrArg (fun T => T !![(0 : ℝ); 1] 0 0) h
  simp only [leftOblique_apply, leftProj_apply, obliqueProj, hSU, inv_one, Matrix.mul_one] at h1
  simp [Matrix.mul_apply] at h1
  simp [Matrix.vecMul, dotProduct] at h1

end ObliqueExample

section ObliqueStepExample

open Matrix
open scoped LeanDLRA.Frobenius

/-- `e₁ ∈ ℝ^{2×1}`, the (orthonormal) basis of the example. -/
private def exU : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The DEIM-type selection vector `(1, 1)ᵀ` of the example (not a multiple of `exU`). -/
private def exS : Matrix (Fin 2) (Fin 1) ℝ := !![1; 1]

private lemma exU_orth : exUᵀ * exU = 1 := by
  ext i j; fin_cases i; fin_cases j; simp [exU, Matrix.mul_apply]

private lemma exSU : exSᵀ * exU = 1 := by
  ext i j; fin_cases i; fin_cases j; simp [exU, exS, Matrix.mul_apply]

private lemma exUS : exUᵀ * exS = 1 := by
  ext i j; fin_cases i; fin_cases j; simp [exU, exS, Matrix.mul_apply]

private lemma exSU_det : IsUnit (exSᵀ * exU).det := by rw [exSU]; simp

private lemma ex_obliqueProj : obliqueProj exU exS = exU * exSᵀ := by
  rw [obliqueProj, exSU, inv_one, Matrix.mul_one]

/-- All four maps fix the field value `C = e₁ e₁ᵀ`. -/
private lemma ex_maps :
    leftOblique exU exS (exU * exUᵀ : Matrix (Fin 2) (Fin 2) ℝ) = exU * exUᵀ ∧
    rightOblique exU exS (exU * exUᵀ : Matrix (Fin 2) (Fin 2) ℝ) = exU * exUᵀ ∧
    leftProj exU (exU * exUᵀ : Matrix (Fin 2) (Fin 2) ℝ) = exU * exUᵀ ∧
    rightProj exU (exU * exUᵀ : Matrix (Fin 2) (Fin 2) ℝ) = exU * exUᵀ := by
  simp only [leftOblique_apply, rightOblique_apply, leftProj_apply, rightProj_apply',
    ex_obliqueProj, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc exSᵀ, exSU, Matrix.one_mul]
  · rw [← Matrix.mul_assoc exUᵀ exS, exUS, Matrix.one_mul]
  · rw [← Matrix.mul_assoc exUᵀ exU, exU_orth, Matrix.one_mul]
  · rw [← Matrix.mul_assoc exUᵀ exU, exU_orth, Matrix.one_mul]

/-- **Genuinely oblique satisfiability of `IsObliqueBUGStep`** on `ℝ^{2×2}`: `U₀ = V₀ = U₁ = V₁
= e₁`, the oblique maps `X ↦ e₁ (Sᵀe₁)⁻¹ Sᵀ X`, `X ↦ X S (e₁ᵀS)⁻¹ e₁ᵀ` with `S = (1, 1)ᵀ` (both
different from the orthogonal projectors), the nonzero constant field `F ≡ e₁ e₁ᵀ`, `Y₀ = 0`,
the trajectories `t ↦ t e₁ e₁ᵀ` on `[0, 1]`, `ε = 0`, and `η` the larger Lebesgue constant. -/
example : ∃ η : ℝ, IsObliqueBUGStep (E := Matrix (Fin 2) (Fin 2) ℝ) (fun _ _ => exU * exUᵀ) 0 η
      (leftProj exU) (rightProj exU) (leftProj exU) (rightProj exU) (rightOblique exU exS)
      (leftOblique exU exS) (leftOblique exU exS) (rightOblique exU exS) 0 1 0
      (fun t => 0 + t • (exU * exUᵀ)) (fun t => 0 + t • (exU * exUᵀ))
      (fun t => 0 + t • (exU * exUᵀ)) ∧
    (rightOblique exU exS : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] _) ≠ rightProj exU ∧
    (leftOblique exU exS : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] _) ≠ leftProj exU ∧
    (exU * exUᵀ : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := by
  obtain ⟨hl, hr, hpl, hpr⟩ := ex_maps
  have hdet : IsUnit (exSᵀ * exU).det := exSU_det
  have hP0 : (leftProj exU : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] _) ≠ 0 := leftProj_ne_zero exU_orth
  have hQ0 : (rightProj exU : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] _) ≠ 0 :=
    rightProj_ne_zero exU_orth
  set C : Matrix (Fin 2) (Fin 2) ℝ := exU * exUᵀ with hC
  refine ⟨max ‖(leftOblique exU exS : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] _)‖
    ‖(rightOblique exU exS : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] _)‖, ?_, ?_, ?_, ?_⟩
  · exact
    { obliqueK := isObliqueProj_rightOblique exU_orth hdet
      obliqueL := isObliqueProj_leftOblique exU_orth hdet
      ne_Q₀ := hQ0
      ne_P₀ := hP0
      projP₁ := isOrthProj_leftProj exU_orth
      projQ₁ := isOrthProj_rightProj exU_orth
      commK := fun X => by
        simp only [leftProj_apply, rightOblique_apply, Matrix.mul_assoc]
      commL := fun X => by
        simp only [rightProj_apply', leftOblique_apply, Matrix.mul_assoc]
      obliqueA := isObliqueProj_leftOblique exU_orth hdet
      obliqueB := isObliqueProj_rightOblique exU_orth hdet
      ne_P₁ := hP0
      ne_Q₁ := hQ0
      normRK := le_max_right _ _
      normRL := le_max_left _ _
      normPA := le_max_left _ _
      normQA := le_max_right _ _
      kSol := Exactness.odeSolution_add_smul_of_const (fun _ _ => hr) 0 0 1
      kStart := by simp
      kCap := by simp [hpl]
      kNormal := fun _ _ => by simp [hpr]
      lSol := Exactness.odeSolution_add_smul_of_const (fun _ _ => hl) 0 0 1
      lStart := by simp
      lCap := by simp [hpr]
      lNormal := fun _ _ => by simp [hpl]
      sSol := Exactness.odeSolution_add_smul_of_const (fun _ _ => by rw [hr, hl]) 0 0 1
      sStart := by simp }
  · intro h
    have h1 := congrArg (fun T => T !![(0 : ℝ), 1; 0, 0] 0 0) h
    simp only [rightOblique_apply, rightProj_apply', ex_obliqueProj] at h1
    simp [exU, exS, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at h1
  · intro h
    have h1 := congrArg (fun T => T !![(0 : ℝ), 0; 1, 0] 0 0) h
    simp only [leftOblique_apply, leftProj_apply, ex_obliqueProj] at h1
    simp [exU, exS, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at h1
  · intro h
    have h1 := congrArg (fun T => T 0 0) h
    rw [hC] at h1
    simp [exU, Matrix.mul_apply] at h1

end ObliqueStepExample

/-! ## Satisfiability -/

/-- The hypotheses of `IsObliqueBUGStep` are jointly satisfiable with a nontrivial field: on `ℝ`
with `F ≡ 1`, all projectors the identity, `η = 1`, `ε = 0`, and the trajectories `t ↦ t` on
`[0, 1]` started at `Y₀ = 0`. -/
example : IsObliqueBUGStep (E := ℝ) (fun _ _ => 1) 0 1 1 1 1 1 1 1 1 1 0 1 0 (fun t => t)
    (fun t => t) (fun t => t) where
  obliqueK := IsOrthProj.one.isObliqueProj
  obliqueL := IsOrthProj.one.isObliqueProj
  ne_Q₀ := one_ne_zero
  ne_P₀ := one_ne_zero
  projP₁ := IsOrthProj.one
  projQ₁ := IsOrthProj.one
  commK _ := rfl
  commL _ := rfl
  obliqueA := IsOrthProj.one.isObliqueProj
  obliqueB := IsOrthProj.one.isObliqueProj
  ne_P₁ := one_ne_zero
  ne_Q₁ := one_ne_zero
  normRK := ContinuousLinearMap.norm_id_le
  normRL := ContinuousLinearMap.norm_id_le
  normPA := ContinuousLinearMap.norm_id_le
  normQA := ContinuousLinearMap.norm_id_le
  kSol := LeanDLRA.odeSolution_id_of_eq_one (fun _ _ => rfl) 0 1
  kStart := rfl
  kCap := rfl
  kNormal _ _ := by simp
  lSol := LeanDLRA.odeSolution_id_of_eq_one (fun _ _ => rfl) 0 1
  lStart := rfl
  lCap := rfl
  lNormal _ _ := by simp
  sSol := LeanDLRA.odeSolution_id_of_eq_one (fun _ _ => rfl) 0 1
  sStart := by simp

end LeanDLRA.ObliqueBUG
