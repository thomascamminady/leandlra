import LeanDLRA.Integrators.BUGCore
import LeanDLRA.Integrators.Tube

/-!
# The Tucker BUG step without analysis constants, near a reference solution

The basis-update & Galerkin (BUG) integrator for `d` modes (Ceruti and Lubich, arXiv:2010.02022,
§5, for Tucker tensors) advances an approximation `Y₀` from `t₀` to `t₁` by a basis update for
every mode, followed by a Galerkin step in the common range of the projectors after the update.
This file states the step as a predicate that contains the algorithm only
(`IsTuckerBUGStepCore`), and shows that the error analysis of
`LeanDLRA/Integrators/TuckerBUG.lean` needs the Lipschitz constant, the bound of the field and
the bound of its normal part only on a tube around a reference solution. It is the counterpart
for `d` modes of `LeanDLRA/Integrators/BUGCore.lean`, which treats two modes
(`isTuckerBUGStepCore_two_iff`).

The space `E` is a real inner product space and the projectors of the modes are data. No tensor
occurs: the statements apply to Tucker tensors once the projectors are those of mode bases.

## Main definitions

* `IsTuckerBUGStepCore F Q₀ P₁ t₀ t₁ Y₀ YK YS`: a basis update `BasisUpdate` for the modes
  `i : Fin d` (old projectors `Q₀ i`, substeps `YK i`, projectors `P₁ i` after the update) and
  the Galerkin step `YS` for the product `modeProd P₁` of the projectors after the update, from
  the start value `modeProd P₁ Y₀`. The value after the step is `YS t₁`.

## Main results

* `isTuckerBUGStep_iff_core`: the predicate `IsTuckerBUGStep` of the error analysis is
  `IsTuckerBUGStepCore` together with the bounds on the normal part of the field at the results
  of the substeps.
* `IsTuckerBUGStepCore.hasLocalError`: the local error
  `(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))`, `c₁ = tuckerC₁ d L H`, `c₂ = tuckerC₂ d L B H`, for a field
  that is Lipschitz and bounded everywhere.
* `IsTuckerBUGStepCore.norm_galerkin_sub_lt_of_near`: if
  `‖Y₀ - A t₀‖ + (d + 2) B (t₁ - t₀) < ρ`, the Galerkin step stays in the tube of radius `ρ`
  around the reference solution `A`.
* `isTuckerBUGStepCore_tubeExt_iff_of_near`, `isTuckerBUGStep_tubeExt_iff_of_near`: under the
  same condition the tube extension `tubeExt F A a b ρ` has the same steps as `F`.
* `IsTuckerBUGStepCore.hasLocalError_of_tube`: the local error for a field that is Lipschitz and
  bounded on the tube only.
* `tucker_global_error_le_of_tube`: the error bound
  `e^{L T} δ + T e^{L T} (c₁ ε + c₂ h)` for a chain of steps of size `h`, from hypotheses on the
  tube.

## Implementation notes

The margin `(d + 2) B (t₁ - t₀)` has two parts. Every projector after the update moves the start
value by at most `B (t₁ - t₀)` (`BasisUpdate.norm_one_sub_apply_le_of_near`), so the start value
`modeProd P₁ Y₀` of the Galerkin step is within `d B (t₁ - t₀)` of `Y₀`
(`norm_sub_modeProd_apply_le`); the Galerkin step and the reference solution then move by at
most `B (t₁ - t₀)` each. For `d = 2` this is the margin `4 B (t₁ - t₀)` of
`isBUGStepCore_tubeExt_iff_of_near`. The basis update itself needs `2 B (t₁ - t₀)` for any
number of modes (`BasisUpdate.norm_sub_lt_of_near`).

In `tucker_global_error_le_of_tube` the exact solutions `Φ n` on the steps and the bounds on the
normal part at the results of the substeps are hypotheses, as in `tucker_global_error_le` and in
`bug_global_error_le_of_tube`. A statement without them needs steps given by mode bases, for
which the substeps can be shown to exist; it belongs to the files on Tucker tensors.

## References

* G. Ceruti, Ch. Lubich, *An unconventional robust integrator for dynamical low-rank
  approximation*, arXiv:2010.02022 (BIT Numer. Math. 2022), §5, Lemma 7 and Theorem 7.
-/

open Set

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The step -/

/-- **One step of the BUG integrator for `d` modes, without constants of the error analysis**
(arXiv:2010.02022, §5.1): a basis update for the modes `i : Fin d` (the substep `YK i` solves
`Ẏ = Q₀ i (F (t, Y))` from `Y₀`, and the projector `P₁ i` after the update captures its result,
see `BasisUpdate`) followed by the Galerkin step `Ẏ = Π (F (t, Y))` from the start value `Π Y₀`,
where `Π = modeProd P₁` is the product of the projectors after the update. The value after the
step is `YS t₁`.

In contrast to `IsTuckerBUGStep` the predicate contains no bound for the normal part of `F`; see
`isTuckerBUGStep_iff_core`. For two modes it is `IsBUGStepCore`
(`isTuckerBUGStepCore_two_iff`). -/
structure IsTuckerBUGStepCore (F : ℝ → E → E) {d : ℕ} (Q₀ P₁ : Fin d → E →L[ℝ] E) (t₀ t₁ : ℝ)
    (Y₀ : E) (YK : Fin d → ℝ → E) (YS : ℝ → E) : Prop
    extends BasisUpdate F Q₀ P₁ t₀ t₁ Y₀ YK where
  /-- The Galerkin step solves `Ẏ = Π (F (t, Y))` with `Π = modeProd P₁`. -/
  sSol : ODESolution (fun t x => modeProd P₁ (F t x)) YS t₀ t₁
  /-- The Galerkin step starts at the projection `Π Y₀` of the start value. -/
  sStart : YS t₀ = modeProd P₁ Y₀

variable {F : ℝ → E → E} {t₀ t₁ : ℝ} {Y₀ : E} {d : ℕ} {Q₀ P₁ : Fin d → E →L[ℝ] E}
  {YK : Fin d → ℝ → E} {YS : ℝ → E}

/-- A step for `d` modes is a basis update followed by the Galerkin step. -/
theorem isTuckerBUGStepCore_iff :
    IsTuckerBUGStepCore F Q₀ P₁ t₀ t₁ Y₀ YK YS ↔
      BasisUpdate F Q₀ P₁ t₀ t₁ Y₀ YK ∧
        ODESolution (fun t x => modeProd P₁ (F t x)) YS t₀ t₁ ∧ YS t₀ = modeProd P₁ Y₀ :=
  ⟨fun hs => ⟨hs.toBasisUpdate, hs.sSol, hs.sStart⟩, fun ⟨hb, hS, hS₀⟩ => ⟨hb, hS, hS₀⟩⟩

/-- The predicate `IsTuckerBUGStep` of the error analysis is the algorithm
`IsTuckerBUGStepCore` together with the bounds on the normal part of the field at the results of
the substeps. -/
theorem isTuckerBUGStep_iff_core {ε : ℝ} :
    IsTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS ↔
      IsTuckerBUGStepCore F Q₀ P₁ t₀ t₁ Y₀ YK YS ∧
        ∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁ i) ((1 - Q₀ i) (F t (YK i t₁)))‖ ≤ ε := by
  rw [isTuckerBUGStep_iff, isTuckerBUGStepCore_iff]
  exact ⟨fun ⟨hb, hN, hS, hS₀⟩ => ⟨⟨hb, hS, hS₀⟩, hN⟩,
    fun ⟨⟨hb, hS, hS₀⟩, hN⟩ => ⟨hb, hN, hS, hS₀⟩⟩

/-- A step with bounds on the normal part contains the step of the algorithm. -/
theorem IsTuckerBUGStep.isTuckerBUGStepCore {ε : ℝ}
    (hs : IsTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS) :
    IsTuckerBUGStepCore F Q₀ P₁ t₀ t₁ Y₀ YK YS :=
  (isTuckerBUGStep_iff_core.1 hs).1

/-- A step of the algorithm whose substeps end at points where the normal part of the field is
at most `ε` is a step of the error analysis. -/
theorem IsTuckerBUGStepCore.isTuckerBUGStep {ε : ℝ}
    (hs : IsTuckerBUGStepCore F Q₀ P₁ t₀ t₁ Y₀ YK YS)
    (hε : ∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁ i) ((1 - Q₀ i) (F t (YK i t₁)))‖ ≤ ε) :
    IsTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS :=
  isTuckerBUGStep_iff_core.2 ⟨hs, hε⟩

/-- For two modes the step is the BUG step `IsBUGStepCore`: the K-step with the old projector
`Q₀` and the L-step with the old projector `P₀`, and the Galerkin step for `P₁ ∘ Q₁`. -/
theorem isTuckerBUGStepCore_two_iff {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {YK YL : ℝ → E} :
    IsTuckerBUGStepCore F ![Q₀, P₀] ![P₁, Q₁] t₀ t₁ Y₀ ![YK, YL] YS ↔
      IsBUGStepCore F P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS := by
  rw [isTuckerBUGStepCore_iff, isBUGStepCore_iff]
  have e : modeProd ![P₁, Q₁] = P₁ * Q₁ := modeProd_two P₁ Q₁
  constructor
  · rintro ⟨hb, hS, hS₀⟩
    rw [e] at hS hS₀
    exact ⟨hb, hS, hS₀⟩
  · rintro ⟨hb, hS, hS₀⟩
    rw [e]
    exact ⟨hb, hS, hS₀⟩

/-- **Local error of a step for `d` modes** (arXiv:2010.02022, Lemma 7). Let `F` be
`L`-Lipschitz and bounded by `B`, and let the part of `F` that is normal to the range of `P₁ i`
and to the range of `Q₀ i` be at most `ε` at the result `YK i t₁` of every substep. Then the
result `YS t₁` of a step from `(t₀, Y₀)` to `t₁` with `t₁ - t₀ ≤ H` differs from the exact
solution through `(t₀, Y₀)` by at most `(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))` with
`c₁ = tuckerC₁ d L H` and `c₂ = tuckerC₂ d L B H`. -/
theorem IsTuckerBUGStepCore.hasLocalError {L B ε H : ℝ}
    (hs : IsTuckerBUGStepCore F Q₀ P₁ t₀ t₁ Y₀ YK YS)
    (hε : ∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁ i) ((1 - Q₀ i) (F t (YK i t₁)))‖ ≤ ε)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (h01 : t₀ ≤ t₁)
    (hH : t₁ - t₀ ≤ H) :
    HasLocalError F t₀ t₁ Y₀ (YS t₁)
      ((t₁ - t₀) * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * (t₁ - t₀))) :=
  fun _ hΦ hΦ₀ => (hs.isTuckerBUGStep hε).local_error_le hF hL hB (by ring)
    (sub_nonneg.2 h01) hH hΦ hΦ₀

/-! ### Steps near a reference solution

The field `F` is Lipschitz and bounded only on the tube
`{(t, x) | t ∈ [a, b], ‖x - A t‖ ≤ ρ}` around a reference solution `A`. The estimates of this
section show that the Galerkin step stays in the tube when the start value lies well inside it;
for the substeps of the basis update this is `BasisUpdate.norm_sub_lt_of_near`. -/

section Near

variable {A : ℝ → E} {a b ρ B : ℝ}

/-- A step for the tube extension of `F` whose substeps and Galerkin step stay in the tube is a
step for `F`, and conversely. -/
theorem isTuckerBUGStepCore_tubeExt_iff (ha : a ≤ t₀) (hb : t₁ ≤ b)
    (hK : ∀ i, ∀ t ∈ Ico t₀ t₁, ‖YK i t - A t‖ ≤ ρ) (hS : ∀ t ∈ Ico t₀ t₁, ‖YS t - A t‖ ≤ ρ) :
    IsTuckerBUGStepCore (tubeExt F A a b ρ) Q₀ P₁ t₀ t₁ Y₀ YK YS ↔
      IsTuckerBUGStepCore F Q₀ P₁ t₀ t₁ Y₀ YK YS :=
  isTuckerBUGStepCore_iff.trans <| ((basisUpdate_tubeExt_iff ha hb hK).and
    ((odeSolution_comp_tubeExt_iff (fun x => modeProd P₁ x) ha hb hS).and Iff.rfl)).trans
    isTuckerBUGStepCore_iff.symm

/-- If the start value satisfies `‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, the start value
`modeProd P₁ Y₀` of the Galerkin step is within `‖Y₀ - A t₀‖ + d B (t₁ - t₀)` of `A t₀`: every
projector after the update moves `Y₀` by at most `B (t₁ - t₀)`. -/
theorem IsTuckerBUGStepCore.norm_start_sub_le_of_near
    (hs : IsTuckerBUGStepCore F Q₀ P₁ t₀ t₁ Y₀ YK YS) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    ‖modeProd P₁ Y₀ - A t₀‖ ≤ ‖Y₀ - A t₀‖ + d * B * (t₁ - t₀) := by
  have h₁ : ‖Y₀ - modeProd P₁ Y₀‖ ≤ ∑ _i : Fin d, B * (t₁ - t₀) :=
    (norm_sub_modeProd_apply_le (fun i y => (hs.projP₁ i).norm_le y) Y₀).trans
      (Finset.sum_le_sum fun i _ => by
        have h := hs.toBasisUpdate.norm_one_sub_apply_le_of_near hFB hB ha hb h01 hA hsmall i
        simpa using h)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h₁
  have e : modeProd P₁ Y₀ - A t₀ = (Y₀ - A t₀) - (Y₀ - modeProd P₁ Y₀) := by abel
  rw [e]
  have h₂ := norm_sub_le (Y₀ - A t₀) (Y₀ - modeProd P₁ Y₀)
  linarith

/-- If the start value satisfies `‖Y₀ - A t₀‖ + (d + 2) B (t₁ - t₀) < ρ`, the Galerkin step of
a step for `d` modes stays strictly inside the tube of radius `ρ` around `A`. -/
theorem IsTuckerBUGStepCore.norm_galerkin_sub_lt_of_near
    (hs : IsTuckerBUGStepCore F Q₀ P₁ t₀ t₁ Y₀ YK YS) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + (d + 2) * B * (t₁ - t₀) < ρ) :
    ∀ t ∈ Icc t₀ t₁, ‖YS t - A t‖ < ρ := by
  intro t ht
  have h01 : t₀ ≤ t₁ := ht.1.trans ht.2
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hdBh : 0 ≤ (d : ℝ) * (B * (t₁ - t₀)) := mul_nonneg (Nat.cast_nonneg d) hBh
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (Y₀ - A t₀)]
  have hS₀ := hs.norm_start_sub_le_of_near hFB hB ha hb h01 hA (by linarith)
  exact tube_trap hA hs.sSol hB hB (hFB.along hρ ha hb)
    (hFB.comp_proj ha hb (fun x => modeProd P₁ x)
      fun x => (IsOrthProj.modeProd hs.projP₁ hs.comm₁).norm_le x)
    (by rw [hs.sStart]; linarith) t ht

/-- **Steps for the tube extension are steps for `F`.** Let `F` be bounded by `B` on the tube of
radius `ρ` around a solution `A`, and let the start value satisfy
`‖Y₀ - A t₀‖ + (d + 2) B (t₁ - t₀) < ρ`. Then all substeps and the Galerkin step of a step for
`d` modes stay in the tube, for `F` and for its tube extension, so that the two fields have the
same steps. -/
theorem isTuckerBUGStepCore_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + (d + 2) * B * (t₁ - t₀) < ρ) :
    IsTuckerBUGStepCore (tubeExt F A a b ρ) Q₀ P₁ t₀ t₁ Y₀ YK YS ↔
      IsTuckerBUGStepCore F Q₀ P₁ t₀ t₁ Y₀ YK YS := by
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hdBh : 0 ≤ (d : ℝ) * (B * (t₁ - t₀)) := mul_nonneg (Nat.cast_nonneg d) hBh
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (Y₀ - A t₀)]
  have h2 : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ := by linarith
  have key : ∀ G : ℝ → E → E, IsBoundedOnTube G A a b ρ B → ODESolution G A t₀ t₁ →
      IsTuckerBUGStepCore G Q₀ P₁ t₀ t₁ Y₀ YK YS →
      (∀ i, ∀ t ∈ Ico t₀ t₁, ‖YK i t - A t‖ ≤ ρ) ∧ ∀ t ∈ Ico t₀ t₁, ‖YS t - A t‖ ≤ ρ :=
    fun G hGB hGA hs =>
    ⟨fun i t ht => (hs.toBasisUpdate.norm_sub_lt_of_near hGB hB ha hb hGA h2 i t
        (Ico_subset_Icc_self ht)).le,
      fun t ht => (hs.norm_galerkin_sub_lt_of_near hGB hB ha hb hGA hsmall t
        (Ico_subset_Icc_self ht)).le⟩
  constructor
  · intro hs
    obtain ⟨hK, hS⟩ := key _ ((isBoundedField_tubeExt hFB hB hρ).isBoundedOnTube A a b ρ)
      ((odeSolution_tubeExt_iff ha hb fun t _ => by simpa using hρ).2 hA) hs
    exact (isTuckerBUGStepCore_tubeExt_iff ha hb hK hS).1 hs
  · intro hs
    obtain ⟨hK, hS⟩ := key F hFB hA hs
    exact (isTuckerBUGStepCore_tubeExt_iff ha hb hK hS).2 hs

/-- The statement of `isTuckerBUGStepCore_tubeExt_iff_of_near` for steps with bounds on the
normal part: the results of the substeps lie in the tube, where `F` and its tube extension
agree, so the bounds for the two fields are the same. -/
theorem isTuckerBUGStep_tubeExt_iff_of_near {ε : ℝ} (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + (d + 2) * B * (t₁ - t₀) < ρ) :
    IsTuckerBUGStep (tubeExt F A a b ρ) ε Q₀ P₁ t₀ t₁ Y₀ YK YS ↔
      IsTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS := by
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hdBh : 0 ≤ (d : ℝ) * (B * (t₁ - t₀)) := mul_nonneg (Nat.cast_nonneg d) hBh
  have h2 : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ := by linarith
  rw [isTuckerBUGStep_iff_core, isTuckerBUGStep_iff_core,
    isTuckerBUGStepCore_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall]
  refine and_congr_right fun hs => ?_
  have hK := hs.toBasisUpdate.mem_tubeSet_of_near hFB hB ha hb h01 hA h2
  have eK : ∀ i, ∀ t ∈ Icc t₀ t₁, tubeExt F A a b ρ t (YK i t₁) = F t (YK i t₁) :=
    fun i t ht => tubeExt_eq (hK i t ht).1 (hK i t ht).2
  exact forall_congr' fun i => forall₂_congr fun t ht => by rw [eK i t ht]

/-- **Local error of a step for `d` modes near a reference solution.** Let `F` be `L`-Lipschitz
and bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`, let the step
from `(t₀, Y₀)` to `t₁` lie in `[a, b]` with `t₁ - t₀ ≤ H`, and let the start value satisfy
`‖Y₀ - A t₀‖ + (d + 2) B (t₁ - t₀) < ρ`. If the normal part of `F` is at most `ε` at the result
`YK i t₁` of every substep, then the result `YS t₁` differs from the exact solution through
`(t₀, Y₀)` by at most `(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))` with `c₁ = tuckerC₁ d L H` and
`c₂ = tuckerC₂ d L B H`. Nothing is assumed about `F` outside the tube. -/
theorem IsTuckerBUGStepCore.hasLocalError_of_tube {L ε H : ℝ}
    (hs : IsTuckerBUGStepCore F Q₀ P₁ t₀ t₁ Y₀ YK YS)
    (hε : ∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁ i) ((1 - Q₀ i) (F t (YK i t₁)))‖ ≤ ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hH : t₁ - t₀ ≤ H)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖Y₀ - A t₀‖ + (d + 2) * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ (YS t₁)
      ((t₁ - t₀) * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * (t₁ - t₀))) := by
  intro Φ hΦ hΦ₀
  have hh : 0 ≤ t₁ - t₀ := sub_nonneg.2 h01
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB hh
  have hdBh : 0 ≤ (d : ℝ) * (B * (t₁ - t₀)) := mul_nonneg (Nat.cast_nonneg d) hBh
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (Y₀ - A t₀)]
  have ht₁ : t₁ = t₀ + (t₁ - t₀) := by ring
  have hΦG : ODESolution (tubeExt F A a b ρ) Φ t₀ t₁ :=
    hΦ.tubeExt_of_near hFB hB hh ha hb ht₁ hA (by rw [hΦ₀]; linarith)
  exact ((isTuckerBUGStep_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).2
    (hs.isTuckerBUGStep hε)).local_error_le (isLipschitzField_tubeExt hFL hL hρ) hL
    (isBoundedField_tubeExt hFB hB hρ) ht₁ hh hH hΦG hΦ₀

/-- **Error bound of the BUG integrator for `d` modes from hypotheses near the solution**
(arXiv:2010.02022, Theorem 7). Let `A` solve `Ȧ = F(t, A)` on `[t₀, t₀ + N h]`, and let `F` be
`L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around `A`. For `n < N` let step `n`
of the integrator (`IsTuckerBUGStep`, with normal part at most `ε` at the results of the
substeps) with step size `0 ≤ h ≤ H` go from `Y n` to `Y (n + 1)`, and let `Φ n` be the exact
solution on step `n` started at `Y n`. If `‖Y 0 - A t₀‖ ≤ δ`, `N h ≤ T` and

  `e^{L T} δ + T e^{L T} (c₁ ε + c₂ h) + (d + 2) B h < ρ`,

`c₁ = tuckerC₁ d L H`, `c₂ = tuckerC₂ d L B H`, then

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (c₁ ε + c₂ h)` for all `n ≤ N`.

Nothing is assumed about `F` outside the tube. This is `tucker_global_error_le` for a field that
is Lipschitz and bounded only near the solution, and `bug_global_error_le_of_tube` for `d`
modes; it is an instance of `IsLipschitzOnTube.norm_sub_le_of_fan_uniformGrid` with the local
error `IsTuckerBUGStepCore.hasLocalError_of_tube`. -/
theorem tucker_global_error_le_of_tube {L ε H h : ℝ} {N : ℕ}
    (hFL : IsLipschitzOnTube F A t₀ (t₀ + N * h) ρ L) (hL : 0 ≤ L)
    (hFB : IsBoundedOnTube F A t₀ (t₀ + N * h) ρ B) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hA : ODESolution F A t₀ (t₀ + N * h))
    {Q P : ℕ → Fin d → E →L[ℝ] E} {Y : ℕ → E} {YK : ℕ → Fin d → ℝ → E} {YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsTuckerBUGStep F ε (Q n) (P n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
      (YK n) (YS n))
    (hY : ∀ n < N, Y (n + 1) = YS n (t₀ + (n + 1) * h))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ)
    (hNT : N * h ≤ T)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) *
      (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) + (d + 2) * B * h < ρ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) *
      (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) := by
  have hH : 0 ≤ H := hh.trans hhH
  have hc : 0 ≤ tuckerC₁ d L H * ε + tuckerC₂ d L B H * h :=
    add_nonneg (mul_nonneg (tuckerC₁_nonneg d hL hH) hε)
      (mul_nonneg (tuckerC₂_nonneg d hL hB hH) hh)
  have hBh : 0 ≤ B * h := mul_nonneg hB hh
  have hdBh : 0 ≤ (d : ℝ) * (B * h) := mul_nonneg (Nat.cast_nonneg d) hBh
  refine hFL.norm_sub_le_of_fan_uniformGrid (Φ := Φ) (T := T) (δ₀ := δ)
    (c := tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) hL hFB hB hh hA
    (fun n hn hnear => ⟨hΦ n hn, hΦ₀ n hn, ?_⟩) hc hδ hNT (by linarith)
  obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hn
  obtain ⟨hcore, hεK⟩ := isTuckerBUGStep_iff_core.1 (hstep n hn)
  have hloc := hcore.hasLocalError_of_tube hεK hFL hL hFB hB ha hb h01 (hsub.le.trans hhH)
    (hA.mono ha hb) (by rw [hsub]; linarith)
  rw [hsub] at hloc
  rw [hY n hn]
  exact hloc (Φ n) (hΦ n hn) (hΦ₀ n hn)

end Near

/-! ### Examples

The examples use the constant field `F (t, Y) = c` and the identity as projector of every mode:
all substeps and the Galerkin step are the straight line `t ↦ Y₀ + (t - t₀) • c`. They show that
the hypotheses of the theorems of this file can hold together for a field that is not zero.
Steps with projectors of lower rank need mode bases and belong to the files on Tucker
tensors. -/

section Examples

/-- The straight line `t ↦ y₀ + (t - t₀) • c` solves the equation with the constant field
`c`. -/
private theorem odeSolution_line_aux (y₀ c : E) (t₀ t₁ : ℝ) :
    ODESolution (fun (_ : ℝ) (_ : E) => c) (fun t => y₀ + (t - t₀) • c) t₀ t₁ :=
  ODESolution.of_hasDerivAt (fun t => by
    have h := (((hasDerivAt_id t).sub_const t₀).smul_const c).const_add y₀
    rw [one_smul] at h
    exact h) t₀ t₁

/-- For the constant field `c` and the identity as projector of every mode, the straight lines
from `Y₀` form a step for `d` modes. -/
private theorem isTuckerBUGStepCore_const_aux (c Y₀ : E) (d : ℕ) (t₀ t₁ : ℝ) :
    IsTuckerBUGStepCore (fun (_ : ℝ) (_ : E) => c) (fun _ : Fin d => (1 : E →L[ℝ] E))
      (fun _ => 1) t₀ t₁ Y₀ (fun _ t => Y₀ + (t - t₀) • c) (fun t => Y₀ + (t - t₀) • c) := by
  have hsol := odeSolution_line_aux Y₀ c t₀ t₁
  have hone : ∀ x : E, modeProd (fun _ : Fin d => (1 : E →L[ℝ] E)) x = x := fun x =>
    modeProd_apply_eq_self fun _ => rfl
  have h₀ : (fun t : ℝ => Y₀ + (t - t₀) • c) t₀ = Y₀ := by simp
  exact isTuckerBUGStepCore_iff.2 ⟨⟨fun _ => .one, fun _ => .one, fun _ _ _ => rfl,
    fun _ => hsol, fun _ => h₀, fun _ => rfl⟩, hsol.congr_field fun t _ => (hone c).symm,
    h₀.trans (hone Y₀).symm⟩

/-- Non-vacuity of `IsTuckerBUGStepCore`: a step for `d` modes exists for every constant field,
in particular for one that is not zero. -/
example (c Y₀ : E) (d : ℕ) (t₀ t₁ : ℝ) :
    ∃ (YK : Fin d → ℝ → E) (YS : ℝ → E), IsTuckerBUGStepCore (fun (_ : ℝ) (_ : E) => c)
      (fun _ : Fin d => (1 : E →L[ℝ] E)) (fun _ => 1) t₀ t₁ Y₀ YK YS :=
  ⟨_, _, isTuckerBUGStepCore_const_aux c Y₀ d t₀ t₁⟩

/-- Non-vacuity of `IsTuckerBUGStepCore.hasLocalError`: for the constant field `c` (Lipschitz
with constant `0`, bounded by `‖c‖`) and every `ε ≥ 0` the hypotheses hold, and the straight
line step has the stated local error. -/
example (c Y₀ : E) (d : ℕ) {t₀ t₁ ε : ℝ} (h01 : t₀ ≤ t₁) (hε : 0 ≤ ε) :
    HasLocalError (fun (_ : ℝ) (_ : E) => c) t₀ t₁ Y₀ (Y₀ + (t₁ - t₀) • c)
      ((t₁ - t₀) * (tuckerC₁ d 0 (t₁ - t₀) * ε + tuckerC₂ d 0 ‖c‖ (t₁ - t₀) * (t₁ - t₀))) :=
  (isTuckerBUGStepCore_const_aux c Y₀ d t₀ t₁).hasLocalError (fun _ _ _ => by simpa using hε)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => le_rfl) h01 le_rfl

/-- Non-vacuity of `IsTuckerBUGStepCore.hasLocalError_of_tube`: for the constant field `c`, the
reference solution `A t = A₀ + (t - t₀) • c` and a start value `Y₀` with
`‖Y₀ - A₀‖ + (d + 2) ‖c‖ (t₁ - t₀) < ρ`, all hypotheses hold on the tube of radius `ρ`. -/
example (c A₀ Y₀ : E) (d : ℕ) {t₀ t₁ ρ ε : ℝ} (h01 : t₀ ≤ t₁) (hε : 0 ≤ ε)
    (hsmall : ‖Y₀ - A₀‖ + (d + 2) * ‖c‖ * (t₁ - t₀) < ρ) :
    HasLocalError (fun (_ : ℝ) (_ : E) => c) t₀ t₁ Y₀ (Y₀ + (t₁ - t₀) • c)
      ((t₁ - t₀) * (tuckerC₁ d 0 (t₁ - t₀) * ε + tuckerC₂ d 0 ‖c‖ (t₁ - t₀) * (t₁ - t₀))) :=
  (isTuckerBUGStepCore_const_aux c Y₀ d t₀ t₁).hasLocalError_of_tube
    (A := fun t => A₀ + (t - t₀) • c) (a := t₀) (b := t₁) (B := ‖c‖)
    (fun _ _ _ => by simpa using hε) (fun _ _ _ _ _ _ => by simp) le_rfl
    (fun _ _ _ _ => le_rfl) (norm_nonneg c) le_rfl le_rfl h01 le_rfl
    (odeSolution_line_aux A₀ c t₀ t₁) (by simpa using hsmall)

/-- Non-vacuity of `tucker_global_error_le_of_tube`: for the constant field `c` the values
`Y n = Y₀ + (n h) • c` are a chain of steps for `d` modes along the uniform grid, and all
hypotheses hold on the tube of radius `ρ` around `A t = A₀ + (t - t₀) • c`, for any `c`, any
`ε ≥ 0` and any start error `‖Y₀ - A₀‖ ≤ δ`, as soon as the smallness condition holds. -/
example (c A₀ Y₀ : E) (d N : ℕ) {t₀ h T ρ ε δ : ℝ} (hh : 0 ≤ h) (hε : 0 ≤ ε)
    (hδ : ‖Y₀ - A₀‖ ≤ δ) (hNT : N * h ≤ T)
    (hsmall : Real.exp (0 * T) * δ + T * Real.exp (0 * T) *
      (tuckerC₁ d 0 h * ε + tuckerC₂ d 0 ‖c‖ h * h) + (d + 2) * ‖c‖ * h < ρ) :
    ∀ n ≤ N, ‖Y₀ + ((n : ℝ) * h) • c - (A₀ + (t₀ + n * h - t₀) • c)‖ ≤
      Real.exp (0 * T) * δ + T * Real.exp (0 * T) *
        (tuckerC₁ d 0 h * ε + tuckerC₂ d 0 ‖c‖ h * h) := by
  refine tucker_global_error_le_of_tube (F := fun (_ : ℝ) (_ : E) => c)
    (A := fun t => A₀ + (t - t₀) • c) (B := ‖c‖) (L := 0) (H := h)
    (Q := fun _ _ => 1) (P := fun _ _ => 1) (Y := fun n => Y₀ + ((n : ℝ) * h) • c)
    (YK := fun n _ t => Y₀ + ((n : ℝ) * h) • c + (t - (t₀ + n * h)) • c)
    (YS := fun n t => Y₀ + ((n : ℝ) * h) • c + (t - (t₀ + n * h)) • c)
    (Φ := fun n t => Y₀ + ((n : ℝ) * h) • c + (t - (t₀ + n * h)) • c)
    (fun _ _ _ _ _ _ => by simp) le_rfl (fun _ _ _ _ => le_rfl) (norm_nonneg c) hε hh le_rfl
    (odeSolution_line_aux A₀ c t₀ _)
    (fun n _ => (isTuckerBUGStepCore_const_aux c _ d _ _).isTuckerBUGStep
      fun _ _ _ => by simpa using hε)
    (fun n _ => ?_) (fun n _ => odeSolution_line_aux _ c _ _) (fun n _ => by simp)
    (by simpa using hδ) hNT hsmall
  have e : ((n + 1 : ℕ) : ℝ) * h =
      (n : ℝ) * h + (t₀ + ((n : ℝ) + 1) * h - (t₀ + (n : ℝ) * h)) := by
    push_cast
    ring
  change Y₀ + (((n + 1 : ℕ) : ℝ) * h) • c =
    Y₀ + ((n : ℝ) * h) • c + (t₀ + ((n : ℝ) + 1) * h - (t₀ + (n : ℝ) * h)) • c
  rw [e, add_smul]
  abel

end Examples

end LeanDLRA
