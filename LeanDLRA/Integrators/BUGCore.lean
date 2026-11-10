import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Foundations.Localization
import LeanDLRA.Integrators.Defs

/-!
# The basis update and the BUG step without analysis constants

The basis-update & Galerkin (BUG) integrator advances an approximation `Y₀` of low rank from `t₀`
to `t₁` in two stages. In the *basis update* every mode `i` solves, from the common start value
`Y₀`, the differential equation `Ẏ = Q₀ i (F (t, Y))` projected with the old projector `Q₀ i` of
that mode, and a new orthogonal projector `P₁ i` is chosen whose range contains the result. In the
*Galerkin step* the differential equation is solved in the common range of the new projectors.
For matrices there are two modes: the K-step uses the projector `Q₀` onto the old row space and
yields the new column space (projector `P₁`), the L-step uses the projector `P₀` onto the old
column space and yields the new row space (projector `Q₁`).

This file states the two stages as predicates that contain the algorithm and nothing else. The
predicate `IsBUGStep` of `LeanDLRA/Integrators/BUG.lean` additionally carries a bound `ε` for the
part of `F` that is normal to the low-rank manifold, which is a constant of the error analysis and
not part of the algorithm. Here the normal bounds are hypotheses of the error theorem, and the
old predicate is recovered as the new one together with the two bounds (`isBUGStep_iff`).

## Main definitions

* `BasisUpdate F Q₀ P₁ t₀ t₁ Y₀ YK`: the basis update for a family of modes. It is the part that
  the fixed-rank, the rank-adaptive and the parallel BUG integrator and their Tucker versions
  have in common.
* `IsBUGStepCore F P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS`: one step of the fixed-rank BUG integrator for
  two modes, a basis update followed by the Galerkin step. The new approximation is `YS t₁`.

## Main results

* `basisUpdate_two_iff`, `isBUGStepCore_iff`: the two-mode predicates written out.
* `isBUGStep_iff`: `IsBUGStep` is `IsBUGStepCore` together with the two normal bounds.
* `isTuckerBUGStep_iff`, `isTuckerBUGStep_two_iff`: the Tucker BUG step is a basis update, the
  normal bounds and a Galerkin step; for two modes it is `IsBUGStep`.
* `IsBUGStepCore.hasLocalError`: the local error bound [CerutiLubich2022, Lemma 4] as
  `HasLocalError`, for a globally Lipschitz and bounded field.
* `IsBUGStepCore.hasLocalError_of_tube`: the same bound when `F` is Lipschitz and bounded only on
  a tube around a reference solution `A` and the start value lies well inside the tube.
* `basisUpdate_tubeExt_iff`, `isBUGStepCore_tubeExt_iff`: a step for the tube extension
  `tubeExt F A a b ρ` whose substeps stay in the tube is a step for `F`, and conversely.
* `isBUGStepCore_tubeExt_iff_of_near`, `isBUGStep_tubeExt_iff_of_near`: if the start value
  satisfies `‖Y₀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, all substeps stay in the tube, so that steps for
  `tubeExt F A a b ρ` and steps for `F` are the same.
* `BasisUpdate.norm_sub_lt_of_near`, `BasisUpdate.mem_tubeSet_of_near`,
  `IsBUGStepCore.norm_galerkin_sub_lt_of_near`: the estimates behind this, usable for any method
  that starts with a basis update.

## Implementation notes

`IsBUGStepCore` extends `BasisUpdate` for the families `![Q₀, P₀]`, `![P₁, Q₁]`, `![YK, YL]`, so
that statements about the basis update apply to it through `IsBUGStepCore.toBasisUpdate`. The
entries of the families are recovered with `basisUpdate_two_iff`. The projector `P₀` is the entry
`1` of the family of old projectors, so no separate field states that it is an orthogonal
projector.

The step size is written `t₁ - t₀` throughout; no separate variable for it is used.

## References

* [CerutiLubich2022, §3.1, Lemma 4]
-/

open Set

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The basis update -/

/-- The **basis update** of the BUG integrator from `(t₀, Y₀)` to `t₁` for a family of modes
`i : ι` [CerutiLubich2022, §3.1]. Mode `i` has an old orthogonal projector `Q₀ i` and solves
`Ẏ = Q₀ i (F (t, Y))` from the start value `Y₀`; the solution is `YK i`. The new orthogonal
projector `P₁ i` of the mode captures the result: `P₁ i (YK i t₁) = YK i t₁`. The new projectors
commute.

For matrices `ι` has two elements: the K-step uses the projector `Q₀ = (· V₀ V₀ᵀ)` onto the old
row space and gives the new column space, the L-step uses `P₀ = (U₀ U₀ᵀ ·)` and gives the new
row space (`basisUpdate_two_iff`). The predicate contains no constant of the error analysis. -/
structure BasisUpdate (F : ℝ → E → E) {ι : Type*} (Q₀ P₁ : ι → E →L[ℝ] E) (t₀ t₁ : ℝ) (Y₀ : E)
    (YK : ι → ℝ → E) : Prop where
  /-- The old projectors are orthogonal projectors. -/
  projQ₀ : ∀ i, IsOrthProj (Q₀ i)
  /-- The new projectors are orthogonal projectors. -/
  projP₁ : ∀ i, IsOrthProj (P₁ i)
  /-- The new projectors commute. -/
  comm₁ : ∀ i j x, P₁ i (P₁ j x) = P₁ j (P₁ i x)
  /-- The substep of mode `i` solves `Ẏ = Q₀ i (F (t, Y))`. -/
  kSol : ∀ i, ODESolution (fun t x => Q₀ i (F t x)) (YK i) t₀ t₁
  /-- All substeps start at `Y₀`. -/
  kStart : ∀ i, YK i t₀ = Y₀
  /-- The new projector of mode `i` captures the result of its substep. -/
  kCap : ∀ i, P₁ i (YK i t₁) = YK i t₁

variable {F : ℝ → E → E} {t₀ t₁ : ℝ} {Y₀ : E} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {YK YL YS : ℝ → E}

/-- The basis update for two modes, written out: the K-step with the old projector `Q₀` and the
new projector `P₁`, and the L-step with the old projector `P₀` and the new projector `Q₁`. -/
theorem basisUpdate_two_iff :
    BasisUpdate F ![Q₀, P₀] ![P₁, Q₁] t₀ t₁ Y₀ ![YK, YL] ↔
      (IsOrthProj Q₀ ∧ IsOrthProj P₀) ∧ (IsOrthProj P₁ ∧ IsOrthProj Q₁) ∧
      (∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)) ∧
      (ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁ ∧
        ODESolution (fun t x => P₀ (F t x)) YL t₀ t₁) ∧
      (YK t₀ = Y₀ ∧ YL t₀ = Y₀) ∧ P₁ (YK t₁) = YK t₁ ∧ Q₁ (YL t₁) = YL t₁ := by
  constructor
  · intro hs
    exact ⟨Fin.forall_fin_two.1 hs.projQ₀, Fin.forall_fin_two.1 hs.projP₁, hs.comm₁ 0 1,
      Fin.forall_fin_two.1 hs.kSol, Fin.forall_fin_two.1 hs.kStart, Fin.forall_fin_two.1 hs.kCap⟩
  · rintro ⟨hQ, hP, hc, hsol, hst, hcap⟩
    exact
      { projQ₀ := Fin.forall_fin_two.2 hQ
        projP₁ := Fin.forall_fin_two.2 hP
        comm₁ := Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨fun _ => rfl, hc⟩,
          Fin.forall_fin_two.2 ⟨fun x => (hc x).symm, fun _ => rfl⟩⟩
        kSol := Fin.forall_fin_two.2 hsol
        kStart := Fin.forall_fin_two.2 hst
        kCap := Fin.forall_fin_two.2 hcap }

/-! ### The BUG step -/

/-- One step of the fixed-rank **BUG integrator** from `(t₀, Y₀)` to `t₁`, as an algorithm
[CerutiLubich2022, §3.1]: a basis update for two modes (K-step with the old projector `Q₀`,
L-step with the old projector `P₀`, new projectors `P₁` and `Q₁`, see `basisUpdate_two_iff`)
followed by the Galerkin step `Ẏ = P₁ (Q₁ (F (t, Y)))` from the start value `P₁ (Q₁ Y₀)`. The new
approximation is `YS t₁`.

In contrast to `IsBUGStep` the predicate contains no bound for the normal part of `F`; see
`isBUGStep_iff`. For the matrix integrator in terms of the factors `U`, `S`, `V` see
`MatrixBUG.IsStep` in `LeanDLRA/Integrators/Matrix/BUG.lean`. -/
structure IsBUGStepCore (F : ℝ → E → E) (P₀ Q₀ P₁ Q₁ : E →L[ℝ] E) (t₀ t₁ : ℝ) (Y₀ : E)
    (YK YL YS : ℝ → E) : Prop
    extends BasisUpdate F ![Q₀, P₀] ![P₁, Q₁] t₀ t₁ Y₀ ![YK, YL] where
  /-- The Galerkin step solves `Ẏ = P₁ (Q₁ (F (t, Y)))`. -/
  sSol : ODESolution (fun t x => P₁ (Q₁ (F t x))) YS t₀ t₁
  /-- The Galerkin step starts at the projection of `Y₀` to the new bases. -/
  sStart : YS t₀ = P₁ (Q₁ Y₀)

/-- A BUG step is a basis update for two modes followed by the Galerkin step. -/
theorem isBUGStepCore_iff :
    IsBUGStepCore F P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS ↔
      BasisUpdate F ![Q₀, P₀] ![P₁, Q₁] t₀ t₁ Y₀ ![YK, YL] ∧
        ODESolution (fun t x => P₁ (Q₁ (F t x))) YS t₀ t₁ ∧ YS t₀ = P₁ (Q₁ Y₀) :=
  ⟨fun hs => ⟨hs.toBasisUpdate, hs.sSol, hs.sStart⟩, fun ⟨hb, hS, hS₀⟩ => ⟨hb, hS, hS₀⟩⟩

/-- The predicate `IsBUGStep` of the error analysis is the algorithm `IsBUGStepCore` together
with the bounds `ε` for the normal part of `F` at the results of the K-step and of the L-step. -/
theorem isBUGStep_iff {ε : ℝ} :
    IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS ↔
      IsBUGStepCore F P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS ∧
        (∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε) ∧
        (∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε) := by
  constructor
  · intro hs
    exact ⟨isBUGStepCore_iff.2 ⟨basisUpdate_two_iff.2 ⟨⟨hs.projQ₀, hs.projP₀⟩,
      ⟨hs.projP₁, hs.projQ₁⟩, hs.comm₁, ⟨hs.kSol, hs.lSol⟩, ⟨hs.kStart, hs.lStart⟩, hs.kCap,
      hs.lCap⟩, hs.sSol, hs.sStart⟩, hs.kNormal, hs.lNormal⟩
  · rintro ⟨hs, hK, hL⟩
    obtain ⟨⟨hQ₀, hP₀⟩, ⟨hP₁, hQ₁⟩, hc, ⟨hKs, hLs⟩, ⟨hK₀, hL₀⟩, hKc, hLc⟩ :=
      basisUpdate_two_iff.1 hs.toBasisUpdate
    exact ⟨hP₀, hQ₀, hP₁, hQ₁, hc, hKs, hK₀, hKc, hK, hLs, hL₀, hLc, hL, hs.sSol, hs.sStart⟩

/-- A step with normal bounds is in particular a step. -/
theorem IsBUGStep.isBUGStepCore {ε : ℝ} (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS) :
    IsBUGStepCore F P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS :=
  (isBUGStep_iff.1 hs).1

/-- A step together with the two normal bounds is a step in the sense of `IsBUGStep`. -/
theorem IsBUGStepCore.isBUGStep {ε : ℝ} (hs : IsBUGStepCore F P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS)
    (hεK : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε)
    (hεL : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε) :
    IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS :=
  isBUGStep_iff.2 ⟨hs, hεK, hεL⟩

/-- Non-vacuity of `BasisUpdate` and `IsBUGStepCore`: for the constant field `F (t, Y) = c` and
the identity projectors, all substeps are the straight line `t ↦ Y₀ + (t - t₀) • c`. (Steps with
projectors of low rank for a matrix differential equation are constructed in
`LeanDLRA/Integrators/Matrix/BUGRun.lean`.) -/
example (c Y₀ : E) (t₀ t₁ : ℝ) :
    IsBUGStepCore (fun _ _ => c) 1 1 1 1 t₀ t₁ Y₀ (fun t => Y₀ + (t - t₀) • c)
      (fun t => Y₀ + (t - t₀) • c) (fun t => Y₀ + (t - t₀) • c) := by
  have hsol : ODESolution (fun _ _ => c) (fun t => Y₀ + (t - t₀) • c) t₀ t₁ := by
    refine ⟨(continuous_const.add
      ((continuous_id.sub continuous_const).smul continuous_const)).continuousOn, fun t _ => ?_⟩
    have h := (((hasDerivAt_id t).sub_const t₀).smul_const c).const_add Y₀
    rw [one_smul] at h
    exact h.hasDerivWithinAt
  have h₀ : (fun t : ℝ => Y₀ + (t - t₀) • c) t₀ = Y₀ := by simp
  exact isBUGStepCore_iff.2 ⟨basisUpdate_two_iff.2 ⟨⟨.one, .one⟩, ⟨.one, .one⟩, fun _ => rfl,
    ⟨hsol, hsol⟩, ⟨h₀, h₀⟩, rfl, rfl⟩, hsol, h₀⟩

/-! ### The Tucker BUG step -/

/-- The Tucker BUG step `IsTuckerBUGStep` is a basis update for `d` modes, the normal bounds at
the results of the substeps, and the Galerkin step in the common range of the new projectors. -/
theorem isTuckerBUGStep_iff {ε : ℝ} {d : ℕ} {Q₀ P₁ : Fin d → E →L[ℝ] E} {YK : Fin d → ℝ → E} :
    IsTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS ↔
      BasisUpdate F Q₀ P₁ t₀ t₁ Y₀ YK ∧
        (∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁ i) ((1 - Q₀ i) (F t (YK i t₁)))‖ ≤ ε) ∧
        ODESolution (fun t x => modeProd P₁ (F t x)) YS t₀ t₁ ∧ YS t₀ = modeProd P₁ Y₀ :=
  ⟨fun hs => ⟨⟨hs.projQ₀, hs.projP₁, hs.comm₁, hs.kSol, hs.kStart, hs.kCap⟩, hs.kNormal,
      hs.sSol, hs.sStart⟩,
    fun ⟨hb, hN, hS, hS₀⟩ =>
      ⟨hb.projQ₀, hb.projP₁, hb.comm₁, hb.kSol, hb.kStart, hb.kCap, hN, hS, hS₀⟩⟩

/-- For two modes the Tucker BUG step is the matrix BUG step `IsBUGStep`. -/
theorem isTuckerBUGStep_two_iff {ε : ℝ} :
    IsTuckerBUGStep F ε ![Q₀, P₀] ![P₁, Q₁] t₀ t₁ Y₀ ![YK, YL] YS ↔
      IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS := by
  refine ⟨fun hs => ?_, IsBUGStep.toTucker⟩
  have hS := hs.sSol
  have hS₀ := hs.sStart
  rw [modeProd_two] at hS hS₀
  exact ⟨hs.projQ₀ 1, hs.projQ₀ 0, hs.projP₁ 0, hs.projP₁ 1, hs.comm₁ 0 1, hs.kSol 0,
    hs.kStart 0, hs.kCap 0, hs.kNormal 0, hs.kSol 1, hs.kStart 1, hs.kCap 1, hs.kNormal 1, hS, hS₀⟩

/-! ### The local error for a globally Lipschitz and bounded field -/

/-- **Local error of a BUG step** [CerutiLubich2022, Lemma 4]. Let `F` be `L`-Lipschitz and
bounded by `B`, and let the part of `F` that is normal to the low-rank manifold be at most `ε` at
the results `YK t₁` and `YL t₁` of the basis update. Then the result `YS t₁` of a step from
`(t₀, Y₀)` to `t₁` with `t₁ - t₀ ≤ H` differs from the exact solution through `(t₀, Y₀)` by at
most `(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))` with `c₁ = bugC₁ L H` and `c₂ = bugC₂ L B H`. The bound
does not depend on the singular values of `Y₀`. -/
theorem IsBUGStepCore.hasLocalError {L B ε H : ℝ}
    (hs : IsBUGStepCore F P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS)
    (hεK : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε)
    (hεL : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (h01 : t₀ ≤ t₁)
    (hH : t₁ - t₀ ≤ H) :
    HasLocalError F t₀ t₁ Y₀ (YS t₁)
      ((t₁ - t₀) * (bugC₁ L H * ε + bugC₂ L B H * (t₁ - t₀))) :=
  fun _ hΦ hΦ₀ => (hs.isBUGStep hεK hεL).local_error_le hF hL hB (by ring) (sub_nonneg.2 h01) hH
    hΦ hΦ₀

/-- The local error bound `IsBUGStep.local_error_le` of `LeanDLRA/Integrators/BUG.lean` is
`IsBUGStepCore.hasLocalError` for the step size `h = t₁ - t₀`. -/
example {L B ε h H : ℝ} {A : ℝ → E} (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤ h * (bugC₁ L H * ε + bugC₂ L B H * h) := by
  have e : t₁ - t₀ = h := by rw [ht₁]; ring
  have key := hs.isBUGStepCore.hasLocalError (H := H) hs.kNormal hs.lNormal hF hL hB
    (by linarith) (by rw [e]; exact hhH) A hA hA₀
  rwa [e] at key

/-! ### Steps near a reference solution

In the error analysis the field `F` is Lipschitz and bounded only on the tube
`{(t, x) | t ∈ [a, b], ‖x - A t‖ ≤ ρ}` around a reference solution `A`. The following estimates
show that all substeps of a step stay in the tube when the start value lies well inside it. They
are stated for a field that is bounded on the tube, so they apply to `F` and to its tube extension
`tubeExt F A a b ρ`. -/

section Near

variable {A : ℝ → E} {a b ρ B : ℝ}

section Basis

variable {ι : Type*} {Q₀ P₁ : ι → E →L[ℝ] E} {YK : ι → ℝ → E}

/-- A basis update for the tube extension of `F` whose substeps stay in the tube is a basis update
for `F`, and conversely. -/
theorem basisUpdate_tubeExt_iff (ha : a ≤ t₀) (hb : t₁ ≤ b)
    (hK : ∀ i, ∀ t ∈ Ico t₀ t₁, ‖YK i t - A t‖ ≤ ρ) :
    BasisUpdate (tubeExt F A a b ρ) Q₀ P₁ t₀ t₁ Y₀ YK ↔ BasisUpdate F Q₀ P₁ t₀ t₁ Y₀ YK := by
  have e : ∀ i, ODESolution (fun t x => Q₀ i (tubeExt F A a b ρ t x)) (YK i) t₀ t₁ ↔
      ODESolution (fun t x => Q₀ i (F t x)) (YK i) t₀ t₁ :=
    fun i => odeSolution_comp_tubeExt_iff (fun x => Q₀ i x) ha hb (hK i)
  exact ⟨fun hs => ⟨hs.projQ₀, hs.projP₁, hs.comm₁, fun i => (e i).1 (hs.kSol i), hs.kStart,
      hs.kCap⟩,
    fun hs => ⟨hs.projQ₀, hs.projP₁, hs.comm₁, fun i => (e i).2 (hs.kSol i), hs.kStart, hs.kCap⟩⟩

/-- If the start value satisfies `‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, every substep of a basis
update stays strictly inside the tube of radius `ρ` around `A`. -/
theorem BasisUpdate.norm_sub_lt_of_near (hs : BasisUpdate F Q₀ P₁ t₀ t₁ Y₀ YK)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) (i : ι) :
    ∀ t ∈ Icc t₀ t₁, ‖YK i t - A t‖ < ρ := by
  intro t ht
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 (ht.1.trans ht.2))
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (Y₀ - A t₀)]
  exact tube_trap hA (hs.kSol i) hB hB (hFB.along hρ ha hb)
    (hFB.comp_proj ha hb (fun x => Q₀ i x) (hs.projQ₀ i).norm_le)
    (by rw [hs.kStart]; linarith) t ht

/-- Under the hypotheses of `BasisUpdate.norm_sub_lt_of_near` the result of every substep differs
from the start value by at most `B (t₁ - t₀)`. -/
theorem BasisUpdate.norm_sub_start_le_of_near (hs : BasisUpdate F Q₀ P₁ t₀ t₁ Y₀ YK)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) (i : ι) :
    ‖YK i t₁ - Y₀‖ ≤ B * (t₁ - t₀) := by
  have h := (hs.kSol i).norm_sub_start_le_of_tube
    (hFB.comp_proj ha hb (fun x => Q₀ i x) (hs.projQ₀ i).norm_le)
    (hs.norm_sub_lt_of_near hFB hB ha hb hA hsmall i) t₁ ⟨h01, le_rfl⟩
  rwa [hs.kStart] at h

/-- Under the hypotheses of `BasisUpdate.norm_sub_lt_of_near` the result `YK i t₁` of every
substep stays within `‖Y₀ - A t₀‖ + 2 B (t₁ - t₀)` of `A t` for all times `t` of the step. -/
theorem BasisUpdate.norm_sub_le_of_near (hs : BasisUpdate F Q₀ P₁ t₀ t₁ Y₀ YK)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) (i : ι) :
    ∀ t ∈ Icc t₀ t₁, ‖YK i t₁ - A t‖ ≤ ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) := by
  intro t ht
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (Y₀ - A t₀)]
  have h₁ := hs.norm_sub_start_le_of_near hFB hB ha hb h01 hA hsmall i
  have h₂ := hA.norm_sub_le (hFB.along hρ ha hb) t ht
  have h₃ : B * (t - t₀) ≤ B * (t₁ - t₀) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 t₀) hB
  have e : YK i t₁ - A t = (YK i t₁ - Y₀) + (Y₀ - A t₀) - (A t - A t₀) := by abel
  rw [e]
  have h₄ := norm_sub_le ((YK i t₁ - Y₀) + (Y₀ - A t₀)) (A t - A t₀)
  have h₅ := norm_add_le (YK i t₁ - Y₀) (Y₀ - A t₀)
  linarith

/-- Under the hypotheses of `BasisUpdate.norm_sub_lt_of_near` the result of every substep lies in
the tube at all times of the step. These are the points at which the error analysis evaluates the
normal part of `F`. -/
theorem BasisUpdate.mem_tubeSet_of_near (hs : BasisUpdate F Q₀ P₁ t₀ t₁ Y₀ YK)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) (i : ι) :
    ∀ t ∈ Icc t₀ t₁, (t, YK i t₁) ∈ tubeSet A a b ρ :=
  fun t ht => ⟨⟨ha.trans ht.1, ht.2.trans hb⟩,
    (hs.norm_sub_le_of_near hFB hB ha hb h01 hA hsmall i t ht).trans hsmall.le⟩

/-- Under the hypotheses of `BasisUpdate.norm_sub_lt_of_near` the new projector of every mode
captures the start value up to `B (t₁ - t₀)`. -/
theorem BasisUpdate.norm_one_sub_apply_le_of_near (hs : BasisUpdate F Q₀ P₁ t₀ t₁ Y₀ YK)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) (i : ι) :
    ‖(1 - P₁ i) Y₀‖ ≤ B * (t₁ - t₀) := by
  have e : (1 - P₁ i) Y₀ = (Y₀ - YK i t₁) - P₁ i (Y₀ - YK i t₁) := by
    rw [map_sub, hs.kCap]; simp
  rw [e]
  refine ((hs.projP₁ i).norm_sub_le _).trans ?_
  rw [norm_sub_rev]
  exact hs.norm_sub_start_le_of_near hFB hB ha hb h01 hA hsmall i

end Basis

/-- A BUG step for the tube extension of `F` whose three substeps stay in the tube is a BUG step
for `F`, and conversely. -/
theorem isBUGStepCore_tubeExt_iff (ha : a ≤ t₀) (hb : t₁ ≤ b)
    (hK : ∀ t ∈ Ico t₀ t₁, ‖YK t - A t‖ ≤ ρ) (hL : ∀ t ∈ Ico t₀ t₁, ‖YL t - A t‖ ≤ ρ)
    (hS : ∀ t ∈ Ico t₀ t₁, ‖YS t - A t‖ ≤ ρ) :
    IsBUGStepCore (tubeExt F A a b ρ) P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS ↔
      IsBUGStepCore F P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS := by
  have hKL : ∀ i, ∀ t ∈ Ico t₀ t₁, ‖![YK, YL] i t - A t‖ ≤ ρ := Fin.forall_fin_two.2 ⟨hK, hL⟩
  exact isBUGStepCore_iff.trans <| ((basisUpdate_tubeExt_iff ha hb hKL).and
    ((odeSolution_comp_tubeExt_iff (fun x => P₁ (Q₁ x)) ha hb hS).and Iff.rfl)).trans
    isBUGStepCore_iff.symm

/-- If the start value satisfies `‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, the start value
`P₁ (Q₁ Y₀)` of the Galerkin step is within `‖Y₀ - A t₀‖ + 2 B (t₁ - t₀)` of `A t₀`. -/
theorem IsBUGStepCore.norm_start_sub_le_of_near
    (hs : IsBUGStepCore F P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    ‖P₁ (Q₁ Y₀) - A t₀‖ ≤ ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) := by
  have hP₁ : IsOrthProj P₁ := hs.projP₁ 0
  have hcP : ‖(1 - P₁) Y₀‖ ≤ B * (t₁ - t₀) :=
    hs.toBasisUpdate.norm_one_sub_apply_le_of_near hFB hB ha hb h01 hA hsmall 0
  have hcQ : ‖(1 - Q₁) Y₀‖ ≤ B * (t₁ - t₀) :=
    hs.toBasisUpdate.norm_one_sub_apply_le_of_near hFB hB ha hb h01 hA hsmall 1
  have h₁ := norm_sub_apply_apply_le (Q := Q₁) hP₁ Y₀
  have e : P₁ (Q₁ Y₀) - A t₀ = (Y₀ - A t₀) - (Y₀ - P₁ (Q₁ Y₀)) := by abel
  rw [e]
  have h₂ := norm_sub_le (Y₀ - A t₀) (Y₀ - P₁ (Q₁ Y₀))
  linarith

/-- If the start value satisfies `‖Y₀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, the Galerkin step of a BUG
step stays strictly inside the tube of radius `ρ` around `A`. -/
theorem IsBUGStepCore.norm_galerkin_sub_lt_of_near
    (hs : IsBUGStepCore F P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    ∀ t ∈ Icc t₀ t₁, ‖YS t - A t‖ < ρ := by
  intro t ht
  have h01 : t₀ ≤ t₁ := ht.1.trans ht.2
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (Y₀ - A t₀)]
  have hP₁ : IsOrthProj P₁ := hs.projP₁ 0
  have hQ₁ : IsOrthProj Q₁ := hs.projP₁ 1
  have hS₀ := hs.norm_start_sub_le_of_near hFB hB ha hb h01 hA (by linarith)
  exact tube_trap hA hs.sSol hB hB (hFB.along hρ ha hb)
    (hFB.comp_proj ha hb (fun x => P₁ (Q₁ x)) fun x => (hP₁.norm_le _).trans (hQ₁.norm_le x))
    (by rw [hs.sStart]; linarith) t ht

/-- **Steps for the tube extension are steps for `F`.** Let `F` be bounded by `B` on the tube of
radius `ρ` around a solution `A`, and let the start value satisfy
`‖Y₀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`. Then all substeps of a BUG step stay in the tube, for `F` and
for its tube extension, so that the two fields have the same BUG steps. -/
theorem isBUGStepCore_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    IsBUGStepCore (tubeExt F A a b ρ) P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS ↔
      IsBUGStepCore F P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS := by
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (Y₀ - A t₀)]
  have h2 : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ := by linarith
  have key : ∀ G : ℝ → E → E, IsBoundedOnTube G A a b ρ B → ODESolution G A t₀ t₁ →
      IsBUGStepCore G P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS →
      (∀ t ∈ Ico t₀ t₁, ‖YK t - A t‖ ≤ ρ) ∧ (∀ t ∈ Ico t₀ t₁, ‖YL t - A t‖ ≤ ρ) ∧
        ∀ t ∈ Ico t₀ t₁, ‖YS t - A t‖ ≤ ρ := fun G hGB hGA hs =>
    ⟨fun t ht => (hs.toBasisUpdate.norm_sub_lt_of_near hGB hB ha hb hGA h2 0 t
        (Ico_subset_Icc_self ht)).le,
      fun t ht => (hs.toBasisUpdate.norm_sub_lt_of_near hGB hB ha hb hGA h2 1 t
        (Ico_subset_Icc_self ht)).le,
      fun t ht => (hs.norm_galerkin_sub_lt_of_near hGB hB ha hb hGA hsmall t
        (Ico_subset_Icc_self ht)).le⟩
  constructor
  · intro hs
    obtain ⟨hK, hL, hS⟩ := key _ ((isBoundedField_tubeExt hFB hB hρ).isBoundedOnTube A a b ρ)
      ((odeSolution_tubeExt_iff ha hb fun t _ => by simpa using hρ).2 hA) hs
    exact (isBUGStepCore_tubeExt_iff ha hb hK hL hS).1 hs
  · intro hs
    obtain ⟨hK, hL, hS⟩ := key F hFB hA hs
    exact (isBUGStepCore_tubeExt_iff ha hb hK hL hS).2 hs

/-- The statement of `isBUGStepCore_tubeExt_iff_of_near` for steps with normal bounds: the
results of the K-step and of the L-step lie in the tube, where `F` and its tube extension agree,
so the normal bounds for the two fields are the same. -/
theorem isBUGStep_tubeExt_iff_of_near {ε : ℝ} (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    IsBUGStep (tubeExt F A a b ρ) ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS ↔
      IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS := by
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have h2 : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ := by linarith
  rw [isBUGStep_iff, isBUGStep_iff, isBUGStepCore_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall]
  refine and_congr_right fun hs => ?_
  have hK := hs.toBasisUpdate.mem_tubeSet_of_near hFB hB ha hb h01 hA h2 0
  have hL := hs.toBasisUpdate.mem_tubeSet_of_near hFB hB ha hb h01 hA h2 1
  have eK : ∀ t ∈ Icc t₀ t₁, tubeExt F A a b ρ t (YK t₁) = F t (YK t₁) :=
    fun t ht => tubeExt_eq (hK t ht).1 (hK t ht).2
  have eL : ∀ t ∈ Icc t₀ t₁, tubeExt F A a b ρ t (YL t₁) = F t (YL t₁) :=
    fun t ht => tubeExt_eq (hL t ht).1 (hL t ht).2
  exact and_congr (forall₂_congr fun t ht => by rw [eK t ht])
    (forall₂_congr fun t ht => by rw [eL t ht])

/-- The conversion `IsBUGStep.tubeExt` of `LeanDLRA/Foundations/Localization.lean` is one
direction of `isBUGStep_tubeExt_iff_of_near`. -/
example {ε h : ℝ} (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (hh : 0 ≤ h) (ha : a ≤ t₀) (hb : t₁ ≤ b)
    (ht₁ : t₁ = t₀ + h) (hA : ODESolution F A t₀ t₁) (hsmall : ‖Y₀ - A t₀‖ + 4 * B * h < ρ) :
    IsBUGStep (tubeExt F A a b ρ) ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS :=
  (isBUGStep_tubeExt_iff_of_near hFB hB ha hb (by linarith) hA
    (by rw [show t₁ - t₀ = h by rw [ht₁]; ring]; exact hsmall)).2 hs

/-- **Local error of a BUG step near a reference solution.** Let `F` be `L`-Lipschitz and bounded
by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`, let the step from
`(t₀, Y₀)` to `t₁` lie in `[a, b]` with `t₁ - t₀ ≤ H`, and let the start value satisfy
`‖Y₀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`. If the normal part of `F` is at most `ε` at the results
`YK t₁`, `YL t₁` of the basis update, then the result `YS t₁` differs from the exact solution
through `(t₀, Y₀)` by at most `(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))` with `c₁ = bugC₁ L H` and
`c₂ = bugC₂ L B H`. Nothing is assumed about `F` outside the tube. -/
theorem IsBUGStepCore.hasLocalError_of_tube {L ε H : ℝ}
    (hs : IsBUGStepCore F P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS)
    (hεK : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε)
    (hεL : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hH : t₁ - t₀ ≤ H)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ (YS t₁)
      ((t₁ - t₀) * (bugC₁ L H * ε + bugC₂ L B H * (t₁ - t₀))) := by
  intro Φ hΦ hΦ₀
  have hh : 0 ≤ t₁ - t₀ := sub_nonneg.2 h01
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB hh
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (Y₀ - A t₀)]
  have ht₁ : t₁ = t₀ + (t₁ - t₀) := by ring
  have hΦG : ODESolution (tubeExt F A a b ρ) Φ t₀ t₁ :=
    hΦ.tubeExt_of_near hFB hB hh ha hb ht₁ hA (by rw [hΦ₀]; linarith)
  exact ((isBUGStep_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).2
    (hs.isBUGStep hεK hεL)).local_error_le (isLipschitzField_tubeExt hFL hL hρ) hL
    (isBoundedField_tubeExt hFB hB hρ) ht₁ hh hH hΦG hΦ₀

end Near

end LeanDLRA
