import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Integrators.MethodTolerance
import LeanDLRA.Integrators.Matrix.BUGStep
import LeanDLRA.Integrators.Matrix.ParallelBUGStep

/-!
# The augmented BUG step as step relations: truncation by a tolerance or to a fixed rank

This file states the rank-adaptive basis-update & Galerkin (BUG) integrator of Ceruti, Kusch and
Lubich (arXiv:2104.05247) for matrices as relations between the old value `Y₀` and the value `Y₁`
after one step (`StepRel`), and gives the local error of a step near a reference solution. The
step at the level of the factors is `MatrixBUG.IsRankAdaptiveStep` of
`LeanDLRA/Integrators/Matrix/BUG.lean`. Its error analysis at the level of orthogonal projectors
is in `LeanDLRA/Integrators/BUGCore.lean` and `LeanDLRA/Integrators/RankAdaptiveBUG.lean`; the
local errors of this file are taken from there. Runs of the integrator with truncation to a
fixed rank are in `LeanDLRA/Integrators/Matrix/TruncBUGRun.lean`.

**The step.** Let `Y₀ = U₀ S₀ V₀ᵀ` with `r` orthonormal columns in `U₀` and in `V₀`. The K-step
and the L-step are those of the fixed-rank BUG integrator. The bases `Û`, `V̂` after the step are
augmented: the range of `Û` contains the columns of `K(t₁)` and of `U₀`, the range of `V̂` those
of `L(t₁)` and of `V₀`, and each has at most `2 r` columns. The Galerkin step in these bases
gives the augmented matrix `Ŷ = Û Ŝ(t₁) V̂ᵀ`, of rank at most `2 r`. Then `Ŷ` is truncated. The
file has one relation for the step up to here and one for each of two ways to truncate:

* by a tolerance: `‖Y₁ - Ŷ‖ ≤ ϑ`, with no condition on the rank of `Y₁` (the rank-adaptive
  integrator);
* to the rank `r` of the start value: `Y₁` has rank at most `r` and
  `‖Y₁ - Ŷ‖ ≤ κ · dist(Ŷ, matrices of rank ≤ r)` (the integrator with a fixed rank that uses the
  augmented bases; `κ = 1` is a best approximation).

The relations contain the algorithm only. The size `ε` of the normal part of the vector field,
the Lipschitz constant and the bound of the field are hypotheses of the error theorems.

## Main definitions

* `MatrixBUG.augmentedRel F r`: the step without truncation. `augmentedRel F r t₀ t₁ Y₀ Ŷ` says
  that `Ŷ = Û Ŝ(t₁) V̂ᵀ` for a step `MatrixBUG.IsRankAdaptiveStep` started from some
  factorization `Y₀ = U₀ S₀ V₀ᵀ` with `r` orthonormal columns, where `Û` and `V̂` have at most
  `2 r` columns.
* `MatrixBUG.adaptiveStepRel F R ϑ`: the step with truncation by the tolerance `ϑ`. The start
  value is factored with `r` columns for some `r` in the set `R`.
* `MatrixBUG.truncStepRel F r κ`: the step with truncation to rank `r` by an approximation that
  is best up to the factor `κ`.

## Main results

* `MatrixBUG.IsRankAdaptiveStep.isBUGStepCore`: a factor step is a step of the BUG integrator
  for orthogonal projectors (`IsBUGStepCore`), without any bound on the field.
* `MatrixBUG.isRankAdaptiveStep_tubeExt_iff_of_near` and the same for the three relations: if
  `‖Y₀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, the tube extension `tubeExt F A a b ρ` has the same steps
  as `F`.
* `MatrixBUG.exists_isRankAdaptiveStep_of_lipschitz`, `MatrixBUG.exists_augmentedRel`: a step
  exists for every Lipschitz field that is continuous in time on the step interval. The field
  need not be bounded, and `2 r` may exceed the numbers of rows and columns.
* `MatrixBUG.exists_adaptiveStepRel_Ici`: with `R = Set.Ici r₀`, `r₀ ≤ m`, `r₀ ≤ n`, a step
  with truncation by a tolerance `ϑ ≥ 0` exists from every matrix.
* `MatrixBUG.exists_truncStepRel`: for `κ ≥ 1` a step with truncation to rank `r` exists from
  every matrix of rank at most `r`.
* `MatrixBUG.augmentedRel.adaptiveStepRel_truncation`,
  `MatrixBUG.augmentedRel.truncStepRel_truncation`: the truncated singular value decomposition
  is a truncation of either kind.
* `MatrixBUG.augmentedRel.hasLocalError_of_tube`: the step without truncation has local error
  `(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))` with `c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`.
* `MatrixBUG.adaptiveStepRel.hasLocalError_of_tube`: with a tolerance, the local error is
  `(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀)) + ϑ`.
* `MatrixBUG.truncStepRel.hasLocalError_of_tube`: with truncation to rank `r`, the local error
  is `(t₁ - t₀) (κ (10 L B (t₁ - t₀) + ε) + (1 + κ) (c₁ ε + c₂ (t₁ - t₀)))`. No tolerance
  appears.

## Implementation notes

The bound on the normal part of the field, `FactoredNormalBoundOn F r D ε`, concerns
factorizations with exactly `r` columns, and a bound for one number of columns is not used here
to obtain a bound for another. A step of the rank-adaptive integrator may start from a
factorization with any number of columns. Therefore `MatrixBUG.adaptiveStepRel` carries the set
`R` of the numbers of columns that a step may start from, and the error theorem asks for the
bound at every `r ∈ R`, with one `ε` for all of them. For `R = Set.Ici r₀` every matrix is a
start value: a factorization of `Y₀` is padded to `max (rank Y₀) r₀` columns. This needs
`r₀ ≤ m` and `r₀ ≤ n`, because a matrix with `m` rows has at most `m` orthonormal columns
(`MatrixBUG.augmentedRel.le_card_left`, `MatrixBUG.augmentedRel.le_card_right`); for a larger
`r₀` the relation is empty. A set such as `Set.Icc r₀ r₁` gives the integrator with a cap on
the rank of the start value (`MatrixBUG.adaptiveStepRel.mono`).

The truncation clauses contain every truncation with the stated property, not only the one an
implementation uses. The existence of a step is therefore a weak statement for the relation
with a tolerance (the augmented matrix itself is a witness); the error bounds hold for every
step of the relations, in particular for the truncated singular value decomposition.

`MatrixBUG.IsRankAdaptiveStep` allows augmented bases with any index types. In
`MatrixBUG.augmentedRel` they have at most `2 r` columns, as in the algorithm, which gives the
rank bound `MatrixBUG.augmentedRel.rank_le`. The error theorems for the factor step do not use
this cap.

The margin `4 B (t₁ - t₀)` is that of the fixed-rank BUG integrator: `2 B (t₁ - t₀)` for the K-
and L-step and as much again for the Galerkin step. The truncation does not evaluate the field.

The constants of the truncation to rank `r`: the exact solution through a matrix of rank at
most `r` is within `(t₁ - t₀) (10 L B (t₁ - t₀) + ε)` of the matrices of rank at most `r` after
one step (`distLR_flow_le_of_tube`), and a truncation that is best up to the factor `κ` costs
`κ` times this distance plus `1 + κ` times the error before truncation (`norm_trunc_sub_le`).
Joint continuity of `F` on the tube is needed for the distance only.

## References

* G. Ceruti, J. Kusch, Ch. Lubich, *A rank-adaptive robust integrator for dynamical low-rank
  approximation*, arXiv:2104.05247 (BIT Numer. Math. 2022).
* G. Ceruti, Ch. Lubich, *An unconventional robust integrator for dynamical low-rank
  approximation*, arXiv:2010.02022 (BIT Numer. Math. 2022), for the K-, L- and S-step.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixBUG

/-! ### The factor step and the BUG step for orthogonal projectors -/

section Factor

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k'] [DecidableEq k]
  [DecidableEq k'] {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {ϑ t₀ t₁ : ℝ}
  {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {Ua : Matrix m k ℝ} {Va : Matrix n k' ℝ} {K : ℝ → Matrix m (Fin r) ℝ}
  {Lf : ℝ → Matrix n (Fin r) ℝ} {Sa : ℝ → Matrix k k' ℝ} {Y₁ : Matrix m n ℝ}

/-- **A rank-adaptive factor step is a BUG step for orthogonal projectors.** The full-space
trajectories `K(t) V₀ᵀ`, `U₀ L(t)ᵀ`, `Û Ŝ(t) V̂ᵀ` of a factor step form a step of the abstract
integrator (`IsBUGStepCore`) for the projections `P₀ = leftProj U₀`, `Q₀ = rightProj V₀`,
`P₁ = leftProj Û`, `Q₁ = rightProj V̂`. No bound on the field is needed, and the truncation
plays no role. -/
theorem IsRankAdaptiveStep.isBUGStepCore
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁) :
    IsBUGStepCore F (leftProj U₀) (rightProj V₀) (leftProj Ua) (rightProj Va) t₀ t₁
      (U₀ * S₀ * V₀ᵀ) (fun t => K t * V₀ᵀ) (fun t => U₀ * (Lf t)ᵀ)
      (fun t => Ua * Sa t * Vaᵀ) := by
  have hk₀ : K t₀ * V₀ᵀ = U₀ * S₀ * V₀ᵀ := by rw [hs.kStart]
  have hl₀ : U₀ * (Lf t₀)ᵀ = U₀ * S₀ * V₀ᵀ := by
    rw [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hkc : leftProj Ua (K t₁ * V₀ᵀ) = K t₁ * V₀ᵀ := by
    rw [leftProj_apply, ← Matrix.mul_assoc, hs.kCap]
  have hlc : rightProj Va (U₀ * (Lf t₁)ᵀ) = U₀ * (Lf t₁)ᵀ := by
    have hT : (Lf t₁)ᵀ * Va * Vaᵀ = (Lf t₁)ᵀ := by
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hs.lCap
    rw [rightProj_apply, Matrix.mul_assoc U₀, Matrix.mul_assoc U₀, hT]
  exact isBUGStepCore_iff.2 ⟨basisUpdate_two_iff.2
    ⟨⟨isOrthProj_rightProj hs.orthV₀, isOrthProj_leftProj hs.orthU₀⟩,
      ⟨isOrthProj_leftProj hs.orthUa, isOrthProj_rightProj hs.orthVa⟩,
      leftProj_rightProj_comm Ua Va, ⟨odeSolution_kField hs.kSol, odeSolution_lField hs.lSol⟩,
      ⟨hk₀, hl₀⟩, hkc, hlc⟩,
    odeSolution_sField hs.sSol, hs.ys_start⟩

/-- **The step without its truncation.** Every rank-adaptive factor step gives a step with
tolerance `0` whose result is the augmented matrix `Û Ŝ(t₁) V̂ᵀ`. -/
theorem IsRankAdaptiveStep.augmented
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁) :
    IsRankAdaptiveStep F 0 t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa (Ua * Sa t₁ * Vaᵀ) :=
  ⟨hs.orthU₀, hs.orthV₀, hs.kSol, hs.kStart, hs.lSol, hs.lStart, hs.orthUa, hs.kCap, hs.augU,
    hs.orthVa, hs.lCap, hs.augV, hs.sSol, hs.sStart, by simp⟩

section Tube

variable {A : ℝ → Matrix m n ℝ} {a b ρ B : ℝ}

/-- **A step for the tube extension is a step for the field, if the step stays in the tube.**
The tube extension `tubeExt F A a b ρ` agrees with `F` on the tube of radius `ρ` around `A` over
`[a, b]`. If the three full-space trajectories of a rank-adaptive factor step over
`[t₀, t₁] ⊆ [a, b]` stay in the tube, it does not matter which of the two fields drives the
step. -/
theorem isRankAdaptiveStep_tubeExt_iff (ha : a ≤ t₀) (hb : t₁ ≤ b)
    (hK : ∀ t ∈ Ico t₀ t₁, ‖K t * V₀ᵀ - A t‖ ≤ ρ)
    (hLf : ∀ t ∈ Ico t₀ t₁, ‖U₀ * (Lf t)ᵀ - A t‖ ≤ ρ)
    (hS : ∀ t ∈ Ico t₀ t₁, ‖Ua * Sa t * Vaᵀ - A t‖ ≤ ρ) :
    IsRankAdaptiveStep (tubeExt F A a b ρ) ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁ ↔
      IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁ := by
  have hmem : ∀ t ∈ Ico t₀ t₁, t ∈ Icc a b := fun t ht => ⟨ha.trans ht.1, ht.2.le.trans hb⟩
  have ek : ∀ t ∈ Ico t₀ t₁, kField V₀ (tubeExt F A a b ρ) t (K t) = kField V₀ F t (K t) :=
    fun t ht => by simp only [kField, tubeExt_eq (hmem t ht) (hK t ht)]
  have el : ∀ t ∈ Ico t₀ t₁, lField U₀ (tubeExt F A a b ρ) t (Lf t) = lField U₀ F t (Lf t) :=
    fun t ht => by simp only [lField, tubeExt_eq (hmem t ht) (hLf t ht)]
  have es : ∀ t ∈ Ico t₀ t₁,
      sField Ua Va (tubeExt F A a b ρ) t (Sa t) = sField Ua Va F t (Sa t) :=
    fun t ht => by simp only [sField, tubeExt_eq (hmem t ht) (hS t ht)]
  exact ⟨fun h => ⟨h.orthU₀, h.orthV₀, h.kSol.congr_field ek, h.kStart, h.lSol.congr_field el,
      h.lStart, h.orthUa, h.kCap, h.augU, h.orthVa, h.lCap, h.augV, h.sSol.congr_field es,
      h.sStart, h.trunc⟩,
    fun h => ⟨h.orthU₀, h.orthV₀, h.kSol.congr_field fun t ht => (ek t ht).symm, h.kStart,
      h.lSol.congr_field fun t ht => (el t ht).symm, h.lStart, h.orthUa, h.kCap, h.augU,
      h.orthVa, h.lCap, h.augV, h.sSol.congr_field fun t ht => (es t ht).symm, h.sStart,
      h.trunc⟩⟩

/-- **Near the reference solution, the tube extension has the same steps as the field.** Let `F`
be bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`, and let
`[t₀, t₁] ⊆ [a, b]`. If the start value satisfies `‖U₀ S₀ V₀ᵀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, then
every rank-adaptive factor step for either field stays in the tube, so the steps for
`tubeExt F A a b ρ` are exactly the steps for `F`. -/
theorem isRankAdaptiveStep_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    IsRankAdaptiveStep (tubeExt F A a b ρ) ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁ ↔
      IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁ := by
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (U₀ * S₀ * V₀ᵀ - A t₀)]
  have h2 : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ := by linarith
  have key : ∀ G : ℝ → Matrix m n ℝ → Matrix m n ℝ, IsBoundedOnTube G A a b ρ B →
      ODESolution G A t₀ t₁ → IsRankAdaptiveStep G ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁ →
      (∀ t ∈ Ico t₀ t₁, ‖K t * V₀ᵀ - A t‖ ≤ ρ) ∧ (∀ t ∈ Ico t₀ t₁, ‖U₀ * (Lf t)ᵀ - A t‖ ≤ ρ) ∧
        ∀ t ∈ Ico t₀ t₁, ‖Ua * Sa t * Vaᵀ - A t‖ ≤ ρ := fun G hGB hGA hs =>
    ⟨fun t ht => (hs.isBUGStepCore.toBasisUpdate.norm_sub_lt_of_near hGB hB ha hb hGA h2 0 t
        (Ico_subset_Icc_self ht)).le,
      fun t ht => (hs.isBUGStepCore.toBasisUpdate.norm_sub_lt_of_near hGB hB ha hb hGA h2 1 t
        (Ico_subset_Icc_self ht)).le,
      fun t ht => (hs.isBUGStepCore.norm_galerkin_sub_lt_of_near hGB hB ha hb hGA hsmall t
        (Ico_subset_Icc_self ht)).le⟩
  constructor
  · intro hs
    obtain ⟨hK, hLf, hS⟩ := key _ ((isBoundedField_tubeExt hFB hB hρ).isBoundedOnTube A a b ρ)
      ((odeSolution_tubeExt_iff ha hb fun t _ => by simpa using hρ).2 hA) hs
    exact (isRankAdaptiveStep_tubeExt_iff ha hb hK hLf hS).1 hs
  · intro hs
    obtain ⟨hK, hLf, hS⟩ := key F hFB hA hs
    exact (isRankAdaptiveStep_tubeExt_iff ha hb hK hLf hS).2 hs

end Tube

end Factor

/-! ### Normal bounds and the local error of the factor step -/

section FactorError

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k'] [DecidableEq k]
  [DecidableEq k'] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {ϑ t₀ t₁ : ℝ} {U₀ : Matrix m (Fin r) ℝ}
  {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {Ua : Matrix m k ℝ}
  {Va : Matrix n k' ℝ} {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ}
  {Sa : ℝ → Matrix k k' ℝ} {Y₁ : Matrix m n ℝ} {L B ε H : ℝ}

/-- **Normal bound at the result of the K-step, augmented basis.** The result `K(t₁) V₀ᵀ` of the
K-step has a factorization `U' (U'ᵀ K(t₁)) V₀ᵀ` with `r` orthonormal columns `U'` inside the
range of `Û` (`IsRankAdaptiveStep.exists_kBasis`). Hence a bound `ε` for the normal part of `F`
at factored points with `r` columns of a region `D` applies to it, with the larger projector
`Û Ûᵀ` in place of `U' U'ᵀ`, whenever `(t, K(t₁) V₀ᵀ)` lies in `D`. -/
theorem IsRankAdaptiveStep.norm_kNormal_le {D : Set (ℝ × Matrix m n ℝ)}
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    (hε : FactoredNormalBoundOn F r D ε) {t : ℝ} (hmem : (t, K t₁ * V₀ᵀ) ∈ D) :
    ‖(1 - Ua * Uaᵀ) * F t (K t₁ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε := by
  obtain ⟨U', hU', hcap, hin⟩ := hs.exists_kBasis
  have hK : K t₁ * V₀ᵀ = U' * (U'ᵀ * K t₁) * V₀ᵀ := by rw [← Matrix.mul_assoc, hcap]
  have h := hε t U' V₀ (U'ᵀ * K t₁) hU' hs.orthV₀ (by rwa [← hK])
  rw [← hK] at h
  exact (norm_normal_le_of_left hs.orthUa hin V₀ _).trans h

/-- **Normal bound at the result of the L-step, augmented basis.** The result `U₀ L(t₁)ᵀ` of the
L-step has a factorization `U₀ (L(t₁)ᵀ V') V'ᵀ` with `r` orthonormal columns `V'` inside the
range of `V̂` (`IsRankAdaptiveStep.exists_lBasis`). Hence a bound `ε` for the normal part of `F`
at factored points with `r` columns of a region `D` applies to it, with the larger projector
`V̂ V̂ᵀ` in place of `V' V'ᵀ`, whenever `(t, U₀ L(t₁)ᵀ)` lies in `D`. -/
theorem IsRankAdaptiveStep.norm_lNormal_le {D : Set (ℝ × Matrix m n ℝ)}
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    (hε : FactoredNormalBoundOn F r D ε) {t : ℝ} (hmem : (t, U₀ * (Lf t₁)ᵀ) ∈ D) :
    ‖(1 - U₀ * U₀ᵀ) * F t (U₀ * (Lf t₁)ᵀ) * (1 - Va * Vaᵀ)‖ ≤ ε := by
  obtain ⟨V', hV', hcap, hin⟩ := hs.exists_lBasis
  have hT : (Lf t₁)ᵀ * V' * V'ᵀ = (Lf t₁)ᵀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hcap
  have hL : U₀ * (Lf t₁)ᵀ = U₀ * ((Lf t₁)ᵀ * V') * V'ᵀ := by rw [Matrix.mul_assoc U₀, hT]
  have h := hε t U₀ V' ((Lf t₁)ᵀ * V') hs.orthU₀ hV' (by rwa [← hL])
  rw [← hL] at h
  exact (norm_normal_le_of_right hs.orthVa hin U₀ _).trans h

variable {A : ℝ → Matrix m n ℝ} {a b ρ : ℝ}

/-- **Local error of the augmented matrix near a reference solution.** Let `F` be `L`-Lipschitz
and bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`, and let the
normal part of `F` be at most `ε` at the factored points with `r` columns of this tube. If a
rank-adaptive factor step over `[t₀, t₁] ⊆ [a, b]` has size `t₁ - t₀ ≤ H` and its start value
satisfies `‖U₀ S₀ V₀ᵀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, then the augmented matrix `Û Ŝ(t₁) V̂ᵀ`
differs from the exact solution through the start value by at most
`(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))` with `c₁ = bugC₁ L H` and `c₂ = bugC₂ L B H`
(arXiv:2104.05247, Theorem 2, local form). Nothing is assumed about `F` outside the tube. -/
theorem IsRankAdaptiveStep.hasLocalError_augmented_of_tube
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hH : t₁ - t₀ ≤ H)
    (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ (U₀ * S₀ * V₀ᵀ) (Ua * Sa t₁ * Vaᵀ)
      ((t₁ - t₀) * (bugC₁ L H * ε + bugC₂ L B H * (t₁ - t₀))) := by
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have h2 : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ := by linarith
  have hmem := hs.isBUGStepCore.toBasisUpdate.mem_tubeSet_of_near hFB hB ha hb h01 hA h2
  refine hs.isBUGStepCore.hasLocalError_of_tube (fun t ht => ?_) (fun t ht => ?_) hFL hL hFB hB
    ha hb h01 hH hA hsmall
  · rw [one_sub_leftProj_one_sub_rightProj_apply]
    exact hs.norm_kNormal_le hε (hmem 0 t ht)
  · rw [one_sub_rightProj_one_sub_leftProj_apply]
    exact hs.norm_lNormal_le hε (hmem 1 t ht)

/-- **Local error of a rank-adaptive factor step near a reference solution.** Under the
hypotheses of `MatrixBUG.IsRankAdaptiveStep.hasLocalError_augmented_of_tube`, the truncated
result `Y₁` of the step differs from the exact solution through the start value by at most
`(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀)) + ϑ`, where `ϑ` is the truncation tolerance of the step. This
is `MatrixBUG.IsRankAdaptiveStep.local_error_le` for a field that is Lipschitz and bounded only
near the reference solution. -/
theorem IsRankAdaptiveStep.hasLocalError_of_tube
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hH : t₁ - t₀ ≤ H)
    (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ (U₀ * S₀ * V₀ᵀ) Y₁
      ((t₁ - t₀) * (bugC₁ L H * ε + bugC₂ L B H * (t₁ - t₀)) + ϑ) :=
  (hs.hasLocalError_augmented_of_tube hε hFL hL hFB hB ha hb h01 hH hA hsmall).add_of_norm_sub_le
    hs.trunc

end FactorError

/-! ### The step relations -/

section Rel

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}

/-- **The augmented BUG step without truncation, as a relation between matrices.**
`augmentedRel F r t₀ t₁ Y₀ Ŷ` holds if `Y₀ = U₀ S₀ V₀ᵀ` for factors with `r` columns and
orthonormal `U₀`, `V₀`, and `Ŷ = Û Ŝ(t₁) V̂ᵀ` is the augmented matrix of a step
`MatrixBUG.IsRankAdaptiveStep` of these factors over `[t₀, t₁]` in which the augmented bases
`Û`, `V̂` have at most `2 r` columns (arXiv:2104.05247, §2.1, before the truncation). The step
is taken with tolerance `0` and result `Û Ŝ(t₁) V̂ᵀ`, so its truncation clause is empty. The
augmented bases are any orthonormal bases with this number of columns whose ranges contain the
columns of `K(t₁)` and `U₀`, and of `L(t₁)` and `V₀`. -/
def augmentedRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
      (s s' : ℕ) (Ua : Matrix m (Fin s) ℝ) (Va : Matrix n (Fin s') ℝ)
      (K : ℝ → Matrix m (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ)
      (Sa : ℝ → Matrix (Fin s) (Fin s') ℝ),
      Y₀ = U₀ * S₀ * V₀ᵀ ∧ s ≤ 2 * r ∧ s' ≤ 2 * r ∧
        IsRankAdaptiveStep F 0 t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa (Ua * Sa t₁ * Vaᵀ) ∧
        Y₁ = Ua * Sa t₁ * Vaᵀ

/-- **The step of the rank-adaptive BUG integrator, as a relation between matrices**
(arXiv:2104.05247, §2.1). `adaptiveStepRel F R ϑ t₀ t₁ Y₀ Y₁` holds if `Y₁` is within the
tolerance `ϑ` of an augmented matrix `Ŷ` of a step from `Y₀` over `[t₀, t₁]`
(`MatrixBUG.augmentedRel`), where the start value is factored with `r` columns for some `r` in
the set `R`. The rank of `Y₁` is not restricted. The relation contains every truncation with
`‖Y₁ - Ŷ‖ ≤ ϑ`, in particular the truncated singular value decomposition of `Ŷ` of any rank
whose truncation error is at most `ϑ`, which is the one used in the algorithm
(`MatrixBUG.augmentedRel.adaptiveStepRel_truncation`). -/
def adaptiveStepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (R : Set ℕ) (ϑ : ℝ) :
    StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ => ∃ r ∈ R, ∃ Yh : Matrix m n ℝ, augmentedRel F r t₀ t₁ Y₀ Yh ∧ ‖Y₁ - Yh‖ ≤ ϑ

/-- **The step of the augmented BUG integrator with truncation to a fixed rank, as a relation
between matrices.** `truncStepRel F r κ t₀ t₁ Y₀ Y₁` holds if `Y₁` has rank at most `r` and
`‖Y₁ - Ŷ‖ ≤ κ · distLR r Ŷ` for an augmented matrix `Ŷ` of a step from `Y₀` over `[t₀, t₁]`
(`MatrixBUG.augmentedRel`), where `distLR r Ŷ` is the distance of `Ŷ` to the matrices of rank at
most `r`. The relation contains every truncation with this property, in particular for `κ ≥ 1`
the truncated singular value decomposition of `Ŷ`
(`MatrixBUG.augmentedRel.truncStepRel_truncation`); a constant `κ > 1` allows truncations that
are best only up to a factor. -/
def truncStepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) (κ : ℝ) :
    StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ => ∃ Yh : Matrix m n ℝ, augmentedRel F r t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧
    ‖Y₁ - Yh‖ ≤ κ * distLR r Yh

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {R : Set ℕ} {ϑ κ t₀ t₁ : ℝ}
  {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {s s' : ℕ}
  {Ua : Matrix m (Fin s) ℝ} {Va : Matrix n (Fin s') ℝ} {K : ℝ → Matrix m (Fin r) ℝ}
  {Lf : ℝ → Matrix n (Fin r) ℝ} {Sa : ℝ → Matrix (Fin s) (Fin s') ℝ} {Y₀ Y₁ Yh : Matrix m n ℝ}

/-- A rank-adaptive factor step whose augmented bases have at most `2 r` columns relates
`U₀ S₀ V₀ᵀ` to the augmented matrix `Û Ŝ(t₁) V̂ᵀ`. -/
theorem IsRankAdaptiveStep.augmentedRel
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁) (hsr : s ≤ 2 * r)
    (hsr' : s' ≤ 2 * r) : augmentedRel F r t₀ t₁ (U₀ * S₀ * V₀ᵀ) (Ua * Sa t₁ * Vaᵀ) :=
  ⟨U₀, S₀, V₀, s, s', Ua, Va, K, Lf, Sa, rfl, hsr, hsr', hs.augmented, rfl⟩

/-- A rank-adaptive factor step with tolerance `ϑ` whose augmented bases have at most `2 r`
columns, started from a factorization with `r ∈ R` columns, is a step of the relation
`adaptiveStepRel F R ϑ`. -/
theorem IsRankAdaptiveStep.adaptiveStepRel
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁) (hr : r ∈ R)
    (hsr : s ≤ 2 * r) (hsr' : s' ≤ 2 * r) :
    adaptiveStepRel F R ϑ t₀ t₁ (U₀ * S₀ * V₀ᵀ) Y₁ :=
  ⟨r, hr, _, hs.augmentedRel hsr hsr', hs.trunc⟩

/-- A rank-adaptive factor step whose augmented bases have at most `2 r` columns, followed by a
truncation to rank `r` that is best up to the factor `κ`, is a step of the relation
`truncStepRel F r κ`. -/
theorem IsRankAdaptiveStep.truncStepRel {T : Matrix m n ℝ}
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁) (hsr : s ≤ 2 * r)
    (hsr' : s' ≤ 2 * r) (hr : T.rank ≤ r)
    (htr : ‖T - Ua * Sa t₁ * Vaᵀ‖ ≤ κ * distLR r (Ua * Sa t₁ * Vaᵀ)) :
    truncStepRel F r κ t₀ t₁ (U₀ * S₀ * V₀ᵀ) T :=
  ⟨_, hs.augmentedRel hsr hsr', hr, htr⟩

/-- An augmented BUG step can only be started from a matrix of rank at most `r`. -/
theorem augmentedRel.rank_start_le (h : augmentedRel F r t₀ t₁ Y₀ Yh) : Y₀.rank ≤ r := by
  obtain ⟨U₀, S₀, V₀, s, s', Ua, Va, K, Lf, Sa, rfl, -, -, -, -⟩ := h
  exact rank_mul_mul_transpose_le _ _ _

/-- The augmented matrix has rank at most `2 r`. -/
theorem augmentedRel.rank_le (h : augmentedRel F r t₀ t₁ Y₀ Yh) : Yh.rank ≤ 2 * r := by
  obtain ⟨U₀, S₀, V₀, s, s', Ua, Va, K, Lf, Sa, -, hsr, -, -, rfl⟩ := h
  calc (Ua * Sa t₁ * Vaᵀ).rank ≤ (Ua * Sa t₁).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Ua.rank := Matrix.rank_mul_le_left _ _
    _ ≤ s := by simpa using Ua.rank_le_card_width
    _ ≤ 2 * r := hsr

/-- **The number of columns of the start factorization is at most the number of rows.** If an
augmented BUG step from a factorization with `r` columns exists, then `r ≤ m`: a matrix with `m`
rows has at most `m` orthonormal columns. -/
theorem augmentedRel.le_card_left (h : augmentedRel F r t₀ t₁ Y₀ Yh) : r ≤ Fintype.card m := by
  obtain ⟨U₀, S₀, V₀, s, s', Ua, Va, K, Lf, Sa, -, -, -, hs, -⟩ := h
  have h := U₀.rank_le_card_height
  rwa [rank_eq_card_of_transpose_mul_eq_one hs.orthU₀, Fintype.card_fin] at h

/-- **The number of columns of the start factorization is at most the number of columns of the
matrix.** If an augmented BUG step from a factorization with `r` columns exists, then `r ≤ n`. -/
theorem augmentedRel.le_card_right (h : augmentedRel F r t₀ t₁ Y₀ Yh) : r ≤ Fintype.card n := by
  obtain ⟨U₀, S₀, V₀, s, s', Ua, Va, K, Lf, Sa, -, -, -, hs, -⟩ := h
  have h := V₀.rank_le_card_height
  rwa [rank_eq_card_of_transpose_mul_eq_one hs.orthV₀, Fintype.card_fin] at h

/-- An augmented matrix and a matrix within the tolerance `ϑ` of it form a step of the
rank-adaptive integrator, for every set `R` that contains the number of columns of the start
factorization. -/
theorem augmentedRel.adaptiveStepRel (h : augmentedRel F r t₀ t₁ Y₀ Yh) (hr : r ∈ R)
    (hY₁ : ‖Y₁ - Yh‖ ≤ ϑ) : adaptiveStepRel F R ϑ t₀ t₁ Y₀ Y₁ :=
  ⟨r, hr, Yh, h, hY₁⟩

/-- **The truncated singular value decomposition is a truncation by a tolerance.** If the
distance of the augmented matrix `Ŷ` to the matrices of rank at most `q` is at most `ϑ`, then
`Ŷ` truncated to its `q` largest singular values is a step of the rank-adaptive integrator: by
the Eckart–Young theorem (`EckartYoung.norm_sub_truncation_le`) the truncation error is this
distance. The algorithm takes the smallest such `q`. -/
theorem augmentedRel.adaptiveStepRel_truncation [DecidableEq n]
    (h : augmentedRel F r t₀ t₁ Y₀ Yh) (hr : r ∈ R) {q : ℕ} (hq : distLR q Yh ≤ ϑ) :
    MatrixBUG.adaptiveStepRel F R ϑ t₀ t₁ Y₀ (EckartYoung.truncation Yh q) := by
  have h1 : ‖Yh - EckartYoung.truncation Yh q‖ ≤ distLR q Yh :=
    le_distLR_iff.2 fun Z hZ => EckartYoung.norm_sub_truncation_le Yh hZ
  exact h.adaptiveStepRel hr (by rw [norm_sub_rev]; exact h1.trans hq)

/-- **The truncation to rank `r` exists.** For `κ ≥ 1` every augmented matrix has a truncation
to rank `r` that is best up to the factor `κ`, namely a best approximation of rank at most `r`
(`exists_best_approx`). -/
theorem augmentedRel.exists_truncStepRel (h : augmentedRel F r t₀ t₁ Y₀ Yh) (hκ : 1 ≤ κ) :
    ∃ Y₁, truncStepRel F r κ t₀ t₁ Y₀ Y₁ := by
  obtain ⟨Z, hZ, hd⟩ := exists_best_approx r Yh
  refine ⟨Z, Yh, h, hZ, ?_⟩
  rw [norm_sub_rev, hd]
  exact le_mul_of_one_le_left distLR_nonneg hκ

/-- **The truncated singular value decomposition is a truncation to rank `r`.** For `κ ≥ 1` the
augmented matrix truncated to its `r` largest singular values is a step of the integrator with
truncation to rank `r`: by the Eckart–Young theorem (`EckartYoung.norm_sub_truncation_le`) it
is a best approximation of rank at most `r`. -/
theorem augmentedRel.truncStepRel_truncation [DecidableEq n]
    (h : augmentedRel F r t₀ t₁ Y₀ Yh) (hκ : 1 ≤ κ) :
    truncStepRel F r κ t₀ t₁ Y₀ (EckartYoung.truncation Yh r) := by
  have h1 : ‖Yh - EckartYoung.truncation Yh r‖ ≤ distLR r Yh :=
    le_distLR_iff.2 fun Z hZ => EckartYoung.norm_sub_truncation_le Yh hZ
  refine ⟨Yh, h, EckartYoung.rank_truncation_le Yh r, ?_⟩
  rw [norm_sub_rev]
  exact h1.trans (le_mul_of_one_le_left distLR_nonneg hκ)

/-- **Monotonicity of the rank-adaptive step relation**: a step stays a step if the set of
numbers of columns and the tolerance are enlarged. In particular a step with a cap on the number
of columns, `R = Set.Icc r₀ r₁`, is a step for `R = Set.Ici r₀`. -/
theorem adaptiveStepRel.mono {R' : Set ℕ} {ϑ' : ℝ} (h : adaptiveStepRel F R ϑ t₀ t₁ Y₀ Y₁)
    (hR : R ⊆ R') (hϑ : ϑ ≤ ϑ') : adaptiveStepRel F R' ϑ' t₀ t₁ Y₀ Y₁ := by
  obtain ⟨r, hr, Yh, hYh, htr⟩ := h
  exact ⟨r, hR hr, Yh, hYh, htr.trans hϑ⟩

/-- A step of the rank-adaptive integrator starts from a matrix whose rank is at most some
element of `R`. -/
theorem adaptiveStepRel.exists_rank_start_le (h : adaptiveStepRel F R ϑ t₀ t₁ Y₀ Y₁) :
    ∃ r ∈ R, Y₀.rank ≤ r := by
  obtain ⟨r, hr, Yh, hYh, -⟩ := h
  exact ⟨r, hr, hYh.rank_start_le⟩

/-- The result of a step with truncation to rank `r` has rank at most `r`. -/
theorem truncStepRel.rank_le (h : truncStepRel F r κ t₀ t₁ Y₀ Y₁) : Y₁.rank ≤ r := by
  obtain ⟨Yh, -, hr, -⟩ := h
  exact hr

/-- A step with truncation to rank `r` can only be started from a matrix of rank at most `r`. -/
theorem truncStepRel.rank_start_le (h : truncStepRel F r κ t₀ t₁ Y₀ Y₁) : Y₀.rank ≤ r := by
  obtain ⟨Yh, hYh, -, -⟩ := h
  exact hYh.rank_start_le

/-- A step with truncation to rank `r` stays a step if the constant `κ` is enlarged. -/
theorem truncStepRel.mono {κ' : ℝ} (h : truncStepRel F r κ t₀ t₁ Y₀ Y₁) (hκ : κ ≤ κ') :
    truncStepRel F r κ' t₀ t₁ Y₀ Y₁ := by
  obtain ⟨Yh, hYh, hr, htr⟩ := h
  exact ⟨Yh, hYh, hr, htr.trans (mul_le_mul_of_nonneg_right hκ distLR_nonneg)⟩

section Tube

variable {A : ℝ → Matrix m n ℝ} {a b ρ B : ℝ}

/-- **Near the reference solution, the tube extension has the same augmented steps as the
field.** Let `F` be bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`,
and let `[t₀, t₁] ⊆ [a, b]`. If `‖Y₀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, the relation `augmentedRel`
is the same for `tubeExt F A a b ρ` and for `F`. -/
theorem augmentedRel_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    augmentedRel (tubeExt F A a b ρ) r t₀ t₁ Y₀ Yh ↔ augmentedRel F r t₀ t₁ Y₀ Yh := by
  constructor
  · rintro ⟨U₀, S₀, V₀, s, s', Ua, Va, K, Lf, Sa, rfl, hsr, hsr', hs, rfl⟩
    exact ((isRankAdaptiveStep_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1
      hs).augmentedRel hsr hsr'
  · rintro ⟨U₀, S₀, V₀, s, s', Ua, Va, K, Lf, Sa, rfl, hsr, hsr', hs, rfl⟩
    exact ((isRankAdaptiveStep_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).2
      hs).augmentedRel hsr hsr'

/-- **Near the reference solution, the tube extension has the same rank-adaptive steps as the
field**: under the hypotheses of `MatrixBUG.augmentedRel_tubeExt_iff_of_near` the relation
`adaptiveStepRel` is the same for `tubeExt F A a b ρ` and for `F`. The truncation does not
evaluate the field. -/
theorem adaptiveStepRel_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    adaptiveStepRel (tubeExt F A a b ρ) R ϑ t₀ t₁ Y₀ Y₁ ↔ adaptiveStepRel F R ϑ t₀ t₁ Y₀ Y₁ :=
  ⟨fun ⟨r, hr, Yh, h, htr⟩ =>
      ⟨r, hr, Yh, (augmentedRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 h, htr⟩,
    fun ⟨r, hr, Yh, h, htr⟩ =>
      ⟨r, hr, Yh, (augmentedRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).2 h, htr⟩⟩

/-- **Near the reference solution, the tube extension has the same steps with truncation to
rank `r` as the field**: under the hypotheses of `MatrixBUG.augmentedRel_tubeExt_iff_of_near`
the relation `truncStepRel` is the same for `tubeExt F A a b ρ` and for `F`. -/
theorem truncStepRel_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    truncStepRel (tubeExt F A a b ρ) r κ t₀ t₁ Y₀ Y₁ ↔ truncStepRel F r κ t₀ t₁ Y₀ Y₁ :=
  ⟨fun ⟨Yh, h, hr⟩ =>
      ⟨Yh, (augmentedRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 h, hr⟩,
    fun ⟨Yh, h, hr⟩ =>
      ⟨Yh, (augmentedRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).2 h, hr⟩⟩

end Tube

end Rel

/-! ### Existence of one step -/

section Exists

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
  {L : ℝ} {R : Set ℕ} {ϑ κ t₀ t₁ : ℝ}

/-- **A rank-adaptive factor step exists, without truncation.** If `F` is Lipschitz and
continuous in time on `[t₀, t₁]` and `U₀`, `V₀` have orthonormal columns, then for every `S₀`
the K-, L- and S-step have solutions and augmented bases exist: there are `Û`, `V̂` with at most
`2 r` orthonormal columns and `K`, `L`, `Ŝ` forming a step of the rank-adaptive integrator with
tolerance `0` and result `Û Ŝ(t₁) V̂ᵀ`. The numbers of columns are `min (2 r) m` and
`min (2 r) n`. In contrast to `MatrixBUG.exists_isRankAdaptiveStep` the field need not be
bounded, continuity in time is needed only on the step interval, and `2 r` may exceed the
numbers of rows and columns. -/
theorem exists_isRankAdaptiveStep_of_lipschitz (hF : IsLipschitzField F L)
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁)
    {U₀ : Matrix m (Fin r) ℝ} (S₀ : Matrix (Fin r) (Fin r) ℝ) {V₀ : Matrix n (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) :
    ∃ (s s' : ℕ) (Ua : Matrix m (Fin s) ℝ) (Va : Matrix n (Fin s') ℝ)
      (K : ℝ → Matrix m (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ)
      (Sa : ℝ → Matrix (Fin s) (Fin s') ℝ), s ≤ 2 * r ∧ s' ≤ 2 * r ∧
      IsRankAdaptiveStep F 0 t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa (Ua * Sa t₁ * Vaᵀ) := by
  obtain ⟨K, hK, hK₀⟩ := exists_odeSolution_conj_of_lipschitz hF hc _ _
    (fun t x => kField_eq V₀ t x) h01 (U₀ * S₀)
  obtain ⟨Lf, hLf, hLf₀⟩ := exists_odeSolution_conj_of_lipschitz hF hc _ _
    (fun t x => lField_eq U₀ t x) h01 (V₀ * S₀ᵀ)
  have hKr : (Matrix.fromCols (K t₁) U₀).rank ≤ 2 * r := by
    have := (Matrix.fromCols (K t₁) U₀).rank_le_card_width
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  have hLr : (Matrix.fromCols (Lf t₁) V₀).rank ≤ 2 * r := by
    have := (Matrix.fromCols (Lf t₁) V₀).rank_le_card_width
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  obtain ⟨Ua, hUa, hKcap, haugU⟩ := exists_orthonormal_capture_fromCols (K t₁) U₀
    (r := min (2 * r) (Fintype.card m)) (le_min hKr (Matrix.rank_le_card_height _))
    (min_le_right _ _)
  obtain ⟨Va, hVa, hLcap, haugV⟩ := exists_orthonormal_capture_fromCols (Lf t₁) V₀
    (r := min (2 * r) (Fintype.card n)) (le_min hLr (Matrix.rank_le_card_height _))
    (min_le_right _ _)
  obtain ⟨Sa, hSa, hSa₀⟩ := exists_odeSolution_conj_of_lipschitz hF hc _ _
    (fun t x => sField_eq Ua Va t x) h01 (Uaᵀ * U₀ * S₀ * (V₀ᵀ * Va))
  exact ⟨_, _, Ua, Va, K, Lf, Sa, min_le_left _ _, min_le_left _ _, hU₀, hV₀, hK, hK₀, hLf,
    hLf₀, hUa, hKcap, haugU, hVa, hLcap, haugV, hSa, hSa₀, by simp⟩

/-- **An augmented BUG step exists from every start value of rank at most `r`.** If `F` is
Lipschitz and continuous in time on `[t₀, t₁]` and `r ≤ m`, `r ≤ n`, then every `Y₀` of rank at
most `r` has a successor under `MatrixBUG.augmentedRel F r`: factor `Y₀ = U₀ S₀ V₀ᵀ` with `r`
orthonormal columns (`exists_factor_of_rank_le`) and apply
`MatrixBUG.exists_isRankAdaptiveStep_of_lipschitz`. -/
theorem exists_augmentedRel (hF : IsLipschitzField F L)
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) : ∃ Yh, augmentedRel F r t₀ t₁ Y₀ Yh := by
  obtain ⟨U₀, S₀, V₀, hU₀, hV₀, rfl⟩ := exists_factor_of_rank_le hY₀ hrm hrn
  obtain ⟨s, s', Ua, Va, K, Lf, Sa, hsr, hsr', hs⟩ :=
    exists_isRankAdaptiveStep_of_lipschitz hF hc h01 S₀ hU₀ hV₀
  exact ⟨_, hs.augmentedRel hsr hsr'⟩

/-- **A step of the rank-adaptive BUG integrator exists** from every start value whose rank is
at most some `r ∈ R` with `r ≤ m`, `r ≤ n`, for every Lipschitz field that is continuous in time
on the step interval and every tolerance `ϑ ≥ 0`. The augmented matrix itself is a witness: the
relation contains every matrix within `ϑ` of it. -/
theorem exists_adaptiveStepRel (hF : IsLipschitzField F L)
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁) (hϑ : 0 ≤ ϑ)
    (hr : r ∈ R) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) : ∃ Y₁, adaptiveStepRel F R ϑ t₀ t₁ Y₀ Y₁ := by
  obtain ⟨Yh, hYh⟩ := exists_augmentedRel hF hc h01 hrm hrn hY₀
  exact ⟨Yh, hYh.adaptiveStepRel hr (by simpa using hϑ)⟩

/-- **With at least `r₀` columns, a step of the rank-adaptive BUG integrator exists from every
matrix.** Let `R = Set.Ici r₀` with `r₀ ≤ m` and `r₀ ≤ n`. For every Lipschitz field that is
continuous in time on the step interval, every tolerance `ϑ ≥ 0` and every start value `Y₀` there
is a step: a factorization of `Y₀` is padded with orthonormal columns to `max (rank Y₀) r₀`
columns, a number that lies in `R` and is at most `m` and `n`.

The two conditions on `r₀` cannot be dropped: a factorization with `r` orthonormal columns
exists only for `r ≤ m` and `r ≤ n` (`MatrixBUG.augmentedRel.le_card_left`,
`MatrixBUG.augmentedRel.le_card_right`), so for larger `r₀` no step exists at all. -/
theorem exists_adaptiveStepRel_Ici (hF : IsLipschitzField F L)
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁) (hϑ : 0 ≤ ϑ)
    {r₀ : ℕ} (hrm : r₀ ≤ Fintype.card m) (hrn : r₀ ≤ Fintype.card n) (Y₀ : Matrix m n ℝ) :
    ∃ Y₁, adaptiveStepRel F (Set.Ici r₀) ϑ t₀ t₁ Y₀ Y₁ :=
  exists_adaptiveStepRel hF hc h01 hϑ (r := max Y₀.rank r₀) (Set.mem_Ici.2 (le_max_right _ _))
    (max_le Y₀.rank_le_card_height hrm) (max_le Y₀.rank_le_card_width hrn) (le_max_left _ _)

/-- **A step with truncation to rank `r` exists from every start value of rank at most `r`.** If
`F` is Lipschitz and continuous in time on `[t₀, t₁]`, `r ≤ m`, `r ≤ n` and `κ ≥ 1`, then every
`Y₀` of rank at most `r` has a successor under `MatrixBUG.truncStepRel F r κ`. -/
theorem exists_truncStepRel (hF : IsLipschitzField F L)
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁) (hκ : 1 ≤ κ)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) : ∃ Y₁, truncStepRel F r κ t₀ t₁ Y₀ Y₁ := by
  obtain ⟨Yh, hYh⟩ := exists_augmentedRel hF hc h01 hrm hrn hY₀
  exact hYh.exists_truncStepRel hκ

/-- A step with truncation to rank `r` from `Y₀` exists if and only if `Y₀` has rank at most `r`
(for a Lipschitz field that is continuous in time on the step interval, `r ≤ m`, `r ≤ n` and
`κ ≥ 1`). -/
theorem exists_truncStepRel_iff (hF : IsLipschitzField F L)
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁) (hκ : 1 ≤ κ)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ} :
    (∃ Y₁, truncStepRel F r κ t₀ t₁ Y₀ Y₁) ↔ Y₀.rank ≤ r :=
  ⟨fun ⟨_, h⟩ => h.rank_start_le, exists_truncStepRel hF hc h01 hκ hrm hrn⟩

end Exists

/-! ### Local error of the relations near a reference solution -/

section Error

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {R : Set ℕ} {ϑ κ t₀ t₁ : ℝ} {Y₀ Y₁ Yh : Matrix m n ℝ}
  {L B ε H : ℝ} {A : ℝ → Matrix m n ℝ} {a b ρ : ℝ}

/-- **Local error of the augmented BUG step without truncation near a reference solution.** Let
`F` be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around a solution `A` over
`[a, b]`, and let the normal part of `F` be at most `ε` at the factored points with `r` columns
of this tube. If the step over `[t₀, t₁] ⊆ [a, b]` has size `t₁ - t₀ ≤ H` and its start value
satisfies `‖Y₀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, then every step of `MatrixBUG.augmentedRel` from
`Y₀` has local error at most `(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))` with `c₁ = bugC₁ L H` and
`c₂ = bugC₂ L B H`. -/
theorem augmentedRel.hasLocalError_of_tube (h : augmentedRel F r t₀ t₁ Y₀ Yh)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hH : t₁ - t₀ ≤ H)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Yh ((t₁ - t₀) * (bugC₁ L H * ε + bugC₂ L B H * (t₁ - t₀))) := by
  obtain ⟨U₀, S₀, V₀, s, s', Ua, Va, K, Lf, Sa, rfl, -, -, hs, rfl⟩ := h
  exact hs.hasLocalError_augmented_of_tube hε hFL hL hFB hB ha hb h01 hH hA hsmall

/-- **Local error of the rank-adaptive BUG step near a reference solution.** Let `F` be
`L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`,
and let the normal part of `F` be at most `ε` at the factored points of this tube with `r`
columns, for every `r` in the set `R` of numbers of columns that a step may start from. If the
step over `[t₀, t₁] ⊆ [a, b]` has size `t₁ - t₀ ≤ H` and its start value satisfies
`‖Y₀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, then every step of `MatrixBUG.adaptiveStepRel F R ϑ` from
`Y₀` has local error at most `(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀)) + ϑ` with `c₁ = bugC₁ L H` and
`c₂ = bugC₂ L B H` (arXiv:2104.05247, Theorem 2, local form). The tolerance enters once and is
not multiplied by the step size. -/
theorem adaptiveStepRel.hasLocalError_of_tube (h : adaptiveStepRel F R ϑ t₀ t₁ Y₀ Y₁)
    (hε : ∀ r ∈ R, FactoredNormalBoundOn F r (tubeSet A a b ρ) ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hH : t₁ - t₀ ≤ H)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Y₁
      ((t₁ - t₀) * (bugC₁ L H * ε + bugC₂ L B H * (t₁ - t₀)) + ϑ) := by
  obtain ⟨r, hr, Yh, hYh, htr⟩ := h
  exact (hYh.hasLocalError_of_tube (hε r hr) hFL hL hFB hB ha hb h01 hH hA
    hsmall).add_of_norm_sub_le htr

/-- **Local error of the augmented BUG step with truncation to rank `r` near a reference
solution.** Let `F` be continuous, `L`-Lipschitz and bounded by `B` on the tube of radius `ρ`
around a solution `A` over `[a, b]`, and let the normal part of `F` be at most `ε` at the
factored points with `r` columns of this tube. If the step over `[t₀, t₁] ⊆ [a, b]` has size
`t₁ - t₀ ≤ H` and its start value satisfies `‖Y₀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, then every step
of `MatrixBUG.truncStepRel F r κ` from `Y₀`, `κ ≥ 0`, differs from the exact solution `Φ`
through the start value by at most

  `(t₁ - t₀) (κ (10 L B (t₁ - t₀) + ε) + (1 + κ) (c₁ ε + c₂ (t₁ - t₀)))`,

`c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`. The step without truncation contributes
`(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))`. The truncation costs at most `κ` times the distance of
`Φ t₁` to the matrices of rank at most `r` plus `1 + κ` times the error before truncation
(`norm_trunc_sub_le`), and this distance is at most `(t₁ - t₀) (10 L B (t₁ - t₀) + ε)`
(`distLR_flow_le_of_tube`). No truncation tolerance appears. -/
theorem truncStepRel.hasLocalError_of_tube (h : truncStepRel F r κ t₀ t₁ Y₀ Y₁) (hκ : 0 ≤ κ)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε) (hε₀ : 0 ≤ ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (hc : ContinuousOn (Function.uncurry F) (tubeSet A a b ρ))
    (hAc : ContinuousOn A (Icc a b)) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁)
    (hH : t₁ - t₀ ≤ H) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Y₁ ((t₁ - t₀) * (κ * (10 * L * B * (t₁ - t₀) + ε) +
      (1 + κ) * (bugC₁ L H * ε + bugC₂ L B H * (t₁ - t₀)))) := by
  obtain ⟨Yh, hYh, -, htr⟩ := h
  intro Φ hΦ hΦ₀
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have h₁ := hYh.hasLocalError_of_tube hε hFL hL hFB hB ha hb h01 hH hA hsmall Φ hΦ hΦ₀
  have h₂ := distLR_flow_le_of_tube hε hε₀ hFL hL hFB hB hc hAc ha hb h01 hA hΦ
    (by rw [hΦ₀]; exact hYh.rank_start_le) (by rw [hΦ₀]; linarith)
  have h₃ := norm_trunc_sub_le (A₁ := Φ t₁) hκ htr
  have h₄ := mul_le_mul_of_nonneg_left h₂ hκ
  have h₅ := mul_le_mul_of_nonneg_left h₁ (by linarith : (0 : ℝ) ≤ 1 + κ)
  have e : (t₁ - t₀) * (κ * (10 * L * B * (t₁ - t₀) + ε) +
      (1 + κ) * (bugC₁ L H * ε + bugC₂ L B H * (t₁ - t₀))) =
      κ * ((t₁ - t₀) * (10 * L * B * (t₁ - t₀) + ε)) +
        (1 + κ) * ((t₁ - t₀) * (bugC₁ L H * ε + bugC₂ L B H * (t₁ - t₀))) := by ring
  rw [e]
  linarith

end Error

/-! ### Examples -/

section Examples

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **The normal bound for all numbers of columns can be smaller than the field.** The radial
field `F(t, Y) = Y / max ‖Y‖ 1` has norm `1` at every matrix of norm at least `1`, and its
normal part vanishes at every factored point, whatever the number of columns
(`MatrixKSL.radial_normal_eq_zero`). So the hypothesis
`∀ r ∈ R, FactoredNormalBoundOn F r D ε` of `MatrixBUG.adaptiveStepRel.hasLocalError_of_tube`
holds with `ε = 0` for every set `R` and every region `D`, for a field that is not small. -/
example :
    (∀ r : ℕ, FactoredNormalBoundOn (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) r
      Set.univ 0) ∧ ∀ Z : Matrix m n ℝ, 1 ≤ ‖Z‖ → ‖MatrixKSL.radial Z‖ = 1 := by
  refine ⟨fun r t U V S hU hV _ => MatrixKSL.radial_normal_eq_zero t U S V hU hV,
    fun Z hZ => ?_⟩
  rw [MatrixKSL.radial, max_eq_left hZ, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (ne_of_gt (lt_of_lt_of_le one_pos hZ))]

/-- **Non-vacuity of the rank-adaptive step and of its local error.** The linear field
`F(t, Y) = M Y + Y Nᵀ + G` with a stationary point `C` (`M C + C Nᵀ + G = 0`) is Lipschitz with
constant `‖M‖ + ‖N‖` and not bounded. On the tube of radius `ρ` around the constant solution
`A(t) = C` it is bounded by `(‖M‖ + ‖N‖) ρ`, and its normal part at the factored points is at
most `‖G‖` for every number of columns (`factoredNormalBoundOn_linear`). Hence, for
`R = Set.Ici r₀` with `r₀ ≤ m`, `r₀ ≤ n` and every tolerance `ϑ ≥ 0`, a step of the
rank-adaptive integrator exists from every matrix `Y₀`, of any rank, and if `Y₀` is close to `C`
the step has local error `(t₁ - t₀) (c₁ ‖G‖ + c₂ (t₁ - t₀)) + ϑ`. The normal bound `‖G‖` is
smaller than the bound `(‖M‖ + ‖N‖) ρ` of the field as soon as `‖G‖ < (‖M‖ + ‖N‖) ρ`. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) {r₀ : ℕ} (hrm : r₀ ≤ Fintype.card m)
    (hrn : r₀ ≤ Fintype.card n) {a b ρ ϑ t₀ t₁ : ℝ} (hρ : 0 ≤ ρ) (hϑ : 0 ≤ ϑ) (ha : a ≤ t₀)
    (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (Y₀ : Matrix m n ℝ)
    (hsmall : ‖Y₀ - C‖ + 4 * ((‖M‖ + ‖N‖) * ρ) * (t₁ - t₀) < ρ) :
    ∃ Y₁, adaptiveStepRel (fun (_ : ℝ) (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G) (Set.Ici r₀)
        ϑ t₀ t₁ Y₀ Y₁ ∧
      HasLocalError (fun (_ : ℝ) (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G) t₀ t₁ Y₀ Y₁
        ((t₁ - t₀) * (bugC₁ (‖M‖ + ‖N‖) (t₁ - t₀) * ‖G‖ +
          bugC₂ (‖M‖ + ‖N‖) ((‖M‖ + ‖N‖) * ρ) (t₁ - t₀) * (t₁ - t₀)) + ϑ) := by
  have hP := dlraProblem_linear M N G C hC a b hρ
  obtain ⟨Y₁, hY₁⟩ := exists_adaptiveStepRel_Ici (isLipschitzField_linear M N G)
    (fun _ => continuousOn_const) h01 hϑ hrm hrn Y₀
  exact ⟨Y₁, hY₁, hY₁.hasLocalError_of_tube (fun r _ => factoredNormalBoundOn_linear M N G _)
    hP.lipschitz hP.L_nonneg hP.bounded hP.B_nonneg ha hb h01 le_rfl (hP.sol.mono ha hb)
    hsmall⟩

/-- **Non-vacuity of the step with truncation to rank `r` and of its local error.** For the
linear field `F(t, Y) = M Y + Y Nᵀ + G` with a stationary point `C` and every `κ ≥ 1`, a step
with truncation to rank `r` exists from every `Y₀` of rank at most `r` (`r ≤ m`, `r ≤ n`); its
result has rank at most `r`, and if `Y₀` is close to `C` the step has the local error of
`MatrixBUG.truncStepRel.hasLocalError_of_tube` with `L = ‖M‖ + ‖N‖`, `B = (‖M‖ + ‖N‖) ρ` and
`ε = ‖G‖`. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) {r : ℕ} (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) {a b ρ κ t₀ t₁ : ℝ} (hρ : 0 ≤ ρ) (hκ : 1 ≤ κ) (ha : a ≤ t₀)
    (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r)
    (hsmall : ‖Y₀ - C‖ + 4 * ((‖M‖ + ‖N‖) * ρ) * (t₁ - t₀) < ρ) :
    ∃ Y₁, truncStepRel (fun (_ : ℝ) (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G) r κ t₀ t₁ Y₀ Y₁ ∧
      Y₁.rank ≤ r ∧
      HasLocalError (fun (_ : ℝ) (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G) t₀ t₁ Y₀ Y₁
        ((t₁ - t₀) * (κ * (10 * (‖M‖ + ‖N‖) * ((‖M‖ + ‖N‖) * ρ) * (t₁ - t₀) + ‖G‖) +
          (1 + κ) * (bugC₁ (‖M‖ + ‖N‖) (t₁ - t₀) * ‖G‖ +
            bugC₂ (‖M‖ + ‖N‖) ((‖M‖ + ‖N‖) * ρ) (t₁ - t₀) * (t₁ - t₀)))) := by
  have hP := dlraProblem_linear M N G C hC a b hρ
  obtain ⟨Y₁, hY₁⟩ := exists_truncStepRel (isLipschitzField_linear M N G)
    (fun _ => continuousOn_const) h01 hκ hrm hrn hY₀
  exact ⟨Y₁, hY₁, hY₁.rank_le, hY₁.hasLocalError_of_tube (zero_le_one.trans hκ)
    (factoredNormalBoundOn_linear M N G _) (norm_nonneg G) hP.lipschitz hP.L_nonneg hP.bounded
    hP.B_nonneg (continuous_uncurry_linear M N G).continuousOn hP.sol.cont ha hb h01 le_rfl
    (hP.sol.mono ha hb) hsmall⟩

end Examples

end MatrixBUG

end LeanDLRA
