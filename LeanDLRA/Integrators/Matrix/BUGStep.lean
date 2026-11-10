import LeanDLRA.Integrators.BUGCore
import LeanDLRA.Integrators.Matrix.BUG

/-!
# The matrix BUG step as a step relation

The matrix BUG integrator of Ceruti and Lubich advances a rank-`r` matrix `Y₀ = U₀ S₀ V₀ᵀ` over a
time step `[t₀, t₁]` by a K-step, an L-step and a Galerkin S-step. The predicate
`MatrixBUG.IsStep` of `LeanDLRA/Integrators/Matrix/BUG.lean` describes one such step at the level
of the factors. This file states the step on the level of the matrices themselves, as a relation
between the old value `Y₀` and the new value `Y₁`, and proves its local error bound in the form
`HasLocalError` used by the convergence theorems of `LeanDLRA/Integrators/GlobalError.lean` and
`LeanDLRA/Integrators/Tube.lean`.

The step relation contains the algorithm only. The size `ε` of the normal part of the vector
field, the Lipschitz constant and the bound of the field are hypotheses of the error theorems,
not part of the step.

## Main definitions

* `MatrixBUG.stepRel F r`: the step relation of the rank-`r` matrix BUG integrator for the field
  `F`. `stepRel F r t₀ t₁ Y₀ Y₁` says that `Y₁` is the result of some BUG step over `[t₀, t₁]`
  started from some factorization `Y₀ = U₀ S₀ V₀ᵀ` with orthonormal `U₀`, `V₀`.

## Main results

* `MatrixBUG.IsStep.isBUGStepCore`: a matrix step is a step of the abstract integrator
  (`IsBUGStepCore`) with the projections `leftProj U₀`, `rightProj V₀`, `leftProj U₁`,
  `rightProj V₁`.
* `MatrixBUG.IsStep.norm_kNormal_le`, `MatrixBUG.IsStep.norm_lNormal_le`: the two normal bounds
  of the error analysis follow from `FactoredNormalBoundOn F r D ε` as soon as the results of the
  K-step and of the L-step lie in the region `D`.
* `MatrixBUG.IsStep.hasLocalError`, `MatrixBUG.stepRel.hasLocalError`: the local error bound
  `(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))` for a globally Lipschitz and bounded field.
* `MatrixBUG.IsStep.hasLocalError_of_tube`, `MatrixBUG.stepRel.hasLocalError_of_tube`: the same
  bound when the field is Lipschitz and bounded and its normal part is small only on a tube
  around a reference solution.
* `MatrixBUG.isStep_tubeExt_iff_of_near`, `MatrixBUG.stepRel_tubeExt_iff_of_near`: near the
  reference solution, a step for the tube extension `tubeExt F A a b ρ` is the same as a step
  for `F`.
* `MatrixBUG.isRun_stepRel_of_isStep`: a chain of factor steps is a run of the step relation.

## Implementation notes

A run of `MatrixBUG.stepRel` (see `IsRun` in `LeanDLRA/Integrators/Defs.lean`) is more general
than a chain of factor steps: between two steps the factorization of the current value may be
replaced by any other factorization with orthonormal bases. The error theorems do not depend on
this choice.

## References

* [CerutiLubich2022, §3.1, Lemma 4]
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixBUG

/-! ### The step relation -/

section Rel

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}

/-- **The step relation of the rank-`r` matrix BUG integrator.** `stepRel F r t₀ t₁ Y₀ Y₁` holds
if `Y₀ = U₀ S₀ V₀ᵀ` for some factors with orthonormal `U₀`, `V₀`, and `Y₁ = U₁ S(t₁) V₁ᵀ` is the
result of a BUG step (`MatrixBUG.IsStep`) over `[t₀, t₁]` started from these factors. The
relation contains no constants of the error analysis. -/
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
      (U₁ : Matrix m (Fin r) ℝ) (V₁ : Matrix n (Fin r) ℝ) (K : ℝ → Matrix m (Fin r) ℝ)
      (Lf : ℝ → Matrix n (Fin r) ℝ) (S : ℝ → Matrix (Fin r) (Fin r) ℝ),
      Y₀ = U₀ * S₀ * V₀ᵀ ∧ IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S ∧ Y₁ = U₁ * S t₁ * V₁ᵀ

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {U₀ U₁ : Matrix m (Fin r) ℝ}
  {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ V₁ : Matrix n (Fin r) ℝ} {K : ℝ → Matrix m (Fin r) ℝ}
  {Lf : ℝ → Matrix n (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {Y₀ Y₁ : Matrix m n ℝ}

/-- A factor step relates the matrices `U₀ S₀ V₀ᵀ` and `U₁ S(t₁) V₁ᵀ`. -/
theorem IsStep.stepRel (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S) :
    MatrixBUG.stepRel F r t₀ t₁ (U₀ * S₀ * V₀ᵀ) (U₁ * S t₁ * V₁ᵀ) :=
  ⟨U₀, S₀, V₀, U₁, V₁, K, Lf, S, rfl, hs, rfl⟩

/-- The result of a BUG step has rank at most `r`. -/
theorem stepRel.rank_le (h : stepRel F r t₀ t₁ Y₀ Y₁) : Y₁.rank ≤ r := by
  obtain ⟨U₀, S₀, V₀, U₁, V₁, K, Lf, S, -, -, rfl⟩ := h
  exact rank_mul_mul_transpose_le _ _ _

/-- A BUG step can only be started from a matrix of rank at most `r`. -/
theorem stepRel.rank_start_le (h : stepRel F r t₀ t₁ Y₀ Y₁) : Y₀.rank ≤ r := by
  obtain ⟨U₀, S₀, V₀, U₁, V₁, K, Lf, S, rfl, -, -⟩ := h
  exact rank_mul_mul_transpose_le _ _ _

/-- All values of a run of the matrix BUG integrator have rank at most `r`, provided the start
value has. -/
theorem IsRun.rank_le {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → Matrix m n ℝ}
    (hY : IsRun (stepRel F r) τ N Y) (h0 : (Y 0).rank ≤ r) : ∀ n ≤ N, (Y n).rank ≤ r
  | 0, _ => h0
  | n + 1, hn => (hY.step n hn).rank_le

/-- **A chain of factor steps is a run.** If the factors `(U j, Sm j, V j)` are advanced by BUG
steps along the grid `τ` and `Sm (j + 1)` is the value of the S-step at the end of step `j`, then
the matrices `U j * Sm j * (V j)ᵀ` form a run of `MatrixBUG.stepRel`. -/
theorem isRun_stepRel_of_isStep {τ : ℕ → ℝ} {N : ℕ} {U : ℕ → Matrix m (Fin r) ℝ}
    {Sm : ℕ → Matrix (Fin r) (Fin r) ℝ} {V : ℕ → Matrix n (Fin r) ℝ}
    {K : ℕ → ℝ → Matrix m (Fin r) ℝ} {Lf : ℕ → ℝ → Matrix n (Fin r) ℝ}
    {S : ℕ → ℝ → Matrix (Fin r) (Fin r) ℝ} (hτ : IsGrid τ N)
    (hstep : ∀ j < N, IsStep F (τ j) (τ (j + 1)) (U j) (Sm j) (V j) (U (j + 1)) (V (j + 1))
      (K j) (Lf j) (S j))
    (hS : ∀ j < N, Sm (j + 1) = S j (τ (j + 1))) :
    IsRun (stepRel F r) τ N fun j => U j * Sm j * (V j)ᵀ :=
  ⟨hτ, fun j hj => by
    have h := (hstep j hj).stepRel
    rw [← hS j hj] at h
    exact h⟩

/-- **A matrix BUG step is an abstract BUG step.** The full-space trajectories `K(t) V₀ᵀ`,
`U₀ L(t)ᵀ`, `U₁ S(t) V₁ᵀ` of a factor step form a step of the abstract integrator
(`IsBUGStepCore`) for the projections `P₀ = leftProj U₀`, `Q₀ = rightProj V₀`,
`P₁ = leftProj U₁`, `Q₁ = rightProj V₁`. No bound on the field is needed. -/
theorem IsStep.isBUGStepCore (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S) :
    IsBUGStepCore F (leftProj U₀) (rightProj V₀) (leftProj U₁) (rightProj V₁) t₀ t₁
      (U₀ * S₀ * V₀ᵀ) (fun t => K t * V₀ᵀ) (fun t => U₀ * (Lf t)ᵀ) (fun t => U₁ * S t * V₁ᵀ) :=
  isBUGStepCore_iff.2 ⟨basisUpdate_two_iff.2
    ⟨⟨isOrthProj_rightProj hs.orthV₀, isOrthProj_leftProj hs.orthU₀⟩,
      ⟨isOrthProj_leftProj hs.orthU₁, isOrthProj_rightProj hs.orthV₁⟩,
      leftProj_rightProj_comm U₁ V₁, ⟨odeSolution_kField hs.kSol, odeSolution_lField hs.lSol⟩,
      ⟨hs.yk_start, hs.yl_start⟩, hs.yk_cap, hs.yl_cap⟩,
    odeSolution_sField hs.sSol, hs.ys_start⟩

section Tube

variable {A : ℝ → Matrix m n ℝ} {a b ρ B : ℝ}

/-- **A step for the tube extension is a step for the field, if the step stays in the tube.**
The tube extension `tubeExt F A a b ρ` agrees with `F` on the tube of radius `ρ` around `A` over
`[a, b]`. If the three full-space trajectories of a step over `[t₀, t₁] ⊆ [a, b]` stay in the
tube, it does not matter which of the two fields drives the step. -/
theorem isStep_tubeExt_iff (ha : a ≤ t₀) (hb : t₁ ≤ b)
    (hK : ∀ t ∈ Ico t₀ t₁, ‖K t * V₀ᵀ - A t‖ ≤ ρ)
    (hLf : ∀ t ∈ Ico t₀ t₁, ‖U₀ * (Lf t)ᵀ - A t‖ ≤ ρ)
    (hS : ∀ t ∈ Ico t₀ t₁, ‖U₁ * S t * V₁ᵀ - A t‖ ≤ ρ) :
    IsStep (tubeExt F A a b ρ) t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S ↔
      IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S := by
  have hmem : ∀ t ∈ Ico t₀ t₁, t ∈ Icc a b := fun t ht => ⟨ha.trans ht.1, ht.2.le.trans hb⟩
  have ek : ∀ t ∈ Ico t₀ t₁, kField V₀ (tubeExt F A a b ρ) t (K t) = kField V₀ F t (K t) :=
    fun t ht => by simp only [kField, tubeExt_eq (hmem t ht) (hK t ht)]
  have el : ∀ t ∈ Ico t₀ t₁, lField U₀ (tubeExt F A a b ρ) t (Lf t) = lField U₀ F t (Lf t) :=
    fun t ht => by simp only [lField, tubeExt_eq (hmem t ht) (hLf t ht)]
  have es : ∀ t ∈ Ico t₀ t₁,
      sField U₁ V₁ (tubeExt F A a b ρ) t (S t) = sField U₁ V₁ F t (S t) :=
    fun t ht => by simp only [sField, tubeExt_eq (hmem t ht) (hS t ht)]
  exact ⟨fun h => ⟨h.orthU₀, h.orthV₀, h.kSol.congr_field ek, h.kStart, h.lSol.congr_field el,
      h.lStart, h.orthU₁, h.kCap, h.orthV₁, h.lCap, h.sSol.congr_field es, h.sStart⟩,
    fun h => ⟨h.orthU₀, h.orthV₀, h.kSol.congr_field fun t ht => (ek t ht).symm, h.kStart,
      h.lSol.congr_field fun t ht => (el t ht).symm, h.lStart, h.orthU₁, h.kCap, h.orthV₁,
      h.lCap, h.sSol.congr_field fun t ht => (es t ht).symm, h.sStart⟩⟩

/-- **Near the reference solution, the tube extension has the same steps as the field.** Let `F`
be bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`, and let
`[t₀, t₁] ⊆ [a, b]`. If the start value satisfies `‖U₀ S₀ V₀ᵀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, then
every step for either field stays in the tube, so the steps for `tubeExt F A a b ρ` are exactly
the steps for `F`. -/
theorem isStep_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    IsStep (tubeExt F A a b ρ) t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S ↔
      IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S := by
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (U₀ * S₀ * V₀ᵀ - A t₀)]
  have h2 : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ := by linarith
  have key : ∀ G : ℝ → Matrix m n ℝ → Matrix m n ℝ, IsBoundedOnTube G A a b ρ B →
      ODESolution G A t₀ t₁ → IsStep G t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S →
      (∀ t ∈ Ico t₀ t₁, ‖K t * V₀ᵀ - A t‖ ≤ ρ) ∧ (∀ t ∈ Ico t₀ t₁, ‖U₀ * (Lf t)ᵀ - A t‖ ≤ ρ) ∧
        ∀ t ∈ Ico t₀ t₁, ‖U₁ * S t * V₁ᵀ - A t‖ ≤ ρ := fun G hGB hGA hs =>
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
    exact (isStep_tubeExt_iff ha hb hK hLf hS).1 hs
  · intro hs
    obtain ⟨hK, hLf, hS⟩ := key F hFB hA hs
    exact (isStep_tubeExt_iff ha hb hK hLf hS).2 hs

/-- The statement of `isStep_tubeExt_iff_of_near` for the step relation: near the reference
solution, `tubeExt F A a b ρ` and `F` have the same BUG steps. -/
theorem stepRel_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    stepRel (tubeExt F A a b ρ) r t₀ t₁ Y₀ Y₁ ↔ stepRel F r t₀ t₁ Y₀ Y₁ := by
  constructor
  · rintro ⟨U₀, S₀, V₀, U₁, V₁, K, Lf, S, rfl, hs, rfl⟩
    exact ((isStep_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 hs).stepRel
  · rintro ⟨U₀, S₀, V₀, U₁, V₁, K, Lf, S, rfl, hs, rfl⟩
    exact ((isStep_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).2 hs).stepRel

end Tube

end Rel

/-! ### Normal bounds and the local error -/

section Error

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {U₀ U₁ : Matrix m (Fin r) ℝ}
  {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ V₁ : Matrix n (Fin r) ℝ} {K : ℝ → Matrix m (Fin r) ℝ}
  {Lf : ℝ → Matrix n (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {Y₀ Y₁ : Matrix m n ℝ}
  {L B ε H : ℝ}

/-- A factor step whose results of the K-step and of the L-step satisfy the two normal bounds is
a step of the abstract integrator with normal bound `ε` (`IsBUGStep`). This restates
`MatrixBUG.IsStep.isBUGStep_of_normal` as a consequence of `MatrixBUG.IsStep.isBUGStepCore`. -/
example (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S)
    (hεK : ∀ t ∈ Icc t₀ t₁, ‖(1 - U₁ * U₁ᵀ) * F t (K t₁ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hεL : ∀ t ∈ Icc t₀ t₁, ‖(1 - U₀ * U₀ᵀ) * F t (U₀ * (Lf t₁)ᵀ) * (1 - V₁ * V₁ᵀ)‖ ≤ ε) :
    IsBUGStep F ε (leftProj U₀) (rightProj V₀) (leftProj U₁) (rightProj V₁) t₀ t₁
      (U₀ * S₀ * V₀ᵀ) (fun t => K t * V₀ᵀ) (fun t => U₀ * (Lf t)ᵀ) (fun t => U₁ * S t * V₁ᵀ) :=
  hs.isBUGStepCore.isBUGStep
    (fun t ht => by rw [one_sub_leftProj_one_sub_rightProj_apply]; exact hεK t ht)
    (fun t ht => by rw [one_sub_rightProj_one_sub_leftProj_apply]; exact hεL t ht)

/-- **Normal bound at the result of the K-step.** The result `K(t₁) V₀ᵀ` of the K-step has the
orthonormal factorization `U₁ (U₁ᵀ K(t₁)) V₀ᵀ`. Hence a bound `ε` for the normal part of `F` at
factored points of a region `D` applies to it whenever `(t, K(t₁) V₀ᵀ)` lies in `D`. -/
theorem IsStep.norm_kNormal_le {D : Set (ℝ × Matrix m n ℝ)}
    (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S) (hε : FactoredNormalBoundOn F r D ε) {t : ℝ}
    (hmem : (t, K t₁ * V₀ᵀ) ∈ D) :
    ‖(1 - U₁ * U₁ᵀ) * F t (K t₁ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε := by
  have hK : K t₁ * V₀ᵀ = U₁ * (U₁ᵀ * K t₁) * V₀ᵀ := by rw [← Matrix.mul_assoc, hs.kCap]
  have h := hε t U₁ V₀ (U₁ᵀ * K t₁) hs.orthU₁ hs.orthV₀ (by rwa [← hK])
  rwa [← hK] at h

/-- **Normal bound at the result of the L-step.** The result `U₀ L(t₁)ᵀ` of the L-step has the
orthonormal factorization `U₀ (L(t₁)ᵀ V₁) V₁ᵀ`. Hence a bound `ε` for the normal part of `F` at
factored points of a region `D` applies to it whenever `(t, U₀ L(t₁)ᵀ)` lies in `D`. -/
theorem IsStep.norm_lNormal_le {D : Set (ℝ × Matrix m n ℝ)}
    (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S) (hε : FactoredNormalBoundOn F r D ε) {t : ℝ}
    (hmem : (t, U₀ * (Lf t₁)ᵀ) ∈ D) :
    ‖(1 - U₀ * U₀ᵀ) * F t (U₀ * (Lf t₁)ᵀ) * (1 - V₁ * V₁ᵀ)‖ ≤ ε := by
  have hT : (Lf t₁)ᵀ * V₁ * V₁ᵀ = (Lf t₁)ᵀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hs.lCap
  have hL : U₀ * (Lf t₁)ᵀ = U₀ * ((Lf t₁)ᵀ * V₁) * V₁ᵀ := by rw [Matrix.mul_assoc U₀, hT]
  have h := hε t U₀ V₁ ((Lf t₁)ᵀ * V₁) hs.orthU₀ hs.orthV₁ (by rwa [← hL])
  rwa [← hL] at h

/-- **Local error of a matrix BUG step, pointwise normal bounds.** Let `F` be `L`-Lipschitz and
bounded by `B`, and let the normal part of `F` be at most `ε` at the results `K(t₁) V₀ᵀ` and
`U₀ L(t₁)ᵀ` of the K-step and of the L-step, for all times of the step. Then the result
`U₁ S(t₁) V₁ᵀ` differs from the exact solution through `(t₀, U₀ S₀ V₀ᵀ)` by at most
`(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))`, where `c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H` and `H` is any
bound for the step size [CerutiLubich2022, Lemma 4]. -/
theorem IsStep.hasLocalError (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S)
    (hεK : ∀ t ∈ Icc t₀ t₁, ‖(1 - U₁ * U₁ᵀ) * F t (K t₁ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hεL : ∀ t ∈ Icc t₀ t₁, ‖(1 - U₀ * U₀ᵀ) * F t (U₀ * (Lf t₁)ᵀ) * (1 - V₁ * V₁ᵀ)‖ ≤ ε)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (h01 : t₀ ≤ t₁)
    (hH : t₁ - t₀ ≤ H) :
    HasLocalError F t₀ t₁ (U₀ * S₀ * V₀ᵀ) (U₁ * S t₁ * V₁ᵀ)
      ((t₁ - t₀) * (bugC₁ L H * ε + bugC₂ L B H * (t₁ - t₀))) :=
  hs.isBUGStepCore.hasLocalError
    (fun t ht => by rw [one_sub_leftProj_one_sub_rightProj_apply]; exact hεK t ht)
    (fun t ht => by rw [one_sub_rightProj_one_sub_leftProj_apply]; exact hεL t ht)
    hF hL hB h01 hH

/-- **Local error of the matrix BUG step relation, global hypotheses.** If `F` is `L`-Lipschitz
and bounded by `B` and its normal part is at most `ε` at all rank-`r` points
(`MatrixBUG.FactoredNormalBound`), then every step of `MatrixBUG.stepRel` over `[t₀, t₁]` with
`t₁ - t₀ ≤ H` has local error at most `(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))` with `c₁ = bugC₁ L H`
and `c₂ = bugC₂ L B H`. -/
theorem stepRel.hasLocalError (h : stepRel F r t₀ t₁ Y₀ Y₁) (hε : FactoredNormalBound F r ε)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (h01 : t₀ ≤ t₁)
    (hH : t₁ - t₀ ≤ H) :
    HasLocalError F t₀ t₁ Y₀ Y₁ ((t₁ - t₀) * (bugC₁ L H * ε + bugC₂ L B H * (t₁ - t₀))) := by
  obtain ⟨U₀, S₀, V₀, U₁, V₁, K, Lf, S, rfl, hs, rfl⟩ := h
  have hε' := factoredNormalBound_iff_univ.1 hε
  exact hs.hasLocalError (fun t _ => hs.norm_kNormal_le hε' (mem_univ _))
    (fun t _ => hs.norm_lNormal_le hε' (mem_univ _)) hF hL hB h01 hH

/-- The matrix BUG step relation has local error `(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))` on the whole
space, in the form `StepRel.HasLocalErrorOn` of `LeanDLRA/Integrators/Defs.lean`; here the
constants `c₁ = bugC₁ L (t₁ - t₀)` and `c₂ = bugC₂ L B (t₁ - t₀)` are taken at the step size. -/
theorem stepRel_hasLocalErrorOn (hε : FactoredNormalBound F r ε) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) :
    (stepRel F r).HasLocalErrorOn F univ fun t₀ t₁ =>
      (t₁ - t₀) * (bugC₁ L (t₁ - t₀) * ε + bugC₂ L B (t₁ - t₀) * (t₁ - t₀)) :=
  fun _ _ _ _ h01 _ h => h.hasLocalError hε hF hL hB h01 le_rfl

/-- The local error bound `MatrixBUG.IsStep.local_error_le` of
`LeanDLRA/Integrators/Matrix/BUG.lean` is `MatrixBUG.stepRel.hasLocalError` applied to the
exact solution `A` through the start value. -/
example {h : ℝ} {A : ℝ → Matrix m n ℝ} (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S)
    (hε : FactoredNormalBound F r ε) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hhH : h ≤ H)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖U₁ * S t₁ * V₁ᵀ - A t₁‖ ≤ h * (bugC₁ L H * ε + bugC₂ L B H * h) := by
  have hd : t₁ - t₀ = h := by rw [ht₁]; ring
  have key := hs.stepRel.hasLocalError hε hF hL hB (by linarith) (hd.le.trans hhH) A hA hA₀
  rwa [hd] at key

section Tube

variable {A : ℝ → Matrix m n ℝ} {a b ρ : ℝ}

/-- **Local error of a matrix BUG step near a reference solution.** Let `F` be `L`-Lipschitz and
bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`, and let the normal
part of `F` be at most `ε` at the rank-`r` points of this tube. If the step over
`[t₀, t₁] ⊆ [a, b]` has size `t₁ - t₀ ≤ H` and its start value satisfies
`‖U₀ S₀ V₀ᵀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, then its result differs from the exact solution
through the start value by at most `(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))` with `c₁ = bugC₁ L H` and
`c₂ = bugC₂ L B H`. Nothing is assumed about `F` outside the tube. -/
theorem IsStep.hasLocalError_of_tube (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hH : t₁ - t₀ ≤ H)
    (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ (U₀ * S₀ * V₀ᵀ) (U₁ * S t₁ * V₁ᵀ)
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

/-- **Local error of the matrix BUG step relation near a reference solution.** Under the
hypotheses of `MatrixBUG.IsStep.hasLocalError_of_tube`, stated for the start value `Y₀`, every
step of `MatrixBUG.stepRel` from `Y₀` has local error at most `(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))`
with `c₁ = bugC₁ L H` and `c₂ = bugC₂ L B H`. -/
theorem stepRel.hasLocalError_of_tube (h : stepRel F r t₀ t₁ Y₀ Y₁)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hH : t₁ - t₀ ≤ H)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Y₁ ((t₁ - t₀) * (bugC₁ L H * ε + bugC₂ L B H * (t₁ - t₀))) := by
  obtain ⟨U₀, S₀, V₀, U₁, V₁, K, Lf, S, rfl, hs, rfl⟩ := h
  exact hs.hasLocalError_of_tube hε hFL hL hFB hB ha hb h01 hH hA hsmall

end Tube

/-- The step relation is satisfiable for a nonzero field: for every constant field `C` and every
start value `U₀ S₀ V₀ᵀ` with orthonormal `U₀`, `V₀` there is a BUG step, and its local error is
controlled by `‖C‖`, since `MatrixBUG.FactoredNormalBound (fun _ _ => C) r ‖C‖` holds. -/
example (C : Matrix m n ℝ) {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁) {U₀ : Matrix m (Fin r) ℝ}
    (S₀ : Matrix (Fin r) (Fin r) ℝ) {V₀ : Matrix n (Fin r) ℝ} (hU₀ : U₀ᵀ * U₀ = 1)
    (hV₀ : V₀ᵀ * V₀ = 1) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) :
    ∃ Y₁, stepRel (fun _ _ => C) r t₀ t₁ (U₀ * S₀ * V₀ᵀ) Y₁ ∧
      HasLocalError (fun _ _ => C) t₀ t₁ (U₀ * S₀ * V₀ᵀ) Y₁
        ((t₁ - t₀) * (bugC₁ 0 (t₁ - t₀) * ‖C‖ + bugC₂ 0 ‖C‖ (t₁ - t₀) * (t₁ - t₀))) := by
  have hF : IsLipschitzField (fun (_ : ℝ) (_ : Matrix m n ℝ) => C) 0 := fun _ _ _ => by simp
  have hB : IsBoundedField (fun (_ : ℝ) (_ : Matrix m n ℝ) => C) ‖C‖ := fun _ _ => le_rfl
  obtain ⟨U₁, V₁, K, Lf, S, hs⟩ :=
    exists_isStep hF hB (fun _ => continuous_const) h01 S₀ hU₀ hV₀ hrm hrn
  exact ⟨_, hs.stepRel,
    hs.stepRel.hasLocalError (factoredNormalBound_const C r) hF le_rfl hB h01 le_rfl⟩

end Error

end MatrixBUG

end LeanDLRA
