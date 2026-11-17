import LeanDLRA.Integrators.TuckerBUGCore
import LeanDLRA.Integrators.Matrix.ParallelBUGStep
import LeanDLRA.Randomized.RandomizedBUG

/-!
# The dynamical randomized SVD as a step relation

This file states one step of the dynamical randomized singular value decomposition (DRSVD) of
Carrel ([Carrel2025, Alg. 3]), in the variant with an augmented sketch, as a relation
between the old value `Y₀` and the new value `Y₁` (`StepRel`), and gives its locality and its
local error near a reference solution. The step at the level of orthogonal projectors and its
error analysis for fields that are Lipschitz and bounded everywhere are
`RandomizedBUG.IsDRSVDStep` and `RandomizedBUG.IsDRSVDStep.local_error_le` in
`LeanDLRA/Randomized/RandomizedBUG.lean`; runs of the integrator are in
`LeanDLRA/Randomized/DRSVDRun.lean`.

**The step.** Let `W` be a matrix with `k` orthonormal columns whose range contains the row
space of `Y₀` (`Y₀ W Wᵀ = Y₀`; the sketch `orth([V₀, Ω])` of a random matrix `Ω` augmented by
the row basis of `Y₀`). The B-step solves `B' = F(B Wᵀ) W` from `B(t₀) = Y₀ W`. A matrix `Q` with
`l` orthonormal columns captures `B(t₁)` (`Q Qᵀ B(t₁) = B(t₁)`). The C-step solves
`C' = F(Q Cᵀ)ᵀ Q` from `C(t₀) = Y₀ᵀ Q`, and the result before truncation is `Ŷ = Q C(t₁)ᵀ`
(`MatrixDRSVD.augmentedRel`). Then `Ŷ` is truncated to rank `r` by a best approximation
(`MatrixDRSVD.stepRel`). The sketch is a datum of the step: the relation holds for every sketch
with these properties, and no probability enters any statement.

## Main definitions

* `MatrixDRSVD.augmentedRel F k l`: the step without truncation, with a sketch basis of `k`
  columns and a range basis of `l` columns.
* `MatrixDRSVD.stepRel F r k l`: the step followed by a best approximation of rank at most `r`.

## Main results

* `MatrixDRSVD.isTuckerBUGStepCore_of_factors`: the full-space trajectories `B(t) Wᵀ` and
  `Q C(t)ᵀ` of a step form a step of the BUG integrator with one mode (`IsTuckerBUGStepCore` for
  `d = 1`): the B-step is a basis update with the old projector `X ↦ X W Wᵀ` and the new
  projector `X ↦ Q Qᵀ X`, the C-step is the Galerkin step for `X ↦ Q Qᵀ X`.
* `MatrixDRSVD.isDRSVDStep_of_factors`: with a bound on the normal part of the field at
  `B(t₁) Wᵀ`, the step is a step `RandomizedBUG.IsDRSVDStep` of the error analysis.
* `MatrixDRSVD.augmentedRel_tubeExt_iff_of_near`, `MatrixDRSVD.stepRel_tubeExt_iff_of_near`: if
  `‖Y₀ - A t₀‖ + 3 B (t₁ - t₀) < ρ`, the tube extension `tubeExt F A a b ρ` has the same steps
  as `F`.
* `MatrixDRSVD.augmentedRel.hasLocalError_of_tube`: the step without truncation has local error
  `(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))` with `c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`, if the normal part
  of `F` is at most `ε` at the factored points of the tube with `k` columns and `k ≤ l`.
* `MatrixDRSVD.stepRel.hasLocalError_of_tube`: with truncation to rank `r` the local error is
  `(t₁ - t₀) ((2 c₁ + 1) ε + (2 c₂ + 10 L B) (t₁ - t₀))`, if in addition the normal part is at
  most `ε` at the factored points with `r` columns. No truncation tolerance appears.

## Implementation notes

The two bridges are the whole connection with the existing theory: locality comes from the BUG
integrator with one mode (`isTuckerBUGStepCore_tubeExt_iff_of_near`, margin `(1 + 2) B (t₁ - t₀)`),
and the local error from `RandomizedBUG.IsDRSVDStep.local_error_le` for the globally Lipschitz
extension `tubeExt F A a b ρ`, transferred back to `F` by `HasLocalError.of_tubeExt`. Nothing of
the DRSVD analysis is proved again.

The normal part is needed at `B(t₁) Wᵀ`, which factors as `Q' (Q'ᵀ B(t₁)) Wᵀ` with a basis `Q'`
of `k` orthonormal columns inside the range of `Q` (`exists_orthonormal_capture_within`); this
is where `k ≤ l` is used, and why the bound at `k` columns suffices for a range basis with more
columns (`norm_normal_le_of_left`). The augmentation of the range basis by the column basis of
`Y₀` in the algorithm (`Q = orth([U₀, B(t₁)])`) is not required: the relation contains the
steps with and without it.

The truncation is a best approximation of rank at most `r`, as in `MatrixParallelBUG.stepRel`:
its cost is bounded by the distance of the exact solution to the matrices of rank at most `r`
(`distLR_flow_le_of_tube`) plus twice the error before truncation (`norm_bestTrunc_sub_le`).

## References

* B. Carrel, *Randomized methods for dynamical low-rank approximation*, [Carrel2025], §§2–3.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixDRSVD

open RandomizedBUG (IsDRSVDStep isDRSVDStep_matrix bStep_full cStep_full)

/-! ### The step relations -/

section Rel

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **The DRSVD step without truncation, as a relation between matrices**
([Carrel2025, Alg. 3], before the truncation, with an augmented sketch).
`augmentedRel F k l t₀ t₁ Y₀ Ŷ` holds if there are a sketch basis `W` with `k` orthonormal
columns whose range contains the row space of `Y₀`, a solution `B` of the B-step
`B' = F(B Wᵀ) W` with `B(t₀) = Y₀ W`, a range basis `Q` with `l` orthonormal columns that
captures `B(t₁)`, and a solution `C` of the C-step `C' = F(Q Cᵀ)ᵀ Q` with `C(t₀) = Y₀ᵀ Q`, such
that `Ŷ = Q C(t₁)ᵀ`. -/
def augmentedRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (k l : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Yh =>
    ∃ (W : Matrix n (Fin k) ℝ) (Q : Matrix m (Fin l) ℝ) (Bs : ℝ → Matrix m (Fin k) ℝ)
      (Cs : ℝ → Matrix n (Fin l) ℝ),
      Wᵀ * W = 1 ∧ Y₀ * W * Wᵀ = Y₀ ∧ ODESolution (fun t X => F t (X * Wᵀ) * W) Bs t₀ t₁ ∧
        Bs t₀ = Y₀ * W ∧ Qᵀ * Q = 1 ∧ Q * Qᵀ * Bs t₁ = Bs t₁ ∧
        ODESolution (fun t C => (F t (Q * Cᵀ))ᵀ * Q) Cs t₀ t₁ ∧ Cs t₀ = Y₀ᵀ * Q ∧
        Yh = Q * (Cs t₁)ᵀ

/-- **The DRSVD step with truncation to rank `r`, as a relation between matrices**
([Carrel2025, Alg. 3], with an augmented sketch). `stepRel F r k l t₀ t₁ Y₀ Y₁` holds
if `Y₁` is a best approximation of rank at most `r` to a result `Ŷ` of the step without
truncation (`MatrixDRSVD.augmentedRel`): `Y₁` has rank at most `r`, and `‖Y₁ - Ŷ‖` is the
distance `distLR r Ŷ` of `Ŷ` to the matrices of rank at most `r`. Such a `Y₁` is computed by a
truncated singular value decomposition of `Ŷ`. -/
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r k l : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ Yh : Matrix m n ℝ, augmentedRel F k l t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧ ‖Y₁ - Yh‖ ≤ distLR r Yh

variable {k l : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {Y₀ : Matrix m n ℝ}
  {W : Matrix n (Fin k) ℝ} {Q : Matrix m (Fin l) ℝ} {Bs : ℝ → Matrix m (Fin k) ℝ}
  {Cs : ℝ → Matrix n (Fin l) ℝ}

/-- **The DRSVD step is a BUG step with one mode.** For the data of a step, the full-space
trajectories `B(t) Wᵀ` and `Q C(t)ᵀ` form a step of the BUG integrator with one mode
(`IsTuckerBUGStepCore` for `d = 1`): the B-step is the basis update with the old projector
`X ↦ X W Wᵀ` (`RandomizedBUG.bStep_full`), which starts at `Y₀` because the sketch is augmented,
and whose result is captured by the new projector `X ↦ Q Qᵀ X`; the C-step is the Galerkin step
for this projector started at `Q Qᵀ Y₀` (`RandomizedBUG.cStep_full`). No bound on the field is
needed. -/
theorem isTuckerBUGStepCore_of_factors (hW : Wᵀ * W = 1) (haug : Y₀ * W * Wᵀ = Y₀)
    (hB : ODESolution (fun t X => F t (X * Wᵀ) * W) Bs t₀ t₁) (hB₀ : Bs t₀ = Y₀ * W)
    (hQ : Qᵀ * Q = 1) (hcap : Q * Qᵀ * Bs t₁ = Bs t₁)
    (hC : ODESolution (fun t C => (F t (Q * Cᵀ))ᵀ * Q) Cs t₀ t₁) (hC₀ : Cs t₀ = Y₀ᵀ * Q) :
    IsTuckerBUGStepCore F ![rightProj W] ![leftProj Q] t₀ t₁ Y₀ ![fun t => Bs t * Wᵀ]
      (fun t => Q * (Cs t)ᵀ) := by
  have e : modeProd ![(leftProj Q : Matrix m n ℝ →L[ℝ] Matrix m n ℝ)] = leftProj Q := by
    simp [modeProd]
  refine ⟨⟨fun i => ?_, fun i => ?_, fun i j x => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩,
    ?_, ?_⟩
  · fin_cases i
    exact isOrthProj_rightProj hW
  · fin_cases i
    exact isOrthProj_leftProj hQ
  · fin_cases i
    fin_cases j
    rfl
  · fin_cases i
    exact bStep_full hB
  · fin_cases i
    simp [hB₀, haug]
  · fin_cases i
    change Q * Qᵀ * (Bs t₁ * Wᵀ) = Bs t₁ * Wᵀ
    rw [← Matrix.mul_assoc, hcap]
  · rw [e]
    exact cStep_full hC
  · rw [e]
    simp only [hC₀, leftProj_apply, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]

/-- **The DRSVD step is a step of the error analysis.** For the data of a step and a bound `ε` on
the normal part of the field at the result `B(t₁) Wᵀ` of the B-step, the full-space trajectories
form a step `RandomizedBUG.IsDRSVDStep` with tolerance `0` and result `Q C(t₁)ᵀ`
(`RandomizedBUG.isDRSVDStep_matrix`). -/
theorem isDRSVDStep_of_factors {ε : ℝ} (hW : Wᵀ * W = 1) (haug : Y₀ * W * Wᵀ = Y₀)
    (hB : ODESolution (fun t X => F t (X * Wᵀ) * W) Bs t₀ t₁)
    (hB₀ : Bs t₀ = Y₀ * W) (hQ : Qᵀ * Q = 1) (hcap : Q * Qᵀ * Bs t₁ = Bs t₁)
    (hC : ODESolution (fun t C => (F t (Q * Cᵀ))ᵀ * Q) Cs t₀ t₁) (hC₀ : Cs t₀ = Y₀ᵀ * Q)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - leftProj Q) ((1 - rightProj W) (F t (Bs t₁ * Wᵀ)))‖ ≤ ε) :
    IsDRSVDStep F ε 0 (rightProj W) (leftProj Q) t₀ t₁ Y₀ (fun t => Bs t * Wᵀ)
      (fun t => Q * (Cs t)ᵀ) (Q * (Cs t₁)ᵀ) :=
  isDRSVDStep_matrix hW hQ hB hB₀ haug hcap hε hC hC₀ (by simp)

end Rel

/-! ### Properties of the relations -/

section Props

variable {m n : Type*} [Fintype m] [Fintype n] {r k l : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
  {t₀ t₁ : ℝ} {Y₀ Y₁ Yh : Matrix m n ℝ}

/-- A DRSVD step can only be started from a matrix of rank at most `k`: its row space lies in
the range of the sketch basis. -/
theorem augmentedRel.rank_start_le (h : augmentedRel F k l t₀ t₁ Y₀ Yh) : Y₀.rank ≤ k := by
  obtain ⟨W, -, -, -, -, haug, -⟩ := h
  rw [← haug]
  exact (Matrix.rank_mul_le_right _ _).trans (by simpa using Wᵀ.rank_le_card_height)

/-- The result of a DRSVD step without truncation has rank at most `l`. -/
theorem augmentedRel.rank_le (h : augmentedRel F k l t₀ t₁ Y₀ Yh) : Yh.rank ≤ l := by
  obtain ⟨-, Q, -, Cs, -, -, -, -, -, -, -, -, rfl⟩ := h
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa using Q.rank_le_card_width)

/-- The sketch basis has `k` orthonormal columns, so `k ≤ n`. -/
theorem augmentedRel.le_card_right (h : augmentedRel F k l t₀ t₁ Y₀ Yh) :
    k ≤ Fintype.card n := by
  obtain ⟨W, -, -, -, hW, -⟩ := h
  have h := W.rank_le_card_height
  rwa [rank_eq_card_of_transpose_mul_eq_one hW, Fintype.card_fin] at h

/-- The range basis has `l` orthonormal columns, so `l ≤ m`. -/
theorem augmentedRel.le_card_left (h : augmentedRel F k l t₀ t₁ Y₀ Yh) :
    l ≤ Fintype.card m := by
  obtain ⟨-, Q, -, -, -, -, -, -, hQ, -⟩ := h
  have h := Q.rank_le_card_height
  rwa [rank_eq_card_of_transpose_mul_eq_one hQ, Fintype.card_fin] at h

/-- **The truncation exists.** Every result of the step without truncation has a best
approximation of rank at most `r`, so it can be completed to a step with truncation. -/
theorem augmentedRel.exists_stepRel (h : augmentedRel F k l t₀ t₁ Y₀ Yh) :
    ∃ Y₁, stepRel F r k l t₀ t₁ Y₀ Y₁ := by
  obtain ⟨Z, hZ, hd⟩ := exists_best_approx r Yh
  exact ⟨Z, Yh, h, hZ, by rw [norm_sub_rev, hd]⟩

/-- The result of a DRSVD step with truncation to rank `r` has rank at most `r`. -/
theorem stepRel.rank_le (h : stepRel F r k l t₀ t₁ Y₀ Y₁) : Y₁.rank ≤ r := by
  obtain ⟨Yh, -, hr, -⟩ := h
  exact hr

/-- A DRSVD step with truncation can only be started from a matrix of rank at most `k`. -/
theorem stepRel.rank_start_le (h : stepRel F r k l t₀ t₁ Y₀ Y₁) : Y₀.rank ≤ k := by
  obtain ⟨Yh, hYh, -, -⟩ := h
  exact hYh.rank_start_le

end Props

/-! ### Near a reference solution: locality and the normal bound -/

section Tube

variable {m n : Type*} [Fintype m] [Fintype n] {r k l : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
  {t₀ t₁ : ℝ} {Y₀ Y₁ Yh : Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {a b ρ B : ℝ}

/-- **Near the reference solution, the tube extension has the same DRSVD steps as the field.**
Let `F` be bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`, and let
`[t₀, t₁] ⊆ [a, b]`. If `‖Y₀ - A t₀‖ + 3 B (t₁ - t₀) < ρ`, then for either field the
trajectories `B(t) Wᵀ` and `Q C(t)ᵀ` of a step stay in the tube (the margin of the BUG integrator
with one mode, `IsTuckerBUGStepCore.norm_galerkin_sub_lt_of_near`), so the relation
`augmentedRel` is the same for `tubeExt F A a b ρ` and for `F`. -/
theorem augmentedRel_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 3 * B * (t₁ - t₀) < ρ) :
    augmentedRel (tubeExt F A a b ρ) k l t₀ t₁ Y₀ Yh ↔ augmentedRel F k l t₀ t₁ Y₀ Yh := by
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (Y₀ - A t₀)]
  have h2 : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ := by linarith
  have h3 : ‖Y₀ - A t₀‖ + (((1 : ℕ) : ℝ) + 2) * B * (t₁ - t₀) < ρ := by
    norm_num
    linarith
  have hmem : ∀ t ∈ Ico t₀ t₁, t ∈ Icc a b := fun t ht => ⟨ha.trans ht.1, ht.2.le.trans hb⟩
  -- the trajectories of a step of a field `G` that is bounded on the tube stay in the tube
  have key : ∀ G : ℝ → Matrix m n ℝ → Matrix m n ℝ, IsBoundedOnTube G A a b ρ B →
      ODESolution G A t₀ t₁ → ∀ (W : Matrix n (Fin k) ℝ) (Q : Matrix m (Fin l) ℝ)
      (Bs : ℝ → Matrix m (Fin k) ℝ) (Cs : ℝ → Matrix n (Fin l) ℝ), Wᵀ * W = 1 →
      Y₀ * W * Wᵀ = Y₀ → ODESolution (fun t X => G t (X * Wᵀ) * W) Bs t₀ t₁ →
      Bs t₀ = Y₀ * W → Qᵀ * Q = 1 → Q * Qᵀ * Bs t₁ = Bs t₁ →
      ODESolution (fun t C => (G t (Q * Cᵀ))ᵀ * Q) Cs t₀ t₁ → Cs t₀ = Y₀ᵀ * Q →
      (∀ t ∈ Ico t₀ t₁, ‖Bs t * Wᵀ - A t‖ ≤ ρ) ∧ ∀ t ∈ Ico t₀ t₁, ‖Q * (Cs t)ᵀ - A t‖ ≤ ρ :=
    fun G hGB hGA W Q Bs Cs hW haug hBs hB₀ hQ hcap hC hC₀ => by
      have hs := isTuckerBUGStepCore_of_factors hW haug hBs hB₀ hQ hcap hC hC₀
      exact ⟨fun t ht => (hs.toBasisUpdate.norm_sub_lt_of_near hGB hB ha hb hGA h2 0 t
          (Ico_subset_Icc_self ht)).le,
        fun t ht => (hs.norm_galerkin_sub_lt_of_near hGB hB ha hb hGA h3 t
          (Ico_subset_Icc_self ht)).le⟩
  have hGB := (isBoundedField_tubeExt hFB hB hρ).isBoundedOnTube A a b ρ
  have hGA : ODESolution (tubeExt F A a b ρ) A t₀ t₁ :=
    (odeSolution_tubeExt_iff ha hb fun t _ => by simpa using hρ).2 hA
  constructor
  · rintro ⟨W, Q, Bs, Cs, hW, haug, hB', hB₀, hQ, hcap, hC, hC₀, rfl⟩
    obtain ⟨hK, hS⟩ := key _ hGB hGA W Q Bs Cs hW haug hB' hB₀ hQ hcap hC hC₀
    refine ⟨W, Q, Bs, Cs, hW, haug, hB'.congr_field fun t ht => ?_, hB₀, hQ, hcap,
      hC.congr_field fun t ht => ?_, hC₀, rfl⟩
    · simp only [tubeExt_eq (hmem t ht) (hK t ht)]
    · simp only [tubeExt_eq (hmem t ht) (hS t ht)]
  · rintro ⟨W, Q, Bs, Cs, hW, haug, hB', hB₀, hQ, hcap, hC, hC₀, rfl⟩
    obtain ⟨hK, hS⟩ := key F hFB hA W Q Bs Cs hW haug hB' hB₀ hQ hcap hC hC₀
    refine ⟨W, Q, Bs, Cs, hW, haug, hB'.congr_field fun t ht => ?_, hB₀, hQ, hcap,
      hC.congr_field fun t ht => ?_, hC₀, rfl⟩
    · simp only [tubeExt_eq (hmem t ht) (hK t ht)]
    · simp only [tubeExt_eq (hmem t ht) (hS t ht)]

/-- **Near the reference solution, the tube extension has the same DRSVD steps with truncation
as the field**: under the hypotheses of `MatrixDRSVD.augmentedRel_tubeExt_iff_of_near` the
relation `stepRel` is the same for `tubeExt F A a b ρ` and for `F`. The truncation does not
evaluate the field. -/
theorem stepRel_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 3 * B * (t₁ - t₀) < ρ) :
    stepRel (tubeExt F A a b ρ) r k l t₀ t₁ Y₀ Y₁ ↔ stepRel F r k l t₀ t₁ Y₀ Y₁ :=
  ⟨fun ⟨Yh, h, hr⟩ =>
      ⟨Yh, (augmentedRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 h, hr⟩,
    fun ⟨Yh, h, hr⟩ =>
      ⟨Yh, (augmentedRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).2 h, hr⟩⟩

/-- **The normal bound at the result of the B-step.** Let `Q` have `l` orthonormal columns and
capture `B(t₁)`, let `W` have `k` orthonormal columns, and `k ≤ l`. The point `B(t₁) Wᵀ` factors
as `Q' (Q'ᵀ B(t₁)) Wᵀ` with `k` orthonormal columns `Q'` inside the range of `Q`
(`exists_orthonormal_capture_within`). Hence a bound `ε` for the normal part of `F` at factored
points with `k` columns of a region `D` applies at `B(t₁) Wᵀ`, with the larger projector `Q Qᵀ`
in place of `Q' Q'ᵀ` (`norm_normal_le_of_left`), whenever `(t, B(t₁) Wᵀ)` lies in `D`. -/
theorem norm_bNormal_le [DecidableEq m] [DecidableEq n] {D : Set (ℝ × Matrix m n ℝ)} {ε : ℝ}
    {W : Matrix n (Fin k) ℝ} {Q : Matrix m (Fin l) ℝ} {Bt : Matrix m (Fin k) ℝ}
    (hW : Wᵀ * W = 1) (hQ : Qᵀ * Q = 1) (hcap : Q * Qᵀ * Bt = Bt) (hkl : k ≤ l)
    (hε : FactoredNormalBoundOn F k D ε) {t : ℝ} (hmem : (t, Bt * Wᵀ) ∈ D) :
    ‖(1 - leftProj Q) ((1 - rightProj W) (F t (Bt * Wᵀ)))‖ ≤ ε := by
  obtain ⟨Q', hQ', hcap', hin⟩ := MatrixBUG.exists_orthonormal_capture_within hQ hcap
    (by simpa using Bt.rank_le_card_width) (by simpa using hkl)
  have hB : Bt * Wᵀ = Q' * (Q'ᵀ * Bt) * Wᵀ := by rw [← Matrix.mul_assoc, hcap']
  have h := hε t Q' W (Q'ᵀ * Bt) hQ' hW (by rwa [← hB])
  rw [← hB] at h
  rw [one_sub_leftProj_one_sub_rightProj_apply]
  exact (MatrixBUG.norm_normal_le_of_left hQ hin W _).trans h

end Tube

/-! ### Local error near a reference solution -/

section Error

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r k l : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {Y₀ Y₁ Yh : Matrix m n ℝ}
  {A : ℝ → Matrix m n ℝ} {a b ρ L B ε H : ℝ}

/-- **Local error of the DRSVD step without truncation near a reference solution.** Let `F` be
`L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`,
and let the normal part of `F` be at most `ε` at the factored points of this tube with `k`
columns, `k ≤ l`. If the step over `[t₀, t₁] ⊆ [a, b]` has size `t₁ - t₀ ≤ H` and its start
value satisfies `‖Y₀ - A t₀‖ + 3 B (t₁ - t₀) < ρ`, then every step of
`MatrixDRSVD.augmentedRel F k l` from `Y₀` has local error at most
`(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))` with `c₁ = bugC₁ L H` and `c₂ = bugC₂ L B H`. This is
`RandomizedBUG.IsDRSVDStep.local_error_le` for a field that is Lipschitz and bounded only near
the reference solution: the step is a step of the globally Lipschitz extension
`tubeExt F A a b ρ` (`MatrixDRSVD.augmentedRel_tubeExt_iff_of_near`), where that theorem
applies. -/
theorem augmentedRel.hasLocalError_of_tube (h : augmentedRel F k l t₀ t₁ Y₀ Yh) (hkl : k ≤ l)
    (hε : FactoredNormalBoundOn F k (tubeSet A a b ρ) ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hH : t₁ - t₀ ≤ H)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖Y₀ - A t₀‖ + 3 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Yh ((t₁ - t₀) * (bugC₁ L H * ε + bugC₂ L B H * (t₁ - t₀))) := by
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (Y₀ - A t₀)]
  have h2 : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ := by linarith
  -- the normal bound at the result of the B-step, for the field and for its extension
  obtain ⟨W, Q, Bs, Cs, hW, haug, hB', hB₀, hQ, hcap, hC, hC₀, rfl⟩ := h
  have hmem : ∀ t ∈ Icc t₀ t₁, (t, Bs t₁ * Wᵀ) ∈ tubeSet A a b ρ :=
    (isTuckerBUGStepCore_of_factors hW haug hB' hB₀ hQ hcap hC
      hC₀).toBasisUpdate.mem_tubeSet_of_near hFB hB ha hb h01 hA h2 0
  have hεG : ∀ t ∈ Icc t₀ t₁,
      ‖(1 - leftProj Q) ((1 - rightProj W) (tubeExt F A a b ρ t (Bs t₁ * Wᵀ)))‖ ≤ ε :=
    fun t ht => by
      have e : tubeExt F A a b ρ t (Bs t₁ * Wᵀ) = F t (Bs t₁ * Wᵀ) :=
        tubeExt_eq (hmem t ht).1 (hmem t ht).2
      rw [e]
      exact norm_bNormal_le hW hQ hcap hkl hε (hmem t ht)
  -- the same factors form a step of the extension: its trajectories stay in the tube
  have hs := isTuckerBUGStepCore_of_factors hW haug hB' hB₀ hQ hcap hC hC₀
  have h3 : ‖Y₀ - A t₀‖ + (((1 : ℕ) : ℝ) + 2) * B * (t₁ - t₀) < ρ := by
    norm_num
    linarith
  have hBG : ODESolution (fun t X => tubeExt F A a b ρ t (X * Wᵀ) * W) Bs t₀ t₁ :=
    hB'.congr_field fun t ht => by
      have hK : ‖Bs t * Wᵀ - A t‖ ≤ ρ := (hs.toBasisUpdate.norm_sub_lt_of_near hFB hB ha hb hA
        h2 0 t (Ico_subset_Icc_self ht)).le
      simp only [tubeExt_eq ⟨ha.trans ht.1, ht.2.le.trans hb⟩ hK]
  have hCG : ODESolution (fun t C => (tubeExt F A a b ρ t (Q * Cᵀ))ᵀ * Q) Cs t₀ t₁ :=
    hC.congr_field fun t ht => by
      have hS : ‖Q * (Cs t)ᵀ - A t‖ ≤ ρ := (hs.norm_galerkin_sub_lt_of_near hFB hB ha hb hA h3
        t (Ico_subset_Icc_self ht)).le
      simp only [tubeExt_eq ⟨ha.trans ht.1, ht.2.le.trans hb⟩ hS]
  -- the local error of `RandomizedBUG.IsDRSVDStep` for the extension, transferred to `F`
  have hD := isDRSVDStep_of_factors hW haug hBG hB₀ hQ hcap hCG hC₀ hεG
  refine HasLocalError.of_tubeExt (fun Φ hΦ hΦ₀ => ?_) hFB hB ha hb h01 hA h2
  have hloc := hD.local_error_le (isLipschitzField_tubeExt hFL hL hρ) hL
    (isBoundedField_tubeExt hFB hB hρ) (by ring) (sub_nonneg.2 h01) hH hΦ hΦ₀
  simpa using hloc


/-- **Local error of the DRSVD step with truncation to rank `r` near a reference solution.** Let
`F` be continuous, `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around a solution
`A` over `[a, b]`, and let the normal part of `F` be at most `ε` at the factored points of this
tube with `r` and with `k` columns, `k ≤ l`. If the start value of a step over
`[t₀, t₁] ⊆ [a, b]`, `t₁ - t₀ ≤ H`, has rank at most `r` and satisfies
`‖Y₀ - A t₀‖ + 3 B (t₁ - t₀) < ρ`, then every step of `MatrixDRSVD.stepRel F r k l` from `Y₀`
differs from the exact solution `Φ` through the start value by at most

  `(t₁ - t₀) ((2 c₁ + 1) ε + (2 c₂ + 10 L B) (t₁ - t₀))`,

`c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`. The step without truncation contributes
`(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))` (`MatrixDRSVD.augmentedRel.hasLocalError_of_tube`). The
truncation is a best approximation, so it costs at most the distance of `Φ t₁` to the matrices
of rank at most `r` plus twice the error before truncation (`norm_bestTrunc_sub_le`), and this
distance is at most `(t₁ - t₀) (10 L B (t₁ - t₀) + ε)` (`distLR_flow_le_of_tube`). No truncation
tolerance appears. -/
theorem stepRel.hasLocalError_of_tube (h : stepRel F r k l t₀ t₁ Y₀ Y₁) (hkl : k ≤ l)
    (hY₀ : Y₀.rank ≤ r)
    (hε : ∀ s ∈ ({r, k} : Set ℕ), FactoredNormalBoundOn F s (tubeSet A a b ρ) ε) (hε₀ : 0 ≤ ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (hc : ContinuousOn (Function.uncurry F) (tubeSet A a b ρ))
    (hAc : ContinuousOn A (Icc a b)) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁)
    (hH : t₁ - t₀ ≤ H) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 3 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Y₁ ((t₁ - t₀) *
      ((2 * bugC₁ L H + 1) * ε + (2 * bugC₂ L B H + 10 * L * B) * (t₁ - t₀))) := by
  obtain ⟨Yh, hYh, -, htr⟩ := h
  intro Φ hΦ hΦ₀
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have h₁ := hYh.hasLocalError_of_tube hkl (hε k (Set.mem_insert_of_mem _ rfl)) hFL hL hFB hB
    ha hb h01 hH hA hsmall Φ hΦ hΦ₀
  have h₂ := distLR_flow_le_of_tube (hε r (Set.mem_insert _ _)) hε₀ hFL hL hFB hB hc hAc ha hb
    h01 hA hΦ (by rw [hΦ₀]; exact hY₀) (by rw [hΦ₀]; linarith)
  have h₃ := norm_bestTrunc_sub_le (A₁ := Φ t₁) htr
  have e : (t₁ - t₀) * ((2 * bugC₁ L H + 1) * ε + (2 * bugC₂ L B H + 10 * L * B) * (t₁ - t₀)) =
      (t₁ - t₀) * (10 * L * B * (t₁ - t₀) + ε) +
        2 * ((t₁ - t₀) * (bugC₁ L H * ε + bugC₂ L B H * (t₁ - t₀))) := by ring
  rw [e]
  linarith

end Error

end MatrixDRSVD

end LeanDLRA
