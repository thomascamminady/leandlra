import LeanDLRA.Integrators.Matrix.ParallelBUG
import LeanDLRA.Integrators.Matrix.KSLRun

/-!
# The fixed-rank parallel BUG step as a step relation

The parallel basis-update & Galerkin (BUG) integrator of Ceruti, Kusch and Lubich advances a
rank-`r` matrix `Y₀ = U₀ S₀ V₀ᵀ` over a time step `[t₀, t₁]` by three substeps that all start
from `Y₀` and can be computed at the same time: a K-step with the old row basis `V₀`, an L-step
with the old column basis `U₀`, and an S-step with both old bases. The results are assembled in
the bases augmented by the new directions found in the K- and L-step. This gives a matrix `Ŷ₁`
of rank at most `2 r`, which is then truncated. The predicate `MatrixParallelBUG.IsStep` of
`LeanDLRA/Integrators/Matrix/ParallelBUG.lean` describes the three substeps and the new
directions at the level of the factors, and `MatrixParallelBUG.augmented` is `Ŷ₁`.

This file states the step on the level of the matrices themselves, as a relation between the old
value `Y₀` and the new value `Y₁`, for the integrator with a fixed rank `r`: the result `Ŷ₁` is
truncated to a best approximation of rank at most `r`. It proves the local error bound of this
step in the form `HasLocalError` used by the convergence theorems of
`LeanDLRA/Integrators/Tube.lean` and `LeanDLRA/Integrators/Method.lean`.

The step relations contain the algorithm only. The size `ε` of the normal part of the vector
field, the Lipschitz constant and the bound of the field are hypotheses of the error theorems,
not part of the step.

## Main definitions

* `MatrixParallelBUG.augmentedRel F r`: the step without truncation.
  `augmentedRel F r t₀ t₁ Y₀ Ŷ₁` says that `Ŷ₁` is the assembled result of the three substeps
  over `[t₀, t₁]` started from some factorization `Y₀ = U₀ S₀ V₀ᵀ` with orthonormal `U₀`, `V₀`.
* `MatrixParallelBUG.stepRel F r`: the step relation of the fixed-rank parallel BUG integrator.
  `stepRel F r t₀ t₁ Y₀ Y₁` says that `Y₁` has rank at most `r` and is as close to a result `Ŷ₁`
  of the step without truncation as a matrix of rank at most `r` can be.

## Main results

* `distLR_flow_le_of_tube`: an exact solution that starts at a matrix of rank at most `r` near a
  reference solution is, after time `t₁ - t₀`, within `(t₁ - t₀) (10 L B (t₁ - t₀) + ε)` of the
  matrices of rank at most `r`. This is why truncation to rank `r` costs no more than the step
  itself.
* `MatrixParallelBUG.IsStep.augmentedRel`, `MatrixParallelBUG.IsStep.stepRel`: a step with any
  choice of new directions is a step of the relations.
* `MatrixParallelBUG.isRun_stepRel_of_isStep`: a chain of factor steps, each followed by a best
  approximation of rank at most `r`, is a run of `MatrixParallelBUG.stepRel`.
* `MatrixParallelBUG.IsStep.norm_sub_lt_of_near`: if the start value satisfies
  `‖U₀ S₀ V₀ᵀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, the three substeps stay in the tube of radius `ρ`
  around the reference solution `A`.
* `MatrixParallelBUG.isStep_tubeExt_iff_of_near`,
  `MatrixParallelBUG.augmentedRel_tubeExt_iff_of_near`,
  `MatrixParallelBUG.stepRel_tubeExt_iff_of_near`: near the reference solution, a step for the
  tube extension `tubeExt F A a b ρ` is the same as a step for `F`.
* `MatrixParallelBUG.IsStep.hasLocalError_of_tube`,
  `MatrixParallelBUG.augmentedRel.hasLocalError_of_tube`: the step without truncation has local
  error `(t₁ - t₀) (7 L B (t₁ - t₀) + ε)` when the field is Lipschitz and bounded and its normal
  part is small on a tube around a reference solution.
* `MatrixParallelBUG.stepRel.hasLocalError_of_tube`: the fixed-rank step has local error
  `(t₁ - t₀) (24 L B (t₁ - t₀) + 3 ε)` under the same hypotheses and continuity of the field on
  the tube.

## Implementation notes

In the relations the new directions are the columns of the complementary projectors
`1 - U₀ U₀ᵀ` and `1 - V₀ V₀ᵀ`. This is no restriction: the assembled result does not depend on
the choice of the new directions (`MatrixParallelBUG.augmented_eq_parallelBUG`), and with this
choice no assumption on the dimensions is needed. In a computation one uses `r` orthonormal
columns found by a QR factorization; `MatrixParallelBUG.IsStep.augmentedRel` covers this case.

The three substeps all start at `Y₀`, so each of them stays in the tube if
`‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`. For integrators whose substeps follow one another the factor
is `4` (`MatrixKSL.IsStep.norm_sub_lt_of_near`).

The truncation is a best approximation, as computed by a truncated singular value decomposition.
A truncation with a prescribed tolerance leads to a matrix whose rank is not known in advance;
the error of such a truncation enters the error bound as an additional term
(`MatrixParallelBUG.IsStep.local_error_truncated`).

The bound for the truncation uses a projector-splitting step from the same start value as a
comparison matrix of rank at most `r` (`MatrixKSL.exists_stepRel`). For this step to exist, the
field has to be continuous in time. This is the only place where continuity of the field enters
the local error.

## References

* G. Ceruti, J. Kusch, Ch. Lubich, *A parallel rank-adaptive integrator for dynamical low-rank
  approximation*, arXiv:2304.05660 (SIAM J. Sci. Comput. 2024), §3.1 and (4.1).
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

/-! ### An exact solution from a low-rank matrix stays near the low-rank matrices -/

section FlowDistance

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A Φ : ℝ → Matrix m n ℝ} {a b ρ L B ε t₀ t₁ : ℝ}

/-- **Distance of an exact solution to the low-rank matrices, near a reference solution.** Let
`F` be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around a solution `A` over
`[a, b]`, continuous there, with normal part at most `ε` at the factored rank-`r` points of the
tube. Let `Φ` be an exact solution on `[t₀, t₁] ⊆ [a, b]` whose start value has rank at most `r`
and satisfies `‖Φ t₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`. Then

  `distLR r (Φ t₁) ≤ (t₁ - t₀) (10 L B (t₁ - t₀) + ε)`.

The bound holds for every rank `r` and does not depend on the singular values of `Φ t₀`. It is
the version of `distLR_flow_le` for fields that are controlled only near `A`. The matrix of rank
at most `r` close to `Φ t₁` is the result of a projector-splitting step from `Φ t₀` for the
tube extension of `F`. -/
theorem distLR_flow_le_of_tube (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε)
    (hε₀ : 0 ≤ ε) (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A a b ρ)) (hAc : ContinuousOn A (Icc a b))
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hΦ : ODESolution F Φ t₀ t₁) (hrank : (Φ t₀).rank ≤ r)
    (hsmall : ‖Φ t₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    distLR r (Φ t₁) ≤ (t₁ - t₀) * (10 * L * B * (t₁ - t₀) + ε) := by
  have h0 : 0 ≤ t₁ - t₀ := sub_nonneg.2 h01
  have hnn : 0 ≤ (t₁ - t₀) * (10 * L * B * (t₁ - t₀) + ε) :=
    mul_nonneg h0 (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) hB) h0) hε₀)
  by_cases hrm : r ≤ Fintype.card m
  · by_cases hrn : r ≤ Fintype.card n
    · have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB h0
      have hρ : 0 ≤ ρ := by linarith [norm_nonneg (Φ t₀ - A t₀)]
      have hGL := isLipschitzField_tubeExt hFL hL hρ
      have hGB := isBoundedField_tubeExt hFB hB hρ
      have hGA : ODESolution (tubeExt F A a b ρ) A t₀ t₁ :=
        (odeSolution_tubeExt_iff ha hb fun t _ => by simpa using hρ).2 hA
      have hGΦ : ODESolution (tubeExt F A a b ρ) Φ t₀ t₁ :=
        hΦ.tubeExt_of_near hFB hB h0 ha hb (by ring) hA hsmall
      -- a projector-splitting step of the extended field from `Φ t₀`
      obtain ⟨Z, hZ⟩ := MatrixKSL.exists_stepRel hGL
        (fun x => (continuousOn_tubeExt hc hAc hρ x).mono (Icc_subset_Icc ha hb)) h01 hrm hrn
        hrank
      have hZr : Z.rank ≤ r := hZ.rank_le
      obtain ⟨U₀, S₀, V₀, U₁, Ŝ₁, K, S, Lf, hY, hs, rfl⟩ := hZ
      have hsm : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ := by rwa [← hY]
      have hmem := hs.mem_tubeSet_of_near (hGB.isBoundedOnTube A a b ρ) hB ha hb h01 hGA hsm
      have hn : ∀ t ∈ Icc t₀ t₁,
          ‖(1 - U₁ * U₁ᵀ) * tubeExt F A a b ρ t (U₁ * Ŝ₁ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε := by
        intro t ht
        have hm := hmem t ht
        rw [hs.kQR] at hm
        have ht' : t ∈ Icc a b := hm.1
        have hx : ‖U₁ * Ŝ₁ * V₀ᵀ - A t‖ ≤ ρ := hm.2
        rw [tubeExt_eq ht' hx]
        exact hε t U₁ V₀ Ŝ₁ hs.orthU₁ hs.orthV₀ hm
      have hloc := hs.hasLocalError hn hGL hL hGB h01 Φ hGΦ hY
      exact (distLR_le_norm_sub hZr).trans (by rwa [norm_sub_rev])
    · rw [distLR_eq_zero_of_card_width_le (by omega)]
      exact hnn
  · rw [distLR_eq_zero_of_card_height_le (by omega)]
    exact hnn

end FlowDistance

namespace MatrixParallelBUG

open MatrixKSL (kField lField odeSolution_kField odeSolution_lField)

/-! ### The step relations -/

section Rel

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}

/-- **The parallel BUG step without truncation, as a relation between matrices.**
`augmentedRel F r t₀ t₁ Y₀ Ŷ₁` holds if `Y₀ = U₀ S₀ V₀ᵀ` for some factors with `r` orthonormal
columns `U₀`, `V₀`, and `Ŷ₁` is the result assembled from a K-, L- and S-step for the field `F`
over `[t₀, t₁]` started from these factors (`MatrixParallelBUG.IsStep`,
`MatrixParallelBUG.augmented`). The matrix `Ŷ₁` has rank at most `2 r`. The new directions are
the columns of `1 - U₀ U₀ᵀ` and `1 - V₀ V₀ᵀ`; every other choice gives the same `Ŷ₁`
(`MatrixParallelBUG.IsStep.augmentedRel`). -/
def augmentedRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
      (K : ℝ → Matrix m (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ)
      (Sb : ℝ → Matrix (Fin r) (Fin r) ℝ),
      Y₀ = U₀ * S₀ * V₀ᵀ ∧ IsStep F t₀ t₁ U₀ S₀ V₀ (1 - U₀ * U₀ᵀ) (1 - V₀ * V₀ᵀ) K Lf Sb ∧
        Y₁ = augmented U₀ (1 - U₀ * U₀ᵀ) V₀ (1 - V₀ * V₀ᵀ) (Sb t₁) (K t₁) (Lf t₁)

/-- **The step of the fixed-rank parallel BUG integrator, as a relation between matrices.**
`stepRel F r t₀ t₁ Y₀ Y₁` holds if `Y₁` is a best approximation of rank at most `r` to a result
`Ŷ₁` of the step without truncation from `Y₀` (`MatrixParallelBUG.augmentedRel`): `Y₁` has rank
at most `r`, and `‖Y₁ - Ŷ₁‖` is the distance `distLR r Ŷ₁` of `Ŷ₁` to the matrices of rank at
most `r`. Such a `Y₁` is computed by a truncated singular value decomposition of `Ŷ₁`. -/
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ Yh : Matrix m n ℝ, augmentedRel F r t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧ ‖Y₁ - Yh‖ ≤ distLR r Yh

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {U₀ : Matrix m (Fin r) ℝ}
  {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {s s' : Type*} [Fintype s]
  [Fintype s'] {U₁ : Matrix m s ℝ} {V₁ : Matrix n s' ℝ} {K : ℝ → Matrix m (Fin r) ℝ}
  {Lf : ℝ → Matrix n (Fin r) ℝ} {Sb : ℝ → Matrix (Fin r) (Fin r) ℝ} {Y₀ Y₁ Yh : Matrix m n ℝ}

/-- **The new directions of a step can be replaced by the complementary projectors.** The
substeps of a parallel BUG step do not depend on the new directions `U₁`, `V₁`, and the columns
of `1 - U₀ U₀ᵀ` and `1 - V₀ V₀ᵀ` are orthogonal to `U₀`, `V₀` and capture everything. -/
theorem IsStep.compl_proj (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb) :
    IsStep F t₀ t₁ U₀ S₀ V₀ (1 - U₀ * U₀ᵀ) (1 - V₀ * V₀ᵀ) K Lf Sb :=
  ⟨hs.orthU₀, hs.orthV₀, hs.kSol, hs.kStart, hs.lSol, hs.lStart, hs.sSol, hs.sStart,
    (compl_capture_proj (k := Fin r) hs.orthU₀).1,
    (compl_capture_proj (k := Fin r) hs.orthU₀).2.2 _,
    (compl_capture_proj (k := Fin r) hs.orthV₀).1,
    (compl_capture_proj (k := Fin r) hs.orthV₀).2.2 _⟩

/-- The assembled result of a step is the same for the complementary projectors as for the new
directions `U₁`, `V₁` of the step. -/
theorem IsStep.augmented_compl_proj (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb) :
    augmented U₀ (1 - U₀ * U₀ᵀ) V₀ (1 - V₀ * V₀ᵀ) (Sb t₁) (K t₁) (Lf t₁) =
      augmented U₀ U₁ V₀ V₁ (Sb t₁) (K t₁) (Lf t₁) :=
  hs.compl_proj.augmented_eq.trans hs.augmented_eq.symm

/-- A parallel BUG step of the factors, with any new directions `U₁`, `V₁`, is a step of the
relation `augmentedRel`. -/
theorem IsStep.augmentedRel (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb) :
    augmentedRel F r t₀ t₁ (U₀ * S₀ * V₀ᵀ) (augmented U₀ U₁ V₀ V₁ (Sb t₁) (K t₁) (Lf t₁)) :=
  ⟨U₀, S₀, V₀, K, Lf, Sb, rfl, hs.compl_proj, hs.augmented_compl_proj.symm⟩

/-- A parallel BUG step of the factors, with any new directions `U₁`, `V₁`, followed by a best
approximation of rank at most `r`, is a step of the relation `stepRel`. -/
theorem IsStep.stepRel (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb) (hr : Y₁.rank ≤ r)
    (htr : ‖Y₁ - augmented U₀ U₁ V₀ V₁ (Sb t₁) (K t₁) (Lf t₁)‖ ≤
      distLR r (augmented U₀ U₁ V₀ V₁ (Sb t₁) (K t₁) (Lf t₁))) :
    stepRel F r t₀ t₁ (U₀ * S₀ * V₀ᵀ) Y₁ :=
  ⟨_, hs.augmentedRel, hr, htr⟩

/-- A parallel BUG step can only be started from a matrix of rank at most `r`. -/
theorem augmentedRel.rank_start_le (h : augmentedRel F r t₀ t₁ Y₀ Yh) : Y₀.rank ≤ r := by
  obtain ⟨U₀, S₀, V₀, K, Lf, Sb, rfl, -, -⟩ := h
  exact rank_mul_mul_transpose_le _ _ _

/-- **The truncation exists.** Every result of the step without truncation has a best
approximation of rank at most `r`, so it can be completed to a step of the fixed-rank
integrator. -/
theorem augmentedRel.exists_stepRel (h : augmentedRel F r t₀ t₁ Y₀ Yh) :
    ∃ Y₁, stepRel F r t₀ t₁ Y₀ Y₁ := by
  obtain ⟨Z, hZ, hd⟩ := exists_best_approx r Yh
  exact ⟨Z, Yh, h, hZ, by rw [norm_sub_rev, hd]⟩

/-- The result of a fixed-rank parallel BUG step has rank at most `r`. -/
theorem stepRel.rank_le (h : stepRel F r t₀ t₁ Y₀ Y₁) : Y₁.rank ≤ r := by
  obtain ⟨Yh, -, hr, -⟩ := h
  exact hr

/-- A fixed-rank parallel BUG step can only be started from a matrix of rank at most `r`. -/
theorem stepRel.rank_start_le (h : stepRel F r t₀ t₁ Y₀ Y₁) : Y₀.rank ≤ r := by
  obtain ⟨Yh, hYh, -, -⟩ := h
  exact hYh.rank_start_le

/-- All values of a run of the fixed-rank parallel BUG integrator have rank at most `r`,
provided the start value has. -/
theorem IsRun.rank_le {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → Matrix m n ℝ}
    (hY : IsRun (stepRel F r) τ N Y) (h0 : (Y 0).rank ≤ r) : ∀ n ≤ N, (Y n).rank ≤ r
  | 0, _ => h0
  | n + 1, hn => (hY.step n hn).rank_le

/-- **A chain of factor steps is a run.** Let the factors `(U j, Sm j, V j)` be advanced by
parallel BUG steps along the grid `τ`, with any new directions `W j`, `Z j`, and let the next
matrix `U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ` be a best approximation of rank at most `r` to
the assembled result of step `j`. Then the matrices `U j * Sm j * (V j)ᵀ` form a run of
`MatrixParallelBUG.stepRel`. -/
theorem isRun_stepRel_of_isStep {τ : ℕ → ℝ} {N : ℕ} {sU sV : ℕ → ℕ}
    {U : ℕ → Matrix m (Fin r) ℝ} {Sm : ℕ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℕ → Matrix n (Fin r) ℝ} {W : (j : ℕ) → Matrix m (Fin (sU j)) ℝ}
    {Z : (j : ℕ) → Matrix n (Fin (sV j)) ℝ} {K : ℕ → ℝ → Matrix m (Fin r) ℝ}
    {Lf : ℕ → ℝ → Matrix n (Fin r) ℝ} {Sb : ℕ → ℝ → Matrix (Fin r) (Fin r) ℝ}
    (hτ : IsGrid τ N)
    (hstep : ∀ j < N, IsStep F (τ j) (τ (j + 1)) (U j) (Sm j) (V j) (W j) (Z j) (K j) (Lf j)
      (Sb j))
    (htr : ∀ j < N, ‖U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ - augmented (U j) (W j) (V j) (Z j)
        (Sb j (τ (j + 1))) (K j (τ (j + 1))) (Lf j (τ (j + 1)))‖ ≤
      distLR r (augmented (U j) (W j) (V j) (Z j) (Sb j (τ (j + 1))) (K j (τ (j + 1)))
        (Lf j (τ (j + 1))))) :
    IsRun (stepRel F r) τ N fun j => U j * Sm j * (V j)ᵀ :=
  ⟨hτ, fun j hj => (hstep j hj).stepRel (rank_mul_mul_transpose_le _ _ _) (htr j hj)⟩

/-! ### Near the reference solution -/

section Tube

variable {A : ℝ → Matrix m n ℝ} {a b ρ B : ℝ}

/-- **The three substeps stay in the tube.** Let `F` be bounded by `B` on the tube of radius `ρ`
around a solution `A` over `[a, b]`, and let `[t₀, t₁] ⊆ [a, b]`. If the start value satisfies
`‖U₀ S₀ V₀ᵀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, then the trajectories `K(t) V₀ᵀ`, `U₀ L(t)ᵀ` and
`U₀ S(t) V₀ᵀ` of the three substeps stay strictly inside the tube. The three substeps start
from the same matrix `U₀ S₀ V₀ᵀ`, so the margin does not grow from one substep to the next. -/
theorem IsStep.norm_sub_lt_of_near (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    (∀ t ∈ Icc t₀ t₁, ‖K t * V₀ᵀ - A t‖ < ρ) ∧ (∀ t ∈ Icc t₀ t₁, ‖U₀ * (Lf t)ᵀ - A t‖ < ρ) ∧
      ∀ t ∈ Icc t₀ t₁, ‖U₀ * Sb t * V₀ᵀ - A t‖ < ρ := by
  have hK := (odeSolution_kField hs.kSol).near_of_comp_proj (Ψ := fun x => rightProj V₀ x)
    (isOrthProj_rightProj hs.orthV₀).norm_le hFB hB ha hb hA
    (by simpa only [hs.kStart] using hsmall)
  have eL : U₀ * (Lf t₀)ᵀ = U₀ * S₀ * V₀ᵀ := by
    rw [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hL := (odeSolution_lField hs.lSol).near_of_comp_proj (Ψ := fun x => leftProj U₀ x)
    (isOrthProj_leftProj hs.orthU₀).norm_le hFB hB ha hb hA (by simpa only [eL] using hsmall)
  have hS := (odeSolution_sField hs.sSol).near_of_comp_proj
    (Ψ := fun x => leftProj U₀ (rightProj V₀ x))
    (fun x => ((isOrthProj_leftProj hs.orthU₀).norm_le _).trans
      ((isOrthProj_rightProj hs.orthV₀).norm_le x))
    hFB hB ha hb hA (by simpa only [hs.sStart] using hsmall)
  exact ⟨fun t ht => (hK t ht).1, fun t ht => (hL t ht).1, fun t ht => (hS t ht).1⟩

/-- **A step for the tube extension is a step for the field, if the step stays in the tube.**
The tube extension `tubeExt F A a b ρ` agrees with `F` on the tube of radius `ρ` around `A` over
`[a, b]`. If the three full-space trajectories of a step over `[t₀, t₁] ⊆ [a, b]` stay in the
tube, it does not matter which of the two fields drives the step. -/
theorem isStep_tubeExt_iff (ha : a ≤ t₀) (hb : t₁ ≤ b)
    (hK : ∀ t ∈ Ico t₀ t₁, ‖K t * V₀ᵀ - A t‖ ≤ ρ)
    (hLf : ∀ t ∈ Ico t₀ t₁, ‖U₀ * (Lf t)ᵀ - A t‖ ≤ ρ)
    (hS : ∀ t ∈ Ico t₀ t₁, ‖U₀ * Sb t * V₀ᵀ - A t‖ ≤ ρ) :
    IsStep (tubeExt F A a b ρ) t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb ↔
      IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb := by
  have hmem : ∀ t ∈ Ico t₀ t₁, t ∈ Icc a b := fun t ht => ⟨ha.trans ht.1, ht.2.le.trans hb⟩
  have ek : ∀ t ∈ Ico t₀ t₁, kField V₀ (tubeExt F A a b ρ) t (K t) = kField V₀ F t (K t) :=
    fun t ht => by simp only [kField, tubeExt_eq (hmem t ht) (hK t ht)]
  have el : ∀ t ∈ Ico t₀ t₁, lField U₀ (tubeExt F A a b ρ) t (Lf t) = lField U₀ F t (Lf t) :=
    fun t ht => by simp only [lField, tubeExt_eq (hmem t ht) (hLf t ht)]
  have es : ∀ t ∈ Ico t₀ t₁,
      sField U₀ V₀ (tubeExt F A a b ρ) t (Sb t) = sField U₀ V₀ F t (Sb t) :=
    fun t ht => by simp only [sField, tubeExt_eq (hmem t ht) (hS t ht)]
  exact ⟨fun h => ⟨h.orthU₀, h.orthV₀, h.kSol.congr_field ek, h.kStart, h.lSol.congr_field el,
      h.lStart, h.sSol.congr_field es, h.sStart, h.perpU, h.capU, h.perpV, h.capV⟩,
    fun h => ⟨h.orthU₀, h.orthV₀, h.kSol.congr_field fun t ht => (ek t ht).symm, h.kStart,
      h.lSol.congr_field fun t ht => (el t ht).symm, h.lStart,
      h.sSol.congr_field fun t ht => (es t ht).symm, h.sStart, h.perpU, h.capU, h.perpV,
      h.capV⟩⟩

/-- **Near the reference solution, the tube extension has the same steps as the field.** Let `F`
be bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`, and let
`[t₀, t₁] ⊆ [a, b]`. If the start value satisfies `‖U₀ S₀ V₀ᵀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, then
every step for either field stays in the tube, so the steps for `tubeExt F A a b ρ` are exactly
the steps for `F`. -/
theorem isStep_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    IsStep (tubeExt F A a b ρ) t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb ↔
      IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb := by
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (U₀ * S₀ * V₀ᵀ - A t₀)]
  have key : ∀ G : ℝ → Matrix m n ℝ → Matrix m n ℝ, IsBoundedOnTube G A a b ρ B →
      ODESolution G A t₀ t₁ → IsStep G t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb →
      (∀ t ∈ Ico t₀ t₁, ‖K t * V₀ᵀ - A t‖ ≤ ρ) ∧
        (∀ t ∈ Ico t₀ t₁, ‖U₀ * (Lf t)ᵀ - A t‖ ≤ ρ) ∧
        ∀ t ∈ Ico t₀ t₁, ‖U₀ * Sb t * V₀ᵀ - A t‖ ≤ ρ := fun G hGB hGA hs => by
    obtain ⟨hK, hLf, hS⟩ := hs.norm_sub_lt_of_near hGB hB ha hb hGA hsmall
    exact ⟨fun t ht => (hK t (Ico_subset_Icc_self ht)).le,
      fun t ht => (hLf t (Ico_subset_Icc_self ht)).le,
      fun t ht => (hS t (Ico_subset_Icc_self ht)).le⟩
  constructor
  · intro hs
    obtain ⟨hK, hLf, hS⟩ := key _ ((isBoundedField_tubeExt hFB hB hρ).isBoundedOnTube A a b ρ)
      ((odeSolution_tubeExt_iff ha hb fun t _ => by simpa using hρ).2 hA) hs
    exact (isStep_tubeExt_iff ha hb hK hLf hS).1 hs
  · intro hs
    obtain ⟨hK, hLf, hS⟩ := key F hFB hA hs
    exact (isStep_tubeExt_iff ha hb hK hLf hS).2 hs

/-- The statement of `isStep_tubeExt_iff_of_near` for the step without truncation: near the
reference solution, the tube extension and the field have the same steps. -/
theorem augmentedRel_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    augmentedRel (tubeExt F A a b ρ) r t₀ t₁ Y₀ Yh ↔ augmentedRel F r t₀ t₁ Y₀ Yh := by
  constructor
  · rintro ⟨U₀, S₀, V₀, K, Lf, Sb, rfl, hs, rfl⟩
    exact ((isStep_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 hs).augmentedRel
  · rintro ⟨U₀, S₀, V₀, K, Lf, Sb, rfl, hs, rfl⟩
    exact ((isStep_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).2 hs).augmentedRel

/-- The statement of `isStep_tubeExt_iff_of_near` for the fixed-rank step relation: near the
reference solution, the tube extension and the field have the same steps. -/
theorem stepRel_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    stepRel (tubeExt F A a b ρ) r t₀ t₁ Y₀ Y₁ ↔ stepRel F r t₀ t₁ Y₀ Y₁ :=
  ⟨fun ⟨Yh, h, hr⟩ =>
      ⟨Yh, (augmentedRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 h, hr⟩,
    fun ⟨Yh, h, hr⟩ =>
      ⟨Yh, (augmentedRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).2 h, hr⟩⟩

end Tube

/-! ### Local error -/

section Error

variable {L B ε : ℝ}

/-- **Local error of the parallel BUG step without truncation.** For an `L`-Lipschitz field
bounded by `B` whose normal part at the start value is at most `ε` during the step, the
assembled result of a step differs from the exact solution through the start value by at most
`(t₁ - t₀) (7 L B (t₁ - t₀) + ε)`. This is `MatrixParallelBUG.IsStep.local_error` in the form
used by the convergence theorems. -/
theorem IsStep.hasLocalError (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb)
    (hε : ∀ t ∈ Ico t₀ t₁, ‖(1 - U₀ * U₀ᵀ) * F t (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (h01 : t₀ ≤ t₁) :
    HasLocalError F t₀ t₁ (U₀ * S₀ * V₀ᵀ) (augmented U₀ U₁ V₀ V₁ (Sb t₁) (K t₁) (Lf t₁))
      ((t₁ - t₀) * (7 * L * B * (t₁ - t₀) + ε)) :=
  fun _ hΦ hΦ₀ => hs.local_error hF hL hB hε h01 hΦ hΦ₀

variable {A : ℝ → Matrix m n ℝ} {a b ρ : ℝ}

/-- **Local error of the parallel BUG step without truncation near a reference solution.** Let
`F` be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around a solution `A` over
`[a, b]`, and let the normal part of `F` be at most `ε` at the factored rank-`r` points of this
tube. If the start value of a step over `[t₀, t₁] ⊆ [a, b]` satisfies
`‖U₀ S₀ V₀ᵀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, then the assembled result differs from the exact
solution through the start value by at most `(t₁ - t₀) (7 L B (t₁ - t₀) + ε)`. Nothing is
assumed about `F` outside the tube. -/
theorem IsStep.hasLocalError_of_tube (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ (U₀ * S₀ * V₀ᵀ) (augmented U₀ U₁ V₀ V₁ (Sb t₁) (K t₁) (Lf t₁))
      ((t₁ - t₀) * (7 * L * B * (t₁ - t₀) + ε)) := by
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (U₀ * S₀ * V₀ᵀ - A t₀)]
  have hext := (isStep_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).2 hs
  refine (hext.hasLocalError (fun t ht => ?_) (isLipschitzField_tubeExt hFL hL hρ) hL
    (isBoundedField_tubeExt hFB hB hρ) h01).of_tubeExt hFB hB ha hb h01 hA hsmall
  have ht' : t ∈ Icc a b := ⟨ha.trans ht.1, ht.2.le.trans hb⟩
  have hAt : ‖A t - A t₀‖ ≤ B * (t - t₀) :=
    hA.norm_sub_le (hFB.along hρ ha hb) t (Ico_subset_Icc_self ht)
  have hmono : B * (t - t₀) ≤ B * (t₁ - t₀) :=
    mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB
  have hx : ‖U₀ * S₀ * V₀ᵀ - A t‖ ≤ ρ := by
    have e : U₀ * S₀ * V₀ᵀ - A t = (U₀ * S₀ * V₀ᵀ - A t₀) - (A t - A t₀) := by abel
    rw [e]
    exact (norm_sub_le _ _).trans (by linarith)
  rw [tubeExt_eq ht' hx]
  exact hε t U₀ V₀ S₀ hs.orthU₀ hs.orthV₀ ⟨ht', hx⟩

/-- **Local error of the step without truncation, as a relation, near a reference solution.**
Under the hypotheses of `MatrixParallelBUG.IsStep.hasLocalError_of_tube`, stated for the start
value `Y₀`, every step of `MatrixParallelBUG.augmentedRel` from `Y₀` has local error at most
`(t₁ - t₀) (7 L B (t₁ - t₀) + ε)`. -/
theorem augmentedRel.hasLocalError_of_tube (h : augmentedRel F r t₀ t₁ Y₀ Yh)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Yh ((t₁ - t₀) * (7 * L * B * (t₁ - t₀) + ε)) := by
  obtain ⟨U₀, S₀, V₀, K, Lf, Sb, rfl, hs, rfl⟩ := h
  exact hs.hasLocalError_of_tube hε hFL hL hFB hB ha hb h01 hA hsmall

/-- **Local error of the fixed-rank parallel BUG step near a reference solution.** Let `F` be
continuous, `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around a solution `A`
over `[a, b]`, and let the normal part of `F` be at most `ε` at the factored rank-`r` points of
this tube. If the start value of a step over `[t₀, t₁] ⊆ [a, b]` satisfies
`‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, then the truncated result differs from the exact solution
`Φ` through the start value by at most `(t₁ - t₀) (24 L B (t₁ - t₀) + 3 ε)`.

The step without truncation contributes `(t₁ - t₀) (7 L B (t₁ - t₀) + ε)`. The truncation to
rank `r` is a best approximation, so it costs at most the distance of `Φ t₁` to the matrices of
rank at most `r` plus twice the error before truncation (`norm_bestTrunc_sub_le`), and this
distance is at most `(t₁ - t₀) (10 L B (t₁ - t₀) + ε)` (`distLR_flow_le_of_tube`). No truncation
tolerance appears. -/
theorem stepRel.hasLocalError_of_tube (h : stepRel F r t₀ t₁ Y₀ Y₁)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε) (hε₀ : 0 ≤ ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (hc : ContinuousOn (Function.uncurry F) (tubeSet A a b ρ))
    (hAc : ContinuousOn A (Icc a b)) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Y₁ ((t₁ - t₀) * (24 * L * B * (t₁ - t₀) + 3 * ε)) := by
  obtain ⟨Yh, hYh, -, htr⟩ := h
  intro Φ hΦ hΦ₀
  have h₁ := hYh.hasLocalError_of_tube hε hFL hL hFB hB ha hb h01 hA hsmall Φ hΦ hΦ₀
  have h₂ := distLR_flow_le_of_tube hε hε₀ hFL hL hFB hB hc hAc ha hb h01 hA hΦ
    (by rw [hΦ₀]; exact hYh.rank_start_le) (by rwa [hΦ₀])
  have h₃ := norm_bestTrunc_sub_le (A₁ := Φ t₁) htr
  have e : (t₁ - t₀) * (24 * L * B * (t₁ - t₀) + 3 * ε) =
      (t₁ - t₀) * (10 * L * B * (t₁ - t₀) + ε) +
        2 * ((t₁ - t₀) * (7 * L * B * (t₁ - t₀) + ε)) := by ring
  rw [e]
  linarith

end Error

end Rel

end MatrixParallelBUG

end LeanDLRA
