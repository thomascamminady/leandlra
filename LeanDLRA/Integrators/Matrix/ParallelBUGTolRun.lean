import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Integrators.MethodTolerance
import LeanDLRA.Integrators.Matrix.ParallelBUGRun
import LeanDLRA.Integrators.Matrix.LinearFieldExample

/-!
# The parallel rank-adaptive BUG integrator: step relation, runs and error bound

This file treats the parallel basis-update & Galerkin (BUG) integrator of Ceruti, Kusch and
Lubich [CerutiKuschLubich2024] with truncation by a tolerance, for a matrix differential equation
`Y' = F(t, Y)`. A step from `Y₀ = U₀ S₀ V₀ᵀ` solves the K-, L- and S-step in parallel, assembles
the result `Ŷ₁` of rank at most `2 r` in the bases augmented by the new directions
(`MatrixParallelBUG.augmentedRel`), and truncates it to a tolerance `ϑ`: `‖Y₁ - Ŷ₁‖ ≤ ϑ`. The rank
of the values is not fixed. The integrator with truncation to a fixed rank is in
`LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean`.

**Setting.** Let `A` be a solution of `Y' = F(t, Y)` on `[t₀, t₀ + N h]`. The field `F` is only
assumed to be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around `A`
(`DLRAProblem F A t₀ (t₀ + N h) ρ L B`), jointly continuous there, and to have a small normal
component at the factored matrices in the tube with `r` columns, for every number `r` of columns
from which a step may start (`FactoredNormalBoundOn F r _ ε`, one `ε` for all `r`). Nothing is
assumed about `F` outside the tube.

**Results.** Every run `Y 0, …, Y N` of the integrator with step size `h > 0` and
`‖Y 0 - A t₀‖ ≤ δ` satisfies (`MatrixParallelBUG.IsRun.norm_sub_le_of_adaptiveStepRel`)

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (7 L B h + ε) + T e^{L T} ϑ / h`,

which is the bound `C₀ δ + C₁ h + C₂ ε + C₃ ϑ / h` of [CerutiKuschLubich2024, Theorem 4.1] with
the constants of `MatrixParallelBUG.global_error_constants`, under hypotheses on the tube only.
For start factorizations with at least `r₀ ≤ m, n` columns a run exists from every start value
(`MatrixParallelBUG.adaptive_exists_run_norm_sub_le`) and satisfies

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} (δ + n ϑ) + T e^{L T} (7 L B h + ε)`,

if this bound with `N` in place of `n`, plus `2 B h`, is less than `ρ`. Since `n h ≤ T`, the term
`e^{L T} n ϑ` is at most `T e^{L T} ϑ / h`.

## Main definitions

* `MatrixParallelBUG.adaptiveStepRel F R ϑ`: the step with truncation by the tolerance `ϑ`. The
  start value is factored with `r` columns for some `r` in the set `R`.

## Main results

* `MatrixParallelBUG.augmentedRel.adaptiveStepRel_truncation`: the truncated singular value
  decomposition is a truncation by the tolerance.
* `MatrixParallelBUG.isRun_adaptiveStepRel_of_isStep`: a chain of factor steps
  (`MatrixParallelBUG.IsStep`) with ranks that change from step to step, each followed by a
  truncation within `ϑ`, is a run of the relation.
* `MatrixParallelBUG.adaptiveStepRel_tubeExt_iff_of_near`: if
  `‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, the tube extension `tubeExt F A a b ρ` has the same steps as
  `F`.
* `MatrixParallelBUG.exists_adaptiveStepRel_Ici`: with `R = Set.Ici r₀`, `r₀ ≤ m`, `r₀ ≤ n`, a
  step exists from every matrix.
* `MatrixParallelBUG.adaptiveStepRel.hasLocalError_of_tube`: the local error
  `(t₁ - t₀) (7 L B (t₁ - t₀) + ε) + ϑ`.
* `MatrixParallelBUG.isTubeLocal_adaptiveStepRel_Ici`: for `R = Set.Ici r₀` the integrator is a
  tube-local method (`StepMethod.IsTubeLocal`) with every matrix admissible and margin
  constant `2`.
* `MatrixParallelBUG.IsRun.norm_sub_le_of_adaptiveStepRel`: every run satisfies the error bound
  with the term `T e^{L T} ϑ / h`.
* `MatrixParallelBUG.adaptive_norm_sub_le_of_isStep`: the same bound for a chain of factor steps
  with ranks that change from step to step, the tube form of
  `MatrixParallelBUG.global_error_constants`.
* `MatrixParallelBUG.adaptive_exists_run_norm_sub_le`: a run exists and satisfies the error bound
  with the term `e^{L T} n ϑ`.

## Implementation notes

The relation is that of the rank-adaptive BUG integrator, `MatrixBUG.adaptiveStepRel`, with the
parallel step without truncation in place of the augmented BUG step. It carries the set `R` of
the numbers of columns of the start factorization for the same reason: the hypothesis
`FactoredNormalBoundOn F r D ε` concerns factorizations with exactly `r` columns. The truncation
clause contains every truncation within the tolerance, so the existence of a step is a weak
statement (the assembled matrix itself is a witness), and the error bounds hold for every step,
in particular for the truncated singular value decomposition that the algorithm uses.

The local error of a step is `h (7 L B h + ε) + ϑ`; the tolerance is not multiplied by the step
size. The run theorem with the term `e^{L T} n ϑ` is therefore an instance of
`StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_tol`. The bound for every run is
`IsRun.norm_sub_le_of_tube_uniformGrid` with the local error written as `h (7 L B h + ε + ϑ / h)`.
The margin constant `2` is that of the fixed-rank parallel integrator: the three substeps start
at the start value or at its Galerkin projection, and the truncation does not evaluate the
field.

## References

* [CerutiKuschLubich2024] G. Ceruti, J. Kusch, Ch. Lubich, *A parallel rank-adaptive integrator
  for dynamical low-rank approximation*, SIAM J. Sci. Comput. 46 (2024), arXiv:2304.05660,
  §3 and Theorem 4.1.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixParallelBUG

/-! ### The step relation -/

section Rel

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}

/-- **The step of the parallel rank-adaptive BUG integrator, as a relation between matrices**
[CerutiKuschLubich2024, §3]. `adaptiveStepRel F R ϑ t₀ t₁ Y₀ Y₁` holds if `Y₁` is within the
tolerance `ϑ` of an assembled result `Ŷ₁` of a parallel BUG step from `Y₀` over `[t₀, t₁]`
without truncation (`MatrixParallelBUG.augmentedRel`), where the start value is factored with
`r` columns for some `r` in the set `R`. The rank of `Y₁` is not restricted. The relation
contains every truncation with `‖Y₁ - Ŷ₁‖ ≤ ϑ`, in particular the truncated singular value
decomposition of `Ŷ₁` of any rank whose truncation error is at most `ϑ`, which is the one used
in the algorithm (`MatrixParallelBUG.augmentedRel.adaptiveStepRel_truncation`). -/
def adaptiveStepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (R : Set ℕ) (ϑ : ℝ) :
    StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ => ∃ r ∈ R, ∃ Yh : Matrix m n ℝ, augmentedRel F r t₀ t₁ Y₀ Yh ∧ ‖Y₁ - Yh‖ ≤ ϑ

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {R : Set ℕ} {ϑ t₀ t₁ : ℝ}
  {Y₀ Y₁ Yh : Matrix m n ℝ}

/-- An assembled result of a step without truncation and a matrix within the tolerance `ϑ` of
it form a step of the rank-adaptive integrator, for every set `R` that contains the number of
columns of the start factorization. -/
theorem augmentedRel.adaptiveStepRel (h : augmentedRel F r t₀ t₁ Y₀ Yh) (hr : r ∈ R)
    (hY₁ : ‖Y₁ - Yh‖ ≤ ϑ) : adaptiveStepRel F R ϑ t₀ t₁ Y₀ Y₁ :=
  ⟨r, hr, Yh, h, hY₁⟩

/-- A parallel BUG step of the factors, with any new directions `U₁`, `V₁`, followed by a
truncation within the tolerance `ϑ`, is a step of the relation `adaptiveStepRel` for every set
`R` that contains the number `r` of columns of `U₀` and `V₀`. -/
theorem IsStep.adaptiveStepRel {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ}
    {V₀ : Matrix n (Fin r) ℝ} {s s' : Type*} [Fintype s] [Fintype s'] {U₁ : Matrix m s ℝ}
    {V₁ : Matrix n s' ℝ} {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ}
    {Sb : ℝ → Matrix (Fin r) (Fin r) ℝ} (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb)
    (hr : r ∈ R) (htr : ‖Y₁ - augmented U₀ U₁ V₀ V₁ (Sb t₁) (K t₁) (Lf t₁)‖ ≤ ϑ) :
    adaptiveStepRel F R ϑ t₀ t₁ (U₀ * S₀ * V₀ᵀ) Y₁ :=
  hs.augmentedRel.adaptiveStepRel hr htr

/-- **The truncated singular value decomposition is a truncation by a tolerance.** If the
distance of the assembled result `Ŷ₁` to the matrices of rank at most `q` is at most `ϑ`, then
`Ŷ₁` truncated to its `q` largest singular values is a step of the rank-adaptive integrator: by
the Eckart–Young theorem (`EckartYoung.norm_sub_truncation_le`) the truncation error is this
distance. The algorithm takes the smallest such `q`. -/
theorem augmentedRel.adaptiveStepRel_truncation (h : augmentedRel F r t₀ t₁ Y₀ Yh) (hr : r ∈ R)
    {q : ℕ} (hq : distLR q Yh ≤ ϑ) :
    MatrixParallelBUG.adaptiveStepRel F R ϑ t₀ t₁ Y₀ (EckartYoung.truncation Yh q) := by
  have h1 : ‖Yh - EckartYoung.truncation Yh q‖ ≤ distLR q Yh :=
    le_distLR_iff.2 fun Z hZ => EckartYoung.norm_sub_truncation_le Yh hZ
  exact h.adaptiveStepRel hr (by rw [norm_sub_rev]; exact h1.trans hq)

/-- **Monotonicity of the step relation**: a step stays a step if the set of numbers of columns
and the tolerance are enlarged. -/
theorem adaptiveStepRel.mono {R' : Set ℕ} {ϑ' : ℝ} (h : adaptiveStepRel F R ϑ t₀ t₁ Y₀ Y₁)
    (hR : R ⊆ R') (hϑ : ϑ ≤ ϑ') : adaptiveStepRel F R' ϑ' t₀ t₁ Y₀ Y₁ := by
  obtain ⟨r, hr, Yh, hYh, htr⟩ := h
  exact ⟨r, hR hr, Yh, hYh, htr.trans hϑ⟩

/-- A step of the parallel rank-adaptive integrator starts from a matrix whose rank is at most
some element of `R`. -/
theorem adaptiveStepRel.exists_rank_start_le (h : adaptiveStepRel F R ϑ t₀ t₁ Y₀ Y₁) :
    ∃ r ∈ R, Y₀.rank ≤ r := by
  obtain ⟨r, hr, Yh, hYh, -⟩ := h
  exact ⟨r, hr, hYh.rank_start_le⟩

/-- **A chain of factor steps with changing ranks is a run.** Let the factors `(U j, Sm j, V j)`
with `rk j` columns be advanced by parallel BUG steps along the grid `τ`, with any new
directions `W j`, `Z j`, and let the next matrix `U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ` be within
the tolerance `ϑ` of the assembled result of step `j`. If every `rk j`, `j < N`, lies in `R`,
then the matrices `U j * Sm j * (V j)ᵀ` form a run of `MatrixParallelBUG.adaptiveStepRel F R ϑ`.
These are the hypotheses on the factors of `MatrixParallelBUG.global_error_paper`. -/
theorem isRun_adaptiveStepRel_of_isStep {τ : ℕ → ℝ} {N : ℕ} {rk sU sV : ℕ → ℕ}
    {U : (j : ℕ) → Matrix m (Fin (rk j)) ℝ} {Sm : (j : ℕ) → Matrix (Fin (rk j)) (Fin (rk j)) ℝ}
    {V : (j : ℕ) → Matrix n (Fin (rk j)) ℝ} {W : (j : ℕ) → Matrix m (Fin (sU j)) ℝ}
    {Z : (j : ℕ) → Matrix n (Fin (sV j)) ℝ} {K : (j : ℕ) → ℝ → Matrix m (Fin (rk j)) ℝ}
    {Lf : (j : ℕ) → ℝ → Matrix n (Fin (rk j)) ℝ}
    {Sb : (j : ℕ) → ℝ → Matrix (Fin (rk j)) (Fin (rk j)) ℝ}
    (hτ : IsGrid τ N) (hR : ∀ j < N, rk j ∈ R)
    (hstep : ∀ j < N, IsStep F (τ j) (τ (j + 1)) (U j) (Sm j) (V j) (W j) (Z j) (K j) (Lf j)
      (Sb j))
    (htr : ∀ j < N, ‖U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ - augmented (U j) (W j) (V j) (Z j)
      (Sb j (τ (j + 1))) (K j (τ (j + 1))) (Lf j (τ (j + 1)))‖ ≤ ϑ) :
    IsRun (adaptiveStepRel F R ϑ) τ N fun j => U j * Sm j * (V j)ᵀ :=
  ⟨hτ, fun j hj => (hstep j hj).adaptiveStepRel (hR j hj) (htr j hj)⟩

section Tube

variable {A : ℝ → Matrix m n ℝ} {a b ρ B : ℝ}

/-- **Near the reference solution, the tube extension has the same steps as the field.** Let
`F` be bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`, and let
`[t₀, t₁] ⊆ [a, b]`. If `‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, the relation `adaptiveStepRel` is the
same for `tubeExt F A a b ρ` and for `F`. The truncation does not evaluate the field. -/
theorem adaptiveStepRel_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    adaptiveStepRel (tubeExt F A a b ρ) R ϑ t₀ t₁ Y₀ Y₁ ↔ adaptiveStepRel F R ϑ t₀ t₁ Y₀ Y₁ :=
  ⟨fun ⟨r, hr, Yh, h, htr⟩ =>
      ⟨r, hr, Yh, (augmentedRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 h, htr⟩,
    fun ⟨r, hr, Yh, h, htr⟩ =>
      ⟨r, hr, Yh, (augmentedRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).2 h, htr⟩⟩

end Tube

end Rel

/-! ### Existence of steps and runs, and the integrator as a tube-local method -/

section Exists

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r r₀ : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L : ℝ} {R : Set ℕ} {ϑ t₀ t₁ : ℝ}

/-- **A step of the parallel rank-adaptive integrator exists** from every start value whose rank
is at most some `r ∈ R` with `r ≤ m`, `r ≤ n`, for every Lipschitz field that is continuous in
time on the step interval and every tolerance `ϑ ≥ 0`. The assembled matrix itself is a witness:
the relation contains every matrix within `ϑ` of it. -/
theorem exists_adaptiveStepRel (hF : IsLipschitzField F L)
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁) (hϑ : 0 ≤ ϑ)
    (hr : r ∈ R) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) : ∃ Y₁, adaptiveStepRel F R ϑ t₀ t₁ Y₀ Y₁ := by
  obtain ⟨Yh, hYh⟩ := exists_augmentedRel hF hc h01 hrm hrn hY₀
  exact ⟨Yh, hYh.adaptiveStepRel hr (by simpa using hϑ)⟩

/-- **With at least `r₀` columns, a step of the parallel rank-adaptive integrator exists from
every matrix.** Let `R = Set.Ici r₀` with `r₀ ≤ m` and `r₀ ≤ n`. For every Lipschitz field that
is continuous in time on the step interval, every tolerance `ϑ ≥ 0` and every start value `Y₀`
there is a step: a factorization of `Y₀` is padded with orthonormal columns to
`max (rank Y₀) r₀` columns, a number that lies in `R` and is at most `m` and `n`. For a larger
`r₀` there is no factorization with `r₀` orthonormal columns. -/
theorem exists_adaptiveStepRel_Ici (hF : IsLipschitzField F L)
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁) (hϑ : 0 ≤ ϑ)
    (hrm : r₀ ≤ Fintype.card m) (hrn : r₀ ≤ Fintype.card n) (Y₀ : Matrix m n ℝ) :
    ∃ Y₁, adaptiveStepRel F (Set.Ici r₀) ϑ t₀ t₁ Y₀ Y₁ :=
  exists_adaptiveStepRel hF hc h01 hϑ (r := max Y₀.rank r₀) (Set.mem_Ici.2 (le_max_right _ _))
    (max_le Y₀.rank_le_card_height hrm) (max_le Y₀.rank_le_card_width hrn) (le_max_left _ _)

/-- **Runs of the parallel rank-adaptive integrator exist.** If `F` is Lipschitz (globally) and
continuous in time on `[τ 0, τ N]`, `r₀ ≤ m`, `r₀ ≤ n` and `ϑ ≥ 0`, then on the grid `τ` there
is a run of `N` steps with tolerance `ϑ` from every start value, every step starting from a
factorization with at least `r₀` columns. No bound on the field is needed. -/
theorem adaptive_exists_run (hF : IsLipschitzField F L) {τ : ℕ → ℝ} {N : ℕ} (hτ : IsGrid τ N)
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc (τ 0) (τ N))) (hϑ : 0 ≤ ϑ)
    (hrm : r₀ ≤ Fintype.card m) (hrn : r₀ ≤ Fintype.card n) (Y₀ : Matrix m n ℝ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (adaptiveStepRel F (Set.Ici r₀) ϑ) τ N Y := by
  refine exists_isRun hτ Y₀ fun n hn Y _ _ => ?_
  have hsub : Icc (τ n) (τ (n + 1)) ⊆ Icc (τ 0) (τ N) :=
    Icc_subset_Icc (hτ.le_of_le n.zero_le hn.le) (hτ.le_of_le (Nat.succ_le_of_lt hn) le_rfl)
  exact exists_adaptiveStepRel_Ici hF (fun Z => (hc Z).mono hsub) (hτ.mono n hn) hϑ hrm hrn (Y n)

/-- **The parallel rank-adaptive BUG integrator is a tube-local method**
(`StepMethod.IsTubeLocal`) for `R = Set.Ici r₀`, with every matrix admissible and margin
constant `2`, for every tolerance `ϑ ≥ 0`:

* a step exists from every matrix, for every globally Lipschitz field that is continuous in time
  on the step interval (`MatrixParallelBUG.exists_adaptiveStepRel_Ici`); this is where `r₀ ≤ m`
  and `r₀ ≤ n` are used;
* the admissible set is that of all matrices, so it is kept by every step;
* if `‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, a step from `Y₀` of the extended field
  `tubeExt F A a b ρ` is a step of `F` (`MatrixParallelBUG.adaptiveStepRel_tubeExt_iff_of_near`).

With the local error `MatrixParallelBUG.adaptiveStepRel.hasLocalError_of_tube` this is all that
`StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_tol` needs. -/
theorem isTubeLocal_adaptiveStepRel_Ici (hϑ : 0 ≤ ϑ) (hrm : r₀ ≤ Fintype.card m)
    (hrn : r₀ ≤ Fintype.card n) :
    StepMethod.IsTubeLocal
      (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => adaptiveStepRel G (Set.Ici r₀) ϑ)
      (fun _ => True) 2 where
  exists_step := fun hG hc h01 _ => exists_adaptiveStepRel_Ici hG hc h01 hϑ hrm hrn _
  adm_of_step := fun _ _ _ => trivial
  step_of_tubeExt := fun hFB hB ha hb h01 hA _ hsmall hstep =>
    (adaptiveStepRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 hstep

end Exists

/-! ### Local error, and the error bounds -/

section Error

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r₀ : ℕ}
  {R : Set ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ}
  {t₀ t₁ a b h T ρ L B ε δ ϑ : ℝ} {N : ℕ} {Y₀ Y₁ : Matrix m n ℝ}

/-- **Local error of the parallel rank-adaptive BUG step near a reference solution.** Let `F`
be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around a solution `A` over
`[a, b]`, and let the normal part of `F` be at most `ε` at the factored points of this tube with
`r` columns, for every `r` in the set `R` of numbers of columns that a step may start from. If
the start value of a step over `[t₀, t₁] ⊆ [a, b]` satisfies `‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`,
then every step of `MatrixParallelBUG.adaptiveStepRel F R ϑ` from `Y₀` has local error at most
`(t₁ - t₀) (7 L B (t₁ - t₀) + ε) + ϑ` ([CerutiKuschLubich2024, (4.1)] for a field that is
Lipschitz and bounded near the exact solution only). The tolerance enters once and is not
multiplied by the step size. -/
theorem adaptiveStepRel.hasLocalError_of_tube (h : adaptiveStepRel F R ϑ t₀ t₁ Y₀ Y₁)
    (hε : ∀ r ∈ R, FactoredNormalBoundOn F r (tubeSet A a b ρ) ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Y₁ ((t₁ - t₀) * (7 * L * B * (t₁ - t₀) + ε) + ϑ) := by
  obtain ⟨r, hr, Yh, hYh, htr⟩ := h
  exact (hYh.hasLocalError_of_tube (hε r hr) hFL hL hFB hB ha hb h01 hA
    hsmall).add_of_norm_sub_le htr

/-- **Local error of one step of a uniform grid.** Under the hypotheses of the run theorem on
`F` and `A` (`DLRAProblem`, and `FactoredNormalBoundOn` at every number of columns in `R` on the
tube of radius `ρ` around `A` over `[t₀, t₀ + N h]`), a step of the parallel rank-adaptive BUG
integrator with tolerance `ϑ` over `[t₀ + k h, t₀ + (k + 1) h]`, `k < N`, whose start value `Z₀`
satisfies `‖Z₀ - A (t₀ + k h)‖ + 2 B h < ρ` has local error `h (7 L B h + ε) + ϑ`. -/
theorem adaptiveStepRel.hasLocalError_uniformGrid {k : ℕ} {Z₀ Z₁ : Matrix m n ℝ}
    (hstep : adaptiveStepRel F R ϑ (t₀ + k * h) (t₀ + (k + 1) * h) Z₀ Z₁)
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hε : ∀ r ∈ R, FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε)
    (hh : 0 ≤ h) (hk : k < N) (hnear : ‖Z₀ - A (t₀ + k * h)‖ + 2 * B * h < ρ) :
    HasLocalError F (t₀ + k * h) (t₀ + (k + 1) * h) Z₀ Z₁ (h * (7 * L * B * h + ε) + ϑ) := by
  obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hk
  have hloc := hstep.hasLocalError_of_tube hε hP.lipschitz hP.L_nonneg hP.bounded hP.B_nonneg
    ha hb h01 (hP.sol.mono ha hb) (by rw [hsub]; exact hnear)
  rwa [hsub] at hloc

/-- **Every run of the parallel rank-adaptive BUG integrator satisfies the robust error bound.**
Let `A` solve `Y' = F(t, Y)` on `[t₀, t₀ + N h]`, and let `F` be `L`-Lipschitz and bounded by
`B` on the tube of radius `ρ` around `A` (`DLRAProblem`), jointly continuous there, with normal
component at most `ε` at the factored matrices of the tube with `r` columns, for every `r` in
the set `R` of numbers of columns that a step may start from (`FactoredNormalBoundOn`). Let
`Y 0, …, Y N` be a run of the integrator with tolerance `ϑ ≥ 0`, step size `h > 0`, `N h ≤ T`,
and `‖Y 0 - A t₀‖ ≤ δ`. If the bound below is smaller than the tube radius with a margin of
`2 B h`, then for all `n ≤ N`

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (7 L B h + ε) + T e^{L T} ϑ / h`.

This is the bound `C₀ δ + C₁ h + C₂ ε + C₃ ϑ / h` of [CerutiKuschLubich2024, Theorem 4.1] with
`C₀ = e^{L T}`, `C₁ = 7 L B T e^{L T}`, `C₂ = C₃ = T e^{L T}`, the constants of
`MatrixParallelBUG.global_error_constants`. The constants do not depend on the singular values
of the `Y n`, nothing is assumed about `F` outside the tube, and no exact solutions started at
the numerical values have to be supplied. The relation contains every truncation within the
tolerance, so the bound holds for the truncated singular value decomposition. -/
theorem IsRun.norm_sub_le_of_adaptiveStepRel {Y : ℕ → Matrix m n ℝ}
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : ∀ r ∈ R, FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hϑ : 0 ≤ ϑ) (hh : 0 < h) (hNT : N * h ≤ T)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) * (7 * L * B * h + ε) +
      T * Real.exp (L * T) * (ϑ / h) + 2 * B * h < ρ)
    (hY : IsRun (adaptiveStepRel F R ϑ) (uniformGrid t₀ h) N Y) (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ +
      T * Real.exp (L * T) * (7 * L * B * h + ε) + T * Real.exp (L * T) * (ϑ / h) := by
  have hc₀ : 0 ≤ 7 * L * B * h + ε + ϑ / h :=
    add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hP.L_nonneg) hP.B_nonneg) hh.le) hε₀)
      (div_nonneg hϑ hh.le)
  have e : Real.exp (L * T) * δ + T * Real.exp (L * T) * (7 * L * B * h + ε) +
      T * Real.exp (L * T) * (ϑ / h) =
      Real.exp (L * T) * δ + T * Real.exp (L * T) * (7 * L * B * h + ε + ϑ / h) := by ring
  rw [e] at hsmall ⊢
  refine hY.norm_sub_le_of_tube_uniformGrid (T := T) (δ₀ := δ) (c := 7 * L * B * h + ε + ϑ / h)
    hP hc (fun k hk Z₀ Z₁ hnear hstep => ?_) hc₀ hδ hNT hsmall
  -- the local error of a step that starts within the error bound of `A`
  have hloc := hstep.hasLocalError_uniformGrid hP hε hh.le hk (by linarith)
  have e' : h * (7 * L * B * h + ε + ϑ / h) = h * (7 * L * B * h + ε) + ϑ := by
    rw [mul_add, mul_div_cancel₀ ϑ hh.ne']
  rwa [e']

/-- **The error bound for a chain of factor steps with changing ranks**, the tube form of
[CerutiKuschLubich2024, Theorem 4.1]. Let the factors `(U j, Sm j, V j)` with `rk j` columns be
advanced by parallel BUG steps of size `h > 0` (`MatrixParallelBUG.IsStep`) with any new
directions `W j`, `Z j`, and let `U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ` be within the tolerance
`ϑ ≥ 0` of the assembled result of step `j`. Let `F` be `L`-Lipschitz and bounded by `B` on the
tube of radius `ρ` around the exact solution `A` (`DLRAProblem`), jointly continuous there, with
normal component at most `ε` at the factored matrices of the tube with `rk j` columns, `j < N`.
Under the smallness condition, for all `j ≤ N`

  `‖U j Sm j (V j)ᵀ - A (t₀ + j h)‖ ≤ e^{L T} δ + T e^{L T} (7 L B h + ε) + T e^{L T} ϑ / h`.

Compared with `MatrixParallelBUG.global_error_constants`, which has the same constants, the
Lipschitz bound, the bound on the field and the bound on its normal component are needed only on
the tube around `A` (there: for all matrices, and the normal component at the numerical values),
and no exact solutions started at the numerical values have to be supplied (there: one for each
step). The price is the smallness condition, which keeps the numerical values in the tube, and
joint continuity of `F` on the tube. -/
theorem adaptive_norm_sub_le_of_isStep {rk sU sV : ℕ → ℕ}
    {U : (j : ℕ) → Matrix m (Fin (rk j)) ℝ} {Sm : (j : ℕ) → Matrix (Fin (rk j)) (Fin (rk j)) ℝ}
    {V : (j : ℕ) → Matrix n (Fin (rk j)) ℝ} {W : (j : ℕ) → Matrix m (Fin (sU j)) ℝ}
    {Z : (j : ℕ) → Matrix n (Fin (sV j)) ℝ} {K : (j : ℕ) → ℝ → Matrix m (Fin (rk j)) ℝ}
    {Lf : (j : ℕ) → ℝ → Matrix n (Fin (rk j)) ℝ}
    {Sb : (j : ℕ) → ℝ → Matrix (Fin (rk j)) (Fin (rk j)) ℝ}
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : ∀ j < N, FactoredNormalBoundOn F (rk j) (tubeSet A t₀ (t₀ + N * h) ρ) ε)
    (hε₀ : 0 ≤ ε) (hϑ : 0 ≤ ϑ) (hh : 0 < h) (hNT : N * h ≤ T)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) * (7 * L * B * h + ε) +
      T * Real.exp (L * T) * (ϑ / h) + 2 * B * h < ρ)
    (hstep : ∀ j < N, IsStep F (t₀ + j * h) (t₀ + (j + 1) * h) (U j) (Sm j) (V j) (W j) (Z j)
      (K j) (Lf j) (Sb j))
    (htr : ∀ j < N, ‖U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ - augmented (U j) (W j) (V j) (Z j)
      (Sb j (t₀ + (j + 1) * h)) (K j (t₀ + (j + 1) * h)) (Lf j (t₀ + (j + 1) * h))‖ ≤ ϑ)
    (hδ : ‖U 0 * Sm 0 * (V 0)ᵀ - A t₀‖ ≤ δ) :
    ∀ j ≤ N, ‖U j * Sm j * (V j)ᵀ - A (t₀ + j * h)‖ ≤ Real.exp (L * T) * δ +
      T * Real.exp (L * T) * (7 * L * B * h + ε) + T * Real.exp (L * T) * (ϑ / h) := by
  have e : ∀ j : ℕ, uniformGrid t₀ h (j + 1) = t₀ + ((j : ℝ) + 1) * h := fun j => by
    simp [uniformGrid]
  have hrun : IsRun (adaptiveStepRel F {s | ∃ j < N, rk j = s} ϑ) (uniformGrid t₀ h) N
      fun j => U j * Sm j * (V j)ᵀ :=
    isRun_adaptiveStepRel_of_isStep (W := W) (Z := Z) (K := K) (Lf := Lf) (Sb := Sb)
      (isGrid_uniformGrid hh.le N) (fun j hj => ⟨j, hj, rfl⟩)
      (fun j hj => by rw [e j]; exact hstep j hj) (fun j hj => by rw [e j]; exact htr j hj)
  refine IsRun.norm_sub_le_of_adaptiveStepRel hP hc ?_ hε₀ hϑ hh hNT hsmall hrun hδ
  rintro _ ⟨j, hj, rfl⟩
  exact hε j hj

/-- **Existence and robust error bound for the parallel rank-adaptive BUG integrator.** Let `A`
solve `Y' = F(t, Y)` on `[t₀, t₀ + N h]`, and let `F` be `L`-Lipschitz and bounded by `B` on the
tube of radius `ρ` around `A` (`DLRAProblem`), jointly continuous there, with normal component
at most `ε` at the factored matrices of the tube with `r` columns, for every `r ≥ r₀`
(`FactoredNormalBoundOn`). Let `r₀ ≤ m`, `r₀ ≤ n`, `ϑ ≥ 0`, let the step size satisfy `h ≥ 0`
and `N h ≤ T`, and let `Y₀` be a start value with `‖Y₀ - A t₀‖ ≤ δ`. If

  `e^{L T} (δ + N ϑ) + T e^{L T} (7 L B h + ε) + 2 B h < ρ`,

then the integrator can be run from `Y₀`: there are `Y 0 = Y₀, Y 1, …, Y N`, each obtained from
the previous one by a parallel BUG step of size `h` from a factorization with at least `r₀`
columns, followed by a truncation to the tolerance `ϑ`, with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} (δ + n ϑ) + T e^{L T} (7 L B h + ε)` for all `n ≤ N`.

The constants are independent of the singular values of the matrices `Y n`, and nothing is
assumed about `F` outside the tube. This is `StepMethod.IsTubeLocal.exists_run_norm_sub_le_of_tol`
for the tube-local method `MatrixParallelBUG.isTubeLocal_adaptiveStepRel_Ici`. For a bound that
holds for every run see `MatrixParallelBUG.IsRun.norm_sub_le_of_adaptiveStepRel`. -/
theorem adaptive_exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : ∀ r ∈ Set.Ici r₀, FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε)
    (hε₀ : 0 ≤ ε) (hϑ : 0 ≤ ϑ) (hh : 0 ≤ h) (hNT : N * h ≤ T)
    (hrm : r₀ ≤ Fintype.card m) (hrn : r₀ ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * (δ + N * ϑ) + T * Real.exp (L * T) * (7 * L * B * h + ε) +
      2 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (adaptiveStepRel F (Set.Ici r₀) ϑ) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * (δ + n * ϑ) + T * Real.exp (L * T) * (7 * L * B * h + ε) := by
  have hc₀ : 0 ≤ 7 * L * B * h + ε :=
    add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hP.L_nonneg) hP.B_nonneg) hh)
      hε₀
  have hBh : 0 ≤ B * h := mul_nonneg hP.B_nonneg hh
  obtain ⟨Y, hY0, hY, hbd⟩ :=
    (isTubeLocal_adaptiveStepRel_Ici hϑ hrm hrn).exists_run_norm_sub_le_of_tol le_rfl hP hc
      (c := 7 * L * B * h + ε) (T := T) (δ := δ) (ϑ := ϑ)
      (fun k hk Z₀ Z₁ _ hnear hstep =>
        -- the local error of a step that starts within the error bound of `A`
        hstep.hasLocalError_uniformGrid hP hε hh hk (by linarith))
      hc₀ hϑ hh hNT trivial hδ hsmall
  exact ⟨Y, hY0, hY, fun n hn => (hbd n hn).2⟩

end Error

/-! ### Examples: a nonlinear field and a linear field -/

section Examples

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r₀ : ℕ}

/-- **Non-vacuity of the existence and error theorem.** The radial field
`F(t, Y) = Y / max ‖Y‖ 1` is `2`-Lipschitz, bounded by `1`, and has no normal component at any
factored matrix, whatever the number of columns (`MatrixKSL.radial_normal_eq_zero`), so `ε = 0`
for every `r ≥ r₀`. For every solution `A` of `Y' = F(t, Y)` on `[t₀, t₀ + N h]`, every tolerance
`ϑ ≥ 0` and every start value `Y₀`, of any rank, with `‖Y₀ - A t₀‖ ≤ δ`, the parallel
rank-adaptive BUG integrator can be run with any step size `h ≥ 0`, and the run stays within
`e^{2 T} (δ + j ϑ) + 14 T e^{2 T} h` of `A` after `j` steps. No smallness condition remains,
because the field is Lipschitz and bounded everywhere and the tube radius can be chosen as large
as needed. -/
example {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (hrm : r₀ ≤ Fintype.card m) (hrn : r₀ ≤ Fintype.card n)
    {A : ℝ → Matrix m n ℝ} {t₀ h T δ : ℝ} {N : ℕ}
    (hA : ODESolution (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) A t₀ (t₀ + N * h))
    (hh : 0 ≤ h) (hNT : N * h ≤ T) {Y₀ : Matrix m n ℝ} (hδ : ‖Y₀ - A t₀‖ ≤ δ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (adaptiveStepRel (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z)
        (Set.Ici r₀) ϑ) (uniformGrid t₀ h) N Y ∧
      ∀ j ≤ N, ‖Y j - A (t₀ + j * h)‖ ≤
        Real.exp (2 * T) * (δ + j * ϑ) + T * Real.exp (2 * T) * (7 * 2 * 1 * h + 0) := by
  have hcont : Continuous fun Z : Matrix m n ℝ => MatrixKSL.radial Z :=
    (LipschitzWith.of_dist_le' (K := 2) fun X Y => by
      rw [dist_eq_norm, dist_eq_norm]; exact MatrixKSL.norm_radial_sub_le X Y).continuous
  exact adaptive_exists_run_norm_sub_le
    (F := fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) (A := A) (L := 2) (B := 1)
    (ε := 0)
    (ρ := Real.exp (2 * T) * (δ + N * ϑ) + T * Real.exp (2 * T) * (7 * 2 * 1 * h + 0) +
      2 * 1 * h + 1)
    ⟨hA, by norm_num, by norm_num, fun _ _ X Y _ _ => MatrixKSL.norm_radial_sub_le X Y,
      fun _ _ X _ => MatrixKSL.norm_radial_le X⟩
    (hcont.comp continuous_snd).continuousOn
    (fun _ _ t U V S hU hV _ => MatrixKSL.radial_normal_eq_zero t U S V hU hV) le_rfl hϑ hh hNT
    hrm hrn hδ (lt_add_one _)

/-- **Non-vacuity for a field that is not bounded, and for every run.** The linear field
`F(t, Y) = M Y + Y Nᵀ + G` with a stationary point `C` (`M C + C Nᵀ + G = 0`) is Lipschitz with
constant `‖M‖ + ‖N‖` but not bounded. On the tube of radius `ρ` around the constant solution
`A(t) = C` it is bounded by `(‖M‖ + ‖N‖) ρ`, and its normal component at the factored matrices
is at most `‖G‖` for every number of columns (`dlraProblem_linear`,
`factoredNormalBoundOn_linear`); `‖G‖` is smaller than the bound of the field as soon as
`‖G‖ < (‖M‖ + ‖N‖) ρ`. Hence a run of the parallel rank-adaptive integrator with tolerance `ϑ`
exists from every `Y₀`, and under the smallness condition every run from a `Y₀` near `C`, with
any set of numbers of columns, satisfies the error bound with `ε = ‖G‖` and the term
`T e^{L T} ϑ / h`. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) {R : Set ℕ} {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (hrm : r₀ ≤ Fintype.card m)
    (hrn : r₀ ≤ Fintype.card n) (t₀ : ℝ) {ρ T δ h : ℝ} {K : ℕ} (hρ : 0 ≤ ρ) (hh : 0 < h)
    (hKT : K * h ≤ T) {Y₀ : Matrix m n ℝ} (hδ : ‖Y₀ - C‖ ≤ δ)
    (hsmall : Real.exp ((‖M‖ + ‖N‖) * T) * δ + T * Real.exp ((‖M‖ + ‖N‖) * T) *
      (7 * (‖M‖ + ‖N‖) * ((‖M‖ + ‖N‖) * ρ) * h + ‖G‖) +
      T * Real.exp ((‖M‖ + ‖N‖) * T) * (ϑ / h) + 2 * ((‖M‖ + ‖N‖) * ρ) * h < ρ) :
    (∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (adaptiveStepRel (fun (_ : ℝ) (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G)
        (Set.Ici r₀) ϑ) (uniformGrid t₀ h) K Y) ∧
    ∀ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ →
      IsRun (adaptiveStepRel (fun (_ : ℝ) (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G) R ϑ)
        (uniformGrid t₀ h) K Y →
      ∀ j ≤ K, ‖Y j - C‖ ≤ Real.exp ((‖M‖ + ‖N‖) * T) * δ + T * Real.exp ((‖M‖ + ‖N‖) * T) *
        (7 * (‖M‖ + ‖N‖) * ((‖M‖ + ‖N‖) * ρ) * h + ‖G‖) +
        T * Real.exp ((‖M‖ + ‖N‖) * T) * (ϑ / h) := by
  refine ⟨adaptive_exists_run (isLipschitzField_linear M N G) (isGrid_uniformGrid hh.le K)
    (fun _ => continuousOn_const) hϑ hrm hrn Y₀, fun Y hY0 hY => ?_⟩
  exact IsRun.norm_sub_le_of_adaptiveStepRel (A := fun _ => C)
    (dlraProblem_linear M N G C hC _ _ hρ) (continuous_uncurry_linear M N G).continuousOn
    (fun r _ => factoredNormalBoundOn_linear M N G _) (norm_nonneg G) hϑ hh hKT hsmall hY
    (by rw [hY0]; exact hδ)

/-- **A concrete instance of the previous example** (the data of `LinearFieldExample`). On
`2 × 2` matrices with at least `r₀ = 1` column, take `M = -E`, `N = 0` and `G = C = E` with
`E = e₁ e₁ᵀ`, so that `L = ‖M‖ + ‖N‖ = 1`, `B = ρ` and `‖G‖ = 1`, the start value `Y₀ = (5/4) E`
with `‖Y₀ - C‖ = 1/4` and the tolerance `ϑ = 1/10000`. With `K = 10` steps of size `h = 1/100` up
to `T = 1/10` and the tube radius `ρ = 4` the smallness condition holds (`e^{1/10} ≤ 3`): a run
of the parallel rank-adaptive integrator exists, and every run from `Y₀`, with any set `R` of
numbers of columns, satisfies the error bound. -/
example (t₀ : ℝ) {R : Set ℕ} :
    (∃ Y : ℕ → Matrix (Fin 2) (Fin 2) ℝ, Y 0 = Matrix.vecMulVec ![5 / 4, 0] ![1, 0] ∧
      IsRun (adaptiveStepRel (fun (_ : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) =>
        -Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0] * Y + Y * (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ +
          Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]) (Set.Ici 1) (1 / 10000))
        (uniformGrid t₀ (1 / 100)) 10 Y) ∧
    ∀ Y : ℕ → Matrix (Fin 2) (Fin 2) ℝ, Y 0 = Matrix.vecMulVec ![5 / 4, 0] ![1, 0] →
      IsRun (adaptiveStepRel (fun (_ : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) =>
        -Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0] * Y + Y * (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ +
          Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]) R (1 / 10000)) (uniformGrid t₀ (1 / 100)) 10 Y →
      ∀ j ≤ 10, ‖Y j - Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0]‖ ≤
        Real.exp (1 * (1 / 10)) * (1 / 4) +
          1 / 10 * Real.exp (1 * (1 / 10)) * (7 * 1 * 4 * (1 / 100) + 1) +
          1 / 10 * Real.exp (1 * (1 / 10)) * (1 / 10000 / (1 / 100)) := by
  have he := LinearFieldExample.exp_le_three
  refine ⟨adaptive_exists_run LinearFieldExample.isLipschitzField
    (isGrid_uniformGrid (by norm_num) 10) (fun _ => continuousOn_const) (by norm_num) (by simp)
    (by simp) _, fun Y hY0 hY => ?_⟩
  exact IsRun.norm_sub_le_of_adaptiveStepRel (A := fun _ => Matrix.vecMulVec ![(1 : ℝ), 0] ![1, 0])
    (LinearFieldExample.dlraProblem _ _ (ρ := 4) (by norm_num))
    (continuous_uncurry_linear _ _ _).continuousOn
    (fun _ _ => LinearFieldExample.factoredNormalBoundOn _ _) zero_le_one (by norm_num)
    (by norm_num) (by norm_num) (by linarith) hY
    (by rw [hY0]; exact LinearFieldExample.norm_start_sub_le)

end Examples

end MatrixParallelBUG

end LeanDLRA
