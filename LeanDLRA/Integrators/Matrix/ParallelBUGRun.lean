import LeanDLRA.Integrators.Matrix.ParallelBUGStep

/-!
# Runs of the fixed-rank parallel BUG integrator: existence and error bound

This file closes the theory of the parallel basis-update & Galerkin (BUG) integrator with a fixed
rank for a matrix differential equation `Y' = F(t, Y)` [CerutiKuschLubich2024]: it shows that
the integrator can be run, and that every run stays close to the exact solution. It is the place
to start reading about the integrator.

**Setting.** Let `A` be a solution of `Y' = F(t, Y)` on `[t₀, t₀ + N h]`. The field `F` is only
assumed to be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around `A`
(`DLRAProblem F A t₀ (t₀ + N h) ρ L B`), jointly continuous there, and to have a small normal
component at the rank-`r` matrices in the tube (`FactoredNormalBoundOn F r _ ε`): for every
`Y = U S Vᵀ` with orthonormal `U`, `V` the part `(I - U Uᵀ) F(t, Y) (I - V Vᵀ)` of the field that
points away from both the column and the row space of `Y` has norm at most `ε`. Nothing is
assumed about `F` outside the tube.

**Result** (`MatrixParallelBUG.exists_run_norm_sub_le`). For every start value `Y₀` of rank at
most `r` with `‖Y₀ - A t₀‖ ≤ δ` there are matrices `Y 0 = Y₀, Y 1, …, Y N`, each obtained from
the previous one by a parallel BUG step of size `h` followed by a best approximation of rank at
most `r` (`IsRun (MatrixParallelBUG.stepRel F r) (uniformGrid t₀ h) N Y`), all of rank at most
`r`, with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (24 L B h + 3 ε)` for all `n ≤ N`,

where `N h ≤ T`. The constants do not depend on the singular values of the matrices `Y n`: the
bound is robust to small singular values. The only further hypothesis is that the right-hand
side is smaller than the tube radius, with a margin of two step lengths at the speed bound:
`e^{L T} δ + T e^{L T} (24 L B h + 3 ε) + 2 B h < ρ`. The same bound holds for *every* run, not
only for the one constructed (`MatrixParallelBUG.IsRun.norm_sub_le`).

## Main results

* `MatrixParallelBUG.exists_isStep_of_lipschitz`: the three substeps of a parallel BUG step have
  solutions for every Lipschitz field that is continuous in time on the step interval; no bound
  on the field and no assumption on the dimensions is needed.
* `MatrixParallelBUG.exists_stepRel_iff`: a step of `MatrixParallelBUG.stepRel` from `Y₀` exists
  if and only if `Y₀` has rank at most `r`.
* `MatrixParallelBUG.exists_run`: for a globally Lipschitz field there is a run on every grid
  from every start value of rank at most `r`.
* `MatrixParallelBUG.IsRun.norm_sub_le`: every run satisfies the error bound.
* `MatrixParallelBUG.norm_sub_le_of_isStep`: the error bound for a chain of factor steps
  (`MatrixParallelBUG.IsStep`), each followed by a best approximation of rank at most `r`.
* `MatrixParallelBUG.isTubeLocal_stepRel`: the integrator is a tube-local method
  (`StepMethod.IsTubeLocal`) with the matrices of rank at most `r` as admissible values and
  margin constant `2`.
* `MatrixParallelBUG.exists_run_norm_sub_le`: a run exists, has rank at most `r` and satisfies
  the error bound.

The example at the end applies the result to the field `F(t, Y) = Y / max ‖Y‖ 1`, which is
Lipschitz and bounded and has no normal component at all, so that `ε = 0` and the error is of
first order in `h` for every rank.

## Implementation notes

`MatrixParallelBUG.exists_run_norm_sub_le` is an instance of the theorem for tube-local methods,
`StepMethod.IsTubeLocal.exists_run_norm_sub_le`, in the same way as
`MatrixBUG.exists_run_norm_sub_le` for the BUG integrator and `MatrixKSL.exists_run_norm_sub_le`
for the projector-splitting integrator; the hypotheses have the same names and the same order.
What is specific to the parallel BUG integrator is collected in
`MatrixParallelBUG.isTubeLocal_stepRel` (existence of a step for globally Lipschitz fields,
`MatrixParallelBUG.exists_stepRel`; the rank bound, `MatrixParallelBUG.stepRel.rank_le`;
locality, `MatrixParallelBUG.stepRel_tubeExt_iff_of_near`) and in the local error
`MatrixParallelBUG.stepRel.hasLocalError_of_tube`.

The constants: a step without truncation has local error `h (7 L B h + ε)`, the exact solution
through a matrix of rank at most `r` is within `h (10 L B h + ε)` of the matrices of rank at
most `r` after one step, and a best approximation costs this distance plus twice the error
before truncation. This gives `10 + 2 · 7 = 24` and `1 + 2 · 1 = 3`.

The three substeps are differential equations for the factors whose fields are the field `F`
conjugated by linear maps (`MatrixKSL.kField_eq`, `MatrixKSL.lField_eq`,
`MatrixParallelBUG.sField_eq`); their solutions exist by
`MatrixBUG.exists_odeSolution_conj_of_lipschitz`, which does not depend on the integrator.

Compared with `MatrixParallelBUG.global_error`, the results of this file need the Lipschitz
bound, the bound on the field and the bound on its normal component only on the tube around the
exact solution, they need no exact flows started at the numerical values, the substeps are
shown to exist, and the truncation is the best approximation of rank at most `r` instead of an
unspecified truncation with a tolerance: no tolerance appears in the bound, and the rank of the
numerical values is `r` throughout. The price is the smallness condition, which keeps the
numerical values in the tube, joint continuity of `F` on the tube, and the larger constants
`24` and `3` in place of `7` and `1`. For the integrator with a truncation tolerance, whose rank
changes from step to step, `MatrixParallelBUG.global_error` remains the result to use.

## References

* [CerutiKuschLubich2024] G. Ceruti, J. Kusch, Ch. Lubich, *A parallel rank-adaptive integrator
  for dynamical low-rank approximation*, SIAM J. Sci. Comput. 46 (2024), arXiv:2304.05660,
  §3 and Theorem 4.1.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixParallelBUG

/-! ### Existence of one step -/

section Exists

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
  {L : ℝ}

/-- The field of the S-step is the field `F` conjugated by `S ↦ U₀ S V₀ᵀ` and
`X ↦ U₀ᵀ X V₀`. -/
lemma sField_eq (U₀ : Matrix m (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ) (t : ℝ)
    (S : Matrix (Fin r) (Fin r) ℝ) :
    sField U₀ V₀ F t S = ((Frobenius.rightMulCLM V₀).comp (Frobenius.leftMulCLM U₀ᵀ))
      (F t (((Frobenius.rightMulCLM V₀ᵀ).comp (Frobenius.leftMulCLM U₀)) S)) :=
  rfl

variable [DecidableEq m] [DecidableEq n]

/-- **The substeps of a parallel BUG step exist.** If `F` is Lipschitz and continuous in time on
`[t₀, t₁]` and the matrices `U₀`, `V₀` have orthonormal columns, then for every `S₀` the K-, L-
and S-step have solutions: there are `K`, `Lf`, `Sb` forming a step of the parallel BUG
integrator (`IsStep`) with the complementary projectors as new directions. The field need not be
bounded, the Lipschitz constant may have any sign, and nothing is assumed about the
dimensions. -/
theorem exists_isStep_of_lipschitz (hF : IsLipschitzField F L) {t₀ t₁ : ℝ}
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁)
    {U₀ : Matrix m (Fin r) ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    {V₀ : Matrix n (Fin r) ℝ} (hV₀ : V₀ᵀ * V₀ = 1) :
    ∃ (K : ℝ → Matrix m (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ)
      (Sb : ℝ → Matrix (Fin r) (Fin r) ℝ),
      IsStep F t₀ t₁ U₀ S₀ V₀ (1 - U₀ * U₀ᵀ) (1 - V₀ * V₀ᵀ) K Lf Sb := by
  obtain ⟨K, hK, hK₀⟩ := MatrixBUG.exists_odeSolution_conj_of_lipschitz hF hc _ _
    (fun t x => MatrixKSL.kField_eq V₀ t x) h01 (U₀ * S₀)
  obtain ⟨Lf, hLf, hLf₀⟩ := MatrixBUG.exists_odeSolution_conj_of_lipschitz hF hc _ _
    (fun t x => MatrixKSL.lField_eq U₀ t x) h01 (V₀ * S₀ᵀ)
  obtain ⟨Sb, hSb, hSb₀⟩ := MatrixBUG.exists_odeSolution_conj_of_lipschitz hF hc _ _
    (fun t x => sField_eq U₀ V₀ t x) h01 S₀
  exact ⟨K, Lf, Sb, hU₀, hV₀, hK, hK₀, hLf, hLf₀, hSb, hSb₀,
    (compl_capture_proj (k := Fin r) hU₀).1, (compl_capture_proj (k := Fin r) hU₀).2.2 _,
    (compl_capture_proj (k := Fin r) hV₀).1, (compl_capture_proj (k := Fin r) hV₀).2.2 _⟩

/-- **A parallel BUG step without truncation exists from every start value of rank at most
`r`.** If `F` is Lipschitz and continuous in time on `[t₀, t₁]` and `r ≤ m`, `r ≤ n`, then every
matrix `Y₀` of rank at most `r` has a successor under `augmentedRel F r`. -/
theorem exists_augmentedRel (hF : IsLipschitzField F L) {t₀ t₁ : ℝ}
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) : ∃ Yh, augmentedRel F r t₀ t₁ Y₀ Yh := by
  obtain ⟨U₀, S₀, V₀, hU₀, hV₀, rfl⟩ := exists_factor_of_rank_le hY₀ hrm hrn
  obtain ⟨K, Lf, Sb, hs⟩ := exists_isStep_of_lipschitz hF hc h01 hU₀ S₀ hV₀
  exact ⟨_, hs.augmentedRel⟩

/-- **A step of the fixed-rank parallel BUG integrator exists from every start value of rank at
most `r`.** If `F` is Lipschitz and continuous in time on `[t₀, t₁]` and `r ≤ m`, `r ≤ n`, then
every matrix `Y₀` of rank at most `r` has a successor under `stepRel F r`. -/
theorem exists_stepRel (hF : IsLipschitzField F L) {t₀ t₁ : ℝ}
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) : ∃ Y₁, stepRel F r t₀ t₁ Y₀ Y₁ := by
  obtain ⟨Yh, hYh⟩ := exists_augmentedRel hF hc h01 hrm hrn hY₀
  exact hYh.exists_stepRel

/-- **The admissible start values of the fixed-rank parallel BUG integrator are exactly the
matrices of rank at most `r`**: a step of `stepRel F r` from `Y₀` exists if and only if `Y₀` has
rank at most `r` (for a Lipschitz field that is continuous in time, and `r ≤ m`, `r ≤ n`). -/
theorem exists_stepRel_iff (hF : IsLipschitzField F L) {t₀ t₁ : ℝ}
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ} :
    (∃ Y₁, stepRel F r t₀ t₁ Y₀ Y₁) ↔ Y₀.rank ≤ r :=
  ⟨fun ⟨_, h⟩ => h.rank_start_le, exists_stepRel hF hc h01 hrm hrn⟩

/-- **A run of the fixed-rank parallel BUG integrator exists** on every grid, from every start
value of rank at most `r`, for a field that is globally Lipschitz and continuous in time on the
grid interval. For fields that are Lipschitz only near the exact solution see
`exists_run_norm_sub_le`. -/
theorem exists_run (hF : IsLipschitzField F L) {τ : ℕ → ℝ} {N : ℕ} (hτ : IsGrid τ N)
    (hc : ∀ Y, ContinuousOn (fun t => F t Y) (Icc (τ 0) (τ N)))
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) : ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) τ N Y := by
  refine exists_isRun hτ Y₀ fun n hn Y hY0 hY => ?_
  have hsub : Icc (τ n) (τ (n + 1)) ⊆ Icc (τ 0) (τ N) :=
    Icc_subset_Icc (hτ.le_of_le n.zero_le hn.le) (hτ.le_of_le (Nat.succ_le_of_lt hn) le_rfl)
  exact exists_stepRel hF (fun Z => (hc Z).mono hsub) (hτ.mono n hn) hrm hrn
    (IsRun.rank_le hY (by rw [hY0]; exact hY₀) n le_rfl)

end Exists

/-! ### The error bound, and existence of a run near the exact solution -/

section Error

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {t₀ h T ρ L B ε δ : ℝ} {N : ℕ}

/-- **Every run of the fixed-rank parallel BUG integrator satisfies the robust error bound.**
Let `A` solve `Y' = F(t, Y)` on `[t₀, t₀ + N h]`, and let `F` be `L`-Lipschitz and bounded by
`B` on the tube of radius `ρ` around `A` (`DLRAProblem`), jointly continuous there, with normal
component at most `ε` at the rank-`r` matrices of the tube (`FactoredNormalBoundOn`). Let
`Y 0, …, Y N` be a run of the integrator with step size `h ≥ 0`, `N h ≤ T`, and
`‖Y 0 - A t₀‖ ≤ δ`. If the bound below is smaller than the tube radius with a margin of
`2 B h`, then for all `n ≤ N`

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (24 L B h + 3 ε)`.

The constants do not depend on the singular values of the `Y n`.

Nothing is assumed about `F` outside the tube, and no auxiliary exact solutions started at the
numerical values appear: they are constructed in the proof
(`IsRun.norm_sub_le_of_tube_uniformGrid`), and the local error of each step comes from
`MatrixParallelBUG.stepRel.hasLocalError_of_tube`. -/
theorem IsRun.norm_sub_le {Y : ℕ → Matrix m n ℝ}
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hNT : N * h ≤ T)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) * (24 * L * B * h + 3 * ε)
      + 2 * B * h < ρ)
    (hY : IsRun (stepRel F r) (uniformGrid t₀ h) N Y) (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (L * T) * δ + T * Real.exp (L * T) * (24 * L * B * h + 3 * ε) := by
  have hc₀ : 0 ≤ 24 * L * B * h + 3 * ε :=
    add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hP.L_nonneg) hP.B_nonneg) hh)
      (mul_nonneg (by norm_num) hε₀)
  refine hY.norm_sub_le_of_tube_uniformGrid (T := T) (δ₀ := δ) (c := 24 * L * B * h + 3 * ε)
    hP hc (fun n hn Y₀ Y₁ hnear hstep => ?_) hc₀ hδ hNT hsmall
  -- the local error of a step that starts within the error bound of `A`
  obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hn
  have hloc := hstep.hasLocalError_of_tube hε hε₀ hP.lipschitz hP.L_nonneg hP.bounded
    hP.B_nonneg hc hP.sol.cont ha hb h01 (hP.sol.mono ha hb) (by rw [hsub]; linarith)
  rwa [hsub] at hloc

/-- **The error bound for a chain of factor steps.** Let the factors `(U j, Sm j, V j)` be
advanced by parallel BUG steps of size `h` (`IsStep`) with any new directions `W j`, `Z j`, and
let `U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ` be a best approximation of rank at most `r` to the
assembled result of step `j`. Under the hypotheses of `IsRun.norm_sub_le` the matrices
`U j * Sm j * (V j)ᵀ` satisfy

  `‖U j * Sm j * (V j)ᵀ - A (t₀ + j h)‖ ≤ e^{L T} δ + T e^{L T} (24 L B h + 3 ε)`.

Compared with `MatrixParallelBUG.global_error` for factors of a fixed rank, the Lipschitz bound,
the bound on the field and the bound on its normal component are needed only on the tube around
`A` (there: for all matrices, and the normal component at the numerical values), no exact
solutions started at the numerical values have to be supplied (there: one for each step), and
the truncation enters through the best approximation property instead of a tolerance `ϑ` that
is added in every step. The price is the smallness condition, which keeps the numerical values
in the tube, joint continuity of `F` on the tube, and the constants `24` and `3` (there: `7`
and `1`, plus the tolerance). -/
theorem norm_sub_le_of_isStep {sU sV : ℕ → ℕ} {U : ℕ → Matrix m (Fin r) ℝ}
    {Sm : ℕ → Matrix (Fin r) (Fin r) ℝ} {V : ℕ → Matrix n (Fin r) ℝ}
    {W : (j : ℕ) → Matrix m (Fin (sU j)) ℝ} {Z : (j : ℕ) → Matrix n (Fin (sV j)) ℝ}
    {K : ℕ → ℝ → Matrix m (Fin r) ℝ} {Lf : ℕ → ℝ → Matrix n (Fin r) ℝ}
    {Sb : ℕ → ℝ → Matrix (Fin r) (Fin r) ℝ}
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hNT : N * h ≤ T)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) * (24 * L * B * h + 3 * ε)
      + 2 * B * h < ρ)
    (hstep : ∀ j < N, IsStep F (t₀ + j * h) (t₀ + (j + 1) * h) (U j) (Sm j) (V j) (W j) (Z j)
      (K j) (Lf j) (Sb j))
    (htr : ∀ j < N, ‖U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ - augmented (U j) (W j) (V j) (Z j)
        (Sb j (t₀ + (j + 1) * h)) (K j (t₀ + (j + 1) * h)) (Lf j (t₀ + (j + 1) * h))‖ ≤
      distLR r (augmented (U j) (W j) (V j) (Z j) (Sb j (t₀ + (j + 1) * h))
        (K j (t₀ + (j + 1) * h)) (Lf j (t₀ + (j + 1) * h))))
    (hδ : ‖U 0 * Sm 0 * (V 0)ᵀ - A t₀‖ ≤ δ) :
    ∀ j ≤ N, ‖U j * Sm j * (V j)ᵀ - A (t₀ + j * h)‖ ≤
      Real.exp (L * T) * δ + T * Real.exp (L * T) * (24 * L * B * h + 3 * ε) := by
  have e : ∀ j : ℕ, uniformGrid t₀ h (j + 1) = t₀ + ((j : ℝ) + 1) * h := fun j => by
    simp [uniformGrid]
  have hrun : IsRun (stepRel F r) (uniformGrid t₀ h) N fun j => U j * Sm j * (V j)ᵀ :=
    isRun_stepRel_of_isStep (W := W) (Z := Z) (K := K) (Lf := Lf) (Sb := Sb)
      (isGrid_uniformGrid hh N) (fun j hj => by rw [e j]; exact hstep j hj)
      (fun j hj => by rw [e j]; exact htr j hj)
  exact IsRun.norm_sub_le hP hc hε hε₀ hh hNT hsmall hrun hδ

/-- **The fixed-rank parallel BUG integrator is a tube-local method**
(`StepMethod.IsTubeLocal`), with the matrices of rank at most `r` as admissible values and
margin constant `2`:

* a step exists from every matrix of rank at most `r`, for every globally Lipschitz field that is
  continuous in time on the step interval (`MatrixParallelBUG.exists_stepRel`);
* the result of a step has rank at most `r` (`MatrixParallelBUG.stepRel.rank_le`); the
  intermediate matrix of rank up to `2 r` is hidden inside the step;
* if `‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, a step from `Y₀` of the extended field
  `tubeExt F A a b ρ` is a step of `F` (`MatrixParallelBUG.stepRel_tubeExt_iff_of_near`).

With the local error `MatrixParallelBUG.stepRel.hasLocalError_of_tube` this is all that
`StepMethod.IsTubeLocal.exists_run_norm_sub_le` needs. -/
theorem isTubeLocal_stepRel (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) :
    StepMethod.IsTubeLocal (fun G : ℝ → Matrix m n ℝ → Matrix m n ℝ => stepRel G r)
      (fun Y => Y.rank ≤ r) 2 where
  exists_step := fun hG hc h01 hY₀ => exists_stepRel hG hc h01 hrm hrn hY₀
  adm_of_step := fun _ _ hstep => hstep.rank_le
  step_of_tubeExt := fun hFB hB ha hb h01 hA _ hsmall hstep =>
    (stepRel_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 hstep

/-- **Existence and robust error bound for the fixed-rank parallel BUG integrator.** Let `A`
solve `Y' = F(t, Y)` on `[t₀, t₀ + N h]`, and let `F` be `L`-Lipschitz and bounded by `B` on the
tube of radius `ρ` around `A` (`DLRAProblem`), jointly continuous there, with normal component
at most `ε` at the rank-`r` matrices of the tube (`FactoredNormalBoundOn`). Let `r ≤ m`,
`r ≤ n`, let the step size satisfy `h ≥ 0` and `N h ≤ T`, and let `Y₀` be a start value of rank
at most `r` with `‖Y₀ - A t₀‖ ≤ δ`. If

  `e^{L T} δ + T e^{L T} (24 L B h + 3 ε) + 2 B h < ρ`,

then the integrator can be run from `Y₀`: there are `Y 0 = Y₀, Y 1, …, Y N`, each obtained from
the previous one by a parallel BUG step of size `h` followed by a best approximation of rank at
most `r`, all of rank at most `r`, with

  `‖Y n - A (t₀ + n h)‖ ≤ e^{L T} δ + T e^{L T} (24 L B h + 3 ε)` for all `n ≤ N`.

The constants are independent of the singular values of the matrices `Y n`, and nothing is
assumed about `F` outside the tube. No truncation tolerance appears: the truncation to rank `r`
costs no more than a constant times the error of the step itself.

This is `StepMethod.IsTubeLocal.exists_run_norm_sub_le` for the tube-local method
`MatrixParallelBUG.isTubeLocal_stepRel`: the steps exist because the error bound keeps the run
constructed so far inside the tube, where `F` and its globally Lipschitz extension
`tubeExt F A t₀ (t₀ + N h) ρ` have the same steps. The bound itself holds for every run
(`MatrixParallelBUG.IsRun.norm_sub_le`). The hypotheses on `F` and `A` are those of
`MatrixBUG.exists_run_norm_sub_le` and `MatrixKSL.exists_run_norm_sub_le`, so the three
integrators can be compared on the same problem; the example below treats a nonlinear field. -/
theorem exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * δ + T * Real.exp (L * T) * (24 * L * B * h + 3 * ε)
      + 2 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * δ + T * Real.exp (L * T) * (24 * L * B * h + 3 * ε) := by
  have hc₀ : 0 ≤ 24 * L * B * h + 3 * ε :=
    add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hP.L_nonneg) hP.B_nonneg) hh)
      (mul_nonneg (by norm_num) hε₀)
  refine (isTubeLocal_stepRel hrm hrn).exists_run_norm_sub_le le_rfl hP hc
    (fun k hk Z₀ Z₁ _ hnear hstep => ?_) hc₀ hh hNT hY₀ hδ hsmall
  -- the local error of a step that starts within the error bound of `A`
  obtain ⟨ha, h01, hb, hsub⟩ := uniformGrid_step (t₀ := t₀) hh hk
  have hloc := stepRel.hasLocalError_of_tube hstep hε hε₀ hP.lipschitz hP.L_nonneg hP.bounded
    hP.B_nonneg hc hP.sol.cont ha hb h01 (hP.sol.mono ha hb) (by rw [hsub]; linarith)
  rwa [hsub] at hloc

end Error

/-! ### Example: a nonlinear field without normal component -/

section Examples

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}

/-- **Non-vacuity of the existence and error theorem.** The radial field
`F(t, Y) = Y / max ‖Y‖ 1` is `2`-Lipschitz, bounded by `1`, and has no normal component at any
matrix (`MatrixKSL.radial_normal_eq_zero`), so `ε = 0`. For every solution `A` of
`Y' = F(t, Y)` on `[t₀, t₀ + N h]`, of any rank (the zero function is one), and every start
value `Y₀` of rank at most `r` with `‖Y₀ - A t₀‖ ≤ δ`, the fixed-rank parallel BUG integrator
can be run with any step size `h ≥ 0`, and the run stays within `e^{2 T} δ + 48 T e^{2 T} h` of
`A`. No smallness condition remains, because the field is Lipschitz and bounded everywhere and
the tube radius can be chosen as large as needed. -/
example (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) {A : ℝ → Matrix m n ℝ}
    {t₀ h T δ : ℝ} {N : ℕ}
    (hA : ODESolution (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) A t₀ (t₀ + N * h))
    (hh : 0 ≤ h) (hNT : N * h ≤ T) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r)
    (hδ : ‖Y₀ - A t₀‖ ≤ δ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (stepRel (fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z) r)
        (uniformGrid t₀ h) N Y ∧
      ∀ j ≤ N, (Y j).rank ≤ r ∧ ‖Y j - A (t₀ + j * h)‖ ≤
        Real.exp (2 * T) * δ + T * Real.exp (2 * T) * (24 * 2 * 1 * h + 3 * 0) := by
  have hcont : Continuous fun Z : Matrix m n ℝ => MatrixKSL.radial Z :=
    (LipschitzWith.of_dist_le' (K := 2) fun X Y => by
      rw [dist_eq_norm, dist_eq_norm]; exact MatrixKSL.norm_radial_sub_le X Y).continuous
  exact exists_run_norm_sub_le (F := fun (_ : ℝ) (Z : Matrix m n ℝ) => MatrixKSL.radial Z)
    (A := A) (L := 2) (B := 1) (ε := 0)
    (ρ := Real.exp (2 * T) * δ + T * Real.exp (2 * T) * (24 * 2 * 1 * h + 3 * 0)
      + 2 * 1 * h + 1)
    ⟨hA, by norm_num, by norm_num, fun _ _ X Y _ _ => MatrixKSL.norm_radial_sub_le X Y,
      fun _ _ X _ => MatrixKSL.norm_radial_le X⟩
    (hcont.comp continuous_snd).continuousOn
    (fun t U V S hU hV _ => MatrixKSL.radial_normal_eq_zero t U S V hU hV) le_rfl hh hNT hrm
    hrn hY₀ hδ (lt_add_one _)

end Examples

end MatrixParallelBUG

end LeanDLRA
