# Getting started

This page is for a reader who knows ordinary differential equations and the singular value
decomposition and opens the repository for the first time. No paper on dynamical low-rank
approximation is assumed. The page explains the subject in fifteen lines, names the definitions
to read first, goes through one theorem and one application of it line by line, and says where
things are and how to add a result.

The page describes the core library, the modules imported by `LeanDLRA.lean`. The other pages:

* [Main results](MAIN_RESULTS.md): the main theorems of the core by topic, with statements.
* [Definitions](DEFINITIONS.md): every definition of the core, by folder.
* [Concepts](CONCEPTS.md): how definitions of the same notion relate to each other.
* [Core and catalogue](STRUCTURE.md): the two libraries of the repository.
* [Conventions](CONVENTIONS.md): the rules for names, statements and docstrings.

Every block of code on this page is copied from a file of the repository; the line above the
block links to the lines. The blocks were compared with the files at commit 571f831 (2026-11-18).
Installation is described in the [README](../README.md#using-leandlra-in-your-project).

## Contents

1. [Dynamical low-rank approximation in fifteen lines](#1-dynamical-low-rank-approximation-in-fifteen-lines)
2. [The definitions to read first](#2-the-definitions-to-read-first)
3. [A worked example: an error bound for your own field](#3-a-worked-example-an-error-bound-for-your-own-field)
4. [Where do I find what](#4-where-do-i-find-what)
5. [Core and catalogue](#5-core-and-catalogue)
6. [How to add a result](#6-how-to-add-a-result)

## 1. Dynamical low-rank approximation in fifteen lines

1. **The problem.** A differential equation `A'(t) = F(t, A(t))` for a real `m × n` matrix `A(t)`
   is given. Storing `A(t)` takes `m n` numbers.
2. **Low rank.** A matrix of rank at most `r` is a product `U S Vᵀ` of an `m × r`, an `r × r` and
   an `r × n` matrix. It takes `(m + n) r + r²` numbers.
3. **Best approximation.** The matrix of rank at most `r` closest to a fixed matrix in the
   Frobenius norm is its truncated singular value decomposition; the squared distance is the sum
   of the squares of the singular values that are cut off (Eckart–Young–Mirsky theorem).
4. **The idea.** Truncating `A(t)` requires `A(t)`. Dynamical low-rank approximation (DLRA)
   computes a curve `Y(t)` of matrices of rank `r` from a differential equation of its own.
5. **Tangent projector.** Let `Y = U S Vᵀ`, where `U` and `V` have orthonormal columns. The
   orthogonal projector onto the tangent space of the rank-`r` matrices at `Y` is
   `P(Y) Z = U Uᵀ Z + Z V Vᵀ - U Uᵀ Z V Vᵀ`.
6. **Projected equation.** DLRA defines `Y` by `Y' = P(Y) F(t, Y)`: the derivative of `Y` is the
   tangent matrix closest to `F(t, Y)`.
7. **Normal component.** The part of the field that the projection removes is
   `(1 - P(Y)) F(t, Y) = (I - U Uᵀ) F(t, Y) (I - V Vᵀ)`, the normal component.
8. **Error of the projected equation.** If `F` is Lipschitz with constant `L > 0`, the normal
   component along `Y` has norm at most `ε`, and `‖Y(a) - A(a)‖ ≤ δ`, then
   `‖Y(t) - A(t)‖ ≤ e^{L (t - a)} δ + ε (e^{L (t - a)} - 1) / L`.
9. **First difficulty.** Written as differential equations for the factors `U`, `S`, `V`, the
   projected equation contains the inverse of `S`.
10. **Second difficulty.** The projector `P(Y)` changes with `Y`. The bound for the change is
    `‖(P(Y') - P(Y)) Z‖ ≤ (2 / σ) ‖Y' - Y‖ ‖Z‖`, where `σ` is a lower bound for the singular
    values of `S`. The constant `2` can be replaced by `1`, and `1` cannot be lowered.
11. **Small singular values.** A rank `r` is good if the singular values that are cut off are
    small. Then the smallest singular values that are kept are typically small as well, and an
    error bound that contains `1 / σ` says nothing.
12. **Integrators.** The projector-splitting integrator and the BUG integrator ("basis update and
    Galerkin") advance `Y = U S Vᵀ` by a step of size `h` through three differential equations,
    for `K = U S`, for `L = V Sᵀ` and for `S`. None of them contains an inverse.
13. **Robust error bounds.** The error of these integrators after `n` steps is at most
    `c₀ δ + c₁ ε + c₂ h`. The constants depend on `L`, on a bound `B` for `F` and on the length of
    the time interval, and not on singular values. Such a bound is called robust.
14. **Variants.** There are variants with a rank that changes from step to step, with substeps
    that run in parallel, with implicit time stepping, and for tensors.
    [Main results](MAIN_RESULTS.md) says what the core proves for each.
15. **This library.** The core writes an integrator as a relation between consecutive values and
    proves the robust bounds for several integrators from one set of definitions.

Where these lines are in the core:

| Line | Lean | File |
|---|---|---|
| 3 | `EckartYoung.sq_norm_sub_truncation`, `EckartYoung.infDist_setOf_rank_le` | [`Classical/EckartYoung.lean`](../LeanDLRA/Classical/EckartYoung.lean) |
| 5 | `tangentProj`, `isOrthProj_tangentProj`, `mem_range_tangentProj` | [`FixedRank/Defs.lean`](../LeanDLRA/FixedRank/Defs.lean), [`Matrix/Projectors.lean`](../LeanDLRA/Matrix/Projectors.lean) |
| 6, 8 | `ODESolution.dlra_norm_sub_le_gronwallBound` | [`Dynamics/ContinuousDLRA.lean`](../LeanDLRA/Dynamics/ContinuousDLRA.lean) |
| 7 | `FactoredNormalBoundOn`, `NormalBoundOn` | [`Integrators/Matrix/Defs.lean`](../LeanDLRA/Integrators/Matrix/Defs.lean), [`DLRA/Defs.lean`](../LeanDLRA/DLRA/Defs.lean) |
| 9 | `hasDerivAt_factorProduct_iff_factorODE` | [`Matrix/GaugeODE.lean`](../LeanDLRA/Matrix/GaugeODE.lean) |
| 10 | `Curvature.koch_lubich_tangent_frob`, `norm_tangentProjAt_sub_le_inv_mul` | [`Matrix/Curvature.lean`](../LeanDLRA/Matrix/Curvature.lean), [`FixedRank/TangentSpace/ProjectorLipschitz.lean`](../LeanDLRA/FixedRank/TangentSpace/ProjectorLipschitz.lean) |
| 12 | `MatrixBUG.IsStep`, `MatrixKSL.IsStep` | [`Integrators/Matrix/BUG.lean`](../LeanDLRA/Integrators/Matrix/BUG.lean), [`Integrators/Matrix/ProjectorSplitting.lean`](../LeanDLRA/Integrators/Matrix/ProjectorSplitting.lean) |
| 13 | `MatrixBUG.exists_run_norm_sub_le`, `MatrixKSL.exists_run_norm_sub_le`, `MatrixParallelBUG.exists_run_norm_sub_le` | [`Integrators/Matrix/BUGRun.lean`](../LeanDLRA/Integrators/Matrix/BUGRun.lean), [`Integrators/Matrix/KSLRun.lean`](../LeanDLRA/Integrators/Matrix/KSLRun.lean), [`Integrators/Matrix/ParallelBUGRun.lean`](../LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean) |

Line 11 is a remark on the purpose of the bounds and has no theorem. The theorem for line 8
writes the projected equation as `ODESolution (fun t x => P t (F t x)) Y a b` with a continuous
linear map `P t` that may depend on time; for line 6, `P t` is the tangent projector at `Y t`.
The theorem uses no property of `P t`.

## 2. The definitions to read first

All names are in the namespace `LeanDLRA`, which is left out below. Time is always the first
argument of a field: `F : ℝ → E → E` is the right-hand side of `Y' = F(t, Y)` on a state space
`E`. For matrices `E` is `Matrix m n ℝ`, and the norm `‖·‖` is the Frobenius norm. The Frobenius
norm and inner product are not switched on globally: a file that uses them contains the line
`open scoped LeanDLRA.Frobenius` (the instances are in
[`LinearAlgebra/Frobenius/Defs.lean`](../LeanDLRA/LinearAlgebra/Frobenius/Defs.lean), the lemmas in
[`Matrix/Frobenius.lean`](../LeanDLRA/Matrix/Frobenius.lean)).

Nine definitions suffice to read the theorem of section 3, in this order:

| Definition | Where | In one line |
|---|---|---|
| `ODESolution` | [Analysis/Defs.lean:85](../LeanDLRA/Analysis/Defs.lean#L85) | `ODESolution F y a b`: `y` is continuous on `[a, b]` and has the right derivative `F t (y t)` at every `t` in `[a, b)`. |
| `tubeSet` | [Analysis/Defs.lean:156](../LeanDLRA/Analysis/Defs.lean#L156) | `tubeSet A a b ρ`: the pairs `(t, x)` with `t` in `[a, b]` and `‖x - A t‖ ≤ ρ`, the tube of radius `ρ` around `A`. |
| `DLRAProblem` | [DLRA/Defs.lean:69](../LeanDLRA/DLRA/Defs.lean#L69) | `DLRAProblem F A a b ρ L B`: `A` solves `Y' = F(t, Y)` on `[a, b]`, and on the tube of radius `ρ` around `A` the field is `L`-Lipschitz in the state and bounded by `B`. |
| `FactoredNormalBoundOn` | [Integrators/Matrix/Defs.lean:141](../LeanDLRA/Integrators/Matrix/Defs.lean#L141) | `FactoredNormalBoundOn F r D ε`: `‖(I - U Uᵀ) F(t, U S Vᵀ) (I - V Vᵀ)‖ ≤ ε` for all `U`, `V` with `r` orthonormal columns and all `S` with `(t, U S Vᵀ)` in the region `D`. |
| `StepRel` | [Integrators/Defs.lean:232](../LeanDLRA/Integrators/Defs.lean#L232) | A one-step method for one field, as a relation: `M t₀ t₁ Y₀ Y₁` says that `Y₁` is a result of one step from `Y₀` at time `t₀` to time `t₁`. |
| `uniformGrid` | [Integrators/Defs.lean:70](../LeanDLRA/Integrators/Defs.lean#L70) | `uniformGrid t₀ h`: the times `t₀ + n h`. |
| `IsRun` | [Integrators/Defs.lean:239](../LeanDLRA/Integrators/Defs.lean#L239) | `IsRun M τ N Y`: the times `τ 0 ≤ … ≤ τ N` are nondecreasing, and each `Y (n + 1)` is a result of one step of `M` from `Y n`, from time `τ n` to `τ (n + 1)`. |
| `MatrixBUG.stepRel` | [Integrators/Matrix/BUGStep.lean:72](../LeanDLRA/Integrators/Matrix/BUGStep.lean#L72) | `MatrixBUG.stepRel F r`: the step of the BUG integrator of rank `r` for the field `F`, as a step relation on matrices. |
| `bugGlobalBound` | [Foundations/Localization.lean:563](../LeanDLRA/Foundations/Localization.lean#L563) | `bugGlobalBound L B H T δ ε h`: the right-hand side `e^{L T} δ + T e^{L T} (c₁ ε + c₂ h)` of the error bound, with `c₁ = bugC₁ L H` and `c₂ = bugC₂ L B H`. |

A step is a relation and not a function because the result of a step is not unique: the new
bases of a step are determined only up to a choice, and a substep is described by the
differential equation it solves. An error bound holds for every result.

Eight more definitions are needed to read the proofs or to treat an integrator of your own:

| Definition | Where | In one line |
|---|---|---|
| `IsLipschitzField` | [Analysis/Defs.lean:92](../LeanDLRA/Analysis/Defs.lean#L92) | `IsLipschitzField F L`: `‖F t x - F t y‖ ≤ L * ‖x - y‖` for all `t`, `x`, `y`. |
| `IsBoundedField` | [Analysis/Defs.lean:96](../LeanDLRA/Analysis/Defs.lean#L96) | `IsBoundedField F B`: `‖F t x‖ ≤ B` for all `t`, `x`. |
| `tubeExt` | [Analysis/Defs.lean:177](../LeanDLRA/Analysis/Defs.lean#L177) | `tubeExt F A a b ρ`: a field that agrees with `F` on the tube and is Lipschitz and bounded everywhere if `F` is so on the tube. |
| `IsOrthProj` | [LinearAlgebra/Projection/Defs.lean:57](../LeanDLRA/LinearAlgebra/Projection/Defs.lean#L57) | `IsOrthProj P`: the continuous linear map `P` is idempotent and symmetric. |
| `tangentProj` | [FixedRank/Defs.lean:81](../LeanDLRA/FixedRank/Defs.lean#L81) | `tangentProj U V`: the map `Z ↦ U Uᵀ Z + Z V Vᵀ - U Uᵀ Z V Vᵀ` of line 5. |
| `HasLocalError` | [Integrators/Defs.lean:133](../LeanDLRA/Integrators/Defs.lean#L133) | `HasLocalError F t₀ t₁ Y₀ Y₁ δ`: `‖Y₁ - Φ t₁‖ ≤ δ` for every solution `Φ` on `[t₀, t₁]` that starts at `Y₀`. |
| `StepMethod` | [Integrators/Method.lean:350](../LeanDLRA/Integrators/Method.lean#L350) | A one-step method for all fields: a map from fields to step relations. |
| `StepMethod.IsTubeLocal` | [Integrators/Method.lean:357](../LeanDLRA/Integrators/Method.lean#L357) | Three properties of one step (a step exists, it keeps the admissible values, it does not see the field outside a tube) from which a run and its error bound are constructed. |

## 3. A worked example: an error bound for your own field

### 3.1 The theorem

The theorem to start with is the existence of a run of the BUG integrator together with its
error bound. The file [`Integrators/Matrix/BUGRun.lean`](../LeanDLRA/Integrators/Matrix/BUGRun.lean) declares, before the
theorem and with the keyword `variable`, the index types `m n` of the matrices, the rank `r`, the
field `F`, the exact solution `A`, the real numbers `t₀ h H T ρ L B ε δ` and the number of steps
`N`; they are not repeated in the statement.

`MatrixBUG.exists_run_norm_sub_le` in [`LeanDLRA/Integrators/Matrix/BUGRun.lean`, lines 280–289](../LeanDLRA/Integrators/Matrix/BUGRun.lean#L280-L289):

```lean
theorem exists_run_norm_sub_le
    (hP : DLRAProblem F A t₀ (t₀ + N * h) ρ L B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A t₀ (t₀ + N * h) ρ))
    (hε : FactoredNormalBoundOn F r (tubeSet A t₀ (t₀ + N * h) ρ) ε) (hε₀ : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hNT : N * h ≤ T)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - A t₀‖ ≤ δ)
    (hsmall : bugGlobalBound L B H T δ ε h + 4 * B * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧ IsRun (stepRel F r) (uniformGrid t₀ h) N Y ∧
      ∀ n ≤ N, (Y n).rank ≤ r ∧ ‖Y n - A (t₀ + n * h)‖ ≤ bugGlobalBound L B H T δ ε h
```

The hypotheses, in the order of the statement:

| Hypothesis | What it says |
|---|---|
| `hP` | `A` solves `Y' = F(t, Y)` on `[t₀, t₀ + N h]`; on the tube of radius `ρ` around `A` the field is `L`-Lipschitz and bounded by `B`. Nothing is assumed outside the tube. |
| `hc` | `(t, Y) ↦ F t Y` is continuous on the tube. |
| `hε`, `hε₀` | On the tube the normal component of `F` at matrices `U S Vᵀ` with `r` orthonormal columns in `U` and `V` has norm at most `ε`, and `0 ≤ ε`. |
| `hh`, `hhH`, `hNT` | The step size satisfies `0 ≤ h ≤ H`, and the `N` steps end before the horizon: `N h ≤ T`. |
| `hrm`, `hrn` | The rank `r` is at most the number of rows and the number of columns. |
| `hY₀`, `hδ` | The start value `Y₀` has rank at most `r` and initial error at most `δ`. |
| `hsmall` | The error bound plus the margin `4 B h` is smaller than the tube radius. |

The conclusion: there are matrices `Y 0 = Y₀, Y 1, …, Y N`, each obtained from the previous one
by a BUG step of size `h`, all of rank at most `r`, whose distance to the exact solution at the
grid times is at most `bugGlobalBound L B H T δ ε h`:

`bugGlobalBound` in [`LeanDLRA/Foundations/Localization.lean`, lines 563–565](../LeanDLRA/Foundations/Localization.lean#L563-L565):

```lean
noncomputable def bugGlobalBound (L B H T δ ε h : ℝ) : ℝ :=
  Real.exp (L * T) * δ + T * Real.exp (L * T) * bugC₁ L H * ε
    + T * Real.exp (L * T) * bugC₂ L B H * h
```

`bugC₁` in [`LeanDLRA/Integrators/Defs.lean`, line 359](../LeanDLRA/Integrators/Defs.lean#L359):

```lean
noncomputable def bugC₁ (L H : ℝ) : ℝ := 2 + 2 * L * H * Real.exp (L * H)
```

`bugC₂` in [`LeanDLRA/Integrators/Defs.lean`, line 363](../LeanDLRA/Integrators/Defs.lean#L363):

```lean
noncomputable def bugC₂ (L B H : ℝ) : ℝ := L * B * (8 + Real.exp (L * H) * (1 + 8 * L * H))
```

The bound is `e^{L T} δ + T e^{L T} (c₁ ε + c₂ h)`. It contains `L`, `B`, `H` and `T` and no
singular value of `Y n` or of `A`. The hypothesis `hsmall` is what a bound on a tube costs: the
bound must show that the run does not leave the tube. A BUG step here is an exact step: the
three differential equations of the step are solved exactly, the theorem makes no statement
about a discretization of them. The source of the theorem is [CerutiLubich2022, Thm. 4]; see
[Main results, section 5](MAIN_RESULTS.md#5-the-bug-integrator).

### 3.2 An application, line by line

The same file applies the theorem to the linear field `F(t, Y) = M Y + Y Nᵀ + G` near a
stationary point `C`, that is, a matrix with `M C + C Nᵀ + G = 0`. Before the example the file
declares `m n` and `r` with `variable`.

[`LeanDLRA/Integrators/Matrix/BUGRun.lean`, lines 381–393](../LeanDLRA/Integrators/Matrix/BUGRun.lean#L381-L393):

```lean
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    (t₀ : ℝ) {ρ T H δ h : ℝ} {K : ℕ} (hρ : 0 ≤ ρ) (hh : 0 ≤ h) (hhH : h ≤ H)
    (hKT : K * h ≤ T) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) (hδ : ‖Y₀ - C‖ ≤ δ)
    (hsmall : bugGlobalBound (‖M‖ + ‖N‖) ((‖M‖ + ‖N‖) * ρ) H T δ ‖G‖ h +
      4 * ((‖M‖ + ‖N‖) * ρ) * h < ρ) :
    ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
      IsRun (stepRel (fun _ Y => M * Y + Y * Nᵀ + G) r) (uniformGrid t₀ h) K Y ∧
      ∀ j ≤ K, (Y j).rank ≤ r ∧
        ‖Y j - C‖ ≤ bugGlobalBound (‖M‖ + ‖N‖) ((‖M‖ + ‖N‖) * ρ) H T δ ‖G‖ h :=
  exists_run_norm_sub_le (A := fun _ => C) (dlraProblem_linear M N G C hC _ _ hρ)
    (continuous_uncurry_linear M N G).continuousOn
    (factoredNormalBoundOn_linear M N G _) (norm_nonneg G) hh hhH hKT hrm hrn hY₀ hδ hsmall
```

* **Line 1.** The data of the field: square matrices `M` and `N`, a source term `G`, and the
  stationary point `C`. (The letter `N` is taken by a matrix here, so the number of steps is
  called `K`.)
* **Line 2.** `hC` says that `C` is stationary. Then the constant function `A(t) = C` solves the
  equation; it is the exact solution of this example. `hrm` and `hrn` are passed on to the
  theorem unchanged.
* **Lines 3 and 4.** The start time `t₀`, the tube radius `ρ ≥ 0`, the step size `h` with
  `0 ≤ h ≤ H`, the number `K` of steps with `K h ≤ T`, and a start value `Y₀` of rank at most `r`
  with `‖Y₀ - C‖ ≤ δ`.
* **Lines 5 and 6.** The hypothesis `hsmall` of the theorem with the constants of this field:
  `L = ‖M‖ + ‖N‖`, `B = (‖M‖ + ‖N‖) ρ` and `ε = ‖G‖`. These three values are the content of
  the example; they come from the three lemmas below.
* **Lines 7 to 10.** The conclusion of the theorem for this field and for `A(t) = C`.
* **Line 11.** The proof is one application of the theorem. `(A := fun _ => C)` names the exact
  solution. The next argument is `hP`; the two underscores in it are the ends of the time
  interval, which Lean reads off from the statement.
* **Line 12.** The argument for `hc`: the field is continuous everywhere, hence on the tube.
* **Line 13.** The argument for `hε` (the underscore is the tube), then `norm_nonneg G` for
  `hε₀`, then the remaining hypotheses in the order of the theorem.

The three facts about the field are lemmas of [`Integrators/Matrix/Defs.lean`](../LeanDLRA/Integrators/Matrix/Defs.lean). The examples of
the projector-splitting integrator and of the parallel BUG integrator use the same lemmas; for
a field of your own they are templates.

*The problem on a tube* (`hP`). The proof gives the five fields of `DLRAProblem` in order: the
solution, `0 ≤ L`, `0 ≤ B`, the Lipschitz condition on the tube and the bound on the tube.

`dlraProblem_linear` in [`LeanDLRA/Integrators/Matrix/Defs.lean`, lines 342–353](../LeanDLRA/Integrators/Matrix/Defs.lean#L342-L353):

```lean
theorem dlraProblem_linear (M : Matrix m m ℝ) (N : Matrix n n ℝ)
    (G C : Matrix m n ℝ) (hC : M * C + C * Nᵀ + G = 0) (a b : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    DLRAProblem (fun _ Y => M * Y + Y * Nᵀ + G) (fun _ => C) a b ρ (‖M‖ + ‖N‖)
      ((‖M‖ + ‖N‖) * ρ) := by
  have hL : 0 ≤ ‖M‖ + ‖N‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨⟨continuousOn_const, fun t _ => ?_⟩, hL, mul_nonneg hL hρ,
    fun _ _ X Y _ _ => norm_linear_sub_le M N G X Y, fun _ _ X hX => ?_⟩
  · exact (hasDerivWithinAt_const t (Ici t) C).congr_deriv hC.symm
  · calc ‖M * X + X * Nᵀ + G‖ = ‖M * X + X * Nᵀ + G - (M * C + C * Nᵀ + G)‖ := by
          rw [hC, sub_zero]
      _ ≤ (‖M‖ + ‖N‖) * ‖X - C‖ := norm_linear_sub_le M N G X C
      _ ≤ (‖M‖ + ‖N‖) * ρ := mul_le_mul_of_nonneg_left hX hL
```

The linear field is not bounded on the whole space, so `IsBoundedField` fails for it. On the
tube of radius `ρ` around `C` it is bounded by `(‖M‖ + ‖N‖) ρ`, whatever the size of `G`,
because it vanishes at `C`. The Lipschitz estimate that the proof uses is

`norm_linear_sub_le` in [`LeanDLRA/Integrators/Matrix/Defs.lean`, lines 322–324](../LeanDLRA/Integrators/Matrix/Defs.lean#L322-L324):

```lean
theorem norm_linear_sub_le (M : Matrix m m ℝ) (N : Matrix n n ℝ)
    (G X Y : Matrix m n ℝ) :
    ‖M * X + X * Nᵀ + G - (M * Y + Y * Nᵀ + G)‖ ≤ (‖M‖ + ‖N‖) * ‖X - Y‖
```

and rests on `Frobenius.norm_mul_le`, the bound `‖A * B‖ ≤ ‖A‖ * ‖B‖` for the Frobenius norm.

*Continuity* (`hc`).

`continuous_uncurry_linear` in [`LeanDLRA/Integrators/Matrix/Defs.lean`, lines 356–362](../LeanDLRA/Integrators/Matrix/Defs.lean#L356-L362):

```lean
theorem continuous_uncurry_linear (M : Matrix m m ℝ) (N : Matrix n n ℝ)
    (G : Matrix m n ℝ) :
    Continuous (Function.uncurry fun (_ : ℝ) (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G) := by
  change Continuous fun p : ℝ × Matrix m n ℝ =>
    Frobenius.leftMulCLM M p.2 + Frobenius.rightMulCLM Nᵀ p.2 + G
  exact (((Frobenius.leftMulCLM M).continuous.comp continuous_snd).add
    ((Frobenius.rightMulCLM Nᵀ).continuous.comp continuous_snd)).add continuous_const
```

`Frobenius.leftMulCLM M` and `Frobenius.rightMulCLM M` are the multiplications by a fixed matrix
from the left and from the right as continuous linear maps. A field built from such maps is
continuous by the lemmas of Mathlib.

*The normal component* (`hε`).

`factoredNormalBoundOn_linear` in [`LeanDLRA/Integrators/Matrix/Defs.lean`, lines 266–268](../LeanDLRA/Integrators/Matrix/Defs.lean#L266-L268):

```lean
theorem factoredNormalBoundOn_linear (M : Matrix m m ℝ) (N : Matrix n n ℝ)
    (G : Matrix m n ℝ) (D : Set (ℝ × Matrix m n ℝ)) :
    FactoredNormalBoundOn (fun _ (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G) r D ‖G‖
```

At `Y = U S Vᵀ` the terms `M Y` and `Y Nᵀ` have no normal component: `M Y (I - V Vᵀ) = 0` and
`(I - U Uᵀ) Y Nᵀ = 0`. What remains is the normal component of `G`. It is at most `‖G‖`, because
multiplication by `I - U Uᵀ` from the left and by `I - V Vᵀ` from the right does not increase
the Frobenius norm (`MatrixBUG.norm_normal_le`). This value of `ε` is the crudest one possible; the example
shows that the hypotheses can be met, and a smaller `ε` gives a smaller error bound.

### 3.3 The same for your own field

To apply the theorem to a field `F` of your own you provide the same things.

1. **An exact solution and the constants on a tube** (`hP`). If `F` is Lipschitz and bounded on
   the whole space, `DLRAProblem.of_global` gives `hP` for every radius `ρ` from
   `IsLipschitzField F L` with `0 ≤ L`, `IsBoundedField F B` and a solution `A`, and
   `exists_ODESolution` gives a solution if `F` is in addition continuous in time. Otherwise choose a radius `ρ`, prove the
   Lipschitz condition and the bound on the tube (`IsLipschitzOnTube`, `IsBoundedOnTube`) and
   give the five fields as in `dlraProblem_linear` above.
2. **Continuity on the tube** (`hc`).
3. **The normal component** (`hε`). The proof starts by introducing `t`, `U`, `V`, `S`, the
   hypotheses `Uᵀ * U = 1` and `Vᵀ * V = 1` and the membership `(t, U * S * Vᵀ) ∈ D`; the lemma
   above does this with `intro t U V S hU hV _`. It then bounds
   `‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖`. Terms of the form `M Y` or `Y Nᵀ` drop
   out. `FactoredNormalBoundOn.mono` passes to a smaller region or a larger `ε`.
4. **The smallness condition** (`hsmall`). For given numbers it is an inequality between real
   numbers. If only the existence of a suitable `δ` and `h` is needed, use
   `exists_bugGlobalBound_lt`, quoted below.

The lemma for the smallness condition:

`exists_bugGlobalBound_lt` in [`LeanDLRA/Integrators/Matrix/BUGRun.lean`, lines 315–317](../LeanDLRA/Integrators/Matrix/BUGRun.lean#L315-L317):

```lean
theorem exists_bugGlobalBound_lt {L B H T ε ρ : ℝ} (hH : 0 < H)
    (hε : T * Real.exp (L * T) * bugC₁ L H * ε < ρ) :
    ∃ δ > 0, ∃ h > 0, h ≤ H ∧ bugGlobalBound L B H T δ ε h + 4 * B * h < ρ
```

The next example of the file uses it for the linear field. Its statement has no hypothesis on
`δ` and `h`; the only condition left is `hG`, which says that the part of the error bound that
does not vanish with `δ` and `h` is smaller than the tube radius:

[`LeanDLRA/Integrators/Matrix/BUGRun.lean`, lines 401–409](../LeanDLRA/Integrators/Matrix/BUGRun.lean#L401-L409):

```lean
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    (t₀ : ℝ) {ρ T H : ℝ} (hT : 0 ≤ T) (hH : 0 < H)
    (hG : T * Real.exp ((‖M‖ + ‖N‖) * T) * bugC₁ (‖M‖ + ‖N‖) H * ‖G‖ < ρ) :
    ∃ δ > 0, ∃ h > 0, ∀ K : ℕ, K * h ≤ T → ∀ Y₀ : Matrix m n ℝ, Y₀.rank ≤ r → ‖Y₀ - C‖ ≤ δ →
      ∃ Y : ℕ → Matrix m n ℝ, Y 0 = Y₀ ∧
        IsRun (stepRel (fun _ Y => M * Y + Y * Nᵀ + G) r) (uniformGrid t₀ h) K Y ∧
        ∀ j ≤ K, (Y j).rank ≤ r ∧
          ‖Y j - C‖ ≤ bugGlobalBound (‖M‖ + ‖N‖) ((‖M‖ + ‖N‖) * ρ) H T δ ‖G‖ h
```

If you already have a run, for example from another construction, `MatrixBUG.IsRun.norm_sub_le`
gives the same bound for it under the same hypotheses on `F` and `A`.

### 3.4 Other integrators

The projector-splitting integrator, the parallel BUG integrator of fixed rank, the BUG
integrator with explicit Euler substeps and the BUG integrator with augmented bases and
truncation to a fixed rank have theorems of the same form:
`MatrixKSL.exists_run_norm_sub_le` in [`Integrators/Matrix/KSLRun.lean`](../LeanDLRA/Integrators/Matrix/KSLRun.lean),
`MatrixParallelBUG.exists_run_norm_sub_le` in
[`Integrators/Matrix/ParallelBUGRun.lean`](../LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean),
`MatrixEulerBUG.exists_run_norm_sub_le` in [`Integrators/Matrix/EulerBUGRun.lean`](../LeanDLRA/Integrators/Matrix/EulerBUGRun.lean)
and `MatrixBUG.trunc_exists_run_norm_sub_le` in
[`Integrators/Matrix/TruncBUGRun.lean`](../LeanDLRA/Integrators/Matrix/TruncBUGRun.lean). Their hypotheses `hP`, `hc`, `hε`, `hε₀` on
`F` and `A` are those of the theorem above, so the three lemmas of section 3.2 serve all five
integrators. The theorem for explicit Euler substeps has two more hypotheses, `hLt` and `hFt`:
the field is Lipschitz in time with a constant `Lt` on the tube; for a field that does not
depend on time, `Lt = 0`. The theorem for the truncation to a fixed rank has the hypothesis
`hκ : 1 ≤ κ` on the quality of the truncation and, like the theorem above, `hhH`; the three
others have no hypothesis `hhH`. The bounds and margins differ:

| Integrator | Step relation | Error bound | Margin in `hsmall` |
|---|---|---|---|
| BUG | `MatrixBUG.stepRel` | `e^{L T} δ + T e^{L T} (bugC₁ L H ε + bugC₂ L B H h)` | `4 B h` |
| projector splitting | `MatrixKSL.stepRel` | `e^{L T} δ + T e^{L T} (10 L B h + ε)` | `4 B h` |
| parallel BUG, fixed rank | `MatrixParallelBUG.stepRel` | `e^{L T} δ + T e^{L T} (24 L B h + 3 ε)` | `2 B h` |
| BUG with explicit Euler substeps, fixed rank | `MatrixEulerBUG.stepRel` | `e^{L T} δ + T e^{L T} ((11 L B + Lt) h + 3 ε)` | `2 B h` |
| BUG with augmented bases, truncated to rank `r` | `MatrixBUG.truncStepRel` | `e^{L T} δ + T e^{L T} (κ (10 L B h + ε) + (1 + κ) (bugC₁ L H ε + bugC₂ L B H h))` | `4 B h` |

All five are instances of one theorem, `StepMethod.IsTubeLocal.exists_run_norm_sub_le` in
[`Integrators/Method.lean`](../LeanDLRA/Integrators/Method.lean); see
[Main results, section 4.3](MAIN_RESULTS.md#43-one-run-theorem-many-methods).

Eight more methods have run theorems of this kind, with the same hypotheses `hP`, `hc`, `hε` on
`F` and `A`: the rank-adaptive BUG integrator and the parallel BUG integrator with truncation by a
tolerance `ϑ` (`MatrixBUG.adaptive_exists_run_norm_sub_le`,
`MatrixParallelBUG.adaptive_exists_run_norm_sub_le`; the bound has the extra term `e^{L T} n ϑ`
for `n` steps), the dynamical randomized SVD (`MatrixDRSVD.exists_run_norm_sub_le`), the BUG
integrator for Tucker tensors (`TuckerBUG.exists_run_norm_sub_le`), the projected Euler method
(`MatrixProjEuler.exists_run_norm_sub_le`) and the projected Runge–Kutta methods
(`MatrixPRK.exists_run_norm_sub_le`, which assumes the order of the classical scheme), and the
midpoint BUG integrator of fixed rank (`MatrixMidpointBUG.exists_run_norm_sub_le`, for a field of
class `C²` with bounds on its derivatives; its error is of order `h²` up to the terms in the
normal bounds) and the explicit midpoint method in bases with `2 r` columns
(`ExplicitMidpoint.exists_run_norm_sub_le`, same regularity; two evaluations of `F`). The table of
section 4.3 of the page on main results lists them with their
margins.

## 4. Where do I find what

| You are looking for | Read |
|---|---|
| a definition by its name | [Definitions](DEFINITIONS.md) |
| the relation between two definitions of one notion | [Concepts](CONCEPTS.md) |
| solutions, Lipschitz and bounded fields, tubes | [`Analysis/Defs.lean`](../LeanDLRA/Analysis/Defs.lean) |
| existence of a solution of a differential equation | [`Foundations/Existence.lean`](../LeanDLRA/Foundations/Existence.lean); for fields that are Lipschitz and bounded on a region only [`Foundations/AprioriExistence.lean`](../LeanDLRA/Foundations/AprioriExistence.lean) |
| the mean value inequality and Grönwall inequalities | [`Foundations/ODE.lean`](../LeanDLRA/Foundations/ODE.lean), [`Foundations/Gronwall.lean`](../LeanDLRA/Foundations/Gronwall.lean) |
| orthogonal projectors | [`LinearAlgebra/Projection/Defs.lean`](../LeanDLRA/LinearAlgebra/Projection/Defs.lean), [`Foundations/Projector.lean`](../LeanDLRA/Foundations/Projector.lean) |
| the Frobenius norm and inner product of matrices | [`LinearAlgebra/Frobenius/Defs.lean`](../LeanDLRA/LinearAlgebra/Frobenius/Defs.lean), [`Matrix/Frobenius.lean`](../LeanDLRA/Matrix/Frobenius.lean) |
| the singular value decomposition and the Eckart–Young–Mirsky theorem | [`Classical/SVD.lean`](../LeanDLRA/Classical/SVD.lean), [`LinearAlgebra/SVD/Defs.lean`](../LeanDLRA/LinearAlgebra/SVD/Defs.lean), [`Classical/EckartYoung.lean`](../LeanDLRA/Classical/EckartYoung.lean) |
| lower bounds for singular values, the derivative of the truncated singular value decomposition, perturbation of singular subspaces | [`LinearAlgebra/SVD/MinMax.lean`](../LeanDLRA/LinearAlgebra/SVD/MinMax.lean), [`LinearAlgebra/SVD/TruncationDeriv.lean`](../LeanDLRA/LinearAlgebra/SVD/TruncationDeriv.lean), [`LinearAlgebra/SVD/SinTheta.lean`](../LeanDLRA/LinearAlgebra/SVD/SinTheta.lean) |
| the matrices of rank at most `r` and the distance to them | [`LinearAlgebra/LowRank/Defs.lean`](../LeanDLRA/LinearAlgebra/LowRank/Defs.lean), [`Matrix/LowRankDistance.lean`](../LeanDLRA/Matrix/LowRankDistance.lean), [`Matrix/LowRankDistanceFlow.lean`](../LeanDLRA/Matrix/LowRankDistanceFlow.lean) (along the exact flow) |
| the matrices of rank exactly `r`; the rank of a function of two variables | [`LinearAlgebra/LowRank/SepRank.lean`](../LeanDLRA/LinearAlgebra/LowRank/SepRank.lean) |
| the tangent projector `P(Y)` and its dependence on `Y` | [`FixedRank/Defs.lean`](../LeanDLRA/FixedRank/Defs.lean), [`Matrix/Projectors.lean`](../LeanDLRA/Matrix/Projectors.lean), [`Matrix/Curvature.lean`](../LeanDLRA/Matrix/Curvature.lean) |
| the tangent projector and the tangent space at a matrix `Y`, without a factorization | [`FixedRank/TangentSpace/Defs.lean`](../LeanDLRA/FixedRank/TangentSpace/Defs.lean), [`FixedRank/TangentSpace.lean`](../LeanDLRA/FixedRank/TangentSpace.lean); its dependence on `Y`, tangent velocities and first-order optimality in [`FixedRank/TangentSpace/Curvature.lean`](../LeanDLRA/FixedRank/TangentSpace/Curvature.lean); the Lipschitz bound of the projector with the constant `1` (and the sharpness example) in [`FixedRank/TangentSpace/ProjectorLipschitz.lean`](../LeanDLRA/FixedRank/TangentSpace/ProjectorLipschitz.lean), the bounds on normal vectors with the spectral norm in [`FixedRank/TangentSpace/ProjectorSpectral.lean`](../LeanDLRA/FixedRank/TangentSpace/ProjectorSpectral.lean); the distance to rank `r` after a tangent step in [`FixedRank/TangentStepTruncation.lean`](../LeanDLRA/FixedRank/TangentStepTruncation.lean) |
| the problem on a tube and bounds for the normal component | [`DLRA/Defs.lean`](../LeanDLRA/DLRA/Defs.lean), [`Integrators/Matrix/Defs.lean`](../LeanDLRA/Integrators/Matrix/Defs.lean), [`Integrators/Matrix/FactoredNormalBound.lean`](../LeanDLRA/Integrators/Matrix/FactoredNormalBound.lean) |
| the projected equation `Y' = P(Y) F(t, Y)` and the equations for the factors | [`Dynamics/ContinuousDLRA.lean`](../LeanDLRA/Dynamics/ContinuousDLRA.lean), [`Matrix/GaugeODE.lean`](../LeanDLRA/Matrix/GaugeODE.lean); DLRA solutions and the dynamically orthogonal, dual and bi-orthogonal systems in [`DLRA/DynamicallyOrthogonal.lean`](../LeanDLRA/DLRA/DynamicallyOrthogonal.lean) (the definition `IsDLRASolution` is in [`DLRA/Defs.lean`](../LeanDLRA/DLRA/Defs.lean)); the distance from the best approximation of rank `r` for matrices in [`DLRA/QuasiOptimality.lean`](../LeanDLRA/DLRA/QuasiOptimality.lean), for a field that is Lipschitz on a tube only in [`DLRA/QuasiOptimalityTube.lean`](../LeanDLRA/DLRA/QuasiOptimalityTube.lean), for the truncated singular value decomposition under a gap in [`DLRA/QuasiOptimalityGap.lean`](../LeanDLRA/DLRA/QuasiOptimalityGap.lean), with a margin up to `θ ρ`, `θ < 1/2`, in [`DLRA/QuasiOptimalityMargin.lean`](../LeanDLRA/DLRA/QuasiOptimalityMargin.lean), with `θ < 1` in [`DLRA/QuasiOptimalityNormal.lean`](../LeanDLRA/DLRA/QuasiOptimalityNormal.lean) (its other forms, with the error against `A`, on a tube and under a gap, in [`DLRA/QuasiOptimalitySharp.lean`](../LeanDLRA/DLRA/QuasiOptimalitySharp.lean); the truncated singular value decomposition in [`DLRA/QuasiOptimalityTruncation.lean`](../LeanDLRA/DLRA/QuasiOptimalityTruncation.lean)), with the spectral norm of the tail, also as a condition on `σ_r(A)`, in [`DLRA/QuasiOptimalitySpectral.lean`](../LeanDLRA/DLRA/QuasiOptimalitySpectral.lean); existence and uniqueness of the DLRA solution in [`DLRA/Existence.lean`](../LeanDLRA/DLRA/Existence.lean); the gauge of the factors in [`DLRA/GaugeInvariance.lean`](../LeanDLRA/DLRA/GaugeInvariance.lean) |
| grids, steps, runs, local errors | [`Integrators/Defs.lean`](../LeanDLRA/Integrators/Defs.lean) |
| the global error from local errors | [`Integrators/GlobalError.lean`](../LeanDLRA/Integrators/GlobalError.lean), [`Integrators/Tube.lean`](../LeanDLRA/Integrators/Tube.lean) |
| the theorem to instantiate for a new integrator | [`Integrators/Method.lean`](../LeanDLRA/Integrators/Method.lean); for a grid with variable step sizes [`Integrators/MethodGrid.lean`](../LeanDLRA/Integrators/MethodGrid.lean), for steps that end with a truncation to a tolerance [`Integrators/MethodTolerance.lean`](../LeanDLRA/Integrators/MethodTolerance.lean), with a one-sided Lipschitz constant in place of `L` in the propagation of errors [`Integrators/MethodOneSided.lean`](../LeanDLRA/Integrators/MethodOneSided.lean) |
| the BUG integrator | [`Integrators/Matrix/BUGRun.lean`](../LeanDLRA/Integrators/Matrix/BUGRun.lean) (start here), [`Integrators/Matrix/BUGStep.lean`](../LeanDLRA/Integrators/Matrix/BUGStep.lean), [`Integrators/Matrix/BUG.lean`](../LeanDLRA/Integrators/Matrix/BUG.lean); on a general state space [`Integrators/BUGCore.lean`](../LeanDLRA/Integrators/BUGCore.lean), [`Integrators/BUG.lean`](../LeanDLRA/Integrators/BUG.lean); smaller constants in the local error in [`Integrators/BUGCapture.lean`](../LeanDLRA/Integrators/BUGCapture.lean), runs with a one-sided Lipschitz constant in [`Integrators/Matrix/BUGRunOneSided.lean`](../LeanDLRA/Integrators/Matrix/BUGRunOneSided.lean) (the general form for tube-local methods is [`Integrators/MethodOneSided.lean`](../LeanDLRA/Integrators/MethodOneSided.lean)) |
| the projector-splitting integrator | [`Integrators/Matrix/KSLRun.lean`](../LeanDLRA/Integrators/Matrix/KSLRun.lean), [`Integrators/Matrix/KSLStep.lean`](../LeanDLRA/Integrators/Matrix/KSLStep.lean), [`Integrators/Matrix/ProjectorSplitting.lean`](../LeanDLRA/Integrators/Matrix/ProjectorSplitting.lean); on a general state space [`Integrators/ProjectorSplitting.lean`](../LeanDLRA/Integrators/ProjectorSplitting.lean) |
| the parallel BUG integrator | [`Integrators/Matrix/ParallelBUGRun.lean`](../LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean), [`Integrators/Matrix/ParallelBUGStep.lean`](../LeanDLRA/Integrators/Matrix/ParallelBUGStep.lean), [`Integrators/Matrix/ParallelBUG.lean`](../LeanDLRA/Integrators/Matrix/ParallelBUG.lean); with truncation by a tolerance [`Integrators/Matrix/ParallelBUGTolRun.lean`](../LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean); on a general state space [`Integrators/ParallelBUG.lean`](../LeanDLRA/Integrators/ParallelBUG.lean) |
| the rank-adaptive BUG integrator | [`Integrators/RankAdaptiveBUG.lean`](../LeanDLRA/Integrators/RankAdaptiveBUG.lean), [`Integrators/Matrix/BUG.lean`](../LeanDLRA/Integrators/Matrix/BUG.lean); as step relations with a truncation by a tolerance or to a fixed rank [`Integrators/Matrix/AdaptiveBUGStep.lean`](../LeanDLRA/Integrators/Matrix/AdaptiveBUGStep.lean), runs with truncation by a tolerance [`Integrators/Matrix/AdaptiveBUGRun.lean`](../LeanDLRA/Integrators/Matrix/AdaptiveBUGRun.lean), runs with truncation to a fixed rank [`Integrators/Matrix/TruncBUGRun.lean`](../LeanDLRA/Integrators/Matrix/TruncBUGRun.lean); a lower bound and two upper bounds for one step in [`Research/AugmentationRank.lean`](../LeanDLRA/Research/AugmentationRank.lean), a bound for a field with a two-sided term in [`Research/TwoSidedLeak.lean`](../LeanDLRA/Research/TwoSidedLeak.lean); fields of Sylvester type in [`Research/SylvesterFlows.lean`](../LeanDLRA/Research/SylvesterFlows.lean) (the auxiliary flows exist), [`Research/SylvesterGlobal.lean`](../LeanDLRA/Research/SylvesterGlobal.lean) (global order two), [`Research/PerturbedSylvester.lean`](../LeanDLRA/Research/PerturbedSylvester.lean) (a Lipschitz perturbation), [`Research/TwoSidedPadded.lean`](../LeanDLRA/Research/TwoSidedPadded.lean) (a start padded with the images of a two-sided term) and [`Research/RankOneGalerkinBarrier.lean`](../LeanDLRA/Research/RankOneGalerkinBarrier.lean) (a Galerkin step in a fixed rank-one space is not of second order); a-posteriori bounds and tolerance schedules in [`Integrators/RankAdaptiveBUGAposteriori.lean`](../LeanDLRA/Integrators/RankAdaptiveBUGAposteriori.lean), the rank decision in [`Integrators/RankSelection.lean`](../LeanDLRA/Integrators/RankSelection.lean) |
| the BUG integrator with explicit Euler substeps | [`Integrators/Matrix/EulerBUGRun.lean`](../LeanDLRA/Integrators/Matrix/EulerBUGRun.lean) (start here), [`Integrators/Matrix/EulerBUGStep.lean`](../LeanDLRA/Integrators/Matrix/EulerBUGStep.lean); on a general state space [`Integrators/EulerBUG.lean`](../LeanDLRA/Integrators/EulerBUG.lean) |
| stiff problems: one-sided Lipschitz fields, implicit steps, the primal–dual error representation | [`Foundations/OneSided.lean`](../LeanDLRA/Foundations/OneSided.lean), [`Stiff/ImplicitBUG.lean`](../LeanDLRA/Stiff/ImplicitBUG.lean); the implicit BUG step on matrices in [`Stiff/Defs.lean`](../LeanDLRA/Stiff/Defs.lean), its local error and existence in [`Stiff/ImplicitBUGStep.lean`](../LeanDLRA/Stiff/ImplicitBUGStep.lean), its runs (a bound that is not stiffness-uniform) in [`Stiff/ImplicitBUGRun.lean`](../LeanDLRA/Stiff/ImplicitBUGRun.lean), [`Stiff/ImplicitSolvability.lean`](../LeanDLRA/Stiff/ImplicitSolvability.lean), [`Stiff/DualWeightedResidual.lean`](../LeanDLRA/Stiff/DualWeightedResidual.lean) |
| stiff problems: one step for a field with a stiff linear part | [`Stiff/CouplingLocalError.lean`](../LeanDLRA/Stiff/CouplingLocalError.lean) (a local error bound with coupling numbers), [`Research/StiffOrderReduction.lean`](../LeanDLRA/Research/StiffOrderReduction.lean) (a family of problems without a uniform constant for one step), [`Research/StiffGlobalCycle.lean`](../LeanDLRA/Research/StiffGlobalCycle.lean) (a family of problems without a uniform constant for the global error) |
| stiff problems: the error against the variation of the forcing | [`Research/StiffGlobalVariation.lean`](../LeanDLRA/Research/StiffGlobalVariation.lean) (a lower bound), [`Research/StiffEnergyGalerkin.lean`](../LeanDLRA/Research/StiffEnergyGalerkin.lean) (an energy bound without coupling numbers), [`Research/StiffOldColumnGalerkin.lean`](../LeanDLRA/Research/StiffOldColumnGalerkin.lean) and [`Research/StiffOldColumnVariation.lean`](../LeanDLRA/Research/StiffOldColumnVariation.lean) (invariant old column spaces), [`Research/StiffVelocityVariation.lean`](../LeanDLRA/Research/StiffVelocityVariation.lean) (the sum of the velocity changes is not bounded by the data), [`Research/StiffInvariantGalerkin.lean`](../LeanDLRA/Research/StiffInvariantGalerkin.lean) (a Galerkin space that is invariant under the stiff operator); whether a bound `C (h (1 + Var g) + ε + n ϑ)` holds uniformly in the stiffness is open, [Main results, section 7.6](MAIN_RESULTS.md#76-stiff-problems-with-forcing-six-results-and-what-stays-open) |
| steps of higher order | [`HighOrder/MidpointBUG.lean`](../LeanDLRA/HighOrder/MidpointBUG.lean), [`HighOrder/MidpointBUGGlobal.lean`](../LeanDLRA/HighOrder/MidpointBUGGlobal.lean) (the global error bound of second order), [`HighOrder/RungeKuttaBUG.lean`](../LeanDLRA/HighOrder/RungeKuttaBUG.lean); the midpoint BUG step for matrices in [`HighOrder/Defs.lean`](../LeanDLRA/HighOrder/Defs.lean) and [`HighOrder/MidpointBUGStep.lean`](../LeanDLRA/HighOrder/MidpointBUGStep.lean) (local error), its runs and error bound in [`HighOrder/MidpointBUGRun.lean`](../LeanDLRA/HighOrder/MidpointBUGRun.lean); local errors of an explicit midpoint update in augmented bases in [`Research/ExplicitMidpointGalerkin.lean`](../LeanDLRA/Research/ExplicitMidpointGalerkin.lean), the size of its capture defects (of order `h² + ε`) in [`Research/ExplicitMidpointCapture.lean`](../LeanDLRA/Research/ExplicitMidpointCapture.lean), its step relation in [`HighOrder/Defs.lean`](../LeanDLRA/HighOrder/Defs.lean) and its runs (error of order `h² + ε`) in [`Research/ExplicitMidpointRun.lean`](../LeanDLRA/Research/ExplicitMidpointRun.lean) |
| projected Euler and projected Runge–Kutta methods | [`Integrators/Matrix/ProjectedEuler.lean`](../LeanDLRA/Integrators/Matrix/ProjectedEuler.lean), [`Integrators/Matrix/ProjectedRK.lean`](../LeanDLRA/Integrators/Matrix/ProjectedRK.lean) (runs and global error), [`HighOrder/ProjectedRK.lean`](../LeanDLRA/HighOrder/ProjectedRK.lean) (stage analysis), [`Integrators/Matrix/FlowDistance.lean`](../LeanDLRA/Integrators/Matrix/FlowDistance.lean) (distance of the exact solution to the matrices of rank at most `r`) |
| steps with interpolation or random sketches | [`Randomized/ObliqueBUG.lean`](../LeanDLRA/Randomized/ObliqueBUG.lean), [`Randomized/RandomizedBUG.lean`](../LeanDLRA/Randomized/RandomizedBUG.lean); the dynamical randomized SVD as a step relation [`Randomized/DRSVDStep.lean`](../LeanDLRA/Randomized/DRSVDStep.lean) and its runs [`Randomized/DRSVDRun.lean`](../LeanDLRA/Randomized/DRSVDRun.lean); cross interpolation of the tangent projector in [`Randomized/CrossInterpolation.lean`](../LeanDLRA/Randomized/CrossInterpolation.lean) |
| conservation and energy stability | [`Stability/Conservation.lean`](../LeanDLRA/Stability/Conservation.lean), [`Stability/Energy.lean`](../LeanDLRA/Stability/Energy.lean), [`Stability/NormBalance.lean`](../LeanDLRA/Stability/NormBalance.lean) (norm balance of one step) |
| tensors: Tucker format, tensor trains, tree tensor networks | [`Tensor/Defs.lean`](../LeanDLRA/Tensor/Defs.lean), [`Tensor/Tucker/`](../LeanDLRA/Tensor/Tucker/), [`Tensor/TT/`](../LeanDLRA/Tensor/TT/), [`Tensor/TTN/`](../LeanDLRA/Tensor/TTN/), [`Integrators/TuckerBUG.lean`](../LeanDLRA/Integrators/TuckerBUG.lean), [`Integrators/TuckerBUGCore.lean`](../LeanDLRA/Integrators/TuckerBUGCore.lean); the Tucker BUG step as a step relation and its runs [`Tensor/Tucker/BUGStep.lean`](../LeanDLRA/Tensor/Tucker/BUGStep.lean), [`Tensor/Tucker/BUGRun.lean`](../LeanDLRA/Tensor/Tucker/BUGRun.lean); exactness and robust error of the tensor-train projector-splitting integrator in [`Tensor/TT/ProjectorSplittingExactness.lean`](../LeanDLRA/Tensor/TT/ProjectorSplittingExactness.lean) and [`Tensor/TT/ProjectorSplittingError.lean`](../LeanDLRA/Tensor/TT/ProjectorSplittingError.lean); orthonormality of tree tensor network bases in [`Tensor/TTN/BasisOrthonormality.lean`](../LeanDLRA/Tensor/TTN/BasisOrthonormality.lean); the step predicates of the tensor integrators on a general state space in [`Tensor/Steps.lean`](../LeanDLRA/Tensor/Steps.lean), the theorems about them in [`Tensor/TTN/Abstract/`](../LeanDLRA/Tensor/TTN/Abstract/) |
| kinetic equations | [`Kinetic/Defs.lean`](../LeanDLRA/Kinetic/Defs.lean) (definitions), [`Kinetic/LowRank.lean`](../LeanDLRA/Kinetic/LowRank.lean) (the rank of the low-rank ansatz) and [`Kinetic/Stencils.lean`](../LeanDLRA/Kinetic/Stencils.lean) (products and transposes of the periodic difference matrices); the collision field of a material mixture is in [`Kinetic/MaterialMixtureCollision.lean`](../LeanDLRA/Kinetic/MaterialMixtureCollision.lean). The core has no error theorem for kinetic equations; results of single papers are in the catalogue folder [`Literature/Kinetic/`](../LeanDLRA/Literature/Kinetic/). |
| low-rank training | [`Training/Defs.lean`](../LeanDLRA/Training/Defs.lean), [`Training/Descent.lean`](../LeanDLRA/Training/Descent.lean), [`Training/GradientFlowConvergence.lean`](../LeanDLRA/Training/GradientFlowConvergence.lean), [`Training/ConvergenceRates.lean`](../LeanDLRA/Training/ConvergenceRates.lean), [`Training/FederatedDescent.lean`](../LeanDLRA/Training/FederatedDescent.lean); thresholds for federated rounds in [`Research/FederatedDescentThreshold.lean`](../LeanDLRA/Research/FederatedDescentThreshold.lean), [`Research/FederatedConvexThreshold.lean`](../LeanDLRA/Research/FederatedConvexThreshold.lean), [`Research/FederatedTwoSteps.lean`](../LeanDLRA/Research/FederatedTwoSteps.lean) and [`Research/FederatedThreeSteps.lean`](../LeanDLRA/Research/FederatedThreeSteps.lean) (and, for every number of local steps, descent when `sstar lr β < 4`, [`Research/FederatedManySteps.lean`](../LeanDLRA/Research/FederatedManySteps.lean)); fixed points of federated rounds in [`Training/FederatedFixedPoints.lean`](../LeanDLRA/Training/FederatedFixedPoints.lean); the explicit Euler splitting step in [`Training/ProjectorSplittingDescent.lean`](../LeanDLRA/Training/ProjectorSplittingDescent.lean) |
| filtering | [`Filtering/Defs.lean`](../LeanDLRA/Filtering/Defs.lean), [`Stochastic/KalmanBucy.lean`](../LeanDLRA/Stochastic/KalmanBucy.lean), [`Stochastic/GramianLowerBound.lean`](../LeanDLRA/Stochastic/GramianLowerBound.lean) |
| optimal control | [`Control/AdjointDLRA.lean`](../LeanDLRA/Control/AdjointDLRA.lean) |
| the results of one paper | [PROVEN.md](catalogue/PROVEN.md), which lists modules with the papers they cite; the paper files are in [`Literature/`](../LeanDLRA/Literature/) |

Every module starts with a docstring that says what the file contains; read it before the
declarations.

## 5. Core and catalogue

The Lean sources below `LeanDLRA/` form two libraries ([STRUCTURE.md](STRUCTURE.md)).

* The **core** is the set of modules imported by `LeanDLRA.lean`, 227 modules at the commit
  named above. Its theorems are stated in shared definitions, so they can be combined: the
  solution of one theorem is the solution of the next, a run is a run. This page,
  [Main results](MAIN_RESULTS.md) and [Definitions](DEFINITIONS.md) describe the core only.
* The **catalogue** is everything else: files in the folders `LeanDLRA/Literature`,
  `LeanDLRA/OpenProblems`, `LeanDLRA/Novel` and `LeanDLRA/Corrections`. A paper file states
  results of one paper, as a rule in definitions of its own or of the paper. Its theorems are
  proven and checked like those of the core, but a catalogue theorem does not automatically
  apply to the objects of the core. `LeanDLRACatalogue.lean` imports the core and the catalogue.

The two imports, as [STRUCTURE.md](STRUCTURE.md) gives them:

[`docs/STRUCTURE.md`, lines 45–46](../docs/STRUCTURE.md#L45-L46):

```text
import LeanDLRA                              -- the core
import LeanDLRACatalogue                     -- the core and the catalogue
```

A single module can be imported in the same way; the theorem of section 3 is in the module that
the root file of the core imports with the line

[`LeanDLRA.lean`, line 81](../LeanDLRA.lean#L81):

```lean
import LeanDLRA.Integrators.Matrix.BUGRun
```

A core module imports core modules only. A catalogue module becomes a core module when its
definitions are the core definitions or are proven equal to them; the file does not move, its
name is added to `docs/promoted.txt` ([STRUCTURE.md](STRUCTURE.md), paragraph "Promotion").
A core module can therefore lie in a catalogue folder.

If you look for a statement of a paper, the catalogue may have it. If you want to build on a
result, use the core, or connect the catalogue result to the core definitions first.

## 6. How to add a result

The rules are in [CONVENTIONS.md](CONVENTIONS.md). In short:

1. **Find the place.** A result that is stated in core definitions belongs to the core, in the
   folder of its topic; a file imports only files of lower layers (section 2 of the conventions).
   A result of one paper in the paper's own definitions belongs to the catalogue.
2. **Reuse definitions.** Look for the notion in [Definitions](DEFINITIONS.md) and in
   [Concepts](CONCEPTS.md) before you define anything. A new definition goes into the file
   `<Folder>/Defs.lean` of its folder (section 3) and comes with lemmas that relate it to the definitions
   that exist. For problems on a tube and for runs, the definitions of
   [`DLRA/Defs.lean`](../LeanDLRA/DLRA/Defs.lean) and [`Integrators/Defs.lean`](../LeanDLRA/Integrators/Defs.lean) are the reference.
3. **State and name.** Notation and hypotheses as in sections 4 to 6, names as in section 7.
4. **Document.** A module docstring with the layout of section 8, a docstring for every public
   declaration, and papers cited as in section 9.
5. **Show that the hypotheses can be met.** A new structure or main theorem gets an `example`
   that satisfies all its hypotheses, like the example of section 3.2.
6. **Check the file.** The script [`scripts/fc`](../scripts/fc) checks one file against the compiled
   library without building anything (usage below). `scripts/warm.sh --list` names the modules
   whose compiled state is missing or out of date.
7. **Verify.** `make verify` regenerates the root files, checks that the core imports core
   modules only, builds the core, searches the sources for placeholders and checks that every
   constant of the core depends on the three standard axioms only. `make ci` adds the checks
   and tests of the Python scripts. The core workflow of CI
   (`.github/workflows/lean_action_ci.yml`) builds the core with warnings as errors, runs the
   same audit and the same Python checks, and replays the changed core modules in an
   independent kernel check. Contributions come as pull requests; the maintainers merge
   through the gate ([`scripts/gate.py`](../scripts/gate.py)), which builds the changed files with warnings as
   errors, builds the core and audits both.

The usage of the single-file check, from the header of the script:

[`scripts/fc`, lines 8–11](../scripts/fc#L8-L11):

```text
#   scripts/fc FILE.lean                 errors and warnings, exit 0 only if there are none
#   scripts/fc --axioms FILE.lean        also fail on any axiom beyond the three standard ones
#   scripts/fc --min-free=N FILE.lean    start only if N % of the memory is free (default 35;
#                                        0 switches the test off)
```

The script ends with code 0 if there is neither an error nor a warning, with 1 if there is one,
with 3 if it did not start because too little memory is free, and with 4 if a module that the
file imports has not been compiled; the header of the script lists the other codes and
options. It is a convenience for development and does not replace step 7.

The checklist of the conventions (section 13):

[`docs/CONVENTIONS.md`, lines 430–436](../docs/CONVENTIONS.md#L430-L436):

```text
- [ ] Imports only lower layers; no `import Mathlib`.
- [ ] Definitions only in a `Defs.lean`, or `private`, or bridged with a reason.
- [ ] Statements use core definitions; notation as in §4; Frobenius scoped.
- [ ] Names follow §7; no paper numbers.
- [ ] Module header and docstrings as in §8; citations as in §9.
- [ ] Non-vacuity examples for new structures and main theorems.
- [ ] Renames: deprecated aliases, rename map entry, affected statement count in the batch notes.
```

**A new integrator.** The module docstring of [`Integrators/Method.lean`](../LeanDLRA/Integrators/Method.lean) gives the
procedure: write the integrator as a `StepMethod`, choose the admissible values (for the BUG
integrator, the matrices of rank at most `r`), prove the three properties of
`StepMethod.IsTubeLocal` and a local error bound for one step (`HasLocalError`); the theorem
`StepMethod.IsTubeLocal.exists_run_norm_sub_le` then gives a run and its error bound. The pairs
of files [`Integrators/Matrix/BUGStep.lean`](../LeanDLRA/Integrators/Matrix/BUGStep.lean) and
[`Integrators/Matrix/BUGRun.lean`](../LeanDLRA/Integrators/Matrix/BUGRun.lean),
[`Integrators/Matrix/KSLStep.lean`](../LeanDLRA/Integrators/Matrix/KSLStep.lean) and
[`Integrators/Matrix/KSLRun.lean`](../LeanDLRA/Integrators/Matrix/KSLRun.lean),
[`Integrators/Matrix/ParallelBUGStep.lean`](../LeanDLRA/Integrators/Matrix/ParallelBUGStep.lean) and
[`Integrators/Matrix/ParallelBUGRun.lean`](../LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean),
[`Integrators/Matrix/EulerBUGStep.lean`](../LeanDLRA/Integrators/Matrix/EulerBUGStep.lean) and
[`Integrators/Matrix/EulerBUGRun.lean`](../LeanDLRA/Integrators/Matrix/EulerBUGRun.lean) are four worked instances.
