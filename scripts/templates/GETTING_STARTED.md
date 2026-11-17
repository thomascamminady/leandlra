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
block links to the lines. The blocks were compared with the files at commit @commit.
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
    values of `S`.
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
| 3 | `EckartYoung.sq_norm_sub_truncation`, `EckartYoung.infDist_setOf_rank_le` | @file(LeanDLRA/Classical/EckartYoung.lean) |
| 5 | `tangentProj`, `isOrthProj_tangentProj`, `mem_range_tangentProj` | @file(LeanDLRA/FixedRank/Defs.lean), @file(LeanDLRA/Matrix/Projectors.lean) |
| 6, 8 | `ODESolution.dlra_norm_sub_le_gronwallBound` | @file(LeanDLRA/Dynamics/ContinuousDLRA.lean) |
| 7 | `FactoredNormalBoundOn`, `NormalBoundOn` | @file(LeanDLRA/Integrators/Matrix/Defs.lean), @file(LeanDLRA/DLRA/Defs.lean) |
| 9 | `hasDerivAt_factorProduct_iff_factorODE` | @file(LeanDLRA/Matrix/GaugeODE.lean) |
| 10 | `Curvature.koch_lubich_tangent_frob` | @file(LeanDLRA/Matrix/Curvature.lean) |
| 12 | `MatrixBUG.IsStep`, `MatrixKSL.IsStep` | @file(LeanDLRA/Integrators/Matrix/BUG.lean), @file(LeanDLRA/Integrators/Matrix/ProjectorSplitting.lean) |
| 13 | `MatrixBUG.exists_run_norm_sub_le`, `MatrixKSL.exists_run_norm_sub_le`, `MatrixParallelBUG.exists_run_norm_sub_le` | @file(LeanDLRA/Integrators/Matrix/BUGRun.lean), @file(LeanDLRA/Integrators/Matrix/KSLRun.lean), @file(LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean) |

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
@file(LeanDLRA/LinearAlgebra/Frobenius/Defs.lean), the lemmas in
@file(LeanDLRA/Matrix/Frobenius.lean)).

Nine definitions suffice to read the theorem of section 3, in this order:

| Definition | Where | In one line |
|---|---|---|
| `ODESolution` | @loc(LeanDLRA/Analysis/Defs.lean ODESolution) | `ODESolution F y a b`: `y` is continuous on `[a, b]` and has the right derivative `F t (y t)` at every `t` in `[a, b)`. |
| `tubeSet` | @loc(LeanDLRA/Analysis/Defs.lean tubeSet) | `tubeSet A a b ρ`: the pairs `(t, x)` with `t` in `[a, b]` and `‖x - A t‖ ≤ ρ`, the tube of radius `ρ` around `A`. |
| `DLRAProblem` | @loc(LeanDLRA/DLRA/Defs.lean DLRAProblem) | `DLRAProblem F A a b ρ L B`: `A` solves `Y' = F(t, Y)` on `[a, b]`, and on the tube of radius `ρ` around `A` the field is `L`-Lipschitz in the state and bounded by `B`. |
| `FactoredNormalBoundOn` | @loc(LeanDLRA/Integrators/Matrix/Defs.lean FactoredNormalBoundOn) | `FactoredNormalBoundOn F r D ε`: `‖(I - U Uᵀ) F(t, U S Vᵀ) (I - V Vᵀ)‖ ≤ ε` for all `U`, `V` with `r` orthonormal columns and all `S` with `(t, U S Vᵀ)` in the region `D`. |
| `StepRel` | @loc(LeanDLRA/Integrators/Defs.lean StepRel) | A one-step method for one field, as a relation: `M t₀ t₁ Y₀ Y₁` says that `Y₁` is a result of one step from `Y₀` at time `t₀` to time `t₁`. |
| `uniformGrid` | @loc(LeanDLRA/Integrators/Defs.lean uniformGrid) | `uniformGrid t₀ h`: the times `t₀ + n h`. |
| `IsRun` | @loc(LeanDLRA/Integrators/Defs.lean IsRun) | `IsRun M τ N Y`: the times `τ 0 ≤ … ≤ τ N` are nondecreasing, and each `Y (n + 1)` is a result of one step of `M` from `Y n`, from time `τ n` to `τ (n + 1)`. |
| `MatrixBUG.stepRel` | @loc(LeanDLRA/Integrators/Matrix/BUGStep.lean stepRel) | `MatrixBUG.stepRel F r`: the step of the BUG integrator of rank `r` for the field `F`, as a step relation on matrices. |
| `bugGlobalBound` | @loc(LeanDLRA/Foundations/Localization.lean bugGlobalBound) | `bugGlobalBound L B H T δ ε h`: the right-hand side `e^{L T} δ + T e^{L T} (c₁ ε + c₂ h)` of the error bound, with `c₁ = bugC₁ L H` and `c₂ = bugC₂ L B H`. |

A step is a relation and not a function because the result of a step is not unique: the new
bases of a step are determined only up to a choice, and a substep is described by the
differential equation it solves. An error bound holds for every result.

Eight more definitions are needed to read the proofs or to treat an integrator of your own:

| Definition | Where | In one line |
|---|---|---|
| `IsLipschitzField` | @loc(LeanDLRA/Analysis/Defs.lean IsLipschitzField) | `IsLipschitzField F L`: `‖F t x - F t y‖ ≤ L * ‖x - y‖` for all `t`, `x`, `y`. |
| `IsBoundedField` | @loc(LeanDLRA/Analysis/Defs.lean IsBoundedField) | `IsBoundedField F B`: `‖F t x‖ ≤ B` for all `t`, `x`. |
| `tubeExt` | @loc(LeanDLRA/Analysis/Defs.lean tubeExt) | `tubeExt F A a b ρ`: a field that agrees with `F` on the tube and is Lipschitz and bounded everywhere if `F` is so on the tube. |
| `IsOrthProj` | @loc(LeanDLRA/LinearAlgebra/Projection/Defs.lean IsOrthProj) | `IsOrthProj P`: the continuous linear map `P` is idempotent and symmetric. |
| `tangentProj` | @loc(LeanDLRA/FixedRank/Defs.lean tangentProj) | `tangentProj U V`: the map `Z ↦ U Uᵀ Z + Z V Vᵀ - U Uᵀ Z V Vᵀ` of line 5. |
| `HasLocalError` | @loc(LeanDLRA/Integrators/Defs.lean HasLocalError) | `HasLocalError F t₀ t₁ Y₀ Y₁ δ`: `‖Y₁ - Φ t₁‖ ≤ δ` for every solution `Φ` on `[t₀, t₁]` that starts at `Y₀`. |
| `StepMethod` | @loc(LeanDLRA/Integrators/Method.lean StepMethod) | A one-step method for all fields: a map from fields to step relations. |
| `StepMethod.IsTubeLocal` | @loc(LeanDLRA/Integrators/Method.lean StepMethod.IsTubeLocal) | Three properties of one step (a step exists, it keeps the admissible values, it does not see the field outside a tube) from which a run and its error bound are constructed. |

## 3. A worked example: an error bound for your own field

### 3.1 The theorem

The theorem to start with is the existence of a run of the BUG integrator together with its
error bound. The file @file(LeanDLRA/Integrators/Matrix/BUGRun.lean) declares, before the
theorem and with the keyword `variable`, the index types `m n` of the matrices, the rank `r`, the
field `F`, the exact solution `A`, the real numbers `t₀ h H T ρ L B ε δ` and the number of steps
`N`; they are not repeated in the statement.

@stmt LeanDLRA/Integrators/Matrix/BUGRun.lean exists_run_norm_sub_le MatrixBUG.exists_run_norm_sub_le

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

@stmt LeanDLRA/Foundations/Localization.lean bugGlobalBound bugGlobalBound

@stmt LeanDLRA/Integrators/Defs.lean bugC₁ bugC₁

@stmt LeanDLRA/Integrators/Defs.lean bugC₂ bugC₂

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

@exfull LeanDLRA/Integrators/Matrix/BUGRun.lean 4

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

The three facts about the field are lemmas of @file(LeanDLRA/Integrators/Matrix/Defs.lean). The examples of
the projector-splitting integrator and of the parallel BUG integrator use the same lemmas; for
a field of your own they are templates.

*The problem on a tube* (`hP`). The proof gives the five fields of `DLRAProblem` in order: the
solution, `0 ≤ L`, `0 ≤ B`, the Lipschitz condition on the tube and the bound on the tube.

@full LeanDLRA/Integrators/Matrix/Defs.lean dlraProblem_linear dlraProblem_linear

The linear field is not bounded on the whole space, so `IsBoundedField` fails for it. On the
tube of radius `ρ` around `C` it is bounded by `(‖M‖ + ‖N‖) ρ`, whatever the size of `G`,
because it vanishes at `C`. The Lipschitz estimate that the proof uses is

@stmt LeanDLRA/Integrators/Matrix/Defs.lean norm_linear_sub_le norm_linear_sub_le

and rests on `Frobenius.norm_mul_le`, the bound `‖A * B‖ ≤ ‖A‖ * ‖B‖` for the Frobenius norm.

*Continuity* (`hc`).

@full LeanDLRA/Integrators/Matrix/Defs.lean continuous_uncurry_linear continuous_uncurry_linear

`Frobenius.leftMulCLM M` and `Frobenius.rightMulCLM M` are the multiplications by a fixed matrix
from the left and from the right as continuous linear maps. A field built from such maps is
continuous by the lemmas of Mathlib.

*The normal component* (`hε`).

@stmt LeanDLRA/Integrators/Matrix/Defs.lean factoredNormalBoundOn_linear factoredNormalBoundOn_linear

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

@stmt LeanDLRA/Integrators/Matrix/BUGRun.lean exists_bugGlobalBound_lt exists_bugGlobalBound_lt

The next example of the file uses it for the linear field. Its statement has no hypothesis on
`δ` and `h`; the only condition left is `hG`, which says that the part of the error bound that
does not vanish with `δ` and `h` is smaller than the tube radius:

@ex LeanDLRA/Integrators/Matrix/BUGRun.lean 5

If you already have a run, for example from another construction, `MatrixBUG.IsRun.norm_sub_le`
gives the same bound for it under the same hypotheses on `F` and `A`.

### 3.4 Other integrators

The projector-splitting integrator, the parallel BUG integrator of fixed rank, the BUG
integrator with explicit Euler substeps and the BUG integrator with augmented bases and
truncation to a fixed rank have theorems of the same form:
`MatrixKSL.exists_run_norm_sub_le` in @file(LeanDLRA/Integrators/Matrix/KSLRun.lean),
`MatrixParallelBUG.exists_run_norm_sub_le` in
@file(LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean),
`MatrixEulerBUG.exists_run_norm_sub_le` in @file(LeanDLRA/Integrators/Matrix/EulerBUGRun.lean)
and `MatrixBUG.trunc_exists_run_norm_sub_le` in
@file(LeanDLRA/Integrators/Matrix/TruncBUGRun.lean). Their hypotheses `hP`, `hc`, `hε`, `hε₀` on
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
@file(LeanDLRA/Integrators/Method.lean); see
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
| solutions, Lipschitz and bounded fields, tubes | @file(LeanDLRA/Analysis/Defs.lean) |
| existence of a solution of a differential equation | @file(LeanDLRA/Foundations/Existence.lean); for fields that are Lipschitz and bounded on a region only @file(LeanDLRA/Foundations/AprioriExistence.lean) |
| the mean value inequality and Grönwall inequalities | @file(LeanDLRA/Foundations/ODE.lean), @file(LeanDLRA/Foundations/Gronwall.lean) |
| orthogonal projectors | @file(LeanDLRA/LinearAlgebra/Projection/Defs.lean), @file(LeanDLRA/Foundations/Projector.lean) |
| the Frobenius norm and inner product of matrices | @file(LeanDLRA/LinearAlgebra/Frobenius/Defs.lean), @file(LeanDLRA/Matrix/Frobenius.lean) |
| the singular value decomposition and the Eckart–Young–Mirsky theorem | @file(LeanDLRA/Classical/SVD.lean), @file(LeanDLRA/LinearAlgebra/SVD/Defs.lean), @file(LeanDLRA/Classical/EckartYoung.lean) |
| lower bounds for singular values, the derivative of the truncated singular value decomposition, perturbation of singular subspaces | @file(LeanDLRA/LinearAlgebra/SVD/MinMax.lean), @file(LeanDLRA/LinearAlgebra/SVD/TruncationDeriv.lean), @file(LeanDLRA/LinearAlgebra/SVD/SinTheta.lean) |
| the matrices of rank at most `r` and the distance to them | @file(LeanDLRA/LinearAlgebra/LowRank/Defs.lean), @file(LeanDLRA/Matrix/LowRankDistance.lean), @file(LeanDLRA/Matrix/LowRankDistanceFlow.lean) (along the exact flow) |
| the matrices of rank exactly `r`; the rank of a function of two variables | @file(LeanDLRA/LinearAlgebra/LowRank/SepRank.lean) |
| the tangent projector `P(Y)` and its dependence on `Y` | @file(LeanDLRA/FixedRank/Defs.lean), @file(LeanDLRA/Matrix/Projectors.lean), @file(LeanDLRA/Matrix/Curvature.lean) |
| the tangent projector and the tangent space at a matrix `Y`, without a factorization | @file(LeanDLRA/FixedRank/TangentSpace/Defs.lean), @file(LeanDLRA/FixedRank/TangentSpace.lean); its dependence on `Y`, tangent velocities and first-order optimality in @file(LeanDLRA/FixedRank/TangentSpace/Curvature.lean); the distance to rank `r` after a tangent step in @file(LeanDLRA/FixedRank/TangentStepTruncation.lean) |
| the problem on a tube and bounds for the normal component | @file(LeanDLRA/DLRA/Defs.lean), @file(LeanDLRA/Integrators/Matrix/Defs.lean), @file(LeanDLRA/Integrators/Matrix/FactoredNormalBound.lean) |
| the projected equation `Y' = P(Y) F(t, Y)` and the equations for the factors | @file(LeanDLRA/Dynamics/ContinuousDLRA.lean), @file(LeanDLRA/Matrix/GaugeODE.lean); DLRA solutions and the dynamically orthogonal, dual and bi-orthogonal systems in @file(LeanDLRA/DLRA/DynamicallyOrthogonal.lean) (the definition `IsDLRASolution` is in @file(LeanDLRA/DLRA/Defs.lean)); the distance from the best approximation of rank `r` for matrices in @file(LeanDLRA/DLRA/QuasiOptimality.lean), for a field that is Lipschitz on a tube only in @file(LeanDLRA/DLRA/QuasiOptimalityTube.lean), for the truncated singular value decomposition under a gap in @file(LeanDLRA/DLRA/QuasiOptimalityGap.lean), with a margin up to `θ ρ`, `θ < 1/2`, in @file(LeanDLRA/DLRA/QuasiOptimalityMargin.lean); existence and uniqueness of the DLRA solution in @file(LeanDLRA/DLRA/Existence.lean); the gauge of the factors in @file(LeanDLRA/DLRA/GaugeInvariance.lean) |
| grids, steps, runs, local errors | @file(LeanDLRA/Integrators/Defs.lean) |
| the global error from local errors | @file(LeanDLRA/Integrators/GlobalError.lean), @file(LeanDLRA/Integrators/Tube.lean) |
| the theorem to instantiate for a new integrator | @file(LeanDLRA/Integrators/Method.lean); for a grid with variable step sizes @file(LeanDLRA/Integrators/MethodGrid.lean), for steps that end with a truncation to a tolerance @file(LeanDLRA/Integrators/MethodTolerance.lean), with a one-sided Lipschitz constant in place of `L` in the propagation of errors @file(LeanDLRA/Integrators/MethodOneSided.lean) |
| the BUG integrator | @file(LeanDLRA/Integrators/Matrix/BUGRun.lean) (start here), @file(LeanDLRA/Integrators/Matrix/BUGStep.lean), @file(LeanDLRA/Integrators/Matrix/BUG.lean); on a general state space @file(LeanDLRA/Integrators/BUGCore.lean), @file(LeanDLRA/Integrators/BUG.lean); smaller constants in the local error in @file(LeanDLRA/Integrators/BUGCapture.lean), runs with a one-sided Lipschitz constant in @file(LeanDLRA/Integrators/Matrix/BUGRunOneSided.lean) (the general form for tube-local methods is @file(LeanDLRA/Integrators/MethodOneSided.lean)) |
| the projector-splitting integrator | @file(LeanDLRA/Integrators/Matrix/KSLRun.lean), @file(LeanDLRA/Integrators/Matrix/KSLStep.lean), @file(LeanDLRA/Integrators/Matrix/ProjectorSplitting.lean); on a general state space @file(LeanDLRA/Integrators/ProjectorSplitting.lean) |
| the parallel BUG integrator | @file(LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean), @file(LeanDLRA/Integrators/Matrix/ParallelBUGStep.lean), @file(LeanDLRA/Integrators/Matrix/ParallelBUG.lean); with truncation by a tolerance @file(LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean); on a general state space @file(LeanDLRA/Integrators/ParallelBUG.lean) |
| the rank-adaptive BUG integrator | @file(LeanDLRA/Integrators/RankAdaptiveBUG.lean), @file(LeanDLRA/Integrators/Matrix/BUG.lean); as step relations with a truncation by a tolerance or to a fixed rank @file(LeanDLRA/Integrators/Matrix/AdaptiveBUGStep.lean), runs with truncation by a tolerance @file(LeanDLRA/Integrators/Matrix/AdaptiveBUGRun.lean), runs with truncation to a fixed rank @file(LeanDLRA/Integrators/Matrix/TruncBUGRun.lean); a lower bound and two upper bounds for one step in @file(LeanDLRA/Research/AugmentationRank.lean), a bound for a field with a two-sided term in @file(LeanDLRA/Research/TwoSidedLeak.lean); fields of Sylvester type in @file(LeanDLRA/Research/SylvesterFlows.lean) (the auxiliary flows exist), @file(LeanDLRA/Research/SylvesterGlobal.lean) (global order two), @file(LeanDLRA/Research/PerturbedSylvester.lean) (a Lipschitz perturbation), @file(LeanDLRA/Research/TwoSidedPadded.lean) (a start padded with the images of a two-sided term) and @file(LeanDLRA/Research/RankOneGalerkinBarrier.lean) (a Galerkin step in a fixed rank-one space is not of second order); a-posteriori bounds and tolerance schedules in @file(LeanDLRA/Integrators/RankAdaptiveBUGAposteriori.lean), the rank decision in @file(LeanDLRA/Integrators/RankSelection.lean) |
| the BUG integrator with explicit Euler substeps | @file(LeanDLRA/Integrators/Matrix/EulerBUGRun.lean) (start here), @file(LeanDLRA/Integrators/Matrix/EulerBUGStep.lean); on a general state space @file(LeanDLRA/Integrators/EulerBUG.lean) |
| stiff problems: one-sided Lipschitz fields, implicit steps, the primal–dual error representation | @file(LeanDLRA/Foundations/OneSided.lean), @file(LeanDLRA/Stiff/ImplicitBUG.lean); the implicit BUG step on matrices in @file(LeanDLRA/Stiff/Defs.lean), its local error and existence in @file(LeanDLRA/Stiff/ImplicitBUGStep.lean), its runs (a bound that is not stiffness-uniform) in @file(LeanDLRA/Stiff/ImplicitBUGRun.lean), @file(LeanDLRA/Stiff/ImplicitSolvability.lean), @file(LeanDLRA/Stiff/DualWeightedResidual.lean) |
| stiff problems: one step for a field with a stiff linear part | @file(LeanDLRA/Stiff/CouplingLocalError.lean) (a local error bound with coupling numbers), @file(LeanDLRA/Research/StiffOrderReduction.lean) (a family of problems without a uniform constant for one step), @file(LeanDLRA/Research/StiffGlobalCycle.lean) (a family of problems without a uniform constant for the global error) |
| stiff problems: the error against the variation of the forcing | @file(LeanDLRA/Research/StiffGlobalVariation.lean) (a lower bound), @file(LeanDLRA/Research/StiffEnergyGalerkin.lean) (an energy bound without coupling numbers), @file(LeanDLRA/Research/StiffOldColumnGalerkin.lean) and @file(LeanDLRA/Research/StiffOldColumnVariation.lean) (invariant old column spaces), @file(LeanDLRA/Research/StiffVelocityVariation.lean) (the sum of the velocity changes is not bounded by the data), @file(LeanDLRA/Research/StiffInvariantGalerkin.lean) (a Galerkin space that is invariant under the stiff operator); whether a bound `C (h (1 + Var g) + ε + n ϑ)` holds uniformly in the stiffness is open, [Main results, section 7.6](MAIN_RESULTS.md#76-stiff-problems-with-forcing-six-results-and-what-stays-open) |
| steps of higher order | @file(LeanDLRA/HighOrder/MidpointBUG.lean), @file(LeanDLRA/HighOrder/MidpointBUGGlobal.lean) (the global error bound of second order), @file(LeanDLRA/HighOrder/RungeKuttaBUG.lean); the midpoint BUG step for matrices in @file(LeanDLRA/HighOrder/Defs.lean) and @file(LeanDLRA/HighOrder/MidpointBUGStep.lean) (local error), its runs and error bound in @file(LeanDLRA/HighOrder/MidpointBUGRun.lean); local errors of an explicit midpoint update in augmented bases in @file(LeanDLRA/Research/ExplicitMidpointGalerkin.lean), the size of its capture defects (of order `h² + ε`) in @file(LeanDLRA/Research/ExplicitMidpointCapture.lean), its step relation in @file(LeanDLRA/HighOrder/Defs.lean) and its runs (error of order `h² + ε`) in @file(LeanDLRA/Research/ExplicitMidpointRun.lean) |
| projected Euler and projected Runge–Kutta methods | @file(LeanDLRA/Integrators/Matrix/ProjectedEuler.lean), @file(LeanDLRA/Integrators/Matrix/ProjectedRK.lean) (runs and global error), @file(LeanDLRA/HighOrder/ProjectedRK.lean) (stage analysis), @file(LeanDLRA/Integrators/Matrix/FlowDistance.lean) (distance of the exact solution to the matrices of rank at most `r`) |
| steps with interpolation or random sketches | @file(LeanDLRA/Randomized/ObliqueBUG.lean), @file(LeanDLRA/Randomized/RandomizedBUG.lean); the dynamical randomized SVD as a step relation @file(LeanDLRA/Randomized/DRSVDStep.lean) and its runs @file(LeanDLRA/Randomized/DRSVDRun.lean); cross interpolation of the tangent projector in @file(LeanDLRA/Randomized/CrossInterpolation.lean) |
| conservation and energy stability | @file(LeanDLRA/Stability/Conservation.lean), @file(LeanDLRA/Stability/Energy.lean), @file(LeanDLRA/Stability/NormBalance.lean) (norm balance of one step) |
| tensors: Tucker format, tensor trains, tree tensor networks | @file(LeanDLRA/Tensor/Defs.lean), @file(LeanDLRA/Tensor/Tucker/), @file(LeanDLRA/Tensor/TT/), @file(LeanDLRA/Tensor/TTN/), @file(LeanDLRA/Integrators/TuckerBUG.lean), @file(LeanDLRA/Integrators/TuckerBUGCore.lean); the Tucker BUG step as a step relation and its runs @file(LeanDLRA/Tensor/Tucker/BUGStep.lean), @file(LeanDLRA/Tensor/Tucker/BUGRun.lean); exactness and robust error of the tensor-train projector-splitting integrator in @file(LeanDLRA/Tensor/TT/ProjectorSplittingExactness.lean) and @file(LeanDLRA/Tensor/TT/ProjectorSplittingError.lean); orthonormality of tree tensor network bases in @file(LeanDLRA/Tensor/TTN/BasisOrthonormality.lean); the step predicates of the tensor integrators on a general state space in @file(LeanDLRA/Tensor/Steps.lean), the theorems about them in @file(LeanDLRA/Tensor/TTN/Abstract/) |
| kinetic equations | @file(LeanDLRA/Kinetic/Defs.lean) (definitions), @file(LeanDLRA/Kinetic/LowRank.lean) (the rank of the low-rank ansatz) and @file(LeanDLRA/Kinetic/Stencils.lean) (products and transposes of the periodic difference matrices); the collision field of a material mixture is in @file(LeanDLRA/Kinetic/MaterialMixtureCollision.lean). The core has no error theorem for kinetic equations; results of single papers are in the catalogue folder @file(LeanDLRA/Literature/Kinetic/). |
| low-rank training | @file(LeanDLRA/Training/Defs.lean), @file(LeanDLRA/Training/Descent.lean), @file(LeanDLRA/Training/GradientFlowConvergence.lean), @file(LeanDLRA/Training/ConvergenceRates.lean), @file(LeanDLRA/Training/FederatedDescent.lean); thresholds for federated rounds in @file(LeanDLRA/Research/FederatedDescentThreshold.lean), @file(LeanDLRA/Research/FederatedConvexThreshold.lean), @file(LeanDLRA/Research/FederatedTwoSteps.lean) and @file(LeanDLRA/Research/FederatedThreeSteps.lean) (and, for every number of local steps, descent when `sstar lr β < 4`, @file(LeanDLRA/Research/FederatedManySteps.lean)); fixed points of federated rounds in @file(LeanDLRA/Training/FederatedFixedPoints.lean); the explicit Euler splitting step in @file(LeanDLRA/Training/ProjectorSplittingDescent.lean) |
| filtering | @file(LeanDLRA/Filtering/Defs.lean), @file(LeanDLRA/Stochastic/KalmanBucy.lean), @file(LeanDLRA/Stochastic/GramianLowerBound.lean) |
| optimal control | @file(LeanDLRA/Control/AdjointDLRA.lean) |
| the results of one paper | [PROVEN.md](PROVEN.md), which lists modules with the papers they cite; the paper files are in @file(LeanDLRA/Literature/) |

Every module starts with a docstring that says what the file contains; read it before the
declarations.

## 5. Core and catalogue

The Lean sources below `LeanDLRA/` form two libraries ([STRUCTURE.md](STRUCTURE.md)).

* The **core** is the set of modules imported by `LeanDLRA.lean`, @coremodules modules at the commit
  named above. Its theorems are stated in shared definitions, so they can be combined: the
  solution of one theorem is the solution of the next, a run is a run. This page,
  [Main results](MAIN_RESULTS.md) and [Definitions](DEFINITIONS.md) describe the core only.
* The **catalogue** is everything else: files in the folders `LeanDLRA/Literature`,
  `LeanDLRA/OpenProblems`, `LeanDLRA/Novel` and `LeanDLRA/Corrections`. A paper file states
  results of one paper, as a rule in definitions of its own or of the paper. Its theorems are
  proven and checked like those of the core, but a catalogue theorem does not automatically
  apply to the objects of the core. `LeanDLRACatalogue.lean` imports the core and the catalogue.

The two imports, as [STRUCTURE.md](STRUCTURE.md) gives them:

@quote docs/STRUCTURE.md ^import LeanDLRA\s || ^import LeanDLRACatalogue\s

A single module can be imported in the same way; the theorem of section 3 is in the module that
the root file of the core imports with the line

@quote LeanDLRA.lean ^import LeanDLRA\.Integrators\.Matrix\.BUGRun$

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
   @file(LeanDLRA/DLRA/Defs.lean) and @file(LeanDLRA/Integrators/Defs.lean) are the reference.
3. **State and name.** Notation and hypotheses as in sections 4 to 6, names as in section 7.
4. **Document.** A module docstring with the layout of section 8, a docstring for every public
   declaration, and papers cited as in section 9.
5. **Show that the hypotheses can be met.** A new structure or main theorem gets an `example`
   that satisfies all its hypotheses, like the example of section 3.2.
6. **Check the file.** The script @file(scripts/fc) checks one file against the compiled
   library without building anything (usage below). `scripts/warm.sh --list` names the modules
   whose compiled state is missing or out of date.
7. **Verify.** `make verify` regenerates the root files, checks that the core imports core
   modules only, builds the core, searches the sources for placeholders and checks that every
   constant of the core depends on the three standard axioms only. `make ci` adds the checks
   and tests of the Python scripts. The core workflow of CI
   (`.github/workflows/lean_action_ci.yml`) builds the core with warnings as errors, runs the
   same audit and the same Python checks, and replays the changed core modules in an
   independent kernel check. Contributions come as pull requests; the maintainers merge
   through the gate (@file(scripts/gate.py)), which builds the changed files with warnings as
   errors, builds the core and audits both.

The usage of the single-file check, from the header of the script:

@quote scripts/fc ^#   scripts/fc FILE\.lean || ^#\s+0 switches the test off

The script ends with code 0 if there is neither an error nor a warning, with 1 if there is one,
with 3 if it did not start because too little memory is free, and with 4 if a module that the
file imports has not been compiled; the header of the script lists the other codes and
options. It is a convenience for development and does not replace step 7.

The checklist of the conventions (section 13):

@quote docs/CONVENTIONS.md ^- \[ \] Imports only || ^- \[ \] Renames

**A new integrator.** The module docstring of @file(LeanDLRA/Integrators/Method.lean) gives the
procedure: write the integrator as a `StepMethod`, choose the admissible values (for the BUG
integrator, the matrices of rank at most `r`), prove the three properties of
`StepMethod.IsTubeLocal` and a local error bound for one step (`HasLocalError`); the theorem
`StepMethod.IsTubeLocal.exists_run_norm_sub_le` then gives a run and its error bound. The pairs
of files @file(LeanDLRA/Integrators/Matrix/BUGStep.lean) and
@file(LeanDLRA/Integrators/Matrix/BUGRun.lean),
@file(LeanDLRA/Integrators/Matrix/KSLStep.lean) and
@file(LeanDLRA/Integrators/Matrix/KSLRun.lean),
@file(LeanDLRA/Integrators/Matrix/ParallelBUGStep.lean) and
@file(LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean),
@file(LeanDLRA/Integrators/Matrix/EulerBUGStep.lean) and
@file(LeanDLRA/Integrators/Matrix/EulerBUGRun.lean) are four worked instances.
