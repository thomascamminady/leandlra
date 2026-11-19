# Guide: how do I ...?

This page is organized by task. Each section starts with what you want, says which file and which
theorem to use, and ends with the place where a worked case can be read. It assumes that you have
read the first two sections of [Getting started](GETTING_STARTED.md); the pages that say what the
core proves are [Main results](MAIN_RESULTS.md) and [Definitions](DEFINITIONS.md).

Every block of code on this page is copied from a file of the repository; the line above the
block links to the lines. The blocks were compared with the files at commit d01afcc (2026-11-19).

## Contents

1. [I want an error bound for the BUG integrator](#1-i-want-an-error-bound-for-the-bug-integrator)
2. [I want the same for another integrator](#2-i-want-the-same-for-another-integrator)
3. [I want to state my own problem in core definitions](#3-i-want-to-state-my-own-problem-in-core-definitions)
4. [I want to add a new integrator as a `StepMethod`](#4-i-want-to-add-a-new-integrator-as-a-stepmethod)
5. [How do I find the definition of X?](#5-how-do-i-find-the-definition-of-x)
6. [How do I find the theorem that says Y?](#6-how-do-i-find-the-theorem-that-says-y)
7. [I want to check my own Lean file](#7-i-want-to-check-my-own-lean-file)
8. [I found a result in the catalogue and want to use it](#8-i-found-a-result-in-the-catalogue-and-want-to-use-it)

## 1. I want an error bound for the BUG integrator

**Use** `MatrixBUG.exists_run_norm_sub_le` in [`Integrators/Matrix/BUGRun.lean`](../LeanDLRA/Integrators/Matrix/BUGRun.lean). It
says that the fixed-rank BUG integrator can be run and that the run stays near the exact
solution; it is the theorem to start with.

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

**What you provide**, in this order: the exact solution and the constants `L` and `B` on a tube
(`hP`), continuity (`hc`), a bound `ε` for the normal component (`hε`, `hε₀`), the step size and
the horizon (`hh`, `hhH`, `hNT`), the rank conditions, the start value (`hY₀`, `hδ`), and the
smallness condition `hsmall`. [Getting started, section 3.1](GETTING_STARTED.md#31-the-theorem)
explains each hypothesis.

**What you get**: a run `Y 0 = Y₀, …, Y N` of rank at most `r` with
`‖Y n - A (t₀ + n h)‖ ≤ bugGlobalBound L B H T δ ε h`; the right-hand side contains no singular
value.

**Worked case.** [`Examples/BUGEndToEnd.lean`](../Examples/BUGEndToEnd.lean) is a file to read from top to bottom. It writes
down a `2 × 2` linear equation with numbers, shows that `A(t) = C` is its solution, computes `L`,
`B` and `ε`, applies the theorem and ends with the statement

[`Examples/BUGEndToEnd.lean`, lines 135–139](../Examples/BUGEndToEnd.lean#L135-L139):

```lean
theorem exists_run_error_le {Y₀ : Matrix (Fin 2) (Fin 2) ℝ} (hY₀ : Y₀.rank ≤ 1)
    (hδ : ‖Y₀ - C‖ ≤ 1 / 100) :
    ∃ Y : ℕ → Matrix (Fin 2) (Fin 2) ℝ, Y 0 = Y₀ ∧
      IsRun (stepRel field 1) (uniformGrid 0 (1 / 1000)) 100 Y ∧
      ∀ j ≤ 100, (Y j).rank ≤ 1 ∧ ‖Y j - C‖ ≤ 3 / 10 := by
```

The file is not part of the library `LeanDLRA`; it is the library `Examples` of the repository
(`lake build Examples`), so that it can be read and changed without touching the core.

**If you already have a run** from another construction, `MatrixBUG.IsRun.norm_sub_le` gives the
same bound for it under the same hypotheses on `F` and `A`. **If you only need to know that the
hypotheses can be met**, `exists_bugGlobalBound_lt` produces a start tolerance `δ` and a step size
`h` for which `hsmall` holds as soon as the part of the bound that does not vanish with `δ` and `h`
is smaller than the tube radius.

**If you want the error against the best approximation of rank `r`** for given data `A(t)` (field
`F(t, Y) = Ȧ(t)`), and not against the exact solution, use
`norm_bugRun_sub_truncation_le_mul_of_forall_le` in
[`Integrators/Matrix/BUGQuasiOptimalityTruncation.lean`](../LeanDLRA/Integrators/Matrix/BUGQuasiOptimalityTruncation.lean): the bound is
`e^{9/2 lam t_n} (‖Y_0 - T_r(A(0))‖ + 12/5 lam t_n τ)` with `lam = μ / (ρ - τ)`, under a gap
`σ_r(A) ≤ τ < ρ ≤ σ_{r-1}(A)` and `h lam ≤ 1/16`. The variants with the normal velocity as growth
rate, with the tail seen from the old reference and for runs with changing rank are in [section
5.4](MAIN_RESULTS.md#54-quasi-optimality-of-the-bug-integrator-for-given-data).

## 2. I want the same for another integrator

The theorems of the other fixed-rank integrators have the same hypotheses `hP`, `hc`, `hε`,
`hε₀`; the three lemmas that give them for a linear field serve all of them. Differences:

| Integrator | Theorem | File | Extra hypotheses |
|---|---|---|---|
| projector splitting | `MatrixKSL.exists_run_norm_sub_le` | [`Integrators/Matrix/KSLRun.lean`](../LeanDLRA/Integrators/Matrix/KSLRun.lean) | none; no `hhH` |
| parallel BUG, fixed rank | `MatrixParallelBUG.exists_run_norm_sub_le` | [`Integrators/Matrix/ParallelBUGRun.lean`](../LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean) | none; no `hhH` |
| BUG with explicit Euler substeps | `MatrixEulerBUG.exists_run_norm_sub_le` | [`Integrators/Matrix/EulerBUGRun.lean`](../LeanDLRA/Integrators/Matrix/EulerBUGRun.lean) | the field is Lipschitz in time with constant `Lt` |
| BUG with augmented bases, truncated to rank `r` | `MatrixBUG.trunc_exists_run_norm_sub_le` | [`Integrators/Matrix/TruncBUGRun.lean`](../LeanDLRA/Integrators/Matrix/TruncBUGRun.lean) | `hκ : 1 ≤ κ`, the quality of the truncation |
| rank-adaptive BUG, truncated by a tolerance | `MatrixBUG.adaptive_exists_run_norm_sub_le` | [`Integrators/Matrix/AdaptiveBUGRun.lean`](../LeanDLRA/Integrators/Matrix/AdaptiveBUGRun.lean) | the tolerance `ϑ`, the normal bound for every `r ≥ r₀`, `r₀` below the matrix sizes; the bound has the term `e^{L T} n ϑ` |
| parallel BUG, truncated by a tolerance | `MatrixParallelBUG.adaptive_exists_run_norm_sub_le` | [`Integrators/Matrix/ParallelBUGTolRun.lean`](../LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean) | as the previous row; no `hhH` |
| dynamical randomized SVD | `MatrixDRSVD.exists_run_norm_sub_le` | [`Randomized/DRSVDRun.lean`](../LeanDLRA/Randomized/DRSVDRun.lean) | sketch and range bases with `k` and `l` columns, `r ≤ k ≤ l`; the normal bound at `r` and at `k` columns |
| projected Euler method | `MatrixProjEuler.exists_run_norm_sub_le` | [`Integrators/Matrix/ProjectedEuler.lean`](../LeanDLRA/Integrators/Matrix/ProjectedEuler.lean) | the field is Lipschitz in time with `Lt`; `hκ : 1 ≤ κ`, the quality of the retraction |
| projected Runge–Kutta methods | `MatrixPRK.exists_run_norm_sub_le` | [`Integrators/Matrix/ProjectedRK.lean`](../LeanDLRA/Integrators/Matrix/ProjectedRK.lean) | a Butcher tableau, `hκ`, and as a hypothesis (`hRK`) the order of the classical scheme |
| midpoint BUG, fixed rank (the 4r variant) | `MatrixMidpointBUG.exists_run_norm_sub_le` | [`HighOrder/MidpointBUGRun.lean`](../LeanDLRA/HighOrder/MidpointBUGRun.lean) | the field is of class `C²` with bounds `M₁`, `M₂` on its derivatives; normal bounds `ε` at rank `r` and `ε₂` at rank `2 r`, with `2 r` at most the matrix sizes; the error is of order `h²` up to the terms in `ε`, `ε₂` |
| explicit midpoint method in bases with `2 r` columns, truncated to rank `r` | `ExplicitMidpoint.exists_run_norm_sub_le` | [`Research/ExplicitMidpointRun.lean`](../LeanDLRA/Research/ExplicitMidpointRun.lean) | as for the midpoint BUG integrator: the field is of class `C²` with bounds `M₁`, `M₂`; normal bound `ε` at rank `r` only; `2 r` at most the matrix sizes |
| BUG for Tucker tensors | `TuckerBUG.exists_run_norm_sub_le` | [`Tensor/Tucker/BUGRun.lean`](../LeanDLRA/Tensor/Tucker/BUGRun.lean) | the field is on `Tensor ι`; the normal bound is at the triples `TuckerBUG.normalTriples r`; margin `(d + 2) B h` |

The table with the error bounds and the margins is in [Getting started, section
3.4](GETTING_STARTED.md#34-other-integrators). A rank that changes from step to step, with a
truncation to a tolerance, is treated by the rows for the rank-adaptive and the parallel
integrator; their step relations are in [`Integrators/Matrix/AdaptiveBUGStep.lean`](../LeanDLRA/Integrators/Matrix/AdaptiveBUGStep.lean)
and the run theorem with a tolerance for every step is in
[`Integrators/MethodTolerance.lean`](../LeanDLRA/Integrators/MethodTolerance.lean). For the rows with a tolerance, a Tucker tensor,
a retraction or the midpoint rule, the hypotheses on `F` and `A` are the same `hP`, `hc`, `hε`;
the page [Main results, section 4.3](MAIN_RESULTS.md#43-one-run-theorem-many-methods) lists the
margin constants.

**If your method is not in the table**, show that it is tube-local (section 4) and apply the same
theorem; the integrators of the table are the examples, and the shortest ones to read are
[`Integrators/Matrix/ProjectedEuler.lean`](../LeanDLRA/Integrators/Matrix/ProjectedEuler.lean) and
[`Randomized/DRSVDRun.lean`](../LeanDLRA/Randomized/DRSVDRun.lean).

**Worked case.** [`Examples/RankAdaptive.lean`](../Examples/RankAdaptive.lean) runs the BUG integrator with augmented bases
and truncation to rank one on the problem of the first example, and compares the two bounds:

[`Examples/RankAdaptive.lean`, lines 59–63](../Examples/RankAdaptive.lean#L59-L63):

```lean
theorem exists_run_error_le_trunc {Y₀ : Matrix (Fin 2) (Fin 2) ℝ} (hY₀ : Y₀.rank ≤ 1)
    (hδ : ‖Y₀ - C‖ ≤ 1 / 100) :
    ∃ Y : ℕ → Matrix (Fin 2) (Fin 2) ℝ, Y 0 = Y₀ ∧
      IsRun (truncStepRel field 1 1) (uniformGrid 0 (1 / 1000)) 100 Y ∧
      ∀ j ≤ 100, (Y j).rank ≤ 1 ∧ ‖Y j - C‖ ≤ 7 / 10 := by
```

## 3. I want to state my own problem in core definitions

A result is stated in core definitions when it is about the objects of the core, so that it can
be combined with the other theorems. For a differential equation `Y' = F(t, Y)` for matrices:

1. **The field** is a function `F : ℝ → Matrix m n ℝ → Matrix m n ℝ`; time comes first.
2. **The solution and the constants** are bundled in `DLRAProblem F A a b ρ L B`:

`LeanDLRA.DLRAProblem` in [`LeanDLRA/DLRA/Defs.lean`, lines 69–79](../LeanDLRA/DLRA/Defs.lean#L69-L79):

```lean
structure DLRAProblem (F : ℝ → E → E) (A : ℝ → E) (a b ρ L B : ℝ) : Prop where
  /-- `A` solves `y' = F(t, y)` on `[a, b]`. -/
  sol : ODESolution F A a b
  /-- The Lipschitz constant is nonnegative. -/
  L_nonneg : 0 ≤ L
  /-- The bound is nonnegative. -/
  B_nonneg : 0 ≤ B
  /-- `F` is `L`-Lipschitz in the state on the tube of radius `ρ` around `A`. -/
  lipschitz : IsLipschitzOnTube F A a b ρ L
  /-- `F` is bounded by `B` on the tube of radius `ρ` around `A`. -/
  bounded : IsBoundedOnTube F A a b ρ B
```

   `DLRAProblem.of_global` gives the bundle for a field that is Lipschitz and bounded on the
   whole space; `dlraProblem_linear` ([`Integrators/Matrix/Defs.lean`](../LeanDLRA/Integrators/Matrix/Defs.lean)) is a case that
   is Lipschitz but not bounded, and it is the template to copy.
3. **The normal component** is bounded by `FactoredNormalBoundOn F r D ε`;
   `factoredNormalBoundOn_linear` is the template.
4. **A run** is `IsRun (MatrixBUG.stepRel F r) (uniformGrid t₀ h) N Y`.
5. **A norm.** Matrices carry the Frobenius norm only inside the scope that a file opens with
   `open scoped LeanDLRA.Frobenius`; without it `‖Y‖` is not the norm that the theorems use.

A file that states a theorem in these terms starts like this (see
[`Examples/BUGEndToEnd.lean`](../Examples/BUGEndToEnd.lean)):

[`Examples/BUGEndToEnd.lean`, lines 1–2](../Examples/BUGEndToEnd.lean#L1-L2):

```lean
import LeanDLRA.Integrators.Matrix.BUGRun
import LeanDLRA.Integrators.Matrix.Defs
```

[`Examples/BUGEndToEnd.lean`, line 37](../Examples/BUGEndToEnd.lean#L37):

```lean
open scoped Matrix LeanDLRA.Frobenius
```

Write the numbers of your problem as a `def`, prove the three facts of 2 to 3 for it, and
instantiate the theorem of section 1. If your field is not linear, the lemmas of
[`Integrators/Matrix/Defs.lean`](../LeanDLRA/Integrators/Matrix/Defs.lean) show what each of them has to prove.

## 4. I want to add a new integrator as a `StepMethod`

A method is a map from fields to step relations:

`LeanDLRA.StepMethod` in [`LeanDLRA/Integrators/Method.lean`, line 350](../LeanDLRA/Integrators/Method.lean#L350):

```lean
abbrev StepMethod (E : Type*) : Type _ := (ℝ → E → E) → StepRel E
```

`M F t₀ t₁ Y₀ Y₁` says that `Y₁` is a result of one step for the field `F` from `Y₀` at time `t₀` to
time `t₁`. It is a relation because the result of a step is not unique (bases are determined only
up to a choice). To get a run and an error bound you prove three properties of **one step** and
one error estimate; the first three are bundled:

`LeanDLRA.StepMethod.IsTubeLocal` in [`LeanDLRA/Integrators/Method.lean`, lines 357–371](../LeanDLRA/Integrators/Method.lean#L357-L371):

```lean
structure StepMethod.IsTubeLocal (M : StepMethod E) (Adm : E → Prop) (κ : ℝ) : Prop where
  /-- (E) A step exists from every value with `Adm`, for every globally Lipschitz field that is
  continuous in time on the step interval. No bound on the field is assumed. -/
  exists_step : ∀ {G : ℝ → E → E} {L t₀ t₁ : ℝ} {Y₀ : E}, IsLipschitzField G L →
    (∀ x, ContinuousOn (fun t => G t x) (Icc t₀ t₁)) → t₀ ≤ t₁ → Adm Y₀ → ∃ Y₁, M G t₀ t₁ Y₀ Y₁
  /-- (I) A forward step from a value with `Adm` ends at a value with `Adm`. -/
  adm_of_step : ∀ {G : ℝ → E → E} {t₀ t₁ : ℝ} {Y₀ Y₁ : E}, t₀ ≤ t₁ → Adm Y₀ →
    M G t₀ t₁ Y₀ Y₁ → Adm Y₁
  /-- (T) If `F` is bounded by `B` on the tube of radius `ρ` around a solution `A` and the start
  value has the margin `‖Y₀ - A t₀‖ + κ B (t₁ - t₀) < ρ`, then a step of the extended field
  `tubeExt F A a b ρ` from `Y₀` is a step of `F`. -/
  step_of_tubeExt : ∀ {F : ℝ → E → E} {A : ℝ → E} {a b ρ B t₀ t₁ : ℝ} {Y₀ Y₁ : E},
    IsBoundedOnTube F A a b ρ B → 0 ≤ B → a ≤ t₀ → t₁ ≤ b → t₀ ≤ t₁ → ODESolution F A t₀ t₁ →
    Adm Y₀ → ‖Y₀ - A t₀‖ + κ * B * (t₁ - t₀) < ρ → M (tubeExt F A a b ρ) t₀ t₁ Y₀ Y₁ →
    M F t₀ t₁ Y₀ Y₁
```

The route, as [`Integrators/Method.lean`](../LeanDLRA/Integrators/Method.lean) describes it in its header:

1. **Define the step relation** for a general field, in the folder of the integrator, as a
   `StepRel` ([`Integrators/Defs.lean`](../LeanDLRA/Integrators/Defs.lean) has the vocabulary: `StepRel`, `IsRun`,
   `HasLocalError`). Choose the predicate `Adm` of values from which a step can start; for the
   low-rank integrators it is `rank ≤ r`.
2. **Prove (E), (I), (T)** as one `StepMethod.IsTubeLocal M Adm κ`. (E): a step exists for every
   globally Lipschitz field. (I): a step keeps `Adm`. (T): near the exact solution a step of the
   extended field `tubeExt F A a b ρ` is a step of `F`; this is an a priori estimate that all
   points at which the step evaluates the field lie in the tube. `κ ≥ 2` counts how far the
   substeps can move, in units of `B h`.
3. **Prove (L)**, the local error: a step of `F` from a value near `A` has error at most `h c`
   (`HasLocalError`). Prove it for globally Lipschitz and bounded fields and move it to the tube
   with `HasLocalError.of_tubeExt`.
4. **Apply** `StepMethod.IsTubeLocal.exists_run_norm_sub_le`, which gives the run and the bound
   `e^{L T} δ + T e^{L T} c`. The whole proof of the BUG case is the end of
   [`Integrators/Matrix/BUGRun.lean`](../LeanDLRA/Integrators/Matrix/BUGRun.lean): `MatrixBUG.isTubeLocal_stepRel` is step 2, the
   local error `MatrixBUG.stepRel.hasLocalError_of_tube` is step 3, and the theorem of section 1 is
   step 4.
5. **Show that the hypotheses can be met** with an `example`, as in the examples of section 1,
   and read [Getting started, section 6](GETTING_STARTED.md#6-how-to-add-a-result) and
   [CONVENTIONS.md](CONVENTIONS.md) for names, docstrings and placement.

For a grid with variable step sizes use [`Integrators/MethodGrid.lean`](../LeanDLRA/Integrators/MethodGrid.lean), for steps that
end with a truncation to a tolerance [`Integrators/MethodTolerance.lean`](../LeanDLRA/Integrators/MethodTolerance.lean).

## 5. How do I find the definition of X?

1. **By name:** [Definitions](DEFINITIONS.md) lists every definition of the core by folder, with
   file, line and the first sentence of the docstring.
2. **By notion:** [Concepts](CONCEPTS.md) says how definitions of the same notion relate; use it
   when two names look alike.
3. **By folder:** the layers and the files that own a notion are in
   [Getting started, section 4](GETTING_STARTED.md#4-where-do-i-find-what) and in section 2 of
   [CONVENTIONS.md](CONVENTIONS.md): definitions are in the file named Defs.lean of the folder.
4. **By text:** in the repository, the shell command grep -rn "def X" LeanDLRA finds a definition, and
   grep -rn "structure X" LeanDLRA a bundle. Every module starts with a docstring that says what
   it contains; read it before the declarations.
5. **In an editor:** with the library imported, `#print X` shows a definition and `#check @X` its
   type; go to definition works as for any Lean project.
6. **On the web:** [the API reference](https://camminady.dev/leandlra/) is generated from the
   sources.

The core and the catalogue are different libraries ([STRUCTURE.md](STRUCTURE.md)). If a name is
not in [Definitions](DEFINITIONS.md), it may be in the catalogue; see section 8.

## 6. How do I find the theorem that says Y?

* **By topic:** [Main results](MAIN_RESULTS.md) lists the main theorems of the core with their
  statements.
* **By integrator:** the `…Run.lean` files of [`Integrators/Matrix/`](../LeanDLRA/Integrators/Matrix/) hold the
  existence and error theorems; start with the module docstring. The midpoint BUG integrator is
  in [`HighOrder/MidpointBUGRun.lean`](../LeanDLRA/HighOrder/MidpointBUGRun.lean), the explicit midpoint method in
  [`Research/ExplicitMidpointRun.lean`](../LeanDLRA/Research/ExplicitMidpointRun.lean). A bound with a one-sided Lipschitz constant
  in place of `L` in the propagation of errors is in
  [`Integrators/Matrix/BUGRunOneSided.lean`](../LeanDLRA/Integrators/Matrix/BUGRunOneSided.lean) for the BUG integrator and in
  [`Integrators/MethodOneSided.lean`](../LeanDLRA/Integrators/MethodOneSided.lean) for every tube-local method; the implicit BUG
  integrator on matrices is in [`Stiff/ImplicitBUGRun.lean`](../LeanDLRA/Stiff/ImplicitBUGRun.lean) (not a stiff bound).
  The implicit BUG integrator for the fields `M Z - Z CᵀC` and `-BᵀB Z - Z CᵀC` has runs that are
  uniform in the stiffness in several classes and counterexamples outside them ([section
  7.7](MAIN_RESULTS.md#77-the-implicit-bug-integrator-for-stiff-sylvester-type-fields)); for the BUG
  integrator against the truncated singular value decomposition see [section
  5.4](MAIN_RESULTS.md#54-quasi-optimality-of-the-bug-integrator-for-given-data).
* **By question about the solution:** existence and uniqueness of the DLRA solution of rank `r`
  on a short interval are in [`DLRA/Existence.lean`](../LeanDLRA/DLRA/Existence.lean); its distance from the best
  approximation of rank `r` is bounded in [`DLRA/QuasiOptimality.lean`](../LeanDLRA/DLRA/QuasiOptimality.lean), for a field
  that is Lipschitz on a tube only in [`DLRA/QuasiOptimalityTube.lean`](../LeanDLRA/DLRA/QuasiOptimalityTube.lean) and for the
  truncated singular value decomposition under a gap in
  [`DLRA/QuasiOptimalityGap.lean`](../LeanDLRA/DLRA/QuasiOptimalityGap.lean); the margin `ρ / 4` can be widened to `θ ρ` with
  `θ < 1 / 2` in [`DLRA/QuasiOptimalityMargin.lean`](../LeanDLRA/DLRA/QuasiOptimalityMargin.lean) and to every `θ < 1` in
  [`DLRA/QuasiOptimalityNormal.lean`](../LeanDLRA/DLRA/QuasiOptimalityNormal.lean), which uses the constant `1` of the Lipschitz
  bound of the tangent projector in
  [`FixedRank/TangentSpace/ProjectorLipschitz.lean`](../LeanDLRA/FixedRank/TangentSpace/ProjectorLipschitz.lean). The forms for the error against
  `A`, a field that is Lipschitz on a tube and the truncation under a gap with `θ < 1` are in
  [`DLRA/QuasiOptimalitySharp.lean`](../LeanDLRA/DLRA/QuasiOptimalitySharp.lean), the truncation with the margins `θ ρ` and
  `ρ / 2` in [`DLRA/QuasiOptimalityTruncation.lean`](../LeanDLRA/DLRA/QuasiOptimalityTruncation.lean), and the bounds with the spectral
  norm of the tail, `σ_r(A)` for the truncation, in
  [`DLRA/QuasiOptimalitySpectral.lean`](../LeanDLRA/DLRA/QuasiOptimalitySpectral.lean) (sections 2.4, 3.6 and 3.7 of
  [Main results](MAIN_RESULTS.md); the table at the end of 3.7 lists the theorems side by side).
  The rates in which the velocity enters through its normal component only are in
  [`DLRA/QuasiOptimalityNormalVelocity.lean`](../LeanDLRA/DLRA/QuasiOptimalityNormalVelocity.lean),
  [`DLRA/QuasiOptimalityDefect.lean`](../LeanDLRA/DLRA/QuasiOptimalityDefect.lean) (the defect of the truncation in closed form),
  [`DLRA/QuasiOptimalityNormalVelocitySpectral.lean`](../LeanDLRA/DLRA/QuasiOptimalityNormalVelocitySpectral.lean) (spectral norms, an a posteriori
  form), [`DLRA/QuasiOptimalityTimeLocal.lean`](../LeanDLRA/DLRA/QuasiOptimalityTimeLocal.lean) (constants that depend on time) and, for
  a field with a tangential stiff part, [`DLRA/QuasiOptimalityStiff.lean`](../LeanDLRA/DLRA/QuasiOptimalityStiff.lean) and
  [`DLRA/QuasiOptimalityStiffTruncation.lean`](../LeanDLRA/DLRA/QuasiOptimalityStiffTruncation.lean); the speed and velocity bounds are shown
  to be attained in [`DLRA/QuasiOptimalitySpeedSharp.lean`](../LeanDLRA/DLRA/QuasiOptimalitySpeedSharp.lean) ([Main results, section
  3.8](MAIN_RESULTS.md#38-quasi-optimality-with-the-normal-velocity-as-growth-rate)). For Tucker
  tensors and tensor trains the same rate, with a constant that does not depend on the number of
  modes, is in [`Tensor/Tucker/QuasiOptimalityNormalVelocity.lean`](../LeanDLRA/Tensor/Tucker/QuasiOptimalityNormalVelocity.lean) and
  [`Tensor/TT/QuasiOptimalityNormalVelocity.lean`](../LeanDLRA/Tensor/TT/QuasiOptimalityNormalVelocity.lean).
* **By question about stiffness or training:** what is proved and what is open for stiff problems
  with forcing is in [`Research/StiffGlobalCycle.lean`](../LeanDLRA/Research/StiffGlobalCycle.lean) and the files named in
  [Main results, section
  7.6](MAIN_RESULTS.md#76-stiff-problems-with-forcing-six-results-and-what-stays-open);
  the descent thresholds of federated rounds are in section 10.1 of the same page.
* **By paper:** [PROVEN.md](catalogue/PROVEN.md) lists every module with the papers it cites.
* **By shape:** names say what a theorem bounds or states (`norm_sub_le`, `exists_run`, an ending iff);
  the rules are in section 7 of [CONVENTIONS.md](CONVENTIONS.md). A search for the key word in
  LeanDLRA/ with grep is usually enough.
* **Is a statement proved at all?** The recorded statements are in `docs/statements.json` (core)
  and `docs/statements_catalogue.json` (catalogue); the
  open questions are in [`docs/catalogue/survey/`](../docs/catalogue/survey/).

## 7. I want to check my own Lean file

The script [`scripts/fc`](../scripts/fc) checks one file against the compiled library, without building
anything:

    scripts/fc --axioms FILE.lean

It prints errors and warnings and, with `--axioms`, fails on any axiom beyond the three standard ones: propext,
Classical.choice and Quot.sound. A file that imports a module that is not compiled needs
`--with`; the usage is in the header of the script. For the whole core, `make verify` builds and
audits; `make ci` adds the Python checks. The checks the maintainers run, and the rules a
contribution has to satisfy, are in [`CONTRIBUTING.md`](../CONTRIBUTING.md).

The examples of section 1 are checked in the same way and are built by `lake build Examples`.

## 8. I found a result in the catalogue and want to use it

A theorem of the catalogue is proved, but it is stated in the definitions of its paper, which are
not necessarily those of the core; it does not automatically apply to the objects of the core.
To build on it:

1. Look for the same notion in [Definitions](DEFINITIONS.md) and in [Concepts](CONCEPTS.md).
2. If the catalogue file has a bridge to the core definition (an equality `local = core` or an
   equivalence), use it to transport the statement.
3. If it has none, prove one: that is a contribution to the library ([CONTRIBUTING.md](../CONTRIBUTING.md)).
   A catalogue module becomes a core module when its definitions are the core definitions or are
   proven equal to them, and its name is added to `docs/promoted.txt` ([STRUCTURE.md](STRUCTURE.md),
   paragraph "Promotion").
