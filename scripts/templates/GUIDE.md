# Guide: how do I ...?

This page is organized by task. Each section starts with what you want, says which file and which
theorem to use, and ends with the place where a worked case can be read. It assumes that you have
read the first two sections of [Getting started](GETTING_STARTED.md); the pages that say what the
core proves are [Main results](MAIN_RESULTS.md) and [Definitions](DEFINITIONS.md).

Every block of code on this page is copied from a file of the repository; the line above the
block links to the lines. The blocks were compared with the files at commit @commit.

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

**Use** `MatrixBUG.exists_run_norm_sub_le` in @file(LeanDLRA/Integrators/Matrix/BUGRun.lean). It
says that the fixed-rank BUG integrator can be run and that the run stays near the exact
solution; it is the theorem to start with.

@stmt LeanDLRA/Integrators/Matrix/BUGRun.lean exists_run_norm_sub_le MatrixBUG.exists_run_norm_sub_le

**What you provide**, in this order: the exact solution and the constants `L` and `B` on a tube
(`hP`), continuity (`hc`), a bound `ε` for the normal component (`hε`, `hε₀`), the step size and
the horizon (`hh`, `hhH`, `hNT`), the rank conditions, the start value (`hY₀`, `hδ`), and the
smallness condition `hsmall`. [Getting started, section 3.1](GETTING_STARTED.md#31-the-theorem)
explains each hypothesis.

**What you get**: a run `Y 0 = Y₀, …, Y N` of rank at most `r` with
`‖Y n - A (t₀ + n h)‖ ≤ bugGlobalBound L B H T δ ε h`; the right-hand side contains no singular
value.

**Worked case.** @file(Examples/BUGEndToEnd.lean) is a file to read from top to bottom. It writes
down a `2 × 2` linear equation with numbers, shows that `A(t) = C` is its solution, computes `L`,
`B` and `ε`, applies the theorem and ends with the statement

@quote Examples/BUGEndToEnd.lean ^theorem exists_run_error_le || ^      ∀ j ≤ 100

The file is not part of the library `LeanDLRA`; it is the library `Examples` of the repository
(`lake build Examples`), so that it can be read and changed without touching the core.

**If you already have a run** from another construction, `MatrixBUG.IsRun.norm_sub_le` gives the
same bound for it under the same hypotheses on `F` and `A`. **If you only need to know that the
hypotheses can be met**, `exists_bugGlobalBound_lt` produces a start tolerance `δ` and a step size
`h` for which `hsmall` holds as soon as the part of the bound that does not vanish with `δ` and `h`
is smaller than the tube radius.

## 2. I want the same for another integrator

The theorems of the other fixed-rank integrators have the same hypotheses `hP`, `hc`, `hε`,
`hε₀`; the three lemmas that give them for a linear field serve all of them. Differences:

| Integrator | Theorem | File | Extra hypotheses |
|---|---|---|---|
| projector splitting | `MatrixKSL.exists_run_norm_sub_le` | @file(LeanDLRA/Integrators/Matrix/KSLRun.lean) | none; no `hhH` |
| parallel BUG, fixed rank | `MatrixParallelBUG.exists_run_norm_sub_le` | @file(LeanDLRA/Integrators/Matrix/ParallelBUGRun.lean) | none; no `hhH` |
| BUG with explicit Euler substeps | `MatrixEulerBUG.exists_run_norm_sub_le` | @file(LeanDLRA/Integrators/Matrix/EulerBUGRun.lean) | the field is Lipschitz in time with constant `Lt` |
| BUG with augmented bases, truncated to rank `r` | `MatrixBUG.trunc_exists_run_norm_sub_le` | @file(LeanDLRA/Integrators/Matrix/TruncBUGRun.lean) | `hκ : 1 ≤ κ`, the quality of the truncation |
| rank-adaptive BUG, truncated by a tolerance | `MatrixBUG.adaptive_exists_run_norm_sub_le` | @file(LeanDLRA/Integrators/Matrix/AdaptiveBUGRun.lean) | the tolerance `ϑ`, the normal bound for every `r ≥ r₀`, `r₀` below the matrix sizes; the bound has the term `e^{L T} n ϑ` |
| parallel BUG, truncated by a tolerance | `MatrixParallelBUG.adaptive_exists_run_norm_sub_le` | @file(LeanDLRA/Integrators/Matrix/ParallelBUGTolRun.lean) | as the previous row; no `hhH` |
| dynamical randomized SVD | `MatrixDRSVD.exists_run_norm_sub_le` | @file(LeanDLRA/Randomized/DRSVDRun.lean) | sketch and range bases with `k` and `l` columns, `r ≤ k ≤ l`; the normal bound at `r` and at `k` columns |
| projected Euler method | `MatrixProjEuler.exists_run_norm_sub_le` | @file(LeanDLRA/Integrators/Matrix/ProjectedEuler.lean) | the field is Lipschitz in time with `Lt`; `hκ : 1 ≤ κ`, the quality of the retraction |
| projected Runge–Kutta methods | `MatrixPRK.exists_run_norm_sub_le` | @file(LeanDLRA/Integrators/Matrix/ProjectedRK.lean) | a Butcher tableau, `hκ`, and as a hypothesis (`hRK`) the order of the classical scheme |
| BUG for Tucker tensors | `TuckerBUG.exists_run_norm_sub_le` | @file(LeanDLRA/Tensor/Tucker/BUGRun.lean) | the field is on `Tensor ι`; the normal bound is at the triples `TuckerBUG.normalTriples r`; margin `(d + 2) B h` |

The table with the error bounds and the margins is in
[Getting started, section 3.4](GETTING_STARTED.md#34-other-integrators). A rank that changes from
step to step, with a truncation to a tolerance, is treated by the rows for the rank-adaptive
and the parallel integrator; their step relations are in
@file(LeanDLRA/Integrators/Matrix/AdaptiveBUGStep.lean) and the run theorem with a tolerance for
every step is in @file(LeanDLRA/Integrators/MethodTolerance.lean). For the rows with a
tolerance, a Tucker tensor or a retraction, the hypotheses on `F` and `A` are the same `hP`,
`hc`, `hε`; the page [Main results, section 4.3](MAIN_RESULTS.md#43-one-run-theorem-many-methods)
lists the margin constants.

**If your method is not in the table**, show that it is tube-local (section 4) and apply the same
theorem; the integrators of the table are the examples, and the shortest ones to read are
@file(LeanDLRA/Integrators/Matrix/ProjectedEuler.lean) and
@file(LeanDLRA/Randomized/DRSVDRun.lean).

**Worked case.** @file(Examples/RankAdaptive.lean) runs the BUG integrator with augmented bases
and truncation to rank one on the problem of the first example, and compares the two bounds:

@quote Examples/RankAdaptive.lean ^theorem exists_run_error_le_trunc || ^      ∀ j ≤ 100

## 3. I want to state my own problem in core definitions

A result is stated in core definitions when it is about the objects of the core, so that it can
be combined with the other theorems. For a differential equation `Y' = F(t, Y)` for matrices:

1. **The field** is a function `F : ℝ → Matrix m n ℝ → Matrix m n ℝ`; time comes first.
2. **The solution and the constants** are bundled in `DLRAProblem F A a b ρ L B`:

@stmt LeanDLRA/DLRA/Defs.lean DLRAProblem LeanDLRA.DLRAProblem

   `DLRAProblem.of_global` gives the bundle for a field that is Lipschitz and bounded on the
   whole space; `dlraProblem_linear` (@file(LeanDLRA/Integrators/Matrix/Defs.lean)) is a case that
   is Lipschitz but not bounded, and it is the template to copy.
3. **The normal component** is bounded by `FactoredNormalBoundOn F r D ε`;
   `factoredNormalBoundOn_linear` is the template.
4. **A run** is `IsRun (MatrixBUG.stepRel F r) (uniformGrid t₀ h) N Y`.
5. **A norm.** Matrices carry the Frobenius norm only inside the scope that a file opens with
   `open scoped LeanDLRA.Frobenius`; without it `‖Y‖` is not the norm that the theorems use.

A file that states a theorem in these terms starts like this (see
@file(Examples/BUGEndToEnd.lean)):

@quote Examples/BUGEndToEnd.lean ^import LeanDLRA\.Integrators\.Matrix\.BUGRun$ || ^import LeanDLRA\.Integrators\.Matrix\.Defs$

@quote Examples/BUGEndToEnd.lean ^open scoped Matrix

Write the numbers of your problem as a `def`, prove the three facts of 2 to 3 for it, and
instantiate the theorem of section 1. If your field is not linear, the lemmas of
@file(LeanDLRA/Integrators/Matrix/Defs.lean) show what each of them has to prove.

## 4. I want to add a new integrator as a `StepMethod`

A method is a map from fields to step relations:

@stmt LeanDLRA/Integrators/Method.lean StepMethod LeanDLRA.StepMethod

`M F t₀ t₁ Y₀ Y₁` says that `Y₁` is a result of one step for the field `F` from `Y₀` at time `t₀` to
time `t₁`. It is a relation because the result of a step is not unique (bases are determined only
up to a choice). To get a run and an error bound you prove three properties of **one step** and
one error estimate; the first three are bundled:

@stmt LeanDLRA/Integrators/Method.lean StepMethod.IsTubeLocal LeanDLRA.StepMethod.IsTubeLocal

The route, as @file(LeanDLRA/Integrators/Method.lean) describes it in its header:

1. **Define the step relation** for a general field, in the folder of the integrator, as a
   `StepRel` (@file(LeanDLRA/Integrators/Defs.lean) has the vocabulary: `StepRel`, `IsRun`,
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
   @file(LeanDLRA/Integrators/Matrix/BUGRun.lean): `MatrixBUG.isTubeLocal_stepRel` is step 2, the
   local error `MatrixBUG.stepRel.hasLocalError_of_tube` is step 3, and the theorem of section 1 is
   step 4.
5. **Show that the hypotheses can be met** with an `example`, as in the examples of section 1,
   and read [Getting started, section 6](GETTING_STARTED.md#6-how-to-add-a-result) and
   [CONVENTIONS.md](CONVENTIONS.md) for names, docstrings and placement.

For a grid with variable step sizes use @file(LeanDLRA/Integrators/MethodGrid.lean), for steps that
end with a truncation to a tolerance @file(LeanDLRA/Integrators/MethodTolerance.lean).

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
* **By integrator:** the `…Run.lean` files of @file(LeanDLRA/Integrators/Matrix/) hold the
  existence and error theorems; start with the module docstring.
* **By paper:** [PROVEN.md](PROVEN.md) lists every module with the papers it cites.
* **By shape:** names say what a theorem bounds or states (`norm_sub_le`, `exists_run`, an ending iff);
  the rules are in section 7 of [CONVENTIONS.md](CONVENTIONS.md). A search for the key word in
  LeanDLRA/ with grep is usually enough.
* **Is a statement proved at all?** The recorded statements are in `docs/statements.json`; the
  open questions are in @file(docs/survey/).

## 7. I want to check my own Lean file

The script @file(scripts/fc) checks one file against the compiled library, without building
anything:

    scripts/fc --axioms FILE.lean

It prints errors and warnings and, with `--axioms`, fails on any axiom beyond the three standard ones: propext,
Classical.choice and Quot.sound. A file that imports a module that is not compiled needs
`--with`; the usage is in the header of the script. For the whole core, `make verify` builds and
audits; `make ci` adds the Python checks. The checks the maintainers run, and the rules a
contribution has to satisfy, are in @file(CONTRIBUTING.md).

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
